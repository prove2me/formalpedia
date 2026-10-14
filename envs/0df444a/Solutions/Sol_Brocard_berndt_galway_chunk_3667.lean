-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3667
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:20:04.098861+00:00
-- url     : https://prove2.me/submissions/2d1a6aa8-a95f-4253-a178-8708ec9c2f0c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 659352517 ≤ n < 659532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 659353767 1250 659352517 659352539
    0x2030a17011409040c090f090203120f3405010911030c060406050c0c06130807060c02090f060a091a0406050307060822050102040e01090510030c0611190f02010801 72
    0x1000b200165440c032003a039000307030500c01540d942042c801e41c01140c0064032072600c0821114503103055850070f0784035401c5000f9428148100e040300500b03d00c0452400188410089051080c11841c0b05441004e04e01e101d552041290041d90300107c901406090a0190500602030810014142c48a1144290132a4035180000711000f26030805405641054034115054030a604600710040e460300800d5415031107944c480740100300c5101d0742c0f145000f006081290041c500729050300000d060080c8440b200000d81e68005009a120160210003140d0f40d8680d0b0105d01d952016030301002080d400d01c422a070042d1f054040e40c00c144002034404124403992001010347d0780300548944008942c0c004080780c280291010b00301005183d000728460800c08954566007242d0140c2e01001c55080c8840060001c81d60303900840f60452301400c106c0c2c485904644071403119034200d1140c0c609204864501c0020500180898110742c50042d681403401c2c086414022000b81e03882da002c0f07000070303035000c0081481c524103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 659355017 1250 659353767 659353769
    0x1e0f1f050a090b010203130807060915020601031101111b130209100521040303060e1602071401140301080106260307030c0c0519091d0604020405070509090702030a1701 74
    0x24184031910345018030b4a801028081041411400104600303105888140007050050000100400b00c5070314211004060002a40204034442c1500301551512a40050602d054a4110101c078581c1e511600040c1d4142c03112141403003281c0515545a588400c2510400f40c50362000ea4a8601041c40321000e5009c9200b102510b0340d2082c901c844012026220340c018014102144241a12007001501d00c06404c02045030128002511900f0903c294400c00019039000007149501143c41e0900c203801035200e8030240592100702c0450062945240c1c0700700d50b40c10710218101c1034036503a5612089041d010302610b02400114003400c00142d501d03800c2c030301c29209921951f0800f45040c98156038084070f01c1c0c0d410b07460a6030949611a00400d4554a8416140200329484107452600303203009041402c0c0e8101c64000302c03140440c1b200804040c2000b081041d482581103900040fa0f56540300f041d103041c060f2005170313034000ca00d64080001d00b903000002440b000d512034030f0301c0c400000f1600c083d008044013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 659356267 1250 659355017 659355019
    0x3020c0d15110f0304140c0a120210020106050a0305011a150d0c171303140316050306031006031b050904021008091005161806171e0f1f05 61
    0x905007209403203404a034811001c0c10340300d602d210b2401e11203001484194005550a450302c501454421140313130010803041d01e031090107444801085141504803c0c84803107104019001c2d100846c03128000794400e61005000c1c0c400104030705001da03100e051160003401c003540546018408c141d8050154078011100c02c150fa612162041c0c1340001071481c00707018080f4044951b0510425018401d0716450010445104d658a031008050001250074010071403d000140343c0364610042050190300d101c45179a08864000506001e503580d00c8120120303240030f15081080c81c1640c0b410902104100c1c40c01250503402140003d45210640c0b06c0382001803002003074400940c0849811032003503101d80511001176010010400741c42d120803120788620180c0720100c0d030f05101441c2901c107008a542c0c200001489504076501e50203505800d00c4d0014160301c2d24511111104d8500200007180700b049901805480074400003809003508120901d007044010507114080c2090b429030442000050a280060803200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 659357517 1250 659356267 659356283
    0x510090515092e0303030f0f0507050a260703090302070f050d06051302121f091109041b0b040501080109020a021002030711061009050c03090604020f01031e050403020c0d 75
    0x2d0b100f0580c94807091a181c00b000e65105819040882d80280548000850280e100400e0039102c0302090000c40d1840e02c0350380400740c1380805100c219640031060341c00300b040500700072043c51822482003c200b03140d4448031440c05c0d00c10702084000c1d5415000388a480348a074080343d00d440c0d00c840380190029000e0160781c0e00235080750610740200f100c40c0c02c4190444071844816088038035940118020b41d110403452101503002d05480501c0c445086108602d0741000d4104200400d09681c030310848440003100688030310300c854082001d019401ca805000c10340c0e05036651001c960749100791611904103205007804034412800010340b411450088030040070480d4081d00381c1400303000c070100c0290009000c3d40d0400c01401c1d1460300381e134401c10480340115454100c0750002894903c1100075104001c1004480b03100034800c0c40707255440002c5058000d075040347c208000e800000c004030000c00e44031403031700161581c1c00c495003400b8034598000c500541c02a42600c0e42083c84005010500c0c017840d0340140185 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 659358767 1250 659357517 659357521
    0x50d020606011b02060d1d0c31052d040b13030c230109080705011a0d03260a05070e191a0f04030b010617040201050306190306051009051509 62
    0xf00c0c05000400e500f43c10b0309000110034000080c04202d00e64803007e210415488195035145034980400d0b5026440a8800000c042c280001126100e02011003041444140c440c404500000c2d10010150030848152606009070325440c3d8030203061000a9409494521560020071589018030782407110032601a140c500350365007243d443c03c8400b07584020039040c0c98210320700341030324501c00c0c0580c114080c05040240e883d01220304009003114501c00189101410a070010883c580300c5e003048143c01e6425003040704001010a0324a000001d00303148103440301d8107510411500b044907038440b50248840d965294040c0700240103001504446103848500e011001d84100001484441c16061b294104011b05003802c0d003141065010390403075001140c100c1500c00041c401c5d96441009004801120058001c0c94141900040c01c1440094603481c00780c1c90300d0981454640310745501400465215200300f00da440c001002c814880c0e141d0040c031450700c1c107000c003041050034501010020400d008101117196 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 659360017 1250 659358767 659358769
    0x1030504120e0d02030607050705060609070c021203070f140d03110306042705030c0f03160f0206090a08011e05060f0d020d080a030911040203090c06090616050d020606011b02 77
    0x203603880780b070341d41d407000030803803030b0001a1424421203001d0b41860b01e0303840d12003149103003190506000824481c000d50740300d0108406142d0010200d0314058054031025443e84500307015034118411004041c100c40c10ba0100942004992030302e026070f0580e0402902c0d5140040d040c200c064a006800d01020400f0900100b84586001d0b40300035070358402070a030b803200c4021100d003a0300c450440c190240d403207802c04140c010000106002c00c1a8450411003e546007003609803081f40140321141001d4404400303480d41da401c6440300d80499840c841d00400440fa03082c0d9481c140b901a05102107296a034452891620000b07035018010f00b8011035005200952100c13031001400b21782a0060b4059074000450390b0190301007030541004000c1998656004500d103452030078095848036004062134041c600c10020002c2098020944100c026012101c0b40d6442d006500011400d000c0c550845140500c080100c00c10001e001650a800040d15001c1e120a80eaa480c0155000d80308004086600d0201017189401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 659361267 1250 659360017 659360027
    0xc190e1e0a0e1003021912080f09120c01021009020616050c060a1d061206300109060e2b020109060c02033a09020303041e030b01050103050412 63
    0x403210007600042041d569010034103420441030300d40c1080c0504205090041d03003810500b081c4d440c00000205a843c071f1828800009100c1a00d402400311075010841d025208034440031641441401000c010840101843c0c446c1c03154500010a8090710070f118908905040c0ca005403210507030028561414541d00c440410990b14a0040440d12800fa821108229544800103401d840c2c492b6500c0c0c508036000401205e08000c80881040d10408050040340b640150b1028850790104065902d0f41d404500e01c55400000b0b001c0d03c2446001c0e0202c0340c00000c2c050310540c090409039010320424415010b00501c43c9071113913030012030703100c2400304050880700d001005c00c0f100400c00030a100000c0c0907203050703c490040701d1180d0840c10040e040055543c45c042002c045030104042045070541442145401c1441c10300c80300c0a022040d070303031100380348001d41d5400d006a8000b4032000b44004140741c2c4526249540c1c4a40340001c54035a110f05c0000710b01540710744542c80c131803603000e85c00001540042d902074078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 659362517 1250 659361267 659361319
    0x60a0b0d0f0503130f0305060108060f24060a320f07030908070e0702010c08070206071b05060f06010f020a0201020303060405151f030b03011103010e1e0c190e 70
    0x18041c8803c00c101022130350120b59200c02031041c00e020105a070308601c1d00c1c3d4100710060340300c41440e0340400240310710b180d000310f8440c0e00040f280308807400302020504201124420f0b4000e4a50240012818180882d009800642004075040c08041c00f4040040402d02980c407121450242d043c0c00d210040c92616074900605c00390307000c1d0500c1d61380b20b5910b0640602d042d0aa4005170039081c5a90144003003d5024090b9034030b840542d00b0400c00720702c0c3c8044000c0d55500010a241d0400a402c5506101000d140d0391000c1c509402c00c05850319440c2c00000500c07502d00650390351f40054070b42c04ca210480c45c800305605140707640c1607010754070350344501e000c010140102608a45502108000c030780c900e661012101d01c20b02c0c072242140726104d101c80701c01604071400d2009850007641011440d0300b5030310590040368192071328a004110540c039101000425000d00c0c806074501403407010140100d00d0303806009040d0045221544141850508a00b1a0410484d1000682141c1c8400010042c1c02d10188200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 659363767 1250 659362517 659362523
    0x7150209030f03041202010e01030506030a15090c0806041703100501030903110a110123030402041505031b150f0a030e011514120105041707051207060e060a0b0d0f 72
    0x1e04104020b441050071540180d211024005400e58070808651300034181c44074026090070b00704101d02d4102c000c20b40302c6807240b40c0207041700e0000105140113000f40d8020b08100e500701141005a40d00c0d21006a0b4441040d241a00c0000d01c006d03d50701c4044140085a00c1140510080c00405181000640103401140e5080701400201403103803000170000c216110020340030300d010240c80c0e8280c0c3d0000d848484100003280c000300300c040301103503010000d00480f50020ba0648001a4204406400007001659130300071a1745805200d19409580480f2aa1050084411111031403103445118205507103205000e6030411890041c000c05402034013907031001d12443c49040c00859554900c80844540200030f40100382c0303610341c0900001103410a40704d05080044c0240c000c1205041c80c2d21a0302c0103603003611080802c0d9a00041ca8070410909021302c03200320240e88000b548078446031800300701908419418590921410f4001580c0c0e0748540962907174001d010349948201d1794503480b1203940c054880c0c1c040e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 659365017 1250 659363767 659363773
    0x20c03041a070b070e0a060f02070e130b010608010e0f0411090703110c030c010e16440c012d0905060d0204080d0201060b04050d140a0b0a060b0715020903 68
    0x88800300f00e20010944c03080c2d0040c1d0b514030881a0707484c1008502d030355030781040d400c2144039034014030070640007d510003ea404080c40710800d0780c1c80401300256119020001000052080c000260a1342c1042c0c00030f0580321804001000c0d507880e82c51202c1d0565003218050710300320380ca0b40d006905045c8807000c550000030a00d004a42007000b9a603035680f540c1710600d0808240d04c00180c1000700c810030700c143c0130141f5000d005800040d81030050080800702d03038014549001c941e0980030240b140c044d41190200011050707001c081c501034900c0520048031001680819003d04801c0d046698410a03c2001c41455105041c4591030400414481c2c80003659800090009814020400e50395a201070145002d0314a80543d0351400c0c084614284000383d0080000d681c1841c03030a01c182d52200090b02e05071034061b201d40c407602a80f410413088900d0f0340094940781d80561440078042c4684401e4480c0701c2c1c0024003090002070359401c0b00c800580700d0040c0141102205484071020741c1c00940003804000c0c1e0003021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 659366267 1250 659365017 659365027
    0xf0201050d050726241201050406060603060518070e040b0301060e09122b090204090605062112070c0315020a1d1e0301020418020c10020c03041a 64
    0x1006040b40d0301628040045000f01e103880d841c041c0d41c1c1e001e8040560f0043c1c681e41d580c2c2030001c00d10506001c80200012043c003440b07a42181619040d06004c0f041c08a00000c2c04642402e0501c48028a424052000000e080c00c00208540c03d142003c02c40400d9202d60342c017540d6076503560442c5c0c0407024205060b4442d844031f03902130300c43e5403d0103100301416140c01048a10704115000e5494070050100441e500038041c03211007111102c200c80d0b01596290581240351425000707802500600351114000e5219180010070420700840f1b82c03003648550340680d49101da4001c800c41800f60080301c5d048401081d80701c00d4880520f9800c0320060145035202d548491240341c0c03240d4030701c008900c140c40300c0441c140e030102c0c000d8811540034001c400034190701e804c441e200c0c4c4002c0c408141407050300364003410103a0380c1520302612901c2c258111801003801540c002040d0341c02e034400a0195102004910f001c1c414010cc4280740ca2051080f28001c0b40c82800440c6054602002d0700c60780040c4142c4102c50240c2841 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 659367517 1250 659366267 659366287
    0x9070e010e4c08010e09070e070e0114040801050a0c03061211031e060412140a030e1e0c0f0405060d0209040c181407020d0f030209030c0d030c020a0e090a0f020105 72
    0x3411640d80312510fa0b0b154660401030382c00310a100007042240d013540b041c00700700142801040396907003014691400c40111140c070001a50240000b45030595840340024002031050010b51002d401802072410501082403d400b0440039a030315800340024403008501800005100c0402504400b000134080d01d844100e1403400e104402c18403001c1c0d02158000c60b00700410400c848182000c030745598144420801a0703001c844590b4002d1000d094241030341e4242e503940d40c420801c40c041d0461440f480d5803080706403146c102c6803901d01c484030450250036508400000380c40c0034011130340b043c10f010340140d216640b160200304440d10040e106640c4140b003080049041d03030303900c1304440740c8001102c404030344107050300301c0d802c0503000051217941150041401c0b00c0340c60b40d01c000e0000c10501c51349000f50303c400328280000d051a042035509940540103030310b084109130700184150700c11402100d4036a0312980d02e2022200110f8215044002600301080344d500141c80d80c0c400b4196540181341c0a414150f81c20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 659368767 1250 659367517 659367649
    0x50702071404090c080d2606060a0203070f03051917040303020f0c19022b060b0301231b07050a03051303060e010b030706050702131a09070e010e 64
    0xd041140c0a030410041144980d030000e445140603a0703561f00410301a140302c00300d5940d495014004a118040c0001c518840d60301c2001524581078000d07000c0444070310b803807030064202d50001002000300381c40200c02d140350740d000340303c03100b204007100050300400d5645d668214000e50005805081500c800c0c808010901c81c1002011107010340070b0329106140d00c00b40100704409094000300d80e1003c10070390a80d480c064000058000440d0701850205081d105000028090100300e04d07403010220f8030145020302e14610751481c90145e2489498070038000d40c0c141b440e6005110b080d0b03010748a680000d03210300000344114001e22200e02c600c042c002c030242e2030340d8500055a500a4480a0a03911800022064981440050010000c03030030024902101381d404150140e158825501080e40e07035020318980d03905c0d084c0141d41100c0700103015401d94504400090038120704001d034140040d100103100400350421140030500e030414884110100d54445100c0545c5902c400b0701400b271210801c0002c06400d10b82 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 659370017 1250 659368767 659368769
    0x139080c0313061e12050a0e0a08031801110708030703020d1b0f0504050f06030c190507030e100801230a081f0614011d03070303030e06070201050702071404090c 71
    0x241c81c010310341034580360000b454007441070f03807404070081003584d0000d1a41d041040124041c901d000007003025034900d0503400c028100e9400128503070045018400030001d044e0002c51044200c0c1c0c00310007070a161030081c0d900305d5083c4498105119400c0144602150a09001e503601c580e0352b00e800b610342125a45480d080e0b5140618461003100c0d000d60410b0066000070003864040d021346000f60401c2e140c080000d16110b02e003064140901000400304904030380701e000310303080c6802d03403e60070b000401c549900408560000105400217803110f1b40701c090b24a004041d070140d1680d155111040f0764208000348006800d41c01680030882040d490000c9a42c840c617a50340700802100f40036140d80040ea4001064500200c088c00340304c24907040c000d00030200d030504655110f0400f8a80110380490891840740d0302402100c91590520071100004101a07050300701003181d0f00043d06650355520782c0c0b01d0680c01d81d04c1c00c0c0c0e9440056002924140550000340a500070241030007040811034071401c1d00c48020b03201c51 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 659371267 1250 659370017 659370037
    0x110304050d0305060a06031a0402031f09020c12030a140405160503010203090717121207030e01050f160e0d0602090a081203010e040807120309020139080c03 69
    0x4010001400401d01c98484002414181072095103455000600c0140150044c1018940d480901c07000d00c40000000c2c100c440301c0648215960305081242d01445540805c2015055500715000309404170700740241c5946011400082c001c40f94040e0001d111030304014034852005c1c0e40c031007000c140c030fa40440e00c05000c0d42c0140f005d44000a030303119148400030b0298001c00e01aa00400c18000c0c000c00c0003441004070740d05034480801c4036006402e22030615034401e00c250820301c804151a1110410b1020007402031001c0e80b0108980d10103011903d00341c5000f11582c80b40c059000c0000f400c1001aa0346030f40703c454013813500c0b805012500c40003494500b0711042c2a80c0c050741c0801c22424504090348002c0282010b00001d01c082c440c004010429880b050084000d1240c40c5008a0100078900044d0f640c0c8a50188040324000241040100144540402070b80092220050301c0d4801c1c5820360b5403509101078100c015481114074212000c1032502917821908081c0801c001c103100c1e201400a0140756030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 659372517 1250 659371267 659371301
    0x15030417090913110103060b0d020c210405100306060815031c03020702030f0a0c0b090406180e0105011733181203010e071b0501060b120112111e0301 66
    0x3405003800e000d4016004d503164141454075a0500500181100356880d8401104000d82d589901403841400c0c011010b412002c5c500030910720308002c2d11500d002d84140c80041c1d6502c0100a05000100d0980b0071a105503804079221202042d030354071202c10040c0b0380100103400c843c4802644c0300e205408030400540000021360105225086140500c103041800348202c00614400d040c585506007001140d00c60510b01c00030008146000b6102d80e0000380003018032030940d801407614035000002500240300c003031413030b5440d00001080c0045405160280951210000c20b1b940301800490203405104601a5011180c01d40034590b400d01046541480380b07401103800c141c1c10350070001303181c544100c0340e030709502840d0180b006100090b00c10b00c3d20355000c1d6291038002e030610012441e03803050400c4060301070304035400c0581c0812103c0c0300000900307115007496802405aa43da201960b4005400795004140311341891040c2811303d400c034486094560400900003500c000e0800090840e4485504400804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 659373767 1250 659372517 659372551
    0x506100f0905010815100519080607181203020c04050103080a022a04091b0f05030c0f1e15040f060e0409021f0201270c05150304170909 60
    0xa03812400d200820500300c0a000c1d0b541090358440c2ca030008130403031042c5042d90000281c0d40380300d80070000c80200005050a40745180e450b003602151713029401503207107070312454001ca84894401e8500e04241c2404090151a581c00c044408103140c05225090b8214420803145046558a0b8400c850003984100c1699540d06a0144040d05114031544680a42248400f5001d070100030740300c240d40d1400044a0008618070325181400803001d0070240c0c0640102d40d8070f004501c00342041c40740000e4540450489482901e40c00070401d00660040960b0f4001c05d90141001c0c6003030924501440d103003c0140008800c440a90045443d900540e0202450f0541148104807031034020400c94811780e4140c42c1400240d4840d00410b2b00032132107103c1c0c00103848440c010258000e2003980012a215490a040b02e90340c21503441604c0b0118401c00196400111380400203a02d140c45101485907107160350078a415035555440e484162011840f2401c0040401c001b0902e0b25034640d130109100d92503111500c0c02038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 659375017 1250 659373767 659373779
    0x90a0903020105060a1805040606080d09081c050d0e0109050d0215010617070e01030e013201030506071b02060c2a131e1803030e011a04021303050610 66
    0x592070141205025a0200c82d00703000c800945046c00030341c8119130101081c107449a14101c401004c081c0e2111501c1d0080200e6030000d41d5000c240e0a0481c0c40c0c003404c4541c82c04003075400410312010840d02c40082501001100c00722a520b0b0862103401022400009800c20161222410030b91000180310058101810b07401441c07521001803400b40c560b6161448410780311403c41440080042c01c002709010400480c018a070384260404187c4405804c000c1c40042002d5900511600305508984000c00660080001e184000c102160403607410034018030540e210102d054848140014607199000070038a400307405a10750800500700303480608014000041c0c0d200740d0b90011500c40124031202c2e00038003c000e482d60381d03015400300100000341000403600c404000216180c45c2d520201c50040b424007280c5c5504c03403950802941c420f40651404d10143c00300700401800c80300002c16240b11042c10f41d24200c2641065400f4050548003003030745000312904d039243e491400c1c2c0304444407130408034281014404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 659376267 1250 659375017 659375021
    0x604140118030503040803041514070209040f0c09020408010b04050705120c04030f03050306040506190b090a030c060206041e0f32010203090c010c022b170d063c05090a09030201 78
    0x92450ad03021810745422040d6981c54441d40b10b01900c919810004201401070508003042025400000340022699440b80c00010b50010b2040c9811546440317180391450900d405034622940036981c0c0c01e0300c1d020045415242c8000c014044000c0b40509000200018144c5103c0000b60b43c06910f81640b0b07490139004210691f0f8000b08100d014400c025803002e10502d10815810035661555962610f42c1c40d810003081c03880d4450751020303020384d0a80d940040d00c96000300d51a07001d40d00503601c074006208480009920f044100600a200e01c20a0720b0460228141d08140144107000001c0011012004c01907400101c030410302d200001c0c0d6000082c0007a50004212044843c102801d004d1902c0791075800041106451120a114201d0241d102034000804200305070700b802d0b44084405000c007520008058035400100120600c04d241c040c000c106046608a04038074480c080302681c030448401a03110046010b149130340004403c900401045a60390441e00c40e01c9104102000120b44059080c001e003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 659377517 1250 659376267 659376299
    0x51f020415020328030e1903030605011b03081b13061e0206181c050d1d030712020c10020a20010801092a051206060414011803050304080304 62
    0x555004010503040007500c04c0032030584110200341c0c0008480d0000b4190090f00680c0045020b600448111481c0c0e00c0c1c0d4585101503c5020303179010001d80351a40c0066800070801c00382000c04101b10780c40302d00080c0c400d880b01984204400d2045418886510003030495400161503d42403402c082d03000e0000075806841010050303c81d000d50301c62480d0944000e502c84d100500410200001c52200c0780032810104920425080707260301d5900300604044000300a030b00641c0c018041c0d81e09040c04a44441c00612600c4810124140035524051090b078580009000d400c802c40190300603002500d040fa52020304012003d942600541a10076692070900c800c4144890000e507152047c41444c186039a11180c000c3c191115030a0008a4008088070038030a20068484071641d02549001e114007982d222000d0400d050038030350f000015840301001c1120034082c50150b803400704581000315000390320502850b0600030090100c3c9040e0750310382d2140b5007558440e8001201c140d0000804000c0c3c0000c00600c1d00d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 659378767 1250 659377517 659377559
    0x150207210c15080c0a0507020d05070302030304080618010c090506090d08030106030b040f020a140c0f1b1207050f0402070218010902071401050405030702040c0e040c021f0b0a0909051f0204 83
    0x217241100c80340019006008071a0080c1c0a001c0c40f40c0350000f080310800c0032501450300201101e84980d961026150380e0b400846151b54125180614400072910500808600c0e12003522450485800c0409001c103035003112075450f50250500d41e40c2004203042c00d00442c003030107a03980c0204403c2d0f81c0605210554a020040042540c8100000e4203000d83c000c50813181c2e08000c0c0241a030350001045282d00d000c49844460819000d641d160302480002c403c81d00d8403084080d180d40d4024034080f40b5103030b1034420380e208641d082100d1080c4000d09240581c000c107030aa00c01000040700410040c2e0300030702d241d401d030000000d1079070002e91401403041c42070301e0b0241007a020000340b000b89441d039031341030f00e0b4003c4c1d880003400380d901c4001d1900f5480c06840c40120882000d00304018401c0301410003551441031b40b4000810700c2c030801104c07402d10580d00030085d8000019001c030503a14604214103004114400f81900d041c000e412000704d05980c1c0450500600070301e8040541c640381080018040300b80b00030021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 659380017 1250 659378767 659378791
    0x90f0a080c151204030c021f0e090604020703021b01022802120303010f03082116080c040609050f0a08030304080702030d030c081303031808040906150207210c1508 72
    0x8031030402110300d0f50380d1103a0b1615000c5811613051011603210f075110340003c090b158049030090111540590610455481125481e006071546400e110032842110f00103130040c2c214505215070001c1e56041c07804082410302c1100e072500340710540f0840010004a404241803980300158041d807a010480040c00c8400f0342c091441d65140050b001d00c068010310000342140004900d0500c0311452401c40c5094052001c0a580c052400740302c0000785a000342091740203e802000071408a695810a07203080e160385880b168034070b0f0304085c10090050000700400798426035904000c1940001800614021480ba000302512401e65204140c1000d0301902c2e00000c152a01a144813110b07401150103422521460f2001c1c40d810b818201240505241c0303904845039502080030780100300380e1500510841d140e00000700407480c1c83c2d40c80c051074058035015101c010b0340125020f0001110300d455041810312035500b1204505460783d54410040100d5100307136401c1070700000c02101180c200d00c80070360002803603c40b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 659381267 1250 659380017 659380027
    0x80102040b0403061107020603091f060503070b030910020406020304180b0a062d0c060513020d0803250c06050a0605060f09030f060a05011e081002090f0a080c15 71
    0x4074803524000c0748070191030151a000454889000300b400c0b543e266401515007a601e1800154051307031894003200b4070003400f041c11001c106070000d506c03a41c170a43c1c2c0024080d00d40b4915040c0040e602d03030809089140b40d4010503014031a40d0005100400007004540c010b1034071185410310b19100421515043c3c2d03501420405079020580c1c450144d0000d035449424180c540d040350320a6443d1123542110400300740c2c1101d1040c00c20564000c001c4000c50380c4600010b1040b41d49030b03110a51303445c88120b4000d412841c0180702e1000111080041d41c7d22503402203101400307804c4008038061040500d6558004690f901403036406214150060304e600c002c9001080c02070741e04d40b4001c140188900030200070300d01340c0407034000002d540510004181d01000800c980310380c1801030410300146002c3c4594440403581a0465081540003041d0008945080000e0001d003110500744002035448002503ea100c1c107440caa040c00750780c80c0c8142c0c002402c3c058009026000907002400920b4404400100b240300080c80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 659382517 1250 659381267 659381279
    0x6030204060e010804051f020913090b040305071a040b040b0c120402040c1101060902040f170c0402070614040c08060702030702030a080705010b0d110103051b090d0305041701021308010204 83
    0x2c800c8603020020f182c10006503445040540c200f1075414404030140c0c030003c8481c00001455006400340301c00881d104401d040018010310201c444900004000754204400500840d004030090b101290194400320f41c0010b4112200c01d032401d0444080b81c82d22032a00600040c171480131481c651100501340982d19140403c6c3e00306030b08650050000b03208584030010b03800041c1c420100c000034504214020700c000f5842e4020701000c2d41060040d481c009480d00000120400041c50a00c661084c0d18003905400c1c0c03100c028032001c0e40c00194140e59043e119400404005000b41e0a144954015100c4c0201d443c10407030326a051000c080c1c02a411907109101c01c00152354046803c001c5264000042607807540d862030300502610341c2d002d003298000100a0b121b0107012009003454040107003640c0821603aa02d180a03159006100c4402512588050104a00a050048081c1d000c01d0003810700320300380356480740f01440d0440c050340107811031f9402282e41064900e10504000281c40702c1710007541491704090b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 659383767 1250 659382517 659382527
    0x60f1308120412150213060e150307080c090f0d05010228051605101d010b01090f1205100c090302010320071707060c0e01181404020c030f040806060306010603020406 73
    0x2030f0021345941080c4000c3c2c0c602900c80c0c0d04450030000d0721458900c0c0c469031404040c162071007034032403240140c0c01d80040003407550030306003240c0c42070540e900c82d00c080c0d4480c10140c03206d0341c100d80441c642217045202414420359400340d08002e003901c10301c0090f1f0307203c0240e4049840740e1290f18000c20707100c4480344401202a00041503400040d0354070041115071490b41070061420600c3c506001c4054507110802c03c07000822a40116a004500028401c0710300d2540111a142540e10403100300c1d00c0c0d008810720892081400030042c0b60b0040040f1a10102101d143c4011560400070b1700b0081240c0030740c1041156018050780510351100303940038000c000c00d4262451540305110004250150812041019506040980350f00581029040000f00031042d4058050104034801e0360104117600402440804103d8180d002d0380c0300c989481611083c24428480a90091a9542da1a01080c0020b04402e51008058401040010001d100f6818058149402e010041c1c00481c100b43c010041808600d03006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 659385017 1250 659383767 659383799
    0x501031113060e01120c06050f030604090302100c030f060603090f0b1003170d0506030c180a022b060608040308160c06050a060f090903090e06060f13081204 69
    0x68541e5000440300507010802450036401c03d882c800183c0002080c4450b030100700c41c245c2403081b03113581059522581c054a46d400b40c141c00c590640400c000080d450b0400d9040003403014885d00441c0c64552840300d020080c0c405100304040060b03a100f46a8000710314602414009220300d043c2003102c1e80f615114141d140c8070308640a400c031070640000c00d001c0580c80d00d0b683e00660308042c0451090b00b11112241080d40000e20100c5441c0c241000300f1203500d4003040c034aa07004401810b09608801c5c9582e5507000480042440b80034075400c0c800340d0f011105542c4016000c114540702d0b80d0500b41c5900004088901c19004101000030160400000a0300000f100d5080307401c04002e900d051084220454109032484c0d8000d1409052400b80412003e540e0071110942e803100f0348e5002a152201c0b1980104d035401900500041c095134410007501080001c42d0340c0240f005040c080c90304c0d5544603d0050703079002005080a40c140d4410030802504144007084450040c0110390740340c1460404c07055000c543c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 659386267 1250 659385017 659385019
    0xa0f03080918010303050c1c0503180c03010c0e1203030c0301030f0c1d100602032b06081507020d03060b0307050c010e0105011401090b120c0d0b03012d05010311 71
    0x1a1402076541d00021403190b440b01c0c01100c0380541e103c3c9002406500034200e00c00b020310400300748480c80c0c0c2002c0d4440410f244c20713996981c2156244e0344c2403c1d141843c0703200002c65004602404042d510280503060800615403620945201d1130300502a010f04800c0440909400510078030643c000c2c0e0728200c82c1100d0308000703104058160790400340d2100c6c2c81c43d4401b40c464001b101c49182c1d6044840c25084c032601c455a41c9003011a40c8450030b0342c580c4103560340019075031444100c00d040c4482145401d1602020080c1c0000d44d103455040701c0c1e1609c03658804074420300311203008000c0002c1e410003401603542410b01d0b052015500d80400124113010107001c1100340b040104030b22040b20000d510500d10300d5100d60081c445540d46000e03002401c2015041c641c0058418400410301410076800c03150007441401c1d800015545500c00c01c0c2e40e6400c0440d1074000161686034580d22941c00b40125016101075000302480b00c40c404204080c0d904040318503408060500c0d00400200d007a0741070307a0140b988 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 659387517 1250 659386267 659386283
    0xc0e0105070302010b0604242f0c030a03020105100f0b09010f0c0f061b030e07050111030408010905100c21021e07050606190806070e0d05060a1a0a0f03 67
    0x1c407900d0103034090825001c510350021804103000070f09004940c1b40c8400440c3c0d2065168400c0c44103d41100c074070307081c11052241c8401a5002884080c03040140b1101526141d0a88058a2800c1e00003030420f96404000c1d40180e444005001c016000c2e90140c1c4e000b0070812030201d421034605940b03011140035800c1060305010030100c6003028207025100c01d80c40709a101d92030002d00d00140c5007003030043c1182900030403101d1b00c21803159140c41c001d01c1000602c4019a00504001d4545001110100308002c446513480c0414040000c580009004403504c540c42200a000640824203010040301c01c00c1e40303004108a80e54416842c400b040d0300b600b0034402034061016035900c00c0c038142600f070402a907100d40f64a48000801e0014843c001c500700703020f03a10458038481101c00d4072182c81c481c0c1c00280030300c01032500070f0300104108034000c04030850b403090003411079104440700b52505401c8c00e80440d1840502900c2d40010142d840f01060080c010040491b5008011414000a10001e00250000404030a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 659388767 1250 659387517 659387527
    0x60a180507110a210201150b0d020c0d030501140d02100f02030c0d0c150603150906150314070e0907120c05090426180118051c050f010c0e0105 63
    0x540710b07400d21580b220b50b00080391900101031038900c2c418000503141c40030640204841000107407043c0200035141c010144000022824900c107050150b0001c0d00c0007500c554208400541907a00307008003800a101924001659803401040e9290ba4a600c10781b24428080c0c004498010780c0c403441000c60110300703454003544121002d00241e255105980e90a060391280310989001c0e01c0e4071186019240d44160b025101c1044200420800d8032200c0c0402004503401030750105074400c00341d110620f1070380541008601080c60101880c0c91310400d81096903840c2c03411682d40066801080510010107041003003608514041d10324035181d00013070186000e00c54010b01d4001c144103d0301d1000014180c000c02c00c1e049820249000104141d001c81a2a11704500302500180303920140240c030141100c0402c2075022200010045442c11440d032458070000000b4030020409480351711b10040d4000402c940940f1010b202c0c1045032400d04010780c1600c4684c108124401010340c8100000040702e030a003003080c0c403a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 659390017 1250 659388767 659388781
    0x2041a0a03200403140d090e0a0204030812011d0702030a1409030114091902010828050702010e160f030b040309180c1b1212020903060c090306060a1805 67
    0xa0511260b150019048507180d204452800c4001002100c3c801e00e05146101880840c098a42039440e01d42800f040c000b140800c188212601c840b0f900c880c91810040c0b805489950301f41c44c9400c0055400041c4051900500c0342d50130b88030f1404600140000344c0c03d468900190b0095030713071107500f03a0f520401000d00040c204607000c90050b43d03820130005000380706540d8181e104810008045070200d50600c61500303003000454602480400994060352107600d02da039806103004030841c902c22004580740c0c60b4807841c0746103000c601c10503008411583c00401c11045070440c06183c8001205030a203010310160040040c8108004128100da03403112200440f0f9450341004e03600f01403154410f40b5180c4100d1420210345840341e0202180200740d03214605030089080c148098000d11b80d0000b000012503c1c0203100441c05511420051822020090314100303406d4086400e140050783e010f841c0d801c1c017007540c124501c2c0510009030310032002e03611500014642000401003440080700f85004d281e03124041214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 659391267 1250 659390017 659390021
    0x1701090f091703040203010b0a060f080612030d0603060c21110f0c071e1d0c040503010f14060910090522030c020301050a060503030a14160b0f0a02041a0a03 69
    0xda25000103040b15010084099600316500071107040b8802d500e042607044035807508000f1031003a20020b80c0d13003411035003101c1e00c1136802e9280a032019610180c2808101415201040104005401c54001140c00c92452504405490003a12510706104051a0251a01240d03421082d0000322824000c222080001c030160b005218100e17029400210029480e401c020001541c40d045a0203c406080301c1a00300425148003141c600890045c500304040ca00702010000400301e07044140d0b941d01500d4035690310002401c680b05101c1c42e011813622004d95841100c900241c0541c40042a22654007602c3c110b0303031100c10140070780580814159100041001011824810034a2016074040304030b1140085c2005800c0703c0072404201c0c442c0d0300308000240c519650780615000c0b02c43c050019030502c0748500095801e006118140c43d403943c414414110340c017a414118000300340c01002c250b0510305000a5a0380002401800d90101500400c820068504890044821201341040c20703615031074034940441c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 659392517 1250 659391267 659391281
    0x6060203160609020a0b0a11030306131a0303030907062a17040e131101020a050606010e030a060507030b1804020d022704111206060d0f080c0601030c14011701090f 72
    0x90491072000300840d506200318020100c1c4c100390b8403231442a9003103142055413440700715403842d000000d505c188451944035400108c3d0040f49004401c1e01441c10101092940c3c0046903103014541c000001003004a801001001e2300c0c0180c418080c2c0100042c1c40c400d1414821900010004444070040c002c0030720401058401420040030103010604006038440d0080200c01300c207840340c500e1810070311038a41c0001094201d05903c407001e0440d540d204001552002e102d45040c0b40c15014004c1140002086d6214461040c6116280000c922a10005010300003e041d43c3d100a501004018000541d95a401814025070304441400e910391744480c00304082211070342c04507414010769090204003d00d010901d04a040700f40d078012603606003840490341c4c4800583d4040d812a0406482c0008600c150014140407802004c869141c035040103015483c24000740e106403428580114144091064841c12a500340801d1809003401d14a4031034455400c4418441e072820305d55149003940b02500c0c0e54003c14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 659393767 1250 659392517 659392519
    0xe0307200a030f0c0501030513020a0302240d0c091710020702060405030604050a060b2407020d0b0414070e1521010207030e0f030106060c20060c0d0e040606020316060902 75
    0xb442983d149400368400c2c0c82d41c002d850101c0d0408000440701810440b0000c2c580ba00242a01941841c41d001e2000d9424a0485000c8170b69000d0510440741400c50700601030300546080000d901d26004000908103141c47d0481d85001d85a03403002e03507400d840096180c140c6c0d070f0011170050381d44401e407001500c64411540001c3d05401524100170502a000c82c804003001c1c05040180103a160880c20800c1c040d003140007d100b68009445c083d086c00b0030040207003140c030344051700f400c02c810401d440e5524010b0f02190304440071960170884001381c1000b0300074034000341203d0444480301d003458080036590090b24480b140c02008440030000c0f0b4104180301c2c20b84d0240804000f10364540c2c40e401c0c0204038030101c04400380a07203800505220a820140300e844101c031615034824119040315501e140c2c9132001081500210070020110040c01d8ac0c403030340140070b4060f500005085602c450741029058688182541c0c1c851440e0001c00c106031070300801120401d505521340704040e0030f41e03480c2039002400d80c04400b03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 659395017 1250 659393767 659393783
    0x3030b0604030f050d2105090a0b16030501090c050a141e0322020d0b0a060b04061805030d0206010e190c0f080a141f0f12021813020d03230a030e0307200a03 69
    0x4801d908180c1c0b8bd44244441d2541e0307082c88180e0300c0b110380c8070580301c60301d000d540082d02c200301210246205400d04146205418041480d000300200624461781101c01050741d542400014481e141040c1540d9000032444000e8881504000d900015400c9400e92400b81180440c1070000d50801c58a901110151130070324000340e11292255402030004c4480009400424050040450309290008140040c103201e580202aa40e007004400c101026001d000c02c50501915806000c40d40480e0085103260065540c508070901070344880180300d0350000d01091403691410b00031401c2c070400c0c1c120f10380c0e000e0700f04004c0e00000d4501c40e00c0540341d552603910903010802498800301d030f95001090710091841c002c0340e0f88106514000b055000160381a03641d08001d421000c0424010700340448035544040c00b84c10000202d20000c145540b002c04039510009a200c0001150000d45826105800100c9060001582095096910400300c40328200303451000f00304810b503400807a61508064409140c0c403640e8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 659396267 1250 659395017 659395021
    0xb030a0b03160609091b0f0507060606050901030f1b1b02090f0609101512060b03190c1d1201270c050607020f0d03030b0604030f050d2105090a0b 64
    0x40b024050b1038041c400004100d03400c00203960303110780150410b5000032440720b003080b40d01841c29200070741a1052582030007401e11480000c43c4551080f013006040c00d469840d90b8580a5000404460380541003e001c06d01c0c01208507044102600c800310080000e0501816244d03014405e40103007007410034025400029442007100d403404540059010701030035100c180098903020352800750700c4024007420ba111a074609140c070308184070f10b068807221400c60400045540c5c4510b205501c6910484008085606448401c0d0400d58548101c0c50082c0701c0340787c0908002041012410035544119203140b10710fa070a50140440390003980b10440900640040c0300c0306100f00d54101c84080c00c90701c000c0d14142800000080d840c10030348101c4400307960040c403c1c200f01d000c010070003120784046c03031041d020181c0c0d50b0f00d56000c40d21a40001e10245010711506040030903580340080c83d1000b0500c0000402040241940504130070490b1441045401000425595541c0080b81d140c428445000b408400d41b00f42 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 659397517 1250 659396267 659396293
    0x1090809040506010c12080a38010e0d0308180a1202060906130201050c160f0f0f060801170c130c170708180f0a05030a0909090c0b030a0b03 62
    0x1009140406055405002c140d40349001034070400c81c45003010300500c3c440c40700c84254500ca9049143d00184030400050b04c54004070b103407801c41114403505691008407000c202c210381d102c51481d552020b030904c1c0030801c01d00300ba401304000240c0c081300101030000040120f6000340c0c43e0145a40700d015000c04590f10313400141007240000824500f0303440940105804a039400c50042565840345014130a6242124566030044529a20003003460045002d41812221b0030201410050020411441c04062031403c16400c1fa40b034000c1307030b40210754000c6041800c0003c00e80100419045403801d49a4a040c0c0d21540303212402d20214501a80c2c1c0f00820021751102c0301d0342c9520010b0066015550b0000060304500000b011220540b800c0e400f0604079070001d81741000f4004100c22520998060b01e64154914210302d2401c0302c00e82c42150a50008241d400340c00c0e5000c1c0d1940000d10003488107100106040e00e071180c442e0ba041c05140050400040040c01b40020b982240e01e000d203002d42280e1400e21041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 659398767 1250 659397517 659397533
    0x6170a0209010902040501080f04030509030d09091d0703020613030506130b010e270f03030108010207110a060903062003130b0a1103010e060d05070b0c0d030204120f03110109 77
    0x1000803407188604200106200c00f2610a442c245e45068540504549440345003128104008200300c0c01c1040800121030991024800017140079a661520300d515402c103040c075010344240040e24140a070038a651625140400202281101e0301550301c907076108841d02e80e01211507041d400c090b06038420b000c14860312207c0081405050b0f40035441c900c110340d03200e010890b0801c40c140c58a0031402c603000011403102c0742c004441291007034140111803000450207129421a0001d070b000390201e03540400c844c400d1100503616031110301c004807500241c4a040c00350140118030140405004a80d5824181d6868880310042c0c0c0e500050020b04280c50f450701228440046404020441d640c00000b000f1030740b5000140552019180c076403001d0742c2140e0070406001c0207100c00030407280d44001000e00d8003002ca41306000d40d9000e0441d04600d40c0c2d0300e250f00440d0783c1c588400324181c401010710420081101c00030300000c0c0c0392a02e911280e440149200e81c14100c0780c08038001c112140651078100e4901c1046804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 659400017 1250 659398767 659398783
    0x170301061214040302150c130b0c0d02070524040b031513020a0507020d02130e0607031a10050a03200c21160624030203060f0412030f0617 61
    0x1520003800700a818002d0955106002e40d00107000d42d014090200d9030000703c006103a4041640340411b41803681c000c3d50f094500080e03034001800c0d000700107090311100c0f405010400745d01e101c6000611081d803a0201190b5070030259805141c140014403100c8000c5441001160000c0c900c100d007554985c00c2c080d001c560309100f0000344521452883d00405e00c40109402510055203007078884504000e466002c2c42501003001c0000c0340d2003c815000844500001d2184a018880100c024080c61500e5100070301151031001b443e854201c00980002c90b956140c00c1c000700700b200107103082074452640490540140a84291501d007007804c21075440d1a030790740c13030014006007d21001200d004d00d0042d072403a54004500805081d49100400840d0a25440c0c03644642805100300000070300b00b5206543c0f49000107003240c0110140004403000c0096180810400d5042091140c4402030390406a4070070160035025110301080c140c540b01d4040398006698000002800300003e1a507203626101601c503262014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 659401267 1250 659400017 659400047
    0x910050c010e151308070606030308011d010b0702060c01140108031e07020a0302012f150a05090a12020304030c0e011a0c03030f0606041508060405090120030417030106 74
    0x3a00c05114a008000142c0500d50b102840e0321001c207441d035400d821304e10088510103884007141000203500051051043c8401540a035651031490350400741841c1e01c2011301400a800d480d5024014080820100c0490381d44643c100d410566903000c2c25540b034058080e2050800584050000010340c840c0040010201e691000c2d80c08611703811002341c0c0840c58042c000020390062483d080920055000390510485054080d9901048520701c4055880c49109030044901540004214450240c40d11240941100c00090140624680200e00359503031003a898020f801d4403c06003401079254005e108a0300035580058500316440d44804180780080d1080c401d0009009080301880c9410740c1e00700648810710140f50156165807030715110901a03403030180c01d09a10010800c80009c90040b00720000d8031501c000e44840d03800789003a03000c21045810080c0303104e034664107010440f0000480d0955400b0340304180d00c4099105c0e2241e080403091107e09107541d00d82944c0c000008201160041c2150340e110394 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 659402517 1250 659401267 659401271
    0x5030403022e0e101d06010905091614032404120e03030720030303060a06030b010e0607030e0a090e0c130f05040b090f031804020901020a020316061815080403050910050c01 76
    0x3600d01c5c900c50064081c091014242c0c02c80740051184044a401c0150070000b00011100620301c2910b00203580710b103070b41c80350300b0541040c0e032608200e08060042e030501107444407078445140b0382c0c04140c4c0c0245034010300080008411100c0a2092405040e000700b01da5006405c03203444608600c4c041c00001444400e1603020b004441d21910a03203000006c0768030989026083d0000e461820034140c01522813602158103100c0302c40e02a01041d22468084c1060b00d00940c0c85442c034440c05c006000f1a401190840c500d00c034105001c1e540c0121001481c1d150305603050300d0750222020000e40210003040101c04071804c150a0409100500640c004154050300131442907610464444641941d2449002e541c840e11018203004c4c001c1070700c0c090740600300060060055541c0031110b6400242022040c05100f605c01030312a030180640781e8804003a0b60810b280c010540f5540e420300c400f00020503103110b1301000300054200007404040c0300b42d050340c00c401301c0540101d400780190000a0117542100003d40410341c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 659403767 1250 659402517 659402531
    0x31009050a0902013c17060102070b04051315030807140309030715020f1609060602030405031002032a040315050f071101060b2805030403022e0e10 65
    0x2081c148181805075905171100c0b500c410500c8440f000400603200d400c216011215190445d0404009005990442c40d40e6202c140c114200180c0070845805410b1a04540c0044414803c0b0f01341801100d00b6901d00300c1d14002c030100086084000f83c2205904c9456416400720f00004002020001d00001c0c2d01c203403040c40c1c00d001c2042c1403560700d01800340003d031300da03003c9a4100218003000805141251062040c0c51001e0b1351404a5860404c000e503007401444640703c0c01b002120740c02d00c20f48000d064a8030117140742514040000c0c4e6940c15040c006176001c1d03400004a000c2c0c0400d0110000c98200801000d00d0b4088a1480210160045e00c81270310030803031a558480c110102840340500c0b032000e100310120140c985c100700320b9400700d800c1d12140a5659502c0c1c00704034011144058101780e100c41d84018012913907692082e1504614079000300a00001380300340000682c0100303601e042151141c540f07144c80c9000d01d98000188011f108410f00fa06d18086c41c05000c0000894216140c6e20909020700500f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 659405017 1250 659403767 659403781
    0x105030a0f0609230c040501060903081b031905030406050c0c03030a0515120f070603020c0d0806010203040e090114010f0b16020a090e030309060106170403200303100905 75
    0x5100403000240300707105010124000034680e9001400707841c09840b50320005844081c0e040c0c100544503815051a9100030030038120340c030b0a40100b40c0074003134a113404400203141d035403519980c1c0a560203940d00100130640390446004100180c0d4140c804200c09942c86681810300644143d00c1990241c4100d400c010000d4904401102110713a0314580340000c6181d6510740c441c171802884054480e01800d814810004256984e0611001c1c0c00720301301c009003500014070114070303241065a5221005060042c85515a09900860b0740100401542041d40b120f51364400100e055204503003100c490000d0380801e2000d1800c05500800e0b1000c1c0011201215076295003150300d2010345481542c103e400200000210207040c8080311030500c0c0302a2011030501d4540e06c80c00113840020b130482e40c5562001c410041215400c011150050502c0c1c14401d1507000707000d558902c0d60f080108040c00b4041c1d020740c8919849480c070b031090442501d40040e26224106a0b8424503101d50511403c0407040c101004a130710307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 659406267 1250 659405017 659405023
    0x15180606011e0903241d03041715070905041a03060114010c1401090b24060c10050c0901141804151d040201030e060f01062007090e06010503 62
    0x40d001619010060311034140d4103031100c0e100c1840e8074100510b10b0300000c00180030702035560b915080c60442c0d240680e82699103404070745544000130305034026141e5240d940c030404000ca4040d151100c0700610802001e5a90900d800243d0142c2c0c06082c082c1010230040c0742d4800000030544e8801c80b0140050301860005044400a503021701d1382c95000300c0e004109106162911001e03d020605029503107103a15107070702890038003601020301540d44070b03c040c00400544080f515445850580901d900b820503e060b80552260082100d000b4000011000503081c4100aaa81e040500403424000c629254080304c0c2550002d142c0301d400318010001d21240c40f40807205540c0c440045840340400008044100000f90425030304400103c03d03141008100800b00c200a15082003504120820303d01f0300340300040490301c0d032601d984419080b02e82070116070801a2001c7e411245c2c0c0b45004803100c01084da40c2c444581513603101c0045442191030002d4598060740000400700051410744000f07a80c0d0344140340d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 659407517 1250 659406267 659406271
    0x103021008040525030c080f062a0a200c0f060406171008120702010e040219080a06080a1b1a03180a02060d020d0b030c150714151806 59
    0x480d5400034000c12029030224001c0b0104c100c01104040b02140d540d88030400c000d561500419600d030001d20301014a05010801c05821518460683c9442801034107440821861200c8001c0103088c0051a00030a5101c4d02140c3c141051240c0b5120001c1000c0c10001e607900e4044102074000d400305100c4034490701e80711069034202c42d207075240d0b0b02c0404840c1600d903a00c00300050041c40604d0b09041301113400902004518007006104032420351300e95072800054600c401c14100540b00714010081603d81440c06800246032000306e0400b043d03c2d454841680c00130b0441508141540c0c07003a04c3d030400910140e001c041ca082d200d100660080c4039212001030b402201307031101c0543d101000300301250201212400c00e010141c07485098a01110040d40042e01a031310405504030900d40105404910031114490001d074154118014218641c0c00c0c07021446040c401541c00b80641c1002c2103050038020000007020400c0d44850507a08200c0764001d042c21014010744840046448400204942e124001160f43c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 659408767 1250 659407517 659407523
    0xe0c030c0109060c051e030414030d12020a11160611031204020d030921060b030c1e460f052704051e0703020f06030c070812010302100804 61
    0x8200c0750501034250f8603c841310320704940303a00c070f103065001d400300c3d5907400d04044040c8036001d9503403945020b07404403001d00007070b9049100c0e0b0000900d8120032a08500d4508e01130b540d203480036803580c0f107070724080d10324410700d00307280c030035401680c0c0c4440096500550500581d00b15454041c4e00080d1095050b55a0080b00010091074890070046000351410380000c4103660312901d0801100360b200d64a03c46080e0803580b0250103401e07a81580030400c4200d000701d00c2050401ea008000305d04080700024100b10301c2001c2103c03407841c01c41010140d13031142d812120703400c5a012881d80301c00c10307800b1020f103410031200e0342c95501075515449401c8a800c04024101203400c2c050307a403c220b5041c8410000c0705007042840350310003411a0a00c1007554001680740d80b0940c0918058485000201f01809641c04c00640044c00d0346c002d0320052005a4409508a0614401741c480940702d0380d41c8460a4501e215200f4091f194140100e140740f00c14684940d5a41624802e1b50440d515403807038030054801107001d82c0c0c02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 659410017 1250 659408767 659408777
    0x51503040206160228060912030f0f0e030604050303010608010b031015030b04090c03060f020405010210020d0902030a0b0912070b04030e0301060b0406091d0c1602030c040f0e0c030c01 81
    0xaa8103c5941c1e088032900075000601c200315401c1c59059420070810810454804101da5100c1041013039000344401c0c2c000c001d01c0c1c60811000c989075a000b400004803000301d1043c05071705c2098004c80b6200305071103550400080d00321507050a1a00700030303076290400d108100c00110721100104200c0010401c1ea070080d6032300540d040d04507040c030190300200019401140d01b01691784200c2c945542e694040c041c010f600500c1508c0d0494254103200707050b0380b50a00d0ba100514010030042002c2e99000452000d5803c01074001605d0f0803489010201500070703004043d60611500b0012001d000f456492107029400300070403035401e1850501507001c140a0f01c1c0700507148651000c00503000c83c0c01403001c20b07060f4000400000d05180c840150440507089500a00005035a03100d090006901301c2d040030a295030f02c0c4900c800c891402c0f6180c86624810040484003915150503440c0854030204020070034801c004109100803620b69800304d0040c801c03043c19145501c0b4564201c184c0b41808510303c00c03644da041c2c0d11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 659411267 1250 659410017 659410027
    0x305070f05190b0901050d02030703020c1e07050d14060705040f0618032a06110c0f0607150e120d0b040c1e0e0301021306020d02030319180204060906051503040206 72
    0xd5003d50883e04450781442800c003c001802c4503540300551054409840c0142c0b283d0120300c030a840c04541100e41680d060603070034001c2a40000080d0032003150f00c00c03079198a01d40001d02d0540c075180f080030364040c118840c40e0107100305079810802610984100c51003c1c030080355a00380c2196620500048c500e42da0304104014030104900450007404a0740d180c0380c0850058000703460209084c03e950041d80011008a42905191000e2080c1c10041e082110169643c044183c0001c1492240c40c40c020080e0b4048c44032040070392042c0e00880c0000f6080000d07a1014440116226500d41c0700046100702c06103040c2d9044c15a182c00d1203810009840c80e0f80d9001004082d540c03201034541e00240038014032140020b15030b00d030380e406d00040c120111340035600d0803100e1030a58003074a040032000c1c0010564000b80100015801c0103d0210b40c1144150004030740540b140030300340710058180c94065000781c245040414200915045003044030000c1d140040c161b4000d0080c0609d500094400035402041082 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 659412517 1250 659411267 659411279
    0x15010f0212040515130308300a05041505070c0317070f0302130306110405040c080411060702181311100c060b0a050901080d0e1005030622060305070f0519 68
    0xa441136410314100c4100e840c1c001140c645907482c00d400d038400c4444920005404901c80c41c00340000441d8084003014800c041c0804496540c503205c0200002c4131150340302c0c006028010750007449410410b003200200b0a034200403030002c0008603101c0c1c040d00840c408a044c222405d0205030748621654640d42c41c40d450841c0b04404801a6104d174103070a01c0c2c003540d05000700200c1d42900c54424840521a11aa42c952410f401d0009440d00c64030224240a0344030f00700f00200f103c0381018203082008990080e5a00f02910010f41035401c03c3c0043d842e58000242040020f60100c0040c9900c180140701540e60000c10200704001c1003400240c00c00000c024282e40c2c000101c290308070300300b0300300000c0284881c1c0e9291380110300c0c0c81c5026402034038190b0100b203000450981046080001a600759001c401000710700001911350b1001404050007030003609001d040c100c3c2c41c0d02d003030201e80e2407200040c1300c0c0a0f601e04250381d491042e8007035041c00d0740345820006110318040c40200d0800ca001c0d031022003103501d040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 659413767 1250 659412517 659412529
    0xa02090a020c031204060609020a020a031101060b0c101a030706080a020903010903021005010605040f03020904111c020102060115020a03050d0e0a0f05101118030a0b15010f02120405 80
    0x50694000c0316024041c0354003070581030000c1c0c01d41d61407a40304409246828107000054a115600805180d841000f1610050b40d0103d0078401c003c5d09400c020048040440e0900e0040c12664041064a00c003c1041145000d020442e1205003501c0b110500100c0101c0d0560080301c15181e400c035a15a0010800700095802401000d03880542d5100041c1826104004607086d10a07090084006070805c0c141480310004603ca140d000d0b00132494410b003403a080080a09104e02e00e404040c0c45030618100040802c180e40764010709100018000078521210a00440001010006c040707001d4013500c000400c500422a0042e2002e401942c000c05207140c041c2c80582e41ca80c02203820000721512a460401910310400c10914014419400c00c0f0410110781803035400c141d25420001e0080342030154440e100c074010004d0381c0c04082905a0180c002c01145c000030316141c0d51141c0104110b103040b08000c00030280c01410003100b0402c0c0c8a06e100c2422403c0202d883d6241800031501c00301d0140710134801e6044c14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 659415017 1250 659413767 659413771
    0xb03070b0307200609030901080f06010f0e0d20030c04111b0a050d05040f0e07021c0e041103100503030f1206011b0b1b040e360a02010f080402030a0209 67
    0x2403c41038801510f06001e80d0410348100d0300c50705540d000180110607542d004800a610941200e414000c0d8200200000d02c074180c41007100f01080101329000340b503640d8810701800201d44c000100032000442c1203015502c00600c0d04054400e00170080080d0641c20503008800286c80b03048400d520741078944001416862441070103a080d48118441c2100082041062040d510714980b1000d841e1403804029604890071a0050005401200c042c80820b580001d6464036000083e43c103107403c03246612049070844485194640d02c6820f102001c07104800c000700440c090002480000360701511802450390328454458800d051520810030755076403128010f03200340c1203a03051400e044c5080040239940c0003060352580966501070501e0902c498803010380d02030328031080ca4410343e9041c90b05c0e00b4400c107031616005048484400c00310001801e500d1850304000000f600b07070306071914020840c003180780d551405038604a002c10311100d1280321042c05080b202d07110703039401002030418400a030300b40b09641c600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 659416267 1250 659415017 659415047
    0x70512010212040b0c5212030f0207060615170f0a020d0207290115050f09032b080408030604020a020a060c030e0613031b0507030f06020d0b03070b0307 67
    0x8240001c1386111058046e544103442d084962024a04a03025040c9110031110701281d171404003500304030b4900403000f5440f580c1d1500003000d41200015000e060300503062040c0b5114600e480010204108030f520ba03c01810f4680320311215001c42040c510940e0220301e40098401e603c544800041d207801e50240250354008009100941032404400b40070741680c00c014000c945c1006200c611b00b004090385a4008031140d080d00a0640f40d5152043c040000012000c008007042000200d2081401c1600101c919031000602103c0340b614200c040c0c040f014424800320b031400480d00d90003210305441075560750b0260f60003503240ba2a5440b00001c2000942c41064102d095000761800d450107c0d403d071048821903401c1e0703240400c0d854540035065003070404c02820005401c0e42625180042540400c26a8001c106a800300c086441c1c103050003490300100d0352008103200c8403070702d041c010070110b500a009000066075084c410045c1e4601016100c101d14010b00c0c2644130b00b0310000c1c0b81c951154034103500d0406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 659417517 1250 659416267 659416291
    0x6061003060b071109090c01080a020705151e28090f1406010f09022104080f03042d120f03020702090405010c18080a0f03140a02070512010212040b 65
    0x15070b5404001254101000c02e913014281030100994506180070307141e600000b040040c241c038206080020300207a00280412010540c00308186040000401100444035844020601145000e81040c00c10801e0002d02d90700844085c0c02162140c0c024540e98013180502c00c10060301c181c2d0711074001c1d0007045401010342c0d12201c45247c3c8400710315000c1401c0b180ca0312250280400c1d60515816051118880d80080d403290300c108230310020b20a0034025400281e5501030500500c4e10746080200242c001c40c603840f1140310001041c4010800502546000c0510500c207000110701c02054000c484c540302000645035106052628640c0351252034060307450000d500300182032407042e80100b800d65100300c60423101d86c0e55401c0e00e0a6001d4105c0c00c01c807451286100c20b0ba400d24180600b483d01c485a41400412028140c07000301c1c10540281e10b03034040782c40144042510b802d41c2100c02940e8010300e02c1103500a00f480032000f0b14000707042c000c40c1d69500c0c07401503d03d481d4443d941c5081c4a5000200081d513600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 659418767 1250 659417517 659417519
    0x24040506060405220f11030313090f060b0d020301080d0905032d0a06051b030606160828081b220509130b060d0209040b0415110406030e07080606100306 67
    0x1064849110031018017542e140c604400c1189400e500c0c80100e0442203109030310620001400800e20100c8070180c1d06804404500c06143c1003106020b810142c01007500c0e00008101c0c2a40078500d07a020314101c418503001c851803540140016100f015075800b540d40c058020020400c29034103041c80c81e150035148681e08036120b80901c00308605006900740e0031600ca903201e0040c000141c20700d1142244c2c0200350442903103941459400500c103841409643c001d1204281e000c003003403180b16070545100b5180510a4500f40300d035510466603060502c40e0b003401040c41100800c0d82000542074040d00b001801406514050400da200401c07054601040d18196481a001040503107810701d031540100c2c40b188a518860810303260042054034010045030080c0e02890b4100c1c05644c0e503518a942040d00010310010b16200c0e4144045234414420501010a040091000c2c5c0c011150000300708680c1c10b541c0810201e12045c003123503207417040c038071801a183e4410404504185000c0c0340b64204881103040002e402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 659420017 1250 659418767 659418811
    0x51306140f0702031f0603031e05040e07031e0b040c0c0c14031e01060e071b170c010608060a0b0d0f0201080603030c01060608040201090801021204081305040e24040506060405 77
    0x421a5142080d103406c0d29030004008041d0042882c9082c0034850ba20b0718100c25500c1401442c40c0a6489044208800c04022900340e501a6001040724002441c8901c1d02c02c1a49001074058030340711042034001c501d08540c080420340305910441003158080c1140d048a4504208050000e500700541c0c4c0d41405117850030900500c07100a07110102c4d500c0b40c00400d05c58940807001d050309000410f100d09201c00c00d20034203542c80b201900b00c2c040c10361040000e0b080c00068603003200c280c003900c21004410342ca080c0004c5200c0200080213031094214440c18451200c94406019225114250080507a07005006010042d8003031132000e6070043e0050112403c8c0041000f4290968900b580407501184441c0148401e5591203401c0c9006403c800000307528054905c030074000c0441c2d0003070005d881c07100302148804074418504808002404000d0091000c0702c9040c4030291110b001458058a00c0000b1000400d07034180d20f01e400d4030036a040006041c5960f900f4042c00083c060050030081800c168100c06003003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 659421267 1250 659420017 659420053
    0x20409050405061b070308010905070504080d0e030d0918050a33050a0e0601030903030209280509040203030712230909090f0a0305070203030f030106051306140f070203 74
    0xc0345000b100241050b0509681c10107498041c2ea803a1103c0300410401500402d4001800504407a256200040e01c1d80d1031840869450140713070070110242c02105500440c10740d1224000808800460076034a42c2c202143e411360b2010b0302d521851400014080c0f403440e400081e43e04c0254803c0c9512800705a100350001440025508100341c20005000610560b4150140400d40000f5140035640c1607241810300e103c00c002124020030840c1015120340303110f401c152183e0140e1310b4404010380507118500c40b00c2d207604103440020445203031440120a000540d80b604041c00760059401030702071440c000c1c05884514158990340c10358014054882d0080103c0d07582c07600b201504640344c0d4500e40d102c0103000108222000013034200411903000b0304000318205000f08565800b6035042c10407542c1e8030300c1c500c00309045006005000c0c90803070340440005400c50f00500148014140e104001c0412920390030140c405103206181710402900030701c440f1035072100401c01000341c640014200d988481c40100030081d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 659422517 1250 659421267 659421271
    0x605090307060623060307080f10090213080c0d02090720030d050402030609060106090b07021201020a08011a1903090f0f050c011d180403110304142701051302040905 73
    0x4180c020003d100454a00b0b8103c04c500042c0b002c5442500d9030070100c0c0300800800c40502003c601030710446c041441200c41098510003014040790564a4104e04600d01416045500c21460f02d8080c1c3e9840040c9494840c96005404c0d600518010f081d440f141c50444155070040c0d000e0382e036520002000078420f0780810161221030304403100801e11340381c2841031601740000034000f000c15501c07400043c40044c1d08295440f0036590b808410f6520745c000303030000030540c40900c029001554800140003000940c40030303943e81a40c80965901503c0c41f0003408135842e92280350700f07411580c41000f5442d4501c83c401d40124400038064003000c7e100001d552140500340c500c0c2e40c0c081b603803a407010f4060300055810101d0f80140d4060300b004511a4050035010461941888981c8550100100c000804040c0688020034203407903800126a212a250180941c2a040001d00c0c0e80c0f140e100e410070300c03451410006000069017107181001002c0e07482e01092040e0001c0e0325512035803240c1c003400042450116441524 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 659423767 1250 659422517 659422529
    0x9031002070804030c0e06030715030221010509090a080306040f0605030636100b061b03130e07020d0309031115010e060603060d141c17091906050903070606 69
    0x43c0da82e0700c1e51401010f01c2c00320380e001c0040102e011040022a990109040003268034070300e111012402c600c14110700134412000b1055239641460b074807d000340c440c0b80392107050b1541590003449549611000c103682e50394144004080c07070010400600c00d8100f030341000d880210303056004035525455800207410401d0450b030040440c0100c044148141404621a440002222042c0e4000f02012000f461322040440032a5070045d0b21042000300c90340701e24084504e103070a00c140d00d90043c89640421922940080b94003e41c0c0403140401151004400d0074150007000150002c00c42d40c0c0350040c040c2c019100801e4140d0a016191348130300c445803020701218154402104d40043c040d8102069404a190054051400740409000700112600d0324144020700c540c010310702003040f01d075400c1e03014071b81601c240e803829841103070824030a0415001080703020000031151820a00342d40300c041c40d07990344000403030001e14641e8414030740d0042042c551040303401c00500000e8924000c0c45403244000d482d060340c044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 659425017 1250 659423767 659423783
    0x7080313240b090c0405030c1504031e0317060a150311130501030e01180f1704150f0e030c15040803030c070b0907030f02040f0b150a140304050d050903100207 70
    0x424407616000381d000b13910910808000d0706140c2028082951800c4404409008581c00c4480c10b2104030305000b070328010b592000c210f0303000c0101d01c20405100e084a48044000c154102d5170381b4100700381092417138410300001d00904c1e051841d1441c3c0c00048104802c1310800c0c181d40d190030f60300040e000001800920a81e404070112603140c04001422143c1564104a00da45410010300da640078080720445a5900705c1c190072182d0449040c0190f40e8126121496610400080c000402519140d0242c48201075a1a24240d8030003256054401005441e100c6078541c0010032950b00501c1c00a05108024100c04e01060901e519003600a1865200341c0d50a4a44940403c0080403c8a5441080d80c08001c0b00040c22190740766540714504080a43c0e0024844d079100d82c103860782c800d442c0c0d0264a5582000703142e02500c00c20b209510003d03500040b000000513501d1a0b0030541c104220041720b015980c498004e01c80300070384120880700c54120052169142c06000c0981102500d0380c009010b100780180340b9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 659426267 1250 659425017 659425031
    0x150a0c05160f0e040b010b07151802011d01082805010e0603070b1e0a14030a09140106140907020c090108010f0f094106090d050708031324 61
    0x307100001410703921a1803080c3c403071010040061401d098582c1180d4003801030700d4640015140811003410001100c2003100c1c9000c5980b050b0040d604240d20710b85000382c0b00d10256520440000c491350300525940c601040c95071002c00d5910f070803017a1140100841c00308980c507020080114200313642080e40300c075800c071355890300780100c0340703800c0c41890000d10400868030314081c035810380d9181e4010202c2d013062081c03001041c00c500050090511030308207120000e0180d6249841c40c8180010840c03e032042e05c42001c5041940318040e030510604055907111400c1640090320b040070441000310042181d000c60040c804100d5440d10b80c180c0ea035018144c644c00215450000c1c1c0d00c2c840132901264030499140342016515404550781d00f402000030002030035940340000f805112205180d450501d811040407000b11888001e0101244540c0990b034101c0603907119100b2500101c0b06406021805480f20b070701007010450f20300e8411700c034041c03440c0319940000d0440c1e1103c2c01d1000c0004100e41d10080207446000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 659427517 1250 659426267 659426279
    0x909030201050405122704091203022101120803090106030503030f0a0b1c2310020d0f0c1e12050c070501050f0106020616031104090b0a090203010302150a0c0516 71
    0x21180c41410400160606c490f135002400c03c019512028641d138680740c00d01e525140c0329900a140d00941089821078080a600002002544048400e00300700700c0d04e000c407041e84041c0211460480c0c000d401107580c02c00382603c80000c1c0d81e0002c0c00003400c3c0d40da500400000103109101a5214201c0c0394402010b071310380046040180c0d844082c2980c0304180118030516041c143d07201c159081c0d5000f1154800900e03c4140621028400d010103451a101d0900452040300d19074005204202106009100081d9a170341c100c803da071204079006001c40c5844500c40c240c4a098a0300610869041ca00b0039819807803640140f080320001d031580040138500094210a10509001c1e03903400041e40913441101c0d62414000a49410380506940303045102c40100707840c0c0742d201ea080404890050b07541142d8803179480360f0141c01000d10052240c01540c1d01e00000919844602c243c0341200d030080d050789440c8205803100d10803540454420310a002200c4074540114404104c100701002039044400ca049007409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 659428767 1250 659427517 659427523
    0xc1903091d040209160c050a051c0503010b04120c0f03030503060f060723070e13030206280c050f0c010c0306080109050a020f01090312120b0d021f090909030201050405 74
    0x40c803804055a1800d0622005131608074019030700444000e00c0c064030503ca480d04460400c1e141801810501c42c0290500502c880420481d1010a8002e1001442021908c040c0c1d6540401d22942804d918240000c0001e0042880e10351820792140a0180c02907444801612249029403c00c0e00098000b104010080c1051000c01035013140403652141000000d58408035407200180300c3e00704a2201d141c14007101d0104001c01409000b01a2401c11186414191500c05001070342041d4014451300000c5260503199808181c4507100e80c4505000c00ea844000d0400a803001c7c008900400504001102d450904030002e44464945a0008501c3c400c0e00c000c0201503a213682c00002c102d900d071071000d000207440002c01e60442681500c8900f50030b91142c0050b00d1128142c3d1000d89102c3c0600e8402d59100e034402c1c4103054640b000d490402c400070a00051040e08014140001e4110784480300083c0500c1d0b0440c40840c90800c549050400b26460300810f40c1650400501100940e4480080c0802c2010038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 659430017 1250 659428767 659428799
    0x70c14040f020f0304030e04020903030c0c04200d051005090c090102010f1a0411161a07021f1d2401090902061e0c070e0f0a060305060c0c190309 64
    0x1c89410340c01c02000e020f030140c0c1e6100160004041c40b070144612034407a103490b01036a00d01c027402400d8076110489003000c40d03140c500000480344110729008801220801d1014500980903095060b103003003030b0000c41c2040c020000580700e2030300030300714901c0040c10f5968540d00600c22904e640b5040e4480741e0000000e420740d20003440080095051090198003440450005c015030300c7e00303d80114502d61500001106845540701c1661031820f5580580c0600c01e55802c0c136010a42c2400b5600c110f6690b00401f242c4450194a0101500180600c04541801a82c0001241c2e11391244040c8018201a0f40c0d11300e0020081502203007013000040e480141034003200700c58014199030406108031240303940004d005204200d01d03009102054411100381265800985042c070078010f08844101c0d464000c0718803401d508a07046148580c0760400a0f94a0b40513000740c01c01c60358401d00810303003034884401c04282030f080a020380b4013034800d0680c00d42000d05424841000d10380603803128a1030909100ca5012502a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 659431267 1250 659430017 659430041
    0x2030618010c2111041203081006080910020912060a0606030c08061c0507030c0305070e0106021b0906030309030106090c1418010806040b1e040e1504110303070c1404 73
    0xb00035182000442c8058806003844003581000803c4d05040c40244650b000c0d03900088825060040b1840805400c4459203004891108140c14020780c0e03010700300d440c80c90803075001006030012450b2462842c401d07000740400c410000d1450007035040b2103650341e00e4041e04459400300e82e03844a004010450b0503215104050b81549090040c6140180204845241040d403414201c440c41c0c03580d0382401420f000031005580c3c080440c6805958030b05190390303103850602401c8103009600d00000340d0907000103007074104801e0103400040c1c404200c2040000038a80184501d4041c00100b04980e11550203200e1240035004807440001d04c0740e07054000618202c4506c0410080c01c01c100703c5211b890b00421514004aa82468040c003103544250109016203821070340e0340d810032414080322502c245840c0c4000ba00c84401d4904000701da0305409003030764a00c0d6104241104070b8905003ca0b020401021541c00a00400b804491801300340c0c0da916a0f007012070350301521540341112410311051502d40128810038007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 659432517 1250 659431267 659431277
    0x210030506092a070501021605030a030c1b020d030e10180602070b070b06010c0231050c0a110313121205040b0904020a180f0302010e0a08071205010902030618010c 72
    0x10760a44140f2034003000480c480c9003180801c51074104942501100c0991016190110700030710f181c071701241d490f04400940c1c03021074104519210082e101daa6034903010448640607100d03035545074091152003100714005808005035944c0601080d00d40d110441480040b83d950f854440c0391120050241d659550805800c54201e40d10820903100f851003564007480c3c000002d01301740d880d0034005849001701003a0003908500030a2281907030301050250030710311000303450038a40da980d880c1c2410012501d04a4544111100511460644e0362007448540000e002c040c08407441c05503a43c640d2440c0d241c20340d10131214212001d000c5020403d58800b0400340b0b0300b440c01c00301d09090608040100074042d40d0141401580d01141091103148140d00030481c01c01480c00100341c06441e40c1c03007850449c0d0140000c1c0e005c40d1404210b0b001c64100000031400312072002001c2d00c00c4600740040c00000c281442003d884940d202c5080c9005171381c05000d0180144124103030040084821100385003075888210041007405 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 659433767 1250 659432517 659432551
    0xa051305180613090b0c040801150f0911041806030c081b01031a12010f0b0d0210230c01360b09012702011b0305040501030b0d021003050609 62
    0x710703a409045400400840341d85000c100c910a07000020001c110380980065180b0003800801d04403080100107640700ba40c001c3c09034821890f0340d211640300900c580c1d03444440a0500b00711540341c6a00c528512003440000fa1700d441d9071400c188070410382c1540000c9081d6951903040040104220600000f440c240c00034114a810b00100503008107c1c03030070300c28141901c0c1c0ba0080056044c4130841c4962031002048200c200703d000c04213600030708101440303054030741c603080508a80c0e160a00c0e8014142d54014440d44a41c0000c2c43d040350b12010b06c80310040307040c130980c43e083c03090041c0102030600c10b034403c800001c4450350301091000f900c2000c3d035031032048541c80d00c1c0c0c005290031745190b8224554000400d41036a4484401450041c0081c034a141040201d000d2215440100c0c43c40c8105168004d0f40c5401080610402c4658699120b15005001c80d008000802195009801142c2c101800605600548829401089031401e022003080c00080e95070003088000c2c5031075a507031038015100301ca0701c0e100c1c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 659435017 1250 659433767 659433799
    0xc041205032d0d0c030f0e161a070618200405010e0108060604050601110f2103160309030e1806090114010c03081f030317150a0b0a0e03030a051305 65
    0x501c41d005003205880c0e1120390004506019401546c0b44214041c020008202241c5d03402d0748500030304d00031507070380035001c840090780340c000328a040d440000f11280c00380b902e2000c6c3c0c0c84000906083d002c00030f04140c4416501d000c103802007551564410044c4080c10151210400c210807035034142c02081c0c40c298080e005001d40301b0001116a4030031002d5800003003949403c0c0040c0c50141d00581304000c0341c403882100841e442c10108240d00014402a007188070507400415840842c00b08032510f450070010490a06545c03031007a0007000c01c20f4040d0038000181881d200102c0c091285c41055404484020020f1040c0d03030030007501e42c2e80100000c005080070070000e503000a180e0101f4030390190402c1018004640840200d06001072a080800042500799030b0340e01c1c1c05085450940c4800b01400c5100002509021940008555200d401024010000d051486a04841d00040c0300c55080100c0462041c40c6900d080000b000814015241d2585502022106000f410b10681002e03015190014110f101c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 659436267 1250 659435017 659435107
    0x12020a0c050904030c08030a0605040b042f07150b1309110f0112050f43051207030f0e030915070503130608071e020c090c04120503 58
    0x1600c00880d1242c55548a81c00c084442c803a441d04040d16100c0d0000501c070061085500070801c0302c0042c0c03410b001c80d40b030a008100440b101c0360385000c0e035100c03403420a0b4414420381e01040607a809003101275040c5900340d25001440d40442d61a1600c0503998451546a890181c0700907071943c050b5a0140580081544d80103400c00010a01078000ca401141441f51a8080d02c00e81ca54440360100412035450000109514460141c881e190b007441c0c6111040c10f002e03420440b040725200140044440c550381c81072007410f003919a24a11080040c00e00821240301e040750103481c0910540d50f004108030194140c5001114a9070580505550003001030341c0d40307501c500092803c2090441ea129407900300a00b80941140b00d440000e0100c40c9400320041500e80e04002c02c9401062140c1d42c440c1d1609030380000d56051103903521030b0400340e03120504154107468018005580080020062402d05550f13101c031a261080699045404c1c2d0008510b0411007604140c072840400001e01c80680d140c0d80c1d0707900c0041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 659437517 1250 659436267 659436269
    0x412090801110909132f030a080d0b01050408070b2803200703090b03040203070506070303140a4a0a0b0a0209010c0618120c020405060f030d050d060f06090312020a0c 73
    0x1b0615580000c140d0003007224044804481c10140c160303000406140342000c0741e54011054040a03d01d0240c400c1c929501c04e0f0262016070b07420b900100111400d22092541942202e1692241340708040c1c60907020f00360b8100c0741c02c01660b882e2404224409505800b03000e04504d8000c449034051306000b0640401e0744202040111344102190315500d0b101ca0000c01e041c032006800c829005900003d0304000c059165000340000c89035610030368420b80b14449000155010314050314400d50000d028441803180c843e107405d140c184400290104003121001862111040c15007485080d002041a0020720052418159001441c0a4110315101d6110000303811300018540c06808559500013013030440c00c180100746d0304160410700c103e1519850344002002403070b03030050072401117003000701040b00c46c05d12044c1070800d1040240034054042c26204101c440b608900294808140c4034070002448240c40d805d802c01a00441d580d946150782076081c0314070403840b940b4400045510000c8000049800c1c80340d014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 659438767 1250 659437517 659437553
    0x102011d0a0b18250b09060415230c0f031201030311030f0f0414010216062106090b01020601170319020c130c03060914041209080111090913 62
    0x1c0c28686030300d820740c0c080e41c0b502407244001c0d1061149229609482056003801c08501071200142d25464481205c001d000341d0301d059800c01c00603c414800e5030b20a9841d200c1141407454074009070750f0544c0c10b08110000100e921485200006140700120100307100c0e4001c0d88074180001c47c40c0c0060f1401482d05840c051001a08000b03600081e010404001d00c00c80720040100201280c032170540c11214051035009214400300c0000510b01c440d001e50006c6407104502180d1100c1044c2035144c150160b40003039950042c03020740c0c0c140c00a0300780342d141d15200700f4004d880c03d41400900041c01d400003901d8280c040e00017100012210300d01c4406180008100d805184004001702e940015080703003689003c494448540d0300000e0081c25540e50507040c1d100108180c0141d40a0225a03550048071301100c660403000101d941c0d1007030019001c11194502091500b00d1481d00c2802107a9a0000c0f50840740c0c03414404480380c000003420805072901e005c2d065000801c00b500980d1204155031002000503400a0308 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 659440017 1250 659438767 659438783
    0x3010b0f0d0209091c020d080901150b0307110106030f021519050f040512150703021e160c06030504120905010509040c0e1903050114010501050a03050405070909050a020102011d0a 79
    0xa50058802d00c04460282c0303182e03840c45c4006140c031034042d4a1b6a50444103200103100c0c1000107070315407414060391114a9030030b07452038034460820b4032994450303000810000c1072068903402156042024403408000718010b65010010420f503104000707509408414034440004144002d201090310388216021000003414035650b1410501c90201250140b544035942c0031040400018018401103440d0103403246490020580756568441075040b8082c07010444102c0305eaa603051010094003034002c1c26080070b154098202070060b0f60380d081e2000083d070080c40000781c41d80709000c10032a8201d50020710200c00d08040d4191400c010000b402c9019070b4003068880c90700c038030782c05507100e000700d4440e03400640141c020080d044d0b809414045c030521034801180c0030740c80c011085242c014201d0300a810794805035581c0b0f19101c0342540c200c001c0c3c00301510135101c9010f4107400050741c3e14140b103400c0c0050700c40c1010b400c02c02d2042c00060f084454901200030f614050304100d50064074081240c80d96940d01c03941d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 659441267 1250 659440017 659440021
    0x1b0409030207061b02040f0e120a0903151416020f0601060c030e130218010206090118030c0302030d090309031b030b06061803191e050a03050306060d060e0603010b0f0d0209 76
    0x4138032480000020f02940007450030715201c4820480d40c0207100c0204404c4201c6440744c0341e0f4240c918580c403031141a00009400d40342d0900004861001c41e1f03c5101c0780241c04100020000041c1e40f85040c150307a4a5401c1d484e80720140c081a40502046090344020806444203600d0184050800101c50070000e041155042803080b150741d0b60302100a045072905011911740920b82000a4015100c2014078054032a403030005208900c14003c10503001c41101c1625824001c03554151403864100000300c056000c207002500308071400b881441406070003503943c120300303034070718140908001759030307800e00e884002e0320002030000c11158900a5005074040c1d4186a1342c12000002c2080080b0410690303a1500810084102050362810045c203000d00030072810b824854035a0368101c2880008a0007086504401d07402c1700801d000e00d01440e44040c01074401803910080790289801c0b203055401051500140d481401031b9420309100e21040030f403003550220322902c94100010003420700303841c000f80b040c03043e200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 659442517 1250 659441267 659441297
    0xf030c10050c0c0a0b0601030b120a170c1b0109060e03070b0f1c050f010806070e01030b040e030d090302060606071104020901090b1603030f27020307171b040903020706 74
    0x200b110f0152040d10180d0b2104001450300000700e0304140d494500007410b154000300399107040307010034485000e581c0040c100304d5401d03654081c04c8240311603002d000038410f00c40c2016000d804e00c0903980d45034200104100c1100d4610015126071070740d070002d81c100a0407a906001e00d440005050040c0d6095200c3c0d6601c4100045441040384551403000704108070201003141c0d401e2064210307034059101c5101c000041d81e01c89450a5613207004884010010b04400f190700c929500960010b00c0052002c0d00204440001700b102a2840d4000e06000a46503515076403003080c550306200e1320360001411188586001c815840b4000d154151411461081703034009100a100e17800384180c5c600400c00f203041c190300d950106051401503050003000390042800c1085869207071201e48142545540484411010f02c82448800640c40d0f01e100422a05803207050008180d100107041143e080d04403220041c0741588003501d90311031140011407002e00980c1091807080000e41c000c00c1082c25120180b50400c01005141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 659443767 1250 659442517 659442541
    0x121803040f0b04080706020a020a060305060a0312110d0f020706110f060118061a030f04024608030304082808040303051f05150c0f060105030f030c1005 67
    0x152051200e050611000100000c185003d0f108440c01e8409403413103181c0d5004166196649100025804070120009025050003940665001040a0007428156849136160b83c210950501044c02052007042c0f48007402c041000098030014843c90a03180c031400181000c0c0d0790b414240a22418002d0381802d2a0f03002800304a00e050b8408910304031802035a40e01102c5a00c2c440361a0349180711400d0240c04200ba43d4003090b25006a000014042d145568111034560b055101401c100ea10480d085414051102140d041079102e0a074808030b10918032002e401c130b091145840e03243c01d01c020b01340c20303041000010100030b40b503029802041880d50b030038511159100120446020812a8510104a00c07180e9800400d4520a6100351410800e540f10b641c511360304654001c40c4211b2a0001160901c414103184000300d10317140300948100c2c00e1141e4034641c07604100103042d0140c0300d94804001008180b13401c104047c0c0c42512103000c0c52900391030b585a2612410031a20f01803030140c503000480c5014800b2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 659445017 1250 659443767 659443769
    0xc0309020306010e0403080f090a031b0b0c09030712080a0305071b0507150c0507060f030b120c030114040c140a0b12010915300b0708061512180304 65
    0x782581c2d159a110408803050342c41c159000e50018100d140011412080d04003e82e0042c1c80d880d00410300e150300c9035000c488010303070b440740c982014107064180d200040b0100340070341c002c00390b030301700f450319014050141440c0c45404d030301107030980b203051320715801040b61403040b19100c00d018940800d090b40d131160107581924000303015000302884c4035186c1c010b0010110b45813040c4c50244a41c82c00c0346c2081101200c0c02031032410043c183d90000d240801c00140104002d4003080c00608002c41e00002d03600005000c2c10001142022a070001d0521042600c1c00788070300d83d42203052003240142810b0588403840d42c540345019600144032102604411580c40b820840c00904d02c23091000d0746d40310100394800c1060800e1083c0c0c1312130707400c0c00610b6a001c48114103540580d048101031500d21258610100c1030101c0d41d1440c03081c8828080d410a0101385040036a030b03c624441e488420640c100803040c8003201d050089400c006c1034051107008502c0c50103490b41c0b500603000451207030703a141c02081c10030304521031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 659446267 1250 659445017 659445019
    0x7020609060a0806010909110d0c1e09031a131101031d010f050c0a05071112010606020a051014070309030e030f070f05030307170a030209091e06220c030902 69
    0x1040310603059501c0032103103100c1c40c0286d990743c151590b00c0140009981d103009120340740c034101b801807080c001603e5000708203180c150702d008919155190394084c03040d0000301c0c0e403000207003102e042401401a1902c0400e0245d00c005080c0d4030300d00d41b001c44034008a0a403000201fa02000712034030080d03a031007074100045045400b1040b40310003000004c5d4078020020040c44007812130070500011031000100d000d40da0f00181c1d6444851400c9207995072440701014842c9020b44c4076803940b07050300390307410240324000c00340009800a01500400c1d04099240000c00c00ea160b109500300420034220030380c0000a150024158180400c1c15525843c054034062402040c1503014410b010915000120000b0403504880c601d1400c405056103800a0685a04c1484000303844c8180c00d00c3d25252041c80781006100084061800504290b480d0000844070403042c1c442d5184a4240d00600c0840e50ba808802c0750024012a21304913042c1d500c05002801740201c12a080341150b480b8400d203030860094000c502c245038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 659447517 1250 659446267 659446279
    0x3031103040e010f21051e0a140102040303110a05120309010207330b061803100e010501091a09010501030c03110316020d0801240908100b030f010204030f0807020609 73
    0xa1556103a10280c404d62003294072800d43d080084080503809019501c1c10b80e0400c000d007204446444a200d0380400032000329010740700b0940c80c0c40100c0e00c50041e507070214a06070300142c1d45501c0c2d810020080b0f80c180f17400141c580c02000590001403000500c5c40c1d0008411045140c60ba0b461900d1a402030180b078802034400c0008807524841d00c108120007001095841c0003041180c0b58903604281101c4c0e24810740d0780c0040040140103100c0c1035620800900c250014100d03800c0f0b80d07801c0305910946a80203440c0b41c00b42c0d114001401401c403140111200c600d0180c00c0c42502c4030760900050461071703061049070305169481c600d03914098032a4020142d800c0540c0802503407400d0500c601107401e030181c00000018081c903c0c000d0583c5105074140383c102d0740d010ba00e91040300b14880d5205682080100d2080a00c80a2031001038a1802800300180f4220100c000142109520051500b004946007a06140364410041480060441410800c503070350000825616422903101180031841001c10b1140c4c454 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 659448767 1250 659447517 659447519
    0x110306152e030b15040b040306090809060c0d08010e0903190513030b0a0b0409050d030f021306031a091b0c01090803040506100b0a0504151812022803031103040e01 72
    0x20780c06070001107001070140c60800343e50400e200506054040c0740500c901b1120104010404220681c03c9100040e01840d41c0c24544483d8400082050303100c02078000c403e07005814500d80746034000c0407031030040c079112441020310326001040399102d10a01c102416203140112000c07030800c0c401da0507a005005003000e040c40c0d064807818941d509000c1101c689020509102142d901c1e03003401c1c06903d0070283d0220081060580381c280035400f42805440303280d0400c0e402e1290fa03030240ea507940380c3e030010601a00c0009240d0150b14450139007801d00c0305038501400740d12003800a003c0441c071021180c2d11200c070083d51903566102e40640074082d0304501a010719004800d1200b4000c010846a0142400201c50240c803696880365111394095801c0d1000820410b01040048021542c05192540803614090240f5043c90890340c1d0b50700e00c00d0700403e07680c810494040c8118185500304030f8000d40c540750311410805080c00501800c0300ca03808010700300140d03030701d080c1c100b40d0040040c2e4015100d0440841019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 659450017 1250 659448767 659448859
    0x1312080d060627060813030c230c03010911150f04150e030105040201091e0312050c060709030b040209040201030b0405040803011806080d0e03070906090203190c0921050102031311030615 82
    0x1c8074075100e52004502806003051b40e00e180510a02c414039501a1203c4074003000e0320300300030881130030504fd0701c101c0c0c1e020441d60060550f414000c2002d021050580007510420102c028001002540c116010368545424080940e0700b100140d8111100cac2c03400500c5140160442d0160051150302c010690f00c500d000080b600d603048400743c0300031a600400c0302e10381d0b074271903800300c1c0c03c03201c1440007410a200c2d000214015003891a00e69038003d006050104c0c4071030800c0046401c40d00112408d07508500c1c044014040591b0303000800c200c1c0c801718842804918184000c10b611004881d40e000203000d64a07102041d5601c0610810000b0007119408220040d07494452001940c403c40d0420364006200100d074921030f06900c520042c0c800f499546001050a01d070000d00004c9403901c48200000201031003100140c02400158822003007004051a038600c1c524005034180a088401c500ca038101c401004000c01030329041c1040b03600110348940b1203003d60b2404001c924140320f0038400c0c9801d84c003004058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 659451267 1250 659450017 659450063
    0x4080307021213030b060108010b0301030b070c120f030c230d090206070605011a120f09120a0207050a09060803030a0b06040302101806051312080d060627060813030c 73
    0x100c0b800f07917810780b03215592000116024103090103600000a42070005101043d000010781790b0107901c0e420151100152031703da641480380101c04210001d000c2126031421307694980601c000d21000e90406142510320059501d070082001d610460907210301081300c49580126800038103809401a0059541d0101d600b001c0c805040b0074090784100203101c09040c0803001ea0f901c100c2d40300540c01d500020213502e456024600d0100090070040c56403007510340d40b22840481c400241800300103500100f01c1d5600c3e06062105503440c56028140d954644601080b0905000c8100ca5000d00d0340e60f00080e40c2908000000c0c00c600603504065000641c0c4900f01100b01c0c2c01040780c0b900c80001d40c00da04030703070740d5640c40c2190b09104d002405071071035003001020446204a141105251440b905071117040c03460500300b0b80c040b10019400300001030741c1e05100c00e00c1c01d00c0c03082ca02c101c070010b002c44142c01c40e414000041c10808028041043e86070280000c80241071107403ca0136503160740602034003029003280d444012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 659452517 1250 659451267 659451269
    0xa0602030c0d0e03031608040c080303070e0301050c040b030c070309080d031a0306040201020c010c020a0b0d05010f0b07080a0e040e01061e06210222060f2604080307021213 76
    0x2000c9480c0102440c0d0000c00081586d00c515801401035130034a4184d40e0880d01c0c900042d20403030b00444800c80c041106c50702440990700c1a000d996402900366a010201800d6800c060000c120400f010802070100440381c10890b40d208440720748555a8401d20f15080782d00f0410755114802500803803a100101a41c10b412001191840d0302c410310f288680c0074201520380e401a00d000b4056800031115003865401003030b589401600091035044400d59541441800d58051708a1007002588c0303c0045c0302d54031050118402510032203920383e0800c0c07a02d030366100c86072050002c15401c0c002070905003900e079622500b0180e0040c403a0b90007405840d50b01c1200d80101c600d00c4444801015500d000850b41900c201d022940d101842d20709004021a01c1f0b4880740250b1003c030b149500320420100341d981084c05240ca1100808071942c4140c0030708481c1c040101101091000d419109812000344401445131492407074100f500310356103039926203540c0700a91910f03466032582031007800c0101d04840c99401d0954404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 659453767 1250 659452517 659452537
    0x3032109050601052e080601030b1f17040507121509051609020c07090509030403170d1b050702010e040204080a080405180123150c03190f090303030902030a0602030c 73
    0xc440c40c0144220f034030707003074210340e03045c0c82c407640d0b101c480404032485004403d400c0f031070604000035102005004a00b06000c0b407000040c0380301c00d9120100702640e01c020003040c000c3d4039446041c0c241c00d25589860f1903030080d11a1007001e11108404500b031007440700b524030140388004001c00c60310323034185403060303c0c0e16400da4003400404940b900001c0031803d500841d4a0f00b040500984905410075403044007d00010700100c03550700c810701010000803118980c988040c518038100703d440c1c1e4500d04500059880711418401c900713042880c113005940d002029a507005909080000401d0700c6100850001d015907808101544110340c2640c3c18811804014015a10155100401c20b0010404210b4000c020304c1240b0031004080343c0c0c4030007008002d03184911000020f041e51030028840b0104d6000c0d410003c4001025000021208044066001200351020550801500c0400203200141200c41d0070310000e000d068403511074108644d410312043c0e100981c8039208545904145403003030a541c0146104c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 659455017 1250 659453767 659453779
    0xd1b050a02150402011403151504121509080c06162d0216060f0215130b0c0f0f03061e0306011701110708070309060e090c0a020f06180c18010303210905060105 70
    0x35105c275200b9681118181e0320041c2c2990b0b0b1583c21a035a02e4983c3c0d08042c0818003560352901203400282d0702000811004a54030000d003814100b915030a1540d26942229101703124054002049032075068070b6811050030803510b0148824400c2c80d080c4c0c2400fa500140201c241340e2100d0116500d03030030080701d03035032003450354204c4504c620507000d415001c00003661052110000300c0070303100c0014004c6038170640c0111000441c42c1080c40b03102400038250400c240b5103a4101e408001c0200c2e508000450542c2e4010a0164000102070b00011940b1101e0600400c0d1108215450702501c00d88250044011980222811030341d56120b4106400c041d048144120002080000002001446505681103006008040b00c440d629075051882c020740c4808000001d6000d9180ca09002d44024070056102d201c041c42d01088855218408500707000c070210b40c0c0c038441c41001800054030500204501d040d240d25040031062a8401c40300343c90038903210b02240454a0a000035001040fa0215500c0e0407510f0645031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 659456267 1250 659455017 659455039
    0x2060106180e0114030a0602130905090c09040b270a0201030501080d0906201506040e1f0506010c08040f0305011a18100b0d1b050a0215040201140315 66
    0x421140c41c1e041c0e1203081c1c85400481c00610003941ca00c096200c00c041c00500f00d138102c0c04980c6d5020107030b0300280410100c000d40000b040103181e00342d00884c0da01000300c4001c2d0109000c41070014541c0301000c1d2000e0000405400047d1107424a44016002170140b01907a01403208161816a92032240c43e0080b07000a050800001d00d201c400684c0d41000c01c0c050b2294400b80307041c4841240c030030450140388101e41d8010791710103e07002410722024500d0b1015000000840c5015414801900c8030320901000540c071038821880241c01002e10400541c007010303008900d0b902c41c01c004841803400c030800640190000540019200925118441103c0c880e4000303020500d07480c0445000500c050301c0e031913000001c401002c212049442a040d500c900181440b00317025498012403240341c1c02845185451981d920a4459801aa0100400750742d19914140f13240c102003110003074449207481c4900301100a0100414110382c021650b15407410064400c2903101d15242c44c0301d40c00c210030f1000036800b0f5248105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 659457517 1250 659456267 659456297
    0xa030333150f080115021e030d1505010504050105070203070e070f0305060307030305030a020d140a09051005010308040b030a0e120a030b030f0318130f0204260718150602060106 78
    0x80310590a500ea80c680b02a00d03803820a0101052034411084c00840c003030311010125421444202a16001041e001580c5456000c1d003081c0c200c070981c0020484100c43c010ac100226a800030486056400c20310b812038884c1540c1c80402e260002d1500921580d030746d514104081c2c01e61240c503e00e410304031603030180401e0b210402450384a03c0140006000103100b0030001b2403408941c0c0050415944105000404d048521140401028190361400686449044074401d00c131041141c1400c100e60008100b046500d1030b03030b03601d801e0302c0707103200701d0700003000200c0094051240b0b540040072a80040c0c043d20701c40c4e1451800c2c0d54130341d40044000f5002c20300d00450b40b14079003000551105540310100003540f810303505040c2c416004011401e001d1748200c1d0030004000c407102c580528801d400e4540c8000d80c6a070304004108401601a8204032a807102c005949840618000340f90300c212801e40160100c0f0001e074000b100702500b5800c0101102154000300004c00c40d50009a0904a94455541040f2400c00c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 659458767 1250 659457517 659457527
    0x6011b02010f0c0201050d0603080406030e120301031202070f0b041d04151a031002030403020c060c0d05160803090705030606100509040b27060a15020a03033315 71
    0x6400a4002404000c0000d281c0d8090500768068500504001c1d0a000c2e800c0344030406d581564004031804030002c6020008550940184094490700b070014140810480e40c079000c2e03a010501c00680b00ea85160400783c21a4000e104881c0a0030700012103204403500d882c0f100070554002c1c4280d50350300881900510038203010301c175854050b60340000d914081e01040e54124014000120012a055890402403601940c080040349130306866005c025842e0f00d8a0b003000b070304101c44540c104e40640c108000840703d5400c04100041c4102e51800d22030346840f41080c001941c49205030005042d20000024000d29410000b484c40c1101c0c022001c4580903a00c01c028401c450420b2110240030900c14401d006c59403401d41c101000592028101c65140b4014440f4804003a11444400c64002151400d000b036070708040600710701038400d5003010000c581c1c80101c025540e00340e01801804060f41d60f80c24240d0f90005072842130710703c01ea200f00040080c000c0d6022074540c030360a2242d411103503203501e000c210007030142e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 659460017 1250 659458767 659458817
    0x2701020a09060f08180115081005090105090a030c03050409020720060405060906031302191403030f0f0307140a030c1b1e050a060612150501180c0201061206050601 72
    0x341e544c10f40b1600c3d01007a400841c0f885c203032005165525000700140c1d4030401010304004102610081035040010000c8408880c07000c1c0114000703074149410800381210005669044a03410320700719026035038505045800d400349400406443c0e00006240c014090841c0000c0720030410400780000003c0e44004000301407042d441100c1e0010307024030000d00c2c5807034548007440d481424901c0a1491484607400504000d41001840180c110010b00920010000500400c1c01c0c400503401186001d03c80e80e000c00c4540280f041c0e0180e60b410000018111601c00c49101c0c965140001c041c5848400c40b40c40070700a811420090000600c20900d0084a0403003011429039142d0005a0071042c1000e504c0111400d40c142c200c01d42c1c0910641c01103000141f11442508004c00e42c80b4a408815580d5161072400385000580c01c50340c0d6820000103200f004030050394605000300b40c000000300030079050026800345c200b56014600d1140c41205039030030f01200e90061846103c00b40e0390303a540c03034117814a0a203204003c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 659461267 1250 659460017 659460047
    0x61509100513020a12060303030915050f040b0406150f061b110603040c12051b0414150d05120901030b03070305060601030f090b070c020f0a031a2701020a0906 70
    0x1d44810192103074081d801010f111555281009061744c0320704070102610f4043e88100c0010795140110014808010103060f240b49040d4000d2126081003141d07225507903005003018001c902c00002090420000d5880500003000b02842014840d5403051901c80d00c0b0151300c600c1d404200c070040002c145020400400003065400f082e1071000781600c505103c4a900010000c0310314108000c80402c565130600f9211001910170f800a00050140182103003154035043c2c44640220300707003803082052a40c0d00100590182080c017031500c40c2e240940000e022030398071460150040c02100001001106114014840c218080c0c0f01070041076030400915030340300c00f60711018065800180c0070860662194200c2500802c6003407001c00c24440c42c0d202d010303c4280a03200c04022034081030018086042144500000440440d04a1340240c5540c54500002d150080352154404ca0500000c01503032074481c20345900650101d0030100c80c803080781001c3c000c0d4402500103001c60308810002541034440c8800800d80e1030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 659462517 1250 659461267 659461279
    0x2010618020703030e03180102120421020312070303020d05010e0c0f0f0f0c0604051608031b030d0603050a0b16090b090d06050a02070c080703020a1a07050615091005 73
    0x100d08600400a41040404400305516142d810f01d45001c06c1010780880c03a54103080c580242000800a03180508200d950010754034244000c03c030b05040404840c602d400000040703041d069040c0300003401e08000200f0701d07081403004101401407507410b90140c03400e503c411504100b0380c0d88400c4400c0701d9500c111443c0802c1c0c00c040004500b00c20085001d002050b0a120003603051804144d00201d2503006002100140e42c007450420007800700803c1000082410020419003440c00d01036900c0d120310909041101c03640384030380c0c1c6600200003001101c034609035540c41040000d4803480c00589661040724103484018402e00814481c03458407188085400440c1c50b03040c245490500011110780100c035002e0b9100400602910105000b03000b0a84140741500b401030303850300c1ea072038580000e00d415040103050394001407043c00103031941c11040017601e9030300c010298040c0843c610760305940b28114004060340502c106100c0c069003003500001c4061011600500c459641051402c00ca503d0f621130994450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 659463767 1250 659462517 659462549
    0x8161a070302010e10020304061b0e0f131d120307020a020913020d140106060e03190807050304080c01200a03080604090b090c0f09071205100e070816020106 69
    0x9009001844428030030300020440c2e0483c10300b004d040c8201d040d01c02040035000000c0008000e0180309980c8078100610380100e030701c1100d1000520036003640c42d41c0ba004042c0003c15609640e900220100303103221440b403d01c50221561189000c41c04036615010b19445100e07000220041101c00784c0740708450603801041c02c2400ca07000c2050041002d001c3c840c4c020300502c5400d0242c0c56040d200c64034280a43e0b2004007200120440a0865101e540711300c0800c1101c22110646039008240e039059582c7c0310f085411000e0300d5003080078491180e040c00070501d100001d4001030301070b40424000c1011131f00744c07104854481c0e42541c41e140e20718050192103664101c0051100024090301e00b468100a014200044110340ca03641c030600e0790000ea075a02140d9204e80c081c110305140c84213a82011440a4481d81001d04010101a0900c3c1c490108600803070b0b105e0b400100320b0450803001c2e400a208488030180c0c0341c184031102400000044d01c100002c00034500d951300c005c41c0140904000c640c0d0110080c0e20070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 659465017 1250 659463767 659463809
    0x8090906010c080a091e12080f09030703060e0607050309030d090302010b060a08010512071d0a0912030c17100506070614010806070f0806060a030c020c09100816 71
    0x102500600d20380c10b00042c1d1120401180c0000064480c4c54042c0d11074058044c1400a8425150810306c01d5040d45415440d06001c03c10043c866811034662181030944c441046503855244c5d03000d801c0b01030790144505080002400100d42120500400c0d59003134801c00d8841351012500361000711a030180580c42001082140491903014090b400e000b0320002940e8807407200080c2403035007c0026200007800400041c40f5900d80042c000b04001da2440041001914001c00000d840683e091030a14072010600080c107401002d0b08059800c5901901d03056100c00340c1040a0001d0035514003000002d81034520650b0000046200b55000d9409145207a000038a46400c0040ca030340a1102100c006031100002504544082da44501038403200d00501090b02c0c2240c00100505e0a1104440c100002c540c00d000356621904200e801c6421103160100c1ca080c58084c0503440c21402440c6176030400d034000300304902c07407403800424426a442c030820744003550500c42c0d85040902250103550884400e045001c066 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 659466267 1250 659465017 659465029
    0x80a14061008090a060518010513030c120504050405040606080c030a031d060f120912030708010e0402040e0d080a140108100b180a0f0509210c0c130c0207120809 71
    0x100c40b0310b5008503008004e10765614000e5800507140c4501c116600c2c4070112070500207001d100d81c0141c0c6c180d10307019240c1c0542c07002410743d80c182c540903010a1005080305480b51184c801c0710041c14000d44180b0490070075280000c02001a4400d1100c103000d0030811503070500c2d02190070040c544c2c00d0f0b900c00c1220812501030444c0c15103045803042d0310030010840b0901414800d000341041098401307031a1003918008400364108115001c041260b0b201c00c00410509a41298036a4151070280f080104113a075248007040040c81001100903091140500c00c101c0f45030701111300b034401e181000d410301100c0d8401d5a011b264010030b00a059090b0081c0803034401400480d0300040c4280c0c8000d200465a01e0701035007146200c2000e49449000325119003091000e04803602820750045903440c02040b011a066038101003005010041160352a00002d000303100c04000c20000e003200500a04c5200d10802503030190300241100b807140005030180300e40000d5040040706941000070b4100c0443c500e00043c1e5810001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 659467517 1250 659466267 659466271
    0x150e03100c0509180717040f150f020313260417010902090a06140901081f0b040c0809071706130609080301140f040605060d02070507080a03080a14061008 68
    0xb08001400800070f0350b0b4411510032a810584041d40c1c07081d04049030006d00d8840c410309100c018081d600700344400203018408002a0641185140a8004542c4803003c081e11608010304c0906001000340311440040307003d00e111b5248248114075142a01700010703000d00008425001c1e207500140003c00110300e18070044e42d002c2d8008000003038000110360008102074415501c016161340d5822082c4100251051704100301401184c010b12190b140c05003842e5180101c02c041003141e48901001103a003901ca41201c00c0d101e00081052001d480d0014000b440031b00210340308591807140c40000a0108030460001e200c090081c00031b0003040da50f4407001074030f101441d4070886013107549040341004a08408090741c0079118103600d065507400078504020f100c0b102c001c1b4840c4600e2614a00f04911b0355500e007103070221600c001e07001d0303140c041e54100a42840300035400103106d40a90102d040406a101c0052407061900660400241008141c00248240100c42d640c1d085080600e1444c0c0f0b0502134031040c0c5e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 659468767 1250 659467517 659467541
    0x10903020111030d150f0501020307020607060c120c170f0601020a02011b08040b07060c171f05040608031314010507020d052a03010609020f040e0709120507150e0310 73
    0x30300c0c4c00c40882485048891050210101207201142070004031008070743e40000301000d2004504010903a00003640d40e1048000013004d10355501b03050084030380100c40310340c01056078000030000178803800d00140610a4241e51030340741010b140001928240002e840c5405040180d004058010881c2d0043d90440104503200340c0303803c144800c00d40092031180050000d0103050445c2a20380b105845c240090300c60740c084040905c922107440744080c54000321b0f43c03580414691554424010a404100d04580302904013a8003e070401c200420303c0d0000000400741000c2004078401810342d202c1140d0094040150064000b80303041140e10f000d4548644a5000b40c1d0051040d1f0b51030900c1880c0c154060b41903036034030800b103a089249461144c5002c0c801d00e4024515032006601d4600e1400001c12140302d14003414042c94142400305c0c007418880c0a05501402c078001c041c900d0107400b4148581e039a0294407a288000d20141100300d078540c4259a49480600013800404940f81c003002c0744409041098004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 659470017 1250 659468767 659468773
    0x12092111060c0703111c11010e040b0402030109090b180d03021b0a0f02100f09090f2d0b0406060519030e12031828260c0d020606010903020111 63
    0x4404031400c03e004800086204440344032404024174184103907044246101481c4100440c01036010442244401e00403d501b4608098004500d0000800500d4620407031a0818404400800c40c0c106a40c0042a2540181f540d1641d40d40c4d540000740c8a11703220016000c00f5007202c02220300907030094025080a04c04002c20301340101c4c035041d400b46000395440c416258a0500e01808040d4205190422107850080c40c1404d403209401e100500740c2e001500c20a80010f5070350759981c003006107507032104d40103541e40d0f42c1040c0c0031040400d8a1500c8411405d40051192800c3d01c05110b52606103e0602181c54980325a400c5c004181d2440c2c07001c0c0301401003e0b06064880781c0020100600f03109103e100700c540a1115224101040f002c0c00c480d2141c00f8040642c3d020700907400112042c0046500942c403032100c3c0580403495880c080107010038a6414101c00e48500401e0300040741c040700982030040107402164a811802e00d000c0f43d82d00000d84a00c0e000c500802018005035109114240c2003041150813 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 659471267 1250 659470017 659470027
    0x30204030f0f11191701061d040c050603010e0c090f04020c0a0c0f050108160210060b1b060103030816140a050301060f0801030c090b1c1209211106 65
    0x154440001000404403011401400010204030041800c0300c0f1689003a2030f0307040b20807034009088035801924060720060503141000d204c40d54500b508000d001c0c1607219800c850401b02e01070541c48036581590200c407020748a12000c521030400509403070407984841040781c80c9855202d051502c952102800070340042004400022036140c078001415059070410003010680a10b06114400c82c10700c0e04040221500c0e101c041003180e80c07100320361340c2018900c1c1052080b0700000f0f1003a4502100020441c2c0c1c40760401c90001080301410010b40f01e02c0301035620546602004041c1036841d0202400010301042c07998000c01c1010310340304140303800c80380141051140055000f12440450b0400c2c07a2500008500000501c00c2c0c1e54042d00b0201c0726010303801c0c400d1032541195205280d010701800b0302ca20031565422a0031a40d991901088103006829003412a5003645040800001e0004220341010071a0300c24005000c82001403a00f480304901c51290070300881d1030307031414038032600702038000e40c04001449 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 659472517 1250 659471267 659471273
    0x5120a0305030a1a040614180c0318190305090a0603020903070b0c070305030f0903072c1b07030c170a050f0a02071a03090d03330909060e010e030403051009020103020403 75
    0x1042c0409800f044400c800a587d01700100440440c1031a82819202c241c90b080c4007285400b00240c0c1d4001114a00218840c00c241031064500301c404002c000401c200307040c00078140b5410030010003d003081552600e140d03039211103094060b4403c1800c1d143d01036024010800c003410030040030b089400120300070380f080d0380e82e41d8807040c1c5950802200d4444064002070042c0a80c0350401c070000003405020055403c841e0310000301e1041d401c202141c1d1341c0090061002a001e420b51043c000c019403051580c0d20f480c0d200c6820010000003900c80101d07422101e41c502d0034540b840420682d81d40e00f03161b5139520f26145815210550541200f1100c03070030342c442c401001c05c1210719612080c24035107602c54415200d24021642c28504046a03850506161030b00400341a079003604441e99541040e400d0401c0c0300c2c18001504c0514420f020b621248002d0716122041c020017203541c000180f07001103503000f0704c800040040103030f27224400d51000038074561141c0840ba030750030017030b801800c5194014100141025960b807 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 659473767 1250 659472517 659472521
    0x60a092a1a0d06140a231c120206280f0603141c09124d01170c07020604060809150622020f1305120a0305030a1a04 51
    0x204986002020a40016410540c403034800104080da07502655000340703402044c034003170742800340b40c00341c4903000f5460b0301c5080000e072081001640517024480f0f41201404241203a44807900441e00520f07501d0078108203520000782e1038018004440911002600304181c0c0742d14812110216a4598031207681296070040c42c442d1030025405210441c0300000c602a040c0e05014050035003207800540c00e60000e400c1540041c01c10143c50441c031104c0f542200e9810300c416003079260b40c80b1481c04003140320340700401b1414003408000300400c00c00d200c4000204524182e44d0b0309406030054009881c01340c000080d00086494150444e2604400c946403200540100d41c2c151b00c160400c50200d00c50a003070181c0c0c04401c201c40b021000e440d00d500e041c00d0034000c1c00920071039601180402502003103041903c29041382c2e81280c03583c100303026041d0307a03a26106c01412020105440355902c5032281046950240740007261000040354140e85040ca15035941d5000001480308a0200042801091110405443d54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 659475017 1250 659473767 659473799
    0xc020904080a120203070503060f040b040515040c030603110405040f0b011e05010815060915040e070906050c060112030504050301020d050115050f1801140304060203060102060a092a 80
    0x881c0d20941d51081084050100b07060900b1607400e441c410010846483e50207070507260401c00460395150078281c000d0000c1c01800f400c18525030b000303203044e0901c01900202603107481c40400a131001c0c002e02c250f0b040c00350202d865a00c80031746040c0002c000c000c03580c6040c3c0d0100d13a02030f100e0b41a202e078249480d01c50310101c0350300740c001511080c00d403589600100003802c030640c002c1400f46095800341c41d058242c3d84981c003000200d1070081001082a039040e94a840d000c0340241e00c1460825101c0f5a82d000d00c8400402c16540180401d41000021604c94401d90440e0040600c0d100140260b910b0045c022403642074640040d410803809020115075a6001c2c001440303001064080801c555040400501100d80194002c07000e01c201089802902c54042d82500c4196581026040c1281c100d100180d4240404036421040000000100002c0110135070246000d02400e03400c03141140d0342c054036503046030341c3e00c000a0605400290322400509494070101c612004c1d864820358030696071241c0d84060f48a0f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 659476267 1250 659475017 659475023
    0x30a0603120c0303060509010b070201030903121a180c031807092c0715050903010e0a0c0305210d0b0d0219050f2e0504080703080a0305092a010c020904 67
    0x4149011030503d80e02d4010f0101810080310000d205503d0103030001e131710f0310900c0c40003070506840710725140525006413181003c0c081d042c1c80034442c0c441071102828a811306080765512401d41e4a4403a1003094003c2211840385900c1003002d440c5403100d25a500000c42c210001340000d110341180440c01ca51240503900c1c0310715425001c2c100074540000c03881103119000980c0c0c082a407200700c0800a000510501d20410ad0003410040d64801e0440086405841d0a100c0c0304207500c2801000400c006228a070036044074040c034705442c500d40110008581c6004c0c141c06101001d20309001003402e541041d48051107071030f001440081d0707108942d40800c860050916010403d40800c60301041503040c07002c2c3d06050880226080042c0c44403d6181030340d034200c1c0310b207900c20411002c401010050701410480c0c01a004807403c40d0001540c0c1d290800e4603520086008000270704000200e480d422001400003c1c000c1d41c81600303a1500a101024034254605000d018104010354200101603214110f20074041c0340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 659477517 1250 659476267 659476277
    0xe0f011a19090801050901090b16180f0303020f010b010f03050618091c0810061b06050a06050109080c0a0306050c0909010306020406030b01050301060801050f0607080c0109060f060b0708030a060312 87
    0x4a054940b13803c452008010a1199040008240c0010381c454060365015070806042052032060ba18202d99010a040d1034000c160b0194070042411584210100b086900c40c1c0e003116a00c01c15040c485080c0c5a03442e07a49404518600d10038804980203401559001f04064500d132500d002d00c802c0010300104c141c0d0014055040210742c0c21400c190440610400340d1603007021200e50904a0380035400000c107200321020401d4042059061407000101c281900390050824041360801a649200034001403094a01181c1144000520000b0224911401c400e00400d040c0c2036528548600010307181c01021212100410810031441e40e8131a620300b8080c0d4022034006864905040015045401c00d400d440d042c0075080c40100501c550141245054500c10740750b440c6000c1411001c14074a00840000400c018004035011880300b00543c031948085004110503c2a0315000340a1002c6580b54001d00c3c2101c1030410450f4041a08400115080301e444000040d106541e03480300c4400d10504051240010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 659478767 1250 659477517 659477519
    0xb0607030f0807030b0108041401110a020c09010501210f1803020102130e250e0904110f090108100209061b03030109060e01060c1407080d05130e0f011a1909 69
    0x56404442d181e0700015070308003000414504000a4200e03040280020b12008642d800b20281e442c3c00e40020482c00e65494600b030300c418580d500030b903e60303c4100003140076004080002805602c1401c0800415509800824035130101000000c050040701c40781d50055070700d4908504201012a4001843d14000d034001078541803401510034440d101540304080c420725003070500160750720f9901d0304d09080e403d4410303041c42d00b2440d11096658201c955081a480300b10303107003003000703000030180700e02d10801c4200c40e401c16181c04041000341c016805e02070800315502903031214004909550041401040081609082c80321010103400101240742510394240c20100c0100030a9000e4040e0742d006e804071115412456040800080084d003605c08041c044982c2500e404215030402d01940307024007883d40980d0b981a449802c00350032681f0108002c48005a080d42c00501c00c4405800c250203500345080d0b8007981c9c1d203000074802c09218038400c0140c0155041010341111003c200640070502c1103034685d803001c6c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 659480017 1250 659478767 659478797
    0x103020a110f0307030e0420220b0c0d1103090d0305070b070915050f0d020918090609100e07060809281e02010e0105031807090207020a1d0402010807030b060703 71
    0x1407072440301d0b5107004908000b44010341d0310510508030701a55002d0000e80c1c940e90070382c27984140000081c840c034144402c04407010405001d0700005001c403100c010b0842d4107000ba1420b04a581d11600070642c0790942051140038540d1400c201c40d05c0e01c683c028517107603092020513104c2204812003580da04000c5268101c04006019000c800b40b2410280d41c108142062804291403c061040c0f2807020840b580c00980b0401039034588414040c0382c901040c0845e558a415640940da0b000b081d0f680d4a1b240c8204500d06140542e03d005d119108420075000d04403440c60018152044a409400c58140c0c2c0151060009805018a4290070030a042c1c50307080f07904856030034403101d12001c0d007000c00d001a0310301084c01c000d81d0704010819034520b130a203015903030b03603a07400d1040c40e180c0300348241070b0403070b0003511070010368628150040e212250007202c91054007030350740e8505200202140c429580c7c1c000c203c1d00007000340d030141e6841580120b0794140808c1808040b80003500c664406071003240440d2032040031501e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 659481267 1250 659480017 659480027
    0x4050a0f1107030207150306030f03030b0406051c08030402010219050c0a09020f031306020405030307050c130c09170a0b33060409150e01030c03111e0103020a110f030703 75
    0x104400035940d4500c1c01c0d0342601c3c02511049103000c0d5485140c4200c3c1042000c2c3e00c02d0344484000c50300030212243d680100c0c6002409441c10b10a45842181013400214103403a0103c402c0b80745044581101e90280d016552f45443c80d080140181d055024040541c8050045030048021484c428400341102c0342c040000c000139544280c001e2200c2034030510140c0d8420000000704ca0308295040b1f000030030180707107251500c043c1c480d640002c2d81500010a402d0300b0080e00280495204400310751001284109030400c0d4215240001345c1c00020b4040101000080c04403040c10600b43c035824162246032046403100b002d00c86040c2c54042d440750400d184000b1820305012110040d102814150203014401d4000070510f0185015a016540c1e13160700c440f1322941912081402800d00700d41001740c82da540d0405e0507422400c4d01c4141d4440c5685880d00640c1c0c0b8000280c0321020881c042c02e600155040303c011402504401e1500085c01450402148610020054400303614140b500460b9034070103e15004003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 659482517 1250 659481267 659481281
    0x11100e0f1b0604030f152f090a150309120509040c020d140f0c06090f0f0706020339030d060608040203030706090312050103050313060c02010c2004050a0f 68
    0x160120000c4441c2103a42d240c08490440ba0010003070030b20708040d8140a81480c9a8070400310850f8a440030a0000300700c00401c408581600c00d08488504601c005500c0e000e1240e0b14070340e68807410720361050041c114082e81c000000005031a000031611051741d10030140c1e002101458011030004031f00703201c141c5068043c6420301402c92001d0710040400b4100503140080036084070380788400129014060184000c04e494941e07944608440c614241124250303100c442800e5502081d004070003003000d03418000102c003011110a90b004510700b101e10100ba42c06d4030410020b81c41d9120b04a1950385c1400c0340041c501010004910140d565400115a201c0481c7c840c0c0d1300a20910100a081101507900030050b144d8458200c0390100c1c21424614003121400000d0300215941c40c503010000c4144400007020340300084c10071121005060f252441501c0d40c0c1c6400000130f000400d904000c0d000a2501040d0704a205224042050320000c0c3c1000601900d00032100300440310b075038680451080f4041e0003811 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 659483767 1250 659482517 659482543
    0xf090b0105010c0b04020f010c020d0609020a0b040b0a05130305030703120516021b03030c0d0801030b10150c0c091805010c050a020d230304060509060610050a11100e0f 74
    0x3007004080d688070030f0b000d44c000b4006441142512060342c2a0303409a03400416060b40182032034038900d16031030184020170a50034164080e090401e00401c0c162035450031070303040d2000d142c0c0642c05c0030500340003121a0350201038000f0b0079032030990000000800400240569130300c29106c40320b881c032840761310008440d0024000d188414411000300c10994010a1007240d007156842c0c611064a03040d008a841c40c468020f82c69224840c041039080542d0340035410798162485a51940f1440d1540301d0351000361022401210510b0007440070418081d401000160780a03442441109401a0b5400b0450111b40034440d400c00d00c0118000110300f041028443da8004100318282a428a0383c00d400c000c4d52102e412940f00c003404129121f022041c400701e54001a0511461880307a90707840e0600c2c0040107854207584213001482130368081403d40c58064803c045032903090341d5590801e100d1680454018202c1554003142d4014100d55000c2000c0b41d000e28520004044000e144644c41e0140b52483c0440c808009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 659485017 1250 659483767 659483777
    0x150e010c1b11040e0c0f0f01050f1803030301120b0703023108030c070503070e0108072303010216021806030d0f030605060d0902030d051e09030c0301050f060f0a0302100513090f090b010501 83
    0x400052303a040000d448000300c8448005890781e4000d0416110b10380c01421141e0f0511010000040004100080351040c62003094900a540c8441c502507069001b1b5880703c0d21310380c1c00c0c1b60145140052850322203036009268180741d00c1d02643d5018103401c582c03220307841c410690000309003480142000c10001009011001d0300c48138075850003040c03644450640c001c03550748540d281101403048110102015468800400855465071542c2d150111855100d00490180704021031410940c01907030306040c455400a00900201858102c04032042e94907580c005040c142d54040200700c43d11184098061465588400114107055004040c548002010840100301040060410059409006100c5a00d40403a0561228241c030002802c00341c00340d0500b40c00d03628001c108805450400c148074052801541d103008609031520510458240b1400041d400910840040e42c038180f190300200b2403030260003140100d0540340d0180c0c03800d03108031800b8503240a0700c1d45054424401c0040d80b56005042c24240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 659486267 1250 659485017 659485039
    0x706360b060f13140402040b0f1003020a0c050105011511070f050d02011209060b1002191e0f0305030103051b03210405040603150e010c1b11040e0c0f 66
    0xc5111110006003018014000e0885500c003540b11001e0302c021042c007500084c400c00302071000010401500322400c0e44101d0400d403103900c9508203090b8840c103058001e04480309002c10b54100390080d511613009072041013007002000001c50000c2c403d040c040d0490082c0c0340c0782d64071034090081c0340e45c1000d141603c80b5009520208202c420030000b0700212400be881d12410940d950006a07140c0b03003801c0c6083c01c90b5080070327622002c1000e071390301c80b009484045901c0030300c1324040346049070b60701c491201003c8100080b9100c0800324007082d01c114103039603801b04100741c0082c1c00d0f171724517100405503202140440d1011006004214007441507042c0200b00504401c0d5142d90440000d5560340b0501c00b8120521002c0c1c82022000c4113030003168040c01019105121003550791a00e55041c3d14030f074802e20544c628189010f0b04075201030040407807600c80703540d400418815143c80c400c501c2055100031190b5003004c8481c950151a140288414404824040c0c1841c09210042c44400710750406001d21490400300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 659487517 1250 659486267 659486273
    0x1112041d061e06120f27101a060406020312061009030f111005040501020f0303100b16020d060501060314010f0b131211031002090f04050c070636 64
    0xb9000c0c0201c1e449034004403141c20802080851042035a84d0051894071400c10245903544003039a4080c0300012015459006a02e015654894141444103800e0300701034032110100c07420383c0140003a0b1480b81c40d040c0c070180c2c4e00d000081495219610103800340c1c0000c181030301510701c2d50540360b521940c02c0e0355421690242170700c02030849025000081c6503000d0130410006000a0220106144001030a140c45270b0018001c05007180d0028443c230f600501c1403001540c00814040113690281258030350343c19030b69042120000fa560400400d004148840a03031150150fa13880c100102c10500542c4001181d504199004047c1c0351500981150079100c80700400060408400820071144180d15494550010540281c208000382e401400d4041d000d5010000703010140418100042088084500c042600d0480c1020f07800740384409544515061007181301030509401080d48411081103041c5001c0c03007581c80204955225034a409124900600f40e441d000c4424030720008000b07080c00d8601410102d903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 659488767 1250 659487517 659487529
    0x61203170403020a03050f1e1c0b0904120c0c06090e01081903031505091801200403030507030e130c0207051c120e0916020712030804020d031112041d06 67
    0x100040030408001f4880c40030340400c00c156810000d114450030902504c1204000c5960440d03102d41d440d0f05820145003a17480824402c407215076034007812959440c1c2d603540b180040c0b83c140900c00c1081c0a40841d071080040c4c00311003254050106611460303802410324080300704074581600b010175158402c44c00304140c402c20200301001c050381850049407441200640d000c0001c401d80c00240c00c006440c4c00d00c070606080d014102c080d44240c100070082140d04d1001003451480c10900051018401c12050020910480c02450424064140406460034480110f555604082c0109a00b5503684207014949941404180018441140c400300c0300d500c110102620000c0c0c6110040500540c0020008510b02484202c1940c410041005d01186050300040030b041c0c04c00d01c407000041c003849002040076459101d11040054055a90074035a42d601e40c240b1076039590340e0501740d0070700840b00780208110604021505c4403d01500c0b1041e04e40c2d240c4600c044a842e800210020070050b01741c1086880d171100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 659490017 1250 659488767 659488783
    0x110406081b0408010c02030c0c0405190e010b0904052b142a031e030705040e0603070b04140a0909170304140715020f0a08030c1b0106120317040302 65
    0x22090750310301511504540140384180d6000ca00d4039400d01c291040e10b16004005424000e071010155001800714004100032118200e03240000440360b4503003604c000403168001012101c3c55000060a10749030f6000458410048804941c60760040784044490400030604100c1002c516805105900000c08090812622900000c452010102e00c405121682c418810350314905000c0a60110070105c28203600c0f03611040860107409000007120094091920840f4407903400303a590181024101204482c4c00311010740038683c1449000030104070f80030034000610040417034107540986500ba0300c0a200e05c4400b594400b86640e4a46000b05d000705601c00307403402e00000240407043d903995891401d0001c0e035a442044004610464801045c0b855013600320302c3ca800e1480c0c0072178400641512a26a981d44160002031080310300384007040c054501200501040c01900d00e080d4030f0080f44404c6c641c21a411540210000082610041d081c0f5400000031404802d04083c4500189020b0310b000e595083c103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 659491267 1250 659490017 659490031
    0x1110020d050f0702010c0803040b04050d080c270a18060b030108100203060d080c0a17090a0e060a081f1b08040807020604030210020c0108090f07030b0402190605040911040608 77
    0x100103070f4681168031510359150840c0d44004c0712a2242000d0400007000c90045504031018032a2445520030350b400f405907a80300d44604101c3c0c0380b500d91005640c0884841224841d40842710801c01241107998203501e180180661640c541203010043e4070540a48002d94040400094100010b000c40303400420401540e03407103071401596948607a0040340b010a03101031f01404101c40454030000001e0040b407118619406002420840b0440c002c0e0000940702d41202140c0c8640c074007074100320341d240e884441540241c0081c0f062020a0b505d880980c1406007100c00f081540020b2004154610400e10a0446d030442070010050141903181000d0010140034101400714400400d42c00215912501183d015503030143c402c1e22600b094031000f075035408444400380c0c00724034200001690401c0009100c58a03540050007490074030306d503440c1d1880001000c1c0040e600884010440303941c54620f44400d500030007165582c0399840d4902441c403011603010b51540c220301c6400304420030255600100f103d0708042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 659492517 1250 659491267 659491297
    0xc0503090d030e100504031a2e051302071214030103060e01091e030207090e030d1e0203180708070e280e0c040b06130e0916031110020d05 61
    0x16034101603c4440c0c0300c45505a0002c640411040c445503c0b4000d00200d070310403900b150010741013045011042200300c0b01d101802c500004848190b0300c01e6410002500f101042c20160700b52a10701042984044620030140940c000881804000400254041441072403501c0d07031600d10703c0c52011207548070610000d0900c6072074191041c5855420741c0b05a8440780d10082200d159140d4040244069008c07120540250049200000300502c5034001c9130780800e02c0c10041e42c41c1c4012900404010405440d40741d28020070102000c80258040c4010341c000c0341c4440310415419002c507412403030800550082c000d180c01a0408100c400311a182c0680c0040b20801c145443c4c50800580701c00303030307103050a402940030306020380081428008210f801d950103040d10b0038040a0114010301407148900c4020320580c00c04035200b000403c0705402d0740c9400040381e405507010b0015031000039070346c12083e404c1178400d400c80141081e05860005e8015511807441e002418100d080414054014003400703400c166a10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 659493767 1250 659492517 659492539
    0x18090b090a05061c110d0b010602010c02210f2109071d040b1518010503012301060e0a1205010221060a0302100908010204120c050a031e020625020109060c050309 71
    0x400c02c143c480e14884050030706024960b0604001c0d087c0b076408c1c425900035511340703501c0340072007840440e10305c02801040d04118250740145000c0381e0194025014209606410700c09880d4402c10403004501d00707080303894800e803141811a02a401d0070b9490740450102d03608800021414002c20700030341d40c465000540d02c0811f07500c20804480c0c4074100b0045691203034140c0012001c800e2030fa8401c60503a01c080d4001c01001d640c000c801003040d0240130540f8101700c0f2000041101610810714190100000740a0f500d82680c0c8100c1c07000c100d2000700742210180d40104007487e5182c001c04481c4032880d491a13260006080c01300214071000311a00000c1e016003801100034040d180902d54441c001d1585070300841d5680e03030300c54a85a406100080032201c00020007400105032a040000e030b800c0c0d89e00500042d82c20844010944d00b00314040c0003c0b0380242d0280541140305110701200d4003a80c103140c2e00780d84800b0985c800146002d40a8012100303111541810700f0200c1c0300002520a1084180e40c288041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 659495017 1250 659493767 659493773
    0xb0f0417071802030604110313050d110715110307080406020c0405011206050912120916060207090203060f0a1e0821070c03170a08090d080703090318090b090a05061c 73
    0xb178071102119034a491000024071141c00700e46278041e05580d00607030558081c0c600b00350044500c81003800d003440d2181e0180b68140078054001d2a0b68003241203a05240d5694244106580d00f1074204c44400c1e10f001001240400041ea014081e211010101b2141040903605050b5140070181801e48080d200a5036000040c00c850400c22456400a038455126501c0310f0740301c0799404498004076107041d05030040400c50070044802d0310225007525540d4010701041410188480c0003500001c00866010300d040c0f002c181e040d01c481c45090054003020380b02e200000e40e891090002c03401c140e488041140c3c013940003032038175a12015009600754203112650b41e40b0f0700c103410320003003003106900003800701c150101e1039480c2022180018a19005191692010b69580a14040c3c44100b00300141010540c40030000c1d5800340b103a400304241c1c80c46400d019a1200c8030511511000003d07411180d07600307a0791480c0311110300d802c81320340d07034000d0034444180500d14100c8003043c001c20a001403400b031701000c01811420 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 659496267 1250 659495017 659495021
    0x7030309120309170d0306091a1903021005030f070e060a1809050906160528020f011e0e0a020307060e0d060903081603140103031202040b0f0417071802030604 70
    0x200b500301c00b81ea8030700d410000d0319505c4144031400c0c01c001c207180880003e02c120f500d00480043c10880e01c0d030420b00500d128180305c0200304800c108840c6016070708002c0010396521601d4016211199146130f140c1c03038071030181811114081c01e41001d01022b80307406442a03480704225155802c252601040b8201070b849a24100303440b0b03402c4034013804d0504c0c04220508900280c3d69125200200c07440041d0a141c1905580b18800c082081c5c1e2000998080d00c80300400c0c00c520010000d08d18411101e54080e5040b40d070703007143c24040f00700c00144034901010580100303d02848071954a0a000340c142d08100780c1c006a0340d117000f4843d04052240c000074119890b501c1051501c803c039000017091000c0c40542c035005042c468110f070003994014401500c8098075210388640048a01c850140310741a900790744060714510400c2058007442c036020000401c882c400321016201801d0720400054603981415282c04032010b41c100e4280b4154072004041204009848284583c0c072280c10005a50751034040100300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 659497517 1250 659496267 659496269
    0x910091805100209030d051806030c0f070609020f010f120b01020114010e0f28090827090a02030f13060902060403140601093b15070306050307030309120309 69
    0x1101d03004564941d6246000364000b405451011000d89880c00407030081078544e805078503514040419242c0045805003050402550440600d01e42c0c00e081200b200d101c2c1a0603484043c0840300151201549000c41c20580034001d468202420b10004040038440c0081c038442d842450090480e890b101d44105990003036005000020045114a04540c1c440e251000900000da50b52481145481e000410301c54001c5200740b013004c11848522201202201c00102900b40b406081d221407000f0000b03d40b00031402d10b043c0c040b4503039034150001c002d44640c04000b4400380c018500001d8500400402014105070002d0a50000000c45c4115450303020307040800043c40440f400940042d00000c0c040b0500403a60058103c0d40244003c03108039a803114401016a20303200c0d52210800c0030505035103a0385450040250103541071295041270f6a4029220350310b000c4400c4203200d04e40000780c0501402c9a454042c000203081e0079001480070920319500100340d6000c9200c2c0020700398040b0b001d081010f1240601c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 659498767 1250 659497517 659497523
    0x10c0c09051008060129072d02010e0d02010206010512010204230429010c02060d05010603020702100c230309030d050a0e0a0b030103020f010207150801031109100918 73
    0x80180740c100b600e803808810368003507960f05204a000004898041d04600c1002209500800c01801320708910b02105800404003285d080310711203800c840e812020003000880080c01c40d038108461b011400050902000422b9507030151003204510000343c2d80019646044035402d0320743d1503806000c500d0884c0203000c4e581018105c001d81c440410361107010b000c0c241500407030441c0c04101d210110060b2000c01c00840100b02501506070006007519030240a0001c1c086001034041454a01107903068000c8810981025000c00c0e400300e480c0003581403000c25034602811500740103c41214a4a82c2889100c5044042e54000c880181c00a011481801a2105236001404441080c0c50b040c0740500250001c01030314000900000080c41760b4500203080030115480d001e030551969095400340f01018446034900c0d815442907000010b0800c410011000c9001082c5d41c1d510070780c1d4110728280310511265142180320b1048002070241c441a035180034804c496040a000030b5814103242c8038100e81200010207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 659500017 1250 659498767 659498771
    0xc120702120a031a01030504030210050a140f0403030e030c0606090a090b0702060f0c5404050c070201020c010309062c0d05030108070611120712020d031a010c0c09 72
    0x164402c150150041420039504000300402843c4603c01102210012a030150042c3d002546451210aa07a0b00c0107411000d0540b01007403d2030039003202a00007030103594a01c0c810303800d1020001419410b00c2902040c911f400051880c01c5001d107800740c1e0f54440680020f110750340000c0071a000050541c0300f9100598843d0742e4090501c1c001c2d41c081e482d60400c442c02144601c24200003680c440c0c040080320301106c140020742801c001c0140e0b5090301d070403017040c0c541044481011140f071404000c410f400040d4610907490342401c05010305000c00c0d0381002c0d00000019509001480060382c0125880328807a00030f1030700080032090340c2000ca000d020141001c6080c8034011900c2d2400c1d000146103809880284030444110620420003121144824854400a50007101b014400d0a1040100071003100026044440d03111301d03181205000e034003a44040300c1d400c5110740c074580181d406010034080b4a00c20b080030024440f100e0400c0b11001c2c0082c020504000f440f1100c2e904000f480fa038450050103004d001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 659501267 1250 659500017 659500027
    0x1e18030501020a03110a020d0e12120c010f05010311010e13110a23222111010905010806040b060f0a091a0406020a030302030c1902070513050c12070212 67
    0x300600039402a1031000001e07044c001003402c5c845c0d100d011104028215401007604140c010011030b082d00c03026400da98020301030100c0c502031040c108000075101412100840c2d54283c90040c2c0c3d0308645035401ea8940e1281032800400c0450350079180200941420b00b48a265a030544000034400d40b84102580e450920742100702201e2503c15020b05001c01c00ea44030031504d80201c82030701d0380e9008a0714040782c03842020000c0f142c600c0040c016490346045c042c04101c01158660745605082c0702c07641821040101c0c0071180406005088000d82035040382828495078280c02c08000a012000003032119020319110a02040c0c04c2d1100b808a030444400b00714259150125134000800c040320b248580007110568442c5089580000c0003140c0c00c443c01500188046406907a090740a908024005940380e8400d011764448072042240128034031010343d004d0103ca50400c0c00304920498003a03683c420452814080092144c0d503801210800100320720014000e03629840224540010381c4181100c8035000300b6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 659502517 1250 659501267 659501273
    0x9080c011b1209021e19030317010b0a09060509030a0b130b1b18010915080a180201140c1f050f07050901020a0f140304060207080708010207031e1803 66
    0x41409448000d030380e528484952181c0950b0140c03900100c0203903106010031600000800000c3e459040d008002d0000704403940079a60607501c02d5410f40c819004510305500010001c10201407980c050055a0329881c144907600e030f4024000001801140180500042c80c8001d42c2c0e01008005107041d84683c0d4030340c003403500404217403100000c404216540901d00002c5001900020100203c012014120b41c2c2001914440407050106101100e4103200c01041c02003a500351100103000086065201c284540c10810314240468500d10296404d4188001640c00143c0c2d0000d24100f03078003981c024141d1a007585100007820616a064a40321900304c086013440c0140b02a00103d01c5003031000066800303a0384030b010940d0030b4428105894010703004050440001001e4880c0103a0143c001c1d400121020107a4450901e980d006410400141e44a420100892042000000040c2c0401c00080d810042e5640d00a805504220b4010303090000708118a10003501c03030008050b0318101600c3c04011f40340c1e242 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 659503767 1250 659502517 659502551
    0xd0e0708070801020c0a200603041103101a130b10020a14071805040507152705061c090213051905010b03060d02041b0f1709060a09080c01 61
    0x311468500e409445000100d1a1040c400d1300c841d080c3c003001805440d80540e070b0f40c04c034804084440903190f41103a8520303002c80d03d8180c0918400e6209001d822079691249041510384505040038801d080e0414244c002d0411856240c2c2270035105c00d60b02c259450b04203040e220040c041e1841e2003a00f0564a038008100140c0c00500c80080e1170082c9545010540a100e050751169850300070b40260702110041c0340f00b0003019030300c82075005000d0015a85229240c100c5031070241e280e5100040040c120004405003040c1d0400582d845206040b176240fa42c61074603020540034044d03642c45940111403e03031000803900864000303110644d8014984a14400409140780c024402038030030800410240000083c24520f5100b214140c070105030b800c604543d41d21080007107240b00b605040b40c01680340d030068801e60040c034a608280040c03949440519a5900c50028080d660307414600c075040c105802840412003001c00c090390007070151a07000c1001c2c8090b0404101906c00d0061119040d031810b000304580e0a100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 659505017 1250 659503767 659503769
    0xb12060f0d0c05010c02060910020c01080f0f0112030c2a05042003130b0a0912081009050c09040e060a0b06130501030c1b0308150307080303010b0304020d0813050f0a03260d0e07 78
    0x24dc0360351010f034880070303000b0802c0c4004031600d1242003102c20050080c01e80044d006d540b01482841c1c4450081400d030b4409080b2903011204180c2d070502c0f90660300c040b00700c0c0d84011003e04420398003000007040740764400001c850354002040052800001042484110700c00c0084e00715009000c100c034500303050640381d0060800704001d66401c10f001e1219a981880f41d034040d4002c42e43c1c90352a00c3c010341080403070801043c2c09803414000c1c0c08108217920003526540502618091614040c14452820803007090130b0301c0204c400c02d4441d082c10003c0700c0c40783c03030034050741c605543c400c0c42d000642c111410415108210306440d50461122200c03408410180e01a1100d84100e1441c0443d000070140c44081c1582c450302c40c0101c6401e81c1050005000070f0300d01c9070240d07901c80c0c0000c001c461000c003541c60b643e03041d1340080320503009405131070b41c207129900f4a0420940c41400940d0141106407454850005542958142e6201504400d5032030f80c800c40e40d4002e50b604c05d00844420800150384401d0f0a83c0c40c081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 659506267 1250 659505017 659505019
    0xb0708040302061917040f03080901020c0a030302070c05060921030d09080d0e160303050d18121b0c061d030313180501140d03090b12060f0d0c05010c02060910020c 72
    0x400e030005100c58a00e8518070380101c0d1f0000c0040c82e1000903907003e40e55510002d00b1004599070034824407000703d408000c5141264000c1d1401665214036041104100070241c0003140100720400c40c40800d5200c80c01c101c040c80c1d0001c3c0b403132118100700f0500b150541c07086410310400e8038107000c0100c0c140302c4240001e01c222a0006420080a8010a00325849071008903030035007804075144042010900800051071400b411200000b00c0c0400b0990402e02181c2281003a101c011046901440030b54101d05084000c42c0c102c6108100002c450341c61101d042c1c0e01c2e003e00d50801080e907518203442540100c4402c1c1e5844000c0a80f0b403904216032480003031890b82e104800652144100305a4000d200e8130511303051741c0d0307240c03215040d00791090305014000d003040404904102400100003040110500901409461b11211100a080c07a5080002007a07590703d5192189004a00620014107095000070458030203007405404100b044c000100c8034007803c46030030742164400c407100071182e0b404207035170002c040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 659507517 1250 659506267 659506277
    0xf0c08031e0f0c18040605120d18031e060b090406020a030c05120406090f0804060210230601031d01180302060c040602120702060d14012c010b07080403020619 70
    0x55060074030b8040201c10b803406040020200301801102c9107590341e006042c080903201103041c6664002107145100000300020243d001211980403843d4811840c0303600342c0d4001100044203003992140001420162140c0780680c043e4420b4100b00261504082e0303a0710302c01403002941d4030f000e081c07102c06584541c01050010789070a46140b880b0340101c0684240003200c404085e0199034699820009001080e030644800142e0217210340003800c0000284050300c40b50707014111800080030402c007620b5920310402c03a4103001107604041c1c41c2e050b400c0258060024038012428441410981000780444082e1007459420440910724120392400006001c5101f64200ca145da03a40c3d1076405102d000300c0c028500103030002103601070b0b82c0c007605018011040c0000c111510345450301401c0400c0356062880f011604a11074010031014004145010004034012070884c018010000d0700211075805001c0d034404284c0c040b8487d0240944034040e00c000e5a03000d4800b03540c0f111080503016100005071010b01c0011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 659508767 1250 659507517 659507521
    0x91505010807210b0f09040302030903060f070c0303051b070b01050f06070803130317010603050f060604270603081201030b01090603080d0b041b090608010e010807060f0c08031e 78
    0x24800e000350300941e03240142d007003661111060f00c10090400c1e030303600660017408400300085640d40c103200280a075106c0d800442c1c1e80c15800e070600d42401401451086502825400c11214a07040030301d02403103a0f894903000655079100381ca074001405802e03030254400900801d00e0000c0048184205041c1c4904850b0480030220b0300c0104003840c0b0a0300001400b050702400440e241c2c1010700008580c031886420b00500701c00002c174000c200020264003550001e0746400c10301500c000e00c000080c1d04a0000c0d5462803421342041c43d070241078280c111000b840100e40c146a09842181540040040c5500c545595684e203624810154041d80038041540c0c450402400020302070014400ea5040340e501c00240303420b00940d08203150040c40d64007601c1d50055120700c08400201d603030915600f00380d0401e454410702c246c146007004102090513000310340c810b0800401803100303200009000045030b030145400f035000c00c840902110749001050b0001c0240f540401407200040186101421140313040700d22103101c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 659510017 1250 659508767 659508781
    0x40e01050607020312070c0b13030b0a0c0912151a03060a02090f100302090d03020d030e010e060c03090721152f041a0702100f090506070c0915050108 66
    0x1440b038924001e506510807142c020340e40300d00d0380c00b5220301030144036070b81d82c2c40e956155a0032140e030040d00581e421000c0300c00b0600c2080070000c0815001131410208000500c007018004d0310b120b11f51302541500d20002d6130000c00300030f5549100d0040c0141100c0501c0014892150b5003500001002c0d541e200303005140010794440e559100341e502009005120559800c00c59003408146070298189404042d020010b510aa484000b210300405119900408260b40c0c90321005080303418181d0881c415905081c001a141840025811b0b0005a54180f107980c0341c94940c82d6521f0500c150340209442c038102125030000c0b08240440c6030805000c1c00016080051441500007200d10300d40805013291014080c61318400405d00407040280e5011101900e070607119101c82c006e540e0180f02c4000c01d107200140040071030601d200e2004c60301c141414141c0306c4004d0045c0103006107c05010b500d01510f004a17024080c0072001d15940c000740ba000c0400c01c501c5070303000040c810a07080d500646000c200e2010114002c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 659511267 1250 659510017 659510029
    0x130b061606320703110702060c0f12090603010b25060c090e0f070f11340b1206010302130839120102070204062304180201180812040e0105 61
    0x6455000340e40d070001c0742d4030036601341c00030300d801c102d01c8100500c10300440f401600c0300300007010540c1c1c003000103010450b5000078540c640141c044c40d0100400c4203002c001581e4a900341501d05580121440e9500d13614a030034421641f4520a0070031088000c4211802c003030100301d0340401c504076055075034901c0300e0752500d0b1031980e406015210b4408001100c000580031a02c136074090658410030b8074100948841d1603005034941070422031281619049640c20307400300d82d4a000d005074690307130f80f44075130b00140e29000c100c0b8540d0107181e08101c1c0510300030000030f029038440e60440700b104040754403040c00b44d5155080566140c403524100203c0140c1104806480199800010f40080902c03c1c07001d102000242808110010300341807400d55074083c0442e4006a0ba2401041c0103041d1802079180b80c0507070356003050701c0380e06a43e46240c041c034039140c1181200a9413010741d08800380c081c01d240c00504c1c0c801c0001585c0240551100d0014040c90381201d0000950030006c0084030255140c1041c1c44e6292020000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 659512517 1250 659511267 659511341
    0x902060310080d1b06200d02280c08030a0b10090504050f040b0c0d1506050307090e0118020315150307020c150403030809030d090602041a09130b061606 67
    0x4c0348610f40000d03140051160382180094030240d01c0c08250b0040b1410340404d441c2c00080c507030600b01c0d80120b91481122400710340c2da030f903603030b81180c00c1c1c000140c150f41c0250504640c241b015001c08000000250130346401e4101c07030003030400034022000321902c1c2400188440d1860141610a80c10403003c1114003189200450007950807143c040410b0303c89180121040e40305212a18241d42c459103903450a03c0080341c483d00801440d00e507281d0728940a40001c02001054006036210400e200050003244661809a404e004007080700503900e44455040740c00601b1080b44031640312071010100705c0240c600d640614011000341d000c94101c0002501040b203040352818100c0040c90301440100046841401c0090700640c1c0701060760b10304001840c80f6803d96068401c2950030b2900060200705000c00c9074100d0f502d03181ca412803641000c1c00c080c005249000000190902e003600d0b9a03521800d60b50750404c5a124000b01481901d41019915201c0041c091640302c40c200c1c0c3c1006500e50f841541c03400c003860 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 659513767 1250 659512517 659512547
    0x3051203060109350f03070f12050f0f0f0f030901090c0f0308070b04081b0601050108071d190f140f030606060708030a06030c120c150c020f040902060310080d 70
    0x10203c80541041d0300404c40500c504640d201c0e41022140d200c00c11710080c0326241c080c5954246006540c01c003810011002c1c680c0e01c08004d0b082002020510142d02581c0c000c0403c180925038680380804d84809500138000303c105103200c00030a001140e84150302c42440a0f00c10815034900664075089881403454510002d03090704c82c100b00c0c510005a0034140319078400c1c800c140041c1004210008600c1e45640884900c0c49e40c1c2c4030381c0040c0003030343e04114565800301040c0341582c0c085122600d02080c8482c482c0c406030140c808003000f001c01d00351603500e400240c204582d1411505a07504032003031690041284540c000d0300c80c014000d109040210b2003034401c40001e4080d0b40780c20910743d5004a154001018201380c540d5402011000860443c00e0300028012007441c0e8040e200710341010154018180d114a6108030318010803030b103454102000800d9650100e44c0200310760251008100500031000c0700039445200002001241140c0d070000074161a1200100e500c0c081c42e0240c00c1d038508040368141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 659515017 1250 659513767 659513819
    0x20f101827050c1b0607020f0115060e04090b10090605121513080f090405151c05010605040e0d0801061b150b030a03050c0d02030405090a0e0703051203060109 70
    0x146040085642000d500240341010780c6103000070041c3c8200e0500d010b104410025081017003400252a810048520003540d40f02c020400d003000302c141c0e114010403a204d42d00034020b1849644005907980d80c40a10b000390071012100032441c0076060310902c40c210f409040006454580f0104503801c104808204c401156802865050490240e0035240e8100403c0c0020f08a000054100003c02c0c1902400e422941d80980796102d0469000300000c0d18801410010540200e50480282d80d07a000c08102660310096107821503000c240c240340f405130203203030807480d0042c0c280307a0484c0b90300e50300251a40d100710059403107080780d0b601e45508450134030407503d86103568224080c8504c0071400d0103121844000d40b42a00040c1e841045001c2410060001c000b030340483c1c0d001c182245410400e0028448080b4548042e610381410000058204d0b20054051000950b480f4885040920200406d0f00a581c01a04a41c030743c0141c5462018a503104a90560004091080024003240c40c1c401000b150404030082e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 659516267 1250 659515017 659515079
    0x9020c0c04180c090b0901081b040b1201150306391e09180c0c1509080409020301030c0e0705180621061e03070e04020f1018 55
    0xc11024215100800caa0b85a03807060500005003500c6034003004101208011130511484010130014000c141e101e0364540e0030000c2511072108202151540e81d0104850010701769110102040140c0d42d004034008083d032905110200496122508a0469108020520810802d150141b681c0d0415001c481e509103d00185449490070001040418074018034101c4980c4d055100d030780c001c00d05031110100200b03004a200344070000c1ea2480c1202c441d030070100d0601c520400c22100800400345410040c0481c280004c040d4110140c40c1c004400260304107043c5500c4503121141c4c06c00951007031008403542e03521180001502820114060700c100c050391181030400a51515040000304070072483c6074805801c0180101c1324a0410300c14028a5111807260032171310f0302c070040c0710742c1035604c01c090500c484880551400564001400000b55454003200310065211440440c520b940c42c2d0051581c0103003c81021b10b6040d0f80038041001020344040c0c540145030f517400b05046801d134910940c2d04000c41001e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 659517517 1250 659516267 659516269
    0x204080f011a030d080a110f0702010908120d0209030709090b0708010603060302060f13050a1203030b031203040f060e030d0507080f06030d030b030c04020f121e01181404110a09020c0c 81
    0xc0a25840b03086c0c5900402c00d0460060303c0c0740310b44e1103081e50f500c0840c0007080000c155688407140c000a42210310040003042e10010303050205000d2401b80d1664281c001079503003000e07102800413900400140c81c05000c0e0007407030318000080f40000c8070803800117140c0c0d40000a50a00c80e002d01c9080701e40113080e40d450085540c08040403503001d0210042488101000000c581d21480d00000c0103000c0306030003c0d1954200d250050130b8441c9200d03207600c02e070701c1000002c0a82080404403500603074003083d44000909140b605502600002e4071842182c000840d488440c4c2100750461b0b4407589640e516407400707079911419080c10704001d4600541580c0540d0203410f91038000e40c4404044100201110071852922000805a0707001046582c070581000c01c0310840b26441036000b079006149085040506080580d0303900080c401445840306488242010481251069202c0141004461807051451800d4180b40e101c08400f0307400d041c00303110360300000600c0c10854800c0c2c41603040514042d141090480c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 659518767 1250 659517517 659517527
    0xb031504090f05030405030d05040b0a0f090b0a0918140606032e080d0c030e010807050412120219030512060a05060408010c1b03021903120204080f011a030d 69
    0x1a480d00590748481460226060015a444251140c0002c5070b4841c10007042c10304000d81600b0f481c081c0315092200344141102d0205441c214601d40c60880040444448201c603056400e501801003044002078083c0895400904c0c141a91420754200b460480b084000504891011a0310a136000c20540400c84c00d00d4000010758104016508485541102a4805000c0c02c01100040792480c1e00c5407041041c10340501202c1221105820b03e44548052600c0c01b50038038610082850400c810310000603001401242981d01a0150f000c40312403070106407400c400301010000c0c0c00703409840796001d04281415408490310105506545540c2855000070600050f01000b47c151a401505160041001c0c0c0350710000e04018407480300041100c54034800054000c40042c01201d8000b5035828441d0b0200740c0000d07001d1480800b44901c2e50070244203040031500e8802c0c041070301500500004000800d410002034124460f4031040007004070b400c589054000b9629816243c54240d041540781c8c040700da010b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 659520017 1250 659518767 659518801
    0x61509030204060609212f0414040b04030804030201061a070201020c0a060516060605090f0a0e031306080901110c0c010329122514010206010807150c1401050414070b03 74
    0x802c10b000c092100e030310060445102c1c1c0402a101c12011601f29060380c07504d03000e0100c29100080c00600141040c0e1148550b10400134405000d01c50040042410140300354881002061440f8040e512503102c50303c10205640485801d034018480c000544880b4074003411620220784146e201c3c00c0c6490b5168581c60801c40a00e84191403042d0f54000000d07440d129074900310711511411600342201e15000240c9000c03a00c0040400c032aa50061101801c2900e041d5540e80685105040082d099601c0344029030240010a03500c1000f11000b28625810a0001920320300b41403007620180881310780603d07d50201e0f0004035507038100b0031034030100c2c500a080805054403402d00704e000351001544c82081d02c0d5040c02d90011000b500c00c1150608000741070203901c0c6510b035007900344050310940d407600c2c5810b0781d075080d00d003c2c24000b80402c00c0d80c0c0b000580201c00d01100309620106021100c0d002d4148540223000480b01660303120754a050103001403101044540550341d003420401d003103445101107087c0d50407035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 659521267 1250 659520017 659520023
    0x1080912030118060e0c04030c0b0a0509010c0f1406070e0102030f0a0e010c0b0408070c0b03310605090f01320a1d100c0201060f031506150903020406060921 69
    0x620b8601103a45d401e072100c1c2c14820403201c101c15a40e40d1039840c0541103011030341d2003004410002c0c496160025404011100908401d1030511a1483c042c00c00480072080510001c0001c0d00c1000004155100400d40b944510034a031106083c000e40980103a0b100d1103040c0c42410070910822020304424050502c0c0341c0030032010b01d072021386140a6034480c00c000d01c060f030f416a00d842e404500030302001a9910a20003504030b0110050660410102140700710506e40c1081c046552041e019581219016002d44842d80e0444400d00542c04c00d6903245840d003608080d02603040d42031526011405201285220561980703d6228503c1000d142200c1c2d440c0d030010b81203040079034503410041821001c12042c55004000000a001215001440c02044400814100e0309590404e0420013550700d20082d1503085039040010710340c80c0e5001d440c012004010581002c5610b1845018082e05503078040000c0050301e2007a41d04010041c0c4486003601d0321000d40c441c42040100590301c3c0c0c01090ad000c0048550144 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 659522517 1250 659521267 659521271
    0x10905010510050d0b062106040309030213090209040f0510091b051c0611070c0308120708060d080304020310050403020a260f0a0909020a030c080f0c070206180a03030e01080912030118 81
    0x200c1103402c1030408c0740c181d40650018000c40b0301402135180180003039504103002d444c00c00550300320798040742c0680401000540300500c0c6101110910005128000e00300721010002c0002d22824503110140f0b5040074501081900d1000d0041843e01b040320070300c1d40a2088401c1e002c400c3e11a0b075520b030054407030051807422080d01404500005488448500040c0d48220700b55511005007081c02c02050704020821410400160280500c1e500d441e1300c1071344981c0c1c1025006a80359114004039241038074030100c07450200d02d004200030a15a010a2031802c1d10301c6890700e01e100c01601d103540f03010040c68504a03c0f14650802908568401180040002417441c4c04c002c204d943e41c2c4d48044040b13811803010000880e0312541a0803080e40e1242040354008410801c01c01c0c582492000b40c0140c1c01401c000034010100003074200c880d0000c6850021071100c00404001407a516441c006207864010903803240801c800c500400e40c84940800e241c0c000301a0319050508503803902a03003110354114446081d14044d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 659523767 1250 659522517 659522569
    0x803040b041a040c090507022d0703081204050f0102030402030d1b020a03120320091012110d05180606090a1d0304050f03070b0d1a03010905010510050d0b06 69
    0x540d2615209100b40c1c002d000e00d00c0402d1030120048146d802c010014011074000142c41d00040c0031902c0d64011500048000900d120100b04030305241001d96000a4800e01d00810101c101c0e0003160b03440340c40703a84188256296044000820b40c2130b40400e64000394580c10404241160a21500b0f82e2502d010a011017100b9203045500030440490403500b0030b0740c6015208020301215509070040c0301c0c2d4965a1030654031020000c001d060040c0c0600c4030b42c10310601038040110300b424420400144030070718120040000f401d031405c061700b03290312010400e0009400c12000800702e4860a50507019034031560080e043c1c07503455208100c03030154024206401155a090110030f03040d40040d4281203240c1d20001956a03a040c00100040c1070340d0640034a00c290320210313062103240e03c001c09072000c40b2440180403980700c00203041c04c0180c5542d1811130ba055880c148da241d06200701504214003522848944940450b141c4060040640212201421b50a4140c02103007090038515501c068101c0481302185003a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 659525017 1250 659523767 659523803
    0x1a071e0f021804030e0307050603160915091a040b2b0e0c1903030516030203070b090307060b040b0123070210050a0f02280f0501050a090501050906040803040b04 71
    0x1c02803840b4440d511030010003000308041d00040340165a000c103e00416465151000094a61000030700b0580018030304100107044500a032038610103068a004506a0200c0ba0035004020b00c15030310074142504104088a030800817600e0888083e0303426404031626042230b10042c6540d0003850340d1441c0034003035842241d4105040324480c10203903100440103006d0600070314080040307165034904500c108151241d81040080e4100c811502e0002e019900342d40c460345503007003c6e070660103294005030020005c6010030102603008001040158410882080703510840410711040b50b900200c1c56010490a49240f00000b0740d403401018041079003902c1d5072816506074003290301c0451150a00000c40d001241d40603645411405006490419100074007071010b145142481c6000b0b081d041480a02d0985c03c1c2c5424028081840b030402500f103002406181072504688004101c1408207803229440c1402140ea2440c010414900407500560f4550840c0c0341e50b00c5401c411040a002100c2c1c0c0f030380010703a034450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 659526267 1250 659525017 659525029
    0xc02060409060e16020606100504050d03200a1203200d061a09010801150201020c070f0f08011406220f050609360c04020409061a071e0f02 61
    0x1070400c40e0710114800d841c00c80c4070955490003419a042d541130b84540001c007550b0025242e40d1002c01191646481042810213894034410707604926004020210401d081c107801c980350000794403103031440800e01c8400340c003030589820099100415003a038030000301281d1880303a04072500070075633a100c3d019040b030300090352002caa119004001c61561030301d00c100094884c449498101c8040d1490803840c3c854101300090880710140164030f240075240e070740e1080840c400d50542c1c204c1240c0b00211761640341c4801c1520306c44196441140e4140d0144500400d440d0018003a0340d41c88841c0300d0300b1103840d40707560080202582100c60040c80005142502c8011090b0900800808030405000000c40c0c1c1401c000b840b00e0300704010000a40354441c00a11124500c012420342a2012010301800031a8000740400342484040da0b80540d002d0300100700030440a61a610090841c1c8540d600099030604c001e00c0d0018500940c03401a055030a20124960b080303540b0300900e08080d116400300700c2d103081107a0008107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 659527517 1250 659526267 659526269
    0x6131203020405030a0b0a14010803040515070b10050907030c05180409150903090510020c040b0109050409080c0d0927060e0f16110a02060904090f051029040b010c020604 75
    0x39425001e0041c400702d44418420310511380042c01007230040f513040503101a5a485184201402200030b40f4202051080010603591031a03488606c0c030002e42807400080a1807410750107a54419007542e40031903402c900030321801c221202c0c951103076070405008605040001b81d40103010f60300300d51036441034800a50f10300400c102d40b011a05c0005800d00241c01c0052078000d05800450003a102d00110000c92900080c02c81c0d0841812078000c64032071084001224505001c1d803116070450304028141003000072440c0900b81540980040341c0710700c070031035900301d40c506401e11464140749131450000401001d203040307081c0d11581c040008a8429502c01112101540440300619013103000ba041c060602a024034811490540c1c0c038000e40401c03810103880f512180240310091140c14005000e8030301d81c1340c540089040542054901d2200305d458144030b9201c01d88901452099032429141142400300500c107090210f01c0e25076a062120101b00a0000a00d00c00040f07505114400c112940140d075405d0041c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 659528767 1250 659527517 659527523
    0x11e0c02120607080f070c110913080406030e01180317180313210b06060705011416020f190303051512010c1b0f06150905101706131203020405030a 65
    0x110b06480c0105c840000c40c0006425541009400110100420311008091040400844060039940c5030195254840da44544004001c01408a0002805505684956464070903040244961000406c4540c81c940c00341c54010041603000c0e1842c40c8020180802540c0b12a114881000c40b0f854841110301d542c204003516031004117071032020310640003208800c01c900103400542680c2c80c2d5069550741440c0c4001041c40d0b0064001150035400d02009400400000307450001600c00c03410886000d0308013251011f2400c01600c600031920010b42c500103200d0f07040d81c101d00c1c00341e41200301d00d50b0100e0240034040c1520800c44080b804c44480c03a6a0284024500c40b40c44000003451314940720302030501ca0b0780c14080f031246502500100045104000c00540c4c00b07600c034034005902210080010700081c40e030b4221001040c5041c04000c0904520300007482500c0740c00d03001001c460a22641c0980e1940200c40d002544100c1032848400541071a82403500c110140c1409410661260042490924556819 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 659530017 1250 659528767 659528777
    0x1a0103060c090801020703080a0b0112091a09030c030d0c1106090c1509090406020702180109050603060a022803240f0501030902220204030215030f06011e0c02120607 73
    0x10754003181d00010305600410f6007000135400c00d88591000b81151000412a062081d214800c03005242e1041c2c0e010310490580d21400c0041100b20700700501a070f000b40074038038010503603000881c0ba011000016134070700c2c0004000a51600080c01c0c040c6c406480380d418140140000c0b04000c002d1a482486081d02ca41a054001c202031248a0f0800c0324070024218102c41c0d54404014814080d200d82c2d0040381e206411440140c2c2d1007180780f0200e42c603441e89016418440c10002c00116003503243d504094041c2400300c08440142c1c540202c03031000c03486480100c07442c000c031945190002100500042000c0c149600340001c0d003404407410715100000c240c500f03c1000d000044103101e1000c3e944100300251a00b0700c0d0402ca103040c0c5501051211001d442d00508a40c610340e0800c4030790007030790112000346a025200851680c1c1d0001000b40303540042d60729070110301c0d031803000550552188103140ca00f165044071902542500040544090f4140441a07800c101400145008401c00700702150259400f50b030340d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 659531267 1250 659530017 659530031
    0x90c0c03030c09080d0c0f05120408010e061303180905130c0801050106082703181008060112090f051207140613080f09120309040b0108041502071a010306 68
    0x3011107402414a8091250b4202d0500114000140300e082107a21401d106d00300300c02604114080e91044140140203100e056041c0d1156860040a0320403107204000a001c0b0110802c840742c0c40d040125943e032405403000424601091084101a080705c040d04003100d8200d403182c58007010f07120b040324404284030200f03065000300a05403241000400f0650000c00403541028001003041901a082c440c0d00d18812102e545412038042d07000225407031200440c1c0d03803001842c6d21204940f001c000301030700c1000070000040485014100c0140714042c16582d14480410080700c2030001c02c00c40c001903030448010141c0c0710026008106e00140d101a007044961500900e00d0400c0002408a2a42206401180034845995a814414200d16601031061511031040700500981d0740100b800603584100c1d040710b4810340e0310000c0001d00d03050400f92420711000c10450019100040c0580e0700900c601c80141040c000e4503042d9000c1c1124a1180004c4644a0b404100704101c6020a070810745040b40e4a9038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 659532374 1107 659531267 659531273
    0xb0d05090f0a0b0a06080d0804260f0711030f0a020906040e19110f060f0f07020a1404060603090317060f04020c07091505031c09090c0c 60
    0x8200c40e090310450405415100d0150b444c0c5100b5860700c1e00106017928040b50302e4510002c0c54844000301c0d1541d076107203100c40001c5c0d2700303803045d404402854610700741585000b804030968822a45031030344602e00340b229004040ca482716210b40e00c4070b103540511030400704501d403c1a404944180c880d84d503c001082c043c2510709807510883c02640010310101d4011b4428840c003d00404072820301080010034001c3e00f14445600c240d02c08014405013044c0204400185610391581502c541424400e0f40420b00450700d5400482c84405144180310050429104800c02040649000d00c040f004a03180945a02c50001d290f1501c10a0100014080e4560510070b6010b10341c0030300115524552401d48a4407101d043c014001d20030709040b03c04051030607002c0080203841005000d0603002e1030302c90144c030340307003840c10b43e502c00380224a1800101d108203441401019100c0b13840b5103c15820900d = true := by decide +kernel

theorem cover : BRFrame.Cov 659352517 659532374 := by
  have h0 := BRFrame.cov_init 659352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 659352517 ≤ n) (h2 : n < 659532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
