-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:53:47.122092+00:00
-- url     : https://prove2.me/submissions/6bd3d44c-c47e-4520-a11a-82e4ff18d610

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 184352517 ≤ n < 184532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 184353767 1250 184352517 184352527
    0x140f030f16140301330803030c03160c0c050118030f0c170316020d08091306090c030b010f0c0c0807090b1201050403021b0a090c0e01020c0303040b0d0f02090306010803 74
    0x201e1030b80c10021451060340208070309411104405111101c0301ca000e00b00d00c01030300d0f0200b60f04901035810b001409100c8256502c1b801c10020113082504245d03a840c0102c007819800403102c41c0b00c1d07466240c440b42c10001c952840c52400d401510814034007808003e03201940d510210106050680581c02d0340e1040c903803c07850a14080c00c4084005000152003c1500308000f030b1180c450500d504124a55011a0f980c4205000c40c6018041803250352101078102d41c4407c0000c10b01030b13196004034116503055106000300344425208800316080d022016000c2000e010b420310394144a40ca000c02400d00c1201c15070303110b40e2500201351070f2400680c4410b010703540340c6020f16030909041c3c69000384585100020304c401e003402d5801030340320a1924400c1224009010b0102e982e40d42c1d442401c001000c0358a420010801c41410050080380403001da94058460603100b1000c506002045804945000c100e240c2000d030030004e0034019081000a4900c00c1c0d03001d00100c0725a035410f21000d4000c0003043c000b1a561 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 184355017 1250 184353767 184353779
    0x80c0313060e28050603090c210c010806091501020106031b0914010e0106110a0b01031a280b01030902030610170f0d1101020d05010803030901060f140f030f16 70
    0x2d90103800ea11118540c50780038900c040910003820340d05a40701140c05c1610f076525a800240f50140450b0000d034040460440e5801c0c00819146448030705040d2815903001e90761503c0156103040d0f080e2401a0000380341c0000515111902c0040204808140300114285a8a0315458003280843c500c00103200310300041088607141c14441c0c54440c160045044903076614210f1080c00000c2d0503c1001d00380300da80552500038200610585c2c50b041e81c000036900c1996103a0400f20300700d454024a22401031510004a0300800341d281c244c64102500403010801101042d0110018003404e40e00c40381410b845949410050b9021b00c5583e2103507803004018500c803031030f00c0d003581180440d01a0096150f04142e0b5480e02510740841c0707142d0600300078246440c800406102c224024030540403481010b0b45006d00101d0900c0020000714000c031000802400400d07150f01d20705141c200540309003005100c07070340a007450324101440324143c0200014161500071102444850070044072843e00400441102e00078881 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 184356267 1250 184355017 184355029
    0xc0906080105041a0403050f04290903060105040b06070506040803090610060f050a050c010906050708060103020a02150c0408070b09240304060504050102090d03030506040507020a02010c080c0313060e 88
    0x1049000000d100c1e60425494000001c100e010140401c03806004c001024140510101c40038840c1d40105581c9d2130760b5a0b0203001031071004a01d10215541c40f600741142d000041d4013070b600f41e007600801a21441e417902081100800072954070b190042414050800031407028032007544a140940f1300e0b180c3d00c2c5440d0a5042c18400000d00303500b00204425400d0000b268021546100c08030755081c038036628001c9000a80700c034080c054000c8425800d000c44402008041d81010f030140daa151601913103522604010340c1640145084980180c0c4940e04804e01072103c140e05a0300302805811451034280c490040500304907441d0464030101400040100e5103081989089041104a1004483c401840c240d14241c500c0041d2000d401d41c0c2d100c5020605100c803e40c111908100b00400c04081e601c036514015000d0101203d205101da80703000000f4480e030f80040b503950042941607550082130b60444d42d41c02c920383c2000b8200c04d4944018413062a03041134482814004e04606d803202d1005070141c1c020040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 184357517 1250 184356267 184356269
    0x9110408010b0904050604030302091516030905010327080c070608011508160c02041b03060303090e060619021911031e0d0f02010209060d0504020306070e0f0405041e0c0906 76
    0x10094088000300700105d50f0109910f07810591501d00036a44080040008030300c4a00d01c0c595000101001550b4083d40002d9070000c0b10907482a103401c17034050f54660040d000c980c9000c0d40c6200c01c031001600c07044401c0c81c000b14900c2151113130000500b02000001e4080c40c00e68290060408074610b180140000c0c2c880000d401303001611450440d50341d150407280500c0341c0e040c1c1c80e06403040c401000c4c01e500465403140c0210032400302ca0110100c010002602c000c018040c1d901c42580841c0c1900c001241d04c00744002114071500001e01202d113800408020001040010703100001180241c1c1c8034080e000460300502907030a401540c00b08480c0501c0d000f01401d241c040203e0b400a10f56000700309080150200e0150505503241c1890f03000208000e205030b01900c40d10740d001d40d101d0340019030000800c040d540054055402034040ba80700e650743e00c009807508100701c01c9059012100000d6181249015001241e00c01c7c81401811010a00c000b04a6540e02c060001100d12800c4c1f0001032001c4007540c403171f940c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 184358767 1250 184357517 184357519
    0x10605010815060a03111e03060a05040603050a1e050d0815040e15060112020d0f0e030406080606090d02040c02010504050f160302061e03040507050a0509010506030a0e0709110408010b 81
    0x240070b50700c0b000000d0468030507101c0300020f06440b41c10003503c11201d4025507060201c010203165000d40c4400e10b0100d00d60048506074461054944049041d09051207032000780ca40c800700a0080141d22f40351940f9451101014810600d180301c160300c0010400d11a411003604c01d52030b0101d8a0400481000108600010f114020351400b80c02c03125240c1b0000e00014001d103140d4001c440c60f254200102e43c0c151800a00e29840d50002800d000340c01415071214922100482080290b490a2840161a84907070311036100054103800200e12030345410700080a00076801032404002004a50100b0180c640e20340e0f4800240c1d66441c20081440000d0140100000b014400703000c440d440e41070881f040c20080d00010707000e40008510705001031152044210000c004a2496499240524001ea034844260040c40e000c2d107044600042c950621011702da0603144018400b6045a407400300000081ca101141f94031a403084070f0300043c003400684a01c840c8880d40040c069030300d5062540741400c1d41c009040365 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 184360017 1250 184358767 184358791
    0x150b0d05030d05090f24060109180c1716080c0a090306021809040f05010f06050a062709140105060703050f0a090510110c010311040626090106050108 66
    0x1a4000410200844210a1075810300103100c0d16101d0b401841d00d00d186895090340e200d08030fa003c2803d00981c04040707440ba0250300c1c0004540d078020044800349003a215400703203a0304000707070254001016080007600d05407a00d0301104480030802c0f80405900c0036110f0f44039140d2404290142240d018503000e60001c0305500302407074034401d03200c014500c01003844003034620799000c140c05c01d040d05011010300040c6001881c2c06130904050510141d01c51003d04110b4540d868020b107110001490f000340000c440d80245a5411246031001c291000c9280b05010000020040f406909407a8184030147c084c0020000c0002d414280b80101d00300c408043e00080d00c80d402c00c2c03228200103507203c412146040d041c615456204c0001c0081940c045c030054011607806142c06184010040c0d10040703440401803003804981060325198015001c5403071006080080080800043c002036024589514130400340703507202405030f601c03c0e4a001c0154400d440b6824103946900c4200059039005050f913170012015002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 184361267 1250 184360017 184360039
    0x3060f031506041a1503070f0c021c0302210307030b06070b0a11130b0d0b0d02010c0201030e0c040908040e010618050d020f040509010c03050702070806010b0c0a050703150b 76
    0x345010341070000340030b41d12490710303a0341800e105030751000a80d806034000b80104004108402080900c0c2e0400c5840030000345e0796418000903e80324200e41410503401424400c459000b01d03c425082ca20548030940c03e521554100c92034418542c0091074000c24920421601c07401c007003034010290365948501c81e01c00c0e5014080c10020030000c60720075810a6100d000001c3c407610009c403a260340d000b92495000d503007038420300002d01c0003c840000c0001e401602c800304200404d460070450b5000100d00e000c2c0c0050341d80000000107502030341c440c245404190040f5100c0c0c448541c00903054440d01d042c115890070340854100300f0004803214082c05070a050034090480490b81c2d0308078207501c0c02445018403a8445149003c01d54461600c0c0c24410782c0040c1042c0110b1034944041401782008181e0400000d00c0c1c1400100c1031480443c1220036038074041c01a00b0300e80d10341076000c40c0c180c0004501803414095000303100001141000323010010344c814036004d0442d18015458404459100c1c0c07103580a07c8110707076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 184362517 1250 184361267 184361293
    0xc0209150102061b04140f060708121003030f20070f0503060a0e030d0b010c0f1b0605030c090603060a0b120a0f0606170403020106180b04050a0b0319140d0503060f03 73
    0x141c0c5e040d0354001c0c42ca104880c4c04500060806600b00030b00c550046000a03445050200b01ca004003022440f0101f4a4a1034490030344408a0300018400074000800015503a080c0510031642981d0301d40d070101c1d07920722189443d02000e0030104158400066895580000c22460400307000342580711078040c0080003604010003d0b25140c0c072510420585841d920105500281c4c0120035400120790001d02464240b4a6031a003080c1008270507900c40500101030000090b00703840780c02260310405200c90038508050900d001e1010702d03000504007981c8060450f0000c901e840c840006482c03650208580c0302650b0800100304811948444481801ca5080000c28407607183c00c40c0d2038512a8022090400b91390f500e504080b401020b03150404a903880c0b0110172900000903540041c9a2030904403402c200c83c0c0c489000d080201c1d51100341040d003640155202d10080d0080c0400041124001c00b03c2d507402d0700114100c0c41c00c01c8003486840000c900d000c0300303010035801e01c51072440e907034601a401484c070350344403003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 184363767 1250 184362517 184362571
    0x5070501050a02400f080c09040305040b0f0c0d030914010605010c030f02010e06150127030b0c12040303020703032409051003080d0905060609040f030309030c020915010206 76
    0x34400c0c00131055607a6281d40a200511020005007401c56411002c0d0380c50384400c80e146492403049010b80d1050940c59080c030b02d0004440da02480d030544800e850070345004056007490300192800c41c40500d0520408440d1541071055000711280f6942c005100c040310b141c1f240d155003000920440503071610800f48002d9810448140300c05130141406401c0c802910000ca01408580902050034020741c000c1c00708490012035140b80d02282602c4004601400b04139074140b4140444412116002144040000c2103400c2c1e00349400124412075145030040e003042510a900064408800080d8005a440103142d07251040702c44900521a0910f1100e031001406000d003180d41c000d010f8169a140c0c0810b00d160342e40d5441a000307507070020750346488590038a40c0000400c04984140c1d00c07070103008001411890710303041d011300c1158088000810451962802c4008040e881412424400940103a00140ea10700061034440d14091084a0640c41484002403c2883c013414002a0988001156a4882c500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 184365017 1250 184363767 184363807
    0x1020904060807120f1e0309090c02030c070b0705030f03040b060a091811010e13090b060102010207020a03120c021c030f02010c09120221060106020d14030606032505070501050a02 79
    0x1103000d0f175441c80c030a81002070150b58807044500a280b0b00c1015034003010b4000d00d0410032544100d4007049141a00502681ca0f0b1052041c00e4506401caa00107025415444000c1d015490180c0101d0381402c080c2c0d050b810265000792002d0360804075030002c00680740b91011050340a0803c206052100b020400005003c4550b8402c0040c12685d00e13501c0d24850340d2250304800c5110304014585810348401c002101c000303180c10003003629004030150000ba155401402180d81c41030b800b4045141882c51600da01d02c85640c00d9400a041142c840945000742c0d0b9610080780b01c1c8440b07075a0011040459103009494015120b070510300351390500f01d20403a00380d04140d80c40100d41801d41410707801402c51002901c03c542140e18040000040b0340003620145002030510f058507141d80032940000a040c0051310003050200010510b900100002030450030003c1c0030b540c0146081648007500040329031410401c0c144002034000040c0041070442c14004240555600420921421840c02c000d022203075040c1110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 184366267 1250 184365017 184365023
    0x706020a030c06020315090703140603070602150406060504110a020d170115030e030c030309070e060d03110a0f140106060e060405060903150103050616020609070519080304080102090406080712 85
    0x10100010740c506c1c00f00d0400c80c405280040c10f0040ca441c01043c090010010080c2c0c5c0408d011200000030304a00b800102242520303d940c0007054190145014034090300c100600495440c0d8549400041c5900d07280929030071007900c0140251140750020700203103003050180040c0b0804c004104550344042070000f613141511101007008011003403400080d4068541244591b800d44030001d45c12060388000b00146000320300c03900c25249a50f030b5038100b41c410058241d0700e00e41d00403c40c101490000780288150440c102001c000d55001202c0d1786c841115554800d00b041c0d941004a802d0b005d0003040a1141d41c02520560070038850312514071002c5103060059008250207801e0000c1c1d03404941e94100070704040c3d209080c11130401036849140c0381d61110010384010401071709000706014020b00204032a4800d101e00710080c1642440c110400019000641002d07002100d9407030042060013041c001070028211410000d030341d40090b8001e1000300c03501c0c0c2c2e201500c00e4000c84418041c43e14000c80320540b240d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 184367517 1250 184366267 184366271
    0x201140f04030c05090702030c030d48050a0912060209060409020705070515090f13020a080f01080c1003090303180302060f06270c04080d0c050706020a030c06 70
    0x54400544095031190354040c4444010101c0c0010030001401502800c4d100c0584000c001500e4008051f40e4034028105141d04035007061102e850f01110503480070012034405100305a07409284404091144601d44001ca0b241c15404400d04050107280e41d1141e503105a850b1176480d1111005005144a6150045004e034580507204102403214940503250040c3c0000c29042d541c3c2e80d0b440d0120006d621400f0200c40900844070002118a807851090450700341e41c100040c500312090041048032007054884981c0428140c091003403066803440a0b0403014401e4861024a0130001030300000d50005034810b403005e501200c01141180c5400d0100001c3c00d4003030501144620706440d081d0042e0131840210b14072001c0c5942e0400905500040c000d000d4190320b0000307092526a50706000a1404043c10018041c1504864a9680300b035104840e500411000c40e6504140c0c03075454540c00e25210381c4045001800d0300c0081003e2060501030840200344500080c8280c0049175000b40880e600c3c200007802c03142d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 184368767 1250 184367517 184367537
    0xf0807060815090903070c080109020604031b0b0a03020a17060312031306020a05030601030c08040506150d0b010e04021201060e010603020d020702030106081f020f1b19050303010617060d0201 84
    0x1110b880100c6007500e42c003d10049240c9041440340b03550344c01040d0160341207011203100041076203042c031a40070110f0700600881e2801d801c0d602e524031929041c0c107922234421509100082c0c0006598041d01d0000d21640e00940d0383c400b0380c40001c20030854030b001040024034160a00a66a800003080c410100108600c9034072923070b4807030482c1c0e6250f415140150000e400018140000380e4410b00441c440c0761700345c80411400d0140541207900e44011240200b00d503008201094400522000480fa1910010040d03807150841da40e1703501d4032442c00c2e40000a45445034040c4421031131712240c103d004850400c02081090320305504081c3c841010b00c208414075900140ca0504040946c04449026402130002c0c04038603510760700181c0d20380801011504075401c1d103840d03040d6000300c1e0084640e49d0305548859070415494181c490700000f00710814078040d1007100242c0200c03030742559100302c400740500c1c09076449616000c405401c4030149404007207500c0c0660104006541c1d010754461100e83c084c40c1c484110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 184370017 1250 184368767 184368781
    0x60f090d030c05150a060e04051509030d09060f0b0102030f0301050d02130203070e13110706020a09030507030f1e05210d021206100c0b19060504020307030b09010f08070608 76
    0x102600030000d401c3e03008030500350403140500c1c0031213400364144003010071110b070759810170b07125030f202c140d50040681d00070040421881c0040450540c0041459040e03a10b40b00e81c00140c04202c0c1c513008000c0300c0641c1c958180c000c05800d01c1c810500d8250080c00a1803a1911020b40c499862105000c0d140c820b41c111081c0c01c080d03444400d84a2a41815448219900e0418010140030303803030300c20800b5114034441c0a09000f0020740b8081d01049162243c004c90401c0c60654919010390010180c100070001d5069002010590400c41ca1000718000c10810000d89c40178100001090707484c42d4450103021030b2201260005000050f6215100c3c241040c40814020540040c1420b01c102c0c5800392040f030000c1243d04064502c42026030244508480071800014201000e546428007201c0181c460b401e075200089090410038481404010514800aa0151204006400c98000340c540e140001c1d5946108002c904102c903229015181414003040001e1410750300c2035642016001c1c440400c04180041610 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 184371267 1250 184370017 184370027
    0x213120609080708090f1504030b250f02070b0415080601020a0c0f050307080a0b061002010b04020315040b0904050d050901021903261306020c03090405070815060f090d03 75
    0xc55101006542d90522403e04c2d000340c3e08007190240c421038500d081490f581c640801d03e40300603011883c1450800307195407100c0348844001010500203403070300081c9103101e2105100c8100311a2a50701c40000d41c145100c8000d1810010750414190008204410700c141203034070408101004481c0ba100c0b81640da41300040782000c15200b0014060034210380c000c18240c2b0b2280c524019104154100d60000e9600c501c291341c0ca08010801410049410020038443e0805141101000c1e025000214440089070041400c9030300884826411066004242d603103031030036000303200d401e400071141582d442c203103920386c691a41c20307500551040c0003000620a03042c0e402480600c880728074107606169000a10309000c2e10342e07004184280b011000d41500ea41c644100d034004c407800790303941c0345091481000d1940e034480294031045c2c582c031880c4401d01c28851a9540d90042c50b1140115958900042c03e0078802c1d0716500020b5250540300e6501030000b10600e2800900380e805042044840d54664451401e050750 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 184372517 1250 184371267 184371281
    0x708091306080d020d0c0803011415030702030a09060e011d0f0301050f0106021c09050d0c030605090d020d090315050c0c03030a0506010f08040b04020409150c020109050d020102131206 81
    0x8441c2000da00040c012070201c1e251021081503000d48075844400c0b0002c03240100100b500404060301400148600e0447d2a0040f008030006446040200100d06850400380c0040ba20100180d000140c4800c0c090343c0b00c00c241004224901348200301003512000a80041c40c0d82e502c400031200c0e0401c1f1070102e07654001940100c404041c000708014106250b4014601509019940c094031031445103c154460020000340c400e00c451392000d42142c101002c04c41c20b0503086409503144503074600003001103442d91140501550013280100450601c89201905010403260a0400c2c0681c2410410110301d442508488501d1fa2000014469503580800d5459000d07900001d0000c0c8804020440458000d50005000380400d03201c070208241400310803100c1d0101100c0c010a14452580810014209600480011881b40c4140c1c4800714045206000b2a050010b00e0340040c1c4d101d40c14002401000d20010319491a00d1000752310340311a250744000545494429440f079483c000040a050003c00e0380000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 184373767 1250 184372517 184372549
    0x10050c090d0303060533161401090201080106050f0a031104030f08071407060504050906280e01140904030f0507050a03030204051801150c02011704030203070b0f070203070809 77
    0x440103000307034100280100072900032180160000400030443c04031081c20089906d506400707000c410a0b04d030309005460b800130704000c103000c0700541000707000440200e10000480c02d40d00000800d001640001020404183d005805201e010008101c0a410078021a0000f07092428041101014645032844070311442e0300181001c8042c00c4c1d08000c00501c600200350960040148844000074a00e0480d25000030388183c01c040395040000300814144140c40030740c0110020800c940203081200d006655070080d1056034200d5400703940a010440e1002000d501510011400c07401c15540000443e10000028101400f800500c1201e048041c0c410301c100c94a095000040c1ca03420051032a014020390481c1c0199803040e103030145482c13410020300000324100d40003c80ea14910300048102035032031410201c5c0070380c104242c44a000196400865842c1d008901c6a0300860340e03001c1c2070410030031a1002820888054070321405004107aa8000203075a40c854024007038a41d91401b1900107514101c1e120998 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 184375017 1250 184373767 184373779
    0x90c02030702100f02160b0405090a0b18060111010b1e03100618060801050907210503180907021222091b110123040c0509160e0d0510050c09 62
    0x10003c99401642100721141c00c2d0200d42c401400200d6aa03a5816940680c50b090201400704110610b8081801c54003c0b41c40b180000302074600b01c1c081040800340031951100e0300841c400b40401c95034000f25003084613103400000c1101c98805400140e4048540b07568803031281040c074000c0c00a84d000e00c9001c40c44250804200404c0350780e00000d0300a04400310710000c0c41803070a03000082c401018000c480c41000c03400d000c2c240d81030821003007050042c6c40305060211205503d12940003c0d8041005024a8005c4040900004c0024040040180f4001e01410854101d80c50161103081108140d491600c5034111540404680e0380a940500315154800c58000382000b40ca45840c108c000d001d12268a030030750f203000e4140c0182e0640390070f803042800305581e501100c100c90401d09581d141d105410074400c0200303040303203903903140090a070f4a02079410b10b00503102c0303008074520181c001880d880f80c0f810603164540403c0c2181c0b88d003501c60105d4030001c1c2c01c407619040040e580400c240100c50001030020a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 184376267 1250 184375017 184375039
    0x130e0d02070305071a0901200a23010b15070f0c17060109050c2502040c051b060c0a12110301081014090c010c030203090406093201090c02030702 64
    0x350340d000e05110070745460069680100e1750210005ca01c0e001c9041001c007013407910f17190400440340704461262140032072216128582c0c14000900c410318152740107040c4a28041c64a440348000300c0c0042d00c003030302140c1c5041c02004468036403810a403007032911861015241d00c4141007006105107901c000401d44000c0c2c5ca408550341da20515103c2d11a1008021246c4036070700c0700780060032500c1c203468101c030038102407001c60504607142c4040c0450b01e850003000481180c00303034041010781d0b0f0503440140205a0202e2071002025800c540c8240d00e40020005100034140314101e1115841421480803c01c42060f0310241400100e8000310009030700c0600c2a81d99603500c8000e6a281e0b081800c041c080181004d21703110418042d12203031801800c2081c003402c0c1c5000c0f07103c01500c8524255070b003141036010500a989460f5158496038008100c00b000119a45842c0703200901c0c3c0b500b000383d8004007085580d40c0c03c1c1c01504090070301e506540c800140065409840181a4907601510100a51102c1d10081d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 184377517 1250 184376267 184376293
    0xd05030703140a14060a061d030f030406210204060905060d0e0f01270506070503041b060507020f01020607140915030c0901080c04121203020c0109050d080711060402130e 75
    0xf120714031045514107407404d55101c080800000208510681000506040300c40c0d10140482c1c00c15100d02d04024201e54000ba107603030201c0e0030f5402c594003a4021986403080148107400c00c41c81d5050360018650708500c1c0c94140600501602003a014440c0105801b10314424190041d9002070300303880c070050450f0482011103403a68082e00052000304030387c00342003440c0540202040803201c20554000c02400c043e0f55483c60454032504010030a45280401060104c0429088103d905c0a03000d207030b5030242e645905005200c0b41100344500141158031480411140b1944990680304986054111981c1c1c2e4a03504001521804000811006c1c00b0000003404903031045c94008050401d400e80ba03c04440d0f444080142c683e02542c4101d070091402d00070040700294425440ca0b51040150800600781514003450608544200400329040d5000901d00d07001c1c69044032205038405d8880c0b40c031400780b002c182d6906446040c081c000a01601004000102e08101c54000340c0b5901010000c5500c5200b01da9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 184378767 1250 184377517 184377521
    0x6130b070206092505031c1b1709010c1205070302070b0307050901110f03120105040605010201050910020d061203120f050603101104050607120e010206060105070f14010614010212040501020d05030703140a 90
    0x45200082070b1751580210000715107400e100320642c1c10240510440d02d40303040800003075000ac0413050400102507110400968510f9002002444658810b929085070b4900640381819503040f4408240041c0108001039030b001084880000086c640281c030083c00c2e880300e81c40c140c040c00c041d03031301781c00b000c12114102c82445d203c0030304842c0220f4050040315601c0005a0032030f4820f903076141142e009500742c0a040b407640c0e00144410700b40840001080f69555010624100e02d58508030002038003020585071614031405001c4c1050141c4004122504010f00003035510b012401510380081d840b60314000c51410401c2c19640108400361030150345075514581181562070450410b07000c10707003029407482d05501c0010240d00c58541038494502d40101901e9840540b2001e1808440361218025510310124007809802c004080d0b8403002d010000d20703c000a42007001e0300790ba400040d242840f04001c181e9000443c640c03151454180a50f494503690400c9024014010a8820541415050098160140d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 184380017 1250 184378767 184378813
    0x3100501151b02010e010c0c030b07050904200406120b03120a080705040e060d0609060c110106060203130e071b030c1a0907090c0302070506130b07020609250503 71
    0xa5580c1c5003400d0b450a0040b004031100e0038080d00281d50500c034540b40394001c1c040380714140e00607080c0b2401665a03645503140d4450480312900010404038042a55060134040c0c1c16000c248405160310102d52420380380f1541c011481a0710402c01c01040581d1200500c1c0d120028601018084c2c44000c4909404a446684804d501600080800f000246034a2090050b0342c281e80e141488100e00d9114941040320150940c40141d662640c0c030310080e0002051407084590740e40680c0c030f030321110f002d51161807402c49600b07130310000a5403c1001507512100201d4444800c5e21003010f843c440c181c480c8030003100e1701c001c200c0b6002030a480e50070040c0c09264002c008411040c0c031030300f040f080031401d4104c0d00b0b0005009443c40c07036890340600010701441c00700d9000210b402203107140040c1800c0c05500c99624098040e0b98000d42400000030303071420b00c1214400c1c29404403041c002840305040001c00150368090300300b085403142c00070181444000100140351002040c00030f084032b44649680e441c41c4100d8101c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 184381267 1250 184380017 184380059
    0x306060b090a0f210c050409140715140d0905030a050319020f07060504050c04020708040f050d0c030303090321020a08150307050d020402040312021e032703100501 72
    0xb103400d000441c00d400d0011202959116804205459001d402405000300100001c80d00100c81070b40c00f05403900d680c4503a0107210f01804105800c1311032400311a003091802d0b0040c42115601c4c07081d11100c290040c155140e0441c0000c2c1003980c5074280c030780031002800d5145008001d4080090000907060303020000e103020300003028082076003d40308440b0204a105041c03418000e454184124004243c10390310560380a402030707042e19070305803a140008049070b21945c000c0b07030f049030041410303c40c10044004c00d0000e000b09454001e203444584c1c0755103001c4803ca03c801820551100711200401d807280074100081c940f20741c080007410b0b0001074404003035048081c514001517000d0780055050041c00d02c0c40c4c0710100010b40904400c2d41030406101917440b0203a42030740c010750200f10010000f0141ca94114042c1c845078080d00c0036281c443c4800c003c4c5458180d0061241d4820710a00c860307078484082d80548103600150780002e814840d8046070400d65440c2240010030300d40400002c103085844010500494 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 184382517 1250 184381267 184381279
    0x3110705040501060f050a12230123060d0e0613050c0a052b02060705010c091202060405040c02010b040e0d090518070503060d08030a0903140313021003060306060b09 73
    0x34455060000b121030902c100d10010700b0503425011031600681c0188803030011494111f0021001e8120001540c0340c41516120250344202614204480300070854090849900505081c2a80b00f886e40140962400b0b09481000001072074090311409074800c0a4200382542911014542107000c0c0090300c0001d502607426000303901c400045440c0107e186801d492004280d03000c6040c02d12086101880c65944603401000301c0203141001d41e440d0005840c440384070b00300114850a000034010400c8104d5445092404690544070b401030362100f081c2ca0658200b501e00041e207580f4000120b01502d824100150498500b0304181851080400c0c0044c41003030544621649660322818403800307115500032520030f032507107101048115201710000c6801401c01003064064012580358070710f0942c4143c5090040c2d990300c400321410540c0200c01504128140b00185045207800200d2005044078144020700c1050604454400039020368019005540c010604020f656210008094545d106842040c0300702 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 184383767 1250 184382517 184382519
    0x6250b0c030f1e040312060e0a020403230d120b040905070305011118040506030a020303031608070c03021507030e03070305030402090a0603170d020d0e01020a0e090610050309010b060403031107 85
    0x380208402800c801c80c1c000020f442c0303540b281c504850103400c1020380343d030703180d21600e00160034420034940724080c00040100581c0c452451070f00702150004945840c0314007401404411074464082031106200e046e5040000700e4090b14113107031005000307640b8000d60103440c1940110a000d0000755040170b403440385008010b541d00b11003c00d4601e0240200990280412070051101d90410340c1140382c020002900b00c1e450030860350b0000703045400803507549900e07840c40600c010716160b22501007600890300c1c0c02c0884450b40c0700e440003034039001815140c031000182c10300802c0c0c1140c4254003124a10b484842070700d854282c0b07450b0080040d80b0a80381a480380c0180b0740070645002c0c0360b206120482e41c1c040ca9210b550911021320054a411102002c900241e091046014412080c011042c500601000040e40d03401c480310041c00c0041c82c0000f80780035001c140200842c5403110090b9058150039403c000352a5540d03512200d015142c200e504071303041200803400004050304548042032034490001510806 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 184385017 1250 184383767 184383781
    0x604060f0f0305060a050d0804050916030b0d02101808030408070306110301080607120e010507030b010237020f0d0606180510060324080c120c06250b0c030f 69
    0x10326810303030f0b42c41e501908645c010004c9103496002141a944242e84203400d0554410000315011812210011100c44280302100e0b619818803910341f401c102110450314006294004c219110749429000b418020402c00c000520b07401c034440340c0020b10014003207075a030399110440c0945a90061004480071820640030756501d01452040d02e041c3ea034440010011603441490031640c10200003e5000a20383e54065011416400c1c0511480f4080c83c2d10f01003202c101d0880020716001d0410030030081c286110b00784103000300f5100e8054030307040342c0500841240c5106000182d1448000584e156002000010000c01c002d86034001504550038622250a0003041c50440015660122200303034200d898004244032080c001d901c0700c00e407000302e0980140d03541c0b580896110a0303605034002080d2580404004503640c80d141602004016030400038000051400010401c0f13805007041d00e064280400350560105000130cc0290103440d00320b10310400b2400d050081c40f03003e0f402a96464a01011140014a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 184386267 1250 184385017 184385021
    0x5031e090f040c050706060f1802090d061a0301020301030c26030703030903031409010603060b010e03151b03070302030a0b041406012106080318010201050c03010b0a0504050604060f0f03 82
    0x50100900760800a604100802c4000c0586440c500b0500c9010f1000c840810800d2191401a0007402c110224040c10024030310100c0d41409117001c0c0e22801005404100e48940c03181600310b65110341c0105400c07078102883c5d0f40b400344111007690198404130000050041a8154030200c408103408031410403c220111030002c1c0800c00e9011086d07108221f10b8000034030070340c08000b505000c2d1400040c0ca45001c003e010045000f41c0706040c2503910340005106000c17151242c03000c40e08090a0481405010001190702c500e4000041a440c0ba1118002250f410300c00c0c03282c0d501c82e803008140b41d50300d181ca004050029001914100040e0b45000c0c09911241418840c04103414401150039285a50740001110595035202802410501c04c00306030101d018940180c4e005020082c025640343c2e00300710681110280c502800e5811a1b062400f4410302842e04011641560b117000c8180b59260b0310104256198813460b48801d421140010b03002070300e1588a106054100c54a56603413540180902084003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 184387517 1250 184386267 184386277
    0x140d050706080a02130b090f0a08070603051b0408150f04030509100908030c010f1802060f130f06050a030f0e0606190905040305070b0a0e0a02090406090f05031e 71
    0x1803a0321030303081800250300410072a41e0100c042000940b81032054030011414413180d41c0701030341c041c001060351070442c50000190100d10405a40010baa18505440e196544074144240c1045c0340d0354001007084040e40200c2400c4100350f1b80386007907845694100d4181d0f02c0480280b200b00640316103022070725a558002e505070069405696607800e003d800c004010a0103102089031050054603080064140d0b410300280142e081e510b000019126030300c04540060305e1078820141e17040701001e10031500503617416003540d050040307001e403282e15041c0c1760040710800d0701c03240c11100410054200000e6500c0e8000c0082c00c03007005c103580034484444144050300503206110030f07429040d0016000510a810411401c0c2110f01c0c821529075681c995a484100484100395010303400504000703400018411040c4185403c075482c03110070040d22038070300d200585980420000078850740340140842c0a108160308064175094001d911206d000d821890610303a01d6012140e58041c2c1030380c1140310103868103039901755a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 184388767 1250 184387517 184387523
    0xd0b0c070b09010b090a0c0509030a050706110307020303030a111303060902040b01020a2117150301060b0301080d05030c0903150906090106030c1e080f0a0c0504020403030c02040905030c0f07140d 86
    0x1440588801c03403400042e02d47c4c0020712040002c140641c080c280e90401042a41c0360080001e04101810102c000702040082d1030000034542c001c000200060f20700104895101981000010f40038007188680c0c603031440b030743d01034000000c1401c40c084284491540440c100740c1c821107003013150520020041e078841c5030740903014100c085221a80380034403807482c0040d5000d5200385024050700c0000b0017036190842d01594031960400c1c210200000c82e08007403142e0000b4042c074051090942d071400048503601c2c0f007240184801c0010100205079000c4e060429520044401801e40d140c2c1500c03041940881c9200311820503040c410f540200310b0841040c0310b5001501c3c2c000f10020314070307410b04854550101d490502c0740300d800d03c41940015606410310070a400d0310001c0300a0080c6001d1402c1000e007104050300000d1055104000800009070801100c0541d1a0b041d100840c00c00c0e4107080c01c600b50f000300c441008441c001c411030700346038480c041042c00c1a994030421264810310b1000c180003400320458002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 184390017 1250 184388767 184388779
    0x10e06070b04170705070312050f1606140c070201090b03010605090f031009050601031505070c03030c090306050c0c010e241008100f0f1a010302090d0b0c070b09010b 73
    0x21800710303902201c92030b88240140c0042150284415540d0055032100c02c041c0e9190b008018203004005100341c040c1004221450218140741501d0060b2595201c0d80804011010030055810100324441e041106101c1e8150207080f5185407545040c684d5501c2170b1804c900140300f83e03001203242100c0f00c069078140c46040c2d540e80c1c01c20314445c0034001c4c562040e0079800c1e85481003403080480d184590041e100020300c13600281c001c03945140343c1005800020004010158100410440f06950000103518015014030700803900720041a81512041070640010300000d0070402000342c488095001000351280550003009810181032116480350951001042800e0456954440001000b440d0b0354000c03040c1e41804000f41c0d1b54014081c90502c4003414015070b65101d102d00c410b0120b103441280d24045070300d0824804496003510850030501c3d08070b030a41c1850350110301e001c0c081d00c0314174a88041d10390dc8441511641050580100f19800010080300e04295080004125107010b00441c44031000182c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 184391267 1250 184390017 184390027
    0x31314012a0312090c05120105010302010e09040f14070501020d050c070614040819210f11030f0f1e1e0703030b041a031b061c06080a060b0f010e06 65
    0x841c20303030303503441d81000da0030400d003040c03286244025031290002c074620420007100b00c20324020500c282d4101030b10001c0700513490200100050707600910800207241040b1601d802c00c2e034507464982264422400003618401d540301103013048560004101058400c26003c491001110f20811691846450b0010340c080c2c01551040210600803400510324654024070241059105c400182c40c240465181c11701b01007480001c10244081800000300f440120610710b148113036410800340c9850895079180e02006140b0f904070400d884148180d40c40b6180f11b040803961120809a070300b1480c1c00012940400078504140384482c28411411550145071a00f042c1c9907817001c0c100c6031600b903080100141e081c51f499000184095503188104004004810b0211141c0e0000e0402d0616145640a60100c01043c0083c8a0041c0d52080181e44142018008800e400041802203202030078165006d4900f5115110101c1d04220264009113480d1a090f10b842526100701030046a0405025180a8020700c5c2041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 184392517 1250 184391267 184391327
    0x109020c1009020301060806070302070204060e07020d0e040605030d0e041d0a0809060f04030f060501082e060812190504120b04050111160201090e04020604121403131401 75
    0x408902d6000500009001e40d980c043e0a0404800311203800000707900065507001c514140c0b0907000a450403048480d43c070300c0c008001075619440420b450b0140200248460300da030342c654022402034000942501c1003030030f000c6805030801512400d010b101c1c03801c0c4564020540490302092680340312040003030001e41402e8072011401c2d03200c8809981c20890411996050203502801030004600c201200351b00d0022509100040b0740042e00310340700740c1c0c1028468082401000c0f50b043c055241448401885d5030990341e0300d1004003d01e50111505004c1e00e4a014410000c0c1405010f00d0020500c20001d0f0800201040b1030318030035070050710031101c0c03804110404101805031450740244924000241503c018070303d10308c1c40d004601103400c2d0304207840192003156440300c044d41c02001c800100c90310a04180c1d0001d04a03001d180103140c0007140325500c0304140b11003007004501801e00c0d241a65619901a9640a00140d00e4051201000c5081440d1b143d2035118514484003414000303141240c10031404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 184393767 1250 184392517 184392521
    0xd29010f120f1e0f061a0d1e0203070207060c05030a05070503130305070501030e071a030c0f12071d090c090604090f0204080c06070c14010c050607090e0109020c10 72
    0x10101c4000d05aa8030300c007140700c0039039106081400842000d4a2403000031407a460081e11032042c00b1621080c01c2c0007003000340e40d03506007145d000c804000c40031744d072112450740b4690003c14031050351903041d41c0c03094510117031900c1d0f5074000c500407201a130907280055100e6034180d44289503140c00800030350003000110000c80c031450250140e60b2041003901c0c98103120b400710b817001c44801d8005680030f420015003000650381600c1100340ca04003007409080403074503200606002e1030103080882160070b070000000d4084031809049403007504446440c240ca801c2c0001c1e042444090884003c0d02041c0580d690700c1d401c5841d5944108400340007841154103544e840c688014907001444280e40040007440f001c540792400703025400500710300b111b0060300c6a1400d5415880e11102240c5640181020011000841c507014600070581c1e400000980d001180700340101e036400f05040020741113000740c0b8240304480f50301c08800c1044558503041c0c80304c944d8844182c00c00303d00c074960702060346030b12000c0c9000507080d41c0c1e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 184395017 1250 184393767 184393787
    0x10501080a0b180f09120405040b010c120309020306060409020919150b0717130b1c05010306090b01150203270a18050c040e01030602030a110d29010f 66
    0x81007001c40d84100c4003000c5502c85004600000e004112003080040f00280010724943c40501c0100a003100070110401e4071241c4114000c06003da034890b0042d141590081581c110040d030b00505154191000040080c014400c1c82001c0307120740910b50100341d4615107030040002c070540082c803120b06070f107521043d5040c11032200000d040e03207610b41180003200c4070380b81c015100816030203c0079aa0b0344094903140d8086056a498204601702c00e00000f00407121035040c0e0401e841c0b101030020740d146010000b040c0c00c1003143c4242d640b6a400c0c17100210401a00d0382048000f0b5106503010344050343ca500740e109501c1080c00c10080160310a02c20aa198420300d1054282c0e6950b030010708403001021004900d00c01c03241d400c54003903006c4190070f484441070548901075010161842c090f0034182002e180e54210300b0180300140080e41c0100c0414420540c9a00808a400c94101000d0343d907003104041c54003401903080d0138505008020900c64549028056045161070165100791a01500d070405031800204 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 184396267 1250 184395017 184395031
    0x6110a0f0c11060c010903120501030803070c0809040207060b0103050a0b130213080a0614010e04030504060302030a02280f0c050d030e0f060a14091507030b010c020d0f02090c030103030801050108 86
    0x258030001500d4403008000c00845544e00c00100d4140102d04020b8140701c41e83c520000c20501c3c2c01c00420201d801e80056a400024519001c03210119a06003111203010304004254014400101202002a0381c4d0089220810a88042c003c0b5030b10040c5103000c941c0300031542e60b0400c55002d001400c22050703a0080011500050303a081541d5182c95659250021000341210040da40700807c3e0b00c80071028521a00500302004640c486140503035006001d03000c3c9100b0342c0107154012001c1424241710750140d03041404040c082c903030a28411114a5101e041480f85900810701c40c0d0060314003184182c00036080e19800100521907802403000882c014200c80b519140ba17400303804110040504140a461f0040c0d401040200b0071211401402e0740d4044060b265124a034040381c44020000341c002d030340c580e000055040029208242500603201e45030a07a03c0250301c4500a050041004546081403440c2402564080403aa842c42029000c911080c000540071400d1800101b056600c1070340b0b60381e44804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 184397517 1250 184396267 184396283
    0x40c2f0f10050f0c0c0a02010509120f0610080c01230403080f04180209090f071b080408070902040305030304170721030b0306010524040b040e010306110a0f0c 70
    0x119205040e400c25604002070351090b40c58600340542c9100075408250818000e80c50345103000c402042c266036a198098009040c403001103400d81e03040e581c0301d11107111f034600c1a0941c2d1074681084011925000200c0740400d2058406101241d070382c0000504000c181c80603102c2c1341041381084090760036060000310246a4400c00c03c0044001090704010f003a00d28850140e140d10789051009081811481104c117049880c07041c03204850719603031044203030380041010403030706280e841c0d282d0110b42040b403128001032655118104581000b4040c4001d20490f440c00007175408054175804454181d12591001912541c82070010501055024041d5102a008200c00030324203045540d55040ca20200081c442e400800345030305220580c0c05000380310080b80110094080e5605240004402500b0008107113540141c0f003203200803034414030040350301804d50003d0854032a07075185004503200380300b40000ca030344074180008600410312180560b1400601a180c5413590825220b088a01c0c0c0051003040d03070301c1c0d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 184398767 1250 184397517 184397533
    0x9060206010f090515150a020105130b15040906110a02060105121510050406120515010807090f020708120415111806070b0109020406090518150303130602060402040c2f 74
    0x5550014103901e07200c0031b045080d46030f10711280d0180c01c5505c0289a40900560300b440180050f681c0f6411036401303030502c0240340c40552084003040c002c10184000402c01c0e8500001c1c0350303c0d8000400500517803580c582c21504180c0c0c1700d000b8051110345020b07a4403196802000c0059540d000f0080003940030840100030030701a9620b400103815945164003075900c9850400c100400c0c03060501140c1c08089551070242c0709540b40c104501c0d500c1343c552061280b229a5610b21011410071501201c091540141b801074460701c0c1e504030b40a400c41d00f0b981c211800000e5035a6006804114000c1c030b000e003c503001d1070300c0c11310680000d90300100341d03481045640100100300305000158911010390181c03400d9a001a119810441e0281201d00f240e0086c600c540c00c0713510401104e520070003000750700286808807601d03118000c4010a10718010340f404000403135400d030008120745600045881c46540219400e0105a50080058580304801462a281601d41620101032062140800400044084103e400030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 184400017 1250 184398767 184398769
    0x60426070b27160f050102010b030d030b0f09040b0f130b0f1b070507050306062b080c0604050d030507080f1302030f10091203020405061b03090901060e0109060206010f090515 77
    0x30400c9041c3c0c103021008000c40601210840703580c0300300078080a000030490010060700080e5030303400744035124080544030800f50105072184141000e4121000e8030820050610740b40542c82504102c3d101907030005154001003a01180b03001c0c001181c2d40004000720b4a03103425501b519064801851400604c02c2c1102c410465420306008010040c054000781c8001401c2c41c040606000006c0d01d414030881d45c20128084030140c02c1c017442c0f54a409402d1480c1c5264051400c106240140c08421000d40110b85c200014880302141040828059940402096844000c1913804c0c80e03003070307070340103868011000014002c00c603408070011407a000900729030840a9203001585000d4000004d4403500703031942e212808100182003192451101414194205030030100403403464002d0f43c403207640c50054a0011500c1800620444000c41c4000c0d1102e20301e0341e100c03003014045892200641c2c1c0052242c8100141c6a88049a00303030603110881c1c44072160368900401640540030241c15145450b5042c4502119 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 184401267 1250 184400017 184400023
    0x50a090209012f121e0d09050d05030901050a092102010f0f0c0909090b1b090319110904020102060604020a09090c0807140c121605060426070b27 64
    0x10301c01d43c040400300d0080c1e2209415041c41c8280b80140c42480d03040c0044408500c2ea1107280b220700c1103034141c040d21000032542c820f000d840601d00180684c02083d200c2403603140c9c40002503100e0304c40440244110f4803030340500011580080000b401c100d440c0c2601d0b200349803480901c203103041c8003480049000c500c1d4a018800302c0b8588a40500c0e615030300c0b00f000b0380242e08800c540008002e41c2e1001c00124005807107040c0c0ca110014412100841d215030501c1010301d0070030544003130b090060115904007c01001c1007411948040e81540d1075800b03d1b41c180c003d407400031040341c4200e2703040c5c3c00f40c642da850340800d020280d00100c50303e00902c6401900400e161150b445103608005060740e4118181c1045003014007040400d81d0040c0d42e075802008541f14000f400204071110b05141800a87e9031148100001c154040700d20340100b1074040d80d01071005115032001c002254401c0403400c1c512082503078823110744c9481200c000a00c240c0662000a030303060381079411441c21800c02d07210f0004100c421491503007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 184402517 1250 184401267 184401317
    0x804020112050c09100c0f0b040201020307060509070509010503010207030c060b040204090e070302150a020a030503180f0105090c06040305060103060b191e0501030e0616031b0314060a050a09020901 87
    0x542c4080342902c180e01e0024850020392281b81401c1d040d90005494541d40300c80d1464002d4165800c01c8040f80859100b04122001950440307010080c505050406940780c0c0038a1041a00c6500c80d80c1c00840c1910f01842240c0a00341c1c075442d188a103603403961b1102c0280040c1c0c05115031140e030903c000103c080183c0900142d4400036006000f40c00c2c110710402140450000030140c0024090217070200076500002c00e072221a40509081d510790b55500c0c1c2c61505403002d12085072880c014081c07004145141500070328040c0d10380c44c090f01d0f40e0b0041042032140c1c44c0907a100252180d480240104082071540d80a1070030740c040135003568070800c1420794801410006a00420f0a8403404090450241d6600213040142c0303024a0140217401403815681c1c0e986e42c3c0501913043c0d404195804c40c401034000d40c0f0208a034118252840700808280390040d0013420b88082d030700b800401e418005101481c01c0714203a81522070041025000c11300308201c02c03000703401a00007a81444549003a03007e5009445103440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 184403767 1250 184402517 184402531
    0x801270e160e0f0109060f0605220608070e0301110d1a040e0d0e030304240e03010c090513060602030708070804050d0f1103150c0d1e0c091202010c0201080402011205 73
    0xb2050300f05250301c041c40c070b281640300d0380c400d61400b0028002003440c03000400032200b6600e0800e442c0c0c03540780d50a5072540051950040b200c40c1c2d15100040d002c0d00114104d1066402d03440700c001c60b0100c0c50506082e143e001169007021442004021502d20b038960041c507041042443c0ea401402008022808a41200202e1540c0d6440110302c040800e40c41003036020001d806402039402c2628040654411185841c4500803482e03c081d01100468856821400b140e00014002c0c0850100210068024500c2d4003038240503190740004c40307210180502030002107690643c003d524109041d1101ba84035040030200310340d840c03410400081c1c2550b400e0701c0a480c09010b008502031000040c5400440c03000c001803014061b030050003a03140000c0380c100255034023155900b91250384841e00d0035010002c02500d010700c011145800d0000301c1c45aaa44c1c4500300024498846500301790701c941c00e41051100800009002562400d844401035105882c2c0e01e41007481030500050340a810880102518012038100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 184405017 1250 184403767 184403789
    0x190b0403050c0a080705030c041e0507080108151b030c04030b0f011701052707090f0207050c120a12030e0102181e1c05150c030402010801270e16 64
    0x8990640f030b003120a50002c0c0f0080008140d460319000c0800d440c0c860030401c007441941c1d19862143c0c9000b481d00c0124020070b0070f2100300080d00c2c0c4000080d00d82c420a001d540b8051207401e6840006420815025004101164041d9008500761040d0b0070160f0004240c148012006e100005c002210920b2441c040d202441e1040540d60410880f00c410341e000740c41c102c601d607040505200010300d1100740100c9130982c102c3d01180310326007102001c0c9001c0d4603904c945038040c54007541072840c01465014140c0a440303041079540c044010001c00106400328180c42119802004461000403459540c0a10103806418086400c100f07042080c1e00726000024681d122200b490181201031401075080101484407000b0700c4061005480414030004204040c1e00c400b010116424080c00000c201c00c507070f8000d01c5940100d86103881910f245c00e58005603000c07401b2584041c000f207041009142d2200d10040d0541001003452204003189010b000035020508640c02030480355140c002c01c3c03c040c600505020015 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 184406267 1250 184405017 184405033
    0x7020f100b180717061f02061b0403150b0415030f03030e120a0507050115122907051803100c0206060f01020c0909070e0112030201050603010b0a05190b040305 70
    0x502c0b030b2000c0664a5070098040030010404915001201d0b4000300d522000350704e6180d80c4600c040b0f00400300740130854100302c0002a0300c2e040c003540040d65603c20403c02c0b090304150300c4002c0d4180d081c0c0c042d9020080403a0762000040048044541c006000844e000788041003948100302c44c04a21486500b0a48009048014580504da014020a03000c3c16401008046000030f0170320301801070017116010000c008002902000340032007500700100300c20700644c84800461b03541c900101403204e00c2000300e400c400403104144800e0f0440c1005017481603242c80341c03410341d6600c040480f0581c0c040400d4001041841c003821407542c404000301c10211501840c0040c06480301d40c4040d1500b080204090301c900001e230340501d001e90340800d40300c0220105036000c0106481d2070800504203100da0700580c03666003001000007030040d0f00c0c1b42d40c0d8203001c2c000d0300200150f0705c5440505080ea1030108030305411019070042008039082c6441211000420584440001c640704c90418a0640c82588192120381c00614 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 184407517 1250 184406267 184406269
    0x501091e0506040609060f0f0e060705010e100204031202010c05030703090609140615040b03070303030c021e0309040c0206060901030b090c0306100905010501020f0d051303021315051903080307020f100b 89
    0x40301300310202d01804d00d1523225a4004009009014643e41c0d64042c0b40003103462400c0010035000748180c2c011680594024a42240c900740080d0001d100c01d5503d2500c0b0b0a201c10482d0041c03090010034851640c45034910358400720103802814003c0c1045900da580d85503108041000220071649050b06c090141c0040c1c1000060900c42d0b00424046134070451410360700e170030f280d500007440e2811240d15007008180c4038a80c18007a81454000c0b07174001c101c10141030000b900c1490100042076049401c690802c100045040202d9861b0380032598150030140490041c404a09200748060f4088425000c8980418414010906204050f80e20b42c000da28441c030705000920301800341070301415013071000384800000010000c1e503460800d620300d420f104002485540c0801c81481c490040d503000b800a80020190724003080c000d103101000b095141d1400c900216292804407a88120306681c0e030b0320300c000c250440d02c8801865101502e0707242940324020700342c4010745041c00b0640880b10482400070701690508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 184408767 1250 184407517 184407527
    0x903020909030f0d11070c0305030307021c210e070605040311060702090f130f0b07030f0204060f0806030c090c13060c08040e070e151b01060501091e050604060906 72
    0x70704481d20a070801d01000c2c844400310000da840409001c0c0740800c0c005800d120150007403081200252596800311008800d00c400000218043d0419a085610b81400600c004802ca204400540001814400782c070b410b140c290341a6085601d01e6040000b060b03818003031120700e00009035101ca004a00042420000d100d0149903103440040150b0320580741141c1c681c00560a0301e03008006100e401e0851010600312881c170540f00f92555403100001403880094240010010021104040040c0c2070442c40b5907045058021b44007281c110740c0320340700102d603544000d84003000b006014541510516800c40081d0341c509a03d640190031200d400340e920348504c00808084a2a60081030a21840d003020074001030003803084908660f41c10074441a00d0321000c0d0101d928640744d00030694001e5250020b440c00100c50402059205580c0b0910390340e4032040e014580c01c0c1c51091241c00c0c00701c0d5a02d00100801180301d00c070000000801121040b44980741c800080c8160416000b90700080e0960724140180381d004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 184410017 1250 184408767 184408771
    0x604060b161103060c0306130f090812090726010b0d0309050a0602030310030212010e0d0306060314040c0e13050f0a0c050414011413090b0708060a080d0e06040504090309030209 78
    0x150060213062500d920500344504c80548218025428074000d02c801e5501a400345121a1841101b800102c069083c410300c03580190326480700754511080410310110000440100300c4900c9400364903800d03440d1650b00c0350701e0b44c1c22907507240a54a80103804002e91b11061003410036803103529400c4009081c0014050381d074040d50404400e6500030024491740c04000300040d801c0320350456889100b0166598003d0142841a045650703d00c82d29008200903074040e04208180d03182e41e542007103600064120006642020b5401a1281000a03020311a500500c141c0703da004200b42c4260080e10709030b5503a58a06640400580d81c0ba030050f41d40101002816000b440080004031014030840c1b1110040c2d1141c110103214000740040303a404950f40c161160705200d4650240344104014091035400d042420341000c46079100001c042c000065020f03c1c2211208040e0b840e16001845e040c541076400b5903070b80c80d6520071986c1c401e5050000190540c5c3d54011100200e21036038501c1c11240c40e51050242038040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 184411267 1250 184410017 184410019
    0x81906060b0a050301150c20040e010209010c0f05070305070905011404050405030d090318180605040e06070e0d060e011a0402040b0708090f090c040e060f0a0e0604060b1611 76
    0x4000102ea182d40c080c065134151400c401580f01822079640c4185c0f815a5450310081c80c840c1e20a00070442c142d040d0442541e104000e0314148480700b07910120900700d10a10400601103140d075440c4102096008004642c654800d10445a4280d01c90320b40c03c3c0b0b00f001550201c4580c54a0b40010321441e11000d8101211040c141c0d000e0100c1e080c140d0fa090788074018078540e0020b140e503944400051611a804010b0610700c2023104c00402c0303071941e030065501b03842e005d000c400c42410003034000f4003401d00748600c03120b02c1e10010180c101902c0700e4000302c1c3c1184141088a5020254800704400720f2003070f1050004841b111000000c8000c40382d04007501125108140510451061004004070784030041101e8246502010b000d40d00d44d02e40e00000c40b4800382e1566690009090400c0004020075a00103209440250191101598982c01042149803132500c03441d400140000d010481249603008003034000c80000c00221b4a5511807110b0031854110002d1034011210b01c07285e04040c00365501c030050440c60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 184412517 1250 184411267 184411289
    0x110d0b040f053711040204181a0a05060d0905060709031e050d030c020102040308040e340c030c0609051606050f0f03071205010305060f0112020f150408190606 70
    0x184000c00180440e02c1040301140c1c000001d8010400000c2c213078030356002c80b000340308549460712070350a48110518500d00e44040c51038004260034400c81c550b0001d0022600a280004240c100340504c43c1c01c0d00000d501180741c680351044000011010301220340305606035500c8002e064a142841008601140488401e480500d05c030740c0c0102e00080b40055056400e400c0124002000040480c020b10031640b000e03003541004200410782007401c500c218052100c040c0c070703120344401d03c181814100035440c01040d00b00d0030748544070183d98022f00a80501c280a8101501c2185440e2a03001c00e03603156030341c03c55050f08251815a40c08502050700c1e0058507481ca0110704181035841b00c3c0b80c180c0300d0254030009220307021000501c0317203109503a00c0c001c20003591030501003965645842962084e05a80345100310600c0d4002007583c6034900f62505800307400805495400701000e0034000a10400c07083e000194404004c040364258003000300741d000d454061040c215054050030103504039003240c0c1180c11804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 184413767 1250 184412517 184412563
    0x20a080a030f1a0d08090307030218010f050316090f11130e070c0809040914031b0105060111150a0b0a0f090e03070308070503060102011b030203100918110d0b040f05 73
    0x600c910002c03141e450b0740301d01d0307050f96a46e41600003841c203030065000030760042d4917200340032840d100106010b0481c3e8400050041c160b131a4401c250316401180e00f00442e0003190041001942c0c0d85801c0301001c510410400907074402001002e203016403008400240e0800e200a0800c131001480e030400741e0180c0c0c02d103000d0700c1503803041d541d0341454402c48028510450300c83e140c601c00d011150744c1010482c06100100d0765100040307451005031103440300c503502a9500e4100025010350155010f0a10305030100c0c060841c901010076200b0005c000540001d404135607480c0e0200d806d41f030380d12612000d003c0a014841d15546815a40c005403800d01c10030b03003a150424444900042c0e001341b0043d4015043e810002d440f680d035034004074010050b4102880012902800c1000c805070103134025405402401d2602c600c06480d048008140e44002d120420100a807204403c041008402070000d80c85000b80000d9054400e900c501e8010041030350140c80800071041800c0c10007030108181030042c800d0606009609e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 184415017 1250 184413767 184413769
    0x9010902070b241908060708090d14031f091a03070918020d032114060102010510050d020d06320c0910030b090709051503090703080a020a080a030f1a 66
    0x401e8088034080d016442000e00803406942080302440500301507400c1b140d084ca0306500040c140401680c07400c15a00401300d0040200348110b1032040d948840b44000d42c1b45458a0300906d0015242440309030744a03005600108400846000301854032044481081210700c2280406080170300d81d501c071420451a00002c0303111010042a08010560100c2c2e00e101d03c00a0b0f0308094440c5800b02c1e4040886507441d9001410a5403640d015071004480c00c0e05000b46603507a0b400584c2200c8060384c14403041d4049101c100160316007049400c0030035101401c1c0c5051139102e9510f040076648002d201e8484a02d40241030005407070004684622a170030b40150b07400d103007400c1d019950907104210b90903004400d00c0350210303415402600055103045001d07040100c58500300c02c1c024015070039802854420840603000e906041003800540e800b51250710080d2030841c1c42c6554500280c0d21083c0c841007507028501482c00803a4050000d060030010316240480e4241e000c41e01a01100c09401c406100303409000b24152007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 184416267 1250 184415017 184415071
    0x20a021e07050d0206041d0a0c080601080103110f040203010306020c06090a0305090415080a0b0603240c091801060809190b06040b060c010e1606080609160e09010902070b 75
    0x85880036243c9041034000ba0010801c207115079003100d10f8414074491001d2940d60500415807084008010800800d80175040c200c40007142038131500e0009900400500102c5c0d070060144039551801060800c0b107120306d40204003aa00300344c2c416581d19601090a601c6803d0509c8426400001000a003600d4226036901400d1400303104074403801642d484080399125590200544090241c500448102050f01e00e04000d002c40c084449038000d00034640b104940c00c034007560901c901480c000c2d40703031426581c2c240907200640103102e216a0144c0f00d200c40003060b410b0700c2c481a001c1c10059030b5201e000d2411002c0941707404000700040700d00709107540040003c104400215504003108480214000314500005001ca001d5400e0301281946130181e6040c1002c0000368901085521360703444481681da40c80162000103048810315000103141000039030701d5401542480c196802400c069401c4e0310000003150310b500090700303d000d0055000a40200384400c0042181c0c7c031242080224124102e00c90301208 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 184417517 1250 184416267 184416269
    0xf060e2103011e180506151c060f050307030303050604090c12030212030f180a02060a030f0e210703030e011401241209050a020405040303020702090c030105060a050c011d01020a021e07 81
    0x1c201c0c0d81c80000c1380040d51030142c80c00d01480251180e54030303031550b230780083c0d03002c840402c140180074a000c0c00019010b422108544c1144e0b0700401922410340303141c070b003600031302801031416a0003030f5180c02c000d000030f4240e65170300d000d03005c50502c000c01c5000a05d07019140000307031006c42e01040018400c120100080c46222548030507510500254444513007021841c00690040080d0b00583c0418148415036150303004c501220300039181441140454800c0507203442c0c0500d0300600300c0a00c2c003545542812440000c0500d01c2c42450001807141851031483d0840b00404842443e82c83d0035401007010001841003150743e1950f40405004d0030b02140409400c46041c0180122820f44544402040c004184081020280c01400034403141c038081c600203009501c524000c81c424100c92000c1002040e040f01a603040c0c8901400700c510b8000c8801043d2415000100942e80030741d210041c40c9000e5160b80c10342d000c402e050f100056114040f101010303042a4041c0c001402401c0180508103440d840020010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 184418767 1250 184417517 184417559
    0x7020604060e130e0d031503080304080306060d06060806040b010809150a061a03090d02030f0904020f090616110103090b040f030201140709090b0604030f060e2103011e 74
    0x1c0c01190a40402c40d00112003e45103089441c018034088512030110310100c0c00759590341d082081c0c0d81e292007004141011400050201141440002c8c0040c01003001180c0004c8020803d50505100c0500c801c00c0c1c030b405400800000300000140085800c26000f031410040090920310503074540301590350f5880c444440050400f5581502007010b0020711344c841c2000c1e00e0b111864019504201c0d00fa030071035610a940c001804d00c40c1076120703041030b07101109503035900e001800c42c28a000103103410480039401500c04c00c0b542c410100a522140e0340c4940041c10240c101000e81d0b03a95240905145e8204070f401d20030303141818109843d0400055102c400260302a40c8100e00b61a10350407070604074010024608015000031054040c8900560020313104812a00d0424003400742600140c00d000450007184801800b50100140c51000030f040c5da00907403200b101080845546080e400c5016500c40c80d0050f1102c45c008000006010300040c1d90602c1542008000307241201c203160080308900011402007413 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 184420017 1250 184418767 184418777
    0x403110103090303020f0403050606090601030903050d0203090c041a09150d030309110904051c180b0c010e070b04080f0105060d02010f03090219150f090b070f0b04050f0f030702060406 81
    0x31000c0500035170540d45850411554503440c1c50312440c000b940c030389003512814425951000010b500790b100f0700803010703059416a42d00c2d0800d264481108042d400140603114035010b404e4001c00552960710414014003c0003c04031003c3d0720346024041c40940103452080c004000c581d50032602d840707240c0602213041e0300d4a4006a00c00c02418103201d50700c41005010341c005490780501062080008814100303141d654814645001c0c034100941c0d03402010007400d0700d9402001d004105060401c0044c102ca00201d00c00401c9294004c00942e0410300d064015090301c403408581401081c90070007244083c2ca1120340200201e0030000001114aa00050000d0400c0110005130307860030321039004215050f41c0900b5031201c08420b0655400008550b0140c0c04c3c0710311480d41100d15040c841c06140c062001c3d0f589030404282e00380b4070880a194440441603030140000309947d400079403200c0149100b240140050301700010043c4045040084181000e50164000c0c402c18016a40b41c90860301110750328108 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 184421267 1250 184420017 184420031
    0x10021c15050a051009080f0d02060705040503060105090903071523061c080f07030c030e03010b10080c120c0403030809070612020a12020c0703120c03141e19090b0403110103 76
    0x4c22a02d85c1c8040d0800801c50040350302d0754400c0c440008924908801036003c2d211941c3c1c0b0068101c805020794428154590b001c5c0c4c00400c040e0601c8805603400061040581c1d18160441c0c0f94204215100400c840505a0314000349903a01d601620218440208210703040302810000f000881e12070040c5114480c40061848050803c14140219000038000c0c0085a0b02c2d003803d0300700580005512803054001c528094059130481c0b0381031040e0841404003c207064400102c0038030888880d28000c100052154042008800091280702110310910303245000030382d51810742c9002070000703201501c4200d01c0d510105007880321580001c0102d0002c030034040016114500c04800b260020b10002c203c43e0091302c0007803590300080020038680c09582c01541c0005050000b52000c071817102a456003c0d000400f1281e0321410707044004000c04209046070b403186103003542d0300c1da00c50180d03200c1c4500c2c0205140d00b078014064107801c851240c0082000104203400e040c80c5440f100440442d52841c0c2e4100350340c0b044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 184422517 1250 184421267 184421299
    0x140d0605090f010501080a11070308040c050315041208060a140f040c0e030d11030d051005091008071a0703050901021002031512030c0703021210021c15050a05 70
    0x804800282030007003a004031800c0000c0704860b090310a00805000840c25400224446650f0207412880e00010003054075045079034a04482d45100a07000725128803c40100156644d03040208900c41810f4511980003402c05250100a4a07100941401400810020044140c3e03031311800348110790002c90800c4550428600040415030f00c000d056510918000100400641c0050b05d1000e218094003281c054221120301914401042c000c01e0740564000c01c24603007081020f0704510b804c0300044441c80d0f8103a442c1d1001610050003180c40919041c06c15a0400c1954070801501e001010808100e40711088110700c40c641c580310f842d00c00303018000300190401d4164400c000240d180c581030b000842d12403d0100204101075030b03d0320b4640c8200e07511000b41511600100441303002555030001070806030b240d03a092240e260701003501c0a620b03000b0310800700040440c0740010b03c00f80d809032144180eaa0101c0d00c880b01115801d100c00c1c80b682034490828403458496078411000c3c2d80b02101c1500480d010300ca = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 184423767 1250 184422517 184422521
    0x606100c120c0615030b060d0503040b0403050607080a1802060f0c07092003010e04060509030d090c061409093c060907140403020103020a051b06060f0d03140d 70
    0x141009200081e80c800395501207a2000411804602c905418003611100e00c2c10745400303000c0c5020140403440d0310310110301c6514280d48481c140c18031450603681083e0b41c82d84485080d0b0020b510a07229900482c00f0440c6c41580140220b52110034404104441c10105424290001506000a00500000031480c20780e03207160307007a1080723803010008607482944c80e0300f0300c100903042c8400d200310018140c025410001c0100015a0305a8850900044180d0f07600d031200c0001d804040c01c5007440303000422010065414034004c1047c42402044071403d001d140880040103100314640c07006402800340144106651150085500800c95000c140351004003240340c000307a940c0085000c05000d0801001c4a1600c3c09226014810007048418402640c1d4039403080c3c40d41d4042600010f06000104410f100641c001d5000e49208800c0d40b80083c2001c10f0011003840300c0014600100c030591001d001c020240c540300c1240d207804003042d43e110340e40e00c0c80e603078029000300303481e0428075100c15001c101d16020310b1060b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 184425017 1250 184423767 184423787
    0x1707050f0f100f030501080d080a1a15040807090204050907080601090506040305151005010504170705180402030706020c1c08070203070e0106020f0304051c1703100806100305060610 80
    0x8007500b5a440005a01030700c082c0d0a40c0b0400301182c101400001e0404001c10351404d0100181c4880032541c1d07854200c54010329025100303008040850380748200f95141c2c2c282c03080003400395a800c0e956a5040684036031030000e595000c240103c3c0104024061500c0f004a0300e41c000005041c244850380b60707440141c1b0400d401e604001d8101e100414000280000004e0ad1980900108884502e54035031f10392200c0822058046c05011510403c001c002c084005c00c172059440c01040706a620b03181c1c4400c0002c0689000820744a4158421002c0c0700947c0740910108009103c240010440303000043c01290b403d2b070450016030803c1000d101900c081c4500003048580840d4005e05071419a03403500c520b145400b001780200c2005104079aa0100407007800030848054550003401ea090740030b01461151740345058420100c60042600008180310034003074000e14001c0951040894109040c040c0c000c2c54140010500b29020b0400e260400c003181003c070310f441e0082070a68076882400140300c0b0545001c07000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 184426267 1250 184425017 184425019
    0x302011d060a05090a0905070906081807090f14070e060705070305030304050102070c1d01030b0601030e010603050105090d03061401050325080411011106070806040905010e0304030303061707050f0f 87
    0xa92030141c2648480100100941202d00760f081c0c03504c6c0c071404411100202c661101007515443c00f4040760f40102c01d010307400886000222000210350280170309200f016403060700b0164481500e401c041e08640104200d2061a001c01006441c105600610582c842c0d42e0345406400300190074418003105104030030186030401c08882da281003600c1e00303078002d5001444c2626076021810000c1201345444907242694900250024180c0e42141c403100000d51002e81464103041d518401250702048c280213110046001d0f0b40002080e2404015803070800c55036a20b44010949065014030035080c410100d542004020710b820350f00ea5944038018002401d9a40c5414120b01d072465509120503808550300d0310403072086025149c120305250042d01d0358580c04050701110340001002643c900e1040e10306507400a4010000301d0704506544603182103541410301303401241c100140c28000d03d90103005000c000d0041360729403c0483c540f280701c2a11030310305024880c80b030b030404c0382043e24960b644440340c014108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 184427517 1250 184426267 184426279
    0x3020405030a0c051c03121a100906030609060b07120507020d05071a0304030e0d05031303080d0b011103030109050a0f0c0c020f030c010c0209101a0403031106100302011d 75
    0x36007420011085403851007014070880c030150b410910304090544105609031b06407038a04402e05034880b070002404100b03c1c0001da0a0000140f00c007a6a0340b81c500400540c034949811100c42e0900400070141e41d81600802c00d400c1c00e0101c10000800058125403940750001c20520071031101030700450782407045250207940036001480000500c10701042c1175080f03d0031460140360105d076550403401140800c81d400341c00f152740220a40c074242041100020300d90700c0b610035685000000f8142400440850700196201c0e0700110390590381c1b411511030b0351403010090821003218040000d0761a624401401642030164407040428003807941c940141c0d2500d0041e00c4c0600601d4803d00008140741200d040076441446802c0d00c0728460f0030003103114105000181d642a00140445e024000d18020241401c0f9101114040000e45c2000018000b07075144450741c95142e440c0d02e1424003c180f21441d0750640407581115051214101c80e003000c1e182101d90a085c1076031003194000050701c1850000d0861a0004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 184428767 1250 184427517 184427533
    0x40c0e0603100e24010e0a03080a090b030c0a030e1203180c10030b09060f10030209060705060a091208010b030a050a021332030601060e060d060b0702041a010903060c0302040503 78
    0x4400c0c0340c00320700d250306242c140c40d0070b00c1300c403400450310180c80c40100c58100480031824004207016030003c060a041d01d040680134155658200403071079100700e44082c48450045201c4a0b03980e03050082040440c0c840c801410501884003099640748000b0f00100c0c03024004140d05200c0c001c06004081e15040e00400c04c1c0c50310408042e001d00078009038224107100d500110002042c44c1f03000a002e01d80c1020281c1000403244003220143d000750b000008596103c4000c3c41864005001000003500c6081d048501040c01102c0f032600d160302d00146103080c02800341c0388005008040b00c1300f090f69030054001c0c00203d40c1d5207030036850344000e00c2817485045010b15070b0040400e04610a101030041c0d650740340150392800b0050a5071036070001d1304008242c1e064110b03200400407035106814206080d10b0092030145070001d19500c0604031f130b001da8461080fa10010881c01d041d031405104d400800303412810a9002034000c0b00c00205200440d002c005c08041d501c1c2d035003045082c07281c1d040d03030080d10001d000c88d208a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 184430017 1250 184428767 184428781
    0x3200a0518070c0f0b070e030609070302010809010f1d0c06070308060405060d020409060b121b2709060a0c0509010c1212110c070f0501050409020c12070305090906040c0e0603100e 79
    0xe140100c1b1940082000e039481c0c0c24042c10002280d40c880c40494000c0c081840c150f500445084102a0140389659290310b0240c801080c980f04800381008a141d01000101030702521a06060440b07044038800d60b000d022040100741c010114a41c03195044030f002580d5626440000e10700510440060f402c035141450783d0301000050350000310403000881c0c0750640204003804069885484961a031140c54500c0c46180203820000d503484170000f0441c02000c164502d001c0d1010040c0300495400c0d4142c1d03c0741e000d00258903140c3c03090070700d00110362a00900d80b5210800180403010000401030148044031400410507100300443c019150544e4001d0080045407888281709800c540031407001030043d110000b0701c404200300c90300b007161410b031621814146085034007002508280848081070043d60305180709a04918000c2900c640f198031482d0b01d50780000144041c000c801441d00303018520f021170205400f40c1003c402852810300b210599503d6458215118082c85140e01610040e10345000303101c42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 184431267 1250 184430017 184430033
    0x140d170c010e060c04260a0f06050606090d0b040303140109060f0906030c0b0705010207081306080603071a0906041a09030d140711030c0a03200a0518070c0f 69
    0x80030351060080c0400052800800c0e11108144c031545000d00c0d080204004c9518100b44410240420f0b0006101c081c104170502400d0101e880030884810130306001c80802c00a5601c42c0d40d81084c001ea840303e040c141c031700700822012a1a268094841c0c501d81d00010101031080d00044840300c0d200358284c0e80755a4501c0010702804060043c0454541b03940c0c40840c20f03000521070642121703003260350b48041c0380c40c1c1010540c04c0d61103004103480c9950200202004112950300034180044001e91040c51286000c01c002c00003500900901d04c6034000c81820402810f03003003280c48402c5074541d442030f03480f00403030b00080783d51080303034400002d0901031440200b2131005580940310b030071415000e9803908500c1000440c0e5007107e8441c0100721420131f001003008124804904e0540c004007600325901c0301c0c80b004c0041c00300c4269038021103694001c2c0c2d0200d1a206402d5080e0000800140c408005890074000001d644506600a04400e0000440040c52071849a40500c000d688c003e80401d0fa034107103038206118 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 184432517 1250 184431267 184431277
    0x409050c12030f0a0c030203040e0c04170109030801060e01050c0f01050906130b130303090b090c0406060e090c0d060302090112050607080c07140f16030b010b13140d17 74
    0x44150460030310034081d05404011612140750381e00085240201c0b410301501c0301170424406804621043c4000728010b000c82e01064043d03104500700540700e1340f410220a90345014840b0352a83d50f414845541c00080d001041d903070548a01c2d003810340001da2180012584c0d4004c18441410510804841c44844a01940064010030700001654020317a54000e0402c070349207080384028025124040010091810071079088007084c820305d404140d03000340b074955856103001034800080c6900000d00454607807509120ba0001001241048480660241e0002d07420302801415840500e1002410456048244e1b01400207164028844001940c480300088440710b5040b408075168450407011940c0c041c000e0304044c2c0f0a0007500f43c0e85103040c03100d60b0b49414a0082c014104c90038070510104561481301408030300111034480c1e910a400c5841c50406448400b412b9102c003680b8281003020b505110340c2c1c6444c00098400407884554003030300040104040084440001c1d01078140c4c071040740307440045480105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 184433767 1250 184432517 184432519
    0x19030b0a06050d0b01290703080907061103040905060d05010e06010f12020607060209010903290c1222020406090b041b020c0d0309050d0303051801050606040e0c090409050c 76
    0x200303694998080c40710345078034203e0182111007084010800c00140245e03d080120018101c030740d04580100100c0d503150032041d01280400c01da0410403260071707030401003d0010f26903894000e030701150399460240c4a1080b4040d00c3c000c552260002880c86d110040e000c1011944034000300304502c8000b21803601c424081c0a49100300740d00301000078414000060003101d041c0c00801181c03400307495540d840d000750f100c50880c605000c03820740000003040110304010003120f1152050f50154080380d00c020885100180580a081018404036100303c006104079070340000c0744400d0540040405400403084034800714000c0d4818200680460103d1458000b4944500d05035018003e071401d1880c000e40d11640c40d142c03100140d00020440c2d00c1444d181c0c010010355030080c00d10540c029180e00100b28440411181078000c0b0b616541484072010ba50000010001c18800082181c1d040050010b10188210301c500d20600c8104d07000304910420321022540845401001004a12294503141e510b40c02900c6000b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 184435017 1250 184433767 184433771
    0x2c0103060b011d09010603050a090f080405030f0f1209131506090501020a030f05030a02070804030b060901050907082403030a092108092e080f06150d0b19030b0a 71
    0x200c00b40300185035403083d0000083c03c103000faa003440401c41c01000010102c0401c40e803a6400315000ca400d507400c0481d01da02a0060756aa1800c20003414074040030480c03064021381c445403515904a0000c1821450760001580d0166107100c484002091030201c3c03c8046d61080c076025440c240f268000304e0300021220a030701c409044a5075540160385580701544040c000c983c00e1400d031240c1d9803180004607070060700c82d030005003005042d8a07141c5241d04640c008441c80f244003824040240f500c17124903401840300300d070003040520300424000e0501c1c00290180f2000001c52140e511800d0340405107421401d000340c120398591f1003009004110346802d203d440450441c007043c0d280151601068500d502d0f4100c07800c0c1e07142c140b4410a21402004039540e00d024a40340d51010810071142246540204441d55141c003000d0038a0640144142c001414440c0705d641d00a034050f0400501500344c581d0003400d400b0009540d040030010900e5001e07154040c218001c0b8004020041219000039940194815101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 184436267 1250 184435017 184435037
    0x1813060f0b03091c030f060b030402090108060c070303050406060e190606031104330c050601090b010816020106151701050406260a0206040b0702010201050a05102c0103060b01 77
    0x8070080c14441a5040320994228680c40c44840440c0751000c80641800c0c0380008030100d80030201006c80e001a040025848070002c148820751610b10103407405002e11602500907420030306216a214803c1002c01814103894000040070700002d580810001d1152b03140c079803610314005c00d24541c4400e07020310070700354a450407e001c65050311901ca5401483c422503003c51074181401c4000c030710540d11051950108a4006c1c2500c0e00c1d0300841845800b0081d0350f103454031603182601c1c1c0745080100580100c4901d030300d000380c15034540c3c0e03010a0403900480034000b41a222000701c50101c2c05001250400744d4030090794407200c0348040d404070112054501004c1060f00c66603c039001c000c181c602038843c0d840007029019001928108224950074007002803812a01001119804503009800940c02111901004a281e030255602070040c26400358100404102c0c0780b40000a2245a034600c6c010007410110000c00450841501d08144500d11444c0f8900b80f020b603520300d81080500000c0c1070603400500043c00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 184437517 1250 184436267 184436279
    0x230105091005030111190305060a0b0c1213050a0b0c15090312040b06010f030b132403030203120609060904060e0c0d150c0801061d011209260c03030406021813060f 72
    0x840c00b030007500010000f01c1400d140c90344414143c0c0000500d0b220f140070709061000dc2c414110020143d0307181122401786101d2615040240d0b494682d03105645420302000032641048c1c0c08501420131001e6254000c2c038039190305400603e58028000c2d4200440040401d00c8103024441c0f425a00ca070f1001d9031381d1085a4204c0c0d0048060310008141c40e038000740402da541c03d00c1d00494000c1c400c407440b085a03038408081c1c101040382e5080d0b55a4000d40c0540c2000401e00b1050422450050341302d02c0540b610b4049080280114249410050002d40301e50b07621341003d110032005200340c00000e0300040c0b0541c0d000300142040169002e503520784202d020316044c4120f000602403603001e170403541d003515243c01640c101600098120a248c00d6181004144901d100e60f103040f42c42043c08990003494009950342711910322203000c6d8103400c26440155014851450180000030032a680107034801000360f100c14441021036090385a068469a01c851925080c1c00450019405501241e0124003040d0302184c0c1d4003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 184438767 1250 184437517 184437521
    0xc05121e1f02030403030e06010e0a05221103030f04030303050105181b030402010201061503020c0f0f07030303021608190305061905010f0903060c0908012301050910050301111903 79
    0x6821480c03944a6854485070144042e809168058040e040214000e1411409203043c040b090304040e003074003e80c409000000b00c0b1440341b80c0d4855500610111904510038200328505186000203041c42c00901c01c02203161418010366030442c07a0045600e8903075890745401307170191109001c4c140c0070709144e40c5105194281a01402d015000800d1180180200c2d00b28502c1594401001607040d5901c9410000700810750b10a03d5040e1442230307500584500c0b454070350301d040006142844103e0b6000c0407003000d24030f02c04130341002102e5041c1001640c908500080c5010890601c1003d4001e40012030792840e1503a0000850f20f20021a641c10007103617990404000f4041400c070200150a01001c0c024860b6501174800310b47c3c0050282042c4006681e00c0c0c1c0c44c3c0341034884444598001030038070201001034020902840c94000d10310711030540b41508001c048070004105200b03030340c41501964049071200510fa2054405411301a000740540612024030005540c00718054102c00d00b0b5036181c54402612038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 184440017 1250 184438767 184438783
    0x140105101e08030301032003010603030206011e050916020706140f03180f07061808061b07210909090b07080a020d05090601060e09010803040905040c05121e 69
    0x100c002056460030110400c000c046041d4504015825241d070101c1c4000e400c20155000b1031156000d000b11000c458409001c034400c0e0030510b402a81420f606000194020a1139415140b0030f00e410f601e40d0b9501c0500309201c0c0c095622158005000b4400c1c0006400940c40c0310b01805103a80032582c00680c1c6900440d0720301031301000511826414007540d10a821910025a044103a40380d0490180a1a1090742c1c04e091441c891010140d012100400c000b54010f894060840220781d6003d20180c5040d5007607403504001401c042071141d41445600000c0303072000999800359000721020004c07002c2c164450061107001c1015201140604400040d02c25290003091101d55005e60700360f0242c1c54041040c0e0300c034031019000d03a020540901158506444521480d4403d041c050001c2100394540307400503000d2044007100c01d000b080800c0040c424004c0000c2190115420420700007881d0381c8a0920305032001c8180c00c85680104000a1440030241c00078900c0850850f81d5035450b00d05a40385c07045641c660b50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 184441267 1250 184440017 184440031
    0x21140301030618060c0806030d020c010c08070c03241a0d02010e04020f070b01050f09060d0f0c0b040605030a0f02180d02130501030c08010e0a021e01110f0a140105 72
    0x1040005100160450b00103c200c5a18024203040c10700309031391484241c5100035866030005038100100000ca1504202031440e500280c0080d02000200b41c0c0004c3c00382d155041e01404901300001c0c08010000c044541800440d044202000700e009600c9420b140c030001c1c00440802c0a00b00705031442c0c1620241d0089503102e00c001c04040c405843c0d9801511201d8087e032a1941c0310341e00340b00c010320100b0b00f0801000d5441c81403e09100c15030500c410411085140d4181034002c2d0300702010440700741c8444034044401a0442992620583c1c0d82ca403007413107201103402150f078503500401e00140e0141c211000e10702030b041c40384d41408110300c0355059004034000c0b00124400b00c010100b00c068a818040c200c090081d00243c200328071402607606600030b44101ba40111a0700c42c811100300300960f002e12646940c4c5602c0c00141076401000c0d000518072890380c6c90f001465919070303442c10b20246c1c003844444401d01c40160985aa04842154064482040900541702912a070881645051044c0314551240c2c0c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 184442517 1250 184441267 184441307
    0x1050105060702010c0501140717010b03011a07051c09091406031f06050402180114070c09051909050f25141206010e07030605031506040e1921 63
    0x403060f0011104050084400d03940c1d035586040700d80d400a41450124440c0d09540c82e41d030301c0c0f004500002680c0300c105034806400ca0030300f400107000c0c2502c01650303402c100700807000a94581c0258180300b030411400c032010700208042100240780e8280c00c040b01c502200e602c01d02c01c0002880c1620120348840c004c0b50459855003140706940400c10102d912184e2517031900000003a0142c45d1401f140880c2d10106a100841c0e07103800791503040f984d009000708545102040310b41d050022640d80c120040d80b060080c40101919000021040080310f125000c400c522482d00340664822400e0407074446459000e4002d0078080c10b03186101941c60000e144005102c20300d0550070841c68107407541c240421400380f590f807200700d000d00c0d000c201f4010070415018106024031524281000c42001c2c0c12124154440f901070b4102d00c541c0d000e03d9407000e60f96980b101e400d94021404002c1034415a00708142d0072030841000c0480f480450601880481e0305040d21a900c080b44d40c6200c48040c01e462540388202800d0a40c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 184443767 1250 184442517 184442527
    0x100302070b070f02070305060f04140304031a040215190906020d02060a0504050a12020d09060309030f08070e030708030d051e070c0c0e0a020c070911040501081302062a0105010506 79
    0x2512403d64030070b90076102e00c141e804090300c9907101800c100c01034a401794040c0e0168148400e000381150642403501e02d00c1d00841c03800d89140e552800747d0113040e01400e0051900c0000800355200d400d1848042030643c02c81503074801040503200300b40c0000c0d4546000141c804180421164000a01c0d4010f03d4290f400512085e0343c0c03243d07900c026080040044034180209040340340050203c00b0b0001c6902056005400f40b018581c000030000d0000d50300c44410541840e0000001c00d40203210749038620214901100181c0d5184001d803038210740d4241154041c03040903000a030015011004d05413191003000207004c1902c4846540c5506542c64034002e0859100c1c0c0003184041d8095051001500d01c00c0300302d40415651848000d01c0305508503500701d0a03540002e0520000c0200b0f01c14503001e01341c46142009027201050042d0100c6c000e5001d0030b41485403d030089588650199002c90000c0ea00401032640d44060b29684140540b401030341da414500a00320340102020180a050706031007000d88032500346 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 184445017 1250 184443767 184443781
    0x18080a0908070b1215121506010504030c06080601021f060305060a02090a0b071b03030c0201081605030c0f1605010b1f020a02040506041503210806060405010e0102030c0615100302070b 81
    0x4400041d1030340f180010b04081d00b117499203030503801e4079078101c034035010b460400c041504902244000400c4076040101c00c010510015049410620079203046162101c900d50f42d00700144d19101d040020111000072184154050078807139088001524407c03070079a0002e40b01c1ca100070080c1c0c065582810b500002c440c0c401c1c4030282c2d002016200c1c043c0903034070424180d403150281c020001c032180c00540004480f10362160039035030044038454000a0320044502000300300b0500424501005d000140458000a480003480c03002a041c0c60b41d03024084804460010300e850854020104841c00d14007039640385070103010441c1d00c5101c031a44248e0a401030200c0309007039800c002c0246001032840e0b61056640d40c21484d044000007010024610480003540b4003100041c8400100b1298514074040282c03103020440e07562900010b58003100c1007803c0c4951942d00380d0300103038254000c5503400222441201e0070008904a200d8043e0706030207058403052020028900110b040c1e105900b80500170f10b410402145071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 184446267 1250 184445017 184445047
    0x61602011b1404030b0901090606051207030201030e0f031305030606010203040e01030f06060b34050a02100903080f070c0504050105030309120c03100e0c0108090604030507050118080a0908070b 85
    0x34442d0305001c040c3ca090b0b01c0b99243c00d043c0c2401d850181c5141e40d603030294030400446200e0345000d84003c883e42c01401e070612100c0399458a1a000c000c0c1015252081e41000650400103400380c4000801900e486a4059926000c4503c2c54840c43d4868883c0701d010403e1540080112402d55001c500b049500b83e08603211504000100b12040f56226901d0400041421400024080d200c41110000307940c091159241000b00d42004200721183c0001041d2000283c0300180c0101d10680c10ba904600ba1fa4060500362000a1958005015050000386181c08a64040014016148980c2c40c80c4135007516501400100c690074016690598001c1010500d00c0c43d050350030103c81580c15088404074107124001c28202041480600c100d00d4846040f034105120078814071100801c01e01c1c01070450310380303001c14654541d405080038041c05070006800f41486003e400401041d55031050303d0f620203d00d031400056552001c0b00d000d0003d40c41ca2008109181c02180150440703240c000001e081c9141a419008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 184447517 1250 184446267 184446287
    0x20904150617070c060f053c130c060f02060106090e0a2d090201030f020f12090a12050307081e06040b12060109051f06120207050c12061602011b 64
    0x4180803403a58500e0014010340103000107101006c101054501703046201e00040005080440b44554021039003048010000700c600200c900301c00c5115980d0380300e58220012213102c4035000384c0301203940c81010074410f42011010318401e481d0781c2180c1c903aa0742e03241e007110038203014000c141050319030351302184a0b4041d541022141b14901d40b01e410800440c038030805808000744050210b00d540390982c41d0190340e091f2081410005d14220158504800c04610410900c43c0c1c054803030243d107940c800304441c4507003046403101144d400300c03610302c0403005c0d80405010783d0011520710000850340c80c0050448901000807141022034001024003d84507001004041c090700c081c1203402c140102e04120900408200c03c4c0d0007441c02d05400240d0b42072070318101d0030400801c00040564203401000700001540049001c004103200c8800503110009441e0a601b058100440390f43e01143c159845403e9030b030041032190213050a030200c40d90701413a618050b03003a25000000d02440100008450003054050500c00c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 184448767 1250 184447517 184447531
    0x5150702210f010912020f15072102070b0a0b0d0b0c0906270102011404052806020703030c09081209090702030408060405011a01030b0f191206020904150617 69
    0x1042d510944a0701801c481c1c40c480c3c01d51710807032a0709030448120b405100300300592103a40058810b0340c040803615861400e0103070654003000500d980661715560160290480e040710305605555a910504111042900031345e034003086d06207002d15040c400e01d003000c0d5400003c0c0d130000401641d5581c400941415800c100b0406400082c10030840414070641011084051041040300101800c0d102c002800c42d07007860503031403d4001c040240070104e40009071303080c4444140d180114140e01e80340004503e110010b4070044c50309002080701010190160800c1c051307600e09030380710300410341d46140300350340c6410560121002c4a03040050000c1c50400d1050103502010720700459141c166a180c100e407500208440540341655076010909150480c218450b004070402d103024400200e001001440302641c11907294480e4200700b2039115a410f1411440c0700600041881d1100d505042c10b0050281d840200224803c5190941c240a07d03002c06014609a07aa40d13030311020303d1403480c0801c03455030700094115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 184450017 1250 184448767 184448773
    0xb090c270f040f060305150702070e060105040e240a15050309031201080f0714060f0d060302090a0f050606070506040206071a040f140a0201120f0f150515070221 71
    0xd40c002d4507103014922196541c4500024507a180d82841c6080046444c5905a020030754002e12002a5001a0000988403040315201c80c43d2038800050360b080c800c80d03004d80150070388082003041d00300c2c03034614803640c074102d100400c04d0b441d45810030441e0000e024041c9090708054074001084592264010319440070b1500100d070300e001c500110b41500707108240d20803042540200142c40c0c0703199050011400030b00b001c10101d09441200d00006070076010300c502c504c55409005c1203407918600e840c2c010710019a00507040410300c0c180034010078054407450f902c07200020300304000700301141491011502003e03002409010682c80e95800c02949510481090700c01407561520364100019003505540240c2c4120340d1981403401b54900b510140724003000f14400c9800c031030010b44c0981d03044014030801051418001941c5608070a000004100801c203d0043e11702e40482e225440044042c00c0082d514121034001002044105488039482030080c0250000c840d102032a0801418001c50b14140d1017803825 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 184451267 1250 184450017 184450039
    0xf1207020409150204150c0b060d05160905012108030708090a0b090102070201080106080f011517180c0a0612020a0c0204020c07030215161e02060d0b090c27 69
    0x8003c0d4403004a64070f030301d1040d8009010083c99885170342d01c030788078200c50502182200040d22404800a4010450740c041e078020000f0504222080c482c00c84c440d01c451703825242440d200e14502004007030901400070550881c6c492110716184a1860310754a940c803103030b442c1c0780d5526900201c40c000000b6010040c1445518a03c0000502d2503404c40c1c4205188000141c86000c1800010007859060344400244102e210a000100440c5005181034441003442400000c0350480122940030a000d00d042107214a0b8091205004c046443c113809400c00000b1902d40702805010000004030610a14005c541c3d126036544c003480443c0c014013014145410405d00b04000c58011400342d900c10070004580d900080014401c500c1c120030501d1006503015030282c00c0c40160312540d100c150a50b00041c0c80c20702400041e00c6840c106c0f804000721294003820007034540041c2c505034005070600082c2c0078414400b403000222841c070a001070321208039501124120742e54818142d801d188441d44d030031a400c6030807466 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 184452517 1250 184451267 184451273
    0x604050307090b090f06031c051b21090603010614161401060801180204090c05030a050709110901210902220e010209011e0216090203090f0f1207020409 67
    0x10078103009082002011468401550803c03c1e128401003c80b00c82c00461810300074035441c001180b00868403a241003c9801c481440195554080c01203c1d54000e00701c00a41240e2080208113000d11004680e07400080900901c20b100d401d0003010f40c101c3d08210148010400b0714400e001000030070040c603510510f819520340d07a104100600e45400c0c0c0b005c50503000e503119510401d11940d00242041c2d00204000078496022844420342c18030003070f10541d1a0316201050040d0070b80c0d00401040000c0c110340780c0d0b8081d482c003592284018801c07454154908440880b168074a801202c0d07400505170f407000ba020003001219001d601407a501080002d580c1c100304070040c1c030b5600d4441c21078440034540c00c0b42207406100c0c90f02551030598482c0c1c41a4018050231070143d8110f0002030b4044495100c1281c6640e8404040303250001c0c00e070341a480902070320030000700d040703040c3c5c020b600510b0180d00340d40b46404813110565036801c2074842c41c1d8803580609509102000d184001d03000813440180040f40e500e0442d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 184453767 1250 184452517 184452523
    0x60603011b05030c12131b0303020d030b19090903090608060d061e0504200a0e04080306122d0d02070b03070c0f0c0609120f03120b09040303060510050403170906040503 74
    0x103950a803071050030320468041c01207111f00c159081d20b0850342c02c04914110f0303500075100d05202000c1000c0c9903c6105004450799401800100c0c04a85038000d9501542c500c00400548a00403041e00807903030843c0c010402350300c10307101030340f1848002d001d805a0300d0302c558900008100588003910602052003007114003462602490340154041c01c480c1000c4c5050604200c0034020352104184181c428401c01c010758510307019a02e5000340c20110740b0340c8981c0d4034404900304e80741890618281c0c1c0100503280108034440c00403600381c200f18801d120819585002000d6552402c0c0c08410056801a0410003407404c180e4021a80440107180c51000c9034240c1c1c2da81d0b2204107800341d048501d20040c90084c0308107a44403003414010b01100101c0f10034810340d07445004000c591082c0103170810103500d02000d40d00c0129040050794901c0541449402c1c9403504005000b0701150082032300c55003d403510328149900c118203480549821006d45100100741c46000d804a07801110040d800c04000d00000035140d4043c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 184455017 1250 184453767 184453771
    0xf0703020c0d1e09140d060221091204050d02120f150a1503030c080706110711040b0328110a0806010f080115051003090803090f060603011b05030c12 66
    0x70f80b01d54851030309018004910194100d91003040000002080041c0c00c642c000c4075403c0b42007500e06081080080c14648081e214068032842c41d660744042c43c0b0701061201c60303803600c00c000d40010742e03914074001c0d070b01001e0038400ca00c5190780c09204500c03108058908004210030514584084440080a8002650501546165006402d81ea45d01001004040c17805802d190a0009091441c0503003941d130042d00c1042c040c10042c02a40c00480c0000401a40b80c2c071900110382c60355042c644420303040c58207480c070a043c2803003e03000e5420070703048807042d050001e002460803c110381c0710045108103005607000110000d005442030000c10207106100d48901d01014040d0030940090702c5158101400c2c200000344a0f800400140c0c5007a4140d130500c4007988001d41903e00840340740040b00328200b8200c01500301030101614101c1c0001c2480005480000c10744500700c2c909090387c81e142e442008241c202d844540301ca049401c28152501c1d20301d84640c00550340314508145850404400c400022508030342 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 184456267 1250 184455017 184455043
    0x80d06080106140406080604030203070807060204090f020705011b0e100203070818011d0901150201200a02150c040308070201020f100501060e04020c071814040c0302120a0b0f0703020c 81
    0x5802440c03c818201030003031038007914034400107220307a04250390000c0d602d00c078440001d00081008102e620030400141c0460b00108080c1400380425910624214000e5100c1c11084505600c0c2c510482806010200c1e04824800c01b500c80d4190032118005026444080300c4041f404c500081044000107200d150140c0b86140001e035400c40e08a0b03403100050410083d5000d48079444551006407211550f54020403410f5510b41c1c40b00c0e04c0440d480c0b903010790240c61800a0051801900000c40401c451004040c0500000350380c01c0746c1844a0b4403280503e01c00094402da0300c040d404200c1070010840840050004d203206104a0b0001000090100d003000440703040c007503003161100c2c0100005a070085141d400040100c404604c0c000c944181541c0d1000540f0418030110a5817241380d810000540c40300780c1d500c0303503440c029006251610340000b6010315800102d1007800140344400f15038100142100103161300c40f000c1c54441d11508044040710400078482c8082640800c24040f943c01c0501800850400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 184457517 1250 184456267 184456289
    0x20705041505040c0801081b010e030f06070e0607020616030504030b010e0f0604020306010507110f0303180307080102071e080d0606030b040e2805032109071a030103080d06080106 79
    0xc109070810003a134008001480c20425204010300010070045404a1604003802c0d202c2c02c1d02d1903100040e10406525101c8a6250080116480d8619401300e81c040c0702b00d07415074990940b118000100680b50141c02806504500c1c03c0c07144159204842c542c504246001e0f091403410903607207950311403410b030098202d1074807040c510003408804001500f0a9400c00d004a03019810b514082000a1490003000005054000b1200b080005912030308004000c960b00a41a030395160521501d06010424589945000f40729010b000540041d06100352400107511070072030340f4003001741450203420034040c81040ea4505800c01203448d51a415200c0c42c0014001c039140070548800320410002181c100c0d5211800c00e030021034407031356200c0c007075618801482250015800c00514138107020385140618000200001005986d8018020500b004581f10780940000c0b50f400d16181c000d2440d4030302004a103419401d0341400184002005c40010b410980c04412001880341e07902e84c2d8190039204e05070b1159000103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 184458767 1250 184457517 184457519
    0x3040c0603050603070b0906032707050102060105090105151e070c030501050a1a010c03020c040504260a1706040906050f07030b0a0503070e0408070b0403120e061005100207050415 79
    0xe6054080d1650001c01200a000441d01d4809440d549105004c01241724110000000b0840c4810040a410398a10400401c0c40c1013000c1c114180d031a1140d006a50140c400d0400024071382c60702d5010a4140c0760041e200b400000107204110206411080a80c103c410b051034481c415107060001600303000307009008841005256091460071100d02900a2803104d0618490411580f428801489404000c0c07030035080d401400d0038201d003414a408030195005061100340f00c24402c5242c90f4641e001e245101158004c1c0c4072a411000d2449805040340c003082c5072500f44c0001c5482803510359403186d0040c0021071140c08540e1001e0803280d044a020810b42800005d01c80d00c42c0c3d1620820314046800e6610139001400c000000e03076200304610074440300d0109000001c00f00040303101510802540710034201218242490b01500800d824540a0042031070800c080703c0c1001d001130b0301802401c0c5541c0c040c6805041c0740c00d122640c5100101542988210b5200103901d444520500801d001100480410a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 184460017 1250 184458767 184458779
    0xf0105040312020a02070b090102030d090c0e010510090603110d050f0906070903150b04023a020a0c0b09030c0d020705030f060106090e04050a020d050c130509100f1103040c 76
    0x30503904403a546071042c0090713000c95400041140030b9640307410060b5120204000100e00d0b6104040035160764509008020b001c001040840000303a4024140702c041c17036a00e440c02d10026900045076580060b800e90340070002e95001c1e42c000440c0c0c1800d02480c1d441c05880640c08030a80d0310aa80e40a4900360890402100c040e05001a0303801c001c09241c8200014503644560759041d8011851202c5941c4e2100002801d90341e5130704460030901e10501100d10800e40c200000118000c00c22034542540f04041d00134041d1942e40f08586080040b41c5a03620346407100c1d15100c0c60f80100400d60401c61100300a1002005001c20621101c1581d41c7e000300b05580c100014181400986400c400c1950700400051110a8000e414001556520490303498030341d6072414120700d400c05010020303400c1a2001100010709c400801c1200c0d401c00f0617207480c441480c030501404100d55088800081a0700500c200501800c95508086090030b9000008204003110700f4079034005503c192412640000c0080c020059 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 184461267 1250 184460017 184460027
    0x4020301060b030702120309010204030c030309090605060412080c010f1a1503070221090406061d100207170304090e0a02090c130612020d0903050c120c031206120f01050403 76
    0x1810440305124110b04000130041c0d5140f0703040c82140e98442000c000505207545c254107640042d40c01a840e000107603a07074100502845114001c001c0100c0c1080c80110302410120111000c03140995158108160551160100ca03040801148529500c50000001b1440c0074024404003540e107004188100440004104c68040c0b0b02a0200800605008201030a0f8011a00c14064042d5011489400541007103401e024450359543d03a621616041000c034140b13031300c10842c000034254804500b04440d14542004030310901002e0340c100591014500b4810200380d1411003600801403002c49080644520b100070039643c01c800c0c00708041d4031450000d4250300e82411040c4d003042c498001c10385040e81c1d0404019410301c00e03000c5c40091040d00c1d00800b010400e0340d03044a6104c50b030603100b0009a902c51400074056885000107420340d2060780c94009031285c8a000701c41071031194100840c600101d684c80c0c2d00c0386000c010034041d031040f51244000141d020504c0110046410f0100001c0d46103042d00d0044c0c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 184462517 1250 184461267 184461269
    0x608010b130b09130203120a03200c0c06160605040503120f010f030305090a08010203130510020c100902042c060f010b03070804061b03021c020f0706020924030402030106 75
    0x1c011401c2042969042d1a0f401c83d80e07400001258001c14414090300111340b4080d1100c0f030500010500199100c070087e4140d200303001d074800b4907c40040700702907100b05000c20b014103c40c04a20350000901d4012515103c4010107015003060303166000402c1603102d520840301c0881e024ac605400002e8680030130f000c07002c90342d81d00980914580300e09504142c400c5840c0c801d1400000c091150014086010303507103046001c0000d02d015002550b5a2900f070003001e5a03000aa50221a0380c031820200307c440c1d460328006d0722459045480185202c0c90700b13000780c0c0054035201100741e80160341e0300b0f081040d0300300114044900d640035000240e483c42c01c1519091070300500030014a0100c410100600801c89a02c0072241c02402e24030309a00980c4450034584010000740d036106442c9420030342d450031025015000b40c804503100003d0410014448081030040e8880c000384c215000c1020005100011042c0c0c6c0503004d622000b40941c50321000020002c5a007641104102900450100404c411440d00b401900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 184463767 1250 184462517 184462549
    0x6010e1c150e03030a020901020c09090a030807050f09040203180303010e0f100b07060914061503070807140d0f08070b0103060e070501080601270902190c0503121302040608010b 78
    0x40b810702d141800b07481340400b81101c05450b80010312000c00360b1080010428090000f402e0303440320300b400d0586541d900042c400c218007251801b000180024007402c01c1d202c0a940e0041c5c064035140c004000c11000f50700007410200c840f2824482c1103040b8808002445c0a890f403882c0305125402c0100d03000350300400041041c4140c0030610001c0c00030201c10380580d0300059010b0b0004c508419113261261b03003a451452003040341c5c4038035010001030341e0025504503103840c015419107522a4684013481c0d296045800f9100200c1c159640c202c1d818201040e2111070395014090320b540c03c200d143e41c0c8252607071200605460307030303000c0c50014000d10105205000d42814002c0c02850341500c2d04002a00889004200c50306200c000d07290303042e2035581c0d101c0301c48151301c10503551345001d0f840304000d00080d0000b450045134142065030001c070440c040c85a11000c1a00301c0011400d00356414550b250483c00101495000d00c0340046150041c0c5480c0111806403072601c0020130110300c040107000300890400109 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 184465017 1250 184463767 184463771
    0x9061b05151f031e110d081801030501050a0519030804060903060b10020d0503060a0b0705031201080d0206060d06020c0f0a050d0e09190905030708040f060504030206030a0506010e1c15 81
    0x20400900701e14031410303c4503407042c05844c0c56212405e01e0303900d1011005030240c101d080445a042080083d00c024440440c00d9541004802001c0f030044080358400d0103005c2d080824640b050186103007825483e2600441040c1c0889401e40301d41d520400c5030000c1e4400d0b030100e4a004003c0c4104410b5004542242d08107503200d42c003490003400020355881341c1654103828000c0000c0450080d40320001070034003074120000c613240e40d5a07c2c0d1900c1503803a4813a02c51100080105400450052804182c420145401e40d0080405403100d8081101d000c00c4030004480441d4204130210340c9110501401c103e03625848060001c1d5800c2d8181603040024520102c0c04006007000010216507403950b8181d044440303000039040400007411103800400540502400600c000f081480c10000b03642c00801c15128003807420750300a555140291980e01503070000035401b270800d2001600f4007502d42c0c0269400441454482d5415a4180210b810494031100c0d0380207080080412005010200015540760849401c00b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 184466267 1250 184465017 184465019
    0x10c0917060609070504050a0803030a110412140102070b01080d030f0608031b1015030c0501020627070b040603020423060a0f02070902030a020306010f08040309061b05151f 76
    0x801c0d11410000c0c0300c544901c24030000b2a540320310035015900a0007002c1d041281f4151540117041d0750350000c89071402c031607041c1a41c80b014291124251004c64030804800003000126540304171808021101b10342896500340502c0010400399040b150082c00e00344050501ea0741410402003d440c18401054442d90500030108808038000007251900128014083c0300b519421480909040400d000038800078200054481c5014140122504607845200d44206065544005a86031041240c000c00e5081d114424034a40095905200000c5018401558070842d02d4814500e10703a0495005400020f0307000c50144100c180c15101b041221120742000a580d9080900140e024450905204100026500d10000c504d0003000118041d15040d5015920382c50600c11060003504101d40c400d000885148054002e01e0241046a0046400d035407940403103130608009481c00c1200c000d60b615111110000b100c041801486101c0355200c07180d40300f0300503040503400500c004200a0306402c6980e084c3c60 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 184467517 1250 184466267 184466309
    0xa0b030c0a140103020f0a0207170609071a0c0703060b010e0108060619021005071e030b011e0905060309070905090f0d080627040302160506071401021308010c09 71
    0x1032048110740402c0c0580010300742c0840124040d0081d07070000d4008410100b0707010182e6402003010301c02e5a80da03095960104005407a600c1d5240d4080c1c0c0c0400d00d54020310010320285d03048441501d242924402282e240661810220380b5002d4a80d00544a150f40e808a842646d070303022601c004c20100910342640345052140005000c1d20031891642d110080b0310803070301c0020380207115412104418072020402c526040001401202095400c13030008200341101c00944d034001e1188000707441069446180c4042018503c1c05002285079411003444004100040c02d40d0f902c00055205510b600301510215180c0201c14082d10406091809250030560a000305c02e0b000042c1503401044615002d03d5649803c804035410003003455001032200410800403000000310900c03203009611a03401c03500c004d07051040301203c66a05004207580142c0822002d004501440030700c103028203da9000520741401704800c041240780c01e5120405036516983c8070f8015541000c41039004000100710300c103c3e280884 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 184468767 1250 184467517 184467529
    0x5090c03120703180e071818090312020d021806040503030a05130b03090a121d041a19030c090203160318020603090f100b101b0203060703050a0b030c 66
    0x80e144840c007001007203450615105181031510803221207040c1040782d80b58a030017079107140101c41d507001107104007903082d80038480c00442c20304403103401e41c0e4021039203180303145d1340301400000b90240c0400c00003c0358054490304910090101c2d0452034001646c49800c406410342d44c40c22050300c1c9100308004d03c010403e80d00c010007100d103581c065141042c0d60b1030109501404510054201180030040031081199a0400003400d582c01405117812030030782d4158100440300303070217a4400c2c072800240ca03c28800701410070b5008142820a8590054001003403000402d14446921281c80764403034003070004100f0701c150300c01400042d09141400f90318524110784440c03850204101541e0805030764150484090021108509034954000c04c07944d50707818000401036907170f220b404452426009800d00310050500d6442552001580549055200c030610a0281c0d03200b100540076524049030007003144016030341400264031404180c3c50004082c282111003108503200c03138502c94000e51242103030741c01540d01e00d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 184470017 1250 184468767 184468783
    0x11403160311061303120309050c030604150c0509030a120807050717090d0f080306040c18060f0c080708071a1b0d0906020408070519140405270c010305090c03 70
    0x1a50030a9580f801002900b0fa220310382d07032016219021b82e16448407059031541012140500950031200039081c0c007001c0544400c2c0030759000b040d458158102c0d40d000304440e00002207142c01e80c2000c504001c0c1081c0401d0600b2060042103d42c802c80c101c42032a09500614403503000015464101e041545640d01c054080c0543c040320450401c1c082075181031592882802801130b94800d59403000f4410910b482a060f8009a60941c841c80c00c3c04103a03030150703200e0011881e04007403052000454520b805016600c1d80d0f0701e000070000b000701100721180854140300080010500c0703000381580d51480e6042c00c203041c000c02c130216100d640911b824000340228440d0865880b61403520f07006d03650720300080c500c0001c00306900010701f562f00100d00011030305c1e03010803100105c45081c0d607802e201c00c0701813400c050300c0130b06030050400c1c0d6212011030400c0c174105030780400c2e840190403541c0300b24032544002e410b0740d9481d8000d5603441544070700090941544c1c5401a142c100c401d41d80104200018400002d8803040341c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 184471267 1250 184470017 184470019
    0xf0807060807050c071a0705191203110d05150d030f030c050c031209010626070e0606030727092f07080906130e04060c09060c0305070218011403160311 67
    0x4142070008484e0900c070222001315901100301c8003d02205400d15601c9c0900107420398040350501c2100e022035000380601d1100203000b0000714600121581100020700340a89002c805400558840c10a511541c18504805001e51035006201458010080548810140d00070420000f840120070307007000042920b18811080702e4416003580c492540078014001a80211002d448521a1a100740c80341c1c2c941003400083c2e142500d400c41c0c1c490342c4403102d00c4d40550311140c015000700f000451941c842c0c0500c41417505003803220359032131004a00500c41e20082d5080300f035506a40c0c4d800184440c0c641c05001c91104110110440521140800044c40c1d008940300944503000020313004400340c0e034a004482c5107034081e0b1917403400075032144603040000d00c0c121000c07190b05180c400e202e581e0f180070749030a13802c44259079688444200303039590844040c1c1141c0c0301260402d60100014191207441d015560281c4446498200c1d003141c10b108040c580421041da00454108c421814000302c2d100c0d611803820300c2c034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 184472517 1250 184471267 184471289
    0x7060c1704061d01050a02040504050f0f0606070302120a080702011d060a0b0103060302030d260402030d0302070311060f090c1e060307090801091b080c21070f0807060807050c07 78
    0x10043e075112040b210071149401903946403008004400b0000d80c05042603a00a4504118950f501707200c03080e00d144240d400d00ea44840200c000303100c0c1d103012401421041c1c4070b0b1064528800781c00b1078046583c0c21a10840c400b14003a4402c10070716aa091007410351903100300269454a444010306203886940160112680585540110025900a0b00264011580a802c40d600c100481500600303a81100f64807414211028a00100c140d001240041c05250014090171070248408000e60003507020300812401e1001d1810307400d05200c01406414890718502c050140c01d031070701681081c00c025100700441d02c949010f507004414410b0000c0030075040081911025a41d455902c030139150f802455020054943c24440b8210402c01042c02404d0a40b90106103240503c1d100c02e4540d4441c030b18a80c03020340121003411000441801281c440c140e850301030080d2850b29171034892182084020360460703030442e0b1080da001c101c0c0a5103c00c181c2e60140c102d1510b075050007081c401c021f484520503c2500e071a14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 184473767 1250 184472517 184472531
    0xf0c0307020c030f0d020c09010f0909060f290613090b010905030604080406020606041a04051b18150702010207030b06011206080607020c0f010c20060f07060c170406 73
    0x16000304a00502c407403006044803401004500b056070742d5207035800020014001d01540d64501e00304241140d05a030f0144c05154840350070494524010010740b10184e505645800a42c10003045500c110100c20705211032425a1219a0500780d80d1010f000c03000a001e21010000c00142084550801c2c0030b86440060100315000210012519008950041c66060148030280810007a0304e10007001110565000e80d50559a0607042004803980c241b00051112600e20000e900c0e4030303055100d298080c40340901032040c084a56044092508951306c402c1442018507083c0d0982e10b000803000407412009804245000031690000f511000c8502c8000c00e025845000310b0600e0303007e00315111040d5820142000400e650b05c020543d207010a940810160040d03195940260070018010314150b0ba040c1c40d1807062a81c1640c4980c07000e01003042140c059420103a400c11130350b840500510959010410860b1159100d04040e406c44400300c2f6400d0601c0b50301003100345200100d80764964416082a400070b0a2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 184475017 1250 184473767 184473781
    0xb0f0d0b031005070c140d0804030f1e0c1505060a050d03020c0303030703090210090e070c0f021008190c0905010e030c220c08010f05220203040606090b01080f0c03 72
    0x94002c9075418441810300c010425030300e900c901d40308043e41c021046041e450a240d021582ca42e600701c0410b100140061001a01203809441103800c040300700e00d44010440100428481c240600240940c0018451000001840350ba07200380840446a460f041016013000d0340050314001d407503c03490340182e000600c810141402440b0200d03d001024058036964a44104000c004081c20384049110307488109039000228820b2100c0300603203003880608182030300c40e8142500c003d01d41e400d00b01e440b025421013610050b120015520403c16050701c80f482c0ca41441d10b030050790310100941c0298403e24013031415908a90200c4524121803003800d009810318403103c0820308105241e640c064110482d40481c681c85070006d01010a40c04041104000c0b101030004203c414130700a20461010038050030090203d032404091b82003c016401c4210ba40d043d0f414000c00040e038004603001d940b400ea44400400c030f0704856000f070385890b9809107043c9005180034000c00d0340b14040034011809007880440003c240c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 184476267 1250 184475017 184475023
    0x14030712060e031228020307080402010e0d0c0b030906090d0801060513050d0b151e0927060703060509010506031f120f05070f0506030403080c0d0e0109020a0b0f0d0b03 74
    0x700c0d48444c60032014902d0031803000e0b41003030500d143e10010040d40e030352041d11030445842aa400345404c1e5850081c9511036400441c2c804920305c281642c45100d0305001c50010303080c2e5500000034180d5031072032a140d10f4021659810041c00600b64110380d00001400301c051540000d41c141500d03040e090854840844104841041c1c03a6a0800c1d904070741c05000c440188180c903c0c0c05c0d403165141c1a1461664182682440b01e28421005d0400c01030b900d2038404502c3d450142c2040d5400340209042c40800840c3c1a441d00c100403403130000d940e042c0c0010041c042003580c18041d42025010070303a030381d4806526000114103039110017412108001400c1664012a10f102ca032004020483d06d5000d6401880f00d0030094844406018222000e1140010021b15854280303001011148020909c0c1e0445c0d5032500c05482c030040040103100c039220200304400c0400d071746118900c40440d0740307000024181d0051041c40080b0300380c0e8100700d01008047c0f00480d5100014400c640e03203103003a441c021403280340d000301180c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 184477517 1250 184476267 184476277
    0x50105010513030611091c1709030d030e12070308040b1308030703020a02010603050d0e040e06010f030813051906030e0708100f090f06051902070201020a1101180602010614030712060e03 82
    0x16100c1003002020103051a01f112001c50907009100346103003051410f0010380d01d40b02d20794949416400c81142100d600d8001d0780180e00110501064485440308a4040202640b0028045000ca00f520040c4014056074411240d4000c4402c1e148a0f0740000a854102c1203020007000b003010160000740c1000d80f07910039040040290b03844400c40d07001c1e00d54207901903c0c500b9400c3c0d03154000c46ca001810f03500715000050700d0b0b04aa405040708901c403800c40c0c681e0070040c1d10046455942c0000c2d486c0000c3c1d40e4503100403000110041240700407400381442001801e49101c0451003443e0f034001d110170702c042e0703001040b03546560b0600a4001072044210710654040c003070b07410b80035024043d040392400a000498000c0c40c440c0803214003e124114101002030224025640c01a0060707024001050000380b4207031800c412614141442c01c01d80f50501843c0108903503540100005035115103040004031125a20b990f0941800c40140c42c86130b00f0030949440840016a0143c40d5a40b22508085054800d01c00c840c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 184478767 1250 184477517 184477519
    0x6020c0108061c0c0e06011112030c0a0c050f030d05070c1a100314010e010c050c07180e030c011506030c020a06021305100903050c09130b04020301020c1005090105010501051303061109 81
    0x5010301e5a6070b41002017407001220070a000c200520010742d0550000f084048054000a0381c05007152142c080c0c020b82600550204030600011144440c007150003004400344000060f0000c540d25415840c004080c1c42e0b0107488034050003031540d005130008102e20382d0a0301c08052101d08030600e954001d40384c9005940303948050249440d040c61740c483d80750306411000000d405d502c000d011108140ba4121140d2080c82c0c510100380d00710407001c0c04100b80460008024030130101380400d414503d8048607045612201841e0307256927440c01040811403800750980020040e074241040368400000300652106510b0000600280d0b00288044003a03001c0204200034040103090710500b004600c002900c2c002441c04192a68416a080c044d054a008048140b040b40b11100c8102e031071286a50b074900c030140c01303482281d055400340a801c41c6040104005440c40501c54800300e0103080c56051142181c030182c2207281003200c100980034040c8c01800d07020301104e0740818000b035001800b600101107401868502e0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 184480017 1250 184478767 184478783
    0x402010e1309030207080706020706051606060906140f0a050102100f0f0903230307051801030e0322080a030c15140a0204080d0e0a1208090d1a0106020c0108061c 71
    0x60020b1541c0011083d00346c58150044811703483d100c0c2c01c00d980d078451920908c0005030082040d01c9801c010010068842480f41c1c90102c8c01948910700101600e070301f904400c1c2c100e400c101824072a440e011034141e0f05003c003507840420700d40c00c0100013034589110074600c0d520652070728500c440b54005a0f1090f52584a102420054164185801400e0b1600d84550210035142e400304810310314101000ca038015821501c495180c4418060041817292807a480181450342c0c0e02010101c0450600c0181848980c0180340714800c020f050106558501340c1d00450550340c007000e81c40d070000c0e402105040b101038100c00303114480c003030041c40075005c0c1502c0411217490341ca5840030701149580c0703038001c0c00c15101d5030029140d4032000e000e001c50703101c1c0c400e204160f80102d0704042000000c0f0b4802a41b4242800b03154511b1501c40060049041c0c1410504100c0d410f21400c0c40003201410520030603405000240f01070081440c003030000920035100170381614490307607520440310130848081d81e0152241e9402400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 184481267 1250 184480017 184480031
    0xc02010e1504080d0509011e0210050718060804050a0f0212100203070e1f050c0106080307080706050105010504030c1401051c14130b180304051e0310020708030402010e13 75
    0x6141207411038415101d052150300013469655018900303031015240182c0d0b032410f9000c4015107061444000070490010341c0242100e2084004443c09440e01c5410b00e5102d5a0035000d0500c3c203042210500e0388403804015100c024000024004503129101c50741000480c0348540013400019115600403c110000b489880e074403000301d18294000c1e500ca010581c03916903040d0f06c0507007880101d01100d090040c200c4003130701101011900503000f40550b01c02c9078000040b100d403110041e03840e41d407020740107455403034000c80c0030740400500b0301a550140c6828a0f1080c10180b559071690000200b500520803408403c10701540580d100e14142d0780c0079000d001080301d8001602d01d11100a01d01d46a481d15060103c200207400c6000814021000a82c4030719403103601d66075207500e00040c522a81401c00103020030440042c80d80d0319144040c068400c06085030f00b500b2651010113107005802c10401c51054018424080440c100b001500d03030080e0207080824900130310701d00085100140d05031a0343c82515040f9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 184482517 1250 184481267 184481299
    0x908040b0a080a14010e241507150c0f1103120106030509010b010201050613050912070506070210050103020d0605070e1c0b010b03130f03140403030807021c0f0c02010e 74
    0x80143c042d01d030144041111810f01049440c20040034021071101240c0040404c6540540c0d50304c0c0c9102d546041ca4111071101c0702c200161000340d590b440290040000b094507824016101d403c2418611007500400400190300c5000d8500d0318544410402d00c465280e054501005c02d00840305481b284175910b80680da1a13483c040c000344003d5841e400c042d031030071010300300ca035005128480c0036280080490012440503002e0300081e040040104143e40110080c2010a41d10200540000340c404c0000c1c0c1030324a0541350083c41e002030041e40701d050702d090100400158559141180c1190b8001d840401d00384c0e102602942c1c0b44c2c007004089904460b54010b0040c0882402042c4660544981e91548041c2d90350a100c641c1408269a88140381c0d0f10316082000107107186a0810b1118404e0400d2019132080d481042c2c2c1c20707017241d8001c1d00801da0341c0d0200302510358140420352171840c441c018a0540203180340d0043c444005080044103205228220b0000c1d1380c000d07020104050f03c010480e50306112440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 184483767 1250 184482517 184482527
    0xd0204060210060f0504020f0c0709090b13150f0209100504051801030b13020a081014071b14010e10020a08100e0f0403050c0a030206010302010e06070b06040908040b0a 74
    0x449104014010401c2c0b00141c41420700034001101c1206030711610282c1842c3c10040203500420302d0402c4400d04121183c1201c42c01e000c140024480640000340128460a01d814240f800805203010080491146c1002454403070070710008940c00000000c3e11844032220f074000384117420701c0e280c5c0803d903035004101096000004000351181528a0f19440b5280c8100843d1031100b03010042035400160000340c40b0202c0060441441c0340000c01004005c2d031b0b0740e2a1030f0300b8024481540030210340c9420600400300f0100b00401d800007110700c3d0000301c1c2c05192070b075020720340e030f4111006007004410240208481b03800d4200480740d801401c14ac0329201020544000254440014000031510300d6002544a40341b510402045a0721a18600899510f0a185c0144908000c0c0220140038041c098600700e07031001c1040c240c40c50f1081e0000c2c60594114000540003040d41c00d18948a204101300c843c0005070161055508608188d60110b01101c140c50025520701868211a0103590041503441c0103039404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 184485017 1250 184483767 184483769
    0xf0c03021201020a08011505040302180915090a02100e031218121e0a080409020a0207140a090b130c0f08010801110708090d0209180609010606080c0f0409020d0204 72
    0x3180c404240c580044015400d03802540c203d8004035407003c004001c001c401039a420030340312081c40e141b480c02c1d42b641d0004244043d104140c6503800510001c101320440c0030010b030511b403071111601440794030b0482d003800e039a8010b000c4028024140200e51341d05150240e80e1820164400500b0758504038a001742400e4140c00542c00c071a820300082a050031241443d4100c000c007460341202400c803000120f104500d201c41c10400c140f0552007000031040214881402802c040c004102c405641c551540344001e240071850723045240c5d804019041c503003403035507007540c1281258841c0e540440d03c1d040b000000795407071000c0003450003420309220090015641c48698092611080e40314008940d0f00c40355190f003259800401480311f214208002c40201d03900101402c8000b500801e003c1c0043c40c0740d0b0104046101c21351312900600e07070007030041c40381145c01d010036584400744000802215250032001010b444010745104540600002e522500958074130071038020341a5407000703540d503a405c500080003e40c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 184486267 1250 184485017 184485019
    0x90f01060f06080612210c0616052505061e130302120f07170a090b0708030f19020703091d0906060108090f1b04110f04030602030a090f0c0302 63
    0x2034200041840c4000010312401c0c0c0b603095955410f56580d401c10700510f0321070000b501c421842188040810710040842e40961b02d0360a000050f02c8031200c0c685c0710b10f41036000e806a0a80314101c10b18040c05035101c0117964204030240c40070814203040c107261003483c881c0114041c20318003403803003080407010b207451034064040541d0598800c81c0da03551150007031002c2044001001a048103107441c1d00c0d022050302a15904400c10b070100d14000c0c190341c0388111161310220040d0300d000040f4601e00882e401415560040c0002c6145915040035643c0740c00861000501800400303041c0720100303403600201001d82c031a506e48111704650f180c400b824007030401000e074800d882c4100b12412111402d02c0c2443c60b454061020f01004003141d85441006550300c00000f48200840e100d0420829071000e000c1188074800f4010300d520100004034181400140c03000d03c415414501c0c4200881800c0d054100126000c4035004080180c81c2d846d06900304000e03047e09100680740d420400c2800d001c1c8000401ea40c011244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 184487517 1250 184486267 184486271
    0x20702100507080a0302070204140906010e070509060f0c01020418090c090c0c020f130c0e0a1e181409010f0c020601050307060e03070b1b0d08010b180406030b090f01 73
    0x484400e086409205540004005590602140c86004d01a0b005424290710050007c5001c000c004816101c2181c2280d0311845940480010000d02c1c10307510f0b02039007080c443d05d05286070401030004189035125034071800c40c0750a000944a454000d0030350654028107121910304070f0302c810700000032003d09440807080ea01030301050000038135520503214410500c0030a0b2510750324500d05800f04009011802403098000c5003a045080400c2c4561248030170f45e19035030720b85904582e290010f10480d55000e810800c9950300403031500b03c41541d0b943c100000c454052007401382702504208404040d100095007803610b81c801c0020b0000900040d08280d606015070310042041001c000d800b242d40e44400e01c62203030103030081caa00b40a2a4441c590b031400320107020b022200d4066842c40c4e00c40d02a40481003403007415501d1003103000b03224070900901c100b60786145411b42ca594146a200c8003144161406001440079210150000e86c4035500540c0080da003200c0040c070949000c20708162548115050446194 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 184488767 1250 184487517 184487539
    0x7120e0108071b0f0b1e060f010207030b070c081602010e19090f02090a0305011b0f090501050904090515010915120f0305040317280f031a03070306020702 68
    0x15105141c054401c40180d40e9000108201200000c0c0c29500d584050340c00c04881407904000c110001d0000b4003512078034614a103c60b8003200102010030024220038032902e581e810005050380d0004000041d00d8204100100941310b060040d0b441c1c0b9503814008210100100d0030158039281400c91049090007030b2208000030700c01c8410040f031190f941480701036505442c0c60071310604485070701000d0303121001000180750403030040006402c07602d541c2c01203d05a440301002a0383c40003e5000b04c1004940d801c0140364080229070240007402c00d4010541004030105d20081a0759550f001240d9054014094880c4800d54000a4908400034010140800c1c20b01c03151031010140702840c035080b83c1d00300e107c441200203182d40721110340070a00401d80401c10248004404548050301b500400302d4145022031303840000c2d07250980c900fa0780c80f40d000d8549191500c0005171542204a6490014082c60001690300260200c26410600f03003900540601c0340510101c2003020682c014004180221a40360040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 184490017 1250 184488767 184488769
    0x7031a0f01060f0c060f060f09060305460204021c0507020f0307062d0204030615262404060b0f1014070803040b04020108063106080307120e 62
    0x305503804140c0004d8114002500401c8280d8003c80048a00200200300d043e036440075444400180d41192080680d0351001700100b0001708204000051050700f541040345405900c0f00f4951801e005404e0340700c0c08022001a109101070000301450b6000b4400c64039403080d03448207083ea00e210103000c04002c0c600320109400600004141544044210040d40313014542d030303101e030080c1451455002c4c8100c100d41c09040007206a803891685100c0818005854a2039400c00c80c040e11050000d12000c0303040186c040c002c2080e0a03d81000386c0310414030520090044250003494210000440301e0090707941d928001030040700c4000c1034000c81c0900c4007889420303580d00400c001c20001c88900741d44100d8024801e10001d000300120480e81c10b000140c0c908201841d124802c8640c0122011120103011004000031580c11058254010000b501d01d030000c02c4008403005100c072040d202c0012006031640c1d00f18098542500000042c0111605480d00c5c3c5030146409030010303c40100f90408280c0d000f81042c05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 184491267 1250 184490017 184490027
    0xc2802150c0403140a0f12030c0323090c1201060303090503071512020f07080901110a0503040909020307150507020915010e011b0b0c03010801060609030f1407031a0f0106 75
    0x41c2800ea5a40386018a9507464507010080c4184c5055207000300381364440030507050315102154a0040304108410020b0301001400c5503c0011000c0605d850303c1401036800c401c21110300c03da02d0002d4030100894a4010410380703041040d25501e50700040c111501c51a070340c0c06400c1842120710a4941c40411034440b002c05480e601b090141c07208074840307250040c0c20944100602900701e08034010062520341c4070100317010554005030b01030f14952400145d2042a503441000125840c0024010746141c03031042d56015142d01c200d100d000582500c07802000d05558040c410b01c0700900100c45d094100030420035000c0e14540000740180c1c410b810090008280e044c0b0307070042c144501c2c0165103843c01448c4080056800501d860741d80302909035000b404400050800340c00300e0141180102c45501ca42c03424000d00d096801903006201049650002040000c4408d00c1d482450756100b02c40883d202c4184010f20720b058010b92028010f42200704040354001c11140c422400740780421f0b9070302040c0ea228501503407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 184492517 1250 184491267 184491271
    0xc0d02030f18130e01021314090c0d020c1b1002030705070e0406061805100b090d080702040e190b0133030f09050c031005040209010e0c280215 63
    0x348030404101940c601d021aa580500d84400180103080080a125003001120104610044d0681d40016810741081707407000e40000410780070300892622503490300442d50b11070001e003000c414410301003006840c800f6550140c814007100c0c081152242c131001c0541b02d01d81176080050301e0054244155821403648040212511180c2000081807118500200d80c144010001e1080c1c44640d81c80801044e0788a005003041d025074a505404105030034404081044498180d01c1745480300400c0000b0902900d81c000741c1130f00140c2080070107413580360302e002103809800d40e85907000184c0550801c0c00407228450384032a1109000702101c0196a07201c540d0000350044a02d0b83c00c251103400701002c0d0f020301d0b44903046074481125140100302d4a401c0d40011741902c080e21021200c41c1c101843d114954181041016020320324014103000078101a00410151300f0103018500300a800900015038400d08001220010440300c0001070381c044902d00000c5650301c18051081c01070060794030340d078191941110594 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 184493767 1250 184492517 184492537
    0x90708040b01060807120c1701051e13091e14120912070e07020307020103050c03060904030c03031104030b16030506060d09060b06040f0602071e050f13050c0c0d0203 73
    0x140c00341e420310400303a0380c13403400402d80c10802c004000039060f85038013070042031900c01240d03d400d00f00d40d0320443c004815800503081240980c807008485c1401000c5e90601950341c990a450040d00c0c04003000d6034601030a00c4841c00351180380117115008a0103101c003102c505040c094480f0700700d0489415001600e41c400f80000aa03c8041440081414a014852081c00c6c6020300100c4865076601c500c0b201c0c041c0e81c1102e1342e002681010650380259601030040c2070348420301e40070891952500c28000303669004081e0000d02041200c4031041c08150080d402582d1142c40340340543d803150b1307032480d2503410118100d4402203220203960030409194042e000c0c450091000818140c14201d0f100c1c400b40042c0210b150a848041d165158801a0380355040144043c2c020b0041c108042814090082c1c07900c0c103d035100001880e0f080b10031803801c000f0f406420040d588100c544490000c0354200281c042442c601c03201c41c0003480c0006020360814400c0013802a906c58000351800c218094600384d07104d008030b20b400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 184495017 1250 184493767 184493783
    0x70e0108031206100e030a03030203061219030c0f0b01080106060e0f03060f1003020405010b07050106171c0302040b130303020d031103010512010204150504091512170c03070302060609070804 84
    0x700303d007860541c1540401d031100c1e00d08040e4046000000901d0020703056802d41c0401d500200380070160510f00320001c85680384000a001c059101901c0400300b40000320003508003c03140301c80c070b0108022170207600c02880c3c10200410391940c592442500a09040c4038034070110b0280640e4a100741080c80100c000141d000303014007441d0b03840c004035511254000304030208406a800300070006a5592080601234562901f805071030384050300e1f280f401c40d59180c00030714114445074200021884009031009100701c004a4010008030741c101c058002e8001d54200e520007200109016500d81c2140c0300580c203ca00a90880e0902030358a1001e804a58040440c0000500701f080140068200828501d00114191000500d040d69502201f003032210b504001600294001904202c441401d00410f15404006120580030038500005502202d1800d1401441d00c00004044c50071a88500c00f0750360401e0002e401d40740e8419481c40c000303464600499a141c030420300d41e800316100c1c03403084100703034415a4031001c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 184496267 1250 184495017 184495021
    0x1060807021903080a0911040c0806091f090902060d050106020a0302060109110720031501080606011d12150a090311190b09010b0a0f060f0f020606040902060904020309070e01080312 80
    0x1174000502440c050580c0c0003100b01d0070000c8562038910510a103014241c0d2241c00a090040410440351405080c054403114030341c10103c000951181c1c40030485034940b00000300c4190b1840414158003e000102c4182498440000f4207190041120a030300c602c86e900f40d800d140c0e00c0e02038004c07c46d00740d40c1605100301820b0011600081c0044150300c074070103049501180314031207900040e2400032403040e00540d11035108010040010100300c540e40243e024281034140b108c203003078200c4c03958101005491245402000b45410241c6c24480511220501ca1901e885482c2007003102000c0c1121f0700c021000105a100030044894012070003e02c4450700084403041480151034002c030070b16000e8416400b656a03081c03c4141c0c2d9880580400060800e102c00540551500c80c024041c03081c0e003800c010502001c080d00403c2d4a80c00b19001d40d21800071600003031100044e00205071240200748080350858400002d00182c0f00000540e1401c0742c0102e11210b81caa80c84c1c2480e43d417030703000c0d4507080c1c0100200000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 184497517 1250 184496267 184496281
    0x11060601050a02010615180602010605010206040209060f040507030b0a05040603080702060a17070c0303060b210c04170f010b1c150f0f05150604080a060e0f060106080702190308 78
    0x2d0103a41038030320000c110b55894400c43c00d2070705d21150f001c0d004a2181d040c2d698401c2c80c901034002c02015180000c1101c58a0440040d4480d01d00920003441401c02c81c0000b0000c0d55184584c042254026100700454644400f0282c0100081151039104015040c0006550310b0300340034840c1a6984000a01d05046444e0700340202d0340c0182c40d500c010301c0391104c1040d0840d022803080e40c1c0302d580b1641d13400f07009150030f040260844401c0d401821801c103040024185c5403004c03e048040e109405003d40c4031664500720010003d0250741c001c0d030300c10002c00310701c43c55103c800168085500040e50003000078618000410101154444103003020000007084075021503416020080f1001030b048000c030b40c0c3c0740e6030350b03004003101c001c0041501200d5881082c080c030126640c0d04213401c0380013074031114505810041302542d9580c20301c06c0142466241c0e60701e0010301c2c406100241c0f004203c03e08840c0d031035848000c00b400745041200c01d0070042c420b103101119005618001d03554900d4042d2500c280d1503c1c4d100b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 184498767 1250 184497517 184497527
    0x303070c090f021b161d13110a0b04090605090103030c031b020a030303140702010614060903031e030a0c02031809070c05060709051c0209010608040f0503121611060601 74
    0x100c603054125509004000510113403000888181d5070000c080d2814400c454940c4990b0a4203822401032a100300706d2801d400c0c841d43c01c10030b030000c0003440c403640d081c209460158848075484460703540003070b2a500005520300c0c4050190081e20490701040c000d1944500034001c0200c000d10000c5c0008031224100800719001c2c042c140c07901b04840d100e00b00222115000b0500c0103035103070310440c0026a50740d6240b24140100a0a5401c0707640c0d44004c0c0b2507a450410744203900700e46c1e03062140c851340001416003120b640030030440780c442826805600c0050b00d61007420101d500200d40420095003070103448100d5234800300441d0110314441a140305071208420030301c880810300030803070b1050004600c1c403000800c1003081418840d06050f81c40d140000d0510080c00580c0741111048600c11807110801030050380c480030280d040d5050352070040e18071754072410030940d1281101809455030000040c9002103a440d41c220f54400d078840c000c52200190070307400450f100300c460400c40041d42c200c600400c0d0258418 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 184500017 1250 184498767 184498781
    0x90403021f06050a0b070b13030503270f010222030803010b07020102010906051f060905060d05071404060207060e0105070f0209060409020a0f05010206090d0f0309150903020c040b0303070c09 84
    0x3407000141e000c0d203078004100910066000104121304c0824840c017048022009594070806030010100e12181a581c042c09a020182480f009040e4022000c060301d0541c0d608401a662042c3c21100613000384482a4000c2d4403000b142c02c1000140103004141c032507480c4219084a61050f02d5915582c03a0080140c099000268124119500c85412102042241c050f0740d0103901101124a40340c030065141c07400d59600d950044080c004440300c2001170790380d4070065030850015240c2c042141c0d552000c003203a060714001c0c62402200c4002c280441c403254001103100680b0301c3c0b9210750080102a03401903d040c0030302407005010707040c006818001811b0200a19030016005880866009001c0d07000440035603054001c0b10010748011402c016640c0d04000322908801c4183c0600b03528080d4100081c600158480f20000341070300c3d800c5041c20014110046041d4482009003040090014a00291907280410203148540d0a0103d002510702c3d001c4111001c095100c8c5000032481c0c03500b188035024200d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 184501267 1250 184500017 184500073
    0x1110d1202090a0504150e0703090510091b030c0602060c07232a040501050105070c2903040305030a0c05040f060c110607050a0b0c12061201060807080304060e09040302 74
    0x4583c0000582ea200d90094a180c0c0c0414259400e013075062407101d40b032081005102038101804e140001000c00c5000c12000c1c00c50b00680c0300452038404601302844159280345180c1180c800484000040c080024a00019185207034261005600c0f800e2510704240112034004e441c00965494035183e1110303400c0030302c030304a06000503141c01c03452010114003401c00014006603043c0141260074038074a82442510302418090900c1824000d1644580d42c01c14068095991507109880c00e210007540c0100307a072205c1650b24071440e5582d10b80f0380740040583c0c00030341d107008560782000d1008a40c02e0040098406468045048101031890300d0812240100b00910954a5004421040b401034403000010301c0624000c03401424205880c0c9400e501c50180100107007101001409001c0c0081ca818035100e8102c1001c6440300d2421108100344d234010306840e130142c0c48a100e1100b00081d07529003c0050000c5410f5920303001ca80d400c03084140450440c0171200100141c00c200090384070003002501599071421 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 184502517 1250 184501267 184501279
    0xa09080f0a02120408070314280f06020f070614011a0f070507060509030d0815010809031b0f160b0a0809030d050408030123150306010201020c071401110d120209 71
    0xe885548a041c1c2d200d5084200321b50031015080c010b110060101000c1c2003442001130155100003011038054407002100741558244c0002404184541c21b55003101054101c88215581c500700700e0400700036031203400c080340c0b090b0800710380548002c841c0782c0007812144524159110350114244aaa0303540c844083c0400c840c00038418080422010003103180a0100c0303485190352103452070201441c04068a500c0000c002d0040100030a070800342c401030b14650b80a0a15140039151042d0240c02d6000f0040c1e440c0d00043c0080404400c94400241c0c1d092401c4c00c0001d07522034130805440150a69850301a85c00da651003006a0021184154605503200d082101500c0c24924510610300036202c00b900c0c01d66201001000502c200700402e0481c215801003402021403204d01c42c1d000c0713040c9e10306c40110914241004000120981d00030f404494410404a0656003801d0320b03003400c0300c0d220321042e815600060641d031008881c1000090054422001a00c440e4618020480c244020390700020090740c10034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 184503767 1250 184502517 184502533
    0x626010f090f021c0209120703080307030509030f0f0a050702040e010f0e15010e06030a080a02060108060618060f040b0418050f03030603061618150e010f0c02040509010204050603130b0a09080f0a02 87
    0xd04c244611006180301cad00d0880e1b564140404010290741024201032500c2d0001c020008000c01550229862110545002c0c0d4541400c280705444601071500040d400a00304190240022410360018428074402401002400c502c42c031116605c81c0c00000c4410b82800070801880506000c40340315611080040484034002110f542e098403640155483c4005680500c0051003145000c2c09100d070300041c02d5840080119104009102c0c1c0c070800360440f801612141610000c58407107801424020030702070001c1c069181d04001b03100c2c0260505506482602580e00c0c54a121200131084900070300006009018503140c421a4406d82c500420f00c07402400480c90016246540b0010f1910042071018403880d450491030101034500c62880d000c0a04101141b0848690684c2100009820301d40640b03000070f041c0c1d2000442ca0084c810790b004164030110100c02c00c42d1150205a01c000d94501c259440c03c0d0544507201413405075440d40380300500c00c3c2c8043c010f5180c44654100500740001e15403040712064 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 184505017 1250 184503767 184503799
    0x204021b0d020a030801120201050301090b120115050a050406270b100e010807090305060c070f06091211010b0108010510030209150a03060e0906010626010f090f021c0209 75
    0x760400d150001581005820400b0305401200890040100d1207030a01811030701d900091103440140280d100043d514000da000503114051300207900800d41c0b000300171040141d040120040000d00c00d545c811151804c022549041500580045504452903200b400b8216a10076100840c00540700703410f1070341c0e219940c03881e42c0d8211320904203258580310702080c81d0441300010031484006140e034040c08080401040000c40c0040c1c01031340102d12402e9503448101c10300d001980100000700142c012420034030600c00b0312030b102841074103503210713912284150800341521600f41d5050404003800302b01140010070803410101c40c1c00743d55056614005141840388400203508920921841000307280108581c541260107101e0840a840f208420f24214500003c1c4681e60f40c605004c0d50040049031150514106004a503c000400402405960039a122000307113048000c584902c0c42c07254240701c650750b00e100e95031089461409070714600c03e00007500c0e0302001010307502c03070003010f0340002d44804ca512203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 184506267 1250 184505017 184505023
    0x3030a030e030f030f01060311070f02090709080a06050604060f15140909070c030e0a12230f060405070f080d030902061902010f150605040915091a0301270204021b 72
    0x3c52950170481030403550420708024202e400e94034001d0b050b001c04100d0701d404034400c0710180400541c102c03a00c04d000d5031500d000301c50600460340081000e128050000040201e513800440c400c000640c5e00308062a0f569100000f074400610800100c1c0c00d03258010410306120711074540c0c0a0407401c800c0391030108000c01284020728125070302c00000d00403003000e104242c0d006c1c48108036201e00b02c0e20000c0f05400c0003506051505143c0e00280002c0d410300c1c0c0c0a0000c081e203201032441d4030220064480508602e18030a440b0382e0201c9040340c4038003400c0008117925420a02100903624000001c0c20307607e40c050001c0d0004e00170703502d0507640120144644420102c008003094182c0c0708076400410300c62014002001550b82e4810840701d10012003000b80640740c1d10030190740803581884800316218110fa50304030107005641d0004140d413410504155400f065039044100f94503015002080800f030b0849041e000200025000d401e81c00148000001600c0c254003c1d2404542c0e03090200300015261000781c3c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 184507517 1250 184506267 184506271
    0xa090f0303021c09050f01031d0105040b0709090c080109150b0a05070312020c06070c1509121206050a0501050a0306081e10020c120304030309020901082a03030a030e030f03 76
    0x140d00004900072944000b446456141c1c0540c20700e191032a08090001d4074159926121904241d0759500200500f45249d0090580d040c0307000013000142068241904404411078500d170100b810070800103000001807044854900903941d4800c284d03401c16000101620b9480506c0d881214040c40100d00554403c0041c51540981d89420b80d65040d01e24001c0e1120a1078800c0010541c81400034429103003020507541e03030091040c9070284100c4614038001160904410762080e902d03203010300c00001c0001242c04100d50000e25100d1248a038000f010309402d0300c107e40665900b19100800420041d4000c0016012080050038081482d135103600e581894078202e01d0a880c992007084104091f442000d0011005030a0b241030b0641c0b40c8101d400b80c69a0300c009034602d040c3c1d00381c0004002014144241d100403d12640240420b409503914041142d07180241105565000c0312030740b04083c410385c4001422150381c0040d02960500c04981800c1d8003d00c2d900100640303900041259041d41508400154 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 184508767 1250 184507517 184507523
    0x40609051012020a030b0c0f0304030509130e0717030705030d150f080619060e070e040f0b030c0d03030e0a2906010c150f1d0f0d090b0a090f03 63
    0x160350700d04014010311421039035000788500c0d680d40841c140962160314001c400e80f03130030049040380350311000c0c050456849410720035240110040300703000401d503208001346886001180c1008400c80c07841d0401040320380006d44242640d102441c10040350042c85234500c0c945440c0320030b6a040c000161076a60440d03004456140d2020b5840035202004403195042d14094030300c8040801c1803d00340307101e41e07960b000041d0002807a07554180c161414071416822600290240c1c00e03140c50780c5c2c00c00c0034018105481d1220710901c11030030692400800302c814800c050348114020300a00c04103d8245c240302c00960900c50030b408058540150584000d0100055a00c4521440b0144010382080c400c42a40b42c0480c41c3e100303044d203115024000075a81c45402251102c2d0410321003507498801014801c001c0480070700f09101c2c1c42c00c0000c80c03101290100c0b0741c00340c415480c80035144030701c1d010400946c683d001c030916807002c101040c0091040380c0124000c1d064820700f9041400e129500d400f81c1444483d0305034811 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 184510017 1250 184508767 184508771
    0x1115060111070e0f090307080a030b060f040312080a02090f0915090c03010303090b03010e040201050c0a050d030b030c0405010e07050d20030702100608031605030d15030209090609070905040809040609 88
    0x1300c07180e256030303403103480d4000709007800303542414666680c0460512415401e0410141c80d4124243c00c0d03600e030411500103650643c2c040780d4941da00c1c503002a0080c0701e070f2001d4001c605084000741014005d4001c447c088040204100907003c00b0408111020402804030090340403c005d403900c1c10f0f255444807c0c05070b0746840c0460349a600d50315000b844080250062806000140300401c005840100940d07006a4242446612040e00000071481c2a6503480c01a01910032a0200012640c0550001365101010380c1a1981c41002c103003071005603030b070a10690204007000300001e00c00301e00ca200038040d502d42c00e020100d0018004030344114240344801003c2c00c0d042d0000b0a00c03164a0301002403454000d480c0405001c424600307000c080e2680202c4401a5101c402c20a001041000a001726024074111040410030180f140d58207103070000d841e010490041c120741000c14000365001030014440e110780802442404e042c031051078040c01c1c0c058411a079414050141000031703900d5006050117449104e82c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 184511267 1250 184510017 184510021
    0x4031202010b2106072d0e03120c0606040506030a0b0103061a0103140106031a060301150314010e01090b010302090940110307031401020403030f1115060111070e 71
    0x20090a004110f850f9645070b00001c0f0700d00749155002c180154849090304104159410b4103559a00321080c26110014141d0790207034810055400c50441046030304103404848050100c050b004940e44142c00d17066015611000014201e45081c0d0003140e801403000c0c1c141c0760090b00582e03400d441d0340000e0b00b0455802d521881000841e0941e01d03444040401c007440e090054000c4030001c2d031000c2c10113015040c105904c5404000d00e605801048880715a00600480d50f2507a48a078a4006200a1880da000103410f00c0141a142d1514407030160690304151001001a480c0011303d00052104009140c141602417010208a41d102400f003440b4002000510000444404032071407419030018080f00c40c500c4280601000c261412280c0303000e1a80006040c408100361000a4505075040d40010003481001801485215064000e00102c03031190f103c242c0b1140141800b61a5281c46101e1203640741d0083c11038500084119041d80d40144042c100703450700000501d80c56044c100203800983c61407081100b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 184512517 1250 184511267 184511269
    0x905270c0d18020d030825020a0b0a020c0d0e0109090501030305070c0e07020c010c0f02101107060c0f0b0604060905090d0206090115151115060906010201060e0604020f04031202010b 80
    0x4640b6010341c4140808400704490b40000e1004110900244c02c001401001600b1a408655411414084c01001400c0500b031440b009640c0c04200e0800c8517680b0009011408030803150007540c070020500005445900032540d8210740083d02d40c1c48040c100140341e0000106c2d5403191145601850113561002d91b2642c083c103000c600201d89500410403515030500701b0041950105040c602c021003480c101b00c0d034602a0030040e65145c00c000b00a03620035014054442c107250040e442d002840307185001e8901d0241e981c90b040d1100001000b000c0d1003505803500c80800680349803040c0b640100700410001c0c03682c0e01c0f010624101c600859216090f544421401c2201d02e03010070070a5070000c07024009000590704021301054001183c455510488016500486800d006000711012070a10a0845200103e900422480d051041c0c6003603004001101c00300d4090351040c0120010780e41140347c08000e0340c81e44810b0100070f510940d8400c2001806000200000e010310030341501c900015400403801c241000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 184513767 1250 184512517 184512521
    0xf0605040b09010b030c07080f04150f0807050f1b011b031401140f011103030a020301060801061b0809010c0c0b0901022806020f0c010e0d12020a0905270c0d 69
    0x101041c2d10499810004000c0c3c0000142140d5002c0d104200054a0380c0141c1b80a68040c0a6064076003580303080843c010075040c242740b11136580044260b039084810a030310001500c180005460101c00502c08001103139640d200d040003820141100402e070b60901c0c83c030100386401c4841d00c9218407200485a03040c054000e505008040c60b8015801101c1620351603e41d1302000340c0e58440f40701d030244003201c0781589240e00039405032820941c0b00c0240d0303a4900d05241c8460003035000b4010f00020a40007800490020300c02c6000d89038070903d05000c1886660307240c41e9444950000380901e4108030002c200c0d040081d03291f90301c000040c0018004151034502840002e42000f180d200703001d00c18020101c0d084644c4480a0380c44035402d07000300005903a0341040030000030701c0c8030382909114103608000410310a031ba07001030f604080d20055a200103c0044182d211802d80c86100030703082c0011a008001e00042c50080ca0300700510090080e941000440c580035403a424004440042d0700410100da1906905828 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 184515017 1250 184513767 184513781
    0x10020f06010906080c04110f04060507061b050306040e0f070608040507170307030f0203120f0f01171015090608060f010902131412010e07080c040203010f180603060f060504 76
    0x5442d052181c607041140040e41c0340e40c0c0d006520301c41d0703403a480d00000690320081210b0015130f07200ca000307a5480e1603e40182c251351004004590306031409000c00004200100030000300d038010741c1c2e498039540300e00c42004050500c0d0380302000507010701c40341e08015040c00c01101000300080d481c0c0d400300b071034541031483c20300c2c0103584075542aa0383d0044070754a4001c080200d1b81440c0d4103080504a000c0e44100c101e185000b01c0481d2041c10501038148551541c1c11000d5901c5480c0007141d030107480ea203c006d030441001080d807910b540e5a0005500c40141422608200f039001d03c0d04054841c020b54403c10344082da240384e44405225044042408a003100c02500319024001254056103020402200d00400044900c13800c6c00c000d0107080c002c18a075881c0a500c0040703004a40007400f030100b2588180b51500010321906480d0b20941e840524582018001c0ea4101c0b26140d880d205281d20303100641078980d40b41601c030420789a4552020001881c10700c110b02c00d03e10440c50000e819410306003808101e802d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 184516267 1250 184515017 184515029
    0xf090e0c03070b0f1305030a030504030203061501120b040f0c050408070f06120e01020d11090f151e07052e02070c060f0e061207080c040e0705160210020f0601 70
    0x4540c0b0180049003100c1c1c2152100414512804da03a4000305890318400c400030381081d41d041c003540003064149075000b17000d0016079008030280c4074162610103c21000c1c001060074039011544c01c0d40003016801155004008208001d0000300c0d4100c5005242001c8500c1c131035480d030110f000807405020f40341c81003103c500609599400718403c141440c402038020030010440c0f4102039110301c49010340d00d200f034040d200410903410b800d200748030311081d2512840d00310214681c01101d6462420100d46803c80c81072a811418202903490300344400203080b80e000f0801c0480441074010803184000034410000b07441c200803101e24142c03075854114408900c0240851400c55481e00501a05010415845d4040116846c6080c22003a0303500d034820545028100c042e203281d01502c0400c1039010070300d15412940c40750104d0368803c41d0395994103020008501460080b4150a103403100016034a42c050b00c02442d010840302450168604180c1c0051882d0382440078a20060f00161801c2040703580400505001d072107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 184517517 1250 184516267 184516273
    0x6090f0c040504141e010e0d1707170f04020f0105030601050909040203120a0806040f06080a060906021b15180c010507140102030c1309150905100f090e0c03 69
    0x8054058a9403509940803003445650748001240c10402800da0f400e240b2506001520030a0078803100c410200000840c01000c5035081c222040840440401c001d550301d60161508020020900300c400814500104940c0034400f1007044202c03003600044075140300e00010380c0010940d1500d032040c0983c810411714210305008043c401c2c000160382140039115101425a1120025034440c000030386002d0b0740366414007184038002040c2400e030394080d5010b4801c5506a8062144004010080f03040b80e50034800c45500d42c0140c0000170002d0066044a4440c90040001500300503900200c48908007203404011102d0340b00d4488201c1e000300c4000d00c941d203d000d1070803c160020b20b00403515141c04190303c40078104407000640c403040003081c42c860140c104100c00215100d04e0b002422500941c45805450401a221000028a45024010402402d81c00074801f07507454035000301d103405007a02410000000d006450f001c21214010400036006204000c03000c1200c03200500b00c14144885a038226000350 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 184518767 1250 184517517 184517533
    0x1061e0f03030e09040302010603020907020307050c030f1c110d032f03061c0b0403080601120203150d030c141f05060d021908070f030308070e01020601170f031204050609 75
    0x280d005030242c2060f5000380c800329a0740c1c0d25481c0803401440b0581009500c0b19121061040282e40000542a0503100b5003c6544400035841090703503984d1140e802500d1680503280f4120300c2e000e8203e4a000089090912031490b680e105940350404006e00c01e0080002e507649500701d03591003003003861048159001c01d07540741d02162403003003282440001c0a040c0220207001d04d10130240c92201a4440c00d503000b450f2080d03942014039008203140c1c1c040d2009800038614091948050501c0d2088a001e0302503880c02401c040148000d2002c0d101c80d01c001034062181000c620008110290b40919400f441d100280040000122003a80d84402c0f007400e001c03503e4a440b00b080140e4548035103801d24250111490700c40051415804e2500750003513088040380b80221107000a074184195103003400e6a10949619280e503544c41e0080b9601e10080046600503801100100540d16030496040c13810786409003079411300e41c80700310001d00d5684458542c07061f52000d8000c000503c40140840c50300040e140010b0b050038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 184520017 1250 184518767 184518773
    0xf0a05010c140712030218060c0a03081e04030804020d02270703060303051806090a0803071104020a0e130609141603050c0307120f060b0c011a130f0e01061e0f03 71
    0x7508055040003810346c0010600e5080d10011418906c1c2c80b0020000c0ea66280450340c03840d11543ca40008501045104012032044d0700c401001c2c001d0b403001c0164580705547c1316202214501c1c4054001d9070401041c0d031459002da118501c031400c04004801656180704485a103505190900510504c205131422a0030320000b540b210450740300849400750b800d10f4415000014051340301d182259540070060810000343c10501002400500740030f0480d01c0743c440380c16014442a8800d84207000300040c2841070694442c0350400d008080841091400528983c4030081d01c2d00303c1e424900340450502c40f800400041d600f4190b940108007145107014042800d143e02d4a900600000c1d140b0018081d07080e841d0f400101c225400301c81c0e80c1014020502c001ca6644045030065445202000c2a550134030360000f04e904901d5a402e01d540202a1003100501c4503440103a00030408101d41001c59031320f030079007400456030901604000d8260355450071180c0d001140410103604280d03200c1c10003001a00810804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 184521267 1250 184520017 184520033
    0xf0c030619051008010912020111030f0601210c0c050c12070b0d0216060c08090d02070512070503070e0105091605040306090302100504140115050f10020f0a05010c1407 74
    0x81c0c001c0c58401003110385440c2990068182c0702d401120440d03203814020020710640b2022001c4001d950b40080040e00501080b62116200c121108007040f200c100200c4c505521400203000e2000408a000108052440382c2800f9540c16030104400112110401e000b480b0007400103103204223084410000701c3c6102d003651a1a45018825120b2408000c100700d0400340050301120107605510b8081c0c880d0140354a44500108042e000c54400600074000042c0055000030703c20091044a800500401b0b14040c200302444100280030215401154000151a207040045601800101d03607c0e45841d810442804040c0d40c1c0240240300e48141c40602d8102c2503000030856003942e8108501042e413102c01c0c102a031030040d0001c01100b01500d413004010921040501c0e16901b03802041c003d02c03224520407040d8440d8540ca018840e4480f9070016007254610389107002c1c50b103102d2180103650789080c5c2104224104022031b40700350350780d945605d00c290466621445403a454202c200c440313400c2000c5903c41c191 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 184522517 1250 184521267 184521301
    0x14040b040204050408210109061409040b0a140103060203040203122106041b030605150405010203042c0405060412080403050702151b01060e060a0302060f090a0b0c0f0c0306 76
    0xc042c640d5440440e0a004020085900c02200f055003005850301000071701e02c0c0104248941060345190810100d00368807c030034840c45141c4010074003205c0c3c3d221921000303610318010304a0035009554060b0400c6d40c00030030300603500a500800740140c40b4a014010300d8180b040000c054804074034100f000c0f4440020710502e000e107050006628442c940d540b03001041c02407041e10b42c000d140d0300b1402905443c070b6078580c01480c02d441055403442d0f840b15003108114818011802260b0250304240002d00c0200c104100025141040c5916a641d07004840c00c020298141690140c0302500300c0710030041400941413444400d90076900e060500b5103841d0320300410500030004001d200d0b0040c2110703000200b101301d09a409542400040c00d072010080c039400343c000c10440c8140f070350601102002506500e031002e070850072a03801900d400e107030003055100d00f49180e12820307076a60700003005140400d4058901f030280883c00080c42c0140640001c9840f510702e8416640a0684264050f1007000119444050010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 184523767 1250 184522517 184522519
    0x170406020c01021209010b030f0313050d061808030709080303040308130507030c0b0720010c030c0f0b010b0c011503051b120f1e0a020307050d05011410080114040b0402 74
    0x40e10780c4440700055003e07100383d03c00228240301c510140300860030107600c1407217042c0d0101e0450304a20b0085101070385901076808280c200c2e10b0715440400c024284590b044003d030f442007000003150f90f070181d460003002490800c141d0f8101800b104107c540c1d070304a188440600203c10081d415840c055a00030140180184001c08642c005408601003000c2000004003650b4401103446140e610384442e0010368008010036a00d156130758288101510703200d07900c040000b4041e5200a41070b84580c5040d01c02103110703101250030446210003207000c0780180850340d020301100d2801c03540c0e4440c00c41109094480c4080728100d4003c080c501000040c20025001c440d0310403902035020712015903000504090640b81110031240250f01703580013400f6002c624074039407002540070400103162201070a0355655100c1c1000b50107502119082c40207250443c200c0070000d214200220700b1007040e588043d404601a01c2e0400ea00210540600c85d225003801074000c0100a4140507540d841e01e901e80402002c0068406 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 184525017 1250 184523767 184523771
    0x8010f1202130905011b14121f090f020d0e010b0a05041107050304030807030f020706051204140d0f030506030a02010c1106090612040201021c0c060f0209030708030309010507170406 80
    0x141d86042c140c0d08048845038100c1c0081041d5a01c900c0754004450300c0e800d800c2d0000d5034042401d001d410040b4240d803c49030801c140c0040716542e0046c0351440e503010040603281401070100c00034000c0d03654020780d20004801030001d038a502840f85100156130340342103851207590501c440d201e0962a2000410101c4404a8000c00c40a404c80c3c1100303000e12030104058101d0100041c04020700050100034001c084c840e503504807816000c514100d80311611805040d0004030200007020b038540c030807902d041e0400d0040d05e400006c1201028498903114884410f40c011030f4208100445103601071107031030b0380020140c3c0501581011640000c041141196004210381c045a2a4100315141d410594403540f4001d44401d40c1e0311015071804100e1001124202e0041c0b203410340c1a40f0003c035010908070141c0301ca848400c500f9420342d036910043e0107038000050450340d00f8810b44860340c1c0c0c01c00c002e000910364039024698a0401034403007400c0d5240180f8000900c04218024440e0070980065254015000f100c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 184526267 1250 184525017 184525039
    0x20109150e010c170c06011a04121113060314010509120901050c070807230402071e14060705040317040f0e0c070206030421030b06030610120e07050108010f1202 71
    0x8034104149040c80031011040402c45038280341d00084d1b403038182c40018280303001c1e0b128504e920007030622a5018110168448824a00015240034142800d04100403c1c503034441c41180c10100403191241c1c801da0f540102c0101103078455400b0b100c0d041e081440c41c0701600000950598154141c880d030b0442604004000403208101c034410322400000d0600101581c00c419039454580d03410140b03071104d1a851000e1010786000350b180510841d0900c1d90b1101000d170403480c001d4008505511200c6050350340041c0040c80100050703007444131600c80c0c1001e8a4103a00c460550905480300c031480c50050301026010003080c08000d150440b000d049818040f0010401d0f0303a820a03e402138084e402c40250042008018081044200840e04e0408814090140750781580a80101d0540d000c800035150040c104002240441c1442011280c40c40c015003000d0714000041205401141c83d4003400703044980180c0741c20700807503178802d0506004000065954901904040303858010342240a0001d20902c40c0b064 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 184527517 1250 184526267 184526273
    0xc0204150b07030215011208071e050d0e15040e10080118031202072102150406020304061104033c0b0a0506010302070b0c031e0a0603020109150e010c 66
    0x36010101084461003051039407084160190381155500b100540104812010829081000349040700c6c150481007602043c00d44a0000340c1c0e01c800010340740c5101080000201c4806540e00c6000544948000c103c881a0340100520a01402a10724400d00515403503800c0d205c000300540b425902c40c056405555105c041d0786c40f01d50f51060340288055400c011216500d1a82c0c5010383e130900380243c44032502c800c40e0000c4d0030b04a12603080000d040ea0340c0c80711000010302c04034003402c00c1d036640707401100d5034030392300c824060200041140c080303590a0b0000100700401065024503c41e500c50001218141819640c1d0b5401040b403804135148044103c08002110640b1400804031042c20801b01180e4281942800004c071034048404034400350400f40410025407180c42100c56094200428202d245c0320b001180c10715500207000a10b2965410b4942901208606519070161900d9000058803600d9031002600300c16580d1300c00340040c1140000c103141c145e0884a0209480790034a07005a100140346 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 184528767 1250 184527517 184527521
    0x90201120b0f0a14010f090e27150108010e03031303030504020a030b070507030201270f08090a1d010501030506062208030a0f110d050a0c06020408060a0b0909010b100c0204 76
    0x2c0c0307154800010344001840d55000340c0303443e090810a07640c1807020b841e13000c01500d0881c4648a0794616000d00400a445502001100102d0300a142401e003030f003881458005140034100c0400b401c90070b0f01240100010030092244c0243d403000000079508500c2d16501051272050f0f000d40260505454000050031503032600c03c040007440e44080b680724603040c80e410003002d6400c000300440156181c5409150340c02c500f41c9086124980c0c2100c829a138080d070307a546254000e402c40d0700300ca0405051089003020b0741e403144003038050321b16213403180046500c00c2c804540c0102c06900c03a034185440c0c01d05020868485a080f2030401400e0a144140a400340f684200c812889911102a0f40030204100200c01c0d80030450001005440d4ad440500520b41403055888880c0d040700c0c5408140204440341001c1d01440d40c0468003402050010700301a6990783c1c1070304110307040b0740c55480b040d59030101c20030a251080103107401c10700d100c000308120300340e40d004105201004038a000500002d251100c04654441d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 184530017 1250 184528767 184528789
    0xe250e0c031803030a02191d040f0f02040914070f0503011401050c0a120201060602060c030708090a0606030305071703062b02040f09020a0b0703020606040c0309050d020d080a090201120b 82
    0x500c085a44d00c0c9003c4546074000d401420035031400032005640d0100551180c034844c0380980d10141a0015070100c0c03001c00c8001c0c134010102c1e602c0c007501c0d801030340e08080c02440500300a0200c08400700700b0b0142014140b0811200512107401c5c400303a2988100070541c0141600e040d2070f0740c060101545000c03540141c3d60f038080c1040c401003610507104a50104690000d5030f194a9a41e80c0081c090b6030b4403039034203036152001102e49400b41082880001d03030350751040d80351503040001311080d50309408181d1103a000f07844142d0000e80124600082c1c4004004038022000c01110f80b0b00710a81c02c608180c03000a07900d000b1264600e52192101074046103c8541e0340c4620316040e4001d0040109241000500740605650304d800e902ca00588040014241606c40403640c40d41e9041c0d01a04085d65180c0810005100e103400580400d603840c0204400203c0400c03225481180301c0c0c00521596840c55001480d4400044c01d43c1100c41c100060140140d030420568260161118004514440340034040744181c882c1d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 184531267 1250 184530017 184530061
    0x2040902030a060510030e0a06050a0b030a08071a0105030c0409060f0608060f010b030618070c08041409060111151312090612140402010c050a060e250e0c03 69
    0x400014840b0401c203a0f803140e401c88000ba10300c007400c00003811094048455000c01c04016400401440e00080c20691041d035001c16214000a40380401c0ac0100745412502c81d011542d5640004030701c1c050009118500440d900d84040340321b00c07981800c0c0030946880b0400c056600407034455212a04105c5035412079203c99803901020031895a480c448691790b28420b48014544c101c003040081030760104e4100312413041c0d601403c00b0030b50103201d4070412084100100020200710301003402100243d0307204003c1004104098a6484010703651040221101380540703e103041c4003102051405a20010684038104150400c00c0c10050381c88444144071403442c2c0000900708410402078010301d940140f440c400362049542c41e00140b491007680101228810005403121001200c00a80190f220f104040700c2d80344680180d800c0b802565860300c059484580384034169030003412200d800002c4003d04540c0c80c0d042c0545800090b854a801b6514902025106600c002c0c80080050740d1070000304851150018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 184532374 1107 184531267 184531271
    0x130b0a05031308090402030a0b1c051b01030608010e1c110703020d060b030a050601150519080c120c18190b0d0e06090c0301050c120105010e04020409 66
    0x2002d488045a111808000700c0265480e1400618001d0400890200326182e440042001d4401442910700d501b240d00707040180820b034001a02d59039200c0c50210120b0706440340b00120b016051a4100741c40940c2001142d00d14454000f9101d1050403034501c83c903a032000c8104d400c84014600916002e050350081c84148058500401e8001040c2c2c07040c0d800040321745220010900304030500707106880d05e8100b01d0042120030401400c03020750303071242d11b880d900e400b04840c00429200700d07844085c0204049200040c42c24200c9004883d215200d207a003000c0640380c072408a201c40e17031016a140d0300d001c2600740315410743c1c14042ca035422007920b00e40003080c840d03042041c180e81d55000345061040c190740f0f41000d07041180381404800e0003900386001130140102e40030f0506094400140102c8043c160811441c05400c10500d221350544400b4603041c00f4106e0000009006401150000f0100c1c40c = true := by decide +kernel

theorem cover : BRFrame.Cov 184352517 184532374 := by
  have h0 := BRFrame.cov_init 184352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 184352517 ≤ n) (h2 : n < 184532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
