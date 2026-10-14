-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2361
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:50.129813+00:00
-- url     : https://prove2.me/submissions/c1fbf744-1635-4d52-9d97-7f16b5d3d76e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 424460431 ≤ n < 424640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 424461681 1250 424460431 424460441
    0x3030c0c130e0318013005040618030c030905040c0c03080a1d0a0c1d01290c0a0b0f010b0a030e0a060c05070510060b0f16020303181201060807061b0804030303 70
    0xc1404185c618511544c404200104810008014607030500301c6c0c0f420901b20f03006072a0140058074800c1d11802c5600d12000103084071050070b4420348500e8020340c06464090103664950341304511440c41c00521513500703500090303088201585403501d05507a94580c60640010080d410060303a540e0070740707580d414803842c00080a00606000e04000c001d1156500c404550003192040c445020140e0000100074480b807030300500ca11022a0070008003012a11400014280c0200403016080e034820b03032104040c010050b505540102040200d00010340c14004081602c0c4503440708402010307615848041c689070b060040054241e800002032040500600e4010480d070401e07081a90035003e46405c0c1080c6005074400c1200329115180034a052000c880c6807003650303030011101c0c0d4030741c0707100740022100580c0c040c0000c00c80408120762000d040c101d1002401903244540c00d00c0c4030641e2402e4000e0003941030002d00d2100f00c400301c1c03070042c111521400c440040e54130b58403c0100a04404240441010703016001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 424462931 1250 424461681 424461727
    0x40201120c052d0423130902091501080613110304050708060f011404050915090f010617060f040206040e0403030b01080a0c0906050a0c020a090c0e03030c0c130e03 72
    0x150b00b100f410740900c41d100ba0b01c021001081c4002c1c0803c0100800031200484206900003aa0070480c00701d00b0704085000c010031400c0e414000c2d03545110394011498030060094211300000707a03102c41c1503103050000e4014000988840d200f01401d42090010790044e81000651141c0344a099440782880e261150f991f4030180074a40c00ba000319000142e503828820303100ca04a800178030030818180401e50074440103160203040300e078160042c08211080c0c414a920098054074264005140b00c882d9415080d0854560781c000905414114125410031800014269000941401040c1d180d4869100059081c0301d95404083c17034003020410072041c99010341c01040401001e884968055880416401c01c59002c204400d000c0b032564601403042510500140c5020041741c18800d4440e6039503000180100083e52100211584030b8000302c80c035a500800c3d14281200a4004600f000140414992110340c881e42403401071100d100b0a030320341c400682024004009140903203680702d035950303c00c0340540580382d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 424464181 1250 424462931 424462957
    0xf060d0828081608150904050703050c01140d020c07050d0602090411040302180601050c1506210a0602070f12020d0225090207060e0d0f080f160503040201120c05 71
    0x941d00088034054078046114034801142060310070302e094400ea43c40034029113001c100c800e002405202d15260070380c0701801140910010540302d89107240043c03820035481040703070400011081e02d201c1404250b05680c0140c20704040541ca406030300d800c5501d401c0c0da541c896580150000390a070140440b0341e0080c21400c038150760622504612400c03d11030b030300c9988002500411143e00c01c0d04101e070081c440a4000c04140360542c0340420090005141c525501c4091603002c001c0402e000042c642102d01a0200820110b60004040110350302900c1e8075540e000904260340024400b0704102c0c101d0040509158002e0320090340040c42140250398980d403038001c001621825201340007802c4c04080c6a01c15844200011001c3c2d82010701034400307500030110031a01c460f2608040c5c40c040c44217020b00c041c0200c10f940d80480310329604000601d48203000c6d0040d004000d4004c2441f01c8c0e65070382c061400c00d42c0c50b6814896507903161440100c41e0001c8114410540518203010050781d01d03404001005404890a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 424465431 1250 424464181 424464247
    0x70f021f080a05011401080f1302190807080c0f0d030201060519090b010201050f0601210509160b1303030c080c07091b020102041401081008060907150201050f0f060d08 74
    0xa910705504000e0501e85d408500740310300080040450440c2070f5403010030580412044003440e0301140e62660b55184a829802c140c6500b80007040007000004006c28010005004881e22140404d20030011406003d00407018088a5400d26000750000c6005140c00f401041000c01c602e00340320b00d43d0689004076074209041c035000208646c41401080e0064403111001661600c1e102c005440e900a07142410328508600000005411500c0c810350340700d05480d80140c02c0701103400390349994202d016007021181280a02c22001c0c8040740507510741c00d8a070b150410700030303550303050802c01898051060301100a204481022842c0b4083d50080407040b2200b804c0c00d100600050001c0e800d0f400f4500030f0301c403038200840b240c0142d50701c40c65001d5007001c121100200c44544441e4140d08281040b034034051a03502c05002044400d6895960306000d090900c0204201e051644035006507900c082d0040101503034007004182d90343d640522400a4590249a4968070070b4854002c01c01e92001d101a1500000c80d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 424466681 1250 424465431 424465439
    0xc060c05031902130504050f010504050f0f0f0604061e0821030c09040e0d0f1209200a050d240b2101021306021609020f070f021f080a0501 61
    0x54000d81e40a00344151002080c0b55039002400025005080241c4442e621070f4800915034580780b08150096840216030a0f182d030400e028002a00d9020b80420422401d810401031529200b401e81504481403100c246d6239030f183c1c90001009000c9607045206420a080b030b00c01c03620613450010400321103000e415540d041c001e4079021114021b6070b004402c0c564004100242c40c1c0708000d0004c1c500458000c0c000a50f04080304811440c2000204c1c0080120300091940310b1400d4000101800c940e026038400e0140081c40e1fa910758007030039060301c070b0301d50300314806d94103440c943d580109503001c0c14020b82240d0000d601410400250290101c03004a100f5030360140c440d0014642c0621501410040d24030260401e5800080c0c841d00e80c014407110b580d56090014058440350005000000d15603075000b000c02d130041d080c2d04640c982459010281c1c82c0d10400c4166840c0410300705681c00e45030480a030030b180c4600741c0041640c41100c0780094020703245104001d68101e41000e419801591000c5007000103a8075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 424467931 1250 424466681 424466687
    0x203090c04110f030613111c0b0604060305060d0b0702070f05040902060f07080f040e010510021605210706030501031e0c0e06030a0204050703271509080c0d0c060c 72
    0x5001201c00500d18100411100000143d00954100c1130180140340141e0302c140c115030444991038102211194001002400c0360304000d80c0b0000445002400c201d840c40c40c00c0000d0203407061348116000d154903100056850b41c0c0b2500340d50000c5800111085013490619002902e80155001d6100c0103011000041203d0030544141011035034040c0c1080c3c901a80c020b24052076030841003003200e01117010030001010f41c8094000e40000c00e202080d40d03800754100b200b00704d8007104812000085500003c64805160312150650307080351b400f521143c0920214284250364150300d42880e800074171811310002400c5030b1560003141224000c840303400d090990100206041d500070f110160101101540c140718a202c8440c1c5590040340040464080c402c481d400b040035640304445690100341d6526407050b03044842142800c00c058a500640401605a030341e01e030f681149400410051540c0380201d8040114030b9045490441e0b0300c004031111500400d00082c02e40895880c12941e440c100b107103545c1140c4c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 424469181 1250 424467931 424467941
    0x13020904060203060a2903060a031502070204050f040f060c0c230d09030503040b0a1b051501091e0c03060e04380402010c020406090f060f0e040503070b27010203090c04 74
    0x24401811912001846106c02c0d1942000d030010b6405114000c00000007203102222800010a4a00c0942c4510301801003104941c40142040110031030f0303000f000000345804040b198030f03903848003000920900255044030766207035101c40100352250314103850015034020241c1c98038080c0c40e04c08941d0007042c8034008070342c5005288402403ca40c42030209000746089140501404c0c400c40c504508946507094002404e134001d40c030b0956494014902c0210540407a5103664094603443c2c40c1401402140e280805407a60a4407208665950318000e03145070034403a400c80030007405880d020501d1410f05040060b40c1c20b65105480102003011201d1448290303010b0091085d12010b0302105200f6a034940055804d00070341d0104a920075502c19021540000600c41c112507060f41007800201d1504010040303900356115040391100c18907100402c00021b000104541e640340d400321030b8014a449001505402c003017401c180c0844611900305800340d845055000d54440d4664104980c0c16025000078030080318 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 424470431 1250 424469181 424469219
    0x40b03010305070815070e031912081617130507150f0207030b060108060307030605090c01140c0705190801060308071208060306131103010903170705180913020904060203060a 77
    0x1701d031000050700719008109039202404041d0a45c0c0740290f2010140300700d40075684045803588140c8051194a0340d205458591044550f40e5500c02038103940c101a002d1254004034459590044001407270010401d40c081c940039501404039440103032254440590325041031409400115001004405e003440040d582084981015aa24083d12648011560440d00400054052103120310020004400c3d2141c036114010300e8010f08810103d00000418100fa50605402c5030441400038006200d8086015000c4a00481d145071014900707181d43c07440b480703c1d64001d8819502c2c0c00000028406544010040c0c00d1151003c2c009610194070162200f100c1074581c113030140c0c40b001c00103020407400042d210340c0700d0081c00586401098040001e094401700d20301140021203090201f07404000e07050481d82c00c038185041032414096206108909481d0319030585100d443d00c040440c80040354000700e50340c081c1d00035050006500c0d042c100b9502951007524141d000d07104400d00000d016400b480243c240d2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 424471681 1250 424470431 424470463
    0x90e070c0f020f1206090f0c091504090f051b130203091b060c0a150608210a09260705060711120c03060106020d09150f031a06040b030103050708 64
    0x40000c0d40900c150f6810001166400003189050b90300e01c0c0d1390800a162203000c612000309020141c1080c9503044c002007280c3c02e801558003600348004521065910b0a4402e4255800254200345051070130030302c240e180d030281c014007410050b000181a60346c8008804a42592010565205044400200d1004032140101c541242d928050581004224034060680041110341420250701c4028180707a0380c0041185c080361020140600c030382047c0540b1000b450a032021701540f5208203c0030490402c11034024504807800905202624050002140074100c1e0b141c00700c5441007042d400c0c03694191440ba1020062241d603500150710314200045070380315a03200302209004080d220501051148440250f4134500860907440d0380d580b410000c01d402000158001c016051102c4405001c912003070300f20200d00c117524191140229000001d00324222010704e00000d110141d041e1100c50108603961b01c0e17038005000100003c4406540d03000d541038030301032000c0c0c1e80042d03552542a81e41e0004035000b0101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 424472931 1250 424471681 424471703
    0x30011a0307030b010e06040602060906070f091401090f0b03090c0f0303071506030b040b15030105060108010510110706050d0b0901060c020d05070b121509060915010309050d090e070c 80
    0x50302c2908030440c01d0308107041c910108100c035030000d10950000d400800042e4442c0007000708085040021a401c140c007801d00360241c03c12003200525071201d41c090040064204c0da1422210391103880424014035111102640b02c94590648054941c0256aa030310a4480c03410716114603e00720b202400804402001149090155515601761000d070308022485d0f199102400000300349401e088501c0ba42c0700710380070185031901460f0000300f03072801c10126009a16040800c041039130081041c0b419214201c0300d10a0040310450111030341422075510007101d00584100180103030b08071018007500702000e0024042413505200388049488244600f070001900c444404c070150509141c0000c00c0c030b0084060f5500a41c4a484034030241d0700c060207405030713030104404020fa010740b00194684c24050856444c1c0c00c50806000050295001070000c86c146a0b282540c2007603680298421484c2591000564800d160030300d0000c0c20101c0580f040e0074201c03a566001440543c402c0323440400312035000c03a44520f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 424474181 1250 424472931 424472941
    0x103060504231b01050c010501060201360b060607050a0b1902120a0b060409050709030b070c110f0d0b31050d081308030a06030302100e0316030530011a03 68
    0x2910f0a43e00d116241846000c10421407101402e000c0c00e13020342000d800203e91a8940c120040c40041561041c00c00305607803030309403c48000e440021106654005504100c10348520000542034803c2c00c00040c000d00c1403014800402904201c22803203402c9020004044142d18a031120691140e441c07021040409d0700009288040f0550200c040d02c04043c0641c3d060944454845046640030743c1c00101141d81d000c0c0c08c200f00034141c2400f5600c111240740c008801141960740040300e4101c20a01441000140303009811074075480040c104460f00003404030107074100402e49031180251050341c100880d6142000814820313060301c00e003050a0740080284003100035200c003103c201001030104156944404516404540c04802660080c1004000040d8903441d516029142140003503001e0429400c1020703202110001205850503008106000c48034071840e85022903c032310690480e198071140050300f0095000c00d042c0000045092194002145e9803a0a91840012091078461007200e031b04200140f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 424475431 1250 424474181 424474213
    0x420030705060c0106080f2a1e03120a0c0501200316021c1106090105010b0403110f190603180b04060b01030b0a090b03010609150b1b06010306050423 66
    0x21103c0b008000081558aa88906050104e14410082d4603405210349007850012a10800100040345291403403070492540402c02c429000003145417101e0218080200c0b54500380030001e4002031820f43c2664690903100f0151400703140590581d003070761a0195150046071954003c20850300c5142c00141075645800c40c47d0040100051900214028040c0d18100b03102130306810f010303064043d00d51100760b02c80f0000c6985400001819599240c0c101401040101440341c01c403415282c000c440d010340d401508020130303464411425a240c0140844c000142d40d054569901820b03504107a405101da0b4207035500d1031000441c80c802c06084081c520012800040041c4c3c40400340c480b0605012400c80c1100001912070314456000158290716600c0b100e40c6440c01b88108000b070714108100b0080d140c1d0b60b8840818420913801480d0304a540013580300700c0d80814010340280300052a0480d404c960710391a080c00985400d84044840302d0f585096518401101c10f4107000d010f14840091a011016400e00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 424476681 1250 424475431 424475437
    0xa050303011e031a040b0a06060f050f0403020a03030e1311030f06030a021503090f07030c050603040201090e01080115090b0f1e0915100f3212042003070506 69
    0x1e108001c03068200040003484079203804500d18101e01c2d1356003003481c1505203081400c1c0010011742c0e0951400368140705103074010030480301d01c20300d07071601c1c035154000d401c0980341034411900040c5d8400081c0c200001090303880a0420134884082d03800510101d2207040a4003aa11540d80515050304284001030502c040400f50541c00300c00142251a201c0a5401090781c5080c00c0d80704603034561000007080300c03992040102c00d040407400801003044a04c0d50b100c140104a0038040e040c07003154000702290541e8401c0341d5402c0034059001c5d01d030466503561244c49008214a0860f0140308500c1c0100103003201c00c92107800d80402d00500305034060010401080022495105031242840c00440302e410303035856807680c192040d2a00b40000a8400030a01005010103a4107a4402001240e040203101144c0c003440c10400b81040703003410040c9120103111070102140c000c1d11000b1b21000400c64080d00f401604040b402603001c0c014032a203200110454131190442600099015404490100081d040183c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 424477931 1250 424476681 424476719
    0x90b0304020402160302060619030b0c0714070801021201150e0907030f0903090906170a0303111b01020a0f0305090c010e0612010e0103330c0207031502040303110a05030301 76
    0x40c0303010a0a41c030703000c40c1d401d100010b81c0103030b00010070000142080016110b403180d025210b10740e5946152f480564404000f0b098030103258001c039242c2e00300300c0340354809500c128007541031b03d40142c1c880c1d45941c000d400101c8804070641e00c00c4000168442e40a4105070b2180315aa5480c08045054061140303d010142201e01011741d51030200000c0d00561203104260381c820341e01d4084035858810700d00159492500a0a6040002c540e01c540c076600c00141070805650504000c900010000f03d01c1030b103401202c018241c41400c410b59240c29038410350040401d46410b40b01c501000d56001c0e0210100d800489600c00030ba40318640c2ca8010f0341c0580d10080890400400303261901d0042e42902101403170a900c400c40c3d04051000500801c800d08034411544500c1107045000e1140790a0300f001544003c0c0c0404040954a01100d000725100740800800342d41c000350310601d80300012241c03100030f52103440305a000880e0f00c00000d25041c0c0110354802065000340042d030a513403e00703e2003e448500d280c0c1e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 424479181 1250 424477931 424477939
    0xc0f02030f0102030a090b01080c010f0f0e06030703090515060a06030b033406020105090601052710080706050f0a05091c0b01090b0303130608091f0c09060807090b030402 75
    0x240e9124021003400150300c01c284030701000c1004e111a15004d07401010681049509d6000840300303103a56640845031200e454030030300d0410205044c501e0259412030900c22610b402c410000108110b42d50541c112220380c80c41001240c6100c046414660a02102030301c0c002e5002841c60020800188039800603101c503200101600c04800041c880324601e18a820510070001e1207900044041e803504240c2c4800502c2c150001b0700035454114002034440c0c0f030501400e8410b40c07802d00394141820650151051010350325400403031710b080c24455020340302410b101c2c2501e50322070703800c011540ca849241a200b42c101d00690b1581002e030503100c207944541001501582090301d0603a500d581c0c044001c071090000c2d01641d00c2227144d50500d000203080d50580c207241c6d8001e03481040380c0000e840343c402c0b0701c40c1140c0c00d42c6408001600c9140c1c40074240082410061101c4801c065010b4841c4165407020075185115250201402e42c0d800c016210318034121014004140d00040030420494000300840d48030b0300c024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 424480431 1250 424479181 424479193
    0x303050c0c03070f0302211608040801020a021501050a0614091f03020910030524040e010c020606090711070b030a060f060e01030e070b16080412080a021c0c0f0203 72
    0x1920091854210f16000d55900c909911410141038040c000c02800c07404030441c0ea0846402101400c0c3c181c4201402042007450501c00d00d014440b085056801601c9610000d5684000210000390b40e01c64103020403210581d0705000040c145451400c40f01241c0d031a440398800299002480e541c25008108141c0e0805100c069601e0f5020700010081d0104015490060b100c5d504041840714540d484c1040106152508007402a503681ca00a400d01c401e0b40118204149584176010402911015074183c6156003001c0380b007682d05802007040c920414040d80e1810071950742d441c00b11103441215402102d030743c003e46000d21654075404011a800301c601c0d1030100c1c1030f03540e4001039020604154001e40004018040c402440e6034180140302c84a420a0700814840c0e0401414154038407510000300742d0410451000c404001400e410384008000c440070410f0300a0349410516011f910103c03403400140911018040b40f041c01340d4500c1414407203035440803966002c0356a81e280301400c02c00140d80c10306c600e03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 424481681 1250 424480431 424480447
    0xf03010908040f030303060501050a051204030e0405090706110a0f02010c03050705030a050d181e140d02070509070c051b0627010f0504120b061305090102120603010e07030303050c 79
    0x10100520042541ca454000100c0c138500f801000c651080e0803a0f810807404001c10b035107007039104c410343c3c10025620f500c81e121912589020755040c284950b02540003808e10040110b1704034041409400c54600d81c031144040c0c44801611901e81c100701c04000d001040f01d0440e000035510441c580c2580c81c1c0300e03042917403a00d9100c0c0c45880c90360300701f000d440d00010800200c200d65180c0c280101d038400750118480000c600c1c5140d03120406062582e2140e481e0151498445060050103050a000d21072414141c1d40d01c8548101d0094441500f4000d9601454903030012950542c82050840311594000019000c6606d10072008603423211130445245d03005800340145100801c0560358040180d00c140b440c0d281c00400c6500160010082c001090240001440100b1a40861050303115505074000024009581c414001894500c003486020900070303c1d2408201c80c1040542c01044410780380050340f540e5603603500406090304e0290190201513008002c080000034000cad08a02e0308541440c1c1c565041c0303046 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 424482931 1250 424481681 424481693
    0x70b030907060e100206150a09020409020301050f0105070b1605071401061707060503191404060b0112060506120601030612080706050a2a090b0304030c151a0f030109 73
    0x8150340c60319240d002248100b14182e000054280030319000c1c1c0d940d44000c00065000b030b4891a00424420198a80501c0c000302640c60011800250929550440d1501e454610110080d0001d00800e40624074410030085250700400660f11090351141da290803581e41c1103260300642007000c4904060000500146c000150101c8603d0034403103e0000000d1070918007030010740310b04083e20340321080d41c000385801e0007059807000450b64001c81d10000d40c0200002185074030300401494000780000c40c0081c05000402ca100e0308440300200d000da07030b10b40c03007004078030401c0c4100c0b111803280c0c540c484420400c3d04491810026456448401418006216642c2d1031541c41198150700d4202c40c090f0000400d0820400e40c0d124180d0082c03403420007003202810402820024411142c84104288441c4419081e852711a4190304040c03c9401e108680368106407401030140603552070100d9107200c0d01c000da00403000441c800c03120340000f2038000b000300d5200c05c0240303c20809080c4545401d5500c03607a070f62000c244 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 424484181 1250 424482931 424482937
    0x90a0c03030c151806050714070624030305130602010c05032802030702030c1204060f050c01021908220803061908032b0e0a020411090301060b1c05010f09090302070b 73
    0x44e91000380680002614024007201d50081000c0244811110760002039050700c016a0300b42640700d000001d403140421002209020526005008040321304004002c150340715001d04441d01046041220b4640c40d01016400d0ba01c1c0e0f580040f002400c1400024100f0343e600511b100b0000c0e0240f00041d60348900d10700203041c1c1c3e1007262070b4000369200088540c001d103003c0059121012282c00180e04050900c5d00013403070b811103180e5000c108017000c118240d5440e002c0d412104250000b440c0c0c0d17170004c0b40c551805026484101c80f08002d0f445020000b0728090003803100c1429159204042074599500c120030404201d91030a08565403a181e8000480c00035020001020403880030141e1460101400548408105013072002074401814681d42215160340002c5103442e4680c110f40105c1c40200e013510b024403500484854030ba02d5030800400160303d413079000060190900c0c0180f21120304456441c40717000d40d2801c1c8905050a00c507002c0400210b020307503101d408243e01ca44140c80d403c0d60365a0a0582c0380d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 424485431 1250 424484181 424484201
    0x100e0a0f0b280e0c03060105030702030c060106080709060c0c0612150b070204271106070f1a1e0c0a0c051b0f100e120f160e090a0c03030c15 62
    0xc84201810500000b50025850080c0b01c001006443d5103011450054140409000c05040c40008008520254003c2c42503486408441d412a200f56a48900042003070005a41c0000456003c1e0004210548140740c02050150040400c20301e42e841c210044901c0d0034480011086240d0b2420b190700280c05d0422480010500c9415050b11200c6078010030046074100200c4070000d40b500f240040d9426580b4480042e600c0e0450980942c18070101c0c04500c16100d0f030400180741c9040902c0e05000c005618040c0c11101050040c0518695504610301d150500300e8440b6801180303040d00014083c01c810070052184991a01d81301e25a8003e95961f140f0700a00740008803606284c110134020141851044110400d50440742030416030701214018012281c001c44560007101201025904c2d140d0400c0000c51708642041252401d0018840c8108441038600071480403580041c0812020f6070005200c4580c0d070b808c4081c8900b510702d95602500e540074500c0c0c04403600100505005242c96203032042d00010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 424486681 1250 424485431 424485469
    0x31404080315010509030a031107050f030712150e0307031121070501150e1b0909060613031e0302070f0e011203020106150905030d0c080f07020d02040203070f08100e0a0f0b 76
    0x1c0d0900b27646605100b81c94001600480001007000c040b0713900050b14004071961458a41e1800009040901c0180004402c00714014100401120080c400000a08446003c4e5844084070380c0b10b10b181c1a21003e15111588462040f64440315180341d092000b0a4030520407000060f00c3d03801c111508058003615400a42d100c0d100004004a00928243c856140881180d2940c9824000c0340066400100605454001e01003c00d1048500070020751140256400c101c20041e94100e804001c20841c405900450042c0942c503c0001c0c51600c1041d100103880d100038465003260301707000703440d4140c4016403c141c1c11503403a01d00c002540010001928106101503032010401070905c41494070b010310145405003004226520320021034000700a80e02c0d00d1010000b0a035642c031003030002070304442c1c6c1c0e00d602950092001007401000b542014048012003400e40b1840c1c082c1d0b0f50514500503a0782e0718417902c0854006c41000035080c0300c69510500f5210b002400020702500020b001c02c1c0680000c440c85288 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 424487931 1250 424486681 424486697
    0x806100f090b01051b0a031211040b0306031906020301091a0a0905060d0c0303020303060901140a0b0901020a051b09010608070e010e010309080a080a050108030a1d18040f03031404080315010509030a03 88
    0x915070b02071596900c1ca05123500034454201c605050b00324603c02c6220b400b00036100403001c00c000380d03024082d41e64525040380315081e99a03000c1c24600d000754001e00c070740911903140640d0000758244c480340034000351390300401e4420b0f160300e040005405440024801540080f00e06d40c01c0b800107820202000156000c0d42c010f54492400070240507110300103800003424004a07807450b00b032507036411141000b902c05081400d81c035a03140e680140d103003c6006034028928087d585160140304d07043d132050300d10440c08894440850f40d03103a600355480c01c42580c80c01e0000300704901d003c8095029041060a025040c500003a05001948034005150030690620000440030070a00043d0300841c02070303501400d12b69010303520f49901150050a815501174050386e06408000810740749503107049548124a6402140420b03610709850031000080700500c00700c002c00c2c50484042c44001000442030b10031540305003280d1442e01c0301c0c0380c10220749140284643c100310f000c00c04001c01d0f45041c8080d804461094030b400340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 424489181 1250 424487931 424487933
    0x80403120c020f04021204030c03020f030c0f070621020310050d060207050c09130b0c1b030d140601090302040e0a0519050f0d08070f0909060b03010806100f090b01051b0a 75
    0x2510f550b025115501c00c50052000509400c40900055003040e4141010b514400c9280360a074180b50061214840030b000106044803c940007280604c00d017046402911002030700d408003a1a680454480c1d904c3c4844508482c03c0141c0141e4021034024101c040c2c0c8900760388e610400901c80d5000c1000807201c158010078010200403080000c500a1001210b11007074a145c03030300950040908415000c0c1550100902081c0300003034503811141080420040114062025116181d4039800035102e200394038900340d02c100d030704049031803072501030b8205039195507005107107070204405800c001b9002c1c0440c1c0108540130000550130450403c0c1a007403040d94984040a81c2010740c1400038212461707505400620120f107001d0350181402d0750142482c100b241c524446d03d4030440f400704403904409174191500ca00840e80301e110001545c12102000115809680e0700084003842c0c0741130784581e00c03580c0b80d40032081c0100340d100d81050101880602d03003a824a404426524100030030b803179406006800c140c080310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 424490431 1250 424489181 424489189
    0x80a09050a1104180503180402091903020a33030e1b0a0501030203130b1b04081c02030a120231060e010f020c010e1f0e01030507030b0d020904080403120c02 69
    0x10141c07080400f111802052511170343d489104110300c40c004040303440c03400600e60362580d040d41e600030170262402d01d4850050010084050b1907010692040000d00c50014a80001d400030140510045d400c01032452072007042428808480342007039041c03540300e500c107003081c050400c10310b40c04550180f503100c02d800300034041c861041d00c2c58014604260042041201400740c03d9064002e081c0c3c4803550000700d54030503042d11559405495949800600018001208100002c1d4004036481010030480002d0004c0402e0381d4911681c0c0407800440d00072492003801d06803039400b03000c0714041202003140c94820801c612a005026448403c1c078820340c0081446050ba00011081c6442c40a0030040c40c1c0c0010b402d000307541c034508041c410b03042100360308000c103981d107804c4600d881e070022b010034504074000401c80240c108013100c9440da001a1504000802c0584240a50404414007130148982c120040d000e00906a000520039a10b010042000100054083c0c1e980c00c0d60680c0c40c0c0d00c0c1144c0039020701c104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 424491681 1250 424490431 424490441
    0x100902030f062e0b131e0b040e090f061509070c020102060f040503040b0708180d020d0605220807050609061b0313050d08010305060a02041a09030f0607090f1502030a080a09050a1104 80
    0x484020010303030000c2c411072207001f085030241d4800018914403035548606441c0390449002160b003030340c040c1009212a10900c0024082c3d2350400b01c5094800381c2d228542203851545840e03000c1d00691200c00400da001481c00345850f0454000e0083e01e24160b02c3e2401e00d810307540066000c4410207000104100c4154052440c00c48200b01111410f25aa8160700040d26203500741074054582070303850002c42e0083c2c041030b290490a00580851034148007442c18800415003040c10180c0d1140505400901031410210b0b05074450036503030b18405e6420b28141707000300043e00000c00c4664258124040d031030100c0c2040120f644520041d990742001076041d03140c080e051840c0034044889050043c0028408200009014401c510182c0070b490303100d07203040e030001e898005035400704407075409408107009450758402c18800c141c1c0c540502c06c441059a0f90f01c000fa4500343d4400a100580013484040400c602c1810383c02d804c0242d489020410192948409041c050404001c40b90303e607240b24450001e06041c041c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 424492931 1250 424491681 424491719
    0xf05070e030f0606030c130605190302040e0d050a0513030f061d0609070308180904120e090606160c08010f050114030f060720100902030f062e0b13 65
    0x502000e01348480401d0759040340c0160b0b81d10801e044601284220301d29032218000b014010201c82c3c00085482c4014022103c9000981c003e40c1895000281d01c2c10002e02c08508903807943c1c1382481d08098640454540e00219103098503440704c2c41000021900103006014824064803000400030511014209061281c400301c0c038840c0c00c07007070400c121750201040f604100c0742c000345030a948a110b14540364403031075840300565100d00010180000c1c045c421030307075081c00042c41d101c85e01c40300103d00070031080000440301c0d1944100c04001c400c0c2540c000031410420343e44901074000c1a29122030104e400d5840020b68414a50344d610300400c604454603005003400c0501b58060003103c81d42481d0349032200e000801c40c5c02030000000b41020152550003420300310100c2e02060300d00026482c04544098021102c1c284c0c403920442e0500100b0307c2d004510309000d800d21943c5408024414001500c00010070b800c0742c210311f00c7c01100000d48104000050055100405240001c00d0030001071201202c04808 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 424494181 1250 424492931 424492933
    0x18030102211b09010f030e060a270206030a0c111509150702150907050a06170f190b04090b01030501140709140105130b0a0c1e0b0103030f030f05070e030f 68
    0x414a0b44000030b4000300da020302c100780b910b40c640103044c00040d0003074900421602094443c0c1000c20a24540c42d502c082520f0092200880ca03501c125440100d00b0054404041d500007020000f041010391940d0101e07401c64450700703210546800814145044c240c0c1d03040343c2d600e031003181010805241c1c001d1001180c00c1d0740c3c0c4440d500c0e071410002d10003950b034240449980004082100450030300d260411502c00204001000c01e5502902d40c0d07401000c03440f03071507030a00b1210815404600800d51a05e4114441c0e401c05980c4883c07001c00520308009020300500c0030b40c101d691841030380041440004043e01840c040d20020411815a6400b00458200284603074104150103d080c8407080c140c1407400394000c02440d14a8076459511a0080c10003520350001003102d41c002813000005400c003c00141550048080c0c4004552095150b05c414098030001008403400400510000b400b0700d050b0315403003100f4600000c51310140b1002b1800c0341c5d8281c40203004034142a00d1905680780800941d4042240340f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 424495431 1250 424494181 424494211
    0x4061205011d0c0703020a0503040807080111041d130f0c06020d030e0d1d090a0b15070201140d0e010510170c03210c010203100f090515061803010221 66
    0x8040c003000c881c0589201003c4100084450034540f0070000340c000385400030305490fa216035500c2055501d100c944581c0071b65500301070fa105042043c040c260703821100342c900c248600c070340c03404650341607134200404082001c407101d050040850700c030345600e0040034407034485a01114140030b0060b03c4c1c1590380d0310504c20582071030f14220190344040ba008203d001c150402346001c9241c000c48801e084111001c698000e80001c04114040da41500510300c0410140ca1803402e1001941c105007143c0305881003e4046007580391145140d071081001880c8106c4003120000300100640000340c25a04262400c5294070b03103015080c80024292480262410740d81402031440210050209441e8402c0e07822400e81c2c2002076410001e5100b00303c0c1210790720500100215940e2030040f030136265060741405140c0081c1018000880d81d81014410a406921001d01488690f4501e400700405907004003203041c440c4102d001d00c02d0998400b4000303414160b00b07024920f54030001168414441400003000205c0400ca54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 424496681 1250 424495431 424495469
    0x10606090b18120a0506130b07051608030c0403140132040b0403020c06160308071416023f03041d1005182401020c010507050f030406120501 62
    0x68554081d001070390003803c0182541145400c0c240d0038030020745680900030400550305c0b08417115030043c038411605003920761110201124640903000ca9042060410780101d40880c10381009954031411803040140fa10b5244e50741c500d090000020981203d03912810344028201d031056030031001002e03501481502605440d102c610307a060240c0701510300b18490003c942454424001441d80c100701511940e80d136800c48007a50503090080d1416000030381010b02042045104a10b04c038a8002c030721101d9401e01d079090716400711a6482440483e44003403d0030b5001341403610700d46080108240d560400f6041403101011002c06922000c0078150f98104001c240100030001030001c0d4010066000442c081d0307180d481c9400b0140382074100a5100788205661207e6806024400d84035010250900035829400303251781c030411164100c00c03405030704242d031400440e5200f1000351411901038411280002c0c01c00407964190b510603005100004d0b007c07a4028001c8000f4020301d40141240a0007990a03816 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 424497931 1250 424496681 424496707
    0x50a020315060c03090a030b010609090b0d1b030b0108010b0103050a0207260903010f0b0f0d020906011115070503090d1407020108130501061e0906053f010606090b 72
    0x5403481c2980b1800010450b0201c501041040d19040100908041c18890301c0e8286954190700c24403070480041d86000011a0342d4056008403030b069a8040d00d0301c3c206503599900c062003201da070b51991035844002d56000021a0103620020b00901c151800068010500b4000405a540040c02c00c4130050042200c00c5c0001d0721440d090161800102c0c8000748a24000001684c0c4e200301c5150b141d0540c203250415201f0040d039442a006044112040c209083c1500c051001148840c003002e54845220800030340c965000d050341c2c290008800003501c2454884c20100303581c5c400150303070000015801004104041904002c1b030300d508021802c06080070b0558144a000d42c4c4240300c0000d040014600201d41e103500d034a12002d40c0198000c000f800000d03110031812400a04400343c07515402d06041c000260003105120340001d0340c40141201ca01141d124101d20b804080e07030440d0f9224256122007032a05442c004015990700920107002040240c580180140300e00035a0f082994015000c0102c1c00031888 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 424499181 1250 424497931 424497961
    0x150501021c050a0c06061401171e130f2303070b0a1a0924040b0901030615030b04050619020a050a030c0201110d0603050f0114070305040204060522050a0203 69
    0x8507902d03099035104000b001c12120440000b80013003545090440c0401e0f01d500c02c041c0d10350380340000c0e41c0e0a40b900c03140d91001000c13024145d4030b022000f81c011180d01420086e45002e0307a40314010111300c00c40030919590b02040190954415181001d08100d9012102032a8461618a0305136500542c04d00016896420130088044c11454129540703805104016607000c0d485100300c4e40007410380e00a0321b07008180e07a2141000d54a07090400202c14501c40c0c09150610454100341c40c060500c08541c0c2c02c41d40c0b80c0005020b600c0ba1600c3c0030310007070b40000008a00c61a018450740c440d20203800c29040c624100c0007494007012455000b2030041c000300706100d41c480207543c090320107444c02003008100103c3c140d00419112012800d01c41000442d00031751100c1c3e8015004803842101110103003908ac00104e8200d130005612040200c0e03084001c940c54610a07084503410a000400004802e0b583e600000d200e0034009807000041d407000b06181540c081544a8186d0011144d60290b1552a0061303040c1070070f80c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 424500431 1250 424499181 424499233
    0x50d08040f24031a0604090c023d02040b03090a11010203030609070e1516051005011d18100b01030c0c05030a030e010e12091207120204050702010e010f15050102 71
    0x1d40c0d036000341e000c9042404c6110030881406004140d5950301c1e204440050284000301101502c6206411100c450030500d020480c0f005080c244140512140c6c14480d040c03040c0305402c95050340030302000c10054550710003140600c044a0040c0303c42002441c0c4a44000f040d61525419504103200300000303522981c25656001d80c25142180d0114080c030b00113030340c900030844412850000800c0c001c0c2e00400340490b840115009904903200b42401e0000d45003a94004d00800c803440100b0100f22811b25000c500c043d1704240d00028080e06404032040340b510700301094121b444850b4031120050703503e58041c403030524404900c0c80d0001071001d075901d8065991240e003541c68105036640c51150020002907001440c20305da00b0080c0d075900a0000851213140c4c124486161045003c7c1681310030078040052303100100e4405401e10440e0616680070400203040c000c00da9001c0d0354942c0700e81003404c5001e11810860b44071003200010725440c11448242c40240641091381036502000c038a500704c603001f4807441d07912 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 424501681 1250 424500431 424500437
    0x1e02070b15091306140709050a0e010f050d0212030c03090a14150c010b1807032d02130b120a0f09081b240f310309050d08040f24 57
    0x100044e19000c0c0c004c105c04c0320220b103201e016100b4004c01356403040c0e403242120822140c10980a4480007003610034030080c442e0081d144100b8100f04014207043c0403400400d400146040c1c40c0d51609120182141d0080384100e40c107402c00641030304645482403841010700350341054804810840300c0418200c0152084602c909180031910308014042500500815900504448880d48980102100884040e43c00e100824204202c000c018030585c400c040320004e820410640c0600e00b10442c400030341c01040d110510031420840030541c110100010118088004c40005042c6010751558085036248009145001e082010600118510740700b03031080300403050140410041005070151400c140f8445000004420750101901036641d06007680c85801e405254200740da58a101070340c14041c0c86e080001d4031801a904c1d082900017601d2074015030b01c0c0b280c24801d11030350329440047d1b5008022201150780b00b0000805010140480300448c00400e059540040a001642c1a030740040c208000c0c10010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 424502931 1250 424501681 424501711
    0x3010c0c02030a062a080627010b09041508030307110c0604060e06040f060804050105010905070507080a0918060306150b090607050c040c081609050109060f031e02070b1509 76
    0x59680070408485000b151078100040609203003402034188442140d81c03520505900381002080001c40100e112606588c100d5009160300708034801520350003c02c2c40941140e1f84449944d40004005200c0c0042e0072500011902d07858031407001006400d5400082c1000c0c4c03c14034030940c80c4e0722594180c8040e1106403c4c407081116114010590900840d07001c1c074060504d0200c00696503400603121401140210001d00c05a81c03075081c054161402510f203030000a0f000c100301d2000c98110000340065641e5407600b1840c90ba6503080001511a6085004a1040e0340702e1007001040b0451081c00705540c41e0226076400340e0318054500301c0d1409852003d9028040005404c810030000707100c11020440000c20400140144000081c13030468200c0c1e4a81c514048102e05d01d103514003c544020450784141d5070111060b040007001c450940f124003c5000785900c0f410f400c0840524034000340175181e1505801030b1102c8543c14501c016280c0074140001000c1c03044100700854452480342d81d48140f61241c4181c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 424504181 1250 424502931 424502951
    0x206070c150c170c01020d06030c1a07020a0512010b0a06080702010c090e2a03241c02010f03060b071506061103071e1a1005040e0a0209061c0303060503010c0c02030a06 74
    0x2001e41320307003600321f000103180407800f100b0015a00e8810341500c4809194084448c01031003d524a44540003000e544225810000c01c103503d00840c10308409084c0700000314200e1081000b040f0041c2d40c90704440041400b440c10403603000c0c1d0921408540c1801c926003614810701d88030071862281c5010b4180174980b504500c140812085e040b0424034a607001c0103c6a903603140038070140c3d505402c04c28032200302e491400080c11a5180038080803000c06221448070402e10f4095005441410341c03114030b6030616843e1040000c01200300c070050700d805400741030810b2071941d8109111044079455000441484a9100c091001d070f1400019103507519884410607140004041d01442c6a280d00c0c00002c04908050903801c99034000003002c5405655116a14004180c5500400c000d031358912041e08042d9000400703100c09460040d412540108014000e40c122180d94000702c550300562000903404251542000c1085050910078210211143c0ca00940c100d425a80001e80366103080c00b001d002d00340c503444944 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 424505431 1250 424504181 424504183
    0x608160f1701140f0709120305030f0a150b07060507080f07032307050a0f02060c07020609150304031d060f120a15080c043207020a0206070c150c170c 66
    0x84040f14510811075003450990041c44c42038000302c076640e000030358506000440181c0c03100701c0e0384007503816100c160131542d40d01428080528010521440c032500ca0003010300000c0c4082205018021825000d5640e18040c101001640c1c03000e4464070800c02c1b03200411460781400c11003190041c00750700d0301007401064000014a070500c1000c42c44440d0520109211030740e6041402040203000380d4803031031486101440e06a8590404640c9113454220400040700146809801070607080c10041028550108403038000c100c80c2c03c111401c4020030750044600490024413100c0c007103003a000b103404918021551889000b00d00801000079280411032001c1503a62503281c020740c0c04032200c000100c0c03119503211030040c0e940e2841810f41d4011840e0402c54601c207150840c03803890300c514036020303000072403402e0b0f1001c000080e00600d18003c50107079503007480050360b507240140f8623540200d4800343d1090415802e0408c02e1540c0c03c40c1e400b070103410100d00b00000c000c8550b1002c030061117000c80381c40342c1c0320301042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 424506681 1250 424505431 424505441
    0xa1701021905030403020f010b060a140c031809010b03130b0403021e1608011104060f18080303040210170604150905010806070f021207021c0206030a0608160f1701 72
    0x8552000241c0c140610344681c094043e41c4164000c3c3c1c201e40e000f4901190103801c8640008040f034015008012030403134140228010742d0303500c44010059190044900089045810545043e090f0b0381c00041905c10f0751501506032805003414075402e078038508040d00850030300c550031007004090480000000701418003d0080b80042d9841090308480d0740007411110791141c4285610301d00e0032040000126605005128040c01c841203100240e10303050400d101500d070b090301051580b0800c22003040d1080c0200703400700440014220700380210740f40d013010710401c41c1c00d200e41c0c80c4a804000c8900c2007202240010400640c1180094500003a0750300d24135205e4881210075000021140d0606000045440001030028840d6240390b03035441c0303c1c00c880305c02240c0740c482c80002d082b1611824009900136143c00c00007600000380340c0b18101d0049410b80d005ca6820f8004070b8180a696940d42e0f8100600c40c0c05202d5001200318017114480d20a00300b034200c410f00380084c000c042050800c100001e4000e00d0035840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 424507931 1250 424506681 424506697
    0x301061e1719020c0a020109140108190b0d060b0a05180610110312010305010b01050301030b041b15080f0121060e03090a0f0f090c1d1809010c0311090a170102 70
    0x759984c02d50914040e9841c81450000c0b030004450503c00034004000d50f035800c040b00c10503901e5111170f450f00c1100c02d2403104008070200540d60307900d28140c03459a840040d024010b101c3c13500400c03d40311580c104855034600ea88424054542c140198521640c032200f8542e100c8811584004031070b18244080350350858100120056100010740b8408010070a41c0c214102c1e07100741d0003404100790714001190180070a1000030219000ca502103030001e46000c4000383ca58802c8104a40d40320350302d803070070306580c03080d03c090340045200c040c1400501402c1d04541809000041044651000f012260000c3d92140c0c0102620040e580d001001c1065814007c940d0304040080c84401c1b1036442e05a0030b4405212032043c104105440100000c032003506001c0c150845c0e2003a11081e020f041c91081e901e20721408000500c0e4880100c44080b43d000484032500f07030041680e81700025460081203400f40403200d04860740182c0d008207000b80840c681c0d50f0030b01d403401d55a010106a01c18403961240d14068090000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 424509181 1250 424507931 424507981
    0x305151c050c0a0609051c02031c0314160e040b030c040b0d0c03060509060a0c1b031b111201061401180b04090b01121a09060d0c0b0301061e17 63
    0xf400096003030340301115405652088462020405054079900c4010a00500c02505500710310b20104044403031080035903140545003800314481e001c003c42c0c401c11403000c03182d0209100455070b50302c0b205035000e10825220700e02a01d04000403400240080d42d20a0a01040d80c42103407071b16140051038480f1841c052442d5800618401020344038a441005000105d688c032813684600c5000a4004400707000e1100310064980303038005600d20240300900e002c805001e0540901c43d01b0480307241288665003e81140742e004000080600031a0740400c1141038010f141d01925030b06046043c05228012074408031052400d0810382905600544940500200b503404000d4044011400003194216074008401e022400d90301c0b00d81303290490204008440050407040e903c0380c3e00001d6621a4248081050303009640140118a00386003641d900c20f03100156000b241d1102c1d00440100100d0307401200c507080c000310000d81ca0701d601e0f840c520000e24000001c108892107494003000f103000003043d030301d801d540c0300c10001c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 424510431 1250 424509181 424509199
    0x2060a050c0f18030d0203070f151e0b1e03121305150a02070605041508071206080f060f011503110d020c030a140f0a03051f0608070305151c050c 64
    0x40120f084000f0510060b42c000e01070302c100040780b144044115a00c0583c4540c0e0a18001e10903203e81d601800c507038402c101c54035070320040b0038032581d003001c0102c031071444035000441d0340e08000d400d201d680d8015110b10009c0d1061100700c0c010340d64000c03171030380c00448443c6241500c80c400403005440ca044540d00c0903400004032100d038640256550300401c01c5800076000c13103003026070341d07902264180311380e104950369580030b6002c2ca01c5507841343c1c8a00ba0010060f08e401700d00310b420340c0c00c0c010484065030f0007000160304c00031010340a50f80a0003490362080c10002c0c01c010940c0f61102d010702080f00c500ca10410142d880e10441b0610808805585403079021a02c115120480c0c8501196241c0c003840c038501c0824035a004540b4800c180070b0403202e0300c2d4600015039007010080d902c1035000c0c000143c0100b94110144c10001c2481c003400300c1c14030013000c045d5190352450a20040c050b0880303001401d800640c554902c1055266281c0420b03040d80b0070314840324595207030b49030b040c03150418118940c8a41d00c07500310 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 424511681 1250 424510431 424510447
    0x30705030108010605062503091a0403060f02070308060d14030f09041503030207060c020a0911042d06200d0807020705090402030a080c16090c080a0c02060a050c0f 72
    0x120103103068801180080142940303c4040020030f0103051804900e4890710310446401c907250412202ea11403081c28100300598036800402c1d00d03120b6034403c0c1303046004049010420b0054602600303a540c40300300000c520300301e01524010b02c0350354010320850040800000c811f040100c64101158422210000c1e01d851300d00d10300075164142d220410070342c800d0b42810b491030207415504034044c0440780d0680003020290b01d050307002c1c0d031881d1070300f0300c00c2c2e0340804910320000c0d40800d90300446640308144010159101d09003454546210310400e00d00d074540c02c4080040074000710100020742611494103008041c03d9a0303080c583c504600d5045581510b009503480010801d410a02603401250640c003135034121900c07071040c000c5488040764080d50550000103100c003c106044010081603a401041d11041e00c40d4171807140040d41580d101039a034030b03603a49030322005942c403602c803607000721000906000070007400d403000b9a0b814014040015013580c0d040481c034030440307035070891312540c01000a140d183c0ca01c4c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 424512931 1250 424511681 424511687
    0x3190305010303030b181b0d09050f061e010302061b0114012405120c0909040317060402030601021c1b080417070e01270f0524010509040f060b0307 65
    0x802e100407404a81030400d821858600341a02052401c01c00c0c6a0450f580c0d24819440280c1542c2c00300982850020090200005040d014482c40c00e8001e100504920a071085454a41100203100102e0a003540c414911182c041046071070440381c04981098541e00f610941c14124100070102a41c60761034441001e08400102d00418103d90018404944050804d04404039001d088001d01d800128108070f040000490240340c0f6402490789024681041c000d500400c4055100382c5003540807030604104207260140000384554420030540b005c1d821130030b0600002c0d5540340c0c2c0a407044500c44212001c6481c45120703440b1285504404451402c804140d41400101940207004590003446480c0703c0d030010807400a0744c10201e491315000100b4983ca411703141c40e90b048824440078000d0140410300080800b40b40107101200000703010008444c244520311158286140b5600001405a4000070007642e821805551030004152404581030440500580041c2202d0300b100d0005d80001c0240100340f54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 424514181 1250 424512931 424512941
    0x9020304051006080f0312040f1a160216050d060b040c0c170703021221010b180d0201021e01020c0102040905072c101814031204030f0b040302031903 66
    0x900c2c140204441900d070f1001940340e1074100c07003900d8260300c20003032036104501c094226a400390059200107a205075540da2183c41c02c98138400e0042140c418800d004e0440c1074500c5000c01c013403040c001085001d2504820405852480c800da600c2801c1c6551890203010040d00464050752004004210b40400e140014084d000300003c140c444880e009a0100c40309120021a2007142d0190000e00325019101280740a983c03100303052861aa0001c1d0b4204601c0441d450014003800402400f1034641e01c60362000c20310200c1c91000d6070700c41c01c141600c550150340c012840412406c64081a41d107048484400103000e8864044021303810762000900103495105644200e00540940c1d64408105e0112104032503441d40004110741c842501035500f114601c1c021210000114017400c00705401440040681051003130380d0301002e54092a40d2101400380780601140c12560b8008a0761800c00d404e40c0c4820f440035154080c0100031626050104041c0750080080e120b084540e10400081103202c658000c2c060b01d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 424515431 1250 424514181 424514203
    0x30e01030f1407140702090a0c2c0f0d03080a180c0e150312030705160203060f1803040b0702100e0907030e010c08070804030c1e08031803070c06080408040902030405 73
    0x1d254908604860746240204c810154000384990195100c5061108c020050a581d10080c00308a1012784620b0401e440c5061700018186601581c1c42e8014051040c0c22103240c0c2107500c01e60801c565840000e400c0601290011018400041c8801c0825200e100289000d07001601540d48004002502c58442c101da600c01c0509401c2c00047e00320720024140d4508013154400b000310428400100000c1c400c1d0090182c80b8401c0f0074421032800283c0101e8240102955000302403e01c007410060000325840016140e00241c030000d515241c6010f0b6100094020b03044000c0c89588003000c2c0071040c031302c06c02030030000c2840105031160500380a10b004e4000e240181c0d0b046600d50810106184440c020b8a159226129544440b039950359295800c0346c013181521400c0326581844003600d482c1901414480045070b1040d16520b980c2e0411548040d01e2400c90016503407158010440f0400050f00c8a0400302100c045003007050f169160707498510401e00a641000e00d56030303c04400c2109200700004c080c1101c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 424516681 1250 424515431 424515437
    0x3031b0f0c01050408071a19110c1e120703060501080601061404140609130204080f0c0909120c03040503100b040f0506060f090409020d030f0801060e03060103030e01030f1407 77
    0x74006640040d9150700039031058140780d400165040014000c00710b44107208030b807a840440d1a10807880045250821503014400000c1c0c0b241d200e442003104c0421230074429201c219440c804a410401702030f5036411803415000d000385400c115141c9140400c00159020316441001409290307102c548490703a8039001d00c10032000854121420078000303008421203003522038a0401001c0714a21a080c044141c2c4611121608028107014041451505201500241041c200901080c0e0728060030035290000c24000a8400e405106c02e002c050f510001d00400d8600643c603d541d180d103280505581103000301d605ca02d8140c0240300c501c40c14500d01d0b0b8040b03040140e046808100c0c0c16a600c80420446400b00c48954000200b00403086d504042000a000b14510040c40410b0f5188140c1c00b080d85c090036035000f1804a0103502e00346401c1908110380c980584244d203004609442c0540005ea65080b0602c0050144040e000850205900c20303001304141032440142807000511090b0301254900d000c81d802400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 424517931 1250 424516681 424516693
    0x1030c020a0b04062003160806030c0901030503130806010f0314030c161802030603060103111306093c150e070903060e0a020d08030604021e0408010605040c12050603031b0f 76
    0x180d03140b0082c2c07401f0f40d40070074603e61011030411043d601c040c4040c0c4015818072550140d404a662019003031406103206034041e64642c1c04a040d612004191900402842c1d00410014040700c1000025001120b421808440341c000d0f117a40d402c0d00354400c9128040190040010029881070308040b10f8044a00c9040c90030120351084540700200e00066804540c5a080340c401080442c0c031500d5507815070700c0000c101c026007134180d603101d8003102c01d0303a0300503c03c480e00c540c1d000702003105200c0d00e5003420313070200000b02d001080701c1a02e10031001d84082d20b1000319070760040103e007005083c0e078410282540710000745041c00e00705005024407809102c1100d038641001144120480003185c1e4000041d40544021180803040d9200c40558000503c42d0360820303401d02030000342035180c000c18a0640300075034080307035a2401c003880300303085d20701d43d400450046040030341d1a68982da0200341051032440320314000860f43c0355000000d003544600010310080c110fa40c00350072401a00801c4020202070444200c0d90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 424519181 1250 424517931 424517981
    0x406091d070f080402150409090203010c0201060302091b0f030109090203070503161214030304080403050708030715020d0b130204050a0806010b190c0c12062901030c020a0b0406 78
    0x180205088504000180020030b00d29821405040e00d5034220384010000201d0b01e440100110903038200e40d011130400384c2c4800307440b81542400c1c4207101100ea0070388000d01465055402207800000040c050b56544030381160008001d40079201951034020007400119600d580d65460707103026245500c0b01364403d0165480000c1d6500d0000fa0a0702c419850468416100e031a01910311452070f0180400c2d5414242d8213403920308004103200440c8158400e949480d02d81d802c40c01d2007490190103030406079660707100304240000300d1a207881c2110011014100540c0d900100801d900190003012452034111303803007028603401c801e00e98000d4030940303409903030f426030132907072800c2c486d07900c1401788101c0400e92410041c202030441c03a200d6071248514030b810503010705205952001c1c0d819050340d0028090303040d03c500c043d0070001d650040c04400441d403640c007400034460311300f1488150851403034507043c965100e8000c1e06003802442540c0c845900401140050311309030402d2070141c0307090b2240051100c0c142003402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 424520431 1250 424519181 424519229
    0xd14031b0a03050f06040b1e030304051f080c0406050d0902060c01060603020d18080a0302090a0e04051c110d03050601021e0708070e07051608040306020a091a070f02100e0303040609 80
    0x1042000d0022301c00b4541004038060b40386c07440ca82016183c0c160004010208103034441e980c02c86040580c000800d171050310401d60050492102404000384200104001c1021903402020750b05500200040040d6850081c800a0707041d1040b54090700b155401c0000005000e601580030b880291900902030180002c80d00f20044818040c440c000c007a4030003440b144541912070b074040d21421034090a0320341c000d41c8801d1206102c81044030200c81c40d86c03000c00001c00034084510321100c502d040341407511701d14010056003529246034884560805542b14001072242c3e10070009070518429407001e00c03507101b4045440c65100e10283c000c40480e446070601c005003903c0070403420b1388038200035a42c060502043d501c0140d2104170500c0141c610150600011001c00e100d13100030302c0300d490700d500e07184038061a01e0000510041c5010f4030341c1d070014003846050041880341001500c01e95048a104030300c039104080c103680314900c1d0180c50340c01d440042808a0019001030aa40698940e049041d0000d03041c4100e907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 424521681 1250 424520431 424520441
    0x30f14131b1203050d06080d270f09090204111801030f050103050c1e28050108010b0d0c031b030e1b0a0b030a090507060507050115120201050d110c010b120d14031b0a03050f0604 78
    0x10082b01c2843d5000c000d4142c6a6000701200b9100500200d90040d504503820310540000450741c080d07082540c00c0e14215a05407080d8030540c03640302c500340301c1507140d070301e0b8180c0b02c03180340400d10700802620102407440d5160700c68406803a04000c084410100165280b400c0c84030000104440040b03200c000803401e07600409616040f101e240001d5440c0980f0072103d00c01034881d0030600c0c018941c0718142c07040c40d0031016084080ca4083c44c2e80010b0804280e8900d50b103040d8031040001c80b144003429064219490b07104110f0152440c50040320b07900d40326440c03040700071300741840050240c2c007944001045582d40000100b850344c1c090300081c081591145414202c40244d48030702e281c2e4140d00160800194000c80181224480320b19000602d510b5014000301da0b0b03407100c0d4003888241d54404440311503182c2555100c2d0800d101200400c4618001d0300007800085101e21100d87c170340c402000041d00d0715151403012a4040401081a444444040010b40608800e55992108a1500b00000e40c40d05040c07060b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 424522931 1250 424521681 424521689
    0x41104031b080d0c050c04020703080a0f05150f1809030307020d110c0411090d060b1201020903030417030f07120825030f14131b1203050d06080d27 65
    0x50001a140c0b0b031020f4800840d695401c81e941e00901c14241b071607540d18406041518040e8880e0036803807030f01104000460701031a14180301c881c507201c1402010083d0340c103205074204050f14440100d400001c0000c4000c81511148e4040000403020045000800300141d8041c0410b90201e80e40344089003010358201900c40b03410380440c5d108443d001281e04e4103400c6900e40100c2d00e003c9500e40034510000c1101001e4400c01615115181e1600517614217002ca282071050003448003c6060055281c0041e8503403285200d100784c1c2001c50343d01228414014000c842e068454a10303540c0d0340303c40c2c03440c190b101211080d200f140070882c0b03500001c820050315a10039076080d0b031035014140780d1540e000090f802801440310280c4003d039614603188070070303040d6100c180c0102410b22780d0b4612813500d842e1036958145000d1403082d038000c821000b089003102c4c2d221a00d501c0c3d6418142141ca0b00b000100020003000d1591001c01c59100e0741625000c2107070006000311105001c8812034124141e00324142c26194640e2207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 424524181 1250 424522931 424522933
    0xa1e0b03062202060d0e0109030c0c0f0617040203010209031005040c0e07021005091c050909130209070305041e1208011502030d0e0307050123060d02090406020a0e041104031b08 78
    0x210840103141c148010442e1900c03042c4000b07140b11b041c9494a00f15898a00102c01240c0c510318a0018801c80c5d003295402000b0f50007054070f6107030810342d0040110320548207101c08a0154008a01117603001c0d010b071100340c1c0b0050103c0d82031080e5a11200003501e02601c0507200e20b0205170021921064101202c0d00c503e405030000c081549c0c011102000921000b44040c02501825520080c08000d00e10780b01c100101030b6030303490340b03580e041c200f0801d0a20b4007900f580c0c440c41e2a40f1900e001a102c82c0d0b0010740c80300321424000350640d03031400c140c0c8400c1d0558040f00040340401011004200344940701910a001c00c0e500d241caa603032150501c90402c002e464010300541d0080c015030020a5903034000e06004280c2c1c2095030301703103182c607a980d40c20342c5d03140c60b405040e4513180320f04100243c440e403012075803240046a40c480041c84039004500b840700d0240000d0400e80e0001400306555006071011400d10402030801c100a0140d0102a44150010b000c101c03100c00c100d1032020380c0719100000311000d4400440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 424525431 1250 424524181 424524241
    0xd0b0102070311011b0c06091403390607060e101118060417010b01080a061a0304020414011502120c0601171c0c020a2306030a1e0b0306 60
    0x3d8019204042c41040d02d50400b001d10b0417040c00240c0c00c022a83c000d24a0303803203100705141002e805a40101104a140780a94041002c10401500b0a040c0e42e4222002c50b813901c000c0c8000859042d040800701400d50341101c1c00142000400881e50302840c40801082c0541d4003c42041c1484000d4034501040e03031500c802c0a101182d41c21050704c034401c040c80d034010300981c507107961000c40b05101904442d0410290350f4644001704123580224842d640040004402c0103140c1c00c1c103031804400c080700409902e03210800b00001d021916680e20040c040028101c2110345580c0da42026042c50b119000404010b0184e109030078261202c0b68107840c0d034104043c02a24150782425450407401c580d004409a0f14420a09218003002082c29803480810990751164202502401400094100c1e640034100007901c1e800e152120401000303c03072407900412031b95540d4070344503581c0e607170050000105800c8484080000a1032605901c1e48142410b00c801cad0103851480e502c00c2428402c9294150b14814405661 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 424526681 1250 424525431 424525463
    0x8120f061315051801050a17030a03050a020c011a0a170303010e043e10050313060b0a1202270a020313060515030615030a030c020d020904080d0b01020703 68
    0xa41011500032615009081103d0791900000e00c943d02401c90b481303d40c20704000520203414450030781d101909011001e0380008200e007480903900d1080f4a8408101070391003010403800c070940d804035444c42c28444001c1c030142c0080705c90381c2403420301902081c2c8610b1120100140152026451564120040d0b02844c1981e01e031141e540da410000070000c8580b050340f035226500d00c81c3c196110300b003284108003150402c000103040030144010908000c0c1c4c0b00c3d8120000f440da5a5a000007169440410b04044141f000030038a0024050096201c645174400e021403004103035903082c20318503070040e40211610401e9404204904c40498004064414400b400400007241c040d92a0000c5070070480441a480080340305803900400c6a80a881001c007810365001da200b0f503490100078050f000341e80b1102d0055400004400a584c49030206002801d100344650450159a1003034076a43c10701d50064004d203a5441c0074605145150f1243e02142d08852512103071340e005502c005031080c1aa41d1010300030300b9410f14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 424527931 1250 424526681 424526719
    0x70308031f08070b0f0309030d140a0b0118050123030702030c0c1017071e05030a050a1515020f0f06071e14180409211b0303051b040308120f06 63
    0x6c01846080c8603c41000301c56601c0c0000e216901c141d8014540c006a203040049500094a10000259042100a00794081e01400c1c0015040484200f424807080e800711820020082d581c1540c02e0348001c0e40b0202c00c00002c0c0760040020403503003017901d065403605c64900c1d04010100180d180d8000000c0e01c440501040445003401103600800c541c1000351000650b40e000d250540010027600e40050004801d021034100c05006a64001c51014010721424103140880118210284031301681c1040018140222034028000560300d96120006d8031045004407420a039551411355503000001d16208054089007842200207522000fa551070142c10300c0d8107030719000b040d0001c0415142040260a011103150745a21820341d0703551045c001c040d50000a550640c2150301c2e0b0716110b005112102982c50054100c050038203101c968903003400101502d8080f00c090360440410400500290002000b00c00e00520402404140c40c445000740074a50f9400c11500c50750a0594406030801c01402d10001400700c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 424529181 1250 424527931 424527937
    0x6021c030527010b01080105090412030b040f02030a0c020d1d091005040c02010f11120115020a020919200a270906030203100b061209070308031f08070b0f 68
    0x1010301d51141c0740710442d0169201c0c02a2482c1d0000035695a040d4010865801074903150040000b1a960a15460281c41e00c401c1104055440010141e6400801013a40e95991001d200c07649441c130219200e01c0c020703100100034940c0120203c0544940c2c20003020341c40c801e2454000c5c41c0070703909882c04140328100c103010380080043e105600728568421f0208147d2203910815850300000e80c008148501a04100c9045941040214070742000800000319528030320b003030203411078400c100d48070017080d000c41d001c80c00d092008100039030003c4418140000741041004040260010401c01c0000c0c941c9202d10204001010402013810001405588991802000700034441c00c82c05502114003042c04040849150681d0450301d251a514802070003941030030001704a0600440504001c41e02e0640000b030b24a000310081d01120120744000034903100b105110304402981e1064070749450342032044c2c50502c82c648228000106c1c14580b800050030113030005100e400c80d01e007031443c41d00e0701c0d00303502511050764 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 424530431 1250 424529181 424529191
    0x227010203070b190903020d0f020c0307030b04150203091b010e090114010306030c27050408030103080d0e010c05070506060f0a180b0916021c050415030f051005040606021c0305 78
    0x240a40140b1213800600e004040450b0b12a034040c1402009820002d8003506860204008544c030070200f090311601c0c0018120152900003840454550300d62500300004a05035010041060000c8144203008a0000d401143c1c24074546406480304041001118954240d00740340c1c1e40040c010300100560900003440b40174401040c5004214140c680d260038081201035403001d000311619001900805000310444050f00d206c03404244030a0070962221881ca0206010142820b1030004070710f48031800c264400104021440d0082c0482c40540d0006002a0008c5c401074880e07000e60b400203210b6203404528152002001400e01d400c0c0d07410640011110401c01c41240400c6544e03805540341550b518244a2045980043c1c1160002c2c0c0054000d081005140c0d20070801251400101405504001540c05442c1c4902038a01c1d80c02a10600724040d002d0481e002d4061403034207052001c42c000d14840313035040c0c560646007440003542e504001ca035a1911058004200c050300043c003558140709400540d048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 424531681 1250 424530431 424530451
    0xa0207030e04151404061811120c0702150c0a060e0c0411040501020f0d23070807260a1e020f0609010903030f0c020c010c05070f03060227010203070b 66
    0xc1c160440400c0c2124100ca80c240e403100c0c140d9034100400141031003032120313043d019201480201e04c0c000440380008040100000d800d1780301d881011200304002c054464007125501824413a081c0000c007880140d0008005038010003c00c40c51031210300c050011901d1490b1154014101c00e44c158035010700520014001c0c0e1054041c2c081410707066601c601900c0b034984050404540d44a2400c0000b900d060b8101c80a0f8403035410810903207602a03044205c80c40305003101c10019003400c00d82d01c11000180300e4904000c02081002c04c2c8070060100c04500300104d40c01d030242540e605030a03606d9802080c01648643d200080c810b4010784883c806080c00c500404070a40101c2c2c02e41480d4010040c14140c040b1031804807030b90748440401c1450743c58060780990684080c000c204007c5104802510790b90040c802c0c2d814003980d01e070350360704202040290500030400190310640440c0ca07464288003941c000c01c001d6680412100c034042891a03031400040301d1140c140c000b58034000c01542c03180d0210100400c0e401c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 424532931 1250 424531681 424531697
    0xe0609220605040204062a1205030403090f0b0d0c03060b0f09030102041706090106060f09170708100f0f0b0a23030a060c0f08071202130803070f0507060e090a020703 73
    0x200d80795130020340040e086c0c0d0b450703840c0c0714285031130410280e403010388918a140d013034241184045006c9010a07803032500300d4036283d1f40d26901c1b03060a8403807288951007480e05d8280680c00045500e240360240407400c0d01d884081c4480242e03d40110309440c0d041c0107002010f402000005a0824142e0003840b054401800244c00d2076682e1024106080c24605007030300c2074000004000900307000b88150700152001c3e040003041d800005a004000384a540910032580d500c070308412032581800c22140000700f4582c02100d450344075481100c4060321301ca40c10384607907a051a507111182603090007144501e1202501c0c07158a0740c075165041001204450405560702c000301d1120366203803400c0c050844080d0007440c0100e01e0200c503080041c5901d80d11040f10080117101c200313100d1201e50020324a034070300c6458600903072142105286e0400700c800c941d11000c480e03c000201c81d4200300410840044060043c02902e4405a0301e90043e108400c000c120284e0014101c0b00245404501b5406028a0350283c94070070700b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 424534181 1250 424532931 424532939
    0x50f0106030f140a0603020a15080f0901020c0d021c170c280504031e05100b0a0b1b070b030405030403021012051f05190909030509030607050a0e06092206 68
    0x24038010b040c4d40c4000c40945601040c400d500300842403100030908645000c1c00007680c40001450950050800621000084007044e22032400350103880100c0c01500985c2d8426851740000b07903071008a440310381034181c04115aa142c3c58010308094100c4002541c1d42c0100d95110400f1000c0c641c40350700100524004c0b00d011900036120401d0032848014a501c41d160365904504041d4200e200501d101500004c83c0d0748020300080c0040b4805814140170003001c00e0a43c20900069242e43c0706802140c000c50020400d144c0d400700c0300d462288007030090b605441c86c49444202401c02480b00301c60203041544104400c00060504c03d802031218000e44c03401c00712002d01c000b4444103495082c0ca0059860b07040318090503060944d43e00d5803000704801c855058448850b5030b0490070f000164031469135001c1d42c4401d40c030300703160103101112840000141619540d183c10344001c0c081390441c13200702001030041060f9040c24208201101e0f00c07050024058042c00011140440340d00040c805c1c1ca00c40d403612110001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 424535431 1250 424534181 424534211
    0x6010302210712020703020a0f02040b0402180a141c0c0906090b040b0105041a09030f01090503040602210403120e030106140102061b030103080a170f01031203050f0106030f 76
    0x9450362031400c1d03086080c18107030001080d40c0056269041024410000c80f0006500021031281e1158480c0c000360000da00d600001d4011300d418010f181d0443d00000b010040350103142958001010101c40e0f52002986407017600d010b9144441c5d0040d017121442c40601460908036083d42d0035684601035a4459945504810098800396480b443d8010748402c0d000440f845e007401200310b802030a280032401c103032803c4941c3c841d00182d10a100c0300007000045014403500e040c041c10f906c0c1c0b20341300002e00c4130720030350b203030440d680c8c1d1084c4913000050084400f29603103100040001200700308078003940c6090030709546450300c114062003e04410b11a80d2412000300b610203001e030314014107240494000002c114000a414650001e02840c080c1c00c0b030762a580402072954050720706582d008030186440b804886405e0310340c110400040c4012910744000c101c0b00c021410400b5060303900c82c0c41071a8024405403815000e41d0b00c1a68200001c6440c1c0c801489803903c43d034002e607040c160810002ca0f0030410340100c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 424536681 1250 424535431 424535467
    0x9040606050403020111061012050c03010204060507050601080106080a0305032805150a1503020a050d020f04170303070e040c051b01021308190605070c02060310060f050408070e06010302 82
    0x110000c0788011404205560b0040654501401060050015854488a025440c1038140280c0300340300000025001401410029a0850b84001d4000c56075191608005040c58002e82004c071083c0c170959001145030350040c020582114083c0004041d05240769406550540004024002c3d00f814032020301000c0100952617401c2c4416017400150504042041c0c12001150000090150200c1c0c02d00300620b001300c0000445007010380c58010f854240490089030184200909051403030700204d00040581841802031080710812640c030a122003d414149440b07000031a0300c040810000030403c001414a0b03044000f03090000c0c031f4594540160001c042d01091a61007103541140c3d400300d62003050180e01e0351040040c100800c024000c8c010038214011301036480003401400c068462000c1001360340100f0f018030078554002e15490303ca1601c549407015a050340d00c1618001510706445080c0c00d8000d0086a095801200142c00d80a0400444502615000d8401810103508001c0c605603900804c0344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 424537931 1250 424536681 424536689
    0x2e0815090f0304142205070c03120b0109030213060b0a03020408061620010e010e0319020a02030a0311030d06030605061315050405091204030309062d080a0608010501120209010e1e0c090406 83
    0x103100c07412380c07481c2001003d09005001c100b850b5071402c030354140542c0e08507100b541100d90403503910a0700e21940c425580034000070341c414407440e80040bd1408540d80c054001d03006484c15082214240d80e12a40803203206007425110a012610203110045484101846440902000000440e000300246000c50840b850140280313015080032078450003001c018a00d04060008610080c19221100d4000070b803200745e031240c02001d0010541e6240c0c1c801d501402950114440760400300000399880c106036000e8041103450a01c40c0b2504100d4101401c01c5d880b03501c1603d140c0203020110740c4d04140c01d020081c180504000658400c1c2d0f242030030b80090100052024510030b59400101030314114024141c1d6640131081a1850f200c20102c0000d000f88041c8030316190614a8881280d49078003041030700910981d0002c07005c41d401e10001099001c185c3c21440c90b902d10984550040d607070784400b516078000c0d0584e9403201a4203500444a80c1c01103080040d5008800c00600d640f402070b240d40060121800c0c0c2d48 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 424539181 1250 424537931 424537937
    0x8070603020408060f01081c030e030d05160c171602061621022d0106080105070e010509030c010c02120303010305150c032e0815090f030414220507 65
    0x3509000f005820720a098202800d554481c18650500801d04e49903608645070b8000400b9021203020180e2180c0c000461540c10107081d80d43d01c035081d46801d0003414045521160340d105082c81070310301c0c1b0f105060f150740c0355070402e0450303040c0410088c1e0541158010311038000800b01d264075440141c0d5825004040c50b200f26002d00c0031b9000d4a2911130103100300c02007140f00402c880c0604810740d58000c03540c1c0c004100820a032203030030756001d001c40d11460084001d10301c9540c40c001c004a14020305500c0540a6072441d100c1c00d10300084200110703918820352403c55096004a454142c00354040c600500c0654401000300d041c61059090740c2e480c541099005035065401035180c00501d0041154641d0010402d02d401881c52419a6008070500308455400a0300f03200c03000114103480d03c0d2500c080c0075100000a031018028502c82e01c040491003136596640318000e20b2106182da82e4000120f40c1103d100e6070410b14040c0715070007000005400c41f4442d82c80300e56501c1d0341c510303424224812580b0030945070b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 424540431 1250 424539181 424539187
    0xc0a0201060513020c0105010503071202130f090506220201210204081903081005030a0b09010b03010603061a121207020109182003010f0e06030708010507111b0f06070303060807060302 81
    0x400c46c00d40e00d069000030700a4000d000248840340d180074411203442e40559900c070442c2c03820742c0c0c5071005090292043c16600c1c901011042004001314800d40200c030392044e402100100c50f8944c690b0203001500c001d0218120b41324200030554181c20104070300c40e2804005040654035081c642c00d20410340800141d40d906148181c04264000b45040c0d040a48030803542c0c54141030901080c0d45524400000d000200350000040900000b500000e15000015000303001840d035918000300505120b0380c4403112040b811a0034082802c10ba4441e0382d0b007040c52002441c60042e01c0b860390005601c0b2071f105904014400b10089421450300908602c44c011449000400d181c44000485440640181c02801e2080070801040100c0d1001444420745809e016401e0301901c0700c000103480c1040d25031108159500307090030060340b01c0c0c1044410301d04007808410780e127071181c8100c40e0342d2283c17070805440b5a1018040c081484c0c0d50030490040d01c61a4402d0034001440303a2618407a914cc846190302250001e0307000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 424541681 1250 424540431 424540447
    0x81b0f04091e0309060c0804050904152f0f090108040f06020406050d1b080a0c0306120c05010f0e090408031305010509030d0c03091205090a030803070e04230c0a020106051302 77
    0x10920f60051845150021b881e540c0d698507005188a180320345032040c6901c034049814441c590b0180d50042c0e80c1914100428403030380c04007210340e8807074000000c445068140b0f4072410750068411201c281c1e42c40b80c00039240000f9480151490100a0030680301c0d148005200c0c40080c074584010006021181c0b99182c545456808070410b41d4078903012030080e0400c0c20204401c690b00010070903000360b41c0d018040341d0014064012001441941d110f4005400310742c401c0818440d00c505071200742c91080c6e84601030500c0b03144d01519100c2984507400c2d000000c0e200050080b038200c1c40516005144144000100c50042d2075550a40700d0a840c0c400c1142c100081007602081c0c1271003070301484042400e0500c2120386945500740c90106000c4c880301803107400504540c1c19907400840380051a805024035440e07003081c040080c00794590005030390080d45001c1040300711445242c1e20b00b25000143c16841d40b10340d5242e1080509410280b1981c003559224440440c059980690002000c0d880903001070f02c485d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 424542931 1250 424541681 424541687
    0x1090606030c14130506060f041e0b04120303090303022205010e0d05060105040c030b030601090903140403050a060b060903010e0f0610060212090607060c0804050106081b0f04091e03 80
    0x40350b8807503509501010010520f0362100d1344011408001c0c100c1c0015165100e42c0032942a00c03440c3c1085a94000014012a08880038120b1841c01d14404501840483d220b10280c3e4a07031190740101181507281e0b9442200191081d004528450310a04c1d01508200c1d00c0e901a0940351010148030b2340c803603c02c80c824049540c2c04070302d6a030881400c484640c805c14158803040d48807903040c020b4500403070311122084000d900980111107071140103400c4480c1507a45011400c0280b11030441140054034a0200950100e4a0025070b020799400030041c040c2c05520b503640e640105842c502003500030b0b200303100d000704607a02840b1303103849204004040d00c688c0c0b800403030003410080e00601240081d9000e00742030040960000703030440320801240c0500e0703980f0001c000040c0c407401520300052a1034285044609920b41c484000d81c0100d1144c002405840e8843e500f807500c41c3e241d102c452000341166074048802d480d1482c903145400c10080c20006400160b502c41c0101c24121141d6012001149a5070600b0164 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 424544181 1250 424542931 424542953
    0xc040504051e37080705060f010501090f0504021804050117010b0604080c2218050d090302010f0e060d050c090109090507120e01150906080d0314040b0403020703050109060603 77
    0xa2a00c0143c5041c0301c00095410180a01c003c0c461000c403441c92840a083e02101000b503149a0481d081644480117440d2069490904562513491008100c00001307a07540030340010010f03501c010410401550a09003444000d400088400c4e400e50801d04039480709449a2141a001c0c002e080c07003148814010070301044c2904c2a24a010b07002d014100810811b240300403440111003001210012030700c2040c0000c80032080000c030400341050780b0b000c01d411880001c1401501042e8803071030680303005003844102691200898400640420300c0302a1140d800340c0300d10740d140c00d0309000400745410135208085401c111030084803070040e000000588884150380000c0c809006104a8500303005514103400010001d00d59407000ca143d5580303c2000091410080d00420003402d6180411040b0b6a500e034010800b8010510508a03540200001d2021f9180b00b8040c41140d0300050030203100f60340f00c940da410042c1030024000d4045000d0407402000040c820301900084600401d80030941e1070031420400300b500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 424545431 1250 424544181 424544233
    0x603060f0f06030b1512010302010f020a21051c1a03190201180510080703050106030e06041e17030f1003110108060a050d030201091205031003060c020c04050405 71
    0x1124200d0200314940680c600c0700c0c180c904524003c120303415040b011a03c1603c1e40d090b0450324031800310710010100c02000405048034001da8484043d0103c0e503100340d0701d401014502501c50500700d002c0120020000c0a120003411130b40c0381661403c03050710b84c4c0c0c41211262141404225498001180d8009468801c9100903902180902002100c4902d841c0b4004031250b002414000c00c0800049000d00f0f51500c03500401b8058440b05812003640802080346404075030000100c0d14000002c10100e11030301c2580340c40e84003080144100e40715500c0700d0781e100341c46c0800b0416901d0300403189000500540025140110204060ba07140d0401020510080340000d2417403070000c2c2f03086010000325800c55401010f0b4030b028240342400e40c941d032000c503600300c505400450f00500303124bd01c801010790540c000c002541c001c0f00ea10600540111085585100541b1000f0700342c510040140080307042c07030b0301010315260b00b801180e184215144c049402d4030000c6405a50325000145000310301418604000003003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 424546681 1250 424545431 424545449
    0xc05030f0d1505060a021906020f190807030b0d02011b080a20060601140304020d0c140111010c020d050c07090f0b03061302011215091a01020d020d02070e06061e04060306 75
    0x8403003900e07002907881482c0c0040360148801c7c4c0e07841005004050f411202c5280a120402340c0c0d8078031041c0404030034110140300400003640300d800074071080d00c244070302000f114004254040c0da1006400440b524036588070034094240f0168a13680005010000600302804075071514198440e40c00049000710b040208a8070190300201c2c00c200303044e030b40414403001452603000816180d0715240040341a20100482c000d01c80c2034003a4000c1180c6200041c5105503002c00d9841c5503000003001d03035481c00c1e51034003580140580c0c00f0720b0b90316038014091000340000301118030844640c582c1c0c60604800b03030b55503450090303441a907401140206041c1400183c1d404028410b40910b00d8855600080c842c000fa462111492076880401d800e01c100e00c1c01c02c0e100109800103003449004034409200c0f50415505081c98058440d01c0304040402d4004101ca24112080e60040c0c9025450700398186070350200104a51f61154040240f240c890103244041c1c229484840754041e02d9506044000c0d0803100d00d50002041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 424547931 1250 424546681 424546687
    0x608010f0b0304031403040302030714030409110f0301050105032d10090509120a090f0311120f1c03181208070c0213020c0118081c0b030604030c05030f0d150506 71
    0x2085e004032a02905d001400340c0a607690b038660400700d066000f0210001c140d02d6003030b4910444894000b0180003960b08055040145e40701074407040049206020f00707011070310300034401000356600a41c0075545c840340c24510300c3c40c40030aa410384001d020440c0d018140b849103071028440c02c0803901d140da102901841000f009141460310000790b4840111001c7c102000b800030700040c00d24403540d408801009406032243c41e103030716480c241621107107410f0501d00902a6415680e8060790021300d04c507442001c04060b00c080e00009000d513540205006103e400d064403240d402d1030381495410004000c0c5d000700e216064100900c0802041690091312600c100000c01c440138000d81d4031410001a1103004010045e96611440e5000740980240d002500031803005581e10010b002c0c412004041c000c12407488858404161805502120b00304d0000c00c3e00360348070000090001703004160070307494280078a0840381401e202800032060f940c400301d00b8103901921201c54910811002d2400005804100d070340d141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 424549181 1250 424547931 424547933
    0x2041a03010e062826010203190b0316060f0215090c121009030504080d0518120709020d060519081f3c060311061806040608010f0b0304 60
    0x18101c00107004144600d92524088640c0824010540d900224041c07138480d2156980711013810100541c8102d80402016601440340c2240c18803c4901c078602180c01d0f41e85080c1006803c0008200046020350103103e84242017503240824000400100441d545000202ca83c14a0090034460003212203142c400340361003030200b441c03000b0031844000541500c401d40b448142003441ca190880c0c4445440c0c503d494501c081007819800f60081c000e840d0007508a8034002000c0350112000d00c5500c00382e420a0a21400080c000d1802c4c2c0d0312901104040d4007180d66142c0c031002414204ea11015807164041d0741c940040066003000d00d0019848100039051428803464005220349511300c00110300d151001191302c10381d03101c010764800da807484d000c1c520301c038801c83d2441140818140c00340010350402100714898469030146004500070b49501501034401610ba00d01400a59001076001428214002c1c54280043e1103ca01820042500740d0318039417654580012408240019007004000c0c00007001000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 424550431 1250 424549181 424549199
    0x4050405060601030c050d060b0a0807020706020705010c2f03010b060c0d05070c03050a03020114010503010209010f0509030102040b070f0309080a030516020a030b070306050f0a030f0204090201110601080102041a0301 95
    0x60380b042080c00d020980d9005101c00715128401d42c65012070b150310303102000c02d01e000888094200240e56441741c10054480807000c0c0c4e81c0350030320321071300005a102240511032075201d400b400d060188035075055001a2455116032010840120281d4400d80c414130528210345402d00409150b540d05a8519180a5450348020340702e1400b82088018400d0005519040000060762540259000000d48a200d070b030310721740240030b00ba90780500e11522206100100b1a0700d410b10807030b40095416146d4409030024080252455007200000b194103542c01c0c4000940800803000030701c2170603c02d0131141c2c02210f15140103009165242c208141c150702c40c5240100080c1c004045902c030000000e140c0b80d2081d49880050340c008802d40000342400071550502810030740542000e8292042103d90b40c0310008810300f03104911451b440042e0444403405240c42c05400d0650010501600600d072680d8640b002c001818034003e020303440154543c2d400981002030820751034440106140e0180582d103594540407400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 424551681 1250 424550431 424550443
    0x8040507050a050612061807020c21030706150f170d0306050d1e0f110901051027030219030c0509060603010605031e07020c09060a032301020919031104050405 70
    0xc03810301000000800c08a1f982c41002d5442e12102080d0514203140a01c0002e499802a2108078064108034001c03148581c0407c00407401d54101100a60501c83d02d031304c1c3e10000d007480c0c800c1c14001200030080400e00000c0c842d440c4000c0d01004241c222441e03a58241c2134078101a03402840c082600d03004081c4920ba850000100301e01380c2051005000004003008403044124030134009001c8501004e02000b002a50110071940c110101c0b00c01080703130384c6c2d00b0501502e00381c40304a2100155110b01c010030340d0b000c0800a00b02c4c04105501c003024207602ea078080ba8900e60a10300c40c00c0408203040007041003103035045200015000c01e8416001c50309110001c58514003060047c1d03000d000003c0f002a1001003070f00c9008107189221000560f280c00c150790003035210b500143c21540500306e84d6000410301d00b00b20381d403002100e606c003040b10040c504032420500c0805c05124105015502040101a6613640c42c0e0707800b1060b182075000100580c074500d412a1101e0340605043c0c0194105420400419008152 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 424552931 1250 424551681 424551697
    0x70803030124030f050a061502060601020c011b390b0912012d1404080909071e030f1a010903060209040b1201021905070b011a0708030708040507050a0506 68
    0x14568040c10541c42034004c0c05558080e049203900d080104501c4140341d030000000c65445d00c0c50240d204d85820000c0b81c8900c3e04a80c03250143e0302c080c2d00e0015075442015a80d8884240035404030020080b50b95950300010600300300c000216010300400001c05201c00c2c2c000100c604005500142c071b02c2c28001c6100b500903408082e1184a06800080101d0400e40002400f001008100f00141c0c1e0814001c03001c0e5442d0b84001d0980c1792801d01c0c0442507a150b2200740d8011a0005d40c450b09159140041010180c6c0080c802020810801e0003180451086540c3c0305103610651404103035103104c01400412140c424100f151038400c0401c6e21481070360001a840b0540350800b034007507a60600000030034050400b8031703440c540004a45095007001c41041d40902030011403206203981410070004201d62034010044050504880000100805210001c0040c160188038034a103080070215168411242c200f241c0b0741c404605800108810044107000e218054401120b02a003400e06080104441e07002d0488 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 424554181 1250 424552931 424552979
    0x605070918110c03031006031107150e011e0225020d121b0309080615090703050a1104090c1e051206031e0709061202010e040213030203120406020708030301 69
    0x408450385a545030100c1c0ca91299030801c032580c1b810481c0d0400348007804c91041c240041d10b01121030141c414850204d507080b68000c0c01d100020010301c61560b00403c01c0c948040210740d070795042c0903000c0041d00c030441c1300003a001d800142c461a45910f03458100c6545120b28020303200c2c4180da0801a91500344040c0705540064210071010402407041c1e03400c01224507140c0d00c46135204c1003442007603440340d0444140c03184070b410354096450f400800240d00d9035500c411903226400384009102c891281e40002d60150303454602250042c03036224100015840f035040214640d8030354040121b4640c1240600c69a90175210900400701c0030b1060041550103102c1c50419411282c0000c43c50550b400c02c0913200c1e80e000341c0708010002140d101907135903420303c0c2c1c410303032003443c0c2411300005041210b07600c030150b21a01a114202e0300056101040002d50105880c85c050400201011025850804c101455108941c940a640d10300b841c10107840e000c0f881e4003418543d4002c2006000c103140700400310121070b101d0b41c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 424555431 1250 424554181 424554191
    0xb04050904030810030c0b070302070519030b04080906040306020d051f17030d05100503190b0f06210c1e15070201120f0b0a0e06090c0f0c190605070918 67
    0x44003010410740d141d0305c06410103800d40804191100f5010003800c10340c1c4260215665566034009114000400144100314407000c040700304040b82d1103d012030b500501c904580c915042d0490300050003034105400c152521507021030308090b0905d60b4441c1a41102c08a60303030440c210407403103c50b0388a10160280000d003015915506820355000c00688500c04070308602840381d4a03290040004291192040910901c00d03020110034112100140031400c9400100c02c10241c0d07100e07640034150800150203603411986408a17420b02100048880002c11038aa02402446900c00c1c00c0003584036030326800b110261001141d081840c0d0ba083c0040182e080c0010392951590b1035800143c0e000c2000c4a10704400608110b01103110a582e0740c400030401508072054070030291181502c6641d50412120250440d03d6800071441d40d600242c086c2c070589100c0103034245800340304c00c00507041080c04011020420b10b15034804c000c1220900070954864003900d4245900343c40d0200c0310f609050303c0d2001e505080d07030b51 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 424556681 1250 424555431 424555441
    0x603010515120a061803090509090319050c0a050f070b130302040c0201021312050625030e010f0903051206060a0807050a2c031b13020904091a040c0b040509040308 72
    0x148481e884042d08403604000303400701c41d00c101c005d4091140045000419643e0301050f64034007420f0040c09154000010360400780f107011483c4c00c01d030101e021f540912005000c2c50002410811001c118948180c02612807144024612840c10300150082000a03038140404c1c0407502d01d0b25224802c490301140c0205842c3e134030660a0380203101b01c00c081e00c0410742c00040465200441c00300294101d2040040324003030340d24590007203190303012022468400402c00040c10f10452203600308190000f0310718000521800b450b06904125842510b044000c0340c400318030341000282d20303820035500010070380f9010b1400d203180e000100102401005401440800320325420140e1141400900c4d414403215050351000d446074185016081d090b5034144039100310312100781100d49140c1207100070704000c1d00691003040d13100c1000340603420001c00180c10650307480009012809074003100b81c2001c1e00500f0a5101e00f0b1070708000001c001582c000002d40381040000300426111008402d500a0309854500207135290 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 424557931 1250 424556681 424556683
    0x70b0d0203221a0106030c08040b061302030a14010f0b1c06030606170607020c031b03010f050f01050111010513060f0e0d0e10180902030405070b03130b060301051512 73
    0x16005004074a0016010380d00104080b450400e02c3d2510540038441c070580e44c0344001c0701034540800321800003c1801d008a030000f601030184941001d801800c0c500342d044451020400c90b00220f6842e01d0395500c0e07020b8401410740540000e80502032090040f04050b051424018062050840c0b505204c3d217031fa9250487c082483d4071882c055a44420b040c000190340c1c0c5000d411a6002c0a00803a141c000c4402140f00540009040c0b0056400a405007000003100010340d840d40001c400220b0b015502d407442050680420312400b40b10f41c00c3c42c3c0380e00c0fa10354100400102800c40c84140d0304140d80c03411050058980c0c0101095416a52040001c1100108158024041d00e54590559441d100b030302485400e0641012440c11310b940161002d00205c0946401100e800708100104000c001440b40d00748a010b007070740c00030740e031080c014411511019900e40400c0e40e1980b0480702d0140c00700b018a0200104a00c0600d0540c100c4400c500a02c01801d044014103c1e8201e6040348a124518030f82c046168854 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 424559181 1250 424557931 424557961
    0xf1103070c0b160f0c051005121614040e101502150c07140601032d060c031b080603070603020315100e0a17061e04201c14070b0d0203 59
    0x39115042c4c01e0300311114507107000000c803e4020180324040e811200548944590283c443c400080c1c01d0104031910340705201c134203150340142c0c5001082500f40120788100ca1b0007000300010b004020350303c0c559160101c401901104d280e0441801400703001d00090301c040e400622102c40200714400c0c0d0f001074458002c429054401c4400c01800d4822640004218031170116009040702c0c0154004440c00028480e044c1c10341038002041c0d8108880350449402040295100d07106081d0700f800c002480c4041001d94160811203121104001901c2d0303010000301e0300f000d010610080c01141010350075401c06600c21000c07003240242080c018100103151a40241c03040f01909100303030300074003040310b06911945d5102c1e28000d032100600d128410f40010070031800c6040c0e006020244032845501d0180c0300d96580551810104078409d02c0c80702d4040b084292070340c422504169103500480070034036400c12440c0c02e08210344640c00048007130b00842e1041020300b101071704882d0ba4248c05100180d4a0f610b01568081c107103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 424560431 1250 424559181 424559183
    0x1080f031920060906091c0311040302060415030b030105010501210f06090f110405030a0b0901020705010c0c0317010e0a020d0608100608070905040f08030c070f030f1103070c0b16 79
    0x500c2e0b10201052501c0c0880c05501540c41c900036135180359609240e603031791a2200d400600c0300c5030200300d418800901c254400504010176800c09841c19980ea000210a40c001c0e0704a110030a141500c4414500c1d0076100d071b0604c0303100c00c0e80280050761400b000a80941c00000c3d02100150088400301d0101e03046500141840a00030760400606448038112401880c0b10740742524064900801d204031000000b0564088540040043c4441181507542000c0c4000c00342c03001c01c1e190340a021f08400101e00b030148071140040d65845c0549000b45042c002c010a800010b984988182c44c00144401c400e82c5401d203a1100f0407110150b40c8081c107242607801800607601c03130f039010301503520403200030111500000d00b2200d003003007262800b9441e52031660485a05950092180c2c1124100e0070001d12200e02031030b84562000d20740c508200c0c15403103691401540c00c00850008001d03506282c200780c0c010315070150140034500114102021541c680c210a5154000e09016241c00319004c215100315040c580f6400d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 424561681 1250 424560431 424560467
    0x1409040311011b0f0203040308030a11040b16150b010c11030337090605190302090310090c1a070f060b1c12030516030519091a01080f0319 61
    0x45201e00710300303a401004001c5244009140d04c4510103110744008143c400b038a40001600d85142c4451140e000200020190020300b140c003408001007140ca002c02401214100010342d411001807407070100000381e00c508007140c44900c0c0c000c82c0c480c240d0b40000c03501502070340103109041c0140d40a0002e49140a55110074070080c010134494030000c2483c2c00480142030301c02d00069020240103405035403070360040c000e080003c0c0303090140780484201c4040060a6440c2c07030030010b00d080d014070007080c1481c003000311500090f134540d03440100b003100203900c3d0b40043c09030000c0034040301c40142c0c3c0300328203200b0780c50090000031460b0300500c14003000f0b42c4400c0710000000d0100e054a880000d5a042d5406a260250b41100b4590440c0704507038001e0044a114511421402e613100240030710560007420043d00c22003610304282c82c0c04443c10300511403200031500850049968490b00103e801131000c050f00301c05500e0b00109102001c07500b001007600e01c0281c010740c00150080c0c6c2d001d0704890081c2a90300c3e485803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 424562931 1250 424561681 424561691
    0x109020408191b06030b090604020705060f0c040b04150e0303090d060f020c150403080106020c010906030504140607020709050c0406082404050c03180708031b0a021002010509060a0501140904031101 87
    0x2a0941d014000e041b6050341c6101042d44c8210400040b4001d2050103049504420700056091154a0090754044400e81c8140c0c182504e4141706416600a0b400803641c40c10030701c80c4a00c00e070f070b081145050191001c1380114606948140424000341c14890300078a8151190f014146481c3c0d96019580000483c004590518034041219600030106407419004111614000b0401501c0400d0342d040190b0103131141c0345403c0c58540c048004000003042a250000b1b0b021041040580030b2094030700454417039008064843c2490009030845001038020000c1000401081009a0700501c50035405450409818801040a000801c0402c500c000066115140204000c030140c800006140109191040030980d0f08002e40c0180d6910307868007820301c07a9441800000d222503040803814007002c02741001da688032080c59020030011400c0710340d0305003d83d44900401c901d40404100d880d500055244085c4443e5240000f125088a9001100750045240c00009000d2500503038045072154141002004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 424564181 1250 424562931 424562939
    0x121b030903010c0c15020301080d0f1e0807091415070f0f0c0f0503030c0c0f0f0612070f180b0906160b06010e10050d0b15040902120109020408191b 65
    0x410013181000f1500c42000c003034041242e15007803003942e050754000f400a050300041408192004c0101403001c0b4100143d61b15202600310310300313500e580d01c1852916548030702d08000c1005004000c87d83c00c14035802500c100001400d80e2040441c0715910103941ca000e81e2400c00c0d0a1400014202ca0806062a81608400d008001c1c0c051859000c9460384280000c0141e240d40c1019103d104000e82000203502c001c40c3ca480c140383c809420924803100030a420102c2c120000854816000742c07198103103041c0043e00b08180ca6421001a1111888500d0220401011403002c0560303240c140c003407200d8060001c1062511500c44104541e0b02e0250040d001e440300e8020318258003109000c40f401400200c1181021000e828401070310880c0c0b0320039440c1c841c02c01241845550050409040450740b141204a4495000400798010000303071141650143e90340302c090001034560201a445140400d1040008002c1000c01144040c80c60103e075604044084060502c194030100c17000303030700c06417152b0008005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 424565431 1250 424564181 424564187
    0xd0f0e1b21070807170d0306290d0c020a060c030605030d0c030e091503010b040203010515090a05090f04031b0f061806020f13050d051c05160f0b09121b030903010c 72
    0x4480461781c00c456410031404c03000c4007566002c3c452018105001150032508010a4120606040541014a0800c2a245480703c01d554065502c0c3d809070b0802c284000600a1501035000f501c24281030a01c892031500c0003090303603998107103005010080c100481c003041504c60080c1045804c0c0081202100d4201860505541101c1d50141440303586071030f0030b042c41410103001741c90481d58010684d030088600100315a5042d840501c1007039011002d0700020070640e6614120a0040502c6a0107070300a16107032401914111064000c505000c07500781400c400695032400031034045901c01404110450000340d80c0c00d4080c2d4400c4002c059600114016005203444000742121840300d00040b14403560ba401030107440820710b40040c1c41604040380045080e0005c0d0b82228110039176151642c602040c14007c0c58503403400400131142c9854010090701400711201e190354201890030090008815080c1c0d002c14a44190001040c07500903500e210241c03054140152120803601500904c6400d507500001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 424566681 1250 424565431 424565459
    0x1807030c0806090706091e0807030b06100c080a0e0f0a06180b040f05010e180901021224090711070321050f03040f02060d0f0e1b21070807 61
    0x21a060340704140010f010590001032000440d101910f4009455040c030520a409001c0641d620300400580c290000700b5034410070002c2c00a42c0142102c1384581400402c000344144e03840c810b02d04111022002001141d5081e085480864a5040600602d001c5402280324020102049a481040501d00141903070708040c0c501c80903501444140e82c190344034043c111b203034015402140d0f010f41281500f4007281d4010304c118075082030700401076106010a204007115050702202c2e002c4c200e03500440d03031046100d14002150740000200780185080d00507030740102179071072030514024401c101a50210360b60768012040c2d000009921015902a162a030038000905105014458601095901c50007019441038080c1c0e01c404410f030304194651b44850b1201c10701000703d00f0b000c2c0da128800304500c241d51072492003010010403441e0000700390b0900c0000c0907404d003101109100800004455107107020350b00e0b000100e400707001e40751105604c0051046100d16129080e00552807903c912407020078540d05003161 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 424567931 1250 424566681 424566689
    0x80f060708010602070b0f0307020f06040f02010905010306060c0f060b190503060114060a05090301020409060e090114060a05120c0a0f0e0601020a0c0909031116050f0303030c040e1807030c 83
    0x36000c070a903038842d03007240d5440d100d114800e404641030285d441e159070100029a000039a40c41151028a200e42c4800c0c2041d1003910226100b264103000c0310f04558203c01c2110044c03a007420100800352420201900d6031080910041c44480340b00c900404002c45640041240000600b420540403c1050381d480d4480d00e501a00c2d12038031622000044c1c1b004816404280280080c05c0b85051580f030a80a0303580d900820782055041d50280000f0a609801e4455800203003900b40c0120765605142c44482e00b100c02c0031b62010b0045d090f840800c1016154a04a60205e83e000d65100b40c03607901d0b08005038200b1500030342c280e501001155000420710f49144840e010340303e04071407480454640c14016a9110003a01008200055114041119010302e0b88102c3c1c9050003410b108035200380000c0341d13a04107400d0300340d03401280d18001802e120a0405101003011098242e0040d849c50601100131081400342d40318072018940f200700016a00680000100c0009940c0c20464081d079440e807911100511003809 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 424569181 1250 424567931 424567937
    0x70902040e0c0906090904170d021801030603050319051e040315050f0a1107020d050d0e0315040b060a030f0b04060506010503070f1422060f08090d18080f0607 70
    0x4085246206194119101401c0003484c6030310305402c08060141041004106544544159010720203550301c503001099a001d140c0001a56924130103040d035840c8000d00c00d01030415140c4001071002603000011608100d081c4980d070780480c5e59031a81216a84620075500000745e14143d100d420707080200c405001a40d1140f16042d6175059803a40e0a4100c40b800c54190706003440d0503001c00c403601c0d202e60100780359404040c010ba1a0040c96004030700310002161b821919507001d100100e518960040641c101204114042e18242503054142c01c048000944040c0101d19850042041640c412030640025540300900004111003801c20401c0042d040300c040e1500c41c1002c0015074650310600450388140b585854540306540f0364130040710040200c408800358150200040d069107404403402a8404902c003000150303050600c5030007000071400c20038407018032480100f444440706002c0707030400088905160900c051f105012203111207155591100803207000b072030003580c0864008510584904000e072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 424570431 1250 424569181 424569209
    0xb30060103020d201e070b04060b0406080d0e0a06020a080304080a0c02030a06050402030d0509061e0d2406031506030e0109080a020a021f0509010809070e0106021f050105060304060b0103090507090204 88
    0x45600c05e584030305030000b04041d1550002a001600329030002d141c0942c05000000e1075034452007090701d4440404071441c0070902001841500b0700d0300200741d8025007814406401501c6103030b0b82c0d212541c08054030080004101085043d407444c03150f410a010356030000e003140d00d201c02d1810008010702e0240d4003607004c0e010b04146060442d000c1e40859210050182c0054501159400004206101c1402490071031004001388103401d09180120b461031260408140001d0b003081901e840e0020070341d84054249070038018103004401c0301c440c006d0100d0341c1c2802e001c0307286d42d0096070711030042006000050060b100895800392150780003c540344540d00c281ea8000c0c1c144120648814038002c089104400034038100004d810f035501c540c022039040710010702140c2c140ea86407415110000003d8201e4001039000010358403000b1580c2c0d80e90300013000024030401003941003c0c00b090103031100900281a19454203980c45560f4442c1d4030581b00380b0f4204054036a055158100b5a000c3d5100d440b90381d0b1041200c1d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 424571681 1250 424570431 424570477
    0x115020705090610030c0c080d02090103140606121b07080a1d060412030905030a030305070f1704020105030c07060507260112060e030f040b30060103020d20 69
    0x2288099000301d80040951503c600305084c2100a0940b002d260420810030070f0f010f40002e58480094004000c0401002d0f0b111190440010101c811000c1c90010065492046c041c05488541c00c440f8140c003a04200000e0b9500c050b510310b14400c4e600851040300d0310000343c403014480c002c000340003007403856950941349013a8860300200c00c190741164158440002c1008000d1644902c0340449a103120741804655199030744006400c00090380c1d400da0110ba2030b102003094065116100300f401f50014140200c4044031118022500c3c3c6000344020305000001002c1000f68012009035550968405000c2c480741c6810f2000030900a4005180c403154407005090321002d4500b0030a050680d1007800c00031082c2c05440d15031901502c0041164002d602080000d00700d55012800200060701070380098650fa00340c504a0013007845489080904015035104107800c0110b00a00303843c1e0041800d10340503854034803410000000b00010241c0003203c0380c0b17010400421030760f80c0016000040d44065425900c81d05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 424572931 1250 424571681 424571689
    0x3220e07050c07090c02010609230f0c03160e040c11060108030c031204020a0308120105240d0c02030903010c020a0b070801050904080d180b0a050105030d0f1b02090115020705 77
    0x911040b440b50350804802407009241d00e5000c0303507400a01e440089a980e40c0c0d012248221500c0800e24a00d59103000e5070000054208240140c01a1010580c81c4040c60200300d20070a600000d04010545451001c2107407806100f6540d44408400013001080b07554480e5201505840c000c04407031045004031400012102d0b404030a80d5007040040b0040c502d441c407801802e0b14194802001240d02040706c0a0110200b80c184001e01140c506052040890354101000c0000d1007140c0c0071f02c016100c0d14004045158080c45054860703000d06140046001d0342504800d03410b50080307403440707a0598a03000c020280980c0c005403041d03a56010b00b401008039103401c074007194100024060b007a0020358003400300b00040c544000a2140d030307a0400c00010a5040d03449440904c0840e41c1c2c0903100c908402c000c0c0000141548141030042c01c04800400441003000e0020348045141e800800c1400030700c0000d0866201e052088800d404d900800580d0651b07143c100500b159200440390000520030803002050383e082c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 424574181 1250 424572931 424572937
    0x110307090b161e0b01030c0f0506043204110a030b04060608070813120e0f0108040312180204181506050108180f0706050414041e020c03220e0705 64
    0x44882d40091008079480310303103141d90a28842c02140075880f00c040d010980001442e4041c52150f103040025900d0084d107c245c41c030b02d41d00300d02d10840c0d08000400c562601004070010240a00051450303136a400f04d5000c0350245450040c540040c14403207000200035004006020710115500c0811a034501202030000315007507401648007080e81d02c0c021a0744e0500409105603c80001c03d0101051480c503921501c0d12100c0050410121380320511104452505c00070203a003400c0203103055103071460151401400200c6800c3d8801c04240e48941c0c150b20185900c4a401c1c040707402030001c0c40308001d00241c1031030b04001131405441c0321304400d0704502c3c15251402028211107051751041031949a81d0142c140c1041ca220101529120b40c0300307280907000b801e1240000410141e106d09880d18070b02800107070101244408103104518048103100c4010600c0f51311540480340301c40040c0c0300c852220f0407518510401c40c00b0703040380d11f11090110300614454845000d94465010f8030100da03d1307401058030b842c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 424575431 1250 424574181 424574197
    0xc061b020a05151306170915060f040603050a0c09060e1905070306050916080c09011d060f04090905120304021e040b0a030b010e070f09120303020409110307090b 71
    0x4550980400052410b0f0300340361070440f103500c9034524100c200300b20100d403007491340d0048010a55204060383c20020015005600c0b1600c4006040d14a282c810541203c080007000786108203182800910701c4c0c2c44543c025805154440c01300c600030b10040c10980c404403036602c102c244260a00201044c98072480009500450481e03200c4020310445601c2030000d8100103201e5010503640715400161940c58062703c034000d200d5a086040c0000180c8401800f244000f404540b0702841049403c2c0703070717907444800b1039040000320340b80c41100c00102c1c0014400b44500000b10030250700101d00400c00d10120361103001d031188500201c41c03582c003001c02400014001100c02a5105640c2e00310303003900308800b0b0f403594083c4000410001c2e00310100c100048000b2150b41090700c7c5503244100500c8983c0500d6078281e006503090501080030403041c10014882d800318099083c405101c009500b04150090701960090010746038180b101c800c01029184840c0c00480f401e00018a421742d00042d5006184c046038650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 424576681 1250 424575431 424575439
    0x1515020304051c020907030903050f27042003090f0111030118090317060d02040203070c0605150312130819290c070f050a03050403230d030b0d020d0c061b02 69
    0x750345031b00e400e074010200b460342a4180001000160705098045000b031a00c1c4888160000f01d00701f2544403003c1c01120228403500651810640b00e05000d1001c8000090052103207221b40d49549400c5941d061010820402c8a298206008a154408144040c1d4183d0b401031030013400013181ca1030400140c0310034039409030110704101005045c54194481055001c00d010300103440c00301084e03001c00d080f0790044428600082c0e2010540c07007000400e02405801144a04031030f1a058620b00000c2c2d11407820f400c401090110025004821481c48140300006242c200c0c1520f00441c2c054400c90440340f040401201c2c540ce8a50b6120b0b080c042c1400400300507500c13000102503540d1010b0300800164014003054613101e1861a9030400148100a18050140319540d03c5440300d15520b002c2c101841c1e03109000d01705001e015050000c03503800258070700c0f08110f00e160125003400c455001c02c017201070340c1c80060341100440800c00140064418040101d03025a0b80b502c032106072401c0c0108107004213450081d80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 424577931 1250 424576681 424576699
    0x10f05040f0b18090a0b010e09010e0a02160b10050a090c0c060218030a060209040b0102120702010806010c02030a0515090307050a080c190b1506070b07031515020304051c02 76
    0x38032540c03407001e8020300c26a16401c0c000c1010314400200003100c05c03600301044a8440048082c0d5503800411400403800a852480403541051780700c0301c1410009126150b00c59021813210303074500f008100c202c41d02d50086000700417400c1c100c0d0140d07543d0f011409014090605030500140c41c4041d4030440c1c103130303280b19610a440f841165071110065807003c0d80e0ba00c0e2082d208201885280e03804d00010100d64459800160b0700ea407400103020a0b20403445200d410740d042040c1402c4103800200844420b01e80c2440d01c1d8003660f0f20000143c0d1000788285001e50144255a4544200704c0c00080641c5900d04030509051169258075405030303a0b00c180480140207030890308482d40000d80510250580103c0041600c0cd003801008010032800c4240c4401e0711f24881c00c1c0c0c103000c403201c015071000c4003840c1d041c0c5035549052215241c500000b600039000204055440042a447e518600c003608003070082694681c03901520200e009603a5002401540e101e08420030924110400c840d8000c00910390103007034800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 424579181 1250 424577931 424577939
    0x17180c1e090604022209110304020a0308070204090b0106030c020721030305090705040c02030414040204030c03081e0f0a081f0630090302060f06091302011b060506010f05040f 77
    0x255810082c051540080d000c0c40500d1284004134844290076281800104c2010303d00013034a41a940480000c842000d0104248070258036050302000c02d403500401c04a55628031480030030300802202a001d0440c41c11800003043c1982d142e00107200b0f0040d15400c03154129151202da40d5640858401000d091840c4180c02d030000c4e0007a0421640710210500f40c860076941c2d4070120b0140d8185806200c0140c2000405001007000c100c3c28034000b64054031308604142c01c1d0b90318004a02940d01003d1b00702000130608001a004840c0302428180b040c0b40c2c17503a105c01d1084d20240081e0410712040010555000003e10145000314039031510107010300d80500f007540380c080280c038080c000320311580c0c1c4601100d00c0886200b4071a2005e0001e001c60740c40000d040015410024101000034207083d8442ca8158203001d4155104802a9041181c0e80c1c050000b4050910040e1800d60303040e00c500940c400514010341c01c0c440320b039000a108600a803906501c200c688074046030148543d01510910040c103200900c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 424580431 1250 424579181 424579189
    0x80a0c020c131508060f100f03080913090b190b0303070201030c02120301080304060318020a050112060e010e0702070602030a080a09020d05031201061b0c09050717180c1e 75
    0x11541c00350311800080c2415043d251545a400b180c02c4400d00350b11002c2840342c1e0090300b2001030750080d12203225803030017401d101c552100c0c10160310014041010104441c111030380c0d520303058020384da140d200c1000300320403900e045403010700c0480341c0c508041c000301d00c0b40c10b251141d4054081c441e81c0041c00340d4503043c03150740154007d01c4003c914070b0071841282d1100b558016004021030280521200842d10360345400c0c0010280c55500c107004405601c0301c0b50800c011307103410118600b5900242412038420800c082c801004146543c422601d1404031800007a84401e0312410318001e200c5682a940501e03101d51050341e0700d2003107889500026840c000002c2041c035140e0b10200c041e51000309413291110b92030310b92078559042261150400015076004000e00c0b0303041000303e0f503400701c0c00700c0e0f000201440c1c2d1102000050180324885d0703440d403a000011074041c441e0741a54842c4a051402d83c1d02d0341051041aa021a908120044d45d4460300e615040c0c58500b68459112041703c0a0510014a280100340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 424581681 1250 424580431 424580449
    0x330507030c170403081602030d030605100c1403040303050d050f10120f0f0615050901050109090f0213030c03060c05030408030103020d210e0112050702120c030405040c0f080a0c020c 80
    0x4600b0001400b000c8009801c540040404d1038015000e050744201600425042000c66901c1006251820348100043c1c2c555000b009100318550610b001c01400900b8110102c415040e00c60001f8080018080105904140030f4070b00c46428103000c020658030300d0500a00c10314142d4032801401c44001d030402800314000c007105421803142d01800b030311903c00d903581a10100940341c00c07105103031240b060f440c0c681007a5507048001d107002c40704003c0710f502d81400039005000500a01000645503d40c03c507021066404a411003051110780000300b560760b0411b01090b0902c9d000869469040444a11003684a14190b9000e01d0b085420700f45103074a0341c0c0c2000944001610101e5041009500404910100344514210142144c540c0d0960304008400100a40b404031a80a9410315203020b100445500050342010210384125480d80e41403886626890345c002d540c4400c2d403243c14480f5620581d54014001880c2c0e5281e600c600485482e5000e54100fa600ca2500860050b4854018040b03203141290507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 424582931 1250 424581681 424581713
    0x6070302030d14040209100608180c060d02070b0a0209030309010e0f0a15111209040507120f0618090f0b0a06030519050d05040e13020a330507030c 65
    0x489107000285451807003603e0402c2c40003a80810740303100b00000d50400000b070301d034040188038405203840c0c03e004010f000220064650544c0421503040003125510820111000140c003c04081d02c4d02c85400140010750b119800c02c4801c08a80320200b2044890703802515a0288010041c0d030034806a54011503080350406e902c65481a000c001060080c0c032080514409030103090611401c0d0a8181c80280105182c68041c1c02d180e80b144400c43c1802001c0030a40303078400380494000c500c507101c0c0402100c0e000031007400900d20320314085800d9404612a480780b8200c3da00c064005522508401c51002101e000c1e100c0600065090f41068001600c1d443c9010313882402804000740443d2a378803072500c0c110315030300c9541802071052104000d00200708140c480a2485103812441d107420130078445503c03103010308107041110147d01d00c54110355400300044080c0640c0b4144c10a0200c8a40c548454070031501d0401d1045840e120200c59102d10070000c82e000d4582640301c0c004030b10b005075600c4940401d0210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 424584181 1250 424582931 424582933
    0x20a0c0b181e0c0901082e0c030b0f010203041818050f0607020601142101020c030c011509110f0304020d080703021f051501050903070914150607030801050d03090314070f080606090606070302 84
    0x1007c003800684a1000a0040c40d40c001441d900c040050143c5007100d80080d038103641c400e100401c91b041201c038601d42581c9414002140000e241c00103410b140f42240c40c0140240079003240e44140c4200000c0b480d2080741290b017118150f9070380d100010050901c0455854015500c0c82c0d0000903103a50a04000c9401103c000051428801041350340c01c6400000c25103884d6519104a007110302d60307030303911500a06400790040044004804030586580300e180c5c295000c1041c0400090f09550301c174044081d645030402d1060307541c3e03001440d0003521605800980c03203050366400030441d40800c05100d1103205540703000200d154108400015603a03038008201990740352051a00100d40b5212501826580c080c2800d488070440c21700f04004500021000c02a50040d1400e014031004281d0254042c0d0441d802034079488200329031030031300b111041842c1d00003514500ea40a21100a40c5000502d034045481040100d5a03031501d4101d5030780c03070b017000384e8089920840c007001042d0f503072404000421103503110740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 424585431 1250 424584181 424584253
    0x30209030c130608010608030a0519050d1812020604050705042004080f06010605120601050d0902040c020c030f01140403050c030706060b03070f03020a0c0b181e0c090108 75
    0x1000030b003401807009080480280ca900080011070b0090007414041d1915a02450030f002c031006009180307002c0c9882a90110380c0501c074401801c0d0107407046810900c810754080c898141d030014030300141c2d4000101101c12490740c040541c0d10910104281d801240c0c440054000d140c42c00e0100005080b41c84101d4005d10b9250440000007401c500003400141030030700c090040070200d403a0039810088141d000e0b80600c0005c001d0341c5114501644442d500c0202400d14507142d84050a0210050803600f10007500a4606a48000c41b01d0300010301c40c00d550b200310115035161022008250a840807043e5115946070502c004c0390009020700050300030741200710101c07428501c0302d440ea102034400c84e40c08142a4003000007070046d5180e01126a035562900703801c00350700c1c240e10300d10f00130f04103082c1c810050003011404012850b582b40d100500c80c944080ea0703045558260144150205411440c00c41660300c1c41101c0c41d1400b54100040042d04070760004000e040c4400a24080c410724002c14031020314521040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 424586681 1250 424585431 424585453
    0x13080319020712031d0706031d0a0f0b180604060b0613090902150a0f0e0321030114040b010f0c0f0209070206091b060d1e180515010b03040303020903 66
    0x688090164940149224118510f03052005401c841a100c0c1840c007810503200700d5400c081001036100e0883d10546000602c043e92021382c1c050b400c2070113101c047e03240a0500210180601c008520404500414a1514075250502e4110a00b6941a03410505401c1240010003086440d404805806005840240343c030302d00b203925910148580e004000756544c0e8880103800c0d800c00e110a146a00721660305103140c07a000c90405007103102c902081c2020010740320561440750b1801e01049407442c081c82421407a02100038410801303608240140704041e0381c9010103428525160240c0d544025060315003101890b01100c00321416051120700f9a401c0001e544c031a00161902c0001a200d030b0300580c00b500d1503042122038181410f000b95200b052040c1c01d5044403e499650b0012601d0f090788005000039050132850240c0c00340142d06a0990001e85403120000d601c03111040c3c80c5100740d1050b4250b032503858100101503008002805070300d014070018030010300000c0c0664020700803020014101c070103103020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 424587931 1250 424586681 424586731
    0x4090203071a0a020c03030a0c020d15020f0903010b040b09070f0c080a05030103120e091807030803010807030c0e0702120d0b1f120b0904030f121b080609130803 71
    0xc1d250b03095401800040c15040280d41400100d10a0707034200c000d180f6100071004001c2248039500d1021b4814680e0b0040300341000400a050340c00a2100d80040d5241c800c000b9030254a9008901450301070350800c044910503161612a02c0e840506c020401c040c1901e17051411610b5080d81003400c2c00b480305200e840d0b400f060103500604042d003055594541d50350304600e81113500d0a20010350005001c1317000b850902d542d5450381083e512044540c4a10552520701c0d1116203480015840a0320f03404c000000401c900001003176040030b407130191040760a419544d01c2a40010b050840316440160061401c8442000c0180c00802100ca07004c0c5e40412694001000101c0360700310036043c141c02c00311980e424011942c0200d6500c81d480c10346d50b01048110044000f040a01900600003001c1007011101c600810740104000198130145032000c0024008008182011072880c0f9070440c041887c0800246035890042c40b01032041941401d005115852565031105030b800241c000103441c09051904d43c02040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 424589181 1250 424587931 424587959
    0x16060c0503041a0f07110f1903080a0309140109020a0e09030a030902040b03061e01050d03020a02130212090a0308010f060c11130f02090411030c0f0d09081204030f05040609050409020307 82
    0x80175100c01b25517420484108091880d250506ea4022810100c43c02c0d01d02e03810001c4a82160303044030302141e40304c42c440c1d8200c0050847c0e220080c81d08421560010b5103200540c40440d000e0b10a44407071fa01142c840a1203c20140200c030000c030554410070035074551034869004806618409000800c0b5541484002410150212170100701a050101924851861520310500608044c0d90840e00d0582540b4000e44849660701d0190150b9071120f0000c2500e840d990484085001403403030b030052800c0c682d2126885103031051094000814030000402c5000c1311900b000102c889036101c5000a441c103aa8010220381c10142c03a0394801c8062130710b82981e01480c0905400c0c00c1b41e4010050381c0700043d00800013203454580240e5001402070080003100b9040c1070031510802105800103803540741c5442400e0113046003400c0101483d401141c40c001442c003e1358024041c0740f081c0c44030303103591044100403544c0d4003592003000002021100100310300d08241e80700b00c402c5030000d000e032010140c4800c240f00e40e0503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 424590431 1250 424589181 424589183
    0x90103080903100b0112090c17030c0132070309083403051605011509020a0f020a03090b07030909020a020a0c06021218060d050916060c0503041a0f07 66
    0x88000071080002c2c6070520681c284103800542c00c00040104400007007a1a0b100e4900c500300b1540d880c404801d10004e0179600c0005d280c02c42c080e04400100e00380841c0c880c1c0007030444030400d42c2814075180f404103880d2900b04002090f41d135050b50400c01c903202c16203800006800e100038545d176920b0901c0407a005030000c24a0000710239503d80354048444921280d80040c03003614211060182d820310019610004a9050b0305001c01d40700402e6070306041950041100800104481d5054480024044010340160144d00d020361200c0031800d01d41e12099841d9540c0040042c0056440c14052103030080c00c00c060000c0030b02903d004142d080d21206a001284d100550032070140c1d100960201c10403003100d1421018002c05e01c040c00c00c4440c800044042c074040d00c3d42424900d484486080c202391208003c1d40c003003586020b8240628203001e03d40c240c4030380d082c0e41040c0801d0180b803004900e180c000c0b0411800503a03c04025880d0514090103480300e021400794510284d982008450011810000548030203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 424591681 1250 424590431 424590443
    0x7050d06030b0601090605040b0d0b120d030903030f090b0105060c25030210210b2205090c0f0d06020a020a021009090c0903050307031409151b06090a11010e090103 72
    0xf42050f4001400c5e00c106a4080000c005040105002c000035070400e582c5500c41140010642800c45400244a010191401c00c80c91065007044050f0035816007280044600940381088030203160040b40d010382e180b061001c0d015003481001005941009001820755404800c15107070624461021030140082c100301140440301d01d01010700551030004a20204000c8078100703401600c10806905111500121300010280d80e100c005001c1c41d140e00c40400100d80109078001d15061174003203194001c10043e26809803e00c40c4210f03c50803410403204c0d080740c452000303200d81c7e502003a0b542c0e40406903012455560450080302da09a00613201c0c42c0c0300344c0e5010010b4480308001e034100301e0542c3c11114105000002c208002004001040012003101e0307803e905482d0200e01b1096800c0040103d01c50f8215441d00720f2a00072141411301806000781c942d0405d100007001100c0424418180d42e01015506403003180c1240e0010307400154a4000c9010951040c140b40b803407428500005280b00400741d20648803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 424592931 1250 424591681 424591703
    0x50601050f0904120c0302011d030a020d0305060d1e0f120806010f08040b1e01090b03061005011e02070506130306051e1501031104090603051203061807050d0603 71
    0x3092411698002036080180c4101d2024075180d250003000c1144c12240800384400508840107040c800c1d00f09042565150703031140c020312006400c06680764450341d9440014050b40b00f442d40403d20a00a113401800c1c0200100c01c5241d0700d44a02c2110765180150a0441d0844188100021713414080718110601403040100076601491018010705001020641042440e2950b001c000d90003140450f002070b003004401d8119504d0f2000d0a40580c0171044201d01c00c05003000020f1109056000703041044d101340c1c00c0d10899101c58204004030102401550301080080c1002d03801c2c0340c807240129001039010b01c1110011030f618008035034507a0100296001c000e03030444050082c45880d008090308000400700600c02c4000018850103c0c9001801d00049654034040010f040da01c00d0300450f4108004451282c0d072165201503410042c81d0a104c201c41d503006100c3c2c40007c10020506803403044801400200380f5461460004451307034001820f5000303210007030181190000203889140041c512881402e54 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 424594181 1250 424592931 424592939
    0x501060e120105010b0f0a020a02030604053409020f0409050106030203160c1104021803030412140303040503120402151305120109021c17030a021201050d0807021912050601 76
    0x14041a000c000500705070306000c0104841e2022104a42c04c01120b01c8003c0e0300c400c101c0f4002c80c1442040c80c0c001e5410303c01c88051005105020544407100c4e10070088000d0b40c0581480e4030001c04208050f000c18410204504000313880c100e800404a018990303080d6894140c41e0b420302d40c102c0f8801c3e000070300081da0100c1040640844440001c0000b00782d8186861100d10315501d21001c5401e120a050051350041242000420f03290140b100c040e82c000c003983e40301c40d1146110b404607114000300b0381e0030a070b0b07002c1100c4041c3c0e00031003228052034000c00550301d441540c00b070f48403e03032001403c100c2c0c100d00550542c1e1548106000035110b40d105142c01e2100441c83d002c101720101803c2103c0c3c0c04c00f64034044100c001079035820b141a0a1002550880011150324100800da0b102d54201100c03e20384000100f0585040705d5000f8a41314444104d200100e0341caa07028010f01080210008068090400100c0d0141c41e100a01c59200180e41c00482c0480c0e44550b2140114403592030119419840080184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 424595431 1250 424594181 424594189
    0x30912020a050c0d020d0212070f060210061205030301090507180801020d0c02030418090507090203070c05060702070302060a1b1202070f050f0f010c1104090c082a1c060501060e 78
    0x8030201e5411107009240d4103a41d000076402c080e07221b000034840d002c0c0e5081904107440602002c0c00804c00c845c2072502c080da5495000e51241d0440f107541c5441c2d450400041548100301c20141c104642010080d41168203000f4050020034000c0d01c00800d00007091800441350080d040c904e0b01400860700090307240d84800080d0020b072045191038000303541040c0000d11a42c4501340300c3c650407820a80c1e011800c1110781c00c0032801c1041e076800c44006540000108100d01e50441b581c101c519108104440c01aa00d16200b2a207034121804020b603c00020000000b80c0c500c680c01c00e0503041050546030103258070f1581c5004000d482d9000b210050381104c4c1040017034202c61f00c040c900a0109450901d215604500016110701024040354140b00b9000307070403000e0150318407402c03c035224054010465561103050568202c460345c401d1002c0340c8205032031654004e4030307180100484807203510302c010252648010032505060907501078110790030011030300012805078041ca03402030000da2540010032990100384 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 424596681 1250 424595431 424595443
    0x70b070c14010605010e0d1104020d0213120b190e0708070f0807050d06020f070f060b0418020d1202100204090f050601050f091504050d0606080d0e0d02060703030912020a05 76
    0x641c240d241c030b5030810469802100c5c0d440c501c10129041400c03080e80345000d00d1003226010810f40c1080c400b02c0c5401041c81d80c0d40c0103140c040401c2855464481c1e81d5080c3e80c21070807150b18001c201c60700d1240030801030b104031262107120080d40c1401254003600c8141082c90326105610403500340c3d00840040040703000e1041c429010b4503950b0060103901d82400045442000c40312402806290b0000e400d203458424030058a1555a1000c04500103034614102040900b045009141c451890702190812031320040140258043d405445500d0f000c4403600c8400d4241030088450095000d00440c061000a4034401480903052000000403c4100c60058204403440241600c0c1400010403225118000b42e0060b00c04128003160110495041c6101c481014052580150741041501610310304010b00c640080098802c410101d0b240035140800c01c039003006000c9805904103020303004020250034080300030f0002c5802070902060301c0100c0e035a08400b1110000f90800144c2014070260708104040c400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 424597931 1250 424596681 424596713
    0x15040b1e0f0403030e0f030a0206010f05010c110301110c0f15010302060d02030c091005071104060f0909050a081303170a0e0913020303040b04090f020408190602070b070c 75
    0x100c80e51540503480c032584031005000846848003040001c0c00301442a00321030044080700d020798031404060008903a9035004402d060015000c2e41002190990402a500301203039416910800802c105e03071a001000c20083c4c1c40356805540300d102d40c0408980340c1008000d08120706000700070420703212006d1030034540980003540d50402520300400c090303925102a40e071040c612080060f5682c8410f00290064498102c06580101141c04030004c0c698000003d00300a50103a4500d031421609001000b003102e1581c011034545c840302074824082400541d01020b0b00ca4865003c40b003021069440e642c40c1604900803000c070410b2050740034003c0088400300881000307004013940303080000b0214040e14151031880301500900703440d00000c3c0c1d400b4034603c0070351900e40c000d820f8035590360304c034102c1540561140c0501c0c40040e01b071110860b10031030540b0840c1d04842c004c03000f40100a400014409192441900903640d4a400b0300903100440c1071400024010314603502c48002a490368500200d0f118400b0003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 424599181 1250 424597931 424597951
    0x7060e0c03060402100c02030a03050d0b0d211b0b0610080c04090b030313080102040602010e1207110a0b0406030501060305130b041101030e061006090806090304030201081815040b 79
    0x1250304419200000c0140e04940e04480481c0c4000645404030307103003100760102039411311820035900e0605030041c0c001c1036124170000040c00b60f00203000910004080c0746000800d51500c08414030f1243c1b610841071405030307110b0724241a0401261840748007a82c4540c00960b8080409024400b4501e890002c88032100a50b00b0003191034907109400715501e01541c030a2021590f201e006c1006165018000c50341310038040c851001002e5100c0d0b00c054001c2d045402500059840c1a00c403802070a40020b10190040c08001001c7ca04211a2b84900c12070913000c03da140c120b42c41070008030b031801120340038101078281c9690000703041d85031581c000c041d6940500950700c0800d05511302c1c070100c0c802e50b00702648a0340044203070f090001c411004a0060010304101680ca000e028180080f444049580004a55035943d4000382d0035120f00c1d1058890a003514074002c4c0b40d10400c410001035018410441d4400d203603400c07520f84e51400408050610164804022001032a402008200031881e03120581000b8192 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 424600431 1250 424599181 424599193
    0x13050415030c1e0305151f23010903021c020f010518090402011b061a090708070c0c050d032006090c01080405010b031609110315010c0203010e0d0507060e 68
    0x348a18190914078010405041c0100c0c201410507000401c150001350350081c04c0303514080381d9451000f00000207584406807c0c0703d0301605032501155031040420f60300c88620306121605a11802000701c0303c1c00d1611814480000c8000015a454440301905140c03042d101c400700c000d40703104004624a000000e907040c06000d000c0c0122484400d04491603040707040d20141059255030005941000104084030800f14a11800a08011064200000d8131050029544094114108000b03040d4411286400040d25010000e04540e200b01f04000c0e02a010740eaa500d1460340729404200d100110540540114000d1603914540300000100e85521041000141840d41484a6040d07141c80e001c0c10400c0c10088280c1c00300d8107015003075010080030f19004007110344032443c9403900d5100c00d4a034424111400d24281c0342c1420344141d10102c034801c21020500459002940006440595044c070040e40c15650f10890780100300707000c00801042454640764603403240082d241c14400e80c0d500440c4581d040d0068 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 424601681 1250 424600431 424600433
    0x1090b090f0c010c031d0a05060d06050901050907020c010c0c0b04270e060721050411010809010b0108041502071a190b060409020c0a050d0c020f030a1a19021305041503 74
    0x161b002c0c08030240d850320340e1859004400004041d40519042a0717840390f40095a4503903040035500100840e001614040710700d0b03994000f0808a0901260804050781011240c03403401e612459040201910800c0d68585083d210903064282d03130000d401a200e40091501080a081c1c041c00a079500e03c2c11080e024002c02595210702da8451001034800824400010034502e0400100700c03090441d01445002008107260a090104000300215031480c04104c20a004c29003681c018003541d520004182c407165140d464035550290285c00002888a015a00740440000a0f03205035a040b0041002004450329050440c9008a11089494440c00032031420508151940307a03001510201c0c0c08443c00180c070b50151450103030901144c0c003c0101180182c40c00b1000c6943c1040320b0395046402550005144443c9105260707850b032640402501410b4030315081041c0300380340c81600d0782c007403080084021000c101d18034032000da03001900001ca0f4401611002d1000d82407911441070b08000301c8a40c80201403035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 424602931 1250 424601681 424601687
    0x1140306091033030c0b130b1c020310050109080109240209030a030201061a03040803150609040905210f07080c030f04030b0a050603120901030203060301090b090f0c010c03 76
    0x488004984060349071002400f16194000000743d403010301a0a00c140351882c015000600581030004480c44200d01c000442d6080c2c0ea04192144a1054041e411040c3e0070401161007a8220801038802400b4414102c1c00c11001400518060300900e540c40703840301d0400b0000b6108020743c6d000301105070324140840c4041801000d000d07145c08241d07031403440358240f50792040010b40300d6428a07a41501c104052401010b505620100c111050071700204481245519001d0140c030007940c02030700c504024070100380903140e034041e1112107045c01410980303482d82d118080740070350745000010b0340d0940020600d610811000c1d010320002c2c4007410f051506e04580040b0314949070040e440c0182158001003440751003850100100c500e9641c820160b04d031104e84c3c074580354680880440300030742c00c02d00b002c01064040c28002400301c03440784ca0750310140c180b0342c03441d00450086d000280800e0303145d03403550382c48004a21180307401c40c050070b89174018000e604580384e0704518206401900d1810041903007044004a54 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 424604181 1250 424602931 424602943
    0x60b030903180d1406150406050a06050a0905090112061a010c030c060f140901230c09150d150e060108162708011413021c0f0b0114030609 61
    0x1181421180407803002000c0368541d8151980113007410018040289071440005616104018200b5845c080030b02040a01060352641d100311508480001c2040c090a8000e202420550300c452504030354240e80d91300000c11125080e841089021600c100d408140080d9020b041d000d42c00586e40b1215416410000070000052741c4009010000500d00c0d41041200b55041881c0600f40340e281072000f460202e0b8107180481055658a407203600c3c1101c0a1500319660302e0103503064400712030b8030002c1da0b1019101c01e115030002d091241c0c004500350520001e050024042d1084001744030002a008030001042c80d0710400681040030890620300c1000700c1c682c4d11003a0780340e0107212000a40740a1445d0341044da501070407800342103240400b0300c16000b1601300740780403141100c4914000b03001c200b913640b0001b019803100717641c04085490140505005820300b4940c88100780d1031003181001500b6503440710100d0785402c5d44112803039508171004200094654200c250901c100310054031050801c0c44015607100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 424605431 1250 424604181 424604197
    0xe030d030209060c011b080106030516030e030d0609091e050d12020918160509060f16050d0c05070512030712090f03050f010c0201020304120c060f061701060b030903 73
    0x341c0c00291050460f01c0c3e510a0702c0700b00d69102c000f4040040c83c0d41995444604000d61500000c55400c00062903d20038001d860080c1d06074402e4202160284508601520120841c51070921003000544c020302450300c1240c1c004e111500e00000c10041c94509031400ca02c16400c01d01006984001940c0480c0d00840c1800c0c0700442c905002809140c070100240280c0030341080c0302c0c1e2012607104040044076100903600c0c810b6103540152920186041d0702501e4500850f02e090360000003c0c0b2041400462800092441d2003034201d00d684980c4003503036114a814964120000040c400480e0041004410020740c0d014000455120810f152101d0b4031940d240182c0e0b20107045422a500c001b220540500b00c1840501b40903000c1b045289c1d02c81c10500e41e0f035405003401200a40c64507101c450018418400c1d603000d6a0300c001e0030b07a002e001444003160001100e0500b40d46069880e02d80e1550039286128031801080015550030900401107500e5003160034550040841c00000c00401c0030519003c42212164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 424606681 1250 424605431 424605437
    0xb0303091c030c0605040b0411120a1103030c0f07081506010c0b04020d060c030b03160506070b0a0e1006061101140604020703021c050720100e030109020409030905100e030d 76
    0x1071a090b007021658002c0d6601c0140496103810700780f10902040d83c00c100d1050b40111120207000c07407250140030064404d0030300d9464079040a003030383c00001c42600406509610080860307007003007046001e181c10000c2141c0003d075a0760040d2420050100c0070b01850040315021507004105113080300c000b80144410001c000c007259501d8000400b1590350080d030310081c40e04200308006040d0310041c05401481d02da40c1882c440d220320740c1c560000002c0d0600100c151003001e40541d0034650103075a1401c0c5102e000d401c1c1a400380d12040001007502080018400c1140103a802051a910703211024101c150340300841102a410250303001582010700a03923a1304580165401655100a82400c13030038240050208200082c0f40000b0b00c0544d513100780540009801b90048424030b0380401c84410300c4980c803c0301160130118500300e820304180240100a1195005000440c5d80b4155500040c111100c0720001c40c00b013094143c0920072401c140318a201100564144609102c007000c000a40c0c0d129150b10203010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 424607931 1250 424606681 424606729
    0x150103050415050403081503030c0d030518192904120311030f0f0105060304150c0c052a0301061211010309020604080c01080703140a11040b0703120b030309 69
    0x8020040c40d82c07041c42c40309200e042080382858503000b404510b0603103d808000f1400042e0000901c2c0205c1143e02000140c4020016012044c01c00c0e80030304001010b10310369501c002c0d80d400d01d030142402000c0d007030084910b0502d5145c0300d514061a28113404001010a103104805401030001407030105608a600058600944040003038210042d20454480c600c88102c04001d101ca84500210144d0040b07540c9000d610703550380c9842c00d211250008682c00b1702200d200200211812403e0781c80701c03400001525051030140e003070f52603440c98a8030110240030301d0b403007030060f10407408081035403100c40c010224020b000840c44c1c55401d9600c1c8a09034006022054404400b0415a00a90060900c2d40c0d003d0700b0740c1e07120b542d2034407019261030b00140b80e94040b854a00015419610920400c0c900c48070090310900107440302034440d801403241c2502030300c0000c0c04003c0490440040301c00740101d24400e64075116290003841502c1c0c1600c1c600c507201402070348288403401441d07035481480a0202000c41d00101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 424609181 1250 424607931 424607933
    0x203030f0c060103171207080c27031005130201050d0f11220302060f0a0e1e01020f0f030703050325050c1e07140127080d081501030504 60
    0x411031142140d1896203600c001114120030002240160499010b56510b007071400b40500d0000007403083c90f6058801e4502c90b000201e000740070f10300c1c054200ca80e0b40d400b02e0801e82456002160407491b44608224409205124079040c90200110540d200600005000302d090840903802d89407024007000341444401306e103540603481d2a51140c4080301c2c424000380003040002d05038070f60aa1156804914840444034801d0003002c4d5144894104c03940605910300c0d0040031882004180c210070400810405048150190307550b4034a10b040130350340400403c8540e0310600001903d407120784988810107400004243c0544100801540c0c4450b4050602c030b80c0c1c9075a0460009000c0d450550302c0c0b4030008240c0c0d08503020a502002600a50509004880030b420031241091402c0100001d40302e8070f40d02001d02403003410f13409040145480e074181404030025148041d5000c3c1115808240c3e41e09003e108401c00505e002000340c0c0c200e5007a907060000890800c80206ca429072001603045041c142c503800494 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 424610431 1250 424609181 424609183
    0x180b030313150807020c0307120f020904030315231002070b040305030406030509030c0c0111012009010201060b0a0806011407120305070206010603060e0f150d030306060212090d0f0203 81
    0x1d040d880c01da00c0c1d14840719142c014005400203440342082c00642d4180018220780d00004101c410280010010942149040000e21141c0c0c94201c0446107280341c8240e0800688910304814010b0380300f51004546004513803191100c00307000384d00103101c40030076545210081010360072041d80440d0948010070140b041c1242a840e21105a100c05500c8800003000414060040054010b135274440d64140116210f00110f20f5407405071031121541030b0485001c0070450f41c05038510100d1a00f20782c001240c00013407003211a08100076242d41250f000790024880306030b90b034207215030406441c1c0c0b40310303050a01d0480d1707200501014000782100c2c103000055141d550503e8458091356441940151454114994018000c02500c019100c1102510031980041070190090041c541501c505040241382a510258041d02c50395014001080d1000b01c61640413140d01c1c2d200009881d00c2c0a41c0303021900a1030000000d2400f840c440421541d5a02440005043e0f40c8031380c1030b040c0c2d4940188252440c4400c500010b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 424611681 1250 424610431 424610437
    0x50f060405090403030f0b01090503100c0e100507050616080c0f04030b2502030a120f020408010e0f0d0804020a03020f030c03031306021006151407050a0602071407180b0303 76
    0x15030b4072210140402040650640068218440c0060b0510026202e8401524120b0682c05602c2d41740d00841c03026044103445031300a074184c84540c03409030b0003548104081030580440654090000d0400900481801020000b842e0085581e2004070117101105030000d007501c1006c0e011003e551000522951110b030790005840145410811500d01e40c180405c0f01c540c0d0710413a84d488281d405000c50f64007485400401540e0841045480d2402c142c00312500f02c5006003013558480c90b50550034000070078106001d03c43e503031101110400900c5a01400c43c10035150407075280d0043c0421030114100401605c0b51007203101102d50540f8004000303a00c5000003400c00192841041d0584000304561007204009034501701200e8031a002d4459410010b6904800c2d1501c5009403000f01000140c0207588a2040d0b000040074240308101e1810005550384071410f00960b65030540d8043d0b0049900802d0081084034185d45805880040008901d002c1c1c00004211802c00c643c031096566500300328003030300d0500031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 424612931 1250 424611681 424611689
    0x80d050a05221805090109021324170601090612060c02030d0e032a031e0f21070e010f0e0409020301020706062c0c1b060f07030c02030901050301050f0604 68
    0x561580c0d5512811008142d22800f00303141e0201d4140070200301c0510045c81034254468002e0301c60080c03d9504860f403406000300740d100c03414150755460f065400001c1841840081c1031554402c00408440040040c50104180c1002003440e02d868000c04c00c1940083d2000c2085a100c00d020805080d15001030741503000d08900104028105100703954101c00110090407160030340401c440c3c0703034510f0106480320054000344002e004e41c000c002a00c4619800ca40d12105414520301084c5400d00e09400e0038220f401c10502c650301c0d0100b0303850b031207005d03030183d580140d0084c4a4509810798a01200000b020001c9404808090003001e0612107a5519190401c4401c1a00035000f90750740d40e070a00d441001800140b25480644445612640c070180301100080b52181d0441840c0354207454600b0714015581c004596450660030b100c03000611450300784161849001d116880210074600b884015080d00c010042010841d04208030b0485160f800c80b043d02d055900503546001460391900119565128a0b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 424614181 1250 424612931 424612987
    0xe0c12040303180c0602070b0f12040501020c030d050a0c0e13240611010f1811030c0409030809070602031e030a020d1806110f0403060905100c020a0606080d050a05 72
    0x3d014000d200305001c3c1c007401c0310501d60895072229540c200f64200390103101e4552150403000c10a104040d07130500d449680050190000510741350311040d901b8555400807104041441d228010042030041c103200d51420240309040c05a110210000000c81d80d44150b450b20021541d144040c2001e03005104000b800c1c20f01c3c08050004c1d4548805018224401c80043c0804641c28804403031f60060050007059004040200c0c21090360718550303180851002000b21054061040318050b2240b60303918010106000e0098130385544900b880300801c0c0c24822260801015584100704010344010501c032401e10000b0700300c04450302d0703442d08100320000c0d2052820714034103e03050201043e010320242c0c0c251440c0a1080108000c0700c5015032201701c041c0240c00d10a000004180300410204040350030009506201d44295161100868601d404550350f00c0b100e1030042e40200030960030003109221300300140406000801311031403910002081d600c241080c450812101049800c02418405941008144141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 424615431 1250 424614181 424614221
    0x3110d0e220b330c07031e0807080405030c011103040512070503030a080106021b0d02010c02040209130b0f03010e0a03111005070f0e040207020906220e01090204060e0c12040303 78
    0xd88260700c1108142d1040c90f0051101c0112074600c68032400c48100d51000d002070305c2441c0c0f450720798100d100142403d40780880d07007800c403050029030158024900c1c2e82c400c0c47d000b40c0320307410300c814903142082403c000d41c1405641c0c1c5160031402c00c00401d8500301c0e40d044860341170003017a05c40c14070b08014841c1c0c4042c0c1c040c400425142c0d083ca030403142c1541a03900c1a8200d4603044101c211502c00852120620798002c181c8800e0b510155100d103980302e85090014001501d4a441d08001c515424290b0442c0700a50f9581c03c075000311032400d481c6041c04948101d000303025070124240d059440c1d0340c1c0d8600042c1440045003212821031000d202044910001070000c1107a80380040c00900200300395110400003030551740108080c0d1a280c4256140507801074000c01041d6900030520440d200d02ca01c00c0c003102a800c10b05c0460400e018051120b01498860010070030041c10310501007aa00c0540284010420075001c0000072007a00342664003481070760303c0c3c455880e140d0b4101980200000700101c02003070844 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 424616681 1250 424615431 424615459
    0x41509180515220b0c09010e0d050d0f030e070e09010b0d0c080c040207211808072c0f060a0f0303021510080703030e060d0903110d0e220b 61
    0x6074003890321583c0001d00400400f40c04440810410303010500c0102540c45400c041540c0c6841440030b88203c00040c1002c1c0c0300f0224200000d40b192208e444126065444000300c00c40040d8080703006111075005007018441c0701c01410f142500d0311f031107000f0f50400b0529000011030001c02500017030100a8082c00c00829124242804140c000d607070701602685114110060800f401c00307200700c03010300381c0052155080d080070380f80030380d030360030414503030508200310300341c07008840580d8400001c002c040210003801d6851603c6500c070048222881d00d00b04641c3d01c0008424089048019960b01519000c00700c08555079160009074014596044041440480800402059000102c002c00c00d04900d00c4a880f6940782e07120540001c0d042d000c0c80740190807204003040001d020700ea0110741004c00030030807410482c580902004903010301006400040106d94130541014041c0b0130b181100c3d20070310305034140101c42d0f030208a0300703e031844610f0007481880c81c842c2ca0004403a40540c204020082020043c5841 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 424617931 1250 424616681 424616713
    0x40518070305070c080412020a090507170604111c110a0e0f03011b0c0f0605150a090c0c0f020414040b1012120807050f0304061a0415091805 62
    0x2140c034030001c00d00d4800801d2025024480d184440c50b40521200d19241c105244082900744200d4100e07009103400c400440c0c544d095000b02c0b44160b0459840d84809075030b003a100c285180000e05103e004915018880080348036420440d00541039031041500b0001034000081e0040c40c070081404440030b00815600b0702d0552080d604c901b01c8504030384409039251030104241c229040e401d01900d90810000700c000c0704501420100209500400c1c1004016001740c540c0000e44000300c541c4980c40001e000c22108924000c00c1c010b0203070150304402c220000c0801c0303010b844c1c100707400e001604031641c800305902190f4498000709940d50b001620032046061034a8149404c00f0141c41c2d04000c07412401010a41c1c500400000030691340003540e40b200040000002e440d07001015040504005040100c80848062000258000d5200d44400540c3e50940220b120104113042d80444c0f00742e0400d8441d800412402011000b66209060009846090500e5592000e40081e00c001d00c80d010b2175008c80040c1031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 424619181 1250 424617931 424617979
    0x3020c090106050c070e090c06070b0603060c070b010b03060a08030d0903110307150903050403050a050f101a0f060408101406010c0206160f0b0108100e060108030703140405 76
    0x80994190840d030362110015903040c000c100c0f610f030701c1d68000141082100400035200d034100c0028402d80c2c80c80c60342240403400580c0004003d88401e010341b030900515050030007803280c0c13018064000038144200c030368514030500010710450080c00c0d40400401c1095540045400003881c210302165036503407044030b0b41d002034400c03014281c011900c8041e1a4500c0f090101c1103d15040e4841d01c40c000c2d20005609035001015081000d40800405000200010f1010403020b4001805440204008682140080d25000b2091900c403071a509201d043c07901c1d0b40f60103030b0100c24a03108580c4000744800d040c011941500940e80068010320440c400c400300100c0b02c2d0300a101d01000340c0d85020240da500d200554002c0c01f004c00086d0032074001c003d08083d08030b01210100c80c1510441902c2034404031350711100c15462082e080401240c001c001c0c0008011642d200d00b2807030880c0c1e100500040c2d071420b00b0068070f0340207102020341400f09a180c8044106411821100601070040c8007075490400520380c003480c02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 424620431 1250 424619181 424619203
    0x1e050d0615031b09031502090a0b03010905060102030a0c0206031e18010e01050601020703080309030d2306030d020d121401140a060311030c0c011803110c0607050d05090a0b070302 79
    0x203443c3c041d041202448a20810000d03d00715110324021503d1550f0b04980d01106000a0b034080d582030007004060380e180d00014004100303c40c8480d449505082c42c0e03c0c211783c005071000d41958001c014590040c0d40003180440301c5030f0111003135512aa01d880ca0400c4150141c407112a80c0e4410320100072040c0700d0741000701401010000200003041e01e0310707101403c03900140d643c10302681c4035034002c100090110004542c0503102c030082c0c90400c1c620140030810380d249100b2042c03c010311818500c459600130200d244c0d01c80b40440003001c182255a0340039403200c0850903000204070f0340c80f02c100803038031003500504590b000c41c1d02e14a001c0c1d03035501070a200407a121a80c0900c02c1807441000100700e8030074058082c40da4031207d079051a51712590403041450788100451a159500c4030317903c044560684500f070082d41d010307454109a554604507441c6c106095040c2c5c9074400d8000b4440480801c100007a407904101150400070350b1032505500080405950b54007100c8510400540e2004250380824105e880d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 424621681 1250 424620431 424620437
    0xf0c0305090d03050c0441011403060a05040b0a050925050f0301062d18051002031b01090503031306060905060d060b010e1c0b070c031e050d0615 64
    0x2082242c80120162041554001403101c820b020600034003481d9202103010005090008605500002c3c03003c628141200d4808040c0c10010183e070721550700006080d00c900b030001c0f1b0251451811800060540074140141c9000d5a03a038000007000741c03145400b020190000078001501c51810320303412001c2515031274007051503050507141520890700400641d1070400b04182c4190840c0c0c20240304460f505507c0070b010021032410754040c9150b542c11403800b0080c4001e0341d03d0303000e460000004003021010341da10503401000d120f42d616401c540c0c0031040d104165400000408504500809640503000e46c0d2000740c01400000140a804450483e074070311200d2090801740045e83da12030324003080301d0085601c55002a00c1044002c0020703e00e5000a1012505062044040300e25802160804038209001c0040303017006020f1005002e5020b06081c2c1c031000e00c0ca0301c281140c02903a030007081c0310a00c0c140003030100b00d0b00512940b06400f8400b59059803000560800c44603550f600c6a4000115031a070403004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 424622931 1250 424621681 424621693
    0x9060203090d080708010b090301060902040608070207080f19050c100f080901050705040302190f140a0b091c0807050105040f1a0420030f0a08030402010813240f0c030509 75
    0xd0640160490f62280d03038140c071419003aa00c2d110242c00c4030380c00041ea403580740d5078940c00803c01d00003610107040503080369907880700300d8601110080d00c0e19a19800006060b804070141058001c1c3c005003242010040d100104001146480c0081c40c02c40710000140d803010848400e000c60f154071850013403410469664904150b2260100142240e02c01c1d103059000034801c100500140c06c0803403a010103450b8005580040342e41c0c400c0100d48030510768100814030081d41c000c580962403c899600c001d0004105502c1c030384100d100c0000c2041c1060035140d4030074042100d003170b801c0c00f40d94015140e28942007402440b442c40e051403c248645040720044a00e441c000e03210403440c054250300c1d540b0840d8011100c0c440303010f0450303c0c0d0401e480820781d1154188140e248180d1041400d0122880c06c0e80301e110819124103161001410800d0014031740481040c2c9218038101080c000300c0a40740ca00c0c809003040300016144000d15018082864105507154141007030300829690542c851842101a0016940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 424624181 1250 424622931 424622953
    0x901081510080705011409030f06071403011404090507080d0801210308150a0305070b0414010f050403030513090e0703050c100806042c0c010e04090213090201030f0906020309 77
    0x1599601c0750107245126408401c0a12055024000c81100d0081d21032110f800d100b42500004c0c42c04e40340d001a44a0340d00714000340300c02142c001e004600c1d03980040c80010700715810704100c880e4001c16180a83e214035100d14181c4240a41408050090301070407081e1005941030100c083c00d510300a00c92021686003988100c078489112040c6036800d164140d40b60803180d11780350007401036005030344800b0398808505000000040c00800003040200f5080480980342c1e840c00082503850340810000d14184900c001d20101d881d079000046905603585400c00546480403a9840003d250181e089986d24034508104142e81000000e80c00c011244107070115519100c1d080184540b20302486c1c443d5004c54070100101303030145401e4011490b02500d5002125442c40302580c0e10314181c005206c03444050304440b540038250350744016050074400c1c2c1503c00b80700380404e0b0303400301e030030b01e4900011425469503905410046a00c00d400004959001260a000303a45050502030002d502c150323480500c921480180031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 424625431 1250 424624181 424624201
    0x501030204060c06090c0503190c15020706111005040602090909010b0a09050c3010050603010b09010903050d020f0c0423150d030f020d090807050607020102030909010815 75
    0x507003596031542d260f016600c9156075030700103456050000c50301c40800d00f1001c075035610100245002074400d0f411a0341d846801d03040c00b201c120800e40105c80c2c1d10074800d00403104146c000600c80100e0b00309140c03601489640a400707a05000b840b58024403d00c2c00c1006000500c15250090100f0740002c0f2450001502c86410150880301c07541a0960442c0d040c11003001080d080d43d200a900c080807003c040e2911100452002c8840c022403540100026460440c141c0000d50485c8030342d210700310180c200c0a80e41413900042d5a400144507101540c240025240c5003130341701d0303a2588002d65004007124000300d50307068080d4494008040c0300300c40d4030420044112502d40307405071f1510085211a4508908003246520300b4100000b80400d00c4610401124440b60321500700744d0018900a40d60b08400404009000381400d40d90305418080100d01030061100348801b0400c038088074411241155a00580e00c0145e086018070f00c070381640031810f0000042c0a00c40410710840c074070318981c000c0d180340e5100c030104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 424626681 1250 424625431 424625437
    0x3080c0f060f220501090804030b0121150b0a0303081602061005100912060504021005130524070b06030d0f05090904080922050606120610050705060a0603030905010302 74
    0x108001611a0001c5001a200c80100d04026004142c06100e0f2800986a481c2541c1004004465454000034104240004582c09901510014010b908403115602c0c1503482c0042d94400500b40540313a003007413a921461a4803814441c10701425800e156540c038100a04200300c00c0700c2c401044141044c2c40d1048510104096114119021002c55042d062800340903520510100c0ea00a00c801410049080c00440301c060404612a60000c141460548140007011100c0c989120034401c050010101d02c40c01c0c40d6500d030541c0c00c02c2d2041c03011741d03a000c201150f0036010040c40454940000441c01c05022300b50010341c1c4940700a40480301c00201001c0c0440b24030440d4410140081d4040c400c18002c0c1c0f80c5a41115001401049140d00b40502c08c000038a91203c0c1100c260301c0011a9150040a6406030040c0d9500c100101d030311509103a01001c0b0a1101d0300010062880743d28003420a241580c001d1007950450780e00a0304580c86490901c000c180201010700099000c43c1c0051400101c0758801d00031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 424627931 1250 424626681 424626691
    0x501350612160306090c0b040308070c0b03061e010e12061e0601050a050306030a080a05070506070521130614010303020609030a2c040c02070924030201080a140103080c0f06 76
    0x549211070340f842e1103c10050040300d908550200e010340c40000c901e056440a00040e40c090050903907101502c1ca008078200c0301c031f540703c10a061710610800c900d6507180c0c0007000e03280e000c0710082e0b0030001c00c0000481b00c40310752076200e5a224000c241200203102d80040c4c901d11900c800d40945500005216000a1440003240c1c414000340080007403010440c4180091a000400030f8200c80f081c02c0681c3d128203036034000402d0078000403070200d0110b0500c0b130204502600620340c0c0c20003600d0068410325280080e58025035100c5035181038408a0303080e40c4507140140c40c00d504403004002002c18002440c40c81403081c403060700148551000b10300e01250120440e8120500d035150000c216a41562014891150a0703002c440001240920065510b0314094111005542c1d80501421402e04c01c41001310340750000c014070b485000745000e500b490341c441010802e4036024207151159940d40c440c0b920140c01c260700501048040710000108004020b00503200c8101d1400036280c0c1c0d40c901d202910f54591084034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 424629181 1250 424627931 424627963
    0x501080a140c06031303080f160f14030a02030403020609030c0c0f0f040c031e06030503030a1e02070303091205161b03080c07090c08040c0501350612 66
    0x2040500264144030703200500c61007070003a2405070842c0c100140907900b0845408241d41c01c2c4175840010554085100c503404080c1400c0300c9401d003400802c071031001d0368a14080003800001030300c5404484c020307031400d00e00d10084402180d4900d00100440007a420075641100540700f1030300840d039000ca020040d201c10002940080144281840030049160514190f4580180c00f60100c1c0c0c40e652164000c08a0300e40060328045a02c1e4100c0078400b06607207035142092401c600d4040e00317000254002c400c46e500144044008519000280c820302024140c0c049642780b51440040c03210201340c0c15400c400501c5004840100d20400190001e590a210b04c0d188243c0c501d42c41001e010014400c4032580480f141c00391454021079440381c0c0e410540e54058021030406a10108040001724903900500540c00d01c0703407501d0505820305a40c1c41e42c601c1c81c580580b40c1800002000b8201c440440c0c103400c003440900c40104080081c0507080400d03110419a609401018010071078400c401c0e00241a500920b0000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 424630431 1250 424629181 424629193
    0xf03300c0204020d020c06070804030806010c0302070e06040227040606030902060d0e0f01020409151502030316020c0904080715020a0c020d0f0506090d02070608060f01120609022209050108 83
    0x141c01c010080d4041500b5044103030742442511818141005154400e19064454078a40c0c05c05003400340c01802c005100030b04111100a00000283d0301050500071501018900c0d407082e183c0d02e0001e0b003e4001e000c22120380078143d03100e1810580c0400c8600310850010340b020007904d500c480b41101034480715007000c0c0d01700c0401c001e034140c80d8400d0380c8084240d1280303e040d95080003840300014260703841540070b607400584038001c03202d081d05041d0108000b000c3c1f204211000300c0804e00040c0d00d0b0b0000400c2c114460f40500e68002c6c0d0a40244900d0404034002001d4400d0351801e80b40c0950507801046c41554030a10346182503622010520071a040340c003c0340c5410030303000d82aa08100329201c060008031084440a040f841c0060001c0100d50300a01c0d9203805405115038682c0028908400c50380624100904030052191a0301d03040d4110604001c03c6c80c16a54020303580700620040c0002c1c0d80001f07030803440052085007012542c0c00103019000c4100c01070301010b5032920303c00300341c40c002c0c081c2c0100c60b0041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 424631681 1250 424630431 424630433
    0x13060b0f0d02010f0306030c0b0c01110a0207060c0507121208060f01080606070807080c03030405060c031b2d0406030605030304030b180a0b0c030a0c110601030303150f03300c 77
    0x11300c000d080032400d900c1c020031542d449640d08802d1a05950040d5081e450118840201ca14280070f038255894143e01042d04008440704001d41da00003034032819040c400350404090910100b030005a02811000c3c030311030032031002d030b18100c0314105000190304001740350b220205d4030311714040c501c00344043d03016903500007d500e401040000380d5022500444001100700201e10010304100080e00c41025079501031512440d040c28181d0401030b009025102903001001041840d03a030061b083d010a40040707406030340780c100701061103211400a9841d841a1078400300d07050725034a1504028025034205a40c188090740e5950b0515960780941d020040021030f00c0c1000803c00501500880c501d0103010f4101d444002868640d0a460b010946900518420000821041c40f4240c001ca9194070b80342e1034034881c81c00c0107031045600d9100600000b8100754481c1c00003154180e01d28100c0003d00034551882e071229030303607242c03082c6003a0a11400c440c03c0e40014130711240d000b00040c0c914260310840d8440c03124062507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 424632931 1250 424631681 424631687
    0x3080c0310031b0e07050301080a0b0402011214150d03050d09060207080a0201050109140f0402010e0f03010c05041a0f071203060b1b10020405010c0312060b0313060b0f0d0201 77
    0x300614a04000044100010100b0300c2034407581020064820760303111031420308083d5000010300030049401d01500b003004012110000418280003a0040140e0425454500c0121004c0744c002064141c810300b0809881c1a0868900d01103000b542c0ca41c641c13150304800d0310240090358074001c201401094050180f4200035420750446e034805440750030010b00e80b0341e80341d4541c1e00ca90460313104000140c3d912801400480240c0c031030501c04240341d1312403007018501032070b54520007040144000e041100e40007c0711034076103903050a031144030b2000b0001d2011170070792900103100303030414443c896490312030104615100c03524004803042001401031207482d0401a40314000002c005801c4030007010b81e1684001030702041680075100d00b250410700c1040f502c7c0c0076401c1c1880c00c110440e1005d09644104410050390380c0154403c000c0f45c1c0c1c10b050070700c64014807400050080607070741d200701d2004000004010b0445043d2100f00c42c000d10030300e420001c0321741c10070500c1402d9035031181d02600f10901c401428050b42c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 424634181 1250 424632931 424632937
    0x120c0d03030504020f06070804170c0a140a171b12070b07030c17090f090105011b020a0302040509032d040302060c0c120d121104050f130203101a030403080c 69
    0x10000c0e00800c00c0c2820280806d005602041094481c0c08002c20284070007031254182a00043c8500010444240f4000000705a4102486a03007940f00d0100403030f24050321a103081c00c00800e108100c2914040d2500041f0b80ca6160070407004440c45003e03a492095445c0013243c411b0000c00050051151034180140d408050784030b400c3c1602484400310900000943e41c0301d060240b00110802c064980001c041401116a220000700b403080c6d01d00302c01030200782d13071240c8100442c80c5200c5c418001440b0ba4008944002815000a9001803c26041000b6001c000006102c00a0b032408036944001c3e06031041244100140920007010604020800c0589040e0014001e4503c0d40400d840004402d000014040c13150a1030720700c0b103034019864440c441c07500401004180410310300d081c880492400001245807055014407440341030500705208a0b904c5110015003030b9004090119030b80e00b480949800c09038402d115000320078aa00000c000b0381725099094a015a916450300c00980d20b40c5003444803a50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 424635431 1250 424634181 424634183
    0xb030a050607021c0503090c0f1503100f0f1a0307111c1e0e0d1b0b0310050f0603070f110d03091403070816020a0905040809120c0d03030504 62
    0x1105020448010a00501805000c0c841c1d980040242490b0321266480d000382201501052107414400c106d00102c000c40d07030b51603048085444901d09031500c030010f0130281000b20b10903180c000c080104482e010014048200303451190319280b28850383e5a06801c0c2801741400307000d00f06820722100d80b000b200900091600b1a100b814040700c20040501314903e4103078400c9442c290000b204100e0ba1000340c0148540211000080500c0c90030300300100050000500300400a002d81c0044466000f0b110569404a80c20700803004010003072541ca2101d075203ea0419110610f038a55912000117403490035040d51120740002034501802d540e1541d60603100f07410b0740b000040a20600108076480c0c0d01040c00b00c980201100c1d00d00007201545802d010b811018200b00740c0c81070350300420949010428280507241000e41ca0a4400740e11a030610104940c0483c550000640d242440140000c01c003004c0c014020100d0290742600c112203807a6041303a601d142030043d040e00081c004000c1004207200780c025640c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 424636681 1250 424635431 424635433
    0x319060207030314071d03011b0503100306020a090603060806071d03120f0d06081b12100f0606030f0b01050405040908220305060f04080301231509150316030b03 71
    0x686500c41e070b8420070060845c4c4480004800d2076500180e032130210f1600401c40410b90003046080c030442c3d89105401c4000c02c0c1d00c0c09001c008400125803891303621050001e1544120195240c1510600140c10780985000e0030000c02d007010800304280c03900040c00c52140400c2c0c0d940d6140c4202001c0b0308800041e10140e200d4042c021202881c0301241d1101c018862081c2c1c1e002255918164002c044084440c4c81d08240905d811030200450054003e9030844017044e81100d0249c901c9443c0d05089141c09810035074003200b28140300344040c7c0754615034012801c8641549003409090030103580c581c01c07a4031803e111408660305120520681c181a40450501c034404c0002a207002007401026444501014102c1d102c0e1a0815061080220070b01406030001000d04d0616900d0819030f4a18002e03000500030707110705900010b186c501091040d106400040c1d406461400310070a50343d550701c1c00754004640e071030043c2c40010a07980c65004c54400c881c460340000216101d483e90900c8200c003d0000001b0300e44c0c2c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 424637931 1250 424636681 424636691
    0x206010501080c130b030105010e03030717030c1603120e43030b0402031903050304020402090f0904050f01051003030c1106070c090f060b07020603040f21031a03190602070303 77
    0x4424004d50b1036001900050509a4882d85000001441e0950380001507000e03030004d026075000180100c145040b02421a28607585a0b0743c3c283c0103d0540c003c00341c0d01052043c00042d028107154002000c02c5156000b00024000034110110f0a545c850f4580d040e8603c2c564006680c0e00c6083c0840c80f80406049008081410010346414524109915401c10f540b070405050500c03003140745c10014200b03004203051060213081c0080d1400340680c04024006170095400141d42940c40da43c860301d0b030b1340c0f091000b81640103505050425540e620000070500d80250f18120100d01c4c07030a02c880b40304003141d6055813a40507130360080e070b600c40d00d00d1040c144807500f0002c1807208900040d00b826806000c0d2640010002d80e901c031f03c900841c15200c0c0e5078400c0b46849030030030100001da11024201c0342d100740c02c01d12030048013086103000301c50306160002040318500414040e00344540d154002000f183d03c018680342c007081c0d50000309a15010803080a140209524003a180021200d030040c00c0e500d8068140014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 424639181 1250 424637931 424637947
    0x3050c01060816080601050a0314031902060901050a1503080d1127040c051207020709020c1605030c242a150f070302090d020d0609020907030c0206010501080c 70
    0x200752a2250000152900318100c511100741c0381d80840300c0107000100050241d545040041500b000e03d41c00301070065404240014240c0f0b5040003226503a00303e0948040d400f0030103c4c0025100c42066801100950a190210b0a0003074036000340c9020903d41d040514600346103688a005643c0044d600340d4038292501d440301a101d8042c0e02a040602601000702d41010310514400c4110343c0003c0780920681c500420501080c2c3d00205440040c5404c54206c0202e40b03c101e0141e103400c03081d80c03081801d2400000c05070320040d40030420803c0e001c2d440d6803a8004680750740c1059101c80f100c0207825001113900306c011982511941d00c03102c0c0300c01c0d205805407514004082020480c2d455072004049646510501e8294000c10000a158250150850005401c080000c901d01c44809052002015008034540c01c040e030f43d4620540407550300820b00c1130100740178a404e0002c2c1c038030a0030a900c149000d10000e207000340680134000e0003040b01c0d4090200760b82407900540e42c00b107001d0840c0f2551001400748003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 424640287 1106 424639181 424639183
    0x90601030f02011106040c080c040905031210031a0144010b06030a050f010b13030201180503011d2503020904020d083402030604030c03050c 62
    0x241c018903a800100d0b101c0d4070080302440c00340641424801040703010b0f4540b03011a662602925170b41c0c0c0c424000c2200312007404038050410340082100800340706814010a6111100340c1c05200810b40780e031030b20104882002c003001d03000600c0c1c2d0b005100d2100c403210f900180c4400b0b280609132583d0200c40c48209203400d00802126080718200c200851002900503060b01840500030548a1605d65810409044180e0741090b14000d00b20001c2003a0b0a800110b400301400d00601d40503031752656004440641e07048003c4401c40006900c0450550790a0040e485420f251003003104400d40d990090342d00380b20001c102425040c494076500c600e14901d1080f00001c42c2c0c0c04464000c81540c403800481c542000170341c4028001000040e42400038080740a04403c803444c2440c001c0b03a080070138107005249541e122000303941640800006000241320f0315900182910a1521504125168481e5 = true := by decide +kernel

theorem cover : BRFrame.Cov 424460431 424640287 := by
  have h0 := BRFrame.cov_init 424460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 424460431 ≤ n) (h2 : n < 424640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
