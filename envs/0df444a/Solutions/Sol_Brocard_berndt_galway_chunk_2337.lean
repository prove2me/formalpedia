-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2337
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:24:22.975918+00:00
-- url     : https://prove2.me/submissions/a745bb5e-fed4-4c7c-9fec-caa4f77a5a10

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 420143884 ≤ n < 420323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 420145134 1250 420143884 420143887
    0xe0102040f120b01061d0f060d0f0f06050306040804060e030f16050108130f032105130209060a06020d0311070f0323090306180114010315150b090f06041802 69
    0x248050043d00358010442410040c0c4520801aa00ca099048000c0c0c02c0f40a000541103403141d036111b42041b5012103490300410426008140400030191811080307401c1104e04200c00401c2914010a08c140074680c0010841c1c074191070804107403249110503000035810301510303c518041e00c1042c0302001e4552984020044020300701700015000720070240c040c1c58107040d951140400a510450502c503150380504180784e69000c08009400d6034141c03029035407420f0381080144045a0490020900546d02c21144200709940316410f001c054032251003a41300580c00040da018a942c001c7d40015034015044c0e4080d49400c6141d11041040200601c048002405d0340c03589a2840c00c6079a501c020031060600ca43d842e201c2e4420000c0d5a030340380134018030840d072000c100d038022044003507005820100140005040315a52130400030b02c2100074400300030340381d404c2980c03131103000700d0312240401918014408035082000010510504207050408286c1054040001180c2ca8004007801d06a203004c064015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 420146384 1250 420145134 420145169
    0x4060206010f12030c0f060b040204080606130b1f05040b18012d05210103051f0203060d2a0f06030b03030307051c090605010b09040c090503060a0e0102040f 69
    0x56910b100d29800b44281d4140e1885140000f90302401c06254650401800c0d8140034440c00c10800600c521060694020320010300021501408150103110305e0701200c1d03d46428650f0307505c03c6c05507900a01d0181c2c2c41614546c0c1424110b0383d000705c10184010600d070282c142130322905030001c954820b81c0c2100c401004c140201032150303401020300c0d401e0007104050007500000708490003965442d40a0705001d0000102d03e103e500c050311404c142e4075004850040a083d6503070f04000d0b441d40350807100070390302c4007081d1180a000c20040c008c0b20301900c40030300505410b4035540c80f0702c00c82c1b0200255154000c03c07081c0c9501008103981c1c406001a10104540c041c00515206c0054216008131141034020b40051042289070b0750008103903480040c0007440c0e035840d003c0c1e12089100030900c800740100118034100010951480610142001400940302080341048050003a2000040f5102d140d51583c000000240c1d5540660000443c5160304800941404c0e04c0d0071941c591120701741c0000e80c0c000071111300c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 420147634 1250 420146384 420146399
    0x13080c010204180506190303020714010e0301020403030302091005030613020c01090507090e10051501050307050c1212131101050a0c0507031515080a02011d04020d1e060501020a0b1008030406020601 87
    0x91b2000402c1e022a400e007891840c0d4010351034400b5427086000c500c1203d240f00800340d0207660f20030400328005000715a116102e10303000e002500102241c9000d03005030300d40d194030140104118bc2c0504001081d42564101007410000654000640100740e5500d6840e084c00003202000a100079000749040030401c880d8944040345000300400307404110320708210510106c4000c0d1501701180c07e40030b1802650365a11341000740c6031441811125040c031b03c50b001c44800210314850203480e050001081c580c034540c9400201d1404082c1001e005460200e038511344500540c0107100a0080181e81d00b001031800e02c52340c6446003411201d41c8180d0710800303500d00000505540e84100c0c500244480d1040c010345003011500b59590b41140c1c0024140f080903a082046012a1001c0000d1108005c10940d9a000d043d411100500010011102c120b449010044200d010a0041000362a01a07004000c00109519508030203400501140da481f82d4900d004940004280010400340c1042d800600309940340050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 420148884 1250 420147634 420147649
    0x30525020d11030f0c010503130804030807080301050906010c15150b0408010906050610020604120c14100c05090607021e10110622060905011b03090b090613080c010204180506 77
    0x1140c4201c0d002140d1171102680c000040d20341001102604a0740300380c0f5480d003005648525080504a00c40210b1014100050340740118103880b01550300720300c0d40e00d81400650710300c102035000524000a109c0f8075612610154812850200c50071a0680d555941d1103a6400741e0740940c12514082e510b8002c68800e001c401e0103455040081038502c0a5030041a040003916500c0203000100100d2500b0240311030035100b8a1085e9400b900400d4441109601d0b0301c6c2a5607844641500c0c400c9581420048031b035090041042d04c650702d001038691440c00e01c681c2d0030002064001003402c06c4174589481c44003c241c45400066a04501c9501c5071040004800c00e6945031800042425541c0800000044a9034109160071258103504c040081603500c45454198090200706043c44902c514072000e5410195050300a504640d0050034405200c0d182c0c82c86858803040100d842000381440f1500e04030020701d1038030007010f29521a030001420540c50b098040f1581801c0710350100981e44031000d0102c5413402c2b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 420150134 1250 420148884 420148903
    0x1b0406030204330f0c0501150302010e01020d02190503160501061809050309010507021f090501030e01140105190905010902030a050a0203060904020f04091403030403140403030525020d1103 83
    0x20640030712440543c010141c106501003854100140d10300400e104a0280000340c45c13041d0300c0b10091000c030801650f1101042490702c4140c0c001036082803102d40550011402c24900c00c9241e000d41100300e50001e40441c0054910822030301407004100c81d1044030607a249800c1c0c02d40c0309800101d040ca2528080700c41d85191041101640340c6800c680200041000007282c003611000c0c21f00b10380302c40e040d000182180c00b54000308030b401500340700765030300040d03018406801784d4100762410003c540040c000076017243c00001d0707541640c08420b00184200d00d4141f040d0501c1d10f40200034503151507112000001662001c1e407000c01c40340c1c2c0210a04c043d1101300d009581d8030841c02c101c114218034204c800500d9082010304068000da542c101045d410b5181d80d080048032640100d5801050b1002400c0c255403079000700d400343e00042ca64041b14030042803a2003100c04503501a81d03403c1c1407800070892400083c2030fa61078040884650702e41d03e00161a0441c140e105a4014000c21040d0100780d03061604105080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 420151384 1250 420150134 420150179
    0x221010506030d0f081506030406090b07020a11121609061d0f04030809010e010e0f2b0305090c270105101b1401050c031b0901080f1b0406030204 64
    0x2002c1c522101d030310201c134a210030301c54603022041d601c40c0700c1407044140829040caa00311000004100c2400580d8000301d12044c403482949e40d40b030b6903101c0c04984401078201e0050400c01c1c0c0001c9514140303050384410324004103240588049e121001d89140406001d6030044079526142d10082042d10300180400415001404403a41c4030310345805401d00d0704c14010002400e020029006c40c540b00002d5025090743d51503030000300034030030440d12082d07610841c016240d000d0b03100d0f001a034030460084800034034050b0210080500710102d5403806601500e0010f00d040c0d0680b00b0f00c8005441641c03400d0380f1000c580c0664090084c4114088104201e802058001502600c1c140d2107d03441c01c0d40c480071982e4500080c01c101c3d81202617900c0c10102854122071810382c0c940c20003040c009020303221401180a840700c1010040c0301d1418110680d5140648407030b446c040354000c000290240501c1c60220360200200c0301043e0088540780380490303642c110742c00400c0001d42c0400c09009100a0440031030020fa900f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 420152634 1250 420151384 420151393
    0x4061e0302070b07110c0405010602160b07030503060d06090204050f070f021c030e0c0316080f0c0d0b0a1d03190e0f040207150608150109020a17060d022101050603 72
    0x2d52601000404090b1403102005009078003e401c0300f2050044500c0c888006109005030359407030000039500c84c1c01e0750080458021007000060880b96405c00c4541c681d50544455007527503555010040190300c13001c001d0320700300c2d00e419004006036181e01c00d50303226041c02c0c00301259500303040d20000c1044086094600a5622540810800c1088025a04400d01c22850b011440500f405c40071401c002c542044642c05204101844013881d0340e281d842c00641d00c035035003181c9064030480e10b081d940d804811101e030b80000030808113a01007502060b40581c400740240000c10400803115500d41e01b243c50004612540e040880c0f852444000030340c0510a502d290701e440f0b100b02f80e807000012030600380c0030300c01d80c0b00b07030350008224040092103005820200300d01c0704200700307195480302070607207804100404000c0d118a003800411442568420781d0b80c0642981c4d114540c44502851060300140c004c1e09143d80001030701b41a00050355503400b4400d450b08052900309130210b003621003a0940b00040c2032203120b03401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 420153884 1250 420152634 420152647
    0x20a030f0507020a2a090501030521040515040b0d0902100e0603061011030304030e18041115300705070210050901090f0602010504030f030501050d170f04061e0302 72
    0x60025400d1004d42d04414018a03e503d0300d0a4006060002d01440441c801040d4000030901d5543d401a03040700e0044081e10704003c411550350304a4078078051100f4034400c0902040c000c1d41049a00200e0582210603890300d060f854040f0600c25030050106009481d0b2129582011030070020809600349240c1d05000b00195580000259540402041e00380240720050f00c03c1c01d01e501c0395404640c18a0020290382e52828a03090041c0307a14144003120f400b40f100420110700413140004a00e10551b04801c4c140c01c0c4900b0324081007501c50000c1d80348203c200c01031110070352913140da040010106d100b02030181072a02c0845202040000010700440034441d0900c0007a015031502071800710110b50b40e1801d035542d691510300580307c00d01160040c0c4010300c40c1800108040703030158046800789000351104c0070105011001101920824081c20b60041c001010301c4000076180302d44915071881150803181400c00800842413213070090703400a1b00140349030151103054040f1000b9515148821300d030a614084 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 420155134 1250 420153884 420153887
    0x40905090c220e010c1b0f0b09060901060608070c02010302091306120c0e0702030702130e1903200c0d0312020c06011d040201090302091f060519021b1c050a06020a030f0507 76
    0x18000d91b03a4107000c0200390075004001949001d60381c0a0b070b02100700c1c0c0e01400c203280300642d6400c0c00c135040030041d8a013510100d8200d00545206200724041c0c1e940701075060103540110013a4201581e51038005190040340c9070091058007810000d40540b41220000036114205003a1004160348086500ea401100b8440350b5903000c000c0719180c94068403203840411900b003062000707180401c03a040d55801290f158030305030f10000345401c030003a000340c2d070b1100200e03030b04d0141200131614150701c0c0c00c0550000000080b541000c4503000903460081c01c0a42002c85242c0847c0d007aa800507140d00047e070803a100600c0070020415207030340181d20042c072602640ca0315500184c0304107010f000c007a00c41c1129200152460b03601e6601c5840000c090a01201e00c00c0d500e1300301812540120f5024141c1c11a10314005c10064400580a8080f042c4854180800041c210a0042d2506514208400c0704288003032000452010091200d01c5880f5010044c1c3e6030520f03490003000c441016100d030f0351450a2000b88075a06c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 420156384 1250 420155134 420155147
    0x60915140d06090f0b24100807030c03060b030907090e0303041713053a050a08090a030c1503050604020c061602010f09050106140402030408040905090c220e010c 71
    0x15030744440001819603c5080219081da071300d00000b418484802c2c20058460361158400c19400305aa10b4100000315020130040710001c2d0085200c001b80341c00e030014001a200b0b40010b9010010713820009280b5444103407811a5038412030b4559440d90041c1010010400c26214101800e46514007443c150f081940c1c40304050402111ba100e848040070031500f0306096032072030320f034014580140302c0e95007646110465020181350004000c0c40b9181920340340010340300c501c3c4001266510038046c01303840034070707690710503e6420814586400028032040400050340d56201c0b48060016505107610386094808010240d49000f0441c03402079006120041c0030010001e50550400c7c0361402643e0302250900c0124010001580442003090400021506021040d40041c094400303610065202e00f0910b070600c400d0f0311003074500400ca0001040100829a46030344515044141002500c2140d100368000a40c0407017100701d180c01c60b40c0d5a600c5007507840c519102c1e400b8540d007840000d001100c40c400d0050034a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 420157634 1250 420156384 420156409
    0x9030f0d0c030323070c051c020d0503041a0c03010816030312020a03110301120201021c1b03170c0c1908250209090d080c0909062206091514 62
    0x505449403070f004a540310380201042e4031313100c2d0700800c0b0180c5004000100383c442c0b421400d030b8082c0070364450362101c8580191a000c14112a40051024a0350183c0440302c980c0000d100350381c1104c00606d10300900d0110034205009200405c0034913100d5041c07421240c1002e49420f030031f0080450034901080020b4100b0340540d4042c0040c0ca0050f00c1c2c03800b48000340c01414402185200e000e400100204e04500030248003000c5c58000c0c0c0c2210f4100b8001e40c0e9a881c040603c1e6450b102051144003074020720002484800b05141c0300307103450301100940305509400000d0507164080c1010001c150304144000030401090350120600c410490098162102e600700e118182c404107941540030001c1c11858501c6030400703407880e8044c1820740030b0b1034950380e241d880342d65050090001440f24004114840541c0e030030303074411600c001d242807031a455402c00c2004a0344041d0013000d4810041000344c40210a904c0b64100410725440080303500d401100f810707024555190003140314059808900c01260b06c13002c40d034111 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 420158884 1250 420157634 420157637
    0xd110d030519110c1e03010f1a060f0d0b031c09090b19090b0a08070e0f01120c12030e06120609090706080c070303110d090b0f0103080304060b01051603020309030f0d0c03 75
    0x403a070079550840170306903030070581058141d07007464020701c1c440076550b100c4139505010f0407103400c0c100010010000039105248049095440c10b0042c10025000c03036024400b4440d0040440d8040c2d03100c842e90490b20f40581580d500402c001d00c1c0d04011700d1010f80900240554100c800400490f144008060814914040d41c20110f5032002c9944e0302d51a03040d511406000f0f5607084800c0b45954804a50a1075011038441284542c0074000107900d8110b01c44026401c1c0d80310610783c0720700d42030058903890503e00040540400a501c1001151034032004001c0a080103400c54540051411005100903a20050812a59540114010030180707034000011600700080300001030707990708141012809415010f06100c000840000c442c10300240540c40006c200f486441c1d0441c040d6290288891182c2d800d10002d42015010030000c0e000800d6548440d54903141410311074182059820300400384d0923150030440140e8000a0f10050900c1e042001c013040e802c110000700401c803c04e4030010040c4400700710090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 420160134 1250 420158884 420158899
    0x5030304184d12040c12150c0504050303040306111215040b1509040905160b030708060d0803040305070218010b04032307181413230c0d110d030519110c 67
    0x3c04010822480200604444044001c030103030700e00b0442400c11f411911030381000c2c81d01e00700007110f5005000392812070314014003840c1028590307100c0c4400f8103200d81e00c950700c0010400407030b5440c0741c030442c850b8013a04895142019050005040c44111544911041d1140c040c0d140c244284122403c225144403d0503103020410405502d03007c0d140c10060034030030020211819001c5000303a103150103944961003e594200c425140c030014070503032a64410010b00b07000800c00000740424080c00007048040e202600c950802c8022000c040034004d0281c100c03d0848034001740410a01080703029004000b940c4800703140d034100310f001c822a6500254031410a510201302c0d0800c17903007078040e80101c4c80464419098802403920a24040c00c0c2910f40000719a4003803148104004010158041d40b0007142d04001030409220703100400003a078506070070031030358501c001e140b00159444050014503403d04c603481e0191240444030704500b94410302141d41d410009507090321600403600286207500d04e4010784101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 420161384 1250 420160134 420160141
    0x1e110616050f0d02060106091d0c09030106080f010c090b1b0a0c030b07080901090c140a120f290f04060905061005041505030304184d12 60
    0x30800c5034064000d48903000310301c60700304070800202d81412020983e50a588450381ca4a9060742c501c5c0b2140113100d000d01500c040030310301e8601d2614150300702180c0407400e41021518400203017550015004040d480c5c00034a210044030809000d40c124041003810214481420400084d400d406802e4020600b00c510301444100401d05000034110780e6089280b190280d80c9a04184001c81030075500303c0b002032404800100640418440c0100007540440f84000c00c6160010381a10842802d01c065405840340e03200081010425001924942c45100350b103811101c1810600460f910104161440c403503800d4880d08103030350150b0031951150407082020b02544032420b10100901c40250700078103038400d0005006000311001049001c41c1e40c202c400317005400c000010148424800d00c20580c041d4000d2000b03001c8440401d1fa07151781d05120260001d03040e0341c04d03800c044074a06844100000d210001610b102030070500510401186648071800d0220900c0340040441d6114010900c551040c0d00c2010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 420162634 1250 420161384 420161407
    0x606020c030c180411060f04080c09190e0708031c0c090803030f0a06050d0b060f030c0a05090406111c14060a0608150604080c03010e070f0522050a0204031e1106 71
    0x340f0703038421783c007503d000d0725840b08240094056000d401000100c0c861000f060805181c2000d19601c10182a54485882c0b01140281400b0b002c40d15070440c5c2e9030080d4000400c00380030420140101d84005401c20039005122004a13045450b07114401c01044610441440726280000c110380e00046541c0315a1900d40c2d4512040b00148034076000b4a45c01110000818107101e070541c03086005040894140d8995000b0f0010150b446245107100c43e00000c000b1000c020928124542175170050050802081249441c40c05410a5000c0d981c001800c9a0780d2000d540660301c1403280b4210710101c41e000030740508103000041d02070f0003940b08100400030081d0008500d0b05210980d442d8080740038180036100e5407101c11140d00e901103110f109004c3e62170140909855840007503c0b0f802c4070342c1c0002c5142c486041c0b5050000209010070405a1740712101071680100000340310300b51050b0070070180103071614210310b42440c11000c00102a4003400741d01c0c0801000c0f0303140691650041d04103c031029a5520350303200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 420163884 1250 420162634 420162653
    0x6050f030d230a03050109140103050d0f021504032003041a0a0507020405010801020d0b04060308040506220f0303120209130f0906020313120807020a03030c0c150606020c030c1804 79
    0x480d40b0008001040302c28840b0782503080300741641e00d0341c4c03c2400945c0100c403c0c01100348007480058481e40c0302025080645000c0d15481c13240700300c180306840c04a02c598001801e01070054400b20b0000704540c800400740c080034a104605000c480f805145054600491151f04424852007400c3c4e2902c00566000300500541c101c490440d40544207009039079669490318002c1d0003000380444002c0c102800540c0317929043c0b0484041e81d03070040c0c0482c2402e05003400d1111070703000011800805903404640c0d1000415414480c001850740300491500b160446c500200076101c054884040c003401409141c0260340c94020101c80b09601c4c0d107001586a41901100b80a07008810015114510000500080c1c0c43e0011083d214030703016140c203000c800e48084003112001011144000160820890440024808d40002011021034502484c0c01900f640b120321580035046044d0317820b1603440000300202a0140300c0d00b4100f040c02c42c081d012012040e0041018000078070045441031003188005010800d0898 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 420165134 1250 420163884 420163937
    0x601230913061e0516080109020306061e07121706010e03070f080606150c070e0903071205180f0a03151808040303080907051c05070812070606050f030d 67
    0x440a0111221000142c68440070520464000340d051200168000c805004001748014295480154680c40c19440400030341018000303c0d4400350070020404488814000c0f0402c14184040d010759030500351400b2840603039444111401c0c006d0300301030b0520700c440140c1080d9000c1070078200803c0102e40e0b00c0010341003410507000406201076a440100342400000340c1544152002d490b2008551804089241a406209000c011650042006000701460030148980207e0403208603810283d082c2e0720580a00c1052002200040001c68005030181030b4190200d00c03020103440c00280c828041c07001c10038241035401301400742c0140303450108283e110750380881d519080854105a403000b82e860308800c44d9010780f20990008a80c400810024032000c9250782c125000207240c4003040804141c100b814119010b02504c0c240076940c40003c0f500c03c03d001c058001c1c007000710f00315602e588914018048030000e802c03290051039080301d03190440d11700040240545025080c41c5087c41e0704103100c94041380703080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 420166384 1250 420165134 420165143
    0x6010903200d05010507170603070305062a1801030506180105040b0604031b05010906090e0112020303090a090f1a0d2a03120807210b0f060301030c080601230913 71
    0x110030406c4a660080d07500c0d0242c6100d0b101506191075001c101940e5441c5404041c11580014001c14540910030300341c410220350420318030104050300c2403088075a82040c171000300800461000090300390303814459a540103a0440d443c1c504021076039600c42e0482014000e550140782d07200a031010540d90202502c00940d4041c500310524000302000e8030f0383c60350900c102804580816070109038180280d09500640d04194101c0c14a68a00440354100c0414514240d0b01030000308803400342c64035030440303981c0680703400080403664002d0302c03200c10211040d40c1c805d40c24200f44688070612640e64481c5c18001c043d00000704040309210260380780c10b0450483c00c210099041042d00004002155851400c28503080d241e030011582c4800301690344070415a2701142001300d091409040e81a103602590443c1000703010190300244240200d0060791080c0c0040e01d000035402810804a90108125400340c5041700120300c0d100b1420054802e82580121098401c01655000824051785101c54080c000d0b0007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 420167634 1250 420166384 420166391
    0x504020d06050916020a1509080a111e030919121208100302090f18031c0b03150f250e101115181c0806010903200d0501 53
    0x32400400001d120902c03460f070180d0590400641d004100c1c403031501d0714641540142c21211401c3e900c44024010700781d08400c640303650304440c001041502024150300d03000c51300c42400c0c201d0f09a03c118640314240407642000f0103404004210440f011080d07030f03101d030740c03d80703a030418074050b0032003911030703e8681d04030685c0ca00e05c40c12000c090012030520048000001c1c0c540760882d884c1c2140c01c0c811004540006900502184003041d25082440c1107507900100c5c6003c02e01e1300d4030461000d41d007182d005c1c50080c461100300d4200320740480803622401c109481e0441c000c1c0300b0f458001030040307500f040040030031840c0080704001a41c12170042c211055030104009519100076405900586810a00100e0900800c3c1c03100c043c946960084403c2c05510034440c0060001001401c400d40030303440002e0001c041050300e0311103240001010400e030851042c10301c03039840c0c4c10041058000d0402c24020801410425a90802c0002c101c07040605c540c8040980d2008541a0902000c1080e419940900030301540c40d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 420168884 1250 420167634 420167647
    0xc090d05060703060b250f1e050601090c08010b0f09041d0c0102121b0a05060901020714030702060405090408070c0305160603092a090c02060601080a180b0709050402 73
    0x1400701d1020310a522a46040000035110040560940a480c150b00e14606600e40c01c80d0855440c1018100c0452142d096000000e80e1507a515803044030703506a0078035004441c0d1504081081c103000940c05880c10800401c500c29a07654020100302041c411005e011800044800102040104480c48a00041d000340324041090040c59814850032252000d18016920510541d62020445412001d010307030a242c04d240d00100b142d0014081881da80303031544110300341c880016506104c0c2c3c51058014070001030f10b4199508003000e0247c1c410b0002e5a841d0000c10040d0016615402501d050764002d680c071003599030351840c04203583d10500303202415400c0c90410000402c6000512407027103440c12600030040301d548200c00c0e019201c220720000d082040003032007034500c031114010000410b0502e12032450110f640c0c1a06200b1100c003105100e0042e0030200070807070556003180700c0d03a8011810b41410041c801360020440702c10200500010801d03402c51010451031032103081d00700040c00e001001155240c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 420170134 1250 420168884 420168893
    0x4090e0303100b09010806043209010b221e0509070609140a05040e0106051504080606100203030a0f0204080f0c2707031e052e0b0a05030c090d 63
    0xc200311801c460381c42c0c0700800418420300030f2065580b4a081a118a40292101c00810002e04115034a0459010310141c005083c0261100180408d59200700c0401050400c5060542540d000000e82406544110550001000710400301c00c0f961141c02c2d4006540d0b14007540200c0f101c00c081d0305200d000c500700310910400c80c03004150403003161960345440c15207a0344d41d03030080640e1101407800d607840380d951081046141481e4010000002c0b480300001030054803000011146001000c454001580104060280e1201080015040030046a0041c500354040b04001d5582c0b2008041035070b40c5d40ca0b4007030b045d003d401c80c0e0191001341201c0b8060301e68000c11401110303a9a41003100320f44c81071070b46a2107100858000380c074a40c403442c9420307409004c6a584550a80c050221682d1208035000c104032150245c84042c0701c3c1d24001d4000304064166401c4a40c09401c0170031501105001403542e580040100c816032030100c4000c920141881d03622542c03440082200f81c0a8000d00b5500007207806a20700800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 420171384 1250 420170134 420170137
    0x605011403070905070e0105280c0501200307110c1003290d12090e0a050411010201050f01050f0a030b0403020601051021051306090507150201050f0c03070504090e03 73
    0x40350290201d40d089541c1c2e02809007038507025240034004c50420a0840d005500c00d000620200b07442051320518181c0762080c8640319080c101c4840005444840b041d0300700403080c000d6411203c154904654030996400250b405448050200c0061064030000308001040c140081c844980d4001c018a44101c02c545001c0c000e400060f500c10702d45071000490b029501440f4406502810000e080c02e08105190743d5081d48000030044004140b04040c1400502c4c00741c1908240e02c61459080082006e003850f20b40000003404c98060241564188000c00030032070400303020b46044130380440b01083c0c0101c009000c00c54540964001a1108a8000410040c180c0001c0e095040b40c4094400c10050b10044070100c40c8240390b13850460b09540d229859102c1d100d05900400e41150200c02903003200807055884008482c03180d00e040300e25410201040298142d81da04107a14400c0c140024032441c03401c0c2d0b1024141140013080c550450302c1c04404120410b00c00c000b50307405403a52040400101d00d0007200c4542e01d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 420172634 1250 420171384 420171419
    0x1b07091a04050103080403060e2b0305011202180a0b0303220f061413050d0605060a0f0e0a0507020c0315040b0604090809010c061b0302030f010b0a0c03050a0309060501 74
    0x80d00e420386142040c00c0510400c0c3c12203070044081ca0401d030a5907241c0c800340418201100c000d1140c0400044040940301d00310b00c5034030010050001040a0b044060306986050340403121038907a601030640540ca07045100c3d034102140f020758001c6a07036081d045070020460352046940504c00410055500340d0f00b010481018403082e40082c500c07507520100301000c200c40340210b100058a03001c0f42080350700c00c00090200c03030707a150078440e9549444030041010481d0540303040da400d0344c590301070114074101440c19001030259202003600345800c0c0b0b0307417194050701c0c003410a17100c440d40c0d403000401c998800e10011910160040503a15841d5001038589503a200549043e16880c040c03e02003200b9151611031482e0040c0d1060f4098103103480d440c01900d04034046070041d1001612441920821543c130a9400b00c10b48040e10016124240029100c1c404001604a1203031030394100a806d0740300707401c408c4d9540e5940d49490000e944050300c00d401c501030324007440c00400c1c6904000010550302e960b4900c0220 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 420173884 1250 420172634 420172661
    0x9050306010b03010b0a030e1e0a03110105060a050d05151f061d010309030c02040203071101060b09030303220204020f0909100e0c090303040312031d010b090c1b0709 73
    0x51507601c2e003200d6641840203110300d50010204120141c0e403940680c020300030117440b1a0035650301d10482034005039001e45c0d003038149416800c18940d0408140d0040381070396041203035800030081c0d45421400705089c04201d01425100340084916401000b4003081180c41e080004103c41850703082010b0f640d0540484141e803241103041c0c015021695910403028505002610801d42000c0d42d00e2030015002401c40c0c440590811800c10ba4100250315640003d500400f29540c5140840740300350b00680c00c449450b08090540901045901e07520341d000010349421484203103820760040343c00042d0391200100d040c1c001b5049030001c24072040349042c1d08094070946d1810385a005031540d42812412090740180101c0050881c0c90011034011440940680018000502120b15294072070b22103c2c910b04007603581c80c000a448901451a4400c0a0400c21400010400071711140840e000003c01215004103100c003698400300e00c1d201c1d403c200292890b0000110401d5401a58445220390b01625680c40d0105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 420175134 1250 420173884 420173893
    0xf0c0a050f0c01051218010c091502060f070e1903030503010306230103080319050a0b1008040512090d080319061e0e0c0403020315090d0906020c280303090503 70
    0x30040c4800318072084141d405a4130545004586901406112030240c11542c24200b01200105403280c248036960758224182c80310003426190088404290aa6807102021508817070140f115881120b00d08940041180c2054000c09064102245c1c41000464040d028110860000000c0c107821100450507a40aa04248560400300c0c1024550344841c4006801c4809024010004100b4100186401100d0980740c0908901d0020145041c0c40d01a0740041c0001da44000d0303950703035140074906040002203e042444d40303842c141d03e4032500d8120700203211061000010740284d841d5942540751a8065100000c0c0c3d4803130519040c008071820700c13490007140c1c1914102011030700307010307500c442c0050039a03003400b141c02d150a240c0d403c403201c0805481000c44c2c58007848044010780d0140403400808540c00d260b21014a401c1980a14000d9078050301c900b4040124014041980d0105100980c22402e583d41e60b0300003150215808400880707201c1c001d014103141d001008140d40010b0360b07011604100c2c101d0303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 420176384 1250 420175134 420175153
    0x3060c020106141c05010b190f080a1e03090b0a021b0f0f0105071719030b0f0108062806020109060b060301080a0f0f022707030905030406050f0f0c0a05 67
    0x4002442c500e102c120b0f80441244c0e001c1c00100124641c06146510880000c101d20755288046038800701407200c0e00c100355038461030511030200d200003960024078101c0c0040021a90303a45414050b40c51000c03840060b0404882c500d002d141c003c0762024001d1984101c2c060707495000c0703200207481e00094013400f400101424401041c524015010200c0701c030000700690b40145d840001507800c0d6020003011a500443c1d03106191640b003c2c80050310801c451000440507450030007070b0007403ca0305800300d035034403507280100c04902590744460390ba40e01000c1501c4920b604000031401100411102079001c801080140002c0391090b4190000c500e80c61040000344403c5c9114002c1102d2030009004120007513002041b5003020400c9000341d209464041c0005070b5010101b50045030310150030707502c8030207514170491411440d1003030719040c1540203401d841d0030441901d0035079a00b134a0703104512039502002404500d0043e0300324107004584048425401d01aa2021003ca13815180e0220380703415640d600540802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 420177634 1250 420176384 420176399
    0xb13060b120601091508120c0d110d030207020d02030f16080a080315010903050102030a140108010b030d080702030c010504050d0f02070b0d1a1009050906220e010e030403060c020106 80
    0x103030400000d40d10241040340e003030076410001480e040450b4201755085400c000b13101441805104220703075803c00869034030094440300f5441c3c50250b083c0a800c2000c2c0359504040e4407004074801594200c5480c01598400990000030001d04041001940c540031340c0d0744c030506c5400c0001f40c2d01c510b542c08003284100540c1e0384604030348902c400c14015014020030400940b021010348003540c036491050402c1d0200b161a600c0e100c0c2260030440300d06410a07070b500000d01032140341d240c42030300401220b4020f201201d02000802d4a622801c40c0c408240011030300840c03402030007030041c1c4110f9410f1400801151403d400c2c0030782e40e41c08070300d00800030030b0f850001d803440a407010600200303a402c0008400d140145180010005022500004003100e9240003680c1a617561850940508005540d800001900b40800c0068030000030b40320510441d40c5c5d901207807819403005042c00141960301c000092a0a83d078641c0d50242c140e00c280f6070420300000030301000b0481241d1080c007074003441e6402005019100c41c071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 420178884 1250 420177634 420177649
    0x20a030b010323280b0a0c0f1b02040504050a08120a0f02040503030d0b130c17070306031a09012d0b010e0a050609040e0109140105070c02012709051302090f070c17070b13060b 77
    0x485080003201032227100140c201a04003a803c54842c204a510140e515200c85c1d01540003107002c1c0b55401018801e10050504c58018499900300488003145842e2803d400240c0d40c1c802c00c049246002d4894242010315035400c0d400d44180886400140a02100301030010154542d080080164108510210319250303c207120b40340540340d000001c4513000031030840d040b00204000380075062940d00c40300c3c0050805141a03000b01c078050310b07115403009000140d400c0c0703095440510300c0f0b070304228110b01504000e07550600d0140803140141e034119510408400401c0261120440303404540d030900746c0d18810889286422501449120000c000c5600c8550080700c20402c1c0e0880030707000803a00c549103000280e02d400d200d43c5926591f548081c0e055030b2400c500e004e0746c90071148030402400c81101d940c10f50414500d000e92040d1560551602c500d007410340909080300f20840500180d100104116010031904c5c00c07590360340d4000380c080026250648900d40180c0780154100d80d11030a010024030181070201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 420180134 1250 420178884 420178907
    0x90503130f09111213020d0b061008090705040e010b04050f06010809060112020103020a05090406080309010f090f17160308040f05220507020703020a030b010323280b0a0c0f 76
    0xb0070301442c4c410f03918048410f00c440075004039090002d0b42c0d410401651680340c8590154441d85002c01c0070f180a808002c10058802d16040030302c04500d0400020b69004601102602e00c02c4400082640b4011041801004d050300e0150700b1500e44405d1140e5248501d17a020306c555401d07078071015603980b803c1405031910b0b420b2180c2d4007540c140f44950001980a80c014140c0c141003454144e0070b129401001406443c141d0740f01d06915040002c00d03a079103580c03120451b1034062940c03d00808040c94102c03000c03d00d126030700c0340300c8141d03aa0781003c156994080c00324214441c5850100c8280c2c584a041003d556400340c4a8a026031403d0135002075103003040706818008c49055140010301040301000d400141000900640c210b0085d448003000503036035440c5000195004849140b1150304602c0c011528005c0c400000d10155080325400c048102c00007108502d5800b101011084202208042c1c1c01c40044114010241c1030400200022010f070b61380030340c110b00307102d5880d00c2d01c140140074152139003610740f0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 420181384 1250 420180134 420180161
    0x9040605010f1b08090907030906240506070302030c16140409030203121005030a2319060e010f022b18060506060d020a050403110f09150301090503130f09 68
    0x7483c501100050880b06003026500803c111403400400c48009109158102c4000f00481c2c0d4418400381404902d02c81c5140c02d50400c0c50011000c0758910b203003d0400c20910600d072089100084180400d4424000c2d078008100c01e00890341d2040d00050301501089050159010000d248044e42c1c05610709030144104054240d0081c500e0301d6400460070501520085c81500c40b0819508002100c3e2010045100c0b640d0007044a403c07140e6010300c030b0700c59031840d404005134240e20000c205e01200a12200c82450990b01400004a41c02440c0300580540710400c02d0b010407510100e40c1c1049001c078080c008a40b8014000c02c401000079035a051821030700008203c2c2d8400c00c5400c0c080d4005555603022076005000242054140040b407840c11061b640030281071400103030045820410880c0e44602c232004507a04403480c005401400010940071840100351400e00503c200d80c01d035046c0c40130350000030415005403c1e01d03541c42c146800c148000405100341c620030940035400089141c030074840e11100801c0c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 420182634 1250 420181384 420181397
    0x605031f0b070b0c1303261315210902010311030402010906120f1103060108072c030106120c050a060305130f1a010b34080307021629120610021005010b09040605010f 73
    0x241080710114a01c407500020502a026628010210b9802640c40c0481000309011403030bc58203100040035a071030701042040354141403050100607a00981c2e000d060703ca007442d190b0700a0418102c00c80280076000560f00c05d640c43c021001240407099001184103400c01c1c0c8030bc48164440c10b06c1150050f500c51542c015296204480c000d403808940d1250300315800040c00030910507182d4000705521000000222105460000104006c2c184901e840d4001c28050904100918080344a011f840004042c014412580390080c801003082c07907800b07522180c04001c0213105a6841d9040d41400d0340c00210524200141c2000110040c44c50401d0106070100c03010710800020386d503035104800343e00054950b0f41503000301d03800d2100b106000610100100303150b01d4140031440c182d28465910b15540d941c01e60702c0c031404000144c81e0307040000f030240c1c000c901560f06500007481c00c8822814030300700d62890000d050622000051040c13042c8064000305900712810008284d030340c40152109149020080042002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 420183884 1250 420182634 420182639
    0xa05040e1521030c0105150102010b0108010614030c120403080603010b0d0c0509040c050303030a020717041d0a061512050c0301241202040605031f0b070b0c13032613 73
    0x100450b0440e200c4001100e0418124060183c2505c008803020b40c6d90010b1040200c42960382401903000500307003030800404550503e032000340600281c420800140c3c0d00000071440060300c51084516099610400417031318203142c0303030040140c882650510710a60a054898096140c100341c00d00301903500c9108065442d150506111200070001c0c800e81d010303900c140c000540e5032000c3c1f0056104e003802da20700599800d451300e00800911014126220751400502003405401507a10345c492050740514040590b41c1e0f901c3c1100b03000303045650002e214203a811070000560680001290001d2042a071060006659030700c0703003a802c2d0009103c0c80510401040401120306800d02d840b071080c04083c6840d00c0c2d2040011040380031780c0d010b6800000007500000800c100c807030500900242c52560450b010007018a403582485182c0502003004d81004840408105450311003011508141e0140002e80882c90b503a040c8295804062030044450700829044129400102012100c00c403000004842d41d01e070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 420185134 1250 420183884 420183919
    0xd0203042607030503070506011508220204110c010e010504021507050708030a080f07020c010f3212010602010216060b0609090a020d06060201090203060a11040b0a05040e15 76
    0xc002199880202070621103100110414400c000295028400842e07503200c1c0c9260080c50000305030300001c0c0501070303000e80e8040598840c042c3c0c2c0d082103051007540307050300700301d404002c5400304410001d5000d49400b00c403000f0050700001400031300ca8098000c00c180b043d00028582030320401c4500a5101e000020301d02d02d4601d0500140c2029030282c412100e495444520b0545150b020005550125000c20b042001e402c035004032a0343c0c8003506d44060302d01071462400113051400c000301d5281c1440200540b17181c9081d262018115580c0407401069990105c100111031160300519020482c1d0001000200b6614014000c9a0701d03113260003000c1c05c0701041c07030702c0c1c141c02001d14221150b071150080100564554071000741900030100d5090040c0e0722071448100004507480c0f580803100b5a4140002c04000d03950100b14140d12600b400f001040580201d0802d0700707640b0580d00088a214004910702d440319900401410030341d1b21400b20442245c90782035840528142c41b0703040c590300c064030711420303217805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 420186384 1250 420185134 420185159
    0x30c0d0e070807060806040c020f0c0603071b11010201050601080f0f040f020d110a05030a030206010312090f0b0702011b02060307030902030c06040905100504050714070206190e01030e0d020304 85
    0x1a00c21081d80d421a8684103014245806a0700410000b50100c00780021840c062042c542d0b101c40c140001c00c002004035507216210008032011504c41c12000c00010069801480820040003446101000c111150303c0d0004900d20045185401580381c030000400c154064107185d40103117503603080c001c90b95170b0300c065099001400800031036500c00300450710710068840480c0700c0c854920501c15030509501d10018032044071541d9026911039032002c50781e030010940106429040d40c4d0800308000c600200414191415004e41e8004203468801c0d8000280318002c2d03c003d410f8040c070076a9161104000800381010050007050f02030342c051001c10129074664040d90003400020b03c05001e9660918890000840c590482d6100940b242c2e00c4100700000540b441100c030000d403030220703002c02090901c0100200030010200003171824001c00580c080956407920300f03480c0d904160218240e0304150140c401003601076082c07403403400701e4280103251000740d10108110b0700c1c3c0390407035004600f058034004880422 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 420187634 1250 420186384 420186401
    0x3030f010e090604141f0f0c0302040b070f1a042a1d0907030212010e01110c03092b060204060221180402121015020303010f0e040212010c0305010515030c0d 69
    0x284030700c420716011b0080702820f40c94041800c01c000502d480010702d101098a4030100b6134130030584108030520035440c0c84019615042e400000180b16a0340314548807400480c000d0440c00c004002008100402c403800620594003036119591402902018007034038001c190300d00802001e09031300030280d80380031489414a039000000c01e00b110301103a41c03500818000200c8050082d0143d44500005038240d07402d000340d120303c40418a036280307081203044000d5180c1c000d9911061144018103074896003d001c1c1741180d55031042490800201508600d8200020350292281801500600c1800000b0f02c1031012440004111800001e107002410800e00d200da014000c01207502590a01c8440345681c41d42d40400d00c0b9181864111440a0410f02003034206071030f0080510031948204018080a030341190904111a4080781403561902d45100145901003038604041c036640c07800001004441d4140c01c86030480354142d0f683d07415414030144166141c801161445020901001000c1c0c5165840d40050344 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 420188884 1250 420187634 420187673
    0x8030106030c1b050d0f0221030402031011120906040c0b09060d11070c0b040311010c080d02190e0a0b0912070305030c01020904141302010c050c1203030f010e090604 73
    0x40f9200305010350101451940d0180da0541c008189400340641110b0f441030304900c00d000030800e902800088002c03e8a160410310720102e1b0201c081411500d04215844030119104800e0240c12142c1000440c0c6410090320801456400000709a40300c1010546500868000d80100711075030801c4000782c0c80e5408082d0154000d80c08008000144019204464403403001c0540140d4403c1d8074180f0b0005419035400c44e444d6000f04101c01c10003c0c0124494550408087c203011401d220281409501401040c08449580d400010200c04020b9400d4010f88900c08039101d554480602c45c0c10b0042405090080724600c2804000c2400c09280c00c00213032a806c04a40c0c120380c038154803541d8a904680250511410380d0b07401040d50703082450140101c2d070440c0001d5183c280145401e800c440660304100384040d040c81051800d00c420310806110304a10740c08050280044207160100c1c840da0b0f54801c0312180380140c0311800220b5084180b2139494060301e004e00040045481c1e90300d6079030848100e03403c91503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 420190134 1250 420188884 420188897
    0x607021c02240d0630020102010b131e0e100902061b0607120b100e040f0501060207170307020307060503071710031b0308030c0d092a090908030106030c 67
    0x20110790ba1400780c0700e402c5603404025a00d91000040240a466154100d40f6500b40c5911158014085c0c504108000b03121220143c00501802e000503401004800c0c407007900000031501024040c0c9054200120b210342001002000c84541c2c00a902211000c4804184d117400542c0c00882e650001c0d000000401d00083c403261500c450080f45110001d07551035140c24940000c01041403490f00303c900b41941d204146028005050314a0000304a0b202c10341d034200038403a800800707003d42d40756907100a84017205a1010401540c5071880650342d846103108280703c4801e00c24260fa9061008003d807103400764082c0003001101c2c104001034456800c001d12810411480d800c01140001601d4840c03406842c408000b03646140c15800c0826000041c1c0c4500c03a404603040c4010000189000110b0798055131100405840701c60303c0c0d840d100079104c024005030000414a0225081445d4038407400e030f41d60648400c0d04001641c4101c2e60050340c8030b14402405141c0140010480103000e038228880c203104a107410f4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 420191384 1250 420190134 420190159
    0x1e04020a18060905030a060513060903120b06090303030708060d0507091a03030c100c0201110c010b0a170601050402070f0515011a04081e0102040803030c09030c0607021c02 76
    0x1012600503100d88400100000303400d40020900c10040c070042c10451400a03280b0341000e020a80da0303100c20a000703080e51740d1180010055188002c4141c0c15a501144c140b0907400360381001089004580204c900840c070300113080c03141c0e00d040002ca4150f1440a4080c50540e902c0c0c0030103449034080180b900b600901c0500041c0c3c0002c800380800400b400000780300151403044440f40c1c0990281030890702d400b96000300040b0b01110f074001650013081044800c00306000d603074240c1c100d01400c2d24122110392070710040b80382c1000f54419089886038203010303504020b50956030410045c0c040311251a009136600010b0050082c1d040a40007040024041c1041c055503102d02e9031060f16100d11540250340c150100e800502005481c2d0040c2d68810343c1215016040505190341c10351165000c051200f00c20241c075404805896080d010340c3c00800d42c1005903030700c1e4540005c1060700d40c0d008074040c520034090500c4c40040d03890007600342c810040d0041c0051a4030b4007115210344010440c1031080c0d80c400d13000b0105 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 420192634 1250 420191384 420191389
    0x2040c030605060d2a0c02090619090b130b0a0612090b0405010c0e03030301210c03050f030304060b010314070c05010e12070b090c090f0403230703080709141e 70
    0xc0c042003500f4640081c02c00c03e03803400302546210658074500c0520a54840d80790440e03021b108103800b41d07011584180151039400000d0078180240c48030f0901c2d001031010004a420299010107511b150035100c082a44225a1152041b07030b900140a60303000182200610001d03103e0451001440482500041c1040250303ca62040220845003121184e440d807003100c40e0140c0c054403984182c103041c2c004606650421400c50503682010500a8416664101d0b043c244494501142c0055803c40240c400c0040d114850503104e174001ca90541c3e1f05424079140ca0140c1d40720b840303100b200524113030007000700e602d64110886041c0e01c4144e0940e00c43d904e42d007140e403600b1003e106c0e10942c0d40f5400d2806685440c540342410240c0401007410907940c01c80707c21428551503840302180d01a10601c515078240d0b4840ca0166042d00114002085840d100c01c0d00c14000050384000300300042c02912080d11542d550f1508480f03004650040502c00c941c841c280201c181010035000c070180400041203001c41441401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 420193884 1250 420192634 420192637
    0x50f04120c050f011e0c03210518062203030e070b0d0605040e1005070c06091101120203070207090f18110405010b1905130e040501050906012102040c03060506 70
    0x80540d4003855030300d010411881e10407000c007811202801c00d590f085c410500d100b030305001160380032802e006824038080708141c480c2d10081c9000b00035502440040e038243c01504001c050407500c2202c503170b04050040c0e441c218002161880340e00c0d1180b045013991a0f081d80c243d200e490018080b8103140e2548980c0c8080d60003405140c0c081d2424000c407a45a0800c0700c0d1100a0b108281d00a50085240081682d0043c03030100e650034030b0000701c2502003415160060100c0e440e08001002519141c0341000b03a404120405840d41d5a1800980c0c070781082e80c82480b0b50001702e12054859501507801a102000720a41d01c1d04803001c0708684680009200001000d4400d0000c0c00704811a141040602c0031044c82c40c0c984511800f52120003081410f000d030041c008000801e002c3c1c020002d100010495251107503003000700d00003401c0e0018000d0100c2c14103103003032406004203072140045802600004544a0f51145440b603c90b4610100250080826000c0c440240300c0c034201001090340302c0b0000311b02030302c90f1030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 420195134 1250 420193884 420193919
    0x8030f220503030d1a3a02090a0501060e1806090a0f020f030103150501051011010b1c030f0807050a0302130f030f0b0108010203040f06020903010e0111040e0906090a03050f04 77
    0x4003064485132207178120b02240604256a00c07030307a810305044542c1002a121240400184000010300c1e41720b80c2c2101480c8042d0b900300a42c441c00640070040c180c010343e00951b04803001600c9a426800d407400400c9400d01c81c1d0034208000741c140c100019039501c0c0800c0030b180c001c50810380010700003441822850a0740c0c4841441131a0a400000410400c6400030041c6030072164a0390811483d4103190024a000c0d045640e60410880030180c400c014000070350110003106001070402d882e030700d01110040e40482d076a0501b0703404039210210800c0034034040d0010912500255848602e002403100b803d40c025045004000c500c00c514801c04240c00e44090603407406980984240c59084145280ca54031886050f003040c02c0a900503c24070000030540e014180c11182d1054016844e0010040400e00400403505013102d01d6007403490f09034950328030400800990384070681211456580200c5140d441d0700c01d980e40d000d1079104420f4240460f00c118003500c41242034004207803501c0d80d103c00e4031141e5030150303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 420196384 1250 420195134 420195157
    0x60216120c02032b0c08190e090f0702071715040506011815060e0f09012304050c12040201091706010f080109030906110a0b04050601030c08030f22050303 68
    0x6041c0c80c0158035042101ca803156804e10f0206030909070702a01a80c10f008110b03003840078080d0481c4403208101808042c1c2c0e09015003803004001e0040c00b0103005083c203071520032082c02500d00c0004142404008200c4e43e1050741d00c2d80080240f285040e8500003c084000d064010a0003401c020004400180805074001c0340500000c003101e5040c4100303804a84c4040581c800c0d40f034075040080e400340001d030010500701c03402410b050071545d146c0400300e80201ca8441030940e00c03000b5440041015960080c20840300c001c40045490f03512000020305c0103c80d01610659200c0c582030007401c140040c11601d15a10a2044c5406010740ba50303150340440059038482e900d02640c1200c00180869a03007030301d58600030b2011900274484201d8076180680101c0e000e009000c2005000715071455030030010010030200340d0344401d400c04140790a04103152110004e010840f4104105000010000c0700001070b0340c802e00c40b1103032452801c14403400e4600e403004d6464804008804004000502f0f65080c8040c2c241614074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 420197634 1250 420196384 420196397
    0x13030506040f020f03060411060708192a0201020c060306041e020a031505010509130b0316080105100b0f0a0e18060102010507140a030b06190207290706021612 70
    0x8a10400004c3c0156200041c02540418100320208400c180e4280300300c1800da0313981c0d07910300b56030410003030703a1050b02848010350005813002c40343d560b0300c20030403550b2182c40c40c881100d00200d80203a4600360756a0801900503813103006030110074500500110780002000340300080301c0d03031400303440382d551710031501c401c03112690115107056140e405004046036070f14440104c0c0061307401c2000190090181200c19801540024103040c502c12141e1300090400c00010120b031002d07450120941c2e4140700e5170007a400e2075404c0c1004144504c040340c44110035220034108081c00c02941070032044e0340350403004242c0108102a80c0e15681d0340c4402c803886c00403443d42d400303001061602c000060300b1344002602e141e0401c035083c0100780c07145030407006460b10f0300348070700d00412140070f40c03000101c00307010342c000b030a10708009100c0071020550006040070032100860804903028542c0c0c00003110014041c03044260700c4808000343da0001d0801c0d4000d016031826003008c4990082c0a444084c1c403c0e085a43c0e44011829 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 420198884 1250 420197634 420197663
    0xa050d0902031510150503070804060b030f1f06061416081309231302030a23070f0302060403120201092001140c071202010504030510050f15151303050604 68
    0x85040000340174002601413020b100030f42c0e10005060744001001a410040e0a070041410003401c0e0704198803824004040307582c0c0c1d40c4001882ca443d656a440e55010300c026050020f58003280340d009100848801d91102000b002040780d41c4812640710202150151401121842c0040d03200d2000e4a0740c15920a000510741d410210701900b250184500342194a00820809500107500110302c1c0d404400d072101d00b8008052840030900d070400345d0400034803451114010045a00301c9aa59a050390746030f1080312600d0f0760301c5c22401d200c14842d000103500711100700414030100c7d8140c0c10b50b00e0002207a2000082c0e26180f920b50071a01180352484c0402c4482001d11001c4d00c5d83d00003134542c01a056511003038584100c42003001e603a0300c090b1240400301400164200207581c00b03081650025604502913031130300044030b008003005201c2200ca038410b401041c80450f08091150203025081900608082420f003030740188012076800c22406103080c480d941a02100065061040c3c0c1d01682c0700b65408070b003403203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 420200134 1250 420198884 420198901
    0xb030402040e0a1203020f0c1203040b060915060310080613050106090b090a0b030a080304050d14070f14100c0e04050a0e032d07121101050c0a050d09020315 69
    0x1035210003102d00c41c3e4851550800402d0313640034000c03003140c154240140d880c071701500381c0c00140c05801e400003031501030804070700b41c0803a5020040d0f01c550300c036610030a1565211420460b0410054503400d01c4680d42420f900b0190030203d00030f64010041d062100380003030799000c005241100403546030b0158240310030210200282401050085c0203824006d00018400c4408140d14000060508642c641c94418100c2542c500744404001c0d150000c0d00f02d40d0368a01400c1043e036034440c0c40c0d072600000d2002d0403012225006903082e10601039126400c0c0104480719211800c2c00c00203e54000042d02840712502825a042d00c80c0700c0014091380c961440301c195072401c120031227000800400d4158188089001401004004c541103036050820140300c1c400c981c4155110711581d00c01c040c0ca26a000565101400001c01c08101c000509603549000440b03881142c500f80d07002a40ea48400d1007050102d2401c1c80d0040001d04920329072410000340d41241a000680703400006038051888400803002c0c0413022 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 420201384 1250 420200134 420200141
    0xc040501090c020c010c060204030203060126010513060e010605131a10140304030c020406140913020108011505160303050108160e0c160c060e01020c0301050907031e0c0b03040204 79
    0x101030010040140c040d00c0c2c40e0180d102c00c941580e290402440714142c00070050720303506980203560040c0884809607195650100e034072460001a15140d41640c8590042d000140039241c0b040c41d58040c2036000d40314668880000d4440301100445c0d40d52a2038020a00da115100642c0360380f02c0544001c140c60000302511900c03800c056005500a00c00c200c07000c4141600075001140803801c01d641555a40d64a060840f801040d02d0030095025003401000585039240d003c1c2c42c47c4282088408508a4580c00c0380b42088420020000b8003040b0032070010091710700394580364a0100b565081051411000300c4900404561002d0100c000c40c0d40c4000600c51600b040000820818400401064040c10094401102e410042140c042c7d8500000d111200c25540c280040c0007039409040403082507141c61015007120003046446006200710b2a50603128a814010f95000b04000d201402600e420360700d030b80e541802804440a00e141401c0401c038000b07256080c0b10001480002e0955440c1c3c2482e104100c01d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 420202634 1250 420201384 420201389
    0x209040308070e150a2102160308011221020114160f0c0803010308090409051606080a090c150e030a03090501080a2306010210060306064716050c040501 67
    0xd0071900c9042c44c442d1313030303400d0843d8012409402c003900c80601130f10b034070741c000c210600c1b002c4d6030580042041c5030010705003007031714600c54403988038000107a0301c804005110724030f18030001d051440b080403000480b002140c07015194521620010440c41c0c0705602902010000f960326001824034010801c56496209400c030342105c13881d1401c900c240d01d640d01c03103c03468041030001030711000c000107211f4020780d510b5100501d00c0b40c0c00380585800c01541c00c103c12000301540304880126141e2000122509502e100700e110700ca0f070018880540074201911002c80c1038036000d401003032000100a42c28a03640400800d8000e41c866a035640c041806d103030005202c1c42024014030750590800c2c8405015003041c204c1d480c4162052030618030300b545c80800403443d001d1601d10f0700101070704d00400802400708640000e81590000061021540141e90501004d0261a840c4281ca038031014541021091008036402445415031814ae061980380034a110040d4403d1004594550000e00300c00e0941c200303801501e00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 420203884 1250 420202634 420202639
    0x303060d0c0815040b10080d030e01060e0a0e1018140304320102060717060112050705090306011a09010f09030b0f010806090703110111011e1d24130209040308070e 72
    0x111b092400014554482810007003105040d180c03881210002c0c82540081e00821128010a01c6410b04030116001410740740504038850045251a241460250243c0c00ca4007029442100c1c194910303485040001141d5004010a070004000009000c80310f0940b88070406a400d00f40d1b0941d484200300300d14800c441c9124603065411140c01c100c0d820350420118103101c180b4844104041d5103c1004a0f02501c55155048455180005010110b82d010717010707154202d810350440321a07036207500c181114030455000e12110340c0000c02c40da00c95940300b40c030700c02241d80050503c440100c0e26551010f481400844003406041c10035801040440300800c0110b4006042d040a011941d04688491680b01c40304000941071141007400b07240c4841095020042d000e5801d00b40c003454161008100b0003402c98410350601c24661503a0215807600049001c0010300391064400c006a985283d1307843c02c03241c009000400040342100e100002d0703203403d0780d03e900c0b652080e0380303019071440c19036006800c20624819090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 420205134 1250 420203884 420203911
    0xd0203010b0c060a050609010b03181501080d11100c110a081321030e21070302030c01051213080d0e0a03091a0304060905031908010306060608090303060d0c0815040b 73
    0x841901e510b100703a41274441d0310001c140c0d2580e900c00341c45900302698059403c50f21400345210346003802002110f0513140200113031050915035540c110740c1000084541d541503007109001c2d416104859005603843d04103400c055101c0a514200d05081c81030b210341c161426040098600d02c03440c089000700000e42000740314070100843c644218480386201990003418001807503003913181c640c3c842001c800b8544418460341c0c01c401c0340401454440c0c2c59031204030300900c40c1e20781da8a0998010001d60340402c181c85100c0845542c1d003501804411010001611020420000c680c3e020000e070040d124480034050013070001c800e603807030b008010070781075400300b40092124602207101a8400c4100ea411981000c40407420f50100c1c1002825449500b800402d181c4002e20202e90300c54101e004030703040300e01890041140c90b5a55400b80c1d120b000860300c0c1c40d21500304000007102c078039240e00c050080b20300440d44d4080e0340d0703143d1024501e09242d202d88683e2012484042004110400896691094407220b000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 420206384 1250 420205134 420205141
    0x501030302100c2304050307080a080d0504030504120302030909090f0c061b0105010e0703050708040b13050f10090501270221100c0305090a02240d0203010b0c060a05 73
    0xb911410310010012005032944407104a15200350110311603505011550304460038a405081c9250b4400d2107024003c0c06800303000905800007040c507050240d0440ca02c0d07403400d200c0305950002420020803c07824420180408240c6107942000c84401d113110b40c00940d51110030004101e48410010030044585c2d010304103007201c440c004038241004d9501a100242c84000110040f5101c0903031601c1019258030380f130000500054000e2015010301d4082d24100302c680c5940c0022034941c0d100300c4d80a0054440000400d1100440005203076443e030040e41641c51860540035240e041051400121206a84800040060040030302c00c0755130407a42681c03600318919210303c148100c140c0104010f4403072036514044450b1003100d004504a40d10011341902d0035900320203404d41c01000c0007070543c40000c0c64a00007030b0800e000021413000ba90340042484e500c3e0b0001c0b448406e40755800001c01e00200c1c85c01d008040501e901e60000d58064280e0000c616292071140c101e44d45452030040482c140d150406007030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 420207634 1250 420206384 420206387
    0x31c0507030e2b020309040c0f140c06073006050a0f230303040e0f180d08010302040b040603050609030d050f0c04060e0a0e07030f0606020c1c0203010e0a1a010905010303 75
    0x400c4050520b207882c01c0303c003603240605a003075000740032000c2d0300141040e031008042c5034814407150f080920350b20750386160341d49685e0021181c004e580c00d10410764840c5000c00c0005000c0c03109450001e070040700b880484070b440d4426608400c4108422a2441e450f41c1c2c00380300515010566201400110013511030003460210b000f580264050a02180004a50050540c6440c00d100f03c50203030a0380c00c580d604c00d00300982e031030b101c00b031080f92150100f082c0904200034080d030215a943c8041c095564580c1c04d070f401c50b02004028074a030dd0250740d026030340f02800000204248103c0c0c2c85500c0c41000b40d43c03508660780300c21059940042101062012050030080b11040c0c4009803415a00527240004496071180f02042114440384c10405e0690f94010410200a034182c0082c9046002c0318001d00c122030b40c030001a603652108000d01030784444c108003644a88007200c0c0c1448400c90004002049000c032051806080030b00c540ca064410045424500d144d00845a80981c0103000da0344080029600d0740c0c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 420208884 1250 420207634 420207673
    0x20d0e1605180f060f0904030e0a06090501080a05060f1003140a020a020d140403150c0e0f3d05070c06090e060904050f0d0203090102121812031c0507030e 68
    0x2e5040c1100d100202d0802d0316110a0152052001b03050f50601e414181006090099200e40b4503224480005000c904140724481c40c81c105c03401a110b00000d600c4003511540a050001c00da10342220500981d0ba6281e03480d20810407501c00340d5100000c18078042c1034049507844e80184985041c0307004202c20301c0042c1c4e0001d8250301c5008540740080b40c0019600c189822072180ba880900700050001c1104d480c2c0d40f10364406440e107200f82d1644042c40a280d0184000c006030035003060391103001014040e80d0703c05540c50501c0b60781d250546444000440b1031101a03405240315464000540c0030a07810f04002011354a980540580c0c18003203030300352a200244994680040115018540aa0100b41004020410310343c00813154826110381c4e100111000b035407030300550f4182c1d0051054140f1400361311403080032a40d242201c0a6100c0c14618040140003010903001c1c0c51001e5444200401c51903203113489500c0201c010700090218080c204030074003c040c1d0700c15446400c0c86421250fa12230342d41c11080c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 420210134 1250 420208884 420208891
    0x417120a1112030c0405090406110a08090606030106060210090215042702071e0809090414160506030411010512010f03150513120905090f0103061409071206020d0e160518 75
    0x1034540b989907981e0f00c1d0401c092b040b2450b9403900701350080380d046000c54004000c1e61040c02d84004031091a0b64810405081e2411340c40ae0390056003100111070141e01581d0424641c00f0300203045405180010080b024069004d540041c41d2000c40b02c0780c10b025403020240f120030188155900f0740c1443e40603244c115129030784000c0c0401500b0014040c0c410088884250f600a460040042a541c9094201401070100c058071840903400742000940c41e0b02d0b01901010160740b0064411070841d6502c2c3d841b5030300c200d0f6010781c040c18890140f0400707104103032540310a4040e00340400c5c411165891440c2c9442c40303402407050091040c1c100002c04c2040c20070001804003494000100044101d0408000e8882264541100350400c28a03c2008040c616441c100341c100c903c030f10020010b02c0440d200703400e04030005445400243d00402c2007001a00110f4180100140c0a031600618000e21104510100c0e410103c210031541c00c10200c20110344411001500101415115140d010364090480d04000d80c004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 420211384 1250 420210134 420210139
    0x9110a0f08060409020303070f020306130309030809032d0111030c0315150d09051b030303040321020403061a0321030901140405030c0105010b07080417120a1112030c0405 75
    0x7000003101a0703590b03008200d42e2600607050300c0d07640840d0b0804a4070301c80040001c1e800392007100c000c1355105034141c0155030701c030781c055072021070203030866070307485002d9112000b0664544035080e01051200c0e4501064408102100b112000382002101d84a00b502c5e00001c0034454240c0500c10000819490b80889512107032140c0141411300c5034100243d80296000319449502001060441605500f03510115040d0300400c1112a100480311607a00c0400d05e81458940540040c0046000640204855000310210200030104211085060800ca8205600c00ea94007622070a041500c9017900c4400305407058181c01038030300d09540044009c8044541e145201070b900c40000090240c400030740c003943e8020b03c0040c43d00c11a04080c101241e5a810110418003a5480c0c00e00005030441c4110403500502c6d48800b000d0704252820b20703480d0103948001d10311800f034040c20211100d803409a000401c03201180f07484020a036031700f10b4003030f07454a01990601580e8490400520a480840e06d0940b404c0710b404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 420212634 1250 420211384 420211397
    0x80f19031d010c05030c011505090606090d060605040504030f17010506032205070e04021c050d030f0b030d0503090c01140d110d0e010212071e030e0c09010f09110a0f 73
    0x200c0c0040320f0f00381501d0405401404045001c2030110010740002941d419441d0f94803407031039144c10410084100c15513101d42d20501c20440e840c2e0344d04141101c40300d0140070b440c0000d0256038903030100d001d60b0300c1141c0850010b078600d020f103845d81c1c2d00f2819440300300313071404400d1075150705020105106220180089a80750b02040007192404007100801e04090341c0102643c034040e54500d032008104da01070314100c0c458030340802d40c6844101e0b458640c200d0550800300418281010242c150000c02c60050500030080e00c401d158200760710100a881c8a8a449030f0b01e907682c900d858035480341010517501c0d945040110b82481c0150b50000340f010340f140b140100d1800030303140c2c00c58180045584580302d4222103840c1071164405031400194080e0600c0f4024502440041d80da84c3c10481d51110010110192440400521900d0603c6580400f4161700f2070021214680702413000034500300804d9028504200c07059105011100890060074071403520b0301c00490a010f4a0240508107650140703110041251 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 420213884 1250 420212634 420212687
    0x1a0609040e1002130b0703050f031003050d080a060f031104020d0227010201060504020a41070c06050301050d080a020c0616062a050d0e0106080f1903 66
    0x380c076444050701607001c40895004000604610000c1d4214604049041c0d1980c180012180000c0003210900750385039035802c0c9414a19a60240300303400160128040d85490100400007070820001c0561500080d00d81000d1490b005503408141c4149403c440c0240d102080708200007030a0102d845046001203e025803124458843c40d802030044c0c03060040400c2a001120300e45074400200100781c04000e90091042d03503112024030043e40318405213280064150412083c6000240762526400342c01d8402c6440207200020300d118502004072501072610340c00150100804c01e840c0190030003407650703040123800d540c90240080c40581107220094004000000c152500d14424009811010001800941c03140c00781a546849284240c1d0304846861a0180c101c050004090070516601c18889400780c0054806804603515041240c507203011540b0780c1410001c010303080c0600005050350380000c099509102c0030759890012130640807540007400d1035129020960048c03004040c02d000e00307401d0000d82c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 420215134 1250 420213884 420213889
    0x9210a0c11191203080f06010801050d021203130e0108070b07021908150103060b011e2102031f060309030207170f01090b010510020c030604021c0804060509131a0609 73
    0x1050003110303040b1403100b020040b484800f400c48440d030301c9010f5130310f8004980c0c4003400c104002009582c07490100f64a200104000c0c40c1c51120350103102e00c00b4007080d003108d14000340341d86141c201c0c2901c4000c801002c0c000b03102201c0c5c0740440b1801403034698010492a89407519040591041e1301004c2d00485480c1c02d040c1003407801c59400d100074481e20085816070000c031041456030000070f0004030703103141c2404401000c641c40b038100d0301d20b03440400d480d07411020301054003550542d4060401d4868061b21302c0584240c81e14503c050742c07040b00c00d1001c2600e206540801f2010300e40e40d980091044c0340ca845018004a036002458005442159031041000815100802d14201061403010100e42c01c060303040c4100030070300b03105a048540a0b80c0101c404003102c80140e03100e011001c4181e4043d4800360016000d032030300703c2d0310151941038a143c1c0b256030708503a1683d01555001d5008040441c000091040c03003410700303000004040c1d0801808200c1c0c0e008950f81804190341d190a414410b4501042d501e0030795 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 420216384 1250 420215134 420215149
    0x9010902130e01061e17072f0c09060316051003020c030a0f030c020708030d0209010c0203100b0901051509040b031009291605130504020309210a0c11 66
    0x203060499211510b503a54150080c0202d17040c1e1080b03100c21460303294100100c1e01419a00d0a500201d00c050005541c0b98241104e02641a0984d041504464070010700e00c01314584d001c40200f11014040d05d0321100c80f4080c00103801e005030809000340c5c000884903500c10500d01045060750000c4800701600041e5400460107806224014021404001200301c240c1c0d0300a02a080703421010b45003482030424003002680c503520305101c0c20003117804c10050600009035030b50041003006414104880c081c02f003900824075100303500c0076002c28150764404040d104d19010a0321401403404076100b02c0c6007010300c5914040c6028140c82d0314001d039154807007041e2966042c0205070510710700d401c1c04c022190b42c1e4208603800c02c10020000c2c01000075590007031003c1d0701800d4003a20401400181041581180390100d546512104002c03001200980b80421596a64001140111980e0000b404071880b0044070390703000d070001c540295800c6002c00154803066006003959901c0743e00310072080c103151000008104130 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 420217634 1250 420216384 420216389
    0x4150203131202040f0c0e2407140f0a020d030e010924031409030301030f1104050c0c0d0908060604020f120112210e090c12010902040510030b0901090213 68
    0x52a0081d200801c02208090400c840580212410703c814420404800c04540b0303081203070000200d0008610180d4140b10224101c8200c0c0410554550003604c803401c1c01c540c014060854568204d045408580c04040203031100c0c40052402900c901111580010191008060024144050800044a9603018900c07000c000e2805594242c441c404031076508100c2c14046103001c2c0447c0c40d11030041c0f11a0301c2c40c8101031003610000d000b5807940e400c503151a0990740d2450340880f270442c040703042c03510349480794010503000340301302c0384280c2d10740120500740d40c101055a01e00f201008003030201002401000a40150400c40c00d860050341c035114001540c405226000c1d0518803000d80301c000051340c400d0f84409008641c0200c607214245e440280000700100200380b0313100002440b1190700d5000d490a5440d050b00400b92955440c41e01c1412240c11946a41c26070000d5005a070214042055040182c4c0f1411100140e01c9c2c01c1100c80407080000e1400700040c0205012203a0100c1e8800240c050400070001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 420218884 1250 420217634 420217657
    0x30c040509031c060f0605090904020d0512070b040218070c03030f2004051801030f03080712050906180a0308011205030f0d02030114060403020117071206060507021e0604150203 78
    0x1c03e14144409031a95203e50340b03820303101c031000103905841001074a003044402030020310951256000c124a004000d44281c6481c090504502e285012002c003c1240603c22400c1c0000d07031500b40104001040301c10a0a101ca00803601008001540700040b01005541400e001513400309100310400103000710f01c5050120350140f10a2003043c41d010010704202da5007182c42c9403500d001e100c0c032150700f50b40a100c001c04518202c0d02d40c80002e801041d501d5482121031801c040500d1304001d200060354015552264036800010034054100b011802099902e5034010081140b002503950090030303400d0500c2064040d50f00118080200102402140c40190890a00980700c3c0c1c1d080801c00000d60082c4201840714269100200305802d0181c00e580407260141c41d20480e001600c4804044500001c10a0003008031079592000019146c0c0301d414047c0850365903c5446a01c00d105002002110510103a5040f0000301d41a466641c0d050807107007500e5604600a608006108042e8694050801800d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 420220134 1250 420218884 420218917
    0x708071103041e090603150903030209150c0601050103020f180a08011e0605010c0f02090a091202010c0e061201170106330804020f04180510050f070201050105030c04050903 76
    0x10f060ba000881c0360002580051010070203a60f10292034040f10a0782c40700410855812244400d510040c0c2d100340340650190802600c1c1072202c03070005540d02440480c8080c4010082240c559035802040402d01400083c00c0c2189080d001180c803d21034051280304050400e8041c1c0000c45584034082400300408003032000b40000d141c00074001c80c0c00b58008400303140442c80c11500160039841800c0030300c0c0c3c486c0c000c021740c40d0122050f0284001c800e80102880e500c20f8440b03c2620005445900f03484014545500016200c4603c0ca03000300f0b007100c6c502641c0c4c490541840f407400b051100820860441d440006015190484107400e1409020280e200098030701d0011466582283c0400c4951000c0003a4600d501e0b040d403008a09032401d840c19940031b2341000d07440e024541681400da0110008500c000032206207644a650380c41e01d0500075001d0b1105c1070b900c907028003459400c1e1100c0e01d50052140d000074010b9604000c00309686180d04a07050744201d40311800305004034400e00071928180d51284112 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 420221384 1250 420220134 420220139
    0x10b0903010f050c03060315100e07030e1f060603051e1e09011b11060f13020d050a030e15030c07231e010212061e0a0f0305010f0b0108070807110304 66
    0x3c04d5001190f6203400390141d4001ca4099450b1400c0d480c0c801d9100400032050356050600c4003d800300c2c010044000c0c140d8030701102420000800140000d83c0b051121102422410718515050721000d074014010b26091000380f10f801180d5040c1410002e9003c03289d49130550300c1e5803841c0b00141e405443c48000d664240f00380420000c044d00a0742c4000da001c684c0411000040720304840b0035003010340b044c0f043d4006c4c03c04070302545000003880d0713001401183d100c490b5240c250000780e000d0030842022207050f8000d0151108050b0040d0003d0740040c01107521562000700480d0103401488000c00148501c032000544000304181592074040c2d003580c1e50385094298440d039564603603649021103c0b075000c030b1092000310005034050080710501c4c041c0b042e0200c03180e01c071f920510448205100018114800c400c0044c1e0a42c0c9980705008010b1035103416602c5020318505049003196601e09540031080e04003440007510f660410002600201580b5080f4038603580c4000880c0c0d54440c0d065034039158003000800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 420222634 1250 420221384 420221401
    0x150405090f040204061406161401020c0304080d110a12030908030f1510090302060d020717040906050301140c1c05240a080a08131e031104060e010b0903010f05 70
    0x4a44520700c20342e4100a002c1d2a00700e1586c16000b161400caa21460403c0351225100303140b114802c019104079120704586c0c204015213802c3ea000303480c204205600100d0f0070411140104a801003810f1a418070700000c102c146145500c41c0503640700600340b500000348041d02e6912942c00000c485401958441d16801c00040001e082c1406407a07495141c20024101009032820b04a4000e220802782c40e8001c3c3c1c0d030b103143d0034080d86d50054072070601c025600340702c1840465040d10b040018601201d40e5595601e003482180012600c4a80000e8026032400c19a4850b45680c501d03100d412210161811f078a0355551911140044040c401c0e5914990421050006190300f110380d40840442c0000d28004078104001840714050b00d80c8103001d000d9000c1d104060100da8090000e080503c56442656040c40d11a09084030351500740c0d001d000803a0300407504205004044203c40c0080328201c2d01800818a003000841070b60300c0602490078091000211089181e0f400d600c012150fa034094018072043c40e0140700f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 420223884 1250 420222634 420222661
    0x2120f0a020607030b030d030f090227090a0305091c020a08011e05041e051908092b02040e030c1f0b0102030301150f1403090a03020706020c0105040515040509 70
    0x31400544210004201d502e80030f409210031501d00940105113031040b80100300d010300081d0101c00c8103d9550700c0f40f080540c0710398210083e50001da00b0800424070704140441c041ca0401049946c158000f02106000203074000304449080c1c5044652085058465001031010214050003e50201004400060304101904101002d044050000c0713a80c8840310000070540b50110340081040e005512081410748203550b40500113402902140c410012010100d09403070840102030328107030404901d42c8000d2510802425980603c20000d108640c11300304810302c5900341c800e000b88196110350102c0ca140c48100305581c83e03001d09008603001580741064601800c0c3c03100100d15289420216003184550001003160b04892400b100d8076400150710100b00d0b02000003900e91010000912208520300d016a8040c5028010080c060448045940743c041e1500c04258040740564015440c500d040f6038000003600c00301d910a42d50403000030520715144400e48170ba5003026074010f0610050003010b0003a5003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 420225134 1250 420223884 420223897
    0x5060f250828060e0705040501140a0527030c0a05090f0c0c01060e100501050a0f08060a0f0e1014220b03010e031b0a0f0f02130507050a091e0605030702120f 69
    0x45002c4c0103500c640604403440d00c29800391a0120724078404840020720040020400030780300b8038056040000308000304014818421814160584403400901a46001e000101c00030104981c124159440c1002055030050000e04006140c0780c40d60008400f000010101c40c0304021520017003044903203a290040f84800180c603088024424451b0204039540684215610a4100d4440320504601548d0448a030070004200580103ca200b400260820664000c0b101602c41882c03d40314910700440880c0700d06071075038403241d100c030000c02da00704054a4003503c48180b8640180f003c500f0b44030006010f0082d0948840c1540c241d849d00703c08070b0425402002428248104a906405210f09400c4c2c0c1e075903d00382c00d4800303420480220701c01800600c50081190107540f000c0c041905456001150b42e041f40c8045540d080400c80016050404a601600c102c0140260b90030160783d4500c02611881040c00b02c1c01742d08144070000002c514403074020040c0e03600c00da0440c240140d41d4100d02d02070704400d4110a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 420226384 1250 420225134 420225149
    0x18110c0708060a1a100201110a05070201030b100e0609040b12030a0807080702060c1c090c0f0f2102010c0f03120f020712030b190305060f25082806 65
    0x400125201075003500400726000c44407402c1030507001c554020840d01d0617504009205541d610740054011003012006000c000301c16445403510f0751120300001d8107658240c5d4529101d030f20300050321ba002940018424031621001c0d00c0340c80c1c0311900d010200c0c00a00c44548400e50101942a001d0345003080000180041113403652052000d0702c90b010103441008059400d500585c111400041c0c0003240400540b540e042414002072444440c007003a1400c84146d048107070340d10143c440003884001921000a0020301c0001142040c2038a41400c0020459007d074080408051407400b4009581c412980e281030290809121016602c0d1458060841c01400c04401801410500c84a064240a100780d60649400141c8503450040c03003002100101440025180d006c10f0f250701c040b400b110305022580103544904028000b5060a810030121540c0080100303d08902d81d42c0019046411850000c0c034855980c00d104d00e5a4846904404408903c5050050303031510382c903414840424640c10850864054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 420227634 1250 420226384 420226393
    0x906030302160e07050f0d1407020c0a060c0209040f050303090c0f0a26070b0c0106030605091212040804030819080916060503180307080c0c06031018110c0708 70
    0x10b01d4849010b2956214465481c901900041c4010740680700170400302507140149032800700c0f042060f0045642001c01182e00c07011610400c035005404004035592004100d81c1c4010051505000800b034030448100240a8180b24020a0812552000000dc0240c6c090113036a1649868001c0d0f40d130300c940c8074042c50700c2a0740c107405002050030800c00541c161000e811081c0c03403031061540b290300070004581d041d8440c0c2c8154840094041050740241c030f071690b010400800c80900d582020015500c01610b40301103500092105c40b07100210b201102c0080320240391081140d960b07400c0c0300905000c1e691028180c40f200007044561410820b07521801c2c9030b0300c1d46918030645c41d04200c6d5640c9607180035000ca4640708214080c0f21190058000e154403600e075500c013070350074840030081b2410b40e0800340046400c0c120104038085401010300246007602c800340c039001d0035442d06043c91049092503204407450507402c412400100380458004610001002220721b40c0c030780c0c81c0c50070b10350307102d003075204241c00c9004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 420228884 1250 420227634 420227653
    0x80c0f030f07230d230705100c0201090801060e01051002071208250302120d1b1707030c0e040e0c0406180609020702030a1e050d0e01031d07030809040608070906030302 74
    0x20980d44180b925a00300e60304990203014000c80d02d03114595800951042c0c0700d00e050010780388d03032180d11810314848550b9071400d41152510000d45600c00c1354000c007441e0313418000705010f092086504103046800c101c40c07105206802200c141d042c128640c21407200c01d100304c142c070010321541c40c0041607800f100c0402e048904040445504186160510040058100d92001c99030000c510000d840240943c3c000091300385055851081202c01c116840400701d400600030b03175451003c3d00011640441d407801c0c1481864260741c1c00501b80c0003401201c6104a03500c0c0c01d6074822039410090718001c8035003e4400c005050303c0d9130800701da0000501105000900780304000c01c001203180291a11194081c0082910340820791ba030a0312401d000300400c004141c11003414012900800ca054054209510303003054520302031000400344c41c400380000303410f880c0008000141d110001a0f1000312904411403a4840380900d00140140880b9072100b0418858000b01042e03d82440c0c5c0b14004603482902162000c01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 420230134 1250 420228884 420228889
    0x301151808070f150f120203061c20100e040c0509130f0b0301020403031706060c0610081504030f0e1c0b0109230a05070e060d051e01080c0f030f0723 66
    0x108121600e4000940ba00c101b503030140c1043d0082c5802180041046900e41110048808a500890019200400c0d1034801003e41a4280a41c05c0213950644990020190540b40038080350500d0a02a000307075540c0215124491040095840d000801003203a041d074007413494144060026030003100c0d502c40c90924800b510749814070807174049a601d82c440e160107400c0d0540108035143d008044603040715003000590004070060204a01c500c51820141908908081030507290440d1640b507002000c1980e414403000c00c1d0071140790760b00c10f800b61810b0070100d103884010031150200034080000c18008500101c041019280c01c0341d050350b603164000c014a00d449814900400d50690113031180c1544040858869812900055400740e01400c0054040000c040400c0c0550b008121440c2010359035024402c0f0241854030305000c5000d2080422036550400c0700083e00c1e04c1a4034a00c030311840f1001d424154640b402d00600000300400380c2990304050340c450104030200001c0401e041c6a002132040010140b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 420231384 1250 420230134 420230147
    0x30509150a0e060f0c0106120606290c1509150609010614070512040b0301030b09120d0c020f060109060609080d05030a050402010309061e110301151808070f15 70
    0x90065841400c10340000b03080c8107080d0700011100b00320304010883e030404558240600e0000304001303404807400e5111428a9011a000c94210802c4003a1110b1242100b08031821800c2c00a06050f2145030b84480030300700c1a2901540601072018650300c9000c20041003804600c41404594842c2d62408507580d240c10007213402d40c24090400810803288a14619030683c03400350000600c12400c8038905082d42c056401e081c0c0055101d0702d40020000018010402c00d80101504081c044000b44080349100056034124042c00740d010000566684d4003029030361007042482d405000b80da0a82d0303610f5071900c1c5c0341c50142201e406803902262120000003840040010084e40009081c2c4c1d400c0c0c00c2d501c0e0000c00201134503014100303a0401d41c035540e0482c0401c2140c420319a0302d511403202c00d054204c2148250040e240d031500d0f0107983c59011b20040000340004040c070706031310b0501c2c03801401c18079204030001d804400b2030300302515a10404c0008510a18000c040780e041d5581d0508840c000401403200b16542c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 420232634 1250 420231384 420231397
    0x180603010b010822150603060b1c030e040510030204050415060f030b0f06010309120903030e0111030f210901200c03091009090f020301051c02100e01030f050403050915 74
    0x2101140b03c800a0300b070340003440701e00600c0c172a1243c1d51901c41c0005000c4141d0340030350400d40c1c4265030f64815017102c1c5040e600d004085041140c0c131f1009010b058502808080701015441e0189844034002804c02484903074000166500400401803070a1a041100030300c03400b5000d12000514060300810052140c621080489a02c00c92041150365070700e44101c000040640242e042c15200e40e050000109040d03a07600601e030069803800d0b410f81c95410018815000181c00324188103c14032280c0489030040100c5021000c1608003d81e18011601e8a03803040200c42040c0103000c40800600c4951101034101003854910ba00c180a1142c002ea0700d004a030b4880c40e034141015600801c50750a00342003403d01c04c90700300e00303a0070702100f0940d5070748510701070b191030b0301451900950020050080b484c150113507524040d902c0300c01040c0800c2c99400310380c00304040380444052103076203454072009038440d40003220018201101402a802e10303280c042d00603000350011b91b1180c0c803111403d15943c0b258500f610b00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 420233884 1250 420232634 420232651
    0x304120605090c0429011704120201110405060d021305061603142802150106030f0f0c090521100b121b0f13021602010908010c080106030b0f180603010b0108 69
    0x1c24440c1c140c40c140b05c011034941a0303810b00c0a42c1031a41001903c100d801c44c07003036008004010007529440d00090844009414010042d0740900c0240070f0740e21501c040d5042c21040400042e41c80b01084030f0008520041d038001c984c4040002100320300d5203000b610a0032000e2181e12400c207050010142000d6a01884483c0c80182040309034179000c0c0c01d0f911070501c0d1101c2103130040e66010300c0d031040c45181d00e0b2005d0b0007400110703845141c480301c0403010b403003180c0c060107170751904001c0300c020644020301c065183d01c1010300c1020880d4250101d4440c4620000b03803d9948011204a0038801c0c0000c4007811000d00c4543c07003135100c6d00d40c1760070454000c00d5030011061460014520400d200040100307081d41d046000e40c029041040e90101150944000c04007031094a1191160001501c00182100c0d0702ea007112405904000206072095000402d13141503e440d41000300d1540a5400410b1805280201d0070790320401d40d10840c07030358846030280640074100982c000c0c80140c41010040d51b0300a02903034080d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 420235134 1250 420233884 420233921
    0x1e0c0507020f0414161103032e17061e1e0a0e030301030c050f010203040608070f0c0503030a0903140909010504020a02032a0601060801060c140304120605090c04 71
    0x1001450b148291022a4400820001e40482c1c8002041a40f9800720740080391108060002d419094002c40c1d800501003c50004602d1842d01d4a20545490315070340c0c44041030301000400b00f0384034032402c2407030018109038100c011070015008a516590001620030340d020040d81c07241c00d480141c0c1784a03002e02c03840a0800c0034490399115050b0700c0040e403000b011001115662482100c07561401d000541c001c500805c0c1821140b800e04040001e0340c00143e0300181035520030402000029000702d51203a0050075410030701e510f120300781c10985101009070b0001b041400f00000308468030f1101d07404440c3c01c5000c0d0b0b8660352020f03608407441001d4840c0c20724065000c400d00700100304614060300144220301e0180b06403818070800c03107090424070403142442820145c0040d120304149800300011070041140f4541301195501d000d10107803409290f0107018140c0380c6c0040024105a000300b04440040100c1080445400210304000780200825550684180035a10322082d051805e401421201c404605428 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 420236384 1250 420235134 420235147
    0x60915050c07020f040609020f070c121a0403020a060e010f050702070b040b0708091203070308100f0b0306010c2102070f081203090703020402030a050603010b01090e0705070c09020a031e0c05 84
    0x1310856400d00d0045600c0340c0c546a010030000014000341c03001c08070400c4250380340e17202c0d07107083c0120740102c3d0451410410407103028000304282d0581d00d480d1100140c8044915251414101e06060414601a01b02420805c10820100c0154046050340344c0082081100d0f882c2d034003040f6120300140c13090f40402d5601b404248041400080244061441100028901940d582c0031072000001c04900c0f0341e044c0c00c0880c2e02020316800406c680d510100c3c2031000f00715241850300b0103000d00d0030350150119015001c40043c4450f4001c0904c90342c0c41d45c0100e508502e03001c50000c28100b403100041d2060043c00380080000d25141100010010344003124003034048004204000c003a1900010404607842c8100d20b00040941ca40d0300c000e41c020400c1c48000300300b5141034003d240c02d482d0a24561410041c5040042000c00b00401d0f0180e004075441c54680d550b072160341000050b805c1150841d640c0f5034400907040c0000e40e015488905000c4d010030040f8004110310034800e0807104c407121400049103081008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 420237634 1250 420236384 420236389
    0xb060306160f0203190201020306090a021207030c050c07080705010f14040603050403090f090c03050f10180e160609061809091e06090c150e10020109050a060915050c0702 75
    0x255442d01515204070381c00c0280f10002c03048138803600118100940d5000062013043d0610500b40c592002c007464040d460310091001e44512070f8001440300b81015512102040c001c3c1c4190200d40441c10350400f1185442e482d03036001034442a00e41b0445000c50010b00d071a040141c00340b11003020a150017102a400c0c64500b21041e005403000804c01c608000402002003402600d041c040d03405405c2a000c0000e200800640180450790b0160149880740705081c20081d100e0a000c1225003034a40442c9011018845084403c01034009480c441c81207000b10201115041c2c015182c14041b52025502c064040341c0d83c00741075609004e464580c1000307501c0c0c49070030f001240703031500401a01c0c2e00c60160020240c01140341c02c60078460310241202c1a64440141006208142c0054006000340c05403041c40700920200241c40e250100c032803140101041d41a45024600079401400d045400100355521103285103411001060000811249241d8610740080e00440c241302ea540b1400701801410703c0c0c103869408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 420238884 1250 420237634 420237647
    0x613050f2d01090b0d0507080106090507111c09150302180108060a030b06151605070f0510080408130605070b090601030215130b130501090b280e090f040b06030616 72
    0x1440385c02c04800060900015020005080207121340800012554100081c840c1501c0001d88000100b201040e050030840700081231000140036038481011100c0c03003400701911880920b502c024403860880c00b400c0842d5030540c0040c22410010010b003044129002e0064030441410354146030401c01c103078014400180715810103600040000e1001c1c0100034010201e00c0d942d441128401541c1c04600c040d0030070443c2c02c00914015100240d1701d88056820100072a8103402c0c00019101080100800304041c0a0001d0490340007841c0d83e1184480103440d103001038466409041e044692202c00c2000410011000c21128162a402400b0305800d5030441e550b0020381d00b16614800c9220b0a0313850002d05d00300440c00810500b86c11004011100d81b80100160180300c1d1a80900d0f401d000820a0020240c1d8000341120410700c140f00400c40741070100c00480d03c03440224078144d001381e10075041c408002924811580304500c20310340080c0590380e6405050711101c007524104d906030741e2412001c403c0d03401741c1e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 420240134 1250 420238884 420238901
    0x6080403021006030c0e130822080f0604031215030623010608010503011d0a170403060c121d060402090a180804031a0705090402030613050f2d0109 65
    0x20446506103240b0340d51008458280d1300803564410803d20800940c3c2d450007070194070800200e84421071503402d80f02d0410038030910190280c402d81000030b6402c0d140355040c0c494003600001c011100300407160001696a05003e44040d0041103000e0b20142e800b400900551040d03480b5400103250a41c5543e40d080058044018000e48882c406800c1c40441410784003014003c080c1640d03400f801d9407410051508443d20b10490f032480303407416010301c0700d010000541c04264581c4a80503031081a4600644d54803030250741c200510b05400d010500e2019680320b20300180c000c0e9010410000e1101084a005a4480f5581051025002040003a0251034074600059000402c4c400210b20300d81c40c0d1180b07200b2031100305800c5607041c00200702401404500f03074020700c54003030010700900c15041843c0040c28600030015603610444e000400205141ca1f074800d0850501000c0500b40f0180c24081134005820b00c084401209941c451481040c440045030700b050880c2c000480b064402c1d900700060440508a140c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 420241384 1250 420240134 420240137
    0x20d050a0504180504120201090b0103111f02010c0f080103021c08090d060e010509010b090109050703021306172a0304050f060f0906010b190806030705060a0e011404080706080403 79
    0x81c040019140900040315241d4010048001113a03e00380c0303400700d640000e01c00010210380c900b9500d4000a0402d469860549400c10906018070b120f8000041040e10038400001c115030f0403000f2081c0003601504001c0c41c4e4031081d211402c611a1401c01250545000d1101a41c80304044102c05440401c40003c000c0740342c025041c83e40780c0700b080b031301140001e1203080d411503a060359038951000041080c072489030030490710f000901941c455100040c689050600429580c03581d02c001040645010360f04581c4504c520074842404180d5032500606144035031680d500da0107420b480040c00301d249801084442640400c5003070174030b17098050201180d41000740100e480e07101c2e0070840b140310304081240c1072107140010a10312403840d00810301c42c2800e0703040e44840201c0b1000d1001d008402c141c581d0b040d4600d0740615010b950b40d612440024909003a0764041d50b00071200284810503503a12003102c0c114060281c030390040541100803460001d10030381c42a024690818881845600e04c10003a658110303019 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 420242634 1250 420241384 420241387
    0x5010f09060f020f120d060f08060705030a09021f080a0c0912050a0512070c06090503060c0928150e100807090f0b0a030e0105060342010e06060406020d050a05 70
    0x71030b140036140c69582c00c6204800c80001c40c910702006124069800500391502407100e04070309c1d084940d903641c0005001e00b024424080005449050700e40d0046084540041940e600140303500d14003140071081c1840b0300c0001345a41e000910b941428040d00003c1c0a44e46d47d640720103854040351180e1a4110302d81101e80e0f01850300b800d00030600410407a14540c100c44500342d51a850b07468460000912548001d091041040007000161744c045a880d500580090050307a82d50400f0000811282d85040403200b44106641c0c850644012142620161080e0a60070508001b004500f6200300c0c4000c2c42c443c1e07005011120030040d1922071243c03181c104803541001c101a135180e0000503c00356085c0c00420f2450808940d8425031355060046004000204000708400c0c10b0207008a6140c0c0c2c80c07404440d181003c40b803280f01c00c11407003618160104502c1c98034840c0b121103c45074400408800c2c41007003a1030040d50b020910524040e0101d07401c4601c1900200b000d010307440340c2518540c00c2200000e00707000c030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 420243884 1250 420242634 420242653
    0x10e03030115030b12061b090619020708070b0f2b0219080f0609040519060207021504050a0317091c050610080a0b090a050f1605010f09060f02 63
    0x408002460290054040e0380842d414944401011102846000c0f8404d20003c10f5a4010070404600950440c1030b11070b2060280401d200710b00000d07c2403070200c9822080c000303540500c085400382083c914145950a44007081c3c0c0c0c0d1622a50345644a0040d10a440001c01c101907198100718000c020a01002032000308a601c0c404a40b03101209540c1c011840940015119080c240002100203d0600301d040401c204d0501001d050541c4c030700100810b008205120200d01400380800c01c1c81100a6000c074610100c03545850480065046010124043c02d0200000b02603085460181d9060711400f0b00400701261854413428144a005500344650510401000d4010b8940c188012242a044501d62402541504c0c250346000c5c4010080056241c00481c244501030010440880b125000074a40b00d040c0c50300e000903030030306000c20401010b6110324440400c103004c0110b8404e050032842d025030007000f99664010342c0c02c020382042443c00a484900b0505c20a801030140682d008060701c101d608804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 420245134 1250 420243884 420243911
    0x22020d0b010e01090501080d0504060309020a030228080a1110110d0f0e0a030c06030209031501030c0501080a020c0622050f010f0606140a030c17040803041203021e0c01 74
    0x1842030b00002c1c164240c0d00c005000650190250a0040c140385000309400844030701c0043c0180154040d4504168503140c11600b90364030312601070003035a002011001480060071440c09400c02108000c846041c981000054000c004514444696080303070303040d50b08944031001c00c1112500030380d42c0c1007030003002d11108040400402c00c1841060f62600d410b24088903103d800b030030441480f024a0b204100d40ca0041c8001503c903203c1504072800c5003001740e12a04a180001e0610404804145403540000700000c00e1000741c42c1c0c03500480d1001c2e200c5001d40c1e00c2f03400351401a40316250740c20a480e400900030031040750034a040140d40c86660403a0b000500030641e14541010402891a50b15039165030300c0e00f024180c50300c601e1004203a1070074640302216201103800240d00074609507005142d0b80b1048615014010b4841c0d240101e8407020340c3c80c4601c0c040c50710601030380056400b600d08a220800c100081e0b402403003100e41c2d9950142c01d00c0650401e2038800340e066440f1450400c1903540300c042ca0703007001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 420246384 1250 420245134 420245153
    0x905100b0a0314010509160503222105070b16090b130509090c010c110d0210050703080c0319050c0d09030e0f0d0b01061d060c0307061422020d 63
    0x401c101d98012a0b841e10b06100301500764010b8009a10544003042844804243d0b00c112000414140c2041600c070768809031b40e9200089501c04d50203604c0e140c600d412080011800c840800e040703049a100d0900e5110300b0040b5041c1c0560303a0700401d84d0400300c003c42c90050b0036402c510540b034018901000c0c190b4440c40b140c0e10680110f40b01c0d00c1c40d00b0710110244410302e0a141001d84c0311040100a2000c01038101c0000c3c075801c1c0d46107000d0940100b00c8515441a00c0d110407440c001c41c0c02a003184079407058204000c02507441030a003540010b16502c0410b50598400040302d0148480e5103040c40e048a0300d407003210080c0809001e208000c4410040b8074400700e5540110b0307504c14025210b51000d011244140b120142d0341d8092280300782e646204032000a03c420121906440701d902e000d402c02100b0185080c4800000440c0701d500c90b5010130304640f0104000014103080c0d116000901032074603100d0003018554025075107c4640395001941d418071450f4059034140315030001301403021100d0917890b0b00740c09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 420247634 1250 420246384 420246397
    0x60504060902090f0103200d0b120f1213060e012a0507050319140712060b010f110c060703090e040b16020c012001021e0c0c0102160905100b 62
    0x129a0085080c0c1260300c4d2280314a1a030300003c0c00d00b031005412410036654040401e241d02c0c40c080002060702c04040a9a44c488841e0b0000908020b01c921880950103075241c000c40c00100c1c04e4400c0800144800120302c01780e03000382240e60411140142000c005551210000000604004000010b20301c54844014007005c0c1b40184000030300a80c04a08003c0e003406000d0f00802e02aa0040a80b1300c41208022902d41500c2e4002c404d4488502100303d4207814107055038840c840b499403980d041c1091184543c0100380e201800d0702c490b401e6114429096036540380c901d10303404a40e040a4070380400380c104240100b4419100b0b150045c00c040c4c231001450400c2c9030a07a000c0d03880d80c1d02c210030084031280300c40541108182d00c1c0010041d0040200c0001d207000c000c0341401c948001d40f04e039440d44214003501500c4c81030004829000d40b508080384a510250030044808465100303400255801d540080381c0c0b026024500040781c82900d08184c211000340202811501c100e0401d0000090742d100c0030304c0600350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 420248884 1250 420247634 420247649
    0x4020a060c030801123002121c0b1309082512030b0102120d020a0e12030a0309080c0307050c03160b090d050312010b04060305060a0e0f0705090d0b042310090606050406 74
    0x591624064000d2425515908010f00035002700706480088180c4c01046d43d00000780c0300d000c15500b00500205143c0e064000310030b41c8040c00c00712900208901d50018100c070611480c1d0080b001c840c5000d9221883c1c000d00c101030304c40a040400c9880c0c540c865000740d042840103004507440c0c42c008010340e4255038024281c0c2415542e01044046120350f20503588a40404115a4041c50400c0390018a4407407250792100800c1c9569080003004110103001602c446109000c152900e80081d03040c40d0340c603155600c0c015442401008034103180c44501500b07034001e8078450100d89052440003070078802d51104010098805c0d20041c0180901d4844000a140c060445500c0c92a1103a1070200060151040908074500c03a480c01c1e68107200101e0782c924060350101003038401110b00d4403100015100d5103c0e000005400842110140061142000d6440e009522944c00c4900010101182d811049081d05500007145c001c1e11000a2003021500b00729051800342500040310360380d41c1c00280c11600544d00c0000f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 420250134 1250 420248884 420248963
    0x1503081201050303270102010f0e0607020706181406042c1302060a031503050f030912010203060319031404090509300d0e030a020604020a060c03080112 67
    0x1059202032222401804181c0041d0b044c0061941008000041203012008074000c07a41803a515a200b504242241c40e05401e0801c8880e201d40076298541b00c00b1100140940703e210f40008680e4820781c207500a11701c40141200d1414200800704081448440e0300703d0344010284000301702641c0038404001141d4103040e0012818105104c040c19410008100d0443c4024589a82025842c0d000031515044c10703e24001400c0503804400780c8100342c80341c1014016201d81c00d8060030412000004214004040350780001140810300080d0a17032004071211a00b5410031071625210712000380e058181706200e41000c01c1d00c84801547d0040507040740d8842e00d203da0301d89060100511040c054840c40d520441d0054021880c007020020f007170b51080c01c201c120301350b0000b00c00304822225030140c4502050344058a50350940321800030b640c0d44090320140c0c403c1910080c001402400b40d00466207244e03040e242c04406030b19114003203440c160807130410341d5030740188082140e40380b4006003200b0b1075008140018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 420251384 1250 420250134 420250147
    0xc1c081b06060a061b080309010905010c0809100905120f0c0a05060f070f020607140702030f010507080f01030b0103060903030204080f07090c030c020613030e090705030415090b0601030b04150308 86
    0x846854240d6109200348010100a09018281350552070620b40d04600d5451f030703c0d120320601074014440d100010b0525480c040380c58407100d41c40ba011500490040045a902034600c80d0f81c90121603c036440104140c0c003d0f04090910305d00d00014043d80d82c04207404506028860032064100201d90754101c039a5000b07041085028080d194049800001c05d15005044042075a4065901e480c05491042841600703150745c00070001500031280b42d980e01030309030b5420f030b503040310307981d010304402e035900004120010b002560592070414418101e81d04954a10b510343d03c1d5445a100401f8582e400390100f540820021076111700c100840c40f2507200200040c091b4501c1c2c00403090481e50340b404030310f0030141490380c051500b650014142f500000310a2507400350039014034040e1060100d4100e41d03500408148200300c030154000c009144902c0c0100104000c0c40b80d016000e404851941178000d1018611802040e000d5200c0e50001507070142c0903000259400c50448501e1003186103038000c075000b401c001440e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 420252634 1250 420251384 420251389
    0x302070b01032d110d080c0d0e030607050a0804030e0604090603120e0301150522062402060c0715060e0c0705160b07020d03050d020d020d0b030c1c081b0606 69
    0x403040141c00366000d03803001000c0d644d5024540500c0003100351181d01d15a08020601c41c180301141c07a40c012001c100c85055110100146c10608400e658a100e07000d0180019003e17402402283d1b400c1259544200141d916650162800031550011130341080090201103201c03400c920400d400fa50040c07801c640d154011020040000148820b110700076410701e84600082c3c0940a500c6069410032203c030788101e0076200e00240c4160040401d0401d050811000143d1144200c035941d1520002c109034880c803031115031050760741e02d10a17600d0a40d8914204286408101c42c01080e10302900402e001140e913940c4d503004d5803001f0209580901880e41c0000742801001400c01c184d00e807a0610541c0c0c50107c2d031400c10840000d024030b81019010b40d038a0200c1c003040501c41c200700c0718460403280c411516140b0000d0076100a4120580d0722920358500290b42000e0300d0000380e00d03442e50070000c0c802c030030001400100d100c110b104694206c94100d400d00c000c008805441c440c039124002c246d0020209442c00300304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 420253884 1250 420252634 420252683
    0x5090301150e0a09050309060316091d07032703020303060109050a0302060406050f0c0a05160605031006050d06050409060b0a1a0703050a200f07081209100302070b0103 74
    0x625401a20750240e00304240c000700304005a00024800380000c4001481c20200d045100390940154040350000400500310100d96400140c13100b542e480c0411142c890f031005110115044e0090f8110022070001060300384260010f05071b05940300302d032a4000c3d180c1c0c0c8003800398061544049000d40c2002c0200123a550740300160100600e01101d012040d01d2031900402d2a92040f030080100b005800280c0d182152010782c00c0b1020034281008a40108002d801d1803034440411404400820707214100000d1040d10803c113481c080c54401405001c40c9107030520644142e40320b0610036560079103821000411f42c0d1644280c00a089c01007a0218030410303601c0402605074000d0b00054680d183c5c1450002c1d92011807030039102502c0c3d0500b40907503a403002c601c0681d51003600041d01c0092401031500301e0141480490205118000300d400c960f2401d4540301d0b0b003601c406055a1104606105100000b0b103840e15003d100050701d03035800c00500d81400380c2caa07441154001d030400e0741c50b25120003002114900946 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 420255134 1250 420253884 420253901
    0x1303110f010f0c21050612061005040b09041109072708010b030d050703031a0a08010b0307050a150c11040504050304030b01050901030309030209060a15020a030801150504031e0501090305090301 85
    0xa4490311040f13005040480300d01a0041c103990940d61513001500c0d035116807015400604c215002c0710b12a2821002184080c1c0860051501840c140002c400c1203007400b0100c14015035101c034000c4003503280b0704180802004d0041000040002d03849807a580c0401511009101c0e02450f015550703d1810842e5071429145001d6805001c1d074061240d00c19490303442000c0d500080d80c1413501245021103054101d41c81101b150306540d111a9101e40000c040c81c0540c4540f0781c1560903401e6943c4c081d80c0b2820030810702a2407107001c00c14030401401000036031080b145000401e100d00641c50b00e10740300c00d010030200c583c1110102c405038400207080c000c0c13141c03e44045004000c02c5138034400315811035400421109040c071000f8024074034480070a5482e99138506640141006a0440010030308004001359510014141940498039043c0082011000d44941e0131410561f520780318905880c41c0e9551301d42d50070040301c40007568411868100011400c0c099030b800240070fa650349031144021001c150842d070451 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 420256384 1250 420255134 420255137
    0x60c0c0b0c03090705090c12010603021b0c061c0906060303020d1d0d0f06023f010e0705070507180204031a19051b0310080c06070b1303110f010f0c 65
    0x2c0c4104078810710009100c0055410585401c0e01079201c0d00d004c2c1015000b500780700301e54505280008100d140d8560b014158510155258401c0c0b9000355643d01d07115100455243d030401c2d4200100a0544408829050b000000d07940000e01021941c407400101e90a80e081140183c101c05403805146501c03600c10303240550b1280d200420b084444000a03c00c404e40300c0020010031115403180c09118459064590941c00c031a18211204514080348c005420b849120803000b100c1c0004020380307844001034007070681c0c128100c50292a12603880548058101d0b000464883c0325050740494a0542e002c803142040d20075407405604c2c0d90a600d0000f40c18a200d0142540c0e031340824040041da000290701e1070145004540e00040c4035140e0501d020429245492a00b402400010030310150101c0940250100c84e8048252030040e180c487c100071092149110240078038cc2048049049600040444028680710b03090441480c20401810350401800c0350b001c80c8646d55075900c8001090860050100a200302e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 420257634 1250 420256384 420256387
    0x21801030e15040f2f011202040e04060e0c12010207060c030b06030a050711030c151f03080c030706051f0b0a02120f04031a070f080c040509090a060c0c0b0c 69
    0x2040c0c04101120040001e0100000301020405200305c2140b030210100b52024106010302000d131060034000341c07001d006070010f01415480c0c620101c140c82900c00ba0741c810314106840303448a07120301d80540fa0b02c050030000c60040d10030f04a030550382d1001044c14075071000000b40c1c4450050030708000f25a0024184010f260030160207804668a450440b40d012031041400507a03511099400c94810034442d240c07014078400054540d0003058000b8401c41035403810380160160707994040c08413034002e0711600ea40003040c408010520000b000310003d031003508120000c80e414601d02d5165170080c1c0340152001c00035100e545134404078071039101c40e005002d405000f4100e1302d4400007420003540c401c5983e071001590a00030842c180d4000791a812200155080040d641021200d60503141c0040000d0301c800d404140340080300c500740782c001c8928901c1110030140341400d21307151809019114100070035842441c010180904001501407088112900346540c1e80380644400d850140fa4001c0043c00c8031400003030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 420258884 1250 420257634 420257653
    0x9070e0a0501030f03080411040c0203070c08070f061d13090210030c05090f030a0203060c03090d0e1806181006030e0f100903021e0c0108251809021801030e 69
    0x4c82c9126566030760514018825650b142001581064000d00256129040111105040d640000a4003c1901850805040b55034a001180e900d140a104001c418142d680c801c00040d4002e42e1080d00001c80450100103010030100000c2c440854134508002150b42c4000d201d003582044000c1105541c3c25003010414010303240380c00f52050040c0152280f045031607241700b9015480034400c1401007540501107464a08241008044070f030421642c0706032621650094800c8148628920724040304091f02802410ba1824562000c08030001c21941e04800c10755184d2004c115030b002c1c02846882d60748080205103050031401070558117860780b04412079000c03001b50041c44201044842c91a4580d810004002c02c191070140d00f8580c45461035003405d0380d0245506108400410501040d010990326401c059a814000e500c5401c0048001034450420110307040256014844000ca88101140d821b00002d59619015082c1e038000c04400700881040030f1f103265a560940500c4407081003403c041d0600c0314 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 420260134 1250 420258884 420258893
    0x6020a05060f0a0905070b091c0f150605060703021c020a021f020705101d09070804031202090406030606030209010603062301030f0c0305040c0603110a080c0d020309070e0a050103 79
    0x580141801e5094030180c40801c43d42011035020b907601c554400141d502041e515815071741240c0107100d107140140d2880d6041c000800700d10b0380004030303a42d000715405058400c40d185c51002281101c201120075644d01800300b110390307400011303016007803207075005160400c1d001658200c20500c00b05070405542c03008101c00300603954140c46189403c441d032166a81801170b0310040b4901812584100d422030080d00d005d0000742d82c4000303250101c030070214582c0d4540c003e80c400c0c401013440464011000424070f4011400292184240150748004104051f0806000c400090304982c00c0364000c8912903900c1c14208110309113110359900425860800300440c9140030441d9061025581c801481c5600c1458408000c1c0c0c000ea000c1c0b0030382e00d0f1120040001070a11b0802800402c41650161619000444005484c500c6030186900701c1d864450200c9c00c121903020305442c83c01014044802903001488403012688161001d03511940c000e8009201d2203240840e200342041000d0211822641050010310104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 420261384 1250 420260134 420260143
    0x201021216020103020904062c060102120304080a11060106050a02010e0604050307021210051305061b09011b060c031b0e060405061b010f020c0c010e09041b080601080d030606020a05 80
    0x19502804c0141c0c6e10086203000030001c0105802852448100061080301c07c82c148203520f2404c81c00843c044c046031a80350041e40e4600391100701005040d400c00000d0001078084000c1c0074202001d08040014080c06079416003003507401d801007400a58003050001c40594240194100d480e4540007130003141c18140c54164692041140c0a405100310604c0d07640e03080d0003007000841138141c5a40c00c10440c18040c107103407a40031040c94255150700c01c51002c82c4c200f10040c040081e000c90b140304003d1620b10031400650303500c0358180c4c03804003109100c448600800c0e10750281c04816006507400054038425100304880b0410500d14100c100485002c80f14a180c5600301101c0c00d564048840d2511409003074801401002c50b81d01c60715555081c80001d2a015456401500604140c001950310724080c1200464a501138134007001d5106140c039010a000c6070070001c400e0351000c05125440115903c542c045032422200303911a40300c540c414441019215814422030015001b0380c4094100b05081c1e44075640e46 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 420262634 1250 420261384 420261427
    0xf10170a02041104080109030203041703090906040b0d05030d0b041407050304031211190909020708040e1305031209072c061c0602071a01030b152b02010212 69
    0x455955003c540743c540c0036000c3e5030060180d0b0000b0301019820b031900a440380c000d8855000a42d2501c40203444d407c4000c400d8440b003140181502c0da25540f00010007001d8004030a0003a00040f03841a140045001072000b400c448500c5072000c142e009010003440b04171510781901054225100c07080c80121a4040c0440e60066050704c2e084d40031141018182000f461568070b000803444000459041d80c843d02040c2c200902c5658441d910542d0b61041070b00103038032032010020b02d61141007100303020903030186183c117401489540d5a1031381c1013080d907500d5203141d000c20900100328510400700101e1120410034080a86050704280380d4408c004007022107440100c1c51000f020900400001c1d1154651010052700d6860f20b02d526440c800090416000962001c102078940035903945451045442d919a0b050403a5030010303203e88590780f19406e061020380b02042d07881d80f000d808194103400104c2c0034694502c0e1400c1c0035400800c0c1755030b071002900c0e018148136440b03500282480b90b001700f6000c0320200c5c8030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 420263884 1250 420262634 420262639
    0x3021009050111071a01170705010c0609020a12150903350705041e0e06130207082704090203120d02070c08071706010305071a0c060f10170a02 63
    0x302109589001c50241ca0f146031420002c410115140c0700784000c003c0845000c004e15000029142d8840035a01c070910303281c0d009441140d00c04013040016502c02c0040030002401014001803082903540000d01e5110342d40d1011110030910300c1c105007880703004411561160440b020400281903e0f0341c0150140012965080c4602c80a0600301c2c0e92034090010a900d030727220243c3c405c40902d0001005400d0360401d005000d009180d110742c440900c1e104200c2102601c6d01d0804036001a07072002c04020340b02c600340000d04403241c0c0034000348002500840c0904603440b9003102c110000080400c5145071218000c600e0f5101d0390900c0c0064015840100740da5510502e0001031319900c0c002d40d0500f9000e889400c0d0003c00036407000074002003160700496008180d6640006d517441e80c00c00440e510303a840b482030002070810780062904002e004090340b980400c26800440700d50034543c00348101810724404464508015800b40c080100840b0000c55840142940381d808680c580302e14011b80c0d54804140030000e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 420265134 1250 420263884 420263891
    0x9060e1f030902031e0f030313060c352a090303120103050a0b09070b0a0305151914030a0305030f0a02070512071a240f13050f060a03030210 62
    0x350880c8690811801c898018003140e804104180212640700c5052066100714020301c021041c1c140c0f00842124000c0c61543c52140e0140c9040c0c0b0340308010400e4429070014050700b1800540c8099984200b100c0d00c8040b5a10311000c030300b0740040395082040c010710804c11242031a0400b012120004130010758291504a22a111350803a4003291440c8980d0032180d010210407000002000303000907080401510500c105130240d298900b00f10b030351b1401d078052030070170304014003200300e496109a0115a2042680a1911000310f02c80701040d03004091003080008070781540d109100072000700f0800084464250300400c0003c40ca82c40080040c0005001e4041d000c1e032540109100e149503405442d030715504101601d6802600e03240d0342103e030384098402c41c2c403502130496400d900f001c0146094071039482054051181d180d41180400c03200c0625410562226000d0410a9542c58030082c0c1a1007107151900040c076414610f050906e001c80c010240340c842c00d0800c1092001950218150180c54900031010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 420266384 1250 420265134 420265189
    0x61e060518130f051b030903030a050606040308071505091917130f0e06040204050108040308040501061509050a080102132306160219030c150e0402041509060e 70
    0x360b0800030140480e440c00e03003419a00c40401c540c0b644940d0003401101c41c6005040101002912103000c1101c0800b882d820500000f450030440d40c00040d4042001001140707010380341c0d41c0341a00d5811040060b203009031441400b0074500c6140c851260030040f1b0344000d000c5038020549250102680380c1d0300600307042c40c81d03c00f6040944614184c03600c00c07081800b0240c100382c40e000c0301203031584c20344942c823841d95502c1c011400c0c6003418421a0250342041c3d5903c0d100b5a1251003d0720289006881207c444d13507104400681c6003100b110f4007502d5003d903558074564500d008208501c8403007035040150f441c0d00c10410018111402c10310401110304142500c40321041009c1d000507000d440c91107113074010100040210055402d55008181144215580c81d0b006135080460707a03000350705020080a50000c102c1c03e03c0641c45882c1e1081500100d841c2002e2004a11008142030fa000341d80070303107103c45102068079401038224580700044c0c0450302c0c041c54450f4113440000c48086078042e8000ea0030302001500c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 420267634 1250 420266384 420266389
    0x2120f0a030605060a0c0c090e030909090a060f1b0201021201050904020307030501050f180d140904020409150503210f1b011d010501121a0901091401061e060518 71
    0x202c401031500070f040e00e480704900c00000d4840e010002c1e0440340d030500340e18081074941151191441c088910300045040100c100184000160040c2503101d80384500325000c800602d0074041c170807440c0103600d0082000c0d50318890108a006000e0910015a401400504a544410b24429044603411560745400c5d480310b00100c1d04042e003d400103080c0d07500300000c2041c0c01c2c0c40550058010451003400500d2040000344990701c50000328103180000d01300404804001c04120702078035075220700402c0146403030703a03a802070402c0740c440c02d2441c03a40390048041040701c0c0c40c0078041801000c07204c011840d22019000340e030140c07501c07031414001d803240b40c082070709560030100791884056180340760020000c0103070070040f403021100030001721a0305d9801e103400858540341140c00d03138200c1c691001984039141c21032606a10340e100b000300040e105640e07500620010032610703061030704400182c4d400040c2c41c070300b080118444021000c052828404007013404002c1637503c0b00c00c58103589c07806559072900d407418100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 420268884 1250 420267634 420267641
    0x3010c0c020315070905030f0f0606310b03010606030509010b0a03030f11070f0b0306030f010632220b0d020a0320090c18151e0c03030a02041502120f0a03 68
    0x10587e0140301c0e615200e10b901100141c448000700340391085640c2c40e900c1404000c4c018006002c418146480944c4070300000e203c44c40c0301800e008110754007048110000003c6421100305500a02c0000d488005014100c0c10138411481d603000c040c1c03100301e01e20f821901c010b0310310907514801e4030070001c100c0c500e80c09035002406154060b09200007040001c642e80d485869843e0819a803280c82800350440800146505204110485050b950340c904200051142c035542540440450403c3d9403110381d5540d1259502c69000880d00020030030080ca600080e4524002c03106282a028060000340c0031100161703941c0c410392401c80340c0c00b0307885003c1010444582044503510002d00790308071000d0302c1403051000401003e0074802d1a1540d040b6100c031020b6041062804003054003030802d580070090080a110030b40d00c1440e0011700540d1035440c2c4401182140e1039603204940030702c42250b0214040c025603000381011413054400384020008014695082c5116101d60304010820610001b09a0080d5001c0c1c0c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 420270134 1250 420268884 420268889
    0x3040f0b01120b07020d1d01020307050d0203250f12020c1503191526030307090f08150a0b1203041205010605030a050a08070614130203010c0c0203150709 68
    0xaa0090030396036400c59110728402c1c00c0421588070f0480300010b9000c0340700190310500004c06070b890480400034200384600703a0500d804150f0443c0420060800864070401075621043c00960003166a092011a00006a6840d000c100c0318540d107140c1e014041402e0207142030b401c641181d0b4180e007901403803100b42c2c60412058000c0340c024003260301c03125284403440c02651145582041c4000c50341c8442a685040702d0705a0b0020004c807003c89170078000403c3c141d030f07814441c101c4000c820384041c60050700d061440d00110380e0314001600004090205030b4550104100401505004101380c3c84008058111242c0080005554070b50350342003001107965000d010348508100748140c2c0d036600c0c2c8030009141809201102910250b00300900000c040c00d0003e1881c200b990000081c081d030070019540d003540740c1d1084034141e81050f180d85080e41d000c0ca158440c030380940740341034084a1000683c4145402e49080803504014022410789400158401155010300602c800190002a54404409030317065801c0b034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 420271384 1250 420270134 420270143
    0x11209050705030f0118080a030603080301080705130e0a1b1206050603010e0f07180605100309060e06010b090906060c01020703050414030705211e070f05060c0a02010503040f 77
    0x209114092100100d800d40c25036000b90251403070080b40a0340742d8241d41d110601c0345011002e40320300348049820800075108118003441c000c601c1560302c1c0c90b00843d580003a000320106800140d001c001501c7c007941c400c10110390f40c0d6014030072204200700c0551543e224000c00352a0500180b081d000030400e504411000c2d180804101071030712450704160740105422146107009600c3c0114050142c2800112060715558a60090550354201032401240000d000000202152100404122a9240340c03e80d080c000050b6800641b049190030302200f0349004122800c01c07034011800600011208100316040400c080d01e010007039454041c0410f90501c194071091502c2c0d4408240c003010180d0100003081120211359072035480c5002c820030140c980c580c070700c10540d101840042000034191907045240400344007505580d0b00c46215036070b04a106007086400303025500140f10a11100c2c4120421401920068403a6402c2c02c08580d00e03180c1d5a01e0141c000b138180030010000604011713007100c0084059920 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 420272634 1250 420271384 420271391
    0x1909180b010b09090604020310030f05030c0a0b1e09070b0f0f03010f0317040b12071b1203150803041a070f05030406030b010302070c050418060510050301150e06010503060112 77
    0x650406200b20780000c2d94482c421803041020034a50300e0603000380ca0050316291144508248ac6682c0c2d2a903030300c43c1f51070440391800b090180204015052022192043c010381c07041285103408909180310181d400e0350b4480c41c410a405001607100700040482c15100201030341d036682c4c0e50f20071326040680508900c52180d42e07030000010440031114100882102e10500403010082d5641407011024000c9000345440c0950038860200d021103114076040d040951800c00000c00700384460440182444d41c0c1040e079840c0301020b800d00550707a042c071400100ea00c0e680c01c883e06a80c2030800c500e13240c1c4544e108a1049152040141c0880340c6010210b035512a40640d2124241036940f902d82d49030742080c480ca40201c0e240007401400c5500038000c54442c82d9014001d984410300308005c1000512550380c085100c00070308844640003c6085c4034807030050340c0c101542d01c40c040c900410103003922903000c0c4400c10622080700070028501a0241160411001d0034043d40302e03034a500040300c00d0000142030403400c40c107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 420273884 1250 420272634 420272639
    0x105060a12020c0d09080303070c080310050d1a1008071211100908060105100813050c040212090d020a080406120b060412260f07050312010806070801051909180b01 72
    0x800044907544000161142c5d1001750b9200c0d0a16103034042214060f01143c102d05c8030700001103196005691044d100004207202e1034450300840c0504000050032542016403112820342540851a09640460b40601024041d420207000c030340c50341c00f035200314440407440c400d810003000120950720304542c0c0d001e051a5a901d04020004098103000c0c0f0400351a40540c00c004039441c00e154007058823402c0561a400c100740c5414010070060b206031141581c5c0d5000c1c101d100182c940c0c5600041554014000355400c039401c14a400e10b0816070f0549401c0195030242c6640700015000f0020b840845141d4203003c040869480c0510001c1c1030042d41195010000141c0880c5200d54800013050380ca000f001d840c01c0b004049482d0392b100d2285019844100c010078440c10040c0f10100c0010714441c0e125209803420080c4905d1428001e003001e0308050303187d412140811140e1940403556900400080341d801c0108019186041941da045000750204a600c0d04061213540c43c60300245140d1590000020742c040d03a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 420275134 1250 420273884 420273907
    0x13030e0a0509091c09121e050303071d0405010614572806020301080105010812090105030f04140607050a020d03060b1204020a030506040b150402030f0105060a1202 72
    0x14548000e200070b03608415030004519220726400c00030f1b82e4002d0404d005044070740c0c840e980314020700d00540c401c041a40c02440001102480554058225a200d070000c50f01c0c3c0b540c60005060b100303181c203070060b45803800401c5010303407000f443c071190100761143c0c0741d981c80c6040c480c40300d00303840300c03041152090115030080c0300f45401c000038007443c8182c43c5028074500300c1c1c045100c510b941c640c2d4882e050341e03c2848aa0b4107a20f84245502900c4101e02001072010f0495607060301f641c009030301500050359100010040700005101410b241024488150710380040c80700042c04c6808050802003c150041001508115030401c48022890100c0200d40c524038103e00024825401601d5440c0140034030f50038855840d00034001c8005a500c0803a502d0f0600c008070019001040c40100705903444060040d0000101c0c3d0f06106050181c2e004251508240c40c00b90b00b4400d41e4015a095180514810003c00c0702c50005200d090b81943e2044480e942c0d05c041e0300c40119104040a450384c0000d52002900750440ad = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 420276384 1250 420275134 420275143
    0x3070f0f0b06030d090b03180a0c140604030305041203120f1a031603080d1112150d0206030a090503270901080f0d14070c0603022113030e0a050909 65
    0x207449030700c100100d5942d00050548841e102a80b135070100b100c20005204000080b0059544200c0d60b4011080c1481c0400d00140340000b11101614810814402030144500d05020505940019100d4070318280c41d642d001041ca2080781300d46030000d0699030b851820540b02e101003070f00e40c811942c0140a04940701c400c40008203441312a4040d482c00844440115040204130507030300c14402c1031800b0301035155403140c80d0307a50f00100c483c038083c969410f600100b24540d03c0107840381c0151100420401d05d007140c0d40148242034241458800c00c5080076070b4005135291001c0f03c0c0d0010b100d9a0216080100785001d44c5180a0300621900c20341c00d41001e43c1170103104e00312031800440d040b070b026176459990742c00c00b0340c5441c4e02d40e481070b80a40049801c0e2600b1402112800ca02502034600c00e1310f0000940c0710b20781001c54076001400026000900303d950159400340701d4806440b10040d008450800200c1071101c4041c8550007010701111510a25442d039850702503000404010784100c02c146400d0701669201c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 420277634 1250 420276384 420276413
    0x369011512020403061d07060f0c0c032901090216081c0218010e040209011e050405033c0601150306080a05060f0c0c06130813090b010201060603022a03070f 69
    0x81c1c6581b019080701000c2c0000c4a80c2101c3d040d48829105104000b41121000341119003982ca95060150010014507074548070a90010500e404141c2858401a15031103501c0607889010300f1401032065021051982e00980c10103540300b0146a560045050300300b40c2c0038013180702000d00e5440416080740000805a1001e8086000d0342c4020508070038008000480c000d484d0070500007010358004912194605143c24101940c5080590400740d803400001d02d0004502d2904812414a141c00c84101801c604c0b442181624101514030490341d02250b1641d510051245080e0588220081894940245d000d000070b0700400b13041d0742400006003015a662401039904101c118041000140b8280b1103806846025000b400a00044e4580079410f00502d0071f100c000740c0d40340f08100150b24a822856004000411500d04007085104200c000603084841e95070001090600402c454010350040342c1001101c8210901d56580d10341a81100629501816100070805800105088280051500204075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 420278884 1250 420277634 420277661
    0x5180106090c0f02030301030f020906311a01120203061207031101091d060d0201030b1804050c1009090c0201020c0303010803030f0a0c0203036901151202040306 71
    0xf20964241c08994a202c2440060000c42503100c0760401440c0250b034083e00940f009220741440380d1400a85082844010113110710070321807628446111801d1f004104e5009428841d02c5030008a58002810081d1003440300c1c1c0e455940000014115075442c08044405002903084420b25600d91070103910701c100000d100340c00303c1e40b09000090890440485445140042207090640e501c034170b020b02c4060141890100d040c96110075a0a095495046813400d040c0b01d120f006098174102410018100924030302c41c00d00408242e080e00a046030800c24603003c0f03440201d00001c0121500c0001c074024000c07021904080d0000000000f41020004051070250248051030090b646030f081004089880e64255a400350f082400080e28034040781003080c48680b992494120555200041c0250b5000701c510308050030381401d03103072a8041c03004103440071507099600d42080c0c48607620a811710641c5414800c04042d905041c00000100b4820b20280c0010381510b0812364a55849150a20182541c81520070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 420280134 1250 420278884 420278897
    0x20a12080705100b130c0201090b130201030c021c14040b0a0908010605041806050a0e01020a2604030816030f0218030f1204050f03031b150106020604050c0405180106090c 75
    0x203d2419162251009204000b8180d842c51541008010045c00d600304041007075550f644084400701d280801400e20418085110520001c9188000360444100d40071150842d0b001c400281400d4000e10192141044e040c01c0075010b0070002c01c1e900c203881c400c64001000c000c0002c0340060380d072604400110140d6416200901155071a8400d2004131141406401d991109403001e040100d902d0b54016030301700030410400b060100201811609a03800404000005164101c5008140303041c06007814110759000d0f80350319182002d4500502081028180384062128007000549923030103540700c9141e82e100c1070310075515a0580c40301000741c071507094485c81c0a40030f01151402c103002c0120340e2806020b10110300c542403504000503c00c00e8a0280406500341c40100510301404591304040303520040072400030603444000100003503502606910507402d40d0b0240041c0070020f040843c10b00c0c1d810f00199400a1035986581803602da0400350203c0f007225501c0c104000c41e60380e8031500300e260baa0010352180c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 420281384 1250 420280134 420280153
    0x609011e1706040b13020d170c0a110325060f050c160f0608090d0f031d100b1f03021315080406060b280c12050c060705030103050a0f020a12080705 65
    0x481d00202405c0025407000d112055000000c281c0300a070201c038442e541886083c00b01c1c0100c81c031302d091001c032025948c0d041040d18034901841c040249a03175041c10444500c4000703a4114901c641150710340500e005020b8140b09103e00d0070b22840a4480c840b820700110b41041404056401070903095004040340020a01008503245014603e0180a820b1030b0005052541a040c030880d408294030102001300768894804106801e04d6100b900c1c1c2c2070090344040c01180c031050002c00215032060700e42c1c03406204d0b5030f11040020040075586a541e00c209040150351040c03500c034400b04603802500809880e444c11499004070540c06181d8511441c80780004006a0351256070702c1700c0d540546c4055000d9025140b010311551440c0f0f14448240a0b00c7d4182110700c02503030350f41c40541d0314160711b0520009001185541000320200141c640200c2142007251031541180c8889445190008000e0441c0160380403542c110b40b07d030050407006040301200321840007110316100d0900d6201c0803040c0c2d9517100e04030b0304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 420282634 1250 420281384 420281401
    0x70608070e091801060305030301080f1504080706060b0706050f150a0302010e21030310050a030807080c0a02030d3b010c0501020d050720060609011e1706040b 70
    0x14a000c0d001a07100d07014056440341c104030b00c00703100402c0b1414403121181c20200c120300034080c0c403003d54492009191650306113034a5501d85000c581081600d540300d142a100604840c560f032940141d00700c02c48580d200401d0410b00d0240809a100c85007800d00021340300e09200310f9a00082c0100d1081c0006400f03074840b0340e0300560009501d905140d0000102400b0401503000c1e40d020f804000010f00110010440c46501146a04014a1655594200004004032085000c03041790280208a4002c4845825901c41c01c43c1400740c0000104224000200c8140668003001a00e004c20b03801000c513440c03a014910010100201202c00348442c88c4407241e079812102d14200529030b01c1d0181c101c0c9a40303c1140500440d184411010180da40d5513003084506608603642c01142d00c0f510135502c405402d0040c1c034800b43e6480f0780c080784002154004905001840c0d5406009504440461416090b00d18410013112203c40c1c2d1607110078440300319070031a180c0d04480031039500d12803409000076440343c0d900c0400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 420283884 1250 420282634 420282647
    0x160309030218010f06030c111006031505010803040b07030215010f06031d0a170d06031a010905090c010e03030c0a0609020a06020a1205160503030a1e0207020a0302040b0616080301080706 82
    0x9070782200c0e04c0c80201485441c1c42540725681c1c2c0d078034520b8024299030903203204e0340c141594100c208185940b24401803081c0030064070941c103000c150f501d04012540c9030041c0b5685074015400703855150000000c41d1014144208040e200300414050b1412041d42c1d03c40c041d4050807441e00c2a40302281c20720001c020b030081c0c0c1040303031140d000f0000c02800a00c1c0007582e4180346a0a000e500d006210f409110030615028a03108000145104e000c001415589512280103a110140e021f00300c80741c00d280c1004011040402c0041c4894802e007403a00c0c50000c250000307030540c06508031080d424400c80214200b400307407540048650074000d8494422043d11040220f07150451a14081c040300b6240203045460340c840c00c01010086025415903480c1460b0f9540c05081d42d1060341e04582054551041c401d003081000402e42041d001c4000451030f1000b00d50101d1140f4046e840007070701c110360340c0188080c1c9851b81400c1b034210180e1000341c1c10081c92285007400b0f039600b00703024081c0a403184041c04540b440c021071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 420285134 1250 420283884 420283889
    0xf0902160f021212071b210303290406050301020a0f0c050a1202030702041a010f030f020904111b060f040f0f020405090102120f040c030b07020316030903021801 71
    0x960032958a02a51902050740820740c100301e070003040070700d144000c4010030f100c920000c2c2152181542d5030001402c164141c00c0b41e0742d00c51744510311581c0d401c100c4400e803409103003003c00c44806980b40169041c04c06400400200c1c0b0003540721004018002c030001d802d2808030200c0d16003107504200c1d040c1c450051500301e01407601c955020444034005028411b003da0400602c892141085900c146801d640314075103861032452100240e80041404421890300e40248806001d040034840703c4460404002006c2c50080c900c10030906649003030100280307800da0112140c40b03002a0043c041703800d81c0e021910150f8003074801c890410b5540c0920907801d03030000c42d0144c0a41c010740b080c840c50380c65a8491400c8601a95004c580342d031164034039400140c91b030380101c510034400c0e000016101e902c9204c2c41404180010510b01e4256080002c102c005400100c24905403038101d54807104540da003580580c40d61141c038004034600600180c0000406a00545c681d058038400d0352030312440861640b91480d02082030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 420286384 1250 420285134 420285157
    0x2130507270510080105090f1009020f1209030703020d09050102060103020618190503120702100e1c0f11091021080d06050301050c0f0415050408030a0206010f0902 72
    0x1000d01c1071006202081c522000041c020240c6401a81c0d41c000601c0202a800c5000100d01c100004000703a00d00382068945c41480d0511804c4189004000c445142c1114020340d240b09a01003089071514070b043c8196004a4480351a107101810070180c61642c030381000c2003c80052290381001c20351988508800401c03100c0c1030300140398603400c590800000390800104c52524554100d400440ea995103000101000000c90281c14894103250905080c6a00d40c0210703014504100407107001601c48108090200c41c0500d0402010647c01000641540f8003d00380843c0c3c089204200092069100c1021760702441000704034040041c00080c48100402101e03044060300c007643c0d0400200c152000724040b0010000f1060740c108031150f0fa15202500b003240c0c9110b5140c0e0b111130500c90b03802c00f4440d0340d030055040721405041040308000a8001c2c8651301a120f01c42d1001440100700c98001ea0984003d03010020030b80f0341718007200034000e43d07480c401d104103d15482c0c41c0d04001420440c52080344c1916401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 420287634 1250 420286384 420286397
    0x204030b0916050f0409080a080a0f090807021315090e07090c0206041211032b18080a03060302040227010f0207030308060a09090b01031106040e07030f0e061302130507 74
    0xf82020091807041d14540290401d031150301c1c24000a0f0400001d10b0b4081154461b0100b90070925911400c460102050b4107046180c80c450381c02045e040c600791b035040c07941120403100354034030a100708003d4111001031f01d41802c4c0c4800082240c4c00356400c4044244000b400315011143c1e40c00c84d14082d030b414659030300d000da0402c60105000c84c9000003001d00e000064185211a1040700340d403a03103075500040b1600c0c1c0003400100810040803c00d003001c0340829000c0070a0120100c01e0084488611400700014940d410005280074818000e400a030000c680040045407241c106190ba0003030845200c010b42030507035854141082c5507004141152810145030300070301d8110308690382030b030715264040c007801e51000b416100040d00d102c0900520207028416810300080e5459071408003403240b00d01c0c2d0064400c05e030601c401d01c2504540045154082c005180120385500ea45002c84001d2820340e0400503a801582d081012040d4000e00714070390380d442030b01c001d20800c0307070349a403130007103550035904900040d44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 420288884 1250 420287634 420287639
    0x60f02120c03040203150c0c120c0c0d030201091703040623060d110901060f1206140d0609060e0c180603060a050414060f0601080601053103150204030b0916 69
    0x2501400ba551161025007101c0040300c02c140704455849040b070f601d00c011140010302880081091240d0210320812801d4941021400c6859540320030650360514000d80041d80e4034400d240c17003500244183e90f00300490318084401c8544035092580115401da40d02e5042400200d00600c0c103040502010103110039500f2140c4903201002401d0031786040c00d55429200320101403283d50388003820f6008041310f0b04ca46800104407200a007003241800f801d1507406282c24010003001a12000c12070340c94900b02d070340da007214034a03141540007400c0301440507048502d0851040310030040001d0032480040c00b00d500014113001c0c001c1c10030301c07440c0446a281d01904140080741062406030031454210b84940c494011b5420591409858070300c003100d5480310007414a0170f0145550f08510307140d400500c28030b0020b15100300f0807603061101802180d1074114007158050042d0110b09800c0c0d0001030b60b4050707090f04134101c41210300f0010390498002640c09030341744004035106000024140c0c55036a030300030780103002d02d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 420290134 1250 420288884 420288901
    0x21c0b240306030a170c01060515040909030504080307050721031d0307120605010312173d1a040509190f051609080d0215150307030807060f0212 64
    0x1c001034a09074051140407800b00c00281c1480b00716000e0015100703d640c9400c2c2c240042d03800d6550660000d0b01400c003400019845420440845054900c501b1021541c08510300c0c040b1110310a5520034440350001044050402101080c00e4080b216100003a98604012440b007413061000c0079401000305044107420884c540e007541c0510a290401002d40742c0705640e80e42861549043c440080380c5441e9101c00500400412020000e007030041460322241000b00450b0b006c3d92540040e10030441020003a041100b0104030060100924040c0172107141140c1c09404161424502409030f40f2944240703152012440c0d2852003034a00f1035000501095070740e1901d40b1122214485094050b100548502c0c1040408195000302070241c034040d130101c0f1849100000040c079030030b42070f0091102504204d440c20080c0d50b0001d410311680d45006c12212954903001000c080040740219901c1d0140a814400030520031010054800c01d40150814011140d10103200022881140c50700400b015201c0c01084401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 420291384 1250 420290134 420290137
    0x90503030a0e0307030602040b0304050f0622020d1e1a0411060c030f040312021b03060114030a0c031b080a030f08060607020406030b01050301150807060c030210021c0b24 75
    0x180e405000d40b2040703174503500c480c0d0681e4400d030083c00c0c91070310000c11301040141c200100310392101d010004e000c0c1030030510b00030700382c41c02e98600d00060307030015589070415944c6281c4542540796110b1015100b04252041001080190101c281c0751030740e219000510440303100d241d19105650101c00810f45581d80070800000c1e82000c90380d0192840244aa820348005000040000d14001d0381400c400c3d100700c0c60000d01e0401d41c0030b44620b00c4401403c4000c03c07a28009134460568400c2d07801c04c12990f59460121b45031650004000e040c4a0000400200307000f42002d09669403200d000f9100307480741d03c81c001c9a9071004441c0b801000240c402000f4080248501040e5820030001030220b407501c15240c0000301540d002c1d0b0010f40392040e2040040003a0b207400d10509140c12955450555600c3c64000c110303449036260300c125418400886400303c1014400e201d0070f5000c1c2e5281404544507000b003103143e4902d40b440d01e2440c04491500300b13410301ca0f1400100c1001e41c0d0030304c0d402e43c4880c0c0041c01c442c000c06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 420292634 1250 420291384 420291407
    0x30608150408040f140f101709010b0301140603070806010b0426011b03050a0b0a0504051f0603091707051c02010e0a0b1b1c0221090d080106090503030a 67
    0x2e1101c02e01000c01c400d0540c0840c000240440455000500b809030100010700007580000e62064400780403610301650084440c0c0c6030b89803a85940d28440e0b4540910310701512800c01e038103031300d5440c0581d44548410107103407090041c0d40550894480c0345e101c07013201c0c0e9210428080c0401c0410284410041c10310f0707070960980050380303500408804140c00d405090039502001c0403518142014080e90510716814810a98400300c80d0106100d40743c41840400e011201900609001c0c54440d00015050544541440c01c0c008000222a96203643d41c40d004000b429141c0f0201d411540e072010485050f1400401d481016409c14042c02c0c017052400c5000b454040e41300c01c02c0301595240c41d0400d0000c10107000b03968146004d54002100740c504405550350211703d0441036056600705102c13201104a4101040b441045000302c010f944005000c400311014002044100324440d142081110520010030340c050740080340d440c3d6981d280d8852105072200030140c0180d5030182e0080c89014035240c481c01c030302c005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 420293884 1250 420292634 420292643
    0x3160501060b0a02010c020609070f090f110f040303020601120305040611071518050315161e090302011d011b020d1a01030519030909050603030d0f0b0109060306081504 74
    0x4240b503039502034118940201c0780000141c0d5407103400484a50701803140742c0d40b144088006d00b8805013420b4000b012081d042c00f944040503a29002c001340c4040d10f41c0305540108454000780d45501c02c2040724040c42d402030104400601840c400040d072a4010486c44000da541503c2d6135082a040850481f04001d884042c1152441a2000080d41e666074002c02c1900c4074240c0e460342d24107000305882004c12200760b4422406540404034124250040003843c9422160388000000794842c110011036048850641c660490403e40060320807032074000035100200c034800e8860401381024010039003404071030340402c0ca02103400c0e582c101c0080f40744140300364142c41c4000e0126408110035100c901050412407140c20008070004010b0092040800c010b00d0003a581140403003240707005076001040c0c640300348030b03038000c05480b500401c5075a034040c01038804048078040c3c00c004204468148402414910907500d01042c0c0748a00862014468000c5006944162000740b0584410040d10807400c40d0041060301c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 420295134 1250 420293884 420293891
    0xa0b13080d0e0d0510050f1008030f0f0a0c0501020a030527060a05091e070e01052d040902100306031b121101022404060c170a0e0106080a030503010306060e070203160501 75
    0x41803211644206c901440308141e00d55998039203860340c49141e6009410074a0958400e0109400041c1d001c401c58a0b81e00328090f240d41c444141c2c0d071017520702c01071990000300b2550000c07408001066161740303e544a06620144051460076040e001e000006203101c0500d0a5046100007511824194104a0304403900d01304a41c3c2107000720301200c3d942f51641d14800c0b0207802c003038401c01150007281b0303a0364050503007100d584030a000d42000072140d01c10411042c00303080c3c06203400da5001d65515403008000303d030050f00c12600f4410700340c0e0040092903a0b000480d241b40d1070098a0095480411801096650110b43c2c1c100180c5141c440c1680e60201d843c0150442c80f07a0840d003d4180510404001e000c10180750402150a0a03d858801c0d02c80c003111a0741000482e0304281c150500c4c1001c200d42001b891900090b90310b0794040740c130340901040d4104800a110301428042055070210040d8106ea02031401003000548416040e0030030034054411000580c4140000c901402884481401aa200d1030001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 420296384 1250 420295134 420295153
    0x121104150f2309031509030714030f072a060c06050a09080705061602010903080609040302011407111203060603061e04050c030412020a05030a18050a0b13080d0e0d05 73
    0x51031414400c2106501e8898046140340079800d0400000c8089008105c4e90034661604054503079580c0914100500400e841104080360200e050044408040640030742551795595400c02c1c041d4447e14843e007003004071418081102c19804105d00707800b80d803126503e9000c1130039107840d0314000c1d04020703020041d0070343c1d140350301d43c00149150028540c1e14400d01c0500600d14001440f04c4008042e003855900f56410288c0100001e684010025489030040b501c1c240580c545040803401007100340c0d1415a01581c000034030210540200b82d0701c502e4600c010403122000300ca102084002d010582d0110b811500600100d819440c10080d46c0403400c100021882c2e400f04540d001406660041d01c40c13010390b45000041c00240050b20030100c440e5216130005203452911507551581c0c0e8420003e021041107152000d88004540245124008040003080907d2003a1141b41c22161030780181000001c00040d41800290300703d010650407450403040c1c83d44200c800e090800d1000102801600303d03070324018900b81 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 420297634 1250 420296384 420296417
    0x140403060606020607090f090218040501030c1a0c070b0c0321100506032a0c16091407050906090a0305151522090f0b07121104150f 58
    0x50402540204408600a0300d0084040d0030400c01620036001c1240700f06051049149258a800c100c035440d00740140d072803605040a62801d8082c17021a079100d4149400002400b01d0300302280d0685c0c0c100501c09a035400304903c040100c1c403c0300d03010400c0b600850020884003034064050510f0711000c2096a00d8a0301c40700c06082d10b21082680001d10000440600480703179100a58140581401d595052440c100a400b83c071031500d115000d03c2500681c1c407007a081c90314802c800c1d121810401d030116003640540364400500c0d5001c502810014500d001200710034180c1b01c9030718500488a58076598500142481030100a500000486800c40701c4580000000b480421004e2440e24407a0140c0e03003682008001d040c4440300d40c1c28141e10400e501c0dd0761200d2894400340c1514000380c0c6c860002104001c518110038003c1a031200545840c140d4410401625040605040301c1c040c10042000b00c6401c2c0f00c1c0000584c0243c3c00759500c80603a8003004c1200314024024402c0c50b4240d42000208400000007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 420298884 1250 420297634 420297637
    0x70e09070b070c06030c05070503090411040b04080109061a0d0f02010320070c0b0406090612090b040b091011030c07140d0906030b04062106021c0623150a14 69
    0x40440c0c0c000a460f9041020580c1031040400181142c41c01d00c0c076080300c540780c1c541d403030041309040c5100e0303030340c43c11140303803025044040790010030302c203d0041e403200c0da25107a99000380301c064070564450b4280000304c0b1036007030528001c0c51750a900134400f00410322240c582c451100c500d080c0c22418141e403070303100503284002204c45805130040f01c0a940d035600f005203001484518580e21000c804c0800380820700c050b40c1c0140c07420050303400514003165180b40440d440da024089001c4040e22004201c030030701082c05009060240304068000c115800174101610800895040c182e00340d110300d20510104003d81008001050918050640201101e8841080303600b0030300450340c0c200c0800d10641080107181c0c0c05000d0242900350171102001243c0c03038288035000d030111204d000f1019120607880c0c0003c1021382e6054425120025118041070640076800700b008010900a0060305020b400030240b4603452a80300072030348100585141c5d000170301200e41d0040c40d041281c1e180c040c851b9580c01190640e503401c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 420300134 1250 420298884 420298897
    0x803090c09102409052e030b180c0d05090a050f0c04060e060d030c21090509150d03050a200a030f090f030b0406020912010626070e09070b 61
    0x18a5080d024035010408400c00c2520341501065080c2d81c02d103000e61130f0003001501c101c030000c3d03440341406105002401c0f482d405505035013203402c45d0000d6001619605920642c1c001405481c03c0030342070124110802c85c0001103441d0610110208545200b880c5160080e07a00460b407402191075550180e0796040c14050680804002d0b40c6c0030f07035030002840c41c1500540000b0310810803003001a04140002c920892490380e000b034148400c1d20304001c1004800b2024184180000f010340d26811b40c0007000034104481d9118140c03044406c1070108504c2031041d00c03110b20709013004151341d0540c0120340d070a03903554000807040414030024402584205001002c424585900c41000c3c1402c0a490b140191054028115000801c82842010f1003000c013050f003203e0030f46c2d0304110502000c0c0d58900e400006846040b503515007042e21014198a2003105410107415220894001c04028080d5403040c0c0a00e81c0c002041f240b19845103d0030003541004168094010300c0e45001d440449840f008c04103c540d001c136 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 420301384 1250 420300134 420300151
    0x1104030206030a05190e0c0d03140307030b01021b062703010204060e040c020c01090905091e0c04050a0b0a0918051c02011103010b180d05070b0a17060a030803090c09 73
    0x104d00b008160100c0040403044031124500401c61080c03004182650365107101c0407940182600c4684009250142040c1c034030300010180e81c16524504064018007604944170102e0152240128440c1d1840c030310704562651072005003015007030800000d0701e900c01c1032800c0500a60800e1404018203240c400703000400c044d01e020b888403280320b405403050100316000c41c2c0e01e5004540054ad24118980e0748107600c4422030f81d9221001c00d550b210407540c1402d011812300c51003001076180c05107035030900c0049540c81da40d900842d81000103036030700181107054808484c00d8651011040350107002811180d40802e0030065020300c0c00d10040300c2035460740c3c508410031021606480e03e940141c01000e0f824081c1c104144408013185085524000140e4036a000b03c8041c041c18241014544000d0707103500025000701c5170400101c65601e80d484003a60010741c00800f5100010703694070002c504c1078020344030542c05024050008500030b440d40c0c460b52810b81000d0b242d910b05018003a1a258155903203081c0c40d0103800d44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 420302634 1250 420301384 420301391
    0xf06060a061d0a050a080106170601050a120311010c08010501020d1119060b0310020304121706010e19060807020c01030506030a0b060607080d140106180915050d12020106080f0304091104030206030a 87
    0x502c5014540da40c0d142e96040050b2b882000144450303251440d00070103c81154110b900510060b241c1500c14409112143c8010341c078001180f06607da010010604881003a020342da00014850011144050014110300640e03002d101007907441d8444001580ea584d00401000590401610001f41813960748803c0c0031865401006000501a903404001c0f03952080c0d0601c0340003d0841d0f0b551a038000c000500040c10302c0045140750400b070b25003100200001080703442c5104d46903241c1802400d1814242e507081d005114080d180c00e901e50103441203c2c0103140c028000d00c8010400c3c1e866401d640030003060181c00800c14410900040c0200300608015240824041080c5203888009c1c190308005030710090401410204d00e18180c1050348082041e00c13044400070881e4899041d965890540c80da00140e00700007000010390600c052180420201d40c1e1582c000e100c81c9a60314002c0b603941c6294101b81c0c40c1a04100401c00880710300750300504040c04403064650603e5500d8000400c160012504614920346 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 420303884 1250 420302634 420302639
    0x6150c070b1b0d0207090921020d2a020402030c19030915060617040302030417060912070b01060f0e04020403110307171f0b0409050f06060a061d0a050a080106 70
    0x2a00c081c1c0001c40d1480c2d004004400c081e0300000d503030715103d00c00e0108499490700c2c40414001c00d084000c5141e4207102d401003007201c0080c0300955440c51810030400060003500c039084140c0600600090b595510811000444400e4080100a41c070127061342520b240c04012040303000c41001410007800c0e00f01e40b0005807441c41e40c00c0c42c0444003a1025040c01e5646810341c203000403070b040a0015102d16050070810790340e071307110f01c1d0a0b4950b11503604074011081c4200c208442024000403460701c1210070000365a506c1c006c015a410903801042802410301c0091401805070b24812020549490450324000c5c040200c100c0c0481d00300e80c4650070585014028402c00c54650400f0019000140282c20104084a0100365401c2e1600f00c1c47c040c1c4003080e20307549690b200c0200f00b07801c8007070200302c000c104214105140c079256503140e016803c200d2580c0038a00c0043c03441c0c504982110210f9070651560170f02941d0400d601460501058000d5900030214a004286515621414005400c00d0f2000050340c50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 420305134 1250 420303884 420303907
    0xe040507030c0803030705030c0904061e03020312030f07080916091d0a02060405040b181e070206060901051002100f05013003031d0f0c0f0d0b06150c070b 68
    0x50b495080a09590700070014080c000d0780c005c7c200c0307910000700100c007902c070000400007a01404040d41b042e40144051081607100e403030b424044104891080b01118950442c4040307060203800b04880c82c044000454000030120380c0582d8800da485504042907075828901450044031180b00c5410028400355135000a581d1403844140c20b10409050750021700000c0c01550002c3c10a110b00e014035400365440d40410020b03030301e8010000c9410b4003242c618040c540b0b40554210510107421513801e51000c1030601040ca000d0000c50710f58068100a401040280c0c2858144440c1032910000b040451040ca40c280c0f61461613031050103414a12840f0200d2694900710204401302004000345040f4220340e00c00c2d042085851002003012641030a0203c0d0200c50f04070709a5001051586000311802004d200300381e101c40c00325685410a02c2283c0100b00c0551035014099080f1034a00000d000300c40d42d40105c1d00390306c0e2040071100e0b02c600914000d4903081000c0c1003e030038124654400390110001195a10040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 420306384 1250 420305134 420305153
    0x50a1203090c211b08030712030c0c080f0f2505010b12030d0b01030209060c03040608010e0f060d11040f0501030c0902070302061609150503040b15030304090e01060e04050703 77
    0x8184403100304404442c443d4a281401030b08401c0100120100764a0b50703600310030481041e00420702001540d40f11a030030b04102a0284e00f944055000900d0269408146401444a142070a801140315802c110034032000450945c800003040d9001c0109011102c4440c019030348122148040c40543c441c11002480c25a00b5035039818009803242e609040c0030a00d6140000c242c8840c80700849000c00c0c00003094006a0082c4101030b0000d03004400021f0400343c1c81c400000070003c582c0b07195184e9030107aa0302c0103060180c0201340c418040b090074174004505245807081010304403030300030341160600c80c50f0100050b0803140c880d080c0145075500c6000400521010040c00c400800d940c0d42d05500d40406a1b80c02510b825009106034445466031014840ca503101d020407001800d00300014a2840000f0071000e000e0382c1044808603080700021000801041204003a075003080c00183c01141014204154000588405200740805e036503260400142d030856181003900031805200502500760840c205100e54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 420307634 1250 420306384 420306389
    0x151407150b040c0201020c0a1b050319050d02010606050711032b080a0908030412021c031a040b01052505063402070308030604020c060708012310050304050a1203090c 73
    0x3c0d1792040c041e040d101000400c2c6940a80d030700c071080090014a29200e105404030603040760b5090320400c2896418564580303001103685001d0303412107141051842080342a18160b00030300c8000ba5060080c000010401f0714581d000c0600141611155060074800701070040c003007052030b0078081114410201e41a0000350054220003800800d0110b69083c2e154002d0511014000402e071000450079010310510178040c405110b00c014a013040c0030111910018080e1006092020002480c00c48208c03081c0340521441e51480c0061712001d0601001d1114010b0144020035810654904141c035200017070350034800140318171002c2401e201c550340b00c4411481c4034445807505030b6240d0000ca81e407a05158001071843c0c2141e60026900d907072a5122404034000e402454113541162003280180300701d0541092085041e964450048407003510300301c5000207101e4031203c0c842d4010000800810b04144510002e42e8064042c40403680345003040d81e15805c0e00c00040b580d240010b43c0d918031142c100040310060800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 420308884 1250 420307634 420307637
    0x50910031b092115050a0b010905100f080901090c0305160e0c0d0507031404060902030c0a03030530090a0b0609010602191b0305061b04151407150b040c 67
    0x80c440c203080c00d403d00b068900f00860640420300d0f855000300050394481c540300039801102030050f410490300801c05841c40403040b601280c10042d000c5800d0a00e07800540502c0000e603514820507903841e909a820300f6014003003285035500c4980100204a101c010034000750301c01c3d801080b0100341c520014200d0341c601d4010580001d00e900c1030107030140c80d603002d03203010000c0c200b0006207a48034013900750b00801c24040c500c5400e03400101040280302c001e900c00742125000f0380598860301d0300c1b42d0400100103514000240810003d01c07202c0d0041040143d95a0030040450504492807030a81c0801c00c012011120500c1c40d5000300301100400c04410b03810358002c0802e4a084020754104200a9250b01c10030444682a002400350002440301c061001c008600f0040c603a070064984a05040d502c80c60119140c4403580400a0b135202445481c000302d43c12a5100100404508561701c000c89081d01d83d905030044d44c04003070181c078001c1417510030b01000a010b00700e00040d0940d0500188001d032200028450b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 420310134 1250 420308884 420308897
    0x9061f120501090507050703110a0c0806060a080606032a06040e0a0b060a14070606030602032d0417130306060902030117010e06010b0c030f03130b0f040c15050910031b 74
    0x504550070409540c1c40d994503040502803110400c460624008040100bc0d1551044140015240740041307512401400145c580c1c1d68a1900e46031010383d03501041d02e6503901355000300d03030182d80b000c09078010000c01c80071810700f501103c000d0b800003916500545c2055541d0585007041c0103000c0e030140316022030104260b51450a0222941024001550b0034103030001c01d0304000b410804101ea694404e00c0510b50100045490381001380c00012220715106070441070560180c465450700c5401001c0f2840b6917403000c100881900d20703202d802030075000106804a41c0304420004070001c2c0c50f900030003020b01110070f0010388a614000c80c80c480780f81c0090044071964900507000140c3e00340480d000313054030083e001c102d5540159804080c42d502c0b07003106008030520048140110904401030703880c490b0313000c1c00e01543c00d0b45030b402d4030042d1080280d0b4001d1a004284030200f00c00000c0305e0080c040308103a4102141000c4000011411178140196500b0002e9034810400c2044d082d040c4410302c24030303000d14229 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 420311384 1250 420310134 420310141
    0x6010801141305060301150f0807090603111005070609052127030a0204140a0e0f0307032006070f0f0e01051c06050d11040f0209060909061f1205010905 67
    0x5400c1141069184102e0380c1c0310000204076880135000800d52861103651086043e80c0c44c107004010352100c0c0101841401201300c0080c001d400c0d805190103030b07a0419145100100008200040d01e20495030101c10f114080c420341c13021a40c240306014515024901600f41d0b0301351002071901d1018614810f0107006e80070f101c0451454010800c084414050a00000302044554002440c2c403214020027075000b410000c041d00d074100c0c0f4071070050144810010920100300c41c98146902c0390100e200020555006000040110780315500d90410b104000d0040340d0200c00107820142045030031194600807804019454100f40d80c0903805010b44101071070030305103202e165000281036100d86140c1005c1900c4000d50b810346921254014001404010018801d4148a103040303540e1035445140c2da0712484c90301c280c4070340300361060003241c015500040030709182c03035080820005945006054160004035960403804901c081c42d1000b69005003d441d16084044010303820030075680d058102d0305d00c0a0409050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 420312634 1250 420311384 420311389
    0x90c09050a0b010f022505030d0201020d05010815040f0305040f06050a11030c1203060a080303160314070f1b06060b070b01080d1e020c0a0f0302091302090c0904110309060601080114 80
    0x90702071040b0024246c42040d081802543c0600c0e91300415403500943c0c40251034030f5015801003481e403075400b000340b100e07a80c1e45c08895240d4106c40c510780c1075510188000750000b902502e042c074149200341419820180c8071646003117090942d41143d0042400060448030030394005501310030001640000b9485c00c0400410182c84060003040410140008400305071746070355018400015100300030440e0b40302e18203426006500d4040080510101c0e03d020312104512082c180e03002d126001d141c03100a46000c07011b00403074030318104005a443c88086840144001070003800f9801c000c002800d03401ea162141c0e418103c1c0300d01c0040c0c2c0488015881450100d25141d0071540440c09040c054890303d0114015140c10b9040000768081c16030700680c0400c1c003040040300c000191042d80e000b990603034080d039510960450070382500304011f03612051440006240c04140401451850005007000c00c6003000521180c0c001d40041d64102c03016000107080000c0c9580c00707001035005001c1c0d00f580703201e0078921801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 420313884 1250 420312634 420312643
    0x30f0821040c27140105010807080702071211030109060506190e1f03060629090f120312130209132d08070c030c06140f0a0201090c09050a0b010f02 65
    0x180344150310310b40c0985001d048410308242121008000240104c94403c0360100940e8800d0244e01c0c0414102004038030002d01c00c0e003440784507010035001016600c5c00d04001000d4041c1c0d0b039003b12801c41e880300841406813001e02601903543d104201c045040e0030300c1401c10035542c1d000f110554503a02040d104101c910b40c00c01101d60050021034181e4813442e079803400145e48000c148c01c0034050a040c400d0024038080c8121180004200900341d60420300c1d01030329040c10078812440039070303800300040640480920b04108844443d6182c2001ca9250215070321f007081c5404022100b480d410788800030030b2029410008100c0350b000c400401400780f180e0703455560152403d604082c601080c0d6003c0c1070502c20a94240c10303031400350303005544291600a6031800000f03000050000700d510800070000081c1c0c01d030164091142950000c0d1085007812100c1034407038a00c4e08440b803100215902c8601c00404280203076402c8000e858406000b20b844d150078840c89041c0e9903058401c40c100300141058400c034550108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 420315134 1250 420313884 420313889
    0x2060c03040317010602150f130201080a020c0106060908190b070806031e030c0c01090b040314010b041b030e030f0706020921010902030c0a08060103080f04030f0821040c 75
    0x951544a4846080c00c4800d030741d848208012000303040001107860750700081c0025030913501d0a120300703060b03903241183e02d4894030a0b50b032400b07030002c0c40090f0320041d8010401a503001d4804200141089526205e06080d40c038142e1000010070380c480c9040c04101d0040c002481b441c00403000c03000880d8002c1e510004c800b28020900410007002c0e1000ca12a90740070306c60010b13102c0b0440c0d0050185080014415103e46c45903007070300c00074030640110f0140c950041d00b0100850701001100c50401c1e01d10b842d81c4442250500110005558800802c2400ea455129000d66141420b070b8070380c0903440407000a0b0483d0348130314815960340c1c801c1c00100240390801040720401c0c0d60180016071660b40440c0070421007040c41c03003186a4010320080403400d0860540c041d0008900032811184100f0009090203114400c030701981e0a280c0017400117002042c01c035001010921a181e400078601903490300c51030710050080b07008840c80200040c00302004440f14911400c0700081483c10b9110341441c3e500c0c80340512080c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 420316384 1250 420315134 420315151
    0x6050a0507060f020a2006090d18230307170d110c1e0a05120607050304140a0507030b060105190810030602030a0f0612030c02040504021f030b040501150206 69
    0x3540c1c20070450150880d00c003100c4282415502c0f848041c40c00780c002d050700c00c02d8900f107069074200d8050070400011a0b601688006020b011300905500003101c03100c1001c03446032000b10070b40b0400120402d882c600000c59421a00e840042290000101400c1c00e0742071b80001080600741d8000d51089030b004c40d020300f0f04212410140f0785e200364401128200032410361441d41c480001c2c1c40c10710007901c1008149203201d20480e40f00c042240c4a03000c1145541380f400041e81c1c3d592140002907582c87c042e0004542140c0641030482d525100e04c0c400a1502c04460f40895982c0c004100400400c1a5102400c7c2c000e402424201c0c00c00000150070219070a6000e1f4440800c50b0600103e81304090501d0180041d5801c10815956403070000d2080010308064002c013114580740c2540000d500090800380108a545951880c43c442225020040030305130241c4280d0b40b049040c1d400007495009442180f01303014458801081000c041c804100032180140c0c8807401440a00e00032034400c42e4082105075101e0f950 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 420317634 1250 420316384 420316387
    0x308060f0d1208061903080d200d020a02060a0e0a032f0c130c12050c190804020a0f08031b071d040b1b090103050411040f0c0801080706050a05 63
    0x8000184201c0c41054000d041908aa124005410b6005440502c10301c000e5801d9054524a40802a00c010710303440b001c3d2010703205014a0345a0703d0541c1080001180d0034224103602d000d42c3ca4008101c0d1b120740d0710f40404950001e41c00004a8041c0715056002042c40c1e000c02010501101e07482d20389568030402010090754865950b8440060712196215100c1d041185800540c80720302c10f503890325030b4201144111013886a40e0308c10962030007007481055440c4d03541040760b422414103002a250207404522801e20520488580301e890b481c0c0d081c141c020540e580101820140144080a501c1381c22606961099203014008480c0000440b05001201d60b0b1a4071600704001000c0e0605907150000b0280d5620b01c1001181c0040c911030b0702d0300075802100c464140e41c445c800040328410741015414034544e414841d00a242d030003a07020a41c841c1c002e0a50f00702d040318031070000d001c88200500c800783ea030f075642d00a055800da0041c0158003500030309005000050400001600c10b009081458040010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 420318884 1250 420317634 420317659
    0xc04030c2103053402091014010c0f020301020f030a05061519020705032e0c0e1c0b0405010f0c1404170a06020703020c040b0105070c03080a050708040306020306100903030806 77
    0xd824144140c6004040c0c180000b19031320a02008001413401c02c185c0c41400c0f40c4011a900c6031610b032000c412030319460104160071600c00015154800580b0041c0d403220410150b650158500b80010306640400070102c6699160466064003101c0c0d001d0a101e009400d500000440c400c2c1d0791044515542d034154204e51249060030040745007010b503130011034140c00703089100d0088031f441c1590740d003691104c001c0c60f201c101d83d0551080129011103d035040041e0781042202c0042c00d00d40d142c1905280a0b518040030b129041d11107203100704040c2d40440d0f50340c1d550120100414400d11035041203449a00e01303201a40c0403000c407120301d40603a018810f400c1176020104108100f0400800760703803e5010350250346404c031900340a0348031028644918001ca01b080404181503100744105c4090b0741e0b000d8412186281981c5504425402c0200c0480a21204000c501c012505010141c070080d0710504015070759203800310521510788980106601489000f10041c070002e40c011158980c03085094961032034811 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 420320134 1250 420318884 420318907
    0x140306030313030f121e031a04020c0703060c0e090105101b05010905060c0705060a0507030209060d06050307050a12030f020c0d0311060708070e060c0102040902030c04030c210305 79
    0x105010a0007051001810000f0812544c2001d140e456030043e03040d200d2200034050240c43d021001c880301000d20b000c104403000b01b14002e50040001004a0f4000d20641030920040b804990210b0400c48641e4020001082000040d010390402103420749050140603207900c001c50400c0d0418000c0b05e04c502c40c440813000380144500458403485a11018100030b1140c1c07410058020181b00301c0a8881d4003504c0000349076070103510300310380700140d010000342901d42e0751110000c000d00c005041441015020442e034500395441c2e401900f08080b040800203070807454001014a03208150744414016482c15038100300d441e440b9054207001c5501801c00c0000f034204003008070300713040c175080070954003141d014550000e065000f400e4001848080382100d01035200c15800b40d07101c50b8201c5e49500081da0403102c49009040100c0541503001d506000527080c903860340c00c20b4048c2c0e0400c45409180c4003010400300b040c0403401403082c2c0203000d0320a0071030140030f441000b090390070314062000d030a0040000d01c041307100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 420321384 1250 420320134 420320137
    0xa06140c06040317060d08160201030b03060709180e030919030206030a02031812031305070506121b0705121803011d010b040b1807020304080106151205071403060303 73
    0x4040318000e8603080d252525020307050494101601400c0c8040400240315401c0c540700c09220140c1240100c2e04040140c0d0070041201e500003022030402d500d401c1052565142045018021f0300c0b02e0b211444060b00303141c901c14a0802d90300000480605269030620300d8200030080b10340418060300d24106885040d00440e004007840d91009400410000c1045400c1c00d090b406540550f6924041c0348103c0d103006041a41d030b85861b42c0141d4503607000c201046801e00f1341c0c5540c90328103210760159404580e1b181c0005481da04100c11106202c1081000c101d03400c500c14611100031040b900c1d201c2d061031402d4030b0361030b69801e040092101500c0c00241001d04400e15034506190103400a000b401140c9070f40343c1d500118038900852181941c20824400b010f89040d00401070124400b402c1c40100c042e60070b0b914400c040c009130110003075010400c404500103000b806010050106116810039180c85a44c004288142200124810710f14190601540d681d0049150400c00c4084150a443e0348440d400203055 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 420322634 1250 420321384 420321397
    0xb010e030109080a0c14070906090507050702180a1103040f06060602070812091f030905070b070f110409050a0515100e060d02060c0708060a110a020d1d0901060804050706020c0a0614 80
    0x284c7c4a64440010400907a421500170358042d41c4040c0710750384070600265410301540710b000703500c43d01c07002d00201c45903d14012664001c01030302010070b03000624403410704141e0041d0703000e41d0201c4020302c10340180030180c01440010045032004201461074440403d0f01c07004e481c1c031841d02c8840d0005014051342e0b20204200103091030102c241c80803e00b0900301070020650003800710b415026480000404d0424a81a5940213802c4a800d2405002c15540c5600403140702f6802039005580e581e9000107da0100200c4070341c184104020a1270140851201c1452603008100c01a0010440070521009040d46280c90304210151081c81d402d44107840040c1c014002e4000420003442184000a03010000094403401541015010040700c510343c49441510300c00c6100a1000d640201c00441c0228030941c010464094000501e50303100c00e00d40d0005204a00a03440600040e692005000900000340500300060441e400180702c1c1c4080400803508080581c8078480600c10101005007d401c00170088030384 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 420323741 1107 420322634 420322673
    0x3040b010b0316270b04030309120f0221030f0406030f0b01050715140f070305100305060601050903011407020703050f0313090f020712030b010e030109080a0c 70
    0x5800c0840c04d8103c05800c86074980c40000030340482042c01510400c1c5160790b90390300e5400c006240b50740341e400429403501d003071800b01d00166444154074407207035043e144001c03451100c824082508020300504901030100081100c0c81040c20350007041aa0704c551000c0120590045030780c000c47ea013050450340462010030100000c07030f00c074414800b64011403c0012840810383d15040f03066040a5641c15281103801c010720103890342500446a0120035006440e25251039a140c041d52040f014041506000300003030710510545081d00030300c1420460140701e03a01400c00c80c500950b110403511080c0c620340603005418040c1e450120440790f02c4a603500312368940e541441c00360401041326030041d5102c1ca0342080395038002030003660942005065034400083c1e0800c54000907001c01030601d0001c1c400d902d04181c0000007441c00c0c09451200c1001e1034106901c01ca185401030755422000c4a0b50b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 420143884 420323741 := by
  have h0 := BRFrame.cov_init 420143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 420143884 ≤ n) (h2 : n < 420323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
