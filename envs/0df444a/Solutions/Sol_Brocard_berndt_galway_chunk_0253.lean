-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0253
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:45:24.000827+00:00
-- url     : https://prove2.me/submissions/b066979f-d4e1-4f79-9385-ee884d5f6de0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 45323745 ≤ n < 45503601 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 45324995 1250 45323745 45323753
    0x320010510050f0306040b011a040b180315010305060a020904060b030108010209030f1c120b0307030305090f0f0904080307090b0f04030c0b03190f0603060612020901060c050a030c0f 80
    0x1800d214009070810a034000d41000d00748520100102d00d681c0c065803028080c0404911143c02a60440c0c540b5940079210046608416101c0d010f642d00204030008049102204d44a18100e85504600c01b46d084841c503002003c426a40103c0c20b21016026800840115107840791a400030035040704090b00205000d0780d1800e242180c0c2c0d1090340054040e9601103000381052409001152406174501d00900b100303001212a41c0c00880c0b041041e506100020140401200b0300b0b40282c418018000d00b5500141e80e282000f52060740064191485800c03042d890080313600d441c08540030b0001c801760420406a8036552280b4555101074507000a1222070100003c102a2417001080500305801100c0d480701d15503e80300510300540d810407612320384144100800f00042000d0701094070b80811003c990300039035150090003030003590409469241040340c0412100320790384000a050740b0039194039080c5c4c0e981e034404440c400519040207005412140425000c24401c1c241c0840700b80c060841000c42d9089552 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 45326245 1250 45324995 45325001
    0x10201090b01121106030c0901050901030b0907020607020d210b1903030504030516030308060904110d0b010e01050a03030207031704090f09050606010519030509030904020301060203030a110405010c032001 90
    0x44000e26041c03e1010a0703040010105406181c21401c1c0da49608500b070032804041d903801810400c40c10802c0104160619038401c0e080000d4a12000d88000807901f0f01401c02510b403c1e0460f602400741c85821014403541340300b20300f15102c000070340303035003a11086000c1000700140404508032548007441c0707004c0001d04424262003800451194583d103075114a185071150408600800351410780c0070600f0100b011a030441412a403055046032600070656451624600401c0050079445d0401d113060010020803080c07417042810790340f0350146240c1c03d82c1e0324002c016401c042c1380401030041e0004401007000aa0a81c04242031101c000405400d00351540000c03002c460788445c800540948564442c01404800d00030290010801e1030003078600140c840590701300f840104104010180d40d50002480f01000f03009448401030000c0c4107640d6541c2d40c0c80002d541b50801d892510140e864450000a05e09043c0115003c4aa06031100c41c0d80380c0c01c544041e5200036030309003485a0b548100810419051082c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 45327495 1250 45326245 45326249
    0xf0904141e0d03060315020c010f06080c0906040b01050702060d02120a1e090309120606090e03120f01050a09020307030207050a12031518020912030301030f030e1f0509010201090b01 80
    0x1031031216440c40d40c003181490546045042002d140c54600d0610215030a91b000d0940000d80c03520160f82e43d107295003810300400c40b40000036100b5142000119240501089a03001010122004141500c981082004403940300201b00e012034420403041d001030030503070050000128220001401d18120703410039400203004035561070104d51380b0030700d04826400d0858540003000164004201c1c50b98030303a8010705043d40502079112401103640184d42005003e0700110003402d00b1107418000c0760700d0f841d0f1290360380d00408901e007030612000300000e0184051501050483d1801043e2104079490a50240025031001c5c203604105030f020042c10303010a2040043c090041d1080060500c2c940c42e82600900701c07194048008541d104112040010a8020b18001c2d11081c10640051766400382000160b0518030384a20720205010100002040c0f14400d02070b10b0440c3d000303031903e81c020b41e010010020807803801c82003000701c9040c205105108512403405880383c140e06000000340000583c9801e050781d5800d13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 45328745 1250 45327495 45327523
    0x40c030b070206060406090209010f200a0c15020a03051801090510170105010504030c03140c0a09050601080a02030c0703180503030c010e0709020705060a0b06070807030807110303060f090414 84
    0x207000f80301c000c5c1442c0c803d0380002c101101d0118105000d0b000000c1c244d00d01700c443c08080198040d440740234450a4000e900081340c4181c22941440d08901d030070f40d468003d51040d220804240030607901150700110b50301c0905176141d5100c62403c10780310030300c1142c0c801002c4098100440300d500481e00c0d46980d6602550300f809612101450079110022441d40c1405810040c10008184010030004a8004a030002e90f9030004818150b00f2481e8801c61426044a00440d030003039240200007401c12256000c01d001d6102070740c030320780d59540706814042070f071000303540d1100220410013a80004c00d11821445001180d03140c12007040940d00d4001030302e950011020304a95035075038495000311000c01c100c00801000c0d034040950410009450f45074680000800ca915041c0c2c903030034003120030b60310203089400a42d401214552502c1e12401c00401c18841150301202144c050815800e48540c00004d59204003c01408171f081e960f68403062100c500c0000c0c00071108840c00c0d0303620312104a41071116600c80011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 45329995 1250 45328745 45328753
    0x803040b04060518070e19020f0a1101051b07050f010e010c0306050a1d0702030c0106030303020d0f09020901090902011107120c0e04030503010b09060d05090d03111908040c030b0702 80
    0x40750600c0c0044990140c4042a0004560b5001c02620008140c0d0021036040c1c4450142c5595000070310760b41c120500d03000110042c0300107001910010500c01601d52000e85a0302d21041c41a1240d28174202c070020361b0450883c6ea010414244190380903001070100c0761080f801e0b15064190f0110356425145c0440c003429242e511000000541c982c14842c107001000c0840e40090514503003140381a0360480d14410500009511000520303182c002c0089425032101d0074000c000041d40c0c2d0600500030341164003030700e030241c0c146070040d503910583c2e0240041d0f0540003419882a03910f00f200860041c180f04c00101d041c8001e0001c40c5801c000180b003a1b5008000b0240080c000c910180b03000e407000c1d22a60040704169030b020003071002003503115051300c0c1582e503d2410544e81e100c14600041c0c2a01481501d2640103041c6005c00000c09404280049400b140d03803400d0245050200c05604940245407802c141d0a802803041101c2d1440f8194964000340541c40d091100f948136180c440ca240b404807070110150340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 45331245 1250 45329995 45330001
    0x306070509042d09031e0f0e010201020a0e1903080c0715050c0304140a05030313060305090304080312060d02060c1c0801140d050708030a020703020301060e16050706090803040b 78
    0x10030380600404210400c2c0c1c4001d10070000c0320700c40c07042c0f0709520142c49600ea03a45035100400d4040c418200b0020030075a81b480720702503c003400900740300c15106203d00050304d00c1d81d010481d5005000b81d0b10392aa040e29418001d41016003481010700040c4c1d801118a07901140c0003010800d01c00041040358800c01c060400503081c4500701030340c42282403020080100030054414001004020742d4281e5003030b80144051201e00500081c6a03084a0b009140d05001c0002c00c40704680451003d241203a420f03440510086d074402c14507540f02c3c0640e2080e07014035003041001d8216010708011181d40004000d007081c42e0304410b9004182603400c60103596229912503040040e004a020740c210b0701403c210300e45841503606000191100d0012510304600411031628a041085020312000d40640400411030b1303212444603000942c1e41d0458881039000754a01900814101204200248516500042c81c0700d030b0b0521000031141a0700c460410b941147da90508000007030191030080d03000f980565504102c5003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 45332495 1250 45331245 45331249
    0x60d0c0915080c0d15020d1b03090308011a07060b0301150305030a0228060b211b0402030702071701140c030106080f010e19090c03030f09080705060304060b0f0306070509 75
    0x4844450144100c01100100740021490345e10b10a0103100342c039000d611401c014208001074a800d100d5038844100050520a00b41c0d4581d100c02031444c06503a0794511640c0c0c651058401c0788500e0424001c820b402c0104201103402c80d0041900c610003e80000b17030031100040e0000c800b0105810884903a080000c6808074079a04002c885e540c4c541301d403c490001001000950312405803404010714407501e913069070702541d075104619100510517078040c00c01c170410702442545802614400317010b03621101c0b0500380142000d2003524843d2006800510401f41480c0b444000b01c040c0e40c2c8016000c2d900e03442841042d040da807041502822500050545039410590040c0c04a040141241c07400c80b800c1f001009201d00d06c0507002d1304090020b900b544560080344846026042c1d90303a010300202c401c188001b080650261020b485140305580704544152208000e580741d094a10907254420030500126010800b1a0300413182c1c1180101800614130000e8003090419034122840340108070041a002818 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 45333745 1250 45332495 45332503
    0x30b160c08131503020307091403031c060501110307020f121009080d0c020f0a0809060c0a0c08010b0a1a09011116050a050d02090103110418050a1e0803060d0c091508 73
    0x740b0340c04d00b8194103500e8180002008045984501440c0c0010240f80d5813032610140201e840034440b00c0182c032240128001c5e45805481244100c0380041c04c9840208141403022060304d03902c5038010510104401c2200802840211414107036556003d007103074000041c2003a100d540c02c01792140d03501544500068100310100e881015161040d5000407100808604e4080b594514503980a03c0341d980721002ca002280480c0540d1100c1c800520407403034400c0c2840203400318142121082d0000340000300c980790900000050502c1030300702441460341c040b40024072420180100d00b4040c98180d600740d180c0b01c401843c2180b05400d40d440c89500c45024006030800b03119210103070030142c0301403103c4019540801d0444405102c09080b200c254020802d2960f510307004030740a400340c03031446641419503040841c0c40d109002412207600384141e0161042110314071030300d0038050300310348403d041d80d4520050010740c2e40001401c40c0d4119610601050724203880c800c241e0344510f041c898440507410070061600d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 45334995 1250 45333745 45333779
    0x90f09010b0a0303020312070516060b2809020a020109120c05100204060e090901060b041d011a040b072109030303141015020a0b04060f0f06030b160c0813 68
    0x240079040002d10101703400004a60940c00d1038086c00000350b890032003c441c5400b4441c8520104422241104140902a08031140707524040703078039076014502c424078210180d40044c151503644c2290311040003804001e07405414842c2d5503000110703912501d5a03605400080d000c0d45d9202007160b001c07402007405420043d07450000f118203801c5113001c0c240070003c1c0540303800c54000b0381700d645a880082d02030b00007908890024003240e003045842e41d85130848008031400d1405240c60032001722000154195140700c1031380c0d0b1014000010340c07030582000300c0c482050384150700940340c055030844084030384042c8404d204e07124a0310b40d44800b5081e042d4980241540c140c1da0350311807800d4400c014030520a0502000a0884403040c00099180c1c02d2510141d00b08401c965003c0d20243c603020400092040a41041e4060350388114100109160910a034003225118040500b00315090b40004d010080c1010b0f81d4103805505080c03421300040c0c41d035584d001990107000241c6071443c0307126081110015000070b083c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 45336245 1250 45334995 45334999
    0x30e01122d0c1409040b120a05060916030309060c020f09100812070c05090702120d27050a060f02040f080a060501120b040605041406150a1406030c03040c05090f09010b 74
    0x10781071810707443c086054020341d43c1c913a105a596101490080e55880108580380c8084415a402a50281801c54568004a866140768040c0c061200c082c0f81c1000480c005907641a1100c094603801e1a104803206110300c2e01c22a0131a2010a0300e2148dd03a030500e0741845400700e00419402c40d410b00600c0e6081c401070504124885a06211410020b036002104074140c03007003510f007a28981c0d2018022032030000403014511504000141041d0120b0703240e008031044120021042d981032866141848481c81c07850000f50083d00030310000340019240d42c100c029850705484016050940b01d480d1410380d212030358450941075000c03c0740d141c100f0087d03019480c010150b0190f180d00205042c1c035040d200020045c002410242d40300d0000c1d04020400804080d40880101214118503103000e02c8000300c4a00e03001d95100e03000e0803000040014a003010ba6203828000b419660030f40e00d550704034120a400240049440809905003c90a900c5240005110b2540306405106909050810070f00316100c00e9031042c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 45337495 1250 45336245 45336257
    0x40b010504080606060304030c080a0c0c1508150a15020120030709060e0613030b060102100e0a11040e01050403051209061506090f120307110301020403030e01122d0c 73
    0xc242880403d140d684004203442c41d85d665030303030f911b01207404424102000b060075801094080140e940321000242841c4100e25414180703031a0a45880040e00800c031050008002d0740004208015034400041180c0c4080c0c80603000d1510b9100c141014518020010b0060b9907404c9250500000c101e0110040b614035002e1074030318102404005e1114000f0302a200503c4514034a10403241c60745000c441e581d5040748145801d0035207a10303140280c181c0640e03060740148607800840c0016130722485800003203020036000780b04a8810b991000b1654502c003250715489070b940c010080c252030003806604c2c411032080c0e44560741d900003c0c00c0030500f01e5003e8002c11040d8000d00400c25110246081004030450888910740c0381c4a144000400c0c0c0c0d40c21074100c84d008450201c10381ca1851001001e4003040c1c1c8200840c040016044062600301d00070740c400580041c850300044030465000d00000c000700032460b0f0000c41c0386400000c0041ca0140c000c09928204148154800380c40b403c0e5201d1015070421615120f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 45338745 1250 45337495 45337499
    0x909100b040303270e06030c01020d020601150302040f06020102070317070203090d1407060503090705031f0203090f030c150c281101050f090609070602030403110a09021305040b010504 81
    0x3140600035404020300b03015891080d10303956000380c40e030581040e00401404424540390103042414100690b0014064400c20043c20041d40c0040368080c11240e4650040c1081d0b071900c0c1c404009074803d1349016003450f41c20403011602d061400000000b8104640000d41d48410b02c2c079000b086010603400c2d1080c001d84240c01c0c04100e03030f404012114406000c40da510050030b1281014008854000d001c9605c1c0d10803018001034440e0030901452080203034106940801d99a0418561a41d862844015a401070392680500040c250f90281d86c20280b0501110490740101201c140740d64842c084030b040540c040240c49500300c4003005007551002e4040303210380c1000015005148040c03038014050088840ba00d0ba072a052034495281c10156082c510002d0200307081201c00d0039805c0c00191041c000301d00500000891584c00003d4040032140399a00540c03030940386460b0712401a0710a4080d81e0b001e10340440026400c2002d001800044d205000b05c4958245004100000c5a10b2000e90506010044c482 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 45339995 1250 45338745 45338759
    0x10e060912030a15051306090e0109030207030f03020c180105041d190501020f040308091e0907030f060b0c0d020607020706020c0108150d0b01080d080c030412020c060a0302090910 79
    0x3a240c11048481021404c0c1c0c0040c440200c0c590815006660009001c55120052034016001082150f10402d8208030180b0101e40311400d9a81c0399201902682c0900400c20000d00000c200c044c4950082c4161407502007210300155074291441101800f4500c03050040c03155107024400c80701d07a1140031110100030004041059282e010441d206d0710105107024000e0140002901202c07040358001e400c0d599110344a140001040c0c00060b0450300942c1c9441203910f98034000700105500360401411040340340d03100d020031005000c0c0116200d40c91900c5a01c005034203075401016000141040026100340409004000e1a00c2b800911700b00071940420030421000c0c0d000f20760301c031940100b07113010205641c8503903062038125080002660024041203000042c05061101036040c4c803101415189050000310044075281c5042c0d6883c1d20310002040801d0001d00701c04500a94441e050051321001d02c1c0410016039680c001441d5a00800d40018160b407503481c0c04030507180d10084038506201c050b8180b1070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 45341245 1250 45339995 45339997
    0x19120b090109031d0d05012405030102030103082218091a0705041503020f0c0c12030702060909091f0b01030c020a05031209100e0d0f050319020901030b090108010e060912 75
    0x94000c0018004030b5080205490702140e11140c02c1d0031500078003c003204030911000e50f52301c07002c00c007540110310113010a0b24501030007280c0c100c0e500503101a0404515011002c8902c684200c0c08201c0309820340001010825141000071620071541c0000303400c2170b81d040503028110318120f01002800311200b089006900482610292407034800808840340b90410160000d10039109280c0352208042000a500c200c00601c00020404c2982c50030050072540031000e03500e0040d684d000354002400e0148a001c2d0801142c89640191010100c80f62030503020940a00c8201c1d8408081c40541c544c0c101c03190658050062010080d91440140104280350300c601d0b86a0007104804000684000e011402c04007040010380700c17240065104010080382c41c070031280e0354402d00d0b40308004140002c002c4002140a18250380c411194066284043c03e41454000001d60009130410f06140e6a660000b040b03450310350499001c1c280c4a000040c288400401543c176061004004034003c0d03100022072907003160f8100c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 45342495 1250 45341245 45341267
    0x90203070b03060a0f0305071502070803090f0103060e0403030905010c0f0203090603070e0316150509010f0c060f0204030507090b030303061c020607060905030a080105030d0207031119120b09010903 87
    0x2081140c072501c480f00002ea4881305640142c0903661a9240030090050200700341044035440054100364aa00d0901aa114960307807203010300580003440703010810304001d814180039450515000902c2e54070b44a01d40c0c0915000e0720700345d0001c0e07510b0510a082103c24032400700ba80905003400308480c0b245110083d540e01c940380d0341710300400300480070517401c500911000000c11401001e4840400e4440b00030342c809100c500c503100f84a815400b00c03a420381d00510071244140010303507900e030004c0e9480301c05650002140703404440407903860707480b134400002d1440684080e520900c00b40412903d0400c100c0141c2c1c0340e10000038440d400030000d01209503038040854541c423904003000320b0726044600004005004180e405452541095540420030502000500c1000c00360f4452050a0342c9450a00d640c520502d40c815025134070040c0180046180030500361103c500041040d01482240c1d5151000002c0c1680807002d905840c1e404282041045290954080c82400007005259206d842c0102603003091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 45343745 1250 45342495 45342509
    0x16050307060e030a0501181104061202100216120b0105060f0304140705041404020306090c011409060403080c01050f0703090c060e040222050a0e010b0a0305090307050a060506090a09020307 83
    0x140142d80c1e0191028089003401c503800a00800481102584640c003051100308200c1e40000e84882e44592440c15228901c241c1d0210180741c65400c10304e50030700016410888c60b54095128051500c0d4200390f201e910080540880107540103181c04034075100048020603000f240c4a15824003000c0202001802580c0d481900011000c0c502024041c1ea00c0c100b5070640c1001d40c02601f40709420701320403103034034001c0d0140707100360202d4546641e68081d082c1c90302c3c44620703400e0000c1c561000c8644900c0d80d240290030b0064004026628280d9290b03501d00d8250710038a00380c40301d40d44550401c000002110300b007941c40b50040c14140320f0442295903807002d450b082d0091109000009640740115251507040d11580ca69404004000070418410410009228813801348600142c450205030b02e002552158101d0300c0680d00c49003042c01c2f069094024042c01480703052944800d210720700c0490810003600440e07a002d19400900340c1016000d025001c100209080301d0941414141c0b4016180007802802b200c4803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 45344995 1250 45343745 45343757
    0xd0204020a180915060309031706210115080619050a06030609060e0c01021204090b01050c0a03080708280c050906040608090c09010819051006080a03021605030706 72
    0xd001514240c9a50080300b02e54801040080341c9030740113901659011131007949100c1903641d41c507012401d1700d2084000900240011021360742d0b110008014541140c0010040b0381c60041ca0b046849150042c11490081c582d100c002c084201a88640c5601c05040098050f0803285801c2e45030286443c05002900c0714140d80340c0000344541001d82c410405160301000034484c1c0c0742582003c1c00a0002c0b43c0d6034541d0390145c1c902890707030307580009580340c030240c3c810142c1414a450a031100b001451140703000e50500408011040e030f1200144540b01d2014800c0d102c1c8001d0f0700380108004c100410050511f1450591038940c814010b00074005080e540c141e1050120300014140412501401b9010000742c0062003c03a010900702d4000d030304540f08864200881e80144400020131066180a2107072411b40c0d0401c51100446822614110b01058094400c50f0804159000d0680031542154040d040c03e4105807281c404056045c4200c1e1103030807200e9403040443e4100400aa1500024402c01e002d10070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 45346245 1250 45344995 45345007
    0x6030c070c0506040801020d06050f0d0602130302030105090f1b0108040b0601020703061a03060a0b0901180905070303030501060f03061406071104020301030308010e0c0c0319020c04050c0901030f0b0d020402 91
    0x41c0d81260344000c1c00001c2c0c681c42e103450340d80100c14040c0d01300989640009080000100c0e8a0030424031000d6529001032026040907810744401000703600c40c1101c0241140c0c205808030158500f40101405001028001c11140b003040e420b040c20140944c14075203400889090001e0160f0740211001d801c660000040b00c981e86074500140d280c401240d0000b41041e0405070100e0101034075609200080e10240c003602d400c1c1c2d503042103400c111543d00c030950303074020700180040c02000f440b07102c0c40140c202d420b0340000c0c0e903003506d48031540b030840c3c039034000c90000741c03240014048181d00c15500044d1400d181001e110050500601c410464450701c080e03409a90082060014000080c181c1994681c000d0811076480d43c481c01c001782450000d01540c581e14107040c0c045400701801504031000626030308003442c14002629051108029203458010451080c1d5401310320310750700e41c81110f009500c3c84803c0350780d5200c00c800140c25140032854604401c3d2404e1207a00250301c400d14401d031116811100180c0d107079 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 45347495 1250 45346245 45346253
    0x120305070e0d03030203010f0b0304020d14101e180308071407020607060605010201060506040b070318090e07050306060102160302060d060f08010506010e040603050c01031e09051b09040206030c07 86
    0x1da90744554080d050408010515425900843c1030b00c007900c40b03110046440e4a094013a51200380d400035001480341c44190b001c20004003041464002e0b40099840d0345c641e1410350400c1c0e81801880101c6015400e41300241c0074298890000144158050140144440e0310b01812961000700f083c014041000300e9940c526880c90100c0c1c1c01c40e98002c101035210701040c105540100759a008150241d0710346040860640703041020740d001c41c2d4400350400d1410b1010b40d01207483c007028100c0c140c50f07045102008120414140201c1005000d2140207240c01c0f132908080618106024041c5815034128000c804160704000c815030080d65010b40d40640d03205014884680180810340c010985440d41d83c201080895040d00103d000d049d0036a1040c44051500080008807142031100a1090f0b1081c1b072110320030750088d00096a0510302c1050402001101400c03001503440111084a032a00943e40c41c1114000a40c00b18107440d40c00d40303000040d8500740c0d001c00d069200140c00088003c03400f00d4000100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 45348745 1250 45347495 45347507
    0x3180b0610140d0b0a0605090a03031b02060d0905060c09130e0a050d0c050601050621070c08040807030b010b0a020706110c030a1101020615030705010f03090203070308030f0a0203010312030507 85
    0x810b19000c1c10701d40d0b0b2401c00803400024961250200d100f01450040018a10710840646035070600080ca031244091550b9820f85418150507803801c02e0103990712002c80075036038850103003980030707000800451481c0441c5892810000010305034440040d051201840d00c4d103619084041d0801c0e0b03000000f540601d00c14001b0b26001501000600ca4481d980e084000035500007805040301d4464811946143d89610411066000300800141031005071454170748404066204a82c2055180c2864540c0d52000d445018090f8000d41141d0f0269000321010000c00010440460040440c02d10140c1080c0b84502e0003500e9440510a100070020250030080b00c0c21020b0101c10005d0b50000c2c119240ca480780c1c505000f411240f44405c2c1d025025035000952942096948448210001030103000450309207801500c02e00300f01428101090790b54080d03000162000c001d11006540541107450b16480e01035503400e00e0050040800b1801401440100002500640348807000015400e011074140d81d8a80c0450304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 45349995 1250 45348745 45348767
    0x304090c031e0e070e0408090103050712050f061c02091f080d020705011b050601030201110f030d150b0f0f030606070206030a09031b0305030c07110a060f03180b0610 73
    0x45501d48008484418180d07404603003040c0c0f0810558120716510b42040140810031580500f8003141000140e1a940c0310354406030744101142072400100441e07103643c4003103030401c60f01c00341980751410600400c0e2500c02c1410850b1900c1c00719180d5442d84981c085070341108040c0c4a515200d030010345c0240035041310b0208001405494040b82ca8030605410300a6039030304988039440c0405d000503150020210866540c443c7c9036008801082181d2030356004480c080101c1d03840c401580119201c00030a003200b03000a01000301000804541c00708000f500c44403141c12503200040a41c010840e280840c070040c0d0031380c1c03101d040744074450362299503071800b0030900d2141100c0250b011500104101c82c601403a404164810b000f50381c2c650003074905c0888040d48414649014000c69428400038505441e803000a0401a00c10081c0503007104035170b0049101000c06070080d4010400c00445010b400d5410300c6500e80001e030880c0f01c80510100340d00c031500240340c0981024021200d812402002e90b0080c186805 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 45351245 1250 45349995 45350021
    0x100302030d0305040605070801030812060301020910020c100c031d0d020402030403021e0601050f090901060807030b01150813020f030f0601090204030b0c03060108130606050901030803040516080304090c03 90
    0x1504031075000c01801400d08903000c03152503144c5008a00850b1294100710305aa03400ba88692400300401e80c0d040200c00000c007900d516640800020400392075a21107044480e41c0c5030003e107103d0340d100313003040520071b403180300c482c10007800403c21804264440714840c10b020220350000041c404885c08215070611194000c1c0d0000e00000078041007685c001040010300c1d00341421044106d0705200c55075101e440a1068503482080a00c0d030810f54501070f4202a000001d00000281706076485c21101d040080b15807003541c1c2802c0c1c0070f004021100f6014905003014003a450144514a40002400d4038400039000203030041e070b94466001c40c240c50402914505060440c1252019070390394583d2006940300c1d0104850130404c1a0102c6c07614082c810a0300d008900503120307110613680d440c4450803e1981c070300042d034585440302d00c0003c00c0c0e01d402000f94003a50148030307100d58900e0281003030b5141040c41d40a002c0c440e280c0030f504220100000c0705481c20744148800c00303c5c40b200c410384110301030200c8000c1c0340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 45352495 1250 45351245 45351253
    0x1020403080903010b0102011109040b060c06010b030f090d080c0a050c01060f060f0201050c0403020f030a06021602040501140a0314150c120f0705121003120809010b030c031510030203 81
    0x300c280624a4054441860110000d1040d000610300480c00c1c2e500350501c0b0003070000c0a1040c65101d152035002541200c03000f90099007000c90310202c3d18601503080e030160341d004600005101052003030a2035194010034480060040000e00d00c0002d240d0780d00240b50807100c100204510803114428030480760304224070002800000d40300c151421041405200d448045101c0050000e10309006008881c85050010b1915040c613245030244500502884902d070f525021702801b04000401c5131015140300d108406007501c45442c03038814401190010b0300200c6158002c00070301d584595a4100c440244d0340d014412140c904014480c180c40d010b2a00f5003c800c600303010040250106460025244000c2821000002525031880c0d04040200c00e0b210440054001c01c50100c9034801881d41d01d400807011504003006954a440307003108140c4107010a4001a140401d200d03a05609004112040c50209c001e007003566480400243d907004403104048514490000080e01d200d03001c440340f17008507000b4081d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 45353745 1250 45352495 45352499
    0x20d020d06090c150f05090411040b0c1501050405010e130507080a030806030105160f0309050c13050a06080d0f180b0301182004030b10030206130504060e060f090702030705010204 79
    0x140590500c14000c07040b50b80d084682c0c0c03a41851180c082c42c0c02c0441c0549520f843d040d046814071018001001e03001270210410000080d803410030b40002c0c113003804010007070005100104480e4441c8081a030085204504000060103020002805650802d50740e601c05e030481030080c070f021801c02c0110f900110060141c110302a040c55048102c49100da0404c40003001036540307040c11000d0307103c10164250b00040880f400c83c050b0501a6008051950050003120640c50700000010031342c81d104980000307119215028098081c0442c011080602241070243c206160042c000508511b1110601401c001c4140014021040107001c2c500c0540040e417800ca0340c030342e141c081c042d0030003403045c52501e0790074a840c0c41d00741044154450141181c0360005c17410b00e03083c9507440d882e0803140064100f00d101e104a5000200599844008000417600384000105440c5400200030840d141e40d4010780423840f54400f00100e84d501e0600112910104496810325511910700072455402400d200500543c400940 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 45354995 1250 45353745 45353753
    0xa0209150408010618051005010f020307050327010309051b0a0f030b0603061008070302010305041406040c0f05060f040308070807060218040e16060f0c0611070605100b0304020d020d0609 82
    0x46001500e05284007480b100d0050245d00302214011284003010864203007040c007035903120320803418100d0790b2481100c1c20084103854440c11588501d03290441140e0a81654490803140b0500380d401920901301000300f160f030758540c40c1e142c03640c0070802c10020308a0700321801c2d6a074403803200d41d003e044840030154040e0f460f4079008102c00c800795640707071080c495000084d07180f500c002c1c0110700f0ba4008001030b00960780f4550065002c0c010281049442a00e048c5520884000c10012144140e008141660b441e41c90030040c58040790035500100e000720b00c10889200000c0040c2c00320340480c6c4c3e000341d1059484609003000c0b4980d004410000704600d000040311003038a05424144685030f40221000c2000b201480318150b540c8081810303924400d03030343d01c0c0104401c5008045155813a54142000f8110308000c0e5241c3d011504039a00c10a8192408256002886000d00c0380d00d41c0715599000040003e81002c003404030900008100a11035000b4191880454035000c044043c1940d0194007031000242c5464 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 45356245 1250 45354995 45355001
    0xf071106011809050616031b0f1b020306040b07080702010606200312010f0306050604020403050a030e150c06010e0106030e071509050603130302060a051003140c090c0a0206010614030a020915040801 87
    0x1100081c02c101c20400c3c80ca40d08d020144003044940c80e4070042c090741f043c00380c0e02402052001510041c000550f00056101440000d1099224504603040c1d0f00d46032102030407844015141108581c5032000c240982a01310f0601d003170080c0340e218407160900c01041082d00e13511a10820001e0718120030700009401100b48a50020fa91040105121540c1c3e0707102800200d014501c0013400c00e43c010013080011034041c91f62040c1c458400781c21004009401160094940d00107007180025901c15001042640b007043d040c0ca000d800c9910b01130050340c0b0107255072981c4107103c0c0a011074005d140ba108000d51805500307610001c08015020a4a0745011045d0000c0201c40c0c1c035068026001d1400010030342c10b941e200d1944101c03504004241928110b0311001d0760ba192588080089100d8140024115603820088074480d05070300078050741e20005600001d04144040e4061018041710400c9902001246000d99610443c0350100607180d03200300d0000b442441d188100307080c24020010380410200c4040d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 45357495 1250 45356245 45356281
    0x11120706050a11010504030914030a020405070e010305011205060c1308060423060c1b07090f02031006050a140a0c021002060601032003040809030a06020d050f0711060118090506 78
    0x510b40f60800d07481c50042e01e099680880c0c00400247c090581403004201c10860b0303030452a0048c0485144d41c0d666030210702240e2055403200041040400c11002540e49809468090320b07044200b00d044000d2a40d0f8203070350710b002906060070044081100c3d4501141c002e0700d2001402003808a4480d801c0c5402c0c100030180b041011206441d80742121411204400070301c1038010b44180400e1403402d510203020050345480394100800130301400c00e001440a40e58060100050040e00005030790f0704051600c0c150081180e0b0200d01030080a210380c405880e0480c4002d00c0700c45501e40600d540d400c162504652030340c1041d60095000c12000503c0403001d0340042c0c52440340710280c900308050800d14054140040e04025001098001000001c001603000405400c801c0c1011b0116407480c1010794907003080ea00f04c504003070956650350302000302c0c401403030312456004205801d01e100c980c0d222501403a11400c05000e00c501030360701e070800ca1698442c03981c4180c07521500841550020b0034469156250103000c0c2d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 45358745 1250 45357495 45357497
    0x70b0c070209070206190c050705030301090e01142e0b0703030e060903160f0201051201090507020114061305090c040f020c01050a06050109090504060f060e04050d050309070311120706050a 83
    0x40300041c840c3e40001400ca0060040070329100e448071600c24031101a2101000307050030040144200d00004108202442c003800301000701180d55000e10030300380d084840c1c41c42c00d41007080c2c2e00380c20f00451180d40c0d0f5103481015040c12a1100f144081c3d007843e040e01c0c006600c01c0c102843e0000f4000245640f6034040860040c1100c01d94000d6180c00c0881680c07070042989044000c070001211000142540c248080c40c14418180710342080510400340c02881d01c00d034030100419880340208001560f0a01c941d4803490607061152519040c0417012684803002c8a1018503c40ea03540049000c00404005a242c0d00c640208284031400c0380c8550440a5005078074000059030030000401d0120241c0d004203426520306030b481c1d0450900e0000710001030100500151003481c0e0340c10170030000c000796005841c0030308105076075100a800e21703280103890020803a500c2e0b010010240140002c400303010500c40c04403904000c0c088180313000d070070008810f2104c02c404544544950781c070002d400b81c1c00002400703034032a41d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 45359995 1250 45358745 45358759
    0x50d15080c09010608060102070e04110d03050711030307210309021009060e03060403020a03050d111201060e010e090c0903010209060c0610060903121b02090f010513020c06040b040503070b0c0702 86
    0xa503c4017591280c100781c44150160300170504c1403200d20036104003030740e11501804109200801c0741c4041060340ca40d004040c0d00140c800520f03041406400e20341c100389004181c0055160210b5500c92040d000d110b2040354a2035100141100a446d00c240c108144290b0028207030340741c025403028080d014401d280f10360f00100c1c50300c8800072458580481d40504c500d4054010744156509941c0c04c40d91580f2403012191095a1035100144100d030304800340c9030010310f040c0f40388c023903504000f0090143d24108a913141045066030801901e80c845e07105050f0400620001075859546620010780603024001c9071580000020030001c0003110b00051190144441190810303005440b042c0c1100c000c201030201a1071a68001900b10f01203220307480b01d1001c0d0580f240741082030754403640081d200303490a8845101c546084801800740349801082d1700100341c02c2c2c040c11840d021965032220344412000340064080d954040001e814490244100c032505030344a080704001c1e15100d52050015000b4010036806406 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 45361245 1250 45359995 45359999
    0x70f050312031303081f0e01030303050609040c051509180103030306060c080a08130501050a0b120706141b1509160303080f04080d0c200606010807050d15080c0901 72
    0xc0c4841c201e0380208002c251050001c11203860560350448040c01105121190100b109180300c0f0030884034000d440c0c4041c040d00c4952550034001c0503a0f02c0130300300510401c030b240148800680c80c140020211407041d9034203800910425408141c0380078030300710300e030f04440e030721a0744840e100040f020907068030710036101081001d8403200c00b190146540c680082c00324400b0420007809074019440d20f80d200c4402c030610b407510840b56841e2425108165034110f42c40b41c0341c2e400c940d06483d10264448429002d0700060008500c2d00340c000f407150101d04030718202d0f988001400780381c140180520a401c03040c04802ca503414200403480c030149060882e0200030a024100740140c146402c5072005003242e815503103503461922441103031144254040c20403281c3c1c4008106a0800b00a24080c4545a400300d498240c204081c0240ea201017480d141500ea8140e0000400c0288a81e00841c485410205c90300e032081c0c8480800503568010300d008640c00f69005c41c0f9501c0015100030001d170148221506950014013a6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 45362495 1250 45361245 45361273
    0x2071401050c0301030b13111005120708090a03050310050307032001030b0916020c100306081e120304050f1b01030b2b02030a06061d010b0306130f020c070f0503 71
    0x80800c2c08000e19952480d804034007044500c9480303000d11f50040c40340b200e6440d8240e0000715020300400d002c2021480114000d0398a82d290541164441e0060818510605d02090700544030406000000c0600c0304c04400b0400002403454054050035001d0b045914254980c1000310020030030204502848805924030390165201c1c3c0140c1c4220f8801602e0080c8a0300c0d90f2038030340100460940404110b10803208211040c0d07035544542148c1413440d4800240560809810504000b044c1c8a490050f08450080000d40c80c2d0000701d4514950070240320070f489031968034100c3e0070000c143d15045524480c4180c1c0005100c115402071005010980b42000b0340c09041c018403113035540c03a285d070030450110001c1303404103034200f030a081d1070040c0b0080581c1d41c6a042070f5180d50807280d00d90000317807480da5141c80d0110190500c215050142a0080b0114214945000014600c1d90310540e414419038840e40008418074164068035542c0060b40c05a403840d903103681c82083e59540501c82c8078824841e4034020042d072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 45363745 1250 45362495 45362497
    0x50a05010e0d0201060b16020d020406230102010b1c08040b0a050a03060501030e0c0103020d06050303160201030e0601080c0f04090605090d0906030c05161106030c0c012702040e01020d02071401050c 87
    0x21a500b281c12420a440020142c07001d900070407048c1c0c0c000c1005503919006a641d84100f101070b0416800c00744003549859214a415a03200f01c1840c15a0314080864031305a8448072070300039081801c17504041d144c0342e0b072810f607205000b82e0780100580200464001c114a801c98003800d0ba80410740c0d810130076650b032000110103031840c0c0e0b010046c29410004c00403141d94402d4005043d0f5415185020800035a12000300c2c1c9960710001c0c10340a0010b40f42251421583e06003d6000c0130101d28005104070350610741075030344030f005c1001c01510070b6124100b20001a1565004030700d007140c001d04204460314041c0c5606465a036812a04030015801050114080f8040d1003a00f2205460350b0301d00d420900807840364404170b01000001d8031900c8604003400340c10780c1c940000307500c2800103420380d03030301d80c5400c2d00302d0b50035640800031803400e0503811001c0032800e00400d118900100d030125000300702100c4180c0001c1c0280f01d04590080c405000041c10020f000d40d042c0100c1810f42c030f040c0204030640c0ca43c01c4005c66 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 45364995 1250 45363745 45363749
    0x60708030709031e0b04110402160c030b07050c060106030207030c06050f040212061006080402030703020919050c07020f01080601090905070c0312110403030c14030a08061c02060d1503050a05010e0d020106 90
    0x60a007040c042004500d0000c0700c07d4061102900041c44c015021120199014481000b220350043c071100c21b00030070071400030300c1c0d4005601d414030368109203101240341d0311110140a50380400d540030580000703042c0708080002400d0781000c0100a20704005004000e1550201c0303090340910320007440c515440100041c4030b8402c020040845d500541880c0c070480728100040c0084e41d041c41000000f00c0580d6403c0d1440c1d004274a40000b182240071a6090703c0c3c26a40018103031202000d00784050b0001d40c840d0342c01c800c8005003d19000c60f196643c5c000580b0300c0300854100b0007826280c08200101980c00401c060720060003922500500700b465502002500c2032840d90608100c0e0505c0104006805408402c581c0d0340300c0c990100980240310031252940c0c105500400000e0427000502983c0e040800e000000d4140c01d60321140e03420440d0f004143c15208034041c2d80500daa0380c01c55030b1031a00f48803043d0405941e010781076800109560800f280030b0b001500303501d881c0d4055908082480c0e4014450075007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 45366245 1250 45364995 45365003
    0x203090f0c100c02030a050303092112010302010302071a0c09031005060d0b060a170606040e0313180e070902030601080106020706020709051506070c060207080c011706060708030709031e 82
    0x80e1500000000c0f0780d900f0031a80d0490701031060200c3e0344001041400598807800c0c5501c010314240c62421207064a41c1e00f0018222060202000b02c0c803610300048644605694081c01d000da541da5107882c1c80007224041e01c424852006415090001001c0242c0090044000450888a00c00740f54082c0104849098802c1070748840340145240001e10301c40c404c0c61703015000909403070000d642c6a0302c80e004600c548005845a400c600304000340c84c0340c144105184140044011400c100c0d0380c5401c2411000c41d80204400525101c07008040404140c00c0f40c01c440046130190341040741d44041440c081e40094030010701180c440d90001c64a070703100042100c1140c140354020000d161900707402d40020a00a806445c0c5180036481b44102500d5000003000c0003071003903040d6152381c0d240c101c00a081070003d400611107500320000707080303041c0c4e40890110088074542d41d1b45003158032110700045880c844c40c2402003a9110100c20404200d03048610402124020107a10710180a00e10860b14600d1400600030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 45367495 1250 45366245 45366259
    0x5220c0e012709030e0d060605030601090603051506030f070801090b0901110d020306061603050703020d02013b010606050415050304080a030f110c1b06031302060a0315090203090f0c 80
    0x482c40110580007082c025010f0305090402d82c0e400c2001ca4158500e0ba070742501c40544450081110741000c1007940d0041501c441c0030081a4210b030b07510b54079080008102e40240070880085090796500384210000e95101d44225804960790b5141c1c54044c01d0585020703507500010600080729824180541510a4103030440d031890403c4d0308a244000b50409800240c0020081c014680c20810006012040501907109c080e2500c0f41c5203002441d101c0610000000c590400c0a1000301017900000c510006c6080f030340c050760380c145003643c46180da038050140c042c45600700000004d01542001c010002c0c0c1e00c200885001c0404038800c01e17211480107a900400c044010400640c03201e00c00d510404c0a034810401c04100752801c111002119080b54501d00c4807034009000344042c0700d514031400c0c0102d60b801d076011411481d046024807085202d821001c1d0003080c0024800c4280340c400e51144a02d9080742c10301c4045d803900e600d4410002e41045800d01c06520603862110106400040e641050300401803010f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 45368745 1250 45367495 45367559
    0x5060a0906050f1201060801030618170a050c01110301030210050f04050f130509011b0e060a1815020a031b02150906040b0706020c070501080103030206040605220c0e01 74
    0x4540039072041c070010310f100f80180b0000305908603400c0b6982c0207202c0d550f9400748a5041d4104241125818a1003580a0603200c580d1000220005050551046100525074403000c112100765903d200d0000c406031a540b0700652984802c24450285051b07a00076512a401e64190303038400e69051044080714020600107100810845c1740c0340362841d100301b8014010512802200d80404156903050701d0f9141a651149107400e0450303000700c8041d404866500e880f06034208050081159481007450031810404159204401c1c00402d055001c0100380c41850319840c3c48a0000c000e403a143d00ca1421070004144080300341c12040606040050941c00904900c251a0300c10a42000d0740c1c00800c4e0140c10401c00c0c80001240d2078140090400540a0000507030f8501c00d84800505103055a008541802000001030003c6039002a202d607016030311000014007a00c40010400b011018031030003003c6040c0c20142c1000b0021a40c002c00c04840d60400444502c1e46c80d00508092410034503422031003d0081b0941d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 45369995 1250 45368745 45368747
    0x7060516060608010f050f0c09130c05190c05010531020406180204050906030f0a060209010c121805010302090102030a180902130f0504110406030c0e030607020c03060105060a0906 79
    0x1203000c100d0311034100041c45503580c0314403e00b91002c03206441a0130b5941d40c00c0000c0004840b950707560250b58840028600604140092480c4505400007020305035641c192030040c5002d041281c04140724000c0d1943c0e910040c0400404001c8883c80441d50365080401184007410700886004403055004401e0424481c0e0688110035003d80b000203992203501c034100052402014100506a107000c18005a90340381814180110410040d141501991100c40400d003101d0020a905451582c0800c0160380c80c02d41c0c0f0b004903800d0001c86000f07010b410307022510080c420340100e6020006c050440c014042195200015002c0b0300401300c0490242c2c000300000550148200712116a0185180160701e4441d1130320038420890304040c0c03003280c03420201134040c4400001e51041a0040038119400d000702241d546011002d80503a10810f0309140d140e58450b521240030303941c051804600a801c582c1540360881c4002c0d600e01e6003030b00e01c5002e03004010021850342084000c03034885a046444105446d403030084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 45371245 1250 45369995 45370027
    0xf1208060901120201030617250605120c09090109020d0c0c11010f02010608010e0102120109050601050d021c0905100e15010b0f0d0c02030301060314150907020c040906150503070605 80
    0x6004ca0405548443c0800d00c03041d02c9400c0180083c0d0b1000820110000d00305824195800651003d0b0342c0100300010081ea99121040302e12180740000310381403544416440721420701030b05000c207911146410000c600782c2c3e115400342ca0a0003441707200388041701c0340d00b031300303490600055001070071000f02c203091070340554001c5081d2610f40c034082c0700004285941710300e107a0854888540c01c0c01640d40000300354001d141c000c80004c3c05021914020030850a210b800a00b142c40f8420303a24901d40c0d00860080c0c0b19030030b040c1c8000181e88044106101c00c107000e01d0f00070b0302c030100d81101c44202d6150403440c00810100182100380e1a5504580c10301d0399007030280c54131103508415020309040d4030801c07a00e5042c90707507402418001000e540003551a941041c102405452200303035001c0c0e0503801b2204101c0000c0d1030340c19806420070285c072510b400b078840b498200d04003002504c2141d000750500716040100141c0740e0101c140700c0028191440030b0707503e80c42090780340c0d14140f00b20000240c0034050b105414001c41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 45372495 1250 45371245 45371279
    0xc0207091a03011a010206010609181a0d230307030c14070513020712031b18051c0b060301020c0d030b13050108100c0504080703080d14040f1208060901 67
    0x1401c0051914100c03030000342580c40180c000701540a048102c2e08855804101c07a80c09810030b400e05050f12410003590b811420389070f00300b21950a88071142e10400e00101c2c0c140b0b1401700c6000e0b0519000d10340c0303401c2910000b1703890024032401003101620700300f5458000c000d1b030300d00c154580c1d14440d10f4070860b2030f01044480c0100b6000390601030034074002003aaa685103150b10080c0000c0340980c80302a1030400d10100d40d0040c00400a050801141c030701000b051400840140d091030811020384038131241c4c901015001034016a030081c000180c03400346858006003c94005201c1c8101348040d80d01c08003810700381d001d0b501c21008a80e1200d2999200240650440001e815016210401c00d4034003001c44c0c4161007003079006e07109c1504131000b1110000c900d409100419842e50800d145001d25000d2400e64544091101030031460b004200709032074540b50741003801d92089859502d0240c0c2002e0800c044d03c2c5a07103190888a00b03c4042e01584001c0c0a44031262282c08020208034560380381506582d0582040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 45373745 1250 45372495 45372521
    0x60e04050604021204120905030703080304080a030e0708030408070801060f1502030f0a0e0414010b030c0c1903030605090f060306041101021f0c0e060f03060607020d050105010b1c0c020709 83
    0x902403032001d515081c401512507806414217a000c43d1b400c40019041c45c83d1034118601a0f08250b5080c004560341c801260340041e030000c0c1c11603841d1240403085000b0148104071580c6401703480400500160000060010b850003103040d41c0c10156100701c800d00b00c584500c5640d1050001c0f140130030682103260059080c03d04540141d0303107403480e4809610342d150300001c040c4000c1808001980d45505080c850003028003c034410404c22541441150500c501004002607070050002882401000e014000c0e280006140340204203c5c1d0010318000d00903200300e015003809071080c4c000185001c003071603083e1030040300007401922194441e03440d0300270380c1300e0300b40461410f501c01c100b60803030018180040000c5180c5429000a242d160402006107440a01001d09101c0c007414003d12010450403422640c000c2d0741220a15658030007480490900201180c1c00b4000d54a03020001030700c12074400050002c2c0c101c2d00031070400368210803103000417185207569007c016030045070140f200000d9035105101007503036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 45374995 1250 45373745 45373747
    0x50c010c03062d1208040f061b080d0e07030804080118030c03030c03091a060103050a0b060336060a06050607033207150e030405100c0c03060e03090f0406060e0405060402 75
    0x143d0100e003e41e030404c2d60045502100000c2d04101003001e040094010384a06d280008100030944d0002081c102d080d44041e0100324005111510102e003680300d084c8022400c816140c68075520300b03041d401e1703030800d00c203008855003012034400d00604142d4203003001d16415111226688200c0e10100c004102d000c200300c007416640d80c44280400d24171100890f50010704145c0c08000d280c801d000405072032018184602035810b001181040b53b803000140ca90016045400c4064824040e0111418600014010320280040d20060b4011903005c41d14500c2030793304c0303001072001c0d40c0d60b0300504c90340c2d109140c1c0150000d085000d1000102c1a03000a0010802c0c044014101c90002005207459a0307205c10821120300b001050091211041800384000c650b2040028500b040e26200c046450014201805c00c1001544c2194000f0000000b41c02001b650700b245c010030044000290b0140d0b280c0c401c2407417511540181604095501e001d0185501f030321003940d61940b401901e801400060b2030080c0c49070303074482c3d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 45376245 1250 45374995 45374999
    0x11030904051302010e030105010501050d020304020303041508010609060206070804060203060316120506152b050102070605010e09060103030509060a090e091e160e06060702090106050c010c03062d 86
    0x20300c074050301e40a07260540100c110160940300140403c0e410504290181c0d04000040000d680c100050302e002410102015940340e441d480003c3c00c5105076046070f0445081c2e501742d00d4105500000c014145c1d41c0301e460781040942c40366801d80c0d840e0021114800000d4800740011700046c500c0c4c001c0c540100d8042c08440e0048145d070900c030700c1c0da85c3c2900100c5001c2a15034801092003800c10071590421034035081c4041d102c440502160481042025080180cbe91020344030742148424105a2042c5803c00001c54588401d4138041000c1d100038402c003030f1519450008160589008100b43c3c2c122641621000c0c62714015400b8490250402200c100500c8001100010a002c11003e018401c9505001803c1c03402500100c1000421000c1c03408070700c0f544040c03610f808030900001c0d11015030702c0a1703d0140003942c4074800900c1034814a4802500030503014000645c554105002d40300c048640070007407200d881580e400318100c40140c46640c0404800200001c4040180300152120390020000c070180e441e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 45377495 1250 45376245 45376249
    0x90d05010b1005031603050412050703051c1505060316110a150f0608070e0402010309080906070b01030203010b011b0b060607080a020a0501060906080312060303040f0909020406080c01050a110309 86
    0x40c5184010b00800c0e0000200b211180482c2c0488000c6030f1035007400c00c51130626442c0c400c3c16005e41074152040c0000002c81d139003498091801d9a02068400060100301c1c2100c40d00f400c0545400c0c52680c0380c036000d064011400d40f0f881c0040d80e2040c050340d8031000340d601324964119030000b600c0204850360302130b150741e00d4003190790440f8403e419154401d0100b502c1042402c2c0c032040b11559480850140c2202c0e80c28482c0003083c2c09280d820030b4091070082004034260420740321521568103201d9008200244200c100b1030786d601c220b81242e00031002000600300000055a600d0342c1c145032000b000c1500b501d10000203010b800003035003041c0060620303800c0040503a01d8003080c0d03000c81488405640008010010480b0034014000a4103188506000350751904c803c2c95568010011100d00d510864000a007554404000741d81c0140510205a52555a5854010000e080c44101a4000e84c02d0110200308800c0010309040703010b1041c4d6805140000540d0110b8418415801c4003800d400208032000b00303a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 45378745 1250 45377495 45377509
    0x60a0201050603071e030b07051903050f07030e0a0f140a200a0b0306010318120504090e030903060103120c0215030f1503061611010c0e03070603020f090d05010b 71
    0x1000164000080074105082010700d02210b5600149028119985082c2c2e4222203401d00c500320703680101c1503e15916182015101c0380607041c54255032980b9800341d040c2042d456080940a00640e200e1034070380d45c41c0c048044081d5002c03108000d8050380104000302c0010110354104207603074003c506801c84410a607400a060080c4844151242d030b80030300418642c465840707211140080c1c21240944814a400c15003121404020f082030306155aa6040b0900c41c1050020808440d80c040c240b02640076170158040c005421501400002500d00802d000c00540c0000c201e4003c0c4800030014103e40c1c3ca5503407440a0615000210400c1141840041005842d0301400403418213540d1135140c0c0b24034001810380b905d20300003041409682c15810400419071408241d5a8002c8807100700a40c07280508030703060f1414000c8800c44602c42d840c0504028415074060175008160800324291011541c1e1968120180e014284c22407041000c00c101c00280f62414003c2c4001c0103101c0c50010603d000880009440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 45379995 1250 45378745 45378757
    0x50a020a0f06060302030601061107030f021207060f0f090b121909060b09070512040b0a11040b0301050f0d080d090f02060a1206050d0308060409050c0d060b04050f2404020906 77
    0xc965243c0c40280114078040c015207004d0801890000600341d200805039a0b2203141348005041d00303030b40d8103c1c441035403144018060644102011210810381d40c080003001003446603510400106940351426200b840b032080c140443c0d001c2c001181c1464007001c11003103501d001400d0414039000403104242155150700564900602840d00016185034100074403082600c01003100e41007200800c140300f50494030803116900300d900000141e00568030520003030024030b6291801c0313900d401c0109000502a55080003181a140e094640d1000394a401040c40014861020700038280241405200c1c404881c03a40039110042c00741e500000300c0c44994003c02d4003036000c0d45030300b0f0000b2180b400103041c000340c601a9600800003507600140601d000d0b20020840e81d4082d00c218403450702c504003031003840070402ca41d000f40080208903056242d4540380c144010240d001400b8021400c000009000241c0350560900c1080007265031281c101e01800101070494110044a500c00d50a101a034450b40f5a2005420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 45381245 1250 45379995 45380003
    0xa0303090504060e0c0d0509030c01060f05030c220902060d060e0406050624090f0307080f01060608060d020f04060812070c08071a030a0e060a0c0809010507050a050a020a0f 76
    0xa9407030401e000d020641e11550040d400303042c1c000c0148090b810b07010049800681c4030480005490f100c0c69202c9045224031400c81025609055003c50034854141842045510481c11201121480414400c40c3c01c03403443c40c5290320100c0d80c0100d103211208c0d00300c9500030384018032030b034034144000f40d003081283c1c031070740006907001034030810002041403d200d1540c1140c800c0b10780c0b0040c42c00440c581e00071449000034035528014041250358072a200d5058250210710024241c480c0103032074904140d0785841e0040000115820004001803190242b5111801060007400600c107140c8a6001c0c400d00205d40501c49400959614001404540070320400c3c64100211006550381d49180c1049030401c801ca401845240d00180d00400c40703800315412056542c480e81a9031a100c0c0da0f40c081d0600285201c90740002680112020040b2148055009580044007078030f401680d13031149502036007203c2c811034100f0082001080007810048c0210702804203000213104607142103a260b45c402d00e2000c03d086040f1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 45382495 1250 45381245 45381257
    0x1f081005130b0f01030603050d0e0f040f0e0d0f0c081b0f030c100b0303090d0c08100902090f1303050d060807080312130804140a030503070b10060e0306010b030c0403020a0303 77
    0x41c080d02e003c00840c0604074007464107000762800d58552035180c000a40b501c405008290b02984001d44611801c400341c170000a008000680036090008041c00421030000c3c1c10307000d4215005249070103040c40f0b04030814547c1c2c44004066040c2d8030004164801803007564032440503040c0600b1850104000f00101080b000a50349905000206610b0051100d0803503e0036400c061000b07801d5103000040e20407002084504040174015400c001a04402c03903040700e0300502445050080300714881e04106040c46c401e6400c88526900c501558809090650f14128180d80800c220703004244188080c2620605091002a915544403c1e2919000b2507074480515030b0400b04010081e94114001a0303823115040d16925130f98500e0355904455442540121441e1040b00b0740b40c4a4191580f4448002465000040325030313a0746541000301034100225611800c5015241000c01c010b4400d2100d41c10540024008008990806100030029000104041c950700c50038000040503030340d24403d00c0c2c02140651030301c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 45383745 1250 45382495 45382511
    0x2609041b02060901020406080f0402011106100501120507080f0c090307030c0315050c07031409040204090b0301290405041e0b0901140c0a08040c03170d06051f08100513 74
    0x10b41042d000820360100d69105200070440c0d582c00940b940d41c000a41d1665940c6907540f4070050302d0318000c007001704c4070340e00c5480c04002e406401c0130800c0007521004d032201800b00c1c03080781181e01500e00403100b100000c1c084801191194a044501d1070b0080c00d1040d000d070400d9424000300340340c07500319130080c1c1e4a891500d1b810000e20814500360340d90030984030300034880361501000c2c04420b4070401100404016134200302ca020b0034240c2c000d60724000c01c01003042d5529a82d445508019048100a4074425482d00000c1040264a020150b26815842d00c450702d00483e0ba6041000406000304240c0f01c005100004042c001001d007440041076102d000a540039080c0125210300711003040500154502c11042817190740c4401c50165002d100b107901d04003642d070381d0320718084104522540c8003c20040c169020380d1141300700d4401421107801e1000c41005200c0e516010844620049949011440800380641401310710807a4200da000c0040340000d04001d99803c00709030b4038485080008000c50340d0300c000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 45384995 1250 45383745 45383747
    0x40201121a040e0f06040f06020c070b030114010309050c010302070c0b0a0206090f0106080a0b0702100603110f01090317130305100c030c020c13180501141f032609041b 74
    0x280301020180100181000f814000c103040d1780c2e0002510281500340c540344c204d4200140d80e0110343c459007408040d280f415680b0240d0701001d41003070160b41c1c5040040c2414400c0ca5102e1710500d40241e410600070004800e40c40c005500a5100c50320503184056400b00200d14589401c0050040440035070040c0307114608400c002e410202c010104410390307410700504018003000001d407820466042080c42599441d07002060b858240b150003001c266601f080000000d110301214120141c200c107948802c1b1407545603004503014482400001c1c09104500706140646038040068000340d00e2020007115040d4494481d2441d2886843c040c0c0c44003602c607002d01c1000c0e58907000d081c40300c41240c0024580d080c2160f000030009a0f8440c049100715170789404805e04207400421001c10103811000030045540210010640d50400f107525200d0112881c40764900703106500842c0003101c3c0c02490607410a00c1002e5100d502c44a424800c64260707000303100074445540d0790300ca10144031000e054200c220190003c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 45386245 1250 45384995 45385001
    0x30f0d0501080304030b0703020a0509190302040f15090e1f06051504060e040e01150308190801030305070b040305040504020c24071d03030415170a0204060c0b040201121a04 76
    0x220b02d429810034042000040c0340310301c0d4160016a1810096100c4948441c01c464900505c411035504c188150900a0052003500c03842d4152030003501c06200040b56051801c0540f10005880503010341e00c2e90003040141d10039409610201c840300d0070703112000d11445000e000707100340500c1c06010b141d442400300102c5c90301b0b000000e0403003003a22416041c94508070380a07002140c0441c91501858603480f500d032040d002075019a21003907000d00130540b8591281001e24298210b8102e00e082841c030040014100c9000b850198100c0758150b071071a00c0e042055440c0d0304644c501030b1084007801801d20010456503640d0014150314170b0030900030110401e0010b00c4920415545c0c0c42d09212804050030b0000c080c1d4040d922151070041d50004c1180c800c90a00400d16512071a07000006004090710386003c8030341c3c4500700c00018001184000340c50340710b0001c45012481b0b00e11030480440e8542081c14002005224040d40c4103005040414030780304402d07681c8051392010b50103a04c01c0194120800b48500e0188 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 45387495 1250 45386245 45386249
    0xf030307180302060703031d0717010509071a070c0e1e06100503061017040305040611030301120b060102010e07060e030706090f0509061906170c1c0b03030705030f0d0501 75
    0x19401e40541407860300814210311800300042c040503180c0c2403260050b0f11200c1c0e5100c3e461000401c4070103c580e10b2170385208128058902c00301c00d509040104502c90000200310041e10030000b07030601086540400d64410b9880070074111000040c4c22030028005082a101522882c206841620070181d8052020b984502c001c20313140c0701e8080410300d140441e5000e03081d00e5000c4026205d48032000c5038402c0a60380d129a00300150030a03400c01c01000b0406074820045c0080311401c3c0c503010135142d1200e00180c1c49002c00d00480c15020640c403842c00110382580c905a41014040c0000078600315805c0e43c00303040c40d5103034201e030010880d0350b090713118682001c01140c001040349107005c10040707061881800c0e8400075413191030b20440000010039065541c07042e81c000140318800c200700b00c0740d41d00d10002e0300d03803505511455100682d220015542484440072100501d80c078980c0c0342c100554440341d0600500c0350008950301440300b0b11103a400107004100034030482141804003a11407003810f1204081c2c1c1c1c016 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 45388745 1250 45387495 45387527
    0x30501060513141302031f0b1c020304020109180603030e0303040b1b2b0905010f0804030f090902070501060e0c090102100b150307110d08060a050d0609050f030307 72
    0x81050880071001158188241c030004060400882d4000c00020b011300512440452181d00c00028003810b0480c000f010024003070887c1c0b1100f070036541e03290491b00c02d00500454044040d11801e0005000400780c0c0103683c4144141016800240c07245c913101120b100c45180f00c085259200000d10506402c076401e40c0300104120011464142000c49402c1e00d40640c1c102d03400000d000046414901c00c060081c0200e101051142020103000c0031003501c00c03c410207210344089000d003a40481d03554030900c1c1c3c0c0342030303042c1e00d0b00d51000c41e44856508035032030a42c128950040044c1c0b240046034540940c0000c00d0128041e00010030030b1801d160700c00c0070703141c00641400c0703100f000ac009141c0700e82d070049031900b0341540a10380011550b0b00300c80411404c0c945040c461400540000410403540d07000741128110702d204508560540082841c1a6843e0300c3c20f9031080e03413003168010308000520701003491030140e6101c0c0340d0102d040155a40d0b150b2901040d031410908940005c8100b03d1303401e901c80c031300744180b00ca0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 45389995 1250 45388745 45388747
    0x20d1d0105070308090c040905070f060305010e0105060912010c02030703170103051e070302130f05060a0e011a0d0204030c0806130c060302030c1303051b060c1009020a09050f070305010605 83
    0x969001a100e442100e00080600a50000040714050203005040a244014005014403a19481c065031a088603001d00030403a01c035000c000c074505100e440b40ea030503217a440514610913400c2608005803600b00c0100d05510001300744034003400b141c084c01503514203100c6400558403201c8500d03010301840304d0400030191aa01e00001000420000a14948030440301d110b4482441048031090341000d04503040a0340040005500a00710100c950058203607030700d13804040013207844a01c20090341c0301e01031084c4418414142d0062144141c5808401c400302100c221041ca0002c848814000781d030001c1d0320640d101810840c0c01c0050603c1400429131050985000031240940c60782c800d0040d00b06801140200b560120008400a000504480410754040e0586c0c0300160380b07107001c564510044e0006130400600e4030500c8405d040030401d036090845400c014010000b6000c0c1e501d802030200c5541640d00013054600000c14101e544203960081d03512000d0f00e0390700d2521490280550b04180c0c001010000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 45391245 1250 45389995 45390047
    0xe07090f150e1603090b0f090f0d080403090501020606030a03050309150406060f0b0307051812060a0b0a080c0109030605060402070804090902010e09060d0f0602130e04060c0e3d020d 80
    0x11b0701c444110390100e03104142800e10f440e003070070061404030547c21940071440f45a04840006400001407845a8881d0b505d1014141c0c452004903110f82d07080c0c41c090b4240d4880d41050000030f00800c0035550092000f81142c42c0c0307003080102c0d107025030741c151429601c06030b44943c04e00c4010040203101024004105540340380d0704280034000c10b02d00c07400084400c054150040100c0e507030f40302000820200a22402c84000341007907502c9100408420441b18170585031608002109000421214103030b16050b1290b00c40ca07855a1135000c09880010b00065100d5420003a5a000443c0341002c0d0029080081c00010f031880140b001400241d407548030940700d51035800c00c02900d56100f042c1900c2013a40803403101905000c0c2d181c420040c1c000e03d820315400c80e6a401010545e0130700c1441c003e1055002c0c40c02400791000d9000b00303840c03811104a20030740080d04d0726400d00e440ba135003c001301207401c20103c1c07440d101c207a5800c2821000d0300007844c00005810000c0b4040b00356a20140784038a0300440080303052288 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 45392495 1250 45391245 45391253
    0xf0606060801060c060506030703020d050f1608150603010b041b020601060503040b06100c020306090a020109050405070e01110f061003061406031b01021005010305150702010e07090f150e160309 85
    0xa078101c0300100301710b482c2c400081d010b480c20701c64003009650290110100d6a0030789407040d22100c121010010903c1f600d03440c1007000c0a405c400d8400c60314a0000f0303206c0c034401c001c200900180010400d40c0c056488110404060f122807142100d034441445408000c1c5943c107800900b0a14180c0c08501000418014000410744203100b0366000307201110307034010848112a0645000e0765900020354180a03030360400442500200314903180b075200340d858001060325a002c1208840041e1880350014240c40042012540100b820258503020b03041110402c440814040d072800b00c1c2240d410192034201002003042240341e0003555200d014011118601d8038203100441e81d1041010043d5100340c00070280c44c2002d034020f0100414000f1007507814041583c4074108030703a903121050b40241c2ca0303051503400947c5d01441032045d800300952031400b50400c50718100004016080d981d90402105a0740d0a120401d255072003815001070145500ca04014500344200400f12044240c2104c14982801a914001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 45393745 1250 45392495 45392507
    0x1508100504051e010e01050112050c0405040504151109040506060a0f031109090109020901140304050607051315020d110f060103151b0203030f1b0a08040303180f060606080106 77
    0x964000c1e600007460f80ea03a0490b094640202200040d02183e0640000c6145400c403100a8181d481c285ca80c0c034002c3c1c40c02c200c5102110801c855071041410103000510032454070382c03c6150400e00441d01c692420740418465811228104c0e031020f6110000a141c1c00325007428011140d0280c4c0c01c540841c01d0240d40c04002d40003d00a407605410940d40d04030f10f000040c40c17602034442110002d80303245039640e1901d441c0c100940c019048a4007203001e0701c0300d00e0b8100125000300da00c5158000302400b01354450510613a01508150019102062075200200703190710030110109842036168024801040a1400a0315041811603100c2564019420f08001e075240091114112a4082d204002041c1c6080d0040000d007140c82100d134850000481000d14154000082e42c081c50b41da0b00b10580725200c5162092585802e494120103000301440500c5c0c0c01c0d80580c0800d81c0c402e01074100428007a642005031441c02c214000300322407901c0708400303041c1071080b144640c07805005142031941103941404405080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 45394995 1250 45393745 45393749
    0xf030807060b042003040c0504181707060e0a02090612120c030f16031413030f0c030b09070305061b04030f050304150305041101020d0e01050705121201150810 70
    0x90a920b4060382d000c0d5841d241c2c880742d0407002c0c1000840e0200c2a040012200760300a44007911622488071020409250600c140f41c06445003030400403101529946640c039441941e05c09001c03900042c02100003060701ca00072210422120006881451054410400e41d07090242841e400b030303452064040a422400100700d012050f041e03d10548400110400e41d00c0c40c4140040313480c0d0000007042d0100001c01c410f00854100c4e1082d00c544c104500320381803480c000d025400f07540c0003440000c2d07401c2002c910540c980e0041c40d030088000001359a241d231100c1c0902441515000746690000a04109111050004640181e088080030700b025085030001c40c101c0c011070101508081d12205840200f05041040300c00170000140d440b480c02d2042d5034094000c100c129420703a8000440407810748070b0f46c408100c0f070ba16143c107034071000e079005d41140c0111120382143e007085415100b6500d034440083d0040b005001001d068140c0701040e9070518100c034000d401400004810b004802c421700c42682c2500a504007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 45396245 1250 45394995 45395003
    0xe0102100b06070606030528120e13060803030117011b0503060307180f060503030310092301090504020a0503121603140a0f1b020607020402070303091505010504060f030807 76
    0x14650450400034085201c3c0c4000180481d1505400000304100401c60042d070342140c140d0600755401d0340d46403151650200e00010719549881d80030240035401009a5100d0300c5000c0d0038500402c40b075403801d200300c4846401522451b8004070041010b407508580c2e808507001808000d01c50340110b5000f40041030522000001400f0012000589a0b1002c1000348003c08840340384003010f403905442000101201c5008031f10040c101200070030b05050010849009200d00341042002a150140305030042c1b0b000c41c00c0c0406514048004808d250074441e81c28060240100c00080c0d90505104106e100c000940c0840d010380c21407448800780704071120540701c070b0540e00c43c0480401015031070101c441000401c060011590081802c4400c190700c1510020341c82c034a501d80103041c11403a512460340c0c00c8002c0000758002d00402c180d00040c1015005011468801d081c0480d007074a8a56541d101701d20740400d2104080c1d07070307500100210320b418024480105040603200300c9460958841c403d0b81e1196140c090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 45397495 1250 45396245 45396251
    0x60105090a090203040206130303030b0108070504030308070f11010c1214010506030109020304081b0c030f0303090706180801050c030906220303090224070c0803040506040e2a0304020306070e010210 87
    0x2a0547d25104120303103d02c0108860300c103400381c4926000e0300911a40e581240040d14840001788103030b0081c012181600e4041c0c0383c504071642c4110040741c1c2a0035076040d4004000b130801c5400050700003405030750900a035949850384811a190300ca00c080b81e8900c0c407406080e080c080b00410040c0c440c2000c80e41991011100075175281c0e42c9003442c246510602d49400a003140542c0452101c00000c034810b282d51504900b80c0b200c0b410410f0240b130740d1740030503a811f0010782c03c804820804640100c0d07500614200900c211402e081d61904440d0031154201e60b901c180c00780010800201c507a0910495501400e00e20346829400510010a5144c1a2610006085c103990740701c40410b6503540044040482c4011550180d00d031488201105103811140003220980006100420300304008008c0c2c0f010f86101800103030409140801d018190800503065002002025132001180c6000c1c0300481e41d51984491015135074101441814030b4400700500307000c00c01c603443e109180180e034049199400c149003c2008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 45398745 1250 45397495 45397501
    0x8040305040305030409021b06160f03090501050108061b03220609050a08190e09070818031603140a080103060c0e03030d050907060503090303010902030c210f060105090a090203 78
    0x2510385219a410141544c03001040000303044015400410b500c65140500f294101025411702d556400b064485941c90a0021502c0f2203081c814801610003585515001c9220041925041c0c00c64201380c000d81250381008003001640b042c059014043e010040d01c1c914503602e04a40b07036030622041a2208904081e10100d0729040c002c1980101c42040d0704036040d180c0028052804405551041802128851300703124411107990190b40d0074811100e01a00c08052540c3e250303000c13261002c00a003045190140384450746284a0100082e00751350b102022525642c0e44d65003009441c03441d00000504807a81e080021411481d40895224110f9511500128a0031012002510150324054241d07030075100c0070840150300009074200501035144e11069844184e1500300403121480100c80080045c0d000b040100f208106541c0255441654641d086043c0140310031550f2100000c8000018600c100c08203018080c1107403103503550003e0003424003034174045150340816581c441d148504000701e5408400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 45399995 1250 45398745 45398747
    0x80604060306050702060103110301090320160b04030b1b07060f020904020a05220b1605010902060301080a0303060801020c0c0d0809040203090d02070501030b01200a0804060905012c01080403 84
    0x15001450b444031042c801807038121402940c0d4002484140c6410307004040c482d415041c10312542e0fa280d0b4050303441c50940060351218003001080148020401d22610925000003c85550070002511f1901c20242d505da1541c103041d2840032010340814054404916202c2104200c5030490314456480b40380450056035005011000740a814000d41d0041c9c00022210b0802d41d010b4007d285141d107411420b04400280741e098100b048160140500021040100300351a041c4500104483c038070410000c200c0350515404240b1a030802c2c0c0c005401c0f64440d007580c10070141c15015200c0905080c1d4000c600380803468403040c0e41c0c1c210084120303001c0ca40302c18100c802c0c0102e0724202c0786425030141c0250366170b041041610355928031151040006000d1102c000c9203a40c4170f03019402401c04142d65010344640840c0041741c404509070300c80500341c0324026240000039561005400104540e48074100c3d0703545000c0000d03000035400705640707446409040305901034406e6000e00a038103807000e182c101c001e542d803460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 45401245 1250 45399995 45400001
    0x8060303031e18070609050411070210080907210201080610020d030c02100e031b010b06090402090607051b041103040b0406020f07050a0602030a0b190504050a0b0409050a020907021b01080604 84
    0x8000d204e0092034001716186402042c0c00c41195000e84081025600c10030000e42e0501039003200a60080c01040e141003213078819403185401280d00c0c000d440c00c4c00d035a0500c5581c8810455000c0f0091042c0d02c00303010075582c0000340198051801d4421140e08a22040000d440d400c00f40c006800f0305d90f0b550804843c2d82c1c0f0030081a480d542c64805d0811401000019459490f001102c0f118000448520003800c4520306002c0c071280c001024000d00d040c21240810000030303400655000c2c3d0051018801900483e40401511035402c0d95100306160300880c100c2440190b81c502c99841204410070014040000c0880c0180703544142c114600585485400696500c1842251000340c04c0b4800e4012250920805500442c0036641e00740c8100041c3c42e900040c000c06c7d50521944000382c10310040d007041942400c2e0013407603101e012a94000b5241050000281c1103812040c819151640404038810440c24011001070700201c1600087c102101e031510710389001c69400051a041200408c0400d10585442d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 45402495 1250 45401245 45401281
    0x302031905040506010302101b08070303020c060a05100b04030b041401090803010906060e040b0f01030507200c1011030406030b03030424030b04020f041a04120c0608060303031e 78
    0x8405001505103070403c43e5a5103001e0006920030841c8000e80600c1358055607484191000030b40030001d9032900707901c4028141c0c026070000d405054003048040107440c0300344101c912550081d00c0009550030405038500c81e603a450340004604100400007880840e1030030b040c00d5800303548001c9107254510054465405045420001040801c01100214403002a47c014809440269580c01401d8140b00c1c108010f43d042d0106c0c480e0440320048140300d0079440390300f00a9104449080111a180d40c0048881000f540e13440020100d0700402d080300103d00e0b0520f40c0b80705069452030107200318609440c0090303ea200741c1c8107000074036170766090b910540d8509200b900c0040149001d00103490041e12800303039180b10061004000a403030021601401c0c41c1510030740b011040d28051041c205401e014880c01140141642a0b6802c00c080c080003030481c00d40c05503018600d1186041c080b88920305400505850000b0704000d100350001d004000045d104621039190784140e040158079075403030365103440c21919003403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 45403745 1250 45402495 45402541
    0x30309040e0d0815090106390212010c08010b0307030905060c0306040b0a03170a05130603021201120807020603040f0605010e090705010207030b01270513020a0b0304030e01030203 79
    0x3075520070088011030307a040320060703e494a440c0f40d0f440c411540f1850000450141d4010451001840780c94454044802e6540c1c1c0044c80045050656641c40003078008100e4481805021200c48021420088541e091040e045c000070b006c001003503d809800c1e1081401803d0344c2c1e143c04000103281d1031090300300705442500700c415140350341005076036a015940202d46050056040031140002802c141e4500e100700c80d000010101048002c0c0c180d074503591300060400b02000400c0c40342c10385400d01c2070310300c40080c079441e10f006079190300042d4284883c640581c0058400d403061054480420b00050407a240d540d070498040382e43c1c0d9164901880c0503e003100e80600700615000001c1a520384a050950107440300004440120740e503040126980c031210302004102c250f001004201014104010201c42106220020048006110b001045a004940c01d640c41c0c031100e19902c1c15803c1c58495440a091140101c41c95450300391400b0780b05481c410b50550406034004000380129202c00e0700520000d0320 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 45404995 1250 45403745 45403751
    0x9060406180812040c050909060c0a0201060f151b0c03031809090606030302060c071e02060c0f070e01050a0b0909042d05060a090b041202100501121214120603030904 73
    0x403903040c4500960f400c8030704640d41c0b1a003c002140e50b181580c42130b4424000c55005008690b03507464003040503000300300c1e560309640d00c83d440858041e00440155024041a0f0014038086161300001042421421036101c9510400010100420f41120801c0181c94042c1001102d82d24040c0490700f840406a00000d039180c1b07440880310411140b82c0004040368060b030b007103070f82c151a2080788072158401c0c0140102141078a025816010b444800494035060004003580d0410f80890003090074041007404116541d00558414001d28092074011405064241c41d80c500c0e41d810035a10407030310f10540641600c1080004000340800c841100301c0309070300c0b02440b8110600750761001c2050ba100e07400b80f021240d80c0541400106203000c0c0e80705500000d6048501b02c401a11192540350107124950300d0b00045004142d104a1900c034a4064070b0f008140c2228094108185410540c68036604510071200f0024500d1040341800c40c1202a9110383d0392130810301c0c000f07031a0300c1c001074a188a45108035412a003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 45406245 1250 45404995 45405007
    0xa05090904060c1404050a090e0106050402030c04150e1e22020d110906040515070503040f080606040507080115090512060105090a0e0712060e070308091002010203090604061808 78
    0x101e542040a603c0240c0d101d0142030584031100d10458043c038082c0b01d400007042c0f1020811851940c01043c028414040001107541d1560701141c247da000701c945164814000600300454202e0a115400214603840e0030b507501850440000c2a460082003110510341c881d03408411a690b600a200117240c241d0f2038003004402440f1104000b0b0b400032440d0341200e82c50600059001101c5904a80c01090000e080350b1405007060108208c2d002c03030101a4610b01810703c90b140005500308000c0c0098484500704150f40342c0740507502da10f8404000c000320b020707034245801c0c00440d540100015042d00c121000028207030200e02e074201e801c0c11280d401b080e4440000204030600070300100b0860305031601600c40184070390311500c0c444203940e05481090655840410100710001e0407804e1860b140380314030404210052418140c61a200b002e800544023980d000401c2c443e40c1c5001c0035140c50070f00890000b54103601c3c20300492900e8040040024001d0350b10f807000e16122121038403c0020b0350313a002d4009911a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 45407495 1250 45406245 45406253
    0x70f2a03090611060408091504030c08010204090606020309090a050601110601090e060711030f0304020109090203040b0f06041a0f0a0305060f0108070609050f220207050f060a050c0706020a05090904 87
    0xc0400e215140110340402c3c2c05200780140400d00e2446143c20814040c5408104800d00c41c1e0052420b1803500f20f80b005010100001b100144680024800d02c8000768a0703c1c01d061440d022102d5692044040d0741c010001500c164840d041c0c41584176007120340001d03413941c84200503508502044485212800344100115a4032810340c40f10008c200400220307803040d503d4000594026101c01d94211059209001c6851501081c0e030040d580300f0f1061500400302692030001c0000d0380c00039582114100c00c2a0b0411086c0c0c41000c0000340e010390211010301c5016907104084914001a58046025224903d52a05151070780500d00e00215403200440b00c107403402041580c2e90038004c3c05841020301603030400040561091810400340c5000508001c1940141410030034142020422081c003c2402c03440041659040d2018248803400340025100040c403c911013400e00300014410071900349018148401c00d100c90081c1c0c0c500c2e6a00900043e030361a03603035500351418001c803120983d00c8588802000208 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 45408745 1250 45407495 45407507
    0x618040e1905010e1b03030d05061c03030b0112020310060302070f0516080c030d1b050f0609030a0e090103030c0b0a1404030c05101116060609230f070f2a03 69
    0x1120030706054444000c45c50240710309800c0309000702e5505603c20310040c401018145d01c25a00507400400c02d00b150004d40d019a041c41106103410750109954280030300c01540c01104500c0300c0619158210319602d0b0140400200c982d81d40506010941d0100364042044100f9203900211500582240e8095008641d89000c00f50503005101c410300544112680501300010f02c00e2050201c4c2d11500c1034565240d209403c3c1c0412481c003510701784900524100b40c1c1c00c00384546409800a10b025555501d140e9001030581d4580301c05140c0a010140e00400100e54804210351145500000d941c0340794440c0e0001001414403c003d82040c4481541800105174010010550041c03180081d10303200658a91110225400c030f02000c4100d04040042408030b80100610800d554402e00000414580740c520150883c1e8030b411101400c40c1d140c0f40c041c101c241c81496599404888140002464503051000528803042e940d402c605000000104208004074410140e003010707032500001135101c044d0708000f400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 45409995 1250 45408745 45408761
    0x320070312020901050702300606010905150d0c0c05030a0c06050702060402010e0f0a18020901030b2b0609240b030703081603090506030a060807050618040e190501 72
    0x1c5a004074032000c008080d802910800710058460b203040080b960240314100100c0d000c0104102080b4401c0303807940117071b081d80b0a90301c1d030034100a2040e440e03c00000340590a2913003005101e101042a50503c0c801d00604981c1301d80e0444101141301c1c0c08c503c0042e00c000c2c2e5500001011408081880c5d4445988210001d1200e07005000603c180e40740c0c8a4140d0310b5280540f400f900141c80e025a000c0e0f1030a001d005501c3c2c0e0a009010340e1590342d560b03548507030750001d445c100100081c0c000844055a6901d4010108411070071142c04280600185041d8201190080c20b4245680c1403108001445642c5c0e0010400d01c0c0c02c00484c50a494904040c0050098411344104030545425005651410005101d6050740e0340881d0791031034605000c10b00740d0032107030210040b0200000740b80c0228507034460801950044044110108025080409903414044240c2065002d2202402501580076198125803042c032001c1d500015015401e03100e8070300707045100040000102035102008104034055015003d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 45411245 1250 45409995 45409997
    0x6020f1e0a030f020315010c030509040e3a0c0501020906070503030406110f04051219050601030b2802310302090c030708270a03030c0807020a020a140103200703 71
    0xb143e881c8a0812004901043d01e4500355401101030004036540501c400f0001075019040041c281500d1500160950b21440d10720101a00301c00c80c81182e21710324001583d48000c4007440540d40440b500d02c9042e000c4031000c450320801c0b1020702d9001c14010298102c81502c40054100c1d0ba4441a900b0701e90760707991040d1030441d82d02d45406030700c1803985040000e80311040e09420700300b40380502d44000c2101c01214a45904414000c020300844800c8007205044445407168004c1e00c259891400c00c40d1140030000c254407094400031210b009032040c1c41005160001c142c07240140c403610030380e1151501c025400c5400508850800300e2a0b0b9842c844507651003241e100301d88400440d5600c520307424960105458010110320203a000c2205003042940030304c151202c2d04003281c400740107014450303c0c1542032003055010030b5440c455001401e511074200740c0d10004900041007807121702d5010480f442d11510071710045894201c44150f0a078130035000100c086600d00362a03032002c40342030340080c2b0325844100114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 45412495 1250 45411245 45411251
    0x30609100b18031e030d0207241407030c0f0f02030c060712060519030204050c071505040218040f02061308010e010c0906260703270b090307020d06020f1e0a03 70
    0x1a16041150703c44d8002079060802840c200100c81300c03c2d070081d4000301030440d2081c0031414042d041e29000d4810403041041c4160103d0000c100302d2000c2412100030b0b1002d0f04242c2031200b8001410380021900420900610704000155041c24080b0304500922104130a0b500a0f4010300a120340e212400795800c803110241003002541e114108001c10040056440841c2d20b0398408202614059000f00d503c10314140600d8680480b660341c440c91104449403841d0b03440d940703c00f13100560402c9203100a0030032100702521094180341c0c0310920661703400200207220340c40c0010702c0c0c1d100c1080111040000e0041400074860303040d41041260203021440741140001d80028030000b0f225104c3c0e0080c4506818942c02c48551016040e0460610304004003000d080c140c5552404101c02904499140c04105e050400c2c0004c05692038030a00358007000e0147d0049500034003a00c405a034801440a8099910000050752041510f480b5800c90048040c00c02010b019200d221400c0c001c1a001003144130f409039820 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 45413745 1250 45412495 45412513
    0x20307090e01060c051e19082a1c030204090e060105040e0105060109120f0803010b0903060105030c01020316020d0b01081501050406060f03090314040b0408061803030609100b1803 79
    0x111044134039002c02901c00c0c0c1c840c00c000320881001d21414007459248070141c4001c1040c902c072040030200758603011514034600081e040000c400c120700c00014242004034003104d0724443c49085959154050880c0400741c00c5c4006030382218020ba044400401169405000502118001c41d8a0320800d202d66070003907040440b21083d869040c4502c81c8a650142c540b04451410451119034034000d08004545a021a40c85400400d0b030041c040d6001b000031401295807080d124082c0340c03c0c002c060f4030403070081c1c2c028030040006030380104c1076075500207140d4a190b980803d0b60001540103403044e02c01504066441c0c0000c94803035004140c0c1c603501080c0003c0000c0503687c036001e00c002c4070b1242c031581c1c000452503112016000c3c070940149204601034034151042d105080044101c40c1d00940c0700130400a07000030108240b103400e0050702da22042c1c00d11800c405031481c0030789640720300c0010300e400d203d0400c01c40052168020300d02c04001038010100e90176201e03403801c0d1079140007210100459110b8030420150f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 45414995 1250 45413745 45413747
    0x10903021903080f0712060902090102010c030501060e1504050405130519020303040b0f0d0606030f0e030723030c060a1401050904030c03050307030b030102070506010f05060c030a050a0c0204020307090e0106 91
    0x800350703865505648240d1070760340d1000c41032107100b00a0115410002c1c41c820300b850a4034140200c01c0544903150f00180e0b035a0030000060308562000a01205060508004110b45900550a580b804500750340501c1c0b121003044e242c0c031132881650001d81d4041c1c81d00051000c014441d070040362006100350b04442240004008000b2955811030001790b060780b00304004c0c0304041600002c0c20001d44500041d41c140140e0b10308031411740350360b6041107000036903c0b2445c8200703d41d5402081040342140b4069450240b0304e48908042c20001082d0001c1c01c00c08019036110300c20704008850005803980203460260030282c0e00c0c9800741c0a404190060740d103158001245e5842c000e4100c0340215410749481416012b80d0783e040d103180e007000b060202459650f00d60841562020300007460030602c124081c24841d030400c48011207400b440c0c0c1255004501c1405400d090a10000496100c00d4403418040d33221010490201c0e408204100002d4001e4004004d1141441d00003034040250b030b003250503a42c1301c0da80300c80ac = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 45416245 1250 45414995 45415033
    0x1805010e100b0406140702030118031202130302040911060403080414010e0306041b080a0c17010c050d0504170403080306120c030304030212070b0a020730060b010e0405070201090302 80
    0x14070110304020072003042010b00800817405440301c040805401c01a02e50000b80c21a51052101808400e03601400070425504c032611200e1010b4142003141071003006408006000300e94040240141d80c1e0b00504028000e40c003000c2c0808820007130030103584a0310380c0307810440c0fa00301d8400c0540304003181c2421002980110040824440050b0050200c0e540d1501e900b02405106650200941d5041502051000b000d0216890250044201042c02441e16250038064184240d800455034941742d8550001030303004080f16948cc08400c0c0201d030588440c20032110f103a2411070383c2c0d02c600c440001c000080011600c003862055404461000d514084a41c840b0307161000030010300c0d45904200400d10051901450292078805180704a5503060303201c01e40390045522060106015034803414040110031003983d598000c460032044001c00c90101311070003d100c000b48000042140c0d0310f901c05100541d1284403c0c541d406001002809a410101000381c0240b0f90072030250014001d040e00d003098024003030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 45417495 1250 45416245 45416249
    0xc040b010804020607020a0b0c010b01110109030207060c060f2a0819020a1209030305012103050a03020d20090a0b0304050a021c0c090b09070206190c0201061805010e10 74
    0xa16000350740e070b4666080080316404040120303409400e103940483c0c410114005041600c0c4100000120000008005800600c001000d00e2980c0e042c9580280007950110310842107480d54184120914198a0280054007254031301d05801d40c07405070310095880c0719880340c42c10303204000000c41c0640c880318803c0710740d44001c48041c80200e01d41e6043d8078030054154024203102e0700314a03080d40b2102d00b40003514103a4020b880140d0004e602da10040c0058040b00d02c40200340030a4841e540c4031100c2942d80900710b8003526150790140359000c40c803c203142c40039030403004002100c62224481c7d4101c00207024081c1d041800981d0207008656800f00d031900c041d8040b01d00958100d401803080b080c081d4200080b0500450200345851100d111410000c0c10344610f00010340a0b00e1008142d00441c8428400b1507000104080c0844d032284080c440311204000b21011424031500000c034803a118a041079025000d5948001c180d82820310600812410541c4858162030b08030070b5503410b540340c042842000307403514 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 45418745 1250 45417495 45417497
    0x312040c090e0d0804020f040905010204090b15030112031808100509060c0f04030b060303070213271203090503041802040f050406081209151b0c040501061409030114090307050c040b01 81
    0x3000405d000d4509900da4000c00c200007480401d40d1030003940c40710b0986c1c100707a0000c41290707101c4d44070000c985070442c402a001c5425998141c10340d89009040718841c20214009428000407480340400ca03000904203401401c1814200c0d094052024402c00c01080119800b560502628020590804856003202c1c0c1104d19030421509050135601c43d070000c40c201800255141c4000c00111005860711180402ea00041483c000341c1003010803500041c20208001c00d001941c0a41505400038000c00200081410149000504600b10b890550303d140b00e035802c0005204407001c500c1810b119550014010b880403850140007036035454060000f6544c460241c031800c0e4020700c16500c1c0201103007002e80610b680c0207009825140107000d6a00d03450b4040c0070301043e0860f0300040202e4002080201c2c0d2408074041c1c408110562407c00010b114261b5140428854100001c4903403c1303076030275000000002403000d10301540c0d007052070f1080c0c0c0d00d13401004101d42900078031404401c40c0c906840382061720001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 45419995 1250 45418745 45418757
    0x5120610080d0906140d060609080609060f01030b0a090615030227040b09030f0a030b19080709020c0a02120d090618060806040905060106050913060b0d0b01020312040c090e0d 77
    0xc020060720380604171041e038003a096044c01444011a0b107801914000c0200e074581012203407e040c00c65091a4005200c403080d0b0348914207002d0509c07220840c15044030b402481003903e540b900703580c03540500001e40014000c079041401140c0c030004255800f404480c8202d441c00c401b0f0346410101c0600005201d10007041011a00004e808203d0380f400b000c0c0d000c0b100340142ea14024a04040380c0c9580c1083c82c07800006580c412003443d950400d410020341c4d041d01c00d6401e546403132070010010750700e14039802000241078000c0b5050b00c082c4420400081d0302c0741c0c001e007103045c6a110b807035001c6da480c64144480ca000405060b000107009001c0d0010b454410102040325002604005081d00d508501800c52508141c0c0c61881070302107030043c04510301a00301c035030700d041e42c6419500c1040a5141926481100765140607000c00100304c803134040b035080c2c0e401150041085144840141d0950103110103013090f001d001300c200b10420110b81e02c980b09448600404000a040d01e02d4001d684642d034040701e40210704c0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 45421245 1250 45419995 45419999
    0xf150b0301050a1d0a0b030a051204031101050304020a06030b010e061b070e10121112010e010506100215060402071a01050411070b1b0f0c0c0a0b0903060c0c010605120610080d09 78
    0x180907007101800c0e204c003034200c0d0100087c8c3e944041c9403803071407910b2420000c0007040510800181c595418801d081c240b074900d0841c00e10703400240303080a1901c11902455501c4407940440d0340621490766058400130503050321204110082c040344d00c00c00c50021001d005585e4089003100340d403042c0c81d0042a03008007400e14903083c05400001120301000581e800e9107480404c1d1480d0f81c6142c02814107180d500004121804d952850714291600035101e2403240c4e040c400380b00c13071031640010740d03084014490942110031b4650701c01142c000d00ca102d41c050501011000e103100c0b50050459407904075201a542040755240307180b840302d40c034003a4605c000c00d0098940e011505440954a00101104018207090b1910001040c0220326502c041c0d400c1140c0e40240606190503d040c01d4003000602e15802a0380c0713441142070010751600350041c05001501800700380c02c4044502580040054030020f4684409045c090340c001d541c901c0115007140144200300800300d5000e001080003681a00706840d1782072074034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 45422495 1250 45421245 45421261
    0x4030804031b17011a090105010c03030b0f04020f030702240a05090c0a090b011418010c0302190605040605060406030314071b0605030106020607050a02100f150b0301050a1d 76
    0x1091a0a030074041c00250000c51800c220901c09011104484000100c0c2051442c4070030b03555503017225aa104000b954010030031660008926082030b40c0c1850001450b02d2248000303036261400540741a0030038070200e02d005044646400071030180000790210754080d0350001028158124150003180d034500d0000108405400c950001a04026201d00340c52120202c4400300d00640669803010030266110004a80903507046094107211070a84c034102464010406200516600744041e440c0c10002d441400905141c400c2c054484881c0d060844421014007908160001c3c01c4161003c1d205c3d10720302404569035242611a00d03084a905444400b841c840704034603454035400a000a94080c00c4c0442803a40c1088446045000b070200e94903102d40740d5062030710007890f00000410b454180101007180e06a6140c0000e010b00d210041c40d04081005105210740b0700140440440e40307945044030782030200d144540785015606a1300250f0302c5a00d015620f5001c40d030305001036100d850003e5a1900030503455 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 45423745 1250 45422495 45422513
    0xa05030a0c051009050d030f02031302010f300605010e0108010501080703020702030a12030b060309060105060702010918091202070e0408090625060b0d230f07060504050406060201020403080403 85
    0x718000c0c41600d80032158048280181c80440000311200c0d0411480b104c0b0080c0c01d4814140301c0c07007a5640c1103040d817414a01e0701a20340480b11002c0d05002c6111a5209414454040e1041c44844202c07044042c0302c2c980140b2180b40308007102c805501782425004555544214204014580140d41e0242142d1a01e0015034424401400900400da02007140d800035032410003890f041503200700806400a010141d0003001c4400408940c2e108180810134011031450010380541561011a8215996803091005031081d44696000d004142c00100340c9580700207182d880303c0e540d1402080c107000c04080841040b030721184140507008d2035a040c80046004108050094094003501408061900142810024060090b1106096590807503080b806c20031110b0300800c4034980c0c0a841603c10808142e90320b60a00050700c212540f100e0281c0c80d0000c148070108940d40395110620b06481d8090f0b140c510042c40c552043c0100ca0240b402c0c60320004400b44140b080f24202d94101c56038500301030459641d14a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 45424995 1250 45423745 45423767
    0x20108070c0f12020f010908040503061b0d0c03150306050603060a0e0304091503020d080d0e06011505070201020115140a08070e060d0c05090f04021009030201050a11160608180a05030a 81
    0x45105e00c22810842d40c1c800d2041000e441d0003012019262494481054a400c80050104d2031002d0000041e001c50024001584c0741400c4501c0c0c081180280100c00300c0051a1300da02c98000f141d0034a1002080c40015030185000728420f60540d92280e5036100c4910540303101591110141e402040101f040d050380764406994150305a03038002c0510b6483e000280e000c15030003000d035a000350000d41e181000c2405e105040c5805100c40181c02290b1610038404000d20350300021109104c03002038084110382c402c0d0b00c502a608400403800c0e120b03641320644200c41003801c00380b05004145c2c9000c0441c01c0d00700016042d0440d846141c2c01d034080d50310391090215010360345800f1103001422031030100e495950690f06c14070510a05d910b071081450180100301800c1401c080c80000d1151190b02840980d13070100c00c0b100da0300c0e4a400c2080074202d03064003d61400641c11440703c10112140030114603141d00c40585405201d03e590010301c90380901403184d8131b580300f8420041c282c0e0300810040091500560218007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 45426245 1250 45424995 45424997
    0xe0c01030b1c08031816090f0b04090b071403100b160602030703021e13300506040302071502060a052203020d03110702011b050106150c020108070c0f12 67
    0x400a00910310b001103064a4035811103407020044104034a4034403003644078004554142c020420500b242c03010a00500c030b640154148070f07803140c074080000c0c510f035009a8030003500540200410000c0d03092011218a05071030720f0b4001000c0051904017050902c080d203009041d003414003c016032a044000506502140d205504000c441502d400400c6651002e1842904d9a03140940e4940069400c042180d0300080c41607242c01c002c0c482807124100494140080d140f01c1030b4110400c0a01000c10440301212040b1200e40040c02280c110807c840883d806004d284680c00303d4000c1515945119940c2c0080400c01d8011383c005400282031801a80005400c1090841c50a102200300707000a55130454441054015910401800c4c0705158140300c1d09002d05d6803088180c0c1030800950000b01510176428064174040140901c11003440820750141c0001c0403009858041da0b185050080c014036000d06040e40401c0c100b0380000e80301030240c00039090460344116140010300007555000401c540f2041100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 45427495 1250 45426245 45426259
    0x1204050a0e090f06250305070203120406060506040b09040b060f030c0706020d0c05210c0d2304140f120a0c0f0b07020102040e010b040807210b010e0a0b01030e0c01030b 74
    0x11190101130051a008050b11140d5984a00301c030385078901c0041041c403110041501c0c020420251607400710039a500c0130b10f103c2446107581c42d58101040076001ca07410035540054000b0f80020040c8082e00200034a400076203050100d0020b0b44104551806117004103088508108005103502010303000401003a80704640060800380559070000c101c13104a00e0041c041030000a500681803402d5032452100d9100c0c0d10008990302c3e00c6011400c0c0780c001d04030744d088041c0c0c481d4110b100f481074808258142e1800c00700c0b02d01c00752409081002145001501101e098000d101600168810101c0c3d42d510740c1c1480130049180031700c040b104031400720001c1019a90584501070700c0c4006120900c0403030041145a0000d41c5507802d1000d80c840074581030348184041c0c0d038100010800568040703010030440305081600d480d111141e591101014130200d0b03000b08103200b1440003183c28052000c145000e6101100104650310720f01e070040d422613042818005041d44080100107182d0300c641c100845079680a0810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 45428745 1250 45427495 45427513
    0x2010c080f040605030106030b03010c021c090902030f04030f0201060501080c0c010b0a080115120209070c0804090603121101021305060903010e0a060902030c0603010e0a020d09080c010b01021204050a0e09 90
    0x2007150740003600030700001080003004009040d418007840c1d80c80300007207000b000088140c00000e03689106c00020101140180701c00d4503a514000c403000c0004142280c0d095540381b130400810a8614001c440072408a1270314012020310620521451098502c103031907156290315080c600401c01c1c1c00c130000001071907480d01b40700000c0d521801c85641c001d1100c02c001085c0b0140d0183d080d0200c0d08030750411500080100c15000140e9070b10310301c1940250a600b4840804070311810820428411500a001c105040103030000803c0041c0c110f42c8800039503559041c081c0e22401c07031407600340c0c481c040c043c444042e074240040c083ca180c020018130180b80d00400000d819060000c501307041c0452100d0039600156100142810340c101409014101a800c036440c0e8590340c14541c9203c03084402078902c000c00355010524603400391580e40003d50060300424116258060704100034040e06034034807017078014059400c184012520700c00554003550300007480c02a4460400d14085a1001d008041484078420910340e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 45429995 1250 45428745 45428767
    0x904020c03180a050f1c030903020d0804030605010b18010f02030c010606050d0e030304050a0f050a02060c0d0207050a0501090e040501060504090b0901050903070f0303050702070302040e0102090f030f0a02010c08 93
    0x900156900880b000980c4410008100c0004801e601c6203000d094020703211501d40da29451402d550f0520401d81c1110380743c05040c120781c4d40c03501e0b0b00000e4100c00000c1800c014800c00c00c0181049034860310701804181c0c0c81e60000b22080c000d8044034900f8032018043d1007603030360141c400e00c0300c06075151040703d0074004140c09640c2520f000e9032020020540c0020500b41e40410350203007026080b9548019032541c1440d54815075035040d0380c40080d01c01481c049040007000001d01c6440d54040d00100541d448070404a025500c43c90039050203405446132550000302c908180103100102c9005850302081c262030003407054085440200101c2745950390f80c10118095a0760301c1108211400340c03d0111607072801c6040760f801c46101401e8000c140e4024482040041d03000003501c610580d062030301081e5a01c4115042e4940700b49a040258080c0c00c02c6c8220740a05e0301540549582841140d500f440c0d581c06005064440c400003030b40c140d00b07801041c00940554002c81c02c0d043c81c035100d840401d14203d070f400d00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 45431245 1250 45429995 45429997
    0x70b04080d111b010605041406010503130203010516030b0409080f0a051b03040e0f01260a02150d180c090506061b010b04140f01050103050c072108070206010f06050904020c03 77
    0x3480f080d080b0422400031031440e0910030700e00a40700c2584c0070081034092000d00c2a0501d001007130103042041c00400540129003e964103a100c47c1e014001b8000390800306002100321088e40002c1c0002880c0900340002440c2901541d154507401c414028a080c4202421200c50342c0160710001c140b0004006c03541030100c40070344a81c4080e480e10050b517100c40c01c10f141440c0501028001c1601d680c0c4440041c00000181c60038170300b40a08400008a0440300040c2c4142440d20782e001c080d502850020044004400600c018190345d450400204000e45280245181400901d1005001000c441609009502d01c1d540202c2d00b0034401002d09040c02a090b032030803a0880e9110000009945a15985e88141800d00404079201c00e082000001482c14039042d07509240c0500c5158105a00c4a0200742d4010905080b180300c190030000c1451100889100000e582c4640c8955000284050b000030b16442d101140040c140c800d06a10000302c2444c2400441e0b03a03800541c03603e640542d00301f10780071242000700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 45432495 1250 45431245 45431257
    0x1003020307082b0906051615060503070512100c030e0a060903090608041a070504091109090c030f070c080d1a090a0204051c11030d0c060506030102070b04080d11 71
    0x40081041e001104080e4802052054030031042101d007040001840383c0100700d901c00d1740e00503e40540ca80000c2e07500483c10034030281e001ba00d0402c1200c1116908036486d0068800d0310030580071107540e190341e0424001040c811000f2949180c000266820701e0f043c1942149425054510380428003158035100300d414000740e401c089406a60314035003d0b040640090003103001b4034090a0100d42c9141c0f944030181d210035110700022540d610400081c4400f8001e100752070240660910402c00d90a8022081001d6440280c4440c0b1552842c00002e010000060461b4800c0c040d004421686448a010503510855080340413030f800103050044044041c4248180140c00011004d40c10b040320003001030083c400c0d8080d05c0d034542d2a004000034021501c0c3e0055003d9482400458400c4170410b50400d01c6004504005080c1c1c140101d1021480343c40c0c2c050883c1c440070340202d608104944418040502300d05c1005401015007c54200050110300d020004d080820000500841c03c0201c0ca40d25140300d600c03031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 45433745 1250 45432495 45432509
    0x302030303090f06010614070803040309080304080709051303170903040b0d0b0103050f0402100e0103020906130501170105030a0303020a0c060c030e15010311061b030c03070308060301140703051003020307 90
    0x3642c0310019903e401c1140b203004240c5030404203882e9412100d204210311511601030031101000001c142010302c01d00400c4005c040580aa945840d221903500c0e8941300244125100d031070400f030110711402c4010745842c0030503a051b210380ca0b6480070b00071a2900a1401080c00744140810f1100081110b801001480804a14540040d800540c40000342c01c460001c0c00c0558000030500810005840310f0183c0440300c1c0c091700f011520041075600407030103840750400d155048800840c080910b01c170b134500240240c0308262140d28240040c000760323200c2d5100910841d90705505c40e03884103004c24080e50040c1411807041c680408c06c000d4030744440041e582c40300316200c00265101c400400b0b158040c040501c001160112061041d4555282d140101b2a04941144200c000044000000c1480c1c1054690300300f511003038079240c42081900980342c0c0c02084058000c0382103640040d003585010710450a4400721441c00001c180c48a007030840c0200300c002d0141c141c21001e1040030001d41d400f0400130b0002c0500e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 45434995 1250 45433745 45433753
    0xf031b0f0207210b010602061b03060a050a180e0a08041505071406040b01050105180909070807091407030605030d0f030b1504140a0302030d080c04090c030b0406050102030c0706030f06030203030309 87
    0x640b13050140c0c040140d103e14210b400003400d003d000c0410b405000d40b0300484448140c0c81c1c0d00c440001980c0904c0c56448541c0c8462100b5000803485043e07100400c0000100000304070180325170555944070284460010030030300d401c21060014452a643c44c41001032036151071401c10065580c1e03010040c20480000c852a4880002c201c2001600d404060142500703180003420010880070b601884210700e1034440c4204c000710b00040c00d0800c00c000d000001c0c40e0b26401c40300d1040da1080c84500518140043c040b19120000014401e80d00900070a000c0310005070040c11046c900c100111645000782c0074a004054640c4494032843c1d481510f000000d00e040c03103e95a0301c61401d101001c0044580107560301460b0007046c20000b607600491040040e1440e42044582075442c034000010f0f0b44500e40203004624507152000b43c4641d81a482140101801e5400b008403640701c0005903503a001c1d0111041007503010341b5050068900c00d4000501c540c003071950220f9004d480f80d00090460700210340c00d44050344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 45436245 1250 45434995 45435059
    0x2040f0803130f0b0d020304020d061e050c03060117060a09020408030a0e040908030403050c031c06030b070810050f01021603030203070c0f030b07050c030c0d0f0f031b0f0207 77
    0x141e0b0301c0e9000104651005104034a180521114050240c80c2c00302404650200000d4255103860400100d07007540300a080040d0056600e80e80c8070950702e00c2e41c07a01c0c01840d010000707150b803100504503030041e8016111030b84103000d14000c440345000b0040c000785d081082d0303050000e090030141c005030002d0100701001e5925181c2901000b40241d0016000d140b00303030b00705031484002c03e0810003280c2d003094041c607045503101c4202692524621541026291044003078042e080c0b81e00e0198040d6056031f01c2851004003039200d5100c101c4800303030203980380c0c00b241702010070800980c035082a00303002d16241801940d06840240300d440c4005090365100ba000b58200141070310800c0114040c44010b062120541c0940074210340710711a100c04020141024880006102110740f0b10800a54144c0002242158400c22024000820380c2c3c08004811002c01d61040e01c040c0f0f014001d000e4a082641e505d6848807600180080c00c5402015086d150400d50042050220304010408032407014131240c54401600e01d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 45437495 1250 45436245 45436267
    0xa0b090d02010c020c0d0807030219060b0406080105160810030804030c0e01060c05030304060203060d05030d0603050105090c031c050c06070201021905090d020d080c191a04031205040602040f0803 86
    0x603c2c458080300440d040140c2c048a240d681220144541d90001c01d0380d9210001460f0903880c001c0c00c8000e07640448500301840341008140d800c00404100150340030b206641d92806007a007a84c80569070012800d94002c240140240f203540c805074400c0806d03550850055880e29070b080ea076801900b040c2e40500503600c0c1400021081d0224a0040c0f01c030340b40c0507084c0d08040d202d80f500c0b400040c000911898002020946d0356841c81110041580c10100b0340f07a644401c1941c00e00203010611046859500789400a070380c5403004200c8511090018016007015200b000745117100b14454940041031090078072400c5900780302002014400c03100b5400060351542da11072054900456400d08404006040002e181e4544464100035101c1c1d90540340190084454503100d1298041d0862031442481019042c1e503400400d0100070b41c0441c0601e9604a20000c12580f031104d0345020bc2d0b02030081208aa0124401000e550046c0e600c140960801801e16480d496607040307600c1594441507660f4004920610a6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 45438745 1250 45437495 45437501
    0x10302090411040e100b03070810090218040507030203061305060409050303040f17130e04050a060c0f030e03090102060c03070306050a0f17070e07180306050705120c030103020303030402120a0b090d0201 89
    0x105d0103c03452608075161407444043c5100003008401003022030b002196091804804500c041c0050301c60940d100c0440c0301d88802440d0b64220050f00c5282040c0110782154001d1007141d00400001e444142c1e009007a010030070180030302605280c0c00560314001940401c2060001e10f000d6032054446105511550510810845840000c10600c02080101c10744415220403107104403081442809070a55950400c1420110704d44400340c00316051400c14082c1c030364480030303900b0309180640303042084d5846050384650b2800354141c5680581d0100d40440d642100c04000307140e00480d50300d000f0800584800102d0001a0a40d200e032000009589090000100c0a60640c480404e104001e0030844c1c603124070325a15041c0a080e440500c1010b8070000202c482c4030341000d010b1a00300009004a0410100080950784030b403066003852021400491511400c010440341241c2c0c000700210f0460f1169000c004920007003100156091281a101c0c000161422134900d21030142c00d40030b41303c40303055440060b088d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 45439995 1250 45438745 45438751
    0x16030c1424130b03060904020f010c050d09210c0302040207020a0f0305010204030b0609130b0c1b03040f080a0b0a02030c07050a050f100908040e072c03160b090906010302090411040e 80
    0x441d01044c41001010f8484408256110750122a52150442d80e04010707210540400380140c140e000d4a401040c0c000d4000314501c04440840729142459200143c210700d03105501381c0014056000c8842c10009880d06802030b00000b03000500c2c407030901e90786044007015400d03503a00403a203694000c10100144441300e004c1e1544100c0035121300d640c03440c000c0700041000d15913000040801d40010301041c01903081d03509036030904031842c60491307d41d807441c01d1256981d0031601c02d100e03032204280c6021845400c08918003103025844100281691910480100650030041128600410612821010450130441c07105c00e20b01a002501911074001d4125051074690309032540f410341801c10b6030000440c410101c0d0112a00b214052003280c480070310071140c0e002c0542000b04001410056201c0300941d01c004031040740710803001c07a58030795000601c420381c2c001d2600c02c00803620014040d4000908005484541c481d005140052030180001c1c005000c840d1189900c4504007800324007446600b0340c4060080e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 45441245 1250 45439995 45440009
    0x10507021b0306040201030507021c03050405060106020f030a0806010e0d03030906060b1603140405030a030f120b100c03030e0709060302040e0109080a050d140406090516030c142413 80
    0x800304018070200340d0710705014000078101070f5250700084e8907034404e1140400c2110151480d40b003d040164008007c0c02050740d05a940340101000005c2d00d03030002801e00b42c0249940f02641c10010240402d0351440f41c028022070600c680405004090764400404203041031180d24002903002c140c0c24030004582540e04072004c00c0f03601700300706d240100b40905081c42e100c0d4546000303c074174020355080f00c0450189901c03194143c450b001b4103400305600601202901e402a42d165030034907030882a4070003550040320b003d54028800005041c103980c89150b00c130f6680c41c001c0c05d01085171002101024a420569808800c0d900d035101c0c018021417400d4054201050080d0000348a84560b584403000944217044212003031110000708580d22240c40c0e0404000110341614203d10381c070341800c10a002e441c18540481c0d03035015035102c004540070820b440c903083e40d402080e8040c4490800c0b1003070081c00d1940300303802c0d0700c40c800c2841c070a80c0041031162410034403407038880240c641a40341c0911010362201d8024007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 45442495 1250 45441245 45441283
    0xe04050c03031b0c041523090108010606080f0103033c1107060e06040b090d05030307080a1b02071503060503010e030403050d1d090604020c0316020a0501051612020102041701050702 80
    0x610a0002440c1b5500b9100c802da24003a0680d00640616121500d4810140d08041c0e5100001b0b0300a1041d80088116a020385400710244e5400c4907815001d0002d00006010602035140e9002004180c1031510101a00c1106c0d040c0780c00d54820240c80150146040c4400a85407030160300c54008140700410044c8124100501520481000204d250180b40180e400100e0081400c035420f0766001801d183c3c0c0340e048000d8990342e0400d04c40c020300b20b440440341c504a1604140c03100b1011180c000901c01800760741d40c080c050290819136040c0e110101581c1c0002050b49604010940d641d007803196105074036000c00110303035403891031070f02e24104146098130340305100c03c1410554400000710000100e0f004111200101036803580000b40007802403040d032900e10f02c0b02191002c0c51107070280911807054000c542840d03000760790740011141c40c03241c0c0c161800260a581c11420000782d031b444030301a90390314038000503082c1038568103040090403542c2c488440d039030745540910802d079805024425460f40060009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 45443745 1250 45442495 45442511
    0xf030705060c030406090b0408091507030519030e0d121409030f070503071703090c03030c0a08030604090816030905100f050a1206090e0606030609070e04050c03031b0c04 75
    0x40c1e4440300020b1002016500010016041218552007103030041e42c0048007441908050802d0340c050342100711850300440c182c185021b105042030058803100c55241d80c455180442d503500404a000c652580d020034140c031541c01803600442032204410850f12a40c1c0c0f00580748810b0280c00a8500342e10b0250300440002c020700c21010f02c08400c4860000e80b1714000c6a032622075183c02843c40c810641c02810340550091040716004482d401140202072290407240c03546002000c1640780d10846107002d800f9030050a2100000d0401805140d201700010301c0052012010740750041103030f0060f1805c404510b0240d031851b0406030802c903010b01400d010707503115621850f0341401410340c00c640948141485400f0482c0c03194503114041044440d04581003c0c040140d440880c003029068103a000f1b40700d402844c000070348606000489901c240b00c0600100100d51800d50f102581e0b440240096900f406207912003245620100001c1c404079020849642c40c900c0f020f02840c0c1480b1420707400d544281d0404080f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 45444995 1250 45443745 45443753
    0x90112050405280b07050703110f0607030902060906070b0f09060603030301120809130204061202030c031518040b0109050606070b070f0c0204060b0a0201060605040b040603020d1d010b030f0307 85
    0x140340f58658110004400e003040792203011a12428100c008000712900400c1056841d802005000c01c0f902ca82c80e000d80c0782d00c0d07404180b40c0f40e07410a801c04403240e1120000419541c441d030130940c0c2150010340f08900d4004c9800204155500904d4103540180c4030f01c00340801440c80198032070340031400402501480c2032150000740c0b00d10043c85900350241400d62083d0611000e0401c45a0600b00201242d888200c05603808002c0d402030722031880802c07800d8181c80c403041c0c107030f0007101c1c440d01c80c1d10809440c503079038a1003803c40c40640740c180580102900c104001c01c410f6203c1e0150180b03000d030418108541c90718070541c00361000201000d0103034205010f44400665441e5515030407403400e080030b00410403494011202c2c000a032001035070060504000240807059580202a034100c141c2c02840743e5903c030390003a6814851885140c092080800040113a03620913030203041803020040300450310701e8660074000034203d5040269855a591003840b00705524040045200340807440c0050741c18152184c039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 45446245 1250 45444995 45445003
    0x1210051f0509010305040201030209030a0c150f02030d0e011104030b01091d03030402100e060a1106010f0315050601090f0806150906061e0c010908040602010605010309020f0103020a1211090112050405 88
    0x7142c0c0e814503454101007411a030198054a18642c0c3c082c1c226003a282060411013007041c5d8500c43c24468038825800040c12500c1418a100c0d0303c8007d80082d4239141d103140c801c2004101c0c8250003034855503a26203002100b17000074020402540182c07c0100303030354140300088040b10110201c80d001200c039124045801403011081d00d83c8140c0464030705402e2455060159070310314200d9041680700500180450015810080c944084600b58089500682c2c845980e072504126601015055800d0203c000345c40c04041d40105511040c103150280050fa07030351090781c1003a00c042e080003d80d81c00c00810003015120701c01c02c242d40390b941191850b00320701b0000b000c941e0502c0741e407101001741c0c0519440c040b4000c103000102c030510b104450003008504094203000032660018080c0d02c0055080c5a00020250701c00e00a4a510740d800805180120490400640003507010b14004020303c40030001c142030460b034900c030f44041540e00700c0049503109007682c00185140c820b07500300344116213428113000201388001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 45447495 1250 45446245 45446257
    0x1707151505040b030111040603090308090a020a0b1e07080d050603060c03130302031c0204030308011203020607030b031009030801050f0108010e0612100e01091203020a020c040209061210051f05 85
    0x40d4001483d40070300404240900008038022a00c1034002500041543e81544903008040c06940d851006841c0c540e1a81c0d150149000043c0d03005840310010b020341203221004180908102118480c18100c15480340615044280b00741e03001c0c1d201040d06a200318081c0a0305c1d6100404070081c0100303213011071244205010140c20303404031103200300d08441014000c1045404070b00038510f5420350200302e18441406580b15000031400146103600010f0301016402d5881140303581341c2c016228560f12150f0840c002d15000c403840361b151084003c040710b5030429202d881c440d58020303a14030b6801d60602003801301410171521b519041000c800010049000f044d420141c00c04000c4402c149400e00320380726545007850004020320011b1070100c84003000081548400d0000b8420303020303000c4070352102030150200c0c000d410302c0b94090b0300100302c48142407800764000c18803184020026410480c0600901e03214800464600404002c00c00040c041481d0500c6c45003000f4140b180b55585200402c10014000c0c041e403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 45448745 1250 45447495 45447499
    0x40e0c100e01051201090b0406080a0b04030513030b0a14010f060c02040b0303041a190e0306130804082a040b1005070309030206030a05060108060603090a0305090d1707151505 77
    0x85051440c040e880740f4101c48070740ba41440c00d6456940c44d2040700300101300c4d0b030900504c5140ba2140001e40050045a0b4002c00303030b00040c40b01040d588030346003501c840c2d0003480c2c10322080750101000f03c00580030061f62401400805000201030f040c1e450407940255044e001b050054820607000c010701944078840c00e1500c0d50558001c941b440d401d40c0400d24601464000892811a40e00c4041d607205a0340041d060309201405280562031040303500751541c2c143c07109200d806400900001e001f1640070320303100007030a220310903051801d50340c2d032590703400c0050606103540480b00641d061030b078005c0320901039419003030111420010000440c0010f42840265030a0710203010380400d950301418001d1804200464014015543e646061800080201011140c40e40030455181c0421502d050900589209144e02c10050140b1070054606803001d82046000d01c4c0d1203241c07003900000050001414803c28924030003025242d0712070340b41c1030114964a17170080f100149006000c0c442407401c4180c00c0308465003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 45449995 1250 45448745 45448757
    0x90c010e150c0102130303020a1b0605030c180303160b010f050a0314010204030c0605030105010225210f03030b01020f0d081506070605010308030a060504052a1b030306040e0c10 78
    0x5102d01c2240a4000c4010340d100301c441c030050003c185034010444140c41d51040c44600c901c0c10502481202044d10b60040d100051418000100c0c00c070341c03042c014103074202060280b04041160000191075a400800f000c103800814055510810000614203405030032800304981e02207003040d0108240004030721015007280c0c01e060800d4042c56081d070480d03000c0e540243d0300d03a003440e484450141043d4801c4c40f529005204400d002d0040090802103a2485648084200c0f0b000703292500140100f4911420800a02e080d40010000120900309a203002da1007920003203031901c40395002a0500b45900d055440d260815422403420325881074040d42e0101d881d038414102c1d0480213001c28407500070507c00400360303440d040000c000d020b008400742d40f094100001c00d118a035150b9080c0301c141d070782c20f07184240303800040118024001803010703507140d485907504841410914030814401c3c0c1c201403003410001d650070000900609007414000d074108004454001c0030b0000e02400451035a00425000c3c00070059 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 45451245 1250 45449995 45450007
    0x150c05090603070818060f041205160204020d02040b0412020103050f0415051504240b070b040b040f050a11030c04020301080a0209090715020105090c040b01080c03060d080304050303090c010e15 85
    0x20040c9800794134074001c801151306910300a04a91f070f056105480c281c07200b0451034400c0d1100351243c000c955070030510034041410075400d40e080c40040c0d0003000003210b0480e0280070100d060301014010b400100300d44c6a10035034481c1d16000250071500d024142d0745440040000f0400800c2a503021191002d180f80c0d00040e903980c0b191625a25452161411075000c0d007419806243c445070071400d50710840360325003000e001c00d0760b0300443c070040d02c604c07000102054804000a0041607400c00140c0d40540180d0881103685561f0b6035060801c255100101ea900c1d03148240010217003410005460f031070a040e80d04600c2c40d41012181503803046c4a8100070b01c51514800080c6110741d05101420090908200c45001c08101d64000380c0a058200d90104a80c130900000503070914107030003280004407044e117802e000d45e201c46200300d8181e400208425008501e9004000000303290301c00452041d402036020f540c0320704001d000c0605065108018604120710036803000615a03e480304071840b480302100183d40c0310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 45452495 1250 45451245 45451261
    0x30615030403050d0923060115030506040902030312010608011d01050d02040b03010509210301060e212d010905062403010608030913020a02030d090201030207050a150c050906030708 80
    0x12103407201100419040030a25410003086e880400003113408800b1240104010800250b0b880900b40300c1c02441c5103d1400002c1c400340281c1c08190003032130250000c42d603032495401081c55540982c2907201660308034401000056480008113000d801d000302242500ba84c1c0408e40e0130075880c103005003446040220710700300841d6a00c0d40b107080400c2e4064000d1285140501a00780c0302e09000b5400700e82e80942c0300010306040a00c90840b416a132481e250701c0b65200070141071184049042410040711180141c480340a221304004d846000c10001c0c2c00018140c80c2c000450b0881c40300d40c0b0013800700340c0c1080e160f00001400811119030103145010005c008031441c01c5195251406004811b4040d440e010001ca1140d401100410440070103944c80241d000300c6050100407880380100200c0160414060800c52040e190010365103a8014076000d4149020b64480500b0202d118900b202d6806610107550003443d600e0098842aa406041c150305003040d417400b00d840e81c44000d00f60410000c212000660007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 45453745 1250 45452495 45452497
    0x316030b030a200d0c1802090a0303030509120304200103090c0b0d0b04090b090c09150910150305010501120605062505060103050c0a090506010c060c0306050409060609060b03061503040305 83
    0x2640003030114a034a5080e0500300c000117081e02949043d002020303c3d01c0d42541080c001c9807500c1e81c010b0403035403d1a00c1c68500301c00505000e041c06c0c1e501d0284112214103542100055070045028016812841c91071140100c44608010162414076051089a82c0420b07200400b40c02280c0080442940d207080c0d40200c03c0003000103e1560341d016182070790110901202000107481403180004a413503000c0190b08102141d10b04070744140302c0340801c945d8541603003003c100043c1c0001c0030070b1900701d2864880b40340050922820a000000a6440380100510340e0311a007091074180b000101080a00d040c0030115100d84143c0b0452032182039a08202646410400103c47c500f607008403d56016586a10385152100342c031000c103a20908610300081030700029841454060b24058407044031068a0b0350303440740644822400c02041c16030341d6100281d15100c60294003079413441100009206400c0c02000c800301d0312190400d1110401c06e108114003a211a2201102004541d203295201d070b0740c905c1c0460352 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 45454995 1250 45453745 45453803
    0xb0604080708010b03060f04051c0e1c020a0e010602030901050f0c030a0206040b06060301050d020103050a09061d060c0f1b0c060703030515180a0902010908060103080316030b030a 79
    0x194441e800000640e0038065104140400007241a11460703100c41420461607001564064030039001500000b00c451071a00d60382c6001000c0c3c0c289500c41c81e4090000642c400b10040c190410481040004070861030201d0404019080b41015801d265050a0000b0368034004c0302c80a5062210024242c002040b07105c0561310800c2201003125a10301010000075200c0c00180c60441c1c41240300c201140451510300d003924145d80c806803000500c1d0300240c004501805015003496000e943e600340e01d101049542c01900e824001e16082c2d0900314403045a56450b005004105801c2e541d020708c10500007445802c11684101070745444001d00044a00065050549420b241d5500c0000082c10400b01501a007001e407241c0da1070041c04407410044418082850300721680e95603400d84c4000060201030160b8031901c1824010702d408124039032201581d42c9000b10a800c113607684c8001008003c0b442130361100e903030640d002c98035041c1716200b2240c012079554148c41100038002c10f80342103084404c1500d8400020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 45456245 1250 45454995 45455009
    0x50d030c0f05071e0305060601030c05090d0b06011b020d0803041506081c03090b0402060c0c03010f020d0506010c080409090305120709050a05030a08160c030b1005030d0e10030b0604 80
    0x400a000380340581e507a502c80c0c0315051070301c3d1810340c000c131080000440741c0d42140e4111024103469550720303004600402c1410039050a02c40c0070721a0520a03107680d4070305001c0c24850042040350381000c40c00900816442c941d241e82d140c480c42420340041e280c0450101d01c441e03120949948a84592500c0072040405080d820301c01e80c9006400514000d00068141603180c07075150301441e001c09500124141c7d110900094a41c402460129006040a40003400e03c0700d422005e490701d003294040001e080d0782d441031606688640104414004120500c1135503040003090030301d42d502c408581d8502c1a10b0080d4442c9000709540d4031510001d05000380f0480b04003072007007001e54401d450a10b001401e8044140915030145400c0796001c59107050009080300a59001820203043c014401401415020002e40494030114100780000001d02e00c0906140585c60000c000944d9a041c0028140703003900301d40f150820400d0102c1603164680303d400602c0c01c0c50305e141c03801094000b65100400e60502c66644220 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 45457495 1250 45456245 45456263
    0xc0311010228020114040b030f06041d0c04050603010b0a0303080c040906030803100801050c0d02070503070f0312050a020301050904060b01140a02010c030e0c0307121109010e090d0f020304050d030c 87
    0x99480c082e03070581500c403540300343c84204101c44140602109401140941e4042e04000c10200348034003c074508082d80240001c03c0441d0010b65451060000c10740c20403622943d0780304841010042c07600f8026260302490507402040005003490008101e03c11610014003440700c4c180c0425248032883e012103003d852012800c2c00001c2d40c0f8501502258412140340400306100d00300816805c1040c02014000c48002403e54201130303071035072120002c3d480903404950a200400c0298000b40c45e101d245c140c1300380a0746841d94440c0c0b902200c002940d9000b070030384515072710400c010b1003540c0e0343c1c07903556030803d402c610002600080040180c4501c1c0070303213088400745980491082d00855054001d6128022190b9043c0304a072440195550340308c0d624200b041e41b41c0c1081da014003040c540c5030540c44615010f0320100400a070090003040b18410280c00201001c00d0382e03410414044420481c0b03c403555590310b80000000c01e8100000c4d164060350081300d03c14440805200c0c14940304040c4d8401e0517411080013 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 45458745 1250 45457495 45457543
    0x31b060307121107030314010f14010201023c0702030a08160609060e0c0a0302030c01050c10050108010606030c0c030c060507050d02180f0307060801060e0a03080a020c0109120c03110102 82
    0x203d210343c0001e14200c0000c1d007070104031907605d541548124105d8071400c041c00381c142d04024100028041148200d03045640c02d214084420040c141c0e000000d40782ea203203541e40c903d044030180000220b80c1c1784010140303000b00314a0340162000107d140c01103801c0b011050b150004070355402c1c685550210050840c0d410410f2103424094654049426003040c1ca08136140c8002c1082404540001840086e5040d00500202020795000d400140304840381041625528800d508440040310f8007a004074072640e41d81c010920483da091300c91000d04440a0804480c04080399400812403503200c2402400e003500e17500400d44040c080e0080d1074900070307144030640d140ca03045406d6031500801c448250f44030701c014140100b01c5080c04600a000d89001c0d58684800345c0c00d0000076500621400c8560f90000c4910351300101249071400a0322410314942d01524079121724000040034117009410000015464805e0700002409540050085a902032000382004c404280141c0c1898101100348440000340d180c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 45459995 1250 45458745 45458771
    0x120801080313140f220510140409020409140604020a06030203060603060d0c050d080706050106030203061305061504080a0c0801111b01110f0304030809010207080307110a060f06080c031b06030712 86
    0x400051071301718003820440d540d1032814207041c040d4035100c0c800b900065034a080720942010340111003200e0000c0d02c04600b0440c031f50784401400e001c1522003007484e0030040500045207000c0e000440202007524007903085050010008a092002a08003031007450703003001000c02c2100102c0c2d52001403c0080031007026072101d090010556005000484100e4035040010401d0340c0288240c1e40507078400f80080311502c0410a44800038103001e0a030650140e140318100c0b1249202000800c09000c83e24047e01480206203040c1083c8403242d04910200e9040c08000400030030540b090340d0900c401c0114140103103020203011801012100c80d40164140c0c0060003603050307600c1030b0046018520076501d00c40326944000406080380901180100034402c1000800c2103644200700c000d48010946003070340d5091040b542d91000325a04001c013000d02c507490300000c100001c814808040c030540e043d0003812440403030300c90100240003842d01c418400d944c00310100380210f00c0303500d10903c002003044041102c28401c8413 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 45461245 1250 45459995 45460039
    0x50111090a0503150408030c0c060106030902010305060a15031509050127110304080f16050106060e120a030810030c060827060106050a0e0904120801080313140f 71
    0x2421a01500000000280302c0c10f0000341a0b802144e15800ca4140741c4482c0c3e56070074580d102a040d1004c40d5402d01c0400c0103903505100381030003070582e61000335560000380b00140589200901d403500ca044202401c210780c0201010b510b00f440b8141c80c0010325001c0043e21a04042195089040c000e4a424008150106254032030300c401030340700d441304a0542c08480d96100340c4100842010f25850180041400208a80d02400c03281c03010369112070420414070050489504643c200340c565a448403410040c098010300e60070071400007034504148484816807556910030100700010304104000c0000346a14510032048000755911910703e2a03003a6440f071005225281c2580e5455903001101203013102c03c514803107008055000341003d010243c3c80c2c103000f601e0540002d50400103014011380403501c0e41e075a8203109807040340301d0039a55100d00c601c10002014918140c01c4a84c150384104840b14a100d40c1403e140e0488101c3e2081400f206100c0020810182c1c2070300a594110501d2043d040c20707c04051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 45462495 1250 45461245 45461257
    0xf040308060109082d030310150e19031103070e180109050303010603090309050916030b010509180a0e030c1504030e090f160504050d02060304080c0d080a1401060e060a0c050111 78
    0x14102d080440c260f04609034981c402a208c5041074204030b00d040001d1809095440e20031324150400424000360007010592100c001e50800080c00001c280500400281001020000c0f40940c001e201003401c01803022200c00b0050400c0103860700c00c0d102c51781030745000d4000785207041d40213041e00e07125651440c010b000350094036011400b14591283c013140c030381010300196119080ea00100c90041050b0301056008003211301915042040400c452522a200c11018a410541c00c056110452030031030b006100f1a540030ba41489250002c000580c1180400107064000c10540d880035880c988403071a040c0e80e41c48140000f030341c1091181e0f003044000d803100a0b1a82c4100b0541302c0e950001d440da44002c48003403040703008255100342c2210400d400360070300780051944103100301038951800503980c46051410700502211000a40e006042100640c164000c0340000c4420303007096441941071003030240c40c040e00584803600805001c6900e0030042d10410f6040803d54009000b0404003110843c120b9203071380a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 45463745 1250 45462495 45462553
    0x80106080d020f0c0105120910180507090207030e270c0306040b0108010f0b0d06170c01140c03180d150515090903090f010903060c09060e0303030f04030806010908 72
    0x1288269031084004605040b1181d01651b40b00e1030160420700001110701c002e003503104070f4440d920501402900750b1152420880400d4503800e08800c2510b006807900c182a00801c11450040c40f4480020b60098003c912a4004423580e00100300d40c4041400148a142e145034186a13991042c044103881000003035000c0d07a41a101804440c1d451401514441070a21580000a22194042201007288009017401c9030740ba010100344650340c0d600d8044038044401d410a46038001c840004c649603000719561303c0120300301000310f040120480588e601c9001e2040b0805440c061030440f1403c03640c8160082ca54a60311090f410a008000e00781c4000408044030003070004904650100c01c130f071070280303c41c904c01d4142070001d603e00241203080c096a149440c40e040d042c0161020044002101805510a9080640d49100706c462034400020102c84a2080d50350098108006002944400e000c090f5030042d0982400380850b2101030040740c1c000b22a500004880c0203401003c4010801300c680c0c1d18504d400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 45464995 1250 45463745 45463753
    0x30204051203071709030f0a0b22050c04150e090705030f0a02130917040602010c0f03060b0d0b01090f0311120d0206011202030a1502070203011506050904090c080106080d02 76
    0x4007401280d81c910960034043c01c0319209050860300300184600411800c040a0141c0314030302d69a0000781e19124a40300100c9503034505c242040100308441b4080140045040d107800c3c8614040e0b100c01351a00000210301c1c4c001da85800d2070040411513902c0c54001040c1c42d684030982c41c5007201c145a03e40c0c46900030750784240642d810450000400140030040c140c1c0040501c00f4060040442c60000c184990702181c000d500c407408881c0b8500c0e091b02500080640350004600b034541003c0003090b11140c070801505051401c94180121800c000584d0103e83d182840050700d801e80030300685540805d64400000d01c86100804000c011443c02e010603014400d6070b0203c07102071124202c41c2c840e0000000c0e1801640107400401c03046c0000b10083c0b604900150580b80900c080361269184403000d9907036485c016400003803203811030809204600d2500701c5401c4d0f0845041c100300e0010000d102d04c1301c1592140f0f03110310f03000060140d044988801071044100801500c0e81c0d5014294841c0c090341458005402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 45466245 1250 45464995 45465019
    0x30f050306061b070503030f07050d0503040f0b0702070b0408030706060b0306031203070c02030307030c120c0c090b06040b03010e100b03010605070f06020c0111030109150503060402010309030507060c03020405 92
    0x1004405503406800010300080c14414004603182040b203400f460050746101c2da42c030009036034809000520503480c44041c0b0650364115400c10510340511085001c0c200a4104204408240d4520300007029a6102c0884c580306d0301c03003100807498042c02d6000010309010005000403030010001c01028841d03c0380000340500d07642e440d031850b5940821103041e5007540000c100c1d4102ca445100c01582c3c40f41c403e0400940303070507964010078550340003004214003240c00034a444042c03240e5030f0b462400d0317105140751161202404e41d50720b40c2c10040034450509007075206c0100480d0b5a0707851007590041c2c410310700455260746e540c004020301640c09079886100200c071100041f4a281811040324141c603c0c90319a07e00d4641a41d856104a14905809031074560382442040741031322081c040c09003000c0541c140d454981d414104024111550308010388003c206000c4100025140401c9507640a80c0901700002d003814941000e68203846050360082420b840e204100b00803603055400340c000d4400581c0e035103850754 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 45467495 1250 45466245 45466247
    0xc010c08060f0405071814010908010203130209090a02090a020306150c15060109030501020c011b020106030201081602070e09030304030906030c0c0b06030708011103060405090a0309061404050a12030f 88
    0x194140d4007507400c0a4804142d800504054011980080c05840c00c2c542c01c1001c05a000170070a1650030140c1500f0442d04215070039a44450000c0240c05500d00840c51070420750401c216241d180f0100900600703a41e40000d12005081c0800564030b13401510b0b2031410300d00441000001e50088614500c01d80a0307003001100c100360705040c3d520b08001c100090501000c04110744c2c00b081c03070040c05141040448000400000d0080c000f0f060040c2c161000450b50511043c0c0e0299140e29403684201103a140410800150307911142454028814004544181c41281d03012820901a82c001503070034400c0005015003804008001e6204600070340d1040451500d0300b0086065070044c84408000071118105040428074803080304e038102a0040c2143c1c9056603440e4001d0a40d6030707060302e440350154080100001c50405000f0540d00541d424043c0103181880e64028244104a003d580200030303c5148042c41e1421101c112000743c03600400c091441980c8240d41244010f510904800042c12072034601461 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 45468745 1250 45467495 45467507
    0x60f03020102101e0c0c0c1a0702010503060609120708070602010504080a0f0207030b0114040e0307030503010e0903040302091302190b03010611031309060512121b0a170c010c 77
    0x5a68164040d1000500400a21004d018100c40703002e01071a0740c05095030041c1c0548160307103036003602d1340b982c0220100c0350600d18172608681c2d1011200030b048010f294440d440640468103034980c2401c1480d220f88800003c100280507400c015034000440012001060380000703100c8007122403400859101d6602d03441700300e098030401c0d20001c0100c0d00600c0b103212445e008054091212440d841180c450513500d48800600020030380c840072070711060500c410f03860b0410b4081c1d65003400c030940c015468280b865500030554441407203201c18200c004008204103d10a1040714002c6400900c0100030307080001449030165a4400201c0c071881c54aa40d411202e40784852100c01c030f17070f40c002c465070a603842d050060b5400816045003005501040200c1c203241406d005172440a0034040c0030001d111410700c414002c3c01040190444460340c0102c0392000007102400480f04808800108071521490582103107180080d0a0750082c02001000d900440c000d00c120058066281390b20024098a580c1e01416552 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 45469995 1250 45468745 45468749
    0xb01060f020d030b030a051006080717060f040f080a0201020a08060f0f010806010203041e03050106050105030c1e0f1b0601170618031905040603050f0c0d0b0a12060906060f 76
    0x258025150388082c1a000341e00c079540b0100041c0640300e90b020f83e5542c041c28402446280c01e0140e540b5213052203100010800c130009001080000320103c080079503a5075407150001c007600c0c4d26481840c0007504122501968440d907903405030710f29440b4025044040e000c0d4100421100001e407500c030000d88540782c00701010030b540c2405030502180f01a00700044594943c01400c65055100420001480d4824141300c1490411009259000f450652030010b0950f0219401130741003000601c00c1c0301c0000781801c201c4c1d00350400780355601c14809901004071001e014000c451060142c000c21800c01c1c0142141d402c4550f002e545060311320071781c1c98856a201c3c52146049445565000b03200188800c1d503820700902010303c0c1c107801c403800c103489820041d0703509484212100000780b011a0800c403040d0075001d02c03600045440c410749803901e4610000c004034018403620720540c07034440781082055260010080003034031a4003400ca502c10391a007400000313080722410484e41c86107841c0001078515804c00c10342003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 45471245 1250 45469995 45469997
    0x305010b07020405090f070f080d03110409020a0216080102030f0919030e030c0a06020a030215070c0809010c02060a111005010302010f0807090503071805090705031c05070b04050a0b01060f 83
    0x3040c031203682c0030300000b05001401e040c0a403044401401c0304503410005500140620201c582d2031508002089003030680000c0c0759400e15080c507510300003a2025405840035501d5050300140c640110b81c004070700e026002d100501c030164855001261401042d00250311a5000024030646901c07948602591085500900454003408490f01c0340042d01c01c1c0b0612480031402011500401c0b000c20000b00181700c10361100340580e01415013034003095014040041342c010b010546c40700714035080b0f03009848190305040080c4400d00008420b06240c0c0981902007005401400c92030b20380061900c06010b202140c58440594407a954200d03120f2405405040d0691764180d6a0a205844281c1c095801c001c0191021081c0010f8400c003050302d4a04000d050001d110441c1c480e9068501d0b0501c00088540140c803030a42900224818400c0d0b40300099101400c1c00b90000d805440d001c4402c00700d07114001c406000302070802c00818401407100000341e08000303e0040c4100d8460341d84e40e03102515540c0c45100040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 45472495 1250 45471245 45471247
    0x110606100509010e0a05030303010602010b0108130309050d0201030212090106050a050604031104051003050f0303220b0402090c2203050c1806040b0a03020909010c030c0c0f1203020f0a030501150305010b 89
    0x24002c1d510804860600c16009446508001d803103400003030464009070000c42c010b0313540d00242c14066a1100c1c00ca40c000034181e801c121465450340b00280741d80340134000c043c000d15101503604210791007a81200c0301c1000c4040102d203e818100c011038064030092103058171402c040d0101040520f840d0044078201d99000141c0b00c06d00401e181808050040200281c120f01e54490000010a40c01d00a108040601a0146981c2d240c02c0d0b00c1845a42d1a24907014001010003070303400b001510300c0000c01c0e0450303011a440744256a8807002d0f000680704100700300c4203129018104c2494250f080700b002c0187c0e0312030b43c240c0310901c0d07800040c018561603000400301000d6a0030081a81414198420350117510b000d411680620f8036900426007c0300107450b00c00c4603039540e9100000c030b19803501c2989180040d600d04581074062589461036805030a46014044413074083c030055045000b941103901e00c0b41c4400103140c450380941c1d0050001d050034407500e104150554500b182d1140f00c0d03c41c40741600ca01d00099 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 45473745 1250 45472495 45472507
    0x13031103120d09030207120b19020c0c040b1f0503011a0903061303050706020a08190605030d200604030c030e0901120803060f060315010909020f0304032307031106061005 75
    0x810080c1c140c0007404d400b94002c2039804600921681d500e2a80300f4003e01e0740c070070303076090151040243d00540c001c8403000d14030501c4104445480070611100c89003003100d01103010b02c40c010000d40409800c0724041e45400344080700401c0c450b004005941291110312601d07101216008003071203a032003458440d50b07241d0408000135032034045000922405a000c1d2070f1036420141da594603507040f45c1c880300d20140490381100030083d1a8541000c04441a03603843e070706003d80c81c034141c0400d5480310700c0031081c402d010150329040703d264003160340c2042c404c1006c4100c80c40c031706050601810700501e84406900049001042030150704140c0d403028101c4001c00a000420305454540144940000e0901c0794003d80398440307041150780d030402031405a210854241c4004105c0000540001580d0703200d20306040c01440340940010700c00742071300e5110390141010104007482d5103a8903400c12034032440c3c0c0c45000d800304e003140034140e00010f2010061140400c4940360b8076054204144c0410b11014000000d0007008a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 45474995 1250 45473745 45473767
    0x306010b0c010e0d030219030912030906020f07060e06010f03230c0d030203090a0801061a03070903051c0f2d030204030c0308030703061a0405150f1303110312 70
    0xd100d070a0140d400001c0310018111140d0a08000514510000341c010a08000302c041a4034000d48a40050034104124140c40da01c00c51140740c0c0080311301c2855994020901404a284c0442c0c0c0b203002a0b0900340d941361020718110009040c3d207650403003a0300c1403100110b20006110090000d5a8228480541c09140180785680c4c10b28242d11001050140d00f4144900f911040d480201240c429000356031034040309010701141164690080600303a051810803c14292810300c01401c4061112400355240d0b15a00280d46440d210342c802009807160a6400e40c0340c010442515054801642d50f20055802000702111503080103843d04403024050050f0b1040c0e6044044000c6142d1114100941855900d895501c104503c0ea802940c2174200001003160030303035040c442d18015120b0001400480c0000520341c2d101401103004441c0a0540941c1c050000442c5a041d5450540f01c1f070600741da070b6000030224054005c0c092008844d4140c400400d0300c0c4524000c90142d1005441e220894102204402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 45476245 1250 45474995 45474997
    0x3050f0411040f020d1d060a02041a0a090f0e04050c0a030201120902030c0a06020106080601050301020319050c0403020a09090303051803070b04140106080706180b03010303030f14190b03010207020306010b 90
    0x10345400e40eaa800c00c0440400d00f42401124075a060000b00e000c0302c41075202009060040023000440c84d00d2040006101d0082c00e641c4c852640d00380820f2060b1078504402e0142c66003082504104000f04d4040341c0043c0c00030181c01030b14443d80c03285066801d410075180601200351200d02009010500800400c1115441684506019030000b000c03110071140c0c4c1404103288803213070b402c1140180d441d92014001e0690403c40d4a0041c1410740c000c52030b40c80c00089c00c8245031501826a44030030f854a02142040850505503030141d50002c1c0a00201541e07070750b68100030000e0385000c5005c6030910300061104501000b41260400000c4007542c6070040907504ca50310100007c1c07040b40e0721082c46186c00070710f031800d1103440c002e801d0000040601d24104100600b100d01031546195901c1005407003409a4602c0b82c007940e044030303451b08000c142c5030003c48003800070748001580c0a100c0102c0c10100f1403044141c1240d094200c0d001c05040105401d494241030903842862006905039104000410000c2d40d000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 45477495 1250 45476245 45476261
    0x609050408161b080a060e0604020906090916090c0f08240301091509170c030a030c021905061905010f0510050d020c0703020a05040507090902031f03050105010603050f041104 77
    0x60721211402c0031403800903c1c2e00380311303800002a540c403e0041c24100f2105100c0d1810240100c4001d0007945000e500040c00d0303020040803103024105140104603400c4040003050b4041e03052244811280b07844003040c1008103011001c07076000542400c07a04818900401d06a401030306a03100c0203056544800c068608130504940d180d0705036588203c0040450109038201141c00700488010444202170700304003c6a0320100400d00e2400b400700642c440402000040300c0d00c080300c030300b0080790720764003220140e040c01d0012020143c4003010003494410000f0100f080c921421211000b005c10b00d0014068a088813130900520b000c4a540c41014009440c002044201d1b25299146c110728110440d54201c05a0700244015250346c0c2c0944030038004c43c034001070b44001901050b90200120701d4100402010301c00c8503c20f141c000d65000010801c1d540380e01c4c0d1003072254580500003a0080307960b80b070094001d10b400d21580d00000d1030140882c102c2c40801740c00c0f40c0210f0300061040e0544200c4820040200200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 45478745 1250 45477495 45477503
    0x1110709050408090306060a0b0306090a0603080d1b030e120915070c08060a020306030a11060f2d040807030b0601031d0f0c06270a0b031009060905040816 68
    0x16080094015924010307144580d1140a0281c0c66401c2d4900b45450890043d09861085818500c240b10007040f075000d683d4090b03000c0301c03005402d456003024000100b920341c0014200500000707100100d14415040303150100011035408101c03002c0000c08030204c60b542d401000c00c54202801140c100b240b000050806004000c002d09940c0301c0303000710159140d104142c11222074501e80d0702040010780902865511828218082d1314601d40280069101c4103110350003000068aa43c41c40700a84401050f14204140660510b0395024404400082e6200c0e56048111081880c45901400000c06042e0340c01c5032403410081043d0340c02c56403442e1b05010001c1c81036040507036070a0340d6991050400124140031211101405ca00114001d003a418100c0c0d2000650154108005011a04619181e11907803500f541503a180c2712030f0314030000f410145856024144c90300c004001e100120310f107059031004035070041c035003080290780e12490305044e80c034110780241020740180b00303103012803410401c0301a0403881 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 45479995 1250 45478745 45478753
    0x6030207050f0d0f030506010203030708011203092102030708070f032d080712210b0402160b0105010813080a080403110a0501021b1203040f0201110708030d0c03050906060111 77
    0x1241d546a14088a0202060000301380c03400414a0070380511506412810030b1025515518080c0000f604842041c42000d44802c5905031700001d040c45070201c10090b004268130b250300c408008229a800020000d000e07417081c000d100c400640a031000030740e10100c03142201c0b40d100540c9140c0324540c14848890004035400301c0040c2000c80d1400078034800311400c2c03041c00b130261901201e00b411104201c5000b182c5092002c4980c0b0112030b0352070142c5031800440c41c0712001c2041e01030840480d0103400360b42261680c401852455104205600c9045810b0700d00c2a600c0c00c101d41ea0740c1082d40c4e020104454042e104203410071408607900e02c80c1c20110b030310a00a04080c4044465005814a07008520000b80e07030595011030101100e1032071b0b0441c5126038405a0080c42c601080135402c10319448041c0006000707103c00c011075411a4040c1c11003031544180041a101c1c0daa50316440c9035202c0d44500e981001040c540020f800d80ca5009126850040c0f00000c000c0000d540c0c1e4000540f02242c5504544d8117502c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 45481245 1250 45479995 45480013
    0xd240b06071e03110a060507120221092103071b0f030c0807080304050105061504081f06050603010f08010b120607140408120d15180902130e0c09010602070503070603020705 76
    0x40c4c200042203e040c410440001c2519007a00c0003044102a030900e25141801040000003005e400c1800020011410822107003d0311640c450601c1c11003da02d0451101a24140600c206200302d005144100607945660408003107031259070740300c0e14102c01d00034200305440c040c03030001c00d01c00c43d00412030030322504001e480c15001d9215812160000c9404423440d80d141e400f001000d0802c820400d05000c90341800da806d150804004584035500555001c241d500b2110440c8210101a0440c00c02014041c101c03039a2941c6404240c80d00c550319020f00b02c42076003003540b403200e00c0c00c02c0303069094411000c00203000e036038440c01c03401c82d0001540501d07902805401d0102003881c510a20503441c3c20000e40100c0c5a4681c0c034003454000b519080420388800800c20101008161001116854030078090440018810050f100040d0444246580400c0842c90000105d043c3c0c840000c405540c42d00494142c0340607071f40c2d280c040303945480c68024160180c006201c100001070094018200051180d000d03a1075082c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 45482495 1250 45481245 45481277
    0xf030403170408030402030c031609050c0706150e0705040308070605090a050105070c110d03080c0304030c06060902040311040e070504090201020708120909070504050d110d240b06071e03 82
    0xa902920300f0794242100005100842c507003004096641501039014242040e0b00c5510380046092922400c41d440f43ca50b0005480014107608a40f9242d5200b44100701420340200000c812001070b00926120841034408203024900900c10341d42280da10080300d6181c0400c0c4c0c5d8803400038000c05045a05607229004c032150000b04203001c3c01d842001c8035034902c500d400107810442502403610705402d0040b41544d20038004a9800141c283c1e0101e040c11640d07540e5129881c040b509084c1d403c00103410385107407580100d03400301c0380d4008000f100c0c06600b01c40001c1c030304c210404c41101d03000c5812400740d0740b03e824100014206034000360000d0f80140180ea05881c1e95514175070810061000c441c0310000e000030131070401e240030801030b90401d6040c98900e00f01401d02002c00d03c0140d022a01401c032003c07a00200f1090303910b840d01e142c5182d03800154224240741204070481071300031140115203414240070303480055041c40f0058600540cac111146466016411042000c1207864420135010440105c20a465071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 45483745 1250 45482495 45482537
    0xf0409061a0f09060d03030509120703090e0612060403140c030d060e1f05010507080408030c0a050f0f06060607111c2d1203020405130902040b010903080f030403 71
    0x2200c04003040700e202800c240704100003029900350b02c41c4551100c100b400043d840d4019201e110036818240020a5210745509516054a005603540504000544407040580c09100d8400b1641400202c0c003a540b54001003044003092061819070070b1b8071200024010900c51500480301c00c81381020245080b500d540f20500750360040f034030440f110707448481c200055070395041c03c1c035400080040205020a0103014200041d0054030645042000202d407a10030710442000326801044410b0481303641d02c3c2024112a01c40640080903030306406450480400c600c40890aa1030010341400984966583c07041000055046244155010900c07095102c1150b19821008c841300301413880c04075120319082c0362418540b04401c1d400d0780421a048859041020350100200040d0b910110340b0f1034518444004900902071648260350010701074450f1080d081803903002c0c43d116402503070140a0000844015500d038132903444010061a81000354035601c407400809560014400d1070001c0c81103608019960300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 45484995 1250 45483745 45483761
    0x7110304060804020f150304061a0a030b041502040f17070b030702030d05090c130c171303090905010501020703031d04140a0c170a0c02010912020102070b0106050412020f040906 78
    0x802c00c5031041c0400d61a040d40d20100001c021142c48101c00b40e6000340c00304070701024100900164070385c00c4c2101e4501207005650607080d4007802c0340300041d5482c14210018141500c0c155800c02a0003910300410301e50b4001c84050342c0000b2107a610a61400b9842c07410032410b1303640e400d124041d0000200d2417011109c025402202154001c43d00e49080f07250000449001900c602d2203035004000c0d0140035150101150220101c2c0c140025a903c02c0304000d481d0000601104060001d42c4010400c80040031547c4510681c0656145403449131102100790440d402802401d0160380807082c2080064800c0c120460881640b039032024403a104000450306507400c030780c4c1c0d01c125170101d40100500004a88604942c5d52040c3c540941c0030030f04101d00383c40011014122141c1180c032840c0031550f4034000d4106c0b6942d183c0c01a000707007011b211b8520084c007e4128000032600e031000100001045403250b0295401d07961900220060641c2940c20040c05011400c3e1454005450340201000720307640c1d2140b022 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 45486245 1250 45484995 45484997
    0x1f090302060a030e120a02070e1801060b041706040b060609060409060608041110090302120109081204030f091d0a060b0a0207050916050708070201020a120201020904060609031a0711030406 83
    0x81c400c1c0490384410300b4442c080480802c080300c01d204d00403051f41d0004245c421607150500071085900c1d030b00d0701140700420341d96400c0c1b030a41c02c0c0000011299284d1005004940d09000810784450300c00e0001d41c0c079210180c1d80580001403035408280c60385041001071424000003000c01d45055501c4914800381c4500e90b00500100e05a003041005000c100c82c2000112001101c14400788101c902d009001e07000e1034007019002e16004d00342e0903900c180960207a550980c0080c50652202001101a145118100d90442c0091000381c003c858a5026890401c10386248203080352441c1000600710050583c01004c8240d0107846000009903c0d09401c010601828541d000e0100d060800083c00003401010380305024081410720701010031607112003039460096000007203940c1c40080c0d000403443d0054400d0090150101c0c0c041c11494513030154001d02c5c94141c2600c081c0442a074074642952414601d10019003000c0003007546a0480b10002d03119a80055141400c400030315290742c80519682080d04004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 45487495 1250 45486245 45486251
    0x414041a1f020705040905030316020c1509040609060510110309091906080606060d021b061f05040902181b0309070f050303030405070302061606050f0f0f061f090302060a03 76
    0x2150706581404098042d1034142c50a01c000a816515039940740f200078607810400415100180304c040c0b0034448401d03c503000511070b6085255107402044694040c103e01440f0350318109000035010310b54000c00e000c50780000c100034200d00038a4800d032140325a5000500035404200f083c0c01d420340d12034404500070030440843c0c02c10a020b40d22280700715400794014040c00c0d4042801c0042e5a5110781c111202018034141c0540c599120080a174400f040003040600580036100c1000302e010340913201c604c0414481001103103031940e0b440074442152100c200194002c41d5040920201c1c500d450041070b0481250110400c0d0410381d4810031100d40c00961303d50302d0071f401001c0100961038031845500701400c011000741d80345046c9591480da0b9042c60380310007409010007107124440319107542640508036030030510521441ca800541c0c021014021202c01d013054605030302103401481042c203000c3c030911000c0e100e042508110341e8175401880102400404129400c1c0c00403005846d12400741003584080d80b004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 45488745 1250 45487495 45487549
    0x4090908031f030c170708060f0915090309090c0903011109030f011a04050903040812070201030606021506090a2007021807080705090609190612020414041a 69
    0x440d4081000158084001050110510210300c820350b00004a03070721170100a442c1c95201840a041480c55406000140200700401042d0003000c001280300d8032041d0140c41d2a0007000301d001c2d07c1ca030401c0c3d804402551007400310410074180141c2481c0c00000034040e2a08207070460002a09403000b02003001002000031550003140e050800a2400c90703186d0b80000d004681c0000b0f0702c402010b040c0304900d8072880d1110085030909030148200c4014103c440150b42d501441500c00c2070080d031010308120b00291070041c00103040781c404504142c54012000c042c41040d190350702008545240035015030070036030303540c89040c040d5004804c00b200c517280004400d0f80c41d60458010401060260100c4080c000e1010b000c20001c01c2c2c1c8401480d0b4024405d0500396128100007020074041c0c0113001c4020380100303032064202007820803803040d18201e0f019552020380ca819450001c500f42e0083d031041d600c259840c400441c07040d19181d00101c00902460030401460301300c0074009030100c0c02050b65040d6540d140800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 45489995 1250 45488745 45488761
    0xd0c030b0603070509060906120a050708070b0a0e0d050f1005012103020a03230a0203071b18020904092a150c0f1104021b01060906150c080409090803 66
    0x100d5440740040b070141103481e00d8540894003601c001441c60f4411889900060340c03a58521407403605240606d42140d01000c40c0380341c170b2503403a8120b0203418042d1191100006224078841c04403400c515140e5191000d00c108441030101e0383e40c40e610304847c1030054040c030104001c0200410340c0c8136a0109c10101d56545440e1015400c45100b1101c0b003410f9456141e940042a000190a2982641850324424901c00d114002c516580784000320543c62200184003171850f40c1c000040d0442c2030080c1c0c19212030040c0d12606508043c0315108050b01001c141002840c1d0001c60381c007500c052840503001155014080d070f02c50813800d114440b920545801c042102d9620800d030980c150140070004403403c814801444081c1800414120042030381107004c903003004000a41441600c01c52000d4402e40d2202d101e0703603442060011400303103980345601c0c10030002142102401448121010604031030000940c00f442169080a45042905c1c502e504200009264070944030318030503240580308580d200d0524003a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 45491245 1250 45489995 45490013
    0x10c0504061101060501020304050909031207050306040e0a05070b0d0209040203341707030b0d0b06041103040b0103140a080708031005010c0c0b09011115010311100e01120b0d0c03 79
    0x303403100b260b0385030100901c4180d800000700e074180c0c0c00488a46400356600603d041c694800d0980b1418045400001d000c3e031240c20030041c5000e0801101c0c03d003c0741c00c1001c0f0403a500c0e503000e4006411684004410411510800010801258850400351426143c480850700340c2c0d00684440352142094561a07021500742c00100700d03444907899545620300c1e2940001000178440c0d003440107a0307041843c0408c125600a620003140c043d000f80180c0c91842c0507050005000f201214034601550900310b0030004420600100c0784140d90200d08032411340d0841c0c0b500001c800c100c00880c0c005110702c81d10711012510b0100540700709445020403540ea8030380900701c10910800344d40040d040c860b81c4400d00000420910986050300c03a151025502c4510308401202e001200c0700da542e545005040004603200c800d0342106068901a440d13411106501100b4021a000c10f00030b050300051071210414a2980700e0a000d039031514106d500459540ca5000002c6d52080f01e0032000c80e45810310410030030401000d04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 45492495 1250 45491245 45491267
    0x503070b0a020706120b030619050114090f0a090f050d0e010c020f0f0f04060b071109060913080d020301060e0102060106110a0f080c0106030804170d09030f0311010c050406 76
    0x61101420101c1007580a951807600f40a030b0014002d031004a041c0b801c000d640034407030150700107040b43c0c4241030805100c5031b24001040f0708a0382c141800c0020a01ea022a0305084a203540603000403500e9507000f114482072038001d0134000225450310084d002082011035000941d038040c2c0c010740303150242498041c0180204544c0a410b20212005a50140c0d540c0038001c0c2c602002070742e01401001c02100081c42c40c406644150360f12a2900502007071a01c800c80140c03031500e2140d551655000380c004c042008964048800036448203015000070420300303200c10604009032185043d1400c0c81050b01d40394007a47c1090700190002410001c2902245d239040003c00d00408007810f20f4100186001c6080d80c40704810500944070300c0c00004c1420401a80408840181201100130000361303807245440211903000f4410319904c600301400c2c9c1d01404001060001c400401901e4602c08146540e850780c00c601e030821425010b0103032018110b4000da01c20b002d160400c400350354480d039413182080c41c0032b40800525 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 45493745 1250 45492495 45492509
    0x2010b03061312120f0c0201110405091b19110c0a08070b090102030403020d03090602100509060402040f150e010501090b040803030711070312180e04050705120c0316050307 76
    0x40c030107a08814103001d014260403410600c0499203001007910040b01c500981c1c01490300e03084005e84000d1065000300518406a4002e1100d44210501c007500c600884c0a80799000030540c01140444940c9100c41c43c4039580c1411180c01e00c0d5242003030581c00002a40a000480c150307a00c0400e07169400d001c05221040c084907050b031900d04101210303035500307114061141004000102c1d80c40580c0204287e40085900412081507152907103002002c117101803060b80003600c21011040b18680c0c0380d00802c2d2050b0000070007001d10780d4803502088040c0076010520700000d980d5007404205400c0c402c00c100d014150f000c0782c80100307514001c001452501140e103d5030b610035052009000385c0c08044112070704102c003440c05141040b0159140380c208400380d48000c04a22003190910b08180d0080b90810281c806034034402c0003150388180c01e8000c6841158010144d400100f01400b0600d0306818284801400d001100d50f019042c0c000710389400c0300c4c10035442c41d0780d2900e01c04115034030b000c0000724090120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 45494995 1250 45493745 45493753
    0x50105030f0406020a03060f0f080105162c0402030a0b010206011208180a05060406020c0301050604110a1206050a0e0f07031b080903070c0b1b060702030901030b0a05030106031202010b03 82
    0xc41061030380c00700180c40205425000a08011118801d0b00300c81d014094445030301520555480c41100c41000f107119148885d401e000015103084146420203002e00603503101c00350345510311582c03020317203942c202e4665904180d0400c0e41c5081c5d44481c405580301d0100200700261140422001910380ba10503402004104224990803000628210135901e0b20103100c28245049401040001c00140480d0000d5800040101e4001400c960019002c051300c2d4081d002004548c403440140801d5900c550031101100d0ba040081d002200c0c890000002c403020f840c03a00141c2d098480002411381c42a5030700c0202e1500a0005010b44001442460354000925050800c07000d2442c413250704010360162521024081c004000541c003810500865502c55070200c18000620707251040550f16030071994007000850584d02111420f80c90000e440390082010b50011424250030400440c00f0b000410b420303540101012200180582742400b494010310301c00e000303140c0390030105d03400282110300c80094030f8800e42c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 45496245 1250 45494995 45495001
    0x11205011202130b03010207050601030b070903020120010b120d02060a061401050a031b170601031a0d110a0303030b120312060904050c151306031a1009180b0a05010503 74
    0x207050156242155041c3c520311020741440682c44000d10743d4110765605540001099400c110010481e1410b0728070841070000d164a0303562007110314082c540402400b10300201c00b1945071285522000c26810008000460005811008120350500020301407440e43d208020030701d8010b40501205074000b420032403c203e8980b6043d0300c51000034400003950b06100c0d00245006c55203120b43c10a07040c0030030080a210703000030080001480c0c1c54100c10700080340602c0c100460841d612078000d5504460303808900200d1324600400b003000501d2400012160ba58107003620625540701c3d00528001540a5180007a0000616051040d04c010545080000d90020400c181120700350b15a90b40e001003056800d0403055803145891464011a0818950310400c240410150310034014018a8440c040d5403c59060540d02d1030f0503002c2d6880304080c4100c4415405161050f410301114400c0070700258074003c41d03003690b03031145103101d1000c0703184541c0d4a54a0b42c031b5107121814038540e0103008200a10740039146107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 45497495 1250 45496245 45496259
    0xd060c031a10030504020114030f15011106010905070203090307032307230a180507030b01050703090e0c070c2c04020906010c060f020a0e030c040b0907081009020705030901120501 79
    0x110070400c40b00140340d030f0340d4003040c01d692142034003c600c0c00848081565a08018018150140048a120b201d8410900700c51015501c15820050000c0b89040201001c0c2d0800c1790389005807500a118000b18070081c00000702c2640c0820591004500440c0c2d8100814203034070202e40404000300d0440c140c1e600c00402000204071094140d600036900000b400079010487d00040d54040160340006811440e40702c0c01906d06c03070954003035030250009031410003230320340200010740c1c8074000c456020340450a0b201c01000b0804944c114580d005441d00c1000d45040340300d603151030302200c0035004401440c40191028200300300c0d80e007a2100c00c40c0180e540000901c0c2c543c5c005607541800424041c104042c200c0103004000c060b4010101d00308245800790340b00c06540f403005204480301e400c07051281c404c019061a0f282810720032402400e074050404a0190303103c501c2501c0064020b088054808105c00000880200510160006521802c09503688424100005010384a10740032103403158a0440100001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 45498745 1250 45497495 45497509
    0xb070e0d08030a02040b1c0605010908190807080301060c050708011a0f010201060504020a1d0f030303010303270329060319020a0e0720030a1205040f020d060c031a 72
    0xd81c1d01074511075407039540050100103402181e001c5c17803035284042a00d01010540c60146d020f165031504041015030ba440004403000d240c14460140035810001e07401c207000d002c0244210400b4051070403580b501841d40c0e5085080d43c000da0001000480a82e081c10401405102000c001c0200384000c0c44149401c0002e455060401d64101d84038500540f00031255034000c2d0080401810300500454550361101405050290034030300082041c4a034070380010103032401c05110440100041c0c01981076a0840d0f400340c2d00c07154940310b80101c46840c8200c07520110312802200c005548685518003195020115880c400c0d01c020803250303516492401004501d4030001a0f00e20800440046d1801a4040e070001c150b441d540c0303801c0480845001c07010051520782140c0c4500002040740d82d20068180c00c04a290348901034000d482000800481d102000c14030140c00c12900180a00b4065142900fa98000f0307150086030030003144c0d959260725480c01610782510810031a04c0c0c2071101051003542000c0040c0710 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 45499995 1250 45498745 45498769
    0x61606141f06030b0102150103050309010909090c0e060105040306090303091104050402010c03051e0f040503070b0403052a030303090a0201030b030109080706050403030e0a03020a05120f120c22030b070e 89
    0x401d680d80ca0500304981c1b00300100d0640305104c081e8589656107a0400c6501c0e40d11a440060101d40d04410000d03000c00d81d84604080c2582001e150f00d120b6051000d94003050340c0c007414070360402c0810b200100100e1074034801c4034403080c4070381c40c00101c002d007520302003100010201c0c3c0ca900c10b51030401000050703600440c00d040c0c5168180790503561409181e05020300d0010340d9054169200c00803032800b907400b11010050040d06d204800b151607181d52400b0b01900d03403045000c010f25940042d804401d2009120916007504d02041002c883c0450f10b0f000880d01d180c10446540d60941d01204040065503058426401d011038140c0091000a41303546440400e40314640005150940c1c600005040c03603c2a0b02131328000c40000c007514001156418001e40c0e03404001403d540c00c1c05141829403e07940c0142c00c680c07140401820603801c10840741c1030003445c00c1005114800503201003120550704200e410740c0b00c206040b2810303011101800c2d428140c601540c010080c0c028440d120920580a54903500c219807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 45501245 1250 45499995 45499997
    0x4150f0e030a0e0910230103290a05090106170613060e0406060f180b01180603060305010f0504050604020d0c0f0e1906060e010e061606141f06 63
    0x188840019806000a16a9611001a81c080400c0081c215075004610002009088490358001d80b00e4100300e000030a00f81c0300b43c0484100070159200035806048103058000e005040000c0d406c1184088601d2002c403c500e400e1105090703031881d020610b07000f40300c000603247c00d4601221039818034401a0891941c4c004011018803008002084c0e580d808064044044560713500b80526a035a00700090340303220a03501214103a0404001007905d50004441c5c000301e554880002010f40990036005006201010341f040c10041211142000f01100341c07601001404a0764000560500d1070030541e00310744001e0440c440a900f070006010201e440040c2c040d80164040790244c490547c1e529140c10174549580c0a0804084290782c00102d07508401040c40c862012450486480032a8810002c2100e030075000c0c4802203021940054442d501c1524031751403c40380942603901c0c00102c0c0c06035241c0d5440d032070380031289691603d03c80718410155642040d040901c8144088044031036038460400c812072030090034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 45502495 1250 45501245 45501251
    0x60303020606011d030d020303063303090f01050f180304050303030403030b06130806070806030c01081801110c03071202060f040f02040603080a03090203060115080408030705070c080709060605030415 88
    0x20242c2607800e004002104000341186d03902860020069200c1c0c1048509510074045030306e00d94400749601281020b0351205080c1eaa01c194100f018050701e54001900703040461180c0b0300328a9541e5004d1282c1800740c2d05480030350025240911601c800001e802215a015810610040001d5240042a40d4000d9814200450403c4071240802c10a000c0c0100610203100c40c00c03070000700d603a4041046806819141e4400c1c1c903907a12003050660395095406098001070400c4002840b8110602400049840c100b00203e44190440c4c1d07034410ba90800b07400320324580c1000030100f04000807004c0e0501c0840040c0090b103480c1c9800d503500b03120f00384010f0001c0c050005030300a00c011540c2d40d5000201555100b00c40e0b64564080542c024010103074200c04070300911800001041c0d0402980c04d18100c80345070b0b698050190748075a24449284c002134408800c2c004180600c034001000000004060140c5000400526240040c03a500341c0c1c1c043e40c04581400020420701c404500942403a1405911900001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 45503601 1106 45502495 45502517
    0x2070b0c0a021509030d060303090e090d020703060905150103110405060114090d0501060506040303050a02010c1e0804050a02060c0c040501090509060412090f090b040f06030302060601 81
    0x1140150740054256051000c0303440086604c0b6a000042d282841c0030f449007402569083d800440c041003006c02c042c803044160900310366000b9482401060b9010f41c00c0006503d810503808007600da41d07165807503102882020003005000000750000c0000d25070b5a410320103002501c03141107034822814003000c0351456118008c0c4091a4040340710984c81c252607482045001300400404640d5035403641c1000440d62f90314400307000298004e07183d041d40d8928a900003400c4955440c1031409006c207030440d400240341610482d05d80c66560f400d241d185a222410014900302290000a50010000582014002e03003c58050307079071030382134400b030107d070343ca40c501402943c1c021140e41c840c0fa44142c0015000c5a036800b80d20861400340c1c10000e1580e40c4484d001003a00072a600710740341054a0743c8940b1454200751290b43e03030500d00c03914200300d014196540251100d1001c3e00980c1048649046 = true := by decide +kernel

theorem cover : BRFrame.Cov 45323745 45503601 := by
  have h0 := BRFrame.cov_init 45323745
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 45323745 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 45323745 ≤ n) (h2 : n < 45503601) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
