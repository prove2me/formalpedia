-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:23:00.211462+00:00
-- url     : https://prove2.me/submissions/795276db-840e-4f1a-a950-b59d8218abe8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 3057561 ≤ n < 3237417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 3058811 1250 3057561 3057577
    0x201060503030a0f0c1109040305030601030c030903020309060f04050406031a0901090201050d0902040e1213050901030b04030f26070f0302070c0509090f01020d06030506070f021504020103140703050601030f02 92
    0xc0740c00303025101d013048400e084510810703929042c0c1849086603580f42c1001c072601a60013540c0d210303541d28000d0300140540e00440d504204251410041c07202103940031069804800044860f50b40d102c054040c000984e00070350b0425548103103040000010000002d0302040c180c502c00c403408005986440249003240d00940c0043c2c0030410801c12011541e84940c030010781d040c802000040c845000b031980d1403408854524048400000180c400d5561500307a0455004202c122140c82256055554071070954801034001814000c448241c820150700a0404c0e402680341120701c40d810001c2424281d04016064460002098107503030b42c2801f0314803900807142442d0300101d00759401c92805052000400004102d00c40f64000e4910b000b603031003401c0c00149a0401900c2e00451510308609040e070800c6c41c0a407611080c043e046225200441d004107480103019061801c1800c5a62140010b801400d12100c060742181c41001c200b086150701503201900801007030b0303810800c0c0c90b202036a14040b4400d101c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 3060061 1250 3058811 3058817
    0x6010302010f0504060507032a060f050a090807080c190f200d0b070e04060b040504050c07020108040b040201020312011701050703020c071412010204080d020c0303070209010302210303070203040302010201060503030a 95
    0x420180405e02921a0385109621007a2140b440301c03189c1e0b002d03a10040c207150125403054039010714000c04007160184640003119294200148442c540c4d9910740e620501c00000c3c0540d402241d1f45e420b8980500010521000c04100d14250505034030744030002a909110441e01006000704d0f083d6034080440b01420043c60240c100f030380300c01c03440d00c5182c408400144800c0030015080e44218490b140c50141c84010000400f60549803810001000241e520040c65284014401d01c009800b5030384c04050180c120350407040c4400340d5160b90004030704520610403840907030036100d8000a9544124034500081c104540020482602c60740c5044040e481030234038003011944450704c144030703007841c0780d4a0785416080103107140d10740207040783d000c2c0c20380e040f41d40808040d0304031801d000368454040c8440c5003e0003007100034518004003a400610f10420600010703008104110544280003070baa04034240421702002103a03100c1c940068029580d500c20b0104030b0043d420680005600d0400105407200010035032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 3061311 1250 3060061 3060067
    0x605010602150406050a060503030415030b09040206030402060a090b030c04031208010303021b010207080106080c0307170a080906070b09010501050114030408030703050903040b070506100e070e010503100306060806010302010f05040605 103
    0x84c903008003500c0d0241c03841014554440d00064240d808000800c02000c01140c0d008010b100001d024040b1070000203002d020b02c410404000c0141c0c0c44600700c80d8440c0c0c0c100d40c0940c448800d00801c40341c140054001c0043c920001040c08030f5052400003800841e41302e10101d5504d40404c00c402c440f2a07500f84001405a400703416901200a0006002180d625042c812104859901e03030b18242900c14540c4502d0098000b040701e8000d0341002c0c04454003900e40d14081c04210420311048035521000d131000506103440104545515981d00b00488510540107800b908290400c007280c1c40c02813400f841018086070031011248140313008001624815600040020b00310394601a040e400303403000620000c0f07140030401c80460b02a004202400e911401030780200280d00e041c4204504046071030300030f510800100c03420011107a5006603d03007205802861307c1521307910f80c40010740314281283c00c0100540c2c14141302194030100000c00c0e9048034005d907034150100c40d010f40203440e5840b413800b480d00029420 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 3062561 1250 3061311 3061313
    0x50a1e020306040b060708031b040b090907050d0e0c010e0102010c080a0903020307020607050102040e0703090b0402010309080c0706030207060f09020a120f060c030b0f0405090307031209020904030c06050106021504 94
    0x1580074540c07014000e440400c030b055a41d00080c10980c828003003121514008000d03c5210600c2c052040341d03000130702078030f0b51605080c0030b48007981d40204154144030710342e0980003419440c418420307103114465660f0240000c0c00c00c0d0b1045501d0389403101d1100e00003050130700890700b15071050003142c003810003540f21602c25845110308175024003000c11060f02507200c104041801a00d54400a04803e8003410005032224142590710f004400042c0c0628100360400b0303005808074081e888115046982420005240400d5182a003030501864020031414040c01d54005405034041d0018480d462140b40f0800900b0449040f04003150002c010107034000b41082000d1090881c400b4400701150300500180800c015a550f41c441234980661603e00000d464400b2050a418031603002d40a10740b00b01e41c140708a140c1031104640c0ca0003091009410010080c0210005405550051100030340203000503500340b4150801420038035415108585032450701000003615440452407819000040300300000544031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 3063811 1250 3062561 3062621
    0x2160f0506070221030705010c020a0c0b0c01060f140102010f09050705010807020129010f02120a05090105040503060c070c09090507050d030e041401080d0206090c100c0f0602030406050a 82
    0xb081e03900300e0b00001110007070001d03812100100141220020001c5540703c105240140c25554685400b40030755028465000014441481d4a0b0980b0300082105031100a0702c8401d502404242d40803110010072081b0128101981602030ba284003402e800a00c039006602d4803e00c110796813018050416042070070148040d6104042c0903400207070900c0045010358015180340c1110390780f100959401c07641d001c54102596005160600540c810340080e19109000c0a407a0700a40300b5084514100a4000be81c0c0e80c203a03014005480260030094200d80039882d01000071152980b080034191003800000c400040c441443d4002d02000320b0380301c5c002d400140e14210910a152200360f000710140304842240c180746440c0ca00c5000120307107c6020058107035144c6460316045c4030121150500319088a4108111b40d180001c002c00040026102c0000908040d407046804040380a0010840401c604d09001408070540240d802140140300420103500e0702400c6008503420540364201502081c600c544030220 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 3065061 1250 3063811 3063817
    0x206190209031e03040609080d020a0b3705090a0503040902030a0e01050703050f130c120201030219020105070f05031603110f0a03050901060f1a070c0b16020102160f0506 75
    0x3014080300d100b9200b140c11083c40c006146184000c0390f02c0458100300880e4040000380017064144080c10381401012802901d40400071000b0b0184845440814400b516001c8080d001403492003142c4004282140e5000c50710444001038441c00b130424002c6041e17408041402c6450780e038400011440e25241c600440040c1d000106184042561051a1a680c4a003801007070b100d5800c0750b80c0090285402c00c984102001e002d0304400240c0100044540058140076141d01550690600002c1900c59480124064402d0340d00a0b02c60f00304060100d2040c80d015049140135951948800381c0344610400c040340d90b40411a541012032845040f100c2000c1c1c043d074068401003640c01c6000341790079101c2003030b030085501031380c515000207560724100310101e0028070030000039008070350002003814038225400700d24040003c042c0082c1c400000b954002c0107410110304004226045910b034440e01c45400c429408008080d00303034058043e040110f0a000780a030051400c0c4c1d80000502c08c1d65500b01001d000c2190 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 3066311 1250 3065061 3065077
    0xa0f0e04090f0501020903060c09060f09060d021909050301050c09060c0f010606020a020a05030c0102030703120906050103080403060e0705030601060c03090302090a05040c08030711040e01090b1f0602061902 91
    0x181d54510000110b400014104038050180c800541d13281c800d08145460104024051348490b071042c0040e0100c0c0d03840700c0403035640104183c101074032f81e1460700019030b0a10900004c030741c159100040c0d101ca644150b42d01441804140c1d141c80d00307165501d109050a0320011110080b0848003000090490320303005000c0d15504521008070344c4031600b046082821507120b80c001e140035070310944c0000118900400c400300501420703801341520101274000030b9030f03030700070204020103000d08803854807010b16195000408040e003005090010356540e0030b050200703034054042035483d035040c00041412a14001561411500098000d2500d603180100840348803400c100b04804102a0300d500002690f10f03144230380d0044500d403100140c582091302e0100301268041d8010600c540062080d100402c18120900072094800e903408520b04103000200ca0042200c500c00130101c2d1800c00c24072002070030a41d001104808940348010a2644a1a050380e46000454484941c00e00014208402c0302c10750300941582 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 3067561 1250 3066311 3066319
    0xc0302150901080a0e0a12020105090c010207030507030303050403121109090f04020a170709050f0907050d0302060103061e0509010903020c0102010e0307020d060b090114040c03060501080402090402060903151b0a0f0e 95
    0x914032031f07583c03070303280240a540700005039121401d0000c1544180184407040c0b6090000307111480c07071a5501740e00d64040d0f00c80541855a148001000c0c035000c4e001400d045402c0400c1040000c0f20903400b01510741047e6070590007204c00d240082d030407030380040d0784e5802503400928440b00c030351402072100380140e00c86131a00c1c0d0600441c480000d2813071a5002d00f90041e442c16a4500b05440d250701c02c240b03000c21b15071000340306070081d50035070012030340111702c145c10341c0c2d08941c1c0407a98121015034079000140d0310b403041c50528640020400c000c0c80660004007032a100b6403d0380c1c40284200012402e884150200703e825402c1041240010f141c2400c5901e0000c0c403901c408110010304100251450900346d005e2124003210000d644607a1410788201414000c01d0b0504208090820b80000d01c00d600c01007000780100050360200c0d040d0f507200da003990301c500401822a69221003940c011011300c08156942051003004030b620801c081801415146518180d5032032080c603a800210450340301599880043d04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 3068811 1250 3067561 3067573
    0x60402190e10020106180507030b090106030b0f03030306011704020d140a0b07021c03020c01060806010902090406050301060b0901180503060a020c0606010801050a060c0203030f04030c0302150901080a0e 89
    0x504001140c038000c400009032654029441e0040c00c0c0074001c80c0241c0c941c41164581441400b4044020030790a41510b24040300049a83da4800309400a00700d640030554400c400b90000980d1540c10b0b080700102c1c4506807a0088040d88141c00d040e5203001c03d450303a83c041001c3e15030f1040c450651462030b130381c8180024421081c021040d118085003102d103003121030a44d04085000d006000c10300c01c450b9002400c0348020141000c443c2403501c81c030a14114131100f055000140356281400940064015150b8502600e032a0b5948444e15002903212000d04c40c05036051040000340e92a044c4a40011a4885668107181c65911001141c82503440d00c0c0d15103016001590204030740d10100041807090b5032444d0010783c1d68000c20105440c1820040030141084030a2005002584400c0c820074112212818580241c0c0300610003e800e5014407000504e40380008100042448004019401107038000d50300052081509904001140308112141c1c0c01325091074049014215251302400b810001c01043da04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 3070061 1250 3068811 3068827
    0xd0603060204030303050603120405090103030c02030a0b09030a030b06071e080705030706020a09090504020f010807090503030304080909010609031703040f0515040201030e0706020a12050405061903050105010305010308070209060402 102
    0x30880e00680c0040c0c0000c2d50714804c114460030100320000c405030740d0301e140700c1c201803130000005e580c60380501005040242c840400821510204a80d400b0240c2c44009480945016182c495036a0000c1c8204400a810b03c01c00280a04048089500d41c541000b40041c7c0e6035a841c2c00180c51000606003124000010400040400c40500c05042198810100540c1c4e5120700d420013018680c4a8000041d43c0d4502428400142d5030600b80020f81c5000b0309012a603980d81c41004d540c3d140c115070105805010010811080110718402481c01440031900001942d0300d809048075400380602005005043e1140c0e0b81e28070408072400b460b4440c6c802c0301ca403c54000d00356180d60508001542c2c400d1503002c14400c3c4000c540c0c050050903420b0100100811140303103010030081d9031710001c80007d4007800050751214007043c03054089a024000c00b0745040d5543c68845c1c4907041104050402c1c600183c0f41100215403584280102c0e0b040360342250455080c56855001c101c10540007078112a405542007003698 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 3071311 1250 3070061 3070073
    0x209030f030f030106030506040606050a080405030c0a030908060a0507020a060902130903030203040b070509010225050909030a08010911040303030e07090501090209010e030109080301060810081e0d090f0501050d0603 95
    0x40700000c02502c040c0c8075490b1440250a0343d0025008034412400c2003404c2c00b4003a401020744114400c00e1174000d009032940d06040e810341c81010980d03540c03800783d4600c1301c090540107208441101d000d1011648203a903403c00803811201c080e2131000058000015000105206410041c0304900003010440d055540c0c1841800315140c43e181200401e8011003044140078280400542c4a540c900f4018501100c140c0002d41703031040c1c581414060791102c200c22001e94a402d0309400600400b134400d26643c100940b080d0b68a811101d0380c607000840803030020400403814011340303c05880d412100780c00c2c035042d036030f060700540707000340414025200c0c0020018516005000d294000e000800005a0f903060500004000c1107909180b04d000e40e04001032200002c130740204480c1116810b260941e507585520050200300d500b03d44c00007240344961448500100201011941740c0300480044544090346c0100c00c0e00d1560084c861300802e40d02c0e40400b00602d50060009008018071500000742140d102d580354 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 3072561 1250 3071311 3071317
    0x170102190801030515040201050301050409050f0a1a0907030c03020108070e03010c0504060311130e0403020715020601060801050f01020a06021606090803040b01050603040503070809010e0d0302010e1204180209030f03 95
    0x1030340010009401001807010500c98202101d40284610020745000d40002c0d02c1c600c418031842c0d02860303403030390758100303000c0107100c20042c0c7c0c21450103550101c5a00d0030304400985d0180d001d08140342c4418040b400c0083c000038203c044a030b0003840800740c00d19503001510481e400411a0041c4287c460412100d030f87c00b0310070680c401100792980c98480e0b040c40c17001001c84915900c4000b0f032010811515400081100a580480c1c40d60040d98803559a14503040341800055480711032001c900035010b10718a60003080c0c0320f050705c5007030784d6000180e1707602d000700040c1003000c0c131031070340036804c40b1400d00c000c10466001403210f1020905601c0030b00d4220b61b2840704880d407504003a42c3c40721020060008010492601030f0040104442c02411800c180d11095101d2003441380040c0500b6000400c0101640149200c1e0640200180300c00c0e0510792600b0042d01900a11103458002c1c0100e402421540a42d81d06440580c3c40c01040c02541c0060040d202c0001d6202503141680740c07049010f4880324103c10001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 3073811 1250 3072561 3072607
    0x4020d0b070207080607050a080103020d0201050c061510030204060c14011d1501120c090b0a0b030a050910050c0901080903070f03090602010609140601050306131514030109020109170102 82
    0x2030540514044c0b445040c6400607040200300202001250000355100040b00d040d2a01150750321601809440140c0700c41c8140b14045104e4020303101000708026504481900c00c903c1501c0d0200030500c40c00c0114101c1c42540241b101150803044043c0214200c4283c0c58110030b9110700000d804010200c1501100181b1620303443c135a0306c004c0c100b0301d50440c0354509500515840c5800310b454001c590351141214128041d401003541c2d5005e100049a54210500d0001c208010196640f4144400b140c405130008982d0b07960f00303100b590f64810010049200740740c81040024003ea0034990301400454101101400410b210b1006100c400003081800070b83ca07440307521035181d45130340c2ca18058009e400d442207035106a82b00c80c6000c40407103c1109120120b6441142403a10507541d03079840000940410012035440720f610314051801016610b405020001e0b02c0010303501100e001d8811003090f01b80c0742c034080000d00050b0340042c1002007014003c000d003124601c0c84005410f2064020102d40c0001507115 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 3075061 1250 3073811 3073813
    0x510050901120201020705030a02010915021603030906080f060112090204020409020a03050403020d02030307050a080601050c010614030c04060803090f06070b04050a0c05030102070b0c0306040906020301030501050105090108060403020601090504020d0b0702 112
    0x382d0208541e01000b0f400011326040c0d019250390215034001078251141031141d68000054800c0d1410282d209000c403a030001084c10302410819102e06004100111b0360152601180640300891000e0020382d140754840c40781603481d001207507148014600600041c1c10120303040b40c2c091001282258050000d807010340480e9a0001c0e0302d180904000386000d13800d55901d019034004005102c0410350000032141c11036914101480291107401c0125a1449100413844540d460400d002c1426840d00b00c5410380d5503401c50460748040d01c91810071088031468401c0d06050f074410403500c0054240480806549100141802d05052690311105031444088408035019084001c0800800920061400207484c00303400031801c04035942c0c1c03504400000074203d4078906d640440000c89035075031500030111842e0311030419500c03035035640b500c0da000c0d000030f0007224801c1c06c030780002140c8203000040d6144150b40690040906929100070311000700781c080c1050740c00c9413240c074484001c2005810060701688540d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 3076311 1250 3075061 3075089
    0x31002070c0e010803030604090f050607080106021204050a0311040603021305010906060e060a2a050c041a0105030406020a051908070e030c0109030201110109050105011205010c0306030c0303030510050901 90
    0xc03528056001d034980240d210940c1d2500180000d080010659604c03038000d56001845401508001d245c640c0720090080c0310744a210204921582d119000718100c0c0c000340c007200c400800031110405a4000c3d0301031a504030040007420008030345400301c100b05003040a070001801c152070790041040c0601e06840010940e8440c4010801d807a480c3c41000b00408840c0750001021645400140c0148074010321941001040c0010b02e051048400c420081c221207400540325000203498480e80350845500b05c288500d1504140244000812150b00300100c0140e41f0303207284d40c3e25075035003030000e42144602d002040300c144070342e41c206200400019030b00512a00c4120b003603d0200b000070007840c41d0401c07850198014044011075a40c1100074107082c0e90742420500049208145114010003010a0150180d803c00e4000622840c810a4600599020340024844082e24150a9080e901144001031030314074080070400109219034005508070340c100d403600c54915600c800003a8040802c0c1c001300c0c3c0b160b02d02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 3077561 1250 3076311 3076313
    0x602070311030d080103020d050708030c0c04050c030402030601030803181006050310090b07050715091103060903030c03011203030209030d0201050a060504060f0905100f0807090e19020103020901020102070203100207 95
    0xa811002040402c030300a014840d10b1002c0140103d0042c80b000303024000c140c0c1114204141406090702410700102202e0315021100d20403a540c02c491402d903030050345000d02141c14002014116449160040d0060600b646141d890b416682e00c001c01c004031a11310710f20f1b207582e840c0090003009181c1c988050045604d9081208160800c02450030707609005207400c402c40c0000e40c51407045070f841480c0d030030700e1a2200d059040001c0e0728482c040b542d405061401c0511420044d1070368000d080080e054007100c4459542405ca140c1c0e81c80140c8a445049000740010409001c0303058800c40f20a01c40d280150601007050042860706175400c02036800750351140708101181c010780c4500300051030304840500000c0c1c5008080c00102646000c0c58000c42d4885002402c6180110f600300020503810341903162082ea076151281d100c48240c0100100b503801d00c2804105a40d00040c4001800d0251f0004e81d00c2c21000d034010740095000f6080c09055540a002d4900944d80900c9880c1c4101c032295009030341c849003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 3078811 1250 3077561 3077573
    0x70903060b0405060109030308100b03040503070b070503040b0a09110303030a060504050901021323100203030402030c040501060e1207081518010204060c0b0a06050604030501090c150c020103110d050106020703 92
    0x36080002d010300d151004004d00c40c1e0744110868112134060a00b00000e4031414031404200c04a42c1110b68403200000034071041010010003860305900500111001e520752050460305484260b40140000300442c001c00d0b80001c03194030080c44544501002d40100240a0109003143c000b120364145541d40c80f00108001d0910b805115445848500214909248000304a8180d03482e800f50b40500524100000c3d1f051154404c40000d40c00014003030407159015440c025900c0d841143e04074024041c08940c91410b003498040d6034140c96050301c856651005c6030080c03098aa245050389000c41c481d011000841110512601c4d00481b001d004038280c40c0b910116180c2c0c96080d8003102c058aa10400c010402035901201003071000d640710f4070078040c90303d82c02034010181c100c0c2d401c07032507100600260000411005500c4885968420340310030303050740d940e04c04e1100c80d140e190031030308041011a845c140056110f5441380c4c2510700d142440600704111400380d082220307c04d13003180c800759000183c24024081c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 3080061 1250 3078811 3078821
    0x9030203071b05060f180301020c060a0b0402030f01120203010f020307180b0403050c0d050307051c030506090f010b0904060806010303090f0b090d030e12061005040b030307050307030e0a080607090306 88
    0x8040c240c0e0065030301e02000b082e45072060348043c5c00b0840b800301304a41e0101e01c031040d0882c003010041c029500e80d0900c0c100070341c44081c20740d12102002e150003090b01840c181402500d10516944600c1d80b11607292200c1210300c0c0c90ba901f4103da25540c0c4800084800180e0b101450050f2844d990710342038031380b00c8a070801d000717607841c0c0101104903801e10042002510016a4000f800d5082c2e41d131658402c0e0b24a8054518000c8600c010800c1c02404400d0750400368400442102e50026075040c8415201d010501540500641307044c03440f4030401d4014030400e41c20304020700d0028805000020216a22041d0508014082c2c00c01c50020300d0382c010800980c00c40e00c01181c0500300801d03030245021200c03c00241c800003034000c01414444118901c0040d07584503d09008000705c65002e03a42c645c41d2410f080c1150703800900036948100e18203e0010f045003000425a0b940a07440401540380c000540c4056079120f06107180198807010910000c40d05031014411140102c490303841e00c08019085141410070340d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 3081311 1250 3080061 3080093
    0x1020c030114061203070b0a05060109060c050604080307050d05010306020301030b0c03070903020d0201050403060c02070812040803071e020a03060903020c090906060904030905030316060b0306040323040302040903020307 97
    0xa070500e01d95072105800041c48542060045850f40c124040c0130380d10504500800d00098440d011410030003c800e14517401544c81080266251060b094540304150b8a4081040c07025246c1e5110400040020715040300454010045041c0a810100c22106401c16180300f60811035205801100400800000303104151308000e81d551898110301d030400707004180009511000c0d105142040340d1a065900506c210750286410010911000d90b0200004c1d5507100c15100789903244c0700b595203105400c00920291810382c0c14141c0038601d4028180c49104000f50694802e8450001d000100c00059580c0d541d00001148103080101c0c1510041c10041c0c1050740304a19140109115810000c0d182004101e00b81d1000d41140e034401903480342d083c1151026500c1d002aa014840050060008828804a5a091440b510040c03101d001400141a1142c00598008011440030030416040510004070304091680c0691418201540c2e40c00103000d65080e8601a80035801c0007032100184a22103040d44411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 3082561 1250 3081311 3081313
    0x30506010e030304180507050c0a03030b0607060516020d110309090a020409051608010f05010c080715051f08030906030c0d09050304060908010507030501030503030711160801021b0a020109060c050a0b0108060601020c03 96
    0x209d030000340107a4850140c0c0d100102051355808243c03075a6500e15098440312a000507080041c3d2400c43e0b4a5201d080480080744058410444d131740c64440c1c0700e145401b02d05005c0b040554201a1071000303200d03106001600c0900f40e603800b84408103000301d151003028440c800c480708902412002d07481c0a0042c4c281078100302440c00300c08005110a903000080e05040e07640c060f007000e595103414140005000000c481c080c1e180303410a0180403640c543c103010b050740c0607d003c080200c440c1d070300e4210f0381c1da034403480f040b05821410600c00103640550390130140055a20414000c10488041e40c4d41ea03003554055007003040030a42888040c003400c5004d100b17091380021203040410280d410b5440e40b40c2e40b40001400d007030400c40340c050074040c00303035041c400305450074000d45c10886c4503500d034410740703020b0b400402c09944944040501484000000101c80a0142d0180c656542541c10319008851000001809449a01c00c07444120b0000382e524084c00d00070141075001c0d000078100b1400081c01e004000440a00ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 3083811 1250 3082561 3082567
    0x5100507050c060d020c010504050f0d0314160903050f03190e01020601050f0d050715020105060306010608070305150306100503010b0316050f010306080f01140f0c0307030506010e03030418050705 86
    0x1407400524071190450841c1c03103548410412804002900c541d80d400c007195420300781800104000010191241403510080c1c40301007500e050210304039034000355502e84c44007030600400c0c2003200300480308081940307510f004c040c041d0f101d448240c904071a81400b48813950000440c030f01001c00100340d54001c0d06172803a0000205030f414000030341d40c26042c0112403103410708082041103a5554044030000d00d9011b07040c0c1e00000da6421150b261007842200000c099401d080c00500716107800300300a0306a800c0c1d511082079584415004a008010040101c049810040d1a60f9110382c0c04001d150b1244240c0c2d25060882401c200500d425a032849a0380d9000780d0102c803034000d454800005101c15500c0544400c00c403480003000403401b81c1200e40c00380e00940100591511560b40c10341140440c0040681001c1858030b07255400d01400000702c464410640043c00801c0a891182d0025504260140340c0040080c181800003070659201d030340315480c0180707000041000354105000e4a0351000960400a007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 3085061 1250 3083811 3083813
    0x3151905031903020309010e04060510020102030109050603030406050403121803050610080c010504050103020c01061d010801050708040305070b07031401060f140a0203070f05070b0d0902030c040b03100902010e13050105100507 99
    0x1540340150b840340c47c1480b0825002d600241c5641e40301000030031005040c00c000c01482d900c041c1c000d40c000c0c02001e664908101c00a60903050010444040318595950140340038555120717980d01c545810000030410909000700c01305070400c203c2800245008902500d440c0c2841c801200c80740055500800c86038000c90160200e5a821500ba0340c221034080c2009a51401c007140c40343d00400c46a080f03401003520050410240c502001515416209000000c0049840f2054265000f0300101e0f001400114100142c80c0000d6041c0c180c99000070240c03c0106070316409004c54031490700260000d000040c5500b244011859100c0c48031900081c00000b528a01050500002d4680c4a800030160100a51407141c0080010030030000d00105400d0300c00c95181e00b10000d42001502551409910070f200c0e05940c62201d00d000c0c461200c40103801401081481e440609810140070480b406905014031150007218030303202d84180d0740415040044c00100c640c180340c03c111910480305482010400140300d108 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 3086311 1250 3085061 3085063
    0x7080909060315010b0904150e0402010909050c03010506070807060501031103070905091e0f0a03090905010605031311030109020301050c03040308100303050307030f091208010801050601050c070b0315190503190302 94
    0x1d8155503170601c00a55406855000c90702415000d1402800b420640c038001600000680300786004601c00d0780d814000c40e94800d0302c1070540b0f8050303c0201090b0010001004289040c20040c80154810304000381010603a0326041c048031070036441910104240c00c0200010702d0b0070301c04203000d0f00105200f0041400c000142c165100380031244004c0c0c6111a14846c5840c1d030080080c0c604402e508421a4814034503841e0091411f5030394895a2a018101400032660b03030301400649200302d0b0142c0390081c000455440700c4055407894100d95801d5580c0e0100100940c40a029091060b89182103c603568142850004c08450740205250060140700400f1f00000e03501008403a0001070710310f4003083c1c0749006041c0300024140000024070780140017241144090700608424100d4104400801c4907589140041d5514440d00d010380c102504100010701044200002440d0014070034020b80c1d1603542c3c2c2102003400b00e002030b900c400100542c500200b1040c6000c1102503884c4e0a903800da086071141c1c41c1d81c06 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 3087561 1250 3086311 3086353
    0x4020f0a080c060706060f03030203040501030606110c0d080c0115030203060105090103031b020102070e01030b040c0801020306010c0f15180605060f06040603091406070302090a080708030a1211070809090603 91
    0xe1803156400041c0013003800039542051014040c01803031041c4d0103a8914002c1c6d40c9510521615000c6401c107a00041c50074041c1311591144200d1001510002e80680100001000154000c4901038000c2c0f2042c02051001d1044d0710030140c58054030382e40e1500b90f004241c500841680031611455901c001030000aa200d0342e50100c0344000b0f11032a0344c0100c0c910050b403c0540c1c0d504031000344d008041c0000184012840304500550040c80000c4c03003030b62100e4030300d401d074801107400e00c0c00300700c0305404480056912016520094060911109030440070540d94043d00d04200d868003070303104001c4c11401440014402c0940001d01202c051031291429004181d240c0140d114440030305030303980c0358001800008813100f078511200d070041c2c0e10540780001e401f4000790801c403142d83c0243d035080400f040180000811701c0c26101e400f0006c5041648080040302e0021018000c500c4190b21390445014444801000e000d080388214105600c4464110600c0034030400103100034400c0e40411805200c82c1c07402554 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 3088811 1250 3087561 3087583
    0x1060203070803090f060a02030a0b010c020604050111070b0a0c03020d020102041406030705070506070801230306010e060604090e01020304060b0906090105010305090a0803040b01050108010e090c0105070201030e0f0604020f0a08 100
    0x5542c0703980d90030121360b081c0584a0350305420f0b401218200141412a60300a511031900d0103400c00504c141100110340d20400309000942082c401c01c024081980102e505802c0c8036014011109c2c1545c0f2542c040040b900881e4401010070f9101c0084408c00d0f4040c031a10340040ca051008604141c50484d213040e1540d004031503540101c0b4000041083c0c3c41c41107048075405a00030007203030f42d581171010b4001c0100f20301b4410711050004200741042c0300996040c0001d148240140109040d909142c0000c00c2c0032409805658003917010400003031110303050301a40e800d40025400042e00c910309400d0103030541e000c40315114811001c89080000a41d280e2080706e054480038030380020583e0310710405910b0181091405010203501204101c1002107101d0361034183c40085e41d403400c075a40c2e1481c0000d020002607910016a41082c9412044d651045010780ba0683c014900841c9040030929a075040c01078031100c00310140c200034200010760601203401c0303000c42402da0b54000c2d558944106a40c40340c0c00d401e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 3090061 1250 3088811 3088823
    0x30a110f0405040218030109110909070506030c1b0601120b01060804030c0308040201030f020d02040504060902070201090603050c0f03011401020105090c0f0103051305010c020604031107050f011b06020409091103060106020307 99
    0x35402c0c1001a4003a0706000c5d504094001c0187c5400b0b803c003040112819030316a88181c4850000840c00c29010581004030740c00540003d04649614070540c480b50414202c40740c4206980300503041000c001c205c014001c20400d080c80c0310f51000c608100401d101e050704074005010f084010301000a074070056000410390903152807803c40d165480102c0c0540720400a0101103800410b00703841e0314401d94000c10482d241142c00700f0407690383d101510281d00a410019000c15490101080218000d4106a42c803450900c0c04034030741030207544c001d21103410a27002101982aa510300703408030758092003581d401c8035401000b49010043c4e140000c041c80202800b443c10152500086101c1e4100c24800e02070720b540c09030081c4011020100020740d15001280e040c1c0004840d41907401680750f0118440040e50702c05840c100342455101d00554101945041e144080300c1044002070204600d4409400581406080030418850310300f0f01c8141030038a00020340c440e401140c0100a003d40000444000f954060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 3091311 1250 3090061 3090067
    0x1030314031503030301140102060a0506060f030c0f0a0503010501030e060124050c010606051201090207080708090d060e0706120e0607030902030709110403061109030606011103070203010e03030a110f04050402 92
    0x40d241a003802410150302c0d4051102000210321400c403c252149a0705084c0e00b114a6552181052410341e0001e55506400c01820030400320030f1204040159800045128980d141402d070101c14106680f04588900000b40c0100042c0f01d03d603898042c40d10030001900003440365504201044802d00450510343d04075640008411b204103018400790360a0f200028006c1040315074600c0c3c00b0b4059809800340c1c41032512140c0010401001d1842954a8a5048000c403800c1c040c050762000e07c4dd9010103260b0ba40322800c601040c0009405001d4007503411800d03000b401c1201c0c03515402a05070074460808030200c07400c20001c03084007000080d81c9540228103280c0840d05074910b001003810002150840f20100c2d003003100600348050954020070440703114a80800c0952540411700c0064000c12001d503501d40c10050101e01e041d88038a003031700f98141410741680d20b00700e4540d001908541d89005002e895400100401500703850f503129a50803243da1411041c900f01e0600c901280c54801c601a0a12440d404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 3092561 1250 3091311 3091321
    0x601020106050d0506161107030201080402060d0f06150c02031011090603040803070909020a0507060b0a08010207050a11010306120803040303091e02030d090501020705130902030109030f0306060201050103031403 93
    0xd4020000034003010f009540d201c0f0250030303c2030315500100ca44400d0110009084102c640c0301e4111030568145000103030039260b05603401129007140150007070b680b040b002d00204800d03214034030814107240948480050420b00d84115910140d9002c40311800784024580b0040141c3c8010641d0019031162000010b040060601d641d041402000b418542014001c0208170420000900460140a140d107840032450381d1004146d09030704c2480c2c04980040e00038001c2c0c2c000103009812804000e9002481c10700050317103440145007241c202e5101603855901c0b9224440c2480b0340020075194008081c030301400010300b4905901000104020014a03040c000000102890321a41c03044628903445100fa034843e030344000b04102c1034001d01d1800c0e8464010704c40d0004c040d500a624903000c840701a0003405005282904001007042c52403111035500c0c1d01c0d140d040005a80a110344d804542c40b035182d81280c0d035030440c0c0c010100c03809500710501756858000180302081e000580c1064007550002c41d50750307c0d80c030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 3093811 1250 3092561 3092563
    0xc060509030712020a050c030715030c02010b041506080c03011d070c0b010e060111010509060a020702010c0b070305041505010602100902030102090415080111031308070812010303030501090614100503060102 91
    0x5509030180110401010036403e8640c00b04d04e038400b0368064030882c1e00710001403080545079174940c0b061a64008804031906180d600940003146650903500000440000100119060750100b118040492a40d80700074050030b80c100e0b0029030058210f010702c50841d8141143e08081924520b030004014601c08d001030700c0c0510a0707900b1542c49500c45450040c030350350b446440c4800081580d10038046080039955107a039400502c20a031103441050018401510fa010320840294843c403010781c1000842d9904a01040000c80c680f801841315030750000d081e241c60309101c0102c420701c0c1418210707a4100ba0040203500da0014201d004041d0550000800500ca480003d00a20030185400d80103400e00403200e01c6441001103000c100d500903c003e0007018042e0f0300600d8948803c491502c0c40150181004011078049000b0306103440c441d60041d403902c490b480d131342c042c20102640304400081c1c07990f005021480b014003c000092044200169103000b602002500401550100e80108500880013440c2e6a00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 3095061 1250 3093811 3093817
    0x602030c0403241413030f02070512030306010207060512010b09040e0d1110090b0f04030207080303190f0b0303030711011e09110306060d0303090302031308010c02060601020705010c06050903 84
    0x182c0698035007102880003403c6903c0d5000003000700c000038a0a050303c0ca00c00d19500c911482030641c1410b80002a000c2c0d0303810b50f6481d0046071300c00c04621800d10082080c0e240c1c55202e03c040320300f0300c00668803440d00d6000286080e0041d004241009000c1c000350907504420000141521890000c072520740c03071381c00049001041c40d440603492511030f01d85410201030b041030818003680040c0065030344294020305c0d85030949178100c030004d14518560000032112190f8110082c1c01c2827080c41a18125580d460314240303075800948000b403c02030b101c12064219011031107540e8141501400621050030302d140040d80b2404020080010302900040c07058540d0b00a501c801112054140a820354140e08036684000307022900f41110b40440a5075100114078000170402c1c450500200041ea1320420742c0c1d01240608030700c1c5400c1f41940b00c180030a07010340b0302007107440014050341d500003d450349402c10028078298004e00f5007415500820340900a99070b07c883d400c0e0155422900200e02a1202d10042d45944 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 3096311 1250 3095061 3095063
    0x30601060e0d0210050a02010b0604050a03020103020315030a050601060f090b030105091302030d02070509060402030f01060c05030d110307030507090803030610020307060908041e060206060103050a0e0a03030203091b0d0602030c0403 102
    0x440381100a084c3d6810101800c41680d02d80d00030030504c3d40080038001544200d010f5158041d80d513001c2040103600c2a002580d0007526440c00b010202c0004000c246010801d01007101d050300900014000703181d00030403240ac88000392810303048451920b030301d00c2260302c03041c01802d00a4100c1c4001503c4040c420b8131008409501130115402100070f100002d4890030180590343c46100c1240114500b86418000e5030300401030b85001d62035136442c00d00255a4100703070500840e01c83c0014440b1940c1e109180c07090085000d200c5454964038078284800074110b03100103000005009422005200f00c10000082d6580160143c400b0f1080d103050031010791540c0519540204160309192640e000c10241001500885209a5440844101840c00c8005035a46030184200581c00080020600e41c440d0704101d070014134251002032400109501203003044002d42090300480d40020030300818000810061042c2154110302c44040f0f0b14210025008101400001d404c1d10b0700071002c556031501d0b003004c0714011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 3097561 1250 3096311 3096319
    0x6080c1305042a03020310060201060f26120405090603010513080a020304090509010903090e010803030a0908041502010b1f081b090604090b09010b040302010e0909010209130608010b0102030702030601060e0d02 92
    0x280f0007844004029501c07c40c1c01d1140102000c40000d0303043c0c014081e080544002c080c1d60082135042c260565142c5413100f00c1c2c06040c9500c00c0d40c6001d82c0f0310500c039400036010740101e50380c1d0b10741c105010b10131003500c042c03d154002e070316000400401c1500c556003d80c80c550300c02400d598038002c00004078554000c940080381600d28080601282400c1580a80c400501c80d8882600c81031b031345c0050b45c110394002d2060b170485070010400a81e984020b540602c035094442c1d030400c0d0605885031801c40401c4e50000103280581e554408481c1d01d8903268100e61619001172400185c000103000000b01480c2e00500300d14110744170403981080d950009410344010360f00c0a011262266561041840030b0400c5416150180c4e01d051300103d0980b000c1821a000d80340c041c0c5a0340400000101070050906005140b40b040c1e560900504445541d1600c2806808402c5a404501203040207612821500260100c6041d0342c030800c0385100684022690380c7c115004e03801c008006a24031804268039443d500300080d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 3098811 1250 3097561 3097631
    0x20c0307060306030c05010305040305040603020f0712120f050105010504050d0507030f05060f0a0209011b02010c0209131109060906010c1103070e0f0601080405100e0a020402040f06080c130504 85
    0x348542c103922075011a4001e0010295090f501c20041d411141e082d10040c0000398100002c0c032100f03000350020540c01201c0c0e45420700c1c00c030b516142e0415001f5003041000014000242c1006107400741d0144609800802034200280e504d020000f030b051307104a00c10140a0740d070b18004a414442c050003110001c581216003a07120010f18074000b51101e808440405e03641c100c45000c184584098401d90705482010384a01680300c0b40d03000e0005690040480481c10480400345210050300c0790500b1304c0c01100409902a140400b40c54840c000e1480d1002c0d444c00f9400c007108018a030342da00e00350590401d1081c2062440c5d5019400c00e110000c40f610302150b0103108807213001400c02e003286401881040441c0910106888075030046a10010655014006a202111070400342e03e07154400f10750300204c40221520800d6950104050740c0041e80f00c40142c1000000801c40c00c4c0c0c004c4030807540010b48861451810042954800c0110403500a180c010743d591001039035440260448450100800c0300300001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 3100061 1250 3098811 3098819
    0xc0e06040603020712050a0804080d092a1a0d0207021516030f030504030801050603071101060306060503060c0406080408070c0e040c0302030705151b070f0906140901140d0201020c0307 81
    0x182d13022000450b05121450075254626104a041d5000b142c000d0b5640d081c0c54880b5144c00c200c0f9046000c40e80a0350f0750324555100090010710256801d4050003036050110014480c590714003510b15441a003132194204030044200000004403072112080e180c00503140d41c81030022401c84011054422441d880002e4080130900c0140e41d0362a02c2486941c0750114048014001c0381601c6007518000d02180c4040018455880c02402450748101c0310700d844108003465010007800c1d259541d0080d200699110018001030070140841c0750702201a00c206440c05207455030050010380f00800150545401007040303c02c0000700b040400060114404841c0e06003400d0030150101c120302d00c02244244500a400190380c241109044884e0034901e0b079407401c00c051808441448100741150030300c0c03401071400c08200f4202c0000351502415005200040c140d0604801c88206100c040303241c7e218072044001000022030031034401c003a151f41500e40907070020080c80141e141021440d0184d50600540390042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 3101311 1250 3100061 3100067
    0x90503070905010504060b0405030d0c03030b03012409050105131104050607140607021222030f0311010608060c180f0913151803080c070204060603060e060a0b04090c0e060406 77
    0x29040c4c0340221410000c0e1680c4509150291007a4805c0a805070040354440041394040c202038003c00d1300a040200380e840082000a0840f0603c500078500251644d40e0740106880c40c1030703000c014202007001000b541d41842c1c0018140c0c007020260300740581d1608000450420424280d90003004081d00140d1281401e2410500485141c0c680c2d01841c032400000824051001905920900790403501500c0c0004450802203000100034581891035041d9200000050300c0072840c1404c1070180c4e59141c54005041040c47c259046540326074001d40c0080d0520048001410843c0c1880b800c40a00c6090014030b000801c400c08504450160b00040e2403003000440854084503070300b818460381500d281001070885400881d80b01d184a00d1f1175130301c40c402070301c00213003e00c0f0341c1c0350440c0d0b00c2ca100d02e00f094040d034009026145950001c0c00000e807140410021840540f100540000003102c51000407800c0000048690107a40301d804811600d2380c05600b03884d070282406c8141150060101c035501c40c0c5034003000e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 3102561 1250 3101311 3101321
    0xc0607030507110703020108060f0301060f0305010207050607030603020901050d03020c03060103150c02030f041203090e07030219080702060a021804060801060f0b0403050c090703110a0e0906010201060b090d030905030709 97
    0x14000b068050305002d483c1c28020901000342d0740d050b103c514094031034800303010610070028880d540640d030b601c1020441950710100f0400442c862000940e4841e01481c10300d080c02c1000c1c00035410300d8140360042c401070f0740300201e140c1920001ea400b80801101c40c00d0032840e101181e06050f4041c0110000130051004002c0c1c060b000020080061002e00524501241c2d00e1007070f007002407a1042c00740001d020180203404545203c6003e4941694510b80340c0c2c01400130300c4015030324000400d60002d400d41401701c0314210012070500320f050070b1060389000354000c1d4803030030020310020510340d0015030680700d0401d242ca04081c004c409041000001d4960040c1f81c000c022034011115940e07407101000480312004012201565070010181c040c0400da102804003c0901924807401d15403503000503107a2003074107006842ca007501962440c103801003070401c0c0602814050401030443e41405418080c0c48080b8003200d9031010251034011031980142400c0f2551101a0041070741405070080020704c03010541c03c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 3103811 1250 3102561 3102571
    0x4050709060305010f05010e120102040f1806050d020102060f091e01020301080105130f0807020102010f020d020909060402131205030403050601030c060806040605010806040209040b06030108030703020f0102070314030c0c06070305 101
    0x400c450303605e4038a01a83d1803040d210740c500168218144201c5402d0031000d0220a00390400050300f0192592420752050346070380c000203210300c1c00c0d00c003610f008203560190000402003500c04003100c04172500000c0d26103e0080c8104001403440020418188042145e0000e041a101400805181c3c81d900e0340d01039442881040801c0d802c04011810101c5c200506960060b4081c495212070a05581e4000254000c044242d0540d503942d100a2400071035070005052450384440d0050b5076100c1003040080c07212003e0442405248103200f007403100c2e001082500f0686e0100150709291448a00d0094927500c5181c000600760300602000100f08030040301000c06503225a16101500c1d603c075801d11007211810b1244c2c40c0020b010034080b03070701410268010000207001400c081035460103400810304682c003e0b44448030a42c800624030040c164180443c840e24085072000750301d440c1068030b00034440d2045448082043d40e001001c10b2201d183c81040b5280c0d44281e41c03e4403118503080c10041c0042c40c0480d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 3105061 1250 3103811 3103817
    0x6020309040f1116030306120602040509090a08040b0702040207140303010e07020604030c0b09010902030109030801150507080a050901110d09030308010b0c070b0c070302030604291003021e0405070906 88
    0xc00c0441a4010350f2035071198101601d042941d08518a00c00c501e50180a500781581c818000c40d861801010b00c0d4000c078080d0002587c0d86244c0b40a00c01400070040000e00d03a81c000340008000500c2c2c030001c80341152110a01e042c2c80d40c00d0b50001a00921603510010b0420238074255044c1c40140c0800a14100d40d602040007140b0b039201c41c0b00380d850300011030340100068080001100010100c081603601301100230000034010034154046821500c4612080d808103070740324010030041341e8040080d1040d1071140780c42403e194017580c0e88107890003422010300c01e01802040549107640b0450804041c0c1002d00111480399802c0034024110102c14003041c0d001840c203030001708001d07500074200c41001507a1402050010324040080380b490b0054000e40c0c601c0e028242001000d07a5081103042d0046c3e001e4100542c10b000002c1820b2041046480b40008d0004501c0405c00e03400c400c1d800d41f104071790701914001e00c54954100d49a10b4680300c0406a43c2c003030715010a019009520035514401e5500f107803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 3106311 1250 3105061 3105071
    0xa0501050a06050c1213030f030201090b0a0603020105040b030403020c06030a09050d050703080a050402060903070f0806010f0803030112150603030e010305070806030703150e07060507050705010314060904050a06060602030904 99
    0x18040303400c3e10910002c0c4a140c0c1c80700c01c10b40d0900c007041d03001b404d8400d01c8810003001c0d25142c1d40c03180c1c81001c500c1c00650041c2c3d1990041028443c0e50340740c00f42c02001040c001c1213014950390020f0054004c900c244820310f0404400202418000d1002000000004112542e02c2ca4803256584c01840710348020354140c450b0700d0000300700034090340840d0411074058071441d1260782da810a030006004010401c0740c106600f400f103400c503a10100042c00c090004400c4080050b03007441c84861401205038050852030a0386c6e9000c0201090100440c0d0540750504d101e0304140c0d4450400c142d0f40e0b2201d9042d9010641740c514000b042c50303407203003480410380800d03a401e004540b6000c1e011245402c0603140150706400400c000c00000784045510050300f0314914001c1410a50400c1840c00c0040c0c4e54000c401050700001c101080103024000003015000900303040040d201c0c860751020310030340700034102c0380076048a4010a0070300100700701501c48030741e120701e00303009075519503d0003074a980003102d082d03008600780 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 3107561 1250 3106311 3106319
    0x1b04030c06030506041a060304050a02040c030e010b0a0302010c1b210303140603060a020c0a0b0108060618010b030705090105190201020406030b0d0f030503040201120c2d09050f030111030a0501050a 87
    0x5c0d00030000d90415030a0420100b010303000802032582e1002e80304441c98441d0074013420040e243c5014030203a5102588001626400d0009010b007502e0030810303690b00c240d040c50014001030381c0008000040581090000324a1000c1c49840803000115070882c00c400b00f2203c58101790700091100304a441407203035809026802c24810240076626042d2211903042e044480050806085a4054030400143c0c0c01150300420407605c0380640102d0a070441801a0400740c10860756042002c142d051000290f461500c1d1503242699032061400058005800c0001c00161076500c0c4c1c0c0f1840940e0a600110075600440742c00c100d0000e4003d50040c4140310229083c0000c48000b450000600c500d215000200f424440c03038995070481e4542c2c0001d0049062161481e60681c1025071445844240482a00e900c20808440d2224122000010b030100000f021090005d8140541c0141508210351042d103030769000c4810000000c1c0034140c10306000c6a43d1001008015008001da08954101c50040d10345907a07054035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 3108811 1250 3107561 3107569
    0x602030a02070e070302040902030126030c030a0305060a0801020d06090b0d0203030301050609010c050706020706030b0d050c0f03120a02010504020f0301050c07030c0203010902040e0102070203071401020709051b04030c06030506 100
    0x4458403000560400141041030211039040b00781d005910b450010b29040e1103002a0040380c1085e0801650035800c801c0c0f24030151100c01e80180c01c0300e089401981858081c088050703491281445140405850344041205038032011840000b0300106002507460340416082d8100500b007602c18108503500340a04100390b810180d0290342c132a900580954503603820003052055503400ba01d001c0341000341070300048020038402d02042c009803000794041c01c01c0918180c0020103844509030f919100b00100c00d000f20000d100010b881e80c0440090307442a64850b180303800203050050004a184104100168100c0e034071350306600191140b403084a400010b8512041410f08803902100d005400400c1000004042402286180941440140041101455a40450f0540c0d2800030104e020782c0d0085000c600b145000d008800103040141102060401001c1c0000d40c1d87c017013440b62042c0140e0b40d0000c6240e41c8011010b000c4502e2104205c41d83e115600e2601d224200c469100e02c100203407a0002194040c90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 3110061 1250 3108811 3108817
    0x110d05151005010c0308060a0510080417040b0403020103050603010f02130602060f0106020601061b02040906050f0a0507080703020a09030507060509030706110703030e0112050a050613140c030618040c030c060203 93
    0x40b041e5148600c610361541c4c203841144020300001e90001950303c001681c0d640e401001e40e110708440d0307034681c1e09081038544440140e00c8640e82210000040c0300900c40880c1d0003003510222502441e022070326803030b41c0380401e00400114a4000c00540005944006541288901c1003100c00170380c211900b5035a40d4404500046c028010342c2e005070800390041000503c40d50100c410700811007003807030200d03055600080482d094000111f030126220b8013008140c082c00300103144e00500202e0107110300c0ca0482c800808c0450020064024181e001c1441504207110b00c600c40051540030084607002a00c4a2015229401c00b02086200707205106011940c07620401801e41200c0c0c0307a00040042d981107603401c0c0c503400c2d070342d944071070400c00f2000c900007840b0b299004240c0210054507000a140c14203a0a11240e07074586030030341e00c140d81061396518038800d007207080ca6030200028043e141c4945a00c0002a6054007040100f00c603941c0381d005110034403804180501c1220300c1100004e07030325641d94400b80e0f2640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 3111311 1250 3110061 3110069
    0x30102030603060106030518030a0e040507030c0c03140403050601030609050c0d0c060c031103030a050103060c050903060109020d020c070602010c03060f06170403090902040807090b0303070b01090207110d051510 93
    0x140001004001700ba0294105030b420407404680e107450705c802e401076680786070042c50361a0b000030400150f6040c141030503c559901b0404624003030121124207000608446a002002010400b001e00d000c44102c2c01c020a03200519804826500203503500c0c2466405882c03942800c2c0c03030b80c1c05070304860b80c00341c641030215040150380810a096424a0b0140941d0240c0d55158250107014001228411488050004510480040d4400107640d4158280481210440012103044c01400c0048480b01d560028900d41100c0941e01e001d643e40b038440041070301a002d4641a581280f180c9d25010640e581c06400c203a034844c80642d810081d5a680762050b400c0358099109400204001d98041840344064000ca594000d0203414286a000e58540d02c2074101da0042d4002c140c0e940041400b40142d402c0c5002d40724140001720021400c0140320345507030f40302e072030184103501300180c0c0001c0392420455088807580395200020418041c031141c82c00d00e19241e01031901381e00c404410110000340c403204401d0100d0191 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 3112561 1250 3111311 3111313
    0x40608030a030b09062d060909040b090c04050c0d020304050109020402040303052d0306010503040203010b1f11152205030a03020403110d080315010207030b0c04030c0f1802030c0d06080318030102030603 89
    0x1e01c02aa00c01e001c0c6c2e0302090310a41100d010885140070b0344447c40c91501032807103140c0800d140c0c54a001c80904000c01001014800c50a14081c80804040b16054842d00586c201c00140e032500d8924150b40100581d40e0029001400880c00006154101020f052004101c00d00c1c0620104810640c10740c0040d0160f420b04050f030700307101180b01544078a0156600520203070000521910035000183e00303a0390106610700310b40301042107058513a44001e0341c80c6060540d10051180d0940003040983c0c44100511184945403c1d04811400350348000c2c801c10780c00e03085402d403503584440040c010003039803060106482e180302c43c40c5003034040e04061114001c3c0c281c101118034116200c4102c16a00a138203400b0003070461007615404000300389401070083c01201c040030b5441d038071031031450883d8007422650f0213120341101d00003042108000d01d05441c05007030f41c0d00d140142c1d4bd03600d41c0181c2595000d0781560341c100507d404400701e260703c8008010b00f0002c1c034004068400e4410541094240d200841d949601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 3113811 1250 3112561 3112609
    0x10c02060109090816080a02120301030b130213050c070606050102031201030201180308120601090509040804060f09090507020c03070f0b070f0507030212070f0b03070206070e040608030a030b0906 86
    0xd14a080d0f0300c0101d800744211541481c103541d000c01700c00380001d001d1003654a180300280b652181b5030108401c0c0034280010005500b95031640e201c01075401002850b41c29161000b00c2c0c01c0d070440d91040485000d954035148100001e041502e140c016a401400088881900d4400041015800001a02c0c9201c1003900480b4641e802e40d40116580100920084084102401d011000454003030180c00300c010307100700e125010b140003000104040410f078005070242040d5001d00010407072032002c07141a198203051040501400c01005c5948401d180e1111140a1401040c040d00d25808240d0031280d1400b1030464041c584c0320411100d4104446c8100c1031805020081d02c00000c40c6182c0401c003050144040d01d2010b5580d4010460785803403100e050010350811102072002403242a11940078105001d900c1d415841d20704030203035030f0740c202510300310600410315416040c60b51903400250140120703c1c141e84e1100404000036010b0000380030300702d1191844800258090900c5442c9401c003040104842c26 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 3115061 1250 3113811 3113819
    0x120403150e030903030409020702091005090106050708040e130606090b031f02070206070b090106060203040312030e070b040807060206010503032104060b0409110916090510020304030c060201020901020609010c020601 95
    0x1080a040785248500040c0800031950341c05101410007403845020159039180d89104118500c000280198025200e14a00b07006545409896505444850400e07540e1510142040b200324062540917440000e0901d007004022407088444909081c440c0d0804c3c440c8540742e1003244191070444030110b400d9403080142c00100c459400500ad0346008040d001480c0c2412500032601e25804840306840c0355442206020311000c0910030600184503034400745083c1411942c402d82604148180c2c2070405031030780365441d0002400c0c01190018101540d03080d5a03540e81ba00d0f001d450317141610071440580101d8000043c0750034044204c81c40c0c00d409584c214400401c000d01104903440c0a0000c1e80e000b40c3e640e900d01078907203440c81144000d500031906240c952400e4000c200c019400103110000d02c00f040800d0090541c0c11208a209656080705c02c4501507403214000c074a107000c1d660000e01549454a0300150164040d8018150100207a082c0e42c840d645440b0900d003610b0341182d410300140d101c100100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 3116311 1250 3115061 3115103
    0x120e06070507020d05030c030a0908070509010909080d06030b0603011d030301060507051509070906090b011e05070503030c03060108010b041206020a03060503030a080109150e0604050402040212040308010602120403 94
    0x1c460644004e222404200740c685a66203540c0180c035070034249500000d80c2208294200c103051008003a850700130614642050049040001c062140c2c1c03851903140c1c1c426400f0041214161604d0380036a07041004a6690390528070326086c025034016010f03510b44146101a041050103803540722001500462640e4640b2904a4a44d40b0910044c0c40c1409040a42c2946c2801d49a05501480d06840144065410510014115000c5500003c5214a02900c1040f1a42c100c030141880007420b140003803001080b01001da4852283d50b5005045000010800a214100e0000b0758003418082c0c2e20f040040ea00d4000900c60340c40f07580202428480b4515040c000980c1035001007100b940a0320b0007081d4196140c01182c91a0400c0d048100480d003d2070042c820510903110b10449040c01d0104141c0320b0b031500c02003801515001d007649003d545ca45e0001819910380c0e4040326042d18212040e5180c40c034150130b00424a01b82800390200602440c04c030f03241105020300070755043c0e80d00840340340d4070146010600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 3117561 1250 3116311 3116317
    0x2090c070b04020906030f0a03020303010603050703053d030606090509010203010308121005060d0905060901060b0904022505030301060905010c03050306010e0a0302090106030e06010902070507060807030213060f120e060705 98
    0x2552601c5440d41c01c1f02c542e0010f00201384c10f64400d070010750304ea5040c070304c0180994000400410802d8a0001000b1659012040403607101c440a011440c01080756000000c0d10080c2110555214400c20800001c004140d8455000c0308c12440701080a61188201c0500b40d01c130a20015000c1c080c1400403509060740e0942080d04040c8800c7c8804000e0780c1d07140072920f190000c3c80900009540c80100c48140300d000d020250380101c4003402040101d00b4140c0b07030a1140142c11106001e180e01044d030903103009440c140b0500c1402c1c0701703811150200c21460010358941c406d00401d400507000040006055004404070601c5691544940c2d00b10740c0c079034004489000143e0f480c40c0d805804100d0010150325554003241c041c0500d0b540c0468000c01404500c0c4c908074041e408500e81500c10440352001c01c2002c20702c04150742d002e103003460243e150b069046000e401400801c0b44069243c4500150359600182110040301c0f80b0746032400320f840d0b1004d84200312020700200c404180c03c40b10000e10414032600003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 3118811 1250 3117561 3117571
    0x8030103020114090d0308040302010b01030902030303070f03020906030406020702030709060509010308030c16050706090b070503040902030907080106140906011b0305030c0c010906050105120307030905010302031509040f02090c070b040209 105
    0x44c00d00c48aa8006000d0020030707a810703000306079400c081c00b051603030a002d00300042e01d080c01c0c10712030364241da408a0f0340e920004021a080041ca8000503a010307100f50101c54104c01c0003800e141d124201402c01100960003014101d1003442000c900003050b100e54010340080b52001015030440303a1139902c8180303107948000c0001d0807000c004c10004854020200112442501072401000b02d98100a0003504003020b40d00045454074050012000180000080700d0944000e103001503200d4607000549460820300f0f420112580d42007650104410a664900e05001801116001c0f51030f110703080152130350110403000c911950240021440032a00903c0110b0f04200c1c00c0d60158a040400c0c405107084500415086802c651900d00400051500e001c8403241380142c82d016616244a030340c4c0242c071443e000e01c0b40d80d044c5a00480003c041c012600078000c04284041c1584030149490719003d01c001c510010304901c80d801c100081400020614242e030384032a48400b5000c1d4a4489408121800d500285 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 3120061 1250 3118811 3118847
    0xc02010302190306090c0e030a020f030a0b07050706050105060c030d0902062502030d021203160909020a0203120c04080d051309020f030f07030209010917070b130602010b04020403080301030201 85
    0x801c21007034208507004900109060342d400241c0f13a05014050059802455840040114a00d210902079801250b907502c00355045a602c400001d0310307400b19050030568035010f040403030690300700f1000580060080600754440e00c8100240da1700c544c100302640c09070745850450782d44144600c240b03a03807a035030000744058002040142840c2d10440703c00c4001c521015600398070714840102c0780442c1800c1005805025090010b0b245002d0300e8000c020b42c40c08014842507214040700c5600041d140204410800780120f00d03400c4d540c940d0212800b9550b43e201202c000f550003003440005030f41d042c0c0c0509480070f40302d0305d0b0081d00c4501020201250b443e003101080401020300c41a002501e82114401020794600d600d548689034078281415180101c0000c0c100000d1500400080301c1c141e0744658070000740c505002e40e100452000c9526585031200d10b800642c50408001030a00b50190241400310840d0443d41c000d11050030710005000a9010318072005040070000d000601c019801100091000f180c04d00d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 3121311 1250 3120061 3120067
    0x102070f06030e0f0609030403020a05090103020607150609020f030601020d080106021209060405040c080403120e030f0705030d09030207050307050d080405010e01020a05010207030c031115040201030c03020c0a0828050a0c02010302 101
    0x120740b401c2c10400d4406e05d0040d80700050030006c5091810075880141800c440303200701c84d0b14503000302d0010312401c0402046000400444030f141c44140e404100070704071940045403507038aa041f00c100c5a43c410760341540944200b14060051031300c5181058141d9480340e000e4014100d00d100405c1258110313080d8950702c40d000348004603082d01c440c030803140070004603911011359080a0070050308078040790722555412400c01ca1146003d4100004681c61954001d00700340c2d441c030380341c100281540580c1083c0e031a09800c050f5118145540040c6c01d105035001181994107090b60361080160b010944d4400500690003031004110642c000c4086100c9140180103590004031b072903490b2422a0703ca180f0440c0810740d407403003100034194403602e003520503541c5000921000c160740b005112500c0d0010002410107440d100f10325162031288e01a500070301c18900444540d00c51604d80380304c441e0403601284c15907410366030001c00d03154041010150321041075282c941c500b182c80d40046907051101c0f40140d050540030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 3122561 1250 3121311 3121333
    0xf09050306090a0b01080604030e1311030a06050901090e07090902030c030d02031815070b04060e030706050910020307170c040b030a0c020f030405031005090c0d030f08060102070f06030e 82
    0x3400128801e6150a003e8454100c0d94540300101d004103070010b5105600c030408000009030804403d0401c51401c84400740c0c0101c112000d00090529a042c0c00400c0700701000344031665201d50020340c140d403c200c907a019103030303281e40c1c0846c00c681680d0f41c4200c0d01c0d0720410003000088031507408105400e00240654886064180200345440d40d411200320040c1c0c0700185034028002e80c5114460000030460786d140d000d41c00d98200b64079038061580302178035820f2088089010040d5680c0b20308030407074140c400c1d01d07180d044504140006007030480d80403d142c00750b40102c130340300c1036184203c1e4801d00240e20b490f1020b0120301d03082c060601000702103882165003000003044040401c0055480703241c40c1e64001c01c0101c0c5052000307003400c0c54903218404580c0148001e110300e50b008154400c013811000d0000400d0f0755014102443d12044800c0075400c032140e40c621009269000704040040d52060b25552140d4480d0001281e94221901c00c03c08250519482408007510030f0b00b000c04040781502c00c5034501c10b41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 3123811 1250 3122561 3122563
    0x2030a050a030801030b0c0304020a03060e010603060606020d02060a05010503061909051b100f1b03030204030803040308010303170108060c07080702030706020304061106010503060c09060d050c0301050414070f0f090503 96
    0x3141c4040c0c01003040701c0010000c00464280c45980100d0b4040714605600b019800315034451241c0c000101400c2d2035880951448909520060080d40c00100c1440b1050791201c01035100c010280000d0010300540e0002070074000d0f94050a17040320006001810a40d83d100a81040405c650400f042190303243e00481007c40e1040090381c1e03034003000300f030b401c0a0594408200f00071140741d9001c2401b070242841c00c0c100c010ba00034000103019010b5410a5511041f2458114001c5c41160401488400d01000340014564001c4149060701d121340c8528007011400841a143d1080c00d205c7c000c200c0c0c2c444030018410181000c0a00700c02880340d020a800e0010359800a81400300b250000030060380081030411030f8940c807040e014880b00d0800060304281d4140404030b501c50304000c10b41001c0890024400109131074003012121101c905150410007414000b444010650080c842c60348030358246043e0b18902518030403614000d00080d22500708200030300c1820b40c1c0b080580c6030b42c50b0520290040c0020280c0b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 3125061 1250 3123811 3123823
    0x703030f0207180b01030605010f020a140a0605090709051b030601050d09080c010b0f0103020c0c190e07030605030d031404030305061f0c0b15010203071401020f04030602070302070e13060902030a05 87
    0x43c0400b0105083d1343d190001170880b8101e901850410000f01106050680c011402c1c41005401c5078104985101c04440c0c9850940c1c1340230f00421a82c60b0030204403400c1004103505081d11420b1400340078946955010007010f0340314941c0e20f6605501000851940e6000e04010a000319004002107001030072511a0111900700301144843d9944411100c03202d894503070141d83c80d47c0402d01f000c41c144481140000c1d95014003001e600c0c0100781070741251155991041c40003000300094a6520b50b103240202c4024081d006500c90180603204a49a004116010303000f04015480101c0511415640781d071421406020003411254026101c0b110407c1020000c900c10444909161100c0364090700c1e625000e04500c4c00205919041e110020344d10f42541c0c1e001c01202d13a0150454076918840500c100290300a1051039440c1010a8000030000b0821200e45c0140c42054000d07000d07101e55030365850800305411012500d4001a2b94900c81400002d4801d601124020780040d04864910300207655082c6004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 3126311 1250 3125061 3125099
    0xf0503070c0f080c040207050c0405090a03080f040803060f01120e0a030e0301050105030705010507080405041505041409030d0c050c031201051f1205090c031002130509010302030703030f0207 84
    0x282000458405000720101c071032004000d2a078800c0d04040ca08581c5644481460301031500c5260001544000d2050400074800da0b40c0703004208100500b050408240c8d03507010703544114049242500001c0c0a0518079040e01c0c4500e4000e4250751540d61140200300d1407012a511240c1070265410329003101c000288506d80d81a40407500400c4460707070b00d01b8081d00c03c1344450000c0d440b030ba042200501094801203003c2040340c40a080c500d0301c1d003000f89002c0c2c1300703402541c1010b600a442d10382802112102d801c07240048540c00c7e141003080c00003242076140400b6044078018090340c01000032406036030307031030f170220051500602d070075030404603103803283c5045d50b0010780c0014241800000500080c0750007081516901d481d04100000c0951001e000b900500c610840d01200d03580d1100043c0c00c5410a20004c21150b000800703503540a030303404002c403009400c92151304100c0f13016500003140038148515100d06030307034004005140b1189995000c030340d101025020340c81140101d150000362032000008009810f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 3127561 1250 3126311 3126313
    0x20a060c05030907080c03070504050606070818130203060a030809031011030106020706050301150804020f03061e0a0606050d090303060f030302010207110603042f0303070b010911030106050f09010c0f05 89
    0x3403e00c40c03019032400e0900d802140c55500f102001c0e00361036900042500848805640100b038681d201d030700265039801106400b605095000a640ca2921452620b0305040c4008684544501c3d008070280b43c02c03800100c50181e00041c4031070303052001c900c10501a000a0301c0003011540500c504c10a40f80680d00004a40d03070102c400403006004190301880208040c00d00c0d80b4000d4190b40c90188480c01324012108002d052280d00b00c003280a41d190398941c00740710a8050201ca050f410300580d078030440c0c0941041d030090b0006c8000400c1c02c60507180200d404407032503036035628100350305090020014404000100c01341079543d035000880c0c0710b10010350001180070b03800040c0c5a106134100203016034840f0626a00c940020410000020003c248004080b81d5406020004102c404800300c40e040c000d0020700d03807521001c26401c080007a090469810f03240c038200f041c040145002080c00c00d500080c010380020603001d0001c07001c000a280301801c1d100c0014541601400e407075880d00f1041d51041c0c28180e0329 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 3128811 1250 3127561 3127567
    0x30b010305060105060307090e0402010e04020304050606090117101805150103061505090a1508030f0c01060e010b03160207030b010605030115080105010207050111010603021201050601021902030303040210020a060c05 95
    0xc1c05014400301e401441e0955056207107180c4020014518800c90198000c04004e0401250a5900c14554203030102c0014000b1952804c15061582c0d80f070804403185445480203200104105400c3d04040649103004001421602400d240010180202d0104001503c2d0080c0703032400815001c100d800c2d41c864200c1e44c41501ca5045041020a070765500b00280e01d5884000703403c01c041c2d11610071741544103031111800030f4440718100e4402903186007940420081d1001140401c0d0b82e90005000700488912100200420341c2d5805c0c50344e140c88824400c402d170030ac409100281c210404595800107140c61481510001030b12981e50611810083e00004009880400184224804d03048402c401450a0074004030b01d40c503240000790740d00c00c14019607040103c02d201c9003542c18025040701d00510341c02000d10000e01808920b85000705401c0b101030b4014410340b890760880c00a141c1c0e40001d04c81d0060065072940d03a8a4003030012002160740010300710700c114114080840c1013442051816030240c2d8070240c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 3130061 1250 3128811 3128813
    0x614090907051903020406080c03040302030705011a0a0603050402060306060c100501061206050102010515011101020f0c01090204050f041e11090403020f010605030c180907080708060402040c170403030e0102090a030b0103 97
    0x282036002c3c42d2400d010b1520400007840642d4202c0d0100d90312000f00c44403550740c0d42d00e62504a086005207880203041d9800c1911075030400010f00301d42080040240c40e240401603072000c0c1181540c0042d180030350407060400100b03041c0d080c400014110303031807001c0c00c40d9a00300c81190740801300e039801da01060001d03e0480d40c81c4048000c0340214130062009100911890809501c9542c054401c0b8417a01d0600c0904c2e0324402c0444000e4060382e20452450a080c0d4860203e4060345002c1e0926003c02c910075850a00007030304c92000904000d01454100384521b0606c103001d5601c6031040d01040b001c4d00d0005640d241c003a860758800903e03d1045129034058070301d000e03c604240d400c5d02c20a8111601c25000308515500a4503200c452a6810b40c81d14400103c80d110068080e05043c00c42d04001241d0203102d43c00b182240b03000413002c3c001c51003924100807072032500308120b904a00300040081e103c020600410301180c413940290a024072140300051a140501001512100c640d0303204403484031039140100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 3131311 1250 3130061 3130087
    0x501030501051002060601030506030f0a08070507060f02060703020a020304090204030f060f1802010e0f0a030b090706021204120303060504020c0a03020f010b01050403020d031101020f03060f0301060b04061409090705 95
    0x150040c181a203d0f01da20b038843e200081d4980070010581d604140da44d0780002c41030760b02000100b604014840544e07044030064101241107512840c0161040e104403400000d007948618440703041e42e030540e0b015000c1a00d030401c0031406540100900b20441c1300c180700209050609100610085104100c2d00b017040c2d1071807500109581c6900170050009243c841250700c042c0648550030401c030390919203160003000240016040380c60807000f00e600f0800d84074000c0f0400c44807043c02402503010390100c50304182e5550049036a044400002d04e1a10f0f8140001c0140101414030100d41e14030a0501044240c0c40d04003042c12a0442008026103902c094080b8040c141c0510480f20701c40003000007480b8014030f01002034020308c21361000a00600c41c0c40c1000c0141846408940d022400100003590740d4409000000002c0d0015191030784100f000d10b0400711246014440c8208980044072142d081c103141600646840b50301c81002c07280e1a804002d11686c45d43c03035101c030078440c452070b440715625071031002048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 3132561 1250 3131311 3131321
    0xe011403060606090f04090609030e120601030c0603090323040f05090112170f0c01020d110310090203091f05070215010e010e060d05150106110102040303050d020306150406020106050103 82
    0x205010360441014809a0346401046410b05401518022070480c8031001013401015411009007035030389450031100815610200200c80d241c000c4500f00c00d100d000688541d2034801c28400200708120300d0008100350f501941200311202e000b401c2000441c1070b050080c4a41061703010500a28100009043c0305840c0e40b0101c240240c03c054070344148541c100f000c0b44215242c00c0c2d4002d000405c0107101a00004c800d0300440e54001d01282c0302070340311a0850b5609010750064a11418070509025110320280900d0f030549206004202503c40041d1409854a000b50300c00b500703500f11802900324901c00c000d4a400e552100070f41100e030008242c901100000d042c09202002d44443c1d054160040200045c050030302419180300001c243ca1076120000007450645c00b980004015005030034403030300e0001c4680f2a803070407100d26481d40284410346801c510b00704c1c0306501004010038410b00c1100000c2c81c1030780c00345a014501400c80210308500000d0426a41c100d0792000c40140c1d10707040c0920071960b050080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 3133811 1250 3132561 3132599
    0x210060602030d09060b0d0f02030c01050304120305091603080301030b0601080c0a030e030403020a08030c010e01020309151b0c03041401031803050a030b0604080a020306090601060f0f09030803010e01 88
    0x4104806420554001d40300d200b8807891000d00e6496550003814040c496018076002500140242130440b240c0c075020020211000050707120b400703520142002c5c2d500401c00c0724405e45d4818103200840b014020194010000644110940c0c41406c40001c001c40176544481c01450140405540717070741c910710f040243c04c5001000541040707480003d0040e0400640195410b5840506010801c8040140700c646036000d0390780007030360018640e00e000400c40e43c00710007010140765400085c03041907a541c10840c01e070721060310a01c0320b40d840b40c0400d4408400700040d2640210502101e030004440d58003600701c05800440340740820350000101004100308075021f414195200382010f02016510700c000341c0727241d481844090306002c40040c056007118426030040c407400c00000e240c80d88451300c4210003a0742d0040007a0481c001c2c4a4200032440c1004001750603812103d10341d480d00e512011014007260580e204041c2d100a2108140f400310014480708051070203042010b406a00540c9805020140340d0420300b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 3135061 1250 3133811 3133843
    0xc0711030106050303030103032607030204030501051303080a020c011805030c0613050d030f02070c0b090a060806030c010f02030d0603120801090903021c020a050a0b040308010503030f0d0b0402040504050906040302 94
    0x3c201c01e880c0032040d6411682c150400725004c6045c0c1c00c000849030014600c00f60400e800e00702b0060200e4241c1d000d80140c0303014070000c100310b9441c070850003503070b0302021400b50115070908000b8000d56280d0700200400b0006100104140d94403481c070700011000c0740c1080302c5540000c5600e07499158204181d507480220140c0281c3c1c28495601c4141c0c40b5040c401e00e804c10581c81c2e9544900ca4112a0120388969920421010000d0b07680ea010100307641000c04201c1c481c5820010005903503110380b51032801048020040e003005c0c0c403800015105241007142c0030b01540021712503200084498854000218090004140d241805610040010a0582003032400c50725185442d0086a40010318640613041c1000e618103250a82c02c0681c07800b40050340041c054440c10285004200d04d05c101140500c3c420b0329054040e1340c031501050f4490151005840c0641428405481000c030707141c0020b0025540640700526044d03c850128051740c404071024901c9502c1182400101981045500e0741801c00c54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 3136311 1250 3135061 3135071
    0x6050603030406140304020a030803131101020a020105041509120b0103051e030909040c12030e040b010f080a090305070b090309010212090a030f0203010204081606020706021c030518060c07110301 86
    0x1050144c8141ea80303891003400f1a01c0440007070119112036140034013454100c140c540e01d0349403010301520310030105039046174015040c0e00d01038001c5d400018100c00b0544d058507100c0c00c160030840c14a2840c02075400c01c00c01c120030140d0024100d150510380003d80303802441d91000d1581142429881e1007041150300841c4042544170311300c0c48502100b9a00c442030122054941d50321641000c01211641d9048040841200c0713850308101a08101c842c642141c0c1502d00b840015002c000641d020a10310006202080c068400100c8000c01940002c0381c15110f401c219051020985825804d040c2c01c0b01d1405542e0f2000424241542c0c040010609604400e41228030b0401e0040105030031905621004081d441a84544011560213405903005403080c0380807540c500048031007401c8548541d12911003d07006850300440c211348049441c1500010b0780c11101191403100700110003c1500510411480c511009651491a070501c480c90050150032441c584800c03407420490740c0202c83c04c81c00d9110340c1c94a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 3137561 1250 3136311 3136319
    0x201080a05040201120507180509071718030711040b040608030a0c03020109020418150603050c010f0509040c090906052e05040305010c0203040905090609120a050702030304030f060506030304 84
    0x9422990256030031030085015100d501c010f0b00d40c9400c104c04001d80b139050108100080b035100800340d03a2100103640305541c10382d85d00144001d240d0f0907104280025040e045003061050401000e0f40c10140b000007090030004035010490458000340c40c01c407208054070441450f1441c040c0118044010304480400807245090f2023213940f4810001c035982800101403c11007818008e5204040745a0050014003c440f80080f00b0700707010740400c42c2143c110341c0103603101c0c980c4d0443d41300b04410340307074000000d2042603001401900e2011400310701d001084401c02500308103844a004a00d08050262034800e50141000700b928191002504460700a10b80201940c95150b115200c403851400001181d08404402540890f110310403500040c20b158245800400015030000c014002c54140060800860310741c0c0507002c0e210750741503c0c0c06445e07900c00d010b1504180800c03030040c05444041d0911034035010232035000c40d080d60455401940c030022801111070a00c4018007034982d1015044010394986824 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 3138811 1250 3137561 3137567
    0x80102130302040b01260a05070512040204050402060405040905010b0a1703030406050c040f081f06080d0f03020c0f01020d060f030812090a02090108030a110d0e0108040c09060312020601080a0201 86
    0xe1803101920841d266070188049902441d1aa200c2180300b8069028060040146140c805000c1d25220605460400080c912500c25400e0780d1200c107003420440c03030300d071036603003c02000d014054001ea900050400c0f00052a6440f4400c11101c648243c00101b294002c4008001d4050303c41c0e4417040402c500040320402190b004011203034001d40c0044009500d03211202208242d000d150810b00c00704280328004120321900107802940d01c103001c02c034092102c80244411094600a106a6855520590a070307a0810b0281002a0b00018186401400d01000000540c82c004a090380a10581d60001d2007142018950150002828400c41030a030400c1c9182c1e12003281d4401c1e1a03c0d40351006070722000c5a4110828082406929001000e4240b1540c4854030251a40d1140f200000410004aa5825503400c0494160400c078400c1d101c840740d41410a0055958030401041140ca0202e880401f06060b0380340d00c2480060b5010f40c925602400c01394901038500441a001420f9a41c00003032100300503030f4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 3140061 1250 3138811 3138847
    0x903040f0608180106060c0c050103060b030703020c010b09070c03020c0904050606090703020705010c0509010e03060c0d02070203010605030f03030702060c03010e0c070201170f1504060e07050313050706020106030606080102 98
    0x2603901d03210800c0d0f55440b203c42e5082101d480c540e07035103508002001a00680c04070480d43e0b441d01501100c0d0a4650f80c80040d0201d0300244070342030b0180c0c02800000c0d400e50003a80a40142c0b0100703400071030321480000c00101094000c442040c00f1941e01d2141c64149541001401e001410a94400078682007989501d9030704c2c6001441d4601c42ca07031001c00114040d02c0382d0142c401840e800f800030312580807401c0000c3c0498101000c060300040e68102c01c01000d03d00019864000c0c028800c205262020072001500039600801040c7e070103640790100001c1544042000c101101e00d200040e640f24142400001d040c460040c10201e042c1d5030910040c0088188030f048985c1040e900129250780b07450610040e00d00011080220307001c025260200041142501c403064030410b21a80b075001142c2c140d00812044403140d0080240c40c015007800900014001d070001c58100c945408402030000312a500c00786010300340e4002c040140d45500c020020803010b03000b040054040b4400175403e20342910088050f00d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 3141311 1250 3140061 3140069
    0x906010512070b03010305010203070f020a02150f04050310020304060b0d0b0f0406090b070804030e040c02060411030703050f1513031e03020c0313030510020405010c0b0403020c0d12080903040f 85
    0x100c00e81c1024030a94000c002c80381c003c091a220454403507940e800d20300d0007500129180408201e80341c40c0d0315042407000c1000c02c980e9034010030550105e82003440a0311180c2000356501e600440c02c00011501d0359082299549045080c00003607580d2070a8034023001a90a125104d41c001c6400d44002c40001d5400b01e803d6a1100f09208013011941c1d850800741c018060410f00504040c88080600008503400b0a0480c46213000e03031180140313900c1040c2070000700e90424020200507000000410700180311080b11a482090050886144c00e07169183c85007448040c0a0743c00540e03000701c00350031640654409040d03002d40b4030381c0d440e100e0035074544000e03207442d0b01e551010700c20010200c01130802c42d0096050740c1b542201c400440340c85003641d00e003880c564102404255614821690041c11504960003218107850040c0e642c40c0c461310a698500b444094042c00450950080c0150703402191903406080705198050003901c54828818103000d4403400c1c0203400c3c0741c4070360020402030201103c02080d03c3c00315 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 3142561 1250 3141311 3141319
    0x506070b01150e0402040303030b0102061803040b03040507030203010e03040e060d03050a1116120b011e0b0c01060803070f02091503190c080304060201141006021903020102070f06060f08010509060105 88
    0x1001c000c00d01183e015502d642d149600600c04240403061607496844903000ca8401e03000c40d00a038603888036182c4412154181192103600801044c440040d8001c05541c0240c803c0381142c0b1403580306e5002070300391a00a4a8560380354000308041064804003d091604410161036100d03440c001510001c05a1045502c0c9000380710089101d502c01410410444032820341d64203070100059201d00c0740403024078549006541071f2441200106060948041c0d03000c01c0298000c460f581ba070728024001d030003a08401c3c2d4060081d5a00c01c1e000510400900003010f6151091110800458192042003848540a024446006a1528411225100041c40e405074419403403070349420140b1440d0a01c450006604449018000428001450754054029240704090fa0b00d140c201e503560340c5c1c3c0854000c0301c10300c2110700617400b44090305580f0341d01d50031965030a40a84005490004e075901c03005e032120301c41c9804480c1c1d01d6440350100241b003040355511029041c1750000340443e080c100c01e020b5540006016151007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 3143811 1250 3142561 3142589
    0x110303130312050f01050301140f1b0c01050106021c03020a120506120f0c120a11060f0405040203070f08010602010902010c08030603070510030b0108010506030105030a1203020904020408060a060506070b01 90
    0x6142c041c0e841d41c4141403141405200038989500b002200403420311420b4040e40c00c04100d18491142d1901c12882414140da8002141c7c0d155605185030b00d50b41500349217989010095601d8041c8207002c0d01d8040d1036945c004204141003404140e00511038000c1c05020144140500c1c22155400141000040c00c04400415a41c03a0040007070003413206030408160510410b00843e06094010942d0070111340c0c00c507290b04a088a112001e0b49031a091100104a600a54494986440c180010b024455136081480e800d06442d82c01140480c3c3c8241c8001011030258106511031582c0f14140a002d0304503880280079001d0710f0303400038040b801c0c00d100c020103800c008000544d0a8800704150341c010302c4028071100301c980c030b01000900200034241e00c0f2800112030400220312400e00d4003c6034120b0340041c00030208000c00d41c81d000034a07190b40e040031040640800105204e0394a50020307001030502a40a412581410030b00c034800c60321298022402000e05000a0020a410b00001c904480781e140c2c11a107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 3145061 1250 3143811 3143813
    0x5030405030a0311040b040f09050109050408070308090c0405090a06050106050a05042303030406080a060501091401050d0608070807080f0604050a020112020d050103060207031704020604120206070c081c11030313 93
    0x10880c0186e40195207010f1003c540003c40d6080e00c031402080b556040400c0080c2d903207645c200c40651b0340031140a02440d2081001d0400a0312071100c0c1940f18070210141c5601080c1c500014040c0e42040d212030300300d5031280344001e050150302e1007003600621490501c00d140c80462440607100e80520f20172180d16058030389154498000074134006101000c01000d0303980e40c60701c0b5a805409204c2c1610385c0340c8054608400403803154020b5101c1d4050710030840501c01144402e000441c2e09038000200e880b080ca8880200080900042102101400d209005060001e00380100240b92104a28404806602030740a01007c0742c000b18100440300d40a10306460700c0d10b0b090010302c0c00f9205201481900910b0030700004144a410780c05030442602ca980d60188451004084040c0400103540207540b147c401c0008210032100d107010121068801f0f0326071b504081c000e8441c040c101e509948801d06a41112a108840b0150741c0d6640911030400d09001d684d040500100513503c0c00014117441e905c682035290a8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 3146311 1250 3145061 3145091
    0x803010e10030b06100c0c0801090309080a0b060402030c090a0e0603010c0813080705030c10090201080a050f010905100302040e03090109060207030309090b010c05031810030b060f0711030a06050603070605030405030a03 96
    0x12046e900b109421200503aa2480300d4020006c444041d4006880e0140118500d0000b20b05494456081030b442e0610b92281c0080100960001d01051050b00c0d04100040301c0340c98030030606000f440c3d003800040080c5419828142501e4440e0f5000d001c000312441004208880c45144000c00e0b50040962903e0b0001c924286246119000c000c2c00c0d148101902d5440381102c541220219601c00e81e1940d030541c4a83e0b03103c1080c0d60f4281d445220060700785006112606c21030b8841903202000ba0b02510402d9500e402041c04c0703950b291030344c1d50b01360000a200d0348a56000740001008140c14401402000d00d103490007007182c0854019050410740f01d441d0001c16a22800e00b484540c2c1c0c0040540350381d100c42d100310110789002c00380b41501580c1821181d803001c80c00307403240c40307007028018242d01d182164000e5000855800b1442c00c40d1425020b45080d441d03501d0030002012a244a240d0000756070521000709441c0c031465610502c00c10008100b0040010804420384a40380010f0401081d0805401080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 3147561 1250 3146311 3146327
    0x3110103091e030f08090303240d06150503060103020306040308060406030b0a020703080610050a1115010f0602010b03010209130b0307050603070e010306080309010903032102070803010e10030b0610 87
    0x1500000c0340100300c42c0c0e1906103800c1c40040d54402e072184900781050742405d442448080f030360246560018070009110b034051244903d400c10030003042d00d00000c080d00c00107040101d100c0003a6100707a40c9800054803141d404100001030700c0110000d00c2c2130b615650001c0d40c0d419004000500308501000880d04944035030300301c1c1c00510362149803800645410072044000b50800a401e034002050800425901e003000005150410341d15a1090f213001d20141c81698486401c512000c2c451051410b01c040d0100d500b40482e0103440200c8603003046074501032000f403d603a01e00004901c640d1040007030109039076a0100000c000401c288020503c9000500040d080120aa02854001c8000420013280503440301640039111000d80707042221580701c8081543d640100304816000c107e8940d01840468011822070540401d80b002d03860491004500fa4416604040c4007100c00c00c42c00700040c4215054913250607408810000c0c900440d81c07542c1c803034001c08170001d044640125015130700c10815502c45c50035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 3148811 1250 3147561 3147563
    0x708130b03041505160203030106050c0304050301020705030c0d03060605040302130b13050601020d02030304020a0e130f030306090605011706040e01090501020301030c0f0501020f1c090305060f01060e0a03020a0311010309 97
    0x501601c901d0305042c0300d41504005480d80c11114134000000ea4078801d41424496180120360003142541c5c240a4141d0703e0354003190203a61544410b210005640e50300b400100f01142c030a00107141c40756800a102c9103407150444405042c1400c214082c03105a5001041ea01200c2d0100d508038400201d00c200f03000200403100385079170004c503840c11045c141491a001580510820303821503003c0440c0c15000c0380c0741d0000356802036101c1e400180030402c0398801c029480d045400310054403c1ca101070340d00c0301c01142c070b900c4084000c03e407982e0042110803000e00c50320008160030300f04800380b0512150902d54a6100500c414410382d42c0312503c04c00300d9425402001010b6010008550b82e58423824031100c5184240700d000d0b0b240885d20b8001c1015480414030203580d03100407005050a10701101076900d845241c035101010040202000070102d0f40410815001d00b0b051070b48c102c85541402d0303004006012801803540903203030800080005032500b644d0b00d800c0b0303500309104e404d034640c211004801034226154 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 3150061 1250 3148811 3148829
    0xd120903051603080f01080703020f06030402011701060305040302060a050402012001020906040f05040e0102070302061b0d1b030b0102070f1206060e090f0f070317030601031508010207020f04060308070813 90
    0x201c800200f58111005602801d42c4845a07001e5030713070710350103569150441d0100030740003c43e100101d44207003007250146420620505003995036595001081400c043c0076404240002e8540040c003052640512500b604403941c0740051003e440e15030001781902d60a9000c07510a200f41c1d107c41c1403900790039410b403554208010310b00c40d9079590b60199901080c1460203000d100764981142e4141c03040052003160001d40e89500613001c150b461100581801e01d40140010b500c3c0010007030809084007501c1817800a2907c00c0d111602801104070090803200b280301004c0c1958480d550a10011142c46a41c40c112080340d060f2400c144594030b0b00c0030240150350b1000183e03441100c24070803a071501140052100107450300300c880c4031611482c1e050356086107200291010700c00362402e039010864200116481241818003284070f40280381104a050a140d00213401c07a5070108c0c100045140c41030440580c101c0c106d606100c440d04580301c141c000d101d00100103010b184009185a2120b00c03080c009002000b07140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 3151311 1250 3150061 3150097
    0x2060304060e071e0906061b0302070302060a0f110d1e0c0203030703050406080c0906030402040e0c0d03030b030c0103050c03010605090a1d01030b0c03070e0105030604090605040807020907020d12090305 89
    0x4001e914004c10f0a400e490049010b100120f0380c2c0d002840380b401210302d9541e6080401440300a01000000d4917a03090b0114091381c6000b00140e1203403c024070082c20b0580e900c5c1000c00f50301400801c08018845a0390803500001c2907020056030103045080c003800240c18014614441050a5501c100d910b48000d406000c0480d10380c05143d0040094801c0340e019840e40a4965600000003030030b0b1160340300095101009002080141c241648808804448141224071550410000490b040d50b2804200c4c00a5200c0e10bc032034003400c080c01a241020020b0030140a1070901c0b0b00015034501050190008014001c240c2010b10b1380d4002c0b14000820300003c00c4c3c441604c5558000d101809e007400190b46039548040071508818140d0201d03481414256541d060030074114004440075072020301020341c07080e2141840700c00b0480610403107009074440e4032b01682c2c800c07140c030501c0203050b0014001815034102881010605d90015100c4880541120000030354640f18030f000c1c0d5503400713048010811701b0a40303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 3152561 1250 3151311 3151319
    0x10603050a080c07050a0b070303150b1201030618050601050907090b030103030f0801060509010503040f020a1a07060b01030501050102060114010306030b0c07020f060405010e010309050304080a0803040303060f0b0702060304060e07 101
    0x2802c0100000c40b000029103810740e86030400d100c0d40007850700c220349520900300002800320340710390300001c0d1445030103002c02520f940c0d820421b0055004080b4000000303003d2030040042041c98031526044103071161036403500e075107240c4030543c41d40d00510949010b030403603100140b03e40b4071412a240103807103000191a00ca58407070134000c00a00c40b9141c2c04010601940002c01c59a0040040c1c55165a0580d0b03580c7c61a5941d0b550703414814a0190100d0300218201c0c0003141502026100b06081d542c000d0f1050780b15803980c00d02600f03403901120705506062904c1c00600450b60b010407894155080342002c0100d8409800048000b060640d04c060032094440d414030208036400e1006001c468000ca690200700b410900c01c000d694800c510550b800704100030311030906540281c110b40c5034103000e5026207007005e0b610f681c0ca900780311803c4411140a0341c00420401015014441c40024118208603141d4003030402032041d01070310603588003078498130307011001804111880d005510000400d0f000e40781d026580d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 3153811 1250 3152561 3152573
    0xa09050d0906020d020a020a0303120b030102041202010201050112020f010807020c0907030504030809060709091d0304030609020a0905160309080d0c020309010f08130303020c030d11030103020f0607050607080702010603050a 98
    0x18002c0c10014000c42c0300d084e4060b44001640d0060540091411050620b140d80c140c420100c0048807444c0d0036200c84c001c490b07a40e020b1018100070001110b0049810001d8800242101e205070485401c0c0108824100050780314a0465005450282030154240c0c0313030100182c0c41e011030540140c0d8010a40c4007000862541b40d04000c3c02a80b080c0c44128658542e0305240d41c072400c00300d4000c2c001883c80e140030061550710303400000d01c07120035024400c3c8041d2110b41403421548207400a4810549803a08481103051a41d0b00100904001c01d08101a080180850480c10b208030321180c00c160700c0b10345003024440300004850503c419840d00b000310f0054210041d460b0b8010411450102e05a100400c141038003540c0703460700c203038030300240000e18100c0c17603806500035006031650413114070003880030901c103560354401c1800c1c181603d040181c4941c558030420007101c02100322240941c406001400003e8030014400e504001241007602c010360315480200e0040c1500c0d400641036101d2280b404084c454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 3155061 1250 3153811 3153827
    0x51e040603050604020702102007090b09100f0302010e060c011b030c050c150a0e03030f01030203010606050403050309010809030d0204090207060507110303130303061203030b0301060e06010903020402030a09050d 93
    0x80c41d00e0500c07280d40c9080c100012170041d80d00180d00104e051283c260b000c0e108500051600c10102c252000e00b40b03090408a1500007550090420f0690b20324046a882c42d080103441c3d4005031000900c05014108900d00280b610707a88002414050441c140540c20364980041e102c030440e428000f0845240d00c0f16460503211410484130010a02c0c0411180010340301d081240c200c3c035031500042034044540f4812201122000b440c40031403541d41d1800c12024030741400114041c0c043d60415905d154110b004050841d0495417000050080800080000a00100a0301c009940c02d00301805142e0b2092201401d521410300a04801407002070b02040e5507085602500195000300c0041150780d440c904159265110011140d410398401c0c03000a00c6030f4039008d01e01440300d1084c40d021480795650341c0048044a40c85500310046503d454407045141005d1061034000c1c00311003450016820b0010006e400b141042c0006030155800100142c90340e017154011040c000da0000c11510304107828200141203003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 3156311 1250 3155061 3155069
    0x60c030b01030b06090a060e03030d050f04030206090601030b060904030c020a082a010503010e040302010f05040c0501120b060405010c05071214120406050904020304020d020d0b07020c0904051903051e04 89
    0xb900d04007003440301d410410705481c440c8101510800407a4108682529001003106241d035140c071041084080003030050045074061050041c515000d820203103000780c02e20f2001041d41c03403564050b1004201049507101c141d600708409640c002d115440e1800c00b10307041110000040d405c18100203000450020000d00380d0800200780070702d100783e40c400e0f55042d20070844c0c545c0000d0000e0000e00040c0502100041c0302c540240c424000002d0904031814000d0030395104880a0b5940314070060f0402055800070341d00800c0040341c0c441041001d9000d80001d855024502075641008186005002080010059000549071248008494a007030707140401c02050642c0c403070001c60081140072841400e0600c151004e54100361641418031261a06000007500000d005a9110ba000082180941c48154070010907d000e0704046000d441d2050002e0724200380d650b4107074041c2c1840002c110104001082c500c0541c826034031a80303c40046810129614040e00303100c40c041d43e00038290b2010342010100104111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 3157561 1250 3156311 3156317
    0x7050102010c030212060103051e07030603030e010c02030a0311070803040905040606060503010e0703021606020307030b040615080f0c040b04080a0c050402070807020f0307080d0804020909060603030403060209040207060c030b01 100
    0x41181c000101e050380500c4c00d002017644075000c0443d040390f00a400095101e180c20003140c000c500040240d451030b200642d41c0101207690b0300800e00a05500054040c44118282051454000245e021076641c004805000d020091008440304d05000706004410080c0450000c8030b8581c2d88500148005140c243c030111503280c94010001070190090050b230781214021088110b017640c58900c1034010b0352040320760303040744c4010030f55980c0042e00034406103005000d5070350001085050941400101c0d8105d402050a03102c19a69101c44240c0c044001c03640a00c81c0c0c1d0440340580c46488165070580590f0f004806035580100d00490310010006000c0e54480c0946400301c44241c2e154280400c9100d6100c011b46180010030601c409400c044410a49100380a0200c81c0a16a117440007800c10b03005a4202d00000e00c600c00303000540c0381410005403c24400c801401c05820040d001035600d120b0707844010200c58010455640301d40d100d0b4196008150003800901c03105001d504010024902c038903805003c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 3158811 1250 3157561 3157571
    0x30b060a0e0f0115021513020a090b060a0309020a080f150a02090a1401140f070512090306061003060e041401050a060b0414030703080409020c060a14041106090d050705010201 77
    0x4001c260700240141c20303502c18081141d0824a604400c021510220802d5116101800078001c00c80341000e8410b003000c540780309581c0b5a0303104121040280794442074030346d4106140100c1942e62503080b607402d02030509002038020a1880400c01a85c080d60054009009102c00001648008200e9503524030500411205e00d580700d0004504900440304941d421143c402414007442c404000091000c807814144460043c004940001c91544030a14100a9020101d242010480100460315825030b0340c40b00d041c00c040d0548003003a6680c8000308420321815450b4003044000c0e0095000d5006009481032261651402d42054007960b0a4114400260342c40c0c0310000340d01040304e00c600429106400383c400e103001c0c50310821900d0340d940d65070741e6503042c000d048001000440b940002c10003410484000368613401042032050800200401120700d8a0420f110305840d9940982c106510540c000e80b0070a441d018080840c20a01030b004030036030800074484000050280c00290107003201e10907402442 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 3160061 1250 3158811 3158819
    0x203041406070206060108090a0b0106050903010b030f0a03030510030506070503070e01030902150a021218040506010804080d05040f050312100602070303080c0309160b030901050106080609040609150204030b060a 93
    0x2694550441e82e20700140c00040201e8055072240803215048141c0e4422a900d50806490b0a01d6401081c2e10020209038002134034841c3d410203004a41e15a00c080f006020b040c0301c0681410313114125010014205590707a00010804881461244051500304044800c80e1500f00f40103040c84c0d0003a104440821103c01c642c4070990700c81d0040740a1164050401216030128014603022504608030503015809060340801c00c1c000d040c400740c034166402c50501880e25041002b48022a500507061a040144060400c00407130440710480b001c00f82001000901340e95142030180c04000190030090580c0000964840001e0022031100e0107000880c0d280700003a41d848100b660384090354840100810716a400045072004070360051944018004240c403003400328958268866822a0130200000790044180000c0ca1024410311b0301410850418101905006c0005203c141c4018002084140c4542c20740040000c206920302902c01ca4810039510f558807441c0c40540d00310119195800b0705c0f61410001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 3161311 1250 3160061 3160063
    0x4060501020a1205090d0c0509010b090907110304030c0b0304050106050f01120f11040602030310050105160b040303090b01090b2e080702070503100b010206160e0409030908010c0302030414 83
    0x101150416001440c40580a6490000500c40060390b03c003032220602120101e511045000f1802500c1203c0724044141018100003404406811003121003009000041207600c4007800541c208800d420003d080d044a039040d285188143d400050503200c40341000036100441d003015500a03031044c00240f0085e42c440702407151b0580d0308482c2c18006400c4459610701e40405074440321a0070410480401c1e0594900081c8071694881e510140041e800001009910400003552501800c003d2901d146000ea5110720980c00c50300d000c8018002040300c101081c200f600a9119000c1c090748140001d070307950303502e251000c0105a081c022500611094115505040500c1101280c80000d881180c0000c03008010841d0908001041c0006511498501003071643c3d003008445042c440d0890081401400c207800207042ca500130340204980309401d2910200ea50708481e83d0200c810f400d850009002039107003411a6500c0da00d6008a03000e5182c03801701c00e03611394590001c5114132b000e601c50701065000ca030b4040e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 3162561 1250 3161311 3161321
    0x2040c0f09050607020607050a0f14070608060111030c2b050403151104090f0504141c03020a0513090c020c150702040f02090603090706180b0306090402060f1c05010504 74
    0x2440c500d030309010b9841e02c01c001d42031150015207294140900c03562080c1c90442581000c0e5012a0814541c108100044000c4c4207114250805055080d00d81000582000001b42407541800080c100303035182103804200381e07202c000d040c40c200c4083d400c02411001100280e4525012400c0c4046080e0041c076010744204c0d070880768484c40d20001d00852400d100e0081440007014410300130700308000a9000c01c0f600408481954600001401e030606d840e00000c40e960340186c644240d0032400d20803410040000b592642e1458500b0056540d401003002102e052241c12101c03107441c00b01d4a00452460303110787c0040c2c22281140c00301d171100510340341000803603c0600000404141c003004601d00508098000c90841002c5400150810501c400007460b01c0e0001c4071a000780d540040c0c0c3c2007100a0f849042c900460918a1410900e6400e00c05109007034400109841c2c0201c0b43d21011504546801342207607280280e050406032141889105500c2c07900d40c0c070f481032001074105400841c041c60300b4815 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 3163811 1250 3162561 3162587
    0xc0a1113021201030f050703050a0803090d0306050303030402010305060301060f030302060108010c0203040b0706020d11070b060102060f10050108040f02060a081f060f03180203030a050405090c070302070302060c0f01060603020702040c 103
    0x42c58280d0f860f581e645e01c03803075621041c01c036418040ca000010001e50f08001d44000c50703100e01e03030f2140c50f840d0036503055260035034403082501014101482003100e52030104c200d9411580a2170080b50399902c0401103400340025a120511040a140000092583c081810b80c1640c810390000c0c440e110340c1c0101280d4078041c500408450440400c40303600082d555a00030b140040017107201080b110440302c03403401c654024500507283c0e031100804001066034140301c2c10350301100c1001030721220300f4000ca24101110023806854180b00000002c541800446186100b003554001d00c043da640702010401841c2c0078096401c40e543e4011000f0007008080011000425900c06903110204038840d011300300c000c0d103404440c7c245d03030000e0086d504015890501c018503c25885d40c40c0d06690b5031a141c10301440d000d0082c54401c140e54144085000aa4081440c10459804490302500c0e4112100424284003903040f030a081c0d580303030503000a42e40f03070150080d0024500032101080300500c03404054807007080c1c1d210 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 3165061 1250 3163811 3163837
    0x31902030304050d060b03010606030606020105090d080c07030201090209070c020a060507050d120b0a03030305011412070506030c0c0a050a11090405060c030702030c0102070b0a05060319060b0103020c0a111302 92
    0x40b0a0005080080c10750303409500506000ca07112070783c0f1010030700b183c0c1142c00c90303000030f0745510301030106030780900806400080500040c5001843c0c0d100060203d0720207400d01c00700b4000000c500003498400d41040a00d10740052540405041035080a403003541c280c1c0c4101d009040740000054008e00800c1565031817900030024005540701d5100032242c07401e02503001d0206981d50340d12034550743c0b9041100805103110751400605541001100c895031310714150690701c28600c0c0041c41000c0301c000301c1e051048901c141c5249807213131142211006280105d01034410984940411441070004c0050001d40d0301c1e000381500300b45031601d402804a103842c2101c015126600031400b00b162600000020740d40b0024500c1034078103004090031020b0aa9101c0d44090310048205000e205081c41c26210703403504064128020190410b4001c0d030b048003008ca0000281c2095501d42003152664041d4045981314140001078620068a5190000c0602c904101103070040001d0800048003802d907200700e03046128410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 3166311 1250 3165061 3165067
    0x303090604080702010306030b04050109030201050105040b0f100903020d06050a0c030b010509010f0203091008060f0d020112020304020f060301080102070308090102031014060f040602030d0f02030105010801051207030b090a020319020303 104
    0x61a0b5600301c2e40808022810140d40301c1d03001010403000010503024a05c2103002044034062418004d00751401038120621551030728142c1074503503a60101c81d98001e4010390741c0c0c6503840ea14500c203a556110541c00650400c980302d040c02c3c2004866444107204800f003000c200480180000d040301204c43e030700d541c5030104000300f01064440d030190500b002c442d034141c41124a44010324012880354070300105a0800300301710758144002842d0056244006c558160303000040004d164000801c240c41000c69051140da00001090940d128039074443d0904e0303409040a9030b01c0d652411010300039844030390140c0c0043e05650204482d01d0040c021a401015001c80d400340c500d0410084801c3c01d556a540c0c0f980c00101003000214401d54a800341c8000d003a05d402a41e1241c4c0c00850850503202d00003030302c401c2d661040006010903a044040300d410b4507000d985c140b02c0032401c3c240d014940781d182e80001d01001d0b003640c00c0060b04e4500141c00741c2018402d41c287c1c4c3e0f00000c400c41a81d0b0f14808c020000303600d0b400034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 3167561 1250 3166311 3166313
    0x30402040203100306020c0a05070803032505130303050408010c03051504020c030d14040c060504030b010e09030706060e0712060803030402041509050403050712080601020a02011803050303010e01080f0303090604 93
    0x1e8000d1504409881e4004100a54a0380e030b01003241d004040228040d0031035102d450912000348440380050404001541ca18986440c3c5500b10010340d00a469036204804603003a9142e104074146c07008100c041c645501182d07101d04000d030050300240b01e12203107507003001c41040105120713010b00c5000e104910b00d000803066206042101075003010000006520040c880c0310080d03501d80c0903000e104040b50901c4103150a1900340411480c07619000308050081c10002080080c44103910b180c115981442da401040e101e4107501401d51240a03006007005041c50008604551004009806030100b51601d02e41040054018003e9858a11418045030010300004000d41825041661a81c000d0501405215100d9841c5011504141c605a00203880444c003001000020301a030b154840c01d5040c8410240b8011000035602c0343d2031600241007007081d5481c2007030000042c072100003440d0302a00b525101c4d030710340c40b60160b0070400348038100381846960003c1d182c070840401124013441240d00500740540e00d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 3168811 1250 3167561 3167569
    0x109020d180f020103201201050406050d0c05011b0f0c080d030627020702030604050c090601051612180b1e03040201050403030c050c060406030b0a0501020c130f110a0f0210020a05030402 82
    0x85142c04034144912102c20080c1b1080f00c802000c03110024550440b855050100380003c0301c2407038228a01400071408400c02003000c084650301120000d01e4040e001095980d982c002c001c0004100406403003000440504100400c0000015150b860085400d84843caa0044040d40c083d0701c64001d080f0361341c0301200b41d0040d50700f03004280001540001b51a2690550201e442c0440031038040d20150460710340800c95190000c0d0444d0404d20900c5c0044c1404658224001360780c004420090440792842c0c48902820701600c0241c126a1070150f80000070ba40d03404d4580001c0e4021110390703032490020113000d01101c4219095a008a0301030751110f00389070a60354161000381503c00b080e9803510920f05a0340c2c060347d4131401040034040550700400c901c9504400c2c000c454820f034000d10b06542161b482c0c400700351244ae0845a00b44103508020940300048101d14009000c01c0b52903541c40380c00098035880e101c0c0c020740e10b00516a0a41e0032a010100c8030300c0280200d008440005001400c01c10104025180c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 3170061 1250 3168811 3168821
    0x604140301061d090601090501050a0b09010e03010e0c01080108010c020613140a080901030b0906030309040903051e04030308010605030106020607050a0315180606020f060402060a090305060109020d180f020103 92
    0x54000a0050f460b659800c0c1d01510030000c08000041d410100446100b05000d900e004100ea41418400d550405000804c001803d00a49000300c0e0701140500f201c1c3e1060646000c86000540204202d441c051440b5885045201c240e5004c14282c038000901c5c10030510403d14468042d50181c840385d04c801a1110345400d4545064039003180952480041541c1070100c042e205200744100c0d42d4503103003a80058255031440701054070903051101080840e850100480301141e20403140040c52900c0c0e450280d5080c02520010740000311b0000541c1d5903520160020000d80340241c55200c7c107a03903192011155031000f4000c2000680000c00800c03120341c01800034010580c640d0078082445400301359403100d4074010340d00401121080c0e183d000b40040b1503100e042d01800e201d1000c0d2030140602d250b29940c072400608000d00541340011400d8045101e041d868000c0c5601c01e0a503502c5507514510307140a5041b00303d800400d1890304501445107041c07003c07500da62690041c40070500b003000e40c0064008107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 3171311 1250 3170061 3170099
    0xc050d0510020a020115050616060c03060902040306050106020f0706020a030804080409051614040303020307110406051302070c1205061b040b070302070305060106080403080c030702070b070609020f06090604 91
    0x100c507000c8100c1c0c4140301c030300140c003840303140e6800018071092004540800e05401d0380598042d60b01086002c05020080703000c01c2486401002c00724213040a03000c12801401c1541c080e801079440454084100503c0741c0019048401d0395007160400100c2c0d8989980301c0999205900250b8081824840003078054030006900034040c4002c2404c26a5039024034054034070448848241c000c5040680000b01c1c2c020300240c20080030304802e281450b0660380c2c040c2d541d03c2150800307403003902e09540210307803070742d03982c201c3c2c1c1c00380102400c0350f00d22001c0400070340040d4001c000b084502d220703030020100e90020300307550500006030484001c0c91161900549813030b070b04003130340c0744259100010040460718005420041450314400da00520300b06156090583c14444180c00c103a04100e214402d20012984c800400354028003102c0c509a5030740c40c3c7c1746003a07103490300e558040d044110011404100344100c0b03512041a4031300a44481100007603d008115241c0300e8540d80d150302034000e1000b4003c0340343e603414903403100e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 3172561 1250 3171311 3171313
    0xb190203070605010e0f0a0501080c040e03040b07050706030e030f0304020d020d050d020a05060c030106020706050a02010e0a06060302030f060603030d09020102010b06070602030415050103050309060d14010f0503010b01020a0c050d05 102
    0x880c40c42d031100010303103200741c0000e04902c04035002d21854801c0ca81a455001c3d90141042066504100e00035460740c046422103071265448981d90119101c051049400070712500023850b07516070301484d181c1d407585903038843e00e00070925107410a1074821000c42110345507412501380c50318554550303003002140810f840090b60020524980b01000900802444813010a50780090001101911f0700620b8a88020300c1e4903038030442880104180c0d50001801d0017654280c0c10100e885405c03410007240140031240b880e01580c45040c040105000c0640d120509a90083d02a80d4542501465550303071102c0036110381c0c0e0181d104018036040c616140e44400030062052001044c0c481d048400540d0507013254000340d4040f980001400100468843c22810500d06c05d00107105942c51511026180d01403842010b0082c000004e40e43c2c650011a40f0150340d48180d0481c5080c82e50f10340c058100002e8481c018180a5860300d46261525800052603292181d4002d800713000c0c1c83d013450103001c05400c100000b00c0b09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 3173811 1250 3172561 3172567
    0x625050105070503160905030c010804050313090b0109080309011d030c040501030b060901080a050304031209230f04060f05040c030207080a0206040201030605100503040303051902070501020306040507090b190203 93
    0x820a01566004a100ea81c035076480342082d02281c1400d030507000201d02445040c0608110300c2d00c02040c0e460303040340f090a0680f080d640b181081d85c10761140550300d0100d08a000c002182001b1280e010440c41341d02a6100c007001621f940c0c2603941c03440b880e040540894026550b0a009082c1030305c60015030000030301641e2070b0030820f030b0206043d83c400b0b810071541d140070f107070030050641420341160f40140b00341001440750103513580302c040d00c1f442075010142c4601a0001e09202150103000000d006005001c006140341000d040442420a0048502446980c250b10313544507500d0240118011f66810505000c1c10310300d4242004000c0c200380d140c21003815003d1140c01c1c0400d00200c00703010400401d401034002840c042c1b000408690700d9400141c41140d0102d4003d120035030003001e80f544a83c0c141800191502c0d0b0081d0168211004115560300a000050f400100318040d0040c5010340780a607420f00c02c0703403600d0605880040e06801000c075030410178084131142d008042d075050f1a421850066034a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 3175061 1250 3173811 3173813
    0x6120b0102070b0a0302030402040b0307030312050402010c0b0702030306030615010f1d03011104030b09030708030601050a0e0a090e01050c0901020a030c06020d0f020307021b030601090b0303040e07110d020a020625 94
    0x111340c001e14062804281c1c00702c200030a41c2820b000b4018907107804c501403c01035065943c050302901c040c80e4a510382c159240e000400310390003003407548134213500022031180c42e1412a000035070b01d80c0101da6681c060b0142c803000c180e5080e8460715004101d8416190b004c030f10000242d044070030783c21482d030460090800c1001d58507551001c1c459005400d0180b09020b694504500708141010006020120107600803c2010041042501076070b801242c240b030010b60320035038542d084407680859250140e0150883c10005080106c96120b51650041c1c40000c1c031996850103040481c0d40514a6418056040b1080d0140000e01c14841146071a105031001410300324600c207075000b1070704130b4003903200e050b0f500200344031101c0e404006040d1000c0d100c090303003d0710800040102c0d81b5100103208034010707079840309928a03280c0c2d018825a80175169020714a0110b107003003000148590941c250004040c0513916075812014404030b580140d09402922803031800d4000b8403100741030a0801c142c10045d070811207000e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 3176311 1250 3175061 3175079
    0x109020f01050d09140a1a09030a030b060c0105010b0a020d0903080703030504080f030a0603031205060a03061e020d090c06050307050301030b071b0b041104090506040f1b2d06120b010207 82
    0x400c11005d044014000840310313180890741c0300c4585111410f140c80c1030f82008007600c400011200c09800c20300c1c0208808410300e0100d05503014401c10b1541c5542010b00102d007201101015081c15403442d0b080356605002200305844000a9001c00b5110001c00c020b42030209000c7d40080c0e400074403503140640350003904600042160010380d5503080d0292210010024198803044010350503013125010071003800c0c45400510154564130004001c00c0e02d84c0900040b00d285411032510480c410314081d5a541d80c1450745d40c00400c5d80030021103440c0c40040d00400c80501c00c100750fa00c03a20341503c900f45144d08640303848540751001002281000340f00d0741c01c007045490070390319084858400e10b1031600d40d080034582103240405c643d2030540180d00d4840141c0214000203080303504036800145030350034a40c00382009000b51b4cc0508000c041900b40c1440010204450b502c052052100c054001521504158145003c28198852034001440114005280326510741c08031600c1e00c0140121aa8203681e580da203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 3177561 1250 3176311 3176333
    0x603030c0f03070b07141e09030d050301090609050601021207050c0a060807030606050316050702040f1b030605010305040201080402040b0a050a0609091b0504062007030b0402040c020109020f01050d09 88
    0x141150400b0443d1010400007000458010085040402000c0303c08000c102443c011070b11505012103041074004100c140207804c94080c0c0c103014082d241103041e0045c0c041c2642e03100784200c9101c103180840014912140e03119441c018501680a0300c41128054581050354004d0042514240102c610b20384040c0e035043c0f2910001c0074507440e10075030b61400d58005402c4078034a511407c2400410420050360070822500ca10b043c10103414800d840e01907a0012034000c15503080c14400c0d5500c0e2094a0301c1c101c80302e2610ba0420302035640d00344607190303e03140111b00740c44081e00c1c024081002e400103d8010314081d084040407400190440b250640d07150001031101549038030000109001d040180314580d0103004115000740b41d20051241d030800c1c00d000800d01d1040b44200b80401c1411005a0014001d000160884101140480d0300058490a210551020a49080b4455031801f51081001ca006001c1c1461a58004003000c00302c14082c00103464590280001c10383d126a610b41c0280054500c1d008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 3178811 1250 3177561 3177583
    0x90c030102070f02030c03070302060d0c12060906031416050f040905010903050301060212030c040b0f07060204030c050108070c0c090203070c051005040201020c03061603021323010e0406030b01050402030603030c 93
    0x83c04104030f090040c9424002c0c203400b0680250061a0f090000d038950340200c403044d0030814800644c00070204c4003100c02c00c10b200803845555040240010305c0d4011070b0010342c20b990061003000c2501c1202e112041d9199548144070b510840342c50001c100d903140a0301c0c60b9840c09000307800485c8030610b50ba00c04d401c42c1d140710403c4011500200061200c1ca60400109990340e100c101c1c210b103141003a5103c6040c50040380b00d01d440d030640008201c0464200007041d146080d0340f040c015074079a81c5a01e80303210075203010701130580024000742c0001c005034450080e20a110f60003c03103c1c403001d81030a0840c0080c0d803000b40f100061180941c404000903504003d0344036402e11204002170103042c42d01c00281010007030710301a40701e03a01140910000c21209002592058080d04005907505841c10440b8002c001a80c03051400c11200388145110110340b0a90550915007681e903103032440758000410044980901010f4442500d420041c45541029801550040342c01800c0b079042402080140f46080c0001c26 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 3180061 1250 3178811 3178823
    0x7080d0c060e01230106020304030503030f0a18050604060f020414040c0e12010f050c0f031f0308030c09030705011812080405060703050d0e0d0f050a0c120e0111010905030403030503090c03010207 86
    0x48465044d00d80c405045014205500c09540307040e145031035070fa0796408054503100c207043c038800100386036011980c000603821484a1910380c902d011800c00c15203c5408450646409080000395600b8840b544212030580310402e170f03850560840c1e0000d10005148000c0080103110010404020607920284240550700301c5e4000892401d0164070034a0982e05e0282c01c0018882080c408028607500306410f503948060050701406200160346204000d548441d80003504046001090084640540e4005d0084001c01e80450b215581e4071001103c0784004010f1020b400e0929006c14040e12400c545035554080c050401c0605054803580000c1c0c451303002c14000c07004035000040d00303202c94100d80201c00800d604e400160960060089002d80b40041c00c55814040000009045090320700600840014a42068140142400c040703406007001c0340911000e404101c098483c15844001401179041c3c859115002c0c6007010304c2d40d074040d075a6810280400300d2a008507010381e080d90b142407029081c0e00307028a27 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 3181311 1250 3180061 3180101
    0xb06030109020d15030206040b0d06031a010e0609010305060c0904110406030204030c0e090a020105030402010302120106030b01120e0705060702030f01090605040b0a0207032309030f0607030e07080d0c060e01 91
    0x40d204881310505000202c0c2503104007000941e807242c0a42d0200d804a0020355661a5402c062000600590300000c0508a4a0380c94100707000b28134400314103075030041c2c90b4410700d07840d1382c0100100b09802b440001e0403640070000043d903d00080025103520540030344040b03018040f100142c074a640094010400099003c20301304140407030504c1c1200281080358000c48a82000f14401d502d03032446030300c007a05100300040400d04691180e41100c00980d051000345182d075840c3c43c0010003030180741d560203000030804480c050855680f03100d0f0b01c1c94082c0440040c0380043c5402c040c801150440315081e40d06000745180340c04d000400f0301a21054078850304000070a8034040c0b40110540d100580412140c91045c4601c1d00084d8210303490211029104212a04450807410b0340ca207207209240c08541c06000d0700220344094080010118060200d03038400348080c65030024195500d900f28031560009a000d041403500480c007480d40351900f14040e400114544809940c41802e44038040d00c09800d0695074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 3182561 1250 3181311 3181327
    0x20f07030609060606050307020a020103020f0706090b010504050a020c100c09080303010b0406080c070308060d02040b0d0b0a050a0b0108070503040510020a020a030909050108030a0509030c030f150604050c0d050a0b0603010902 99
    0x2d8404c1c44007030091420a14110f081c9020000d55442808034002e050581c0001d007400c00007032203402e80d0081c030780c0200305002285ca20b19000c04404001e219450095083c900801c1c0610414001d07514145500740092140d4402c0400380e42c06801c3c4c10141380700780000d804011032207200500045000e00110b49956646c0d03850b040780100030640042c1005411501400301500081d4801c440c0394000300c2c1102d180f800c1c0c04050001500801d00300f4810780c0c0c45a08081c0c2e0700d04100c10a80b41c1449118403080c20406030f600c40705600183d81103110b500f400107803414002000f035030048010313540090141086a00c90b5401d200c114080f0792007104821b0150b0301c2406050100b541c00501c0d403024044c504024000ca5140410081e500d0144060072002d000e800701e114440f9032010440100d043c03030000c0441e094100c0004070243c80b0341d88480421049420240014600d003858050360b0301400c2c42820803407402141100e10001418003030450200e00c1c0e00c415200589075204000745020700b01d18140180d4581c11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 3183811 1250 3182561 3182573
    0x503030403090f050f01050307050309070503010c020a0302010501050609090f04060f1a09070c03020303060607020105091807090e060109060305040204020c0a21030501080303150604030503040612050108010b030d0e01020f07030609 101
    0x140c1d9004c0d511562100f20f015106076840803c0c1c079040001400c040d612500d03040c1480c2e0421165811907034040d80780c88043c4108560011b810162180684c0003040243d88503024804188a0482002d0700484602c010404d040b010901040c0c2c01400340c0c03c00a4070075080d8803514280d60722505680c040107811300c40100145003141c41c95130000c0403402c003a010250715030b501039101c3c000281f0192180c10040381a02c20359014a046030032900e0000d221549100c2c5c003140b0f00001c140240e58280010714494004101403400e011143d004d84016100c0581c0d0500d031110480240000410880e00f06030203104078080502c04200c24030045101d40c80c2e0078850501010000182026154030300205400e000041002000200490f0340001d683d904000c04070300d007400805c1d5648925440141240f10000300000e0465018010003030f01a030001040c451070340d0702c4500c28260f030303040407046526810282c07a2409086c014003c401007a401070059030561041220000c0c02c00015901c183d2700961948400010008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 3185061 1250 3183811 3183839
    0xa1b0602030403030f0b030601050f0303040308040801151a091507121706010207031a0604060806090105011e06020d18080a03020f0120040303050705010b0406080318010206010605070609060603050303040309 91
    0xb8001408006e0710005000182d92407106118a41c015a16200944160346081c070884001c2d5400039481039840303a03141c092500034011000340d06000303008080b000ca803d0b15071135565120038000725100c604152054081145245500d2000d1007030f11000c2220b1000a209030119001c9607280e61170700c007036945541c032000c0040070004003400e04540103202c0600005040d907003440b1010b0941d0312040016a01c8001140051000e60032154051003042c04200307281005400c518141e40b04001040d58a8040b0b500404003545a0700511016030031224a0f0f0360018400c010800b403d0202100b80c801c403581e01d0000c3d82c10440044c90940040c3c010341407100740140300b4010007084105d4081d25601c2000507000603041c42c0600d02004042090003d01d00040c01404d411164107030100800801c410b036a94450305a40e0782c04802c403a003171181c5034525420b40f5800411114101e07a81921036518103003082c2d40d404014080100c040360602d0b541e10340400840c1041001d18403861003511290b2403103040007000c001a031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 3186311 1250 3185061 3185081
    0x50d060801020901200304030b06030307080c0d020708150703020705100c050904060506030402010504060809030c070f030302160f05010e130504060905070806040807031b12030213060201020304080a050a1b060203040303 96
    0xba017001414100c41030000125030449410241d02c8145403100d10000b41903106e008000b414140d8045109040d02601185a1210214603000c0324000b50b03654204981b0361400c50483d4007a0352111000820560094004111b114428016101007c4150721070308212074038240030740000784001ca05501d0a06240c850344001e81000c840389402c41c505940005c1c040c4c441ea0042c40c0803c15004049404c485c010815140c0c1e440305602640c0041e030300d81d0f0700199800c51520060300144143d03a80d241060b0314000c0c19009940c1c58070b841003121740c00e100c01558504e04800d21170b9007054207194450b10440031762190710302852160202081003442400c160385418500e40014039181c21040900000071000c0d4102c0e6403080e8581415070115100702c031004c0e140f4400c642e010f0100300c49451400c017002c3c0d0650042480b506454241240e140c2c070707030004034200c2c001202e000300403010401915032514041c00c00f4000da02120b01d05402c04400c803040030800e04e40150000c541c819000700520003015018081c280d216 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 3187561 1250 3186311 3186347
    0x60506010201110708030408090a0e0708071b0b061002030c010e06100503030a080a0906090203030313020a090b0102030301090222080106080106050f0603040204110d090b010515120406050601050d060801020901 92
    0x8901d00340c45001c52840051f00c018240100013034924829298125498010400e0f04120a52032170115400b900c5850704032402000248401d805031841c140b6862a542700a0308250501c0709036489005000e2a11803a42e0494298803050000a030310741424041c02100c0666a409000c06040103039004408000c560411440783e0802d024141d05143d0001c002c3d40d00c0031a500e000b01da02682810810024092040040e4141c00b00008100100c8581c02c4198009071003a52940c0d859503482402e001281ca1140781ca60058008000400c008000c0c2e80107841040740081c08129840c2c28422040c210b22010b034010002651140d000b081200b100780f04940041000713586080105c41d1090005100703200c0204020711442e42c81031942031054642054900c0c07a14041020000d80c2000e0608000304c0c2424070800d446190020400180f000500c0145e031480c1c0b283c45840c1a0a031a5a07985801030500100a03a040080600900c035028195007c0d10006040314000142d480220b20001041031820b51042860 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 3188811 1250 3187561 3187567
    0x5010602060c0313060501060e01080c040b0702060304110405040506010e0106020106060504170a060f06050916080f040f020303161b0302010e04090302010b0a090506030d0e010207030f11030a06050601020111 91
    0x9a4000c00c84590010880006a80e41e0781c59030300350041074449034006001586070400100751280c0009001c10700d40c03c2600e0713880b201d40d00d803805440383d8840c50080d0b0120210038804200107080000140d50868828850302481a014a0100f802c66804507420390316035000c0750040018101404109000d0000351009100c890706025002d0814402c521400740990003000c805000081c040c4a0600361b950310030303070602005440c0c40020010f0220303030142502c0303070602c580898141813880d01500c034403400700d0726011100e44c0c550070380d8034528030014001d8a488502800703200060750244001c01c00391014400720943c801d4241444006100320496290101000d80c0003400540c1e080b8200144c3d0b01c5d012039000c01c1000803450201c2c0901725500642d9044200b994000c80d540c000c5070481c900c1008141e0407110f071030002c100101c85504c0002101030140e0451031060000c06c641044d09800280281d40007002110240082031030301c0381018040d100b10740d0380c00900c039003580d0a0103884d14225045100c981 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 3190061 1250 3188811 3188819
    0x501020405090901060509011802070506091605091003030305060307120303090c05030a030e12010e010203010b0702040e060c0403020d0201030e0607020601030303060503070501120c030b0a0f030b010b040b0901030905010209060c0717010501 105
    0x200403010301078031100d105450390248441124ad0115102940e00c10300b038510301e082015001da510421401080b5101502d1080420f05042c00402d0350300c0b0740c1e83e041103180c4080c59a20f0130350080001a080d0740c0c050041c4800800c11a00340d90302c4002c0f4611a0340c00103001c0c80d60382410900b450a68000078425005006c4000200798072042c40507a4581c00c4520300c030301c90852043e440c0106000c10101c04c1650000c80005170001010019110080c000d44060013110240c81c4803d844620444a120310800244002c0c030150030041005d00d01c240c810705002480c0d40090316080e16219040b10890010b90003e00140f04165241c02028001d103016401003014505000000e000c48107025110b4542d1035075500f040701058420380110030101e00c0608503010301612010704605829045c00b040e203228640f41c00004400c44020304640c1200c0d0561800c50901140000440c064482c2003001c1d261590244180701c070030b40c0c4000052807000600f00c0101092454030f40074001644505a150940f80d01d4800100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 3191311 1250 3190061 3190069
    0xf090201020a020909011506050306090c0a0207140a0902070b040204060f0513090c051011010e0c0105071212020301090603111c020114070506101806030809010f03020c010905010204050909010605 86
    0x102e04180d04461080e03890b601c00c0b070202e00600d01900054a0450301080000e403a94020009502421085e12840e10503520a81d20b81000c3c442c80e03086500584c005002004005820039070852002c0d0010101c0326100d6895204070140d81169000360348414001041c0b204611300340c85440300038400031215544003803506000541e02141e100004440b41d031105007907402c02a24400c1c0401402e4001d000040c84400400c1c0204402a60300710035449e507203052003643d05040005003400000805959084c80e01005035601444004141d0311801802403800301580b42c1500d42c00994085c01750340e0000913005280d400c180b1030fa08690841c0344d01841c229041041c015880e00c031040000394080c00d003402408a542c1100d20188200e11016041c0d02501307003406020100c84005400f12011355000d09800034000c111301c011556148001806048100b0054030154002c0034610700107031003401c005041c40081c0b0841801d540d00d612040b116a507000400b8030152030030080268001d52520020454282420085 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 3192561 1250 3191311 3191323
    0x1101060b031504090204020c03030603070e0112031d0909010c03110306060301030209040f0b070201020a09061e030b010210060905090d090803090607061b0201050103050c04020c030f0a030905030403050309040f09020102 96
    0x2040010714600c4402c0e40a0b103a40e000314640a5000e40110b5481803403890381e0b6241d420545155100e800399400004407000450342e0300e41650040c1e040300f0031812281d0780c00e1300c40c0302c403200070318416207000b07890030090b565690f000b14410010600081948550381d0740c01400c0f981d9900a52544040034800d1014648841041c1e0341901d905890000150300e641c1001101c2c20607035440109020080b200700710862b6819000750903042003a844c0c0e281d03101d0710f0311419224440035001100798110410b002c1c1f44c1c0340f07109400c1003203051010b0044e110024002c00e14442510050703041421015207400c01d20405007020480d01c01e50240d286840915641012113103a00c034810141b880d44141408140302d030a0101c107501c0540b140442c62403035501c0003078030403000e40601801d01c01651a40615040000075081030300031504504a141d02540c0b50202c0d81c0380003d215080f02d43c2c2c42c410180d07210f06400004004100400280d03021b000219110340d440d508001c203031030003a2000c5188500344649600140d0700040cbc4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 3193811 1250 3192561 3192571
    0x80114150a0302060f04030c060c0203030d1505030f010e06010602030405030d0809010b0604030f0605060301020c0c01080c09100503100803070807030503041109070302180a030b061002010207120806011101060b03 93
    0xc61505440c800020307224503190700040d6100000150184483c1c000e100284120b030301c0740002185117907407100c0907550f00708103100113501500108460b0134a03c1d515807005080a0704065402820340d01ca502003403924844840601c644d0395200a00c494103402000400d005110500c01103141a0801011a480f103816014800c203200303d0f00040380d60404290003002c15054040c20840d1503076038a08000e20521310f03103902a11414034000228209003018000c0713484e40c0798003030024150b0780340340703c01140c02001c01480060880014052032142d44d50310302082c0c01c03200729941c6907526428580e0004182601e03950159041d540100170910005400713509451220350181011612640c55050002882151b00e11581d80b040562081000d6190158042c0048906803e0000c07890a0040c040c003a0b810030f140009804611050001040c914100c2c615004c02081440050705040c80c80d41d5010b080454122a5808100e0a0040001e01c0d60300003404c5007440d50b01c1c4001d04c01141303411020740062001402c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 3195061 1250 3193811 3193831
    0x506030c100509090a0f0507020d0801150c0501020703020f1c02100209120a0302010203010602010c05070b01090c0c0501020307021e0109171303020901030b0103020405100803030c0d1b0804050106080114 89
    0x200040e0750003941600c0703a07400d015010307000601d400740a500040c103256008803085403404010410413880094800c1c1c080c2c1d91a02d500b6207990803c00d5445016450b254114200040f0070013540c001142030002d0003105100360020100041c0c4500d490b410700804051145001c5250f0ba015803255600207521040021007030f00043e0f50340a4107001c9040b61600000240703661180c2e068403410150305500450490342e041e80200900c80702554100c815101d051006030100c9002030051009600e60391114040c08007500b400700d0104000da617520b082e0303003040b00c030341d4050380014508004100710700210013680000380008101b140c55555a502c002c0030501000c00c1d050601040090340300c2d00588032038010b9600142001410343c0e4a16111032120000d01041b0f0041e800c0c0004104203540101c0600c080d1203016000d0350650340c0e55480200c403504406101c400c4943c0b078a0902044100100c003a4040712219903400702d051419080c001d00b075402d5984140c0700d9a140c5040041c104460100d400d0300b00c20034070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 3196311 1250 3195061 3195079
    0xc08040f0b0703090f05060103060506030703030c02090603031b01050a0c0807120908040f080304090e010b100804020f040207060504020907051e0d020c030a020307030f0804020a0e060d050318040501090506030c 92
    0x1d00c00f20001c1001c2c0030700400c902440c000e40400c3c00800904c85041b41d204000c24002681c4170001c0c582c440c48284401408626001e89000c010b152941c1c01c2503010001804907420903d4030303801c0104401c1ea80c185501980d550328280902c100503802a042030341e019061407010707401e00d004010910110740481000c41c0341d89052100405c00a402107500600b00994100310440e243e0791032a8030396005202e400da03018134000300f9030071a5106011311400707a400186120140c07030300c280080d00d0aa0303004200701c2c1d004074800801c051030350342d40c03003d000540d004a00c0001c59141510500000d00700c06408441804810720202d210059622400c403c0307490b201c2c000035220384070044018042c4c0551072003d0b02d203001c00324040900e9503002016081d418040c1e940c14141403012102962a420700b80d501a4004014142c1800001c541812007500503101501c144052840e58580c6030860300120265203140b512a10251030700d29007401260b0140000c3e0004101c5410b1040004e030390341e1001c42505004550903 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 3197561 1250 3196311 3196321
    0x3040b06040207050f100212060f060301170f0111070b060406080d03020c01020f03131208010e010b030603030702030607030605010e0f030c0909070306050f0105040c1107180204050402040b0702040c08040f0b 91
    0x9011031605c890a103000c48282040c1c1d080102e0280d00655150b600700f0120300001001494440c1c42191403141c041c10161035a400c21441a4600f080c211986d4a503210700c03075418002103030074400d86e4500000040429160b4026261400b140b8002400007482030782408002d21110102103442801340c0418140181d03107a403510740703080c0640620348488403070000c04030400c005c0b40c620340301d46810984a040c088091051880b82070b19031241c01c0c01510300c05907101005000f0f10500100454012400508403400e1084590009207000c1d4212000780000391500303810009541c0254200c0c0b080300f8212032011181a000c00425500d004a4240621402030300c404120081c506108030000395030840703030070710580c903008250740c1c1030303034000c0c41100c2c0940c0c0b4048110311118480c803401442a0f0608024211300d41c81c0480c8452611100204041c41135402c0100141907a05d600c0200014501c5000058880e00700340100000c417002d0700c04100520504504000005a907404020f04095000c82050070139152 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 3198811 1250 3197561 3197563
    0x21506010905180402030105011208030103020f010504090c020f061812030601090f0303030b03100204061d01030e010e010603020411120a020c16080a0203010501080705010c0206070602160807030905010503040b0604020705 97
    0xc0703a803025800c0005141c0700c00b0000c1030a141248580d000f0f40007848180da030b031583e901000b0001000a0510a020b20060005140280f02061802c070145403903410141c6030b8070014200c81c201561f0001603804030360110840001403050552000ea08a00e0380c441c601d00140e500d45488810254415a07040080040c2c03180e1702980c0b000307025220b002030003202c40e80c503840c001e00202741c1000c00314868450705001e198885454004c59040e201280c3d210305408248020f0741840c03c201940040c140741d01c1d00c41200420781c0034481c0e07840c03c1e45081e00105e145840c50040c04203d4002c0c13001c0c00d410030b41c100140d0007028151030f54270b03801c090702d0000141d8a90b103801017541455580078581d2450300d00200d00044404000640420f03d600840003001640d0381c03064115901e040e0341c07081c3c602061200780d101015291082c06441620701038400549445440b00c027084444100740070449210002064030070a0540c40503204001d00000e0134102c0c61428030351240d010980d0000c0c55648103540000f071350020000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 3200061 1250 3198811 3198827
    0x3030f06090603030c03020106050603041a041103030c010c110105101809060906020301060305060d1e020307030b0c04170303010602030313020d120503090c0103020910030507020a0803070504030b0105030a0302150601 95
    0x440c1c1c5000c002e980e0f120729004111040c205000d500544c2008804520b6107044002c030303402950300a4240b101c1c200340015441d0440802841560003100390700d1707a00c0003030301c040c4003c1c0f005a40180000645501920300038204452a05000309241e15100c01c20503284c8400400c1400d848a04c0d010035440d820303140c50b82d006072540401c010300e5581000607503010050780ea00558181c0c2c51a4405002030354810060000c2da500110000d00134014203840049400f1600c0d0ba080011030001e41502c1c81140c41e5182c245a0000645401220b40d100007410005910f03c00040d8600750403e00140d407035949001002503a07808007038171001d0080c20142680c4115940d6000c0d840e075455100601000c203c05110014015410882c3e581006024208400c0308662182c030031a110407000603d052801e00c500740c4201e0080000500490a502ca92382c540008101d807400514400e0015695040d620f40c21440c18039211030060b403016001c0e40c0720320303030070701c0000c1d00031402104c40a074005200d011303560703501c0040b10401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 3201311 1250 3200061 3200069
    0x3020306090604050619030b0601030b0f0108010303030f090203120a02120408060f06060409050a0b010f03060503030f1806030411040b0108010b0304120e0a030507030506090a020109030803070302040b0313020102010507090506040303030f06 105
    0x5404071b0000010002c0a500341882402c2c240c904019220781c035014442003110b0130310032600061940005000003030007035012007902c00d01d1000020719264540e003c6450106100004030b455000070a89004607a810002031040d8510b89480d03604052034945407a980740740c0500400e441ca42c1060000d90b0b151100e009403401464480403d0019040440060001744001c20344a0300194040072804401c5000740215421034034080d008500d452280f040005058004001d015094004142c0818265680d04003035400f89004031004c1c00030314106010401100c044036035403818410f00e08010001101c0c00c50540358170903003000d40c4105102d0440301c02c0700d030b5100d84940658041c00e030120202c00d00c0000601c03102564030510488210b6102c5013010f903900c02200314024005085c1100c140001a00c00307020b1600401030f4100582490303118a00802c481c0c104a61611030741c07550082c06000d66034240039042d0808814208480c0007410074006c100b0074421f40c0005404c0c162200703405070b8040c0c3c0c9644488010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 3202561 1250 3201311 3201349
    0x20405031c021f0504020306090105090c090a06050306010602030301090f06050105030106080702010603050708030901090f0506041205010f05010303030504120306030809060a0903080403080417010b010e040f0b04110910030203060906040506 105
    0x3c02e42c00c161a00003088103440590007841818000740900030144180ca006441c540010007440404400700305100100621270440035460b4100001c594604000d1140a481990055520388d070600d0807040c2100d01901d5480001c0b800e04c0c50410080e41c00ca01140e041d0342c102d1602c140d50b03030f480320403d0f805043c00740d0004109201d80880014520030210141c42c0e5000240d8851400706d41c1c03282c5400070b002041c022554050020070040003080d016244d28000030b481940003140100a0388400001c0394026403059020a49a01c2000100491a000c0c90340041003400c0030000b0320300795100c1040c00e020702c10065010701c50001d00440158080c2d80e0210065038440300c042e0342d984e101c1c50010103e421502c1480380d1000820070004404106010328090900706954a0313070380402d81c1d0100005024419400d00c90b60395070b407000d4802615180101076070b0505104026969061143c1481000a56400c01004252040c01803002c0742da11b02c550242c000384211804034007900d51500142c201c01c18a807280030741c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 3203811 1250 3202561 3202603
    0x1050414040219090602010c020102030114060a0207090e060103020a05060a020a030503090f0102180306010f0e04080304210e010906030204030b040206030c04080d0c0201080f040510150b07050604050709020405031c02 95
    0x2c2d26403200007039003a01c94a1b030084c4241001200140d00f40c0c0028028823444041c51800d003040c504042d80944480621841141c12072580d4452020031151000a0031000703802140050081d42000c0031540c000700b1080e6201d51900c8441500291183c28412005040000000104401a8003044032040d5051108003c6507200301c500e101840441140051600074001c2c0000080c64590401410044600040910700150340740e0740c68004980c0014001c40e090390ba1600604040c050030700c81140c0c60aa2921000040c0b03e1a80c00036290406a41c040c00807d40108001d00000d0000c0030b00c25049513054854984035201c0150307090042c0996080b02c5520300c12800c1203051242e2205200384518000e882e442600d4861950310600c8240444000d4001e5002410b800e01845090f4030030401d000002d1031b95016a602c400110000d64040c010036207040d80304000788402d118060100f8001400c040d9001c40c686440c101c013190f01c0385500100c1156003640981150200c60080c8828402d1042c602c1d80018 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 3205061 1250 3203811 3203857
    0x1261b0c07050f030604050604080a02010204030b090d0909050105010e13020405060a080a0f06061704050a02030610090608210c010902040213032001050d0e16080106150c02010504140402 82
    0x181d50405403080720f1280596440c554018200450610302603500321024210a6955449031070040c0c0c0030440203004c541d803c200001c0170542c0d8404160042002001400124903513180017410b01c101604400340c0c082c505001008607a8009039100c01600d07098a107032800144403681040203001c0c5030300440d00000009420700c01294850642c510861010108004100c0d841c101c02044400034001c240110708c0c8aa64a581050b6090b120b03584940305200b00e1f0510700141e404a410800152210340ea504481d14050000c3c2215000b441c01a001e00e5000f030a6001482469681c141141ca00b0b01c0c00081001031416183d40080d0007403035405401610032b6649144920a01d00340074664802079854110701003902c800040d01e1240010520b00582d181410302c460046224002c280c900000c03840d505c241c80104004408041003040104810000000e17401e1400b90412004003500075040308001d01c80b40f8120041c0c1e0071500343d4050780d05132406a0704509038a0040f4000f4440c1c0035400c0c000f420744c076401340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 3206311 1250 3205061 3205063
    0xc08070804090504030f0302040302060403080904020c15091b0a0501080408040f060203090406050616020609041808030f07050c030421020618030c010507050a060507031103010e041101261b0c 84
    0x1071300840c401e84d0f5020003880c4c6140101c040b0f00170b0b40002980b11b032082200b04042001e0070040e10300781800500051829032450a0035180c0705180c0011920858034008115800c182407090106071001d100c224a040c242c0d4000150112015005035030501c119031000c1802d01c0720b244290750203003600142800006484290180d0b40380c1000030058811410310340085220b00b40a4261481c12069001074402c0710015402c0024a0308a8805c403170b0015aa800765440726200e4100c12a4207074054441c89a403411300413050340c081100144410140b100411185030b207030a000084a00b01c912031005d81000303844204014120300e41110000e5804078010030354411400c031002445031900021070032102a6031480005507011f000d5450080c10903008460f10b48086011030304203650105192400003906182815107101c10b810070307008003d51107000f00c10403041000e01005810401000d0801c08510032020600d20504091100200400c050b04e0011610080209805800c22a071010a0a842c1c8000724025 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 3207561 1250 3206311 3206321
    0x7031202060a0c0516060902010201110a05030a05010e060607060c030b0607060203070206010e06010f0305060303070b0f01030605010503010203040f030c020a0305030a030c0201050c0c0a120908010504030905100315060c0807080409 101
    0x44030402e0315081080a84900032030131250304400b04440e100c0d42411503101d03c401801c5101d01a410355494003e02c001444a502c024014414140c40300c5482e0f01f0029080e00031124140c008280c1c2071800e80911441c0d65452095611003680100d002c80d11280051040700503125072036140d60800300118810b4100421038001e075100b000b10358202c0e90140e0740c60300c0b62001d88a09860300f83c040b0701c0c3c2d82e2035040024402d1300459842080902128030704419a9190f02c0042011600d01c100c02c24a50014410410140a5140107100403802942036041985a88000c60903c10005041c455400210411034447c280380400035074000e419a43c5072140c4000150107801e0f8206c003280154a0726000400410308241a41c12184114009046a041701d590300c2e07904600341c001e54801c1c000c9958000400481c24084d040c40b0307501c41e40d45c5110f05850101840210b40c03017240410b0925040861440c03283c1c40c1c805403881201e00c2071a01540030034040c100b084980c49900e4018200b00d07030014002c58101d884e5044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 3208811 1250 3207561 3207571
    0x102010c0305011401030e0102040b1603110706140304020301090203010f0b0a06080405030421140109150e0a0618020904060501030b06030a05060115050f0706060501090503030a050301170703120206 87
    0xa02410302605400c5003115070034002e8409041030340381501e4055100c1d510003852070300309900040c9040d03124141006103402c1080c2d2512030f04800c1720781808059000f07103496200200b4000078070400303060020203001070261030850707041c1000200010782559825000503501e0354018000f004a103210301512009882c8840c041ca01403105090006a843e2107001041d114680000186080c98107003030b400e0031605141c0340080501650308000d00c001c203070406040320858042d81c0001504400c07501d000b24000a480402240f003615008040240031004a170020480c0d40c08840080c030310a0741200b00d46841c0344040080d400000950400c001c020483d030146060f01d005980b0010300b0341d186810903960704c60440c00140140c00030001049803085010045106684500f0310300c0c2082401c604900450300b14050985807641c07120b004010b00d50300044007101900042d00a14600207038032501510f24841842204800d047c281000c0407004000e00442c0d0103117502541151b0690000794000390754ad00d044e14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 3210061 1250 3208811 3208813
    0x501080606030a03080f090106030213020a0f0c0206120a1508010e0609010507020709090f021509040506060a0c0b040204020c06010602030d050a09030807080711030a0c0c050a0506090603040c030503040605090102 93
    0x101081c80c5240c005420f0850540c156100609640c4154441140c00c8016201b95000c1d07403030340004001640c440f02c817650901045440184c0715002220f00405041c40d400801782031100e02407242016884030800c444220b40980300e141d1041d20b802003160b006005a48102840709403500c2c3c08240c80300190072042010300c21404403074132074948002003800c96000b540c80c400964020f080401c466011504207200450144949100c1c11700d407038001c202d40080351042c0e070041400004601c01e140c9001c0c030600307802c46000d444182c02c282c211400079101001d40e40021b051892208000f508660740c640484034045140303001e40c0e07025691030380080c0da0f80d008081d030701c665030b4100740001c0c602c1c121500c00e004150b038065403170155644039101d003030740d004d4000341460042120301d000007140301408100800105581d552408441d21250921418047d400c0d048141f19030710040c03007003127166600015110102001c440640d682d0715245025580c41e90203600081141c0404100010b110303800901900d15134400fa0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 3211311 1250 3210061 3210073
    0x9080d02030d060503010501052103090d060b01021b0a060509030115030309061202030402060a0302071e0c05030f0303040506010b09030f010906020310050303130315060302120303040201020d020706020601030210170406050108 99
    0x1404041c01c1c1c4a09000301032b00100c04061984c06141721560000c4018034010607a4504202c40022440c0040d0360501030300c010341c54007091031035960304009940c042c2031020b40780c00c4244005d00002d80403000c0351007148c0800034003080b82c1c81d4958081d807092001005100300c0e603d00310f0382c83c600a0055841d43c8145404600104007410b01141a4002c681c8a240d000340b5503441d013106c005c0c05400a40100c5001e9803001e40c407180c0e20521500485500b0040740c014a80120100d01e020304241c81c0000445003445035400078410300c0000b80000500905645030144c44a8840e000c54001c28603104510280031200c0d0308224010b0203120450703000314042e00d030034440d800005803180e05050790b070b200700307002120380c480c00d100200082040080702c1100710941000108845503242c001030402d1500c81030010254000006110071980c04015081c405502400604100341c41c0c410007940710603052001078003e4a00d03a060801300391055a03410003002c08201800d600381014241840202424003a1080f184100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 3212561 1250 3211311 3211319
    0x40302060f0c04050d06090b04050c040e030903031902030c0a0b090d0c0201080402010810050301060b0414010905090103080c0106091103040302010608031602010e0d0501091a010608010f05010305040309080d02030d06 95
    0x100c01030602c18003100a42070700e450b1401c014002c450402c2101520001e5540401d800082c2c6130808450245000d04010401040e03541b040100712400d4041c2c42c002503004000284c0075031008001e607040038130b043d200d0301032901c250102641944211540d2030000d0142d610104208016043d60354000d080000445200491408041d6504299488007a000c80c0c207100000780150710803410306a00030320006059041507036400200c2d081d6640c9801c1821102e10114081c0007109c010500c0c00c000da807003444e00c080c0d03051602001c150503400602010700318440004008078000380940000d8000d00c0c8041d01089019171660119400b90010b81d011001035080980008004800009540381d16008440b07a403441841640159594504c94850b190046080c01110001c940280302e10442d26014440310714070441c1500784410701d000140c00210038801004010320071030a9500400702551420700700014680c840c0c2c10144e803030044c1036000d52803910608480048407075000c4080d01c2d074642c00c000140071103625 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 3213811 1250 3212561 3212581
    0x50108040c03080a180f140a03020f1e0a0311090a0903020c210102040f03230601050103020d0905070f090f02030603030a200102040f0e070c050a1115040e04030206 72
    0x4261409030050308070380410702c00706038443c2c01025030400c0d81c100482e6070181d0200780c82c50706005078020403800148940c20000078165041500c5120801c540c541c45080c1554001b500740d285601c3d07414010310145050840c01c512800404030394040041411440641c0c0c2e143c01114110702c90341190142036000d0114800380c2842c0250007145030f040c0c000c0c01e10500020103004644080071000003e090380d0b86421540c000c3d080c8000d00140c10301c04404201d040c11414098908100035400f00c1c0d02a105507820048240702042c1e10381901c00c24a400f40c1d0700c0700000a101c016088080d4003409500030413000041e000c170864a010111004c0010070705c03058109041d01e60403130204981203030309900200320580340a44070750a0048000c01c18165060402600c4110900b241c11a030011000c04200b48028420b04110300e10080e4030160301d03c1d0020318211203a440c075803214585080101101e41c503002007030030742e44c03071109076000300714a042426113a950701c5109002e6528240e80507805401380b074020400b9920 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 3215061 1250 3213811 3213827
    0x507150203060103060801051009050718140301050601050f030a0c050702180405010509030c070314010204080303010f030201030f09030203090904020a08030711040c08010305060106080c090a030602070605060604060e090c1603050c01060501 105
    0x450078000401c118502b822081c09458020110800c0144007008540c0c180c00040284001c0e244001c0d034041180104010316086500140086061000c10b0040071755600c42d5404607a40940c500340041504144070805071605e008203c1d00940c0300c07101181c404032003904200d5007403042e8003800080c0865241c40802c039880c2d01c01d8103c824440d811446003840443d50702d90040030b40100340c034001031500307566108460a58100780c0207020b00320340e420340420642da4180101040441c0320181005203880b103a41c00796891261051150184221000180c02e5589115414000b00907440c1501d55881151500303042091030034180912551610000724445803154103901d041e01c0d440030080510b40d082c42c109583e1014010041c0224810801c5800420b80710304000740000c500c01c02016031100d03403900d0b2681c10380380005c0605002c5e00f010f000800c5110303804652110451003e45818407503403a600301101c100d100300c04080d85180d190450709010075610030300801aa00d07912008001c110749030001102c07550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 3216311 1250 3215061 3215071
    0x16090203150105090d060501061d01030203010608010509040201030603080c03070c0806040203071707050a03030801050102010e010c120b030a05010216021e03030a0f11070b03010f0501030504080d0903050715020306010306080105 100
    0x30301c1c10344014907540540002e10302c80d18010b2803400d801d401c5660700c20a461090308010005128501a0001e0740300d00305182c1d9030007009007000d40c00c1d90b0401d00018490041445454480c070010030200302964001c0e441140519008100c2c60b94404680d1429035895012001c00c44410140900014110101140c107500a9500070090155949421602e18551581003804a0745000320030000900d81e0782c480d070f140c0003144a901c1d00202c41d850000060300b1980c0130811441241d0420528940f03d07a408495149000c1c1102c2000510000460100c0e10300800c1c8030004100d98400113488000c45442c00c1c01d12146031003281e0210308082d49001041c0c14401403041140c05900601600b0741d480d00840c15110b001c501c1e40380032040f40720084181c500d03021955108000b0360350000014881d80c008c2e1817024010301020700b0240054101a0340f41c06061240207022804a540e0303c4281042500c070700700b11010380d038000056454a450100c9207400035030040d181c19002c2458007800090b448418040c1920034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 3217561 1250 3216311 3216331
    0x30604050f071e030201050913020c0c040b040507020604030807051b010b0f060a0804060f09020d0b0702010506010e06030a0c030e0d0e09010e1e040303020405060c0105090105010512060106050f040909030216090203 94
    0x4d00d594010b4605800a1005a921003095120025055510301c040c1c00c0381819580281000364000003408103c4540c024440c1c090360810f0100080c85400003821500709030b05280070032041e541c01c1c108039460f005080e00c0b40320300c4003403072601c82c0d4190301500b010020200c00c4a68802070700162040104030b00c0395481d008042680540000c000ca690b40e4071610700300e41c12103c0442c01e81c01c0ca5002507426481d448088030600e940303100340030300c0355424484c1640c015070a080c0b00000000b03d2000a1060100030003a540254840d1403070010540710b078214541c103d503040e04070348240120245c00380c00a40844419030160f42541e0002864010203109140241a001c400c000000c2d00384422080049004000380e080c140c00304000a0961a081c009055840380b0b40c2c000500c0b801d09612050a407081a44040d20030155400188003510002c2012411640c00b03052403590340c8bd01c600c0c02c0035540120b030312108002c0d20f414441c406064001c01c04440d090700007800e03402656103460300700f42240000e0710602c0034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 3218811 1250 3217561 3217619
    0x10090309060807020309060a020102070c05030601050a0b09120f0a0302010c050307091511030310090e03030601080c0304050a020d06060303080709030309050f010314090c010207060203070308040308070e030604050f07 95
    0x460007002c0e0150080d9031031054900e003000c5080800c0f041d034031840021005030347c002858000d02c070280c804140506000c40107031545500d480c0004507207061500a48500f8500080c950566965010900103806900c80945003c0c2a020720619243c0801c03075400d40141d4200080d4500340c0c0c1c80341e01240d1003411152075011503142017003502c0300c08465007030181c41400103c4440d010100c030200042e52103a001c4001042c00c3c6404c029804007924010062801d0b594014802d00c4840e0b038010107216030211448050685954440c28482e140c080e101c03501035003141c0100601d005100068024400b40c9000340c50744a240d484601048403484014480030700004c0f82a10140124907054040d01c084080500d004145c0e02c08401c40480302a106440010f0365500a01455800c0c0d60103000d880010041c9002850800d4001c0c2c0340504000c00040c40102004148000034104c5801000c03154150f00024003100c00b10301e170924101e6501e0b02841c0400e44c451040c8080042c0003400340d00d100c00030b08200922914 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 3220061 1250 3218811 3218819
    0xa02060f0702030c070803040609060804020d0201051e0307030219180e15030f0c0f010903080409050a06090e060a0501050a080307060b03070b0d02030714180d0311070e0910090309 79
    0x16000c0c0c0050310140441c0000c02502940744401c12041028114010103956101d00d041000b4160720b096502038030a1000c00390400000d692010150b281c040c0e020301b0001c0d9141806906070301d00032141440c6060f00303031012050102c0181d06074050a14054880385000e281c2050200555040b6010a08480b820126110030f000003500744401c103400440209402a419820100003810f20850101c0045185c1c00b0145907a81380c64014140420100300382800760301107045d40c0307800d1414403403400b07040c4045846001050010250380d020b0300c010105101c00304030341600242c0085e103ea60075908149401d041138000309092600708803002c11120180021441c00d400d90b03844001402e6a02211035050140c1100021040c40c041d009010075050000300598a1030941c44c080c4c0408200c43c41104003000500c810307800b03a0703081482d00c504440222000c0c008010710340b8080303510040c140c00f204070074040c201d00040c4462036003410501034a00c3c0000d9500e4065445481030460b0003003003020b0005060100204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 3221311 1250 3220061 3220081
    0xf06030d030b010e040903180b0f04030602070c030f081902061603090203070509070801030b160c02090603010b060408010209010806030a05070e0903070506010e0f10050105040902180405040c03050d050a0206 91
    0x2c50101030604000b078201c00c507200041d00304c407002201500404c42100499034060102c4d42c1480c05080e4001d06c0c9810030340b1440d924002405103010041c07400d0350005218082c41040b036040720040d40d00c208054640a03240c1351001030750b041010000d540b20203200c1600c14250021600c907114104032040c15100030343c0c41d201103001c2d000940c0140c0c0c2500401c0408030b95515049406440360740f0390b44403070902d03501d5840c08040c100c6c8010400e601d900b10810503400007581c4071180d04005034040310780e00803503282c103000240180068200031360310401c000741c000388599046d0080c14580301c00340c80d14070066590f0030030b150300c2b40445c00e0001e0068000365014083d10302c5608440c0c0e00080900222410819165141071400d0402c0c0c110040801070310080040401e503580107107a1081f81204000860b0b0b1401002a1640c0924003c46840079000314030340011491460040c0300e4081c00520a006500b01404c2c10b8000c183d9600050f84d0902865540d101c02d01d00910032102c55250070b500400107552012140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 3222561 1250 3221311 3221321
    0x11070602100f021b030a1b020604051512070306080106080102030105060909070c06090c0306050c0c060703050c0928050108040b0403080601050f12060f0409030504050d020301020c0a050102040302090f06030d03 92
    0xb0711000d5402c3c8219010b51000c01e00012007a054007005507a9500c9031680030700700b100703031092028021030400d100741700684442003520200c480c2902e00115503460803641d440c87c1d00401400000106080080081a5515801090448201d600200001903c4141060a0b0300c02406805d4001382c1c20130030701801d4105001010b070302601310f14160644201681d01c41050321048801990010a542414400d0003a0b038800c03070f50014001c004a0b45810035841b00c4c0750719224018488814117640300300003141444e150040b00d0f81d0b0080100084061760710469030150500f40740d1a842c00c00340b18138001261a500a002c4540525001484218160b445580856000318001e1009041010610002003442d9500b4043c0c40c4001202c500da088915018050054400311000d00f54883d81c01d01c0c20a80109030844101c40540f20165040e25065200340007203406481030094004051140c0c5882c00c040c04410b6003e0010340c0d100f195480c5143e142c0c1000d01501407010b40d001c42c0e1641202159004180c001c0d800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 3223811 1250 3222561 3222581
    0x40302060a020106030b0106030501050a0b0c100509120a030203010e010909020a1404090807050c090906070c0605060f030d090f05030106031101080a090804060908010506060304050d05030405120f0405011107060210 94
    0xc03684c144c40341c0d030754035100c0740030381c01f0b000404e803600d006210500e40001c40e40054503242c0b10180c20520307141d0520740d4a24203007054034442903882c00401d9a0003c00c0c403010405001e4400d41c140d940780c41240080c006d6009215540d61100050000704091100d401200240e54004200e60001c60828440d0a0300d1248a4603950303006075a42c016100089105001d0440d03a4000c401804000c815035041c807000200042016250fa0030410800803002d03004013102040540208000590b650348001141c003210792042200c2c5e244c840c0282603a081d580c081141c0042c1c51103100186d0f2005c1e500c600381070176180d003804000c000210b812200c0c03225501c201c22141e0b00a07260080418080240c0d15040340c5640075030007000000c0d004107814800c1030002d003e03213a04a070040c1d54152942c41d0903158240c4801941016504100f000000705061050402284c0302c01000c0c04880c1e85e503091600500c2880f584648100d41c0481d04800250125890100359181220603d40140c200342a150400c00003c10079584 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 3225061 1250 3223811 3223813
    0x50f03090115090c0305150a14010201020c100203010314060402060a050f1b010507020d090b03010509040201110628020a020d0305060312040905010e0603070b0a03020a09090c020a0c080f03040302060a02 89
    0x8110002804051944003c041010340000d48400c40e54000301602c80080464420840c0c1d66440b201c6515a00041c004444000c60021809010030340101d029120300f01e0341103498170425010b40301c0044183d00550480c0d10462441510b50b181c00d01090f00d5810484010394010014004520120700400c003c081c051440100b09103808405601c50141250a00110b07400360341d590200f0014503010070010510032614100490101c0c942400c4284030700c014020f02d0b0149441c24007180859000d030b49010850512102030340d00500d0b002a02c0c90050b0441d181311003007000d2100c030181300c1003c90710880f00710140d5940035201060583e601074018041c0680b0030358041c40341800b03e4202440715400f50010b0401c00c440070501e5450100b41680c40e00018103858443d8005d41c0f801c000e5081c501048440ea28043e0401607200e440501e406d5904042503844052640d0500b9100b0365201d901107058400d403846546443c910607100c004036652040c43d000010f00540c0108000d01c054a00040600000ca44900c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 3226311 1250 3225061 3225071
    0x212070c0302130f05070509030c040207020f0a1206050a0e030901140405030f030309010e010204050a061d04020703360b070203030415020a03090602010b0a03020f030c060a0c03030509010501030201050f030901 92
    0x39000c92001c070b051950358980303a43e44480d00005010140200c0340c002d440da00c7c12600b071444240001e034507100200070319031003254001800002c644035042c00d1318400c90000e0500003420f0360340d4205081020380560480d4401e01e48800035034600854481c40140c0980c4200075400c002c0109c0064800031580d081501c0b51103414400014107070b80c10000ea05024040601540c0c0760b00304000f1590a403003440040310f8a90f40140010f00c003030744800e10700900304d400f10b1514402000000c20791070382c4103c0800c0401c3d0001d000058400925800004040d10900000c0c02400038600001c40b0060340051840b003001503001c1c100e000c001c2051413101406003140020117407890681d4603860526010135044602015030803103a0640185a000100c24000b003034035000070710500441d00d001072084060b5000091040c403691003041d1880d2020080c45c41e03d06d50240c031a075520080301c880688400d1030058210700082c24080003e804441c1802514100e944c1038441a041c030340c240d00c0100144d00011324100280d90f80e2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 3227561 1250 3226311 3226313
    0x10b0307090e10030201180e04031803051e06060103060302090105040f0e0102042c010609050108070e030d03050a0e010204120602031e10050a0905090c040c020102040f030803010e090604030212070c03 88
    0x842c00a0107141c002c00da072000c0c02e19500c000341010305e0004000140080004040022000800710141d01c240d0516151011074010f403165980180d4540003c0d2851088401c4840b600900070401610b80f280c000865003241d842d84011001e41e200d50200940004005004111508246d000200c12a451000226003a9500c00c861404c91308940e102c20130b40c001109080300e0300c5449504d002007441030088002055810180081c3c040c00862107281c1c10040c640c4002081c2510902030052285002410388008485220006029000594487c0f000c1c5291405028a00c0e4051003140c04540303a0035001c08004030319444041c02500020524a102d56641000510a01d02e1203100342c8250b8450201621550030641070100550182c3c01c82d40880d8981424032402500011745080c05041c1242c01040010340d400040340a4000c0c1c0c4d001800a8080b0030000c400c10480c400514103840c01030f080055103640c3c030031540b41d5454090741c004e1b015070010201070304443c03c07000050403994000c00072800601c1c0c4e2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 3228811 1250 3227561 3227579
    0x3070509090f0105090601020a050a0b22060b100518060702010507050f0708011811090702010609020408010501031101020319030207110d0303020706050601020706090501050309010609020307020a031101060e010b030709 96
    0x10071140c40240c142c654005115501d004c044882c0c0040c028030003405188c00680e10f60b136889a00d0322015180700d010000113030b44810002210680207003104000740000d2035520301035000d040300e9200540308070410912200c440f4441d0b81592403004205081d8030390711802c4001c2c0003541d405400305904120041004201090003040021541c00360000104109850803080c5821078840400c4c55440c40c0741c0c0250800030a0410b4605050716400301c519480e1515000010b90062041c0d03403040320084d0021400081e0088194006c0741242c0c020780a07140c039800c051004907164420320710312922017a040d440030f000c01d80c070903400390031600d104d02008200d03c0404000111003404511040340003e07000100c0a00304640343c0151034001000b030004144850810401800701051401640e041020210000300c40e003809401c2000108481d400456803805c00e404000c1d1109644c441c10380209141240d192450394051140004540c801c84103244140d0030a640c04001e940090441c7c8100106040007103600c01d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 3230061 1250 3228811 3228829
    0x7031403040812070803070509041d0a021201060e13060e070902031503070605030712090f0c03020306010b03010b03010513020c01050c0904060e010803030403030507090e090109030801080313060503070509 90
    0x5010008640725031a00710070614054501080d00d400c2d0106000d058002030070b82007a00c0d0085480d0425544513440200410000c0a01c48440442c4988004111050f0b4101090781c840140c0251b0303011280d03a584052560030380304140300e40410241e8140004520b09900111450080d00c00c10000c1841c1585807007091602649410100311070343d000040c0f084251000c45180e00d82c04003607010340f65661503c44050701c1c07404010f2140b814003060000c1011080200d81c0b0180140c0e2344811415084850340c2440e100241c0140000c070f00038030810001041080719501564100c1e85451107040c6036a00302800d1100d2414a0201b000e01550280041c0140385428010726216032141c0141503110680303907042000b520003591001155880480061214900100450740d01c181c15050106668942c124201c8091b4507035440800d0f141d81c10403e000c5d82003030640042114a02a0707a803003a07141d89502c0801d40b0303803003206810030800325400c500f0800d05020340091640070046040143c00c000c54400070820300b003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 3231311 1250 3230061 3230093
    0xb06120108060709050d03080a021606020403050102180a030b01030f0326040c0909020603150607080c0105061e030307030c030306090603030e040f05040308010308030a0b0d0807030f0e03030d05090703 88
    0x608042c040240d015800f10f410002440e0494840c6250340071900c2c00381200070040c180c0224580c00182c600100080d5811084240d42e101008560703c9070389003080f500030340154400c10040391101101d68901d2030800d501d201643e07000b5401380902d91039a034400c6024081d0003021828000c04000710b40450040c8d450081c68080c801040d500246020f18104004115030741066802910305000c0e00050784a6009a13070f400b40c1e449803501e20459150000515500611038014080380d0000340c400c01245041d0412809414180c42d02c1e50903034655005c030004150710003035042e09a0b00030b22940300440d120b030340c06a2006e4028200025030742d80310042a801d4034486d0700182c0c0416028000551641010300c1101405191244c2c10030140c00c0c01e030341c010926071040c0300241000c00701001003552040141d10031030749030400624003224060903180180c0c0d00e81103c1e01c1500424100200185030a0040c210142d4401c40203001d545003407100d03240340000f002c002e8a48643c1340302d0408040005110804050410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 3232561 1250 3231311 3231313
    0x3031104120309060302030c040b0306030f030301031a01090203060f01081005100e120607020a02060c0c03010903081806010311040207060603080a050c0709020c0c0d02030a02090a02031e0405030304060b06120108 93
    0x2949080c10094a4643c0c290700c400d0030980304004200032030300342205503000d0310341e030106096403921080002498a4045216481c8070300001000204000115144402001c80b5a0000159a82e90740030003049000840d042c9402171800019500298411440140d024401d0740d114030300c051702c03540421004100f401114000c1480c0042e01c0300d49180c060304d00c454130401d807002440d43e490001002900c600202c07030000d019410102e40040000010300c952410b4030b0b80a0000c1240003d1403c005110703d1003500c03500130840c01904480314100780494080c0c1629002115880c0214000007031100075030010380103540c200d43d100320120004009000605900080f643c2d99920b4101001070241450f4195001218440c810459107030140004178080220002c00c880d000048a114000729051801600c8000e6001d00c1c0b00040068003100742c5d0145000f5039031102040c81441c16401030040d0a501580c1c082d0055109100040006034160080e0300310341030203440c0c02e007400803407221500900c0c42038000903d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 3233811 1250 3232561 3232589
    0x507050615030c030102071110020a05010e03040512010e060609130501020f0a03060501090303020604060f020d02030a1a0f0d06050a020702090703020309010c0516060c05040503070b0408010501050f031002030403031104 96
    0x100b490200401800d0050442c000c52410416913691007608203050030a602411801d448001564000d01251011581020003442034001004a09807650b01030300500d40b0908040d0382c42050140144161b00c810074003039000340f0160f102c070300030400c4101c0c0082070140e0340004c140701c1b00000b420038009801038207011503034183c0741d606152010f02078030b0a503044541002001c201c1007000c80c0c0e0000348507070415008040080d80f082c07120613410180c8185580c900c4044e00000034007014075060340c4264001481c1d816240c1030300301207200304544a0301070040a90701c138030880030610124100768490381d0000509100145010002d9002c5281114106c1d100b0001c250b021080085440c82801080000b441c189401460070509403040a140100188003038070a40d507070200c4500840c01181240d002e041d004040324450355480b0460001544a030244490550130310000283d1030500300318942d0510401009801e0555031640104001c1d08010800c1d01016100c80c401c040b0348400340002d101030507042001000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 3235061 1250 3233811 3233851
    0x8040305090405061201060803090f03030a0c1e020904030503070908010606050403031107030605040305070c0504050118091a0928020102120a0302040b0d050106030c020f1c020c090a050709080304050306010b070305070506 97
    0x140b2a0812f05a0130701940003000b22038101c680c4062244101540400031031550900c010700746000b0030a8010003504054240240f1084c1074000c805184140541d0396442c042070341300c9520740c0c2030742d2907845898003003242440180f0000e802680440748598180049541481eaa030311032a003502da003513505802140380040c0d00c0c428415150031200203070031300765814041e82d454564001009455400c250101580d2100c1c02030030440140403050451108030ba0146a0b0300304450156180c02c01c01d1a1078031804642c1c907101c000c0340c403942c58410b0200d4050b006000703608050300c6001d840f580311190400400d5400c200201d01e1a05010190160210f01c031030008256040100180807181c6660248007950312480320b01c05000700005020f121038940c00035011017659000d078243c0c40c110a40e03000c2d03a0302c0301440b000c0007490300b00ca9020358854906690f5040005030f6466016840c0d204a000b0281c16030084d10050010346094402400113034880c4c074055181450b15159942410415034082c404845d01000901f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 3236311 1250 3235061 3235069
    0xf0a050702030d0302090102070303030509010e0a030f11060405030318030408011e05011e050609060408010203090303070201110301080d0305070c0516030201020606041401030b060103150f030b070804030509040506120106080309 100
    0xc0f1404103080031440c12800f503002070740d00ca240f848010704054440001801c44a020b402030034215000301c00b00c6002d01407614006e01050382c1d512000e00000c6191295200c08a00042c0303e034043d1f034003c07001c0d42c550740381c81905200414100550415600c41000005414402446481e07114200324030204443e40c1d01c1031889003a40c0040c0d200c0038008201049000900400600d6181124001c50381907a4030ba04400202d0340740d0085034001040c81d4400300406ca98100c010008610840b560b0b030007001406510402d181d40342c04207000d1400c09a203c0b6161441881c003035400207800588030300b0b080d44000020303039441d4501441030407c0a05140c0e559402c00c210758041008070b800c540d040b282480580309014040354404030510020303000310282000320b0b031981d0207684200d001c0e40030401d580407500e450b140410240580ca10044442114240009e1411072082c1c41075402150b050350f95071320f06101c01e0200005170102814071a0300440703800c480248c15900b44200303002001424007858032400c0c114104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 3237417 1106 3236311 3236323
    0x100b040e010603080702040c09060f0c030c080309100b06090105090108040804030f05030403030e030a0b04062301080708070801060302031504060f020f0702040b010207030c050105070501020f0a05070203 89
    0x3c014401044001c2c041280243c8040c0251903818408881e0000d031703485414002045142c075081110f00c00c201d100c2d039450291a001c0812030542c1c4407424507a0007601e6110f02944001020301d84189103009000300032034125009818080088006406449202c1d1414108803801c2c000900b04042d02003550003550f0040e000907101442c03854101d50b6540503010640c0803030700350300f400e081e80e28000500301c04081c0d0100030411144c50382e0f640c0101078910707543e514010000901c140c2c01080240300086000b003813502d004000302032410001504102840d00442460790600f1001d0000d80c8001038080b00744040c0003108099566103050800040a034000701104960000601c0c2406250b418082c060060088408002c2102c5030b0700103a03a08c2225103c020503158855100f0020341d0f0091001e44411801100094034101d0034140d2200c1701d602c884015000300c0c0000c910752003981020489 = true := by decide +kernel

theorem cover : BRFrame.Cov 3057561 3237417 := by
  have h0 := BRFrame.cov_init 3057561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 3057561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 3057561 ≤ n) (h2 : n < 3237417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
