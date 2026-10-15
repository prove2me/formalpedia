-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5457
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:33.140593+00:00
-- url     : https://prove2.me/submissions/201027d2-9af2-4093-90ae-dfddc66abcc1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 981294964 ≤ n < 981474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 981296214 1250 981294964 981295001
    0x15090f030f090b0435070e090d030203010e010e04030203040f06020d03050108060702100f09020301091b090b130b0a030203120d050c030609061e03060c0d0e011509020a0c06 76
    0x549541d00501c9100988540c00c5000d0515040c501190801d1351040405d044804151400341644d2040c480c000303007200040380442d4a820f4440190070803900081d42c407180e20340702d50224031090038080e00030b0328140d03005181c45030221ba18001560b060070794041c2054065020070003011451390355200d41840580701d036800911140800100085c1120016408000b454100000703200000d82e01141740b0709a0402540c01003162a0320890070340c018000c42200941c15881c20780460101700c090007008035280310a0180458480e901c44c081c0c0150b5035149180380c0c0c00034041c041c21320010581d41c40341c2c1e100304018145071400c0351641d0200c2e00e09100318003500009013000c90300c40e805000d68068280e20042421400d400c6051140216038a04d002410ba41d10600741c0e9280070b55a0a00c580003428803603401411260203090120704148141e000c82c5007212124240400f94024032014003990012076045984080107515000c10b01c8002d42100c0c0501d8100042d020564003c0360490164040c5c00e80104641d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 981297464 1250 981296214 981296237
    0x703140d111801030603031b080423030f010203070e151902160803090a0302010e031f0b010809010c080c0c03040e041401360809031606030e031615090f03 68
    0x21a40910003908071410917040c14810300c0002da2001b01c0120f0b1071481c2c01e0b100b4001400f840c00c120b80d409950812802e84036824442a01d0000c001c107419198070701603050352030404003100d0040c00d0744405c0700d00703101082c0d550702c0703661090030b000040c2941c1010f01c0580a050640e0104480c00100300004900f00585c06078000f00492040040c0c00001089280c0c0110700e00b610007000700d1402ca500344006414059010f410b0701c001e840c00c1c01441802c00440441c54507425004904400408018050a0004a0400000d0090001441803498000964030f9000c460b544801c000301c255401120300e11460f0005000018101c0000030340103014dd4030400070100c19652111000342119402006402c0504901040050100190707005010040456800c0c0d90b0103c0c203800c0840f100c0c4540c0e1085034251080300f024071898034030011118284e81c082e81d400c0c4001804000c0141c2d680c011507071002e044c603c24580100c002200030f0284403258002c0340020035900402e8880720b90205d4400401e501048a44802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 981298714 1250 981297464 981297487
    0x9080c0d230109030f05071106030a0e0a03050a030b040c0512040c08150f0c09060414030106050d06091202010c0e041a03030301030c030b0c0315090411090a020a020609030f0703140d11 81
    0xd11a420111b8a8030700c1c10210300d5102d2482441d00000040c0c01100c000001c202c1201507a0420f04516440b40111200c800301403800400030341c08200424006890081100100d01c2c0a001d910100070182c0d03655402c005803103480540820018200b25200c900c1071000054a0f00103000c40d1042c0241d8881e9020107160984000400110040055400100030456075440381d681e94117032026a8a07000a0f00e602450b030718046401006a508000da009005006003030400c0b44c00c0e0402e40c0ca03244a4181c00d004600640e40136402e03506007107400008100c14003103104e0b103402c0c29030125034040a9204081170300080c40c0301080c00c6038401c2e0001d6491070001102881404003141406800203c0c81005a1462411240320b0507903d01241c0020302c00c0b15604c000c02d040c40320844140c520118024100101814000300c501e000b0b600190b443c00c00350003240b0004441c41c1e0080140c03401e0092088200345045019942100c07540c05800c16002c10f04405d018041d411100c610504000c402c00281503a55200720300301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 981299964 1250 981298714 981298727
    0x60114010216031a071101062408040203061f15050309071421102414130908160c0302120a050a0303020a0c02040e0d090609080c0d23010903 62
    0x1884100300a00d14410000201243d40b513000400c0c00041219141c0c4404608517643c1071403c85505540d1f00300354001c81c9640000840c00704180c0c1480c0040500140d04030152040a01200d000e503058014200144400580d810305580c554682c10311a4511034541c6102000c245142140e440005e41c080200711009038104181006060300f5140c416810b01c50304000f605611190083d40a030840b81c1440036070145003044400991000c3c0c4c001070050340d0720b150723007000350940c000c1d070092202429050014141e41c0414140025140c007500e45152408201c020038040c200003003003114041c1c8208031100701d001c59080c80c00c448a214030141c03200f0030300c0c41c010458400283c20140c501c44c2c01518588002030000215283c00236450305001d0780321240070f07d06a0f00480c10641c0a900141440e242a44116000c0b842c0f4402c0c0a40313032102919a600c030f11040f50200d5142c040c089541e4030010107500f0074500303440c20041c01c61281040000f02250500041403005002c101c040040c0c0d11112a5401c0640100303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 981301214 1250 981299964 981299983
    0x3070315121b030b041205160308160f14090a0509151f020303070c1e0b0406060b0a02150c04180b0109050f0a091505030f03030f1005090a0209120601140102 69
    0x901070302c09542103445a92500401400040889030040c1013807503543d01440554002000072010301044807100d04015100b050101c56504c686404825048036403401281e003904440d10981d591003200702020041d0309650b010050003a401000564006400e82d117128426200721200103c64401880300c400b0f01013225100c0c482802c548040c0754003040403d074004152944030300c2c1464201100701c1a130809003500001509084444914914032009205010040b94011442640200290750781c0324440314250003515508001600802e03242c0000200346254107410030307080102249000d90700c40d100c00c2d5100c2003400607410a034590044010540e0080480401030009030385028140d04c601002958001c2140034140f0440d0b543c40c2e119844404880c03180001e44030280c120b8140100d41480c503030b500c1c0c00495024010300d481100080d0b940322400c20260843d4030280440b151601c1d144d64040c040c2d040350a80307541120903e03010004054040242e20300800714500b40450b4802408002428040c100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 981302464 1250 981301214 981301253
    0xf05010302060a08060a0323150105093d0801050a05072309091003020a170706030f09051002090301200403030804020105120709050a060c03140307031512 68
    0x1001080940c0380c80e400c880e4044403601c0c002c8080d582d42000120700704160341025120300c501c030740d0742403141414000340980e224111080b40d81401c0c00b070310452689a424029a0303044006a808a1007901034440030361703400c060300c4d1105100c0d042a1a8102204003581c040c2e20980016108108808442885041e8201401030302c14403191a00c0803001d420000c000110442d0034241503051140c1110301010394400c008002c010f05450b00701000b5101d001e40e1940026071060003a504005115a40c03100366540b460002c00140445a01d130184c1980145043c0e9040000300340c6038a15980052414030000c009441040c80041c1c4a02c181000e25003116903400c04054171100300d240c0102140720349802d480883e5858901b900e0b442c1c2e13070f510040362180074043d5182000d42c640070034000d042e074000621000b50f900a035002d226640d076500c8111107a0794451005804940c80d410520707040d00d2a940115485442d50a0104415940c11020621340300ca55009403546413010300004c0c2041800c80000c403410a00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 981303714 1250 981302464 981302471
    0x1509083004021c0206030a23070f05030711060f0406060f0303050403021306051806130218040504170c0c1201060303080a0207110405010801090311161205032505010f 73
    0x1a000e1000da080c0c00680040e10554072160124440c254034408001800e43c05003685849040034811040a009001c0c3c0b0820303400040890040c1f15940c845004d40300c1c0d155076449060f20f108000081d209544050648020020000202c0c2403480c41000481d01440d84906940060303d0181480b804a4203582c11039088048408070410206e41d1060540b002d07660100c03080401405212013250050550381c0c0017036003004044141c0708548004000b02e0b8818241510121700303140f40c03244404100e2250301c98800c2d11484600300e02d240d5040036808075500c00d10900c80c140c00c0c1000181c034480148c020111040b569400040260240d041c58800c1c80e0b000301c440002400003608540e0064640b00f401041d09c6510766001c1410001e128030b00303a05080094020f00104200d5854003082400f9100504003a00800d1202007440c0e80b10100041e8844418076400a05030810b06040d16101944c4017032400790b42038071050181e00c00b6080440100c0c1e80d00c004100c9102c58400c4280750480c2034603000341015029528 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 981304964 1250 981303714 981303787
    0x15063106090501050c010b0d050a1a100b0c010f020d021b0a0b0106051602100903030e0f060307050c150702060402010f0908060c0f0d06140f090c070f150908 69
    0x401101250540b1000d007807258484081180c1d480c014860b42d9141da80c0100d82c445003006100003c1841d01c0301c58041c201c8252081d0080c0303580071143e842513400c0c00c0302aa210702d0403c0886103aa02509444001e000081000124107900c401030340c00070304036214402ea0008400882ca00140a0f403200030040c50050711070480562101d0306000340510a030000d0000000b1244500a19031440d0301c44164020801d181480c5406401080214140000c82c0880c91f802c003000c03c02e20385020440140c11009010720310f950b80742d44040f20160003800743c110091150707031483e00b2801d1380841c03001c6c4510709941c001d140030315090000510540d1003041c11014000c003400e062010500110350706a00c540503d158a030381c0c05a40004464034410042e0141c009481e0038004141440c4100e1240c4440c282243c00000040c040070811042d0340b025500504980d00030401400091013400001100d14010306201075800f46a0b000801038882403032084680541c0090000008541e104081c0002c1c5950100b00c4480030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 981306214 1250 981304964 981304967
    0xb2805060f04090215031e01091505010e0411030c0702090c030c0901080c0f07030f0f09080709091a0109050105271801020d0c050c0d020d020a080315063106 69
    0x518640325025607152100760007991150a680c160199214011070780e40d1512441f84025680d509113041c403c941e8030710002035140c215014907400d00143d40401d070b44882c680401510150000511943c0103600c0d40c800f43c0d1507100210141d0b00c290180d907844c82d61400c50b403041080000c2e00510307490b450301c424000d00c002c9410003016211141020f00384040c0c41e80782c0100c07440c094098481048418003000400d0010158403200ca00524045500e0b85403084020007001d860b00031072030282400d0741c5c1c007038002040401c0603174101c21407050007525085050128a4650210890245c0000c0c1013071fa110350042105040c1001103503442045000005100941140252000352015210541002480c01c81a46128080d4103e800100c2c201e0010070801c06014030180c4541c20002c222049402a036014000ca50700204a0381881a0554050003001482e95500d04e081e400c00b404e07150b01241031a0780f420680c0c4980c802080d1221640008028448841c07840e15400d0343d0011001100c9019041d0402416 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 981307464 1250 981306214 981306229
    0xc1407030327050d110301110405010c0624030b07020d17010e04060b03030d090c090221150d060b040e010603112205010e06030f0c1c0f0b280506 64
    0x1c0c0740c00c2c0e003107941d180c16210741e8071180862a04500e51010300c0b8a0450b00304a850308a60441e0782d8250000d21400c40003c418103080d0056100b6140425006900500040d030b144e809410318001c1c041c0d003101d00045110b2a0000d00b42c0f6a041140e1120500c01804516601040001194180c610b4886071480c507004c9040e00041041c840c68012401400101d010441e440c0c1000c3c0d0300340400350031691912100440c41001c4e0154000c1070352003150204020954000c140211400c05800202c0c01103070808109418a81002c000c09a81d5001200385038411540c0d00c48a200614501841020400d581c015003004100c0714410000e420603071404c13a0400004000b141c1c64040900200c603e1b408030481140d4800d0034010315042c0c200400c0c071300b07400070a40d0003185543e5400b03810f0940803564040b861500b0b040d07460740b8004034603600507160180300f40c0120901038100c2d622440742c0d14140110b0240e6892141d407030710a8400f1446884055051452620075417059400501c0c1c5400c184800d0810402003401c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 981308714 1250 981307464 981307487
    0x180203040507090f021b030a0f0512010608040f0b040804140f010f051602041e050c070c0b0a051207020708100c140306061911060123090a0e0d0c14070303 68
    0x2016113035000d82030328800c41d906a4440210043d03100b00ea402540812540781c0c1c1c032221465001c958001c10702107030f40380b00c3c500b65903800c5040b0142c490164204502600c000324000c00c11903881d40ca405180c000038030310445003400f80348600e69846d100c0381040e0490900b0295400224000c043c01f25150f40d0580e0301c070f03007070003040b490a007050365441c40b80d140303115105604c08001030742150500030f1908030401c60800c234014540504c1c208020544500551034010320484030080c02d810b011903c00c1c080134080c0d900604a204890400c2c5140c5500d490300c00040c640b00b11000009600001000c000e500b50901c0f241d4952010498104000541d00c0b1024041260b0385102c003040000120010b02c007a2079100407158080c1c4140000c24880c42c1040c4028540300341000912118014000002203000e4180c0c11541c1c5c25100034100260742d212107040c800c09150003000040250348900c0000322502040c4280c02c6a01d041d5550141c00c100242042c401c00640b11000701940c0d44002c0007000840d5000790b02c03011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 981309964 1250 981308714 981308729
    0x7050c0a150209060c1506011b3f080906091b0f2d04050c0304030f031418070f1a0d0608030424030c020c0f011b0606180203040507 58
    0x81e058404400c0240650300b00c00d5000003002a00f2061100c0020302864580000c0e00440340d81d5980340011550801081e00d8522040000c180103000a0003405540da0034180342545220b940312103076010134800304201401c1030fa0305a14907012400a41c0311140c9170344404228000e0004e4101070305041d0740c96850001d403111201c0884010302c491f0795441181c407510000200000d000c084200055540c280c0c501e0001e865590340034905501c03c1c00c1c02e0182c2881028000201030540e81d031603e0a480c10885401e0074070415540c3d65180b02650f0710b4540d01d500903c1440d60190500134190f082030700d461000d4010b0341c20a0080c40e410041003000746034581c8029001088291102545490702c00500807039003007203206000205012581010122a070411040d810000d0030383d101c0651402ea0803079100001c0080140c20583c0c4e424041d051412007401c0f11003040c5000d0401000014807200d9910440104460442e02c0302410001015012403400c1c40c01c0903001d0451541c18159940e640d184220f11540b40c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 981311214 1250 981309964 981309983
    0x1a03071502030408010507030501050108090d020a06110c0d050409180c210501060b09041a0915180901020705010b1504030609170c0703021e01090e09030c0d02030a020607050c0a 78
    0x451981c424800d0760000e1504100901482c04d1100001e00608000d00400e80010144400500c4240000691030040c40035a00544501e2402da1208006001000111188030500b0880d0f040d14190170400c03072103442541e980b42c46e1114203100d8502c1c1940c210510001401940d1002180402d400300c92120403034504031001000403011440352142c00b103250074045c4c0070354642100002e40031100c400424940c2001c503010004007106507098614480e01121542e00002e1440000d5019422a107190700150b4008203c00d54200601010105102080710000d500f650003280070000c1000034058450182da003201e154519a04810030b12100d4051444007810fa00c0e140c034001d00074071118103c0c201090708642101c9940c1ca0a455682c0d0707441c04c903031004030f02644000840c040d4903c1040e00c030044141c0142d446003000c40c601500a00d0b44203003d003100c055800104540b02240004005250403d0030640143d41c40b0804100c0c06401d00b0001800c850610008000c92448142c2c0800c0003008d65901207401d0f17 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 981312464 1250 981311214 981311249
    0x703051e1b1b0307170a0b0103030804050715020c0405101203021b18130303091703060a080105150d1118150103020a120c020f0d44150d06060501031a0307 68
    0x11352074094402d8000c7e01101032040084141680102d60511643c062011030300700c0d9079620f5843c1058242c502035200182c00c82c1608044a21b090340007940c00c081c030044000c42640c3c036103095507d001d0302150110090b900c1102030f24003000040000300c6c01c0d00780071508100c140c2500d0403600101d0000400c0e070910032480244110805000390f02444a131500500040c003c61500541c0000c194400d5424500c240080000041c1c6103805005051144001c3c44400b090500c0c40c0040c02080c2070842000c481805191101501c2c40e02c82010861a41500c04101c610754100342a49081c05a48031003240e041500404c03014084a4000c07090600c05034040c0ba00142580100c00128209041070502101034004c544540c04015400000418000c800024082c07100c0290f803091800000b00c02c9940c002580001111003540c4001c1030007039845890700d101c00c8041540b43c030008020040d4164100d4200b540d50a09000c0c950b4188600100f51000008000d11111b0300d07400242da8114500c1800a070800c04c01d0341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 981313714 1250 981312464 981312509
    0x28051f200703151437020c03030103031b020108040f1a010603020d0b03070f1502030c0303070315290c010f05190c050f0703051e1b1b0307 61
    0x18140304900c1a940400d4581c40e260b00c0403452000725540c56828804050b4003044d03102119130143e602400c0386110b41c0d041c3d6070501105524000c484c0c41000341d40300d402511018500041c0700f01c0c1c00c40409580d0700d40c1545406000120f41d00d00c12039513507400560900060340c0100c1529002030300310040c0030700c000c1c0528110b402030200d0ba008810301c09072b40f800002c030590190068042060b01301c03003c2c000f6103040c071709056564240e07100b0f80e42c010116803800c01c9440c401c1c11001441d100c43d44162490301803c80ca0343c0d450341d4402d0302d030720300040da44040c2e580f52001c00040700000382412800d4425815070315003001d039040c0300b01c0b00302140e90322002a0a1105030800d42c40030b4620074a000c07040c002403402d560f8944040c4501d030708844000d400c000d84441d52600c00e4045070b0000720f2501000d800d2011070f840885503900034409100b652000c031100140038402c400007404001c01c40ea2800f0b0b800301003117104141000190b1110a40c580780850740104244e070085001819100c4803640c0820051140c0c40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 981314964 1250 981313714 981313757
    0x60306150d06050411090a0b0903010221061906080601030b0a08070b0903010506090105101d0d0501020c0d0207080c060c07030c0b12130f0f1128051f 66
    0x324085000001810690003681c9401007021294101d508100c0038800c070350491240d00c5480c9015130302803400074080c0304610f1030034054000544064001030424100142e5105043c401541904100842034100401460f100029144001c07000783d400b240b140c076107480605108406003c5605040d25100d2100f07060f180d090303c60f0000c0500d203040702e9010380c5d10910346000d580035000743ea002c1e508110016406091440c2d08604891000e04a1100c042201c0310484000c260421425803044d41d021451416039074000d410080e0a00a500050381c480044032040d00e010500300c0c4403410354000703110801c80720f0381c082a60159080e0030340c0d407580d9484400e10001d08000c0c460704002e0691400802c003040061240001d00714600000240003915201c601061100140c1608010704418000c0c201c01d000460325140064482c1c03180007804c01201603d0006454903840d0030b5041c0350860034009884c1c2031522080340000405095822030180098144800c01000002101d4001c1c81464260442010a03480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 981316214 1250 981314964 981314989
    0x9090c090d0516050a0e1012050a240e210a0201240e070c2003010f14060418081b070312090e0a022d0c010905010507021c050405060306 60
    0x30640305850202d080201012911340209409031030b00b14800f148805000c2e40f901c1c0104503401301c0d0f05000d40307007507814080d4043c4040216501c1c0920144600000c00c607a15501c5810000c140e4146146107080030300d82140c0c4412030440c0207078410071228101c00c50030741c0243c0100c822111341c15600e1007149401d0380076207a0810440300001030090000704a802410101e02580c00215541d00d090b00d1b0188119a113506170340010745001d944901a00e822440e001403030076003020140c00461840f0b01c9813241c00444103d444003800444605040002c0341c5000e200b8480906003106c02c13920154416101c058080c060000e0b004010317074040c048504408000c001f80c800840d03014514402c02003941200a180154a2040380481c8075802c001c41d910280c1030007620740030003484005001800030549800651400d0b42d80b003455003081003260f141500000e002d480903a82c080d030004900b40c200150000c0c505202c886c000c4024008400d10500701030b501c070341203504440040350070540f40c1d180d0b400040c2c3c1d00001d00b23 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 981317464 1250 981316214 981316223
    0x402010e0405061f05040e10063c03060302040203180c12060c070f140a06050a02030c1e131d09010b0901150512040303150b13030303020d0e030a020f0c0609090c090d 73
    0x82048100b02c24848040140c42103a070303c2040d41c040d044852500b516200700200b10b0038007805494504450b104501c10020800c3e0315005c56900e41d00ced0085400c030380c8162017514041240e1086014605030401504150040c180c0e098204010078611060300e4038406492000403d800058400c1800b20301c50b02041300380c0d0060034052889015007041c07540c4010b190012280a0705081c0010b0f140c5aa620a813441031400c09521442d14410307241040030b490142400401d0b0080034018200100c480c00039100142c0303040c072010f0b0104000c50080c1c5800d814010000e640c036a050030244982038030342200007411207842040501f521130140400703076014040d039580390700303c0310f0b409003040103055250b081081308201c1d400c1841082902e68030000d56522403d0780700700d041030482d801040000e21a41c001c0036000d101140001e80040800005803d40c0e0102c1d01500c01680508102d26485000b4010100800401c41c5e22034548420980420201034005241e50039000c1d0104440b00a6201c0c0c0c1c0551a01f80e030322 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 981318714 1250 981317464 981317489
    0x20414101e33020703120302071506090906060801020405061e1c05180a26040504021605160e0f06031f061503091a09150c030402010e0405061f0504 65
    0x29040c2048044085401d80d81568600c40402c5807418000314212055030340282803049041100d840a6000e0340c03140388100c42008115101c0c04145007c0c0c4100800f8182c034540203c0c40200c00d003807807810740383e158112072006d9104102c1007206130b403101e0807030300c9184002c080d002c500311030128a020342c2d02034680840c803260341c001c401480c0c21a181c0e001c01c0c800c1c00765401001510600242c0b0347d50354086c015000385244911707020304562801c0326561148038400d0000c4035141c0790700d9078081003d80e008181c00304240380317940012904010007444400c0c074038070500c00c0723150115103090300003031540c00041c001d90700d541d5040d804212940c9013441801942c074030300962a1448550b1038000d0005001c0743c42500c00e1404961180503106120b4010190150740242200300044402030340c008074424041e118104d1803180e240e000d41c1c900c41101296200380d00242c0381e591280340078000507064401035801d2602c01e902e0030007001041c0e510110120400540544d50b00300103000c1400c252028811034100c1c01d5481807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 981319964 1250 981318714 981318749
    0xb0306130e1203130b0a1404110d050f07080c0306130201080c090405040b010609080109031e051207080615091e060f0d020301090f021e09010909021204020414101e 72
    0x1c4070a11810b00605c85d00c0c00c8021581c440300c8860807201364400030364401003104007140105e8148107803031401010080445c02c1c0602070b0382e5070b1450510341c2c00d9100c2c0c264000c0141000000802c0c8401154078400f54088c100610302041c2540800c1c01c20711009040c403000102051b19109403405580c1c907a03401410070801403d00d0704002c0d0f94150b0034450400081c6d100704000c65103c1040c0541984075916841b0101c0b2814030411f204541a8842c0c00381080250a0040c0c010300780754003803140d01a80c400d840300d900c58140740741800b110903010160150307008003c01c288113450300d0341c80d038000b0700192284030800300d24201c2000603035521500800010005012980f4000c00c40c00d907000394103d407a6103108110007070203044944140d00907024100f041100b0751000959140038130005144c0400145010400c040d01c503404d0000b2600080460018181c8540c204230031810305108601c2d0f03950303640208440b54a000e10104400300c81d140256030319400381d441060111183d41400c0c0016000c9481450900003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 981321214 1250 981319964 981319981
    0x20301030f05070803041a090f15180306160503070c020415061b02180403030f0203130b13050705100e0406270e15090f0f06060a0b0306130e1203 64
    0x2801002520b0340c0c002d4001c0003c1401300041180c003100c4c104c03411501484950210a03805070020030700d041c0c02803101c488142155a4901d0442c0251416511490b11003400311840c0034a840003c2807a4000e60005050068807401d0040d010040d07040c1c3d02e4041d55a60b25010100c0714900c5000000f5001424590f442c1100b40c28103015405442d96603880301001c042081312a045c0707900d4648043d40100c030040e607000000d0b140e00815607101e0300a04001ca904a21500a80126442220f51842c0c00707071018442c1c030402016032040c3c2d401c030a0324041c0249141c001d40b58180c60380302c40d11030584564540b2b03100481950040300c0c4210b80c100014001c00145a94003070b826a446607040c03c003010028403000b0740205002038450703e03076040381d08401040c2c441c5188003100c0003900c0c064a40703c500e2040f244000e10300e4604105204c0c4203502c0c0300107468981010b105200415507203412401001d441442002681d0300c0714000d200d046c00340d62070301040c00c42104e1802c41c00d080078114011103000001081110302c3c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 981322464 1250 981321214 981321233
    0x30f0f06180601030c0608070203120f0f0a05041505061309080c1e03031902191e020d0806091315020315010915030b0f120c03060106030b15070302010b0402030103 72
    0x7000c14003816a1204004108540c4a401c01d0000400040e46100148202d512803c0f0035a400000f90048a10340b070040052101c0354072044032a00100c1310705804205000240001180d089081c00000384580d0a1581e1f03044a00144159080107035560b441c00030754656650340c207002d80c1c08a41c40c82080304203014200454a5031103003408900d08e200c0c4103007010107401c540c0c0442043c00203043c0590b0860711480504018140040310f000c800c1602408440180140d000300c40011301c901e07481c0c001e0301502210036441807414a881e00c0d81507411228050125640044005510100461300c52905542e0841501600480c01c40050503240d138081040074000981d9000394041c1d85030521485100780e95000440d8052800e001b81d9403000640b410300c0311402e00a400404903110014020b01014030780c240810200070040002c5500c66018a0b400206030409200c041d000d02400e20b800d214406601000c1010320304001c442456103403000410400f4035200798003096010381c5c0100301350740e03d50f0349040480c4407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 981323714 1250 981322464 981322471
    0x90213050f0f100809030f04120501200a080c07050312010f080105040c05040c020c060a0914040515090408160b1f0501081501050f03010f030c0b090105090f030f0f06 73
    0x1a0780c4030700c1c01d8516072415415900e55004010070b6802c01140280301103802031400f40032200c561200f40b00c40c1a9515484001c0c0000d02407070f800d094911a00c4e4103200e8251890494105145007400c50b00e40d00f600f80c3d00c02103803102449410079401d2034039241c030504000d105118014207030f800003050310341d0305042c0c9a52850403604040340e01d240c2192100c040301d080300c070161001001200e0300c1401f0841400e041d00584100c0d02039006a5128054032000b04660380e12080550000610388001409840082c00001d50030010030345c0c0420580c900842115004100020713401c1c07080d00301c01c0000c0c0c100100a400c49a00c001020040c0c5941d24207407600004a040a40c0c0040008140f500511203001d030500302175048650594541a103600c072a8410042c03428000354442c10000d0030805000b41003d400011402800594401c42e0704c140303181441062030100781c004a4580b2070130001c0c480700340e91040c15284910801c030b03640510080c3c2840040d10b0885c0d01410040c0310301600e400c4004504021034824030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 981324964 1250 981323714 981323719
    0xc0905090c2103071e0f0b090d03201e0f0a0e010203031e091005090309030c01050c150a06090e010507030501050109030201080c0f0f130807151d0a09021305 69
    0x601920a002c002038030002da8000b400558814400c90000c40c040115000641c5091080644000e150707417944409411409404d58048065000303100d0b840f4001c1111b512202402d150801180d009000f4041d50085640c201000c0d104000c2030401119650091880d19018011015666840161425081900f00c0040200070944060f02c1c161103500110480f44901c3c04e050350410300d400072407100490040f001c0c2210950340320f81e101400d1240064030406000308a500700641c1c64a045400701b52402e00004613030b5041090a0120001410700050300321080300c80c1d0903440030140c5d079040388a00184050b42c0408015801c1c03a01244001c001940064001c1907103681c180440d81e2600f0064520020b1071000900042d80b040000c0e0808000310060401160090181032a040e2405a064032580101801d00440741d030104040111441c1000004014040d50603950344500203144060306810021020000c82c1c403102e0004c40f01940c80c882e003c0c01a2035140c5045441380060030b14802610301300e025490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 981326214 1250 981324964 981324979
    0x60903070909110a050616140f0a020a090c0512070c0f0f150b0d0b0a06170303010602010e07120618060c181205060612120f180d17070c0905090c 64
    0x701e0f0307030402d2070729103060304c9000d40543c0c0b40c591603040d208054001083c050352560322a000300e640803c01400502c0000c0c00d00c030001d104c41b18660041001d155056400702060524112a03d941c05401000781c0321002070b42517034004d0301d40d944203080c2c1e04804140c20081440c03140411000410000b5108050043d0241502400c1100900e1502044454414900ba0300c08042540c0c1c000090001400c194480c2d000c0d1804501c2560310300c40c480301c0001c08404100e0f150004401403003400e50900c10b500c00003051700d00800d18280b07004c0c15805446070351300e0050a600d4407400c441400d210100081e55081d0307401007041208040000f40149001c526264090400290700c80000c1e00340d41403800070b00c0c0c00e86c110b0040e001c80c0e02c1b00401c01208801e640da814110b070041c01c401b03900e908148406000a01901d020066980c0070b1440000041030541c00e03c41d1060000440e548041480c01e00031100c201c504440a55440c00b076401c2400c0d0f01241580701642990615081006814011402c0f001c085011340c2e000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 981327464 1250 981326214 981326243
    0x12050f0f0a0903051e0d020d090b1311060705160609060e0111030f2a0a02090a1401230603011502010c0c03140a030e0607030518031c0b060903070909 66
    0x101d05542c188800a03002a10070301c146018190300002c800b409645407801c007032038661403901510036a00661301070900e0316a0f4107204002e20183d40c084a90201c41000b0a10894030566240ea00082402108a0045078003207101d4041240810854903c01c030707294180c08206959030002400c0040381d0088100003285c2075003522255004507118048103500784040c1d4107200e0b66450b2900650055a101c44e04021300c541a00b44074580451110305680300da5001e0b00c1070040c81d006028103500046c2603500403514041e9000d080f41010121681500e180002c50401280c1da11500140c204401500983c00300c0000000175844200d508480e1001145030024405200f1312442941c01d1502040c4c06000300342680c001070003a05500008084000860900090040c292030b0703000d15014080b1940b030040b0b40d0710b50911290f51540c070008094100800011742c80c21190040640c20486400b80f01c0c8180354581203aa40180d40e0441510f12088001d0100c50403983d03140041400303400c0c8172a050340c40c2c04452210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 981328714 1250 981327464 981327481
    0x4050105062701090902010201020f0d0c1d09060f01030f0c2105060a1206092a0f06050d022d030f090307020d1e14150109020c0c0d0312050f0f 63
    0x4400c6000340e02d59010b40703283e2030031240102410742e065040b41155420483d034100c4101610240100807507400000504030460100503000403054402d100f2410b0740c42651094655132407498551100040d144402d50429800040e4050001100807003849420018550b942640c49007801e4240f424010b05424800c8031491240101d64050322400d4110100302c3c0c080c0200c030034825100041d503119100000e000742c00c58454141c5005460901040c420329107460b044030f00080ca940501900703c0c800506030749450204090020f103e0110011001074010600c41e1a0349070500000c0440315405c03e80c628003102d2007100c0d07803403907104461a003038084001d00440c62185001003518005540503241b04001c0c0081e8581546030071080d8902089124400040400030b12101d0140400c000c852004018112040c40301c4100d15405170007205c090341c41480558804800001d5000c08820245d58800000c002810103d038880081007c04802508210501c1030b0482c00341c01c800d00c11541d103c0c04040c2900d400c41c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 981329964 1250 981328714 981328759
    0x110426120d140108061b0f030c0403020414010501051b0106080d02010903080f040c170f010c0224040b0408130308030c03012d03080f07051614010903150b040908030405010506 77
    0xc2c0f111310360300020003c2c020b00d00b070032a94880c0c50180041d180c281015080b00b041960300c100d60813440c1103404942001141010700a00e0100342100031350365000e604160008066019181c0d40ca880c10105100a4001000079440030019049080507600498210300c4060f0103000c09000480c00100c0c000b00180c3e03030441240e850f500803588038130000015407910042054145216141407903d0080481c0400301400910400d1690045900a813040c101c00002c0400074407151007120010340b00d003004000008004103d23542e0300a9010180a031202040d0840506000700303500020141c0d2000002c1c13008031081e07000618100c40d4501031001000d0799070805114411401003800e00380580f940c4062001404550140003891046400e207800c240e080d868042c603005445415000b00b41c41c5820a0121141d0014000806002802d050f12058916a100d650b04407070560050301c074941d10f1465002a0742c0d40d82022440c01c0e00500000e07101d0810b81400da00030075007902d115115074a415001402a03100702c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 981331214 1250 981329964 981329969
    0x3709050729030412030e0118030f0f0206062e090f0b070203061305010e030d0609050105121b030717010b040608010c0c02010315030203060717010504110426120d1401 73
    0x30329900b1500c07107a840c203583c0100140c11009043d1104144203001c1c50920814208040b1100d190b50381d90300a0901410244843e1481000c1000c04034100741030a4000607140d4102609403004411a402c84001c141950521401d602c007001c05009541c2e4034076405442c0c542a500710748840107034140c0d50803a8001b82d20495100039010380011001907400000658280c1e0000d005400200d9120790800d00c4078116880080d1b0055090f9681200340a019000c0c401c031805000d00b41c0c2c6d044854550342c4a6583d850603081640381e16100101740c5100300361002c1c003042004041d00760b0341d84582e800c3c444003140a89010802c05000703c3c0780200015002c40140590b0200c501035440b04801d04456400460141c0074460691400c00c0c942d070000001a2400c1180e244108256940d504d081021140c14560003907040c1d101038440c50030f02c1d55406013009150201c1d01200c46250903402d0b040f81d43c031603010741d0569007400c01419000d607003144001c440100c40103080282c030441041040044683d061a0340c1442030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 981332464 1250 981331214 981331289
    0x90f0f03070c1e0e060a090e030d0f061d070e150c10150b130305240c0301241206090605150c07062304141837090507 52
    0x2040f041100304000000c05400000282039111465110080e000c02d40396001040143ca520000381150342c0029441000c1d440d645800050155a14000744218201084105000080600808106150b01660358090710700b40241c4503121130449461130710425000383e11611010b001c1e442c0401001c007010312400c4801801e2806910040e030501c3c1230200c10340c2101050102c5c4008100380400032510400c5030342c102c400c0004440c0001503104c5154070104801800c1c540c03000c0400e1006220284c505000201c004502c8811170040c01e0150004a42400e015044001402d03c4d043c004074001010790814020740d4800c1e500ca0304550056882c0072000d201d100110402030300100c4017409500d01c11030048002074031001c4101c00c3c0c0c240100c41036503540c0c800d501c46280c5101044440c141414203042c2c070200c0c10740c42c1e88401d0300e40c41e00700d04ae0052241c1284441034007003411443e0f4402c00e48041c0b464a502e00014000700086095458241da6844660042d010000300e0144088456000c5e980c0c141105980c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 981333714 1250 981332464 981332519
    0x315033c032d120f060a0501080f241206071e1d150c0a060b061602011103130807140d200d0b04050105040210180608090f0f03070c 58
    0x2c0c026a1080d0100c00031445201000070090440c0801c048455240281c62044145605003084401c0029002c1c0740d90015040c031245408020450b0851056268000b01581d030024030704c5100b517461000314103846100c40d4820114501781c00a5040060540d100301299141c41030821850b080d144100c022031880031000a48100480304000c4020051094900700030f800c00510800890012903503800811009005074441c8000d44184061406103003003040c400d0396054507000c287c10120281514840e0042c1c14041100e0498280e040200202c6041100141c50410301d20b484d4101c2c1c17911780080b4400d107040180c104c40241302a2900c111032400c140e901c0200c440e19050b015001514012142e406a40c0c8244200c00c1040400c4c110324140c1d11480c03160000041e1813603e4070400c111a08403142d03020401c40e0520b0340d90700e12200c1d101a130f401c3d655a418155001e0361228030b0030303103020070000300c070161800340c1c046205a040d00000500301c0140b2a84941d0340f90341d1240071800f98008800503a800e0042c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 981334964 1250 981333714 981333757
    0x40e0a0f05090d12021204080d060905060a031b180204030b0c0a200c18070206130b010603240303030c02070602030c030a0806030c0a06020d0e0609060315033c03 71
    0x7a6145004c0030300d55120141c2450920704a40d1101802168180d0f100300d0001005e0710560340a1203184040d00b9103160411079818502c000c15018813150000802085155246540008600824030000c0030b800a4499103010700481982c040e4029110444888605502180c507010000043c3c0300310704001e035508840c4080c0c0060118070a030045040300c2c014003441103481c9550f02e96098460f0b43d80e042104008807030401c21030007803500078000d200311050b0418104a50014500380401c3d411a13005150200da10100b90001d58446c1b500804070285659604500204160701904290380c070410741c3d000d4801180d600c0d607090f0785034031460500b040c25410820103090118080d040303da070001070142c1216189112213002c0f68010910b42c216001503030100603002c80850703000e02e04d40d8030b0850541c0d4150030000c210707000c20440c2c04003810a25200c401200d445407507480801040340110781901004049461064000508000f1010409a00e15181d03008080801c000000c03900003400340105e4600005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 981336214 1250 981334964 981334967
    0x2191403030909040210091203051215031506011202130806060909071e0503030a0e0306070507021c0f020604060305061f1b020a15180f031205071106040e0a0f05090d 73
    0x7142c03100441480b42c003020104088c00310f41d40201920b03200b516410b54a40520058201c4140001d0054a001404100c442070940300402c01c191110001d022040d029101c05006951020000034094801340c4045058292040b04072040ca0840350008103940d22030710340c0000d11800d040201c1d45c60009034030401007041401c0126203070f5114440f00040c0f8204641d00c03180001c1c111303030050104000281c20780c04100d08515052155a42100180c2811880d04040350b0106000440b0b101c00742116411903140c20040c0a004000d03411070300c0d8001c218650b07860315040c010303004203015140d9034000c05152264a04080100760300340700606840d25080c81110104c0541448040d01c1641240c012045950005441d036000d112084030341102c0c1c541c2c0404081640006001e1600c0e40d019409401d8408420000305e08003011010701d84e0400c3c40c20969a08482c248240c449490308082c640040c0b0014000900b0b03210171700034600035204401305105000344264500300340d510542e20513480c2d0b00207910726554139 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 981337464 1250 981336214 981336229
    0xc1b04180807060902090703050601030624080c0d0207030903050705010c17070203011103130203151006050a090b120a05090a05030f0705190b0924040305070807021914030309090402 80
    0xb2441001c2c08034074030000b640400c034401070680350200400d8450080c00440c8d0b81502800c0c0c00b402d007035260f04a81151114822401e06500c00d924414000799101184941c4001d00031100750100c1320304150b58a14640c074004005002c03500c8150341601664001040c6584603210101180f60022000038440d9100d082400c40e6038000f400481c3d16669498070a4640c1481d00040c5100e0165042d224400241900500d4108804a07514a44a10001c010000c0c0703c03281c5e080c030301e050b07400c07a14110f916100c4003d001c2d203e41c9850b4212049200e0085420b072030350004025a14440d544601c401c0c000f43c4c0ba0140081d5a40c044107130000e01039082800441401e803c0c40024004175409102115003260021346100d101b042c46080540b00b41802038100000e800c401c120031395443e490550f80308940b441c5200a400345030005000102040400100c420512001e40c0c00c0c0d0705082c2c0c000313000006200f007120401c1100308043c410045806212406090189004000d4880110b4040c2000810b40e07142d07420448407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 981338714 1250 981337464 981337477
    0x2111030f0a020322050a060311031b21070306090209220b0a090e0c01020d0906080a060e090109020a051c23030c032205030a0308040302010608030c1b041808 69
    0x1148024000401807104d11802a104001d0300f03c1420030040c140002d0008140703180c2c01202c10706061070000346040d40c00d2403c4941c44494400030318070004401002e41410701c00e43c41500b031100044031400d004441d000d40d115001b02c1c0151001c1161a40d01c88600059018026142da0b20650f04012100103402c402d003450700280c041c02e000a444100240044d00c500000c1e006109100c0d6240c940c4001a1010000003040c82001d0006201c2800e07106c000812010542c010b240800044001140d01c0013034980200028100c210f01c83e105514182d0035040c02016010020f900c00c49401d030002a882c1085480109100c0040a4940030001e01e0344404a8159840b00030720051046001c0001450070244041d0603030312118406175030344042809400e00701c14040081140c40151414003044959000a1084003540c2e040c00c10040f1503560b41001d130700401e41548000c665010010320880560008280b55100b0b0302c1078090f6802e8004910188411501040c0051500d2441140703a140420b000f00c001e043c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 981339964 1250 981338714 981338717
    0x50d0e0306060f061209031b060f07090302130e1002040801050702160609050103050408090402210a0b100c020a05090117070b1e07110406091e090302060a0f0b030304032111030f0a 79
    0x1030648c074003a220b510303902d100b6404001d0b85c0040b002e008074200c44202c01900140b10f4600354004070300b55000254500000d80c0c0030150320341d840340a0310414100381f1640c9001650740d07a046455540d5900c1e054040c28007140c010f030041c010390310f60001180d240145001650240d5407004145800c01c8010740c0207150150040d108070500b4800032200d80e41c0c60008182034001c460020101100302500c484081201411075900607003041004c0c502d030703240d2070b90712240d540c1c640c5041d5503d03180c05d0010800c2e03480f00d5086070707030801e81003000480c003409000500740c10481c2d00d40864820998030b260707406080c05455000c4501d2840b0701484a20001c841000d442458064030041c1c0e160ba160f800003904907003480d031020b07214a440e50007040c19030121201100c54095110003d106007485950000c1d100c4400802504066230754260040104400d40d005908491020b012669100d44a0601c1c11140b00b41e2100c0c200e60320a5540724010a80c400d60900e204003103140010b42c24055600749150720f0390026140c160 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 981341214 1250 981339964 981339967
    0x36060a09050c12010c090801020a0206130807150e0c0405100506091f02100c0f02070302040203180307080c01180804050d060f1e0b0102070f051903050d0e0306060f06120903 76
    0x3140b641d1009011018285400d0000030316604010015140c0c003d654004083d5910511802e01c0d86500800c4265020384a070001c089050080e20709080da6004901300a8684c12020b007e000400401e48d10510030030a0700c5044480e140703440d4082009940003110f62841c40c00c8986400c0080d410508003416040b04000c000e480012400100b014009001100341401a84101c41d84140f40905108a01c9620000c2c50030450280b0b808001960703e10031031000034000ca500200190255a61500c6071488600360402e40382e452019080803103c0d504142e4001059503e403900080c002840c010f5500400799002d06080d080902d86020003d2100f44000700ba994244c030343e40304407000d00b09e0340300f10202c03064903458840d001641000c00c01c080b45c4451078032034155804860180070501c0c0804218046030021655500d4410309403500e050f13a0320080e030004007188102d4084601454102d400340d001c0c50f005400704c61040e0ba03000104150b13405200c00c501d800000400000b142c00c819405c00d0756003d1880b10071203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 981342464 1250 981341214 981341233
    0x7091d0604121e080721150509091f0f0f09050d08010b130918020901120b0705031501230a020106090b0f0f1002120336060a0905 57
    0x403424100216070448000c501400140c0b10b541d002420300c41e12103480c10248031081e80504000c0d060b0390029003c24288606240888040d980380300e0752050040c4021b00030b02034501983c1050705034092900801c0d12440d58a400070b47c07540c400141c4002a140c0100c18403c0b9034118445a01c010200d01050003031941d111160000082501d000390103007180700307000904d0707003071003c14005001e510181c00140c240c413000c0150000c4000c411540c4801d036481000001400c04845522410b4090301c640003d40200014000007440840802e060021601903130048100360744410040b5210300c42150041205a01e940c00c0c46a01e510030340120842403590140b22a48084d00440c2e14070b00c2c1c01820b85407006079102d40c414040b90f0628050038032621820313100c22102900c540001040c540c500c1d010ac500070310010301c4280300280300f00002e000901c0d008101c0e0307a0364280607504800031550540d9030305002c4080800c902601d40816150445001103002400d183d4440641400c0513001004003581c2c64402e04044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 981343714 1250 981342464 981342521
    0x3020f130c171e041209081515090708010b0c0a0b0c1b0109030203030106030e0a060e01050907093c050703020405040c05120a0c050705060c0d0e07061d13090f05011d0709 75
    0xc154a008200c160003251328000d401c201da2750789107180e03940c003502510052241031600a1551419107070391500107504c48400f00662407030214842400703070a44090105019001d412a0024404080c08165081846200304c8050742030350584100240181e10030001000290320070760011420080a80c1940d00e40a42d90715004113584401c24504051307556901403190245080201c0b00040c14045801d0020403000e21030110b500d0205c0880c842004410017140000d0f04c0c40c5c0c10340806845942c0700c10070150905603001002034105000c0c403070143d0720309038020300b40d2400f81c000d40f103041d4070705004030a06030380391b800c00c1d8007829903403100c882804014050040051410b1190f0b51003180e8501c000b0b1340b107100078650300058a840700e040c0d040e41d400c4200107104181e0300c1486600440600c1d115003a10a8002e408150355502c00d5540c0d05c1004c4c900300e113404c10802c4844070840e900c0d0203400240550800c1032080c407505d50b103a038840c3c07032079034405602006480705d19000822150040a14a010034095144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 981344964 1250 981343714 981343723
    0x2120910090801050a14010f05030322030b090f24040f050c0414090c09130303020c1c0f02010c020303010f17192d0c03020f130c171e04120908 63
    0x3c003401d005481c2c0c001c80f1106d003030a41d01d00b80104000d0341c68418091808020035164400c58061004014a84071401c8482100345101c50046500c81007901c00752802e0020700c1c1d100e40d86a801003071203014000d03810341c244284465610a03202074584910082d1251b90300c83c1c143d0303801030b84111818012110074034030590ba607202d03a00c21815005100d07441c13442c01820082c100705c800807400c0c0c0702e808068180180340c0c1c3c0d2800603644403079040c140141e5400c5420310643c039080c5000c01400012120404e56002183d00c100ba040c0400e05c140c00078014903144a00580e02c2c3c1c0400d02640742800725488082000c440102102d07810701110b80c00b42c8118445045a102d960a849403040d200340c02e2207000440a00b2840c60080026280c0300d00c00c43c28580d05680e45480156184006442030605400009181d81c030590f0b007003400b0348030041c01c010f410310b400800b0f0041030420120600d0000000c0016140804000c40f20910500c0140e250b1859a107d9640f078281807110f884020401801400c0030540307980420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 981346214 1250 981344964 981344971
    0x1817070e0a150e011a070c080d0c11030705131d06010303020d080901020a08060607032c0a0806040c0611030d020a0305040618050a02090a0b060d05010602060105010212091009080105 80
    0x180401d081c114aa640c00c80c442540d80702149100f1094010003085c07515035003001042c018251420b55507901414034103001c003001e4000350314500401442149441d0030161080311184151200003128a00008168844800703100f00b58010420445480302d1800300d911a42580000d119502e445d403580e0f440103450964260002c03400359003c40501c2d40f405400c6030540390320102050081d840c200c0d100b0380007005000050460b82c002c88010588004141c0541000d541c1480910900011103c0041c6d04003802c04480a00c07500900748500c02280820010800e284541e0f04000c040c1d45aa182050031145840410080001401f0504c16074140c46040c0c001801d9420169401103003506090034000100d9644070500d60000034641000d0000540104200c0840d0760100c3d8000c003990b55440e0340310060300c203180304c0c50790200c400504010400c500e075120505941c40d07a4201c4040742e0301d80005903995081d41410305090b0340180210240c5123410b00482c00101e00700c2c41d00b064407e56400381d1a0a481054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 981347464 1250 981346214 981346231
    0x3070807120b16140f090907030f0f0b36040614250e1302040e0906090a0f0f0503040b0708030a05070f050406050304020619020d020d1817070e 63
    0x511014040c400b4410065801080c15403004034114080d003000350012070000f5900f0710044011611642c41403204090f20111440030b450612240f402c3c85c0010001c02c80345074140003c40c41c0290411410655105104848101602d5516a04424090740550f81c02425107105070600c4511002641c284440c21280a40c2c40b407440415004409051541426001026200c07c440081b0644121032010742d440c0480c446c1508100b52016040004102511039009440c2426400004c00046030500c004806124107100c80a84149440b0381044580f26035040102502d0440ea0f84031540100d403103160584001c038843c6003220710307150b500c00c410b600c15040300e031043d0f81a100100c10842c02641d00d004250380080c40b440c004440d61000310004d0943d01550180c1030070000301000090464031254211a04c1d5807200c02c4c1c28055441141c0003c0da104208100308006004250072071407018020100604442884811061042c0c01d08800390a03a80548030201a181320742d440000b0520031515102d4092440c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 981348714 1250 981347464 981347489
    0xd06050a020d14040530032a070b100b071b120308040302011b02030f0a020a1b031209050a06030902030123072007090c0c06060e24010c1103070807 65
    0x80c02e100382440356400101d440300352100307070000b0a0304409100c2a082d440804205440b030320f0f043c0c3c101c223002d140100113140303440ea0080c104072000050300150410a100711606030071a9a84021140d0410302c911a01204800038041d40000407402c1404c00041a07418049005896554a1160b0018131501080d004030f0952000e00c0145982800b0310341841c005240220200c108100000f90b03039204240b902031a45002203501c1c50030070302c2440784803034158009218918500035030b8540c123070b003050501c0122014032240040c04421401003d0207011590020107000203d464100c0a4000d024100c80c1280e15541e9988041d01c00240407401d83e12804441040003240e1800342c03000707400440200c03486410007004103003200c9558000514a4140e426158002c02d02c0240c4450564803200782400007401c0501344030022949082c40e20302c60340306100c040304818045601c681c0020400b103107007083c0e0740011510065a0045045c0c1015020b450f40060200d602240c0da401c5e4050402450380c001015003d003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 981349964 1250 981348714 981348721
    0x30319110f0721051b010e280c150f08010612020327011d0a2607080a0e0a14010c021509041802040b04050121050307170309010e0c0d06050a020d14 65
    0xc0d01c1d400c17440c103080210b00801c041c4800c1004596598228806401d041c2d51501040c400c115548005a2980d035119030b904400903110300b005000b40c51000c80500001e84002d580410043c458030001e0304aa06c0340e298441d080c044200d066010f94070050040787c000346c18526000d00408030008080070f0780450000040d0070940b54150040c0c404110302140310a0740a981032101040d02078280100390182c0d00c02d2842c69100c83d008192442c01030f008041c1030f800e004214030b8511500a010b81203d48000c507441482541c030f41046a180d402501201800540303a103401c000181800410031100410aa840c1410505c1c102c00060aa4a6900100400504181e40801141001d000e840d000507021101480990b051460f80b0340c810102c0c40044c01d80ca21220500024000140308480d801c6400c801d0f51000b541924240d0869a40142c5041c8055032800114071003044c40850450381c440750060800c1145001034403448007030140030b0842c522890b420081502c4141052041c4019501c0d0004015060316 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 981351214 1250 981349964 981349987
    0x21606020c0f090106320c0d030509120a180513020409150819080909010e010314070303050307030b040e06041209090603110603070c050609030319110f072105 70
    0x50404080c0034020f01c0707005000d100e070030000705400c9510310740043c6050303405030341501c00c09030456484e0440403000003074080f41c00c0c1011406401502c41910180301e60380350941e03032075600c0c5215002451120310a04c082c10209d840703401c1c1c8100030b68240d100c460880b5202c03c0010380c06004012001002076000404108000f2a4090031036038000b0769407a60b901516050342543c94502d0741c100714080108a543d000d0400056000741d802805018003030f6610366231144c048a19651003030201361010a44035880c03003510080090840c045c0d0394161348150071501c0c0e84c10150050f26111460960040d01e0320400500000c040144510a500611014260b001c40c8003002d00a0b0805400c550b0780c40d41405828008204010101351681d801036440c240d032549c81c5031003100c00014901d4020424014101407054280300040a14045c02035030501050351141811100225032000800d040290300c01e00c002003048810901504503680034602c0403080301030301034400350765010001441010800c0850b0000111 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 981352464 1250 981351214 981351229
    0x110307020d14100f060530030d020c0106051503240f03030f0d06051503150a03050d0e0319030819150906090c03020306030c0915060711040b0d020d060507021606020c 73
    0x1c02060315a15000f1480c5c7d0132544810801d1000060303004014100c1451041041088a220884812045407034960f03c101850117000d692048511a40b0307081441d8009030718010480e40030b04415210300b903810407440144031140d001c045030183d100200f4141010740340c40a0000f089510707184030341103554840c03011a400c21544944c00c214018017503282c0131560b04007280112608040103c400002c143c000e00d0006201c0200c41c0c1004019000b48100303a40c00c580c0040e000058120110140c4440c40c0c00401c0d1900511403d00b00500040d04000c046406d10320808001c0c0d02400c6c40e0400820840c20b00c022028142b641076102510172951500c013000000031912841d4014400e504d0154614244240000d0707071004904105849042c0402c01b260120101c0b5100c40180078010b08002d80f80c09640c1000301c2c40500440c8414012401c007a01d00e01146003c91815841c20380c001d01c1c40e82068010386540b0010b000082001e4190300c9030000b61943c02c52017140302d400505031540280046036200050280d603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 981353714 1250 981352464 981352469
    0x1a160c0b0a0b040f2405030a1502090a060f03060b0c1b0301090b010e090607020120090a0e1504200307050c030705070f0302121c0f09031a16110307020d14100f06 71
    0x180252000140300076074000c2090700003079800035003403446489d2a191400080c4200100036074022041e00001824a4000014801e4104652401c21016580e0320200a40d44656950309003036421402107012860103540c001c5022580150000074030807007696407109014003c1e0012030a84140b40b0401008070810440a5809250b038070090001c05100340103404103d10301481d50300c01a002088095080c0c40d842d613000c00034031165946164900308120080181c1c011940b0341c0740a40e040c071072480782c0600e40c0640c1c440785207500180607195039503004017101c1c42d40054070301c5082400104900b10110b0010885080a424500c1519020a10f184100104844c41c41c0c030313a20380358019125541d084503164072130040007901403d01c248890352804045841e10600d0b08028005030081d1100c40f1640c00d02085640701e01214840c590907001c540d8810f80b1301034681d000f140c426078410400c030401414811040c44031144102d001080380706200500034105004e0241c0e01e10403a0341c44e21842070600290161000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 981354964 1250 981353714 981353771
    0x140c12071b021e0a03060b0a0909020607110d08040305030322200621160503010e0c0d1107050a03021b01020304260304031a160c0b0a0b040f 62
    0x20001c914116011050710100d806031041e0650440b5000300790702440044a0301d02e0003810403492684900d0403900030403280c0001c60145401080c0403803a8811489002c4241e86c000f400581019070b0b07591000c0164204400c081c1e003140d0041d00c01800202020080c1c00a14850009075441e80f41058104565403008684c03400079200401071800400d10315200a03407010444000a035014154202082440c0720b01d0301c1c100210040340c1e040b401c1102540041a01420040c0c1043c640350b4a2044101c40c203020a0280015001900003c84d840a03030b510300a00c8038080c40e80300401d801056010300381544d00030380001d0b5038035003000400400301a8140204100006170300c0780e01c900701401000003940d034040c5010f820f80408040040071807920192041c04038605286080701d548035103900d0442c45140c18280405a4241d612004c113083755550015070225108607903e42c404440705440300b501c80d18028103048000d036502c92151540d0f0316076010b4600c5960a260020500c40c0d142c00700c07030030000f1a202410f907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 981356214 1250 981354964 981354977
    0xb1c03120b0d02010c02040e0f0a110402030906072604080904050c0301080309130617030406120216230d0c0506010902120c031b040f03031b0c120501140c1207 70
    0x986039440e4404160203030f4080c070f40440c0c072000c2c0d07101040041240311110039152080d100800d07910880000c48403805841041440c150454140c03d010580c0025655403485401039400140070034801d0385040c51180691102c4001201102c508102041e803d4805864840d8000b4201c440780c02c05002d465000113101d000b4628540c0352000c3d4903268012291864803808030828981850119500a44040d001d0700501810600c40707480b51030b603640d2061080e00d0214181d09100340c0c0c0254944240c561401c0101103041c00740c0080ea840013080c0040184081c012090b649101403540030030000036540ea4095251a15560114208503261680580c011036119004120b0f00004031246c488407500404007002d03464403510f85064120350500115206000c00e240410005045849881d44000f00c9000e030700c0746180c5080030b101c112402c2042d8000605007009140041000c500303000e840c1c80f031541c007030740c00080d6041505900d085410410b03034203e41003103400720350038600c10007401ca002c0c0c105036942400ba = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 981357464 1250 981356214 981356231
    0x71e020a0804090b060904021b061006170613050a020c16030807020603040c080102070303091101230319020301080109050d02030a0822080c070f120201140d0b1c0312 73
    0x101c010b40b16a00615030303c2511203119401035190f1030107440c0a08001041992240001c1004201c0840c64031981c5465124000215910060f41c0d0f00340f01c140d41031643c0c0ca99002d0215074011030060400741c00160410412030b101c061100540c03052500503a104440580e603101608a17481ca007192010703030f0803c1c581a81d001080054101001c6030003a56050b168182c6030341d6542091101804168001000c0b94000202001050f61682c00011880d228030400e60300c0500d00001120741e1400c41c0560000c0104070715a160700800d01c200a1640800842c21000050000700e03040c03816a002a03110280740c0c1e4680c1d8940c41000018412040c1100580c1300450a03c2c000320310040050324060b040302140c2140c01540ca0404100c243c01710b01050f0460b8100303540d0744550090035900c103041d03c1038454800940304082504401d040380c3e00d6203030790160344011818111101e90f60440d48840681d2240c01e60301d110704074040d11060a40e2140a00b01a112051b100590070040c280750b06403840021013a1411085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 981358714 1250 981357464 981357473
    0xc03031018020a0e0409020a0e13061514040e1e0a020411030609150d0f030503090c0103052e0e04050d020f06040f0f051203010b04031e030905010f021203071e020a 72
    0x4c0a20703c8002ca1300810034142a00104501d004660080c210100d80681040411604440a590348500c1450100811200148440141c0c065402010300c80000003030a4001441c3c6900608a020b00550aa5101c0c079001075070080c1d83c0000d005231500c035030088208072040d864580300d00748403454010401459480c22500192114800410320004e9004042c0340c40c5840e150f89002001c003a5100d0720510800300c80303040150058104031049461445080c410341d981307502c60b024040c0900032100c002401030010a02c0e010b043c0c43c40079401e120110701088000707901c181c4000f00c0e500841c001c2c000341914841122000741003403850000c00400342c3c009001d001c006a415180d180d140d80d0403d0203d52160303c1850302da401c00c1d0b1822510a150030300800080707001407912005204a030b205140803c030800c0b0607190303000708940c40100900840d2232070350100030950003040420f00034101403040e070303c45044121883e4040c1c2c105039000000280c11005500c2401c541ea403500e500d220040c0001c0041010580c1c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 981359964 1250 981358714 981358727
    0x1109070903170c1c0c052b030b090118020f0d0212010f1203111f020a170c030c0309101a01090806190e010b0307080d02060c19030c050c03031018020a 66
    0x8001013402070012a9071280380b1503148000b0702c90f406801c0d80d10360510444040c1c240100c00403201c085c900c00c1e980043c0614003074442c9062650000e0a0f1880a03881e189200202c0c5003a601042541c5808000c0038042c2c1d62441c00900341601e201900684480500380a110a90703030503080404004402c0d10300f0701103800700300c80080072507905280841d052040070403110300f0541728000e251486084003035a40c0407141c941d0081c11070302d24140c0c4c13202400c000b890207030103030700d41c0c192440e5001c6074003080441c0d0200050401198020302c00c0c800c440c00444100d003114201c408074000301003d040301c803144c81d80315039000100400608507040180200e00740000042c0001c8091403804004958840038080d4504082d04406151407004080e80c14095464140301d840b01e00641042c00140554400075403c0403200055544002800707140f5075a180c004501540200401c151000c10f0210030310562000034800c000075032003114040c0c014550341d85040c03e113503c0c14102c0d201011360180107005050b20f480d404007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 981361214 1250 981359964 981359983
    0x512060a0608240a020d14010302010f1701051509060706020d060902070210080a0e070305010f0f0c0207030f032a1211191401022b06061b1109070903170c 68
    0x10b83c00d00781d900c521000314000d204104e84509998101403c0301144803900064030304aa000782c070303060413111106004035413084e4020602c418280c0c41c6c1c0e0040c400d50400300403500c0c4480b2002c1405150040000002c3e940303402c600303000c413841038000034501c49040c62401802c0081401d10b400b9400c080859001618540c4500d003850100402d04000401c080340d0f80d0004445041c00c41d080e0b803003203520303820503c0c060050140311049041c02c011081411104600c1034016840d441d40c080c10f0158116a5100310240c846402607003005240c11050078100529400600700000007400c4101d0840945061072004001c40c0d41117040c4078182910900048003c101039030f07030700f5800740300003c0c80c0c803e0f2501c18052001c440c0307052001e42c80450440c4081641c0e0b01030089803406007034001d0b1740450845008094501c180209030010380340040b850412444400c1440145200304542c6c005403a40c9004502071003011203152001500b084805c000380840c4074800c0310451484903020380b82041e2003101030342c2c07440e0301d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 981362464 1250 981361214 981361273
    0x1e0503280f12110705032407030222030506090a020a1403100221010f050109030b0604020c0a030509150301030b041403120114010f02030c0d12060512060a0608 70
    0x80d203103403040201c1451070300701190384240b02881400344403000500010104500c10744622822002180518000075007000b060b411241c1d0030700034480d0440032800403001621003030503d40c081c400380103241074000c0780428280c04030104052007441d50401031316101c3c010b07190444c16000301e8182000340c2c60310149041074804031036030b8014225815002c0307441d1001c0107116040e964404980188907181034a94217210680d11100f2000390707600c40c410b10030500070f00d201d81b40c0450b000c0802007000810000710310b6030200c802031005050000c044002c41c10700e840607a0440001e503000401e00810300c0c02d103412600070b0305030f0300794142598150b079034040301c070b00002c1c20161000080c44242d0a10110400858140c0301c0400740051495a64400c07110850a00c440202d011070140384080c14010320000c01d544042680e00c0040c0f450701c0e5807407000e07030300c841c040d400707011159440340004a40f0380c46500c10714400a8004008024a00d0312024000172200c07282c0018507170340c100d41813642c8a11004a000c64100c50b08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 981363714 1250 981362464 981362533
    0x2150f0d0e210a02102007081b1903030b0a080a0b01061218080705070f080a05010b09060f0409151d0706050f0708030c040306050106030c0f050901091403010e06011e0503 75
    0x7540b0708001c18421b03600f4103424000f00050108204544c08026000d06402443c0c071005220440304003d80f1400c8000d0029100c188901c413000109210b5000303200e2003000603150060760390b03c440406007407100150301075400d8150310004204035a80886001c0c100e05450200b00310520008050b5018110b071510f001e054080701080b09414401e0a11240d4000e01e44103102030f5807256501d040c4d680b01c406140c4282c3d1254602a403014075402c003142028071902d0006c003003101404408042000500c10b1030b00a1355008007520303142404141c0ca205030546611403444a1480141c124010382c034000480e048582000b006108041c140e821080a81d03000036440060962640d03940c0c110f0003864082c41d071003e004142002c2c00054080e40603884518090200d5680001c0c0d00e0f60241c003540c452142556183c0010800c030410440d805890400da20031801c01400030400034045100c4900d42582a000114003441c503926801e05c81401c1900c0c1d10040c481613001c1e00755100d0001031100301c03503140345800c00500c08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 981364964 1250 981363714 981363731
    0x15030c040c210213121b1212020111030a14060f06031b092215030209060f030a02040212070f03060e060907020f0109051f060302150f0d0e210a0210 65
    0x142c0e41c042d074a60a00d21404601c116940e42540403d8084c000000c0d1035424040194407000000b0b21291026101200c4d501003040c5030940d03921a014015064000c01c42d5a038070101000401403900940c060207000c00c0c08922942000340c50000341501806c079030302c03400301d0007580c405035120181904e0b88000040c00f0a02001070f444001000c034850814416400040c1044400b1550a454465001d040c40c00c20100301d0541c1000a10103102c006001c0039501510340400940c440ca000080041c0300b142c05010b84021107603030b03030101d016030f0402c541e0060600c94403410040125403099400c2900e40f0749142c2030018500d8101c16410800d80685580c0c098141400011400e500801100d40f951411100822070b030a240d042c40ea880d100b0001d04d4034081d81581016604041c1c1c036000e42400d4a13001020100c05500d0000a140e056015080c5034600e100c040c044011800b00601c074100700e10341c10a000e424051000d03000c80b400c1100e81e00050060a200b4010b170f02c8000d50005440170926a603441c001000c14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 981366214 1250 981364964 981365027
    0x50102031603110f10050414190b061c080903010b030d05090d0201050903030706050f10030201080c1e0c03040305010f2309120a110d020105071209020f0915030c040c 73
    0x8002e14201e412178401c202481c1e41e4421241e200a1083c3e0180340e00310300d8003d02844442d00c4881940c14011401c0c84902e1940201d401802d041c1d800c094010f00d41c400440031207010300c8002c12285010348190b500800d0116884c1802c1c0584141d96500301c01601c121540300a0107829801840d12140c045d40e058007042c0c0443e4018000c403540c0c0d440c02000c0742c1d12002180b800c24064041152480304032448003011900c0e9094400c11441070303980c16101c03440542e45e01000409070f40c0150603a03420611300300305c5890445210350010031410305810050341c0d581c2d040d4100306095550600341260800e2401ca089060301180199140c107000d0081c0e01c84a658580c80005442d002202c901e02e522503e002401e488403036040300c184190303140f900094590b007041901041e0300b01e480c11607082000ca00902e24842c180d9071240c0c0082181403009040350403003200f100c0401c0b800c090071691401040041d9503889150328080020740b2181d14121403d00c0360481403840141840c40104004904015070a0302030a03a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 981367464 1250 981366214 981366223
    0xb030408040b0711150f0409020c0c04060e0708060603151e03071d1303020d05070c09020d0501032a0911270a060908060105100216031b05010203160311 67
    0x41044180443e110780d01c1d800d00c40c0c0da480560303024070301c40c1e2115141e8240d150b11140036200c521b403240c0102c80c2000c2c5000c450b900a5031110b45140c020340180c001c0590181d99178031408000c3c08071001801424a84071030b01400000c800b5001620a030b20500c02c01180740d91a44080c19000815a014503107980d00e00007003c005444448015890b0040c0c1ca0042940c01c903054021109014600400e0400c1d05c8242104050000323801028005820020104900c24041d40c020500c0911484c0c40c0752405640304021030407a0000814a074245448200400901041c0480c0301c1c200210480304a0380343c1e8407205240c00c110018418003501c0d81c1c59444032404181c0c43c800b81c0c3d04a0050b0009644280081882e0002095054244600c102d80c0710a01181036441180981d003034a5102c00204056401c0c1010080c1c01313041e02000307104501c02c0320960001f40c00d104200e0801540704098284800810481105d1061300b140c000a0442d882071180f0501c104480ca400350030b035601801c0000a0051032001c56041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 981368714 1250 981367464 981367469
    0x6080f0a0b0c032418191406060a0804050a0b0403121b02060f07031103161106010f14130f0614010e06040e040f0b190c0804051c0e10021f0903090b03040804 69
    0x11060107004000b10004101d0070644d8500d4021003c0041c0c00b480b40c46210302040a40c8c4a03608041d0520112054a024510050300140100d044650040b400d0f07651405000045030201e0002d00f04d0340902000304007500501d8491b000300315010764000c2c07085800035696a001840141d03024a60004a00c52074000d60000c1c10151101010a5803454260044007203185010b85c0031000410f0103241000b02040440e042c0e050303a5025006100c001d2800019002501040661640c480c03001c501002c48189984100b040080c9100d2010130018034007842c0b0140c141e00c2500403030500001045008056039900304031003e41c0c4550200540365141d908002e00c401c800030744003c2404807004203100722549064603003001c4201c9408240161042d101c4115060482507030001c0030b0350700142c130140300b140140854811100312440c01034031010342e1000049030906a03403c0c4c40003603041460710861402201518421000903503c0078400000241c0d40100003503002e20a1041840e000720200d4204075849088600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 981369964 1250 981368714 981368749
    0x1b090a0306060305060106050405180601021606081017030418110715110f0a05030402180c0702010216151b0c030c0e0603060708160306080f0a0b0c0324 67
    0x4580d8503071405a0051507240016241407203102c0001a00e02d1041045500b039800103003a02c1c500c090740510000c0140030240125040d4001c0e00e040b00070301041403141000803e0b841d501c084c802c1c24506034070801c2c00d501e5088909a10003c41d580b00d0f5800c1c00204940454020302c40186003e68070300d005000510720b007000000c21020004a000c140200fa0801256440c881e850401c031031051519000c030f50b4810100c04980c0d055084c080782040602900241d544940098004015043d500380306004c030207000ca44824040c200032403190f065503810000058851071503408507c9a40c00e040341d8010717841580a0400404c000302d412400f01018450f44501584da00032000005070380c85e46043c5114600d1401810a500c0350400003584502d0009402c5000e1005a160401aa241c103004020505100401141415240c0f02e000030480c0040014040e203503076480c080e00401000d490600014640940344030803001b400c0c002d0181d4462940ca206545000800350240029147d602083c00044501c01500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 981371214 1250 981369964 981369979
    0x90102040b030a06090e062716260c0102070302060a11011401090b040e0c0d030504030c0e1b0a08040b130c030614090a12031d1905120f0306040504030e030d051306090b031b09 77
    0x281068a40e1040e80c40308900424ad01802c030182c0451543c50315205c0805005900012080025090060044c036100202c3d2804402c2402a69205400c0d615040043c000e8020a00010803240c06103106040c400c4008503014819129440000c03545e9280c1c031110f551203031400260000800d03000b1011100215804120184441d070794041c0c0e03242c004811100c407248400c00c2c0d84008207000342042110002c0301251034100c21358546480d40e40382010002c154040f5030102c0d02c030050108082c42d824000441c8680e0000c240c8a5914004030402c000c0601990415440f100040c0c000803008541c0320300800c0c8514001403c4145030b21914001890400e03401c811b0f006030a124032143c4032070249074a0300f070700130f0045654000c1c20001034a04d80c8103610322010007040c20b2010896070b02e413036002150414081c1ca080042d403001240040e007002205110345020441c000b640107808041020580c00405007810400344142c40d1014505076440020040c00e02c0704be1407007454003c1440310044c0d4410352070151020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 981372464 1250 981371214 981371219
    0x4031a13051005010e01050603011809021c0506190501050d0303091a0903130f0b0d020903070312050301180635030a11160f0e090102040b030a06090e062716 69
    0x207003c03c1c0070716401030300100b00100d80c0f41032220851b03048549090b6402942040c050480e0010303e1501012644000904c00e5010311009200704180c4040c081c2000e0081d5007081110f03400030112141e450030400d424600100100c7da540100c02d80800e4142c11b0204581c080b03803034240301d080c640d4011003812404880500c07032030820010103014100104609418a6501d83d0032840d4000398601c680261110100041403007201075402401080401904650381c043d101e03500c080704241042c10300c000184010004008004040e616a02006481081048204d04002d41c0100907504034800340e901c400c0740003801c045403100f5911200c1150044056940321401c80400500d940f892454603c003a225070040a194131004003010030131608040d58491289107800004841807000404980003954203000000b420848240218420100d004001480c0c2c2c0c02c00d10704008a540c450b0011490703078458420408030806452190024013081c41b0880650342c031441c4550724281e00c0300101c04c10251041c400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 981373714 1250 981372464 981372493
    0x24051219020310180504050619020712050a0215090d080c1b0c030f01140a0c090b0f070312151a0c01020c0102030901050916061d100909050c04031a1305 67
    0x440e00750341944c00b1401c2204440910030703054800a0343c0240554105e00040792101a211101c500c0410820b0300250908103982c541c08000e00030803010b040800c500059601c40c0715030620851b007141803035030150081c900708140c119a60b040000b409100b44040307140030840c580c050702e0a480d080308114004c041c01021044070b80381c80c0c41003441458028400d41800d03506000b0180540c3c0c180d43e04620000c695030b96400b8400d005440b035034000a0621071400781c0442c01440000007803803501491003d040c3d90f51300c0c07450300900112500351607401c5c0c1d529154000300c80d11000d14641c0205c0302c140402c2e440282d00c0760300c0e040300c500c107071318020081c2c0d1301c0002d410a0040040d0099407245d400c0c07d00812940e80c0b400303103864448640c0c0c4109000c2d600007103c18040603016071010b0001a044410505110003803602003000e003502140c480001c17482046042006051500030719900c50541d403440d500341071540d694102c2c0c031515200f814160807000000110744c00035800041d00c074650840220340800800090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 981374964 1250 981373714 981373741
    0x30b0910051f050304120309140a0302060c0309100f0b0409060906111e0d060e01030302150105042003040f02062106011e0318080310240512190203 65
    0x100c0c0d001d4441001014101d01c40c1c80301040312108540c4030f092660f5516603442800c0c56055010400385952424082c1c0810300e0440000000c6030800300800303600342e06040107403804030014074001101c0c0c0c003041000f04101c00801c070040b40700c00d5800c011503075020844c281c3c0e0140805400007074101e845d140708441072003c5504500c4e070a50043c0010084440802c0b203c8c0302031300c035502000d40c40e00c94810b01906805401c03002407500000446000504513103c02407007126090a910030340050740040c80605014807403050250041601300d40c20010066909003804070400501818040003d0100001e0144001e081d001c800b01036004018603030300c0c0440e01507400c82e18880501c0401c10301503100051a07550003200d4620511411045002e840c45840001300c01812210460302c0c51205e02c0c00300c070b40c00940e4083c0614080c1c1002207410401c83d0505007101e5011848682c0c48403050200b980f0054610f420108942100c0d180c000d950520b5a1582d41030400078161100c0c840c800d5200100300016801003e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 981376214 1250 981374964 981374969
    0x807031e0207031205010f0608040c092a081006030e0f0a08040806070f0e12010f0c080901110403020a140a1509140f0306010e1e090a05120a050a0f030b0910 69
    0x4869001c000302c00d051143c00c4075424010901f0015a0341f20902c8000d0081d42d0982e407280c441c60348040000d07101c1c103464003a1049102c101c0308001a03040c6000d8044000075003081404141e20b426061450086c140c0414903030796200311018541c2e1006000740194041c4440c01c26406008120786501106140c015184c3d803003446010343c180500c17004181410721410b8102100c0b6815943d152035a040d0310308002110001a01e010740641d6101444030350b80c07800e802186050711094480c80043d05e001c80c601401c0d05d10a0720742e55540c080070407080c001603665900a10555041018204030300082401080d00c40e0b9094120180300380b40060b4030701c1116880319207107080d10440c1a400c0c8403100c035081885452074118061591542184006108241003020515841060110805843c1d02c40b4210800010301c20340d80040641c11240d508814840708000100303868402c500402d10708032880344000c040c0d01a1011203002c0001050b0f10744012440703504848640d40300101040c1c020705000c600080c14520380e2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 981377464 1250 981376214 981376217
    0xd02071a010815280609050f190b1525050a050709020438070f05120a0507121e1d060a0e0103050c160c030302011404030903030807031e020703 63
    0x40104003c1880c105402405040000c0b0100c01d5000004410300691114240c00c1c0c0031540c4e14a00001c0300002405854041c80d0240b0032251103041c070313045869030401d40200003007409050010054140e10b4080444802210b030800c9940c41d62003003400b42d074074804507483d100001700e42502c400050050204900c59107070300c41d800319080076076514840b00030307801075119034210f5020035070114803076074044001c000d0803800d420300100724030901d0000c80c421034111810a81d0340c0022152032804102040100c901c81240b112001400c001c14140000e0240c812803c0c0140702a0380b003042c50b001c02340503d250019200540208020200d2b51000044c40701604501c1c00c483d604040d03080b1002410b20ac41115a020a181d480c80502c9075800010340103804041c140e00116102046425182e1114450ba1104d0610402500e80c00f186141002425520810384511034190500148800290441682c008483d41802c2840389130380e031824250001c1c0004032043c40d008400c4040400001c0041d4000c0500034840d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 981378714 1250 981377464 981377473
    0x80c0706030507051207090f1404050c0906041511060a1a1012021b010c090503100b031e01090f241e051f080604020f180a020d02071a0108 61
    0x21003804400780c4000755421008034200b007096005c41c0120030641c61b8040d0f05400c202100541c0c51380c900a80364110340c400061313014070702d040005514140c0201a00011801811424000d0180010780b052203644a1107030707203194881100c41114050700d5000e118000c1001074030510302d8240203034006004412403008203400d003010081c4c01440d0007603d41524055503520341816408180c1c010f0000d45c060105c030b0050140391101604005424050b401c0f9500301d9a649e01c995520785000d061800001c29a60903581c3d0629020b40050b0310001426040c000c4007082c01c15501d103040800e24018204081c0141420a160800d1801c0c00f90320181c3d000d40100520301c0760340d2800d00654410072155a506c24501c148030031501c10030100740c2074112a8000c100c0b4039010440050800d1411402145644940b800b6040b1100700401d62501e80404099482d080d60205d07000243c031000743c0700401c00148020419a400b00d02d80501c412140d059501403036210620480500352442d654199510074854079036030703118 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 981379964 1250 981378714 981378719
    0x3070b10060f080a0b0411030118060f030314030c09040e0c030706020f07050d141507021e030a270623070302060103150213090516020c010203091516080c07 69
    0x41012000c0b075101482d030320103840d41c8501601d20302808103005000d0b8041d844802c00240c00500c040110b00901240c0c2443c4036024000d40c142d03040e601c1c2d0f076000418024074601d081004c2034200a42c011401c00000c1c0050356542c4400c00440c140c01030300105a001403500b0f0f031880c4941c80c005a007410025085003143c1040d507640904903583e600c100460406508240340802007802c24151003180980f0840403005010381c1d00107030a140a90300080842050302660900802c0c80d01400603604001c40302480301000d02c10b1000503592403003252034203410440303000888040d002c19400c945101042c0c00c020092015602c3d5401010184140251100680011100000e40f41d5100894040c1075240c0c01800c0c1981ca0b54403241c0b4640b504000303002d20307203808020390400046d2906541c00074003084540042c050400d80780c54051682c2184290043d0b51101642d0a0280e80000a03101d01c02c00440d2945203c0c20792170401c80d8240241d4810712000000250340c0703000c101002c005009914104400c58081c941e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 981381214 1250 981379964 981379967
    0x1806060812090d0c0306051303091e0e07020a081605011401050a03030f12060303031407092301050c060703140c090a030303020705010e060103080408120903100b1203070b1006 77
    0x55489004401070030003007085080342d040418082c80c8190003452428100d41e40e070303190380d000d584044030030400c0354180d200c0000805800410603809882c50310520b441042a01040d00c00d24015400350503020700b021000074008130f100304514041c0c103511210351910740603280001c0b55880254407080711154244020000104100c020032412510010b20000c0340070702c0c5403010341e09524a81c07005400c020030200707a107480003070a02854000b1482030380c1c001412a1300004d808a140790140c41181005a10601044600b9400b9882c40b0f180a01180115009202000594940c0303d500005d41d494004e801c02c2025040d0590b001c090050500e0119007072599178111074079039a20584942d650f011040b00f00500109200354050f140c01407141c000003404032040e0500e289000001d038022112110005024030203413009110765070120001c0000e4604084108001949610b58100f0300c0c00740b1555000b0070101342e59010441c2c165890020240c90340c5000070306002c254100c04840905000b02080c40025205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 981382464 1250 981381214 981381223
    0x816050a1b1a0a0804080d06030b1b03190b010207233a020414091c1106060d020613080d0e0d020f04050417040b070c060206011a0c01060918060608 65
    0x1100c0303410701c0b500d0303e140941c1c00d03501c06502400035a96035030180044018250540700d0310002d58050f140450a510f007200808641c40c80c0d1510094030301c2401e10034041e030230b4600300c07160070b0101c080074021410045110040349460f960ba1301c85540c01c0410f01c01360045d00c41c440015558440305403009002e0840130049401d08826510300380ca4440b038071501c12400313a03007404c0f88100442e10080003c00d101c501ca000110404209440c4d880940c0c01c1001c450445116151070661001c07114108038017007107080303030800b5190040140240d005020040d203000465031210f049a242c20038a07100450311907143e01c03015540707210300c61411740840c2c0140c100307012510f054644200280e40c000d20312100145020140300181c007000d001103603541900243c0c0c0b0394144800340584054510002030a4070760b9601e060603410240541d104d041950455801407142c490180e50140361200100030096844200c905d12500410180e4041c0c0b01d5140340810780e401d03000d01c51040d180101e00829041c8080351301d605449455 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 981383714 1250 981382464 981382499
    0x608010302060d0c0216090c09061d061b06070f12061809050c041e05010e010e01051e0409031e0f0801140a090504030305180102090108040816050a1b 66
    0x11040c00e020f40500c2040c1074001c0324070480d95105030f0300c5041101245848010245d04408019501e40b82014400c03540191110014451850483c10554056052401c11039034003a041e4041e080004400070341201c803150144403207040d282101c2c00341c80c1c0980c0c018000d1400d128900001440e078840c4403010042401640281c1310030100107402228542041401450700c600304803034070b000703000414000f5683c038801d081c60048881d20000044001c070080004490058000d011110030b0b01006000a4180034800e605482e0251220fa5117030703180c0c1d9030325200203c400081e2580182031072804010075a110050401d102c4000341040844440c0d01420303207071600d10039045070000b200c482c0104080e11500c40b0042d00000041c0c00907c005440e4074446040e10412039003a070100340c07030f80180a090403103403001149012920000310300b80142200000c00741d40c1c0c041e1000d070407464041031406e0540c824003000001141c0c0300c03044842c00303502890400d07258901c000402008070892000055071520003061100b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 981384964 1250 981383714 981383719
    0x60a09030b15180c0322060501090f24050f0607050102040609090507110a0210030e0609010905120c0d030b1c0f03030b0319060504170304052a0607060e01020f070b0f010608010302 79
    0x3c540d1080044106c4000c10340ca82d0102031101c1d4020004540c161150a002c0c112020340826000e070704c420b0010994802580c0c02d01d200040e0103d00400520102c50030b0700380c410071503400010440f44c200203281c9008000020740f43e54400100001d0160700704115104941d1b685034140f010b0b540d0000242c6007144590709005050b0400351000d8010300d0b00c400d400e0107181c42c0d400c000030a01c0280781c00a00d810380488641200e030395102d09183c1880740800c6542c00c1c91503000d088520303061420000c15143d900358500c000605031221001c200903554074040404c650700742003032580d5140c100c2c00d11111108046c1d4060380071a241204008090401082003a045540b40c2c141603600b040564400380140001001600c2a24102c0783c3c049130114130b500158002d07800741008000f1040c0c0c212250b0a2280a008403150498116060060326148d002c161405650018400035a43c0a001c1d40c4070f001e4400e0401e406040500010810100240407485a0158500e201120030503a2901d105981d192020700001c1e6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 981386214 1250 981384964 981384967
    0x60c0f0a030507110a0b18060c0f07061803031a15250b070f030e151f1503090b0f0402030c060a111e0c030a020f060a09030b15180c 58
    0x5280c500a07046140c001101e46804020142d10240c04e500b07092510408940280b40e11044c040c00040e03242d1a07510505064028041505002d890444503200e10000007140c3c1001089001c148921680489a11009076103140c240f03446a140c010700501d043c1c04580c0307603021650010415401c044003c1d10344842c0c0001002c1c03074050b0702400400c0c5074070b56a00c18805984040aa0b80001e00300c0c400780c50241e5000d031030300001101803600240545020961210b4140d00100700355460580800c145600f12605030199800032110303160310840c4e0368268100841070b007000130382c0c288226855400200968081c6202400645514641d0f4545501c00d82d4045e42c144d0000c00d089000d8500b20005000140c00303818010000c4007180442c90038240c5150207002c000030650000f411601091081c0205c2c5001100604228502c50340010f0415501440a0740100004203200881c240038810200145820010382040d07443d1200d10120b0b2984c030410886d0150844044907071000000030400d0780106905007905 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 981387464 1250 981386214 981386227
    0xa0506010603150b04061709010c0c0b0601120e030a170105030a0201030209030f0106090b0a05090402180c041a0a090e150405130f05060a0e0309090c0c1f0509060c0f 73
    0x114050b103801c0c0442c41500c504aa000282c00040c035000f400103080310345035600103e41f00c00c08200d071804000c080003040e9040007000c1c07101940c00440349082c0c1c2e41c003254a011a40311000100d40741711225007001982443c00240714400c07075001000c0d00c2410643e50302c0c0004012600000c00d182e882c00e209158040d0701c18420400150b009402404200c10090102c585030300e456401d040c291850355000ca9000d640c1c6065910450070040d41c040c0c00340000791804c0d18141410b41c0490416620304090755141c2c07070298041a0f001205208a070700a02039080c584003524000d0f04050410b500c100c5078600414144040052103d4400c1c0d40a84510140c09007140d0320140c6c0d00520000d000000e0000c640c05040302086400141a0054036041501540091115113804e07440a0102c90000c0042c0e10580d2060008810994a6010142c0d00a0054224035100c6400c0b030102440c080340d01020000d0300d4000d0000e0908620641d01131481007031158212000d680721400104a14401c146a1000058040280 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 981388714 1250 981387464 981387467
    0x7060201060b0d110c0307200a0806070f11160f14010504090b18011806060305330303030c1210030c03060c0c08040b0408010e0105270c060a0801170a05060106 70
    0x8180c54245041480d1030302e40d0484509003180d000381c0080740c60b0b01003921900ba110001c00300081c48c4e800180e0b01c103407455042040c0560f4401d0000d00c1c041c200000c58503200c1d01e061244044945c4000c0360790031503c2c02c490f110070a1190424502460004000240001814040e00680d00f0343d07010043c1c45092038070b401c0003c084068145000003e070086c640303100c0d4429030210742c2c04444c0208038401240000501c024054000e4034220344c0464200f42c100f0090180461903030510a900f50001000f000c52038410101200300004100c42d0241c4c503002c040b040202c01e9030360800403d2074803403610f8141c900b681c0e20801c08000e00d4807400060310188031003a003440080d420b07a0090340a0b4a082c2020844602d1036aa1180e05610a41080c40442c0340483d003042480002d0040c0d180241c4003100902640c81d1035121a08070300304088090106043e5418600600c00013030080ba1144d880107440d150365200e000d040900400401c0c400c1d44a00c400c0b15158210036500491180c50181d44030000d010180d107000030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 981389964 1250 981388714 981388721
    0x20403200a03082b0606021c050405040b150301031a0109050412050d140c1909121b1a0406090e06180a0f020c150c07050a02060307030b09040c030507060201060b0d 72
    0x102010344c0d243c90340c030485005141e07600c41098001c2e507040216241d0b003454402418170243c50414000600c04409804503103401c0000e5030282c80b0242d400182240360400000c041141d41380443c4500c140001c004810302c2203080c0151607078250012803103071591340d404140045400444024010000360540051817030b110344010a40c1000c1410b010680384640590900c5050050318000c411450005415445020f981c00c0d441c1d0120941c100f4202c00703407824444100c5c05401c800018481e8507800154000b94222202c0705001d40998518240c08501207040030b0821b0303000c3d004000100f420b4040024141034a6078800388603240107000c605041100c44c0ca4100d54a0014084810154a440d81c2c6480d0040030303c0034088500ca41001071007001280131050141e160060603d0210400811030000070850008280900643c1035030390342c0c1c0d44d036140c00c0128000c001c41e51072641d201d040e10043c40140603484c00e4010649020302c0039200155540c1070140e080321814072610850100c00c0c42240e0085085030b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 981391214 1250 981389964 981389977
    0x9081c050a05121f080f03031f1d01050307090902060d05071b06091b061e03020d050c03070206090c100c020d020d050313051801030b072001020403200a0308 69
    0x902c0350420560301c100f2402500c08880000c00201e803240003001c504404244000106074a201a0030074404190000c1c2e100d21000b44000d401c1031041450040c2e101c0f40701800c038018490b001480c0c014414961842d00e4100d003e21480f44640b04524021030340c0081d51040d808080c5c5e004103003034902100e404111300034102c002c180c8020b0000000c10000c0e00e0b0301458481440c54460340c0300041340481440d010f280c401c1c2031083c120b94401604000d10106812903005110802800f01c041c250f2541644210007902c00c10103020302980c285401c0c0060b0000050166015101e95001d0740c6003076590f5074105584003001c66800350310102a418180d0454001c1016064181c00a0914011411b4540101d201500c41d030b4012600c0340d000241003005842040d80000203448215080716040030031094200340204103002c0075207032280005c0801c40003406210090456401c1d00c040c541e0356096000700600075042407000742c8452140818107031001402c1050000004402860301d0000d03811511042856001407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 981392464 1250 981391214 981391217
    0x9061b27210d17040c0506030a02160f12020d0e100e04051005090f010b0a0e040912110706080c030406090f21120203040b280204120309081c050a 64
    0x210341204204055610262468590700001e00254a0512008115039083c035808450743c0c00303150900c80000c50300300c441e40c11180c040b81c2c49510390b11071800702030084c0704500d0351224440039a26408108001e400ca07100c0d040c2d02034418441c0c6152040001e1740c83c2c907a0408100001061801d0201c51490520b120448110082c40d1503040e0401c001c0200c0c0403141d090700e5016101c501d82004211900e000021254040c114003a4440903501d04070680c0141c0c0185540c0da4244070344801c21307003901c0e2a0f903440200c5184c1c0011109413126610480070344844a81448852240600e0b040468624050604140680000741c10a4135590f0365403a4400144a4900111400d045040100c000b05aa602036800700618104443c4051580d04030054041c0105104801002e07005104210124030a039071069844120700008183c1901164610105000c2c0c1c500c2070300b403031880410301145075505d42044009561082c0c4800b01001d8640f404a507079029014041c1700c07203c0c01d81c3c10010b1481c3c0b00760081c02c400d4009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 981393714 1250 981392464 981392479
    0x60807080612101a04050601050c060f13080304060614040207080403080a0212030108010203091908181513080d030917090a030221063d030b09061b27 66
    0x4001c4500340e80051110b861444014003140c104c03454184130b101c0e00100c090a0652515040e55442612280010080b191007601a4005413624000303194944a0302d40c081e4559540c1e01e1706180041c002e0985014860307034846540301207040d134140340c400c64403d81e80141a540c00c0600e1580c0d0750725035031f010340508002c40c002c0e5030045200ca111840554003070054903002507282e10b850701d96140b030580c0e030034a1401c82c207a921110360045040170048510310015140003940e0910030700e020604440c0c400084856081002905c11500c4801507850005c0e03500b01401d4801a442d120400c4068602c002d80c058814190a0014240769400b030000b008078000140015a105540750000340742e8070495041c1c5165081c22103000c481c40c00e0309100c4180d1000d0311034110718408a03a0b02000d424a07203200d1540b0701c03400300b2070f58082e04403599000c03442c02135501c086c09411a1a03d124130584540302603c5840300d1454120011030400f03078910130749010700c1c00c1500d40c07100101c094031110018190481d132690400b81 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 981394964 1250 981393714 981393733
    0x150607240204061d041119030902060a170916180f0906020c0c01090312030f0b040f0b120a0b240a060905150412020f0307080a0f060501060807080612 66
    0x10a001074002040340381c41d0f44190b40e04c0e5410385030003500c0001c68144514600f400c440740b050a00c0301960300a510b0b1503512461103843c98030030b4000b40000b05e4080c0d072104001c120700003659800340d000d00010315404020049030b240c111500382e6a03c42410540307a00203103c035090ec201c004030510001c8004000e000402e00000500c284011144140030a544954001542c03042540c000c010740c0711007601c2881d11006075803460300c8820705140100000c10801d500c80114909006886d0001140207070002d20421850041a00748030041917508207550250030000010450550007203203e00d00140c101c0030109480d41c424420a0309850303185001c29840000f81d01706086600d0700e0349110080c00e02c94454008687c10941040301c818005540300c0d8071b204003040f041c0040746111018008450b41a11103e10900c40080041c0c10040303035410070903c5119070f10443c0d0910980c001c031540c48034003030031081081e030362211022a20000c0c21951800411118000300b2820b041150103243c5441a04040d14040607 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 981396214 1250 981394964 981395033
    0x606010806180a15153218040606050703091a070f12030b031207060b0604050303070507150309030f0e040f061712040e0103060b060d140f150607 64
    0x1c000d4a60210199a400e40110031350030a01102000d01000c4e180f29040e1160240000d00300b844200540340140741d01d4054112184041c20007001d85a81c0c9201ca0780c44402c0c01a51600d480c611041d07082c41a41011000100b15014808960304250035a0782e810f940b9003800c250305444d0807941d40031503020301c0810100011079207100c2c00d50034241c81250a6030701038003100002011707101705440d641d00c6604400010340100101508803072005070311141c04150000400006011801a64005030b010b01000803180c0c00c00502140701c10139201d408040800c0d000a503441241110f20200005000c0385140d141d00f55a2402482448c8060300001d0000c1103101281200109845107540b00d4644021401001201c100d41032000b000013042c09003c45080501d0600c888a1502040c40003500081d5a401d900b0610380f0760108460500c401c65006021002d1000c00e08014031008035120088149c07850081030f001c03034174080524180c0038010034090510340f01c0d072a5102c210004c00c02803100355224014101405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 981397464 1250 981396214 981396259
    0x110f040b210c1309260a030510150f030c0e0625061505010e04020f031801020f0f04030b0907081f0e06100302030d11071802070b0414010606020703050606010806 71
    0x3d04119002c2290314a03860241c2d00707403040707442c0006584281c000303000240380e0000a445811041d03103008a46510b540d154401500c1c0180c00000060b00840c4910b000070390440e181242c2c01001d0f0340c0410032280400da003165100345410603d6803110040000c080c0c94032041e00c602102d050034001940011041daa28001107401c03003810548286035818040103950f030004d441400c42c80c0156425454407811405203142484014040610200440d9044900311001d5046d075041030300d0902e0859644901d04002032603600030344001c8500c1e980140000f2510306000c20b1440484048070f006100d0b04043c075100624516640602c0c00c45250f80c0d050340f000d40041001b240d801421485034401c5543e007036005140c00c03d0481010001442503510700d40f000004001261802c88000b0101e10b49038030400c0d2100c4000e4800e89070090a802c0c0c0c9a014007003032004199405000200a000070420b403540c034a0143d0710b888092101034141e07040302000a6455020700703611944508003d102c0c1c5015001450400e200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 981398714 1250 981397464 981397489
    0x1030515090a0c09080c100818060a0b0f042306011704111503040c030809011e093f020415060509040b010c020d0311031303110f040b210c 61
    0x99843e802c0300606550045908000740c03840c04041c0c05031841d04404aa100791200780d01300301b08403040300080c0c00b403019000303489003400c00304056030140c0c10158080c0014081c0542c0c80b030300c18a400c24089019292500c00e1190b82c0c23700d600b580c202e100640b00e05200840d0010840d505002c0c1d000c2625036103000650b00144a10b1003104036402e001080f005000c508281c450000c0d03805541002484003143e419a104e4040382e90101045958a203450012940b105081c40080c1c800500f2000c116041d0360010031000031b59600204000500031a0109651a4007800401811541d09880402c1c224804003500b1110540042d002150360700005c09070a01c2c0300d6041e1311a00020701d000c201a40b0b20b03d006d008000010070240f910511000d850b40010b1548518004001c1c14000d44200c5246019824401d882c0000c680c8901540d99540d03a080140243e580300164600c10240c00c2c25003409071401e4031814041c1400504003012a00c41ca59038400980c0340744012400c14410032540601344d075a001e020301c60 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 981399964 1250 981398714 981398731
    0x11110020c0706080405060408030405121b1c0e0d06060515040f0e01060f0c060b1e13060602060403050a020f010906090b0f04171803060c070b0903090d020103051509 73
    0x3600c14640740c01d01e0078000e56030440f804001c8804207000c0400c03400207400d504940c000181565986480c6001c0303142c405954140a5034036008a40480c14400a00140b1040c00c004015a4130340030520b0b0588ac44100075604a00109280e5414482c07581028101021282e1281d07000084080d1140001501141d400410f40c0c108075000909009070540c4420300c37001000c41181d002410350502c0405020315001d01c0c2a10108201d4038810814013003da00301d16010107000e894903100c1c61801844042e58150310310010301802a0448621f07100406108290807206ca41d40a0a01b035144d80d0303011582a0b0040c01100114494801c3c01d4448010a210b1000340c030744610000103a5546520b02000107a50091102c440540d0007010080800c002d860020b10400402c01500c0c3e6845815903a1041417007400d0409030544208401c200c5203403d840000c0090702d000b1081414107a1318403094a40d02d1080101c01c5802c840240d20751030055000350000340d080041d0409055200044d28041340c0084001c4420340c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 981401214 1250 981399964 981399967
    0x20409020c0712020f010503070302070f050f011401030506060910031704091116140111120601180f18061e1502070e010308030408040b0d020c01110309100b01111002 73
    0x103880d0389040000e00e00400d03d151202c5201d141d6a00014410300b800b6550303e05101000001a10252099046411150703000079017081411a5051840e9560841ca000c51a29807a002108e42c400240c2c4100306e041341e80c45002421150790784000d000f06808060130303290084000f01404400a070b00c0c0b404280b400d114011106480b185054220300603510320328520304020308100700c2000c0211008400d0038121350000041c01d01d030030030407240900400000b1f0700c00401c07a901040101a07003002c0c2c0744050040310240d90b20385000509009587e44c042c190303c01c3c60491a82c829081041c92855408807071800002ca0740051410f550f20090a28420325086075450002040400d0001e15917003644010901b0991000307042d22828803c40110004040c08040c1c402503001c4001070401050703c048030040c07c001c060981d00c4500c8900341101030341101c107485025508207003044560b0300c03072441520700c41d1b042c960041008024842528004044940f4001d04102420312580b205007001c01c105a41c0345060400107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 981402464 1250 981401214 981401227
    0x171203011706062704140a0803100506031003030305150d03051c0e12130503071d06030d050a033303170a0207060f1b0f060c0c23030d02040902 63
    0xd9040010003041180b107080d612802c80c15018504810121007120480307610138680741c504100780800018040e1070800d11031b8145c91410003219001460292070600014803155480c1c208001c9240801c60380d901511f00003100400110b44aa0041078004611045007604440c01d00003140e103035a0300d00030070b8020541c00100b040c5181d025444080c2d0100d06078008218541c0080011130b00c440d801c11030045516004583c5150744071421040000034240107080701c0740c40c1c5d900d0240d148401034040c03480507016030303c10004045040201d40440250025030790b00780b50815801c0250300810070b0100400101081e030403101002011160800b403401181405c0d0b5064a18501e81007000b0803a0304180841404207009600e4186d400080440070345240b8180400720741c2003840100e82c3d0103d4400c5120105a002d103200d001c7c4007004084040d5940900d00502c550440d00d001503680b480365090042c14071800380c1094002e0000d40000001d030000450a5919004120010900388e03005908140c1c14642d002400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 981403714 1250 981402464 981402509
    0xd0807020d14010203250e010e0d02040e0f1e0102040f030f0f020a03060209030708070503060a2a050d1428141008011b080a0b131a0103180c17120301 66
    0x4106ca48403c7c80c1114032004800c000801105841451502400d03d000e094811550740d03801070b60fa10042041224610382d04c2c01c0b25107a44003150703d8075110003a86105884441356042c0222010f41d12884405090a4516558907610016403901a43c685101c6509800140d5880b880000214000c07040540c0f14a00d01c802c15080420690000d01c0f01e40c84500d0810030760318041102c030340c001c0c64008002203a401c014540074400b000e12100c1484c0210348481080c481e500b203400b40400800101042200040c0710740b03c1c02d9581801e8454240180707004101241e250409403121402051000000c1205001c141d81144045020382c0d94000201e1500c4091104590912501541d940c243e11041700500c0d540901501552011306420445a03c1d94002801da0702d8052643d50350fa0b1643c03100b003140d00e0031a0300344000c1140360204580000d003021520045944010b25560710140c201c1660f04030a4904400c1030400c15000d00c07583c01f01d0041c82c008021800d00341000d58000e050b024000700000001720b04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 981404964 1250 981403714 981403771
    0xa1d0d0606051921080c0f03130e13170c03131d070f0309020a030b0a0504050c011412060d0803040b040c0501030c08060f030709050903090109050d0807020d14010203 73
    0x4500f0006400ca60400104420203908620180854112003111825080c160031070700c50a10b8105980c070507041c1040f02c8840005c020300e41d82d034441c0110f0114030f40302d840510f50340005444582d07070407001c0d0414202007451845c20803040c4a243d05481d10300340340712091b40c0c1507070450b850082d1074440c1140c080145003018204600c00c40f20f00d002c02c00b82460589400380506600140034010599600210340454540c1c0c503808000d150004d00400207441c10005040107403004403811036447c011400441c00b2540903803038112142c0c805040303560406500389901c1401440007003c455005a17080101004290450b000b5401036014004003071079071a0a04100001d10040d5004504142c50420b00003401c940c4040d1071070b080740c002c940682000540d100000c1c902403168001089440c90030082c8601a200000144541c010a88840e01c03080d54903801c000b03400d5035810000d049408100025801490140e2802c5540e034401d43c5140c00380042d03c28030700c1c00c98000b02d8001d0301c0b00b07140214611028801e0031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 981406214 1250 981404964 981404989
    0x140d06090e1b0a12150603170304031d090117012a080c040302180a020c06151203030c03010b03090f1507090e1005010e0f0913021c080a1d0d060605 65
    0x43d80c109201e40b8100718203030044460314000c0e000303040c0c01007040c00000300381c1c2020009540040d01141040c1d540c1c4d0480503a54415034027240480e140c44400039008a926110b23031003e000040c04111541c3c64040d10070040102442482895542c485000b181c01c280642c88a40035103c80d442c080c2c0c0300407012000f4107078200c090020329008100380000c01c0141d58030452025a4500f211a406190b00d60104800181c0034401c00005c080c050041003264a6000710351f650030a03d07003101e4a0101c0099a449140c591000380c445880100c010030047c080303900c0520080d90410005c504590258040b249120304021849298440601850040c010880d44c40300310480030b8020a490301c003880c1000d4000743c01408a500c101c038140015104440032581d20011000a21003000e0218001890445d00181a40f040950103e100301100480c00941040741c034440540a603001003001d2510340181b800b95909200c00610001d1288502c1001140d612401d00034950948280e034081401400d00342048090541d20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 981407464 1250 981406214 981406219
    0x80c0706110714060c03030703090c0609060206160e03060901060e010e070f27090b04050703020903030d05130f0b06030d020c0109180b030304150201050702070303140d06090e1b 78
    0x1c000035000a003000c5402801c45090700c2a15062100d0302c0e010444500070380d41d118555000c040104040d1a805801c4455034a2060f60403424098440f102600c050340c580c0650720040c0d01540005000070380740003d8501c10303102c0b801d0808100c954500001d20b002030445d84540265141c103810005104c542021a01401c08200300554a2405d0032000b010f001c04c00340c940003040008030320500681040310204e10a41e60041882103402d4540c1c00e650007412007a0581400749141200003a43e440c420b100340e4410002c002d02442c6032012f6800b82c0f0010340700281200340e00c1a90f020340c0e200083c400362141703107507580b0a800b01d400903c0d0001c01c06003046161200403055412a1259015580c1d1000c14a130588190018800e5241d07035805d07401004024416015406200005010600040755820144844800c0c1e000380225030b00d07494201c1e1a4105844001e011608002c03640040d00d1504000e090690f101c1800000e16581c2e610100e0700380d0382d0f1481100c3e500d4111109031803030180ca404011006610070b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 981408714 1250 981407464 981407477
    0x60510050c01140403121a03010c030c0215071e0e0306040f030e0f010807050c070801020f0304021005190c14011a010e0118171903020c0f030a0201090302060a120603080c0706 77
    0x41d14064194046c130403603204100e5490913000002841000e0020355120050000c0005216008014004215203030305103002d441102c140316408000800804e100e40e1155441030400c5e40b03000b0402075502c008520a405000e282e203c0114140c5041112b1840345008040d40c24075000c0a003000b4101c0e0020309411400703030318101403078080344e42c1289100da0441e4291600f16a220141c080b102d0801c0940e0f04040000c2d4000103012050404c86405940201e00880380510082414013054410b845030616401103904121154510140160300b221019030090079103203588032081200e01c0c21203102c0ba2400a416180741712010070342d40d104031000c1030038400307007480e220040f00ca122807041c400b80c80c4110725000705c04100c0d8000ea00414800320602d03c1c402c98543d4810f4409240194079013101804040c0501182104803000e03140002d64400c1e0380e50181c54103601d0368103680900000d0343c031244003401481060b4846d4006c04030079100340b030015801881c0340f50300c40708180e051f04c0c1082505e40c040c2040080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 981409964 1250 981408714 981408721
    0x30109050a020105030a200a0801050118030201030906110d0f0e030702010203190203070203030f030906250309030921050d1106150a0b1b100c0905060d060510050c0114 74
    0x8005540c0c00030719024203001d40c4994072425403001030030083d40601c0d00c1c85105c103804400455a0340241070328103d141c9802d03060ba230700d40f00111400d2402c011400701d24031080d0302c1040954000c0d44503281607800b0300801314441005601080e580d41c06104684001c550b2040c20285c0c5110302e1054404e158107903009145400002d400003503a07805640c0805400c003000200726030601e0700820848107956400303000d6039180c40c40000018103503042215224054000c41c40000c070740d180500c802a511141043e100b950821010701c1c01c41c01850451801c900303204007480b012681e010854014a81c886e80b0603400380e4444114a401ca04100015101c04107200c2107000264400c4408582d496102c2084449491840c0c41d410000d0108030440e4403000364404009080d07001c01000e4940d0f14940304407201100c0e004140314140c481118042c44040d0700046140d0f10911151030654010102d02803200c2000c00c0031519080003401c1c01d190742c4c50000c041000040c44802c040f00078003800080c0c0762003442c1c0780490702c3d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 981411214 1250 981409964 981409973
    0x20708030a09091503060c050a11061303030b0a0503071403010f020708033d080607090e01050112090602030f0709090e0c0904020111012d0203060a1505190c0c05030109 74
    0x300c2c0e07008001039280c403004200c000318902d42c0c00b0401140c01801c01d011901e00103601404540c05880362a0000e2080c000c8543e90381070010b03000740501030078228015400426141140203160441845d68018182c00001409903403c000480142001e2400829800d04440401d8212074101c0d0200c5107480c0140300744004184030340f050f240c0c4110300c0940b8004c50880c085084500002c910000302040300d074a11086008840420039006880240040303508030b03140d0742801c0d00c400907540705980e050442000107000340d52150f0a40e12441d0500b04020581e050303030b50b0703c15060384c00468001c00d60044c5241004612680894403100400c812001008919030303d001d0240c0b98441c80380b41c01d0150340000c01160459100b9101c443c8402c0081c07000304105141c485405625140c40c06c042e000800c05004005080070032442102d010340c400a01903404585004803d000800540c044001840420b0010042c138a82e800b01460102d111681c48000f0700032a840c1c103018100035600700b24042da2400702500000b6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 981412464 1250 981411214 981411227
    0x160c050a02100504091107060501142119060c09051f030c0e030607091a0421030c0c1701061d040f150614040507020a020d083403020708030a 62
    0xd07015658120340525054040c2c1c0d03144500c2e40505803e03441d000445120707400360009440707214842c0300c0901090740d0303601c00300c0840e420224119505c6245240200110200d10302031a00108020055a40ca140c1d0381c00d0110b008680440c0c02d44056882d03541c081d00c0701e544501e4000291034221007180154103c600301c2c0d07000c01e20398a990014103503121001ca05c1107000d101c42081040005040310842d20b04008020082081482533290002640303c00700e9240400f03100740c03015076000103c840100c0c0c90b0900d4845a540d0180c0301502880f0303a070720742e141c0070452040a010140918001111146404080007801c6810a03448020b1100c51504034846004081034020781141d01f04422030132182c4503007000d0740d003c44000e05807481140340c40c9001580102d5001d89240c0000f044608220560342c4c0001640c8600c04410001d601071540020680011010400b41490515241100c880c0070a9000030800401c40e0402020074040c050141c2010140d04102c1c8802800c4941c4c040c1d070400540c070b000a400d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 981413714 1250 981412464 981412483
    0x27051c080a0e030d09110a0b03011d0406090507030c0311060f191101020c0a060e01050906061201060519080f070e01120614010323071206050627160c05 67
    0x4080d200d481c0010901030820030381d1481c240300c104c00c115600440c50102060000d1054131801219004030004865441c1c0c42640d0484030522070b04204070086800d00021040001c00444042d941d60801c5008a0801c1003240042c600c10300c0038a4241d4154248031100c07140c055002482200b04001c11000d9050b480140d1311440c0366040c003078039007001808064a86100b90b8a000721342e58408200f2101d1280700044441405000e01410071150420103030072030a0f10400c49100e4000d80c4080301103410740c02c0c00203c1d480c485590b00c00001e00941ca07400015070700400703001c0780201303180100300c10b10422405204507500050703d80000c0200c20714041e06190b10a0701441100070702045ea415201c00d02c01d550304a20901a100014001c031582c6038039001082c030306180080e50741c410a2452000314028000b8152083c0c410b031201d203805803030310360392160080c00005003203941000035403071004216912001c41c2591800c038414200c1c10341c9000c0c001c504015690050031001c0040d040c000c20081030001c51800300c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 981414964 1250 981413714 981413731
    0x19081e1b16270f020306010e0d050a110a080601030f0209090c0d0305031003140a0611040b120414060a0b010305090a110d140a060b031b2227051c08 65
    0x282818103140054001203100746a401003030518030400303d600120741c01103204071001d80300c40c0c03003240c000e106012407c1e600d50001002a844000313001c0c00700b8a010b03002c84204900801c0961000e403509545424000280c0c404c8a522040c2940d1100714641100201d40c000c6da0000109000380100000030b0310050480b4003d024403000001282140300c00715441009560810108410714070060541d0380d8a00303000070160b80131031521031441c011086200c03c8808948640000504000d40031600000c42500504100c1c0c01039030030381480b02d038403505010052042020b000e001603065284800982a94401042c42145420628240d070004141814070300300104150f403030003800219881c0c004100c0c01255488031151040c4443c20702048025000b00007008010340c00d4601340c480444410320f603200f403403542c41e0b0b004041a20b2500c0c2c010300f2807040090b422076440003003101c1071120f54100803c019040c410340c40480c2840c500046c420208000e88500a00b004a0b00440e9001d1400500b8220084d14480d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 981416214 1250 981414964 981414989
    0x7120c030f1b140c450a020a0e090408030601030b040204050604060c0c080a1202280206072103141302090408070c180c0f020109030219081e1b16 64
    0x6690001c1000f40402c115005041d540c0c04403901044200b0380307201a00d110494001310640848203100140c070680e8804103040005161ba140c0c2d0035a00c02a420500804081151240c2004010303550418414000ea004074241030307403403d0a00005040e1481805841d014600400c4100300603120f04e000c446c102c1c0c04502d481198100503240198041d280780c2d10080c481e02c14115070200b031145281100b511003080c0c3d000c40c0c502d45c401040140700c0111010b0041f40203d46501c0810250030100c00404c0c000748100c0b00c010011003003039190050645080c5407500085da03244200b041301d0081c540065042141e03034601c06640c0e0b4031580082c4486078010002480c80402058550400c006089484064201403080381c0c0092469800c01005001c40c404e20000501001950b110080c0188560030390140c055020740380e02040c0030b03040c0391000c01000c42154400c20820860080400c00001100101d40100610707a4031603440e0a031450700c00e0007901f1450070740c120100c1249802c109010321001c50301c0000055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 981417464 1250 981416214 981416243
    0x30a0c0509030303010b09030d020a0b06220501060e030d03090215090a182304051c020c19080606190302130e03030f0402011b0209150607120c030f1b 66
    0x311900d00541c540103402d031101000100e89040700c074000d080b5030034094048411410b40d61074200d9803840d000c14090700008641010840c0c9041030720b880c0b481802032400010f00c40401030021011035100340d010300006496003644620a10b0f003800440382c0c94041e842c084c030079540103400140c0d6852100700c084001c0f240c0044e00144685805400c0c5000b4a203448680310720042e00c050b450081d0100a490415441344030303440ba514000000441c0380201d8002c0c00030280c030140320818421014841e582c80e0709501c40d000c8032080c195211500c1906400c4400c84440c03080d0700e00f400461074001c01520551040c502c07403040e0030101c10f4161944c41140d40490f204040802d001300785c0300091103010ba074804a8080003080240101c42c403407001b4002d40c400c0e030791110113030b042c400e8503c020307030482100a507c025900080307100c424003405800f140b04d10080030240b030600a9502c00c1032911090702101c002c41c0c541192102410b400c0150440c00e88094140b0040880c85048802d0314000300441c01002c41c44680c2c46c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 981418714 1250 981417464 981417467
    0x509072001050601080f040506130615080a14030f0a0f03061a190e0d060f061203020f070e040809010c1a0c1c021303020d03120609020a08060f0303030a0c 68
    0x542110444800104030803004040000d07000c0c1800b140d18502040394100824a043d82d50700c50544100c2c0c2003000741c06162a1052405503600f280c0c0710a540d10b540310100744591840f505070030401448183e0003428000c004c4e251078190041e090544800704e4209104071420103240f1811188601c680303160800b5002c50811094004202640060f401c0550325030141908465050045c1010050982c64222603240c4103800c581d042d106001907900112203071074840c001030081e044002e03c601c0b00348011440640341c0c02d000704100807c0e40e040d0016400500d041c0c49241013031209001600b9146283e0700c0d00e161a0300c6000d0319110b0405c01c68104090311070f04006006000550f51001c8001c98040d01c901d081050307440302103400c500341100400803490086000c40240e403084640f440c00d00d05000c003a1070310303680800807884021038044c0c041c00303c45a03452045e10f040b4800d10000d40b070840d6005880750702c13000c4010710741900104003034041c60603101003082c41e0340e00200b6a07034055040040481e40d1040c0810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 981419964 1250 981418714 981418727
    0x120e1c031b11011506020d050c03300a09081b03190f11210309030d021204140a0302101d0a0c030501110310030f1e0c08070b13050907 59
    0xc1403440100c8007141c400c1825446110b288030300401c48021300c00e85240303503c10600280148207110260740417802064aa502501c050b140c0c0502d5241641e05252901c804000500c1481602c01800b181d045002048035102c01c03500340d00180024410845803003940e4940c002c0340f04052589440d01010140c2d072034030200c00c00485501c00366008241c1d24481c400c1c2d00c054000e40211829502050100003808622080081c50341c2082c41c2242e048620110135158089030340d400034150079070f20f0104000700903010002d1300041400228408100d0781078034041c104440b1602d01b1714856a1941c1200b03030103d0200380c0c0050f801401d2182400c00090700e03e2141400e00341010001e160003814001c0408540900081030005002c0301d0103100240500341490061455600c0222003519145070b86060501c04176041081d09403800d072155480c1100c40111414000c1038100001003140e00c0c55008100b40725001c02400000028030707121264a0400406040c03c880c03880c5c1500500780140c0d5080d0005036400d20920 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 981421214 1250 981419964 981419981
    0x50606191d0a0c0e01020a060b1503010314011d0d11190c08070503010608100b01020102070b04060b12030c0d03180b1611072d08011506120e1c03 64
    0x80301200d000219000711881090129140780d03103a45002803810099001da1021424110140c1c050114076060317640700e80c001e202c00300d01c59402c00c0d0100c408074440c40c04540110f001c1c50160b80409880700c00032000c542950156105a44024a045a4540c0d440800039608603150414180200da0401190039140f030b08001c00b175800410042c00c0745040500c809840400242c4904400340c0702d80c141c0380e405050030795126100b6003505512213001800b8800361030344100c074840c50505c000740c50807005071518001e40000382c1c0d0680c3c01c0342d510180e003541850115040ca4081c200e15001e18140324002e03c506454681d810307099002d150b15403444071440400502d24020b41030b44158070803403c0c100300d04018040f44d1071380c19590108201c001c8080803000005540411101041c1c240020b001b614494640c0c000ca61035055403000c0350f507800110b1003403000e01920400000c4110f884200500e407050082c041c80d480d4007481c0d2810715068032401c8505020440440c1003d40800128004000c144120010f00c400c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 981422464 1250 981421214 981421229
    0xa051309021c03020709150605030c0d0504080c0c04050114041505041109011b0b010314030d090501020c07140d02040b060f070309140103150510020313030605060a0b030405060619 79
    0x1518801e0701e400e44248041006030096017258482030f2548919000c558a1442c0d50204202240c0d080003040e00c1400210303404264040001c1c10204c82852607015034005540440d1080d9011800711001c1d04200309000c0d503c1c0003206c1c10301080d49401c52501140c1e031800802d030700440c0c40e04951800c2428800c1d0341002007402070001c104941c03881d1801006500600201070010b02900d00d1020644508400d200f0040e8100c00c1c02e804903440c569030642d818540b207905c0c130f059000c10b0012042c025490700c16807072214060400940c1d80e07442840c0039810306e2000d4024a102c0c1098501c218055141d5203503041c1242c0d8161400600c011512000690902030301480b070283d000009000c4040550108000c1d04030b032001810802c2a10400c0010b50980b040c80e0303001e0f40040c03480030040000e46440e1a5681c00c94543d40144c0e80382c85141c0d040948990800e8206640301604c842c1403005500380007024400500c5040011401c504050b985c10fa101d20000d03040a100d508011105a60500307400e00b070030010302c03d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 981423714 1250 981422464 981422479
    0xc060e34030611220504060609080c0d06110705010606020c04020a1b08090a1203021005060904030f05130b03010e06060703090605090a1503050912031003080d0e01050705041809020a05130902 84
    0x24641424148414011700380114201140010900d0140c0d642c0d00a460010000d00349103040303d82407152a074400d08003614029182c3c0c41c0004940b04100c01000400d02450002c900e05003081c2003e45031042c0786607101c0c0264410428442440d900c0000c418100b0100c45400400e214141001c01d540d00400d00401d81c8214441400150074018070054160f41d4481e8007503490302a84d490001c8215482200e0f000d4000510f0400100041c3c4601d182c11169991420610305100030301e00d603c0c5c034505682d04080030221001005100c0515800444e41e80320000b02c4810b0303d0285142d8006010070380c20f12559042c0030700410248550b80d02d810b1401d01421501403031100d43c03000c01500502a0100b0b0724420158005d6416104075035045800f103d109180c4d41c00381c04d00403465541d5586c083c2d4422040c5001484c2c0c0c032031080b1900002802114000c8003140e54030f5486504061400015803800c1d00c002e10402d02c1e00995500588440000c3d02c2103031821281c002c2c210b210101c40328040d01d1500c400941c13051781e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 981424964 1250 981423714 981423757
    0x3100911060a090f09110403020607151a0418211b0f030e01081b1b01240f060e041d120d06050906060f0a0c060e34030611 54
    0x40c0024a0f6080390607581070b860b085640e03102c00208a0340f103174245c5ca18080d0100b20603c00340c01d2100003000b07002d10440b01c1e21f00c01000849140120754a04601541c54400130103518140c0c0b625014141701c11000e1145840900c401b42d9130341c071a1041c0d690b0f0541e0f030041c4c05402101d4180c007130301d4034100e0082101c429130440800c524246010f1940840c0c210003040c01c1400381103c0d07503c14050980b0504041c00120501e203103214060450780c03c00c2921608013540c3e01c2440091180c01e0003a03034581c0c00d50310a5110944803500102c030601640e40c1154540900015081081640c0304281c1c10300301c901a2070000d0070400c02c0018581d54200708088000d144990010a402403003004002e011014509070104500e580320002c00c000500f0603201d0550050b014403100110440e010020881d03030942c2c0c01c100c0e83d181e0319980c400090303c40100d164400c40d0491012468018507910303144d20712503c60240c0c504481825007128020140600024046d5540c4002400354082031030200c902c045a1810030100102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 981426214 1250 981424964 981424967
    0x1180303170c03070f1b020a081b011701030b13020306100810020403020105070b1f06090303080a09050607080a0608070e0910060b0304080c15070507020301140603100911060a 77
    0x110003122850141ca00303070000811901e06541620b004400c140d8880c81c003180355101c2207030043c1c110200b64142105e0980d5100059886074481c3e0010140c030320140500e480c0805080005451030340d03c1d03e040c8884581128000b805814183d419a6841240c070b68450302c400381e0040f03012103d900c0003501441845d0610000c0c552211003e004c44240b5011144655002000001039009030f01c0000e0208805224950005503084c0303455038054241e119444a05000e10400c0e680040603604c400f000c502014028414503a100e000e540d4060800d000074419440d032079a51554a01b1b00034150000c0080380e07800b04554001a4105000408a1004658403203845103480651000c09482c1206148038118100a46121342d000b04411a00340c01c003102d04580d103d032102099540460850000b50140c03060100452501600c16401060a640c49a4899400f40305040c00c40b1100b07140744003441080750800c02c280d0b50025002840d0013039074002041e44c80c1c40340703401050310154044565011101007890080070f03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 981427464 1250 981426214 981426227
    0x20a03120c170d060501480c08070603020f0412050f0303011424040612020418050402330d06030c14090f070e04110d06090614030f06130201180303 65
    0x401e05080c10004180e4030170040d540b164140c040c1281c41c961031510b1900d15103910211946140c403403241014040c090b90740014012001d11404c6608111010080c000c91004001c500050201c41c00c04510b444a4010b00c0502409039100e504110402d1110080401409210620840c030318601100d44030351310341c00041c1c0301000001c6024040e0002d00803492041c0c40c082640d20035080350041c0e003403410f400c0a1040715020000300b040e2020980810001030b00381e4009540f0303030070f00034986d90000c1c99041a1041111134410f41311000100010241100100700340c040484101c0d2402c140100c0c0e880001c90085005046168405801405007a9001441c882c0d614500c103d52070003250501c034030b5520020319001a0005a0344040003c294410f010b507541000c1d480850090014183c2e01c4c1081000140c10003510110307001060354030303103d140030421450071050460031404103c028111200500c0030b0f040e42c4400c000c102030343c0e40c4000c0386038205590240c8400d1903071803030403d520f03242e20f0348904018044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 981428714 1250 981427464 981427477
    0x290f0d050f0111031323240a09020f0f040b040203040812060102030309060402100909051003123912020604121e0c05010e1f18020a03120c17 62
    0x5039400c04a01103d0009404122445802d082c00c1c007038a640000d8072100341114250311107030b440141c1081c10902e0030904000c030384102401c402d0100c401060b03c0d03c8217a021003018007a509103d0502c81d0541c0140e450151180c40c0840070784031031090b4079120300014050041c4020158000f0300c00000c0c4400e20115400404000401c0b00380e44507183c8407980121b0303992008480000d513681204021a0052820402c00c03420341c641441c00b03c0c507090300e902e0040102d80c1c09072040300407800b40380010000c024150062042c0c0960780e092200d6208492101c01c2c00301d24100b071a4440c0ca841540d90b90b481c0e4894200b004640e61740080d4080c1e41b12051000103507507041c05407000d80303040d140c07040c12840c85889102c200c5481003010901c0518800042000e41e90043d41d1101240c055490b002d0805030310310304000084024030003001c0b0020320400c000b05401121074251044101041580a100250710f401e8408001c60350b0204014485114003001110342903025400280510700d80711120014500c0701000e4101e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 981429964 1250 981428714 981428743
    0xf05190e06040f1a040e0a05040213020318071a090111010207140a03140f2709130311030903030301031b090606030203010918120f0c0f0b0f0109290f0d05 68
    0x38131003100340000c1010b002e035100d02454410000000b90072070405404c101c1e0030510107404000003040c41015001607820403a02149010180181f60892003c01c1108200604410500b507208007001154911903102d03000d0f5081c1880808010340600c61000d5044070350460304003680d800f2001c82103819a40300c0881d06002e6000030204420309026081c040c0c110b41072004c02200040c030b069117907140c208424120340f09420b5140c2900301800c0f00d41d02c030006218841c228120704030080c004586005081201c00800440142e4002c0c070100743c2544001044906582c3c00c800380300d05580f05105022080d0f099074000d42015070426000044040d01600903505075071804009100e11014240300c02080b0040351400340c515008820712050240c080c0381070b00445042c500c2c200b91035261640300d03813814000304041143c030700462900708006107400703041c00d40c0505140d010a000742e1090440c14284001e80a0300c2c000d20508001c10282079642e941151800144090180810341801d420011745902c0301c207181c0034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 981431214 1250 981429964 981429989
    0x4090c110d022a04110309160312210e0606040e010b0906210f0d080124050d0b120c010801080a022803170c07060f05190e06040f 57
    0x8030030040200d800ca80100c0154001d2681daa10710001100d0840b036114040200c18100c04005601d4aa9000300704410124502096590421002c1649054100707052170010103443e107010b00019100c202c114610303c04d41c0c07038460f01e4071400c1c118410482c14280d003500d0029141808003c504000070540b103104880440e000c00071140f151030068241c90103c44100d07448032110000a80c58900400e1841c0240c00311043d00000ea0542651685443e0001c81450345c141c5c0190509000d56a1014800d40585180403050100b100c0040240400c0740d00034400005110300440d02c050711800d1980b000080d001c1c01444403600164a02009403140c0300d002407203002465001c004141c1e500b0000b2141c0700c150b40902600422904d41003154119078a090014450507403000d80080492710441c01d008041a9031401e4607a5028204151031501c6690b178003a20501c6084200701d0705c500d8105c42510348892005003605420403800c4012a065161011712a41c0039501141c00f0804054428170941074a03000140007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 981432464 1250 981431214 981431237
    0xc0a0507060e0a03050d08040311030c011401170a0f0203010b281509060e030106030b041b1508130c1a04060e040e03040b130b12070815030c0409080c010204090c 71
    0x1c00e0f0100e4013000e00240c4c0400140e82140380b207800000d522501a1401c40c01315591109040e0450381710b060748000316074403402e21000d07110103076084d20300600da010709410401d01d61240d12500c8022000000e042c901308403070070f1000c0d506c0c2900f1140c5000d0008101004041d1410032200e1403640c0c1d58407424203083c168401141c002c0c58180c060328504807586441c54140e2610340201c40107a82c1c00c140c079405540f2201c001001954040e15a0300440c4500314400f801c000c012210401c128290f072040c002c0314617040c0c1c01c4410300c0e00180701541051040c1380201200388103040440c0d8042050784420b80c0701b409610200d0b03151011030041d04c2070700c003030f035440784a83d04e060f10821055a035568040c11858104100400035807103410000d10b04030311154174101c0b440f5558070001c559a04a09000c03901383d000c1d44104200c0552040740f40f42e000a682d910b043c01020150042035580300d81c41c0115000702d9036880c920701448a22000d0702e51110040000b0355807140c0713911950010b003000c08848404940c217402c50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 981433714 1250 981432464 981432469
    0x22060b0d0b0d05210f0a03020316080114060d090b01260105011404052505070201030f0c0e0f030a0b04060c0f090b070b10052706040911040509030c0a0507060e 70
    0x2408003a0007800a090400304481074410100041104d40004002040250114507141001d026860840e84005132a8908000301c842020610b003102400c1081c0e10005100c6a80800060b0085d030509035031090300d42c0090040b442c0107042d00000a401540c00000002d84c0051000b00b09001d441b561000d01c5441036150740e514240c074028001c14140054640c3c50210b1401c0c65800940d200c0d000c42500398201e0b21011040e101d2290700d2200340b002410008078102556010f006030700001c0c80201c0b00300640d00216400600100003913100ca0301c10641401010420b030303400c00c2880900c0790412889040ea041c145414401408036004034004207580c1000d448540b4000d010b01c0d0100d0f1040b400380c9150000b20b990322141448020b0440c540d24061020120f60b644440081e1916131a003413221403105d440c80440b10a9600300100828400e508007082800024040300c0c031500c121000380e50120b034503206e004100f4214010311040301003611980754000203100d0001403403011158107444002c2c990700c0c2b501c103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 981434964 1250 981433714 981433729
    0xf06071209110d030e0d050604021e0102030a0f03110d0e10090519020411030c070302060901110915040e09030d060e0f01030327080d020c180622060b0d0b 68
    0x10050960b40e1040712003601401d0815446034628403a103032501c3d0440d10880007401d01a80d858082e034695101c98104002c6003001d000340700307a000d181000040f6150110000175528031400b5414420411466a4040c0782400398100b0080841a000502e454280e0041807500030140c154900c05544211420080a49070922419040300d4000000d02040e07000c89407040402e941c88402240c10a42d44c0d0342600005100001460040e2403104150b9690034550400034a00a0060821a91039141444140503010000d080f00d0109038151030103040001e00000c07181c1240500c0d4020340c010f418078000c000c400310b4080018000c1c101000420000140c0354210030300c2d0301100b00e81401d8108200401440400d018180c2c03500000000c045900c840c000000c1100502c1c280741d4403c00305a440440340c0030300540c0511a01003c000d00752985407459040c10480031001d20050b001078001c03427015600200003544c504c0219003400801e0014001d15070390391050b1445910074101001380324a05801c18032540790045 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 981436214 1250 981434964 981434981
    0x30b060a02060103080c0f0a03030209240d0e1e07230139120311092815020309040513020a03020f010e0901090501080f030a05030a05040c03050f060712 67
    0x1d00078080d680c00c50703680b001c19511540007a1014400c8942e034002490040021810552207a03801507114290700f4240304082c0c0d8114420385031043c0b03100b4584455400f02040d50517102d100030f8082141404036003501d041c00b0b205d01c4000c1c0e051107110361081020310001071b807101b1907003802da0034401d041d07240c8400c184149182c6c1b5110300040145540d00552581022500e044e41e00c102c500c01041000811040e0a0175006a000c80389111812104040c0c2c2d5014411003008401c1803c400d8501301540e030009000c50307501c5a4141c12400710230344680f0304440188003134014260240703054aa6001d01100230750b4a402078a01c0601c0703242888001040d1a8520090243d200e501030440d00b0342c03e040d80d080104511000c8441030401031103400302016a9a80703420346008202c1c9060018041d41801034050401248083c058100c0c1c2c802c20401d4030075584201240d0b400800d00313500184585451400f4500380c0f00e184c1c001342c1544640094852041e002045181c0281b86072b440d282c10452290b040c8c42d00b41d42010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 981437464 1250 981436214 981436217
    0x180b010e01050a3008040e0f040b0105030102090d260c070e061f0305061504030605040b010b0a08070f05090d03021507091a090a12030917010216020607050106090516030b060a 77
    0x41c90051000c600d661081c403250b520403405c4c5814107403250150f40c034450080b240c80100c04030b488280801d106400d030b901341c09054240c2c001c1d0301e0320041070046000c8034210080201581e00b4000681660358039200ba09043d003c0c000038540d540c0c0c10080e86690b4a4005d4010780701e1442400d8082032507841c3c4000c641611500d40644000c42c040842003e40013481d008208a070003041c443d5010f605080c04034014000345208120018460419003807143c482e401c160846003459408000e1050f8154001c07406542c8460286040001e1100d40ca004807458010794081d2034000321149500c03020160042241603203960b4207007001802c2c0e95654021145090b482c03181d803803480210158101c440c108880140703c03406010740340207085640c8603150058190005400e0b00046c42a0303006001004030303032408914481e1039000075400e00b010503080414100450b00000d2241800103801420840c0c2904500002e0801c4481040b1720b2408071a404e42412125140c140004d20346680702300c80f4504101070300d000d003246 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 981438714 1250 981437464 981437519
    0x10b070c0801091101031508030a02070f080303041a09070803031303030e0d090611030405030f010507080a1406010e0f0405040c0612020c03030705070f051002070311060601080a180b010e01050a 85
    0x1044c1c0154020607001c02e0f9003218034a0301001054111042008141c140e150394010001c0500d0084000080790903900240c42581040003804085000004e0180b186001d0404001c1e40391034101040d842d0401c980c1c4407001a001c04010003210064101740803400902944081c407041e1254822281c0314130940d042d80780400c3c69403405108542c403031488204441c219008480c07400c3d0311100000c1c40c2101100107011a80e444000f0822000ea00844640e0414040301d0184525815a030b110b45801400034505810401801c0400c1031540c0c8500700c065800c0300103402006642802d042017036200b4076a01130500802d24a5041c007d400186100715080c41280f040554115180d1020844440d8043c6005a5010500b0303000d010214005200400e5580800c200043e5030b01d41900c1c01926480b40408503101c1a0445c2c02006400e07600105540e0340002030040000d60340740045091841020a08405012074082400109081d0414a04079040c3d403411110301062941e114400441e149410030200c1800e800b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 981439964 1250 981438714 981438743
    0x1021903050a0902060705030a350618130b1303021b062709010902090906130f06090b040510080a080717032706101e0e010b070c080109 60
    0x110307a0100341c0200000c480810440b00700e80000309075070003101007619103170400110208415000b81d80080b081c10300041002d414441c0d4030340c1c00380d180e0609000954021803080046c809642d02c030b0821a440d20401070329641c0e400d01101c0c02d80c44503611354007100c80a00d444003090484650080c541160f950540c01000311083c4074614038074170401c9803075542d089030060100250000da940e5104c0e11001155441000350074610040010355001a03016880700c51040103d9140e07a00c5481c000c95001c442915407007005820280d000000f0803001c191803002da80707001c40200b003100e82504044510082110306110715100c00359001000720161040048542c040c0140500107250030340074000d003e0062010031244200d100f43e1640691085841411080451703a96101c5100345a00e10380c45103644c800100031515040c6020340c0803503068060401c000c109244001c460342c01c0b0230701c0c20323000d41301c40007042e9130650b510a00e41c50305400404007103800301c10302100840c030840e05218100c0002c1c4c101c083c3d140d9111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 981441214 1250 981439964 981439967
    0x30118020702041407020f0d14030c090d060c05222114010c0c0b16022e090b07080903030402090103171306020d02070b030c0703140d060308030a0e010219 68
    0x103010752002c03a00903131a000a08801e40340c001407a485100d00f60068001c2c42c036003400040c28035540d034401e001400100d100c061823503000001940e0740503402004d10342d512010030000502d20703409090010301990905036030383c0007184c0c8200680190400e8250141d900201ca107031140390507025004000d0b98950164030000704003000b88068920902a40c0360404210240d1115801d40d01c410300d20b0781c0072403400c0c404c0904101c1800b01c01603100f00e40c4005012812034a280094036a404942818501600a5182c079820b15840007010005800d000c01000f001d8010324080ba444c0f80308070740110104088000140d007101002c02141d00c685d60080c03400082e0780c05c47e510206a204240403e44000d80140180481c01c40307142e078134201170103658004016558210000038034223500340c1c1101c50610cc00f40180100501d130003007a540000d9140c10204180d030400d5203e13880d40d00881c025209654200f100c00400c0c002a4001540552100c0109000450011366030509034441c06240c0618244401d040c0720849 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 981442464 1250 981441214 981441217
    0x10050105061206150f090a0503030903060f07020705040e06090606150304170d0e0106050f01091412030c070618050901080a0312020c0f06060405070801030203030a0c060b0603040305090f040203011802 88
    0x60380103042020902194004c002a50060740f899548541d00042030b51043c070f001440305004020440055150440d2000401c0c0c0342c00015000c2c0044c0742c0d041001c1124113000b4003007032002e808050810005c030f000090b00260b482c4420b407107103e41c0d4052040401d005081902d0600d440202908503145140c984c0c0d99045a040811004e03000039490a00180c00802ca40d130081000b40e001400003c20101c0c20141001200c2c1d60940581c4d05100420008005084101906404030f4008079110f52031104d900541504621590800750301c0e6003e0b00c41e01181c4c241c4c00c081a0160f80d81807003140d07040e40c0d4458044c00b031100030038001c40c0502d40c40100706000081c402c890030841246440d002508145103088082d03e403401d101c4058085d0341003002049040e007801e200e081e40c00300d070030b140000300c41d4919004207840f440b46202c08410000d40740a1942840b200340c0002001b600050a000d0341c92900c0d0500030220b4001400d83c0348110b0304030641101500e01030003500e0603a003107600e0300c40a5501010500e0003d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 981443714 1250 981442464 981442471
    0x314030603071a09010f030b2d040204060215010609060e040c12050a02040501080f0f01030b150a0b041d010501080a09050c030304270216080d0e0709020c100501050612 74
    0x184034144021414243c034a0a420041100c54034a9448040c0c003000074046c1c1c10b680800d10304140c41d0902880d880e40e10161103a0100710110f001407107034680d458001c2e4440e082d508001d90890700000d800600a980025801081d02e60070304188500d036200c46084608590900c20000000c0c0d1100d04607c091030309034448040111386003030000286080d903107010140ca10441c4da00a080342d02090400055800c100015803060483d1101442d42c070703142d50300206420041c00003a201c3da180704000b442c102c201c0342d00d000159100416445649507140e0120003541d009000d0000e1100070f440700343c030b035010303007250ba56050f60016101e4084555a40e240c0ca0001c00d0020b030151110700c03408540c0a40f0751000e10084c000780010040001c44020201c0100322071080d0030599014141c410005009000c60388840f18080315802100d04e0741d10302451030f00c2000303041d8080001da03841c002d03a280003803c01c0b510750092507020080015641002440e48000b402c03a102407103000e0f0411410866030016820041280780d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 981444964 1250 981443714 981443719
    0xf060402040e03070209090714030f030403030c140708010f0f09050c010e0103020d060e010303021e0c1504082406030c090f091510031b060e1009050d0303022503140306 74
    0x5140b6135070002002003400781c0e42680950051041032081d210301284d0a41c040c0380a070000c081e100030a29046603248600d1001030100044005428108442d1050030400e074200b140480c7c6c4103c1c0c451200034000c0c40c1d00e030380d03503140c151400c2c10b003440004242c080e400c82141c01034040d02004804c400199100c00c40c84190b81e040541c208000442d04404e48074140290000c007031a0012581540307000f0307161425180c1001f200d07040100c4100481140003501e04040881500c80c450a4074034880b081c1351902a680000c0d9076801005904484488181704100c1c1d02807001d00c1c03401c01a10395a06040e2140354102c0320319085004400020641c411100d92035400c1000f0104035030140e81c05081c1480307542c10594284074030305040c400400c248242c41c000c2140c0301881074010000c05150403000f400b6803141c80842c3c0e0040301c805c3c040354103081c010700101c40207000140c078280f8490300b28038000f00258410f084801010243c2030204100042d408000341e4100d91580b2441310301008041164018bc10040581c1d6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 981446214 1250 981444964 981444967
    0x902030c09061c1a01080304270204090f1e0b03070504270c0e0c0a08041202010f0f0f0f0c05030601050c0f030418050703050c0a0c06021b060103050607020f060402040e03 75
    0x400c0b070f00319080301c00f40303006044190205000311041c60410300c0607800743e8800d0b807041c0018411103e00c029007800501042e0410000c0f41c4030b800a100c068010754ac820b89003185002e40e5014485802c1d0000c090141c249500c1d00c4d00c100a440780e50045039401c0700d1142d0554840034050140741801e600c00c40310440030340804400c031324003039509000c407800c020380440d140107051501300020900200c03086d0304408a002a1403c00c0c20303240d0000c007148002000035110203900003114044900030351110b03042555901d0240301c0382c50a010b141000c0c150300c0c0d020000755441c0c0003140188640a11a003014141180e4400b4615240d00c1c00450361600a101040202d004c0c0a00c03525001c4010002840145000560051400b540080c1c0c0d00c00c84070000c0480013410b00744010804c0221806045a0701c0800500b060480480c02e814460024001d188201c144c61841d0040c1c09811100002d02030304880c4078404455140e5581c5604a8856041e101040011342c011004200145469004100c03c0c0d4060000c90303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 981447464 1250 981446214 981446239
    0x609210c0b0f0d020d02040e1303020604030c0f0614090d080907090915020a020a140c091b0408030705010b030607021b06030627010f060903020a18020c0a08090102060a0902030c0906 80
    0x3ca0890740280c039a40b01c01d81d07000074100883e041150045600009001070b0341f00f40c000e81d0710007a49540f0700410003410031007200352080402811180c0d01c0a42504890200411008a1050083c808e8241e60f1707007810f407223074005062400c0d100700b013218440c60007003000e0301500d45803041107406004140e9080701c4480f00d03080c61050342d8141e44007070314010318690300602d04030701107040044148141c4811110507801c4550261840e40b1030407081030308035215807a12882030440e540b48852901032500003052034040054000180501500000c40900301241651881d483e94031003681d8490f0082c40090100e600007a00a1503071600002550b40243c000e080102c05040c80440305040142c001ca00c5550055094014009500c02072200e07005400da43c00c0c6108028210b40028a6091080c403d00c0a5609844001c0c04001000c1e019108600c040d0700403a1030b44603451504480a4000780c00e1140103100d401c00090314068130380108021160090094559041c9200511860030b41c01400e4903000031000910 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 981448714 1250 981447464 981447487
    0x91401090503190b0604020c0a021210092f090712021911010c02120708160b0c0403050c042c120c010207061107120f0c0b010609210c0b0f 61
    0x440c3c02050707840e1080090b440c0e003450104040d20019182600a520510040911000c00241d020103142c044074801c04000c11000d06c6480c100c0c1a4a00d040340398241407500041220001d0f5000201003200003440d1001c1340c840c88405085904c01c0000c0c0e008803d400800c01060041c1320b50031010381d5208001d4078100d4241210258601d2000001001a175007001c0200098428402c182491030240b01030310200c92400742a41d0603026041c5c0140400d03400003841c02141544076031f00d83c101c550164001d804da2420440c0300c01140c106120585460054021900d02c80c5002d1198940c2191981903800d00d030f45089040c040c0e183c44505401015114000d5032090b91250b100181c185c903007426001695400c00391030654107840700882c06000c1000c0c01c0c00010006810350f08205d4549030545003600043c0380701c460850700056640409088800d10000100c0e690343c0c00601c00e001e41c0d1020b030320b00d0800000380c82042c509246000002d0600c50801c3c400f4841c0405680080540d048050202030401aa1902 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 981449964 1250 981448714 981448723
    0x1212020706050708012103053007110d090602060a1d010501140f01030207152307050a09080606101d04020d05010518090a06090201031b0c0506060301060303091401090503 75
    0xc03c0340c0401c02850041280b5042c41e40b1016080d40409100c0000741c22665000c3c145001d40c81601011130320007451980760314a0500b22201415500c2402d8200d030419101c00b03880d01c9000950070045000710305400308042d0040010200b2507c00307500820306035640d001c0c0a0010300d280421180c00b03030700e44485c4403801d620902030f01d03000c0c0ca0b00c1c0344103e0803035280000300881b080c01a01814107250041c0301c0100417a40400c0308407180a0040303404205440002031050050b4444440702d03150301020342c240440141d00c507000d4200821184c6071444102e484079201c9a031038404490555010488031035a0b49100c0c4a24145400c079008140f007240303540c04c514000b0b41a81c205908103680540c3d1400104003600e41010541e441e8a00300e82d01c50b6044c200a00d00720746444020102030407140d01c0e5061502164400c0d4401c8254814080313065940f20200c02c8000c00c10402c40d04140d4141c407400000c6032042c501885070a0840e0351544070790b0300161502803404502c00980d00c40c2414003510320400160b9440610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 981451214 1250 981449964 981449971
    0x150403121a0316051f05070804061809060e07030b031c050d0c08040309090b0616080703030e0319230304051c0323041115071e121202070605 62
    0x80407900d4100440034180f0f0030307101c42180011a280700c4010012a1510f1075a104800f414400d250103014100303c1c03c0c0c2d02c91103160700003411818000390000e8940ea1202c180160034a110300007480d202e03036500c08401a1000742c0a21044030710154080350030b82d4001e0344000041a8060300380c400d604004284c03003d04038042c01c040c001180d130000398440c0040803849020a050303060305162915007860b4034020044049405071402d5550380d000e91281640d1a44241d42c08103800346995031404441e0301e42007240d504040c00490110b410040740b11800e400100507100184020b122006104d404450f0449207820051101914481307002030442c62600d000c1c000b148038034014402050828214040d01c22840e8004807010304262038030300c91410704010000400b5501c0e10741080d02c180742d00c448c28a020300c510344142c241e90020616142c521090400c0001c2c0000038011040c07d094507000b02100310030302d94403100003041c0d8071401c0c21814115004042c21032410003072500c0141449110f50310581100d13000e5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 981452464 1250 981451214 981451241
    0xe0a080a050c011515122705010b1c0302010506030a021f200d1103090102060106050a0e0d060f06050904080405060c160608040b0a020a02150705090d060c14070515040312 75
    0x180701c442501a00b00950341b4600d404203404000e004110b681a0207502c41c0c9480030346408038104003400600c0001d41005402040040c0b0041141e09001401c41000300c502101b01c01550074400020310a05e0302203440200c413600070b01841c0381a150104004065018007021400740098008007411507040c0d0705800d5038511240c0000d10310b00c3d00300000681000c0000c860300f0000d900c2081004400d07680811a80d045581500b0003d0315840d480d002070341c030140380614554210180441d071a0521171503401113051440002000c01403942c96200384003868408032005172140300d042004101a090290080020210b9031060b11100781d441100c41014a0442d844100000c100358240b109101f00c00041c10340002d039580003107250800d140f41c041c1d00c0e068944d01030505041c030000015040fa000300c04503001101c0050030300183d601c1d54030b4001d000700b06480c420300c0083c1c0c002c42d42c1c280032180c20f81254444c523003102c0105648540b0501c0d48541c4100200200d04209079010110101c1440c0c0c0101d02084401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 981453714 1250 981452464 981452489
    0x301090b192d0b040e0a0b07030617031b0a200a060e1309151401090e01060513020f04031e151a0d020409081c0e0a080a050c0115 57
    0x10140c0c14015a141c5881400061410b0156002c203850501e00d0710702c484000b1000443c41e5003a0350001002000d809448552a00400d90800708010170b00c1c01c994440c10040e2010070219488580301420000d0701403400640742c2c801c200034000c01a101c491420100e21860403640000c11507502e00c0600d07198610403412814001800c11250f181102d030841c0680720501d40701c42c6100c15600020060740d01c0f018280400d82e51010a1800c0c484004240960180341d902c0c1401141c00c5040700708450402441600b0714640f80907680d012308201802030100701d440050a8901e814080b0003d00c0003940101c0c0c0710b8901c02020040080081d021072030f01c11250086003c0e8000c8158242040c080b03411502d02e4560025191108005010b5045140001c00540030b80d480840e6145501c08103004000040001e0400c040102d03c05001100003030910000130701c9540300703100b8a6070b001000c030b56890b408400105a108144402614140300e4000307070604d00c02c000004510305907004110350380c80d0060f4000d010b00028 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 981454964 1250 981453714 981453751
    0x1b060c031125032009060402090111030a1706062110030c0b250c0614090a080109021207080709020c011401080102090f0312040303030e280213290301090b 68
    0x9414819298644113404030360110011500094400ca03401030000d4441c0d0341c0441c0c40542030b4468a264041000c400c070840340d0700c0d0611b070742c041e02d0072200a0701d114200c1d40c00c0300003c1031410298140c2e1400e4040468191348054140c1844540c410002c3c038102e80300c0c00089000000c19a000483c1c002018030300d0003a640c4074911320320b87e042081603c0d104009030b4030706080c02c0c00054501442c10201da5051610401c01201480c03840c00d98410300001741c3d8414070180c00412400d2041d405252040e20803500340700039880e9030350095245c504502c10403d0302d4100120802064105400030403101c0d0040d40001240303461500400030800080e00010b415030360200d01d03042c03142400c4002040043c0d00320000c0c40c400b01c181c0740241c2640700301d000040405071a035020042a620410001d18099882090070400c1c50400783c9260ba08414020164403e03640c844054500f22414480c170007030416208009525140c410340e81c910030782e80035004550150342c0ea200e074401160300d11400c00d01401150315072001051 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 981456214 1250 981454964 981454973
    0x711070b03011409090a02040c020123070f08150f0f030d03060503012910050c03030c0c0111091e012106140303031e150d0605041b060c03112503 64
    0x8030034095250044c92650f060042528001814004a07981203c010403440716480b41280945019040d102d00d80d0030011607800c100800d030240a10600441d40c44043d13140191b981100e0b5580c00307880d0850303400c0360f900d01e403001410f0030204100c020202400151011000c0408a440e08911707141880010b603950302e082c450381c5002c1c010701c002012003520030f820211031060300300000c142c40d0340740c94411284c2e9130881c0c0720781340502c5c155901c445030175098945900d0240c10741c0c481688144c3c2842e40719462301546c914184c14141c01e684a940c0054180300d44030b15683c0500c00e0800c59a40ca150600c101820300e011090403075080c0e0380407a02100c0002c10003e00d800f84034105a113010a40c03a109820a004100c590f0b80c40c00740c0744401440448c4d61011725143c2544500b40c1c460b400c0505900408403010040601840790081401a031080090402844810109510394110341c010b08001904030700c1c2c400c0200e071040ea038500040003868252a4640064110241e490711144040c007401c2002c45000c00602 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 981457464 1250 981456214 981456239
    0x30212131a060604091817030f06010804080706050a092a090e030f0706060504020d0b280b070602040e0f0105100f0f050d020909040c08010c2102030711070b0301 71
    0x204440d446240c1d6410a000065418022400b403030000701e56600c0c06000343e00e8071421601290360402e80344040b400b0b101403220100d50044460440705100b0502040c41544240e00080c4980d81100d01181030404e940d54820181a0161100507903548819058002c0750043d122010780b50300c541c5485054184250f640c00c0401400d43c00000d090f40f402030090011080441103c0c44010103140303256541d9498a4040000c050b81e80215400c1840820300c00000e070601d07840b5100a0310304841000a1b01c003e45030f0380c1407940c030340c1a0701a04048261340801613141e030140502030a034400c03040581001c0c0c465071004030820048440c215801c0d5020300401c200d0400b51101c58480d11380340791903c00c11511000241141b81d030408036000300b240001d170b080f60f81201c0364103031a9884c1d00106600031310309050402c030114060900507906154a0007266100369030080002a0349100240480c0c1d0640c509a41d5000c020740004000034148000d211050b10a400c003440a03502030b114030380440c0d40304e506100103681d00303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 981458714 1250 981457464 981457493
    0x80a030b041401080c0f0d02040c091206020405011103090310110c1f0b181b1903050601090609120206070503130312020c0a06050d110409060605041403150a050703021213 75
    0xfa8603205101d6a107a142d400f49241200e070127032001f00300c0c1480390b17108440c00e0301551f000c00320000800700d040303080042d641c00810480e40d0998401c100c1040a00d8410348034414462696859405108100d89080d4941c05c810081d484981ea0380c0e04000c001d10007a070500100c00051646040032091000c0303408814426000508401c1e5001c1c00380b148012020106c7c4000a00300060400000b18884120681141101d02000c1c80b6982c4905041c4688401b4014100c1030394100e012441100010418074402d003450000c075105017a2080390380403640c0a04c070140e070000d103094903240810002d00401a03081d040c0800218821103c0c19512000194001c0c10400035015083c803d03500414104059a480001d481110401250000381031b40d44070b40c4401d2034810740e0b100c00804d6082c40c8000400c50b070054003400450300380c00c03c5080e285569508041c0c503170b00081e026800303050011000c41c4944500e035200c40d9004240e420010f14192581c080c8600411003100d003400209000b019140411419075481c208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 981459964 1250 981458714 981458719
    0x40c02031c38041a010e190623041d060303030f01090506040f110d0e2b02010605030a06060302040c030618020702150a020d02061f03080a030b041401080c 68
    0x400d95803030340841640c81c1e010000c020b4550701480e80038000a448041501007040200304014603c034403403114010290300c00d460350200701808100100c0341444c01c1601041c030718908480d82e001d030400c2020341e441082d29000e0001070042206095410a10300c0c000c0004c3c0c841102c100d081e0070000d001c1064440740081446000750001d000740407003004030090860540d801558042602d40c5e40c031010800a00c001c00c1c492161505205c940521904c07810001d1240c502000000d209050842d00e807650746102140d200030a01307035034903940d81040c0420b04081800c07400504c0045003581ea00c1000074544001200192481d90341c4031020011850248503424035402e141c1811302c02d1610300031200d1740c9015400380d5000070342e40008500c411503450401414110a2081803d515070546030030003035070340c080c5449180c05032042d08080f806448240103191198500441c01c131168506603690039170f158000102c10024075071240b99116080d9118068218680d480380600051507140031001407608000364107850 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 981461214 1250 981459964 981459971
    0x706050f0108031303230d030507170618101502030301051c0b0411031603050319110a02010f090905040f170406050301033513050f06030f15040c02031c 67
    0x10220381401c1310b142e00f01d0b43c0043c0c0c0a01008142c0036860017078118010700300ca0f1406804400a00e06800d9408103009000f155601c0c0d200c07100c102e0244007000001c3c6d070140c1e031007685000d401c1070100340f5010456110111611450341d0603524044444644c80c04020140036800210040c4114100429140f01000b0085003448202461b0749a44000c000080e002400c046004070800c401c1e07440810400c0e56040003280f00e0483d042d600c0c140151682c200c0702c030010900a039041c5000c10644106c1031040c0f6140e07684040d00d80c03016241c0c011359002180f007244d84103229404e52300041210f0f0f648186d074440c90144000094aa071a85400b000c030454122012102401c01d11040c040541c1c00f03401d0f00c0c1529800b00400c3c0305100c550640c113410902542240351000c0c021a442c2c0740307881422018000d408402c2c240c0342c50044e240c000f0400c3d005101e424860304104103000091000300c0700d941c6941c10500d0588001d03a00151400403e003a28001c001090142c0e0001521f03001c11590380701d942c00c00f11813982d03080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 981462464 1250 981461214 981461227
    0xf020d0c0b0601110f1501240203220906080a0c080303070c03032003041a09031c0b0409020a06051b062a0d140114031204290706050f010803 62
    0x4800041d400350076141040080f80341036020300340030820104812003d0089950303401d500400a0580e0209000d071101ca9550300700b80440f01503c02400c0e071684180c680146041419a4048a4105102040341d54483c0f80700c10000503441d041303101d280c014bc0100740c094030420031181441d201c000d07074651241050b0342c410420010a036501c40034612569900d8030380407540400040e01c44010401d030340c6d151102048000188400c00c14803401c9030721035958030540c001450b40c80d085401c0e140d0240490365a81da00030850b802c40ca02ca80c690101a0441009200040e8904542c02007000c59101e90855800310340006181440c900304d88071804c00b40d10603c0c0040565207044428403007000541301600c103420040c0c4101c0c0a243e505d40e400d84204084007002084402c42901514a120001307201e441c070072840a150411260134041107001d04944c5000803180340a14191284001442d494a4000c0701000301e010342e45075030105401004014001c08011805017814900c500b5080010707404425264400c2004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 981463714 1250 981462464 981462473
    0x706061a041424070c08120903120c030d0f1e0c03060806060d080a0504150302190c2d02060c0703030201060509040c140a090c021b12190f0807030f020d0c 68
    0x80b581025100594142c5480c400d15040c1c009110302c6d001000d080c000ca000c004545400c0c0009410302c800c0450031500c0141d0416000d01a51050020360b4a0f10780040108002011040c0c0010344c0101c107020001404e070401815400d030700c65219101881554032801c0c00c1c92410b42c54040c92002c3c040c0540644058140240001e0110081a01c014a0440c011401480c040e000d070013520010000d0b109c00c803030b500e440601c00800a500c100c203420407108445001c0c2c511a4130038452547d006501c181510000030400d80a100d02c83d01400c0420032a11710741c0820320044c0c4915000d028a4210b448c000c145103070031442c02a09498181c0c0003240900214401c020119446090b064119116514100d0030380344100c001c90071102c0150046406035050840d900302c5035a001402e009240108407007034400e60142130030042c0014a40c600381886902804081080700000d61034024031520440c2c10310314162403566007880740c2e00302d110709070b012409155002640d1074040c040c2403106070140c40c0003030b0707031124581d03c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 981464964 1250 981463714 981463759
    0xc09060307121509022106011a1b071d0603060601020604021008070309120c050c060a0f050f04090908030a23010e100801050a1d0f0c060706061a0414 66
    0x1010b40b04a40740c4040b03481c1070030f042d4002059650003402c4801d0b0418284500100c081030110020224800c6500005d203c04004241d0f2410a850031003140c40c0c030101d40c4a010300440c6158070303000c885c0101e82c8000f8080c0c0000107268001031804c0e60074462480e02030109402d0100050230181550840d42c2004010b84d6616120b809461145c10605460f45400100310b00070031102d40c0c024528400c075011201c83d10307000b0f004480c0c0309204008807100600ca001c14000c0a00440c560103011400001010228501031800f9081150040c2c100e58202a40c0c0d4088101780c0c0d031803100984078660700005200c85080c030341c0030324440c02198443d1000058030310114400350800c14802d900740003003a003020031380e143c604d091203800034940c4500074442424050070004c01860000c05144540408954500d261000480c00d0f60901045034040e2038241003203420b02c4401e90003698102c4110782e0b1001d01140c5205d001442460000e45260625111420105070407510385145138024803541c40107407441c03031058031140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 981466214 1250 981464964 981464999
    0x150501090b0318070617090a12050a030b0301051005010809070b042610150e0105030d080613152c16030209031b1903081e0d0e0c09060307 61
    0x1c0d51aa5a5a1000c070f1148011040010070503460082103400203140b0f600c50340c11011710300d8640380640503440310010307036544041050b0018801c19039054000300755805480a00403030100d904010171078268550029085500c200c4025001c0010440103101c556400b01c180703a0300044c80401070041d0f0741485650240c6018501c10380590380680601c1c403010310720058008000b114040100c450310080000c904000c0c000e1903101c07031807210035001e000400741d041840b564106c03100580a05030020380854101d0790003500401032030300030640120300c90700c00e101c0b1711544420f64680c4d0000070246003040240d1b5100d0400103000c01800070220b410031407201b44005400d411207910305441c244414100c10683c06400380188050741030107540c0102541d100c8540e50024049004c0701c1d4091030150700540490b240b6640d000250a40d4001c1c490625680d12400508907114100081d50b4281402480c03024156406c052000c1e52903040704003170b0002070402036200d541100d022006840c80d182080b054424844005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 981467464 1250 981466214 981466229
    0x60f010b070809040f090b0a292806050403060b060304020144180a0c290406050c1b03030d050604060510170f010f03150e0f0a020415050109 62
    0x990543d90f507840d5070042000490000060105241509100d51811404c407200070100d0705000302020a81e0518064124117504414608007203001d600610000000707a40d40120b501e10032400c02014249400c0345030004103007030b54906a40d6415850010f003074401c80340610780941418004d2100503a045202c50301b145102c0c0300e1030149841111440b0300a00017203030910080080121028000714040305a192044c0c0010b0704121446010103841540c40030240c07000342040740341c2142441104079882421110098402c40000003000409110540d6482a40a5004204000b4105550300001e00c1029071480a06010714680c0603080003003500e03881009413807000136a80d00d00080700d6986650241c4003501024240702d100b240d0750b24000d0f08204441c10b50f02005007413800014580e005125074a4140c8404200701203020f46107642d11203410505502c07038810310342c0b9107070354000c601f81c10007501c15002084402080e4074912401484110780754a560380507040603680052203107980040e0841e0454051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 981468714 1250 981467464 981467467
    0x1050c07090c02010e121819330f020d1b060603030302070b100305120d0e0a030806210c0d031e091d040b04030806040e06010e040302060f010b0708 65
    0x251019410268580c0004031040d2909696000300d0341d0551000a00520803022904403401180340c002240c00303014202000300304402c0303a000d000d0500d03100c903452443c5009801040d0544600326080746210b0300c1c3e02d8802404490000742135081002c071506100d2001c0381454198022800320080d114002e11200c1400e012800c1d003041035440080100a0340030b50840340030042c440d184d1600030060f500c41002a200c004802e40480e4049480601107400c50364008000c04c2550b0703540c5a200501d8116800032200320f50ba030905010921828000501c039148a030b5100703071040c5030000070892004181025140a161a10f178a4081301e54002580d062400d001c90f0b242485103107130314007181e01000340604050030b01c61491101400300c1e00700310044140c0c0c0600800300d060b03100c00380110301c500c82c1c00c40c0c014080021140204000c2800f40800c4c581040c00948041101d9802c582068505802030f4010034411801c10200301c14540c1c1884925006421840c552241c0d5261132000600c034040ca00c0050b041d03020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 981469964 1250 981468714 981468727
    0x60309070f031202070b0301080a030e06040b0d060302030d0c0f171c0c0e04092105040812030103022718012705010605100512090c041103090c04050705090105 70
    0x10108050300050030009408903405032a0f1400c0c0742c604080340b000f4805172040050120b0300060386801c1d00d041e690702c00d0040c46103065603201100c40c400c6011040b90031100400020034640f24500041c000c10200d110040390451440c418146030403514041c0c4410010030000702400a40c28400f9403840503004841c080302440001070561445c424042c0140c110507a0002180502140c0e400030301401c0e00b40e8442c607041d050910180000d480300d084005000682c032848640010741c550f051646101034601e485030820307032103c4c00c2d01d103000180c3c040240301e5513003c0010400c40c908100601e038071418032000c030408021000304524030b06d20040c10f2400c4a03000c40c20f00d0000b50000354040072821b03910169019405941030980e004801401c2c005035425402d011000c202c0341496804c1001001e5140c1e0765a142c224202c560100401003d0b2640015000300b0001882942e03450080140284a039102d8035540c3c20310300c034071900e4145085007a0380290306020801000907001000c0d0344a00e5003e0900f5581d03283c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 981471214 1250 981469964 981469981
    0x9150d14070f0206070206130b100902041e1436040b070e01020105150105130503030c01020a091202030316060e1f0606090509011707180b040c0c110603 67
    0x8092414034250110401004012548030003411041c140d10f4080e10360300d48440500700d844400464208005d09002100500010100c41555034010740b48140c80c496142c8600c00d560580e4055401703403078600c4a0050318041031000030510401400c1d0a070000302a0302e80c0b03901044032003881d603154015180c0304011550105410301c604845890541845149900d00346c038020f1160310058030311900040c0340c0e0710050305550052182c02d0107494500196001e00307207804c00445030b55101c0141409564500c440005198601300701402840700b041001507140c01c03c1c528010944115540002c00320320000c111100542c4010084465070941141036603014001400c2100183c112001420b6441c802d4074600b450010a045001d00542c98292050000541c2c0703101c12500b4107514060181c0c05030181004103e005800c001404980d4118015500015542c0d8981020b0717102000784c00c0300c1a6158119820540b910344104000c0d50035900388111080f505444091130140342c1020035015040c000081003141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 981472464 1250 981471214 981471221
    0x6020a120204091d0604030c1101050d050c0a0305070c080306010302030604230117010b150d0e16061b0503030f18011130040f080d022d09150d 63
    0x85111801d550342c1e6642c5120b48010169000000b900804001c07000c0028640810100e01850301035440c203440c884140c41e03184000b80030340021814802d08000c2100b07495050f0003690300c14100e8800c8140c403000070010103070035a480240300104000010a078800000c3c000740a89070424028a001601d980c0d44030046402440911005691036000c02484045100d0619490b410f0342c01004070200600d01c0042c00301d080e2104224250340c004600300501080b0300300b10300a0000d1001c13103180030440b608680800c6003024800e2030154400c400c02c05051005a411000e10b1860b4605114690781c5c411032900d4203901c038000548520442550100410020340c100c00742060071502c00740003040300c24500180c0f00d54650100e801040c0344019010801e0341c6c1502800c640070758103034949e00012941d950740d0390701d030808641c3c1c1c80448090070240403510241d0781038405010903501381252445140926a41d16600c03d180b907410002c2e013a01000b2010345c50700e83c9021034140400703507500680c807869a500d07000046c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 981473714 1250 981472464 981472487
    0x6030109150b0f09160c0f060615080106050f03070804061d07030c080a0c033c02040f0b01020c0f01231e1e03060103090c03060f0b04061206020a 64
    0x4440e4500300740400390301c00d07802141c2c00c400880c1d04610240203801440801c0504498221010a260064007041c5000307149441c0d00382d20464058041e48040d5894008441890304035408034500c100082c1081034000c001c2030301400990400c1410700404d0204010b2038400103004104004200000c9030400030180c11141c03541c00a200e41040c440c8010750326036540c1e01544003d80f2884030031400006c00c502c0201d042c89140d5002544034403440c5c00c54a8842c003400c1c00003040d001c040d41c5a000140303001603259042259001000701d80c1100c3e8000d00400007642e00c031554503030307115140c00d000c805140c5c5c00090380841800c06640c0c880c404091680180c9803259840158681846540c06203128040000c0003880207550b00d00c0701d034040180c00428403159004050b600c4440c0248100b615084481500180d9070050301450045007420840d40e915003444803d40c401c888060300c82c1b0455101c1102d0303000700c0980b4541520704004851501859235000e100382e500184c061a800141d901c0c460780708017030540d80d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 981474820 1106 981473714 981473723
    0xf0b19020909070c0c08030a022a01020a12050403050102030c041a04031707060b182d0a1104080609160605121821070b01121a06030109 60
    0x7030710404a01c05480d90054044001600c120400080c988840710764041c0c02d455003001c1607801c447c030b0010403804070389803056031854ac0da90b0b002529000041d0401c503865072400ba404020781e043c1c030564101a14650002040201d000b203942c00034421180f0f035001081d4000803e4000c80001e00540c000146801c0d114903900f061403e480000d40b804a005010024100e013842d4001180000145c400070000d540550801813040c12440303801c055003031181070b0a6004107602c921528410340040ca100046941d8001c0d241070060004262001b90107240c04956060500038440c0c0c0d541c020309006011030455044001c6400751054064582036518054031388a81d1303d60b0b24040c04c2c400f01c00741c5885820b228203445006804524803041d0201040c290400342c0e03601d40d9090842480710140c02014038072220810300c40020301c950008030303c5107903c3d0002001c541c465000107805403400040140 = true := by decide +kernel

theorem cover : BRFrame.Cov 981294964 981474820 := by
  have h0 := BRFrame.cov_init 981294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 981294964 ≤ n) (h2 : n < 981474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
