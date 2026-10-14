-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0645
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:54:56.823835+00:00
-- url     : https://prove2.me/submissions/55640abf-81fb-49a2-9819-b6658a6aab9c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 115827338 ≤ n < 116007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 115828588 1250 115827338 115827367
    0x50607170a09050c0405190e01020306030d05070c092c0607090506070f020a030303060510090b030711191b12051e0304090501080c0103050a051303140c01021b12 71
    0x140107069030400240361109080150816101021032644a4035103c2000f11081d030008007004540c004c92410003202190003081400c0b07102c19076401780e0541c4107003070303c800700d6201d4001040010f204241c0c208a041c0c1c4c503400442603485c04020402d04908a40784800440701041c0c035420004800c1c0020800c1c2d09001c6005410500e140c05407a0046a00051040911107210923440169034084c000c00d40fa41c1d6a41001002840c181c05864401c1142160004d4035502c90400d031001c1c1c42c4040c40c0a03165844005003942d0b0b207420690b070710109000e2a802240403210002c000c09041780070b00714507d140d200041c0512014505504003850301d2154044203000f0460005094002e000c2c03120500c0700400b0381aa0461071801140d214590302400c1800108543c5400f1940442440007a2000e04c590349800c298103042e10400c83d10288100d0020207201e000c6071207030403aa01c18140f8450110f150144c0b00f00f00c070b426a4440c40c4401c14050701d11807481011102041800104000364821605200d0719003003050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 115829838 1250 115828588 115828591
    0x30c0601050f060a0f051e040e0702070f1512060506120405011b020304090e0c1c030206060a18050406061d100b040308030a0c0203041212020d09051302030406090503120405060717 79
    0x1003004001f0895200542d01c0c044d0703241000c1c9402490a407640e5507030341c10890050080303510341c0060107401800076402c104011804282c540c403010184603a8001d20701112841d01185c20410f0160315090001a29150007000b480840c070f50003840358261925042c0142541da00c5407012150001400d01c440034140d021081d541690701c0d800d00819030380141e044003464209603503c030300d52240c120002220500b8030004403840562194003681d0326542c0b00420485009568454104086294002c801d10b83c115680801d9000d88240c03800200d030f88d101c0c0100080c0086503407a0701741c1c440045041c01051804151400010b18010041614260866032804141c0c0009462096011388410a0001300e40c020f0098138041d00005600c481400000d0501c0a52500d00b01c4c203250140c000c074034011581e07078451203224083e20800740c0b5100d03000400000a8000758801002543c505584111141c0051000e00041c054200c6082042c9000e08040c241942040700207060002030042c4c6049141c005620342e0843d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 115831088 1250 115829838 115829867
    0xf0f060b0c0a152a0f0504180c020106031203091e0809010503070e13020406030b010905010f05070f080304051c171303050919090c020a020a090b0a08030c0601050f060a 74
    0x4a0f00f040150307208801805801501000b1911600402c01c041301c98000d11844442031550b9440d903402401d441612188218042d01c980d030f80080c410f500c001c8600340c22401c1d991078107200001d5241e41e03035228034800d84400c4101c840080e03118042c5a0a000341c540c0800307242c0d134543c2e08030714411080f96a810700c03921030030a585050140202c0056442d50003510340580644026014071400014000321000a501c117004520120f4a0070080b207089503c01c601301c0c400d4440c107840e010b100c0c00d0032590584141d040b500b4100c132544c2808000d0400160044041c5004600c114020041044880508480d1008180c0c641c410441c0c0310074904c031804103040b103403500040c003902c0550301c402d02410111010b20409200980101c42e020002542c0d01600c5030701000c845070b1600800c48505d00600498440030f001e0006540110380c0f040c14410405590f00842c0c00c3d403002414508161307561078a150035a0000480200b0507004000104581d040205251101c40c0f021282d4510b08031054002600f440c4201461 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 115832338 1250 115831088 115831103
    0x80c060a0c02060f04031b140a05012106140a060c0305070f030306030b0f0403180602100c05130308030610050418110d1a0f150f0904020d0f0f060b0c0a 67
    0x10390641d1185011a060f13041c044d45003a96680e145c0c184401188054000003484079500c40c40001e40c2d054040d803001810300020028512180b8040044604c90001051201c00340340d41c9140c1074404020f40708850003400d036079281c4952410340320100020385032960302c50018003030b42c1c0c5038003800240c0c40800c0300c00803648000d07042044945420210300401e02e64100070850714200c002c0c1b001104400f01e8030340c49544203655008050400f540000302170741480c0318000c00369220221190955035030b60001a40d40c4860b1030450304060341c0c83e10800f00550700341c1c410794050b000003003445803034101050b40c24250b1190342403140c6002d2520700a5842d524111190605083e652076600418554203402c88003500c030308010500c42d03450003904040c4010b014100c00c91046182d882c0006140c1088890b11a101c9903501c3d203142030940002c00405143d020b8040d05601550811140c050340c02980b00341514214110400101d103100810140101c0e489a0007800b583c1c03005010004240d00001070302246541c1c071040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 115833588 1250 115832338 115832357
    0x4050109121a04030e03070b0c1002070515070c060f02130e0403030609020c1e060c03040b13020307150f090503070501050d0609020304030c0201020d0e01020a030f0c0605070e0a080c060a 82
    0x6000e490034070070100c00c40398407240301c0c140f00925a005012007030860086041d0b94051350349401d030400034400c6020301800c50708050740e2610380d40c0786a40a4521b45003d8015549030041800c80d48140c50000c4862002007488910420180083ca21403485400e0180004618001d1450318003804c0c01030620402d50740190a000240805200b504500c0041500d440e040d515580008001600c0351007c3d100d12946410a00c0e500080140004500b8080d190840043e407450f2140d0702e0340c60a030400205003441d40c00c640c0b1030344401a20204007420080420f42a400d001608003000140724203240001482000000a0240000da4011a0b44021a81c090a0143d40c440c07002d0103010250a0030351010300c1d80351020081200785900a46034050462003642510b885800d40c501c142c3c0c00c40164008103005030300c41c1a44030000384c028080e03401d0203801402d00e40e001e035407103503140e4090340d0f0119109000038503c140b0403201400c0c00e88031407015040715005000115420804100307171340246402a41041326a94 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 115834838 1250 115833588 115833593
    0x703080130030215040c17060105060706090203120309010213080604020120100e07050102012a050313020306040c03110a06051c02040b030f040209160503070e03160f0305060c0405010912 82
    0x4142c0c004201300e0a102800ea241504101001d001c43c0e2140a03000c0380b0714401600400800f040250503a0001802e442c00c1c0005074075801d009001241040383c040c403a2004070786101c00c151000c0d510a0901000140e640d640d800300390140204a64000011a404042484010303a00241c400c0211040004940403103120000182e103011102521014118584403901a54007008981ca00990f0421380080c0141e041e000400103e0b01c440360182e010203104a940e002d01030740b00780021600100d40d80c15241010500e0b0b0000b81c1005000d64080b103000c0f102070300800810003181e8902c07603d00740885240048615022003d04544210b219551000c803481800841c0910310350305540180400c544260b0300c0c1c2c54401c0781d03c01e02c41d07401e44040c1e114032502000506640705400c1500c0c40d0340030603501c403411070301d80f54802d13144110a4140c1c9a0315002d49000700040c0c4044030700c4d45004041040c001d005c0c0d14514180103050440140074003c428a00f00300c00d129036600302000c0b00403144010301d6144111941e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 115836088 1250 115834838 115834843
    0x8101404060c1e0512070806180702160b12151e0607050703030522050a0b030709090c030b0f0406081f1103070e030f010c090501030e0a0506070507030801300302 71
    0x1c040c035201480074007003a00e41d084d0b010000e0209003842c1041e442440d1200700d81a51105000c0740c0003940034281c184004500c0840e441450b80000c02401140c0700100c108007452116101500107080c0880e000c95440c800c400c2003040543c000403c081d00700d041098540116040304c000d0f0b024983d0501d0b01624440d12078031a201103a500580100a80e00000c1e164980140b4a501a2074070312100c40c0045480250010b051046104032035008241134806031030100015443e40004061005009100300f00080380101806080201d10716a0340000c1e4004a00c2c0070851b0300c0e42034102050060307240400034040c1480000304000203400c0309258101c045e00d00c0505402030044244da003006c4c038201105101030250012641440d0b071900b142910300e03038124437014500b00c1d240500307504002141080300300060350180c1e02c20f080b07603a80b100030f07140d540495455152410505682800005e00001150f0f001e00d0361102e40c4602520481c26003948010300f84d406050b100314220030b0382950329024400c40c01050f008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 115837338 1250 115836088 115836107
    0x1b080114010224010302030d0f1e030e160501200a02060702030f03070b0105010806191a04080304030804030b0907060903030311070b090a05010509010605210106051908101404060c 79
    0x68410b40344414030000f0203e4512100b032200301c1c000e100c0c0640e12109540103241c1040340264aa4902c64002108445a5007a40c001c07240d01c020b140da240c1c5081d400c9402030200c00b00a4000130381da8044a450a40010b011103c11044400e41c0c090400f4099802000460781c210440c0d0110340c030b141c50310300d039000013802c008000321841903601c0002900c5007000700b6140701a040365000d8990799801d907a18030070720801452440c01c5084100c80c110040c070140510f040e50640c1e000c5060142c609207034540030214519801504140e45c8080c000c0340c1001001034a0500d40d0348038025002074910380f85050300240045000f40001410f06427200c0700c0b0340c440b2050400707980000c0c2c0c002d1004842814038480031038840c505c100c025203141d400c0000180b80c103141405103204880c00030384021221410300341c0c005000441c640c400c2400b55200c4000040980d02c0c018000c400d52182c0755640c4440d0b2926558611b0306c0075201212144505014070300781c40854452a4507031043d040140817440da04d80900c1264400304 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 115838588 1250 115837338 115837363
    0x20111030114040b040b0306063304090501060504080601061202070c09050411040203090c011b060219020d0c1a06030109020a060201020a0206100b1e0906041203031b0801140102 78
    0x2404000014042500d1a203000203541c2990100140d400e05024082a0b82009000316015484900801c00390b00f040201280c62211b84140780c102e03040d103004502d080e05902035034154071080128003030010f207141d4801c841c010803207414101c2ca0507241501840c0c4443c01481140c00b07002d1070540480c0700c421345804880c3c2050b13102010412007519040c08800404056406440002150780780943c10308080c030851b8000e5840000501c50343c80b0940044881280c880034020300ac85e00e086110700041c100d80060405025880003180c1c110405030002450141d1103c2000200014a4124408180f110040d0a442103250b011800103175246808a0b02411415030029007000180600190307099065020b8510324183e81e0a903010394039044205500c01170503004060700c6907001c11800d40006911012610b8011000d502e580c14070408000081c21600268001d9042d07118442c0070100701580740c8143c1105086608000101c50501080181070743c0050040d00f10b1048000885282c6138000c0001c6400e402c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 115839838 1250 115838588 115838621
    0xe030304050d05131e090b0103061404110c0a030215070c0b010b0306120d0e150708040b03040f0c030809091f031e02040504150507020f060402090a0e03030403020a050c03070807090207030201 84
    0x34040e0580c001c01c54581b240d10030103403801b000020550700c02d005083c112581c070840c0303602c00d101000412004081c1c40c0342d5440250400c01080c034000c181070069550007070098020340300e0000e1010351039800003c010705020800003107a0340000000e603404002415034510714402c949980d59a03002c12400000303d030103002188180f14041c0c06569010070183c08071181503546540300482d80541d0b040501400318002e11005042c401070100e0070100c00515886406848002114125034a810b117501a0301e401c19280180005448102d500f482944540c21005c01c030380c848006400c0c10284103030100180401400c20080d03100310000c02480c10108038881d0b80040041100c1d050604e4200880107020310300300703421420304000038032090000c250007102003201400f0700026940c030350030401c1c5550010488080c040d9500c01c040c01c1c0d1141000a948031314801d400074180f203202c5040c003e2501c0403520140c1d110794441c071014002c5e41c00c0400c000c400c8445000c40543c84045600e0281d0160000e901480800d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 115841088 1250 115839838 115839869
    0x30908040b03150a1e1503060302060409050604140108190201030f02040f05040608060603070308070206070f050607080a05010b07020409150e0d080615030c0901090305011e0e030304050d0513 84
    0x10720220f200c0310104642200c06096083c0da4690b6907045010082e10f8244411801c1402c020140c44d00201c681100814940007170001e40b242c0c00590f2a400681150014aa444c82000751604103441090110002402d0000c072540c0b50000c003558891150192580402c00404800116400381d0024040c00464100554440b601c52504041890b00341c410944100d0404c000002d490b0008240c060103803070050050940c140c21616840c0d096401130004903088601080414040743e41c0c01141c0368010712404c0600075038100188020311400c1c01a248030241c1e460080100301c03903040074045480c000c0c0d069401003845009030500c112610301d03000e241c0c60319600b00400c8108240010079076046445454035102d00301d072580c1c814021640154a04030060303500400100d100c0042550151404400c140f5091140315140e550350307420344801800398080300042c0007440e5101c1c01c86001d48608203a01000950440c50b081c0c50f082d581d00c0030b924843c82070280000d042102040d41d00e1908000d0081c26812f07800300d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 115842338 1250 115841088 115841101
    0x1806050609060f040f151e0b280c0b0c0706050f01260f010e06072a03030b030307060c1806080421090305060709031101020606130527030705061b0406030908040b03 72
    0x1913104407d00c030890454500808a400d403030407020744110784800d106c444c441c1461b00e03c0c003c0e056103848100c002409480d846880000b080d04040074454500b8100040d2106400d10300441540c6e0f000d0842241c40c40c407074005000d03920741c5007a030100c41140e05000d5590030b95001003044c2886000044003e0039401e0400c14003960400003100d60080013940c0d80c0c0200b804d680308040c0401c100ba181004c3c1c0c904100346c00078020a01c44c1d0072001c4402001400d61785002c0450740e52104940b2402488000b08120400c90b05d1610100c000c410004c2000303041c80c119a107800d50764024034084045040c0c010101c01c1500c06a00c40c818039820b80907540c44000c0720420705240c080a03003c45602c0c802260f502c0c904c0011074403103510208001d40140702c0908080c0d6000b40980b2040c0250100030441100c0c0c28051020f25040520b02c246031030b4000800019607941c80440c02c1c65420148018400b140d0380b0040c04003601030784010000c40d01220354600d00064245030300c0c60040410f01c900d0340701c00354459020003072001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 115843588 1250 115842338 115842359
    0x150317070308071b0213020f0c37080c01110414130b010e0907030e030d0b19050a030803040f0f051624050309010f1806050609060f040f15 61
    0x4250703000703484000da00d40d20114121000443c5600360041d09425160040050a0100100488048070040503003071810944509400380c0101c02e1060035980060301103c1032a0344015200080a0f002021005d078503089440741c00d0f914002c8c90000d203584c0d4009455030007000c0070343c030103190b214407040703195030740c07681c2c2d80880c20480344240c0d143d44190201c00784444406100d04c150f105460301a1038042c0703c0000b2600300914520028030040c1815100c2d0508041101c05000908610b4811200001c2a12810080c01041c221030410800d004804002c14030445c1d0322048038100720381d401004030b56030b80d91301d00d030050741e42c10740c800c0c010078110503d0010001c04c0408141d0754090a00310009808180c0d4600000901001c005600300c192244400917031745d054880c0d00190342c0403082d6400441c44140c2090ba0304104d42c556008015004100c21814003040218050580c010108642403013060070010005520007000e9a501841640e44200c506040c80ea07a4000781d11041c0c10060000045554803034882 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 115844838 1250 115843588 115843597
    0x40902030f070f151d0109032103060b0a020a1205070b04060504020306060a0510030e0114010306020714060411042309060604060909080a0f12091208010902070510150317 75
    0xd08844580c20104d095014a11103034150041eaa4481484000501c0c0b2100410340300b00c549410040b16400120114404402c240301c00e2000740074130740c414440f04100404903031381904001e070841c80130402546ca10f41d0028404406a4010403007078140720a0b000240c805215150004144c044070804010611200b64010307445030b4000e805568069032800108642a0324600410b540a82c08280c0324000900c244d0102c0d084801c107600000c0c0130070f910030039602040c070b090f80110740c40c41e00014071004102d1a1a100e00a00c01c44d040102000e003002da4420f5040314800352440e0040e07950303903000340d40040b078003d59880141e21554401c0300c038100444010b403500000c481c550301071820504002074180b0944144100582c0001d403042c10001c001d5401c640910309400400708010085d051190090024403c008005215038003042d41c08070a200003174013036003059102081140c411b00c0080041540440c1c1c4480200c20400c00145801c4051220252140d0030741002c0c0c00c0c42e07050182c40c00070918180061 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 115846088 1250 115844838 115844849
    0x50a05040c060c1a100902030f07020d11060105090a0b040507020a03110c010c0204050a2009011e0206150a180f060506090307030311030d020c160501030e0309060702040902030f07 79
    0x2011030300c072201030f01d4400e02c62030010814080c410890070700345036210582c0d41040c0c1d152010445243d80d03c200c0070998100752102a01c4a0700c4405022885404004400074106141007200c00038140740040c0340c50300300511407135020b050000d0001c1c1021500e40d200450740b2100074000c000b01e00340b50400039521840c110003207000c00c20030107910b1100540050038682d5254142d640c0c0511810550a210240002911001318162501c107001003aa82e6000c9440c007803105654040c1d210030140300018800ca40d603194119015440b4a500308451341d01084c09039000300c00240c0482c00c44022008201000003551040280c409440c0e07201c0900c040a030410114960140c01c14404180c0b240c0420405126181c000c56140c6d200d8001000064000d14190160017600381c01d59003480300826940080c1c3c3e104002c0482985c02500c00300c204400c071407000c6400b508007072a003002155180105255030707106010301e0500c82d40c0d010a90400315504c3c3e42100d0b60841d40a020b440c1c840c0e03606103c6503581d08403401791 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 115847338 1250 115846088 115846103
    0x309100201050c090d0203030702100c170906121e01180501080c010e01180b07060b011214060118081002040e070e030d35010501170f07050c0709050a0504 68
    0x200000910500440e4081d0505011551800c1100c400700582c940d448402207070180014002c0d0000342c1e50350818543e1680c41030700d8194042501d450010076040c0c007a0040440840280318203c902d4454800381d0707084201307143c00b024480d1900600344001e01d42c1c103101031300040419400030030a81465850b20304118034281051185980390351134a9164041c102c1c80d07034000f999040000300781d036100f02c40800b180c0c24402c8445050b581c4410420b9010360010405a949a80b0340e410440256449543e50005e4407194608200518880c8102e19860344050000350411510148413024614140c03601001032255004580891703501c020360002941051003810040756104000075440d034003881c451022008014090944021391240660b0303c4d80c0355030002c01411b2042461900c0245903c03041040030700c01e031080b44100c0d6141030001002520004107100b0111820424040c071000b140b17800c55000310740c03410310580b03810180e03920078908405071b409114400d040c1028004056817682c070440c0143d010300c61 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 115848588 1250 115847338 115847359
    0x30a150b010908030a0309141623130209030708061501020606060a080406021b011a04050114031c020c060d141015030b011806080a050604110703030b03010612050309 73
    0x649129002e80700e9510107400810030356603020f100b5070012688520031a400c5100c7c00041c860b05182503c0c88a40c445c654626150070b010302e240011100301c02810a5031130110418009001c200c1e17021003000000324440d0046000b071040c0d9001d000c81409414100226034035880c0005100000d02205082180903008520101c1e0b06400c1c200708480001035107484040441d1255031b100c000071352058483c48401e40c070740e840e5024041420b001d4640c40d504002180307000280c03200b00700401c858040e1f0000d150012180c0c0c10804a440202d280c01c803080742900d070240c04010f120426410a99101c0e4440e510510005d500c20000c00d065210109421110140d0030890b0340c1c10346483d20054071401050bd00c0c140c000c4020010038440d030804071880340103160070b00c0c80d000c0e0745154410303480264010401007403000d0104405419180b141c10343c4850b046400384800b0a00d80c1000f1200d20030303070b00041c04068940c4013107101c685003504008010091020100c51000719800c28079226040030948500c60300c40c103403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 115849838 1250 115848588 115848611
    0x70201050708040f03090b0d020c0c010f02070504020306040207081303050c010e0109050d0c2301030f0b1f05070c0b1b0105010305071701110d1509020304050a06050603010209030a15 80
    0x204891107a2426240c00c40e068442c1d07203a46442600708801281005100e00b00800d001c810034019158110714464051707195190b82200500b028844503c5504201d81034600981c516400906401120360a55005a81391034103030205001c1e206800000e850f540340004c07a0483c1340700b03026000c4102c9001d0300030f840c0f00f1805000111070040031440c0180c00250079400a0295203003003400c0c2c201c42885440f41e031841a40d01da505032410381d038001201d02001c01c44201c3c4a8156013501949240c654000810001c4001d40c0300000c8415030010500e880405110b1600d0710414050002c803241d45801100a804c015541d50720720314945c0c0010748a01c04207000ca40401d4550105016081c140c070b81c8103014010f01d40c1010a4110035000755030105002e5900c8a03403850b00c1c0c024003001010404000f220200e0500f4046105101c00b01440d0f110394105841003041002080c4041440390400b64480e00c04665515804002400f9004200c1c4180e8940243d003030041c204010320032007600f40e4024403002d0020038982c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 115851088 1250 115849838 115849841
    0x60908070e040804030b0603190803060a0b0309030304060e1e01051e060a0b030901090605090601030b06180f10030b070810050a08060f090115030b061f021e070503010c1205070201 79
    0xb5140100003580a1005000046801c1c20181d13100c940a821140c0f244043c1c1d06104100401410664000c0c10020500036141081d240326070280c070b0320300001d07031441c1094108a580c9210040c0302808890751101040d005000612a45009144120001c4600c8615020841c000c2c0800d854881c44075904101100c40c8004000c101403107a40c0051904490070324080048019500c0201191070a5594410301000110300e885001e014041000080c07004d03604618114041400c054041d87c82107026840105000c0454030100741c3c0080310900f070180580b14040c04000ac2e4105400c000e011465403410411540e03484030f4440e00c50192380c01041c40d071564900c03c0c800e1201550040000c10f4202400190005c5c8641c0c0006400c40008000010f80f100300840009101005410440d8040c219200b84030303031803070204d008007014245075a422502c408680d00181d6100c0c0d0212091800702030043d26101903040c00d0280d00000c00e400b600034031282d071074024008c003500b02c8840660400392400c0e0204281307a105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 115852338 1250 115851088 115851091
    0x509070f03030f1103300603060f01030314120a020901031a0d030507021203040f14031605010c03031e0213090c0c02010c060b100f0e09040203100e01020d06060908070e 74
    0x55103d150040d080307000101c98002e03000125a4003840200020303d0712032618600700c030080e0f8070070a078180031505e00b02d0035a02d194006010688070b60722030b10a100a40f14032403212030440b80c0c1418a5007000102860f084d442c0e02034018400103200c0d401041100e125240c1e0000d04002000340e0b0108040c068500b4403007816946042801c1d00003001c00c4d01a00003034001c0c4c0c000c00b101030004140c40304002914040c28559441a0841c0b8035810b41280c04003c00071100140b805035140450207886001c1d645040c03001c107007403584123650410130302114000604d40264440c48108807060004044010000f030303010060351200480340c8403131103023000000705d800b0b00d40325840421007103a80300c0714030f007100b6001150080e90700c01003503030003a40d942c0b8050119543c10800e60041c5140b034a40901c51900e2880c04ed05403101020700a0103409044d080100595001c2104001000440300000c3c0178810140c4c44c500a00585080071603103850310102003101d80d0403000314011030b44400105e55404c1d84801c001c4000304030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 115853588 1250 115852338 115852343
    0xf0501092d020a03090c06050a1404080309010c1109041b0902031005040504021c050604031b05072615060a0b1602130209030313030b0a0207170c0a05100509070f03 72
    0xc0000907000d800c0c0690020b01d0700848524011507015880c0d00c424151400980c89036005c20300009890060340d8000400701d5007274049068040c1007a140074190b503100e101c0c0144c4141005104101c6604005100100c60318072a00984020841d28103444c0007019492090900c1d10720000d5980c0c00240e008060007100c1c4200454042c41102d43e15145c14000a058090310807a48081f203000003a00c0c1000002540c200c26004000801050420f4103001c0c110419030090b1200040b000141c80b800324200080b0002110000c1c418076042c1ca2a0540c007180d4004600c15a000900a0520b44a0502d0203101114000c240c101d52032031806554240c0b0328070903c55481107116401010104801510303040305148005103240c0745c05840d140400d03000070700710350102d1840d424591404006005204904001550100343c01c10300718504011074892908d0103070301c0500c101e05c40c81d0010340385d180004240315441341e00381e004044600e20f0400c0d40980340a0181242d09010b24806ca010020b1141d883c99609412240c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 115854838 1250 115853588 115853651
    0x250611070c09050915040305120c09090f07030b0301020c071d040b1308041706090f06010609030212030f04170d14090603070306080304080a050f0c06091002070503010f050109 77
    0x103260260034005020f005141403010700070301c0a103141d01c0e00410001131003603211ba44d0355513a580340907504400e210800b070018604188144059166901c40e4070480e0b401200010020046645002c07044016241c9000f1903a01940041800c0c1c2107000001044000e4400740030344007803490402c425010301c102c4100c6000d401c038013591010500d42a0707015840c19070301d4000c56525140580b00c12400500084191640403541e01420030084c0c0c1c030a091081c00d100034410405031005500d040f0f4000c00c0c140c903900000e81b00d00340380d4004d044001e4040048480400500855544459031902c0d10103640681440964950282e140424021842002d503004c032605540f0100e8100340e0300c00140b2491f07810041000090543c0d41c100410840360400c040c0006080e0340c0d0090004200c6403502e0303401c1103e101d02c5882c095112405000d00c950303803601a40c4a00c1d030162070b0f064500d13654074000ca02d0f124040d4403035a0554a028540140c58440b500510305035104000c040c40482d00c8640028800c1207050445a90f48 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 115856088 1250 115854838 115854863
    0xb01051509101106070809100c0c0203060411120c0306011215060b0d1103010b0412021f0306230315060406030203070f08061303020d0f0525061107 65
    0x3454151021a440030403180031504091010300030940440e010410500414901c2c3d60408003030204209140c2d004900d80b42c0128541020181540e4a040508030a12400c0e110804062050b210f0009500700c00d03002012588503040c2420400300903640400c030b160060035111300300b4605010000d580391030b140019005080c00d030318080c0018882c41182030121540b42c2480d43d940c00d04826402618045c0c01886001543c44c0c05000e414821034140e5900c030003078480d050004104a0110030140d070100c0381c0b941402d0700080094400039001d07402e200c0b41e1000003180382950881003a45548104165503c840d900c1c0036080340348003200910f101d0483c2055060b4042022400102c0703100c4003090f0000005080403a10640340c0d40007a0404219400036a0040302500c001c001d5030703e00b0400641c003c054846808864142d6850094480f03805010020500c180320b03036400b140350320450446100400381c0718042414503401d151045001ea620405503000c2d41403090103801410305004440780580e104841d40080e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 115857338 1250 115856088 115856099
    0x270304090203060f060c0105060301050a091a040c0b0a0906180308071515060806030105010f060c0b0c04050607030c02041a13150302030102030910060b0406050304150b040219080c070b01 82
    0xa584003c09843d00050039909403002511030b10042e025640c22040080b540b45800814142107071001041810f41d10705190403d0003094001e1254400d844003540340c640c20b581c440c2860f031105e006c1b0b50700c68034585400141e1454044d92182e91181070f80d0b41981e40d0152410100c01d90f5031554054040a0000c180810074100000e01d85545642100e4407410042010b800800b460840490300d984114086a94036082003524503080c41040e0142c000d02003842c00313850a189004004111100b80200320303c5540010900900340202940d00500d4000d05050361080d16160003415030003c1d0004034051400c0258151a181d1808841da00311070016141d400d0140c0041c1d62503014044000354408100b00c0ba51011002d038500380002c52041510100410b2400000d03004001210090340c044907921105002c14081d075640082105e407c2500214080c07031324160718518100038081445d00c1580580b0010740c411403055807881410301c1e00d403145c448102320b660700c0140070058812600014040c0500304010b210 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 115858588 1250 115857338 115857341
    0x102062e050604060c0b09061b031e040f0204140114060a050403060f23130305091810080c01030203041515030f0b0109050c09031020030c0327030409 66
    0x11841118400d0000807a03507400401e9242d401500182c00040040400700288030f07800100e5038028403590028a031a24002008808112001012100c480e4000003c100118501005e20000c190032440c45a02801c061800d000f8903140c015080f80900d013013103040d0b0b4001f02d807100400d040382c0228000d80a405c01100130800140e20036440c0c00103120080c0008030100b0789034850200003000600e0002001034001091009050700c545094856101140401c40300c0c10010310040e01490b80350500d140c03600712140004811000c14400d0019101e100e00800204046040c0f108085509400907200c011b40c5075001141079110440e4007a011a80c0d0300070f0261104aa640004d041074014001e081000e038803640c50649801c405a030964440440794014001542e8a1081e030350012648a0b195150140030404203454200d1210248600c568400f9216110781004c50b0901481c4540c0780b500f503892500c0300d000764181c1c0046c0d4941d209440d098010103100c41c5007560300030303034400c035100250f0919290401080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 115859838 1250 115858588 115858651
    0x180b0304290c03130c0801091b03080906070f0b0a050a0606020d080415020c0307030203180121090501021b151b030109050604021606050402090a02031302120102070203070e010e0105010206 83
    0xc8400040c4004e007030110f20300f9101c800281144030004110f122544c10020f024071040e0003802d0424000140400002c0c00840880e01d0b0781500303642c025102c47c544d0502c901407291b1401f002e411640404204040c0c2c07895a84124810a040e04c020000191102000c07a0781e403010405034004640300c0008035010034a656030038040c04280c2c0340050314010700000e0340c80c115045041c3c1280564000706c1c000da420b00d0f1055501171489000e04e0704445604a002001d14400303c601140e203800c03541c481c0e81c0d60902c0401c3d01210b42004480e04030080040b5241c070340300c7e80c6800030101c0c80c5e500d1000d20049007a034104001c201202d152440c21203030860342000100401413130060000d03980583e0800600c580c6094050500b0b0209000d43d40014903071401e40140548928014000720b0310318810020010150b8624103200d9401e601551601c94226512000d24024810f810010707501d0710803035200081034040702001c14161841d81c44030f8149030b40d8500c0103907690b420a5840c0044003801036000d5071000c50f000c1c1d188 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 115861088 1250 115859838 115859851
    0x901090f0f050f043902060f010902070f020a230603010302010f110708060a0c080f07021b0f090405031b0624010e040c02102405040c180b0304290c03 66
    0x82c0c8042000c1e42d10010440040810860090f4002d55000c400742d0b40760305d80003414144c00985140c0c80c041104440307204050040c84811036010884006002c04003980030083c95018000b041030030b4540d10485600e65070115080154806040c1c0d00000341031601c10b40381240c0d410303159001d007000311b40019107011201c05004036851080010004a5800030010a40285144440010507010405005051080041217100303800900028070130b00079400910300d0145c401c007483d0030340b801c4c1c0c4200010301d00c01700809025a021203c04140300030301c00044010140d002290340c8110071a148805020b844070422034000c2d840210800c03010005012040102da156101494950b1341c9408060004049035952403842c001a441400e101c1d090032441d00c50400300514010f0380d41c064120008496554a0081c003c040c082e03a119a10100c2d01d600820904042403d0844038402158440c507010840c1d400845051710045100b1043c2d400801003050a545140c040040740d00c042ea480700180500c075840074058 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 115862338 1250 115861088 115861091
    0x4060b1507031e03091113150b0c060105090123060c030d05040b060d15200403031e0504080d0e030f0703060b0f01091511070b07080901090f0f050f04 66
    0x4144800c64184020805248640c452600c02c680382c401078008449a800d000090502e4025500003191420b208800d03039203400c8401c401002000b1001c1800780c00c031194001c82203802a600850000618005084440c10384003c4480c2683c0c1c800c10005058001e00c40c0e0f801d0404048071941044a240e010401c83e881d000e010b0b01d10700000381880d0752031580021843c0742d103603648000f80410000d4002500b500040d04840c0c0f00346080c680e4507510b07a02c502d04540072040660b1948400b100340a032923020780790740819020039a11160789041c0038042c4e0104100785001d500500108855a9000700180c5007640c03a040c0061220741c80c82c1c481034640141945455615100307844c601c0078641820042d40c00514419000803500911442c144000c000040a106040c401282001e01500348200d00c00c00104050345820303108056001c0d00b80c1d08000040e0804059400000303145401d00240d0001400072842c01c0c0da4405045a68503a8400440c030a4004e040b44801d500d40b0410091a0446c2401c2c04030718005c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 115863588 1250 115862338 115862359
    0x2040513020703051e030f010905060117100506040f150305040f030309051e0d17070206040f0f0f061a01020c060a050a05040e0406090201081812032d10060c0b04060b 73
    0x445c00d03050800560380078118100004001095507200280740c01012400028001400c1c11000030f043c800d0700340342c000c3c5003041500010700102c41c0301103240001c00014141641c0d4540702c614101c00e0b0342c90382c007404114101c44000c0e031810034464480c0a100b582c11500300c00d44ca00c1c180e501200036241e600710644a921030303174292200d01d00c031581e6402000c1c407601005001450b104080600b882e04038100801001d140581040106a00450010752103a070200c001380d038181c0329113040f50504080390000380c8003400860307000040201e0380d0700405100c000a9000681c402d0352000480c0e480019640c8141c2011040c0140c1205600442c080c180d0b100150414500702340c3c03641c020300504441200e044d6021072712245440259604100c2040d00812031084000580c1d8240c48030550ba05802d80300c508050000000150484d9040c15500e103a54406202e048040d200309004910b00310b805544d11961100541c0300001c8140c06104003500e4150700a000b03410581c2c440d101c10000300048007000d50801001d94 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 115864838 1250 115863588 115863607
    0x6060105030f191a03010605010201090c0302040c0c05030307080103140a03090e0601090914060f0603040503030103030c0201030b060a0e0a08010c21090203031c050a0902062a1209040f0204051302070305 89
    0x42d402400081c001e1300030074505990109400e40302e09a000a044d645010030403404101c1030911501641d0b015200480c80300d0540e0703001c484040980720081c08a0202105018840b548203001c4e40c101c03030180903462a07260303460840c6600c0381200c07800103020030000001000740c0500518a0345d440382050501c0b080c0305549000e4041903840c001901c45408171f003101000a140b1302984c070b44209540030f0382c055086107001e50314183c3e2480107020103400d10042a0300c09085a11070b4001280c10003020300a5605c954008501030000e4403800c80c0644114201500032600890501c03520070607041c5640c1c0c0314982c0300000c490034074100324069441c03556521762a1500150300d08100034201d034014810702d0016108205002e404603900901801e041030300b070260b01c2002d039030758100b61101b440749005c8004921a80c25074034105032040c000200054050711000705503000e196405172046335001c0e10184880c8070b00300cd115049114502038641d1100740e800900300c0007481e0754080c1050300d00c2030404078900303203101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 115866088 1250 115864838 115864841
    0x20d1107120501060e130201050a0e0a050409060506041b0509150c121801170a0f0b0901080a02150405010906181e03032601050103020c030d0903020309011106060105030f19 76
    0x180c405039144c107002c200508190121035480301c00121204081c0040c0c0e80000c18500c00c000c0a4403c1124010802c5450740c1d5581c2c0c0311000f00750091042010388542d10b00400500000c07a01d11380300b5494210b11302082e2607055540704080c00c40341d40d802d01c0c01030351004002c0d03003400c090325610480ca0180b0905a1001d0100601584050f10f03804080d101c24030130001034402132819000504010705061405500102540101c0c0c100d0726136800440e0032400540c0180c000c0043c0f40407558406034020001a00013004540c11810900a445c040741c1094418080b0341148a180302e454001642e0980800400d40710768115408903c1040d43d8408060b61005d90301055a61041e080450080f281410010103410080e018030031001070780542d0350b03d111800000880c4405208a5040c0358000840c4800e5000500c1100c3c041c04011f8400c100405850034020340e00d400404407103001c80e80d814940841103200240c0184640d0050391031519603920b150b00041c55420181c0141c074048008038086900300c105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 115867338 1250 115866088 115866119
    0x3050f07030905100207080d0e010f08151f0f030509060403030b061209010b010e030a0302120c0111040e0403080108031611040608150603010623040b01020a0219030506010603020307020d1107 84
    0x21344c1d000341900781c113140465050805c1c0e240108140a5070200a0150381d8100703518106034280ca04080d2029a40d0400c4070b1a41d820160b15207034082a40450840640001d0040c0c00c107064413550b03030142030845100154102c2c0c0041e50762040f207502003000280028401c2d0030440d03058070081d00081c140195416a5001e486080c1c0b100f1100340d4440324502c0107540e02c1030240c102607070201c00421003e031207510060340310411401c104a1a00e0300041c0700c0c400c44025040b442150510704251595180e40b4040520724140544003100000c84803000003a41c00310000c00e40301204c981c0c02c0d91604001c10340d681e4024440345214226005a202d074000645101c01b031080c450701c52106c46030000c55160400415084650a800800d4484140c0b08208400419090201d02040c8140c40008070030956000507840c0081801000798803c01800c0001441c260b260300c203c08803841a000c0f108070381d80300c4078240d041c3c1c0412210000182c1c040ca0581d1081440b0717071144000f100e075207015181c40b00d840e148165100c081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 115868588 1250 115867338 115867369
    0x209100e1005040b27040203032a070f18020d18060212070f2a050d270302010503060d02120f1501090e120c0f0d0c020f090403050f07030905 62
    0x1101d9010411802e280c080e10200c1c10046900c0381402e07004052440d0201d90283e0b00d6100710740300100040445d202081210241840216014220305011400000c81880c201c58500c1c00d0013505c90000c0c94810b118100300940c0d01c01003104504400c041c03900d0b0000d422044410074039079214209403140e16030f0b110b28124034500440c800744e910300c00d054044035001400f40680080081c04c0c068502c18640c0303c0d403818552041c00340b94001400c1032400301310701d42e00d854034098100d001e051000c62030350350001110490b400452040303040c01d000e0b480c103614000b001888041d0114204100040c0c4c54503081c21f041012038801040f0035803c482d1140c07030354035051617032010018941c4000c03009074400250080d03540c0141126082406600001070340e007500c40450013441503c08030046400050020f00707000c282d00f10200e16003102e526800351880207003802c000300020380c040d014841207449941002c2003803611660705a02d5603840c1000b000300f01d603595800300300150100110890301042658844186450340c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 115869838 1250 115868588 115868611
    0xa050d0f0903030903020607180b090f12011d1c08070201090606060305010617090c060c0f01090804032001230f040e06041503030c0803060a05060d14060406030c030209100e 76
    0x2441d00d001b91400d075000e4805000e2100002414081b038280404240986030f45084d901d458024030804514240640384581f5400f00348150014010581544440c00d0007110300034805402107103000300c41c0c40c1c0c400c10300040011400a51b07400009800364850a0300549079100004000656031642e07002c0341c0740c9400040020351500d0040003203c2c1e00c50700604082a500340c01400905042c3c0c0001d1f5900303140c02c00140142c6002ca241c040f5001305000300c1d4000c42944000f03002c0a82e031403401d80c955600900045a41020300800507140030300c01c001030000030750183c450360340c040268140101c0e81001042c07101269401081600950942c0c000600003c12076400414154101041000191400c441240419013003103001000403a6006034508555500a0403640d500d444a8002c074508003510f0308180e0b04684001100c610010181e0300800880300000d03248001034540e4820030055640310322026110101d0305c10305001500c0c1c01200250412100c0409048107035840d503080b450705d0811200c145c0c681 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 115871088 1250 115869838 115869851
    0x11120615040c0314010302090c1303080301060f0903050c01081f1707320409020604081b010807120e1005010f06080106020d051605010e0f0102090f060f0a050d0f090303 74
    0x1800c080c0104490b9004505080c0b00c95040801c6400d009101440081c0c420015500030130003400b030113030480300424520010301201c03c0c2c9a08044a03154028840c2e0341c0029003080d09055240e10400440042e84d61210243c80a00c411200445040030003401285035508d100030313040010400c20b040c00d0010400d5541c500c0358401e40c0d10500d41050200d0780100c5004542180d65200c24140c0c1c1441e840c6108411000240c100c04000480d0090120420003900113000203408100f81c50001000060700c0c0c40900580c45142840d401100c02185c00d0310017202261103d00d09584000468024840c01500c980440e148211910400015110207034000c02c01802000d20502c005903210004c3c50240081e40001c0c2800c010605005001c1c4c41018084d1490215207004c0b5010440290004160030391a04101c440c4441aa4070640c000d6020080c0380e489400d025002c81076074140b00080c0e40010044403031032818181041c005450990126100b5500c1507610a2210268043ca214841510340680c2c0e000864 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 115872338 1250 115871088 115871131
    0xf16050a05040515101106010303052a101e0606081b0a05071e0b010b03150d21180b1e03100603020a0509060c0c010f0516111206 57
    0x80385031a00664007540c1098100b060b0046000750b1504640402e03551815142002201125809002448109240114030000040c1640140509020684103208000940100340661036410301d0150701c21540e0801c0b000300c00c990b442039000484000d41a5030380c56800100c50889400c03562581c0000e030200362414140f01e803070452a0002400c84080745009464100c007030a001c0c00c1d50280603c01005529400d19000c00c41010700082070a06502000c52030080d40c47c2c2440c004190001c03200466050890720480001c1d1038040481c184090b00300c490b03c034204230000a140c80c804080e004002c107002c0030100b106035281c10814284010204443c52640745c4280d107150943d000121041604056001d005000c42000e03002944021110b0071304006035500400c4c04281c4040c007a0300e041c01d0740441c1c0440c203481d2110300415252400d200076640c0d4180700302ca19000760365034000d0304c1001c1011001a42c01c00f0004500074942064100300030400441482c1c001c2380181342040884102030a0f040030680c0c5803e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 115873588 1250 115872338 115872349
    0x90b07020a0512070204061509050f1014030603010e03030f07031a010f21020406090f08061902090f04020a0e10050307020d03021602030d05041406040509010306020702030f1605 78
    0x1005001803000d000070036440d40700c099a401d4640e0011464240010b110310441d5600d0344110f00a0101002440d4102001500030308074138100d200b01e60003540c064081e1511881e11015035400c205181c5c4804036885503e6608026035007000707005075090b40d0303030f035501c0004c0036000c00107503115145068078825185011040142a19504035403150070341400082d400b000da0700315283c84079040807854240c4054189200050b290541989070f208105d1000a0104d056548801d86005071400702150900041d40d03065400d58600c0110383c90021000b04051814041810341c00031319801b1001000002c000d5030440000d8100d9101200714404120440c0300d40c045410300415540802e500b0b41022419480c0618000e9220304040141e001015400a82e00c0a0903501e014550441500541240d02c22191104050150b40c8a4040c0660b0036440040500c0c00340f07800400c403004e8410149c1109116440c6584000203904200b04c104c0e8540034005036a0804501080850100901c4a0740161241c1c5841e06004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 115874838 1250 115873588 115873591
    0x100e030c09101206200a090902040308091e150705060f0c19090305010f0209030f07030203191a0403020307050708060705090607080702130b0a0902030c190c06060906090b01020c010e09070504030f06090b 89
    0x400149c0140010008142007038203550307200d42c00761007090008250005130885401508106548112000f1110050450300340180041c81d01c280121003440d211058115540700045807180e00440e001c11800d00c1840c0060084401c500385400d2520140341c9030760b01d081c256503c5480300030100740c1c0450748003078900d001c210440d5442e0200300506181801d40c0c0100703841d440382742d100708110512191804100803090000c0c0801018021405130181880c0c50b0003922a8011101a50a8803886030040f81100c1d0101d20300c0d00a56844d2140351400c00800f041c0503098202845c01c0d03945c920705005000168951000813030044022260010350301601c1402c11450411540000910501c1071080088060500045401c12824000c0d0001a02d034003041c12a0135000d0715800601e22824020300142000241d081a015100ba0f00b00a024a50b00e1400490b52002541010ba0001e550901000070b581005031100760020442d150482c503094903034507410f1740c000c52101c0032103189984100270320a1004201a19 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 115876088 1250 115874838 115874849
    0x3091807090608100305120a030501060206010b190504050405090a0501050a06030305161e080d05070e0904030305090708010903020703020a0512030406030f0b100e030c09101206200a09 81
    0x102260800d00c400400e2411240181001c1c80302000c0441d1810f4041510300c0000c6500508541000510b008a03030000c2e04150284004a42010004139400c0c0c008a4118103039098800301501f00301346204000c0403240710300007040c14404100307c00b260584071800b0701481540090000e0856400070f1500b01c0c01c460f030003411101e400c1d26021003400001c1e072003000c40c1c41618600c001040c1104240c1403100798009008802001d03a01c1e031002510400c4501c0024000b000c0e0640c4040103581d580c0c883c1607410304c520804d02a40710025070006800070340030f90711054201303400608aa103001d4441144c1d608441c03c1e85410707000759001000070000c606e095031a0b08003030401900c406e4122620402c010340c2d40c2c0500d014000916440f032407030300b684c0c4100b9800704075480310051507901c40f0075002e900940041c203110200f6009025010404601c3c2c28a1469940655000005610000c0c500046028960007280c0121403c680311101c2107100301c2c000d0501481c1c0c65a41c2c000941d81c55558201070310808041e48039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 115877338 1250 115876088 115876129
    0x1e0301050109090902031203280605060901080703110408030409051522090213050906070c0302100e100501090615020a0c0b0a1806020106061107050d080f13080309 72
    0x144a140d0b07221405030121a00304001050041031480000d040001684c1d02100e81e000120410404051a61010360303902440c03070304800001001c03035441081d03030500d0003400c0d0080030400c207100840d4401c0060316030003032403458002600b41111550180991050344001e1090b03202040c01c0c0240203161180b00c0e004048080032010316803c04010a1034111085209801c5503010141082c00649a8001403910340d4010800c04e030b82c0307401c10f00010003000150740b824150f110703600c0011071260090000078402a00364000301000e8480408030000760081c907201c80c1c8207000c0c004000c840c10b8600d0044a020303128000e40030812904044100d007074121440c2c00c035402c55104c00550030100317502e0010764080c2c940c0c590748a43d80d0003a510301501c0344000070027000c803541060400026513039419800302082d1201c5944450368401c141210729900c08150058652084641590303100060b200c5000700026802d00e15020705024848004400c002c0289e400041c164000040071032507403074550140040313625554074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 115878588 1250 115877338 115877341
    0x307050a0807030f08040e161205071e020a06050903070b070503010e011406090607030c020406050d050c060d0b0306090c0118080303070c02060409090822051005070f06060b1e03 78
    0x7180d50384010b1840058043c0303280c07520000a1008950445001d861031000b0704c4040d003010140000803509510710040014000354100f03407601407a004850040046560321101020445109215528000131020941c802e4104007000621940606d0344134055602c091502c0b102c46061003a90100020002810040c040006100d50107c1c0003405065649140390009001038800105246100d281101a4001e90124000f0b003010352003259400c140748261800d02c0020740d140244480c05401032002003098100e040e40404d1030515402500222001c014082003425080021030f0802005880c3e020094200c407020815070350f000356894049421981c12810303400d140250041d1a804090006010484c50b00601015566014242c9014201c0c0d041c00f000200c0d01468820082c0d0301c03400e0582c1200d2681c1030156105200e0b5030662045031800303070001910111044044a05a0100901315801d204420050f00490080c1c80303110083c2081c0001e0b140c0d83c5000c0f1010580740c03c000525070043e20030800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 115879838 1250 115878588 115878599
    0x60702060f0406090807060e210a030509030702150c07150c020f24090916020c1309170901200d0e0103110c03190e031207060e060403030b0307050a 65
    0x910960156100060360400e859a2410f20041c2c10300c8980501000310108010301440304a48c408240140032000b00c51a407038981081c00300da100d000003e003103040720510401c5006402074000e0b40d4004842c41c04e8a2805456500080c0d144407000c1c04146050700115050f849030408000c100d001d00003883c04884d11007140100144006401d15009000340401c1150704030b65159901c2c240310045540f45881c40c45d9580581051498011000040c82a42d001000c10039920500c0e03c826642000c640c00307000119590710074808614000609801c100707684821034400300348501180748800000490840e6a008441e000405011001c5510342c3c0b052004002015060400110000100d29605051800310880c0d00160024142c02c1040c5d464200b00054903405650088000c1c85410200103000c1c25002200c1012075940802d100d289405da4844140140248550405001194803822010814050b01007106003010000e13602100801e8032502c503028140341c148261409044290b5580c4079042c9082c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 115881088 1250 115879838 115879843
    0x8010b04050d021f050a03060b040509010905070c080f090405010e06130b0f03100b10020304060f2d020c01121503060e03090d030906020d031e0b0111010606080a0c02060702 76
    0xd12440340b28220302514001107403180081c500d9020070782d000d4691010840600901980d1004a0600020385810000b00b9081c206005407000d840b0041d1035603070681c0c01d000d107a4000b8100a80f4079414000b0b085400c6000400d8000245004119592501e864001e103405002c240c98040c4c028503902e4540004005181c2c851440c407c0303000140f0070010450121940c0850b0b2000384125206416003e0f03495a0107901c01c0c0c40c0c100b084004000e4a08180680617107001302d8480c040c9010301000102d40503c030b0099107100f01501811108d0040000284c0900f1030140c101c0d01551000e1080542c022115000fa150f8100310007900e03000141200703000c0d000e902041070001602c580401802d4540c0d0f602c03420041c12042064502001e0040c1c00412012a103040207003038000e5601c03c0400520580e054160a43d220307000d04e01a215400c464070074940c86521700540a025000c0b40b60b4100700b000d2403c010f400109001c0c000040045480b041c110b400c0407007440064031480c045803000c0d0750000090000b0b0b207600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 115882338 1250 115881088 115881097
    0x503090103050a0209060403050a02090610200c09040311010606020f070b0d09020319060b0f0a0b090409080307050408010b0603040b01050d1110051801020601050f0120010f0c0f08010b 81
    0x2460300042c0c030790f0741e0361800c030007402100a816003084007c00c0100400c00c0c00501241e110b4022210751040e82da91104100b9050144e42c04180000c00e00541048801b14600e100e0402c1400001074404181d040c0740440c3c8010320840c0c00790005150000c1c0d45007400028850131002d844144081c10400741022521551103030184215054402c00041b0300d1a800402d40c4214252503009003a9984450041403e0010403100b65040c1d0b043c510300122030174646003968200340a24130160920b00340500c5c00f181e00301c40390409400c0541062f118540040040d000314015807040b40b00c1c0d1501074549041c161550300b150302c40704070540604801c205120101d44083c1c04641103480440e24111131000320324041c5001c49a42c03040c01e4010542c1e8000c030701403e401c00d02800e0514908500d854030702003140f00481e6501c4d028803c1c50741050780c2c801150000d500c1200000307005000003034032410100b4510311403400c413805e10b4000d001c96a40c1c2c02c2c40c444280da002c2018019031985262440381035050200b031683c0c038403d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 115883588 1250 115882338 115882357
    0x30a0c170a03051c0e0a08030402030d1b14010f09060617070e0a021e0706020d0b2218020d050c040c1e1823030d0c080714120309030406020c09040503 66
    0x10090068134a420140d08040c0e000d511550903500c2405491130218020781042d10200e11a000e004004990140714807003490303003140d02d09140742c803901186e02c506190300f08018401c80c0e155240c414950341c14885d80034020a207442001d0025505160003890b005540072043c41c1c0015401031842045805c14800b5880d810500c6000010b036a1101d405003030074208070391070806042d464082880400d00c80d650f8054440c06111070b4082c0300510f150703010412404422842d6104150804400c800c4031070a0358401000111048010714260800d9000a0081060314004850550ac1600300c2e011605140c02104420b01b090f040425989204040b0304820411403000101040001a1452240000340308001c000f01400549405c419080317210141140c9a81104e140c041d21a44035801c036824810004400c40942104506051070403039910141e9070000102601c1307141c881c5112203001109045c000390700420600d002140d54034a002406410000d4094542d8800e015460410002c68408006c41d01e0646 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 115884838 1250 115883588 115883617
    0x7050309120a0f06020d0f0c1d01030e011811060c070324020c160e09070314070e091006060806090705030703060e1603050a05040309030b0a020405030a0c170a0305 72
    0x11101c280840c609042c455010303014a140403207100520205a00400700056141e005000b10303a0344d8056101515000b4a030540003690480200341501c0301c1d543d042848000500d8041b4607009824803980c01d441c0c0000550140b0030078031210300708000b01c1800c40c0d01c260800341e42c810b041504c43d040d000d4445d0703071512014011214030000e024006400c0c42000005801c150400c45d1a0303001d080007640c0e29120b00d680c540c4d0400d0740c24004903052155055040c403602c3c0d008010180d060556640c0100d0003001107614040344100c020102d03065142e203200701e00c01c1c198500200700b0701c107448408100380c5a0a5100f4418451000140042a1584900c090303118456040150742ea0301c0300c0348114000c1001d0360000700540742d00010310006181c40c60048080d8500c543d4140140d0712664149000c40300b09840080200700080e0080001817058640c0661103c2c0c0d0f944014202030382c420105c1d0400042220465a00c0d108440c10b000d94100d10381508040c640c0c000090004005d41c0c4d9001d4128032405081c010080b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 115886088 1250 115884838 115884859
    0x30c0406120b0903070602030106090512070f090c02030f030f0613020708040b220f2c0402010c03021c120e010c02100209040b03031201060201061509090510091407030b010507050309 80
    0x10f0f40030000c80c0d0190f40d000504550700e40e503454004250034258040d1074801c48208029001c00e1000040c0e48099a5143c14026040303071408840c50000c100041403602540424400740a00d8441c06000d18452045005124010700d0b01100b0882c0c0c01003010a03851910b8410311020340421003100c241e03800d807a10500076568440c480011840400804d010032880c0500c9420042908090140c0000840c1d044120712190742e103080c03401a000e02e407884034500b00c1058030000174002d50321800c0410b6505000740165207540c0001c103d2102100001c103859000b1401c145000c40d0074104a208010000594000800051401d00c07002900c03080101100341c00740d0740108031409969159442524041c00050890b580d4130650070440c5400302c0d0904c10301d03015528000300082c020306485e5007482d410800d075966009240c2841c103940c000384009081d9030f80c2003104180210b00c9816900c15910685107800d0741d81181e241602005065411800070181041418091301001860000c2a111076450854090420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 115887338 1250 115886088 115886101
    0x8040909032c0f01030b0f060702041b02070501170103051914010c1d030106030f03050307020304050a0801020d06061b02040203091011031f0b031f0302041505030c0406120b 76
    0x1144503000d6040300c01410049a45019402d0034010542110306032041003008095000550449640401c55500903101d0740016990346822030080078079610050000401d80e406010421028500500010240e800351070306121a40e040344d400101041d80a01c41c1d94158156641d994944955440104c4c101e003501c10f900c000c1115229040380c4001400008109035100350200920310513960f03282c518507205542070201c0d6804d044c0102015a90498280c28030111159002c540a0744000c06c031908500081c88045900d40d141d182c00b0005000d080f00140c0c41d10041c0b504213044402c1e680c08401800f2241030913101813280e801000c0345168040f5030044c0c4a540ba4088182440000c0890103142841c010000211010f1503003c1c600a0906601c0302585e076208040d50165650a80224001201c0510014011101c1240703403004e81e0002041c072000365603813540031030161011900c08103000d0698000500040c1020058100561000c5505005582c9070580392b0300201c401074000741100c01640d000941 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 115888588 1250 115887338 115887347
    0x6010f0509090106051009060914030a0b180105040c0e180c0d02011e09030c0602010902090f060d050a03030507021002031909033b010513060e0109030f0b07030e0a0804090903 77
    0x1e000244c40c0d09000d06d503592008003010528000c1c5404600e050b100440c0c00e03403088444101c03c0300c0140042c054030311030b52103444403440020700c9050001d01c05012590740700c070280207940c01603124400c0460194102403103031f001c88200424454254078003800d40c0341d9014000462200800007900d0b104859001c0340012502004211103e200100742c0000850509600004c4202120300450740b005072640c4810040303080e030b8140c0c00b01035404800c410229006203840303d441900800010b0481c0350b0f400311a515581407100340c14042d80403e649400300710807150103101c540c00311224440b04514501d404000d400c00301016000c1d0ba0000b80e5249000001c0600890310801000078800392446160305144007084c20070145014807403000c040f030b60f003502594010016501d042e901e81d4850030007a400c15074200da0300100c00c9482410403107001800400f2800411a29400360b01071030510003d440c0c810406000d4071014010000d46030300411050300071a0380c1e841528152285440b010501074680e06003200d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 115889838 1250 115888588 115888601
    0x5090c12010207060e0a02011119021c05060a050f011401022113090e0106140d02040f06090e060109050c0702010f180902040b0306010314060607020d1e0c0f0806010f05090901 77
    0x102424945803080f18001c5001a4031b0321a00d200340d0b54250310483c94408144c5070556581c64070000d80c01c100c11a0014500150001045a0343c0c0d18065070030035054a03040e207440300075191007500d155180207010401200d800e031540500524401c1442d64952100002d640c0c004c400c0c4102280d111900e112006c2410b00400c86800081e41c01440c0b030b5039a11149510002c1c11245030384041c561074007000080e402081019141e5458004107014002c0303009400380b0000d403d082a8107040c00765600e5020910103014403174800c10380c04050081c0b4507581041403507000c556010703140144641082c001100140c2e4084041c55040300c843ca00074542c02103c1d1201c14412b1041d80051801900101d40031a4144210020b50303c1036800345c4e0140302017400c9400c010030300711b030960f506504000708104941c054100303c1c044d480107521880d0080a0303010b207502510b1202150080465404081003010407140c0b00042102c005400c0c01c102400301549000c1d213201c04182a40300321030296500c04001100c0400039031020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 115891088 1250 115889838 115889843
    0x1051e03071215050702010b090402010c030e0307060e0f03030301030f12092705060d0c05040c05070221150f2809030201060501110a050a11190303030b090a05090c12010207 76
    0x5800d100610b182030f2005040b29410500a54034140c00510694414002e14103c1000075180d03c0454555400443c1e43d07806034001a000c1c0f02c000c100000c1b650710304004180081182c1d40c0c408080c010f06000308403040c000c1d500e51510a600910051003c201e00303100d541c8880d80d00c1844031425440700380c010341d6210040d40c4816100350404082c0141c4d51440c0320700361900380d00b10100f04841e66400c030820104503103f0341d014100c0410960709003d0b074105036018448080c0e05091803805c1107000d60004640c2c120341c0307011100c50101e102a0062000c405c0201c04654000100f040c10f1601e0040c4c562120304c0700003015185035607418080310901184041660601984001043c4040724460030064064052407190600041c44070583e85030680c0045400003c2d0703607000e40580113850710ba0300da803c485410001c1c181c0d80b000154251110340c80c20030b05100300841c42501d011540c0c0071040d040142c0080001c0864070620b003000d082220f0040003140103145240100da9941d001500c00340240c0c028007411000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 115892338 1250 115891088 115891109
    0x12020a0f060507021309051f0e0304080c0a0509070c060c0504030501020304111c05070311060c150103150e030d0504230109021302250809040504120905040501051e0307 74
    0x106070168400010002a802681c88503c403403544008081104d103241805046504002d13003607146814041d04411000144e4000814880761070f4900a00303641c059401540c00b0b034040070140031581401130701d96009020444d152405882d100078051303c44944484010105560745107806c13510f42c0180256000b035034000b40210346a00d80342c600b00400360808090f492040342e4005d00310090440d00308c4e03811740341075000e0060140940755076621000100180702079a40318405114001c024181007000520b68810b000503150344c2d51660170404181e61503844c013844040d05011050030343c03100000840e01207002059001a0a80e1103082168004201001c07900d540a080c030f5861200d00340542001304400d008803158079040b03500c181c984040f0b10903d8100b00100e4441000c0404100c1d0000400b0503450003015003616000c01303803002508a810441d03044600c11420030300b18024550244030200981001e4508000303950414000803076990147e11207041140c207a4034030809584040c4000c500130582d070341a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 115893588 1250 115892338 115892369
    0x8040306110d0b06190c02030c09040f170f0702010503091018110d0506010e070c0804030305030108210d090204020409021b120a0801060507020409051b2812020a 71
    0x100700c06501607150401e409007003584141803407401c4000c44008806104110360740407240c5005030f419540808090b40c0c9070145007116051525144020351245205850f80c42c14070400786031403440080d0803612240e00b04c1003031041c864621070010449000c5070302401e01c181c483c0e5410104620f418856401c0e4001035081106022003c00e9400711407003030078804d81d00305074a070010340b01388510803e1010380508140d0108004001861100c0040e0b50880100e1400c42206000c2d52204045503025a00480000c0d100000400c0080f0f01440079034281c0e4071022054403400b650000d48a014061144900507003543c0d11400c2003107554a5048400409183d4010354403101b0280d04114010300c000081d00244c0626110007104e2a60071084400036400c540310044940d08001c0200c80300c0d04034071070403a003041e5103240d8940402c1c1f08111881850308154526040d85d8039201c1030110b11100030543d90880c00910042c0b20700c1030028507a02080c4c6010001240048070207000143c60800c840c1e00c07001c43d0865400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 115894838 1250 115893588 115893611
    0x21b091b0d11040510050f12070921020906030303040203100c020f07090603060c230702012c0111030a021c030b090103031206050609061207050c010608100507050a140708040306 78
    0x40151013101d0040b0baa4108081c507007401a00c0c82d10907004c405111310410001c0091949041c4502600300c6654500f030000b0075124a40c030701da4a815010301c414a4080740542d1411460b0a40d40a0791040b41640a1030840c20f1070360100e9926141200000d180c140c03184d00702c3c914a8800c100008145104a0071140f0450355500c0c03d0b40245000d0005444850602a00b800380b02d016101289080001403c112442030304000c0528407600003041c202e04002c0d402d028075516803050840c42c0c2050604002001008921000142c1030040c51518640c00381c000b4012510015008200c41c040b10550012031201c4400130f440880040030041d120aa0101103103001006042c1e11078401c11b01d9000500007001034a440358100b080500503215015841002044044440440035640540000103401c0c91410400e00c80c0400b803c2d15180d4010745000d6201c022003e1184065004482c0c00582e00c0c28054940000490020000300d0f800000c80c0d109600050018200413400040382c0c000c680180301045140e4091 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 115896088 1250 115894838 115894871
    0x11011b0f06050105030c0303160309030b09060709081c0c050c030703150e030405060f07110901180b060304030f0c05031c02041401030605060a1d12010903021b091b0d 73
    0x680055900c02d18040000ca00c03400c0000e000200e40ea001401181801212252010a1034800d41d04804100030b841c40040010040c01d50180600c98440c0901510301e040b210041c001d10140d800402c9541c4101091184a000c0c210014020140c07403030202c4024800d41440c0c0e00d050b000c45541d80c0c1502c1a107400100380400503098252000c03800c04144106900d806259550313006500401303500000811800b41d003615100001c00084d845603484446528030b0100145d03244400b640603215043c02c08410400f8103800b4400c078036218804569460440c01c054034014203810b001100541485000310141c0c00384201041a980e400748050a01c2e03010348108600031001c0e40085c4100300f840000f12140121541c000d02401040c0e40700501072504000c0001d00440c3e03ca800d03100009070352100d0601c014101d0b00c40c0e1400303642e0400310300b001058080312440c0c000d1404040d00c00b1b258100d1070285400000b6523902ca1420303000300f001414003045001d04100b842c0360b0720981002c0320786c061a2025030840007004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 115897338 1250 115896088 115896113
    0x3070b07110a060503010f0e06120a0501020c0c01030207080403020d021807200a0302060a05062403270a1112060f04050d030c02060103121103071103010f0c0c11011b 73
    0x5a81520b190b540c1d442c0c055815000a0190802004681001b80111715100e0710303555000000502800c3c2c3c242c0703511903150500c200500d05480ea6500000c2c1140e22403030404c2681e464400a2070210b1510311b5503214240ea900880c04000d00c60107040072250203658a4681c86506000c5540e80d140c2542094200a0b2000341041d043c84030700000d9104d0341c40c80000201d0794442e00da4058020f8016031703551007c820010107008000c0d540c4000549080d07a82d05010440b4201d03156131a4003c1941c074141480d03000071540b11200c004200d42014048a150100c010403601101a444440301540c4110f0f08005410800418440c907158815034003001004917201400034001d81c041e0055034030300140c03140100c0a89a180c04003201590203c4e0040000940c0359038580743d100e002d80742028403031815441d00d50a6030b010410a4401105820271400d041c0340031301c02c140d50400c03404410480d1034202200586008643e80b0083c0000f048240300729002d90040d1a254500c0040c82464844280140741c6550341258 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 115898588 1250 115897338 115897373
    0xe030d0207030b0417160501050c0306030319140a1d0f010203120408040e040b070f050307020a08090604031a0103120309030c0308060a09020d0f050f1b0c0c03031c0b100e040b03070b07 81
    0x1c0801054ae65110402240d000750000360156140000500e074408050030440428010408a140d140c0f1400000700040d00012025170707246a15500110000401c18813520881842108038048288443c3e030000110f4100d821403c1e60040599564100000a401035070b10501740c888007841003000b080303c0c541201c0d1142c3c4075503d58010b44035000030b0885803800111841400f59112050b0200814070341c6000c0c24010100500780d0b8542902c3c0e03a034003e04084050340f001c031200e5a401c010704c1004214107410f074400c400c030310b42041200e0450718000c0c4000d81176500582480b201d1408180d00e61240710f283d0001d030409140640d039810100c102c450050580c030080b407400603e2b05001c00d9440769080b0540340902e0042c2d2400c28095100d0102e0030842e070081c0100d0309a841038000d0307103040f83c509101401c6542016000071161108818116094400c40c0510710712400c0030b1210303089410f4001400e8495618180c500050103101e41c00802c2c03034086642c2103a808194003180d018200041c8041c400390202 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 115899838 1250 115898588 115898591
    0x1206080a030806010813080f090d02120c030f01151401050c0703050c0f030c09160504120309050a06031407140409090809120312070c02010309210e030d0207030b0417160501 76
    0x10b4600d181d0300041b05070260003c020540800856030f60314900c802900350410000e0400300316041c0d940c0003401c0400603400ca010180c0040d1148035191506001c0031031140c000c98001e004038140b040d110440c40007640520000744503155501c00d0248d00c00e1081c0c841030a81282120600e5849040c201d0f9100310040038280306480782101c200e103a0030041100d85160720301810024040e00d920411002130b1842032504000c018090100140d03c1a00013607106080b4080d0722411203a500b40010303c040d4802c1c80e00300605142c00d18204a604e0900c00030030a520200c9441c000da0340c4030110142940902c541e40c001802942010b026006006041d0000d00fa032840480e500445007051541c042c0c1c0720300894609000702440c07400042c4441e40640c4202500510514000482140c10b580d0464207699802410142d400c4003144d1111a641080c8000d014071422001850840e40454000390340e000e4130301000f04510800c001007810804600ca20501041805030240e480300351240380700804d40c03030150041d906036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 115901088 1250 115899838 115899841
    0x607031106010b040311040207021903080309151e070203040801110405041406030d030902040f0f020a12060f06050c030d050408071a010303050403080a11030d02040807051503071206080a0308060108 87
    0x150310f500845003100d80c444043c1e6092000c3c0d604000c004e4005200680c2c1220040a45408142c2030143d104007451107025515100d0800200d46458030a2a8000ba480041c8c0541402143c1000803481000d000462400703640598032800102e040d40071359480301c5007075030812200c441d03440e000e80080c0003501c0040e103080144000c6038805502038581610855056048201101c058030b00c250000c0d48003038009480440d145030310a21940480e021b0306100081181e01103000c00b03645501117013a844521f0528001d00c0481c0c2003520300d4680201c503105038000e0100009401442c0394040c001d40b0081f410343d071402c02c0585400d04003500c46038090341084a0314243c0060603081c6120321648035041ea50160f840c02c0c181819580c0c1c440040d07009c0c0b00b035030051090040303200e40d851804000a04c0d68400f0f000d00561a50f1070010b6135443c051064200c64468580c00282041405400c001d90758880000d00d440301210040590403801004e282e08031340301600413807960400b4036030003240c254000c680a2384c640788107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 115902338 1250 115901088 115901099
    0x501060f1704121101060510030b0f031c0c1a070207050a080105010609030303110c0601180e0a050a02010f170c12010b0a0906030b0118030c0603060510020705040911060703110601 79
    0x5086040b203006003600395001003c610148615401c101c2a1111000051016151000178500c032011041d8100001d0701c1e55a5100385003010481c00f50b510708160010a091303080c0402140301c070084c860390941003002b0042410144002103400c8080044800000c0c40c02e4104944001e44a080900426020312440000014030180c1403040604035131302651042000307811682e048010b4440c803101050381032418030500e4607500040c4020350081c01410702c15680c9a9000402e901a903921001000e1107400692049020482c0880c4040b6403e5092801d8817000d5061007060301c00078a11046070540c1e007001d8040004103c000070041412100004d104a826030b6a606041802c0c4191076030600080c0240300204107580c02500030080164050510145102240c1214072001caaa0351066840e0603080300100604d6405101e0040035010a640300c05440040c0a4060f556600070301c2013500556849031144103204400c001074656103030090aa40d920300c0b0b9424014004207c00c0b141010501509000144 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 115903588 1250 115902338 115902377
    0xa02040b0a0e010b16061b020d03060506090904060e060106020609060a090222020c0a060f0b0f18091005090a0b0708011217091507200d02130b03010501060f 69
    0x11540d20210551080e13080a07240310013031300404a0058038036004104080080e08a010301080010801a0508032160b0680300a182849050180040c5460718400340310340d44034038045880b41201690b41c601241c50b6481c2c070340d00500b010200005140103441c000f203180d55012031080e020743c0061044642d10f850b014085411102200002940707d00305c0300d00185580c01e254039605801d00060001030402c40c0f00007846090401c140340842c1c0b2181d1360b810110680708140b080940601c003d58146000741c00380300c08039000102100c80420000d00360710008620130750410140a00400d090f0040c45142003000701c0f00e80e2658080011a202051880040c0c00305214505e224120355401c800303404402d1043c0c5804081c00d045442490a9510810541031144c1300d103002d08107485031002c0c1b8a0b0b607648040c02c20719210b60303502c3d10344d240201b203107840400255900442c0c1540c86804490804144403810308070f0004200322001ea68240d4200300000030703d640c206034100000802500c882c0c1c50b10041107016031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 115904838 1250 115903588 115903609
    0xb0108070e060d031101060602160e070e011103070501021309180803180a0b010803030f0a0c05072009010f05040b030f07090c0909020309060601110a050604030302030601090b03090a02040b 83
    0x600050001c400030b1940d00d0580c2d07003010307040c3c02400d1403007141e011660b1150035142e86c1d4100c080980d200240c2c00b0012403044900100400341e01a800d4401d05140781c0050414403c60811170420443d40d01c0d032002035900748100c0e2a040d0303100c0d008540d5107190359240c1152000500c2400a08c0340352025031101150040070300204136070710032402440c1d0ba03038400c9031400c6403215040f494044c0c490003640c4000904c0f50aa1a40a0203086000350707282d14005081e044402d0000304807120890601d00895a0550084180c90410b5440401e2102a00000160480c03610120852a034016140c0c000011500035031002101510000c1d00c0c280708a845ca2002e05035500e09400c0e244030340d41d114210401c07004c10994041502403e0520b003103d60581d44000c0c540c184c0e0020744090356942c01040034084151380100303048140c0c180a038050421440a51203054803000d0040001d070a00d0b400000191003680b1849168002e0980310120301c0c0c5034181420b1040d96480c02d100d08a00451811003460007519103c4020f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 115906088 1250 115904838 115904849
    0x24040905061807030803010902030907050a180507030f05070e0102010c1b02040504050102070f03090602070e0708070e0a05060403031110110f16020409060504030f030c09060c140d020a0b010807 85
    0x3031425469040c01d2840110b80c10005240a0290842c0800040c0c0381c08000c5008082000002d40c032420a220001e003010300b6988110710a4100070f104104409420303481301c5002c105860001899504c642e0182c0c043c2c100c0041501030613103420200715032290803400f404400d032000c6c0d00800c8600680001942e00c41d030441d1284a01c50f0249590000501d041d070001c07036100d803180c800036062800d2035a8a800c1880c016800b200418071400701444003950412444004002840034144241040c88002d0502d08025100c1001c0080455000c419921b0f203822000051102800040e6201e640c1d050042c83d44801c2030340100940502d0718407000c0e02c1d10501404003100e4840034010b107809185415a443c0b0341c014407055030345449041410f0700cd40d45510038003181038090280400d0928181c40c0042c01c0b4951030307c50700241442d0040d001c10107548006000e0603945c4030300704200c280400b4204071540c0f51035013006281d9885680d40b1407410230750116007205101e00c01d41c0801010f0747c98074009610f03070a050046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 115907338 1250 115906088 115906093
    0x60108061009090c0504050c040305060c0418020309010e0706051213030e090901110d0218030604030912080702030708072108030a02070f0b010f140306010e280524040905 75
    0x180048429940080c183d10301c5a6181d40319140d071348001c0340a0b174004851380c68540030301140030000d100c0d0034081583e11a078440c0e021b40c50507040140640d00c000d031080500084542c040002070200909500c0806034030700c400100d1340713036a40d90720008203243c9c04100c010a60b5010400881d00e01100e00c0c440648207649a00c0d02611034200f0000c1c0b00c1900c6004080b0801c5640b41c020350826114200020b1090b9505004096907402222446035400403141c0101ca0003a03100700100004203a21441c2c24043d10884a8100c0c0e035640300e414015850302405a000c4e50601540e00c000802c030a0010b4004222a001c05402c14140018054810500e09101e4042d261150401c001160500154018a8030910034481d545028025490b03610034000260030852403891442c10920650703214050100c1c07160404c500a00e150f40c108641c090b000c00000c0d000c0200b90300b202200c40841031042c0c007030340e86040203a8400c01080c07a1403440c10242d903110038083d18026100f48840c1142d07041c503005441403143c01c20b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 115908588 1250 115907338 115907371
    0xd0c020310020c070e07120c0509130203090a0203120a020f030313150204080a0309060206061c060b01050c0609060402090c120f06040605040204080303010f05060423060706090b0906010806 83
    0x88070180d400100041c825008144012640c810750a0760f903401219140d80700540550084030f074030111412500c04a00b800418001910325541c1e0404581400340f0440f4050303125210005014900302080c10000e5040c0208122030890b4861b06d409000c086045600f200c20303946a103910b031520784c03006413000410084a004901c012480340e4480c0c1140764041040149810f96408141d82400c010020440c001014141c04000d9140e04200b40c0c0d400c07082c201c41004905a40340e036080014908620002d0855071140303003400d05030317000360103440c409405002600d0703040c54504496502d0714805c032001c80c4103004d0b078004240c9090b8000d091786c1d440c00090281d400a40c8412045041341000100384582c000d49030b41c408281a11140090b10003072050000a584030350401041d568841520740189010301070601c01000f5025604420024003019680383d04260840031010a44500c03600c80b000d0180c505141c0420100001421300a2040070301d04142e030341590b2900075081d1204e00079110140c0c02180e050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 115909838 1250 115908588 115908613
    0x1030501180e120313032003070f050c090907080706050a0906030b030c041a0102010608030f0301030210091505070b061906050c0a0c1e2108071b090e0d0c0203 70
    0x14080c1141c00b24920881d0080f00300040745003030640c000c490f04c800303254095000c28105070b000740e500119a0f0300c0c03c0f00c46041e10007041c1000c1d5070f40a021000b83c9440070928810381031000074030140300540800b6000341410300d80f100450313649001900c1107020910030701800292042c0314405460b0884110352b20201130520306a0103e01030300d64403d03500c1d4140150900c900407540d0300e124111071048028041100304607040006802c44c1c915038403803507440c1c004004400705c4403842e90840741900c0d41158031202c5c40074541c004407054002504622106080e1034801b110300350300600600800e510455041071907664440a2013141030241005142a658005003440300c180504050700c0550303081c030120342c501d224076210201112200d034800d5048e003030180c0c02045000000301e0802c015088a00b410046030111000c80ca0700c199030311801800500e00425481e042080c0020740c15056606100303d129510f8403022040014800f00808210500c1142ca24070030083c01641800841c0d038006014102c84420301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 115911088 1250 115909838 115909841
    0x30204060e062802010b0f0111030406080712020c0c090105220c02030c07090b090106230304020109030812060406080c13020304080403120c15111e0409020a0e0f0103050118 76
    0x1081040f44196055440300c6520400c64202c10742881550300200703d00c8003080070b10090015030640d450400000c001d89880b101b0001080301c0c116a0b2a1500d80740540e260441224103a8003080c103030440300e0002804400c010f1000684c0240301504803250300c10f60740e0f194108443e0300342c0c40702d804401c401030680d6482c020f06030750f001c10382d0503c003401503924011104083c1ca0501d1242e4000c1450700d90390380b001040d1400c20781001070142641f801c0444000e86958042c1000292a842c0c071401414000001001c6912400341c0200846e48100f00b0798441e031080001450b010404c549440c096450501c001a50450019440a2040004d0000710404102241c074401951000304150782c00d041c2000000300140d2400c01c414604903080d0348900c20300b10f461400341c0c1140c00b1442c000f04224109010420340c3c030600343c12100070485601665040c0030301c1c04800c1d00c8900840c1d004103140703440421300034445900711820030141d0784100c0354001300c2804080150219502809240c84249044000e80c202040a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 115912338 1250 115911088 115911097
    0x30216030e06040504021c060e060607061a0405070201020a020f031801030209040b31050106080610140c0109051603330c030f05070e0f01140d0501030f0b07030204060e06 75
    0x6001c0510f840c0d1642c0119003a40c1c0161603005607060380c1c1c04014080c521034402d81001d0500d4041c0c204444c180310b40081ca490045e0080a0f0506a480128040282404100705107400019009101510341402e000c0d000790450788210008d40268204101c041d0004021503900785810a296200040c40000440003508803010086c0c0044d035403000f4210b07070750b500510301c60180c0c1001480781d044540124181604010121554841c070704120050000c9900700d0031950780a07005407803503100322141120454003038040c0e034100e0b20f580000042c0b844180700c040d000581d00354084c00c2200d80d200c1300355640f024400031920000d418403000f280101004820300d0394408100c0c0038001e034200003801d190386081c201c03007130512414003007a512602000700c0c0403a4010307131341c2c80b1155082488240c5c0c80d070b84c00302d40317001040d1484a0400c004817003803050030040d000135070300407140c400000c2019613141d1620001082c1c0c14802a01c840c0c91600002e9041407090080320140c0300356030303202e07a041003e003020b2000301e412 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 115913588 1250 115912338 115912367
    0x6110102090a0806041205070213020d090c1412070b160f0b0f010914040b01090b06040914040215160206090d08210703060503060c03090a1e0c0603021603 68
    0x408104480c007076a01d00060704050071601020703107000c0c20545807905002c8545003130071092103410302070b480259a800c0c1c0c441000e45925a8090b075610780344001c0000521080341e00401e42204030390003080c0003110501625140034282c174012203201290f030034aa40e0b0394103442080c0d031101e0104201d071907035040c5030101900c052103804007140b608482e46d5481e1020300704650012040400400402c4003c046008210318400750445d41d02c0300e8146a2200c8117015014010100c41a44618000d00d43c1c0d1075850403140140081c5400f000041c215400d41d030021503049d1026441001180e0301e02a403a00d14000300c0c0e9426181c6c00300c01603210340e03690900c601500000b8015074480e090f601c2210108001c01c2c0280305803020030010070720401811200c2040c00e0b101401c058101480c00c0400d02003a100010215001101c01c0c07001d58a0b551929000c620b00072085000815211410301c0d0340c2202a14004108143c51090303e4440103541c1b074107811404c0380120201800c100c00090f1030100401d0060b06815907210 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 115914838 1250 115913588 115913591
    0x1401030f05120301030501020a08060a08061b0f070305031806010509040f020409151b031a090c0d0c020619091109090c041d0105090604020d0b190f0507021902030601061101 76
    0x1400b000c04090701d80c200764000e60302a5000164130403803981c0402c015500580031285800c03018104070b811552985d00620f10441c810030402c000b1485010442512101c200c52460b2640e18038991400610540040d60720f450006408100d05201c13041c00b00384a410784402400491881d607561303c45600e9190600002c1c0d07006070fa90003002d0b01181c0081c80304080c18550420103e90000e5507100c01e8250380707031030340c90a080602d000709460303440b0180c940d5943c07650006c82e04001e454441d000c9000c054031034517240103025881c0c500000c00d21500892120310540c8803104121410703d083c60004140c078a5043c00511070716540f0440012444d0143e400ca401c00414001c440c183c100c2c50010508484a5882d4108802100598030304407481c00d01485501500e2640030307001500341503001c20142c0014010040000c5810720024212030b100028980003240c0c0c016048c0200c20b48035004800900095902a00600800603004504000c01e00d0140d4400d50180041c44140c0c0b0f0808100c0c2c85a0740c4594080855 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 115916088 1250 115914838 115914853
    0x150901082a0a14120403021009081804060e0115081302010203120405030d1e0c1805010318050601090510050409030806010e01030608030c010e0d0906020709020715090c06080601031401030f05 84
    0x2480f4040181c4080000030041d41010b040506010345803642c19540920039900f00041c1d4400680550141d07544e035460240102c001805100c006006041d4542081000b804084000100d014a44805000c280a141c0703d415850325508055854800343c00f50103030250b48201f10ba980c2d0721000c003c01c682e20600030f1041ea07080c25103842825003521203120640c4201c00e4041039091681a9600c40e55810907003600300301800b1321998048040b010040e200e85814560348410b2803102407020b07070401140300e80c00016545150b84605001c001008241c6d1302c092036040410012800e4206449241035064145e155881c1e1940d50f04011100504030088080c100b42c0c4801e40002e25110400141002d04504400858401d80700303207043d80f50103443c981081c200b090556080042c0394011400200b9159088800369581d0b80c182000c0320310755031741007101100510700300e00281807282035403000050fa070760341da220b8401d038031100b00440c2981c2000030f0305050045200010400601006181080b0b0392049003a03d080307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 115917338 1250 115916088 115916117
    0x1050d060e010f0605030c01050405030c19080d020d0f0f05030a050a0e1f050603010b01050417031c15050306010f0909020d060203040f1103070e010303110c150901082a0a 75
    0x80d10054451564001d807513a60500c01450107200400707103401c00b032a00d036003000e1808002a40d1260045002c1f40a081e9103140c4e21401240c42d90850301070036a02c022201d10030243c4000a40c0d44030740c02601c000190b8498a02600948600801d440030500d55640f00d040d80ca40d418800d000b4140541240f81c81c56442c221100c07461418041400b40c000500501511645115581d10036030318010041ca100380d1408031042420307a00642602c0c2900d42c44000491a1803480001d6480c42c450000000200c0341020006c3e00d0115194001d1544e0020101a070f07401181d83c0e400340f650f035400070b01031a802000460401d0045140035846500b00034001040e5880c507208944a103800ca9000f40c03000d440e9a5462000315042c411881200142804154014181c4520341145000000018040101040a110b08091424004100041d01803000500085092001418418481d400865400d000c0b94860000aa400080641d0380079a141344480700d54150041004230103242d4840074040d030a00510304001d580 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 115918588 1250 115917338 115917341
    0x503010905280204030209060f0907140405041b02100b060a05090102120301030803090f0609030a12090221010c0c081902120724020c0a030e0d0b04050d03060b070b01050d060e01 78
    0x129001800b0050381d550640c0103201d10202e005102c64004e440c0725035109035540350b403180750b94030085a18000c80304c9a003010310900d0303034030a5034041a80241460101d104407c4003445030840f02c042a0201c81c92540b5201525064801b02e6031060b84c4503005000b61081140502c00030081248144190350607407980c20012641504203800c1a16110707008403c20201e81420406032190142c514003d1401e4035000120030707a01d220f00441c02041000075940d5074810f0000d500088201c90b0700425103690f419200e0300d921507800510300c80081640c00c000c5051100b50007030b204a801c09801072021031812000d90006130740080781140c4201148100b000a211421a21000d081d0491040c0d12003a403600c1810390804071401c041e24031103072040c810041d0706491040014000d00d41549420041548001c60000449100b1a203c014040c1066201080104200840c00502101580d00c0401113a601d580101c0d05500452400528440280380103100914088441c05002845001d010641041c599141e50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 115919838 1250 115918588 115918651
    0x5090604080a1418040606050c03030403030f0902031005100911030a0c0e090c0903010b0a0501051803030903011d0f2a150a050706060e130b09030c03070309030b010906060503010905 80
    0xc40302d2911070780e0404505d42405010014034407854000e080018051815407a4800a4401020b140c0e440d40408040e0820b50002000181c0043c2641c12440117600c1c2500601001c4424141c019601000800c101c0790324443c0c2600040101c0304a030841d5140840c0b107004041c408010001c0c0580f00d456126140c2c1d42952031880b84104a56981c1c82e40081010316094495090071a072186107800000c0c0003d036409429540c40091880c44190030000394000310342144074012443d03800d5400c01140307138000020b00301c3c910301201d401d0302101c4400c50180402903c0d129085104c500400300481400f241700c1d0158500181802c0042516013600d1a100324080107511540032500810340204092062000c83d101c0c0100500450980c04940e141800760010986522100100500a000080355041c0010425545204542002c80f582d0f0125802c01a081c21490312045072103202c80700c00403c044180d40a00b40031075525480d09800c507420800c0700c0001d064020302d810121604001c070411480f00034401d01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 115921088 1250 115919838 115919857
    0x1b030604090f050a03140301050f0409030908160305070503010c2106050307170c030606010e0d0305090405040602040f08030f070609030509041103070e06040b03070c0c12051c0305090604080a14 85
    0x18240d4650710700c0c02400320b80c02117101b004000414401000551542c0707c00d450900d8080b580014246214a4161103211842d00000b02605c43e400c40024484040c4810b101505e00810845140f10340d00c400705800e17240b9541d22040003a003010000040c460390500001c59403002c100001c203806480d000842d1401c030742503221b010070303140144c840d840b81c030424032038110150304c258040d0042e4900303030001034150b0010b90a0355003c0e200c2101b02005140c811070a840c085500100107001500b00f0f424404040c2d0040d009110651070310f148001080d070b900008640d0b2801e0889070240c14064070303881e00f0000305455001901400810001c0003030304d6499219031800c01e9900c0f000e44d41c50382031800e4020a20f1842c0c51205015000030003061201c0e1143d1000e0340d52002503482c010f4000c290301d180c07039000402e040d40100100c1f50009525000c10101044110440e607841d400d0740d4155041600813030030380380251031000c2c05810001c00b207400300f4807070300040003405001d082003001e10001e88541c0c410342d800360303646 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 115922338 1250 115921088 115921093
    0x303061003090f02100207050a03060b10020d08220803090714030a0807110d05030a0914180a0902010201020c030a11190302120705070b0c030912061b030604090f05 72
    0x8100051a10515080300c0c480d2900d020000c0701c4442c0c1c0c0b074084400c0382c0b8001a10540400d49070350030b860700c20081e4001820002d00500d030701c6540e80c0344c1040030b0420b64000501c10b02c015200104114400282d070b00c86020b803540d4400382910341c080c1c0598201c0c0c044003071504011303003400400045008400154010084480285000745c64040e030f0214400303112882d0352103a0001d22555000c0b0f5082d00c15100c05a8012000059221480c000a189100c51200080460001103500c1c8101030300074468104032030b05170356600c140c0103080c0300304900c200c800c0398424600556440406c40b41d540070b86c031a8100c5841800010b01c0c0522861005141d0b410000050380082e0748000210b940444c144070421010380c0035146404400400e6034003079195810b15103e2040c0c20f1010030707020107200003082074000401001d10800d988117072400045440341e000d0140b8600581080c141c464001e640059170710312801101711300e002003241300c003180301e050352010741411b502a440c6c00e880e90129651480141c2e1b028400c500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 115923588 1250 115922338 115922341
    0x70c030c0605180706050f0901050c01060807080a05010c0504120f050106030b0112050705060a0504030b0c09040204060e010e032802060d05010e061c110603070c0c0b0a0212031b03100801020a020303 87
    0x3c0d414548885a00700804010382405003210714240c031807d40b40032010900b003103500d0b0000348041318014210396205907003e1050000014002030f000c02c1c034035182400742e8000d00c40403c290360266450700c10381c4910740a2210500101010806900c1401c107000d128000115002d039a98a401c0003000d001e81041000785098400d1f501005000c0001500910380fc4e520541884404440903140d0302492002074503002c0000002419089580121160755600400464941d91581d000400740100f02112a0104006150300308185c900003d038000c0440d808001611030040d03004d4015181ca130400c00c12138100c801804481300c0354000d07018081c040c0c00e0400301d90b04149440780c100150200803103a10307024070084014001c0810024a010600c1d0103056407903503641e40762044201c800c9a07a4950143c046c117600c40b0081950b0318171000902e0b00f80310503401c80f01012800c402080d042c0c44155140f00b070f4154020b4900c1104503114002c0c580c8072030340c926018891940c4006207400da07446072100d800140c00000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 115924838 1250 115923588 115923631
    0x40809030d080f01050609120d0e041a03071e050310090201030b0607210e03030c0f07080304060203090d05070e0c130e04030e01121d070f0e060108070c030c0605 71
    0x1c07044000360a10318000e1580e081141c01c150074032406008603401041c001480c5807158842e0b04001e4000002c040840b07034400d00800b80101042000f8464074855801c0511110203244c208178142104040100900078191408207003a007200704083c00080443c410610011359641c041c444190b410100003008212000e1501c0010100c94410f00e88030f01c01d078010700111003c2a13121806030400d1408100c429450640701805072054800007968a0345031000044c1c2081d0f6143c040340301d4180b803031103c01303c402c4c0315125a8800d071240107901600e40140d00c01d200181151400046881016000e007083e42d41258885002c0303c444103040710509504840001c01c1d110010020b500c0c4802480405020080381c140b0340d80003804120000080382c10442c0d9007081c1101c1d24250360242030403500c070300042c1c01203a107060b074146d403109002e10802441d83e01e4644002000385400302d5140c400c000c16035444000b69a055000e43c0d01454822090b1b0800641440e84000184a031007401d0103100c0c1c8640a03022020b120 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 115926088 1250 115924838 115924843
    0x9020123041e1a03060609060403080702040b06161b0306060303021c031104050105031506030709091503020f100302070503040b0405030d110d050c0a2003070e01060804060507021504080903 83
    0x520030420403404489042202c09403d600b64103010000150041e034a8452100180490007100022a4001000140081000b6501d40185451071094809000f10075600c02040650700030020303030341d5081c441c000121000454801185a082d21300003440309125850b84c482c5412940366410850148e4043c002031400f0940e5a0b091200e000307200e103410300401d00a23441c514a107000d02d1113441e040c40004404240702244180720003980c8800038000350344030310b81620000c0c041c900511031441c2507803821003008989000707180a0307001d032500030b4102e00c481810441031150340c00c10302421404144d0700b0300002000a10a00c0248001c10300d910069407120f0505041505007102c00542c042400345400325020712480c00b0a00b0203418600e824203545442002100c2414105400d000403c22200a00021155242442c0091007110103508680c10240c5810018028030400c0c0140b5002c1185400020009880d42d000558015002c0c81964010441200942050101500c3c100c45040c404140000141000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 115927338 1250 115926088 115926119
    0xa02030d050a0c1b0c0311030102160803060f0406050616050f01050403090f090212011511030d0f0e0303091005070c1b03060c0201060f090c0908030a03050603060f16030902012304 79
    0x18654004d29610750ba50b07450071210380c0b403000602852007100710003440e66080d4156000c074003031280300035042d04491410802d1a0700490300c1e075218985894503414981050710801c410380744003914091500740007511403264005011012102441041035a076070040c1c080c01841d0007203100b40c0b1101c1c001e5041014203480c2c48841e4000d0125244140260105000e01e001c0300d50440b000205440d108151941d8100c1d0402b080c03095980041c4030015000f603000055600c81c4440d041040001c12105800303404090701c911090358a403e060b88000344544500c0c5240c1d000365005402030030000042001e66981c030a4a5050160003441100d2240d410000d029690051721001c0c40148000c00c50301d824145401001d185600600f01000e641c0d8441010190003200410060b20066081b25101d103100070b8020003400c001c581e410b000e4050080421701c0c001c4a5200751340914070024042801401e840000c800626012009134100940107035841950308403403414001c5004000c00d0a0354581c101241001c003840c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 115928588 1250 115927338 115927367
    0x1308031207030c0206060d08130e01090f060503070b0306010e040608060402030f0712110402040e0c0315100e091005120c03011803080c0706110f0d2904020a02030d050a0c 75
    0x10301102c40f0720070b903020480700e070300640c11900e002c030110507401c10076440c0c080d940d00c29030100340c070450110345004010000350480e20600030074800140c603520482d042d03480c948102905644600d00c18000220002c02075a40300320185052086007113000b000030b06a032070035808448150841000d10095080c140861000001c1850040044e140f628001314050755404502800e4000c501052000503036854041b03c0090282c4184024903041404a0110a50045d64072111000aa914192039410700440041c109052174075500643d030a200c0038041c4140000746075901c11140301c003020609540303400b100c00032070101800405298510748185401c6415504580492200c4c0904c1e0301c4c0080d900c5618940c0c0910030032100c6440d43d00524060340903105490f07803669810f40c042044442082245d009d0a9900d88040f41800191481d41001c03004451081d45540c900c49804201e5102741400d400a154508151040707a1400c0e0100c6a07030700403a0819901d103a40c060304c501e54018440c0d03100c52450302e00d21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 115929838 1250 115928588 115928591
    0x509010b010c0c1a0706020d050609090a08120711010e100e060c04060f020a05012a0e150903150a02041a0a020c0405060a08030a0908060a06030206040302040209030102130803120703 80
    0x10b540c607121082e4880b80301d1502004030302c600081c5000c95010035241803c0d07002c03909640351880c04211201501048075114041c10034000028007100c0e0000d06404116000518540741200783e8101c1d4014030700c0104100140300c00b000c0c000c4041c1000b480742d02403038070244001d090f0524040041c041690803000c140402d550100b000d10200c0e22000c0b04680444150341400c00c0c502d89801c02c180d0030050804005011540b8103d03285124800128104400300364092240d0959070302c1c49015039151200140554000c044909028042203aa40c02080460001000c5581c01682d40d1612104102c04039020381d04182c0206040011000e0010308510314403280450342e051920303840000f540c0b24030300c0c41d9440c0310750f458102242007516203041e020054460310054031359910b05080054080301407442030680700e1083e0b6002555400c803a00c07440040d65030050109181c11f10319001c11000c1d410040c1003a50555080101e13000d01c402e40030b041002003d1142c0a90b440f060f000e2107c1e095410010010414076 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 115931088 1250 115929838 115929857
    0x602070803030a1d2a0901060206040201201207060b06070b07030207111e03100605060f0c0106151812080708030702010f0507050c010b030a170c01020f04090509010b01 74
    0x5480842501c0d440a480000020822050482c0c0c0d40400c030342d08240707040c50155400070500400c2c45c00e04e403400103010a045100e03840f000d4041c084100024460807005070020008035005621400d14803003158054540c1c02031080614580c00e040070504204030104e92000910b50302003140500074605681c504407030a9052801a40740c124900b04010042c0080550005240003004800c0780c9244183c2c0c03014050f82100d0341481910f01005008010207403092041c84515114540203000711006d80b400a454642880d07811200c141064014400722051175480c1d00b0003007038000b0b1000c42141da641003599580768800c020b40c1c4550031841c0642000751903a82c80c80044000ca8854800c40d24100c0e40190103a50b20394450307004a00500304001c2c0d01c031200e8209024050303000d41c440d01504d00c07941e680c8002c21100c3c00d032034109507031a0038204c030091840265212840460f210321000e801c0c05610a0009031401003090300700813a40e4410f400c5880441e81d50002d2100440c02482100201071080c02c00310743c1c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 115932338 1250 115931088 115931099
    0x90b2b1406100e0417040f03061401150e060405090c1b010c020c0f040f090b06030d1d04090f050f0105010f050d02150c010204090608030903120a0c020108100503031909060207 77
    0x1c0d01e0060140c0005903d404020604010509107607203040b130350320510541c841c1e440da1000030000c2100c0c402036400d1410001c2846032820103d5515048420301d088216681d841414150b800d00409581158490000d00c400241925060b0001d80328452451106907a90030b440d17a08441600b121714490401d170700d0240081c100340e40028801c02d081604807000d4074003428101c0041e000c2c00209030480903540c2414680c1007001102155903000e50001c42c1a9200c42150080413a03c802d0825010000d1421202ca405810b08090f4400b10320030f8042c580ca003c41001b25258030707150941c2420185407980d902c03c0108130840c0c00c500c00c50064441180d640001c8890341c2c002a4a4540549810707032a070100040d2040038034400d5048800030b0031210801d04c03082e42e44248484d1260440c0c02103a0080c021600284080c4042c4800c41d4030010b42c6032a080b503000025001101c1d9010010b0101d80d2005041402040d00c0c3e400b04064180030007602419000c10802240081849283c0d9200205641c8140d506202 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 115933588 1250 115932338 115932361
    0x4050705060912030d0c1d03070b0906090d080c0106050906010e010f1b0501060305070608040c090b0604030f0b061005030915090109060c0206010906140a090b2b1406 73
    0x112102111060340300c0c20b1070400100c107900d4002e06a103d610000440c0241000035400518400c0c0c2c03d9103540c41480c155041d000080071904000c0c96054101c04e2040c800886083c0c054601c0070340140c000c03802c015011001c030b090341d500f000054810013000709510340010403d002d010060131003a07030111540e0134480d002901d4408850034050610011010b46051207106680c1d580c02c500e600e540b0141c00030505c0c10003d0080c261400281d6260080c5407000c100c44e8050000107000c0c641c0004a00c1080b842e082c004401445900c041641c0580d04004c0000452840482059a1b43c01609071840b00d06109040100318101c2c208800c3c240039043c0100440c148011130364409081034101074000903510042101c1c014803c45000400d0140303003035001e0700642d90000d0308034103a0300030354820000c05448010a84080d0f2000c00380e40d5000300c2d200001d00041c4503d412404400e6006031009100300c9007498441c0e00c0845031031180080c0350aa010740c100348200c40711044014059000613080c05e00f003001c2c0c1400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 115934838 1250 115933588 115933603
    0x715050f070203071d090a031d0127090e0d0504060c1103120c01050f01030203030901120e0609070608010807030f03050a020a0b01090209040c030522080724050601180923040c0504140405 82
    0x4a40f143d101030843d0290b401106208241501f100b0440700c4c0e1042d812f002c0d80e001c410340c080c02c0011842d25503142c01c0290002001062085240c603642d003401e01c1c02608556140d26501c007256042441c00c0c09100c1030b10100403621445001c001d040d5103501307200261034210b810042c04208041d200100400c003686011048810502081c6008188500080740003000b628049080c138030a445010100308881002013081006c0d6011070752110010b99880c4800e603590800740c0006401c0b1a5104048000240584000c00103001d05005036200014652901c1c038014609030f10403480d040d00060304050a2510b44561010035019041c200054207003542080c2038803a41070a21301004403112071740780c20f00003030b070781611825680b1400ca414240005600d428a1142c000d020301c82c40c50070722001c40c21301e42c051520502031301d010003458651949400c0d4010003901110041402001104003070921480c000780c0300521030350042c00d821064514000900013100c22800d040704210048009000024a002ca40072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 115936088 1250 115934838 115934867
    0xc1003020d020f030f18061509190903030b10030204030f060903030209030a14120406021510050a03030201020319060b0304240e011d0715050f070203071d090a03 71
    0x1611420080c1e490802032003000c0d2038103180d02000c010400c808240940c0540b040c45010401c0f8003801c1c484d4800303640c45400760340300c03074101070580586e02032820310078000d582c807110104a00600c004400e51540459408840503400240c81e040f80d50198204000070064042146c507085140600c1d40e2103002074032801c0540104410749070701190b070074184241c05441d1503070001000d580580c009444e03d1001000b005003124040c3c080e041c00d28041102581c203841c03c0f0b0302c040e00508403a5540703a03c071840e100c600408103041406801c0303011a03161180c0f54030402551003900016600e0904600d080403201421001c044550b0414409004200d40d203c01c1c0c0740c0141d440a0310035200043e045400890582417a03070208510b00d05600c000b101c80341504625074071100030210b16402500c60585c5a1110043d01510250782c1d40d85101d03050700380c4140d00a00c6041d115035110b5007010001e500080c20300f52680d00819607801d1121f5864030204041d4a02030f041880c1038001c0114a9141e900501642001c0080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 115937338 1250 115936088 115936091
    0x1080f07140406080706050c0106060906050d02030612030a0314011401020a02100c0f0b0601080f040b150a0302030f030406020609010903120203060d020a09061403010b030604110604030602030a0902040e0c1003 92
    0x14009602c81d0b41010380509400c0c41a01c0c0150348400b4020401d8000b03403d40f400560030b140300054142e00420903141503404e01c3e07940030302d000846890b40340a03502c054145900484401c0f0020a03101080c405040840348590700490715950100c0c0d4a000340b04182c1006455800c00502041d2a130f0b0005403402c0000e50699203442c0304028500c0c252400303180400098058040c1441c081c080004000201c3c0c032805098031042042c0d1a50071a06c40e00307081c00c0758000c08412041001c50060300002054009800c1700038230255480d0b86039408203041c400311207180300d00c542c0003080500100d81c040c49841d07484082079008005541c0c0070b0700c2c020300b0900d40b540b1540045e40d00201241040e121009450016a00608425a0303255101c800c000144120311403240ca6a42500c00d101c060702d0180184e409121004000788041c2d00d8946070200c0d100c1c0d140320140d0340002c040000100059490010714072034010040c0c005440313007ca0051005440c0300e0a07d440c1540c0004010303d5082d03848100c01c4442084a250 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 115938588 1250 115937338 115937369
    0x3061508070516080403020112200306060408160302100f020303150105211f120b090c120f0d0924020708010603050106031403030903030a0908120f0405010501080f07 73
    0x30b89141c400c8004116000b540032401c0014030214030001c0048a1003039940c41c0c080d00100c20740008807420035030342c60818800300300c00e100340c401118041c68001384020005032516995962484c9841a0404502c1070ba2204107400c1066240134441160058860300700469a60704841000b900d901c00100818042c4100000502c241d91051080c2c82d11980c0004c09004102003c001e400e440280c01c0700d448002d2042c0e8600d448004d41070000c1c0000b01c60980c11150b4000d0701c1a41c0b0301145040c001d1450109214100c680381c429039510340c0b040d00c46a000c07006080854075496850742004140e440c48401c1c080002d50401440b0306200411150300704c3c1c040554042c2c2540030040317007009a1b65011013295802d281d0048284141940100c007200e225490711070207055403003074894036400116804800ca8005000051040c0e04d103030401aa55407041d400a80303003a031200c101880016090b5080d01e141a4070700304100800c4001d100796070240c030055005100c1000c020b1409a03842c00b490040d18a01d50a191 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 115939838 1250 115938588 115938601
    0x2090703051f0308030a0c0509060a14120f011401210507021e030c0115060906080a020408100203090d080405120c0a05010e01020702010210060e0622050906060f0103061508 76
    0x18401c000c40e07055030303101c0b155a9030308082c209508207483c4984802e26200ca1300f11442d000f00c0440358060005072600d8106180c41c00207480450291003070745036181003005000d82c40c55030303041c0315403003101010240d01c019410040c000c02b00c55031885000d03050000704500e104282c0140d074104080344c22070b03500101c0d15988082c800c90505044011407200c8010341d02d101e80202e000403002e400d131096514001c01009404101c40504200c00d4400c200215900780c2c0248152403040b002294000132840015190680d40e90801c4e00e0300a1a1b215218600d5012040c0310b08910b00344801c803500b100c580b41c1242503040c943c0f26651113040700182410b681e44d001441d45125601407040b900c400303401000030401e400051340054042e40c04076804034014020514404103c4150384242000d85410340b103040e0081c0e0743c01040c00303401b200294883d2203902c2d01002008061a4600900d031040b40c000c0c02801c840d042480c28404031005481c0814141410200d0600c0000b01406500200c6030291070030311403684559 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 115941088 1250 115939838 115939861
    0x2030402031f0b10141207180f060e06090f040203090c0316060206060306040309050409060209040507120b0f13020a091a030105090109291c0c18090209070305 70
    0x900c0d0402c503a507107201101040c40030035401100341c1d020544405422512640c0100d44c0300b0b40f50301c090404200140b002051441c2c0d600c241c1da60001040c24025201c40180944003404081035000b441e12071424182401075983c002981c080001084da4410304043c040130028035201c6070003010a004950200008044000030026284e22010182c10b455902c500c074030588609a4050090401601c14400800c100d8200040c140e032041d6015990030304800c0c01c040412010b050361102c20740d00305070244500a003641d0b03144580350055017540c0743d82c0c0c21243d49182c0c0c1c0d003e4806594040e84608040d0070100115210340c14858000c9280c98030050392000302000680304100160400100200c1204000a0118203180114142c1d102162050a560390341c00c40c590542d4150030040c2a160000328030b9810500500d458032140d200c000f083c0d07207508158032400c00d9500d86510002e44000c7d00404c0c0804c482d6016080b21903c2e02034806080c07005038003a8020400803480030300580209985e4100240182500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 115942338 1250 115941088 115941103
    0x4180b060d02120103120804050d0c050a021807140423040906090b18010510051c050f0a17030903031305010e030a08070e0316060309060f0c030e0d18090203040203 72
    0x60709000c41d210041c0e004010000c4100340000c403174900220420000300c3d80180141c52040398040020818030f108400d003103407a0104400d0440b5070703202e40145400140d8400710040d14424420603009120b00d840b5000900d0318122042210444808200c03c2c070000c0f0f0b0800141e0b10740c00403064007071400d2080b903000c54024141000e014001c14580000b8204101e5400180b030f00600c0c81103e13803980c4200803096039089810648190801d45044d0704c0410890070a400d844029508022900c402008a5100c50b07040858860074014503411045150702009200c150540c021005041d00c541585005a03c00c2e81e17a200c00b829072090b403641282040200301d82500064424600c4005427900e030060703c040540000780c01ea81140103e2481c0000300340500b00054070b00490345440c2e401115882c9040743c00d030001c1c9000c803801d503120358503030880300140102c0b8041c1c00f180d00c2050384c001074030849444080341050542e1503414100036183c0f811500f0241d0209110081e903c4901005a8030f45452000070f151010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 115943588 1250 115942338 115942357
    0x1b01020633030a0c0b03040224120a1506020c0a08010618050606070507080a0c0909030e060f09040504080c0105010e0f07030f020c0105070e0a0b0703080f040c050a03050303070f0504180b06 83
    0x258454082403808518000c3d5001c0c0b0300c01e0354409d030010300034900c40c043e040710f0300c41442090754240b114104103261500c60a40000e1040b9001490001c00c149402c0401c1c841d410550150f80800700d44025070070031024540052000340000c000050525040d07100c0c4000d0304119412041d100e9010074a156981011981d2250b80403081365009a0b503458540d0f2140c184a206581d802580c6400007282c0c01c1742d004840402d541035986078041d18403001000001d07008079545100d61402440507100c40e0b1614421a4065070046000b1511600015201400e4800c160080854910808103000000e8404400b10f500a8807504011805500d00342540e0024021401c80200707079801c0100780014503070030500340f141505d41601d080b904551182134560091084010090015111400040090f08405070705604031f40304040305a10f540c1d0301c500040881c03102d0340060f19540c0001080c4070040350019074405409003a070409a0409244c000070701c10008000300300c00001603d954160405543d11000c0710a61709 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 115944838 1250 115943588 115943603
    0xe0f0f03120c0f060c04061e210e06060301090209010303080901022a1501060504061805060c060907050a0f05040c0210020a0e0103060902031302060a111b01020633030a 74
    0x2101129059030364090711490b18050103400c0125a50505e9181198141c400e292a80c0d4280400c03076001d08038000e100f140c0070f01001305104403940c045410300b400c001d1280d0004030224031100e03000795035401d080c00136182a210f0707803400c001c1100507103824a0540c1140e801d81410101aa18441c0030b42c061312070b221001c00c0804908203041c070088210500708500c030100c2811100041c0c00c140034150341900038082d80002c03400c1800204106c86c8681d00c091111000380c810010b81c80d0f55400400c0352900640b6800d401c5401c007000b0000d138004100500401420100d03810ac14192800e07008007013400042c000c0034000c544407000310480f01c0c000c1010302c0306003503c1e080c01c41d5a00826280101008448210a40020b0800000080013842402683d000341410014201a5401c035820002e16038060318051003800458058082216400d01c0101c80c0d00008912f0118014190800241010360041c88001003c01001e00000400c928040113040f43c0c0100d10225240040280081d00c0c0a02c900e00081040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 115946088 1250 115944838 115944847
    0x17010503192d0b0f0c03062403010b0714060601050d0c0201230702120c120901020a0503040e0a05010b0a080a021303020a09020703030b150d0513021e0a060e0f0f0312 73
    0x70b105829000100300e0041101d21a151100f44d09480302860a50b86200004404e002044d00351905800396410a030704404d80300c210900459aa0007a60000d80c8071061110000c9072200504c100303000030b8924003c3d4100038140925203400043e140340640c0080f4084d003580d81c405110710b64002d51140d40444100d403074042c80c0b00c0d4040c1c11203001a41c126404401401014014450510032100751f0b1300710110306001e80000040d2032803011603604804080da04502c0f840480c8004a407090000f017003c2e084505a0105502c0c01ca40e13940c0a550040c0e00140c4c171a6800c10040403420350251100e5004028120090b1340c905946000750303040031490700040e40c0070041802c00941c0d281c82c0c3d4000c01c2007500ca070700d0a20107525000100a1056040c10011140001c00c01040ea071100407540040d6000001c1840c0e109106001c0e000f08d006030244403034406000c5441030300b2082610f40901100700820062603c0d890110880340850900c041c0c0200752406044401509030700c942d014004840d42508135030f01107488 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 115947338 1250 115946088 115946153
    0x30c0304140a05010f111305090903070c0b03010302031203041e060f0608100c1803030f020114070c14011a06070c0506120a1401030f0b070905030d0306061701050319 73
    0x2041d42010500d1725520b00545041074110b02d0342a02c903039054203110080380c90300d04010b00030300000041c0704041e82d02040007100e0004103000101005410751043c165280d60540c810b15141c185500461011110b0600400001440d0007a500203070340c900c03c250724825503241c50000060059288151452401c3c07010100310a6070009001d003c0b80c20718101030056038400c0c001681c20341d40e103001d040c00900c008041400468040c0d2502c1840f600780e4070000403124640740d41c142e601d010540b0000001900b070140350051040350f642111180d40800001c1140240303094001201c560680c00d0240030f981e02055003c140012556845c00610011f4111170750b50501e44c02085071310740e00f244c110341030624240100da90070414206450582e0750003244003000c02100e80f1041d11500c8001c0c01c02c005c105c10000040380d00d49041c00248880303002c0f41c9000c2900b0b81040360141001134400d2140481c068020010029950000341140903e08081d40c0b14044a425041c030580701100390360103001c15001c20061a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 115948588 1250 115947338 115947341
    0x906190c02101e050604050103020916020a02040903050a0210050c0315010513030b0f0c07020d022b030305090f01020702130203071206030c1706060a05100c050703050f010b060f030c0304140a0501 86
    0x11000e0f07007994104600e5580340308200c2281c80a001c081d40150540d00000e58074074556581c3e400c03070840703401180d81448455002a09990003030a00300c0005801145180310a90100410900000d00140c14005842e0001c00440940001450380005541000c05540642d01800889098081c1c03c3d0360900055160300700a41710f940c080c0c582000c00900080002d4100180354161184558010418000c00c170480d02000185105015403d42610b0012040034100f00240c48280380705107e928080307018a0304203020360070b1030216010100030b41d0041000b4401651614216040080305040058403621540303800c40302422500002204603181040100034400088505011141d201282c1c101c0140141500b40c2c6038081603a6983d088181100e06011500d0030b40e03681e0700800b2607031034106144000740d1a02072825825600c1550603030007440302001030b084207005100d48844140c462620309a081e000c100403a201c0107140707011051021000c00c040009005014550150341c40440d02c0000322418510b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 115949838 1250 115948588 115948631
    0x90d060f1b0807020307080904060506070302010906241806050a0602011a01090302011b03021c0e040b06030708041101030603200108010609050a18020f0a02060108060906190c0210 79
    0x840d40c0307070039000301e110051095084a01c10380c400d038050341c01c2c04050341e601200c0c1c0c1c12045000740d12a0315542c0101d22900c41c5405409000e0290f07001040c3d003052410000112002907040c141160345c044035003450f0100d81000c0c1011601c05615407010b00800d401c46100500054226035448411501c0004031550705400c60304848440007082c0a100189000644014040d0700c0003e0109102846140303400551004e1200c4450081c0140c0d21205041e6000600032042d68108002140c848120440c1c641020f20410300204400c0d28128a50b0030000c0e00a403011600400c020222080d400a0a441f03900c29000b003030082d6070000d4058107040c10007a00300c01c94180144000e000038280400000ca0074407983c010301c1200ca02a1840800d1820080c401003413a22841140d03241940030018642068410001004440d2041e409840554100020300b8180340001e82100010b038444020701012440c00c0d4081405000b50010000d11440c0d618070030703410300515003204100d007480c1c0415004200031503519070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 115951088 1250 115949838 115949861
    0xc0b041401351906061b02040b190305070e0106020309100c0b010906031101030606050a050c030702090903070506010b09130b13050702160801110f07080d0603030c020f0d17090d060f 80
    0x6820040059210804131103880c801c5a00085921a050680c0e140ca0105122a980041c00102e404819800425050120080c5003e00118890000c2040c481e06018500c05024071076041210340d490404020740e2070145072504c0e4031078581200c1303c001450081240c03c81d003940c8a60100d00d03569440b07201000500e1305110070b8410084004032090158403c1c8210025036440e521403904101210b10220f80315001010f00c0000e07840f0410002000d651042062441441300030015a9140c0452920318148401030380b140003114020b0000c00040c0e6500d090031110164014000101d92a81800007182100c0d03030214821003625001c28003003610340c003103000358410b4601d43c041820541d9910510b07007240d6021034041d07901d40d018400c041d1803040c008001c10909000f10070700781c2481c000c1d0b5100011520385510850201d40100050800c50900300444008404c04450082200030603450385030b004c02d414009847c1c030034000a40703070940c1d640b401264210550049404c1191001c003046080083c45641b520 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 115952338 1250 115951088 115951111
    0x604112704030f02060402010c03030e0708010e0307110604030c14040f0507020d0809150103060b060c0304140301050f0603150406020c0a0f110402041503020d061802070c0b04140135 80
    0x30f42c0902c5000289042c0519410380d1075245620064400310000c001c514208011402040b2b00040c0030782c0c0034019034032200840d42c0615603c054500d08546c451120903070b00c0d8000e40c410310081001c28816003881007207030700510038404a002e035540000d00404500c40c400700c0d15854030040c415480c0d0f000071144110140e64071182803c3c0c071184402c41d81e890842c48460020b218000060001900d250461410260301a190300d08141a40c18002c0c1990841d40140c0005804409019594682401344d685c12150908040896090007000310b41c032869616540c0240c000c0603000b240c10084549c1c102c8211807400002c0d10750701d052906e0054000c4a140b00291103090468040e1040c41c40c00f4422281241d858412a5010010402080c0c0c069000304450050041c1d0710180011440300c511140910328502e080c0042e03a5100720b2a18031031040d0303503070091200b0107030601c400d2000d200c0340d5400c4415070000342001c0300d080c01075030000054412604080c0301c14481c01802c21040e04100c5c40d02034081e0980040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 115953588 1250 115952338 115952357
    0x40621050d0306080c0112110304050609010c05040b0405190306020d0b0109080f0c240703050418060b090d1b0e01081c0c080a021e030301050111010608060411270403 73
    0x404a06640c0320780207612645d0482d182c001059800b4aa2401d210700264802060701c0c4030b041420852504100c5098070207030030038001c02920700402c1c8200b0620341500d081c150f01309030a02e003d91400e0f014500405004400c1d400c00c4645413898000540300441c1c0c001e406566669420718500094519003a02a0229024a001085140380819241c8544c0c691000801300b80800710300300207001100c1d20848046440d1030f401c40740e403601508001e11300b03035000782c079002d95480c03411498480709200c0c999003401e400d2414800348848100c0da0101c405c0b1010072201c0520490072424505c01c2020071039803a0002070300e01c0100203001500c4012440c100d45070b17841503d003682e02c40c0b11224983d0030f402d202040090124030b0700c81c0000e110b5501606070500588102c80d1010700001c001046020b074552031055946c0040010004d0350391000940c10039070f1020000b40240d500d041100d590704c90001d0801031102c0c44403407840d40d4644440006c0c81d204100d8442e00c0c00e90316000d51700c051030f0b40da00f070b503081d00040c01040c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 115954838 1250 115953588 115953613
    0x3022a0706180509040b0c120703050f01150804080f0f0706090219081207081903090203160308030f0408090604030b01050108060a08150a0609110903060106090f0b0904062105 77
    0x203410b20115030016103e031149a403666285006120000c041060a040034028001a401a00000c134072904c1980c034005601d0901f0352141c10b00390b20591000c1c912201410407555810703480740d0b8a541040d403010085888101036401c440c128050000c0004c031136200801c0c00c106101c0c0940103a10400d0081d15602d90011114000742c8070701d00240030b2050564407a108000d02561100000c1c04071500580c142420071402c422801c0d0000b4020682c0e500007521032407903070305600c0d003030001a041a080b04a0f1066440c5156640c41c95804021702d80940d12041c1000142031190400490b00e07081401012107540b20307182d2400050b400402c7c0902800a510a4002003d50601c00181400d503111180104801644501c00c0e80c0d20010061050141c252110800103000640b800351096007074580700c040e0317214551041814038150b0305900500400c14004002c11440e111442e0b0034040c1ca0410020590312000301010801404543e4080e10000c2c0800c10b100c00741d5505c00c09010611442401960040f44024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 115956088 1250 115954838 115954877
    0xc0d0c0906050d05030f07030201110d0f1b0221040306020f0408010507170a051f120b0a2a0201020c19060c0e10030b1804030509010912080a03022a0706 67
    0x424004c10075481007080c00c80200200024007440d505c03c1c4004101c3d0064240030311a83d800c0122000d0301c076900c4015400d5085090f01654480b078240380070043c14102c00c020002c0d0703684404501d44009203010304280030688a0101150051908107005565800380501c1513511a0f0191041080e80e504e440702040101d403156286100e42101840381d603429450311105000140070107000054841900545002d151000001101c020000004007000300440780c100340201800c001e00700c03c10b0600e8031880001c0700824001108003c01462204000b1b071202d10009d80c02441180804003c40c031030702800c101e240f060340c85110980c9110700d07024001c40025aa0607241041c103480340603032004040418460091081e8030207402400018140ea00111020408000240043c0d4007039000480c0020f40001550300140d80300b0040c50b921564900e07443c0079844480141c0540c030b000c6d204242d00020311041502c0c2c40400d01c188500204010303400740c1c5046501d107070b440c80e0034842c2801052002a516107e403042c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 115957338 1250 115956088 115956109
    0x305040608090f030d1a12060603010b0603090307080703020a050307050610090507080114011701030506040b011e03080f210907090209030705061b06070e03010f020306010c0f050c0d0c090605 84
    0x2243c0c01541089101090440581464070054141e400350f04580c40346030342c52100c4a0042001c5d04050402801c00e40189802d4503840031000340201c8041003440120302c0300000300c4400303075041015242c54401030f00d02242460307000c0c080038005110215030882030102c0811994081c82e241c02c51403080a60310352a0400340d803030849010010510b1344c0010005d03e034070b5403176003a100034052501c1000211003c82401c495002a04150b48a0344040d00308010000e08141c0a405840e068100b0306040c030652560305040c8100d400000c081410100710792064480c07003410b4030038092640700114041e400541c58007204075022100002d051060b02c0380040c42c5441d078800ca84880700d0140c00380c0011810002400b0b610303408a40b003000e01a07400070144904290510800c2d000c2c8100b559410100c10200041509450a0340c404041c040d104009100c040d0fa085500030f0419644800e2810001149081141c01d180c01d44402d580c00c6517240c182c0030100607010301c001c1e080d05c1e114041002440d84407030074421314007507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 115958588 1250 115957338 115957363
    0x8040302030a08101208040e01060207030b1b120f041a1b03090307060e0607020106150f0c05100c020109050609161e05040911240415120207030504060809 68
    0x402c010300d00c0701610541d4003641c80302c0d0101070304001d603603a100c2e100d1408100c50001d1350a07080105083c001031402c0085140100024401040d1041c2140c9458440740f2010308145c80c000ca1100940045078010416134540b00c0b080706041d10945850031210007000b00c00c035011601d841d40700304480241e00100200782c0c001d0f9440d10f00d001c1d1082140d00c1d210220703440507007245414031044c010385001405901414031080020000b400c0c050420391301c040e0035901c03250030444d06c04605007100f02c4500d501a060442d041028a480c058011050505a00f01880c040450080c1c0e81004103201d609601504400b1141c0c2c4614101d811541d104202c130740c1c42d19810080d4040b82410548100039002803450310300e007064059100c070407069a90701c002400300d0307241c90401c8800c0ca5103041c07403000c20314103680c03404517148042c0142d5200c60743c180340f0b0340791900c01c40c01029000d94080c04603184180c0304428512103000700c04411540d82001d400c0150a03508a4402c4800099449000030340c10f050108500700d4040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 115959838 1250 115958588 115958593
    0xb18030904090f08032e0806060f010e03070e1807140108090f1c09080c0a0b0f0c1218220911030a0609030212090f04050624030a060608040302 63
    0xc10000400001c0c0501010079141c84030381106600114030a0307001103009036050002910001d12999540c41d025000c012105908804440c080010b400b011030f443d0b03804182226103004e12200100143c5204c0300b41114660907110701040841d422422503216130188100046080a0707241410f22990317503116034041c401c1c030108907c80d807a03e2075024150180c1c201e1002400d071a2a0820600400c0c603114040c1030040002e4240c20f000040d06807c04150809081c2ca40003902c490400036003c1640e9205501c20540c54010024407015008160b1040d074000310241d1055a03081c44160f1b07030200e07480d0403543e6000c001030310000c00220903262003980000c0095a84490300a4140f041e01000010010040140d0321900d08107507901480e501804580002e0340f2038a070000b01400d003403d0091901860742e00c0d03110034400070429003083e560303098071043e01040226030202d600c0c3d4030b000114884100c28804804c4403003450250034240e07940318000e140715500c0030710200801c40ea13424046550700d00680740034001d43c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 115961088 1250 115959838 115959847
    0x1290d080901030e030c0a03120603021f0201020c011a0f0a050312030402030a0f03030509010606020f070509041505041212020a3c03090212060105030d050d0e010c0504030b1803 78
    0x121400064454070405040000701400e10141d100d0031503014020317000158001b08404410181c021001c6d0f22900b02c3c03100204485400e50340814444040fa000c1c0c1d001951520500140e100c0c0300350105c0340462034400081c0070b1481d0744114002d02ca00e08080703151141301800c50700342050401300150b50450b00020000c10210448440c0300c105a44060400e0b030709806001001c102050301c41c160b441c5801d2199400292615290320310700e08441103a007201003190030007000c1e0f448108002a4000942e04102c0c0c3c11510740d1940c3c5003802507140c000c080300b241503092008200070b100c1d044000843c0c600154541124000808080c0f80880c401e01100001068003070050000e4070008450040305602200c0341800e01856020310107101c5640784036108000f0340c54502c03480460400003d441d03800341c8468000d01495051034000390311025441d045d43c08101010901072480202a0841148450781c41c0c002c0090340500400101980d0081c0002d40342d01d00b030381c4007254101030011626002c03010050080c5003013 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 115962338 1250 115961088 115961093
    0x1706060c030a0503040c03120e041a010f03021809040c030311030301081c020f01060e01090b0607120f022418030304050703142508060903120a23070201290d 69
    0x10b904090015030300450b146c0f401000040004040300300c0b1442684460080c00071003010001902d001204091451001c04074810880e600140074030705278101401c0250300c0b40c0140c140c19080e205c8403805254001e030303d002400140001d2a030b140782501e0080c1d46130103411702e0a8101c9940d0303200c00e2190306001c0e80a480088200d82400030480406c44861041e11404c0341c0d010f071400e0a640d440e03045880f05a94510040088046d548108000c03248107454481c10302c211616600c01400c120b454600502000402041da50b5109004421054500c84071052076a58100950740d03180004940c0200908038a5035a050310b600c0c000140ca1085034485c000f44051411541d0f080101d00344003074061294810806064403c040b401d41c07000c50094140d0321149000d2810883d10318002001d00012000d8100300070600100b4040311140d40e11160720940030803810b240d0700c1c55440030750204800264601450b014482c440b0780c19007140b61001d8040c0302d58035035495400040b030740451380b0510a0340c1c04030300c01c10000300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 115963588 1250 115962338 115962347
    0x801180c05101101051008100e061503030408060406240308070f05010e120c06070302030121110411130522050615040326090603042003030a1706060c030a 68
    0x42c006024a07001c1004060084420709442d003d41c0e0b407400ca41203400061016060030000031500701a0a07805104082050b5503443d00d800015000c1200c10002c0381880840c2e0302c013041240c008041041c11202c2c189410b04150000340400c00303103444100d07a440d00b071000004101041d00c1c152908030520f54900051580e950300b2400c80030b0300464441d500d951201d40a0708080c866510590071082c02213654030f65010342c85061410042c015070a052050005116022900aa1003014201076001220210f040d062509408040042c4036621a04020350f238040e0360402c4001c0c0116a8194801e5070419484100300118071003402041c4883d51103443c100124104281c0003581c002401520794049030481701018046540b06800982d00c2c80465540030051681000a00c03400d4030b11903414a003400203800c0042c01610004c1d00c080c050303400d10103042e040c0000070f40002d1f03d10800141101d0780d482c0c244d04090684400b400650900c801034000007140ca09204049480d090319840180d03140c2030100c0340548 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 115964838 1250 115963588 115963609
    0x5010302010509220507120501091406060f13092301030210050d06030213051905060303121e0405071d220c090c020303060f03010b0d23070f0801180c05 67
    0x20100280452401007101c09441740340e01640c0c141e95003c400c03030140500581564010707030106105529100703403000764070f141c00c408680002c0c04840240d40d03018001c910260074000c124000e1902c241e0340b08001244141a0f100d518410f82005040e0319400700000c952240e400b0910029401c07004d018409000c040c8290b000f003450118242c00000d1441d01c03500410808103469080c40d05596541c014006555080803114114510340b100038842d5240c030384003182e1603028003401c03544003820794008201c21048031442011a00d41c0711000c20520300d01801e049a80750100d124076480350200d6400c00810f2351403244040d20403200c41d6600f03a0401e600c1c0c1d0311102182210392040c3c404c0302040e000809e610b290390089180b00b0502da0b0085441e070501f141000200096140c903140f1903032408802e84042d880d1500503c041c035403c8280060301c1c2800d6550f0740304014034030391031b032806000e80c0001052003103075243c0c000c0030f4400c0300c0001c01c0104121410b4210783ca164801c090b142d01c620040170409407507c1d00500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 115966088 1250 115964838 115964869
    0x1060302042310140f07050109030207080f03040302190b0703030902090603030a0917031c06080d050a120b010216032d0221030d020d05070e010207061b020307050306070203180405010302010509 85
    0x15458505ca980e0030001c145c2207140c0440301a5101c2c1e4902040c5941080003202406a4501402d003c0203100000b542d40c1c45640720007401181c01d40207409001c400700c0c0311032b0010400c44c008183d80b43c4062400400501c2d05420481c0b19841402c0441e1190500000703940480744291101c0d40d10320304009011000107003124000c0d41c01d00c0100400f0040c00d40101e0000031520316503201182d01c03030500462074100304044040b81d0400c4414000c408203550703c80303414032640580b14000a091943c040040341005020400d0140228400c40d00108000000101d0300e880180c5032580c00806103d99815250580b038600083d5020258a40c1c8102d0340403141d10300182400003d00726441d101030b0030700c8142a0380000074410b1001ea6500b0800c400e01350010903089228070248040c00e909403c0c04c6002e8200503240082c24000b2100b46160011910f0030000c6c08003800e00141200c410f881d102800035500e60280c01d00000d10080038503034800c0ca060900510303050704e50584609090016050030b00001c0800c403800d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 115967338 1250 115966088 115966127
    0x80f060c0a02030d090f12120f1a0112090804081b0a080a140120121302010203030a0e1f051006020109020904060906140708070f0512011a070b01060302042310 70
    0x1410010b040707d035026040000d1034850071039000898034900b003200c02c003a03211030846040c044046241141031075000f034102800d085c0824441240c041d814010b01d4031040042c0744240004000c981010002154029030600c0600b01940803001014049200500e1003020206c0d84103001c0c00000900c8000f528071000d8400d00002281d0643d10803640c00496580d414600781040020002c00c5410301c400318583c02003003602d0705809450280e000035034a101c02451500c0e8640e9403404810810700c1844400b00d090200d026400702c640350b0400740002040190342d45070400202d41c000003402c5006000c0e1500040c1c0040041800d540c0c1d40d11150040c11241c201103601c542e0b40c8490941540e800c0000501444440d07035a1461481c000e0405014844000802c0c3d060107400e20010098820f5419a2815919020300780d02072038110710030a20950041000c0142855081e000200381181d250b0f000c0d10444103884090840d1094101e5030000c403108044e41c007a00042c1c1c0c40c50310310210780201e0988540d000000c0a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 115968588 1250 115967338 115967363
    0x9111011070308040e060306040309050f03070902180307080a03050a0e0d1a0609060d08030a020c0c0a0824041119090e06100b12150d060501080f060c0a02030d09 71
    0x308078107140240c2c00460b00e801e000b040038020681100705a6501c524150018241800e150720003070500303505881298030810346003c0c00c084549091100e000184059082507444050010005c00d0070414901100e00074802c500000641c40e038000741e9071542a0b010384501d46030504006044605d55210b10866400c5014402e8860020303403c6c444002d01801003402080103800c150703040240000d0090000c0f0700c81d0341c1413480400401c0608080740d03006841c013000140d0b00c2d005d1103c0c2c01c0c00d2080219415600c511502c000140c003031030210703807041c0c0110381c41110302030171441519803040440d05541c060710383d203070203880d644641c1041c400d030740e54000104840e80080790b620040c0500f514034001076008240c0100e010310280075a160400c3c1c2c0030b011042e00749414000707620003050303402c40014611a521500d07a200b4201e1511340d00c03682c3c0c1c030301c0c3d030011001c0c0025a103c20005a0f2040c1151004241c0c0c0300d02c60009103901c0b00c000c2a100080c0907a400b031490848000407031000b500030032109440e1a450042d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 115969838 1250 115968588 115968617
    0xf06030106050d03020f070608012616030b04060b010507030807080712050c0406021606050703120b0303030406060501020c01020f1c120c02010b0112050601120f0e0106080609010c0201091110 84
    0x1510741c8192440382e4020315421000301b000d81c1c1422a075502100c28008000c0040c02100768102c00e41c0c44c0d820985c2c00c42070401d6206001103140652110400c40d66103014803022051101682e6020710503070040000380300030302c406070044609101c1c010018002925940c007080c05644203214142e040a00380c82d00400500d04c01456008a54069840042200d80000c1c00c05c2004c2e010300c03074441c0800004440d805000c2c54004050294499904000c00304202c2c02c03807048081c0055880000c070814040d089a89034035003844c100c00100b805005080c0540300d00414140598800a1810220100030001c1c00c0b0041069804001085425080100f4800710b000c91700c0c034140c914414140181d4195001107002c000358400134048101800c3c86000c5982401c003003001c0c0382d030000313030b15814070003071010004841d942100000c00038005040110410750804a00107070f56200007c05900030403440c802085990040a410f07400c80e0710001000f40203030706040c400091841d105d0461161201c180c103008002c0581c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 115971088 1250 115969838 115969849
    0x3080702030a05060a0c0e010905031002030c0d060f03060605040b0f100201020702031b090105150901080c041707030309050406050319020d0b070504030309140105070f0302011e090b060a0e0f0603010605 89
    0x450300b511788140c1d00c501c104030251703010009841071602820203405080c03c100c0401d84a803810319140c00c040ba000408610118031400844141304914013003041f920303895071442c160850280c40241e40c614180140402c0700d21b00381c80f9020032030030001e1038804c04a00c840b041c4000c0042d82d51090055541c203101500140e20140a0711a81604c8030032102d14180c038000801c03041c00c00680040d4040c03408a5400c03500c0d440d00320100e0341e0b510001d08000b503190756409207201c0315100b203801c58400340c0c40000741c04001000000761a8143c81c4640c884552a0307407200300717210488a49101e00742d490b40c0109000005010301c4036120000c80d001a00c084403043c03181e00e8010300c480080e41e80c4000039400140c2003040c1075104155070064003044d02c40228800c88400002d100703010302400a0001a10010807a04260003503000e441d070300110321542142c00b00c840e070142000b801e003400c1c00d0380d0a6022000068843c54400301c541e041e25101d61000445e51114248140d4180300100001c1d0550351340c520109581e6030301c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 115972338 1250 115971088 115971091
    0x30f02071103010c02062a091509030c04110d1e05010b0307020c0105131418090c0109120209040f11060403080c010c0c0201050412150f0b09070e01080103080702030a0506 75
    0x4011107100210312030241421103201c1003c0008541000c0706121100341c1075000c0110003100d2408a4a09101c180d040440c07521501284c2c0b648250701080380d500070316000b405041c00440407416589400c940d68140300980f175055880c2041d00000704280310000c010740e441007140c2441d41402c0c0012400e840803001c1103400a03040000d070100c0200c10002900e0307041103001009242071038280e04141a400c803206004155004007548050012550300f41c580780c0400301c84050702044480501030404042803074880b80007c000900280c0d9800c00800d45030101441d50211070b5014003c6092582c1e140c84103a0103500040c0111174800c0641d000c00c0440e034034100600091030081800c5507546044246550844130000d1010040c00040c010410140c1c1c1c100d000e03907040b1250900140c80e0780710305117043c060300d04070b90b60791020041c0f412513098000c3c2255808104e000344141d81506054813544002d0f92002c840c1880d00303001480400050002501c840d024220080c0301504803006800c40c1d03603c1c141017010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 115973588 1250 115972338 115972343
    0x31410052b080a030b090a0603020a09020a02010f240503060c0a0c080403052a030f07140307050301090c05040507050408030d090303020d0203070804120504051c020f0303120f0a06051f030f0207 85
    0x1710b84a045585280184c111500444403141c104a00b902c0c50f4042075058050788541c80c2c0b01c540c0401c11b482498003c5d0055070f000030a800040007036808501c56900030782a404041078000da0848804074050400250250081088030600c9040c044061404c6540d000c030100102d450590a002c000000350f020006641100c0c2040d084080d118400f6002aa03c4070b04132010314402d900c1505503003e4070314085450700c00d50f00389030f003039100a0311000e000c40e2500c0402d80c0555050b610301840c800030b1041041061003940c030100c1d418483c83d207407100215414000ca00a0000c150070401c881642c00105620111810b4840e0230090700706000b0114507800c980003141c2c501e02003150041000108100c5d0a882880c1d0041401e03c40d0500c0e043c0008600307a0320031300090369541d03084041228195070328440502400d80000f000c0b26585c1484001c07203210a0b10517510000300d0a800340104401c0c0d40540144415204054100050441249013803004c0d110519520420b060f5121260b4071001010300082c8603c60 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 115974838 1250 115973588 115973591
    0x3060108010b0306070306052d1002060402180601080c0a09150806010306060201020c15100302060a0203070b070f0e01080a0f0204080c09011203050910050903010c031410052b080a03 80
    0x2c4064050604140004100d00100f40c90001c2c144050b5880052031030520150180b80ca00d80030b4104107980b06500e01010300341d4031080300400031252035400510288140c0c407d03551003c0208e036114007070000000548a8038041500c880015100341012005801501c045241c5402c40300e580b00415007000e80c1c50220b040c000758000c820044603507014064000100201d01c002c5141010000700c050700d54503080b0b6040e080e01802c20202d1501c0c054400070710059600241500c0e610000c00350003959a0b8000802250188049000542080e026081011007500b980d120212558900e1004589840f0010320003528140d4030340281029042900c003030009484074400401c280d503807200422003020b40580c0821120340e41400b40c0d00c0040d5018099038080041516080c4103240e1144055915018068016805602e0b04c1500300c000b03035042e00856100d1502070741140c031640307030344c00e2405094215000b001d800804000c00d0003e0030f02c16040c0480b00b01d40e130701c2580d91210043e030750319005a4402040034002a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 115976088 1250 115974838 115974851
    0x1112070b070f0614011e030c0b07020301060b0f0a260106030222080f0111032406041a030406050903270d0f060504050610060e010c02010516051c05090901030209060a050306010801 79
    0x6c01301c040e5500c82c28143c25400b480f01c1e0318690b079122812040340940c0d05903043c04101d88045403025005000502200d8a500340c4543d44608010391581020800c0310015030005000a80c0100c0001c80c0d035440200d03204001d800b41e081c4107040d0080c0d407000003014401c8601c4c600351100c07102c40001c0d860103400300b100602035001050303e406003958594841d6151082d400c01c02c0c000c461240140e41009400401200b54404001c4000540103000b16405200000345649010340640c00a800031842030340f042000b000700342c8400038100c0da6800f80b041e40e0381041c03280c0c03450b00c102e01e55160400540030f14028401e4140d001070303540381700b00c07002050411a2203a03142c00c1031204100c4244107003540440040080c143c094501a00204001880c1d2402410b01189080040c1564442c2c01240d2070708071800b004442e130a40031f00d0815590310800442000c0c0442101401c0c0c0382c28400d404075560a28002c18854281c0d0031502003241400c4040e05013a44100d0310715001480e038900740310042c000d000300301c00020807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 115977338 1250 115976088 115976099
    0x8010e0604030206060105040807050f0102071a1c0204120303050402241206120604031112030403020d03060501031509020c010204080a12080c070309060f020f0106090204031112070b070f061401 85
    0x4d02030060308180c188a4240700611040c030300011600c0c12600d040b50080800740c2c0d5a40180e007403040c50340203510200c140c054030010703030400000205601c2c40041c05409d1740310104900f180407802140901100c603203900c0301040c00b0138405d40220f038005000804801402000c0f070030310326260084140d8090b182d02c0116034002482c003019810b5a00920907280308a84206540e0005e1310360780020700c02024400f40e40408407136035400b00000d03003492206a8003150b480c206824041e40d5105003120784c800190801d48042042c0d44a40038503030701c105880418001e214204440003000e5007040e02140d180b90b50070701000580e000c040040b44a2076010b03140d291780a5a811300d00400070f86d0010b1803c0b04500040060100081d1310460540403140d281ca0644c2035080c64810403824524031144010f80c0d036003880400f14002d05181c4c000d0007201c1c802c6d002811000b0000d0103002c811625901403030015081090100244c0025000800400d449a0000300c44500c040d52510115202050038004001d04038005110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 115978588 1250 115977338 115977343
    0x1e0718050f060702010804030e0d03080a0c09050306010b070f05060f040506130519060902090703050709051504060c0c120804030c05040b0f0f0a050301020301090c030c0c0b04060207020a08010e06040302 89
    0x5840255203122050200c1d8010071a1441400c1c0000d0402a00600280c10300d44601d030303100d0308400c0041c44240c02d40380c7d07400c1c020400001138a090455a01e0981120b1a25020b0b50b50101162000f07406404680e28015992003607401102060310005038418001001400600095214100b0a00d0f41030b2142401d081403890030f10003e00808002959100907008a4030000e110205111040032418070ba100c3d525056018040a0078025040805c2c0014026000d4054010b58070079041503440040d42540c0c1c804100140e4420504000582e43c20802030169a201e0542d0120302401200406550740d61000c03650300e51203038a901651182000719050041203805034106c0d0003090112000d0201e801380c1c00000303e80700d0812030b920f8411700c42d10040b0340c1541c841100500003000018000c5490f581e42e4002640079010a041c51000240707400c0281403281e008880341c031625904000207224980d601d40d5090007e602411090b0ba2000302c0180004821809004240826555401a00607410311f80740107031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 115979838 1250 115978588 115978637
    0x13020d0f020d0e16030206070f0b07030c0201050a060f030f060204050a0803070203010605011d101b05030304062004090e0304030f0602120117030a140d0207031805090c030f1e07 78
    0x40c82c135008640d40c40c410341c2019044005503034040751403594030f03410340c13405121107000d21400800320a04c080030008000d4240d4000c47c4000810340081c0940c0d562814070804881c1030b801003000039159428140003250308a5020034000d88944001480c0586030b030001410001c84d42d0084005a10000e00c1d0400c6050a0280e14000d14085c01c00b00008502d58102c0c04464001301d01086c0070b11018542d08901610440140740c0c6412151964480d01206041054982c0c2c0101c2c0e050b12581d040440c0200020b199050002c1200c600000072402c290402c4104000741100d041e8130b1078284814440440490702d000341d03606200d4840e4000581d140c1d08a0701802500005a0103010800c03407200c940ca0154001208444018001d031070500003203441c0300455003050207a17080c0f00b410280b000c00e0020030160000500d0618403912560700507100d54a03803c001c0320711811a002545440c080c80401d011042d20b0600340d1300030340030319270354000c0045500d281c030310034082181e1210001e00c42c1e5030100071054880320100b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 115981088 1250 115979838 115979861
    0x304150c120f0902060d1415030a0f05010e06070c11030105040c120c03080d060501020609010c020703030c140d0806100e030a0b06010c0c0914060306040c0513020d0f020d 75
    0x600c5040c100510181510188080300094107459610301c90071001e042c0d01c80010395034018103160302d0709450f11300c9074003e25003c07107803480c2d0b040d403400420000545003030340082e0b000b03005004149142a41e56003030324500307110208030b07555903ca10104920942c04e01c00345201c0c4501e41da60003c404500c0c205082803244241010f4000d03403504080c400450107222103a020b98080c00014180300005190031074420138258070103492018082035140302048250020f81c00c840090b070884e000c4d600d540f44a80d00b00e640d00ba0f140005a401000100000390040280d41041c9000c0c00400002c2d14004c000a4141b120701e100050024051780304002c403d1400c2c0d0703002c082a04082c0f610700300b18840307070011030780e698004000a00341d40045800035203140c0c4a615042135096000c03400c0c46035203680d800307098060880d0700392a1b0320286689000900b5410000340ba6842150413045549180b03251800380300110041300315100001d502045101101001070082000b0322180f0b403801a601c9180c130003003c0031a02c411041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 115982338 1250 115981088 115981091
    0x3030717040b041b17010204090c080f040f0201120903020c0907090b1b0109080c0109050c04090f0b07120c0e0f03060106020607080705070b0708040c05090c0703080603030d11030415 80
    0xc0c440030a41c0b448805600c1075200f4080916450b204441030b2000050790300079415070b1078082c15407880300b406401a00071200901c509002040b40c140e82a80d400c8000c0b200b51a03889510750018020480d4118015002801070404032a02098200c019040d00c08424050340540d01040c201c400d2810681031141d404000c07441e01c203407268200448180e03a841204a01c3c1c0c50040380c9440c060700b461080d80210480c5502c402e01da40e44a046d0520107019011810301a505400303641e00700c100f2410320b8020854415400b20112081c80303240c3e940c1c100c0c01280600b06800b00302c202126900005d05600c1000d20028280d2120410540d0900401c000000405625030081d0400401044503a1f000550b00f500403506003410611035944820803901800703030300d001600200d00c120503c4071840e041802280141d000300001d4180b69210f4040c058120b4064440042c03c050403c002804a031041c01800d40000e802001d40345450204409003040d560950394240c7c02c0c9074000207000c10000441025000042c1d107400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 115983588 1250 115982338 115982341
    0x3060c2f03340c031106130e0703150b0c010e0a0309150e04090c05010806030f07050613050d1208090609072c0106030507030b060405062a03070503030717 68
    0x140d10788900841e04482c039503400314491850410b28481648000c056078000c0041c2c481250304240120030403921007a1080348449035844541d06040c0200e07000708840800c524840362421685158150000b0184001c05079103031010680306100d03001c2c0c00010444c400d580364460308060441c42c00c45a0412840d95564404201040040d03082040b00046620480401300e2100c2c0444013a41c5a420b03407060290320905d45520201004034006420082d07a0081c1ea4040b0941c2ea0b000078183c3c0e51044007500b10f125445054104610315101d0000d00c1c0d0034030200142c55500c0d6031807011130103000f05c80c48100d540d0403800f01d041040c564080380e140c0d4000014402803038981000e00702691140300c0d034040c05002010001400004003540d80c01d450303000320041e200c50155a92500001d0050805403002c100190600f00390140614000d030980e016100010b00a926201c001d00340039a400da02c8110800f40c0d0344031a6078010810307000780050103006000f44060343e40da107060300e0000c10342c0c038401d081003000d009030b81c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 115984838 1250 115983588 115983677
    0xf030c0c1c0807030c081306030518060c0a020a06020f0d1103040b010524070b010e060102070819050c030a03020109020a090204080a060911030708070e15011209030903060c 76
    0x500380c0d90082d4001608903600e00190030100e9617906140c20280041400140440540820005000450303102d540c082000d6165030080700340b10140f129510a240e800007010501d0509004014002112240122508103480e95140030a076002451750748149030340410541250042c0780502458840c1c100381c21440e5181555178081c1128060103558051203001d42501e02080c04103000c5000d06415040e138545620301440d0200910344240503030380100d61440003140c800d5000186034415650000f0107003000342031500d00c01e07901c41442101907902e88500b85000310b4640b0140402c2c40c103140654008a810400f80c0180410035696511040324244100020448140007140900580358000030100740426503040000c403007441080e64542c94011442c00141e5694005554002c65103c0d18a07440103a850f40a5060340040035240c172400700e00b01d0300704041010300b07035444044034a110703042c20b06c00c0d66100e0b181c500881d4214040040455000c5e0b1816030700c2c814601101841c8402c40300c2c94022a040b44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 115986088 1250 115984838 115984879
    0x406061d030304030b1807150903020108060316080f0105011203090501180302040510080f0102041202060d06080601231203040b0706060302040f0213080106050102120a110f030c0c 79
    0x2508940d0031000203a4040a0340e03024403ca60085400129400c1c085c100200c55100c020309807060401c1910075003030300003002412288802c00864098480310000c9140d0740041d0b41240f401021a40c0c1401a034080e40340380742442001d400a050920b008082c0b1224403c4110700b154010382240130390302d441a12710710000740d001007881300303492007840c1c0424001354202e240c0750841c886810084d440b0b424401003000e5006800d200c10202d65180d012100d07a40c1100003203508070f00c02c078094201d00c22282c8203a1400f604000c1c00070702000020f42c00010b040c1c1d548010321410305100780c0048403201400080040030b00408114050b9910341181e100d0001034103020440c1e0b883c4100d02c01c03046074200100c2c0c02401e00040754400301c01150081c0042c0103804503c002c000080d8860a9004441d4280201c0422400fa0500c40c44040d2041a0014402003c40b0118420640c120090400802c92019200c80007008140072861241d82d150008644606854190a040c039010f6072030b550080303144446481030712406 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 115987338 1250 115986088 115986107
    0x305070602030921011509050601090909020d02040e0f1912020d020c090603190809150f07020f04090f030905100302120c070302071a030405010b0f0f041a0a06031505040606 76
    0x920713910010f01460135820901500741502996405501c80000041c0031990f90001445504d01b40d890680f01500d5580e040c0070bc40c4001e00181d004415a00c201c401401d1503400500000010f0003144c03c0c26400d6440503103031070490384610348401d43e0001c1e13407800c001038400c003840080d00d10300203003c1e180040c1e90029070341c0e43e6000c0c1031fa1255903840c021407040e4038180069502c103084d1111030745035541c45041c0040113900015055010700c4454030a1002e40c0b10610650382000465081149044540cac0c0030000c1c045201e005030b60b803083da6080081c0c00078070815900716000d80300740c172107101c110310b404200482d41e043c03181141c082c9401048190440981c0b801c42503880150120300685466241c141280390004641000b00100b04c400700380000700c070303200340594410b91081c4001d028100c440d0341803180060300c030009650400c0020303182103054502a005954440307041071000440b0400c0cac0c40040d070390144541c4070601180d603440c03080c13003c508146500c1015100030350302400280c2c03404074000d041106 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 115988588 1250 115987338 115987369
    0x3050d05120f04210503010503060901090b1302220f0507090825081f060b070b06040f140a020c0105011a271003141e0a020c0106170703050706020309 66
    0x181c000060810000250641c104241a035440d13130f14031103552010700507a10031301406209204006c0041c01807401409031280842e44400114820f131074030410401c2c00b10f002042280d101c13482c08503101d54a015050344056011080308045000e60010544804844014114504100c02c41005000510001850344007006245e80310401344c0351011005500b524040c0c0202069004d04541a00c01e011950340034202003c221070704105c0e443e910840030440e0b105140c0001c0c01000e03404000381c2585050b1303020000341050f080001c1200c4070424490041400202c03484150541d01190550a4402c00d10486015207a070341d28024020812904c0e000300c1c3d006444544654170003082c018603031703031212a8454805540103802e052140d00d41c00c4019000d014500c1400040062201c0011a40c00c603031100d8003e40c030041d443d90045601c903046000003039480401d01c469030790340702d61000550074544036400510304514009032014605500e803440c1490201c0c0e125408651041c485000c513641c801e01030345074444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 115989838 1250 115988588 115988611
    0x31a010305060c0702180708040212010614060d020c0607031e0b0a14061603020604062405120c0604090615090b09090a0e0a030210061e09020904140c0403050d0512 72
    0x40c42d10000e00c9240304061306c14618070280c0240100c1c0c0e034024000a000d18400c540f61180314144408507401c031020340c032600c203084c9600c0300660600e042420084c900c58001100c003514041d0b0718031150b8a0030301709071142d00010f0b13580e141c6183c0403210710103a406154000401030050b07031441c03000070762412450300a040101c6202c9807451030b55502c2c04122a40b1143d1850241c0d5540c0250030042d45a035011602592202d060440d040800c008240140c01d4000284110321030007418203040c4803503404e000340a106140709240c1907907030650300d40e0b029000070882d06002282090070500d9075a05010301c01c1280c81440540c05043c07011110410a0b10060281564400d40a40d94589081c0152210342c80c0d6041600034062040d081c5980480c0442100321180e10034822075a880b41d0072a080c2c0b22400a40f4618070701200280302015240d0001e00302e03001300400200d00150166140400b140c410380b90702c08000400102001004811301400540c6442802c2080c2041450001c2c2003076144010400c05681 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 115991088 1250 115989838 115989847
    0xa0321020c01030b0d061a0d0308190212152b0c0503070302011b060f05090c0406050901150302030a0e0715030b091e0a091707020901081c050a050405040c03020301031a010305060c 79
    0x1e0703280d40c00b040404000104230944150050801404d0840243c1c1c80b07441000c00079a10000c00300b10790085840000780103081055980c0e0f042c040618010321041e03805d60281000d0303200942c4818400541b018202c180324615469400d41ca41044510310990100b402904601d00420160b84c215903440f610310451980280e4158039807402000400c540c50b410701c0c007946040244000b0800004518a80d203806890410045844e00d04100c0a000244241315140300106101c000880c03084c0c000e160021454a80424076441608459040c000c0300e030400c0800b0050003102a004560502034898852401d0311001c04606200b8207000003501c00004042c071140b0010b000c2117150780705038000b074050382d0007440c6103202c00314600c102c8080e503010003020307882504002c00115503084085801030144c80d04096140c151140f2103800d803a56007044110f001403013000d00001800340c66a0040b040c00540b076507070040e44c0c0d40c1103250141700400c206148014105016005000148002640a8002e0090041e040d181c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 115992338 1250 115991088 115991111
    0xd020f070e19020906030a0203010311221e0501080d120506030d051b07030602090a05030f100c180e190902010c0b060f0607120e03030712030504020a0321020c01030b0d06 75
    0x44d118608800760000000402c004038408141d0146058a20400e00081d050110f41c3c10031002c0c040c100038031981d601c0704071540071704c0301443d83c01102c86100100a0043c040900c22810341127500990018a03207402034480341c4401e5500c04100410750302e64a004220030b041c6040800d513035040c03840121041c02000188406100765400100004202c0da03012035025030740324645000613401048686000c0d4a501c0c0c80031800d0300e0080740c00400700101c40000c1c10910881c0e010300d4003030b00758001804103000d001c08255450700d0b007440b1054040c0c0391a030b09001d100d0810f652000001282407200320450383c500003170400140c0c1c0c001c2c0300580c181c0c0c000d03d40c29200d44030100000c0c0080c244840d603550242d0001516020003606540c0780703561017503507211421400016014151240f0800300004e14405d00e80e15092030b028065440907170020f002811451306140c499448403009805a5030440425084c41c1c00d26207500c1e0b04201c0002e4401080c1f90600402000b0300125943c0704e00d40070f00601107510741d080c1c80362 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 115993588 1250 115992338 115992341
    0x504320c040e09210903060a051510111b0609040e010204091a0a060201052806050607060504050105010605090112020912030403030816030213120204110a020d020f070e19 75
    0xd81200d5070b4200083c2450440141c0e42c2c0700120b44081a41c040c0d0142d80810503c0c60162414440c018001d017030140d0b15400b03010020305005065401154159100c00c0103600c5904c80015034415a44a00e00e010041445040c50aa808140c0318001504205052050340b18030007600c030860420b98021840100c000e180d5806805a600103851841c9401507a5060905204443c032040c80150f810704905610b520341207003607c02c11074640e44031a038059030741c0d0b000040300000840580e9158000084040d26980040c2441d4880501690402c0d110f90504c0f051040038840d080c0100b01d18204140303020f440300c0010700442c1004507807003051580440d82002c580c4a904544121540c2d05080e00d5690341c5074031340648200c0007034401c03440d00704d000c01007424403c0c02842100d041206003809502540d00d05512501d01c940700c0c240490304913842e0207900700d0080b074150181071500f400c0d4011341000d4108003002441d10407103155140555100020400c104500548015000b0300720340003068050700e01c104c1000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 115994838 1250 115993588 115993597
    0x30304080711180c0706150819030e19050f031c030c0903080301091509020304050703121808070801140609071407080705030a03050a1a061615060504320c 68
    0x161200e201c40200f1241e008440014001144101c0702040b46142c0092041078645850040806503800141c00710f9202e4031210100d81fa9910034580714041c000c00cbd0b00030821040700d5001035078020b2203c1000744200d10300f01200c80801c8006038010003c0c1c0500380e21360100c0751041407040003030549e9500c1524513603100d0228240a160031400855503541e44e500800c004140c000c448040308091584041903050b240e00850b03001d03540000042545074219200e2996002c4480f4900060000740d001070050000b54030035400080252401401d0114603026446007950803203200d4840c50030b00e00040058554031482c6c070503003282c114035182031a00c042c40b8a5840c2032140f810045e1002030081400005c109000001b44031615090f6000d210644a0683c5a8181d03414440e14851008010080d0b249500780303003020701800400c10640c4840812a5280d55502900c0b0040f1580745a0b240d810a10860410740200c0c488001c61070950070400031194048410001240311804140c1c01d55004176000124a4003605c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 115996088 1250 115994838 115994869
    0x311070b1803010e0d050904110d090f0507050105130b030a020c0609060601231801020102130308090f0109030804090f020d05070f0206090d1205060d120503040c0503030304080711 79
    0x6a0749088080500c0680481d108190784250b080290310080448080f5603258500885d45545062000d11010003015040c00000c102c004031042c0403001307810340310b401080600f5028050704001031002e03041c580c1c102401900172078140318042200407012948800c840c0211500d0030010380e101d40700c0711255000b81c85004030b140340340d1040205029000d0380100707038a8010202601d031a0b0b00105003074480030741d0960004c1c25100c603074414040d56016020440c0c0c0342e00013980500c0010b1030025400900f1151034038a0300b0544080f4000f00301c648036410710914a8131581400d0a041301d8080c595030300c0b10801d00c900c1c010000300030b80f0381d90000503a40c01c540554480c8030700d401080c486460080da0003003030302039030740b031054018412000421240312011908640c3c10509546002040c042481400b01070500501440c0c0c2040c0d000a21401103055a076544020030441e9440d15568103050a201c00c0b43c0040342c200c28441e400400500001a4000302243e06c92a400100d440c0c034a9050750000e01c40101d05401c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 115997338 1250 115996088 115996109
    0x30602070c0b121006020601060804020609010e1203181e221802010329012105010308031f05060d05070309060f05161e050c0a0507090c110307030c031107 68
    0x80f00c00300708241c411840b81d410740760881226561880700301d80d560000c0c0b1414010540380c4000c03401500f08000100107110040c11310a0030b40c06d42e2008508a080c407000d02085680022031205020075881c002c00301d1624040b295900e40041b6403400311080c00701d6482c1188102103202c034000e000d04081408440032540c4600400c200c6580c0e03803101e85100e00c003440480c0007a2903c0c3c28921035015280c00d17522111046641a501100883c005550702944031988900c02c00004c00041c001c2c02280c080c19010b144915020f54403418410307814103007801e05075501301e00c2c482200e034207200c19103420081d5400640b607404049595202c044042e4010989001b01601840c102000300040c2260341d0413290168824201c044200c0e19107100c00c0b01e0340c009003001000b0b02a08464039200c0c85204801405e5500c3d06503058640ca080300780c1d500c3e49024072035400030081c90788451060203c1608210080c3c41400094003461804580340e4004003e800ca0701c800400348805050009401c4a007000f541d00070b403401201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 115998588 1250 115997338 115997347
    0x31221020c16050108100b0d24030501060608010b0703032d0c080105010318060504020105090a03200402280509030f06150303090d0605191a0102100605010504030602070c0b 76
    0x21040d8544100e54074808010b034a10200080c0b9511502c0e41030710815040130382d9a861410403c800c0b020b940805a4039052a449400d60003804414044450a100d4900c00000042d882c504c3d02d2400d68070258001030a0201d60310041007100240b204689800d58076107000210318002020703030300c1d0104480b0b4001100c0c000f40308150000240d03617888484205125240d0743c80c16070307071180110162006140c880620803082614040040c107940c1190760080d2050400d281028038400c0441c8000c0070070340c4142c54000961243c1c1244c6d4a0341d1002100d011402c0c1c030203514042ea0f02085400303012005450308800c06040342030b903030040d20510540d0320340b040040c10f440b000040d00408960303a16046c2d0f046a820347d80c40010450916000080740c0c16140c0103418501c445c240307526420000c080c01000c0302415440c0b014100c1c0128024400c807103019030311100910700c0c11f49440c0020701c1d1518054220030500e14015061050f40c0e001025201100d602c800c015070f41d58118a48441a00c04aa008002103000810f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 115999838 1250 115998588 115998607
    0x201120c140408030a1d03030a05031003060509060f01060e012a020301020d020a09080102040f05060d02040509130b0f24010201060b1216020106030308070c050109020307081e01050103122102 84
    0xc024a007100542d640c441b9110091051003134420f8612220030b07410b0703100b0040c0100d154080c402940e030203039040001c483d04c10382c1d07516084165413080341c82e4592034100008000c880c0e540383c103089000d442145494080504203d0001e0b15181e44600c4046120451090440c0c0030703822802d00c0303a1130982c054005e5444486501086010350480c001c0c0700049501d900c0007260714a0140309460441e280d1000e41e042080c9890700340322295000074200080d0b50340810010074103840c5d2207a202c1c061440076160481c800064107000d13503422006050540d0004c0ca0300f0501621800c01000340f844161003d9142401d4440040180e0052219500c9074003088000301c3e0642554807901005407143c2e00c00041880d50719030781d2008030700300c1c0c000d400001d0104a1070303800300318040d100324146051188180000030301c241007a000286000c9190348240c08542c040390072012100030108545001c050454001c3c070095056507a080000c460b040d122404000700141c2001e44014000e440942400c5203040440d980c48018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 116001088 1250 115999838 115999843
    0x21c0302060a11090901170703080a050d0b04020c3301080601030b060910090b040f0e0105010501090b040317030606070b01030b06010f0f020303070e01091503060305010501050d0201120c140408 85
    0x4071051050300e80390103e010508403a50044800c2d48200410080507a0300f01208840000022400c1032102c1c4606c0b000803001806400041a071252603850f01078460704503c1c141c1d4280c0c0c400e440c20078065070040c410b21007221000203c0e00c08803500c40400a000c00b16504280b11084181c12164100c81c2d403202c000645c0c0c01002c240c43d8143c0b4001c00a08010384d0f100300a122100380180c58500d0b6144901008212401c20341c2d100fa4600c0c980148082030192803408a80140c40034442c00400c66590340f40104100d41c0c000c1e07285001002e1414883c2d0406107503450703a040c1c402c5505c040b1084400d002000800d11743c3d8210489400c19230002000da969616800c2c1103444820031500580400c1c1c2890121200c240103100b200d0000650754006d610f076556840d0100c1310202d9640030326044c04140c0e603010614044002406111800554000941d2441c43c10050300b5030ba41a0312041c040d004000752140541d0707006a16015699140101103004198490708581d108203c3d443c014010b500440d012805841c003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 116002338 1250 116001088 116001091
    0x110906040e04060506010c080a030902060909090f07060318021905090103140105060303130b0a0903050d02161505040b0c0a0204090f0308060a210c0e0103030c1a010f03060504021c030206 82
    0x43c2800700150f070340706001500c0d0385150203400382c01c0b401d0600c4102c8013240319400281c4618800f0744241e090540640c046070a5003000d840a138501c0e003010703001c0507200104010050041c10700786001c0c4000c007000ea4185081c4104d14102a029071203550281030b640e01050140c100911018010704003d61f5603080481d00015516a8552a9402d10f000b040b25840d0010030b950072074885a07207008035a031902d803802440c0e41c0050720b01c400b440b110000010110b5824000050059401d4015040d5a000300b81c1007100010950008c80e45442c010100034007035035020054030169070341011856901c0480141e42032074120108402903000703082044072000c10a20381000400c091198543c070710562205010440e02c195140100307c40c100502c1100c0344100d18800c1540d00150103156181030141d101d46115080380e809810135070104115501900806c01c00701e51503008540704501c0803215505002d00002c031903c0b03521024099030b40343e1001c10300f0341d07980c444a2b804642541841052500a624000c0d403117440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 116003588 1250 116002338 116002343
    0xc152503081b040305190204090c150212040b2208010515040605030606010806060a0c0606080a03020f0609030913180f020406080a0503090d060e0a0c0f0f031104110906040e04 77
    0x512003100302940ca0b40c04240d4040e2a48540503114140b00740d240c08003030a00000059a00c0360316500b604012880050140000d0090b00406c01d007203900c1101c0180c9454120104001150000c020422250024001f03452040c080c0809050891280c0c41540c000017000da00a822594038000500c2071402e50b4841c45c1402840c20b03035043c03001598a01c10140c8a400449481d030100e490080080d03000d1500c040102068256802d0040e07042c2456181d0000b2039246801101345031740140f400c1e006041d0104400ba40c61500400100084d00c1d00903480c0e030b164003d03840d800e03018550803481d00b400000c1a81180380d0000d4012429941e5000d03604150103440c00a801c00d9000701e142081c007281303a0b10042064019160854002e51400e0004802e0100100000b501501c611340e072007001c811000400d1041503e05030180304060200d606100c1091021001a0300c03131500400c51110402c00030b07a01d9040410101e208860016003800141c40c182c40c40d1180240c15039020000050200d68240344900d03281c050750 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 116004838 1250 116003588 116003611
    0x140f040918050606040504021c0f02031603021809121c0c1e11030d05131101030504020a171018140328020f060c040303110c15250308 59
    0x25030311010382800303600807040648107412860004403a4103141d0041741c0c10a2024243c403a88402d0346002c000a100c032204101e81c000800c3c650300040d0300d020414800c29441c204001007c4a00c3c5034002030b003845d0b00c08405141000e10720300240e0107072014004986039415041665580300d100c07072a403940551020720008010307807411240c140507a20400c000c0c500c403056045a400006c180300b400799a00601e149a6444d140310422607072060120070300825001d10b203107819405001005140450300d481414020078101440c00b4200302c05030362800d02e810f0884407103403210007182c4c02110b0210b043c80c510034508201103051610b112076406002100f1034426008031403d108991003100700715220b20801d84090015040c00d450b40303180000807050b0304c0b8191403074012102c03000800490756080c00800c80b1403102c2814045810800e242c0c0145198140b1a040d00141c660bc005e450009100e15640d240842b000c1540410781d809240d481c6e050b049404800130f43c40740c00c81030131494000e050740d000312040d14480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 116006088 1250 116004838 116004851
    0x201080c0f210a0c050a1103070204060b0301061403280209030f160e060d03030c0507050d0c020f0f01080414010603080d0914061515040902120907050114040e07140f0409 75
    0x2040280b141080c4502c06507036592406c103504804450301400e00c00b045103107010410410006a071a403090200a0200d141c80545a61412202600c01c40b145150011036030000c06c208102e408801d4040080307a60216449030b1030400c151084402401030100ea00d03094442c002d404045c1c80b00004110a64103400320320380c0e4501e074860240364502c02055426035003005550b60f20a002074000c2d00001500c034414645942000320755151a490a050381c1c004501140c0f040d030b480c40c15800c050141d00b1500341c0a4402481903840d40000030302944c001400038100f10900107401a00d00030030740100b0019034000c520303d900c807070750100000001e04c0c007a07008031504007401c00302c041c0178600070540c280b00301600d1704542c5442a1080c180408801c000321a80c041c100e04202c0800d40a0040c8042d000344150204044000e15011100d1031822126801c00c03410310110484011401120000715411b03924601140d00d07207a241e1380c00a039245a18491001d160b41d00128466000081400144c0100c500d00e8000f4001c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 116007194 1106 116006088 116006101
    0x6010b09040c0306181d0a080c060702060103020102030427020a0f030506041116060207020303070f110907080a0203100b04080d0806040506030a0201080c0f21 70
    0x5010000c00d1064441c00c0500c1001d42907241c0741404c2002a00300560b40e0034075000c40d442c03070183c1500c98034035003400e032420350310007054400080842e100c907601c1d850300c0c01d0b451f04040e050595520515002030911480096040d04903601a0090340c5083c1c1000c01d186005140c0e14500340d04600007810400c06401b82d48010003280405070384611031880401c0c0024251f4a000c1d003014072403420561400b14000c000e0301190030040740c11741000030314005440d10501900035004046d5060001003410010310a404210b02d40c40b0380304076a848940344845040210310201a1036078000540c4100010f41409020340c000c2d034100c0c1b8980305507070f1501c1e601c407946010f80d0322a800201c00c5810014400c101c032500115050b41012003181c0511661a1050100c1c1d950700c0c05450103410081c0d8503000c506100915002c46903020b001041b0280c5c4c440410a0f010b190314010401340200d041148000380e903 = true := by decide +kernel

theorem cover : BRFrame.Cov 115827338 116007194 := by
  have h0 := BRFrame.cov_init 115827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 115827338 ≤ n) (h2 : n < 116007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
