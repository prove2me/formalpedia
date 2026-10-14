-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3215
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:53.781053+00:00
-- url     : https://prove2.me/submissions/5f458e0d-43d6-43c7-94c7-352904a10ae4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 578057553 ≤ n < 578237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 578058803 1250 578057553 578057561
    0x9021003240e0c0a020322060f080f190f090602040905010f120b0c040306180201020618100207030c0512040503060109020703020d030f060f0603050f0f040305040b0307140c0a0501 79
    0x4440d00060340740500a0100c03900042e0b0380440074640300380d030b90188404140d1a500844000b00c1042c070881650b40c0041600b60184002ca0b1401d0722180440300400d1030950b00c00e80200c9400e1041c503002e4000550090640f16655124982490000f5201c0400558202900c20110084e5542500003d003081400c0062040324014107c0c414142d1543c0d00300b610b020080141d410006e4102400c1c60042038106140d84112001940e00200400100316014106c80c1b901c401d092050b405801803a00240c080340403402c404c80c1048681024108015654407528001d40100714203508020f03c840035070b00018020400ca190083d26946e0250711a0710385000c051410707105802451249005010303400c00260000707070f6000ca1b41258140401e1012800501c10004c2c0940e034460000c44000240001c0c4d02ca4155024a0140207070350b81e608203a43c0d52808a04c030661082d0f0300100011410481084411501005503800c03001d5407401e00c4000500610301107254010085900254101e46407c50801c1401d00c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 578060053 1250 578058803 578058851
    0x40e0601051c050607260420090127090c0f1503110d020306150a030c02060604050121030e040912022a0f13090f140c0603070e0409021003 61
    0x1500d08002d141c540c0d036007910764a001c0c001c2414441500001520090300c41c68002541e004548903842c14501420044080100a01c0c0900d0501d80c90b8401206810019042410b903440030321022000218680c0b00c0b607010800c649030700c003403a50300d41064000030075400d0300c4002001000b60341c9041504207c4006581001106580241840c102030007071800000c20a694983c0ca80010050300d955950b030206400d902c0070400a50030060000704500c0854140e4807400300d00343c560f402c03542c0b01d55540c01888102c03002801500d41540c58a68080300940d241c000e650307280d078800d00d414000050b031031006c42c05813240d69004450090111111851281d41040100d084400e0822680c001950300703c01040c00c100718000701402090149680b4010780c403410090041c1d0301301080e04101540440c14980710181001004854a0300c00c208111018132001031103c0154070000c3c001da24546400c03000303681c4a26980c40d035035005621007242e94013580e0f415601800600300c9403000300b05038084080f60300350126010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 578061303 1250 578060053 578060089
    0xc100201020a08060108090a0c060201380411190e101e11030702090c04050406122f06070605070906140f0c010605120109150b03031602060405040e060105 68
    0x488082c20050380100420340240003805e20000c5903c03100102810071020360302c0584003202d107050010b0025415407100082021201c07142c43c2c400c841c02d080d101c8452810a0601c0340c800c0104586841c1d1902d0b40c4004846500802201d00e00315207444038881400d1800882c070082030260510b245203060008008000f4074443c40c0c41e41401c1e0b88d83c107181000740d5031140b42d0401c1060a804a11034500e04000301c0e0102a00141058258038041109174038560107030141c0c43c069070801c5c800065541034460704a0241d030b485000038030100c0a40420b001c500110b0340e18440b4bc450b100e5000100c1c0e44800004001300da015450202d0703689030034403010f0300300d11041d400171040080a10b07111007541d03800710590b04400009a01d0603030f031b160781c4400607014006c2d54100550007500d001d103040d8511415400031008a1165111020100342045810101c4032202d003c140c240d0030801c0a06ca06c5203100005052681c40103124908090301c03031001c0f070308580c0201031720f405982c0803000521207032030012855000d1200b02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 578062553 1250 578061303 578061307
    0xc230301030219030b040f052104150912080f160f0b090d02070e251d0f0109180608010203090304050f0d0305040605030a02160305032a0405060d1503050c10020102 72
    0x50f17916240462401040506060242c60180081010034031855410302d0b421000c0420710001e000c18100294001d202e260b1001c1110324021f0300343c1e800303000320404607442c142c0004032a20b069250039010354400340c0440210031080048101006d240308400d06100e005054250075100d00349051359a040300035007038412662000a1442c0030541c0002c2140a42e186412032280985850701c180d00125080030910102c54418001e04541550001d1020922103a8a100383c0e0160348841c14004400000c02040e400034609400c10700407c2051503894840c549400c2c0d001038020ba80d110168226003054818429981002a003040503280c000941c42078600200d50351843c4d142c20340c3c0c010341a846282308030310078408040001094090264190b81c1180c0c0103003242c4929144030f182c0140658002c82d844184e45120b841c5450fa040300340116005852459107903149458100400c01a96030070100c4580503803529610025280b040688080d402136210f8030040211305421410030092254400d4404116841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 578063803 1250 578062553 578062559
    0x30403020901090f0e0a0b061905100203131703040308090d05070f140901150e0a0b03010306060e1f3006020301030201110f030d0b0111010e0607180303080103060c230301030219 78
    0xc7c4000e10b8008404440c4141307203060420100000070025404030750f10140fa8115180d03680d40101c02400e102001c0080d41c60b8640d2100c0960411402046c0108403540c01403105000040700312000b08801c4200824141c10b801c0141c0c1c926103003080c15004030cd600300346001e0800080140070340190031311038100c6481d0002e6050044c071a40d9008030b044668208000c541a46910b5100c5854190140000802c96581c079a140e050940150500c0d00c610854040c0d0384c000905090710744400710000501c820080010140b505586000c11802128460314981d200300d9511040100c078016030300c940e4840c401c00b6842c0e601d140005056a4503e403019045038200d420f1310740003440003208440c100304400500050091801004840706e02c0c400e0406140c1d50320340340200f050305000284040c4500e0b0190340c0c0342d1009101d81188000351080c3e03c0000c000c1420350005000250007500301c00c1515203507150200b01c511107004000e84281c5503e00d96080b8040c004014002d50030704005510380d04500121090500313103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 578065053 1250 578063803 578063813
    0x10b0d020d0b0402180c030603160e040f0501151d1b16170319060501050924090a0303050301030b0c0910200102180f0d170a02030403020901090f0e0a 66
    0x21044001814082d600340090304560700c0090700e041074118100f44150300d1901c1030401c11903a000b91401d62180c0301c4c000c85882c2000144000c0400d40d02810340c04100780d2282d5640c440ea0004c030b00c900301c907207540320103640703e0002c41b0420900c02400840100e241c2c0140d1001c118103190400f401c0f141140da804401c1086415a0b08119603210444012222207a5044e080c4015280181100e112603c0c2c030000a10008013250401030720380c0b1004490810100d646c800c01502c003445404489500002005010a05003400d4400580030103180c0c803c0e5464690b070000002c4120385281c0003140402e00100050052110103071202c1e910400f5907000610300001da0300056803270001c41800324100040341080e6950a01d44023841c0c240c0284130300003952a9407101d4000c2c2c12520b44811030600548039201d1040c02e914240c1c11480340250045000f0100308008800c545913540084503902c1540f10801000005803150f280440c000c1000d50360014000c0581f01c0c0c100c003954130b1500301e0f00c02da07800210054041a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 578066303 1250 578065053 578065069
    0x608030a08060d0303230405010515010807030c09080706050a090905010609090e100608010f0f02090f15040b0a02030423130507090f080d020c011d1c1e05010b0d02 72
    0x32074200320880c10504d0200e002c0c200000c02840e00302d02c203a6809a0360001040c5140c02240f24400030b114540d601c41c400810800404c01b03140c001099400813500c590300a5201240400c0c0f90b10380000709640f117000a600d04181980301000003140000e041d024181e0000302c4e40c0c060704003100f091101c2c0d45032400040407060300d0b00036414032580c0c0e00c02c0d8400030300007000b10302c0c21078070a21000c2c00300d56544c2e0110342c0285aa15100c40249040c0005800c3c0c1e241c89200729128034900800034030b44000f01905109403195203582040c5500001c10022a82c0441040600388500d11580155601d90600d40d01104100440703a1204040d111382601000e540c1e13440c424000600d51400c80002c00c2d640c0c0100031203910000e60f0081031a02007441c0089408070001c9041c14614500d6000c807000c039803088c0c00440300019421038804088820400010062400e00c0c92044103028280c0c1400541e01a84c4403048003450407101c2524070b02c3c07145416070030040c0a020707040e501001242d07030704101e44840e004074400c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 578067553 1250 578066303 578066311
    0x1109180c060d0212070309060c030204030201050d0506040b0306040807031407080304200a12110603100b07060b060c0c030d05130e062e080606030c040b0a1e0504090608030a08 77
    0x8940120340c00030b410780c00c0e81c181c03011003204041150f12170806000180040880141c2a00c10604241d40000316a001e8004c84040b01d606944241c602440f0f400c6001c020400505803541c0207403600c81300c030400d0fa001c01c296802a400b400320190703205000c0c900a00030044041c91a05148000d0000c0808117500c4000e8a6002da0442d101c159100c440140780c04204510001140d8070400181010402043c2c6c1080a8143e0f4803408000114000413420801035000803900145031503411003051003607810200c041d201d414480c42c1f0208d50900f1240001d80c0c244c1103460451159400300f174280919290401c40c940e88035203241050703890100c10044c044c0070760501c0e00450125210090202d0f070703507469580d001c1881400303015911700d0050080c0540303640d4142260304800043d100e00c000c10181c0c508442164000e05801c05074510301460411640c456801c1209032009001203c62846aa05940b41031000c2403c240d59440f55a1400c16554804a41c41c0e90030400d0700d58801d1107010720440e0041855500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 578068803 1250 578067553 578067559
    0x712032c011704060615120501050607050c100e040f1b0822140303010e070906030204140906010c0501060608010510030b1c0f080c0703030306082406040605030601031109180c 77
    0x403a511400c002d03002c2c01d002e134030840112010307122049146600031401f1044040e60b550601a90741e858007081168000c40d08050441d0300f1040300030b2007038503083c83c41c06041c01d242e0800c4114001107000040c2140d01d008443c0c68941d84072044118210580201100600030a040840702800d2860740c221b501c8100540548064411004060501c680c1204100703848440008490ba40d40e19089000ca0702601506c076007000c02d0007a603020a210740603009580075140843d12029410400c04104081c20002810041c1813202d01c07029800810000c2c0aa01c0150406444448081d4588014807070b12080e02c0515101b00740ca440112241aa6040701c6841c54000c01c0515104c1040f041c202083c8140d080540104030201c0041c2003c54050081a0300044a010792400c22201f643d491800d500d07010036190300d0400c00007090101c031108003602100741d00804007420002c0c020340c503100820300d4841c0a070415078240c5a0041d15056510b405400b15500141c080450f040c8210000640c40c1e641c0391622140d44 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 578070053 1250 578068803 578068847
    0x903081803030c0c040e0d1d2b02130b0904020402070204110c0a210219290f100305030a08040501150303050d0c1407020609030712032c01 61
    0x41191040030640c1200004050300d50302c030311101107142e40d0700d640c004483c0941e003041c200f80614030303000c10842c092001b5500d0340c441d01c42c28000310102400050010942c00701e12800100c0344402403c144907088508110840c3c10702c205401000300103050051300e41d03021401c104c2034244a8a582441c0c0350456810780b40941c40c0c45d110720000e4082c001c40c10a10014040229501c4107501000801a8880e8060301d1000400341c00d9101c2c45440190300000880580e10180d81c14000340100b481e140d42c4540943c2020781c0da43c441c81041800035103090640c99591080400303101078155200c000c6600034080541041c815880e59681e02c0d03c0c0c0c001d0010002c14020a0700000c2d040c00020341100845208004090485903143d180181098100b04840501c0515080c1c01352445400f8404550410b4601401c03181051034947c2000003d9101c481300302c0d018001d1100000322617040d92040d1104502c00d0b1604403141401c6402c3c0040f40c0c00d2600030417641402d4800c1c4054698100fa5050700042820000348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 578071303 1250 578070053 578070067
    0x10050906130902071a090d050304290c042d270c08010303080a05041707020d0803070c02100e1507050a0c06020105220b06210303071d040507090308 65
    0x100c1040c0030703503011100c03075400050079004100d40070404013440000450f80c0d1902d600d684056030b541e11821441c00b80403a000304046404208080086007445102070301d00e02d00312900147d0089148021707100140c2da1480403800b804003c903140780381507005412602e4100d24140a4070741c40c4c180c02e00c600c503200b9900c0390206109040d0400e00c000350006181d03540700303101303840200800410350340003403109900042001c400f040b40102c450003801d004d9a000002517201c0810071521400c15031294400f282e01c1402503400400040f0340768040c5101da0b105842d0200d18a0316801800b0780032111111480c00c01022055051a03503603241c448800400203000c2a64071403c0b1803410500c0c060440501900503d42545c001512650540100d40702c3c4a17a02641c6840341850502d440e260f03002004018003000656000490b141004840c20319440300c4440b5030b03500505c40c06261400c6038416a20040000c3c42c2041d2a20030507603000300b16004071016102044076150210000388005061701009151590005800c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 578072553 1250 578071303 578071327
    0x1050c03040311030a0818090a2c0f0a05010501141203180f131d24090c09040b0a20030420060a0503011d01050310021312050d0e10050906 61
    0x880b03815a4006c00d0b1a60ba20460841c41e849000340b2003034540305520040002c0d003a40c0060207072101907146400780034201641c00003058460303203072a8005ca015200e02c0324041c1e803210f001c209400c202806240001825414030180150040042040c2409151440c8440090701c50020856112131a850b0304040500e01460000341100c54a22003260300880850a001c0f03001c605030f000111100401a0344c254200c1c1039040035444041c07114841075038800100110000742c0d0074041c91581f1000c00d1059920849806000803000a000e503030036240400e030001003000f00482440340f5514410810b800d890750200c0c0b440380a0b181d2000a00003004e40155540f5001c1c0f24002c99607910108000800e915207620b41813000a145d40c00c2481480d503c107980282d54440940803045240c140d55000c0d0291919402e01320400d0080d5100c00354421117803050307003000a40d15084e801a80100380c031940c0500410b44500b070000301040c1e4480d249030301c00c012540190249a82020403215500402d0f2040e64a9110140072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 578073803 1250 578072553 578072563
    0x14040303111215090a0b0109180b0a0b030f090318010c05010e0102041401090b090609060c0309100806040f0c0905100e030a0804061814060319090503130501050c0304031103 76
    0x1d80035140454405000c006071081c5044200404207030b84180076640c40b4003c1c4401d540e00b851685011400c00390040c040105554641418141e607850045481e100940215404112f00da0100b20826004014000b000301c003442d090f504003101200550612482c0401d1002050700e401855051100d540088410024207422503610880040000c40d1910740d0341c030054403031482d0b24a0090020702d5a4002090645015080d90700070030024043c5400c052005051040720750007501001c0141c48103103e150001e654030f0f000d03401005501d9403400e0040c10440280004c1c2d8007503042080c00d20742000861658194805140d60803941c04540300700b01d000c2d2280c000d840260944090759014003e01c0782c600e051242d000c008004640c595680ea04410070100d044081102d2240500208101c01030700c03441203480c00c40c002c2c5812035500031103170103014151034210045810300142201c1e980c2021680688440811500c10010034003070030a41c3c0350419211200e900c0b44030340c2c000104868104036086e8220348007006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 578075053 1250 578073803 578073817
    0xc0402160b01081b060c06070e22090b060d153204170301080c041d030a18090b030a020d050a0b0a0917090d030e031216020406091404030311 62
    0x141e003041961503104142d03c1c3c1e0001052107801c50110a0b03d50054104007045403401c103110005440a500c4030070044607154104406154020071094600d18001400444c114990400b00000200800d00c0d16000449090080141c3d2141e164896003801103400340034400101e00a5240020702900c0e05010f0300050420710690040302000400b03e48807a0740301d204154005c5000d080700142d401814a014100391109003d1200c160704040c3c16807010307040c660024071850a80c05158040300070040c0c40c0038550b811440c079410000b440f1404540c0c69200c0f4490342c2020303018441060181104079004281d483e40d1045001f4040d44c0e08011800500c0130038030240141907404080c120442c20620410070291030040002c0c0d07603681f510500d05c1c00b0244004101c807419070b4050001d00c0a0203040e1070075a040c80c0f4181d220b41e01030103440f108000340c5680301d0003418141d0840b44828100c038141e00600003103640a8020303d00d00c600e4803482c034101c82d0361020f126a0080d032504d00802c1110196603400d9280c06140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 578076303 1250 578075053 578075063
    0xa0f1e050a150306140901290409141b0109050d080f04030204020f131203080609150a0602010e120f040b13050405040f060b09040b19110a0203030420030c040216 71
    0x61008070130011030b604007600a031a881001051610740380d0005003201d1380507148040e003490082540aa60040740a800300055000380006004c40340c1c4d440390050440c1e011801d90168101e03190248119440c903804080221080c80d189170080c0c10b000103d4602c20341c11801410490300841c4441c40304490404542c0a147d000c0c00654803145011040e0310990001d040b4030042e4500001d01103061462250003405d565015514559640c503404184404070401400c086504403404502540948a0980801c010095a800014a20f0f014140340d0300f00740c022520000014420044100f01101440a0b174054030303000310342180d8035200003103181d4821441d076210a4215080c18108800e00c5000340440c020940180d8080c004180b4040400c441e903c800c132001056141c201011601d030807204140000e2038a010400000c4082c01d41803403003c950440803041c00145d1000040000b00558014144003c0b2640e9520502107008500041e480d001220041fa01495010410b5035a1801d40901c0010542d040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 578077553 1250 578076303 578076341
    0x2101e02090a0512061008030702030a0609030c020a41040e030408060403120b010f0807030b01021e060717070c0305030c070807050106060801060215010905090c03150a0f1e050a 78
    0x500c0721a5182c1031704403902802120401400200c008011084400c01a8020090070030b460300c0c0e46e03032030000b0300d0360003070940400900c5504e030801a160030150402030714443c0300030410175104841491000550003410b2060307035088100c1c01610510b42c2c03d4288000300440340451003841106001d03180d03021701d80c4132004920403c4248401e26402035440306001c1503014044c0000c00030340006581008143d0440d05c0041c01c0a070028941038860382c0503080b02d60051051b9000040344cc09501d50104500112007203641091061209050b046122041003100111000100e46810780e0054803403102d00001a0500800000250b8144490421902c80e994400354981d00c1d01c14034203100c1c0c000c20b0140120404501e50500124440d40000344101c103242a1181901240c0e003030151000103494054011050782c443d000480c20195402c1c01010396882142d50164043d2900d1000481540c448840301441c451a11003c0950b4401210b0106840c0c2d02194012400b41c50380d02501c1c0040a940400001220704 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 578078803 1250 578077553 578077579
    0x6020a2306070f02010b040b01080604050c13030302030c0f0c0616030201021308011d010b0a17031213110603010501091707170d02070b040e01060f02030f071202101e02090a05 77
    0x30140c8000640c040c1d9000704460190306c0148011145a212a01e01090f05900010450703e000e0700001d50029603014164142690400f11541c001e0741f41e0811005a040400e441c1522001082040c010b008076500610f22003403000c005c282a40f1413004000c0c1a41d1014064109060003501100c1000a00495001540744c0e00c0302d42c1402880c1c41d20740d01840c400f00500b103145203441401241d508080045c510780c580740c904000e00a0350729441110820302d0105115058a230040100003511800d940403400a403440c2a292101d0080f40da0b81c6184d2062009000501c0181d03800b0911006a4004004a01001000022041c54a501c46c2e02011414001c2d50300390003084800b18400e4a00c3d400c40e002c075407403180c03107401d000e145c2d0150b4040c14030720080319001003059502c1428000103100003401500e01d0207c4000c00521030358050740c0e0030366090040c1aa8101400e03410000d450a45000003010000c528252054028100c01a07220b03c182c0c070f4001c5211039180c0e8990980c04005c0c20010701c80c25100c1a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 578080053 1250 578078803 578078807
    0x41a030c19120507080603030307110c090f0115110c060309011d0f0d0c1104051b0c0105061f02070504110d05040507150f0206070f030603080c0c031606020a230607 72
    0x203118020380b041c003424003010400113405000c4031805480000c0207103095580d0800102c2b0000304039482603089220741c004100413074035044080360207582c04403040c0c003003503041040c030030403030780e5440103040800c040e03c1c00d44002140c2c00300d15048540390444240350389441c0d4152080c0074005105078001038001d59a00012a40303c006a12541a107284050f10311000b150348040c0c034402c5000e10007402c803256401d11510a454607901060344010500008003210458804ca098141c001845009640e0764490a020389450800310301e62a8a202080b41c190b4680d07012402500c424140c492540116102c00301e5241010325101a120002e0225004000300c5c0740a090080e82c503003d6103d46101004116001d01c5498070030740020a4050300c5070010512a250381401703ca20882044445003003690301c0d140400012141c400a04000c0c2001008140d4004120105400d001c2c5e01248039411031201c00c2c0030051940c020800c1d03a2019041044c0c851020b680410502c5090903940502c4858000d090070130a0b016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 578081303 1250 578080053 578080067
    0xc07170d0f060f06080f0703021306021f0b0d0605060f04022a0a0c1a040b071412031302040b0607060204031211060c220305030a020a0303050c041a030c19 68
    0x148001409204a9a540c41e40943e002c510303000d11800510b40c04001403409800e810000e030445030302d11b0010b20b040c003001100d02424801d60130110050700440000c103100d03d200c85844500c209000d508004440300007000404480022100800c0f2549410000340c0a544101c1003410054001d04155580e41015131070002c0703040150030706481024100c054640d241c0c4005020500c0e103a00100811480d070038a844a4010102c1850181000d4410480445c100e40442c3c090445107211780480701d01340318a02055410907403185021021001d05004014034001d0200d8203031181601075070001881441ca8010401a12500c80044d04507400001c1c00010401084040d61030140103a075540e5081e205010311548501080d0340c601000d400034000c440071000360200300b04584e0300c120180e400e444d03500d030760399400c2da004100d44c0800368014090010a151309405840d03407000700496000c0c6000d0070903112a100c030380345940d904008500400040d011910380303001c1b1050314105448116140c01a090014104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 578082553 1250 578081303 578081321
    0x519020a05070b090910320d0308010602010e2b05161101021023090a050f0106061b080313080c0f100e191b03140106150c08030c07170d 60
    0xc1c020300000030f1b540603d0300c030301901500e010b13980c04641c4e1038190051000c8110201d0310702101e1810307805030007900c0d62000583c5e05001e119446610040d0b26000010f42118400480c243d0140c00070075108125000c40e20b00c01002c0c803030f0300c510301c0c484036150042200c070fa0060201c18103904007040805400d10655201080c0424800da00326801c640d0300c045101c040d12552111090110602d1013a0704425110862840e4000d202004031908080b00d5102c00d850507654464405460750755150601240c0d9100b40210400070443d40703174440c025a0f07581c0b0a10248001420200240c43c6290144200803a82044400d041c6c0d02c101100d00c445607805801d41c03155081c1e8840d220680c034248003003240c110301140251000b680c02f80c81070119201ea8403410300e511440c070f08c032402046090901000042d4003405021502c0310703031300000070b4180c1007100360150031480d02c10350000e004100d404100000c1e002c10450358408060b9503240d4941c5540d1400340d00c80401080340d4140c3c4070010030480c9001d40164441905 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 578083803 1250 578082553 578082559
    0xf051c0207050f03120103020607030c020409030305010e062422062c09060906031c0804050606011e030e010b1c060609020405100302070f02330301060519020a05070b09 74
    0x603001c3c1038441c00f0394a1041445164250395800010009481c020002d404807a00030f0801c54031100465000070300b12040904110301003940c580051040e8071508079646d03402a001d4031050280e0b5030030300840c0c580502c017010300d03a101c0c00000307094010380c0c24400b8031601340ca0303c200e0411501e070307100c2d0400780a090000e52500402d030500703190a000b1007001815085445000703065007800391104010b002d070300c4000074035070f0b5094400c0b01e0308071038003400000c5820303c2c0420a60311002c00b81054a000341c2000c001404640c1000552600340449100190704213a41c00d030f15050004604100c043c909000d8034030556406c2d0b01c0200b800c0351600410040000301d96061151108005050300c4018100403400f503802015000000100314490a5000c0e074010254580a000c1441030552030b41d0004020221450b50b040c0030829602d03004503c902c01c0395401c80524000c104681c04d560400c000240f0b58000c4004030b14802200399103405800d4024080a106960000c05540380b498032031800601c01c2d4070076524180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 578085053 1250 578083803 578083813
    0xa0b090d030203060a05040b040908040b1305040209061b0703050703060e21031b0d05070f1107060c020d030315090b030c031f0207021504140a090513030f051c020705 73
    0x300c0c0910901c01c5a10a000080440c442681481c084c8001000142000c580050362490001c001c103910b60050001072070124242070380d60810b044010000e00c0240c2c000c50080d40140601c910a44d41c5505441d841102c2d0340e00c0342800709070302c40c441e480c0601942c00a0450301039410701206014550f00000302a14a90040301c0000c4000550000d1506540025019540091011820007800540301c0f84050207162a114140b00e002c80442d01180c02c199a00070100d400504610071140e0006054030300c0600c7c07903028042907460035102808000340c10000a1040c1c01e0112270078205070184d4030190030141ca410b0782d403125507200d007042002020000b8035a44680305107289100c0c586400078140d00c00c06c10208240c000082400401d01c060b400c450340483c1d01121751040b5040101c41100034100a00c8402d81c4038581c03a50b29000d1000410054214600c00d07401d0508100b800b403038408092040503814a0600b0183c2c045020446040c05031400c0713000c103040c05a0700e82240c50b03450307006071203031901032010384d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 578086303 1250 578085053 578085073
    0x1902070b22030c08130306061202030d090b0f09180a050615040308090d0c05150403020103060b0304020612180f0a02041b020a030f051c02031503032104020a080a0b09 73
    0x46a40014034034002d000408550f810000185460041d01003a040440c1400e9a81e49a030358500a8641e1a04600d601904400c016402e41c40d080107081202c61070350800098490402807860200d103d014101040c402c400141c0b50156103900e074140c00d041010117400c8080d42010920800030b01002e5030340d54450814001c964850543c1007045500b1654001d0503d49440c6500041c0305110025500549520350341e0f0b1400100e54075032900e280041040c1c4203803560748500f144000350132640c054021801d01c880520400006881c0c1d2001c0321f000b000c8400d0b140303c003551420410801c03c4030481806155006002c501e101d114000200301b034059108603000c1c01000b58070310b10715499074160407601005074130201441d00032a010341c3d10b0102202c41d0345001d030b1a11142039a0207030b050300020240540664000100b100c0b413003880f11b1000e41c00d10120040c500d0214018044003228002e42c5021124a441c540030408655404014030018507040c01583e48000d92800e108000c0c00e0b013140d40b000107000d060114 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 578087553 1250 578086303 578086351
    0x3021905060f0f0c0d05180304060825052b0c021e0c0d0305071505070507150606080105011b0611030412030c0c080a050c1605100503130b1902070b 65
    0x42d4480e440040500307080906005c510380180034041d09000c02822005072202842500380020406004030361a4690242025482007402c1c00c07a166603440c000f840300c0401244c180c0d002040780c0200741e00b0301011400b80442000004420059180c4084291520368240303075880d0040352480d210b002c107074107102c6200c1d00d10440303540b11009284000d80c0030101c40c080500190148001e0314040d4010f812500003803003202c194030115482928100f0100d1001f050103030400c40000d41042d140341c0c1d4000c0600c04540350000161250206028003030600c000e0b01c3c0c075104d6842400052405e007640006060003200e8002c090624217a10a503410350345201c03040c4411404074024012595a0361907a03450002610031516a0015908039a250000b0418100304000d40020f0401011484c0d50740b603124501c2c0305151074100907841c016181c0217401d00009200300301c10391070710854018101d90070080e03a10f69695035010504040b020340031280081c0d407000c03400e0024410140e80d0b8601c61420344100c0a4030403452404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 578088803 1250 578087553 578087581
    0x5071413170309120d0f1b060905150a14070203070b0f1302061809100f03170702030609070e0108010b03100e0703080a0c061d0a0f020103150e0f0f010303140703021905060f 76
    0x201f000800940d40200002d4850350144150701c0c0540306545110f02541e40000840d002510000c0c94a500c4020301d11441020f0f003890b641025a90000718980b007502d030703143c6074401001010955008902d00000b14100307942000f03042c0090740203000c59600c04c030840850f800c000c440314050340210207242c0010914403503030b0170280a6800c190f07400c0341424596a10694902000440503409000070b100c18001601c041017014015004e4001400751282040303440c01c041c100580c000030a580c1408465080c0d82c030082110b030154000e15401090415070010907038500b581583c8000c0904d040002c4404180d41d202d82034040f07051080606011041c810108100300411017250442c05400c1040380100140e050402c1151491060601103185d500034400b0b044403040b00d90091648800304130070800c06840317030b5481741c1e0321102815503a001ca50658070000c0c0340303091500301c1d4845018009400c03c1414000c001c0c0702c510280c1200c40171032001d0686407260312100183c43c00d8544010340360100764481c4035402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 578090053 1250 578088803 578088827
    0xf010906050117070e090108010c1202090d020f0301110a0804030e01050a1b170417070e09031b1203010b07140a1502071401050a05071413170309120d0f 67
    0x2580160048481c00c00c0c070107200000d0104028042e05c1d400e4480039880b0300000131b00a00c008400000c24403480180030300702d121030300d071031199203413041111031540c0c0d440c203000c600c1d05501969030036854485440446d00510300b2480300c624118002c02d1400d0940d5020210718800c1e403190744c41c4201400c03940019625800380c021400701107101101c1c0011100080d40b081c010090050071201c802d80c04004003070b15030354820f0b08110052000c0d4941010b42050400c0103500404c0f00084000e090326040440540381e0150741c60720000d0a11625102107461f00030008030000760041e00c2e12130380e2542e44042d00c510035031105d4001c8600700c9425201144148000c04e45010281d0801088040000c0344410310009500c460307011204641440d005007140c0c6001d00c1458030880c040180002c0904104c803001c1e100400c0544801c100640800000e84007100c0c240d00001202c1d10b15000c1d6100341e041201090540c05040b58464010030789c10544d10040d000011011058952a114034a1703940140100303e45144d00f00d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 578091303 1250 578090053 578090057
    0x2105030103112b080406090b1905070503040f06080103030f080702060406150306092a060f0e211b030106030807122312161b08090310050f0109060501 66
    0x107141c1d8209810503440708031030005000710040b030f140d40c0c0d2210840c9180c1c03000420b9403010b101040a00003150080b10890251407400042818a244000000d01214402c94640d00700a40400c0c20010043c00700250f40203044c0084140c044d80351540d00c02040c050382480180e0008800d0802c0e02c4000780a580864019501075003e40403a55558a940003d8000120105008100d0980010206641d84114a801440703408000c00380c080b100100010610812480b0500c0e9040d088100302107a00007852118032822410805c6074a003446001a1001082c41031800041c0b0b81403142e40c05854012540c0e079140c0f502c200015540001c4481414201d070304074000282440d104101d19000700c1c01e50300540c81f6244c070070310b05542c400c2c03408000b403940110741c0700e45485040b0f80480e282160340c02c40c842c2141d00400c03418889400c441d0415004158191140602d082d41d101c80000c2d009200c440005c46e070904d03601808460700d0f4610f0314072180080c44115900e10410003034030004035441c0c002d409020100c860503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 578092553 1250 578091303 578091323
    0x316030f08070c0f05031b01021803061003030c0c03080d020904050f1009020d0608071d010602060f0a0f110c0a05072c090102040306110c010b010c02031e192105030103 74
    0x144e521550041109401502c06101c140407211010707000b01d6809988181c40c40000d61200c80d074202076050040c9454005100303400c810b080050794034241c0c20311003c070f03a00b61034082082c074070b5828206980800340c0c0000d805882c00081c07440031080260014080010143c0b020440c0740e0316014a01d45112003a91035580c6400c030b501007004481c0b01a009425500a42c203000100c199449015a161480680c0048040507040d144445050b0307504162500419650000c1c01461070117030764440d81850700400c81c03511a9500c06800c40260016803208400d51514447d084d954500e1951707150b903403103003003400f110300d4403032000b0224035247c80422540392030200700501150042a040307000582040100b0f080310030740d800c0c000000814442d005110224144900407940c40d80768021a50039500c0b0842414184803034051114016100010304a80c0c0d143c806003524414041005054142080000b0000e00e100d106d1406905210180e020071290b0f001942c124510080b5004069980c1d010034400070b030210583d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 578093803 1250 578092553 578092577
    0x405060901060f0216120b0106050310210b0f010915080a2d1203050702010207110f040603021f030606080f1f12030809060105030c09040809060c0316030f0807 70
    0x20709520318007140c0f90040d10b6051000814407200006076620809000107644254818000344e0030381c5901610052070080d280d441c10343c884480c5000e4502c2001486139860482d000d00d042545030b0142402d60100145665041000c4000520790742801000503031454a2090784a0f106001300100c00c031085000a44106400d13602c86128449249602e013800404c48941c60039414480d001d6603c08a100350030f101c0c0c9001d21101c0080850380014554001c0d60310400110002c1401803114511080003224488410492080410058141680b00039049814124070105111141c200324001503803668080110a503070340c5003290710002c159403008170801d4190100c1e10300b50841491034170301c880b034904018010766181200070040d490036109030000780c0c0301010f01c000c80302c0c180041c6004202c01c0707009040d505048000690141c801800081c0a0240080c840c81c264076900151517180c28060152501d6402124a01c0745600c4155012000103008061001c0c0c000d029000c40c038010740042d034511841c060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 578095053 1250 578093803 578093807
    0xa0209040501020c03030106020a0303141302120c040903020304050321030f0601032c06012705061f020319031503110d1b050a08120a18030f0f11040506090106 70
    0x2000e8010348080d5000c1007880c00b001c10410080d0300071311550380205a01d20076410001d003126101050303801031680c9281404089194245030b094420380499440210140c0304132128906680c03080e440c0c0d00176081c07810000601d034000c000b820440f9015015100811407060000c03224000903e500f06401c01d0900225104903c16820282d10640c103040002d51801032803c641541502155981c5c8541c82240102da400030052002600401c15400f01c48640395440058000618511240c0c90b4030030780c0d440004a49555650341018402d40d402c40d1040001410300c0001e480754040240003110005011108000350311070320442084045a00389108010f065550700309480d240241e038194001c9061a001000c0b515200803034808010317401043d9540340c80c0005011003848517600502d0715030000e115808040403a00f040b00c424140b1032401c610700b44200610a1814203660300007400003101211800304121b5264100607295004008203051082004104410b540d021581183c0001e451401007202174 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 578096303 1250 578095053 578095069
    0x62003040b0307110106080703080304140c0f010509030c0604060525080a080403031d010b01020d021b0108060a0803032a09030d0302130e0f010527061012020d050412110a02 76
    0x14500206c3c0d841d135107201880c60080030750070554032000b0000900007000120b0005040d0502154040d04144e0001c0c00001d22507101c0d4a900b0307041c0f0800003080007959a083c002d00907905070080903251601d07150240100103800403202c0658600028160207465403012620340541903010000c1454590100c8040300c017130310007900403014140c55400c000c0c500c849000c4100c2c44482c402000145c40d501034400207290500700380e038000c01c0d07420171a140314018682d4422002d100c2c4080c00c1c04440c40c3c4408011605120351603100301124040072081c0301c42460301c1108503c0380019107900007080016401e01043c14800d102c4182d074950b02080188a01d02c1c041d030050007240e220001d284103403a60b03e100081d0700d0003040340d410510410100c014011498080321401007207040c8404843c51b504907101741c802644000d89440c4c410306240d90704148143c418101080300300048a019500c4510b003c0c60782010300000d5400303c4000d902c9001c6000c90341c0c851410250010001e90080c0010461502449845 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 578097553 1250 578096303 578096327
    0xd08030c130e0405160f0f03020f03030408030f0d0b0a0501080f07030e010c03020c071208071401090204020408010e060a020f121005040203090313091505130b0a062003040b0307 78
    0x481c071810002c1c0408154020034840c41c05031014203590001081c54241d0710300c0303030340080191012005041c4142e0f40030300000c0058990650b003880803400041d001a207140200d41c003090a9101c001040402c8030b100b100980900030a42101b03001c1c040c0010704101d0351044900400740007070018000110500307650b00340260064640c4c28001138025110319443d00307587d06040c6031400b081d00003640003010070041203401e004045014140014100340d503528203491041580184c0fa0001504140c0007141c0c00390f1060b101388d0750041045503610394442c4554080c1c9030100041200d4051fa100003001c0310894000c0fa43c5507503100b0410351400e03071460128085480e01900c040741d80c0366060000308181c0c440b440258040e00d4160003c41d1900a2500c1c81e002403440f0b50000d00382d9509004072040501240d014110540b00300301d464039560b00710b400c004402008400441c951001400000241c46904544d19008405c7c0b4a08400701401c1c2c4640c440761349205900c00d019a0803010000542850302c81c0c0064450 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 578098803 1250 578097553 578097577
    0x9150215062112040e0a05090307021302041e0305011b020717031308010b130c0c0305070f0f0312141b0c1f020307030b0429030102040b0706090201020c0d08030c 71
    0x1041070580107507440c100461807240c0c05050f0000701030003842c407005116940428444c50610191604100c01c03610303805001d000a008100c0901020710701d14840d01035901a00c104000821103d088111440c0c48403058442940c8551800e85d80200701c1c0366421200040000071b030000d0480d03501d0000111009030b201ea048a54500051000042d0a50316081040c02811210000300b103000c580c108111051000070100440303186890000d05200707070000c00c201819505420b0441e1a04001c0c03e18855100c034103180205140069000c0104240e004408004800034070300d001c00426544069558581c00141c075160000c00c100b0001c3c1003c10341d1900202840c1340800261030f20340c01d900aa048107004c4015040311708030740100412400d2945449100e0074403404807000c0c0829440b510710040d210b01400c41a5111aa0100d44000309031008d404840c02040400c001e40d43d1440c090038200000c008066040b80140101001117055140801b03110700c4560700a0340072840d58035000d940f99035a500080078111 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 578100053 1250 578098803 578098849
    0xc02012a021e15010e0403080f15061201092f07170c071805010b09010e01020102040b070303050f0a0e060a05060d1707120f0203041a07020307060915021506 69
    0x480b18060300800100e1640401804400321035950300214000581100e400003e40c0010440402d82c03024030741c2d07045154954082495120020003070340c5001c2490340309030040310000d44141d904103016400360403134154450821008490380b0301d528001d00d03041043e242c1d0f68403990b82c80b40500800b200901c20584206e129007005c031412149910184c000f520050300c0f680100301c00b044404180240c503551422a00b02c100701e83c1d03040c4007600a0900512a0450400c04400c1c0b1080e001e90017581258003420a010200b03484403804c0c03900a01038039084809800700c0180102140c220b4005008444040820310094110303a40c0d03420010005100007044a0303841002c0b249400b0110310381274544104c2807401140b19a8541c1c050030003940c00c3c0d0ba4100024204060b407020710940d15070100c1030758155011012905440700140e210020240101d003400b9616001d040ea0020f00b0755088900b9008451205601000c0e20004440680e01c841c0c0c4141855a000c034580e00007400b610f405000030100c604050b264130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 578101303 1250 578100053 578100073
    0x110604030b0f0405060601140d050603101a12010b09070c0303180f210e190e01060e1e0603012105150a0b0409050309210d03020406030c02012a02 64
    0x2040c00c1d07094805028500d814030621052000c00d00c00160b1003482030030400400341c0401c0034603100c1c0c400c0500215503035076a07102080300c958041c05003143c2120540001d101601506609078051510740342c000d48545454001000300361010f018900d030160000388003030b03103e650311041640c00768100e00c021004c00d562000d000205060314801c070390080b40210007251101c2454540b4948901d02c0b015044410403103004100281c0394480d840007441c017000e4660801c00e400f01c025200c8503c0c0a034120049855102c40040348640d8000ca0925812604a80c00a580d030324611215039020403141600780c0080c0d04000500400d22a807407001d035400705140905007220140d4441c0c90402c0342501c030440c150f000070350500102147c54010841d9207007084030200300c0c660b495580c90b41d4074130403105424000c680d000703a00240794a480c41e182e00e443d040207094403016041010014000d6009001d4000482c1c50040708640480c4144940740446007900310b00000158860101940791084080c08803c51141203501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 578102553 1250 578101303 578101313
    0x90614210f03070f030e09040b15040f06030b0601090618090b010e0904120e030c130b010203090d03081f15030b041517060c07030203030f060d0b1306240311060403 72
    0x4080380c82c002c0103c015403282e14a402000d01d041c0d06c0005200d040403909103c08642803400c0c02d60040c0c01d1140121034030aa070000700b40609407041d4030540c1c85291800000600c0075822415105601c240d031440c1005440d803009440300c51001070750844079010f080c000e01c901007184c1c0c44203500172014100b16940c0e8000344001000200d085500700c41140c0d19141c0440720941000900d981408100c001c1c24800c002c2c8004a18840c2501035100304003030711184140d40030f9009008544500201901c25402609a420042c00e10842500c0280c0e0907a0000841e21000c0241010f42c0250f60f8400f003903d00c295002281103001c0c00c0c05910160b4410350f1619104d9910340208481070040600444101119452290751030074844002c280d402032100c01c001c075000003035002c02200e84c8075130449150300c01c0e511000045800c9000310b16008044003400ea00388540d094607004140c0c032072072281b40d0a04c0103c0b007c1009192810340d145003400e045051007401e00005081d28442940ca600c0501801c3c2400e07940c0d04c40b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 578103803 1250 578102553 578102557
    0x5132d060e010b040c050f0a05160501180506060a051005130e090a060b0d0f1b051c12020705013015080f031602131e06090614210f03 59
    0x319a407581d0342e6048046681801d000b8200d041c641410891b007840e003010130b175480c24801d42d01110308100c800100310345035100e4815002d04064010000700440c00380c6150103c4803000a030341c191f5540c8030b40000102a0b01d0a850700c6801d9840c090804212440b071440150b4079500003084580c104045030a000ca26400c8010311a84540c041c1002030124106a041060440705201080c0b4080e2000e541075034040741e225885031242540c000b080032848000f1102071003205103e600806c2d40669000c40310380411804486001c401805500f450005078560103040c0e070365007000d11506001c6900c0c212102500e00d8003919404040d241c0701110030b0382e01d0f81d4a98042c100d4225804a500c0040d01ca0020300100c08208515a48151400c0c02107141a80800d0882c4004041c2c0c040280f080c81c0b6180c42c5290300965800205d000340c7d01924101004028034442c40c0900114060306121918110b400291800c02c1080002a00d1014100e81c01c0c000d040018041c140041400c190301c640f00c0d07002a00208402000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 578105053 1250 578103803 578103821
    0xa0c02130c110318060c030d0504030503040209010503030a0806040f0e01090804061e1b080705010f051609030b06061602130606081005030322090e06040605132d06 72
    0x10001540341d484490203091201d521160b140300d0361040c40311804c4001c492180c0c020003c42140d09607140d81013140040d10b1841a051312250080c00c04050204058111010f0341c0554402c4850f1041c41c1c2c1c0f100d042c9942c90217515082c10014000ca0045460313410250300191515400c1b00c004102c07035642801950a6071400442101c0f42e000014007000490762203d05107050050001c3c0420703c248a81301300900415003041001e14214405540f60f080019040c200e40381d40b54400000d104c0508805011001028121503a034261080010085a030320b1191032030394180c95100320b000040c1c0d140c000902241c1e40020070155606142100018090303603541030940410317a211107000c9285410310000030511240905004031100201509020954010040d61503c1380c3e101200001c000f107071004c60441269907403000100303610380003d22904c040045406403166005071001d204907205e2400c0c60f154200c5072807000e041650b02e42104241c1408000207020a02d804610341082d29055803076030700450b441c1507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 578106303 1250 578105053 578105089
    0x6012304080d051303080903160905100801110f0903030708120a0612020d08070c090e03040303021504030e090705071205030601020105130804090f0207050a0506100b07080d020a0c02 80
    0x810104809401004031000303441091402e0344c18a902c29024800081080c00001e0410502141100a41e202000a0025000090861030b10142d0310055840213090a54290701200c4003a03401050356403050203086c044002c0c00005d240f80040b44071030f840301c9802500090b81c0c14042080401d0105246401070700841d201d0104080c07540c104007800b0000c0340e840d588803003a1410901c50b201c0159407480b500c0c000d00d40e00030344c020b59a0b602601d01140800340d0354108019003860100380c0104110000003503c00e892080d000c460f100e41a01804140b842011078009000030401000104075040c05014990044018104181451200e50342e198030500408038500024001004004043da4240911500b110151000c0700c41301c045512086400e20582c06025949901c0d8071014201094650441c0d1655804c44191795405001d840d0241d101c8a0549020001085016021401100da582200d90045c0d01410380303071421420440d81406500031040c1007081c4900580d000025845844054041000e01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 578107553 1250 578106303 578106307
    0x207120212013213061109040510150e03070504090510020703050d05010e070e042301031b05030d0e010c03030914010603030912050712022107060e010c05030909060123 74
    0x1901c0d01d2420340d5400030201403c0004081400808080082c00182c010b82080c008075065000590030f1980340304811416070000d10345001c00c030700324004107646020343c0d0111000e881c60051940040703480822284100b54141c103c0c4008118610b41682b00810b41841502510341010340e2424003003c0743c00405040d00819800100625000440d104103409401c0309080380029040511000f441c00c1180c0d41c50310300469a501c5190402080b021410359a40102968602a5070312031400c07410f0401c803014400e100c640c98140c0466030385008074180e82882402c1d90b811116400306801100d200500b003106074145a55081d001021942c816400d804a16894001190390740c5180780040510b001d0380d21101c0500c009000c941e00003400810810204c40341d6000c14102d4020500000d036500708403118440e9140818a0300e1000c0078030100d240710898100b502d5008021045d03600545041c120300f40020701542080121034090310b40f4040c400e400c00e2061502c041c00740c3d100d1030a0b03100d50380d940c841000c2074200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 578108803 1250 578107553 578107601
    0x6070501110c07081501060e0f0a051e0907020604030804061a131506050901050906030a06120c1e0b1c09050106080f0106051203030708090a08031501020d0807020712021201 76
    0x41003011580d0581705156a84c840c1d80740c008014400e050340541c441c4140101c1c50024526030303480d25003001420000f481b15840b2030f40e0070403038070012001c0b00c080c3d402003980a0016650a0021030643d01c140d40684401c074540c1d5642d55844010006018808510141010740002c141c80b56030203400480e5a00d240005c002000e00b00d20741e100c0840b43c3c0300500f00401005595010399009003034411340c0070156500342e103070388908980e113010f80859041010360092030041c0c1400e00228503004030803100103100c0d040205110700004400c0039210f00440000000400500d0021060070100d82446d00c503500c0d0005020f01d0540d01c05003500c0c915403020f403490f44102c0400000c0307a420311440004040841e0903d2002250101194407800014540014002000005a88405c05000c55080994403040320b40d528505030502c0001c0c0340304404100d005100312120032001074003956096000300b84540040ca081d81c40e120301000031014000d41203070041c0212103855154034090080040142e1801107001d21244 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 578110053 1250 578108803 578108819
    0x1d0403020f1f1503060510030209010905070507142b09060309020a0515040902070828120e0c06030405010204090507050a0801140f130e100b0f06070501110c07 70
    0x1407101c855106039004001110038012082c2018a01c0a01048011485010400803d91120b03144d50019000c241000200b0195900c00003840c000d0301e100710303499401a625071700408103d4408440c4880421401c00003900860840c3c030b20226030140800c00c542e600e81a803943d5403d00003800b40141d480010f088084e008084c2c112100a005d800e080c60100329001399070b00041c2c0204020700c250780c050880c045c5100b6030601d0120840b00035044010003507541c0e58291504502d540d1020490a08000d00c0303103d0f84032410481865a4581034442d60382d00760151020f2400030041008000c2c81405124540c420030151301c40001031440b440c095800144c0f198036168904055078030003040c0700d00304801003000c0e03001c40f0781101c41c01e0306641450b001c20307201c0c1e0411030114180011211145a000c181600059200b020b02e8102c1848514a2402ea4112003404040e18043c0c8000c0784080b41e00070304400c104491410554041c1503007a000c0c00022441c0d902244003d40d003a4850a042c0c40590800042400040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 578111303 1250 578110053 578110063
    0x307052a01080115020705090c0a020c0a03081207051603030204030c05060c0d122306040c050f0d180b101706010b0409180203030d0c1101050601081801061d040302 72
    0x52104611503010094080000741100b005015080c003802c1d5031500801094420004407014000c060325090480c20800b08a41ca66000b50114000511603542495405d00307001d0850740440f680095000d06101214000b417180b070400419a40c1080340900188030805140402c80025500a840c01a83e4605504003076180c800f840d041a4000c00303080000c0142e0040028480d0710380b40a5280620140c20014400c1001c0c010100141440390a11440a0841101194030601804044a003045850b080c840c0c16921401181c0810740e1001086c080c0802e040c030aa008070380c1000c0403a490200c02d00700d503550003030140416aa519155441e45005104040390a446480d40e00d40c041c0090015600d000c000d19082d200314011400c00708d82b5249203006a14644044c443c400b0f030300800340c0b512840380040c4007000b00b00709040c02000450141404022050604c41c1602880060f90780382031704c3c1e4940034072280540341107241079410b65a81200260a04e0701c1111105140010045160700c2e003800e00f0000e16107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 578112553 1250 578111303 578111353
    0x190908030a1409012a03090f0b150a0f0504020a0e0d060605030f06060a120819050a0e010311070303020f07060f050f090d0f0f02030c12070512040f0308030604020903030705 76
    0x582c1c9030441da0007850304001740c0c01041c240010b85244400b00d9034001103003c0c01d10184000c044d10603858004042044a1811504c00d440d00520001085540020002c0a04252140c104142c001180510050500c0d80081c2144c00d911b0500b00c46006441d004582c1138483d00b14255642e56842c5070502c00307440c040c01585035075611240204014106600001c00d444060301c10b0030200549c3c2e034450b00801180400751112102c2644c01d0350010300101c83c0c058010340c001180d000008a0621940700b2542c042c1c4140d03030401d68504a05400c15129540030340003907100c01000f260320442449102c2c00030382640210749011881c5940411203080040030b81304001c40140140340581c01410100c910036a00203001d5440d21407915020040e4601003034164150300c600c1c00198114014041007903c140d56590080450501c5901100d02881070038480391103a015900940c41c2308001041c0410200314000c010b183c014100920052804284000080c51548050001c80301500070903002900c02d44109006051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 578113803 1250 578112553 578112571
    0x20703021207030909090c080f1507020f0a060b040e16030312020301080303072003070f0506180709050402012d0e03010b15130e090601031b0e190908030a14 69
    0x30580b0a0340c020709501501d000f0b610521741c1c0c5410903014801c2e4910004014480142500d10005006004644403200e08001c6d030800b00c00100421025480001c0c0c03d1207d10030f600c081c01c180b46180c0d0380d200103090034500d02544291640c04400b20b00c0418004420f03450002c00d0901001d51a40c60003500210419003a6900a0300c10700041142600c04000c9a0384500280b420407520100c402141c0e00d14030b40e032007480c03c0b28070000c2012400c03c070b04200080c044c1c5000d80219100340d0f0702e9030410180b071031400c8808503054014a44c1040303086035541001c2d42007841410101d0010103106075654000170180c0307604100301c0040c10007550240c0c100d0000b1840b600160001c2c0450300480001c41c1021b66010014604010002580c0c00142c25501d00745000d8210b61030300440718205205c245617101001c0c042512800103101c000c030016031020079080219003c10b80300740c2d0540c0e0f50721449070009824000c00f00c0328548411411b03002070160802075200344200d0754000307030f120a0250100c4e0781d40001445260 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 578115053 1250 578113803 578113807
    0xa05160b07030f02150903040f1e0e0709050409031e0306140f191514070201090b0a020123010906060c0b0a020304080424080601020a0c0603021b100207030212 70
    0x1254103101021111010303014100408a4512124200d24040c864464001603044050900079200c0010000300200e03521b00129048540c0c039481c0c0781c00b0542300d06041007181c040245081000e002c030594007540c80075140c20301500d520741c1c98022a055070b00d40101100010305558041d0785000801c5407441d040c562901e03042085a0621040760341c40c1200d141407038032459007504e040c0040c0c0e031465550400a560814040c80403903031140e1410341700704c1011203070b0301080d000055034140001c000260342138140c0507503c103406136113802040c0f09594002100790f000c5548459101454408048481d503034013004155140003903250032210422154142c000c04200440782e03080ca030200d040c00010680180394040016aa900d0314a400081c81c400c41e400f0600e050030300c4000f042e1500314541041401701d01603e402240b03541e150012600c580408200404021000303000740b20b45032003036000e8148808104020202814642140c5142c0075140b40c01c800c003150002000010154103203c10302051381e518080314 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 578116303 1250 578115053 578115059
    0xf181203070c030b092401030209061e010e0d140a0c08011109100215040f03080c0a20010609090803060a0b04050a060e03120a1d0306070c060e01060e090a0516 70
    0x51140d003401d00c0f0203026014008081221003406005000c500e42c0b071080e80720041d41c0324000306003410307209210586c45502c048002904a00300414924043d9600d152101624800c1d500155545034088a0b500e401c810b10b01070400000b412191045200c5603041d000300751445d524079000b15076040c580c00c40001d503410090085841c1d040171003612100300e4100e5000d000c4141c0c1d41801c91404207681c0e010006081400b00748400e204680d203030701c80000d00940c0ca8000554600c000002a07115200322440055101c49821301000144003600515a64038000072440070380d112203d005503030303807140c056446031000400e0103003a1030000d0010008050030400181081c1c904000070303010744410304c03d110034882201d21051040d80e0920841d1072000d42680d081c0e0704d414940e00000e0403840900c80d03581d0b80071031049001c5140d140004d0300e148912815941d90419411590781d0602801e55803064041d15074030741d00086810702c4200047c41c42a18808014400ea0900b400c0c507503d811000c01c07642103654081c280034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 578117553 1250 578116303 578116313
    0x50f0705031b0c3607081f030f06050402010c150b0103151a0c1006150e220b060705150906070c0203031204150507051308060105130903050f18120307 66
    0x1d401d00244c10081c003101d001250070a00d0405103500c100450640104002e8016045000303140200f602510000316154100d1030448440784c9800090100100c0b400c08a000502e2604402c0e4030601c10301d4001b082642d80e030707144180707918004100820aa12000041c1003968940304040c040ca090814403607403079242c02a406806a03041807124105400041c103214000700030451f9251108604c4c0d42003043c0c6a49001088548107051030136800256215503100d01e03490100c001d981c004903200c011000a1a803101030348014070074020540e412040902034100862414044100d610595091240b240e24148422600f0600c0041103081031120a412075409078034000240c54840ba4004078100c50394480341803030b941c220f8182c40310768552402c0008000700540e20002824600304501404484543c407841d00c10340758402401071310b421416216852001c1505604001083c0f80203084c030929191420014a0304c0c0e82c4441c222618110030503100c1045828a142c11140c0d2508a501a40c142040d0380d40b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 578118803 1250 578117553 578117569
    0x1e0b18060604060509010c0f060515180703022a07050114070f0f030e031b0103150e1f0f03030801030507050d120f0e03030705070e060f10050a050f0705031b0c 70
    0x2c0d00301304500803400c40c50590045a800e40616002001c00c84135900c0c1e443e0a0020380030803255041d0040c51118040e015080482c3d240c0d0504100014442040c2d0f1f440324214000e4003c00d04a00c0d81807114207024900742941d955a06030580703418041c20a07070f401c110024010100c2c030903c0741039480742048414049040c038070f499902c460780300408076045140c2d81003c07100300710f005001c180c0c1405040d500e02918074207084c481480710303002c0e00c041c0644100340840800034030142c807032490362403020b0b0001101d00410100383c07110841c85450300503040d516400320020a80007500110003091081d4014402d002080003001c00400044600c015082410b99508500d00d10100c070010030310540403285000e41740a404268450500542129180c1c1da141c00e02a80c0c036041440351107105a2600017081103401e117114070301001e0384090310082244d54800c000b182c082c0d000707403010340400a05111140448400d80010309080b80203800658a42c800108035080e0001c01e04101c8009900180d01500c4c643c44c0e85003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 578120053 1250 578118803 578118809
    0xd2009030a06020703030b0a0806060306061c0b0c0d050c0c0c04050103171b01020c03070b0f0106020a02310c020105090105010e0a020c0a0b2502030a02030d020a031e0b18060604 78
    0x4400750704c550036460154042c0c03010600080d070098101802017015803002480038440c0341c08030101c65003501c1d004107125010b071134103070710440000f291041100451040c062035a0464003102ca05417411101c01c100c0f00444100fa20120007000b00000d140c041c2000822080400c0f032011541045554036503950b003403800e442075569402d5600d0100395400c150001c884103100c1001d1080003503550b088045100b5450340e01044040b202d442e103110101d0280050700714a5030580f022a001480061441e03002c04c110541000704041046da404400090001003009080f043c1501d0a00082184c4000040181c00e440004006a195a250800401c2030300c2c03400c02075540000d000d5500603031300e00c0510304d05401c0280149014018440d0304061081c98503005a404c17001500f114000c40c4a03000c40b250403a180d00c0340210660040e4401d0024041c50109940206598901d5090000c1c0240050000245480800d100c3d061040d5403003882114505010130700480c3c5601d101c070a03c0d1039107030402c0001c000d405980 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 578121303 1250 578120053 578120063
    0x20a0206070f030b0306090610290c0a0c0806040606140109050112020903120301080f030708030c090a1e0f17070e040503090d0606050a060804050d0c05070b0d2009030a 74
    0x202e054600c0b9000340e0003850700d008040c045d280c262030401c80c55651100e058030f043c46922494807002903800b1a020b0302d4064002030a010800e14601003080d44c0594201549044242c00303100c0c000f200285032903502000900319100504810314150408400300d03403590b84034402d07050039031103510403c0c1e0b8080303120003e640007400d003c910446288804c500038020103c0c0c054051150000c002079405055001d58103c0c0c102d10200c0310101801240d094490244902c0148100300600100340d100c50b8601c054102008003402510143d5501e5484a404407240e0620020b52100050203000c00d0240e14002c801411580e261010141c1e146101d0720341d01c801500c6902919151000410104a014012103507400b200810100c1103507103e091020003030800c1e20600b07104220803c0001512400780074010700c280c0c1c00c0406009500f00380101a02c0c010000c841c03c50381e90044070300200f4800c0401d4040c21042d021780c2c000040141400703032140100c0d00d10300045002c5000620a0700b116940004d074035407102d5800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 578122553 1250 578121303 578121317
    0x10c02190f02090903130807180606080a0e010902221406010e0d15022101090c0801120f0803070e031216080d0f1107060c030912050f0c030313120201020a020607 71
    0x1101950171802403c00c11810b074901013030300141d45900000c100c825a1100d031707000d02c002009041e6050490b13600b482040003182c04c2e480001e003c10705580c04040740728000000410300700c0ad00d0703001130a218040d400308510284400010019108113110b4020114074540c1c25607441d040c0940042c010f03402e541d0301e25128907680100c1c802000b000c000d03d94a484403d1800707544603008003030452a4104224580c041c04507110000003000200c0b401010055001516510b80c142d0801011001140030648282c607440166120503000461310f40003140314003170643d00d204045050707608040c141404418100d0041005110100e03001e46c1d100e9201c003844c0d50100b40207a07107106011600010b003070000d00c002c020524040e52404011071201c02406a18841c07101003124415406003941114288100504100e00d0900600318090082e0b0040c00c005409980d4141062820300445103950f0080f510300940c800b02203000d808000740070820602415a0303000039424003004920080d40c035035000703054000b00108 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 578123803 1250 578122553 578122561
    0x50a052502070f060816140a0c1b030b150f150307021c0f1b0309030209090a1e0303140f071d041b020c011b02190b0705010c02190f0209 60
    0x801610b0001c05103503d4030b01050344e4035030001e40b0310700301200e09802d252030b5102500900782c0b040d030819490f00c42c903264050400051980c00c8880c0d40c014181154158000c11442c038001304510f003030700c00440c801c4101d581c5901c0c000103e061140c0d12224098000d000c048a0201170307a458a2640310314591100000743c9a41d0388440c00ca2505401813220010075011040c0c05c400103030300c8821462100c02c1c40d1112807e40c00c104032010305040c140c400140000c0c0d0001014001031400c0502107401c0124035046403c4d42d43e55880f020740c0480c1c0010070904a00c101c000d4001050380500490707a9006c043c040300324240c0341480320b1030760052005002904124400c043d640c1e003010b00981d1291070040103481004910210220861003e500802002c058441c41c90101c1456101d055140b59104500c103489900080c3e542c284980101c05085951210070703c0766020889940d034101a20003d4012000802c1440403088040c1c1080003254030008516400d00107003003c036008100c0d0076090f0781d0540e020055a51 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 578125053 1250 578123803 578123807
    0x10f02030d022505030c011505061207020f2407020102040b37110f0c010c0303050c07060912030b0f0f06030718060c020f0a080706110a02031f050a0525 67
    0xc024810780220402494403c01d0207000400342851500303110081011000245201041107030342e1280603030115081001c0b241078282d085002d40c06c40d9440c0119803191004007426403c1c014a4101000c09007480003500030f03c4d44241d512544c0000300c90000714a0300f030820420150078450380d940215440d00030620a03405181441c2e1001704010482095041406c255000404002c8824910783d020300c40c0c0c42140c065180045110b60141d0303016111105042403031754003075020341002882404040b80170700003400821004e0040010903031107000d908111000c1c0d0340c00507040381c3e061404613001e550080044001500e5401c3e0620130440e08660094607543c9008e02150f00c00039010306001c0b07844d1405400141c00d40c000d004035030104d00c00c0710180c500000910500520b24410320901c00c0700c3c1c2c400e41080100c1801180c1010072040100c0950b902c41140d0b4022a2508002c600d0a0030308000344c071303004002d0082c03510445800010414060156044c2003e0300301070b22041c803030381c80a00c46801031201c2c401d84c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 578126303 1250 578125053 578125087
    0xf060603063c0f1e0f030a050a03030213060e060a082d0915090714060f03010806010608150108060f120f010e010c0203040e0f0601030f0e011a010f02030d02 69
    0x60b5910444150244a4440d41c8280100d03508914050320301000c03580c120b460092040040030350b00c111000380310884801002040b85108110603098059200c480c1c010403018414511824007030b80340503a480350140d414090740f85441d80404108400108401c0c81a6104011a92003c3d090700d003420642d10b17031041d002130000c107581c200c03078018013544102c5259419210205119500314026501c05c0d110004030711407012030031240010035810507082800118007264188141d164054403003402c00d9804c2036080c01a91003a00004150343c400c01c01000760b02e0340840300951107044a200345d824640300400180010304041e290510a810910700d403803c54451008000215104000304c81c820014803501314001e00c9043e01d0044203508003401003040074000000c44003150720f90440c1020981d10a10105022180903080604150711040d60031100c10150040b640c4001e9880000940f243c18000b1400140e940b81d5034141c18842c0c0700c04074003451074000c01174581d004c410b520b016907074010000d010320f551 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 578127553 1250 578126303 578126359
    0xe0106080a0627050705070809060c030702061308280b06040209030d090306140415051e04060b0a0e16080402040e0f0304290702010e0a17150f06060306 67
    0x60195059190b0502010620150012070b0043c0070030058a49000494451141c130324040c1030300104102048560030700e6402001180010130580b810030080390700240d0703a503000c5041c1c0b041c0c122001070709001c854402d01c0500041c2340c88080d000c91442d00c00401c074401c01c03c8200043c26203488000001d1198644e1f8048030312412004091f241c010740941c0c0081d0803100e2501003902c5032450b040700404400b880c0c0c0202030103641c0100202d40048048988040a400010b1070064900707203964003030004200d5000918010741c0f1131070010803d8601042800545141a40480d260000300803d100d42111070307000069076170b500b0703117080a03141d42c072400410040d00410600c20210b1140f601c017054039690100191090ba110004403010701d00e200d26440f440301c800303150800030801d8100300e01c0c401580240400400207501420242e00d080c1c1d209a0b070090b00e0701b10b600400c4140c100c0940070680c0030f0300c174180300d500c25039604118100d0704212021175854040284681c1c0107200c2c0080a102103c1e0785928000c41c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 578128803 1250 578127553 578127569
    0x18150613020a11160815010503190c23180c1b03070c0902030105090901020901020304180e0d030204080d031a010c0c0312020106060905010e03061f230108010f0e0106080a06 76
    0x116138280540ca4903810b01034030030305c5103e010f41902d0384904510080d44604030343c0018000c0648900e6029070b0040603405000841d00c00004060001d41120087c84100210401307090000c00072800c1c50900c0300360304051003440340088482e01042485211035007a500b600340c841c2c1d00081f0924100142c03510718071504d000501b500001000014000c40182c005505a500036607600b0300b00e40b220500345007030340209018180980c01c10b200500540e0483e007100b1102103d0180c001c140e400e16044041e0500e56000c1000740001c2e0009010b200c292800c003c0380c03030000d0b0035160801601d000800c00c4d0480c8105101705034100321215250505002825510398040c41c1c004034182803c070415036010340200320030700c10400400d80d0500d0003e0103600a40c410b42e504107014000e4481551021001420000038081c18010340b00d06003030101c0c01074003840940000c0380e9840540c5c000c45c001100050240701050340300d04c0031a00c81c10b400307016824104440394110781040c2812003003512a89104405000c0136084204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 578130053 1250 578128803 578128813
    0x7080f18030c01050f091c050304030e0d02130e07050d0f1416090b010801060c15051f0e0604060e0403091707170c04052512060e18150613020a11 64
    0xc5c9100300c20010a000d0292082141c0c52001d10803c0a0b04c4210840d188002080c02800040e01080c064480010004801850f845001034154001816400c1c0a04e17252404d50b40c07243c141c00503450401140c0b0103488111503080030701100c1d640300e0708100c90b4003500038540c0002c0c20301424003807010045450703003039036001a101c40540c0300c0500c1c2005001440c02580000d03804000021814044c2c81c90307101054001d011008001044401c540c040d00300540030421120559002c882c4221500d001e101c042c0084c0481440642480302c10481940c01c19041107104c403a8503018030002a411442d40c4040350100e043d998081a030800349142081000e90000700d212000d144146840390000c100f01402d07001c225401c11044d200ea103004850302480c0b04040007544c0d640745540c0240d6001d501540c100c0c00355034030003143c0e00c0d0300c0d0b40840e55035200a42c3e000d58036060300d04118560b42c1701404481c410101d100780c0c42c0c00500c0c2c6240081c840318a2080c45500c1c840d8001111030402d0301c9840e280d0840c4a43c0da08440d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 578131303 1250 578130053 578130061
    0xc10140d06150f03051003060b0a050303040f1412070312030204080a0309153e030c010b01020d0c05210d0501150314010e010302091f030305040e07080f18030c0105 72
    0x400c000c06004142c00140580d400c1c2c52214001d104684c014601c1c0003160351510300710364501e40200580314849038002d242c80c03400a407a42e01000200041d040a00c0020161440c00d0041c0503010038851400c1e214000c0024940c0d004a07000842d2802c40750072044901100e01c071100145c00074412500294040e0107500f18141c107058106418200b1601080c1c0b40303403002c000446089809c100075070030b10262a481c0d0721034010010f0114005078200d89a400d111030714030003a14507903899075100d40d0301020603944800b0128403540e0180458105060603040c01d100d01e600c1a074600380c480003160100080320040c15002400c08100005807248410070f80c81c1000300d0758450b5040a468120308240e42c000a00305410f170403d140c2c0d2140114100e1794030100b81219030742154200050a0002000240ea14034400c26818444081801d031800850103030321107170742e00c2d0305260090f0540c890007800e010038460404103112450f410791903141d9001e40441c0605c0c8820110b124058111b00c600500c4880d950301345800c1c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 578132553 1250 578131303 578131319
    0x2150318010911010e19150509040e0c1504030b0c0d112d0705030906032d060a060906050a0f02010b2e0201050106020604030f03091401021201080c10140d06 69
    0x205283c09001d80729490f6420a00341044150f00e00b4211000c00d90005140c00c01001107255200ca0080c0601c0c18054103042544010504441480e016080c07107038804210580390b401c0000320344804030306c0341c850750746061706648901e001c65002410035214500c0001e41d0700700188450380030310201c02040a50a0b900d0b81c0e4510300c0c03003400002c83c00302000901c000d1107204011003803e040b80d1030168840055410031003084100f208981004245800101f2082d1480182001c1d002c40f400c2e400340240307041110350522209100d580070980c0c100f9800d00840810a000b0f10b03800c90190360842e2413a2405003a11400b80c202240036208100106401c40001180302e54442803062821002d0170940c1c2e4200161611603c081b400c2e44c80038411070300542c0150002c2030100380f16242000441c0001e003000704084481d030341c1d100340f0100001c01c01380c00c9035400300d0050500081851150300401c40f0350000c090025541c00000d2030444196800d40c248101b15490301c0c0104c64034000d031360340584e40030020881d0b80c2c0e4620072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 578133803 1250 578132553 578132573
    0xf0807030e091f03020d021305250c020f27090307020111010c05030c1608030c031906060e2b03020c03070f0b04031202031e25021503180109 62
    0x1140308841000000e03089280d403070f4072410000c441c85107000401d8556001e02c00001012076081c0c1c0c22541103050000012001d003d014000c100280380c0860340411402842e41c490308042140c1c003000441070148000d43d0b64402c00c0c68440c2411603082d41d851b0031802e1813080e011601c0000304043e408807000c200303080c88080082c101c594002c2c2c842c05220500300d00c07490b080340d80f9030488602188052012568610094001d8000320021103001d072454180da84401840740c00441d0b88000ca15400001c00400c185c080144a01d0984071341030034407410b0700341500038043e608484052030107244040c4000e4603445502c1d1203958021001d04000008014600300203440c4e01d008135910f40a44941e100c000b4250310004803030021074407402d03500d504060071903440006110380d0407004011480180705c8407518001c000d0b0702c42910464240500e41d5600410380700003401c1d5551a0410203441c00220a40241c2c88000c0c41c411f400c40080c807041d0340d907034440c81c4922440304540e06c0c0034050f40c03900c01c0560400000c150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 578135053 1250 578133803 578133827
    0x515062b0f0b1816060806060f040b07020a08010c020a08090d0b09060124020c040b06070b070c0606060507020f040903030e030a050a1737020d061814040f0f080703 72
    0x240041030310042c030f0482a40d8030b44403040c015000507824001c00090744036517803054100d040100702e24900440c00c43d94008507041504165007182000902804602d0302d110040020705c0020b000b880450719024010b921880b03031181c00303003259000080d4011701303942d42000b84ac081c1d68459408d054604021840c00ea440809000f001612502141e04104001c0c010a10300c10f00c00a070341c0208101103010041c8000741ca81d0290694000c0c4050210303400162400d10b241d4803d000c5590b9650b1000600c1c18060281d0321a540100280300c410801500582c40c2c0a0200b080c090083e1000300e080c0710545000c400501c1c00040310701413408007141d50b90700f050b48040103140c00c200c6c603910442c00340036401001c004104140ca074040d00c900804038640d000114a01148007880040c1c052880403a59800090140c3c0c0c49002c04d07000c1f2a51340c050078020b4000030a040074000c200084100000041e890150042d140c0241002e400854041c10f204100505125110810796111000940b01d0302c052901405d1030030046 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 578136303 1250 578135053 578135071
    0x6041101033b01020405030706050d1d0319050c03120408070206030c130f050f04090302070b040b04060206010905012904090213031101024b0a0515062b0f0b 69
    0x140b44400c0b5454140240c40070b130b81c0020f000d00500b43c60144203446690040003448417003612041c00c01c2a0300f03035600440302220b800c42c0c0903544e0b90202c4101460240c11204410090250600c62076050f04400811707110070300001c03e000c080d2a1518180899203004412009521000002c100501001107602421340f01c2603036a44201d040c0c0e158480710390510140d00407160007496031140c0302c3d428a01b0b50494104e041c007e0041e10364464580d003034421a68065084801042c10002c1e04102d000c1e410810640100166903041103103504003095100c400d9502c2d000000c84100c0c40c0015100901c0d04c504580c020011034a04560702d204500d00c541c40390807544030035565600650303ca49a00c3d400400c074940900f80c103074011044200c2a04000501e0342c0b01e458039010184440414030300943d0100400d0406906a07070040c9298042d074a012460725010721103d0b060030b0010341c140300c2c86840b80500c1d158a081c0340300341103c2d00c1065501501e04003032105070203000d0181042c92035040c0200c102109000b072440e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 578137553 1250 578136303 578136401
    0x3032113030e0607140a0507061101060e01060c0c0801051315020c12030a06171b0102071d062d01020705180a0921120501050f030604110103 62
    0x814041144401810003401180a18190803054980300c0010000c5501c07491007100d04038000b0b10218a0200b00c07200441c7c840d0305c525001d220450304501a002840d2003100280641c1d4140b10448450320310600c501c1e82030280218903070041220140c4041c02816024008018500c0c100340040300f01000b040050ba0b10490034074011b202e0400500071188500e0092004290603507012607114a1548000d011701200c5a580030045000da0550612001001a090040001032403900000c080400d050f98214195400340004110700101e0350701d41d405070140b900000c2401e64584000ca120310101c899503010a48814000640444048000702100c003c01e90844c3ca003a0344071030500030a0946280300816001100700010440b0b281a00b0003a5043d200c0e280400301e213040c01045031110715051484001182c54203d96000c00c042d180701e1207006107000c0300c40c40310200543c0007007511140040d102401200d0035145242c00d69009420500d40d8281d80d0452000f9000c00356401c03085200c1c515190381180c081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 578138803 1250 578137553 578137561
    0x1418130c06080106171510030207020406120506040b1009020403030c0605060f0a14030109050f10050618010312020109082b02030912071a0a09020118141509030321 72
    0x1040b08014181c0c0d41a8071450628880180780304d441840091050003c0444900307221010b44075030040849006243d03c000d41c032103d540c410003098440360b410686078054241640e04c082000040c980350465000014a0415105d03103200d1004510507030052904580009000020035038802001101d43e80240d0007009540c030b9001c10400d40e485004c60300342d4005180e880030f10941002004d02441003500400000305042655556810840da84140401c542c1011804103180030b502d02a0729480b6000f00c3c0c10556030504400c0c3c0000c80601808007500e84130303440c80501c400b54001d60161601c150015030882c1c45400f0070207000c0c0c0c90b9a40b040740c804185003a4402c070200c0c0c0041d00980c1e0040ca4400301074500840004a01c0305070f6000040c0c00c0e0303040d41000b0b8842802e4100420707054003401040d800410b000b861400054204005050070650b00040c4603010000e005084080c4032040000300d8802d1450b5464002c00b0005000e03542d00a43c0c03600001488a0440035204584806052013410413850356803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 578140053 1250 578138803 578138807
    0x16020114131a100515041a03061905010c11011b080c0115030c0308090105040f1220031507050c01140105030d02030403030507030e280e06060703091418130c06 70
    0x603041e12824000c0002d048240800d05d8456a003d01d03409054602c5803c05e40d55940b0031441d91010701021400c3c100c000103001c1941800c0c1000400c09111000301c01c921403401300024213081301088003900364a400b5440840c16841181d0300b498040d040200e58a01d1822400c1940c05544211040c0c5c24941c607201c807a440c0000224820001c0726007000c0405400c1d440d58031800c2503035000c58907883c1084010000031440071400803001c3d0142180c40000b20070741e1f0742464925101c21619110074180d0f02202820390059500040c25403010440749880102d035101c0d000190f510380148210300c603280d400c0100344a04404000d010b181200c904904031206940340b0380090b41c07244140e00026001800410056001c2802414001900030f40074108035252031000312413482c0400040c5120525284000c020010080303000c640320342010b4115080c6150000c2d950340a40003002e1446219651100100301c584a5a03c401c10420b0035403112030900c00901e000142036828049034502150844040407011030124 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 578141303 1250 578140053 578140103
    0x3140319091509210e0139240209060d0b01051603020109052e0222081b0406080a020f04091e170f0a0e031002040803040623031602011413 61
    0x381c0e041c1c481c0c0601c202c007014640f480307d42080e8100014a001c4906000e5401894500d840142c041d40d40c640f8514410b902d4400d1102c82c00070b40d1040c0c1401440030091660781d5030222014003412402c00078100d0300400059459014a19040034588000610b11003070580640084800c92b2054095840740b40c001000c4240101805101c0901c001c0306401ca03072408001580180a01e141031000c554440b80000d0405505003860b030401600798101c00c0011860702c4400008581d04001101c05020b151700703041a00303599440034000680b00b00b18482200c0001c0d107071540700003006604015003a20f50740540861002852041c4800c0712042d41050188604403468004d07140c2811070304121a240000c00c075022210b040389030f00c400786c1c54050b41c0d41c40d1802030b60901c000c100030402c02d4040d42e107030361901c08080c090084207180001c02400c148450703c298440303001160b5019250140d80b9054a1800d14100c2c010104101100203429a10080c450099041590388120901c80c0006244e03040310522100115 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 578142553 1250 578141303 578141327
    0x1309110603010b03070c0606030b0123010e060d0c0e04020c030a120e0c040507110601090b13061a130806010303030501090b03011514030f1203040314031909150921 72
    0xf00700a0000c2000ca0340b01e03c10a9401d24001c1001048003612a112030922242c281c0c0402e13400f06100c0145006203ea2043d00302602c036090900742c178040040c40105a082c400c034014030b076480e580c91402001c102d0040c5400700031220003410854444640c1c0d450a80c0e40c5d44648400030108000c444401180b803040e014880e1800a8480984040c0034000e00340005070a018280c001400071010010944030400c0084c18000d00400c900071405402ca201403014044e050103c85114904001d010321078000d619445a45488510284a503141a03090350140d90454907041010103015180c0000241607258100300d05a444a4008101c0c1e0405402098200d5900c446800929004131104002e03074403a0064600b0b95100c00342c192002c101e800f1010f58200390802c50054850301010050000381075000c0c41203c401d0340c40300d00b600c1c40e40c100503034440403011113501c0010941d038440080c1d40c00c00010707216240c0c003941c800c0000c5c441d4551070f2a04510a440443c0c5c44031601c466281c0009001c2e00c59040110030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 578143803 1250 578142553 578142569
    0x60b0310140d1e1707030207090b0105040608161806020321060d1115041211060a140904090c03151109010e1c050a0b04060608030306012a02130911060301 68
    0x5142044018922807030035000c004c0d50640010303403005070032910750070060a801d03101ea8042c00740e550030107044400715811024000d04101c4103000502c122904007112907004620745041c008002013648048980c4900280c0c4150700701c10500001511070340000141844a00c01e5105454821001405d2030713803000d040783c00300c0d80b1104134484480402ca14505120f0104d80c0500031010301554032011003815446030f8400c07600610000402d1051041a24401085803401c40c0c0301403070900420f80050100c003203400c036001c0124002420200301d90701c59011006a5600c440f05042c1c0b507540c1c2c1041065100444072240307042e41401380240380503c0c2c03d01111801c2070140c580c940018422001c0c0402c0d444001c1841117203100c021440703404160100321601c245482192509201c0c50180707090800d5564650040c80c50354818014813100ba81c00040100b40c00709107a4070b9180c0c5440d46d940c0600e94804242003e9000b1005c100811405141e075008084e00d24020781d82410915111418401c02d44800d2050240f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 578145053 1250 578143803 578143823
    0x604121401091a091005160305010e040b0609090c03010f02180a030c06140d09051c0201021303141608030a031404110d0503190c110d050c0112060b0310140d 69
    0x100b0100c116032613004009501110b107040b401d0501c0354201c1c0e0040d18414400c801c542810b661090749801054003504609000365550305003603a0300800d0001c00381010703111b5015100010540107041045c0c11200800600034444480202c030f122000b540594070002118110520b842c8603400d04a02e080101e95000820b108000d00c2c120044421449403032401c514130700700700200702c10103a083c055409a64000c04c040c0c0f6050181e802d00c038070b140010517030307034415079006210700103198030700850001c04c0fa0303003090f00040a084014141410301c1007548a11554000e50b100214200c0c2c0b002010300411000d03514104003001840b100d0b10503594045030b000b001d41e03450005030441d5003061450404058820011241400300703815000c00000f0f8102e0050000491124444042c000c900c41d180010800c1600c0801a400458440b40e031071340d0300a10468140182800c401054042a606c000f0091040d06903070360300ca007058110006070480314800c29a003900000c0705031400d458a41000b240699001007044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 578146303 1250 578145053 578145083
    0xe010b030405100c020102040b0c0705090106080f01030303021c050f150409050319020a05060406050708180c10120905031c0212070e0a0b071b0e071b02040b060412140109 75
    0x4002e404e91284070000c65409000001d20903001001a140c1070b0701c40d001038180e480c24034080c00741440c0164094002c11042070180408074882a4043e410b5903058134025a45010503000d8000810b001d1000d40452450402002a2000400c440390f0007003001d00740000b110320b8403004110030303240c0100001c0d1054208000d000710498200512610003d400d00569a00006544030760381440000c9900f6500c40d80c440c010040c8040d403011240742d0195408520f070b04039818402d03032160b840f0040c02007240038912070203408496a00a01003403001d6450701300c09010020031460310940326046041030840401100c000310048011600030b5450340c6854501503849584d54100403600c80b6640c040e09900014a03510100c3c50b501c0506c010400d050041c00401c030600c4d504100504800240d9100c5288480c81c8e00174800307415446503045440254104088011900030f0000500400c6035210160307000b0400540003c101c1000450101c1c0a8002c1018100034050038041509803480780400901c400314881d440b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 578147553 1250 578146303 578146333
    0x8030103080904110a022d030c061501020106060c061a0918011514090a091211160608180f0a030807170f0c07110405070203090420040905130b100e010b030405 70
    0x26982c0c8507807c181900600310080a1142180c0c442260800d03103801c41c5042202c03610114540030000b600038030013007080071f140c420020300090b000c410081c03582c0c1d02e13a2140c030385040d43c24121400d1074000030503054181c141000040c00c01c0c6920b1004014950030414008030203001031001c4800c50f81d500100308681d90074141000011365005040502140e503030100c59020529040c05014900c107192a131444a009081000349401e403882e020f01910256640c0901442e64002c005a4000f4503103640100d40b500c8090384030b0b09040321620210311902c2034101020a041d070213a0070314090201c0e5140c075105e200e082c201d100d15094003110700340300105004000c6021010504c0050800602034028940450000000101610415216403005a02c0400c4060a5140c90301c107984001d0510302c500160406401c6d082c0b0704900036403050000c00782e902d2002a002034002003117403c0d00f9503c02d100412928000400d001e00710703054090b01d80d81c50300e804004079503d02c00c00e0480c1e0150360810020090740302c90640c4c2c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 578148803 1250 578147553 578147593
    0x114031006032d0c1106040c060e0f090405030409270b040303020714070905091f02070819080f0105040e0a0f0327031b120f0f08030103080904110a02 66
    0x4540902a8811041d068150032103080d052042c241030003c110045405002000c1c200329031204e211580041083c81f002502c0070038030104640c414185040a03100c80c0c07000030880d800c0e00d03500c2a00310440700c040104010010008205990184400304000202e0702d0200310480c00000d9840307403100300d400c03444c00460b00c60154140e0062003813902600e088141c0d52101400717603680c6003000c8240d0109800348030203c0c1c0d070300504ad0308c0349141e0024901540101b991104040c611f00981c0605a4001807072000c0c00705013000c441344128180450701c2ca131048041d00030481e11044804401d01b00d0800004681854107001720203024801c032000706a100910780b20040c40b50310808045041c40030000041151030b600b840c150380000522144040f4032072540c1800e03020320841d004928100650060113100014602c80c007005095001302c2480e00d00d00e458980720514240082c005085604044000010042c419000b052085815a070520510121850451080c0034010044001d600111a019080d0240e01a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 578150053 1250 578148803 578148821
    0x1e0709020706021e03070806120d0806060c030f040306060b03040209060415080616020106051207030b04060216080703030f050103020a1205030706051f15081b0702120c011403100603 80
    0x120041c901040c207210f800d000882e4601c2c1204143d0007004200955030003940d01603001d5419627402c0070504030640015241c01600304010284600400400e1840c0c807802c0c00e803800300f200d000c21660b4503440b0003292521038101c1d04c000c8450038200080425540000380a49004940c050505d4210386c40e41f00400c4042d00d2000000d08204810440004005038100150f40c0141000d01e510b884985071004020b096034941e400c880e0048001072410301c2c60307420001d03e0504890b0800e085c841341352600d240c4000a03110310a4000c41c00c0740c5a010782000d00080000a181180c8a524204940309103074480e841502c00910000e9441712808030100024400c04881d40300d224031a90039079190000c1950f03200101d071000d035003850b80501070400f1010002c09180c0c0c60809402001903443c00240c0d5500c0044c0308450040081c5800e0310507005441000750000181c0302a154003c1030000c034880135001081d940c0c885440007500007030980c62035481c046036100840c0e008601d554541d4400320b06003a000d07400f412000d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 578151303 1250 578150053 578150063
    0x60718050f0d020a0f1a070c0e1905090d09080c0f060a03060506030a05090c060f0d200a0807021009030c0209061912030206010b0f03130c05130501081e07090207 71
    0x1542c4140165161306062001c1c004e03650500c0109410318141c4020060300d400303519100c0b00d08100b1000402c0328070420004544c00c24462103180ea4900044611030b103a11071a1607029401c106c180034070348a010075441c0d4485000d81d1000394150340d4072082503499841e85082500030b08024000071103800c0400040c1a40c11840c100880d0b01a5203201243e5160700884280542c039075a5418800080b80600c5045012a0100c4009042013441a4201c001c1d22034048a20801507070f460420303a01802103903854101301000380300680c5580031501d01030020b040488110005001e000c41d414041000ea11803000101c0c1c1681e1440c8840380306900340700c41d81c0d6024219a5000c015020029001c918900480d409400f1417507007204c1a00c01c0f40b0700a4507200c410b810611440c8824130040c8110145402600d910182d10b0203c5401140d05003061000c4d0600d5811035038000100c402110405030440d04a18100c07003038442120b20904111081410581c3c2c40c02c9800140c2d0080070040081c00f403c1d80240030481d004d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 578152553 1250 578151303 578151319
    0x308120601080f0f10080d020c0a15020d030b0f04051e011e0902030c090a030c0f2102062d041706011a36090a0905030a050703050c06010e09060718050f 67
    0x15001052820a0010425006030300c940000302c0281000310020b4010404130542f015036501000d0080d40340d04807210b0f490201651000c0c111080da0761203c06195a500240007001142401001d0241d138010148170502c1900030b0000008030fa811850580030002050440481e815080c502204060752000d0040c550218003072002010550f1341070760310f1008500c00d00d11000440d10b4040700c05441511a4411105a1a800035121080c8440c0d100d00079110342c11201560303941d184484410040280f18a039095100c44103807200301e1035001d10010070a5404d01c80c1200440340c0c0e800720300380d9106024001c410403441c020391540c590091806c00340c0707481c1c0160300c585403c44900d044210803000c0c2e400b414044034180001801801d0402c3c0100780d4110014003401d0241d0051034403055601d11621281004008002405906151107403080d602c40c2c0c0c4c01c0d80c00b40c0d1240c0d40d5911186142c80d1084d1074014031400382d0404101c4503400345100c010510201d1011142d0700d4600340400c0340c104040d102c415001191 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 578153803 1250 578152553 578152559
    0x30f070c05040c080711030408030f0706021201030b0a14091b0109081002120f040201020c0f040212090a0b01051206150d0506040b0a05060312040e0408040305070308120601080f0f10 80
    0x40c3d0140381201d403400e81e1420840e107003a00d40105130080021003481942c00402091000c50740c080300f12880f0341c0718168000e98526080ca0414001d203e4000e4244020035030900200400080d054981d0003141d070b2500a100100114445602813a41603d03082220781c0114460780280c1d03c1c4504402d40014141003402d52103a550007818181403011201c1c640455000130400349403c4003000e100e4020050200d605014070340780e40080c0d034451030b20000502c034410701c2d1401030a40d91550115400342e0521041080c07030f0308000744c00680d43e00d41d060007201c032089400008101802c1c4200e91081e00c00119004040940b5900804c1e008805e002c80e00c56081070341d40001d840801c804105150085101e0b03c5200c1d01481c0a8000700c00700c810242c0014860342258001c000c40c0b081c03100c1681c0c1511484030a4400e60f454500d1710421622959100a00c20f0203251000014803d984000d403101340401d101c50074044d6200c00c0110b8410000b210050101012540810383c5945c80c02c076820b03404924040c1406140d52 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 578155053 1250 578153803 578153809
    0x120c030b04050307050d08010513090606090603030905040e031611240a09140a0b1c15030b0c030105091503010b1e0307080109030807050c0c0d0303020d0b12030f070c05 74
    0x4086400b961198000140304040050400a9901c20340d41440d00e820954100b600140340e101c04800008035443c1c442c41f198040c0900d580c00100188400765003002400c5da20320b03024140c0c4c105031007071030720a628011017a040c4903004401c40d020f035001c030f0b2038031400110165914441c103070354203100310781080680951342d1100003207051350340362800fa0600c0d00761078845110b030091080d0760680002b10300d1810001406040d4032002c5c010030585142c08580c0ea150302c420000361050360b100303007400106d1604241c1ea03081c040d024220303804103a038041d001a4410b59280980002588000e2044079003200c00b0000041038802c20620b090700540005002154400300b410010b4428103d9030300760343c103103c80340700140c1c054581002008001c001c49002446503903410384020345051001032211041c85400507140c95403a0080c0301420440c00020100041800c2074180200250096a00d4221540c6407914641d0310b40340ca2910102819030510046107042c0c02010110a143c10803001141d12825004010034699 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 578156303 1250 578155053 578155073
    0x50d0f060e01060b1801230a020c0a060306030c140d060209030a061b0e011b06110415030204172a010c08071514040317070903050f1c021501120c03 65
    0x4813164000c55225194080c80400003051050030a0600141001d682c840003070b050200d80d800c192400e2810f4031224451001e03030138101c0402c0d07100d9008103854008103145805500120580e030080010350358442e143c00314418040d200700202a4440014030302c020020f803440e0010a16141c02406403040e072070301b90351540180c41c01c0070644100e213100710003a510626800003428485410910300001014004030000c07030078400314100580300a45541e140c5041482d01c03412203004210700c5030840c94031089c900e0010300035002030084800150003180c10303012907640000e0850480c400c100f040c00d0300c0b0801410a44500d80002c080b941030000c100110008148048040d080090160045554000e89840301c03034120b0348200e0b000501c10403140180000f0940c0b20381344501c41900ba20880740300e51100c0c4419030340c0b548198002041441404048900c0c090041151030507446901c00c84101091846e0090b615901d044c115100300064030401005414000e036000c2240a01071304510354800c3e200d0301c40b40440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 578157553 1250 578156303 578156309
    0x905040302010c030507020c062502090406270312151d060a060302250501020d0501140a0f0b0f090402040503030a0906120c08011715070c050f0601050d0f060e0106 72
    0x1d40d640e01028058181c02d80500e0358410414805400003e0b40400083c546005180c1d100040780040c0b103080600b03401c044e05031080c103600103291103090310301407074030710050806e440c0b807020365005080d0450240c008844071401030b546d240c0c03191509490011050f400810300500400103090103d100011080410b10100d40100c43c028501020703480c0541c1440003494666203d00c040510400100c0507401c10441a8043c43c03441030f9811004178403a081490280c09200c0b03d8203c0640780c5000000c8110b0700001544100c072040c0c0d40c108840781d444c2000c0b450040503110701c000c4074004000380602001c07000d0041c06c01c500001e100508141d2034038082461030300611b0b150300c0401c85685080c4409900440f500c01c0a0360910014031044802c00402040b155041c40381002c0103001c4241088a40c0d000c0c03001104002030500385032124030300300b0350081032011101c03000d440d24021601c405080540201d0007030305981d000340050341c07920141e982d0180034001e20b40003a81c40b55a6401140d210300b000b03001e00401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 578158803 1250 578157553 578157557
    0x120a150f08250f0501050a0e090a020705010c0e010206010512070308040b0405120f0c0f010507051b011805030606010c0807120903120320090a090603150e0a03210609050403 76
    0x14050780c50b003030021050340c1000e9040304400d0a04040041079048000305003554406e107002600c2e4000000b09071404000135405aa02800031070800203900d80d25400b4100f40d0340614000e02081c1482c01d42640c0d0f00d9a45003909006800120042c4a581011b10461202030b0100c1d0803074900c25a00c1e141c006890f0000c3d0820311850f000000c080180b80b501e07085042c01015050003824014141001d880d903150041c690b401c1c0580c95245100c54240e000d00241d03001590464142d40800d1041ca0001d01441d080340301e6140030902c0c20030303c19204100700c28100241c5501070b0052503035448942c010348000040480440b46903400700b050301d0000c0d030300a0300f07a00002d12507103424054506519008501101858000c0105803808230307600341080c1145e40d0000c405d5210b074006642d4400010104a6040198201c2e07040d20303050050002c200071801044100c00640c1c10010000d1600310b20503292101c80423000034001550b40c518103946400100100c1000d001d0300000020302c45c1d07981000074140d800803102900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 578160053 1250 578158803 578158813
    0x310030201020120180607051b1e06030a110f0d14071403151c0f06050f060a0e070203160b090615031207142a06120a150f08 55
    0x821035809002c0c3e0400041610700c52038600c050031020340c05a0007041e40550000b85283c0e2404043d40b03400c403c680109402c142902c0300e24969400f40b90701503500f00301842c002d8042800d00c0c0103980704000520700c03902004000c9840c1d62101a0003002400d440807000030b44032401c00075003950401407030040a01e00a003803008541140900030103148250024041000e1210728140800c3c510780701310440c1e41c0900100d05c040036140b0044080396205d80030005070000303400805126814059409460b1032100e10910040c002a030728040c409a003510241c81d01c50704101e02401c2440a04803503c500d591041039441140c1c10610302c40121680039030410310507591072202d1014042e83c220240320107540200d002e17020890050b121030219039111080d401483c9400e0011031480100b290324881d001100382c0d81002c5410a040281114103c0f0040b403002d28a00384450000c4651810120f00b0b59a0744040820107000582d03400398290040e100b150550b452074103540300701095000042036028094a142c600820f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 578161303 1250 578160053 578160059
    0x120108070e060108060108091e0f07080102131503090f031d0a060807052a16091a060c100905010b1008090307030311130b1309090b0402090c0408030310 67
    0x181804500d8100a0711075180c60100a05030740c200460940202080c42c01c81c10b29a10400c000c1d0400380b0a0741182c9804030000040c040203000080c006100d00003940c1580c3c961940c2d619000d00301d200d01103e80b0540d000682c41000b01c3c41c030200c086850a00103080101e10039021384c0d00c24810051142d400c9020880444604001000c1c50b4202c0d01401402d581400700349051220242103100018403c508100001400700111010401032015464419000740b50701e0103a600d015460b240d0016503c50511011540050701142c24060228080c0c1064080035191100e01e040c0002540105401846846165030810342e00312180705554485005000015440088108020300c010a81219404100114061246c000d0011003208c3c640c907454240000c142c03e503218280b07018002c40000d0764500001110000e01d1000400040c841080c2c41d484070f6003416210340d076000171540c80c0d0501510350b00d210303000035005007000743c0c401d07401083d4200d0040c18140e0396031016245510407590900d0f0039a003178030b0030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 578162553 1250 578161303 578161319
    0xa03060203190f150e0402130f020c0f0c1203030705030c03071e02011a0f030601170c0a030317070f0804060c2304050f04110f09040615020313090c2c061201 69
    0x45800f400720000316808509190f00025601108da001260511765103030303044c5031400c0c0c450381140c0c068600001980c4200b05103c1081d80c5030440200303c0d0380602c1aa14005402d40004000c0300d00c01c40103602d0f40c6d400c0d51956542841d090300010b04d00014043d00c4c2001c06250a080c0b05001c85105160b0b0002c1642c05241800c00d00720303403d1141c2076009042480e2242d46541d0046041c2c1d043d140c0d501000c0c0302c2382e0107407030107945081c04041f5400d411034a101c1020060651101c45900c185210036290001a00c0c0d01038200c4201d4034801100c4005002400031600203103031703a042151608014602800ca001c0040d00c08802514a15902d00b00b841d0005010480750a14a14901d4118800c640802052101c006460000d10418148649100000800814560351039111348003a181880c4090990614900b01950700d9104c0100c082900540a5001480702d0013402100c04c00c210980e600341010483c500b0f07a08203060080c11070020a060b00310702521a0712607034050038070b503d09001e441100c1d51601c43c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 578163803 1250 578162553 578162591
    0x1002030a1b110307031d180f060910030f020310020309160801020a091e0f030f02040e0105190903030b030102072303040b07080304060e0111130609050a03060203190f 73
    0x30308070a00c00001c102e0b400d01c0c02c0220585090a400d800d1004402c2e914900c00c2e8403c10003207244640c40100c00e269244002c0c003240e4002e2141c40701800c081482e03102d0314204203081c4c800701c0d00c0019030400b204082c0005003101020803850f0388017404591704c006c01c03211400243d030421141203100d43d015540244002c4007aaa5410083c202000214500882d01c00000c0c5141e00500072650210281d0401d49880c200e040b0a040051103100c008444040c2c407031401c820690b01d285820392080d4100078440c0d095000611030180036050b4082d40204500646070300801814211005500f415a03c1c19055096242030005120482c480c591038120010941c000b03071840318034610400400d900500080c85900300ca402111110794008110039100d03a180d10740b040150454851100c080e500340700c01d0000f03152000d006004081c0031076981d072502c83d8503070908413034840c001c0c420703154030200720b400400c00b050481e801103401004201800e0030304100101e02005803010159061302283c2e0311000040074070001c0c15 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 578165053 1250 578163803 578163851
    0x1090c030506060a09021201090522120311091e03010f0614121203270d030b100302070302151302060f19030204120201030e0c0d1a010b0304020a171002030a 69
    0x2c5c11814000507100c0e8121040050086040c4c6580d10383c08224000e8481410b943d03c0510701e1611288460b040c030740089048290341841022070304140b98808284d4158060720250400605100010b01070050782220040c9112001505950381d007208078841901401840c0c01b4101e41d03049158000540300c240f04103d8004003440d0308a800181171510382e280f8420840340c01c903d48041d9500c2d0b224524590f080c0801e01103003808d010388501c0040d180a541c1580002072422422603002c3c0e80c55091580130b8050b48660400140180c020040481d00c1c00da9030500b1a070054069001403007440225400708080e98480050044501c101241c0c3c4108582004040900c80c21149015814503180142c441071003a2103100013414582c4808016010b82c0041104120114009112080142050500c01c004141810600301c611215000100d040c0000904403801a5405001011018a01000324032003800105140c0420f00400b540034070302c0100b03800070b0b50265400c8980092401e110b14507803091303110408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 578166303 1250 578165053 578165069
    0x30405060c09031c031104080c01091514030c042d050109061704050f010501090b1914130209100504052404060e010903050304080d17041101030b0301090c030506060a 73
    0x400a040c5480104610074001d60a950700307440d80004c46029001340108041c00c10740218003140028017010005000e01c0801420b80b03400e0152900c0b00c0c5441aa044210690000f142050314001355904542c0c001310b5001201c0f2151500b090340701c201e42c0035001c4007903103607208005403c4160803a900715009540003c09090a01441907072410101030411a06051400a1420b1010005061040c1400318121096180000304525a15041507a00a18180900c40d016092002400a491503a11080e000703440d491140300540da584002040300c6a034440050007045502804804901d4a60021400c120a03240e00c1e001d44850412003030194590140b0300480b681882005282902c12480c0c04403416540d00c1c0c50050100c00c1c80c40f0050f1250f143c164002082032100140c0014020004a03000107044507070b503030304200f0309501da00c1000c000c441a80c0c00351001103004a00c0c8282d41c025403090180903030190000c01c03010215152107101d4031003a40255000e4008101304551494044500d0014060304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 578167553 1250 578166303 578166307
    0x4031101050103050a0305070501021207021c0e060405190305150a0c080f04030302130302120d11030f34060501060306080111071e05030a0302040e0106090b1801180803030405060c 79
    0x364451990711725848501a06100f4001143c405005080d0100c4e02c800482d80c00c1c5420f6400c3c00c210003551040301c5041242d41a510f440c0e600c1715680702d80c01060804034000c020300e06044c1000100010780c0c00e40704884942042901c6e0020000c0e0060020038071400311191390164070302d0990540025542c040d48110200324140c0c041000b4032441c8400c040e00641c040c90f00603200c1e400d103808035490300520b4201940c4020b402a01c21940c0c04001501801030190782d0340e203d98100282413035a901e0041c0c0c01c042140300c4041c084003d201c200724070711b54011544d41c480d201090044100904003500c42020a0341d00a4a850042c04a682c050203214024031501000300607070280041203040500500000070000866a03d001840300c101d01c02c01100a60441c05503a41d8a0094501400950007032040d440c00624180000480c24080d11400049407003001215241000740a607005002c04070b40d00d0241802141c055900400070407602c5040a401000d004540d00e081c10700784985803110003401e6000c0c500003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 578168803 1250 578167553 578167559
    0x60801030f030c14071e050109050a060507110405010311120d052703030316030c02070605120a09080c0102040504112107030b032a01030e21160605040311010501 71
    0x80715003500d50498143c50400100e034098500443d440100f40c00020701c61080d1140440c6214000d10a803400340758404448041503039032070054810034050306c99107034003480050003002039601440041141a2080040d60030340580f000c001000c44400f07800c05d5517001c5100c0503110341410512012501d0725103400040c014040c0140000b011032281d100b01c000c607600d1500601407000c010311986583e10f076000341502d840b80b506901004940d8101c034060400a4240740440e40c441c0d0000c2200c500303890782d540c0c4840c580f040c800b040004c2c0520240c00f02000a6542550801040310780002d0480004031600142e5920710f0038003000183e07210241c203002c4a220130000c290701140314170a2200e0305014164000070594421405400500e00740312481d40500401c11041c02540315454600c01852f485000d20080f10600c00044085401d00200c40d241035120381c0d820504a84031480c0710080518404d6840d00e4800d13240c0403182249880e03501100c040d61a2070a00040607080f4a11130151202e400081120790302d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 578170053 1250 578168803 578168813
    0xf051e0d1107090b0112020f03040b0705040305060411030f070603020c07080115050d0c0b041d0a021822110d110c030706090c09050f0103020906010e09010b090103090519030906080103 81
    0x1083c82041d40c1140c0d2018900d600d64001c01405103426100d04c03045440720102c84c1c0710b204c03c3c1c0c400c8408035020030202000558140c010f0303003070340c0c1a20b40043c01403e1071340e1113646080c4200c1d01a00e0590f8503100301602d085504034104403600103407019690258548003100c40d09032030040c940c1c00495031641414424900d102800203c18211501215541c00c04185428007441801c0160041070480c040000d000c40d001c017a80000035654603445120b0042039440c02281e00c101d001c2c0703a5411030103402000c0300d01c0c440d1800c540ea1103d500210703003030100600310711142c0c0811a400d81050a05008000c01c04281d81a681d03c255040041601c408616000620240303a8980c49070340340c01880aa035400a25090007565440a00a0003201d2400c00ca181806520603801c0308092100320b21800314400052259403245508000c0300c10301030302c007244590800c0320b10301c20ba03001000c2403070405030b417000000e010610401220041004e80b00aa1100075081c0c10018040c41240d0400310502c0302000042000030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 578171303 1250 578170053 578170063
    0xc110d09060c170c0f0d120501032406091e06060504050303030f07051c0b030c06160204020c010f0203041406060a18150b0408070e01050d020307050603040f051e0d11 73
    0x740d01681030141200f08030644026406040071030112803088001031800c00100140da1891040d55407901000d00b510601c0100640f1424000100b4181080d071900405203000c40d0800001c030b0862074003140742610768202e441180c148614015907840b52620010b080c0a5500c1407002802a40c50500d181500717101c04a5a24800a004024101c66110029075124828405e441100342105200701416031414645809441c0c2400460301c80d01a0440c080d4480c50f0100c125440c5040468001d900e00d25183c081000030740100310001219526044085518185d510042d4484c51049003028500c42e00b003040b0b18130740f201c01408180030b001540c3c0c0901000500c1d40040ca4105070340100468142c81500c2c102c9940d0034242d000348228007001c18049280e1801240c0703002580c1c031501907819140c0e6140c007003121003245000083d40580040b5018009824280b004681c018000e02030061016429500c0e1483c26803641e0946e000c20495080d0744010810922403940c40204514041002d0301701071003070540328 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 578172553 1250 578171303 578171327
    0x8160b070905120a0503121003050a060c020c1009090b0301090b0a09170304080304020405130c0303081801020f09300a060c0329011815030c08010605041a040302040c110d0906 77
    0x40d0081f42c0000e00e22840040b21100a594014140c510314416031074150701400e81d0940c5903025000700312002c6018240308100d04551402951800c161904e020400b000408000c4c42142e059502c2e00c00b43c10106400d955039130701501d01c4500000318038045091075249202e1002e50501c21380c800b0800d204c0030540000541c0e0304990101c9000805440b47e40c007401801507055001004072451480000501d070300308030360600c9001141c80708150300724056015800c07807085400d0040c5140c0148003041c01c3c1d0500039815642000c58100c0c040360107110100c81882244d45148401c480d0f4003000002d4100081400740407130800ca00d007000c2c050801e4080b424034103101e9000054542d070105010303403c11a0f00c610a4040200340403124070340c9080d1143e82821104594403400360129060412f000d13022441007103024122400c40e56000d0400341855601015000010343d420b401c100103000c04805079940b4030800200383c0080d1503440c006100074042a04210440c0380715410301c0300d1101c04101c0175401042d58841e03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 578173803 1250 578172553 578172577
    0x80c03071403101509090e0a023015060102010c080f04030c06020f0a02010b180417070809061204020405010902041412070909080d240308160b070905120a0503 70
    0x483d900c00b0100d0440f148507500080c092401400c01d0700310603800c00300480a851030982d0034401004244046036482018840007900724030418044000c04506081d20501e000400152381c000510708070b022840c16551445144564440c403003406915a0240b2501c039009055042400052410420a80d521480140003909000d805800c00f420031204c2d070704681e261280300114607118596010028024203503540f0b55801107610b031241ca0341003000031601c0351041d44e010544a40c1078400c95100c070126000000201d80591090008003801d40c1d03440302130034100030907600c12000e030300d0b0078010401510b6042c1e010807403941c41041300307011001008142e481a1a800d446100412016038082c40c901552644000381e19072804514904000c221802000d15581e40d550600c2050721f042e29014140b0700e4116142000304040504000041c81030700038092414041840c41e111101d0381d1184e0141990031554a00010074015052080c2e203008050354002c0500c0c1c50092046201c3c9994256482c0321381c07658101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 578175053 1250 578173803 578173807
    0x705041503062105190809010c031809020a0e10080a09020f04020c011e1a120f0d020717010501050607020f1906020102120f070207030308071815080c030714 69
    0x400d54000d40220000340319220355044008118248242424405402100c850082076000a10708071920b103406156a044068a0715024a0700010354016000b034804400780280c0c011060103800005080c103004101000005d0303501e131040240141440d644201240c410050000704580050740801d64a03030203801e03800e0000300e900440c00080c024208141010364010b00028440320385800641011400c04480c0f80d21600d0610b00300041d0042e01c224403d00700b00c80004000221076032405024900c1e40c01c0c1050295580000150002401c10102c0040c03070025901c100b108012692509644c0c040d44180b90300200465418040000c04034030407100083d10036040200f240d0125603c045101907900c0011600850807551840c4c0607010350844049036200510b440c1c00a003400f00031040301c611a0b144d0380c1c05880c90380d00355601641c05080140140341041458110562030780700751803154001d000c01d16803003610280784440041000c0e400800c000741481040c0305008907107400c02101d44904641000d000d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 578176303 1250 578175053 578175089
    0x206011703130305150606040803030a18050a05070303120e150603010b030d0309110a03050a0201030f021b030909091203040f030e130e010c02030405130203060f0910080c0108070504 80
    0x5495400b60b10720030040303501c02103030000c00c0250001e05220700350081e201811180d50341c4000c201c40d6008074400c507074143c0c00c02c10001d021300f0026880180c01c01008108074100b1405030300c0d421300e03190031150b0407140741d40300c2101401410780102e80b48402a03d41002402000c0d28049500e890301210769040424400d43c0300800c07a10380d001e4001503498030020b021249041d508603401030141441b020182d8a1103c081121115801e082540000b40c035042070050404941c0c0340e004400030000d8038524006140d09015280445440202c16a80005110002c6441b0300c0d0900400c10650809031032000a039000c0401004a200d1b54000e4aa0040d08065134603a10030300c0b4281590b40148400031250f00041401040c071b02510f50758001d20151280300020011000c04020031381e43d81c40b80d0301490f41d124041103440420360712990001e5600840141800b01c5114081003c0390100200761a108200704059400b030010030001c02550701240001d01e02840c0034184003101504030f120702e000e01c05034140104250 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 578177553 1250 578176303 578176349
    0x6030c031e07150801090509120f0703030b03030a030207060e0106050a0509040c08060c0307030b010c02011b050a020405040b072c01110c03301806031003060905031206010c03020601 80
    0x4030041096820f07501008106000c010321804003402812103184c80d01e0003003050724000140181c5401900349890f0721f4850b55445d0090503401c266001c0b001c041e1580300720038a0781c805001a115049103601c0150703d235800f40c03404405440e0084200076150b85841c400b080356641d0303101d8900881c1e40591301007120741c55a09103961f1002064021480358410702041c45a400c407894015071051420359001c00200742480c004690802c11401e004e8005030f00c1000d6a030301843c2e81c1c1008148036210720204c0784040b030b40794080781c01d6603411138082c1c60100c044001c0100c00c94212015600c90740104a0300144210b1807806218200c00002460f410803c40225141c03111030200300d651050b076002012580c10f1040081c024a80c038000340d1003140360340158000c8900c1043c07070b001a43e90101d095003e1160544500050100c1d0317400080140944030a03100c4000040b4855210342c02e15203000d400510b540c1e03581c4080751080058050300e01410440c01b1300240c40400c0e4007149080c1902c503d842d9640025540c6045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 578178803 1250 578177553 578177563
    0x209060907110f0a170a1413030b1302090c04080d0806010504030501050f010f0603020f07080901210204090b0a03030e0f1215180303130813090e1506030c031e 70
    0x4842140d110307403a00400740b0f150000388401c02d1482079404448903441801c0f0509036000d84200310011500d40d90480d038882c0e17a2200540988959200b8003640f036680c0fa2640030b0307142015158401481004200744055041006d40c490b80051541c4000d40750902d1701207a00e42c0c03a4a220007000c06c001c1a00f0202c6c10b0380e88a44120f40003160000001e01290078401d02d02d02000d2800c0c82001600d03052140c0010b4041d002e4000c1e80c101c0c0e01842015410314406407100c504039071103004614104441006100c40c04248a211500d03018000c0c00d0040e296401c1004080443c1c078000d40c1c0d0380c81034a007001b042001a0340301059465946060b1200420f40700e051022031441542885000514041c0c420340104042c0c03903038821445551103a6070406910510314503180c9a03c070548154081d190703185145c00200304000020980992044004000156900321500859003245001d8016800a24218610703010303004206030802400c070007801d54922140d0001e99039030a0464440c228600c41080c1e200484400e001d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 578180053 1250 578178803 578178827
    0x8011509030f05030307020c03010509190c090c091701090b07031e020d0b090a05070c1704080a080910030b0618040b040203070314090d0815040b12030a090e040209060907 75
    0x1002c1107001d0014941a0340b20780040798440014400c0e4441040706103414002c0c1d9005802200c042c0690b0543c603424803011005665040d00c1c803040c448070008807940c0c944501100c1c440144d444049090401500341e161003c01850b9000d56130503c0b01050200d074020708a283c0000180c01d00007445400005124032200c43c1c40c1200c3d404910100d0382540c001003641103d080384101f169981e650f070f9a01c1001d50110f40b415038000c40000d200c0020600010000000300d03806102000689045c10303a1680e0641c0b03002d028642c02c40d131300c0c5400700315107030340b81002d4642c148078074150304040c0804505080400c40c3d900400a421110b8002c2c1040321202d46c503540d014402040300580159a07900d4040005800fa001a03d050303958a8841400509000e00204000f01030034120741c0c542c6050744455204580f103081c1c4400440c2c1c02562181404200d80da2440a6410740c80360b0005140c5907094054041d020501c0d56110003040b1088504100040c0e40e0070420950101048502c285942c41d149000c60348400816 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 578181303 1250 578180053 578180063
    0x190804021801090f0e06010e040602070519050d09091b0e011209060911010f0509040b010311070606030c080d020703060f020913060515160605060f030a0812060d030801150903 77
    0xd00105200c1070580003c980384c41040402d0144240340c03425150381c0ca00c00d206140071250408041000941950001c1014501900031a411911003515203c502803d1050445072948880c1e540b0760480d4010307e022008040084080100d01040310307504c255082c90036042c0080280c024001c00040c0c1c040d40d214240d08110070010400a0540d02d0440003c201041d4283d8011f40e00c800d244006620034250010051070175510142845800818080503000d01c2460b9414507440d030080105084422014292690040c8030214010781b85040100c0004282d4105507400e0700040107250800303400007802401c0340d901c114001340c5030008940c10030007402814030310342d030042c4011440411203441b034201400fa9482160140380000b1003908604451040024003440c081c04a507013000401c0c610741c040c95006a0180c00181301489080000c0d05056081d4005c482c22040411741c044d21a40c140d607002d03407041058410b5880342c81c0340c0e10050086801481032212042244003130420243c42001e600004681c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 578182553 1250 578181303 578181349
    0x6072003120907050a080729121e061503100906061706060715050601030b06030a021b0304050a1a091c110406180b01020111070606031202010219080402 67
    0x11806220320740340c240e500b00c0052180b000041400d1803c1d080c8001102c0480c001407107074914200944050a64100840c0c1084641c1c0700809032000e641802040207440195002c00189040c001440d2101d030021400070030702c0c1c00d600c20020607848440340c80700003101d4500b5076600e99440c60b1001c900d00500c1e4004095450a20700c0015180d500f100d02941c243d081e0070f44140959488209002590088000c007a20000c842401500c80d0f038000c0d808250019010300d03002ca0f1403080c14021504a600543d01003120030341c00034210018810701c500f98034415601700061840c003454800000ea504800d400f82100d0544075080c004084c80740c0e5001c40768404800f0740442051180b00315507005010a40c0d00036144910554142c1c2c0c8940f1b40ba108100035141001e4001c0c00c1d42d001d00c803006004080c0b4140f100d055641c0c40400185500c40080506646032203010302094190551801c803c0b0741a40903a01019a030040c400e80054800b082c00742e10220345c1c14600400380340e4445c00061000040c40b602c3c07079241c41c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 578183803 1250 578182553 578182567
    0x30f1506030607030c020c0d0503130e1801090b0c0c251401030e070923040b270d030b060403083702100902040204050a080d02010f0b0306072003 64
    0x2014100900ca41011016203035107a540403415000d40e8800746414005070840016036440c0e2a0110161001d00e00403c2200d040208203044440c4070700042c0c00001c044100a010801d01558a060f50880c0604a50082c0141e10b10b0780d403200c4800d46c001e0001c441301c10011420080351082080007854003290007494202e9582002c10038a02000103005401c6140000300314200a035019000381c40c03117440c410008151581ca0058403074028001c082e003051000002529155001c503200314694025800350300314020b203041c4502d10f0451045003082003240d821203810001d8007070601048010f112140c5042c0417520250380400500130344100d030001000002d000c242e2101048a95541d09048100b28030a440d4415180031142642019903210304016030001350182043c400c0c80c2c00010714284050300160406450300005054980342e17400045c031962258550a2440b0b509002d192840c03590220200155010040441d4440342c0044c90390060218000c1d0800030311030507062010f4580501429030351614a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 578185053 1250 578183803 578183833
    0x1e020315151f0f0306031a0712060b13060206190504030c0803040501050402010e062d0405060a1206060c020a0509062d150c0618030f03010e0a150f0501050702030f 72
    0x4020164003000844200180c1c40c0f00380244a4a07055940080806085170008401da0203503010003000034040041111041d118200036024400240ca0720f030303165030384441c5c0e000b0550230314094a070700c55011980280c050140c10000a0b90161245403c41d07804100c40e525400c00f61244c0030a035000800d242c030300104000c00d0000661006004034400d0340c030400c1d00e04090301040954000ca00926003c038405125008000c100034000300f0022a0213525507007425030390780000340c890b0410002e04020070038a000307a403c031543c58030428000d0042402d000801c03001580228060050318000c6501805001000c078201d95200b8481520502404072400c04908240c01d103040f1600c03011101a029039584907540c441c60f29408182d031480c501d40d40040074255202d643e40e003070032084005450ba680c00304105c0810407007540c030300450180004224038400c1c0d040c1851080304448801201c0ba6030164802e0081c4505846440b40c0401c03a442464065207410306400003d0900780074506101c81c034030030301d050754540b00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 578186303 1250 578185053 578185099
    0x105250311011b1b0507030507030305031b0703020a08031e240f090f04151b1e0c12030209030f0a29060d0305120a091e02031515 57
    0x100c1c01c00080c88410580c25144024000710800b032400300e0300803a055404c1c1d00902c1c0c2e2100b203160040341110300e41e650344d8913401d00f0200309401c2a03001440c00401c01000c04031058010100d46800c4c21101c0c68075041d078400a440d082c5441008118440000204211001038a1075000f0264408860141da040c121600d000c001c1d00e600541300d42038814a071515a5260111074002c0c1a080130f080d408066407401008110403000038401c4030603808200c141c0da0001e6451242d080c00c500075000c000600242c40c1409403039654040b280e41ca48804450304462429400342e00105499440b03c008101c40007018400d501030300450090316094401c9013018110b150b0006140340100e0302400c001800810908800c04a5514606010803075600703450200d60340c0d0605040d01d400b114020b2400c2c905101007451401c0e2010760545561144503101d40210091118182c01e000580903900030086900c44154046a00c4080f407400b610124003140c0002403100d004501d56020400009003028411019080c0054182c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 578187553 1250 578186303 578186327
    0x7032315030f071a0a0311070c1d0108100519090c03020f0a0e0c030405010902060406020105100602160603050a3c0624090305010c020c041a0a0501052503 68
    0x10b072040e55210003240401180b2541035a242a01da810078440740c3c1e41c0c0005036400401c43c08109942d4900f0922000210409440c01a1041408890035807030035149013a2241009110702e440f21354807004004d05200011004690003c00e00041900c2c3c3c2d030400101c99030b9a4130b520b01440c090400e50f200b81006982c03000a01600d108032404105110030350700b400b15a400c14041d008085000002044003180040c010b140d029200b40d0021519041e1a0f000c5280b582140d0310480160b0b44a1003400074643d414041c440c007500083c1b004250580b001d007180d0070103c0307042c8182000d060707441e000304903444241e0700b0000c1c0496005590503050941d1034408085543c0c5048400d0b49894082c51711040320350300e40189401c80d02c982d1a195071041562004080031000e10303000c8000e00071844030002c0000c03001e018944240000d50060048000d04209000c182c0b0451003085030284030800651005a1300c0c08101e1041d0398080c6801500d03454505440003117107a40ea03440c6124444012010030805034404c40341400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 578188803 1250 578187553 578187559
    0x16090f090903031107020d170405271302091506040306020c030c0d260c0910023a0807050c100506010e1906030b03070b030a0e0c0d0b07032315 63
    0x34041913000c00402c240143d0100035407200650803410081f858041c078000c400c20280080d03d140030b035107000085891000499070015841080d1045640101e41212030b940420000543e02c0501c54590008151440080404001b0303641590100010b0b143c6c3c1c000d603000742d6800342c0119a9400d103584803a40d640c00041002ea00792182c0000e0040c8240f1420b4000c10401d0300815200d5070701061143e0200c074002c0142961094501485040c10030780d111015140d03d20003640103080368031003030a09040b0f05144141c0610445442021105090404c500640ba01400902d00072141d501c0705502158140f10310713440c1107214402d4650f41c4c0601c4901d980481c3c01034030241c941d0000c0394030030002e02c0f101300051402e501c20ba84c0900c0c81008020b0094002c001d20403c011301f40da03012501d422240d20160006d464244403a079a0702514401014200400c482500d4211144101c40304944d607080c5400d1030040c5101c04040d21959884d0301408601c010381101c9080014201c45440d180300c01504149004042d42c0c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 578190053 1250 578188803 578188811
    0x130f050309090115090608070e060d0e0d0509060f0a1b0506220b1504020f04140a090b060a0c0f140c090a06081e0705061204110301110316090f09090303 67
    0x19510106500c00c1340040c00c58031081c072031a01d04102900ca002c001807001d82071101c0f0350140700d80d80c2c2d21000101100e5905801c00100e41c042500c103646403031350030701c0c00c070084c03141c00c03c0b20b1300c0d69030740b410141c84548140c440d18940d1402c0f800c8003207a8000d11444042008660720b83c2c403604001000c5151880762030f495040c400d1200b10300c40d400f020004682c0e00070380662840e401084e40c10030114214841008042e0001d45001704890224030382d0b0380305501030480f9034003c0423a0030b45494036000030303001405180c00910800320a18005101c0b4031030388900a0510a000985004020400c07440c101042c0d040f801d0700c90500e0313015080544600e07040250503c034108180c0040d402e12003c6c4218029143e04030010040207502c1c01a10b05105404801c2c50818807800c10001840e56403070700141005401031a8000007810546059240440010302985c07003070341050070f40994a018441501d0744449860b503c0154100601410303a0b100b4807507048088910001000881c6452403600070a500340c0c42550104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 578191303 1250 578190053 578190059
    0x5010e04110603070c030f140a020c090c1e130f030602070302010c0207081903020a05101d0304080604060207150509010510060306050a030311070f060903110102190b130f0503090901 80
    0x70140b00032611140860000004200441e1044030700120301c0443d8205841c1e64206000261030349e80085040ca00141e02040300341c002c504040030016046080c0322800c030700b002e03645240b01c8904041c030403504108000100b061202007040c401410000d041444441207015180d00341100a0b6102c034200350095070070016040080752002982e0b00c00c503280040649500c8001c40b14100346500d080c60154210710800002e10003061040c0200c05110078000e200103030722120a2516204000c48203151996034205001c10040d286020a0103580140d1001d0700507620440c40c580114079503686482000850b1900d0700700659207005511881c040e120043c180c1c1d411a030b5514044069514502585800000c1500c0c10000a801500c4401d004041c035400d803516292500a01100109964422400a19001010010305c20804600f5800d0102072014051202c050b41260000b01c0703048000801c09aa82c2d000248002003d00390380d104590b101443c0e10426001d42485a076a803c030a1810b40701d404824000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 578192553 1250 578191303 578191309
    0x10303080c1227030310080d1e0804031b030210050108010b03030702060a03060302030f03091305010b22081006090501211b030f140c0103062105010f05010e0411 71
    0x25400c40c0480040c6002e055482901650100065440c24051911a112403035880c500c1400514400c2400b0002404040e24200c1c0480c13030308a881c025101031081c1c0715241450340045006d24a05c1846038145074649480d42d107011101c020700308400d0300500c441414000d040660104d058543d110034410305012598884150b00e08a4003c200c805605a008110784801401c00c10f0150044a02900300062007075a29004070b41000c480740c180b82d0b41034000003680c4e10700345413003e0340400c1400391207400c10043d81040d1120659110700803404a0790888a1040d400b80c0b0307884a41d11015100030707420348140c030340c0950f080b601418403805144040d40c146000441c02d04108c50a05202c0131542c0c2d107240300c524060301c94204400074001000c00391150900040b001c262101a650490f602c42c1800a80d00701c10510107904003603640380300781d0400d070074028204450324151094618105288a04074580a0240761403801044140c3c0c119503146d0070840002604041481a170b44200d004910554036000c2c0d002c20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 578193803 1250 578192553 578192557
    0xc0518030d0518060d060f08160303080c0732070803130302010c1403070b06090f102601050412090605090a300809030c0d080f131805010303080c 64
    0x5440019400d00c444400051044400c42c81003d015110300d1811400a00d0744065601e0b41d00015240e00506200304007281c01001480d68141c01a6024007c5506607175000b402883c0140280c7e010000200d0640f050113800350310740c030001d221152614480002d801150391036000a40c01c4003081e0080010000708a070021044400700e00c0e40c1c030402c2d00e40d2411a8015549240005815603000b80f1384a8090401c150400007014403a0081c030740c00080c1c0c0b41000411820500041080c03007940010018040c07040e00100a12060300c90900d9030b0303201c40811044c1e440384560304105062484d070a0505220500ca45002441a40b81c000e90740c0401c40d6071141c0d01070700c00d4030850007001c0d00020140b200300094042d03120180728051000d0406034414945680c03a950401e01c401080c2c0b8a240300089034445880e0802c40c1e9072903140c050b64503944004543d26046114000c5100c076a00c06500002e112010100441a81d40a8600d6410482c0700c618a2000c02c8010107090004502180403000840c4101c203282d02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 578195053 1250 578193803 578193823
    0x20c0f0706030c1b152004030807230a03360609150801030f02010909020d050a0b04090f14070e01080f060a0905030d0f0605060c0309030106090209030d030509100c051803 75
    0x1e818103c010600b00f0b103900400644942141d00c1650f4403a100d0190b1b000c0e0024801103008250340c6888500130f0508400b1a5004407955040c1c00300c0c24000803500c0800f20301c0742c00c03da40508000c41c810360310072a404003c450300b0641c8010864800030050000030aa0000720554180d5030310030021a807644104001d8a0301d400c2d0002c0030415038001040001c0380911010411072041c0f60401107542e031542c01c11300b82e800c0a440e0b00c4595031601c0c10800c3d03000c801e21400c0269801214180034000c46621a600c80010060f0003401c1c0c44803540c024000000700300b09000050140400f420029a0b4517240d841c1c40350301084110450303010b604041508182c15001e07449031585c00030055032420f20276541030002019181594540d2603180c00d400030b04d030b81e01c0c000503001100454002e1170b520303171030142014210b070794540003003d95520503c07800c1c00f1500d0000c3d1120f01059927007000520764680156203460b06c072010b00031790b0f40581030034444603066600a001e1b203802c2c056001c2ea00d00d90006003040544498200b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 578196303 1250 578195053 578195063
    0x4061215050708130218190c090513020705011b02060f092b0e03030a030c02010e01050c0f0d2a0f080903180a051c051207080d020c0f0706030c1b 64
    0x10010450036130581c150342c56050b1008181c1c422005000000b01049041155030504e02c100040030110080441d00074110360080314601290f07040e0600c400560103d0b1200c1000c50020390105116003081025402050042c0829202423500a281d0200030341e01c40080729030052605458002c83d102c60000100f9012207042c40d100315465a0741503442c0040d17444403041280811096a200d40d0050324140010910610a0b0740e004c0740c4840350560103401e4564410210780242e00d40000c00458080f107800b5104007440c4194443d40e030b40000c50001c80902500780304600c088074980e008030b13410708a2002140d03e0f6103d64441d1900e1004110003600e18500403100244281c1081050800c01d580f03402c1265540030000b00710500c2c940d2258089400c0c64994035034000f4a18861040d8424030404000104206030f18820b11454600d46075990002401000100d0480ba82c0220b9510b02c0b8400a000400710f040360141291030007595110014007034006d0480c0c91010a0201c00c0e541c41e944048101088199081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 578197553 1250 578196303 578196317
    0x7060b01120b1e13060807081506091b0f040603140f040b070807020f15091603030906080402131a010f0f0e0d0c080a060c14181509040612150507 64
    0x4100c0ca4081286030303810307801075403411300c000075403560310030103000d000700f000140304441c10304500c10302e0700c82030040050f08140100304011081e9501da00550344070014201c00e000d03414001e4007100c03207030203000c640c2074200d803000c1004500141d1541c0820351b022550410000b01d61108109694452820b4a020b0440001c000001f040140104012030304810184115910700485e9074150703003040c940c0070400480c460b0701002c1c012848000c200701c4032140740390b0ba001c855852865038040d194128600c076038001e0102840008040d942c441d10b00c000b5401c03d43c4820700802d9515110a141c000d0582ca078980400c3d26080c800205602c03c40c95001c1d41100d544035807042080380003c0001034041604129400b80c101d005c0030504001c14045605001c0c402c80300032030b00b03040400c03020340302050180c01d40f10800000c3c00522066284002c0c90032000380159942200140403046045c00d40c070903954800c0e0041c0c2412000035130417003542c88c2d0721111400390852a03030004003031402c007003914001c1c0d4507040002c080c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 578198803 1250 578197553 578197579
    0x4061b0512060604050a090207060b010e0109030f060f0c020d0914010e04090503070f050a050601080a02280f06020c0a0506040e04120c1b060216080304060509060f07060b01120b 78
    0xe40c607031500014020982401c00d9070b1400015500300803500300000da02c3c5c02080540030410749026288082c0e8003420100b84e060b040d500004c0c02c0d40b429100c054440b0800c0461300050000580c4640c0455480c6001449044a0b071a4041e42c2c0d0440795042d40000341410000141c1c0c40f414502c0d807405100d050b500c0003000c070403000c10000079014003030f0b0036181030200b00300300340c0001c404d44072200a16200320040c040b82d81c140d050031810200164010340f0b071500542c2c09880143d0302c050300d03804030400645081c1d0122442a900140301a03043c0c2212800010300400402d0b066000202240312410480b00c02d1803046d00d0b0014814a8000c52160307588501072940030600148102d040d04640c9840c519051502036102d0f00e074864841000e1480c1e2140f084003450501095605110714178220b01c0c280d0001d081e06140103a81a601e11540c8124400c01c0f49c0861009110794404080710304500d09400007075103da04508086000340403001c0c0003804103611003801450455540030784988150001d100721030840d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 578200053 1250 578198803 578198827
    0x30a03090602040b0310080f01050105180403110708060a15051309170310030b0109020a0e09060f2805030a121d03010203161412130c150804061b05 65
    0x9800219071980e020301010402d41c089601942c41101c881002010301440c1c00902c50810f2445681154030b40d0401d80144200d8072031641e44002810781c4401c201040d40c5605048480c0d03aa5040c1d1845107000300d0100003224140000c42c3d900843c84400d040204032203005402802d0103142c0706d41e0390840c50014002012076500d6001c41c2c412030064110b0140e91008124074250b9030700c201c032200301c82000644d050051000a0110074054070901500318504501401c016040c2c6031086c1b40d041c402c0c001c8600203403203030f01c510b041e014990001902200c40c014850180e82c0811340d040c2410322688440700400100c520300042c00801e080d40108200400c400400011100b00060704004221000d00b040780f44140d8400740700861240101046103505100000402081c02c040104942c055500504c0311001c2d24183d03500f0103400c00e001c21310810850000c0e2602e90b400c4201c9903c4001102e1402c5e02022069400c070300c03224800c42c03154100b080400c9108409190825604481c5000610140202a5541 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 578201303 1250 578200053 578200061
    0xb010e0a050402130e0a0c02010f110316020304080111030f060d17030601020703020d031805040506182212090b07120503090a12030c0e040e03120c0c0a03091e08030a03 74
    0x4034031316407508200342c55106401e140d4105072504450241d8420700c6c560116420310a0000310346103c00305002d80304400041d024540006040075070180508409440c413503008108070b8000300310810090103055510540c14080d9002225082040c03882d0100080c618034000380c0046026500420003c0b2200008680340e815403c001c0065042d4800c000000c009a40c0340d03102011518070a80c3e0340a60b40380c0301e4482e10b4120350b04d07130b2040780203604200611041d030b0388081d40c603403559200c00c42000d01540d07008913042500306041c400319001060740160710306014407010f8900124049403514a203441e998032200314148107180d405014400c0e403841e49042503101e04011600008082d0888c1d00100d030a85075500c401304042c00b400302090391520440c50310fa40050340c0200c0e1600c125003c11a2014002e6103548912448005814100380301000039111000801654544a01403017250b5001c41c176850080c0282031030340074021801c50000340130044a1140151003090b0303168240558204001c49a05030050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 578202553 1250 578201303 578201317
    0xf0d050310030b280b0310180804150f0503060102190302210406020c011d010f140703030b0f09040f1101052704060e010e0130050c040b010e0a050402 66
    0x400c0307403484000b020403044201c02d401540000d00300c0c0d00c4100302c8152400310506072441d182c1d070b0a003424081001a60040349401c6401c1e0000c0002c144011500e120b2000c1c0541e01000514203240803502140e590034216440c000303040b0300d40710002904203d0100340c4503400100e035518016441050f4050042001c21120000c0764400d00480d900c0c01c802070b12692541c2c1e4800b01030068100d01103010000240e04001b0700e5254082820000c203040b58000104441250003000c441c10700c40300369203a58005108080740382031040f0952285454862600d0028054408602c1c3c040c130686a851080e50a071400c811864010723940054948130542035981d46031321805170021058144402801841c007400d81d9070780b00c5034031490348058800b11110b200d030400003203480c0c40d00900c072a041040014020089a80600f034196544041441d42001244d180c030188810b529040640f0900040740140411200040030280001c04a6043c0081940c410045686481280c600f6a0003581c4c2d5808120b241000e900030001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 578203803 1250 578202553 578202571
    0x1090b01050408010f1b09030302061803071e053901140c1e01020f04170307081218060601120545160501030f1401091d0f0d0503 57
    0x1007980da14803213821500c6413100540501c1c0c8580248140c040c00791040b16600030b25080040010307085482c02507507088000d180c1c24400c003040361000d112a5080050300e14041d071100c00044032802082c0002c0010255500031502441600800400544018140b95482e6081100542005581004002c250b42c1e0002c909040c442d02c000d96241d052600c000500108018000420144112910541d1200e540140c072100741c5c0d1043c400c241c10000c0c44d50890f012500040215003c4407240100706045208425004220200c002501c502080380c445980d4810302c40700d01d84081d0301d00e41e00019034807503004449030750010788055802d442d8131205900c629000050b07081d08411811980c22100744807642e00020b0101c411040b400c1c42c9144900354000c1001c40c0450024040e809603022034015008041c1c01a203042c10341f6036202d0b0800e90030a51007a2819100d1394918070343e9581d1925054000c0424903280419100c11103a5805446000116445560b101c40b000340303c8000032281c1200e131908080c04030701c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 578205053 1250 578203803 578203807
    0x50c181f0c0b0c0f0a052d0403050c030a050c12160612050702010912050a0c120e091f05090604020c10020409060504090804050d080f0c0d0815180703060e04050c0a0f03080301090b0105 81
    0x104101f00e008031200e4404c25021556100d04600740035107040086d04405102e80d0000007600b00003280443d0402080304159102e0f0504079003101140e050080c01c1200355070304098050b00052545e07000f2000010320b0364100b000c001039180c4c10402c03400c1e60f034480c00141189000104010040340300380c00034103c4600510f003402c0c00741c181c0c0d5140d0005c3c200d02110703031002848403008090245031801f07030310760403110039590300c0300c02c0030011245000c1c620584a140d00c030f01d41040000300213844a4040f115406002070541d412081c1c0c9094520094102d802851b1106103440c001188604151140c06082504210b590342443e1130b040c00c01800c005413210841d10000c0030301c803041d00e148085010742240b120b0764001c0c080f102445400205048070040581c0d400c0301c1042d20041d01a181d64041c50464855542e8603181a9a0a88154003501056104103001d21140b0b0801061140c0440c04122000d4211480000740b9071381d0b101c4408003040c07400058a078110801c01001810181d030b21803880d40d4410f0400c18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 578206303 1250 578205053 578205097
    0x306071110020c0a12050c1c030915050f090a0b2a071101120221150a0e010503060f0105010206070f032c0f01050c181f0c0b0c0f0a05 59
    0x40203a8109008140044e440044a4000c00c09001ca0075003c81405240040c1003c03c8440c005a84020f107410326020a4002e51080048600c240c00040109800520440105405203204801000212000c0c840e000044004c11001c0402180300f200c003940008596210f600d400e8002c411141c101e0301070b20509026130103000301c1c1d00c0990001c0c01800b805520b4280e03800041d84c001400000b0020040c0a98620411040680385000b00620000f0b40b84404580d56507511a0318140d44010420b140b503501100d50400007508040100e0801e05a880c19415a890340d10b4914403261003420a016103400b5802c42c41c0054445032142d505408040290b00d408600358181216030300e40b000c1046c801e00c9401c4801820440d4222042141803800c0c00c07034000030461442c0078440d4403000e0291010021806421340c3c1c0414072550380c94081010410b4203012080402d260b040040c0c0883c0e150041220f22181c42d000241150005e00700790740004603090006850020194003c90301a4424000c1079901e034400c001013 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 578207553 1250 578206303 578206333
    0x1e060501080d0f09030b01120212010e01020715090c051314160e090403021906020c03310f0506210106020304081006140405090715080601090b070203060711 69
    0x11a00070001c80000d003101d5820702c01c1c002c00c5804400146001c0c420703041c50410028813441175050445408401c01441809140b0010b40410124403401440d5801d0008480c00b40c4810340c0244010f601c1418843ca15803072814504003594001c55014100741e4810004004c2402e060900d481b00100004001400340e8080d000191088400d4400a0100000e506002c08264000b00002a42e401c12a0520210700d42580c00070749d188005806240c00d1150751000c01d04100c0d46030140d4106070444070540341c0310b035041e41030182c801c4940e02d1a05074200540303a59802d104d0140c0510000d8401e1000e60742c00541c24442448510b9201d407440208441b00e2481d074000c8401c1c0a640e241c00f030030381603000d155558500500c40745008072040a206d81035260a4040018440c1006036040f4403409940205495680f0844941004031036440050750b5a810000c80104aa00c49403640c400c03d42602c1e5840c586844503080d081c42c0c091048025015844107000c40c280f14010302c0307096002b40d140022a00b81c5800242c039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 578208803 1250 578207553 578207561
    0x3050601121b180e3c07090e100b091201060e040b0c0304110d08070b0411041104050d0227010b1c0b0102030a230a172d06010c140c041b05071e06 64
    0x1c1e10304002c5d50342090080040e800b4032100b000b40212464907a080c01c15598480303450300d40c3d10400801d0b0000080c00c941c20740322402862541c088000003000304aaa070040d5904000003160111000c642d0240003a501c000310303400b640d0149400201c4d00c8503c47d0390805003ca1200510402d0382d0149060015400003824540d10502ca90303c9110315029442c0c00d08107000c107540c80095403416600080c0002d01031611000c00280341c3c1178040759601203040c20081c0105034a601080100181d0030140000710b030340700c1da600041203020442440c50003003400701909041100c182d541001e005800400c2400c5985100344401101c09a0a103c80304580d98034000492165002903640700200d691441149100c40c80c101980b0707030203401d41c02d280c02c8500b410421070b01111034842c881740d0300c09000800301d5204c1c2d20403904000f080b944204121001c02550f00b2440e9600d481d030380307294452801e040c403046290300003095482241c075044d201c45080c0381499456892a4600a1041d940703050280740e180003107620741c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 578210053 1250 578208803 578208901
    0x15090c03061d010c0206090a0201120908130623030a02090f030706030c020609010504050706050c03121003120e0a0b1b06071e0503040308010603050601121b180e 71
    0x807101c001121030b01250a45024a144d10107540081040198690001c2005c01509a0900c2c08040c841010342c20340c40140b00300d2070041d0520344013095444000351800030100607226035403164009105c02c003410054036214001190f01541d0248045011080c09802428404600909180104c8982e4010a141c21169480040026113600c1c01c3d0711890f40611403e41c00490280003441146400d8035502d0b40c40c01c642c0303e000c00308100010806080072080c030030380e00c21005010149955040218006400c61800e00003622118001d50000f0030103401002d420100000180100c0041894903490142d580c02c04c0d107030039480c100c2c480b0b50f0261420060250328420140e0703881d4203107840c0801c80e0703103800c90200d40c1e44001486010002d100c0820f810500e107604490007458040740f01c4d1f8034440100e60700300400d07560074501c0303040045ca13035221200ea100c0c0c10b4109a8076a10700140d407140070080001c84c07205100d414214200900031851030780d2006030518400081c0da99122084403000c514840c6000125 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 578211303 1250 578210053 578210081
    0xa020301051806060906160506010e180f060103230102042c01181a03030c070305010b0103020922090215040509010605120a0c122906040315090c0306 66
    0x1005101c90700d4003034190420790011450700a9549020701c003040c03140c810001007071300c1402c012680516180c40301072074111880e80081641d116581d2080fa03804550015904190340e041420001e0001140c005444680d041410004121903481c54840c10030440d10303481039181b1071510083c0e0081210302400200010043c1100881041070720f1031006108400d01c0d0352101101c6e8040c1c0040002c0111042e45c2c1c0050f00d40468006600c0c001d2070314948240d0b4550b6002c40d054000420b400c13a4518000c2120b03000ca90155000342310003000e03100110704a110341011603502c02105584584040c01002103005213195208000a482e01c0b26000030311000d2000008030b00780ba4001a003408a8100303500200e004040c2401d00f1402d08d05d01c1030940884090080400c2d0034582e49080c0380b030041c0d10032800c0b02c44a818281c000c11174401807070302c6e001c9604041e0f05101c01100301c07803201a54600f0040104d5040340d40006c00340000710040403078040600440c10055031200b080715400300c0444c04902c10210b1610180b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 578212553 1250 578211303 578211307
    0x8070e121506030c03010203010513020904021b01090c060212070f080d0504051c09060c2006030a021e190f0201020c010c0c02030d0e0915010302070f0501060810090c0e0613050a02 79
    0x42c0101072034442d00941c4036001e83d005000401c11921080500d2032189001c8101503218010b24001c01d0007402952080d032412070440c400ca101c42c950643c040c0480340c0c0549100b41c2e000d42c442c50281e81c0d07400c4130020981103100401006001c1800d585000c60030601c07982c003007450501d0380e5814600765074040d01e003514580c00c08024100c031001c82c0314040000c42e4560401950b500c0c0f80c2000a0401c00d100200a00918051400c009544040c40b80d801e400703070710086c8020703103d042c0958402c0081d0856008565100904400d01c2c488009400a6400d081d40c800d510001080d00c0800440300801130100d2242559000d002c540090b540a00900307201e811980e4072042003e0740360040601d403035180401c081c14456200382c450311a84803c10b0481c3d2102d0303401810b00e203105400c40101d009209014001d8403210004080d8400c000301034015004407118082100d40898800300c102d421541540c0700100240d10004003040b40181c00381c41c141c0c0c8180c00900720760b0ba100c400313100c0f40181c6d101259800211980 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 578213803 1250 578212553 578212561
    0xa0b0c0307120b03030d1109040507030e01150302030303070c03021e100507210b010c02060301030c0e01080d0905041109090411010f03150e0a0e070305151608070e1215 74
    0x40040004081c00100302d0030f100e4030301c455000c40d4480c840c10205807045901c904a804880320460112000c1c1c1c90040d104101d98945a0401401010844a441829400c0c80054100c85031500c2c80074064a8000b0003551854a03a440145c5803a540c940703080b0154002c0a800c07210342c0c42410780c100d4284510401801c0f0744008445040c0464200408400078000c0c5150701c0080c054042c110b100c40801020305c002030020220005807207080c080000290301c500004004020404205011411100c1e00058020942d03203d6441e29101c0201501c201c00040d03d00d40100811f1401d90041420141c0941e41c2c6031a048805d0003041c0c3c80b1108480070303200c00c030036030036103003240d50740803050316915800c0e841c0c2002214000f01108440584a114031603042150f0030100301200b1841d0702030710310480c0000407104650760704d14009445903041c40b00c200c40b0641b80c0c0002400c52090000030b551914403aa2071440315a15074100386c680f01c004142c05a0040c1c100220520758030410008100001018880c0304014a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 578215053 1250 578213803 578213807
    0x50a1b030f1d060a050a0b10260f040b10031a040c051002070e0a0e0307050a1502040f06030914190b061014030408070203010f0203011e05100e030a0b0c0307 69
    0x40b280c08034001c212003080c504030161021a00c039400200345440841d131070711140c8529000e4903c0751585036211007156001208140c00c4225a120510340040b220b081c680090910030b001002155001d106840450001e00000c0c010583c903648202c0e62640c101c010b507281e0b203a00c0c5c0c9500b070010340c2d82480144c650501c03081c000d41740401d400505049400700c4036090030580c02500d981d21486120100103541c4003045402c001500300d04002c1855000316a1250711509003507540d41d105000a03101d048019100300212900360080340c01b81c49408084010480c0340038030031001400000800c0e10316464041c080702650505005030b05628803542c440f1980341100782000c1682441c003030a410303c1440100c3d2640445134010700d07507000c81001c0b0900c40d52266100c0c03c2513502c520441000a605510f0700c88004c80311039155000e103050703620010000711454640017610215101714050036a0000c1b103e10341111042c8203103030403003142102505913649085a9a9524001e050540f084040c8034004420025519 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 578216303 1250 578215053 578215061
    0xf0d060f0806090c1e030a1b0e0108010b060403031416080d0c020303090616051209070905060f180c09060d061a040e04080d0212090f0d0e01050d050a1b030f 69
    0x50a0f00010b400c4242c4608005410f510342442030000d4002488942e80c0180c0c1d0500005080b150405806018440d100f918202852201d015180500c4040030010480c648144100303100707500090102c5151505640702a0f1b022448882220103c480412034009040701f40074492806034440c041c60750700e0300c0c68040d03060140c3d00412020700455100380104030f254800020000e41128824200c807117420040c3c03404452a21940481c001100603060500070100b01c0021010100c40c80094204039a4035190204581e005c0043c5400381d101c0304c40c0c034107221030704001c04500e174010000b0b01020386400403400110b0b03a00d4104021090a035651828100001c03000080003442d802c020040701072030241000c1007400801ca0150000d0901c1d04080b8145940340050342c102c400121521290084a1600d0000166207241320803240c6590300551a01d522001d010b54a8a48001341c140c4529080800c01c0c0c1e0014010031000707010707294854032803c4540f00740b0b80518812210090701c1d50f010848815000d0132000356 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 578217553 1250 578216303 578216311
    0x507030309150903020409020a08030c06070e0105030c190e100302040801060b040f0311010c061b0909020f0d0905010912020a0b01120b010504020306030a0b070c02010206010f0b0405060f0d060f0806 87
    0xc100202d4500d1254085401d07819a0390458000591181c036002082c1d100c0340d242c1040c00c462100007105d100714440024203034803440c110f076140d4031000d0341c1600444144c0015600e50030004014000c1603403c04c01025001280380e41490442002505100007031a54a4071105440c0402d500246c148112071007030007000b000c1c0c40e94034003903403070b2030320701610282265418030020301032030800c103040f001517032040003c0854140c0105007805404c1394810799045004400388620301180400400003401c44960003507a10305101990158100b09504050501808036507908441d03956035402070380e0024103205100c01c40c2000c40e0b03009095004161800000b40304060b00130b1928040300c00d10503400107a82c45083d506540f0152409a129203c08000c01d1614500520003007031070105204003c80290302c190030100c3c843c001d90888e012a640d4500207402590140100382081e602000248014180715004082c1009242102c51402840103d00000c4070456008074402c80039400081151400801c0001c1c4c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 578218803 1250 578217553 578217569
    0x115080105120a17041a0903010c030c08130201170f06100c0503090f130c0203181912021201022209020c060720011a120607080703020708040b070507030309 69
    0x1816040701d402d5a520400f1441c010b2034400c0303415143d80054404016a8020080911000862160000946629000002064000d62a041c034a41c3c2d402c0c0f1070f004840b446030103a20395401c182c40b90200c803a0626941c841c2030341805600c0510003110550000f84c0c6201da5203100065a060400500b00030f403d0500440741c00401401c0c40511000c51404803c60709003840445032801040c40c0c540100d42000540303d1259215894503c88000c044d40210041c40e24410444030540c40c401e81c401044860015030b00c03141c0442200403018000310034180340e03c1c030020380001d2200c501c01480004070707402ea0303109100140800c0700442220b482044210a0103001d0281e0300029804e003120444032940e034140041401c01005805c0100010b5090a101850721458520000b4005002c0d103504c038031105000031003038500501080244170b60420000c03030200c1c02004141c5d03480c0160703203807943e0480c0a0b4000c0b41d07050b03900741410800003e605158200505c4964411809860300c54034606002d003881c21543e0100603 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 578220053 1250 578218803 578218819
    0x40f060c0f0f230a08040c05061804020306150307020a1b0b1624201303080901020705040501031511031915150c05190209060103050714030115080105 66
    0x30010b40219641c0810324040c038000d01804010b07000c0704403036100f041c1c52030030380352001905584055010008504c1503002d42610000b590b40c2e90140089445007012221260106603501c1c5c0440c54950000d54100d08020b00b0f1009889440340042e02d90340c03064070302d10090b9120150070800c20420070a00000c0c461841003100c001881c20502060074451a500364150702018007004042040c2c8600251000500d001254524650105060001c1c01c0e00c44464038a84413440013082e4161940b002c03503c51003038020844224915540d10600303146c016221050644c0030360b13007012071680c546124160085002d03400c0980c60081d100c41010481c0e480040c3d00018210800810402d401c6104c00c0041c0160a10000100ca448050364100e5108060304244c0c103d0ba100910f01c8100e43d03102014100c20790040c4241e0342a11011750304c48103402c001182c001d401503d0000010035640c042e9000c51b40c4004941440754490482c000140c2c5694001d1700070020070f440c2c455104030340950100e10680900342c00c1d02d0041f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 578221303 1250 578220053 578220077
    0xe060d020409020d060e0309040501091104150504092a020f070611031207030b030f010203040c0909081b0322050a030605100807030c0302010e030604200d0803040f060c 74
    0x102041000400603001d5a2a041c44204544039044150540303a005101007000008004103240ca0390701c5090407605c164281800030800079194030408041e5022541854909490590050300e251055980c10043c020240800218140c0f0350150310b0b4220400c15122445089241c0240d00c0b07903500c00102800c641c070100070007000c10070002e04403059401034200a8140c0c60668145461031082c40984c0c103101d20039205000d09150581c00c607030030055089080e160b4400043c0030513401c03800700329806010000c0e8000100101c2c8803607880a07071402d024801d680d107002c0c508410300701d0000701c1000d41e1f03031560b2001813410001040b5842d40189084a8500703141c02d103240c000010881d0006000103480196100b0100b000001000e08110081030343e1001d440c20f840d6603050403040d03040603100c1a40818500070b0206504d282c0030500074496580085407030440b1007807500e0700d9240c1d44c842e15425003095250201c03d01050078100950301c10382c80790a4403900860103203442002d4554003204c51041c0215100340e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 578222553 1250 578221303 578221309
    0x13060606020c01030617060601031e0906050708010e19020d0e1f05060a050102070b2809050406060905031c021002120a110a1b020a030b091015151101022109070e06 72
    0x2c6908238800b40b1300494140c01503803118401003040110403032014074100b251010007003280c03c0b1900ca40c415031524a82030382c0c1d0b4640c2600b810812514440703094240da40c000510f00941d406080c0310748615034001415220b180c00517103010411004030b0001030301e8140d2514454424081c495011500b40c0384d0740b55241c0b6101c0080d40e0f400ca18000d88044410100e440d280070019182c41d0308900900489600034400b60920180c460840343c09818000c40c14540f02240c0c0c0350140b542d01f001c480015005202c5440440c1c0000c440d0b9034519110300441c0528041100051201e0026240b41041005640b046080a40c4948125000b80c06135213030800c0140aa2101c60b40c101c83d40c00c00092030712080d03a812400343d1000410655407030704010f065001e1101400312541c80018800d945c0704904101b0002c0c40b034611b5a07241c18000600c182d103091505007240c00b410030300c6814481ca034140030800260a2102c010240456070311200f50b45286001391804004410300100701403002850a0b000c00800c0d82420004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 578223803 1250 578222553 578222563
    0x3030e0c01110703200402040f03060506030106060c08090301060e0106020f011401081e030c1f0e01092109050406080f0607050a0c23010c021b0f0a03030813060606020c01030617 78
    0x240010b40c680b0489504401c0c00e440c5e04811240c018011507079191280d0b04585810602d0100b80e0b001482d00c0c0c0000c0c0c03a41014070a520999080d034440c214030340420356800d00182d00408100e82c241d52181400140d10300c601e502c440c042c00d80c64020300030701072021484608452200201d800f00540b51001000164404510280603c21801104040c0500a01d5040c42c500c5000d1a148040c406c015840300e0140706c10500214030054248144583e2400340811801e0321554240074110300c803010f07080c0d018901441200c603420341160400d88907640c0c0e160005402c4070304541c800c002d2030300159040340e5005420300c0005d51144041c00e11a080c000b0141005103000912a0010050780307207201c0003680c00318180c0d0b00c0540007518400910402e14610402910380001c12240c03011451126404070303582c50450003020321820081c04954089103145c03030844521a016001055031103084e240c050200c7c5041c00344d800504150b4000b0481ca0001a000404540032a44040c2c800c010014405142c2000421 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 578225053 1250 578223803 578223809
    0x912140415050a050708040f0e06030f060711010e1c080108030f030403030213030b180606010f0203031f080307030302040f0b03041a071b0c03020a060e0a09050411060703030e0c011107 81
    0x10700561903c2d0100310548440c0302d810b4004d0018000070400142020b1b070940101d041d5111403592401c2a11080300f03066aa09920780c1e1f105e8241c000c4800034034828850702070107004066400000c01d01d15010f00f1068101800e00d042e08900b4102c0c4101d00a296800c10720303081c01000001e000794a802900e007400300e007500000d0302c006d08141e0002601c01e5649c1c807455016001d140c0002c018815814003449101001604464a42079409000001180d560160080b0811403120350007071407a640d1503e5100d06c00454949510122400c21080895020030404c06061050700c01e13240166110b003030400d80c6841403010303482070309140010000c110000d03201c1d003208175410202317103070182184c2c0751000b050320354a0480b402c9004540c1105544020f1080c42080001120300035525090034586500c8202d034486240300180390855540002004550501d40c0400d41c0580514003900c299601c0c2c04c0040d009511199003600020f4a0303040b110341d001400d102000a00d0024203220300790b5544085100d032a00203502c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 578226303 1250 578225053 578225057
    0x6072a05030717131710021c0b030c0612090102070c06080f0609070f08041406070905090a06030309150504090f050106110c01021b12070611060a1401030b040212010912140415 77
    0x103e15611715540400c04504000d902410564880c001c411515088010b034001960186042c6031401c24581408242802c0d10720001c0c00480c901694004a08500d040c0a80402100c2d9401c03c0071101003800304041402420443da182685e60170500c0c0000107007500581003c0c40750700c0b0101440105504a0b4030082c9507103540c00d04450940e15070404604881403941140c0d00740c003d0500300241664065403080c00d0f00c1b0304444001071902e4840f2620102d0705280402000b00d111498140602c4880c15444c104034266483c0281ca0245c4425114007611440c2c80c60004840d01c440040c008150814410307003840703080e0320040503600c0c00c3d40c0000350b4404100090141d049010401051a52101e4100995240ca040121140341383e0320f050050004880000f44e4442d4019034010980c400064080d80300b8400b4031114030600c40e400d6482c0e072012188050001c036400b00c150708807040060001c1c010354a00c02d0181021075040c140d45a03024014a10803040c407031000c04108800c0c40400803691250f0944001e038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 578227553 1250 578226303 578226329
    0x30207150b0d120507210f1b0201200d08180309130b0a1e030605071d100c02040f0501061b081815040b030105041104060206072a0503071713 62
    0x200f00782c4040c82400700182100d2401c0791040c040e51010003008016000c05c0c1c1c0c1e40d189119074840c08a0390001541d4107400529403080006000d03600c54032802c203901381e000407240d180d000e03c1031401e8500981d2019560100e428802004040c171659441c04100e080c1900256150a030204001038040764030400d610711003075aa01e903a10711307502c0b130002c120050060b10b0400220100c1003880c0b0004095588421160141483e0000d19254420503003e02469105070110380e24100c4101040f5030b0503000c0d4800002c0120701c00e03c282c0075130b650380a4401000c0195500080035410b2200040100d040e03c2a80700c118180e195400d400035200f10304443d0307000e0781c0c0700c5c0c0389050000312000148040d0b090400704000c0c0d000400d0100c2c61020400c0110b04840040314104410118442c0d000110301561140b500982c02c2007001501c22809032400d000d0a540c0e2018203004181d1203541c000b118034481000f528654004034099042211004083c90103440c40c0d50080c0c10320001100c03c880741c400f64052202c8644803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 578228803 1250 578227553 578227583
    0xd0c03052a0a03020a020f181603110a05070b0a0c14090310150e01050f010504170109140709060504050402090402010c0f0b04060507020d08101703090907030207150b0d 74
    0x7100c502890803400000560b000565241002540d6000751038051b84a89803071080c40000f807604a001000d6120901700ca08101e40c0c554030354054581c00314100a00307064403040c04488003511103000388640c4645403900d035100c80450601c0f0703081c003000400d040e401e07915040002c010780e5000101e528000c044020855500c80c0c1e21004242000c016404030640340d420240a0074650034010348003c1a03500c170035254502607036130300c00304081c4605894030385000c507004100610842d160844c8900c4541c0300d02001140b070703550303903518400c06a0091901d81855003162000b0b0011210714007a010041c58212018402c509080d0000fa40c8000060070085c1400b0311070078102c0c104410072a8102406400c0308002c21989010b00b0b042001c0c0c8000c464070b50050280b1a65903001e0350089003518000e6042c40c0100000f2070404010519002031a8103c500e140310a0101112581d42c1ca004c60384102d170545e87c090f848d09110319260300003034140b02d120307000103082c2110b200785030f11092618a407172030b0019108450f0100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 578230053 1250 578228803 578228857
    0x3031401140618130605090901020304030e06090418081812070b030622090c0e0f0402220207081e0712030207030e030607090611030a08010b030a1d0f0d0c0305 70
    0x200d145030480d003058500c06000401d041545c45001200c2043d02c4003032160741c038919940d0807844100c500070040342103421486070608018002d03064408005d03100203a09a00d9007090840c248200c04201c0750726500140c6c1030001c05d008030072010342007001e8070f98100c05441c0300110740c1c450016000b43d0360800000702c0095001d0741c40e0600510100400b810342e4481503545011032000d03043d0030800b07036104410314000094030401d01d1400d074403d0304880d0302ca0045071580c2e0302b001011044e034200c0c00165400c0001c4250003180c2c03840205604d511030030590344c0c0c03004501040314006108000748007a0344424400080813545007420211000c0e150315005a640c516482d09a80c11172404280030307014440d910030022456085006035056807003646400c3d10301d48071107500f20b6991180d501100c00162001004001c0725014001440d0418007184020032000a45440e8101c103095118142c00c499000001d0502c203020f050001031280900d9103494540e04405442c080c04074450301c940707214459130140001100d84 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 578231303 1250 578230053 578230087
    0x61406030714041712090618040b1206040501180b010303080912041701060e0105101d040903020d0e0a061b1103010507020a0201080c040614030702010e1603030314011406 75
    0x80c0301d41640e42c50315284c0c0c04030f0040c4a00c0b26500c061510440c0401e0154401100950f00182801414246020402d5059641075000d81d82415003041e101c0040148030b50341c41c0011a821050b450040800c4d240a003000c41c251040111494100e00d94a000840460b10051a840c15070303405003850320042d282d42d00501d107000c2c0d04045e81c0c2544100820b020502c1c2c0002c40340d08441d0b0302c14800a01450f42c40700784520b00f002d800e10072658002007114611200c035008005002350202c034003401c450070080d814049010f48802c0403040f80160018015424015000b00384c84a0600c415540341c145d503424400b01074240b01d407103684900c146103d10b03203244c10003010b580c4040719401b0103070090009041400c40a903461a170480100d002c1240c060000d5295409007094600311059070365202420125080240d2250f440603080d80215500c41d8100d40c20781c503042140d100411480902c1011851443c04c1c01401c94007948060340e00e4900340401001420304018810104520442d5119503c07d01c40c602940300c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 578232553 1250 578231303 578231327
    0x1080c0705120f0a0f080c0409090f020a12020111010c0504090e1c020c1e03030a08310209070203070b01051207091506090e2e0b07050f010606030614060307 69
    0xa000003c0b00500380d00e00d900644031a07901501e502a0a05e1602402c1d0740f01c03101220310348200e1f04240010410305030301d83c121180c014090380003444c8054050b001f00c1c442c840690041c5403c2d1905107008011547d0015032880b00520101c001c00c5041001e0310001c14a2140f8840c003500b20f0b44034550119090424403220019a1080e0500703d0010030180f8080e440d4441511040d10418440c00150401482c20483e0b116204005001d0362400304c0c02402034590707881c0540301101400d10b54144a40083c1999a2090f43d59440480640bc2c1c0300288100b0401e0300c4010444d50864005000342ca001402c0008268191081290040c2a02c600900c0c0c80b03207011001d500514000b4107210700258225042d013580c506403880d56503603010300740c1c83c0c03980e160905a095a5041b031031010760003030040300314440200801103051558819106a5980d100c0e00b001d820048044e1034a4001c1100492844001d102e00070052105040501030a490310940540000761551308601510000001440700d40c419040c3c5601 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 578233803 1250 578232553 578232583
    0xa0c020d0602091e0108060303120a1d0d02030304020405150603240402040608041e0b01060530060a080d0f030207020d05060c030417090a0b070309030b190f02030601080c0705 77
    0x880c010031040104250684c528090100b48410b021a2031400c010048071040790100c4e083c0e42090b115101b00c82c005080c6410340c0103c0c1d0343c01505442c05844240400001c0b400349034021500c90a00b801000304907140a0000310030350798800114402278544009481d40140800f81c02403991907044981180c001d07541414540c0b06100060200b025604aa0a40d0080380102010741a4500c0d10080300820401a0400381c043d118501c010080750748140000d280040a00400140441d200c0e10900218591190482d0740c1000383c20800505080413070154009000000007080d01032607401015200c454070100720010150001500740544d00c608000d90b400075849400c0b51454a0500c201485540040d00e04507503183c1c00c05c070340c0c00032540004103456900368001c00402c51240b51014000b0729030f01504045051100755080000420491010644241d8172103c028a04080004c0c185007164000100680414418002d0094503648041004da00c62500d0a40c19901c44650a00380c0c6844c0b030040d000a8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 578235053 1250 578233803 578233819
    0x1020109020415060e030a020303070b04080d05190c0906080a021303050304084c0e01050c030912070c0302090402060408011a010936020d1b020f030a0c020d060209 72
    0x4500340303d400d14075045442694038003d40000040c105903e03015420000780d410381c020301c07000e00460140c1065030303009840359204a14129010580e541540c400320307010900740e44085501494242c0c00c3c019000c48500d039151080d520790500c0c0b0b01501e40072015000c1181c00b0b41c042085101e014043c0703449800741d9005411207840760380d907141c03090341d80070b075244440000301840861401001c40b40e00609052116021600030122a0300d032440c014580c54400302025585980d40c03016100307003e21907640640400e07484c0b00d41c1c0e444c2441c09141f81c9403102e0344a05c05030390204816408075003504000801c0c4c139070480e000101c90321203000040c510301480e0020911540b9090341200400580302c880700440c1001c2e2a59a4220f59480d5883c00c40303400b41c900c0d01d0300d0318440750401c0d40060180640c1c00100c039246000505101540012004a501030381440400d641c2d1b040030300c00d20a80400441c424040808021441c0a44007000204403071419a0004c0c016040b400da12001c0040702c0d0195500c0c880c0142c5201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 578236303 1250 578235053 578235071
    0x3120c1a0c0f0d0c1403152202070b0403110a05120a140d240b0a0309030201240801060e060d031214040f1a01060e01230c060f0f1311010201090204 65
    0x801004c20504080201c0d41641c01000fa05103e04166882455a900080d1485100300280024411021040a1081d05060074014056800e02c05089041d0042984080c10b1804e8900609070170380003a220790990b03000440314030000d40001503990144011a80c01611621290029281c500b61100c43c2188500007143c1d0600c0300000b544403034005450aa4800072030146076818401c1e600d0703203015050100c0c10411003e01103c0c02b0b600100340081c0b2030720000941d00101c50181c413440080504840d0507210b4a90104001e440c02d00940300a00030341e070300303044840c28a54002a94a1041e400040c1880503000c480458842c10362311100350312101202e00d070054900392521040000c0c0d0030f101201d00381d40c8064601102007101090506035082c07510794140b82c0c0030840041d520111650481c44510084a0042041d4480344002c1c00c800401e00000301050300b0201d00c040420340380100784840603010401004102140c900d4002c1c440e9810038210800003804000407805001d10781800394015050110503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 578237410 1107 578236303 578236327
    0xc0f2301152d15090504140f1609092a0e060d0f11041212030911121c0e1206040807060e1c080103120c1a0c0f 49
    0x6003105680c903543c034041103c25412010025006400030001070519000724030103a02859048980c1b8984007804080e4824010020400c0b1704013100c48214040c090060f64020b022086818465181800d0710030401c2c03821302241100b5100c890102d1110f03a03110b0b000014110b80020460b80c170f004002000d0030040c040b5050402e560a6580e988500851160b400400007080c510003242c142071030504003200003c900400f100306050500d0001c078005030b160744900401000403200c0703019910140d5107448c5080c2c0304140302204104e07a6030300b1441d8039811600070301001c0c00444400740120340c58804030340c035880141d40003000c2500605c1100000340580d00981c0c0c0e50841d58088070307528908805480c1c8004c6141c0c08010109040c0001402801a4449801100075050404500700303141c43e0b80312200503c2802400302800d0003000420009101c400445090b8180c447d03403107031290111040 = true := by decide +kernel

theorem cover : BRFrame.Cov 578057553 578237410 := by
  have h0 := BRFrame.cov_init 578057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 578057553 ≤ n) (h2 : n < 578237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
