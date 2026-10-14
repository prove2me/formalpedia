-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1577
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:48:16.996617+00:00
-- url     : https://prove2.me/submissions/d4be94e8-159f-40de-854d-fda34d6d6c83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 283453237 ≤ n < 283633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 283454487 1250 283453237 283453241
    0x1329070221070303151e06090503060f1015031d070e07080717011e05010305060a0902030a02070501020c0709111e0313080a09090506060f030c1c0504230f030406050a020c04 76
    0x1500c941c42e2904015019918030142902120043c2400e050484000745403800ac25180c40d80200b40034018001c2000081c505040020020054000ea144086940c0f21160700507005240401c464201003170082c0c50448400d13400540582660b040f41c086072100c2c1c5a50304103580b001c1c2c014000105000f01c40048410605545c103002e4020200203013042c034019002ca110328000007160b08170034105410a82084460344804012100720740000740d0041c2c1d82d40e00c4c0c0c5100300003070061007001001940001a02c404210340015250143c0e8040581041031074001c01750031480380b040002042840b04100d0002c01c104020001541c0c1c8455612000310141c0708655031844594042031400c804030301070180c24440c0c991140310701980440103807111442e0202d500041c0b540c40c000200111f07244840004c40740d8610b22600301850f8401c400c55010b000900303017803402d1095240000c40356440e400e400700c1c8003a25000005800003c14052078080c42ca06828103808039216070050500380b0a42c420716101c0d0070315881e24 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 283455737 1250 283454487 283454489
    0x804030509031605040c0e1e06070213090212010912080603011b021b0603040f020f0303071506031a041101030b030312011d01080d0203090603132907022107030315 72
    0x2ca03c0c4a030070501003108803031001c0c078100d0400c1032040d42030750540c440b024900900b85e84220480e0000c1da034000040c41c54803489000941091588501000b4041542c0240a04a100b00d460010501c4c10b005164208c0c0e500d40e801800310701c84220040b41306801445600d400c20400790020803251642d44c2140d0951024107401c5d001030b4040003408980c22034800070101da400c01200d0b02031031400c2030b4a9504109482d042c020340308803600c841289440d40c0800445800c10382c056481e64241c40c2c03c07048940102464807040e0303031400810085a241c00b00301c0d07108070700c41d0380e2004106000c1001100110001e01209010b290984400c00510321b1003410b026955000b0007260078500300803845203014a2010301d0690194205500000600c08150340200035913084100076036919482c0d903501103c0110002c1214005003840c2d05000c2e001000004200c501402150703500030016040d1101c0c5030803641c1c2c82c421000780040030307180342111a10072084001080403d0007464080307448031040c60900205049 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 283456987 1250 283455737 283455763
    0x604090609110405070306030b0a0c03061e15080f041502040503120702030d022407021e0102090103140108212104030e060a0906081b2b0c0906080403050903 69
    0x10800c2c910b40645440d0240700c1e0700024602d424840d0502e0340e5500c1403102c0d40600780401c095201c0301c181e00e40d944664000c07001051550607200e0b03541c000c1c81242e0946105809200084420341050860103400340d58003602800c55161004083da0320350311040d0324008480da00440702070b020400000c0665081042c2c40150403404581c1c0d5880b4014410145031a03042c0c0d42d0034040d90440c030030780c40761030240f818510440c15a1210411290362604812803d0440c0109040030744000c01c520036604031415406061040c00030b807000c2020a01c44850320b00c0d003920074882c1c1c48407070384202040d010002203a001031202850220360343c0d0030554409084920060400d03103402010181d003081000b803680c800e21400c01d640081c1c5516152108194000b002c141941c02100c0c01d21500c1e41c0401e0b40c80d400c2c16181c407004003c05c0080c68075032000403082c0c14114034400c104030f92030b44000c0d00d641505446100700069020a601d4070322204d4034052040e203082c5c1c001802502804800d00c080b2407541c405000c24110511 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 283458237 1250 283456987 283457003
    0xc010906051806100b0a26011211090411010f1b111f020601060e03100c020f07050a050f04180c08010603060c080906011811120702070e090a02090604090609 69
    0x105940305a10f408070040424034558110035080010744049000c550010241e45092607070b0400c881380c09003100002030301585e08888841d0001032020902c01c00001d002e440b40e80c0d01a20b0840e00d500304510a03e040c2c0b000781c001d40c2c0c65024650190700031858882c111556080401a07240c0b0801c40e100c0001010b01c06a454094071820341009103050044010881d43d40c00a1a1104520b80b070000c0d920b0310140183d9080c803035001203020f80c1d59030030426110214500c2d00d00703000610074214000d458218040c4144a030384a03c000109183c5495080401541d2001d13210303008100084040001620b28000300305101240b50000501040801941001400c024400801c50610b189407403c110f0740607232002e0b020440440e0600072443c8020405504540c0701d11010800c811a00303001343c004100300040e142d001040050303211001e50414047c1885040b441c4c0039a0b400725510350010790300c1e8800300c65004203031708910003080044c0b5102840da40c00050261000440011aa0b200002c90701505001e9030114 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 283459487 1250 283458237 283458271
    0x1403150d1b06050f0403061a03030a0c050715170a02090d0302030c07050d0803151908071503020703090b0a02150a0906050a0204050604033906020105090d140c01090605 74
    0x1010501c0490010007862910a240c400f00d510840f40e14065408000c1c41c9580700c00350310b650500400c43e40b80c003250008090300e0366407526040252041d80e01c41412030b5103000e1000c0c00a00010f1403400100650a240c6403850716401800c072081541d0300003030081d0412942448400820348504000ca480c023071190700159038130402c402c0610301c0c2043c194030070392144045000440000b04500c0070f894100040c600311000d10758084d8001780900301ca102c400720350300d1001180002e0080001030000c085a502c10b40e0b241c2d03500c550078000c8050303204000c000380c003241004200308030b0500018024088405144181c0d0b2031003034010740003510346a00340c0e03020b16100d8803190050b09000c00b91241981000005600b107242900c0c10740440e40c203018521025050305401c10348204d8078401041407600803403003840551001d500341508003203070300382d01d00540c0d00561070070001584d50640061802400c40041d00c0e214454040071143c440e4603070141340303a00d1241d501d414100c00001d0a500685011781010101e81d4820 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 283460737 1250 283459487 283459523
    0x1204030c090f05060f010f09051306060905030607051909030204060608011e0303021b01030b03030703111e06040f140f01060617010b07080309070f03050604020108060409031403150d 80
    0x150350492880c091491074038041c0244e0760344010710080e0143d420700b40542c038481d4154094844500d254001a0030100242620b5090030701030b40903c090704d615031520050162140c044c103984100441d048400b1a808019002d505080351100e000310040a180c070381007117602c0764085820b85425600400210300c2000040c030409001100e0188011042d82c0303680c0c4020b1454038025501c3c280442020f1041694a01c1c5408a074841e41084c0b05442010302102d540d8821803400078501c0d910340c44564041d0142c1d010001d400600c0c42083c03641d89060400034555078407a030b112a04c040e00310300001c55884d040081418400e500901440600060000000400c1840c01e00d010b001c003103821466203150011003005014500780c0f1026218103d402102d00303501c90340d58a2284d441d1000075084206074504a04002007000790014280d0701c2680700fa600c01c0c1c10303511541c051005076140103030000d022412000544005500820240d64000600703003515200d01c803003c02142c2540c46109041daa4200000240948 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 283461987 1250 283460737 283460741
    0x3080f09030721020405180706051c1508060f0f0c030604020d0c1107060c17090d0203060f061e0102030a08250e030105181f0f05130501060b030105130e1204030c09 72
    0x100505000c0003041400300c0741c030510f450f0829401600107011001c1040612801740c04103001185d000e03003200300961030711800a1480330086203e2801140b14400c0001c00d010400c00646006604507029200c40351110000642c03190001820702e60000d03420700400d80101030600504203248440e403101d619100c0e4104200381481002e070000c2050020242d00c2100103200c0b600c16800c08998941c0160302c0707a05400c00104040c000b0000a0b6051180c1014000c1c0c522001410f5409020203c8055201e00800302c40941d1500c00d034802203025800a03c82c881c1c00500074260954001640448624804610b4001149034612660300c4e4000a51403201095036081c244611900460440010080b4420781600290b458103070b8042181c10005c540c802d426070000039040b00360101c10f101e00c02c0c0418030f020200d1070f07086000c0440649072582068000108568210f0440303040e580c000e040c0c4940501000c0307080019040e03181034070509100700c000d0214040c038410b02400203540300f00003c00c101d41c42c224403001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 283463237 1250 283461987 283461991
    0x4050d0203030601020a11280905310201030e03030703021206090f04170705060c090102212a1903080919200406081c0903080f09030721020405 63
    0xd5600c10000e005a0303a0700020310311211035200080b0380c0038001002c042a00d508400208040c038600a40c03124214080c045101c0d42507070416502000380d581d503800582419121420384100800c0c8801f10b040084000490344800140103040121b43c00c01250546441d5910032a4000b000030f6010801088904031540e04035000700048a440c542401c0c110f4105101e540cec080d10080031350b403000b00800159074202003a15481c5070450141c2c2e00340e01d40389841c40d013950b00c44402d003801400b402c040d901c4030454600c9050b2580c64003402660034440b01d0882c5804032403803400700a9048650724001a65007500f00012282809c02d2100d00203452110326000e0900324001d00640b00c69042030303d03000c44402081c0601c8111a0700004d9480e4407035484500d00c1e8103050620400d40d0018108100403c011030001442c00303500f00d0404640c412080e01d05000c690750f0385035020003442a0302c200200c01c1940300841c040c00904c0c40c0107040d600c4440c2d441501916002d81180b0844c9490051000001546861f101c0d072a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 283464487 1250 283463237 283463263
    0x60b060715020408100e030f03040f0503070b0f0f04030f180509010909020103051303020a11061b0a171206120f06040606050a0b07150504030219030201090c0501020c010507030c0204090f0b0405 85
    0x700c100710090291b66181d000300f200602c1c640001000040510006814194a1a070080d003500c0c0d8540003810300700340c556011540102020300300e401298140300103940840c400c039010f80d203c0e6511003c04000300d500041d562410f1218911a03000802c0c9550340e1300c880f500820740c814001610f0345403840054141c607001000a00c0348041c3c1807206000ca500031905c1c6401c01d0b03020481c038004480140005026006460102e07030a04480c00003000024800141ea801c024051980a2403000c1c0c0d21298205070f102d140401000d605403000400d20505001c00e8440c035081d0350380b00351044400021103407494460119025a0040e03207c0500f04103a00b481250740c0b01030009900098035196240e225001c80502114454051a07036410004061610034015000e00402c41409032440102501b4028041d01d0008400d0b64007540403600011151b000040702c03400b500040e100c80e405c04066031801d49a81c2c07441141607030843d0300c1d81c0d041000607502c0d0304010368070752041c100c514107030406042c40c42c03608041311001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 283465737 1250 283464487 283464491
    0x2030403051506060409090308090606062d0c06090615011e0e130f0e071409010b03041a0408040e070c0c05060c0703060234030c060b06071502040810 66
    0x18000700720041100000140c101e11405280e46804010a020380300e9584141c070a64500010744041640c890b41e03c40c0152481c0c030032900c05488042c2082500d10403c00240403d560704100b80e0800400300e00c611100a0f4480d0005042c12880060a8140a0119014541030f0045010451441e00000c4001040602880e104060100d2807421080101600a4140500c0f4012884d446243c2d1184582e40e080d0400c050f0a02100900c004c040000d170402000900c0140200170010440201045491220380c20043c01041980d2030141503424640c0007800607610f0721015061204400e11245038103014610510020755106d103030407614051020043d00d86e104001d0842e440c031740230610750036844042d2901100c40503650a0050905440c00607a0390005064500200350100b0060b03866000d04c028650142c07030107086a02c0c0c0042c0400418280c2801008a8080d0410300c0c045a01580a011015006441c4601d4840f00342c840b003c000e0103440342401c2c9660002024040d000b0203211341300200640c0d45007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 283466987 1250 283465737 283465739
    0x13020918100b1f02160509040803040303091a130b0702010203190c030b090c071a070f030203040f151e020f07110f151e030c0d0c02071502070e07020304 67
    0x10352501c8800500749401921101d0104071581c03628200300c0d201d503442d020701000040b072420294465800400c01c000130345441c43d0000f4542062070300d0501c80c03a4003003035192940c3c0d201c0c3d80c03d80082507a540d0944004200307154005102d489030032818054030a8544154030583c0a180c0005c0d0080018541c03001c590051082c440f000180e94181103c80000f04000b085030070350a0012002407005807005540860031a0500101440c514020b2502d180646091002c4400b84d402500c8903000543c2c0c0400054001d1f91080c5016200e035024640152080242003000281030f140d030403440040f10401001350303a0320356186204c000302c45484141c0302610b0205608042c0c602560083c90f001e0b00380090705492074101540c01c1d96a412605507603c41004110660f54045a4440900c0b9080550030040705001c00d61010b01c1e188501007a41e01c5465104450361900d0080440080903001c01052041988903140c0007242114900c80000d012406030350080450300d182100c000300b11321024204400355001004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 283468237 1250 283466987 283467031
    0x2120f06060d021e01030e031201050307060e0603240a031b15020307060207060608010e1506010207270905011803020c0d0b01030b09030c010f02070b0a29030a0b130209 74
    0x10450b0191131505000100aa10000050b0301a24268021101502001600f1003030421900051411f80744103404448900e0f840d50300c181d0320010b0b0360001c1680f00d0414030004034034124240301d1082e04c540319294040c5499501011800a07829a001158191601c00741341440314041026034005005440b640b055035000010040d44074492284090a103d40000303440d0300340803850704580024402c410007000401040c4e0304158540500d00002d146c81075041e00880d110351f20028138401a03448010400300c10742c0d0714a1400d0080249102c910340c07241d48412401c0085802840399100b4440320202130310160382c035454002e04120114182911803006801e070347e40410035440e001415250306c0b40712460603444400c040c615500800c01c0c14909907007413406101341c040c2e0b00d801611825128000c142040c0c0c803900c01d02419204042000031701c0070a190794031031041424a80002825501905807010780b01180c90307401000e0401c0320100c00310310303400f400c000c110b00780188503035400300c03a0f18100c54040074299 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 283469487 1250 283468237 283468249
    0x2d04030311150601030c020307050601080c1e012a02090c1804020705030306040203090f0706090e1513020906040b0c0601080d0f020a03080c040b0d06170c2b02120f06060d02 76
    0x382c00f9a04150b600c0c28844035040c001c2049911450308041142c01ea0341e0b40701d02c0940e4454040d0100350049500101040c3c2c5a04a14000b200307a09058558103200840c601e5420040708074580c1c03034000540900161005602e501d05014011910742050a555841c0c1801d0f00c004815491100c602851041003102c0c00700d0404800c0e20b801c102c003203c02613625141c00d007201d80f50081c000300499140c0200100041c800da00504001c0450b0690310307411105070341d240b0101180e51410140150080c1c609a0042c050000c154010280d1440040c8142d050940348c00304c4004680102001807400d07440b000c0140030f03031001001072000001581ca40042900d41107400252035011980c1c008081c0f2142c90041607a1000100940d0090208606156200d4100c110404050b10310751240c0c16964010803010300c540340c0040740440e0351000140c1844036000b02c5031100c0e1000800344420640b26122130284200603a2007103201c0c2d02d40e01d0200020300034100318118041c06c02d8000380296105103c2c00c0c08403c01a1150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 283470737 1250 283469487 283469491
    0x90f0506040311120102070b0c090102011413060c021213050f040c120c03091208070306080607021222060503010e07051602060c1203130506060d172d0403031115 71
    0x75200903030f030240c8113540b0f01c0c068020300c2e800410303001d0550200020918070300007030050303084264000d0180c400107940001c5050713002d0b1003c03c1510840c0b480b8101150550b0488008410f05204607800c0904070075441001c3d0b0440e80382a680c10312149010807607031405441c44900c2c400b0845041005460a660151940540c05c820025007500d40c001c00140e14000c0d031004c188150001040c019107022500000d068503802c844103c0860f1620b007000c5030021000825920400302038009241501020710221013a4100581303c00e051414004420140d14000d04500b000306669200e082e165410701544803c1908014100d0042041c14003038407000304406c0e00f00941942c2c041e201c10b0b07500d007039841c2000d060082000508403040d000205000034107078031526070241e0a0080058844035103540c010002d01241e5503c02038504510844031560016080d8010011012034281c0719100703252014070401c00382e1a6520f00150040302180400030f25801c00107100c0c0500c0c070131000d4840b60a486000028007400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 283471987 1250 283470737 283470739
    0x210408120a0507021306050a060e031908030606180d050601060908010e030d021c05190c020a080901110f0105010312080105011b110a03061104031a01081b011e090f0506040311 77
    0x2050701402141700c003540c01a4041d1801421310b401e8075455082c054195000008498020f1151002c402202c004201400000750391044a561a40c0c840d90100105d44c4c11480117407445003603440d01e5565680d544540701e0652407041014140c65850008090081d01d450307485903c1d0359041c0707a408103000710080119a0101c018080060b00c3e200b400c0848000030884801d40c802c8030b031404050141900a112401061200c454414008000c80183c200d841c1c90300900001d12041052151001d15801880f081440c43c020500301d80007a40042d10160079617a0a030320a5554031010420101200c0e48803040a01404080c2014000c0703080e4810040c0728040f19400c090640c1c1b0110701c507485265100402e0030010b50f0842014403210340071030721810185c0e000744000c40d005e00c1e1804182e254141c01b21b5030036049070988406448800c2000381020900f047d111800c034100700918060015241101444d11800c05090741c4801102d0b080040034861981c903904107500c2980c0074442040068000900000e40340c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 283473237 1250 283471987 283471999
    0x1150804030905060a0c0c06031401090506120d0e03060c040503060411130c03020c16080d0f0c060609090309171002070f05030c1f1509020903210408120a050702 71
    0x2440381000c8414010940203e540200d0000b030020186920444562002c0e024541045015035645425401c0b202031030f100c00d140000441c0104102c111070340c06030303a00200151a0f4a440002ea907a1142005c0e491301c0640c000c035190b00120529420300300b209aa101941103180c070b21b0f05041c10006503580381c000f04024212500d03c0c4818049480c3c152450751000b94000c0300b8400300c1e03408200079020390880d80d030224243c0320303030601d03410103010420071182250b01800140555190a0500301d800c0200b03154080148124000d107000003a00a10603078004142584000580d004a8603004100c01601e6004940300c031201c4124484025003c60115607080003010f0040c3e5450203803a203100f810b010814085c045020102d1502c00390b4501003110414030030a0490032951030a00009941151408141c18550200c030f004203100303050540d4002e00d40020000d080b40c841c0101c01c182c510901c020701c80e200813103400201e0100710800082000142002607501210308006c0031074002416401a03580281c8958 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 283474487 1250 283473237 283473241
    0x12020a150b0109080f0f160b0f0c0316060f050a0510151e0305061201151a090d031d010912020603100b030a02030403110f060c2a01050405010b09011508 67
    0x1a0040070300c2c0000740130850584107003041120019843d4000b41c6000640c1b030068000b80090206000241010307101241c1500703040c0318420301e05001c01d0304a000540c2440c0f00c100034010200e06a0550084424415000881e80c209c8115680080d40c40c050135501180d8280320030320110b0300041c00510160342c2400b5028010149603142100c01241c5400303500403010420701440d403202e0340b6400452081c4002c0d1072020170001005806800c80307018420180c012180031a050000082ca6100e00c02c0c0c0a25001c642400c0560140000b10000b915500860101c1c251107107803880c6482810300c0395066802400c140c2c11443c90541000c4040340000c4e0001c0c82010b00100240402c00305607a45400740841003601d82c2c81f0714240030300a000350300070f0b10281c0100313280810004044400103507000603150090080d000e280ca800700c0b083c140b40c00000c1840d070074100d10194000030b6500315803c0c000d0002e5501c00450142010704040e400c5566012081d4000c01c070403401881001e45c6c9413030900320700015181000c220303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 283475737 1250 283474487 283474489
    0x3091e150c0118050706110a200a05100c060c03020412021011060403020601030510020a17150409051005010e0103020105030708221505010b0306030c010c0501062112020a150b 77
    0x404507000f259089032010704054003400400038030201519215110048040c004440c040c0c0d50341c2004200a00c403038101c642c012603d0001203050303881c104000d44058107403501c0308000b540554060703080c0c04c0003075107000903c4244800350040da4130300070303c50408615003410598218125030b01d04030701901660401c002185450f2041d503092041d40080700c1600c0d05401c01c4e250003500e0302c00070301c020340f44c0b44903100ca400291b0010740708440c032001d0b05803100d90485044080b94200c051005000784c00c440140e42e48810f0035204e0f401a03510040c8504040c0800400910607402240d0040c0c1002c242e0342441c1c0300510041c0d80000481e500211f40b03092005542c1c1c0d6031800340e062a01c03c00e40141c800030031031131004204080d50555006003101c170300e400d001c90ba1725024464824041290ba80d0303407650200704115003650003a100c1400c000c1c00340001103000c0d0f803500070401c07614100620500d0692544200345041c42403881d000340c0342c40443d201420f0010216110507001912100d4458480c0d540e406100c801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 283476987 1250 283475737 283475741
    0x150c0206130308070c140d140f030d060513021206061c060f150f1d03030d06080f070f050f01120e100b010e03060402151308010e03091e150c01 63
    0x1a00e001510300c01809502d0745000c00302500300900489812440040104034a24813801c01e11181d400500748500e078268a0f01c03424844401c040c2200268064000d110103103000034001000c0000d848440810064988402e100c60190700c000700710311762481800b0035000e54450000294011301e08884841d01d80082290707401014001c0b42614528524181000602d21004450901100c80038540000c0c03612070854113658507900b0700c0300d110002c0d9995000c52484040324010030500000175040340c2c20508290300d11400c96045401000c0d51741e20034080041001d50070003042c0b000e0b2100c207070303000c0205180c4004640748982d00c1580c0c41c10310119105003e00090307280e019241161002d8202c8020480d0381c80c000b8001c01d040400d40b400149014051340d10b07400c00207aa14041c9901810004015403030202d42ca02e250803944a200b200e4051890025000d1824003580d5540d14604004d0b581c1c90a0600400bc00c8a0488200900035003048501e4401e981e140c0e00003000304607034100c074540d0b03d110f5100000c1c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 283478237 1250 283476987 283476997
    0x312050a14120703060b03040c150507060203090f0f16180230061507120314041a0f06030606041d010c050c010c02010209060a120b1203180109150c0206 67
    0x1e41103800304000701c000b48081d0180f806505140c504129070750b1104611010b602c400c6401500001008004024181d02010150b60001441c5001c6082c03003c1c43d40c420080c1e0b0301c10790358000c0301c1d4022400303202040300a00050b04610944001032040c2c0d01c643e5520b50710411188211000d800c52201100394242c0d00b501100c0e60030380c0c0b0300810701c503a00d200398804c00c0030400c45c40c5002c480302c0300c100000d415081103c5049500403400e04641d06000c0550ba03402d0301401662502d00400da1101e601d070103129895400140034a1081c2d00c00000450488030312560040001c003801542c000100c18040726440108800d0703000901a900460310401070590060189000300018515601e0003440c03c04107648440a000c0300305c0b2340b1000b88220900e03184100d0a034055445650342c000c1c41040003080403070060040400e048401c1d0b40104442c069000001c11640d0f08840201d19034000041c3c0704404150f0110400a002d8242003186c1c1c03240c1841d500c20411400c001c07180c400d01c08104400810344d900c03201659 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 283479487 1250 283478237 283478267
    0x70608060105210a240b1e03010f06021504020d151122090203071b110405040303021c140c0a1106070f0908010612061e050a0b10090312050a 62
    0x42c0d01007004007040f03011041d003210b4005200d440c0034540f840b019105069003001e0200315403140b00303ca0030300d403101040340d11020032481c00010144c9030500d400c0540c0040c500a003492501313006142e140600185c148450300300c110300070780140803c1100580d10740825055080d04158990b60400c01d04000d00004c0030020000c0321202804982d07192a0018040a0301201c1e200100c0220420703595441d0005a01094403414003144012651560402101000c01c40c92405031111550700c419003408a4100d9000396400d40c002900082c03454420014252008002d024505041200955a400c0c00104140140400f9900c07880040c2c2d00100620601001040309114025500300382070220020f04051340c1c00c680328020541c1c0400020f54540306224503000ca440351941b000c4000704560724400200280c011110300c06440d241000c0021650388592071180d050a4000502011a18200304020781c6082c403510030000c00c3c0100713000089600d80017511030101070030590f40b2030600700b02c141d40400000301070b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 283480737 1250 283479487 283479517
    0x70e09031204032c0a0509010e0f040201050d110a08010b07020a090b060405150306010314010b0a030b01050418050a1b020318040902060708040f12020d030f020111040b07020918070608060105 84
    0x140c4480004d008000000003144c03e4041c007030ba180705000702da0a00b4400c1070003003400e5000103440c0510003500d042d402807052420b1894101c401603040c00b15900c207015a603030030344085a02c58080d41c0010400303025060444405040c58041e03400140b82441314003980440b40e44540200f01c83d61100b0702a18050407000b0100324901c01c40c030301e5541854000702c1c0ca99000078182032000403003080d41000141038401a0300003c0c504042000d0940140006100b0b50b41000b00400000525440031082110318084aa4012170981011003280003541c2c403107100001c4d0828040300d90003481c1d400108852440a0840442c140600310200060003080780d070001a4219500180710410050054020300548007613303580c0c4400d503100c09040032480040704000303402c0740c0f40d0440c1d070010900070048030840400f94400070516000380c42044034550070542c050205040c022445908500d013002015a202060303032000904c0c0922110210ba4402862066005100c2d142004c078030300764031075021075048004070442 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 283481987 1250 283480737 283480787
    0x305031e160602190305070207061107090212160201020901052a0316050601060e090609190204060c061425031b080405150702071e081e070e0903120403 67
    0x110b00c002e94030096000d00c1c0000a0043d1000042c003d104040c022540d030750041442c2d0b070800000361200c4202c1c0b4032121722489070010019138500280020f100f02980c0c1c00a140c01c45c100f07203001c1210507406405903400c1d64014001200941da0000565101000c00c0f9064224900545547c1043c8001e83c800e0961500000500910742103200c0840c443c0341d4400c81c00c50f920350b80e0380c0a080300c3d070307420701c1c40381650043c0c049001c10954540340e119190412504031708041100c0495601d00101d0740320740d1000c008030340c00700003500a004041c461002282a40d06182203e4544031040100040c460011011803c1e500c00318000c1c1903200380e000c0004c1c40d4005000c01140710602c0d0000c0d051102c1141c00f2a5103118041c0d02000c4020350016982c026a000d03002440c00e01c0c14280380c01c010449c1e90311103000c1c640c62880001800b03042000603403030482003c504460300100304403403e4180b44451300310003440401d040c00c0c8002c522000046440000104c2002096511240b6040305c0c0d1a40280410b8600c000740f40d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 283483237 1250 283481987 283481993
    0x21309020d090b0f010602030405040207020f101806030204080712031704031806020c0904031101150e04060e03030c0d0903030609050a0605040b0102010c050306040e0a0b100e01050a0305031e16 85
    0x10155503101c3c054044440707140d68119940300c180209002e80d100580080c0010400b0741020780180641501c001c00701c541c1d48140030045000107100e19407950000309500b94622403200350802032405442d1520b03081d0318050400c610243d803046103115214000d2242c10b0000c09241c4a40c804018a1041040c1c0c0c81c11070629040013403c2c144003004001103030320700c0e07540040e00394000200c40b00070070005043c52000381c1d62601d0940d985404641030600c43c0d522211a8028940741f402203001410b41e4200b284800e0410782407000c200c0d2131403481c10f8010381c4104103002681c031441c019a242607001d81e8011510407030a02d0114082c0c4025480209154100010f01841d00d0040d0014400d403803083d5802c0118000c000012820b03604a00660000305400b0808036020342840c0c0c0002e01c0124007801111000c6500c0d43e50222003080884441005080c2c0c1c00c014031110204201003801410101e4804203124290b071a001c0e00e034818500700710401c4010403001c0c00445094003e43d41403904850345402d400310141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 283484487 1250 283483237 283483241
    0x7030917040503010f05061c081905071b06091a120a0e0f01021305330301060305070203130e0702070305100c0e0a080705010c08090406060c030e03150703021309020d 73
    0xc0a424070a500b044100c1c10380340c05506c241445000028540020080c460b070308500003064603802602c80c64000c1080510007224040b1400c06120f40ba41d800c1d07a64860360400018210991102901c20003400b8010403980d4be22414000c10740d6200c0e050100029188500c40086104266840c020300c04044100500004103901801004101c1019514008010400e00b401c078490303081170b20f04009135854248a281400c02200b11484c0c808205800503030442034501d0349054003462604c0604000000520150b0f900d8081c203504601d0703500080d4101603d071403640322041e01500400d9a00804803001810040c800c0289c03800071034200003581c9490b020008210040c01c4440880d00104201441c00740081c00c05040b50030880d03d242008d0014075040c5801159251000403041d03030340207002d2190039400d5841e4400d02c00100349a0300c42e01d400317001614001e0a0003060741c1c0a40e22a4101030490380406a400d0311940d441a1a4900169078200401102e00079280641016903124804903421003c080c0903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 283485737 1250 283484487 283484489
    0x608070c0b01030b1e0601050307030c030605040204030c29030a0902032103010603060e0114040543110a0308092505041116081312030f32030703091704 67
    0x40303250f140e2606408440522014019074031b0b82e000a1042001500c4248682d0010207002118034010a8681e942d60004081c0c0e042900b041d40c8050000d6070403c40e146400101044400119491000829007017800104a0000400c0518119142e400c80c0c0300b1540c061080544903000b90615a9901c3c109108441c1150024040c50300480d1030400d011641a100d151924101c42e101812005804541c5013800061310002e0192101d4440340c0421000e82415220346404040d800519100529400c2ca500c21758100940c3c4034000780044017030740f2114100007040810140d601401c00c1703456900c441460b40d00c0c001c940051207041c0310328090341c81030030070f040d102c2c01045440486060000612000c000042442642803020307007012071081c1c0300e00150200000d829505140c403804e110700c82d9124070719000380305502011400241c54020810085030409202003103001360200c0c80079001e00e2401c19010400c84a00b011070601000300010300c400b4400c0d041075403220b6001442c1c12a0b0b07500b0304078601103600f003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 283486987 1250 283485737 283485751
    0x52502010b04060801060b03191e0207020a060906050d1505030d0504150905090f10031a190b1c23061005030d0801140a0503070605040306060e040c0608070c0b01030b 73
    0x106040004c04100502811043e5214441283e140d51035088140d5240c172504400400317025124048080c2409441e0103003003000080c01d401507540c0029104000038051706402c241d00b401015001449840e80c4001524601003064800042e0000000320710052072242e030388000d5140c030072400b8101c05a5403040103030044442e0f10307650440000c10a203040e01e0300d80381402281d40109a900008140d09241c240281d0825a8000b18171107058503611fa0a16107040011522002e0b0b01003028459140c0340300408544c05c190340281080f91285842c000398a290600d40ea42050110b14103c4000344803d001345100c1223500884242c410381540c2c4d260b9a200c2c80112210004802c5125000490b42008511031040c0000c555451065030b09000c507550201400114441c3c210200080105142c1c40400c0118054111a02c1e0f15032160300e94640007040e07640c0c0703401a462070200142804000b030005c515150649041d402e1600c81659070f40012071b10590300007809448429440000810b0044021210b4000d0342 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 283488237 1250 283486987 283486991
    0x3030c11190204050c0c03160c0f1212080601021c050409050f040c080c030601090903051e0c1b1e1207031203050a05040b1803070510020c0c030f0709052502010b04 72
    0x91080e00c5542580503442a50107650408c00c504400210406170303502425218038a00140180c4800f10004401e516422031048081144070f100c0c10f0040c400c2a13002e60130000e18020348180b1303001c2d000175120555035680c003194a540781c6008158078000e0342650080c11821804100c1403910340d03a09081041e003a20107840f01c541c44038020840b420701003000452101e015008080c16480c0c4000800104200c0c10b00760b00f0000203024820207030602c40c580070708840640c0d091940310011a100e680c105030b0340081c5407520b04c1102c0b00e01c5005071a0a5500d00c001e80d40061aa6180d0259001250411105818180003409120008402c01c00d01c6011005c0c06400340d0b50400a0380e0703900c000101140d1082e900900454003000025440c91820505008101606020b503414501c043c2d8889261220485113003060325004180450090000c00000388da0740030840050803008c000000043c0c495003507004a12105840e040058001c0e110004049a55038064403229030622aa035002402403100d030210350300c60f074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 283489487 1250 283488237 283488241
    0xd0606020a110d030e06030f040528080a0207180c1407050c10051306082d0a090c0315020307110c03070905040516060909062103030c1119020405 64
    0x500c0040c1c21141c507580040101c1d01d401a82080024907220880102c0811000d0341c0210550303201e19000d035004e401c4181e00d200392403c0074a0a54100814140d614400442d01400d40c031050700750014850700250030809042da15070b041d0f88101d040500c039030400000c1d001428161a06080140e1107040f00d294240d8605440d820914a01e820500c035240002c2c20743c3d440580c4035081407420841e02c01d0b0029040c00c0c0340b0319192044070710000c20103e650140002c82c2101080080d00300440c000c51140804072800511840c0c0c008010345440103000c2d0404651907540d411007802c004200b0000d8000c5c64020300b50724281001009502e02a40c421124800080c0ca80ca409404880f4006140c1c0d00c0e075031000700603004031400c240c07900c8004c00c8014010340300c42c030070a07051290ba54950345030385000c0c103200d40d50742c0f80303080c24000d05006642c226030104072816006560503c000441c25190326070381d5810714001c2040584446c04840418000d0950504c40c0181c1c0200c05801d001d0440e110841842a03900748103171f03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 283490737 1250 283489487 283489499
    0x20901032303030402211f0b040e1504030f2304140109030506160507020603040b040b0f070c020f040f0e010b1008040c06050c0f03040e0a18030c081b0307080d06 71
    0x64001034500035088200040060f00c2900c03006d00d2020049035205c00c48139151060840190807102900a291406943c8d04800865050600426203452584801410b8240c402da0b141c1d91010401000034040021034100301003400c0c4207068000048100c41800d0091303001d80e408424466002c2e1007441c404220200c201082540110305031003c6a801c00045e005541d1242c2c0031101091400103910204601084002d00607544c484c0918052801000b034080d02e46024500842002800f03840500600c078080104860540d1102054840390b9050307500500040304200418080c08129820700411800c065003c64251815842146031031811680608070491049003074074804815070f0302900304d841c90681070140d107003d01e00400c5400d01150484524a039200d0b241411a001600004000c0b520401804845861400f8507052003003c080c0c03010301e40c001e558000e0921480280d0050041d9400714280a66629080d851016443c040c41070729507500103483c1c030403090b6000724014a0901c1ca070503004905 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 283491987 1250 283490737 283490743
    0x50601020c0102120d0908070b04060507081b0a0302091314010603020a020c06030402060c07150806100c0b250e090a06181a0a030812010611280209010323 68
    0x8407074103070084c00500c0f11020030040c0503071181c0e0a9aa02507210100e01d0002070751000201602d40c02013509c510315041910f4490260f07440030b001c0608000c8064240b02c13800300040d8a0805008170344030072075a5041d4504064000e401514172560740034410b0111107039200744e01e422915200b80c850b030f0303094103581e00c8d40019405c07030051f140c802c801648028580209410108010741d0007a00060000d8204500111aa0b191041c26005441e03100c0d01565041d00154001128030b4100c401100e0b211598a070f0354100900303415002130003030400e85042003c10107006000304c1c4803840c400031160402c41000c2c00030b009441c4100085002e40070302e2410000070b103407010718401c0030103540d1f000404044032103404118402038072980d500002c0b08000394912904a0b9200c90311301004501c540041912525001c15607101200141d01c204103000c9981c04070138945101203070742601c00411a40c8030792648504114510b1003903820302e000350010702c08130021060211500c0e07042e05600c02840d00c0302c101d0303006804072a1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 283493237 1250 283491987 283492003
    0x602030109150b030c0d2a0207090f0c05090103051003140a030e0402070b040210050409020d0b010e09060a060507050c040f1401140916230c0c03160b1e07050d0305060102 75
    0x16400900c01201b01800c1c94009280714807810140c8014004143d440400304a80d204c00700e40075038402c030020000803400b40514024030007030030320030405481c050b28080c10701c1c0705200200f0b0416940d040002c00d509001210340020f0f58110141c01162542c5d023445540e18038002c20243c0116036507010782100380c98035000f05c40c0da17180e000510f003200da10340307034280000390f07006582802c144041070001140101407032000c0c041004011902007964600304d40050207000c440700c0c1c0603000d54140020020b150326030001d500d046032450310f001940d0301c58a00f05030381000c501c031040c0c950041c00c0c00b45410325001a904103268a5008400044050740d96003000c0c4a62003200494176003110500001400140781001035103900c01e0385061204c1035941e4460120314031700c08101c1d688a4401c021070380d00192202088dd0030f8200b0030503001442c1403a20980040350800540c0b15180811400090110101e2030711080543c840069810190300d8003e1031500341d444180c003007021000240381034001500c96200044081e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 283494487 1250 283493237 283493251
    0x516051212090d1505150108090d12090b010905010501090b040f0e070306031a01030b07030c05090f0a0f030f0b070302030105090a0b0120100507050a0504150306030602030109150b03 80
    0x4400751102500000c03500000c0480740d00058041030302020842c2070742c09080100750214001070520701100f1005503d0084180b03107040180c100c040140c1c00d540001d8404206d9000c0c1824507001581084a01c042c0a400c5001464800b00c08000a0908001d17040310b030585100340ca44a4205440c1c1c210510701e8092031140d0380e60803401020801c060140d580b0b12035000b854506c1c01249007901ca032516594400c2c0c128414602a660703000400a100240c0715240c4c02041c03501e4140141c00807c50300415501800490600c104800040122107560701c0b03104400800300142440074139a070b0b03030070203a0103845c0e4030788155100000d03100010040c0f4401c2c42228181c41c40100308071080e845410b080380044c141e280d1424103004a004030701001d510381d000c03000301444041000b010107a42060200c000d88a005c1d0106081c00b4081c0207480f074213038205080d90180c8510711100512541c0b03924045016091075230000d00014070000011622030306603084a80c005515944600d40c43e270340e5030050710f100e2004035061 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 283495737 1250 283494487 283494493
    0x409022101080f0d030b0d080f07061109031b0301060e2d0708040303180206180111241f060c0506060306060a150c080307080612030a140318070305160512 68
    0x1418240d8007070b9000c1624018003502e4410710a0f4595100c18903035003c0d5064180c4980007044ac0702c2000f0a80c080d00400e4184041d4140c286010300c0c0102c4d507182da180d090241c6207002c00c500041c0c6601c1c254407420080c050120b4103501820010607170301b8815a02c1c081e2014841161080c11010310b2404500b40c0207810300e03030702e04029645a84089006001da0300e107200e64801e943c0c02d0000035030354030760207043d0121442024081030880d44001400b848002c00c24801c554000300680070042c000c2d1012841c0b89681c80786510740c0c0b9a1110410721040910303150303d00740f05002120110780558004999551540710300110303101e50303e814080680e500001c0392690303440a50b10344280018041d5800024400c40b6609005e500c9035100c0d9201c00b2107030800c42c0c07038000160003901000124689842c0141111030344002640c94140c1c8508010013040c3c4190129020603030000100c0e8800246140b421204820001a202c496880e41340450b214815080b01074041d000c9400c000c00c15103000140054006050001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 283496987 1250 283495737 283495753
    0x624050a0b0304051b18010e071b050304030f02010504080703030503010504111801030c030e0105040807170309100c1103030a0501030303050a060f0302130b06030109020d060e04020d0201140409022101080f 90
    0x2842c240310900b4444c2035040b5501500032003860b00000841c0b1f010789140c103850310b20303480d00150040c200842c402d180c0c84450105603c41c000714001004403019603412004034001c44002d400142e40c0c510a6030710030505072162600c00014160701c074003d10305a401c01c640a1152211000b4807040354094088600e46180d440d0410526560003540720004100301785c00c2c04281d207840d130240307136007101c3c0111802d555542000403d40b041060004030b020303c03420201100c908606110715500e41d5419600f45407000907a84201403100c080c0a07140da42120702c45041141d0b07076813601c200400040c04003803001700d01007410080031682440c0540500003d503542c0046a00c955851034080168400c4c44410783d0303045079a181c001d1402ca88846000f507020307144403038025a450032402031f60402c44005500c111003a00301c41c002e004c0165600208250036540900c0c107100c841d03099507002d104520032139020355525407000803030b0364036040e049900007242915200c210341d650b079907612840e40f90306c9a8000060b1035040160 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 283498237 1250 283496987 283497013
    0x3120d050a090b3603070c090e0a08030919151d0a031805040e0a0b06030d050301030b1905070f08011203050304120c0516080115051c0624050a0b030405 67
    0x980c081e8285070300096051310405031245101030300c1c0c0504036281da0000a510802c1c0040c0325100401800c104a003082000c64460b04207031101f074040d500411451000010604150081250940e100030810040194000e00d1411900110262003801c5900782080c0500400c0b8104480d009061a040b4002c6e2502603901d0381c08540300b607a01020001190038001002c80c240d211031241001b04800301c002030001a02318207007070072040c40c020809403081d44039040d105000b40d848015641160340c007000c0e403240703600c605482c141c2109910342d441a505203414100b0030000d50103440001300b07400d941c0700c1c520a0390b224090164600741341c19001e008540200080b0300000c5200c10320b400c2450440c0fa00e0503028000c0e80d20b15041c020480103511240f10004003c3c40110000e10900386c03449108600d8407801c51501c00491400d0340d8888500709920010312054040c00311030b401143c4040502003905c1507464a2120769441c802e40c1e4041d00d4015940c803000400c0c0b401580c82101e0040360004014418425460 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 283499487 1250 283498237 283498261
    0x6050f040906060e040302061806010b0f1803060c180f0303031305070e0403020109170a0c1118010b04030308060d080d05180a060506010f021902040207020f03120d050a090b 76
    0x14012241e5a9a40400251441051044c54003403442907002e0b0605080c20101c03101406800090800039400000c01000110844d10440c2c50420042c581760b80c8440c9140309560b481c880740303001140c0502510781046031a510403402002120066042194051019400e10410441010b08550103174020070228102d51b809861030b00006108000b2546c582e0b4a0b160344044000d81034404402607074451701010100501c01000c0406983d5415005060603507209006083d901a944054112551528000c85503240c0034032845401e040103e4004040d6950001c60312140c2c098442a000207120344003050725894400c0c0c1030f0740110b40000c40d190814047c100307a5001094041c0960043c01c60a1040841000080c80628282801048005030a180500002d064480c82c1602807045402c4605281d415410907400000c15940540740184c81340018404901030300031156030a03a05105400050340746590300b0004100320848114140100d481d1a501001955110800200030320611000a0f09030803840d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 283500737 1250 283499487 283499501
    0xd060212160302130504052a0904050f04050a02010810050d080711240906040320041a060d0e0c0604080a0501060608160509040906020c01060e0906010303091710020f031906050f04 79
    0x100d0130300360f008801052040701003c1042d080c8c8103060004640d440c52860107110b495480b40c1d10f010a00d070b0b207160079a01c0546078200480000d040c00468400326059221018181c0003404015010807100c10340c0e0b040003511600580c20441c2c0720010b001810a15060607000e4500d03070512450310641030308804d001c8401d15004242c90b46c4c6c10203810b2000001060f0400034104683c0d00700c0c903115154462a000303120075614503008040b001c611100c83d001d0140c07140c40882d807171010b071010300082034580d0701030343c50928490300e00c8180e10000c08200880c01100124240038014494002004120755030301c41556020340c121207a000d48040302080d010311074042c80003018034010050000400883d555919802c0342c204048200e0140e5440c48103100400041b0501900881c04600a101640c510307078008043c500b00b40a0b40e4801d01c001c40724130700030281c02c2204980686016034155107a19443c44c800500b5001242d04020038403101c031702c80c0800403281c0f181e0f50075603801900f222a407c00076000d11010300341d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 283501987 1250 283500737 283500751
    0x51015110c030105010303030609050a061512060308120f09010c050403060c021e030a020d05030f01140a0b0406050a090504150506130e09010e061806010e04020d06021216030213050405 81
    0x101503103100720395000e201e00c034080c0d403107500e0001e45542411449000c44200424004074185800002c0c468a40701021040400d0910711b01402c03109040c5004101074000d03580018010600400c040c1001c2c0510082e95120300110f03500c000040c0d569240f00b82c26150366075502da0102d07104100c188080741154101c0c900c1202240111186000340c10400c3c580c0054084802d4206d41003c40c00c001080d82c1170004070840140c0b0b161040c11400c020b42180700c82138062190900341c04c0300b030321100041c1c1c407080403090040620358440c0f03403103d9462801600d07030b5100540e000c00049000d0400b00d0309103042e101e001800050403110035003403030030f25080c4107280d4080301703806603140c001c000b0025010000c0250144100f0490001284001d1081c820501e0500c000e009410794100701056008040000213120781151402040070000b503c550000c201181400c1402410316030000035411110640d9000c420700030140180300c21a040c2107420201e08074010182030707440401042a04006a151682025400040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 283503237 1250 283501987 283501993
    0x290109150e0a06060f031116020d080d0204030303051305030315030c0409081c0b1c1707060c0e040203160518040507080106030b0906010c03080723040905101511 71
    0x1d164400d00c040d0550890b20036903025203944042c030129511658403121491182801e00c80040c0d0141021000d0066250310911205440d000780155039503007864980e000d130450465641d849103490038001a5019000940219003813601250000b02a0383e01200840e0700b08000d5802e5444030aa80a00d0680f040005903051191a05140003690b441c4a4030001c240b180000702c2e5034202d4050034185a030b03514041e03030b100985030200b01c1200d92526101d03908042e061090012101d900da1070910865035600318144e51040001ca075840420025074020210031495884188186030071004100692004460b15481d018003c42c01c0b11101e405000a08900106581c25404081c80440814110f990480c0c1c1c200020381c0349001040140d416208000d112007043c0c1d425501da160200010348101002e1600600304010304002400e030a125a221100c1c215110084222480315050020200e4000c3d0040300b00691400000c5031300010415860341c1200c1c2c0b0030240c1c0000c512418820744003c059070b083d203070340340c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 283504487 1250 283503237 283503239
    0x20d0e211014060607050a080c03160606080609010c050405010c021503090c01090b0a0806090a0905070305060105030f0114160c080c0a0606090c02120d090209011229010915 76
    0x28090040e100030000078603001505841040b075403201c210300a04007502800d001c02000e004644045106441981c2102d006503841c6440c18641e80b8502c900d030a4400451807441c405810030070350741c11860480d40414201c0d1542c1c0c4612070118200d598031340c042ca02013002003108122a5003d04241e80c6001d000404040c0c404108440842e90303a4011500d98005070803125440b880356800c441010060170105860034108000041e002c0c0c01e07420007070480c51007007040200088400025800c040c401d140d05c070040e030741e04550f40d20340281c2d6042e007070064a101e80505c130500207103881c0520072502000c00e8940164007607251022122460406800050208858120010042102c05004100101c0c0c220028109405070b0304050b0102d81194000d03600c000d041094000a4070760008034031001c0309030f40100e55a1040800a104001d09084c103000b0741094158000041d80040200c6848515007c1d40600131449400c041001c0c1c0d89640c0c4034040101c4043d40c0045c455404640d01040700e50900300201d02c006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 283505737 1250 283504487 283504549
    0x703141005041d1b0f0607050d020601051804080307030213080604050706080f061009120305120f060108040f0f0614190b0a031401020d090b0f07020d0e 67
    0x400216030001529180010410807400c1a2040041d00310303180b90440041904105081c4d00c0709030601d420440c4003050f407540c03111940d40e0516890030b80d0f00100388903654911481c1c010349842815400310094040c0c5000051282010400c4c0c0040c4c403401c1d00c90a4196440d5030724902250400b5005400301507084c0301842218000c03020300030141c88210001d110354500761406524001d80e076007124041001560078000446105200944c1082049545102c1c40810600849031080c0b00c3d03011240d046a40c2c00010103040d000001003107480c2d5003050300c958035991815142d00c080000e4a05030300181340d4100140209a29040c00c03242d041c0314203c01c5280313403416140c0209640f20a44440c0d0340c601131105001c0b800042036110b80c407011005c3c100344284510a8001200041d80b03100141c0701c203114403030000858000703604130342003d410820200700000f030a05055941c210304440c003c880030884004680300b41d0001030220700b5a0043d41d1030544418a0340103020804104214885580107500c00303003004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 283506987 1250 283505737 283505771
    0xd0803040c031e120516061e0c0314090a0c050918060a0501050906010804050d0e190602070503100b1003090503160516050108091905030c060c070c091e050703 70
    0x10010b40300361007051100c92802e010b051010080c212505105c401c110060b2144030103140c6030110394101c6000141a2100c002c1c000d46042c09408203082d092400c40c10303550741d60b019488004054041d500200003075844010299407000c2030480900410040c5004100d94600f008406601458407201c10400454030b029551400c60180d480f40c07405500d0f400140403900744000c40c940e00c4103003481d1501181c1040c7e10748035225080740c11042e0800c600755041c0c4100f0b4490706492200780c44825414a02c0c96980c1400a445420300c0c00350328030a010b10320490a1360000e80c010103088240081066601804240c0f094004101d15081150300c0c2c0030600008202c1c1c0210107250340c51a0042010b455920707607032000c8014690741030308214140000035060182c5072200181209802c150340542d0f074040c21050901903c0c501400e5201c86151140c881003001c011010005002d6461040c440300b100c2c99141c0c072220080c1d405401c01516503001d4880ea914541c289500f0890300804d2900300050320b01c0407401d082032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 283508237 1250 283506987 283507013
    0x30f0e0f0601030b090a06090c03030806090610050d0b0d1a01120507140109121b0f030507050904030905031c090f050303030a110c0109060524091614030f15060301050d0803040c03 79
    0x49c8042d0460001c0050542041c3c0e076690048044510107403900e04180007448030854606070300204400802c20076541e820543c000050060001d10b80e400e104c10718604201801221604d160381c0b5400c00c03000244030f0110106102c05a680300024180c4a802d00e1950a1345007007c4403810b0411420580000d140d15040b654084031500802010000210b0b401c42c491a46e00e09501c43e907070901e9165401c00c0030900c081008000e0343d030204d44500c1580c46a0600b102e01406c41d8000940c14010070340300c084414500000d00300d4490380398859a402d6903440d00c000e03006055a20403142c1580080002810000d041c0d0b22800b0212204032581c1d040902e1940380c40c0c00c40720318240071280741e036640701071000007520360030449450701c2c111200054510004021541644010f086510614400d440310745003a4080d110f0395000360100181180c0b01d1501401162080701c00340e8606143d20003603c10381c100f40c10142c080728161080500741400c003107030039130703030006075500052090352580d03c40c14000c400203100d092004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 283509487 1250 283508237 283508243
    0x21513060507050c061015121506082d131703070201020a120b0a0605030a0603122007061407141006081203010317090d0b0403030f0e0f0601030b090a0609 68
    0x1035218013030b850300746150010140401c80c1046512208000314400f81d010701d0b01c0c9a900e03180c60446000b00660280103428400305074950389046090203e640b6510455451140001c0320034610300c0002d01000f560800c104140500b42c1244400008441417420003064441512519140250403203040c24600c0c1904159401d400503500060401c0f007883c0c2c018249021006101ea04001c0e00034001c0004620503140c3c402c2805104010000880001c2e0a84c420341c0115007004c14171503004000f900051010b09640c9842c1c48004a510958111840004071300003030340c01645440c0409400c6404d40c1e500c80d00440030844481c0c000319902d607a12003003441a4140d0151030840400c250f23040414060500444407641c40d80f00106200410216850b00a44103101480000060391110b00d43c0120b500300401d100d029103000080b101707100c20594103610a4a540c60581404c00246080300a510303101c10036544c010019500100c014004109200002a00030240d1f2080300c05c401d202d940d600d82a80d981c0401a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 283510737 1250 283509487 283509497
    0x10c08091806130e06070f020708060405010204090509030304050c0114090324010e0705090f04180b01030506101202130608060403021f0507120b19090608010c030903021513060507 79
    0x841020f0a0480110f06102e60b5141e042c00182558448a56100401040c000030020f0703c5141111140c001e00040010b4510002070320307036138501820118040d600500c101000f042c50000000c4001c240441500c0c041c5038403001405801d40c0d9100112409500c81050b0300e82030000b041003035486d540812000000c091030303074031400e5100e580181f080c4802c1016801b5148140340c100800c52000e50040032035560480c122901084d400464001c5801054280e0140201c40001038070705c414412000316480c100d900c100100c82855550f001d22090801d06441480b00307002022103050010f1902441d9183c0c0d050802c8000220b040c0c6d2010010316043e8269010340242c1c1203003072204107140a003200c155004004a0341400740d82482c1000030540d0745401d01d0780c003007160345040c40300040e42e03501038a035400c65901103013404683e16519040c1c010005845801000c2d8600401800f4140c000d0161144c3d1315090740141144d07040c58941044d902200402c69098032092207403280000f06284941030290b4125a54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 283511987 1250 283510737 283510741
    0x3060103090816060e0f010e0601180f020307081f0605070b0603011103040b04060501091406060a09150203090a0801090209130507050301090803040201020f060c041e0b0708070c060504050906010c080918 89
    0x950b814a040902010021f904180b20352039214400282c040c111442103800071502650b070801c00f030003041e030089403040c1ca40c0008107018019a010880318010400b081d00d2866a541d21307032000c501c03203141d0710486011030418044074020501c08002d20b0f0340208054001308042001c00300b01a601c0c1d00c2203400f07c503000d5411083c00113014052103540e01402c40f5440c10040c0500c10000c0707509a84000700801d1040c40005001e200c4a40314103010401412005e20000d0689941c04020351640c1005947ca80184014000082d240a05025450115030081c00f9061103031a4000c0a00350307083e4a010955452003208000526502d0920412183c035004064807601d17070400b03200080c142001190103058070b40c4120244203014442c4812102203d4081d03d040400806400c808424100346912000060101048060612601000900b03580d0710545501448503203414050f1203d01983c00f900340c01c12200070004050b94018500c25074464012501c243c1022041000550254203024810800040e4142 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 283513237 1250 283511987 283512011
    0x81f1107050604210c150902180106141c02070302190309090605010c11040506030a0212070f0519090504150218041d03160c0f030c24050306010309081606 68
    0x7401c4602c202100c1920100443c40301401800e0149901d0050300e01c3c035180d44011006c55260340030180d055070140c0402c0c08149a4200c00d18410f5091003104085419504084000105034013120b090035015501003500a44552124000350009401201944122060380b42000f040b400d6041d0024481c1e5181150a0702b0600f0f044160707522503104a060102c41c0b420240010320f04408440200c8050b90005015660440064900054500003941085421020303a00b502c0d00820240141d032005e50480f0115035030394080c401200c038120319120034040d050905000c0c03c071150300300302e4000b80506071100041914007515402c99200d0410070160403001e203401d401906043c001d0329030b500c40c5181c41e45041c444035040f094507449040c1d0300c0840001000c400e041003101c060459006018008139414400da03c07454070f40e000ba04140541340b030002e2003c3e00c1c2640c401001501150040d4a640c1d02410f58443c1c00043d006010880340840d001041400b0412070b000d241d8540c0c072000c030701a11010501050b050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 283514487 1250 283513237 283513253
    0xc010c0f0e1012020910050d050709031203020304030e0406080c0f190b0c010e010e06100519090b010201091e0b060604030b0c0703170403030c08090601081f1107050604 74
    0x605418003100301ca11030016070364941401c0c11982d160030300e142154609030000c8002d209005c850b551012858030320a07550741c1d002010744001050b00c8030411142d120001c0a03103035452148401890074608820103d04a84240c0145411a01ca81440c0460001c130800203002c0c1c03038140e080700040e0744c4500140740c15851315030b640f03000d80c09050703408108480400340d005400fa40c0e80d0054807902d460020382602000000d6004100c0b01e84218000c0101420402c6459220801a6800c80088800f402c01299034900140c000441d100c00064002c81d01e03242c00d24940150a81070090750544d5601e9001d240410301e4107407100c0040261718000c00caa00031500d894401980082c00c80c42c0100d80501042c0000b0f0400411250070100310320195480e07003543c0c50f00301d0344942c0194611401d100e04030309002c20141c243e081104122115201d48213181d0301c0b161401e907149003d03c1203080c154060501c501c94801c401d034500741441c10601011461120240070358a041c0e009110480359a407012040000340034500f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 283515737 1250 283514487 283514507
    0x1205030910090f1410030c12021804050109060302090108011434200c06040b0f071b1a0a09170f011508010e07030b01030b15120a170702011707030608030c010c 70
    0x10741420081050007c400400b00f0405005001e240c43d030006545440103002d800104a01c680140140141c3d07131520f5108024000324031049000e040504008a03000f03030306006c2c0e82200c0b026581ca03a0695130303a02100c0c441600d02038994400c400382d0b0145400440310204040549881e0070344619484421005510035403c0c1c01411600a5410004146d01d00c0c1d0b4551089a0850b070311080c48a0300d400a21172032210384e114000000741600082d08800744003e50883c2800100d030000c1c40806800125102c04101d10b20596040c81c000aa01640c07d221040d42c502d00d45008080000803960502d04401400303085442014624a0b0700d0000c41041040040034081e52800f4614200541542e03455503644524200c010300004110440f030100091286c11005c041e142c625500404c02008005002105900c0344405502a1b40c2c0c44095818000c5501d030040c200c500b072070b9040c0c0d10020301c0751054410902601d0040d007031004140e1144400600254108041c0008081540002030420401035000c4c041c8910 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 283516987 1250 283515737 283515769
    0x5061516020108150901030f03031107050a020103111606052503050906010f030c0b0d11070b0601030b120703030804020315010806180610050d1b1409011205030910090f14 75
    0x140044c1802922075038481811643e10210090901c009441e003175004d01458903c2c9180080f0200310390090101c0004c0c0360042e00d000ba01c0400100d00c104581c4002c51040700e40681d204a01007070a8000181503900982e40150100c246071050b5000c02d82003502800c0c401100c400181d02d600900c04000c206008190042850802d036410303051551351079071004440c0b44148050303080086460300d641c0c421074112507440948203030415030358040c80c54092210b05007502c00e28002480c041d1002190b0030310529582e00c15680074003c207421840e5079411030740b8440081040781c1501603140c4041e18000000145806031a541d80035081902d07160141c07154411180e54400001e0344800c09118003410203040e22009d98000350b92a21001801e82400d080504640d00d03096a5080111800035580460391803182c03403000122404074160341c0e90a08000380300f0500102604542081050004a1414030b880d07025080e06801c1020b1a140c1da0682284125503a034030160f60120000011203a0780781100a10480e088 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 283518237 1250 283516987 283517011
    0x20a060203010611074e0308071b11121e0a0b07030b061812070312030f0615030b0d081c05180c01120f02030a061d0f060405061516020108 61
    0xb01a45182800303000c0f41002c9090b1050701d1031581c16001c003450b900030705001020030318000c00030f0507e40101009822140c1e1000958039004074403170300d45a0554411126001000d030f403601c8910381c040044140c1c1c1d058582d505032003400b00030001610400030204092615401400da038203100d00741006544401000350b82091300d8860342055503030b1500300740c90040031061082c40039602d0b480b010940311604402c803040b06204501000080040e0422664001e180c070765828030402890300518001d5030400c0c003030500d107240c2f00801d41c0f410074441e60010a01803002040780003484825160fa4101c0d80c80302a9500c91408505580c00c1d078140f16000d0241c2085000e901d601d81c6075005004551110070510f40181005201c44004004201e9a0450429031000c40000c40d681e043c0a05140700030501032258070702c2c21a00a419010401c0c14007816807061500711044021540d803a07041200404004220990001c50606a400d00001c080041d0891101400203600384800314000500164001412220a24 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 283519487 1250 283518237 283518269
    0x4051f030e12160c031a07030e03040b12060a03020a0602010b0f0114090919022b05070203030a090501090803040b061f020c0405090703020d030906111516020a06020301061107 77
    0x1800250484600312580b400b03106070743d001898010030140480c0d201034002e0560000c000b28400e4142c01183c0a00100d46040003aa181c009003c0e0300c0f40958451082c81c2101403082c003a0003008406031503071084000701490001c90300c943c00100e206401c2c1d0081c80042c3e42d151010445810400c01c00d4045441c00d0900c1e0312200709501c0c00c84000e03c0394041c100d004482c0744012071111111050124244841c0c440295121100303481c203103d0900c00c50055001140e04400030000e01c82152050f14001e00e0305902641c41c0d50741d0115007002030809510110f90340e660320076000300450805030245000703521444809079141031800410140480340d9a000345a031281c0c084a03c003041d00050a00785401013501c000c105a90f0710316645003001a103901c0a03421001c0c02c44c00c181015031012203102920421b407140d0801018400d88942c0d07806850f0b902441504450000c100700644201c03240340032544510454000b41225610082030780c00030fa0089010929840c0c101415020034010000a07000010303200da540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 283520737 1250 283519487 283519513
    0x30423060708090307170c0102101506110c0d06050106230a0c080405090f010314070f0b0f0c0d0503241c02060f0a050d0e0c090406020a0504051f030e 66
    0x3a1040d03110041110a0005508015071428403001c1c008100d1822001c080b0030440504030340320004044850700502861040402076119403184001000d1002050b201c2d01d8100081a074840c07480041400b828403a02c40540d26030790320f10000010302d0344904800b19480d490200060510a000140c56000142c80000c0c2204101301c441512096174051414200c1d030b00d81418038584601c5641c0109030415202020071803a05034107004036041760720505200d04012845804151a03203601e0180348410318544400304103140c020005440d074401645541c52528428a02242c980b501326201e2a01240300072080028820f15001042e40e12810010880c003070b04d031900005556000c82008c44100c3c2e84110b404801076440d004240c4a1529503111281d544848001c4040e00e56044801c11241443c284200c42150040200c0c0c01d5030041c1014100005686a0ba03640b280650410a800342c02c0040038080042c6942d900c194641d001a41e18241c8002c10031290801002d039240a00101d40c0c5a01c41ca0381074440c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 283521987 1250 283520737 283520749
    0x8120903070308040809120f011b0c0f02040b040b03100b010f05070503030f0403020304080d0206010f050f01080a0f02160c030c0f0602060a020c0a2406050913020111010617030423 79
    0x104c140e200f5038080c0c0d034446450015a402c03e41a4041589204001c7c0d480714280055216070b40c510a81c242030605460f000d1002c40f9180c4104d80001c11480c04191a280107003016003019041d01e40090010031070105410101c1d00d0300702c070104407040a544400350004c403540c001d005005204114500303e0318200d526111641d0300d01c00588110311210b40340c400541414428000d503000341a04806a40d12182c52510007980e4400038055420311590702c00c400078007890321042d10070f02140c3c1a10307082c05550380d468061000b010b081e0350140c803440d02000f0f104040c00305e640c840d184041c40341c449080c107a8210f042240c81c260b2250410101c0e001424000c0c882c0640020f44594803040010015a80e200c070031103007504080395400d000300107050000d00000d242400c9076110306c038044032020800007280d032401000048182611407a41c0c451114140380c0c050f52041c100312042d951120004907502d80d6a40d0500d084e141030000e8050203800c0481d0510100c64030851f100f81d10551030340081410751901d00029170b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 283523237 1250 283521987 283521991
    0x609020127030b220305180a061d0d02031204091107020a050d05010f0510060e04060609172b0210050402220e1605040c0c080d05040c1208120903070308 67
    0x10500d4180019804000042c44030a0030f21000540c510001545c54042d015802400c08200320f0034126001c8846400c0109860342242c4041d902d400031542000750401900711410840c64000402420340c00c05603d00f00315100c000302c3d174a05655905ea02e0700003c1411915050020754480404001c2c41015a580c00b2042c001d0302c2c0c0403624004030340500e1400728010070503440646030503400c1904000e107444070340c046482114090f444e04000c0c2c45080003048102c0700b06010b81804a4001346043c48081c100901507099164607008544500c0c030040380a2564500d549602d80b80304258521040c00300b42d040c486001800200700091000d418a9400202d19a80a013200600103103130501814141c40d0715003181305a40c444a09031904101c001c034205041030310768003800e801030307051503040307452035215011021456030851402ea0a000b131000103031010708000341003650a101401008a42d908000750f1b16842d8074070501103d66285400391142ca94640004e0a124880d0801e00c1420007081d08180c0d10f03a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 283524487 1250 283523237 283523243
    0x90b07030b01020f1506090702012c100f02090a05030d090b0d022104020405010b0906160201030605060d0905070b0307020d0e040e030d090506060d02011b030203070f060902012703 79
    0x1c5204003540300100d2402e9100484200070b8130609542c2240b40426240a60240390203031841e45082d03654920990a0b02c14240c200044082c803007030903501c20744040d42280c03120001c0d0000d90301c840f5600100d038001e036160703040c00342c44c555030000b249001031034003500e01c030010700c8185c01424802500c04006490030340244a024529100080d1451010503143d0445200c4090140825000320300032540f0b102001003184c080740078501d040004500340c56140260b078100480245180c0c944454901d071030030213800078401207041c1511180007049598680015103001310000100003166480c600380f5a103410781c1c1d50300103040c0d01410424000059800f10301d007040c030220703810706c0302902c090000401c005007012658403101d4000850709150101058001d40d072402d000d00100c620b191250030070040c0603a10410001d011a03030680c00c004170340c20141c0d15503800381d00074015a418015151a40365404c407141008907001036403064140e04541e0000201d00e00c08000460801c60502c0d0a000b81a00020b580006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 283525737 1250 283524487 283524491
    0x3050d0b0a0f032a090507030c0801050a1403010f0608030c010605060301180515040c02030901020c03010608030427021908100605251403030f01120201410c01060603090b0703 77
    0x20004800005100711a4144d4058410800c1940ca01c00f040062809803100d200003820312a00c982c52500ca1704006041e9400282545110b500d82403040c03d503010340c3ca10700350300365403100c16001019500d0301c502c400500c10140515a50401d6100940c21180c0c13640101d48504000c2c001031040040341c002e082060581c180b00090161580301810007100010500c0aa22074103203412101070b542d000c40508040e00082c3c00715446a0503000400d1f003664801e01800c125644280000c101113400b030b410300c101421000c16017034200c2c402141c0190603640f004564803105905400e00178021a40501529400101c2c070f844da42d001420728400801911545a402040022031081118020489090746404d03a0303100b81c0440d1440c40140707806840f508100c500c5091039041100000e20155001c44200d40c0d40d070305940b56201036195040040311460401c1700343d005640e810305400892984c5000030410b5003e00300c400da0725040e003da1349038255406030708281c0815040000c161300207500c420f10140c00000e64140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 283526987 1250 283525737 283525763
    0x3090601090203061206040804090605030123071206121232130e18070b03040b040f080c060901290907170a0b0109150206071808030703050d0b0a0f03 66
    0x180a40200105210140c091031b005e001c204000d10008001b22404202c0502541d43e171141058200c6200781c1002501e0074600400301e40114100200ca5882880c50070408441c0d03106481c82c01c1101c0c880c0c1c12500350000b0700207281c414003c11140c1102c48000529102d00c8804000e6424000015001e10240c2001404400d4a42d544d044405442001032001090240c0d655142014080200c0a6039450340c45840055211500e5402040c10400d55500c00f001c103142d52155550060580001042560510924601480010001402400c046840c01c0080819090541d40b00f401c480350082410200810300c00301940d500e040c4040101c010100701d40000f6503640d503007407e0f40c051040e40c2c0d140e042d00d4070510070010340040c19070205661315020303a20136003c1034a401070300b1603d40c112120302c030241e40440c001665081c45910300c0b500d088100307980b210710140e98180e607900c0c5410000040300800e802090a40080b143d41c4207414242600f121151544c900e0a5030980c0c0300c0e03205000290028146200c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 283528237 1250 283526987 283526989
    0x606072a090f0203180d08070c060b1002010e06090c0a0e1b0c070303020105090601060503011401030603020913020405090307170a0c1a04020f1906030c0e030703030809060c0309060109020306 84
    0x39001004110180081c01400785401404000b58800c80b11803804084a0400c0c05100000003013803c01c00c0d4164954091036101c103031040c1c585080b1820f08481654444502044684a4030070425001d040380e000440c142c0d600700c80f041e042020091428001d9880222010400c0d075a110340034084581000e50300b8150b80340d0070302c3c011180070359452020390b1000001d20041c03101c10001707816044a0003980200100d4a0304540c042e11603200707100c0c0c40300041c0d062005000080387e140c0c650500000505000403038654a0703002c9404144119141580b80300c8940714a030950519008550340808100003a5190500d107589d030000000034403c00186101b0045000d1841600602842107195080612001102c556600080254800f103504034010403203050b1110440c1001d2408401c07400c01c036000000e10030b0400000300c1c020044030320b01001300220b00c20300c2c0402d91028400320300614000e95820000d454502e424070b01c0c0500c06000e03000d03401400c004200307850740d01041c16415220012405a0b072922910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 283529487 1250 283528237 283528313
    0xf0906010c0618030513060905010e100203130906150e061b0f0a060c09140109180f0501031103010c0f02060a051015080609010b0a170406060e100608060607 69
    0x8410680603c1c01040405260300040501950b806a600c812001da84036201100c1086281c400c42d0b002c90285617922503a4a00240340200a030010320499041050ba80314000400c0c000307a1002016640d00d9500b44101d0b2044e4190428080450401c05118002d090200702648640c85190003090505c003c0c1d014041018410a0890792409048507038100130390602e040100900e18000c00464403404000400044030f1182428401058441214942ca4810401d121028200811181d9a41d6035004002800c091041502a501516a03c241d00086c0e070145401c48100048070003d0061500040713021503030025016030f12408a00003c07480381c940030441d8900700e249030001080782c0f03441d00f0f00303030340266001140e1032082d10b040382c0031100c40e42d031101d03802550320a0000000c00240300b1841c2200000280503407e40003846034a00044159582030070401301d03082034500d060001801c42c0104840ca500c110b0035900107004032645c900d131135015030310b41c01112010303182826062038011140c010000e1203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 283530737 1250 283529487 283529501
    0x609080c060403031b080114090c090607051b06070206030103140a02041d01060f12060b0a03020411070b1e0708060d12090e1014010809010207080d1a0f0906010c06 72
    0x9035003220098141450042c0145c50350400c0138540701c002000301d40d01c403885042c09504030340b480c901d40940540a40113000000100411901c00c030340c02041030440a48848005101d2070b07006202a00940a141c0c40e518000000319649900c900024400c03480542d41c1c180490381160f0b84620b50000d2540c410240c80d04000031401d000c1d5001d4607007107110701042e07030b8546000001a03203074000b0800f6544440e1031a00c2d192860141c0b00910381c01c1c03401e400c00213146510410b0801002030844d0011035803980001d096030310501d480300e0010070201c1c1540801244c5408540c000d1006076804441c0c00009088808014005001c101005902004034880ea201d00382460700b030346d4100c1081c01c940e40c0103000180c82139800d07200d490380782ea451070009620152020b45a505a844051394140496155401164000740150001d09503560810040002400041c0140030050740144c01140b620909101c901c850095079103414000c14100b0103131815582d500042d00c0d400a02401c103a12007141608181e8010241 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 283531987 1250 283530737 283530757
    0x13080f121e040b1908070e0402090a030b130309060f02100f090614061e0f01030e100f0b0f030319030f0b0319020922020d061b0c03090501030c0507060908 68
    0x40010041407821144004102405401e02c4207185180b01030b201701e40304d801c12692080040e40c0c25a170b145c021f2801d0f400034808028001c1855040d180c0300d494120104a040e1000414169450360010406412101c40c50080440e402c104420a00e6030710003079154040c00300c0001d0b00f0ba545408000c41d00f4072a5202136003464002d1400c00540c182e1180004051809a540c2c52180da60721081c88034040042e40c010034203800107040860b11506100c0194080c0c0501d050f240d219000340c0b40c0d1260820241c0c85000c0000c107805c4804031b074080440c801e10030507102103002e20380243c10801100c01c410250000480d42441c8610340002d01d4640494208024201c100d04a80d03d40941b02d040400300180c1040c403400c0c1130089402150039129040500c582c41c44100f400c2120030101c210344405894525980a513807401490049110301000c0c441d100c2c5940c007034410304003042400a01200f0305601c0b903c2040030b0002800c040142c5004408090f009000d0a007000b443c440d101d81700001080414002c0da954001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 283533237 1250 283531987 283532047
    0x1020307030b12032d0d151401090b030405010902030a030806040605060405091b0409022209090f0f060f14070e030609070902030a02040503060408071109040b0106050a1107080313080f12 82
    0x1a80741306070043c0c0003150880755001b02031f0b10041003100d010b100f02500941c0507112005441d150411030300042c0c00050068a140d5a03c1c0210700140c0c9003800403100c041d120f50388000032482e081041008681a680095000d64418041413080781ca402c0300c035076000201d005c00a075000e0b00c40850980c251040f0b420011115001151955207052601c0c01921141100c10313041240c1e5441c1c2c1924000c603034410201820428031200c0c0c041c085a80d0f00c0789100c0d950300484000c03440c00b02050510051740c81c00301c2c464440300101e00c1000b000990040404400c0c0c42e00b00d010f0300362400c20702d40c0749507581d03118020000c0060303000001c10b040202d40d50464000b4007000d000d44200c2e1030141414507068200d204140e0383e01c80041e00702042c6142800b00300d40308a0744507068654503428503008031003d4101c144a40b05014558a000b1341442d403c01c11203004043d900b0041d0b945084009080d03192408a42c001d40869100031419164440c022600c440b60314440c03512203071600f000d040d103910203482501c01004004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 283534487 1250 283533237 283533247
    0x20d0605060a030f06080c06040b0f0405150702031c020c0f1906081821090f0d080c010e2407050415020d0e06211306020c01020307030b12032d 63
    0x2a8254001100c0182c944d0020071800d42d03281c007030b152245443d80c90160b104004100900543c410314000d020704001200b0400e08007900ea802040d200d081030a00c000320b54401041000c110300d02001000c44030040550245940003141a0103550741900c41580c51040c5460040034a01e5191200c0400d503d144000c134585a9650310500689410002e541c12a00008400c4840d0b24400300016402d25600c100c88a8110300542000d2041594110642259014081000c00c5605070b0310040c45071111801100c200d9900c607403030003480303084400c1d85510b046141c009552030070003480c0c900340200c01c014045400070516510490212228401ea402956000c01c029503c44422a0f000030301645421858450f071181b0b1143c54200722075402080140e101384443ca011881002c20f6403210590014811003039182260f0203580c03036000740c0e0002d0f0114452a98088100069980d05014002e10108255036105040011413100c5844e48104020340114001502040c170f407800c130104082000604401c00e00d5251 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 283535737 1250 283534487 283534507
    0xf0b041d060c04180c030f090b06281412070603050f0c030411040903020712050a0b0f010b030403050f090901061701081c031a1801090c030c0c0204020d060506 70
    0x1000c0355084045551148070000b65101009000719000e0702d0602030080c524020800c4500c0291880c450074404064440d400c01190b100309005045c4194031038040c0b41c055145c0305051100c5040411b0060726440a043c07059004044195034900c280c40703250400001000340c0c0c130b01040480740c000c0a590303803500c03440ca070000306154140d2006000d00c10441c0046401d458055a06105002c25500508100c2c04001d01c034600d85465407020031010b10900640d5079550703a03220007003095240603c00361199005503070140c1c1080010f101c0190300ca42c11542c100950350602021600da0f00000344010148000002d43c6040403804006880c2c040d280148610090340c0c48000c0200110703e101c00b2940700c5104040080740c1081c01003201800a220800070305080034110b80b0841c0039004a03055844e800d000462544010348a198290781c80881c4072244911951402950104031105609208100741c43c02107058900350303000071003c00b0741d03804503405038552820809113001401154055580003200251901341 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 283536987 1250 283535737 283535771
    0x304051516090902122a0310050a1706160e130605030607030c0e100903050318101106070e12060f0603011401030507090c1205041b0501031e0f0b04 65
    0x107902079503a41e078040300c0c1d4611080c000e07801100c040701001c204550005540d1840b844010581c82c8020f0720b801c0f4240e80c40300040103030b580256880241da6003400350502190424069040c01004003130341202c0302c04d54003a07074075131075410151a01e02c1008414040481c01e5115541d19203169000902d00320400c00c6508114004006d0340c030683d4081d021702000158024003a21a00f007000d402c03034540f0001c02035008108148104103521000500003910000710114904102800001a1f1000700190007030010301080010b16000794071798100410007001080380d10001c103803150015480c4c1083c0703101c5403255000601c5000710003d103000d20302c00c8404008491802e01461400303284190001c20100d108000c4034500350209020242c400d500100c005c00a844107a8800c0132900203929001030019492400c6806980d420f6400f0b851071442500311103005140c400306540281801d082c00c111003620602000107414500311035421b01540c41c031400c40356904a40007000080c10007802045121380007168080c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 283538237 1250 283536987 283537021
    0x1f060c0b01060e09040201050a170426070309050105030c09040207030e0901050f0a0b2809050103140708041202070504090c03060e061e2a07140d050703030203040515 73
    0x4a5501038800003a00724014a846415040c000d0a0091280d0320350f00103403181d42c0b000c81035404106414000581910030000c19501940c032584500801d9031022592210070410244001810394080041c0c00000f5041920041100e0342070038a141c0703a54408031542001e0103100c44150b003060001511204069006c40e007181c001c0c104807841280c82c1d80b10740070300840499411140d07411018081091050700742c0c09001c0d00398038584520440c130754022820b60300e02c840c09481c7c0c4003004ca6081784042c0300c41d40e094003c1c580c4036400c01e202c0716002c0c40d02c898000c08e4180c3c0508003504d2000044000800148240004c0004c2c0101500034002c400040c94203800b44c601070710003a030360186404030242d081040890b109000725540d4610080091a4040c405a00800070b01006039150b150070012240c00e848101415500c2000090152103888500341324501c448940880845500140080b03035035150803505403411140c0524005131039698070300e803007482c10060000d40c1050702445010031034001c8298007500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 283539487 1250 283538237 283538243
    0x2206050a0c1202040627030501061d06030c1516050313030201090b07020303030103080d1407110c030114070f021905031c05010b0301050d03020307140c040e030c060f1f060c 76
    0xd160b4030401e914100e01a0380076040014400181e00104405440c0d512809840201080e04440d07503030303590703860840d10903078401980f41c0c2141c4807155040d07200345803040d8000c60603805803107407100900000320620351310040f803505001301085400004440c4a6140c2c690340d0702a040302c2d642c0b0112080c000090250b844224001200c922002c9043c4c0c0182c000e03108800d5014000754216403c5584204841e04a469400d90309a99035035860301c0031504e03a41450140800d520b07603180c21100700d40c841d070070000c60140c26800f0781c1c1410748a021810340196036075030040b4980380c0010083c01e0381008a0904524007161a1031807000d042031018044080001c0c0540010400213070118010314140e007003a030300d003449024a00c00b02400100080e007800300c4e0140b4403601c644142c1e490240310359107054940205d42c400300c94a900090854489007400d00c6182c0f40c40702040015410210b884042503a90a401040050034107000c1010940c00c1d00c44000208450b03202c004407079111501e03a0401446014200815 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 283540737 1250 283539487 283539497
    0x30c0614062d09041b0b09090c0c0601050f0301090f0b0105090702070605160201050702180604050c04050303180414040302011e0911310f06060503070203032206050a0c 74
    0x710800740084507070b9041c1000084508100d1810380d0003001410840200240d4081d0103c2030038024030700541e2240d402030b1102900460721807000006010303009400030a800c50120041100280407640080c5503811614102c441d40e144071031010101e8050540302c0e00051070502c03809100c404001d55000800c0c1a10300176940226607903600c041c1203236680c1c213a03c07a2134049001000b014004000c4c7d6484145c42c54010f061140c98042d00f5800716101c0452050810400074058083c4003251400e801440d803c042c001180f03909042c00d0000083d10382c8115800c00000801c01038900e0038644480e0003801d00c150300344114504d40e10f01410302a01800d060583c40f032080828141c1c024044d681449691100750f003201500c1c064400c0402170085842c0c0c043d0b41c1146900e0f880b09000703140a1140e0040c2e0050546180209000b040c7d12035143c1661a2500060700b80f1a050041243da15400400d0300d50222045c0d0800c52400202c82c105409580f50b85030140940381414108081280542c201c0090394580d5aa0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 283541987 1250 283540737 283540759
    0x20f041a12010b1303080c0105043e030c0405041a0601180e04030e060c070e0c0301060e060d0207081b15010b1801020111070b09070b03130f030c061406 67
    0x2a44030984181004000c07102142401803100d5207000e00138180c0341c903401d81c4142c041900c9441c0d0120300d412580e0b03c41216034494003080708210840c01c0070f60811030303a001200c284a11003a81500d0302102c91313044000308050f110029495035802c0000050488025001f00840d081501345104405508040c0c0c210394422035012401a500c200c140410125441003803103451402c04d00c1c8200600310260080d02001202203000b54956115070080000b5039450300200381e9245400f115030f591a0008002241e805011b0004120454000302000c601150489025968403201e1000704020f00454030003410001003c16185050f00d11452400403000c0200c0c202d60b260031000c3c1d1510003a400034021520074a805214000d0900111140b103901844140008216001d82c0162603e05030000c4e2421b40f2912200018070203060014407001c00078121500366070b0325500c4c04140104608550000c010002c4412208034030516115522072189141d0210080c4044000d80d1204044140b058445621582c00691 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 283543237 1250 283541987 283542029
    0x20102031f0509010b091906021608031c09080706020a120f0506030d030e1e070920041a040308031906120b0f0c040b030f0108010c0903020d060c050904020f04 70
    0x2115804aa02c014200c0c40f5a070309020b41068140c1003150503903040708801052105880c3c02c0d4000f60042c110035030040c612600c00b40d1800e082040c603a8820b42668004001e4040300562481e5014005400501d02007203405c41450184641c1c071460300007a0440e0300c0495100c0c0b0440c7d002950003610b19002030180070507500c0c07503c044202c4606840d400e90503440303030301074400c00d41c040e0b0403408110483c08140c509103954081e110101010b45034482003540c103d41401d2207000c040748100a0714010211161291180b5408100290300c201d001d008803001e02d81c0d40ca81c201d00402400c81c0d01441e800419607840381400c1141410b0000203514407244242030020109200c032038515484400341e00507011030f609458132416079031940f2000c0c0041c260804104400702c0c0d806406070007580500042e807440e41c89589031115442c00c640700d0742880300c2003005240081015949203124244000e8001d20700092043d0301d880d003501c1c0392140010b100c0c0c2050000c0340060410080e40041d204903020820f500c1c80e0581189 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 283544487 1250 283543237 283543291
    0x3070b03010806070e0a050409080304050d0309080f0310050406090e06060301020f040308090a09020a090e0f0709090507120f090b0121080708090a0f061e0212090301180302010203 79
    0x100445102e548a40f000402d0706218640c1116540310103004140510707103440c041015910b00b404156100320001003800b0030890200509100c11102d450300300301c40d0485640e0190188600c55041c1e060340d4001c000724044130361401841000b00f50040040198550b5000c10a000d452408545405405807400041c050b08040c021203840e40300c40d03007001e0714040c1155100b0166070401505560480300458010400e40078078801012200c1154803040120b924164074001c9010001308030703106410f1854103001e50540c00640301c6c001e941c880903001c43c0694a80ea41110504002d40d4440741c500c0c180721414440c0c0c280ea60020380407600130410000940c0c0c0f2045428404c07440001c1c0b40c451400da00d02501d0204820602406001d8440c1d00e00030b14041c02c1f1400510900001d4001240010350600208107064000d0850700000ca038a440f09044003072030706c101a443e200501c1c10302401c55800212030300385030790079403052200208540103220810001d0400a001703410840d03030b980300070700009103513007031202c00c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 283545737 1250 283544487 283544489
    0x4060912150935040b0f0c0d09030b091c030b190e180303040f02060a02070e04060f06090c1d01020f0a06060501020c061602010e0105160302060708100e040b0c0c030f030603070b0301 80
    0x402101c1d03142c10300c1c240c5c401c51a6031043c40d69692400041c8103004040304244107407030b010303122507072681f039a1421824006030f10070000c0c140c1c1b03c16034072611700b407010020320991851405426003400245425200c0209641440d094199854808055008943d11b0b822100c02ca01500d041200400d0002c4208011039032448140c60207007048010180650052070540003c003900203180c81a10140c580e50403c54068110550f03089900c107803202c0101d141c031000740c8508030040c201e484080c0310840c25514003800381e085100d003025410303282059110850f4020402030341007403103503012901c50a400b418840c004146a005841c0140101c4002d48058905081542ca48842e201c0794444840616030066a007456142c0b00181840018043c2e031282c1141c041e5200d06090207600600400e1038080b4004210002c02000c105240900c8002408401810300060303030320a41c00b80080000f42c1360303a05030074182d0041070380441407407000040038400381400401a43c0034030300a80440302070540341c05580c1054042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 283546987 1250 283545737 283545833
    0x50d1b030509190506040803041b03030309050613080304060525091d01050307180627050105120c01110c0901120c0501020d0e1c0209090102070b0903040609121509 72
    0x170202c04140440c14040095800610455000e0710a0003070810703944424145070b0095012aa50f01c0a80e0280302d03052210039441114000a109011510363701c241140c00080c1c0050400c56484000926034580c0a46c00e003282541503010034040107441c0b000528801140c0204588145a0303070514240910881707e076410303950001c1c060000c0c1400c0030086001c1d2942042c0e041c10040d20740400280c00c2d00c0010001c800041d070070001421041d281007410040d10810383c003250080416081030710400038081040c1036544002d1801000e030205400d209450302c800f103e040c9502601940c00018180764458400f19094490550310440a03034550040e41c640054484802c007151070130352661803034501060411000d4070034426050081380c0940205450b11401c40e40d0f11003c1c0c2d030010f00e0406000c00d0510599019004500543c80c00f030401d4002003103204244601429044201103200402600f00400025006071071801c2180445604000141c40c1c0c4208403190f002c2d0707100308041048000b400001c105c020b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 283548237 1250 283546987 283546993
    0xf03020a0909030804080c121c14070e0105220e0708070201020c061b0d06030809030f011a041d0114061c110603071101051801060605070c0303050d1b0305091905 71
    0x2581d1b48a00305281e0021600b074449018401c010310b40318200030090034621134170200340c0e074605096000400484041040240a202c421003c000036640c3c40990110481c03802c0c80e000d070b103d89490307200e00c00305040b043c0b0088540001044c0841c00752100d01c0c80d40d01c01c88003a512a0310f02d480744401617080384030740380110080b1380140707002400040ca60180e081b41d8001402a003480c20039a002c0000459141c0d41003182c02c910f00080100c0d0924041100c00340d40c5640c44000c00c4510070103400c0804c9440000780079030245071520079101000070001c0c034014601d01584020301c002a880440880e207014110350103407041d00441300b070300c41d101075990852401c0c0380d00000d40201002031401304507098100400c0403003000f02269040d020340100b0f014040c003900aa04034084141e150389030311400d45246401c0709003000424000307207000c20401c50903041282c0d003504010741d84003c0e005504026040b401c0a1489407260190072800700f0ba0700d070b84160f2040241406071650403101d80b01418052280c60030140c282d40c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 283549487 1250 283548237 283548241
    0x10b01080c091c050d03051014090a0c0507080703050409150e0f0a18030801030c0501080c040e0a020f2a0105100902090616050303010815010609090b04090503040f03020a09090308 79
    0xb04000c8010124003001c5070502c41e0420342561024a0014413181c03c5d80001e80303074020b00c141c081c4004226005801100f032007038098a0030f01c021405040001301108071407034403007028820007406241102e2010307402003030203070303031a0360500f0040c2140e07116101e4042c0c0c841c5030200100000c1001c2481c4000e803030080c0d00b41c0101384c81d03e0103a801c8c0d180000d400810030580d01c02c101980e03030445441281500703202e070720780921542c07650130003182c918070316402181400054003c0110f0003041c5421581a5148602520f41540345e1a0110000740240141c6d809000c0d00006e07400700141804e40c03140342071441a02045100140c001120b4240c0b0800c0e1a0f030f1694852a02c401d005988003a00580724803e000f1740002c2c01c1005591001207502c080800c295015000040140880281801014a1f0103481d00e8030b08120b5150001c014a204018481c2c1101203507a00000d01083c0d445410070590540c01108907600d9980300e50116408116034032089110b420450000106140d50b40074400c95150903885881050b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 283550737 1250 283549487 283549489
    0x50c010302032203200106060305010806060901060f0207120303050a0f09021f182709030e0108090a060c05030603010b0103060308030402062d0d0c0216030219080708010c02010b01080c09 82
    0x1c50b020660071028041c1140c0080d101c80103040d4018241c0403141c00104107e40350000250845d581a0000070042d0020b40c1044200d440e482d14441c1103480c14604442c0003151110700702e0034510a82c0040405050440c0d544c0306066064000500904c1c4805c410801070b00202031100486030f11a40080d0024951903410380b166100f00c0741801c1c0074000d4103144010103440d200c0141003803400d400043d948c00d1180440850710f101c0658403080c441545a0400103445661006400c4207559219241000f107031b40c0002b100b815061042d15480c650050091000540c11100a0560707001107403014000d610b006949105507201f8000c0100b00c94100f03011034650389460302480381903030184000b5014a20a0060051b40c0301e402015140b089803000982d640340c0c0184000b42003a503a0354141501190b1140e42140f00d20a070035010403046070303070440e0700c02154211040b00ca981c9641d140d0180c0880d01410034002143d26042d04103a14019440e8000c220000520005407502c44094a610b80c08080c240810812 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 283551987 1250 283550737 283550791
    0x3090d080a03020903100c17100306020702011101090c05011e08011203020705150414120c0409051e0303090f030a051c0f020406180f05060906090d0209070c050c01030203 75
    0xc0c1c50300780d1801600c1c04104d54082460041020703907014655645440041e80c107a44107880400e5101a401d01c44001c0c1003144881e40c5c00642d901005c0c04e50b60340010940c0843e80142008884103540000900642c015401d001e02194043d11649020900c80f1502003901c4005034000768824885483d440c103070340d0804650704000921103e0480c15881a9078002c41c442da1501c0d489a0820614181140d07144e04045407907101c00c401c440b00383d0042c803030f20b0240710414801040b495107043e000c1e50002181c0e041803c10b5407a00e20000001f082c511246100400d004c00d0100045100d070404104980320000414455950b0b40f0070001d44800048040c0001480c04140012070290751319100c5011400244070003c2d4400c9a00c290700403408034421580718040d44082c014107000030701e2031803456a00d040c640000310302c6521400c00458822900002d604840380e40790a0941c024640160041d460340c44d00c4640504110103d980540340d078414440c007030711590302c24000c0340d00c82c034042e007420000d829403002d0b44c0c50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 283553237 1250 283551987 283551997
    0x6090b160f0f140408011104080c010201020a0905010c020d0212030a020c090f0106081906060f030c0f14250b10080a050c0103020304051c030c1409060711061c09031103090d08 77
    0x5003c8010000080c501c0000d0240d0000c0d2020305003115583d920380078844d8501502e0401030382c15a401800b844d5100e0750400b030020200d4000b800d0041d4181c6480c40054900218454025800010b10a81c00740d01a0008007421000c6c00355003c40d02c1c0d080042d0104030005100b2504002e907481144010320070548980d01d039681240b0b00c4050301300c0c110100108002a078059403c0700c40010001410b08241d50791500a09003401980d0600c0040d00401000080c68150007502690f801c00300000e42d8401504d540c1e00c1c0f4410800440110f400c401070b80d2034541e01d13005054822183c3d80240000110302480301141d03000003142d2000045c004a0b80da41c00560103900700a005503981c0c016051118050645002c08111141803503034006603120901c50058030b10b580c0da52030341545c41d03404d0080401641b00e0390101d41080c0c0e0000d420078040115a00010795030710410b00c41040c403891204c403076046800290403600d1014800d89a0f4105641614085552030013864171013a405480340c1d03003010104040b400100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 283554487 1250 283553237 283553267
    0x13300b0106030c050f031509060402030906010b0a050702120607080f09031207120e0607033608070c0e04060614010f1805060417150103030c060f060306090b160f0f 72
    0xa050030201c08000b5017540040307400508000d001396455409103407000121740d00c1001201c08600394180f8813101035039604140104200510300240020540340504151603c896008012071070304140c400005840e410103803051300c0401c11800204810b1501c200d581846440c0001c01542000b00c41e101103030407104003500e114140021010b01c07480e0426180034110a03544c4072070060900c0c0c00c0000004084548102113004036070300c5041c0d170071241c500042c128510415500c00300d0712803030030074200a4202e10074454014001d9009000009410100c000daa40c0b080c0e025100410041d5641c1440f44c0203059000a55400100035001d000101b5009074130704000c401c1038101400b2102e031610b010503da81d0064000009010300301480c145c0303d01d803c0003440104a611900703a642d0354590307070b00a0701800c8007100060006846480340b50320f81407182d000c400115000002800303810024142010303100c0c8182c03501410400c2a10140a07d0fa0213202405402d4049903214402c0c812903003c100d540f84031040d411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 283555737 1250 283554487 283554497
    0x4082a010519030f0f090b04120801080a2a1e08010b0105030a1523090108160b0f0904060f1404050106050315060d020c030a1d03030403060f0213300b0106030c 70
    0x8102910106d210346445e0360f218170304910071401c0c1800c28007640030160000d5800c0024a0b4014841d500307002c50070a00c0b00350b0180c2c4001a207251300161980d4030407645160308042040d00c6001600c0000750101c520560844200c20f1181074a0740b001300e080e0ba00c0000840d020400400c081000a812548400703070003212074603510440d9803200b03802910038100010340c4c40c0b00310004002c03200c00e15088060a0050803488020f2485600b90a9101c000300c01da40310344042242c0102c2c8401480052100f11941003200920800450351030700c0d01003a008405000311a840c1d07000902d48102c0f0305041c030810741a660365450703076410b6070345001120003583c41002051740c01510501c041123001540f8005420b490400c20081c584070481500014442c02c80d402040d03507245600c481038040b0382c03000710442c0e081e40c0d0045004a002c03084024020040e2158912031062440b0b203540004440300102507103c2144c0380c1403034a1140f55481d20007008618003e12000d000084070400410205000398400c404800d90750401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 283556987 1250 283555737 283555751
    0x8010e03030c0a0e19050a0f030f0204092303040e010b0307120b0a050301020715230f0a0908030412020609071d1302091e01120b04140304082a010519030f 68
    0x30804c80308945c40881d6a420040fa0148000e1510001c40310181c001c1c2911803a510b03145803169072028101201c080e0245e55601019014031000c1d4902030084180080201c4c41d15a5507000940c0e02d512a00c200c2ea0410004400440c440d40906c0840340030f08050307036070a00d0083c80b104080000340190300f1a50780c80966940000b405e61400e00140c600c1c1030040c0550356085a071007105c1c00c1a2580c18070341c03154a90f0f08001c8400d030a1030b502c4005070045407410700440d2650700c0c100b103040140780503c405001c0420110402040000e0340500c0410008560300741c400a4882c50305459499282d40620b01d05864500e69521504400800e8154080d1b80d0081c61500401a1b801058003c3d0341510084680102c9813031414240704a40e950342c0c0180344000c4484e481402c0c64030340100034000540014401c82071b4074040180c0070340820a84001e40802401d030789141c2c4400c0c1e920280d400210300c880040007808801d00c0d450b1744c003a0007070740c462002402900c403203040f841c403080780107102072801100c00130b42e207400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 283558237 1250 283556987 283556989
    0x2a030c01151508010e2206050406090c0f0b0703080a151806080c0d1b0512010b180907180219030c0e1e13141302010908010e03030c0a0e 60
    0x2902204510010865100d509040b5100c10700500400060b080c00811001013000310b824929640d44101c210852901600103510701000320351004001908250400003400b0600c0129400032110718070400c0c841041c60340d20710164001e4800d0348540041d400c0c09103c81c2e40401e01601c042a071000b4442000a03803000c99409070100e51b8215041606400107a0354807601c06a40c0d4030840b0040d204800060016182d184000703140345c50703d0300c0003e280500c0000700b0388206400f40f805002524000b8442034440f640c100b080e0f4000c2c980b1412040c42181000202150844441d2046000346090ba01500e0800d04044011402c145031240302c040950782040042c0120401a181c0e1660fa070860b980032903070300d130034410040403000c95110007071007800510981c0007403a003000303c050451581620b142080c11040c40c14100200f009510042200650320f081000d08503008016000d2507100343c1b00c0400d5180c491345001d0884107890300c2c0400c00ea0003080130600d0b010354003003c1d02072040c02c1d03d002221200080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 283559487 1250 283558237 283558241
    0x50402070f0219150e03100905031c1b050702100509012303010e0a0b0a090b0f040204030501200a0801090506061b010f0c020a24091e0302060c2a030c01 67
    0x40b000440d103150031400d120641c00e014141c1d581440c85d150082c584202c000000e0b85034a80c080c0703c04c4100b5070340d500c140100403080c070556102c030b21400c4282c0403030702002c5440400740400c11410329440680350f00c0d060f01d881c01a41a10744a6401409000d03404041080942d000e5115210042c14810f400320301c5100084090a01d6031845040049251a035250204100e01100b025089030005801c0038a0318450703480e0711850030100d8180c03180103e1411180804100050070b41e11060b60060300029012083c4401500007255a42c41d2150b0310050401651030440e8034040d030310400f0001000e200041010385242c0c0c0105070001c80090110340350041c0400c0218400b1a40e208410482e51100816800d422440c851f442038040300f1f0018150f00c191603514000351084450b903d0860300b400354203840503802103502411140d40d101503aa1082e41c00b802d440103454404036401c8006100c2c00f40000c0d00d441c85c0d0016074403041500c41410411029245015802d01c1007142e40303500c1403005010741040e0140034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 283560737 1250 283559487 283559509
    0x91e0302030702010206070306050310050705040f0b04050901090207030c060f0209091314030f04030b13080f030103150b1f020c0301020d090201020606040e03031303110307060501061b030801050402070f02 90
    0xe8004594a5449100180c00d286005085400340340ca00f00c1d0070055034030082500c0c188a014100300040940c1c0c3c00a080c0c0d0240607036040034003440401000810f0300c000460003001620000c40b505040340c3c0c0d84005a01c00c0c0e20965400900003044190ba00c0005602500580009900410094103058002e40030500d5040100c580c03a05902401001800780481c81000c3c400000340712029510300010191f40c007200c2e100c2d83c4030041000304030000281c00807a03103e881280242e030003014965225068102c03005190420701050b500c82c2c504110304501c41806105002c1d074110f003c0c10000c060080d8031100d800c11200ca00c020020350003229060180b82e41c003840101942041c0381000504010540002454040000c2406000e03600c1d10320002111640081600d03448013850245408504131131504807200681396a15145502c80400d0000c01c000782604414141c13052a42c4a07480308030240d8029aa00c3c0c051407018000c2160240107110302d0400340c00034522103018282210900c1c040c3c0d40841c1ca208a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 283561987 1250 283560737 283560743
    0x310050606091c241506020606270708160f0909020901020307061d0c1915051201180515010903020913080301090504021005040e060f0a0b12010302030c1909091e 71
    0x13000c1c10080004c030961040002c141c448100a01c940b0303060400196507688013800407407103203110001044254070400d0642d902d54500c0f400042035410592400b030910350080d0303100c103032204603001420040e5101c0c0c0c940c41103e041943d14400041d2400ca4190000d40c040102e250450008106040100b21b280c003944011080e1440c0600603a012111380f42d041c0b0b404649010f100d070f0641100340d02c400805d005c588050710340e200e40701a00021408010f580501c101754903641071a86130000000c403440c001108116030300617410280219074801e028400850105074a0130302140d41c0240910141c2020b03400d45500195a00010145030041c0e112a076071a0400d07800004556140c808010440c1043c2c02003003644002424451b04103400e01e000e0581e02a0018070a030702800c03500c0c030184400e035a00c50f0490028100e101e2025a03038103001010364041c7d4424001039000f44501c2c90081181e007081170310700d094100140088a10581026690006445488005d940040000c1c10518030000100d480c0031180f44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 283563237 1250 283561987 283562033
    0x708121306051f05120a0f0308040203070f030218090c030f0703050705090112151d0109020901150509010503090109050d080703050a050c091909060b090310050606091c 74
    0x6014070300315050b900c0051000c1440e070241c00b50205201c4518212034140e40d81220112019588051010310345541c0300700242024000308201c100f455007000740c843c0114000ea081c0d0740030070f0b02e810380c98081c2d02d1580b000a40001c0d2a5864a4204131910341c0c854000d01c400060f04d08514094002078503203185260041015000484200200701d420062900100030594035404c10350b16000c02006250369140f0050300c4800c10701c207502804205548482c104030304c0b40002c81c0e06840d0141c0352074001e01c504e1604a010380411000440c1200320180d480c0540d8000b9620b013032404007040011a92034001900c48201036484460030f1002501c02c0c010000007640680c0c8004d1180f60400300201920405440c00c6e201c1860f0806100c000041c260481d0b8042c1d20603240400140555615a9004050b503030252303002c0c52800602150010084006202080f0110115442c1c42ca41a41d60821600240c030b0712a80300c1c004000e52811410a00f450409400300b400b41202040025180c0c0f85820101038040b0740001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 283564487 1250 283563237 283563271
    0x804150b060d230601020c010f18030c03020907110607030c020a0b01081612051c05091503011802091008040f0506090709180b15040e010f0c020f0d09060302070812 72
    0x2010004211100510380b083c0c00f6200d0822000107034880b5400481c0c18100a064180111601d0040449081455101c000c1619180e540e08250360503140d00c0c00f0481c801c08051011480951007140080e039624200c0020b0b107019107d1081c15401000300d0316160341503020b03131082c0700b0101e0060490280204541e10146c500c090a0345c040b540c009009810503c1c0000c0140f540c1d402148000402c14400b01400241c603a03140c600d81130590b920300a80030510f07848101d80c203010040d840254040c6040701d07141c40c4030010420b1004c107403005900602c206203420000403818480d03114404c01d992500030303018540300380440003942c0ba05805c1c014225488082a031040c8020007100c0d2051140865081d40c20114207102083c40e034800b4001040605900d201c542c122a030700d10560340f42c4e03002c0c140d4600420001c0101c0252188141d01503c180035203940540100020b4980f4080d0200c1c0e041d072521800c0c0d80700c000071401d0a0702a0000e400400043e20b80003c11f000481e0181e1429411a010750008000da1500d9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 283565737 1250 283564487 283564511
    0x4060203181c030f06030f050d0311070f06020d020f03071107060804080a120204180609060e0f0a0507020c100206060406060504050a141201060b0c010e07060804150b060d 75
    0x1980352507441c0400d5112004018840c507070b20b0681c40e01c0000500d0046010013000c0310a4014000e5078101a01600002540d0001c00c800020134010303016171503c0500c802d000303103802040075004400018182c2c80041084a00055081e4000c0150840202006091100e2050407a186400456584011582d202d10200507100200b11b02c4004010302c2c070f089142864140d540e1540b6001c0c3c2c4003820107105a403003034003680302e080d901901d0185ca02418000091160100d0300f00c00b5021910926043c185400720102c1ca91004a0742c0c6845142c90b4819551701d521100c0201009001c02080001140107050310440c0b140d4890703000319509400c0b40d00600207400c5c988100022030300c4941c01841070110400082000e9262518403030100c0c0e2090380d0b1410810b480c0c0010070b100d02120810481c5c0c0354600071000c24110990700203000c08105160007042182c10202e2050360321002d5000340400b003004200002d000410a0307c0440b4042014080481d89206410114440d0341040302c6000c5070b40c2e19000c0011071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 283566987 1250 283565737 283565761
    0x70609120801080c1018170706030b1002060112060e0307030c0b0604060602071a0f030a02031f03020f04020c0f0d030f0e0c0f0603042109060f030510051905040504060203 75
    0x14108160240c40d007a40c00300d00052222840185d41d00c2405000c4040442110410155400402a1016004260010000140e00d644e110300030040881e180c00240056400c2140c19180c10148603001060b5990800b101d4408004075890120340e890384584404054000074005005d4062090310f0710b0075080c0c01c918010000c3d80005203024000c516191081044690001d00703d000c48440616015400c6e10988400300d5911900021a070000c1e40001400401e0105500540c401c00500b100c550190461070a1800c02c03103410310029620091004003400189055401010100234501c00c481000c540c0000a60070521121004030109948010120784100c007802a180c40300912000381c04220000d1b030000e0700c4c4090b0092480d000d504040006000c024070901e118071800000301c030445000e59150401800e8007214001c000010b000c000c414107059019004a41c0139140941c1840c90103401d02c0305001d0110840a6180c07200c0b000700310001216142c41c425180200c0c010040075a8900d4003c14140b2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 283568237 1250 283566987 283566989
    0x7090b0f04090f0b0601050721090503060903190e0919050a0902030316020d050703051006090b0306070c2d1b150c050106150203030702010b010212040b090402070609120801 76
    0x1000702c2c14a4441ca00140c09201d14030a0158055010788030f6880300001211180107020000300640c1030341c0c0050340307240380c0000303e07a94400721070b81c400301e81e10b07111003d15484c0c84064a1105503540180812616074408105482d001c0006150400e1500b4488001441400090b6a5040401450003034070b070a1040600030310f40c1c01502140b041c4811241913001c2607403881055048010000043c030203904543c1da40b039000081c99005411546180d490741803140d12a5041c49405504a00d40180020701004c0c03030165074441c08004020301702550b60781400b03560380c2d402c00000322940a40b07a20590341000c00e003080354008034500845000c014440b49072140000d10341d0b0500f40148808500100400240c0403d10300c45c1151070f00c1c210344281c01702d141c0f00d409000d60f60801e510b02c0040d060790b690700c80d0307000018511401d03044e8000d219611070b100043e038980c2d641e1845024070290400c001e00a04c40c1613001414007e0b0094801442c00c2c040b034079103d0440e100d031401203583d090411600e0364039a60100c0514 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 283569487 1250 283568237 283568239
    0x609060d0b040f0e280203060403090e06010816050306030115060504050310020c030a1b08121504090308010b0c030f0c03191d040f02071407060f0905030d081807090b0f 74
    0x404501d113200c907150b5030300310700d22041c0c50613917170180d00040f10040004844007182e01408407109401d0915000d0f0248c44203004201c3c240d03005000142d4190300c510181800b9248642007100003209041d41101c40754002424607800d507403240c140c802200408880c90b4000c0021f036603400d03184c505000c101070030004c1d01044110614014410045240c9002c012a641c01c0315130304296001900d0200340d400c2030038019801030401c04005c10004d858bd10f089215030b20bd8918070014952001591081101316440c0e404080c00082d600401402006507850003444100d0700c1004881c240144149445003591082a0b14400798202141c1c801c00ca0b034000715411092542030070560101560070000d0303031341070700700c40840c1c1d104a84400b407035085213480b03a040342c0c04240c02500080720100000c0c000795442c20240f085800168410b401501c3c517074411400c0c0c100303039a03000740034000c44051008212402c000c080c0c2025400040c08040c050303400010000783d8001e028001020807081d00c6030301008556000a0306003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 283570737 1250 283569487 283569491
    0x5100201050f062707050703030501050303120106050a030b0d0f0507081506010c0204060510030501080615010210091e061a0909191106040306020c0c040207080a030b0609060d0b040f 80
    0x40000d003080c16030b03000da20000a5640c2c000040c06502d20040100da50038100c40481000814010340310f600600824400d40a51820700041c1d917200181a5248030389100c0384114600c0000600c9003030f1240004000000c42880c000c5032103501d900000360302040120003200c505040348004020420f040c0481c000030442d920140c00c1748142c0045020301300318018585410481c1542e0240115a51070f0703c0b540c050301e40500520b031b10620b1400c000e40201020700502e01c0a100781c2000071244098a2540060380d0010381c00307440c000101c41c62406c090f24000c030040f19081c50b0803c1c81001c43c00b1500340d08103c51302620b00401e4012040041400c84e5030610b05a600034900c100c1000b00b8000300007924810f04c100c10700308000401040c04c251150040c140704040e8403190025002040c4206078001d0315640101c5000d840c003802c10602000200c0c41008001440c80d501404900140c1d4041e40c000601d030000909954079000190000031a070703900c0403420102c0705940d00301d080820300341841600502c94080c841 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 283571987 1250 283570737 283570741
    0x14130b0d0323030108030c070b03070509090402130e1e0109030504170c03070b040303020105060d030e0603040c09110703080f010506030c0a02010912022401030b04030e031e070510020105 82
    0x2180c0110010140035080c00700700702d5180303008a0191048892006000b482a4507541c607085081c0d140d9220014034400c0d40b09021000ca00205420b048038002c500c592100c42c07505220300180501c50100400903a4864511145000e0700601401103901e103500308030140650300d1042e10b8415821000d145001043e03031400d0b0101c00001e4100c41250b040c1c41c0074001030300c0700040d001240ca00d4210707001440c03601030007001800104158070310054800c3d00d1094000384103031b90302c1d038003802105905c1c050040c000030024000585641845001550014011401c0740701040d00c4041440076101c0001c0700024145000071006c0505a020001e40d812107810380d120305055240200051540c000540110700c400c100092045e0070078000d500816a00d5844403440c100300c440d08002035124030641c14085010705080640004c8140700b045000d059a6004000f07103603544443d1011560f1414003150280c062082850b800100c04525609403ea010810000c1c540c0c1410801480303050000048640305680c10541 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 283573237 1250 283571987 283571989
    0xc030f2a06040b0c030c07030c090c0815010e01020f0114010e060d02030c0603100f0b03010303020118080d0b010903080d1b18030b13020a0306050108010c090b0a080709050a14130b 79
    0x21038046982c41010707580c580441404e610705500c00d0030003403040c0348504030f40042001071015010084800d01c10040154190040c002c0d40c210800325118a40c10410940c40f44696014a28243c0340f001d045c4100d0b42e801da40740c040d850071901400300007100e10b64120010060151a00d8826500c1708054903002c455440b103901080e83c070307501016270328801c880103c001911040507506040050000101400d902d81c0d41c0c4001d401668000c0c00258015401e0010340d61041320540c03020440c071640300c5c031580e24100354000000001c0140c455500e041222141d4000045a0114054103e00305c1501001494038845591800c1e030001604503c000c0c03040e100c4c40820400e07000090441183d80200c1c860540350380b1090b5448116002060095210310400b0020083c032070950702a40c10703a0744000c0200f24108181d4400d6034260f00c00c0c801c04ca0791003c10801d040c2181d120b2800180c00500d82c3c24003110f00d5880300c00182000c200c9800c03080f900c0c50340e840351030b159180201c40c280505003601020400510824 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 283574487 1250 283573237 283573249
    0xf090c0c121409060708120907030804030803100e0c0a0f020118080915030f04030806090c040b09030703060c050d0513052d0a060c080f15040e0c030f2a 67
    0x46400d4007448114007031142156401d0007120030710b0400400499851711a8505008250007403882e021070200f5920000303210500000d01c0354141c9400007101c504051540d612503506910080030004c3c0e451203408009140450310b680c990207546104031661325405040f80c000d02c202007180550085a0515010051803240f020541c40c070942c0150780b05650b103c00c900070030b030106400502011070707080000801040000070300c0428000c4d440ba640c0c070103075510b6030f504110b40d050007540c1c80c015100003004100080310140340140902c0c400641a030b5050340c0d503032700d803641154090701d925404520000350080d00c20101e48a103c2d40205003020001e1808655143c042e90744091a0503070550162401c01c82c0340c0d517214020b00c90201641030085906846c0b1514190303020300500b54010300131801800c0441d41170080410141d1090b003000b0820100c0d90044410400907004503002c0306000d00904141800720303207040c030010341d2000242004080301521005244082080100d6441c509481c4040c0030a0710707a188 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 283575737 1250 283574487 283574513
    0xc06070e270106120204030516080d14030c090f030a1202010e010e0319120504060f06061d0405070e0a03110906010507080702010323160e040e0a1205070b010f090c0c 73
    0x901d031840d0000344c0b00390540000d03c42d9410280940c850101d4122110f030543e00c5260a03200f200342035035000c000da6201503582c047c03029030848035a10180001013009100c04080e200c022402000014003440d50f00100341020f244000a03602d0981907600286002d40901070a5068140305000300100700001110701c3c1c90340078000c041d4076540000381511112078403455030041391402500c410401070034585080c1d0000c0c140e01580c2c4907903900f49000098480c1c000c10100c65150600802c410300c08200300100002420020320311000d004503007400104a4450354100800317107108074000360060940b5010004540300003000c00341041003c0081c10000f0f05080140d5081907420b0802250714010f060314000c1075030022400703000c8072040c107007000807408840d011311580404039207070b644244074241b00b03000a0361071a10703800009038803110f40100000d0288040030064000c0d40f421900300411aa40c03040280000c1c2e21240e07070203094160a01a4070460b1250014800c080e05080744803401c180d554020520351 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 283576987 1250 283575737 283575749
    0x1090e04060b06030a061d01060c020405090f03130302030c0a1802181002010f0f05010f05011413030c1401170109021c0e1b090702060c0705030c06070e2701 69
    0x44400800c003042500c1d00060b01032180241000d80f41d18003454840300816162141e03d1a9084412880c605044049841d030f060b2180c5a0b5440058091754003408007615001c0c241c0d80c4d00344203c0164040c885824000782100030715025940b5192840c500406140c058040c14840c4114003184081000c183c40090459016840c02009a03d500300140c07400002020070031a01e03084210301e40c502145d9503043d80300700b450201c41340007040740b14946030350503040740c2c001d01425a20146901d8180071941c080c1c0200d01c403000c140c001c0c8514103080595101c0d20303841147c0c008c03038200c01030314028410070301240f1306452180402e20b0b090003090110a16a072443c80180f250050702c070360001c0c00d05804002400f078591030b0007620000b40401045800515a140c43c60840250081120034401c03a441c42d0250240d40140785a900401040d22400f28410355980400c008542c0d83c4010802ea000d510700034403e507849014543c8031244031034410401d11000d40a4203c2c046021100035100c070f0192044000340c9419112 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 283578237 1250 283576987 283577009
    0xc0507120c0f240201110a1e0c08180402090d0602070209091b090402060c060408040f081c0503100f0e0412050702013f0507110303070210050a0b06070302010b01030b0f0109 76
    0x50700c0303c01030740101034540203c1c03094240080d0040b222600b004884030752800300c44090000c60f080c028111510002600c00a06580040200c8000a038040c030140440304001040185440a21000074114100060f030880d052078010405000750f251041702a548009410050300120407005801c84107018003880341e9200d024980041002c4d5110b5100b9550503000f031200701c9410b4145405c0a00c071070741041c030525004108111010813440c402103001c0d001d51071650400c2481400d10300d8166490740008260384040244610002070248100300e0550060401c9014200c0c2410306090184d1404201e08046081c42800c019440060f64480c410380d0803c21600340904480015058101c400c150f1410300c0c9548201004204001942039484940200d216440d2201c400700300300c400e69200e0004450100150f003100060941c0e800c00c98210360f5200b00b1031000013684581c80f400151154201080c1900103130b55804510300d083d6018441d00030203000445040c0c6048030300800007000c0074568021110f0050b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 283579487 1250 283578237 283578299
    0x80d0908062e030818030705060703090b09030a020307030305030a0609050402061603110106080f07050102060108060a09110604030305090a05150a1110140f070806010806060a0c0507120c0f 83
    0x40b14140403800303940d200000c0c076504e000742c0c8603255004da10b8291a43c07180c0680350000800340b4060301100c89850341916490981d902c0c2035250207264001030403160f0140180e52411005030f8081c803015010b5840381d1560b13500c904142c01d90a08076038141d0041c0009904e00014003001d41d0350442501d180c9105c1c030844c0c0340021098541254180c1c0d070040004850742c2403110100e00b6040c080f80741800e100702c0c0800c0b962684c0ea16001240c1d90003080c45402d5681e00084042455081150401000d442c01104041103180202c0080b0b6040d034810740c0140c0002d071000c1205892840c1111001000703002c02c50781c4400820800210003903910941d1b0444d401e2155440244400c2001481b400e607a083d00502c0800880c22040c0e0365080a00313086420744201118040054030060140f28124040c0006035203000386592342c1014405554060503144013440b5075403480000050301040424060190800000c40e21201458805191403007600310f1608101020414400990042e0349101e00b419070781c5001d8100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 283580737 1250 283579487 283579561
    0x81602041d0309120d0c0209130507090b01030b180606070f0501060603020418060e01060804031116090e06190908040906080a02011209320601080d090806 68
    0x4100161100700049002511400c0c00c05000c00030744210101600c46401c8409190526038881c850003101c8070108102d1a9044090309281c511158000c2070080709411044083d254240b501e0079941c0300d50100e54440c00310070b030196030601402010b00016109401c4088482c40100c00d4a140104018001c44020601c4024070510301054402d10b604180208112521904000e02941c000e00a4030288841c90301200c0c0072600030702c81c403011581c4100000c86c1a0f42800c0c422203a860380600306038100300d048039440c100f8020900c418084030003041c401c45030480c030780f00070142030306c031480c5980300b03140c10007002c001020f6a07406c00010b039540c000200285110b103a00e0201e125009d035400a20600c1c3c5445c2c00414010030000c0c7e00c4885074001d0301c074490164807102403001510403501c80248102e0f20760180454035018001031623500c0ca5101491220010624502e0389403000c01d82c0a090258060800c0c1082140c02029150180841d100607100034a41a8918100d41524041c0c818002405a211004e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 283581987 1250 283580737 283580741
    0x10020f0904020c0102090a06090b0a05070204020d1515051309050a1404030e150903150a0f151a0309120c03071523070c060221040b040611040308160204 67
    0xca08030007801107440320b40c50300c1e00c0b6000390018403140740071b07806201010862501542454046486400003149803211101003201c5541080d81c040780c020750280052014032034076015058145044c41d0f0b00d072080c03034908410710f215044129101c9090120402260f01e400e11403400c10800e5514450f00441c0d0350b04c407131802d500117296810703440200c40e8244080c4000c06621040445440c0d404507040100301400324803050540c072170364403442d40c980d00440461000140542000b54411030114000034140b9003605040203032003688441900580c078010091003c860644a520700302c04103140800d0540c9490413100d6540c924110002c84000b202141580380c1103030400c01c448410354095000e0151a0025040402511000e40d00040d0200e01115a4020750003a56000d4420340e12a41c92003201c224a4883e00029400b50384520040164001080403a00b180c041680c0141c2c03140340f05050605e81404c03c44221a00c90610400c40c0000304020004a02d0b010b003501c4c02c5440600ca40e03039080c0964400540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 283583237 1250 283581987 283581997
    0x1101031118210d1806050403060c030e10090b0a0c0801030f0606150908010c020604051b1f020307030f0305010303022a100e01030b03010b18040f05011e0b0d0510020f 73
    0x11098981080480d240b51002c6603890981c02d481e280c80d103214403c0841c031455110300c0c1c096800090800d11003003001c40d8241e004120701c0341c03032030900040c500c1101c44000e0800071548000d000b49034965070708008010204201d6a401f0b0010542085a0031080c0002006408103200280180741074500920600041d030388000010100c000b02440544140308000d040700b40140300d080150f510748401c0d20f495500104402c0d21441c3c2c0007000e00b2050204a5210021344546c1c3d00d099000a240c02e038240b003600f410200d2410300400c980040d40c40d0394180c50010140c11000030001300701030424004100103900020304103407403002d0391205044411140e10700b07c0440810000d0543c40761040c10740b00c400030740210041007404001e981c00d020420034a0245070a882d08a00208e811074994804065118500721030940c0042c821f40490621601c9501c1d0b560941d8445440d035054001079202cbe43d081d4074018401d0040d070300b005490034100c03003559441d140c0c1c17968280303a400030700e00343c0001d035031440364100404841c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 283584487 1250 283583237 283583269
    0xf1e0c15150d02090a330e06010f200c06030a0515120a0605070c061a011101060e040809030102040803070804091b02030910090f0303020a14160902090301110c03071101031118 77
    0x580c81000c086c1841e01160418071404a16032840400319026520440c5c0e01c9850801545403841099181c01ca9184903264400b510111800340d40c40c1083c640da10714006500030300d02c0220104850403c80d05620400c076071041050300c6054214442c420148003c2254000903030088400112b996803860305543c0e500e12264005c00307040ca0002e50802d4140005020201c01d5400c2ea100d880d4081c805000310b0880d142402031103d0122b00400050015003014000d12000300301a001504080c1c3e130703404207803031500102d03011030380298041401c0c443c04a05210780c0014000720b100090410001280203074491150402c001d0150303000200c880c0c2c03890301403e000c80041c0103c45100304125507908000b51510403400c4100c588030700c509201c110b0b401000800b41000c56015455140840c94041100300a6100d200865050b54a40f195580440c41d100003030112014924044c2d951140146403140c1586038040c20756051500c0d0a2170030659120002c00d8641c5441e59000425090406070700042060070010800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 283585737 1250 283584487 283584551
    0x9062102130e040b07050309120f07050102040807140306010302090a090c03080406050d05010515031819080406020d090e06060705150c12010b0f1e0c15150d02090a 72
    0x1802d0401400120f102d5401540c0ba10f800c0d40380c0903000c80342844143c84091256000c41a0304e600c0310a0a0028815903615016091400590340c0e40e00c1c0c2603801640c0a00445e421820b010401d81c0742c2820407106030101140513048035070540d8005540c101010b8504100580e58003d110300f040310642d00d80300a1354010388a10380700e030303551003006041e0342c442c14150000c03508000000415045c180c03a1101c07240343d8400c58500756a264603500a80404d1040b03562031520070b052154004003031000080c00c2590050341c83c2c580d40e60030b09101134070341030326000d0f20010045c00b40000c01800600d225180c0c1c1000c42140c83ea551010b0300e080c205c0c541000800701c80a102403420034010b055190b00d0050110a105070984441c0341c1c1d0312030307444a01b8020341a41c07400c1c002d82004a90780030480d810341c401210010140b21410043c48a442c1440c11910f00126541542441d0500a0580a1840c2c00502d80e00031109850012455400704405103400703045903401548440840800c404420300100750403040b0491 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 283586987 1250 283585737 283585739
    0x5090a0b090d0908010b060a0509131b110d0207091a0310140106050307020307021020010507090801060803160c05150712030513021e060711100906210213 68
    0x1000d80b52410248218081405020300007008803040c0501c21810340020700b80360400d8040c55060f64103a00403012284d20266420b810194251148505201c0f4081c403c2d03010b074241c040340c1001e001c41c414101c21401c203a200c190b0416000707900045a41c240c900000c00403503004521500d008110003111642d9070315000c0c089485c1c0e4441c040e640100e0070700340c100500c0310325a40d03208400e4559210945000c4d0040e0010041c00c405400c0420489500d43c2641c03900c040580c204061040c4030044404004400d070351500300388051103620404a402901042000700401d51038403200558910840d0400715004030203d48201c00c1c040000744400051601500c440b40d81000340c624600d00b41d10049003150500188501118070074424070035142305051201118500c02840d030204000c0040d55100441504900e580b08202603c560019002851180c0300c6884000000c00c00c0060b140320101e40d03182000010042009015803028407101d0b0004240a803c40101c2805030b1140a442603030006e104c402d8858070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 283588237 1250 283586987 283587001
    0x40f090504150c05030703050613051611010b0a06230a05040312020316080313020402130305070b0f0403120201020405061321050622051005180105040c0905090a0b 72
    0x210a201e103214881800c41c150341c09a1000440300e02201c040001407040c400100280c2c040d0b0b0025800c8040180304c00241001000c9420aa450803594490840c1000304045040b9810070461780c664003170040203100201d128004100350b001c4503c41c941c2003085070b980d00901d07854808034569210381d05da0030460369032681039000f0b411580b242c07100b00c03801590103061000282c80401078810035005944440c913882c00320307201c13240d403500b02501051281052184403c01652944010f00c15035444c801c80700c121600d181003140c20044c8a9000100307000d010015800801850b60031142940d40c4800c0050a050304075000f01e0080c02150002504007100240d50000c100503143c11404031b448191400d100351039062034002c10f140c02000002e1050b4003500201c1d1040310408505840601c44295103c0c516546480d502e25101d591251070901995500c04d01503d00c9034100030615030807920000b8401d9040942e51854a441036100d890322960f5154082106480144a1844025040400c03283c40c0e0404403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 283589487 1250 283588237 283588241
    0x409061a030f010219051c090b090d050c0607080916080a11120d210f05091203040804120807060509073206090a0f03050d02060609060306160302040f09 67
    0x305814428852401005140c607014000c41c1c211820003481100c618202c00429222a000740854480900ea200c0d0190702071400c9100d07010328580501d0542c1010b042620440741003c901a54035002c20204000104c003490002402542080039844c0c038004698680500300c3c10700300050f85811030540340e01000288645c4c0042d103802090301030381c01c01d000c0c2e210420400118000d144581c2c056500003a4084134450f0061030206c02400c803601d80c044d808125203000078111044003154520095503442480280141040b640d90f07410080312085156082549444190b4015846400014000302e1140410400401c083d05e0980d03600c21828482405c10794901d87d1244620b0046a6a0081a4645014034a1000c515802c402c3e06a146c40d2084401d03c0d06010941c1d2110f417589070824008023001880c904195023402c010350044c2d014003104005000028107285001d46060311948086062107215a4081101e80d04182140b20910340c4101c80d0030700350040c3c0102e07441542001640040020741602c0c4d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 283590737 1250 283589487 283589531
    0x30c0c07080d030b01090617090c040c031d191205070f0b0f09061003060509070308040b07110a03150e010b0a140310050403050301050904030909060306091b0803090f040906 76
    0x241c40601c014135003c00111200301440c400c4800041208100d00b840c42d804e0709080380c226181030240cad491030030240c0210b41aa4021040d84000996542274509102d1b050441c03c2c050008040c060308140000c2d20074285004235207107001c1c10740107880c403840503610701400031203080a1707001403450ba21011904241d0a0b2810442c1c4440c1e101104000061003840042142480390440400e121001070a58803031100524000f04a080244220342c008008144d01c04003400040c148441415600c0c80c20340b60410001e405c441c180c50281e82450400c1c40081c182c00c1241561200c083c4c2c0000d800c4034803034040c03400b415440c003c1640005009001003080c0526a00c1c0418a24080c2c00301e81755910740c00d0010086407804c0703d0140002e0401c0c0010b0000f49441460990094001c0c03900300e401a455450708400c969243c0e1046400907620103096081204a08406a02540048204803140d00c0c0c241380c0c68480c40b800d02010b109542c04010112643c1e0f0b00d0740507100260b081072003001034142d01d502c0d451900b90b007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 283591987 1250 283590737 283590763
    0x2303060a02120a1407030b0301060f091b05070201090303080c0d06030b010f0e06100309080c060c18010e130c0c05010e03030a11040f1401033905041a030c0c0708 71
    0x20150010f0f280d00010b00680c800c80a43c102d89007226a1640d0085006228200c1140d9240d522881c0014641c5440c0b0f12120240640c014001980140906079800c48250901c805007400790900018026030b030007030f0760401100d07090308086409940340b4416215600c40c0c10790103080e503032070502c1c00310a2180d442c8120b8140d90243d410030940ca5250407001d03145001c00c45950740c0c805211000a030405120380c10000070300d13104040301e40c00c00194044480c18100100ca51410369900441c5080c650f442d0b845001110360001c0c200341c0c01c200c8610022444000c0746d900c4500420307407210070701035540340b00d44c4100840c035400c98001c11100104891084c0c481c5e00607200c2d034180608100011411854050840742107031125100421810b15105010b10117400d010070300b905055807510400c0c48056101c0003503070103800203244030b003d10312207200443c4d01b142c0e00d8042c102006802d00082c03005c1c0d028401c0c1e0801c0d00204070300040d1203684050100d0110701c030300d49c40c0c4803550240d184001000c9000003015000c03040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 283593237 1250 283591987 283592017
    0x70f1101020a02090c0904060b030705031006052a0c180603010606050f0a08060102030f040e040c0902040807120206040801060e07090b12010e04020109080d0c0b1506042303060a02 79
    0x5482001203075074240c0031030041d600040380000310b82103120714001081030140140000c1041075030390282c035100d0740040702c590340429000810402000300d81190b0304094404ea0410501300400b0818184c8009040c840c00ca01160036208841d20591040154040703042c030081031500c2c1103401014410f141001030f9003c0b4041d600740440402c541d40254180d884841c50807280d00d09010700c01008030741d10003000e00303c0c5040d03000c00c203c6d9114008034000148094100d18208440d6400c051401c1d0b05210406e41c88805c210344188010321405001060004c02c40341030500d200303042c214500004500e84243d070b22812044d8a0918000350340f4102e00e10b0b0920402181d2500101c103552030803042d070f9a109000740101e103c03507900014001d9480b8040c0c6260403500614203011907d454000d0907240000b003500703642c041809407e6020410901508440c1c0c800340c1c6040900b100d0b6682008110280203501910300c00d40151400100b16480c01211000880340003003c5454030b0404007003080003584421151f402486d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 283594487 1250 283593237 283593263
    0xe10021506060403080a0c03090f0b030609090606030d142101060801060e01050906030a180503041e030b06060714060a0504061404050a0b06040b0901090509010c1103030f1803070f 79
    0x21402c2c00544007169040380e0100c0c5007004900c030444038a450f422048040c403094034004511410f4101740c5202034900354060903900e04000e01044604d050050821109500110810600751800705080e610319100d41070402c00703100c110b0415040341c09802c070054551610080d012008a00c08200f8074101c5c2d54980381d4840340d0343c80da4400c1320505000720705103020403020444501c0e40d00b819801540d004144050002d02d0f030306410b2090007201203142d801d40e415030001c0b07018090518031040c202646e10150031280c12203031031a5680c2410490003801c10b84580e0f4081218400e110b500e050756114002c0306803c0d02c200e458071050810080005403001c0e10a545460708100201d4012508030b8020307a080b10080042c0b08699441e2008040700808440e0080c0d1a9449c041043d104d00703c4090181c00319190101e1a8941814100c0c2143c0101e17005d034041001120880074800c101100f200e40115030209100c41e41c0d41d503da042c8000365909162100c2500c0009000c40c1805100c0e401070302802d00c0751000c25030032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 283595737 1250 283594487 283594489
    0xa02250c05190503061014091b1b0f0c13062103020109020a0f06020606010f02031602130c030f201902070f12020a06050a0e040207050a08070f051203070c0308070e10021506 76
    0x60888001c9d00c0b24240c1400c403030004d00c401000c1c014000d40000d10036501c0720f9084c0200d0520f4040202e04030598401040c42000b89008241989403a80340c4004012452508500d4440607050a0f10204503a104048680a051007034010011458000c0c00e0039a84a81c0c2e800e01c10080340707041c804c40005000b0400419504d610900300701030800ca9a500541c2070410348052480e80345400341049074421040f940c40401c200d01805001c025989544000600c03000c01d2000c0030945441c54400c8034902c4080030100080c0c2a014180d5004001c01039a2000361100150140e00d044901e1b08040c0c1c0ca2a58100000b40040d0140b0109119600c2600c0721459156164402d4034903000d5200743c5004620304031840b11080c1066070150500c1d9001c0d500301c03034a10107286c82d0f0807050f500000042c3e0b5692900f8a100d0280301d400c0084072003035000146900d181d49000c1c40004d0958808000050030007019001040d45140300c0c00b503e914000004281340400e0b000000069902c0d0741640ca6030240d0711000340081c3c41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 283596987 1250 283595737 283595749
    0x2040219030f18120905041b03050c040501020a15060f1403010b0301050105090c0c030f0c070602150105010210240b030717010e07260a02250c05190503061014 70
    0x8840f801440b1101c01d0600703a070303035485040c80c0c5440d04040007081e030800034042e56240941d10b0346514946240b210180c1098004054580041082d8003e60f4200001c100f266400a6010611608a229418800c85601c0c1c00ca0241c0015423017490240b00300314001c40c040c650b1740c0304541c03000d20840c02002030094407001e140c01d85100341b0655511025401c0055600d04d002801480a0b1201000b62450100f036004000ca9039081500141309070380c4104818071299030108010b81c1c0880c41c80348942000e626010000f5a80c001d000400010541c40784120960035036082c0c0340049031704041c40c204020b207031102c0081c0e207550400c5034284000741a001c041908144001030f101d040e59407001485920790f581d801c06032407014840515034020854801c2a42a440360700d4126409580d03011409684d03101d4100990402c00d16030b01d1068a8842c0b00554880050340d14180e00301150403e8070301509024a00107010030a038244d074003040d05800740008114210301a546820306842c8401c0ca00d841c40f06040b400c1c080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 283598237 1250 283596987 283597001
    0x9070e091606050a17100302010e030f100912080919080415080402040f0c0c080f070c0b040305010f0c021e070b040f030b13080a030b03070b040611011d0a03081302040219030f 77
    0x41354016a100502c05540304980444243c4130141c2164103150400c03c2d400d140220401c4503000c42aa113b02907400c100c801d10000784168124079040a01782043c410040d240d540140911031030544c16000d120401810308281c80c014003600e00250340410702540c3c082c0c07560300c0407a8100d129900d401946a0111410711800d20514150390b11012051758036035524040d80d001d2402c1e0740700d40c130702485460001180c1411038009803812a81c4141c655180d031511500f95015141c4000c1c2540c10318860380282540028078405c0c0c103000419414424010074081414100c482c0c000442c455400074002c544a402c0c0405102120302c211030900241d6103049286400540e000d40040070f80c6401c20500000328440d40144400c00c0e00102034501b06036640ea145412544158810008a103070065107800740d15003845541c0c4006520040b01481111291005403200d050a10041c240400400811545d00c0c00e0b203050f0400301d50207002107607241040a411b42c1c80c0d6203501d030ba07180064180103891184800e24001c0072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 283599487 1250 283598237 283598251
    0x20112060e160219030305041703041a090c090606030a090b0c090f03010204060c030804140a03110607031a060f130b09091005010e0d150507050307030b010809070e091606050a17 78
    0x40104d5125a011400740c00b02030810b684c03101206450850350b211510043d4051880790320748070324040d01401c010f2450100100380502e41e401182d600380d8152144004e940e13000c00101c1d0100d0f513030f81e01c0e146110001c005149000c2c249503559410803a0f161001c8000702413040c0111107c40c03401c0015010103080c3c4c4101d014040008002240c00d400003401140c0036a0840d200343d58144065001c0100740385069091001030300018172134000b100b000d403810300006400c0441480d0030300100c2c840900e106401ca404688141c012a000916a1310605071281500e032411f01012444041a0703a440d0040c40c1608a224030034402c0200c2c2000c1071006c04208086012140306071aa428000850401c20840b014040e43c107864406d0942035000d44103401e4495184501c02c90748a5546900f0034180060454508806090502c088c440501c40300c080000703551011201101c90403106542c032030180d1030030080700400f40c0522a8140c0c9001c1215508503019222890480d41ea01a01940c250170b0008000780130361f0b00c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 283600737 1250 283599487 283599523
    0x30405060a0c05010c080a05090f060f0601110f03090405010b040f031b030b070305100b040305030d0203100314070305010b10050901030f180b01050907080405060112020112060e1602 80
    0x204018140280a0a8907140074203140d9411840c1e40c9030070b400d48001418080005401d001042035030081d9204240c0c02c42059070040800302034101109545480107446c0b40107420421001030840d03841607149110521200d401e4840c120641501f01d0391302d0300290000c1c0e10907802c1c03600110309a400c600555080319140151000d04034510781ba0710744041031002c521940071000c1c1c50b020010841c0b000510f801840c242c1d80009580c0b811603000296200540c03c00c180c0c0100400081000c41d00000a84800e15584c3c0701c01039403034031058001000d250345c036480100f0548104a090070348010100f80c040480b406a0f0091000c1d4072040300708003000380c92191503004210180140001540f00e5448101c05201c21000001d40029841030070030740da80c0d140b03000c8891180407801400182001c00d4856080703500b0b800c10384020b080540da0991102c1c0c050094107040c0d00d040e5284400d5a11800126460701c5450004124440d2681211021b0800c2214020110000805000e820300e2002803020a074004240032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 283601987 1250 283600737 283600739
    0x70c0308070e060f03070807270303050f090a0b0706060e0403050703050a1205010f030614010f03021c06150e090a050d1202041a190305010e011214102003090304 71
    0x142c03400d020100d40d00e50803220030701000070b80405001c002d60003540c03a034440c055649070400d8000e005a10b685045601c040d654440d0b0040c90807121100fa0550368141071094584074181c440e18041d009214141d42c2c098413010000036540495001008081d000301c6050100c00d4940c20300c0000107006543c028001107003000341601091003040a45a00002482e04030004034980c407050064610030303045807020500c0c0410810070080284195007010062400c0c01ea903640c5495000e9540360f500d44800b0f03004146218803080740a04a044180d140c6500042c204540c1800801d09031440e08680203141c140c144020100350500350010390f0720f002075031110081c8404e02485104a0f40d05071700303085000c1c2c110f40911010812007001004c516003041503034110390b03e030070841c4000380344e00c00304541e058107044c64100180b05211111100c0c0741540d102c070712100c0d05441c440c0703403180696115458900b02e0f400f0740110303140345000707503005038100500072412090300c5c00c00c05030b0b45a601d11040d9040c01696204000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 283603237 1250 283601987 283602001
    0x10b03060111030a0905011b05070e0a14060604060c02060d05040606030c0509090a0201030f0b03030c010906060506040b071e081201060e03030c060a0507111203101a0d050a0e12070b070c0308 84
    0x110217a040d008410020a00ea070395809113404441d410be404204194001c204401620703200d100c000b69500d51000145081c10070101b40d19100328004c0d041080307690350180003552140780c112403013510595800c111510301801e020005098030700044a0460181c0400610340c40c0c1020094060001c16015224420481d8015002070401000180c0d1340383e15401240c00e0340d43c040c4003809140c140b200c004030740703040d0a241c03810445000f50000381c444d94040c00180301c2d070540e080c241c50350300da4032442c860003081c2c0708006420070102e2014024080c010018007026141d800c600210b0403925182c8036003040c0c1610720201a00d078040c0004140442d4840d00014541341140d030059500010769060403800c0c9422a064141803080d000308004c50380000206011001c61002134000c010001148030405244008052025610402081299458070f400c0441d82c501041e0b0b1107a0380c1c0f00c42c0c0030f007280c0c0d07001900145c0f0b00703007504812007e44a200036680041c104602600c0220010707a0325a80c2c6050550303400c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 283604487 1250 283603237 283603247
    0x60f0108060603180c060a02030d0c0309050a06020d0f020a1106090624120307051e0a0c09200412051e0601050d1b0609031202010903120f020d05010b03060111030a090501 75
    0x2501c180140b085e102030645c1529503100500101c00c0c80c1c1d02070343d95124040441c1060b41d9074141203804161034946400c2c042000450210701440d4000b002683d80c05000e021000900900f149002c0001e2000881d00440c9402800101c07000300e802e4213032036081c3d90740300e213940d21411300700c0b04521402d8a218103200c01125003440924000001000e420740e00c001c07581d90728595044030504403441d5009401446010901c181004030004542004110780e00c1d040e5a81d118030320091181c81099500d4003a40c41c042d141c0035481c062a884959901074035142d840c45005503a5100c558151841e000c1e01da001040b441e11401d00d21400703010400140b680340d11b00360500c90341c1c3c50264401e48016803842d18103a00e450584c20700e14010201a514005010b003141803200030140d648a000040da85000009400a5004804203a0300700c110100000c070910080d0009000c0d208580c00313a030402e8074240020034205008005503014440c2079903841844105006000e41d6840390030001004a981501c0401141d0311035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 283605737 1250 283604487 283604521
    0x2070605130b04090e0f030c0c04020a031d071716060f05040315090303061e0905060f0a030b070f0207081b0a0b160308060105071a060a1d060f0108060603 68
    0x18041200442d03980c00500c0a20380241d0440e014094888982d844004410000e8400001603440918500703010f02c0030444e500c07a20f4000c0ca0b0300450300480d83e81c03400c1c0d00075030081d03016251072800c40c0260615204c407242c80e8541030054a030401f90508812008890010b50704030300e030704504054000181401820740d02c405070400540d08000080002000165400c0484d01017241841c0c804141d603140ca183c080c06841c116000208002d40e078100300d0210101c10f9182070111034040000203584c0d1030300c0303012400d2807050f0780c080350f0002d08100d000402c10103c848080d108540d42e036260760010000c00822601c890b100d2207012555882208041c2030314444c0c501d02d80100368001c10041d0150350320468100380b0742002c10140c0c131240c9a2a150403d0503007214945038040000d20f003180c0380c09602e07510100d00520b10100d0384000300340c08000036443c0d12030701584c6014107100250042003030007031161000c0890301291200c0c00b07045007800640495010b40c1440380501c500030b03c01802e607540d0002250540da20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 283606987 1250 283605737 283605757
    0x21b04050c13030602190503040308060d05010e0f1c08070207060e06160506040201031406060409090f08270919051e0a0c0e0d0302030304080a0c02180103120f02070605 74
    0xc10060b5486690300014881d004510460300541c65103000d0628210000005014800340030040003048000b0b98085405a880031080f20040c82d4200c0b1424190300500c09045107142c140315201188280350b800240a142d41c40b40741111001c2c0740000d00701103d030307514261035103001360340140ea050200502604050954001c040c011030304041170904e984403c62020b80040d1156004402880203650341805030f082c5c0304e98080f02c040911300f4160003040b41c0d072180388075126111350759580d180d00700460b079a1030a6409400081c134a131503000351400007440303e401c40d680c00e10002c0c01c40e4003000c4605044113254440d0031880280d4512030403400050010341801081c0c20f07442c0301c41c00c180100742d6869503400c9009104000b00050500030220015105880c0075821a100780c2c0701c54540e8000907800030803241d0181d841402c00341c644021841c01d450200f0f40580096200322034101c211000a80070302c0030b5040f64044c020304c51010101c1501034501c00c40c1041c40000507080060b042c088a4081c1d0f00801010362 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 283608237 1250 283606987 283607011
    0x7080d0f08180304030c031e0221030906030c0c15090a02040b0111010c020601090f0e0a110d050105040503090414070804110612010e04051606210b030105070e10021b0405 75
    0x518200503043d40d0282d00100d40315181500c0507c280001044020000145040c20104424040c0c000409048034045520f0b885000c119410710100028410743e01c0d41030015000307a0b203e04054004c00c61a81240301135129620075036030803800303c43c5002c00c503500902c40c26001d0040c00c81c0a40900000e070203079408042c180072201122120010007442a500140312981c060f116650404054005640e121400000c20350309180088100250129500c484c0304c1e072121a42a02212200c08541040e00b0024040d100e9440e000400082c00008002400c41000403135003040302500a200032018403c0c151400e80c00109020001000241544074882d0200c1c00104082c4c01c0c5681d0400391404010300360001001034008001307000030400100001244070410204070383c1c2e840e01300b8a000b004c541d0445001d907007a2403104409403260303241d58004951034102500034071003450080c001610031281d480403907000e0102002c00c41c1c001c6101042c840400410054881001001c40c01004050200a405110400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 283609487 1250 283608237 283608271
    0x24040f0605101d0a030c090b030f030a050403050d110613050f10061a030c1801210b090c030c0d090203030d0c0807120522061e0e07080d0f08 62
    0x42d49440c55a508034600c0c0e0758440c81181d0345249143c3e640c04005986019045003041030001030000080c400503070300c4619000a2020101c1e000910b4a2001490700c8000d0200043d221503043e40b0600400c1900c0c0654211000307007600a0084403a442024800c08050f00301c04049a28550a04144002c1d1402041252011114072400343e06141c40e81071014040d903a101001c20102d8030b2203450302c01c1c0106088060f8210700d80031500070f003184520108202d500d001202da002860703000e0186240d1042120240c5540c00707114920183c01020b8032a400d0740724820800004404266940803641b1a1144d900100c1c2050710007041c0e500170b05400300e0101d90600040c440024110a14403440e401c000580d60b0f01d4140c2d05007010003802100f45881a00303480c0342480c040156240d560849150034007401d1a20100e07254290401c40010060300a150b4065039644030745a150b0340d250b81085028064400680756100e03607070341d0140e98034000300a0b64400701d0b0082074449040d90141c41c0c0355500c249841e0b0986041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 283610737 1250 283609487 283609489
    0x4090905100e0c030c150316050708040b120a0c0e04090c030b09031213051b0103021b0102031008010603050a020405090a0c0303050d0501050111060f0a060e09070e24040f0605 77
    0x740e400c2c2030030300c89142e0102d0030085040c5410045004081400c2c0c4402c0c118040c0900e1042c2640300082c500105030810450215031144500c0444031869003100306942c0b2180c403400c0e880401e600c02c40f1a0304494501e000481c001d40000d1042e000b010070719440f403038001c504041c144000380ca18158180c4407214202e03800004240b80c440503e1080c0b2941700915650b05442c58421700c201d03409803005503d400314961400001e070001030341490005200c840200c8502448004030040d00c00c0308031450125884550074014a801500554020b0360b122140100030750b1101031700317402c80700a07200140c425800b100c450005810581c2c4820b4004000d8015500d0100c8661103941036030300a0b501c100c1c0060301c00501c00c404540184213150150100340790141c000e079004207400d40d49020150044014030041c1c030125001845a42c002c1d0700070424250900076070701e008002c140d241c00c0351b8420102c441145c0000161031a618002c0c2e644440b9810303003050969600c0e081404000c0445001213103000f41e54103030104072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 283611987 1250 283610737 283610741
    0x19051005040905010b0405010f03122d08010305190825080a0203030109050c0f07020103050603030405030a140d0203040509010b0a03090605011e08120f07020d02090708090706020c060409090510 85
    0x79500602c008901d03401560701b03110403950142d205058280441c0700c14000181140450500541c207843c0041001e41d420042c444d101e5004c40c0a00042403800000c0041c0541115a0354100da02440c1514025940c04014140d6401e40a41c02080294100036256010b5541054004e1040e140990b0381580100760f13817660704681c03001c4000030240c2e002000410007201c030350040381e901c51000300c1c02600740760b10403000241701e000c2c41c42c00a052640b100300141850300c0420a9a00512000b0119440750456040c80c608044400e2407080084c001d054240f684030b4000412182180e5015201d002968a49030314070704940c22110344502010707119420340d80410100d0095034045c0000584236003001c1134200050101ea007803540008043c0d044a514042c81000802c02c0c0c69040342c2c2d60720020741d2182241b00182e60604c0d03101c00258032401d0401807028050b40469054030806059003211041c584940c01640e45141c8081c20940c407001c01c11003444114460780007408864441c1c400c49242c1ca803110b10040c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 283613237 1250 283611987 283612001
    0x100f0c0c06200c10050603030a08010b0306130c030b1809150405010e010c09050118180906020d06030503030f0108070b0d0e030d06080d030c050414090403020712030e01171905100504 80
    0x24031350301c86000c0d02074100d400e100c1c4a403c03001c114000c5107000110200a49010fa05200310601c00d100407001543ca03444441c030a107544074070280200040a14108090010403c00080f64011200d040000514004a81c011802040c0d0701c40204100c4c0b5070144200142c1c440100100e44035500c0c3c01302c1001d1000240540d01540a041d01c034211460308140c001841c00032070030b0342c03490040300d42041080310007040c010469501c4a104000714040426091940c0070340711b000048200e03986440c000106020021000c0d601421402c4045000e90b6a42c840d125a500082e000d4007013a28810880720701d030b0358460f5001c0ca8000340c06005803414106e4a4000c0c0c01110501c0e444503d81c0d4000d541203c0c05039505109032200d60031581015401e081c06d1400d004002844c0744030941c09607103035002140a060003000f070407005013034005001400301c54901e0001c0c885041510000d01040c1000c034060140c286045945100e622031002c40c04044900a04460251101601c1c0040c0703c1c00104c004210f07a180c42c0a004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 283614487 1250 283613237 283613257
    0x705071407050111030307090515040e0c0405041103011401050d0b04051303030c020f1c020a080a090f0504272105040807060203090a030305030901060b0408100f0c0c0620 75
    0x1c80c11516003030002d0003154490240c00c015403c20010007407501c0e0804e04074000d546050301d000380b48040180d014800392003a03801c280b9259007041c0800c140038000c68000c02c04c0c1c0c1c0c1e00b0b5030144650310b8200e0a0040d580802c1c0240c4180001021190300503502c1203018188000200d00b0110b040c1a100000c03030105c44081d00c0710f440082000c1d20500c14160907019403201d05200d40b004010303401500b00c81f1511001000780b102c49164100442030030b800e00c204154070f09140c09c81860790345c070020000f0203848029244203800340d503204521300107030070704d4103208103108032003103d20451021940f5050b26403840041001280e1000d000c8403928840010943e50f2100707100151101540c40b41403142c410314014140e4840400c550040000c03e819031203901c15503084a9041c100039071651103000405014110f250004901044041000910b20b0030014a40d2400ea02c1d60300100301c07690400d07046409039141d403a6039a002c41c0700d01d20351000150060740203000141ca102c4d13602085052200700c80b800c95004510745 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 283615737 1250 283614487 283614493
    0x90e040602030702010b01110a02060d24080f010b090708180105090a051614010804060b03010f02071b030c05060c0f010f0204060219030822151b0507020a0e07050714 73
    0x50259024420080100004d082c00e0100c08080b11030249c0e0b680c00e505000740a8000450301d1784400e00541c000d464400311072141602e9907890441289182c0c41e05124240c03641c0700710021003881c040103204042074601c02a080703400d079a49441d4296403440c0068181a90b0980c6203074805000002803141c203000300307a014040c080c00411400d1186c5418160030303101000e8401c6c80d00400070000d40410400481c00d0030b08000300c4e01e943d2400c01c6030041008102d200d0f01035082c0b1000001440856006000082c4070341e8940c080f1800503400c03a0b0342c2d50418000208018482e003070920007450040c0150a05c60440b01c00c2703d0120040d4002c05082d20480b10307401503229000701e0300344030301070301403241c1880a09001e048040c014117944000744019805440c3d00b203001c02c1003003d0b168002102d8a10168585c100107512905038810560b00c1c01440c2c442c030b0035600e010710034105980c458803410480300e54580013046028807504000351200d68940250000041c4070080045a00258804280c00708200d00b400c0070f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 283616987 1250 283615737 283615741
    0x7060f02030c0703060c03061409011527180e0a081e040308041401080c0f07020a0530071a090402070b0f0402040f0c080703270506151906050703090e04060203 70
    0x40c080d23440701c0d0004c070b813034044442141903503407560f0035403d045590f0309180030702c00e00c000c40d0b0944594482e00441ea030321202007209180c810720329030003203070841c3c00a44580b81a800007040c0881190100206141079400c42d180c4603010409440260140e008054038403e10040c1000900307682d90b002e03a00c01c44101d031012034100060003038003104440c0003d086c2400308803071a014109104902c501d248407800c2c0f210206171407095441e00d101d25000340001034140d01b6061418260341c0550460503a1400314500d502c1e1a480d0401c0d0040389110456040c0d112403502e000480d03007140000d4010b004001d820650070b02c1090b0104610381d240c1809054149c02502507401d2a005100a03510300b42800b0400c2410521411f02c80c65010060340e90015091400003001c030850781090601a1000041c8040000c0c060401002e100c2c000c16001c6c060b04034200c000c080c00c2012024040e10462131499460003075810b0000300b06250041c0020551139220b0f2821081c0b154070f400d56401540801e540607a000b640c0802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 283618237 1250 283616987 283617011
    0x1404150f090b0a0e03070623030c0f0c0a1209150804061107030f1106041109070207091e05130807031107152a110411120a05090610030507060f02030c070306 69
    0x6c07018000c1c110628000c02e103801152a0940640d5a040d030009001c0800000103108501c2001a501c80c8946051030f04d40d03ca400680d0241c0d614517801d030545110801030155003520740038012440840b010b0f4400d0a01c050380004003a0303155803004000303903429521040030148810380301c1c000b01401c074425113844221114840c4010000248291080d0340c503400b010a020109d882180c1c04a19990111010b44113036480e020100c0c00d1140350381c00009c1043c2807290358401d228100b03450151140850170104981d80e00c00c0b03100314854032500d80281c41024100112000b081c0704400004455502d07600b260b00d41551103014500300a0036a540c40f0004000060b80d071a1022529010024400c50490100300c000240c3c45400020074002c0146118550769000c0894820740c45095401c0340c4600c40c5622100c2c949040c0c198043e045c00c0b9186a00340c003d07a00054585400b0502d0201134a405c0300085c0581d5003001c81c150b8514401d810b40000358401400b070302410340420011400598460040494a0034800c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 283619487 1250 283618237 283618243
    0x1b1819080708070b0708090f0406170c01030212061c0f1a010b0a0f111006030501050103050c09070c03140912010f06090902031c0c05060a020301061404150f090b0a0e03 74
    0x1800c4684190040c84007000340b84030391303803d44982a402c800c505940700c1401c0c0c00141d9a2a0200559800c1800c110300080c201d404008080c0c1d0302845c0d0000d03a003143c0c0400c0011400c80c4140500c0702105540c030008600c1034241100a0600019421402c1c800701040d0b444044040b85c1d2240c080364282d25100c118540180f180c0741071401003c09070429403d00000302800707404500c0342d00418040242110800c6203803841000310070284440340d101040b5494a03400c100303000e40350134002501e00348610150b81e081420005c00d07491003000256600d02d241f0340301e80e40c2141c407046d903c085650000380130302012640da03842c8220409051081c00002600703000401d02d807415101c1d150f01000086242401ca2000750710003007800b80c1050351854058803000903a1005440314036009030050005c0c0315650811081e200a40d00a42c140c440799100e2848e00003901220007900d01c92401035000b1140144c9290f581c143c003a0442d003c089400341410981d481e16480c0c041629081520f84c5800510340c192408441e08082c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 283620737 1250 283619487 283619489
    0x70203010c081302010c0813060c0516050a090504020303090619031407020a061d12041d19020318030c0a14030c06060d1407090209181b18190807 64
    0x606026000e40b806a02e50b030050f42401c0f4000e810300c00d490301107200304615030048402c0308809909103080680c42e1280103081d41c451030001c0728240300d03074030080600c19150b125038812903800500b8580c0d613908102d102c10103420041c008030780520040c0080700b9256074000103050304881b8044d0f511004000d03850014142e030080400360790600760440922508980c041a01075106d5000140031416444900c0084100b00d04d01c10310460b1402603c1200040320761702d90040088807820901d45040440341051469044401e0740c3d0307510841171044e9544412403443e0050741d40600c0384012103d50300c000401c19800d6a010422103610f64100480c11070800000e03074400d1541d00c210100450404014411040d40c690015201c588034002c41d103881c808210907588090301b036a48448c02c1e41c1d416035560900714043e401030002d85204041c1d00b00e28942c14580441c4d050721031480000c2180c101d01d20020401d601c0e50042040c64014140401525000c0d10340120401c0f15841c03103101d104407245068040e504100607 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 283621987 1250 283620737 283620761
    0x2030c092706062a0604030818030414040b040e01020409060e04121803060c0905091503060a0f02040b07080703110f0a1b081c09050604060503040f050a0f060207020301 74
    0x201c450075603034040000c10180e62054054070407607a1011800410562001d0000507074411808000049640100224501d801140710303441e0700045c4c0d15182300f519483d81421091782240e034410300040100e6601d120311181e403113a001d40b0004500c0c114101080503140000b4408a080c2c2d00007030200510380182c45040001d002c10780c2d11030740506107981c6004911880c0f0750341c1c3c0300304007003401c1214907444820b85440c029175004200300500c2c2c0c08038001501100140c41100d02c5440c45000044c5046034000c104d15541c84014003420303643d138405c3c0c080b034010000500d80d071070250781c20b0101103103480010b002015a603024851807600c9140d14a0300400095019103145002e400c1181e9260444200084461015510405170f07441c8910301404124290300c80ea003c0403492280500305114203078000d024420b0303600c480c0d450006e0300e5125000c3c04101d110754030403280058820000034020414403a040c421042c418011b032102401c0c80e4846400c0040300c4402903900360b84c000b840c42c0441c9800d00c1543c00c4100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 283623237 1250 283621987 283622029
    0x29010804240b1e060d02030c0c100b0a0f0e1f080a0302150604060503060408030a02120a0b01080a0c091802070b040c0e0609070c08030a3218030301030206180402030c09 74
    0x103024022541383d00070041c07107030305139600800030440c042000c0d0250789140a011040723070040d07640d000207840070b402e040b82a02e0041e00e4040d40425a540d400c0d1801082c0c03100712140c0c02c840e440322402ca01c9201062442800350700269000400c0310481404a00340250280c0d00070084110b20005c000d21440d00582900d00c035500c0c08008100e2520302251495110350003040184c0c80351f40300c2940c0c8010b071007402e00401044995000f045000d0141d5441038002202c00e980c0e0f402d0760740d42c2c0341a032003c8480b04844030300810780c411030030084d481d000100c218051100d10401b50601005607140840d00c8400d6408484062030130109000819403e024507a100310100c41819050820301005044075030260f2029101e028000001034100c00190070024107580715107c200f4001c07141c80010880880c02e2680078102d0078113100860059080c0c12400e07070381805140051441c41c1d195908000241d408032108001280884955090319520340c8090f43c07040002003c80c550b503c0c003400c2003116904803e643c040b800e013 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 283624487 1250 283623237 283623289
    0xb0d0506060c1f180606060f020c1309020609041d0d0315060507020f0907030b0112020c0d051b060c1312050a081c050112050129010804240b 62
    0x207000200c1c030300e0452507101c81407090360051542c5009031241200281020340c00d040c0040401050394000411200701e03a40c3e2340688001814100e8070350801c000c801c3d5204000d10070042451205070700c0030490340c3c4000c1045192815060104c0c09895030040f110038501d07036074400d1030b0b03d8107014000d9151540c01c1d031030108580030082008051159450081c0d004003c4081682001c5446142840d181c181c1c0040840380c1d1480c7c45280100500003500c0203900203000501c0003080c0400c1802924200780c0300c4130182a02043c1000300f1247c40d080ac0d40c4141c0356501241c89a05808818040c10f402101c2029116076101c1988405c0070400e40c041e800b4001a12400d50600003107580850849001d5a2120f0015510010140b05c098050341d9115600071041c0b0340800040d81d1680714980c4100720784188000c0c05001d1500c2400c5a448944441000c1c031504509030100b559131107040c0c1c00b940280708913081b0032100314041914000e07039a180301c0b0390440341d624454142e1f9842c0c54000000303031680181c8114154 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 283625737 1250 283624487 283624507
    0x90606030405060106080601050f0705010b04060909050309060d09150b190e0f060613080307060b0a0617101a0901202802030114041b0501050a0e030106030c0b0d050606 74
    0x659014417680d410404024003241c000e84c07040084503000c10b00900e2043e10342560303040c032034001d004201190f8491440c0c00e000089a244500507004015003200180d400c0100d288180006d562140820720b840594880600c4c0001c0c0040320502c084107442c000001e1002e00c1201442850307484c12004066481060300108415540c0c0004a070380007800d9400c4214544958021407082c1c003a41c100d40c046817650310004511a04008050040c071402014140241515482440355800c003034040c100c00104100540035042c0000b20207141c000c0c40c51015210615070b124000d07504640c624448880c200000a0708005543e800f000401c2232192085201d5807a00003032040075900e0998001040c00c001213400261404030007a891040391503005402030010800e0303010190303404041210211600f1015880c0ca42c0740041c0f0342414820b941040c3c450705d02d0a40b40500c10303540c035403209000a6241d900c0d440044000b07024404540d00401d0000406074554507100a40000d882c0c2c000c0c8041d001c3e030414410b031001d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 283626987 1250 283625737 283625743
    0x501050618010c11040203161206051c080d0c0e010e010f0e1c0506090106030212010c090e0a02130303020606010f020a11040509070b13051318080d1d0c090606030405 73
    0x301c03100b400d0070401880c01d440c1041150501041c01580540f0200400a0f441c15040c600c008016242c2e030b99010207600000740f101150428082d941e04024a44158121400c490580281c400e0044160b1810300c0003040c4003505440100740b0380400104560300040495170441074404c2000c1090a003101c0d498070507030000b8494401601058404c040600311486214007511a40740d02d01d0304482914100e01d043c500282c041c1c580c07031108034007542403100d0a282081c410310aa600c41e200c030b60307107124101e40f82c072800d28518000a04110070300ca03401c00220301000001c150750307030045d4400d03005021549058400540100f1802180d441036401c000e17900c0c3c0c000388100b404600300c048100c80000d541d40301c00310b00515000003a0401e400181c03000958543e4203003903e800c1d504451003100c440c1d0968650b0704106080c1c1e0440b0600001c0322188062400004200c040902030398542c180001650050803a806040400101d96140b55600601d03018292400d10004003640f140081d1085071442c1026036441741c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 283628237 1250 283626987 283627027
    0x82401050906070602040e0403140304030206010e07120f050406050c0f0904020f090d031e0e0102100902060f120115031107030c03020a170c060901060b040506031909080304030305010506 82
    0x41040340c0094600074981d00e50b41520700b21078000b01c045450710340326000c40c0c2000100b580c09402040c1c1c0601c0d218101c500e290102d83c03040354198082c0c00c0d82c0e444c200d08100c030200b02400316001d0018042884c41c0002c0a4402e41031941d4489801041d241094180002200da02405041d20094100908814a2029411203c4100080d01e0040e5154910f003100d42d06070041d00525540021841009018107500000c9034001c00310381c00c540020131407603000c15119482026022400750f004120286044520796000d104142e0002d02117070300e0302101c40c441401580c008030280c070710303078014400520812906444218880000303003020031181c43c500040703203c10301074017000408120248404d07031f04051083c040340d0400c035400341119011020b40b010781c59107a00000d61200007031156800158107142c050203600211078100b43c10615082c140700a000071503100910b0004482c14403030010002d28101e01c90101582d0082c60880d40340d040916005050f1241030b4401741c4070300d2003030100035081c3c0000410b0329 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 283629487 1250 283628237 283628239
    0xc100906020307110f030d0233010e04050a0503030a060f0b040b160501060b070b07020f06060f0d03030b0d05030405031b0112020a020a0b090f070e190c020f030d0c0824 74
    0x76900404d03140040d51803410b400545426001e641c1d800040d00d900004e1510540ea91004096512485850400c04038004d001d0000190340e1007a00400882c44240c580d17642280c0520182c464003100b54840340d26680c800d03204100441d542e400b0401204e071080214401500080c00754628141c9051689011800b4400b1030f01140034003a120340c0c0c10001e00350311060082800044132602c0b0281c504101c0300084044036540058040c05042200d80100419260701c5440004e245501c415403080510000070505041101495034a880320089545d41498a13842284260300442e40c6604007030505007460960074625103100600388407800e140e07821500ca0120341081c1c100041c0c980d915100e0491a00300d0004024012600350818000203c0000c1505180083c0801c112a05c0950f51170b0107200c0040100e6080382c0780d035031011440c10019035940042d4003054181c41221410003040002c2070840e840011340509984e508c2a05940003608410340507840401360040d2440c0d550212204078454000d1b940c46 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 283630737 1250 283629487 283629503
    0x1501090f030512030c1204080406110a0308070e120105090a030311030709030f06093002211303021201090506060409231002040306020306211e0a0807050c100906020307 74
    0x1c076403c0b80c1c04260352030030442a0002005060509104c16249d0183c05200700080144480f00301c00680010074400e551b92640e0746144980e1f54000445480e0400d00885a00540c440142072216809018290045003400090600d106892401504994054402646090041c010001d5580d0400b0040c011250007082741c0c6201e40480c6010001050303105001042c0940c004c10413050b00350019580a9045481c1c44802d0303a5582044003643d0303602d0038440d000f2002c059481c0a48462040702c006d020345c0c0d010306a0800c1c00c00c0c1c40780c1c00104401c0603524a156180e55030000756040c04000c02c030080c1c00400c1541c040044100945507000d080d508005100500c0410084404142c00304000e5000241f4030f24204544503a1a8601040a54000d0365810710460020002591080c4460781c60441403403002c0c018030490102981c40b84481015009032010b50195902042c04501d5240060090394810b4002c0c0104a01e424100245031018400303040410000007401c1c0140398001048602c1d1039007140305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 283631987 1250 283630737 283630741
    0xe0d0c0309030b09031e16080c011401081516080109230702030a02010e0102090f0d03030209130c0315050603070e0409021002010c2601030209040f06051501090f03051203 75
    0xc1651190159440181070703500d0b0790200034a0382c101101820075007100c48216030301c11440600018041c000c0e1026161400c984440310000a41c450000342090740010001054440301c0101d40c0c0f0586000b40c1c40107240d5081401524551070221160a920000316036050303041d001c14080040c00d03680140a040d01c1da0359696601050f004a100500751040c84c0700c40415558640080001d407240c000340c841e24050341c2080c01706101c817034042c001d490720903402034403407140ea103124410000c1d4804c03a00016030616a003085070400c207858084001c0241e0300b45c0d40000c51400303802035006044540100c1400203131a1400005d03c040d40d200c0382240d07084405031918107a8001c001300090b00a1041040081d0301c01c00b00c0c29401c921680640150003036501c0c0b500d40b200c074102c00c80c5030b10303c040103440c0b90380e00c21440e81b40c010700040c41c00c11902030304640101035203000504a99101011a2030070346007070070b000b00b80503020b040035a8040240d07030160070380b983d80100302841d6980390f030380e82c10705401c00c03a00c44200800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 283633093 1106 283631987 283631993
    0x6110d02060f0402010311040e04030305060a0e060d1401060509090610060804031403040f0605092a0a03061109101110020c060712061e05040509010e0d0c 68
    0x1280b44968444d40110001c19021550b504d880400303020100310007280c82c0403030f4421803080e140000c50f81804410403e403144103501507490617241600b0031106490b803991b00c2c1c252662041c60707100340180400700640549043d40245400550038000c00a031100002042d034041c0000e51400d030200d1340c0b80c22003258035400c216030203404500ca5a0007009000003120003954414040c008000581c80c040d91417409440c8262581c41c1c00343e2101e05a880c080f5040c0d07031100c0841060620b40f00d2003d03614004078940b025248405410984e442d11204039480e1940200c840040b001000110b80c40106107024110020848600f1654031030106851810841d9108568400b02c001d40281b07402d54441404031910554100c01008094a03008005071040241d1122981b030003d00081c10911420070b0188000c8803402040c500c6941c0c10019a02c0c010940030814800c45c0100c0e141c07640e102e1142d41 = true := by decide +kernel

theorem cover : BRFrame.Cov 283453237 283633093 := by
  have h0 := BRFrame.cov_init 283453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 283453237 ≤ n) (h2 : n < 283633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
