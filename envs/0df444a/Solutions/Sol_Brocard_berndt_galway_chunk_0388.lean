-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0388
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:33:25.747996+00:00
-- url     : https://prove2.me/submissions/218e06c1-a745-4c62-812e-8f01e840805e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 69604318 ≤ n < 69784175 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 69605568 1250 69604318 69604343
    0x60b03010305060a1107030807080a1e0603050114060a030311070b0d0b03010c08040b0703090515090a2906040e101109190f0e0709090f05040c0504051006030c0c020d 73
    0x44e00c46119044101c2d0005025030318100b0161f401901061000703103100140460080018401d40c016040503403020301084125455600c00305000f80204040c0c001681c0300c0d071074034205075180114641c1c042c0c0514001442c90100301e241d560100e0349000d605804603294024890000341455940000c0c000307944003aa40450b5070402c10042c1030031600411020f100300300034401480049088540440c1d0850307014a0045000f19890401c0f61130000c8129182c041c11400d181044100030010442180035842003206aa10034295181c00b90246840c12480c00b0841d01c0a01003641c43c034140c1d0040c110761000b01c0c16103811a20f0290b880c0100d0b01c00000707401c0c20290014100c00c0030702d445404003d03c1d906602c40381d00c100c0c0c01e240c6011310f043c03070038052802c520034140301060409000d24043c0d0300030050844103006172462a4041800f801060710200d50142100402248900d031a0103034511407510240c005442c1440c0600480103002148904801c3c421002d0041e005600c46580010308203004280a0021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 69606818 1250 69605568 69605581
    0x506010302010e0303070b07050a0302041d0103030f080108030910030e01050a0e0105130807060b0409080406020106030302070504061d070306120c031401020c10110909070815060406050403020103020d060b0301030506 95
    0xf5011400c0c0c00398466001088010009010160f8040d00402e50340341c4142c4800c0100303019402072286400440f90303403c21290107188149008144c0341600e102f651120b1340c454094600744c51407582801130705e1664000303002c2000c15003005a10788032000220314012880820b501480c5003103c8041d1801390742030382c580d1402e030010340d8240100c5401000a8841301481c10031500e07a04503e0044140c024a140d440381c0091205640e81d403c4691000c0c1c1181520303507980d0395418042d00804081c80110094015200000744515041c86018111203014101e1038400011251140100e0f000802032420f060713480d030000c45c19141041c1103060b1244264000091203040d42846039200c0d461040f11006607004000312080301e100455800c038010b41442000c6080c941825282c1c082c2d0040ba442c0da500440c449081280c5168000c05c0140101c5100700364441c0ba4180605100d040c2c85607003d801d000c42c4003040200010352180d802000c040e0300c001800554552031304410304456200307138003e954591100b018001c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 69608068 1250 69606818 69606827
    0x60c03020c0312090d020a030203011112070c02151308010f0c320a020f0607030c0f090b04140607021207030c0906180911030f1b122d0a050601030201 66
    0x10604220b0041100301c03810b580c907142a00c00d07401420701481c40f2034403520031502c0b18803103e0040c1d54010001d000340c81d21007004800f41d8200b400692412500c0d403001c2044280111080100160003600a441d580c204000c154030f2a40600c0d00d41e5666030811301c2c0002c4410081c41017089162070208040742071100c0c4e000061024034070317104c64a9850181c80000c60799051518171401d5460901c4030b41c507220300d503d100690a12004420390310319400b52100b00700d07526031301d0341c032041c481314868489001d0104e01e110100c4006060780039004c502d0200700824040d01c000001340d203000700c2c0020700044c0703003001541c08541035950098140c00d1961015800f80100000313182c107030025022080e000c110103450440340345403290f204015801042c1d603d8a407601130080c84050800700d824050b0443d1068040196415952140704803504c4140049064042591801803070503044404031f0001080c070f8821910200c0281c0d442000040078891840f0b0305000c01030002c1c098440100e0103000580340e1580340d07000160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 69609318 1250 69608068 69608083
    0x702030d0504141e1917130302090f0f04140a081b010b0306070c02090406020706021803010e01020a0206040210050c07060503010e100e0a09020a090f020417010204080a080c0115060c0302 82
    0x41a4010342001141c004000080c0b0701141d03a1722000131800300301282020701812800184816540c240080d0b02010740e4001001d2408880c42620484602e035100c45540580c14001d03a480e09a0685107001315000c10404080d0000d2064074600340d0f4400b12156542c001581e10540316a81c4440700c03000030741c6078500203100e201000a8241c1c040d011a10b42414010702041c0e02c540b00a200e0828840490300780b05281e416110141d82c031110456072045a282034140300300280b40403511943c00d10004c119000410b00a0b00e030441010740080c80c15444950030022940c5c080c44503541008000d01c602241c0310030802c200b000900880d00d516540f54140f101c504c8243c6e02c01440c0c40b0003811121001c01465945203202584198200300c0002e0034109480059442801d81d0303c1004014141250148090850f6004100701e985001c00d02080d0401c4610341ca0a0780598400c3d00300315000701e0200d4000c590910014038041344003500004240307d40030a417500c640040d03000345000030004040b1800305034040000c1c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 69610568 1250 69609318 69609343
    0x30a180f26030f0f1803011107020f041b0f08070c08191e02070f090516080903070b040303060608060109080316020604080a0303052401020a08030702030d050414 71
    0x144202801e085540d2400000044121404004482150300d041024800e580d030851880c03c5155441c1100702040c426500100080c0b4036482050710b60106a03d070502c1152105800d0089003070400b1265020481107510048219030007945907041c4034029050740314100071803e419100c44004c000c0664000b0030011000301028180301c02d0807000004101200103544802034843c000c2142903400d04821142c666000400c20392103641c0b0740e80310f0130054000c40d0321000c0c2d5079152181c000c0c8071340d6585078100785d8a05035001079080c40034042c401101c81c8110101d0b540841c00400300c915010741c50391004111030003154282c000075601c403802e100a941c031420442c0c00c80b100346407100c03131a802c0040164581c46010550381140131784114000841d110042940c0040c80030606607440804142400360242c00100c81c403601c1580c2c0c901142c20040317110412229070280c10b81c020400303c0101e6039007180540c005041e130307003e610043c0034884d07a24900c0d002d0180708502c41c1103d07086001c0b201d000d0921701240100754 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 69611818 1250 69610568 69610589
    0x605030405120a2f062509030c05060705031605011e0209011218020406030803010501090803041a070c12050a02120d02060f0c12090a12030606080f040501020c030a18 73
    0x8003c980d501c5050115030700c0040e0290200da2403001c0e68980f2038499030030380f296540110000c010b00c0940c40c2070065040722120750003078002d1845c2c1c0001c84070280749010052402c5840c0f102130040c0d00300b02c000307418800e2242c0c0807a0700e44001c4504000c4200d4032040210b88070307912080114010003800c4350410058014a209604208007400007800b5002c00154100341c0596170402c850800c2103a5403510a05038000d4000c00a045d141c0c107140d10640e100340100d80c0440c0da0300c030000440c510004101d030f0071142c11040302d6580044040e185450355000520907241c0d94288074022031019000c4160280b8140708800903c8171004c14410310030000e980c0c44512045400200c00400b40c41d4012a1990340300c6c24a040030708599613801d491a40f24042d0f510395008021510003000303920f04000501007401c5005000824110346112411030546046001c2c44002440242c08580f4290340f1000d03494001e442400050b05205421b07511070729540100300304c10001006119982e544810a04200f009820038011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 69613068 1250 69611818 69611827
    0x9051b060304060e030409020711030105060909070306050a06090e0d0e010e0f0405180d0f020c030102040b0d0b01140a050a1209050a0318091103040204230105010c0602070c060503040512 82
    0x6a65800002e00107459507440d140c002040c003505000301e4001e0302201c10119102c40031800c0c14454103409820300381c020361800c4003188a9207807a001c00e520421840005010003411030355104040c007005400e500120ba10386c40301041030780301070088001c81e01e00c00d0700502400c800914000d24003100c151039103060011080013200281c69541c070f4058070800998000c540350300ca810590715500104c8480002c10300643c2541048280e002606006040403603088841002e102c0080600301d200b94401c58403441003c0001400d00c0f00f00382c1002d503004e6014103055040403414000c0801d50f5000c0500c86000403400100c0e110100c0c0c11081100c00d841591800308003039407003a0345807036076402c0e016000f6091080f03003040d030700b0000320030120400030380b05001e41406020304140303156650741c02c00d84040348035a0815805084230700e0700075240c0700c008400f003180d800070364038002c01910100c0c200002590800e408000300340214003640001d5000b031101d943d500c0e559141504002c1d0424078503044407000404c0401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 69614318 1250 69613068 69613123
    0x4120905010225030f11010f050c06150f040f06051207032006040306060905150108100e1e0f010f050315060609060705060a09030e04060602150405010e0a060905 71
    0x504203040c43d01d1a107800e040d1803101c1d50b8400082a4940c0001c02c00b02e10020706008000c0b112580f8100100e080e2500702e001c0380004000c1c1d40c00c1c05a114608050391250002400c480e00081c8501800c060251400d030071002001c01081c113641a0494600400e51210020842801e0820102c1541c041e0100035040c4c481c1141d4a1080584000c0d0342a080340e421102051181d64801080b18015030340b1030410881d07a139541170a41c028120032120f6400da00f00442c0341010a5029800713a80c440c03903e544008106609000384110f48200c094000b02414080e0841040b0368004030702d405014080300090066a980b602804502c4203a0a820a5002c2c0d0054003100381c0c40a01c03515000d4000030b0460340303141c5610564020404602840c60007426038481c8200f4428200415803208810b140a91b5941e8210806001448162140c0e8440c41c0e00581c0030b1441600c0d0460422000364005200e00000304840d5542d20705146007800c1e0b03440a80c2c20715600d12103402084000c000100286501000c02c90b0401140c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 69615568 1250 69614318 69614323
    0x50610090803040b090303210601020d051837150201110a050708090603071205060402090a0513090b0910230106050a1103040902122406070c030c0905041209050102 72
    0x610507050442400305d1901210fa03000e000762001d40141e420f03070560841031001c24400c0c0308000e0b01c0385809030044000c0041400e00c52002c440b85150300712014400564038600f803004000312108002e120fa126480c0408440a00017001d01110b2001121250301a0611984030064014040300005680c548004c40030b03074103450000c1e90400c105606080f074071440582442d61440c403400d9a1941c0c00310002080142c6030f9007068100c01d010780d10305410400380e6500c0d010300003240f05941016030302c09001c003420001483c0c4500402c020251187d40400c0506280d07540d416207880603a4cc3c910241c05c802141483c0c00c0c1c1c1032048011050850003c185071014606060701c00742018012401008000122440558000c0c9017044024090100f00c036544d44e603450000740250481d8144902c035a11007404191580040303440c0700c0900300501100844044d40c40108803c1d41e2048004803000e2415610000104e802c122280700180711154010030f0701d00c2c2038070f804d904040d840c0e9004024003800a4050040d0f9030f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 69616818 1250 69615568 69615577
    0x3011103250504081c030e0a0c14010e030304060c12020c0109060507030512070806040e0c0a0620070902030a1404240f060b04080115030b040602030c09090901050610090803 76
    0x228000425010501c1007140c0300e00c00c640110b45030780700e031001ca001c0c682c4c20f0000090450b6078070781e010403a44d107140c02007076103c81d142d20001d800c41542c482c05014600001c17000002007241410996480007410b40440d06540169000b20041030448000300103003e500b080050748042e00d44080e0103c0b007c0c000010f003603540f06018200404c280869214200760142044644402482000d40c11a18003410010000101101d070f89001d1400d200e1847c041c00000980011800e03030003001d4001c002d051070000c41c0e8650400080700050908a1070740300c3c10760401d00201010303102c58540943d992400340300d0740c025070380c1e042c0280070740c0d450240401000c07420076603001003c5800080c1c000000101c0d8220740004d0003203111154141d500d041d100040c50007000d0000c00488100748024818441454107000b45000c0d40c5c0710241042c48014002000100e840d401168000c0c1d40e081d900e400c203008600829960407040300e508941d40e42d11010300c609460b08103440c84843d646031078480b001908180340107441e03024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 69618068 1250 69616818 69616861
    0x307080f01081b0d05060a090507050301020f0405040510031a0402010311090904020108060103021e070b0c090a060318080412050705040c0203070f05010908030f0a1401030807020f0d0b1503011103 86
    0x44000083d030855036003d565910080c0c0000c100d600e54240200281c0060503280000c031024411100001518141030096941015240c11180d0400349854140030180c50020160180549003220120004c2c0b100010001c010964101041c15403034203100140031641491444010460300b80042d6595555000c002640180d081c40c20000c55110000182e011f4050460f11001c107408080300d40382403030005c1700900f0649004072605151912402d190b44103601c41d03008080e8202020105c1844030500030b03000348004046003505805000120303182c034040d54201c1d4014690f810b490009440c10b00c001081210050601201c0070000d001590001035a24481c4080c02020345d0b000c00c411400f44602076105400c529080742000b5901c0c6022041d03009042401c40394034807910302e0f02c40a00550f0b49813501c82410b0f681d0000b1040c1c5020880d400708946042110b003420381c010204000303030000802d0310740203034080c102c0d0200c0c1d41e40407031400d006c1500791042d903406c000f01100c091041099014580080c0e10308d0a5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 69619318 1250 69618068 69618103
    0x1021305010507031707020c0102060a0203100302240a030f1a01080105011101020705030a08040b100518041e14010c080c09090603030403050115050103051302090c090103060512030307080f0108 85
    0x214900c4c00381c50350914004a0034604416104101210350040744042e03240009a00392200d540d40e9264240403400700b91108880c0c4040e00000340014204440120841101c3d0803826100e480109030381d4416074088101da81c0080e071140c480c0d6401e80b2090041c2820046200f41c0003005041c000c00003400d03103d0500c10b803810404540c0000710301040c02e604650041c0c0d040001d481d0b9034001180043e080c0030081d601111050344007000640c0000c1e80c0716807036003511402040962403010007050b00e040e91201803c1a5038900f0f10300a00103a00c40a11b00e404600d40c80351100c00034124041e00210308407501f00349440e0510041408015207154008100d9108480c00c413103440c07058640030701007803071809241c1005200d580380c09003441490321882e2207181220003da90911060b500c90036044444c00391000001d410015160204660040c0d1030040c2c40d0b544018900065141e990340001108101c540103500b542c4d0304008280104568811071a6902042100900909500d0902040e40d40c0750411001000f19 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 69620568 1250 69619318 69619327
    0x5031810032f04320312030411011e020606040f110714030906160b060f031b011404030804090c020601061202030a090212101a01092304110d0b03010213050105 70
    0x4203003400e03140540141c07904185000004c4021600420074000113110000160a0f00c504a00e00044d003202405580c44040303045031a00eaa4906059035807400d42c03818848010062100028006034032034000c00103600416580c00c00e07405004c12507c4c0c0c0ac51032004a070412019480c140c9950040303860072540000744150700c03030541e66014118054069481d130320040010382000e00b8079600c2d0b050328450f400349046050036200c0c0c3c000c2141c020150103055030550801d210748031102c10314401d101c100c56030604103910440b019002c140d00d160b000b600200c40000c0e0118082c4071001d1103204008004641d400100a0343d41031400190440e0b558640142a4980000c00103c1e071641c90781120402507405084000900301d004c1242d91582c00420603505e441e031500340c98000170080b540c0c100a0010068448004290400c0359a9000305207416901d0500702082d41c03040160b446522403d910503800c04031858440036645c5d03010080c1c0306e507180c4085c40f0360700500860524490319000c0c0c13000c488090800a68030f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 69621818 1250 69620568 69620651
    0xc09160207180603051c0e010504030c090515060c1b0d0302060606130b03010b0a030b01030525020c09100f0b030c0301090c11010e030a030605121902030a0503181003 73
    0x1600c4641c02c0200355029450100c0c01b000d0008a2402c40760406807282840360417001d00440301030086110103004c9100c460002c204100880e030101d278100a807000c554905118040101d44294882400245a540041582030303a221180492400c48041102c2060301e07240385440c002e545840142a1504c508800100c000040c1784800001008280000410b138480d03075500301d1441c61360010390b950300109040009900e0103611920840b4400c16102ca407401d41c240000d03c01001c050010070200c025403146107960000c0ea42c0300c20310744e0b00c0355071241180080b85003808003120040a0a40c0000c9504405000b0302a01c20711510a9a0568942090005081001850460341031000c9440c404e51946041900703a008400400100f84002450318240440b942d623100b40460104012075001c050740204c1c0c12145075010106070405014002021181c0715015a111380d42158000d40b0044c03401090030b030301c082450410a05142c192082424100802d024881c20004040001000c01c0d01681440d0745090300c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 69623068 1250 69621818 69621821
    0x6020309031e0702040c1701060f0c0c0f1403060103030203030403080406090f050708012d0509011509060f090507020606090403120617070f060903030e010c0b090c0916020718 77
    0x82901c100301840c05080c4041c2e0100c000c80e0b000c6070042c3d00071343c00c003800c6104041c080c0083c1d82075a480c038007602d540d981c6402000c8512108644501c0c04104510f617a0b03001144d62252100007030002c0020520040d4a8107041e00e2980403000d240b240070350400401000825001700c01d9991140c1c041c102107416035524a0044000c1c00680801400c004180021206001d07000461009480b001c1c00200840507412002a816481e042d408e050190b280094161601c429904070540000080f40041412a00d01049440c14a01600080e102c5c56880d41c0c104000000c010400c0e0082950300801c22960600c01802521075100816003070140b103400c00030808052242c000801c60744100e4600b001120f0720703000010356511645001629910409801040e420201000f440c04c85d249038513441c0300d281c910755040c0d607001c00c051015410700060b0710449022038a050340301440303500301801070411602542c0c2000f98601000e032102148840050058003d42c0d00010400e09071400c2500c602c0e02a11401301980 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 69624318 1250 69623068 69623077
    0x7060b1309030203090a090b030a0204090512040815010b0306010503040b060d08180301060b0c0303010611010e070b040602010c0c051218030f060601022401061b020409030503011d040b040602030903 87
    0xc041c50701c0603007414580e01102800422400303c03809903100c0e951307003240415250b03104484d55140e000b90640c07100600d09607120340003052051059a501481e10f00007040f4030780117070788464021780041d40f4000803030a148003504d0241010b96215815410640002011800010001400c0e42c0d582030100d046c40ea5000d4180a0290348082c07500d42e0750444105a0341013043ea4000725002c0d60801c01e021500022007c01d48001d070700342e0402581581c0c40c054084503101c0e0102c11020003950b03104045848203074144480c1c0701400c4001c040641e50f40c33034980001e0840380980a1b0b2000c1000060130031300019400308208500c8090348071004d455401c40100c1a0130b60301c80e201c401d80e2600c190b039070400100b01e0105046200303050036000c0e142070146c0909419800d140c200b00d00c034402440709005003ca40d0141c8240c00490803461200002d424240d13002c1000c580202109401048012004100100306e02041491490351000143d1841c01d00d65100c00c00b00c4006440140a65004070001d00050030410a03103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 69625568 1250 69624318 69624349
    0x90f040501030303150f0506030c0702010c05030304050a150c0212131805010501090509070801120c090c0206010e10210204090219140108010303020a0201180812130909050307060b 79
    0x30440ca59507454060014504240c5210310501860800201d85200702c441400300c902c0a091686560b451504e000346c00c0e07000c070300200d051101c8050030b1030200788108051403180b8480c000429108034a8180f82801d0711200d001d40c1000b508003d6918801035000c1194814000a00b5040b51183d204c0c042403951302c50103030004001150003098075404403665401c86412504280c0310f00f054584c5034000e005161204449441c042020100100b00d01c0c1841a280084140074900c842c1c846610f8500301000e03070301380780c00380030069028900520044094500043c0c0000007047e6060b80145410840760382c8422284040c08a030401082c007a003503440f00d070020100c02d9030041404000b002d203507000001c16001d83c00b48031751410f880c2c030b0344000950042800506894040d001010700303d9035a801140c1d48861503100902c1080780040004891030100480c61003c0c03904043d45482c1c99884000d04c03c0c200b1300350f110b184180e05081c803800c08100003004072400d10340c00c080d01040f02030700e200108000c0251940710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 69626818 1250 69625568 69625571
    0x3211c020d060506030c0301120507030f0b04111c110d0c060519031107060b03010b0901090b01020f010c090501080c13032925030603022e03020f03060105090f04 71
    0x811956025980c0282420300c0c10358810054642c0360010301c80b00d0701084540c00d01048041005000c1c81d5064125504024410030480c1e580031703100d9072602c0a03a01d010704100e641902c120184000c01c500448036081c00c100680e00d41d803c0640d001d01303140f6000b441103c01b418805504428030b0340f98aa184201d00c16079080703100c0c0c03000746544410040190f480364100491550081e0040c80e6183c0c400d003d2101c1e6000c2804640b424100652030f200020040c04a031a5031640da1030310300f02183d49441c443c6c14000c1600b90380024001804600190420000a86c8110180d141c2400802e820303800a0410060700d0302868414419920854082c80c6441410308030404500044000410802001840100301c0c2c1d41e892035900003d02c501c60205001d8045e42d440c5220040d1100003030030040545c0855070740300358a00e008115103070b0382d4010404002004210b8800c10300141004102c015032150030706411109490110f10b007807100105141c0d03038000500308a0403c100080d004406550b060710011004400900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 69628068 1250 69626818 69626857
    0x1902040e06010f1d0403020312070e09040507080706030506030706030b06041e060e01050901080f0a020405180f0c07120807141b0727050604110309010b010201060f050321 75
    0x200304100010391044440210960064071454800484003174010340d8140c000314107004030910141500180149080200031600c0700c502a99690040a80e0060380a00c0c05403809a0604c41d0302c40c02c141c920b801040900d0300784003d03c1416100040c6041c111410703031400040800000c00040d04c603200c0c81c1e1144651900c64521120011641d00b19001102c0f02a1645080c822000006403000d000380c020b4203001c0f8940b180050310444802e007015a001512500c01480c09840e103000515411002c290341903107a00c20010030051114410215400406007107006043c801a59106079400303000c8070b031260400c510366001c654040c1c0103001410005400c982070f952511149040c00020034402c501d9517800e81310b5203100181200040030584e05100b03100c4030120051f117150811307902801c0081d0056420550301c100c04840760a400024501038105080041940c0c0340c10400203080d220190070500750b11289440030805950005032103034500c000d0920401d4640400040c484241c050428048031103c0e030400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 69629318 1250 69628068 69628079
    0x50a02061209070510080f060102010609090503091302070c030f031e080f0604020f0405091503030f0d06090209010e01030e07050901120311010b01020607140c150103061b021902040e0601 82
    0x41181c0b15541410807a030880e540c420800c0b00740c107421503654010580c4400402d007140001c41456600080c11300001c9400ca9072032409078221501d144050b03401d5000442c1042c2985000c88d11921210748548080d400c2800c50344441010500030302c00103040300100d16140e4101405000100108034007864000c0300314101003000717090f00030b0490721030b01001c08070b000240203890a40300750ba4030094204120f60500c0e00705020301920301030250546060003074091090b006c60340e080000345210701481071620f840d00c1d4071500700c82c2510440d402207041c030f0340180200349440e6400010318842040901c0c0100e0101380940000741410346540000303811034104800840e01e1205168030407800e500c20342d5601410011907034642c2c200d540300c1d25228016000340d0302050380c25208800406044080c542c443c0d05e8a414a103038140f1382031295a130000311052100041003404100d01c98078402244400890380c6120805000030b40720014800c1c001c0c1660544034404046d9142c6a00004c0100e0f031000483d6032658591 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 69630568 1250 69629318 69629347
    0x70b21040c08010b030f1018020a0b0903060108011407140702041a01023702060d1404060c050a23120a0902041d030304060f020d0f0c09210f050a0206 66
    0x501841c0c40544c01c0036403100e41c0d82400607561001e018040054260300540411000280440d1800e60085c0b4182c020001c01580c0c8400c1c1c044010801d280f03c0c01e958400c05000e01d4180700c2c050b400300c1c0c000d0345030082c4c01c07007c6420942d00c1a0702c80b00300d1400c1d010100c030241680001c1e004621000e500300d0703e012450b042da40c686408008070454241c017103c828217800c0f6400d8400c0248494884000c030400b80c01021a44440c90f030702180e070351005008038180792400c0041c4040f501c0076001e000c901508803003440280082841401070304040703885c01500e0701c00c0d0108090981e00c00c6030300240c00000700700104840b4000100543e01d40c0c0442041082035414800b0741c034005418801c0e000e80c030440ca41600b500100c92407481303802040001ca00554195503554075180010011124082040c0e40c0030407200161a100348034010b09c95600300000986080084001020f0044c3e0b40c101c980000101c010030141c400c6100e94040f000c40e48642401103041062078260304201801c10001d410140c003145110080c2c1c602c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 69631818 1250 69630568 69630593
    0xc06210c0c1b03150207050703080702180a0501030c05061921111c02090904031b020a0303050a17100314030702060703090305010b06030708070c02032506090b0309070b2104 76
    0x4d11452041c4061804510220b01c252000144141e00c1001c0410010f10080301801d20180020580248424003c418080e044030071207507505466075600050040201101c55900500710070f854450501040010400c001149004035005000100c00b0b00560007924420101d0315110084042c80712002498004c8495001102c0d25411002d5440d6061640301350762003034800442e0014141c000948071034a00b51200d04034612041121003803000480c02685945000782c004604c295a00c0750744218218009214280c0095024000e10740c420500c0600ca07411651042503940080da0400d202c1c1c1850022407a40c86500c8000b50041404078440c002c0c1900920f0200403280510300900010030700d0010899548805c55034080802c2549001c54107041c410450040541d2001c1d08603461109540c3c6500107070050003245580d00c07004001d0034003030942d01c01201c200400003101000c0c10f40c103101e290107441e41c03420b001702008280007048a4185040018480d81c0c441101c00b605659800c1c1800c1ca0780d4100303c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 69633068 1250 69631818 69631823
    0xc0e01093303020903100e0c01080a02040f1202040b0d02012307050709020c0d020c091302120105190e0c03030f0f0f03010807060e091005040c110f0a0c06210c0c1b03 73
    0x81c411b0300c03820b05060340900c14034070380100050541001002d00545558002170100c40c60395a00b44000301c1d401c42d41d42c101e80c0241040d0607200014504a01c1000280e0f0032103c0050300a5404000704001030b60088046070710080ba000340b0320391a049881840c45c5602800b031002d0128413030b40d00c1c00078500c081a0b00410ba095154400d40310b00a1409000740d03500c1c0740c03c28a05802001d00000103507285065032003d1212031009114000800818101d1401d50307605494200006011001e5407100500d0b601c40c66661081c40c6016250040c92100001d0f01c900458480d84a1007200003074640d400c02240d0100e84c034154403004200d031a541c4074801c80e940d40712140100000301c1c0c4084404209460281e0301c0506c5061f40c4158241424104801c0c000039088045140e0280400c00360300d4080071005010850504810f94010100000b95080c1080c07c0d603d1030b48407105108444c2d4099102a40c85159002403845e58100440c2140070944211608074405501401490700c16a140c59401c254200f02e05c1141d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 69634318 1250 69633068 69633073
    0x30a1401050a0812031e0a0b01030605030703030e0d030e120a02031605060a0f02070f0603090204050703060b03070503090a0213020706150f0303111203010b0a02010c0e01093303020903 81
    0x20780790030902081a0450141d400140e000784c0d040036030420042d0046601c6503105070071a441003040f0303074543c50f00001503983d0b540003070300d5070310b60b09041d41d15100f07c0c1c00030f080c00c41c01400f49900d10748020302850140192180500c016450400c280b5020302005801d8610203805840c0c42000c50b61115111956140b04038880c0c0551225034a00158682001c025102c0c020040b5203030403403004040d20220000309400c4250300079980c0002e5840300040f0090700500b255100440c0030b801c980704000481e81d0050440c814546010001d0180c2d24100c015640c0c0700740d10f401c0855817030321a0a4110310780300ea180c1000750b0100c0060902000c0d40200d8000d40501403041105000142c01a803000418001c60300515901090400041020074403c000311110700301c08405503020302c0491115241c41c1d91007608440d54800000807214a415030900c41d2504000d400e02d802200040c3c07910009285c02868454402100c070401074111036040c0171100b80410001d40350180415102003034000d0069009688804d102c0d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 69635568 1250 69634318 69634321
    0x30b060109060e090403170a0f1503080f0711060f0705060603010501030b0601030906020c0609030c07060c0c05090601030e0109150b06040515250308010e0105010c1104020f090402030a14 82
    0x194001d0201c0c1054030996103590211080b08000c3c040c062500510650810040044001801c4001040d0030300442048501041100881043c2ca0079101d0011010440c7c6204d0282000410440c1d4243c40040d1450301041c1c0e6a041c1505100001e1200d90b682c4d640e100600055030b04481c140764000f070210500c143c0554000b41c3c0c404040508072402440040c042c00000c00000355150310940c801d8105620601d00141041c5080000c9480d002003200c01094640c00002e00e0704904508000f8480148018070b01300b000c00c42980e8908410400301c0c41428014181280402c5460703000c1d40010031510740b480001c22004619040500c003446c54031a91400304c524011310907806003444002c03034058074005442080008260b04800e241035003c0815041e11084214491006001c074011700d441c40c500985c0d56074603550411032882d10304c480c107910840c18440307540a4000000c034418609011076404440050300d481c0800000001c6226080f13885030700c1403001040200101140e80543c0c10000c0b0340d100d0704100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 69636818 1250 69635568 69635581
    0x70b0708190f03180302060105040f0221091516050a030e030703080103150c0c140f03030408030f1012020d050106050406080102030f0c03061c021804030e010f09050112050c130b0301030b 82
    0x20f0b050613403000340050300701000500103810f141e004010b00440c1420010f1400c00398405c509219000c03c0c00907a05601001e05000c46502c0801920302d00e116201121102e5040c0010078225041a44030110180b1401243c2555078600a600c08640f10500e5410b807031780d400399440c0041070307000e00f404200c50114001000205429082c81034565036621034645800080054440398a4541950300030142c40c1f0601a010100d08000d001135409680f00780303002078903070138040a07031500514001d01c0d45c01c41ca060b8072010002c1c0b40c0c00c60200c1c1505034060720000815203181c10482c1c02b6100c2034002680103402d151002611600c1580114811500907501188070f440306800c00c9554030040c1d580c0391b400300d00c41141d10350703c1e40d402802e5000d040c802004a03c521014401e55011900210750603004900204496116560000d4104000c0c40d06072425040003420030001804521004140a00d05562400000e506000350030071641803994940052480c43d40e03c180400682d072090000300d43c0b03542220041141c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 69638068 1250 69636818 69636851
    0x60602010e150405071505030f0109090c030b0a150f03021801030b16020c0916030e0a020919020d0608010501051003140a1e0903020705030c01050408070b0708190f03 73
    0x604004000034000b05100e07400440c0900101500664181c000c1120008800100400f0810054016126151070386010810039a541405070f01044801d8244034602d000107821290480569a0003100a80c442d100c0c0071100000b008940000c0090b8001103901007017103000d00e1041d2080300c0c403c8855401810281850300e403a83c4080c80000e1402c0d07035400c0403c0d074102141042c0386d84104d0380c0c411910a60030722400915440c1081d1400c0000c461008206860035502d40038580c40c2c1c0074280018114508280d01203120540700400b51048104890b901c048060000d404489001c2c5c800882401000c2d21003070a1030003098281708941c8500d0500e54261a031078028090303a00320000c215800d80081d944c620b07443c0007800240c9121a0000359158001004841ea8030030b03801d62034041d0380140207003030419040c5490808034100303090510000380020400e80b4000540b41003660f0040762a642c64421034503183c50702d03000d942c64002e01044543c0310101c810794001c2d11490304100039681801826050700201c0ca = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 69639318 1250 69638068 69638081
    0x200903010e07051309050a051518030a0e040513050703050312090a030207060f0c15050403090504112a03030702030903060a020c1c050d0c03020c01050603060618072a0606060201 78
    0x1500300320303050100111341602d41d00a4941ca4043c4d01666a0b0b01842d584103420515284072030380359000c80701c0501050304001131382d031450540400025407518070380200183c5454007041249200b1070304c44000422030901c04c0003943d140f56000040b81c1005031a49001074403038000011405010002c60000303903800038002800c20300c1c150160003400106040c4441160710000c0450340000b03102c4605014400601c8004100100c20300f1035500081600f0302d441c00500c4a031150303000034407135070404044408819054040300c05070340301d05000802c021051381c0344501c5514244c080309030600006c402c00c84050303000700003010000e1049058030305a40c0c070300c003c0e803080340076228203104980e00290b61102001c44420b0b4007800100107080941c200304e42800701c142522030082500c00000c0c5c0118a161440c00d00b405030300d41090048002d8815490400045080d80303070840d840c3c00300c802c2d4103404900400e0107040036003a40c030047d00280b0303030b020091133881c01500c0303102904444443ca40303200091060300c10b10554 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 69640568 1250 69639318 69639329
    0x313140913020d0b040c050a060309020f03031c1508030307020609070510050403060e07080d2102030912030a0207021806030d0201050408090f010e04020414120109050c090703200903010e07 83
    0x714403c80454481d6569900020021180b030b1000700c0b070224072a902c4425060040001c0c0d074012400c1111441800b0301012030f111031900950090100c1800006801e161058512800341c0c00100151a01e0300d10044500b564004207950000100b480a0581d021403007510420000c0203ca10217541c030402d211001c0c00105502c0d001440c1400700340000345041d0000311603101c08508941e009600d0309111804c0141c00c5042c6c502085449108110b02100d4503039055a40080e41801c504500e08840455111050540143c56001300080041d602a110340c0c1501c1d02203402a0880c03440c06004403000d0100042650750b140729219454680e4131482c414028284a01d0b441109241800207907420303c888a091180d80b241880302481c030301c0005031034900c003500040070140d211200320024641031200c60b092210141754264100400310300403a07000540f0541d00c11098800d03c1c4103507104903080b40201102080f009207140c018207011000c40e02c00d0060885842c04030000c1008011107010340b5500c15062058 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 69641818 1250 69640568 69640579
    0x70609060c06053601110c100903020a08040308070303320603120c0105010f050105120f061206070e1c02011e02010207050706050d0c110a060e031314091302 69
    0xc4001522500300b00d41191a02c0d401c0b15580c0c2c0c88041e002454402c410707001d0901c0ea900b200013007440720700740a018892030003844454903141042ca241038030340c05203600b080c000c2a10380d44c0c050b0401d40b00f0014582c005400240311503c0d45d0302c91078070f0b207041e610004080e1f0010341411000d07009603c0b5403110b00d00203e10740d038000c90850102213415555000083c81039506000351005141803000f08002040001405c2000085a41c100f0201c1d2a4010303660300044e0400c03000348a89041c402e5440c45040e00030310000c821440581d41c4070001000700e044000072000900806080c0132045420242c40009081d00320307060650395150003415003640002110290000c1e5448150300c034400c80310a00c090700b01110348005442e0800b1615400d00c1d2842c40d600490000c5d1000650b115881c01900c105003d001d03807441c018500a00101c0080c1e517802c083c01c0d01900c10756589642002c905410400c036514000e0044192001e01c4d51400c00d038800c903042d003a0389805032844100003a0081c4214103e0410290300500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 69643068 1250 69641818 69641837
    0x5010507060b060f0c01060314070510030f020d02040305160b0f07021c0b01030c06300e010b0a0807030b090601031a09010609140106180806070c020103020d110c07060906 75
    0x1c840700503101031520190464020080342c800710004100071300c5101c0c0b4031000424054a0b52401942100200030100c019800013002480300e42d6503c10451800c0c03a140c5008030300a85041c290070000e11440c041d0640c42440080c001080007000f06000348500b0001560140700e941d1410050110300c54480c0100017001c0400410b0010b103850401c100c03400409900070790b40b001d000e91324480003210a030000c0c1c4a00744c180e0000c11940f80d1003c40b01aa4665142a2510031032080c0d084210510342c4901228807542c440c0c119041210b000d43c440e40600318002c2a440c54241d51340091030b2a230703185002c15500c80e0301c0b110000f40c0c1d0400c005413042c12a5444003003061660452096010750480141000030740d0354030342e540010090201d010f1454201a02507500c100395242400150030300e403049803401c0a528580a0420a4800114080c0e80c440e80c0d905122400132014030040f030003840744c1d000d01c0c28580d240c00303c09180b900c02c200240002900680466001c5509e90000341c90035425481201c000404400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 69644318 1250 69643068 69643073
    0x40c050a0507050c1309021e0a030f020612010308090a0501050f030601080c04090f060e0a05040209280e03090a050d050304091a040c0f0207060c030801120c0b0403140c01080105010507 81
    0x244070b480c1c00f4005491445a02c000056100b000280c510488240c86044403400c0d450080307840321305012010582910303400d4600104440e0030a500c406003001800749000010354070703003800716003220001c0d40c0302e078156684a1602414641101000c5c2c0c0c05804261800318155028408035986050074001107425917440400440b40c0c820006c20030451034405000004a13000340340036242c0c0c018140d10011512508040032210310200c0180506401070502003400050f072140000f141c0c001c19040503550040c08100308142c01240c1d03800b41d103000507190800d030a100c645e020015051228080b01c3c0c0656250351201040150000c2c40d1029100760001c1008120550041e445080d00545004641c20040715105c00642103840c580911004125007080b507031a050360501075600a804c1d00d040c294525005601d00a102000c1401456424200319041101b8800d04c095034800400e4a040e003a9030380d544030b2900c6008000d186092850307c3c45011590724040d8010140703a4144d48041e541c2906140098 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 69645568 1250 69644318 69644327
    0x50909010e1005030307060c0212030c0d0b03010b1002010e0c10050307030203250302070201030f050702070b0f0c0604080406030c020c0904020d06110a090e06030105130f050c1f02010506040c050a 86
    0x761030b60400901c5508001000c1c0c8085c005403041900546001800c032066010290411103d8466050424410420040d8025515081d01e481041c80800020180c0700b40020a00504165010f6580400c24080c0360740c85c50703070542103503411419820588214443e000107102900b4101100000070403420300008040610a501540d445224140c18404220924121501400c2012010000203800060081c1996014010030344148400c04080007036180c1100001c2d00e40391140070f443c0c40c0038800600c9180a084074400e8444440c4004196406800d00703103440c55040d4003078400c02c000319003048100801d450010a0360066102d019090000c26078580d800c210100c0c20b00300741182c455507100403100945042c500602006c0c89280c85a01c0b1550621072680fa540000078892886607040c401040690030282a580443d140e014189040310012440c155090585d501c00d00c0f6080b0000d48070715558081110310140100129070000c00441d21920240005e85610002c0003021070f1040010b00740c4a80300c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 69646818 1250 69645568 69645571
    0xb1e0607030f0c06060b1812030306130b090c04170a0209010e040311010509070f0e0408070305091c240504030804031103090402030907241d0a0302100807020c01050909010e 76
    0xc40c50081c40c040350075030350801104d560740c01030f640303501d008615691913840404040c071f4006000c403030920645400b03955055503403000514040c0039250106013028400c601c1d4201c04405a0014a203504500d08004400c66941140c8121641c4056000070146680d40c0440e0001300545c0190080034143c0c2014a0b040d60804064011805c21004012840104000f8810301c0d00421800b00a864a84d281805a81a2900c50f0300300410707515500c0e040c44006015841125483e50b89418555218410b12000501c8000340f030000b245204880349641081010501c101002c0c90102a603100c818107044451100310307001114002d000c912210007040100303003d0380103004580c0e0003004503494008c0c103002103000ea03001690310030000ea0000f0010310480d94642d035070449001101c20707900322400a40d03030010401000403258283c065842e1480344550340329aa003100103160080d00d21440c04044a10040ca1500c0c11600c480050007034500a05403980304030110741c802607008100d034036164241100e280710b4080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 69648068 1250 69646818 69646847
    0x90610140f061b01050108070602010c080604050705040f0b03061509032a1206060a1502030301090b0102280b090105160e040905070b0304120c0f0602070f0204050a0b1e060703 77
    0x5081c05100f11030884440d42542d180205000460700b9454818414944560780e0461402c1da41040070f00030810b6840317105550310060485010170142c4036030009856510807500000b250200b0404089014140703280190f0007040c098805141c80000c0c04500c0e4650b00034000c5040c0c4c9600b0280800c056160007480d03017258503164510f02012040f52400280c500420309614070a5504602c1c1040709034544010304500400710712003a010f8946013808000d4591005001d130f0391007240e8600380c0701c006910800c1342494035050f900b4020040118045034821295880da82110356840c43c4000801203013041c010385024a0440b204456031000380c140640d80c074445886081d400075519020500407034401c20648006011203011165241414200041841e003003201c00020702c180e81b1805000555458030030031300f454000c0d20058031100d0700d2804640700000790f080a50312a00f44014007001c00600d80c00842185400c940c2076100342101002030042c4004d95100c1c1ea8011380900070580460b00502418020342d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 69649318 1250 69648068 69648079
    0x1154101030b030607020f1e1c0207031203020706200a050906250c060c0305030402100302090d03050a030e0601050a0504051009020f0301050a0e040b010303031802040212090610140f 80
    0x314940b0129107084811141440180d01c414420360380c82030306115500c004030030500380d03800c80e142c0020b885658010724034140101d02d03512124a002107101384088806540d02641a000888a00c10300601a410041e004e503581c5290240d0191880d2007078401c3c00000448151f03a0f0701348804100144c0706074000070b800c1500810200b00b062280c1482110b028002c007441000040c40c00d02e0340c00c3c010764000300d540080040c40818603512010079044403c1d0395206a04580045140d90440750880103070041d01c03001900460032500800805401c44003525a080b80c90b9020402e1054140c01c0a950701d1003881a2a041010040c0c00c0c00941402d80249030b00c505076070020388241d0390741d01a100c100d80c4035a0304030300c40a80100051045117401d807280001000e1003809031b9a642042d8403260248107041c80010107050b0365502044d10040101981c1b450590000c03c11900d40c00320904541942a04a600016a0240c40002604191204410401e8404600d2940840d1407404103018441403010400307035214 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 69650568 1250 69649318 69649331
    0x603180604080406171e15030d020a02030f191101090b0406030203100b0301082d03040e01090605010207230103110d0f0f050601050d0b0d050115410103 67
    0x8000401946004070321440c0740da03685500d020340080011030100c580401d5802e00409000c0e0003000b14245049210400710041e0700742e201c3c000241e110035000c84e00755401d0700500c181501096004640c0c4045c0314000d8080c0c1e00000640500d16032500241940d00307481c040c012205001144160851049030030041c180200c031540c5580360980f184e0400d6002200090b000401c00641c2204a00c40100800e84c6841d405d0555040c040386a0b01c036080a000d0540300c0140c0c210051140344641060076070010101c2c00c0e2603656031200000e06400500f4000c03949003034141040054203510008803602210140c520046541d00d00728040348111954074802e0341015150502074594100c80002000c0084082a00180c04071159040c034003624041e401c44a251403034102080050f036002405c0347c030100b050440024207441c02100080045101c060f01800c15840c21101c0000c04510801001c251084248100e14803210040303440d080a0140390354190a1a2000f140041101e0103d10246110720504010880 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 69651818 1250 69650568 69650611
    0xc080708030115090b1c0905010603061a0909150105060a0207081e010510030201050f07050102040e0403020106050a0807060f0e06070f2109080a11060d0c08040209010e0906060603 79
    0xe9400030307003018000c00d40580780070105a422801e00313001410703a403800f0b50510501880740858101201000c45800307840d038090b41e040210a41c800b03000303140d003d030b810003645081d4810740d12059046030100f80a600c0740c00c0841d060f0040080d072990341d207009142001a1b617003404184501d0f0f030090381f8013074150300c102440411548003c2c4483c0d10700038070301e000322181070264400040c29910081c11050341d0364540841400540d0703000e0121030180400d0b01420b5a07600c841d2a19a0080c400d9a101c007d82c9040c002c1400200345d41034010500b154800c035000d0301c850b40c45640040c0c40d40f07a940301d0040450000c1f215592507500412090782288001416a0305140780d1f030301c9039104000300701002c84206003000111008120100582d00c04514a85001e2000904000c681070f6240c88484000d002c0b400c00080c0c2464640e505402c40304134500c0c10806011040341c192000e4120340301500e00300d00c82d1451400205250000d03145071031040301c0120051a01c0d460300e0f0180403030b40d84003802600d030388000500a000e8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 69653068 1250 69651818 69651833
    0x20f0f0d03110910030b06040305120d050903030c09040903090503160806010807050d0602030c04260c06030402011b03090b1c0b040605060a050a0e04050906040b0c0c0a030c0807 78
    0x11951108015114a5000510040444a1101000b4084802488120810744611904000303a0505007000110243c28000040c45402039a0004119110b184030b1243c0080203c800340c840407441c000140001e480304000e803510790100300d41c0740403102401c1c00540704501c4e09404c024210b90007814200c201e59202d801190524540304c6c000520b04a41e0b40c42080344c2c00c000c00020b4010310001001d0544a802d00000804d8000c0e02500a1701e6541c000c0042140b00c0704441c00c6070002d00540e14402c098407103401205980001c112608201c41c09440b01004050402d80116482542d059441e0804a02c5a504512891034540425410015800070210341c200c0780000074504c0c4841500c044108600c01310080082e2040445820300903400c2020400054440c402544c400106a06225844c1c030030001048a140080341d4944e903200f401d24040c4210b02c20b0104440b4003403805000034400030340d580c08400116205038a0303401060f900601c501d1010a1107101021502c610461801d49445440e41350b081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 69654318 1250 69653068 69653083
    0xf072c040308040f0b0a0b03060a0b0102120c0c06070302071a12060d0f05030d1a030a020a032618041505060307030207030c02030724020a0305030609180105010806060114030f010501030903020f 85
    0x6c0d0040e541d01d40c000d1461404000d03440d13000910000910902c0380c9800000d4030f440640c07214094501d00460416100d500c00c2c0030344409035501400003a165000350500039540c444521034030301c40040d0117144160300a400011500001400810a20247c8442d014031031440501e0742d0a890403044a048a000502d003400248042003150b00c0214003e40d00c04142150520b0314103100d0312981c0032050303450041e00c4204410080b60f40261449500000850320312080e603507400070030b0840c4000021054030030b454171a07014010030343c213607030401121144a403100c1c5121120b000e0a9844241800011803040c0700750000c0034000c1c1301e032404903002402d17940032a1a20f15140c100007201c10503407058103401c05458032003a40c242000e00c02042048540d8034090050310015000c00d004000346d5001410409424440a8106006800070041581e41d50760780c80c0c03147d02c15100a40020b11510020310601c00003425240920100880c00010b40d00e490019001800c01410071000d40c05622078400181c1c0d002d00601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 69655568 1250 69654318 69654331
    0x14030d11090a060e090c03130b01151202070c0302040f0207140102070b07050f09010315030b0907050102060703110d09111305041b030b07080702010e0f072c040308040f0b 75
    0x4a4031041400100807681006070003603c208881118032440d5540c42c501340c1500050480c031402c0c0d80b5224081c52690940110310043c0c035032104a000003131201c0c413141680c46517000301d030f903130340c0c03200c14003c4a20041e48200351010307155031400c510500141c50700b5440715612024414005180503115520701040c05000890b100c1103035408140d007010300c495404400e6009126182c4646010800300810301c43d40030310104181055629565418058004c5441e10007850700b040c0d82c0c89079407801c00340c2a545c0301e000303024043c014000d0b0f602142c40140640101096200b180a40c1410102903010041c010012950181c1c2c00508001003050b650304d90140085101a00e40c0000c1080d18242c02c24082126000440040c40300d0f40350300c10004201100515608143e091401802c1922031400c101c0c00342c1581940c801c25400340034405000b80b1800111a0300b1105044084414943c1d00b01c1030500e2200382c5d018043d9500c0e61400040c0010f44200805a4000c0c81102c02000e89540c51b2507244000300100e404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 69656818 1250 69655568 69655601
    0x807030f0b061903060c02030f12180601230d060207080304030801060e06040e060d0804060e0108100803040b07140a0f0b09060c0406030b130c0527010c14030d 70
    0x188010301020718040ca0344100d003526002d00e074a008036842e88041080740b01c003038146035a80440d401854400d00446075440318201300c0301d45a0b40e000c210303d5500801502c001303101c814082000c1d405d1600220b0106d040340c8294013203004440c1c1e81c90007021100303044161164440129aa1040000da0030300c054000b19014100da5503d9241c03603c1c0241a28006030004000d00c0f03000404038519130b88140458090b2960358002e00410785410010840b101100f0710020300b8031b031000c0340116865501c0240c12044c10310903030362540f040d180d0400c060004a00e5014031101500100410b000080c01c800c02400b4481c854034464880b55544035501e0f00702814190304030341140c1c0b070101c600c06200d14060b8003508034031a14041c015504048104500741d00ca244200c00500d0b881e0341c1440078a59400c02060840d8620000034080d605c3e0207100105564801004182130621506410030b030701055039540391100304183c440c600050040d0f11941800b00700c0c0c40e0664a184010058842c1e200000e005490144c18406007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 69658068 1250 69656818 69656843
    0xa0e120a020703030f02070b040605090409140102090307051e12031623010c0807122a020d090806130f051009030f0201020c0303060d0c0509071101050708071e030204080703 76
    0x1001003174002c1000c3c2000c110340c80010280480700091044034211455428140d503181017502c04100501561000980441a8110180382810b070640003400075003c110155540b80780c4070820800907070305001d45200780b00400c3c2c840e0307444d81c205a42040c0611341d071001100e0901071410440c58040400c0c0600302d030868811075010303200040d4081800071079a0070708000d20640d03140c43c10050920a00074201c200300030043c40d05011080c0c00d42d0060020f680791851980d03c101d601902003480711090201d00c4010311502c0b449940040c810300c0008192030041001e040191101203805801c2001148144c5900125040203030008404001240580c2094600800c9211060602a080d000910100820b40e4010095a210010080304803648a0303c22901c000066015040c03200000032070b60092a0855940018000c11540244c031200c0c420301c0d03080003440310ba40d0302002120785020681e03600c0080b5421203e988001110300c203550b0b00c440070f140b4006040c1565080c102d4604801e075401510024204403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 69659318 1250 69658068 69658073
    0x2070507050a03080a2d03020c06010609050a06050d150303020c1305071b0602091909050606120412020a12090504050a0203010503030a0c05010605151801020111030a0e120a020703 79
    0xa610003800d007114500681440d541352115a03214075001017080120745000f082c060041d03c280110060042e0164581440074404060300035030042e0400c91407403007444000107110340314507003080c2951009050601290304c0c108007640d6035000514034082290725914900b4198441400000041d40254002c04084420f20b05110032011a41107101d11241070404001c44240c010130005803100701d00e01d100b603000c08241854402406401041c07644807000e244a0807440e00306032000400c2e20300e0944104000d4840400700400392040e0110f04007543c140da00003d010444440004580c8240342c0140c81099210b035076004141c0c140d094100011981404041c880c5040c184690b070351080c442d1004510b59410035000130b61300e00482034440104080303469104100b000130342090000740406004c41c45100000c8070401050b811483d031404507640584058601d5603c1400384840b1191024103240c036503110343c503501018190600062400d131103030800c0c1f0b60f40e0f00c1529008200320007465010f070211a0461 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 69660568 1250 69659318 69659323
    0x50705180708341202040b1e0408070b0a050c2a030303040c03170c0f010207060b0405060a03020603060d020607060902010927150b030a06050a0503010c051603030e060703020705 78
    0x5000e4240401071500d002440b0003904190100c0144a81802c611812951008444d2400c0c40304500e11400d001203400201800b012010b410b00c0c000034680350852582582c041d49003130156218500848d8030250041001e034a184c0c1c02000155850301d80b0300c0c1b6244c0c400c402c40345407080c0400700480c0d5428400d040704100c0d051280002503214200c000d0341c0380d8281034490100a00c81400041c0000602c500c105094044000480b80d040310b0000a540801480c54581ba000b500305801c10344d00340c1d0a0241003102868207106c1e003441100018001c2c00704500310f03003e1140c1900000c0c1980c1e00010601114005651503001a054152141e000410140103602c0010b020006550180c1c1c8190305921420500d451400d0441c500e00b08076840014a0201c5522030300d0300ca0340f20b40e02c40942902c000003030084199840d0020f0041e5202910a01441640c4070141400c80d10509640e8000441c1880240c4170945003400e5085c00ea0301a14000c50b41d03c8100c07442c5030a0407001d5980c1008254002442401c21a05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 69661818 1250 69660568 69660571
    0x40321021902100b06090f10020a050a0f1b0e0703050604020408010905100b31020d09050d0f02030405010906050c240a050601080f0a0f090c0611070b0a1b050705180708 74
    0x145d800d00d040c0b11300c080101c1c01c81c0d04804440c62007400d1620010150610802800c10f4894010089a580b010b65040c07090800c402044184e9101001078032465601006540e00d80842c0d0f85014000643d60b1108001c40050102a00042c0d10680070480001c6a000c01d01901c105c00c4d00a202a009034180c00040c107040b01c0b20103c100b03024100c11203805100310040510882d2900203a20400c10b40c18803450618000d10030b20900c03161440c40d001d000d10900c600060310300281c0b8030b9911600d0713001d071b040201a650b2340520704c0717400d00250681d03105001052251014000825822003110b00e071442c00005603034011503140c0440d003007500480400922143c1805110380001c005c4c00c100d111401c0c0480d4408160034014001c03414582c031a480783c0003c0310b655200304180b51300301c50034290060302d0350030081c140b042000a40c6884d100e00040418210011022940c1c18071440d12160452282007003400030803c2030640c203480034060010006400d40307403950503840e03a07030205440b56418509040301811001c6c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 69663068 1250 69661818 69661841
    0x4030c0c140918070302090a0905070303120b01020105090705010c051c020309190f03030809030c0f0309030106080c09010603050714040803070209070f08060909031c06030201030507050304032102190210 89
    0x740e0894070030311103c01089040c1900e4054031b4007031090341d4070344400c8040c01d140c020042c010710a8030030010074142d100608848541580d4030500c00940c0e14401242a60b03000d4450040300e40250b030003084150300614025555900c6202550f00c06003840d814000f0300c9089440042c096000001c08c50041c0c0b600e00d06c0d01e444500850308681d103590408000d030700314505a02004043c09800c101040e2403c500308142d4050503544401c480f9030302c00034084580c50782c0054803c03078020b41c203100011959241c0410074003450b05000e0807a0150360700c1c0010850103001c014200c1014001c8220340e074003520745020f00910180144000460b81c0f90600e00c140100c0f80310040a030010010205a010681070f4816401da8216100315410308803174440300c1c045400c2d4400c04100b500401c002d140000720380007003074006608403030003600e040001d59946001070780c543c44210b600178001240101e031950381a000d1545240ca113800e41000600340320320149810f054030450b42424000d40d0003040c0300d001014050080181900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 69664318 1250 69663068 69663091
    0xc0602070b04030e01080f0a0203190504030c06150308090f0406050a030f26031306020c03040603060806070c02060304060507020705062a0f0304050603040204270b06090f04060504030c0c1409 84
    0x1600507c0c070100441d01514075183ca80e0000085034480038240c03401c1d0301c4840d810000b04854100f602d0094001c000750241107401c5810221090503e45041c10000100c9400003a121326050481040044001c10403a216902c15030f100310100d03d5803211148840614411075a501042585003850000c42a007100c13140d0300004041301900301079024000341c03508031400c80c0c0c01c1e001e40319440c41c00001a01420110312554440440e00080386640364000404a81002c2d065920035201c1480031101c42a065802035000031040010500240030b5502c682c0d4418410f01c162070f0b01d2919070740020910307841001d24401c0300d0140244103500d440015450702400c51800300424500405068081d101e000d5071040920410740440020155201c1e41c10003103900d40c9030000100244110101030071021050030040e02e05142e0000001e049042c0b4445048c010550b0020381101955156280e42c060702000b0821400c002e460000b51001801742c8005c44090141c00c0300e000c0403480d42c001071021034103000b0303d4004a01c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 69665568 1250 69664318 69664321
    0x50708180a031b02030109080c01060f080309010503040b090f0a080703110708061810090c0e1506030109020a1209030e011106010506040e070c08040602060604110c0c060a0c0602070b04030e0108 85
    0x3c0c0c00810103225034000044141000b520383c0002401007000c441c2c017034945c200c00100104143c106502c00d030103645014443c203095a49075019155a4010207045078081a0300b0008200031500f02e640b065807060420040725200c41c6030181050502c0e0075030a08491022010456000300340e042180000c9000320b0740020b29245144c5840750707603a0309001d42a110091f001c261065507100080c46100d0545002d00000e0041948a180c0070310707200d001e8800d4684030354800000c200e90000c0020b200b05842002001d080c01d40c0d00f001000030023580300c000c03202c060159a0025400070f0341c03140100c120703541c000e0320781e001e0b01000c0b6030001d0810300800f0b44c0411160004801840590343e200300341d070140d43c16038201c51619590f0310020b403a4030400000150518030301050000d03071076900040103803062006036002e100c208400c10007034100b03000710342031364803146c1004c03503149000d040401c0a00818403451401202914490320360000700d9024100989800301e581040206260b04034601058071307079007817030003071050b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 69666818 1250 69665568 69665573
    0x90608010203090703060b030f060411150a05300a050103060c0c080d0207030e12030c01140411010309030e04021602030705030d080f07020c0a1706101206110d050708180a 75
    0xd50606000080900760b44003140181c1d0303107042005113000342781030040301c0c100e0420f420240c1643c403006040342d1180e0781e44011000350a407111300ba070f40c40d1039894550509003100c0006c1034050182c07110500c5070001c081e43c580f440c568400c031112402000708410000d003650450804c207013602c08416a1906010401540400107006142142c031070b402e030080e006854922600e408c540f008401c01507594040c0420180440004000c8010881d500100000304008a6408800303402002d04480203000d030b580c402c1c0f0ba081d165000c0c2d001440c03468030034608072114000c40300000d001c980080f000c445a80d100d0004c900d0440c00c0030002007015060803070083c003a01c00c4544008000910040c20304980d0036514010540886c020010004002e0009200801c01c07038072000b04102034101c441c0c00c0c0700284a6840440c0d0048900c41108082e55502d112417004e801160b21001d003e0a06ea05250010200401040d201049940310b20380c0118490b81c0c0f41c401d40c0c14581d002c5003150000d01c02038a1984c0004814100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 69668068 1250 69666818 69666823
    0x901090b07020f0405040506070306090902010f03022a160905060f10020705030a0b040201031503030f1b05070b121e010509071209050601060909020304080a0507050f030d0609060801020309 83
    0x8448064011680e100002c0c4042a0412591501c50340c2040c2004117010801401064040c407494280d501081501d0340d80d00c1c6103082d1492024040e01060410840400082c42a0010103510503480d41400d11b140282e6403000700c2c07140c0c1001031415500800448110030307803200765100040800302ca00340228100107000400e20742403425140d114034019010000710b01c0c001c2c80b205001f410000c00b5035110290307608083d11003071003c131400c0380001c2c0b804110307001c00c0084240e40400d0301d070150f03a03540c00220303104410386070000402c040b1f4040d0300a6094120000701e00b00301390805001c040c0d078400e850300e0301c801000444103000b601810826190501c002540a110000c840c11624205c0751205941c80d4420140e50b5155040b00c40c41240741420001c82c00d200000070142c2c105d81c0143d171506030580c0d0f20344c405c501300d003c155002130014500f00300e00d0740e555200f40003400b1154018000e848604034003c046601c6c66001c0807040e03080e59102c078410040a046071003800c0c02880ca0500a51651404516154 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 69669318 1250 69668068 69668087
    0x30a0212030907050d0f0b0411040b060315130908030901020c0d09080a03050f07140c0112090206040e0c0405101d0d02030604031d03100b040c050403030f050702031002041202150901 80
    0xb4040c455850203517041c00254042e40c0b01c40741e045803408200b17042c20b04000851408800c0d60038015410480c0b028070b28248501224400c23555490840c0321320460030200b22171032408403860000e180e1100009004a09204015400b402c8ad078800182c1c0d50b411645264203141c0d8003041e42c0e060140c0e0140c100700700d00e40400c0d0191065414034001d03503188131b5200031007034030b0007400b4000c0c0021603082d00b0320310aa000000c1c128082042626250303a004014000082603401d0088000c3d08490240410486180e040012940000c00c41c1c402504150700c407008981c1d042d00c5003400500055440f145844400a00002c2c200ba040742601c1e44c1000c9050703030300030aa940002078001410081006014084811000785400b1050001016104800da400050a000c0c20074150744601c228540002144058060400c0301d04481d41510781105a1801e04000c2d19a908041400e0740c05004001707007444455001c0c4000d001420740182c0101c4050301a00600a015100c040700a541c100100490744230380e0303005040c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 69670568 1250 69669318 69669329
    0x6050102070b071716050c0301270b0a061d0103030806030c01050f130b040b070203010b2b03030209090f1806091e030d050702150c0909010501050d02070f05030a0212030907 76
    0xa142d03d40b0130380000c0030b20501c02d500c1c0c0441c4a00d86039104008000c03d941602c45002c4009000022441c6043e102c6013a43c0d03000700f03003a02d6051881c20300140c000304046a12000e403a0700041ca503541c0d030840c0449035011201c01c01e100032045005104268205d01c0300c54204a056005007040d1613074a0019199204070b241e02048650041900710002c400c00ca14803002e4503440d109143c0b19655599120b03610341181c2d2040344254240607030040a802c02407440342c450b03140030000003199001250002402c422042043e41055000c2041320f9080e15440c0c1f1007030051417010021080d80c500703140100061500b070240c400c8a034202105001d5040000103000114001024103202c120b801590760364614810340903903010550801c0200820a90040b41000ca101d84068990340b040c0e40344c5444950520609026562040c000c000501055200740c0150192099100005181140036240e01c3c11b10501aa000c9850340c1c00080c864a5440c0c2c1400300d08081850200d016086050058001d038582c541d90056 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 69671818 1250 69670568 69670583
    0x201110d0203160806100e0d050a0308090f0313090c0c080c0307110301020702010801061d04061508070f050a03090c09051614040e01031725061505030303070e031c02010b0406050102070b07 83
    0x8900746691840580c0102c6a07000003210600c61003890040c01c60942214900c20a00460ec0c0a454206000c1b080b12120900f2415a0340540c2c20f04115030000d2104003107020401c404480d41ea80001c400000800507850400300440e15541d42c0e2401281080d401c9110600990041c40a2801070742c0224015054529508065080d08225803039490754940400405a00909044001440c040849603191450500780d58034003c43d80d500d90150b62805500b04000c000444c1000b24200491103940140c80382445881c0213071030269148103082c241c400a81300e10841030300c02c401619100707400500c807841c03c041e034241103800c1c145030030807008140005100151a201c501d40d042c0006280503412100541904a96000f941031001c140310002044941c040b1486403404072201104d0b103010b681c000440d48018021407840d03540c5001252190300080b24650107100f10740c81d03c10340b824852184115561241e0000403100c82081c104801d941d11540418195004008180721072508981120000b0303400072107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 69673068 1250 69671818 69671837
    0x250201110a0305030405010605010504080307060e1014070f09050a0314330112150b0102070801060b070312060506030f07050d060e040209160801050409030201110d020316080610 78
    0x1039a1280c100c0405008a024030110201090780100c090b50081d80210020000952948010b4070b0601c9603010301d1072582e000f0b0040c040091080d130890994981c152084d1520b030311200c580d22060b034282a20703402c0c980301d4000070468525401a18030300c24a100345420031280d850440410403010782c501000d032a0028483c1c2c20351079842c042081b14091542d210000d68940d0702d540f1340c145040105021110115142000001c5c2c00300f0407a80303030040580004607000c03201d0240d0401002880c0050200d81540641600014501e02c02e1084400030119007004641c0e4240f075145c001c21030600f000800440c1403520000740466100c8500396540111100c5000f80715466009040c3c80b03e02801554110b22401c015010030b081708869100350086209440f01f080d02d441c7c0740014014081044060000900081d00402192401c1d030885280300f4003d00000400c1e092980c0500411761185103001d06594000ac03e02c10304004d054500d81107031123107103080c941c5414100000395241507480924001c0140c480c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 69674318 1250 69673068 69673073
    0x10e0604050121052401030212010e0c040504020f0d11030f030c060c09011808010b042715020c01021201060f0f0f030908040806040f030206011d0109020c16090204050a0b25 76
    0x30103100c002c5102c05581d500117000d1400700e103c6409000c1240203192141d8402c0e8499030501503480030448540c050700110803074006010040000400580c4d1001000e00e20301200c0c0c543e00400684e80e4040c082500301d1003d54820705182180010391180c007913104018075040f03140082a410707041981031044503a1800c489004a4a946030b208000c4d013650300302000007035000d074150301024040b20292414000a85110705c1001c04050040500c1005c3e052612010b00156880c2485006035030387c00e200500700300815040c0d5003260000c001080004030204010300034250030100810a810543c9000042d0070065500203015881c100081e07014142c45d85840800c025240b0300765030182100c0300c200c52031740c03405042c0340302c4044400c14160054090000082141600400300010036590307640c401310164a003260000096001c85280c070b0a6001b04c44500d41c9649440280400070000c030040035884509140411202080036071001e03a00540420810454030081e41e4204200301d44200d0030f610b03425060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 69675568 1250 69674318 69674323
    0x10080a14010b03030d0b010f0e030c0f032404020909030304030504120309090222091b080c1201062106180903020c0310230c091e031005010e060405012105 68
    0x3540550f4140408184151401510b6100c840103003002d03a141e010302a89003800f40c5404492071111501a003146402c803569041192124014100181c01c803201c00b142c940324000300459540d0b02036080728148013400150300e00512116004101e810186245051541d8081c00c644110302c41e480220100c1084d810500d40035002510040c240f01800350360f40d203203100c038100e000c01721507140c010207a009000100342c41c0202d1040014038940c407200e406010407807040903142d9550041c601010420100b0201103056140104c0381c1c001e00003529801c0d6422030340d1100705407850124083d0084581780c6001005061034859006901c0c5010840010308444542006c03800c2c40d6401003019014400d81d141000d1504a40d800350001420f0008a60751855109c2590b482002c4240d0761400103900600880c7d41510300440006000850f00c0c92100c400050440800d0401d00014003031104d03940e540004202080b1000c460b2640003070111800c000e203606010500240a08003020410a00151b050600405c4401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 69676818 1250 69675568 69675581
    0x807050916081b040e181204120c0305010f0b01020d0f0212030612061008010b040612031b0b010603020d0b0d0c0621020c03090f100c020409240f0510080a1401 70
    0x40f6203070396a00d94031500c07100c004001c2641c01046500c003204002c251885d0100c0c5008003e1500c403041803a19240840300d130f00b851070141090f00d8601c0341c01030000000740b003440390a101d6465084c1c08600300c0020000a402c10b0310703425280d01400107441c24401825030110b1030100716109880190744a440316008600e06079526000703002144180818491300545542140b021966164024807048100c1d00c1400213a64443c440c2a9542e03e1070700c42c50700024010081082d4051506200700c03000b9000f9100c1c0c2032081c0007070b0300c4600820303800078091018882130700034281210001c0c0c42074000d011551fa6000581405803040d1010031080b080c01000500100d40c80380c000c5480440d0544d11101d040301000d460303a01c2420a80c1c803074840c000304d19100e810035440820107481281c403584c0850600313409201c00382182c8071040350308040381c04201e081954100404110311030181e60009130a0141c00480b411144050802d10741c0e8041c01a040006100006a41e4042035104010f074070710401c02c0c40601c0c0075006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 69678068 1250 69676818 69676861
    0x606080c0304020d060906050f040b0c04060207050d0206071502070209180d030c020c1009080607030c02030a0509040212130c0b0c0a080d060e01060804030905040606050403030c0c09050907080705091608 89
    0x105800c0c800d84c5509c48120340c0c0942d001c4d00388c030b40c2c50703071110b8000ca00c0038421481050007680020b0000c1006240801c40d075045980007a02d210300d0180c0c40e07501e02c3d14031004001e915802d1580840d0f00320030f5003008401c00b948241c0700e00c03c2c29001d048080600d55240407600c0d03090200360f21071450b0f007246032082c40b00c82202d86015209201c6404401405410400d69005541d16480780c040041c2c3c01601c00d004054081107103801446c81d110041004803070544c4000922600541c08000b01e400d0194040007441c071981540081e55055102c82c81c11524079101c80e444125204010b0292402c410300c0810b20420459102c54a907650320300b4400d0b894003410b10355205503184140c51000081781038015520034415072103039880c05800d035140d5013000201e490b60301503280061002d00091000a004001e185180e5002e8202d104810344d80b272141a090358801c03030b80d4140c1c9810079441044500800c22031000501412105004545000d10000541404c0e80041c48100006140844d4800344001240c0ca4443c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 69679318 1250 69678068 69678071
    0x90f0f050a0e060c0406081b0c06011401020f06070203041205070b04060e010207060921030e040e010b0109080705090a051e0405070510020604050d030e0f03040e01090606080c0304020d060906 84
    0x290680e00140100150b00e034000d19030150800254058014100300d5041e1000c6845000c1180c54000310f0000c403860401c50056119002c0010000014007004802d00914200e542507005484102c002802d000001100580c2a8041000d1002403030b004000d9400b502c6c4290101070403881c10703060003454144141d002611044c00040c000c01d115038008070400084500ba0200d9940c2640c41c034003200c9070300c40751040320701d19001002000300c601c44110310300350490301134608004103003059800102280d40e0981214040c3c0c0d0360701c801c0b4205507009404071f001400e0003c06010300c2c5203003002040c0030345c100406044003180d44400045540c800042c0c807002180751720865503210310b89817400903a101ca941c0102d80c8202010b081c45c0003001c1c03001900718031071a44031000c3c1520490540040d001340040d1681b07002e66002c0d0ba082c4060701d01c1c040004d8001010003500d04111945003107564412a100c680045042000600c20030000300c41c21411260096415509140c15803100d0a1050041044280080c4840d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 69680568 1250 69679318 69679321
    0xb0a0803030708010b040807030f02040207050615011d01050d02090a08070b071e050d032708030a0b0f0a0b0304060b0a0b0702010801150905090c070f120f030b0a090f0f05 75
    0x4010000c0903510408007600c03280407990300c80740c0142c000e005503c030702d40d45e035804440c003030000a614040d10a49180702074409800c00c100b5554050400710200c641c0030300a484010100e03a10740c1d01158a001040c2681048524170543c8000201036100380d4242d41a81c07900040d98071303550749801480da0020b040720826580d00c1500d4008000301030344210403c0d1101620b44103000d1408245410178503480d94004020004001c142c3d6040e0040d1a4010a03607540d01c101c00c810441580b00341426154a41c41512031945d00d1401062410840342081c641034011028043c454415455981c414010385155060300c940700d546500e09800030b0030404004540203542c074a00003610114200140211a100b40c030f80c112542c0c1c0360201d05540300d1001001c0b40010320141400c001368142108410307040b941c122401c5152417150303203030544070381c080c84001c640c18107161000740d480c0c03540940c0c050410309403843c0610019401d240042c0340340c050f0340035a100445ea28003580d9038400c0c441c0e01018000340c1d41030b02880b06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 69681818 1250 69680568 69680579
    0x903030c0f030d0e010213090f0b030303090a150b0102060708090c0301090f030e030619021b0d0c02030f06070203030103120309020d030905040b0108040210050f07060204030b041109040309090509010b0a 89
    0x40b0f40008990150080c104011088901c03018003e6070039100310588500c103540d142c6041c00000d0310b40c60040e145056a500308140040c2c40500040d4828403102004200e201c0d100d180005d41c07d507103a10184101b52500a00c01002da038007058661300f0180030328005100b515070b210b900c1c0c01c115900d4142e41c3d0540c86e0003032100822040c25490401d86001c1c2e1180402c500021043c03540740c03081244c100203260324000e1440903008403a4003401d0300e4044131008003125a40706403c0c900e014010402007000c101080c1c000e60031440d040000700035013000e04010b0110303806c040384041d54900041c04010103145000d6644007006103e5805070440c103400038904280c1c1511800c0251500c078aa01a4500a45c1051400b00403540504540b600543c0c1c007420542640450160803076013908600307800b800b480c40802900b800304a0030b0014001444c0950740441e11801c1030300d425000042082d1400e40955180d80030040442d42282c00360b400c50703d0001c40856a076403501602e078010b2080d5160240d114165040201d003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 69683068 1250 69681818 69681823
    0xc0207050901080607210207060504080d05100308030a180f03090f12031b030311120601030b04050c0711060405040e03090307050d02061c0906020406022119050903030c0f 75
    0x1156015107210302180d80f02c48200c0d0f211441180c0c450080b03a03900300c1954450b003001940e48841780101c1001824101e1590b1040c0c1510403e94003a554110040340500240c2413900c1520740100803501450305586c0745645400e1b260100400100000d0381e243c003098801414500e00816117030b8000e03504280900ca6240c0580612418060601c410020003000b01700068150901c2000b19010785076150514007854240806410b80310048003055150b981c020711051029010301146900035503007031801d20b0a440010202c500d80c030391251040d8100014400108506000c40701102e40060350340341540c0310900801d0041c412540480d0708140340c940d200c020540d010000d412007000840503548443d5542040154002c84050301035400501004860f903411610014904001a0f10401003000500364941d4403c0b6007050b405580582c0042c41e021662030074100c014501c03203108500c0c09040040c465108a1619060360960090000008540b80645c1e410015515040c60b210129000a08504450358 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 69684318 1250 69683068 69683083
    0x60207080a0806040e03040e1009050106090303020f030a1407050111030c04080f0a03050307050d0b060a080604050a06080606060913090c08060a0e030306010e06070c03060c0e0f0607060c120c02 85
    0x107002482e18008510380e484c19004807000c40308610002c504280c24003001945208002e02607007442504240001010b6050380201802400203840d54038a0a2640c00d010307080c21128040f01c088d40d001042040034042e0844079500d0fa0350041918113848130014540540102041d0200d0340e1300650110412649001b080000e00541d490350003075944622801c424507682d52010b6200902050040c070024088511506c0a070001c500a002c0c0811a0312190001c00c0c16a84400c446000150300d400400c4100c0c1400c1c01240d8029000100400c102498208020b0300e0320360281807144601c1d00012032028613610340540c9603900c02015410000c11041d0300d408030000b80580b107480d0950060000003960b4a8040c441d03001481c80c2c440c051031543c0d55820046414502e44d40362158050010700c10340002c1900703990700602452050741c0000d092034000c0c402800e452201c0d42654490a541644207150307442d1001507034240d60380554042420740310103005a81a12088003c44c804c02d00e025203c801c0c0c60360000b0380c00d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 69685568 1250 69684318 69684337
    0x80d051602180a0c14220f0312030506010815101403180c01080f01090c0908010c03050912091e010306030b090706080c0a021c03150905061201140f09070306020708 72
    0x4000d400314034803080c1c840304841000f0b130280ca00144061103059110410382000e01c1b01c2818003105454031000300f0705114015800c00d50f030300c0002e03031000000c84d0f805100d00c58010b0400d08096032240ba080620b600010342010440b0300030a41005000c5105012f01541d03040c0751a80c6080c581c4a00e050050742d19203a032041035a885510903481280503950180e14058010001c01001c0704660f070900360200301914030b00b01d101c0108100c15900150350310080c85500d00100d41a9000304150500d010003900c0c0c00310381c500c4003040a2040109941c1d5981d1032000100010082200140c00d02e0204c005800138a010391010748010f04c0d4004210404401107280c10a403025615584810f440703807101d402c0c0e40d000c0c6805107009a4000d26138034501a5620b182c0380c2c2075010500c0d021030f903c5500310b030b0044484459800500100d859100740b040505d001100d00010250010081000010f00314802050b00c1000c1c3c00b0f4964071107080003240c1c604000307114a6000d103400080540d44d0704c41c549054000755000c209070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 69686818 1250 69685568 69685571
    0x5060105010309030c06050606070b040302160608010f06080c1b0609150103110f030c270f0412050a0c0606060512060405040c05061c09030206100906080d051602180a 73
    0x8121076000f4402e002d03410360141d4481881030982e603103c03c010500503043c190b0010083c000d100028601000f040c4c0304a1103a0b0141002e94485e11082038000100e40091092140300c400605c040c10210040d04200d944030301e000000c6403200c1c01031072820701c00d100c1071f0104052017072200f01c0741441c00034030340f4018041401110070b803849540807170381c4451081c00000c10b4100406000c0300d492610000d004d04401004050750b042d10118000a1818400c00c52008118124405038503aa80301644206502c00c600445110261034203a4455145110039901c4809004003c5102e4000c588258101060154456400c10079035450301c801500907003000c580c000c011031181001495070b040c039014290259601030710f101c1d907003401d00080160f0340d040644244901005840c0001194040c1d025401030346000c3e0300901801d00703020750001c488a020780c00c1800303018142842006001000a850130708000549007640d100e211010181101928440001e0362004165400a00080030122494019404d8050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 69688068 1250 69686818 69686821
    0x3110304060c031707090b0f091e0406061805090c04171c020d08010302011d03010204030602090102011b14030c0d1b03060801150909081b25050d020d111203070506 72
    0x4541d0500c013000c0f0781182c00240c0c0800200150304100340174104542c10494400d08200f070301c40c04600103c49070980c0080501d2840b41102003800d0038031071400a4509441d00c11300c08a960364440c007140045104690060402a00285042d03c24100380c50151480000240c0321964540ea039658170700800160b08601d013003540a401c3c0d402d0001540d13000007005a29803215980c40c507001501d507076005c1510810b0243c8038071f5102c04a84e40030720060024511801c00140c031600301c20002800c5440007040030303018000c854140300d8142c2c0c101c040c1c4889103440500003607490f0b90f89031204000380078a80c03202400030305048411102440c011104006400c0b1075404014440c0d4a0201c1400e80f103041c104410348001844050100e00c045030421440c080c040d1540ca8031740100182d01409840c10031058002d00e802850b40981c00c4c400c1861031000401c80501c610601e42e00700000143c014485243c005c1c4900704207040d0b28200000f13803182014401004110728804290720f00302c03e8503030340301100c01c41b000c0c0110030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 69689318 1250 69688068 69688097
    0x3030606080f0f1906060804051608031801120926180f04140702031822050403030e010c0e01110601141c02040f02070203010c080903031303110304060c03 68
    0x100c000d1044803803014180c05a20344240030143e20b080540505610240081c1c0485140c40034041d5500800c071135558401d580c9042d0402c0c504181840c541f0f4002da1800d5502000203010000c03e4a0200e100b0f105180c40030064440103840109200c1d24000c6801e00740809642404100c80c015011019071094030329154a00700800c4009204140c51307840741e13103500f080340d40c0c036400c00c03030111105418050b200080102003080c4240b0145012180721005900018941403250507094140b8480c1005403904480400c680000d240781002c2c02c05540e114030b07a524002000e040c070a0300300f1411407000314020460101840b1000348000703943c084880c0480c1c81036210600e00038000800030304a030403450000e0302c05d4081c0c50030001c11030b413103950360310040c0c250f403541e803001d80e50f00d11410900c2d111040c0010398500180c41498295000c815014040c09041010814007400100440307500c00381c0071424404000d000d180c00d4440980c640743c901c800d48408103001c075007c0c0d0440040d4181c130707000380c42d4118801d0700107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 69690568 1250 69689318 69689327
    0x4051e04050a1b02010e07120507051306050111010204030f0305030604140702010c1107080a0f050a1703060a05040e06070806030a080408010b09160c02060a030f02070501090209130816020a0e1303030606 89
    0x50b52102c0c0c55900003103040101c2020a402140b401e4270620681e84991751700d070000f40c00c560054030f482d0350255071040300f0080c2e980c11040d01030301e540c0600e000b0750503e80f441e10b9052070b040704100064140302c400000504103035200c0d401000d6030200ca503a403040500f4a003000a000f40020756152001c00c12034180d440390207000064036000c803441c6174000c2002d0140d035950307825101c14022080b03130507104035000000000c01d0711074210012070412082070b031249000c1c4104101d0140d1a84030b81c0c062858200c440c4101540400d0b140c3d4000600e080020350740d260080468502210300c54094a0f40c040814041600d00042d088106e003d441150080081e441c2e040203800c1c03041c3d141081c01d01041c5607884980050410a001d4407080380c3c0781c01d00045040c1401d00100c143e900c030900488482e55030314840411403420f0070f14160850001502c3c1e848007007940d030b684103842c421400070805100c010300d40078003150341d1140d885e80a401c2c090682d242c24180f0940a010300492188101e0119090260129040344507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 69691818 1250 69690568 69690581
    0xa02040b01140304200901030f0c06110309040b061e0301140307060f1409040615030507050a0c061d03070b010f050402030f222a09050c04051e04050a1b0201 69
    0xc00900030f2840d121541c8501340c5440762000f4442d00c0389109600d882c0d503629408568003c500030000040081114609030b00e40c4001500910240440e50035080c5c0042c2d400025661108070a031390008403414000c002030424025045100284100c0038603401801c3c1041d0003450480350259102d80da2071200300101070b01d4150b14050300f030010b42d0000c100d040d00c0c1d00c50310001c00c81d040003242045c50281c18070042015144d00c0c1d00038103035204802420540d03240d45445002e902c0361040c07906508000c84030200400248030018040e084503182c8601c0034035020174640c503826250389141100da450b805441c0504009209206020b205034040e140010305040c1802101e00c58008185421495036812a0041240f0b0810f06400502c0da0080341a80c006040c65203810000000a50391010030a0114004802c0c5e107666040003c0d4281401c0a01104d03c07400001d440c155031044070140340307580910b415030700b450541d044000c0c0c0c05402c1c1010310200050641c0308004100000300080703000002d003c000c0e8283c482 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 69693068 1250 69691818 69691847
    0x20a08030307050a1e140703091a04151d010f0201240617010e0c07050c030703051b040605090c1c020a0c0605130209010312020307080c010b0307120b010b09060c0307050a02040b01 79
    0x2106c1e110182400c5007400418045100781840035034a520351403070b42804890001150304803200042d040c4011030001c0b2591084050078900030300c610400701d0441d200c0e045501203007814000851050300885000b90044c44109894000c1014408200b10200c10010341c144034800115282050001b8210f03005a1003e0507120b420b04c0c0c0040ba51100d080540c840e03400303003005550310300652000007495942405800001c601440090200c188844141c002403440002c00074441c0f460488208503580b03910700140e82c002c8110740c0d81c07503c03002e02c030000410000355048400c4040e440000c1502d07040b500100c1c08a001d0f4012035081005a44240300ca030319054000c0c0c40a540804142c004100207281e60344544500e01c10b51041d04d041c12499543c410f1b440e00010b00004480e5103c0c51509440d0408000920050031654010a40311440d91030f102d15014040c007035000041e03000506030b80c003502e031001110f0850074848103d0359241c0c49800c150391201045181284a0350500040c0c0c0318644c03040004a0b1b0512 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 69694318 1250 69693068 69693077
    0x6071211070b090d080c010e0c0f030106080604080309161d07030204080a0213020408100204031401060b0703110a0c0303080916050310020304020411070c0602120a0c0f020a08030307050a1e 83
    0x1c0a5080202c000c6000c031017140c1c02c60040006000c506000c2c01190814582040100303900040c200030400500301c9500b416004c0d071b15003901000666000a0310a80164000c00300c10b5032522a0741c0d42174200399902101492051510600013003141d441600c031000a29034604d40590740c3c480d01c10846c10b9204621078050540d20000066015142c21892040340c00000c410062030036985001c65418018514260803800344c2c01b06040090005103400c00042c1700c103001c0204116400c3c102403c4480c06207010150801034455100319880c4000c010f459072072034200d02d020071191340d280380c006c00c0280c048078a400c5d180903211120024080c00819a815600014084c016104211010100a4100420907a802511104050007000c010401002502c1c0120038140c2c480c1d060000117494101c227500b00042004041180c8806983d201e81001051940895030024548180c000200d00303110a4011000718003001050002c500d400200500d008407541d00d03000c0e0440c6c81c0c1900011b0415006105d200132a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 69695568 1250 69694318 69694327
    0x610140603060a170a0507050a061b060e06040f03170c0a030f0b0d080a0207080303040f060b04140c0901020106080c1e060d06060801050a05040207170309030906071211070b 76
    0x103182260140d42c2c00400903007851012075503008400078408103003004100580148005505203c0180003070f0014110589441105c0c0b440e02c24014240303c0404640c86d034501100480c0001c000300c68024000c0794078808125182c44c2450305240e400d0fa4180b40d8100d0201d100c41c2a5142d5100c4800d4403241b04490702c00145040400d08201503000e003080c0c03599100260755400203110b0541e2000c016030f200d01e004e401c0c915200d05601e080a0319000c440c1d08510007950040c810000091000d54441440a078804000f00308410700801040140c0800588200c49074100b80030046c044e44100301030020202c00741e00a1082c2613030b4105030307610b0b2440c1507030458000300c008820000700c8260300c0d82200c04020160130705140488100c0030204445040e08484002003500004120302e26040e00000003030b2804980031890070035550b665040a116444081c0000c190200000344005010303c01d6503460200602785030b9540b081407400c1c1c8143c1196403000c41c041107414000040b80107000070320205a0304082c1209281 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 69696818 1250 69695568 69695609
    0x314070e150a030b0601170903070302060c03010b07060b0d0f03031b03060302011407030e10050304050c010e06120408090a080115241d060c030a0207080c01020309130207080f0403050610 82
    0x6001c010202d07811f1000400501c4041e0203000d100a1007505054007460f128021803800904081000d842c000301c400050005200420002088411003540030600142e05e64008000c85e0400319403c40240c03150002d01d89500034560140c02c00c49000c291a44111040c2c520782c6016011a202400040d001070041007080407041d1861000341700032406070424620411081c4000b601644c00b08079a940002c40110030b11003000010440041c00c2002400e08000f00c001c2000810034a01405000c010080078010204080c0040c4c1e1003240c0c01310101a001003006511003000d43d0181c034000c149401402d0700414000b92820088610100008401c0703504084500050300c1251400c80454040c22003070400844200d481c5c0c0c5030001400a200e045001c1e68840805003000b038242340151b400742c100d0350800a005072007a03a011085543c400412030b00c0d04455541040244001e00980f10000c0c403004000440c812100ba9440180c41101c0c8a107044820958401d1503030389080300b0318403601e00c80c1c2c0e04000400d1403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 69698068 1250 69696818 69696833
    0x7120902030a080a180e01030b0c0a1205070201090b0603070b0405060f160309090513050607050c010906020d05040b1b090d05010e0106090501080d08160302070c0314070e150a03 78
    0x20500d00050485000c042162501c856070303445030b0311a0000c280070900080402c0300c003c000300020000856669215031450712840c000c0003006020b0b803040000000c620f000d80f80030381100f48002031454010042450700a401a000340300d60700d0183d40b2000840e00086a40c41e002500b5000d944015120320300f050326040c244003080e008041c8041070603009103d1142086415100743e03400500a030358141b000c51038121400111000a06003290030455658150003141001502c0c5401c48030382c3c0b404c00e58900103c10002e0041c0460398008049038000542c81c20784a0f03281c0c1020b4010781c01941c207250340e44c844903e100c4101d0304090181180510034031914520345040b2500c030745554005c01c000f00310b843c11410b0250131203901e90400d180c030039510310050216020400494001c1081c2d81000800c41c2000714944501020800140701050740000300f1804006140c1c60500056a00203101d0070401550ba141d141c035402d01c0d016a841d41c0a03c10001070341c1c69004031003a424a01c020b4280c420700c60a5072501d60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 69699318 1250 69698068 69698081
    0x3040501030c050d0c0512070e1809010605090903070c060206010f06080402150c010f06121a06030a15050105040b010519030f020f1606050c0304020a1203020a0b0a05041a0712 77
    0x1040c41018454135013444010301a40c86040d500399103455071280400c0807003c3d0b03500050044000c000800c942c0400d1364a54503400322880d10155050807541e516400e480d03000d05001c0d0000d6800c415000c090001d140400000782c0000c3d4414140c1060b210307120340d4202c1c0e540382c00b44a49121071100d1071040000031f00590321550001e0020f8100e0180040040e652801c980c00034014444e103a55032000680c521003188940d4010f807100c5050b9103911a4540c8400d940805081c81a0125075100b1001c80d0341c540d010420001c25aa100a07040440c40c64800300c40c00800d801d11441740110f04014640700d056200d84211588400010341030342c0960012403003200202080301c4140070301070342007281ca0640031409014100342d100c241d00c14541908145800020b03540003412180c1ca2031014000d020050f82c40e802c00c502a01e103d5199004900b8403400d049141c0018400013905480d1f6500600c4844000c5070031071403040740500c21a2140201d034011045003010100c8440001602d007c03030688103403041d50400c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 69700568 1250 69699318 69699341
    0x51905010609020408030d050705090f130603060908070c05030c151602130b010905040b100507051903080402010e0d0b07050901110105150111030702010219050a0b09030c0f030c0304050103 83
    0x60750607240c1c0300c91422a849a0064070960740003081c040420300850048903071041a078503100d820314041c41c0c003084180408000c040d100c7c130410750814030300c0d10701b82d8414001560054028481511182098016a80030850903201c84859010110701800e00060240c80e40c48058001c0c01c0c8a03008140d407101c1c3e60048010322144035841048440542d444910030703040c0305c80300c2034000f80e05001040090000f5242c0d6101c2c40c051414001c5100ca80e82d50b00c8400007076442c090404503030398400e51400f14107213454002c60f458020340d015854024564800d0344584941c1c401c4c0c0b42d900d0149640c40401501c0c20107000c2c000d0039412500000f5181c948142c01070705100c80c043c1001006000c040080c5070a540c4101d0749550842d140c030094544641c2d1200168404100c80d0000c0c42c6040200c0d00000d4456607850441040203144c01d0b00e0317104000c07042006185854100000b001c0c1d40c2010015181c4a0307118102480b1079100d4103c040f44803402c04000c0b182d810480c0b9004515240c40e10700190301074401032419 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 69701818 1250 69700568 69700571
    0x90f1c1d030d02030c0705030a0c0504020f0d0f05150303070b010303031107050106030605070311071505150402070c0501030e030903150a1407030c0f0309031d04060f08100b0d05190501 81
    0x22018151010000c400d0b03080b40640141d500c4102c0380f0900c502d0000c0e06d902183c840c0d0302000040000c660444c00300c0090300c1050b01d0140e038a0b802c80f41c001d4418032590f5180014149007440e2194441080d901c85802690340480300c0b01c024860304105680c030702407080043d065100072001080020f0180d80a440c40c1c0000d0100c1a08052071a10b450382103038101e078019070310b03da01c0d1000c001416a2510803800910390039642c490502c00542c40d04200c04d10030080300d8164903610320200d072a0390842c810035081c20030010002d5641d0f52242c5400c4100b072a46100300c9011a0604138510400c90011080c0ca00c46040a002030402103030f250707041d280c41403004e05a80c1645503201d540e4084400440c0c03105200309a9918080b98981b40418000c0141c22400c1c4071204040c5401d0140000940c00315840885003003402d00c4410201000001400810259020720a032801c0200002006480440c03c100d552140c0c410030007112480c3c10901c2140c801c0741c480184242c01002030212141d1b10a500c0c035607224040c400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 69703068 1250 69701818 69701867
    0x1b0603020f180333070c030507030e0a05120109020108070801080d03050604020d02070c030308061801060f0201110a020106030209130506070f030204030c0608010504050a060602120f130b03090f1c 86
    0x281c003240e10030f2480c4900c0c164503201848510004c0b0601000b5007104103403411b500010a6910024070f203004d41c480060030041006030802d100c1c0d032403c10300c4e0b01420006000d40ca0042c04429145d0080440300c2081b40401c1402e00083c0d14180a005e01314100d440c1c0f0300190031482402c4d02c003100104030084c80a0303405582803060416100c61403000d000c02030f20411400d46994198100901200802000351303102c0c0c89868042c03044440c001ea44541114030038101440c1e42d6140d41001d0b8054003031821403031001c2c0b002080b1440e1090b415042501140d0094602d8115521141107180c1d08281d0741d04040c000d5406800070904c103611640c0c648003031812030f24005080036200e6440b0b00000009a02c031500040a000c0140250718080c851650418820241048242d00d8424082c0d11140a0b8192014045011459040340f158007403c45004006501d0502ca081d6250204060300d40c1082d2103041640c856848214002000003990440c010080c02c207001003000e0031032084a0a001616110301001210030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 69704318 1250 69703068 69703093
    0x301020f0403060203010e1819052407030f060807141302030702060712020903060c0a0c05120a0906080106210908030f0a0b040b091f05030a1b0603020f1803 69
    0x4000c1d101662084101590341c2d490100013050540e0054403100d00c034698040c018206080014030f10209850600c3c90a0710040681421420080503500446140e541200040d030060355407031a0501ca800c090721b003000b11840745403d40080b903025000d100202d038801c030424414400c0707440c600040c0030030040201514802e8032150781305907042035490300e025070701140c00d220305070303801c9490035200030706001c411801c0407110b400180e62034401502c40520083c1c001400002607104040301c2d00c071590484100d4044245108a40b07009070f03c10b16444000910981011130b0701c510030840302e4100c07800c65031000045141e4050f220014041ca00e40e5501c1c0c140e45000000028202c017020790b2080c00ea007003000d14186000f002d89c0c0280e84010b4900762165140c8402154150355050311190070140545502040700400041c000817608107400250b07040c4a43c4504000300100c00c840345a02d00281090403c18541d9504c3c00d0382039006028161419440511030403403444039403029994070040007011075a0190640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 69705568 1250 69704318 69704347
    0x4051308040b0903011508010504050c010e0f040b0102030f0c0a050f070b040603050709050406091e05010605070809120a050706030c14030105040b0d1e060b15030c0a02120a030e100e120702030102 86
    0x203507c00c88003039443d802040140041440300200e0140c081c20482e0410002c0d17000602901c5004440718800c0356a18850700c80d9910230010b0b02c8005541c801c01d9540c6995104d007055980c03a07401021110391044417880c042e03039040894010b084441c01c521b450b0034581810002c0d400b8040003481170701003280c80000056199103030300402d0028890b081c00081e020f144e50000031700743c000c014003a40310982802c00401400358048200c4070071a422503016a21152142d0010301103441c640300e9840b80d072084004400c01e00001107101300461307106480801c13009070307800d40c00d440e079000c0c40400843c0102c0070b01c010403035401c0a0f04a17154218000306030719030000c225540c0461581001000c082018120310310b00301049014403030401841c0b01180c040b070460900141541c0c031440003c001da9121000481ca21404500802c102e0500001c5403050784e440384401d0a0003801024103d40503c43ca200e40c1e2184614074141b0700c11a0408000390016210b8481d09030f612503540d030700104040ba010743d07003000110200000d0303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 69706818 1250 69705568 69705611
    0xd0516030614060f0306010612020f030108030a08070c050d1103070b0a0203060f0307081902120102030a0b01030506120d050a021518010c080c0301120f020303070303050604051308040b090301 84
    0x421000031481082c0d01032100404009101500551481d0082445036400150f1141141c00c1d61800410500d407040d1404003074020302c0c071205d1010134084008182c41d003020020349000729495983d84029510910700310b0b4030078071400e0042d100e0b4000340001c02403203100e41c001101034401c030000c4034a4a8241c2d56000e0546030112141c2500650200c244034407442c280702c800c040b80c1021001046518145242c0c1c64455080b610440e51a180d02440e46017191644180c2ca2203044861008644928000041c070001c3c02586010500292a040001d9140d00e4544981252000044020880b402c420740b8141d503282e120030008001e611600c0c5000d16581510f40d03200b40304581006980483c4445c0141050a4078051104032040c00200030801c1240c5464a0130f60341140e09101c038a1119031a80d0500000703802104901a405000010702c0b0702c00c0c136425801c07440c050340c410b540422540d038031041d10203410203182100401107102000100702c00c254401c084c0142d81c100400001d03440303004e12105003030b4690 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 69708068 1250 69706818 69706823
    0x1050c15040309050a0b09131b030209090109020f070b071e05040513060b16020103090b0112020a08071d061f02061501050403031e0210112502010e0d051603 69
    0x80c0001004209580092404001d02040e280c0006140c103040100c106030081307440440c00f030284a0005c000d600d0450b0023003062240101b86444000408a0005010354404000b0078010b906000000034481da40d4800c4508040e000144141090100d81e03800b03450f0700000d0240410030144c095000c42203040c0588800b40300459458055880703280c4000d0101c28180000168501880c1480c00c0007100300c028100c0710f85512420304410802c1c80c5100580c02416440000792040040c0000072230034202c8201007121540c002c9414003103003999030305880c5e55541d05005011aa001008901e04002e042c22600d5070044401000308085055802c021221851f442c0806c40050780850180100903500c401c54448185081ca80b031460300d07081d910090450381e038111a01c1c00c000244650b0880403842400b42c030412500c00c00c401d01140d040c0c0080d5032071507000300201c01c800034446c40440ca6010310340c600804030b1581c181c603a004c6c010707150810407804a580d40d806440b075000c0c0d10940e004000841c00e29401a61 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 69709318 1250 69708068 69708103
    0x341a090c100806010c022209050f07030c0e09011e0e15060a0902300f0114010e010804030203220503010e01150302060703090305160e0919140709090f11010504120303050601050c 78
    0x14243c1420ad290994030700501d04241c10555040c0045604921410261807a54a41d0051600c4400d10f4900400031050b6007000c01c00b0140c41ca0240903003a401c4010360210600c1110b5a441070030402004a03d401d5449503403001c0c1186040240c010b0700d801a00c0c1040f403c1401c0c1941400c000300b02580c0e0a81c1d01d1342204082d01d202d04100d1081c0048034040e02402c0300d41040300405018400181c80401092034150502048c10009401c15100300210b5050360301019201d102840040100280c0c00e4090050610950030210b200c0e810640c140308002e2413100c014105607481c1d24507001c0c02a00ea01c030081c01d9042003044880803020410401c00303c0b55181c2c0c0c111801101510f42244038418440181c04603c45800000c15141400318025030050b600750090100b40c04812500c0c0d500c1e10b090581c0d4031402711a411b09880e4000d2000304204a108540210740b401c030f2440f503000044802d4400c500621080d10700d16140440482d1003a072203140c0c007000c181032203031030500400e00017854403811911008052 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 69710568 1250 69709318 69709331
    0x3040303030e0d140711120a030f1106060d020102070812030f150609100327060b0405131104021b0a050c0402341a090c100806010c0222 60
    0x340d414402c0d01040e00350000a407208018016005241c400d8012007200c0000001c076144007445600f0014200ca018003d110500e10b180070343c1d040c0e0b240e45041009901140418030400a00f0f80078007290b410b0f258000000d080c0c0c0d40d4510041055690507080141e0451107014400304010404100c1910303440d405440d074585070314060881e082d00500051020713501e06000480400281c40d0b02c4103031080c0307281c03c030f5040c101c80f0482d8500310002c24190000d6020345a117131400f0202c202070790a81010312030003880c0a000d40c00c04902407100340c0b18156810610060f03200d0b81c41000c20b0103940726614000000b440946481c254080450041015901c4c04084da0001c1014030700700042000400c00e0580300350f80075410701d242c101071113004420400c42d400c0b4024842d1207092103c0321312544450140c1d8004400b4001500303102115502d0a002c480b041e42c0f41c480c50a50f44180c0c40c0120402c41c07407020540c0c039800346998030001110300401c0007004030307000310100d003a65003202000b807030803400c1c05800c88000444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 69711818 1250 69710568 69710573
    0x3010e040510090b0103060203130b0109090507090b090106050a0909060b0d0b0d08091009030501051f06020703021509030c1008150a030b0604090f0602040f05010905010206090c010f020c0d05030403 87
    0x4082d50079841003501ca1070079560b400042c19211040b41103e03040300c801610b030782d11900c00d600210041d100081001c4044e00010078424103551007240340c035007d002218100e5071030b010400d049400500c44640d000d100100100400c92194000b031008110902c0d106549070f581d0704024040e01c0e40c94001404003040495088440c0c4000d00c900d00300050111001e42c1e1052054460280a1160441c5035020382c0c02910792407a40c40c041c0f441d42c001561710900030450343c5130401c031440f50240203e1000d541782c022000c0c00a43c507440003400109503030b0000e0645400e10114200c0088950101c154507406008841c1000a103070f8800c07280159841040d00c401d4050b00c1c0100300c1d400302620703100300b4a1160701605001c0c004102100034807039100006950003e42800ba40c1481201485000e074010056400060081542e9140102e20801c40c0c030280c035107150711501e440040e40c95010441c1c0466140e40300c03110700d0301d80e9071161741d00c034018070b50380d0058480035000c00020a0300000080710544890f44002001c008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 69713068 1250 69711818 69711823
    0xc030f03200102030f041e020d0c050301110a0e010503060a0b03100303020607050414090c0f070507060905091521070b030f010815010308030c0415020d030f0c020d0c0c0b03010e0405 80
    0x181008201c000314650314100d41900d0841801800217020407040281039940200f01812041c074503500200b41810303950441c9024058030b074140c003482d806035090146049880c00e100d01510314400c0c0c140c80742103840e0b09004c01100c490f04020702c490741c0002a50800600c140400f0021070240350380807000f02000c0d08604001e40b50541c05403000080100401081041042c280f40c2d6608800342203e074041c4035103c2e4400200d80e07000b28800a240070a000513004100b1100103101c41c100c50a0f900c030420305507950010003864980440d4841184c0303110300082e110a241254040b0101440c090050b0f202c1110088a245080c5440c5c2007220454000001c2c09180059035407101c0c01042c0c01001000340c0180f01d046010f80400601c002840c9d550b003c4040ba02d48148a010f9802a00076002082c100800f0502c0095440b00c0040d83d00020901d4a80802160940b502981e40820010b40017042e58807801d0320101d855054800c2c040d1180d0030100c3c800b094041e21000154000c0000c0c01c1e03502450300302801e0050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 69714318 1250 69713068 69713117
    0x30305030402121b270c0706050a050408030402040905011d01060501090b070c06050a110d03050a0f291302071202161d0a0b04060308040611030319090c030f03 70
    0x5481364490204880c802c01240002003480c50150703a020220401600550010304861850b8100b031010703042004081c20700140030340209030140000b4011340d00d075080d42000300da40983c3c0190258804100103005030030140c100c654640d01c20310000901d80817500e940750441180702d844158594540b10708000c40c2d039100490341c0c0034001c0240c4040c0ba18400303640d411745505451042e1000d01c10041844107407580205420202c01d035502090b1403030490003600080c001c28044400c06901c42c584119040682034500c640141039050303031202880700480c148030301000c180d50013009601030054803005104660f00d002814842c0d10a01d0002681e603807100000c1d04006070902c251441365412801048550102d04081022401c482c04003001d580715a00140c01030101000c501c2c2d08541044000410000c102c80200100c0d11150355400c1c1010703074100700b103031030788001e03a0070200d0340d1842080c903540040d19078081c40c640b510916107904a203941c0d40d02e01c0003640c002c84003580800c0315140b012aa82d4540f41100c2d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 69715568 1250 69714318 69714349
    0x709020903120f090f03070e0a0203010e0c0910030b04150b1b12030f270601080c040c0207180603120f0212030618060103150905040c060206010b0d180c030305030402 73
    0x241040d00920b081071142c021364032500e2080d03001000400c00c43c2c8017406490003820300301e0f8030007103940b900804401c041d40c400e128428880a0210001d102e62084200f56400d544c4010b06078000b036128030f001180038101c3c0c92079a40c0c3c000c0e6161981c2098070b0907001d140340240702243c040d54a514010402400c40c0c40c03085001901d81e003110b8240e084c03007000c040c116a071286180003110f17080d460304110201c1240045409040e119801c42d03200741c6000c000189030381241d40450407240ca2082a20034001911070042c01e402c00340c0d00220041c0711801d031003501c08807084a000c0c00040c01c1d6580e03407901030703141c102c40d002c180100c0c04e6a0b0b2109a0680e06018401d0421124039a9a20f14141500810341d01404140400e1595a00d8000700781503078400d4100c0415288440004060f254030340c05000700400c01600c04039230805003503c00140090000c95428100c65100d0115070400c0c5007901d040020704846070400f80404c10204094002920103190000954002e940780d13603ca2074148107026080e480ca5046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 69716818 1250 69715568 69715603
    0x30d03020901170403090b070f02090106050f04091d010912090501052502012d0801050a211106070609031d1e030106080a030503070f23090f030709020903 68
    0x80c9080b0307600039641c04010407510011403841d03036a5050403607a140d190f403c20840403500203480f2042c00848500b852280d4000c581040680e40e0320310381a182441752186003c80300b84180010000c010a075400310350300d81e8081c03000ca000846000d0341b490071a5102c92044800001d08503100500c507038400041c801500f420300704645840110b244820003980c4107800c1e4400c601940060f0411a40f0540c603400000c43c00e09119609400c20704442551040c600a90100141c0f080c0d000040d5171600b840c0050440b1800e04030b180f88808000800808500840815100030200c150f10000645a19000b4000c4500401e80015030a409113401090b407448420504143c07024009030410315502d403549680001d44031894030644800d948042809003103154030442d024000c00c3c40c00f000f41900f00c40258841d620300d03503900c02120f8080030142c80500c981d1240c00c03540000140741010504402004019003000101031441503a6044002480c1000d079070045580d080e00850340c421705041c20000d0400b9664034031302 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 69718068 1250 69716818 69716827
    0x2030423030d0b06070b01090608010c181a070b09070e0106020c010e040203100302030a0501090210020607020a030e0a030602030a090606080705010503060411040b070b060109050f090a15180902030d0302 89
    0x1190380c1d480c000e0010035a081903071044a00c8541e0b42c3d0004841d11164440c40102d5250380d00c1070008004c203101e00c1002c4155081c210801e008511690501c241c0800402000540e00c1c00c040b042c260000c00c8a134201e80c40a0b0401484001c5050903100034803074071030140102141070906d510309c4071401040c0c0c03010055604c0088011500e030707081100d0240c0c1d110240d50040e241e58610381d995000b00c80942c4069010700602d2002014820190491f10b8444c2c02940d040c1146188100100c1e62080c0c110384500050b005440c03580c0019102b541c1c1a00a0400208a0050b060303c0341c81e282d0407a4426035021403010f5480701c1c80d00400505004407c0101102405003d5a03898400082d00c0d40c031005000300e00c1503580f00440c642d0030103541d042d6000f4000390849980c890f40c2d240384c8000c14003030903540c0c64080340e40c030f0400080790301c0c3c1042c11000b03201000d0480c50541e140c0f00006c2010f086100151910161080e80201e0219601841103071003400410b030226503295140185810120b1ba0800c06081500400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 69719318 1250 69718068 69718133
    0x30c160f0b0c1005060307051302070620030a05060d02041803020d0306290708030c0703170c07060c02010e01110717030702030703050a0c0203030f0909102411030301060201020304 79
    0x2991441880340003e010030781c0d55034000002c1c100740e410303008030b54003103007d1007899890b004030340c0a010501c0c400c0c03a04000c0b000c5000381046035044020407032500c0d0b079020000a40d01010340e400940e0040f901a08500510f0011350005090b248114005142500014101018954100000400d0301c05506040082e1070604560341c01428203202c60045003400003040803050780c4040e0480306010b0b0003110b55a2070f0b040942c0810800c1d071000e00140e00049014803c0b0080e1001e01c5440341c00740207840640b628007800ca5580c80040d24003080d05174203556982c0400c444140023030050100e075134240e06080396510304a25000282c075000c049001ea82d90800e00c204000c190b0000304880c1c0c401e0b0103040007500c540407801d04507220100000d000350540004100c3d0030400f50f011001d02400c6804403104031107941c0e030002d8110f5042881c492620940404100d403200300c1c2801c444454158180d1800e0608110210040341c9035502c00c0e44150010b039800400c0106010480e045900601c040b8802c03007003c86100c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 69720568 1250 69719318 69719323
    0x603060114030a0602070507050a0609080a03030506040b031617011401060503060312040623090307090e0c040504050d030c08070c0201050d020c0d090915061b0203030c160f0b0c 78
    0x50241481d194810070701040345540030803805110690040d400c0d5030321201031805984a003401c2c0f1a290050082d802e0100741ca9018000440982d10703e14000d118121041c3c400302c01030038000c0c02840d0404c2d82c0e20107000f102c1e1002d01078180d030504202288540c15283c8002e035400301d528103881100c00d0f40f42c90180a0b8030000c806149044070041c0c03818031345944802e400a820300484c1c10161000a0b0009400034819400202000704104808500207000d0000d511b183e60a214040e00720b581604411000c1c0a90603050348031040783e00b03101c030803101d0b00180140071a003180c40588081d02c00b5030003a80501c448503811300810211800c04d02e0070509074245a50003820702c55442c000281800750125a2400d1150360760b041e684200b1001c002c079414402c8041000d4800c80c1b00d805182c2c2090b00f88a0120a01c46903046074404880d07481e6500382c41c0c1d1480e2131207070802e1880c0c5101281d0500040151070305001e0100072000c007600d1100542c030420b0b403806484800e1546145c2c840c0d1520030301440b40b140140e002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 69721818 1250 69720568 69720571
    0x60504020a08011a040b0f1e1b062404050a020c0d09051201090213090f0b1f06050412030e04020d2405180703020a020a140a0302100204050d02100207090219080609060306 75
    0x29884c0d079450301105c3c101c940c03110310004e25231100300f0380203e24103096607065441501e050401c40242c07500340c5c07150324130040c0c20640c58500c000f010300401d502c00c0380d42c106507002541c40307508070700c0060920b42c1002d40303182807a8112030315a000802e003100921040c40d15a1682c00049040b05c0200968840360340400c45020814040320b660a56170035040090103c0f240024110b25400002c101d83c1e440e0000c040c660210043c8680030386c6450012010071031500420845056491001840a4281841c2d40403124a24104149600507809010b004a207030705600464480d0002e110741000200c401d00300040500b0300c150701c2503215291001d0840644400041b60513001040c81c540540e546440300301c2071b803a00d10000380c020070741a0809030482c520380c800309900300114425800d40d0b4804190001c1a000d9001c1c0d400ba841d840340b4100144801494400c61503c0716510790b00607a01003e41d1820110226040803035164088449202e0501c1c200758003104a0b075120030101c07445041401d040c1d01003aa160310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 69723068 1250 69721818 69721837
    0x90b060607060609020d05012103020601050d14010501080106051002010504080304021c0b010603020d0f060806010e090f2505010c0b01050f03010902060d09120c03020a060f060504020a08011a040b 86
    0x300000d5200c18080141c0064014010069040d90740b0482d081c60b80005007000d1044003010004805c511091000341d5002e181c1080d0560300424060f401e020400c4160340800c01c01b00c80c840700700071114200389d030280660782c024400c000000030f0b5031340707014144907401d07044600c5d02046901d0201000009200c1c5000e0743c0e0015010780d200725500354111480c00c00c0560030b104c0a840c031004000000707525075254005110b400440401408034252645003e400c1e200c0e1402403580c19008080103000742400c4500c4d45034402c880324100d50707403005c146840900384148000321448215640360341b441103ca600e0000d000a140a18100342e0145194851a2500c00c041c0a058414111100c20780c0566600350803d01c01c007500204400c0e550641901910010225944122040024040403d40744c40c01080001181d42d0907030094214502e450b9034080040060f4001032882d00e684040c0400c05484520183c8509041c0d5100e2070100d5041102e0700010170040c1c00c032002480c038100300910800b2440f9041d6800c039074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 69724318 1250 69723068 69723079
    0xf030406090e07050705060a0c030e0114040602030903040f03110a0b0301050d120302040f0f090c020f0307032304030f150b010f050c0705090c040e0106020a020f0d02012c0a09090b06 80
    0x4940fa42c0480e280d100d4a000a4298401d900a00120000380c2d400959034545944040040c2c0c17075030341c0e1440e00b0303100200703002101c2100440001c0c02082d43e6400543d407185241041e2403600f529000c0d15a50b0305104e0700181c80031003420640002a041c032611001c05000090012350440d89010000ba561401e500801881038541c00200190180070f60180c4010305110125a0a0310b51201300c000803070400741c480e20001c00e00380408140c9450020036a17601206240f0081e45c87e020141e00c06070350066290741540b000700ea454448100e80030440e40900050362194850b511015440c1c10842080c5141c060492050f900c1d208115a482c0e8000c2c24214104100d81842034031a61010800c50801419521041d080781e00002008001100c0704020803d40c2d141400b2243c43d42d0700c45038101d9407841c10240007074004090380c00742c82d52841c01c0b82001940a105141040c422070841d5020759105c0c088590342440c45480601c0c00c40e2900c0c00241080c0541041c1d0010000020360751148942030f800907041c01e0041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 69725568 1250 69724318 69724321
    0x60206010801050c0928090501180f06050a06051b1002030411010e03070909111002011b031512060f09111005090310021b120a030b090630010f0c020f030406090e 71
    0x191214030f4007400420740d40800300410740c0c1d520ac1c040d0070452000940c0964601c1c2c840d03c1e141d80c6600c3e102c0c0c40141c4034041c1c001090141058015541a407001d6a13600c4940b0510904d142000820480150402e00b4040c0c05030300ca0629140418124820f41e07241030500c94041c0d0240039540b00000c0000c12107100001c080b03800096030400100d410184944590030036001d40c00103c14a03015003240c00e0008000c0a00d8200304600d00040b1f013203e80b001130034400503504035005c0100f80320b840680e00301d040c00341c1c00004220f14011500307401c031114814100c0d00900c4c481240340051a00210b801426469030500c0c1c2d1500c40e0f40e6000a03100c0c04565014041c80b94003155010003401400c010b083c496000340c049850205040307821b44070980240d508040002c3c20146440445d04180e00683d0180e0006081407054222131212420b41181041c2560810009a80f40c1f900100b0240501084092502c40006640c251840004c3c1420440c103079050165004200400c07005d94881d003c2c90444003031200f12580c0707 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 69726818 1250 69725568 69725629
    0xf02010806040e1b12070605040302010c0212010f0b0f180f1503070b0c0c12030a0309081e0702120a0b16090e01030302030a0e0a0b090904020a030c060206010801050c09 74
    0x10080700340b420b843c42c0b10300903407280d0b052501d003040c040c800021501e08071241d548450761039070b0301100d000c4c3c0f1700024820f01003000103500504010750010310040034030103240382001001d4215500320b0101c52041c0e8546568a019003080d03030b0380340400a0309490310706070608003210b0000b0080029146000803103229000416074081c10a42410740d110007429501003d5981c12651016003041d21f001c4998041c01c5100c1429241501100d0000020040958206070105000390000c00301340009841181042041658840896510000100da0b550800d51201c030300d401804500b02401000c4d22103584007192803004100081c003103a61141d00c2d90a4500c80c401e26a404a450f00380c198405005526214004010160080040d0002c58002c0d0b50301102e006c0984100714860b2480c4c452148151f40800c85c050180c20300080b29a445030001c0c24222103103030b8903030300d80f136107900c5540c015030040e003001d401032180c00f000f070040d541c00581081c165814010300200141064802078041030890010000101c80d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 69728068 1250 69726818 69726821
    0xe0a081803031c060905070e0d03021015080f03070206040e0a0906090804031b051e01030207051006031707020906060703030e010903031b030203040c0b0304080d1a0109080a0f0201080604 82
    0x803a030318094140ea849010300c2d100740070080000b501d81d4800500f000703c0410707080c0c01d600ca12132086000da514221001070b0041448104006800150110b02540301d42c0c078140a860700a01009882c80101100c08500e08003100d400c01c080c01c0f00d06080c642081201d100580c0ea6001900c007a24030840c03c274405600e500240e2340041480c84c0000388401d051105200c18404aa806041120302a14403041c81da4403810342075071350208e10300070990f00c80e07802e4002c107126488990640c0071521040c14010314000064590b00c0c030340041d1581c402c5980b0340b15103091040100c50010780d4101140e0700c480d035007828034543c0000c20440c0003d110602030b0501085603000c1c50b1280c0c01c10041d82c0c0c000c2c8003c004000722410b00070701412100b003001e00c4089000c10400da8041c0719100300d901c115040f0603030602850502c442000c80b03500c080c00c10344d25814140948070170703502544111240210b81000300510300d8035000002d85070484ca44d00119654004641010200e40440107010000e40e09203800c1c001da6552000140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 69729318 1250 69728068 69728107
    0x3050c0712030504030b060d0308040305090a081002031e160503130609050c0a120203071e0308040b0a021002090f090c0d020a05030a0b09071709010906050c0310090e0a08 75
    0x10480c1d000e1510000b41038001d001071083c0c03400f807403219910b40c0d119001d1124018211600034001030100e170014011031f1140016000c1c58000034084481c00c2e07078683c0310906e044c08081000a090398008180f151070300b83c12008c2c2010a00d0340d0b0f0001004d14180c0c40300c1d006802c0e200312440500c00000006100700d0103074068190407e03440f5404202003441800c1541e45d4020000c0c02303a0142c0303490740300450050113000841c520f096009005017003503824034608044081c0c0c2078056180759100742001100280182000d4000303440c400351200c0d1075680345403000385400c2121040c40350051042140107000c2d20b460805410050051781c0d40c0300c0c5a10b41480b10042e0344140a044210b0034070200d805c00e0440d920000560240040b001c051040040c920b081104084041c0d62010100d4041c1d010062690b001c6842641c2c8800a5800001c11070785988034082695806c03204040842000030811640100c504000310190030310480070001c401042050b540c0d600d400d06d1010b0326001000c50003080010f000040389 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 69730568 1250 69729318 69729329
    0x904020403030203070201030605031902060c0a140f0127060203100b0a05040306141515070b010e09060708010b0a0509030a08120103021302090d060209060705010e0c030f06010509010303050c07 85
    0x21962541c1d203080c000e48903007100104a001a041450001312440c00040010061032080004248091035500b00000c6074855a44c3d803049014024040003c101c01c14074403144c50108c0d5001d444130325009182542181c80c51003003450584200a88000300e0b11102140c1407050358060340069036600c0f140c0c540d40083c1d6040c5d11120400000040341000b140d4080090000c4070300c6200240f180c00c034084c0e00341000d810110307501d1003c130142010094040c0b8007001e980305000300448010307207089000e071903890081d0400d820824030480c1310f806124490404000066100c0041d20302078071103504002c8003202500c522444401080400700e40344410740c0d0203000503c1115070295030940c0c2c4000c1c82c800c99200250921003a40310310084c00c00d410320300c1e40a00132180740c0b800013040c107416120036a035020001e400c00aa003c2d0422000e200080024070700344940d404c4544144004e1607018660000c151910804282c416483e4100c9001004076807915007403541540e5040c10b100780c80d00124001240781c03c4903035004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 69731818 1250 69730568 69730571
    0x30b09011e08301309020a1403041203050c0c030318070602030708160809030f010e011505221e0504050c090c09120c0406063c03050c0904 61
    0x8128041045918400d1070303414100140c1951012116103c0c518503040c0715041401c041c0c0125061409040b03403001c145405481424620714100711100740750f854210f80c0245600148171581560004128a012099224400c4c0f652619982e0250b0440d04c440c1010141034940d004107142c410600140e44207088403030101d03511b03854410380c02103c0ca054000103600d01e0040000100b20380f840031048410705030f0807009507071070000110704403500154000d03c00e4130441e10901c2080c03100d55040c003040c00d85a01c002e0002c50800450341c41e5600f140c44440c0510510b605082d0104160346602820b550303003120548000311a2101c2c82d102d64054440110268010300034400c14440002aa42c01940100d020310200c80304540401d0a0010201d03040c0e8140038000c130144900728244c9840c0100b8038500e0000000d0b1001c81d100e080c0803030150703043d5030000030110750011032065510304000503890240d50a1540144c1c82c5134400017418800c07400d681580308143e119400100d8035042c50049940d5030802800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 69733068 1250 69731818 69731821
    0x60609130518100b1806030303010303050d0605060c0a020a0605031b1b06010611070806100b09010e0307140103051f12060920040c02120301170a0c0e040507080a080904020703030b09 80
    0x183c49008140414034079105801a8020303281d01da40185089100c0c280c0500112724590858500b651140c000404140c03c41c3e444541c08174950700c6480241080c040c0380801030050852520401911091640140c010070605004204038070713030500f0418006800c03401405654052140e0f40b07071000c002c2d44400c2192803180000008405030703c030240254420046c0155201aa212401f0702e80302c1c0d03c10350300d201108039046020700502e04500000c103110141414820307003500c0c0c00f501003401d1080a6102802890004411051a581501486503c541e0352401d405d1a40b411244c03400500313481e40110760720543d41d80715500c200025607000c503c0a0f0f13040348403954045040e00c01e0800062001605502403402e10705651a41400000e0607680794040310400d03800e50f03003400c0c1080c81a502c601c203010101c0c03041c94010320103d406e000326507000d00155220300740305181a0a041340340100591201d80b455005040311030204059000f96568614211005a942c0d91301f406c04802400d420b43d00b250340454140d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 69734318 1250 69733068 69733093
    0x50c1017041a01080a0807030e0f030d02010614010c02100e010c06020304080405011b210909020d090c08060106050406081905090a020301050702010e100f180804030b060609130518 79
    0x458030407050b01010782c01a45030781c94041050303d840000c0802800c0b4481070029000090203440c00564200000c0c2007201403040490002c2d1500b034501c1004c0015035940c40c400c0c40303964603007814242c142da000c0c280300403d940954081100c52480c4e508500400c448900c5804450384140c007074a14203a04041c056450f8101810134407595030091103018042281491001c42e10102c40e0400d103403041c1c01800c03403100303070b4144416447c005031158021002c00600502c046502e04851001c7c045000c0c4c0c10303030b0010b604491450081030f5506c141c1c000e41c40d10b6102c180100000d6500c90308660903241e031880c0010700c3ea140c00d07040c1010103070f0082844a6503403c08003048080200007404040c2280200c0080c00291541d0704281d08844141c2250a8140c111894058501601c0d402c81031034038034019030006015912162034400c004920008072040580060100203106504d1040c0b03030420003c0f45c456103440711450008140c7c12003001400039440d03c40000030000e202c0ca1102c0070240f032584060380c50300840d46 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 69735568 1250 69734318 69734333
    0x506010806010614030402010c140316140102041a070f12050d0f020f04090b0f0d03080108060718030f170301090902180601020a1e0c030b0a0c0c050c101704 69
    0x2401000c00c14031440c0e0000840b0b40c4109458041d076401e01c054545191074640044550318503a450a440000805120131701c0e9a00410007488201c4c10744480d800c0e881407515145c0705001c1204120840d17680144018080d5800c015001036060074407415040d0303510305619140c45a00c2004070085e0460540c20308140417250003000a00a10301c64090401524080048c41e104a000f18001025856401e02003803002142a5004900139a4000e01080030106d00c203001910880d60010110002501e82004001c4404100045134110301681005402c0740412903c1ca03820102030310001d000c0341d200841d41020b00403014485603461071940411070f41ca41e1940c1c940301c050503204804070301480300071a070542811039a600303035800f440e070580c0506200f61194881010301d02c9010200381c0d0702881200008000780b80c2c00700c0d0600551040240c61003501c1c0c9968030f0002c40b0fa1a10080b000d002c40902d03001d000420104108000c4141240c408910304031142c021514000c4400401840c5840c1c1002d000900c04c40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 69736818 1250 69735568 69735571
    0xf0405120f0c0d0306080601050123030108030a080a0b010e06070201120c0e0f0d020307090905100f150e092d010e030702030708030a08062e030608010c230315030a0506 74
    0x1038000700d511810f46802c048046810360303c91110704c0c0d00001c0c01401258824010156084070258004465089018541806074000c0c0d200214590002803030040c1250071480460307001c19270842c100541020100083c1c0f0207606012401c0c0300e140c00180050841e802488004c02509200030104410440100c000c8c2c070b0350040d0342440744601e40040ba203801c2c600d043e41245e40307080d90240280c400c180c580391011002d0f0241c80c40032556806654100c0100003868424409480441d80020400c203210280882c0f20105070b07000804000491410403685c1d00c80000c4554454040012280200607039040304050601010041000340d4203000038003e4110000014052150084050720403181e91100220303624461854104041011140040c04c2441c044c204030100b580050040000f40080d10003c0310802c05444000340460f984600c10700c0740301710902c206410024181041503501440303c03098105002590360f0340240c00720000c002020392440900c030451880000c1e02300c9240b0300a625040340c48110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 69738068 1250 69736818 69736837
    0x609140c01020f2407050f030403030c030b06190c0201180b0409060b041211010201020d020a081e270f030c0618060114100e0a09020403030e030102120f0405120f 71
    0x10700c000c03400240d8000f0a80158903514611140c0d01405285004c40001c00010419020310806014068006141340b00941c4514030a96000664421040d0b000e022904103214050248409014400304100c1c0c040e003120b20320503141003003110035040c0c1c40120348070304403134207030f50804d0040d0000010207107003c002a0041d00c0e0048014010291182c240e5a074074040da01caa00605031410200d800411404800c03000010010720000d40342c601c0001d0b44071f081e030340409082da0000e48100100038841480c4424803100e20503c0042130032a041480c41c4400c0381e0b15602c5046a008110144030742c00e141c041125508880250081e00e0304d5211146225445c1c2c4012141418601100c44242e15000008200345058820031718040891a000d441440400c80220000c0018040b081c031400d15113540d86c104040050007644409641c2c1c6055140062a00c940d122045000c1d82c0140682e81c1e400305462071455000246802c02035080c0e0f80c6081882c079088001780444801040050070742020303000000103060090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 69739318 1250 69738068 69738073
    0x150e070602010e0309030601060c05030c070b03090d02011406010315030b01080a0c1406040315020d0f0e070b030c04140102031209010903110c09010e09120f0d14010f0b070609140c0102 81
    0x29080019130701e0b480b881c0b51103a4540c000030014050b003400348100b100c40e18021021a420301045407480d500d00038075900280c80d5400b001c81040108101080705528074015440280404182a0820041010054401c07418141c6442d0940203048200046000440e00110015029651003c0c21500e07615035800c151071804031420045103480005600001c0d0b4038015200520309481d40d12119901c8065426014080b9020040110f445016024903031000e000201c00040403c0e103004e101d4030f010138903071011300e42c0c100900c200440030545800395402c9034160200751540a882000413070848c811001c00406003c5110180001c9901c15445040e22034402e89500344204101014196624036003070305280c0c01526440180003220122903240c0c7c02ca80810102c500c003c001003192403080e0080031203001a03800200308405240d0941c01203500c3c401c2a070955420a5040c003943c2c0110460502601a00f4440000c0003800c000160b03001caa03181d0b40100701c02481c01c881e0301e50662140100706803d401131 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 69740568 1250 69739318 69739331
    0x20906090906010b0904061d390a0504030c060306050f0a050603040609020f06040e0f0105060406020d0c0201210b1002031602010813020307150906020c060d09150e07060201 76
    0x50800d020260700031010003005103110382c130380000440f05078040d1413500d800c0350316004005100c124404441100c8000c00010310118a800c0000c8521031410064080281d01d0001c2130002c000c0308040c0c1d0040344e10100140070782c0c2e400c01c400191124891603100421aa42d600710000d202d65255001d00c05940302207805140300b580790410862181242d01401d80c3c8540c0410101c0c00280442c2d208030704031840035192a84c440ca28000242031a04664810400b0311400c4c810445c4c103c0038041c1003405000d04685840c181030400800035541c940311840041800510385210055a00a8150031000304400c800102c6d008280c00303441c006042100e0b665401001a00b0803414502d00100984058031940c0d020b40045012a4004480700d01015011400c40c00c0c9454403440540c405020450180802910a24018180120080100ba45a03210008540040031007031f0103070340c0d000100c403c0b240071305c43d011410340040e0400364113410b000d010305101310385496040e04094101080c044121017031034000304180c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 69741818 1250 69740568 69740581
    0x602030403150219050c0106080f100e06090304030b0901021c140708010b220e070201090506090303040210031a12061504020f03013303150504090c0e060102030706060e040209 77
    0x3607010300781c84ca0a90f09000030004255501c12009090310005400000c1251542c0e0420a8100345020070841c003030b0340149060406152603030040e4840080b90710001d04c0c4030310b41030125540364000c501000744858001e1001c2003c5050940507910304081e541002c02800c12540302e041c0050484860241c45101040c0001c1e491038010b1040d14129100c2c20711403850010242070501c1d80c140c205d00041124050302c040031610488000c2031070b104840ca90000a0150020f04185140240090074010240e004004220060315151030180b03401c6d22a04020800e480c012107400b007528022904181c0003180030242943c4210009800c50241c50901328aa070090783c0c4109000507480b422284c145024410401005144000000f20141c803150180303030300c49500044800b0026400103910040041d032507180186408451844040040a04039030810540c02c2603681c80b601c5415600c511300110f030143c0c0014840707900900407520016408a420400d164480b41100011041642e09902841c1e00c000041c80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 69743068 1250 69741818 69741821
    0x1c02030310230411040902030a06050a08120d02030406060b0319150b270d0503120f0702060402040e070515030906061206010e250804030f0915050306041104060203040315 75
    0x1501c69041150005441040c05200113400b0029400a078941c04010000e9640f515101442c05204c0015010940c0c51502d01001720300c107a160000052a005032801c41900010f080c1141d20003003043c200903072aa81e41d401c00d6030007810b00f0303807011007051800001c002c2007111081081c030561744c001c00c0820442d501c840190442045a00520310030101c20010a410715416540444108000814045042c29180e020404664015108642c254008500c031043d850030084d0070760b444064014000200d250008009580f0728003d00060b008990341c1140384820b10050000c0c0c4040c00024003a10f400c6000c2d440044496801200c41c1480c50143c1c2000c150649001000c032002d8a42880c01001c559080200c03801c2075030005056051242c0000c05100e0035203150042c0060640080d80320480c040c9000d090140000d505c1c4401001048400c0701c06002d10150310900c02c01c441c80350b04c2c110b5103907074800010600900c4d00402000c40c001010400242c42d907400801001078901c100242c2c00c00038454250700e030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 69744318 1250 69743068 69743099
    0x306010906060c0b1915031101020a020a030605040c05120a0308060a030c260703080306130e060a020f0f07060506030706050a05030c030405010f1406011103040807050d0201021c02030310 82
    0x40020384a0841c520118480e010030a41080e010814112842c501c413445d04111120030740040013038007a1900401c00d00603620f100290001c000e0001d421000540e03030015014080c2e90100030300295940c00810705000034903115001501004e0560155420701c5100f0f5581c80390005403c0303001600c0100050014244001c440e400c403540402c02c0c250031070400704002010030440c00042d881100326012481d02d00d00030841c0b07800650250340709036035278189101882150104c0c0d08501c150b25040c03000d101080c1d240000d10551044041100588440c000481c080c601c1c42a44070f500d0f00410007280e040180203079548494041c8004074110380440d0790f0385000ba602406001d00d201b0100d071080c00050b022020010046900c140700380000120001b08440c02400c4420411a00d110607002008004907541c001b00d1403070710b03042004021070800f407404074080d60750b07034541c054240901d81d048450411a4020400482c2c2c03038043d08220704106e20704c844003c2d500d070003c0b030f2a042d48008803500013400401816490 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 69745568 1250 69744318 69744329
    0x1507030507230c100219030207050c010f1b030c060b03010c0f03020a020a020d0516061d0103090c030b0a0606110304240306080d03090b060901030b0f1f08061801020405010813060207080a0302090306010906 90
    0x40131200c1d907410040d41ca40d04142d00120900048000642d1000c00141453b000c042c400d0b100d02907001c0c218144001110300c1062154020380c5054848081c0d141c1001c041c400c200d00728030300545d440445090032810080f485000a4002d1400e24030801000004120130070811900b00900419503602c0f40300320f0b0341d1010920100c84e01c481c211a40c50345944260080b030b090324000e40b06003a65513540d07951a002d41c20102c6882444540d640424000c19a001741200407a02550008609003401c00e00b641a54002600d106609060031240c00c050040c000d07007251004082c1281502c030300300c404c10ba02a01400300c103103003200d0391000c0d0f81c0040e426191510340c040c180c2e504407500d100340d03543e0f84951083790030000e0120510f02607190084500c45298012a101030302039600905960705203001c40b0074039000002d04440ca80d900500040c03015907030203001160f1000d040c0e260030741501080d0405400034841c1c00300140c0348020001c0c3c004d1440f901a0000c103282c500560442e00b6036a0b898a40348126440e50250 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 69746818 1250 69745568 69745573
    0x20c100504030222180302030a0306050f03150a1503051f0603080306060d090c0807050f040204030803062205010e0f0a050f070c0c0906081507030507230c10021903020705 75
    0xc0d00c4095009000222100c043c080005410108040c803090b000a00040c2240148e00000e50001d0741c03681401540c00034101900c14000303142804000035207039451141030041110414000900702a00c54104980202c0c0104c100c1c12000e403203040154940c40c0200515602d4421080344580121007840b81c001129080340c0000d00f541c0340c890030004a80d001c0c400041c04241c0b03071101000800e01941201006140c0c1c1d00003448018500418010100303990502c040c801d070302c10f2204002184403001100c0e4080c0c0b00315030307594481081c0119a9458803a030303d80c0191485c9071030000719461414403c05402107a041e528030302d41e0b988002c4c082050b80c60880350740d03a02c4aa80c4001c551700c1400b842021040e213100300c0310030340409c1d162044042181c080e640301c070089034802d5083e0715201c000f403003c040c0c1060b5a40740c20300c018a08040c0150408400079034502e60202c044103455082d4903210b068500c0c404403981a540c0c408056510300e0060f4010318955036440b059000840314090180c403c80e002e1542c000301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 69748068 1250 69746818 69746839
    0x703020f0303060a14010c0212060114030a0c14060d060e0a0e0c030c040b06090d0c26070509180102031303091e0909080702030a15050f150415050301020406020c1005040302 76
    0x200204502c5100181404070784c447e10401a5225a004047c104641f4000c0c11a5031518841c000144d000c40c031018000e800c45040c40001c5070314100c1c10015941000c6c05408040040300c08074826100e290000da04092030f00402092800394003590741e0080603c010144160342d010204541c070350560008c1d02303500d540300d00c081e810542050313004072282c01e5008244505022444000c00c102c4100c84508580c1c03140d503689d00340000d041e00f560301a20070741540c8a9a06a901d035448a41c1d5030101d40c0a010b03c2466500000740c007004c1c0801401031008482d000075900c0b410240d0120040100240e403c0780802d0444070003184017111620750780118216040c1c2422158130f03100b513020080bc0741050036114104100f04000250710100580c03d400d51146074034200b000c6180060600700e480280401d940c5c03146950500a20746e4010001c960b1840085030700081b0070b65004a0301c0301c604603641c0310580550010900103200c58010596480c611426910160301c1c2d003031400122094890350000a601075107800c0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 69749318 1250 69748068 69748079
    0xb0f0108031912021c0513020a170a140c01020c03060903040e06030106080a030f1202070f060f0609060b090102011a0d1202120711031903140702031c050703020f0303060a 75
    0x8500790b519158149107900d80b0b03200c03050000340d074400303050141c41c10500a044800c03200e5510130307039134480890b410303d08400e1f00690020b10913200c0c82c4560f811407941075007010640d0700140301e088511313584800030b500d002d20802103807502c441041c22204d000d4020b0011003c01c6060102d00380b480b07022042c01440c40c0c9410460f20860100c0064000358140d0359075840030450341c42c1040764510550003500c4111181400003402403484140304000c840c100d005000f0320300000d0102d00300d24403095014002240c0c1643d151000780080007540d000389141390034243d000030394214400060000c0b03e82030b4003d2180f510350368044580e85459030001500140c038040c0c10f00100e4080300c4900210b442d07601c1501c190803c1c03410003044035000b000c0305942111202c642a0321502d03040040030040303c501170300c400d100c580740c0c0c8010341051070b0030401010300407001424408641e810300c40b0038031b0452a041c0244d442c030901a0004c020b500450340c100d001d48150003408180903000400d491061314000d18001c02c2c40c0c1800c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 69750568 1250 69749318 69749347
    0x4020a09090f02030703031e0201060e04020607030c0209070503090c030604020a050613080601060e0111010504022d040603080901030b0108010b07080706020909240a0b040b0c1507020a0b0f010803 86
    0x740d815502d0003250b100c1d40b801641c0c144003400045000f5942e601c2080306070001d0102d19241c80400d20290ba141280800c0200ca0448145074860b804407066030f1505c2140c10240c5a850381c401c00258449860400c1040041e00000510300400b8880112100a40c2040900d80e84001c1510080e42c040316600701000249003610007000c00100c440000c1960751b41d1030041e1807800703c081e088240450f9040064500c0340d6032001c007000c19039044d100280068105a00480d1680300703a071480550300542104402001204c4886403d42101301402c100201a640d05011301541c2202c2081800281000701900244d88a034002e64143c03150344062501e42002c5541e01d81041d884103c080350b00c0d68081c41079803816501d614079140700b600c81142c0c480519500ca08406c86091040d28540e20071242d1241c14052101c3c100c00765030980e00384d101c040741d076044903500c05454100413014524007e5010030402140d964041400c115030343c820515034090761101210a94801d500340a48400e55109021000700140030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 69751818 1250 69750568 69750581
    0x1e0a02070501271502070b07030f02040f03050105040c08030304150504020a05041802030d0f050d0207020d0605040f0c12030509040b15030901021308010507140c010b0910140904020a09 81
    0xd4000003d800024142407603004509030705140b070052041c2846018007450a00e051107011028504501c0e00c3c1c25079803440303905500645010101030b52440c800c00700c60b885604a8010301506803420b15202c0e603d1030704c98080c040448044507a030000300340005814000000396400dc6900c070340025203600601100500034540240140d03030080e011741c000615901c41e072140c0c2032031075001d12400408001500502d40703000800c000b203070201314504010700704203540300059903003007400c44402595a410741d000150342d005c45080701803c981e00e0101840100546d0801c40303d0303100d00c00e50b000b02e600da980d0f42d14a41c3c4100300d08030203004102c00300f04c50540c926181c0c0c00010241001004400c0800300c1034a405000d0300200d03002071860b035000500710903a001030188a00101030400080c46a494418402404072000c03000704440e9076408102c3c00c00f250002e40001d00910400f8040d46994648140503100086403840769800e440d0540407198105d04003810134501c210380103412218042c0c0380c43d0043e80140070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 69753068 1250 69751818 69751823
    0xc030c03030207020907030504050c0910060c050a0501020c06040201140301050901030201030f200a0e03010b0a030b0907170c040b011b020609030a15020309061015030507050405040c020f061e0a0207 87
    0x10b0800c49603006941d11602640508030726940020a49090310f041c0740b40601c1000c03401e21415411040000c2c00d10b40000b0310f0240d94007454621f0302410180b40a924011501c04002e00d99400881c164454080001701180f05038004d0340e03104045d041381405281684020b029031500840c0c031000610241d40203811003110700c1c540b00400602c9661510a030968251090b0303108101c54800651365910035400190000031440440003089400b40e0113001401a19003480000c040b0790361540018000035041c8896002000310300c06150b000070680c0c41158a03985d50380284c62081e0314022044038503510900f4200000c480800c82503031818000d40800500e6017090034910752601c203201d90701c00000c812403200e00c0304c0c90b05400c0150704ca003010401e460a0a100506040310340005100800c080b213002c141c2080111814240050303940c0ba042811140c0744203503004240c200d820441218116640000c45d410505581030644a2031b071504c01c000401d045d480b0240c4500180100e02051004039264020940c852 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 69754318 1250 69753068 69753071
    0x8010b041a040b030403020106050a050a050319020f0306070806040c0e01051b0705041103060405010911070b0601180602031c0209030d03050901020d0e07090f02031e061908010606031107030c030c0303 88
    0x1a075a083c286041d50040310101c0c010b0351105410071160604107201c0000d845c1c1200da1121160500e80800d80c0c070a4050250074501b07181004001c00d54445d958211800f032405402e41d02c9070725201801425400c42aa0054061498041041010392141d000c10000320743c140c3d207240ca07000403030361003a00c00c07141100080d0306030007032190002e405c4d980c9219008002c880c2c040030756164540401000f0455030305910030501103003000c1300c7c40051203c0078101e40e000d5034040b2000c03c90381c4820004843e0059180c00c030040c50742000c4404aa81a00040941708241d121150b19102c985d003c0c40b1359050307002c0e2180a80d0554410100b201c0494066080540d00c008500c00060400480d00c003250140c821707002003c5000d0300100c00920698800b8000c2688030707581e070340c41940b07107081c10305c0444400d03518000400c10f00140f09000c203a00740c2d10075400d012441a100c2c682c10000f619014900e00030b161920512011914008007840c6104440003511901c1d90142c0750f80c0d03511262603e0588449040c0c200c21000c15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 69755568 1250 69754318 69754327
    0x3030e01051009060b04030201080117030d060905042a06030e03091309020102060f01030c150203160b15010207050303030f060307030807050a0303050703090b070e0d0501020d09020f0108010b041a 86
    0x12502446041e1203032035080c50358a12545080740100440b020341c0c000c0c40245c14104001c0c000341c0d03040350b031980c1190703074031032003100c0d030300b6030459100e066024070810341310401c0c00c1890000392412190450b82c0983e0284a600d00040e906502824054842c02205281d5103000c3c007007081058026403040300038134030318000d603486c100390240020340260900405411690342d8800200540d6810041141e00140307881a0840c1d0b941161100384c4038040910900ca0000e0b00352040b40c400a109005813244408a0040080100c81c14645002d00010071685611480c46e4806200d4803584002348603011924081c02451450300c62401e281c01c1080000c1c609038152080c540004000f83c400002814080d0051024191000040c90001e00380c80014100e1800c15083c010300070040790920b0b14194005400e82030500b040d40c4008080303401814191005000355102140c11107401402d43c1111503058821a582c0603030b58035640056415000a0241541c4c0c1c020602003403205050a45048000398003100c070081c02c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 69756818 1250 69755568 69755591
    0x80402040b2403040b0106140d09080f0a0c1101020a0206030a050402041d0607020d030204140907034107080417070b070e030709020f090d11150c0c0409020d02010c0303 74
    0x1607034482e0480c0a40460020811090001c17201d0700f07034050240c1d482d14050b11403805031003084a00172030728404101a0340f0580c900800ca00300d02140c207007400200d985600c40c1e8100d40301400d08000c107042610842407190341c0380c549600c00702c0c482c0f6059900501241c116102c80d01d43d1002040c00900c201e8209544108610801c03a1810030f00e00c85800c20402800c2a00c0c04020080c2881b01e01e211003403e0500501040c40b42c1460850140d11a140070b462007222030b500c441084020303002240301514201c2c0005d0703180b60141e60021180801204c40b02201d0300c03145520f003a1404040c002c840c0c04000880c000b020800084130307582c802107046901292181402d0b00780d2a0300300000410707100300010540c204d015844608081c40910000c2c07011681c21400c0c4030b51080311308914820740030b0311b0340300d204114203400402000b00ca218a40002c054850742d600030072801e44034070369802480c1c140000d1080720b41c144520321305070080071880b035070260054614140c1035006407206180035000300c0505480d120b01e14030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 69758068 1250 69756818 69756859
    0x6040f11042106180c0504050c0a0513050402040b04090612080f070309081204090e0d050f09031e0d120506130b1206091b01090e07050a14040b09040e010c080402040b 73
    0x2068144d200e05060a4020362801041c0301005a0003c0e001c0c0382480304021040235400c060310440714142c10b0003176603030402520100341d806840e004281d00038400f040111b21a910030020304140c6841d20305c1003040030b4030b84600a82941e4240c10007040001b00b04200d0018500c041c003d401560f200e4100170220680b0340600c1424070207000b013821030030400401c042000d480d5500441e60340b41020380203442c0700c10036032100515901c650b511030321440100041344640f68400704444034417611903826500900501c1d8182079101e844849142001498151004074030800a00c5040d014070001010200f080750013481e043c0107170402c96805640030241034800c00c1c001d002404064407840103c400307441001542189510f1603180911414100880f98005128500d0082403c0c0e030010f155007801c5480705500a0110343c5850140c1d40740686210214001909a00c1d80f0040c00b00c1c10070440d410b0120710001c818160881c0c0c1415032210005403c2400315002d410290b004115150b405400302c0c0303281d0082d060000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 69759318 1250 69758068 69758081
    0x2090613030b0a0c0509010212090a120b0a0c020303070e012604110102061302090103020f0303040f08031315020a03030c0e03070f140402040302150d02130b0306040f11042106 77
    0x442c0d4400010800000104520030300c0c40741402800e01d14200380f02000002d42d603170004520340303c0e02e28000072000007030f035078000031b44000b460b6810208507019002e10b000c101c6c901054400900040c02c040d003400c002030000c404c0d0b030f01c62180c940e50721754200f2510b40119040c0140c05075400304030012040031480c981a41405a00c01c90051030a143c0080120780020b107845001440340442c10003c000c4c00c0010303614a00c0c04c070304407501141d00012506000002a0441c40f49601c403450b581201c2e540001c0b2039030b0200142452808550750015a2961659084018460010791400503048055480c0003e8040d5002da46c2c0c00302e08d85849030040107050301080c50148581c102c00007079000c0070300c10058099003843c681507101064400307504013480c50f40071542143c0107002e0141d8405011034038100c01c0c625075043e907940aa180070f696000c25922850f4a0071740c1e1056800a000390b0511401684444050007050064000284030b10720b0030340381904010500d0100351042c24001c2490b44003a0100d0b45074001c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 69760568 1250 69759318 69759323
    0x40f15020705011b0b0910021c0509030301050109030602160203030a0320070503040e15030a03030b030f07080303060f030705130605010816020a030305042907120506130209061303 79
    0x200450608000080d10700012544035904000c0110703800c82518942d002482d80ba2640031a05026913280c4c003407000e060220202408070081c0c80426404082103036a901000ca022117030004000c44d45a0403049500ca02c4240151808100406400c00010b40c05a00070032011440304040310a002950b400a810340c3d0201080000080d240c0107000410f07081c4950500f84210556030961418030140c1d84d0f25180d000324071a64a10801c06c2c1d00150b110014a26103950420005083e5014400c003450090020800b0701105030080c8641086507000708030000b405815607070198019420340e9100c1c002c002e02045045411501b5000780302000460391550300420445061155012804a0409000400e0528001e16540804e0000038410750301680109100b10f04680514010600e95564204003480146240950580840c1c10241c00c161807180c240705405196983d0740d8a000d0411450a80305503041614903039403115440d0007801c01c00307901c0d50043c203d04a021f000c50b8103086d02e100311004600301c2036000b03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 69761818 1250 69760568 69760589
    0xa08061c08030a0605030f0a020603100e0f040b0f04050703020f0f09010f0504111201090c17090f010c0f0801050f010c0c090b04060518040f020a0803070326010303050d11040f 77
    0xf804070b10b504a0140e800904000c0d8014004684506001030750740300c8021000c6c0c000c05001022891409510400001414024200003040d06108034176080e041011030307050320302d011000b010494170001100c00d1402190000c0c01000518156000c000685c1d0505c00010350214004010900a88074a0101ca00920100c0d100c07400b82450700050105540300c004849685800421101720700120903000d050550f404502e00240340c4070721030001d88a00c030040c1582d0925200d10700c00c002139403200007485015411070300001e01660000130f209452207202e402c425000f01d0386200c018002400c000c4848281c0d1407051500d90b2a01d546c58880c007a45011070b03002500b07401d80300c0c3c02200c0c080c01c09001f140000c00c0195101c001e864001150a09142409440282100d2001140e82c0a40d92500d00080103800e902069994078a41454040d00f001294040c01c0041b03111b10061a401108000321305040f6500760303c415140a0002180c18010b10540c907208003188014040030a80f8481c00d020034001c1d0030204c12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 69763068 1250 69761818 69761821
    0x40e0a0609020a05090f04060b0105040513020a0e0604050a03080705010f0c270f060e0414090309010905060414060a181202041515050703020703052b030504080a08061c0803 76
    0x6001e0f00034584e40029000d51090024000140030800001e1350003500400001140421500121213a00c40c0c2e0b0301859009940205007040c010040e03000f00600c0c01035445105c100100002441200c0c080d80c400e4580c44040301c10200041080300c001440f400303108070000a07040c88514562403c03901000f50400001e42c0005214101014202d1031042d40c6488440c1d07500612300d000f51203185610140030f020100050400c00c1c44954980f07400c40744c0d581100840044c042d01d0461442540d1f500700304c1035140000c0c1281c038002400d0800703404036016103c0b000c1e0355a114444110902410358004102e40301042510303d00307012a04031101d44c00c40602038100300103019141c13030300400c800c3c0c96507440302d800c02030002ca600304602441d8a862101c407864604110313860f0b13103903401d040c2e003042c506a0010b032450040301e0400124980030916441190341710080544030b41800c402c110b040311001c0300c004100d000108040c800380c0b4022042e4075405400140b100c1d0100c2c04e86010a103014408003011980c0000200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 69764318 1250 69763068 69763073
    0x60d090c0f15021203090d0309080d0c110c0402120f0c070c0b03040b0a1514060408010e0601030311190f02060403061b0305091906020a02070803040803040302040b180f06040e0a0609 80
    0x41300510843c1d103041158114100f01b03000301c1d2952130441d600010716541d100e4003400c00001000f80d800c03046400300c1c00c0000794a0440050300684512074030164502507030380004e08034500b510a0314010714048499401e10303130f250f00c00c40300554405041200d07640403c3c0202d8000403103080125000c0d144c5030440503220700341460030400c4040c0107000c2c2000c95080040040281590701c0c00c48007107400048410400343c0400020030f030144540d4118584075401c0c80142c044030840002d0150480c1c0c030a03130f107031040703100800b0100707440c0c0c649036001c0d00c00223035035440100c00300302c018250078050340c00100701501c0e05540741da0300d0040303d0042c820020182801c196011b200f640610580781e001c1940005090b040400800c041c0101e01001e000410707542e030100f55413081d90300c20060030010784a81c1085903aa580c448011542c4ca030071a100480c170440c10b045188120381402c8041c490131800003580020182c8540c1c00c848803040c2c0080116400903550600c0c0d140c1c0620401003100f402e801090002864103550 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 69765568 1250 69764318 69764323
    0xb1e0705120d0f0506180c0d150806060d0b1501050f07050d170601020706120f0603030203030901060f05010906030b01030b060f04081002030103050c09091203010b0a030e0c060d090c0f1502 83
    0xc1c9114220501d490104041e940769a1034803014001d106c000880555640030781e4046c00d00034a40c410000502e4000319580c018065806001a680b2a004132601956140f00304088400100c1008081034130007070200d041c818000d062002946014144240ac048401900003616081440159000c1d07202c9900f482d9520740124010401c0b280e003100780111032802e500040d544003045d1007640100a02c0c0d07501d400c6c130f05110b1360180f00100140c141c280072195507401d000b51ba80c1c20945451145500c4c0c45000a030351200310343e81d00c2c11039406858030f00203e4a001d406400402c113903110103040c9922099015400e40d104e0300105130b85c980344601aa01c860424070020314210081c00242d000320710410051022a0001808110b4040e0860307002c2c0d01d81d600c60883c2c80c00c00c0c0d00051445c00c42c030310100010030300820420192410081958003048110000c0030001d5503644010400c68200008010040b4806110341000811318020085402e80c039644914412103803d03145d00c80380b03140046400c98801c2c164103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 69766818 1250 69765568 69765581
    0x30204091a0711121b0d030c02060f040201020a11030f01060b0a0908030913020310180207060c0c1a07111006081606080a050411180703050702070b1e0705120d 70
    0x4a01e000d400800d03e4450040c0d5800070010041d60420300450807012201800d83e0701c1010a0350720054500c8050f0485014001c0c0c071941142c08050700440300083c189a000e07546403403040360141c1c020480244523494375528620040025a00b50203030108003800c0718803d000e808002e219020a8540d01c100340c0340b00406488045d007101c0c1d076903003041080103095940d961062029405000005a0b2034440c103c80000c1c40d081540711304c1d00f1040041a850a96400b90701518a080c0154001c5c000404481400c455008109800500040c100e0310460740d2001500b0340c1d20340c0030001e41403a40c050f88107051014a05080b80894a03852a2074500c00d114181041c084041c00d84801d01032091654140b03000500a00d4008200710340955071a0001400e02003084000c03811a01d000e8075208003103014421160002000b2181400407078244008109240e10000700c600c11104001171603402c2110700700c0d092150308000719180100b0403080c421400818010303c0a41042180286059034601c516980030054515 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 69768068 1250 69766818 69766831
    0x41b060c05070e06010903050a0305031504090b0720071403100513030c06060f0902030402040507050c0c04150f08030d0501080109020f0103050717150405090109020d0b0907030204091a 81
    0x2500346800c00092030006890003075800b904800c0342540e903010700483d902c0040742d002901ea482039030340d100c0c149504800254010300c44c06000306050301070f034401c0c082980c001480040c542c405250024010a12410b00c81d0400401341032109104070320b080c009442c102c0e50b0b420145000707060b050001d0040c6402c00200da079404e0104000d100b80e2500403141d000b026a143c5018050190b842e841d03904200c000d42c02140a44842a030206030385483d0051080250411202203000c6c514010202d100c090144040d40e000480700001004001c0600040c44041c029014180b0703800b885440012491880c23506504000d0440340c4021620380211290f01010b48106a00c41e000c80d91400c889a00540c40d05819036018100a0802040139240c0402c01ca40d400140c10a01007804905001e104943d46042c00361040320004403400d0000780c480780042c508075001d105000358841d400345189000904076490b800d6010001c4016100e0300e6541390049030030b5809605046460a0071905450684c14007030759003640000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 69769318 1250 69768068 69768077
    0x1403010b091003080310030c0e01090b1f050f040e07030b100e03060103060c1106240114040311130c0e040c0507022409060c10050c03040f030c110405041b06 69
    0x180003100d0b080030516404050442480000080c4c22044000f202c1002168840000c40750a03a44460000d0601401e008042c02030b42031400310891858881c6140c9003140c500d46601c0d040105210301035406078490840ca1500e014140030009040b4801082948280d00580700801c03180040c108101d15000700c5c83d00c050901c941582d4030b409070b442c00180303541900c2c2d00034400200040d40210943c0c0e521551810802184950030400001003c0018181003c00300b005100c1d88141d002c60054491401d001090f5903803040c140000c102040221043c54040d035005088a03d544181a00724000ea42665a00307002040c41d90f01031070f0040c149071040c4408007001d85003050409541c1c0d40011540014000c0342d055002010140c00440313a501e00449180c080010011503859000b000600d8840e5810f02c481c0b84518640400211040d45604c02c8901c0b17554071508a0042071000e0f641903854500c00030054407a11000004404c175510b0718810240a01c0c06407201d0240304800245c0e5841c84500d80c1c1180d0f0400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 69770568 1250 69769318 69769321
    0xc0405060307120b0711010504030f030606090503030d0906020405100c050705040506091611100e010e1903051e0c030d0b010f0e0d0206090406030b100504020703050715090503041403010b09 83
    0x1c01c490f15804201c0d6012504040c3c41d01c54010880e000c440380b41440b10b5035441c103018002090b403c01800c2c407480350591800c0c0702e5507560721b0040d03458002920460f42c041d0010408003100c50240e60013020201d1107558010708258807800840c1680c07104a034100302003481c1c0442001030000410542c001458201c90070701c140c0c076222011852410026003001440051300b031040c3c0350f81e0302900c113400383d40c80020200c809548840381c40c0c0002d400174020700c0c9483d51a100302e00810038000b1071006148040351440484110031644c0071101640500e042041091990401c07110300a0400010194056082c000710b840b041035140120031105006001814403c0a00c0103d03c0c441d04171010b8a1400f800b210380000340800340c004110548240c50820381d020b8905100030080019501130035005c0c0c0a88000c0407103c41d1220140001c0340b0030300c003018020036011701030320300010101c0b41c0e009011050380b01c0105202085d40d403040c4c515007250b00301170007035200c0d94003981d40d03402c0074428440300000031180c1d50b20a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 69771818 1250 69770568 69770579
    0x801020301121506080f030711030f060c0a030f1812021f0e151f0f0608150f040623010e0f040902030f030310060801050d050601060e0d020904050c0405060307 70
    0xb105421008041e44000c0450301d81021090780320310010f0030264156121190b0b2406c24907181c1c0d00c00401140e80d071324500c8405049080008191071400c02c9a402442551079024520080c0d803c5030300e810081540741c0300402181b0300315024a1804a540003449445d038085450140000780c1180c03103070801c41d4009402c40c2419018100d011001c171459100028181140603601402d200029480c1c0c0d00710b695541c140311440c0070311401590820703071a0007d0b08905440e070144181100399486800c000600d0480850403510f4087d602001c03413107004184c0704040c0d2150340410306070303901c55114415010042e010400e0515085050000980c02441d1402400d00504002100c0c5110b8848490040f9a03a403829000c41d00c0030000004a0f01000c000c998591070203819a007201420750056000041007070b0300006d0786080030441d000c16554800060402a030070064101c6030001424140d0b680800c0303810107100582c640310407043c083c40c0150081c107054850401030200b80c50002d000e040c001c1d071050104001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 69773068 1250 69771818 69771839
    0xb0a08070e01050903070f0f0806070c0b060a0e07080415060503070b03040501090807110307050609090f06060d2a0c02030a03120908030711010b010801051020030f0307090801020301 80
    0x90048850410040d901c01e4580100e4590152256054040c400d03a5004140c1d81070310601141110074201c03100717a205441d0314a042c0c1b01c3e0800d81354040452456515100015040d0300c28130743c440c0000d0b15143d049952806000040320b401c2da43d0602142040013408144602c0e24140360714000651424800a480c220100355210794a100300000e0140120100301044820b400c0750700042d8200c1c03407150b102c81250130455640000190080c0c406c0c86044400245428200155003450200030705050255030b07405400103030102c0c000c14150744a4401c1003c823488a98034070641100c04500907030052087c05140a034990000000c54200c2130015640110006a50008400b0215603061804441d0200510050406048040e400600b40d28003c010003c02c039a1003941c0b822004000c400034010800e005006450f9180280a06034004810301144a0361900644106803911040f005a44801442841a5043d50046201032900031400800c0c0144690f001e6021400b400c207900085155504d490a04036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 69774318 1250 69773068 69773071
    0x801060807060c05031207050a0320030604050702010609020d02040503012f0d02131403060a09050304060e0d0204050f0f010801060b120a020d050405010c1b05100203090307060e15010b0a08 83
    0x1c00010f1004001040024410f851200002c401800180d040c6102c02034040d800252403000024031b04840c00a00c081b008618100102c5000b0203141307540c03103000c04d10000d000e0040800081d592601c6001440c0381440c8000c0040c90b240c404010703252400d0004140c00d5034031045010b07502061020b4543d80030b107510068080240c01c581001c90f520645148520064041c60a651410f034444c00b50014103007507200f500c0020702e81c0c205c0903a455a910031032a0340456407141c034042e10350ba00900007404841d014078648822564000c2000940748015400142512811101140351440709070600840c0300010441e00c2c007510000d8002e0006508060a600403800f60fa5000d03044c0043c810040b0703012003200c2e4101d600000311500103102c2e0303241c03500300180030740305445100c1f002504005201c00003803160b041901d82c259200e0302130b00c48982d104504c08081e40008e4400304042c0000c109a10000300b03548920028074011002512950031110500009010164400890600c040103620303146507002c1d0106 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 69775568 1250 69774318 69774329
    0x903030c03042907140304030c030806040b0603010801090605060d08090d020619020610120809100e060a0f02060703060e0f04050f0f0703020a0501030209361e010801060807 76
    0x20360312640c2d503060182c0c58410500300d9040c0b080708203600c1c001c0c10624280e07961041c0d41c00c0d10740705c504c480f8101c402c04440c802210b0150005160090520000f44a103964a0704001c0091002ca005240d0b40c0015819510a0707200c1d0909a541d80301640400103035014070780d84000708451911000d080303034903221694402e00c10010321a400b0320b00f41004640d210f2041e104609800021880050b60b2070705c1c06555000f040c1c410100511020b040064141ca030b80d0422028542d001900c1800d244404080c040080c0013030301000140110101e034941191600000340a142c00c09550700305000c031a501c00170303040c00341c003810315401c140c1060f606103e0124105000c64101c94207032500201903845003826420000700102240f0303240107440c6040d031003000015520040e01e000301c40001555507504010b4007207102d40e5400603000841585048400403d09841402017008145040e1117102110901d291886040341c80381c0c1940145500702c1058240f1002c15800f502240d0001c02449042c031030095501d8005102d074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 69776818 1250 69775568 69775591
    0x9010c0803091c080405070f06120f020c0a03080f062d0111011a01081608060d0602130906030311121e0408060c1209010c0e0d05010b0d0303060914090303 68
    0x101d101032204210380c060f0500e8140e0886045505080000d24024003a5000c0d10140f00e40c160104440070003d040744100c900703584031044510102c6542d44050724006c0d030100ca44c00e40c280064800b0140038401c08240c54402da59480e01458020b0301c1000512016000e0b0f030040304006008220319400640e00e60f0202d190b040c4100755946020b00407101c585028040c4840307542083c408129914100c008901940b401742c0759480180d4414031002c1d41c0010703804c20030000840200100e030841c10b02207008107400d8020702e805854082301130762050002036681d00030f80c080d0b0307030b103250400500d9072104d0b00111040c040400360004440440c0411040d000310940b4600d440c000c074859000032141001264000c000c4803068400515000660f020950820140102e5040801c000070f00c0c4100c040c882d141c070b00380c1c06455031081d400c004030520540e40400701c02215290342e50f8254190356030703401100003420307486950702003001d50030203480e13906072598484280c1c0391544a0050010300d03c000720580380c0c00522140c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 69778068 1250 69776818 69776821
    0x8010902030d03020f0702120102190e0906041e1e0f0213060503060d1502040e0708090d12020f030a05061c02010804140c09010e311202010e01061206060b09010c0803 73
    0xa0707100c070b81d00c46d0b084000c3d0310065034102401e5041d0190043c1c40241c1500f43d101e61030100040301603078103910701c583e0310768441d40002c0003030428503240d03000d103098904200c1c0380c2015803221300707030007003107407100a00c1180d031440d00e80c00e40746c03c0512405489070a0200100940c00c01440344840804580e1b1405140184940480007a00c980c6a0a80310180c0790b07003004605e828002011111802540280141c200100340c403000644070030301480c103450141d20000c008000040b0b20402c2101e24649600084102540800c03c201880d03030a2005140074007050100000d060030120200840700310300002d10900d9950304411600542e8011035003580c0704d6004800c0e0103050100c501214105980b105140da4081c00c44000440d080020064062140500f84411224602010813018075180c0144001a4903a44103500e180000c4480c1c1a0140004c0e00340008544600704010990135140c1e581c0085501000f03e4150390140080d0b40604001440c0700ca181701d1416013010002810230725010005401e000d0f0000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 69779318 1250 69778068 69778087
    0x305060a050604020f0403080d0627020a1808010b0a0602070f0e04020a0f0e0403080606030c07081c060b0d1407020303010510050c031c0c021b01110109020613030b0108010902030d0302 81
    0x4040f1000381075a4105070346e84585914120300c50760843d9401c2140a85007900110301116090b4807030300b03654500340c0a10b284940300c8520001030b40c0000001c0c070802800a00f00c0c5490500540003501070140c0303000100e605103e6805002404c42c15900caa030445d80311000c00c000224103026440140c4661600e21651036445001180004049a0003418000450340300040c0d14104030b50a14011486551445250b88814041003034a000a441004003080d0401034540060b000724000c000c2c078445050280709102030b08501c0021200c256214441c046000129901c15902921480100114081004640341090340000750b0f603010501505004080d00501141800c0c040c009503025425004101c969406014071501d5072482d008512101281c10064401d0050303001080045500301d4805120010401a43c0111022101c028000800b5540c90342d080b005031715410300030504501c01c1c48a0907401c6285d40740001d04848168060340050b4076150310345c070060780e0105100c1c91004c51440c01603110240c1d41c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 69780568 1250 69779318 69779321
    0x10309080408120301050102071e0e130f03021e03120103020904030c05120702040605060a1710030203010504051e0a08070807080d0207050c010f0302070c0e0c1b030909100305060a050604 82
    0xd410a4540b4443d0161050080c01c086005606a03a030a07403d4030132043d0b0300d613441711022038030410f0b0703910201400005001c0a40c5112b00c0b1075004917450000c1510801540380c001c908800944281c0058100d82d100c001d03410000c65040512922103c000c1d854242d41c0d401c0105035030010301000344a80702850105e0241449a1164407130700d90082c0946602255004e00c180d07440e030003140124003903418450300049920709031050381c54190752904c508081c0103101544c0c00124800404403681c2c241181800300160b1801d1203203501c158850801044d100203040c50344060070b4801821400c0b5580300e5084800028041402d0714a0700d1313804205180c98400d646010540c601a40d100c14624a1020841c6824080700181901c1821b10a81f40c1d520f807601d000c80c088050b445a01009414400401401c00c1851050281c20398401204e08070941442504084401000380d10449807480382d01c0451100352616040c81c1c240e400000c1d9400b813402ca64a0b59071403d494100041ca214140b540c2c40001480700c0d03c0d40d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 69781818 1250 69780568 69780577
    0x50a09080c0601030309050625031e030f050906040201090303110c0d150507031521020a06050c0d090608041e02060c01090c090203070c020d1a0a0605010210050408040501030908 78
    0x420681c5600303454507581e980c0d003001d12080d000100b0303a85001425040c4203080b2400e15000c8028070303010b03880071005141c0c450720f0304004404204000c21040040350f2003007130109450101d507501042c0d48000800110aa400152040381540c005074180801070ba001022042207a506040681061058103445800c103800024025082140c241c08402082491001040b001441410800a82c0c030f0b60501241100e066510840040d482500c0510003490b41c10814207418500d5444100925400e501044003a00e80d64030003008120049a0600e10a03c10b12008880351420b1505140b26403502d100200107400c040e00c0030b05120b40c040c1d4050140c2010150310190b05401914aa548452186602c1d000b003038090010780e030080446c41c0120383c05c111070084038041e0861350b640d95901800e6400700b040000810b202103800d644038603400b0740341a0b4203000b80c6201b20a1250002030b0140b8200002e403d0018400b20004290728110410002805044c20345065500030301c0c0c000703412032840c50b1044a40c0f04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 69783068 1250 69781818 69781823
    0x509071404030c0303030e0d0e150c0307050712050712020102030f030405010b0306090c100305061f02101a01080a02090108040b0c0f030907050a0f0803030f0a0b12070509010512060604050a09 84
    0x403c00200600d60142c11880c2582140400c840400031151001c0325111030100287d584501c180ca0f1072400d001c84c3c1c00103010710240740000e89107045140c0e550036103040340b2076004424900e03211446409108090080400502000d8020b102030089640000d4491044201910440b2400f1000c502400400d50040c2030000e8080d0488980b401e1800407242d6581c500701d001c42c41181c5030b01b50302c1141031003400b40d00e004100151000313100616510100150f008600840000c5119088800b0349030400d03801404002d86d000061007040c2c8130142d000500e2210020311800050b40100300501441e648103019551064002041150740d49580c0001100c41c803800310114050400071042c0108920040f659208070743c01140c011400c1035440ca440e8101000c10310600e9159081480003c0408031880d000540c0554800800142c0d071041e4400504030210507142034140e6400068144038600305601e02a0140000305c4000c0740e014080491143c2e1102e000b0035541c06140c0b200c2c0890007500c01900729a10456 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 69784175 1107 69783068 69783083
    0x1d060a080f1504300f0503010e13050c0402071103150c34030513090e030d090c0302040504050d02010c0c02010801050405040c0302060414010e0406050907140403 71
    0x802e0090060b43c3c60881c0301c121408108109201c464100c0081c40c6005507840503880061600c11086030740c4040c000c0400050081d181c04214030f590042c0008140c1c02d513a0390034a0f00d5410000ea0a80d02074104c1d00200d203c808102002600c45000e0105500301d0b0b20314800d2040038040048180c03413640040c01d007002004121000000b403602401a0b10200c1404143c41c180f40500c075800c101003e4000032404910500b501d00418152030003044074480c148010111016090344038442c0c82488281181e5484500c0c00304042c45e600d040040d034005000300214a400d0408584441d0304003c113500651070074000041349401203e0300b00400d501130391044410307070901d000d00008000c098003d50380109203140000050b5901d80041000d8948102d06511084940001422070b00256510b50300c61420054140540e0300d5070004503034071201c1d034a004c030000180c4014014291141d900043c00c3e04 = true := by decide +kernel

theorem cover : BRFrame.Cov 69604318 69784175 := by
  have h0 := BRFrame.cov_init 69604318
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69604318 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 69604318 ≤ n) (h2 : n < 69784175) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
