-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0334
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:16:29.773986+00:00
-- url     : https://prove2.me/submissions/2096cfe2-e41b-4d6b-b56b-4ab9d4c6087c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 59892089 ≤ n < 60071945 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 59893339 1250 59892089 59892101
    0x9051002071a0709050a06051305120c030a20010507050c01030209011103070b100501030b010203040b181804050111030708130c1203090f050616030e011202180102063106 75
    0x4602c0e09031418100304500418000311801114051504d1241c0050070511a0003250181c81015140342612420002040710201150003c0c0ca074a200b5918500c0880d5014000000198407500d04000c071081c440410020200b0a0844141441018041c40001c0395010555024060007440c0040e5283e40c80e030010f0300c2c0004108505485888082044020400c4404050b07002e10180031032909607582c1d034001102030355596604240180c000344420440c0340302c000042e101854006020700141503250000c55601201c420621401000b81c10030702040c06020300c08e51001e0120300000700c1c074500c1d103521301400203c4040c02541080310700c0c180c80e00600c40003552003c0a01481c45000d0750540090074028001d0380c060241c14181c0c02801800078040c0b500c070301122000a0b00da6031056107500141c405558a4a0300003610b414028107d146041940040c8010000b08600c44500760401081c0340c002482d05000a0440400f016030b9600b0381e20314460040b201d80910710340e07103900386003600c0792619001500c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 59894589 1250 59893339 59893373
    0x806040f1415070f0806090702030406081509040305040e10030305090906010207030b071710050102070b0307020111040b04090c110c0d0204020d050a1b090e0105010507030c0203061609090905100207 87
    0x340100034071210940c0989406211011517603100f12980300c803c1000b0704c5100a98250380564800c000030003429001d010600d500075444016580342d40304540108019038021078080340003810025052054201c04c17602560403112410345640441d041d650040c00034807894000320300c234000845c0003039116071082042d82c0245500c00348078065410074090151904550745400c62003684494001903040b902d4128440031900140d004040d16480c19542c241141c0c0301070034110031552a504100220305100c00240010200241d440e6a12847c1401031000c03649200d02400800c8680c00c010200d411000400f540c031160111010140900240b0024001703110b4025040d40c09030804040004044030b80d441209905400700e00000f1121000030115071161090060013500c841c10b000501440d441003000e070401c01d10a0905150300c06064001034980072080720681501940300e0184032240743d000c418100203114000c1c050150342e182c0d0380c580b80c55910b6039101031801580401c0c210140180240549a41d103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 59895839 1250 59894589 59894623
    0x50306130807150b0a09020909040b0907031a01030308090a052104120602040e0c0c0d0f11030d0f0608031204080703050702100203070201031103061c03050c01020d150806040f14 78
    0x681048043c0301a050b1940e08030b201d030941d01c4000845d2030043c02120444500200316410969960707403112603181c0d01500401d1a8499041c01000159440780c00c0c4203200010309619004d9895480d0081801100500c3c0440135000740c41b000c000100c00269414943e200244003290311980c40e020304646000765880140d080d41417180c403506200303259008100341c802f1441c0d40101940d03200070180309c61040b181140e0792548488800f0410707a1041b0400720242c012881c003582c1583c02a4440c82c9550000041c810069644004096121b075151040c5002000c21001a50a0940020702100e112030b0041001d41400000500241018411011140c0580e4010a416011042c0460003950b0b5000007404902091600304442d1000705000240c0f0f20510000f0414090b000c44c0d806c480c403104a0700c0d84101c040c03020a001c0322503020028009484403400ea840001920201d40301e1601211209501108950b0803080a0001044003a80c150300083c2e0465080000255100c000520304200945400e0f158 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 59897089 1250 59895839 59895863
    0x12020d0318060314010b0a0c1709060d0f060501020c01021e07030c0b030a0b040203040b16030b06180906040908041e0503030409020307030f05010501020d0c0809091302030f07050306130807 83
    0x143d8040e4041604600b031224102503e80c0c0b01d0568070722600c01c1e54004408100307000c1038040015030356240d225418903494051070070207112002084050b041080c1c024050b6440340c01a5a2100681c440d090041400f48020030140000e00e00103500e480b40d10003803401482c4c01c50903407a40d80034100b0031100110340c002000908103917200142403da80042c0c3d00c10b44954101003050200d4074050003502d0003070303070800742403805502c4030380b5110307600d07404080e0450505440f582280810341d03c020140a0328407c0200c034250603141c0b0010040c0980004120350b10803850035405602081d07404d000c2d03e00b540c855000c240b0f41540b40544000c4c40b0403181c0c0c00310390700d8800010040341200c80c3e500990301541d003d844c144410341d041c224050030b548003401944e005902519002104500c03c10700303580e03528001c442c200d1402894001046040c007040360051030406d005c105c801c2c21410b04110000e41c0e442c11f0341c0904003040c1408006500da030000392080c5c11130150307030310088240080b5104507181320780d0100f020011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 59898339 1250 59897089 59897099
    0x206040801060305070605031005040509100f1e1407080c0409060b04090b01110a1205041e0602160609030f0212060a050402150f030a050c070c0803120a0612020d0318 73
    0xb802540c04219024001c0d00e400003a85400b0f4002da902800b111140c0240042c03c201c03c2c4801414000d00c6144103101da0201135480401d039218030101080e152070046140c50140340f021f2000d0700a850a091858900741840c0001141588130381d4000c800c2d85030010003500c808011140d107008942050450710b00d80900011580c444000500403203070900820700c1040c8a003001524185010281c1c400d054000c42207100008240035401140d040d140d09110341003075120042480442d010030031503815480f6925003400704d144c040106424469203240c8555101d030816400078616682e910004100e048100d10700011035581054420110b4040401c50742a0b183c8030200101401050385d041e4000c100190f407550302041c90508550040e9800b581092847c2c442502800c000d06001307000070b085d07020500c101d50001c3c0700400c0d20001032500c00002c50f158440011240d50b12a80940343d9850a881c00004200c2d0300c0300c191a0403c020b0301145c1c100c0c0c40005605041d15801400da1690000030005240458 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 59899589 1250 59898339 59898341
    0x603011d0105010302010806090603032d161703060a030b0402031207120807030e0c060309011512110a1a03060316120b090706020c060708130603021c050c03060d020d0206040801 78
    0x41213074001da880c040b04da260700c4144142c0c04015194190140c208200f0010300e402e103a9402c0707618078402c0c0080d0071034243e0340c00e2050a82d0811110807415a84103148001807040c000d6a940003d410034100e5459402e0800c0006d00306102d80c40f00134412016640061b00b59039041c4400c50750010b1189140741e5840c41c03468005e5082c0308085503140861500710104200c00e110340b0400d00240c14140007440b1086422042040c00c2c1c0000748516245d6496150b4440007003030300900200101041c4c00c800341c01042d14504084090700106c00c0901844142c034003009401480050524803511035102c4664075190080442d04210956681c44000904224005105404104a0300d031103402004d003900c00d6110401030b83d0300c8806038422100142e100c81003060700c0d844c041c4004c002192040c04003520303040c000c040c06400030b42150f02c02000300350b020600ca071701145103001e07245a0345c2541c5000c001030700d40340245541d540009820036015003200e01480e011900c3d041d803460103040d001010b450320b031590b6824140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 59900839 1250 59899589 59899591
    0x4030804090b130b06340317150102030d110c06040b0117030702150a0c050105070e010306080d080703020904111812160902070c050418030801120c0e0603011d0105 72
    0xc0d01861111103c010308041030300c502030400200504040c07801d2000c0c002034510038900700b400540300980d00c42c141e50150204080c070b21030500ca0380302d120312002d07401c0d080001d40710000c01003010315004201108403030303034040b0071039408c000c0900002503580d88000d5411070902842c030409502e8030a0400340018032480c01c402c00d0488030f10700c481034002c5410898642d201e01078050001e411041c0540b61004ca0400b80700238101444080c07030b01410128060b240c90342901d80603140e18000ca81417098a81c200c3d64076000c1c0d00050500d0300c0040500d50701c00f070402841c00c0c0c0c00030004010140d0203c3d0383c940c2c590302c1b07400c1480705981c0700200d140c03100d162106244030982203520f140d210306540e0f01c10301021a00070481141084a40c0ca48410903850040c212001e50301a445c211074810407660046140c0c1e0707035031040341240d013000010403080c034180b0324000d041b02e407042c5c002c2c03c1c003008421400400180f4001e20070050302c1034030244113a40c1d110321002c80d015000381c0212640b400c004002100740560158029 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 59902089 1250 59900839 59900861
    0x302070812070215030406150e010303020601050108010e1b04050a060306051e0a090519091410150603020f0706020301030f0b0a090f02040209370506040f15050403080409 75
    0x154400114510500c0407510078110025044900d0541c50004401c02c600a580d2260040c0300104840064180e14480318a40b03800074032010b500000180301b4182d04220290140c5000e00b010307409541440082c680380b0b600180800d440442c1d010340325000c40e21801c140d9008180181150800c40d4440350040d02131300450286500404600c203000300c0c82c51205951031601d0101902c000455428606000c003d484001c007402d12181001200240d10348042c410030305842e000d00f202071200d10000b01420b09040044031444a881c1c2040c01c41c0244a500a0502c1c00701d030308604006913134803030020024400e4010250082c01c020b202000010501c000900e4070143c0e588109408082651034011400c200c4030403840240050359111640001800e256000308110030300207242d608814980c0901d14060b046a040e0340010003440300c84003c1000341d071000d800150004503103450030a410601500b104c1c05103480741ca25003c1c2c01400700343c0070500800c00c5402950f048003995944984030785a00015180e00f03201c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 59903339 1250 59902089 59902093
    0xb12070906090b0307060c02010c030507021509090708060306010b07030c05060709050112020c06010b07060b120c010e01020109080306090c040b0d2703091806050d0507050f03070f09050703021603020708 89
    0x90310f0058500420594180d82d03460f00c5214080d112600110303100c1d01035a4040b01441020414200035135a005110082182d01ca2000303680c0d40c480409000c0c030408007622110a0054540a0111580e07001c41d48605441b07144040b56103581741c40c20b003264441c0e020080a020741c0140400c0c0903c6035070040800e000e650007a01d0381c1c604401d0f0503d05004030311403008041010b40121005000900148009101690040c2c1002c10548800000200003c16020526034550300c0305000500da56000803019034201801d0000704584085929140302e03038030004242038401c032103207000103003a008801c0544d009044420042616150a10002c1d4001c1242812080a1841003502e68100f5013028007966111039240d5aa484028a01119420640d2061002c103802c0c54941d00c01007110380b109800c1d8420315015200a042c05441d1030140180d00140c4140d940c000d40011506103c24011200d003030382244c402c4040003941c1e41d29018214001d000350108184590120300b030190900d98001240ca003a5190101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 59904589 1250 59903339 59903351
    0x130f0e070e04031e1e020601180b011707030603050616120606020307060c1112031b07020303191803080304061a010c020906030a08040b070b060f0a090b1207090609 72
    0x40e4008608208880040000d01c0a152100c0c1c00c142103280e01580c44002d0808200c0d01007815070749048040e00462a0380107920107c01085000c400e2030079a40a0728420900f0000c40c4014400204540d817043c0e5084c41140c41c0c4408280ca483c441c0d40000e0040d90481d00707440150a10b644143c10802441390200c0014044841c4050120b040d889054100c0e5925001180f138040c55560300350182441074140c0303050100300c3d45011120103052002d030ba8503003021003500340da92070103046222020030620b01c030841500c0140440801624000100c4950341da0b5030651103103000d04ca0f00c046030b501c81d41c1c142c1807800421001d030000820644501440c099846080c0911241040134440443c0c400b4006a0720b0000b001c10801101500304080c55680041014064500341c042c1074440803610b40c8298070890b00010001503000500ca803c205054101004448109407100c800d40090b00c8282c003409a261825517031040200e00d41e407004800d2041180310001e55520039130f1107000074000c10540c410082000c2c2005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 59905839 1250 59904589 59904599
    0x8091c0c030516060e0d0201140307020a060f0c0c14010906020a0e09070305070801060c1a010803040e130b180a0611180f030a0303020f040902040f050a0e040b0c0306130f0e07 77
    0xb250f41826500650f4404030030145007000c04c4140e25020009078140b01c1d00e101d540c031000800000031485420030360014a9060120318209003101c0c82c03031002031f118500c0c1902c002011580142401c01c81c640001034198884140141d65005000103000203061620000301c014043e84c0108050017801ca0458445031540d40e000c1c400d81c140e070800c803031070300003d406800140310980c051081407000c1d6000c4c6c00e4414035810000302d6030f1200b40080c1c11081a65002080030000034551181d4603a00c031003c45011341d200182651011891074000c1c20210400d0b02c0095940501c0400300702440c08030f604600240891114018039031550784c41461308503852102c0c2901d5401604200a6074201180050020004003403141c07000c038000c0d004140308800101d01000700240000d200d0018001424400e282d15644034035080c10410b00003000e52115144e0301c0c81800304408a403a4110103680030040d229625901e50755200020000300f5680070310040305103400040d003002c0060b5840056562307145021600c02c01e40391 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 59907089 1250 59905839 59905873
    0x10302040f0903080720060c0706200313020111031209010c090509150103090807060c02060a0501120f0302070b040806040c050d051e0c0a03060516051608091c0c0305 73
    0x4942c082e0100c0e40550101e101148541110020062440c81440c50010004101418070b507045c0c850440c80d103008902c0c0300903c00c07144034003520b500e00440076010075020b500030300003540002020300789a09001c2140e0340659004000c405255010b40082d282c0c1c0d80c402d110a00701110f802c2e00d040d80c0b903620300710098840502460381d0400b918001004000c140d035031a81c8420041c3d4010450b641015103410081001410f80000307008690722486011039051180e4800034504040100b000c0324160900c030040100400c84c20440d0000354114044100b030080707034101a0300d043c14603807100d1903c4100041c00141e8080c00b02d4441e010303d1090f116220b00d02e6840b010411000c00740d508c00f40040e0411401000c840e002c2ca559840320f03400c0f880988850841490000e9034042030b9600964045c3d440c2d504000200034806170380100d070f4001d4100b403410310042c03101503084400c000500038111000018054640c2c0c1c1c81022014074602d1114440000280c245403403c58a00c4920003150703640b00d01e807003041030341640b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 59908339 1250 59907089 59907101
    0x5010201050c0d02130b0f0d14060907030c1817010e010b060909040606090f0509010b010206010e0115030e0f03041503060503030d111204050c0f01170a0b2205010302040f 75
    0x201c01001da0400c580718401c50b00944c00405c00048030800c080d030020b802d00340000546400901070034801d84501000100c0e10076904e0782105050002c0b010303000c021065856a2040d6001100340c0f0700050020030540381911407100a180380382c1401c030080b030009810003d6a0f252a81c902521000b480341007480c48001c0e003038900d010403480d804a4184505c032070030f00346550b107540d00902450001c00c0384d940d03c03450740f001c450401036540c01c600c1c0c03a24100002d207034003400307450703400e10f000e20040a2961604001c110f00d800180622010600544952001036202c3e401c4286248030207410b64009030100341109603240e01c2403240c009180c0070350800d001403902031704c511800c480c005400786281040c107541c0e510040205c0802050441014004070300101c28904106100f144140020141b030070005040182d040c020010450410604550411241070000317030302c0b41c000507040804500c180d03800d0b0020b41100401500359160b100c1c01c42120600d80d455070462030489000342c50811415a5140011095640d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 59909589 1250 59908339 59908351
    0x60f1107030f0203070b030703150510020c04020318030309031305060a05070f031b051e030a091707081006091503020102060f040206040510030204030204050a06050102070611070b1902070501020105 87
    0x8040c03000c101082d05044580c038498401000d4031581c035182d400d90306454001b9a00800000d40e01d06038040401c80c001e440d2806031104461f04600081c445000a40d2100c085141500a0b6004000b180703400c4009103c200c05d0303600c45000c0d29140c1c505143c2e0141d0344d8000a5191a0303080881000191074100b034002ca440740f84d1296645071410001c0e40380c580c424451203000301d04101032441e03199201076024160110703043c820b001419506074050856002d0104040d4031182a1b00308008031808940c000c3c03d1030b81101c0c0b0b841e0110000800c2031031403500700440d6a01207200f601400c4119480302c801d580c03140090390881c03001000702e42c1c01c4c202ca41c00b401810b130000131701692080c404154100c4410398565480761004000d142792503103400c0850305004200107244c0100c3e401044c14400c615044c040d0781e62040c1c02c1c80081200030315040000303603510b54504c01c600501c0402000160741010a0100d40041c10884a00c039580d1034202c0e02e41c5104091010030800180921500425198410701030540944 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 59910839 1250 59909589 59909593
    0x71109040b1305030d020d09020a0e060f0d08070209070507050f06010b030403110106030602220b090a05060a050c0105010f2d060509030106030515040b0c0304050d051c1104060f11 79
    0x1507606182c145030002004010366861000f84030020b81c880c90741c00240425112450041010500391040c040d440d0f050b0741000010710720741810005113403100704011490782c43c00c0b40d50a00b040c10900301003405110303410740650441200e00c200304860342c0160041440611a10468408402c040b00240e19400207004030600d099040011a0109100d80c0002101c00410b00000a40a94aa4554049a1001c0007000e100d080300f40c02c41e80e0603604880c45800408014240924005071080003804814281c09514801c1c00041035140b401403181d010343e048403114200800680d43c441d80f16180907000f034800c80f00c4498642d0f910301500c2000d0324985c03100001c0351240801031800c0c81015586500419612038040d982d607400000800c8003007100c0640c403410032448103581c1c101303428202d910450040c46504078900800c14003000960020360034168400034601103444114a0a1018403a604101d01c035000c2d500b17040e00b0400d803842520080c030455141d9119401142c45040060b41c1c0314200d403031000f20366 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 59912089 1250 59910839 59910841
    0x40c0f0b0a081807151b11090403090306060915090903080402041112010b13120b04080d110a0f081501020c090403050712081006030504050c010315050a030503071109040b 75
    0x1090042c000560402030707400c00300d14945081c05000d49000a507501180703090400682c4d0040451308011080354083c090200c0c0300c01030000b40c41d1690340e00d4111400f280a08854070000b01890300c54801e200181d68090400e00c03005644000b400060112024014113020100310300180d0031155100720303034150360725880e50301c0d032951036408001c000c002803044040000360800415801c11085c21105001e4030a0480302ca0700c443d001d40c1c90a006650301c0e0406205006000200c002240d841c04080303500c00d03030101e015552030012044040c05480241140e400d01000030424903103003034011614400d0307805a541c070350340345546d02c1840c924010541c41c103103070141e08114130082c03086c10000800390340b05000e406e05d145054480d03501c443c00d481641214100040046042c0548a400200104001d00d071358034003800103044c42d49466803200050769a41c0d05050355030b02c2c20015080c0f0098120020000213040d4102103950381421500c0b40e1202c10700702e03140c10b0490302070341962030300303545141c012a000b101901e51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 59913339 1250 59912089 59912107
    0x9010f06050d0b0f0c1603110607020606011202030c090a0b0a03050609060f060904090b0f041a07140a0908030d0b130207030903030507030203090d030504030201030e0c0102190c0506030f040c0f0b 86
    0x1304042c00340010f10303400000c00800e030070444076030343c000c101703e2007942d407510300c1c0d5039100c0320702c1c10310501811810840d00a0014010030340e0f40025204c4894000300401a41d1740c949650000152150718040e40d084101060001400600c44004e8450303010580c40612840c0c0c1d4690400005290071a41c1030307403000032546010950700304a005824092805032000a03044450389800c461500101c4e110458010110204020090000e010307034000f001c44190a083c5050069015181304840d61502041e5880803c40c50300051085078948010a174410a0b2543c0710101c845450140034078804407401a90740400d12000310540b4030845600d60380503a6045201411503030202c0381030740001801d03402c51005100040030303560345101300e065007840381c0c5940e40c1c3c1d0744c81c0d8400542512a010389070b4405030051601100180d0300407540380511100091405203c2c16940742108184a1a400003500608080108081d00e003101c140030f03000310301480428282c030340da582445d400b030b600f14098202c0ac05000d001c4910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 59914589 1250 59913339 59913361
    0x210020705030d060e010623070b0402030c0904061a0a0b0d0b0d050123060102030c06040b0a09140a1b0308040b070c0308181908300309010f06050d0b 66
    0x9062007642660b1030100002804000d4800a411512201c120000104811604058078040440f215004600c0b50030308030400310700c0c6009408024005100010001d0300315902442440703065100140740700120f0130181840380080c03a07642131a205000400640e440107107000f00104040b41d54006240f1301c0c249803c18108060b1290041054100c001c0324030141c0007900a000355128888511000a0300c1e0358694403d80001034080c00c6941550020044001940f01c049800c503441034100c0148101e07901c4241180340245004c0401a100700c030f8003d604000380070301160500c2441c5c042c041581c4451441178104840c0101d03840028082d1604110810100211901800015015034404d044041d52901c64810302d600c03180200e0848825007420501520707010b031031090344181134221002e03c2801c004003143e1351850307a40842407142c444102d0422125030600300349503c1d82c41e29042c07500c904101c03100502820001e0222002507007820004103c90600d10b0a02d002640c0200080100d9145d0f812094 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 59915839 1250 59914589 59914597
    0x80601091a0d05030a090b090906010e150d060518070818010902040606030207150204050a030605040602070f0804090c0305150d1b06110610030b0c180306010b07051507021002 77
    0x119401007040048859034a90101003003143c0a00042c66561516990090001250350801d8004400c1401030303200c5a00c2d1034080b150b00c8442820004a160030070b000207990b83c1205030344010b008030300042c00d08200310746d500820100e420030381e40907518194410320003842d10340031038604000958000001e4030b20308054446d15140781d114000010041465004581070369000d800207400f2940000b000b904216001400101e20061010114145810000043c009500a102c09004517440748080340500003154121181254080c0110862000c645882140c0342c00078460310b044a03280061703244990b030280c001c82d84500548611030500c80701f8403041014025007100c055981c001307100f4281010424011050024044075203680001c199030092036494060018480c1c80e00c154a40b10802c00103041d000801d80003070800c00c00c0c680710420101070300e000e80300e10303842160f0611900c40001760008022004014840c0030744140d0300c640d0a49039024500382c50907603d000c0164000c03039440d0700c250481d901034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 59917089 1250 59915839 59915861
    0x1020a02030723071d0610020d050901110604060507020d02030406020a0b07051902072c062107090504020405011512020d0b031605010201050f04030c021e040e010e0105090708060109 80
    0x100e19410301400c0e051410384030360802d100080081c140c05550455408400e035120f041198a000d4087d17460340c0c0291103940050070142030107400700d10349445070f0040714291039443d2031004682c164a054108000604030544038400035000f05003400c06a03510104c00c54080c1c4420360005d0011181c0c55070b4100c00300100070b2400c4c040080500c00b0a0500c04401002c04242a05600070480103041c10f211460b45168002920482158407440f244854420006990b00020484560480340c2140c2070030b100d2480380c800c0051060084020101d02c1148503400940518000d070b904210982e00c90102c03566004a031101040403c0d2420380c02c0050300083d800034100a0780400002c20f100c400f00012920303200002c0351054440d8107414040c070655078240318a42c0d011042c02900f540c03a09003030b01c0107041c41c2c041c640060f0141d040030081c084101400c15030b0402400024204100b0784c40b00c03458080c001e01e510b40031130b5035950810000c02c4000d00001443c5054403080d0020300000e03464a0540c4000700741e000c0f00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 59918339 1250 59917089 59917133
    0x21030703061a18010c02030d0309120302131e03020306090706080f0603030d0b060d0e101103060618030102130b0304140f0d1206030206070507080c060f0a110a06020c0a030201060801020a020307 85
    0x1740d280161414083d050700b00000782c40214200100b840c0c1140341070350125681040500c1071010303c21820900700044201e1301c50303a200e01010300c1c005000e21201c04082c0c0019402d4030030b92040c801c1d960380c00118001100e41030b80e1240042d48952404010a0009a6003241e16500074031003110a108a40d1000000107001041e66207401e000c44071400c02d9410b1080c14250940000034802d00043d00e0340180002d05030004803140c9145000000a0064002c0c207540303900010000c101c8103da500d096040b9409079020211030034403903550704901c88107135104540071201420240c003040d200390f000113058490665072001070040382d108410300b16956400404002c02e2661525070000c090b071a25001004401d01a00183c005507041840581ca4042212003560003500104182070400811005494203400b107460058002012040b90a140444110000e4211440007500d251044000140c01d4202482a002804090b541d181d60508078001c04141c0005a0010403161001400f000d05001e0014901c5071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 59919589 1250 59918339 59918357
    0x50306010903050d030e120405030717010915021902010b130e0a0803010608100e01030201122325030b06040b0c031e04063e21030703061a1801 63
    0x4900349400081d004e80e80101e641c448400d4040e00050100880840502c811546000d10b031802180d503600c0c4910070f000034001c008454038184a020b4100303540c0305802c01c3c450700801d1a002400c0009520491150801400d02c88020241c680180030344210704000400300010380034010340343c0000d480d8061640c0414010008c400c00050040e001450183ca0303555541c01c101d241242441580e1039854000800040342c000c01080183ea001141d12407050b050f941c0429801c4034500d070040b1403200044e603018900c1e468020050081d5003030320f10f081030280480c03103406a8080e42c0b405500f10b502680315183c120307408103c184403e044190007810484000705c102c0f4a82118503108142001c800150850415000101080b00e190b10030103c80350001d089402c40c541c8010b4100801407070390303240501d81201c0700c0b40481517082e14080c00044540300280d4101c1740c0e40c0100480c0c0d110107610443e800030229190400c00718101811218100d501a44600418505820301415806000d0411507550402c42c01078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 59920839 1250 59919589 59919593
    0x405060a0506060f03010b0d0e070b1602010c0b0702060a1a0d06110f03040b1b0f070605060f060c100507020705010c14010b040e06090c0f0f0409080702040e15060103021201030201050306010903 85
    0x2500171030080001c06006070300c03980c1c1443d100d000e9035501400701c91903034048071003071100d0300700c4404039810380c0300d8010825244105880161107210034800c02400754040320003005002c0c1e40210f207040c4942400601001b076000c601007a0f0000079010180d241c2c11000c0070b0200c00025134258040d02e00c2e841d4022120742001c4400d4801811344c1d10489048413954112030500840003101380400c5903046801102078140140b081a00300240035070100989929129400705100e520707091400818220054400750380e4941301d0540c60b540300400441c401c5100e2030300d000112250300c04155001543c805079103810100009466640b5043c4640d60001c0103075603150030901e400e640358030900604841d4003001c3d254514180e5042d6091006c2520704901805e00c1e21840707409035550b0383c208285000c0450300010307400070f9410b14841c140180d1030001e40241c07808a03030035081480020401b044942100b1000c00036680d14004400f6405040f81806203554402c005100560084c8007846d8882010b00d482940142c0d00c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 59922089 1250 59920839 59920867
    0xf0a03140d020f032b06030203010c0c1407060e09090102090301020315040b0102010c120903030b0303030901091b0b0a120921170405071502030d0c02010605180405060a050606 77
    0x25000e04440d40c000703040002101e4040c80000d010080c035801940c03c0c00d6201e413206010b8510855aa980405401d03107910300c0344c1107a1b211030040c6401900803c160414494040c00d0b04036209821740344045105082c861401001030f03800300b03443c051b545001001c42c1c21001d00c526041c002d40200d65039502400300c4c880544091010b144110302140108140c0c07860340b01440103c440084840d81164140101164100e4201070340e4814400d00e400000b8004209040c01c030002c21200320203d500d4000081480b039080e0054100903030460080d424002c0c00d020001200d01c0045a5104005a80d04140543c2d861503000c0e481e03410070b2502441c3c004c13481e0303401903941e0700700031650f1400703c0d40d482002100ca0f081e6542c014a81071f44403503011a203c2190900d03440360740e174a203417510406004000132403c44146078803c1c02610494100000140609030314000c01074045d140c41e0040b82c1c00740d03a8584444180001c070707804083c0103d401a002d0801c9840c2d4007002805820000c00054103c141040140d0010700e00b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 59923339 1250 59922089 59922113
    0x160f050d0f0513150203070507090515010203030906060d0c03020907080703050a180b1024020c090f070305060a120503040503070b042d0905010905060427020f0a03 72
    0x41a0090a0000050400909280c1500004408001080c000490341c08034100e403000503a0144414009241031a503800ca20310700c2000b0008115010740d01000913000e84a03001103018844d00719922002c080101c00482e0f4074042140c40344070079404000030403c5800e1860710040388600503401c0407142c40d100c0c0c010030341d00d10084d0f443d08006010041084409549440b82542004c0448824003819500c1800000e0380038a4102c0030342030103005c4000c00d21552514510300c00401103c41d00c200802100c007400a40901e82901d840054041d02012030b5191800321010707441941c1e070384250303d22620f07005030440080100808140e0849401407000c10b08607403020341120300303911400c010b681c1c5508090900d810414103a1010000000610007405107008034502c066448084408142c04014802c4504829144941c4182e20b050329050000c1240509900014031171032040d203090042d0100303030760301d040522031010701e0810b0010350301c44a10061800f0840100c0403030005110025241c0c031fa40300c0404610b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 59924589 1250 59923339 59923343
    0x30e150a05070303060509100501050f090a03050d090b0901080112140610030c08060601050a0f05071707200a090b1201060e0708010e011802030406020c07060e011b0206090402160f 79
    0x50007040b00070400d036041c0503001c050070301074525240e10b0500000110041083d03000700fa040c4072010070b841580c461240c095030b66004008101d00340c203554a083c00c03502ca0b40c002d00c02d100015140d00d800706610550380e00311410f03610306030b50f56034080e803800060320700c004101d00d400c445001d204110b0205a900070413030540668183c407900140d9500d91b103030011ba001c10b6a0f1102c48540c020704104030741a030b0013a003543c1d160003250a11000c0e94604090031141803088602c010611400418403c3c00c0075001c01c05070006900c038140031042d4418500c2c2c41901e004410820030742c40480402c081c0852845130700301c0014003201a00f0034400000b05e0703030f0060079128036800606504171200c041002459004031180d00410300c3c048030303100030b50400400c3c5440040d150300f0f140c00950000301107420841141e04641c5a140f0b008240c071541c503140d900003092030b0a1400b801780003990b100b8540c2204011820271106950740200f549152002c01d20610019412422000d0000c09941a107a0046980845000c8440d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 59925839 1250 59924589 59924597
    0xc09010b0c0d020f1504030908030a050315010513090b0f130207060b010507050d0c03050d1401050301051602031c061205010204050405100e131b06050309100507020a030e150a 77
    0x14001e07540107141c051925401070840d07105500011182001154802d1080e48407444000700d980d950078160307070398265030780300844600c00010762281e141e611002030340c001c00c8500071490f01c100c02e01c401100c00780120180c0d5849010541e204000b40366055021800d01040604000400b49270000001c2000302100f120ba0f01403500058050104401031042d0009004c00f420f01a0a020303040e1211a0f50316a050118024414074078280c0d0145400f50041d1a105a680807050110303800c050706058104d1807e10480e8000e60034400440c2115400c0003501c10308d81403a900450030b2002040b03c4000140c192400010456501e94020a1020300100c001184034010320000d41e440d40381c002444101c4000030f10051031aa00d102c0c0500c03054401741c079559081511b4840448401c030700d6060418000402e28200740306c1040e51140040d0311030b0020047c40c81200c500d4151241a15114840707002d562049078200c0068010490700e00002e8003a003000c2200303400181010349461414100044580d001600310400f00f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 59927089 1250 59925839 59925847
    0x1e080f090c3111040b070323071403041a03060d0501061d060a0308030604200d0e07080f060601120e01050106200c01050405150d0c0c0203100506061b0c09010b 70
    0xba0000d100b001c49002c03411030040201000728031201140c0d025a0050018480c2c00080400605204940740d2510900c0c80d00e801c1231b02411400c22080a6111780c2c0b040340c42c5c2d51101c0d89a0030341c01000c0b0560b0101c1c0c0aa0207045001400000c95031465407000f0b1000c2d40c81105c10b40c0344d0020840074400c1d013015181c0f040d40f1907080300880308908421040281400c2c8988825001400001c08841c162a000b4809903008100012452618400480031307407000a100d080201c2c442c51034100c0c6030010b42d407a8040074141d4249549a11089440f11810300b030500c401e03840500420f1300f0707510820814010034034580740058840412419a030170344600b07034803220000c0c440c032501c03151120041031808208000c11000b8020241c00b640080c1c0306000b203104042c0b10b2151411540d207a0700e485405c888260f06c5403402004590303080400686041c103001c8059010344284800b26070900d640740301c1c0078020580240782c3d5040000c0c00a4000000701c00d114141c4240c080c8032404015900ca0b021030714080c00c10748400c6500c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 59928339 1250 59927089 59927149
    0x30c02120a05030405100c0509010309060b04110901030e0c03280501020309010c03050c0903100506010e0a1205060c12010e0402040603061b020d050a140706020f040303050a1e080f090c 81
    0x3501b40c404a5001d0ba2a00d44190125851740040c11914004400e080206045910b410400b0061000707400003a0030608083c490941c40007410000c201d5000300340c0f010089050741c410855a2541c1010187ea010343c8070050650b1507070350626013000e810464084200c129010355481034207a82003038400c90030b941e4403141c1c06009240c05000381c41d80300c2c5200b0b000d00e00f03042c49030000030b07a601c1807081c05612103581c0d000460901e0744115440d004070080500411201da40c0c070714075800c401d0035104040d00c2c14010100881c940d10441800c881c1d079120407508a840c1a400c04000150744907020f44101e0b0322554904000000503802e00400c0c5840313000804941031640304100103070400101e904a01d04100c000c001c0002500d400980380f804060000300400d46501d602d1401c40000e00c03802400035002c81003c94004101680a4000c040b65141990794004940e0146079040d1501200c0340c181e804144010009075200200004c5160701c42c403210115080c8840503408145414401e401642c1c0c0790605010001d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 59929589 1250 59928339 59928343
    0x1703010306140610081504140108011107020604030803060409060903020606010f050418020313020303040f060e030a030e09150a140a0b0a0503040311070b12010302120d0f030c02120a05030405 84
    0x250b80e6031071200005252a12400203407040b980402c0e8002400350290100b6140300040c24080d00c2c044002c0c04c2013001528880340600021000d12035890310391300707241c1d869000b04207140598201681c0907000b58101815960b800c0020f41006003134542280e59003100b000031505500801003000c1c040d4003d81000e04000380010164028241d07403200b40a001c0004000105000f01140d0b03944d000c807000144c59403180130322021030003090000a54188030101d00803591105030f10010b022a40107858484c10b00320400281615440d28000240c0480c402c8050300e640e038104050346070361003488550840d100501c401c00041106100d50095580703060111060328031420100e2020014026007504203041180600004015100c0203000804015001220300c0701c40d8020010080a01141d02e82c03651035041620100228000c244000c0c0d110b034100061034001c0794000302d04031541c240346688a40b100c28229200340c01400d030710801c0d04c04500c42c429041585403800009407050034400e030350b0075907241042e08040e8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 59930839 1250 59929589 59929601
    0x901050a02030f0310030b060f03330a020306120d05090d020402090d0507090e03070f140703140619050402030705060f0d09060507031d030403170c0d020d02070f0302011d0307031703010306 83
    0x2034000e16a180d102c003ca0b5500007180d070304d10002c00b072101e040030f0100182084002c1c84000c00be03c01b10500c40070320003281066000340d84100d0003591415403014498a14650b031344007040092000c9030003040301030003c1c14200d411019060014202510704114200030030050700c104039054450b508110001c0c41405882d0051079600c4515100031030070000c3c151100c030366104007600700800001844440f040861000e0160074000c54028203145600c031000c07105651600022200b15400d2040014154040d4165110b01d03401241c010b0003e00030750b0700f44018410190301030200140d60325401c3c022031a541059000300b001c4c492040310007107050705200300c0240a075140f45a10314000d07024083c2040003540000244c0342241d0f0080350500ca19100c0f40d040c40040e00c81c50120720038074000c0c010a01052500000e0000c031601e45a422204c2590303590810f51074403a500e000c02400550540001d010500e242d00c40c51100078002816101050f0703032070795644803a03140c600c81c0806a00002c001002405507500c80c203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 59932089 1250 59930839 59930851
    0x40b0a180f200a09090f052401060906050a0305040c1503090c080304030b04030507060902091810052703040b0301170f0316021011030a120f020f0901050a02030f0310030b 75
    0x1000c2d00c0e10b40c40700240c14411580150300c2003d07603a10b010000d109103005000c603c647c03c0002e03100c0c4c0fa140e448481000204140440328980801000001c2191162600100b280c8003580c551f414800b00403030072001b40c40054001c0e641c00e0300c4078802003403d04c40c00003030441c0301016440019880301c00c4d05d041c80f1005050342c4081495001030100304007103408200b078554000d030b040c81c10039564585481c0c804010100040040e4110409804101800c0d0994010000b02103485040303c4603005000915800d4840840c0c00e124502c034954415200c039000852003802400501e4141c85c05e10b500e41d00081c01da904260f100342c056101c0ca019000c0800c905001030b04030300c00719801961414860780300d089651f81c80d80c00001d00840d0903030640114280306e01c07100c41400c60783c4001d8a941d9441c2c500002c0c0300d01c200c0c949c1590714078507090741c0341001c041510071503452110031030350349050408440065034244c202c41003000035408102300010b12488880c1c0190703c1000710300101c1c860141141032a0070303590401410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 59933339 1250 59932089 59932133
    0xb0306010909030f18030f0b010302190302150703031e0225051911030607050c01060501031817040b19030e060f16020c06030405071d0f040b0a180f 65
    0x2007980484d0384860812401c070030344d0410b442503100040311443d44d0092a0b0026100201e08203084040100315105241241e00840d04498101c0041d43c1c82c08070038040b031000035400310380c04074152100b42d2040b001c0c20056000f803c0000746800c007101d1030450010bc42c40c03070300c0c03c0c02c1e03000414500d015940000000e045041a4581c1035940581c1e4400d56151040b000b000e10341066104040c0030070218883c11843e400c0098103603040c0741012030001d040c1d508002c0190b24a9400c008011a0952281c0304042c0002c1a40c40108039454050712400c2201c001c094604101513420400070840000083c014111716604610300c018890440c0001030850702d941d00701c2c0a08d500b040003880112000d42e500350341c0081e01c0344d21b4801c03045101e0b10203030701d041000c040582d0402004001c00040c01030214070f44d0102d80c5151803400c11080e0802d0240d1100004965240380c092a15011074041a244c040f0164400c1c40c000000132400d507402003840150702890412500b80c030200e00030104101d4a003031007816403108112 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 59934589 1250 59933339 59933351
    0x80106050a0302090a0504090f06050117120304020105190e090f070509130b0a0320120d03150e010b1902030f04030305161704080f15010e07021f0b03060109 69
    0x110092940c4140442507040540101e800822907491044140060130010302c204034540c0c0c40e146c85940300d001c45000ba2601840c003400003420111400e104007040c0046409400e080914250625540e0800382040c0e040140a02c00b031066040c0b0101003aa0701c0507c0e86407086600201d10070485181c00c014004000c0301c00e01018801c1d81074111040d40c1c46440200d940a00c034504900e070f200000c1c0482e4039565440251480004240200300c2141840b0300248003527140c17024206000e022150a000d906191190b009120049245200e68000b080c050342c10300303c1d0920035680b10400c0c108400280c03c550b4002c41b00207100038000103107445140207694140061414050004034807807040c0102d100240c240301c0d0015a000c0407006201e00c900c0c2d11640001d40c98080a041c614200c3e141d00980203040701c0e40303d1801d06904840000998a0318407003010075050660b800c220304c51105020261100042d0b12452111a458000300c041d24000c592040740f000841001180c10103281000c10f81c0f082d80703141d10b805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 59935839 1250 59934589 59934599
    0x8010e0a0b0705030405010e011a040f020301060903030c15050109050f0a050609071103250203060906010b07020f0103090b0712141608070c050703050c09010603150e06040f020d090c060801 83
    0x4910307980c1c409510700700030344c07039544138204140900581005280a540381882c0380300381d02910b44144050302c40c00c0d2410070085419408410480c4428014040842e25030720701000007921964096130818405d444092310403104214004c1660b00031b8005003080e9848000700884481d100031010380c0031414480500c0300b414080e01007440c507070002d000c541c00c2050707022036122000402c204841c0d04072400ba945091002c00e80280b5503c000c403c2e40100e11234092725000c0b80c0811800035895041e900d4180c0050b00c1c1903140d9080018179460705507094181a2111200408240141d1640344500303650340745d600d100e0380384a0090044500005500c0100c85030001030000755410031200c03208140d064245a03d180c0c07214241901d4990040000900c0c9102c0c0841c04400c000c2e0124000303030035100036114040c3c1a621400140c00b030300c030f18911001030000703800c4040010100d00f00906130402d002500001c1e06041104480d81641d000041d0b212401d0b465162103800c11400360020070060055180c00002e95041c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 59937089 1250 59935839 59935853
    0x8060613020a0804060b010c1a18070f12020d05100605040b0a120605150a080d120203010302031b13020c010203040b07033e030702060601030e03090f0d1b0e0108010e0a 74
    0x260014041540e00c4200700e80603409410b13440c02d45904070b1120140703103003d4500102088030844074100c52b007005400707000c2d51000001d40413003550348604084009074102810301d006101e07010000d0364080c112f080b240000c59014800d250072507100e0741021426a003084280800da401015000303008609c841e0342000480030079400210165884140842c03c2d448458200310849104050b140d8010a505c9000407050000aa50607060350300741c8860401c4842480c00404034042440007a4140c1c0016102c0c1c90b43c1803c4c0c00c040c031180c00d0b005000d10301d00f00c5241e882d00100e03040841803c0c1103070340c0003040c403043c0b002420389564485031902d0103001e0184801700030058040e10101c440d0f82c40c4515031000303d0012038100d556982170710784190741c0d80700e2138880f4000359140d07002c1d038003a0301082c03a2820110181c2d60100c210780140c80c0c054400c1941000003000d12001d82800319091b6104c0e0300449512103012030303903030040c4010400d0b8041c500d10b0b9410300152a00b1603094001c81031440c3e10041311000000e0781 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 59938339 1250 59937089 59937091
    0x2010b0102010c260907150507060605040519020318030c0a05060606030103030e060d110703120b0312030106050901030207020406090902030d05120406090f020405040605011a0304110d0507030c08060613020a08 92
    0xc2207030146054a03171005071441c104032900407451030310307400e064403229a070300c540a042024003544060180d107960702e05100c1100d80645051100000c14141f071402251380c0d400441d0030506075041e00704441020b58040f400c54011010030803282e0024145101405400c01c01c25420a4003150300c00d10315451507401411981c680000c9601500001c00d5040300f02d191503014105102180a180f9611015890014010042c09800e809040d00e800441c103d00e050008102c00c5103c401ea090628503402c00780143c0700c1c0c1d0400c0c0085410981c0810610b40162218061480240402c05000c00c100c01c00e0b00c105414404090701e410200442800420103441508610035085a080840041e071201c80d030828403005541c0c120044d41140c280782c00d0004000807580a40c2c1242c010300686441c8903050640d1a210f840260303800351003000a24002c0032540307040c4810002031b61084003260074003956696440c1003a01c60f50722090031070300482e04110580c00d18600c2e49980c0c0504107011031801c4c03c8414080d004081c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 59939589 1250 59938339 59938397
    0x310080105010509070c0317040c051c020906120c03070b0409050603030c0c0112110310030b01120507090509191208010609050d03030b04060915050316051005090d1202010b0102010c 80
    0x1b081c690345018540150038151900c40c0e2595400160f140504040c00d00744030b00c0c8034190250194180c120b10360b4240740c0381c2c1c41c1c0301d6078010305c116120346424081008071039201003900c1c41c60003107100c0b2120950781001103d00410429030400d88451521100c9011100010009400b940013000109844040421224004002400c02104501d42090348100800000f18441c001340c00002c04d0141d07030603001014008480c0f0540441c400b81c0c1c1c07111026890700340a980000c001d035010001c14002403c581e0400da51048001c022140300300c101a610491058080400b592080c294450000c0b846601210f40d0b401350000b424980102d61401d404103440010844014041640d211180e6010b0b5a550704403000401c440d410a101a0701c5088940d0f8509003a03218243c03081c0329200c2c400d90140e0316003078110100c1e10001c0c2218255100c0340801d1318103038050150241e0140c0d52203088000250300801a650000780c540c00019540d1100002900f1280041015005c0c0946d440100b80320706500500131500c55 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 59940839 1250 59939589 59939597
    0x601021501030f05010f020d090501061e03061116080703020f0a030503010b1c0c050c0105060904050601030b070e030706030b090f04200a050301050406240608010e07180b031008010501050907 84
    0xb40084c03d00c117004020354031070781c40c1d143c0c00041c131071650300550340080e021030340184004c000081d915500845900d0702101100300740c5002200c00c00c0401c6689e4001e0751710700c4803080245c1c03030700b00000100030b0408003080003100e1010000c210f003414194100a420060b03d00e10f002050201d185880c0a0a90b010506c5a00905440013542080404000e000101b0b0144094401d0200c900c09002c0a0003a4010340ca285401d50301c5c0c03c0000d5401c0c5443c08440c1e000740c0c4c01001500850b42552a520b0708210010b203c2018803140283e4600c00340c90070070110004104a540000320b401d090020001c81ea000607006801382040c80e4240800300f6600301e000d8900481c2440115403a101090201e183c0c54001d500448c0e04d0751912042005010403030704003400303111000d0306418030b944003400480c000051900402c800940c00c800140801d410808889030407689a06140f404907100001500068171700342c01c02910340303030080280481c0c0c84c40080c407034003e400200000e022541c1881c0104505550080c0400100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 59942089 1250 59940839 59940863
    0x5060f0702030f090102010b0a060801230a030305071a040804031109060102070608060a0503030309011b02071206050604111b060c0406080c030a061e14060c03160c080a030314060102150103 83
    0x1342c2c3c000d61182c140c40308058000b4540315a00c20002c1e24003130003407003140c0f035012106440c034103024410981401e11400062090741121f0950b10203da150f006107100312200e103d0350300802d100e6088180e055119038400d421440e921801e526140c1c07195600455018001e00119092200340c2c2c0e0042155403e40d2810b1801c1040c65441d8400100c00440982c002d50f0940400800d02c00310500c103401c28590740c00c00b24504002e4107000d00c0f049a88a09034030455600c0005080c0c142c0008016400640d0403034401000400c0c03504002c10402d88552081700759105030029001584403d42c000d2103c168403d5010900c036040c01d151850185c4440d00040101d100f00b0000000103103440819030261018203501d5060501040b1020b012544219030340c09800034600341005001c0e441d01d4140d040314040c20b400c0000c0d5061043c503200c0d105540032080021180207611180110380c90304200711450030180260340106602c040401195003141d03010308100e0440d00500c0681ca0a01c141900860440b540440a8004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 59943339 1250 59942089 59942107
    0x17070e09060a090c03020702030c0105090a0e07050708121f0b0d110f0c0607110106030804090e010603140114100b070b0a0204030605040b01080f1b0f030109021003020705060f0702030f 81
    0xa0380b4858000d416a280741480e00c42c00154950f001d40b005600c00d908030703841842c01134015140340c002c8007070107503018065120500070740303010b0307984185c00400608160303042800035520400c43e40c00c95400042401007490401c2907020319401c041d041006c5001d18080d46c2420b210794000c451080a10f105040354450b480700d02d107072134044115004c0f0001c00e11342517140c030712104d10740e43c490009072250000103000c1c25401c003401d80103101c3c090449500c42900c600c0c0034904080f00c400b0702020005403046560300c0038004042801e00e08000d500100c0c01d0000903020004410400110401400c0c2d8030144148000621890b0410400c41c0c1120b0707003102404030f242e50380c040e091b80a44201e400041090b8201014881046814000300d4142d61001055030240c44020041e143d6401d101d400d02cad03403110341007440440ca43c01d0403044c0d249503180150001c9400302c100e8001c2844065080c500c480060b43c001100d00606c141804525080128018000e0721030804880081d0749000c1e08450002c140070001c0c0e0995 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 59944589 1250 59943339 59943349
    0x702120c19050718110405010e0310060806090d0c050607360302010f0e01140c01020c030412050106050a03080a03230702010f0509010c05070b0709050307030f0317070e0906 76
    0x303094000c03040698550340c40c525149894102912a00b9031180704c0200900c0000c1c2c0b1400307460382039041c075191942000c0c0351100466030b03200541e0240d0b405000c0e039401c0c1e480c035003050300484005c0c0c0f1260005110500b0461070380341c98045900076140401c8000909140026804110103030001da50b850a000341d50140301403900c000c28003102990b181c1210a07a9803812110a040d500116030003601c0300340c10750032415800c1c1ca85200b2100041e00042e840c8030108c0010300404041c001a4031150001410004090816440c661040c0c1000c0164100e81e1000010000c1c24010403001d440141e800701d454618554894409024080300c840506444244071200c0080bc04080800100040c00c0c050381400c05d0300b8064020880c0700d216045a07410311001800849050040814a0400365126480c1c4601a01c1c1c2c143c200d2809080d003810440040800a0300d80d03410081c2001450148000d141202c41600e00944070b24661107403071843c05000400c00c18400e4120000526040c001e6801d01c501c0d03950400011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 59945839 1250 59944589 59944603
    0x240907051003090b100803030403030c02031606060f08030f0a0507061b0309111c030305040c090c05030a0608070e0414010b04110414030c15131203260702120c 70
    0x390080306400c02900307250751540000064601404461034180c40b120400019002103005040990340104046000203120381c3c0003000c2040544141e038105180440f0150102c80740c140255001502d030502800204c0c030009000c4010305d002d6009514111401d05c0400310390003014800001d0040c01302c2c8a5003840001c1c2c00070080d415401d542c0c50040304c0c01c003001a00801c0081c8098034014442e14103180d450811008080201440d18400e19130b00c13000380e6003103001c1d100c020408c640040c3c407640001103d04c440d0140514012013919400d48920304107001204555080d408030b403696208400400028414203034003601309400141d2480b0681085c2c00080c090110792083c41d402030302c1d00506420301d03140f440140066400445050001e0400c190401d90781d6a20409070075070100346075440740b0200e51808000d0401baa180c0600e880342a5841105840c04c942c1002d065010403444804642c600d112030600441da20346462403e141401c242e070b002546d6003181003564241a000083e00185d10104200300b0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 59947089 1250 59945839 59945849
    0x1030201212a030605060f0a0306050303030901020901140910050a0215070906091d07030504021309050102090117040b180c04050a0608060f04030e040c030b04022703240907 76
    0x501c0703201452011102c04600000e482001c100e0b810a126034030512074011001182d1004108904088108100c51240d41c001075041c01450303580e210006850b1014005144981248000141c50b1120364001400026404050740b510780000c1040c401c040d650640720b1020020707d40b0700992118a10701e02a4945800708079042c2641130f001c005c1016059020b0404800c2d540603640d4180c44c16a0b40724000010041103a04c080d1005017400001c461900c00d60006600500041c0722102e0306040341e146000303c0d0410041510181d40000d60030929581104c207225110380740030340d0104035251584481403109000717805282d0f040380e841100480c0d1001082000b0400500034010070950814020000082c00d0038400e103d102c3c0a55400203014208017040707184105d4060325172041d0081440104002401100189001d15581e4140c210094840303202500c8025030a0820303554400d880c0e0fa03803d00340d0400c14402d500c030f9445020a24260090303824405100121641d02543c3d6446001e41d02c0d090000c0c2d030b040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 59948339 1250 59947089 59947091
    0x1103070201142503111210050102010c0914060417030409110301080a02041e0e0a050601090c02070b0a050409111c0b060d0b041b02061e15091315060501030e0a02090103020121 77
    0xaa10200380c11881b028025001d40b1650703c0e000f0b07600d80043e401c5e00c0505040c180401d0941004010000d24003901300030b81d03c0001c00d0300307140ca40c171550a00681e403080402094254000305040c083c007a001d2240382c4003103104160a9007190301d0311940940d10f84156500034043c98982c182089494554581180144411982401600d005844d050740e151220041038401b441140c00008021400f0b2042d03450840c400d50240c400a4201008038003154000501e050801504101c000b841c0403a611504819080c0f0f1841d81c1e550b089403031041c2c50b0b0303031546d0881d2035071461602c00610120358445e0112007011103103c00105040410800041c01000140715000b07074044c50a000c4c450090340403c445124161000600318440c41e0204030301034440c0700300d0307102c480d141c1100c0350070110345480209554014804261080c0040017035a0b0722400701c40e6808100002611100c00b1b000310341c1c260017407038a08280d41c00104030b02c19054000812018040c400079062021445103d005071141c2d0481440b03c0d152440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 59949589 1250 59948339 59948347
    0x30b010c05060705180f0a0e07021c030b03010f0b06160602040b0a021e0d0210240609060e0405060a05040c050c030703090e060607050a03140d110307020114250311 72
    0x10301140c3c0302079011941c0b5802d0009203c924a40310031040305c5140d000e07003140c800d6401c154042c0c1e0701901c0270303041c2015841147c24148819540020192241810b0b07540850ba80c400c1105244c02c1d10750440110005908210700c05282d0b4984005541c90491031f001da5206c101d480f810500300900c2641c1003030000761000500350307110301d0f0002260041c0d03494110f210425a03522403c81502d075a01016114016041030695214840580c1c100b800344440c4103412404800c00d1203001002060107510800200320700c41020407002d03801c18952251840b00746c809100d2403800300e00289400c5010b008040c0720380c4d42c4220f00c1e03042078490001e49056580510403a5074854407030038090880e103400e00c40d21416a414400040c40703801c041c3c00f07584009600c1401042c440d1401e070780c1a1490080d9006141d10603006010321000c0f29118041c007200f945085844656a04218100a09450345100c1708a0541d510000340122300e1070400405003990400c98049240108e0f21000324090a010b2041c00000310303003c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 59950839 1250 59949589 59949601
    0x721050d23071b0e16080601030e010e0a050d030c020a15090c03060203040203010b040218010809011b120f0e03070b221a0718090b0a2403050601020703020a06030b010c0506 76
    0x810300065140e00e40351100c1029698150030702c01303903c01c95041c611003503a50303502190386000e4141d5540043c4c0506011030241080080c440c00c503280408c1c00c40c038981c000400c03001840030501004620003068075090158080c42e0384003075580c00d111a0001c14841140c01d20b2103002a0542c8650712071130f4801050b00303000782e5078180741c40030350400c2c0c4040e8441e5281c1050883c0354a801e100b110f001d007800c442ea039030040360b10b40f005544401006100c42c4865480d14201425107280500341d210301d0105480c1c6c0c40201c84c07003440c100212040c01200c400b24606d00030708601c170f200001056811803580506038600940e6012002c180d01d0004850191300a0074400300c000030007200b07900f540083c2d010784031a00b0103a500d1030030807124440d01600000f20000008421701c03042d0403540052240c1071002d402d020b8290b83c3c0b0813114201902035051341d0a08015100c4c0680341c91760602825800220034801003054070b056400164207140c080c03003080f06142d40e9645500003a4001c88210b20b4041e0407600b524031901c0d0071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 59952089 1250 59950839 59950853
    0x7020d140d0507051b010603030f03021c0608010207030e030706142104080a1209030518040204050d05030901090803070503030f0612070801061d0103050307030c020d050607020721050d2307 83
    0x104003c0906005840d21700050404144108401c0300d406554031500b017265142c09070000e41c4004840c44400f81400500d440003250342c05840d0003040820001a620805801d00501000140c0c0000d4400c2c1c0200c0400c1203080e40c4805071804003110580003e46e1095000e4441c40010800d007612140c208100c0d00300014048460f01901c60030000761606614516038581420484030f4115001780032074400d1100c83d450507900040410700000103040145810388500005500181140007200c15903c001507001055900401c00742c01451008001d506084465440b1034590100803d004400380080d80001d0741565086900d6402c81e44070016108000e841d180124003809039805204145440c0c003903500149140d1205c164120b070b420074040c41c100b001ca56011500500702c61026640881011560004501c041c41014080c00311500140350f0b061401002900021031041f1800c00c43c0c04500451021a80110f00110f55403000d240c0904c40151858680c004400e0320368000c5200311001c10b80320b0800041c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 59953339 1250 59952089 59952097
    0x10318060e06040605010e240301060803031003020f0102031606090c0b071209081f020a050405060313020a380c1005090708030702060a050d06120302060f0601020607020d140d050705 80
    0x2613005103e241c2c0c9803e1f00151103030083d1910f1060a07522618000c000310381c00b010510f080002400440c030700f0380d28049540780d9001a20340d1114140c0c50402041140b8010031078100d82d101c00e002a50030050030070a0740c079062078100c0000e070005460704101d07000c00c0045e000c0103028020041c4510f49413280c5081002044230000a01c40c08114400000b060b00e0400249601c01e001480c021018005092480c18002e90407040414090040c1400702240c0c903650748015610520ba4640003c10151050041140c4003400c0e51040c001526904903411060b018504da480a0032142c407446401840c0480172022a8400c855440c0807a01030144001a003c501e40c110501480e441000c4800e0980c80d041076584038030070070300002d5000e0760801c02500d15174003442c003801e4108c2075210000b41d8295502004200000080c0b42100103030428010480980d00d29058030b50060f90030300c02404a442d0665003e555a0100b007085002d202d075001868600340f201608031000c0754500f01c0c050000303003000310001d015604 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 59954589 1250 59953339 59953343
    0x60405060601083310020d020105011e150e03010f021809010501021c050409020412060c080610120b190303021507050d020c03130e0105042009010318060e0604 70
    0x500001c14031a602c10365110b400754221100c0703400d00203862038003a40c1115454890101102c01207046080c169580c003d800142450780d000340c4411070250200908640b4140c10405031408500c001c510904441240001504c10a01d40840000500d500a40c0c9040105003040da143d130820300d810131400d946401400d0755491035030568407004078600800c926030f4400d0048130f0059020021400c01c24411980901002d038080c1080c034540b90712821304134183c1e4455000b142c1905034100300e940403c80c0318070400100171080c3c6000c08490070848001440341c240c0200724810080c009481000d203401961100c050010003c01c404032060b00200d11401056051106402602032500e01c0620307902048110352140109968080c600103240205070000c0d0041c1b80c00c80c0f098131040c0b10480c459030400c0c0742c2074081c220140e5207810070341c035210403c01034030b8480c80e0f400316060380c0b90b00b402551942c4106039400074109080120340409841c11124281d411400c01030007850403c00d00b00141400400c1c4240602c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 59955839 1250 59954589 59954593
    0xf06040602040801230f2518080105060a140301060f090501030302120a0504031709031006081006120f0206070b0703020d050a0b01020a02010f02070f0e060a06020a0804030314071202060405 83
    0x1010301800403a4080c415850041d0a15817940002c1d000b181e1640d4840e4010f52241c01710f8014820440500d00000e16281507501103405289504000c240b443d41b56401000b088000740304e180341c48030100d40d040000d072007006a00041e0045c038002540d000e40000019120b001020101180c0e00d100c180045e29086c0b10980140c01032521460f0b00c440c0c114211101e411040d201c0d5071401c0e02d0359896130510594441d0b84812107409100c800709642c2d00b842345005600314902d0202e1007a052049090403c0c0701c50400d211a145841c01c208448402d6003c40418036400c07264407441e500d12800800c560384608000240070509074400c001005070141d010b0b00a0081c46042042150f444c2081ca40440d00c402d070001f40903138421000a001984101020280702d500c51040d42c0303405968050031503003106190817048a620209080040e142081c008100013003d075440280768540d0303036869280d49441603000c0507040040b400d0580d44151884012501210742c0120054804011140c0081d2100410303a4101c50304c5c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 59957089 1250 59955839 59955851
    0x21c02070801020f130e0f04110301020712030e0d0e130b0d06021201080706030504021503151903050606090124110a03080105090a0c0e01050a03140408030f09070f03060e0f06040602040801 83
    0x107801103031034640b2609201f94807800c02c0d19a81c9030304280742e00740b180d043d034590340030410a80041d1142080d620810440c4c1c50109001c41c0f1442d299040558006000c0200090703c0c04031420f590704c0704215a644604040700094003138498012442410800c2c1c0080c0c00c642c00085c101c0482e481985009040782ca00384252541c0303a40b07803002102611020795029505c00302490740c4640d020301c00710046800c20340718030591707600408000c0899010203503040001011003141000b0401d0040c24010150b00100441d1007406270b6050074040d040c4001034030418602c0251f014107804a49000b16007100070f002d0342c23070b00701c94001127146401001e88409000d42d90151544d480441d070444d00600441c0103440d280c4d02c4407511000480011205604030074000390405441c1d071820000b41044540c4039024078000c0030015500d140141c1e40b51403521026014088079800070b14204841c2c44c40d000d030741d401e0321350000f0040b4454254015103480c020740f215090240e0b01426041c8800c001855004000f100c420070001d100c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 59958339 1250 59957089 59957099
    0x50a090e070503091e1509101d1015091d01020d0615020307020108040206090120030705060903030108070506030c0c010c030e0d090503072c13050114040201021c02070801020f13 78
    0x5024850030341c01a156114032000c1c2e1040c4050700c05d0f682e2110064040f1804200c2c01490041510b49c41561071000000c40641a11490010b001c000703c61111107009000151000c400580811001c0c800c010740c0ca03070343d84407012410560380103000d002102c01000390b488485140d401c90040019206090414466a035100c40e200e0010064903a4035405031a80705056807645c0074041d2076130042c808030307040018034004841e2101d1b00c444514807104829004544424441c40c100e0316280c0d0117091500a07034414001001120030025525040d58001d480403078483c1c84404408400b0b001d01280e150f2194200000c00038030547c16480f468920b006042160f03110071401d20140c5490029006850309900650350030f00020301508582e8104141040e100003240c0800d440009034400b0a0750290904030302241e18506001007400381001c1c0312450050003400d030a01d40c0c000f03907031040040f0010540811001304002c00e40d0080c44000c0c002d04109000355034400ba500003e4001d80c5c80000c0050010607015004a2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 59959589 1250 59958339 59958373
    0xc030b0904030f0e0f060403050a05190c0603090203120403140601050411040603050c0702030313090609020301060c0f0516060c020111030915070f080a0503010905060d03050a050a090e07050309 85
    0x1c01250580c4034001c1400c520a0100c46030805003c007680c1280201400710300f503488480060008600800140034009154a04a03081036034103046248412042012880810407181c1094225151400c0010382c2c1d03101032021030705000b2007131440e0501400c0801c000060281003008500e101c2c05a81c282d44042e80c8800130042181d524019503107507104d003404107100c1c56010764440e94010f604004c0e854101b0351150300080c5103500503c20002c02040d2a02c0410608103140100005041f03c0b02c001d604560400e140108103c0700c8210145c4130250350351a4006000c0c05112524501d044111207804490706d60340c010f001d651201c5001c900082d070012122181c01c00101c19070f1034650004100b0303a4610005040110190800380c015a501030000006400140340000140030100942d22007035100e6241c2460501203500040c035181c0624003081984001035400300c01c5070765174581030074180d888206072102181c0901c1690400d50b40700702038409003d06a50060007640c4a64550022103e0010140b81c1e110b07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 59960839 1250 59959589 59959591
    0x30601200c04090c0302091e010609030210050f0d0f020c0c030114060d05030d0513120c02090601032417061810021b061807050103020a0909020906040305060a0c030b09 74
    0x40e9141c0005954007014500b5402c242d90860060704c404a0b0b140e1242c0005000c16030968400540c1018200000046210b214201c0d004006900344010080d00e940c000ca0220702c00742040d0010000d00080b000d0080d6000300030f80d45800c2c0107982c100245030086260034001d5001000c0f2506074030030501c1c480c459107414003481c541e06404001c00d1106071103145c01d2001c880b401c00400c8607140400e101a203004101486014170607050341188000140f81c600f030072803103943c0100c881410814628902000f5854805041d9001142880c000442940c2e40c0002d803040340c40b1101c4941484100540090403200032140c02909800c560b00341c42e040d03100d2250f220942d8000c100047c08542007a001410031542d5a4060004d01940c8180d0841d05050b012115040c81c1c41100c1102c114142c0249010906030304019140c05084207003004c5241c0b4a0180014107040518418144456000601010035850742002d4a00866001044498500300100128050441c0c0e403030b600d00080c6018201401ea107070142010b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 59962089 1250 59960839 59960897
    0x10050606040f0504021b030a080411010903030206070e010509040609091e0b010b0306040f0603080a110102090105090d0c031e05060f01050d080a0c0503040f08070905010f0e04170f030601 82
    0x80b5080c2c1e4580f0781800065004101082200c800e80c1e8040991000b080c03008007560003e0f5601c4851624080c6851104007094004440c1003250400341400001c0d0001802900030b2900e040c01c0b0049100c540c01243c0c1c40c8100705a0700d40045c144800054921455042410180d200320b610070315100c1c8002d4210b100b02c0d21400094154090352004101c490144001503400c031758080d0011648207805002c600a40c0c22981c000c80c2c4145000502114240e4800300c6840c003110307102d000754a49130001000070503034000e644030b0750320038680e002ca074508204582d4041002035070310096800e0500b50260501c0d0304c1e00c1c404882a10540540000078085024046185060300c41c020300002c4901180d46030340c5040d801c0050400c06000340030052402045080000d031006049292140e480c250901c01c600e4103119207a8415172480d41448010700180301e10400300800c0d50b044e04030001c074907900d074203200c4041d5228140d001d91101000603220840c61004d001144240d83c281c83d03c0141d5813040340b107090500610075403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 59963339 1250 59962089 59962109
    0xa1a1011060a1b0804080d02030705091201050103050714180c091c03090e09030c0a060515040b06040522020d0b01080702061302060c030913060509070c0302060103080306040f0903021005060604 85
    0x81a80e4000c84c00c02d40c006008610081c00d011245d015203081341d10640e8280c010940200e002c0040740b8080d2100361380104010001e0000d945569a1141e0f9011540603046083c070b54000b60000585800401c880c551144484d003500500301011160003d500c240441c902400e05e01c10040300ca1000c0d9640e141c00c0325859950710040e01c0c98102c2420704480080c080c510940408c003c03000b07884408200034803c46000b00000030303441c1003490403c648031825403403c90103a414040d003400301f50703100d0003a02d00703c0701e05860024054414880035410f0392030401d10401142d20108201c0d5801744c0b9540462021182030703d07858001c3e1030301001680d0b681c5c8126444014680368140341801420040054450090380c1001c40741800c500c00e0009040301c40804e1510301c1c0301e0381d40d04100310f1443c10b041001e030000d0003420090407070031250b24020340f01c0c2e80501018001d80d50010100311b00d03490303070707449241c1420502d101088801c2e000d140c02501c03208402000b1100303904000108416107070010880d02201c0705151 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 59964589 1250 59963339 59963381
    0x5090108060a090c030b04050601050901050d021c02030c12071a0f07030c06020c010c05070516030209071b0f050d0206090c060d0506040213030f0501050109140a1a1011060a 76
    0x40c1c0c880541581442104c0c2d2074000400040024454560140124031400c0545003d42c1403405120314500140c2c0682e20031020030783d00c0d10168442c2407000b80c3d0034111720803a8801c016503001280c0341214a482a60308070b140c4441301e0846a0002c00c078801500c00380302c08265941441003007104203004004540c0c003180420010310b40082d00410325100c00c0da20501e0054100b00340390307111a084030301c204c0e4004041600040c40c1c0c0b0401c85c082c03004001d0804106003030f40c80c2c24119001326003132290003000341d024440289a400d0f4036010b0924401c40450f80010143e105524030f2522540311640318843c400035103c0e00c0c003c00c42d070741c40100b0314100e4503202803c0c840c10720858001100203044042d08061b0400c4d82004246c5c2c3c130f41080000380000c2c0d030194070940e008403030340e10b4150b00b1144140e100d100401d01c1d03c0c200d5070b05402d440030b0854024101c040085510803051030f0400f0988503c12070182e000c00c0c0506020601a0003c8c40d0300c0d10b035140d040640d4015900c1807611419148039408075241244035107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 59965839 1250 59964589 59964601
    0xc07170c0a060609020703030605100206060105030a09060f0902030c01080601020309010c03120e03090a140a0512190b1b0705060f0709090c1d040e100216050102040e100509010806 79
    0x5000d4822182046034007189480d2668401c48a19822144d585031700040c0c0c44d01450740600a0344014901650380500f80044000000e4403948050030030741c104480000452035540384d503009244003030f800120800500010034158401800700d003100324000c0c00344903140c03c2658056801a48a228103801540c540300d581001140d08061a12080342070040700c007041ea4034004940715810a444d0000011541d42018804001c01800c503130307010070303803504801d0003951050f02c65500c540b0440303005507254001c0b0318142117940e00389441c0e41801e08901100c001140241b000c041e0205002d111504041c0518045001444003684105800644140c0c000404103402d039900902071070b4006c20038a003014805480d20148000d403210510300c0800110521420391120540e0644403800701c00c01c031800c20250502c4401d55803141028002c0000341d40d070129408508490f40c2002c0500c1c264000c008642c0c86803a0032910200f814141c03554101800c4910020601b42820406581650102402000155038036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 59967089 1250 59965839 59965883
    0x6040b0a1406130810110309030d11040510090e0c0c19060e1e0c010804200102011508100b06070308010e06010c06021b0c061c050606090a030f05060c07 67
    0x8555219007111003003000c00c1903000c540301810f0240141001070900139104528440070b59048051503401071100f001401046d403000070449044001800d000702c0c1810072072142441c5070090740c2c09160800219116004000d030b10401c4034084c2c3c0d000c80d650300b42c41c0e11348600b8842e540c042e845100d84603502551540007903290701101d03c4a81d5218150100790303042140707044c03400e080c03031101e20b404108241440812000b000703103e081a818070a18120700d140c50242c580100103000c1c1d11121040d89070340c0d440074400340d01c02e410200488a9000d000a90940c0e103128440c3c0c1ca600c6400c1484070035190081c2c2c8581e52400200b11a42e40c4c1d0195221a1941d082071014422400f0103031803d0b06200100b04034034001840d5002510801c075090240c01040500b01da01c40e030504015801e25441500100180312401d005824140a0022070050004081d541e0401080c02e912540c5a25a4403403031740d80740081042450b2a007014124840c40543e0626102d4148000072802024030003020000c8800003100c4e8140c00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 59968339 1250 59967089 59967119
    0x5030a0807020406090c050304050c010315090507030e0d0509011d010816050405031207030806031f0209040603210f0e0d12022b02190c05090402060712050901030506040b0a 76
    0x4000203800356131507540724106c43d0840310880102d00c01200300403e0010920528600072801c2c01c0c107002840d04408010b60841050088130100e40d902c00108100e82e120b43e02018a4148000031109016080c0d5000b4004e071300042105400210510542c2031410800e5006041201042e11030302c2154031841584403191994240070340c100203040c000040c084c0d44c100480300004440071030450307481d81641070003450080028401030081d40002c018280050305642d0307558442c10001001070f22080d02c00d00040c050719155001030a14140002c0d884004030398894040841d20060720340311240400c6002c16943c00211551103540040320701c2049000c030300e00d842c0580301600d00c0c0c8141e4100140402012036800740040512036070074002c2c2d4120900300d0301040001c0004c445c44a0844121400d41e84005811042d401124024007914003c10219203c650a450300c150348100daa4030300800394440100207800c01c4480a002a00b000041441c60606200b10b0002210140043d81d0f25402c0004a8004190b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 59969589 1250 59968339 59968343
    0x1903081b13060e1804030801031103061303030515150a090f080c012105040c050f010c08070212070503070303020c10050a0c200a0b030109050c040e01031b0e010801230105030a0807 79
    0x151440000811503a80c0400e94801c510a81f6040e407903504509001c1506d40a000c0c04c240203520200603c0b412a60304682404490760607e404595a628001404451030131203010301d800c04006c0d070241104d01e40c0503000e041456000e070f9031000c40c95540ea00c0804a560f580c422503099400c514051b5003d03502c512080024820321544041d40c95409401a804036a0300b21001d80d072412a0349028011440d140c003683c0380024003464181c01c1e100319a00d07070709002d02c2000e01c003d11a0000316002c42c07100d03100b0310410000384801029504107641e00d06020351510240045188541020360050403c240680700307855401080d50f85070103000019565908076210702d416005008011001d801d005a070f01d060719407000e403400d540c82d00d0303c0307500d0a100f26080e10005403a60214400910040c4140c2c0c0c00d1808040c1101c0c1c020741c03180c030200606151012400b41c65081401411513a174004541e05d101500451003030b2181140880b02071070100204c04e03d84100780507040d0301d07411507248440403030582c82c0a00380441c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 59970839 1250 59969589 59969599
    0x41515031503050309040528020304020f060c0d090608071e0201060515070606210308040311190b0f10060f020f0109050705150405090403050703021903081b13060e 72
    0xe4a4030748080810021688115599400050758440130f00300b5000307441e088030781c6000b10040703102c00d444603920808400b91081071060340031001900f50754521000c4c1c28182d90190015648440d02202951100c10715187d00740407510500e0700040c900d2140f02907502c54481c80d130314031048285030000b400300041c1f41040f400440d0b4a0b26070116580d51000c400c039401441004240343d5500c280d00e0020182c2d000c0d5448801085503610403c2130440a91040c0951542e140c9001803041e42c0700d18050b10170a4443c41c4c01420b074412187c10750741d84040030306c2074910356000340401506695401c50035418044101c2d001c1e4202061106c0c1084a18020008840c0100d400d0040c1c5e2001d0000c0c0d038056003180d5003024203441650104508220900b4040c1100d0000e501184445141a013420041765800c00007600040c2044800103508040c184280502002e41d000d0700324004100c8c4d11402c008010b035405851480000c0070134042400300c42e5011080b0350050b000f411841c403505140081c103441c00054192166004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 59972089 1250 59970839 59970851
    0x6060901080703140a0e01060812070b2d01051e01020d080726060901150815040f020c0106030b070320130807120c150e13020f16060b04151503 63
    0x2220041c0804e4812603d4803400140707141c01c828500c0c00d440c015130009000b50000744a25482d01208030440780d01359001400c1e130340c1e070743c07100c00b81c2410b134500b1500884c040d070000a142d0301700c2c1c0c7c0e110800b46040354030885800f84008002600c1006a140080c030040c0941c1c40410325916050060301000c0d030041e41400d02c90640c141e0050444403020801100c854007034490700c100080d40c5000d200d51405444042d41c0f1102a05c44000050034084026240703a10f103c450100c1c000c119507840c1c014a0708090f4202c0c00790740302e1161800c0c50b4040d0030a1302003182e2104200001981840c482d12420782c050141410a941442c4d402c03500c860f030b6030b000c900c0c0161020003000000c03404038020081d09000700800503090f41c0444c6141000f400e0400e56421616003040e2001100507000c2c0c0c48915028070b440304490980300080c0c8502500024403500d88401200030b00480c80d01400e8000d020800400c50181400f0300c00b103040350003004122000d001c070703061880b0300140050020744001040d00540600c0c90900082d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 59973339 1250 59972089 59972111
    0x2070503010c0302040302091e01061803170d0c0815040203040213060312020d05070309270f0606080603010b03070b0f0c0105010b0c011505011e120c090e010e06060901080703 77
    0xb503455182d40c0c03501203500010108214281894a15031041600030752410003006d80c0715000410340b061260f4400c00c000c042194940342a0b20440c800195441106190711701510304800f130080d0003099054201c14500040940307001d00030707091580300b81d010450140d1210705020801c8001e400140c400c0ea00902142c06ca1140030080d4440c0b000690b00507040d0405070040710030001d01c1e01141001e1102081014020400069042544042580e5100d03c10f4143e002ca41400044002100c0c9088801d2030305007040d85d0a44101a4001e40541d40b455890507035a64850301494240d4200010543c3c051340071003010007100031031a000d0072044001540f15803510040c074181500751042a002106040c400041c240e8503c0024868400c40e010b010104440480c6080c0010304030760308032581784e40d10018840e03800f403c05204602100000740441002c0144070300b80382004210103468018400000b41c1c080012824882c100c1c0210310540b030081a1915118034800111294980035040806154880b8002a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 59974589 1250 59973339 59973341
    0x22030206030a0209100309020f040507020309090a151707030308063f010902010914060403051009110a080309060702060d0203040b04050c100e0d05160303030e0c0a050f0409030207050301 82
    0x80501030a00001d40c5036692a010045e069440345181011716290180c0d4400503110000300d1104071a04841c0020140e88545050f0304500c81d40004660050b520000c100090000358040c0702042081401200c001d0b84176880c0150502c1e42e81c882003288d9000d0074040002a100c0c007003d0342e1281003d440440b01c01d03046200c0282412814540000804661103648002200300410b00700024803900203001d80303180340d0000303420407105000b660325030011407542880ea516000122002503611104451002a4810724280205020340c01100c4c3e4a42030410074000d0300c1c1070844a002c1c1c40c0200d014500d0a0701d001d04012107584901c0049802c80401d00501000150350301c0038500c038a010b01c00303040181c074191902074200f081c00b040462007501001a14054240e004802801688007a03c00000c0c00240c3d0915510b0540440e000700c200204100c00030007015816041041d040c00d0344012036880c010202e0820004a580d80140d94010b10f40044103961032a281d004841218080c0c0140c488040d2a0000720f4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 59975839 1250 59974589 59974591
    0x301031103010207050a21031116060b1c11031515010306090603080a1103040602030d020f040e070c170322060b04050a06050a0506030108031b120a030c080f06062203020603 76
    0xe100400e45401e01c0d040c0d81e2901211f0461014030745000c1243c0000f012180006000d10400801041c0c040300d00c0e0000c00c02180e220300c2004500410701820513544055811012000801c00c440b01d218144e22829242000103010882040c00a0f5400c840d64a420070041044243d15015041507280c43d400114401180b03e03400c0614001c1400c65034424000c4805400b10000441c101d1355076200304803c0144c55408000e4544020260101503901c10300d10444191902441d007040c004004504140300c0c250340c2101c9145061032258074501c840b0500404885011b01040301c10500c405070031004007044071a001c40c0258018071032040003806541100110301200c00458440c2d032525a240010f100c0d41c90043c071020010f21044683c6469503040400c0c940d100c1c003800d490000d09082400c0c078140c01c03c20600ca00321250011400341911040c829130024050a290040741c0003050075580840c0d0354031429135205105203400741c0300c5880c1c0100b45071044080044c0c00c040803100030a0130000300059a0f410011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 59977089 1250 59975839 59975843
    0x30f150603030e0405150f130204050301061502190506010b0304051c1115060a09051314060609090a030e211009020a0602060f060d1e03090306110705030301031103010207050a 77
    0x1018164102c9004d000889402030f1200c1c0001c0307490314031441c89540d0140c81054000054544240c0f80c4000d014490180c040d82e001103138154203065001c907180c01b140c0c2001c948949581d08031186110504912582031710f90500c00f4281c1d4100f80014000315000c00021034103c1d108200305d07440a40f10581c8204076a607141841000140f0b0003400550044040007640781884d15001410041d00705800010803480e2544510114143c854001803445610800701d0441c90360060300665800044001a90b1242400c0303413070314443c1d81003d01284a81c0c5000a0104100740e264885586110b0520104003249003242c1500382c074080c0907121030302c40d80781c2809880c000e003c450a020619002034410454091181d1f049041154440c1c0200425444081d015a07080b070b0043d00d50450030101800c00c40c2c040e90400c0848540440c1d0103c00d034080540c89040d031011240112800c200014282c2985025803050b2040540b0a40c400d20050010030121004214a000010001482c1441c0e83d52040e041043c10841 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 59978339 1250 59977089 59977097
    0x20f09040203100602070501030c1d040216060203010f09050105130e1c0207080609010c0f0f0207030b18060106050c030a030e0712030c031205010f090506040b33030f01030f15060303 80
    0x2040018036010072285015020908050112b09a003410090101e50140000004120700403640b103030070388650341190b80c100740908060102c01d0303103824a0b1020754802c0c8540550584a071340009260303411442030b581600c00c01001c15900c401044071135001740101119242c501d00803000801c904800041b0170806c0b010041d0040c001580c0340181d0507051042c018031501490341446291081e5981c884010b400b07882d07603404c0c00c0f0411615284100e10303005e0313103810040001d001c000a000710104612010115032030200202c0b12036030f880f100200e40c5409485070540c0680e00902940c4445c5029820074220120030104441000c2c0e5611540420760b0300c44042076012900000603a0f061542c0f00321440c0407411000c100b0b100030352600003d56040c0085216074489a036030ba00101d03010b40c0d0b441d00014079040740140340008101f212122804110151075082c0410404181d00c000320030341174001e1382d201e520210451581a8a56216a00d1a10f584c44d03003201e038540f1a059400030200c0500c550030186020307940b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 59979589 1250 59978339 59978371
    0x30b0a1701050a020703090e07020109080f0c0d1103040b07020d1e140105100e041a09011a09060a12030203041e030b0105030613030e150f070c0e040b0406020f09040203 74
    0x2400600311040a4480f10040340100320700000729410a5005040790841c860f414101e542c0c02c0c0c000c90051440e480c00404d03840e800901502c0114002c40a0300c0d1094140d81036a040c401042016511460500d00400030f40d00140420881803000f60041e02416002030401564a0703440e0f901c681740b5100b8903c0c0d070381001920720000002c0c070150791801007080e8074981c000c00460400418125522003584140c8842c039400300009010031400302c1e0407684d603010b600d180c601603040c030781145030203800d10301c41d000721003113451201510030300e07000b00310038001e00d0058600925207081000307044284403010810b03000c0d48420070000440f1050040401209209002807c0340c003801c600e0700c0070480906a00c072911035800841408028500a803d07000410750505190a0642c840d4020400585150402030301d030700c0d404a610007100d0a40801060780d24801d04901000940b43c5080d29885c8805640107414800400c0014000804d954028000489402145030070086034100140c01d0b81d008540303010758291075031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 59980839 1250 59979589 59979629
    0x1002120f06061e030a0b031608060c090a0b16050d030207020a0b04080303061905030f0304030b06060f0a0305040f080d090606060201020906090f150f030f060307050a05060307030b0a 80
    0x40c248a40001044a1242c03900e95005054603070036082d000301804004000022402c44d04003503010310040c0c000a029500c5440315013145c200720040e50701c1003041501503000040c0b10412181c080b0b80301c44400a1441154a05002c50500c25810010740d05a038220348801e403502042003088100075648180d41c0140c1d41c0d045a00c103004040c140d41e8040e941c1f04000740800e110141d0088250703603019200351101c01002c1c00ca504a58a681070b580d01c81601406502800d400c26600400284107403801010040b105403110740c01e00c00c0b40d110700c003901c025101e000e100000350309200c1d401c541e030018015220840070903050b0305c82404070392240540203802e0b82e440c00f1100c10808107025840c01841140000c6081821180200d2600d200d10f00c06644502080d4640d0b01847d0f4440500ac1c4c9079825550015860318031a048580060b402501d000d000c40196100044a503d4009a810160380c000f4100e40d09880c600030a214081d04081d21003000c1c151075a000c41c0c410f8071810308240c01040038461665614070701c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 59982089 1250 59980839 59980861
    0xf0d0c03090201050405010e0d020a151704050303040b100522050906040206030112051c0e0a08210306121c03140c0703080405160311010807020d170702100212 70
    0x2582564245801c0c00c0c400c40240c0e8204003901e00300c4200303090440d564138128000821615144500a40c000c1c3d0904000c1056806442c40c2c4102c013a55494030f200765007801d843c4040180f802c5600800b01c0c0c0c001c0000a00052016203881d42100d83c5c819010f89c542e840f1400151425141901e501d50000400640020700445004994211a0505c080d003054203058000c10b025100501030f99030362105400d0f8600401c4801c011401c1a0070348850111000d5040074001888080390360401743c4920780b000380100d1401c001040c221039058144900180040c414030420801c0c0d000206283c1d4000c80c610489232101c1030034803200700c0c07115590000b00881404000c01500b1502441c9a50402500705820450480c005030f04841040b501401c01041603aa0780c6000d901e400c001c5c2ea1480340100d13811100004000500c403006001c0c200c26280c4100554810008aa40d84c00c11042c800000d0600203000406080820481d900f080c40e6206885203410000920400d03680b05240382610f4030541003c00c403031400300b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 59983339 1250 59982089 59982101
    0x50f07050a08070b01060e010c02010302130b030a0605031c020d030504030c02060706050a05010803041d04051f051012020f0f0604151e0c08030703180b090a020306060a2105030d020f0d 81
    0x102c2c07c0c84011410440c000074143d604000000381810750000b000d8905402c561a0030004240c81103a0740d60b00d10302903c00802811080c4102030103481500a045a1003c0c20000c00183c450140e00824414a401c4000c80241c18058025030a102d0204980800343e19128000c2440b14002d14001c600c07810405030741e104585050788611181c0d002440180008010b840103000042803085401020b0f84560a05905001502c07000c1d2151039000c54002c0002c00482e04030903ca400c00c00001100c940d030320f5620600f42e0301d1040d0020340c020740401080285251851404c100841d002d4031a5040c103031101c40306c010007070001d8180e0b408564840200c500c00080222820052003107031524049051140e0b0f10141035005c09884030007419180c0c8a1841c800510400058805070045402035103401c041d5034142d12954184826400b0303000302c200003002800e0501100d001c96241a26107d61800f4a07201030941403010f400407201408108040382c0201c10600150180100224105984044a02540b821648 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 59984589 1250 59983339 59983349
    0xe061b0708030f04020a21031110020304050d08010506040501080109021b0d2c1f0302090d06060302040c09080c01030207050c030703060b031606051e090406030308061512010303050f07050a08070b01 87
    0x2240c4d01047c4100303c0040703410403540f6410705250400c450b013500418185100c1070446901c0e10310110400c0244500000c0c4080b0348040303603d40761020390700c0d071050295030300c203d00030b06000c1303841c460040202e03d550342e006005140c42800a612211110307900b241c1424003030500000000e54a42c124100b020215240403800d402021031003568184e120042210140c04400702c80958291500120000b4040e8048030b00c0e50b5001860000c08120910b00f401c001c1c6614001a400b96107084e041c44a0240600254000d8a0340c000090034041240702c01140a5403040204450b07a001c0c3d03070301510403a18100720707110155218203804100f0240420506290042c00704a0a0114503500300c1042069040411907502070785c0c0c2119a080c01e50180c9070f64103144100600c840d045440d101c000001d140c3c1c0812001d01900c012a11010300150035809058503008080c00e0340d00c6c07040303070703000420001e801400101103460507083d00ca0708140c0103803a003d08161100d0f07020303101d040c000a450003c2004d07001400703000d01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 59985839 1250 59984589 59984609
    0x3071a0603012306010507030207030b01090204090c0509130f0906020d0525050702040504020a0302060c1605040e030d02091507080415090602060f060406080708011508010e061b0708030f04020a 85
    0x45a4050f14107807250340500b0080c1482030014810003072502c2031251202650b00400040020750f07592100c040294403e10480000174a4030114a1140e8450f204450010000400101c1c160342c480350348400074440300e000061003680e00c80701c940010380f0500241c0071010034181c2c0003c0e18039000d100b10510b400e400b04008560821b00c0c40440c0f600390030106a801c1190140d4001502d5034a41c808078403030290540001c0d5001c1c8000c10403428019000031030086039000e40333400d5188030b0358400c18081030707a80500b4040f000d60024404c003103112029074080d1004010060040002480c046103040065102c000103a034441d000090510040b4000104004110f156244c0700c1c0f80c1c64a4413100948849002d8002c149182400300858400d44c4c403a0070800107403100c103042d54139660361880d0f103d000305901c01c4c2407491881c4042d0001001d81061040141c80f911074006851a0307559403150102c2e40740c2407218901c0c02e92040c042407011071501c1020b10b11801284929001e82d08107401008908400e9a00c010120 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 59987089 1250 59985839 59985881
    0xf03120201060e040b0615030a1d120403151b02030c010605060910030f0b03060108150901090b070f0215040f02010e120705060f040905040f021203030105061b03071a060301 76
    0x1c60fa800e4902507005400c50900411a00c6080c005000500c1c07031210601803038008410b004440030710703a00c000c0358503801040740350b55501145450f50316903603400840c401076030091004102180c203411601c1004040c0c40c00003c0d944410f04501c01d40d211010440e080140c0c0045000f40c40203100344207440181108480c080c0c02d0540b03110001d800301d402100d0590800d83c03144910102c040154010412041c0004c0c19105513603129264256902544110108502d03807070004030340104410311610418607040030781d08503a5510218143d07030340b000e000f0200c011480b40d90580d012610303070007040714000c078410704407203e417440a4000144003000c40301c3c542d44580480d800c0210b0b00000011403d0031540300380c55031a195003c103450070714036000f95400103004e1070401c010001044410010345a00c00d200311030140c5c81000032080c40e0343d04e020034028190000020445180d9100d0001144845e02003110101c0341b40000e2951782c68441a00d00c000c050b4a25410000d01c00146004c0c020035500303541d070050007020307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 59988339 1250 59987089 59987099
    0xa060e0c030408040b0f0d050103080918040c0504090c0e01030501061517070f0c0606090c0201110406090e2d1503030f03010512030c0604080702030c0a050108040318050a0f0312020106 81
    0x150702c200c1c0700d501c1c0d410000081e00c8040182c044103547c0c550000207000c009940e0740781008800307540040c00702840b44660008005444202c1503986009942103900111940d05150511008000b812820385603108200b1000510070b0f8015100c41c00707184136100100301c0601e0651000710103001600b2803000c2c17140b03800ca44061400002c0b00c003039100085203001c0c01c1000c84040c00340d400304642000500900d040c40004160103c0c150000c4084d04a41d070300800400f01800c030023200a02030780c0074081c00540c000b4170400002403403045503500180f10001c581401c007002813009250b0604009400040f42c40380080001044610201185901d800c1d00558601102940d00c3c04041c80b05015507803094000501c0c01c2c8900c0c1c4104140c85850180f60125801e0341840d0400c90025001520124440d100706e400d68545820041954011a041a103030b07000c8507180c1d55001e0b61035941503881c54a060008100c00500d1755680c0652000501c1004846400d843c2142400381d00880540d00c03d80544e8104542005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 59989589 1250 59988339 59988353
    0xb211212070f090b070f260307050c010f0f1a04020c0316060e0102041206050603010605010e0409030e041a09010b09220e06040c05030c10121a03060a060e0c0304 71
    0x161000d5545081d10781402c00034801c0e51403100e10380064690380c101240300800c0100d07850300144c90038021980300d01c400c010405660340603200c0d0090700740c802034240041403070f960250b0090503281c5034800021511042e14001901100c01c0c014020350081e40700c20200d00207005e20203010340140c40540d801c0d0710f042d5100d10b0007556413188102c0c0c41e0041d8a418030a80a011595200d600320a0109000b9551507654000110304240340d40b82c2601d00e540390101055507445c0500c00c8400700c3d903041e101d149007c00c40104200c01042c0d00c0009038103000740810b18040c81e6980b1f1260f0075003a03100d0070b640011000d601040c00500101604401030308401004011050740e1807801e80e004a40d5800080c98416940006550241c207002161b9480761290300b061008026040e0043c00a80d00c040d402c80c0c4420803541c003000720018801c51102c021401c0305035650002181ca4000e01c2c0c2e40840c0d0101c80c4271405091000c04d103040000c40f036007081c80303646030801e115510664005039000780c0d0b81c1200b0b07801c0d810103448844c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 59990839 1250 59989589 59989591
    0x30d090f0317151e06030109060f060302070b060103110d1b0f1b02060a0909020a080a0b09070f08090a020904060209030712031e120203090a031202042103030b211212 73
    0x381324054040d40650004440090f031111207a000d0110b9031656960081900648083d000d0000c914801d1440454000d21074401d6400664000d042d88845445000040d0000e1000040c4480760300c904101008030340020b1300450b9100f944115482c1c41001c244040200495400c109010401c40c403d101e50200c1d50301441c07060003468045507490f0b42c0e40c2c0e001c3c83c181c2c1d180c1c1450740701c0540b260020400b4403105811000d040d1092a000c1c0f03080c02a48030000c100711041c40c04071100340200f15141c0705d07c0403043c820a11141d00c00650700407a40c40325000c0c0c002502c42442114200c581c2c60b0002080704041c24203020042c000c05043e00710805065655030301800d103444244600e160605039030046c482040c403d4104c0200120f03681d004560f43d0074140d0714140c0701c600c012400d07400708210020230a840c1c90f80740300b00c4080750000091050b000301c0da06010000d201001d0400d804144e2030b2140114a41d88920002c4070501c2d510000403050000d01c900349061890040440700350000a100c540c1700d010b8191011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 59992089 1250 59990839 59990881
    0x190303080601051309020a1b0302060907090203070f08040201091e03020f0f0303180301020d090b0402030106080d120b0f09130c0b160809120304060302070c0e04110111030d090f0317 80
    0xd6107c1402040454040b0305885890000b81c0c1c4940f004014140c000c50710a01608170a01940c0702075849040070000e900c02505c0d0780c00041c040405811a69204035880313a0090700c140f40c00d0080c0369540340c034a1503007508190041c7e501c028006040046151091a90581c0501551810810400000045e8503170150540c0103050b2520440040125a020f50440b843c400300305408100c1d500283c204012766000c200d070220301035840c017000800d41050006c0c42c0940d001c4595294000c80c180c41d81004007803c0c00366141038000a14000d4040195941c41c5421711804140d003408400b207000c8d003000c0100002541c8111541c0f030007082100d402d0360340f5040c0030042603041500d23140d840314071402240300150b45004c295005d02010901288056050b001090580d00600340451819141c03044003903449010340d001082002e5041002d0301d43d50080c460b00d5451428081a282008110090301013512000c030000c46003c24007444d24410507402c41c150702d1185400145d80c40b02440e101c8a001000b8507042c0c41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 59993339 1250 59992089 59992091
    0x4030f0314030a0c02011503020307150c140a03140702060d020c030702040f0506040b090f01170f0d05070c080d0c0605060604050607080306030618030d020a0905190303080601051309 80
    0x204014540900003541da20201e048480340d9a242c07030580310000f800b940d00c01000550030024460080304030100c0c14002d0b40e4000340a48842c0d072420440584130307004034040d80f0603c4154002c0e00c0104502040d08000c40000303c001d044120358914008142051074042c03410262024080070000d6101c460a5645030002c1c0240140d40b14001c1c4045d91440c000c40e00029072050074560140d4034925160482c07030145ca41945c00384000c849010412525060840f14181e8114100004008804144000c801604400c0e406e071103140011005441c20002d04120740000f141000654404201507481403100400c1c43c4005002421041d0388024040c00072036801404903601d0b003010030f029555905c111802801d00030b003200d584e0340300b07490303c103003640c2044031002d12034040d0310001a01c0c0305004801c0151710705007401461900400c0f0308030340020f400002c0f428082010030107000c41c5984410000d09179140c2c0010007000060f1440c0f030300814020000700514104407051101395000c12038441010240d9001c010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 59994589 1250 59993339 59993363
    0x405030d050411030d0207090f0e060a02070602090a0303020c01020d0f02030304030e01050c0703210c0503070b07140705100b040e0d030906151e0e0601090509040f120f0201060f0b0403 81
    0x20910784460b00031003c568140650801e1072259600080e141c012122000824098032032020045801c903078024059014540141d40010305040c016801803010a10039100182468013640101d461400ca03508220f0140e80100c50480066804001e5a554148070745405000b580c2d585100030b4a03400301620080c18050f000084500c2d41c1e0003402900c800d407104001322140d8950b20305000c2c0040410315002c0c0c414210820042c10854801c0d40f500c3c556640040085203045035503912412021401071002d010405c86043c200d41c4c03150302074014524039002c0c40c010310882410000d81d000325089074084134480c078903007503414110b4407022501065012990a0000f2403a50906246014142004544103aa20b010f10013052800040c8410200c0240c21039102440396201c0c03d0400004100303a03003039030215480f20713010030003403500e00e200d0343c0d005128100085100580b5a910321145e81c445503900082401c1540304403044c1d909224400041900c51000401c0380d10f040b80c118914403443c0405891020700750 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 59995839 1250 59994589 59994593
    0x90f011103061e011202160c08070506040608041a13020913020a050d030306050901060504080d02011107080d0e0d0e040c05090904060b1504030302010f1107020a05062209050609010506030405030d0504 88
    0x1605d4004c0821032407029580d4048039004580151030b954001c07103803801e5060010408242c00900710050b038001030403a43c40c2a081640a41e100c6800620031580b911030440c0592040c070b029a00700317004104e0701d101c00705240c00e42d204219425800030001010340804503840790140c1e4030140343d00300300c641c259000c0400e1082824100c0103006150043d5800c0076040000050031a03004005008407207581082d1521900038102c12400d851a010603448142014090807010903100e100a100091455500003100710700e145085042140c110058004508180025104c80c1441d01401d030004000d858541c2c80d014244000998080010300060301c9240e5580b0700742c5071900e03910050300e00d40c0c1c0540c8460b03442c0d940d6444c00a003e00201e081440f901c0b801c11128681c40040340040c0d4100550040107407421a0901042c4681c5810451032480000314002e0000343d2402401c00c02c8002e000700c0213020846140c00000c0c85480001a8071203401000c042080102240010007030b192600c1c11201c01243d90385441c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 59997089 1250 59995839 59995847
    0x1050112060806040b0603060f250912060b0307080102040602150406060302090c0403030909060506070f05070504060906090e0606060720040501090c0f0e010f03090c030506090f011103061e01 84
    0x764004048510560042c00103004024014034452035044007120841d030f07158150158001e4068444e00801c1303030440c4400702e410b080011005813103035070303071078040c07401c580d1200400e0032440948002d4526550741c103401e440b9030a052000c54050a6040000c1d4607251520f40002d40e038540d007003160750302e1a102c10003107001c01005e81c00400c001d58001f40b1514240c20b02d40b00d4605164410700c0b085010034619900010700d0020782c05840f044810081c0068100095511940280c5902d41800c8460b40034581e4049502d03516881010301410600c1030005802d802c002c529400c5900d0544511416402001040a903513944401c48160641c00080d2100407460b41c122609100500030150368024141000401c2e0700180790b000204804c910b82c1d50003200c00303540780190f40089845070458002090215038400c40744c002d40200b540b0320700c50a041f015485d80ca40768070b03041c803005030380e46651a04804e0160b20a0842400740c044c9801c40130b05000c4c41c43c1000c00000c0d0035158a400302e0502c0f08100c10780343e10786a0007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 59998339 1250 59997089 59997101
    0x7030819020f030a0606020604081603020709050108010204080c0303040b07080f0405090a05090606010e031b060c100203041a0907050103050408090a0e010510090b0412020a03060c02010203100e0f01050112 90
    0x350300290349a100c001d42000c920341040320103d0300325185c82000108140300044c034030702650304014224a080d2040403082c1d0080101c410981c1507120354071000a09015601c03400d8001e1205600044c0c5642c02c2440385400e003031110b0f00f140c0c4a80d1007400180f02208a00d02210f4501e584101c1c856643c81400350a86460700581e80600da001c0d80e00c600700b29610603603400652180c1020800d42c0c009558050044d1001c42c1503230750301030b0103901c1422920208001e19008c0c000b0b030750300201043c0c100181021003a140c406d070365030000b00c519004000c2c0010441c4041c6102e003900701d07044040e000ca00d07003240308aa80302585d10a40b810903480300c0210301404403000c1100c5201c0e0010f8800d141c0603440da0351903e044d520078401c03180180b016450342c030000751140e004407007681d04c0c11060714035040c90f0000044041c40e40e2070099901143c528400800240340d0700c501c580b59030080e0005600c0b8a004114403551210326404030780c0050300503081000c5299000c840d241501c1c2d0900f01301e118401200811801018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 59999589 1250 59998339 59998381
    0xf0102071203050d2304080306040605030709090c05010206010602030708030a02120412120213050d081204031707030b0102150c04180f0b030a122303010905040312060506070308 78
    0x81d00c1d80205040c1e104000f4881110440c3c0144010554a0a501140c103d400070343c0b0b0030480e0f61000300700040c0c061001150450001030000c50344a4640d80068201000742c4d108140b843d80d51440c0f4400c1000b03001400c1c00400e001d00140500350302d04a406910303442120001000c01c0d8000000078448500c039416a050250000c80004040c0341c14941188003603400c003140c2001c1401d00030300d038070045554000c550812070404001b038100c0e0314100a0000c3c80303031040f004544842c824010902d0b9016158080d034030582c0281c2e0703540d0182a000210300036011014145030704040c28240c209a50740d0300003079278000d000b400b07407880d51050751500c880408a0080741c0150001c1071012a51ba1420401e5401801c0000c1015004001d003486003810180d54015424005141e0001c1140d190702c21805034000c15500b140a2030041e04072401007a002d0aa94000d030082082a581c88080c80207041d40103850701044003105408012450611002640c2401010301c02402c00609000040e040d01c03801c803403214500e0f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 60000839 1250 59999589 59999609
    0x30714030d0c030b031002160f020307030204110a11060f2403010e070f05060c120a02010b0901270905060a0209010c0501060305010507140f0301060c0201020c03060f07030c18050f010207 82
    0xb1081800c02409042161007903442482900c0310311102203280e100700d800300644c0d00c20560030b003030301e5a4515806800540d01660303d03025400b00040961201e01441203040e09981d24240c2c0c0f0404200040d0550303040e0796010300950f01000c100041c0f49039401d0b420382c201c032002c90b10308403400d9540c17000d2480f24040200319401d9400c0807294140381c440002c2500c269450b0800300844a0385420910404d40148400c00880740d00003441d04805150300c03402407217081c030f0a04c0041090318088010540d2a0307400e038414028005105000d1040d020b000ca400001e000d1116014002d1243d15140e40781d40b40c4e0003400364442603a002928011130b0f80501400300140e54858003d01207241d0b00c0c20514002d000444801d00414802d03901e801042804000b00e518966540341c10342d09590801808580448007044200c0c154030510000c400035650800419224410704064800949090100201500d44115155040c06181c5c652540d014501040130400d0302d4003500c001e00004031030f4004070718001e007c2e4049800c3d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 60002089 1250 60000839 60000851
    0x60304060b032d010207020d0b1003140606090a091a060d0218070206100b07170409020304050109050f010c0801150c080d02070c1a0702091801020a080f0117030714030d 74
    0x40000318185030480c2011210f815203c940044060a034030400d43c0c000c2d884402101c246001948513141036808c8a5888051032245440b80c0e556801c0d10f8205445e510250302140401c001c40c0391814000d5806032302800e06110003540c2c0d41d501c40c0c038084081c9046960010b03100001e2495110f68044030403043d001032013a603807103420400c0e014040400f1b44403c030042c0110000255020b81444041046071001500301d454240152a141d403d00034104120b880e0010801002402d0f652a001442c0554001d46c0001904145498101d00e0441003129203692a410002e843c0c41d041d401c803c00a045907903010a0008034a08072000b1150704032001002460400007050681030a402d59001d42001c52154040840007525081c0d40240c41d6101544420700b03400800021005007068070b03e00340c00407070603601032415052080d5050b00b644c012030409c40004c1d0400e02000402445102c0d2103004005110400200c1c4180240807031b12446402c1e00a49200d00701c441c0c042c05080b0810490b4a6120348801c10490 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 60003339 1250 60002089 60002113
    0x130e1c0305011505030103080a11070308071a0105090903090d05010e01020a1d06130b0a030e030a020a02090a11070f0c030501050708010303022a0f03070f09090b01060518060304060b03 81
    0x500382030140c1c603000c83c10410200c1c000c501400480e070603a030700a00c1180c28a06152402c90310ba40301c1c18800c1005000724140000041d1500e4040c06025100390a0031603a0111132000f0b05c00d090051f4480e83c41140c4007414030841500210403a141d2020544107508004114140706015180308401418030b90702c001341854031b080d40800b50000c4412850347d403006401c00c01042110500a4a040d4a2035020f1a07504003c0760380140b008062201060070081040d082ca400ca4034250340044914401507000043d020046240460081740d10455100c1d00700700b407003039000c2011094054844010000450048540301b0301240107408002903500c00000c0c06540303040100100700e440207200c1100035218011240203500f049072981c000c1800c0d10201138071010040c0b02041404000698920b415020b0381101003a0703000070004c1c0c1c2000e4030444202160741c5a00d454000b011140c140d200c4070400105000581900701002154543d070801101c44540702e03200c505088004002c1c00300002c1d4944214034445031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 60004589 1250 60003339 60003341
    0x210030c0302040e1015050901120c0c0b07051b010204120f0312060306020d0b0906030a0b0c0706020d020918070f05072d0b0108070506031902120a1401050a05130e1c03 74
    0xa03611015440d2140038406c150580b61401240310702404160030703100d8001000340c680d1110341d88004d58600050313119007a4840c5000101e040e41c04030002000003a000442d0360384044d85240d107031031316002140740c5450000058242c08401500816440301c09040809061086500d9412050044010800550340b450024029801804c20b0389055040410842503460121001d500c1a00090054206918aa41d8840c24100700402c50034188001307004c4030000c00c14a1015000c5c0f1450103c1c0103030307642c02c41c0c0100440600780c21003480607001130b502000b8036240c1c0302f59041c10340a4a07041c201d440314000c1c54614540701d9180d008040303524040000d0010500c40c0445c412180307020b044000301c9030f6211941e440c1c680f8194042c880e001001080030841c80c0e545100301d8902070725500801424510959904840010191a48240c45840300c003800e4950303c0c1906424018003040340c42100c0241b5200c0403d81d03440b070702300025055541c4c6442800c42e0030814881e560300c105400c490f16003030058140002d8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 60005839 1250 60004589 60004621
    0xc03071712040302100309020102010f14091203070909090503070210020115050603070509060304051c02030a02010c030612060207171c06090612080c0715031d07030210030c0302040e 80
    0x24500c1401c1100075010285000c0300c0640c0d401400314106400c2030744042d000781a01e030304220b04640d62000d00c0b092403049449102d000354102c400e101c444c0d040c858800b500d4012110034000b0300c00d20820a002c0c031140c0029011040756240c02e80840c90003400d090960460040c0d04020750412064003078600c0f425819403081400b000090fa8160300c840d01c840074800103010444034680858070070040d15002e85071500286601a200300d0898500942900e081c40300413180e023111402507440450311031007254081c000d08078001d03003d250400c0385034508040401541401c003800740c030050380040d5240601c10900b440c03c100008400e2a40d42c2c1d030340841d405c42414031030700380700c000b102c2d140c104003251429842c000c00e011118400e21110f0b108c002611074500540c4500c42e0740701c2a2050b000009505003400c010b48240308190340300018130749500500e001d5484541d003401d088a070418142440140c1d14070141d0230581c2040d241c00110301925400c02c1d4001d1089801c21001260000308000400318040005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 60007089 1250 60005839 60005879
    0x190504020f0901110708210f04080105040b0a091e030201090b090d030b01020a05060604020c0a05010c0f09080c01020a030807051314010f05030f0c0306040f0c09031b05030307140c0307 81
    0x541c481031074115120303845d000e560140c00a07a400a030860b580c0400c01998500d2035282004a480c608a2a6040206194426031040750030365111000c0005200c042900039500c80740b0b00c102800b2002c256a01c1c01c02c0131041c5076945070202d510004603c2132501c01d43c048441c0300d5205401000c14100982501c0e584c4e46200e40b4040000d09110005006510104458441d664480010011911190704000283d0482c03202d860381c601c544c103114404075100340280c2000710900e8031005003101c8100b500401810703698210310384540c888a06568981d0f03000401d4042c0a1f01342c9014106919070710301c1261a403080c11100403529841080210342d0440100354590038403809d0301c0e1030144241e44003040d16940002c0764524826050000001d045041c2e82e001554403002c0244001030f0a5050000a02140c0b115446000040c904120074400c10042c4503200551f1651085185d20841c07410b40040da5a21600341c00400b1036400c000211000c0808018040100c00002c2c152100c00b03031288200c503801c00b010740b48 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 60008339 1250 60007089 60007097
    0x60703110d020a030e061003050c0f03010b0d08040306060e04020d020f040204050a0e0105030d092106090803010311040e0309060d0f0e06070c0c0e060f011110020c03041a03090c190504020f0901 85
    0x420142c480da501e0301c102300c950203c054045d940d0260204061200c1c01e400c040e8055484001d9058184d480e12110000039101d910900e440da0b00b9030070070708216038194100c83e5940310200188000340c1e441c002d0209681e07a0454200819005100118000e0700484d8000e680003d00c281021900104819800d0f050b07410650841d034122402117000c0b80d105034184607140b00c561074940e1150310340c4485101d2026442c040d0502243c110096680c002a55000364400c0d116000310380703010107851030710b8041c6071041808040214140341820380007440c54440c1401301c2c504d0658070880b8000181407900301d8000c1c0880307141503607a140343c080700203490003141040440713500301382c1031004c81c0700f03103070314050900034a8054201d8611248103001541c2c91005070450000d9403007070030450034070451a0700040101c0b04514021b1602c5524041c0015800c1411000098081906004111490070000764544c080802181c0412020344401c0b003107a040001350300318541081c00040e031260f842140c2401040280c0081c1d80e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 60009589 1250 60008339 60008341
    0x9050f040e10060915120b0a0204080d091401020c010e010c020f0d0f0b010909030806040f0f0e07151b0602090a03050d05031605090109060302030604020904060e04050606060c060703110d020a030e06 87
    0xc01a08883c016014400d0f920280f00c501c06e021175400daa032158040e09107000107207460345881c1c0c4540382542c061f4510000424407141800350b01e0030340d441815078000c00e0004081038803078400040d019081e0410042d0400c4140a080d20541d03507052480803c014010b00740a41c107000d5428217a0301c3e8240303101d0039135101d010769000081803c6d0070303c43c8040e819010307510014540c5420013040b02a010b003141e0207290303a46582e40d10442030341c03620400a80380c010704010591545010031411028503d0020f61080c0170002c40004408130086880c0c101499200d5401669100c2c1c000c0000c0340d880950308003508520561442d2401e00380c00c00002c600811788049030345100145802c1c129103034031070300220500203140420100a454000d4025582000340200302504000d000c0740410100e03500760b84801c031742d00209424401444000d200280c2c216100791410784c80c11810000f81d641e200e50180481c02016914002904403406940545120910241080d9034807644402c00402418091034028500d00a01c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 60010839 1250 60009589 60009611
    0x70206040803072102030306060f12090d08010f0b070206070f0b070503102106050621070311030712120311071103100203060a0e06060909090d120c09050f040e100609 73
    0x90084000c3c1130703580d00962565030b079a42805001d8229064190800c5000d0192020440b00c0701d01c802d110740300410062000320400074000300303500010307400300c0c080f46040c450038040e024501c4100c03516a0703015500d1541e29446407600b10f07a0244400c030302803c0c501448042c0310a41341e20a0085010b03011118001c150030340c41d8001c0100e00180402e401c0c82032140301150300c0020740d080c0c00c111340c003450051075924084861075224103605240c6101c81e48542100106000f08080c490713070f107090500300364014140c00f81000c050f00c1e040c4402c150f01030608161031003000c44c0140f080c1c2001411aa4141020f034440f001e526151002e402c801c000d45120317001d4103180d203d50b02840d100703491207524010702c1045108c5c80c280002440c040050304e540e030860002c02c4400000c2e11106101400360300702c3d400800c1e515002a00040403070b8000c0d142c5402c1c0307a080101c0c140420b603010300000151442112400c000c64032190001e001004d445040c803625015032140c07401070400d0f95018900300e4180308014064a0301103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 60012089 1250 60010839 60010883
    0x50702071703120a0506040f02030705090909070605040339140409240e010507020f060c030103020a2709031805010318240203090718020703121107020604080307 71
    0xe00c00f6401031070341c6400a04121015000503800260140c030004410f000ca17080b0505070b030b004039017000c04140002100703000750030404001a402050a8044c01266003840300c02041d5106074880034003c40901c0030700c0782071941008803503050900a0b9640f190703501d1019130301803030f109418800c1d10000b0f000e14098103040d09140c0110b4019036802a01c540baa80000700410b0401c0e401c00d9500c1e80716513a200c807286a8040c1c00d119245c01983c080d00242811402411802d10b4040010900da40080341400100016210390095400b918040b1211075035464040380c0e059401211400280504d60401e401c150500d500650300341c034005950025900700945600c0198280c5800600740180c1c00060141c01000c91882510040d8000e42d4a1091000c241e030f03100904140e80042c0c5914159400c841001c02c1007081082c24180b01c540c001e681075040090b01c0d207025000c0007040c09000601501c500304c40b030f1148100011548400c0d80205844d4a0390b441d07a480c1d40d52034002400488400c0f9002220520385644 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 60013339 1250 60012089 60012097
    0xf2206030e030c0705040c02010b0303031008060121020607021807110c0109030309120201140409020d050604050f0720070b0d06050103110d090309030606090203040308060a050f061309050702071703 87
    0x40c0c3e0004001079450181030000030080300e00110115561881032408954045c001103002e2041005da002c00c280c1420700d41c0c0d040020603801241a2072020038069261080100b466100c1e9404451881c0c440d111030011582c1880f4980c0c6540f803031490340c01088201d50300700814203a581c1500040b12504d00440c1d0055880340700901025000c20021a41008901061f00440340b181f841032401c0524640341410404958205070400020b40741c003c9120001a43d4900c212940420200c60610450410321210841c101002e0004030400c0020890390509443d41000c41c200302101c0012509210307550001940903420094810f06680e080c2000040d456110340240c80142d10b42c09032031407900b4800c03402c0704000c04002900f141807004c0020004003203010f0340f003044010188001c0150b074a2400303250060054030000c207030f0b84c4a404402c8060115844500100c0d003060001c1d50181d1391a0038542d00707a503034806150720a580044c105003c00000741d501080c0041100e02d030306400c0e14118894020b803626070103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 60014589 1250 60013339 60013357
    0x20a031d030f2101060504080d030908120901060308030901020a0e0a030308071d040213080c04090c060e03010f0f380609060d050403020d1103041503020f2206030e03 73
    0x10081c004000c2404001c0c0003807840c2c0742443e040150310340020200c40b00c542000d134020004030b100842c04001065091144002844c03482c80c04010350b03116961143e940780111450501482010800900c501c0001d41c040b070080c2d40c0140302c0544a00d40717420903c1c00707076112422513000249800b04866803410085000401c0e6a4140c03119441d641d2070390380848803281c04032840c9035941d0400081c0440385c1c8651000708000754420180380720351340c1000d0101d40751a100318022802031389001d405c0400308401d41118800d0781c5481c90b1030310010400d1800280905004468800802c0c0f81a2031000389101c035070302106241903a04d00c09281c3c45200451006806040c840103024401d40c40c000350f250385040b10040003d40300050120b0300344500b08003890200c1e1704c11981140035034800740800d07810395000f24410b01050400402185070a0130320403640c0c080c0302440f000d002030680225a0410112010042c0c0d91a000b030b8140a0b801c420204601c858800e49903c1200c02003890080341d000c126002104640540b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 60015839 1250 60014589 60014593
    0xf0601031203020c07170a030905030307030f030f02210402010207051f0c0206040801090506060a15021002071106031006080705030402030606010c022d0a05010305130602030c0913020a031d 83
    0x440101c000350040d5000b840b8080f02401865000b003035142601000a0111404000415145103a450058010045908094030990061101c0c00c0025400a0790290a2010b45804102c1c11804110340d00603010340340303880781c000c84100c85a44c06003040f09416031056000345e0840d12840d42d00c105000441c6134441d00ca034610346480e00c1c3c0310246030085402c613100c244068103451909594280785421a0800d100403121504070f002404002e142074011100544601c51810306110b0006201075540c024140444840680101d5210103000116551001c1c1c03000c0078019a54a01d8080c560341b039240000d00444001c03c05450206500c02c2c440e4094070b11680d8084d00810040d1207032401912504220a01245e004a416400b440f0b0700380c141940c581304417814280700340349a03c100e04011607420f40381c0005041502e000108100d54880e030050034071054001200507500e072111440b406e00740c400c004001d508200118540c800000b5958000e04e04480142d5041216092a04112602c103103020b040110381c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 60017089 1250 60015839 60015863
    0x10b090109030807030207031a0402120c0307090e01180309090f0204140d051002130f0b032502030d110702130c090504020921070602210a140706090606080f060103 72
    0x4807803d000345440c44c000d0044880c620303681c1d0350302c03100b201c2965075000b040110704091104508141d01d01044140b40031018000e081e80d100f0120369a07103a0b0780f148d24080c5407620f035008400c18007135200e80d030b43d404070420050f4099424240905000d070680301e012003192070b181810040755060b05c269010b44541c0040015045c80d0710040120074540302070191014058081d20020304441440103164071400c1005600d0003030728011462001c24050383c0201780186040040024a00c120b20305441038a0043c10304c0c610300902d81808078518002c85c61800303420b500d442d200522a051082c090030000303200b16684e20000c0c0071040a81c0696510519150102d5030280040c01180390640280440038005412084c403610040340d1704012000d0442d401007545c020883c1070050a5040c00a5903c42c1c3c203140190074185100c264000a41c450885424204404441480403202100c0d0032101240c0c1c01c411b05101c00345003030510000800c4940703c0e0403c1449120044002d0000210b5010304807a003150002c145 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 60018339 1250 60017089 60017093
    0x10f180e070f030c0c0b04020f0a0801051012080301120503040f0308030a050601020d0e100c020402030a0504030e010807020c060a0306080105070807021c08040209100e0f1014030d030903110307050a0b010b09010903 94
    0x6c0c840c0041c00803a4410360388100003d040d218012054000c010182c0040740d142807030b00907203407000c1c1107400c00000c0b4003940f2007160109508200302c0341152038042d200403008a4a062a0f800c501803500b22000b101003094000052041c004055402041f45c207c0400c0305450360001a030b6074000300c1201901064007082c228125107081da003a64810b901d82e08004d1220103483d4005000c0740c2c421141000c03990703034038800d12003410303403006014003a241c00b801d141403141042d0b0b6001c2d64880448052a00c907101c0040d908081d5446500520000c2992100074403890605810203805044c0c02c550030030041c800d281c0c1c420810900065009031056140d100d50006482d80e0302440480d800082ca6801030110baa440000c08020312504a4440c2e1003050f100940382c1001998400901c0c0103900030b04404420a56181142c0d501141e10a030840403030400150302c03c82c624007070303031250020381316030840313010220350722003400804a590170419214a031075a101d6038072589501036500440071440d000890301101800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 60019589 1250 60018339 60018353
    0x5060c0604050d0519080c041802030910020f030a020d0b0402041401080702071d0a0207050d020304030c0e0f06120f07060c06141b0c010207020904030905100804020f010f180e070f030c0c 82
    0x3801ca03007001c509501d400d44803022604d27001866801800c1c955070000c104246480180152003c80360f04040a40c9070240303500e0707042e2203400702804807089242c1c001034805511643d07501c5a003081d00054001c0d515140d4544080303606890140c4100d0120348501c00088400c0d1002c200c240c00c2c0c0350003c100d00449061003020b6010036800801c15078200b07500f0440100480c0080001041c0703076289600039030740d40d8214a0031200c03000056006414a0f8101018802d190f100e55201030f5201101b5207601c51441d14100c0400e2902480c1218200350b070180305008107206510600c0714900c01d020b60808c2c002c100c20228401010340303045541001c1e1003840c1080b0f00108148100401d460120714001500700102d58000940880e82a10704801103054000100b103a82440745802030507986509005640d85055004640c0c1c80300b040c42c201d410014002c5100448502500300881041101160440300503201c0e0401d41c9090f00a0360f050010401903c400c20b03c252003402101803004c9a07960380b14104005a803628 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 60020839 1250 60019589 60019591
    0x7120504080d0c0c0819090807051003180221010b010203071a0601050c0304060c1103012903030c03220e150103020a210609050a09030c0803060a05060c0604050d051908 74
    0x130000921811004581c01d003001d03261610740102111082d81b94450003a18030400b13640054081d800007003082000707664191075030a403070740b15040c045040071406020f0035004458582c004c0d88021004031240400710f0019038514810540e000030440e14403524010390b0741c0d0180d400000e1400c40d41c02e01c2805200c50004682f9008401030408600b0706400da9206415508540c10100000d241c2401500501580101413004403200350000c2120307804900e0256007001080846010b12042100001d40b952010401c8446d0582d485094944035401e803542c0130250301e6242c0c0c03103005800b62a02e000c5541d035011f905050007020003911881c444840180154041e4000c190140c0900c400c005a03c111001a01c00e08040300d000d11200280031810190a00101c44000d03082021451030104823000080d00030100384581c40d0010303100f03074803592a0b40c0015110030458104070303000740b0007051803a28264001000c90180b44110281d4400d09520202200e1074010054282d0001c943c03044626001806a8401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 60022089 1250 60020839 60020861
    0xc05030418230402031e150601090f030507032109060804060213030308160503010503031602030c030102070b01030c1a180d0b1608010b0306010c140102041d07120504080d 75
    0x101e120540030311200c140b901d810800d041e414010108100845c03405011030820130541c10048551002020126170740c4016940c40046400300300e40105da1603a0284035110000c0c00072240181755540c90342340064981e0303000e20007200c402010402c051071401e90350b40383316008925a038403918841e00e4000d0884900c14080c0041c0c90480d42000741d5010042148181c13406140a611041c1e0f0a091100640349200300300715070001002401d00042c07280ea54044105c03000c81d184800b8140c0784511600000782407000c03020105a15610000c0d01d80e08018481341c146040f00e0081d40911802547e0380d82009005c4020038480d040c290007044414019030020f41303020350040d4050803074402c080030b69a610040d40e8090f00c0015500e15807003500030300242e000401902411194040702d0860800341c3c00130700286c0c40140020b10120030703441440d1201a00b58140d80c02084ca603000c010900c0c0d509402d2218030107080d00c141002850310400341c2c8403040d160003002e001d00d80c01070509203025101c001c041c00400003007400d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 60023339 1250 60022089 60022091
    0x41202130e010c0e010206180606060c0304180914030703080106110114011e05030a0f061d060103030c03170f0f0601050403060f0e0d170a0506010302220501030c0c05030418 76
    0x1020280c0400d220301c800d190f0300c43e01d40e0441c225101c00060f24041d40105181c42c5101c0c1503c10416648021401c9904070307100f40d820a44074640d0200650450080e5048046554410000d03020307105019080215003902518807284600c4d404801e00d501c80c072503940003401207007000004000c00380c0324101e02151203c8200002418014103644880f042c0d50070f9122405108c400020b10f0040080c810316203004000480c02800c501456544441c07280c1d10302040541300302d42c0c4029107a01d1008480c180e100f075040040c00e894803503860340760150503015041000c2e00020f04188500340c02c000f860b001180610481c4507803c02c40c1c1c1d030f500c8224a00d10001040c26040180c14080000001c48038040d0302c91400c452880420400507004241e0301c1c103c50b00415604000203000100405c0703001c40d0807907400c081480f501084a07921040107a0203071007850350a4070000d01800903442c152900c0303980e42c0d0540f0402d82c0d06000d0680b21b580111030340135681c0405000d94108100410406c0c14502c0c2c40100ca04003880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 60024589 1250 60023339 60023351
    0x1e010e040312050703050612070f26060c040608100b27031605030c060901140a03140f1f050102070e0a0b0402040f03061b0e010815040f0b010801080304120213 70
    0x1c4003200f900c20984207600404c1c1c8900a009086c5882c0c0b2080b03030b81b50001001000c409103800c7c400980c014261046024411801604103504541034000950060683c401c0b101103040c09444218154010321440000800300c0f0003103010000c0c080f044c00121425100342ca070819040001d0380015511b2882003004841c0d03034400f074005644091100040c03810010416000e454900700a05040a22200700350744190401c001e4294281c0c0c200e0070a00c0d000c83e00a00f003e80300c0803d84001e40080441112403060002d101c0d04000004d541205a10300c0707071042284941d00d038503e00c84201c1c00005540115405604000305c14010f0100240019920108210f00440c0320000301001c41c08a0384503401141d1810340d1294144240519801a00c1107501025152028000c485030000c00c15058201c08074100251000400c00602c080c881081e04503e008000b00305180100c0d00c2a001030030b80b070764400e011032a03110000802e044044280d030b0440e85e41201c001e811922540c20000e00c4407100075005080355440e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 60025839 1250 60024589 60024617
    0x30f11010e010c020c120105010602032502031903030c080402030705040f110d0e070605030705190c020306070207090b010801080303040602030c1b0a06240b0a0201020714151e010e0403 81
    0x102620404a0044d005000c0181c0c003001444000040f8444d089116070400e001004556400401c032903080c2190440400d0310704c0725401c0d05024490f0780c040130b541807088400a540038180b591038101c4442c0b1a071000c11400c0106502502c0e08141114080d41c950003045007086107040030307000b90940103071803040016100803c242c000a50b0b081000e002d0021580d43c0c1c4000c42021007040850042c00c0c083c141a0306615002ca0018018482d0b503c125030720319071500507038200c3c50040c582c0e030a45030340c0141070720310a00d01100e0013960341c0d4252040000d4a810200344118030350088455506a4010101a515564543c1c66a030084e600140c40400b20785401c1012000400c0b011a034644624981d102400e1200407070f0426000355400c5908039601079551021499100c400c50121104580c201617201c1d4443c400b00c48181d009006818001d03211400c425008032445001103035010103141c1c80c0440340c880b5290303502c000605004402100c04850040c1e001030200c074814000e070f80c0d4010301c00e10380300311800400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 60027089 1250 60025839 60025841
    0x2040b060d060f050114040b030112020418060f0b150306040c0207030b010602010f0b0a05030c01030509160b19020f06071b0f1407051c020105030402040b030303090609060c0403030f11010e01 84
    0xc0e601003104801141c5084c000340da4454601c000784803640380007a003414100540d04815100601c60b420040844144403411500c036a0014018000d04107001c08c4000c1207404e008010703110580300c02031120301c3c10020121130700d0300018180416211046090950b501c40c000e11008155116a4009500c25040004001a01900954080c190550001c01c6d005964031030b903c25610018031041c403400c42860280901d4500041100d411407003441c0110329034a40b0070703100741004544418151100586d00c000b0801d100034074010400c0401424013009084030500c170417a190820580d0028a80c0c00c001e000c1600a4400e80a24100c2001d032505030014203010b984904402030300080c101c07006a02803111a481240c1031007506c004150580b21103445045c20400b40c4a000030a001c02410f11001201003029500d4680c03004140d403602a080f2650b03400e10340340c1c8950710303141110b01c10ad80d807186400045e00201d401d0151001c0380e5060b100d5140322004044103582c01c1840220300351084d0360b2004a14041442 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 60028339 1250 60027089 60027101
    0x10203090a0b090a020609240a050903060604140f0c1204110103200a030e010e1006030c2c0901020702030a060b0102070806150d0201050d05010b0a080f090a02040b060d 74
    0x42402015622940d28000402040062100c44944c01001d4400c0c0983c0780d41041364000310b01240c00a0300e100302c407a00301c4020094506442500380d0041601d00085400200400b00e01c0800c0b011601c20756a80810002a6051081280c3c4003100140124651880e4400e080c0d4100a044085504000c4c0c141c41581074080121800d4481a040c850707c0003907940c15102d1451540855a29440542c0202440c0701542c819040403d00b055540e08a00540c0e03c0b081d804400f0120808041d140c0704a03c000255016000328002610100107001000a164521401c1c8a8007006d800502c1c4110301e810301d0302c0700d40d60f44008090069554080002d44e00690f0184a12111148600e00004424400c540024a808440e421803103c40d4020310030b004d01c200e44500c41c0c802d84101110711861021441c07004840c14080c011081034818107000c0007282001122028241d501c980d0740d00c1008a54a50f076525602860507100d01d070440d000440d00c14007505040c0c21900004002034983c03444c20225149110885034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 60029589 1250 60028339 60028351
    0x50409090807110105281103030109020c01110a0903030e0f06030405010e1c0914061207080115050403151a06041701050603030306150a020111120a0c020313031112010203 75
    0x41c0028015003002500003a800c101c100a2070450b0a1101c588504000e08009910504464070100351030aa079a00c40c0b0794070300c440702c0e0b0907064130384950b035403c485006504202e4071003420f5400e040a40c0186900c4400340c4615400d155980f504481c6036450665803400e0361910243c0008004070500060313156000294002d9110350000105080003031403150410040d401941c0c2d070f840c810a200d03102d02d41d1040940080c0ca45003800110084020030009000d44039107103100c0c0b00f4604520410000a40003074815048620300140c00e14140c2c400c42c000c44480c480c2d40401010045a8440c0044c413082980c403100342c80054080b076003403800e0a81c0005007680c00540c0440305e00000c90741d2240003080203010700c5400000680080d425801e0090000e010100880401d105031100031803500c840342d200b50841c950903111040e11a9448402e04503e2203590f200300e4248071610309022400d40e65603c00003c4482035120b00320b9480a00b8111f41d141c650030028012101e5210400382d00842c03038100288000d501440b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 60030839 1250 60029589 60029603
    0x60304050a14160302040f0209030d080109150509040605062b05070906080a2901090c1b0305040b070501020d050a09021f090306051f060e180108030702010e0105040909 74
    0x1540502d401c24088000300004880da80103807a03071000c00c075107a02c0d400050341e41c11540820a8107035400e5043c020700a2107280780d4180f203003515030b800e15908018218180d0b15090020b222100c6810700c1011072180d107101d50707508180d101c00054042403071940002d40080c3c1c001d00b424801c100d02c0052460741070240d941c042c9158510b40a0600700072081002c08001d0074009014400680340c101004d0b00c40301d0304940503100124100c02d007083e4002c11760300300c002c10050428201180d40c48223080c0006222401400d004208084c0758034201c4c10f40b40d489860380a9059880c0341c0f5181c01c013682c1500a400c0224226440c2d90213001c42c0611035428003a462040660342030000d50201d243c0100400758038407048024501000206504400740c1c40050801629000300c1c0200755911104102c100180590000303c4001029960100e4120f41c008100040d1000450780e8a0700b0f152904500e10606401788101c03000c07503000f04007000040d405841020140c0c801414001c0c00c20765500365020030b55110040c01c660700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 60032089 1250 60030839 60030853
    0x3070306021b1222090f020403030807021507110c042901050c030a0315090c170c2503091809050706030504080a030f0209040f1505010e0d06091106030405 68
    0xc2c144002c003054200c1400c00081000c92031212800001e84502c280c003070400c0749055032052260032000020001030246000400894690100b40c40081d00f15001c124009454400419909480001c3c00320f4040b80188089032a80c030340e10350581e203001540d0b0038007200340950b840c0c042d29a9258414040c00070000402c03c4080e810342d01000c1c58060031900c405040c840709200d155091440001511082031050500003a05030407090380445441140d84400d8085050071042c000d2684d1000002c0c44008426000300700310340f10064401ca043c081c40c650405c80140c6d615900724400050401c1c65105402420b20407021070715005020700070208400810704442d2501d00c21740030410b0400400b4010700807480d00308540d0038595900a100c0c490141e070502096114800c180500c1a99811641055401002001030684461f11000a0070212041940340103800100160b1540510300d03c85003050018560340c0c440c007041d6a4640100100b0b201940c14030405414880192104d500541c09103000740020014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 60033339 1250 60032089 60032107
    0x3020105010302181b0c070b0705100b0108060f0d140627060103030518010e060a02010f0b100c02150c0604080c011505011b030e04090b01030209090d0e0607050c0307030602 76
    0x18180b0010a00c16401207a8080091039002c106400c10b002c0c04400b0542c0d078486c0b10301c9041d407400900c0e400220183c00c00050713400800c000020740f04280c0090a4090001441e050700548180108843d0035800006a03484032071280362050981051320301ca801c4000c5410600366526243c0902152440036411000341d650180e4144200c0740c4586d00140c43c001c2c0b800b0740c19954018064041e00d0303641d9501d40300b01d080035601a8010520724800d0f81001c0d203402d4582924180c028040c1c01040ea03925401450502c9511060400c0d04406411303000c01d49400e1201e4100b0b50070321031525040103800c0d8801000344484103e4000c180301c800d0185008104641e01c0301c541241c02400c641000e014a49801042d4200f00490b9030071004264000b190324908020803101400c0c20b4520f04042095981d1040c6480100000c00003c00e01c0c01d4143c0f402a281080c540d91440b00c00c0b0b41d00d00120114802142030468220924030300300d8000d05060744110140e4403a81d00304e0010a241c002c06070400c03201d81d0f402203900e41c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 60034589 1250 60033339 60033349
    0x7080c0609011e1d0105070203040512070819020d08030f010311030a0c14010302040803040b0316050f070206030c041206050a050702010b060306280609030606051503060f041803020105010302 84
    0x900000540001c1108041c500c01480301d503000f0003a02d00302280c842c110710080e50f040c2007540000d055102c1c003e02140c5400d90000f034582e40a402024030500b80f00c051014440300014030a01940c255100504209104e800136810510305400c0803684000301d42240700007c3d410f038002d18003448000c13007000074175410f44c03501102c00d110269082e80241c0c0400e2405002c60b1903880560111844240d81c0a01c08105500481c084c0c0300340c1c1c01810b4540f10001c1c0000d0802002e01c0114070600c0c08541c0382230030041e41002161a031145100b2032502d85c4e404c1c03040c2000343c43c0020046802c014070180b16841c0a81d90380114000301031501083c0c075540d83d18410008000d0040c0916035211200703100801107041c0c8800000d07400d01000c0c1c02c10b03000e422803603180020030305251409015061081e0301c010345150b5a4100800f10540b5020840343c082c1015070004060130305011400c15900d03501c884a003141d592106012607a120580d803154801d444080d2012501c08608600011600030b500100d010340c11801448 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 60035839 1250 60034589 60034591
    0x2062d0c100f11030f040204020f1303020a0f0b04171005010b0d060806060616050a0204051f06020c13090c0308040617060609010203030708250306031104092103020f07080c06 77
    0x7415504100c40400c000c4030f20b0040325030280c14045400c0c0c0300c2c0c8480c00807c00900450303410000501300020307900c190400309441d0368112442150081c8034503484160100b9180120b01c13805a0b01c00040c4428006007165084041100c94940b0850348200c0c0144001c1007501d60aa00c5080311031400030f040a01d030a0f441c00f611025101d0840205500c0c14084003082c00ba1040c00c0c0e80c0701c010180983d10000b041070a1210300340b5a60018402e02c0281008001842c01c5000034814603031440e010040060144c1c00400c100c0800d040c0200046405009000d041018140d81d890072501c44190480100000765007201800c064040c03079584100a52405c1c0e04005480c0c80602120701c17480f03090141d9001d90381d00200710b1350710400c5880d00c000e82d5151242d1052281410030040d14942e00203481440380c0503895031101080381e0141c41c4445081c8180018001120700d140360141c1030790f4486002005d040149524420350b500c1c01c6c5001450071a40d4402c1109035080014115040d131030005001d20111020071142d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 60037089 1250 60035839 60035861
    0x5032401050d2901090c0f02030d18080723070602060c030402030a051002180405150d020a0f140108010e100303050a090b210c120103020f060c010e010b010207060c02062d0c10 77
    0xc403155541d46200030b0354034041d2901000c107160301c500c0bd4003d109030b131102c0048980d41c010f041c1e58480f241413410100b01490102c21490520700d5075130704880c1d180001241d20803100c0c1c0d0340180c00e658452403501019035000410590300361041c50350f013000040c400c1040101c503681c2800700689a0520405d1246038280c0c1041082c0320314107240c18020350030542103003c000d81e141203406006048841c4042402e0b404640d0000c0c10070348001400040c0206504450b910480c0260390741e607000e80e250341200751840b40507581821405613400003480064010f000500b0b40c040300d41040c10300150b03182019107899102d422031101d1070406010300c02030352541c3c420782e540240c0c0802085041900140081012500503c0b0207842541310010f03009864859000310703154000c8440082c0803100161800704c0c041c0c44c2d820921030051182c83d00025000b442840003402035940140482d250040c20000300b1500c00951103c060b40207600441300681c54400c2c40186600038200004e000301054030304250045440c41c6100b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 60038339 1250 60037089 60037097
    0x3070c0b07020a03120504020102070e010b040609090e0c090601030e0d020a0b01060905010c030e06070c06030506120c100305061513091404110405100302120705032401050d2901090c 80
    0x14a00042c0d040175591a0b006045500003800342d555000413464240a82c1c03003075034248007800001c200820704800420a4070700c82c0d00d403400324035039070341410045032120700712102035402200d07242c80c00f8940902119003043d41454007042030034140c00c1460070407002811007409684801c1800d020040640c4a0700d00404245c180615100d14040c0041c000d514125401400c00c2180100100f140d0b6070781c01600c4801d604004282c2c0038944598001e001400c0554420340f04900f465900c114032100050000380b001d1000d0085c20300e0100c0c000d0240c1c042c1002803c050340c00a09141d0820003e4046400f8081041c0a000d05101c124942200c0c0c3c1300312980c5070980080034010078100408282c0039a06600b1240301900c00061560756468a003101d00318030780009501603054000d800342c1e11400608001640e01c21016a000907043c100d00d00305480c0241016982420300b440100100d00d480294500170501507078000c01c04602c0390b08205042d00c29070343c280039901c1e060700052010080740c0c4213401c110310090034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 60039589 1250 60038339 60038353
    0x20d0b131a010507050a0606140f0904170702060f07050606190e04021e0301050a020c01060f0e010e090307050f150906190e0106050303040f090c080f0f0a020c0303070c0b0702 77
    0x409450299010705031581401000104c92003040401c00c046442d0540280701082415210800508042403c1c91110b1055100981d0700b205450002d62041c015a44040045e43c1801c00114034807940d044110103a80c00782d130034400320b44014200e4004100c054030420103007000c2e14101c02009a107000b81c20355850151030841c0140803420b0801d058541094040315031544196004007d55902503140921a4065090109000080820b41c01a1060072440320080c000030f5254440c0b81c0003101107201d4040702295100041005a00011140d81c1104d0b044094a1400c0e4194440d01d03d8407288070465401d551240303103170481082901c940c5a0308109040050840d81c01d1003445070502c0248140d0208040381e0718901e50042510075807003030000788405002d50352241e5558090850381d034110f209442c80182058a241e4482e07100389180c600c2101c07585e10050321500c0d00c06420041c024002d0842c0059503013084080c1c00298200080c40c485c02040d070364000d4242442c502614020310140400c019980240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 60040839 1250 60039589 60039611
    0x711030a02070902070618052b090510050408120705061003080d0c110f010f060e04080403060905240709060810030201081f080d020d05040605030a050a06030204020d0b13 75
    0x468001c04503540483d0240e2107290324149a4002e140c441c2e0f01d1081508550030000410602062600383c1c40320311000e5032200d40c2040c5c0b1441c04078003100043c50020f1462601440a45070212140058120603e0403c1c03d00b904c45031503d1a05050380c00e01040c40c03001240040c10407c00300a00344d4400c4000b030344400c0c02d1b8079658440889015668800c1d60440c0c44903803d07a9118410511600e21400f40c804607119200081d00c02802800744181c00c80e02c0906041c8007140c041e46062500f40541da2099441e841c0c00e01c0c50300c84c0e40041100000844031401600010311078143c851081101030110f80c55402900e003040b6502400100c0c42d58422003c3c40b17005020000b65002c04c9901c5000c680d028203000201d13982d0f135170407000e600141c840c03c542c1c9087c56440214005000181100000030141c007183d040c20030040c07081c0d5840c020384c8501c4c0005201040061881629500840d400100111f40031030b03041c0e00c82c3e0000c1c050b83c0288441d61000382d80c43c6242c103c0740c58203030b01218201d0820f5004110000b445 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 60042089 1250 60040839 60040843
    0xc090b040b07060e03030711060108010903090510050d020703030c0305060d150f020906070c0e01080708060a110705120d060f0e01051c0609030903170a12050903040e0f0711030a02 79
    0x5205100c1c4030340380400c001003404025002000641074101c1a240d40349810903010b0704000d50f20302c040078148140703000401c3d5a4814801c4448031901340d200d58401a10303103400c05c003110500822140410405102c400141d10742c50000e419aa031294802203500d146403d8002d0854034010300982c81000341240c801e0100b2840038642c049003000030380c0803d28500c9081c0c0000640b091041d0a5041000086c109040c00b0301d000d015400d075803441d800240315036691300f402a6141820301500800350400c2010841c03c64060744140051210002c0c01402c000311500d03144d0400321202c9003503114440c00142e42014030300303900c654030103010200c8220b60070030308040e40826280380c14061140607a0032081958600c024205a078500140e0102081c848484603140042c030550303031840300305d0303090001e50348100a060381001600d03011021641c580034060303006500140a044043c0c10030386a800300f0040860703040c001500052041c0500e0301c10340d00d40e0074030b01c80c0284954044c6901943d50340060103d05012540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 60043339 1250 60042089 60042097
    0x30904050a18020f0111150612150a0f09080a020708060c0414040906090209010308040306060605120417091002011406030c0a030f0303020d0509010e0f07080c0d051216060c090b 78
    0x1a540328070313100203203801a034420f00c55110100207842a146407022819040c041c1d9841a01d0030340301a055418102e1209a4030145043c41d52100700b400c00006140e00601d5100c058804444000810b03e81f002c0c2e240c14050703911030030b236007801a00160342c1804088010840181c0103007081307912074a028a800e00060300000a1030240d44950703140e94004080c4070741c98000581050b0024103110f500d5035207180440c40d950161004407201820704000140e0310b0301450554009540b0100700d41940d5850b50f440c508028070358a14510f24110502c819012602e805642c4100400a600005207028044040d04005140140550f100e07134421040b990454992041d0441183d2740600034210312440c40c0f0b41500030b80a0b4503007c108180c9808104644210150810b004040e101021b0f2465210750444842d290041402041c0855000624903000e90034090400c0c00d08038001c1081c0c452b0389883ca03c00700c4407070784003180305111840311655813414000144140c100001030343c10607015480c17400b030380f80600e405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 60044589 1250 60043339 60043343
    0xa060903030c0507050a0617090601050105030f09070b0c010204030302060108070f0b0f0409111207030b06190507020409030809070905070206070c23071703120c03060102100608030904050a18 84
    0x50b0740c444081103010090340c03010b40001010a0314164070381d0b00003030100041c180c0c4d40074100071100210300c2685c004142c20781a960180d4480d80b443e5140106143c10540140076882c10380b00d4400009000000f90300902003a5100c640003698940c07a42c00c00a1901c0011307002412943c001d0141006201a0708201504a071847ca100944a4010303107070f03845060003030b68049007542d814240301780e001c03004040081c035404e8442d080707a450986991400304c0072510b44400c0a50003c0080200000c020300751500a80c04000a2a0892030820584d001c1070079942c115004401003040001401400e405c14045080a0074200c08100080c2c40d260000956400b0701030122001d1102884180e0144009e100c1d06403041003d0100003070102c0c43d454201e50b42c44e1000d12403841c2c540703805140a01020004021a000c40d030700300c0c15043c0aa2600001c0300041d5001400d06815407240c0ca0020341404464014800248803810185840782555418002650001808068164500310030303890400e0601040d410855 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 60045839 1250 60044589 60044597
    0x307060e03100b0d0803040501140f070f031505060d0e010b01110c040c0c020d0b09010c03020906040905180a030203070b06090f04111212130e1e130f0b0609060a06090303 75
    0xb82100c0c04201381021480000e422000d00004201c24882c0541213484c200200c00841c0c040d036a1419260312440505070781041c00200a15144000248240c0000c0c250304d00c60b0000381040b990362000955654800e845803101c1580341e1501201c03c2901384200d0a92003000e080c11250044001c2c03025484207501350fa481c0c0304a40c2c0c3c11910b01281d1140c1450403110740e0242c40f201e444142420804600041100c02049540c03c180b84290b100c1d100340203840c0c040c20081d002c0c42c01c181c1003d14500151000400340060158040303001a5204030800c10401c8041c080d4010315522035007820b0880d100c00005001078007586801c0f0511802d142031154559003d6009503010704a40704400001d001020034071809299845088804d4481c465041e00900701c00c2404114045e016595141e14010007004130b0302644440010001d0140c8084044440e0ba80541d0021030200208169690b20842c254030f500d00362081c0c4008800c002c1d05040c01000c9a4124030f04452140b205454580010540825404020208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 60047089 1250 60045839 60045851
    0x30406080f10030807080c011a240c01140a0c050909070834020606030601080d0c05010e0114040b130506070e0303040f08030a0f0807080402010c0503090d0b060307060e0310 76
    0x100014030702c01009180d0010425580c1c00f00d500b4640780c29000a082d20a20b035103032444034800c651490102d5000124050071020f0001d0820140000b40180031aa00a1040307040001c1c9030500d60078820390510071103451a90741d031801c1919000048611540b40c00c42800400c06c800d2100c1d40e80c42c0c101036804455490700c40f140d581c0b00b02240c0c80c01260f10748141100c051010f2681607010007102c250482850b20f07403c49110f070b510030041659454003803081c0400e940044030f00c02000c0344a00340b030807203ca000300c0020844003000d0f00e4032030840f503180c440d142041c0713203460034001002030400b411034000e903044203c43d42e1042682c070340644070100a010041032180c103070340c9103880780c0b010b0083d18010701c2c0d10004221910390790300c201511b96200c64002e10000744607001002c171050103041c8082c0a44515610403000e80d5484d801074031050004201a0342a00c0107120620407a0758074400a224030344104048140740c1009400e041c60b120954000000380440c05041402c60b07140081d4a00c0b0642e40c0010100384 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 60048339 1250 60047089 60047101
    0x5070f02010225090b18060d0507080601090b040f0e060601081e04050a02040e1b01081915060e01020703080306040504020a08070305060f01050406051f03021605010617030406080f 79
    0x15001403800b054140d401d0800c840040401c02420007000c441d6040340c00c5c0305845150003040a0344401c01030703a00c0100084400718020b400c145240f180828400d008136001030342c40c0d20702c451070071100f40d002c0e41e03505440e800c4126003400d207406490a580810501800304905401d0703c9901c032240100a281000400f6000440c03216140c8407030f0004105181d101c0d034241c1420700308161582e81e001c2007a8002c0c0d0401400a146030000507507400c5004200303400d006012613400c0111015400075101805042e03080b04060311808040c070079400f1240070700030068440c1d45040310103043d003600034480f5810f5400c1034408001007030485003140d034852070840d400550f079907551001a250740c0c00d9801070305603445a840040200200020040e0192155102c82c980c05d03a81d078000c03c019036015015030754020658000c41e0800c0032004003000391003c041c0c01c01509041c6c80000051034020400010b461680d140e007810011618071a00c040b40080303846001e5840c003400c0c510080c1c0441400f801904011091a0020b01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 60049589 1250 60048339 60048343
    0x120e0102010b060a171003050304060c030c080a02010903020f070b0f090d051606030b060711040b12160e010f0812070c0803040314010506090603120a02011503030818010501050105070f020102 84
    0x32001c00030043c0762a049222002405080b1502000000192140210350045415a5242c0840c0d46c848001c1d1729150515904440380c94044d0021020301c4511204071000076500c0b0301400100c0416400094012480d0030002d291083c5101d17400340c2c9401c01c540238070074842910102c0745100c00d81c0c2010f5590718004004245007000100024100340945c0111131102507100048500301c13071182d60148002d800703010401600d4820082c000703021108a090040c072504168000c20b58500004000409040359041c0c0b070b44c20142503140c0c000504d000e01d10144010302244c440980509031001700c0041e014208083d03641e6444600020b104210000701d103800c01c0003004101c02002e420317034038152902c0d99580d15040c0103031401050080155424240000c0c40d0741003000c4900d10410b401130040150002d01c245503030a603401802060119500c07214101c0d54590743c07481d00c400440c40b030390783c810152400c500c001006202ca05841c2c51564100300040105aa204090703035585a0410780c000000981440142c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 60050839 1250 60049589 60049601
    0x20d02130203010e1006050301180e0d050306180f040206070206040902040f05120a1211030d0216030e09070c1b1701060306050601180b090103060305101a0607120e010201 75
    0x25804541103040000045041c0c0155040320258001c83c8041e459480d213143d4241000d0085000154080c03004204640d1400c100045a030184c210000703450300420701c2c590820425080c07050100d000002440480c0c1040000b002d140c1d00b2601c00c060490074004142c103981d0030b0141c0701901c9280003040303503401c1d0341c1d034402254002c00e0030000031541c0f280d5a002002000f0401d12a00740319420802418190140224020458a50009003a130700e50050481c1078070101a658076101051000703011825100855100405030040c183c0112040c0600c180f50080400f402d07412418003800b2030300d00340980c5980001800d21040c0c3e001e081002c010710783e0080c1083c1060760b41e00c28864521004a0f01c0b04500c1c041d80002c0c107590242038240520341d02c100055805e18620001000300303488000042202541010242c180308a05140101c0e00b59a80e8440510308071881c00c00000c150390301c200f041011040c0c400f01804010064890700d0070310450740c641103000017082800c141030004078591035285a00c02e50043d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 60052089 1250 60050839 60050843
    0x40b0f10030603020a0515030a2403080715090309090b0f0a120b09010e1e030d05010605031f270e0d02030408060f01030807290a140609040803070c020d 67
    0x5909000003800041c00741120340b205a02030040840c02042904141c04100034141c0000d1445107191520b180c4079004181000d1a40c81c0865044000010130a4803040000190b0060800a803a04110b007003020188240c81140c010080c5040c503580c00003904000c600d02142d20711b5030005010340090300811600c16021b40a00c0d400840b01c02c010640d05a40055100310300d0140d07082c00c2041c1c0d07601c000a400c0720005c00c007244403980220304030354504010180c601c00700c03074403034054030b00b0145400100b0095034000c0e0043c0e0003156012042100c0d50b6080b24001618242c4030b5400030500d454880545041450b1308040342c1c5003100e0001808200783c40380c00c05240e0044e07550848801610240009440e50414000d9607103038003844010035a002107150070b16044e00c0d01b00302d81e039142400701c1d5030f1031488002d8012080c1580702041180705602d80150b4400d031055010003004030f0310030321000034001c00c1d140081400e440741280c1d9007031001103814501500c1d800043d60514100b0880c10b8000501881004c90380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 60053339 1250 60052089 60052099
    0x70f0f03090315060311040c1d0a0b0a0306080d0905211603050f010b0102010b06030109020c1c0314090a0c0302040e010b13020405040c021207080f1606090b0c0405030c040b0f 77
    0x383c2e007031401290302110840f402985406a14502c030b01c10841607808601d00c00000503660340301083c1d0790152080c80c0b0b41841e4024404102e0a13a24584140550009045000400da854070f04010400301030001364054038580c03801120107810030f80002c1c6c00b04012410850380422a90101d002c00d4010007401c441a9002452109000d69030300e48165501c400110b000029400d08a13005650350050081101180004040e0342c15a030802140718025007203244065002c2c0706400310302d901045504600100e2041564000c1048890181c880003080c80203090510740b07601008881340406e017010118400d40750304403401f080c4010550310711409000c0451440d85d101c0b031400c20026042e4420b17030062045880030f07642403003001d09492040c2d03144e1150f0b1980f03000803081000b1013000a0500002007020340c941c02002070510001160a141d2101402012107005588603100b209101009500307030b40c800c40400702140b4060410021a071194160b4614500031600d844826580e5038a08888210026010304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 60054589 1250 60053339 60053363
    0x403050303041b05060403080304020d21020f1b01020316060f06140301050c0301030308130f1406041a06030c011101020909091b102705060c030d050903070f0f030903 73
    0x101060f0192a00041c00f82084a608000507a030600b0340689040301d801c0500309055941d160280015604000ca0807101520181d1100a54403500e40d2402e0810f0703071035030003083d075041198100380ca8003200c10390380121071044480389406680d0000071200c1880000b904a19400c61503d4840d0140ca05100d001c064a4105400807803142400240104000022402405962100220206148400c2c040600010080c1001404030440e500d00c094003944129507050001d0384e1619200e45840d1825058020ba42115040c4403e0000e02682042c0216902c0d55420007400c1c1000007a65800707000c20640e050090b4000c4c02d00c0022000e505070b500d4200301600004d074910b41041c090392121300252420140d5884072803035901c01c1c14888a501030000e001d03110f070405c15600c480c0202d1039401e42440340754002c44514012941e500ca40014020a2001c41c0045490f030b0000701031203090b42c1c0c0040050040d03610a0040001041e2420301045c900ca80260010034005900d050456092071681c1016150b011843c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 60055839 1250 60054589 60054593
    0x21e09120303090c0102011104031707110618030f150a0c030b1005091203040605030402040203090f01090602180111120c0a0c06020d030b010507020907030c0c050109110f0907090e0408040305030304 87
    0x1013034074054048241d0080290326441e001c0607055009900000e0124440880c0308007222440c00018400e2a008841003038042c000b0f400001c8080e0300c21800107002e08001000c84810303050400002415146070b40103050005d031001c2c00c4d1582d00000618403005036449071550074400d8003030b5022038008400544508400e81098001800720b81c407804081c3d000c0c84261f98103160400c0c01100352820fa40c0c903a036445113161196003c01010790005420010039000c0d149020f44401824800c1c24041d602c41c400c05a140c160250041c82200702d039007581c1d810b00c010505c0840c4070710008540e070f802c0c0d8605440c801d6110200f01920707500c0d024102c04000c21400b0014008500103400080d0510790152907541400012071000c0116942d01a541c8000e40007841e05010581843c041c0c4c1088948915521304140662495140e460030749065403c152980101d0003502c41070b5040c1051401c02030340c02136401803407508240d08014041d01d081d02c50700795201e50583c040380811403240e040310021078100049a880b4140381c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 60057089 1250 60055839 60055843
    0x1801090803040b010f060507030c080d0525032304030912050f0c0103020403020f0405061504090219050c07031101021203090c01030608120906070213020f0c10021e0912030309 77
    0x80c1c1d030079550070f01c1520000528007011801481641c0d802c0e030b549030030701c2c2c00c90780c0a413000007603403c00f20b40c0048188480b0100c1c01440c03280074401d42d045203c0030450403240340c0b002040a07102161208240c1800742826482c0608095000c203034071012080740543d9214201214902c1e4150042500311601d0400042070040c001441503a507120360003a1208004d640340150128856884000d4000d42d03518121300342403810703610050344004013900e110b141c203502207602c8049500c5600701c013008035804940098100c0381801c2c1c4050201071b60409518010804c07107066503d80d42440002e02400d151030503251a6403007800035016602160b6030301034603802c01401b05a10b070200d0301d81c803d000131726080d40062a8040042d41c1415113940c034614918101c0321206201050340170250982c1c02a18000c034125182d021343c4010700e08803402c1ca0303c443e21081000c04d260304006098031101da10302d0041c400b640f1001981c1003007240d01654481d1484c0d039062180042202540c81c000e90000034040481004014040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 60058339 1250 60057089 60057091
    0x30606090f14040e030a1707020d0f0309060f020a09030501050c03011409070509060f0c0114040201140a09030c240c050601050609040e070e1024050a0212030c041d070c0b1801090803 80
    0x4640424092070340c5801e17080340e8035045011002d0018090132f0700450101d019070702a0340600c0c000c901c08070b481d03035030880100189c0c0d02101d4250002042c2490410074004203105080d00302c110310079240c2c0745514065081701290701030f514040c492201c0002081f00940103000b2220400307000345c50541c460310302508400c4190010110050fa9500b0108020034490302c0c2c1c24482c1c070451f8140c40f2850f840c0040040785803141c01c001500428446143c0c40400410301c801203440007084003c0804001c19207040211003061000d0107040207000c200210400000c40100309641516411b40e0041e4940c11180002005040c141349030344540d016000e40440c000c0070204e8414801c6c00184c2c601c1c404c5c1a920780903244000da8580e2001c2c80b218601d0a00001c03a44540014203005c0054811507810184060b1031100c1c0d944160303881f2104900018042100c020318060f9241c0301c07050702403000c0503441d0018000c0c0010400d1800100740000e5440044c0044211803000c135900d00c0c9004c004c0000890320f01d0044035540c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 60059589 1250 60058339 60058367
    0x5090303121f24030f0b0a030b1501090f030201050304030c060906050907050f010903060905030705070b090301050105060f0904050c0c0a0501060311040c09060507081903020703030606090f14040e030a 88
    0x1411500102d00004001810a505880c007400c0f001c0805403404210020212440c03100f98003070300c0c0d07084080c20f9510143c0a00c0a94003a0101c0035040c104000c1b810382045505001a0622807131240410441a080050f107040b41d4080c280300da9a60307121f00e000c442d04100404001d007520f01d0b00d40c500040c42015803201e40310304450304c21181e020340c840041107200207007000e003a80040c030307114003e00014400703401510788944910100d80c10014070359245030a10042c0d40281c130610380d0104114907149070900856006040039202d8910308406062841700c14400d542c07204d0300950b141d80210f00d00079080411112400101429220328560502d0424060036040c8015180040c2c1c0d01c400b4607980c41c00e440358200c0d00010340c0326448101c0c504541510a07401001d01558002000c0c004032030820031848024000c201150f400590f1000380707243c050211119030300a00c1c02c0213107449041c4026182010101c080c0c41c4102021301400445000040c00790009000a181c18000851a41c1c00580c0152820110302 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 60060839 1250 60059589 60059641
    0x807080718030302100515150f040b07080a1805010914010c02101d0616030c140a030309020310050906010b090301060b0d02070c0b12130f02280b030903030105010509030312 76
    0xd110514024004011030010f03507444a4804001406248210014272044912004850509640d0560020b40390422242a10a903a00041340c0548a9101045160f618224034a0404950408000030b0005000b4010700304c42050006d00245a6800354004c1650031391b00509050303114141410051404540c85014001c465030800104d05600d40002a07600d20580003083d030071920500d44040740c2d843d6803903a056500080d081142c2181c280244104d00c107103800303a100800d40030058414540b07003145001e0008400751512040c8040700c500422494111001d01c00c0941c2c86075007040c0024010151988140280310000445407220509a00a040d820340a400c100c10407681c0c0701642c0005114280117100101000d5001480d036140c2c0346802c0c3e81d0b042c0205118807051085902140007254503c0c040000c0d04105400c81c5880041001c080e0040d1034048038030780c19800d02c008026a24003060042d1414000081041545624104142c511607002c0005c00c0006042008409030103009a088400c420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 60062089 1250 60060839 60060841
    0xf030207290a08060112020d090c061d190803030f0109150308070b07030609050a05160504080c0603060d0b0a0c0f050a080a0522030302030619050108070807180303021005 75
    0x1c42090050700074608103207404185401e00b0031000729440c3c00010b0045050090320006c00c060079100d0310160400381081c01c2c0001e0400300504041c1d5420030302c1e62000c1c007080300000035000f01316a40080b600107e1010b551098507520810f40c07010500109410034040b0b44404010010b980075071408040c100c6200c0f98040000340c002070f03d510940310300342c0005480c4040411000002581700c1c0740c201c5e880602e034900010f60366222517000e42030b180c09451310200d240d110000d10030301c19400824000c0340249824040e19152505100c240c496807090f5800e07105075000300c00684076484507103050220310380c802034607a1189810b2a040d00200b00702c1100d500024100c0c8103e840c2d443c0180120b03204c1c450a51078840c0ca0b5500c6000302405083c0c0200820340c00c4141a004001c020004410803003051b100fa00c000d41c480c50314805000743c0901c1d035040308141d8403103807004105a9810005486d001002c03031410305500d0f540c03600f066802c5500c40d2403003c25840c410300c00000341640030400d1402e62411607800d000c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 60063339 1250 60062089 60062129
    0x501050102060408030103030e0d0f08090a05010e151e030403090303020d020607080a0902010c020402041511030703080106080c0403020d141e030904090c050910080d110307020402160f030207 84
    0xa500821507004141c990200014004a8024030740d2589d08100108011040016075468500f19004260110f403203500c046686440b502e00002d52030080c00081c41d00c90174108030700c0005142c80c0500c950b80a0400300c0022080740c4004e078155140346081c00203005560300d06151800800010f00340c032098005015060050010910100325540581007507550105503407203904000c0d00070900c0d24012414080f03444500401030b01c490014000922034107201c1d541205102c40c01604001001601c00301c1900f0420070300c80001e03005034079203041d06c81c1071402c120165a1311410030042e00c0340d9080654401c2c00c88a03074100700807044c4000540704428a00f41c03182c03201e126883d4561450000c12100f0260400d00c10050b1740d0902e503001c0300c4100d002c5e07043c500c045a078440224178101c105a0f440146901c82d0310092201c29020009800c2207030a0389401d203c1c4424298682c3d80301d005400e4002c2c8500d400203100b040180000704050012608038400d00a40704103450060341e103203010f00c40d811075950008844e5107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 60064589 1250 60063339 60063343
    0x9060b0d05030c10090b16110703030504140307030b07031104081903170601020d0e010302040e0c03070207061b03030f02040503010507030903080709050d0f0602041715010522090c120b04060501050102 88
    0x17034001d510404210b8507850b41d072402803900e12280002010400c850041e210048410014000114020340390b144d561810203600303002d88101e41354054001d505c503071020030000d1101002039038041120b00c0c0014007902640c45848192140b50301031282442800350400304140d0b030141019500f03119403034003848040c005009240d1400d08940315800f42c1c01001c560403800d805103d2914030804145030041c901a01c480f006c0f100a0b206558600d04620007004014a0130f0b010031a4102130f19460404181103c402e440720b1502403158840102007540f600381140510520340c041c5c0c0c01800008009019603d00900020b000f0420301d08254000381149011031a6503000c0c5a40c60250b501c0a0b01007424803003180c44858000d0444035046808507401c003c00901648265825a2600c2c0c03040054400c0b80f00e20042820400010b8010030311405000003040003400000d03040c940c00e03291100300132400f0b050504003d416131903503a00919015103800808000c0000001040d442184600400c12140e600c40c8012a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 60065839 1250 60064589 60064601
    0x306100308070201080c0904020c0f0d03020708030a020f04030804030b100510090e10050325090203070903020f040e0d1206140105070b090a1a0a0507021f09060b0d05030c10 76
    0x10348403040400c0442c002d0352142c10425800062200d025203170840b44004641203074400c070440495500002202d2403208028080c001604000f45000e500b040030b03d4440c140c4612000c0c10b000c42c510350000f11a0810034084003690001e5804c0000c180c0c80310758a0800c0303041054102e8260703804031310448012485142c084032201c03542100f0b9580f40b10980c20704d216410f032008060603847c90a00004800a4581d804100d85220f16000195505406443c0b0b0321400d48040190804030318280107104000110358480d8a000483e6011902c000560240102003001032800070100000b1707014040e216100681c00c43c082c80c903004100c103000c00c44c00f9601c81411000c0f690450310a40040c00400914000c14800d01e0042c1e0401c8408091b24003c6c05650348502c0000f600c41200480c9242e05020404600003522410f503005007140050701c2c800b06403000c0050944282000341c0c003004d1307845e00c06c48103000081d4842030100001600305001011381c3c6c14400d41d41e8009422040041c481d5070f54400c280d91450142c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 60067089 1250 60065839 60065843
    0x40c03020406140f1225080a030c02120c010c1211011b0906020a05030a08220605061809070308030901020c0f010b040605030a030c08070f0204020a0309060c0507050a0b0c07020a09020903061003 85
    0x340c010000b402c0c2c46d40b2000000350f540d81441c504020004100680d0a1020782d015a20a0300c6618547d0654030600200c403e950381a041c0315042034500701c02a9802c41114840d1980c02002020f080120081c02e4034408001490001603600e012841104140c0c000741c2482c49451503100d2216035a03440c030782203036940000c03100101150400e0149043d00b0f8040c9a14940207990b001083c10b1110303241c14140000c000340d01d400d4941a40360030610509041800112100c0012002c0d850158900008241c1d9600d0b50351000a00c40500007000540852081d410f0310002000441552090320390a03104a02074034a48074158465403816800048070b26000400d43d4041d60b0540f82d165090600d51502c09680e0840318051394070005122040c070041c1d403548018224403019407400036060010303003408800c54000340c10b00002e000f010000703c40420000074030120b1091f80110b402080340d45104900003180a0050001d4101c040800003103a0000c0320740241c803081e10180c0c202c40d0940e440d484407010742c58a034800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 60068339 1250 60067089 60067093
    0x307030c14060705030703020303010609090203160c030306090e030306150a020a0602070609080f070c082805010b090f011403030418090501141306051f050108040c03020406140f12 79
    0x7004000340000340c025000e10020000380c00d040507511032604540c0020300c2180103810010050121f44c0d005603100c000341890710402c50962904088041d403090b081003000090081c00c00501080620030341007000503060404d424042c0f55154030000381d0300d4009540c0303503101d2142902084146110001038401c056250b90040c05a500d9984035040290300141040d00c00e651146120030118444100800c0240c0002100b039a54030f00d1401e01d1400300c45190000c1419030014030320b010081c600e8905402240201c0603030600c1d02040780c078283c0d006156a814903500500148100141e028004044a04032039005160318240583c500c101500da1040340a4010b03000c0e00030303800b030f81842c440d50302c01409540b099000240c01500200f045590100490b020900300b5070001c100000c0118900a60350000d15000c2c0f03c103071242d01844c0300000c1c481ea5000b02410400c440d400201030041280c0070304000c0d41c01030000c20003a521180200342820008030300c50b000709508100085542003a44040d201040d00e280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 60069589 1250 60068339 60068363
    0xc0e04180b0c0705030c01060b0711030706020d030e070e04050a0213060501050304060f0f050a1506080f01030209061810050a140a0b16051f050f09330403030b0906030703 75
    0x840c195001104280e6191206000300e14006d0002d210790b4001d0101400c0054031403045181090520303044d041d00b18040e1700590703c104005a000942500a01040c1c00c0100d00c14200078402d6150581e154042c80603e812038040c0030030300c00f012030801c00c0c06000ba5200321800765035000480982d0319922a10740040c03400c03c00640840c02660105a000d0952900032070301d00c0000c05148181c84094a04500580d134405240c0158120036001c1c10040c400ea080100040c0341045036180030160510001c0e000303910601c001210355a906c800c4000c0404d50380d0000d40d150a240005d1801201540280c5004e81e1880708080303207a844a80c240c08808100800310506182480c501d0510f5030403080240380c4007403054010b030700080d4041c03191f10310030080c0c0c940f14030655802944000c00e40b0000303414100000c0ca01402d003c41c24101154501081c61244668030000325103510680503c0800d020034070000e43d150003440304050745508404030701c03038084501c98040d4484504140c1c44183ca0b2000920520044d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 60070839 1250 60069589 60069601
    0x406060e0906040c05090a1409070e100e0a020a0306050915040506010804080a0c020f0a1706060901080d1d09010b0c071e03031412010303120e1b060d0f0c0e04180b 72
    0x407410701e07881f03a018000801c58000040c15004415019031b544403075504040018071001c04405406036000001803202030b125850703e0325018040d24080c2c07000980d80d40003d4072604203402034002030018800036190000c6481c00c40110020040c0d5882100d105a0a2002181c00356209101080c00340c0d4000c0d41803450800c0c42030307003030725500210030301242c10088422154070995160700c603000043c20b116141030707070080603175214905200005220601c511108001404030b2480005e00d020098218101070f9103d80500001c410524200c80395541e0290b100400810f041008402404900d142d4808a40c1199159801801e140c405500c030242c1e0081044410404030b44650561892082142e50160be02080c000c0d03c10300d4400f098000350041400111030b02c9075441c0c80d1051607000c660000240414005a0090040c01d481c0c850420303200781c1010851306d4001100b58030044501581c190300f0814640d03c0e170300c041c00d001051845140f06910784002201d0440701060305d00c1c00c00e90300c040c0700185070b0380e48 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 60071945 1106 60070839 60070849
    0xd030b03060912070303061203050d0c02070501080a0207030302040302040908070519050d030b1201090b060a06030b0f220c0305010e0603030c0c120c0402030406060e0906040c05 78
    0x2074042140307200012564654000c00b660400b40e0390000d03414110081c1c030594200d0300300606c00c03440c0307a000c2540100041c14080d0082d0024000042c6600c010381c1c59200700e104160200d1100c02c001114001c45a00a02541c1c1c0b10703090040c20540c0302e0b000f1030110354085c0c500322440c1c07c0005003281400401c01070300384a440200c24103400c1c0211a40c40c141c613031f10039007461003d04ad01c0c0d40c078101940c0d50f180207601030318a201001b081100b0303003130070704100440c41556507074095940e5207408580301d840780c091b50840100190100101070b0000c4e0034440c1020ba0030505114070b00c481c80d2155100411800b400030404525580881d00e54108021118100d60290449200794820000c020040c00d000c159043c40343c1c811501d8413080c21402031f41c81e04060f150044145d106100004000c104002c40d88140261845650001c12503500c00095559443c42580c004c0d1400341104000c0100d4904 = true := by decide +kernel

theorem cover : BRFrame.Cov 59892089 60071945 := by
  have h0 := BRFrame.cov_init 59892089
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59892089 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 59892089 ≤ n) (h2 : n < 60071945) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
