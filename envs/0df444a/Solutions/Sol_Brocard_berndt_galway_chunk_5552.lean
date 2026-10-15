-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5552
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:14:37.191307+00:00
-- url     : https://prove2.me/submissions/b066da78-4c30-4b2b-a6b4-851e82f03504

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 998381294 ≤ n < 998561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 998382544 1250 998381294 998381297
    0xc11191e050d120c12030212160f050711030303041518020307150c0209041113020a050d05070c1a01170c03101808030406090311010c3509010905210307 67
    0x1c90200c0c0c030907110b0765203134490580c8107100500300c02100f00c0c058040c2d000040b92502032110300000600b07101402140350a904010341d1940700da05042c0106941075030108506440d0f070000c0c003144100f036440810007140210b00ca55136442c83d1814102c014400c40e0308007a80d402c0307a211840401009640c1c005000d00c182c0745880b000119018007287c040d5800d4044d00070003900075928000b000140700b4821080c184481d41620100788280046684ca407c031710030f050a000120b10180b05008410321180d10042e8000d000e4213100c003800c0c60b207843e0520010aa03882551700c800014005024002d00c1e070210f10701500710300c07000b004d8090703400f00000d4440c142c03108a4124195200a04480140d8076010500200c4d000900107580b42028200200505980a415000700b41000008082c544052240c0040d681d0a42d9a40190142c802e840147e010058203a010111440c01100d401141030f4400850040e0354207800024101120302d4080e041000038900402200b19500f100d203c1d03503103d18212607000300c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 998383794 1250 998382544 998382563
    0x20111071a03151e042304080903060c0304150513080c07080c0307030b0c18130f110909070c051c0201060f0603020a051e0f0a0e120708070302010c11191e050d 70
    0x800900740001600042801aa06d56510500c001c1c004e65200600e52076009500f0b61381c02d07540d0301e154040c40b440241e500900040103d20064550421035106030b4001600600740d404200090701c1d50309442e085035000e044d00350089801003040300d00c100a4448002d5040c0c002d007000c01d141d80c07515021000002d0010390b10000c0002d6901034500c1026000801010050003444410344440d0000b008009601d55810541d18100b0907000606101041c4e44c40c0c0c1d030707009017480c072555a070040485040400860840305441145411401220480381da111010301e0b503400040c82515110002c000c400e00785d480f4800741441000140f190702da0020803104001424884801e8045c03052440c80d030306128004100308258170108000307000c0e651001066100e000101c901520580103015250f40340d100c42c0c8920101c5500150007003005500448940e000e407401002070781000034059021410700c10503031000501c0844d603080c0c1031045580c01d501380e84c2c2d800721800d14448030f94200008508201b00e0140b0140c0341c004c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 998385044 1250 998383794 998383811
    0x14150909060727170f06010603020414100c170702042003160e04020a09050405090d0807030f1e06030302190b01030b04060e0d030b030706030e0a020111071a03151e04 73
    0x4010043d80241503010000260345000c20020703440d500a00040304060182e240006104c910a0080c0c40a41e81240080c040f0300c41c090082015090b40316a1102c280b040c9040058042420f00c490004020350403865030769a001280f040200b00c2c1d4038810010502c540301440404400c032460b040e643d10a0b4410f0388000380e0b540c00d08050f40c464900c20310040d4800e00028504042651011b0300404070f40c0c1c243d070207110070b071280c903e455210305418501c1ba000035203800005180c148250803418454561250001e40d00c690013418909203070b481c0c1c852012082d2203070401c10030940c0c104030145172030701403c424007159031242d941c03200b4082040c8006411019100c0c003182c1030000d19032100710002681400c0712000758042c40c001c0e01801e24803180c140719009001000034428061b0040c403102c02c9030a00a401c2000c42c40c4c1c01951700b20001008800a032040160100d0b1440d40c000d034000110a82e41c180340d03104d282c8240110700310407119440c00d018210098500d04040e058a58003100c485046601040111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 998386294 1250 998385044 998385107
    0x603090304080a060f06120336030b010501081b0a12110705060f16021f1407020102270906122a041508030d0b010201141509090607 58
    0x290742c1001a0a01441200b40c081180c15800080c5100e01c900003440050342d40d42c10500785031010080900416222001c01c1200300c0603020008011640500c00400010450f01c003954110042c1c20890310301d03400800600c05980c0180c00c4581c091582c450002020030b4140c41d8011600404070304500f40311014100301030f201e03559002540810074035001d59885d601c1505040e0b07525003040d0f5418401d9409000415000100c0645101c04a88207030002d045044440818000880c0c0038410160110384e900b80000040d50307111070881c015441c550001d42c645c0c43c0ba4041001e00a01a201c1070718004507a9011070580d16091900c41e4480001c03200b03040d660058410350341c2011558540207940c65071380118440c0b8401e009c90343c2d410303114054604202d0a0540c403003040e1011800e008030340d502e07803041c04564080d18098015801010041c07001140d00788598520382000007082e41c2e05807a00c03545000110765420010303e4198404e10100007084103041c07419015040c8040b00c0c008500c90700c4c2007003e40e03030034a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 998387544 1250 998386294 998386297
    0x20604091e050a0902010806103501060f030e0a0b0703090609080d02070b0c0301080c0913051c02012f0904060b03010602030a09122118030c0f060c0b0606030903 71
    0x1d405101050200c0e103000c0b68254000c00800d00201e000c600503901041c014140403800e41400c4000391141c0c03110152010360500d038200603850306528904103481c0c000c1c01d140d1200113079008141c03e40b1400419903680002409441d0601c0d032101140d40414554004101040c0e0899045030079418000b920b49600d08004024090300340c1b01910318880050260900c03409940200222030141030b02c0b1809803100c0000100710b120a10a1800550002900b805186085604103400ca1401d0b52840c0424207541e40301400c1c84c420000400103000983c0c4400401a020701810101003030066606c040c0b0107e00911180e0380d101c24105600ca007101084900881d1038540c41b403000703425041020341d01c2c3e40e521035000f582c0341e1250412000107014602c001807a01781c1d80d01c2c02002e231a4000314850428401c410403103400c03074884007400100900030800103038001e080441c820255001b0540c120340c10741005540300600300c0640c0500200500c0e928003030b01180c910014181c200000b100d1030f543d40c0e1540d45415146 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 998388794 1250 998387544 998387591
    0x9080316030311070215031f08030421050607020604032d0e01050f0c0102040f05150d0c05040302090430020616140d0b03060a021206040902011119050f01020702060409 74
    0x10000403414086c29451001341d4403d0200c501c103d91404800701c80b00c1e02d080c1c039620868500f0f178010322040c415207501c03505074101d01b41110400300d0041c980c2e403911440c201c0240c4420340560000d81c24407040c19881000c22260500103505081c0d6034801c0c0c0603455503c0000c000101c00c03c1400324072440305030320560444000e07071411400c0c65220000c40007040e000394003500c5200e000144030310002031103040a000401c01c0504041099080660707041c031800107020900c44040030813034108400310040e40d4a03509903018601408400c034100d404140d615a582000440a071441d007070b59100200b08940c0003074559884451300034040600c0d940d01c50160342c0c5c0d1032502001038403410041032140c01d90035140d104100c903240407003c0310515200c8020980c203e22031422040c1003282030348001002824036401400c0150320600d080038003001d115840d0b0b82005641c2800d044100301082491040c08401c002e002d1540703003000002c40c9840381c40d0740000c40314401c81c842d80000700d480b0b4268000c0c0365942240c00303c0713 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 998390044 1250 998388794 998388799
    0x80702070909050f0d020a02090109020703030f02070b04051e0d050f0c01050115120501061409030f01110c0c0f06070f0c0806070f02010c08100b0c01021603050901090803160303110702 81
    0x250440c68a000b91300c41482210000d03161107040030380e0060a20014403e846107401804440b00c40c1d0030401c01c100a0751014a0603403e00d5107070003140818107001c3c80100000c90281d05000c00c43d080c14034040b030400102aa2140103121549a00c1c84401340206408104030154140169100c1e00710051002034022a040800554680400003659101c2048641d0301c01145950304200c229005400b40e003181c00078000c440018003030446c84c1161005c00c10007020418130007400c442e4141c0301030013030070f080da1300241120303a6103040480c001540f00e000300b100305400c18081313a22510f0071469101140150017241000351101601d41e0381c482c184200000c00101a040c5170050b50084d25003280c02501d0382c0b8011240800541c81c0c12586003e1a00c80c0d00818015221040c0a0b00000d24041204c4126000340720081d03101c0d5408c115500b00b040030488a1000184251100c40d1901900c500243c5100142d6001030046d4104020411040d0700d5404c4042e0050340c503041c0083e080500c0600001e540c00345140c000d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 998391294 1250 998390044 998390051
    0x1212110405130f0218100c03020d1116060216120209070c231e160317040503190605010e150103021305100c2a03020f1c111509010e010807020709 64
    0x13a00782c5850685c0070f101c000e5989100078554242c040b43c407035405180c00b9005800044402c41c0c560700c242e2100201404180c01c8400d201ca0b2103646441803ca1644598090f901c603600510384001c6a000140041035000001e074019a401e4012031000c1c40700500d41c41c100200460f8460811000c40c44100d42059900c031120300207200c1c00c0c129583d4000d49215000c40000c40c50441001030301c0001c0c07405101d00490710144195180d503849a2440c501340942a184c200280710108040c0c40800c030380d051140841d0140340300598a4101031089034810707007001441401d46410040d07008039403031246095100030b10380180c4d100d0180c524800b82c0f04154200f1540181c04207000304106030300c04005440f050081041c034412001700348a55202502480e162808244c1e21038080000d0b00e80b004162014400280602504220042c1d402c0c00e20740503103c04945045ea0900344010302c0c101010840264640480da0700c7c54003101d40c0018007583c44d03400181d8100030500d0009030919100703001c0ba800810b500142030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 998392544 1250 998391294 998391307
    0x312071407030302030d0b0409120e01031d01060906050d050a080d09061b030606080106020c01110705210115051305040c03051c081521010b06071212110405130f02 72
    0x29101c2d4410074100d242d0380d05024500c0540d28181c896271100036480554a1602020440181d07a0b1a642030442818142e60b084203400b4281e982c1501420034036a6000011007500784081c0d034085801c56005280980742d569509800030328002985084107400859803600d8501c00c0e0042c0c0040c006503c001000c11f414424014003c601c00c9110241e0400d41d524280a15030711920100c4100d0007d10503130b001a4024151200954040d0203040c020030740c100c0554280c03a84038000309036025648410003644600110b0700c602081002c2c41905003d000207180c11603481d06c3c07c0d0015441a9001100101c000e540d000403504000075801c007103008541c0711040e60300104d00c0c10740000700c03600c020354001c0108a5030340c001369040d901e008201444250062a40c000b11410000e200000411075016090642d80c54042034401d903100b00181c444140728403800d20107011b010310014000000b2081621089062041691050603c50260740c145c42e030581d4048a44550642c2c80e1014102030500703042498030000d2403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 998393794 1250 998392544 998392547
    0xc0506040b03010e06100e19030501050709150306050102060403121407031b0306030f0b041a1017030c070506090d0213020306030105070203030405070536010503100b03120714070303 80
    0x50b50407030701d8541c1c041c5001d0340c0c0c59052013134040ca011040000030725010b041d01c02a140031803040c0b11013035603052510445900c0f55649802c4500546113080428000304040114482c445c1045540140301d03d0180703c11850480081d698640180c0011309100f042d10340341c14480b84642c41441c01001d0300c0002100d504101030084c008255004000040200c0040b07401d616034000d0050000301c0f64040840034540300d0546601c07a8807100984203c0b1021390b0340d5025000c0b504400b40e0f8500407441c0760880d0700c60919000b4104402c82920104c105a07400600220902d1003021806804030ba1041e1a041e680c0d109103030000300807840ca105c00960242c08440c46180d1a81d0580c081d40c8140c400350001c1110f074840d4201a40c0d6408125030003040b9900c480801d0003142070504400f8844000300003040e02c030000b0503401a400c1e0f111175441c3e003045100e003401008140703000c2100250301c0c590b01904100c43c000660219803076000c081c13014124400700140d8041041790084051440074000c01c260b950030743d180e150 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 998395044 1250 998393794 998393797
    0x703030e061c0903030e0309280b0a270b070314090604090b04050105220b01020109170901080c0412110d0609200a1202040c110d02010e10020a1b0c0506040b 69
    0xf400c2d00007a14040320040700820000484125000080ca200104400a0f500e007001086079904e101006030380c800b00141085648028044140389525400311051265a4070300da070410009c40510340208210702009803d89030f5013180c1445170145070181c14807089222104440c4900d180c040e030070503000240052403c40640c132001203000122018001a681c5004005040881d0400c0090481c01c9164560200c1704035807003040015418000864180415115004403142080105203161000581c000b0310b9a40f11685590251080084900f000c0c01e0804118406400141c01401e0041070001c030034142c0c3d40c9401000c2007503440328080c4801c05192400b01f0f00306400c1c000011142c030401c142019545840c0149900756500701c005072007851290340802c07001d40003800c040c01c00e0051119660030502c0040c001001607200903000841e20549086400c0e1400e04111307402880c0c9481842200501039000b020000c40000402c3d50551800440c01d0080705e240c45644416072055000500149070724007c070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 998396294 1250 998395044 998395061
    0x100501140a0801050d030903050d080103050d0305150105180a080337030218040608012007080d0b011101141501170703050c0d0e0c030c120703030e061c 67
    0x280c5a01149845404000c154098103a410010681c0d2000501190030009549810b00d8001d2030985061070303032603c80341e060880ca40f8032000007a064100600c144003041291003010003240c44c08000c20720708410414800701141d41c4060401500140709401e0031424090450744c00d20041941c103504c1d0b91140f120741e0b680e020484158180b006103051203005480e040b003140b505680c2041c0c5030295261004114002c0d4800d82c0c3e00e001ca01510f050094850321a0710600000d0005140001014054410601c40016000030b480c04c07159010000b06000401090a64621842d0f4070300c04181080c0701c900613a840b030701440b90301540750328006076071400d44e5440450310f0282850010350520700203d4001119110002044c50321241c0301c01001c07420f02482980029440034510782154240304110790302006554400c030f83c1c200b0580c0040385010561406009603040001c08851011010000b080015150fa400b444042d0a20a0005602101d500c808080343e00c40134164100040c007840300f2a80701c00604259 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 998397544 1250 998396294 998396297
    0x1020904150b0304081c0e0d02011811061b1203060a170a2a090609060b070b0c0a030902040207140f0303100e04020a0308121803030f012309100501 65
    0x70041103007492500d00c1c01e010358040c800003500c0c3d40e80700c4d280c0394500d070312084031a40c0c407144088044840c4083d82c8070703034410050108090407854400f000b0007801d5039103862040f000e0001501030180003c0100701041c81104044e0341558842c0c1d504070201043d82100c90703031810540074408240030501e074174070010341c4190350480b0a0103513192680c1d032003604c2c260020b4014402d68000c074411030100300c050141c22a4200522000d144584403404102c9200c40e0a622401d000ea85504050101039440d00481e00500f2124079001e00b00305a98540300b02d07141d000361007054401000541c00580750b00c00c0d0019804140c01910a540e07c5059180103040c0e06030f242c400105501440d20000d02012012040707170300070402c8083c41c0c601d950901904091500e0301404c1244e02500440780080000e401c0405030000c40c0310409510941c0c9818840d4281c420300305119030030990010410088075501015845040d01c000581c0110b007021221464000903141072100b0f9404020754040011000e0f03140c1380349054032000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 998398794 1250 998397544 998397551
    0x1b090f04180c03260313030806030c060c100f0c020c01050d02040509010e0a1d071a09040903030203100b0a120b011116050f0621040c03060f1b02060f06040209130e01020904 76
    0x120f50072103a0740825940440c0084580c45506d0100b88565945c0c3c2e0842001001d46104101c0c080015120354090b01442006402c4408000340e400310b2880f56003803084c8030301d000b803000e501c014030029201d01500b0717004c44c18000e02145548030031390180e05642c0905000b61400d48956125682405405401c95203450f590303080070101000606079040d0511961424002001820b003401404918501c21031204540c9c40300c14040701c072903507449000f00441c041c002e33103006940381010646a2440c4103550404140194104110105140e0200400c0c102c8400d401c00021303082900401200c41840d8000008518458410303134040170511001000111002128166070440c0001d044c01894020901c1d00340004025601c294507442081c000b0582c41441800c40c0e884540c1c0b03d6403280100c40801c0d03d00500240e688802510100761840d0010030f80e40d450000303042c030b4604440c002124000c0107003400e0049801054014107900e902100e8120504076031020b00c400388040c4030f014001c2d0061610540704504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 998400044 1250 998398794 998398853
    0xc0822080f03190e0a150c1a04020f060a090612020720031b060f0c0a050601030507050a090203012d0807121a0105131e0c081b090f04180c03 62
    0x256542100b803130b8014010717003081858085111003280c81e8410000620008801040008a4030038001820300c1e0840c420f4030309801c080c010f02c039150070304003003090251008000e0b10440581001810301100c04526018082040f0003255030040d000389100140561002c0b0420050002c05c05111800c880003a004c441204284410b140d484822000c4003541202c000c12110782d8141d4520000e11038250f14000b00c600410540e901c00303140240036403056507031740c00c2140140000c0c03900048260041c03240c810154259411306c0c40321440450780003400c44429040f00040d0b090300041d01c0445004203006826074507100d99500100c1c2c1f0103461010b0480715034038000040043c011b41000840e059a1001d010700d40c040b2001d8110ba00102001103044481841001011074400007034011200c10304070565071410300703040942d060b2040403a950f207a0245094244103c0b904e584440c4500c90702008116404601044071120114855081c1000500140034501d00441030100540602d48944010243c509107001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 998401294 1250 998400044 998400047
    0x60a120531081308060114031f20130806090f0703081c020a030b09060103140c070c09181a0708040201052107030b010207060c0822080f0319 62
    0x1034003081030410802041d0300100d941494031040d0440318030900c40c031440c06000440d02101c038001d95004904a601c580018810130095188000c19484242c1c000d00010360b01c107010003c8800d1054200c054181c0c1c50540f13146000c18081d41e6000b00c0c1404440c1d60703503100c0c0d418403007080c03040c68003600407507100382c0c03011501c5038100081c0268000d10000c0035010207030442d41c88600a5000d20700c0d040d03030728418802e0400d410040340300900c00b08025032800618600001c3c18804241001000c181c14585001c00341d11001801910080e030141c00d180701140e0307402d1b591600510a41d0300341c2280c12501d241054505002d03071203521551803240103113505003800b0716400101b03061141c01c0310040d00141c0b224010400650095002c1c244a4610f804506402100320b11400c1c1d00b07010440340f40000940b01d55480c400d5580602414000d0b110b00e2400004034046511200d02c60f02c103070025050343c0e40307030301e402c030707041e2400f08185400a0503400040e65864200c002c0600e0340c0e50440d0482c12420072224100c0320b03078103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 998402544 1250 998401294 998401321
    0x10501021e0307110d2a051f1103130909020909030309120a090806041a0606091e06040f03140106170d030c02010b06070b09010605030c01081801060302060a1205 71
    0x380704040154a8110141c2c1c2d0480f40102d245402c0c0d800007080241036000804045001002186c801c600341540700a440c881c0c2c4038078420307500850003450407130080030b40a00041640b4105078034178241241c0b8207181400b0300b0318620920780d100040140c45e030000f043d43e00894016146032402201c14540e02d484001665840c4d20094411032010b5002032904000e151640001d0b0546520a0518034803403a560070f0683e080c80030486040710032200c136030b000d60081040f40d2440c54028405440440c204000f000100e00c20301c608240c05455103c03002088000b613034503e4110b501500c0014001d00810b5980c3c50700030783c82442a12a43c0d0f541d400d106003c188005809400c102400390302000f040e03014041d10003a0014000b401840d411035403a500042c495450b45001019402e00c2801240c0e2146008038505085400360780086120741c0026000300d0f078980e4480c90f04ca401c211100140c2542c02481d180140c010507c0b644000c3d0041c03000301c3d41018094100200f8022031410140500c443d90350b8034402c03100b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 998403794 1250 998402544 998402593
    0xd0e0105063c010e0a0806070201060b040f0902070804050a08030c0f0a0c0b073306170d11010e01180b0f04240608060c0403120216050f0102100f0501050102 69
    0x1207556280d50011040b0507040c070389650041c10b0524403070640b01800891a910815048120203900400510070942c0d8240b01d42c20040031001d680600b0507050507103041d4050383c148a2110003d07000310b100420b00c48008101c0f00108002405000c0c0c80c0da0350320b419900c0e42c10240141c90940519240805140ea0101d00a1080d0307a200e842e06109504190140106070030013441541e80c11843c03100100707401710582c800d51100c442d000e140c1201901c4040e44d4400c0e5400c9400208124056940324044468000f0f80031083c80042d06050b000d07810f0820056006048500c854103c542c01c1a05410310190f40c000503c42c114003c440303485290783c1e02e02144040d100d003610b00800c07924481c0b40c1421242c1d070007003182c002c0c0c40781c02c20017040d0b1076550842107152240958990480b4040002c0410411010b40c04c44681c1a45c40c1c0080d01c00303411417501078407121415201c1c00d03025202922a81d405a0f00c24490400c0c4030584a2041100301c5c0314503001401080300b402241e0142c8244c001d0302d129200c504810401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 998405044 1250 998403794 998403859
    0xe0708061b0304170d06031b06030614040b01050c0a08030708131a0c071a010816080c040f0e030a320d090212070e09010f091e03050d0e010506 63
    0x20356151962850300e010a2045130740785424041c4500c41c0350700360500603240107501402c9074045869102000340405071450b408102030504d032201c01c010201b0040d00780b580542044a00150156880300146e403c0d01c942d02d000001ca00400031005c082150910141d402002241c2d10000075599042c01e180e800301030341002400d0b1180c400c0440034030141c4d00c2503080d07005185284650501800e40c2d14841c44071803a01d5400148041400117200c00d401c104102c00349501540014819a1b207022056501c90040c01900c1c0c1c000d5854000034650301704d003504441c1500014104490b641d4601d64401003c04110407510500b000080d000c6200003414078000078801507e58200320b18100f94454440d0090014840890300214116a0080125411300c5494020410142500154607011500508403a52483d00d21212490250840007090000002017a80c001c1c01901c001c4412260906680d103010300002c042c0f40300c0c1402d41102400c0b4041d0170071405050160b031490700c80c481c03900c954980308481814441 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 998406294 1250 998405044 998405047
    0x1080106050d21050f0a0908010c2c030102070c06030b03010b0303030108030a0c02030109050304120b130b072304060c110406121b0b0a080106080f0601020718020d0e0708061b 77
    0x511140c001c64450032407441410543d240036090080314100b40c1207506c006020070424041000750803c207000d01c00c4c01001c036181a0003071030500c5c0154900080754005414424101c007540703405a480035811220800d4000012402980d030391800100a041500c00c00c42c041d50a03d00c00c80410700307002003034a05031800c840145003020801d94080b60b0201d284030050764550f48901200e0041403081c0020030190156966032005240982041c02480c5000341051040e915040310340b07804698412401a00b0108502d0907580725000004034681c0459190b455000c0603100160020324241c02c0102c00c24401d100b00501126100f42108004c00c4503481c0c4601a0040800400480007172040d443c0c02589142c0c00d0000c3c4082611501d04c3c2c1800d800ca00809c801240000c40140182508040002d40c020409808c041c81da2510500003500c4980300c0c4a40010010b0403407001c80c86d040c554066505051024804019175100c0303083ea0b43c0d03510940c3c4111040c5020302c0011a050490320000c0ca03244110710354171207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 998407544 1250 998406294 998406323
    0x5040504180b0403020721020303090105160204050106050c0114060a0909290103020a091a06130509090d0810120215041707030309231e150301080106050d 68
    0x80094241d0080c5800a80808014803000070462205607000da03001c0e42c001c0c9091410142c0242c10514440c4583c02c02c9040c9a80560059500000311946e480e020b2920585801d01150405040600254002e5201d400d00001184059108028200d50040103000707000c850480850308583c0744041c0e501c43d420203e0740340f003800300350310315003180542c54072450078052100c100110740c0c100100840041c0b0506d140d03a000400551901c401e91101403c0105420031610304001d07038541c190381d40884142e00030076012844071200c40c5d100c1195030040070041c01890103403510400042d00e50710046400c02c04248050003041c5284c0e03071030782c0d4031040e43c2e1000c00c1050450380b02d80820010889507640009200e10070400840e00c011070188028030702516400515980d403c524015084801d00c1e0404080001070000044c0c0c541080c040016184200341d48210800514003002016038419a900640141c071103022090600d0aa90007103040392503a40c001c1105548441c100800e19a5203000034020500c0321103c2d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 998408794 1250 998407544 998407549
    0x5070c030b09150a020c0c090c030a0504050c040e100f090b040311030d0c030c080702011104030605041a100801060f05061210180b030c1203160f0b040609051606050405 74
    0x3290802e88000403500c5010510316140c007100d1048800344005034000c54900c42000041024041d501c50844500d00b0501d4510f05010160200a105c501c400c0d440e207002c9418090240308055080001038014004a8002404030343d5451061a40001e070038071b8001601d030208131901c40c01854550003a202c19050721280c07421071701c00740d80d2101a111404104695881440d092041c03003030310b80007510081540d558000000e01002c500030f10040030344e41050760b448040c1d42120308039070031782351b00050005080c0ca4606000151082c4050107480c010105010f001c02240500002d000300c4104d50000d11001e0780b1010003d100300c2d41840340e10b0b080b0343d007440100e0b2000c0d41c3e03101d05988901c08034034440381d040e69194803088010b14081150402c50355100900c0080c01d0031b015034088414252480c0300c00306402c001c069503d2050342008000c1403030040d07825081040d41c0c0c8000b1201504603040c0f5038a4107160420400038511242c045031944a60581070b28110350b040384102c22140991549420240349c0300c103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 998410044 1250 998408794 998408813
    0x40c0c020118051c1209051014070b1e0c18040209031906020c01110301150c29010e01050f0307050907020a0c0e10170a020f010302040b0c060a0c05070c03 68
    0x20001d503188240d00042143d80f100c1a0300a0903140d6198444d588503242d0901806040b8018034034003c200000c6000d02554a9a4004501c0c03c800c501d4103a03010301916a03080c883e0302440400031b000f1001340041c01030354100313100b000702c0b44840d440d0885d040e0384611141100c6840703029400000c00180e45001c04151800740d0182c0b464000103402d840310301c890013001c0841e091038258100d410541c0415070107003e074000d1084440c8003024101e01491941071a051070013691000701e40d94208503c2504c40003c02150000031000400c04101c40003101c15050001c514521090160710400341205000045900d40b0801718030075100c014001d404e155040805000c1a031784001c001005501c6155840400294010b428030003c1015940c50390590411141490840c120755002d4545210554440b4443d0f080128010250f035504894801003000e041005901a028a50007101c1d106800700e1001c600003808a2042e118006c041c008101d411149841070382d25001d001c401030003200c0982028030005e9503586 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 998411294 1250 998410044 998410067
    0x6021606021203100302131a040c0509040c03110319050a06120b0a0612050f01050601090b121f08030a020709063b160f0c08030c07030c0c0f14040c0c0201 68
    0x600b05076491703143d030041200c0030f5070407441c1740d641355541c0380c2d11800c01c04000c14049641ea0841e02400881c1e09180010028015513074018411030303440000301f102070f00a5105100d44035480c2c404507181d29140540b583c03540b840000f0204036508120010f900410248160f800b42c8a04048681e05009a62103c140b4080e000f410200c0c403554688001ca04840c3c4010506400c501c20f100130701518110120850035038101806181c1402200041400040420070035600c40d0300b050018088603030783d840304483c07041c15484044502d21210307220100312120040300411240e2159002c0b19019079039407100200311446481050743c070341d11500343d40304180c4000118121041004080c2c8080304e1000211070482c1030300b51643d00b072484010001841081d04010700d500281e40383e0070300f208410030039198101030b40f1004240c400603c0000802d181010300800180c41499000141640a0b9466094013043d008107409450860f00320a07030214120314040c050030b51440c20940e10b61404803000d40c01564881d5126 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 998412544 1250 998411294 998411311
    0xc080a020705031002040504060803030105090402131104030b042a090207030309080c0c0102060c2107110f011d0703020303043b07030b01050703091811120106021606021203 76
    0x50303000191582c3c1c100600301c00c1c00280e440040c0d88030714050403c0121b81c41640980c00640040c0010007056480c0400f017540540c040d2019031b480e000f0480c0140080810181e848060a0301103404414401c2d044d801e03d108034403d21211714010349a158089540c1496981d050700c9000f1000180207481c80303070300981075071803084c00d010400d150582e58803500f6402c038621400540c2d01120070742006680c108000c94010b070f6014034840c50101c91a600c0f00c414054901c042105107001c0d0003080131188038400c00862150300c84280d03542014050116400b03000800c16140c2407006141126040d0100816807000f1a135000380110324107850601e5150605130070303003c159a1403003103a910905911010440c0d05646154031403441c2c0c5840d00c1100502160782c140101d40c10040c003030083c1000039030010300c0b28080e904040800203281f02102003a401900311349224a040d002d0100b22004030f00c48000900c1c0c169002502034a940741f14020900010551611603440140e00c480c4078001846071042c011500241107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 998413794 1250 998412544 998412553
    0x10f0e1f0e030109150c17041101090902031f08030a021515060c030403030f03050903070204050c22030c06030e0303010b0c011811042d022206050a080702030a0c080a02 74
    0x1d00003a0840d2104a8141c81040c4410102c284030800d62040c200460890300380921802c001c0164010226402000103007540e0801c203040860ba17006400c400000c00355007005545d02e20301403030010424040c05500c100c4030b0081e41c0f0046580310000c0159030b00c0700d19680c001c1c0840341000182082104014101103003080141028006a0701d071100205410041c60000f1640d5a01c5d5140007441602221185401c240ca0f000074030010040102c1121a9160102c40200380382d140c60040340d40b58441da004400c0c1d161650051b908280c00d60001b89000c90740200d2000180c01d540b0041a81903c048034410080c0e504104018414400000007030180f0401400000a80080d1003a0f00202245400d9054400c040780ca1031003d05450940220403155503805411107406a0310074500c0b655614501200096075008940041c501c0c9100d4880711081c000b1040c110302e40d59541102030000e51140403400c0004e42d84a0025140c01e0000040b1952403a460341c0c0c00d54152843e40300c200581c6c0200380700904500a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 998415044 1250 998413794 998413817
    0x30d030b1c1a010801110d021e0c0703021c0503040303230a20070320040b0d0f05060c0a020c09180607020c280918060515010f0e1f 58
    0xa00c504031a101481680c8035290903902c400d02c141100416845105a030381410061098005008243c40c07a05d00304000241c0c40d00360315401405030030300c070080340c6415210126590001220001e81802142c4c0251340c078440301920b05102c01c540c0b00150700b000e01107610800c4200000782c82444c040240f41c0c6081742501d400740790460f0501050f4040305400c00010b4590403500008619030945048080418008103030081c910783c0e664150100341c103602050100f16191319070403511590402000350000400c0d62514400310b140100f02904540c400341c500d4801c2d00300290b600301c0c17480200e40700e511300c5800400c80342c6549000c00c0015440107109a4807040c020060742ca058604100081c01426a50040d01030b000c0300c0c40a000190074540031310503051051800403440202d00c0f000300e00c04e0701e81000e800b066101595521001e400ad101c400101540d240100300702072662400c0c20060303a42c00c240d80c2d8044040b0744140c111b030729070201e08d280c5038040c91841c061200300c0c005060b542442802820003070740508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 998416294 1250 998415044 998415079
    0xb040f111905040909030503100b090a06270305010608062202040903170411091e0606030a0e1f05060d0308150a080f030705060a0c0203030117100513060606020c030d030b 75
    0xa018103000c4011030808018000c27081020b04034803000e00303002c1901501b041d05100c00a0050b0080e4450300052080740500504149114070000f044803c60030074070a0070b240ea03890414001c20303251055848502848003c103803651204019481407000120004d9113100f200d4003084003c0900c40c60441c280114001e043d6894022880c1251083e8099001800c40900b0001440b2090758014594840e44640c04000e034508101940010b0300064161051526035940000e030300001d18402100e500c00303205018500080d100c040c6c500c0740203020303045400e1040e0b440c0e103820701c41c6040c0d00f80d10040105071207200150001001d10712040c4800170082c02d00544035507601c041c50800481e09a10034242c0c0000034030310140320081008075049000d01c6410403085400e0780e4001c0d201c0c001030044000c502029a2000c030f0007081040224840d20b00c61500304001d040044042440290750401100d00505007070700040e007a400031491100240b4094090b02e800c2600100490040601c0d8005a50080000900b8400c05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 998417544 1250 998416294 998416301
    0x905150c0a1406071202091e0a0506070c060e010f05182e260613200c0d0804200301110d29010207090527010b040f1119050409 56
    0x10301d20b001d080207081208004241040b20007118000b1401040b51610382c0d100c01e403489000e400c040c2e81c0412446101c00c002442400c4540c04a41e001902084000a1011010b10141103a405440b045080002c5000640e112010f003000c0c3ca000c0b540c2071066581c541d5143d8420040c508004084d44d60007000403403901da640c41c01e56020102855800100d000c020341280c3d18030000e104600580000070002c504a02c02d502f00207040d41e019044c43c103d01041810541c0100b0781c06e0404003c0360801d614900d50200d596005081c0400c59817040c0b41d15403c0035030040444c0c2d401240c03c2004000400030b111030501c041c00030340700c18507003541d6a510080c1c0c4040000300600691600c070503000c940d40301021891718825a8400380d14120030814088000182c0e00061840c2c1102c201000100d1640c0d10390f80f02d4055042800d46801c910049240820f032001c4065021003403841044a0030403080040000040c221160621616000f0400b0407041d6003011065840009540c8103242c024500741e12002403405a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 998418794 1250 998417544 998417573
    0xf020f06013020180103060c2c011e08150616050606090606031e0c0c06040b01172d072c0a0e03090f01030605220b010905150c0a 57
    0x103200700c100e80f030701c0e00c2c0014081c281001403c071100100d2480c00d001c901419071041c40000c00303659941c040c20000300d016450480e94403000701d80a031081c010f0078541252411091203800d00055a1200308613410b81c000c0b8115034000307002d980d04031807980c40180c03032500c0c1c0725408000c03a440801030240078042e42c443c603501c1d40058400e0003c5d00642c1032490501500030005400305100e00340038020407595551203a0380010742e51100c1c2c0444816183c40c85609454824540510381070300030501013100f845900d2451b28122140780040703220815600c0c040ca610752190080b00302482031a074800100c2580300b105484081d001510543d4000b580d9000c41d020744032401c5545007075203180306c2010f8040c52011011154420452a000d01150b038501d821a40c0341c0c031510b03401610402600d000d10345185d201c0d51004001e408054003d01e05401810280103032030b61482400317000b8070708004143d1001d51041258008440c4040c0c050840328009011491180d04070226503046446070007031490200f1841e20b00c8104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 998420044 1250 998418794 998418803
    0x110a0c05030f0a1a060103020f070b07022b0c05100501300309120645020a0302090a020d020a051803011109041a10050a0f020f060130 59
    0x15140c5800c090604245041921000a40158030000042046100701c41154051801c4000443d910600140c009015401c00303143c190001040d6202041040c0c1c220030f005507104d03002c9035044400703c22000381c001201c04613841404445c1c2c205100843c0180d030800c09840c41130301952803940140304260308680c8264014503081d548c9014075541d245001c0980c05000d81c09458103119155941c902400442c01c5124100e8074601000036502480780f50f5100223841c01841580400c0d801d81c44000d10000d80420421010360503041d142100d601c400008800040c0e58041c101c1d075001d6181d80c082204448009040e02200c40d000c10003044d02500c51310050050210301e440d00c545071941e0040010908829040d1316010340e240000108144c1c0c010000e03103000b883c088a000c1900a11283d1502050500404a13034004015480000034190040060004000141d98904501823031300000c0380d596108052500b05c64100c80014014a02c0c90f103007811000d655018407000c1c0308082d03411400a4080c01c001601e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 998421294 1250 998420044 998420063
    0x1504091a04090b1015020c10020f15060a0b0301210804080f160e060a03060c020c04060902180a0b03070e2b0510110d0c090e04051605100503070e01110a 67
    0x202404d0035914040540901a010703111021030500c042d40d40c44c90136044c1c62044110b4030001c1d042c0780c401c00ca81003d030101201642c0e9841c81042c00001041000d45041e40b01d2140902e010500400c94016a412030703400c01d91203401554050f42140705940d5901003526909010040816141070070042d00092070b041c0c20003803002100b01309844031180082e400020345030b02c0c03400030702640359104420310040d250005000684090340e2042689400c0040d0300040c0c005051801c00030b03c0c0c4055602806e00c500b14069081011900300342001410040e034058224265030501c042006c0921914419006441c0a81107003070003410440310034041d202c80c155100443c1907400e0b0100070400c0601c00e508201c44e800e0402e104035030b410f0890100c98050320030404c1507a81d070340d45400c001e184580c00c0036006040908280071641005e0800039207401c081d0415a401540d902400a106d04091038003000d4800241c0e00c0904585032003900b2640403074040540c50401030690b000c0030600c0e0060040c0c03100c1078850044031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 998422544 1250 998421294 998421301
    0xc0b0f1e0f04122f2406100f020a030e03010f060305011a0406121b0b16051204030c0905100506030703060602010608060f010b0c070306021603020c1504091a04090b 72
    0x3c402c0d0618101082080040540f401081c90001e00c41100c03c05540d14141c0c40b8221003ca061070006400c18244a10030440c0d440003180e00d1200d03420b4021842601c241883c030ba6000002d450070b42d00c2c00c80c0c540051744000c0f01c98011a105400c505000701c401000820348807404d41d0605d080d03400c603410a459595583c804901c00c0881c1d5840c0000001040d11f00f8482540b601400e80040314070004041e060340003442e02000c01100340d845060107040380c0030b001e0307440d00d00109114122456090342140e6a124000e030946440d411070051b43d007103c1d8800c019100c0c0301d00b010703146000f4100262620307081c2c0e0303110740011400781e0b01c400245101d000d031aa00080d0305813500c0c0c0c00070700b59185680420056000002408107040034080362505468140c0c01050f80e4a4210803594a41509a4005000e5501c0428502e850b1240c00110450b21030203130342200d072072414017020084260048001b16051a10410003040030884503084848074036000c40b2520882c000d000701090950700040d8040700c448020f503040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 998423794 1250 998422544 998422553
    0x712030506040c090b16050a12110319030e01091a060a060e06220b0408070303030c021b090919050a031e0f031512030206010608070c0b0f1e0f04 64
    0x5090703001104550502c084002d2080280080030b40b4001d20b5101040041c02912a40c6200701c0c29081d182e003d01203d81090b60390a00c91b5805074401c20510000301000b0155022030303400411f413132008420441005c4032080040054004000c29014012203540b1303254500d0104401c00c040e113828410602c04500946030820811013030a1440c1c000c203061040c43d11a40e001511250240c0b00c6000d00d041480c0320b800b203180f040c40c42082c01540079041e0f202000a001c2002940886c003402100d1107030f20241300d0210380d00c00c143e8882a8814461840c0d0031204a80d075450b00d09500901e811541c0b072001d03250b42e0410810302c51450011100151500e9021200d07200030168000075100701c940d164a10601048009207004299121a039904820181c482000c1c5001509403210b0b00700070312000486100d031850074035020352112402d01c03603c408600e00d0000109480e003e1641c501c1c035954415a0260196030f141c01d00d405115010307000700c0f10418200c89401c40c007840341d80034901840d10411103d00d14602883e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 998425044 1250 998423794 998423801
    0x3241305180106230d02120d020d09060c0515180a0804081c1e02150405060403140a05220b12013609020103090b13051501030b071103090303071203 65
    0x605000703141c135050303c1d80800a1046a44282c411107050700e004509000095400102d40000c080500400c4003411a80713400003000c00d11f400507a1038060742103036192030a961007144130308040c00302d400c419181d181102d41480001d5001140d44001080c030390b6003200c860700d4400401c0007103400700301c009424810348204202c0c001c44800740e20a410545864403100070b0424440c0b00000c0c44c00c04c40c0c1080c0545140c0203004100030081d01d03040402c5a86080d00300155101d1041e10306601084102204821400c0c031441150000340c09a1206440e14968101c0c0c12602201e6900f81d90640c0d1000c0030104000c05404010100008007404029070703541401c1310b17607600c0425155280d0846c3c8519900915917900039901d5100c100c201c007030002d5010081d00040c1c014203040107004141028460821036032100c420005c030030305405107048486403802e071020702c08012028003018110843c0680000c01c440d10640c18581040e8940041d242002143d4010038613503000b45404940d15040072075017140c6140d0610 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 998426294 1250 998425044 998425049
    0x6190b0a140a1b0804050409203019050109050f070510050a02030d060f06090e0606090f0105160507180b0a091508030304050609060c03241305180106 66
    0x1c1024500b0a1198010b4010058000046248079000c41c01a041c841c1140a170780c02442c020308180a01d10507460485000e000080c01801c3c0790030702221200b01410300080703826408091601d0700d1000b0143c1c401a003400414684640b01e68031800d00c45454101c90601b103490450b1080001040c0641c152400506183c1e0745c1450034070759484010100b115a95044418080502c1b034104195508840001281103114002604e40b085080100c0000ca130101a0305040481d2265624181201e440d508030080101043c0c50301c039071100041c00ac81e169850145828009403505062140c60214000500003544155900a0b1035603001004100102d0000ea030342403101d1a03040400300000035000000a0320b5414078002c568025598002c000d4026480307030301620103420014100ca4483c0381c1441c10659410003100c0e209400d014403030204480c00500030a070390081001403a1070b6040016084082c4903183c202407215800301c0c0c1c0c0740c007144d00e08501d03114190107216440e0043c400311440c0d50503507003960b0555 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 998427544 1250 998426294 998426327
    0xa0f12020721060519020705070311060a0c060e0c1903061b020a06381008040f080711060307030b0307050a1514190503040605060f010c060506190b0a 66
    0x103080b42190340403100842000c5901540004080c0c55404441942001d5001240f021610000e0144248100020094100c912526074020207200000038840c050003012802408551490b6a80000030480c1c0c004000140d5a0b0084400c0d0500620006082c00d815040c603409a20412405000780300d5a401421260200030032518110a04c000009546000b138082c0544100d50751141829104401201007040e08e000381d5080070047c0560040c2c4002d500d110703400a114695200784280150b00880700d5070302c82d9400800110f00007259803240f4540c1e80c48010700b1034081c0c081079103000e0150b42e80307409103000e6841c941e80026410f40d01000c1c10b103000c1b503a4110707510070442003004100854000440d028a10b181d49000c0040c00007010b418803003402403200b004844808003c1c4291155405130146100d1805844240700545901c020b0061005101107014005600352181e02c000c20850340025420600103801c1032001c3c040c0300c00e9082c11410f25000718101c840001290516a03030700100391311814189 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 998428794 1250 998427544 998427569
    0x150503040b1807030210050a020106080109031e0c02090c091311040512161502101107060207021201060305030a1404120f0203030d02040803070c060c03021005090a0f120207 76
    0x103a1036046000c1c000401e40064807100d803464071025401400b000303000b0b40e0b0162000c0c04221100c1c1c03024160390801004000150300e41800000c109005000d90002c094154032280d000c210014625003607040d06095460502c01589007000c01a180c041403070b071041000c05136041e100c4a41004205204101c0c070400004242030404031f240044c801000c5804480c4115004d0358401e402c0c162880c180020041d600051044c20b02d0b00007036141050450440c2021036a00307440c80890303171785980411280002d0189034002e07000c2c028a80003510703540c01401d2141c001054101503900b802d01242c01c1d01c5042e081119140c0001ca90b030000690080788900b00300c50000d045500b818101004000c840035200307009011128180b481c0c10640d1024801c0301e1000103556070956507140c0b42c4070740c656a0b0f403054030215010952108002585032103035a51084595069010744102d807540d2802e01d014110181c050703441da0094402c402e0004148401680c641440340c1c1c0b441d4400559848040d040100036130001a10141 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 998430044 1250 998428794 998428801
    0x1d07030c0e0727091802150307032901030b09010f030305030c040512010f0515090a0b0f120a151b0f261f030c1502010f0501061e0908030d0e0102071b150503 69
    0x107c501c45410411001c20302d07a516540c031000d0480243c400e000d0b8102c1484840c0b480c240d0840c40d280000c3d03c80903000c0c2c07014802000007800b8459884801d100c1c42411160040381400020f100741d0043d40c0104074440c2c100c0c100354980c1c00180520840005049281e0340d141408000241c150148542c0314910340e02c01c10800034031501040b1035840c0140202981503940e561a4410740c1c41c1d6000e000b180c0c5000d0320000000e81c0b01d40384030b0341c0c030100c043c01034605a0144601c0a06c00e50b80d402119814150502c82c061503078500d04090795500003a100c03140901c102107001c03182210545116524a00180c595400c0c030703003040036480703041c0d005c0314081468100060a051010036413501c010400c0b558020415807035030707400b002c04900521aa00400018500f000300000e002c41d44400d0061960321034034255000806a0b240648030144140300c1e42026070014485060394000319402312508289550000d403a0140303658542400b0030300380054802000661505000513404010400202d050900b0114650305 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 998431294 1250 998430044 998430049
    0x715050d05060301090609260f0403031d1e041b050f0304080c0307060501050909010504020906100903060c0f17010b070f11131d07030c0e0727091802 66
    0x2188121510350345846001040641d00c0035801101101e41182c810003150950380b92040303042c1031031068079a450b0300642c450075150030418115018416006c00d050301e010705d50b0350141c42c080b141c8104480d0103100302403690320f60b40718100d00551850300c0c42c6a01140590360800c105c1114002d507890490300d40b14007404e81c00b49402034111090164014090790b2641e882e45050101f41c40303a1321786146507002c0480c1800412500303404c0a0b0582e4412a900090b6540f0360b07000c01d00300c80b400c94019501182e040b0100b131017402e019612103a01041032034000031141d22600c0b1101907034059800d81c00020390324000d0309501d960081a68080c14000b281400155150207482c5056009039a8080c0417450903c0e46801040440d9400600122000e0300c03103a0a00802180720000340920f10701f8041c45000c0b500c032030841010129080c0d090301e602c298a5001d990428403440d00000004241105200d40c111001074101d2140d0709045d014055012031001c500e04100040050345e900001405400641c0022800140d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 998432544 1250 998431294 998431297
    0x80d050301150e0a27050117060103140c0d11100f020304090f0204150903020103180312110c06010305061f051c060b1c1208010b07030c06150602060405071505 70
    0x81c01d5140010400300640d0000703c8284c160f41c0021401603141c03d60310707001203903420303103c004046400d01081035a0782d401c20f003030f40ba400000da00700d80ca4100a006200182d0f8040c04655104c03901c400301d803114059040416944800000190785600d0b01550561251508034440e4050859501c0e000460700c41c1c610380650790340118002e401146480d004904962541503041e034008020080560401e04207900c0040d06241c440d0005a00190601c2d4810b810880f003007005112030b0364150b8501001800d0021624002c104240513802c44450400030342009050401890f406103014030041c100710f00340419507041041040305949041d205c885820041a5541c05552041c01142e0340342500004c290724021004210ba50b050503844440f00c07602042000c2407480158015200f1402001002d850f90b2050701e00040c00d100b81c4140c442c040082c040024400c403c0c005e0441d108100105001c002c01e019000d08042c0381c1c0085005901c048100000c1c003008003c0840240071850101d03941030134221000303126 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 998433794 1250 998432544 998432579
    0xe010506060c101107060908030a0b060a0e09061c0309140316060e0a03050d09082b0c06060b030717070306030b0604111614070609140d060207050610080d050301 71
    0x140e5a90724000403000344504c21590340582c820700800ca210611320b8030300e00f660800d46203165401e16180e1640c28508208040320044101038998540540d420b10400404079001400d180d0403503403d904d140034041e5031074043c8004922a40710b5034291410801046040c16100390050300c01da000b5180b00300e41c24070582c007003001d4032503601d04103c20303000744004190b04d500c4a5100a10742e10901e61342c01100c03940580344a007a5183c0300c080d2042410490052056158085081210a84034064112215002e0b174140014140f0130400400c070350303688049078240c80d0422500d0750b01150048202168a451010b94203512030001d0508208483c11919401125a001030840e4000c551b11150081d0419000003560070307030304200c1e041e403420101600e40381e00d01c0b44000303401c00755520078407201198560043d4180402e0b294a0717102e80d038002c201d0030100140d0640003101500c1169003044801d0101e0000d0183c00d129500c18400680c0007850714401e03528000506002404001061005125688070350035030744c45 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 998435044 1250 998433794 998433823
    0x3011202010314010e10081c110708031c0f180b060103020c0601080a051c1d060f0310150c0b2a04030f05100b011707051308010e010506060c 62
    0x8100260310058004081079544254902066000010111040c89806200350040d00d040c004d032955440d5403955902c0342210006052000f0b45000d86003c1c42507060007812010301c8211207999640b2221a4110762100350a105c0c82508400000c0d00e00700d95004017000314080c8036040100ca600404a0b010614a50b0340040c008040e00e80414584d0307120350141c940d28041c0c08140c680c60f5a4071101e0343d540d0403510604540500030603c81c03e98034045840304800840c4141c0f01d07504480300713140c10400d03507089011715540d20510501c4001c41458500024600c50800040062a160f0404148462681e10300513600100301801d0290400510b0303c0c01401c1d0040b40f48020196850b40310324000f80c1114442c2c0d02d40d102984049000000d00000e26864241c00d80203100b69000d070b0403000a00000d480d00180c141d804640d203d40e01d4500c580d000c5490507841551860101c0c200130f02001e004103500d601341e2051119030345640b42000f00900038440c8a030004021156685481204030840352030304410300401a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 998436294 1250 998435044 998435069
    0x30f13120e06040503120d0c030c080f0a140115030e010b030a0308130204020319060f031109071110091a1005060c100903080115020f061f05040e070302090c0f0301 72
    0xc0d12a202c50068401905000302a2084100c0c182d201c484507410903d049078299080c0402210700c00d01a01c0f5460200203940e4418035580c3c1c1c0d44640d00c408038800341600300d40700d96a03031b85204004d208903000c9020341541103800d00032a6100c0c0005040e80c0c1e0b694201b101592406001e143e140e070f40060900c4415501d424075038480d55800d00b1402903444c184001035001400041005144d01100d403450700392400c0800100903c2c0d488031110038980c0c000c0d00004162011031f81c01c10704649032040e80194416500d1520055021038100e405003844c41810380d6400c4140c803810311000b0880907d0301a449094130a807500702c41d10f007401c982c410100c541d00c9118021040002c40301c50703e81c000d000700701c1001d0300b0402c02c1c043c66069143c0145401c0007403140545c055000085030f09038510208040000d0307000c00c001000143c40e1a8540703648030b10380002026503160065000240d07a2100d0054030902c035507240207008d90500d0360040c800c100070000c1c8580310a000801150304aa00d012040c0e9054480c20030656 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 998437544 1250 998436294 998436317
    0x20f1c1202040e090a0c08070501090504020304062a031a0603010b1c091a07081306020a020a020d06020d1404030c1b0e04060b100e060301090509031e030f1312 70
    0x40d0020300c601e8108225100f114010001100300000d00800c10a114207001009180e42d5090540c448900b405000d001443c1400f04000a01c2c15801a582050103424009148080c81905040c0c1e09400700040000301d0a030814485615054031608000050601400104050940000740c082c8814000e4803c0300744049411810080c41c44030352030100c409204200030805060078050f05001e02100c41e01071000c80311001411013481103140500034502d0300320b843d007044034030b80c2d506010f500f040b61503004501c52801003401690f03075010308103060b90145a00590703a01e005451502501c14405036800d6000054080c000041d51120b00405103903000000c10504100c440300b507081d0703800d4903030012084e400c4d480140300c01e200d10b9910811511404407082c15031024544e0303060f03414502c8a00c410b0780c0302005000400031003426802076540150900180c3c3e00e030029440c14462420003140c130b007242540f8040300308244160030701c2156403c5000c16507a101c2e1091143d65851414605c80540c2040100b030111301c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 998438794 1250 998437544 998437577
    0x3191a010206220507090f0b06121306020c011d0105090601030210030905070b0c0309100219080f0c0d180b0313060b1909090b1b0405060f070c1203020f1c 68
    0x100360700e0660000585c2c0940799104008030141407051502c030050f524203404800107103030840c1280c2210b0740f494040718550b0303900030760380d5550f000604085e01c5998007040704003264582807080d0800c510300041048010091510b4213401c45000901d643d80c15805000107002580d22818081f0401c0f200d4940403c0841c6c0c145000703800c00555a1040440a6001c6a4241d0602000c07014060403103081d9032203d0414400d01c02241d81d55846031950709003100c0c264085021401c0000144840c1640c000241e00d050b280380510b614285290740d02c0340000d420b522802e00190909018407000f00f18511b0564154208080135059034201e0326002406c0a503601201551f940700d01e112000b103801001101e0400c19034820252001d4462490300311040c2200780f00144051041c580103980684620814a04180c2850f0501c01c0c0b0780e1000c2c41090950105205080c002495014103c01800764036145044d0b62509107006440c01501d01d044400d180c100325200e01c1440900401301089105600d0002c0d688118a41d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 998440044 1250 998438794 998438851
    0x1a120c071a0c04090c050901081e010902090312040e06030d030c0f2a030f0225060503040c0b0301090b0f092a070203070915050105070308070c14010203191a010206 72
    0x20b80c00c028102140345680b542c0250203400c0304070702a01c80e40910394410602c22050ad00c2d4008117800100141d005000c07081c200c2e8054590043c2c058100c0e03010178507003905602250070640c010f81c1c810600c2c038200006802c05100c4403d07441404e05080c840f030070040700090142c0c40ca03c104103081120305003000d1180b4001c981641c8903002c400075898505012802c004101000e06a8a81d02610807140010005209c001510340c40101c280c0180b10054107240342141c05a00142c8180e40385180040b0120f918504000158024144100c0000350304104505000c01140f0b000070f01445042c1d50001c0040c40240107200341c05950940c42500103c0c3e1603443e080905000f01003020b50544140d10010035210203603405a034141c080740048090b00c075500e10044034203100d01e0324000e001402c0070000c114958090b02030b410021740314450031070505c501613201c03500320703041243c940645841c2030101c00010384983c8542101d44105940c3c996800f00c4200c0041e541e208080c0c4080e0260a924201d8480d0007039294 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 998441294 1250 998440044 998440049
    0x30a020a02010e040b09180d0c020105040306050a110c0304030314160210110d020f1b0127030f0b040c0501050301081509030c0105010609030512030f01140301061a120c071a0c04 78
    0x51014540c2c7c00c20000c0380d4100900303500701c048584a401e0116000034001d10000c1c407071039416510380780390600790340d0b5000c06010040c0001902c540c8609070750308840d503228080c0510f014900000d40e00d8a255080007050b00e200c0c030b00f250450708000c00040d50100c01070303425a0b0010f6016194a8001c100c0ca050440703071100d00001d0610a40554001c0d1599180d02042c580c0249454100322451501c2c02216183c2401c804244540071410001400215801c2c0042450b01d82c0341e035100882c1c5441da29100c6640280440c10111000c5110404000c20031244d5603200003c0d01080ca461404d43d07040844083c0d45034403d108040b5070401d0100041c9455000300101c1c0c030301a070418024000d5581d2510301401200050004690328000d144c0c55000469254068078480ca40d04540b40c1c14903480c00904c4885968940e980c16019520b44501164801c0114880070021594205241c1c4e02e9160800ca00d00746c480141c050390351008200b00d190081202103021611300c0800034800c85140d00d400004248511556 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 998442544 1250 998441294 998441299
    0x60112031710150c051e0105090c0f090406091a071803110f0a0f0e010f0e06031e1510090e030705280b0403020a140c031c0201111204020111030a020a02010e040b 71
    0x501c003480880401e05a806d0f00c48269000703220a4442003940fa44036050240c0194220310b0014210380035152007001d158125000f400c0004100e0034a85402c1e081801398200f124001c000141071000380d6600c1403001781c4035070a42c1106401c0c00c1c1181d0f1050401000003010b18880d02c280e505d11156580d1383c440800081c400110b0407941160703919081da00e503840c00d02c01d01d0a1010a80400a606070480b6113140c440c00004028020109502608124144034007102c501c43d44601d03203903000c00320400e06a290150b10041d00120f00c86103003180107415039202c2240701e4129002488100000341e0005040b00888034881c48907504819504003581041030400406410400f43d242800203040e00801c0444009010b42501341c0a400c00c1d000540d50744100110b0345400d60300c4200360359080c0110180e08113407034040b071001041d0302122104441258200380301600600c2101b00502c005c641c0c018000c00e0b9103803200e401440c101116040041d40715040d1500107418800e03140500400340d59242e0000d0560f4000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 998443794 1250 998442544 998442553
    0x112021f080c220311040606140d020a1b0b04020f0a030b04061a060d0509100b1c060e0a05010b0321040e04051f09020909010506030705040f0e060112031710150c05 72
    0x1328282920100000e03d00741d07020300d00c0c080700429564880d24801c90380b00e2081000b03a240040081c0098001d610039020300701085060400b07400c00c7d101c6280814034690064441c0460383c1001e004101c0c1207002500e01c50302c900c5400704c04000084007501d22660040d007040380001c415404618520500781160383d460b9000700001280c0e41440b4031648924001d02c00f20045884480305002420300302c80da02c1c0c01659004110038280068520307498100180140700340b0000c42d003101344180951404a904904860503512401006620304040000c0070098000018036809180e40c2c00e5511007601c20381c0944c40c0e0b1420040300040030301c5010072800500060403400240100c00e400c0c2c800d0001c0440c19001ca02c0390310b02101255005405005180c0078903002000342007003624040c10080100010704004d60f0154486d88610050740c1e033800701d9070080842500e03841010b1583d01d8020301440306103d00001840b190018400946500301e06542503030900072070a005840c8a03803040d0381c1209400300040040c0324 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 998445044 1250 998443794 998443799
    0xb0d0804080f060105040c0905090a0906060b0414030a0f02010c1e030f030b120d2601060201021b0313120204020d0c0e100503240a0e0112021f080c22 66
    0x6000810100300841c482c00c0e14101d0341c07a0f1301000291071103595a00006000110144810325101003803d800c00441c0f000060b50380c01d550f4406c01601c22a9001031580000072a08200030304500303500711100a011805040c3c032a01c42d07514510041c4e0f01c160064100404e41026104010034080301404001a51062580c1d02d80607103002804100240024030009040241580c4c1c0780c1451110003000401c240d01070001c06c50141421502441c0d070516880d21100760784022262800c1c01d0b400240600160350015955101d100d40a500c0707140350f0f40142100707510400180743d0151a842d5400b0035104c025076030741d55814503400054064041c0215090450f0f2800b517651050541040702e1928568064610311803000d80180241c07101c2c00201e039008808445090603140304820038901501e1103100030f142003240d607211070601034040004d07000843c9940b6141c519000354944001200e001171200c0105503041501e840e4001c0c50144c0c0038100174044080880c10b46a1050388100c08144180d071091401ca840f070303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 998446294 1250 998445044 998445059
    0x602190807170f0409240b0c0709020708040f0f0321050c1c0e0307030309171c0305010608150102030a14190207051201020301080714030a02060f070b0109020306010f030b0d0804 78
    0x612911171010450b01d0102c000b00008202d042401ca0001c03403a0ba0a03403000d14003180c28150342d20440c1c070000300303008000f00803604090a20207000000c0c01110804e440380d0a04007030b40d64a08c031079000744450311101d0750101f0005174203583d081c1c500b20139030404044402c1e5115043e91180180990450700e03000d43c00341c6143c2d00e000c000b04040e003860190f4030350300d46401c010240b54680f0141d00024001aa0044085c400c0e402203030401f2070340b02c4a803400c80306000e40740c0345054560b44501c1d59442c0082d4036540101310059000c001184c000003da080c0c18505070802001075541d11a003003007402400054a484010004d03035005844050500070058201403266080c000d490302c20301c3c01510300c6038507003075400d480f03100d414400e403030581300c03000028070440341000c40701d0210700c0b02c2c2003000f9418820240ca080058a429014181040b40f400d030540d2607071641d281c07804501c038058106540303803881802001400ea912400d491000c44841c100000c0b03502c40076000c41d4400c400c200b0050310b402c0700018001001d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 998447544 1250 998446294 998446297
    0xa080604030e010f0e0103051b03070503070f180303080a15092c06043009090f0b030c040e010902060c0d090905090703020112140c130602190807170f 66
    0x4038070030ba03a0b07071402451080c0107681034200c1249a1002a0440022091550003513201d6074102c203848400c0148210161418a40c40e401100c12400096010050158041c3c0040050070040c10a0610703540c0c14044ca40c0d00540405030380300140030041000d0210b080c2401550149454101c0e540342d20410a0f1030f440241c02400c090550100b21801c180c000400088003612204860000d1601600b0103840d183c603030101c209043c002060000844d4107882118800984014491a20644410440c0b61811080364225a12601e000602a040042c9910300d44c1d4007080780102414203c40000c1c65010000d00903005003071101c4002d4100c00c1c00101c1c059448000948401c45190969030010b44640b980b8051066480c2603d40d40f07200d502020082c801036000342e0500f500c0c2d0a02000009803051a400166060362701550442e80000d800940400d1940d2410360070300161500340018100b032581e40b136407484440090314000d00300a40214560042240b05a442c10142080030311a64995901c1000d81405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 998448794 1250 998447544 998447551
    0x50a0e0a121205093301030f11012f03041e0302040506030a050c0d080c15010302090108030903120d020f0708030603060a091e1412040e060105071e110a0806 69
    0x204642200120740c03160b49010719403048200380003070021101640000c10455058800726004a9500640f06030040101e0015600a40c018600103058404a00b03101c3c44200460700740750f04206da600101c101010000103021520802d0f14039001c404500f0954003401c4bc01741e0f40112150911011410b50007062914010007540e008450422454407031104050382c80c0010301d401041c6030840265204c0034580948070032950303802076011500c0c166904e02c9030341c00d02d65101108500c5109410040c0709505050b8046409042e030340004510f401d1204000980d0350507002071143c02414001081c1e007800e00140c050b00c80442105070080d860302c441d440c11a0003030b041151500e00070312440d000264110483d018034400103030016000c03002c19040d00307800c841c80c0031b1004064500c12005001010410410002074000c1c2010ba10080d0300ca40c101103101c0391105002e02421b041040510903d0f0200703a2001d40302d82c1e540b0814804810307440051400c14050f6162410035a4409244100010300c004c020628612 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 998450044 1250 998448794 998448797
    0x6130f0617041b0f08160602010e1222090e0f07140d0f05010203090303090d02031c050916080c010e03010c0e0607030e1c030e090135030304080405030d05070510050a0e0a12 76
    0x16498079240d08274202d505100c00e9500c0fa50141605509001c141001014500c154124080b0003d007000d4400803004040c2c0d1051042681d20419480c20002c1840b4070302c82d41c42001d000d0442c0314a410803080c0d090f12880c40c0395208000c429441000c001c0408107910080d40e011000359124502a0740c01a12074001300c0c1c070030a0900500e01c2d4150035502c0481128100b8121604450804030034100b1840144001860080e05100d84801860f0449920102800424615000f000c144186000040242c507503885a107000360705111000d000c45030044800c1603c0002620810f4680105003801c0361007550344403100d5003000e02581e25a0900c0c15845614480d035002c4d84500c295442d0700000d00170030070383c00d01c0303100d1203400400000c4420365030080c1e0904074850003415540c400405001a44c3c10344d80251022200d05000060412007803c1c14040743e664200c07036042941c14a10680c846988400b002c3e2010108a40e881000402d5160540d020710021401c3da822102c00502c030303240c247c0c4500e100340d0300da40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 998451294 1250 998450044 998450083
    0x9020a060201230c0909161407080904091e11010306081917070b0c030f09120d050a1103190615020307060b010e06130f0617041b0f08 59
    0x160640c014083c9500c401c584504003c858010780c850010f44074400380c41c03d0b09011041104810315641d280c80d503805413008601c4622040c0300e80d80098818049040e5100aa8005011150200c0c0606098404500b0300356000304d2100200d250151000e440c421000322140480300c698024441c400300c9071400240c081c0c03800c00000d0307203c59540f956000141c0c0003001b5100c1d00d0141e030000841a000210310386076403664072810910b140e921100788034070803101800390000200030408891800e0400070341000300580074080e4a0542000e01c040392003040c114071101a10350b00810740060196002d03490544816060985a00300380c040c80d101008003548010b511800c007800403c2c0510205812040803000d500194030704040c5541d890050005245010705001e01070201c0704094031980d00400c50b082825418505080c100180c58000f0805900414100f1070b94552441c6000040c110483c1c016811120320f907a0540200c40c442c890f860650018006008e1501e070014406031300044ca501d1b000010034011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 998452544 1250 998451294 998451299
    0x901020c0a03260c0708010209151c02070203030f0301060c0c090c022d030a1707180302040218150d0b0315070f0201090c0e090606040504120f120f09020a 68
    0x86000c0c985400050400b942d6000100c0070298106041c0810206529003d4103003150824030500705426644980d0059400080e42c40d8586009071603900d9400d440c0c0386050524804083c480c2038141e000100400069000803a6801d6690070000d0b02d081110f0544580e40d69038590000800e141d9503124100e4141c0c40d00c04000c103100181d8080d4034200a4183d00400030070b10030444581000e444200ca4500c400d103800c030002c0e505103060000b40403c06035610f81c01e115552124850350304403001449031003041459824291824042c108a100700e0f90115009078507019a034081006808685209560203960040211703404074003c40640110300c15000c1c100b140420040506455081d40c0c2d42880c07410040c0000183e005010b0082404800000c2c03000286d12079080e40c42500c0300748181c0000509a00709402c01a47d58010003100f544500141d4040c0400c0c1400d941d0100a01e00c0d5000d110180824460031041140c4107800e5030382070801c0c84038140140300107035552000800000350103900420241001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 998453794 1250 998452544 998452549
    0x1081807090f0f050408030c1c0c08070f0806011b060b04050103030806030c15033402070311041e0b0420090a0b461107050a05010804120302070f03050901020c 70
    0x10a88142e8002980501c0e43d42c8e40a25008030754080aa0702800c2351005002c0b44160036140b0076221040400c0e01c6604407070501c1e02014121041729213000003001454000c000d140d9a00100340d040400070002c0c0100f00c15101d150510142c4071410290307030058503000000051545c0403221500941c1d05505030751900b882341081c407800b401d690800781e84140042001c12074000300c3c0e0300c0c8401c01c0c0c1001d030420b02100b0446014810300c000c010b8811001640144000c1c001e1003040c01414010304c00480b405c001c6003c2d0410a0680089014070000d216980c4144100c241d45442d00300c030703003c41d41c50484c00164201400002080d50004d07800390b800382d0700c4200046a6811002c013146c1c26003c0301c0c003100d011502c49030300c49041d480d0054612411095810201d26500340194544945586c46440302c560301c442410565103400304550207640f243c85c2d043c1080107281d81020034607802ca904484080c10300c000e130340c0c0c00394080d11900340c00a2084040400000906a11501400b801e031002d03821f484581c0c840e5000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 998455044 1250 998453794 998453801
    0x100c090503070509180f031804050106081e04110a030f060e211c0f02070b091207060f060b0f0a08011a0f030a090b0907030c0506031501081807090f0f 66
    0x43c041c0c01000240105800b09503003030707141382c080c0f0000080f40c2d075403511b20700702c0340c02c54004050382c0c00005151085c2001c0340c0740078040d880c054a05450320080310320340800070421020340c644018000b00c04060100e81030001104c60f003581c219010f0420084981e49186c60720070401c0a5006640403850112402510710010a002d02100812912901400d4012500d02c03520b5003c4101115520384904100810041074090310036130008a1b80016102c4605040281d10187c0040610300d140d0880300c500d4100141c2c90007560034460b08088000307400c80390000c20200401035030f002004070200201e0442640010b100080000d00810303951038007103990354031101d4005e40ba44d4481d00d5015034103100104860035024051684031040d0207000c2100c586a40392501c8a02d0706481010040d0080c0d141441030200242d01c0d40e00400b4151007403403562401108000c200c4007000d50940c10003072402d011444028140382c9003d02105203070191802d240da00d9901000401046442d100340c1800e000c406655400c1074030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 998456294 1250 998455044 998455049
    0x8191407051014090d0b0f0a0e030f0d140406060305150c07080c150103050105070e011701060e01020a0c090f052503020d060f0f05010206090303040c0b07020d05100c09050307 77
    0x40081214410590042c1c81c0b1258001e0009083e500a02683c0802d0b038985480c02e103054050403440400d814659448068504010542504d490401c0c0803030f005c0b09000401c0341d032130520000c015500d81001c91400070240402d003110603560354100c818041803010640c491400c40c0c0c4610115110b0035412968a00c8542c0121a44880c0060038000100420383d200010701c28401c640e0250f4428401d8404800348141c4207030025160742e9510360030403292039000b800500110909080681152041643c01c000e01d50050143c3c204200340c80480403840c1c0d00030400314030040d62001c14200d4481d104c03902c280042c8402c1840502c842d040034003143d8082121441e1911203402052548100148000d05902130750140d5500340140d50350390320004401104c05003e401a0458000212500345000002494820080d00410541d001001031100150060b002c050440d500040759503181c6401e1300024000415261000e05507001c0c4152071808205560b101c1007803000d5035101c840ca000e032140e0515a88100a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 998457544 1250 998456294 998456299
    0x10e0f0303220e0f0f0c04150e040609020f0412030e120a02031c051e13030f12090b04090c0509061206013b06040503011b030e0105040803150a0819140705 68
    0x1080850f1340d50482500d10395000004d00e50041c6400c0d0f55915090076140a070b2344040000300303c41e10030f80c60762a041c0112001481d20b84410341c00e0100c6c0c440c0032000b03072040b03200d250f2400c0003034907052003094027414103850038200c000c00821913660700034001307516030741040c0c0224840d008610003180250125031404100105568800d404d0040d50007041001714030308507445030a40b005101a03082d0280c0400c80201448c0304142001c60b15900b031520314003615507a1101018060301c0d00e421b00045102500351000c486031030801103219106000150750612a5030200c03a00312500054880030214403c1c00c00b8000c074400ea07030703120203070040f000160176440311019407010030000080109885640110094144032009182601d025640c0f0f0000b03003198031094040c00c001020000340c550241e01482801100d404183c0244101d20b4030f990f844500b840010904a10881100103d820a46800d100603000c2c2210300111803c0f07042031142c00c034864811440444039000360000d014412180400d000c01141e001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 998458794 1250 998457544 998457571
    0x305070b012102040f110a11070918030813020402040905040308250c150e0d0807020f0a0f1b0609080d050711010819060e15010c0b0402010e0f0303220e 67
    0x101e0f8200300c0580000048260b440380c035a408920102032a200401b503200c5a40c4072100848240741051b8100b90455105844242c5040b10b0000b400c0f104c40044042c1c3c039030526018040c0d0340c0d90300d640160100e000e04003941262010401041040c01c4e49e200c240118001c0e12183c035150b944c0c80c07005240584c0c4212407410020040901200d031030140311107420440c4108104081303e0f40280810040f40d15681900c0d056510103160b021102d504a10304a4000c1140d10141820010424035552f440c0000140108140b0849510906104540581c0c45480301c40720031001860b0394602004010b521240030300083c42c010603d562818034021403c484a00741d000d10524401c050b9800107541c15040142012480d100001640340d4000003481113002416078410180243e00b06860f04040300c58002c2d00f050706000c5081424400305000e800c070301c1c2c4d201d80d0902c0c000c001c02d400d52000c500801c2c1c15404071501403001050405074940343c62081600714050008007020710795150200401d007102990108210b403003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 998460044 1250 998458794 998458859
    0x102160c080c220b041803140c03030411040209040905060601020105180c04051509011203020616080f070306050d0309031a04020904080c03070b0c0702031204050105091e09040305070b01 82
    0x3550610780380e108000115041341c4c80115003036a01a0320003046004003016003600f015009200d01c21001154517420342030500c400400b560724400540091310710118582004030543e1150100c814060307000e40240910300c40b500d4001e80e6180280c5485001d9400d020005848101540304030141d81c50007802800c003c01d0101c2480002c290140c8203403071040c84850016102d4030380b48000c034020410440c244d0b00301059410006e0a02002070840e1036980c4040c9401000c507503016055a03004580c40c0422000c3e074840345400d80c01801c059000b15004804041c0a005154002100100b00d9003c4c90502c0594100c991a0594581c0304443c0207522440c1e01c004100400c5601c1c0203000030803004030440c2c0c50640592144051032031b0483c0c0e0403008900000304041107080c1440b011035118801c011060825042c0000604603006d52070400c1d00035048031880c1118800c0a4103189110340300035185418030704003070800038181e0b0310900d800da640c80c002d0381c00002d00e41186002c080142282c3c9007008100705 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 998461294 1250 998460044 998460079
    0xd022d12090c1815010509011e0c060e150901020f041203230a031b140f0403060f0623060a03020315092e030f0609140102160c080c 58
    0x9000740c010038403072140e0400c0071034940b00e03190000c682c444510820486841c0c50081060081c584c01c04450401c402817140302d800341d0b0041c118080070001d00f00e0080c04c5030055501254075503c10500500100d007065010b401d10040031580c540d00e1207004440c80c11a0b41c0300301ea980d00342c2c45004030701c0c4880402000300708024a1074150340c1e04c0ca03d11038075207900600f41c50349452152942e201c540040b000000500004010303003502c5071110800840001108141c11a1006490b015404020803480e010005601000c01c003410102d601940d4422000c2001e1710141c00480000c2416001740c8a500c10042440b0410b900c40301c0b021400110000c082c03d14240410108401030740014040900e5100425051007180e5034640505102e045202c49010750000580821804200d1803020741507084070551041c00440c4915a038049110341054020484204c0ba181a922100940035840f146500c042030fa035045442c25010302d0007960050b0000d0320120740b2002e00b140c80f100e10b010880d91121244030b0521458 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 998462544 1250 998461294 998461327
    0x1810030b0103060e040839070501030c11061503010207080c0a02090603032b110d05100f0f03060e25060201050703110306041a06040603051006021f020306150d022d 72
    0x710625401081c01e0030301f02014501003d03031950310001504001820f01c500c0d40e061146100401d417510300100c00301e80124199072a8680900324503680e003800005000241c4094041320001e55210b01015983c1d81403403682600c0d040d028030120302c00c5114030302096107031400005482c0800100600b20607522148803001400e00d0a401c490340300c8940300c0082c2056000c40c10080e001014217000c01003118600729090f103100510b01d800c032101c8211188014891150207450600546c0e901020001e80705241c07a02103807400d2a082104441d00c0441c4494481c0000b03074003464022101150004d00c20b40d103402c0e00546c261a510800301520b1030061000814520341500800400c09504c0d8040c4403c3e0280400700d8800d50040d085900441c2c0c0360810700554003202c0c0ba0303c0004243d0f41c0302400c6030304845403280504040c5480c10595080d0084040b90842da105802006490342c01040c43d59106400000745000c0e41002e24450000303130070540d0100c07420020707880c2801c464031804030007403400e03c810080b9241c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 998463794 1250 998462544 998462587
    0x1060c05100c1407240614010e041b050c15060f090a0912090302010e0a030c030206030907210209060306011809080c0f0717010b151810030b0103060e0408 68
    0x1c026290300400c204107440780003401198003910903120405d0741d84030b45001d04d40c0100010102c1c0c138907190003081030380c0300b00a400d00050300900c0c1403500c00f200740d400503010345403c100b21050115145512014507400c040244040071200e4281c40654940c00d044000c0c4800c21201e4030707000040400440d45030716007812500c2c0d1105414200040005060719000701074040841c228010514042c01801550b030882080d00c0402d03412121540c0150840da10680010004d1000038010480800403504560003401141c0280c0704074580c03822241210074060400c07e203200d800340c0c011005000801c5c501d08000c5102416218a041d10080c0074801503a0480204001c480681d40b8803c24042180d03800c006120650382c50a0f07e600030001070741000301c2210701181c03104032409168034100c5007468903261080140d003030707541340094a80c403000447d000046141c500c070060f0f54050700403040140002d4055102d010060030a80e402c0054036100c0384601d400c201c0585002d49580000c0c04510301c24a211615007c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 998465044 1250 998463794 998463797
    0xb040308190c1202070513050423030d0903091a030f070807020a02031e0d051e07031e11070503011a040902120a05030307021504020f0112060f080a0b01060c05100c 72
    0x42900b10b403240103a065040000301d00581182e00c00300443d1030301175982101c10514070300c01c0106042c5680c0d03690380001da01c0541102d120800005604051090081e9009071a440d0014001004a40390041440f00180203a03040405a190140307504c119140582e403080001445001041d1a000c20944a03014024201d0085100365240740005840900040c45804103044189418204e09003100741801c1c10b04c415a810080c040c00004ca008200c00204040b074003120126543d03404c401d040480d00f24a04d03a0091455a81e4001400304669004040c06070200041d420ba6010030f45820405080e103202c02098092072002140d074409030302e42903004141c0d5910082c544e54440c90240c210500300204410b0542d1160408802c00081c19018040e51643c0741c0c190060641da80b0702070b80059901d03100c00310100d04004010341e07844a840610750118020b040c4080281c0c0388555100b51099640e402c8400c100c91542d144000010703200e010301c09461040d580031001d40200303a9904221001030002c01641070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 998466294 1250 998465044 998465057
    0x21120f0b06161104020d02070203100504053c0307021f0f0518030601151215120c08031902011b1b03020c090a0905160605041e09240b04030819 63
    0x18944c1c1e607100400c54483c6000e00942c940e4228010103040c5154800e103000800d0a100030000003500c00b140104a200c07040d41d400c00643c0c1c20601c4005d01d89458a8508610000c1c20254088500b00201401c2014030807030303000840340385203040c2442c6050007000800108044010080440e80158040d24a0709100304405002202c1040000d00e008000e90010760386c10707031b9514498007075035106e868003280c0b101c19881842000b00414449505803d94400d0b0b07105051900171b19420403c180d05140c0c01032003080c0c110381d2030310030b031204864200031442d41d003001542c0380c60140700a440c0c00300d60035503000b101070b141c5185c07034501482ea10780c1428154004600714050854003036141c0c0d0311a00d4490141c002a14001001c000509d417080c945204101f454a031000c103154100461640b000803201aa0b5501c0f40c0c01581c0440000c031141120750981001e50380c41e091010600c64810314452524810080d440695040c5568031040f514920036800090a00c20b001c100b0640b4007124a00c401c41004143e16249 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 998467544 1250 998466294 998466323
    0x3091c050613020108010902091503060d0204060b09011101050136180b091b01110f030f1914160f08030406060501030b040b061621120f0b0616 63
    0x460400350121882001000809002c80540d60311400c0f01c0d0150034580001c5113880401c0c800240c0b0001040b800211282e800000101e06480d580d289415456000c1c2c0240710f4135884d8000e44130141c0041c01c070030740018002c036100844100140186412100b00c05600000c030311018441700380c1c0b044040780319820300804144d440d4203d44203209003001c220f03504031112209489032801c81da0740300b40509010300641c003a00c00030100d44000d4028030410402402c001e140d0680c008686402c00f046410300c1030650002049054a004000006100c61240391201a40303504004030141c1d4455807400380502118014010924180f042c101400641402030b020441d0840c20303555841015401186c003104eaa039241c04081001d56018016100700881c103c5051180420140104408d40140301c0020b03031051200303a0080502101418a81d007211611074490318103116104064014450b4240d00603030719150594010184696128003071407a003000303200038a058550f81921141e0184101c0c159241681c50411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 998468794 1250 998467544 998467553
    0x308040e09120c060a1d01021b0c0a15030c0e04060303030f050109060b1e04050d0309150203030402150d1e0b1804020603040209070c0203010501032001020a0503091c 73
    0x544020884949000500d16007510858180b600b03038408980e1540c8240083c1c100c495000c80c1540e401030041600080c04818500d440e2130700360300000c010540354030005061103c44180006a40d800158000f158405003400e801d01103071000c24451100d601580880340c81030320b807082e00321141007090391070f1540203d00b200e00050308490031584101c3c080fa40c0c902c0d4002459066024541c0104254601000401e10f0102c00341c030144108400c400804100b41210380344050040e003a24003422016040e00090b1110385800b40c40500f4500a01a043c01142c01c0035080c6440001100d100d03a0317011308803008129005001000d40d42100c40b056a0b6241c452a1329000d00d0074011710100c07181c62100010902c03841140600c0303201401c0118105054608108001c0580c440c03d0440c2d170842d0341900d44002990f1041d6088504900540000303626508040c000024890840e403652203480c1c8259030300809034910741c0166500d42c00750b00000c1c140e80091003500050700d00050a0401c2c4808134854807401c0f0384a544 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 998470044 1250 998468794 998468797
    0x703080a02011b0c06050912180a0f091d1c030c170703050a0c0e030d0f0210020f04090b06091e010909090501060f06140915160b010302010e060403020d0f0503040308 73
    0x2081c3c0002103603000b1394000d001040c003800741c0080b103a40c054180010300d8181c01501d4418441c181300e242c0d0501d21021016102c181c0c03240c1c014070724501c0c40300c001038548180e08058454000c8501d005002c1400b00e100644000c140d200d8a22804c1803504240d10400505402402500000c502480300702040c0503840e81c802542a442070003260b500048614000e12090b0445030550314480801488010410258a000801d010b1040f141d0818100040700c1440032450b02e8004d9021350056400801c0e04060046268098400da0303480c41c2003882001d440b14144007039409004034031980106c603405040e111201a2520200e464410b2402442998565650070141d441c0c1c02001c41e020382d5100820000441c0b0052824040e008503c2d200094008100d0241540d0140d0080350b4820482c604c0344180e49402070781110f002d43c4509046158003152401e08460541d42484242d010501d46000d04c0307040c0ca44001140c0550354010289941072115865040700f41d4030b0684120b41c0c5200400003c40841c10050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 998471294 1250 998470044 998470091
    0xb0612030d0c120905060c03180313051309080304020d06020d020c06040b010602061614091f021b0d0b0405030d020c0d300222090204030308090f0703080a0201 70
    0x800100b404100c034000142041811030300f0360022443c205040f00000c201284403a0030481440c0703402d450b600d0b2488405854988070b08255240d00c400514003100c0c90701d111500e0225402180d400d001081c51003c00c0c42507800c0c0c803500412040c010800200103242c98098484d120703000c1c010050414200000c4203003282d02920a19150740d02c04020003080108d40d514413409032a01c0c0c8090081403c00444040f0300300c405583d07032401c1c010100b41300c003107001080090300c1c40000300805030205001c0b9401c810200d406003e0700100140141c1c0c00c600030000c8401d030034098407000500749c440c00e61a5038a0b440b2000f24081d104940728042080000c80d8401d2074005001c2c1c82c1c01800c0a0010102c0b00380c0064100f00074030864020303100c3d06071040016101c1c03801c1c81c60305090865001503503600c1d9643c0044030030005912150010a101c68001c47c3c40049a4040c1c000d45c1e12a4555004540390000300d156220500c254049003a40045c80a100082c0e005000d48100c541500020400034540e0b4520312043c01910b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 998472544 1250 998471294 998471317
    0x702013603270509100b160512040608040b091b0f0a0909050c030615100311090a24090e01121403180405130317090a050601230114070b061203 63
    0x1000600c030f1403512082d01a0045a05440001103910b4203451060f240682c06400c181410700c0e400900c01e015060022010410040c03640b15a55a20351402500c10242503a0039600c80f90b200f00040c1c20000005181d5070404139043e8071114041e61402006802c1c0050b5040c4c5810500000001803001c40e0390083e42082d40c8100040c08001003441e060501e00b0301e009140e90b503c042600301150560b200c0c0c0e544860441403d14001ca03049034608001d44e15803103040380d02a08600d40003000205485010400f140012890b00f016030f010080200c12683d11200340501d0610568190042041d030f08100507140340180320349540f502d44c181c0200401d0450f0000d8071412401c00c406895050b440c6014402c440d8000d13003105c3c1c1c1c1c00f076981207070700d0003000710030704040e50030300900382c2004124400e0041003204412540401120f009607180c0e203841d0700c110545c0003044a0580c041407911455030203175000c480e81110300300c040c6003060103540b50344e04403d80250175a50007000f9401003102204003400204242d1301403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 998473794 1250 998472544 998472617
    0x906080c0306100e0103110103090f03080108010b01020a032c030706030c0306050909030d05060102011d07030c050a0e07080403031404050a03110624040b040606080702013603 77
    0x2210a150510364020310460051600f100c00380100701d1241a00c0d810b50703070421141100311000c140180c0051181c4140588810312841c8040e04166118640034140c6110000a00200c1034100069a640d080c540008010600310f031088040c03026401c0803545d030819400c420026030034512001c00d003401103070740205002075103d075500b038080f64244c01204001c0c4010344505510b45081904641c59000d1510503940040d2120b000c03813900e03131003500b00b02e50500c903862103074035911484041c1310f641d051301c3d11049842240d9002c001800c5c0c900310440b42c00700e039a0540a00e00301c1e501c04204030354281c4007c200320241640c1e59650054400728682040c42584180e008107600601c03030070090408085680007403101d0f40000c04011240e2001c0188448403174049020016030420303040094040c0c14039110315600039103040c1001802d40c2c0c0c4000100d020b0b1480750000c200421108507562440401c00c2c04034907082c0c1d040803107807843d50041080c0a41083c001d10349010709148402c0c60f01301150b2414100c01d06243c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 998475044 1250 998473794 998473813
    0x2030637080d030b0d0f06180c090609061205030a140705060c04090f091104020a03140f0105100206272104081203040b040f210203070606091e15090608 67
    0x80510640f030400c1313421a208250b020791a500e004000841c1d5000600150322420740c81c410283c0481c00054803640007001d0312140d5214048880107105c2d900c1010f03061403c00304000740c0c0500a072604811f094001000d1858a0500c0e00165400d0300412200700f4070100801c40800811820b0001c180166040f503000390f03840340f400e403000d401da4546080320207003646000c08010000d0700708800bd40c00034105940160301c5503440b0380203800800e203460081512203c48010000b450800b4003645040e03510440d80103000142a1a040713950300c03403c6541c19203110b02043c00c40395170310200080c0450016000b0450301340c030890b034220701851061402c0320401c40380041014031582206002d902c1103000681121030940c50582c80e484402503029001910b51181c10803101e09105090300c0c030302c200c65181075a03082c01c0c0d011420025520790001c0f03c00d4403400d2601d50042405106402080d482d40152001140701581071281d000c014000d0b51060180009803150016070b100050007560000d16000015040929 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 998476294 1250 998475044 998475047
    0x50f0a0204051e01060e131401030210080c07030c06020d1802120a0305040b0d14240a0e061210060b0904061512090606030c0308190302030637080d 65
    0x44010f03004070b049248042d9184524040b10b07885030f046401629005c071103480080041071400401c2c03070742c1d0309006050840c40c200c034103102100d80c1e04030391090310565544d0f9071171036040394080800e458811543d0400c104c0e0350046441a54600b20880c01842e0046c6010354059120b02100c1070301210203210060100064290320301010b6040c50007405401074440d18449a90007000d61003a40205c0003849008120b4001010703490b4400c9040e4201d240c2c4492841c100301540400681500000601e1800b1240c101c40c05420210703902411103141845c00300254841030100b00c0d50309000d92210405108620303014070380e20441c6c0100c2e00282444011641c2e40c10510080c8001e071100c030341014405a00150000c1d0b10554403117000408600c04e0603001401141c186494805007900c2d82c406090600909004420b00c68104002c10780c6548821403a01201103007001039050b8041214400e03404001050050030341d40304a000e1003220b0b40c0144007108040414021180c08045680060702958400102c03201002d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 998477544 1250 998476294 998476301
    0xf030c030f0e0f210a0813050105010f09060801020a0f031a0306070f120902010c0b040507031b2301050f070204020d060e09060f090606060c1c0e01120b0603010902090d050f0a0204 79
    0x145000440364100701004040d00d130300351003044202c0007000b10f03103000074000d45105021a110964494024065542d40e61207690b440f5056020340340704145000b2001a10180500c01c5802c0100c2c00d8944c16a12904080d06500400d921401c01a045004540304000c0396014404c10b0700c26170b12501d4525140441136030042a81d4110040342800f14030b00b4015001603a0044503800d50584d1008280805948500d09607041a88941c0020400f1640f0308a03008200d20540449084d900040d4420341030f03546200305400d00d0301c840b6038410b000c0f801c00c020010060b040d5500a080c9180050005860450328a095804881c4180e21220021501c0b90511180e02ca0900905811550a400c95825424510320b065100d400292085104040000312200d40e51018041251a0501001030700002c19581c5009080c0380348180000340006d1011544840ea880300b4400d80b8100c00002e0300c2e1030f080d40e00f001501002540712086540d440aa90510305000030010094444d08240c100f016015030340c814030510094 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 998478794 1250 998477544 998477563
    0x1061503060f0f0b300414030304110f0a0b040803090a0510021f14040308070f17060f06130b040f060503042004060510110d0c030f030c030f0e0f 64
    0x4441402070410516103c030004034107950144258903a1060106014400d84202209000e004c44c13102007483d80303e4041101e1240300303501810f0121843d000c2040b24548920040ba030081240158018203074040c1008a400180518050001c002158580300060740a4006a02c07038200744d4000121030000f410441840f03801088140c84442644903050302c065150703441101c0b40308590b1108951000d10442581084d08650008041a0182d050606008205031800c48160000c11403144501203101d10841000c40030382500c00700000162130300700030807840291580c1034960103903040c420020f2842505070010010112046400e61f103915218a0307000482055101a050000510401c80071503015005a00c00039021801c0807011480303c400600100302c40e800c440c0d005400f0b45a11040c0c0364200ca00d0380f021150050456000d0304490038101e52018482c2401000100743d4080c5003076440c02504503507400d406c0d504002c03480020540c81c14003200c0003d5040c92055114503014000e40707005004d807184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 998480044 1250 998478794 998478809
    0x3140f090f040903090b03310302062401110a0c080304080f0a0b0604090c0e0a0c030b10051b0f061003140105010521010b12010b1906090905180106150306 68
    0x103542d03034541340542803060920510010391000030024940400a81c03100c2c1c242c1001d900088096000c0000070b10418000382c10440151040f0004180000705403040c02e50005101c10042c84214486001101e00700400a20503a042c4500350305d6400240500f038203c03014000a100039622249080f016529241044c803142c070300c0e80c00c5201c0315400700d42c003210200d43c000070a40e8041250315251a2400e480c0d0290b500c0000b045088505001c00036900303412690040000365000d01c0349510000c100464030540e070220300003242040105c54903002a8030102d10000d01c02d8019500f0700714000c001c6504001040355000780e6140714000c1402040704606540102c00282d000800c5030750705203008078601040030030b48050100e0042d02c820745210005d402c02c003103400016201c05040a29200d849029010742020301d4400d240d182000e0841c10302580c8400200c441d9656140d1015141035182d4000b00401b8141c00030300003880c640070070200002d00440004044170940c004100d14281002400c842107608481d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 998481294 1250 998480044 998480051
    0x5010e0a2109150c050a080a0e0616030f0c1217090c0904081b100b030c011e0c02040b090f0a05090106030203120c150a0e0105250c03140f090f04 64
    0x1010759602086950542e201a05426070702c2200c0384082d81d4842e4a0f24000307265119416a4600b008220341c0a044800c1003502e6007420f11495100300000c4c0d0007000e000d02d2040c00240c4078400401d100b07128a281c04500c50078a8403400e045515200b103280544800c01001c1602c0840e82031035821043d045941c00301540c000740408150b01c600051618401030400740a80d040420058070002c400013800e610a90f490b030440d8007000101071240f01800e00304000c80c1c440d02a035400e042a55014410300c10f211410801c2142c0044201c0e0b0080d500b103102140207a81040d40c4d400002c0890300c1d2641039a02810341c65108004914104411000350b82c001801c0e10156414107004000503107000540ca4242030009000c1078540c20a10003080ca13100000e000704900348042401c0c0b007030000141d0302154520110034021320079030361045044001c01050258103a60b0000c28154100d90328401c5110403200b038800d20f8100b000944034070b001c4546410040a5500c100341c0004e561481d407400c201d000030f022000742d13400d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 998482544 1250 998481294 998481353
    0x190305090c04060e131506091d01060b030c030a11120f070207211a010f180207321608160303021c0c24150509070c080705010e0a 57
    0x307034444c1010303000740c0b102120100840b003001540d0000c0c92851081e801c08101d400c0e510301080b4081d0590f44501d28000d648098490030a03a018042c0c40240c1c0d0401c001d00340745445240e402c075900c0d8001025000800d640b0105140303950100c2009000051114070495842d0418609400e50150701408020640d070055804128030401541710a08112401303082000c0c00310242008250310070404406040c0110410000c00d6000c0011402c1c41034a00048034034401303a001c1e4050408901c02d115000d0070680170074100095402c581c42c1009045511540c41c2c40d40b0595807040140f40c2543d8400c1c902440c0240b040c1400080010003551a4044801403d001a54030f0341c0c0340651607680c485403904034034240c4000c803040d5900500b0035119040c0d0003076004c0184e0102800300d64008005010300550b844c10403004520f445288001c11065440040a1451326220154280d50318060100c0440c1da00320700b1712038000400c0080c030030340000c41c1d0820060034201510b454038804442c800b00e0181c00712007840f50300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 998483794 1250 998482544 998482559
    0x44b021905031009110a080d02071406091e152203120507020d120309030f18051903060e010207030f0c0809040b1201051e150d0215190305090c0406 65
    0x8007100f000799400000308400b0509202e1810209030703080c1d503081100d41d0780004440400084602400101e030b825201115280d400c804514095204501c2c1d00150a00c6500050f19140703240002ca1245443c03d2000e00044802240204040c00d40c40000c2d9100400c964101984d8200b110341400f07a0001344408803420340e90341c5040710303440c4042c100400502081c00c0d402c540f0340052031510303a070b00246000c1c8540034508000f405400074020480000707186142a81c491401504048400013403428401440c5091405000529400410302e640f0b03500e24800000210300f881c400c800e2803403255030000d49e4903250750130040c00408100158500300010740e501440031580c00701c19515071801c201d9001c00e166000780d00086803d84c00c0510717102c1030f500e0300f42800351613088250088460011070580060650313030078100c13610401034001d4058114032003600d4000140f41040ba80c080c280b0390b0b1140d40d03080a250222100d1081c000250038404240c1d51018004034a10410060501e40401c070380500105040c80c43d0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 998485044 1250 998483794 998483803
    0x17101401090b0d2c0f010f06030b0402040e010b101d0604030c0308070c150e03010b060c03041a071b0e0c07020d1101030b040f09020117044b02190503 66
    0x181030441962211107008420281005618644100c58002c09425401c40c813540c90b10800c0c118400c0c1580303030804d102000d41107800b50b981140d820080c1350b4042e513103030740911000d484551100e140d035540c0c80620140d1559000c80140c0c502030039540758400f0701c0015412842c000b1b1165951407099100341b0040000601400514044e2030b40969500d84840403482d200d09041c486401440d0b081b65405003070264140e002c1400a0740c0300c021802407110070907000a10000d84240a003804a40e041040240000103844444981d0b648000c0ba2007407800c411030319040e4204004240d2500c8580447c841007104030001000160084000c00d0500c1c9007409983c00101c0301c4104200040200a05110200c07081e80240d0007980782e450082c005010311722908145800421551204a010911056612624a1480c84154030a40c1e02052400c418210300d0340048001000c6048003d40c440002003680d603040207150881c01c00c0c2941d2400641c88030452040010900602e402d840c0c00c401207580c2004070350360008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 998486294 1250 998485044 998485057
    0x90a03120e2e0f03060b040303080a2f0c070807090203100f05100e0409140f1908030f040804032a050f03100c0c0b1503010b100c1217101401090b 64
    0x91401c02002d1110f001d9000d0003007980007100c50310b00410000305060304400344c1440780c980c180003081035080754010100031001041080b9a915030304803440c0113070000b03200180380d11303140f2200725418107680300001407418642da0030440b1041d0b000300a0280c060070046a040c0581000b441c0c20401e02d00381004540c0440402c4178017010840c0c4c11801c0780c600e448590008040c40e42103964a811980b1081d06c0d10b68491a18054941511131129190380c040201444114a20f9011000360310390345980080682034000030b8014bd8000c1001c10000002584a10200c403504810304104001701c90002d480240003207ca91040e8044c0e0055000d2601d1542c011820039018105a000052402c071700f92411615002104402441200f81c107007440003074250000315100d030480c11402407245512020078482007070380c2c3e406076401041d0b11422580000d0942401c0340441800c6e80740c0902d000c8540240b41c6c410200541e03c0907000741516009200986903d0740c07031544140d0078201500349900c0c00c003041c2114403911 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 998487544 1250 998486294 998486297
    0x6030f0c091503250501050403020109030b0a1b1805090610080907080a080d05010506040f030b0403020c040c030902010f030615030e12030f0a150509010506090a03120e2e 75
    0x1030000e60300c00d0307081c034a00711000806412644e0741088401104c04542c03100b03010340000c3c20781c040b0014403903204204544c240d030f6040c0e461407d903034610b68802d10241c4000d03007000410b94841c41e040340c41300110400711081c0c3d00240d4411589a110780e0b0006224000c80d007000703002e844a54108a503a0701c4644000c5070110b45450031680d80d940e41c524130f904090181d00111a24003500d0002c1c01400040b80c050b010840c0784040402c1a40d03610410400c50780715520170f400a464030000d040011400e08008160302900a0055914014883c40081c2c1200e420000f03400110b55204004415542c0c4101d030350300d906030305040c00c00485007803195a03520f81160040c0e0b9000c164641c0ca08107a0102d00740012011411200e02c40c6880c1e041040c460a001c0104403480d102c1249040c64000004a12611700380440c4c1001d00f9010444e42000280089580010003143c0c110a10b440000009203940c83c49002d10002c0f1340d140401d1105517020008981e0001c821141c480390652480c90081238481e0482d0040c014a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 998488794 1250 998487544 998487559
    0xb0a14041b0506131a070c03031407080d0203010305011a0105040909050a15060509090304120809041503150e1c05030601090e010609030218090c04020309010902030a060f0506030f0c 80
    0x580918082003050b00180c0d0081c80204400d0129100504607005440704990889460308091a201340c0500402001910380c0b0507218040021070700914102000d507802003941480e280b116200c245e8240d020b81c0900342c0081d0700000400a111003072080b90711f00d41130080b8440c20401920700007422030040307010b83d085565480c0350341020848204282403a15500000c01c071068050142840b009001904c00d0034020980500024640c1201100300e034180c8034502c0b1411480040b589807104190481004c482c3c1088e5622080d9020044003560b54005500c03130030012210320451441076081e1000d03c0d84504907907200c2c50103003440f14034440c2c00403a43e041910304140ca0b5501c1200488a0003483c0c4c5c420070083d1040c50021484a9108140d1804e80f4000d460307644004036000c04000130391a08481c1d42101e60007400120341a8a05a0011500b01d9a8180041501007250f000607041c0031440f801251103c3d078804628412009c14068154002c4042700a04205052051240d80b07821000001903c152a1b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 998490044 1250 998488794 998488823
    0x12160e1008011a12040f05060f040f080a030e0a0c26070e1b0a08070f05181306090f0b040b030607171918020a0b4b070b0a1404 56
    0x40800075961240c402e0682281385040c5420b200030795141140059805000310000905a5001100c0da2030140307900251104031020b003a151941150001c090138410907886264001d0104000c02084003854081c2c00d101c20300303a00c2d004010a8042188807032030742400000d031307500340e2500000c500c2000301d0342c80040154813691003041032070300030542e0101d45120070000300b00088101d9000201510440840d100c04c0d548006c1340e4010303509070160056003420280c1c0801c9000407402d1200940031402c06500c40403da150315410040c003aa0481500107141c0c6030345586ca102d00d450103001da010310314001e40107003400b401e082c14020240319500c40b180c2007c06040011882c000204a0214021a0030320020007022071001d042142e00d84072520300745c0c40b822800d0008503120344003130221686451182c070440ea480b914071400e46050701c0c240030702d140c80c901e11035a42040d28003000141c2c00c01000c5150034230380d038001900c0e040806078406404030494901d801c4610345000b120340781c00764101d40c02c10140c058021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 998491294 1250 998490044 998490089
    0xe120a0e0d0f0c0315180f1a010603020d0b0d0308011a070803010b070209090c0a12050f0709091e05100b0607140606040f090503070f0812160e100801 66
    0x11007900300100249042c0c18460280410f42d01c011040c0d0344030342802c00002064910395400d50303881c0516480f040340030050a800042e50490b8602c2658410180104041c0901d40c00025a620076482100842e8000901c00841c140d5071080e5000108211016940c400f89920024400c6074140101910820702042002c00000c3c1c032000d980070309078440e400d0350b965a180c4896103600e40040c00300300d004410a00128440345d4012030070fa41c00f03e030064100c1d000f89140101c0300041c40c29440f001d407500c0c000c4070300c02c5000900078447c64001d000107481c00b1030804018035044650b0b8465090030790022440550800028002140612009004810101d9038216140000d8903d10030428000c2521419840d01c03410042c001c5101c51190400326410800200450864804d4403024540107149400401c2460001104200d00e811220701440555040c65243c110701c00010000f038580200040d203034400c200d0314540c058060070941f02c00b1b941c12100c0c400d0315000a0700590040c0101c40070142035114404204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 998492544 1250 998491294 998491309
    0x30506012d050a020a0c140f06120c1e0d1a0604030c05040b21010c1b030c0b0a0603051b041a09062116050f0301140a0e01062402010e120a0e 62
    0x50360002c60144c0001d42c4d0300c801000c0c81242d03841242c008d01109823120240e14200040d21904402146400083c2d512541d0b003904981c000c24003940312050800d18190445900c20103041b07810300b01c4000045824000000c0d100d1180c0e20300c100381c4510400c10060001409152202c000c072001542c020a03521f444200241d02c140c00240e05a0340030f81c0128003241c4070f84054100c43c0c440c1c9115254141040140c0000c0d407002c6550410260104024032450400508080d0219510412100001800c00c0d181c2e5074250030041d0b90015402d041d5480640c47c4880c0c5400c0c8035180400c1442d604450740b1002c04008141102e0000300308600c58966010709200001546042c042e04200c0041503681c1007203d0602d00c800b02d01c1d2400303091f000b038100905280d00d9013414410f42c0e10750300c000c1d043d0030410b41d07441c1e204402070100c1030400b8001d9525414005600b20308400d4120b440c8840e00b40c180e07078401d2103d40c02802c4030412848045e030b603440802d0102c1444111021a281c003c1207203415003103460702c0d00124a05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 998493794 1250 998492544 998492563
    0x1902010504260c120a03140d0c0e1002010b010203090603060a24020f1504120c080f18040209090c07060902030604120201200f07140303131505040b011202010c050d030506012d050a02 80
    0x402d400d00da000310102e5404101c00600c40000c403031072f485010030309408a0884240ca4540e070b0260340f0410442d546854510007031075100c80028001030314191126071480c160b50740203c10240c41000740b0050f198844d014404502c0c6a032800b0010305110180d4500440701d240c01510260080159000c604040791042c20010049900302501d83d40d00d0f00d450f801c0c40c40e80d034041c00c1c0c184001c50000352100038515180c000c461b5603950040c41c86005498603425030000340c0c0b220004480c1c6035550400d000050b181406000c1c4514096424100d1080f1501c0b1f02034207454030540d100300040000b83c0306140d2101d4040c107440030008101459519a800e914001c000190a41184406440048100442ca405100e080c4a03441d00c00c00c4030000301d090b500c0503d02661030a880c0201511098001400201800111020384500502d40b00008000b07a0f10b80700d00340100b8500000c0069100d200304825540c002a074007404d40c030055007801c1001d10314140c6044600701c0c00741c0a07041000020b58041d82500c200b044480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 998495044 1250 998493794 998493817
    0x6020309030919051314010603050601050c060a02030414010207020a030b18071403070b160204020901030908120907050d03080f040215040e0a050c04081902010504260c120a0314 78
    0x14540c600c880c50358407800e91413103803038858109016503030441c00860154040c0e04421a40a81c900d908012082d005024014091810400180440c000b050760070440c1c00d008100b8460016520304150070004c5404c2c1c2c1152032150280c0c010020a001605e442c1c419808890700480742e01245d446030481900340910760542e5454511810b00b0100b00d00c244440b500170f40034000c808541c0030503078640e880a010300411310441d00310f00c800300740a00941001e4000303103002141454001401002c1e996440c400e500b260144403007503c0c400d0200070700703c441001080d0240408607041c0c0c002e552990ba00802c60b81006041078000d245613408101152181e04001c105071f6601c2186940300c03603c0c2c240b0540301440072201051460f051030040354910210104650580350042c000e8803007107080200c000700d400c9401d001281080010007000413000c00805a6283c00259808040d0903503c44030600c501d07241e1109440c900c0b95008034241c2210342000180b510b04641c1c541844919040c3d102c0d04005903001e60340d4901d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 998496294 1250 998495044 998495059
    0x140a050d2001111506030f0706020706181a0306031e0c06090411161b0f06030e0c0901120b01140603190204050d0f0303140f1807030206070305040602151003060203090309 75
    0xa840f041d001117100340d4080c0c0450b45040d41003901b480d039456242c0300e07040260300100018046030384070310845482d8440320009000c4641c0c0d601e546040301ca14007120489100008001e010241c070f4140400c10744141604000200e089254000c00d03114041401c060740b103810000b41002594880743c2005510014a0030a961990300c81c0d07941d21282c00060400b00d0345c0c91020781c0c440c10701550311b00c6113006446030102038806a6040c88410740c02850400c0d201007040c4245c5004074420b9940d401243d028110710710b0920926006031a016510b1041a007001201ca66011090092501e13440e0940390b1000391040c0c4507081828150003034009108035000542c01c41824880c00c010b0050982044104c60b01c00e83e410803030740e6008841c819813000705680302c0346d103003000b10041484030344c8602c0300149403541c8606880c4850307902c2e400200c1944c8207807822000b10314080340401400350188280d00d8100141e0540400600c0e006d800c00c40500700c203010003011180d02002084609108105481d02400e0190031034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 998497544 1250 998496294 998496313
    0x51914120406110d050403030309050a0605090c031e0a021c0501112713020307020106120b01090c11100917071506170714031204140a050d200111 64
    0x44031580c45802004003103400c402601c0c24070900040e0459449041d5505c081c00d06055a03801c4002d0010718100f0740f141c0c4648281c40b8086142031154030300034404200140a40c000b83d005050601c0c41c0c520242d045040380b0301041450340404950300d4001c0d50304540c85a0002c103420b02d000400d21880c10054160743c40c14a0a006030381c13100d001442c9400340c0490081d101c07290646107002c04002240d0180c0c003c0d002c0001c4038508413240d0003035900034016000110b200b0341c036102000040000c0500544000700c02074010050302d44140304402c08a0810f203403545c05442d01d003140c0d0b650741128410416103a03540b005148280070351882d19030461008101201d56440c034904201a2140980c0302c1307441143d180620002c0c1020502c40b10b0a120461280a49201443c0500002c07100d0301c64440540c143c0900211039140070001001003000d0000c0c0407603600d103840c1c24414055200d185400c59402103160810322004901a0040000c00703022221014400015143c0100d0b245444004200c1580c818540d84 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 998498794 1250 998497544 998497573
    0x3060e1501031d1b0f18040602091206040b15150c0c220501061d040b1804081905070c0e0613020c0106080111040f06080c0906072d051914 61
    0x1c96094031102c0e100f10190103008400c00c40c058000307540180d8000c5075402d1b04a00e4100b030301c81482c0d0050090b4001424030300c0100128601c902c03484002401034104500308400c01c07807803407035880d0044020041840004d005802084440c2505601d000200e4408100100b0750b01c010812581040700c0a040c00044094940c11117684421640072040800d00340800416451310801e440c07501c0c0c03071b085440105c1c008000000d020040c03244128042d00440c12207105891103846001c031a0103948161a425650404400d5201103804642c201000708501081340b1008182d401e48102c2c250f400f8458503840c5510b903500000d0300262558484082d035800400c0040e112501907101c43c04548400c8020b11030800401c0b4900e02d64132035406242168100c4880600a15204104155001c252079145d00c3ca04100b1000207140c903040440304035003410074000c840e43c0d403840c0001100300320310368482404907100d40c0e60b450903240c498400d01000218070003010901400102c8880c1c80b003810034101541c4e082142d2805 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 998500044 1250 998498794 998498803
    0x605070201181a0a030e06190b01050c07060c021306080d260405030d0c030204030206160825020a090c0804030e01090905010e011703073315090c03060e1501031d 71
    0x4650f004031b4980448118181004a0958810a01036600034000506c5581d280300034040119800e04100c0140030303070300d0482c40820801010b0031542d120412411224810481e00c017051680380c0d00402d041080030480008001581880c121090034200c0700c0000382c448030f00c1081000140382d4441c81b2090b05200512402000404d955103ca000610044080c60b10030b505a00c078901c0000d41101e000c2004031240344000c186908820302c21000d0303500c0c10107008942d07120144c607504030000314508140c04808604d40304464000a0203685014426007607a8a00948140c9005002905001c1e030a005071002e68480e00c6483c000d820500803c0165585440e40c18000039024095030403070b081c0042009040c05000016150365a034456180d000500c6005030090001e4490b0288829012002403040c24504090180710102010015500705503407508251074240c0d82c1c0540b011081c0743c40c181050020000704804298800d004036a258500d0b040100120003c0031080503408001d07801c40b4000300c90603004213 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 998501294 1250 998500044 998500057
    0x402040e15090d021914190501060806130201121104120b0a063501060f0603050717090a03232206050f27030f0102041d010605070201181a 61
    0x2c40c0d41075855240f0580c0d07280b0090382031401d030300b0b030340d103d81e100013250000320000701c14014040d10400311400d08245140c50340d40c6c800f00c42a07511410b003404258800c00c8041d0384540715104a00302900d054001919003851b10000394a419110600c00c00011440f0045030000d0030030380d1450300c0007810741c20003c030f01e500300360f8152540b581064030003e011600300d11030282d202c400e2501c80d101c05080869504c0030390360700c0c0003034106075494603c001008102d08030044014419610082494680000f0080000f03504403001400141b6003414072015000000352480034036407500b084140403804038a55003825070b0700c2c400c41c4009880042c211000e824581e05041c141050a007078280010740740c00703041e43e00d40602108034142131001e0200941e400030103c40c900c86a116103582d1050351540d080402c1c2007070040c07111f20746543e40019007040040042042c03000003042c0d00450035225410aa0001d00c188607410002c1d04000076801c440042d0030a0300c20300740051295000d440c1d00004103070000c1760160040c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 998502544 1250 998501294 998501311
    0x32408010e060408190903120903060506010801060f110102040308070c030b160804030813020315091912030c110303090c0111030a080f2a031008150109050402040e15 73
    0xc440001041d03002410a0180b9031001300607041241e40f69603050358a00d400c2003e0204484031700b0010101c1c4000f251139503a03048656540700181d06504040c2c3c00d4410140110341040040b03401007048640c07042440345030341010714101c1c4c40380321540c00d9540039001c2c1c0d40000d03100b090001100c90400110b080340ca01120b204d128018480da44041c581705000307001a2214002c102000001000244139084203540071818920354000c800503500400d1901c0100071400100400e0b400c140110440100715680c49404403030358401c040310003981c0d502c5481300c050b01004281910b6503201c05945008400c040c0c1510030071002c5a890345426500740c3e5460488100300d43c04501805070318440d00300048101d41d4145202c1e200c014440e1501003445000c020300414541d2442030001d0a15114514440c90300c07031034210780308895142c0c01c09038541d080c5d0345529489402e81e0360010781c2c00c4480c403942c101c80904583c503c1d9400140b942c0d8500108014080780766100180e40240459049074029403c0d074580a822030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 998503794 1250 998502544 998502551
    0x5280b04050108060403090b0d0e0609010539030705190309021003091a070e0303071a0106030905150a0b06031609090203010807121505070504090c090b0d0c03240801 73
    0x25203c2c0503403241c80564000d4001400c460040c4001401c03030f002498010050074000030940103580c11031f03003000c4060711300b50b010b651150184410030180301840790845600340d03102ea500380c00404a10790780d140c0001124419810203c0060740750340c000c8050394000c580c100b401b880707003a41110f001002403072161812803040301c7d022118200c80e40310b840398644495208051820301c00030300170154440000186040d0401c010b40440c80941c0e18103001030300081c1d00c2410b035501c90703190903142009500c0058120a0030149018110000700e0000540084003000425410445448900040000e02450844d6541250002089c0007244081414400011038140e94401c0c205480c0e0190505034402841010415071140d101400001c061140c100143c0d84034a5240c440e50109203007200c15140d0803104000400e10100742003049950078025412a14910702e400500da5040c882509168002c400b03615130855610010b10078002c0c080d88c042c560144545202c104450043d000341e8803515100d01031310909508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 998505044 1250 998503794 998503799
    0x9090204050a090b0d06021603020606030102030405190c150806010206070c0209010513020d140906090304060215062409030c0f030316051005040b040204061202011205280b040501 79
    0x4520a560a96800030000c110b80d61508001c58040c0492900b2941e02005000f08500054014801400e049050b0f83c4d442d4545181d609010b401d00354020061030090740104208000a0b00110b007915000e250203200d02d8448445040c003008440d0a5000010545003a02000c1281508400b03120f00c610003d80c00c5034000d82e03510000300d551640300c0e480203400c008244010301c110b14080041514600e070400c001820001d402c090201640d01480c1e164040c00181c00903c1040e00301400342c5988602d0160003581b80a00e00760000b59a0782520410300b2403110414085071042d034404000a40114003442d0586c0c0c00542c40c01c1307444140d8800d26000e4468440d0000ca00c107542401e0041d102681d00003030246040c402c0d84842e81480030807a00713045905025610980c03a0007440c6115143c0602d028089800b124607140c03060004488160308840040032041032518010303030f4010f00701d0700151003148010a154a0b0b0a10401d403203440c0008840d20310401c22480f08200381e03594813821984008540601c66641d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 998506294 1250 998505044 998505059
    0x21c0e0d081b27010906090f15050702040f0b0306070f12180b01180b0d02090a11090406030b0a05160507080c031608031b040503151e0f0709 62
    0x82000034600081103462000640702004455500d0440301080c1c10a03141025160381c0710541c64050001080100c1e011040c0400c41d6801180080608581d0500000c03160421980310903140c1c40c0d10030480321049a0b05090b203294819016201e40d5070f03000c0c0003130101001109170b80c00588224044140688103c0340060001449100d0707500030b03401c1c552940c3c2c0301502c4810f8044040d024811015000d05e1000b0800c40001d010640014000c14990000d40700354070603c1180411341d0750b03900e82588110f00d4623249101590340c916113950403503110040011104d08003a2015840d01580d60b80c1c56000303160031000800d02070404042c42c0300b11040b030780406c040e5079511410080e400301d030b4601c3d10001c0c5051000d400001c05d032000403c08000c55404a03070504521240c25048425190000c445010300401488010444070031420342d0369681d603425900342402e05002c6a5500011040749112840300004100c82902120800c00032942e0401500d90358501083d52543c401401d80380382c000280030400c00140c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 998507544 1250 998506294 998506303
    0xb041115070605060f010f0e0d050a030203190327020117090a0b0903031506071403032412031c0b030d050a1205010803090105070303290a050303120103080715021c0e 73
    0x5c030050b1604c281943c1030391400c40703c20004800c0180c000654111804c08184204000300c0038910039801595140300d002100390000d58100e0002c0c05146c100300b0001c1903110b480c0d00a00116070421480c1c4c8285116000480c1d00802c90389215005072070b00410300947d1980803e0000c001c60080b03481c0ca1141e1614a203182e9240310840700b109080751300c1001c100e02850402c1c01411820b00032003844580c1d0400303060050030b5038016100c0400c016046120300d01100042054508070100885420022181114a940e03c0e0301c96075540c0174880740d4072200035941c1c81d41c42d407240803075910250480303140b00701d80040501291302003c01c40700400d0350180e4402c410040390145a0684461705c1c090740c00c1000e468010760b0150861f880c12000d05459402020300122408040c11b0865848603200800fa11200144004400e0783d0308100d000303400812070600910f6040c10010b0451783d005400305d90300c2002d403c00ca41d02100900300d4485050000800711004107262a080c0e9044101d4201080f00034080a1030035030300e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 998508794 1250 998507544 998507569
    0x230105100806090a020a020f160501080903034c05040e1603030e0a080a0308010905100b0405060c01200711010f0815150c010204180b030a0b04111507060506 69
    0x101c43c0d003400042403c409a009849990b01d98012a5980c0521000c614100b07400c07040d0110060309810401c100d15070340f00650940000c0c04078040d51441c14034000c03120101d520b412032424120522016102d281c2c04107100140030519540368000315450494400521006d5840790500c12410300e102022800d4021941950740c0d80d41c20404100e952550744d00f0303102a038140d980590b010f201c50f003001504031811b003d01c80f501f0380f00b9075910f0400c0d8140b1840c40110707480541540d203041c4c18000e0511801d1500320846d015100101c5210341c82d00d81d0300e141c05001d01291440d078001c41c0c10700700d000c0c02030720443d1028124440c030621100720889444001103a800702c080c3c140c1000100e401005c1401014121503400780b00310f0103003104c22240003020311485150309c580c13461a00b6a600017030030880150710002100300c120194205010103804400029030321a8948005004078035200d0106041005c2850f00d2a8400d4014103104c00c0900801044000c82e00000381c141c0f08241854001851440c5c042c112034079 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 998510044 1250 998508794 998508799
    0x706021e0a0c24140f0a0e070302130e030a020f210301060c060905070626062103130f030203010c020d050f0901210b18040507031104230105100806 65
    0x18841141d0b01d545801c2c03441c524240e072003860419402124440f0340c1c00f07006510044541c2c0740303641d4201200403004280e401888440c0d42480c15501c014805070110b036420440343c0444109002600b4044140f0003010b50502c50003882c03100098602c551034000c035801580d94041016113250708001409010f00c00c806940c03860300c08104000500070f203805500c1110441340500000510b00c0e0b16031b80d40e5460b00704d03650014030124030300f0704540500c40d894000c200030042c0c0311a9100c206081c268007241381c6601c2030071028008881c4107940c0c81650780030070039a607080120300d0000041c41e580391305808201489010a17402542070810385d00c0101c0c0000f84d0303040c12901c180e0300c1d02d203005804034240706160018204c041c10044000b85615084641e50703034290401604800005d07456007000100002c50b01c0c07100c105410400540100004074101041c02e104890300300d0560b0024610300c10004009003042101921002e07011080810040049002c043c1030f2030040da0b0b0010344517200e2a080e81c0c9903108440d00c55 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 998511294 1250 998510044 998510057
    0x60f12021605100204140f090a1112040c15051321062301052e030b03030d0509071205070b0c0a0b16020c010311030f060102120706021e0a 61
    0x150012040d401006803001d0501c0010900d0160390715141002568625544010b40108081c003503580c1c92008940341103011600c507200e009940011448425001308104551503450505600900b01c48040b01c9000c104a0086485840c25103402145143c4500401e42c1113404802d000d07641c180100c04588141c8450481d0001d03da00d0403940401500c4881c2c0c2c00c085151080300340c0000135855000d00003030b00001c0055070405610710494000c0241059024034481c010a01c210000308814840441d44134050120411b0060395580c000d03406807070391110258240c4000a660405180c075680700c68024145403064811055a6120300ca118400b032400203022500308180401c48442d4910081681340b144200b5031351001c00c2d9480301c201005007107070741c5908190740320901c1a00a506000c1251010b000f400d04104410407800303e4115400f005141ca0b00702e03e480b10206150b60f000304031907028102c0f162061991191b0600e403032000f94000003502c441100d41ca80501005110366001e40c0c65001080d502e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 998512544 1250 998511294 998511317
    0x1b05072303210103020f010207060c0f020613080c0102160b0a050d0f02070309090c0302030f060402070c080609010605010809070b032415030105011b0203030d2301060201050709060f 80
    0x61204214140342a4824441000781c4002440e00800741c02c110202504214501e41c91343c018001c420078400900d5045411845c824412190041910788210780c10000c0b004483d449440400d0040c854103d51080320500c0d5000001c989200240f1440f0b440020723420744400d8101303440c0400340c00e040d0740645042441c0502074418407030301c00d00c00b0709020700184002003410001001e182d000c9901c220016800522402d406015110090185402050481c9011403451030150f100c0000f80b40083c000038440da40004803002030111400b0444007808080c01641c2aa081160784c1034001c002500c01d140c04113002200107503c42c032010038a5802c9501c10200c00c0e00d10b03600c0d5141110860540c0381000c40c444100403811f00302d03844040c1c41d44802c2c0000c02d0304540d00c0d41400000b4081c1d0085039111011229040341d0000140c07400310507034902c07031492080400d0900c0c401c00404488540032540c0d5840f40c01c40b80000601680c15080140030f01620307203540d10003a40303030441100d0a80b4440d070b440c0c001ca040507030070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 998513794 1250 998512544 998512583
    0x804140a0312030c0203161217010b0306040b13060915060203030411121e0703150e0703110102010b04050c070209060105030f1302010c20100c030207030605040311030d1b0507 77
    0x451a0100c072071040d2494032404405c820000d1f40081030544160140c04482030501750810300350400700d1119145c00b192980340100007805071000610041c0248c0c0c0b075030780d41038442d140d00c03900d0b00b0540c00c0118140107240e114039102000304041150504000070754000000c14900110840f80120f8103c51951040d02001081c002e204010100b506124452510031041d41c8284580035581607680e42c0c00742054911b0350410034840c1c1c86211400002d14071b0840c054504002c00541081280d900840300d031104155240107034010f010110145400c64182420800c0035186400201303140d520850301e6a8464454100465a9020880314130410305a07031808036501902c003000a03180075105241880c919a00745d40c40200c9101c0f54445e00079049000c0aa07429280b4204000da4000034552600306200c01641e1002582c481240c48003604803a038a8010030181403244403007440f140c182004881d902d2142500e09002041f549002d4481d01e00a50006170075184281c049506142d0049545284070b040143c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 998515044 1250 998513794 998513801
    0x4050a0e0c19170f01180518030f0d1a13090602041205030d05072c03010b031504030201150e0f070c02090a0e0f010e0d050309070f030804140a031203 66
    0x80079003800c103110096410020040c0c0038a80c00c156540c0250710484060780d6250468003610401c2c0c280312800040c0060082011078421121101d480410b0741d40f14000ca0b5513075802e640a51100754040010f10140101d524801011380354183d1030200000404400e00c3c100511440406ca032748880f840c03080325a402c00300d0f0071031030140e402018010b00d80359440412031092a03420ba021540c03500041140014440e4900c140f9a10201070f05080480ba42210b2081c42c03080600c410906c4031040c10131203011651402d6014101c11f044c0130701103603010210b81c0b411501d0790008036800c8005600b0102c004146161040350303c0101c82d4040328040c110348812200c010590b8000341503000704a9070191020240e500c02641c03900840c0000000100d50125070b40305814003d290300007484680c1041c0ca88101d5071000184010140d00c4c41c034009850b5201c21f0600c90500a00fa442982c0c6070380c3d004000f1050003585d600074400c403421001c0c004406c81e45801405142d10103440007170001060403c480042d14041e40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 998516294 1250 998515044 998515051
    0x1f0b1303030c1b0e012103120c0212030406020c1209010c0b04081c0b011d06030403110a0602071212150b090109050d12261504021c15060504050a0e 65
    0x110007801c007010b1003c0d03512a0055582c03015003070715480c000400c0605109600c03608074410010803006c0c420b20316140642242c0c5a40c825600255460b042442034074820300400ca040104010080e6403800c090500c040a9000641d0001180c003902648040020030a0704a5804a0b010b844130200000781c2d4994800e00e8074014420349510104010300b61404c04000c102010100c0340f80400a05500c8840c00104800034124844030340380c0c801ca481150603a281825a60701a41c1491b05d074510105200c9000c0c20044900030081019001240840400024009942c08843c503644c80c00340e0310303800c000098255403031425071040340014020148865402d20300140b02a04044c140f1440c9150382d030001c1110551005000d50300c1200d80030b4150741d05503200464401e036451080104607103182c804050036051001034001048034098105243c01500c807030301030b10003d82402d0440f259420064090f44007030700c6501d8148150a000703c1c4003040241c025016581a203078017501c0354016a04041c1164031004024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 998517544 1250 998516294 998516303
    0x61209060209040c02100612110402030901090b04050303070f08072001061806080601050a08070e091e0c01120509070b03040503070f03090f08010b010f0f090e1f0b1303030c 76
    0x2000022183d48441c01a9094140b42ea402003010b50b0170720510200701c854030342000c5200003441143d01c000c00c00071088142090800c4800613a03d0700c0f01c000c0c0900500c44030000501c14243d100030007080c48030100c090b5218207a540c9402d01801189403086032100011100240414070408510001800b9201140e4541d5400b400014070f1544030719810f030520130b190070a00002525804140321010090107010b00602d020740d0041c2600b41170070010341d1508440c0c0640c4080707042c0503000603a113020400c0000b0408501400c00c0401c5541d804c0c00b03585404403880c84a004c109070100c0328866882c140300c0c0502c40c0c91100c4c050000e16051000c1c0d0750a80c1e001400a848611090000201180928182c00c58180c800c0e11000d6034189400e40804908007541d210304001e9160442c4466140d0b00600c26484232400351a00e215290010802540e00800d00c1d08680140c250342d008009911007013440c0c140c0a044404000855640c0e20311758515144681c103110080c886503042c007000024015445500c250784035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 998518794 1250 998517544 998517547
    0xe070f0c03110a0c09060303031a101413092c03030105100c0c0905010f090903051608190e151305091905070201020d0b1905150903030c061f0612090602 67
    0x40e03454a0045030169000405c00f29900c03801042015014481c090740e1007080c8445030103006007440001d44503803010380742c081031014030f80890900c1c0d0000b0089540c00d034030942101c075042d0345501c25907004001540003400c41d0a103507625189101d032404044421840c0d854011469030782030006104940d8880032600301070000d03840e0075400051088030321501418550100003410343c07616507030300f244c410075a00440080c2e251581314401710307611004990b2810543c1070106045145e514000009201d83e100300d5544000900481542a0b0b00c03000005d04d42c0380c101c81140c10003600c989000c1c202d100f82d01440c6600e0301c01d1300e810000c9003030002c2080d50101501030001e001105019010341510000c0701e26600507540003074140d800c0c003aa4468854045000c1d520003412007000300e95080c540e6924010705200b41002c03000320704280060300440b2280d0390090152510b904203801200c2d5240e40596526824941540c200740310a040d08240350119482030795504842004c500078030004001607a01607038120740 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 998520044 1250 998518794 998518813
    0x1050f150f0c1009060b0904030804201c06060b090f090601031401090c020d05070b18030d0f0b151201060509011e08090706050a05070305090d0c0f0e070f0c0311 71
    0x7010f000e11120004041004078a00c00303185803207000c541294064601c2a03150b0024800407a42c80320409074400e910005400c003442080a52080c44548650240e43c40500140c0040781d02152481c1c10f203c0e00e00c80d0800b40701c090388800e600800d038003d0403100c64008845c02c8145400e03141000035580c01440c10704001550380c00900c10720041420981102e81c01c19220007400b0101581008114040c4005141481c00c01409a4841c01c40c61005040405500c90003641000c001e00203008640c0b18034020402000440f03000c2000101a00102001a01c21580344026405048607a01252080c80e901a862000c582c01c0600a0b50f10340c02007900c5a040000d08204143d01c80422503000303008403c580c40743e0940703141c42c2d80400c1c0707011100e8000c01c04111007400b21002c1d031500203058458040d0306007001174403240b4180c0400d4075562000005001e40302c1031000007941481a40d0600d083d212280f010200c140d07900d95064034900c128034410310006140c0985040424407c0509450902e103030000d4851040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 998521294 1250 998520044 998520067
    0x501051e090607050d230d201c0f09240e070e0109050711060c0a050f0a09060210020a082d15030706080105030303070f02030f0c0d0801050f150f 64
    0x200055000c0703805500480061940c19085983c1d440f4a06d00144800c48040000389140070700d004010551400c0c54440c0030301d82c0f0109950314081c078205184002207459002c0603140700d40791201012000e1400d481c188546041d200680140c86960f034018501c2100c683c05446c1101120700e102951a904581c0c0e14480c541054041c00b0786401019607455040c0c16504210303841c4100d4402418403000d01028040c6050f070b0f24004079140380e10210710251541c03078050130041074030310303206420f07905505601c000f5680243c070b600301c1d402c1c4040c1c3e89560b00700ca03658000c81d05980700701d1140302002404078900c0340c0000d10b1b90000710240208008200500402040f401d0f80c16503400310251102589040c81d01c0717400c0c800e41400c102d120020409483c0a555039450800407c3e01c0e844042c240c0020803040c00000307043c00c0c1c020401c0398400f100708080d060b034400803a11180c0c1c40703004465520f00042c000c400000f610349000c0031215507110703004101c100d200d1a82c920400044c0d01c02c0e4071111128506100189564 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 998522544 1250 998521294 998521297
    0x1407050d020105160302090d0602031b030a0603030e0a0305030f0906070b100501110106060813140f071509061d01090b04090e010c0c05030a0806010201060506040801020c0c0a0501051e0906 83
    0xd00c80e03800100f0503040ca1008810251070b2160316200705031042c0b04406030380d61040080110301d9009400182d80c0c0d207882c800c5102003555500d50351000c0d0400428008036440c81d038003848c100e900a96960170540210000c22203001054403020f40315904c288030324100e0328003500041083d0113004006500e0442c2e04d588000c5100402c03100c011011107140313010003495810495a1007a8a1610001c0005a08240002d026548054205e540121040200c64108001c2c0e00406841071318400440700b2025418007500d56607a60750103018071b85034088203140c6010b40076820076010f45800740c480d42c0c00c3e010b9041003001c2010303201c480a0704025220324000b54030300c10716004201820310901c01003440351002000e90b0035100700144c42400c0190085c840380101c0d0010042d121030303561178a009611501e560004034007500440d00030680c0048005800124000b0540c001c1c2000800901a01e8001032041c04124103004103114150100303508012800403100c0000900b40c668012403641c40c1001c81000c04101c59 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 998523794 1250 998522544 998522563
    0x31926010603020a0909020a0212030a0e0304080601240e0d0302150a020901020f12070803091002270a03121218050f06150d0609061d070f1a0a140705 66
    0x4264002545200c5591141010028080d0411b0541c5084904d0f50b0080d5207920b4034034403404141c0007001007201084c0d1a044034400d601c0340000c803900c41d0340300d4407800d4440600b8440e082c200d54070f500b400c0f088007080c071180d0b0b01d4869a039101c50344000c5066041c006031120160b4100c0460162110394100c0303802c0c02204a0044840b6500140c0703402d24038001900e0903100001218503584a032034003000300084203040343d584a40c0007010395100c2d120710f050640707018a80020140c14031b0011840c554904d1a0a00da030141603030304c41100766408240d106010b00d01086000103028500b0140403080700c503002d90740c540a143e45144000400800074104481708d20743c2040100e41c15042480c0b0b10b40c85001c1081803c3d00300385080407402d084e120350400103005041e4800020030494568001c0b00c14003907660700061001d00b5450342220564081104280c56005070700030000700c4100d440d008111003858148040d1340d00d00c1300f0440703072801000c0031059400b140002d40c910241b00701004404000384050105a03c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 998525044 1250 998523794 998523797
    0x6030612110f030a0311071e090c110d02060a180515150d050c03121c0903110114040c060905060d0e0f10020d060504020306060a0c15110702040605030319260106 71
    0x5441c6c0100c6519414854568451156405004c007480c01e000728024101c806c4403170b0041c0005100c0b213011403d480f0020541d4112129006480b4128916600455500e12a0807071520030030102844120910210580c071001815070750001d01c0c40d9821840c4400c50a0708410302007801040582070704002888800b8800045806030016a483c0620781000c1180000c407000d81031103d4145502196189400c040031004121000d03281c9860b40240750154840d01d2419035108001d022400121080070200d2030180c0e0102c2d002e05480d1000100d41c4e215056260584600401c0d4510f800000401c1e24060004c00d4840c0b5086c0c010035920550000080249c444980805100036844d40c8104164004540e0681d1189006500400130407990b540c4000480e01c0c0c241440c02c00d481f0001c0c10b41091142c1c002e000c4040e1102d2071800703203030354041c014240243c41270501c01c440c00d00416441700181900c038001e40d507280003941400b09003959a14006c4a00c941d4031840b1400c0c4001c12800c0d203000d244d100b40281d22510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 998526294 1250 998525044 998525057
    0x2e050a0204360606080f13120e011106241503010e09211c0e01020301090b0f0f0d0b07020307080706091b030b1f050d06020301060906030612110f030a03 67
    0x4401420382c0303500800504003190104040c030318043c0c0c081c040a0004117020046a81080021000c04142c240d04e59040d8015440c0c622204d81d2040241210803003510442c0800e5060314901c0c0310700c00c00600c0720710804c50003c8022049244082e01484180c80c0c0b868203501c1942c4480465007065100c020b54020310218841c0030040c2000b81019003010601700c0c2130b240100d030103400711019440440c21182c1d49281c002704150580300b41e5084000a02c2c4c1c032804401c00e94000000090094008d030040b010610b02100c0c8181107030260302c2000600d01440d0b11443d00b00e80048400404104060903141d4042091700607285060030b99070303500300b10754000d0a04842c89551a0740b51401d01c80300c19640c4005070042440b04e0700c282e0440d1150011108000d1105802402c540390b03001c4603610460009008007006803200601e00090724221020f03410901458000031001c110014000b8441c0c0520412248400c0007290110007648078001c8100b9103d02240d0041c422034100d09403a01c080180409641c026036528 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 998527544 1250 998526294 998526359
    0x3040b0705031308150f1317130603051303030b0604080d08040b07020307030e0609030c03101b021204090917070b0a050702030c151506031501022e050a0204 69
    0x9590100d0fa541000141d81e2101401018a0075001e6501d03400149480d5103880301d9580c0a403d01d1640c0700e44100408000c002071000141c2140c00c005014109040c41351781e90603c3d10b8090840880b2012961052004c00d29460507003c00e00942c0004189400070f04402e10709515650070300d1800d0021403d4000290f142c5040000f4003160f102c20b5070304110648003440c604600d0f61001001240c02c0713280782d4803801001541d0186035800700802e15190b803003d0151503032003103410000d000030f00c1a24906640c01e414864000515031020803809804280c0040341c0d0309003400c00f40c1440040c15455030031503400f940a5803401c140ca03502c130060b00c2000d00c14810500306107403950000054650191030541594021300060700d0b1108049a050000b000100000543e59620b088014480c410380107025006a400000e108001d40ad0341c4442107100300a0b003c442c8070000035000c0251b0080c5c16041592098200070000c5c03015811a0402600101d04400260525484007d607040c4141c802d58040100007003240305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 998528794 1250 998527544 998527567
    0x50111130f0f030218180124120f0b072102090406050307051c0c050418030905060304080f09031002040f090515240f0d0e0f0703080a0f0203040b070503 67
    0x707080a400c0407800342d44050310f160b01242180e0b40c0140c0862051504000280584056244500300c0d001080024011181c076042a035240c0c080b030464a07900c41101c1e0202249200c601041070782204e81c41503e8140e4008191186000180302511400c00c112080e040da400c0c408541108088040d80c40d400140d0b070b0030030081008201ca441c4d07401940031740c0040204100c40e680f8110071510308440c03124210116015460014222407903a0002e990051400d2035120070007101c002c50302c4c0030307034070a44588544544070010850745000860b4000e0540d5402c10800408040c00c1c4043c041b511400703401c65611140e005c0703a500c1aa0403a400c8640300b102c5044040001980d04d0281d42c2d040400c1001c60440c40d0302c10301c00b107481e21340c19500c04c491460325001c880074142e000e0811200702002e10201c19460701030034112040070b020880203c2c8010300c10840a0303030030020301003aa401200c1e40545000d01c2c2048074030058030050034100e0b40d4419030005010014908141100400d042c5100d00065030b668410f1462 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 998530044 1250 998528794 998528819
    0x280e0105090f011a0706020c0d0306081207080d0b0f090403081e1b03060a18050411011e0806120f0c1002070608010608130816060f02071a0405011113 66
    0x4003030040b0180b0010089454484140c0d15010144902c6503a2411141094406403141c1080191a0300c5281900807003542c5c55402241034404507030071350340711440340303010305029004000340076014401c1082a1529000182c3c041000b216000c0c0110044003041e0001515012080340c058010400c000100012140d4800981644040b005045138a9003009002c80c3d102c1c005112125060380c0000000c2032966403040c00020040240c44045001000d42995a00c090b04098070101c904410011003059550302512401818454090220418540203082241d40c048080c4c0655080440240c0940d40000305114a5010032050f100800c058045001031000c0d41100303001d610119048070b4403e00072a40e01016590464000c0d28016240d42c80b0100701d070a18115203100240050340000d03408892030038540795035030000d002d803c04201c08624124680c007030b4861703c0720041c180d00c0201c400e2550181210b80107900540603400001c2c042d00c102000c3c900f1503001c03134440d0500280c108010400c4090809 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 998531294 1250 998530044 998530051
    0x203182e0e19050922060902010806010306030803060d140307060e0f060108070303030b0103231603020f070807080903071d09031801051e0d09290402280e010509 71
    0x90741c980c8034102c1c0074030341c025181050103154030a1144c100890403003070680b01c030424822070010945a0440039450540c0c010401c0403000c0b40814018000100d0560080c403981085a030030252191655a030b4034104076800701481000c440d10032048240343c0d08a101003002d01361030ba01c90b49001903101e140c00f83c0c82c0c0c070340045510003100660084005024a0402148000481c2da1609001c101d0020042c010f9000c0d25100900c80c000040400b041480404180301150040e503202c90814812002c0010844c26445203400e0040503000400200001500001c01002142c0c020031a180c209803854001904103207080c0d00c02c800c0c0c280440700c140d0300800c0840003260401c0e1114020340c41c04410400c10000302510781c145038140840031415083e070046c1000c04104860300e24881983d21582003450f80300808084200703070f81d151800421900300c0c80c01c108501140e694010340841050f0380d268200300549601800c042003041414032550f84902c01101000d01400e80707500c141da0f00c2d604100030b00c80400c0008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 998532544 1250 998531294 998531299
    0x2010e011e05060418080c1507051c060b2508030f0f01080105060f1e22180b0105150d05010f230114031308030108030a1e0203182e0e 59
    0xf00040c0e405c4d0080102d40340790540c0001c00b181c03100c0b01c40300e600d400e1004c00d016440c0d0318081001081403041e80500200fa980d4030300c000a8406017400340841040740c1c4039005501c45001e0800c05180c9130200b111014011012140c029000c40d402c031390350800d098005666507080000010103201c6200780c0508041e01500d40311008000b81e1510a0000d040c0140c195400b0b4000c603c1d01ca4990301c079110031400070780d00703150107045410040f4010800405030110085c0c0d01281515141803800300d203038142171410885400c206881d136243d090104002c0c1c015080c040606900e281000b850101384000d0090ba40200080102202802d2810384070420002203074600e826444c0324800c110f400f5030b0308030b01101d42030f80401d2070340c1c0d4032030f503801114120f003a000a4004c2c242d80742c00b000002d49000000700400e00035009a0724016448085806040520b42d01042c0101680060180d40e143d03070402640001e034848010918001c01001c0c0b40c05d51844049080e2944181e1038540441da15250402024221003805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 998533794 1250 998532544 998532551
    0x4051201020c010b03030a0909021810080916050108010b030603010b0a030303060311090c03131b0e041202011b1d1005030403090b0c030403171308030406080703050f0a090302010e011e050604 84
    0x2525000b232140219000b201c2d810b83e40441d40340c07200b401c00c00c0c0c00c1d42a2040902980210707603010f8000352164008858400d590721840031544003107000d101900e0f040340c8040c0c50700300b40799081007048440e642000f440749400d0b660782d0710180c80c20f503141011503000718041d440000f00907080d420000002c0010700c0e411405680c0620503c4101c1010a089a03409005418400d030194214589180071601c01804066208203900c008607501644280c2d45004502c5224120a200000b1009a007030f0780290000d00749440455803c0118607004844040b64900480b200601400d4178000184000146400800004002004010416800c4802d1700d002d401c01c05101f034146500e40c10031960b00c0c41140001070106445a00315810204128187d034040386001c00e164807540d4680314502d030f0380d41051103800002140c104c003041d0154044e00c2910300401c0f007503100884c6540e0f0505032001500603580300b201159a5844a500d0703808003031156a000801190442502c4220000c2d400c3c141d58025121070721442c40c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 998535044 1250 998533794 998533807
    0x40f06020109080418090b310c0512150a0b010f17011806050607110315060a1401020f060a290303030a0e1002030103060906060e0702120c0304051201020c010b0303 72
    0x22010680741268904849100e5245c0c01050001c043d140f00d02c0000c11140e1140c0502664007400001402c3c001018001268034407002800035141140300343c40544040840c01050240d07040141e81d5241c50300c612022106800c040402d444031004cc2125560300300b0751f859003e242c0d60340c3d0040560301c00701e03803e1502c04909041d1070100400ca42041c0301d0041c2c400c486400131002e1070b0060300410b004003402080075032241421306102074040d1801003241e101c1e004e5504241000411140140c0c0941005403000003114140340340d01480c5240050001c2c1988070f006503040707881000b0400c1c940300e02c060a2000c03450203c4104031000d0810195411518104031100c0c0c0c030316644001080c1c7c1d0340125200008500f46e091030b25040d052000491001e501d0300d00000000c0180002d9400290301a4410041005035650b1884075400982c0305440c10f84c010f0b000b05600d40a2103100c00d01410071440103009991070075a9520001c0d031007264811604080c2d03500414060f120802c00c1c450001e40700c030b054002e1031030070030b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 998536294 1250 998535044 998535053
    0x207030f08040309061b050118060b06040806270303100e161b0f08180112020307050d0b01030e010e0a0c06030b1014070f150608030405150904090c0308040f06020109 73
    0x3c6140c000d0208010b0701c011b02d180841075030200307107070342e035401100800241058845080c0131080c010b4058403440d0401c0420f06d03240c203100c03085900710b40c1003401405098481104180002c600c503a028144038804085c51140d805082c00158000c22040d2700082c6400e2404540c8004000014104000982c03003042c15a1203681110780e042e0f8041680720080d1603010310b8509841c0700301040038098231440e80460019501b0501160b140c0940009032030340100450203400b080c4c00c0c3c2c40100c2d418400200705000700d1884100642000c0d4401138141000308250414401203400c41d0700001c03010700243e0144c0003900900c683c0511700e80140805140600455543d04081900c00003810b04520400c010f0300b040c1c0981840100940f00071680c03001d4003298020a0b811f01c2e00304c90840313090411050345001000502c094000044808843c8054803022007aa01c0742e000c091140c0103600c940c1c1c0c01a448200080008240200000186102d501d903a03440e41e061280958008800c1c1d08041c05582c541051207001c80d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 998537544 1250 998536294 998536307
    0x1608030a0506120c01090e1801020a080f1f03081e0a0e120d08010303050a1101020d0608010b091b07050f06042405070c021e100519020106030f02040203060d05030d0207030f080403 79
    0x82d5054644030095071144d023031128000c1c0100c40c0c8200c0c19440450b04203400c90340106c0d40303070103070719070102000c0710741c44910a0700700450a10341d80c0c91030201c4400d0b0820010b400070380034000c0408111180100d09002d002004803a0303101d24103c00004031a0805d280552030302040b00d01c4403d80d10030080080d0380e030703c0c10702600305407040c00081d050040208000715068407a0b0019008141050000e641301c0c158a4104005043e0a00a580c0303a9420148035144070306141c486103201e00c031030141105010b030350044400080e070300109080d55035024040200c0340c0307400100726032030007135205918400d0048880e40c0c4440d25a140030120340e0a26040009200f0761952021038060101e4040387e01151a0a182580c221009a00c0c0c0003244c0040004817a90510380e00f041c040c190007001b0244400365401032110407402c075005400014000740c0c4000304640035040c56805198000d402a0200c0003503180c544440d031030764011395221030915800080d48000c2581c02003001d0300c41009801e03d0140c0341802e5402030102c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 998538794 1250 998537544 998537549
    0x23040308060303070804080606010e060315120708061e0105121c0c0b07020a150e10020703020304030b0a06180c050313030e12070f0b030c07081608030a0506120c0109 73
    0x200200c03480460090364051044a441640c01407043c0c1c5d55981d02c40d401c0b41c4038003085800501080741540800107030304114044034400c0e550b60481d001c42c103000e0b00c1009000950005050300620130300401013080c01007000b01c640900e0014142500300304001021603030080e0160401c5000f441141600d00a0301400149080c940c490300135601c0f1310b00039000c0122401110604c01822010020b0184200319401045800505008911240400f044050303030780d040c5c82c051a80030340c040e4130000650003002419405403900500c42d1040d24a402c0d980d07201e940c2034140940d40c1e842da861744e800781000451035007100100075030058102071061100c0707100017801c1400010080303491384000d000313410101840b400c4501d0668100528804815050b8a0826650001802070000c3e00744c60190200308507840300107992269000001c02440d05403030360754007242501310004441a103011000c0d04070014661102842c450a04c04a000400f40f503c041009844c00508414200c640c10240303d410150b68800142000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 998540044 1250 998538794 998538797
    0x10e150c090619110c040e0706050930150c0901081f140405100302060a21050a0b180408160c08030d02070201020d2f0307020a060909230403 62
    0x49070080400400c6651040700c03003501e0003581e2280f5007805943c1002002e2440c880710011291850108424402142c802101654487d84003042c02c1000506c00d0004114104d8040d0003001d0200c521588440e208841003101018141500c2541031380e8001040141c5c55186d10408a001506046241a40074424098a10b0400c155540001d1f1444030300c140c2407046001082c481d404641d6602d4000440390345002e440303403185080c00046844000f0f4000120103407500104914a880401c44054589003803008605840020092021505203440d100d1389109001000002c115410b00c0c1007003002002054044001c044058024080410b4107c0c3c1503908100501d1400c3c0c40212b950b00b0700e80c085049a5000d41c1da030344000103000c101040c09401512410b0b101381c0880300b0511103013034152141c00d034806200e1441c11051103030741300006071010192089240c41054034a00704154003c5403103200c558000341c0125900580400c03800c0701c14440c01095200e189075041000c44901103542842c207007d8030240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 998541294 1250 998540044 998540047
    0x50904060b0904150b04050c09090421050a08180606272406120a050a0b1201060f1203020c06030c090a1502010516170405120403030e03010e150c 64
    0x101040358590220756090001401c0501c5441e140c6010342c9015440d0f0407102c20382d4141000040035042901800740190701081136107042071480e4003400624900200705690560032041e041c400889161400c2070200382980c1c60658030505200d02404441c00034246840c400c1400303004034040180418210780000007190039010740040c071703010b550780140c2e02070002c010040c0107010b0010074498019201407103034115640b122034501c100200320490065003200c581100742c00000980c1b48030079901070343d444601c800001450300180008261840d02c40e91142c03445a5484505200351510f100391a00100801082c030001082d04d581d00075100c1d0802c00880703000d2031b004804030303204590031000d482d010f003809031803100c0300ba5840780d400c0c100920900e50700c0051b510340401f24810107646009070711a00c3e40340d00d0303140f030080c881c006c49164908010015200c50280400d440c400c2d00f00d41e8003c0000318025910302c464030f00540201400c46940c2001c440c2c041d8080500644000c10443e0741c0da80c010510301d40309 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 998542544 1250 998541294 998541301
    0x5031e07020f070b070c0605030c03130c1a130e06010c0615090e030d050f010308070f0203010e030d150806010302100809070302041503051015090c020102070206070b041a040b010509 80
    0x1645080d4800014682c0c80c05404008241169900040c001560107881d8400c0800d540c0d91060781c0901c016104459400c00c10000501d00b101085082154144101a044c800703643d0f5081c12034000c1a8070207507a0401c0000a100072405180d80c8000c400b0f40385010380c2a2641c00c120001034980000c42c5001001c25864800709600540707010000c0004000001d028000c4259640b035031a129400114424900c0c2d14003808903d60242141145050340e074481c039005c0c906460764a881c005030030400022685992600055800c1c10b0007480540100e00140b07078081403c0540f10844210344100d80c10924003a8840001000561399103111002c6102c040c0c1016003054549404407401c00f00e541c0c101035081810710768010320701c0400b09554411680924140d8004002501105041d10b4a0340d03104016495501014026604140c1c000c20b03440d150380c000107203854116030101c1d0850b0001d12044c0c0354040040100018402c0340200303010402d54140b0380d203030280b07001e07074600100a1040c06028000c0a041000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 998543794 1250 998542544 998542547
    0x260c03070e0f04052502010c02060103082d1b0109080a05092106251706130e0102031b0c06040f15020d0b0a06030c0504050f06190804110105031e07 65
    0x4004105101410034013007841c1c004411104810300014444c01d013021001303541d442ea031040c0300310305403180b496001e040b0503407960b00c40701e120380c02485c2102000030a5401d13211b88084035105000d0f9207103246c40c0440e220011150b071044420031460306140b050741004000b400044420046402c200080d040103903e0306080c00c0811803144d0750424404c511039034010200400c00300040e440e8440c003500350f41c400c10b085844810703030b400d50f200c5103464020416007035000481c1c822691200e58011000b4040b0400498001c40d050705440003d542444907950000502421903013800400c1024990040c1041c1740203035192441342d0307036080204060f1110168020740c80c00c0104121071003103075144183e001d548407041ea401c84001480e40b00c0280e03214407801000017459a0003401080d010400360340301caa051525040c28480d9079054200c1207940081c00b04650f00181404148030001c1200c6642d81858a151501d02581064505203010341482024010072002000d12207001c10803004880f0b04101a440b450b60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 998545044 1250 998543794 998543809
    0x140706090c150309021e0d02011103160f0219061707050f0a02030a0206071b1112010c261603021c0e0c1f0207120311010606260c03070e 60
    0x300248140642c5162880c2642c150020a52a4000c6600d11440c212181e030303010004e424116007507040380b040a0564050745c0225189405070340700340142c03440c01614074850040a540b1120445040200035580d105608125100384031244902404803074890a03c48080c29a2045440240001d4074440c0001d4105200e502030359481101804504d460f940e16030710283d141d401100103080188070704800a400c651203054803c600712640008000040020744410400410100d1307000d410400d81c00e51902c04420074401c43c40c0c0700000380e03510500f8015022a1080245a400c0034040f1900007000340309034401b0300800340f03000381040d040050703980c0c084070700c5600d05040680b000241070f0f1402e01c21701100d07480403414030004d000464240d0794500c010250f026030080c03090025401603000040a000040813510020102e40c040e04201c1d000401090300b05080d204507030801b000140345e865065840c0c519800d6103240148450105015502c1c03e00a84035a600000380142c3c03c020206424082c6034032003d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 998546294 1250 998545044 998545049
    0x10b0421061107050f1c0309050703020603010e0f070207061403071b050c0f1203091c080301060f030f020a0824120d0f0203030f0f0c0d05090a0c06140706090c 70
    0xc0003804810410046984141c1160f8010340e400e014280c01c519241d8400324003a00707121001d108131408541c0400c0120024005501e04680c0c52041240101c056074841004c0c500030040d0605202c81c601c1c1c1070102e141404405040c0b0b0056611050080c0291a0008056803000d0f0b84413558544075500c0400491b2a280c42c1880d04107612455001c0c8400d0010102c0ca070400c14100b40d412102c005425418800745686000d0149410303007003400040000d10b07004440c04480d100c40900d911713400c0510307120007100b50310aa01400110300d5207401d280c081c0e82c06001e800b040208200301103041612000001e800c014008042c0506000011090b01d00a8603100f20502d400b034010300607840c03400810201a50310f85003008032a0100310801c801034909403002080364454502c40003a071407546c071200d40d241d03d0700d2001b401d43c01602100744030b52008110303548161807140349020014850801d00c0d0401750402111908680100b0403100a0768484482e6002114011548400c00040182003810800100344098 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 998547544 1250 998546294 998546303
    0x80703080f0d0f090b060604030b0c0c0319021c09120b180708070509010e0405070e06040908180907052505010b0a0f061107050a0509100f121406010b0421 68
    0x680c02c00c15800c0341e92241382d10078402c1c1c5030300505854003000c011040c012031100078100340302140002d1014548401038603600384000c04580c01d0151802042e0480001e50840100583c000107a0904110900610303111188150500f0002c40b801c001041c410304007500d8000d0725840d20680882e112100e00300f9100b05505403501520076a42c1c50fa011a82c40e003506101700c611079402440081209000502c8041c050756002c4001c1c007030303035281588400300404001c003100d500c1955003002d10b01040c610402800c10052010b5512602020601000819540901818100b0005010350301000f0304203103000140b50241100401060002e16000e405032041c0100244c1004c568000003692030103a80041c01501c00c540c03554540d0010303144540c0d03516101d911800764017901d80c800402040c10820411030b001030101403076824150b258121500612132075803140c42d444034100040418840c0c84080544c18802c180080c010651401e035003a20180900d00447d07581c00000601880d03102015000206003c5e8070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 998548794 1250 998547544 998547551
    0x11071406010b0f0a03150e1009050105030d02034008010c08040507170a0c0e0702060901090f110117010608060301110c0a080f28030e1c0e220b03070f080703080f0d 72
    0xb0623840440d441510402810080003144a15000c20184003002d003c0d4019824204410030f03d22407110812111200b68071038071101012070728a040c154000340d101500000c00e42c0d07d0008900d0841c2d5606e28014100b00b000824000050800701f1000101c4a0881c0c01c600e08880e085901401d015240030f0003031040301d040030009080d1841d200307401c0c03080b1aa9026a0815603c14030000c1c00e81d424103200500c41035400e040207000405110001c0100e00d81071400c00003120410b542400d0019081c0c2018000c914160308102003131500340260b503450b40c4d11070345007414924034580c0a40d40d0640305900502116000ca107160f035040c40c0009840d0b803010f003a24450003001402c1c00c005030407144441030760000f03804c0c0440280e00c0a00025000d00c0400403584076032042407580341c2186c40340c842c9207100d03900c2807003e20301d00c001d1505400d403000c681c00400e00006803c0000c0c4101450102a170340711508103500303444104120103012408108498000c90243c0d0b8030b6119400e4a070580c4203404502d80907514 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 998550044 1250 998548794 998548801
    0x7051206040201270e15011106040b010b030a06090f0e011d12030a0b0918150910050a061205241909020a0302090c0d0c1e0c0611071406010b0f0a03150e 67
    0x6c04c2903803008903401c2c0c0340c017400001e1403040075840b854216070103020380d03074411700420038001c10100850b03000e1744284c40003869584603010721095909c490f24400d046600d500260f00361480038403036800304100d1501103105000c0c0c44040d1944801103004088105140440000d0b0340c026150860580000c0c004c03c0ba805a24001c2040320343c0c04c4203101e4140c854800c95480b034803a9004120f581d4040e12408006005044a01d04030b4030207407031f0003807004011546032000007902d00003020742c14a43d80c2c81400501105800e010b100300100c410ae464590800141c0c1d02800302c0d074107902e18154102007502c01d010841f180f40340003140c1217041e43e07800207401c131340c0110400c840401c60b8000342c800a1070404051181e955100c00c111441181c01d048181282c0032840d480035034a00440c0401d41d50b610400780402c0d42140d006a0208c0368002c0d01041d140b544401f005a000d510040c4041c5000d40080d028460600440c5142d800e481c0c001c0c18014030038580d6440150406480380120a801450410013041d00b926 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 998551294 1250 998550044 998550061
    0x150512030a12110d0c0905040c0203120c090a05010c08251e02221112010f090c02030406110a050a05031c060e1f1707051206040201270e 60
    0x244104040e40004440005956904a0a0007903240000110003081d007070400c80991040202003c1c178080e010300035010000a81074a40b809903210490b1590007443d00c07506a0803200c250b9200003000d4020448e001c10030000d4940c3d5210081c02600e00c20728295144840c1881d11003051300c41c0c0540c0e80803a01e20700e0014440c44d28a00038000400303101390041c010081c1d00d04c14a400c03100b201c0e20020350228030304d01998608104900b544600e458180b80216129089000307284466102c40da00486449850006006070b10110300c040c0010104a40c00b004100310701d11000b51030b8002ca0040d80c1c01c0001000c051694401c0411402c0302c090703044410391f14880d8061805603034030351201d40010201d84220031520340c0048213101d520304851010100c200543c0d00c03040d41c145103400644505038140004040450f0000181042e854031905040080010174105410041d00d150029440320b682d9008000b04001030741e00c512500c1914060342d5844090707594140141d4807404060308105c90341c0720f51504008184 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 998552544 1250 998551294 998551297
    0xf06020307090e0f04060b28080d1713080c150403031b0903080702040e070f030201021506010f0c11031009141515150c01090311160915051203 63
    0x10545619030b01061540c1c0d0881007210309003140c00c2844030216000040103d920398222480c0000000c080580900e401129012844910303001d0505104402c0030511100004110b00c14540702c039800c099204427801c0071040940da00003000980c510751014280000c2003a440256a0365000c964140d8581512891010a21030406c88040e8006403d140024070b9421038403042d2003d24a0316510a03625504503103400138941c1c1301200882e00b02c3e176981030262026100b402220054402c2c074081d0300b1182c0c910b00009291407403541a071480c8081046c24020103070381040d041c5400c04168141407180510038106000c40d850000b60300354041c0074400c9075500500507030b400004080c2c4a80301d5030a4480203050456a5241d201210b106d9080f809000710f0042d885401000710180001082440c040062400d1600b00740c03c40b2010a445030b464081400401d80c00074210b07031001c001c040081c041c03807070603081400b44071070f0510480c0c00c150340d250101040c80841c410104041d2001034907005070302e5005265107989 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 998553794 1250 998552544 998552551
    0x91b13050a150b092b0209090a110102030a08013f060612051e030c0102041401030b01030c120c030e01020342041d010e07080706181703070f060203 65
    0x40d415a514041a481d41101c00d03504504c030040e00c0c0754240600d22801d00b4841844070241d60051410340c0c03000c0010317a0b9003002c1d5403207185030b003000d448050302c0d5280c400306090384500703960706541081c0500210725a00440705030444016031171541c401700c0d445042110580c100c0000b00400700610b901c009103030041103400912540304010411910741d5819651007048800c02c001000b82c2c00020305907409a0a942003965982201015a4907000441106900b2684aa072207100d003001c00015005d80740d80c0503c540801c031802803c0512402d00c5010005007030704506400202c03000c0d590205041d03110700c20f500001c0c42d10b9004008560b01d062296006003140c0c02c66441d15081302c103601200c0750318400048866561031040d098455170700a54000c001c0501198294021884d04400b04240303480e9003402803602e10604a0060441c144c2000c1c08a42041c075103402c51414004628000c0a1121443c01e2600446094a00d40b07504c041c4401c903001c0c29403090110150070801d05035002818807c4d80d6008601 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 998555044 1250 998553794 998553821
    0x10c02010b0310020748050a120c05100c02030105010f150f0c17073504030206030c03060409050708010507091a16021c06060e060108091b13050a 64
    0xe2184000082016031041d0100240325009801c4205030010300d441191340161030850000000c00b80e2103258240c1810400f15400700011b08401c204411308001f0245806084694108526003020344c444104241c42d5104e403d0103103d15000121041e0320402117840350390f030700800070b202d5940d482d04043e261001c0344c0500d102c5c0c0c001210f000491640030b0344411001003100c1c1c480c00c4890b4110744170680700903441e046002e4041c4081103040002030452090300c000400b20b1100c0080c1c07154094000148140c0203072010b0785d6840400050015a031a00183c0340d110136800c082daa0380b50340e410017080150000010080140c40780e4000402c4110b810340044d40b041829603106d440860350351403010700c940f0314182c209a0311326040103000000401800301042141c00500150460302940c00341c0340c802a440384090798840d941b25401c2c02050010216103801103024039241d4614182003516030307110100358480c15026812440c104950b6103d90f51641c440c1000450300b0015032800702c5481010340752081d40242d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 998556294 1250 998555044 998555053
    0x141002070605061801030b07140a0203070c050609131509020408030a020f15070c03090b0301080d02120306150310090911030f070810021b0708150c03130b0a0e010c02010b03 76
    0x183c05050a0340754140865950010490700e900e142c459415280b000740c050b100f0400c40c2150060078030441d10040c05440c03031076401196104046e040c14405150a40c02c458442d010070002d1001d15500e010210040000d8200c000600242006011450100c10f50106200f507001040c00108542c01002901032110b854094441c02c50741109026244c6400044101014000d0700209a00a1040d0f03011030006101381003070b80c0515214458002190426403081031b0030390040715142a00c030345c107000660542c81d040400340d0450800b0000585120350f03000071284048000300002e000e00d00c00c3d5038540d004250f0710301c0c2005400e8550901078079400d60107200314001d100300ea20906074490000f4030f02c003c0391042c4001d030200204c040c0b11000654440006410380030117100c0381c0000d14005100c00d00043c01281c005007840c42c80c00c10000807595005202c10310b0b49400b4800c00c0043c4040c811b42560495100d660700401c1e540c1e101000e00284089120403131a58608011292015015401400390303c07000c60494 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 998557544 1250 998556294 998556301
    0x30403020a060224061011030904050f01060207080f03070210170112200102060a0b0d0b0907030302070605031506070303020d02031305070b0c0312090f030c06060112020c19141002070605 82
    0x90400382c000c3d0b990319001b464000c50510b6072482041103103410100034090f2840c1c04010300001d800e07601c007a10300c440064180d0340100103194040117000e0052a0307030005800101d032810342c420385034022000081d004106103003020000b41d02c902c5070181c030720307200358a41c07a000d50311811008401c1004001c00c80350040c00084c40003002e110001d0440620a050f8003c24081e80c545c1d08110191074604081504859241c4c07a800015807682c484610840c0c085006048803407840c2002032401500b5840401801020030510609400b1030109150f2140c00362046c41e070ba11850f1501314001e1080402e22600d01b84084284450001c050111044081c061000c44001545424281c0c04da80304190b031847c0c455004100c0804421040c1800039030045802d025501e061003c514400c1c21365000d040001ca841d00030b1030800556680100003010700c0501c9000841c2040044c2917654cd8480083c41c04401010350100300307038100003440d2681000d204108007541d80d03030a0411a01c0700650451380d01102c4050504001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 998558794 1250 998557544 998557603
    0x5010b0901120f05101802090109090c0b030c0f0d09060501050102061311030708060702061f3006061202090105240a0c051911010c1101050903030403020a0602 70
    0x90314141c48919002c2d1901c00c1259440c00c4054020318000c44860040c0f0030800b901a01034403440841d40c3d148802c00245e04c6052040040d88101604010606440d1401d501c000c00e03c91148103064400b0343e480700303640f622a22000c05160040c0000600511800552048101481d0700015610307842441d007844070b6625070005980b00d04046919a1504010890403804140482a40b05807010054140c0d110b61791216203407402c00c181142c031400968080c00a1118482d41400440104103014000c2101a402c10348a0810078510f4401c50707000e640341c0d807000006041c0c1d28800311046a8811010030040d0340e10b101825041c8892001a84100c603144000075050070007080c4800d6803000c41180d0801c003c00c1943c0b0080b40d1700080250003c225262040000007001042038007000152440001c1121710b951511803151a184642c1c9810062200311150000e1030141c03a43c20511000d0038001c1e1100c4d41d40001c070780b65000359400a98020a0407030b0002e41740c0d13000309504001030717600d001d02100d6001c40300c031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 998560044 1250 998558794 998558809
    0x204061511070608071d030303250206280b0d05010c02010c0c0c030b10030605090312060102010e0d030e0a02130c020c1c02090c07050604030e0f0109031e060213090905010b 76
    0x4031400702c0c0380b003400200320b10b1095040c0b8140d00e09180800b5144031b2032a000c0b074599002154104000d00d4051f41e95024000031049140d07613207a01c0e01c024510b131310b400c503401500c1c0110300301602c0c000c048040c080802e400403500710485070f00c0094a580485030080c10091702810080d03081d8000340d460248038038911031141854911664100361f155100c1480d55903000c8141c80d0080480418800d41c800100001c0c010b805414092000c6200440d160b4000301e40e21b80036540f020702607034156031402031000801d5502058555000c5040d040020f41150044030203401c028944034000d51280e203407481991080b20951001c58010029070844000210a030140300403c44100083e518020518030750000602d49115001d5000c072500c01454108821076542c180707008420758046010824007a9803100d1410590b0300002c0a8000746807100c08103103141c03144e48004c00c180310095140d4200ca207104003803180c90380440d03003568500358201a00990701ca502c0c0c00104100d2004840ca54203103503452030946880329 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 998561151 1107 998560044 998560049
    0x51905041d0f0f0921032202150901031d0d1701050d0605041b15020c03010504151a030105160e06070f0b04030903020406151107 57
    0x4850380c00e030920710034110a5040c2074004101d50201030000350b0380c00505190070f07001251035013a40241440b01303030001c0c4c10001981d03440c0701680d6056031004520403541c144401340c0b60303140409001081c02402d100654000150007001100c111400000d2400c02d070141000a03c0105411141013480242c60791000b40d50400461080e8007904141ca1910340c2032981103249003581400001401d140592401a000304c1d13440000804205440348074402030251074801e6016942d5500703aa265006011041c903005004d000c00e1502581014007a0b103014642c400100f51494583c03101600044c01d10010480e182045801034507226142031003464010001a1640c1548001400014007503064140300d070380c0203201c20805174000c10342800c0c0c0003088940c4601d035000262a181822901c141150708082c0d80f181c902500055025010044000d94510541355011400c95402d12036860b6503851 = true := by decide +kernel

theorem cover : BRFrame.Cov 998381294 998561151 := by
  have h0 := BRFrame.cov_init 998381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 998381294 ≤ n) (h2 : n < 998561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
