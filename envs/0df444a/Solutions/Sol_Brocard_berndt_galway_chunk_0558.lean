-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0558
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:26:20.361253+00:00
-- url     : https://prove2.me/submissions/81025db5-c506-4bbb-93d2-44af2de367c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 100179856 ≤ n < 100359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 100181106 1250 100179856 100179883
    0x150509130e011a03011b09030f03020111070302030703030b010801120b04080f0304140d02070b0a0305151c0201030f0605152124010201060614070305090a0f0f080c03061603091205030108 82
    0x140c008002c01d03039034000120008c50380c0090302d44800070030724141203024100740030703d0008403130001402c2410150f00000901e90a0300960b400c000c0e0002d08401190074242c28406c0340c00700e003034204045001c81e40f1a40c04a81192040601d2803030811100d1045000d0f4000f15419607003442046200440c50b01c040c40500c045d8140b600c06400705600300840780c0118046c0224407000c0540e80d1000508030411003110100d41c40000384202410b8030703908181c6401e02a2402c3c101e000a04041d480001c5544030f004d0a010354070300400c0e074129511070800402c1160440500c1288076840140f071481103500c9400c0f03040c021800e084400003203e240f500d01e60307501043c80307200c43e04682c54050104800b41e80410b02030701c80c0e01400b80c020760780c0c15942401c84003405613840ea5603001040c0440081d400341c0f28241d4204036443c10080b030200c0303a940c890007170300c80001c554620f4043e00510b0004480c4030b50464402c90b07074003c50130b0000f8001e00c03d44070303e000b40300080d451401054000005003c40d503010800511a1010f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 100182356 1250 100181106 100181141
    0xb18090106090e0c0f030f06010c020310150b0403050a0803040f0c0f050405132d060e0c0102060907031a0601050d090c0501020c0d0309030b0703021c06030c150509130e011a0301 78
    0x2c64410040d146c0c80000e1207000059a01008100982e11400c03600010a4006046035110480001600010204807505a0a20040303d00001d1490a98010f0360200c0303402501074184112961100301c2c0590004008849881481ca409030000c1c0c0c4020f102409010342e41c94640d411424039092100300c0e43c0182c010b10040280140c00c100140d0a1400e1204150000c1c026910b400c0700042c00c2000c4910541c8001d010701d0030030310296000741000440403581c80b002d90848603140c4842c140c1f540c841426020240c80340180388584950805140400c0780c0129041c940145460b540d00e81c03150072103030f858070b046850380d4512504010725a410000000c2245040740c50426140c00c0380d402604001c041c0c4801000c600345400095840c80c000c1d415501e488113154540c00444140207005c60040407540022a03405031107001c0440c1452119031010884900c81d1103940c500040c0e0010081805610b0791035606040d1a0000351800e05005e009110501c100011201c010b24000404c02d400d440381032a48200084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 100183606 1250 100182356 100182367
    0xf03050f0f18040b1309050c030a0b0a0513020904060b01051c02120a02090303040e180703050a1203090b010504050604150909020103050c19050703030204080703080301030210180b18090106090e0c 86
    0x54407078140040e10804c1d100e002644041c503103007c1d07040c803000c00604c03a03060064a40704400d2204150b070709407050b061031401300410f40c0c4481074080e60070300e000c5000e03400000280c00030b4002032a6034070424840b101418070314103050070110908071b82d4854019428580d500410b07044a60511301300c0d51a0420180fa10650818030444e000c40d549015a100d09a465100b10010403402140c8200041e0034107080016a000302c2d0f246d0801994580d0700b080700711000b144441c00550350300d01c2442505041e69014900c031005901e0a4100409014050704540d48503550302605030b041c0c0070b071403416801003212400c0858001c00f540000750440300001c2201c460b514042001d11029100380403074020741c46890a12603102c401c507080c12002070043d504114154451442c3c040144401080a90b04981c42125207280350741c01110300f00c3e0070700301d1301c18443c5020f0035040b400e10440403001c0c0600b40c090f00e501002a441c5210b0000619013000a034000c901181c46000180a84480c881c9802e07400440302c440e907842c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 100184856 1250 100183606 100183609
    0x3061d0402060a0302092e021b0d0f0201021e0f160506031b0d06030807060b01030905060624040f050a06080f060f060708031e01050411070f03050f0f18040b 69
    0x510030f03800d82c90101a40010f840203941e03245084c04164245040600c0100d088a1609400c02050005d41c000584a02040c04100a80070130010001c020301803c0b0b00d0b030401042c3c0e0b41d00010410520200e056024200c0035a41040010f0440002220351400502c41d10220415507800d040300c00584007089800c210050107141c641200700c9410503801510503007901c822003024507117405410045061141490000001d004280011b003201901629081088003800001581100c6039100300400030340010000902034036010030403e102c02c02039501d01e8604400d12030a07515651050f0170207144600e070b2200520a41c2001c510050180580d810100703500e00b040000c240f843d100040844e44120400d06100080f0b031500c4040d42c11031603200d00e6003600c0e420301c0145503030300035890b500c8886081c3c06e1000000d00d620b41401603c11800040142d04e1034040780e9110140203070102501501404401c00c0f4840083c0d8202c0000c0c00e140c0603801c56582c6444420400603880384898074218820b03401d111034562203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 100186106 1250 100184856 100184869
    0x606080c090f0a090503070308100905010e06040902120d081501020a080d05070207050d03030902092508040f02090c04230a05040f0f0f0b120706020c060c0a050d03061d0402 76
    0x400445807550705030f4072035149001816100000a00310300000c5101c10170543c22500190003888d500801e60041a11050311104076182481076085501e4800003154541c101580241c00f81400039003160341070342980110502d414454811140040d505000b0814241548212070f41c40038424400307044601c1564032041c1b028051881c2c168039286d902d00c041140180200300d008010315000d0705131103401245050140050100c01416800303882c42000141a0305800c3c034808801445510448903075540440e401c5600c208010b1089812580041412000d41c7d54a0902c07403084c0303000205960340b0f604003481d10a00010004010400e10310260b4000010380e9001c03201821340314192800517860031090b41413005802031000010165140511207241d41c0e82a402c66501c5003006e940801408000058142d550406440341c000140c005d0360303d0480c0391400800400145811004540500c0e40302c0e21180d013440742c040303002d5002c00d030380384d03010481040400044224510801000e0b4664507064011404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 100187356 1250 100186106 100186111
    0xe0313051008070f090f06030c0216030c1509030f05060105011b1703040f0c06180506030105060d090524071b0b010504050a020c030706060603060b0a1209080906030f040606080c09 79
    0x7032100c041e84d80c104140c801c014410060100c461300340700c21550303040003070010301440d80110014090310014400d40f503044400101203d50041040501034134010030301c00b803000d01c00349240412004034000070208400c8441054410300a401070100d6515250014204c4500c480e00e0a104a14812160020890240703400e0a02a04407080540e03954861400807a036000300745000300341070550070011a50039441380722100040880d20600340700381d48800400c04140424440e05a020740100140082c40d81c19401074682c091080381101e45030038886080040d8201d6403420522640385020130042601e5200c0141c201004500380d40001001050f102c1c8020254140907090143d5110008100c086219604450802c4400d200707807500c4025900d410030140c4600c0c41481c002900341413000c2a40c0c40301c81c1c00c6825001058507803044002c19894150081c0ca40110b099481100074080c0c2440c5860b2030300214401c5685884105541c5011701d004000c980c11340d00130541c60f510005005849423105c060540c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 100188606 1250 100187356 100187371
    0x90115050319020309010b0907140f0d11040b091504060203090909070512030319050601020a1203110409090203070f1a03090c06070506010f0e131506090e0313051008 73
    0x1c0e40c940c1c50342d036070116045081d01c0d020360361807001080042000042d0320403204400704888254554030b41220031144100c5814000f0103000042244800d0103c8080003004c0b8041507480200702450403902440c695000780d8002a052200001d001c8841e15005034044400305c201ca040d60706081c10070300f0003076490056400c10b50140b1004ca01060b10b0680402c030000081100800c0042c110b070303200a4807030700d0703400954012106405501070354120703200900070310b8460f86060380245034040322502d81e8280b00a803940c001c1c05250740c803a00401188640b200401c0900001c0074041150b40f070310310501d4a010780c150710040d81c98089000c11720501191460000601d407690b00071503180d40f0703071301425414801c0441281e030340f010001404000b080b01c0400e0681c102d5552072850110555980f08001c0f48603800c65201130111480500000001c41c02c4804c28044100003400045183d15802a801110240d0b09000180e03407002c125240703542004a204c0e8003920b016290042c07501900c413400341c8604030240400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 100189856 1250 100188606 100188617
    0x1a06040213031104110c012307081306020d1107030224011202030c0402040e1e040309030206030903090d05010e011808070f02030a1b090605010203070302061801020705030705010218090115 83
    0x60005561300d801404203540040398180d81c881c41411070324001e10010b4074524448554000b200b034007101881c00b0702c6c460346803038441c002d140e9100241c074541004020070498020794280400081d0b00780922803461400d90010003a40d80c1c8a1904000e46820407038a02c030038030550080913112506002811301e604480e00484580501c4216100207820095408107041d00b10b840403500003074004041219074001d0403d0190342480c41103070030461300940c1048501070041084840704100608050004583c80b41e032030019681012641c2000991500c5505130030f60b0142c3d104c01c10b102c0703c2c04d003e10451050490040c0780100c401101e0352003519a008520014095145d02c00c1c4030025034078140946518198043c05c002050076040104a00c040c00a0050518591500364003154039400041210801a0190010203a90340c8540f1039a01c60030010241103443c2d50241315041c0000d00410103071136032500c200005070f03c0e0040c2041041450440c401c40b144240e0007100100503d48201031402040c50191406 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 100191106 1250 100189856 100189883
    0x203041a09070812090109080d020616030603120f02010606050a0e1203070b0f040b010506040503060609040c0519090b090601050a030507030b0901080d0e03032a191a0604021303 78
    0x3500d00340001548010305134000d44c000b06000301505002456040001d80703410745129114135007a950383d0305200761392015a1040000c5009044c28910300041e8054900d80890340640ba5654039074812030000302c1e08080740c40c444a410901c1d03020300a1a0103803500f4030744a800d00480c1d0b90001c10103070010032035900989085103160000c0c201030040380d254a401000c07680075418400510150101e0403101a00d9414101c4004500351810900711403ca81c0011b00802243d150141003000b60a4044d00880341c044640d00001080d0700e0b0041d008000088681036000c0d003500d00410b25040c1c90344494610310038201b1000b0412141c2c1c000d801d40303114000a141c0002c06a03508603007500208005c14140780e0040801c0c00015507060001092a885e1110303588854981201005260b602d00800c0c0e10344d035060b088c590140759517421600c2c0c04105a200042100c980c8030010261f003280310110a0b003a12402c141e0164540118803170102c5640250050394110300c0c1030030f50b0702400382c00e2030302c0d000080501d002c0300300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 100192356 1250 100191106 100191121
    0xd05090a05060c0f01060e07090501180b030603070810151706040308090102090316051311040b07030e0d050c011b0201020715050c101a01082208120f040b0a0203041a 73
    0x543c80c0c0d044c103607008000c040d1b01d030643ca03c52035008847c801e001a1040c9000b25595104584500300c106105503d081c02606000d281880c6800c000c08040c4c01d8400c401e0001003800f030411100c030842900c0c04000901003c945000c05214056411440f40c002c141d2224050b0380f0000a115580190503152002881e19a06040e5003e842005003c0354503200c0d030320300309900c0182d0315000401c494040f640404600406c0e030041d020b42d200341c025510365040c180030030025804000002d0001c00d11a180036050480c40c0c0300010042022a1800d40b200ea0100d84c4500555130402c1194800c0300414103900c3e901740d030642c0001e42e00e04041c0283c407910340c01c080a1414040c0510305490000006c88181c4112481007a9468000e0403140d00e00200e44480328010842c80d40920386050180061181e50113801960ba40b0a022910016074110f400038020004107a1000c5038002c018000e00d0403c42c10840303400d050070484403d01000c0e1141d2406072040090000107403100000c070441c1020080461910703910f1a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 100193606 1250 100192356 100192363
    0x2090703090206160803160f0c1101140d06210f2006120f060a0302060409020a05040308211e04030305040507050301060305010516020c010c03031a0d0501020703020d05090a05060c 79
    0x30300190344210758031034013000c01c50101c0c090742c410421145641c0010007404002c441108152402001003171500800c5c03c0070400104418090040c18106000c206280c10420340091303020045e2200c009036a03881c140300c401c4c142d02030011b5201048501c00c50031010381d10385a0389803c41650007091440080c0f1811300550840706e01ca0708458004000c2ca4035101c2140300a00c1c0f860044131070b2203050011078009040e0345000341007a42629009804281414200b888810095000c46003c900340703c011f020010004404c0b1000f0700e428100b400844509022014041001d04005013409040540d00e10503d5814402007800690285e018a0085415181c1d41407803400c000d56500215055400d1810220034058150006401402130903200d0901c3d00018008980703814684109d54009003455041c20046480303900044021070f02181001c400d41744050000e0103800294a0482c1c01d07940120fa80310605070103000c8a03208641340e0030482d20f0140e10b02c00180c1543c603e4014548240e00c0400c12901c500c2081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 100194856 1250 100193606 100193617
    0x307030f0603060501030b09060601030606120906020f04080a031209030e0628020d020c060a0206180309182a030a020a0c200a080f0709090501090210080105011b02090703090206 78
    0x1180804c16943c480c20459408941102c00c06181c0c481c840104410307520070304c030361000c4400b2541e5100f6180505184c00020342001c010035190903801703000c4075684040c0710000308010300b60071008028000c0d0a10b800b034503580304425014031591502000720b0120350010382c10300910104440180d610806a0701d203455045040c8040100e040c03184103010800c507000503031544005216000c90340300e44407440800c06940708183c9044010380210300401c0b00341d1082c240080002e000c92041c1d0f800c10302414013042c481d5030300070f2885c112080380b81c042c407500c09a8008a20407010800b03400b2400079a151f202182c4e40d10000d000d0b00f10055000030f080c074455102d01451804079a00030304c1844a8801104402c2c04000c0300301d862841130344200d40000c0c40e444006107004100b0a0365015140080c6817990501c01010f017880c044d2855500d5a59a40050307031020003481d10800180c94a030455410a030005040b084441f4007900c244080380d5154002d681d40c8141103901811614003c5003a200c90310229445e40110f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 100196106 1250 100194856 100194863
    0x3010315020c03162405060a12121b0f060504031b020a1707030c0b0301031e0c03120908030c01060806010603180b0411030f011b0504121101090f14030f030a050307030f0603 76
    0x170700c2180c800c078441e65003040b030258004658054805482d04075100c00003a440d58010810b03401c1d0034411035440d0180d03a5041d11540e00c140141900101515000c0a000e00d0b00001c8891591343c4080008168210025500c0a00113408110b48003000750301180d0101c0703a81c00b42090b0702a440da80c8841c418801c00407072001e982d1041030055180e50703884115a20b604280011031b04084c018007074014410200040050040c0c000e4404010180382d901c1710a0381c1a859461182040281c480100d5806001c20090841030307554000080c40c2444c2c44803942c105441078000d51b04050904688442000344e1152081007150045902200d44e20385180a895555254003107903011b002e40314071001c60300010b501c08116840311042801d9814801501102c642c4194040c90040d041c040a9400204482c44860350f030004040c10684442615540c80c510840c84541c4080a2240322210401c4542010b00c08688044802e10045060808450300907206000080006003090340c0c40c8581c2c101d071100d54100720002d542 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 100197356 1250 100196106 100196153
    0x31b091c05010605010224060402190c0215131701060f030c08070b040e040809030a021c0c0905011410020a020409030306030303150608060103020901110d0503010315020c0316 77
    0x1946124000c40d4440d290a460552921070005110b50000c1075542d581040c680b28162140300c03000b030400071988040d001541140d82805a40f800c1c00400908022045041e01e4a4030544030501c1040422302400d44104070030a814442044c100981140c55400c0d518145004601040700e94603050042009911002c00e510f4104400404d104013581c00005640d1480c003920052522401c094155115601c03030700c0500425640040c0201d6004009414580002415516404100d03000600400c4500801801e4040340b8000b4a00f00942c0c101c0c01c6000b098182802d001030740c5408071031145c01b41c254160500400c2d040c28486c000610038061030b038005a004004224008840c02e008000b40000d0100710042460030300440030b50018169024100c400d1965284095547c020044002c1d42000da90340303060100c492000084c0c040305101c0e00800000c2540c45035169899410500300740c403805c0c03c040d80c40c940704000a031003c150100860b00d20303c1001d1002503e1445514114640c0c200450b00c04001d1007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 100198606 1250 100197356 100197379
    0x3030302032401050a0c1a0c0a030605030c030a0b130602030f06040e0c03060106031a060d09061104080a030813080a080403030b041103040215090901120201080106030e03031b09 78
    0x58060380034500940c10540c000109202456800e49100e03004410b26011900c2480400c10082c815181303980802d124803c10702101800ca003548580f1001901e00c10f80810000c1103400e416581845500c0040c0701c218010030006661002080d190590b521001c2e00b03460b8040d00180c0c4d03016048002c421500d520420440d500c0c9495035540b0206042615080c0c4500e04010924031900c500040d51405440c00070007500c090391034010260f0081c09800b440802c08000d020454646d581d40d403000d8a01c0c07081c2e089010580b03060524003c1c048901035124030700702e80424401030085810016045060f980d00d800c241130903031156a600c081d00a80d02e00b001b450381d03d00142d51208940e11071a41400b86100e43c809005200310076041005035001810b800d1609081800007038050316291601408449201c80c0c0f080c135010503440403902d510401d0708a8981c07426441c61410441d60300940c2c0a00402440c907081207880e41c07041e0f00945900c40641081c0c1110b074010a8142c0f103031000e00c102c81078000010007818040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 100199856 1250 100198606 100198613
    0x3050d05030a050709031a090c1507060b060c06010303050a140403030c020a08010e190c03080403050a0b011d0105040e0c09090c030601090c050901180807030305030f07020703080d0b01110703 84
    0x69204640550b0700c2e5041c00003260f65503001d5824401580c1c0d1107010840e4445031850004036043c0c00804030b2821344102903c155040d200c504000c440003480c0b02d084c66960303186040450a41d029469038038080c1d02d04005609050901007280f0741940c1e80b614004d5035415800000321981e04407204211030003c000103000080582102040e0340d202e01c29103090311100e9a41c2c000034201d545180741c4841c0354000c1406450900b800c20303524103101d8854420700000545030345072800d298105030030854155000c1c50b080e40074484c0058003980104036800d04002180d00d4070050b899500018480c40707000c0d0703495030f81003480981d040c884009168000740c002401c1d441c21160031981c1f0062200300901070b0140c0000404d00c07040c1c0c3e00424103294400e8131554a0320310040011141c01003044040000c400f20712202003906801841142d000350300a130b031800d441c1c0c2040307400a00c68880203862401590b00078142040001c55000a03100155250074000800140b1600141c4401c01c00301e4001c9000d019091010040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 100201106 1250 100199856 100199867
    0x803010f0302040c020d230705030c010509060108120a0f0c1b15020102160210140a020309040b01050a08220b01170f070f0504151701060501080901060317090102030403050d 76
    0x700c0340200c40900c9070003d07400059803500d030305640120003d41c00171152042d5009400d07041c0440b01d0100b103010b14190032910f0325410f580064000c05010394540c4d0900114000404c01c580c0582841c01c007070040c0c01182900c003025032141220032410310900389a41c46400f40500d00f440381c40e81c1c0000c007201290b081258198080c20f00c60260384100140008880300c841c0c4148252001d003a0301c4450b00c100408503400b08800f2100014900c03082180c4035080004144055002c0e007202185900215112540341040006440c03102c3e247d00e04111702403003264a01c035844038040b40c2051018122002d104070b10802e103020b0340806c020180154502400000e80c1c1c2204120140800ca001010f032020300c4080c3c1c42c815111801c51043d0030342490160000e001c6842c290740710b031050000114410021755514810380e2003481c0395000400c65a5991202084a0750b0001142980a2117150082180a056541d44402000552b0212040c020040396002d00703a4000c01c21036010310382210441e0065151b10400910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 100202356 1250 100201106 100201109
    0x80a03030905070f030206070209040f1a04030f08160f0504080f07030c0e0613050703230a06090506062b0501120614040803150103060302060a110111030606040e090a0803010f 77
    0x3810b202c0c03024000b412004c0004070314145c0e070307004050074076000300f503001c00002c00d2000d84192040c01c0d0b070030940c80004400804103400350010707045400a82c6082c0c10081e15024204081c0001d000340750042000610f204941c1c05070404e0395040060111034012403c580c1c50080360070030381e914031585081488000001030340900712031041d12014241900c5d1500052144070544032107030882841010149001c11540044e07502c12031501e40013540c0906401812407046080f05245185075200302800002151409204080c01448200340007900f4000086001c41c41202003a18640c00317000d40c4030f070300c601c44214050001100700d1814005d558441c070365600c1c91004041304030741c0700e4544400c0c2c50b502c5c0010141c3c50311480d00f10340103a041d40e03600002c910010101000709070401d680c13000c000c40180e0b5040060b060300c600641c1c40c2010b00003084440c83c2111b0700002407036403c0c0410300c1086290b6441400f21019144811401c0c462500c2da041c1181c0343c500146d000078441007022001003060a003650b0001e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 100203606 1250 100202356 100202363
    0x12051201050a06020a03051b120a0201180308010519090218030706020a0c170114040b100501030b0907030213080604050c09070c03090504020a021002070c15020d020d0810080a030309 80
    0x12000d980ea0340030000d00300050b01c00e680150300110340c0d0001090007200603000032149403000001400129082e02c0c242158425100072400001c1520544150309120f404003c07810355004105440403a01c01078182d12052140078841d042c280d12214040c0f941960080c0100184030044d5140c44c004240c981c102488030072003902a100d2008000b4100e440058001c0b0303000d070400340b044030090070420340d600c10304032410240e0200d6494851002052109011440c030442c000c0740e203044d007402c118032408034503130b0319034840c6040600786165814140d480d0302a590700214103040050b5102181c007000f81203817a59a010429900884e010407040c840c4c04528502d890380b00311081607440e80c0d0090159a00c20200c5c1001d400200c61234418003040c1055801403d049006004a528509405072010700344c2e40403503c100c80484d00c042c4200b203151f0002d03090384001030060019180740b2030007900096552012070240d004010401c40441d041703201c1100010098042001074480c104114180540648001d58046 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 100204856 1250 100203606 100203637
    0x30309040f05150a1406030705070203060415060f081207050705030d0e0114030903071203020c010204030c0f0b04060c2d03020f0c0a060f03050406151701451205 71
    0x141461400002c0d200c169620901d440c01c0005d032810502005400c0202480c0c00d02c00c00700100b10141c2e4080261503c9148600300100312104412008425030b07505600039207107842d40075401e02446078082030710f4855440501010f91616182d0502c0c03840d110056121a815010781d840031614558130a01403044048203880e5640480c001c204e0150051004840145a0b030f00309018180018054682d850031001c0b4030f2801500708020781405500f2030b48aa84101c40c0b44003001d00070040c03c20040810700082c00f08200e8a8201881c001028008c18215500140700d101c48050b0b09800c100202d42e413030080d10740d030741090821640b1840e0203592070680e058040358074456080020810314100488e0002c0d0740c0030f0f03079038600741c0500f004040d070107808080c00440c0c0048e159000d0070000704004c560300c130007404500241048041d4100f105801c45001c1900203610680c1560b0075a80b005084200d10307010040e080c80a0a00c100806d00c0000080c0780d100c0003460207011401d818400c0307034050042c4c103183c019900740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 100206106 1250 100204856 100204891
    0xd0f060e0d080c040e010e040f0c06030b0a05060705060103080f0415030f0b0d05030a0309050c04090320010203071d010e09090313080303100b0c100f1a060c1506030309040f05 77
    0x1c3c19100d020328815a40302e40078501c014071480b1100c4418981151069154035403a4910b075440501048a607041100041d50351110344400b442c1841f80e031002403905035041c610746440ba4807116210b080c1400b01400c84d400000b410b00115030401c0c04c690080400000b0705800a44001000b8090300c1450400385809044c850f401c03c061030501d00900b410755001e0011460502d102c00c041c1d019141010f403d413034600809061400715140c40c01210b010a1084d9203c4c0c103140700400203108051001c0081a6450b8414000c1181040d00441086885419100c0c4194500c940000403510714050140303013500011782c2c0701440324090001000e04440c6194418001010b41c85000140e81d0b4001100c1182100b403240340b041000000040041401c21500341c00e890151422030017020540b16440c101c004e0813596007400e50315036010000044100340c411242c461a1003103416000da0b07684000c51903640f00707504d0b190200d15195410800c4032a9602c000d0702c02d020380c01a0480440092200712051035a50bc004280b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 100207356 1250 100206106 100206121
    0xa09060e03061603180f050f060f010b07061e0f0923060c070204090b01081516171f0f05090a0506030d03050903090406090e010606050406020703020d0f060e0d08 71
    0x14140d100f010840602d141c642040b5200b1070280019600c00c00a07207090040d0980445c400310b00248903030740110001c00300000d114444510b0068014148104100d0200040c8200110340d400c0b15070041c2c014802064a800c030000e2410715040c8402d400505510301000c030312826856030041030030135014041c950b40a003250320880603056090308404140ba003221001850500070300303001c6c160260000c0c0000038243d80c10384d20600d10a200380c10204459005040f1102c03d68103204d0720f941d200c0d94030204d802020200e20782c003400300c00010815138100d0100c400050f5882ca211102042d11800f000d4800c1c48840d9107034001ca12000b498000c00b4012841000021000800c03805407034000c0c24040d00030551403003200750450040c4005081c0b0507442c0001c200c4846c10381d90b280071b600040d0651041c002600040d000f0301c0350842d6290361001d400e001c1c09010400c00b0a4010405004894059910600044061900280480030707218002c014525050401d424031000050404040000b0389916449860f00b9a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 100208606 1250 100207356 100207363
    0x616030e0304030201031a041107151116050f0723030312130303091b080f060402010f050f090303070b0105010801090204031e14060702010e07051207050f150a09060e03 74
    0x22103000254020042000154405e501c01100380781310442c5038400d04032500004058400104005c80460004100c00d01440000ca0f090344c5800c1c1c9000c070801108030510f50320f03250f034003807000046400144043d40d903040c07100c2405480c09040c070204c1130f542c401c0d031900c0012508025000e451038100220100011842c2000421101003503843c0300d0380040c0395a000034a4440250025046042640f1410010006081d80700102e103c0d2303601e0401202d81c54100103406e442e03c00304c0c80365501d03203500180c11321015036001003580400d00681d15205030740700b8907801703910098803e410502d138040c8000030b400414060480d02d000d041eaa0243d9441105903a01c25201c0103a004602001e0304a0f4015600098180326130ba103180c1c0700d284614000f9403080c07081c285841c2442c00840e40f420240c0d443d60480014044113100c503001822040701e008011400000b0f10680d02c0c0317501c0c09a1401400b5400d0110032035510050b4800c02c609109000310703a00c1d0102c5100a0680030b20380714903800b05054a1008145140c00f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 100209856 1250 100208606 100208621
    0x150209030601030503030a060e0c04051203040b12010509160806090a090209010305010e06090706091e0b03040f140102070323040806010303020c031c02060a0b060d022d0a09030305130b0c061603 85
    0x21004ae40c00c0908000c02c00c0121000440700d890244070421000138034504000181c003039400b0310308804c5d0b169031601c000c0c4503c02d0710007010304208410100e100f50980d50017503482500032000f0f450421403903440c004d20384001c000002020350300683c41d400000c02c12005400ca44c160401150070b50fa0207498840100b075840d4000d00500303020400040c003c0c0200c8880b40c84800150300d10f9840842600e60342c0e01d002e641170f801610240c43c0400482041824400d0305180c80c0b55800c0100001c510380b80450324014048a4817280400d10010b00140c5401c490b43d41a0503a0302502c0500265281c07540c0d01e19020750380b0302e100341002d400b07030065010480e501d0400869120f4421100d070054441c69480448903402040602800c580c0600b00f0700849400500510290244049029203c1c105050300300e00b010200082e1030340400700003000c0002001496102008400700d0307034503003040354803800c1d2003ea5100e03001440c1c2190000c504007040740040b054000609a006004224410007a01c0000d1412029260078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 100211106 1250 100209856 100209871
    0x60206070801090c12060b0a080c040b0d020c0106170303090105060306010b030a150312030608161215090b072007060f1b0804030827010903150209030601030503030a060e 75
    0x1e80c8010404042207400011079620302d4034040904112803c03a000c1100c68075040010070410101d0700420403500030425a0300580031a003820b0501e481c254108a8912404c03030402c8040e90085901140604250400c4000d0903a8810450f540102120001e0382c07a08100e4aa103159030800300882c42c141070100d1501c1c1a5018000c0c42c0e0f2035613940c0145200540541c40c11580a0f4160310b030004040360300d152106041c00c4603681d0110314a86040021b52910344002c10710308011606000420211008807001c030321035940001070b50b483da80f0f400040d000034084071700701424a41c0e02404011b2160780c0304800041e51110800f21600c0020b0034400703903950316818000c2d178012071508410350542078000c46c280e25200386503154202c6902117a5943e0306403604590300c210703090800460042040c099441d100c07070384404030074002244200e0210000702003d18034400a4045010840c01ea02c0d01501b9804440d8284409400c5030000d5960b464030315940e038001c8400500c210b02d050380102e0300080e40303000c440c0a0f696 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 100212356 1250 100211106 100211117
    0x10603090b0a1812020f1e03070b040503040306020c1f050f0106030b0a080a0804080706021501030b04020f09190b03030a080103080a2c04060506090d1b080118020a06020607 76
    0x182d080c034900c0105401294204800640e5072040b00281c007845104201a50940c054071030003031404180d40c5032040b03802084043c03140c84003030030000d040b0010990f8401508045082c0c00c44d1a1810002d00f5445582c101a1180f4000034052600000004034000c065004240c3c22155501441c400b800b180c1c3d050300c0800f44200a0401081030314469007180342500c000401185010781c0c1c4581903860084184003c0750806030100f01041b459200340034002c01020240080e007545580c501d29150028014000146400c1c1200082400c0d92112400e641c00303803001808441f01402c020a03c0250321803a00c01c0b0303000107403c2c10b02c81c00603420301009a911a449076140c0c08070503400c5648104142c0c10105a000412078010819038521401c103407134802121080206001d81c1c0b070800284070a0390101e4202c02c0c001c0c2c10820103e542602c600c19110344143e0440000c4a400b00840d602d80f040016640c824800ea41c24498a022050003034007007044260300c221036541a00f0f641d030302d0680e2508002c4601102144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 100213606 1250 100212356 100212361
    0x504030c02040924060302040605010c0b01171009050609010507050c030901110a05031612030606050f030402010908060109150503070303020c06030408090415080d09080303310f0b010603090b 84
    0x92542040240d01e00c100c0b4002028414541c40f44104c21a051011000070344504041003581028410b1801401c001c4c03030516214911034898034074189041c8511078540342003070540681c1d10030030710207076001c0080f40d1400d000b1154203040007941e46c0300540d0866099460a408111301901550844041d80d00d15800345d07040411a0005507411031a82503104454080c42d8161000244140028640080803814010744c80980307082c031442c00c103121300c1c1e02070525142801c02c1c03009613007060690310554080f10b101556680ca510040f244248140e22640341e41c487c2078004241d40c242c68012000303621501d407a02054940e50340406503201e14a11019002d42c0cc12002d000490821200550740f050007610010300d450348500102e011204807920b10781e00d0412089041c00121014403000307107802c0081c50103500c800d0510300c9658981c80041d1201a0004100320840b0003144405403200401c1a03030480e011003d080d5080c00e4089041c906011202d1070b803481c2c00460482e00a200e205405608070744600c0e680d9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 100214856 1250 100213606 100213609
    0x8150310090204140901020703020609030702010e04110705010f05060310060e0c03180304030302030915030f01060f020f010e010204150c0305090d060b121c09050f04110c1c09090504030c02 83
    0x100129141039810a4a030380001c080d65400c135004d180a8072640000603036510b01030030f00034105000603010031300310b130810010180035030b1740452072050410003150005048421341c80d015901c3d20400000810b03035402e20f10303c001401040d600080c030824065080d40c03a5001505e03c6c0740c0440e0018025061181074210201d000100d6001c081c43e4001ca00807003035081003502c02005450358101760700c1200143c0c40000d082c0040d042814100f0031942e41600e66038118281800d010400300c005001c2d0f041040000359250540e0780c4200314084225420304000c02c40c1c1550500220702070b6100780200e0040281890075038003124882c044035010325401d580e4450174139120004000804200b040240c44064403515108003596907004440c2103043c0d0131004241010100f141111400b000341852801d00c142c40508221545850360741140e01001260300054400fa0301c0d0354a4114058031080018604c20b0a0800341c6001000b11511040c0b070705038441c1d4460aa907070070b140050369021207004001520200c00607005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 100216106 1250 100214856 100214861
    0x9160605190c1a01050109050d020d11040b18010e0906010303050d09020f10050a090e0108030409020d020d0e070602102706060e0a06030204060b03061804030e15070308150310 77
    0x40c003207900d030031078100740c5030f8441883d009600e02d05044000c0300310300100000d40e00506180c0050074203441004945445400003000c09080440c050a2181c458910b20b20640d250b074012200004002d25814078103001d840d103981505c2090140410215001c40070501156001920300c0c101c0c0d41c160342d5545004070390342c0341002400106a007283c01604000008820360344140d0081800c402c1552810b4941c0e40f041002840f000da41c0c1e201c0d03008081402c005000001010040701d041c0c030318001000d0303580c03034a4031482c80080c07040d4001420f15903c3c2c09005640b014012440b0700403560150b0845540704020442041220004401d600300314280c805e0004004103402c0700d909103d405503e0000740c0035500c091f500c003200f60458140031129901c80e0709008501e000e101c0e520260601e0341046046191240200303038130500b084a481040d15a1000140415200d0301d0200c5041002405ea08036143c060611030806400c100360440c04140618000340038102891030300d4070300c002c009000f014410b42c1c00d03042400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 100217356 1250 100216106 100216147
    0x9023d020a0501020307030e100b0a0501050a0c020a030b160905030a0311030712031506050f12060a150e0a080607081906080610031a15060f0706090b09160605 70
    0x40d402040038000100d2028805588900c842e9103010910503006012582429465107048150900d04051424a078035040003440c00c0c0d44081c2040703561403054490540300c00d802100003e510031454440401003040e204034513030207000e902006100f441443c1c030040ea400c046034000c403a01a44041d1001c00800d01c030b1041c0500107641802a0307131800b92952500340310303405c03d4689000400c0c0c9449070070b4050b010007024100181100e140c0030707040408620300b40000348101d0340f078102000f5000c00031441582e10703161990003c0c009090003184201c2211400303800c1e01d1303641140c5803184480d1100010800303400314089209054503a28a80c040e83c81c607441600768200307075040c1c140d060740c0da210100b10304008020181c0500315180c200d811262861800d855203415101c401002030103480c040c410500301d40228503001c2c0804890a50300c603100c0840e0114035016182016001604180e580340506c0000003c642c0241412010386014085490b000c813552841481014001407042022500d2403080c0580a003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 100218606 1250 100217356 100217479
    0x1101032a030506130f0515060a020c090402040b0d0302070608010e060310050c0d06030305091f0c060c1e080415021c1d06070807080a050402010e010e041d010902 71
    0x4444c03c0000c0c4560403119500012290907030ba5005102902c0c0c2c012a8900a0900460b000c615000c0800c3c17000b9161090395210174020020840402c046503240d03048000d00c0039003e4450034001d55a418000d58500d454481c0c140403903048400030454159000c03407d031140001800520f000c0a01c1e03a41e0400611005010700c0c01000b05100e1000300a1a600450000b0341c000d5a0ba1b64580a101c8100b19070034880034840e0080c1401e041d00654000d0b0461441483d140d081540000d086648600a4407400102c0b82c405c1d001d001100c415181e803e8210351101d00070350048141d202104803008684049100ba95840791a0003540d03002e030264a015078004041940d001c00381c40781c03507032096065641b0b092025a8203501203003824041084055004490030b038404442c2e20700b400f07075041580019015031200800141000b000358003949090b00d5a0300702450100400683c00030001184c07803414001e00321100124031914508241000c0c40712608400031248560304485000021002e050000d0b240300210383d503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 100219856 1250 100218606 100218619
    0x1060507150501060c030e03010507080c030403020f0715030e0f1209041b030203090628050a0e0a2402040f26030309010606140a09060f110a1101032a030506 69
    0x10741d01032024081d4a0013410261601e90a8030500d00c1c0180000c840b403000f0b14026850607082000040c0c1c001600b0390860300d424919a682c0c1c5450030224100030f082500412584565540020b240c00c000018480008007640c0411000200a9a1030345456942041a00c0c0354000d03051071110300600801080100401040051404101518941c050a600640d50042980401040550501800034650004544400710503482c01d110100006903d03800300301200750340c0c0341d001986021081c1c4c0201d0012109404641c01d040440c94458410340e801c42c0030f12030303400318a005050309540700c0c0251070503120150641c013001802c0c05c400828095828000c1e84801d440320281904c849424001940103510020001c00c4031800e00c0d4015141c81441c2c0caa20001500070400403425039030010070141920110310300b00e240514190411500c0394846110300440340120081a000c1142408144071442400e8030280701c1900c12201001a10b0b003010181e411076403507900d00c00d0005210313504c919403081c8000e00c40e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 100221106 1250 100219856 100219883
    0x91b03010f09051b0d0b01150903050f070602070f060e040b040204030c0905010503070608090d0c03110d02062205030a08061302040803070203071e050906060c010e0715031401060507 80
    0x4140988100100039038258000d9000c04a13139900070030650315400d0059030113040fa0103655448014180301441000b10b800b40250502050340d03c41c0c1d0180008507000341c21030300303546035130201541c0301c0c40c1c248207003809807151400005039481c03038202440454a00d626020f513218184001d100c0503100c60f00100d0350181d802c01c0701000040c120301a20b009480c65207000a6198140014180340c07032100d821003821b011616003085101e40000030340101404a500c4c001011140034a02903514004405007080c2900078a050b200754030741c2c00100e4030302c9181c0080b040c1207021004851010000d4030300340040d0460f0803c110386403d2900881c1d16070f03000f1030003900c1d9094804085010400701e07017050304101c849400000312441949001c00400700907090070184105441d400b45009201288240f0406005060355000203455564010688210003185c800034484801000e5a05840388541d014400301c40110f214940341d80ca10a02c41c03000500e080c42e840318556400c02d8400c1c0c91030741000350700f16a400940d000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 100222356 1250 100221106 100221131
    0x90c200a1e1407090f0203100611010e0303010b0703032007020d1a010906091505090117010e01021317060106051803010f060303051e130b160606031110020105091b0301 74
    0x14880c0601407000c001e03049035030508130844152104160003001d014014000d01059501d4040e140d4125100c41c2420f0444c41010981980036214480c0035111600011000050410f800c0c401802d480303200b03950802902881c0c120019403602c3c11014421158014401c600060821038170100380d103070155038003800100d991501685204802d80082003403648500b13040260040318014110140010040e0701d0f61030b0305090200701a440c051056400b003000154550031461000c2d445003d408003440c00075541c1e0301400700700040d00b141b144924140c402001e24142030f404030100b601e9040c1c0382d00303a0703699242500c48898200c0d02c6205405465040d5179400030710444914900c940801140f180c0c44450321090541001401d0050400d10680044800c005801b213460b4002118800d890b404d16116890710081824130103c4cc4034904000c1a23145014408818030402061070351200368200c1d0018003450140700200d09840d0241ca25200c182e201fa243c41522401794680304813440350203000060716040891 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 100223606 1250 100222356 100222373
    0xc0b210103051e0619020f131e0501020f0604030c06060b0309060a05100b0702040903030605060c06040501050115020303060904081608030f0109090807080d0609020301090c200a1e 79
    0x280308650070380c0000280a145003c110901e982c201c514009007001e45410000d19000000c1c4205044403254001500d000030740c038400541e01d84405080362a41c4640e141d9080788480e40325810780d40030400804500049941c800202c048040d07400e58044e0246407540d50741501c1000c10044100c1f0625150140447c0644010001c1c0d84100180b100800e1582081a4103408a070f0028001c0c0b0b540301440c0000380f0100d4410740464410b5641030b00c0c002800ca00500b0120020403e5400081e40601c0004442c0160a40014018001c50050700200180d90360350741c41940400c1c96010280150b0001c3c000a20b00785071020040c0d1340a801400c1251500a000941c500c1065031000c08903035411000c070074001010812041d0341d002d03101285003000940e200740c03902000f80c090504001d0659400284408000e52203400c038100405a401e410340d22940c5079010680940b003d820040c001a0681600611406419011203220048540608003180e8151942046064003030180c0380034814000031301c400115140f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 100224856 1250 100223606 100223609
    0x12091f021b0102070b09090910060b04060201060f1802090135010e0405030f0c03160b090c0a0b0301090b0d051c0f03060812090f0a09050612010204030c0b2101 70
    0x10390103000e10a07088010701400c940c4411205046501130881440310682c440129206064201c0b01c0803aa5552000454500346d0320600c100c130058140171000418004000141003682d08540007030080c652950300308517010046102c0c085c404d110242c2060020300d860b80c018011001c044c90a81400301c4002c0c3c204001c0ca024112a406220b40580342441c8030910b020031501504070700408085500f41034540503503c0c0906c0001400c21080080c1d4505402c400f001140c20f1704404107094001c4100c682000742d20b007441243d046000b0702400c0d45c4c030103c03840c002c03042005442c10002c0f0142940d0a20480c03600820000f024a5000340400703c121020400c1005003c0e007070102d106428410280d041d00082c41c0200c2642c0311420b0500f0a5000d0103420404125100890a42c03e2141d07107a0400d940040c800d5030380a449140c10080010010503906c019800c858030800050f40d1125a00c080d000341343e130803072140340301c042e01201e580ca04c01e202d42c01a00700240400b004900400d0244581d0740315400501301c0c203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 100226106 1250 100224856 100224919
    0x90216020d0809030726010204050d03270f090b01020105130303020a0509130501050418120c03090b071109130f08090607021207030b101202131d01090204110403051209 74
    0x101e02001c980b80c1042c1c0380340702a07801028001c8d07090602d002d011031010018220300605000c4000729107d81c0402044403001c820070304080340c1d00c1a03a034900c244041c1e82018002c80e4540303820040c0c004299401409110b00030703136940070344004410b09601e040b4001d400c104840c0d13007044010000e44000b665294090b02d01413104590000b825407525042000b124100517080f00804507a11100d4040742c034002d0240050741d0079081c0419134141524080301c8103031113500002503080f004149a011b02105010444840c0019110809503445504404051501400004004242c038032650380002c0c42c15005405004005000c4030f08084003a40020008400c0090304c0c0542d0303112200c104103020076842e0f0303d5002860f10510300e80c06400d2202c0ca20160401d0390003c0d0250b6031094a00103000d01a1b80700c0007901c00014103812100c1580400f89000e4138071000264492070400035030102401c145021038044951250092151504500c000d010f1034009505540c1e00040042042080902983d0120b00781e41c1d6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 100227356 1250 100226106 100226129
    0xa180f230c040e06060a030b0c0909070206060a0f180e0c060705060709090603170a0e0909010914060f1b0903030a0818060402010504090902030a05011b0207090216020d08090307 78
    0x1c514041c801101e112608140710b580c0800140865a110041010141c1e81c028100d820f8940c0c440139503581d03d2180000854000b01c02800700030700540e0101c1c1242c0124401c0300e034513203e156142c0341c00400340b030349010b2040c81884040a00101c1c510341d03400003040000c1c081c16502c1e04940380d400640c507500304250558440e084801040002584048000c000e0150f4604c20000c66055842c1e46009003118101c80072020400510005602e001e04034015280c140200004002d14040c510705000c0d118104040742d21410340300b221100e01e0340124900388a40c002142c01c8000d95103d0142849908101d03035803800701002041004142c3e00c0c144002d0055840c1d0f500d414000c0e080c4031301044034203204040101e50700d0300501c05100050303a10208a03800c0721101100031454000900000781000903e0400400781e600e01394900150380e00d00b003541c1000e071142d80c007951402991034102d2010f03440b460826028051203c0c0f030001c0140740041500c0b20341030081700004d091000040200b440c11000d508007886244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 100228606 1250 100227356 100227373
    0x1060f0e040309061128140106061205090c1c08190f0f0c08131806060f020d0804150207081b010c05040806010902160f0303020d050a180f23 62
    0x15003003c0508000d10f11803070624612a8503080c001c0d1550b0036040c203480e003c0c0c03000d18070701109607040c41d8260416800040e025030300c0040c064401d0007420b182c810907011550b003082c011203014992156901ca01d05007009062400a600f00304000180384070000d0707098403d03260002c0003048241026109411954400b04034160031f11030040c04480c082e45d9503008201540c80317403e40d0664014580007080703610852454a8440341b80c452414401da5800c1600c01c20f0602c420110300f58169048041140e0540d11542105140709a080761a05010080b10b03001c00c07504804a00000c080042013400010b03040740040c20b0256696459146603c45422445402070344854203000354000e1040c0c1c49071140d1814054549840c0c44c900c039460b84d20510659540307541c04200350503005691100000c0455101210b00388841c807520340038000350007209c0c034012168509400590710140074807c2c80c50282082c49400c1c40b4004907900e40c00210b0b5080000c0351802c64500b9251380c11840180004c2c00100c403a800f41404c41c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 100229856 1250 100228606 100228613
    0x106020c0a03210302040504110d0c1103070b1506040303020c0307051e0609040f09030512130305040512010b031b0405090312040f03021203070309050114040b060d02010201060f0e04 80
    0xc040e40318500e00c15121807a00700000b801d0b66a034840c0e1001c0c084100541d100d0000c80540c000c0c0226800960010300f0448003400007074008005100381c4106c030303108002d5903035100d0044031030000020303924000e03034010040100417907141a03072164002c141250041038800d15401082c0e041e04280d00032009079120100105241c40d00344018805040241c80440c0a060640c0d10702a00890513201c3e203005020007e001d50b40c640b034542100e0400c500e0703003900b84650142844c00811b07a911000d035a000d0039400e44003040003241003800da03114868240e03407a2403d0500740300c100b080c1c41005039aa071500e90360341c1101d2a65a1401d0100d8251402c14010701c14915040340c003400240c4000801010854104000001520b000030540a030010f412a1a01420703040600d8140d1405d0303540200b00301560b10100400c001560b042c0c00c94024030303100308020b0000503004810594141025a00103000d00b4500d40001c20f076041481c05604c140b0700503c00400c440340e40d107044140400c195048402106000c1c0100300c20f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 100231106 1250 100229856 100229863
    0x90a0207020415090c0e031b0117150109090c020319050d0c0e100903120503070504080303090c0f060703080a020d06030b0108032221080c030307020a12020106030b01030209100b070b010602 83
    0x100051800d00c2024541c6c001e0029403184000030407611410010313003e040d403d074864801401c08000c85e0307501c4205801c050180102c014114201e2320b00080d903540c00440d0181880c06520b6400341c10360011070901880c0c519490704103415a1250b81002401d03c00540d1303c0a13031b0301500841800341c4c0c42d504186c540340018003480d024071000050600c2805101080051100021408102924a4520f8494480c440100d0750b0b44a43c5d8401445440040140083e42001060301030a0240c1100c590703c0c442c44141c280540380c062584040d000c5141c000000704159044d030018011071030f2248000030f1503902c958449455034803c2c1c01100c5507a01c007084641c1111803c00348a03003031541444201501515104c1c40380d00385e41d6042505220750f6800340020040002840958004c40f80c2d24003583d48038540b02c2002581c1d5001c0f01426076030700f81404864613106006201d008103403030300014000c4040e803d580030b00083c460041c00c500480c899049000441c1400340d805440d07600c0c408c0300520169407418500030318 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 100232356 1250 100231106 100231121
    0x12030813051c090f0b160501020c030403050c010906141b0f070605030609060a0e040816021c020405010603020906040306020c0a0803040309031103071401030e010b060a09092702090a020702041509 86
    0x8140f008580030300944c00c85c00f06803982c1d020400d402c1c4001d00e426203020b9019004000c07048050344170220b804000c010022030403c000c4802a07a03807011503907a40c00112505011048051172224042004050354140224a00c0c1384491040c112003242c20303144841881d041855002d200001d0002c002d003d46c524201c2125a04020100d4208500508124842880182c0078000402c400c00020303c1035040e200c0e114411680b40d400401c24005250030000c030440c3d00007010404c0348224603210010400d98020700c20746032003c0010340b02d00d06150465036140029801214a50494450320104000080c0c040d001140310703d219a681c400b030300b4a1840e12a0310180c150843e18441e80100a06109041111401e0510300009107004502c100d01391541078014107d1703012264001c1f03030002c0d00c81a000e07040140d55045030741103407041181100e00003051407000c4c0b1180d0764000d110b80c11174404002d49015001d080d0400380b0b800307005160100d10340c0081e003110700c0070681c0207a004018804003c0d01c40389101e480d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 100233606 1250 100232356 100232369
    0x60310062d0f0309080a03050106080a0510050f0a0305070b190311070602090d02030601030b150906030706110f0303010303030f0507020a02130c020708101a060412030813051c09 78
    0xc07151050304049503503950021040308014490181c020348074482c0d00040720094014051959504100384d00070060306003405103401141400c40480ca04006c544207044c4540a85052424000e0030b000800c858007020344036596000003881c4000c40420410b021900082107490f41440d550583d41111018400038006048141407070a201c91a82540c40001c440800740d001500503a01c1c12044d0024200748158103002c1e4141c07140341d0000c01080511800c250040c0365000c0ca50924512140410040e8039045882d0ba805401800c801c000003405000c8050a0703a02c500300b0f40c2d25100326040c820749582c00980c010350009407640301d820480b005074401c0c41d0300101d451003d004900344580110301e0200840250b855056641c3d248450384038400d01c00140a000c809017076813082d400e61102e4002400d4195074000b001d8048600c0c00380389242c044100c804503442d601c100381901406490660b00c45900402c20385d05c4401010b40790001440c1032090352260158800c503407100c003400c814018500196a04241c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 100234856 1250 100233606 100233647
    0x60509100b04141206040303150803040501091205010b0d080717030705071b0510030b0f0306060916180e0a06090c02150a02130f170c0604050f010e06031006 69
    0x7800441c0c0110100d80039240d440540c00c1002e0740000c00301d51407251000741e00000d8020802884100751b890340000101d603078800749180006454449141d207902c180d20606003c5011502d08104a2003002021228035004000020700501440041000101c00042c204c4503d88009552010420074181c4039040c501140c62050442c46c02900180c034910030307a8006020400100320009403507043c003084501400d8003a000b102803500e107040c09009031000288a500c10f80298804000f1410005426480351000404014903911801d205400e4500c02e070502004104000c3c0c5c40300040c0c0202c007109002040555003401079450310710207510842c1d030990170907032813182420100308141741e002510314411700519110440070303220050132038000d11074074100e1075460b4488400040e801a49001d140100c4c1e054500b03414840c2c0d4011001c1e9101c1804c1c51040f42e00600a0009115500b01403040c0c15803294181003000864004a0004146800449681000061090b001e00145911a110810121954408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 100236106 1250 100234856 100234859
    0x5120a0e0f0a170313080d0e100b1e010e1302070807030f180f06052104050304030b090105040305070f1a04140705010203090901090203101205010903081311010806180a06050910 78
    0x140c3e1010300840d0300180c0000004036640d203005000d030340507038501d0540300300300d642d03220f16100404041d0ac40038030080c0c41491440007007581403007941e20f1096841c00507911036061540c40d90402a0307803400d01902000032070342032100d00c0c0041d0385030300101034141c0240c58499400c170039880300500f0f07a0005031054013002c401000400c036403080c20a455080e2140c5082003902d030300613030310b20a841010344c0a410005d407000000b4007042c801c000c002041621b0155011012a1b035400d003a060a89409480003400280b0130003440f4041520744000402c0b06e031040e65608001e807185640d03044041401d42f0281c0350200e520002c200c5192081280000401080c00918240f01c007450000303203991414400c0d01c2c0800e80010020f2038050109c0740450207401030100101c09080c641c24001e00a2440d02c0045000c60f030030070046040e440b031100c507045500d64092015040805044011590b03921b000d8007040d00f00643c000d840b10040490314009110b00302014002801074178003405c001d00c40700d025000840c0360824a50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 100237356 1250 100236106 100236121
    0xe040807060b030d140a12050c070c061b110d02060a030f0b03120d090201030603140d030501050922020f0a0e0a0b0f0904030f020705061206100302040605120a0e0f0a1703 75
    0x22000441521402c0d03a4451503451170a4600081b550413201e10289888c040000f174030f041d007014050007401a00040000c0391030b23081c180c3c0d255100c0c2c0c040280341c01d001500100011541d1150301c1103200003410b4231000300c083d1790225440350013040c0510003281e121003010520102c0307441091220b6400b14010000c00040c1c1105196a00c00c03039220f90043c070b4692403080156400380d08030400a65100b8031301c100000040682c01d841302c030040384090000323060000008441c07500d4844d441c0103000c4441c041c002c002d403802883d5050034011408030f802c92850407408215943d5281010020300e0b0214040c52180b030001058002c40d659000b0043c030410001d10110301036140c00c000f25902603418184034164200140c400d900c1e0540300d90140d64847c0f4005241c510307145441800901514081d904010340392200c0c0d00030740590044e8001e820001c0c00074414004000d020390390a0350027002002e40020141451b590040c207080080c1030200d10343d400350348500c0c02c01c0300c03890108071000070f40050b60b41141800320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 100238606 1250 100237356 100237367
    0x3150907030b01080604050d080606040909080415050309070603050f070c060e16050901120807260d0209010305070c03050d0f11070b1e090606060d0f1a030d080103050c0108070203040e040807060b030d 88
    0x920030103a965612153b04105600301100c01420018150001d06001c40c400140369070310490b40e01609006842000400601a00809000301003400c07605000d0380e69441b0480701c86002d440c3c1590301c9503d440301400034000c2070041c0001b84001c0070018484500300020f000012034185c0c4498440c0c00301c564060041380e500009c0d00c1e01590b100c5500c00c40010082d400e1a51090305a1000000800024505504000e00d0b07000304803e030b10070307203050090b81e80301c0c1c60a42e01c0314541d850242c00f0940810108441c01c4850b440340701c41c0d0034010000039030b514409000041c160843c2100b201c3c5540c01100344100c5217024444690710354030305003001c980361a0525626032a001c0c040c104600403e0701080741c5181011940207101c405160345002c101c00c04000044d030860b0000c00482c0c5000f80207070491000028440c81c1c41605a940000c0280403902030075004440044000b884003085010600c00451000140c2140c94001d50003500345a0300c40c1801d0a04104440c0300d008014441d600c15842c4203003064011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 100239856 1250 100238606 100238609
    0x81608060307140a0b030c07020a1d0a0c020a050304080105010e060904030c0807080f120a110703050301030b0721020408011a220b0d0503040e06010201020903150907030b01080604050d08060604 85
    0x103c1d8400b0a01d81440c000c42e0340705501c4d4019802d880740100400a0540000000c1c08115008803005240e0b02e0352031003101d0440c00c480500d94844600c1c000003c03c0f0300402d0f003110003000c0c0a44103d40d0751200c50b0b1101400c54025800200c40c83c0d4460f4010860300750300804083c1c010704200d48440c0c5c1d80c10f15030340c060003501c41c01c8030080c00c515011504500307010f416800d48081014094040da40c400701a00107100160086540c8040c2910b4075807190031002511007603611183d8151511441c1d0703421502c80341011a00141044200480c50080c42004646080101e500d0f00100d03001585441c00c15103a142980c90158000b034406e46204d5010f03100380c1d00c040302110340551219100100a0030200c480c0c0c05400c865241c0c64000c8440d0940c43c003003110020060045801c84083c000700c80c1c0322040124240e109501e407103607140d40440840641e2403005074402da00155903004450b00c183d030701d54880c180c21a090340300d0b6803180c100e402044140030041c0481a00440c4a2130702c20744914000780002d940c1c1c0034a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 100241106 1250 100239856 100239869
    0x21006090509212701031103070c020409022e0305010b090604091d0102130513060f0b0307030e010c0e101707032301080604020a0b0f07021201021603081608060307 72
    0xf403039103030342032071840204588a5560140700f0030100030300c144181240b00d18890f42a4002890020a54904035440080e64020300300c0c1c1e9500d0a11740101c1d02004040d082d080400c0e070340900748034892030583e507000441c40611808004041d050105600010f022200b0585c0046005030041100c0b030b210707603505005c480695000b0707035000800f00000ca039802c0386024944403041c0250f100044960340140c1080030700c3c0488804640b4100d034201c0c3c0003011020380e8443c0c41020b442b101d15036030034032211141e80043c5501040314540041d03605130046683d070956034449454400306140d0b2802d8441801c00c031400e0015404ea03421301d05003a0b00502c09051880c7c40041014042640d203417a00440704c0540d107264078200138030303450444155840d04082511410309580c1288665495030000a004042c0740949840200010025040c01595000e010403845c031410801d2a95500301b000c106030b80201c03034400403100c1c000e6860381041d2610201070100045038019440038810707804100195607070b0014607242035503203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 100242356 1250 100241106 100241143
    0x906070312090b04061b03060302030a0303090f06090b01050406050d210219050f06010609030c030201050304030e0918281b0e0c0306130e0309010c050f01020703021006090509 77
    0x405080900901c041440203002843d554288420f0007041e800c0305151141c242c0d19000d4860886006030704417545440025055001002e002020902a0340085510790043d20b01240ca0b070380e0790b603a407401c44440000481d2000803444c0140014181446140060074055035076480c0c1c11026120030000941c0760640d1014a01c001e03c200305036910038000704d441048000c482c09042c9001b0300e0100d03154480005c04811511139400001816481900c040c0c0449811a54140f01242142c00440307450b40001c00903402e0180710400b00c030b1140c030741d080d45d01e1140484072480000900890300060038000c0320f403116803800c07000c000d40322542c1e2204286a0300e02303a403001c034041200291a02070a030a041c5039110b180800f000204020b4103050b000010f511594040b1109010b48081c0040042159920401044554401d006018195010341541e4001c03501641c200ea10800380362002c00d003641c3c003a00b030442c01a00304616003407010a080c0952005404400c3c818059480c5c2a44925550580040140007548 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 100243606 1250 100242356 100242377
    0x12031a0d06090305040503030a030b19030c09020c03040f0b030702070e10050108130203071e08011b050a030605040608010603290610050403020a0617090d050412020a050405100f0b09060703 83
    0x5025400305c5000b4070016042ea500d030035103840082e006050000d00e0a0182d145c1d0300c02080310800840c144401d81c0d5000c5071020001c0d0900208000079001980440403510040101241d0740c0241c0140500402c42000030340e989141080000341030074400e078400e9140d008807000b880342003100e00c5001d205a0b142882c0c0744000d41d031244a02d010040b1915406905800740d2036012600c518100c1400d074403081941044c01d500c0e603644000d42e01301e580c0c480c500440d00161003015141e483c817440003407900c40100c1c540031440945542c0004c1c1111042d900c8081103a544800810070454401a10102e02181d8078101c581c0703800440300c003696100002e100340d2180c0500459440c1c040e0241090710042c2da0058201c0d00070b40d0b103845001d0807410b00c6103840f003855031400001800782000040d0006020b0040d6507940e04052070000b1103a1038460740e8900302e17400a207aa001160365100d0340b241034418901c140d600102c80e0315111303120104500c00c1d004400501c0d0108500780382c0d034541c9012074a9840c2c0c035242911050303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 100244856 1250 100243606 100243613
    0x2a05070302070e0f0906090c060304110d021306050f0406050a050103090c0338061008090f19021203040b0405150d0903020d0306060f02060c0a090e0412031a0d0609 72
    0xd03402e5000400500840001d1081d4030100161041c0b00310300c4c0c02c08136403480d2034108505076940001d0001c2588058100f0025002542e8000c2843d51980d01400d01c56100c2d42d80c2e400511180001000f0b076002c1340d0b039100c00700b100b441d2412000c012488242c500700011400d00000c40c0c2111014007c0c41d0505480e0704040007002142e000342e0f4000c50b00b10032003d58410351486004220f00703a4504003000d582c0f41d46e43c44c002617980e25070381030702402004007000c880c000b00c44c8054946131401880b560301405941d0b00c181944409103c0101e03c01440342d59140d01c01454410032214a1803429004520740c801c2c04240845041f842c21142940c200b111702007101010484407481900c50301c80309400150505c2f442004040d000141070503207a42945080c043c554550034216800054080e0944c01a4000004540100307140b00050201496a140058180d07880f40c00140202c40306803012030320b010050700c1c420000d5a02d031003002610300c424060385046a00407800240038011a12024020783e540300701c481e040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 100246106 1250 100244856 100244863
    0x70c0302061b07080a0903020907030b0603070305270c0909010e030301090b040b0a06120f0b01021002030603030403240609020f1b010f05130b010b030105060f160203070e0a2a05070302 81
    0x40c031342c1c080203031070752850400d100500b00034403031008a000f060440c02041e850b0b4007038040d10206036030290429096503680f8030200d01420001d0202c101c048030464000c110f1035405410f000e070380358820000340f002c800c0308000d020f4400c03001442c0c140e40340d06d80500544208004000c480c11100728240119460342c1c00d000040003000c506a6107075120502a00001b4440c0d00404126034010700244100b25583c903842d002c0c8161b56892000600503000401407640580056025580000b8050102c1e4203044d00c3e581c40c180d8080f048040d00d01c0009609052110360207050041e00043d041484041d410440d0070420030109004144c609036940c0400e031510303030f24107400f54440c0f00d0035800c40f07030140f005051105920b8030780c81000d00709464614400c000400c8030200300701128100d03140a044a49020300c0007600d840203410036034a48000d03484400c01c900140e9410890f00c0090203000120190070b06103a1a84030445841400c4280c40040042c21240c1e03564003000503501c0a1041d0a045940305058a0202d04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 100247356 1250 100246106 100246117
    0xe030a1103040b0d050105030d020d050a1b081602100509010c02060d02130e060411180103051e040317130c03080a020c0402040803180a030b1b19020d08070c0302061b 73
    0x215a2010880791303210314054102e00d04036182502551280001860126105c500c04408040410030070801419964030541c400b01000004d0183d5400d0041c80b17945810281d4044261070141a000400a005501c0d06e240c800c07a071440c01c0d08010303241c0b164400c00a0700c102c0b44440080e01c6800080740030101e08919804031200d880800010790303800d80e165040e80302088015a5101d010368a011000041c00070030303004543e400201424041d1030340d03102c170004402070b01d401003041e502d20850380300003031310000603103141405203120b500c5642c0c1100c1405084000c10a0041c45440c041031083da010300490074413140c034030a81c0d4102c50459a21055648140d14012058507415041840080c0c0011283c101201030f00c40d10400c4400b8943c0c280540042024200c0b60340005400e01c80d00101203150154803d48400e50701104401040c101b83e05a01d1058407260008040c0c4050b82208a18642c1305500c0741d40c3e154051518102410701c0c03a0117032402980c4030130042800c0303661a2080302d9811442c42e80001d841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 100248606 1250 100247356 100247369
    0xb0c040807180e0d0206090d0f0e04020d06050904080403030e0604060503060f04020412150c0206091b22021903020c1504050111070c030501060801051311011202180f040e030a110304 80
    0x86280c5804100255100b00840320907e0324000e14038498102c80c45481081411030b020b50720300080c0b0f850302013008000e601208241c40840c1d911200020292103042e05984100c0c061070780c454a491660a02174145992158901c0c8074245c104414402c05401c1001e50b600300c0400d03590440b08101d10070201d0000c2c450b0b9042400e43c1e40603490a4001c000300a100305c182240c0e0300c1010301044d0541901641e6600043e141300786590041c500050308600d140300700384012040101010b0300c803c50082c1d45116165080c108180b6035400207460307444454201c1079410b1911a515003189000c400b1074101d0f8403220341c118600307400c000f81300c0410180310003500310844001152120035540c0403580340c4003c0d6124584400c44195092103030006001006208062086e921039085116042d583d54079210700410b0005928140700d004844035030004414806002080c000302000161000b19004000c096492503000502c02c4c0d042009441818070302106544000246083c0410424200000c060442c021a049103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 100249856 1250 100248606 100248613
    0x4030c0b01080703021504030209010506070507090f0e0f0d0503071b0c08010b0a080a030c150f06060504050f04060b0702040b010c050a05010609110909010303050901180b070b0c040807180e 83
    0x4a00c2c8000481d03c0f00843c0d00c200d41507038101da1040342a451304d004a1001139841403520004001c00e08103a00103041c07052140043d180c00700d440c0c98004045078149001a0103180e521061020070010400901100380001c074020010301403090710040c10b07407200410410412920758a841300f40c8210308240640a40d11000f804a46a25800d101e0300030642e148100c0e210701c7da540340002e14004007159119100350140e03150842c4861980301c0040e40143c00c000c0080c01903564602c00b80040182c401c0b00701814880e5aa00e0340c440c549400c100601041c040d44610031841d2410402c8181d14410032034980690513100880d0310001d080050302c1d50804214040d0160141c0c8011004000043d40000281d03494050104000c0c1d40d481c64038116809460300d196000082d02c801070021074007400180440320790500d00032038442d00c46001c0b140c00410950240c8280350000c22550f003040214001151300c00503980b03026041074a13207009c0c1c41d51000103210322501e0450160b561460900c00f5004503140400c19402c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 100251106 1250 100249856 100249859
    0xc050f0f04020d0f050124030209010e0306090604030908150604111e090306010e011223071d0702030c0709052a0c01050c0f04061d15030109050c1603030504030c0b01 73
    0xa90004d05003266007156200d18010012803158480c41001d00e880c000c0d000400304122525006074025841682c01ca81481903040b4807143c2a0b41c20002c184c45907180d00c0c05041d19007082e00c2c2c0035000784201d80120416401c102901a50781c0140b60348141d100b54202c5011800045605001c100c502c2400100e007002d000c01d14296a508000d14010080288143c003280e007540e0765400b00c208010310a00800702e460b5004c554074004101c0030004100d0000002030081240e000c4201018545180c40e8040c8180007250303190400c05c100b00521455000406001441ca0040c45051094071081d490040e0f060b11645c607400f003200800d0b4003020200c1c0309a8603803848640c01c1107001c20342440d0000031003603d15600f020001641421924203840307000301101e1065003041c2c100042a0703280303091443d10311501c07410303210404000d68960507400ea09400c0c10b106996a54102101d220a4a1008042501c080401c00424103c0344050b1582e0075a15014900010076448515084032582c40c203810252029289500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 100252356 1250 100251106 100251127
    0x30b030c0f0a0e071827152103120c08060d0305040503010207030e040e0a11040207051002070c06090b030405070b090f12060108011401080703030e01050f0706091e0c050f0f0402 78
    0x160901c190410303801e00200350f55035200f01d66141b050b0610300030044034014000d01d0821110341001c0c0a04d4180b0112040c620345511980c011050400760150307186c54042c541d0800d0503000a00030b403500340e0042051101c1b1f900c2950141680c44060103076400346070400c80310740c2810310a0f01034401402c00180203550301d2059080c02032030614140c105910851502c11b091000c110f0000313480702d0003a07001c05400314030348900007004002d4000040960f407a0051444c40807c50141d4802082040e1141a801c00303114109640102990b509411040b2400c8042040c000030800001d01c0b1030803500e141500d240c1d1454070f0008076034903003111507030107800c880c1850a0381032898003c070340c40e416604508000c1240501080c002140f20500f849010b4042d04003840c148086849000102c04684040c10030078504410103501f0005036010850542d10103540348040e034208003055100c0c444007200d000d10b14030305070740a850b01c0d15003111600c6154070032040600d804003952640600c89000c102e00420854860034505c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 100253606 1250 100252356 100252367
    0x11070206040e06060c0f0a2102280f0b01090507022a2205010e070302040303091719060b01020d0807080708060f030a0b0901360303060509010603020d0c030b030c0f0a0e07 75
    0xc408846012100c542150300c010104002c8e02a45915802403144801d40b00f440888044000155800c03007001118040c04a01e403550760403a11449503040040c43d61600b00060300f220000f03002101150031038100d00700020403140350305a1191010b490b1610350600c02000078403110410142d007082e8004e090000c0d20406003648050304803800001800382c56a18803008808900c101d010003008a182c03410140320303160100040480d141241002c403030440c1118074540749010010b0700100d95081e01c5107070368081540c0c103015802004c3c09a0400251604004c1e0020780000801407101c03082001440004020340e0340c154004141850150603110320092605110f00359080c00c4440c1d514039030038038030502e1151025415402c40202d2074610b0b03541520502400e01d4100784100025001c041d103500c0d01144550304d06002c14004c0110f502c005030b90758001030300c800681d0f86100c03140c41458544441541c094601240420194204940c00010702507460001500034902d40c01109104004804100c11a50440d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 100254856 1250 100253606 100253623
    0x406032c0307020f031c050c0f010504080c1203010f09020903070e0a060305071401081f0801020a0309120306080d0e01051c06030c080a050c0d140a08090411070206040e06060c0f 78
    0x80c0c075445000da0441e400d041d07546c1c2650b200201e003402e031000041e00462140e406013000d40058030a44030b07140002078840b400d60b05c0507541510806070010741f00f031aa000070000048005444ca1826003150b00d03006a10400240c5481001d000c0c0b5000582c83c5020395041c8000005072000c1010260241084501c40000748030500040382c162003401c00c00b18640c030310141c412400800c14ce580c100c1c80e640d100d6203500d0010b014541200c0c034075101ca20114001c0800c1c000341124402d1070742e00040d410f50f1030401c1c8014134901c00d195000e05160031814819850041031411400400c0d041011600d503070400100c0303461042c02140306030304201c0c200002c5082c0c8107400004c200ca004403882d840a03912049115110321032088005c00c1548a4505102c031401c01d280c40300c130035034010f80c0391405001d0020b54041c284050014100d540d607000160342da40c0e42c9020312920611200f4100c01070f0034001180d010a040340320f10300840940c4045000000c140daaa2101200d40014a070070544e0041e0b1110300c2082d5681404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 100256106 1250 100254856 100254859
    0x308060a060c0b1f080a12031109031c050409060b03060f01050c0316080c060f07020f0f0c0f0f120a0b07031a0f040e070f08070602010504080406032c030702 69
    0x6403500041d9184280300ba45285070300181c2184054407040440d00c4415824801d03162450b042c80c1300007914100074043c04089a004d400041d55411001c0f800400300c41a1645c01601c0c0321080c489280305403030000c0c00203a21649005080c0b500546201c0545107400399500c8030b0400350801e80049261504040514007480c02602d50b0700c850005080155018010000e90b21119442030145540c0310048250003541180249081d81c540f81c0941565800c0141c100d50b0342e07021100307072400e00c10415030421051203034160210207011103401003c0d00c41e8868403c0c00d0700510814440d00d1841c450faa0300510070306010801800500080010904103445d500320709001e9070059640c0002601c0c00d402401002e0302054800c056202000503030013005107072051074040d140c0080c1d540344004c09100c0100400005030468403004c04015180c50550742c41c007061500325900f10390401c0d040c000010605000e80d130a0719164140880d90320701503442c50328054040301e101d000c040825010100c00480100090400900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 100257356 1250 100256106 100256119
    0x8060a0905100c02010e01140c03041b0312030207020901050603010b0a03020310050a0305060708060a0f1205011b1d0303040b03070f02010f06090914012a030f05040b010f060e060702010e011b030806 87
    0x10440c6c0e0704d4000c8c00c0101d0b100400000100b00040004441d8032a000c0f070040394007a0b1682040c1c582d11201404000b103041c58011a50018008040d80b400c3d07080c142c010841100c1141c17656040c400100b8181c0503034944140bd00da00030001c901003e40c0400641d0107000c0281081642540e80e0a0281d51031781e06640e1040869171040110748113052a148034410f45190394803a0308001d140c00d0b01c0d10402c0c400d2a00540300c1d5540e4090036118465601c1c203800034822141d41e181e581c1060805c88040c11507156245c5031080c2d000700030402403080c1040a807503021090382080d03040042c00d110300740d01400385e04514210740b51500b200444c1410855003d2083d082c01800740100c3c0d06810f41c80f560880f2403035908000e45c81c0d5800c041d80c1024551009842c01c045c420304c2e010654a107060800d4040d141e050350210750003855180140300c1c0d01500202e0301c0040403185012511482c180020810301e11075100083e0401000c1000806180d0048401541020000002c0b107072100301401c0c014032105003600d90a00c54035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 100258606 1250 100257356 100257371
    0x210050703120513110303120a0c0f02030711091b040b040e070f02061b2101051002061302190e150102011109130509010e0303012d08060a0905100c02010e01 69
    0x4459128161080003a030304913882c40210350315000100104880007541c54070041086880c81c0c601100d545004520354840802e5032002e91a0203814502c050304120110b40c4140000000b0424005d01005421402d40f4401c0302a107a11850703496a0582901c00d50036040002000240900710380000d100b150312042d50417843d41c54444085513040c561160050050740104d01142c140c1010501c150700508900890724580000313030710342c0c49540d00d150071000396403140000100700c90304081190540c040f0452001e05003e00e0000c9134084907a070100c20290140054034030310008007803010029800303010034980301c0c01c0c0d51a1005192110800317400c0c001c2d00550901c0d002047c41c1003410103449a14100070490418000b031000140010900202451200d41d00c0f418020501c0606100440c0a09000b150041e401039040b401405281040c80004019080380720f010400007401140b02e41e00207541a10100c0c03c02c4080c101145801c0440b428481800e10f440e0300c028106070154008030b00350403494000d11400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 100259856 1250 100258606 100258637
    0x5060307140f0c0d0e1008060307120303020d151d090a0c09150b180621040b071b0305030606030a0609060b040f080705030a080c01060801020304060603060b030f120a09030210050703 80
    0x1a0080d481a46c01c800c403204aa030455000d0014960f00080107411140059914100c3d00380c0c1031003641c003e0307003c29130004404c405e032040360003500c032120b0720341c0b6098403c0e80c5001ca140a1001c51005420702c400f0160300071841c511814010f803005143c110008c202007030348074802d24004160710301c0d4030754608480782c0c00040c186403a070301503034215216000300000c00c110b10000d01441c1d610000003400c0a1510200480c9014165601c49000c0e600941d2020b0440c0f4020502802c8d1421941c40201644c005003840c1c00003e0f8000100d9910100568101da00c03074941c0040c41d009880203400c245040f030b0030701c1c030045030b55250350001d0801c480d09228902841030380c400c00ca80d144d0081d405029059002510001d0100303800701d005061000c0700c5c400014000d55200041422a00b0503101201d16603150b6008009204650040c1001c08c4000c40242800a021150160344c8a80d01a80c900492002107401c022140c017440c1c81c01c0007550044c00c0e0112040354840000d0107a405034400300c003c100c1c13402d95901c06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 100261106 1250 100259856 100259867
    0xf081309050c04090b094501061e0e04030c1103070b18090108060f061305250e09060909070e0f040203190302060103020634020906011805060307140f0c0d 68
    0x1900c1c1c140801c44088010024403047c0301c5080c0d054400110303603141c0811224a0701d05000303640b8213002c00000b5258208150f05940d0f03041a00c1c10712044014250a1094400400003640c00c00d502d41800d450b404d240e0f1a111040c407144c072404a9150140b81e1000440602c036000409001204000c2440221401740c10803603e0b140c00c0c003411903a035028000003176641c1032801049030070800c018040c040c1d00d51544500e506450086441c030550000c000d6992011701500c0140c0b100300c1c0554101018640e4850020400a4a0050210344110120000310394030580070700c07000f0090000103000e625649441455003400d41c1d401e5071700b207000740f140c50340d240c400310b50100c03104800c168554060702c6070707901c1c60702005569000000340510401821500403a81a480c01d242d10147c480e01247c00000380740c90041240004000f44078030b05002ca41c007400050791811088810917560100e40c241d413640c82c1d19004490001480340721480b10503000035920050030f00342d00500040c010b4841150108031a0503402c565 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 100262356 1250 100261106 100261111
    0x10302160609050c03100915050106020303070c03030b0301020d0603020f19030b0705040f081c03050108030714010b0303270f010e010e010e060d0903080a090f081309050c04090b09 79
    0x1180400108a00028020b60011075080340140219a44a98003600080c10038030a04602680555038803810020443c40046415041c4400781041180750b143c000c1c0070b034480c03100404031020001055010010507000e54010300c1d0302100a8000c5441d0982c17542ca181c020415400280d10460042140d4245807920b000c500114800440d07003001c0c3e007451a5038803404404050260014008240404280c0841c0002404000e0100000502004010041c4800c1120b00b405031030080500b400c005000f0b07d0000411a10255844014202c03030000040c411401000c55644881c0c2c58000040c0030110745000fa0a042041045400103501c060000b00401400240071428107000c03d00180043d022076000343c04030341d292032060500e0300641742c040d00000e90981c802e800003a0b506a0703980645050580c803070149030788140481403c120003a8581c0740c04d991440c174000c000f00000e400140d0a490281c41c0c0c06038078020701708182c003030245080100f0921450707002070113601805071401c0307041052854084c00450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 100263606 1250 100262356 100262377
    0x120406081003030c0813030501090b0406140f010b0c030d050702010203060a1706060906040b04110309010609090c032904200d020f0402030709030f0f02040509060c03071d2805010302 80
    0x40c0481c06a901d07000240c0001d0500e207030349141e41b000000455030a00484180724450401500e00303280074a0444100c88103400e45440c8444060104242c0200000511381580c41000c00c0503101c1128210b264514410200c104d0700e0142400203100c80303250150095030260604403517408a20780c9401c41b036400d0204641c4441000e50003040415064102507445603000349002c2c102103090000800400c1c165a8680c200a80381c100000801c019040b0a00c5060003401503001f09004074440c90311066484080303808090144402485a441c2c070290b6200d0713881f1041c08801360301c1c059113483d04015184000d101800c26144000d0191914103145c4030358241207c030745c010310703d541d00141007007404001c0d0030081070a024008144c502202003200c01c1e085810f2544a0010f078a20791400348184000c0d1000581410810760009050180c42c805100599a22108503d003101008010708103500d02001210b03115500f22409a2282d040e070100c0c650344a80b04001401407840f41c1e55154011012445104a081c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 100264856 1250 100263606 100263617
    0xf060c0e030616140405041503030e030705090408030703021b030307030f02030609070c0c05060d061802070b0a05130f050618030f0d020903011d030a030501080c0f0108060d0512040608100303 84
    0x100e1000d801041c02c13120440c031441c4164203040d1100e0104040715411540704040b114444d000f00101940315a051021040c140c01034100fa51602002c02e613042400350000381182c00100004400740c0c03080d41659940103012419040e072070700406a240e12544181c40410000b800d0042c9030074001e1540c02101e00810006c0d0508585070340d0300030704070780b41009043e0440310310403000c0c40000c06980381d03005048269915000001c0f401c2c41c2501c04060b02e400c0c0035400600f24018043c280c0030030070508005c0e600003400b000124072669102c00c2d030b00b8072114225006108020f500408418000002a0280b00715800344c084074109507074a400744d982e8014000144d00300803082064128440c10780d0043c180101000d000030a21011180e80c3c1c101c80c0035260440c0015030300c08280301c22401d502d8080c0328010080c8401501c0b01c1300074000804c026140b50340101d0706011078031010400e65110060066611504042580c000c80032805014905030b0081c4551000110410040354402b10780030205400c40e5812740380c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 100266106 1250 100264856 100264891
    0x62109030c2f09090f030c07051f08180f0d030203070f14090d052a10080402060d05070c1b090c02073f0b061305060f04180f060c0e0306 60
    0x100320b050000101321801d94060f0160424403440300300040c090041034580601821820f1606101b1031821400040f400726000103030206490b0b4008100680040f03035800000b10000c0a18011440c107070ba1400b06500310b114403c1da60211a9040d030140d4020b62555030b03004d11a0506a0048400000d00201000d0068040006499610b0b1020700c508540d84110f090f1000d030158555040811018003c0c074583d104a40714040a481c54114000d40f0b03008042d062807141d03400d0a0b0040b88a501455080843c00c2d0307503400c0031844880c002c41105120360703401103080074070005440440c040382d21107106e04004242402a09041c1c5800480d000003a83d0880c0c0080103007880e141c040c0c00741244004081415103944850500240b403010b0120b52000303014888940d004d04100342400407601003450148041c1d0728120078000f85588a5041c2c0d00039000032a00030540c0840c070364540013002c904880082c25404244001801c100230380d08110b0307403c00380740c03620402604804141603c6650071035244160f100e20300403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 100267356 1250 100266106 100266109
    0x60f090610090f030f1202060705070201050a0504090507030f0f02090102060f060103060803030c0a09060f02031602031f05090c0105121b0904020c0f0706050c07062109030c2f 77
    0x5111000061918207801260f5940907140000c81c000c3d001a5080d204402050050280e20904401c100791244001c140502c0c04420042c41c502803420000d04000340018020780c00c0d07120302d003540c020705480d407802c000703505140c3d01c081d001348001600c0030042c5003040400e0035000380354800c0d194100c0c81a00a440c0540d14880500b61038a402019281810f80d0f4840c0070803404420005503103d820300500080d40c2d580a0400942050740d146e00200c10005c5038148561075650100c140c8a205050f280180e903040003902c00070b0304180b9418030004801410803907403800c0c0002a042103000310000c906881c0700e01c2d14000111228171410078600c60a4080c80041500102c800500d444080070442000c4c0c180519400082c080e030b80f0003880301c0c4940d840358000380c030103035405e10808009000d682015898298003904540e2291aa84101802d00c0718540104000054820b288810340c5410b0340200080380c42841c01400261500320107072168114138086244048202d4000540d4442001c64074005008020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 100268606 1250 100267356 100267369
    0xc06020f0d0c1b260d09030f150c030c080c0703090b0309190c03030e0f0a0b130b0a091d010e0a0209060d1d210d180b0403020c0108060f0906 62
    0x100c1c1201d0710311074002c0e0403e0580a280742c3d880901400f030605014100042c4440d24030b10b02c10034000c4015041a202c0c52281604151210222035001c0d081c0f2105c121507040040c40003081d50400d400c00b40c1042012081c641d8507a00030481c0340c8141d01d4840c4c3ca9200c00d00030710918002e03814004d0200c0d10003903003404040030031405158804800c1c42220755810140f00240000072841d0412070320000d01d0041401095000129200c0c3d865090f10050620306252000403c2403406202e5034840080c0050b143c405020304941d10b0700a0091880e4641d640d40d55034000511008013032098400d0000003900043d410540c002d5a81c0c125006001e000286890b81c01c1d00000035030002d0345042d8080810407041c5500300c3c1d140039100009544016591410071450403007400c06488804141a0b22418258001e02d04039807001c1e51096501420002440069401d041c8546144000041c108820440410081590004030402d84200c281c1c0c03401855150101803003071142c24000d919900c8014880000c04030706140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 100269856 1250 100268606 100268627
    0xc1b0103061d0117070b0a080604180203060403030e0703020a0f03140a050a110a050909060103120c08030f040f0512030a0f06120201030506060d0213080c030304050d1104020f04080a0c06020f0d 85
    0x43c080d00d480e5070b82c41c170700d8086e02c0e8089000000420519420003516103032901c1410701070b440c24035021085c0066580041e80343c8c400100300074149681d5a40400c592002040070720003865024201e051821344030b04100c607000da4644001c0702c403000c0c400e5800919010208134102c2250780078009082281d010b940302503131050100002a0800004207000401341d80b03581000740903031002c8020349069410742c2003a40f4440e020358480001d0080e08a1b000d40040e01c024100c030340c4901d8180f0b400a45e070303d881c40e09041100c0d41c414060b005221344200140380800c403e0086000d4008400100310110788992800d00740c071894841d100c103c2ea0004131020155010760406079020300000c2619241454603821030040303030004815a404011a01c81c00d0100110802c400003914404400442c06c241c5008000703441130030b940100800440801c40d0001d041e8903150103480300750000314181030b141c0351918600b40c0d03141414801950080302d070302000140503002003800c80c0c0c0c0c41c180c01c0140c182d003004040103503010f900c0c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 100271106 1250 100269856 100269899
    0x7060b06070303020903061f0504050901020c0a0813080705010504090209010e10020a06060b070c231011060a111602030a060204060c0201080c03070c1101050c1b0103061d01 76
    0x2151014941562180010101c19200c1c2e00c0058550748084c05142c9072040c014400c10843c00b8400f11064441c48803280718003102e00445001c074036940c40d2945a806405030441812007845a410300f0000c101502e00a08250500e02a4001119507911178050369541e05104541c04103100700014041a141c68004008500c4103060149000d00c1038400711340c00c02540c08030100182c0060701408100902401017200030a48600c0c16400c141d041d890302c9241140350711694102c1c001c842003043c410b80d00710703d0103182c3c0310b401401c05d0394640300441e0180c03003e503441e985a642d81c010400010b58010807880341052040045500324244803040f84410030003481050306a03810322070b085000c00003800a0009202030301c0d40382d03224000340b1140d100151480d200500b5000f400481801003200c0c041c0d004051a5040350441c03200420304903001c0042c3d455102d0b07082c2178081c9000740c0c1c003e4844010306034006c01074040e0aa900308041a542c4180307150481d254082000d418806400402c1441c10710140c101e1071049 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 100272356 1250 100271106 100271111
    0x30705091c03020601060207120203070504020a0212040b0405010306120302100507110304080c0102070602070806060402090105160b04020306060d020d081e04060905131a0d050f010603050c030f0f030403080706 92
    0x12400040107180d104240220300580c0050010b1280c3c56041c0300450003071421040740f00074040e2a60010f91103074000c0c020180a5680460009903885c420011500e4407070b00942c1c540d58941d1111024480e66115000305c3d80442d08091001410a5500c1e03d1000126050740c090200704440d2440040680005801e0301c040200c000786c00c4405810070700c0100300030b01840d0b0047c005060140006400c28140b40c1c090002e44d0018003042103104c20201c2d40e294840c100b1203005950754004070041e50750b800344250402a44800380481c0f01004a0494842e0083e40201e0844c0c9150317a41e50100036000d802035100940012000000c0d1001940080161040115440d4003501043c000f9510702069003160780b0040000e81e4514041119050690003c4d0001a2300340e014054440b003d10310844141c2c04050380c41c0106d40600e0010140142407100c500714054080081c002c1e10755030304005503a80c3e440d04032680300c0d000c0d244ca446002c0700300148001700c1d5400c00c800756081506e9610752040580140fa01900d00c0c40c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 100273606 1250 100272356 100272379
    0x50402150d06080705010806031c02012a020c041107080f0705060906010f050a0303050f0d111c0b0d05250806070c14070b0d0c0203070f030e030d0305070503070509 72
    0x441000c0039091421122500140007850700620528040135a80320f10b0601080c4404e1210585011449103244028480c0a414607140074500320b0042c0101d02901d013070702c0e165012020421803007101d2a1541036982d0308440c82215000100811200d1200400c0e5101c0010041d0500099230040074050000345130210a00f400d0080c0c8806040c95022079009a081d0031280052000c0b050325807a40000d44030a0f25200007860441d580500300d4071405034205404007003c141aa83d03a18550000c040c00150780d00150744134804518418519507103c07540064081c102074050009041080e00780d000079800400508924698181c10741036603000303260700d40a0f40341442002c2000c6208001a5003c0d00e01955407000003411070914407620412003100502940007804c00b0019010381c4015640b2511982030000b03484280010240c3c558070800c0e0b00107107003038403e10001003170580280391103880c50400e409650340301c16910b10440c01c941040f56081e020501c00d0012070880c62046000d0b0905030700291048842d407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 100274856 1250 100273606 100273639
    0x150c030e0d21050a02030a08190603080901020d021603021908030a02060601080a05070f050c160803130e2202040e0102030a1506090303080c0c01060e010803070203011802090a050402 80
    0x101201e034415500a0b03080c4100d440e50070410b40b81c041802c1400d1a0182c207211595100035128404d1582000412868801040a85001c24146002000c894401300004e42c1e6a1508141c1d81e000000280d01500801b00070403103490011602e05002400c2c0244941094119070030090010701c0b904903a00e0300199100013040c000420030007011416969002400c0343e2034403100043c440d030001031080501504200070b103d010364000c401070f0910021400c01e140c43d51405a031482c40d00185001015120320424030000d030203040400109144c0e070003240c8002c103150702d07042580301e0403006480d16820809808047c1c00301030140b0440003440b42c8010404600e884910b4600f9003a0b0b0000d954902e0100c1e560f5201d980d11a985104c03000041c2840d0801204161542c4c03006416420300038a003c451030000142d445603403000303501410150040c03080030300310f55031591020b07a90307608071240c100c2c025880c0058a902c1038000f10701404800b580200540351070340d10b0060300000307001c3c0a04120b070042c0012410202c1d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 100276106 1250 100274856 100274869
    0x307061113060903050106210b04050c030703110307050405070906030b030709020d02120f01080307060b0a09180318050d030e0f0301050a090501050c03060f0118030503040b030916150c030e 83
    0x1c1050f60382d6010f0003821030500c00e00315111540105024104104c160450f076070b5480c0060315050300711044081580d22410804d041062403100075074540107103c404410001da41c011041445810f80c00c48134819101e8050100301d9009070741d020040f40c0b0b104405c00810b4403a80018850000c0681540ea40c6c6580705100c4044e82c0003520b070302c0c402507004500c003610180346050f181e60000742d01059003403d515001d040d42e241e1040b528060001d07521142d0040c466120500c0d008010301a03c0810042e603d0131700002060a01101022030014401d81c080025007284100c09805503a00240180c0d030502c00e950301580c841d0440550503810074201c00c848840765600307100713444c40303440300060101d0220b20528000d401c65030001e003a040014010b00a1042c60b0312624280140c0103c28205048061a003100a00303440c1d4142d88000c02920001802050f64010030b0065802901080c04440c1003480c803d03d60341d0700103c1402900300282c0040705070141d0070300c5074139000c12050007030800000a6000001146a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 100277356 1250 100276106 100276109
    0xf03021606080603060603120414010c05151603050105100503070c0c060f0e03060415020f04030503341101051c050c0408070812030f04111002060708070e030307061113 74
    0xb10b000a42000218101400b10540c4080100c000d008208007841550f442401180182400491000b51103003007179000c1c403002000301390040304450300c10421800c111000e850403913281d0b210140c1c00400707680e864024001c5505a0700300900007002405c5011003219a500010b0601e03080110b04100316010031000c56059020b0203c580e5030710000a0407041c06001c01422040ca01c0c00307503010b5020040420180042d00e4070000540c0009030b0346000a05121549004640028042d8003000480c00d03001c080c00314000800c0c00c812148141a081c038050010b06000c042701014000c00000100a1803962082000f000105110000c003180148516100812180704550340d5101b000000350902c9410020004003005046d21b038010b001941905001021500019040381280104140410f0030801200c01c0c021148401915079001c0c1140f0b00002956a5825070301000450b40e440041074000e8030a1340080e5594501600540c80c000c1256541030081407070096508501000744024145441000403040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 100278606 1250 100277356 100277369
    0x40b041404020910020a110a0308030114062101051816030509190305040e09011b0e0d080d1b0e010c08030a0605090408180901120303020304020d023105060d0f030216 73
    0x90500c4880c6082a942444618428808c0030704038400c10014154108581c159200c034030742182421101000300308039001d01040e05525042035902e080031031101580060484000300c4406007140e1034010710f802039100a45101040c00c0710800c41c24a118000c0c0c01c4141c019001c501212103100c84d103941c0b2100082c015800300c0001d08001420421000c07800c079960b420041001c001c00c4001e034107465803c2d044070741d80d0040040c02207034101d0100303541c0c13589540b98041d038204101580c7e0741d00e0b010b0070300000c7c1041d040b1040403d22074000c40140b588030711600c1808540c10b07102c0c1c2189011035154480f16810003803017060310548480c1c1c0482c080d26040345240c080c62080341c1c0503444000003000c0c4880110345652840c000c0c01d0030b400411403545521031141001c2d805050040c0da030386541c00840e000003030026011f90006800d03280c0b44602c00300d0382168455800510302200e0003014040c501805e98606a030701583c807104007246140492141007602004038468012200d840d0540c071480c990003a540c1e807095 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 100279856 1250 100278606 100278613
    0x120a090c091a030c0f030d0c05010e01050114030d0f0212070c030c060807120903020601030609030314100f270c12090303021b0a0c030b0c1c09050111040b04140402091002 75
    0x400b241d0500b001a44a1900c0c216035080e0344214150200e81e8615210511004000b4900d11700d03000c2c00429884170b0a2a010040207010a603101e4141d61320700310b801c100f43d60103849074030a0450130030b104085240b003200290340078005407610a440380a194200110507100b4100101c0004000707904030b246600208002d45490075a482c10000107010741401c1d2031140503503401c2051030740000740d0116000d41034039484400010943c20605045004105040f003041c8105c2c0e2078400e02c03102c5100e10664408841e00d18000300e80311500d44241d2446030078402e8900c0300c01d1040e5820007442c82c5268200d400000d1603450402500c0c13108040035420340b5290801a030100b680010013251000c0e001c00340a15003a03081000b4034403d40c0d01c3d40d55280204a80c400600703240040c401080d40380320124100c5904111780c10082d01812442d6603070390000c0c161311740e0858803036203000d207905848201002520121030450820328101890706004030302c0c01ca8846801c941c019400c02410303400da51105c420351707003001484e07005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 100281106 1250 100279856 100279901
    0x1103100e01150504230409050c040e0d050403080a110304180b0a0605160606081204080c01080601050f09150712030b0111030901110a060617060606120a090c09 70
    0x3040800441a08400c0002c02c1c6200c4040b03640340c000040713138222400b103850800c1c060089182d041c044040544001d901c0790800741d44000703002d4006101c0d0810031701110104001100c42001c0d964802c848503969011030320a00080000c0390310200a4007480e08142810440c0d000454070150961b48139801c048070076100301240d90352001a40c8150300440c0000c2c1d03040c41c041c07414071001a1450081c504101102e02c00f90140c50204503868000a00511041b421075050781200000c1c29600d401c039018a10481c414103020040c0c035803041d481d40e0f005840603102c079072034003284140780d4109a000007911500301380840064514006404006c114050081c42d1500081100e1080142604d100100440c1001081096200c1c030b402c2c0442101d031400c0c0242410600d480c0d841c804107042901c2004043c0240c1c3c6032000c001581221080c00590f0104520184c1e00d40d55039410400009000d007110401d03c46180b00b001402050140c0e120788201b501032540c2003106aa210208002c0c1d071401c00508014210b620704 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 100282356 1250 100281106 100281119
    0x4060c20090414070b180301050609040309030b070525020f04091502070c050d03020105090609030c07090507030912020c030709110901031e052503050f060112110310 73
    0x82180c440105850608100300548001104940060310241161840c0080385040381030421442004182000c070700c6403500100f03990f07450500c0d5043c1c0d815000c6e5091400003411860705103403440c400d5a0646842290754215103071010010f800030801030070311008000b210701a948400d101c050404140140790200b03800f034070500000c0d80c50400c41500580c00c000d507100000740507000300101980500001611140142042a032080555203c290404c0081ca5040103044d41034001c1442444c0a10484030709842e807991056803882002c80c5030f10309802200041c030004c90203410090704049685030126492506448180703450b18031710b040c6000760b4030105401000d800c041c04804028860311004118400c64054085024070506801604040e60f81460328254840410444000b03002c90340208590b160000c40c983d546a00380b0702075803108540344a940c000511a0042038032a03003100f444941d985c0c84000c01540c0c4948540d43d808040ca840302089020609240040c51043c00404000c070580d901c0c02c803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 100283606 1250 100282356 100282373
    0xf0c0b040306110a0206011e0306020f070501140115031d0313090b0609010c0615031a0703050f06060901030b030c151305030f150402060405181509010f17030d0204060c 74
    0x1003014114680c10f2242d0707103c00b45c02081c10384c11550b90b0002001094070740a06101c9000031904010207443c404201540c04a201801038000030384110000c0107001a660301400d01caa400348544c42c902100000d4580401d071203a001105500304030070601107280d1701e80040170304540024441c0a0281d5000b00104141c00c22800307945400c04040c0d40051070310385c510300000e04007411500301404240c0c452042c402e00340c07800641c220045402100e1004888440d1100560581090311400b000905080109080d03a051441320303030103850000d01e02490042d0260065001d04000001c0c4d0340d05004506800d0420f8541c55691051464001e0b0000e907207040d81d920501414076150400380c0250f00c000d50a11441d5000200d0a00302c10965031461891ba940d84005045845540c02c07490308030f03186a2944448010f1030700c269000d001996040340407004098240b0107070f90424403803e615216040b00070030241008034685110103412906a82c81c006100490704282d0b40300380c1c0080009005002c0787c406005070707103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 100284856 1250 100283606 100283621
    0x7020f010b011d090c3c2502040615030e1501050604030b0a0f020d02030405150c0307110114011202090108070602060f07030207170405150c06040f0f0c0b040306 71
    0x242000c11030312081484102d68051080d0b2058001d8614a0104139400d01c0c0c0c0c0180c9081d0030908880a06441060900d0006c2c680c0c0420200c003610101c04180c0d5a8440200c00d94070355180c4c04413844050b1200c00c0c012039020104040903a005651007001041411201c0603103521840240c0f400715000d03c550a00b41c3c9400390918001040c4040c04005100702d80c0c480044608407a00314605102d191103070440c03070b4028644000c1842c40300b84002071440521000350003949c407450280098501010030143d005a005038102c030241c080c140100300080146005180141c0d03008050341c000218004a4915408030041c2a0802d440c41030715080c00c00304514200d110a409000d0f00005015620300d000d001030750713a001c0905003001006490001402152095040c1c489154021850b411095900b8804814030ba0103030141c0d80c080d10102e0404404481007000300e590503030705100100301a50791a1174082c031000c1000c404032446907261213441c0100d40d80d201d00001410030415443d683d50b103549010001c03610705 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 100286106 1250 100284856 100284859
    0x3050c07060206040f0f032604030905030109020d02040c050912030405030708030f0a0f1214010611070302010c1506030b0405031c0608060f070201020d150f09110714010902040507020f010b 83
    0x203d0104400503000a800c420300d26440402005804030b0344c41e05451180b245800d98440070b40c240d0903145801190200b050103a8003d4a400c90000c3d2100c0c05c1c1805d9450400c1d0282d0071400d01d241c40001403d29a001e00001d40044c90030341d01340410b2800007810000c2d601c020303104992010800f402a4602404010020a0204000c1d403400300401078210300c9000702d07203104050022005488040b603000d2100181000c4c00c45104110015640369524a40c3c0d2080c00b88100051074620f004501d001c0c0003d40341d00740c90b01611000015a81541c0312030490741075004521105441e45d84c00000902c00078170365800b17513208801464032602d80c0300256942c0c501d100f07001d0203018181401002480c001290040d0042540030b2038440701c1da00d002c410b03400380c80350224480402c0d2604c1942d00c00228036440c28000d9580801d010416150707104c11040aa44102940346030b14036080040d0b100003104034440c9008040303208000700f907044d80c03600001c04540003201c09070b003da04009002c01600d0801c1c402d008190a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 100287356 1250 100286106 100286113
    0x1a04020405010923040c0804052503060510030503070b0a1a0603060f1503090d0e040c090b2b0b04180305160309030501061d0906011203030f0f0903050c070602 70
    0x1d000c000030102e941e584900c018101800e004103903220305080c0c101c020a80301400501207400150700042041c0012103060342c0d9802407800440940503610300078401d80300307622481c1c0800f600315102c0c81e00411014081141c2001012400030001f0781c180003074840c07240141d00002c40d61501020482c02e4400700d55400002003201c140c446169947c40081d2900400c003510107048202d40079022800c1c050940c4440c1c110140003000700080703003000080344080e04039640e42d098003009049041c08181c0306042280780120340c000d44e0502c90203803410064441c04584d1400e8448100304595581003603c51428050302142d140d0081600c04c2c205409440510000f00300b84c40440366003907d004050b0b000741020082007540100c454400e051080c03000b40e0242d40c010000304480e0b5910800080801c0680703a50341c0a2112020008114100216581e8120303120035590072104812513038224000c08e9002042c440d00c580d140c812913000c0c1428491036080034460b49a580d40c0f80201b0012900d06001540302004651 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 100288606 1250 100287356 100287359
    0xa080403050f0d02070603020a02160803040f0902030f061c060908090915030c0f0a031e0515041e0c090e010c1206050109090e0705090f04030806010f0206040f080409020d1a040204 79
    0x51380003841100702c2d5030f60300e00161940480d2204038100034030700000100c4103143d2140070901c2c1070301100800c115030000e202071010341c1d501c050342c00aa000482c0d280a081d4045000584981015200e064112007003600070f0700c003d41c86545140c2180c0044070700360381000d000304003848181094056140c0100000c05403500d0302e40050b0010790b40c0c00090840c24050030844002800503110000d00310040c44e03004a051001e0f08808122000c03003031150350f040c0c803140f25100b00030303074185580f41200340210340180712030841003510450030403103c015410032200820f01800c00500e010051140c88148030401d00041000245040c004201002c1400c0000040e40351070020400c42c0c1c2c01c55540c0c0c0494140c0d00c00403808000070701c800c5c3d00348079107a80003d401410040412590000c10722055126078489c2e2201881903c40c00f004584128280242c0c42c09a803089c404680071516454400240340e218150562505848802c0441682c00a0950004171500c0f00c5c0f0719207581c100f0449100400c00291002c40c20a0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 100289856 1250 100288606 100288633
    0xc100c0e060f191814030c060903060f0718080c011e051204060612121701030309050904020a03061508010e011506050c0c180a05090a0b060613080a080403050f 70
    0x502c0f80c102e075881c4109242e20b5041e400390090110009a90928511454460ba03440c2e4aa604580080c2c82c140b00780a010a014400d00c0c040094072030529000d80180825610500042014040170384400c041c8441c080007215015201c02c40d800140889102078000303903809100141009005541c400c40c000040154616060f81c8041600c05400710850b281e550341d1580d0030420300410280c1c100008250340d00c1942000d01c001160040300001080d82daa4215070011440940c141000313010080005407a03c40410840c500700440f9600140000c0154418540c0c070713694681207a18000d92180c03441e401040030000c0800070301c100070140d20307080000c4c8483c000c1000c007000d4002c2e160103403405005000c20b100a410008110080c0b81d140701410050540c81d5001030b035080d0000441e950616076061400080c03d1920110380f803124258071080507001d6880740303c104150350700220040000388d00da403140068006002c0107103c000c0303401808629034450a6042c06400c01000052a0649505c852000030383c0b03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 100291106 1250 100289856 100289887
    0x9110405063c09040b010f08010903020303010614090405240301060503060112030c1a18161a07020306130b0106140d0f02040806090f010501060e010e04090204020c100c0e06 76
    0x41803542d0740c04a0342d000c400e064035100e81d60040040d4024242c03000708002c200390b03446224181c2d0034402c0341846265850101a0982e0401e07040140103820500c010060113004d01c8005240103121840303242400c41003000300f4201c8404490301d508001c0303860745c0ea00714484180148491210150028402203080c4004280d480c401842403c0c051807601c00244d0030f00d8410100700d000f480c0d1000600c0e145440055406200034029103000c0100c0d40d510400030340c500c5000420720b00c0603c001d0002519285020024400388101400c00c0b1090300d0100005401a5014001d6500c01c1244590140302c914284c00d14055668050700180184203811481d100000c00e05030540f031045814200100d141581080c20101a0140e680000994854030381409505e0307401181c58a1940d0010008010310b170780e642c81c22a4081c1c0100f4180d8042043d030b50782000d00b03081c1034100c48522400541f000d40723007440305c04071103142207501001c81c11919510480000455800046915403040c11941c840c100000610841c18 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 100292356 1250 100291106 100291159
    0x6060f01170f0601021e010506090601030c0e010c02040f0c08040605010b0c03040b03340f09050a05060c0106030b01060804060606050405090a0b0109050604120501060801020705120c0309040911040506 88
    0x5500070b41000460300d80c800c1204075000300f40702c2c0b50340300c03103441404125000e4001621110300c160b0b40500014150b510910900031005015501c4180c1c40a0005c01074401448039141642c10a032540d1f00c000f0b0282c1140982c19200903607684000d010300e400c1c184501292410382000004c0903040200c044040000410381e810740fa82d004140340c2d01d0329240c0e20030907041141300c40910490a01c0869424034000300c444440191005d8480c12080781450104603600030b494001c1d190f211403108030a0015040c80400b51024443c3c07c00000380550f106d4843c805124401d0b48040001182601048204030450103500000c100500b44641010708290000341e01c0e20000300456119542d843c01c040541c1c0c13241516000401c7c0191901ea40e0315160b4401c5258070700d0120050350b4541c00d0040000741403e0500c00c95650300d80160140400e6100b40c0200e001e2072303000c04d010b200603200601071245656554810100518440c500c90300603800b13108244001e50308020003c030320510f4009610300c5500c141e10070441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 100293606 1250 100292356 100292371
    0x2a0f0f0118081218060c12070306081f0f0f02070302190f0818043e040302040c050c01020c07060f030203070e10050c01090b04060b0d03020d03021e0a0206060f0117 72
    0x801691210814600302c00038104c4076100d07100b81c0707080c006007202c0c0000034818050b201c03420303620550304c41c48140c00350741561060709110b40c400e5140b056294281e08065548c1003605c4400f00301481420002c8066030321030081e407c07101d580018101c04050b010004811201080608820540300903200d00604d0011003001420440e0300150102028003004000e002001d0020020000c80d00302040307003030741c8110101820742c0074200220490685c00d55410280d00b1404203001c1c05103400c0c159400c1c0030151909803450401e018050001814011080c005052590045001041690320b00030004005c0032000d807898051520401c240000c49030b04c203045020826040c0e40c244050746548004940c58807036004100895441c0160801c20030085441a0380241d0180710140805002e01c020000e1300c6030030000c002d01507800380e01900c003070a00a40141080081d54880f50f1544188070062100c5540800b00c0c150050f08028200001031038250007240c294902840d262880250b55100a1046c7c03070050100e9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 100294856 1250 100293606 100293637
    0x91d060409080405060c0606090a0e0c0d020d020a15031a0f0f01020c150403050d050c0a030c021507050a05010c0806060901030b0f0423010503030a052a0f0f011808 72
    0x1050100c0d41c0200da0051401601c026aa1082c0116040c7c5442083d914140b28100d81808245400382600a03211860340002c00303024112001000c00c451070b1036010080f40c000c00a20451405a039440402800601081300801e0380c00c000108000d007180d000c04131300360300000740c20008032a0b0307110010703456061041543c20200b03600c0b0f0354006034070305004140c00550000b5050f23103006e406030f214800790049901c214100c0c2e4a44a902c903080d00d00b40695100f0303090541c000180b0ba00424030500714060b80c140040e06180d004548000c542c201680014810341720b690210001c40200202441604070030081071038903032071900f805030016030760380700b0f4000390740c10140c8032602e00036281d845011002e03010400903c10403880e80c89000f81401004102c00c031040c840201c0000140c42d007004030403205178426554507140780407130320070400710012408156100101c454031071034a00c10307108110b8841d0403c00e0b6001071001604030318600d401d50303444042180000d100f0304020400210020103564512140100c507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 100296106 1250 100294856 100294871
    0x51e070513030f0501150807080c030f1216080d0b1003050108070504020f0c0d0e031507080a0203090a050d02061816151209110a0e0609010306021e1801091d0604 71
    0xe0151006e80f20740308a0101201b00010920343c005600c00454075580291240b4441c04000c140d105c0c070405000744d51036001071012881c0218288000c1441002206146039990301503112020135400001d11700d8020340c2d4403810002e49207003031502030081c10100d14042c44258103001150351200f0b150b1003014019500480d08a9490344c0420680313050780102d600702c40d940740c12408000c0c044210416003602900030070707090445401005c0012441805a40c8404040d9103035036442000943c001000c00c0034600504000500240003801084010742c2168004e1500d8107001c610b410408551021301c03000b96010409013003103070281e00c241104030f940c881c10740c8040b555114400d444d16084168000d010500e4421014100003107081c3c00d101e040030580e05850070503200c82c4440445c8005540c0c1030b51000700300d0010000548540c00074016000c0e0000480c100b04003c02c05401c0ca908210050f4482c0304d40601824169640103600000801b05980200424404083c1201030464058201070140343c50751071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 100297356 1250 100296106 100296113
    0xc030807260a050106020f0d0f03060302100305010311030106050d0b18030307020106030b100302010221090a080609061e0a0c02070f0806090d0504140108040f0204051e070513030f 79
    0x140034042484962010204101d66851100ca25004644101401d40703083e001080c51840080c200040d0700d03010700107021100c01c4040c00e0b2150f6104492550805840d5a4080011303150b945410f1307940346003903c0100301941180b410350f009415829405000e03a14081d01049107a643c10b0112801b10303084003000030292520b400405500840c0040c0358001d00c00041800712646d815030104040301e006104d502155114610a5418100703107200107030040c0c1c821030310301015015800c4075182c000c03056515245450803440c081010202765500100c1c440d041481000b2050b03500b480a198800c0442511880001c141401030810a00107030401e04800d0365040c91a04e402d00030040c84015010080c3c0c8a0601d994845086640e10000ca5019009005d8081d0020780207009000352016580204100380148034114011107480070020802d94000506008480c0541ca440c420f00303020311400300740880d44442018160382111000380041007007140421603010586101030114007502c0e03100159050008142c03c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 100298606 1250 100297356 100297367
    0x1309020409020409030503070e03061005060a030e01050c04030b010e040305032208271906030b01031d071518121103101d030304050601050103020f04090e03040608010e070c030807 79
    0x1030002e4006140000e10000c5c135810002031841011150384e20307803410180f081850707260700007510800741c400d000007014009890120080c0c8155002c504d000584040602c14150039110281c900d40e000c000009000d2040c8441c0c1c44510b030250240c1040c0c81141d0030a80e82c01070107840010640604040748216200c00b40b03007210100740425030003084040c0c0354039003031081070420881c0449904601402001c00105401d000350580d17440720040d440901d0792483c0001c10350190034103116030b07030405079240b551030304041710b11a05141e0040910020131840e42040010791245511811560074058184440307080c020b01e1081182c1901c04e1148214051881c914244419524640368942e040c05210700000b440205640401c41144051071800034a40c4424403407601d070300c810344018107150001401444154040d4000740b02074481c1049985c503150350740501d6030484950760b1000890b0742000070208481580008001e01424144401c0b21490409400152200c0242c280060174458520002040c1a0040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 100299856 1250 100298606 100298621
    0xa0c050706030501140315040623040f0507050d0503072409050105070816050d0b1210050105030709020f070f060204050d0515090102040518060409060f020705070602030913090204 79
    0xc46005540301c03a40a00588803d0141c0c8081944440c4140c40c2841c00060710181014120502d0001c1c0c0c0312074071484041c10001000d08400e0b498004494010030b036420032284518040c8240c000b5160182c0780060508880d94400c5129545851030203011460110071203400d01c1d40304c0c0c084041d00030010b014400354080364aa100f292850702224100380081908034511400c82551034650310f90310101750001c4008040040d6001400c1403060400681d141c0d4000c0c01c0c9541c0041c46102000c800d111041d24100b4600103440341c1031f842d200100401c1c141001900060314041d001582483d150700100505801003480c06424210103103408000c0c0712440d4126400b5020140441c0000b103e141000c503a6102441c042e504035074188000107020200602c2550107a420051410484014001158501c0d880242c4016801a0740701e07185000a8158419110a031141c1e84c00940c0f00e02c1a41481420b054041e4010000d5400422040c0080d5444010007003207000030102c005417845443c0042001010314 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 100301106 1250 100299856 100299863
    0x5070305250e06070302011a062703010912020d020d0c03080708070c12050705060f0c04060c0312020307080105010e1e010f0e090403020a020a090912030b03031e0d14010b0403080a0c 80
    0x51310014558107412145129054103451a20103900e0400c0c88028801c1c000d8000020080c070b0200625400c90b80e01c841040c0f00001c0c004a00070320992150112002da414a101c0940c0c0000c100d54070882d01880070311580d01590800310441c018688014280c2e21009010a00f00141c1c9400035801902520703640b0a0a030308004d05650200c0c2210b4054800c3e07100c2e501c180c8603403203648009005003000b040094400c0c14080c864504241c600f020a0700c0396040c0d050100c080c030150316a214440c0465101840c40380100369145d22080d45410000b5050b0007000e1940d50041103449800b402c4c1c842003000400d00100207180c00c86105007010301c00c0b0351115000f0325040d4080454030500c0709055000514040e054021a24207031030b00d640b03114003170403608850002401040c52101c0001d405000b82d0000300341460140c1900c1c90412441880d0540401148081380d44540206140510204a01c250680038500000003503030b55050400c210114001c511008120312000642514064419070b0011a039550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 100302356 1250 100301106 100301119
    0x9050d02030324181003080c1f02090a061b05070e070306051008040b130b0f07030b120a0807020102030c03040b07110109060c020409020301020f0d09020405070305250e 74
    0x20100945940c800e5803c03884403459034140b10840c81100da645a80d0743c600800c2c8030641050f480c82d450380140010483c04000c503d048000011400c07a40050150040d2031001e026a446070348039030764a1811161101290074814005900a6192140d60340c05903a01801d00c203042e120041002c210181e03510f10001d002d4010b4600c0000d03041e0f0800041405100c0c2034405010680d00e880034442e440b2244104880000d05860105011030081203402e0b030414a1256101044800d42d00ea08100c03100a854540700c0108070700400c42103e5141c82050349030001103030014000c5030750150a07581c981071240081d0510700c00084103400c580c0200221500b48041c90103680c5c48a580b040041c0c816045441c054a0084543d0b0503145203610440c541e01c2644c0c02a10f81e02420222902800000e104e030700310072078042d076082000402c5036080c10041c1500301c5c0c0f11400070820022510600c0203988010304140107041c201070a101d09185440c0b001100c000c2da1901d04a0316140c80300c1e00b00c5100700c80200c480d81080c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 100303606 1250 100302356 100302373
    0x1005070e0409170d020702040509030c0a140309100806041d0c12030d0905070609090212070f090305070807170f0304060c0302010b150403121103030604020c030702030706050319090305070b0a0905 86
    0xb50301d401031b0588a00845003001641d1351600800c0d1644034017030746640d550b0003200d9000001003080d4002414079041004503400c201d4a440420301e040f14120000b00070070411403c204452400b4010151500308486480c0d071903d098000300c1d5035071200d8801d0540b050300e0b0b149201003540c0e810403d46040c0e485040080c0109840d5081c95901e64004c0e000d184002550038001080b916258000c903802c600081207400c0303c4e551400c2d01200c0109035034a48008114000e1000004500200403d1000d401c070000948413213860129801015922a1903080e604c1d00020403032010705034044213503400c480007410082c0901030503181c01c074010403510b110190300c0080c0d280200350200a040203081501e00c113074420031148920540541c1d0801e4041000a116401040003403490308040d0050f0000c103603000b04490411070140d0001e420030565400c204000340d030110400442100c0102d9014507240b10400c10402469542c800500501c58031801401c0c0c00c1010000c210000c0c100c3c0c0c000c0e00c070aa0080161400034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 100304856 1250 100303606 100303627
    0x240e0d0c05010f02030c0601120212060a06140f10030c050f04080601050f0301050f1603062102040b0108040c030b0421020d0f020c031c020c0a090c021005070e040917 73
    0xd44080c0503190001e811411124001c0b80000b044070b00b0301c4284c0f002024907a2802c0c10b2200c50400c1800704036001191a0781c0e0840c01c0c40308100c1c050049100c14000f00d07043e400d004498108524500303c030340c03080c0c1c0854605002d540300c07603014000500403840e0103e44e500c00f500055901d80310710060703080045030000c2c00040c280004078038141650400c469a070011041001058282c035025035000381007803440000b0821101c03d107075020090145600380400c0417039580942c594100038021036000c40c0180200309104503d064802e084020500f428a8205c41c20a9110007540505600000303200104080100c0e0910004c0300345103180d003001d5a00b1003a80c1e002140020348814101c00d403034022540501564500c5800032a42400d8288098000c0c0307003800c140124070402d02c0303c448603042035000e01800d00c081030700d07040710600203440041000300b0b441c00508030003880c080010031440318040c078013001d00201d40c1d44102c1c0b00c0e00d1550100c40100313410300282803e0750480040160b00c40c02130700004610140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 100306106 1250 100304856 100304873
    0x15020c0c0a0602011b11030a08060f0d032f03030a0207210e0f030102040b1204060204080d02060f070207062001060f09090c21020607110a12140106240e0d 68
    0x40302c07280303240d0300a0201d40f0806403003c40d05403801541075002400b08c102524415540113a03c240010311032014041c03850040345800410344d40c19070004100b0518038021420b4042101038000c400800300783d100000034901e9459000c00740c0040885a000202d01040c004800d0003a4510140541d40d500440001c03500603089a03c020425030268a0500c601c028625061007920200c1c2c1c01c0140c03882c40c1c00104504c00351a04401401182c41075420310001c1207001080281030300c3c003041c9800a040e80d003003c0044120f0503200406020440d84841d40c240001540981100c43ca403940381801043c0914540c240d5000d00b0580d003040c0b5080080060001d001c0905400070b100c0c03103005181030500c02d81c0340c625001c003003c0c00c804400352507076a0016110041c00c0041c02021024000e151519400695a0014011403110341c090400c4400790640c140c2446140260070b6032a1010900070800c091800c082c0c1d5034403250000c000b012086841d4581c0703a1050160040d419440070080c0802d140c0d4de81c9182a070030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 100307356 1250 100306106 100306121
    0x302061602071a0915030f0a0b06191116050918070501140d05070f030c110303071103130b0901030506010309050c012601030f11180f07030e010905060609070c15020c0c0a060201 78
    0x20f20b4840208c1c1000f00310744908425054040e00c0286080d4840c207a10320f890408510100420010b1451100d01704020303c10b00040c1901d2501c2c034544039241c10100000d04001400005038400800d8014418150000e41d4008586003800c0c0b0380d100c900c90b00d80d490541c2c040d0005a4881038100804c100e0142d0b0f012114451500250b1003c104072081480c048039010509008040141c3c41000840c005c3e500131031584800c0000407080f240b9200c00c1c01014010007050b5841710001d450041040b001c00c0d03805009031a844402840c0c20400394a840e1a201e568214400034035041c4054047c4011110b002d10851340c0310b800684450440b6540c1d80e2500c0c1000e0380900005851002d083d0b05611004d1405982c2c5a813100006001d20540b500e480b40007156641000d461a81416079414000c0032500c428014141c509014002070017071440c120003405071044000700030104000c0d16010143c001010712590008030300c440a0016210604175014526182800c9240caa01c0400a01d00195640d8150070034035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 100308606 1250 100307356 100307371
    0x2304061e0c0c030206010b07080d050907030812101a0a030c1b031214010612020a05070f110406060f0c08070606080304030b100803031006030231030302061602071a091503 75
    0x1005a031fa9100e00341203e00409500800d003a5040211201c01142908181c1e0400d50301010340702c0c0d040c0e0721f54500c06035500076242043c400c034024082105003c49040c213403000b0250b06200b846010001c02002025105d540e5040c0141aa03551241904600c1102d00250031782c842c4600f4101e2020a0402810326141441800441c5080900b2a402d0913900005036040314905d44840d110900410380703500181d0808000d440400c40244820400f050b5600b0b805010603018805089110081c0014002a111590131242c14403152200c0201c1141e0300102e10395819400036829502c441c0785140403406012030758040142032102280c08414840e400c0b490a010300a40981d0680043da41c0c0442d076120b001c00c9845241c2d2144e03060301000070030300075002401041c85075207540d40d40e03e0581c1c070202401c600c1081d1580030950b0751380c400d1082540400c0680d80000804050600291404100035528811800340640304104c043c6915455901d6209551003800000c100d518440e0b00e04043c400250000c4800c1c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 100309856 1250 100308606 100308613
    0x5070e0a06030605270402150f0d020a020118050607200105090303070807020a02030c040504240608070b030c19021018020906060306030a0803070c020406080606042304061e0c0c0302 80
    0x40d44041100005d100d14200240c007500180c3d43c0e1a020015141c2c403140d00342408400401a007a448803c0a005010144180d2030041c4c84000b50003009084070901d010341e0307000040f0742d500c140c04504002401c90b8400518030381a140b0045a0104c841c0005560071825015030030b140601c180f20b04040050344c42080b90b0781d0303040041c0d6103400c8201d0341d603040b00710b019425420a00180c0f5007400d1036000f40c1e6100e8000c207540300d00b61146801da035411058165108030441c0d42e802051041640500500c8000c000d4440e4460441c2002039003809e103031044d4034541050f21058261141c407140280210740c40c00d9040107041008895400c400c820581419900300e10614480c800200f183c541081608e0140c0405130040c552443c01e50b560b218280d01c0600301c01d0600c00745407100d00059585010708009080a000906414140340c014842a6000b1190114004041414942c41c0300307401c10141d41d115400c11000300c0d01161648407400a60101c09800c45158140082c041505030002e400410f41c46c460b500b02e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 100311106 1250 100309856 100309879
    0x3010605030a0c1706100b0a050c0a05060103050714010801120c030804031103120c030d0504020a17011406040c05120c0904050a090b010b091e121c0e01030c0c0605070e0a06030605 79
    0x2000c0e00c0b903204031000c03148134001d61401d1014590380310145c04088d5903810264646010000b229140448400085446510100040c020000c0034060314001340380d84c140e0f211082018500181221005002d02001444142044030911040c0d414620003143c1201441e40e0b04c58903030070048082810507820700c1c040e20403035500255403082d50088520021040e00a1401c3c03c0e0b019070407001804000d08280e9200325084000b00303298803a41c014411403c013000c0005400407041d545540002030003460729201d645060221012290030904440c141c1d42a40300c0d102455680a41104a40c0525218260018500810022581d805038041c14110f4020014121244ea884108605511910700c042e5001008046503401c880700200403e5010300004208600082e601d00c0e50600c0c1c15110b008032100d010320220103000143d0406501e442c92003003803800b480040d81201010744441c2c441d2800030301072070341c803030004403254441e401191007840d0051200002c650b132101c0080c05130507a40640c500c1690322004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 100312356 1250 100311106 100311149
    0x9060503010501050a0507060933050402030601030219080d050904050a061410030905030c1c050c1b0301020c07061112070218060d1a07120911060903010605030a0c 72
    0x36a030403194140c0d1103130720344020b015003101d260300082021074445494403008000104014140001c2c21540b01030000c6165a00100c0e12018411401c2c02032400d00d00401d103c00340e140410114150fa805540d90300c8100c4602c080c070801803040d940300d800540100c5010400c0194400014004100c0480d0140410307281c0c84028012140644180d1600141c1d000414119041c058031a40440d102800d0004540390103440311400c5910440322041103410903009203000700f1001260ba1920707101c61070030600f00a010311095503030308003480c1c1000c1e001c0203854000550b55400d4045811404403c015980390036551400542003c80e4600d00351081c2c040c18800840442449080c0c800041c1c0080030007125030940041b100c0100805016940c22411000c0d584010a4400201c040ba80c0c034140c10010051030071181c02402e5440806022220604240841c1e01003034843c40f41003e420000c6400c0d5580d030707040f000000d00401d243e40c401601801094140001d22401001142c200d5090461800c24000c0844 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 100313606 1250 100312356 100312367
    0x5210403080412031506030c0c1b0e10060206130204110a02010c030e011a120a0b0f04061d0c2107080717150705071704030f050c0108060f0f13020c0a030906 69
    0x1004e221711604001c1c41001014841e40144044940c1400c0c800001308003510ba80000c59030900110240304d0401000300711b40082d040b0320139030005540100040541c10440c4c000e4813a0006040703540320301172050503182955215030080b10f02c0d2004140c01c9588400074400a4080c218540040010a103070954128844106004680c0b407002600d111035441038440040081c103501415010380c0b01e2054465040000b586c414200340103800710881d0300e24502c0c0901e0440d0564410002180282c21031600054441800141d40c090f880c07c01c8444c00004030041240b4079001e508225528428402d0781c1d80040d04a401280e20b0060b2441184459503003140d56040543e42c2854070007445196584000180300c4901c6980941b00741c500c20381a07504049003140d10807880d60056001a100740035400700000c01c02404004449503c0000c0c205145603240013400120039402c2c1002c014000d0040d6010706070503688000c40b94040c01200c440454540d00042c1c10aa91885c0c0c40000300c001c034001d40c5020610f107000c0d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 100314856 1250 100313606 100313621
    0xc0b010806100308030903090901180c0c020f060705011b0507020406080304031208070207030f080a17010b180303070203070311130203040503090f031c0206100b09100521040308041203 81
    0x800a110303241c0f840d43c5407480303036200810000060105003c0200d40760b4034045c1c81c074001d010044c100084400298131440c125060040400144800c8800300001130700e0b0f90380041c4007503104950940e200c5606081060240c42920014105505540001c00c081a0030801501d4030170b0098800b044402d896002c500c0c2da0f4400da01010300240400120031460a00c00c050860748030450f0720554001a551b43c3e00e150280f080c1c03407422038030b55101082440b08250700c4407071103007582c40c8160410642c1d4034220b8003141c24420400710748a10020001860701c80e860030400c544180380d0240807a250343e943da0a007140341105000c955481074034034002d005e842d12141e00130343e40513641000140d13262984100403c51096007a0210350b806000d40c4c02024020744405412404400254000d081c2e00d2800641d04d0a4000c4a0340203150900360070b0240c0c1d5402e8940b10700e42d0701c1d442e0003400d00700d036998031814581b40801c00460502c0492001002048105035105d050140954400d00e03480e10380d401020026820f44245 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 100316106 1250 100314856 100314871
    0x50603040b0a0207020a0e040503030106030c030911060a0302071a07081312031a0d0303060906120506010b070311030f0903010b060a1d011e090f0801050c030408090f100c0b010806 79
    0xa0301050b00310a030b59009024051009012035426070342d45100c2840c002d400c880a071800e8201000411001341c05000c0c030000e021491400300000e20302643d804820444c8091000d004801c0424803000003170190f4120707280580c114060075081c24005440c42d03400d4074102e1fa4000069910f0b80812031340b40302203038046680c5074840d50410344124013900c110014a1010714203017a01003601d901c03011907140c0c41000c801207402941c01140c2541400c4581b010b48617190700000c1c04440c1d80e000c0d4400b0850200718103040d104488012035541705582400c903006241000001c00d2408000b94a03428825880002c0c03130600343c154001d0020460781010003400d8007400d509032000c161544c031900d10020342e00303408042090050502c0380051050000101e0006500131114002c15201602030244401c440040c400400e1120002c2c04185042c0c40040c01500002d44014890380700891460b00325501c0b80c0010300d0411015001c00d00381e40406100420410310001c068484034000c90000c500c1810200c1e11501c6081b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 100317356 1250 100316106 100316123
    0x906120501150608150307170604030f0207060f050c0307021809070b03040206040b1c0617160f1502070308030f040b062b02010c0204050108060601020d05040e0112030e03121305060304 81
    0x107501c403140407040c0002c050176500d805458030115140076040c00003522424450010603103407410f85006001d12880c0c0c2d410009543c0481410895a0791009440c035060004e4600b00c0d407941c1070711000c1071440c01140e50095021350501c0c1180801000d40c105035118290f0042182d400d607980b541c87c15641e1209444c06501308000300410300c0066030702d000070f2484402001e82001d8010600c10a00e08035a4681c21060210500c2400c0d60340030784040200010001040455481c1c01e8a0401003081d0110076102c1e80c128820130182c45481c0600034002100150340015911303541380380c0500c420999003012201201e02ca20070f400450307a1803c00b0300074100f084031698550080d04c43e603915000c4916480d448124104502009640c0050704c0b14000c6600a01d0100014115820310b400064103140f801c0d8200c1d07040100902c8200401c034035a42903d41100c10102031030700c2a4282d03041c126620b1071180001c43e01807040c0144060901c50130802403568030310003162005110388640c2001030f50701c4183e070b01410516 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 100318606 1250 100317356 100317361
    0x7020109050f0f0a0e060310230402011101050705040608160c06110904020d09030e06070b0636011e0e0109050c0c0f0a0218131502040906120501150608 67
    0x420000320b20040000806052445840000180305090190403800c0031288003c01d200031414104880a4084204442413103a24290915140000c10340450001c2d2001c04c20046401c5d64021140c0ca81440440300092015262042000d0850350040c412400014a0000011841c026410341550031903030507030314080b142040740c4a14000e0210f600000002d5a07081001c003103a680c2c1c1c0e00c01020260315101001c0313441440e904000d41108040c14847d8000c000401030480018441450346074400c1d0101d0b1600d03c1401d50718210402e001c119050440c88203080d1b14840c02c80d00200030054101e4040ea03466111182a0306c0114562030a01d108407541010900c1c01840810066003005511a001007101820050b00c0d01e0f20364a414424041c1540c40d41000510700e0540c2001c3e100c00c0000108440300201c2d50419007070400302460000c0000d422021b01500305140301c4210f070100c43c014038507060180a281c1d03d8402c010311103c5180000c550541c82d103d0710104643d40c55888030704407411625411601e6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 100319856 1250 100318606 100318609
    0x50405010210050c040b0403050c040c03020c0d1112121006090b18150406080106180f090906060e090c090a1103011a04050406030c081e0316020102070308070b090d050702010905 78
    0x410004d45030543c602c60603c0041002d006d00400781c4000c44c000c50050060812620500c030491700c9121091042600401445440d21000035800500c070b8458130b440303c1c1c40303010030761034500b000d40918102d6103080e03000920900d0900441c010902580f0400d00c540c031429901d800c2920707a0740e480d00c54407001540030301c008600d040720140818030b85400500b181c6000400708041c228264081c3d08100d000c01c2a81d0018000140d001945400c481c440c1140c054400b401c0c4004c0d130303845030103600c200a0800e40b201000410405d054110034010413a80342010b11505118003199103603101500a40c2c00b07030805c03100050030700f0420f0095820001c1c0a00a061460b428501001c00c8540291100030104100b08030000701a12248550070007140a00401d0010500305044e50b030a11176942402c480c00480071220302208540401122480a080c00c0c20b00700ca080e8500c0140c0c1088600c0d4030107841400c0100b81482449402c0503030303d1040c519142070340c464403004081565a03008103000031703000510000050125 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 100321106 1250 100319856 100319861
    0x100801140a0509010611100e030909190518161505070c08030a020109060b060901090504020c120705010506120f03040302010c0317070f0806060901140d0908070f0201020706050405010210 82
    0xc40805801c025441da00c400102e95940004c0e80018002000400210000502800340c81d1024004103401d0180010681c0c803982e6074001d86010034880d28200010914420044420080302c03440380c1014890b62074800c2803000b05104105103140d1502071882000070f014441d4001c002039455000c1e4130f4803411250072045641f030f00000f5084030040c125000205000f401000a004803091541c00496801d8943c5071020990f04a002e9450040006112a80d01d981c1c0040080c000c9d07a4060b100140c0b100c810001341490100c81170040c07101351800103400814020f044d003100e0b00c0340c0019560460341400300c00c29950380380a242d92516180d0024001480103611809040800c10f000e80350040c0018421000c10200103000d498160100c1c0100000181054028200a40c4200c0884034103082c00540c00020700503002c006880c59140e400016140000c449035480392154603000300500b91100064038042e00210308000040c0e000d841041c100042d4148644c04880a03203a06a0103800e44001c6d14515002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 100322356 1250 100321106 100321139
    0x1051f1502010e10060303142703010204050d03120b10020a15020909090a0b090309011b0503070503030c04090506090c160c0305030a211802060c03070b130302010506100801 76
    0x442d501c502040c1e01d41c4000308000c0000800c25100062210702e1850042c2510002d54005900d010049c00700545043d04409416142407c868180415030b078850f000074024803540d0031155000d89540620000d150780401e070302c1161043d50030200420300c07908003080341c45080240c14070300590215281e903000038000d03a40800e5a003070000015051040c1d9400103165880e048540345402e40c024810307001846000d9041540004000d400b0398906020200000c0180070035402c6420082098a580010000108103c60120f50004140c2e42c0f40d08001c0720341c41141c0c4c070a125190800381060080340c400e1418440d43d0f8010302801d1181131501074061010000c2c21602c8005440c0032404040000225000340010103a5103282e5a98191401604241c810741c00d0950014011417490031b458040e02c0660201815409501103541d5500c40e441ca216045c614450068010f2000100c0824000f00ea008511000d101c18070a070000d218982d10303201030203100c5034210801800100c20800400000c40d00c04082c03013 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 100323606 1250 100322356 100322399
    0x2180d0303110301151b21050c010203011e0803030c030601030e0f0703060c090e0609060d2402070605071805040b06120f010e070504030503030a0f020405130c0201051f 74
    0x14190304820800d070068200b40d10400b90003060800c80c100c42c5a000d8020360300c10040c40d00c18402400f05c0e031079001740002c0e803202d0400001c1e0038690350322540707000d00103585002100700001c2d0750f44d41e190a500d203000f80302080d501002c0d010900002c94051008001d881c400c1c3e54b003201c00ca003107941c0c0f08011009842c5943c070f8948a40680c2d41a00f100c0b00c8184450700c040d5020740310100d203061217264000c1406089510992f051407a8a084c090f40340c0d0b54800068000f14119103900b41c01080b400e1215009085800f0744c0c1242e881880c81806000c1e0580181110740d000ba0b60410882c0d840b241c0581d540842100343c020700c1d00e01080140042c2c5440c0e4442040e8100281c880350a2202441403c0b035003600590701120108440b1004200b0300d8111503803954404040e1030204d050515569031a952070001802c0d421040f9101c1c4514001c88503598142d400403c001408505428040340f03150008004038018000194200310018494070114100e200c2c5a1485615901e90349140c2000d910303002c41c540c2c5165 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 100324856 1250 100323606 100323611
    0x30601060f020318120a11010810030c050f0609090106090905010b0a0e15041208190f020303190b090703150f060c030c020310060e090616080414070503030406020c031002180d0303 79
    0x70b410201b000464040c41c40f40c44100c0e0304042c801d00260425000034401080d881c0e100c8828000200138240020496500b502c1c1c0751a40700c1c0e424002070305d0780500d540c000d40140301880001844c80e8068180c208540b1400b5041003643d803100c0d003a900d40c1c811124010081200341d50b51a081d0b0810040b07481d24851041102c0b410240c5403040d00c004d001a4100c2614900e01c00f25051001101c2e1541d2400c04004a090800401040020180d22400010000c1005000d40c041c451100b5943e6040944002d2009080112914007480090010f0600014000800c40d444001052000074441d0395029102c00b84c5400c19103056640d01120035021141040381c06000345441d102c280700d100d004020190400e070394801740b940ba2040c1c51901d8000001d014080140543c40342c548510b41115000f9002900614500300035200010031511f800c02c40d0340040c0c0c242c440003a001800030b030301054414032000218240c9000030307040e0f1140000d034010220340b4240c0f64a82501e407102032400007200d2840c00e00c01d0a01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 100326106 1250 100324856 100324879
    0x80705070305011d013c020f03130629060a0203040b0a0c1509020604030f021809010f0c090e07050903160308120112120e040f061202030601060f020318 67
    0x5241c2504d001c3c0805024030340c80846890301c280b20a000340c2828440f40181140c200c007021040c041c032008110640c1c1101040c0e40b4072581910b00d16011150b14041256820740d50b814240720b14802a4641141034600c1c91401c10700300701c2001084440e03000345a509905d0a0003c1c0c0070410408180c1c001c0b00300c80c0651004100c00601843e4900c05080120b05a4541080040c1c040c2421640d003146c2c0012070000d02e10380000d1200503902c0c0c2081e41c4c00c0d2078010010601c90805437020074100140301c0807c0441403480800c00c06803401c15000786458038a850b00c00d01100c3d40007030080e919280e181c010a150a408100001c02841c800c4000d8410f9082c01812540040310001940c54140c005400a4402c040300298150359500550841401450740300603e58070651366895181030032540341d40820401c22900c821450554071904198851010072100300102652080380901020322030000300d019000d00c0000140c0c0c0c034051410001d010071590003640c9070804620025405403143c854803a0b001114201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 100327356 1250 100326106 100326113
    0x30819060e0601020708061003170d0504061d0a080d0504030c0b04030915050f070201030b010905130510090209100c0201092606011a0d051803070b07080c0301120807050703 76
    0xa1100400c0c001c1d10003031542c20220700090500c28190032040b9558405821301054051254100c0b040781e42005a034000e079040c880ba003409034828203203180c0a1504000600050103a207900c0181402c0030482d68030130000c02c4010700d54481c8100c400103001d903072051006c02c02b0429290400d580c402d10a151140495a50f6560f440c81c5240c1034034150006a00e401e014000c0c070b411100b18482c0081a800c05030300b0171802011800302807044920090406440c0c8142400c1030b40200f03100c0e805044000d0240484460388401c030300082c030f01243d1816151141c0140040c01c5e1b46240300b02c0b5540c80d4040c2c40d40c02e005541c0359090743c2d0142007000c00c034108800c1c65000114014103180d030b0784040c2c1d40c8440d6052001c8840f01000c1c40c1420603046114442e0200c01c1d0706076204110b004440c8088041130700440d5645da032644a0561122120810003607000005d880c50130481c903402100c1c4a0009a2100e1482e5141c082048140d0301090003044400d00c8032500d1007000c42c0014000d070038130034400d6048a21302901c954 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 100328606 1250 100327356 100327361
    0x41814010f030201052a0a06050105010c0f060c0e090106021f0605010c0f0507030b07030903030c0f120b01050706140141030307050f061e0405060708070212030c0a09170a030819 78
    0x1b8411000d8000c0600c2104006141c060540180401d2921020510b40c3c0c0c6c41e010510315041c0b400030800c1c0e6070b031002414903601900c4201c48001c1c000744030319120340c2d4802c5c0182d2902e02ca038108501c034120700903141250304100d03c606425240181e540743c0c146e40f0315588048440141d10f6094406100f40800000025695541584075a006079404030f4100e94900e0098241c0b1580d884840034002c280c507a03582855400f09040d800b1100c803c0c004500400502c1c0145c400384181100903200b9820800300710103000440364024103c40703a0301280781042d281c41c92080c01100c49820080c080d04050020030071006120aa60022540c006042c1d03480c00405950b4145003072140c40011140b1f80118040000c40040c0007000020400b0b4502d414070345251941e44e00b070310740d0401048203061049040201c2e480354800c11000304184401428240eaa04000210f180e194012816003800641c00d51070210701c051039604a08842c0100800400c2e22331032550781983c560b40300510208828000f5031000803401c6150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 100329856 1250 100328606 100328677
    0x801180210050c0303040f0c06050313060f09051006030c06050c0d3005040201020705030f1504030212041706010506040305031c0b0301020406030603050c030c030d050306030111041814010f03020105 87
    0x841201101207d10f14210104100c03651050003071200900400c4004175180014819150380088c00144482c80c4801c10030082c545050041c11030302c1107998141c00d51181e58041c209480c050100b0b80d03529580c5160480f40da01c18450364030301640050a8000603107000340448a640c410240020001d0400048108502c40381c0c03241206005894006010035944c0500180b005010194050040d1150804840782e580814204070042640410002428035101303000c03103500f01a000003126500c503503a0740c074030070021950710001c2a103008031000042e4070b18080c000ca07001c40303500001840c00c5c06200c0341c1c8440801196559aa01c10b9180d45000c00c56a0702031004101134800c0752070000e04d2074150f0404624003807082d0505030003540492000310007960006001803041d038681c94207554070391b15980030034058550540340003100d0380041030216541d0203100c84001074034400c14042040190041d40c2ca1a201c201b0300c103500c0c1c0d86244030b07001d01c0507520803401852260180280c00d008403032494010215040d44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 100331106 1250 100329856 100329863
    0x12061103040516091107022101020a0503070201060f0f150e151c090203070509070e0301090f111f050a02010e0a0b01180506010e0609030c04051f0801180210050c030304 74
    0x2240c0240b10000c03080307068805006501005c100845c01c0380d07018a05031240c100c0c040c1c450b8124041c1070a103541d0b80c0100b801107410150081d9203e203d10070002c3d089070070956000c800740d400e011000c5041900140100704407542c11201d00d070224640002c1c0b0724048034403507814080001e00c04400304503032503a581c1001001cac1ca0303010030355a070384104450030000d010b041c020442d800d040000600150303a0001d610320950707900b00c41d151201d40310703801d0640303071640000101501942804414070601640c6040c1c1c4a10030301070080200358910300d4007003080204038500700c0f810a41c621031503c4112072060010700300c1d02d550f0380000901d9040600510340303030145541040301e214441c0401405050920861115115089482408182803940004c2d0807244000d13140f90080901141c2030700d5581e805c21a4240159018001300170074200020104c040c00312030209484040458400010381000500c20745150380004a0800d00302800c990030001d43c000700007800c0c0e003044010b0001c17810310322090004601544c030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 100332356 1250 100331106 100331113
    0x5040602010605150f09030a0f060b0108010611060a230f2e03020405100314010b09060a0303090e0c0c1507120e0307060504020a080a03051c060609120611030405 71
    0x250800007030945050b60040381c000d10301d0010701c0369203200003020741d020130702c09460b500d440c1c02840b0f0200c1c0c548010302c140900820000307181801030020301c2c0c0c411009402d0a90314400507a8885100b51402c004800c501015948210001010400103500c274003045200c030303010046003084001c0340400c805815110341002c0c400d24400d00054801d4011007402001a12126424111080120321400645448003034000c545a000040d01c2e920f544030603002665100c000c0a2503070181e00341c0503009000a203141401401075101081d01450241103103400c0303a50542c4c94890141c2014018519400041c3c0040c000b460705001c1c10041c4c046c280641e00749032907441c0f030340060381c6400300700141001c50b00035943c401d0518100c60442082408821242d1040d082100450726072102d1000c207000c210144d00000302406401c0320403041690240040c4289814101100ca14400943e4140b0403101103100310004500301c55010003184844500c00c07485a40102000141c01ca01541920707926442114200c60343e40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 100333606 1250 100332356 100332359
    0x20f0c01051806040b07030e0709020a03050405070e060303070f060f0501030f0c06230c0a050f100b03010510060809031201120605070f050405010c15091a01060507020d022e0504 78
    0xc044014140280303000c1d00140f01604260320b40c119202405007083d01010341750780758413090302401c004100040903421811540d4140030b041c020020300e070a54040740d50b406007a10002e1405100d01c143c500950008000d0761030706000380c0c1d03000c3d58900e15000441d0025200d212000102c460351041e14001e500a0f2007100500400785006407046446800038820f0101c0e501c0d41600358800701480a814426a440780c1d070351785080c1030019251400fa031000418902ca0440308a0746c00501184104075012806414000d01d90301d00c040609031981190b80d8a8401d4400004200706446a0002600800f0440c02d582c90500c80c4100303000d07185004d800c00d80c0100302c0c8011010030000d03248030b585e034450080e00e80b00504410f060801000ca10851081d981005410290320b8240100039091100c0c1454401d000c2008000c0b0303140a40c44404a00011041c0501980000074081e001d00110b4110300e50080079060550031a45c01c1199048c0300303909000249003454400c14041e01030590040d040702d050341715540c807603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 100334856 1250 100333606 100333621
    0x12090215070614010608090304090504050a140c150c031204022b11030114011a1b01090c120314030a0605030d020a060e010608030d0e0309060403060609050601030c0507021201020f0c0105 82
    0xf101039001c0b10822080d4010000c1ca5480070040d201036440c1060701149a031510305142d4a4440a10400303090350005400c03221718a0000540c2d000007420075100c42c81d0445410b58200024010110b0000300e940042000d481c1030700300c01e600242d00c01c1c4000c0c0020381656486c4e01409040c0d111800f201c126002031030402c03050044650200085407001c030000d0088405404202d400204184142020082c0f841d45121945075000c0648801c113280d40380d0440c0c5c0e80e148003100c41c060078103014140c0b5143d80450700803442c881020042615039815441d0850000502c002c0c002da980e20090044050f01d81d681c0740401c4555040c05442c250070110f60051a615400307090000c1140c562011105045c2c1c0350440801001d0030120654850003001d803000a0001c1105a2287c2184103d02d4030a900a000140c04410007415501900c1a184005401c11090755890015003c403404404080701003203060140c003006141c400c80300d8115400202c00035080c200c0003110108039800042c032201c6603945400400042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 100336106 1250 100334856 100334891
    0xe030c1c020f3007050d0e0301110a2003040303052704021903050108010e0d110c0904080403060c1701091a061c1812050c01231608040201120902150706 67
    0x1c00f041080c141d20b0a5001d680d03240e581c00f1601c11000130700ca03180c1c46a030b405a8080d44030070400714010324180e60b030745e5000303100902d0b102007513881c00b0750009a8103000107200c20000a070780c00c1d02e605444840c94044100220600740c680110310003020240d400c2c00c211030b40c44a0014002030906240900b070613500855018080d184141c000808503898004c500109860014401600703039040c0c10121038400b00240d44d5070800140e0241c09800891300c00c10300c010002d03c04001c3c000c80740950f004120082c9014001c50340c23540c1000c3c2c45400711a0800c0140700c1885543e01c046150904050754845901001b00411619000141042003072243c0f032003022811055030007400144c800031454103541d03880c259030f42035003c0508410301d010003201281c6c00c441c44000358802c06452024804560141e82c05145030207045108907050501d101040102184441c080e2810a0150354161181c444a00c02603a098004010b001000c0c0d13400511040244d481c1e2030490000c1507068050030022600c080c000124004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 100337356 1250 100336106 100336183
    0x3080d0b01030c0e010503060d030306030b130b1e0414010f1401140a030f03030510030609051c0f090b0c1504050d02010c02030a0c080d020f03150102010e030c1c020f 73
    0x51040a28413605542e03800f00071260f203c141222500007480d000e0400714000c04080e007001b070420820100f449040303c000c1c0c031111040b42c454600d25441c0e607200741c2142da50300d420884524000c68840040340000b040400030030b081c1c3e00100300024130304641c10110010b4460850200441c101120010f00035804224000040c12a05071002d449103844c2d9503076440c98480d03500c00907080640d6000454001c06c0e0606803a002590411424048192070741001034503603400490481c007421540c0a800c8106004d07914043c2480d402d070300c1d00c45000d49420f034056071561010b2404142030080c1c1c2c07034121103607500f89041400740d8000c03402400980000d0001074219150658040150f50050003618000340e44031170382c05161a0304c18641d54441513480700400290041000140d0840d030040108101403450740702d000c4840310240e000380000c0780c040d070907a900c9100796614008290440c08200f0100500c1d110424000f0383c040c411140d0400d08003000c80d0900c07124510070b038107a02062404410380d04ca21440401c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 100338606 1250 100337356 100337381
    0x6060806031b0f061c0f061202090a05040201031b02030c060c0c070b070c030c03030e1e0f040515060a120e010b060a0309061d0a14011b110703080d0b0103 68
    0x340c2115020002d29499041c01a1449080700c20407800503038407110280ea076031200d4240112040a80c0b11315543c05030904405111000d444c0400009042c100134a149003616009002c10107e9240c4000490282c20000c109a06140c1c9076100f105c0014010804240340da0131550284d0380310781c8888582170400402800d41c1125800a001c66000c2c4140803c90b20110b0380d80c0ca211542e11103c070720309000844140ea0020f0312015910b60008149074000a004110403401c50341074410082c0b8903069040d5441c007a0200d40c101c080814000810f04050340081e401c001000c80786005c501c0e0000c0042c200d80d214032240e8000802504110080314040e0090400c03603c01c0301c000344140381000b408035066024102000c02010749403074140c0700b407040340c0c6d100b424110071000107040620130904c54156036108048040341d207500c002070000780c0c03082e040c4501c010080707520b5070030040807103003c100300d0b0740001d2068134035020701504d4400000920034370010b00d2342005500000c250351500000140486501e268503030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 100339856 1250 100338606 100338613
    0x6020c06031e04060e16090c02150106031107120c030908010603020105030f0415110405030c1507020409080d0903020c040b060c07061b0206040e060405070504080601030602090d0807060606080603 86
    0x305101d6842c0060a241107200600e5805a549a040c22400b508150710041c05500411400110700f2054181c050184c0364403e10030b00c60103c4071041241d480074021092400b4110010060020b5071298000307202101d1030141080c18121309484550045540c43d1841001c1014162808101034008295030001c0040100070001546150000781161000605e4104031814403400141041148501544000110350b01000f444003002210a0a580305000b0940300707104244082115290040700d04c0c64490301c0020a03070920503a6800c1c0800f404202d00c040302e9001c000c0c800b10054016502c60000c0c0780e4040d600030116150301009010032619070903091401418204644d02d200c44c6c0008042c012502c0c18600075201212050a680324108040c9009600510021b000944031000f020f0781ea001d44011103040041e81c60710755050b1203c1c411031040041c190040d038010804200998040c100c0003402501f03110301443c103039a1701000ba6000f010112081d1340d440e44240003e9511010060380054281c008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 100341106 1250 100339856 100339861
    0x1403010308030f040f06051005040e1615050c19120306030302030712030b03030a02010f14130f051905010f0b0907050430052817070f170406020c0603 66
    0x5075805440001d00e81e030b26110b4104081010082404500140716812800412890400c0000406142c0d46842800c1c815405c10030700108a00c030104005822420707034841d40c000d092a00b4001410f82003000d14200c1403080501c80810155414803044000900000e490079812005140180c03102800c41c00d00b400301880c22500b440002c1d000021940d50a82101131255a00c0788000110050328106810640600010420010481c1c054009010080c0031000a0000322000c502448905000300d0b0042c8414881004500c045002a166010040d000e00d00b55000380002d00c4420348076034444030b02112142c0d95a0107070301e02c3d240c1c648190206040d04962886403418001c0d03005105020364010f0302c80d01c0f1218401007524900c40f880721b2a020340190100c001c0c1c00351074205262941d000318035444491400d0010410140f109041c00741344d0f6944110950b0500c141c0c641d00c4082608505000c84200400f0110500482c00d0304002c4042c1818a02e82c031030ba01d9051000081c10300398400100750103030005205 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 100342356 1250 100341106 100341113
    0x50108061b041206020d0e0304150905040507082403010603140c0109180c05071b06090e0603030f0d1e0b01020c040204030b010b0306130615110f150702070306060b04050114030103 79
    0x1154903e500481e0141c3c40d80000c000b440001c102c52900e04460713200c00500042c03a81c0301d0030700d0318010319019100c1f4801143d03504240000d4030000c60381c12002400d058002030300c3c0045d01c2c200311407441a8000c014001d1080340d000c6421515150400d0358010010303485804042420072030601e04050a192141ca000d1604200000700d4113100c40500c05207403105490000c1313070700c100203945003d41c00035005a118102d105500903140c0e014040c07500041c41307100c4042000402052400e024003030140085290a20400381035600c0e4000110452020380c6444500840740c80140302512601c11550000803898100c00c006881d1800001c2d215005d64010311080010481e8091114119071030300b0115642e03941c92800041c0181008684082814680580890b1140000d61104811b411325102c543c02c650304c041d103d42c4e880ca0803004035111580800390308030750360002440040c2c002c6074500403200800d0f26507607100250b407a144c0120280340c0b004182004990380c40a03844d403c50001042003807955042d0345 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 100343606 1250 100342356 100342379
    0x10803090a09020c030904050a050105120f0d0f09180c020606030d020a060e01020f030903040504050a02071e0309090207050609010f0606050301030803060f0a030506091b010e011101020706050108061b04 89
    0x420100c0455012030003600f8804d051046070b40c8018010020081403038180038030720040c44217000360b0b401034031518500c45000d440051522200c1d9041402400e40c6c0f003d0403002c40ba0000b43d0304c803d408101014500050324800b09105841040311160702050190120800900c0c10100621083c840e60280380d20012154010a80580380d41d0010742c00b08290a2004c82c0c1d6000e403040184003856100c0002c10070100603000b05c060015034004503010b00075902e441d404002a03000303c032005040700308640444885041000d1500c04098404d0401d46d48060fa5488160200d0b0172125055556421007070401100d001c0c28400d620344490b0321081000481d042c00700040c00d034041400b00a000001c0000030511940d1000c1c40301c3e1280000034521350940740c90703192168548509075111491807240e60301000464021000c5201d1010069403681c550000f00c81c01111044101c1c11080a655420408800407500134042c1a000c1c0440380e0003400c4034201581140114804a0003540703503400c1c1480140848007444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 100344856 1250 100343606 100343609
    0x50603010f0c0522080d0c0506060604030201050306040b010908060c040306180f14010219030207050c01110d1b02061b120c0c0105280905040e010e03030a0203040807050708060f010803090a 83
    0x4858895900e20000c80f0407207413580d0803060703042c4110410500d2040c2e0004c03844200e54854026107076503440d070f42c2c1032040764001c03400028046102400060614240b07030b40940003c2e941454100c50b503590701c0c18224141082a074507484c02c0940004e00b0700500910380a110a0340c82910000c00050307007140c646802d00d04d1074800c01403604540030100c00d01101e0940540c0c00e005420786012401c0b0100c024060002d5004901c102c49900800100405960082c0c041005c3e80e00e651014001882c1e440c1c104940c020300340b10340800c0051702000a2070140e02d40b500070700610383d65501c400c0d1070041d24218841c50030b1001d0304015030302002007003000102d01e00460f440304201c2007803c016890720344162800c020004851407039802109400200700006602075801000c450003070310100b1801819040d503900b40c611802e070001240d4404c2000c80d03202d03000c81c1e0080d81e0146c0100d6400d07040050590b102030a00d421076003d02102da11100c103100120385021015401406488000c5141c41489030101d0504120ba = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 100346106 1250 100344856 100344877
    0x2030a0807050a150c08060303090d26030a1a030a05030a141b01150603020403020a0b09061e04090c080103020f01120609021c0c051e0702060702040c03050603010f0c05 74
    0x8924403040050030080c2400c10395014042d240e074a0501c00d04500149485e10001000038864404181181004400c460b04004c000d80760784518441341e21004c00380603804400d00b088514882e410052a5030f42c102840c09201ea200d008203004a21003441100d002d81102c0b0f007442a0000d41c148800590f0000440d2858006401c2c4503000e90030448200c4810301450041c00d00358060000050308121041d030050301d4050540f003400921a0302c90804804034055400300035000348202ca400c0c815508904054800390400a02d06450080b00743c2940e01c5c1c00c8e032404c0c0003c0d0200d5021405101402141c082c12035040d4640c80c00000c00c0d817441d0001040e040c9208641c80c18803a58805610546600341c1140001e80301d5844150340e20802e2640c410f80415007a000081c07518a804564a40c40340710340b044885d00741c40c2d100800091540c0b142583d00a0b440102c041b40d00c940104081e50068503107003c0e5941e06202038400141c03918184091500352800c080001d500580f60080c0d00e192182c00405440300d5514 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 100347356 1250 100346106 100346123
    0x10c060b010c021003050423100b0a080304061e031107020402091504120c0b040608010b0307030f0504060b090a06030201120b0604090e1606050a1224170c03030702030a 74
    0x6010016900c0b9a00000301035008641c41030000c3c0c80302d800d600414000d900c548011201503901c10710720381c400c449800c00041c098110500450900ca8142c002294003c00289524034140c3d541d8862803559002d0703881080410113680a0211640c5489450b021001700c03030400f41704803001c002c0092990710565200a01c1a64042001400340d00d0b03e01c0241c03452422100515520307500c8001461070000c05100c00c80b04100d980f0310220300c03e41c6d144281ca089132605c0d02c41c035440340d0805400055641000384160205070341c0b1021035000c0080782c0203150003280541c900042642da202c082c446130900052000d500c66003000c10070001030740d00035850032405120441c002601d031344600006070544200c7d40151440da00707055150810407008540c011882640704080110195a001c1c1643c841c021203801c1c2e8041506140040040d460b5900404c58039894100750582c5c502e440c2080803842900783d08500d000c040700740c030010f0548a04100c000c00040084000b581171520700c1c0c3c0000c0c0c2d100300c1c50030700500c0c0c9503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 100348606 1250 100347356 100347371
    0x4030f02070f0e0a0f090b012303030307030c05120c090a080316060b010e0910060e1f0c0614160f1803060b0f060a03050702061e13050c06160210020606010c06 70
    0x16842d0340100d00600d41c48001b4000d82015080c14041d009083c010075074818401b00461180302c8843d00c0c40048900c01601444c1190344221060303008100354030765076042c080c0c10410360b00381c188844820351092101c501031b903032500d250740c06008204265800540707142e0b1080014105114400304e6502c103607030740818003040340d00800b00100c0740c0f0500c4422440e0800d01c01070602c42018200c0084c81f0075a0040d42d6060712580d420810000000340c40810201454860b000a9401c81d109008030017009000c0d000100e110010950f03e500154401c4840561154103900c44007665940f2a400c0c2d0380820061421181c0e000300f01030384144004440c80001c1620742d0752203006200752120400c6181050004264030307103e021076000a400b410301103800304010b015900005000c000c00d0903458003070400d00c0b8041d0500b6550400c20784511100503409450300d21030000d036803409a0360b003030042c100700c040c2c41c0c80e2281c00308883c030500c035141644003026800d41d04014100b000d60b90b80000500034880d08900c1c04903041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 100349856 1250 100348606 100348621
    0xc1205100c050c0a03020105040218010f06260106020d080c04080709020c010608190c120b0402102c040609050906060d03030e070b03011e05011d042304030f02070f0e 73
    0x520800d01000c80c2e0b4001c4d01c103500300740b58066011a00c0307076001380d6003140249000840148000350034020009240030000052102501c9091110000c8524510020900072040c1548405244c240e100d84010f911412100b1007a951050030b0070382050b5481a642d00340342c248071490b5165041c81c003e80d0101c0c4c1e80032035040043c04003508183e0090000d902501c4949500c0c01d20004030b100e0407401914684445000000c800c001f58001c50780c0d45810048020858840758200710140c1c201c03184c0d810070851010103100e103010b0f45071001c840098500102d41c0403080301e60180400e0f50300c00d074020340c0c41c2231502d420450314242c08191541d1040c0200d90010b001c041600c0c06500508403a03c800c6603901c103250022070003104400c0150f060f110030740384800103440455003c442c3c02c1c1c44d6011301c9001441c680f040c1c117000d50548071000c4494000500218204002203e014980041c040040081d4446401030001f41904021051303025050b92000d058043d00308469a440e448051041003c400341034000280c08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 100351106 1250 100349856 100349867
    0xf1509090601120809060708130b0a02060403080c0c06010602010506100e030a081615020d06080102090109050402130e0a020a080928060f0911011b02010c08090607021207030c1205100c 81
    0x70020021b18161315520175080607503d07034008030b55210000142c110081103038090201521b01c1506103500901c956501c9644c05c681c1001c3c050b041d842d90017018040040c54030400c1c05500e001c0d21841d400000c00d49058001c00070224903a583c090140200303001d0703c201d07540300455980c0d2815001410156200011200240000c98884001e000d01841c1c1c10081c22080003a00104150000d401045c00710320f844010707030f07403c07403140b1042c0314045295014100440c0c249500500103071210240f503007000c942d0781e49080c900c4480460b0307041003283e40004d00840740e542002555800900074030050100540c0342c0200304030b203c451035803541038141e0388000404000140c0c00040c0c7d071980100c82408080382514001c0580c0c0243c08056000ca084000c008203078010400d210445540c050752081e801c0000d544491f40c0603486909210781144041000001684801003d5040e0103039160090221504d9400d043c01120042c0d08030000000c80f03d204540420340c009140f01300c461a0050000721189080030503203a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 100352356 1250 100351106 100351117
    0x7140301141207090b0f04020f030a09061b030203010f0b0a050f16060903020d02010c030e0a02060d02361e012607030c03050f04050d0c03021002030f15090906011208 73
    0xa09100d0304201184c0002c407900184011281600c140949244c07404c208002d074022002146e900e03401c01c1c40040c50032401368100c804a01d015490009040f960b016004050200c58006080442d8002004105200c07011a142000342801a02c1a0500803285070041544c41045007800311040081400f01d10756201e038001c1d8900650041007000001d0072440c000e515a1000c0d50010b000d17510703202c0c0b8406400d0280c0200301c8403d5541003d4007500800c2d500b0410f05421201141d10034a900307002d41d8451403100e00030b8001c1c6842a020b4003d07520040385a50051f00510440240164100c0350440c3c00d10302c1c0e01a03a900b4002c02407c011000d04d00500c078079144004000a40002c459070704003404840d64050388801c070404010b54092003503640380030100b08a404244c03001842c962121810030a018420300b80d40002da4800d2040d9403408508002c44410f0341c2060b00c07400f80c0000c1d54401e01803c03025001e8260b8aa6100303403076200c0b107440c000c024551110350503ca02d4a0709908520143c00304103182040f81d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 100353606 1250 100352356 100352389
    0x2010f1103040f051c050c2e0309050f07080d030209060d050a020c0c0a03050d0f14030106030213060c1a07020a05010504060b03011103040507060509011e03140714030114 75
    0x2a1680c3d550328903882d081c4854401c0601a40780644254200201096900c0b522034000c0010644d03811040d06200717441c1511602100604210040d503941010781c1014100301d07418558010030700310003504056007014814111504a5805a03101f0007810101240d60200300101d82001a00e424441011400c03500c41c60b1414403480f80f50004000b4600713159030141c0b001c52201400c59483c2d19110702480a11403041c000030749641c1c41040c45901e8144600580e410000da00c0c50915114124489000c04541080e00402c0c041394010401e002545682c0350442c000b0205460f025a501d006038450480340340003010f900c1c0545801c1000100414001c00c00203000f50b82c840d00803c1980f03003074148103000b810980d82d828425403c080d960408503480b10141d0f80101d80200161244078940070098400740d11000000d41446040401855406c220104010a0764000d0300d0104541c1b010080420741024020f10b080140a810704818a10380c200c1804c3e00e0540302010644001181c0410010b4400700002055a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 100354856 1250 100353606 100353613
    0x80303040317150303030a020a032c060a02040521010213180b01170a051e0c030f0601091d041a180118020907081803180118030206040302010f11 64
    0x420140c0c4111503400c602100d060750b1840c0d0300c40c0310302084403005440e030316039041d8801d0010408980069000344241d15445c02d002940c01840020225410058040340758800301c60201e0b4160002c041c0070389527020046510442c5040e05110000c0e0054207036103504044032800c5507812003690340c00d45c11211007560100c0c958143d25a106411195503400714440c000c09030410b1003000c41540203c61465680301c9a0f2120805540c80b802d0300c1c030003020700800105811040600b1100c01800040e242c07402008110005940e910302144c82c61608980901841d04000240340100004405195141d1001c00a00f244100ba5190390804640510780c03807030a031103d201c2e41e009201d824010042c0d10002020364100a00c0301208210781411420603a100c060b420101329400039580511454055501c041c4410b003c40302e00b0032504820b49950080d1900100300159064000d07901c1d07070070040b141300c0d01c061400030001c41d50865000c98054081ca200c0203041c42003150310881c8050050f030100404034102003c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 100356106 1250 100354856 100354861
    0xa03030807030f1a01020115080304050d0507030b0411010f090e0604090813170d051305130e060c04091a1e03100e0102030a05060906030d0f11070e10061707030f06080303 75
    0x2010784d0070b0030001d00b280550710300a80d020641e20411080011916450061800d140c0f61005115140b45095801c585600810501100023008041c8490080b4040c02214414501440008d0308400602c2c41d940244011224100070090ba14a0569407204081d50041840612440c00d45814007507240001000210110f01003201c49900f402d8642007480308049404c6540500019201c901c10000b103100c601003112030501841c10040328064055030090340024484099907403190401e0f4040e6800581c0c00000030b801c00005c000d9000340444d03601c076140101a03e1903414006648d01100600e4002c4004008401d85002d41c0e0500601866610768141404103020039840d450007035000700c5400302141d140038007003089411709011075845004040c0007000c00002e0707000e050b80d009054503a01c40401c0012070941440308030501400000701a00c080144140c01c05030b00058285d20241c01031070410100c840c903260301c0300c0002040341c0c02201c1380c200002e6110380c148610028003506c1c1c11840e55480000207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 100357356 1250 100356106 100356131
    0x100201020d0e0a0204060e1308090607061a0a05041a100908060703091a040203031b03040b12041e0218060a0e0403020609061605120a06080f0604051b0a03030807030f 73
    0x55a0340340f64800ca408014150300c545044201da601561524102415a0300480010341450001c6c9886100100b115040c840719940e040b082d10b04000d800c260070034079601d0000b07241c18000703a81405008100c6081c0301e40d103000c1e40003520b881800040203105180a80d04042418001c4c0341c202701401070300003520801c1c5462400900500403482044510044802081040c4052288407500440d03004000e54038002c000e00c9400c0c02c0f802c0d0403550340d0050008010001e203002201000305404041000b0300d100c64605414060380c60103601703020070400e8a03d91a0240181e407a4429200707095130300c1c241d02050f500c60b007011070201d12060b000078034107652440620051540005205204034030240c101c615599412034000540d10404040310086034060000303440c0000f80a40c00c651107001d840001880a0ba2004184c4c81e12540101c078007002d400601c00d000078403000f0311000e070f0340c000070102e00d601500c880001b01d0724113101c502c0040c040180f20800300b00d110748284c12099101060a0303081c45040c03003849 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 100358606 1250 100357356 100357363
    0x605120d09060309021f030f0e0d09080c181005090c1b120301090b0609061315050906070f031206030303060f0e090705010807092c0f0411100201020d0e 67
    0x349a0408110059000a00c061290244044079603000d0300708410b81c03503031a4403030403201045451582415211003204260018500c00d401107070380510014040e84403080000b9052591a400054142c0c000c11202e07070302500d80c1000480304404103080c800c415503581d91106c0b0820341366001240d10003040d0302030102040e0940e001d0800e41141910b0303004a4001502c205688040c8011074100c2e50300141700403c0b502c18030354480d00c04400007400051910303940e0800a4519403000c041f60b80c0c4034000d46003d000d602d82482000034291040c0c20b24500c2c1020400c00100709004041000b080002c0d643d080c01c0402d0b12403500c05280300c041b0f5000744507950b1280380c041e0251410b4066400c1041e45000006111030042c0907680c054100700001c2c003542c41c2080b00444d42c100004110b04103012820034005103401600c001118410345036000d54101041080c4108610280689141c1003c217071102803001080501d0340d0324078509000c03030340704d600024694000d0b800381c0256088119017034901110100c2003507011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 100359712 1106 100358606 100358623
    0x15030703080c01140c0a0c0b0a06091803020c0d0b01030b0411030d0e030c0a03120c03030b0301020c0a02040b09070c110105121312020d05070312060512 67
    0x94070341c41007541c030291440505a650b00742105000c400c400310706411100e03410080e450f08032103100003020304910311000362510386510045041c034886503206800401104409200c502001c1450801d20810100140c01601850940e58060718000014600b070680c0813044056917400c40e2540070044c0001001110000001e4000030501d603000c0018003a24103150f86c550b9680b00710501450b050080c249070050156184c000c0c1440020014000441000260710781041c011526040403000b034a203458079580c1551000615040c013400200b49580340710700a842c00c0c4003030901e0805104034078004886840010300b0700c5102c1e90000d41224400c0d921480145801804c2c0000b000e03680303030b2071802a02d017200d8004100d584002008110707101c01c80d161580c1c1c000703400501c030a1304029040f485800320040030050081005038145050340d0002c0050100a4050748050305950740c2e1654442a5 = true := by decide +kernel

theorem cover : BRFrame.Cov 100179856 100359712 := by
  have h0 := BRFrame.cov_init 100179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 100179856 ≤ n) (h2 : n < 100359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
