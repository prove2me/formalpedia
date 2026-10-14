-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1782
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:39:29.66152+00:00
-- url     : https://prove2.me/submissions/d73b6abe-2760-40f4-aa6d-80461fddbe1c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 320323741 ≤ n < 320503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 320324991 1250 320323741 320323771
    0xb220602040e0411090609061e06030a0c180608010501030518010e1e0d05090f0607050f060109050109050105010c150f0f0603051b01120c140c0f01060f08100b06090603 74
    0x413400c00b0014810141c050b01c580300701c1301080016140d106c0c10a40c07103603044501c0c0d1850103200e40c0c1d000504c5061001e203600004004100000418560008160346035140e485010751142080c0c0c103480b1451501650740001e0042c401007080d503119401250b004890081070b950107005a03140d2500f114606034100d059900508450501a05400b51500702c00b100c0e0f00180464800000c001019881451521440b66104210032a15074032184142c0705c51340d41c40070880341c0025120310f0244d504d100034032030000c006040000110301c400d413278014a0b0403100180c4801d0101ca0f07450350f0340300e04130751004c10f050a480d5032603196041d40c005a001e41c443c40101040001403160850508500341803940b011f0000560602d406c40101c0c0e40e1054220000c6400944e00240050a07048100d511040c101c91030620f461003c1784001344c0c61400b240c240c03040c1c69104020050b0a603103428610078032145102d103100b1074010f03e2030010801c3c0380c0d800007080300000a2481e031402e4100400184a600705481a1811900c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 320326241 1250 320324991 320324993
    0x12070504180510061d04150801050f040b150d150f0510031b0f06200111250302030904150801090f0203121c0c020309030f06071404030b220602040e04 66
    0x681e0f008010b031641d03240c0024090000281d21a060030401c500303a0055070386441c005002074000072000c0290041000038001400c0030400040300050503601a628011302c1070108519003460224402c00c7d03403002d27200446810036902c402103039441c020041c031104c41d00d1b44002043c944161245a00c28510103030619001421030802d40300d0301c603c0803035000d01d10000c01d1092202052600e03440d012500c40c0e14140141072500c4000d44048a20002c1c0814a50b00f0f200c00b408824910300e01501010300802410030f152051140d0903c0c24084c0007201802682080154403440c0c1841d030030481029000711242c2001c1565814030500312002d411f410340300a4541103090085181c1071003a2030220b001c03090042d0070080304440558a6956545000c058180d44600c1600380074000d00170350703030f081d00000c3c195015818034120f002d8441c1001c644842c002821200580030304207840c82681c055942084810a0a5a4441c55103c035010004c407940e818480081010b00050454001880074100c0552560071605003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 320327491 1250 320326241 320326261
    0x10317091f1101150b0703050c100209010806030c15090301090b1614030709090236030f011e0504020a0e01030312140103020d0308220803010314010908120705041805 73
    0xb5041500701e16410000c080b01a448aa1007443c00c0c1c82c03042260f1507441865150641d003911943c8a042c0e4540181180525a84a13542c098440b1401c20b803544151641e92404168944a80700580c40d445001004008601d80c003000150101c0d14026000045504441d1520555003200715140540c000441505980f610781c4404040301c0100380712031042c1075040031200506910030b0b5000b0b10328107550104a4061002c10719039101c05d038441500030303420340c41d0501207008511240003c03014000c1c070402d924000c03100c40522400007034030b24106510700c0400385603080d1406030101400607a404002050003040c4d210109030300c00c0c000c610a8079403040e040c0e41191400d0a07148180b41d030104c1c46403c20010805600c1e0340c4822800ca990500d02401c1c580e0700d2088040006402c00002507500000141c20020001d42800460680e401231540041d0a48009001400d07240f24800081040c2014044c905813400c000c803038141c10903160704045083c03644581000304c40c005101c2649580d80e031545c0611032002c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 320328741 1250 320327491 320327507
    0x108010c050403030801060c021f08041101050c0a110d0204020a1206080a020907051b0102030c0a02070e06060f0a050f03040822030b1501020f0d0306060f05070b010317091f 76
    0x120300d04060b03042c00e145480c00b6214000520407001440340a4500c1c0d0119945c00ca9925642d58500b0900c68410328000c00c01004c80c04219030440301c1a0700491280d000e5800307a010399a80c25555001004002072a5490344601102501002c0e080004205d0940c0160fa035800500074048803543c031140048903030315125050f540d0702c1d440386a49400c0000d03c0383c05a140c8204044d4401d6203401c10360f03038507240c500c02100d2102d6948042980ca510120030310881000d030f107000340141c01081c2c0c00c9030070031b80e103070442d24103202016525250b010000f0440c1d00094400040642082040d5040c0b00d414201351040c408190350088034220741692000440244a0f00c075080c250490300440c404800340c00c0c0c119641c020030310401910b80b4442c2044220700440585c0300708402c070280719101d82030f110349012099002d4050030303143c01002c021030062009552418841d1090380c5000390005001c10492746544c40300c4540e08054401d540340840104200318054480c003000000c000a050405454640f8080c0000d01c414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 320329991 1250 320328741 320328761
    0x90b131a09130f060507021011091008131e151b0201020c0a060213051305010e090a03020706080c040b070b01230a03110f090a020d06050f01080f040309120b010801 72
    0x3890301c02c030b6400401c464511000600b80e00800005840d21002c5040c1d11b00505041b8141c01d640c203100c0a1f81d05020040041c0c070030300381300341e4420310304100e15181910040400c035105007030410341c40d160002180040c0c005005503941a41c04101044217500c50721034109004103000a265120f1021070b1100c4600902100306000a100841c01c16811400b190344403012010060701041e004959100b44103610300340c803401000014508407102c004802584042e10b000d1281408000071503001401c200ca01082c002c4007568140e01800b0002c0c10b154090340c622030080c000343c1920406001c0401c030f140d05040103100c2a4042c00449640d5898051401906c08070000c001541c18a030001021003606d0b6500d4483c203403503025841d0003e8410704070200c2c820b07c440e24804c07680300741404140401d410342c40c2d0041044132500c56080c000c16032581d003404441c0308801000da00040402d4001384141c20000b541c103403c5446403401059a50741c4156808500341072807000d50b00907032400300400003c042449540d04903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 320331241 1250 320329991 320330011
    0xc0902040302180604060512011505010206060a06030203100b071103061501170402030f030a1101050106020a03050406030b010309051c030b0d231903030c020c011107090b131a09 78
    0xc641940d0100d50070500010039581c82c551100b02140ca10b42c0c80ba080500684030180c00e00b1410b801c950300050180c40146641c542c0c00b07902d603a0124181d40f0200d06144500c0e000b910285103607240000c202c0095200404480e2000e03800ca1011451130380010040c500300e07016104003000b151541e4101420400c0281c4903a001c0d6409520204050f41c1218565485501c0c001c541c000c590f0b60350010a040100b5400032480c28040056a0242190001d031080c480000c8803000b000701c0c3e82c071004281e0796880251805004103c050004002c1c80b031203034220b501001411f00d4085450f2020b60307201d0f0315020401e00d01c0d03440b50314001c81074107480340c0c1803081c140c2800c0200e4001c81d030501152200907075901e482c0300245d004080c075066805d128904100d05401180104a107150a010b503080c0280146180400400107008004510741150301c10801a6107000c07580000c0c0c80e05514000140d4010010901c80c5500031a00080055280f10103114a02d00c030b00c20f00c100980d005146004010008900401fa4146 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 320332491 1250 320331241 320331247
    0x8010507091d07020c0424030b010f0b1e0703031e1a01050412290412030612030915180b0c0607171504020403080d0606140405030a02060a03110f0301030c0902 70
    0xf6103500191414810340c0940d00040c0c0c0556090541410710000c0c003100b2002c80008030300100b00440b102d200c0381200c5083c0c404030740868581c40c0c840e00c240700300b5050011700030720101e620241e803007204010502036100b4100012003000304131082c0c001000c601c1c1e0f02c1e50040d0307680c0f10f004520036080301a40080315003442d00601e41401c180c4c0c8825000b0702c0399000b030813004c21049100d2021511070240e0038030481d200301055031071801d440e0050003211400741c0400003038108013002864400503000c403003581c6d51586415035483e04103110103c0b4000203141c01c800b04010512041c0d10f01d0b5586d403542002c0c140c02031441d42e85420f074016807480d028010303002000b000207520002c1c8100c915171406075086221100c1e0600c1005904000031301900a40d000a86180340000740c542c0d5001c441da01c090100d0740d41d5158505214102c00400032940254465290036803c6403034018010729000c07008000c180c0860a00041209501c1422496500055400d40309107000100510900034100704540c02850845801d501d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 320333741 1250 320332491 320332501
    0x15031407020d080103081e030109150504020715050907090f0504020907170403030b1f05070302010b09010f090908120103030818010c0e0f0103110a0207030b100e04031808010507091d 80
    0x2540c4148030140c02118041040b4000640c901f030100071804002d0103803610307035858050031030080c40706c0010004107194110002401c2d00f803a0084d10010342e0043e480741c4c0c00400a032032800c00742100901c1082c0c0f0f40100c0d034021605014034400c81d514070016840c001001e02c1c1910502c8420b45000d0002410301074400c05400c0740b582c0f100302044e801941450040b449000e4240460094080c12442ea020b1403501d880302d015131584403001e049003e020358020f0007a49480c3e402d0050b00c200a004024446801010034040380c01103401280299220754100c0d89007888840415940800a800031000180c01d54140325210b08111a2044201000c800800c01007000160162849503040440f0740906084c92320714505038007a0b407024600000340642d99582d141c0d920300080d11402c0c1408116020a400e40108001c1242c100d94032081e540c2103103d40603251555103099504454100c2c44030940c410724032010605500a02902c0d00402c8a034644400e1182004e40381840e940c4802120000c41200b282040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 320334991 1250 320333741 320333747
    0x3071808122212020d050705090a0c020c0f060d09020303070204020d0c080711031621031d03040806070302031b160311190305030903040801140411030f0a02010302030a0615031407020d 81
    0x103c100d030b030440d06160710b452941781032030a0030040e82c0103035440380419003002080c284682000d40d0410742e035030a0f60343c030100b04010045901c500c0380401c0d030040014485482422040c0e40485091070000301141c1c10041281d0000307059134005502007080036100c81c40f0350540f0390407105954100115060210202c00d41d0001d0aa89000f240c1d518400111100810740c14002e4001c210325a0a20b069001107000b14a081c000c0e0140c41102c24203089007110402036180d40c000441518252000c0902608860302e414008602a400c05000c40d0301048820254001c46170040c0300409102e05003a0b41c410007040203040140120a1110981501d41c000440f40704030b001c0c042000280941c1d06080298a039244e0190940c910b002e02c0c0c00007132044d0710b801140c0e401c950b15081054406c038810300c05070480540d801c090640b03807115072044030425408000603100540c082d802440e403151102c030b0002040b6545418080000c2c40c0d6424020100341d4030020030207200307042d13801540e120310680001d001c03458400c5401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 320336241 1250 320334991 320335019
    0x11d010e1c0815220b0a060903030801030b101508011d010b16031803110f03010e03041404020702040c050d060b0a0e010302070606030605090609010608070506030718081222 76
    0x40c201c54450000b000407991400c0c0d0f45203130010040c20b8108070641d810016030003048111015031060080240000f0541d1003400c0c81c100f0340784e044e0361790070559103950b6135101030b00c90107820345103d00f81c40307100861100c0c0d0580c405000c000c070030354030b1260951501140d1107241000040c2c090b8400000c000511440c40e601c03003101d0301e1180c0700300400288500c0d4241115000032812034918400080b400000c00e01081c110400d047c0f0745d048400c1000044a001018220703084070703030140250341040c0010400e980c03500c141045000c40180c0090b15003045540003d040700c560b0140c1501095002c030f400c502000c4184501c02c00b5100d20446a841c3c01c0508901800040d58000e1550426800184400800c1034a81141d4021540901d0602c040d0402184490300c90340110f6125103103600e420b0303000582c1440000c0b40d1084810141000d840c40d00c03003903411038101d0081c0d00c802454400072800011200b00402c85540c20640c104e01841c0c5441c1c4411400c1c074100ea01c1186c035020020469020300c11140d0140e98 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 320337491 1250 320336241 320336251
    0xb0906070210090902210906100e070c0b040803090f1b040b0409050712031707081302180a050901140103020f0402070f0f200103140612011d010e1c08 66
    0x829640c94034980080f9505606a00203028140c00400d04103250305400f00c0e100c91003841496031500d250f85110701d0b00d0b80d4100460394030301e95202e040c0c0e04100100c1c40100141d0000c0c40c038500302a2407281c584501f01040000e4604482d200800010841c0340481840450325021040000d880b451107400b011501c1082040342d034a01c02ca031780d0b441c03d0901c3c0d50356070f1141519a034400700341c402e02c90b44ca140905d10301082ca58198003040c0340c0200440c00702c64807421741c0d105a0b00c0b038840306031644900642d031030032560310707c001ca03001003d02ca64100441e2803200000c0c400c03017403464089481d107004400d003800e4688641001d04508110703c01840184c0d24488040d0890714250b4005840e03100074203000301d0400d503110307028041c80700440d801e10501c0050716400c031015283c4106c107405402d0510045044407450170002e01c041e0003410210302c01c0c2c64815070801d000a00e4800124100c00c003e1076412941c04004000341c404d80d51000c46100c084e505200d15003d2000c450501e220340e2a0b840c002070030180340104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 320338741 1250 320337491 320337499
    0x1a100602061b090d140c0f01050c071505070501021215030318040e1e1011250501060816051924210e010506060a1403090f060705130b09060702 63
    0x390100d0a0344030031000c1c01c0b01c980c000486170f8001d001032002d69122030203001d4460080341c072201014225401181100c070b25030000c400a00d03819140101500d00e8003c80c0d00054200070341081407801161090002d040ca01c065510003001a080c004242c4860080d501100c9000c0c0d001440304104c2c444c0310034008580740c0d4050b18042582c00342d055446d03040404080812000c240703050026400c0708000681040303495010401040001840c5e0203050042c050980615038560f001103010070702e41c0440c12101d442c06d1040c0700105040e500d0354149400d0040a020300011008203000400c4a4070741510088410380390004030b40380c01c60404c92041c400e410a03001440c2040103410780c6014007403181081a0049500304421010240005c040c1005064030118a03c01d030740c01c000214541e4541a0122182401da41c0c5400c0e0722100d410040c0b0071075400042090300c040c0038000320060107820070300c425840b600d000e582e40c1d0341d107081c1600350000905007504240e40076842442a94015203885003110724264041f9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 320339991 1250 320338741 320338747
    0x61903020c0a06060b13083c010203010f0f0915030f020f0406270905150c0706020307030506010f02010515010e0d02091501120e030904050408130303050c071a0906161a100602061b 79
    0x81444030715980545c400d00e52320740c400000011090034085c00e80065032045406035214030758031150002030b0340120703211002d0600c41d000f00b08002074901510822092015100c00100c6441d107002404860b0623500c00030780000305810042b20291258642184202020030402c201016a19860364030608a09048895044100030402c44408034044c2c3e012075600071402e5541e407030045d0f401406494240e500c640800c0d01114242c0314540103000340d500c90f6802c900840b440e0760700480115101035501c4800d071b8001c0f0001a02c00050303100c03034000501c901e032180c01014151041c140014038200100340c4100049182c0002c1541062000c400c6844944c0c045401040644850900058910a1076006084030001d00340c00070030190040050702c5a04d610400361a01d040e6103101a1401e035000580740080b504003000812000d02d00b44000e81811490304a824000d4000e47d9248548000c0542d220486280d1880030448941c1c00e1259610282401c3e102030103450410f83c400640030b10902c820f51407000404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 320341241 1250 320339991 320340073
    0x501030b0d0c210f030f09060f020c0105030714070503040617010806160e1e01020115050a03120504030f03080a06050a0e0402101b0b090606061903020c0a06060b1308 73
    0x1801800005600710402c1300b0329440514002d030005074200c3c00b50000c00c60324440010000d0140c440c4050941c01e90300903040c0070b42c43c03200444036940002c0c840c1c2e00303012a84e9040c80403092050f0141000340d1040c4002e5580d0750602001409210100a59800d01c401100040c009940049002908100425448070700320b102d4410030398a21918120f820f8000c15550440140c400c04411385080b400c0d4280c0003040100c1122800620404040c0034060700920712800420010300c1c48034401000032070743d1a101382019142d54a0001c02c140e50321080c0c0000c1c41ca84180000215103220f400000d14080743e0030511246032812032000c00c04024400b03845180c810300841c25031030080e01d60306d010310101d558013103001e130651915480d1180182c412010034401e240004096060080454540c964400c0c22152042038040e4101d001c0d602c10f4806820318096800b4080000e4128040d40000c1d007a00380c1c4068031407101c000e2151700c626090f40214038562000e0402484050654405001c0c08a138101c0c18014003c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 320342491 1250 320341241 320341289
    0x427060902090405061e01080a0327080a06111c180804090c030e0705010e090a11030406140618011806080d0306050a060203030910020d0e070801060501030b0d0c 71
    0x10404040d421600540c1000200000402c0071072046c2c1809440a04c00c885400d84c070409070009019226032540110078080c003181c002c46000302c989488800c0000701e40c02c4400b4440c04100e503a031000f000756000c0c0c0c09000400002e4043c0a40503012000c03028104102100700721000361071f605107100120b685445984020303884070742c41071519400c800b240395995a200095801020858034410009141141c00062203001080d14011100140d66402c03200075044c0401c240d89034043d1030151001d0ba04c0c00e201503088103810245100b10b02941c40002d5414404d03441100f0b0090040a0a120b1182821100924071810040780e0640328510440c0200d01700605000005126070b420140641c4640e0104000032645500b2550980c1c1041c0d41d503841d410340c0d46038181c1e501d00040c0c0b112109a04000940030f03c2c1060340e030141000079104e0b8400705034042003200381424140b5640089001d84d444000610141d45c041c02a20310820054410700c8041c000c94440095a021502881602070794107030b02c091000d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 320343741 1250 320342491 320342501
    0xc0501030e1e060a06171203060105071218080d0903060b030c041118010c030e040902040b181b040303050f1e0f190e0607020d15020a030b0f042706 65
    0xb6a400d4070309031044024507a520812501c0d43c080c5810504086038440c000c0062569501e4504001d08050207141030441c640e400082240741007240c10b01520700070a1a4200380e00c0705100540b988200124484009601d10199404c41d684a03440040000340b403951001003a8112a002000024514200c1c4002030900f40b6a080072a03025080c800101c800320341e50402891511800c00304801070a07203850055840041412000e408950902104501760825400c0308095a10044c0001030b80114000003c3e232a07401c40c0c901d0100c0d0042c5004122558140d6444401000c419200c900c1c02c052565030001c0007840b541a042c4e03d0100007113107404800c05051641b09844115012581c0c80324084072481c0055044440c400c0f8081c0e50729040c00208c0c1d80200c403080c442040c058070480c542a4141c0a1114006810300f04036494504a1804c0a070b94989201070311020403981d03000300d00340441d801002204820380203034a105510308059460041100d03500055100d013400c00e41c030340101d080d00b8801d000701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 320344991 1250 320343741 320343763
    0x919020c030a031506030e0d0e03071d07020c0406140d080c031903061401080c09210304050301150501091a0702030d0c05060f2a0d0e0a0b130c0501030e 67
    0x2200210b81101907507010b820a52081c00909040c10159a903448101d00747d8505241c2110107401600c0d10601e41c0d8480c0b0110001c501e8045c0403982d83c03641d60306102440041300000c421114051105000282c1d60500c010b503035051007114244052410400c540742d40000d550b605511900000400000300540a000d8690780d454030700030740e900e4150200c44820010035805040d8000f238a45080400c00040342c6400d075440d840181d66103941a506c00e494825580e00c902007482c0e001190f086c030440c2c2400c04048042c4510307040009103859615010078142074a60072a207034464003241540c03c1c086a40c1c024058021500c0351021900c02042000900d005407280ca00080d406005845120103201e4122015850840c40b071000c65003207981710300d80a508503009807000522094150110041c07054032010400f00c1c1307440d00000781d18103a040c203400300c1190851001100c0741d030000b1103420140000700c081e0a40c8030800750500395510201d0f40d10315421403124050941031664420082d910070104002c2d2488503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 320346241 1250 320344991 320344993
    0x7030c05070303050702210606040c050d150f140303030604051e01031214031017011401120506011703040302040c090504020a090513020906070213090f0c0602060708060919020c 78
    0x1e1622420300520503808004140d004130040c0d502d00c01c1e00c04804061070401d611308401f51a0603110341e002c0102800e4080b06503000c2100c01d201050560406201d92025040030743c00f50500b05240c01c038801c519600c10b074041c0d141e101400105c04140d483c00300c1220b40c450030403113001809aa40b03c1801480030030b080701002540b80304400100c1081605c07030f40490340300a16221000c0d8444601c9490440d88021610712290240804d004c210100c034003500c0b90300143c1c1b954004210907980d4a40003400800036072111095614610044041c0501400320034090820341404a070241c1da6405001c4ea28421031100900495403401c140c2c1da440c0c8611400390180c4002003041d941c404548030010000c500700e00686101d00701a182700d0380310744a40d2085544100303000e0305280c02c15409400700100c528001c1851022552503141c5d00d40012811380001016500c2030110740c03280c074100240249000c200800d400c040c4540f00d400e10100395594041282d000c6c4100000c0386440c00c241034018080c2c003406c40a4051 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 320347491 1250 320346241 320346253
    0x60103030201020d0f050105030a03030f060b071a0105060f18040603060f0914061b0d02090d0b040c060306050f060d1b020c01081b040611010908070b19060e01090207030c05 76
    0x105607041d00100201c06065006002889410001c401195020301c0340c541d15a120010b0000000c2c00703908064401c550641c000a0f0340c0c0e40c3c84101d89000d0b449500708a40021810200850b807540d100042c17400344c442074803001e04040b0f510001030401d11a1001002602c01c5000c0820030513980e980015024540c454014061042740407002d001603c034042003102c021040e059a041112000950385116030362112100d4426010909184d005a10410710140c40d15000c220b118010348503040070702d00b0144a84085d0b0500d18040c2001040311310b054108504150170300ca02000700399504000c1c075280f11021a041503444042c240b0040c0140002d85400244047c001404038903940c011841c018682d90030780301e100480d0340d00c1100542c44062415004122075040c031060041c1ca11a180c80b400c0d10500000000e07000e5015180c11420360014601115020f080f0300400141c1100d40f802100002d41009007031101c40c1c1800488582c00c0c805004a992440e80410748800b031500c542c0026020940201c01e44007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 320348741 1250 320347491 320347493
    0x3070305161e231b040e0607020f07080c03100203090a15150501030e0a0314040803031f1e03060b0d0b0405030406020c0307030c050d023010150b030c0c060103 70
    0x40604280c2a09440e90124003c4590480401042c1401c0742410b841c06001850242c014030000054203284158110b580c414070385002010400c4064013907640c0c2e40081000c00e4495401030700e80b1031503070071440181d0081e41e9512030580380069801030b620300d403600258482d0ba4070020545403152506001c1c0c00082900408650003c45500c0603000380c1c40750050084194a840054003034440070100c0003601d40c804910400440e01c940c071400149402d0300d50891400303a844038224070b15003050307440c0703002c11f07003203d8100258000d80f8000000401c4100c4003c25071900b03040002010784504c2c4405090152509807550a5a03101007503141d1840d4040b00e002c44608090403d1652500180585409845664500c411501c1c0009a407021241c0c800385654040b403c0005006003038001d500100c0c0c0211b02c110148201c8080c016001000118200c44400d0161500116a2411b4007030059102d030380d0700d41060108400032400c0b15100741e0701a07800160303072500c4590717030400c4921480c3e6119545002d0000088 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 320349991 1250 320348741 320348783
    0x807051014031311030d08150d020d03050406090e01061e020c06040b03010302090f090a060b0301020d0204121208070e0d110406080303041a060d030e131e15080307030516 75
    0xc0001030182900c20300181c1130308141980c0f102c1c6c042c0d04c03c010403080b20005007090b1011000c0c02048030083c140c1259284c096021a040081c8d1840803404540040b80a02566910080361070050543c8610a100c6515050001d040200110124130300780201811108041e40201700c003401940001c0d050954440d51030070064140d40080c00200d02c1a080800840c180c0030550069500480c800006010740d04503582d1131030003c04180740c2c01074042d5001c1c410003800b410341e840603000500c5201101c1d40350603030a00e03088982d4100e10035010b00b4000c0d9a414070085580c003d80c04070302a6415034414409480078240b8203070b1a50254042c580c01800d085000c201c092000c40510f02862041c44000c1c50350000b4141886244422aa041e4108059584200103e171159a500f08412405010401460400c00d00c0e0801c0d190083c0103291121615941519403c00c6881401102001c1c803480e42c02c0c060825640310b17100c0c85040b401808100700822400025415405090744480d84010540d8402038014410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 320351241 1250 320349991 320350021
    0x7060e1608070602190305040501080915041104050f0403091a070c0801060e070309021003020f1606020a11010504020901031112060109051e060d02122409070f080705101403 76
    0x10030040c0101c001d6851266444206950090b906d51185400c207411b12004550701c0380000c106100911503006111103890649410502507030180a000003a02c0000043c002a06c1d00508402516a4990f0410000c680c1c0b21800405940040303001c21140281040000b101d07008400c0040d09140040500188050341544100f04030380c900503840f200755540010940869a54440203500450140c1c985e1003014403950082c8161000b4581844c1040c2140000044400062400311103403980040d000e0342c600d80010400c0d500d845140002c2c0590b103459030100303600d0350046c4001001043c2c2d202c0ea440403a0307035400381d9100034046502102d0040d079403021420041c040554840e82c28107290fa004031204942e40c00300703610520b009490883c0081003542484091090918514090f000e01004409a07826411000309a0705c1d66480944c0c0c0740c20101141c40c1400d0003030340140c65000720f00c08104144440442c112007190b1040791184011001c00e8403c3e501c04a801c102c81403000b80010812040310b506144c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 320352491 1250 320351241 320351249
    0x90e0a020f0303042312010903020c01031d070312021f05060a17030307080c0d020d051e070c081c09050d020d020303060a12113006070507060e160807 66
    0x2400404100d0001032580f02e220b1405032640011082d010750f090b00e52078401030b103903100c006020f20440d0070000c00c42c103013140c002442c22401a04072000704446e07507a06004a041c111401428101ea043e0741d5640e0720340d2403015120040c4004104103202c13126900900103032441840340c82008040403034140000004007403c0728103604c03c14044201241480f440501c40d0b00c101d06440003140346440e005000e459800008180c421044010826266190100e002400b90017000c242d02041c2400c00096811031500401003080d151030094003084095580a82040c43c055009841985c4c0c401c0c0043c9101c85035800030703404452850034a0441010800009081c880d025010303401d07140c641120302c1c000c986920050781c40795071102041509110355804502c1c4803d5407440b0301e490101c2c0035041404101c01ca21000b68480f01e00d0201c0000404420b10621450104034083c00500750a2900304000703003e034001c01001415023691030f000030a8508040140307418101c0c0034080b460710f040d0380d014219a11021405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 320353741 1250 320352491 320352499
    0x1080408070c24020d0801030327260d090b160609110310200a11010e0a2904030507020315041217010b030c0a12050901020d0c0c1110020106090e0a02 66
    0x59101c101910220741700e001701070340c2e40e500070903a4650b03217048071041080c0130041d108255400118665600000f400001070640e540541942002000108000c1c0c4040041c080319402262070b070707601030f82d0111600094924104105d5152411300c1a44c1d41d00164000000305420702d0401f05509100411442c0d08580d07404804031580c480f030302101c400a40b505804082d1000f01502803030b1440c88510b80c06080f901a01d1700c1c080801c06101110707203081d126803120201a03500034190a07011300019080404421514446246002c440752488000c92007004101400b00300d40843d064085540038000c0c44030914015643c60200c0c14641800215000f095050f280414080c2000a2228507014001f038100c44140c0d65540c01e51303130b640450320b5080c0d01880b0b80c075041140c4a0300c0e140035000030784103290003007240200058a0f00186841c440840341a8040c2406000c103500c1c01c90009151000c024110402c103884555141c00255016405040d45400c00951a41801081c400c0071100080a60165000319 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 320354991 1250 320353741 320353799
    0x31e0f02090405060d150f1116050705060c1005040c050d0507052d0f040902220f060803090103240e16030506060f2802010e07090b060901080408070c 66
    0x3c420401404174100004150200405c03041105042c15400410400310700300d030219484800107081192a40015072a1601c1350f014502c800500604218540240c1003e03103150345410b900d8803a5543e00c100300d00a241d80c031030702c82000800700801030801000031702016000c0140c6040d90b18001d520340c13005006071030044007008802c00400700007400b40c10002a02002c80b9403101003241c24402e20b104007080d034540141c2c55a0387c80d001a210b90040556543c02618421002032201401206685529800c1d5035101c0c2404414010340401004540709054242000038105080100c259150031051402a40841d031254000031040c80d00154a4032510300711400d1540c0c1030300c083c001e80840d401642e9082e0090000d02c030601c1d035101c3c080020060150703444891102e030340d1860101c8006208406203100181d45a084034003220070104008000340ac000c00d03003400916190310200d0b001d80909510a41049a11001303d410b11000d0301c202c0c0c200036000151104c0054171060000d8554081d020200580a56030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 320356241 1250 320354991 320355001
    0x92102101b090e0c0909070c03080a060e0f09100f0c181214030f071104050702060f06010f031103100302010906050a05071401020c010e0d030c020a0210031e0f02090405 74
    0x1800c1d903000510701c0c0c0c4038a00501d040c0403800d90310b80742c024600d0029050410240000e580da00910320b102c2c1480e0b60f41c0b200050000d03d002042e0403000f51200c20028101001842115011843c66520a23107510710381016580315100300d49006205a24862824601001144480342c50b40002d1070342c08030f80d11030010081c0c120340e40d103031408014481c2114000c60010441c00040c0c58184401014003100c0480341880c460b04003144d002c0d401000c0c100e0b20190700c200c101109050600a0300c0d402b45503030001d0152417a1213a4100803400c0c00610590400291600081085000743d00207001c000020044c40d07140c0c86c210080402180d000d0200fa40400c580400014640f403140040711175600150752103904100711a0341da9917078500401074036039241d50288100040f039042449201e026600c51001002c41402031000502251052a41e240454200d0711042c405a2500548200341c08510b1800080c2640c428008000b8901c8480304034601c00e003031400018002c02c0c641c0181000c131008540410140e118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 320357491 1250 320356241 320356271
    0x905030c09091c020a0501021305011116030809040e1f141018020403020d060b040e0304061704050703050613120309051c140c031b16030609210210 65
    0x229004021544030000030720010380302c1030b00c01c803c1d4015070049803081c01040e612182660030501c1b00c40450140700038100110f40c4d00c0507801c0341c0c0d8900500900210091040c0b540c420fa4030600024084601c001840405500d85500c20002142d091041d2a20912845031402d1841001c150580c2d4850509100074542054520014020b02d0112140421949081012502d036050b80306075a05003607003400b000001d41c80d0503500070f400d2803042c0d0300010307003680700780c1000b08844103041007400c02d0f0b10a0000748149500021031000180035802046601e54592500c14035100090308001d106020300c0090001400b15503510f0080140702ea5124a0340401d008030440c2220718280c0058103d070b1201c0c221800000b80c2004103100700b05107180440f01c0b07504401400c00d00d5884040760b005113a000141104021030312403281500340250b00b016060344201d55000c003443d4540c0780006000d003a030328403402007080959540200b12202d0444201d2610003c041c2c040c0d11054819540050241131540c246003882d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 320358741 1250 320357491 320357509
    0x915040902070b0103022812050a08030a02070309153204030b0f06010c0f060903020f070b0414041107020621161d13020f04090e0105090d1103030c0702030316030905030c 75
    0x141d08180d10000da223081c481c0c0d80d0001e00301e0025500360280700344034070100364048006c1d480f4625295025a079111280b400400b0600c550b488800014070201c2c01540c651b911545000750b4000c903181400c5865030b480d50a11884414038000e000140300010000100103403451100d00c2102822011002270b40d50348015110080802001000c0c885969442000158541e0102d070300345000b841125a05042c0144c0e1620b4020030390046000c1c0c290101d4200f00340d4107610441b0365084020746007404683e0f858900c0034002d0003008002032185101141201c091848101050b92103503070b002c004070407030520000d0950340e28911245180001e40824034411180d00e1705940100c000c80141910351242d410f03c81d414025000441d08024031031081000142d2041c0500580f050700e04142c00010303070b609202102c80d1a140440342d25800f840a007800201c202c1e00c020081d00d50044c1d00d221605e80c0e403400d030320029044d03109000d1644019a1042640c000b03056101100303a0545038150101c2d048280240d0410003142 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 320359991 1250 320358741 320358799
    0x20303041a0903070803220b0313080c0607080103060e0105091506010c050303010306020a03050708071d0105040512060402011b0507090b0f03070e06240915040902070b010302 77
    0x260080204000c01014645200c1550908403201030a0072400c400103402c1482a500003842548046603200000b1b0545401c01c0c1680303405061240900d1408100d4002d50100074462000342c00c500740a1000e00c00d001c000c0740e24035480134040e54400d140640c40070300040403e00055039018039060038079614950501c188c3d8041e0340020f00621003c148507d047c44200d01c01040c0034104041621040d00003041080650302951003200056210303412000010200e82c0c00401d80000c2004010038010241c3d088040964100780c03410290b10142200c0c0016245072140c0d42c4441d070424840c041c511030400002c00c4030b501480c800da0740d05040d208180e20600100d4030320300000d000c580024904000c044920f60020f41d0101000d00300c0c0500b901c400c00024100145c40e8000012407030140c0030031a0625000000b40ca101c00110000481c0c6004185419041d00039410800e0045074044214080c3e03203410b03000e88008040c18542503540c2c1505181c850b940350000c0c48100c1c0956589a031030510300142400b40c100315 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 320361241 1250 320359991 320359993
    0x30b010824132a180c080601090e0901180302100c03060f0e10080a0f060605090f150a090e0304080709051b0d1104170f300903070306090b130203 64
    0x880c0c4a4650414824030040c1c40d0003151080d03429004400f181c00041d20062500c90844411410b180798400107a500e660043c0040040c4002000010b80c0c225101005403070302019140c2455440498980c0144480b801b5071039102071074030921f0105540014110194003c84c20180101042030600b58161410381c05818078010100e1020b00c81c003a2807858a961241001f00c4140d141d035034520303d80c0d0610890070300a45401c0d03907000b582e034240070184c000c00008003819501d482c900e1a01010100f40f1050150011003041c0758620240303000c0c0c1d2010b0f03680018003000d010030003240c111842e42079901e40c0a84101140c600414030b0000b9010882d00c00c40b482100c00744010f0325484051500c056040c0d00683d200c003030903035840800c148400c00392406080548191008810f43c2e41803207460920700310b8418800001c903071000680509081c03d40c0741100c80185401c1072003110607100e200d0b121142c054040c219800d40b14402000081c0407082e00841c0711240160681c940d161070324492840101081d010103909 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 320362491 1250 320361241 320361271
    0x207050f1003020d0204030b040b071704150b031515030109020604091503290f090c0f0a180212060303040303080f04021807020c10050a0e0907030204030b010824 71
    0x41424250724800281c4854a8010f280a642402da401241c1054100ba00c0c0d0903480001c1208100744600c415800000e2030a0881d103202d2042511074100c1002400100800300319000300066103006d402a13054510000e003620036200c3e01c0001042104c3d03048902d203208440d401c0c2c4401c002e003030606ca01d0350103e802410261030141003209100190541024075528414168400004283d0072102c090108882d0840c01081c114200084c1060f2200034080020350041903040c0701030500000783c02001010144c03018048c40c150003000070b1f6060b03801d0340152000460103944d0074803028a5802060a050110301d001e842c0c1e1591f806041c1e6074040ca020007030101d041c010204a040803004039555216100400c2c034030080c005041081940c000607281000583c2c8240050100d40c0b81c04d290032120042c2c2c0e890b1041c144240000300900c0003810880e6a4040c5400001292100303200b0340484000e11381140050f61369503911040e60750365007000c0f2210844410302110f802081c102d20100580111149496502 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 320363741 1250 320362491 320362519
    0xb04060b0306060c0c0307030f12080c0d1d10020705010c020a03083913050105090f06030a15060c051c0f030b0109030c080106060e03010b061c0b09010b0403050d020705 74
    0x190740b04038420180b500c101c40805d02e01d983c0800003200958400c02c081e20004490349040455020040303a9041440143c40030071a04481d240156000001c10340c2c3c0116103012500510003440e090081301144500424078880441c0c0c0d81c3c0d40081070280c0c4030b0741c02081181c00e4120226101c156908000300092030100124a40300f04141341c40d140b9500e10a0200e2810086500681812081103403204000300d0115400c0020980e92200e10300400d42030815600d00300711140000c05403c410420148942c8022012603490b8030650f0125a841018a002c04061600c9641c094410010000e08450504c100c0120f40d01001c40b00a441160224a8039410000f81100d0b2081e4007403c3d50202d04c60410844110000105501c80c981000074a0800000607129003000801081106194800c41c003a80c10012070000036243e4104607041c0807980060440308000440c5c2640c040c04112804075030200c1010300100d9140034820041044034400c004642210b0f00d00311090741c440f0068404d40da408002104140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 320364991 1250 320363741 320363749
    0xa0201050f0309070e04141519020a02012306150c0319020a051f060b070203032d19030b0108040b0c032a0a090e040c0b13030515040201030b04060b0306 67
    0x41e0850501c0c0f00783d520094030f0f8000c00f8502a011079040c0d8900410300300d8a00602c00038054101090716204164504d480c040c00501c0a1421040c4020400d5070b001440d55803052003980300030340c0110050301182e1440b40b5440710040c0c0c2078045d18034a00c0340690401561114003c0011250f400040101070360a00e00041c01d0340140151810010b42580611408007000035000d10104014440449207548420400758119089481a1b0402c1c10a07905c1000008096a07000003a035410180c04000000400c4555440281c0110b410040600c0c1c0f000128404e0702d82509001e2002020741107660400408070b030100110740504042d01e0280030012444e0100d500c400c0e0600040d80c3c003940d022044104041d101c000c0019910300e0036540d80e45c0140202c4d19080d80c66001404000a01c1410703000900d82c207054503180801000b52150440e0720100142c080c0640310f02641580c015a00041910b880b90713441801c20001034801c54040b030000c0d103400516001490184142c2003683c42c242015820360380c886042c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 320366241 1250 320364991 320364997
    0x90622080a150c0c240c140403060e010e1b010e0901141e0a03030315050405010b030c0c19030e040e0105090a0303050c0903011814010b060a0309020d0204020307031406030a0201050f 80
    0xe0f07082081c407000c28800300b000a40904100c0f919554052504400080c11008039031002e00200100306485000781c0b820004082aa825030790441da002940044030400380380141002e24109040f80100a80d5201c10a070004001a0044080e00d81e0380070b90701302d402003188400d024000c281c00000700100701100341c00c2c001c0d0014800442c00c0340c008290313401100098000e88144c0e00480c0002d03180d01320100035000301e0300000000e00301a20184080e5040909445060000600000400e500840c03603e8807550108503c0b618442e240440c040000d502e8100100040308084160b4041c80c105101c54401520500c501407240c000030015290441303955504030060a8003420100c2600d8050000840b0b0340e400784915107100011728114040b140e018a40f90144a541590b0128643d1400400e440152248422619284041c0c03a0016040361036100007a9500d4801001a401c140b003c0f0400c801660103a0000c850031391040b002c0c491590716041015600d03100325400074005070050103000310000d005405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 320367491 1250 320366241 320366261
    0xc0a06180302041109120109050604020d0c12060507030b011701090207030e030706020105090607020303010e3408010602070506040305030a030203041e05010b13050f0106110102090622080a15 84
    0xc0364159650350006400c0d21100100c99a04080005414120b481d126a80340c050001d4071000f804080025202c5503100c007c0140040e0003800c0030303200041041075050000d006007070081c01c207015444a5040c00f500a000c100c920002003440d203071160400d58007444228251480260860a5503805d1a2803580071350440c0701c00328180004140c185c07a507a075081c48944060300849e80001802e140c400c1c0020b203040302c003a10503815900100010300c118000b00c051158007141c55540f1030707606034400c01d520707000782c4007501c03803280502c5001d42d0301c0010b950100ca5a81242e40d60b03400ca80509440303004114491140d88801805588200842040240290087d6600038022540007458000c003480032201e00400c100121220707551207441c003c1c00d103014042c035242050007407000c000e07604d8055a031003581d04060003180b0a0004102d0300034001c400940441300c0c006006000c0e0f548903130380103806c500c1080140d138101c001351000100c01321b001c00000800710239a5812111002c1c0c107042e40900c5000814030040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 320368741 1250 320367491 320367527
    0x60109021c020706020d061e0501031e050702070e10061704030c050a05060a050a0504052a040914060a0212071b081803060f071d2404080f0c0a06 64
    0x180d4030039070110342c03001d44400c40c015640507079107058028058040382c581d50031007034601c1c1c604540d29007600b500c60401d0301520001e0a0001e4561880103100300d4446407020404c01003030a0004002c45694040b030340c1c0c1c0c02c4800000b0349c038401d80c50700b40c8481d5a4110034000d40c00003501c6188985070081c80e1526940d08a8060308200340746010755103034103080800c0c0781c40550300703039002c03000b440001885131190640c0840354034010801420541c0d500d0b611007184aa41107264a082401983c0c074134494105520300040080c4204103608549c038001d030b0301c2c00c0322000da52000d001c2d040024030b03440000e000300e0b40c043c0240a041ca0039980c0f9080d060fa40400e212101c4a20319028220243c001010700000f45500003100c4c404d610207114200805162403401005ca8010601e0700040c80407a81d0810841e039002e0700511641e0404100903004076031116560041c10f15070340020502034a1160b4508002c0085c1e03504070b410750384140c3d44c002c02160798454910050380c1202c1c040c1410402207200c1c136525007011402030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 320369991 1250 320368741 320368777
    0x2111031c0b0d0c152604060b0114030a0905010f06081c09090612021c0302070501110f0613031d0105040501050c010b0a08100e1f021b060c030a0c0e0306010902 70
    0xf4450544030900c80d001302402c45200084800d0345034120a840c5580802072240015012024941060128000d070000306101d880d980301e841580e00421400b2448114400780c030b622440d09a9650000d018100713415120340d480c04000c82e0f0744202d1802402d043c0d82c152001422a140214030303c500d40714915454004004004402060041d560300484005060f0b05d11a501c4a4001e03004000c0c80a0f103908561180c040c1100700200000d40204401c01110000d08008442d4202c001c40b060408500d200414428000c40080105160342140d141c0103860090740d8042014880000040c0e003408155840382c0030030b0091100300143c0d8031800040c131070300003600004114000c42c000440d080c50340c0e076000501e02d03820007101c0c125828028420514082040c0000741403404215444415a04c2d801400908d41e81c2c0001e409420007503840f9600303a6003460102259042c2c50300001403100703a0003d680e542c06180c28410620495449000c1550b40e03403a00038007510240c0d1800700300a0003503204001c0307182076910003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 320371241 1250 320369991 320369993
    0xf020111030c010b01091203140a051608070303050105060304080d020a0e0316152109060e07180f0b060a080402010e13050a05071b0f030c2111031c0b0d 67
    0x900191240d400b207207001150380b100050015001c021260801d41e0390030207895200300483c0e4005200350307117000c805400581c1c40c03c00250485581c80742c3d0a00c400441c01191941d010440c040b030013000150f0181e942004143d80700c0301003283d207101c02c0d80c1c080c0508100748a1244501e01c01d90080803c80890b081c240c400c60308820200303040c10702109804d560140e10300c0081040c51303c40d000d0b18082541c1e624002c0500c00b000310040704110044580616010f03a5518024100f01e20b80d80700c200b40c804844122024160b0b60810400b00c5607106040e010b095041c815049800309541c015850011002410541410b43c40c20049a5401c1d000b003007a8104040f08010f00d22a898000200d088110340c0c4c88080390314a80214491300740c0324003400c00c6040001501c1e00c011450940908655010351001076040390500c0f600702203500c85254003018205000c000320481c01c070b210b4010020303904a5180c840407100040c00e0360141e161b000351364020704880c07810014410042a580d0050030000d90041100081e03040c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 320372491 1250 320371241 320371243
    0x100f062105070c0215090a03080306031002220503070e0601032a030b01110705011b0c0905010611012301140411030702030309210406120b0d050c011d060301030f020111 74
    0x107650190200f003c24880c0d4095040410720707680a1003064000c0c0f8900019200401c02c000d01d02d200142c0300007408000328180395800d0084510003501003406648407007506c0040604038148002c17a880820102e41c0c009041d09012a2600841d010400e480c619030362800015000341c01c1081c42ca04400194190f1491440c0c401101c0c1d110040056800080000b00e1900241c4280d0f03000e80012080d41c820641000a40e0f03129105140050003041c0e050038074000340c54031500c04030454110005a03800e040002c00c000da48006071410007440c600c0240304c0501c50050303110040c402440c2c24040f07204407200502c03010240d20a01c2000b500068400105038a6503a01c00d50301c1d1300b0545180005800000c140700c80c0d4101042288803104a81084a2a49908510f008982d208510410050203043c10200203041d40ea5444420f08210261184030b60440911b0700f1034075a43d048100314041030514a1744202c06026208043d001c401c041c0c0f132140b40d6421038480101c0008132003070490401c001607044520f4000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 320373741 1250 320372491 320372501
    0xb0301091704050112052205160305061b03090c0103020901090e0103060605090601050c0309040b0406080d110106141804020d082205060a0c030c02030f1e06100f0621 73
    0x1e40c0c500c6551200c0c00c0500050143c151141078400481c142000c5c4404c1c0c408010340380301490841d02030009116054a01182444082c0704c2a01504505c400d00009000d00464203078072a0000520640e101c25003445074024501044d50030b0400d9610800890000d0350190303005121944050511901c015030300c3c401c49415a03c241c204482c0161554010000b40c10050708a61300322409007041410a0900c1c501617603a4080c1786c9407584950303104d40907051a42c80ba5403220000c2c203886015902c00c1b0015080c041c240b800f10f0590450302d9860141e0004452082e600109040c41e40100041e80c0210440000305100710080c10a0783e01c03c070702d0542c400015412070f0050050801c00d4a082c501c80c0e13004c2d070001e56a004207074002c600a02e400c010004126074001c40407690305034103041c1a071071043d00c0c1c0003181c642090100c80400d0340c0b03e180a02d00d585459040d4907041a2410b604484c00d0b5a21824400d8105550b84120603031844070300b10601c034407409540000150b0801098908918215490500660b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 320374991 1250 320373741 320373773
    0x2060f0402011218020a05040203070815040204050607060902120705030c061e0307020d030501050d020603040209041113060f120308041401150b04181406040c0c0b07090602061312030b030109 84
    0x1501300b0303d0110443c05c105036554000c1200300d4007141945401140070700b13070080052010084548012025005a9a950558002e03000c05010b036038554000385031020052807031210980c8a440a60321042200754000751130010303210b0203005406003009003030900407a900209101e03610416800c101800c868282805180320b01603035801408401000350000d800c41d00c042c2c0201d4050515041d5480160302c3c0c1c030b012250000e6041d61220640d036110300b0035201c001c1a1040c8540e0002d484100c05920f544160001d0f019100c992540d5070200390390f0015059010444000100800e14000014003c5400e009510392404506000407540c140d541804904001c890340140041010104060061078412685217000380100e643c1001120145d4503c92000a40144841d20540e110342c41003406a11030700132100780591005408406007001e08020f4041201d40c000c00b030041c401c400025101051008001501681000c02c00d1a10480004110060300c90151010303099900c49000301c00045d040c1082a84075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 320376241 1250 320374991 320375021
    0x5041e021c03260f13080c01110301150305010e0a05060d120804060506031b150d0e01020403030f0f0806011d03100b040507090806010e1314060f0a060602060f04020112 74
    0x412030800380d64400c020582499400301c3c0c114400c00c64404400a00c00750410b4048884a40d215054a000ca00030700c180a1a0f1015500388031003480601622002303181602c211385d000d07542c8600740707000c202d046030f0003486803010a076034a0300850459412030340550740101c0090700104040c2481d413550400500da17440c41a000a280b10208000d10219114003508441c0c103d0280c074014101940c61002845a00c0d03050388100440008542a0003146084451142e0460014010b8a0608ac08103000790000e100980100e0851f514112440784200d0014101d2040c54030349410366180c071001100c4e0301440c0c07420140b5004640700000015071301080f0441c0b84180e10500070800f04d04a01c24003050311005460300050154004090007007400c0440c101e41594400780038856180c1d00c0d540d600c0d035841e84c0d00c1d402401121500d034107012141c1010a1451080c11a05c03011a40740d00c035402050102d03081d500c141c40060300048041802e00d42940821500140145808450003042e40c80007401ca480ca03810394204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 320377491 1250 320376241 320376257
    0x10b03030708030a1d1f0f0e07030203010b010302040b03010b0702061b0607031d0a1707020607080a020d051c1a040515030c1e0d08070c03120e030105041e021c03 71
    0x1030484a0302501c10000c0d0034501210784000c020148503546d010340030008840103400c07092400010b0107540100b00607043c1000600c40c034012900748030785800850206900070750074003565920650080c02140c0c100c801440240745142c0ca48100102d20343c0000b42c0403640300408004100b80d038034281014000704030010340605030505140601074129190500c44004510100c0041510b01402082d820790840e0003100041045002402c3c0d41820321451800940c0a2400710381c000911110a02070408034032170f5001c641c0c84202d06035042d03d00f40603442049014a0310355068080041036508800c40310349010740911380340266040040c0030364004079070124a680903401d10347c0c080d103030410400306864802c2c0d601c00040c4200b141c011040700e2032128903900512036840b50008100340038044504d055003141070205030f107480f450301c20a82c90000307802c00002000d80c00100c074a4a410f1081c81d02903a071004555248010b4480000c0c00c606500740705030ba02c15040c80d210889007024030300301040300e8460b41d24400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 320378741 1250 320377491 320377501
    0x80105130501060212090a0806010603090507091107060b06120c09041121070504030507060906032304030305100306060803070209091507050702040603240606020d0903020f03010b0303070803 84
    0x10100e00c0d00c00c2280850510300100240703500403400243c40030070050070320f50b030b4080c010200300a00415440814176100e080c0002800039030691003e082240700d141511021540c6950000a03503a040300242c0300c14008000a4000a07204e41c041a04194041e000c6410415015a100800700046030310585005000400d0110b61070207114a129038400c1404907410b01d1041114140c2c2800224a0322400440d000041201740d4051003e035401140d2240c1101ca00c0760f00d8000081c211180d510614000ca03081548440d404000100c0d43c1040403001401681d940d034036920100c001c0e140c05800d5541d4000c8c00036001c030119004d13001c0e4101034000d2100031350795599944148a40d07502d0003468030119420041300020002d0444c003103550091000c1c80c00c80c0c0c0390061800010014126540010400b91f5418510510101d81300181440ca02e001001040407980d9400243d8a0f0302c8400c04010002d03171754001c1030005103001a014003c011014000081210311400440d1a55000e00b0042e00e142e400441084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 320379991 1250 320378741 320378749
    0x9190915060b0f120601051608040807050d08180f030f0304210209010905150d050a02010f1e140409060f030b01080a0c0608150a06110105160807110f010606080105 72
    0x1c00a000c02c0403214074110b003948000c6a64000c01c070011100706484808203007240e1080c4240d442c0b0050b080361b1204100c00034980350a0541c801e10525405006031700d0000307444c1c502220146040b5800012280c81d200d0507401051290001d91680e0340c0c4281c4c404110a00c80c0c808104026103400503000440e46d0301d003040703640d84420813640300014520840402d0100140c4920581c50304480103107002085a0700c9140352030781541102d240107030304041c512001105001c00001c3c4900c0560003070700c540c04083e00600301190300d5401c6000d0074010781c030b1450403242c604d441403200c590003003071002105e81490384502c00101030f00d003264085690f00032a00c90a01c18860302416090042551000400d04c40e0942ea444a6440e01c680c07059a017400b00540c0010840600d214051542140040c0140f83d415242ca00c003a01d070303694082800e04950700e401c0024082c000542c00c104890402c6840341081a680d45a04886190035a50711701081d0207110212102c80b5024091100030f81860303103810b0010360509082c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 320381241 1250 320379991 320380001
    0x32803080a11091e06030a05070e0114040515130f05190807150e0d050f010b011803170c030406080103060e03130b0f090604090203060405100e0609190915 68
    0x8800440c500140d28240c00740340d00486040c0401501c1160704040d03403c00c4030400d504c049a000d9044000001003000c000000d41c4140d200e09407a8550403125241d480045503150b48410740e60000e43d00410050145207440c11031042c1491658800c180343c408031140c4074142c13030b480ba0700c981c00300c01113140240000d140015090780400c60b02810406030600e0650456580d202511920a510407802801c03c4a1441200e40c010b40500c083e00416107001c4518000355a004004900c8000d5403800390150306661189120500303200c1103020715224213003152140780945500e8032040140d404108a20381e5100c81c20b00c0604014002030715070001d15807541c20000e090701d5520107140131613001000740b04a2a403440081c00240da07001e40c5115115441003058602d80d05c0340c2d41c203c6a0100c3c01150020354650260010b44c400c060a441c284482d48910309200c0c0d04030351601948102e03c0501000840a091a0340440d41c018010745000704140480d124420403111800002d48444400e0300a941c0e03c402c55000d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 320382491 1250 320381241 320381251
    0x115291602090609090307230a150501140f060a110604050a0203060c030c0315150c030304021c05031204050106170303040201090f0b091c082803050103081803280308 73
    0x1364186240944211b80ca0f4482e0300c0000f080702c0901b0342c018401140c00240100305001c41c3c011504d0010390380c24030b006c1035950303070008443c01405c000012a2804000300142c01c0c5a1015001e0100d07103000e14100a40398101c5a10f00c020000c4802c0e03070030b10300d141c1001342c00d008030700640285c66410014014141004001082009100010400c3c004051030000482e076006100780600d50a1105800000d07030341e25190b040c5800260408915581f417010040001d50185100310307109642003050520740d210001d08054081c041350418040141c8407051030340700c1780e8030038455000040e03116110102d0f500c4250041681660980c80030041004558114400078064240a450100280e1034240c1c0d666440c81134882c110f00a0002c816203104400058140c0d1588541c00403a031610703400c0b03041c40d030440382a4020031210444148440422074502a110b1141669080312016181c10300910000d0003c0d00424140b68141c40b42042c211948421001108044071108081d10030742941810020850480582 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 320383741 1250 320382491 320382499
    0x910050f0921061e070c14030a030c0306050d020d081b01020406080105190311100c0c14130902030c0d0f0c03080d0e070b040302210304060201021b01152916020906 72
    0x40100010b078240d4100c1d40c0d0021003403034001e91b001710720b18081c054082d810346168094803011440001d401e8141e00451405d07145603070b081141503502c104204004044520194214015005840100d540c0000400b80200307040a20805250300d158914226442640719200052502e8010b00c031510b0400c098140c01c9903054518000c070307421519088a008403011480d0322404442401040050048071460030858200501402d283d0795000d01104400c1042c05079072013030920004030210000c2c144106442d45070080c000300030a54a10781405500c4d01c00e02016104001040242000100d601e1038400146108841003610b07000740c0541039051301c000c15514040c1d900040b0041c4403100045003900c0840e03030100c86440c5000030780d030009014903213072411b280441d01000901203202c40d015001400302c3c080d8080500041e24004095900301c40341c940c81ea00345050707581c82c2000441c4a00203542600300c09644500550350440c2c3d0b100360a64000d0787e00540c1c0780725128030a001e521344103d4581d403200d0141c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 320384991 1250 320383741 320383771
    0xf0316050c0d12090606080610060203030702030a0c060605090a060306110f09060906070b0c0c0d0318060e16090e0105010801090203060408250f0b0a020910050f092106 74
    0x300ca9107850b41c0035802103400704026000030300d8401d02d058118181e8140c00420030041d2a440c1c201d001d4079088100c0c0c1c92032800070b40b4100001d0b04c1344000704481c801e0081e03a000d542043e001e9642282d16101c13810069428544a040c085000c0d07403080d0301c1d0340c01001f1801d00007030302c1c0c0c2c80e5207000030a07600c039102c241860040034000d10900c568813004660886004840311a0345400f4240000c00c640a400d03000762034000724a00700810440d00d24010304507191701e41c045900001c1000c07412800e40f8640c0c88110100000c00d6403510000b00c40340c220119001070503042d1251006c290044601408840c0c1c0700414680d20303280a0141d60000b0f10034240901807000080c4a00411500441da454001a0004103203400001d80d0b400038600096825035442a440f00d00701d00000181850390356106248026180d070f40014012880001591080710482580a0603c84c41c0d841e0842c803d80300e9401210a40764260707000c01c12021145e079941c0d0b0030310404c030a20f40f0398a413030740e00b00c0c1000381752000081c0103e4020041b5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 320386241 1250 320384991 320385007
    0xd0b010e15032e0e0d17060402072012030f1b010b010e011101090c0b03090f0d02120d020c0703140d0801060e0603091e0709180209040b1305030f031605 67
    0x101002c070010740c40f03450060000801220381d04000d015002d0a50b94500580d0040d4014a9002480c64104030752514800c1c6551603407000c0200b240328015005010410720705a80d1100040c0d40b000d0159031800410541d00b4041840d0f00340d04540c00440c00c1d103541c2d076001032908400301c90600c1c841c101c010410000c21010510200281110710442c030141d050000306481101105425003001c0c0850742c0c400500c403411b540d134040c640c600b0380054544000e6030240c1c000c02c049615002031044807071701c0c141e030081a00700000184042507612240c5517052542d000c200d0184207800421070b10703006501c40c3c600c03041030315014a100380c1404d11082811082104020040042e03540c0084120441c0404550301a41e07600c038080c00304d10700320002c5940009c42e100c1800c0205420300228034441210900074040c0240c15800015044030408484002c0d440410f031808100805c4e84e0b03181a603400b44001ea035400c5000800d84078030785140c0207076101c100440c10000c10000c0300b0801d240b08803026902414064288400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 320387491 1250 320386241 320386273
    0x1b090504050309040225050304091811040b0f09100302091e01050112060801140402040c050a120b0d021503150607030f080a020d0204091401080307200d0b010e1503 72
    0x49103002407086801107101c006c07070300020301990401242c60300b200715030030860710306541c80b0713003192180360201860000384152612a40d40d0740d40040b6400303070f48103652421003000c01c0020010208410b0300640074000c0c00d07000e0b80b91080e9040c001d604c0c0660030030096245104100402c0e800802d810305520448280e400d07030030940c4140070b0644409090858040000c00701c9000100403d40c0328020075824030304201d1204070326440c4c1901950003683c050080c800d0700103003551136100e00c800c25400a10518124046c1c1080b5611244501000502d1100807500a400140103027100076502c02d1864000002c2c01000851582400c10041c803d980036402c01800b502c01814a950040f000301c00e12a4950004100514a40c110761a809200c1d00c2103440d41d0b1070300c117450020504407015444038081c0d640041382c4c40c4c0001041e40e00069119214500d11100100450070540403180442c0d0804c2d0880240e60020b080745150034007a01c0010120060391900c82480c2c1c2e0b6031511800140e010b500130381440146084 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 320388741 1250 320387491 320387497
    0x18050307111f0c24090c05120706050903070e07050a0f020703030903020405102304050a050f130f0b070323060604150c14011e051302040b0415031b0905040503 70
    0xa25410100303803550050802c1c080900742501c00008025010403520b0084c1000d91000452a0042c48a40d01880d200c40501c0401580407104600f41d2340f202c01d00304900b074401c400901504201501b56140320303656841000b00c26070203442d10404a0404281032031940e0f0f01440d210012078807403000308070061131620081c061084901002e401142c0b1100014404000c0102d4078001b0103d43c403101c0407480c554844200c1500c08090041e10440c00e1078045800400c0728080c00d03020341c6001ca01c4200c9500d079403d0341d084880c0d0034581260448907101c20315001c0392015101b5407140350b1075180403a00b40502203100340300c1049581050181c5c07000f07006110300c1d40c980c0d030181d5042d20440d0b5218011030385015021381d600c40d8a441e000740441c070182e1740141145e2040d004005a401082800c0b03850500310350714001940c0007240c0892008040202000140c601600f0104840402030000601c0783c580b0380c00744045180c6508280c1d200c038400c00c0607141e149500e160a0300108a43c010402290805a5038113490748 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 320389991 1250 320388741 320388799
    0xa0e01031b0b03011404021209030316140d09051011072907050a0c0209010816080f0a1101030908280c0f20030a03020d0e0609010e01121805030711 65
    0x20801c5d840d090740300d680c103c4442c00310501c8a01c6152030100f2440d5942d83c81140c10405800c18010401c14080c010801c410079095584034990030700c0a0001e80600408035480309844900c0b0b2031a07400c8111a04d407040c1342c40754400c2031a590781d400c0c1d40d0030011948400c1002043d401005481801e0040a091252907004040d600e440c076a1200600c60445200c034100718040d500100391400003034003240000b00506508440700300313003410540e1045401d85908450888182d640c01940f4504005014101c4000c6481c0c81410005440302c003030b0702c4502c40b80d0003140a46052110340700b404100b0102c94055031925500310701d403c41042510740d60f1003079230b2216080c0c01014044d000c0300a840450108408030348001000c0c1c00c44c0c05c15207850034002d540c0d1000c824038501045441c0f0401500741490011600c80c03440603102e092455082800460704c03441e000c032010b0b9500c4d82c0c4980703003902c00b0090160f400d01d10740108001c5072550314038180000354803110894144100001003c07204901e0030b00701d1240400f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 320391241 1250 320389991 320390009
    0x1080708060f1507060b0d0510020307120e010234060f0f0c050301030b011203090b0c0a02040f021c0e0a0308091501060918051902070606050a0e01031b0b0301 70
    0x16444031004501c2c00c030010030085a114030000b0608141d07103103800207020721900544e014131910100406002e0358080140c0d01404d2a0449501c6481002d8603800031030300810039260000322086098900c4040302e41000c001002079400041c0d100603c00946000c56982c415502044c002e500d000301d8a20074a0013480d002040c0c0d0381c4804200000d0803180d0f1040d4108280c486c414840b80d060b2440042181d4400d01045a4800181d40040b071001c01d000c2940a4041d8580c031803d40d00c609240e42d080c0c076900a40342901c203078452101204016200c90103081991100c0c101e000d07032240b08a26840c4003604445140c019294a403140030005400000303035032940b5503050b0801e40100d4039110080c0c3d00b00b06030031180b0f28096802c540005000d42d88130051008490000071087d2151801181c807809841c0d0544141c81144207000380c84043e002941e00030300940f4420600059000c0d0765401080140060780d0100b0311440350880100180143c5ea0807512001300d02c818810000d41c14402683d400b404180520005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 320392491 1250 320391241 320391257
    0x30f060e16020a0c06050c06010b0403031704051609060609060305061c17130311060313030e0f03011b08090a0f17090402070c0501030e1513030521011d06010807 71
    0x2494001d200d010641c6400c0b104041240b40c0764203014026507c461003004030f034070840000045906181c0c007a54152076160b610a0040166400d1040c82c0b070f44098016210342c010354101e000104200c00c0c0c1580100080d40000c21080d1a002c805403000c880355000405040c10300e000c1003031640d40c507c8981c0d03100c842c0d42c0c00c1c2100c526203410842c40c50881d207459030210003400140f0300400031184500c9011203100350f407400d0b404030245042c060540020340700c02140700303203215660740060301a00c103505400c5005803032041c150301490300003402c0d1240703903c066014080d820110000c0c00d034406201503203e1120002001044001d43e18003a09400c2d01350040e21a500452a040c0307458aa6800c0f07a6880d00001c10030b6450740041d04182600a0b41441404c1c042482c00c40001c500312004600403029154030164403d40341e0741d440b8600740ea10b55500003141000420018202e40104d000d101002c05842644030a420758103200c03407240071014203400e00c150740601404204460317901c860482c0d48004a4900211 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 320393741 1250 320392491 320392531
    0x90604050a021306021b01030903081b1603050c06090705060409020a090504020a1e0806150f07050604030215070206041106070203070803040605070c05060a08060607031101050c0a030f060e 83
    0xe00a0f112040584403240710000344143d800644191210340185101c0503006c003400040d0304607800124000c7c082000c81d0001076000d81020045c80c01a011110013601e000c0e40d03400140ca110000e002d040300456404510f02244400401400d5800040e03403000303100503800c0c0000540d40d0300541c49546802c54000802c603238260310825802000f000f000e0000e5443d6410504050124183c0707000f00d40756000029015a15540b00d885668001c0350050710158407003103001d801203025440103e0340c2030b0b140350801c1604001182000000e1049000c6e9001d05145c0c1da99055000301160041c0010045601141c00d0202203600103100404d00142241d100340e540718070348042424000294880c1c00c1500020030000340444c2c0040040900910900000054030f440c1d60401c440c50040c0c02d10400003ca48100050300381c18400300400e03480380282403800030000403411460945030111101707010050b01042031211940c240c007e41e8082112800b0602c6580c0c1801e10401c0303181d00c008c251150883d81e50350510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 320394991 1250 320393741 320393761
    0x4091d0c01200a1217070309022d060d090309080a0302030909181b0102240402090613060305010f0506040b280b0d0c110601120303021308010515120c09060405 70
    0xf140c01c0da070000c80e41d4408003c9a0000e005607550030028844c150340c000000e0100e038440d10448201590040c1885652003025000b03500540441004054240320204000301c107a807014060a010141440d01045204441c64002c0890076039a0000f980c9078040b240305d45c0044e0300807003036802c0010261440710060743c601c0e46c940c1c041e00241c0402010790054140002c010b0207541100e4036418001c1e000c641102846100407071700b82c0031800001c0c10114041c40032500519091924a170407850040510800d80c4a124500701103954507481265281c0d502c60840310019658001c855016600700ea041018100c1900811510303110a03812504820081080000c9070301c040b88454080c005410320281c8a4081e13101180003024010b1000c00440e41441040c5000000051054140c5803020503074182e0b1181c643c2c0950184d04003c07448109031010000c0840c184109200c1c607441084000521355040380d407001071010b00f80418006041540040442e0041921400003040e0071481c1614001680c0c1d80300c080364 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 320396241 1250 320394991 320395003
    0x12040309050409120306050d02090a0c0509211b09150102031c061d071202070602040b0a020610050402160312090210080118060f030206070302010f0204091d0c0120 72
    0x8580c8245041e0f01c2c035007403280500500c80d00281c40c3c0c908100d075940f19010002d20a007000340095011611301d0001da8074070903903040340240758100c1c10564148920303d0002180901e4003810040d1880c024803d81c601d44804108000215aa5440400620250001117550482c00400740001001ca40028100c80c1c3d10800c00c07200900440701c6440c481505100c20708014141500c2100b00d0f0480d400020140b60110802040c05449651074030441810030041074006034102c1c92003034480f10381c280400611004004000e10003502c00350302a00c3d1520f00110005001c0103a41c00c864001ca1050200c3c03211141e03c0240d0900940d05414032a0f02207090b5900303030300a00004d0b44001c1d0030100005089150a400c54190f505a440d078144500d00d134006030707080000301c0e086232250083d500b0303080d0300400c00f504107000100300c094003034400401d80384841503100069a005a0001c1320065681040d0000102c804c3c0f955258403072400b0140810f03105100000b0f02011204070a1103d0008a0913881002c043c20086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 320397491 1250 320396241 320396249
    0x120203070306060902090f060310031b030602030414010c090b0306132c0d1106011404020c011406030705010315060305061c050102120a0e0604080a020f12070201030b030d0512040309 80
    0x2480004d07101e5074800c01035048180007601410014101d0081d502e840c81c00c0d81e105005980300545110b185840340350010200550855629403991700102c0810718034001544510302400d0300030425004843e00c1d9003141e8403040144100200340c4d00500c0444045400c5a030000c0c0c0880fa0705801558000c5112300400e00171b00c0c00b2044c0141c002451204c100c030046600340171001c804c1600d0b00c0c0b2515030710503644c140070340c00d500d441c54100340014041e96440079401d002c0443c01420040c2000f00c000c410500312040c0c00070800c1d0503101c00c0e00b0010145420007104016081c02c3c0303000e00084480803240c55900085028030b605140d22100022050340302e0044000800c1000341c11254002c0d03803410100d0003907014100044203c0b910000085450b0018011101403100840007804c0b151b845440d1010290000e001103400c6000340910760849500400c01050426441d10083d90384055610001d801c5400310142180a0f403c0804145060758100c4166409000107a21040c411381e110301d000ca400565a0b00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 320398741 1250 320397491 320397503
    0x204050402210601140406080c0c03070302070e061e040c1106010603020706060f0302030d080705090d050c03070e0115050d15091401080615060c0c101107050a0b041202030703 77
    0x5402e1100a039841c00041c44034610300d015012070b4680030011244d100c5403a1005070320150412041200c14030030b00c030f1160711202e1451868106200741c402a411139002a609400580c000042444424130b01142d4580140301100c0001100405c010b018400300003240e40ca5114179650072200d20014014180200049249000c1c0da0b069a12448003500070b420861050b0b44844c6082408907a80250001001c01d0340c0d002001010850000403049036006c00007404282000405c2c49809115183c5c40500400d0610480c0038240d005c020409061070010f181d4807040408681400400c0b0323040011810b0425500c42e407902a45e500408048000541135954071012850b070710120000d4180c040354031100010f8405d030f604480310390740c2d02d14090740c80b0340a6912041c1c08010000e0031203240b0300080140105001034068804051001000403540450140c02402203044560720108410301801213202030f11088400c0e9070340900348a48403205000350b0166184440303012940e84107550b010031000c4000d5030701071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 320399991 1250 320398741 320398747
    0x30c04020316030f090305070803040c031407031b05151b0607080a0c11032a12070b1e01060c05010209040e070911091c03050403050607020307020a050603160302030a0204050402 78
    0x88201d400024140c88080083d103000303200404c40804e4000c4840746909a900c0c0f81c01c103041500c038401070f0f03800940205c0d406002c0a1001002401c1d5407420725a901c03081d8050b000b8546941080b015180c05141c051404494050080c40386545110440e00e504040b0690241c580740480003548010ac40301d44010310070b210340380800500540c4600054030650701e5907414000c0d0066203200313441c4030300204100e084641051002c2c1d992984150120103000105004003042e446004118030b04216400300c1041e405100050100c051110812066401c6080001c1c40c4036000d9800391005001d80060049a0811512082c0242804801d405a0311407071001030040040e0302001c050700d1341c2c3e00340d00d00c0344604d12800c003202c0a03060360f034040c242c039101d803005880040b1160380001540202c5181d80740440a0100601c00480800d404010302445070003150021651940c003030040024410b003681c0002c0c8244000c1003000049120310f411058500d2090902603125118002c0c42d6000e4051500550f42040c804 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 320401241 1250 320399991 320400001
    0xc0705030c060415050f010b0306061204050a140d020604030309061b0e030f070b030103140a050607080f0112080d0903110a0c0306150b0f030403021f021207020c030d0c02030c040203 80
    0x700300b00f07005900c900b282c40c41450b18070309003c0990f1740803160040d03011014401048643c11440c0199030002e4002e118910b00381d142c00400107042070030398003940c580d400080c241c005c102c044082800010041002807461a14441000799035142c0104002c040549582580c4200045034004081d040c001010300c1c41080e000b604c0013041401085c1c01e240c031a204180c3d4035030480304086204000e454025070240d1035a030a5484021143c40128041210703440341c40c40c0b01010a006015141c09821241c0e54031000741401c3c50408080c00040e000700140f01c00c06901d000c001242c11086a0028426950211395040c1c1410156800c2d0401c50f4107981d203004602d00300c0d041010309903008007500e00c00c00080020544a152586180540e4025450008000c000c2d0090511200340a140e00500c2031040710400c014101e42d01c0c0740c10400c081c0c1000c84540100d1113010407091000c6080d0b0203076051008006079894039001070740c1d48880220000500880d4444002592014090961042c201a000359502e00f00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 320402491 1250 320401241 320401243
    0x120b1f091a03060a06050d0201200f1e0105061309230c010801090b030706120b060a090302030c0d0201050f07050111031006080c0a1d0d0c09051b071a0c0705030c 71
    0x3049070310320038068607001404140f5140b041c40f00b41e510161560420f01c0c0240d00542d15001c08190108214000204010ba500c600b0801c000414030034202802050700c2c195a410305d9194500400348091341010204426030f200d07a80545072511682d200419208180c1c09d00d07103030448541c034000103010b44452007500000310000f449a0310280030b0740ca80b1420303031362600030000700c0c0c0b94400c15640c1908003580c20003d1912841e1010100300c056000000c8642c02000000c9155100e02503803404221074003810021352509000580284505441c039841800c00ca500080c071911403071a54134a40c580119038030080c04401d6100b400b11004c0429034944c0c9040c8410a820700310050f01c540000648202e0001e84d02e011010300303880c50100592100b1100c001002801c44050a81184490b001403071040c6600c04500900480b40040002d030400141608004200402c80010702c1c81c1460700890400402001551071104861210302c80900d000054580e00503240183c41076620280251101044011a640c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 320403741 1250 320402491 320402531
    0xc110a030b100e0603121b0d0c02010809030901120f0b0604090f15030503090d0f050a0b01080d05072003030403022205130809121606030213120b1f09 66
    0x5142d4106911140d4038520003c0c000303012120310740c140e00702c108503800c0c0341d03400e002030004078903060f03210502e045034803a00340c0c90700b02200300b6000000c003880310003c00d550304213021542200e1100b0140d480c04c291f61001800b01141c114914241c10340d6004444420300b001d030300c40c0c504154002c0c01c1e03507a20b6507260100d0300504015810f2f14402d900c0c210ba84107135020b001ca401d1003141c0c2d2040140d418007044400f0004504000ca40a888010b031400d00300780000c0303041c130904130001d00c5400c0780358455042082036468200160780500500104102d01000300b50050b401031f22142d0303881c11150001e05040040303421401180c1c4020f410031990700d11a40300b1403240c3c14503540c3c00d6000d0010003c41d03844202d810314481d903200780540706000400c070103010360400380d24402d100d1121904807240401c16043e101c481d01220f500080001780c0c0440c001e40c1011460041c1c0b80142441c00424542c80300d10348420f0038184026210840d0909001d02c075201c64840c20301e40e103000b800e5801303003082442c8007050b13810070020b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 320404991 1250 320403741 320403751
    0x121113030c0f050d0b040f020402040b0c430509090f150103080909060d08031005010816050316021002040306020901080f10060e0102100501121b03120c110a030b 71
    0x1c007900d400429100510b01d400021244000e0007406000d141e40c940e0444c04d00003a000b0f03200401c03443c0c0b10030050788444c0010b00083c40c1c1e01ca03915558000c50141181023480011401c038801e080c040c40c1841c000d0a40c51181c01030551200014003003034003140060840181c1e0b910580c1c1058152040019401020540c2504400b40078203032340c0840e480c040c28103400c1d2030900006080200c18054500981001e61500d0307400880504864070840d000c0e200c5d900380b07800441f03803c40d6100f2000428001540d0252400750440001e41040c20501c0d14500702a200c3e010042c145090041c0d00d8003d00d1289200f0418600d00582ea404115900d58403414004040e5001f022440e02041035900400e1321401900c2d0094030071040d026080c4505802d01008980c120741e590525411803040390200480c004091095038006c1c0b4652048041010b02072a00a0b00000c40c617030300741010410484200003107600c00c080300c1d082c05482e1030b10352101d40d440e14000f40002c000d1000142c01c8591110048100081d400d240b50283d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 320406241 1250 320404991 320405003
    0x110c0108010911130825080717010b0d0b011d091209190f0609060e0d060b0612090c15030921070b1503010f0b01020a080a0302090316031b03050d12111303 68
    0x396041e82da1b80c441d08402e109801040e480f000c000c0281c041030081d104200d05245001240440c0c503d0000b88440003280c0c400d980803155040100700103a040798021141d603c200e06034200c00d1800f007040ca502c501c0c90201e402c0040400040110f440d580d1101c0d00c1b058480542c04400c005038139404009000d16142c0501c1005c1007120801044860051807103001d14500101000302140c15039594030050641c2550058000e2000d01c00c05202c2601542e2040c41104000001c0ca01c00c200c4004100b003265400c0d4042880220400074000f0480b408140040280c40f400000c2d00440882000032965209070140035241520480610003110302c03400c40d065910104070000c1c0008442d0111480440b822140498007581c0a01e98400018032114003914003155030382001810404414040f03400e160710481c44400c2c606403120107000304020041c0c0e00f91510345c00035a0041090866803110340e914401416801881074006400d50500f6168003c144241410464103071134481e100f86448504030325000c12122 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 320407491 1250 320406241 320406283
    0x312070e04050123010c0c08010603031106070305010b12040203100908090108010b041d0a020417060a060f03021507050c0303040f050a0b1206152206110c01080109111308 75
    0x65901e4000035142c401d9210801d0a5514041034015103140055080846480c1c2d04c1c00000103160000388140c40c001d5000740c9801c00c180b518037101c5406d1520040048050514110060049101c103005070754896400506142c0e2688642c00020307e42803161401078005401d1001120401c80310f035021f00703982c4c00280c850a40f60390321070700c5015150003203010f19140361030001c80e440414030200c161590840c03010680185860b880311442c0020b030118003121300c0b0f0f80d03101109000381120b10744122401000d601020341c4801d401d50707000034001c0d030740c2c401721102d00358010804030280038081c0003100840e00c0060840c0c0d07940d076032201da400040c0765034400c45209500010001075000684021208040d86250341c00803d82d45000c01c02072003031a4811140740345203040c48200044020041024000c1c3d88402c0013807001032810b01e0040000003080024941074018041c001e0031039030020010383c1503480742c0402003280da5541800c150700d07024010703100a410b170452000080380100401d20070180003040803e504 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 320408741 1250 320407491 320407499
    0x103150b030f1b120a0506043309060f1a0f090903070f030c050106090605040c051602060d02160b061908060c0307090312030501050f1c0807050312070e040501 70
    0x502d40309048800c04071a00000c3e00081407510210749454080001411500c143c1c1104005a241c06401e1000719180d6201131f09010600c500340d0080302c000e20aa402403002203805959074500b9505a03004040e4030b50700c0318501c2c070412907a030300828503c04107c8020000890300074005104850010380c2c1c10700401d01109440f00c0d508012000d1846007242900444ca840c21030b95031165aa20000360550421040240e5403000a90078003c000007000c50f8407001c80c80314100020007044481684000703042c04402c00c40a03020b944841e0000c1c604039012a07407691107400030b42001c0082d100e41c45980030320002203007220040010300c0400a0083c0425901d62036001d2060452a034141c2d2240160003080d0f02100001c0d040c0304c014401103600410914280b80250394030395420001180c108404004240c85000600a504120b0380b601402217007120710141e50f1501ca400c50003000000c030009411140001000313414002c0c10002ca82480011405c0d49419240c141c500904a240404105100d80c1c1000d000007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 320409991 1250 320408741 320408743
    0x5090103081e0f0c0d08010b09061605010b060f0c070509013f0f0b01060c0519020d080a030b0306060108071d150301080a11180610090504110a20071a0d02030103150b03 74
    0x284035030101500452070000500c0d00f40be0f444141c442d045034550b4907905000300030380b0781c80050b101c0c1d08059019640c88000c00b1081a040c2203290304140d006040c000010818041341c084880d240040d610f035800780c0c030000661800e0542c86c280c42e210400c035441a04000030040700c82903601105004102c0c1c0100f40e40c880c502128110b035038402c040e1240d800b05001c0c0420b0751031000d804191f14070040060310003680b50342d1218143e400100004020030343e80d11004c04a070501b405102c1d8081800d03e460006464452030140000d6082c909811840c01c00100b810324075164103034540070000051540c19107a6942e8021103649400c4c140080f52440b9a603558800f1600740780340d41d15403410081d070301107030156a92014800032f8404809100204080114001500c4d161807040d0303807200e03c24505865448240c80c20107440034000c204024032000c03260603581c2e00c901c408580700e01174500c1a000c0200149042421400500506e00c0c20b1070003a10000000080000d102da440d007510251420510020000c00209 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 320411241 1250 320409991 320409997
    0x71805011202010f05070204110d0c0c030f110304050904080a180e06100e040c020c01111b0904150c0513060c2d0c0e060a05090103081e0f0c0d08010b 66
    0x80e1000018807000541c00750000404100c007a14005041c0101c036000101a94900c40c400c4000800024403500100b40074010a0b03400c0095041144403844c141e5001440126030800300410002c084c4811000c016040c0308480040c000101010840e080c2410320380f900b548005d240300d0200381e01d08100110500c28911180468a540c010300740d840e030700c42c0107201c41d105840020804000c105200e400869849106103401c1d02425401050710100c010700150840811914100726a40082d2200303071000d401c0c0d104e0a07007180d02a14000005e0b01d0700d151001046951800010840d4200122002e061781d100002d001400203070100c546805544910680e101a140b00c805081c0b201e80903d500044008525110f80080c404608061a01c0d41600c0b04440310320541c00ca489440491024055989844012031010709811540c81000d54910b030782c2c22260388200208420101040000000042c00c400d0076500c040c582e64104913a14481622a01d484105584802021078042c400201d4010028415 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 320412491 1250 320411241 320411249
    0x30c040815090a0303020f160f0201021e070306020a0c0c08011a1816021c050304020909010c0813050307020a1412010203100b070203070b120103151b03021303080a0207180501 77
    0xa00b0f80c280281d201103006c0c0d40311002031610a8420000c0c80c81500c941040d21215900400001a00c0505403000a0a2807590101e0140301001c49440700004800810a907048940c02000140d0b01e5454100980d00300204010103040302d2a04100081e8802d410341101c5a880c98410601341000b818108020560005050610051036800c001a408204040456004d0507050040f10010810b812000c40007420030f40c0310200041c00403013808210b0501c040e000d900706080b80c0080c0050840460001d20641c030041c0904801d8120043c58001e0041c280100c482c11500038141c0d039080d9459600c0e440355241105d04103409410210f51003c100301040c82501d01414650b50140519407802c0b102144a40042ca03003030760b00d8001c50300002002d05420005001d000018a00348000d50701d1400e20208500541d846441080c0c10811100d10b101007402480e0300020781d43c2801626055021003141c0344c28015000240184000034114242c00d0b000107168048400822200c0c2d183c1107820147e405503070003840703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 320413741 1250 320412491 320412493
    0xc0306070f0c03090504020c0c0f0a0305030a12020c1615030c020d0f0528020d02011401030201050c030c100e0c010207050a121a070309031101140105040509070b030c04081509 77
    0xd4050080e4440c60007000000d003e4a070100080d41c440d400642240e108140268055000c02c41c031026508000c0e0010b40d841c00100c5054006030300e07503207900d5243d11408070b640e0b04000d0b4040c03a072034800c88a941960745085580c000c07250b50100980750110710650f503010b2100d400181141d00110244a0300410704109150780c054800720b1036407141516541d450003403900600405021030304420b900f40c0c0d0a0b084481c480f1111035400040d80300c0107400c0c402800785180442e41000c4020780c1c04990701300c1c1181125420310b8855641e408030b455203415401801c00d0142c590050340c1c444c800000a0b50044290b00c40b48200b035401c0c050980005917503d00d403502c226134211114010030861a5035521144080358001c0241d4040420700d0400c05042c284100e0341c0b140440e585125203000e05900618000b0800144c000030000704031040e0790181000300522071244030700d80703560028081f244d003408808000c00c080360109490341440c803140081d9800500a266a03403107a4400540f00f0031140b000d1900401080d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 320414991 1250 320413741 320413757
    0x6050c0910030c0512130308010e010f14061909051302131406040314070f0e251101140a0b01030204050112050411090405010f110f040603180c0e01080c030607 70
    0x141042d409418070700b00c0350b002e214051100414030520811007a01c610b555207401c2c10560041c3c0707000341007408180c00600c6030104450050040030440802c01041c0c1d20a801315000c82c150300790001780c4600c2084161001d100d2740081c0e501590303800043c10300030748404a94a5808900b510308140403801351340b51025a460f5800c0081281c21001c5c0e051004a00740a044140b07019129200c0764076490100464050960020000b00641243c80074201d028149184100d045410403441304200000031010b1015011003000c100b01481c0c0c013a80a0020244c0c144000780305070b00c0c000c110091104000c48504000741c0c01d10551916542c4203101301c1e820b4500584801d4500070140b4107600041500034001ca410407540d1840e48041c1d40d88141c0140301c0c0c1d104400124202d81c48008420540340121107840c4140c00901024410101c050b0559003517602c1403600092000030900e0740030704548100000381017180451404140e18142100f03140c103076030b29181220fa0503040c400078180e9803102202da01000031071003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 320416241 1250 320414991 320415019
    0x60718030b060d050106030c1505034303020711030303010f0b030408090a03080a0201180201080601030c0e15090a062109031719110c070b13031a010306050c09 70
    0x8000d07000e4100d20094610440c15200355615421541c5a400c2900c040380302c0d140c100103440d8a4005100000c0291070b0080c15030405215020881d1060040440ca201c52465043c07440b01034014816058502d1104005130407521800140080d4018541234400448140c012011410b0001c11a41204c84400c509003101c0d290030f1555001c2c2d0405007040390300850412210029550b81140700001e1030154100d1942d805008101a08558140c0140061034103031440700400344c0e8000e08442d40c8000300f8200070550311a8980101d5100004100d0590310106000d28500b080c0c05407000790503070320004e860141c12a61500d00a450304001e540400402801c0e542a140c8001c19030b41210211504c00d04001d82d00300307180c03404003025030300c100d03003002082480c842c2400c0120402e010740010940108191441d040e6050556a01e9a98034040e0400340000085d203000c1c01d032003601c1c02c04011741e080305000d01c0146070b489820304041e03403c2c441030b50030030708103c0481c1c00e10311600c040320300d00c01c0020581c030b03096944 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 320417491 1250 320416241 320416253
    0xf12101809080a11070b03010b0315030c100305060d02030109052415040b040207060518070f0302030307060506300106050603010b0d0f060504021b1203070f081f0303080906071803 79
    0x4241c0d00e090580c000c84400160701c8140c1d0021f10302030700c0c0c1c800b0400d440e840e04100381600080002c004901c25400600281e001d0f0f00d41103c4460044030f50310340031078a03603114408180201d0041000941640c80c0543c43c41c1841000725015404400ba112880c2c0c800e207040468801052090360344107001c0c0501c46940b411868150f00042d061100030304054204103558442e0740444000f220001e0007060750a0680207115006e00076003000c1d150510300446030908680119569000d0a84010045542c0b6008a10340d139454a800d88103295071444059034403400781d40058483c0007501c1540d0810f6090030808607240c90600141d90503905c24101f480d040050388002d08000d403400d69a109602c2d9075907440408c05889500061402040d450404e10032207201c50081d915104100600100e07081d410300510944907401200129034400c18a004003098035901004030075074060742c8555401280416000003050342040f0442d10030f000e03500a0328051381d00c0800640c0c0c6a451115485110340704101c0900c00112 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 320418741 1250 320417491 320417507
    0x12070303081302030717030304170f0405060d020c0703030f02100c050a030f0f060b090a050901030209040b2508010608101511070305030c030310090b0609060f12101809080a 76
    0x20005080303d280b030386c3da0a6808040110701c001d0314001e0300004104014007000b80024101c81101c050342920b04100208520300c140214000c4070f1181c580000c18540c4440c1c0798060f140500c0360740c019182c40e40e17500d00c0c020b0280b1200d40070f007502500820ba0980900c0c80144110b01e240d01d001d880d01c62902e81c1c050070440c003e143d020300781d8000981c0e81e01008016a01440382102400b96040c1d80c690750007448040103110036a03035010074801c4800000600c01621106203c2c3d401c40da2015240c000d070744841141c500740303132080c0c10100c481d65100301a29a06640c00f40c1032904031056500c0301c0384651204450b203074420485025100c2c10884450408505178883c44010703102481c0300c815100304503103c0d56114150783c043c2c031007400b8503403010061100006c100140d140061042e031504000600c510b101103412802101603413840756a0125448034050019000c80311443c2e04406c5042a61030b103102041d02240d40e5000708048000b4034441206507001074407403c0c40c4542c00c66821802e04c60020000c071101a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 320419991 1250 320418741 320418743
    0x503070b0f130e09010e030f04060c0309120602090925050a0e060408010e0607050c0a170f0c100e0c06190903050a080a180308092b030e120703030813 66
    0x200200540b14810b419500e008001c1c00c0c28804105050524140d09802d5400461054003281c104005140c0c101c41c3c5082118121012420500c40712501414251070418a641c49a41544903c2456074200a030703d600070920302408131034894042d2104450850030344000305591407048440f155200b46035000380068041113040d072401099502284001c9842500541d0201010b0380d1105803922102e0821700c0050343c480168a0154100070025200941e40c810400c0080c1c0711044881c0d8105880c03582004a90940005104c926910003130301912582c0d410521074002100b0340341c490f41070008038000c80c002800c03040080409082c0100702003105080c48100100b0340c14802044d9000000820600507408840d0260452540354105d080300076124012041c0d0620000c0c0c490f00080c40007882d4001502d1602c40161526a24808100d0344007507040342d90b9548064a005406800c400c01d5070016200302e1168041c3c40411020481c40700155840e145404000d0204a0306000038200440c0030800d40d880c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 320421241 1250 320419991 320420017
    0x305180f180a0e0d020304180b04020f0c011406012001060314100b01050a050304120306081f0b09010f0e0702190b1501080c04050d0f050f0c01090e010503070b 70
    0x80d0008000606250908158041503110300c800b000034601d41403150500c2c2c40f00f9000540900982c00c20001e442e40b045000e1200041c4a00b49054a0090303258016048400c020b0005c6588805421582e003103500074042809641d82088040210003034030a008601038041030f160484e030003440115a0109100410000389550750392000003000c2129035284210000303105020305000e040c40f400c0b10090341c0e00805403d051020400c0384440843d400422290b1288d0000203410500c00c0001c0c040307029003919448000d1701e200700810501e07204070003021450402c0c1650401c0141658407001e02a2046c803d110300b004d10b40c10319004100e900b86880980e1791009051040e94140058a051160f8025102e40d00342c940322054401c12544404903020108004400d007060f0403289018051448917100318064180030700d004000b0305c002c018007919a0000701d98010250790641d60b126003200d82e110440d4410034001100c650000a91020042d5036a068a501030041d05803a41014410f2110b940149494806 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 320422491 1250 320421241 320421259
    0x30307062c030712082206020a03200901032304080307080a14060114070c140a0518040305090d02060c071724090f1504021c030518 58
    0x6251442045448444480580034400d00380715640c600c0c034440044840c05a1041081802156800e4005a0100468035140901d0303a1849003174541c039001d0a0204581c00504071084040203440d80143c01030000c0d9940401851010820805003040d0485242c130814104011015095203c2e800c0a055481d412007100201052400d40480706030003101d00381c0e00c001001c000d00c41280d90001c19640c00440bc05c00c1440f200b9000b00c0b25440f100e102800c0380d81403110700d14052020b1400402a603100ca0381143d90114070668449003502c1d000c3c0c2d000b000c2481000b4500010030103141424103801130781410b0344c0b101203d0f40d03503079401d4a4641c40043d10a5028821150080040c0d80d43c5000b02aa820400f0281c04a0b61903e40f071100303814500a401d600c1c5070402d0f41c1c0020030040d032400d107031030311302c20b00540b6162900c5541156040000c450101411401400200d080741804500744078052031084e6012101c081404c40c101200440c01080280022003c02844c0400b41c65100d03039000c07074000140040c0d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 320423741 1250 320422491 320422493
    0xa120506190902210405010c080c03061f030b061204050c0306191521020405150d0f020f030a0f050c031506010503090c0301050a1a040212070809010e0a0f1214041202030307 76
    0x1304a04101c404031466911101c2484010780d10400a0780c04c0004280ea20b801d508190002514a1960307202c041a0343d40781050307801d1040c2c865001201c61203009031500d5500d10000600414000c0d040b10161110321903299003021508001402d54429004462410882260b50404c0409031240521006a00c252480081860450f1071100500a1a04c0c422071103809400d1040c03109541000b024007800c590345040f2401140c0396100c2611155078001c1d44180d03198550b1002400c4001e540340140d40511441021008012007500c035124818026011603080d0b8900000301507a44101006410300394400402159455004d0800795410000030300944400d5403503140400d08450003200c02d041403a40326400b407803402d0440c2c0c110041c210800d41c0e055203400d120003110190010054120000c100c00c5000240038602c00b0746c0122000302e05038090328000203a5040041c51100d03000d100b40d0300240701c001c0904881d4082d000060600717140b8441242803901c0c00c420131100c41807081060b6018001008000c4c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 320424991 1250 320423741 320423797
    0x30503071e050d050f04020f040b01051e040f080d0f0c030c0f030801050114090f010e0d06050108030a0e01030c0819020f040b300a0504080c030a120506190902 70
    0x200071214035a54040c0c490340b050b81c0314802d50700081e0401d400012800c1c00c0c040036840d040001425040c0545e0003140201001c001242c941c0f04120a820ba01c1e0450050b0624108068000300102d036941515503888549907a082c54584032104c0c0e419012800e014030341c2c10600e003c1e200c444140380c041e080c86d481503091510303110017800004030304500040310b4100501081d80c1042d0a1000812011130310342c05c1071804c1c800314084540c1141114148403281c07412402c140d4a0391295400543c4c00b130400d00680d40c3d901c90301da81d40d070001c1c00c407540030402140324540e0320752207442110ba40d890190b55078071894540d454420100030b15100d40036a4603408010510480303001a0042c80280302c03028a4940c1d0350003586107841c45804440c1021000d2038402050582c1c600d8119085800040580d400911502c43c0c3c03038000d0040c401ca02001c0002c0c007000c01d0200c00070740c0001003098500341e011014011a0350310340c1040b40040081c080000b003020400c81c240500481c55003e021b031207a80c111048680c45100e2001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 320426241 1250 320424991 320425037
    0x3020405060f060c0606100f020a14070f0f05100c05030a0e041508070512011b0827030307090504050c0a08040204090b010e09010c09060509040b010e0406090b030f0c010c03050307 79
    0x880313a41e40604140805410031008040c1e0f0000c0d1440c05124001c0c00d10802521001040c0c6c002d000303101c42d058520f600090070b008100003849481039030310240381d980d003030540c0c0c4c0c1040e071280900c19074082e00a950114000e40c04800003507801070295107008400c520036074800e403c282e007081d000b43e9a9441050040b401c3d00d1858040c250100041411918020800140360198140020300364105001c0080d69580103610030640c0340d03a41440512550307400c0128194070015440d00000d0b4440c0140c601000d10040300030350180f00c036561140491900c6500b0712043e0380041e113010003141410489040c106210b0148160010310050010030108240d4607000509403003030b040981c814840710248144604248030b491302042041c1020341c4050b280400180c150701509002c14040e54440c1100180c6130311a5100d110905c5005000308401519003104000800240004900034412140104100000020b10014a9005940b20300c1c07002c1990390100d40304d400c098130210520000b0a800d00b07030150340e2003007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 320427491 1250 320426241 320426257
    0x21002011d030c01110705071a0904020a050a031505060a03020a0507140c100e1e0d0507090c14031003020d021f0329010c14100e011a09010b030103020405060f06 71
    0xd580b80d02c00700c0d070001c4c00c507103141c4c0407001000410091800007d43c08580712046610381c16812501800107411040d240c81a901d034561b20900c0059070114554000014091850b80d982c0e003001600b07022209100005554014140e0004080c001d6080c0d00303209400500100c84589020b45c1091a240c2c1e070700c644800d000c520400c070f40e040011550b141d410030001a130303245109441e0001d10341c10080c002c50411140324000ea40000b040c1c40301c3c5d801d141c0b00d6410700b0310020b500a04079614183d5030f00035103004008400741c0300000307040c016148a039403c2c0c0b48290303406450101001440765181d9401c0010884c140b900484c2c1002061040185003c0001c44840c204403040d1404039081e000030f4500740c4101e142c40040300090141c030718202d02c1c50743e01c1aa40c1070660750202c02c021040201000d002e2134006c02c03442da800746608100080c000c086040d0881990307080c400d4610b603480c06411041050b1080240105030200006000420240c603080e00560b80220000c0c001008100c0301c0c8021403560303401401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 320428741 1250 320427491 320427493
    0x1801020403050f0f12121909140606130c080a0c0c1704050a1d340203040905150d120e0a0b031005040501080d0c170a0804050c060a0c021002011d 64
    0x2824004c02041801006100b03024528900c2c5481000d01c103a00d040c0301c0140901000d040001700750803c00800d5482001c2d4030340c10088041c5854946e10b50943e6520307049802a008c0d01c810488010b000e40d40b40aa1076400c9000d80b0380071038940e81d195003140202404011a8100a0608004004a9604940715884040a2580a56441c20202402194000e40e80300030521810200e010340c030340e001ca0004607003082403526144003404070303032405040c52200f0000c0080145205407581090940002c000c00807a2103d40080c003e07036480c03c92841102d0003002e01150030040414042c17000810214560001b00a50b0500c462a400c44c50085070801c0d0450704201e50040c0c0c00020300c14020307502c961440c001e2808a4080c00a581440005901c58580144900030b10105a562804001c544450481014550604592144640100180800410b5806681d40d0013101100c1015080410840d10740b502c054031201d41000c22942840042d80c4440d4104045540c5c070340c051803a04015102c410000c0034180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 320429991 1250 320428741 320428753
    0x1b0b0f09070b041409070306030503040f05040e0109050d050c0a150b0102010b0a030c05130615020c100318080c010f0504060c02160509011505040b0a08100506070b1801020403050f 79
    0x240c4036038507003041a0001803000e4000d00081101c1403a40320030080c00601565610142e48071000103070042d0100b1381001f003041c000804c1c007044803044000e25200f250070458051048081c51449142200c50020300039096030443d0b12200c190300c0c0584020506001341c2d000722810b9040a884059885038007501c0480200d46030f403d40c00240d83c0c2400340040940301141d01c6004c040ca50b03541c50032070b81000c0c481c0c14060201c000111034403410640c0700c1001040d0940984030750140030707a4020b460b200060f100c0d91140007254107580e607081c03280c440c03280104441c03070641c064103806488510740f64220071041450340d904e41605524080703087c011140100d210347c1c00402c0c951080e00b0301a04214085002c00c54512071100304110030781d200c9403101e0441e44004458280f00c015a4401c17503481c402e58000326a01040050311504491780001d0603482120340b40c0041d54040d4440302000414423885501a01c50694072000c41c1e4400050f12100d07010500d0f49000618140e62903646034188501440020101d8000c4c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 320431241 1250 320429991 320430001
    0x30e01050f0d050103032726030711093d030f050d110111030a020f040308130311010e0f130b030d09030605100b1b19050c0406080d09061b0b0f 63
    0x1280f48410150b01c07c0c900e24418048000c101080c40140314010744614221390b00080070011412810841c1207140541e43c0e00c0300c184c14544c4054075581e6400d8000d034600c81c0003e107011180700e54210324024140110702e100c0c0e0415403013a13401c0200c030b0f5500f941604078240000020451040300c00c9841c0b20300064003500c04000e01c06041c2142d6a06050803e9050460710520141a842220751002c01400016142c5044482312050383c051600001c241000008540180c110f10001510131644a00c5400040010341001100c0c6010f0503e240c40e0041c41010500b600d51078034040d5202d49450042000a1403c54a400649000a000c00c440080b54407180c082c0248901c5000341940f05000c1101d10761800c4ca0400c5e525010320030091110150b11802c820a91007030402d00c2b03000c0c14800008040440b000e5141892a2255519602c2500c510300d00980040e5100002c1481c803140d1540e51a040341c4145492001d9405094206e24040814030000d0031030005111000981e0040c0c04c144507040d407502e89 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 320432491 1250 320431241 320431247
    0xf0a12030b040c02061605130e04080408030a110d0207030803010b0315131a040605030c0d06060506030c0c0c0d1e082701090e04050d051c0e0607030612080403030e01050f0d05010303 80
    0x2219540400004020401d0030248240c0440c0442e00444800109d13a511070800090360301440e080b400580c04000b400400c1c0d00d92203641c101c42d4107540b10a40301c003032100a50503640ea501da03100040c00c148090004001c160341c0345010f140d1200c40007100031010307121100040d41c4200c2d5115200451070365a882136902c4000012800c0f800d0800381c8040040500313140010342c0d514450700310b5901c242403800c0c1800030403101d900684014400500741580b00e080c10500e2107900d4000c00d4580081f48501ca21010103071401c2ea580040003904034580c9680c0318605015868812003401090311315120410600041c804041441d60800700341510806003034001c200010034000701355010903110b0384c21b103080c4404541d01280c0f580000b100c03818581d58071200340c00b100070110030f941980c41209162485007001080d010a1240c480c0400f503900700100d0741c4910110901442e03040e00508003200034003080c00040c2c050342c0c1e003142e0014141402420080300003106192030b44900c6d03c8559140d1108010001c260f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 320433741 1250 320432491 320432521
    0x11a0f22020a0914090402060f070c0608190c080408132105010c020601062c0306070f030b010302040b0904051e0414010612120305180312090f0f0a12030b040c0206 72
    0x10351390300d41459030000304000500d004000f80c0040e218140005001c05180c00d0300c03040f40c28169110a0441946540380f40103444803408540802180e10b60706000340e0016039601c24201d00e9500d80c1c8400141e030b110f544607100300f504100d120100101c1003000100d801c000d0701c5140c0020780c001c1c60002c2d09806480c42c0c12404c0d0380300010300c2029541b00100600c0031a80180d4a00c0042c2140c01508103001951038100c0301505c1c01c4412184c05009001c103001e529548120342d0010740c03296803018440541d800004404a02c2144580c0b08513500034400d41202c0d00d81500300b15003014880740e42004540410181c01c44528094804690780300400b200010451420b000344401040c000c6070b00702c60400a6111103010300c650f4401542096a1180003444124602808244d0b0800410440e6258503404011401d07200041d100c080c11071140190322000e0910000306803802c83d03804800703072902009907070315800000c13442c2c11050241522050601c505031110700c80d03000180b20300c0e4010103480c1840c2900600d404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 320434991 1250 320433741 320433749
    0x608070b13090905060a02090301020415110607020c0d03180e130314040b0409090f050318151603120b03151e06030303161806090e09011a0f22020a09 66
    0x40d00701003003200802c1012440300d500181b006009a0354400c0702c0c002a0092040303400100c005034548010544850744804404c40004e1000d088034140d4440405c02d0ba950b007205100641d00003021096100001d1080040300c402801a4010800141d10341b9161141050112074085951010300c41c00401e0550104401001c0c0074031001d840e01d00340c20302c000d0162611943c0992440341e600e503a00e03c01007200c6100c1ca8a041c64215099940302c0c0f6000d40c052001061030900240710703a5240e0034103101b070b41c240d42c200c2e040c80a082a000d0100103c81d40d0682c0c0a40e060803101a1840e50340e00e03400c207a41c80074810074903910701402c141034880c506031004824040942c3c10610080c2440760030002d031074400004032600038484203c4030f240482918412110a0030010003412050031031440065440e40140004080c0d45d8920005a2240d9411108608a071020028006115001001402a824442a00b0046e640042c111204204c1694401001d4600381c01680700c03015800501006200d0b0702541000c050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 320436241 1250 320434991 320435009
    0x3110a14090103020607150f0209030d05030618060a0b0a03060f06022a030703140102030402010207170616140a08070f0c0201022d07061101110a20010608070b13 71
    0x50940d1000300350404014000280070382c0c0f000905405010351000000854040ca403418004c600790750502501a4120b04c103803078040e1088042d07454071640034030280c9100308009003d001d40d002041843d1129010054001c54210b8528940860003449040c02080c001d00c60341c030080348892801c1d41854410000e50301400c1190000f01920b0132600e0404580110790161420700110414080000380c180030302c40d440100111610007680d183c451064001d0743c4268002d03025211b0b40c0e527981981f40c541480c07060241103150410030010705030410203154000161941d140031107041c04115843c110a511000604000c28109030030404803036803100f540103010b1020f140250711707580c031940042d40d42c484540503244110340310080c01d8400c6540d0000042005104d004440020303660b0b031006011441d81c100b08284a50030300410080f04d02101040f151030700110780c0c650000f1105213040003c0780103072502280442d501e81d00300080d02041008000c0c040d050410b0420780e1099231070f0040e02480c9140d400b050304 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 320437491 1250 320436241 320436269
    0x9020c0d0906050a1107090606021c020a030c120e0913051605010c06020c10060b0c0c1807030b12072c010b09090901110a030519060e1504060f03110a 66
    0x300e0b50340241074860400070340c2001c0011040e102e01150030041143c0121055501e42640003070141d07400640103c0d047c002419110078100c102c242282c99926200002c3c002c244942c584400207101c3c4040a641c2c2a40b0f8940f8070b2a00481c00c00094481005440d050741c084500524001030001c00d001000148020140c0c41c418945400000f0300070a443c21800f070101c50b800300b071001144105100780c040d201c02c010410014161540d0f40301441e50881c4507c14400c1c4198003c050707080c10003481c00c0d0b030708484c0000fa030381685d950145c00700c0141c03188001e42030304264a2025054a60420001d01d805050020704198005035100300034600c0400042102041000200040064804800440d46111001c5d0ba01c14000d60303401c0041c501401140c6021601c09500040c00948168143c0c003560007070350300e4010080c1080f440c803007001c242e482c0c6004a24060403c000070030303d054441400b900c2103440285c00803d80070703a154400c480740b0903654000c0e41c0364151114001d00c50714140354008007410103100528a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 320438741 1250 320437491 320437499
    0x50103080711040c0f0f0c0b0103120801060302070c03020d06023c0313030c02010c050a03020d0e0f03060c1809010801020d0e190803071106090705010f0e06120c070c09020c0d09 78
    0x104005c1c40200014069804042c501807442103c2640313905401035041103455a5030f140200d21881844a00d0740040d00210001c2583e5200340200c807960351704070188245d841c3c1142c00f00441c000340b0520440d0142d80c03c00240880321001e02c0440c140110626203040240c0c0c2000d50740c4015266000100c0b1240c10800402050f02c01000c0342007180c47d09403605419460b000c3c80142c6a15144c0032025080384121448d060030107a00107414249411641c2d1024528200307078092100c840321280c0706c640c7c0354005900140003c0900700240c06180550f6841203c1000da20001ca03500a41c00e8211003003913500029582c42c03c0c0260b01840c52aa41000010542d4450f0303007103070f4841514504001403050070004085001c0920540194010b0001d981c1a00c902e401c203a00d1480e680c0140b4850b02d8040340c0c0c1b120078421420300840500344850760282515107040185540d030340400c0b10052003490301240600005c404903004150300c0b00030780a80314005a03074840070700d801440c05200c680303100704221140d0b000b80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 320439991 1250 320438741 320438747
    0x90409030216050a272903160302030318010216030506010f0b04030b0c070501020d0f0c0f1d0108061801030f0303050c0a1202090103140c09121615030906050103080711040c 76
    0x15520080351217407842c410b81e1002c3c0e060302401c07103910001c011601c200306803e03504000180810341c0250440894601d40d100d4503400054000600c4080d603d0b400600c82100c0e9510407001c0c144c05000140b042e96400c240310800a011712000d50800d89181c2d2018005102047d51685810003814150408600b4a41f5540d5900c464010050680d103030000d0104515040083c00d405031000c1a41e400002d0042d07a030312110700300007000b651810000261070009107240d114040c0104040c03010499200006600c0c4260054a484102401d166000b41481c0130f8001c0081c08450168060341c4108042c1c502c210f181d080c0102a0741c0d001d081c003000c10404101c5c0d02c0025402c0a021900c0d51600180540c41e080300c02c2c01078005250b41c0c800d02200130b0005c1d041080c83c003822401091200d008a450b8801e103100061042d990307080300e000c0040701000c0c0950500400c14070808415103800740e0b18020880a440b07039548015107a082c1e1040340c0610002c11a00c00b040101100c03220500020780d010460a0b00e510001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 320441241 1250 320439991 320440019
    0x80f03040303051806030f0412030902010516022103030108070b130302011d04090804081203010f030b131e060f02070506040624150e0102060705041a090409030216050a 74
    0x40030310400181c1c500149080c000f5410341100300800446d100d140c8805500c5c20784408480c01c4900c803410200c5140010300074031501040c01c1e01a5281810324000200b00001030020240c140c0c0e10217013200c0a22080b00dd00c5200c02034801654002c0d603200c0d49800c6200749071460702e07001140f01460600083c100b440380002d120003180e8092034019901d988110801c0c1d1082c0421400e03d80141c14141c0004c184030380003008204a5980c2d0007150540c5940300040d07001c070300081c01b6580d96004040820008144441c0801d41c104465912403821200300d40d0384c081c003442030308441031410a8aa1034000900450b84900c240d141d28440055150020b0350381c54680350100244010312140c3d0340c1000020603040408540426040440c210708155103440381c00c00804641034803280043c1d0302c0700903c03189502c007140542c001d00407a1901802c1506102d44541203010080300c1c550110030500c56612684d44601034800d5540c001c0c4c01038450404140080d4a07082042e4114600508481108010141c141501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 320442491 1250 320441241 320441243
    0x20c01090812031017150a060e060d0503090607110f010302180111071707030611070503030a0e010209100f02070819150f02030408130608070519090b030a0e0106080f030403 76
    0x403d507070740c0d101c0e03110440301e007440c0d040102d400081d03e111407400c0d02c002582d4a844100c0684641140da10b80440100343d030924090000c041407038030003061306402c0c17241c04070360028482e5050b02d05004030b1001060b455000003038203403950908040401503c1c2840740d02d90017411030070704c0c003980391443c514280c11011000303c052604100d00d41004c40307412803042c4480c0028040036200d03490b03200401e5110961303c4015010660310546400c068070350740c0048074100d4186a80c854003860a503666680b0000082c88146083d0407195001c208a0703241c0e90700c03040c072240c0c001000e40b11254032842820340249024480c1e084880c081d4484421821150b1000c412444002c5d40098100d0507200a1003007403000c0d0620300741e241c140d14004030074002000406000b90940400031420b404a103555004102c69527982602c440010510030055680100391560403120f1110381c500300104a51b540e801d0142c499802142e4102c44103541d00070424800c0c00a000e020010814400100503400b058504140c0300d11807480 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 320443741 1250 320442491 320442523
    0x60c1b0311070308031603060902040312050f040807060309120206060916170f091204050a05040b04020714010c11150606131a09100c03090b09040605031c020c010908 73
    0x103440340d03100010480030b80a10707030189255482e81800701c0641d81800c00724001c40b0220381400000309007680e0510903641100d403c201401c503107984185044c0c44a90022181c141100410000803e9407081002050010001590002007014076410240c5501d1001098942150008428440e070ba80e83e007a0f603a03400150501440040d1489410281c5086c12148044000b585100c1c042040138806040701a1007a010301040e24420319404980e07812611517401140e0340329808100501c05410642c0c001416184060001451311140b61940761401008600071441e0ba0344524040200c664480d49003100d1305480c0d0001c06001100590032841c0d500010b001f18021000410703088080544544268010100d0032441d100035010407403490303c81d81c800c05e10035000703505110300c10641900c1800030b0301c0582d8143d581c06068601f40303400045103921035249c1d1644141c4039140411695420301802e0071b00c1c01104140f41c21080b8000c8041e04140d54941701c42d060202c1424104508a00803c480030b0404040b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 320444991 1250 320443741 320443757
    0x11110050a091a010602120304051506042406110d050904020306011718070f0509060d020301020d1d0736060b070605090f0712020103020c0c04110304060c1b03 70
    0x4800c401c010140007001910b845101d0900ca070354490100350f002e06a40c40c030350035540080414a00a030561100b0760740204070358400080003402548000d40650030010040011540c40c4191261070f00c1070748211200401e54190003000c018040d08000b0314031440c2404000303007500d00c900303100141040c001c1010381d40c0640c3c2c00000041d01c6a100741c018404c684144400465182040c0170b122103640c4820800c503c603481340741408501d46100052107012140f004002d2240c47d5541010302600c0d00f030001d0220303003640d020700c03c4482d011024090303103d040402014607500d010a400d0307000d191543c60340c0074452034110343c0c002d0102920011640c41d00300c02c82c051a88910354142c81c40e00020845948090144370300460004104030301ca4015500509000c2d0454080f0320b41c04a529466a00902c100304580d1401040e00c001075000360090204000ca40381a01d452015440201e8103554185400c04c803150030020800040200900c6402c108540e1843c2c400d032040e140001c4481040417400c806030600c0420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 320446241 1250 320444991 320445001
    0x3040905060f101e0302070c05280b0a02011427030408030f03250219210306150f0e09250e030c0613061407051906050601111005 57
    0x105410708180001501c241c0342d030052508010030004002c0d104d155444e801c0b0802c4003100c2e01c0380c0240c4000c15084400c0c040414034000401440b41c81035018044200c0040704e561004255030503c000062815154427580d41c0303d825002401c5032200b141c3c0b10054102201441904403d004c1152560f00c51900002a5282001c00d95031075805540d201241c41d03c00020b9610300021000301650113201284144540d40782c2c08100d0b00064400000c0b10001a800098030900080202c201161780c58000c001005000c10b440c0c1d0710080c04c44030700c00e4050101e910384074100440e031030b01048c0c0c02092010f4070341840c115003003d800812808004a0462007402040040b800800075601060000e0025403044040b07011244c0c0054882410203010314464040d0304114a5a41407060840d03154000710984c0e071411500f00304c010b1390842e035140c640c84d0119909104501c00500100403148446501080d2031354840d00c607162000503103500418103410030000400c1c40000402c0026481d400038000c07503004c00c50342c1c1e0f4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 320447491 1250 320446241 320446249
    0x100b0309070501110313121406060d02090613090506010e010b04080d0e0117040c08070602010c02061306090212060f07090b0a080604021c0b1201022104050715020d081005030304090506 81
    0x501c0c19880401c0d80b60000001d0701c95802c00c0301c107d51511418011645440002c88141c94100441d21960880d280001440061070449100380d0b0100d402031425005002840048003150110304080342c0307076409800140f1511102d68030740d500420b9448040c0d45064100700b200d07612107049000107002d00441e210b1032000c0d6801449004900364040c2402c40d514a031a09041003144001d100707880e0640030b003810106819106004484070401d0a4000b004251511180a0381c0240b250030190f801c660303110b10200045ea284105007008108a00052900d801d04100313001000c5c0c4058100310610510b21000c0041182920a8510b0180300f0308000030300d6583d603804035010744120301000c000922114407103a4034103140e034010140500107a0301e80d0348403019448007500700c2c0f182801201544004031017881c080d5420050302c40e0b11a104009a401c410f9440f00d00d140352010300448503015070070065566020652000100b907000361081c15050b40e041c0f40801180d00c0c0d118034002e41c0300035525100010000d4403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 320448741 1250 320447491 320447497
    0x3040c06210507022d0a080d06080303040b04150c080106030203100816030311030306010915030b031608060609040213110f0708040302190e07030230100b03090705011103 75
    0x1940360051240e0b01d0000c0c8000e4484c43c942c20241902500000640010034100100100001d4007a001b04a00071058581c1d200c01d8000500b0000e59a4450002044018052000d18001c510901c00c00010f030425252032833280980d841e450038441d2900c0700c04504903038080da40a045601a0500594903201c0c000082c14041c2e044d000202680316002e500e0081070f00600702c500032a4042d584c0d0050140001204c25183d10050301e00e04e0014800b0041409103064055400c0780903075043c00c0000d61781200401003424140361240d5042400c5501c0b84c1042104820300696900c8001112200700b5032034aa400101a001d100103802c50040d1b60f0007002031500d24020441e00e5040c45400c6450729a00d05181c00300d1207a1190100324028038004e68448120520041140300703550419441c0d400690326020214002e400000c148a281078000300c0e041da02c000c0703103008a0214822a1010101032030310700c4011074803005603030141c002003108100700888204080f6010054031801d107464814208840c0003a49180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 320449991 1250 320448741 320448797
    0xd0b030d020c010908120d020a11070e04060e0d080f15060f040305070b16020603070e09130605060319062c1f1404020d150f0f05090303040c06 63
    0x88200c1148414468000032441541d480980c0c0e00c280c036503103036410795807110080e410384903080c0c0c13040c41030141d20552a009032416040602d00070038010500c0300140d280c40a076601a0b80030780c0c058000c3c0014040a40548d041c1c0848010042107460141e883c0100b400034010b140650114043e00480c0804c7c0400c0440c8400c04001440a500c4403400d030600c20680c3d00c1340c0300c01c0f202442003d20004035140442c0503a82401c0507040c2d6220106010303003d0103040e900080c80031040280b4200854003a41da40d21140e4082d40c6000c2100110307411030302d051421613002401c00b610a60120b080750220880414107208a681d10000128207030940801206281c032100c1c0f0901204e003c082e07500142a04001040205298001400d43c2c4030014880341100301d512202c1c3c840c0c215007946000a015007800300340100f04602c070b521803404030141811040c04851080d001115041e8030390104800c41041402810317000380c82c0301e01075072540c1040e682d44102454603109100c14400602460859213031003019991a00b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 320451241 1250 320449991 320449993
    0x616060506090703061203030c0509040504050109020405061914030a1725081207090b0a090302011215050d050307020405010303030615080f06130b060c0618010504080f0d0b03 77
    0x140151a002025000c21503141e4050900000001c105610a00414045920100d031002c03451031503480480280400c0300161050040420401c0d18948541c07152030300c01c500500000030703885990310402041c2d85c0d000d0001d51149002154144060705100007840482d201c04100c40d607a807a090703000c203080c868600380c05400a43c90400011104001500824950382c150172000c1038007403081000180c00340111030107880c0b1030050114005105a00211540000d101c1c00e01c529642d50700c1c1d00c2130314281d00801c02c020004210010030030031541c00003000a07079510310300c2e0140070910038210083d00b818a07074460b031849a200b0b10366060034003406108507181d090f0050014085581c4904008e0050076162107000c1e0140c000390002400c013441811203a000d124607442d03075032464030713084200440e0fa261048201c881e6039a41401c140ba6a03200402040612049009040e4a10342031085804201c031104415099905050400002400a00484042c04800c0c4d400c40c0c0c5a001188080e801004a402c4c0306400d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 320452491 1250 320451241 320451277
    0xf090e061012051317070807030c0f050a0309060e03190b10030f0605100602030a0e01111002042301050c030a03050411040513110303090a050d05210c1c08060d0206 72
    0x5138200344d548015280c090040e100f840d00d20712491103118401c992004c0c01c4901c09115610020384145042c40c0454080d524841d4601c3c5551201c6041544001c000c90205411070010402c1d1504010a02d10800d4202c0282002d02d03800d202090a540c0b800c2da00a01c2a0800350010741c04a54111101000d075030810751010386801107207001b42c020700003903d540800d5401c81000181c0903200104484501039613544100e141c0c01c1800c019a440004070480c041d0f9070042c503600c43c04940c8a80f018000516591800302e8200d2075010701d02c0c8c0d00540c01c030045030401c102000349912649002045860329800c0c0c2c60005450741e19424001e04101482c240181d01c241003c0c2401f00c0300500c141800c411600032720328403280c1b517241000c040c2da91240038413050300304d00b10716020402c074900310446c91070040c0120240c3c0d21030f0740c0550800442000c0c45941f2401a200440c0c405440e05081000748a58400316110a004030031392100901440c100510070382c0b00310603e4051200315111030080d03c41b681c000b0000112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 320453741 1250 320452491 320452501
    0x112d0313060201320702010609090317160503150402090a0303030b130e0c040e0a0c0806010623030f060d050129060301030308130303020405031c0f090e06101205 71
    0x159126548208401503003020440030312800e0490130303c407507440b40c2c000c3d5051181301011485442d0310000d041c841036550b18180024034800c1405a552031a00c2030b51201e024200e0402c160084040140000303030044000450300711082d03049800c907a081003420341ca1000500c078103c0064064480e90048030707081001441d00004160300341e08103064452040300c01403400310f400440001118810741d100710003680100300000281c105940b0106480490303000362420800301c4d84480001c000181d20078115070b8000b1004101d102c0d404040c1c620312010035800300ca110312086184a1060102600c0080980644404074084e0f640396100a020680d00000a202050107514203421444440c950340301003605c800c00703588680c6003501c1124140c2ea41510b401500b82c43e604040031820168081c210241a8200000b041c0c1e642d00304900040701ca070210320707600000c4d031800c001001600843d036800c052005075a800d1050400748003816500c01e209441c04942a03800c0002200e8542c0010700c26140309143c80e0600c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 320454991 1250 320453741 320453767
    0x92b140f120c06091f090303060302040617190305070b060d050a0507170705030303010605130b2a0a030207180207170403030e09040f1e0203060a1b112d03 68
    0x8507100b20744405954003a640d00301540d40b1554500e10740b02c61105083e2030200c03481d042d54000444a40240341c0003400d0740d140d501103800c5450a800c41400c0c4140c8544003007003540100b1042c581041e0f421942c480071006650003901c2800307021802880b90030540005030f4075485410400d01020342000484080d40050f090817a111102d601404200c0340208021a00b40300f4001444012144050f004510b543c2c41e200c01250160030500da00700385082041800141031102e0790180118640c007410400181041b0354a101c081090010008c00b01d8101c8c019540120f41c0100f03040080f5145610008002444042c00d840240f10b0030000501d075100284400405002c20400380c02603a10a48664000e078000c64100600d1000449008181c0400102c5000c0003454036106000e403607103040c045502c003030100c1e400681000012504800b480307a50380c00304211480300c04402c0280c01e2071407c101040681e458802ea8990010f070554162080010781c06031a044a017140414148070440207882d29aa424a804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 320456241 1250 320454991 320454997
    0x60423042c010b0a03051e07050d060e161d0703151d0703020f041a09060a021b06030c040b070c080109120801060315090b1311092b140f12 61
    0x3041d0961034004610081e08141c0c0307000003030702d400ca0000c0944035044c1107003501401000d03009820a000d41040000d0036100e440b121b1a0360303482800003082c0c8400b01032142d450048a4054025041d1082004000f0f41c2d1014800b500805103070740c112001503882a4090b009020b080e603000c0b400e501080d0300011502c07019a0382405000030940c0780c403803540766800118164040e0070020040030780308100401800c410701d01c26807043c4190b440020b003806405000501940c202560707180260300107140541e031a5030089501718280303104480366030850174840d24049050040d4060407103c001e001840c0420b101c20008244014080a03000340618400303881c049907002c00100d00c0301e0110344100c002140d02030180c0180714201210782c41c4844058549105071001d41031200c85141c03c07010f800300c1200c0d15100c900552501c2d00641c0e80e02c55468401800f03210200001c0d50354001c4042c2d5141c88070a80d2182c990110440a0300910700c01250031000e039025041142c81040c0030443d110b0201c6085404803440c0c05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 320457491 1250 320456241 320456321
    0x2010e090a2a020c100909050a020d2a050a0315081e010603020d23070b130f080d0c140316060605030613081b0105100302090606042304 60
    0x2c10600700c019010154080e103811041c00c00742c0c00c0008261403500788401c545010698618140400c0343d66200c42c9000c461007a038049001d41e400060680d0071348481d000342210700f905103951503041c20804072950741c00c1e105044d54400300300b00081d0314a09030340300c0e070009406995508543d110080e502c01c50707076a907403400b0a40c0004000f42c0204240c4c0700881803003810126034001d450850b64007002e503640501c80612241000a5081101d00300c4480350003040440d0141064404596655078034a514408000d80380e40100d000d82e2075070ba018006132002003445001e0706200d04200000c065140b412202405585405914500c40429404000800c1440c2c2542d283e010f44020071003281c49900b45078075100205c03a004c0d00f22420448840010720b07407800510208114014610112203400038050030f482054604413442c1140d9402031043d4600400c10a402040459245140914204802c000003410010481c080d850305130003e10541c07925000103c030801290340d10420610140e5a400084105140d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 320458741 1250 320457491 320457521
    0x4030201050705041212030e031605070b04030c09020d06150210060b03091903022401030b1510031a0d0f0b060303040b180d0b070804030e030607050904050402010e090a 74
    0xc085000b040c09141154262007081181443c04e98441d11100b0020710207140010804d17607103e100100124042c0041d0000c01c4a00200c480040818200395290a00715005032000d140c04000401c00a0f100500c0c440c02c03600c240c2e2001d601e842c1070220407401442d09500900d0280b0038006903071200d81d404900091043d4030b40000700501600d131200c3c0551030104540c4015140d200780c0c0105956500d4880d9003100500c030b0310490341710103080300b804012900c41a1070401c1c03040d5004010f0042090503102c855101180d0080c04442901751400a030307440f90b4100e00a4140341d511420942c508010214070725031031074044c0c048260900c0501d0181c03040c55004900740c828805200120300700e4500442200c0c1240c0d0188a143c2c104203c078aa2885d885024100b6250b11001404e0b00300001458035440903ca8040c1d5120490245898140a03111144030b07000c00f8404d8101000300300010341c0010603102d032500e040c0c0e40010316583e540f0041c0c0d8a00c5413035482c207034019115000c000e9500b1040c2c0141812540c550 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 320459991 1250 320458741 320458751
    0x105091c05031306032d0b0a0305161a03060d1e0602030f180c0307050120010609140f07140706150305010608070e0606030609040c030f060203060906060a0f080901200304030201 78
    0x454246039050300340c0d100612000070b44090008050060308447e100644c01801c4d200f031507643e81e4170b2501d8481074518001c80219120420045550090314211109104615452652411100044800d144c01b4401028190007994119102e920151451903060380403038110b549050650318140f40030403c071101003280148441c1c881141c40e020460010030310001d001000e000b03082600654050403c80c1c4c0d00380151f80100858a800f01003409010001c10b401400020201d591107143c1d16680001407a04041c0345c01c03007060007840d640c0449040013011800c5421511503421740f604001600181388548240c0c20f6010b001300038072406520903170844041c10b04a40d201136445543c2c40210a048501f254000414000210a42440c550031907000c2e00c1041d030034103466126510501016200d1406840356075000c01080030300d042290805070004021038034a0b00340100311134001c102e042040740140130020450040350340f0900941191118080c18403035030080c0001c850034280355410440d402d400542c200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 320461241 1250 320459991 320460011
    0xd06061706010f0f050c01020702180411100905040213090509060a0524130603020603070c02040b040501210c08030c0f0d1e03020307050d0218040b010206060105091c0503130603 78
    0x40000707000c0c1903030a1310740e01442c002221080d200380d00049038840c40c030354003009030700c0050f551055a507070f000343c6a0045042500382801e1140c0090415014103000e1880e90441030185500000321004440c02102c01580e180c01003148000072140d268030003104d107030804040c030480c21004101d9502c0303003103071290070401a550182c5401c4050803040d0100d1441c018403000039464144491042004810321001003040f035581c1d808a40c5c40d60007100c400c0006420720700d829045140c00c1c01012860082100c003484294188071010440c2003419031018800340c803480e0450308111803000310900070700b061030542f6240c0b0303d100c042d00c0c0c90312147c2c10041c0c1e40c0d002d81944400c0a9000b00340491900c10400b5000d6641201d0f01c0c0103500961000d8091000e02c00240035803038910004e4002808031584044c00d90030484154020311058840108180b415034001d0020405e8076640402503910600b011110742070300310840c01c0c0c1c02c90400300805d00070300207010004420301301c3d0841507a10000c858241c4e40400000b048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 320462491 1250 320461241 320461247
    0x30b090606031b2e02030c010b010206060a05040e01090203010513021c03050301120302030910031a012a08120a020304030206071715030c04060303030e0d0504030c0b0c030d0606170601 81
    0x1d010000d41c6294820366a403550f9042c540d900d50b29401e034444c0b51201c2c01c080703000118284054981200d0040e4400524281905428000da4070440400c0c00141500c0c2000ca0010f010429030b800b483c0d0140c4c1d0385034100900e000c8c094001d8444c99401500810003410084008508802040000d90085420000c0b25130041a440da040c52082d030581e0300d01781181d0810603549001c0140e040305904600c01400842002daa1300d070318070740280b45944c80008007111203c40050b0303820980c40c8401d041c230840304980300088003003600303103184050131720400040700c080d81c03820551902031001c1850700880c14000304046480c0d2640214010350080d001c07103041d65204503045403880341b005001600840c145000c20f044094101c44da40944a004064540d10025070012608441140e8000d40011f900c1c3c20415130101014024403c0726109881c0441c078003411034881030000c018610800d1583c200c0080e101c100500c0070300c20303121100c3c401c01080c0515030366600020031255440603034480307201d40c90020034040d40c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 320463741 1250 320462491 320462503
    0xd0e03070209040605060112051501120b0f040b121f14091506040902060c0a0309090207080f090406050604030606050901140102102a030e0106080d0903060203040204060e01030b09060603 82
    0x640100482e84594550765041c1c05014054945070610145101411840c03145000320341c400c203900c2a0a2820780742400c00108500340e5047c0d008182c0e861701c40c95408a49400e090034540d10815103011400300e502d60041009120002c50020490040d07100410711440c090f00b0101030000000e500744000104400384008071b001c181c0d000001a4405c14080517120384050303085d03920590007800011410580e8010801541c0712250010054110380c004004142d00118440c2c00351142180450812030155141d4600313101d200d1a400c0c820801280400341079941c1e82000c405410050403680c2c4560741c3c1d14002c80944454010140b2907001381d800420680c1d0500c00c1c261154105a00270600e03010685550b00c02041c0d815440f500880042200c664440400c030300b1303c1c3c1c0b924200ea03000582c080c001155a42101d14903005210143c11000100a1700f0358040314040030380790807400050b9207131038510010340103120310b9014101c495600700001081c05606c00c0424441d041c0741069980d280d48031410151210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 320464991 1250 320463741 320463743
    0xf0209282019080c040f0b030f0f0106050904050a020408011118060306060405090402031002220b0a360e0f1305031911151801060305100c12110d0e0307 67
    0x100e0903000b0401c000d202d401880e801002140c0c2092a05485034490002c00c3c50790b800c446c482610000c01d100040108100845c1d000c24400c80d41c100650400000600380c4c41500380d082d220f50f17241e10100340704040c01e60443e4010554103000b080f80102000f8410307003540080503860074900f00e0644120b00d034100300085900c9505c0007841d0501d032034100b00800400c0030016000366013510800c00c144600d58914802841e090180200d1050322051200125a00c02c442e80c002011640081c04861201780c0c100201801c12180711004510b82c40040c0040c100c0d1902c2c564002c1800104074000140b40c1c5903c2c200240039442584400c003280e50b941c1d2041c0b541406c00e0030014026032007006400c440380c041341c02d900984680c0e883c0140b90384a20003200d0345085014400c500c0c040203204140a00469440e48901c16141808024401e01c0e295407125500e4180c1d00505401c881d480f03101c6180b440b072140840001c6030394641310070011100c0c0310660b40d070107800505520708101c0c0760041d003c442450000aa521507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 320466241 1250 320464991 320465017
    0x901120804172a06030714120f01090c020304030f061d1504030f110c01030216080409020408010b090f160c02120c0a080106030f081612020102030a0f02070f02092820 73
    0x1038035422411a100c2d01401f801920b01801840707070020407070940340c0c264080c01e000e030320000c51075041c10501400c8500201004041d50300820042001600000351001d4580d0004800103c9500c41e00a0200c1160032141c003a1183c0655000e0482007070f925900d09000d40d019071b9405401c6129007000359000030302021140c0065020314a40030300ca611a030001d00700044021404c0d49210907982c0c40e001181c100d500a90b20850700443e05000c2c10009128882441e071084400b101681440a40d4540b01600074200e1080c03c500315402260843c01048207040240d8007804444018501c880202d854090081c1c042c0c4c03041040700c80015100805004080c15207402c51400c0c0001117450b0348000003540300784004690b21854004407000b0840c500181c034031059158001507038920308601104101e4151103140d6200c5403040c001c401c003140049812001c105d90555008049494051090f00c5a8011741164818819191854a64003079a81c00c40300613055400302c00e01d011880c0000d410214051812030b8458 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 320467491 1250 320466241 320466247
    0x1003020a23160311010905070503010509030307050f3402010f092304060b040803040806010f03080405010f0c02030607170609041a2a070b0a0b0901120804172a06 71
    0x8029120001c0382d820b94440d04161308000310041d0400c2c00d440d83d170075041c0c6694005100c00c0180341803c1c058141c0c44501718002e10b24510b0825006800703405247d40000c0850404689124003000403103000802010200341003400042480200d07405c0c1c0181030303089001408407604059843d0007a500602540c1c103c00d4030064542c1c918800542d81900c040c001036019071180c80008031f41000e40e000380003900b86c0d00043c40c2d07924200001140f81c50b4043e4800c0984c40501d9900304046003683c0e0580342030314400d1810800a101d10340e400c07902d014441d400a581406100c0a002071142c10081d41c1c410945040d1820015035580010841c1e440e00807100904004034a480d203210034112003500d103500100394180740080001e00ba4148460f0341c0049a84c800c030710000560f48081c001c4103480954000b844030350510a449128012070341c03c3c003040c440c049100d984200980304101078241580d0191a80100f0859201c00421500e0750310243e412050b51000da4510820003000c200f802d640107407141c042c092503d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 320468741 1250 320467491 320467507
    0xf0804032f01110111030f07110c01090302060306181f050d080a080c070803090601050906190b030703020903030c10051f152a06060504020c15060607021003020a23 72
    0xc1030307403032000c000f44155a80d20b181c1c0078189006010b1802208000c0c810411407410307640c0a4424141c0440480481e03001d801c0000c0e01c3d030703030244000c02607a6050b603c158480d155a404203502d070940441d900703020294002000401001d42ca01c01005d2140c2202107400290b99200380520044d403400302800e6160200300700348285001f04101500450300c100741d1742ca0300300303640c81c0d0710095001610840060340203d40108018603140d0361071508510103d419a0075400000701c0e4501171401c521500300c4460001c000502c046000742c0c1aa18050006010b882d0368460341001991101d41003070300d01c0000c2d40b0b4a030100d4514451400d4040800c01d1218240e035949040c15030070302a2050000d8400304120010702003000c2d241101502d090f03c0040f001c038018a0082c03a00d80030050b2101a08881e0056105201e4800c0d200c20000b0041d0841d600c40035400c04607100c00c40410614810200043d4105840072006244a41e0543c000d00203091603594100c4400d0303400341901c200390420441c2030000d02003404499 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 320469991 1250 320468741 320468747
    0x150b0118090207050307230c01110d0f030209061b0114090a060209040b0d1202070501021b010507060b03030a091403070b0f160606080c09090601060804030f020a0f0804032f01 77
    0x2101140c000d00880341440751b10b82d101300f82449124403022503004c54940542494404000003048200c090a242c58403400600800381d03241c2e80410f110003040040c1e00d5141e80c00d8003e604441510a01a2906070707036583d412a48480f210010003040350320b42c40c110410441b040010b101d94002c2c5400ba01a140514141d190031000c0e41280001c00c0e4442d580d41c4600c0308a69406010398030300d5202c0c8085241030340350150003a003030000b40d030310881c150b401a0080179840c0300b0740321380c8106c00c100c02d00b84251210018140200184050200307160103103c00030301800d0700c1d600903c0560444070400745014200d50248240360b128005403195140219050100760300c400d0b07144010304410b0801c10360410601000d6128401036030101c2d032001400e0707003205c0500c0396242001e00c50290b2018140f001881c0035450944c001b012048010009001c22000100f0020403903c2400b41610403500002c035402c5880941c1001c612990051000311a02006824851140503500d01c1c44e04444031111156001500c1c140015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 320471241 1250 320469991 320469997
    0x903020c030c0604052403130515060609150904060311090106050f0d1e050a0f0b0307120f02030a082a0a050a0b100801050901020a02010501050d0b19020d09150b01180902 75
    0x5420307051504102c0080c600b0b0f1910242d4030402501e11023445058042c02c016040c038801d19500410306401000308070442d25010702700c95149109a4078840f041410901b181c0302409400b0003103510a0030810004140a030358610301980403002c445290160343d80c0c04040d6454410722043c0302d0424414050a05034000a034080c41e8500360380011004034030841c4542d0011190100c40d0403004542e83d0004c110100c0640c07007404810301096009006003401c0400c6e08411540d035903c0285880c1d8421000d0007151001d101402c41c507135105200a844100c023104183c0760803030501488406850300c40302c003841c604000808002c50b58001c0081d240d5013107940c03909181303085c0c0184a10031030352032101e0025a22000b4404d00c0d209504081c00180c4504a1444c002d00f914010ba010724071a443c000007000100e036500c0400b6401900007500302103005201a04c18000e8019005030301c4100e0726000001041c8807240c41200190396400385e04101d600b182c81d00540d6030540c0b40c40c0002d000c604110051040e130010b5801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 320472491 1250 320471241 320471269
    0x6030203270703200609060918010f050316030320010e0708031c05010302130207061808130b0a020709021e040f2102010f0c061104090903020c030c060405 68
    0x18542084071808140204400c0c4a00071240da940628020403e0107003004400754002c038601d0103900300b803407220b0000350301b409030b00360f100c1c0311305000203000c162603032501028690301ca42c4030100103182da0360700c51840550010380301c0d141c0030f4000c2d502d02d1450145140714403803d8a625454016040000401c0c000d00e0800d80c0c5030340394056513607031491005040200821401000785070000c41d51915094081052900e080c00030b80c070900d050000500040e502e400078000c0700c511a80c0c00603110207107400c00401802100b10121071104022600c01c0c00c2c800d040d0020501e8840d03100c1002100b41d0340b0840030105125280c1c8490040c1c10030308040c0075520058004242c40c0c034654841d000740c1e4400401d28812a4000c0d48607003850f81c04003104114036210412901c001c03898010800800b200b150300042c010210f004100700410a4622401040050580c00a00c694641d04022500c960b181c0703564000408802c4d2044e0701602c18610008090710340051031112152000c3c1c01142400e141409110120b01a505 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 320473741 1250 320472491 320472511
    0x70804150c020604180608010c08040b1f06080117060702120a05070c09092d0303020c010213080606180907090c0512040c0609080604110603090f03161202060f0106030203 75
    0x1400c2000b50740c600000d0310262545143c0b00821806010071a001c0318406e40c4120070607410003412000740c0760440700e03956005030004064001c0b40d9030200140f50040c480d003042030f4002c0120201040c041e81c0441c44034143d0754145143c152010100c500e50380c0c1e030041200d046006901c0502101250614180a4446a003142c281241014803940d282100e19215401c42403100c1e580d04d243c0c40500110785615180c50b1000880c0506141303080c49815800716556102800b4581c00044648a0260941c11107540e45220082d020003c1cac1c5440003281c45030010307a0414450f03120914070710490007001d84c1700c0d401404c00c4801000c07030f01c3c502a0940003901d488000740041c88001d110504504c840d10152070f204600c81c107500e83d11141480d034080c4c00641d058020006503030080c010040019008520282c0320013048488a40329501c0351500c030b2400c0c0513584140228040810290a0b41401c1c80d0400801c501c50344000c03140c0a070104003240c0d5000111081d4080d40760307100040140b24007030390003590130840082d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 320474991 1250 320473741 320473757
    0xe0715020c120c0307050a0e0606090d0204050708150423070302130b03011d01080a030c150218040e030a0f0c061d0d09090c0906110114100f090207080415 68
    0x100000b0200c1d110380903440090380000c4031044030344c50240616400f902c812140d6070013150401020410462004142e20f00940300000d070309605541b07a807a00c12039282c0c028800d000910340800010040d02040c2c80401000c040d00344410f9203840c00f40100750540d034664401c41903859960860320301e034540184c00781c004c0c51b03400c005a5000c84007044481001e04030040d2442e0307480d490001e0056000b0914111210243c014100600c90285c000c640010400e17058035003070f400042d050a242c0d00304201d0510900d51688001a00d8071403440a4030f145140c800121800c110802c280d440030b40c2c0740c1c071500b81c010b000500004404402035004442151089000e054005401c00c1c10541401c10483c1e00180928240d120304168000c455004000501800040c1024000340312a06005003600d90b6501448081c400300502e01c05545409510040f44584540300c02182c90070b0801200c00c0341d4085020340708401e0328030400464229424001c65204c0d990054800e031030245003010908540340327507010180400c2060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 320476241 1250 320474991 320475013
    0x140d020705031b0c0d170703021e0706020c0303030f01030f0602120a0914010905030a0f18090605130605010c061a03010510140909030703050a120e0309040c030e071502 74
    0xb000500000f18040c5244840006050502498042503080141c840c9108582450009103110a0b940700240300700700150b04d9004d94030b000c2c2d0500503002c103040824000000195424200041c1c1c02d402c03070b41d585d000d40d691100c407201415101d1104454504d9803402c1000100000b44d04144803800d0580120f0b40141001050710070080b05034016903182c1500f540341c8591030140801da1043d90000f07400d510007000b074030f213590b40c0e40d5880c1d019080b0080140030380c8110b41c8100d180640001c200b41842c11040203034032501c0e800c004000f41100e02030a0300030b03411460184480000e502c1040c0c20307540140c41e030065030b500f40d550380d0000d80044446062070508a40c9a4855910240100c1c2c0c0180c000402c82c0516504184441440c0c5207602c0c51a4803d80e41e00052001540000c011561441c1d01840c0980d6144402c002c10360300104242d1400d0403051425440c006003150204c090540044211028000340c01c140c1c9049094503040340300d00304581c0004008000c9000032000310365a940041c0140c3d4890005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 320477491 1250 320476241 320476243
    0x607060f0209040501080f0703030e010507052b0f09140109030807150c030b1305040620030f0f0717060f1810150c260309010c180501140d020705 64
    0x884402400c03041c0d0003140d40819840e06000d11030140c445c0380014200e00902185d240d07507a10300341c80702400f0301004070a40105039114000721610a504141140d00b10002043c0a41004c080b4001c00b69814070703c030314141c045030302c2018004100b5901d80d44200301b050505040745501045c21800605206144000000190400d400b801e03006005003004c0c1101e43c481080c0c44155000c00c603001b000c052612400d100c969480b07008650944949910002e050b9a80703140c428010030821b00c2e00d58610071181841160179003104001c500c1340c1070f04150075850740c07680e100210440c90141c80b03400c0030401640c444000d03401c0406009a1050340145454483c03c1900c010030040958920714146894403401004010068004190000c000b0107002003052410014000c01e03180d26504000d01e1100da40050030078070414a030a454400070354a104640c0c9090240e1040c0c0201000c2c0c5042e00420801143c01e515803e0310440803085034010b03101c08071010103042d00c0b20050781c4030540020120713600340008008100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 320478741 1250 320477491 320477501
    0x6270204031505071805060f0309010608030f0c0705011b1b0b0309010204030311032a0a050115030308070e030d0327060504031b020a05011103190801060f020604050309010806060706 80
    0x244550b0020f03036414950401000c200c000201850b4203241d2802c00c005a4aa01045895603003900b00130355187d494909a40f03001d41203a910030081c0348000304216642041c0c04005010404d80c0d902104c1081e13507904011341e04410b0240901340c921031144c80c283d01081300e00007081201140500d005040036124000701480c0e40040e101c80c0d100703a5010130107004040e001100807030b10b010a4001141050680032482e00c1010300d0710000458003101c0301d56411099410804a410079078004004d000b101c00113201d40340c090701d6078402a80010103840119640501507038040c0e14800001e800313000365000205040e07014010240d04490138121980d20704c000881200418244588191070110b402d040c1820001c05001ca200c69802c20382102a84180050341d5004040b401c0328020300b01041c499140822543c00c0d0b0080131107008903c400024075800d503d41c0000c841e4188e070700b03945501c3c0c11510015800c81e900c406c1110f0044c52644200540b801c158082c80c0c0d0242d2010300249000d280a6282c0c0d5402c00396a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 320479991 1250 320478741 320478773
    0x507030305040614040f05011b0602160b0c0a0c1407030f05031e13121104050a090210050703050403171b07060801060f1e05210a0507030627020403 65
    0x41c002240034804168052100d044e040308891826003001d04288820742009514400c503070500a81c4202107801c800d003e00790000560304010219100d03088805203c904074408181212807a0b14903002030000c0354403800340c032400780c441e076102d01c0071178400d60316070103442c120440c0c000d254401d1404c0000050801c441780207101303218001440c0c640100c01540650034160b010410541c60090210f80005450b0241150445400040c2030101b40e0040c02d141903e9519000d010b50000e013050b08010100c8032541142c0032045c030999051224102140c012070300c9001d00310004000440c2040f040011514019100b4441640001810320f4656044906125840460104142a00000742c01c21454ad005629075004102e039040c40444070401500040420219021400b03000c0c0a00c4ac0e50110540309600742c50296180000e0111218641c410100280c0c0044804c1040e11b810300300001d4290740f103401141e04036261150a5080b0303496487c0c040420004581030b00c40e070709900380000404075500d404070003102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 320481241 1250 320479991 320479997
    0xc08070c060f230105040615081e073209090405070806070c030905030d050f0307140d09020a092c0f0a030306030b060406080c131103151c0b01090c050705070303 71
    0x4008076140c3e41500401640300c144150b00d803910070003800075000303046211944c19140069a950b100418000c00d00300700c4041407031a020340002c100c400c80d001103440c00076903c4034003048446100c18046480301004907114021a0310140002c91701c0303040820071543c10510440503901030720340300d20b8121301d40708e01140d101c400200c0314408501030680190450000d031206501a080c02c0d0741c032180c00b030418400d0440b1100400800800501ea0a2241050001e1612508201c55650344150700304809408081e40c168401c40182800180341509441103444650798244040341030030303528801d1007040c010250a54482d004e15904040c0c0aa030034800701c40300b0381c400c0d200000c4840c2103060170400b42400800e000d008500d0840c1c1403040c0500059070741034061040350300d0b00e81100818244006030600c41441d45140030007000b0321401121744442c1300d003401c00584030380c224564131540b0300450550f590303400303030045050000503c03020b41983c21810701c810f00350030001c2c541151980c40c0c600d0140c043c1c3c01a000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 320482491 1250 320481241 320481281
    0x625080a090510050408060c090d05060405070f08061501081905010806070807020c09063007060e06280302210406051305062a130302010e040c08070c060f 68
    0x2071424a032002d004601d24580107085c14105281c1d00e603114000703003100d012074001203840c00301d694440401d1810317103074000c0568005080c10700d49107503200e4940c000c1503800c090890b004204603100240941c0700d840c15140c2a0300c030b41034500c0190344003000600b0b0340011900f5a070381528464418000c080c02050414024410380c0b5013484002d042080140490045400841d21220190f84942c07900381c100b0402c80d501c1c038a84420b0305a001704031000500018011022600c01d09140381c0100300c0c0000c80e0300903102d07291000b6100c0c0c00c220940c03241480c810000301000815210900030100e03000100c0e40213080c0186003c00d10140700d0300f02100e0000500390391007076034200010401d41d800780d243c0050380a90006443d403c965038064031208010000d00c00c50300062001c1d0245001c0c580b8840d00040881b03a00795450b0396034042006a80000d000aa000c640458943c8550f03041074440c0465001e401e541d400c810b5111903104603601c004014090790300b00c0d200c0b400300102d51480d1040803400d2070280704041c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 320483741 1250 320482491 320482499
    0x4120305120609010e041202030913020306030708030304020915030c120105040c050402031605250c0305120301030b0a02130513060611010c0206010510050408010606051b0105060625080a09 83
    0x1d054000b8406030250381000010043c00800071304094000303601807191700700040d004008170300d1405401020b562043d41c43c4060071540c06a58001c0d4043e4a0640aa0307102c22b8860f0302c499074070b20094034000e40000325000002c102c4032040e00114410322008050b1742d2008004400900e1092808540041e503035900d200b404100407092105000070401903400358103500d8010f05500001d224002d000782801000600c0c003c0c0100c4d0840d2010321400c41001941c20b048440c00d02c1c0401c04003c0c00110796510440925450050980d82502d0403039a200c3d200940710360340c141d00341d4065040703c42d44445c60303600740c84040391503602ea07915120200c3d11248001042e0b4540040204210113008040343d250349051000c00203503034007040707007810b54034107035407108407803401d01030840b038510455006003619460100045080c40e8448001c1c01010440080165002c2600b40c0031400c07030341c0c103403520307030344040f0400c0000403035401040d044c07c1115080c1804100d264003500c614219511601800000895200c1d00380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 320484991 1250 320483741 320483767
    0x4060c0e03010b010203040b0903121204030207170606010e1c030e28140a0306151410090e090106080708060a1d0307170918090f160504020f04120305 66
    0x18180803400c6009108000b0540b0010b5180d2140b4058803c25030800903040000f030310100603036044440c400c503c281d51115414030046000d001910f00310014000c052002480c0f4001692000e110340c4840302030566070311014019104007561420280c0c100c01d03d0020b0303200c01e000301d02903010305c0b60003502c074a800507807044200b003414001106561001001d03031522a500e038008040d05420750b01200310074625110120001030310f103011b070742c00103210a0a000c0e15104e0700c00c440c094402106c0c805c10042d60b45004ca8010007490081090707418002422442c0d00b0850381409983e426005441721000140840e19100c6031806d11805801c40a02a40482c040c04158100c61203a4012010300001040f001e45080c0320250301c070302c0781100242c000044c00d648c06020341c603840c04030703040040f00030110b6450411442c1c42122460048030842c1c0e503401040c0d0f540282d240c0100f00703024a0320215421380440c2e418141000025002003d07052000d15092002051040c1096040350415000f43c403990f4680302802880c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 320486241 1250 320484991 320485007
    0xe19020304031d01020d08040b090f0304080c100e130c0e10030518070e16031508010f060503120f0d020d0c120f020a0915030b030607090e0f060303070201110a0b04060c 74
    0x20f181107511074843d0740e0710b080d40b02e40c089812940c8081c2e254100c0c2c40ba9603015140c50307901d600090943c000014000b40141c80040c821a0421094400585c0158008404e0303801d2a0f080a00503000703900c0009040f0344880d0795100d5451420507007040c01c86001c6200c00f05164140000e802804039680f081401003c40404942c4010011440010901c50b410000c080790754510180041200102c288514030009010350003401c0c921420042e81c144e060f564000c824041d0178840d058030041440c0040100d00c9003000300d1030148048546141525040d201207091059900001c00c01c1c02c0c4c141c0c28481023000700700701e01440c0c10030b0302c141d52050b0b4020030012250701191020506080e084e4030400c1201d6403190030031803040032194000210040110f59000030b4014110300130800340e16009403400c0120003900410031300300f980c40080369401c684e80e5085001401030301c2669560781c1980248519401988901a40c0086c1c074003080954081110035070390900d0125050310101d91081c0c480350340c0b600c40b6a200b441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 320487491 1250 320486241 320486297
    0x207050601080f2d0102030703290a060c020d06052809030c02010806030115170d091415041706041a060a030204150e09010e0609030a090e1902030403 66
    0x41c2034083d03803004070a84e0742d000b01c0d203100410006003071120302c8000480b41801a55409000295030b02d10300010020010303c950321001140c80d80f150003401511500da2450144000098101e145070360131314909996102e0b5003030040360702c0803c0407491030004060b802554014004040c1d0180d00c0d05138800d0075010780c14001d41602e007051a00a400d80840d034005c005045040d020308002c0040e80701c010100c2d025000041241d4051503c0540014001d174640d802d000c40a5a80410759103040d04480040380c505d030152083d469031810502213040b49141c42e40b103408421840b801003e207041d40d01c6102001d00410b4000c0d20016400038420030051100050301d801045a8040c0000210300d031130720001e801005c4500029003c0c40e510000703045021902d602e840c1c05401103040c44052854040d04541c0a46064030041c6607502441e400718401c1100001602d002c00c4190300d07400b5801e4200010b4480045004004083c900000200d20a85c00070030304c02540941e004c1e40d15140c40800003025070300040c010002d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 320488741 1250 320487491 320487493
    0x70906030e06100e0c090a1e1a030402010c0f020402071209051503060f0a0510261303030c05040801141006030e060a0b01020c060a051207021f0510030b1003030306060507020a0605030721020705060108 88
    0x1b440c107048510f4127045941c4550709090200c850f002904141c5064640328000a401ca4130004514040c489c1d40d011030801641190360f2841a15100da05028685a20310716010031514140f000c68101d1030000c0050340080c80191801c81d0050382c0c0d6001900744105e5405c0c00003c210702400021003418034103101c5041b00c1c448c80c000f0b040c0d03081820510403003085420020382010390381c4415003042c5110724101d6006100d40c000901550b50214107124412206841040c0c02030108100024924040c1c0181495140400301516456580c44401406010400107450460180e2001c00202e0f0f504c64001d41420034030703596419100e9a0007482481d0301e4402074213035411340d81700316080010700e8003460003061083c60304000815103890300c0c0c248002c90640d6403c01410350a8803820446048a00c41c00c1204880c000d035420302c0303090b03990041620140704204019420210303001080c80340502500046400c00c0c4203107072048144e200d0aa840001948901001d82c0c4d03d41c0000b02103060000c20011240500502d80c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 320489991 1250 320488741 320488769
    0xf090506040b0409050a091709010206091c051b030a030603110409082b0f0209010206100b0426250602010501050607021504090203070906030e06100e0c090a1e 70
    0x1600c0b050079010350701c01c45200c5901c610010740c11401540054101c3e56114201e0708602d0440c40f1200354580001441c640148580c00024541c0324002460b00c1e24a218074030712400c01c1c1e0388000103c0309640400600304e030f800f00094285003030b481c04000900907100d8507540010b0701811840c2a90301150b501041c07a100741d042403000000b1981c0d80c003c650002c80e80703841d5910f907100807a21004121620080d1601c40c40d282c21011a07214103560000d2203140300903800e88040356101134a0205d8141d282c0126103a4002c1031000780002180b010b01182c810704880c9144400340c080c41045071410110224042c4042420b40304000c404500c5104100501041d0009025544c107000200c1d186010f01000a0312400540306900314044000f030498000e0000c000c0150b5991604000103840c81d100b43c802d00d80000d15040380500744440102d00c040c016040d10001c80705542c503000030401001005806454a500704010150b0541c1c1d610300c0d108002d00d0141c0c0841c0018420fa12511880161039010303550120500d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 320491241 1250 320489991 320489999
    0x150201091709040e070e0a1b02031e0c0109120216080c0f0409050601090e0606040908030403031a131409060709030308090c0a0305030c010b100c0b0408070209070f09050604 76
    0x60380840500340000750162100580310000f0090b01c0d40b070490200304d005007480421031683c1c484035a48508803540d41031240904403040c5410301e002e21030401d401600144030b240307000b00703540c01c500d0400f01d03d26021500b4881061512030031140e03038403401c440408a800301d060886805011001005000c44031411400c0c0c40e02e1442c1e40c6490220341143e1048191090604456440ea800703103103076540007404c4804035038440c0055001044180c8102c00385104100004d0f0f03803481c1600031340c039034250302941da0340c11074460f60340c242c0c060035442c01d450005c3c6000303008a44554882107900751048401c005e01055603000030404000301d40000d006516190410401c0200c0b00340c0128031002182e5145c501450f072540c88021540c204112041d5650b444100121b0000a21400001909429102000070002c80c03101c202080f0540050030311140104000b450f0341400310308170009240d8454014100107141c41d4850340000c0520004481420101d0a01b0304a80e40d4103510001000c00340c0300c117450852401d420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 320492491 1250 320491241 320491253
    0x40f0b0304061d0705130608030307050d0609020403030c02060306031509240121030203040f09060806070914130f0926040806280f1a19092a0201050115020109 70
    0xb540141401740f52031401da58402c001b160300c17030340c014040682500e40f00e08104000a14541c801c10b010803050382800408035403002184211812654591560170410882c3c2c0d0900400f904010f2415515004a82c02094005c602c94440380c4219000d401428220180301c1c052060004035000c662a1030080b003006000d40d00b4000f0303031032204002d0a41d03110054440d80c03034100e1840c8120340010000e152501c0300020400171507040081038681c1300040c2e56141d55900340884074418203203d6196680c0c44400507002e14108140c000b10f60040c0c0c0c100200f00095200101030540703444103821580510500103000c4510500d003482c1007c0d40c2075000742032409140075101607544c0307809004915550307064424804200b0403606085d190018440041c8025891503046400038010101003040c080c40c080707030f10f040710328141c95000220828111244881c0b800c0011081c020030003400b0005a0410500c95541d811800240c0d4602c1c1804650010034650304082140b40d00b0b140e43d2a5550a5a041c81641400645 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 320493741 1250 320492491 320492503
    0x8031c0506090402010305101a09090a0c0f0e0307030c030b010f0f06020a081b160f05010302070213050604110408010c0320070b06030c1305100803070f080f040f0b0304061d 76
    0x4d02442c01003003a072110a440c80c4001c6159020080802c60035070342d15042e0010001510792007404a13403505140c0d640002501c00d50303411a4500c000100c402c000800b03c07500413209140f022101900311040a42c076559500c0d1b109001d130704144e07010b040041c010032940043d100d842c0085c0c1040c14603200100e00e0882c0282d580c00300c0e0180100710190104501030791070020000c07180300d030040500302c440c03804110000b84c441010354058060a918600d01c08103242d4001c1c022940d101d580540b00d40030900044034410002c0c0000303004998030944441844070041c01d0b01001c0c01c054080100000340c440c80300c010140c11a00c0c000c3d0901c90f50314074000316282d00b01c044011740380f819810401021035540c90740c0000341000c0c0300c0800030360300080c007503400c030403071141c5038407441c49a01800c0703181950300d403150398283e07903405122030091516400070038860008085034003501c001804030040605060b01c41c5c00303541d40d038003180d0000c0d01c1100c004010402400f00502031442c00644c04607102140c034000320841c41c1c84070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 320494991 1250 320493741 320493743
    0x9031b0105040e1f03060506040e010b03032703060c0d0507021b090a0f050702030c0f1915020d060603020c1501030c14030c060a20010c05090103091b08031c05060904 73
    0x10f040000042d50302d11003124204025413400380740d01c2c01e2546a1500900600c020b03178407180680d00c1e001c1c0100100805104990210500a00660400d001c482c00c131040d24280740e100300840c01c50040c1900858030200301c030500400e1401c0703a49441c2d07043c29002c6011a1001094081190f00c22620140c02c948081c0404550b070005a1710460b10b0f560b500c0035a809080704480c034203100f51801e020004155408005022950301c01c80c141c5030965180b0410300c1c2c0c1c40041020304207071211004005400969200d02c44a8160020350025042517102d81c0349000f102d000f40d00c03d40c042600025841440390713040c0000488a0301288010380e0550458490307004400c0640240f50101d200301c8c044c0b04207542c04115202900308014166541c856041d403000302180d8008092044600c1e8080250407034440600440720fa44015554013401c0224040046014001d40501643c003000109100c515840c800081036002d4841403000303568030303114000d075000f4071034400100c402c2c011320f0141072105aa4500100a41207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 320496241 1250 320494991 320495009
    0x610080601120c0c0b010e10060305011410110d050301090621080d020706050c07020a05010228030509120f07140d150b030a0507180504020d12200309031b010504 71
    0x3c200f8642d800c0d114036618040c0a45074900c841d0000545140301680d56121b090f40c40c83c800030300d6079610400e0302aa0401e020740070f40b50314070041e0f030140d80c181709034107110401d450300e40002c907182d41c1241d560a00c2c401d10100d13000a0000401885240c0c010300405008114102100c80c3c1300b0010007182c003580350311040007401080b00082c1942d0108554050b55500d5800070302c100050f00700114204c4081c2c1c0000c80480c008d03118000005001e40c00412043d6107449840180e070345800300c0c07200b880e1440010000817410b1000071f00c6060007981340c00c3e001a900400c00001032601043c0c0c8040c8500d007821507031207420f0310940c00c0001480c0380c035214880c0c3c0c908c03503100e11062403007220750035807101074000c0d01c1a040d01032080000c1c042c18054005405811203070010400713840110348100b0320094580c04c075000380d0021100d4690380d0000307038400001407039081e1618103d100000b52034004035000d00e80b48807c682990010a401031189811302541d40d150b407140c00c82c0e000c4024101d0001e400d60040e0700c034400d04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 320497491 1250 320496241 320496251
    0x7060b010c2118080a021206100b030a060308030a0911030c10120f140f060a0521010e0601080f070b0a02060105010c05031c0c11010501060206180f060c03061008060112 74
    0x2d405010740301042000683d0350419903803a4100103903100e50089050381309004590740455440804108a80200d00c6120540903940c00d0042c0782020b948040d100210702c3d66180400800725420300051801000383c0d1801103409403003070511208086000300d8182c440c0d000400c2d0000d95690300b0104900307070002e6040c07030400c1c0b03004030344140300030162081d003a501300d404c004c00882c02d8000c105980703100e04904003e0b00025181c1e041405040305280c0941c94000078950f001c207112180d003180024881e0000000801c1c151031784800541800020f0380a08520340c40f44415060300d000c14000200501546020b4038107000074000002e40d9000d0604c2500d0600501d4403480c2c040c03201c00d20443d03000c00c4150482c0104030024160341070050442c400d44400042c001c0302d144c500b014040c01514101c412542c014041910703039414201081d00e105540303507141e20440300070b41003da4050000500c0f540150020540f00e260240500408010204159007040300d0f0030b082000340e17a00000302c01381c618451180090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 320498741 1250 320497491 320497553
    0x130c02010e190302060109022a0a020a0e15010e03070e1902072d03020706081801050124050301030b0c0703111618060f050906060405130207060b010c 66
    0x200619400d0040c128034002d103014510b0902100284102a520907822501d9580e62031038484100d0140421425241c1d0440b1000c9506000b100348180c0340391051020fa9280081d00d41c0050000c6042d9800741d001203c5203420008000314284020581031401c2c203110200750f217200b000035103c408038003d1f02c0b03440d4084008a061580300810002c103031900c501d0119500c600b241080c0098001c211032040d03914551648200900d080f213841560742d107616400500045051401c29602c3c2c0034014214000c0741c3d04091542441007003405540c1c001c4c0040c08542000b00c13075400d0942d41c0400011808010302c41c04000400c00100041d000395480352201c84996114500da1900304e0b082c01c0781040300086e070320880c4840903145101641e450212030341d009041d03601c000c0c10104001600c03e68480d038060408000000c00660070100c0030170398001c0d80202820b00d801c0d140c0001403034400000340d414040c96808a80b40041181600c1480c00b0040300b42090155602c1a40d1420303007154290001c1080343c00761141d03680c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 320499991 1250 320498741 320498743
    0x5090f04030c17130f120b0a110403080702030709090c060c080f04140307091a040905030d0504050703110d0b0106032316020105010b030105010503011703071502190e130c02 76
    0x11030100e0f4412800d407540110b000c02909a6041150500c0e0f24140758103001640c1c50240c013203503003180c034029010401e8444640380e21504810080c0b088480350f85030221304a4001700707040240301031031040303900c15203440690042c117113409184d421032399807685418401008203507286000e40c11240c05140080302001d1924001d0b000340240d0550446038900403c000c2005901c803240041a5413060b000c0f100985c1e40c940c5001c068601001110030800c0c603021100c1610b0038103030800075085020304105c901d031800e0a9100c1080b510100c509a4080c1c014010500402800c1020050081802c5509480d007110a40751303440360b01010302c15a030505607125105003c1d015813151115083c901001c802e0325030724028070440d00400c0070080725401940303010300110f0000f1520060301c4c1a94410303510700d401d581c00c020849001140d8036411002920041c001c020005c1d406003024400740e00321450240c2ca402c5603c10918201d54000e000c02c090124003003e00100c0e0b2038800c244843c0a05102c404a1010220102a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 320501241 1250 320499991 320500007
    0x3090513020405060d060e091c03111c050105011103070302060a0f09020d0303021e12070f020312070c2906060d0609020c0109230607081909240605090f0403 69
    0x3d84d800010101d0303a55080f526541c882d03c120340c00740031a1551607032408503141e258210394500046080c00309402c044220702c6548401503408024850303030b191408142011882c2c0c041c0012200c0240d803220010b00c103550303011804e41480307180c4100039814071a8a03500a034a9240003030089582c80d688007008905a0483c2c0c20100580d41c0181111092502e0340c02c004001e0760044c0060509501c0c0031501d000c0241074202280c000e15001e085c54480c64031002c00480b141c482c40301c2c041c0110300c001d1118501142c40741c0551406000951030f4000c400509103810141182420341007401c951062104140c80c0c0004201d803588818112081031b034903c1d0700008800200b80d6900540c41c098404103600501240541c002003455004082d080f910022904100c07080c0011000c4010454112a011601060199a0140d08035101d80d4801c058134805c14034003401c0301c222540a4500c02071a0103120301c0c460701c0409010700c108039400240300c02c2d400d01000c01c405030300240002100340d080c0c400040038035103c3c0c00d40c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 320502491 1250 320501241 320501249
    0x1501091104240207050d02090f0405120301060c030905010302043507030b150f1309030512040b0406050a02090303090f031014040b0601021b040b010201140a0e1603030905130204 78
    0x11240c1d4020a0340042c141880030200c405071060300700c04140c620b462081e03812143d034002e080d40c10036610702c5244003090b4406803007204c00b84540c132a00394100d520403002e1030113000030307030344002140042d13003001001840c0540c4041d0500d88100b106004400340360042d400d40605105100b2049000654681e120074542660b800c5580120310b808801c00150102841c0521003450903014201494030800c012f41e6000b4105030b602c900342801010300c1110301e42015100c2c034024100a42030410082d1001002d80301110105c0d02091100d08010030029280315441d00030b405c01c01c0450405402c500403954038854106024406c405482941e440f03940d0800c079004003582c080d0014001200501d503680320118040d642280d4030410040000e080b5440000d070b08407401c0040c800100320030215420b0000628030014418115522041c0c85000e90032500c0c0040c0c05801802000075080b01c840706640e003440b148030f00c423456880ca4003c0800104e940400801c1c241d480440303410510b07036a00946503000b0700c620741c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 320503597 1106 320502491 320502509
    0x3010b0c16082d03031302090f101a1e070210030b0108070302030c090405090d3005070207080f0d0e04090201120b060d110d06081501091104 62
    0x805a4820140600c109641051210f0500b140c0c41101c0b8000032403800300c0c0e90411800c2180000c0e0f80f00e013140d103c16210b800c00321241400b6010034403a031152036460280894070941c00c0c40032a0300c4424005510403011315032682c01c1c001508403880c140e1080c0485440c0f405044e000b8041e480b00c81c2c170142c0d15a0a03c0d990403000358003d410142a442e0116414065846240c07201d110b964080c000440050901c2c0e015448002d1900f041101c030719020508030009000051031104504001071a07001010549643d03009040b460b116081d800000e00e84211000d0307068030400440c4407009080719654440d4143c1644080c0070642d49000b00090000d80240028a01c440e81d40d4040c07004480300408107882c14042045007015107240d2030400c4051840000c1e0041003503000d120304c0c0000c04000001e00204030b00132504100d00036051040076100c070348811030b4182034016541260b0250003591 = true := by decide +kernel

theorem cover : BRFrame.Cov 320323741 320503597 := by
  have h0 := BRFrame.cov_init 320323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 320323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 320323741 ≤ n) (h2 : n < 320503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
