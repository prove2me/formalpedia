-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:31:57.592364+00:00
-- url     : https://prove2.me/submissions/ec7726b8-cdaa-45c5-a0b1-ce1b337cb867

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 7733820 ≤ n < 7913676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 7735070 1250 7733820 7733837
    0x5040201081311060c010e010e01090c031101020102070204020d0f0501060203040b040b0f09041d0d1403070e0301090c06030c08160503010501050304050c040c05040e1f12051005010f030b01060f 85
    0x10120b01c81e02c0c41d0b03440c21181d540c4040c080b140036413a49009842224905000031401039080100030703003524a08440f4150582c503007000712000c100000042001caa4100e6443c6003000f80890041740a485006e10181d042400017622220b10507066000000c04c4540c40010006030744c0750902261603125900c03a240e82c45505210074411800100020640500304050740d6190440c0030010806a4240190a24180315010000c00d080caca010720031008034103d146040d0107440c03015070304045e1038000600340b8000c04c61241c51800e10341d00e09600c0680030740d41240425613a2965510014040d00d000c40b0070100190320240403030300401c000c0d41c019200103100d45030182142e08180044846030002070040c0c51511400504044917240d0307208241c115201d950b22036680700c2c20008000e032170141c06070001d8080030309940000447c1011091040943d50304d141e0000329600e03e414050702e021806d400d100f8415103440000200012240c00c0401100e210303d03400384190380c1c3c071041030f1a4070004024080c042030112 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 7736320 1250 7735070 7735081
    0x24030106151b0203190c0e01050d06050903070f050705100e06040302090601120905010209010311070b04020609040f110703020f03030907060c0309090e060603010e0304080a020402070203010b0d06050411040504020108 95
    0xc50345245100c11991142c1905520350300042d103080e41042600d8030101020746205c0c24408a070714242c0103031080d65080346480d4548070101c1c00d20852880040c18440c0d407070000c105649804d20807a154160020040082c2d5401070405949030329803880f41e540700d864142c040a1020b40102100041e0040c01400c45083c6403554080c0415900014009410041804041905101c1512620340a00e0080f800140c403a00040005000c47d1800102035050792030a11440300000c0d80d401d02681d2095064601c29190031048001c1005003504460f40c1a0b06c41c10312208441792042c0b10054007519000e0760881c0d94070094000d200d501d03440103403034402c081e0b003007558240701e41d5006084400205101c1d2800345c000300c0d80c60a460044520039404d510300354014800348000b030301e424011801d40c101450003131494180380030311080c0d0710700d0b1f0700d44001e004540104001056540070741c0032104101e03000c2c06c10161a800b510b0032500408003202c0840b00244e0725006480c050410740304003807285a06841c1c0a06d0f07900c50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 7737570 1250 7736320 7736327
    0x60306060e06190504051512100302220213030f0b010b0301030f030c03120f0b0306010605030c0d1d0109030c0618030804020d23030703030e030a0804030f030e062403010615 76
    0x1000c0d8035820304c034040000140c139468561022001040e110007060301c07228000860364082401900414010600308824000740c3ea0f25540180340c410b4256450f40f1000d0f1003030700b02010303000e94030a83c10800e00811000042c8001c10b00203610030f500c92003103001284e88030440c1914a0000f0702018080b0040c98a1240c002405803c1842905000f400c110b483c9101d030a001d42c040c2c0390f03114003c0811684408204541c1e0034100941809041203040013030941c5884a400031060250f016916541510b441d04040c2070300c01d800540203580c0c0e000c002401400b10908025000340308454040337600d40c0c504011840d5020202e11844031071a40341e43d0354402c5442d280c08200384036020a00c2075412420303981ca1942409030301074517194036032407aa000d95200c4000b404c1c080e0854048010704d9010b42c208100f086015030703000101a5000343e250038051002c1c50222403c4000f4110341da0110707080d01c560400c2c8580d40b00107a4200240406444090045441002c249420380701244580c0910a4075603022a010703600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 7738820 1250 7737570 7737607
    0x605090d050705040203100302010807020f1c090f08031207020d08060108070314040308010503100203010806010308030408040806090106090c02010c120e0313230d03080412030b031006060306060e06 87
    0x141e030072241c82e01e0f240c80c009802c0f640240c6890600d5200803104200719604a100d9a501c0343c03241c0080c00f4040c85d406001500c4000840200c0800600707012010304044c050700304e860207010180d21a01c0c01c00e8440e00110f54a621081d000b41d114001c240001b83c5840c400a0880c41e18403603a0380e05031103a110b840c0159213405021b8101d0302859140d5030700c82509141c145000388154040d40d88c12856503d01001d042c00c00000e92080c241c81401080140b00100000440718110781e40003281a6807681d40d410114803a002d0350b00541a40d014a00c10311642400c15048042603e090741020419a40c0e030001c103030b080364400c02e00030002c61841125400c01c2142d5a01444105081c0d0050340d2070500340f18100c0c03005034029000001400d019031808014401c0d81c220404200b00e0946910500d082d15450240c40c24100030802042c059045145070170480c402e4009007084a8007804680641111000e6040608010300a01000a20b000d02c002007640c450116042140787c0a860b01d80303811600b00e800e010404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 7740070 1250 7738820 7738823
    0x3040b030714070b1005040b06030408161407050a0b0c0c01080a020d0603030503190501051804020f040e0a0203060901051003060f020f0301060519081902071703070c03180605090d 79
    0x40078035140a4840d03100010101c1c180301350360010003454900600d04105900e03403c914019854100c1030b405a0301d888040741d82290708940510f80316140f2019071900d004030110010481400c001c480c030003543c0002080f02c1a07800840c0d410f04050307111000c80c0c459014050010449a001824194503940111080d581004101102610b442500c010712800d81d6465481200020350000800201c80e140241000407005802002e1000394500030000392658005030080c40791080480c041b608540d03c0036010321121801030406d111016944100070f4440f800690103901a000300c1c00059008038040c0700c3c05100d85d0b194854924003030b0940e01c803e4003d2001024103c860342d0300304615002c40300b01c1c02c080c5009011964840c0c3d46c881410b0741c0301500c0200d8041e40300500070410300744036a81e0704008113421200480310b1300503251000e038240304210020480b01001c103084008284200c183c3e02c25091800d8500a40b030301074404036032a40704080004540f04100c0014414400004039250040c04107509a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 7741320 1250 7740070 7740077
    0x5090121020a050405030111070f020105030a0b0306010303030504110108042303120a09150501030803010302061c090302010f0606090308030406021b0105090a030e01031802060d0f09060207060605060403030203040b0307 96
    0xc0300040080c0301203070b000010502c08502d010404201c9860240200342c0e801d0700c000d034210700340019550360404440403618000d05000c2e01000040444c40c064ac070031090710000504071003c650352814041c000300821f640c00e603160313524401d000c811540903040390f07809980d0105a107009110b28076184a414004900c071131005010401000804080040341c1600450840c10005529251468080000303c0d5410740f007203882c0c0c2007000400110b101039003501c1c1100e405541d11030380c60044200b2682d8100ba003069020003d0702d810b000c4421b043e41540035101c5807203a1482002400d0700e690068540400d9480010000c0408200190005070550040c00c050400c2c0b030740102491008440f407600b91081114241480c0e40b010f0040400d040d1700c242049802102820704003c0288852109110060711800103070103603000048030000e50f103855004056114015100300140700d81c40c54a0b20182d800000c096488900700f1001050b00e1826030700b01c80c200c80c0d15030000c40c0380614117440c0b0040341d00003c0008090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 7742570 1250 7741320 7741367
    0xb070c05010512180a02040608061608010605090103050711060a06051e0906060702040b030601080a03090e060102030702010f020f1b0406090b060d0c0e06030103140f0f1509011d070905070c03050901 87
    0x42c1c0347c60040101400542002c1d14040c60038041b40c40d200208190044d0800c03500d0b500420070141c001e002c84805000c00e10300450b140e40d5103882645c413030512600fa0f00d120301c5600300b003042c0c440550380142c1c00d540301212035080b1031411811500d83c2e10015040903900c225520702281c803d24004000300030b11803010b4804a21030500d00300190800c1402d0380038002a030020300e004d000301039000801c070000d0300300e240e00b600c0d6900b00000000c1d9280600d50000b4144040c1c00107041041d402081034251000303207041240e0303000c2000c040d1607070f4031907620031074034001d070709148011840314180d0045801a000103070010741401c0042c0100c20280441c03482c02e03414800d21130220300298603000700440c003940c01a40c1d41092000c090a64518010190740d210059030080c00c0050442003000c54840c05102e0041c2d0a0800c40c0c49101c00e00307004114603400f90441007c803c0f03104040310310201e4a07000300c4880304420009551071500c290383c0d041c0c1d1114010001501040350441310341c068070031802c80d400c00d824000c62 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 7743820 1250 7742570 7742573
    0x504020409060c0801150302160b071101060603020702010e090403050307050708040503070945050102040503010501061106010b09010e09131205030912161212060b070c05010512180a 80
    0x1c0703031020402d1000054413480103029005184044140100492404610b055016112045400b003c034000070010350000b004a20840e105a030b400416045a070001c0000342c0d580c0e200030340250f0014008138041a03103030004d445240fa0a0807114425909511001d1566481800440303183e80141c00403240803105010110b816141009010b02030080b94400280341080300c0c2c081007080700c0c80062001741d0040310441004041c0122498144e0f00000500c00000c80d089180c07090281c0901e41110390150703c1c00c1c00015009520001c5c02c12015074420545400e039803180100750f5648240d42c3c106010032620100034030203003050002164001c200d590b07030b505007104580c5d842c0c40c1100340300380900020f42c000c818842c0b1b50707070705101001700e840c1040f440520f054200c4070b00380f121700403a000181c9220041c011000c520340c0142c42101090711060400c00c503c6444001c0181c0c15040f882c801d5070414604500420203500503000c50300b401c0b8000140c035442d07a80300910b04580d4812201041800d0003103104210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 7745070 1250 7743820 7743833
    0xe07080402150d050103020909010e0705040203090106031a0106110d0903081806030a0e1b010c0b06010e03060106020703050106050616060c020106050d05030711040c12050c070b01060815040209060d0504020409 92
    0x152115a00f408103481d45503004001c2003030409007403103138241d00d040d0b040c01d10507a000aa020803a40d040d1000b68070f0382c1d01c404130a030040159900c00382010300c04030405140b204810f410141690895111280107040c2d0305034044d503400a500825012810000e02400030a40b8600944104120030440c5400000168089011a00305480100c052600e45a00205540701401854a0b1040d2100c0340c100665884000030041e41d00420042d04c40b640d040003044299208a8804034400b401608031105965140790003907554120384400c1d0384552802101040515000f81110f00038183c1600004043c0d107031b80c551900401c003003801c4005640d61b5000000e0307283c8941c21461403ca0094000e1600e4a101d824040c1c40240b4110f031203803049142026204005801082c10301440c007a00c1c10000b500d13a9014522a4180700303601380a031180d984074000040d42070344181c90724401d4007120250003090052005000c1a80a5024882d5002d0300034402e034074103814035600560b0f00500061000c41c0c00c940684451 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 7746320 1250 7745070 7745077
    0x4050a0317070602121b0307050a030504050f01020403030507050705010806010e09090114090a02090108030406090b0a02150f040302011d030d0b012d0906090b070b090c121c090e0708040215 83
    0x101798131120802040705c500800c040071054420300010341891071510fa04000c10701c0c8503e16184d003d01d136984001c102441000c021a09038281d0000086648dd42c480c00c000d03069030000f040480d0107100d800000300d01544540c5034a8000c4406841d010b0308070550000b00031200600900c8000c607503503901101440f01020203084c50041c500c100141c40c81c1030b49401400003144058100c0c0c10150310806c802c001295104c540e000031a440c2704e5100751284041074040b405c0c1000d50000c2c1c3c11070031080c2c081c4150344507654460f40c0560301c290001c01642526511041c00345a5003184852150024084908003020a40243d00c00480500d40314041242107001910b840c440500b8941108804003c181c5417a40c2002c1000094450307070a141280910b0140168598802e901006000c502144e0126201620401490820714002880c49130542000d00030665948242d400b21180c0340f4036002191055402072201005030f03481440c0c410071a56441505845803480500200d0708030000400140784a800e04014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 7747570 1250 7746320 7746337
    0xf01060b03090d0201060b07110319031d040b030c010e01031d0f07080615010507060204030807050f190503040e090703051501090501240c0c08150a0f0204050a0317070602 75
    0x1640701d050914038545080c0c500c0818100f9a854901c05002ca03081c044180c40d5086c1d0f0003074100e006803c50744042030401c0418003002c000f00039131241e1801019004420703055060341109500d000c2898000030413054550404029805030004056400c5d81e503c14800e14000350010705001c54a080054903d154030b150f01040001035400c0307240703d200d001000344004801000600b0080240d42000c1010719085003800c4a903506001002515400b0040a501910003c607000120580c65040908203035031940d034500320030489400744c251304000082010013100c25094004009604190400c039441c1107210014103180d41922400c400000003800c02c10003045020350304044480154581201c0e041950360603040103001105041034948169140201080844954a0206103055860400d0206a4020b030840d002c1c50140c07102c003c03e407003221003002d03005505640041205403034a01c02141240508e01600b580400c40d0602003000c5141c1501d2403110035010110549486469600e8504a030b02c503075103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 7748820 1250 7747570 7747589
    0x5060307080d03090203010b03060c0a03020a0201060510020a05010608060705090f0a0302150a0e0603010b0d020901030b060c01020406180807030807060f0501030b01080f01060303080a0207060b060a0810080f0a0f050f0106 97
    0xb130003021401c0038010714000c00015001072034035040c010250030690080100c81410151702049940c4424801d4112100500c070203821301043d800d2640c0300940310345044006441942c24180e001030200c070001801445503c15607030b0103041c4089101007200490800218583c003032001240800036944014101500c0884c9035810b50b510008a800540b240d40c00e800168402c01c01840100b000c030008608840f030b402070302d003801aa0f403240d100c010b074001d048055400e0f4000c9000301e000102d01d5815801001552915240d010300c400340420a00210b1029001d20005da80201d4810000220300360068050f0706e10890010501d0080c90b94800c04481c0260720039a60f0110210040003000d42c14040c007400302503420003d120325402d545020b05480006054a860707982d00103041c0c010b10100c0c4d03000b03003100407000740a26520f0211980003070502c80261070084545680703138000181d80d000058041140748466002d04005512506c0344549102015810b80d528080c808105d01401e00038810300004c0e208022 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 7750070 1250 7748820 7748831
    0x6060509090f0903120601030e0d090f12020f0108070512090619090b061005090301020408030405120a030804080f04090203090105070e01020a0c0e0402150f04180614010305060307080d03 82
    0xc00080e0000503110014550a54041c02150b43e008012a0a202074902d401d00b0b80e42c49840040303008080c4c0b10001c00301c9004003103c141c4180d030702205900440741025008501c098480000704071030424004001d40c0324015100b441001e50040361070303e501c01641e0525500700754980301480004c0c18112070b081b00c282c01c0401049000707604c0e19860080d040c00500c04100415082d51101d51005024001c46e00c00d034410584500c0c010312500803246d90b118050000d41d02d032075a4040c9182d41c1d070024000d00d40301c5d07000d06040282a80001401c1100c2c01d03090b40c2d4801058459494145080c1d20140500700d0800c0c003008040781031242400154060907a13040001038074582050020250f00ca40801c490440d04215000c00c045100710f01700105640142e44900e0240c0c844d440002e0391070403000e0f8000062000401c0c90800d14013180702030002c40d600180b002e405250180207500c212100342c01488408010582c2e4041654425800307aa4049409001c030b4001c84d0f2103100350343c542101003035410002134403034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 7751320 1250 7750070 7750087
    0x50d270303020a031401030308061207050d050a02030105060607080409050a02090a030f06050c1e1b0601030b01080c042007020109050a08030d0b0a030c0509040609020d140d08010806071809060605 86
    0x14407070402d0000514130302c80006d5040da5001448020003a00407403240c590040b89501d43e800501450004000090100744111481e01d00107032a90071079802070b4841d510340800600d2038101041100e910300c0d48a44645e1500d414554540020070014101902140e82480b85124a89810140c034000d14002c0713601d611901d9a03480c201c02030f544018004070000200b40104000d05040c460503804134002c803980c00c2c3d02c4901c840107880c040c1c0c26408007a40d5502c150341c0004184100644841d058030810429102814a25010300040d48c0540201118625450701014901881007002d000b83c5881490310360750346030360307400098000b241c540c114100075000052110000d81084c4140d042800081c2c8d8039614a528548918410008034400c103801400c041c40054104480c0d40e11524031070398014030700802000c2c0342c20b0008007801c203007254092501c50703c03120300e04450042e40401c0c12645449e0041400d0381c2c0d0b080048850101318500d590044021100c08600c03103100f4042d14000d842c41d0344e50300780c440350103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 7752570 1250 7751320 7751327
    0xa08030901050709050616051005040606030201020f060601020a060506030c030607080108010c030902030c060307050408030a050403120201290402130905060414040507140609030102070b04060e0706050d270303020a 94
    0x1a09000070711013283e02c02c0041745c49107400c1d01c17604d1040c0ca0103101c0030039040c20310780c0c1003c010500c3c007002c5e640345c05c003040708000560b0f0103007007030b24001e900302c1c1c605c01003c40710140e44440a50f00c0da40541d100e500ca141c0002c000760045c03580044090250703540c554000020038a0510b050b01ca810201d0052001800001030901c03410401c050710b0705e07007400311217020740109880320702402c10380c0e0081000000141800c3d005500300c6005100d180c085a40d03907441e80d40d0050203074100d8001200c0d80f100020040103a1881406460000c41c3e01d0b6000218445806800011104400304410f40054007444025914581d00d602c060042c40d1620000c100c6140c6082044111501c60b0550703400029068207200128a0019400e03080c3e52200417010450300c00c1c0b800148581c0200700d46030f0360540c000641d40041060f01540107000b94480c110511410020800d110b4480515009600020b0300a0164201d000603d0700506508800c40d031005c03205141c0c6030076462403100300440a03030101c3e40000b04075905562 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 7753820 1250 7752570 7752581
    0x20304050c19063603030215010f0302060313030e040e0106050a080f030a08090106151d0301020307020a03050906040f0815010905010b0403060c0e03010204060c14010501030f020904030c050a08030901 88
    0x111a0104001141040801307460a50003444440005a0010704001c11100c0b0030444c0002c00c0020100c61402503403490001d503900d055030f40c0e52111484001c00010070705600500e200507254020b25075415582c4811210f0b0941300d4428040d410001d4880c201042030f1958490151202c00c0a000071920074203000030301c071400850760b100781c0d20750f07015a002c0c40f42c021010040e60b40c0300768549003292803a200c0483e214098400ea410409191341400c0180000503080b4401e4620000701d80c80c810540d1120008050803400202e47c60300258111884034000203126100806422400400746c41c20284c9034108210851140c0d00312403103560001d104000c210604140a0f030042c0f1a03801c084c4007560600da80c01010740a0b0f840010030f500d444072003e090442c001d501323810043d40043d0003107480315510900104104003600c0c043c0c41e8035206403500c0c11804c1e0180101810f0742d40001900c010b0201e150709222606000030030540412000000c4000081c07400c0c09130000c0540240c210a8481c00d164030340f2400c40c0d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 7755070 1250 7753820 7753849
    0xc0806061201060f090306020a080601020118080306060a12060305010b030f01060f050904051c0e1002030921030c010e0109020901060e03070b0d0b0310021e0301030f11040b0301020304050c 83
    0x40248120030712000e8400409040d10914a800a640b203400072040d1050381050704000c0c1340314001300303924103c0b9a1000d0014401c5000341d0081c882c41116050280030f8002e5110050701d48001040051201c0c1045002003214000c580340680e17544036404506003c642107900111040d03512000d001005141c1004120f80f90102c00000300103503842c0000c01da05a01c090710900c3e0142038254000f50074401c09110070555001c1c1d440c400e840d141c44407607000700500d941c3c5545a03c140c01111542c01e03114400416070341c07803c50181030014045400700c42d00b103d900382030040b040a440300704440c114034002030140e2102c41342c42c8070001c40d940c181d601c100300f0030900580140c02000100107111010340d400150310000c8646c6042420790722185490250050000c1020084d0035119000c0841c03807031070303482e401410440400e1b2031070b200208610041040d140b0080c400901000044188100414601d92030500c0104c0010000500408513001013826600b00b11015503583d00200100c2007282010714a42c0500c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 7756320 1250 7755070 7755079
    0x40303060e13021003090f1101092306070507030c08071a09060d05040501020408070303170c03100306020901021005010306020d0c081b0304020f0901030807110303070f0f020112020408010c0806 85
    0x285400340d28a00c00c0c202d09580648a090b000324030b1400e181c001c2e030140c10a29044500d4440104540c1462036111400035012800581031100002c1c54802c0b50000c0d4440840d01d012031404004103e0801c0783c0380d048441e040c4c40d54000d401000000840b011240401024460007030a00b980c40d01d692119030300070f050504c0c017503a6010070024080d0350343d40b012240d844a040b04000780f29200d500b400c9009000d56003044820348601c680210500d60402c0c0444045c5e9007501d005400c0e90b03030328880075269002c1030364000091504241c0030b0002810680140c46155010301c11940d00702e010542030000d640313003039100b074440c2030340041d2210914005000b4180104000d0800715041d0420076200c12900800c0f40c100459194040b020a085549981082001034402004410b0650b1241404102c03075000240c126010246a0480000c909000c42503840303258010522240c4960309480e003007140280c00c10124100202031610701180c074102d1000c0d00244c40a00d0001480410600d80600300314406000e00b03104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 7757570 1250 7756320 7756349
    0x105010501090e040308040f05030a0201020904051305060f09120307030507121103060d0606030602030903030610030507020705060d0b041b02010c020a0f08091201020f0310140901230a0b0304030306 87
    0x10850f01d40c40700303070700994540f0345040150380714101800008510311005002e80000100501c007a0b605402504020400b100c04000d551210380303035107207100710904009203d0b802506c000350000041507906039000140c103007500c20000004280b07882540c0101e894501103561360060041195000b840010001041c4c1d5081101c400c000394052030b035000003070443d403003140000d034071300704000b03581c0c0280004591040c0159220b00b04000c11645a4204680f0a0b00070003c092000d42010310038043d1900809054000c0c00d042414501400101d03401003400942003a1640c5006100c5d403528418007180042003c401d181e600440c85000342940c010b80c00503401c5600808401002c030f00d042819030045c0398002981e99407100624003040010f00000c8150200394408100240341c641058004c61140200a060780340141d1903544002d1100103030420541c007c0c42032001030200c94004050303505c1c0c001c0c0c0d400400b0a985900c60028500343e15035008001e240c200402030008041e054003c0e4400707803102000300c0300e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 7758820 1250 7757570 7757579
    0x403180603060e0106022103060d0501020d020702040e070b0f0d0e0a0f060606021f0e070819050d090b030a050603120403050109050c0406060525060207061a010206061003050405030408030c0f010501050109 90
    0x746506500b000c61400c403800030216227640c2e035500c90640c0381a840402552240ba1810883c0025040301000340c1c0940d0038502480018400840c0d07160a4807176445205040401d003864024040c0c000181128680f99212102c50b541c410801007107594a10a03054092030034006c0c035065044d615180d0000055501c010940c007a0010500458845607030030039000280c4d088540f840340d00d40461039001540724062590001c40500781c040e115504207000c0c0e07003100e45035107800d0310803031705494a441501c0c001e5209202080c843c1c0c000d500f006070400390050031501a81c1d4080d00c00103031680580c2c01111580e54441c054410400c05000901e20820b00311010040c42d032400340003500310300c20900f000c3d00c078510300002c0610f51109070b10203004094011003315142c0d1900d1500d900100a8810aa8903800c41d10028011030b42c070028841d4401da00140101540790300b0350105030050702c03012780200c1c0d40740024230000c900c461041010f48001d1010303500405013000c1007091142120700680000e410490190310900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 7760070 1250 7758820 7758853
    0xb1005090d02010c06020d02031317030402010801030b09010b061b010b040b0307051915110c030706091a040b03040f021e0603011401050d14060a0b0304020d020105030403180603060e010602 83
    0x2040381d50282091100100580b403c140280302d45d400e00034413148013009000304003000c05080c0c010382c2c1c410b10711071250b0b0110300081c4206002c2110000e0010380030900600004403075403034080d080380c0c4901c0081010320051000a4003500300071001000c14950220184d402c0800f4050100410070036030741008500b0544d000f00b911030320240250b07402110450300f40203451109080c800300070411070100c000c45841c0b0200007050b07040030b9900a50248200d032409a000c0c41c0100c0d001003103030919110b95404510f41814070b15403c6803a500c1000410b014000000c40403070f03400043d0301c11882901245002c0c0304510402c04044000b907100a03609008044040d066283ea0b0708503419905030081c2000709141c17400040b20384e40300302120451001c2c20403601c80c0340c0301c01c04041c00d8010641200d02c3c0c1e0300706484685260301c5020855000c0d60100303941007400d01650081c0300a41c0c20900a18120f000e80c51045400300c200440c17a84040c001954807481040b07096202950680903280500c041c0008021503565076 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 7761320 1250 7760070 7760089
    0x40b0403030203040203160308030f07080906070f03060f0308030105030613030f0518060703021507020d0c0b04080f03010f0602011b0509040e030c0703031e030c05030408070f0b0405010b100509 85
    0xd0038568000089400d40d68204021000300c0b6403601122286a160301d400c65458000381c9060b0a805035036004518041e02480550388502e800030001d10300c0d03903143c7c1011114100c0007128102419270311000031518580b043d501401460103124101e56a51415091600c0c00030000d11030712442c42400280000650300013402d09000100e80341c52510b80380c44054040c4280c0c2d0354025254010300c00200311080540104405100d4602c0000070a456501e05a05a0700d69094408000024007054692400151241040364005003c0c1a206080c00c80c024040c80260b4001e80150010341d444044c00c02203a942401126105160000c404410b040c0c203030005004d9000c0c0302081071041d82c0707034045503072488401c00a46810090120131a03800d00c0d45ca080180001c0c0c00000e5242004054882c00e00c03006019000303204400000b55103907490340d911501c0c0c045550700802c5c0112100e195100001e8080380500103da40200c0c00b032000014110028020003100d1003042946000b4801c2c28040303102503907101141c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 7762570 1250 7761320 7761323
    0x102030417030d0606020a06060501020d0c080309010f02030106090f080304061704020d05010f0f05100b07030f020309130204060e0d020f040e030909090d02070801021314030102120705030601090e040b04 89
    0x80c0c1011140e030007400e0031400358001c0320034914505540021069070005030195a24002c034020030525881c0c600482c0c84045130202c0c00003180c580507402e070008444800560f40050039900000b2207014407902242a03134420307402031000400d11441031082c8004400b03900c00a1080c10015072400b480e11001412113044524100c0030b2101c141d00003400d648031040c0242603158850004c001c481d2124849100030800840400012403a1070006a90303070b54048040000e0380c004090307442c1030050b070f50f03012143d09225804000c21404144200c100da5210110000904000034102685450415400034844101d144000d8460044c00c111000542c840c00d02e03200c40a441690302090501c045070080389540329000f401038002d9500803c02c40c444401040d000991101542074035002d9130394100607420303405842c3c11008441a07030441000002405540d85050000c00340001d4101140c9003941e1210040c00c482e407001199001041110307030b691050345100034041100b03040d905800c05455429030810300600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 7763820 1250 7762570 7762589
    0x20a02060903030c0109060501140102070e0610140301060903060f0203060a09050624030702010b181317070606080f031303060c0912050d022a0108040309080102040e0411060901020304 81
    0x501e02090380702401103d0900001100a01285105e072900c0402003000348070781644107000c03005641040d0f20116100d0112003261a400c0e00d070351102c01c1007111021324151040b09008041d40800444520320001c0c600902041d191504124a0750920b2802c0c1c503541d800888040380704004100c1d007a540d29800c0c0041e11040c0e440080e03140d89030703408150010f07402d401401e038424a4003210741d40080f1440007140314200c0c44c3e0003401800300ea00c043c403c26122841c00c981c0c1e0342d0031000c00100044245900011054054940250900703900b42c59201c495100510a50760b850719080300707004200b030030401d6800140350341d0001c6283c203090f583d40200040103404000c10340c0b03443d034074030a142d1480b07041060064908100190020b107035030b10341160f8aa007401042c401600070b0b029040d40111003884400305ca10b2528a00c050300340d01c024011206071030000c0003102030001045c03010032803176400d1002d8406080c0c80d407105a01030409051202c5c8114001c200d60780706200402071580c2c05c0e40d0100c02e40f01202ca1a94 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 7765070 1250 7763820 7763827
    0x60609090506042a0305010b0a081906020d020412030e040b060a0c03050309010e010204240503010f050904020111060106030b0a08070602120d0e03030f06040f0b010207051201020403050a030203040302031507020a0206 95
    0x1e51482131000202441010003144d13003008420700c4010b610001d41c2c00012100d65100076554440c560b00c410702001d208841c207400075112004200260024030a07040b05a800520341510703264040003c803000e041c241c0028100854403280c40c1440e110b4502c800b9000c0b90010308040fa1034200030325200a0780401010040c01101140001c90250441a0507904640080d51921307101e10078080c44000100c4040c0e00c0340c0700440c25101503401030003220b05076032440184540d00ba05003000d0010006029004070704004842c1c0e04070034403200501900740079142d60750340811412074400410010100a030800d0009410102d4104042d81d000503a40341c12000c031103078880d00c0782180c409200041100ba891703029280800000c020780000b180107894070852007118208406013000d00d115040790340f0344441a01581c0056400d20041c500980b5000d20400c948002511741600d9035a01d600700940c840c5c080700560300210b401d000b10f01c2c1c1404100611a03240e90790380100c1c80c01c803000030354465081801070f0103508000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 7766320 1250 7765070 7765103
    0x2060609150301060807060c03080a181712090709060b090307030b040f0b01030305041701180605130f080c0c0607110d022706030118030804020906060405120102030406060909050604 80
    0xc1d004038000f800d407a800d81b070066680701000740c0200c4120070100c0c00982e201001444030b0040c1d10444081600d031400c291f00d07441c040c3d074072200c0801901040c206801e01c28003550080c070b01c110141d1446940c40c14090b10905103000c1c044c00c00e4511035040418406403e00442e20151400141482141e811803400d00c0281c81e83e00f4019002d02c130304000900360f003007404004801d0540201c001c01c211000011010120b140c0b081d205401c0360384c4030682d0a203c0090402060114000343c00c866044140c03400d145440583e65516a440c002d003540d4201e40540c00881c1e20203400300148a006580f179010744401e440d000f5541c3e0360510409580001d50f01c99001028580e0070b5460701c40c0c1000314010700c400c21411090407520f00344200c0d5421200c1512a60030000d82004405445060340c42c40e83d415120000c054545030b003005121a4000c0100750440000d000000389595401c1001c5540d1040780d00069903401d041c1402d00a0399465000b1140d030f07a0034a01004001607002030070a0b03019820010040182008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 7767570 1250 7766320 7766323
    0xf06081f05030303040f020102070b070503030a1a03150417030105060a0f0e10020a11060a0512040204090b0708010905010b070b07050903010608011a01120b061902030c06040f0203010b01020606091503 88
    0xc50700415054400401004204401e484180604c10b000340c00b150503032a0345940600a610842000810b50341003840450340181c42034009403081c840c11101b40c0d0002500781d001c24500b0303119a120307520f048515020b00062065150034045000002d511085c65503041c0340104400e48501305100041024a0a0580845110f4405c0c0004044010002204030405140007584d40c108000c06480c0110005182d00b40d5144c40022070751040300a031220740c1041c2c02d18415100ba024010402ea0700140c9a1139954001101054114825035464403514129410aa007400484405811800c10710004104200100b0320010503107900c541e85140c019a01e602e20f0700464094440caa10114441d0700342414400700e51356140c2408000202a40e422015661030000042507440c1004101c0c0c11140400c0a4400e03c3c00000203621501d0003401183c1c50040120300142c81c03d0000c0350140c4a8070642191002180707020b02602208031000d100610b030600b81400011200c84024011540300008400c0c800ca090301c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 7768820 1250 7767570 7767631
    0xe1005040914070906111015030203010b0d020f1504030602030705030718060e060a0c0b01090204080127020105070f08030f010504060b03060a1806080303040b06010908071d070509060d060503070f0608 88
    0x20ba6078008e000141101d001c2441c02c601c1c1c1c0c0000c03407195003004400b41c1582410001c6044c0c00350014008802c0c00c0c4600c00b0f001030101c045152a403152410040800850b0b424002140100c0a940c0c03019030f40d1802c05001000b0b2000f00d0100e660200c0c061104101d0300340d11100c55240d21100b00e8180b951580044e90941d06d40210601c020440303640c0c44000504800954050421039001e03900034884181c1c074901e4072402d1508086412071700114002aa009544290007511116101d045d1020f2580c0546e121a101e98204581441c0c580c200903006002504042c05070070002c10035210860300b1400d0090000b0300d0202d1600800342215a03880510040340f44580280e130041004ca02969964180382c1081d96407988110b80041c0411181d50f00080d83c1d6100103119022a0007080383c95490701d120034904a10b50384040c002104112090241101a698800041040120212000400034600800e05081034080d911030700104141d444100805608244100e80c042d000e112444040842c2e42048040200c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 7770070 1250 7768820 7768843
    0x6040204080a06090302061b1207020111040906031505010b0a08040c0b04031b050a1203120f0507080603100605011202070501090c271b0e010e100504091407090611 72
    0xca0740702c0420602c0302035800490818000d0f800c0c0c900383e981702030032280315000c84540858484c1c3c00704041903803100d4140c94542c005c0304c54800401e11161150030400f003a009500021407190740c4400400810112021385100d100040006000a61405001c074190f4042c102111040c001d00304009802c22102c2c0600d0f10192410025468440342c481c2490702d203000c40c2e418115030b10703514a00701007024030f0103c7c1d20f4001c5418560144200c190710391740c11110b2403004100190120388600d8400c0b0203403068082c05102c0c0c03513103a88a02c52403404004052610b0342c140440d414080c40c1c43c074144810b036404940380e00d007043d10100c09640c45103503260107030040050b9080540010721148011426003841401032030517000c2513003a407840320b42d141450740445909001d501780c2c010b42046106156401004042002001410b014107150b41c0d80022428030340140107a0700015200240c1031014140a201e0280017044807035400002c0e140c80c4001034403007103c0740100b206200804650b10b403850380411402d013004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 7771320 1250 7770070 7770073
    0x50103050609340f030f020909060105130f03080309010b04090209130c0905010b03061905030303010302040905011409030c0d0207080309040e0712030302091206190209030703060e030a021204060203030a050604020408 95
    0x54010820003000075405134800d0000038103003500c0b00030400d900c0c02a40c0c4807400c0103280000ba44c5400c030054481d540140d03010146000d2400300001e01c0c0700d10b07445420086001e00c40d11b55691804201c26400c40b07008081d003d200394a40159240540c868024036030740811100350302440310704207080030311050381c8035840400c8860030140081070441449002d0343c0500020f0303580c01b002c18600c082001c503000d00e80c0500ca4040d030062004002503d016000003050500400000800c140c40030750f500511401141c0c404401d910000d80600b00c0354003008903203051010392001e800e000781040b00e859164460812500d106980340c811541c02c5000503c0a10b00410039882c0031165140d803443c000d8065000100c00c14030550340342c0c0114104440c041002489445481c110ba001c0e50340040300c80c1c000b03400070b29071140c06d88103d51000c40003c182e0300c6100020508000210f896240118000340342141200512886010601c4204151900002500d4020a0302880825240c1e20303080410001e005950054045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 7772570 1250 7771320 7771411
    0xb06060d0f090b06011106060108060a0302120601030c0f0602060f060a080f0604030206150102030d0c020f03071103060709080a060c1b0303020307020d03050105010207051306030602040312030501050103050609 92
    0x82041541c000a42c140c030070b02120002d0354808005581d5800c100410113815002540010300645c81200c6140c0e00c110010400a0810b449401040e0740c10b410790099103a940c84840140103010403800c0403002000c0107507454200c5400c3c140020346a490281141f4800300c1c1c1c00340401c00d41c0d91003c24460103806040110b603180f00840c0c0314a40e566101356000ea000d0b000d890081001c2e0031050181400c54081a001145051040940480140540256642140a9070701d40118040b400e00050003040d00480f40340321500d18080c101820700d14040d040c5820b000700200108201540400d41c00582500103c0009140699070030540da1403d001400200c0c103442d114201c003c0581550196001302141d42c01c81d28955940c48054088600a01501c1d002d6400640c0420007450040d46503407403003503200804503010382d59aa5810591b005034100700ca10048980c120690b46503d40328660060009190502141c04c0c4400410510308010303080c44c5982c40202d064a825804000c10541c000230080d40e002403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 7773820 1250 7772570 7772591
    0x902060904090f1202010605211c0201060303030617060402060304050705040609050a0507080402011e0201110301060203040303020f06010609030f05030c0f030903010b06130902090312040602010504031215030b06060d 95
    0x14081010364048841c003103941122000548144130349429a007024224030040308903ea021081c278408102803010500c9901c0d4003000b4004d8007081c51206c00065000450528110310300030b0140e480b01d4000441114903418003282d44080021019042501604c0bc95540c5e01e45040490031f002841c1c0010390444e05002d00000c840c1001d0703001e1445400c4011041055880e00d0000b1250440e090b2006800100d401440710314130000ca812407a251109400005030700750081c0c4000c900c80c0c000741c0c4080050b8001280070018150140720829680300c4102c0509443d42c1042c00142041d909400040c2486e8003106a42c407c22070104101c1c6e07101e00c0440c003280c40c02e05012440d10707500e90140c03b0340c0d8080d5081180c03814490800308140d541a510250342541054101901d07800250400da0041e5407510441d141c4a0352418440d0046c000340001e54008500c0703140908010700f00d503000d178070300e522007038a00400e010080b10a0700c09a815681c0c8507000f80440d4032044001001c80c021a4001c851840c5420702158 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 7775070 1250 7773820 7773833
    0x411280605030a0605030f070308090d0506010b07020a0b0408030d0f06031a0a0b030102090105090405060a0e040f1109070c0609020102010b150301080606030604020105030703090c0b0703030c0e0303090a050103090206090409 98
    0x1480743d040c0100a01819441d141071644401e0101e0b0b590750301d0b910802c01400094110380262401050203080c0864035000c0ba01c5103490036600b03030300a41d05050009000f40c1503007499480030000c0c124540b010381c5405d1030065401e540e4031490600316481035a82c0c030140c03920340480e08114000d40c0c1089023444075100c8000e0040c4001e5041c0c440000061801000d20018141802500c80000c01611a0b0b8107040b86d01c13045c0f001401005090f5070307200c01450004038032410303040b091600450041d8602c0c40701b03440310b1420f0022924010314062261480c0000c0200455000b46003c011903031041c004074486a861006034054058903001e40e5000100f0040030b0001c21002e00654101d80700c9400320348440d15a4410f2540300c440c02d44000c0d00165080000a942c41e0098100300e02d00c0c1e10410400c40c10b10340e51101c03905c035900300c86401c800007900c40c903140d010710303a00000090040300100c01444c07800c807804d0009144850203209080c149922106040255660641900c10040d800f070800e00c0502072918129 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 7776320 1250 7775070 7775077
    0xc0702030703061409010b0102070f0e040f0b04081809012706210506010909082203080a0816080106020d0e0a030507060302090306010f0e010b0f09030708070513050411280605 77
    0x1700035a42ca00105001c01e5840040c0c0d410444210300700602d6218140200c90071848002041600d400c11000f1183c0000382242c1c1034248140d00554416403100f05007800030318912113201c4010301c640b4100d001401000303500c00c200c1d8401e540d0078296002c104070500107000504003d9009a4210f00424001c0313054103858500d40c501103101d02c044d210180e0b01c640440c801c03103031003c0c0c000d803e040d018032040644886140e04400045e0310120041c074400e5682d41e41840540c88803074800c5c0004c9052080c811400d160802410414880b41000003156040000003962071020802e500c0801203c11400306a80e11040462405950400b065808a03a220700015000e544079210407806403181d42c00006c0c0c0c4030011244001a0342d820030090032241d203420701d0400550040c108000a20700104080c0c080c40c0ea0400001e40100381d40005000994a05402c10603540c5014151900c40ca051004000008401240514200384100d0301044e96403402401c14413801e044600894025465880c0466043d0300300780603 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 7777570 1250 7776320 7776331
    0xf050705030f03120105010c080d06060e040c17040602030a06030f0b101205150a0b0d060f05010803092d06040e01140d050c0405060609030709052202090c07020307030614 75
    0x111146102c210588a56900c610752804a40c0c5120200621503503100c3c8001c51603150242090740c3c1407041c1080d1090880b250350f402040441c1140ca080c0701281054000c2440352440f42c10031000c003d408452104074400000c0004096903400000204400c4180e0300201c05950000c01440449000c0e20b00703031000c0d80c0145e442c1e03c175240506800048403d800b80c0329a1100c2e50240240241ca00314074240090180003904589416481e07007000c00142d1030780040341003514040c42c800700d00c000b10900010708498043c1c218143da43c004100307080c401d455070020b0300d823180220240c8001280da865030150090301200c02c220ba00c40400500010302c00640b4659034182c0c0c25000000c621444108204a6480510038008002d5080005014a80c0c03920f0f500031540a0400703002c8030f1030320100300b0002e030400400b138002401040c0d840e010b000d1010010709000d640e02d40311441406464145400140300e81200600c5000c9020700020910304540b0140b080c1c00045900100a1210102901c010036118800b20748 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 7778820 1250 7777570 7777573
    0x3050402040f1a1305040201020703030809150c09010809011104050f0d060507080403020c190603020d060302100c05070b04030206070b090109020405010312080708040c1403030702030f010510080d091203020a0f05070503 96
    0x8482c01300501e1403080303d004d10b134141c00800305c161843d6400d9070480401805070100b80aa550705451a00000c403400b4810300300491520f645081210014160403000b500c0d00703403107078585170715803941c43c102ca801c841c10f13102c084940d0070044006000254580c0903c4000411080c141428002c500382c01c03002c1c00e40154866026079440c0b0080d00c043c01174031a1082031605501c0035041c401c10465002c0ea00801c203460080c40c02041e02501c135000300b1071802d42000101d0015480305046802d114040c07100300c01406c0084c1d01c0d41e141c5480c3d600051264086c81102a116019072404501101000d500000350558043d109110070760307680c1003010302c0d161000c81403400b00d00a0400036032814418804d0500c44d5500c81c0e01d04420508100e80c9400d901042403030650948001c2104201603a010030002c075100700d150b400450503150200307003035000c00070710380c0030800316840b00c01d00c01025900101004151214600405140c0c8441c0c10202c0c0361150790350010b000c42c03641039101402d2050101da4a020b0f0791041c3c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 7780070 1250 7778820 7778839
    0x90305120a090f03050306120f030a0201060b070c0b0c1603060b0112050403020604031409040f0605040e030c03040303030b01120504050a05061303140a050c030a030b040b120a020103050402040f1a 86
    0x90320704080c1d82d41608010015060000c12000081c0900c1c003a540181c8003500400207050400d6a86186c2003040c8000d4403503034000f0035075514a950900805000d82252400c40e82000e2040d0384072680d1000c28020243c0d03140b004103c075103100c1001c108901d41036020760100704009a076418003000928030060140c0c0040d441c8046158580240d010ba24082ea07416402410682e556403003ca03940f20111100a51642007085003c02c1680d442c004c12030f08031803981000455604d00010003003260201c54080301030307130824803c0080e040c501000f40d0701200c1c1c140c20301141d00c02107000100d41503401d45c220500d10fa850103050005001002440c441c81c83e100768202c424684803544038000410072418020002880b0741041c404440300b42020300290440750502c142050060200c440c1990003030381000e0f000913501c80e401c00c440d1403d8080c10b4003a0a0a42d8110844624a14060346074401400c01905054844000c03400b152120340c881540d20302400310070001c0411a250803c16aa41c2050f034910503036080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 7781320 1250 7780070 7780081
    0x120406020c0103050601050d0b0411120114010206160e01020c121501090501081f150608070806040c0503010501081003020303030703020706060b090f0d0602090904080306010f080108060105010c0203010b0409030512 94
    0x280308003401078170705031200d034101650041d03142c01920146a10f185c105032588004030f640380002016052414190705c2c1410b166041c0301860710f8504480700c0e42411075101c0c40901c80102c040a60240c6aa00a860045049805180143e1504d801580025002205880c554452801c08079100c1c0f80811540c8505246980e20310240c0140c560a01400b20b19800c010080d0391010341010591034298408174010861b0b030414407030f044409586a0000005c5840402004039840e03200603402d90160b42114200684200442c00400c140070502aa50601100b13002042554803000044402076038000c0032280e40703140036400180030303402c06041241c182d414684003007065000c48042e81c00305a40608038044000014042050307422056105544203682000040100d441d021a810300c1180102d181c0f95a908186d0001880344141c18000800c0054610061000f1040401c0e4281100c60074a05a6031982c002c0c00041c0c01003007011403007584a80f83c414541c0c10550801d015058000c26202102003e6544 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 7782570 1250 7781320 7781327
    0x302070f09061509080c0409020307030b0103140d14120601020a120e1003020c0307170f0406020a02010f0c02010906080901021201140117040b060d08040503030304060906050105030f060c07060e120406020c01 91
    0x13140610801038200e4460700001e410541c0c4882c1c1070b940024201c440300ca0740e82e02c0e0803c0e19002030300103850b4440800d00c112003440f000c209200ac01714461030081444c1012089856141c001c80e8000b0289103550b0380030030403e0b0f10803c01c0700da090b034225683e08400550b80034054404000382c081540a000d60031702e000c1001d4001d20945190007031900144d8a8a5000e40e07031807c0752004407a01850100d8240082210144990041c1018001c0c075002415000011300001d070100c02246400380400c0a00803060005036800b00412007100e10500b0030410940790b6016150280c0243e01c2100820141840005800e5006801424101c0e01c00e0b200c2e29800004103e40200d410000c03540506440041b201044442c00c1156040a51038000c8046900700b64507040000e0541d0700c20f507001d9075503079101c8060343c050140d02d100d002d00500040f002003074551181890991199002000340d044038801085003030501203140c020f0a00050785000366040144455566240d9403c113015801c01407242c0003081d80d85501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 7783820 1250 7782570 7782587
    0xc01020304050d06020a02010905100b0901090501051e01030b061204021008010f120c05090705090405090102130308070503040e0c0a08070e150a030e01020d020c0609060103020f0105070302070f090615 88
    0x80203840c1e0711010f95103844110103588010282c00841d035807455000d02080341407128103000c240300c403404034491621004000002d081a0051141c142c90322004010070350360710003604c1d081010800311112900c200001a070051104828041d04008000785c01c8800802820310305200ba84200d0300054400f90410045401c01790034003820010480241c014840842421400c5c03202e1440740350314011041c1c172140410385900054400f40045500402c0002803494140111030340184008c008500341703010882c014020307c0b150f100282445900013991001e00c0f4060040b0b502034405121600c810381440706207005140c1c44014203100045400d804580c40502c1003034866200741d8028817247c2c0b08618600503458540c0804491003e0694808882c2582c52082c0080d007820882d148006854410707050140e814404011701c10081a08040010300050f620351240b143c0c07140080c60800d484598610b0103034506402c42c2c0050b04c0030340c00114001011441908000f040d20781031408040842e52505d41900c0030319 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 7785070 1250 7783820 7783829
    0xe0a03051b0a020301020d0509010f0b0102030d0b010c0204050702070305060709050a030803090a06060b180306011a09120601080a21020616093c030c0b0a14031501020c01020304 78
    0x1542040580000c1c0c02401015032806200e200303031040c80d11203600003801c903401010070f90070090b1120100031903084288203e800a200021040c0308007242100001d4682c0f094650305850385a681e06c02c40345a07407003003d1718685d0a5000c1c01c05c1059041c0920701942d60303580351100311410f10807000018040380c454540e020440c2e5015002155035030840e0740b4902c0b96000203180402d288904054500494418020b0000801e20f9104042d90b4080140340c8080c00800301200500a61001e001000040b0000c400408012426050075803110451400101d00f10342d00c041400d21445000c0001c6080d92020910401035441030340a290b200070301c03c0c0c442121140c8c00d03002001507000300e000100015405020554030710003e2030188145615000b00102009510703035014076005000403410110f054030481824841401c120304a0f072103145607901607042d10180120b00300d001f004940600024010107203460005822070400392289416000101d0384060ba0510b01d005200d401400d54003940088221010385 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 7786320 1250 7785070 7785077
    0x60f02191d0f060904050f060f01030c0509040e0a08040b0a031b02030a080405010e01090516060318060917070b040606090b03030906160506010f0602010b0f060901180f090f0e0a03 79
    0x100001e08010040014099064103c0070402c19602c9035615032080b01e1080b508480c15146a040c80824040408000f0344a681454500603220442640040540e5007080c8111404101d4030f00341c1c401c031400d1240c4190003c22003140810023140100003071002d40315805066074108100302240c400305c078140003503580e070a015800030040d2804091282110951040c09100045298500c55006608503401800252000e03000500389a01c03d8181a040c5801010070746000c1c8808074444c0b0031f0001c40790031f0440c0113014585d2400741800b005041800745000c84139a056103511000d240c100030300f00d901c08030350403180d0902e80000850400c2440c85406580c0348050004d60500d00200280b000b5540009099014401c900d01d4010004400b00940c074060082c080d10b020b40e1503d043c00180c00d50b5a03003580c0c0ca11400400000c100305807600d42c20349082d072100b4642480c4040d00903a5400d60030380d054109108a940034240425010b016070405481602004070402002c0443c60f10691078100014004000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 7787570 1250 7786320 7786367
    0x706090504050709081009060e0c090c0703020a061a19030b0601030207060e01110c06010e07050f0a1101050709150c0c03060e100213050f01020307031218060f0219 72
    0x241402d9201507405021401c20b5140380c0c2d02c604516150122034007441d00c8440d1510081810030806004052404221500070a000080940001c030300c2e980040c07032507904020101d900c001389817003005210b100b550040000c01180100344034100500f0000750115015800c0c203400c40c45180146610b0b0011280c1000d01c144954540800440c080d6000e0380040c0c920586a4020281541d4203125810320b0b01c00c16441c0c1d690740da00154595062220503408410f200c5000340401c4a00750300074084a012881e0b001d1a160b4801c031946044d81e1301070722b080303003003505610388010480c0c0c040e00107680750255200004590078038590300c4800c86107401039403001000c4900d0038004200280158000003681c6101500b41c80321400c1007100802203821801900085c1001041c0070402410b2420442e0350300e45080c80a1890609161405840e408040c000c00094507680d0303208440d08a16029800031099204009000c101040240e003c06074008050b042000480440305000d002d004840604140021a041241 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 7788820 1250 7787570 7787579
    0x306070210110405031b0103050606070b060607060219020d02060c09061e07021003021806180910080a05010204031209060906030504020103140f0a0606020f0c0405060f06040b0a0e0102070609 84
    0x940b0341481540c41c003000a00000c603090f641071040e003024002501c04403010444180006098800103401d140c00b039907080051002242c84846141e0703100b4025103025a865015203400c0000784a8810300a050070927100e152141c0740da002c42c2c0fa401404550342103681c0c41d00d07100e4003d241c51064040e0103031311003c100041d164400010305003a1042000c07101e06820000705401085c2407580248103000040d60005081034600c140c0c4104040d4084182c0e0308070306007401d280104580140c4203070980e2158042c074000400c601c09454014000c2c1003d1800e549640328a0300c1c0060103508140400c8514504100c408246070384034034811402c6901c3c0303540e501069441c0c41c00c140c1c002c000c090070590406859031b002020009582000750300822480c0600b08207458507242c8a812a0741d5038120740215003210d4203004d2490400211641c01c10300849001490340c860f2000030b0750100e8404103031a0800b8000c00c00050003540c10001e800d101105449011207680a80012600c50031366016030300c0400c0130005d0030702 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 7790070 1250 7788820 7788853
    0x405010c0201120219050406020709060311040b040902031b0901050d0809060f0405060403080409050f060a05061602030d020a0302160b030412030902041103090c0a031a0c070f0b01050f03060702 85
    0xc0315107000340014a80091031802c0724248001c07605c602d010071400181000126810801d600c01007401480411280e402c40c0e41c0d0445040c10b10400c90311a5884260f2031920b90390384e902c840803c550003400c4414000000d40042580105060b0580c07080201e04000140340c00d0444980c1001540408220300c1c1100302c40800805801c460103441840f07000744000316880d218640240007a50051015603180c5181c82440c0701501c6000b08501c0d500c4042c001030062035183d0608207025128100d070215140d441d590764904c1340700c0380c820019505120701040d000100750041000018079010744d00382c490185001069802051b0140320780301c1c0039201000058042494903003155400b400a140214030a0516000103094030241d02c1040c101d1203000007071105884007080411214281603444502c81455900c0c0c00205030307501d2844000403c03407000010301040394082100c10445c0d1000d403000f4164014100815000e909000e000c0c041c010f2840180400d1a0025095100d19076036070081c8540f0000c91b102c003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 7791320 1250 7790070 7790087
    0x40203120c0f07060504032f0f04020c121206120c060702010c05030705070801051f03020f010302040f08010c02010506011e030c09080a060203150609011b0f0c09020c06060102030405010c0201 84
    0x46445000d02d440030070141c94280540310090070759555554645046080030890035210f0400c1100541c0041c7d07940724580c0401d00f000c512400304549600204014502140c045d20442500081038002e0880243d05240d40101030584407200c8407810000d40c6c3c4a03014400000304030f1500034001d60203010500c405140072802840064070601d403400c09020b80755a2503223545c10491040700d4603000050b0a00150034244102ea0384504240250340740f5620449600070440000c2c040a40122000c01c0c0d03444640e4000c1d01110010580c038103d0702126581c42410310300908428413181c00550030480454020341c400c280308bc89902d40c000c00c1800360f0005e03000940007012004c031001e090040489001964400c01c0c4000384600e0f02070203002da641d04d0f00d00d4031500d05101610302544608002d009006903a40d12501e03071400c40804441d400007510680c01c11560707281607007500030005465101e01041404036900a40741e201c40030030898040d0b8603040016078072402140102d500190340e54505201562181800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 7792570 1250 7791320 7791337
    0xc09010b0d15051215070e0f010c050102040803040305032d0d0c0201060306230f090d081009020f0a02010b0f06030a090201030209060a021606050a09090b010e030a030807030e0604020312 82
    0x10182c41958403030103c2d0021000a2100000350448581c1c40080a003200e44507034045503515040400b42102400240300344400008181044560340c0c00c03108104096040f1000b40c692141240c2d11681d69284c0b2540c0c1e5440404280743c00310170b041203030490a280390050010780c9803017100c4500b0000750985010040c000300580710115902c0b080000040303200c5104041209042c40029902c11800707150103542c0040c06042800b19a0600f030402072070803404620716085007840d14104110f03403180d082c0c406008440740c06c5544201c0c4009000c081495002d0010102400c468009000c1c0c420b50320208607444003041049604441e00300006024030815130f024064481c0705040040c103004001002c0b50054000700c80302005a48003807240d210712610181001c00400552500503c0c1114154008208040034402d0f1450f02c4c0d280c0e0251308040e806a00c07444098103010301150721860b006d01b0003c1000c5810b440902c00320f45811a1441c40c1c100c04103100b845590050010000c580d8051004130702c60b0300008c2c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 7793820 1250 7792570 7792601
    0x12020a020a0f05011b0801050a051203030703020c0a0b0a14060301090507060f0201090b09010501030b0f1603090201050d050405100c0309030503040f021203030703090b0f010815060402040f080601080c09010b0d 92
    0xc010440fa0355010540d80242c003d030b40d10741b110f6040400b40403050b406604098455681c2802403081e0f000000210b036071000c450305e0050b03241d621081e80a0f162007081c00c0000c0c1841c0c4514100611484540c0c0700c2030011041148460782c90b01c0c2c030b0040c18200c1e044002c015145070000c00e824441c61707010750035200039003c07903200010350700302903442d138105000307003a02c140d903160751034030010000e10a03e254007580111010704948018284040d04041c809aa0442c203c01e01d070f290182c1c5015a070140082c0c4030308240a041c107100e40c0c0742a01d02640c03150071000c1d00121a038580510250b04038440d108102e41d403503141d00c900e880c1d900c442d1604414400060000c80e40710480d100400c01c03462f8240b000e1400b0705020b480200c0c7c0d450781e505d000d088155009044040950840c0c00410840c1000600c0d10005030560810f1185034984101045c0030780325a4008404074135460400080030703000010350604a4000000740d03907080d0443d0082201e24030081c82010315410003071000c8001d000840e800091141410403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 7795070 1250 7793820 7793831
    0x1002060a091112011b030b0109210209040602030402090f07121d12120105010e0901090c0201090209070e030c030703080901050a020102040504061211030105010f0909020d020a08070612020a020a0f0501 88
    0x10018034071140f400005016070b51600240d6441700141d480c2d40c1d01e4403d850400344001d610500008103805030354458400c48100310f82d502682400402d920280e5150090481c203c1854a414848003962040c0d070200e006694980000b500d6101e00c4000e1070042d4090341c1c41c0700700052000c5d032660142444140072003504480c1c00000240c0c281c200580c04407075407100109521a503201c0c5911008c031105a201343d043c44040341c403606040c7d031103020407070654509040000b00410300e00c1d42280103043d0040700941016404c0306102040750400701408040c1e80071030440785105145001d140d11141e0320320000303114010a02080c6000e60040d4080c00914446200040c105543c520000b03065551b2039200503c11350210003024240300e45030035451580c0d201a0300a00c41ca51510b0484000e1050078414840d04641c0c4280d84011552414059100c2c2a002080d4040ad5a110a0b01c20b84404841c441e50b0046442e90701942400145130081d2008440b0680141104c1d250f01d03140c1c800002039103001100e1555884 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 7796320 1250 7795070 7795103
    0xf060d0b0c070c08071707090c0905010804030c0204050f01050a0902070203100b03030d02070c0e06030102130302060d060b0d0606020f0f07051302041d0105030d090503030706090212060403050702010e1002060a09 93
    0x1003000e54010700f054103c810001b0468100d007030815410ba00403c01d0107041c1455074030816040640c0d0030455a0a18007100f003a91142002c560800fa400e000039405424034042c0515154000c4019050b10022502c2401045e41e0b003010704224881c0e220700a401d50401c110701c1e012080300c2d9001c502c08200240030340b840e0000070081e140407607000280032101d8002c50741050104600c02e01943d640100b00754002c51410b51049240500100d41c0c4c40005d10a0741c000400f03150300e25141c0c204a000b0f100a18060703841d6510303240c250010b40b003e401075000611400c0001c0c0c20b01b08000503407005410408000c0c09089041c441846108148000d02090054080100103502c03812101040c40c1481c10203c00d034031035410300c810581480b0039040340740c0030071514410500481c2c3d008000c464180e40e1281300003c40e10034034030100c0d218003120340e180d031003601452040000303160b000001000c02c18404d0b65280c00081c0804200000d40e80c801201d43d006a1000b4001003c40c002540141030240c020400901c414444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 7797570 1250 7796320 7796323
    0x30b040c0302030a050102030a050c03090619060f1205010c0311030708060409080a02010b10030e0d0c060906020408031206090103150213090e0706110601080606010507030306050603040305030f060d0b0c070c08 92
    0x21a00b046804e80e47c00010002e4200c103521941e600410307012003080c654104031110326981e4002a100e81c400e84050100440c911805e5440341c4001c20210200d0401c1aa40d04543c1c5d6004480b030b00c094445500788440b0106092203032081c1a4400f0628100c0c9056894240707003194020307001080c050b0041d5580c0700541c0840c44030b201404230103c4035030000c10780c081a9018454481c4c2100c1150050506110b08005403890104440302c141c01c40c0e107003240d81560785003407920240c4003541000d0030241c4000303004218040084001c0460f0041500340e40c003980c0760181400028802440701610700750780c10b50500440560754005040b6100322094061b016600c4660b201c0403038820b0743d080351990740082c02c208170741134000c9115108040c03810003900c15585060b0003d91031b0000185918100100004d003001054081d80c4440060700000d01043e84900c0c040c540644694400c0d00c0840480d1204c030002a10741c94802c1001040e194068402002a1140c68070940181c00010003211071204245001c20ba0110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 7798820 1250 7797570 7797583
    0x807090b030a020403050f0105060105160206040b03010305061006051201050d031205070e10020a0c050d0218010e041a04030c022403040f11090106051215030f0a03080a02070c030b040c030203 84
    0xb91040040e0b8039491468454034003c0c40b099001e4003a41480100041603811100f03845510a41c80800034030f5140520004800e07118035040b1088004c0701000100c180480010064801d080546009440c0e036141c1c6002d5603a0300446641d0300200010b180103004904281c80074101d040d200e800c10001300800d50301700d4415608200c49450004d000c401a4000618010981c44080d17140340c00a0190b101650b114114024010b0158600412030801e809046448516500f800005000c40300320b010b503150f10103801000000d680949003d120900400704041400030321b5400796602d03894210002c2040d600748009c05840d500860001250041000e01c2d40a200f0025032289201c0c1e20318040a41e03480c039010481440016450f0700440109005201180d0804101d80c020034620b6240d410a41c2c03007a2410300d01e0020822815018054840a10a040000500c02040b14425103c007080c030f039520345014080340a882009442c940c00b804c4200042002d9a20440d00b1130300075842500b0045e180c4d00800d180c41d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 7800070 1250 7798820 7798831
    0x3050307030c03030606090e0a0b0d0f050703030e06040b030f040c050307060210050c03040f0807050115030b0403141303030c021503130501060902070b0a0b0a0e0702030a030b0301020306030304060807090b03 91
    0x1c2c00c0001140c1007503414030a10000e81046d0800303038001030074540709507200c02008180c0d80c00682d980400400a603030701401040d07155807041440ac0801158980640c580260348412004200304034111150344c42c18405680a841100c070755641150740e070000e0789a5804002c3c0c81502c0030394800201298a4031700f802400301030f0050303400074041c600c07110340b04004841008060514940050052000003280d0308902555903070000442a114585810400d004003116580d4006c40c0100c0c2c0303400810486280e001c1071240e4000c0d26007640328014280024003510a01c1b01900d295040401f0602c0080d0140000b842d00500103440006414100740c5040480d6100303954901040814012a00c10403e090107250094003003650250b0034118143d4030701ea02c1d80d00240c80b6560030b948a24840519840d00c100c524010808060004000e09010b00040d4a90b40030307108200c002070a148076101c0c14101402240d0161101a00540ca41803510383d007242d0165014103d030301040b010000009120b0b05203800b41d400349 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 7801320 1250 7800070 7800077
    0x402101803050706020d090f0605030402061305090a0b03060601020607020706050c03040306140603070906060509040506122a010908120309030d050a0621020a03060b01050706020d0506180c03011401090305030703 93
    0xc0f4403051000c1c011f150a81d004c6480820080400d100d495406016240c002d0743c15a00242c48000c8140c2c010400f035942e800070354002120008000050340550058001c0781425001d46440e516900012621814101c8080c00503900c004810007036035102d040104000c1a81c0010b1344c3c2090349994400c01a201c0065038029548281c2c0280046450180700e800000c00018034200485864040d002c3c1a03070244103921489142c0d1000043e560791600d5a040e060200484240c0b010001b00499801881c07465413083c03500c0d0810003920452550164003140e043d2401100200080540d281e082c0c050ba5200810701101400140712880356080540074150003103454072030105045c0c0c00c00a108240d0380060386070724414030800000c9070241e00c0c0c007207403202500d0f0003074008910800080c0041c0c60070301c2078040040055100040100301030174241c6c00a0701608040312030749440b00c240c209403c00c00005440030924064100010445004000411000d010f03042c1410b8203095030f030361100b90a5410502050f00403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 7802570 1250 7801320 7801333
    0x2d011401121d0601050d120c03030209030607030c09080c090f060102010905060f160518040b0604050307030f020306010602030702061605011506020a03030b010908070603020f0f161109040210180305070602 90
    0x1600140143d40c0900390a940740030304164607842d2500180c130b040e030210003881440306911043c580719404075240d448002e42103961504208900074002c0c40b400c11680001688040b0100c0c0c40d81c0003141201e40f0810080c06070680351501d41e0101a000d0380504503d0542d07584001010020b80c051104030300c901901d020581e0b05181050901c8005c0c40041215020000c0801440c40001c0c0c3c164024030708000c0c02d50f00000d260b010310021070014400c5402c050760506c200354002040040402504d10040c0c401d8050b107009076070700e840590383c81c014020300039400030040c0003080800d54030707001012a1602400000c64100c20065a2520101042e0043e00060304801c02100038141c00d03000750380d0740c0c0c4002c0c600020b4172403410001070b4807007600b40682c20401d40c000a91514011038103043d00e00a0070340d01c05035607032100c0e40c00c4510007071340c040c540803569009054102042454240030780340c41a6006000030752540b0300b40030b003141c000008a560081502e0540008800b1910400041000c1c00c0326400402c41e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 7803820 1250 7802570 7802621
    0x10e07060807020d08010e060301060807080c03013c0f05010303120b030a05060106110c04020301080307051501031707031b061a030604021e0a1701052d01140112 71
    0x75685004101c001550300086000b00c8190f800307411141111b071101e0701c202e9103031110307000240508016440411180b08115002c59021004500d00702c151000710020130402c0040c03454004142d501d0f400045000f0300220032160a170701c3c03070000c2c59921058400e00150f8a5296a40b80b81200c4080c0c0050f00000c010072000800c2c07400f54800d81c3d40741d0408400a00d42d40e005a43c7ea030ba03a4180c140281000c01583d1805000ea40c032080140a010101c001c2c021b64803980c449000d40e1740c03500700420545207481603100384143c844015042d5810303a40c02c20010170586d8400030306070b0f45a0303124034000c80402680300d40301e502c00380c5c4040302c05080780c0c468603001c540a61070905411001c00b105120710305c80e8101005000069880451542c40c1401520300c2e200c146045100117401140107a01c03000b94070b48110000c1564a4042d4037151040101c90134140c45483e144014000740300c0c5442c1401c445002900042c00490150049034540a00c140340c4030302d6580e010000c8000b070300c441420820600001c698003a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 7805070 1250 7803820 7803827
    0x306060806100b0f0412110301140108030702010e010c0501090b0406050603010b0105120411090a06030506010b070809090603030f040306020309070e0708040b090c090c03060a0501050901020a02060f0c010e0706 92
    0x200242120002407030030342804048116484054822000b00000015501c864080b5000c103030b900802c513111142c00c050590342000c218040e54050348500ca07510b09400080c00c2030325813184c10b040c1e5510f48000d40c14144250f00540c0d6428495103003905000e04114550000382007402144803861046401403081c0c01c051503d9000c0d150302400d11842a410686d0449031660322005070303006603011000202481d160340c1840c85500c04040b06098100c2010000c00000801d950481d80840e44a6002c441c2160303070703e09a08016004034500288000001c201d2400c0502d40b4840301900807900500b564a0a00700024a108540c440c1e881150010380210030009480000c0c0b0201c0010f1042410440c00d9247c14240204000c00040009141080060100781d22000c10042c11402000c050315220341802c21030315110301e82d00111200c0f40b04640b42403001c51554851400e03a40e84006c180c00070000000150308100060b000821000d0740e9407001d10440398082c00c24002c0d0310f16411804040c04405040c4003006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 7806320 1250 7805070 7805081
    0x15020d0201060503010b010f080604020c030c03032e0501110f010c090504060902040e0f0c07080d06050f030d050406050c011506090501020d03020304020a05090403020c030d020d0e18060103020a020a060203040305040306 96
    0x344c442d9140841c240d4859800c00000c1c14000d48500d00030001765039070700c0002e009018009601c031251001150700007001a0000007580600e400c812078408650349200341800c85030041c2c0d1019484071000e201080710b54040d20341480000c8410781921302c414a424000c90850f03131005032840000c1c0c82d4001c02c100304c1c1401c0c0b10301d82c081c01d102c05055107001d00b04128035420810160405589404102c0021040703110482900c50302c4e54040925651050344601c07401c094000350007018860240300c03000074500e16000a5842110a0585401d4185440c110065400f40c2103028103941e03a5480c3c10701d03583c0c0300c0d604c08015400b4102945401c8c110f54103100009203403000131769008090500c108240000359840720946421110102e90100081e6101d2408a00b00442100102c1d050711415180e025555004a95050740384100c0da0b40c3c40443c09030004000c500c00c5400b43c4005401c203041c010405a5200703400411224510740101c50601c9810b9544100700da004075001d0b80000c101282c28000c011003030192 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 7807570 1250 7806320 7806329
    0xa0c0f03121a030606010e010c0b0106030b0a090b09040b090f0a0b04061103070c080a090504020706090201020f0c011205040f0b0103030512151807030b04060b0d1503030207140102010615020d020106 87
    0x5500d0311000b0600425603c02d00079044034140310000f07080c0c1003540c0c0b03d06036100480c0d5101c01c1b401b20a59580c4c0c3d01034003804c00c00c18500d1144110f800d0201d0321400710300c01d01c240d64400810b40c03035050700c40f901c07410480103014002c03044a015124000010b1001004801c507002c0c45401c220801c1c2c0b03000d0600d44210b44008454074818401081808002c9a1200c200040d99030000007141d594000340348207032060461603105507001030000c90218240060f43e4000700800f4000c3c1c003070f81d80145640100300d807202c60888000340811040e2079180040140e59000c10f03403061040403244412600e6840702101e5050903030040380041c6001801c0000000c0194200d0b403c01c1101d1180d0143c0c41c68480061510440c03507092241c0184040001450244a5005070117040c10107401001440e0301c81c0102c14041c0e120100c5250641c1c1808440c1c080b186001801000702ea4156003d00215030411608901054160890728119901c842c40800d218590411151a02c50541c00501c40d84110400103400e44145600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 7808820 1250 7807570 7807601
    0x11010206090706050a12060303030c0e0303090a1a040305010908030109060b03010e0c090a150507020411030903030609131506030203060a0c020607050c011508070314060606040504020a0c0f0312 85
    0x340701c441040001c09809841150030580d0710b0742810341d800c0b1145807034101c04850301d40c1400000414982c0650201c0c6800400c1da07103040301554008145640ea20a24031100d40120221b2020840046116610088490300000303080c0303480e6580d19450300f0b44070743c01d5060b1110b04000004125400403841040010907a13540381504640c900030b001082900010800601c8000010781000300d03035592140d000182103183c2c007401c10050b44200090403500b1061040380107e2800211145c1d2140210a803072154001038000c2d481c0d5903590081c00791442c009405881c0070141404241c00040503a4040d9a40344410080069402d18600405241140241004d2485403429000050329a404221203920884d503090450743c420340900e5481c018600201540c2c0d0350011090045031040011404030200d038014910740092107020b0b00d060380c90b00c00580311140e200c401007004000e06d081c250042c12114040d400d01c03800e43c100c0da888050030607018684c00c07000140122401e5040d01254401c04141000c01030303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 7810070 1250 7808820 7808833
    0x60302010203070213090210030c020106090603020609040c02120309010207030801050621090c060304080405040b0307080a0f030c02032d0f0604020d0807120903020f1e090405010f0c020a110102 85
    0x800107900c910070681c01900a1040c0f965003e4034260300e40011b400d265000d890120a4604440c00030300610a442c82840103500b4013000041150032805010190b0307800801540c50400c0c850100030040000416500541c02440229a64144450043d5218840090025a0750311183c075005000745016040380c0c1c420001030006122003000c0c078400800e4006848450102c036116040100c0c40c1072401c3da6a150300000020420082006150241c0101d41c0c042d40c050110700072101c1010384680c11400381c41c40e82c0d400402c420010840082002d480d1501034103204200750400e80100e410289c5943d0250030310007400380e002900016141015038694001c40240c56050901a9450348a80b0b01920103031080e00b6010090301480000c0341214021644480141200307980c8490280c80400e40f03110980c42403220f141501120b0400000321540700c0c0304420b110b8600100724040014450004d0403d44040d035940c05804c410009030301c6940c0071b90341a500140364030401464219505001c0f0640307a41190800e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 7811320 1250 7810070 7810073
    0xb070c05010801030b040b101701060801140106120209010e060d021c0b0f01120b0603090f070902030403080a090309050910030c091b0c03030b091503060a051902070602040503070b03010e07030603 86
    0x40745c0c0f503420542c4088601250340ba04481c08904003400d27004421051380c00224120110015401003044920280c000d00c8004404c0d1404010070500344218004180480010300c0c0c0c2801960040010a00c141040000310b801e5001007186a0009107003140044d03800500607400024842a1005000100d0360a02036a81e2400200d405417014103280760511448000d0150400380c981c0142c08202c42c058035035a00c0c3e14180c0c2c0940d0b40c454034002080c01e40c2c0146071020403800320074000c603441180c240d100d1703010a48a843d410001003550040c10340401400c6130300400c4543c0c0c8c02c5500f9020b50042045d84000c0c6045040090041c55158841d002c21842c1040b4054001440458490801d00c17506117045521503a050a03005480c94848466120070400c04000348080c501002c807043c0c1409404481aaa5891030703100201c4006030385031407865412500e011000f80d01070300103044a910a1001504255643c004640f516075940c10401c12400040011701220303010941c926402030a07441c2c14440076265 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 7812570 1250 7811320 7811333
    0x105010b040501030b03010b04020c0102040e070e010806010c02030309150406030f0605100503040213020f070b0a02030702060f060307090e060103211b0c031505090106060201060302090c1e040b070c0501080103 92
    0x303030b01c540d6050645600c1411400c0c0d800f07601c94429000098011342d620000840c200e4000e43c010b01440c1030900701c203030100d01170a106d02401c614003c0182c5031440c481e11850015078501e4540c00040741e06200800c444107458680c2d40264240e082c9059100e40c81d1810302c1c40240039104000c20200f65549020420012681e80000d20806c010141c02e0884c1c1e681c0399400891480c49502a401240c940002200c00c2c228864a00902000d4001c8415544e50784415030400309901c0141c522000690002000c582590300e0915455045807000782103562440d951501d410944441c0b181081c1e443c0c014800410900c918003480b41a409280c0c001c81026204040000e850f10003041d050301c03145034245882408101c40072110034003541d0440c0389510b100f65018000300181c04100e90303545180d42000000100e40f4014000d86080d80c1c3d008080f40c074503540d40481151540c00991902c28000250003002a018048000a0014140940b089a50f41c401420140c019160f1170f03000c02e042028520042010860 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 7813820 1250 7812570 7812577
    0xe010e030a020d0b07030209030f030306040b04050105030a3002010e06060301060305030a0e0102010603060e01020306010e03010e10020c0a02090103080703030c0504060c080703020703080307030f0506040c050a11010608060115110105010b 104
    0x1440b1240d440c4c1d589950b20120001d024051005415100d0001410244100007029501c01c4604882c28032800d8400d10502c019541c080c0304aa41580c02409600001800b6032110200c11006180182d2040c2c1070301d0841d103a80848070385c42c4c00035075503036114074507005400c0c003c0326402401a402400305500d5580c82c1940c2e031145104440401151000c180080c0c3e1003034002d0002140c009400348180306010030014001d40c006d403500c1d404a420b41c07050844038101070141140c0b00c2c80240142c0b401c0b0300c0c3d01d01684082d5111618407041402003219520040e0f4544207a24040d6008800c2540c035440d1a01d030190480f1190b040180a204052104100d0954000c50f1203400a6000c0107280e00c4442e03501d400e0f894080c0315000100348040202c00c000003581c2c10f81c820018148107139000e2104d40c41d08828401142c0ea484c04503000640300300691907600340a07903241000c4a161000000c0c0f03880d40c403030340281408002c0c4c1003090b042c50b1044000b105182e0140c0c0b400121032031000200080d52400021414510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 7815070 1250 7813820 7813823
    0x52a03060c0f0316020f100509060702010c090603020703090509010305030903120306030703080703020f060901021c0603230a06050f0a060501020114010509070e040614010f260c0403080a0e010e030a020d 89
    0x280041c0c0000e14207172081c40f0740411003000900b168a8040090341002c00b800c0304480345c00451141000160030a4814000c1d800c000005442e14549103040c00d001714060351004001b40c0c10700982a100007a580c44017a80309009600030405161940c88000805051102e43d0341248502c40050091010940e0041007100c1140d900100e51940d9010302d2409a087c66140d04040c0180d0068000304051040190001c1511b140c155011020380c520345110b14044a0440c040036200103080d600309200c041c100307440303840901c121b003044444035041e0355034001c00e81e202100d441d003984480c001489251000d0f8029100a40340c05d000a00c18450080400d407007a4030148105482051403002044c01d1500a10361920b1803180a003007440b042e030f282c06031901041214441c5500040d0326294601d10f041c401d4880b802ca1440200406480c4200032031401e00004020345684000a8100030020005207148014031206c0c001d5140e0b001c2d110440c000141600100b00384060098020201c488016903d00304500d030b005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 7816320 1250 7815070 7815091
    0xc0602072702030a0b0301020711010e0a0612050406060b0c0c01030615020c10120608030306030601080d050301090e030409060311100f020c040e0a0b0c0c010f02190309052a03060c0f03 81
    0xc4d95881c01d40780c094140e01c003115405510014044041c040710090f03000c40041f003a260603019903010b0b01401404041e40c4107000004100c0d18240345138010507009540c0140c090740010030041d80b11007103113205500c50141050f80d5841240c07450050350301802048020001c0101941d401022030760b02945070309002048a2040c8060000d0b04c583d5030082124042d0760031143d600b00107681d1280c1d20542c1daa4030030703200b182c441e10030407000040032800024681c81081c00c070b540d21411640303041c0e0581c0142140c041562450b01040c0f00115241d040c41c881c100085019003007034a034094151062010090701071036107004025020f02074000098000810306059001a50000340408014182a09203505013000070081e403c100f080c4820111540c4c00742511410400080003581c8a00850b4402c03481031008840e42d030201d0342072507000700380250b00220740c040c080e1084c1e0f0251050009844504d1007901522003010706182d06405036401c04000303080e071203030015041a14054614514170442e003c000c0401718403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 7817570 1250 7816320 7816327
    0x21e031f150f05060721020703020306060d020d0311151006030c0207030803061210020d02030f0a05010303081801140403090812040506090f010903080703030603030f05090907030506030111070c0602072702 90
    0x4000c20030700c0300e021b18410300d50005440c481b5810700075144c0d600d0744402da2103449070a010070103500d815101c90289581c002c00840180c20f9030317a03060720020a040500000da018005120150383d0758540054403c0034102c811542031410004041c0455600c0a1040110b43c41a0b00510000724020700f169041001202c42d00b486c401c6e50060f603840e0031000703034070a00c8050000c1030742c1d20000310355000b55001f05004401c0803076036038440103003070f01300c0f042407001500017941140450920300400400c1b0803a01208000895a01c580080710189540d0030b4030114006185d24004001d807420034007840d111114800c03030861500b0b2514001440c503014044115100c0c40c03400e984c0d41c545038001c40ca100e0085510101d890b80f00c5001c0d083c094024007651105802103034108160b5680c2c0343c4100d003100d0344070360014042501515002003c41c01080c000b8240e41e0159030381d10074641c9907664840a4085140b01d9481c4a281074284680241800c8255110a914600c0007246070404038161a4215404107228001030701d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 7818820 1250 7817570 7817573
    0x50402150a0801050f040b130f110a0507020603070504122f010203031b090904030507060c0912060f1d031c02070206120a090605011205070501020d050403021e031f150f050607 77
    0x18041414188d91004031041c051500960540280241800d8110308000f02c8401400784245441391224550011713900300301c120010326124000d075401a1252030107900300358540054664116010809492040e4040c05160b000c80c0c010600c400c0d1101d03241d1001c81c080fa013210003c0e540340406003003000500010142c1a01c140c1720b03401580c0d88800700508022050030542005000b50340030300000c0e24210f080854014896001d842d0b800100c48088007801307072050b401c2d102d040040090245266500b41c85503041030b601c00c400e1910a04241c243d1019641e1404d100c1605048801c000200d88440c0c0e00600004015981d00c005440300e9404135002d801c40356031001d907040c00500c21100002c09451601c400404d40101d0b41c81001012485807007100c00098864006a17a1000445050400104108010b20050034000c01d09109241c84521a03441d503503d62001074245240103c1101c2070f06004001000d1440e0a0b00880031510507510780e800c51181401c5040000000fa0700603a4001d5100045090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 7820070 1250 7818820 7818829
    0x20a08030402030a1e03020c090c0313050a0b1501110105040206070b0a0b040204090b01031a0906040b010e03030d140c0702060d0e03090d03050301060207050405010b04120516060201050402150a0801050f 89
    0x1480c0e554010380c0417800d1800c1c040070000100c0144e00980041c82640170154403810310b035814078001c0c0328420205055030b8a002c03884261100a000482c0d180c0102c8401000003600c01d0a034501030410403241a0aa4010310001848007402481c825200ea042c4428000036854580c2128105a0495504450f40e81c030203400b40c0140060b6150a03401a04c001000511311089034000190980240d809220001180c4409003c5075001031201e6440054000410598030b81a4010f0003108818100000c000304c0200000f419a003119180c259020380340c0d00c0c8018079011052145034000100c09686003002e5141e00410b965028484031094901d80e03a013150200f4034802c100f0348000d00e40044c00d060b0020f1140c9401800d5030001e00c1890b001d4411000042210301d0700c0d00410341078400d052074003400c1c80c1c60500c070444070076111441036880b4000c0a40f0305c0d004003581030060029002c160004121400d06206200e0b40c00c00c61048500c080751b0a03c20803114940c030048450444001312101c190034900d800c0001e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 7821320 1250 7820070 7820083
    0x203040f0b0106050a090905070806011110050c0408060601090806040305090114031e090a200a030803010f080606010305040b160e190906050a05060d0207030509060403061e060501020a0803040203 86
    0x240141c0c00030000003443c40d510a009009440981c1c0e035164240d540c5506050a40714242c0301c01010910010016205512078a18a68560900000c945d51a4400394010044a070150b6110500303582c00035040c001c03810100301c45600a01c0c28a0214100351910a1054076528080d0000317042000000e00f07001c481e0b2241845c1e4120020081c4000d03603a0400c044445603918818001d0100030442900040c600800840c99450041d001160401c40c0070320b12100d403010711086405158000c1252902101003219040954041c041030384c40d0588290506241a15020000b020141017504003810030000800d07101d48903030404180c0d2100350413200490340030740303030a444510b545802c194841052403070741499580490845e004d040040040f25100d00134000c6102007030103180e401242c00c0014000c000425402016058028509903040c50803207000200c850f40235501c16210203440c1c0900507080000b441c0c821103e007640d244204903051801c1d0000c0d4440030104001b52610401100180030754505011b003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 7822570 1250 7821320 7821323
    0x408040e01080303062806050d0204090c0203120a0c05070b06011211042301020706080a0609020a050711090405060601030b0103020c060109050f090303010b03060d140706020309041104030807060203040f 89
    0x2002580c441c4610b0390f49820440d4500e204a9001250000184000704c80100141402040200c42401d188060325070368045100c00782040d908000c0010020b0b40f43c4500c96030a04254040c595400301c440300b00c42e8038000901100c500914060390555a00c0d001b03803c07107529a500c42d404246950303540b401641c0d032010b00c50f19200c00c581001d80840400d40104010006c1d940030321101e41c0c500c004820400980c0006e0010a40035a000050501500e8052002c5a80c40b11965402145071515060030100340d800c40071101000c6800855103904224030b5218202c203c40e401d803011034503450980c81d81c607950b1401821190505070764640905941e4400d030101d40c0121607941c11110503594401c900001000304980c1d541c21400f030031011580141e800320444e4101c0b42501c00a5080da201d40c41004aa600301c807004507100b0031090100306c007225041c8682402403019801840c0c84003540d90612041c0c80700400c129a0b142c100f04007e0001400b12400c0c1d8014a030045070040c0c481ea114a4014200c1d86060700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 7823820 1250 7822570 7822589
    0xb1201060b04050301060605031905090a080403031e0507050d031104030602120106030e0a050706030b0105040801090b0901050907030203060a0b0105120108010509011103060f01081f0e010302030f03040b0f03040804 94
    0x800310708655600018002c0340d40550080100c0c03683c0b0502110907000595146415107040302944803110426084550025046e90584500545650390107005501c241d004030040381c07804003542d0750700105e4420080d5060746410103614082c003598541d500da00507003c0032410326540318020308540d5084002d03580610390003141190f44000082d07940421500c2442640d00080c1046412a41100c02080d8442000d611100070900903040c04001d6016001d42d880705410041c0611000411450901540107650f004501034241800e00d40c85135070035220001c16043d4103031300c03600d41000141c40014100e075001d00c0c0390074001002d031004070040f02c20348900300e0144d6003050300340d00200710200c040d8400b44c0a060658020018242240c065404600046501b20b0b88003402141501555004a00d550740c05440900c15640f1146105409aa5421760740c00c6089040041801842141400c120100e00e4407011001035042c40c1c5090242d102a121f40c0801140804000c00450100b010420648000e41010b12 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 7825070 1250 7823820 7823831
    0xf0903021c060f1112090d0804080702060d14040203150702070905090a05010c120c0e090601050a0e060c0d0e090f011206020c010f02030403030b12030405010f0c0f030206040b0109180201030b1201 86
    0x11a0b0100d1500840c2c04040c1005c00c02c40403420b62000003803000b0303180c1256201c095980d9030790b403980c2850760010401030b40c028004101407044100148503a001420380d2580038080390810740141450010100c0c40d040c0246110400c1c0614030b600003072000212031404d08003068590f180b0350b4080c209444403400520942c282503071542c0c01a003000c000001d0900000e4200615034405100b00c50f00700350f09031a15001400b0030003060303a40d44104003d01c0326030100c4c10034030b07010740b031960114100c2e80c8446011a801c3d040a2110700c00303d540304084400000e0129590149828504e4142a00729010b2048451150140e0300410400070503070140d038000749140e002009810078151509000c2c0d40116000c90000340742c4a441826850542c07000040a50420004d5007000e050030300540d00350302140c1c8900248400391b4900313030014440012600581d442130380a401c1601341403801050a10060700420706150400100903802041c9213800e680403502480c0c0422907440100c0414120140c00346000c141c0e50810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 7826320 1250 7825070 7825091
    0xe07050a060c0b0a110a0503041e0803011a0c0c0103090c030b09070e06010c050c10050c0304030812060102070608130c030b0702010b0a05040204030f0212032106010f0903021c060f 79
    0x968002e04074020f141c0c1c21144d6a6a1500e1400c8070607400603118401018489000c001d0710900c059036100d03100e4240c6a00c1c946007601111180c40c030f911800c4980e050000014880380888085402c441286142198280021a103110b910f40c15180359050406559109080500040301480d4004540207004442e0314240b44580d10707210140f5000e20342e40d1582c00004107072035500c120000360050741c114020300700890b812801c0003c1e8220b1506484d0411030144110241d40405000030001540302d01441d41e650040e80c04280301d25180203020780c2c10341d00010700400c02145c000c2c880c0b2f948440109000c05071401d1524240a95500c0c54102601c60721782d81742003280320341c1c05500c09002c2039001c9807003994803981c030710400041e44103074000240794181c0324001000504040ca41d050720034909400343d03424262600101c4c400908120fa0940070703600d0401c11b106c03055030401050381705c0001c82d2030301300300060035900807840c610060650401e581103900c0d5000c0074050a5441111800184a070500000401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 7827570 1250 7826320 7826327
    0xc09060a05040e01050109081c030e0d0905030601060503010e070c030203160308060f0411040506093c0616030e01030e0f030c01050108030c0d0c03050904050f041b060509040e07050a06 81
    0x2e40036944101c00c0010000c84c840d03004140c11000c0318194030051a182c14102c50236905066088401d1301030603200d041c00e41900b4424001c10080c0c050940c0c40707507501440c0104140c03610406a1000041c000e007040140f111b00010100c0aa100045051041b00b43c1c265180c22441e503c18440081116050b00715a034042650081e5400d00640c1d040f240c525604d4190000c12048544100c0c148123014400c010800a506203031000d0040c02c60002e220f00c45c8401c0c0340300b0341e01c2499619039440c20031030036403108a035021503035a6501071400c1041e521242040000011420000001311018080c0007041107450311683c400e0300310100300400729050f0f41039020047c1440c2e55030380100341302c00c0c040d509280010420000000a072000f84024000410a40c3c10001080e540c54841d1002642041420048440315807101d00a443c02401074480000041c5840d0a280c2c1c8071100c02480d079100c00210010400841d5404415110074000071280000c3c50100700d50003d02e02042a4411604a0103980b0700042890300b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 7828820 1250 7827570 7827577
    0x4110d061d0111090f01140d0507020f070303020c040203180d03050702010b06070c0e040311030a09060f050306030606040213050319060605090702060406020a110f0a17040315050c09060a05 83
    0x1188444015114818000c10b4280e03031080559840d44082400a0b8030300303290203039501c2c074040c106042180000c100c0054001040e40828580104a9203a205104642d40e04008104039030200c90302910600b070071590020b480700c00000f001840380da0088049001d50544e00680240803164070212200d003d070304c4034090041d10781284c5e24400340d441c0c0007400b2382c64105001200c141552050030b42680904160078080391800c003900c10b801b04421480c010b04031580420007041ca449203a01c40040b080e1a01e8030041c180b0228510140c00c00c41c0900500030310342c400203120307a04004201d50150301c3d1511905060503028041d880640c1c0342c421410500000c260b868100701e0001c1c0180c405101440e110b40500c03465070700c00c2e51b010b00180c1c00200090f01084050b805000c07510010b18003d22300c0701011410506c3d0050404030100260044603200d410040035904450300f640c0c0140140e030401c1d1460f2941e4220010008200c541a41c4900019000c0380b4000100d402441c1c00422560325002200c100030107540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 7830070 1250 7828820 7828841
    0x20f0705010c12020f160f05031602090717061509041415060705030304080304080403020a0b13060905060406030f020c0114010305060106020109020f130908030703020c010506060c0a02010804110d06 87
    0x42e510182180074454070b00071580c101094045640c46c10086413014011760004080540302031540020341300c00a0b02c14801004107003103078072a14104101600420261940103444201402904400345075421078070344040d58007000489001f8a10206c04103010346078814105402d501c2031400c48903c40420000e21303244c1c001c900707216082c050b140e0a4002d0107190b100e90580544260310900010b4001400200115400b510900c00d0358180340e50703640810859407030350704540e001030b602041e282c5042030020214002041e0070304e080d44015181401041d41031040307008000030142c1700d0103070343c83c0e0081a4044a03420740c240c2000b0000d40b50381850400c5242000c1c081103070030340210b0000007010f0b1b20501604900640091072130105850640800407848410041d0710352041d1034000d5680444c190101031403141006440143c5c0d1200186180e908681e401842284601420b02c0264185c440025440c1a03040c2d080c204070302079846604240c0243c1d26030540c1d0b540e200c1044c280305020841190000031191 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 7831320 1250 7830070 7830077
    0x703060203010b0a090801020702060301030b0714070308010e060901050f1908060c070201020f010e030a031d0d03050702010f09110103020703050f0d090b0c0a2106050d0807020306010f0e0109020904020f0705010c 93
    0x255164841031f4241e00c20707940e010350f002100340014004106010407094100c007160402e000e1000e42c0980e0240302e0f0300017060580210740e000004100c610300019480b6404074045810030f20541c100b9000880c0c0529284015010701c03103030006044c0c3c604080744a0000391070f501d001c680861908a40c414035540c45203500320300501031311000e4841100140039042c04030b6803940245040004014040b002440c040740e9440344c0f41c48007580f441a03013000340209420050180e80210705d41c5001400a8295080c443c060b0307007403a14118244001c12003a800d10301c80c465013480c1c05a540c6060b410b00b11241d000c0d041559004e524000b4500c03d8011242e8044a00140b0440544c1e0840da110000340980c2c0c020307501000c011860410895003070540f205062040c024076104c0004406880d100810055070348124120b4142500240f9801980707420407003140102030b80c2d8400407050781841c08203032040300180b00740310314203401188464407543d440c0c06035107002044003481d50b2600101e00f0880d0192880b6244032010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 7832570 1250 7831320 7831337
    0xa11010e060720060304050309240d0507030516050909090106170d020709050906041b08010903180b0301080316031b0506040b010b09030a020d0206070f0804150305040308040f050703060203010b0a 86
    0x41341024800e07203100700e40050283d07080004880a005000200c0342c00005080001e80c0e072226448505009000b008a69002c0042e02d03150021006c2d00311040580b01c0300b0b064600b00038035405260701c9803c8826135602600c809000d0380703401c1121800b40801d60400907000703520045800c825040011074034070101b0300e58215640d0680da062110200c4c2c000f03449480381e5070811f50004000c1444615000703021a500d503041685580d5400309242180c640400840000d089100151030701308100c83c420001d024548801071442d49130410305a41c0c2c2c07040c01d03071030011002011100f4040c903004e08001c10403000c4400082c420820b652500030f03190036007158120340c5400c0c2d12001092000c506003d03600103200c090010b0090103565000c101114546d201c00320b0380304008200481c000f43e4009040ea62083c401c0742603540311810000e10303000d48001c2e04d80c01402c0618040401000c00e900000c004d4100d03400495008800100342449428110141c1002d00010f0002000045000f1808000c0410401c20741d1a030f0b95 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 7833820 1250 7832570 7832633
    0x20f010c090e0610120e0106030201030b0901050d170c0703061e05010308030a090507050a091b030c0804060504020d0b091605030304030803010e07020a0f20010e030a11010e0607 78
    0x80034046402880d152502d1000000c540341009221603070002540d040041c243d01714022100159000c40c1180c50440e5101c800810455030140108002e464003140c11401a41c1800040b0740d9a8890f0780d000760848100d040011360007440d100032164a4552501030350720b030540742e09066003d48401c05203280c0444003609132a0201c0f20328400d03d41601d50200d605855901c4001e02c1c200a4983c4201c1520036000c0c602c00054035649071341c41e0b140104864200030801c00c40c1030000440d007047c442640c1c0141404c1101000940f41c5c0039218a922540c01800003486071214004a0a000c1000000400d01c20f00003050022000d800540d034090300c804804801905a141c00501d40c40380228403000f440270809000602c9240400300100d0703400300071032040701d0251086845040c621030042d030701600c0c6204008050714604402c0325403908000400e080c0181e852a4900c0400e40d580c415001c05000b41c0540d402e81045688500220002402c004210903103235403c0e410031090420741070303840c103d065440c000f0144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 7835070 1250 7833820 7833827
    0xa0507050f10020706030e010b0301060807060206010614070201120603080d0501050a080f03030c0304050f070f060e06090117040302010216050c0307150503011712030703140601051306030207170703020f010c 91
    0x26514802d40d405031407030500e008000c1e030241c80005c0c011080c954881c2c45000d0075031402d2103914001c1c100c12009000891901c0310290404006030020420007400110b01c0150f0b2450f00101c038100c42d420300e8040003d0052084220041009400003003403080001070b120055801e5400042c1038540854120412030f903140c3c281076403960811100c0381c880d0405d00c00a1040d0400750003440c0c1c094002c4040ea000315103140742040c2015042e82201c1d10070920448140b040c0d6902c0724801142c40c00566105140142100c0042d208010b420700d10f680128106000070301b014400c0d0140d03420081038010807401c800040c40d046486561502440d4041e1041c15800210b203042501809401c242c81e45404d0b00e5a424000c044d00010241b22b1140400c1c41400305600741c2c170310310384000e5116581ea680c0008075118155007100544102811013410840140700c0f0340c0d0703410100b601c1f600c2150a41d080040e9259110710304902c2c602c0425040301e0041801040c0c80003450780102e1062a558405002003100c01c0442c43d054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 7836320 1250 7835070 7835089
    0x806060d020406030c020c01180e06040b030102120405010b100806060a030e030c030901140301030b04081308060c0705012004090209040603020316060f030203040b010605030901020c0105040309150504080303150a080a0507050f 99
    0x270300c00007080100101c080c601c1003941c00420160000c9041d00980001c41c0c03c0e40c0c0510f80300c4600c040860200010701c0002c0c850341901c0b0340c3c201e1310075440d6205008001c0030180054003880c85180d00103002005107000354809540c0c070b1450019280c03124030740085c01da140e800158485000c10100c1c11844129000c4600701da050700d0f844070309041a81c845448404040e000717101c4100703100450383c030080b900107810022680715240c0702c2e242a40e590b100e440c0482c00c0d00c582404d1301e46204140c00c200b52101c2900b02c01d84055070301c04540141c48420700c800140c0070745141d510194140c020201017843da0000d90440c1c40c1038820f941c9903d0301a0740011800c80480c40211006031054490700c0044c4210380c8507400035500407030014000750501510040c541d013116401c0d03c0132808510280010400746450031011100075529081080c102450050402d45a02c40148036000042002c3c80c4540c40b036803200008000f40078490101d5036075031154070700b070b0b50340e040280545840b4413102d0141084030314244426 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 7837570 1250 7836320 7836347
    0x40e0f0703060c1106011e0602060603060406050a11030a050901060e011203030f0b1201050402030c04020a1e021509100f0c0c020f060405120703110f0307060806060d020406030c020c01 81
    0x2000d01901e5034071154014010314284008108403140c05802c138080030003465001c0c0208000c0d0b9450000f072012070410142c03081c0c1c41803056400160821510340d4002c515aa842a0030000120b41662502d405000801c141c1c11110106080032050140c514202c0e400765114402c840c0080082d6038946a030022000c40c240b00f40c0601d1703010f0740c00450001c0d219812103105a8211140860510004000105203250500810503113a54440c01c103c1586000c00c443d02035040d040d6000c500d8555040402440c403106c0e80c400f00381c03d58010700c0c40440c032882001a201c37185c80d40d501c0060301e42003090b41c0c29101d07081301100700d0b40304d41443c020000d03c4105104595404040343c5541890708020382c01d0081080c40c150003154080f009002c0043d0544800041c1c119000d94600608070241c19494043c6c0c1c10300cac80c608141d000d100741c9003141c5c885850008440c8144d8807207080944d400d685c1c50000420f2803140071030b0042120300100300050b04a401d508084000206502a5440c80449200450342c94500301075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 7838820 1250 7837570 7837573
    0x91d01060e0610050f040b0304110109060305190209060705031201060807090b0a080a09060e010207061401030f020105070809030313030302060603010e0303070c0606030804031a09030c0703021201020706060b0405040e0f 96
    0x10707207a2501d0061000f0159044005105e41c2095a543c4001c1084d410894055801c05215603050050f5a0b1051b030710405041c80381030400550038090585013461251115800c420b650010304070210380c0d0b801e0143d90b0001d501c03104a0707a507007024501340c40d5140350a108200101c0d0190001c51132050040203030b001564078203c90340d070521030909400c896550b03005e4008982580e80c2c0410340d020414600401c02622044000035950381c18528041003100d511302e0100600004120050001a4110500d120040d4091901c05d45481b0715042412552141461040e0706100002e101010b1030542c500080c00c69002c1d8003601d0490b550801072500343c4800f03601140c039a400400c00900468080c200003144035024000000388961240da5400c1e03d54040e030410340e044411644886414840d105001da8022024005541021801300b5600e07901e1185000003489080030a90642104600f5410786544640000342488100c1d80d913100008280d1040c051a0b010385d042120303090542c000012a140b40300103000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 7840070 1250 7838820 7838839
    0x30203240403050a03091a01180e030a05070503040b04081006050603060f040c020c040908040e0108070305060c030a0b040504030806030c040603050a0b060109030503030703050702070f0602030a0315091d01060e06 93
    0xa9003283c19501000c00075090581d03031811040400c08010040304c80d0b00c1c04051a4010794101488030082800c4501c4048015080c22035040e0072031004000d49240000c1c608001d9240d900d1403030080c1c2507008980244101c1a4007040c001241400040c500c82d150560510400c651516041480b0b4148402c40703600e900504c007000740840900f41940301e104e848903144142e0701c1c210181000a000e1b94441c5809403031a000c0481e05201108240d1207890042c41008000c044492842c2d031200d0302d9001c001e00404c0c000750701000013070940105822511030844010810400da10307242c60040d14840b01130728001c1c000d200f0340703907071b00c241c2d0034148a50400e03030740c100c0002d040345165a6603d00100303000418032410401d03201400800660104003a500806654a000c5180d290040000f40f9081d5140d0204241c400e074200d00700003560300802120b007100394520340410400812075410514191660103082030610302074005081c3c2412404000012960500038440b460f6981c01c0304015010558440f5807200e0281d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 7841320 1250 7840070 7840073
    0x9050109020702060327100501090c020604050d0e031905010c080601091202090a0209040207140613030905040c090b0c070e0c07030503011e0306060e0702061b030109020717040b040302032404 84
    0x1030820040310551b04801c0c51312880143c2c1d001e040410b08054189090f89500040c03001544a01604c2e240c843c441c40245403e18054a80d10b6551051080c40030a004070400e06050701d4809004200c1d1500b08070030201840422403401c00d000346800801c41c0c0004a00001060441d072041c0c040c0c400f1200031221940e8114503075000c00c0700703014014003000d0703d1690070044a01c4070b071150f0001d8185180618524040001c01c51405810000014142d0322200b803403044010010307420010348820794000fa140052540d441400c01c0d03c40703800b0368100504110b40441c1c0d9818510001440a023139600760300045225441d0040215664000d00c480103000c00c1c001c2c80180b04800110b5158404060a45522000156030b502c4103800c4a034a03030407071450440028200f01b0b1a6030100100342e0040f04891795400c0b0000d95141816160006004801c034007074000507402c05000421001e60a0002000481da81c0c8aa542c0f5036039007190322510040f0300900a00607080700210f423100c0c2d40b07800070a014107808120780d5135 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 7842570 1250 7841320 7841341
    0xa110c010504170a02090405060f070201020c10050c070c030602030601090501050702100c0206040b0c0303010608090c0102060105010e040e0f07030210050408070e06040207080307030c0e1002030d0c03020c0313090501090207020603 101
    0x4502d0749094500c1549004c0001d60b8480da41c1c14026405640505030a0500c8004031000d41c0e00285404250380c0104450f1019060001e441d0405d1220880c0001d00d5840b090103901461103540d0f80134080c0022642c02009000131940210f0107070f1000d88a1a060aa0361801900d4034010b000020b07500c240800c0c072100360180200d4070910014801001685016180c0a40c0a1180c200c407071031003d180d1000c4014420700d9044050f40f40c00100300e50081c6a9482d006d40001c2d5241014041c0c2ca04015801110b0400d54a03542c100301c5c01d040740e10055441e010b680a089682d02e504700d11080c0d100e0203054a80b042c0c2580214200e90540d0880300203850158185104100110300240045030020740c00c12010300414841c502442c020542c0c0d54000c60000340101000300260707c5656002d2081201e90310142c00c460300003007140d101340d051b1031010882c61422503043c2d00a0048903c152018000000c0c142201518441a1016a000ea00d0104902c0c0d80760540c00c2e04078017503450000c4d0040ca0420114400695 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 7843820 1250 7842570 7842599
    0xf06100c020904110a030f050304030303060501030204080307020f01050c031b0d0801030507270504060506090a0c05040e06130c020607110303010501050405120c030d120506040903020a0807060e0703080a110c010504 94
    0x5014107070505c0941c4ea0790301c0306054105204165429000410207000301070f03160160030010202460154203160820010548434482c08200038443c05940d00065050303400343c4162402e408650b02030700e0700c62403d60440381e21015040d000d511503015400800401c10700402e902030684e81c000c0024114282040380060f59200e5140b60840b1100703440042404c598501d00a59106034440c000c0407882e41001020b1140149020f40390000f618241110210110b50210035039080b510341000a04064490724081120003003410300100200e0b0506480210b10340c0c000414500404841e41c500080403d110801910ba020a000700d1b40010300400c0200110314000c0114100d5900000c143c034030480284000900e800e04810070700000c2488101c103a60024401d11400381d03c8507054a0510540d4481e9070001d4403807901c0c00004060f1440815910140a4140c0c04400040c106100701c580082e200c1c1004036561308420840c01c0090a8100504290440416803818007003041c1c4801e0301b01410f100e42c0011442 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 7845070 1250 7843820 7843853
    0x6090705030714040b0d0c020c01030912050901090801050403030e10050106020a030807030e0d02010c0f081b070503070b0403021005060d0b0402060307021207080706060501080f060603070e090f06100c020904 91
    0x9000d201c04103801d05e0703007001003d00f024030041c00144540101c401a08160950801030b0616140c4100341c00401d40c5ca10152440c1003d62038125a1000303000c005aa618509030002c456a40c6058208420907416500103c200115101140c00d201860a49003081c1c0d2000d00070f580050f0450011600020f0248940541000090401090080304800f036240313400c002d4030724280180e4581c2a01e0316020b07088019800160400e2030300700c149182071404000c0c1b02c00308a000e800652070001c0c0079003c2c0041402620095035000c440708001d8189410000d40d030b00320f0719036551809840c0070082299417030b00394014101075a03c4030101d0300c0c9075202e408004158000034108015401030302140070b09c0f40741e00001451074a1040c540c05858480c00d080c0070040321030036080281400460410f010312003040c05030f080d0380011300321286070f903c2d038a481c812100d8000306441140c0082054040c095080f44084a1a200d40c20943e0340d101705000d0640115000040400e02030b410062060118021032001c00001c01c4c0300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 7846320 1250 7845070 7845107
    0x31707030e0d03020105060a0605040e06150702121f05070e010809070519030b07020106080a060b040906020a0309060c02010b060d0f0e06070c0501060503010203060a0608040c050910030b060907050307 88
    0x20300c404086040702c0004101140141d40d100e0800205250a0428001521840c80c100c0c2c01c00d800d007440702d038107141d001c0c00d99803155a2000c40654401d43e601c04840c4034a5002d0b00101110400100040c1d403458050700040313034191505620104088144680b41c4140c201c5d07a00c0348200d01c4441c0054581c9040902000d64500035910086920340700c80095409800b05000c0c00b000d00c1e1b146080071602144041c1940c011a410080c0c07c100311040040d80c0010030342c100000017140a40000090000c0440303003001004940082072000d15282c040d4042c0b01700a0090405218061005000320700b220240a0f00300e620031400c0c0844014a59a82c0c4495407000d05078074001042404002e00c1c519000086443c8400200c00c2000c0707108204083c0030741c400400c41078000754114101400002c2c441c030183d0190030108210b4030001400d22211040010082c18080c217200710f00d060480d8241e8002c1c402d40810345580d41c02401080042c203080d845c56125030345554540f0b00303645a6180881d01e01a8281c65603021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 7847570 1250 7846320 7846337
    0x301030b0709170706020105060301050106020604080f0403060c03020306040b010903021e0a0306020d0b0310060302090414010b0901030606080d0806060405060304020109170106060906021c080601020109050a050a06060f03170703 100
    0x45a000c01844940000f50400424100e0300e841002425180c000700541c1c007990409004001d03683c0c0000d8000e801c0303588a40d01070f8a81001c0b0304c40034040e00981c0e1018101d6800c0a441d034003115015402103000300c000740d8040c02000204c00064a03010010321009400c4015801d205240c4200b0780d40c03800500900405d9940304030780d662541c07000e90300f00c052034003034940c0d403042030801500d41000400c1c0e41d50302800303050000a02d1a0001250703003200500141048144141e51030544000794400040d4020040c0707030102c503584905005001348074500a50300684581d428102c00c0e0380c00740e64264410040104094a424242000d0082030342028004905000402001140080c030071008229002410b01c00004e6052814100414000305a4005000c2d9000500c28100141c82c64410441c0381c41541000403c035101d110040b0f00410006502400e140036540c3c1c3d41041040104c0d01800482c0038070402d0104540b90442c004002d1801d00c40180b10801100b41c075000c44600e400503080140c02805c040301c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 7848820 1250 7847570 7847579
    0x30a061802040504060503070f0b0906040e100521060105060a09050907170c16020409020109150206010801060806010810090f06021207090e0c0909040503070c170705060f0301030b0709 81
    0xc00c5030302040550036402103014000d900300b501c2034800608007200182412031074990703200c800241500403034001c0e500016800d11140c43d23290894009111640d900007082c03800710300e80601d100300c41c0101c2c0c7c03190761003d00d1440c8085103180070300503042908000c1d110a900e40000c000d299031103002442c0a1180000002a02c0d54641002510400b487d072030341090a0400c1d11480d101c0300c030060104041100910003411a44d01100450b0300c400d46c16180003c8101d0240016100446039510907070031061b404014088403071740811414100c40c803103002440801d0312132031450b484032002d00410603944d1020f90004520b441c03a4201191242c01603c08400c40502d84e1140416a4405c0d0008680c490810302413183c0030b0307031200540c0000e01084015010314200350111000c00d22a0f0041103204154500c0410144001131003101c83c6280e10a035000215550f40c85405a003900071400d90400b130084c20740000e95810960300719620080440d0b5494907581c00c5540c2c409004401030301690400c10503880105 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 7850070 1250 7848820 7848839
    0x906040e030c03030411040c0903061a10050a02010e011a240403030e0f0904021507050f1009020109060206131202030705100f18050c0d0f06020a030c0801080a0c0506030a06 76
    0xc008030b001019680c2e0386014140542001950000c072402903103008612031080390300204800c16203910120100c1e5910710401d06550340e507440442507030320410b92464224039540140003001d595010381c00900002c0c008180040c05c8980b030039900c400040c13164662072101e04d03200d4524256031455403100c4c4540e10648055540ea40c0254108502103100b031195080300c0d1800c0c0a5000c00343e103007210a01c03401d02c2c080c1d022034000040d44840c1d4030083d03070100f84442040828880b0381943c0703800380c0444003074410300c0414001034490440705a000c1003a98001080c010700c0440d0262081521451032048110b07607980c0d61002c1d003107540700102140424008000041c06c18004002e881c800c1c808040b07103400c4503d01003002c9440c001d8888060903c4400301d18001100401d100d00086000c5900ca02203140c1d6003840381081c5090b0100800d21072000a02c03862294165100b502141c0060751180b9031a07884d400d4450b039a0031451b101429010001104010a103003a400440d449615014080341da156601100c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 7851320 1250 7850070 7850077
    0x3020a050d0c0801060303080403110d0f0311070b040602120903030c03070c060605060706050a06051915090b030f0103050d0c05031602010e0a080601080606040212070c08120106030b03011103070e0906040e03 91
    0x101d00148d0140b003440245580300341d17600d0360500d4110160050030701c074560140503900c0c000403250500d6280c2c1c80300b02d504d9514006540580d81c00c801030103403501d4946800802580281107400e42601600c0c0843c9031a840002942d104410764505103145866440e0180c1e04081c0c0d44c1d400300c500300c0e1646808035490700c0e40d101405946201703030b502003858188047e000081d03400f20340105005810582d0001452020108500110342258200010500c0c007050f003100d51200ca078024841041000007400003018101920904a034001c1081c0d5001d41a640c0023158124a0300c5005449580305001c5070555210004586c036003148141031110340580100c0204182e03111070780c44407429401c034500410902d54240f005550004003103c3c110b00e000748101131425801d00c0a130000d410000c101d9402c1c0102b10b1250103d6940c1150505060300640c0d6a2000502030440d02000c18081d5003085003200f100310419040e00d0007843c054803900b41c01d18440c001d208480400605c415445034031b80c410080002000c0c0000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 7852570 1250 7851320 7851323
    0x90a02060a030905010e0c0f010c06180c0f0501020706050304060b01030e06090c030f030a0203030712060503030d020702100804120c150510030201080c0703020705040504050a1403040f0902030103020a050d0c08010603 95
    0x42000e07482801c2039804c4420f20b078a41d1046807c503598030a11580e5403000e0306280002401e0401ca010010704000000780b031130072504000403207682c000f10140018103000c4011034054140c601da1040c0c40707500483e1520103d02c600c0000c0ac03c18004500010502d41080b440c070081031400083e0000701202d6039240031320030368241d40c06070000040402c003800c0921000e4090368001008510304909c20000039640d100080c000c00800c400298440807800e5190440c500400c4000c0071603480740900a8880020760181d00120301c0b407811440a4002c081c01141414030664018095540b040310700601a2440702d00c2d4032040b03401080180d11104103555521030705025148146510760200d0a61001503e0b00e90003800c00f4107030000c01e1021a001a0740042c1d4017069070026a00854641c03654905030f880d000700c2e504020b09a01000040740d9950800002070070481d101c0c030210f0031800355a00701445c100e100030300000e50080025002441b990074140c20680e01075200c1d50031600615603902d641030031944140c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 7853820 1250 7852570 7852577
    0x1031107150e0f070308070201080720010c090504051306020313080f03010302030d0c151104080105090c030d0905090a05060a1703030103021003020301080d21110d0c0302031905090a02060a 83
    0x118842c0b441080654001c04140009042d80c900f180c4400c0c2a600840100904001482001451440c07246420310450b40c005d1044103400c900c3c03800100d010302a02c101c501c3c0090001f14002a00345880d0140c14011041c0c1c020003982d08040b919600080c0d031004041d6007483c03405280160000b0841401403050000060901c3e031603504610406060024102c20b18003003040d0f020b4414041002180b00000f04840520700003041807203016906602d00441e88a80c00a51030f010070045402c40c0400e24004914048050360185800b10006031000052400385039041070f004130000d0305126440d07116542003000140b05400403075495850700038401c4003620001d030a40010004004608002007007001804030360500303500f550304082403180e07101015070404080004084c0e45030586418044081d102c000600c0f010700c65513130f03004103403681540413281007c6000d10345001d84407624800c5c400d40b401803042c0b00134500e035a01c440700c01e034010f05000340005d5420b00a07402c00c00010f80c0c40c00010302a042c201c3c0c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 7855070 1250 7853820 7853831
    0x10204090e0c090c07021c03050702040605060a0c06021b0703080c01050705030105060306010305040f080409060303020c0301090b01150215010e0708060a05090a020f0415020303040c060509010e0103110715 90
    0x401030688003812a01c000350b81c8652103110095a801600c0c5912082c0e410f03071641c071000c160000402000e80e40c040d45405040450401080c50781c42401001210f00a0340c0c1442241c0d6a041442103a1003980744650000f41800305070030001d411074004140c1904042003101d51015001801c0e0704104e090b501c1110f05010024459666000a00825601c21a1420110f003117624050104a42d4440144500d041590b160300190802002800b48142650840d81494803180c81c0c1e000301e0001d000070701041d4054032802010b00240d180502038217604e998031204545490b403800d8110381c008818a0000b10547c000d40d006900070b85801e5010354020404c0711500d10142c2410030010b0b06014019200a0040580000910907905c400d01042e402812440d4010380d03a2300c13409c0c105545806250484469007038003101c86941c4940c00400745020314001c0094414540d920341080d500c901c54410b09a02045104800d40802d46c0a47c0c05030680080c00301c5403915240c000d94580c0c0c469040c104050100700d6a44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 7856320 1250 7855070 7855079
    0xc02010624080907050604090903020312240f03070e13150c080a0b03071a0f12010303020c010807020a0206030406020c030a0f020708030a020a02090c040503060a020c0105060d031b1b030302010204 86
    0x5140c2c40e400000507000740200e6414280411000c3c4910f000d400d101c1b40e11004070f0402c2610800486414041051003000b9600b071010080e565031300303402c103031804030300d0914040b03901854032540c0248003076001030041030014070702802d21203610001042581c0d04503059003010003140291303407000344074030349000001219180008054800c41c005030800c4031451134480041507903100083c2120641e014000d00310041d5030400c1140c0328074401d42c1c0d0150703886e1360045000e140d11032848140c039040e0781c82602510094141000110381c0c1d0282222102e0050340482c1448001d03003000401190070074002c100251802c204031021500e540e1140c006500017a4002c6508200c0701d90500209020700035503c0514640100744034002d55404031104064412400100800d8400742c0d2042260010314000c1d041d070350145003c0c04200c000703400160081c1c24950801300051450b2a2002d00f51b020035526450b8203016090184627040c591032146821180d88172031409141e08500b42c2142f0340c0003103129a0015a07a01e041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 7857570 1250 7856320 7856327
    0x1020904050106080402030a0b0a0219020102040801060b0c0604030503040f0b15030d0f0e0402180405100303090905010b030708040c08011508010e0d0c1e06020424020a080a030c02010624 82
    0x16405070003001301c94000c4c07000681c0c01044418440780c0103401d0304215241c2c2d1510100134800c214403042048035060802c802180c041d00036008072400c01000304821a50f81e11800940e2085920409a5400500000340000d000f40080c6401501031035180e01881c0c0e041d52800c1183c1410755401c03040003403007003850039949010402d04501071010b181030070314801e00c60001340010154200b0180305903008600d005030035640202c04022004010010300140c242a51045420030b114002070b4002585100b0114030380d61240281412200c0c280c000b01c0c55552600c0c0c0032941100007400031101ca0004a00016414009002e10f90054192507546021030380b80c10f000a01b11040340b0810783e295002101e20714111604410159140c035003000100410302a510042c0c0808081403000500191000c6001300d0862040200120111400e8141802d0b5a040c0102640e40318501e885c01003440b0b20821003001d98501c41c2c2c02140d200d001500000c210300d034440d441d41103e990305045104560718011030062a4560 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 7858820 1250 7857570 7857581
    0x3060906010c05061314031206130204030201080601051b0109050601061b0c05010e012307060f1406010e0307030c0b0304020307050d03020d200f0a02091609050d05010b030f01020904 80
    0xd003003042801c02c540d030b5103039241c00c0020300f40802e12264002040134046c0200382a5445a80c10069070303a01c4500080602c41284144c803294052040401200107140f03080c401c440a880c0c0586501813141d83c4c00c8011030f001d81c0050384011245100c008015006071013402030321045446000640a0382d810520b0041036501d440881005a41d21003070f41030081484061083e094650a2a00034108064180140c034035221084110070111101121001c4010104000d840380301e2007044240020440c03004a04d090f22000c183d20881300b41d00c000811481d60091009208406000c0c00f603589890b900e48800c48013040d40c0d4401071010324000204011490b082c861100500412104600001d2260710001d607241c90680d042014020000c2120010070703813003a110b034013600030b020841e04448811013560351246594041240188007090100e50b1480030f00c2c4c0700c012840040d59031400007070729150800116080444081d500703075503640c0c4400d01d02d0300c06129082076400b041c400035a80d00c83c100c050008890 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 7860070 1250 7858820 7858831
    0x20c0f0c010e0f0901090b041d160906140405060102120703091d010803070605040c0909210305061c0206040302090720060f0a05060109050a09060305060108030a02030403080a030209040203010b030609 88
    0x1004003008566a900e90813107a0542c0c4000200080303403039490011134014410080c1121034194003140022504100080c4038600e0034000b08102c2e0000d54500d4038006542c0d05000300842010a25a900302c2418503070311145e48801c051040700c0261200d00035010541c1d006410076400601084018084441102c8444070040c2c1c0d1001d41889c198905050340b510f9018081c0b00501154a5401184c148190107c5c1d0b800070b881190400c1000c0745003480c0042d8090605c550441e00d2824901e00565528003900c6924030448014060400882410804801e0b110b0403130390899101307105010110140e01c0301880980706e00425201c0c3e40d841c001c004130a0414510820307854055611074020050801140d4401a8001404031030104070781c1c031b50300c0050310220426001960401c80d90f10300041c03100504e030401002c882c011010790312140d0725450940d440b03126030040c060141c1d00800c001c000282e0400d009005e0029149401424154450001010b0b40d0007a0300142c1600c5000c0284202850210b0440390408c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 7861320 1250 7860070 7860079
    0x10c0206060a050a18060308030a0b03060703050105031b0102010212010b031801050408070b0603010b04050705030a0606080108070e07120903020a20010806100306090504050303040c05030f060c030604020c0f0c010e 94
    0x6440d003c0050300c01513407030003020f02181c01d4601c0e51442d103a550300400042c641c000c82d0262289440c016403001400d509408902c00e1041402086120340648035103810707110050301900c0b01d2145110010241c00300200c0550456500b01322030903c44405807665030207860303070b104900c1c1e5a040140da0b0212008411030408001d92400040c880040d509008031000c064ac030101910483e581c00001078010240d00307010315046824142040a4580d0002c0154812803070514108001a1581c204491020090245456640c040c010500c8048810418035901c509036140c10396560304ca8a40c00cc6c283d40c01000d0490141e403080a410003003015542406c20311960002c001050203081c03000003000c0780c4002e0400f500800a11b40700580c018402d42000c000340c03c95403401d00040c103161400c90b0b0b0725882140d040c1c4416202c000c0c04281807601184662000c510303034000300361030344801c00490ba1941c8090191903005a080103031200150040c0035182d44000700340090003502220f1400074001c2c01450b03c0340b334440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 7862570 1250 7861320 7861339
    0x6130e010f06090b090904110d06060303140702010909090807050d020a021e0105030a0c02010b03030f03060f0603090d0516020a030602070302010c050a05160206160b04030f0e0a030224030108010c020606 89
    0x244c03d031000d40e41914001c03111003449459504100c8000408494141c0d00000103140c032100740300441d008507044910a903600c02c0015045880801680103601c03000b03001a10703100e402c000469107600b00f9080c1c0e5004107000e03840c29038140e884600d007000003840c010160704100005410740ca01090941000000c0003031060139403501d900000c1140c840100b0709203401c1d82d213034926903140380b00f5440a401a84040e00301c90f076070300c0340443c903280503082111842d10426510a49c4030b01c0341001001c0c0c90003042030300018500701d000414140e503903800801c008412000e9956002c0003698400c030710000154051440103030703a154941802800d44001440340020300508025401c1225071020460301c2c7c02a0340762004d1040700b080d100040d124420303541c407216801c107440180e00034800708a40032402180b194031007800d028010131041e0340024511043c140d10000241080025052404166150201d40c803004604c0d407602d101c0101040d0000e170000c0f0750a030f541d140c1c040c80d100d070100962034210300c084070034120 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 7863820 1250 7862570 7862579
    0xf09020904120201060801060f0302040e01020903060408070602070606060f0e030d0206070c0311010203040c0501020d081909080d11040603060506030903030412020708030a020a060609021e030606130e010f0609 92
    0x1036a00050401403280b2411032800e081c0520070341c806405045c209009002c01651034112038007001c00d03800240d22540c544440078004034014401c2b00c01215020380a818a41c0d51621044e001717801c04482514000d4007001000002440c910998004d419543c40e41500c030502034a0041a42d500181440c1c000ea02c617000c050714807900025450340c41000c51900713400004841c58202c4c0d551100c0b5036215000d40c008800d100030009529051400d440c0c00381c1c03c95102183c41802182e41c1c0c0015124900c1c04c00350440c1d043c2000310150800302459000300d4000d0324201143e440e09007145c4070041241751a000210302408180e5160040c070f00180000c0720000d0450400c4a015512444080c2c0000c04200420060b00b40d070a0090200c6001016641c0c10340c1d8075004030a0000c0d484a0884e00202c0e1040c0c07811002003104100c83c4242c0e02a940c10481c511038005034014601040d03030001e0304150740401d0500a20005801000c4800c0182a004000c50042d5140110122030b99205400800901803010350030320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 7865070 1250 7863820 7863829
    0x22b060e0a0e0c060c0304091103010512120f070201030605061c0506010c1106031008240c030c07030804030306090f0f05070c030215070e04020a0201020c0c0102030a0203040b0d0b0405190f0902 85
    0x30750340401200c580d90340d02007034020985140b01d107070720a00c903403030030b00300801c9c06540c1b000d0286048400503101c2250488254070301e541c50b07a5081c090248800002d0261030300e040089005041190b01c18140006c110b51110009007564100d140f43d076100c40c000610050401150303008040d000307502030030300304060380669039001c031640900034105004000200000351921454040c00700207059041c240c40402500389088040f190f041a1681c03481c0d00d1600204604400440c1280d10440880f030701d80d4245010703540e0854442101800503030402d600d0350004201c084841c810a4200420380100140075410340c01c8007016242d00030a01c1061119002602c40440d4021554102c0b41205d451f40c0000d5542d4440190f4100d070050b12030681103440403654507006501580107111540c1e0380c4040302c1d1051100e030012a50b91061224200c016041480208a80c000da1005084c0d012405580483c8118044001c02d080328411640e9481c0072186c80844000d2140c68400e00d69501d03102d981c1401609407076004038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 7866320 1250 7865070 7865083
    0xc1401090b0906070204060611010605010806060a0503070909020406110c0d021818010c0908010b150a0f030b03031602090c040807030b040519050d020d08040b060103022b060e0a0e 79
    0x380001c900261101c800e6032a02c0072582c80940c014010002652120001400107450f0180240c40f50710308007011880d580201e4006101d64002000c01c0c0c0380054000302210150405400c20080c05171050003c07615000c02c0c00604058600756540070340d03031441c15941914100c0420403480c080c4a80340b05100140e120203030454100464100d42d406035403507102c005094915841880c1105500c0d01c81d100001030351048000003140ca001c07000f0702260080000f0040c05120300d840c00418a1020800700c0300c103a02442c0314200d0785075a070a00251061034030021a003554070103aa410326907000fe128090031480e0800801d030700700c0070361022542003504104100390781d80058040601941d000c0300001e8100441040303034019150300b0209840c61890341d85003007980e030286810740078054081c414100740c1c0e240c4a51400c603c910307040711f603640907910344100640c000e5001c00d03da50a8100c5804100369001004403030000d000e1340341540014424a0501e890a82400250880341e0450902c0b8100400c041c000456 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 7867570 1250 7866320 7866329
    0x303060a0609180c020f0a0c0e0f090c0405070c02090a0903110f190f1401060e010503030c03040909110d080307080a09020906040b01030605030708030d14060108010b070302070315090c140109 84
    0x840d44e050034000e0f0300d070648400100ca40791190201c2e030800c00066550310011100c0c046020301d0643c8038080d04001100c4221034444460384110110301c841e28190b0405900b2034054205a607450520707030042903072008101c1c0d140b503555403512807450801d5440404c000303041401d0b0000d003000306000d45109840d0035030008640c42006092040c8000d000803d054510740c80e034000e055041a0520350407643c013078881842030358440030f035810001425080200071100d80c0404480030354601030a0030308640c000d141158007501d0041c2c0c1001d86171492307184d00c011903240500820419840b8a024a4014055400200440350031400d080103c801a2210b103985604042c04445c049114808200120b00900d45035000302c0d410301c40d0450005a0140120041090481ea000140060051110800320000b0700342d46075400140c1d87c0c80100302510403400541005440f80c41601c84403984c1c0c0c0c40f21080607281c00510303070842c1d944d05411000c100c00700c3c500100500ca402044150314004c1ca002800507844c0b80704 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 7868820 1250 7867570 7867619
    0x12050d17010e040606050a06030b03010b01050f070204020c01020c010507080906070c02010503041509020307171e0705091308030a0605030d02010c0e060703120504060203061507050a02151b0303060a0609 89
    0x418100308139600711402812000c0c0c4802d80055a40310010003038100164014000e5180c9654540c00394802c03c00c5500110b541d017800303464140c1c9a424000294004c803180d0031155424040d003019800c0c01c0c0162406103019507240021800d107201441d00340310f030252424051141da0b024410060740c000d802d481e40309800c0030000d0782444d052244400680f41c81c0310700035454020100049655120103101204e03040880086a41510800240003034a10b20220911010750080000308407078540f0120040d404130320240f403801c101c20659070307130301080d001a42d00c60400c1ba19050144085d090801840e00c02c42d0061000344100c901214019043c080c400c0c42c2c5c280601d03400119a01030500881c0340e64400b20345290304010900e02403d21030001d42041e07079400e10586090200c5d600041010055070740f0f60307811202400c0e0086644e4208000d2900f02155010300750418001d181c41e040c41d40b030700a83c1d244035074405590f5a14062007000142101034104405010515206009514914400a141580046 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 7870070 1250 7868820 7868849
    0x50d0503011503051f0303210504020a050405280605010305060904020d02090c0f0708030a0e030a080705030a0905100608121806030601030905030a03020d0c080705070605040c0f12050d1701 83
    0x25141040145c198011070007202d1080010405171300040b0360010f82c1c0c00000001c140d034848040315007a42d4050f94040c1d8002c900352010302407841d2980c08540c0001040402801d001850900f2280640003a85101923407640c0b0402001075581600600307900000c00c80e4951118a0568001019818103d0002c0d0048884000103130607003000400b100c55100380c01d40314980301d201e50302d8883c0c1c10b640202c40700e0703220a040500810081d58000152541e00b41c0316225001c0c55a94148100da42e500001c0c0f00300405500e448000d000310310207000410301010181b00202d1418284040c00c1d280200e140d02c0b1405030181000f860325a41d0810b140c1400d1044215180d5580303448220040340509800a0040c01c00e000024858414170780640c02401d00c5003591600784890035004c001500c0b0004100d4410001ca2810070003040024056448564014800c80904500d181c03100300002c05028181c0105d142807040d0a10001440706c204000f10400b11603150600a03910002107901c0c10660622a612a221103027 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 7871320 1250 7870070 7870081
    0x909020112050606090301020d05040c06020303040c090e100207050c2407030e030309061603270902090109090203090709060e06010c020d03030b030a08030105040c02011103130311010501090207050d050301150305 93
    0x13508603401030710020000d64480c960509664000c100a6504580589981000048460000c41580d20944d045885101c0f01c601d0b2521001c081d1000450000b441d025840c8081000f403110f1025046050082c00100303112905282804104000f206661102e417261400e61031446c1c404104491640d54540303461410303001d80e03074080381c80c0d4002c01c066150b1142c404110a00c800c0c2c0801e01c2007821900954408031140400940080350461001d40070b44132031741d81642800300c09035a070020040c1c00018544003c0c0641d5400500e4126041030390440d0007a00300312801c01c1004550b0261002a020312450600c03241002400030303055642c40500240662840c0043d5401d160007540000c1c04c0840c0917060b203104240510b0130341010350090058510a07480c0010000301c2510502c030380d0303040c0a0800d81c0b5a03d19150f400c0c42200803d03c2034002c80801665080d0118051403e000f5140204003c90025803104550302d8580d0506580d1000c50007000310a00041140000050304888040b1071420000380d141c440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 7872570 1250 7871320 7871329
    0x5040e0309090a2702010c0b0c07060603050f070f08030d051009020406022b0206040803090703080c0307050d050304030806040203060406030602120a0c030b01020601031b080a03020c030709090201120506 89
    0x719810725034442115030812002403010f800144c00c11382914140001c410340e00380901801080d5010181c0050200c1039071b540080d044003030113500045076109043c14410a56500f00682d140d030340040701c00b904003c0400547c00e5040140030060094944000f9140c0e04181000c3c1e92030003600c2e0b1003900300ba2aa00410446280e989881002e000309220035990b4548500c2e001e59030f10003441c0044052480031100d4442d00d120010186e241d114540e000e0030042c0c54585030042d2941000d8881c4105018603800040014081c100411203808001c010710348664040c2015410003145104080601804004102c0041d91208903182d1002e0200c4006890381c5401c1c01190040549410050070284001164504444215011441864250030901400d4200d140480c141d800c4c0076881409039001500500010301c10960380c10000b40f40700080b02240e9568a03215240c080d14510550160700070100c4e10071103003000e0090101418100d001802041e56650008044101c4640d6001c2e101d40d035200803458544d107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 7873820 1250 7872570 7872577
    0xd0b04090c060e0102070b09130509010e070807030b0901020c0304060302070602040506040605030f0a06050319050f0d0507140c01120209041b05040512060103170703020f030d1a0103050405030405040e03 89
    0x422030801c0c1c1d40181c4605015114400008199003d845142d0002500c010f869040740d03001c56010703200010000300c031300c1220041c100184c900d85281d521810f40d08140c001c01c01480004150410041c842640340d41880180c0074006081c00380c4507401040013030003181d0b00100300c608403500e9150051755464641441d6000b401580c01089e44400002030010300141c1c80000765024202540d44111a41c8400502c0c0381201e03218810b00d509904410000117450300b0614644880c43e0095058400c09000300d200365040603451403800020450108126040c000c07603806090145020078000d2a50450b4180041c100001c1607042c4400d40d0b400180c94030040c1c5650b00070b01014880304c0030080c4468480754000d081901304e401494001d5901d443c10f224185000120705040700e1b00844550210740c40c00415048940c0010019800d612501c0252403c490041000740b101c06020500010941c020b0040d400083c81501c1ca21410581030905009c0440c05c08811642154807c8030001a600303c0403811500b9400f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 7875070 1250 7873820 7873823
    0x3030301060807020f010b0a05150d05010b041508040203210c0d0504090f180305090612040501020304030e040b01020607120e0601090903080601080103080301050906010504030b10030b070c05030d0b0409 89
    0x20000140440d0002c4515000341500c1d003c1c0c42c940880c00c881c040c200c80b14480050b91200030f04600f00a541070074040f00c4450f20070b106513145003000c1c585c0c800c8242d850030f0348842d5800c00005020001145010007013601c161085c41c00c82c0d19401e09800190340c940c02c5504003080d0307420103180c4001c0300d2103040889955a108030145c1d1426004040d000d08a03411601c95558040d0400c52950703d4400907106401c0d80400140c0001c110480d0758804860a030000d42d0320582004003001024000c065040c0d540e0300c164401d20025a07286002d1800a00040601010314000c0b8140241d1104507030b000b2402a03880905458038014101e20300d01c00c100900302201d28480e1900407000081680c5d00d20313400c10707403865000b907d60300c201d40c40e14001154202003d120107480b1007802d10040c4414584038554030380140c014501941040d440f03496200410b030b07041e01c058041102c204410010401c1042d0499802141820204c241c84010340714540c0328070500a03c1c0c11800d554030200d15a039030341d03035201e1500719 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 7876320 1250 7875070 7875073
    0x7020414090607050a051e0c0604060b130c020a0605150414010e070e01021b060706020f03040b06040e0a062a08010e01050406060e010305070903061b11030306030d180503 75
    0x3039908110005481815a400d100ea03000d04000120f00e54082c80c100c482d215202e0395000d207032249001901d0841c201460344900e1541e0100050107412008000031030080b4094100095038440d060704000400000c6100c4c4079505041030340d40600700d500411700c80440c80c2c000c0800300b225a509031400079000c00b50700d600ac1d403140c0380c140108180040980d08a050358404040078501ba1582c0005031703010107020110a005070f000003525030340c0b0859003a520048150140c00c082c01c2c80495614041a42c0003c640c101c240e02e4003004210a221110812076007000782924108901c42100c542e081e1150340841018106507146c0c41c407030100b00c1440815440400e5284070030b001c400707000c01000b40400c0c401e12862005a60010000c901d524203442920100c0d5169260702858000c8200158040c040041503001803105c0300030004040b038020301881001740000c201c0b0781e450806009010b8944890858040c4540e0720500400005460024800014400600f418000414a1401d12811107001d07008550076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 7877570 1250 7876320 7876331
    0xf0301020d1a091b0f0408030409090203102c0309060406020c090109050702031902030910050a180b04030b060a080a030513080a120e06130e04050606060708040302010e010302070204 80
    0x1240c010b41c01401d00b110400d0020780044010020804181000e68450440240f00024840c8001000c0024002000070054480c1003a0351601c9060458009a02c0100301503203401d044401c40c9001d00c00403030404034994080080c1700e555660b1f5561544050400040780f02400c90001901c0c504100f541d80c0075900a0040703a680342c4802c0001d4075915842296409072081900101702071b01c0c00e00074280301e0b410f9540298200711440e4421659902e44001040640c0010040c4000c10345400c1038035400c40d07590361034031552900a0100202030b0100300380e94a210700c400300024000081c0b0542110100ca40229080b603154917868005102240103501c00d8045104859500081623000b001030001d03040c0840940300140c0e503900f105626502c850324010041e0340e1024002612a015050400d55000003802130341c02c0000801700e41d00c011000d50004000c0050b01e2013008200142009501ea02c07070800d0752500c0c14262555200d004a00403030000034140300015008141c0d03640310b6410380c2d4400740c004105004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 7878820 1250 7877570 7877587
    0x306090706030e150402060a0c0203010e150108010c080a020d0b060301030b040c06030207020102060609070306051008090c150d0c02030702040207060507090803160609020a05030303070207060201050a09030504140f030102 97
    0x35904003600c034840110341004841c00420b1008202c03240301c2504140c00100356525642009402ea10201d00041032203038001c0600050f0700d01b48640043d882a5500a110822028000c00306c0309105900c6030300c00c1c6e0b04001401b2040e0390700c4031000e50008880030f405030302c4080c401d900030003138003020312801c0d04181c0c00f000000502c40124000b0f4043c41c040c101c0800c045860b444110141d11480340013038056480f040c04150725040c0000758541c46191071030001030a907101c00c0016410b4050104ca20000303640d91080c8042000d080c420907809190844110190540b88500e424440c01110b02103800266600c0c071080e03000c3c1c004d00480313801c2076000b881190ba800c042d261000003030209a40281c00a441c40c040440c036100000110380a0145010340c200688465a507000c0c050424100100d8125042c10707400295901c040000c0c5000b6502070f0054015281402c1d802400c41d01c1c010600d00304103007400c0001011035080700c1268190390340d1b00341161108104d8004105030341407004443d0741641c030006030480c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 7880070 1250 7878820 7878823
    0x10905010c050a05011815020301050a180f020d0b01020115080d050304030216150e0a050109090207050102040504020705030a02060907050d08030702190305090a090603050316020d06050f10050603070f030c050405030609 96
    0xc0c6c8510620107e104031501201c944128002405466082040c1282c1840911601c941c41c0758130f1003610704045807004100380c0c0b520503600b20a10342c1c2d22054440500580719030f02800740d03003200d048110300c241c601403504134200d03521040c90300142c06024002000c1407d16200780071401411041c01103001c1030607651030300300f070000c808500b42500040d141440c03d002e618111281c5400c890059441c2d101d43e03030909d10f06034000e40c0220000c0390190341c200000183c0e9201c600141403040d00404c0915219003e00d08083e041400007010381c50540c120032001d011030341c0c1d0381400a00c1070344c201c0c1030607442c1e50f01c8000a034988500000343d613101c0d88080c3c4600007010750000c010500399a05960b110071041da00c10002c002d40e0058040142541c00038046c00c01c040464262003040d1340e0006001007803454094988108545091721103080d00300015007001403011082c240500240020313203000b841c6141524000b130030b5886101c040c20400d920785044060603403003501502c0103020000c2c140d0360a8249190202d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 7881320 1250 7880070 7880111
    0x23912030103030f030509060601030e0304030506130c050102070e04110a0b13030606050303040b0f030403030902060c0a0b060907230408011e0b0103020c0a030e04020d020d02070302010506030309010905010c050a0501 95
    0x203c0c009585584a07900c058805d00410780240d0000004040d80c2d01c5820040d006002c20301c81c041c0d000e2005010001c0802c4003000300c1c6008105600c4592034200842c20301c02c10b1600243c105e20705542c84068200000e00035128996405504034005070f020502700c800181592010f944501d059103408100c08140c5410060907a0440f80b051808000c132a41e030310203047d101e00072031107101e0002006110b0300507030000100055611078464036000031041c2c2c480d8001109508142c0c10101240d01440f140002c000c402d69080d60441000c07902e01000b8644103800070110b10b00c0c00924001c405942d000c04404140001c15140607000400c02441803881d10044d015180507200426810380b030604140d07192a50082c030031640c1c401003402c0070384035801c0f064a05540412100d0074407600302d82c1c01c1003203803040c462a10292004071b0100c0303809a41c5109500f8028250340c03000d40150b00ca82c100300103c00190383c101000744100c0d0000e007881001c1c1c00f243d0a0190600f0140b16000d007065081201d00940f424043e140c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 7882570 1250 7881320 7881323
    0x611030703020d15140909010e1c030e0c06040b0703020c040c020102180906011707050702030a0303050114010305060f1507060c0c0203060a06150e030c0301061503060504023912030103 81
    0x200840d1125503130610105500b44283c4e001d0100c910320030032840c00c200441c10f0b0b000d440880041a0080c0042c10186400507980f007003541d44100a0b4440b0b003280d030600840c8007140d070010050000e450b180001034840c0c852032050501101e030006004041600030300c1340540c0e003031004104101816200300c01901035404800141800455110190030310b1900d4124140152010b032b582c030040c0b401c40f01102d00e4050018140b241481b006007d1b810040c0d90402c0341012007840390394081501d52401c0342c2d0840c241ca48008480c1454188402c01050707458640800e080d18108072203520700c40c0e5151800001ca07102d207600142c01c90b410400440c904640024080d440c0501c00d408961160ba100c1d001042215107038000c011540c00e2551303400c4030140c800d02001484850043c10b6440302002d00e80041d003141c605d54864140c244103100c0e2104500d805118182c020681a20290710708540c80102d0f2161000c0a02d0250342411040301c00c4100511440c08404180c1008040f510510b00c4145903110030f4009110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 7883820 1250 7882570 7882597
    0x90b0604060f080604060c020a05030a0c0b01050603071d01050f04080601050a0602031204020103090201120c0e03060709050603010e0c0708040303020705041107020f010e0102010f020d02030612060402010906030504061103070302 100
    0x24000303207036601c0b100e1000455450304080d01c66522156100005403d00300c0404046202d0004118041030051008100020f020b44801c0c010000340d14161070030141c160b0049102c1c40c018000c1008954100b2400d81400b20b0b00340400d82955892070050b0748901825811603182c0c5008075010980742000103a0505880003180c5072603419076101003c0741d492040e07030302c020000900c0034003150055020b80c02011080d0b10504203032290130500d4100b90104c3d0401030505000980c0320032950744a060078850300c0d40090062030880401381c103100c0030071914401031194010005856000840c3d40c0c50900540e4500341d449404680d82d680c0e2800d0007907480030b090041c54461031030700c001210942104000c840343d055010b0b0101d42001c410000648441110304080c40c15552a1401030980708071910062030214029600180c4070f04060781445404100140031040b00c1d8400c2c070030b001c0540c1c1c010350680b0407620249000f056035600c0c1d01e4030300041c002002609070721110200602c0030321505900a001141d80049 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 7885070 1250 7883820 7883831
    0xc0a020405090105220203031b030304030801060206070207230402070b01030b060108040f0809030c040219120c02190c0503070f03140d0f1101020403050d0905010917191104090b0604 80
    0x8150034201d440c250f030800c10007034450b045082e245e0b403002001c2954600007402d9906009202038440c2c84107000300300d00780141e040002000101600307d1001c5015024620040c42607140200c2e0281d901c2519006500460340c8240001d00303003011240b280031003803130060001c2d500c80429103405c203000380c421f0101303c40c1c0b140d046001030700315440380100f903200c1c40d0001d04191003802c840e00c540c01c0903448401e0301c603010b014100100000c0d4886000900c1c50903c40c85031200d032501780da2001000100a401100500750421310700314801c80d80000c410910b000c100c00c0100c4031510600c1c05001001c1194041901400b40d480001180c4c03400b8004c0c4021030f805450a01c070303120711042001c1e4172400480501004200328941035a00603200d41c122028142c10480014500350f1070b5280d29142100350807d81307000944845c1c0c14061543e0000c0c101c402042420307014107180b80c225240a4545603610300782d8a005601621400a01103045100101400040c008000480d42d80c1480310b0302035006c03205640258140f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 7886320 1250 7885070 7885081
    0x30809010c02030d020a020a0b010b03100909080d1d0a05011508010b090c090f0418050f0610030b1b0a0c03030e0d0203120a06050603010e0703060e011202010804080c030c0a020405 79
    0x40c02030004074030403a0301a40c948240c140114000750800e205030000c501c01e2118241c00501e1485115020b010300c03035441503d925100203580b8180d503042e040001400e0510010000144c04d44040d0340c0c2c00c09800b80081494901d804001c1c001040d07824001d1041d100f000c0000081c0001035000741d0342c68020007445501c1684500f419400c0c3c0700d1400c0d589030412007101c009140e445407040a0721444c072004050301c2d2800d40660000741510420390031401e503000c10340f502c4410400d0400c0000714907203030754010300340600e00b9014058040b1f44520019114010420024182c041030b0200b041c0600d8102c18116142e41c00803500600c03c0d92664002c43c00b0a16008082400c3d0900141024401140b68011868080401c00164a01001500807003540d512420b002c9070f250394042c0070314040c064a44e80800300d40713400070004055a120340c3c44581104003800052282c04100340b4400304503a028240704005445a1526400300d2141c0035000c080d502000c04c041e12480d0000c15031004482c004c66082c44217403100c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 7887570 1250 7886320 7886323
    0x717040308010905011401120506010302040515030603160f030303180204020d1406040203011a070f060212070e06040b030402101106010b0403031707090302010c0c03060903031d0705061c090804030f030809 90
    0x3102e443c5004c5801c524907200940d20030f03003149c0e90101c0189030150800383e0301e2000c564544040c0446040b4100c0c08000c000207820100021030040d032404030010401c40c07400004021182042c00f000d01050740b101c00c01c07150085840d003080303078566000d04115516019000c006000309070036001d8611076050031004c03d101d071405001342e9068602101c01c5802140740b90311818199880300c030b0115498114002c800d07011442c644041c141c04d414640c0008054540300c6c00003000309042c07000c5d040c4201c6d01848144200c140342d10640340c0c0998180e401041e039011001c0f0540e0651000c45120301d0380d104031800401d80840c950040e00451340f2a480d1624101c40680100407081c000300c80c01c0000071800c20b01080903620800c01d9520755401494401107150716601e0380c00503140842410740100740c90356002c1054000b042d004000ca41c5151000e0100702c0d041c800055614407410100f2500c4400810030000078914542c064018182d0010480d0313079a950740c2c6000d190f480402c141c1034021440b8500002d07402e840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 7888820 1250 7887570 7887599
    0x112030f020d0815010e041a0a06090303090306020a030b0a0807090b03010506090402010c080c01020c0106060e010203090307030314090904050c0102070501090f030303091103060a0e010501120305070b071704030801090501 97
    0x1074440e103183e40d540e500c042803565081c503c030504200310082120011746076842509032a80500b800d0184050ba0740b01072002c8480182c0c0f00c0e00c00c0010014081002c20b0b4000054415281d106030007580d43e495003101100980700403040107502030120355000840110000d41c10040352100541800501c104504145c201c4004607101a00100070f040041d0056100300c0318000842c0c4210031140c1000c0343d540841c4c1c2260000c1002401c640c0d520601845980c0d041000ca0080500910003140347c02c0708900803036215072103444000d00780008103803401c040d1001001550071105c4064a089061310307203400c11303a940c3d249405c0c01e030340507010310b07400443e00d54403561240043e1880b0720980580705145590031070040240309000e89207210b00c410400803036071b01440740900490307010750045104800164881d086901c1a03100503020030460030305600082e00041690074141c1c0140d49000b055032828815620a03c05061081c0e440c100e21040104160708401b80906031103107040200541c1c0e0301c804400300082d6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 7890070 1250 7888820 7888843
    0x903090b07080306040e120a020c0109090504050d0305090304090f06030b0a020403020901060c1109010305061006030501080a1412031801050c04052d031006080c0301050103080906031e0112030f02 86
    0x82d0104002007003400c241d0410340541c181e40b0119404e45502648040311038001403243c2005130090803180f2100d40e4044150809011001010030242c1802d96916075200c06a804400a054884002414201e0300344103442c020141c5070320911004600c10503180040860740011147d441741c9501089146040b07100b038a00392640500355411503400c050040d5208944c0c150110307918554030702c1030080360711010262402548600b005003481d0900d0021501d00040c5034000303004061500e8010802d5180c0022100d8401d0f4108401c20b40c20304124407c0350510b09040d415031075019000081c8140b130b0703030f8007040c015040c234500000b040356450310b00c60212a072095105059201c4040750b0060014501035400c060044445039140449180400100c0d04001c03880441a112903a102010845501d06000c3d800c00d03240220004c010325030560b9541c0c0c203175000f00e944060103804040000b030110000d800400c00c10003030b5181c80b51407542c2d60324412440c0c103000f0f400440c0004c01210385080c90900008a000041c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 7891320 1250 7890070 7890083
    0x8011401091803050706060b0a03020a0201050a05091b011101110301050a080a0203100b040212070509030705030a0b040b190213030303060b03040c140105070b090d0206060604181104090f0903090b07 87
    0x114043e48040b1072641190780c0c1512255544c40000802d00881801072413002501e840251f15441d5404020707085550050040d2611307801c020810a0b081c4021528020404210841107128200140120b41c03601020100c98601c0d0718250280c8013042050015604807001110b0206000f9115407509031a4411000000e406a00c076852403008044a50044500c69a01610040c1800c000300300d02282080c0643e4054003007080003031440f20a007001d1002d000640000c0e001000d54421329036415460030070090006c0e045004030320105802510203d16451020406e071415511107000b5000301a944081380b204902203403030003030009600744024094030302c40d580004e440340c0c1b903e00e49a508a00c4111042c0c0030f40c1048410800c0b0000106d01d4080103000d20680070044c00403d0703601e180a458000080c0030940700b010140700c108050f180901c10100080180240402d80d00140700e0180090700462704103a05090401911014001041d800127920a000b90b58145005554030907401007032140307a0020b031a6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 7892570 1250 7891320 7891361
    0x507030906050307030207050607080402040b030a170306010207030203070b03100609080a0213020f0406030e070902030105091302041103040311060705040f0605070f0b01120506011406070f0507030c0801140109 92
    0xc1e58041c801550b4400300c00d04002d840c0c10116a00c80742403000445a0501056100d0240400d40c00c1521030348114002c260020704101516854680d408001000b8140c00c00e0303800000101e4503482800b0400041d54050206c59174a503c811000c00a60411111803155414a1800242051049030104221400c46c00507104881860f005c0c80b0040c10303c0d034210821941c0810040c1c2240b211140104003d01c500d960001d500308880c0901070600680754082988580148014401e66980f55509900700c82200e103104d090480074030100300906601c1c400c4081406000c020070040c503411005800030500d903407040e40d00300d50310640f0646090141d0702070140742c1c2000e004184a4280684014a801c03130180202522130308840e602e1461915090f04845001c2480b407902d0400c02408100b040e014000e041f0641100103440804190640104079000d4000384c0c032850100f05022040c000351b40650340010a00d02480d4aa400007806054100b00f603241d42080354000080034003051184800403e0540300c000c12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 7893820 1250 7892570 7892579
    0x160206030c04171e0a0f140703170a110a02010203030105131803030203041a0c09060c0102040e0403030b0a1d0c09040b1003020301060f02060603031902070b0a03090c0902120118090507090b1005070309 88
    0x1030840e1f0028003003d151141c40000710120b072804c410103440402424100c3c2d91200c490300700504034096601d4003000d650110420f040107070f03004400d032810360300141c0311080080b035140c03102e0002c1c05142179880b02d101d100e000c0c04000d05a0540007980300c4e502030108081d00c80040202c420108404649182a107641486421258580b42006003080c41c105000541400c0c4c441035010006081038400700c0100380d0380c9807070a8941c00d003102010000d105140c00d001249441102d170100940004054007003c4234005201003551380c5650100c0030841000c1c20342851f000c0b0512000d002507000380261000b15218902244600740b002940b030f4071880c405400343d400c0800c00c0c4c189109411012640303402b0760080700e0001c5006c55a00010308081c080c60740d004103004a090034010015007403038000c04070700d40c010480019954a4844c41ea4115032010514072040010030030018010460b80c0030061450050b0040000c2d22000d54000380f09444084a0310390a13802c4800041d1042d02c0f031641e000340843d40b841d00801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 7895070 1250 7893820 7893833
    0x30203070c020a080604020414070507060f060b0703080402040509030a05090402030402040615020d1d100c080f0c07080609011b0e010519020d02010c020102160206030c04171e0a0f 79
    0x180c00484900706032499034030035400202d000c4229003054030700d94000002c01c001c0d032070a0300030342c1440ea030b8000e00b12000b8200640010040d10801c603000d440c8176258810240f9425007075003d0b200500c030040c0490b4075001140341c010300c07014040c0c0381a4490340c103040119000d10300220495007600240e45503145044043e406201c0650002042a644150f690300005100c542d124210148484c003507000d040b0101710114003515421483c030301c00240c0751008040481c07a0301e03480110b4180785003905100c0303107000c072038580a070407803103040101040304102154071542c0180008840065400380e0050700c109554038440d80e402c9410712a10206000301070f08200039041e000311118000d00006240c002c0c5004041d001c106850000420700c880141e01030f43c1d8052103940e080c03080d080700e6520b9200941c5403032808243c40307104e60f1900718040d100c2c02002022800d01e03000d24040718001c010a0440c0d1044800302c110054070f071280b5011680d04d80002107201c80c44290702082c2c00da55164846a0500f000c04d6a03103c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 7896320 1250 7895070 7895077
    0xa0204050c04080303040b041208010b0919090e10060506090f240f09010807090609090e010905010e06010303080109060b03040b070e03011b020f01090b01050906150a0c020a050907020a030302 84
    0xd0407541044003041ca02414070041d4803903801550790710030b5405d1902d000350641c405002c00400300310000c401400300120100842c0c2444000700c6001d400b0280169541190000b0740d0300c0303d03150b82c0c81c0026440c441040414005008440c02500b004241d91740d00a2002e42d11a400d46a40e0100c0c0d0079a82c08124980b810740a4904070454041c0000c01c2c14078800a845d941c0200948a10a0404600a42c9a6034405000d80c2c1c00102407034000ea0310b07450420050907000d030b2760261080c0c45488800090f146502540134128041d0800028003401031440c508944491080c0400d80002d02c5400020410301c03410301554086410000d2203518590f5680c850030040314029000308104000c05180310050741d02401850006091051003211600c80400081c0c83c0070107104024a1603410800303018089041c2c007200c141112001d6490340055910000000c035403030088a44c1c0c61a611f408154403c08030b0307110f0410a1400c0c03003642d041c1d881e5900d5108103c030b9103d04a4443c0c006078442c101c0030740024030a4014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 7897570 1250 7896320 7896331
    0x8060106030c0c0b070909050915040305180913060507140d020f2a07060309050303060f0612010806060f01090305060402010c0606050a1d1303090b0306011205130302010b040209030a020405 83
    0x854400f005991310540e8010589500c400210f404200b4080150144100303508180101c0041982d6014081102d41044c8001c0001e002c0c0980032401ca0340a103031160100a101600400c000001c2c03420000040780189507010580e5a18a4140041c010500414a062100003c40000c03410102e1740e11201001c0d5001134100c8014241c1032000c00b0807a1801c80c150805100105070b00000b01c001a8032442c41c10303e40d6800741040506010458010620210441e0b40004090341d00c0360140301400c010406504c01c1c49140040b1019003c00003c120070301040b424081c800031030306c030f0661160035401107410450a0101a10301e40080f03002c0341c010740c01040030410552251901041040c2d0340e0703001505c68601c540c40700c0003101c10b4104001d085501000c000d0782c0482500300ca42c4000e4103039200103041049030300030700e25442e03400808101c1503030080310090403502107035805018618002c1d0b01c1c240480c0c40828102c02541c20144915080d150a00a80742450805001001203600076000c00025007000b821 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 7898820 1250 7897570 7897577
    0x4030807110405010b070303051609030b0a09050d08010305010614010f0f020a080f04030506010504020c0c090405100609091a01140f060d020316110606010e01050c100c020d030c02010608060106030c 87
    0x80d20041502c850140c40e008244d035094903a11001c01d8240034003079401c0180340c580c0030181c00034003a0034640c10480b15000e0f680c2001d4110b02a0f03807100b034038400915080300b028141e4070030b5440303c480b803681c000040c9059910541c000c0c03001c1641d078400d03401140030b00e440075408a06c02d03080300752113280b180161100800b0713180304039450400707292942d941c0756000d14210281440002802d00500200b003000d6401010f043c0c03000c40c035005c007959095444e038a03c1020309204490030000702d803d2000400401d1042c2c911a0020002c10741e40e40809002025030034001c030b5483e0100121b22115078a4010b00e00d0498624034005800340750000b040100d20b910409145c0d40c800390a00c600b20640385548040c5100b802c24100500361644401c030040e064060403901c2c5000d0f640203108010540e64413154001c417400f0f080c20520b8076240440c8005080070307014481e0f80781d51032038006202c248550010710414080043d45080101803642c0204074280c8166000755401507000c0001041900c1c4698400445141d2624 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 7900070 1250 7898820 7898843
    0x507170706090f050d03060506090a090c0903060f020307090e040507090c110109080901030b0307080c09040305070f0b0a0506030c0918070b03070908010c05070f06090804090905011505030106050604030807 90
    0xa450701500901c900044c0d40d9a48080401e2040981612449000c0c2c08100ca9803030401d040c40e0005018468540214114030b516010405012809450310a000c0e6511035424410028005040c178000c1d003085848400040e022000001d41800300c0e12002d000302d0300300c8041c040d440e050114400113030000700e07007010070041200e40005c80b00c1028400c840103a80b00b25141079641e00030800050036200d404011034800d42000000f0000b00d4000205113400b08820340b00030510366a5410b003038400d8092150301400080140a2a40400c241c2150007442184c8800e0100100d440e1b80017850740d140140e00720a504045044003142462600a000c02d84500c01c8000b1a8403213900c13130315400380b55001a1183d0010816103142401850030a01821031180c10300c1ca020703400c012442c0ca0726038804000c10030185c007603076031800940d083c031420300300321005040c15040521860800b40f810368000c10b0448007010984800d59004100b034501802040c04403440244140d09150071508c0d01c4455a000303160445552301d095 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 7901320 1250 7900070 7900073
    0x604050919060203040605180303040605060f10080708180c01120b0a0305070f060201020703090501180f081b0d110108190c12051503030406110109050a0b01080706050717070609 78
    0x21030000035807520400c4003580b41d0409240100980340080c0105d48007104900e140b411086d0000300303030f83d4056005000800e00e501c0c0c00e0003240141000052181e0010240d44a24018a4000340342c00c0c064011540c9820840d40c4100055000c0c0303404503050303840d641041005036029071042c240081003070240c5000240c55142c4100040d45c1800b16071003225681c0101c01d04224000e20706001d400240800e0000750f03c0e140803030f40c2c02444007800380075443c18400a810b9000303070420082c180d18050003d204132141c840340c03580c1101da070f01c0515100c0f06282c22112601240b060410141e000c4066500c14500c0c811408114010f541090f00140704060b0030402200002041e0000e008200c002d030203986404c0f0a202c07600d0403c0f8255480106a424901c08d504600c5545880000442d0300303d40d400d243c90032094038000046400f6000004001d8218400d001c000d109001d1407565250490700c0c0b000840340b0303940c0c4e102070a0318603001d110b201070000c0e902c3c0c1f45018007000050000b04a10b912421002550306000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 7902570 1250 7901320 7901353
    0x7050f010905040e0d0206220308130c080715050405030d0f11060403030b040b03061005010e0312130501020f0d090b07080408010e15012102040c020c09070c030909020702060306040509 81
    0x10f090801c0b2280c0c0245400032405d03806002c04d681250044d08460392030a1862111001c0d40704c0804003d0030002d10b070300000c55010229202442035a07101111916443e52101d019580b1300c102d00680c00c0d84607164201d015881d005404076400c8410283c003030800d100800409441d00420540c1c5031003407186141c00c110352040e043c0800e5200d02d11035280000d145c100030040c04112650b84070701c0f602a40c011418010003120100030601120cc09103450841802240c01090400b0000c25007a84001710106d05032107441d4a00d0100001d8500070307800c07100840035481e842ca6848074410112004181050001e02038a02804001c2c800e060040c040c062505d42e031080d03058219480300e2902c1c40b09400070709010844281d00c880c0c035401403000e52882003420324880b54a521b1100031410013031150341c0e20822007544a00911480c0250f01d0000c0517100c1e546080100985902a1700394110f00288a0b02e8003c82c08503418402d40d10f54070340140c07000d41140d0f681c006100041c40f001d082c00101f407184000d20400b0200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 7903820 1250 7902570 7902581
    0x7091701020316080903030411120a111003050717100b0d0b0109050406080c01120e1f05012103030207050c0402130509060a030b040f0c0b0406050415030e07050f01090504 75
    0x496000042c2c0d2032400e1001122a1110480800200704140d401c0c003071400000010341e90850b820007041c181204452000416403080c1c00c43c038082170f018682e902402d111843c1013030b5021000c00e031926446407440036000c408a0b00d040b00e5120202e80d680584560818955080c20792141c00000c5100106407240044152600402100c2c02c02d0340c2c517050406006e5a010070702d900100400d8400340659400c1c203480719228401c15901504020191500120b088a29000014050545003d51301003c410051250304004c2e01c0200d0410f1504200000030fa01c5410003000c4421000c19200038000c0e06640d508401961201000b80c0d071a100300110722400340e40e584010000c400c40380d100b4181e1186860103100700b04000a00d028400c244080d02000421260000d4903481640b240c145042000d640c03130700c070b0b5151102c0d811011440b0800b003030104005130090000c0c010784041544081d030f00d0844d010b048041d195030503586140e076006040200001e060015040d40c03000c1c01410b00c0c6110584420100d8202d51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 7905070 1250 7903820 7903859
    0xb010b03010501021603030e010516080703020307230a0b0402060c070602010605040f020304080d0203060d0602070f020112090f06020307020106081c0f0813020d0309031b0503011b14030709 83
    0x55000004005035078040222417034101280c03160260b41031550f06d0141400c0c00c0f40c40c2050510100240d8000d5000c0c075510842e11840d80301d51000d880303e001d410020b40d41e400c1807501312401c180340c401c040b24440059045a050f00b00c80001003d00104690340c1da0708000001d0000ca801c130806215a120120040c0041000351a46900000d02c0c1441c00d010841610b0301a002c105040d841041070001140c034070b0342100c100410307840300036903680c41e00004254100c2c2064405000144086134440800902c9070048030b03030714001d03606c00404490b103241c3c0e0402c0300c0052400402500c0c65240c0240001c860343c010b107500c880b0318000018095070714030703426003842041012920001d604000e241105604034801138140710852414580904e020610186000c10b6100c004e80302d46a800068001c061140080340051503100b0721200d586060b2455403103c1180c0c502130944203500301040001d41ca038150711441065107190b941d400b6854484104183c0b1584042c28100820041040101e41051504071200505 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 7906320 1250 7905070 7905089
    0x703030b041b0801050105070305040909020d1205090906090609040605040206090a140a0803040506040303050903010209060a12060e0606120405010b0a0f0609050406060e12210406020705030f07060804030c0b01 92
    0x3032180301801840100145c0006051010500506c030101c0e074004107407000d94422110005442c42c25000141a040d11100000c3c140f0b03070541c51090003964450068000c405050340e1802043e140c8200b08009140100c444580002d01c400004000c07410542040350058005480d151500050001090240340c3e00d4001045503002c0c00300030459828440140b030700034114000510f04040c00c00c400107043d881540300140401001244100d5075603820b50464a40140c010411a600c00700a00090700000c22850307200d0b20181b6000d40040d2051400d0003141c81500700406081c40c02e9110600005c5090380071300300341c541d9948c1c0c202200498680d40e00d0140940080000030040e240780110081c407403940d43c0c0186000d1400c10404005050700316007540d008800461307250307011401c0304a038076240a0394a0082c1c00703c03e1448262400c4115000300900a0f943c041c0c0c2030318030f400d80345c1081c50750715210304011525130380c06400c042260b40c1c494101c5980152103441c1552100d8031644584d52008000e821001c0311 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 7907570 1250 7906320 7906361
    0xa06150509031002030403090b03040302030409140603010e0705010e01050d090f0602070506071106010b071103060a02090a050402040f0909030504080105070206060406060f14030a0f06080106030b0f040f03050703030b04 96
    0xb0325041245a1441039204019072440c0352031b80e0300500647da43d128a203004440440071504040c001c0c8160350103400d112200b04044444500140c52141e01640c16030b0182d4039000a0300020f040c045028002d8900684644844050010044607039a110111804120b076a4031900340004407c0c000c000500e0340100409030719080035040003810b1000c05000d040c10b00031100600031041c4008595281140c2800380c0290301c8181d0360a118042c0c84818007021703810300800d001c0100c40000c2d64003a000c5c036003042c1c44980f052515002404120320030350080c1c6285002043c001c00401c1c0058025510080c401d02d885c07402c0a6881d0b020070309450003941d9a001507041441080000d090610680006092038500400e03043c1c01c142006c3e101c90b510700c8021210080c00000180980c44070b4020458400c244002000340942c0ca2036264000c160b41d0204444041816012881051040401501640e040052400741560300c0d90161102c0e804100d0450905407030300845442c40d82d40344140020b00185003180ea0a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 7908820 1250 7907570 7907587
    0x50603090c09010510020a020906010516030c150612020f01020309030d0c02031006031104090318030602040e0601080103021008040f0c03060b030c030d0f08090f0307140607030903080601080a061505 87
    0x2900c10580000c0d00845c03502d941c0c5116a42e001400020725034055411214648406004032a207105022014994400461070b0004040d8410900c2021500440728007800d0b1500c0c20892065981c24072580b02030b00c241031400800f5207406203180160440c14012a854880002e020909141e040e10503500404c40c0c90542d0019800d0600c400000425088401c0120500710742d1500140512290680d014a40e00d00c8500d0406000e035504070b50403003141c4003031440c1a039a8a8454044d620600603041c0c0c1005000c08103810f540030300c1c807160690b580205600d2071100e0040b0308071003d0302d0042041d94070b011803001500c0814003203c01d0402443c06542d02203443c4601d50f0615141681c5428500c0c0282c1c045005503400642c0041c143d0f580d481c403491b2511081c1c4404501c2842c001c0e200c40707811960b01000507001c0800c42c80c00a040100d031044c0c1c05072000c55491207019070403100040c2004d008111868002101903116900c49644002011800605942c54840f45201c5000146806001c10b00010b0b074840c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 7910070 1250 7908820 7908829
    0xc0b0d0c05090a030813030203030301080f070504060e0117010605090406091101020c09011206090501020a0207050108010807050102060c0a0c050d020106140d050c0d0807060203070801030b0906071d010306050603090c 95
    0x26251005007081840c041d00d07080450742400c040c2c4405001d189010803c0c0c240c00e10340e43d8a2070011600241201c0e141d5840f03254441d01c440040340c0d070003801d128000700010241406e000e03e0041320400284005240e18210304948001070900b1541ca8a56850502040550303074080f503030703000c0c41c02580000b44100541ca0600d0845160460f040e040d5804100302c1c1d0050b55074a1a5a4103482604244c88030a0006251040c00703404032120040041d400881c01f50040c55000a502e411218240e0320304482d07036030703443d54907403110414009c41c1d0050308050700042030440e10b24002e100d807100354a44030805034043c1d1909802c22440c00c41d100c0050351503030010042440107900064180340d08613039030320030000d07d030340c1d580d80d0307502d04000160140031490b44075005e126072201901c040a8204209550740c0c6452100104a264240070484454904d000803460f030500000e1200d1190146407241c905121048100c0c050100b0100a0281003644801d008110341e2101ea0146000341d03c40c50043c22460318800c10030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 7911320 1250 7910070 7910081
    0x10501080906250504050303040306090c050a06050703051806030901050702060c131403010618050610080601020a110a090c080117010905100207061808030f0903040825030c0b0d 78
    0x10407980d070044041c030001d031032020b420076000400204036101040c004102981c003801103030720107a0f0500006c0380001c00e000d070716003003803042a2090a245441c42e0b11603040094402042c040d0000259040c001761002074080c074024100e04131000d802010401c50030000403043da104a0344c1e64a182d45840a00411580400255070040030103d240c504200c01d040d00001c0f024000d100d50b140c40250307400e012059403001e52110b0302505095400a205d00a41301c540005090140c95040c0101800d0780e051110b280301d0703c00703039002d480145e0260070800080cac3c031a0201b0946500e202548403e031284000350400f964411440034604549513440b403136240912807403d01000811a00c0386906080e0481c000502c00302d00f40503201c000c24001030b02c40d07404c2d007403000c0184100001820405c000c4101c810030700c41c0f0b4074080e500c00d0b01858007003449655204200c50f02ca02582c0700b110304640c00086c507007554250f60210340d091001000603451566990b9100c1d04100102580103049401c0001280b0000705124081c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 7912570 1250 7911320 7911331
    0x918070501030c0507020103020f0d09230601030b010e040201140a02070905060d0f0b07030b0301090804092004090b120a0308010602190c05010804060914060a06080a170c0a0f05030301050108 84
    0x10400c4080400f0301410b107104d00c03034000f4109030780017410140f1450305006a0307000301c1d08000d0801c00700c4020707d030400d04040103803c01e034000c40c070250b030301e440c82400025168180c0c1e5001e20041481d91801c2070507030211b000a00124140019401c103c0c0180714020f018204126159000b07003509442c209012049800181001c3d0003100c8460007280404c0b10f0349107030084658440441e001da030b51594002c5009014004165505508013401031050010740800381096038440403082010f0b074100103070703c003608100d80088054154188420400061a94070041840034013406612040c1440d50700c0758207203800301404902060343c03800180401581005441100884a41d0540c5400c0305500c2c2c0e08041034151003068100911900058200003180d080043c400340d0264190080b403d4180c01c40c3d44030f4800719031410030203251400c00103580e00000b03107030010303560040c10801c000a40720341d5504199001c001510400d129504107080000c0000c0c041400a9000d0005180c0365418440010030130f9101030003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 7913676 1106 7912570 7912577
    0x4021809010603030f020307020d0303111b03030a050112050a0b072105060102010b0303070206041509030803010617060414070e01090b0d090203010c08040c030807020607020918070501 81
    0x10103010b4034825120600300c401540301c06c903603a01507c5d00281d44510341c1c0803001c000c203010303601103640e43d524196041d142108040d00c40740303c0b15040c200d40c44194400010401000b80f1b41c8217003405004032003005018011ba64a81a60315403003144094014603c200125110720701a00512043c1c12141c04171800340408003035000000d0400701d40d800d000d5402d04284002c58038020049848255000f4021030400d41420100c0120400740c0c52035405020340203d010001c00c0945010b140200200e9035691008046514a4410700002805a80c0600c0c246626012007100c0380306525403181551902d08081c2100070f004a41d0aa003542c842d520b070303410004151324001c085401004449009800a012806d003941013103a1145045401900d41120b054060002903417240080282a0004120030f041415a40014240d410261a03e80e90100f0103066130035201c1c0d0511a00000706400d0a = true := by decide +kernel

theorem cover : BRFrame.Cov 7733820 7913676 := by
  have h0 := BRFrame.cov_init 7733820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7733820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 7733820 ≤ n) (h2 : n < 7913676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
