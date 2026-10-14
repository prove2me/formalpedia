-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:55.854606+00:00
-- url     : https://prove2.me/submissions/56be75c2-08a0-4fb3-8149-d834657ce2eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 548741007 ≤ n < 548920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 548742257 1250 548741007 548741009
    0x1401020f0c0313080601030f02010c0609060207030314010501020a05030d020a1b12031815110d180506010510020a080904020d020d020703022503020603040609020402210109060b040509060307 84
    0x1a0481d90384070034000c1c060b625440868415041c0086180020303022001040040c101d80d00311012032940586070340111b400507030034241100c0003959908000085156032010700441031203506c0001d501800e00340300005020f416407080c1c0c1198005c4c0c4420001071004000c0d030f0360301c0110000c0942c45182d84041565903d40001d600c0c03441c0002d4111040c24000030300403031110300b00c0645003000490309080549800c14034070000a0a41e6100303004448014809511001000c11520300032070500b000c0b42c020300c040c0c607011280306102001c02c01005050202c140446070041c20121030344102d1030000307003001e51241403104001e0043c20000c1100c421a4031150101c80f201c039043c00c070842d9120030544d2810029008540242c00611420b0345140e10543c008503500d481198021100105c0c07450343d401c011140e400104100d0b0f200c1e80340c41d4000c0058031075001800c1c440c0403058803c016560900d000c110860740c140d010350001410010104074001e1554211025150306444c075a80c10351f40c4d10042840c003149 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 548743507 1250 548742257 548742277
    0xe011503020f1905121522060b0a031425050a1110060608280e0c060409200f090405070c0f200a0513020304140f01141f03140102 57
    0x800004003151130340003008000040c0703880000501c2d603c0e2004002c004100030025250840150443d03602d500142d17a11403841d90604060100340b19844001000554102100c0000425191201404a9070103262500d07400640c003000c442100110300c60241c100d0207841105010300000044c0950700342d00c04e4040070f03501d0107114215542e502c010300c0c0e000021b0075144200000240b01c18045a44600180c1201d03203107031118407a0b00003143c4002e0510b4020507020321349200c103206440d0b070021f003519424007910040c03496400c0001c0050581000c0b441e0806400701c034000448041181a001084c2d890a41c2c000c8801610700148680d11100140c51080c1381d4413003c2c103000fa5956070700c000c00070070601c51020b0b003204051515103120030005101d00c3ca5403601400341d02038113500f502e807004c002c95409143e0090080f54203038400454042d110b400d2110610810707115035141c45040340e0751a0184801900320f00c040c07142006150400094280101c03043c007004000d010504c1c1050440c2d8000d4064400742c40c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 548744757 1250 548743507 548743537
    0x3020f030f01050c030a1a01020d030c180b130e0c0412170309060709050a03050601140d1b050a05120c0409030302090a1e240507030315031203060e011503020f 70
    0x10725800300107117900b00f02c031060021404d180c802c04080c041c030030042208200c10b03001450a209944810380c00f03468983d00420070400c50420b031245c1039119100d1813001308000d649503591509039000412803005c264002130030070b8030342d00d09000381700f4210320071241101ca41101d2032075403c480c6e01d4080580c14141c4031000c01c0100200500042c07190100340940980016242e00d080c0399540c1050000c0c04d42d0b2480301500a4201c5801000f0321029408a08401900280070110355030590341d078800003290240d098162a100c0e0a018459828820100d5001e05001c03075111514101100c00240d403071030045565401980c4811040d01054020380584101d040f008040808194031100340c1808a40b85c6008035138445144140000d1044a14036109030804507481c50140c032240d05101550070303510814086040640c0c0740305a06050f44100d0141c0e000d10f101e0010000050080c503030040948407560004000c50b4508801000140c3c4442100b0900024134100503840d2a80d0349101116030060000c070780c5047c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 548746007 1250 548744757 548744761
    0x121a0a1401020c0603271b010302030a0b0d1203050105030109020d11010327060b1804021009030605070801060305060312090d08120f01170a03020a0b0c070c08010e0f0f0703020f030f0105 82
    0x8220406e0840d15200802090941c008a0001a42d10f10030715101402d05180d40c00300307031041e521070740003903a10100425000c290301e001d50f00400c408900d400c00684508007000c09503c400b0f9032500901e8010042100280084803468000030b80c80c0c5034003e40104045242260220140d00940201034443d0803480001060a030b100b0342c2d111500380d14007084400518140d40c800342413502d03681203040070a02049e42c0700b41c1c1d983d60f401e0081064400c0100000c0c0120a48000000355840c000c00744208c0c841e946121007545080000303004e5505c0a0001c91280e040303030701c100c080c00541d10300b0307101040d0003102c007805009424240802144203031100030064541140400010a84212031141241d000101d0148181c22000308140c0390070618200400603000808610040340c0140c950a07040100c42070150300c1c08103140e5444281e80104d90008e40240d45600b00030302100c000b406002c003c40c1c80e0501810300c80261080c4d083c0c5821590100078420525a50031a440351010003011221031200c00081001d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 548747257 1250 548746007 548746021
    0x90905091c0e0d060c1112041511060901020d110306010c120e06070f2a062001050405010b03070f06050d0207030203070803070305100b070503070201140d0c121a0a1401020c0603 78
    0x5060032000300c802090506801c030501080c0083c52000081024812234101400c0c0f06500c03140c5400228403400b004158200302c6030002c000c0c410325014007020800140d0711210082c1a8091301d03201000b500c5019414810050355076080945a420540d2020900c180c2c8101600c09452104250070b0042e04450086100f20410000ca210aa0712a000381c01d0340380744001e0b801440e070711411401d0240d1030341641c04600f00080750180984c0665880510304015895040410b058211501254159aa69151603000c0f1150806025010180c403070082d04200c6681000c101401c0340c071485210746d0b400341e80001e504062520074401e40e05042d501c19541681c030b00b080040100a860152194182c024844034001402c01c4290202d800c0d50364050080c40c100483c9400540710740d6904200c11400d01c00400c440d05c5d942203244102a400035039a01c41403040d10002c0000e42c01c03500c013070750243d40c5038800704180525641e40610020880f44281d501c800c040c12401c004031b0810403001714080e000b0320f0100038040c403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 548748507 1250 548747257 548747261
    0xb03011d06100801060b0f2a010b0a06050f04060c02030f0708030319061d0a09020604080f010b090601080c130305071205010c0215010b070507150c03090905091c0e0d06 74
    0x68680814440c1203d0b202c04640b07088502a2080441c0424204440305003061528058401c410f800c8110503200d46020305d542c00d44000017806104a03954411680c452860071444682c0980210703c1d00c03a007449e0290442c041a8070960041174284001264038404564080010050018913041907641240c0d070741d2030003641d940066900401009107000301c02001840f52040780100ea248240d00d42d080300c00b250358803004c58405084100840e0701d42482001580300d003030040004103c1c41004112000707580100c142140c013a501c0140c856a01e10080c000c0c00e83e40401220740120348071124556801541c4481252004141d0006009002c1c8000c0000c0f010f22440c00808040d003c0d90091014494000c03080340c440900407066080d1308800e10042c1310a014203006450040e00c22021500b085444507074000b610b03003080998800040b41017408404041d07004080500420b03140400340501d040c10340006860304415010040d02c19003a008440002d4850705d000705542c0d4014140c0c0c080719006040000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 548749757 1250 548748507 548748511
    0x131b0806061e0408031216081312021606090501020d0c0b060103020306011806031a101706010e040f200309030a0e010519020c010818100b0a0f09020c07060c02060304060b03011d06 79
    0x102030040000f0a214003401440c115108244164003010402e55541c0c5040301020302030460021440354005908806074ce06507120f01408240c1c444501da107190100092800980d544404204844140e9160000307848078071090b0445400d00700076841742e07075060040701c04001c000500c050780040d2610028010360150300c10031141b240303441d41d5064010f210b018807000d400c0768030860303001034241c0d08207281c0304124400c02c03600494140f500b4004100ca120002d001d40d10000043c000f40740d90b507820040c02c061080c034810b80094065501505525203c010942c0b030b80190911a000d02c00c1440c1e16890681c8500100c0b0180c207081a14480e0240e044e402c025990701409051601081900002c40d40c1101420581a9074403034541c000c0511003a0340d03100308c0151402c80c00035030300031a2441000c1000b810b02e192040261030001c03001070f00d403042c030010709182088503408402440362043c0d0b000050384803802103175071150b04040086030700008000400d00401c1d016000e42202c4000459075110a1000309201e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 548751007 1250 548749757 548749771
    0x91b0304081306030c0f1d0a1d0601020a0c0630050403030c0e1c23030a0e0103050c070209091221010e06012c131b0806061e04080312 59
    0x118480d440e043d00360b0480700381c003801e4800300301e0504021103914441c80c041c8403140f034400d442c955100c200318049900c4100030307044091800a4408a60780e00021002c030700b03522403c2403006103c60801030715405a941b0040c0180c004100e0364411810b20001b010890303003030400b041c04440d00103d4501c5c0264004150584040f00000c2c10090855540b92254500c0407521070002c03d10a9583c40307034444100300214004003280ca0004c218009849010f070404402d4145c000480955a03541d030801000740b021166010181c1810319082c14060211190000d540e0034690643e4032544a44518080c180f44c00090b480c920400b86d00080d61140d0111300e00740540345a00750100700c941c1a40c072108e1074a18440102c0c1c14078009084140c0000302510b504081d10721001c1c0000c124090300b80301c0700100302900c01400c5124907050700c0c0c40f40c2083e00c4101840c2070020714610f2034451502e0820303500145c0701307110b02e20303840c05d140900d25188841c0a402d00200e40040c41e0700c201726995100c400302c01d07607540c2104440d45c2c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 548752257 1250 548751007 548751037
    0x40e09070308130e1302060912010f020412030f03060819030203090d15110903060c1b01091209080102090d03110c0306130c1203081332010b0d030509091b030408 71
    0x2150304580e0300d090000540b0b90042440f82412108000d104206100c8003105c0169921a0070b0492f00601500c020b201400c00110301d0401590a410068201c800600d2000d0070145464020004c2c0007002c42c01d003611a038010141d45c40d840321401d04a10b140074000903d5401000f48144408100700e103d218000300f91304000a10100000c0c50f1001c21600a0315180794054012000103001410317008001c0c140c0c050b10000041144000c0d0701002d00316003a00d08200c1c2c4205146d030701301482d16007100e8903000410403d002549000302580102c0d1044041440003818407241e5035030b1200c6482d00780406000c00c54040c044034464038050b074280581036804a0250703450726996501181031000f481082ea03120343c03d920340300805d44420381413690380e0224078801c3e6401c80039414169424100300030390491070b0680c0c0f01c10785811860b846490f400c40f0240d900d560f1007007590b040b022000ac1d4000090307600107002114010802d0303031100207401003916034540da400b10300000020401005509405450410012810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 548753507 1250 548752257 548752261
    0x30b1e07030c080c0304021813050c09160e010306090c0504090e030403050d0e04140103200a0f0902030901060f060f030c0203180402130519051203030606040e09070308130e 76
    0x36821100c080301c04000094003c1d0000320fa0340c406000039a0410f2000d40803041415503080708601104003134a800c000303200909140c00c03e01104210501000008980030000e82c10102d100310041e0034190104400d00200c8032078030545a00980c010783c01071008080a000505142c0790050150741f00d40180410b8920707185540344030103000030685060b254403030020031b0b0022494505545000720046010351181e00c0c1e440c0464080480b4074254021441429150050400541500e911040002180380503204076101002800e0602c0c06250071038000d0400140e40303172181c2000c01d0140030250414031500e900b021000402d05c1e4003148500751948030361390421241088550032a101c0c4951a14520481c0750821780c0f20152600d5030007010040305c18018428020381c0d80c6d0101e60740003443c04070f4080d091040b000c10002c44c240000700380b4000c043c2c180a145145403401c0041c15a008502940c01941440f400044904a042180c0e102a542060886440383c448088001100d1898010001d06040d0040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 548754757 1250 548753507 548753521
    0x90311102018010c0503090406030b07030f1a0d0507090908120a020906040311030f1f0c080f0a05091509011b020c0d1403130b040f330504030b1e 64
    0x20948084200d2102e20540010110004445009440d20195a18082040030780340658462140344019446001d07012510725020801604030340f400a0070300e985504149200f00c81807002403401c03056131001c071381c2e22a40078040e0030040e01c0d10020ba00051038152900c03110364140300180f00580b100b40421100100c0076521901c020059000e0300300c1254002e5070920052001034820500c11000c01c5018045030011040c10000b40d1038050340e00c24100221030803140030b82c0c0d200e0007802404c46007174140c145040c140c20b14056030350340c3d000018002c0031540d03a50300200380610818044080a404040407020310741c1841810507008241d529400741e40b40c010b10003840c103150f001164240d600100107010f101035034550340b41d040304208072000e100503d0004000380d580408071001283c010705400040c003900e40c0d0604c19500d6803580203800150082c2d4440800031007442c11441440320b511040f4610900781000c11105a8080c0619003005080030300900822122208a05c5000107080c0314480405541d15440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 548756007 1250 548754757 548754821
    0x114120d020c06070f080a0306090f0c02060408030606070b0f060f011724030f030705010f020702090c0a0e04090516060f050708090f04060b0c0111041809031110 71
    0x5440540c202050802c480d1030b210300a081524010324041e990100d459842119680c84000030001084c0d07940b905100c001b1140c81400e040d1980c200040011200003a00655100c10040c80203195400020020340300d40c98410540c1d050640c0070080000ca42808400c5d0701c0e8122045803045d01a4041c000980e036190f12403454036901c02200030840c0410384854010766080c4442d1403508120629810b001c58441d14100540214958540040c50301c4a849140042c00e50f181c552045040900500000016a586468a41c0c100d800b850030303e5580c2d0410355080d2251000b618002d03921500e04801a400c0c4903001c5039a1036501900c5200d01c0100d92540401d17602d0b04d80e081e1080d80000c0e401d02c0b1003000252040001d01024400511030f04c204a0503000043c1550247d803c01143c2d000003144030785910209000d11804c40304221a141d0900717041440418404010800c1c0200c9071ba225040a411305008030340c010500c00910301034440c04075409a4801c00303410542e035038202054810051070502c1100c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 548757257 1250 548756007 548756023
    0x2210106230f0f07060e060709030c14030718060306060315050f0c0a1d0d030309050f07030f0f02221a040b10030506030f0a0308010501030c170a0c17011412 69
    0x352a500308107504024003c035421044040782c0345591882d440901c0002001494403840c1030b0b0790f4400c603903421450705000201c0c040d4021500440546007460381a80c020071070600b82d400d480c8840d480ca001514000f006071200f540f002e0101490800c01000313025525180c848005543c813002d01460b1078050340036400f050225041e9120080034400740025921522040e03d01d00c448400340c10040341100002003203c000500100c1c04a9914503054080103000e22464440c1107a40024180345440c5071100e003451085400300402c821401d0000d0811980c410a56011420b0120a0080000340249151b802060300f071044c400342405882e0303200d5280c50140140e2665820240450b100d055100c0820303030240c039010700b50582c5402010f0031f90b81031840400507940458020380d40d89929500d424000b408503500540c1d24000c002903214100314101241e00700f1508020341800001e1000700d41d0b403007203900c54200c01c02420f44a4001e000000c2402d20147c120113090300031103001040e0802d108403655a8029 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 548758507 1250 548757257 548757277
    0x1103030417090a08011a030706080408040605030a1805070905090a0206120903120a150605030403023c03120606042702091f020c01210221010623 64
    0x70395034000310940c0014025080e46840030300703c0392215403030380c1509083d2440c0e07040505100d0000e00103c10f041c9010000f03000140101e0802200908127912040e18a1059006003001d100001000c1408500c6940c81100b441400c844800f11956140c0f4125449804a200d0000703400c1c140740208900c51404251410225801401c0c1458000f81307481c03150341c8a000600403c2c0900060000e51940d20305031b0308551142c0e014003c001901c2034211000b40d030b851119041f40080000034000c00002940024074903410890046029003007201ca050345403101001c1e0304186510b820000300c0b4401404000014046241030b4404ca01d50540e5040c0502c10300d40103610441d0903809002d6a6040c6410301811001c002428290002d4a800d5021001c510016895141018880c441a2132044030590600c0100d402042c2441c00e84c0c1e01f2041c1c9100d10365404080c17080040000e5001800d840000102d5042d01138110301150030300c00940e96800094a1000c2039003c881c1d0f180c4520001e855048424000c556003088 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 548759757 1250 548758507 548758523
    0x130801020406020d1b17030f07030501150804170a02070311040e0309060d182409030e0f011101060306061e0608040303050613050108011b02030c15040c0911070311030304 75
    0x1c13590032a1000700307003994007150021401c07080300440c40008122040801400c4410358a00b4120381c8007198580040001080500d403400610604504040c0c81003005424942124241c0317440c28541d007081000c00714111016400210081c91503008600d0404481c040c40386482d2000483d002e002c1901c007803480034105600100400c0405140c180050318484880300740010720403801079808504c1c840c443c041550b118140020321040701450f00c50304010f44240130000e10808045a030040d000010a060141c2714180e404584091079126205906030b1104002c001e21240759a03050000003011a40900e040c1c03075000080030400c0440140b032038003c9668075601c03941d142c6e0300d0b614120014003020702110742c000d0b107a00c003031103000e0003600409010b0b001324070000400e4294140460754428461107400250340042c0407014070103c01050042c890800c1002d0ba0355141d80c0e520305804034080c0794018004081c0742c40b41c5415103078011005081c4880c801c0c5c44558141c0c04082c52681d8034001141c004103024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 548761007 1250 548759757 548759773
    0x103180b0c0f13140105120417073212030a0f11280e030309211b030606220902040e070b090a0b1c020310030204090813080102040602 59
    0x1520310103066070000c4079160042c2030100c42c0300b58079403990040076001c000304089581400b11090b000241601c002d401d0901030b203800d40c002803480c1172080c000d00c040d05840ba140d4142c048560380e5001c9880056000b50041403c0d5000b1350182100e204a120100000d40407100070010444e0000b5180110840402c190f4110381d1644d40702c002801d4241c000d000c0d607d444548001c02030744608040d120130704404a0900344004001200841b02c80006100c40400030b24002d8814552408001c9902050068035081c20003c0250404102c100b640c00c48200f0505c142c446000010410031403400e84030000f28180c0b903030f40d01d03440c2c100301c1c045a001914804030418070008800d411001c2c2d00101c641d901c0680041000112007007100d040c19038650240551402c00613a04545180c182c480d08064440081500d003051101d8080301c00c280164440401c1a650003c045000c240005501c0e070001d640c0100180041555490191190f40084011000000ca9250003040038181802541c0580e9040d500401da16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 548762257 1250 548761007 548761013
    0x6040305120a0b130905010b0306131e0f080406030f02090f10171816080a03120e03041508090d08280c02030322050c0d14010c020f0705010318 63
    0x1c0400030301003030480e954600030702c210758558880c028003110741040700054405041c10b20609540202481c81e109400c0760082042d58040c01c071030000720542116642907100c1103070004c40c2e80e0090359100030b0244c1d41180d8162003040101030040c01545e10720707941400180c410550003000da020f004441c51b4880b6103101d98000c0b0b402c1114002c02f0300d036442c0c90011150061140c8800b41a08203440e11b400702c140c02d03141404640001c1041c3e150682c0340d200489240f6140001140e00d81c000218020208043c0340e0004040040c1600200d2030000510140d0f603450f036485a030300c0c058011409010000c1101c65000585d1440082590081c507041034458004030346e1441d507021030b50000600f08010100e22030b00004c000c0c0103070384120001c84141c0c0d00110f5883c103061004611149400c0941a040e480d0f149041c4001140440c441280b5130f026600d43c0020b00681c6002d03068041c1c241c0302904650303e03200d4500c0d121135002409100386881c0c1c030156145961104011400e440201c202d5660451400c41e0700000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 548763507 1250 548762257 548762287
    0x80a26040b06240c15040c172107060c031a01050f0d020c070e1f090c0909091101090807030206120426090a0e062110090c1706040305 59
    0xb021030014494a4402c05800c1c510f01500b5070f00c00c2c45002c050001c5644904020100059400c0100c10305039005207203060341e520280105180601d82c802c500c5107003d0710035508100060200480000b80c1021100c81d07003485010740b9001203409843e003a0500c080000707903d000e4440c1c0300c8100c01c10344034101503464440040d5503d0b4040003c1e108004810400d40307070186c400388007900b0000c01d00e0b80506075081c5070404203007858102078802040c0141f6286c24489201100701300d80111141c09078042006440708009440074050747d8001c1d03030702d079040180080400041540140180400341c0303031a80031548590a8565507500303400001d411600400403841036006d9801030540c07007840703041000b84071140f240b1846201806503031600410080455140c8007803070003940d03140140045c0c04d03810401c0e02e400800254505000707034244440401c000c500303080e0380c1c0e07042c00b9596594260080c10f00c141c0c0094035000c003901e0030900c1001007101440e244824913050100c0c02c00c0c084d5030590780b840d0030034181e2919a08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 548764757 1250 548763507 548763511
    0x20307090c080f0105240904020c070306110c100c0905061b1b030d1209020d0308010305010506060712050a020f0316030201060801020c070b1b0d03052d07050a0e03010603080a26040b 80
    0x41b102040c004441c0554172030000b4481083c03604060890030303195243c841c05481100980a1803030b5418070182441e0f0100080480e104150340c90040781c20b8103a0f48003941c413030065803c000d801c040001481a985002824500d281050060881c0da107003000300c030313262a910071594000b0752540042a42000040c1b00303020024490004407000070f20004660b0010322154805c1004030040342294004005100307081c880d05510500c143ca506180800640d0f603400009200050482403000c0440c498240c0d603c2003003101a03c8038802d007184c3d503400d411038456011030f1038188110010741c280701e00801c520006000f504d40117400c61000b800d41e00e00f0458941201d8100305007000c8400c20440340c0d030305915810441d10a0302d4040761000078035810204480044c242c0003021152040007404184407007100b42d0940c10b40d00030402c1c6040c03600c03000c107510120b9211034420075042d415802d00001105101d9520001c0280e0091030326088104c180c0f40c1d0b2228400c111440d40d400d9076140c100000350204028010445d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 548766007 1250 548764757 548764819
    0x2030a030f020c070305010605090109140c0c0f100b240409020928050a05030a021302030705120f090610060815041112240d1e020307090c080f0105 65
    0x143c1850a6600640c0c42c0c07030025841074650780c0d15804104407500b01001d07a0341c090000c1c020184800950740308544005036003c1c008940a83c0009140e142010003800000e0032121341c0019079a49805030140000a0280d001c440c600c120085918084040c155207142e425a10070032401d01c0c1818039080388d9100070f42000c028130b0741181c070020b6100d01e001d80c100906204c0c00f40c0038031040502c42c01c000c244010140070380c200324044e40c04600c8001c0580d0b5240408808a03480f07010140c0d40769510482120b03139000e086420035100d0079032000d00039001c2150070420710518900381280c2141d03540c48800c0400844034481d04001ca81041c0c04200230111100c1400c414510141001c035802541d10740c4414540d020380340340d08005c0c03c850140001540e100001c2c41486a00004207049181c0240000703550710b2804400030104404800500075070382d0418162201e003038004050b04c4c2c42036138800210001d4440741c04c40100080d01c07800007503440e130040011380307040c1d42003e402101c217807200d007401d2112215041c440c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 548767257 1250 548766007 548766011
    0x60d050c0a03050d03180b1b09040207080909071b140a0b01080604061514042f0d0509010c140a14040602030403020a050f09190605030a0317060108040302030a030f 72
    0x100384a5180c5100070300c01148120020050704101031001011140c0003a00c004442c1c605643c1b48011860f000c4010b03402022000900c035444c9405404ca0540d0700c00c00604942007400441e00e1000c0c4580c1501078580c5a0050310741100703550391404100c5e20b020f001030607608460081c0c504040400d0b060205008208080c10407103100c00c00e203403100c0801d04003d0f0700c04002d42e07100a0800082100070f008070700c00d03046030700c0d240421642054080300700950300f409250701450359503800e090401c5910403005500300042060481070311040000802542c40004103800c40b81c00c09000c900400e00503c217099020580d80e551044a40441c2d40b01186588074000300c84c20003450b1450881c0c81c0c441d4200400040003e90003e50383c603490740c4148110307880035502c018800c0180d901140a01d85540e540c007030344040004000f00d40c065600c0455001445560481d540600c5802049002c054014050600e071080900f203100f855940e0f800111012402206e0090050f0014007a03503203214001c4c2c00542c1c115000c4000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 548768507 1250 548767257 548767273
    0x30c07060b03060112110907050301050f03010b09070c031b0f0303020903010923120c0613140318040b040e0c060c0705130203010603060b030103030c03050f04090905010c03180209060d05 82
    0x20f00d041d03800e81145c0303040241103212004004804403100940c0c0d105641c0d690b00f031b141c540ca010700341d80414421240500c81c450503280032560203501a00700c91600400e140302a0401c400c3c0103202250300c400490120710320b200d86441c1d85031f14000040b0740c191b10003c0700b01c201503141d03001c6000c1d40084860316007640d203e4079218009002c990b6002c0400c41d0600c3c5040c051508120318500d4241c1074076003403a40c00c00c10000a480014089451b55002e040040715076140841468000311418010200f01004d0201184400344c7c048501080b004401007114140700d401c13120303010003003203449075424940749074000c1d803000e042030a004007d85155054501a245c140ba07503480400c0c09210402142c1c018642c0c00401404010303014410180a414030305010303400c560459802a01110921001030f00b0b1040100c1e00707a40b40c04000040b2000740210003c24000395400e8901280a8450600c0100229040c04008811040c00d4101a01403c0c1c009003030180c140c91304020f200311462001415143c0340a0054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 548769757 1250 548768507 548768509
    0xb09010f0f0320060c0c270f0402060705060c0306041a180a0f090312060806010b040b0f0f0c010902120607050405130b06161a010608160207170d170903030c07060b 72
    0xa480101c0540c03020307201c0c052102003044018000d47d00d00d180860072008000c00d2686403003081d40ea100030f280b507940d4125101d90001401c54051054028418440c410420983e945404061406140c003554240115840c99020000c0c40c0c0804807055007010b05e43c10705801000150b2402604546440f10015003a000000040269003502000358045140c00040d403035a140b05200703a41c02828501c010300140d50504580c210301e8840c45c81400701080303010800200300e424190850302501c005500450745c990201711000c0c040d290b8000b007a032144041c81d41c014580c2c0000b042080c0718660a0b540d1a10b07141c00c1c80104007003038807100106116140e648000340d0706922220300a0000004024038070000c2095441c0200c88a00c179801c90030303050700c42c60740100940c64101d03454681200b1402c08030205100b141d1070480c50003a031a4040c0a0711508041d034076280c42b00100d542021250995219041071045c440005609034040c0c400c1c9046900c104002003502120f01c000d00300e0b03d8400c45d004544403d03200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 548771007 1250 548769757 548769769
    0x111f0c090f0801060501080108030903060106050703020c04140702010f06060906052203060b0909010c050f031e2406070f020103091509211107050f01120608010b09010f0f0320 77
    0xa00142d2a036036580d80140002e42c2c0141c1c955004103800e1005503c0d04c000c1c0c002103510f9420621500091200202da400205802400343e611402d9004d00200300310140c01c080c60000755030aa4003440503500c0c14a00c074900f40d14500955003502e80323a44841d01880e00e0568202c80c030307a0201391080d91424000303140c40b00755940100110000d5004803004a00380c0200c201708000240701400d00c1c00b4aa1400c100b502456420030103640c84400100c0386d032500e035a9039101090b01081460b017590050306d042002c0001009045a040d60301c810b001418090f07045e071180134820984101203010f405082c00c4011080198401d8110494641c42039488002c00d1484e80908000c3e18005034003200d004040c0b0b0340392040c0401c0010708882602c010f1500c05031180c01d01c00196100d101a020703036400351100903a0311045074080c110900c511080784404000071942d500b000c60080600f1201380c5c6c85410054000100381c404070348446d065a42c4818081e501900d10794031401d40c41d101c0102c10b50f500390a0441d00340c00d40d98031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 548772257 1250 548771007 548771009
    0xc0f12040303090e04170d0e060f040605060114030103120509060a0210050c090d0f02010e0310060e100506030705091f02010c09051c020607060b0619111f0c090f 71
    0x8002015110360440c58043c00800300d070703005040b00c21504400c100c0890301250300ca09055030034042007544c6110101c0100041c2c020651030700f440c3e118400038000415003542040b80300d98000e1408028a03201d2500442c0c142d00d00c107420400400007400180041030710303041000b02c5580da6041051401181c0f2010501507000404650096000000607446006941c05110342c090803090b00d041c0b914070500c1c0081c0380350000300c00141c190b0a05005490031139000b9601340c002540028110b5030344080b141c4004c000f414650044d840c0180d00368004c50400d03030403041e441c1c1c1a01d03801046281542d49540d0112002d0700426a901d9000c641549014034040c00911100f51306102d41c0d001085002440e20081e00174429640418010712111841c4540048164180c050300f5504036121940d903060390034588094802c60f001154013141c0002c0c103100a1080034145569036603d9280e042d01b1000c44030b5882d844c4c031541d008600c1000c076110701a20481761190321030a90b02c030060030075403600741c2c40d0680c00b050b0f2101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 548773507 1250 548772257 548772283
    0x2190e0709030c080105220f0602040902070c0b04240c0b180f0a0314130f1d1b04050409150509031e191b1a04031101051302060c0f 58
    0x215941031050020fa00342480180000000074081d81c1041000e240c0342d5a208141c40b0346035410743c0c0100c0c0401c807040c0c8203ca003160300408250348554541d038040c4003d40c0304406c200d6a103600c041e00010251700307490568003140c1070091058040c45101c0700e200082c1904500d404100a40c6081e014001911b40001a0042c010003a07242c043d0040e00c0505858610f0307403c2c1d0800303180c2c45800300f0000268000c9601d0a1542d610000300d4036180480c01e0150400695001008288002c4501107115040c407001d4040c0a20010110005520380801c8076026850074840d6851441c1e0811080c095800c0c2074120a21307141c03082c14004210806c0001d500111442643e1000b0a0341000030f00f000020740349080001120103802c00d26141098404001030681696521982070120303030400341e8080030300c0c0401f0100c0280c00102c04000841100b100c20712140c42101c0031804164044445a4069414814107120303410103001007250714425000c00075a900040c3e1040c0c9107200740c02e4013a0404c2014403c0c21a9084 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 548774757 1250 548773507 548773517
    0xc0f190b040902120601110c01030213091b080115090b07020f03100501050306091501181b110d0c12110309270601030207030207060c0f14060f01050301020c03040302190e07 76
    0x1460501000c1880405444c01b17040224510844880742c502140246003000309013001641e41c840d500c0c0c82d801d043d00f940d2105103101d19048509081262882025054040c00d0307560400d1070380c0794040c240040c031031030071154000380e00e80d2800d0000005d901c00920110380001d05981c404408200041e00d060b030f24000f001c0c86561a00010000c2d401c1c10003050380c01800c2c61015203200c3c03001d0801d01c030505c001446286035000100420045058284e40440c6403084c200c05450620405014091300c091903401d6486445e1161403481100740d48200c0070240c8841d449a03240369900c504840c111600403000c400352441d4081044504e070a91346440000344070b180b031005501000d00218440400c0320500501550505004010700000a0f43c00b007940415240c03e81091850b81c41a406d103140d40c0da000760001000d2007000d080c01c915155000611b240710350309042d800c0d880c5a0300c0d0b4040c58242c1c01b811000d80065442444240010301d0300000b03c10000150000007022550f40c4c00d050503101605582c2200030070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 548776007 1250 548774757 548774767
    0x60b090405060a081207060e1203070905010815010e0f09010f06090504050408030f040804030807030503091e030906070303020d1d060903130b07061508011d0c0f190b040902 76
    0x20505008581d441101160b454000034981300f000790b25000310300b0008110180008003501000000d601100712111a1030032218a5020001705500c258815126103012455421001406602c5000001d103c1c0c848054185480d0b010305006440844a0600241c0d00081c3e500203c01140c807000c280f107000380a416040c808042c54800060062006908a80c2c06182450100404a103544085942103003540080c204180ea50303050000b020300440d0030081070020001019030138540e01001a43c0500001c0c0d094480c100c48411001c2c28440a01c488550700c0e40040c005114286402c81c0549003803802402c000d071070101828410341c111031401a0303000b13a00100307242d40c43c480042004440d60020801008518203e40307900c13460403040141c4909440240c00042207030400c0b80a42040071130b90001502036002c5074031007143c0d038017800b00041c0074100e500b6441c1c403002070034100040050103410b002e40f12207c0c0107049001c1c003008181303950441124806000c0001800e01c5c0e42c00c0144004d0020344001a2a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 548777257 1250 548776007 548776009
    0xa030c06020d0f0b040605180424020f040518071202130306090f11120303041101030221010812070b1609030b07020606011d0919061502030c010c030509030d0f0609060b09 75
    0x440141c2c1000e40201023402c001007084100f407402d290016041200e40034045c842448010441d0f403006061a00d02d400802c0143e00300e000803004d481070b00d60484000c202180342c078544d0702d0303940b508071401000604105050300c0c0c81c001355401806a4094000d414210139101c2c1c0311401507600c204d00803290250348a440d103060000c01003c1680010086030701d9501800c1180d02d1960300e0002420143c400e44c1c458104d86100da01a5040300c2c242d90107018081d400b08a0788400000680b424407404c2600c1c0a0070300b942400c0c14040c1c0484850a50100e0f0070700c0d40351190f282c00c078091500450715205000fa0300e803010000c540307821480c5220b091281e0040400e460007000040100500d54041c1100000b00c540c403141565403850004c0e17000c03103c82c19510b1009059240040640056404100b0300310100b1b02c00010903501000030481d0007040c6000340001010821700300d045039400c44400009400501c51580b040c5450f030809400c903044900041032542d220707100c6108546050b80f02c02140203000511002e1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 548778507 1250 548777257 548777261
    0xa0903111f0f0b010c060b012609060105060c070303030e031308100e150105012d03020406080c030402010c030c05030f04090f0b040905030301090b031501121a010501020a030c06020d0f0b04 83
    0x80100b41907000d1042c0f028580c00a03044106105004000319200d15100300141d100340c1c5905480c50542e5803a15440b146020680d03280c10091b503c60302079005010020481d0b0030a0300459665401078401042c0c1c0074130b540c030202d000b02a01c5044204500080001512610120070b208000c1c05501e4040c00c80c1d40d5402d11524221100020020140e4004181d10310740e80000b00c40c031030304503035003800c041a00e9503421410014522024440070000411a0b00300e100341681076014000341c6105031208021901d402041c0c2a00703002c2102c0080c000b4000c3c0956800180c80b074540c4915040c03040d0216410b0076203490b0803c006401c150440c80315159141000c00107004a4003d91510f040d041d036003000750308015280c0c10384030310050140720021600c0391017003950b5440c1000044c840c2e0490000d003603501d5071113041454a0004403030313003643e03004030090f0000e1141910f1003200c1c0c102c80c41600107041c83c4003140d030190b8103056540d20a0368010343c01d001d08941f00d581070094150703d0003800c0c80024884841410001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 548779757 1250 548778507 548778521
    0x2090d08070302160f06020d030203090a0569010203011409060d03020706030b03070b0d020318120d050703290a1a0304060b04020915090406090e060a0903111f 70
    0x35185c030040040000f5a0041800900c4040c58540940c0c0d941d14030041e41e280c031038407150007042c0e8402c40040c030f1540f110b6420f20040205d003003035001400a0b0820280d640100703035100800b00e623040690760b824214181d0aa000800326080c6408101c01008a03405822038209034051001c070702c502175845480f49001032215900090488400030207820399200295100104e02685007416500c2c085074842c0d507010800e44c801001c5500306c1c243d90350240030a41d400ba4000782e40424811410000c48000000c02240d292041c411403507900d030500001d41124030203000003030510301c01c0c117944105403100b1400d4036400481030000c01c05c100c01c2c04072006e070520004004550007194035204520800364000d8a2804076904682c00c07400c0803030920300d8200010028460401503580c407410540100141314103280c003500c0c41620490302000300769a2144003a080d00c50012403408142c10890016010715000e43c4041702c11406071920503e2f0b860390034011442c04007880f1034903803c070320a220502c1c0362a1040c05240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 548781007 1250 548779757 548779769
    0xd050c130513330b12010b06070303050a1e020c1e07050919020c06240906120c060d14180a2301090305070312150902090d0807030216 59
    0x851410070310800d900c80c0c03140760050041c941c265458004100310314008075000600e0307914543d501d9424099200030a025610213001e00744c83c04600020041c103104003240b046000c0c110074603040991354220000c000080c0709080b40f580c0c90b0740a800c484030646004074808624000180e6861490003528a083c503081210282d580c00510444080800070035810700f21102070768081c5054882c2842000341208584103440544d101243c141119a0000342440c00307038070b00c28016900d41044111410a2800300d081e84ca4014050501043d110704109944040912440c0c0c1540c0c00200108005640e9500491000e4034aa44446410000c5d0082c0b85031541c00200c40c6108003030584055030004c0d250250108060220002001c0102c650076a007404034420b021010000c00ca50405e42c80c1c0644960000141540040c0c2d41010400700c0110601c1100c1c07082040b41c5003c0a0149007030441c02c0a54402c0c2c40554001011282003000240e03098041c040e414825005051585860324a8800608180c0c4c004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 548782257 1250 548781007 548781011
    0x20a030b1801090c1419140d02090a090b01080129040b040504060605010311090f06210c030106200a02062101090b031501060c082503170604020a2c0d050c13 69
    0x1405551b1801c9910b81c0448500600010743c0030000000610b0104000801941140f401020050810340a5100c0c8109070312405908d103159803107486060803191440301c1219031110003980244841e003460520024140001c0011880c0042c01011809440003038404603a81c6444041c107010940c1c240c007441c1d4403500c0803041c82e07040c4132044000038641c40d00102c00c2401000700195074641c00c0d890f00c049800807c880700c1e0000c858109070613030086036802440b500000642d00d41d4410301c0328003940c0c50140c0c800c1401008040c210283e0b002c20109038400c000708600c03141c1040d0042d03030120a40016600804090382e000800368029001e00d820415004242d1110304c848400500c40907800c202c0d01b4000d02c1d00007240580302c20304401070350f00c030f5103180349941070000891145408265002d40c0700c0262103417041002e43d90f070301d6010a001c180d01440c00e5203c01301c0d24812040b164445034102004003668061100d0b64580c013003201143e61020300d9071042e103403900407206e440c003581084040e14103403c1d00c135001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 548783507 1250 548782257 548782279
    0x3050a050109090c29070309090f0605220204090606110c06070201140f07141e06010602190c090509160602070e01050d0f12020a03020c0607020a030b1801090c14 71
    0xa20303200d0300f40e2070050100d07000d00c4840c8001c04900c0c00d1111103007045d41e4902241d582d842420301500f115402d100d80c840c80d5080600b0314850200a01411044880242000c1d1072442054440241c05c00c40e034442c00b0580c0d6003032000180b50007060051034020400e035100d00600800708000c0d03500f004106000c2d94020201082041c0c0180d07844a07019100303600300c02c0b281d91101c000640030349061051250162099810f414502e11303003c000f207960400c0d14a1815965401110202f24540741ca1091041d80c4c00b50b0401c0b441c1e04040b260005221680c1d42c8a452580d8401d919001940100d507000c1d50014420380c82803044900310100019a84081c03c1d09000800c045841c0800e0000480c0050240d01c1c000c5030484a01c508000900c50040c0040342d11803964172005c944114000c0d070b00c0704001c1082e4014072803081039142d241005000c5858180e009080555241d09588031991341242c0682802018004241200041034084c03180c1119148580b1034100c2c0355181c9100b1042d0300442c420b03140d104681308a9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 548784757 1250 548783507 548783513
    0x90303010605041a07021005120906040201020c01050c0c0409080c0708071a0a0309052a01080114190807270b0a0315020708211305070509190c03050a05010909 70
    0xd803022515013424a58407060306089808060245850080d00452010344034510103401401070a100100e03140756810a0303480300d007500e60307610041e100070740940c010455243c41035100e20020110038110108940200c1110800b00d01154007040d02a1035000e0003060400162805002510040600c5401002c0090600c01a80c000050b07004924080da000007540007a0f19000350056441e0a401c8425502c1c0c5c000000900580070718680f0030b0350b840340600c1861038640c0d80603284c3ea078166000340e811407004802c40002d20081503840041322084440301800058020801c11107140a002c0d41e41c0c807216415405034401c1184480e1038034401c051750920307072102069181c2e180401c0c101c980080010714406a00d9407904001c0c46441000351544c1c7d000101c081281650801003403c1e208510b00c68071403982c0c2d051031026404900740e001055508400c00c03c10a030310340000004c2c0c0000c9407903810403502607007146140480e5446042400440d403201c01304071460450388100d5004103060b980034083c0741400e40e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 548786007 1250 548784757 548784767
    0x90c030c0d1220030a09030c061701091107050a050a03030b041b120e011119020607051909050607050c01090e07092603120f130f140c270903030106 65
    0x40040412840c0941c0c1d5000f22002e4003841041120f50043c0c0707541c0c41400b003005100340078900050710600344c0c030b500005046105144030036805054040ca555142d007450b00100c00344c0f41c100f400000c2e03203200380644400710704217004015075280715000030204a8860710700039050b92441006203100b80d280600d40c840740800c040100c4003909580c940380d4a03144550a003e4018845c02040c0e414079031a02003082c100009140c01411020591030b030003c0c408903100070480c0d47c0c45045a00400190741031008c180601c100e100c8130380751a42181007004c000342d280c00100c1c1d503e402c102c10540da82d40c800d10a41d10f81c0e51300f0640002c040c02411200e0882c030b00d00039002800220051085140403115a0034960350300482d500000070300784204050302e5a8000b08000f00c9440035041e1049043c50f05c040c004900589914002045d04552000c219010201117888540884600c24048a503902036044034070000c0e510041800d4034150320746c101e2507524402c403046000041c0014a10a1b190f0b1003040180146a045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 548787257 1250 548786007 548786033
    0x1a03010f06050702131a0424030f060b060d0b040f05160507050a05030408060403020d05071a09030912031b011802301f1b080a0603050303090c030c0d 66
    0xa400c00c20780e03d504901c086401c95040d43c100441e960b18241d2902d05880c407141c0b003464200d0003100c0c00c7c00340b40101001510240008450300e2805030036200b0800000d44a010358100c22030060f40001a0300740018041643c6520003582500040d0b0380b8040c0303288c00e280c10712178801d80c6408088100890300c0e103420800515903024400c903050040200703520f000c2100070068199503640c400d0540303407241c0d601c10301c480d07a400f8141c034100c0250140d0079402e00c215100e80192a0781c0c40c0c1015071120f00d01c03400040681800310141060049000811110105458070b1844ca140b000714240150342d182c80d24072400400d003004060000059042164928641c40074030714054140e0780442c3c026a24422130220807205d010714613000901c601c210402c0d640c05440115641200502d1003c01c140600c05162117101100c2c1c0d161102084600ba0744854203c541c4141e1826134415100200019080e80701e0b120b0500d1900102d0345014260b001c0810701c081c034201030002d107050382002d4484460090b041e0b0740e0002c501d099 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 548788507 1250 548787257 548787269
    0x230a0509090c030714031e030f0a090503010c0f08060a0b0405040e0319050d05130209041412070c0f0906030510090f15090c06090b0d09050c060309071a03010f 70
    0x1100d008140075890502001110300e50003801c540c9040d684120b903000001e0701c2c0004034424080c54152130200001ea980031903014114401951801c50300c600c0700f40c01604000c1300082081a048000b04460720240305280710429240c5504e0180c0380c0d1050000d00904000b44240e004003240350080001d01c010000b540c0a03280704aa003c07801542e8075414034034500810003070040342510302c1c81c100746064110009000c60710000d0070130702c02661088042281030048440007500030400c1c00002e4046065414031408905401042d910f1480c000d10707900e100340c1c00c002020f49019204881c200000c0c03405400b0800140301ca03100500415255845d125242c4a00c000003c2d070042e00e4140e403030704000068549610741940900084c2c402c24485c102a4010000c851040750510220400402c407280100402e5080b20098240a450503240e0007080700600a40102103440d131040f01e5000c4601d5031001c1c0a10301ca42121070082c1660b51802548a206411450307060201c0c03081080140314880c01c540100c025910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 548789757 1250 548788507 548788519
    0xb0c0d030f020c1501090b01021c050711131a120d0c0f0b01030b06040c020a050d0f0c021e0a06030b060d240e0106030c08130209040f1203020301230a05 67
    0x5404201d1101038400d402c0182d181d801001243c1d09030140780c015290694110701c90030018a82208016661359007a19070316041d4100311102d0a0100c0c0c8103000622502c3d1080306110300100842c804103184001c10382620030200d0704c0311420138a174841601c03c0c0080040417550b90003100c2c0501c20301d03901c40302c2241591302001041e500120501401c440780340c080541c00000c0700c5066035a030030020107141003a55090b1189007031400103000c051000030390309e03c0c03030b5040005042c00300060031081c1d8400b88044844420301a400502c480540e641415074020600c044a0b91346010b4254401c11442030242e810440038180340403031844040d11000d055900d0742d00b103620b0000c0d4183c811001500383d484000074000c510a40303017401003240c04070500341d24121216514284031101c98104240c40860382100d0b02000d07248010045800361805006103500103000302103810009606441e1800c81441204072000440d80000c0104001d20445408025000d2102c000510400c8070000280c1500050f00c02c030b40c4550 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 548791007 1250 548789757 548789771
    0x411040914030a0f090b030f01171207060203090106050114030109020306041b020f01060b361215010b0f09010305040501020408010e1605040b0a09090503071205130b0c0d03 76
    0x21800c0d0721a41981c1c068442200d44030400c0c034200030030354900d41c07003080002503011800040b50707500c1d48203590240111164485003070382003c2459a41400403020f00d1520701c201d9190000038100c400003403040034080c0c4400f5070b403440d004070401d0964075070f40c0c000c90410010030081c5030121098000e80b410745032900f001595a8885400003809000c900301c55412846814110b0741c001500043c0143d224900c04000f80017182d540c1c4250303c4c10307014100c100c140422060380380c40300d84104600c04d0311040c0f008008030005211003101041718022803280f00786140e0310680c091488035900000f814018820344907402c1c6820104601440c8500420001505240c5c803103012608004e400e40581b4054040d42000704000c9414184041d95407100d01da46a00c41c40c405907002c210360800d40140b4105541c0036140791400d502c2c1c0460b2000a210300881920540014003061000412031008154800540d6503010b440d0700705001ba00983d4055580489059242044400320485021401d100138000a0070300288072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 548792257 1250 548791007 548791013
    0x206040b07030b1008040b100515090d08040b0a020c060304082a12040e1005010e0d0f021507060e0d091a040e07030603050f0105040f0206090f150d1404110409 70
    0x20b4a00e01c0f0415038007482c28484802115808040244a6409110800440d440d23200c011408460203015a9401622080d40400050720650040c00d0b81038028044002c100b9040c0c503014402d03001604250210080021024009907040040040b8028111805407035400d007551086450b1041400650417480594169100540201c24600480d03440e031080c2e4620b00c4040b0300e58007159119000300001c4000c040c000c10241c055001c40c0e60192001a120141c0c0400c0090030001d0481180303004488141680000c900107031165400c05460f4181a0b41d900c3d107603452890701000b581c000c6048200d03150301c05044401120781c040940320881d0000c0001c034a0100c0b219100a0051140b6003107141c445d82c3c02000e0144441e41070340003000301c038000d01c20b80309001c2c0d07000b145030f00341c030800c4e5005003100120000913005840c240d801017101e008001c0c5142c0c1c402040070007148901c0c0700140240440c0d00d0105400303e02c84e64600502032040a6a444520146055078550024201011209018560b110301030020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 548793507 1250 548792257 548792261
    0x1b0d2606040e0f0607020303090d092306040b0a05181221090303070f0209090313060810080f1f020703140c070806100807150c030c03030623030d020c010206040b0703 73
    0x65003c0c0c4419102e0a14118074080e507268070940d195402445580c1074085400d228003030610a440b102c41f0340780c040004924400f040540e511509a0340200c0c1084001002c2b915070340249400380458580380d4449030042602c2c0ca50b140380565450090002421100302c411010512145442d608000c80c208143c8091064065004410201e5090701c40040c4520610142c0000d050f40f40e4400c40f0141c60b140d81d00304071552030740078600052980031403080301481030a005002655011641d00c1c03204820350307603c1001c6c51610749210b400b68015081500710510140ba440e40ca00c8807034444450a524042c02940c00801524055207400110140802c601465a200740078403401004100115403440c00c101d21348025400d4035100700205442801d40014016030b00c0020100c000c0c001c0d031a2030380114829102900c51560b1f0034030450030550740307500205003ea00c020b2a102e111190b54084201280d00400789450400c00b0102c003402d66010140c0e260481c0c0e070000304158840d612990807042500d401e42d0a0b40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 548794757 1250 548793507 548793523
    0x10c0309050a03050715030b031515040c050a02101104120f0803041a3d03080301080c010219020a17030d140609070e030c0d03051b0d2606040e 63
    0x140c0b101c004100001800710000300641903c140ca59400721800c0b8600d0141c0440384041940e9805070001413001c040d40d2281c4848550182e4580012806d40c1842000038003181d18415a80e0b012640114940003510740c100003000884a074031070f0810940000740d03141100307030040d8072074076070400301d00c40c40d40c2e0400003a050070091007680801c0894983c2440e16090039020140b1600960348008040000c03810030900040b0f00c003210700501e0205000d10484c0304900d080c0076038084000540c580900000c00603001c500114000c0c00060003402400703903070304002801c11158a0a80c52040c120031000e001507aa5000414106d628550b40c1c48509030107480310038110300429513590059403404d0345c4021b54240d1294003a202c0c0004592083e419550940b041d0740380d5060b62021501035000d01031900302400c0c448503040b1480d0080c00c045041030640040585002c1c803901c001000340d04407042c0c075003840e50410380d4840b0b0404010309960301030b0040745c5e6403041c456006140611980d01d0341c5c0c10461b200800e1101c60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 548796007 1250 548794757 548794759
    0x90315110d1a0108130c1202010509212b03021c020d0207021507170a051209071e0b07031d1305040507051c02060d110406020f10050105030c010c030905 67
    0x80805609140320b400e03207140000300e03640451010400110144000c01d00c000e401a40401143e00e014104010011105101d03a02241844010000000300d561040355205c0c0d1036026460303403440700501500040c2003000c0e038800c42070168041c808140c19044240c80c0314904e4000c520b401a01e42103c8642130588101d15221900c07a075200068007100145680c0003041c01c3c03070090750320385056091540b03045024450319030043d00004d001c14403810b0180c0900010300389181e40340303409400c241022641c16089203044d140c0380b0140d4884001049124800c80c0081000700c1d0b076000c01801c040c03400541310030314456400014200040c0015003c5070a0200d103c8600100c000380905030362300c0b164419400141820b0304c007910584034602000919103410412080d2f00f400309801201c0380d043c107500740855904040034100c2200e450b844100d00e076020400c084c000a0410358002c0107001c0c42e00e1103150400c41d0b000d00c1611814140030051085490024140c1c090070390a04e400c07681000981030440d0403010719008030f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 548797257 1250 548796007 548796011
    0xa020d0605040302073f0503190e03070902030115080103261b0609010e0f0705060c0c030a05030703081e070807030e0313031415040b090111030c03070f090315110d 72
    0x10300c128084c5500081011004040340e1100e150b0701e01c03007800600751b00c000c0003401c0754400c0044440d000b16000c03c0e040c1000c910305211b081121a04006410300310a904810221607002c0300400131001c504032100c0f0b40b02e07045d06041500e5410360310745554410041e5a1509030081895094510b01c560780300301d0f4182004000400c99903d80301c00026100d01064803242074640c00c2c02c0b59103000e01804540d00000b00711403030040c602c4604d86000d119541e0481c03411400c035070141101100064505108418035036205501442d81c0d403a01e86409001c2080103071440ca00c80c80700030340b00741e04012240d20517a00160103003010400d640c1c503403000701c01600c2c0b4480481c52600000c1603401086540b00c081600b980d1040d41803558004915211941d582c0c0d010401416450a00c000708002c04e1100b4070755600100c60000116410500041000300c5500940792042e000b00000300704210b040d8445000da010030360030302c0d140c09024919291210060f0148400c0110343d1382d2001a440032029030030482c3e0401a8090342 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 548798507 1250 548797257 548797289
    0xb0f060c030d090f120306060815010309020d080306091509040807080c070b0d140f060f01021006060c0209010504090b06280b0a020c0603010807120c05042901020a020d060504030207 80
    0x4c0341102d40c0c2046001c54181d86005034003078100b0700030b004e07210649116580d806415641c0c401c1d86840601002c001c141410b9032413404001580b50201000307401400b0302c1040381c3d03034206407081c81103031413000f000301c4809e40002c102d4030550394402c41d9031034001d6000003619032542c1e001c2c1800900d41c8070380c0103800320500c128000004c00c01d12000c0035144119100004000780d003071036003541c4500c1c0021500c000a000306080001c2031403409c0d600a000d407074810b10440743c3d0300c03012904001c12965160032a102140301d044a0381c0452900c008680c1c0900420342d402e002c4c4d4080f583d103c484102015001500c40ca061042c00301d81000d02a00b25088038902500c10002e031540c45554040c00d900042d0113100500496020105c0c0707050003400c582c1201c250000500402c0e280c6080403400c038182e802d040301e41120084000400c0c0d0780300d0041000a2414030401600c1180c0b04100203804151103520505541022840318003581d146000380071503541002d0085001e5449107812420401180c0190b000c0d40e03da010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 548799757 1250 548798507 548798513
    0x60801020a0e040c050c1f14070504080c0616030e1203070605060301050906040807060c020129090912071b1205030a08100e24120f0c040b0f060c030d09 67
    0x10b90580b440151000c1180ca0a86041242d403480741240d200300356030226040481001d296020392002d110300090015003460b4120300503001640c01e503011000108041004c0c0000301c0148107440403c00f08984107072502c8048822503070008902c410280511100c43c1c6051026155001d203001c80303003441c4090702c0c2d4402c4203142c004000d02050340c00c0b80c001d6103400002034a48400103000c0d8001c58100d84114140440d542d500d80c041e10b0001c00010841d52555890104039020409040d420408241c00388400c0030342c0b0341880304c1c905004020050035480003502c018510410b070110f81d0382c940c000111500800b4207504018080c01d590740241c11446115400c1d03c01e0060100141c00c204807175a4036460907450343d9030040c1a4010b180a900c1c2410141c1021034848411b40300d5a0a0b002a0428100400e014550000311401ca0301c94a02ca0150071406180c1ca03121000d201810142c44100c904000107200400450004030031816814002d02000503a02d5002d4410420783c0e40f6540a09030901004080b0301e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 548801007 1250 548799757 548799767
    0xb03180f0703060b030a0305120a06030c0e01150315060c03020c030d0306081905101a0907110c0102030c030a180e04050a0201080703021c050c0f072123070303060801020a 75
    0x11006a0f252403429405640d5072401180e114141030301903541c94140743c040b61403030f80e004201030314004405590307400000024401c007141400070213010134900d40c0343d8980384208101501c01d2179050b080624080203101a00c8400c0454030564a181c03601112030101303881c05910307241000043d81e03410320a6079250480381d075258115600742e584d42d100313403060005140346500c040070308a0f0740100a600884840c2c00341c08602d92082d44840d0031606e03108814080d00c03001c1288507d0584528001440c03441507054181c5007003280d180008028401076140840c01440c040c0c41707000d50070b000350402c61881020b2100d10406c50101d4041c21700b95080036400d05062070110b60315054560102e011030504c01c0010300c0a8028402c6d5140c510320503200303200320391000b411880105401000444000d4080c045445030052403409031601500c5a1100440c0440d440450b20400341d4110700c50041091035440e400f080401000388000318107806003c81d8481e24540b40980240c600c0790000310309507101140789500c1961007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 548802257 1250 548801007 548801009
    0x80c03030601020c060406020330090a03020d0e090f09010209120a02180601050706051008100609140c07080306240d0f182004020a0903050c010206100b03180f07 71
    0xd8080b205044c41c0007007400414000c80c460703030000d80c1050065080802e6152580d280f13400b0441038100e15240c8404152041c40810781e54036805600c101c1121041680410009628030340d1814021041c043d001d001480707041008002011180c03a030700210310110703000d405031409050005d28151278664030908035a920605084245d208080c111641c036001100507200718090300040c2d44075403400116445c1d61002c0c00c03024202d10401c01515000180071401405a0580c26940c403401007417540c500032000c0180c500e000d41084140c0080018040306c01d090800311582c0a0303010400c55240ea07910000100d101001e4401e03a07680b200804070140500080c0f4004000103900d1007010856485003da0740303002c50702c4607602d11100c080c0808410002c10400d0031900c44040300315421704495200d02020030103a0700600f20840c01b03d40440824410840240b2049882c224284010401450506d204074000952485420404c840003c045038a0152501b030300184c0d0a06c64084903034000703035145495603885030307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 548803507 1250 548802257 548802259
    0x2030106051c1a072a06150807150519020c0d0b1e06010e1c0f060606141204021c0f140706051e090d0c06050702041b0c03140403080c030306 62
    0x1505801042c05401411a00401551740c07054403038030450020110749450807507051100340700c417090140000c1d6103001d050f082d4094019034001140c9000c80c260b141494130b801226071620101c81e18103055521006558996400c80301e110003860810f001a400d25602ca0002d60b000401490384209002d490500c45016000600f0031600c0b20200103403207140d0b0101560010300040450481c03541600c2e06a1142a40ba83e00320f21030580e5140c260b940060107216130a003103411a8840008201242e0442d0131141c010803140009441c01d03029952a800da207100400c001c0c031072150458006400403c041c0c0d10601180e0002600d00202c0d01800e00a8942c030030314030a00d946206008010070003d1290b025120311244582041401c190010640c1040d90002040a500b00005c0d00081010455080f0a0303801006691605035462031103006110940c0c0190803800406a00301c8640d070406a404102c1029550b054030388490f40c000144c19100d420300c2a98006049000c000c512030440c0c540100045004d100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 548804757 1250 548803507 548803523
    0x90a080d0e010f0305070207090225050d1814040c030603020306150a1403030706020a140f04030506060103021801080702011b0810080f030f0c01150b0a0e06040f1202030106051c 78
    0xc40000c03805d03290103da82c0310040c0c10452040110b820750350050130112441c0006010541c04031500a8610001c5183c00e03901540140c0410759081e40044d071041240545141003545942042c0d109245080130482090259541d14400f0000502c40d5002c040034550041c1680c9160425400c02d07007103480003e113654440d0209a03000038040c9154000c10042203400703000b9604002ca9034035400001e40240c11200e0512105840c030440c4154403200030206040d024038040d480f1811030030810b14148000b00b2141c18140b0400c9a0b543c11030404141a003403138024070303040c00c0603502c2c0102240540884510b590a2800954401d440e0319000103200d845000d50150b40014030303540780754040e9140e0350921054400c0c0c00800c002c01000320304c00010045c5014900c008500c506005112075041403a0f0b5214445660001c100f6842c1c20303038807000700071600d0030032900340381450704000c544015200144074910350816010036130400c5490030341081006000c010002502c0710754990403815000044901211820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 548806007 1250 548804757 548804777
    0x1050c0a1404050a06120b0f012a0f050d090609120b070212041d0a11091c02030d0503060418030e011206031a010e130f080309150106030b18061302090a080d0e01 71
    0xc1402c045030194a2014ac0d130380541410b816010760884401600c481031031804001c03143c008076a50000e0488102d2052008200d06003d00c5801800e429050300000208016200d00b00b0072498a0880050b00701c1e0003e5a41c10a5140c1c10b80591411340d410100c040400404200021050054021014103110310040407009a0b03600140d54202c40030400e00c0d280d044810710585000303041100c0e907603000c03541c1060701010000c484e80000c0d16060307004041200041d0f00000b04020360509000d00c401081841c100040041420340d009088038001001c03131410040c1d03500d2901017064072034100900840d040b031034000b00c3c401903652251415909020b0442454810000302c1c0e80340224520f20320240345c01000140302042c1996503584113900c081c0000741c0c4c6201e202004071540407a200e1a9000b003800f5200040c4c0c5101000601030a00403440e00041a4101c4904200c21500c0b904000b80803807065050050b59550004009150b0082c144c1200240307204040e0101d6983d6044000d148410000343c84e084ca0f14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 548807257 1250 548806007 548806009
    0x170d0815150c0c181303110307050604020a0506030f01031502040504020f0703032405011409060c0c09071d09090f240a020702010f12021905030402090901050c0a1404050a06120b 78
    0xd81030185000c009504c140091051003400350010701c2c0510a10b8401d40000e50308103014990380001c2800e9480390400c1d0240811460083d02c0c500041c203040d1125804c5140c00c2d4000c2041000511020700b2461600482241d03001c0f699040310f001d4500180115210000010030140b40c0d000000304401003450080980c01c800c0d00e00140032240d500b40c4240c401605d061a00455050056954200c0041014800100240e80e00805090860b6952000304118051442004240303503000d04001c0900c0441b0040100b40e50b1200044408002c0a84040029482d401320f611f10301044081540028058804408020300c0342c1c4800304011001c0c3d00074880d01c1d845450310741d0100e12540e80e0080c08203c0784910207042c8ae005003214005012540030041c14507440415403502001e43d0300150000071303000020401146800c1510b50380101c100d800030410307482c00c0b00700c120704c9102d440d40e180c0501c5100c4c4e40c04540c1110f00f00495018110192454410030340e07455020b010900d8a01c1c040c45040c0c02c101ca0349040b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 548808507 1250 548807257 548807269
    0x90b0919061802040f05041104020306181801020f0a08070905010519110f030a140301030f1e05010f0608010b040507080a0905100504120801170d0815150c0c 69
    0x81042840080d8100340380654680c0d005080160103103200701c0400682030003503503c40c40b5000721900c2058000c501440c292410b5844003421210701c0c5c1c4218414418840140c660500c4042c5030040407001786102c0c3c4508031004140d8002070b01e01f01c4250f00025004907400407285c0a0107145215807500156600d400c0b005840710085405410f0000d041480b0880095200030071010001500e801c0501d880b00e95400c3e003504210b10460040055440081d01d4030006510942030100061102c00140c115410f56442d0003824001440180440341c2007008001089039070901c0f084901d51107002000400c200c4501400a84240d12890185504e410504080760800f40900361043d80310b0f82d42c0c2c0c11940c3c0c54050f0200181450355054940b44034000502200315141c0c03140074055030082010602840e81d546000b00b0143e07050b04103007c0e01c001c08003040a00c040c00101c02e0240c070502d080c110107a503681c01640b926030070840b401c0d61780140c0e091a460a1101c42c01c000381841c84030582070380c901c8801c40e07041c851 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 548809757 1250 548808507 548808523
    0xc020c190617130c080102032d070e03100608070609060c0b0601300204050906032802120a0317010b0a0c02062b05090105100503060f2701090b09 64
    0x400b04203003450040380e040002d048140e1100500040025510598035440c11541d65030b00891466036002042c04402d021080070000b1108130001c1d081000303201d07101703c003415050192a46c030500000310181740a0b03907400d03c0580e44200c50700301c04100f00e17030f600d81c021585c0f0f001354400c520218601590100340d0610500341644241d400500c0c9060329207415004481e8501c458004907a4051411503440f00143c00a0010065820800002d0780b2103060100f080749a54010b802d2501c203034043c90a0134601003592007141e18402e01140303010f05c2c210b594000704081c0d20500101405034080c2e89400c1d010182c014400300d240c602c0c00c01006140380e80700c10046445210300c40c820008104100811001442c1001c010140084001210b84100d00c55a11401041031207612041e82c0f59120001c020800e2424850254406000c4200041c0b441c9040e0129465500c050030042e00d00d262440021225646c15204081e4122a01103480700c03140d01000c05402441000c0d0102d40110408011429110380059814 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 548811007 1250 548809757 548809769
    0xc09030c01140903010f060e0c0a020604030c0c03020d0f06050a0e1b030a0b0711010f200c01061a0a09050d23010b031902120601030b1512010c020c19 66
    0x1150401080e001550041d126851a800d100010040402180c0b0280900e161010400c00003040e03080c1040d1562259803401400215502030900041c0181e5900191035170b0003a4140c106103c001442c4c2c2008a080c441d40d420281d049001c510f4003000700a90040308a18950190408004589410003c01c060340c440100004103580206441c161040c00da03240180c40910003411a103055035a9580d20088000c110b84140204240302190008a00280940e034100da8072b01d417080084205110360042915004610700e01403140c0810500c00d546825070280c8041c2071440c100781c1502d40144105201603000044140005640090015440c101080300000190380a0b00c403401c260640880a00d0309100105c15841a64035441020555101440070250071100509004d40090340c0e4014005402020003002042d60700000040000c104880d038030641021490034035051420654000811a9032111940c007029468840281491a00015201400711080d5070580700407440c1e40c1340b186190780f580301e00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 548812257 1250 548811007 548811013
    0xa020405030d0f12140c161e0506010f0305060c0703120e0705040b090f0610091a04260d0509030a1704030b130f06150e13170a050403060b03070b0d0c080c0903 70
    0x80340c0000704501c003414030800b010366140701f0041d042d195903042d1040e01416030703e52007540000500740b02c0305002c00d50141c02800b202c03102e640d00e155502c542d280001045540f000e90081201c404052103a8500001d06c2c6e1445400c2c414000f032540000d490b2002403040720701c5145861080a45428440e002c60700c2240f0440c0031820320340d100803d02c07a20420305c00100b810001c3d2840003084111807003010340081245c00840d80c4e190350410302900301c030340f040d1902c001580039410304140d03a4000c0002c004403800302c1450300544580145002c28942003420030010480110321212003030005480c1d01a00803240a17003902e90306a11580e4038101c0326080c0101c0544203000101a40300030030403a0700140c080601e094100e290149d036407540d80d041644c040c0e90788040411a01814402e00040c06040c0c07088818442d40a0300d084240321000d000e81c482e5200c0200b200342c880a0440c044e83e0203204120040800901155803080d03541c5142000784018881d45001c52a4140403803030b400e05400594001c2803001d402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 548813507 1250 548812257 548812261
    0x2003120708240d080408030a03090201030f090b0601210c02010504021908030f0c030708040b030a06090605030d080c13030c080f070302130e0c030d05180619080a020405030d0f1214 79
    0x5211101c070b25a00c1c165100d820170030000495400c00c2000b00a10149584e0000c1d0007851480010140d03000c07810704041e032604000000002c21031001402e84c01c0002400c2c0008040c640d2008120880780741c5810017030301817800b40711080e965010b4103d10b104903c225490458000807140c0d80f441040d17a401003500c0395006002103441006108000c142c05e00c40d03401260b00b0400710b503031005e40950282d044006d0a61000c01888034400c40c41c081c840142c612070300d05100c2c2e2414a0302180e03030b0709100b04900040158090100781482080821144124410b0200d41c0e551074590070090910300c0503205150385031185001400f808100030400c841540e0740240184e074034004444090000e09a0381d0f8248200703000780000d0b000c055404101406288060b504c0703181c4c640084d081d100c1c54201841003810701443e020414020503005d41003201d041e19580d42819001504c562003a04001d0290b504600c1d018810803003001011170700a030301c0a20303181c041d580c0c41300b200309030b07140d02c4055030f040c52a0024940030000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 548814757 1250 548813507 548813509
    0x20a14060f0601080c0d02070f0b06150306040b0103021b0d020d0e0616020316061805030c181e100f05040c02070e060103110301090221070807200312070824 69
    0x1385154002510010541c03c01c4020860201240d1000c2421180c4607035144040040040b5810b0042d1321150440365a114880c080002e8802884010042c9100d02c0c1e45440e00011680694182c41059200c2a600d920044c82c40e00d000d903660102c02080c0d4090310500c0c42d000c4805104030085022000d002e0081420032440c41c000d107200010b4140100e03418000c581106c00c030401081b0380f52000300810340d44d074600010b0190140500140f1a0002802508189404080e9461368100800d00914540554186641c0c040b56000044104601d103004e2006500501c0000005203484200740d0b82d0000c1c0f4241042d0f5110100011591010010800341c0c2020b1010004642c0c81940c055108030103041c0801c3c0a0b102c40050401c41c1e109030002c04440c0c4d0301003140c04001c4040607505400102c207100e80b132401d0800c1007002c0c04040004103403a040192100f4040302001100420502315000c0004482d00c860b6400807040b10040101c0704803001812101c000351411701132003425020310b040610301440404a180c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 548816007 1250 548814757 548814767
    0x1060e0603272a09130212030d0222050d0b0703020d0603060f0608010203251211070201030b030c10050c011d0a06060605031b1b03030106020a14060f0601 68
    0x1003609480c20240e10007255200c0c01c80000342c0324150a80041d0044a190300c00000d4100041407007072180081a080c0c035003403502d411031201d821003074080090641c41c50178800100b00585024000b443c0f40008280341036191410f40261801c0142c48140740b442105111010303250710600c1c8155640483e8a501080c08180c224102d00c0c0c02848624000d03140090700748402090700d000343e01c05c56542c1d0707960140c000700d030000e44540c80180005034000d41c954100b0441c800c03c544003400d80c0c6040200400d0000b400030740196913101c481c009040052002c0000c404445030103800c4044103901090905440307080e0b5285c0030481e10304140000702503000019205000f00c405800035014401150750300d51001d23054034041d155409400114100403c1e240030a440c085080d110325134400011b01609005000b10302c08010740e803640456900c291280c0f180510720310306049095414903412140000170010502c80c0e40032681480d5103001c1d00c1380d48a021540c28640750341e03440c02c481160b0352140c0140490000d600c11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 548817257 1250 548816007 548816011
    0x60b120d031a010c0b1f0602070e0f0c090114070203011103061c08250c080a03020d0509030a020904050120030907060c050601140a03060c2114150a0305030d06140901060e0603 77
    0x3a100c0701c42e9140d4006c0c2c468225a4440d0468805640315800030448011480341d40b55015803040c46800107400c0c58141421a0300400035114140810180d012a07091800020b41d429980c004000307120607030382002814000d600c25108907000304070642039102a001d41c41210010282d0041e02280b81c445400600041d6100c05510704020614104529001c1503110010070081c04880c00070782551140b9280c00382c03034114801028418001d003071008080703030361b0082801507807035030107444240742d55840c2e14005005048503102c048a03889803002c600341c146038600242d4405c444410841c1c003425201c8030309442181c04424006c01d154031070340043c0f2075004442040820218080c2100c42c100b903c82da11501078450310404800002e178141ba0781200b82c6a9080200403401d241d100810407500404080b01c030502004080d40340264003c40c01150302c3d150b4190680095800406680d01c5102031481c131405400c051041880340c290480e103440d054500b8140c0b0390704072545900c5502010102005102e81c1d5000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 548818507 1250 548817257 548817271
    0x50c040f060f0e1e07170c04180903020c150702040b15030a2406081519030b2a0d0908092709070f12060b120d031a010c0b 54
    0x84900000d5040c82060355003000c0c0060b5440c1203118a490f00304c0c00000130f014440e030310010700c0c0c880c14480c0064204000090040c0100801441659810440342007071141c1da004102e04200e591701071380755110740c0c0d0140f200036100c0c0d409c3d1110800d0400c10020008001000c00001d17440c1000300c440145041c1d400341d45101009080f04100440c3d1284c1d04200c0d400846c1c1c041071441e211300c140403e00c900301701001c4481000c1c21420702900c4c02c012005000c400e0003401c0174510080e4480000090383e5a025060300e0101c0c08891f00d44154aa113003141203d0070039103042c00e20b4400c0e441e4028a054118108003810305074011400e042018004420002e040156015100301750208600042a1241d400038000c1914030b044805c01c41c00c03840340310201460014001400ca411000e0140451030703440303500c0e4044401030f03000ca0080520605240000b4244046c54031342c030010740d042020342140c0118010010107095101081510704031000000101c0141400c5400507080c002204001920080c0392f94019503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 548819757 1250 548818507 548818511
    0x604180b030304030c08010b060301060c021c02060f0a02100e03070327031202100504052a040c0f121103011a13030302100e0109050c01050703020f19020a080a050c040f 74
    0x22001182c1164025007044e00d10301526001840707504000d004091440c10180c072118174543c50200020501c2c03410380c60083c1300b00d950107414034880503407448224009400918055852408128440d107a5010400203800360003076080c101000803ca07c074420f2913a104034082c6180c06000c1d078085805089803152140c124840c50340c124001850342c138000e0301843c41000d410750042801e40300a03241150500882c5280f40c200410880024404614420015580550981d201c80d46d4290000c840400480341c40e0454079156400852030f5001c56501da80c00459220301c5e9001c1c801c0303540c643c16107c1c1c041c8072545404003040100b1011900701802803040e090503040c0d80c1086c15074482112800c034a41d1041c2c0060f80310a662807005002031103079201449205c00200700b00720040d952503859903d0700034a181800303001714112080c10b0080c0801442901803400703841d58003050685040f4441500942680140b155410100f03110100144099030541c0000082100400311010040500074030105120066 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 548821007 1250 548819757 548819771
    0x12070c090e0309040e0a170c0a0b0901050411270c0903010e07030c05120601030b07021513030e0405091515040908070b0a09030c1b030f0f0212010506060418 69
    0x314922550180d00d0110000d140d48000c01010002541c0c02c881c00509903030441201d0780005400c00c00d0130518820760b00292900c400c0d000c44c8980c14024190409010000500b0401048034019400684686d1007010040c82c00c0c110b0906120882c52140d060f141e9030301c205110004005181009607510401c040f002c1c034608610000402e01b501c800010041d01a444000184200124104094060507083c0c4540b01e05080d0541011340d6040e0610028080010880100e99098400e000d00d084201d955103c0c607181d820444840da0206089100c16400103e8400c0c15880070700d041e001d0a030203407042a000f003d11801210b034124100c0b20141980700c45a400c40c00e1580c00d0380341c070700480d040c1c50b000d00d10b22070701c07500c250501c0f16840d803000b8094a0094038044000d0002070b0003003c1c044c42a9002941e1301c141c9010f05030091110340c6182c0018065106100300f0390301700b200300842510030b20700c02d4801e0007200d0036940100303003602d1b019607140c0c4e40804c0a01081c02580b42d0118400920310b03c4140209100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 548822257 1250 548821007 548821019
    0x504181401110f0d3e16060b0301020904110403030e09070f0e010e03060c1b03070b0f04030c0206031302040c03060f0b0a090e150a060e0d02010804050a02130b010306080f12070c 78
    0x24450540c041c0e0b1742c0c0070200e14000c2070b1041303034500c078440c00790000000c07407610ba08120403559240a401000b00385990301c90090ba041c0d14250b064402550b8060400c0043e2040860600103a41207444103c0c006040550320303820f01d0400c800e1160183e0420344407a40600da94040549400207040e42d803504010000040c04403907681041400c0c080c114007580030740d031801d184584140c076a07450f00c0d11080380da1003001400d0008800000566100d200180d03000fa494481c0e00c5e0450704010b0114000e9400440030044c0b0103290414008183c0c01442140c0801440c00c1a05080d000c2d1480c6109036040c0c08003480041109054120040900c88910b291000b58a91244802c6003418420f0729403003603c440b0303800650005d041410144d00a8005400c02050394002140050342003080c81d04000d04000720b14000c0b070100300c002c00c0080302280d401040c11078117203481c2011400400c00113a03c3c9000034146440051074042c0490610a161001d0024042a100742c504c80a03481e40500780440c3c010201e03010014074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 548823507 1250 548822257 548822291
    0xe09070302120f1509040b0705030c04031b1409060a060e012d08070822030c02030f0606091303170402060702281401020d11070504181401110f0d 64
    0x2090f1000c0202038440e0400410341c0440400e2006010700440c0407005000118113554145030b404102498002d0b600e54942081118a01441c0d000400310b5030310402c0240340341c99002603c0140c83d92507034080f081e00d00600801200100590300c0390f4018400440138009035214052006202d10107050060f581485c10a4206a402001d002710700c0c841c03001d0617110041d23584000c0f0329070030006500d820413080c1029500580c00001710000302c80b03107800c7e0113240c4040600030321000e010190000d00350b0b0352410341150443d0321944100da0003445417541c0b40c0010b20100410308801c558a03010740c0d0f02d40c402003030380f090800c145102601c2030f039010750180003c4c40142e5513805645000540c0c0381e0000719011414211050041c01034101d00e07200f18450105120701e036800246d510240c42c6ea45007409090001d80001c0307040840c81d0b0002c41c4c026092107540d2080d46548180d119031284141d460041d8030b0183e1812500700e40d07a049101c40e4140c02044882492100600a081000b0b504407000030b5000c5007484c0c22071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 548824757 1250 548823507 548823511
    0xd021212040e0405060702120a27180506060a0c0b1b042c1e04061b050403020f060c0a020d050f010515010f2307060f0c0215070e010e0907030212 64
    0x7a015000e18100020003c05000ba19009821b500040100d03c901504501d90b40c0105032078402001030803417980842d481d890aa442140a0141c90000281c1e1615810040da41464190411803810b00010a00c207013000011141144c03182c0d51900c0c5098015907900407030000161440300c140010000c141030f10140d0310014130080c03078050b142c04020440d180150444400c00c04043c0c0032801154200812070062088202c09003c04031420609581c4034070300b0b03a00501005480300d0125444224441e85103422200a1081d41d000301d4096207160903100801249115040e8440394036000054000010b040003140e114603584075400362415411035134030407401c40f10308640d0444a0040f00d900c960301960040842603055680d4a0103c03035084101c040d100405085520054220070005150018014658000440c405041a00307210344c0030103040080d070301d038041d01d0001c500c5c1c2c01c640042224a4041e94400d480f9440607165060140d032407908101d42c201c0000d01c60700a041e0208009042200d0303000b4018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 548826007 1250 548824757 548824769
    0x10603110f0c0c010216030506070c020103020c010e0705010e0402180411040314331605070501150504140f041b09020703090e01090608280206040f03060b0607020d02121204 76
    0x1040c2c0c5096140024601b06a410b200142e81c00d00a6040c40803482c0450b000d9440440c030705100000001c03601c0102d00900c640030002d0681c0d440c24440001e108008103011049803426603d003111071141108200032445480300710711080206812000540c10140c200b00014909103034240d050607641d4503401c00c1e240c540038040d1074942104250090800c04002140c40009101c01006aa80c8400403401102d00020b40304011880301c0b14040440d65208200f100c4440d5444402401a8107808282c0381e4420414000c06220b542000e20f02824151500da010b4072480c0002aa000030b070302c0b6600c075040e50212500a44552645400000c11034441074002048814882c2da90032104c5807030034a0b030060428040c0c1203405c9403424035200300700c1e0890025810102491320701a01543d4140d0446010840c010081c0003904032101280000302250302c090244203e81c0511020300407d011502005007511070114025802145a54034030050304200400d2001c40d87d14104454403200c080f42c3c2500c0030f80103a4810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 548827257 1250 548826007 548826013
    0x103020a023f090a0f0b090f041d0604140607021b01050403080307020f120a0e011107030c08030c01230c0711032509021204080706060e2403060708010603110f0c 71
    0x1003061804c0c212503079001450303da26000000c5052400b41c0b01d003445401401849005c2d0684001001e50741d81e0f02060100c004000c06084204011800a0b1035100455040e200420541d000100c0d0f03400124540c0d106140e03640c082d015400400181542500d035001a00d810448184000b10000d51114020b501400160300244180449145018a080c22202007001c5c0b0507818010840b015410407000741402c4001d0a00d000314800038540949040c03019070010700b051014400005185002000920401101900034000c0c00f900403282c142c3c104c6488035054000c440c120010707104d00c0400d006000818410b0184070b0301006200700180c41c03d03010a01c5140a41040c004540c40a03030441614401030080340415401d000d4003010010030f0100040c00948511800140b25040024075401017002e401d403c2c6006c1043d0401d14450941c0c0c0701079141c088198298055001001c0c5000900756126141d15a92140142e00748507049028050184040820003000d00140d0f103801445409421f80311070034002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 548828507 1250 548827257 548827267
    0x1505030c120103060518150106032406030507090801020307020a0b0402011106090303010f141003090317041a010506030402090a0209010c0c0b0c1c120c050409090605090c0103020a023f 81
    0x200c401440d5a082c0c6d14000e9403049046056051150700007170b045410074200050720a942218818201019102c91030599048410105080c0d030103500c01c40c01441d5541c1c51450440d00c03100c40798201d102c20b4460102680c0080440c5c40055651524150b01a1040c07410a00d1517400310038461404c8400d40700540c440d0800b00042c01102000c0390000018882c0f04030f2902482c0321171010441c0400d02c0d204540c105a21416244103047c0641c407401d0782c1c8100b0741e4007044245030030305042455203820303540c1280085e4100000242458070109036401250020104000f54560101303080c003d5000c100b085040c41000603444003c00c485e9128040104821903005948030b80c4500c00d681404080095100c640c0d038008006079a030b80d17000d07066000c14181d5550000340000818400d0b1120700403a4014520681031164000030020786401c09030080c0605001c84403039044a60054059000d00410600164400707459031050351207c031201949422400350400140c10540e2074440845881100c41e02d02650010b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 548829757 1250 548828507 548828521
    0x18080d0f0b0109050a050d031103030c0304020a050105041809020a05061c050604060b1b120309150606270a05040203040803090c0d12050306030c040216020405101505030c1201030605 80
    0x40210300c400c00d20f002541e0a04010010301d80020038050207001d0f540c100901c4040500030354200501c0744581003180d450749804100e01180da4800c4800f280507601c0844001103e5000d0380903207003902d01c0d5030055018840e15140c0c4400a10b58094181c3e40300c1941c1000085584800700100030482c040c115454240b020032001c0070650b00003924030f41c041c82c40c01030200140c00c20f9100742c40b16010f55260002d0035a000301200e61030600c600c003090420b41000018080c012000040f8154007451190302c196840e03440f98200203641c01b40c40c00b0341c003980d6600d210041c5850045940e40c07000020041070072442d10b0300c50b00410101d03042100c00311104240002170080d441c40401c0010301100007244c0b0038800340d110b07945c1c1c41580d030b1140900c0e40601c503012010410039501401003d141c1603001c0c2045441d00c41109098611b20788407442640030324503000c040741c00c00301c2c50041c0e2015a4524a19444c002510b203204480c181e1000304000100c19040c0440a2904098140c0600075070140b500030600d814428 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 548831007 1250 548829757 548829761
    0x10b040605181c21020c19030b010e0702010c18051003020d06030c0f08120d0c1707180e10051203070c0b0910020c01080103022106010b0c01050c070503090418080d0f 73
    0x1107070042083d200b4400858410381d00180309546c1704400c1d501c0d0f0b102e4102c0c00c01c20172103041040d01b00a0800c01014008a1000513100541d4400c81d00f9a0003032001002d451f2003566282c41d00700d20640488500c1c0c02c01e01190602e80c4940e0184003031071900500c3d02ca094410703002100d00381d400446514511a80411880225280d1b400181c540c0001800304402e04195100b128410307030781075800e15911500900a11809908034218240507520800454500f847c4010042003620389000c1c0a04001a8080780740800200c139180b10700d18000e551580241000308011038082c40c00341400c0c40e80300804c040e10029503510070020050001403182c540f01c0f16032108000340200008103003000c40d44011144040c2daa409025641102d4043c0c4e2400340c0d000300028550303284c14112441144c1446040000100206035100a11404810380000c0000e62544a11010548141c00d00580f02c1c0c1d0041c0006100c3d864507900001018160001201141707400d035452060940140301c100c40d00c96615a000460441c03a8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 548832257 1250 548831007 548831033
    0xa2d03060e010803041404060506191b0f35090f010e130f06090c080108150103030c06020d0f0c08060a05090121172b0203010b040605181c 61
    0x19280c401d03981080d14503552801140300d00601610348041207401a142c60744880040c0ca0b0181583e9a6410f281c07032082500c0d86180710520010300410a10307ca1580d000c00544401a40a0316203034142d10540c90b201061141c0b075030100c007060614055803428051041e51400c15000450076542c4031380c400340801420313401801c019418098074003e17802c0e4940e43c0d03580500d000d5994140c001071480e41006640010219500038829613480c0403610413507d1b410146550403140044222031952405d6610341c01013840a10005010901654050f400600590040c00140841100005046041511440566050100400100b00c0d0601404107a041406c00b6401911003a120010654034100d52070401501e40c41e00300b40c0ca94410b00c0361340e042100c0c021000d6560340410f201c064452000e4038145207041403603136141c04801081c1034405661213940c001d0300c0c101d58001546904081c07405074107a840d90310140803008030040307104140b100c50f6185009880c40d0107104c0910b161000040c1343c01203039450a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 548833507 1250 548832257 548832269
    0x31f0329011206020a0c0c09020c160302030c060a020109020612042303090d050129090916090c1e030c02010b12030702040b18090307030f080f0105060a2d0306 70
    0x2085005211844525200c0150a0751080f00103a0302e602d404011150700180315002003200e10040e100003192100c41e000b804c003841141098a00b98464001059058103031484000e4040d000a440c107505442c000c00601140c1c3c0b194000814001410b500040795036201246090008440c0b80510080c40080d00400c41c01034501f4203445801c00b0410305241e601d000742040349200e90000503c0000b0043c0a42104801c1d0710031030078600f40d8244150401d10708101c5036aa142c02402c42d0400110761a0700010f12002010f02d40710f081c80c1c1e250401030214040e28528194009111400340e0320010300c5c006104106040400350340006000750440402401e6a200c41c076501d20522404401c40d402c0346c4080116100703194102c0b00000e064a020001c01c00c105501c100c1024110a65410401a09000f00080c18004d220303903104e1061402e40801aa007413407064440307699141c0782c44014801400d011005001c21200c1c1e05046d86500b8441c12009980ca590f01c0f01c801a5203c5080f40418454240c054600588a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 548834757 1250 548833507 548833583
    0x9060309030206041217010902070302011b05040905061c030804050105060303091813050706050306010e0108010311040b03160306060305070501260408210601080901110906031f03 79
    0x50541c90095985030050809844201c2d24011120854000c07006081170302e56545c2c03c08529a560302d0700c240207410a0b41d003a4059420046481d40c03001c25031818460380c41d0280c0b541e078140381c03c0460090040400900568011145141103010140c448402900a42c400e81e01c000d210b140910340f1900303581d00544114043c4d80140541c0d0050781c0d440c1d42054400760100f2041907075649601c64060601d10520010300517025240010540d998000001c5206501c00e0320b510404a600000440e10f200003444080c046d91440c405240c40c600e0a03800003004c41034003d04980d40c00d5003000c020306510b4105ea000702d41c0595904810000c014041c40070400030107003400c0c0341e1622114000c994511080703201d402400c00030701c41c0024003000040d50590b206000216000c10a4490824404642c0c080590f01c0d1380c0410b840d030000507007100341402042214400052400d04203000d2070700788a0b0300c2c3c1010300320307000754448400c1304000240079107a0301000b180640c0c8070318075898000d000e20805029880125000c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 548836007 1250 548834757 548834771
    0x612060504151a011112040602070f08120d0b010e060d0b090604020c19080403060603080418110f0a1205040803042306010b07020334080a02090c0714150403090603 72
    0x811520200000f003002800d043c244894643c074900e00301450040c43d413000400204001c01c8041d0300161003410740b0361040d0106212502d8091a0fa43c40e98035421440c62070384100000000c0031441c0e00202c0b070f0ba00c01030404c1d4060070b1032417001036030030303008141000e182da507035080901c0540c604085092b8020500703480071441d01c040c2c15003a42e11154034208204000c025143d40c5410401d80f10120350066800c01001c01c006038880c90882503c1e400381c03040318071035124215940c0164206101d02541c4d0000c0c2c4040c86d15208019a6048441c5c000b0100007051080402d842205c0c048580201c0d8851440358401c2c50b501d02d40352070084517401c0707815000030710140d29a10302c50a4943c00a4203038150703035024080e2030b01c4000d248000f81c40c040070100090300c4004001002d103c1140e400c0c100c80f00b01c070031549020180644940140e036840000a0000c4d51100000c800304944082d0800244400d41c0602421409e1410000702036103089054545088086a100100403c2c154084620405002e0310318050000b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 548837257 1250 548836007 548836031
    0x1020d03051506160f03180803121f180e0d050705030a0530060f030102070317060f1909050c0304080724110705010e01021c0906061206050415 63
    0x100c8040710610b401084000380340380303110070801216480c4545c07085c05803155070f2040c03800038141038448881c44031201c82251b0104583d007010064550010b070301e650110842e0b0300c1a01403118202c5286032184454080da2022a000413141801964410403110209008041c103c000d4500b01584900e01c080003800d0000500159000c81181c510074841e1410544a070450044000e11031040e56014020021100b1300034000d8580058291248808540c04000e9591030420f160a070700c902040180000d5030840c1c450400464524080c1d048000984603c450880820110391401e12210424402d00c1c01514100040f001364040c1948c4519051101815424240d450700d4050140e00002022032952403e10b014819000290408000300e4460a100c401501c040001299200c89001d484550038071803009095001402200d100f0240042100c0d00c07840fa40426a0040c04928011039189440701e03c005400060441d01075180d40c0111000920342c18030f440e20302c1d0340054030b9000038450740c2020415411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 548838507 1250 548837257 548837281
    0x108010b0a090b0f040e06061810061b0c080303010e0603030a0903030c060b060a0504050f040213150201021c06140f21010b03061f0906050d03050c150a0b01020d0305 73
    0x44440560000c6540e0f80c00d440040c00100340425415042450150703040f03050b50300010300314000e01054400c9010840d98854070b1024103021900e944c040303000a2420081148903002414182020355241c109500203659001e01115003540803c11991000c0014400d0303c01c1c9400c2150421800c400139031419400e40c0d00030782600100c2c0710203001c3c032514803600014441c040d000042c00c0c480082c03401e66100d000f04406030054000340981400f4240940310000c25041c64822119aa80d6950600861600d040607600e41c21310080c402c0021075401348060003d254030000d41903e03034402860081003050400c3c051111400c452920280305001d00709596407107440d6441741d410700000015500740800a80c00031180500343c018070341078041c419042003107a64400910003031420301503200130a00311591501941c040e00d1480c0070300799000454205840c0064020383c01071a85000c210240d400740c1d420002c103da05c0d200100c83c0880d02e580c40e201c0902c983e43c2c2c107100b0302d020034583e42003c001a060003603040c0c40e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 548839757 1250 548838507 548838509
    0xc0b04030201210b100503010f05040501180b030307061a101e2601030b0601080f0702030a1214040f05010c14040312090f090e01050c0405130903140417060108010b0a 73
    0x2e80703085010005000d0002e42c1104c1c2e907940e4098290309210080b000014440c1e4024400c4100120f50004013103024a000c0c06000e04840c1428001500607a050302850010240061f80c194184010081e0740005141030054100a4500c6840d080b000b40b408403e11406000040d910002c1020b940d045042c0510b44c0d200e8a080100c0d180b03400e04a80103031150b004075495100c0c02c2040c00960f040c00000070444e2580103640f01d404207030380319001c945480c00d10320f000078002d80f00040544c100340049540d440c498500710210b0302c0550304c0411455150210350300401001e40d4140c512546284081e070034030109006441208406292130385203007a1b9410000b026029500006107010000f20320918494030035901c01c409081001d2403c0081666014000020101c0e942244059420702000039180d500328010780c1e00302c41000d00180e0001a40502c3c0c64000d000e40c032000c405004110000b0045030b01100d0140c0701500410400c030000032a140c00a03850400140e010410f568100b80c1207000d81d85600c2c4243c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 548841007 1250 548839757 548839787
    0x1090e01113903040e0108070b04060c1b050907030504060b0a050d0b060d0b160905010c03080604020313120203070201020f1c0f02100203041a06191205150c070c0b04030201 76
    0x70100c0000a0100c00026442800c040c105103c04074001c42c003070f1510311000d8100e6414600700d41140765501900002030040703129aa010659144000c0e01052000180b10f81c400481454044910344490006d5030060095844c400041d03980c0c820001088414030038481c031008111480c905c204d28003030000f120075440610050000b0191808180340340ca95490380e80303115610001030394540c030b03100b035140000700000d503880800164081c034001030769401a5580c81880e40c00d13980c0e6511965a003418400a50310260144900701645802400400d43d042102c02d415421759010b50b64030489400028641100700d54002500d0b00961302c214000390040e0450800c5039030504200c40304100500c1c2c240c1c00d002100145005c054000020001040129034000000c2d404545015070756446010038481c42c0540b01941170780081c000c440a000c10003e40f6031500804d03126501b100d8820900208402c01010240c80c00f805c807038008200c80c0104640d80720801e000e032400c06d18107401d0505d1600000e1000d120f0036142 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 548842257 1250 548841007 548841067
    0x6190e130303020705010c020a03120606050d05060f040e030d200d240315050f060d15090f0807050d020a051c09030812101203120c09050901090e0111 66
    0x1a004041c001e4060314481c45e001002001003c545280c060345803501c07658201c000590524a584000c001c0d4401e0100f62001c81d920305080c1010000c41d040200805800e60354403030540c2500d121160344d54003030000b49040701e50181d80c961070740003254800c0d51258036041d1007000e503841610100216920559580d05c10f612070104014504069aa4070901050010488030311400c40c04818414020090324110484060070811659552441010400700f656010307840100c003068039022400032170904414410300f41c00011900c041d5651210f414003010021954014046241e00500ca0306110754a02c804960000d40025049a5206521790951506540c0d6940d009045a08424071400d031007009507910100c0c555880000c6404241d14034400c0300c9500355001103110200380d00764a50840c4c1d40b240e40c50340b0703010711203c40e8031090b10280c00299013043c00c201c450b0070005256965440302c075008140300301e0f0000340050400c0c07009080d64002d4a002504200400c400c0c20104030401401e01a140ca150350 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 548843507 1250 548842257 548842291
    0x1090218060f040308160b070e03212a12030c0403031101020409050718050f010c080315190e0906040f060e150a0b0306060f03120a120603060506190e 66
    0x101100300c0c00f5a40020b4080d1402068240c80960000c410302c8240d4080c42500280703035207804046800941e20184c1a0f0107400103e1b640d83e01500a41d420740001d90103100d014207154001440d000000200c0040c41c951000314261042e0003003080c4070311f4200700703148a205851441e0a500c0c412042c4524400103042000d0401642c402c58000c2d03042e9409080d840ca02881982000b800c02005955544800d0030907010342d80000074030703180402c412074480700107845101110b4142d44840f00e45410090483c0341c2a03405d003229038125a1007480c801c115466000600304031a0401c0d1070070120000c010103000d103a5200c14140720100b40c200755a038a40c107500400200f40c410308100803c0c1802c000d00c00381d80800f408071080c0028003909030881c1ca101c0106400300c0e580740c1c1c1d8482c00c01c61007525400844d5090307001040032170019804a001041440440d040c50b03030102c002d01020004680050340160740913682d84050103d030345080352060f1038401c6c0c0107500544403801c1220020043d03c0c09050000724011100e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 548844757 1250 548843507 548843527
    0x40305040501050a0201150303091d09060a090201110d020601150228110a2d120b25090911090a0905072c012c040b010c051f050109021806 61
    0xf07d0200c046a044402020781d0703803402806210320390003602c507412070344805100060b00b911101841100e0042c010401c54403400316142c0280620141681082152500544240004c01c0728003641d01d1183c0c0240115807612a90034030304404005400f013190448101c11400c565240ea80c204940003018070241c56a00515225054040f400078650b00413400140014180135048070b100500c03800d544801c01003840d43c100e98115000705015000092244c50f04001c013203042030a00341d904c05140003400d030b2401c0b9800c2100001400200ca408000b40509100381310991140c0185118070031420000c80c14510302a0018560b104240100c800c80d42c0c0d128006803210748500380000700c0c1d004101c12030100d00c004410340641c02403480000c0d40451801045001a46802e561148d1180d146628003200c0042c4041004054600c1d100411304001e600500b05004c58414000d14513141e20400d5280581110085003800380d6005070b000c0729640340305000d44a0402c84540358290780742c004544c4240e40342c0c1420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 548846007 1250 548844757 548844761
    0x2010e06040905090f070b09011d060c03070b0403170f07080c090a0801020c060105091b071a07030f0506091605130f42050901020f0d0903020a050306040305040501050a0201 76
    0x141c0040d08043c1042e007409840c16012600a2500c41e00c60b0544e20415110480006e0b80d00c80c821040d8001805484031545595003444180290140100200e1800d004200c0b00740c5541c001500a690010040f01480704050300301081d00b0900c0110b0351013452920b003c40042d514842e00030100014880c02c0000070350061182822541003644c0184411841070304c503c0680c2c000c1d00900340746140740c487c043c0042114a80300c03696900c10703059244e20b0f40c0d8001b0450600c160580206404541704400c0c8580f50351000e4810300e449200307188a03907001030b5101d100d01501068400281a41d4001c8541c8805d100100381c08910a100340006401c046580b172860f40c2c40b2405183d29940801c032100070040c0082a13a0011819070211030380c861404000a60200c0701055181059800710b0305100e88413404c5180490054001e0324103594140181c58205050680c41801c121401001c03200080c0c4d212014411803405044180240100b50300401c0103180a582c0580310744154052907040c020086102e114840c030035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 548847257 1250 548846007 548846009
    0x40b011b03090509090718050108060402010c03050d0c05030a1b0e010f0e030d020105042f040e01090605010305030405030f030c1509192402070309060e040e011104051c0c0302010e0604 81
    0x4c0c0c199001458803060300d41e1200c103a80152410f56501605d5400400c0c01e6001e000d040e1a0600b0280080b80c46550054899503055803045041c0705083c048080e40880307500ca40ea0000ca400e03281c4a55030f02d0514141c074110303078a0013140f546040074104480001d55200e030310300c0005442030a01e000811800602030740c01d14020f1015a615201d00340b50745c040194103401090045100c0c5034458010700e051403144040d09507031000c0001c20050010804403904c1e0940141c80e80150320300c00042d030b40095446050a40c0c009800c1a02c5903400002e0801c89401c0401c0340381200c08401700610b0400040d2002c030b0341c981000c0d0041481121208000c1030302c800c8240a11078024444401e500711940162508605480005150b00740c1c40300c1e40c1d07c112038120080e0080329109a8542d550b000003500f8400252030009600e600c041e00603a840c44140d192500912541c801d42d104c61403180c2d1124944000c00c02d18190f80502003041c89542c440d0000041c49025485059a0342400c04220010401c000704450f0b0040e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 548848507 1250 548847257 548847259
    0x71112010f0204090e07080f03030601120204090c0e0316121101021e06070f0801030305030423031227150c1c0e0c030f2d070e15040b011b030905 64
    0xb0003c3d00140301c030020340c00541c0e110145800e4521031590741071850b4880e400e14003500416041000041c50561040b1000004040d081100500b000d8540640380c08940000e0403c0c004619500007842c01d038501041017029040d12a4040e4100c2414802c1840c4885241e420080c19070728060318070a0b20b0b0b80244454003000d4008652908060940e00b041d0b0ba8400044d2500c05c0490043c80382c010841c0d10400e000c031705a0b034150310f0341c0d8035503295560381d5603000b20320109a00d02d00c032034035000400380c2c1000e000038994400350044540d11030800700d43c2c00140000103082204200d90300f020000207001d0100b82112406d0500c50008020b0340c500392450403611900015002404070442440e14001c0b856012816220300c84080314031603030003030061550b155886850b00034030342d1007018040c041d03038035030981072250347c45540d0001c0c01007041960b05890150107800241030350040d02d082100c840004444079034803c40c00c4406200301c80d050000030380001841c3c403103000700002c4514040e0505010309001402000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 548849757 1250 548848507 548848511
    0xc090b0a05040e03160f060c0e0d03121113090e0f07060c110a0b030919020f1504050d060c08090118081b0a030504051903110603090a0606060306060f05071112010f 72
    0x403185000c8290411b41c1c40c045441030306d130060420785140b048240d008007440c0604070192140076a281910841118480f50307851a480785681200c01c042c98001d40000228000540912030402c4103401c1624441e6106d10b01e940d0050006000392030b0000750000494034a8201851400c81c0d508114881901150036140c2049221a00144555800780103500c0303a4000410b0f02e10002c1c40c419145d25840d01c031000a50312110000407001c3c0c03450a00e1100c80d652050000951600da0f6507004a01d45092402090f66590303914802c41038034a0f00f20071466071158880f4003c011900410080040302004140050a086404101d50001e840841605007090740840211503189415240003441d40d4424002c0c00d02482c0f104090882c0034010020607400d07254020342c04c601c190711480170301101e90401003043d2264410b00c100000812020700c1018080e0089503401301d05603003011b00240444507005500c43c1040410865100407607441550811008411101000b52444800c01d1501520081c086000814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 548851007 1250 548849757 548849797
    0x12903010f0302090105060702010806300102040306110a09150e032a060c0304052b2a0e0a0504050313061d030c030d0305060a12050a0c090b0a05040e03 67
    0x742048440c10480e03100700d8014a0756a02d92060201034020508028046880c80c404140c1c0c0d4a0502e420403441c4441001070025207a004091500703019005207940d0851b50700040605c00e008841c0030b58012134000080351403410400d00c6c4010411595442010a0402920703503086405204040d40286a01c000b0102c60144061285c03050180c080420941d00c100716801602c0628180202a502e1803022840030f141014a017005002007001e0b010000c2d000168103126a105030345040d0540340341d140c0900c40b4a10313005200d6100d4400030304464036262403206210700c00c00102c030076584100e41c01424200c0205280d200c45c03409030b156005e81394417029217410001000c22030560001e551a880200300d4596504000044145030325a0700641055426420618508405602039040b1303035006000034240d012800d81e280010303d42c1400503030b000c8a45411108508051001000c0d0f1040503021803001008064801800030380014594440d076400b40342c940b06001b1041c0014804e841035810351240c000e0100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 548852257 1250 548851007 548851019
    0x203150a0b15130626060a120c0806010e1003030c0201091512060b0a140319020703050406030507020622020a0315020703020f06060306011a07060f021803120301290301 74
    0x2038021206860b901030020034000b618a1103240090440e9050f2609000f205c504011001d0b00c001d801000d081d0032130410500001c8030801c80c41651040c90044030045001c0d420704080034101101a80100007510300d000c00e2050280040384124101c07681810a43c1242c5190310050724144415840b820300c0000c0d4020000750a03401c480640e14407810301000f04402ca0312082c4004042c003509443c076001520300c510503421000c03004000c5800a141041b6951280c5003403104905a80c4038000031030005802042c100102e42d098080e45130020b02d580003902152170b2480e843c03003182517030013020031102c880805010b065449400c0241e0103503400540c28542c000300794a41c1c902941c00110304500510a4084109400e034010503031502442005014010036407030807003280442c54a01130081103c5800b00034140014006100d41d11000c52100301c00740e264145d40c041da042c0101d0780010640030340c1201103001e0040c80207104890640d007441048080e1a142e80c8245110454040440d092a4000000200e10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 548853507 1250 548852257 548852299
    0x151b252d150309051c03060506070f030e151804060e1306110d06080d080f010f0e0403050f030a05040b0604020403020609040e0a120806090a0c020c0f030f010c081f030203150a0b 78
    0x1c82c8200d0324244885030f515022702849114091010308100ca44c81d5030301c0006849003000c030303106640040103502c41d4440362030b4070b903e03990003103800c0d11303070403034001562140303400d1502424005010010329204145800501074600800e8010b0041803a0391700c41c87c1c1030710381c2010010f07607200c1e40c03810004011481e21411070350b50b10035000c00d2410101f518800001d1840041801c0c4606039602036200113404c40c6002ca50701000000500100c080c84000d112003e24a52190003440c804c18026102081d2410581804400c03410080e154a001d180100070600c0580c84100854a44503419a8002404000c40250034145144440020118513502003140a11707540902c0c2c3d14003601085646060607103c540600d4201c440c480c088001680100038801d11500d4132440c0840060700280a4499070003103092241e0031034490206000c0401d0400e82407003207505010314090340c000069500c0e00c085a040d0340000eaa00c0c4c014200b4903071040507070800540940500d400000e144c800203001c100f9081080d0740c0140c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 548854757 1250 548853507 548853553
    0x9020a092f03091908070f1203060b0f09090402060405090405150702060103031d0102070902041203110f030327101406151b252d15030905 61
    0x1030319242140100c01c01000500032207005503200342c01410002d0390358400040d01545101d06075000c04092040d8400304051100b8120041c4c45040f0075180213441c40300183c100c032116000080303088014840058581d0014048411080049880c01c0d01660380344000f80301031003590415904000202c00340001c02c400011012004104150112041c5d0b0b14030500700e030b5a41c002d01c0080d002403145221034014541503255101d011406205559038103482d544158261307171065101405440b224101c0b1014164400b4000182007000d602034412003035003c20300d40d52800058020010394500e0110070b0540c800ca4000203c085803800b064560441501c10460001c010349030503c04450640d00000380c1c0ca2608060840d14143c2c6803000600f000e1031071220301e10008640d22001e03118850346612103110641c640f1203030242c40e140c10341032138210b0030200c90003002029489105580f983c0c00701e4030001060150110815106512641100c421422030110045c1c000008041c055000d4099508120920128244 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 548856007 1250 548854757 548854811
    0x11e1805070219020607020405040f0c501c050303180a120f05040503010515032104060c0309050409151802031c0e0a0e150103020708090409020a09 65
    0x2520b4003c1c103040c80b00490303550350030003503115800304243c000501d040c0d8403060b0410b0182c081c044009881d03640d0403000c4002170308415042d059000310440e00d501d000400440f1a18202601c0316900705c0d08202001c03100441c0b030911440c00301803152080b10788030740e007101c0e1940807100048000b1141d1810010707120b0340152103164141402c0d0b1150f50580d0b00001702c49404aa1007500012400c001502c1114070005201e078081c20801c0400000415035000d001c1e2038001c4a00401e840c1503110300d181010b1401c6a40c08907110212040c21204603c41001000d403030403100c9600b40302800c50000e260445035200103821032a402403500611101b84641c6a40814034402900d0b800c010b00c5942d0240e4690003140150005e6150784104009a003907051000c1c0b01140071b4403410304003031190296001030700003202d640100c01c49120001c10050601e4404020007c0b00d00c00382021460710780a40c945084521580d0308407805070391918802811521340c1c0e0b9a801c010700c51404104000c06100e0b83d02d02c04041182840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 548857257 1250 548856007 548856013
    0xf0f02030d03152709031e030b0f0d0b0403050901050d050726090c04020906040e31330612050f0303010609030b07020f031206120f06011e18050702 65
    0x30501100700c24950f0180d440c0464081d8294080100036006417880714402c40c100b1003080048003c0c0f0080007210030609059403800701c0c90f0205602402940c0d240e100c0410310400030340960001080328884a149c0098051400035620112040103803098410007000302c503050b15240c20009a1980000d100d40c2e07200b51880e0304042c05412030700c450402c901c107882445a81c0c000420300111460300382d00601141c58003400d000d0038295210034954036820f0071a542d04d600d120307040c007424661080c10b490b040801500080322a010025440e8010b080d481c031500c05000740e02c10344000c03500c0020300e4481151060309100030700000d51076450344c1030008500601110305124600c1e8407001008080240da040c0d80c91940d94401107407550b02d880f58501c1024243c04198019072140040c400401d01c0100200d584030410204a8207051061100800303040d440302119030404a5a0200303e800441d0960468604035200560242002480d42411401c0e130701c4249a00d0344c802090300340041030340220340b0a030845c0d026 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 548858507 1250 548857257 548857259
    0xa0b0f0a24030906090302031b03040e07030507021509160b030c070206090622050f0402030402030c010f030e1501170303010b0702010c03140705100b0f030303040f0f02030d0315 78
    0x9100c599846401000d0500c05500e0140c100026000d4455012809620700480c1c2403c854681d94101d0714200301c00e80c0140c2002400b0fa13545070010b00940030403482c1200131072609152042901411101514940c01c040d203d17008604051b208100c91140c40781ca03400d800c002810140d84050741c0769181d903910225041c1c01c4400241e12024a42038034401c50810403940d10f420710340d41c03c02c000740d8011200241c0c000420700516100700380803406492074505404091400506103401c20190a1000039070303903c83d074010000c00c8010780f000700d124858030a082c01e0104402000c6402900506101e00f409070003449032000c101c1c08400c100b0303042030488041801100c092a560715207251248004d0095042c041d40802066006501c00e0312001c001a019192211410136104401da810b90b0006c40d003a6000d510208c0c406401d20210300c030b1a41111360449001d02080b11136000f1a482c2d000c0103002030305002c659684402440202003201031510b50003010390f11007000241c80540108a212a00c9070700726003142c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 548859757 1250 548858507 548858509
    0x1b02060702030c1504030203190e011403190b0303040b0a1e030c141e030403270f0b250503031b031902090a080f010e10050f0601050714060a0b0f 64
    0x1142c128400348005000241103801080c0103d40c400b40041b0b0451104102c6061300312030718034880d140c010303550f0340700d200111075040010588200034244d100140c1c0c00708280980c45000c000c1c0c420001c2031618020503105203039000241540079540c4890403848000694000319940043d003210b070352040410000400ca010b460840c2241d130304561001c04940d400582c207454850789009085c1c0c00c0712024030300441c01c0110484001c15001980e041300419984418070202240c9070013940d601600039684650440d141260904252203d40300d103286d194030001e000196980c120301c083c170030465a4804011015034614265540f680220750242c01913094155444410b856807003168001d030721700340d10280803802240d1a4402903100c64591940b01c140e01c0c4000606080520190303022511080c0000350240c03d94844606088002d40c400f0000d929190400600d0b50340b801c8015040402031034800d40381c80c89840c0c50130468000a6000d04940300b242c00b00074442201c1e03004414043c00955038000d0b41c4003800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 548861007 1250 548859757 548859763
    0x4091401060e010801090c0b070c0503120c0d02010b06040b0c070803030f0129030c03060102010b030703080a320901090e04050d0f08070801030209060d0b0f06010e0a060c0209060d061b02060702 85
    0x6e034020310708001c20f50108030400c82c0001070030311140500346142c5216551000170b4640308142c0f030316220000c00402c2a030801041400f4021000724640004e1059810f50b20000f507043c80359005030402e01038042090f1413103030b504001810280c0101811641c1c1c9040070076100e00550002d2080e455011034810101121000c5074011140c514400c148040c25a1140c00a240303054100400c0070341159a501c14000c201d98040204000940c054103a05a0742d124a210050804191258019407084884d03032448100b60b61660303403044161a80807041e1260180801221102440c2d880000c40c0c402103030512003440790204012000881a4840c140c1154a00c5d0b010345005408681c01c10209220307200410240c00c101a090b03500843c000c005407000206980d607214009000d40c3e151070710700705240800c11a9600503d000600e02005c0359408842464090000c1c1403130600c43c03000380240c5410300030070707525180c486040706515440041404420410383c4442c21014401501744014466880403d81640c004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 548862257 1250 548861007 548861021
    0x80a030c02011d0607140d030905121e1305041505091303050d0c0e0415030503190207120b0717060a050d0f210207081b0405040204091401060e010801 66
    0x140c40d0000e40d0500e5400640301814000c0c0d030b81a5070440380529460990391500100300062040d44400340c2048035200643c50080314140010501d45441c0c50350300400c0e400500380c02240b526490f1203035641d070005603a012802c00c00440542e03c0201049040c040c4141a402c0016510103a400b08681c41040c85483d04030081c601c980741e04070802401050a4004001e555480540a420054a0311841e503850354125551502e5503400114030394460a03c914150040750000b1161034001c03441c2600755181c0e07646034070960078444142e81281621500c0d2500a002d40402070000440b54101e03203250341000316200c1e400f00c508400048000b40d400010241e40e041c224011440a08010f500c01d00701424010440318000c010340d00c0080600b054070000d40d90111401042146200b55840800d101d20042d01e40350554001e01d00a40200c030b01458000b404c116154520901254081215155400402c008200e90760b03015110004180c1d00030703d80700b0305401c41c0049540d040e101d611503a0780c410b001e900325158 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 548863507 1250 548862257 548862263
    0x51005010c0809150f0c10020c03221d010e0a05040312020c0c090108010b01020601082a011214220804121505041a0c0702220608010509010b0307080a 66
    0xc000341011600c080003409841d500070703102d403001000c0340720500403d170070407810040003c400007075050800c1000d221140d540c0620b01000d6080916101105403a405600d1031900907040d120b0202e00e82c045803601d100001c14002c1c1c14955005081100c0411582d424004c5036802828030340071903001d00341c2e03100c0d1910864050340d840080c18941e40c0700070083e60242c41c0c00103491040c1d8502d5402e42e52007038025030003403040030000038581324603074006410244141d11102c1e098200c031003a00d20f40844910f11a90b4104e4008802035003c00d41001078941c10040500c5810b51b914003040546040340c0c046200d0b002d4124640040040714008220381c0d08680120001445900103000030000000c100311825a628481d4441c0c1c0b1446d981c00361040115501110306039030707203c41c02c0004280c035070100b001e89400560485049140070034a4010451154401016104d03034005000314121560241d8844000307401d40500900250900300305c00d9001c0d01c04480f11503c24010f000c0700203420000000d4918541d94 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 548864757 1250 548863507 548863517
    0x28061d0d050a1502040806090c010f0c1110030e0307030c05070f0621060b0d0504020a060813020907030e010207031d0d031e02011b05070b0c03061804050a1a0a05100501 74
    0x440b6503507500030052260030f9054060b024000450a2101030040510034a12000100003426240e000104078013550940c440a1180c900c107180701040f000b03207410303540d000e0039608414000000c09089004240e0240c1e40141800041440c030109513000703e00c59a200c1c010003c03192032540320000c820441015100d4940440c0a0781e03000d01412001c443c0d41641d03641c180c2000a1003d95406501c02613901c9103030a000c0d103d40c0c407070820007145009281c1c1c5014010610b0400300318030345003034015584019494081e00c141050070008100b00e2203a0400c2d03900001c84c0d0029501e8110900c3d003d0003400381000440a583ca11004101180c100030741c3c4800e000d5015982c8034440280307101c610000c090a04c2080d002c554842c88180d0399510101f0b0089400141d9070703034030765039000c042c1810401d2000c040d03d402482802002402620f5031001c02e43d03e44000c1c038051001042d107a0303103080751a06541c200020f101c0d0840420b445243c901c08180c980c07048600346000d000950343e804084100042c0c03400303586d012030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 548866007 1250 548864757 548864773
    0xc10080f0609090d080a1407020f0601060903110d020301110f0a080a11190c05030f09040b030703170d0609060e04150c080c03090a1b14010305010b040528061d0d05 72
    0x7900c04c42c2c2c051b0b04030a0076080010003c018080f1101500c2d0122803480240e4000c08002c0400b103420445180100308500d449881142180d8941450100e0004018031550308030000f07100755a0290b002d480e00300b90805100f41d82d038400660a0707a1035042a44402c000c10107200004140e442240584e5004500c001c507001c1c903002c2d0f1384e0044c103258558403425600b0040100c0d440800582c0407c02406550240d12a4a841c3c0004204010550340015a2640250440ca204000081400304801e440d0a1940603041d00c1e201c0701803050f002080c203940114813507420003030002456002c0b42c3d0703114002c40c0110900c070402c0104000004c01d03141e1a120030000107806000041040c8804070240d07401c011460300f50b6040030465241c8508252050311404031120075000c0820421784504050032180c8803e080502807503141003040e9513240541e12a5600030440c55005140704005178800ca0100040740c4a0320b28440d840300300080844403130205c080900030321000c1990492400c801c84040d4164400c0c020140d035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 548867257 1250 548866007 548866033
    0x140f071a031e0703020d0b03030a0903200d06090c05090c031611060403170702070b18030703020a03050703060f0b031c020304081b1009060914030c10080f060909 71
    0x1588014094200080002c0d00000340d0004060258010026603902580720fa0070a4841011141040039991280d03004200d1407400c0741d000349400c41140d40041e40c030710421100b13100710840b070301031026255800001c602444040042c0303548200c55444c000c092103d10f481e11801070000d50700c003c1c1d035404c42e1000c0510000e004203144002c907405406280c41c14218203040c417104207180080c1a80c044001c6044240c030071201c42c2103400856403010075440203001ca01d05d007044118091046201c1000002503d40c086809910200b00100c01103a000e02045a155074074140726807a02c07000d00040380d0b000e0130042c0001c1950524028440000001809000f054030071028000d8500541940d01701035010610000500c203c041c0321329504100610002c5070804540c408110040854400d002e06100a21109106581d80a60818243e0310b901d000308002c81c4421340042d1074801200c0802c2ea002c8540c1c111980016800300103680540d41c04066009951591010440800740c2124080802c0c0e100e41c211b2060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 548868507 1250 548867257 548867309
    0xe0a0203060109031103070b040b1b120a030b031203090d0311131509080607030f05060a0f06140f031311031b04020706061206051006030903020a0b04061503140f07 72
    0x88030b41c0c028200c2e6485075481124048d81d0700b1950210010301c00c0031944510880c00c00701c480c03c2c90740c10761001e054001400b00c5c4500560040c8501c103800c00da500c10904540d51810000c0d5001c0c00c14000c103d03a101c2c40c11351845503950803001005000a410036510003840c01107202981c100e00c040483c0c087c0c0d010700b004c0c0c030030702c2540846000724100924400d00160540741801000c0c0941803564011441c002011710141c25548003804031805031a00d003d0400c1118085c01e046010781d1000c0c9481d4042008403c901d00181c05008881e244012000050201d115400c4011101c581d104030318542c4c00101020401da1200c1c1c131101030b10301126032013000011600e0903500406503a84100300028000b600c9050000640d030b5103500403940b4039554000d0010b001100180070300101060329043c02a400e4035034000b91240c50014004100810020100d410460241c000d80e101c240d40c0c140315030342c150342c0e4100135000580184440030702d8000d0070020212060003044030301c19142e280b074104560f40c90312688140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 548869757 1250 548868507 548868533
    0x140d0605190e1b010507080a05160c06360605032a07031106010605070f0f0b1005120f0712050a0b0c130f1202040506120a0c0e0a020306010903 63
    0x1e49a40001c0206101c14a80e10410040d01001c0380100481c0041042c1910381c4031100400d581880420f211180c0014040000c44000d1245840d1032501c17422101c2c5020402585040000c101ca03034551404503c07550f00100e201c903544c640d40811403008500d88518050b01d0a040324120b150000c0007020f11119000d04001d40d0845540340440041c00080402503040c0088040701d1070031043d000075000c0c01d241d88506034410b01910354000c2d010f00d5140c881c025209126800300100f0b07980f0011031400174040b400e8943c50220341c1141c03521a252409480200e000c100354010a4801c90408400d018040c00008141d50305401000040101f130741045500b640006000b14111180d01ca6800c011000441c100d28150140760f480d01156150115040c44004050351038204c610300341036202d0200710030100703c18035041044e010740340000d494071070394046503c0b1080000503072041d10078401320408000d0100b04100440d4505610000d0980300c0d5096a41031388004d66801d4005248910144007142019403204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 548871007 1250 548869757 548869771
    0x3140601020a1101050903010e010516020c18070302160f06050a050709050108060a080712050d0302181903020405010803120a06120818130e06100320120a0c0f140d0605 74
    0x5401c06c05528000703403d581ca03180c0c000fa520394440007484800403890300f02248109860001d058601c0042d801b06503d00022a81d41d480c102e014404294294082e40c1128800054a40d008010030540c2c00d00811603945500c0c00c469092070000040d40340318251240310300840a541d10188805d19100c01110702541c05004903038058070389000040d0400c41048401d00415840800710400321807401c000781450480d5110341c0906004000c41c1107000503088141221032000c40c2c0c440c001c90811f0f207121100032078503040250400d281c203002203560700c4008090315405150070100480c0355a481071a8060300d456100c3c16030f40b903240880c001300242c40503014065040089060049080401001800455114640500b80b503030321208040c0555050099036480769074400c80141492560384d9003940f64808081c034041d407103d01085d2070301c071350380d00d0700c800c1584030359001210501445800c01c0c060a021502c117004203426200303030014040000108802c18000000e018101c152041e031038143c0a414010020303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 548872257 1250 548871007 548871017
    0x901080c1e0d0507050a090608030f0d0e0105092805150c1e09090906090c12030904060b120708010e070e120d08010906050f0d080a0c02091603140601020a1101 70
    0x101010b5121201c4040c03425029800400d0480d03d05010705c00200e28680241a80505115050007070300b10000c01c9500f000c40191072195242e00d841540b0300244406103400000b035013003100740b001958000812140b00d1000f4410358101d50380ca006480c42240791243c00401a421102441050a41d00412107a12100042c0100d29000c04034094103031311040801040e4030f05001040003111070510079039155000e5180b1000b0040c500b4001c892a0b660341c460300d4150f1041c90b40c5114141291001e00541d0010b1402900500065403a9286060300c5d402c00940005100469400140c202c0c0c440c4c20b80300d048031402c079120003007030301c840c034040f04c20f03a800c0c25074680c003d11140d503602e000060400c11041d80540c50b03540c080042d410683e0450944100340c2c88148950408140e04290307540e05800380204c558400780250791020b451100783d403c5601140040d5005030f803482017081c107500a402000d42c03e8034560342000a081690301e020b401d1082903a1050040c1d10030a10b01c80060380001d072006130786d0414100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 548873507 1250 548872257 548872309
    0x3090109030b07051603031a04060320060409020a0302030a1b3207060e07090e1207060e0303011d06030d09031b0302030607030e0c0303030105030d08250903030e0901080c 75
    0x100ca4103503036004001c1b0000703030f500c081c1d050b90102d16107a4483c1302642210107000581c0307581c42c0d41d51072111201c00d118003082c009410304030582e240745c12a401000c8122095458100c00c42e4082c00035003048803281640c0b810584404080784801d00312035101c2c08147c4850301038200a81034000e1003030f12140c125118a010940080320199043c0140034020311546000c030310200d010080c0c1d41459805d0340048200c1c0e00307003204144450404908400d8600004c00f0030303512001c05082c08805051042c8100005000010001c2550004030070407825190140c00c02441648400d000c0c50303903442138201640e0000d26011020300029110101c95640e6009909060010342d849030002402c02c40d003510720102007541c5d4500e883c0700ea00c0600c00c3c0c6540e086d04901850031585042c000c2601c1d903c104008008000b1110005189105298501800c60880c440003d0030040f00e0304d03000d0700940903404142d02040c009559085140f401228682c10303200c655028010207016001840740e039810040002c020721104803d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 548874757 1250 548873507 548873527
    0x307060906083d2301121104060e06161b0609050a0b0a0c051b030115120605070c1e110907020d08061305040510110f04030209041106030703150803090109030b0705 72
    0xb19a03041c0945041c08071058502d4130000342007441085413124002d0304180b4121a210801d4041c2c40844210341080e4081c0c04001d00000c0c810700c41c6280000c0030200200b000014410200400028200d144080001d034079102d0034261b489860600c6001d6008106400c140660318201021744229540341c01c0501c2850b00c26690036003000b80c08030ba2901c124008003010881072800f4000e481c8640400b00324001203605240414035405940c100142000d81c5400118424610500c60081c2c49500171196040707284002258000d05040b441060300c940b26801c640190500c7e041200e5401820280c0040c000c01202400a854110000308440c3d4003440f010610383d1026803030300035188202c1c811005090f058440c0350406080328440f0340402a941c2052041d070b040000100129000e403030701207030105002e0303441c0d150600f8024240302817030b5042030020080c41001a01504580c01e032f520744c00e00420149072203030007895032801541c40d4240000c201180c00c2011a40d0400503640003140b82ca001841c0104401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 548876007 1250 548874757 548874779
    0x13030503160303060b0703020a14070b04030b071e0816090503010c1e021501120804030204230106022d030c0f030a03270303020a0e0307060906083d 65
    0x5000c0d0740d03581090704168003015810f11500019000e2200307818101201d43d1030007590b610080c0401400290040c1440c0c00c0d900041080da0010320400000c19591503c034601036004140588050780070a15482d40d000d040d6501700c1114400e00010340c5c035034100d0b03513030b548501001000c0c0c41d00c0032081c0886000d020815480a02940142c0f448a48800c100451410b40c115170802c80c40600c1d20031074018142d44203154200e248a141159400f070360b403050a0307003a820820b41d50f1103658070084d0303c01c3c940000303200380103d0081913003221080184140066a44c0c1c11040c5c1c2c03a4840e1a030034419000c80b03e01180d07258943d5262681c0800710040171039003491130b070505051409904140701012030b840032030350108203941406640c0000c000c1c911100c4030701d045c82102e2a401228500010180341c3c0108407264080e201d205140c107800002421a00c0303095039820040e201c021103008000000c0c0d00a00062851983c01c21440c0184c00c202c0144038801003110319030100c284080d00e0541c4030a000e842e000625241030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 548877257 1250 548876007 548876017
    0x10302030406140937030f0302040e180606090108190507030c030c1a0c10050603010209190518040218130f06022a0a0602130b070501060302040c17070513030503 71
    0x840020001e044d210101d2509405c0701c07a03116a58445011501c00e440002c01c0c0007100c1c4194582450201a48600c0e4240c0c043d00941c2c004400050081042061001501c10b000d40300c81443d80c140d0300b107030f02c6d0141132002c409024000c0d48030942c0702550112045c50001280403a5030700030000d0b66140c54a82d82c600e001303152103a0042c0c81c4589034003c140400119095054135040e445680c05141001c15400305440d02c501d0314007201c0c1c05640350009142c544007901203030195100203041254505504010302028401805594003c0340c0440b03502d003140743e85540050286070000c005c0f000142003181c40045408000745503602c920381842d44940010007001c2c030382803880c0c4500704c0580ca40e2116004801001c115800401001040e071410000d00030012505034003841e0402400b43e03544141d84000f4402245079071204c800c00400088071014040c06502407810340c0d10895061041c040d6028085440c2401c8494910072113100d0404104198003c10080291b0345000000c0344030349560b521018116001303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 548878507 1250 548877257 548877271
    0x6062103041205011517250e0a150602120d0b03030f07030804051b180a0b131505090408030a09031806020a2a06050705071e0914040803040201030203040614 69
    0x11004018a807041c003050000203010030306444601007040c854070907a43c05400015003801c040c0c0203a0286038524647c507000c00741410010554550a00d011070038000c01c45c4c0a581891b00c010382c0300c0030602510100311005000241c00c942c42c00e1540c0b0440d81c2000313101540d83c0300d034144003c11104a0160040001e45203260082d1610045031030142445814110135880c400d000c0710000f01c01c03034030940d10364529104002c1282c100c111587e8640481380f00034424114510351021f20381c2803051080301300d6000501c9204161400034513803580e6605010001c04191001000c0c0241440002c2e90b9031000da101c1504103020780b51101080700e8441e40c010341032405410520040e0088094201804076a4920981040d21880b0110202068505520481c130260050360200200007981d1802d03c0320401c428005040f03c0032148250f01c1e910780d200c0300000da2a214240f0010b082030b441105d40261945c1e0b01d4410340d0001d0f032241c075680c0c503a1300440007940000c10448085946440317054a658030006541d20980c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 548879757 1250 548878507 548878511
    0x70605010e0a060f05210a02150d0605030c030c0613090504150e0f030a3203071b0b0105101b030203030702101b0f09030b0c0406030c020606210304120501 68
    0x1020300490b030a651940d04284d00b031000e07161042001d0345070300426401911000740a020580020194503062200480010f9800348106203070b9082e000c041d01c000d1a0444004400704522a0303502c0c00c1c15121030b10140000c0c0d042d00013080e00c1c400b6003000c1d03006041c01d000040c91080c005480d8034800044910540e426600d046080c0c540401480c49889452000031103c0014900262890300346590382c8a2845840c0800003c2e46685441707903034600d0600b4000c41142c10340300444103c803040f5100d0340c0003100ca110002c3c0104c11800c0103806440700040300340350040460781c650b82c2041c06201e021112640c0c4142000321000d5459401d02c03450310354008062095000e980d882c208040002e282401c201d50104c6602c0c540740c41110488911000d10710740003e503081c00e08034100350701015140e0740381d642d1000d42032020304010000070070513000c001c0003581c410ba00d00f00102e6003181c0049a45a4080b1507040d04060400d11030564245598541c2c05410382040c21245081c0d00d0780410301d4044941e00040b12140c2d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 548881007 1250 548879757 548879761
    0x903020d030506041401231e0f0604150f1101140702100b0616030201020708030a1b0804050d080402060409020c06190506150306030c04050903130f0b0d11070605010e 73
    0x194035004030b40e0800000ca9041c006202d210000500c02071040c862818028408420620014104254500340000081020307450108404502821020005c44c0302d12805240b0380c0d0683c1482c021060760151450074a401ca214102e1083c140c91021098925200f805140060885500c2c070034000d0300c0c104c084c0461141d030b09040c14513019240070355480406034414140403000603203883e443e069408240311a080c000c1c0782040781c02c0981c028482c840014007006400020419441da10303400540004180c00700c804d185000111089603400b4058038020b205400405030703484003d21515080341c1280c001800c0620301a503d0340208103d030300981e6000d900b50841000c00000d2002e8122009154018160600c210f250410000b00f40c0c0c6a034808159521101101060060b10304000700c2c4803820002d082004a4140744a42d59075982103100d102204044d00d179004108032014140500c00c0711102650380d07051554440c00c020113403540705c2a88514a5062000d8030214196010715402400700c00d0343c2d001a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 548882257 1250 548881007 548881033
    0x5090a05100c03020f01061a070206160507080c040207030504090510051e010806100504060815030714040b010216060c06021201060504051c0807060911040606111509060703090312090302 82
    0xfa03142d050a0003039900d022003c1014101181008d8080106480b142c0c2e55a061440000c10700e00039207002c0c0c1082d48140350304900704132000890b80705440505040341e5500c408030041100347d109046000b4001003091000700700e541c04940140d50004003c80081c8900d0342c4950104d11111012a003181e90034220b034181e501e41e035801141050300003901b5510075081c0d0f0b03c0d428000e45503200c2c1e41718981c20816034100050310407400041042078a48020309030b40d54582d139020380590070100644510301c02c500c0d043e641d0780a5800002c16406030008851050306251410300240c8205080f10b5080e43c02e80c0e02001402d41e0064150402800b03440203031240d036111810081030004489070f40f81c1262003402c0407030707000001c50408001c2e500415071045010070380390558a407007080102c0296200c0d030018144280840c050b60403801104611650740111040d100d600e15400502c55030589080c1d2903500080c0104802600ca6013007030b088640a410b00c2c0624190100c035410031949000c90540050b00603050070410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 548883507 1250 548882257 548882263
    0x409120807090b030103021f050d0f0923121804140f10060e0402090103020c1605010305130f06110c0706081603050601050a1107210507060903050d05090a05100c0302 73
    0xd0115620f0b010b095604550209080400d2a161400d090010440744d02c1040e119030115034090501c02030500404e8031405c42e031400f402c030810781100c60034460903030b40720510340030114104003000c0c4034002c0915083d82c10000c0d4180c0d106403020013949162008909840c1c80c1e90065005502440c0b48101607403a1682c40405411f00242883c000303484116000c102a035807100340e2880c4600211401070b170311025200180c00911940141481074003851084440a219982102d8101c42080c2c030140255501c1840d1412000e465990040c54145000020707404100c2710b50049a4580c2008503061034841c40d15040e0349480040c0c0d0000d0002200d620030080d0841c1e11600190300280d442c201406141000000a025401040c00750b03410401319401e030442200c01084030700002c050343e8070705180d64091940103c010516251080e95140300303072500000d80c1440b543d14001102c4c0c0080c050700240031500310448255021540c2d41c5d601c400010000301d104ea41d0300c500040e01501c3c6e031321800d130011007032b24000e82 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 548884757 1250 548883507 548883509
    0x8070503010c18090b0d0b01062d0207060518060c0a061802150c01140108030406390c0e071706100206010513061a0405030f0304030309050f040912080709 68
    0x41003060070503510f00060341c3e54070002d094401c18800401c0c90080540812031108990030042c1582c4075840001030400e4101c03a00186e44480b40703001003981d94901c4010040d090000c1c3c50b001c01a03101310700400030a44100041c00009411482100d071640c051130000c0c600e5007080802c401c03103030003c0d05140100701091242d81c0c884516a0464003004115030000381221400485004d822080014000c4015200f0340c410500316011500c104400e50310f07482d005699401901480000c81d82c41403200e04c1024400c0e00001d186a041e03034280b160240c62000b1210704c0103000b101142c21007030038140803502e0b03080408058403407c0d00343e442d8101c0240b000c0d042c1c0c1c24120003424041c0a02346008058120303d501203006d506440d41a141680e4112000c0461001003000b0342c0100e035402c000100700f80c0800c00040040c401c95001302c007103070050300c00030148a450348180d10000f40401c80c0d03c1400c101c01d0800e66200351111400800019088041c2c0d00d8100f0f8504154044c00009001c0d1004c1050031500291520 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 548886007 1250 548884757 548884781
    0x13230621030f121e06090f0a09050106290f03150619020a0201090b09090a0203100f0f03020a06020303090307020d020a0803120105030d020706080408071e060207030320091203130807050301 83
    0x2d020308100e000b003900180003801c5100181f40f0704001590045050300118201075002c07008105e102c1d511582103010600808030509482080000c0c1c80c100c0129400b6543c906000c44091483d64442145c021014407a0003001e90b0060002e0004e24580d042d420900c118921039900902000d044510004004006a030030101e4184070500400407140c55800c17085601076070319400181d994842414000861030568041009020030900c04240416203400080480f44207440b68a001754481c0d4080c2d0316030004480d40743c081d9205110003805441c1c41c0030b03007500440c006400c00c54040e0b01d0320281402c583c8940401501c0c295450010400360034100549621269070344013812a040c103003c40103007160030240010b00003110100e07004081c8441044041c0543c0c84560100d10004e04070b103054400303504500c00039070200b0702d00402c10402c01c84503c004092000140300b141e00e000708100420555034043c14406201c0d00c000d0101c0c00217201c032032100d000130300320840080c010503290108250a41e0400d80c590 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 548887257 1250 548886007 548886061
    0x50409180f0b150a060302090301050603030a02121e040602010203150405070906211d01061208070602030415020c0109061a0a1a0913230621030f12 65
    0x1180108941d84408060194054210074041e103515402507000c8001428207036201c4625800000c905426500805043c4401d9000340201e903548820952240108000360300540c00c000784202241d4100c01c01001c20101d084291403050b007003100d48032031a03000b0780c021101503035001052080200340c0c54610100d6000c126410311562600c040d0090140741c0300d1148005002c1002d01404100301100016400111840d504200c0310301e0200d01d071f15407901044100c640300d52800701d000c07900c807240301054400c49401c0000203240030500d0351400020342c4014025520b0710030151440e0407440703070b9000600f58014a0000420702003e40d04100d000c13100a890200c202d980403941444050311440c130b0303420441d0002030440700200d20b984884c0c502ca12030f2144155001c0888211011100c3d815403284c408041c1108086c2203680b42451075501e4111b01356010b42d0b206c01d4050580da0707121041000352241d600d818096a007001c40820880030741e070300014002010b61800608020089010290914080c090384000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 548888507 1250 548887257 548887301
    0x80c28080a1505010302070c09090c0e09060f0c0306030c030715030e030c0c0f0d080a030f0b0d02010c060c090305060405031b0a170703030b180108060703020705060a090f02030d050409 81
    0x2510509514a103d800d042c0354020500c441841042d003400342c0140202c3d40c00740211021458044141d10f40f40c091200340c080300c0e90104907000d100142c850300c02e20100300341800640b00c400780c40070305400003041503a2500c038001860401d600d0038441d20b0010060720f40348041103212601d014054030b181d01648611a40140b060103005940001c521025400684000c030350014040003003240d48000b21006008901c000400c07020982e8954080d03401503000d69030030003c900c41581041445103440c140039000803d00007002c004204c2603404101e003564242400025142c0c9c0755102d42c10800122000c0c3c0b0540c001062203400000d2800008034030708180c5000d081010402e50ba21001c07000102500070703034404040780c1d4a080600952104000d00d100410381301d1502c18520811042050900445280380201004036803018000d0003a1100d569001014001a9071400081d034024001c0305415a0800d104a003000050303201404110200000e0782c0c0c58954580c10400da12007510004d2801c1c400780740c40164 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 548889757 1250 548888507 548888531
    0x6060c07030b040f1b050a21140c10200105190e031201091505150f0d020702190911070c14030c040606271203080c28080a 54
    0x2a4480c00c0da50300031602002a220303410080840c03031050100038465502d00030652888000d1600d107108440c4c00b265030801c0903171100b84000a19401840c0d149452074508912000505000309442c031741610842191541d01c0964000780000300041036010110705140e0284801c003d405002164849440d0300a00060611401c11290890b06090a4a00e80d41d141c558460b40701c000d00440742001d501e205c180480796120f401601c020aa06009100440b600450007d4941082400003a4042c40d050640d402c1404103900460b0301d90110010340d04455003000400010780d50626001466894178886417012810300007040d0444546030503141b44005c05028480000d0384125000d4161038a8204905182d42c41001083c54050314030b001c00d9116003031002c0420540d9000404181020041c4840110342c00c2400002138000c1140c0100b210444141d054500424002c01d24036810a10324040217181c501a8850314420f104100d24003a03100040d807564000c2203501c164450741243c0040341c01c00860b62080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 548891007 1250 548889757 548889763
    0xd0609110405150c0c030105040305030702210412020f0a0603020c1b0913061e0c03060501090312082a0706060501020606010806041d0102130e0c0c0607030f240e06060c 74
    0x2c1d410030391480000e4045600070140001a01805c002e002440b0f641003e180103407140e0400c07038000005208942c5c145a0001d42529203e107580000c0070000d19180c204031a0142c84101858141c1c0c10000c0c070701e0400a02d40781e121519008010a17036005880f103107400c4070300d8181440110500440d2006803811070342c61381c0c0c0b491602d41040c0045003818000c0d840d8076001c00540312038803290000902c4031030800e41c800031b947c00408034507106039001c12000d1344910056401c2d1400b40009004250402180182c2d0b03400381112642049481e0500040000101c0f54410005d5401e02d03444444100440c61030b0400100e80202406440240080c009900d00b50b40003d01c2c1d070b88014013141c03080391142802d48100104e0341888003500420703402990759040420b441c101000c4c843c4500c401d46140240021711200940e030640b8920003098010b07269607212a001100508001400c03080c841d40d0740d01e0b01c3c251a00c047d01100c1c600c0e01101d0340d03a0301414031305810440300c1d10006007824000d10303080041d515044008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 548892257 1250 548891007 548891029
    0x61401050a0f0503040213020a0c0213140a090c05120109050c0901062f0a1a090f030d1e1d0105361c09030c090603081614030d0609110405 61
    0x520f860340e140e5580d0300000b03020f4030088019007001c40c0300280c003404641c1d204d04080c5803107000395111600020803601020841d10390b070070300d1554041580003040903200160050b0346200e005481c15007006446a0000700c007441c80945800d00c9070355462000e01080300a001e841f0013810210b816410962508002804007060011803c004403001c105820b60040c07100c00d4142001d40702c0003115145c000f145480d00c06d43c450510a2800340e00d0200c00512112400146080d0040e02100654189003c00d1680c40242140d2030040c0e1400e440c058a95000d911103124003a581c0c01490700380141c42440300c1000e0b007100c5003c0c01031000840403101e080681c6400c0b05c4460208040718050011300c24601d508a030514a44c070a03c00c0741c02001c1c040340301c0300703d510102c5141a20b026440c20b0305d9540d0303150301d400700b100c01610008100b580f0500c001d07501002400101c0004501440c4a10040100340400e00d09540c071442624030803658881c418040403100d44030308042040c1700c0c0c944502e010700b070000040640702c40c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 548893507 1250 548892257 548892287
    0xb0906010f03090b011d0114030a021002010605031f0c080105280306050a140108030a091403150405061006030b0a150c060507090312020a0f02090703140a061401050a 73
    0x7804221441140c03103644966039440d00400c9200c0503584030b00740c0c900d446046c1c10300350300030f986000300105445580e000380c2c001c525001001050b40c6034141e0300788010240b005404900395540c0d10000241503d00744140c4940310f80c20401011415040c014000032590001501400c019a200050080c1e0725080040c10305100b10f03060140d41460906180004829142c1004202c07a0030103041c880c3d20215500000440c1070107440350704042e07880350005540c0e401540b002c94000741100004002c00b0032005110355040e0400740560705012481d070b02c40c01d0310410588003282d00364800400c0017050544103003440040e207034030301d814040c0c4483ca40001d1204642230289080390f0010300d040c02041801001005640750b4006d905200c50f103003054019009203124841030f40e046401d0f43c04180150310200c0e0441100354000c90856a0681d60740034010031500044c010420315030380d0b45c070300b2001c10094800d04c2c3c4030740400759010800702d0602c41e2100c2d6902c80094464140701041c4418101d0039000f80c0000308542c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 548894757 1250 548893507 548893517
    0xf01030303051503030c03041a1822021b1207020303041e03050a05030c060a11030a05060411070506150603041e080f040b1b0d0c020d0f171209010b090601 68
    0x21a078884800d00032003c4038403545840b000602e154956004000b03802254842c200e0b2090004e144c500c401c030f45101d00031032203d500440e5a28202e107454603009603041602c400b00050440a04051000102e0f8810808091408810315298280703403000c1000810680c0e00c244114200506030f40401c2da00d015502880c1a010054a50300070f12204000c14500159006000c60b05442c0d402c0c10625200ea0102141d89240d014581c005443c00c581c50050004070041300300d1715031441c1c0c1e440d00000010600607000c03070362240c4c0f543c4ca115141c0e8038120140034401c0c0500c2c003034061810280045400000b0741005c141c01804148200001304220302000c1400000b07404401d03d2010344c6c2c1ca00340b21584580504094152004180800e0003421603001d001c6962680c0d0750700d201c40c09500c007410341e90604104400001080c600c80c000040c140051580c2e50316200389403049284440390354203c40318003034001010000340081600c1088001154160707401140325002001a030b42084045210300304000d10003810f0103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 548896007 1250 548894757 548894761
    0x60f1c02120f03070f0303050112020a050907031514040b04090206031314030a200106030b060f0118030303140708041a04081309051f0e0a0e031b0109020a0603050f0103030305 77
    0x50302071182d00b51281c01c100035240c1e00c0e00545450b411400200800350006446c041c00411036148407003054291503002850f03203050500d0801084500700d8000d11100405072249400740c28030786100c400382c019105031071085090503250380511044500c0492620b10980c2885800c42c09a00c40c807088903003280289051800003451404c0001d00c41d284142060614030001070400015503008004c0d1a01511244510351544038480380c440c04e0710f1031401f002c1e00854458000c5046480c1c144448040307541c060600004c51030f10401e618550700b00c55802500425158101c0503507989210b00902d50100c5203040c104030701d00f02501c1b04840040d117000e886105042d21030104d0140020300058030b0754129401c1c65007440d41e440345010400381c1000d6a0710303031841d000348003519164014000c9500503a00070302c10540255450700e8210000d40804080c044290108101281052a928041c002010750100c00426118594810f20854020641c89041090701d0729051154142404418a0440340c01d460007007500e0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 548897257 1250 548896007 548896039
    0x2a04051c080d0b0a1806050406081f0c090b0c0607080c0c15070314090f0f0a05030f090a080f0c0112060509240a0e0f0c0a0207150201090c0e060f1c02 66
    0x1214481e00103094510003541ea036403800106402c606d095800940d000e00516a440741480d0742c1d120002c00601800312082041100c1125507401050780d85080c1c60450b11b5a03649a240e21210b52003001804000c3c0c10160400005681010010f0340040b908420b0a150403401c1a0480c1c42c2d15140854001c02d03002c00020980751032107604500c004c00c80303002e02da229900345a08016a202d400c48200d028074040d1154000e120200401d81542c440d800002552520f0380b04000f07070b41298030080b640c9a000c400380001046a040800c0f5024521a1500061105428400c0051320905101c00c1000030315051040500c02c40d11140c42d060380000348940c102c042d01148a8030541c4001040b415682c020026420000d4071000c800c5219001d10030204180c803075611380602c00c440d944903600346c030000b40c0d011a10070014191100c00e9a10b071001144000241d80465036546148010b80e544078a680e8646941444202d190985128540d8203089030004410780d46940e03c1d6011007000e07800640704e015140702074020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 548898507 1250 548897257 548897269
    0x1a030703060b03010e040b090123040213051807050a0f290c0705011b050601050603040c0e0a0b01021c021902040b040908031e06060f032a04051c080d0b 67
    0x41d24101280b140ca940c3c60720107400c54040c080380c2c255803030700e482400b240f00000b040c45400d0100040d031546030b112141c00c081d0080d0300308000e0002c03a005210070303648003d100d0152242c60300608840c19603055604600318000c0c03078041617070003c6104e40400c030000c00030040d0800340081220068084007107a181c02c40318002c04006201c840401000001035071201c040d2003c90440305448098a400802900160300b442015601c3d801c010203642c0241c00500140c501139000c0c55110348500140b180251301e0300d40354646100207842600a43e5201d0794411a103607018840d43e5072010460a07921760245061000940d00c021400c104220039104c0c0604005546882c0c02402459801400134801d0394414602180194000c6503044d8061108c4c4040700000180d04031040d0040134000e01090030441e40326900e043d2544041c200c030343c1c40c20500c0206042d0341c1e481e40201075034103034071400c041d210342ca040288125030aa0040010070041d840b030785071340054040000d54001d000c00c000c00040c2004040301007a5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 548899757 1250 548898507 548898509
    0x71b0b1807060906141614030c01021908090307030f05090f150307030b1801060f200601050102241f1d2a0901030b0406120302060901151a03070306 65
    0x12060003902808200c1581040f207210803600c0707566628204c00c80d0300d504001180500c02140d16000c40d404c100e000030504102c0c04c100c44003400c80907170303250002d140c40e410b01720303444090040b8070490306102c0300c01c000b40c10041c1da41d800203035a0701031880c102c85503400a04110000700703004248000800c840f075440e1a00703151900a80c0001d030192000c03a540c0030303a501098008484507800607003400721a00075400c080c0c0e01d81381a03020441c4090a10f03424038100351440c43c0d500501e04c0401420080c071940f05000083d108207100080710141001e541402d00085c140403103607040154001440380f0b8241814078074954680d2290a0031554a000c46005200041508150703210319102010040c60f210001807d540d000d0003140000d03003912100910b41c82c0720144800800405603c0c490078441c1480c0d9501a802c260710b40c44009100252040c1c5030b5185003001201518190f0050740480c0030401c0300002407042800d90000310210310940740ca0851441148049810081d0940c5804000300e42d0043c0240c01c010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 548901007 1250 548899757 548899801
    0x40302070f06020708210a0804260910030e07060e04060905070207290a03050901090206190305011e03030f030621021e1507051c0215071b0b 62
    0x322071a52844000d594940b540107081c3ca6000703000080304e13004a2a552008861101e0380624100b9011710810345000c00d0003042910006442580e20300c450004131003503240340d010b03c10060f403280846404d00c00d10044844076401890301d08401d800e0101d10006500048481520b80f01c900e41200700040340c06480140d1000e0040d509100034444c96076008901c0009407200f0010b01e80c80030b055003403c00000041400c058002100802c003003280c00b0b100c0d4020640c018031000000c03440d81032030b5000c12800c1c3c0c040d807140d00030300d0012000c0e111140da040c003030b190052821032400e114000c0d4400410300358020174800101480340b60744018900354020340051000b4800c00390001c00d04060301c1c141261881450104900c15000d840000601119600b5a00d190381009001226907082481d2021005d91011100352840d1050581c210744100c58049101031541c5598060280b07940c0740030201500c080b003d00898180b00d0180655440d544c5195080d82e03555800c421080c4c0c280e1100c541c14103010302c5442c400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 548902257 1250 548901007 548901029
    0x20a0306090b0705070804050111190605011d01050a090e07080a0302030702041b02070302040b0d020a090621080324030a050f06071d040209011403090c180f0f04030207 74
    0x103006880d40652900303805000c594107599199002141c0741e208440c4010050701c4140420b00095200b40001c0f854608010116074001888100c12101080c20210440d09544c444005021030749516003060118081004408655410a000600921458015060b08503030b40c254250991604200b844020324152041d036074024950701300251039500c00202607004034140981b20f640609004c0031044010134507400303001001d0540c0d007008060400220100e070320203441440240582e9030410b10a0081000100010700640f40c15070a03250207111010f41100c1081414038880442c800804590b800310340d41000552008a0100400d811248041e0302c94041c82110200350400c2400101600d945180030111107846e99107650803688441c0c81e01c42004402c800042a80d0b09082903009001c5c0c0d0034050401480d01311040a50304040d80040f00d04034950782c080796071012a424001c0400d00da100d1100c600f9038240c900103124012403203000c1c141a05c040390000c0081c0c2494402e110341c0c00501490100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 548903507 1250 548902257 548902259
    0x1002160f061b0806010c0b0403020f1f0e03040f0e060a09020301171605010c150b030a230d052502190306060f080717070f03152025020a 60
    0x20400007014882500202000303040b9400312242c2c01900100e20030803050356101024001c0d41d80e59034108001074011001d501c00e00130044e1410b0b105200c04002003210044962004501400080540c0c88240c04103001d07400c1080180301c0c1c040071140e10001d84118803401801502e4180104aa030311150784110354061002c00080303202101c4000c076100e6040f814086882c00120307040d941e000001540b281c130b800b003403036400f140c4d0000c1e49880a00340151802d030000900125581d000c0307420400c0410303088807080280091740c0c003116a00388005031281d40410042c03404200051000d080c5201c0c8840c041c3c5200220b1520301d1440701800d00c002c03039180e40234003e402c0d1211420203522981906020440f0741c07504001000c0b8402144507003101c1158202c0005001462528207200300084040030361480b94080da40c804100c40f240c00b00044000d600c103100d110a00006400c0c601e085581003c14103032004040c0c00911a07044011054072903600259800d00c0c92078003200d1168907030a07140300d0001c0d0800807c00e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 548904757 1250 548903507 548903513
    0x141014070c0311030105070207270510051509030307240603060f0612080703110a051906110306180a0b040e0a02010905013608030711030d020f1002160f 67
    0x19841c00b128800c00f480e0f04881245401c15098840480345600141c0c8050001c001081907a128501c6140b030001c0c19010528a0200500540704d04854504541c01c400b04200010304058424130941d0180b8100541000038070310000341c80e4411382c80d000c0c008040340880100c56464030030403021a1112030300c0030030090399603150420180030701001450609241100020b03200c50100c0443e1003c50b4403400d00c51034004656820707551a0100c0c0310715503c0740f040c5200e02300000c10810071200e1443c1c4402d0325208501042c074000041e10001c6500401490003442031154640303074819081140c1c00600d2040020381e0328440030b40000c001c0c401c2403507032040c10300340f004440040108104201038000e9a031822000d8440005640d070318130407030914892002d5451b95000308014408030541e019521070741030300344641c0c0303141c014a183c001c41015106a0740c1d500c400c14061400f040f90701076444040c0042d001d480c0c2d0890f00701d5120b082e50344254050940014010b149820790122035644641c0c840c2c101d0811282d281 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 548906007 1250 548904757 548904773
    0x91f0801030b250309050d0203070c0308130b0a020f062413020f0d091a07080412050405090901021306390501020a0923060a0e0d0c06020c01090f14101407 68
    0x8842034505010307209032804d41610101c1210342c0f0ad9000170b441081545127664009080c0d01c215030808030300c54500000310740c8071014802400400005d900410556030300380241410710401401c030040030b403101d151020340700342c0d100b0024807414000c0f102039010308001c15003180030f0310506540c01140e0200040310091016503500c0b4a01301c40c01600c050042c48a9101d2000c280302081d1080700125103410000b800040b010650740040111510b0060304199030307200441c552102c1036420b0440781c0d40108881c4412000541540300915107803801d00c0120201210f807420541c80e40c200c174000002c070b0002140381e058110311600d090b40e070311078021940c030001070344014070382103140c042d01303101d20008071010700b03036500308400500030b1840105034034034003030449005031104a10148100c0e0400002081c52003c01e018603c0c02d0001d042e260007410105420000041003502a80c00032240e40c1d000003024029440d22194406004105640c04408d04041c1281512481c04651652400d66000101c4108201d189 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 548907257 1250 548906007 548906021
    0x3011701061d090709110409051b031807081009050c0904021f023a0509010f050a170f0703110c0d0c0203031303081309091101081317091f0801030b2503 67
    0xf1510400060700c541c20707203c08680c00d4950301c1450010a1010840603200804900b331150151070449181c550703076115090030303d802c1d00d400380c8070641c1e2004018103201060184a1000004458000503442e284d400600d50004040342101d40304481c42203100c060b4020019814540c404403070724001507280c05480b039001340008074000c2da20500d01104c070204a0103642a2501c95505860300724043e400800210b50940040300c00070100080b10885116143c00031440c1c50040e6051030f0000c0309490400d2015055440468031001021001c0000040848010401a0f500d455628098521952500001c0d03d5406a14504040d0040d80b5400008004040d8001d1650702c404511182ca41542e0341404403c95040c25070140200c1c0d1410100e0007550710414005500c84038139895194605051f44074103c2c055403415007200d20503000110303900305d440d00d4002003400c152015030300c40540c03080010081c0304c024103210083c5004c840c103011032034250380d01441c3d000e8289002d020036845544050018050181 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 548908507 1250 548907257 548907269
    0x132903180709090201021c17040804092a020c09010b0a050403080307080604060b0306310908030402090615160501092108182a04020f03011701061d0907091104 70
    0x704540001607c561540300e0040c1d03030313507921078065005900001b042c41d804002c04c201c0742440208804201c080c0180705214405c2c030786038400d0035404076a0070355082c07548000d0100c00030340d0712003007851960341d44011150b41901d150a0000d03407240c00e01a01522107010796040248a94408010095481d48c0103101c64450f500c02c807000e10145a50300031107609884103032aa0b0350440c00d48945180070000c000c00e43c4040707034603000715a440020303524407180403915205800c5800d224000144070270743c9403180d03995030040001ca4806210403581c041200d00e51040074a20200301c003d0300c4203003081c80307021740c0907044141d00324440508251000701403102e026421003440c0b022a82c4980401d00d03461868008482c1100054010800340307001a0840c1d00c0b01c01a00754240262490308101e07403203500e490019001d0440340b81380c2c80b51294104009824203040d0049019600d80c03501c0e40400c01c00004801080d42440103150207889034507210b00355801d1010039000030440c1030801080c0e0021585080c0140b04441d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 548909757 1250 548908507 548908513
    0x403030c060c050a080f070e090705040905090d050405190e13120e132c0625020c06030a1b11010c0c050a0b0606040f080313290318070909020102 64
    0x744061040c3c0329030107069943c02c0003903040c500050550800c140380030b401017510b092010240c0100d1001400410048484500240000c40c2c01c114a0004c0d000d9103800c248058040e020701d10142d10002d040c0d00070740c03182d6441800c0908141076103e0180b10344101030080d0030001012031400145655404100789411903151813100010b03452280f1034440419410801001d0004d2044d110741240007400c07603006039030300b8194603000b000c0030105840009042c1c0f41c0c10201a11451400801d080e00c0c15550165050715001c10800d43c14803035601180d0251100b070101c60b0291a07845502c1c003a40108a0440c0125020741e9201480b41c016810141005240c0e01c140000e00410301c07081c1f0200c1d45c0d01444407000f0115070007550480002907500059030340c00200542200d003850f50711a8003d11240d0301d60301850032074200244008220300b4810500707020b072409041e0804040030101c0d50340340d420100312800c0c6035110048046283d40c03454600c4c542c200100c41d42140e00b09038840600740014030348110200e0140c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 548911007 1250 548909757 548909771
    0xe07090f050603150402090604080a05010c02070b0a02061909080a090503060112050304030b072a020a05010c051e1009050c1e01080a020903010b090f0405060c090609010507170403030c06 82
    0x319100341284d04c24920b142e100451140d4074810b00c80a9000a03285c99401401800042562401001400030341801b80002040c922005040a82415165003060000c01d00c04c00429078126000540340d038203c045c2d0311000b4800251640e500700241420711004000d00310014032140000c0d440106401554002c800b0b6070440c0c0d030303a281e03401d0a0005540008045820500c000c102040380240070a07408441070426a4440c3c240c101e420705060390700d0344015034500301c02d00000f0550404068900142c2000e0a008600c10fa0682300c3d580d58691580c0351140c0070010302504880000d0502c15950b5000c55100d09001140c2180b0300241c0301e11001c01301c28000e440c0f0003080c0c0c1d090031191181d47d03001c40041c0c441c6480342d102c91356007401030350085d0100d503059900e803144005a900c0311a54035101e040300c40454402c90904d841e1450409401808a19034001d041c0f000403215500c0e6011a444168242421a0343e10103918000100b02c8010201c800400070214000050641180f0b1229040e07224010402002c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 548912257 1250 548911007 548911009
    0x30201050a0510120b0a110403150e3405032e020a05031314030301060f02010b0906010219020a03060e0c0a0801060807090209120d050d0b0904051c090e07090f05 71
    0x8483c43c4108100d102e0a0418031001c40d0701061180c0e0408481c003001300b240b06600301d075200c4d20b40c442d50084810940150459810416503c10450101300040c007a001d125143c000c540c96081d0070495585030041c0524040c040100801c025000504015065400941c000c130b03003450b42e52501c4030310510942c011001c00d207510342e2148222280d030b00300340e10b490b03065403290807120381c00009441c401c603000300340028601c41c50f40013080031718001c0c0300c030380e60311106204e120768001c0c00d441c50f042045016141c1d01043c40350f180c0e0086502480a440c40100c00c49400a50000890928a903440942031902d89101d11103200008694100c2840007500e5500c041ca51f203860b020b080304c0e400c0c0701d0300f40346400c0a0300c284980b01d50b0790020310001078010700300c0307004151803c0c9042c1070140304001c0e41c0c00705400180c0c4851407002c070700580541d04800c4901c4182450151682c513101c44007990401814007030440a40350181c059440d000140c80081084100303484c0502001e4002c03800d40c0034003501b41c0c0e4149000105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 548913507 1250 548912257 548912281
    0x50a03050307034212121403040b010510020c120c010806220f020702090a0f061509050f031c08010e01150f0e1201090605010311041116050a020a03030201050a05 71
    0x8802410114a51912581c0920713182001c0c01d200b442511480359030008008451042d815840340c0210240718002c4411034002d00b07646802070300b03480d5002007407003000301080020800710304480c02038942e0a40e80c134004008a0405800c10b400c90350100c1c4195100952400c001b8100344d5041c2d003030700c0305801502c0d541e081104095560101540d15080801ca5517099002c036040f0310460142d091015091009a50010300341e50000c90f40c01104a688800501d220340083c003030740e001011454041d44c8035a20341d94000b031000016000c0c49001d1100760900c003410761801c102c0d840c02c010084880b8289000340203001000c0b01028400c055503d5000000030444104283d104121100a9225820b2507950404140c540705002501207601c41c220603d81d082203c1c0038001e17555480d20615000403a58154940f00729519244090306000d07034070300000c0c02e1180318003400301c4070280340003400300c4618002d40c5030903440d154040c1c0f0300a4000100c070000104060b01500298011030a10034248503558407101c0d107543c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 548914757 1250 548913507 548913551
    0x131a0a0b0d0507171b04050607030806090a02040513090809030a0c030308060f0a1806150f090b030411010516020a0608040308130302071a0904050c04080d05040e0a0b030a050a0305030703 82
    0x403d6401400200c2c0e118050403010280369500a00b017142003e0b6200300242e807580012000f9004240b00c4420002e00d0714006030240c0c2d0182401d00118103290070903000c148228024040b440c04607035210480740911400b00706580007000000c0c101c40703a520240c504009030046500c001c6012440010103d00d039807902050561386290090011441d4500c0c103034004c1c140c400f507060444405a40c0f0900030a6004044020a4185411b030300c1d5403001803520b5000501d00d640c0c0b54440c10132410309005200004112689a09241d4000d181a580b90000c2204450040c504031100035480312041c000041c125802260761380c800ca0098844281d160340b4400b1046c28510300036001001070b0071000d010301c0302c01c3c1c2c00b4000c1081c1010003a80c15040412402c0414200e40013625000d00d050400b04e000c2201031000c100e5240c0107006850003d0030300d854150170010700c00c00500441c4c1e0741c07512034040c404070361802c100072a100794211080300e15220745828050314980c000d07104500040c1c200038122194111100b9014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 548916007 1250 548914757 548914787
    0x3060402010c0201110d02071a031b0307021029060c060105060313061a1005130b0a050c0d120e010603020d0b040c05060c0610090b131a0a0b0d0507 65
    0x465a55540111010740300e140c0124188046919600503025007041780c00c031620242d030010b00209080210400c074503d051880c020ba00c0408204011414104000880030000d812464030f86a8a60040a1b4107002c0380058103d0040d2501c03845914022601c030000e030350841d85803000c035450000403080c80118030030070f8041c104540c414001000641440360086510441c205580315020000d40d43e142e054880c0c1316000c82040003811a4007290303181c41a0402c8000405050070352a0242500704030340080c280f84102000144c012400c00419800380d421a88a1110314003661030011100c00042c000030f1510382c035010307040d24002d420201803005204c2c66099030303002441c181900c50240d64000c0d2104004008550b824444030340050281c4803240a080c4c00e40c0d00b10081d1129250101c209050070b40181d03c407121440c1403135006c1c40c044d00c44c1c110a88031198842000f103078031800403e5100c0c0d104a0340d5401500441640c50000780e103907085003d02032004007490140a01e440c0e14100719524810180c2c20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 548917257 1250 548916007 548916013
    0xc0607021b121b130c02030409050a0603021005090d0816050709060f0b09060408010507120b04090201140d15080a0203061003110907021c090e180303070509130c02030705100b03 78
    0x10320f10102c4628040044180700610502e6510050442503003503034800300210016070300c0440c00744201038041c09080d9000040180800c2054038640008100c0101e920081c2c040c89070003d445070103074942c400100702403504041102d41d80d1000700a260600c5c02440c0c4142c6060141c80c0000c40c1e440302600078170007140c22005074140c07410305100d0411142d84c001c4820903031140d010000015500750a0141a00c1030030305071180c0f250f580b41205403500341d0b03400b080f10500c1246021400001030380c12020a28540140c1000c00b6102c14200d00a0401000c0e500c1d81c4a203030540b481c400181d0040c4c00120854042d1098054483e10340780c2e0400c00ca80d540040c00000c1019169511080c42410400c5040b80d0100081c4100c403001e00800c0007802c0400d840c0790306400010f000e00030a012014001441503005600c0502c82c11030030009103940d40c0c4900010348140104880010650065651032000500c0b00780e41c00d03001c00c00c008030a18042e581e44e02071207045659015452042410385050b2041c8a00307d8001b03406 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 548918507 1250 548917257 548917273
    0x603080a03020c070e09032206021f09170c150118090206070605011d0105030606090411030a05030c1006080d0918091a06040605060703090312050c0607021b12 70
    0x815000381d000380c62454003030b204204c000543c0e0b082800c0c5050260320f1202c00745035560340c650302c038004410348100e0968003c02d10841c1084116800202c0600850b81600b0120041207091507840140c07115450140450b040407040c10504500b1400500502c8005801c4920003000c1c5508100b0425091280b401e82c04d0001c080c10034085415000304090300d200a0990303151060955542c0200c030020b800014081c00c84d407165640103001d1030069805014100c0c01016240740141c00207403428001000140101c0c041020705006480c208201090079500c170003543d8031426104c030310703641d01c08041e80880032480c2400380005003603401141030140b5001e03ea66942c00c0d281000340310a0001e05c12000b040c0d025035101361890200c0d01898030b10b40284c5e041b50a10606081840400003a601e50b40c0005129901c200200300020350040c0c8403004503070340100d1070b44500000300408c0c0d81e2400303038051644180c080c22040200b40f5501055280c40103404013981c0884020704410b101c1031505610b802c007419480300b15 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 548919757 1250 548918507 548918527
    0x129120c09090a0b010b07020310020c0a0204150803070b2e12030909051302010e010305102c33010f031a0a180f05040b041523041203060308 62
    0x180c0d03640c44a16402294484040740e44c1c0d5a01010090307104050556001c5000406c5240501c159200d2032580201035041210070041c15488211002001388259940c00303640300d900030704008074002441040e00741c0e9103582032800c140d01100b100300c90541d80200303007040c140004041d0741c2c101d00d8401d140502c04041e0700d09210f420034071840c4529095040c410400c4000800c0d150b1405590700c030340340031008581c1a8000b03200240038024984002814903051a0400400461140300301045400e955410104200c20100500350380301d0380c072480100600b1490070031082c40702d40300d060701c1c001c504c050417109880703201a1607503d4400000440742c00510301c2c4205681c03c43c03081d005400c40030075589001007104059000103200c84e480c2c2c1d0155810341d281c0f5003c0100c881040c415019020000b040a008501d059910302d5242070000700020220403030503940c1d1040131225449031440100000f04490b1003100c0514609480740102c3d41155080340403450f0440491183c0542c100302d80d031020603d0304040c42d840d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 548920863 1106 548919757 548919769
    0xb0703030c17060d140a030302041a0a0e01050c01150905070f0203070c05010f020a14010207110303180405060d1a07030b011e0810080129120c 63
    0x1540120004802d540e40d00010031583c880c801012031030040c0446010703610a807818821014098201a0540c1c000c1054903824542c0c0290105401e440400501c00c0c41e8180000403010070075025954020800303403280300c02240001c104100b01d840b900d44400e070203074011320407540c40e08140210f1580203218509041491b2024501d0134280f07854428941c41c080c441d071810000f49109200e01103100b0301203d841e460307101802e8244208550100c0b400303504a40b4041e0b45181d2017609003441841e002003104c140c94460301c030104003400e50724200002800014082500f102409280c100000c80304009e03940051280b0304514010b040c8402ccc01404c03280f001401a0501080741d5120114000001221204140c203180c01c40480d9600b490320581d03004e060784841080d40c01c14024112088402c9400d50210010190700c515004211040000e0030303d1406801c482d039000031150003111300b044 = true := by decide +kernel

theorem cover : BRFrame.Cov 548741007 548920863 := by
  have h0 := BRFrame.cov_init 548741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 548741007 ≤ n) (h2 : n < 548920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
