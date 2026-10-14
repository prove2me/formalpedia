-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1866
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:57:27.950118+00:00
-- url     : https://prove2.me/submissions/a6820172-3bec-4009-9122-1f076e0fc529

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 335431654 ≤ n < 335611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 335432904 1250 335431654 335431727
    0x702120c120a02030a0f1106060907030207050109050d0e030f1213031e060e03070c0303080a021b030912071503021c020d0b041b080414011b03091101 66
    0x903000d019908001034611000d40a03034401c92008000d604040b4020048030f4202408180445030740c00c109130082906e001d140d1b117550000b440244241001000300e2111032090781036070a11503001d0020020346650303050282d074904000d81804002412810911610309020070054070b180b13801c0c8010010340d5054021511981c10881c070024131404500b50010205080040d01c5162020b82038081c1c0c001d5201c1c2c107003001030f41d0510136050010361003000070741c00180100080c042125014031700303c0f103079456142080019205481181ea080c18104101403414140480100024002103840442c140c40e24403800f6141d440d0f1703200750340892a40d407002904a9000340c00900504d0412058051098901400300b0300b203807c40b94106210650707030a05120a400c080c4030711600c5980d034091207038a039500070000030705800d8004c00040000302d5480f00e4be01c02c10003d420115405000080c2a0b0070303104280e0000740106051002990003440d041c050800550280003403100750300080b00e0740e01c050202ca900e1000300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 335434154 1250 335432904 335432917
    0x1031112090a0807060e0115150e01030608010204030507050315061e0409170c0d090f050f03010603020d1203150f060827010e060c2d0d0f021b06070212 67
    0x2900801c0240400143c0d0b400003800803910030680060303a035007505483d900712115a600759644004100d0300b03100c503c204e0366040e44041150f142c207142d9103000900480c0588030fa40d020b20035541c00820007100f001f801081880540b00280c040f540d100e40f00100442600402782d0b04141c000142c0b60b44841071860082407055080c1d0044c2001c0b4109642c0c0d0f844c2035100c056500201900c3c1700210308003075502e0041c00390f060780f540300d480d14030641070410641300c9042c90684213140c41607064101c42c4159840030b400680007540c000708840c2d603041040c209516990070001000001910309441c00545002000c09402074440064100d0f014500f031140c160381c1301c1c0018008030b05200180e1009041150409012203004510070f0020030140880d54003a86440000340082d902d0020030700c000b10401c440308203040382d13250713040c180b05480354560f50000103184660f828400d82c0304d0915009910156141e001000c4e440542910946000011860207803503140540718040180c015518866200c580b21014101 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 335435404 1250 335434154 335434171
    0x8150c030c0c15010e010303020f0a110d05120304030c170a0c02060304110d0c0f1d0c0f22050a330e03030c0d0201060b0a02070e041104051005090601031112 69
    0x110309980d070411180643d0907030007000684040801481010781c11310a40d000c00c2e10150050189661583c2c682c8040245000e503140201c160340e64107014400200401441021800e05040d41c905260400400898001f4030a480080000d13408915902414044030915540ca0b5a0405c044c9019402c01c501540054030641c4c1d00103c0701c84900b481e03662800d111a4242c03143c101414070600e400f412181800142e400044645904510300ba42e2202c00d02d078050f40480d0030104988d440c2d450514001150207480c00390903001e07402803c0d00d085401032041e000143c443c1101d001e40001e82d41c1000007201181100c1c200e400d2215a50a01b02d80441221402e40d0f0a0050403c00c40b44406480424995004082e4420141c0e00150448201075021711600026207031000200f480d0924042c0701075592282c0784958545c44c4640000642488115160007140d5a0000d02c2440306080144403050b20b40300e83c3c012039210301100c0020864640c000d01c5900c0c80b5442903000305040540420300d2880d4640d00524088 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 335436654 1250 335435404 335435413
    0x1203020c010509010507030c02010b011e0c0503040b03150904080a030509071a090f010807050f0d060e0a020a090504020301120f020d020910090e030f04090e011d0708150c030c0c 78
    0x48200302801400c0c880c410b441e0000456140c181070040649505008050030359144c005682d8140e41e0142d052418640900c0b501c003603660b01d0450407074402d640850007400501010401042001342c100056000c1d000d584400003036030140340f0401c0440c040964004002800820124944c1c1d07001c2e40125600040c180c090301d00c165622030100d940000d51040c042c14203000010304422604e0509812109042c0a1801e56401d10f8983c602400768491149056240c110204480c0c5100c405908500054108140c11045508281040744040c0d003115203150042590f104c0003040b00c1c10b0a100392812620305c10401001c2c041107807102e0740740341001d03c4240c1e000312807482d0000150300d922072964022154920303005a03845c0307800c0e075030780071102c40c420350a42d0741c0c00822110120301c044006580130f4072440c200009600840c0300e00c481c01002c074626241750f110b0304280844034061300801c0c5141102e0016060392036810404416246043c411502c83c0c812010a1001c548900c1d0b000d000382002002e050103c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 335437904 1250 335436654 335436667
    0x9110324030d021f0209090f0a0b04060b030109050a0b09010603180506130b10031101050a020a170c070605040b07060509030d050103080322050706110c0604140f0307080307120302 79
    0x342801026220b01003d64004903008010062020004081d0f0004010442c1854501c00c0040c0205d0800707800d0488a884d41408501c440e52039900002070904c0c000c100300843c55407100f0203000c5410034031400328200c2c549800107901c90f580307028265402c1d42c0145aa400d070381c02c0980a90003040784010b0a41e14007000150100080c404215190007050401c291024201a600d02006a030000038a80c130101d5100d041c0c20400503401c10034555001109003401c17501d0f5224076a040713180460008016182c0c0f405038007020f203082021780040544030860030998141946aa03003e489612940c41076a6155900700201c002040080d480260400001410b40346041e020103004c8054600a820075981200c00005008e010030034451902c0c0034007804150302d95200165164541c070341620340709401c02d10494548845800b0000e100241a142000b000c00352580e844140c406016100c00490501900c0290010146480d000980e0790459411100840c0340156556074400954510012001416000d0000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 335439154 1250 335437904 335437909
    0xb061003021b0703050f120d0209041803030b01020105070c0203030f030a02040f0612060f05010509040c0e0315010e010b0415050a050f04060e0f09130602090d0609050d0909110324 79
    0x415600e840d00c0c5008083d69411030800c90b08059103c511451a070344000c1d02003103015201d4040d1184440c90082c010313100d280701e8002c60090288a03050364085400902590205601640b00c038003c84420790003004030baa58424240c030382c4c0c1d0208001960590041c4081150001c01c04015503014121131409030030190350754034001c0700c1c005a8100001041ea9800d2071800030400b407103403e000f4000351801454541c98030b40041d000d44514411a03008a458171030f09120340d4002c1a000f0001400981100c24006000c0071540700e016003030145070744060304080006803021446090f102529070886081c11010716101c000d070784030f9118400324801d01030244919080d18400380c000d4070090540c1d44601c003401c03c1480422124a0400f10384900c21424042401041458003215021280c1d010030b0050351102017100151501ca03095030010300842c02e00c40c850080000c04984102e0141990311420800c5444010003015504481c9464071070150500000e0001d5114124070421501d4108503000c969803400e01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 335440404 1250 335439154 335439187
    0x150102510a02040f0302100e03060c04081b10120b090c0301090c020106080309010507030201330b0702030d0e0d15061e03050309091e0702060406180b06100302 70
    0x200e4460510300024061a5502106a10341e0103607100c0021803a06003000c11100d51400c25000c041e014040075080003404c58040c010f1042c080c000101140d000785440d58038000154000d0080300d08900a4001112500f5000b8490722981e41c030080c400408c1840c0d108044800403480030740c480709503468138040131313191302c0c0c04040d81d01644607141d03410356039030600700d01c1816120b00500c808110380c50b04d01d00300103901e404425555805002d203082e0b6038800d0207007070480c05401100454402c5003c00080015031030740303100c000b80c190007009195103480b5564030440000d5002c0c901020b501a000900014101c5200e141001c50b00c01b0001d20f43c00d2091150340f2490b40c601c000b00070307001a9581d116000c0c000340c8041d0034030080e504010b5203045840e0703040d0b03943c9640300d003e108407d5010ba04c400d404545007200d40c1c2520545822000000250b515019500943d0b85209031000c0e00c10134178285090070a04085841c11140c0c98001a00035907585400080c000101038031080241095400d201805580c0704216 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 335441654 1250 335440404 335440513
    0x110606062d0d0507031d070303030c120509010b040e07060801090213121203181a070507080f03010303080604050103050d0e04020c0703050c0f040203070206070e0301151d150102 78
    0x182c000303890703e480d0310090220784c951141d0f04a5a1104445148086400251a010350758036103030100d0019100e8a0a544140c912035200d100f00d401e1a007008141c60055008410747d100407542803081c07c44a00110340c503a4200d014807030000700300e0001406000300580091000880c03628807041c6055440f2401c101750304210104489d0950880705504107940c0c14060b1020303091003801140c001460a0b520003030303400036801c0c011004002c400c0019010600403820b80d07140d6504540b07210340d13036084a8040156035001340400c9010500d8031010440310300340341c030419041c3c9501c0b000801c04441e001c4c40603240c4902000f66540d115408100c44405200c0c107221500003503100d40024400040c00310704100380c1c01c03a0380081c0b0b03001e20301c14003c004500b030b030007e08507410030850700f84144039124010200e409401e1805890240c03188081c00040c009900d501c640081082450400d9840d8460710341445c0c180680d101004d0040e031000c2c45000c001d28501c0a611004000f940d50301c2c2055451441c1102c00b1030004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 335442904 1250 335441654 335441677
    0x10f121109240f030309040e071a070309150c0b040609020604090e0105060f0d12020a020303030403050c01152d0f0305011d0a0b070c05100f020a110606062d 69
    0x8800e440301d0b107409622201c00c001e804641040d040714450010982d240585001284990341302c03441e81d0021039060154501500f608403140d90032084601c00303d0f0f16503001d29400c0700054104003001403006d190b000200310040d2a903130f4201820020b505c917245003c4002d00141c0f04685e0740c03405a801661140000c0009140940380031824030f00f910f510382c0c21204001c003168054040b07a200006265980c0b54068007040c5d0125035076420348031b01c42c0304a00e4250714400080d010301c40002400145034110b0050300c89a048c10000b80f02c0400908001130700d4500310300c034640c0c2d01440e500c0b5454492846200341d107071040c80114042d20107580c640c0f0703034074480316036034800e0310303182d40d90103120f084042c1c0da403000f03c1c4107a26400206409003a66442d41140c0c01c0c010300714020040382034800380030080c06202d14101200c41c19420700045160201060083d031007903082d0008148030013404800c2c4403001c10603620400009160310b052003020322a130300c0303100790380070440d08038101200d61100c04000030000790144ca00300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 335444154 1250 335442904 335442931
    0x11208091002012f0f03190507120c050c1f0b0d1103010b120705090a090f1a0702011406130908030903071b0b03040609030e040c021f0203010f121109 66
    0x1a40120084104803152041c0110135140d03290600035199000c85041c0901d540d5a07694940c0e0300840c102c20100c5400122107800d0804003440318156010b01001554240c1e00360030807480218000559261141c403a0801c25a00041412405100700550b9140d10450092010502d00025030003e03941849100c402c0740e1400141408014a050034803c41c01c0032074041d02c2040d038140078944119a01c0002c0e10459220303582e8107001610a4a05421480f0681d91241c0b00c07001d8648a441d1842c124202e00381c004a21011040c00511800e2050065005d03000290001700b183d80c803020140310038110600c040840040d22000314070005006c60000314412921440038649400042c5080110425a0600e441c08283c205409000f140d082c0c004070b03a0082c0c4c1c441800241034840345001c0e03400340d9a0102890780540741c100b64400351a004510300c00e01040b1401703030400c0030300d1070413a0350701b240003e000c2d00d03100d05880c4000307000d0301d1503803010008072601402e48550303969000000240c00203030407a9060342d500300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 335445404 1250 335444154 335444171
    0x308060f0415081b030d050d0b011808010b01080603060c04120f02030a140f010b010e0402090d0c0605040302041d0c091905071d04060503030a0c08070b0a0203060319020901120809100201 82
    0x62000d1110340442c13040300540240c007110f102c001d100d40500107464119590f18058100e4603805503200c2e5080e44c54102e100d00d107460340c6245084c020003000c0c65a901080d56038001a00502e0080f80082c42111901e5100b401c00303042810400b91003c0b180310858540f980c9003208405a80c040002241d800e2081d1004030906080c840c90a0074115404d4455140f0b0303040c40d049a04680e000813280c25856002d07140180c4030304804c00054415285014090954400001e011881c01d9200c402441540c1c000c1e10b0500000e080e44200c51101c0e0b450608151664020804500300c81c908112150f410000340d88400d40040341108034032088031000d98074074020462446044941725200307015030310740b40c6003210204074681c43d00020a41f2403041046443c20041d0f02c40115040001c0f810540341010b402c115081c140345000b84061340254400c0e1680c9210340301d03645800d04818010000c0f121010342c003500910701039280071000c1058559484007100e05100c2440710000c551104800668650f08580c0007080429 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 335446654 1250 335445404 335445433
    0x3216050d020a050307110d06090b01050a0b031614250b010611060a0b0105120a060e0c03040519020105041e0611010c0212070c050a031a0705070308060f041508 70
    0x11810340c018155000246403502050022003680c44041d045110000221150000110903280c0400002e0101d46401043c105201400b950f15040e1081900d45440c0391707031035810020395030000719950052000c1c1c00541210640c45090f03000200050030b171102d824640a05290307005000c00320703c0101c8211046c4604410700c860903401500600b02410010f40b500e9040c0e81b40754480c3d8005050800c080e40700c110f1001d04d40d200f081180ca0074140485181e070f00303083c100794001c0903101920a450883c424840443ca114210b80d00b00e038041c0c4d901c80002c0036046443c4c03a020b2a00c1007040310a90502106200028800340000c0ca5907501c00329075220502c00b21b090907070140405050a05c1300080b60b01d4821104952070700091403182c02a0209a0682c450b00a07241401504443d40c0005170011001b01001080000071503014030510b00e100c0384c106c1c1690b91140119114001d60b04090300156049021420714204001c0480c0c40020140021500b440004400c140c4041c02e0b90094031300d80d220541090144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 335447904 1250 335446654 335446663
    0x4020c210c060c070b06011d040e010608010f0c1d0f04050405060f09010204062f03041509050117010504180206040b0711040501050306040b0a060812091807321605 72
    0xc80e042c030070ba0800300c03907444171141c8000c0100541e05220310340c00c0d0300b641c051501050381c400c010010070a05c60144000b41480c00780c040c7e4402c074800d82d82080404290180c0c14000c503907001c0071326618007030f00101c4c025003510480c0c030406a09802c411001c044400b04e880358010749100d24040c400412a9040140c2c54a40d1904018001d014591051005011140c0d010564070705034003100c00420200081618a003510b44089a202810752000203000981050080b103403106201ca552204607000d07a0760b00054075454031a900c2e119010380180014480f51406510070605903821281c900803e0744164003058843d03110340c02c01c50b0b24140c00b040c2d12041003003204c06041c840d0425901840594502008079075140d01c0a0801050b207854100000c0300030301c00d64041c00c01494140202d41c8a440c000c94140da80303900403c011801181900c0400c03440900200e40180112415524103001013100803255045e155204020801e030010341007070190300407400c0081d200ea484160040c4c102310311035242c41841c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 335449154 1250 335447904 335447911
    0x30305180a031e02190303030902151c0e011806022a06040605070519210b01022a06070b0901050108120a050a1103030708071b02030a0204020c210c06 66
    0x304000c040030b00c0042c07008010011003409550840d00e40791400d10000e80006040c1e030350304091344406003000040c503a042d0460480b02d402501c1d000c561241d5403078221040d04c1540720541c6101d51455140368900c481c0e500c00100c1c0e2951400005035421054000b0b20700030059041540c1c1e05402142204803011607586d850300004404905400500d2800305981d01c03018014005050b4569500000740901d004100b11891030064031a00c111905010354007400d07916402c0d8524104095001d1084280c40032441042036010058004158a60850710300827021800c28800044549c6000c50362441600c0d004058040c0790f10528110413180703000d003072040c00c440301680711007080e500c0300380800d41c540400c42c119154021a486c00c659240b070340c041c2c1a14245114401c0d18800e00c0008108050075034070411560150000f603440034410300c1800c2c03802c0b8110304113101c044d5254000c80c103280b00602d4158001c1421001c01c2d415181d690136041441c141d0a225410760180d01000010844100c10080c41002c2d0b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 335450404 1250 335449154 335449159
    0x60a0602161404061806060e040b090f090715210506060418021315080912120a1104120b0916030b07020705031213170d050d1503030518 60
    0x106140d41e254040c1c207a00580c07150010b00c6000001c4244a502d60b90088800703030014a41c0200300380541d00207000208101d11501c40060203803e01e0011615160166428041004081400d5070700c81500c0f94892400107090007841740b1654000103004044c207180758401c0f40c601e4507030300300106581c0e500800001d4810f0000152618001c1081066500c04007520f007942c0020040c100d08481046e0204028822050951580c4680100003d0507800d4025404440000f5944610144d02c0c2d411f99155901c404402e200180314040c069003281060707015110360302030044180410040c0382081e0309502ca5106401032507900805205450038044a0003280381c1021585000703140b4414040d05040601c101400003c003000d070182e01003203500d44200a0100906401029105a0303002e00c2808402039004500940c8100c04102000a89150080c8281480b0001314082e04108025003021501c3d40c0c058215032070f8079a5260040000f18001041c074401035031094454a40e2110720b850f142d200001041d812a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 335451654 1250 335450404 335450413
    0x5030a08040e1503072d0303091a0403020a1d0c030708070e04150612060b0405030a020d02181609090b030c06030a0906180c050607080304121b0605060a0602 69
    0x80014440c00122001c0b2205181402402c0d1100b2051500b800e0341d0909040d4580b188440c00b0070100c0c4410044500c014404e441c41000900428280c594500d0300e220182c041014010100013040c400c6887d1940d00111605007460141c5960015541312a84c0d0030009901803866144150090411030b096013011031f00b26064218508050010300c0c51000401d074a0400030002514440c0b92a16040651840005244440110f4035404020261008072881b007201c103080000028203608140101c8040e10300c0680074000c07040e0706800b4043d00c40c40c4140b0481e041001d5884268074145504003283c06081034649041d4440d03103c120040810001340c004610462404068826036580040c40c0040204107407921922965808005801084080000341c10707a0305180c20070941d00e00400c6200c4202c0d01c1102d4030300b545500c0d00180400c038010309000038403400c82040403070046100460301244e0062207140c20304545980c80100c0d000480c5d402c000f09c4005444106000d5036240c42001c2c40c011341440d20007007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 335452904 1250 335451654 335451673
    0x1202120304120e1f0201090203010b0d0209060909030913020307080f07270b070c1e181e0e0a0302010c14070b09010603020402040b0703230304020108091e0f070503 72
    0x20b10354104220001003e03c072003810b410781d003603c407099a040d034000daa02ca0351900c1208400041e020b80030080c000c03842546420030507401442d10020900f00e454001e001442d50359221424405041d801401d0002148824042c000d40c503030ba4102030f181707001030918015071a41001e81028202c1c28015201003902c8803000104130b400e40c2d01100380421040c40b50041c2045a10680f42d940540305190801c490340c1000140503c01d00c20505800000c4034640240380541c921801401c601c0f00700380b80207000500031440c41100001c0400d803c401a90b135003450b4124034002064100300100c600811800d00c0940107030080009058080c490506442c985080909400d810040c4282c0c1034800c80d000200785c0420b00d800309a080c082540100003543d0f002d0411540e1f5034641d03100541a401c410401c070001011240245070004101040128984e0340c0c3d0b000c107003903407505d03401910600070041c40403800b4410111808840001603c0c002d0b040360b81400500610760308a00001e00785645500010f000b0303072001206 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 335454154 1250 335452904 335452913
    0xa12090f0b0a0503150f040e0a0b0907061e0e04050123030a1e0f0209040f120c0c090f021e0c07090b060406081312120501080a0c0302090703090f1202120304 69
    0x403aa840701001c065405d02c41000c000007202d0102d4101c1d429002032a007e510043c07039100140450516024000402c11561042030b040da46059a004420010794009510141181c1d514031002d5400c800741804101c1c43c2c1c481001c90700b2280c1c01d900100075808020080c1c020940002441102c1941c1500908840607041c0c0710b000d0100409155030b0744019a9603000380c00e00101886040c0015030061a21072641468100030f40360b054105416030b414030081010340c0003107014044010200da48040b2034a00507180c10618401001407504c820748490702040389104640c0ba80d14901c12a03000510516141c0010b01001442d20b5200c2d0071404141d440d0080d030307610503a2203030b056404480e5246003a54884d556083e01e5917400c48012070040804861402c0e9283da80d410080340c0c1c4200c80d424604010682c0e940300c941d9941c09840740b0150440d00c0340c0c4400c0c00035040007001c05500a4540c2008101c181099075850b130050a000b82c1600c0c21035040e84100d10710346d03062201085120340d241d00241142007980302c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 335455404 1250 335454154 335454157
    0x30a0212121204150b1e04060b04030b0702060f010303020a0201050a09120606080c100e04091e03020102040510080c1b0708030f1c05010305100203041e03180f150c050a12090f0b0a05 80
    0x41d9480c8000030b00c8046d84481e0383e0750b006103020b03103c2204070380d440e20364a241060440c1025989103015024000010b400801c0481c1000d0490b40c1540c0184041c1e40d20b50015155607101001c180100700f24450045210001040c0a107560b51103180b001a00360320b080c1060b030905442840b443d204c0e203c142d164850b460f07070000480c69210310444000819882526040c0304800e4840c100c103184208100c00d010600d50198058000c441f0181c4d00d150410b9010101101c07040760498030410112800c1c010001c5002144d0a1407800361008011110f40da40c88181107031441c2c0141400001c2d0302c4e00010b00c0a803080c003900349a03c4c21041d200040c085941103590f20f5840d882d190102c5066140d0110000d020300400e803a052a1010302414513042106c0300342401000c4c16804401120581c000712000070b90380c90150036190071070703010700c00c1c0301284a5030760f01c100c1d9102203401054505204171440d0402085000f0398400920080b45c984074000c0f0b1a0090f01141d440b0140d0042c1c086190a000c945a80e54101c0c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 335456654 1250 335455404 335455429
    0xc030109030512010b0a090e040c0f171c0504090f0e01090b190b13090501060b0310030c050d0215031302270f04021c02010909020a02010e071a0301060f0c0b0406020d0b03010b030a0212121204150b 86
    0x40b001c47885000000c541c40051851200100c220360034007090609002c0f101006034024030b09841c89020021500c05100165410103040d15000029000c220101d81e0581c0e01c5143d03168410b00002c28006c1daa02030178034007900b0a03142d040b84440c4102c010000c01801980c2d0800402e425160501e91a0312500040c03101d85903400202d0a107080000066065014004020905030f80141808580f5180f00001641d00b6040140500303608000320200e04088040d030900c074030039540148503206160920300b1101007845084400c9051140c10301000c01c8c2c407000713070028207038280c1107178000112880302e4a4000c1c0b411020b94000440c00207032485912041c0e210904990640d1042e0509450502c508241254607d41845001e410202803109001c100006a00208008140c808003402280040e4007010700321140e2468441c0c1c1503201040f02801400c041041c0748910200d0001e070380c00501001c0034403149521210448000451500070081003240388100c200010308030704010041c0c5895200854401800070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 335457904 1250 335456654 335456669
    0xd05030903011a0a09020c15090d030b0618040b04020d1113150504060e010e030f0106030521120408091c1719110c030109030512010b0a090e040c0f171c0504 69
    0x10392480c520008004414074010419012561843d100c27141e207450301045207400002038102020481700d460044259928240c1c29040580c03040c0040303041100030002100c20382d4002e0740030301000c00590001c0c42a04178400e0000d070300e43c3d03592505c2040d50300c07000d003113070130000c0c21820b5015440101c96203c8142e4065a0003802e10f0100120203d00580d090001d420902e030341841801003c904011341904110b0459114504881409410240740b840e2400c4004032064404c0302401a020b8401400203565002401103840500d0008040041050300004030100d501308003c6020010420924041d25880c25110031800f070304081480b00300f1802480005280c2080100a4054031041401482101c0d01c010300200204054102498050006c0e08120034207403a01c0c0050000107100c0d1181c8048610385402541c6480d0443e05000350300c1c1300701070041c0080d074a404034000302254003203881d0140b5000c0d00d203c5600000341c0ca49011014941032040349406420741403420030b11080381d000016241540c005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 335459154 1250 335457904 335457907
    0x15120312060b0406030912020706020a29090a0b010504090b01060e13050711190305121003021908010c0207030c0506070317150a0e0601140f090d05030903011a0a0902 73
    0x9001440010300303050b03080451003140c000fa000525a82540c014000d4a1084001602c805607002c410f0341c80e090720344107200c0546c010540e10360000e41400512008540e010007001d01c0140507188903048200e040361040440d512500c109001d000c00f01408600501d4200d40c02d000701d6043c0e643d00c81000d0018810b00003880801c00405400340c1e6040d10407040119411070401003441c14100c0100491046c071011105030051810200103d035a200601600310340540f111803510410b461300126201c001022014240b4202c0c0002c0700580d40d035004151310030f44841c030108900e0b041107421405c6078102e6590348290750100c5010400260081007840c1121021101191604014207054800054044d80d241d00c48490030101302c107a88004242041e07038601991400c9186d501c0340102c1183c00003d880588c04a80c0c40e03042c100c07003488880c004007041d411100c01c090500c48404041842020341c88800c841079080450010900d003400d100e0380301407444000504020100ca8404590120078600415050f42d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 335460404 1250 335459154 335459177
    0xc0d020703020a02130c031103060d03081015030504030f0804051b01021f05040c0501020d09210b090601030b10181503050f06010801050a110a0c140a1401151203 71
    0xa03c1110500c0d40c001d040c900f130816440c808a401003218181800100e842d051080d0344d146255815288143c00c081c1001114454603282500c18007002412107414100825021500d2441c07210540303c80394075030310f022915045c1854080c0061200b101c8800400800004020129200040e034011400c10008009407502c400d600403400c04854401c00420500440140042030b01543c0c4064496030080414960942e11034004a884661050304c4000042c04554184400c4104600301508007105106580c00c0010304d9507411640501144d038081aa08608010000e00000125140d40500c0300142c44000f2410b02c4280705000340c0406440c00515901c81a18240b1800484040302840e00724085034105c00d59050700301d584030303c2401038110715420f107400b10ba28510b150065541c125401c03080c050a0902d0035004580106c100d00056501d038148044003c0400001c0c817070640080d010701035140b00c4503102c0008a0942d9221041c0c140c0c007201c3c858003000980210103038518903d41c1031034506d13480b00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 335461654 1250 335460404 335460407
    0x705190917060402100509060a2a12020c010338090c07060e0705090612070b0a02160515041e150c05010b0f0a15020f0109030201020406080108060c0d020703 69
    0x24410740016140380c240d00c41e07852401000042a82c4103d108880c006401680b113181218140212214140c02103c24000d1041c181d000715903e510b01217504030101c3c0040b680c43d001c01121014017000b91042c1c0141146404c00507030500400342e60364420300703050001d14561a80701244074198051010301c0b40070340000c42c0c02842c41c0301c0d40d2118000b0040c403107402400c00d108016141e41c0b100b403003290128a4804800d885450100d0307800c0455400800c520f60707580d1400c0074040041c0c40f1400549150151000105070350200380701601c410030a9500a010005007110540d0800d8400d401a600c0b40409200f528001c03401a003c440556170300c0343c8194440e8505011b050f6001e10b40b5004203600b200c4500c01c54154650209191300f06500030310007400640341400038094070110b000b001c6500040c81c82e03801e2140341000c05240c001e00c00d4501c1115000d032060b880b1942102c9003800d00320010b03500041c042215580c00504140980381480140c101401c052802200510645024030400c9801180004c18913 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 335462904 1250 335461654 335461667
    0x1e240d0b010e100e011209050706030f15031112010614060a0504080f030327070b09011b0c0312110615150d14011d04080c0705060406020f010b0603070519 68
    0x60020b084102c070192040800380256205003511030002d42025401a09118680144072a482d04100603091a0381011006c03000b4080000c0001030301a1681564003040c0c42c0081990025402080003f6201c240c03942000301d01801e0301c0e806c8038141c0c10305500303003d20743c4c41c90103410418030100c07035042d540c40101c1000d4500340115801441c4a0051011240c1d0000b8040000c61042c452080c1c0741000c43c3e02c0c0d1038030b001d0400c01c1c000910902e84c0700144c01d0210402c078000900d0703448014101014000c1000c0045030110a860b44211000255142c04004016401d60441c1c2d2003655030418540a44001010071f94604001341700f801421a494450411900d40c0001c5c1640000c642d000650383c1e4032800041c0025102c5c0661210200100c4000041d40e000c17058221074542003041c0001c4515161b030340300c884a0b50000f14018445008602000420380d0b01c0c40018001860f058028100c0301c204c207401c0500319025045058003410041080015140d4030000310b4001e000c1180700c070704100328082002c440e81c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 335464154 1250 335462904 335462927
    0x90709021c051f150816020d030506150c1c170c070c03081216091202060f250b09070e0403030c17090312100b0304021309021e240d0b01 60
    0x4007201c100d01040d40d82040110049030007003a15102c410351121202c01e011500b03200001b4006802801d17440d01001d00c660001d542004000706800407846100d51035414a5000164041030b0740d000c40802c9402d04070108000d4604c4560303081200000002c041e0b2800241001000704207101c00001c0c0200400545030300c120b014540000001e502c604000301917246403401500c0302c41341c40b01c03035480000074188281c2c60042030b03409103082c1c50301c4003220381e0902056803c503080280182105001401c6807460b20041e06c4202070050350b103010711100604200754441405490380502c0d42140e10144a20320081e03400f150010f5040c0f070b00080c119a2030751300300d90810002062111060032a000e00441c110000080c004003c0980b6100310291078440c03d0313040915003485006030301e24043c0006405441c1c03c0c200e004003c41c50080100310380e03549900085403102c8890105405448540304600745081030303000d215049401e501d0703803215900300056a12441c0109981c00498585442a02c0300c0c43e4403030b4101d03084 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 335465404 1250 335464154 335464201
    0xa0215011508060d0c051c050105070f110106030b070c030203090a060e130b030a0f050a080424020a0f060f0b090a0c0f0203030c07021302040506030a05090709021c05 73
    0x1120358640c9001d82208581e001c01034009040100400c0f100e01d441e8842c180d130a5448141880b510380392400717104903a5411000a0380d240c2e910300b20440414001e014080c824181540c0e210300703821a502001e0115152010401420303072400b0720910000c3c40101d4a150050094180170a50214920b000c920b103200f214004c0750001d589000026240342c2107207840f900d01d0300484007016140740d024408800c0724030010440307500d64000103280c00843c1c242410700d145d49014205596904c0c0e146d07119100a03502c00c1d80400640c401708507440b566150b1000185c24900228809007044216a80f00e00008078808000904529680d90700c01c04244502d6124085540f0090402d64140c80e10174019001001e1070a10351011403100742c1040c841d58404811a4403906c1111a804e0038400a502400080070380c401c903a48816600b0000403d0030350b02c010141d0710542c1c502c940130419140c11170a0782d041c1440365000c404603a0041c402071215010b0302c0f001c4002e4013014440064143c0d2043d03135940388203010001805 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 335466654 1250 335465404 335465443
    0x20c010c0e030d180302060f192102030f04020906130617070609030819170a021c1503080705010b060a02070e130b040308060d050322090209030307080a02 68
    0x1150355400010300d081c5035030220300f41e450300d000545040c0d4000030780f48081032000e1503014003440140b4207080540010b5014042881c1401c03510010460051043c9040401040c0d41c410340c55505008210700301580030590f0015411418002c8004581032001340c0028400c00d10b07040003c0b82a02d03030700e540304500020418103100507a51141201381004c4078a440402d6402070000c08210103002c0c1e001c00c1c0c1240c3d0b11601e06403a01500e41c40c6840c0c90342101d1100c100b00001c080d000c00400410125040c0600d01e001001607607072141032241060003a2020088110764249401296280312020780003040300d800115059480b0340350300d0034500400c01150071543c4074001060b230308403442d80003981c007055500290700002c1ea43c44060182c11038003184070000780040301203000540082d01c01e281d0a50040b0001d00361401203802c40d41d40a085800c101030800b6554070800b128500940000c038604000e00310000704510b40f102070804030b5100c1c491901c024003900ca0004100c50417900c02c2210081011407149070780e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 335467904 1250 335466654 335466671
    0xc04050a0b0a050405100612020c06180610081c0203090310050423030f0711090726010b0f03061306080c0f060c0703030806030a051e060c1306050706020c01 69
    0x4100422509107680d009184009001c10207007000e1151034002c0c0c110080407031100740307040030031038900f1000b08108082c5a000c1c020009003040800c4914007891680340c035100308030450180306203040c000800d589074000550004110054010900c12400d0f03460041000c40c0700038071403082c0c2c03540c030031021500c0d0035100e00642900e0003050350340302c10302a51007107801000b844410700f0f411403001c1401010b80c503103401c104001c0c440280104010038215118400942d807582c04500000d9040d82d08840040205d0814075044021951175021440344000100e9189955418804030100c41e0103041180381a40c140040441e14030b5441a8106000c070b000c480081c40140c0c0c840000e00d4403014907000540c006c0028807020b0410346041d000b030390b95a60320500181010361850f203045400c50406001a0381501941c1c1d504000b003641480016100181a1105c0000700902020189801c20040203002c2c0306009218110840c801b15500da002c440d003601d050754603500c039410034030001d00c0780c44040d100661070322041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 335469154 1250 335467904 335467921
    0x2150a020a03062916080c0d02060109140f0a1103090705030115031104050a0209040218120706020a0803150d120e090c09220213080607021c0c050c0405 67
    0x400003044103580034802c642d0f440c2c007405003802d100b01c942e030b2400ca84e0b12020114451142c010304107039400f51380d5607500162552180d88043d48446558449600115104903c1c0c0c0d804200103401003003000403c020300116056416006940a8035621a0300041404243c240c1e072690001c0c0ad64106c1c2c8070800380e4a0620320142a42c49540e0300c9058003175401c20981d04080c0000c0302c481421a038000c1c62848030f00e00c0b0541000000c00005000d0181d00798203200d0000e0030b1321240701410803076201d02045440002c2c50004c001340c82d00081d00c5400c2d81c1e440a01e06019480d40800d10107044c1c0e620401d655183e480e0a031251405104021a060b048040b800401d000d000620080303100e104440e86030303215000c4ac3e45043c403100c0402110360107880c001c02c03c0005040e0a1005001d00d10205555000000301c500c042800c060741e109007400e640314600e00d40d0a124003074060025540002c0c05000612603003100700d50458240c40001c0c560005d11001c1c04c0100f0a001080c0801003550300c2c010410003551900f1b40341c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 335470404 1250 335469154 335469157
    0xb0304061d030301171b10030908042601050c0a0813050d030903030e1605010507050304050d0c030506090d0e01031d0609031b010b06030103060513081c111e030702150a02 75
    0x81d1000402001c0302d00c603ca502d0110381d9154088515880242c6c40b250402813142c0c48840d40ba03940105640d0324891300228400c0b10240c4050001040241441920620315040190200442c0d03101c0e41d2500041c00102d00364002112003501136820890296951000348141c010031481000d4803030300401200c00b4105034154040041a4842d4504011190301c0840d41da5075036110348030981e200b4900721401d001c0b0390301900242039118464030407645026102c0004c1090030004080032102c0bc0d0340d18809108024042c46015405055000201a01c0410304001445204c503100c0076410b1513980c810100220400d85000c0d101000a03000322081c908228541c42d59942c07006000f403103da81c1c6030344103030720108060088540c0100c000f8203c1d41542d003540c4940d40102405011039160714050090a000a15043c0107400a110450034040c1c840d161003400206440c00c44c3c16203c0220410810400b0702c0c40c0e412420f01c0302c207024040d49910b90f42e40407001ea2515055002d503100507804c0c0000c002d9100c44680 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 335471654 1250 335470404 335470409
    0x12080f120a060603090c090e010609090f0302060603210d0e0f101b0203030a020307030b1801050406050603060907030b041829070909050405030d020c0c01140c070b0304061d030301 79
    0x2010007003241e550804801721401142c005040313041d103550810551380315030419036801c0e04060001980c41c0d52510b114046510100040f203092030f203482c0c20700505805004169014100340d0161200c40001c061049402c0c5040106034070072031010603014140c0b0115400300a0502001080302c1840003c0e80c03140d40e5580b10009600300c19820100000c4a4074800d400a07503400480d0380040d401d5403188070024010703400042094042580d141000f00d41580c415800c0055110301e0403001606505050511080e5404d5801c01070180800300b0901600341c07640d9035100d034014050302c0d000031442741800000740a40b0111f0b96041003039901e040002c4c14880500701810b50303500e9424400f01c02561480016001e024201d5a00022842046c010845000c0070342001d41c1c82407040e019285000c40c8500c0c0c0720100e03048580800d88a0380540161111543c008003c8403251840031416810442c3d480c3d1895595500c40c002c440e644100440440e0400005070444c0c500342c0d92a120290354001c00c8442d880d9690006d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 335472904 1250 335471654 335471671
    0x9020705070b03010b0721020309010503180703031701060804020a060c17191e2a05060709090c0c05120a0c0b07020606011704051b1305150a0801060f12080f12 70
    0x2d11000e80404451a14208965110b401a600b03112b0000c0c015100303030b0802403800314546806d5010b508001d006103c000c0c0914402e0322042001d501100d88a0000081600401c091002582c1484056030351807000e0303000c40f00b2525141c80480358034904200560305000c65141c1082d004100152041c005080810102400740c2c1c900c081002c121598144140c04001d901c404500d0705000004100f0b918029040d00300d0701014808241803665540c945030030400c88a070400114085014041075940d8024114020494505000044425154261a02a5510740a0b103080f8005604180035014150342070a0540068141c0713118944000b01035150f1008540c0c59000a010941c0309402c03900d101041070240782c015000b0400c142e64120803010f841001c107000f96101a15000d0744564100c00c1c00b80320711442c0707001015040d08030140144258840f0342e40000007036905054080c02072180340034424007144d01c000081e03100c075202410842aa40700c4c010351412008c8d00001c98044011181381c81d180180c440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 335474154 1250 335472904 335472923
    0x21005040c080118150917030a06030201090519091505031506041119050a0c150b01020618030f13030c1e1401020303060f031e1c0305010e0109020705070b03010b07 72
    0x2450400b090008500d40001d003111102c1ca0121604d40d45584a1a00f21f48600c3e25901c1900740b04607012480d8004170713035085646840c0d200500440d40d001e603030b0800801e020740d18045003c148030a4405040c0352402003415943e41e4035003503610700442d03404070402440081c06565010850b111005810f410441c0d02c80d0203036040c2003851a00b030070404100c0b442030003000000c03406154105400c85d140d50000d244401040100d110590129003194000c403ca010320351400551100100001780c01e101d402044039506242c2041000300480c2c0100444080841044049a076842c1c165120908101e07207810180c6640100c4001141c8100010510001c0b8400504030b8603201343e903401428010038103001d019005800910102d5a2414a121000020342008080d20700505e0500c00ca81e040d49110840c1c175a440e440021080c0d5040281e40303210121015510b407c1c002e541c14650000602d54040c82035056039580020a030050040a00080000d441d18050150762540d460602000c5904600000e5804092 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 335475404 1250 335474154 335474171
    0xe150409061d0403051b070e0a020310060807020d03180b0c040807090b0607080307090302090a0f0b0f010906050a2604050d08060102120721030c120e1c021005040c0801 74
    0x1408060b4512495165a0b2180303000055003840001061803815090f05218030440481d1100e0131008940c0f00d10000c000040e12485c10b00342c095120b5100d0350055091140071010f10010aa012800380044c00d82402c012410600034040d0720000314004001a004544001c00c7c08124030600004004442d194001c035254640c458607481d049070150706020b54800d10420021002540c0c20014590040320340c14100803040c0c0d0390700030440551044030180481a601c210100d00442544522010080140e5802a04290010010b002c081f507900441c400e2040c0400c1d80d801107403103054244550031949080d030b8810f41c4a10b12401c030410307050303a08403100d009190b030702c141c40f52040d1a1103101c1c0340164010403a9000c60700c045003450b44900401c0c3d42d00c83c0c41d80341c21035030201603d0306811085840c2e60002071b20003444000600c160301c280d0001e851541010103080d210300300080c40c1a60541c0300c0740741041d0745412020503441d182030040c24040d40c03410f01e41003005014040307403200210341c500e80c024400d050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 335476654 1250 335475404 335475449
    0x307120f0506010f1203030c050d110d180c0b0309160e06090108150610090302060c060411150d020d1b11010609111b15010b090f0906010507030e15040906 68
    0x603c602400e01c80b030b05a42050f42c00309200c0d03045081c03443c148d414040e240c100707400d8041b415501282c1c250700340b2000000e041000d513041403140c284204a50400e030911881242c0d40c881100d0304d50b1080045519000c404103840503024800a4900b00c52131a0f8011550756500891032002804c45d600303031082001200000780c1e1040819040600b0b0401220010169500781c1000183c11450039040100417000c0b901100503102c000c003c2800640c507000400003441c3c0b5281409048600701c107054051810212410340460010061f0b52218602140250301e90154500c017400400500031828074880261210040243d005074049900029400003804860b85601c1b50205071882c804010f1480e050800c0007040700700600d039180b0031204011059a131810607194181d508840d003038008182d031103000544c0003060725240310911030320303003007136401c40c0d03c41c6001c200182c564010005c0280502c861800030b45401e03550b110b00045800e10f280911511161101c6021001f01014002c009890741860b50048640c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 335477904 1250 335476654 335476679
    0x5091807030516120903091a0904060b09090106050304240f0f0209010c1e080f03010810091208180d030f0f14060112020d0603060903020c0109060e0f0307120f050601 73
    0x1420319413203100541c100e000199000b444440c2c42074041002e0014080381c031001035070105485050f8501140e48403d200f404000866520703902041c5104000c00c414155900c540000c81c0c111031303050419607166603075403e0090500d1852080c841c02e118140e5102d818030503850744802c4801d05643d2040044000d00621b141c100c1c4115010140071480103482280003d4024190b41041800300401540c009032659605100e45c0089040134203494020005011410341000340448445440f0802d1056460301d071180044440e070b50071030604001c1c0da100020600d2045c0602c1041c03451880c82112075201c00360f20003d000300590740d5403102c014106680c0004204150103a0340021000d0040c3c8416034032a00010744000d602d040b055002d40303409005074008121148039805c0250700a0001107104205032a00a04040c81d58100030705020000500740401c55208504a07042c0030150b40700a540280403000a1400140d40e01038000e07050491006d0042003061910b0241240c03142c0100c88059895000041c0c80c4c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 335479154 1250 335477904 335477941
    0x115061701081905030903010204030b1602060106050a0507050c030607030c031a0a09051e0408030106121404150906060308430201170412020d050c120901050918070305 74
    0x450f406400c000701d00200c0741e18031600c5544a402103038604001540860300b660010307442512564401400c00031407100521030040120200e201a01c1690704000000d850b40c02100c004004108002c6134420030450104021b1011810041c1202d2161901901c020b02401e03000c050800024100740d110194040458000c1c124120000c10750903065090034000700052034020900c040e84405440441c4580c0c1001a46038080d41c0501542a66903040400142c0002100301c840294a45800704503006e61500040c0990072540c841012840181c400d015040506990440501400d141c00c00c00003c001442c0b008107550b0250740c410056481a201d070001c0b200d01d606031010104282d5144004100100c06030f02d25680d40305051140c60342d40041c100341c0342c40ea030403181121780200948075a00d01715010402103003109202c0c81c10a14004000d81d83c01c0e201e0310152202038030342c580442c587c5c42c43da0007901070312b00e848805401c09a1a40c0040700c45100400c0a840400101c1d15040214010000280b0070608 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 335480404 1250 335479154 335479169
    0x120c2b060f0e040b0a110c0d0e2b060608070f050a060f050a050702031005013507181d0a06060902090105070b131506140a06091a0403050115061701 65
    0x9a4468842c283c051304020160250603503a52003a001c2030300700d80064042210060001e06c004e42c0c5101010300030a0502d011584515824203222007508401c82c0f0f01c00305144c3c0c81c2c40c40c1114100340d203070540240501d508061400d00035200e01040003045052018121031088462052280c0c0c1c424042d5031005400c0010400a202044000191703802200201700461001d412555481c2070706103410120344082c0c1040c201d03218100701026604440c04240480c0d210350041c00018040145089541e580340c0d48038044112566a600940e01c000320380c0a56110000c032540240000c10641560b41c6803440c0c1131044400a14140001c034501d02103200f070300c50314101a12103901e04140d0f0f8492640c0000000d000307851000f42021030714005822098084400c102118002c1001418100304141c042d50848007a80507281c204001c01050798003401c8101207900c68090b542d0400004000e0380401e22507070304082e041c1d601380a07410038003068045100c1c04640c425600c0320b50b803008079542003005104c28444e859 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 335481654 1250 335480404 335480429
    0x1170705060f03060d0f05033010120309080111070b011d0112080702040903031d060c03070e2106010f05010206071d0d140304090b0d0305120c2b060f 66
    0x4046040400c1c02c640d0090086d100001c44c1b50726603031620702d1603000441440d0369074808c4400e050143c1440100e0a00640c004c40d1a00790f500d006503260380350400500c520340494010402090030b240c0948200406041040d0082c80150b60b0611112981e03441444208c03a054800000040e000061401e25044905034000100d03669203810170380300c41022128025500746408000e9000140d0f51445403050083c42031701e010440051414803903a41c0101d2090401d81e5400c02007c0000c84103652080361350110203800c00b40b800841c000045000b007000002d50311107402e8841ca255010180c00242d01781211011001944510f8840c0300480c3c9a0b0002d031841000300e0b650f441c107110540c0100400100142000d091215640d800d81c42d00038404090000311038140c1c2000034103000501150060948070704069880c03145081159030b0003400c41c41500c6802070007211420100d0b480c4d480d10300854948840c0c0724072500301162018105059050009030960a075403030000006400462608210115031400500d078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 335482904 1250 335481654 335481661
    0x21c05070311060906012301050702060f21040209011703031303030209130204090f0203060a030b040507180209041512060b030703020a0303110c0a210501110301170705060f03 77
    0x261500d401801040302481400c0440300c016560030000035201c1e00d40c03000200850b52506100c00a0034400390b19030703800c0702c0d039990342c40406903040f40c00c60f400c20381c1c1074030b5240d81c0e0140c440e64190a8051410350308200400c0c0c00b0b442c1c0d02554450159800707070b402150303034111507607032904881e00c0007418200340c60311900180b001445503c1d560302201c1e07900e402420003500d4a0003032000030708040d4494628041465010409101c840c045205030011200540c8003145982007000001d60f40d21224031004110118200006040203424040d00b00200410b5400038400e00f0036603111400307500590b0440e401280303840540481030759a0030314081200d20359070b007141c004000c9840c0c40026094280000d5010311031001c1c0000142c4902410000860082d9503404040980032900d5040815006490b48038495640d010301c8039002101000e035a0292600004907010614074182e400742c10413880d0503400c40004000041e1400051034890400dc0c1400140c0d8207498407441001494081c16000a07a07400d0240b000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 335484154 1250 335482904 335482907
    0x60d022101060911040314071a0f0f07080309061003030f23030703020304051b10030c3e0a05061503150108011a030309130b060f030a02030610021c 65
    0x325101000c1080000c2006034960040c036058601c40004940007410002e000c105004a43c191101030301401000780c040c8518100c50030f100c00d09181403420b485000020344e580075030840341c101d8010032541c1006039200e014604082025407c2143c13707031010300441c030015601c0c1c29407046203000e07603615440c0c844002080440856002d104032610100451358065a21040c001e4000514030440c010340d809030303881c41c2514040f8105501310030703256034034141c180003072815550300c4009244850a130b107000182d540491030100c030145252410702c1005005076814205c160b070f0046041013107096250450032078505008096a68403180070010741030707401c8400403800c80402543d20101d882401000c44807000c0945001c1007060100b07134402c1c11180c4d035880d040640030341f400c00d101c0d041480c01c80c0a90b0a20401d00301242c4500f044241c0c3c0305905a0b244100707a450795609080e5017034490740c14171294072487c1c025540f8009510031703603035284905440d5903184101440016040c884038030600300ca40c140c0307105110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 335485404 1250 335484154 335484199
    0x90501030f05070207032303030901050604060501021203160306210203010507020d140a03060e0c041508040201021509032b060e01050d1401111810030c092d030515060d02 75
    0x850803c901e0b8102507c501480b040000c2c5014a08100000416045c05e004000461300030b5405203040d500400d2258501d44440c0042c0c2c0d41c482e0300b85d408610031000d40303101140185250741003000750079403c0d01c0011b80b9071041c090035071055109400070403d6441e100d00a99551000024900020303414005280c88101c0000261a00801c14100412600d481d060341c00507418044443c680615004501040008441422100c040840d800d08004909080d00003d40304c422012045003600840710201d807080004000b140c10321160741c100101200ca0840e035041310760116800c402007480c00e290010400b02000c508a9048500040c03d24074600d5950342c80c42c1d400503c407900c000155680c0d000c240c40c100d0824008200c0b000d803004905440b039125008100ca2400800b456030105842d09100719041500060200140c2c2d051445000c00c0440400f818034a50003d4000d40d91400072002c400400c002002400300b80c810032126290466542c0c113410300040d2000071402a512000302801007540603810203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 335486654 1250 335485404 335485433
    0x80702042412060615110c100512070207050a15030509030306030c01210203250c0c12050703080433120f020c010903050a26010302090c07060507090501030f0507020703 74
    0xf0000720b0402e9444e411441103440419448000c07440d141e110500805040c403060789041d4044641240400b40408020000d00400c01032071041e120140c00300b9926402040f08800601c07000300041e4940da1142d20fa059601500442a00480e0410011400022000c0282c1c2d2081d00c01400170204002c0410046802400506441c2c4a000030852220590541400110301c11403442c00c40c0d1036155182180e80340b89900400c680000c20030b01610490010384111072400448002469400d0f01c0e02071820a07034104504d80d84004c129450018001403000000300000003510716000a04080c1d900c13107040890052001c452801c00590b4117920902c001400b64420b500b0f40000d5040141024100722500d400c4560254040d4080740b004164185010782c00340c1606610b80200803080790340c804040c3c00b0500c00c88107020003032280c000a0001402151150281d030019900715030144a1410540b40140c004c3d5520300600d030000742040e0a90700350350254060309028408036030090001c0b40c6140ca441c40c2941e5000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 335487904 1250 335486654 335486663
    0x11040e1006081c052823131703160f11190b28020a0213140406020703030902181e011d040302010f020d0f0f0507080114040b0d080702042412 62
    0x10700c0c0301702d00c5444d4130b900c540e2201481c0e00c03042050300d910480c04085c220484035a05040f20200140300c12043c00d0007022040b50241c3c5008451a01c05d00e02c41800c6004003207e241d644140c07811607174140160b9003040c00c0c07014004e85c1c042000302e61500502c16a090403c07000c0d100c0310a4a8010072503c0700d0080240302011800c11502d6900102c4030106940580c20000380700183e110710011410343c44c0440480189005105d0b04120910032204583c40902000348050001036002c16800300b410f0098101070106a8010308080c00821000580310004206488865000c0e42c0c0d100c1d003e00c1912040c0805060b503a1030038034582078010707107141d15104000007082241195280e40c2240800e03002400940f910b880c69410101c0d8040e918041481102c807112100d00030b60781040c0034880305507004100607064405100525202031300040115014060255040340c001031002000400e20192a0140420314400c03a401d000c2d8440c1d4154216040f1215100008031221070b5504000308011021301c1c49525104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 335489154 1250 335487904 335487937
    0xf06050102032b062d050603100e1e010806010303020f0a0804260303160809030a0e010f14071119030b061309150e121606050411040e1006081c05 64
    0x141c89012405540b208614045c1005512286228540491800707015240a40f00c6a042d840c0288500842102c20f115981c00070080b500070035020400200810020305080048603425652060020b0381c0e44000d22050b0011701960707983c100f42d0074005c5200f11045401c03201060501e03044c104941d044802d5000106552015401586040c940c140f001d14400c4c001031150089440407150080d181b92001040f40d245500304108089440703400c00e800203900c00081c0391003154600118016100075402c094060120342c1c000c2040f00c200190145c54418201d02a1540d1a4032401c030400704900d0344030303400020008200341c000503441c1e080c03076030800e5116000c182c400302d154005a118070010402300740707880c2c96040e15985551180142040002204107054070600c1c41d04101d021440072600707800e10300401054980000c1024040010320312810000c00910811906030030400c0710382c0e07890a0004403442c8d0b6061080015002101091002019001c02541a414032240348215042e91014800c1042c03041c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 335490404 1250 335489154 335489159
    0x3030c09060d1812030e03120a0c09080307080301140402090a0902030705160b0403081006050d0f0b04050910050a15031203021e04030c0e01140409020f130f06050102032b06 76
    0x822941802080d0041d408000c982c55210001416079a0346c07009180300364420040044200c03c0c0110403503200304803890014070511400c100304c5038000141d0100e10544404546c045c02d01c00e022008504036005669801020305d89003050005901807161200d0b2b00c0405480f0400c03c1d0440703138004644c08551791511515154040d103c64210000300704044c2e45c001045001c1004264024010f00e4204100032281085c140c64000e00410707501ca994503020401d0f48950307491140d13060340e41004034490790080041c4001d107041480566076801c1100c002492605000c0400d80c00006440745506214005400003006425a25941d6045075960407403402c1583c20030074801000401e1150505104800c00f005a0b1603103581005e10301440c4603008882ea444980004000d0704146441802d0300c0c02013540e0104001c0b801d400002c5400712642c141c141c005400c20043c07041d00880d640f0440402042c07610400209807a60300490ba2400360b0004241c0c09014030780400c4901d091018150302c25592030030b01280994 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 335491654 1250 335490404 335490431
    0x1c05120709090f020403020a060527031005011805100602070303050f070f05070614090a030b1b0f0403051c02030a3203160f020c041e061d0903030c09060d 68
    0x10301d40f4034030250040d40820305104502e0b0007882e81000703000314a440d0f414500d0061115031400410724001e408243d04440340301c815101072161040c480e40c29802042a0340c0e5550041d80070041d40540482e44501c5d060004070210b2403020840300361000c5a004003019811a5402d90b01c9500095150b800c0d000180982000a00b0324200c84010074810805041e866250800184c04090210045246444107000182d06519410603000850f0b030041d8401d2815290510103000b6061840d260305c00300c20000408134095070800000b401120300c1101201e55111243d2404070441460b4070400e00160005c000c1848454860701c11007442409d2103d2600440050400b00040240c1820969403407250100c20820398072550500c807a47d643d214140314403034040050b80207498030410444e85114030f0b603031200d00c1910054240070001d851344448c420480d5076110020410500801d038040c5c203882164100141404102105880c02a44031310403445c01d105040082107080e801415238891032607540c044000012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 335492904 1250 335491654 335491661
    0x318080705010b150c0a061d0105010303030b010e0402120708041b0e010320152d120c04230114120a05090d0e060309150109020307021c0512070909 65
    0x36071040c000043d8001d240300038031408441c3e034070481480300b2040c01550200d14004c1031401a05500000005441240140090032021100d0030101c40398a020008410150103622850041d0002d0b00d508a051110604110030b81c414800b101e48080c40b031601040c5024040c1d070943c0d8101d48aa44400810003085030902144c07400ba500c24060307007180301d00400030301c0b00d0200c0001e20300c25014402e0034500150f00c0895201419400000311168000907e07441800101d550704460094904281084100c0401d441030160804034500750307003001c11008941d20420b0380003101e00311410b007440920040c01141c4041414a44000b00b6030500c07044050185142581e00d004000c100399102500e189804c041025030708613075008000300c20582c020b1803108126a04418281100351080760503c2d9a50303030703a1615500388801540d4054a0a00d00c000115003005660082c40c4606070503803c030384a80d0040d802140591040221500204074100402155490452441a440402400c0c8000ca2542d44c025003801c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 335494154 1250 335492904 335492917
    0x160f0f0206070321020406270503010623060702031f200d0b011119060b0a03033f05040614090309010320041211040f0e150115031808 59
    0x50300c4201c084d940f030341c1c1a0300c402c00e4084040b50114185820f0a50140c04407500c3c0550380301c001004a20764080804034050380c809024098024000107544101d6071005601144420140501d1040b10310007505002050317036090f0f03400500601c030882c1a008034460f80c04841c3c1000b204607484240340e20003440d28008820301210039031410341c0c0d1303404071003002c800725000340c8156810800700c404504980b8500148840500800131000720324481c85161003030003080d112929940001c03881d10000305054000c4e81c1c036001d50b24200010011501c000e001c075110840102074000f00320020960001c0c50b0400b99002c261b200f1300c034190004000300c07443c081c034100040c03c40e00c09899034000140118107513498024495074902d204c440704142ca5500707101c0c0c10a80103500545a0000d4404185808e0010f40d0000d820403920241080200390704803850307140902015140e01c03505118041d440460b480720038400030f048461080c2003402c40081c0e20011800b07841d01d01200075881d40300074254070200780c0d020001e001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 335495404 1250 335494154 335494157
    0x301050f01062706121506092103050409020a0e0a030507181401140a0e0a02072d080903070b04080601060807090f030b040f060f050604050606160f0f02060703 70
    0x31661418034001e003024201c03400c22094040811100c5201c04000e4a118260b54060074890861050130001e1801400c80d040c0212189809030f4000076040c0d0049078410944125503400d80c20480d0b90403a84001c3c044c2c114004000900800c03041020400d42d078064030209259140100344440070000086170040303e40c00682c0c481c0c200c40c0080000340c4e003a0300303503c1d05542d20348424490400c0c01a00800201014400e4190703201d000c5411491035910741160102400c64500c0d01d01c0c050505030800c00c02500041005c94848131b0700c001c0340e20680340a241c5030760f00c010a40440707070704800d180c0c0d5180040e8100920958142c401c080f000f188112005000e40040e08100d001442c20358500f46004001900141c60100be00505d0081031048216100c80a070649c3d4110422614a03203561820701507000c0e2900c0068003041c40c0101c0d0080d0386a15810240c001e24044409100070b45070381c0d003040200d1180c0c8420300d00000c0c2c0403802c280024035154808c841035001d0903c01c520103040740c02080c000e6014010450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 335496654 1250 335495404 335495431
    0x13050405071205070306030b01050f010507050f0102030601030605010503040203030912011803031b320f0412050d08070509040b0a030209070c260711041116053315030105 75
    0x20b095949034416158400014034003403041030b1954582c9140000180501c900801980f0380c603503d41e0340181c040726100c0d0b601408a510030a0403028180c002d41080e920280024240240010303690700c510160b034000e0380c0040c0590302d84020307401001a8004d0105c03483e0040d5480b052550706115003c9180312002c0e006e0b4401162a000d48909801581000200c1000b400990b481c1415609580c01c000201d046c00e4000701d103005111040360345410f0050240643d82c0c0b440004001c80c02c0c501d100340c2c90300b43e103104504071941514020b10503a0040d00807900d0f0303000190140f0404115141070f800c41502a80c018002040c03036a2250040303001006e00700e5095000c40c401d0324200b410460031100003840d038244000c0d43c0004542c1c6580480143c03284030005490041d00d00c45846480e92030381e0080705c490300c80502075640d646599091800b14050346000341d0343c6024010807200a81040c86a0554002003041007540302401607000460350724001d08100c00111103000d40b0303401508e00340f080c10f024031003401c40d05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 335497904 1250 335496654 335496677
    0x60b04031b08030307112a010f02010506061603110706200303070c15150807060e0105040f0509093a030b0d0b0601050702131505010512010504021305040507 69
    0xc0d07452284510325064201c1c6807103000c000300750300401520b4022150f49880799440d0039000000e0f00d862890342402d10340840e00400014008a03410112050001c203807215080200c040700b099080301d4044171a190040b4041190b80300c2c0c01c441e1801c50400906c02e040030245040d0986840e460240d60f50030000c00300f03841409440d8000440450350452114800003140b9520300102d0003041040540790060801015002224454070507400c2178a40e20800b150081645a0722407640360b48031034500c2130070b0200358042800460780d4403400132242641c810604bd40b40f42860482030001d1701000510600c05130084150784040c1e61000c0742c0c0b01705d0404071041e200c040d44100210101140341a144d5503806d02d0b2070310304044c400b510b03582c40b0300003060380103106151183d44180060300c43d40b01d400300096001e074090340f08030000c4450380c0c80780b0100d4145102003a5100d4641d0b0056601d48540490301e240054510010840380c60140c0050200130417051150000d160307501d010901b40c070815100d44000c0340c180450b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 335499154 1250 335497904 335497913
    0x70e010f05030f07050609060d020a020606040e191211240a09030804020904020102100e031e04030f06051506040b09090726060d0f030f020601060f270504060b0403 72
    0xc0d0800740804401401e00c50301400721981da92034152107a94019400454003210503506c94080d0382030002030400540d500c508902c0e00940f2900d089030814070592820b001400c0b04a400508001c0e40d1080001c0880910704a807145c4031070690340010602045900d0101404142c0284004007449503014000c820010034207582c2d60f240760b00200559281c44c80d0041500100b076010003229003103901502d0b40811500c507800101d00b404060741282e40290300300020f0241500300000141110352030300901c0360300e0740c4c0f100b50708883e00c0c42140710280a0042180d06503000c200a40d000741e070031150340ca01503000040890301080d866001644481d810950200c2c2c500d0701410988806603100300035251950304007980b002d1584000181815001d480f503040d00c0000d10a450f0605642156508104060f0303180046140c010400e03040141070304010b0041e400009406400f840e884640e09000d501c5680da442c46030188607840c01340160130050300542d60000096203803100d12611025100150645507100d045040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 335500404 1250 335499154 335499179
    0xa050312010b03060907050a1403070c060f0e1e070510110d0c081605030f040305010b210304060813151506020a0f030e0a03060c09090509010213030b0a0e070e01 71
    0x640b5050703040080054039a10000f0040c0d20020304e060081e1078900d24002120b080700c400001d01c2030301000006112550f030f0011212140184544810310003803030b8200e02601a40d02c0c0c4001c40a59034040c2d0402942e0030045005803200744845812070350b8981c1e40e180044c0501021240c1e410100380c41110500c0941c0c0203005c11400d50030b45040c0043c010b006031740d130808684503d400d04040039114200300d5007005000e10071034005580c445052030711107480b0f0038814020410340c1c0b0441e101e00c410021040305030602542c054070340030114014500307280c9420420343d682c0400401140c4001c1780c00c10f4400004a40c4001d070360f0385442074000040c200b00030340c600300c8014005401003015588103405c50703030000f10307c0b01c00740301c88990500d8a90251101800411031440c8942c0000f4072040c1001c10903d189503002c4030034022208d80107402c1c0031075207407001200d08030300c9035908105a2024020051010035111040d1580240e0542e20000e446a50024414245080c03078118001e00c5028000400000e000c610 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 335501654 1250 335500404 335500409
    0x91002061506130902280c030903170702040e010608071202060f0c0c0307080a050105010603060b090d0212070303110c0411030a050a0b0d0f021206010b071e050a05031201 75
    0x4140e181040d500482403255604242485110001607003006801030345503a000902c0759410a41d1a07541c914444990816203007007000c4440200080d403500c0620035654114001d406807503942e4003a00710b03101c0c85807010502200d50a40c1303804004000c0181c51300d00c54984000079103400081d686d41054409403d20740c0070343c072412040010030310440140e51500200e406911140c00710b42e0b07179008612545410a01140505603040c043c15a00003601040810000e280750f20610082025a8866001b50219812802220200c0409210103074840c01c0040302009040d0009180c11892040d00981501d00022504206e0004010441c80c0d11075501c02c0000c1e40070720300121001d0000b000750903960500341c00b0003440390003025110340102e5000291a4444140360300b0103022240d82e5500c03810205002c02c1d4400040b801500717203450ba50b02c1150007140442c1a5152004a1403420380c50ba1100d500c0ea52004420b444070340c025120440010750100000c010b03a502c204061a03c40b000011002c0c06200140d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 335502904 1250 335501654 335501657
    0x5070303062d050102030c0c011d03060f010e070815062d04050102060c0711190f090203010501020c03010603050601060513210b0705070c0e132a0b0c030307031e0207080910 76
    0x7d002c52011b10001182c100e0000200b840e0101a0441c1b203c030760000d00f05114502a05801581c003845280c80590020f00d042c1d40d43d52185003542e8640060444408004131100c01407400c8082c401d0281c0c0c60410300800901c2c1c1d8204c814404990400d01060021000030700036102c40100250811032540c0502c041e07648a4003910400d8206965a10f0b0900380100300208640b1411540d107107003902e00700c0c518500b0080d00050303040d240c3c5030b611480c00e40025402805800e0141c860740044429914050041a042e030303030b10102514059107082000d9131f0a40141ca00440d5003001800e0109a80c0b054501c00c2a95004010980c40e095071581884140b42202602075420007004200780008114280d8540c400c423503003484290311681c2c1c1c0c1c1542030120344e050300c0000e085074585103010020f01019450440d02c07002d0407401500c031556408800c5403030f22441030000c905410034030000f94054025031282c0d404040c00d800c50281030341c10b90220000c9904c0741000700c9419001240d181c00030b08007040a0026122030b0f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 335504154 1250 335502904 335502907
    0x9032802010b2d060d0e010603020108090f1c02030405060f040905010f030b061309051b032505150c1f2d0504060e15012c01030305070303062d05010203 67
    0x192802c460b803004071800f00d07846035180031880007410340302e5500b00c0700591000710342001007502054103140a03088a01c0b00b41d00056500d0701080100c400891802e1039440d0801c01040e81002c154402100625044044025170006000004031512450010304113440040201c6039603d085c0f0803a041141e0042c0c010440b001001041800007400350190250040c9040310030784003ca41d00c1c400e80d0083c01400c403000b020b40c041c4041704442e00c561010031f850048011030a0b600d404107403c410307200c8081c03849080c43e135801d801c01c0f08002e603080284030300f0802008007030824580580420000c0c94400e66000e50b1940d008035041c1c181181c065803060003403200213101c0314030308026280402c008050312022110607042d50340e404501084600e03031098011306111803c1d41d0f10001c140f807203105482c209100b506550024924101c80b00d80c80098941c0104020404d5000b00d42d00b552800c5605070040d010840925a8446001c1089905900e41d0212842e0b80c1c07100c00100c0700d000003100c156900f1075206a055500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 335505404 1250 335504154 335504179
    0x1c020a050d02030604090f050303092b0804150903050c010612020f010302180a06090509130201021213331103030105040906090209010902130e07050a030509032802010b 74
    0x1404400c81c0e4a80d10356401c0541c9a03254000001c008040c0810010069858050103608001001c009184907030007543c00d64100b031030750402c00d1380e065a10140c40c0c080d104c1c094030039a03051409070000c83c1d00540141c00701d0000360362400041046403072051040d400f150003c2210030300003c003401014098004c1c00c90201d242082a40418014800c0c200120706050b00401d4995102d101c0c1030044202401c01405840703c966a544003505840442c081d041c01201e8050000e00342400c214a0141c01d42c1d81072340248060700c821114400c0c1900211484a01d03200c404100003008103004072004291541028240300c52960280c040032620242c82500f0107100780b4810001b40c045020040d42d0440e04107690100368256607141c0f0760003c1100481c0203600c030207400000b140070580c941c0505080140a100120196212665044800ba0840344500001e07004c11a8a030703030510070b07040250000f82c01d07011a803c0402d15060100d00021007422410656585030360700907419424096118900c2c02136448154110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 335506654 1250 335505404 335505407
    0x15120803040b090f1204050102070b031003170c010606020c27011802090402040e0402040e0a0b070f050c0a0f020a1509051005040e010303080f0a052e12081c020a 71
    0x800150090b02248000f07011402d00340150f6206060000903600c842e068103070855580c0c0c1042c01601d00621861001098030345da60000c4034081d1b0354900030550b48a01c3e40c0d49040341121540004c2400303840900510180000900940740035122a40107071205607110b1040c07010f0100c04611512035507031105c20301d032900c5503280b4501d03040d508641c04620034040b4106412000e4440d40009075006440000c001603c0107007108060b000e40c0c8202c4083c8001c034580380149668440b001c0010700103840300d00c08a01d080b401852090b42c48030050601c1412310a446681d182404100c03003080d603000040d10051011440c08400200c050004105001d4051101e44002414455076002e16400380c02c00c0074543c0511401041518024031560b01c901030a507849140040c6941c0003580e00c15142e00040c40811100307403803401040c2c841d40443c1c1c842c402c0140c0801c4c00c4080c00060240040340050b4140000c02c00080c81280246035a0040c0e0f151982ca400000b0041e4604103240d980d8200117205000b003644a9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 335507904 1250 335506654 335506657
    0xb0f06030a0c1407050718140c131206050613050106210608061006120b060306010c021305180613020a030f050f0706030b030c10090b0a030b030a06151208 68
    0x40c001c50000d8407592060041c0c4040039081c150340281076010400d0001c018000a00c9001d54028201032200c00001c03c51a505560141c00441150382c0084005001c140154001c0c2c140740140c072240d4000309556109410141c000000182d403000d0300c1d48100115820004680b8ac00c080c44048200041e6141010040480b0940c9181c28103801518808210030f04140d00104d01405a000c2a12442d040940e400004201d151080d80e000c9420f641d80c001c500c9031907110300c1501203006410b440c651fa44d00380c011220f800340321108030392080708204911400c100031700c04c0e24880d09082000b80c00e940c00c2c10105524002c0d0082c240007260160903511401070700c5090140701107da120340c0941c540c01c0307a8500301d420410504a403400500c40e50700d0004005505402003050548194150317100c1c81c0c101001d0001680d001035511022035480c0b030341080903818010080032958400e14000401c0007450000038104074044405949681d1101c1e018920105541c40c000c00400c0c250310403609154940d5210a5603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 335509154 1250 335507904 335507911
    0xc02030705060c03091309030908070e01170f060903030712090c0e090307050a050a020a09020c071802090402121e090a08030a0608030703020a060b0a14090402010e0a0803040305010b0f0603 83
    0x480b004079959a5144080096800e00d0340018103484143c42e5020a9a0050152840c10740001d0902c03000041c00b13407000309005c41581d41c1081c801000340e003400c40d1548000c94a014042c15031113140300e07114102805001c0303a0302400810000c1e554906200c900104046010030001040038a8031310044009109080d060f001c48815030262800383d44c40c50009400d500480c0c0d4040c005002c0d41d955401000004246142c450348200c41d8011a20344880303460b400c90007440c800070101d81c00510184010100c114054a016110b0f4a001d40b4100303841c0c0128080c0d030007a08000721062244d00501c1414004409503446203c51517068401915107e00401c1c1d460107640009800143c00101041c0c201415802c0000a40806021a9660200c1d441c0c000d40d100c00041e8142d45852505508210342d1a20080c80300c1114010b02c0301c605002108410070030703902c0001d0702c01c9051201c0107626010540342c1880c1c41c801050720070091030b11186141415400e40f03980d110054030442500c041d81c050b9681d08000e50b40c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 335510404 1250 335509154 335509159
    0xa12031508031215032b0e2110021206040f0207021c052b031b0c2d030f0e0301020f0d02090406090e0102041d041a1518070206070c02030705 62
    0x41c04d46800a040e030511142c880060381500503480d0300c920440e0901001d804424070300300829a460990700080f1181c42c41c815555900c0446a00c1291141000100e09145903550718141d94460a42c484000101c1c0c0c8030490008641941030308000e114a070600c284014030b004120b013580740040b81d1b400a0844000c1d4500c6034415862000c141080c80820401881c00c1c00b054000140001c8480100440049820400000080c202845020b248001045810305030041e0b07250700302304040039610b01000d840200700303410703c10500c030902111800e2a2013900008501a0310f0b02d5481104081d002070001003203035060760080e0b004104240028030403c085800c510044400141c44959410018010f00341590100c400c060414009023040c190650040003111003c03162030454186074903840000c4001103801410070b0300c07100460b00c142d40010740403a07404035024920b0345103129841e00242114003e03c4151016884900c01c00607803c0d010072901d90000b5403800c00c0e040303803221640041e07a640c1581c0555030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 335511654 1250 335510404 335510437
    0xc072f03120403081608070204021819180e0c0405040b0f1e0703020c100f050a0e07030506040f1a090706030f05240102100504050c2b02010c030c050a1203150803 71
    0x4284050482582e4140323900900075950f80410101400002e03001d191014440c4010f00000e000c0c0c1c030103181c007040c1140d07044190034240e2004183c001000703107051a200d1625009150000e1125940c1d4462140f00358418140580d150822461a500c6c103800140101c1c44081094a540602410082e903aa0720060320f04d40565140480080242040484d042086006003482c010700407110803900b0862043e11030000030000d4000d5411800e5407040c1c1032001a0160b0850307000315020899154020312010f00500e02441000e0308800b044044c0c0303004071048030160f046184180442940341c0100c103d00044140c00f07000a0401041c500c281941504d05c01010340140c3c0b00d10841a402404180850084074108020b9440d0506005440702039450005116184008803100d102c1c22881070038400326020703080d040210460340d00640e0304100da0181034007030020a543d1140010000c0149501c194031405040030010b4642c0005016180300c070381d400c40c06145034403040c0840303140001030741d561030301040868 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 335512904 1250 335511654 335511697
    0x403080402060906190809160f14030703021c0605060f310603050123040b0a0c050712030906050601080c071e06060b040e0a0908030c072f0312040308 66
    0x20b0b0b858805e140410064000c004c000951054110403040c2c440c60010040c1c40072a0b00781500100329404900074181c031021109001e00c42840c040307100303921099028045807201500ca400146900c1e0150300550b01c180d00039547e500400403c0d00850360040c0e0142c07078050480590100140140c80080000d0005428500c2d040501c5503000d0000408544031000802149407a8280300b03029204007141c0f01490014241d080c2020b491900b103181c070840c0c00141114080d110089000c0190000b14103a60400030140a100041294204076000d0b0020075200020064214a860010349134020102414459030b03000300507120010000729241e440c3c1c8001c006840054590444000590f0004045e06442c500040410451041c01c020f2007900d2040c1c06200c200c0d5144044041031310540784000b0400300041c00850050f00e040005888480e00c05da400b01030306207500c400001c203d41c6402d1107208002246c0700048450400b400789045424052018500d13150840d01d550309144192441c14041440e1561398 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 335514154 1250 335512904 335512909
    0x403030e01060f1502010e0319051303020303041d06120c130615110f0c010c030c060f110301050a06050909011505070b0405030301090f230a02130e040302010c0804030804020609 78
    0x100b0183c5098014150000d0311030042e8610f082c200c03c0d0300000f40d80381030701c103203514030000094480803030740e0300720710400c2510320002142e69811001032440c450f42020710200040c0d0313051001d403000e410603400800c8007104003150785410740f0005e03200b640070305000b50703c050002c000807805201c40741098070f8041d400b050750080d1000600d06139111011106040c0150750040b0381c00381000c0640f00d02c103030440d2603140c2102181d54a803d4424501400f0079000701a10b00041c1c0a10702440c2c81a000358400103049514202e4203081d030b031011601c20100d00303002006000d01d10b481d95000c00500454035000d8103000702907000c120b0000041c0200700020091407051904a0312400840d8079413a4071149540c0a41003500e400781c1d50f81c00a0086210060514600c01c201c5003c1b40304418401c030900c000e482d03888004803d8802e00c50006444c40103103a80030080d503100c0c100c4803440d2600030904007003002c0c141c0ca0039040007070845109081d00300421000700c1c144804668409501508903404403141c1d541c44049100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 335515404 1250 335514154 335514161
    0x806100f0c02090618090a0b0907240302041502011b05040b030f13021002030c0111091f11030705150606030c040b090303071220161701090f05030307090e010e0403030e01 75
    0xa0103454042c80c400300072150b01b0118110000ca84501000d5030243c888041141d11a4410b0082c0d060422000f104503c0104500c2a040032017050307070400500d003684600410204281c2140e4440c090f030745407083e0340410300b054900d1801c410254a492814242000c0c0c5555540c0b101600c100056101c11010894010a8088044040358000c04401d9000b102c501c010b52690044080c3d03030115481c10405024010500040b50b142c840300031704010325190500c221a40d980b91141c501d404001310086105035a64040005049813406000200440901c0c601c0b050a20180109440d02400c020320a00c4041c3ca4a80165000d484040f40c1090715060243d01080c80c42c040e102000d0b0920000c41019108544c20100ba8003800c550000400c08141c0021070040d6104d0308ac0d0740f82c0042d04080501000032815082a42c5a098100e80c00030400b010756031030b510b1050b145800103a409030400030034041000d40010015004008288803c842c0350b01d411484840300d84000d002800b816114015202915000c0d807 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 335516654 1250 335515404 335515429
    0x806010b1b1006030f0b0603030315010804030c0209071d2b170414010e041a0f270105100309030509090406090f030225081905070306020a0806100f0c020906 69
    0x4808011050313580c00e007002c40b00030f42c030003d0701c0d01540d00010620b14203010007124428101384540c4610115803000440350640c00030000c0e820046182401030060f61a00c00c0c0902600e059500c1a58454180f40c04d4004800c41e842054030601200c100c0e0316040800342281c4890503e4910208010f031161304191840d0340c220356001202190000380842c0d0642c002450710a10342c0300ba40c0c2d40440c024130809020454880380e11f48071410100880340c5000b40b5001d0101002c00d0005005890100a00002540f66998604888608411800052000b401c0140e81e404a00800d0b00c0c05019601c00d82d10007900c60b12031600041d0040b08004005018803000d6048013290b80c1d8450041c5200b00080d0070029155041c5210601c50008000f036101e400440855a000580d048040a0301e500005000962984061108220b41c0c2c0e0003001d2000000c1901840540400407450719039000c40c2c500712040109080e10344961005122010015941465000d200c240c000396040e1111050390b180c0b072000800000100c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 335517904 1250 335516654 335516683
    0x101d0a020d060c050d09060c0305090303190c050f0711270c031503030d2c060a09030309051603020a090606020c04091506230d1a0a1814070806010b1b 66
    0x986c0c1000c1101c103602c10f14011449aa0800043c3c0302c24030b07100d4072880140c1700c0300d003d102902240404516154441d1050301914141075241100c1864140059081141d01b6100d8190b207480f824050b081c559451140001c01114203540c90220099194000c20050240e449482c1e010000500000303c111856200420042c2220746a4003181c1032240900f1002d030750700020031001a403500400720384a680c81c180440f420098181c0380da61b0300b4280014020050250201074030b0b0810400800c1045c0090045080e40c190320411a60441c01030018200056000010b1103140010400c41d070360313001c10a81602d1000b100d000c80d000246060802028a00c0c0a52441180c6050b400142c42c612940810014462013110044a050345500f0840603a440da44054118007440e40c401c2c1001c52807071101d0340d11000c0300c4030000d1007a1482d000d141800448420882d251501c400c0b060080310b0081040c07900174646c400050000d903041c040c40316854012034080d56560040c0303001100000e502440081b00c0b23181503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 335519154 1250 335517904 335517911
    0x2030a0c0303060b22140a030b060312070807060e0607050909060d0501020d0204050312310911070b2410111b0a0b030402010206180f101d0a020d060c050d 68
    0x46074040120102d85e040e20a2450b801d001000610107107041003000e038048010506598145151510b0303401c60b00c02814a6418056030304081e1103064184060700308503008000721610b8054915001c02250240d0118045039407000c0200112251320070111502800c0c00d42c2c13440ca003170b00c8110110340c010384080b84c000c3c095400441ea1002c03001c00d640c0508100c500c1101168900c2e03000740b05120303685c0b00f401c00310036907000e800c440c3c807402c1d0074080c40d1104111a046680c030440e03595030440b80b04407519880e02501c0c4620005400342072000b140c41141d084910741e9003541840161420b68035104041c603800c00d018220040e81d40c0002401450b95582003108503085e24504c3d0402092114954410071000e81b1610011401007120142041038070700c5507034181c00510035900c4501d00c46140e1080c440f8080003601c5050410f00364040c040c010350307404059600b004203090f5203d170090a141005004415040ea1210358440301607610013587d000c426400080008210807050400c5503d881024000c5202508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 335520404 1250 335519154 335519167
    0xb0714070e01120f08190e0109050f0d080f040b04080d080c0c0706080601020c04050f040318082104030206130504050a020720030304080d020a0213051303271815050102030a0c0303060b 81
    0x4001f248404900002d0380c41420f007944407010488240146c1d01400d4205d032a0254220001c0e40032402403c206074025202810190f82d041402c0d010f500540080e032841d0000300505840b82e4000108a0304544c2c900c0d00103081040101e0b5003543d60003140325000420560f200441e0f420390013409403c0c82c654001e0030038445448c24048081c0441c40980341100010400022500d1803e070400100c403c0e00c200c1000381590140c90b0510000202d20f400035400b1855041000100581c0ca41d4001c110003070041d65510004e07441c100070081160390041c00c0b0541140104598000240002c0000e50007107940b40034070701c0300f1070f056010034514040c6800c0316560784114041115202d0b0000307003001400b4401c9600420402a084840041e1081034446008101c5040c03030840c0000c2c000c1d0300c0d80c8848181da240364021003e942054415546003a4043c5031401c071411a500c200d2080b6020700f5058091947d8140c4c160362130300000070355910801c4500010484000b840c1d00805120f50404001003058000f00b80c1c8490 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 335521654 1250 335520404 335520407
    0x3150b07050f030319050705120a1d07051012180807060e010209100c140601120213050601090e09010b04060e160201110a050705070b0714070e01120f0819 68
    0x9100300420307a024810070400898071000042140d00c200500c5a15004c0c940c00d581144025010240000f0b080c040b09001800c045140c44003068412403c091003c544104002c400c0300b00500c8000740b0300859007020505000c651103c0e056071030154128645030143c81e045404003802000f01c0c2d10744168019842c020705060201e900058408070b0b000d0a0304000c5469000383d03807800c0340f0070f0070009a080005d4510440c6014041d192661245000d41007411480b10000c82280c1030800036044013801c1c40540c041c40c0254240712000d00c0c2942c4038001c00300320741d0400341d001810424140c490f066203000b80c100050384180003034100160558002d40284443c86e218410204800400c84003200e06480c1ca0641c1d8039468414041c100d283d51240c0c41692500d040010b00300c9050740f040308255494400c400340002c403054841c008140940c0220400d102c1d80050010b40342c1080d4055000a00d0b080c1d01c030005005031000f201c424200036a0003c203e107184111841c068035980036110030b0400d07050855800300f4005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 335522904 1250 335521654 335521657
    0x32105070f061e023f0405071a12060f0d14060402041a010e0906060403021203040602371403070b0a0b01020a211808070906090203190c03150b 63
    0x720051a03082c80240f424040d214124040d01c40d0b10107410701c4c0ba03e4602038243d20000c218014040c042c034800f400d1041d11015240408042e2000c440c00c4d40325420400405001d2011080c0b00041e03441c100d0300d4039003801d5103460300d4440540b581d4403411603d60f401200c0ea40d8403905140055009160144102c0501065515050100c0f410b0f40a03a040c1b01d41907000c81d0744180103440e810416100c0700c07490319a24041c070085010080503580c0040d410000030000d80d83e101c04081c00549000b0085645900b0180001d04201803c8596054880d0300b403922284040d81c043d0800c04054030300701c1094005018101202c5150000c1e0340180c681c04001200700c240140300314106d2085154110601c00800148012642d80700c1d001c2c1c000e880d4410302061703003003000f034201c804001c82c600c80d1401102500d50000308100f0104941d00002550b03210500421580c60306025041c01012100360450a40c5419000140c2541c030306401c1c00c1905613107070401103800340a0350140c80300703c00719411800201e842e000c090440307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 335524154 1250 335522904 335522921
    0xe090103050706031a090f0406020903011815090209070507060615021006050a260a05010c050d1406010e09100e0a0b010311040f0e18060f040b06010801032105070f06 73
    0xd092045590701031640680d40341400b00003030500d05960f43c841010300d40e190b402508c1126400d0b000c10954a0343d980900514051009440d20300b02801b54030f150003e000807851003404219810328900c100907a80d0412600d50050860070a660f85503203e14000000300305035007180403400d044041109800340d0003e01032103040407841c0200581e2303864108020700e403031a6215011909a00c24060003205030307404641c485500000045032031240c5203654080c00d5a80300101c03140010f00201e01d413000d00000c3e01900e4000c884040c1410803a0400c440000c00f0707002031010039401241807101203501c000c44007500702c00400d03000a40c3c06140c148190814003030a4a20325841c0000d0510008040329680c4900311812076090340c0441070301c68034044010090b03000042c1025841d030241d0480c0040703c64103221b05882011004200300451910b850105907805015204d14100080d41d4018400603488039812122407840d84a0071254100074201103e0900c1000401410881303280d4902003001004d4015511 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 335525404 1250 335524154 335524157
    0x702190302010807031b0c05070e010806100b04061d060d0c210212130c1505091005030f15040905070f0806060d050c0904080d02180108090d1e0e090103050706 70
    0x41c2e0740c450300400c0301134a802810041d249204110b0204000b8047d4146421280c406c10035201d0180d603c034800c0407005c40913800700b0f0303a40e0010001c01144500e00c4682c2030103840744902d510f05160070000b004140d4810700309070350012890340318030f00a996945800e41e8800403002ccc41c00d1000010101004103400342500c8031480300607080e030007050701ca191802614491000000c104c55a50384000c440c5074003510900054030100082507000c00c660182d9035410790801c425455280d99001e0380070a0200b1420048001c10400a0510900c100c0d8129040659040341481c0942c40701910518005001030114240081440c440ca140020b030640718010308004039002d400680d85a5601d15081c4400e5102c40c5000812a410034141e401c0e642c0380c0038520b150094014152030382042c0c407407105d5400b280d00420326a10b84680b2004018140c2d030740808850350054022014111035206600054120b03100e401440182c881c0b4401e2001d50144a03000140784910014100100b650750303810503e80f5504580174603030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 335526654 1250 335525404 335525417
    0x3020607090806041203140f15012a020402090d03021005070201050f01182715230c0c01020f030108070e0708070f03060b1801080609040b040215070219030201 70
    0x2500c141c0244140320031207100300064411552640c1d10b01c011191802d10560a05036256580c00925030603446d107620690501402d070006061448034180f816011101c114100280a070000004041d0300c540c074541c0c0000c1c9814001506402e20000e00030f4011103003100c0d080100b80140c20140356000409549081500c6000c01050b283c520f4101d090715412210301040c242400010001308400c084825620b10088100152401c500d24403040b03aa0b01d00c018103000003220790709000901400c4500a0002901c03003034201711000b00010300c051001d5020100144000d040000503e40e181190202c440c0d005074500215500c0b4030320501d00c241900f080c051413005104503900801c20302c4031481c1042c05a00d2a480342c82044d51648011510020981001c0c42090b840d0400010355003401ca014107507504000c2842c43c400d03088240010003400000b00410b115102807002e010100d40c004006070b800c680c05a900c07113001045103010700e042d131290302e6009407c0354401101c6140980c024107180c003070340c0c801da8500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 335527904 1250 335526654 335526661
    0x11b050a08060405060d030503070210090b010611060114060c0f01020d02031009090206090906040e0703030819091e0f0f050d03110909010519030b09010c02070b0c0303040204020913090609030206 86
    0x70131544121900360b00107200c142a080400d0146024690000252045402070030070518104280c411551301210024220b000500200d03420501030280b1102c010000c0c1407941c5006000c00c14042c030120014080c550000c0c111800c003006100c1700b2400d01003000290f40d40c0e1006084000258011034090f03109421400010887c82002d010f030f02d2034650024495070800b06684c040200b20f40028240c113510940e2031000d2407207004240700304001107002e5260f03a501c03807400b004044421065083d00800d1249007034102c1d000200481c40c1031700c2d69840041c0d00c1c402c808007031824584e01d00701e0140c003524140203401140d0800100133a45107a00319155800e0218520314030084115019000c503140c0c0c4001103900503c0301d8108030010400f0100c5072b0700c00c05000c0380c0d01c1c0ca804070807880c10b40740001165145c1d03c4100c81240c041090f2402031840c000c0007854411003500554490001800003803046800007040c81103a9165609a2068200d0034010001c490092909000409009000300d01500074003000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 335529154 1250 335527904 335527909
    0x8061008030c0c01120902040e010f18150c0512090d0212120a0509011808070c06022b020a020a06030c030c050c0d200717101a090405011b050a0806 65
    0xd44202da40100018052080f807000155418130503103141c4100103603100201c1d800b6a407203000c1d006201070110300029400c00c000202c003095803050034000300d034400c01c80d4845001031050606244090011600000c20b01c1441504031440d100b461001240340f95482c0038400ca1603000314654124141640884d4004060f02c4904d076454080c4246100c8400c035042c0000303422552507005594401c0b1004000110aa0b0f0b80b040044c12652640c802d6030b015030301040f010108103c01c03480030098007a90000f4460000c07000b41c14440701000040200001d4004803040d0b8400340200701e481d450542c0107014a0307215446400081c014080318100d20300103810710006140c021301900846000301e943c9000380a001359080b00c00c0d10341420301e00c440181d925102c80c182e610154144042406041c00f42c9645c001c040316082c2c9a850224050300c0c5080c068030700389452041c41c0030f50b0024001c904040d980517090359141c1c18254014040707200015500010080f00d040901d50090090590803241c1e202c0344030b961a00c90a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 335530404 1250 335529154 335529157
    0xe011d0a1a04180510060807050405011203110c0a0e0a0c0c120309020109030b010f0e090610030f05150a0506100201090f17160302070617090729040806100803 70
    0x424425028188260403002c0c01e09800090071441d800041800303908480e42c0c0e0701d01d4030390510f008480301039848900b0300150100340a00d00080604032024820355052417410141e00782e240b07400a0074824000d04030749242100344130702c03003115100030a664100e581d42c0c10039500c0b00c001283c41c030344428548410181034a028112408406400c110514102c0c18101e506400801e00d910302a810301c080030300d00000050000c001c00d80a4150070810048180c134103006004c910f20b001d131100509420030020441c0742d8402c00410360482e508907407800d443c201141081e50900546030325982c1000968802c010851040d5040203004510a842d1807105030381d0b900040f402c031412040010155441502c0f0780c0d010520280144050f40082c0204034a020002e0500000c00382c100b00c012000340e00100f40400401360401c40b8100ca0021503d02e14407549000340302180c50f91030700c0c0684988058004010651494003014010a07003d8400c0781c03581d00c40d02d9044440c1e85210468850b41c411341c0410022a01d002d0100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 335531654 1250 335530404 335530421
    0x10f03050f060105031e100e01060203070807060f0b040507081506131412070303030c0201110315010804030e0a0e04020a1712090f04050f06131503110303040e011d0a 73
    0x310307810203071540801150700b9031014010840c1c40e84004007040c0d804203244445030080b54008426021280341014010103030005901080654206000800201f420401211945580b00600182901915003150000c0200815280d00203181c0380c20004102c2c5c11040303850280c90410080c103081c0e5070f80d1040180f103108030b02a070032080309100f0b07080040d03d4040d800d504441100400442c0e2025501205c0c0b450103165a00c150002500c3c0c818104c5150780a1142c9448544036042c5203241d40b03012200804100c01c00d442090400060500050030301d0f2144243e40440790b801000c91908964800801c8150714040d90103a10a00081c800005c2c03040c40021080301034101400604001219030303078144255000070300c44580141d80901c134000f03c1c2e80e6034445c03944144581000c01c00c060400800380035004001d07601c9a03c00c0351070902d84c03954030303480d0000e00b200300c0798482404080c0840310030109044d03014075401480024074600010600e1a0703d95400380c2c020307042050300c04c525074230300c503140b801c0d03031080b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 335532904 1250 335531654 335531671
    0x9180601050d0905071d01060807051e0904320f070c0311030d0c0305010e1006020616030b1302040e090106030b0606090402120106030f0c140a03091e050c010f0305 72
    0x20010302c0306000b0b168114243c0345002e2070964000765030b03031085c49000030308401e07052401804036001840384d01d4000d664a40c10000c00d2600e01e00b07100c120200038180c904061002811000f02080315501a903440c5c01c01c203200107141000002d844040c00303100200c01e224034241102812103c0000d000e840300c000c2c40c244617403003c0d52806080d01e031980b02503070384a4805017811a1800200036401222105000703002440540b903400040369807404144d950320040c06040704c240c10005603400c1004607400a0000d801c0310390821541e92610030400160001c1001d180c4013600520112420700c400d94007540540229a5a6000080c0e29a1440002401ca0341d50340030041060b5000c20100b080c80c14000064044502c0190006180228100d000c28044000b6408940003d4803022048605030301401400322500312070400c0512401995a02030990041269120800d60744180d85001e0154243e0b007c109440603441c001d03681c01d8181805501c8001042c1c1c0c49000c81d401c1c1c0b5102c0c402510a00c01c40d880346001d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 335534154 1250 335532904 335532907
    0x60204062a06090503120c0a03051501090b09030307140106081e100b011403090a02030705040e07090207060605060f0301051504060807270806190b0114130306060b0918060105 77
    0x200c0e902c41008000c404410b4941d48020700003d410b04681c0052103000f9084880a0b9071160682079005082c4d81000b840003502c0214548000c445980020880c0251000310b4490364641c05000d001c0b0749103000f407400160104440b0301c0480c038070040640c051422b5072512419203031a40540310039101da000b001e900a40c0340d507003c08005004140300c0d03403000440c580145095110314202c81c007401c445800503240c00c0c0320b035000848178008515041050000610064078103101940c2d611a155846101301d11886402d541c0000d200404c00c2400c2e440003014001c02007003151100100898522203410034040c9a01600c2d115040e420076110301c1095500f00c80c015590300540c0d6840060464101d00d00c0706141805120215003805401610280d90000c2e00e0440020b04061800c1d901c0100607131110306002106030f2503d01071400f0b60341d1081041418805d001000c40c1e8031498500040c2c00d900c180c2e44040d12051030018086420030302d400041c07501d42d4080320004110004030031168a480c40030746c0c4a47c0410030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 335535404 1250 335534154 335534237
    0x25030c0504020a1e0306030c080d030b030f190809090c0d0b010c0c03120e03011802010216060207050105070311030a0302070302100b090a0f0f0c0c020306010602060906130510060306020406 83
    0x440c200d19400c0130207140740105217a035032582d031042c1070a03c0d47c01070132954002c0005880c20b80d50611800072541000c4004000f0351450343d414907201c91103103264152103820304010b441402807032030880e04503035806002c01900f0b107000380000006800c041d19000c4c0c65810010220020342c4a0100c60003081c0e0801d503c140c9062640c1e58112003180b004110000f40b00c4844801c081c207550038811700707200e41c001c030800705501c00c2103100090412400445011417402218800d10190b81d000400304152142801d181e99100240e00b02235a0915011030820b82c28480055210041075040d00942072941c4240c007101c1590421640310302c151405e460200381c00c40240400615425081d401900303012a658500140b04480c1c016034000707942614101e440816000d40c800021802c081050700c0c01400c02d44017402c060700309410819203500d8058080c0300c44141d0071001c0f00501c4010b2110000326000c42c0c00400c0840c1d603a28204010750442d12820003c202c06024500310440190b0000f000d00707400311f202002140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 335536654 1250 335535404 335535437
    0x1030b150d06060602071d01211401061409090303040b1605070516030b090a170703050c1e28060c0201060b071416150804030225030c0504020a 63
    0x8040c8000e90344145040005408500340d44114405800c095014040d0f55052010fa620b2030b18408046210803e4600c004001204525665003000381c10311440c5010802207003800c1400000e02100714042d54a072240000d03020301c444030000c01502054840c0c80f01c0341d803498042e0351030b40000c4030041c0180041c0000074010188008090004480c0f50520030f04010301d07503c0c0c0390b142c80c0c521254400340c0349140a091042c003002150060340b0401450007000c0120040e0781300704207400e410074542d00c03004010512504041c092002d54801440d640d00321003202c410082400050240042002e14a005401908500d020007284442c0c042c8140c00410101003610303604c030130003880c0325182c100c2195602c03100030030f03441d540b04020008070740601541c140302016076459078100404000c0504103084690010020114000d40c0c0782020081401c2c441095540c900b4103a0070603900012003540d1145a8505a0300e025408204000366402120061403454498003404101e100e42d14015011400d03507503030301e040707039 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 335537904 1250 335536654 335536681
    0x5010e130b1f0e090f0c0d17041205060406050a0e0703032303090f070816180b0301020c10050109060b030c0a0905132909180a021c0209010e01030b 65
    0x658424904012000854220b00d2659071581141088401200a200318003004003c4200003e00a41c0a001c400e420680050014a10503c000b425012a0f080c4c6940e105030311403c2c3c1c4c0003420002c041058282062401945940f01202c049900e1440d0201140c080d02d640c0c82030445c1000c01e0030080c01600d08549060b039000c0b5040d0111011040140d4802c42c42c800c00d03101a50042404030000c08648100320707062810000103030090201075005061841c2d000082d482070704105c80401c04c410401d420200ca88001030303c6d6103a5a07503003543c00050941c0030300000180c1402c0c1080000d01c00c0080c1d907241d000d10815226548142c2c00381e203405001103030000100c01c005140040321070621b900c030107a480c00482c080101030b030420301900c1e0750743d805845100844140200700c40b141d1300f075030680b140306040010603000300030344030b200702c842c074005000b020110030083d240340749400404030444004040d0b9412561100200200d0080e0307928400010b151408000d01030690703074000e802d4074032940d6401d0101401d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 335539154 1250 335537904 335537911
    0x50915040209030d0c0c290d0e0706020c040f18020108060a0801050f04020405280b010207080604080408070518040818210708030405010c0204050603031e03090105010e130b 76
    0x4103078204480840e5540401c4062a20740240d22012160011070a10081811250340f01c40d49800001003109005660000340b541154102c990043d103071007a80d14804000c001380600503c2d9485204c2020900c00c2d000030f000341c0040c00440f03090040b02c83c010031311002e40306120a02d070030301028045800d00540c003d410160740080c010b030917150060ba880380603609403201503403030f990030342c0c02c0506007c1582080d003e0142d00541080140d400400a0507842d4980103c1c0f4004a155542e24042064140c0c070a01009001345100012681181003130304040046921031300c0784400c50b1051000011b09401d1a21098985464014405900d5a141c0c0c980000b01c0d400f4007031504d4070003090360000c20240c0c0c034619150401003207030485061203801c2d1080c1e54603111903a00407910941c401c1c0700810003a80d1000030f029019a05841c042041c1d04d4210110b841c0d80189400c502d40501400c584c240205500d1018500c01c1492400034000b50b41d85203031080403807034162500d00600c00c0c0c48000001141c605c4010980 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 335540404 1250 335539154 335539159
    0x9090c0913030e09010b03060f0d0b060d0303020c0d0801090e0c0a0605030a150e0f0f1618090e16050907091e15090e09030c210408010212060910050915 67
    0xf44001000008030195400d8108155200c4040207000381070030811500e08111205030744071400088130341c42e00d00758010010b041e148260703200e0349000c0070180703c0e4040c1c0c1c8010401c0021a0032071072505601510100c424020342100a1a290322040036200000e070a28109a0182004000b542405000c070381b15840101040241340d11504280741c0281c040d0414002881c0145080d015404e014440e610400c001400803012000c94905000000502c81c2681d081819142403410760102000a1044a0841540302010051074030340802845403000c18008844400c03190b407000c40944801c10010600701c2520300d41d0000b010350405004041000d18400e1100742210fa48030b88a03076883c0d070050203220b01140741c0000140401800c0200141c5a1401a003184d80c00c0003031800d19100b0700900ea40d4804a040c060940c0c3c10000100c3d00f5400580c00b02c4002e81240c200955a035002e81c80540c1e0260f10940b6410700407042c8400044050000360920720071b444004181d00410744905035000566003945842c20b9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 335541654 1250 335540404 335540417
    0x17010f18020f0a05090f030a050601090902010c02030f06010501020f06010803031b09091f1403030d23090102031504181203110304050f0c0d08090405040c030209090c09090c091303 79
    0x203204469500070f0814040595141c41c1d98107160814400000d8902020601a0f4840b0703000d400080c902055113415036005282c001101c00c9076000485030140c0c0c903140a5010701800f107030030100042c04601907040e103400782c080b281c20100b21000a5560341b400d214120b2903410900104480d0483c550303461492071604800503080c140d425000035151072041e21460f0b211a46980c44001d418400c1000500800c0c90070303031024070b081038000030036101e00c01c0c0b482250006550f06c00800361040d2081d9524034200c040c01c0c001c0b071540b80901c402d5000f58002d440d9281d0440c0900c2d19031400340b81c80d000b008249502c41c40e401ca56268641d640d1000d48590391a41010306803940303c0c080e00807141c072002c1d61095000e207004200b04540440d9050802c1400c02d09140210310071010480440c84040440b0740343c1f80c0c20b80e0f0020b42c40e5190305001307002500a804c0254029020030078040c2440c0001100c806c2c90a00300d8440000780c4403901030300c0e5203040480060f078010003c100010040300500344408180c5001c0e00b00795 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 335542904 1250 335541654 335541667
    0x150307081b0a080f0106051014030c031008100c08060901060512220f0b01050402090a0b0f0403060f0b190602070905250c031724190801060617010f1802 67
    0x2c3d8207200303031301080c0b21450b07540d801c0030401481e049141c002210214140380c000c0d0404051050381600c0014458208208004040340700d01c020584021300400d1020203562102d0120800308001d0031885140000203404030001c82d001e4600744086c14100c6142d91070b158640840000f040350700075401440c82c3d11400451925228003102c0f1018030a034a842264046100450391400030364006040e0401e9005e00c2c81444003280c192034103040e08081d43d844070800c546560001c1c120307907402e20403600020031990416482c545645e9035508a0219940211140640e070900a00c01103c00d508500c20200143d06c2880204101c2030307140d0081d5049011001a00c98001e0a444109000f0f01d55500920000b00c20300c1c502014158400f4400720103d00b04801031055040410610182c42c4c0c120041c55051034100c0f40e0362215540b50323060b01200100405100c007040350360b495014024006071040e00003065540c5004040d040f202e00e0014183c4403030001c061601d07801d2007040005240c0031082c10170015400c00c543c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 335544154 1250 335542904 335542919
    0x61c0b03070803090a0e0c07140a08120411010f120c03090c030b0403020f0303091e0c1e0a060c0206190908010204230d0c030204020d090812150307081b0a 68
    0x340009008214001d55030b071040e07142400317031081c1c2c290f03c4081a1403041c810320410801400031500c0b16600f002d00381d400c25610200c0b443c106410318100a0403008001820f690400c1d00003a03641c480c60040000050701000c2c10015260300d00410000740001e1050307080740820240fa684070b90311150081c98006254184d640e0342d003000c09000d400c02d43d042c00d81c02c001c210805074100200100781c1c4024010310306509007641781c070b81e0712980c01c0440350b020a402c0c9121070030b02c9010481030207801303801031804800704645160907007198010b40c402809600c5001703001c40d98600482d140e804e15075024109524107003800b5075204c000e88a8140c807208020b1003000c005040c2900b4000b40000c0c1c41204000c1103c0c803507410302c249030600d480b0159405420020b50102c0401d580c8403030a41101c1d01900c0260b610303420f0b003840038010028000001e00041001c034003000700100325403825204240d0751308105c0d8207020000c10150780d0802481a41516445034214004012a42c00707400100e00004e0b1003120625181c012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 335545404 1250 335544154 335544163
    0x1020309010509160609060804170d0b091b0910021504110117160e0a120b060f010306030804090f110a2d0203041406070c03050303040b0c09061c0b03 66
    0x260303451140c0d191070501043e004240110842e030745032000c0300d9000ca840c080c40500910018400c9406020000c0c00040500c40c0001201940c03560310099150345c2c214440013070000384201d980c40390203140000e0020303082040560407105203070765551815044c16000000c00440d90745d090314900071070003401c21503c5001000c500303180c001c5201e000648400c00c20f1100041540080076160b28080c401201841501c01e040450380417005160300c0c000c601090200c0c017003000480180d204030000b44034421203806016a1501490192004503000300400d0001d000440580c1c5c414040607082e541c04220812881c0030382e5101d200002115800810743c1c4a0000c00a816604203202d000c000c80c007241c4042d80b08071581c0202c0fa9090540c0301c10000c41140c5110001d40d42e02490180d1001c003c4a440c4421711951414140c0b9a5164400c2c1c9140b40300e52249405600c0b9041580c080701c144000c20003188032120b500c01030750401c0340c01400360f03400c0040410300000301d240d04401500280b41d644481c82d0340e9803010700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 335546654 1250 335545404 335545411
    0x10b04050c03160905130513080a091706010b25170408060f070824060316080c16030c020d170414040605100c03110607020d0f020a151805010203 64
    0x901c1161286405040c614010300c04000a030100301100c00140480d50307600d007254001007544c42d4002400d82d514182e40608076045440500701560204100481c2981729800c20241d4003184034040300b119030482560b550300c0c0e0030b01a150070744900740400032507030000c014440c0b044040a054501d0445594613030034180c1084200315003203024002012b2000700c1d410042240c01c4010311402400514107000014000c41025052000208441416a1038020102504c6403160b400070101940ca0901820b55803c40b401914075101143c00755001543c0000400700b50781202046410550003016255000c03502500820812030740403e21112310030202d00780b0307052840780c80100e89815540f903042028940380740707200e50b00d0248554141030f814011520b80425000c17203060380b81019240c0f07070004c0c07406941c0318014202e0014684600010043c84030390028451107018019101c0341c000b1450050103d03110091010080c10a11484408040d0394045c2c1d4022401d22002d00315010f04a145590341c6402d991098 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 335547904 1250 335546654 335546671
    0xd020901030f083112020d0b060d1401020903070605040e070806011e080609100f0b1e030702070302102d0504050a03031206050306130b0408070f08030406060603021c0e010b0405 78
    0x11000380d00391042c44a0b0b5001400315140b00c110090040e0740001c2a410030751f00020055201c500100d840c03034540b151041f10166002e840c8945507007901c05168003d41090015622034031501c04000344072800b61080b202615820b42c00048596550241510b2544000e07068a0400076000d100c0101150240f00e0310000410540e00e43c80c840c05c1400400008031005001e010148184c00c2c2e00b0003007003031580888800c81e40d001075401c1d2100891a5070310350100134101c00c034800510000400400d641c0c0407400c1e0041e64422100440344508400b02126110b0200c400800d400a040080e0805d00030607101840b0100214902145010303110804101034041c268022000f0442280d240300c3d54903800d0103010003a000030b0b00106a9440d0004130700d00c4100f003d6002601c0301b440036000c203045c01940f0045400da66000040440c850700b1a1900d1030280c0e1040b201620b00500d441004a1860700c20300883d145403a40218100301e04100710101d000a2480b20b0a03000d0a40da03c04402031142c0351405083e100b02c400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 335549154 1250 335547904 335547967
    0x200604030201050105010f200321040b0a1a0118030203011a09090307030507021c0506070509030606040e340e16020703021311360d020901030f08 64
    0x14900642520743c1a048a41403081066904145039031000b00603140f0311005007114503000398045043d0070741c880d80700c03a168543d0252120002c2c80e08200d5540c0c0c0180d100304090051036940c007407107008450410903610400030080341458020b40c850700305692600d200c120840c3c03000782d580c2d0010742101c0340e20580211180c1012b502400d41c0c505112420b60087c0c100014500d030010b666001041c074032450000900c1004d10b03d201c030a00501072741c810803080c0c0c0d2000c211100703810114030180244d0810b8448501c00e108020000e42c1c2803c00340180d010015403c0c00401c0f640c01c100203000b01b4440c0c8100345172075690900c013410f002840c0010074030004100c41903120100342010304010085148559803903065600000042005860701b0808020219002c0d02c000360075075016030901564816841d0300380050f8001f86c24615030141120400040949110480c040c1c3d10319102480b07641d00b41002c5c0a0740c4145a00010808100c54202c0c1ca90201d120b02c1741d25140c041c04225000c2c05c03d403070f6800c04031422603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 335550404 1250 335549154 335549161
    0xf060105010906080103020d17040305030406030203160302090307180905030d0b0907021203010b0a090503010f061701062405090a0e06090a0e0d0e06040f0303030f0f020307020a03050a2006 83
    0xb0040030950152056250030441e0390b04640206003402c6100000400b00140c10b070341c20701107982880a40713000c0c5034000151b0303a959a40c0d8400030702a40003503070480710510740d03000010305c100d00074403c503010200e0280281c41800d10b002003241c0000004030380701903242c0c0c940b6151800102d00744000c002d004107103440011030a41d110140510110010404420755014402c595003001070001034038110703080d9400550f55100360754000c480c0050241e0101360150309101e800350355030307646070064001d03103882080145603080d105038000d00365030b42440350345035010004c81d0899000c03280c0000340e04085803a051051030701e0420408100c481629070b015032400c032002c1080c000b003490214805900800d00310030602010400203500d03510b805200b118141442400b01005038242c0780c1e01d0941e402007400344061a0544e40d2820060090903155091594141c0f610803000d114050754070035640074503415030003844404495503007510194044004141400a9411070800710f85403092540741018185000d01141e06 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 335551654 1250 335550404 335550407
    0xb04080102032d040b04050703020a03060f050c191b0203061006020d030203040c0b0c01090803091605180103080304060b0306130318050102100c09050402030403020f120f1207110f06010501 83
    0x1c681a9031200c0c1c0043c040740c82c9074a040300e02c4040c1c0c00c160032404468140d01d96142075450101d440d84002d4201100346000418060640c1c071000700c0c000380314070500541c0c0c1c404940340c5103803080c1c0007000c84043da03500d1610903440c41a01030405001040103120b501ca519900040c0c90a8070440d038a6091040210303042c801c650b41404801c50308066801c0c01d50540c1415514085418414010050302e428041421913114400750003800241c0d8200c80c0b0747e541c07810300452054668900e0a00e02ca44110300d0740c800580c605140d01a0f10218451601400180c0d00f10340e1642c1c0140e0020b80300391400c40e04d074850078140c0d0b6801c0c400c507401601d2414800781000b840345005000c241514400c1c81c20501c1c2040c0811440c0d8000c541c0c40d822080110001560402e051b42c15151072006401007904580301004001c00c064000800c050a410800219a254150311881040c02e01c56170700c0d158480c51061015030700030750a180d43c03030350000014180170b01a40740c648005d40c038143c8038202400143c2d001e034004020302d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 335552904 1250 335551654 335551681
    0x120608070b090112061404020d020d05010303020601060e19050103021605010f090209060d0201080402121911041d0c010309290609060a0b09060304061d03040906151e090b0408010203 80
    0x12072611045c00490725080b0040e4400e40c83c0100d05010700c0d00060303484250111541183c1051403642410002943c6030b00b0029038913002401a00c000c1218508101450b15081034042c040d0000003140020307003030030200118003030340200108441b0703450352884d01d40003e28207000d00f1141d80b000d084000b03940440d03801044410400500384501070060300b881c03800940da2049100b039200c0d405540380d524041c4455070b01d40c43c1c242440d640003405a01c414083c400c11408003a070003400e0404884c180070032078500d0b03005e00f08184502c2501c412076010000d90450365009401c00d02d480c034001c10100c540e0381401d00c840030300362031401c401e00c2c0c0c816000400c0207510301d80540c500b034111506640c0350079030070300b041480c400398031407466894030480010001a0410a107034104c006881c401c421051380021400500503602d410600680c281c5904014001c100140d00030107405440304035030b582056683c2000d01c40280c2041012115040000e02807001c10071411040c01000200040d000042e52444c1800f81040030b03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 335554154 1250 335552904 335552927
    0x504230109090b240904063b01031101140a0201020a11010614010e060d020a02060f06041a22020a0905010201060e010b07080c0c0d2001020d0f120608070b0901 70
    0xc280c40e09000d929242c84060074030082960144c45610481d1320400e802c1e201e0301a9141e0f40b64054100003000c50380041c60005014800e04041c0134207506580254003004a04180d041d451804211500410101e0090b09800c6444141070602010303120a024564032550701030384009000d03079000103600900c1c1c0d521549103444000400001c0081a00300f1003081000c101c0030001d0f904100b0000a030390400d6480e40101c0314a081d4085045640b40c000040c0030751258411291758841780325200c009085070506000e2014a8a010175210b000c0846c03c004006410000340c010650b401c5503040050800a2584005c0011103201d0721180c50151070107000a0945040c2e03088000304105c0c3c2c0b401003000440139015504400d0380300000d10b0701c0d10105440d0518001040c065961300c03501e1001d08900f8002c00800203225007510168130725500c080d8500581c4e59658110003100010826120040c09034031641403150341d1040d02401088441d61001428070300040c0b600b00d10703502d1000003001c011f20f42e00038014645 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 335555404 1250 335554154 335554169
    0x190c15060602120c0708010e011d070501080402010809150906090d050408060a0b010c06050109021c1a0907030b091f06080702070b07060204031a09012d09030504230109 74
    0x800390030000300a4940260f12010000c1e40b0300401d0b4103d001c00300b40321480161100c42c008028400340c80d0000c5001c0d140114400340d0040b803c4500e25060310000c5020300607103c0c1a16401c2103603d0760340c0110740600707005012509038050b078080d90076606d401e4000240505a64801810340782807041000e81081c10103850481808810001001881030204a165122417000c000040070b1610100584030220032100c01083e0518140c000704501d111070307001d00409244440403040340803d1003203000845168028940c040003110505085e140b50240102d60f200345603207001310386a0311410114510f0364050725040e400d448001c0b0607109450384906560010100342c54401e009003407001001c0d488500501903814a06030000d0403c082c8074464049500540d0322030f269815440e00c5c0c000c1e4800c8800180d54641803942044903004032031889400110445041c04030080041c040c24000c00000e09210104030300b0300c2410702c000103118000300c000c81e52503c1d151825004890401c40010b001a490344c02c4940d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 335556654 1250 335555404 335555411
    0x101d01020a0e12031309020703030b0405130609051204030302010b0418030903200a03050c0306060906060409090f080f0c1516030e2b171b0f190c15 65
    0xc940d0b070380146282c586010607580703400e008800c0014181503101e50a00d482c0051101c0c4400074a00c11294001e082d824000e036400c00c101d65040080206403030040c1c2e160360402c1e1140d482e004c0803951990244210900c80c80440d5402c58130030100e01c015030450303801540940d566444449641c103042c001c140c4c042601f00c01c000c501c2801c139580034100729020b0002414002010a452900034103114684441101c01020305841c16501d00d4619568420191003500034001c9a01040040c144400303050b000740300c000d184906150801004500400e160903054507a01a40c070391176408501140020304020a0740c41c1d255660f403881c0f01c0c81a1030f20724008209205440c00d0030800c004865800c5040c00c5e0074803240b401140c0458040c0b042c600d842d85000e281e40c1d540d0003c035200c0c5100724060a010600119a8444044080d2000785c01141c0450448154610000808a43d8410303540040140841e00e101e8000c0d0782403010302024008581800d14086010404061540c401d01440c2e040d0042401c103804c5051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 335557904 1250 335556654 335556667
    0x120d0c140a05030f0c0f060f060117010b0906070c120b01052119020123031608131103030f0c0a060605030102090a050405060f03060405030904060519210203101d0102 73
    0x43c0e502d100c0d0500302c03180001e0101d80801d06401c244001c10524016a04030303062030038400b6840c102e000d4199102400b040c02ca00c030702d02200f88101855812240c1c10303200a800c04c01140c00340141644000300c1103032100900500031448881d80300100200034017400c11a90300c1d604000600c0740308620401100c0e0800c00000e15214130320800680c0c0007000040e0034a26000c10198030058414030b110101c061000032102514503d401c8624000d54840e8020b411300100c001074650090b9a2200c09a8000741e458285400e6640421308100c03440001a902034100e03450030314201c42c40000d43d000100d00301d01c5604188600d20503c52107015000c0a00300c120001c42c41d120000e400030f0035042281c4503640c0515100c1c40012030390343da038100c4943d0318007004e400d48020345010300c0c1081e1681c1c841d51030684120b240c2500803902d030812082800d0740030300540c070500c01d25041c01c1d01903000942c920854410712103030b6420640161014070006120b641c0c10100401c001c0580c0b09500407001102508401a03881400310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 335559154 1250 335557904 335557913
    0x101e031202030c03040b0711090a0903031505090406020c19050304031109060d3c05151902090d061b02010c030506030a080d0906061d060109180b120d0c140a 69
    0x2150219000080310a0b650380c02231410000700941810000d61001e200400c2244201807a0000f20101d4801d9408000c010302c81d030344020390300711280100f50700b0142e481e002400080d0980d0050000500f407d00b02c03800c1002000c440c1000386e131440002c55140d08081410010001d120105002081c0d04580c4008203140900c007049030300310018400307010a4490902064851401c201410345103e15015081000c1000c0ca050840a002007404485134451550b007209030300341910b0b160f405071034501d0307201c40c480c084041040c010703420444040e40c2c4420003000c880d000840601c0380607251805d41c408041c240c4c0c3c0115001c0d00715141101c588042c10f00300300c02c000041d540410401c600560040304bc2d0303110322240b80d102005280408000b4041d03441d10300c0c041140b881030054440318012440c003400e015601d143c0115808407551091800c1202000c0e200488200c85400c8108840d0700901008500000c240040d441d00307154117408404144003a5900080c01807211001c0411488c8100801d580c0c0b815646 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 335560404 1250 335559154 335559157
    0x21080403030f090503041e05030102030402010c080c07080313230f0103020f04182a020a030815101d1507020603040c0f06080f061f08101e031202030c03 67
    0x341003641c1e400e03810311100c03a0340c1e10145500d500710040369151038030380c1e1071443c101040004001d0600ca4928000641d807405001b120700c5664180c0d500005010035641d80d03103454003c550030300070764000c000011411410810252008084000c00c41303040c02d18010800a181000c842018900c0c1340c00f00d0143c0c21600c940954003814842841c005a4991032525101761740d00540d04400d4000c03052103040f0304280c246802500036081602d0400b1840700301c00841542c3c2d8190021441d0240e00145541008a406180d126501402c04070710001c0100f10600080d1480d40244044d9021901440171848580c1d524508110780c4002034414400511000303d5200960086203402485010004000760810942000356002410400d80891180340c64000242c414a012a4041c02c2c0d911b100e800100d00d403400b013044401c000b40d4003c0001c14a28041011900010024180c2041290407a000168900312080030b6402d0800c404001085604526101219060743d0b0791500440d80180403000c0c03200401300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 335561654 1250 335560404 335560411
    0xb0102070302060a0e030304080a1e0308010e04150203070c03021905100506030708101a0d0803070e0303250b010506070b01122409020a1a070201080402040b1207032108 74
    0x320f0041d01c0340401c00e0102e6010a8150702d668160201090000e425800059010106c6114801031410181c600c090022500c080301000360002e176220004101703000210040c50f800c140140c00020201d070b2058614002c2ea0300a64052001414207580582455410300c41d03240a040b14000b407082204440d110701d952600500718801c1e00f103640b03502144080e502005100010f040712003d58820304610700c171090040030300d060204004807020814864614000e514104031036840000141152241c1030304445c55240340140d15010f01c01008030000700038903070803401100340310007051b1075a4800791b03d0401d030aa0b2041c0c3c0286c2c00b440b0140030040c0003407018040241985d04030032540c0d061007250704244c0c881b02d00300c410700d00360362915494013080800290020080c40c7e0095610081d015950070061645644400d202c03641100b080c4a0840150f00c2080041d4000307000400100c1c220400c1c5001400b04080309090201a41c4410340030003c0000044212130301408418403039405803080c54003c1c24001c80207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 335562904 1250 335561654 335561659
    0xc0d02090d05070e0106030c02070f06030b0f040f0209040f020a0c0b070215010b18030c031c0507060609060510030603020a031101032013080610061818050f0a0b0102070302 76
    0x8218500c160300c80000c0340721201c0d00102220182503032400380b91800c140c2801100002414551020f04280c00000e40c0012030307214110204229140c003004500400a140c0003540c840c0305040c1c0c181d420b036114020000300701051803006135a00440000c200440d541003a44009460061245807034081d00583d181c001030390000d800d1001c1c0c5d035454000701d040c064404480030303840d050400045004500c010180011030000759051030b000d1800000c1507079442807071841300e80c07607440384403400d11555810701d03c20303038a06140c2003480c18241c0325075500c412f8034901e40000c2580c6944100c200564541100c070f0079014001c40c00d080160b80e003590003040c80e500a0f40005042c1850721444c04245034840e9220741030514540041602c0100d81440042196018044d0480701c0c410015002c10302c072502283c1580a04044201c2d0100790780362070400d603010301226903051244005000300241480544102c0044403004060000e82468001d840242d00800a0a0030407034034540b10009280b83d80006600041d240c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 335564154 1250 335562904 335562907
    0x10b040308070f1b05040e0606090c130815070e090c0702010305130f03030501060e0406060207050f01020c03030705010203040b180a17190e1206100314071203180e0c0d02 75
    0x508001c43c1500c00507100030841584c00061100001e0842411025514111824041191010029651342c0b50503107080d94407940020214085082e040c00400000b07031150b812120950703860302400d041081c020000e046000c807080810600c1c60b800701c42589042411204111103080c807581415090040c004000d061569550208440f0601c80da6480c1803240d10030440d001c40400d41c03038010050b0000b0f20604000c1041036070301c9146442c00d4003902050302c44a50080010510308000c000c0508040560181075000302e00c21a0307065241800103001d074030302410016907281403910780031040c6403005099034948150a000511603041c007141030900a1b07004001c10341e008118090b2547c161040b4650402d41260b20ad00003d40380f40c105c40d108071001b200712000d000c240e802681d020b448a07022a01088084440305050000840c907015100700034031400115006591107a80c08035031000602e20a030040340c00c084948400b45455075003000501001e041c80b08450410f0850865203008201c40381118580 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 335565404 1250 335564154 335564167
    0x1006050a030f0e0a030801090c020c09100f0806090f01090c060c060b030601060e0414011412071a07020f0a0302060d09020607080d020c1c020601060c14010c0306061205010b040308 79
    0xc25040a09011102c08040100e00c65080c006640c8202400048010520150000440c001a4450f20300020a950003030b200c4071040b402003022540c4003c0520300382070011a00803801e98104000c0034041c102d088000c00103410f00c000e07030070701e440944112041103038102088280050a2081882c08441590a0000c95a84117240c01c00160038400d071403d416101c2d00300000f80003030784008d900003d500706582c10024800c3c00b203007081018009008414400e88900b84030031b400c0c07c09800380ca10740401002078030441c6455444901520381c09641d400729505012840c03000b135242000c000381d0000b1044555408003031842e070100701136014074503400f460607565265403000e540302c80301141c1034164004c5103281d582600c0000c1d4002500a902d90030024400c0620050182c0000c40c2210042422030300104040c3e1b00e4503004403190038a18000315130285104a12012a1000b401403c3e501c01841d200824994181000181040201e00d030900d50390b824480100030051102d4119003d503a0800b500c1c03a078461 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 335566654 1250 335565404 335565407
    0x100b0a140d24090303060617040507060c0201050c0601030b0105121f0b04020d0204080304090b03030a08040b06010c1a1906230102151f05121b03011104170111031006050a 75
    0xb119482452601800c2c41c81c21030806034143d2016007500c119807a1442e50840c1000180e107556002c5500401590140798184400d030700400c481006144145041890080c5200d075282c1054400e0380b08407070324100038006008610344210b80181c540c850000812110700441c1e1480e800c46c81107030b401c500090342ca90b4140000e8940ea01121407000902034195662907030755107013598030750140c40780100c0c0629000e102105840c0220480715420601d685000403500c03243c856004041000c0c1c041814401801c8001300040c1c501071030601649105007010146241038400c111158180c800205200d9180503001d10103480e600c24001029035086480311042549200180c4c81c0944c041110841711540030304024109604008039501500825507103400c840d9a5024030070381c40050800109950044541544640b10294042c0b83c000c20040c00032944100062000c1c080d030b881030304514422905140e144c0c0700c040d4240070300450081c2c0721b080c0601d1890064406480151280981c60420800080249149 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 335567904 1250 335566654 335566703
    0xa080c0d0e07091d030d0b062a0c0a08250305062a09060d02031e07030f180804050108100b03070c060e0c151605100b0a140d 55
    0x244401a04001040d440124142d44281501c02c02e00f00703a08040071900030f225642900b03501c01c40240e0040d4207200100d1100c0001d407240c0841c0c29040030701400750054403101410a507100703d42590550b02d411040e100c049061141d103081d03440c050792640408100144000480d020103c1620707008080c180810041d03504046095800980b05204020034009200000210054528500b50101e00c0160280c60f041c00e180c05100822944040300744203007806103072142c005550080e001c010748040c1c44503440551035201000e031800e40009950305d6040394140c0d42d6100e242c1000c01000707080e0705081129500c4801030320840c05001d041100c2e0380d001c42c82c202d440600703000c054400b4175100d0740c903460160001091a41c0144050b1081801c2c1302940080084c041030034002c41c04080c0c000508806400c04201d544d6008030305807030008182d40101c401040d414409402032000c0d01e080403a006c1d42e103000700072407049a41c100e0004c0740c8800034541d002d0b90703d9a0b01000c486500c090703000c00f0400c1e803401000750b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 335569154 1250 335567904 335567917
    0x14040b0301020c1506010f0f050f0a030b03010603050105150405040f17040320270a1805070f050306010501050c0a12140705071e0b090415030c0909050105010902070203030a080c 78
    0x10f4496160401c0070154003002c01d1303119078001e0343c035400501f0305008102c0c1c0c01006080c40c0c1c0003207401004810600c0319800020320408a841c180801c030500c0220210342103401c1a8829205a59150140144500b4211580042030300480d000c0c400e60501e5210708511030202407004000a107034030b40d81c140a240c01d41c00d07180203640100041100e00d034070081945450341c41c0d805d094890000e0841851044002e00b1003002104440e442809641c1c0d103a9140600038030030144000310340c50204d1602c5000860400541014100600d0b907800090f1a01c000c1c5854a07078103070030050501c68117008251107500300041003002e05400c41c0c0c0c03541c03040b061000c00b910f030003150408051440100280d00c0050090004a4008850100000110151100700c0b000c840e6540381c003440100d01010008003102e032509400028603034600c0101221910b60b80c0d9203d280d441c00c0d0b80c1c480240d080c1c036a482101440001c0c40740500408009030b06602d05102a07000980764071902c03d9900a102d070f00707000b040180102ea01566603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 335570404 1250 335569154 335569177
    0x109050a052b110414011d090f030c010605121906050c091c0b0a0b0102070923040c030c080a02150a170a060f0519150c050d080108010f0614040b030102 67
    0x100721003241080f401040c40105094000c506182c1250041c40c20384404030304031101c07292181185680004440d240306030180140c1018460207021401c0c90f00f0500080c0a10940c62000042c86494881405180d81504034148601d4010071290f0100340c403045c1000130708aa02c4000040c0303595400c118a506406104c0e115500301d100c0b00003032900c0381d4104070202096405402c41100301d54450303c1e004283d4032004c1519005070008135080181c075a660700543c2c0000781c0b60740d0b00303032032502102c81c10100d4000448066030a1030b00c2e1081001170003076008409015020b01006842140c0064020a0401c4190030360305200307240014000714003d01c40d2440216405c00d040c11400d103070070410081c0c030243c14140030744d04042c090150005410315021800c203600700c2000c501c5408052515111549074460101200103200004511400241090001c04a08000c9856510055042665190845420056081c205842d085042c0040040e900003224080002c89000ca148804d4a010902a00032000401c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 335571654 1250 335570404 335570479
    0xa02010f060f03030e090c1608091c0b10050d080903010902100e03010b0303091810150c0b06061606020a0210020d0f1103070e040504031403240109050a05 68
    0xc0d2925860542c60304680c003a40d41c2c101c803a80303a5420045000d0040d180015595001c04c0101440c0000d079540c11520790050000900b030041c0640030814028404040c0f03000c40104181410402041109035030304020b04a505580741e03070505010070b580d041c901001618050010a02088541c0c0035080b8202456024203865502c4c40c1008010300080403211134030b84039509010810390345060000035240204801070080f0004002c60745a440802406000702d40441d0102101003100c500383c0e9041c0502c00c0c01031340c40040007121420890380407500a0038861150b0403c0050105a1003440680e4102980001c401a03489403070b40401d80c030300078112400a111600102e092161916a9401800018070b4a00700780500701c007141056a180c88111030050210780c1d0142e14647d84d00f8183d01a6078494420304103034040c0f1089c85940b8aaa8000315600c448407424501102c40d910b01c522054441c5a000703003080311f48181004001504102c450003000e000d000701d007030070000305134200b01c000390040307070340c00418 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 335572904 1250 335571654 335571659
    0x3190302150c0d0c0e030705010302160f080c06011401020d0e03150a0b030a20030303071b0314121005010503070906050d0b100207080d0518040c020f1b0901290a02010f06 75
    0x207041c54170b491103e2031081c09108030002d2254041c0c0219040d000030a2548a041074450b950141307410045417040d41c0b505818460300aa040701003065901078151011100d01440c552400249010b42c2035a410701040a05c0242031019140003c8044150880c503509600556440840900401c10030b084c80d42d05216002c01601849080314041c40210315070703281881780400c010b06140d540e00c000d45004001482c00880e81110816403d5240745451003450701c0918614401300010341600000002010818001c041c44082c10101203514000c1c8000c1c00c2c95411454240800742c08469144501c0e414401e0008003850600c0e8583d211240c008001800d08000ca150030000954a280d580245030310703445117071448190540181c00340c80050903400104041401e1003018000a80103410442d41980b1a621141480c46000d00c910041040c2d0b190101c0071503846a402c200d00a24103a0021001c87d0b0503c489401101140800000b0a446460380c3ca81c1c420394060304078014890a10021061894000d02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 335574154 1250 335572904 335572907
    0x170f0403080a022a180601020d050a0219030806090907050105030c0c07030f05010c0216030807020609010e132f0301270c020105010e07050a081b120903030603190302150c0d0c 77
    0x10300c450304c20700361820f002051045030b080400310b40560b8581c1c0540e0141291038289480b810040500041318415699042131710032520b00d0a00b64904100c1c0030035403c008129440c1050b1f00180c1d1f01451000040420750300e0100017038082c1c1b0014021050000c00002ca001c0d00400c00c20024000b10b50003122081c16141c40d050250003001d40800100041c050b20b81c4180c3d418900783c4030f000507250000c4200f442d02c1d920390300b00820740d4041d50680d41440407030000401c00340d83c1c0603500e00005c4c001c08004101c1951148030380702420f208002540d02c0a6080d03010b0440c810440b41aa81982d20024180264116186c080c0748000d5400c594a44030506040745952280e0f81034220320704032751003000c1080c525150203205582d103001e200010800a2741840016402c0e800c010080b81805040d401c1161500401400007031548030203c940c2c0003103034400800d07c1140e0804010464100082059444110040e550025182d5042468001002000c500400c2c56203403103030101c815114145104100490b5240b00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 335575404 1250 335574154 335574223
    0x1120e0714100206040507180f05250f0503040b04020607080a020a170408060712060f0f0f0501170f0411120a050d030213180906060b0304170f0403080a02 68
    0x125004254030b0402c0040320b800000c134540038076401005040c1c51403e225a04041c000c1c0e801a0400315600c2c0d010b800048031207417244500460f0a0710103d4103884004205200040250700d071441040324140c9d040050742e60103400e40343c001d43e00c281600040e031608d0000070146d005400000e001c61030001040354100d0380001e070452485100c0e80030b10040139001c402c0500c0c0d5014500c034136031094100700300040b040c91207440c0c20001da401e103002c0020310075210224015004090f402c000c40f00e0f000100c09111400d0345080740c0000f00001d1800e5551044c2c03219294000c518060403034100c100d4140c01260401c000034006003002800506518003407217500c0000c583e076181d40c800640c3c8034051403034070a811a00c00d000301d4002c2035141a100b065907141510701091445a140b11b14415030307580c03915400040050051100400544003095101c1c00c1609000e12403100d15042040142e20070003a081c1d640f0b41c1c250a603001c507a00082019229101300c5400c0c3c2c20401d920f9000c605c403180100001c881c5244981 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 335576654 1250 335575404 335575439
    0x3020432090f07050d030305060301110a020307111c142401180902010207150c08070b240a030803060619030e0c010801140616140703150504030c0201120e07 69
    0x11518030400070281c1580300c580a008007a0000424105c50000c41d02a030072081d04050b000c0d000140100140251014a0b04040148001130b013002600324140300328002c94a43d20003007245c1003030507204607510b0070300062180c100c001c000480ca40743d4206222401e0251038002c000e0070910380c2d5400504144400420f03000d000703010b543c140648442602501600c15449080e5061700140740c001d052090850008078a0a902400c110440d0804400981c403040a021000e100b503500324201d0408445a6440a200f07482d10aa14190301080d0a000d644008154044a03040a809540c0c0d0300da0401140c1d81c4e2084c2c1c0e072005102c0f2109694160100d80c10b500c140b2882d10944182d0302008001c8004664901d130a1044030283c003a101c0400c0e0052034003d0043c003c3c05d031065056941108159525000d8244140c00e000441d00f20084c20402d0103548445056080d1040324100010714103030b079014108101c1090040c1c100031111040800302d01c020f40c410800c42d1510003c035445541e80d021500429060b54 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 335577904 1250 335576654 335576671
    0x7060605011b030c081309020d02120903192a1b050d0f060b0103022104122a0c0f081b0402070305040b070f12050306031209010903020432 61
    0x3140c00408500c103603059030b403890341a44c0e44034500c501074407217001c545c12403042801342c602e5002001820720340030320003001900702c02035001da20b5101e80c4210001c2028010040041a001000040b0142650f03e95201d60a0134904043c00142c404074030840c5084081941e0514004400701500c062040202a510b080c2e16a40b840700101520780c014801220341d8074400401c2e05c0180c403103840c0000d18a03004000701c410185001030070001110b1070040700721601e910441c40620150288400e0168403464107c4089031414042010901d03054402d5400104494100840c58141c541c5020860481d505100800701100260252900c50002075107440d8004142d29241c240104851550305260003602c501c3d6815032500340c04c1c18a80880c40946910a1200700c0d0020100e0030080c0c0080c0380036200c180c03146a1a550180c40c3d15000d8249072a1500e003040c2029480410b000301802682c3c0200f0200580747c0c19900410780142e00182901c4001d005140014000c0f42d06400343c040d122040c0e0b00b2845500704 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 335579154 1250 335577904 335577917
    0x16080c1b011e051608190813020109050f010903060e01020a0207050a0b22030501090f020405060405010e180307050d0216090203010b180609031f0c02061501140f0706060501 76
    0x260801981c102e203041590300300d88151061035250140c00741015184144000a07404414400c507a10303082540d01404400411205921303c92210700e42c0021000e50103c91110054907116046e00085d045140c5031040501c1502c4000a030310b075591182c0b407440001e40d8400701c148411040d5000d194040e401c002c00410040c803a800340000c962a1026048040ba03224408040c40c2281d0707690500b0440d900e401c58984020580140000041c1c400d2241010181c00f6019003010001c882c810041039070000352565101e00e04200040c02101c0710014107980040400c05101c1442e24024000c40c11806403803400b0b1300798020903585101c0f054005c01d880d004040c1c1d09120100898850402100303e000c20b0040f050100e0091044401d140c00d01c003111490301c040240020b00b03140c25940028540482d01c03000741030001c50070341d10003041c0401d07009101e8082c031540090b055600e0824010500c1032014913501341000b00c0c00300d0704000301c000c800884884200780501260b98508a0400001030031440c801e142c00502c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 335580404 1250 335579154 335579203
    0x20d12030e0d0207050a14010516050102070312090c090e1518120708120a0219030b120a020d0b15090403171b090f010e03030403030801030c050904030f030216080c 72
    0x4041150b2090b554000e0805a01b18103029a064845003d0740c04207060010400500030040360751480c88201038402d07400540d48904d00c0c94010251a40c0e0f40614002c2410300c00108005441125418181d429140c000552240c002c41d842d8588182090300c0c6544800003410312070f802c00c9400c801500b030300800003160350703e10006221480b1480f5108000d0300c03401050002c0b091420407500343d1508084102000750030f10000d02c0c040c4008034442241980425a1034105c1d408604103c800b4421f0343c0030990151411101c0c540120304040f07210a4010400e080840c009003c5c8841e0860708420008041c019802c1d074a41841d0181030013503888504403184040c00001020740d00b5085600e0040041c42c10a076040001035014001c080244c0440c60b414403036800003c030b0b410b880030030180004500030303510f2007880e524505010b005070350181c10584c028000401000046608039059500348441441c0069440c0d840c40109a004008490001d0a010b40024501418800062231034449c6c0b0020035902034030710 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 335581654 1250 335580404 335580407
    0xf12090f0f06040f0201090b0a051206041e02090a150c03021204030f0209180609030a0e030d080609090a0203120a02010f061503020a051e0a1404060804020d020d12030e0d 75
    0x40c8041d500400c1c0d110400040005180300d04250301c0c90f2060514500190f00d0f4620840250840101c00740001c401160686568800040c1e1a0b00080c050b00c081168010340016002c00100e48012022001c0d0000307010341c642d071140003292b802080d00300c280fa10300d01d6040c00018181d118609041e801407180084074030804c640b0000301c40c02c0300d52004a0740e00d1000d00f5403d00c01c1800d002000d0040c000240414504116800c7c40f4980c0b040745c5000281d540d4440003c8068040e1030001e070750740d000364003400c801c2100c150000c1c00715800c04011912400155039403100c1c913107043c80b5004001d42500400781a03203001a019005840f2444040d0000c2c010b140c64041680111101d500c41c40040c5005400f01044a030700a900500d0000c0c0a441d1052420300e440d51040c1c10001c041024024002c000101280807075440340f00345402c7c1d83c3c84c94191385010302d400c40c000d04442001c3c00c0a40f169000300701382c104546d21007486000c17160340321030361500d817000541014004101c12202c0042600071000c4070060907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 335582904 1250 335581654 335581663
    0x219030314030c250605180717060a02130b07060c030b0609150f04030c0f08010e0f0c1e0d06061701060812070c0302060712020d210c050f12090f 64
    0x11590041040c4c286055011003030640540400646040311220203c1000b0031240e015841c41554624032442400e0101d504581c60000154000c2141714000e0f05004101000810216000311060501503107620388800c401249101c65444841c001e000003403e84100800c4d504045651080b98400304103602c0d444084c0000c0d07200b21307000c642c0e000c0c01ca4428000318a5a26020788031034510910424201601ca9662041c42d1082d9000307448881404a01003010402c00d0040c1a41d6440040c05005810548140f25550304040040300e8480c0c090390300d00e1a1034100860340095911401000c4070550301c800d061a200401d018001c01c11039003d03800c40085c182c0414001d050482e01c4210042c80070303c019440144003504074a0040740e034020a0580080541d440001402d9030500801c03101280c1c2c0021440a440c20b5210000c0c5030920116108503021038100c00094076816860503c041142d455484084a4606c1601c041006100c00480d40c40301d6203102640301d40c450207080044034505074862241a948 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 335584154 1250 335582904 335582911
    0xc0c080702041a12010f0b01051315030212010b0703020c04110a0513120503121006050327070b0909090106030c1502070308030f06030c0a050105190c021903031403 72
    0x400104200034401070034035901076011a051590302880ca01a80b20000d50b60305a804080100c61707445000480c0700704102d11413015022002d08103140340c28902050740c1c10407043c51251400501e00e62213100440c90083c1c04549019410400303c078103960b19030194030440d400101007a001441600c54120310741c140386c0b103056001140000c1e2103041c20145c1504403407030340c80404041703030350125844009600d0001404100d80c03144103102960300c81c204110001c401e807030000c0c40300c440305100036020820282c211088a41103500d4840643d1082c6404000202a01c10035954107003d00c01c1e0700b80003600e54416800780c40300032011141c0c941079480c2c2520f09400d803212400b01400d0743d40340c01c004101e8030300810940d4403481498010f90344c42603541e484190b6290030440711a1a030482c40820020b503480c050201a000c004101d8030394a4081c01c1c20002403a0340603142140480d14910007501202900810032901120b50040000d41c402129085070850b0510358441280855200241c44007d0310f19841a02e11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 335585404 1250 335584154 335584163
    0x120a03140732030c09011806020a030809010507050702101116080708030903030d0b12010f021312120f0e13020406020f030304082b020c010b030c04140f0402120a05060105040c0c 78
    0x1182c83c1e604090130b00e54043ca8460b8140403600b043c00c2c0742661020550801001150050b1104207040c0c100501072640041c003c0020381d24080c02c004515070031800713981c440c580582d2005c0791800e1009040e5850000d400d000800b80c420614801c1c00d11801424600968000c0d400b83d4214070ba0b6080426030340e0203400045941604140800303040c25600d90321041c280d1200800c081d04244106401070300310362640c0310744e00d00d59030009000200b4400c60b98820b0000c0070101400e40803400e80d51a000108102080ca820030058072790600148544a28501c030781030304000b820021400555000b44000394003600c50f0300054003031200044c41d540c802105592141c0d4000c10410f00e17002004d80f550b50018426000c0c81548844c1004c2d010203800e10344040c1c1181e00450b000001d880d101c0351308148c68141d440e05024411420206071304d100a41c00f140081c3c009500b22802600c0751034a10000e0404070440007950440d104a00e400000d000c00000d40038101d0314195800c10000c009002c0448444040240c041d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 335586654 1250 335585404 335585407
    0x1020c0703021c140309030d08010302060d0e030d021605010606030605090a11040906140f100905220c09060e03030304030c030813060f0207061a03120a03140732 71
    0x1000d8201850030f44584000b400350440482100c0d507802e8982140701c0b4040e42e00d82c0c03004c240260b00382002c004007841242c0900b0891141e41c55a40000c09500c180031504800c90b40b608411511054204141d8007410b0717840509540321003421107106550307100f0020a90390b543c01d013040060300c00d01920171070003030b50740c0035110003a95661222540d000e00081081103807118000c020001d076180f914401c4074060429841209000c100000801c910f600003070080c10712a400c0b00310803050854001c0c0d4801c048803030544510801f03614a0011504c0600d2101c00498190701b0130b1410303000f4592240c00a0b068650b00d442c3d44488415050a06643c0e01046400402044900a1040c0400c0c015500245d000800e02c80500c1da0350100d40d1042c0683e0b0b6540c80c920300701034021801d80104844c500441580300700d41401a1084a0800c0c000fa07911016074a06e41540b00f0001512901a4460f400244141001da4101e81c03050a00c03079401403140c00401505a80a00c104042940c030b504c0d04103042c1c0340003180700c042c2e9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 335587904 1250 335586654 335586659
    0x30b09060a26150c04150e030607030e0c1005090a0803041406090409050a03050319150b341218030308070512040b07030510060519030f02070b09010b0301020c07 71
    0x100030340e0400c02d240000780b051001202d400c540040c8624820b07050740f100c55403507500e400e1101580b180700304c00410500179600313114100381d1000070300240e12040394a40450480c03004c0c0480f6013080c1004c60000d41201c00c01890558698001d07000345074161003a14400200c694440c0c40ca92a40198081c04003195220903013031f1070618203000a030842420051000a10b41d401d5a0742d1490618014422408148003000300481008050007003041080303041e1080c4178604240004000c00c0c0c0144c01540d00c0314001140080030030f0442110001c2c0c1031036441031002860450160840d2440da103e90803540100c054032514400c6214454039450481c070303105404c50503400c590f0180e805c0c2c0310040c00801044401c0c414009940e0b11804a94043e6005a4903c82c00e400d00b13420060996030300610035816004624820010550b101d401c0300c6143c03607010b0340703409002c00d069011406032034046049c00b9503d00204c2d1000070f00c044102c2190190940800800c03502d1181c005050a03402940c50b414030640110008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 335589154 1250 335587904 335587949
    0x512040803030a091e0f110f0306130515070e0301060501051804090503300c13030b0c04090603030201150e011d0916080619060b2a0d030b09060a 64
    0x1020345481503c00c3d00301403019054417070010390390750740c2a94044407418444017408810242d00940e0841614403100700c2c4000c00c04281c1d1440050042c040810007400340505119040c000b000f002c84c0d800e11000b00c54107007944024100c0d50f101c203500713200303500e4104009115030203a02200c9031050400c44009110944c078040000810481e401558640020440c9990b052440b00c1100703451401700443e40f02d102503440750003807070360001820011740c01070030071981c180380343c0b50301c9090120303076104001010710744d10144524560300885c1e0001c4a02400e01c0804010150190400aa500420300003251039542d200390207142d000080c810081401c0c3d00c0300030916601a809011988002d142046400030b08401c0010151000e050b4410315054001034144042c0c0f031551686070720203207200c00050000a080c82d210305070a128003045002c00342e044070004900410f1440341045038000c0740e030588186074104000680034105001810f0310030b00c01000000d905140050400c0b081d80e42c9154841c0e84000040310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 335590404 1250 335589154 335589161
    0x607020304090c1707180b03190b0609030312041704061116050a050d0f0c0308070302060a02120a0c0e091f05040207052e060801090303050601020a02090403200f03070512040803030a 80
    0x2041c40c859103001602007047c0004000440c01894001c10701d5178000f1110120401316685009541d20512080220014a50300007045e541c03460f0320044148695266481e062500708980080d01150f040007080c00200542c1000b05142800d1512040d501c2c5c01051414000c10440d0b540105c5600041c4407406000d913050800103211000c0c03080c200d030300905850b502c0702021284540d00c211108180003030308108241e030502105401100c2008107500f480208018001000c000401e11540d10740d0361046140c1c01031248072040c06000011300150070300e08020365114480e1880815000e850288a20f00040504240c8220313201d1325000070162002d2404c00b1006a40062a07100c1004000e4074010401600b5101d0722400009120340310000071203409615000d410f5820080900e81035400c0403d50b240581c607010340705903009507d440c00404007851810142c00c0c94440c049040c0b00c0c2e01c10404a9480000000014520344d4004c004032011604001d9600443d88102e00ad16400c1713400900114040c00096003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 335591654 1250 335590404 335590427
    0x240d0308041b090207050a050f0604031d22090b06030a02060d24090614150a03050c1317070e0c1806041802280f0c0c080607020304090c1707 62
    0x5040000b0355141d4004099822558064403da00860100000c021b01009000000080140580014036250320040c1454203115859009071991801001d801d5441c000390060341242140f650540300000d000010091017024001c07502c124030f11011400034030b0300086107100540c0c0200154602000c100b0b007140684040301d03400b00c580064140300c4d074401d80c00d650440040d0981c9540025500c0c64104002c00320610403120900400380e01002c1c2e040d150001d0f04595228040703060114683d124000600444e104050021440001b0040c010030040210f00e0f09181154a02003250b48981d1a0104034034100c0040d203480322038072000c00811003011000002d1004013903000380300c10300745556119040c42c500d410282d0704209590004e10446a0500c410302c0d07000d030358144034403c48862041000035010641449040b0300740085040c40b0010403001d0f0101c50301414403c1c0580d1828140a8006590381c0c0150141503d05030400d6160b0726610700c81c1d005005554070000c001000c0d030311065403e4401c1900349 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 335592904 1250 335591654 335591693
    0x10e0405060709271803020f07051e04151802070201020f0606010807231315030b10140f1305120c01020a030c03021e03040501031104031a0618240d030804 68
    0x44d292408480b617501d40d618986400fa8019119506181c841c0500701441ca40007140b148a1040c941d08030a50300c1d50003c2c800510545000030a801090440e100c1e40c40182d010070003020708a90902181011034002d40103441c07003a000c50350702d0308004503d6525400b04460450004a80d400003500d02ca1040403041080700c48294003002c0c0d07201d1111314005940c0b01c0351845a00c1c04000204100b1001c0c030305481c92001c24946001c00c8901252000204010300107010780003040782081c8051154011107040300d030491440302d051556178506c0310f2440c1c00302000c1d1144a2258140c040c40c003082040228070104c080034168050050041540d50940e55805072460640442c03040300071a04c4520515096824111a000002d6407540c1c078007000182643d0307040802400f0900244401c100083d041000f00e43c0701722122002814907a1001d02042901540300c180d200c0c4000160140300315031142c06000e040c950b800000d04007640c0070000a000d6110035203140240000e103101c0c002800b065007100000035003400c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 335594154 1250 335592904 335592911
    0x60315060f0d150626090111040e100608040f06110c16210b060411250c05060a02030d0b04151e090506010503070e010c0605010e040506070927 63
    0x1008441c00c0d030094840040c106565030b800c0305850310103910280c01403582d454003212120100e14044000d5074030b508000352140c400c40124511000a4001511a5204110380350700c443d40e54884c500129820303641c13028084159500414004d1040344002e1099420107004818002d031543c038440141035508181083d4001408440d0b0206400d21040191501600100b0700d100c2c182000d60180762801030507820290704460308180001c040da0001075124804540006240c1c094144409052151000c2d01c022107400044102030380300c80c2440450744c14020301e80c02e4903240c3c4071030500500c0e10035042d465015a1041c4100a4600004e0708a40140d40c0054030106402200c60400c01e1119080d410200240400d42c500c40d034000200f45260340106180c2d6818030643c01c101b0006001480007400880410516a29444499000e080c542130b2141e80418200280e694034290300c0e0001030244c404030342d14080d69000c0380115108103802400c1d101d000301b9412030310000c4200104445417460080010986 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 335595404 1250 335594154 335594167
    0xa241502010b04060306090c050303031006030506130603030f030e03070f061e0e030406260103150908030a0209030c01030b0102070611011107050307030216081903030e0610051504030206031506 85
    0x60f10300460f00114801e01c8085240d641c1c41c580082d186506402160003540140100301d400b4403112600000c54001c4d0a001820b030300c074074001c9030000032000b1441c1116403d141c1c000003055800300c2c00700441100c90b0350400199102c3c0c1c0c00341d40c507845400c001812158941c0100e42c0884d0711039004140700400784840a400301c004d49120020380d044203d003119690070201d020410540c020203150321000b558102e404a141d50086190075002043c0005440707100cdca000c450644c94010741c440c40282e90044074070794803071401040450295020b04001030090051619003281c030750003030080c00507900058015102e094144030040b1400d29160214400645d2181c95038508d441c141740c0101040c0b0700a00c0a541e660406081c0a45040001c5400c50640d0701041c1c8100000080410600700242800c46030300c1850415050444c0607100c00160410a401150180728480700c0d403e290b035080728020740e848858400c1c090505181402075100c0030790019410000914010040000200060b4004083c1c0c1e04000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 335596654 1250 335595404 335595409
    0x311010e07060810090203010b03070c0f0503190e0d0b0a0c03020d050406060f0b0f04061b0b100306061a04030204020c01140a02030f0a1a042c01050a241502010b 71
    0x290325070280b004502e018080c0112030041c4071068000e000f2440c400d40c6954034040d504100e0748002044001004004003400d02000120740342114001c0d004011681c91b900741c0d5801580704100c80b00d4900c04501840d81001040c140800b80c6c1d980140c20031080300d190344d50002d5000203480c0c25a484030405500700070800802d240f91083c00c0c0102c0c000c0600140d0f95043c00141381158180e071300203085451045c405890741403014422a000d980861034986c100d59020100403114803102000100101924420002003450342000203007200d02030700301440050380e550304d006018003a4840c801c0c4a04000c10041c07015007030540040c0307138013200680001840f01c68120000001402070303505200b2540c0000901c2131404c1d5920005400c102c280b00100407005011340344108a0380040e0000e405180c80e811111a0100c0300c44410700003c251140030642030407170907a114000d000c100d440000081c60013107140302000403443ea07245400302400904440c0e40c01c2007101c0e1640b01c400c0c07410400315900c4000b0304041d80c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 335597904 1250 335596654 335596663
    0x150f180b0d0b0406050109050a060309081603031e330e2406090603060f180702030703180e010e0c04050d0c290f090a03140a1403090109030311010e 65
    0xa0308020000a10b00032400d042005840144c0d0009040064080c42440f250380d51400d4002150124140040d04080e68a0414600e0142c442d2803c0250301c405002d005154050300b01c00c401400c009007940c8010504180b45d0111102415001d015402c01f034079200c0400d05d910041a0b4900703401140d0205140e6450048059150849840240078400400d080035150b15140741d07691036000b00d4040f0b0a152a400204105000c005c1841f0301c1000c00145680c107070f490b075405110030180225200e0200349094080603542c1d9010140840000320301105910701002941c09460603107052103d0226142d10744140d8040a11016102801c103405c10000003800d5035892001940e00c62045180404c407615001d115200c10301d90403809980301d8500341032792420710104000c459400f800100d00544031080107021514030034854000408501c9003110000d604c0c00c0000344220302a21801d40b4401e40c12401c250760340c40b4000c00303d200f07010400c540c20600000e4010422051621009030000400401d01c1e50b81e02d241 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 335599154 1250 335597904 335597917
    0x25050c060106110f071a070809040c26040f06050402060c01090c03120201201b0a0809031c02030304020402071e200f06040e06010c0c0e10150f180b 65
    0xc1041d100e10328400400501c0300342d08042c035841c017804100346840c05c00001c0d0390024132102450716001894204200c8820b040e07814404020304108400e8075070301006440701c10000410070101c41141c043c001e110503c9103500d4801e651006000124002c155901405000040e108030b030b101e00c0c180300c5100366071030034030035001c14034020542e060485255040c8120310038034909030b01d4210390500f00a00035070001b440c201c852040401c0429544d402c800044004071103e004aa04414000c000c1d070718040c00020005040072400403003d80308080002001031002100b00784c0d1080140c1c005100080151038103a010b0300c01303507020300d01c1d014107140c3d46884030070b00b4034043d003007141e4151003103030060b6600c01824603014000c1c00503a5100441c25410340010814001da03c18001881c80c2800007039400d900c03c0191901c85640281d8050000d5214460a034805c0030454020b6a034001030800041c0c2d0040c54040007601b200c8544a18000c19002c0100b2114813855015626114200000000b500c22240700107100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 335600404 1250 335599154 335599157
    0x9020a0503060903121e07120e010c0503010f06020f07060c0609020904080d0501060e240d020c0d021501050d06050402150a120605100206070f02070b040303050c1525050c060106 78
    0x25a5960160748101320800a01b46010220a40d41403910b2000400b4009030001e49904040c0074103c3d0480d80f402c080d000002c00890a9424207000c02200d40e0070801950682e80b107203c04460f0785440d0f0000300d07691587e405c101c211982c044003040104c00c1c00780c00f03031003120740c0100f0022801c0000b9070042230901105807021101948001520800c008451240a02403c850314241c80301c05402c1000510070440a01004588072695803d410a01c66030801c45441d00000601951144034103000e4a40782d03002803c5001c0035004020103901c0c44d2000030703c0181078460041882034803024945136a0003c000050089801030600a07094035104081000780c00202c1c620740d91070403a00c2c204102042a00c540382d01650044076107500e0110007680102e005a40303c041407410a40c003101401040345000c44980c0083c000b0480000d01000b4503500500034084c5041ca1422128000305500d242c0e1199007027200d286150700100781d4509200000d00a892802c1403c510f40541054600c208207410708034207910000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 335601654 1250 335600404 335600407
    0x28090320070501081501090e100509071e0302160b1005030714060316170903070c060509130203070903020a0b0d0b010f0509100c05011d07080708030d09020a0503060903 74
    0xc119010301035600e24001510030103003107164a0b1a00103840304001400c03040511303030b00c8085550f15034820710265000384070065124003c0d0030030b0b4070418034195031400740a0003448080c1c001440180500482900030f09241d4141884100c804000c400a400c041c13845500c0340c1c40060314501190600a00721300950240c0d5440900302c1c5041d08140c40d00c0c1241d03201c900800d940c18482d0009513916010303070346e00c1041c1c0d0740e095031036225101048412201c2458031500b034031001028003070001c200002500281d07120341d00025020b074136543d080d581c2d4050384402075817100b00c1300d050b1103003801290040e42e04808641040111a0749a0703000440e101469000840011000300340101010305502400594240a0908401182d40001c00420901c5031b4110b45000314200c2030480700c1e491003452540c0b03190350000000c0009585484c03540390300241101d091000d80c0701d90030011441d210082190003c841e08200210710b03040c0b40d003580c4c201520108034180d0340a140c82130b00240e00c0e10300b8403405124510342005503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 335602904 1250 335601654 335601677
    0x18120503180312091b010210050606120103050102031f050d020d060b3102030f0c09031002120a110a0c1403040f0e070305070c02090c0c011b030b0a051008280903 71
    0x258a041c0010f0307100d111641d000170307181c1500c0e600411040703d00d10780c41401050390340e10300b0007107002c034804c41082054100c000350001040c07100c10340c00f4602603482d281c08038403205104910b5100c0350105029035540110004001c0005140c0b4881030340c02a403040801245c2d888000b80024514007100d8622a41036003128800c00594240c4048080c130a21407010450850400c6004104c10150040c50341103850000110300d00c16650400507642d4940220300d095685505007a040300c840781c0d064a0384810a404c3c001844d1006400c0c406582e4580003075034841610703490035102c07403011010501d980c400a010030000800c0b55001c044042c2c02403c80107580c1400da0070b040380d00900b194001400340c0100f1003002000d00c0166210524250080410452981c0301c0c2c0144072201e0040c0741c1102c0a00d80c07032003254006032a0310f416410584003003c0032101441c409a680c401d02034640502d1080e40c002581c0480040e81882800b28010300d441161010402016882050780d0100ca50602c01500030403400c4142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 335604154 1250 335602904 335602921
    0xb1f0908010221092a1f020a02011805092509050f0607020d050f1516020c01030902040b04150503010f090b0105010f1403010f090501050316030303180515040618120503180312 77
    0xc15021100e4034844181b01d4442c0200a4031000d0025000381008590960056180c1c0710b4080c803409000020b01b1801c0c0d9007400b9036944c40c0a90801480d01e9079031005c1d0020100f20f4000d003110011140041c04483c2524880000c010302603000304002c0340c3c82511a4000e402103041000014100b45a070780c000c0070900c20740e5000c2d0010503402000e40d07000041c0c00841c3ea1507280d0124410f164900c080c28003203100382c542d10004025020410601d078005286c641d0222805190f40c10440c1200d009034020400d10030200c02d0041964043d500140c10340c83c54500406c5154401c045188040045240c0741008404c803101d0079440390300030b0f8081880000c019806220031203e034450381d40108030440003001d001c650700800b4040d0072701074440941810341d02c4c500400e200272003070b1040d1580c0e82d00c142618948098400001c443c2035055078295131040c60501c01c00c60040d00300360407011203a00400d661000704000d14003120540c3c0004d12000c0d2010400391132455950003040074050025281c43c6040320352601034031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 335605404 1250 335604154 335604169
    0x310090609061812030c031410171b0603060301060302060c06061903030f121808030910060b0f03070e040603060c020f0d09090902040b1f0908010221092a 68
    0xc05110010110722940044c007403c48a56641345982000b00303000007086030030b80060090000403541d00014908103e05003104030f5010307041e1070511001d009402d080c11030701c50b81c414603102e10703410510103080c11030301d5807510802441d44550000c1c0040703103071034481c0d021030450b03080b503410544680d0022050007128034000300b44030403034066105000c80440c65528000c203c0b482c03034034140b001d0000d050070711308019496401084901500c581c034101c0214051078055144d6008035031855450003611301480100d000d40c040c00c400c80f000059039901305428210182c08076400a0700d0002800781010705003607191240e004000c01140901000103002c0040c00c006410300c46003541d000c0d040c1d00000b00c00030000d40c00080000a49404030000a5106182c1c40450700801e0103402541c0e1001103140c06110304030240382140032120301a9502c0049558822000d402d0340240702c6071035496449003802d200507082c50543c1d00d030f0040d480390031502d000d801c400b124241d00040e40510448031080c9100c20449080110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 335606654 1250 335605404 335605421
    0x60b0108070c110a0305061009060b090f0127140909060603060123040e030306011b020a03030e0d061103090d0203070b1303052203021e03070b09031009060906 70
    0x30104a40e1800190040c650307451554000e110707818001204000d0f4503200400c0024552040c03c40d2030a0821901503400707a8914420040c5d0141000703800b1500c81c60300b4058441448020b02118407403020607005641d0310b200c0c10b440c580502c95a8800190407040fa040c1c4000134195004030f0340d001615141070005a01f0700820031041c80d40f0080620140d52000114141102c0b4131440c008450030310f8000d02040026440711059005040c20740b03c040b8500c02100460244c10262600e003204005520100403150380420080d50010081e80300b000801d005140500909400a100f0303900803045950354011a99103d00c40780302c2d000080200004241d041018107905441800154242121070341c9004a007a030041444406502c00c0d400300c5c0c201030040094400d0381c203c04c00c0c2c107403107609051508081070140340f00a034414000c401001d1280b050180c00d82c2d82c1c0c0803000d4090500b00c1e0078020104070590140c9040c0da090310035040340715010030140c13240700c0c6a0351080c44081140342d6a402d0000130341f150071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 335607904 1250 335606654 335606657
    0xd03020a0f08250507051c030c0207121506031a0a05100807031101050903061806070f0e12101e110405090f040303061a070308070206090a0611071e060b01 68
    0x4100f80065035030307a40c1c1d40c04445029181254101c0824500484050051038402041c07441541c010800e8016280c10321050240b10b980c00f040074207007450080341c1e2402548a0a01c0c81c410200c504004950038041c0700c0c10040f000382010031420703940d9a56402800380d0352087c1d413100b04960244120380c40c00d4041d05800200c10704c1c075a4062400d0403a195119407017440001c01d440020040da401c2c1d6400f0300f06860321104000c05503106031074040340002da20003262106613190f010b04c80016100038000c000c4162a10708135a90382034420020b2050000c0107080c400c0211442c80362a40b0020440c001d409219041c10002d40c80d5100742ca0f5480302401910301c1482d450a001c0000e100038042522903803d4558020b80d4209904540e841c0e90900350020709180d04412000c0e003000300c018020009450040401d035100360350b0012155120b050032030302c54000740c1d04200345400c45845840807944541000c280890407500b11450500302d40d4810303803da031411480410440b280a1070209021403071190440302c650070f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 335609154 1250 335607904 335607917
    0x70302030115050d090b16020c06131502070305011d06090109110d0c0b030703021c0c090605090301020f0c01062c01030b040f021302030a0b030106030b0f180d03020a0f 74
    0x10402100382e45030080000c0030401402150000c031005040d00320007242900a40900c0d4a82045174a0b10441c2c924501410302511481d944070703100d03045c400116036030180041034103840c181c14200020030000d00711a80404600c50340c1c0000c40400e10038418280a002801035842c1e90812140c0058103090700109520031a0349403001a602080c2008605c1003005401c48a1a1003c0128130300004c0c01030954100d1010301102004000c030300c0760140d0040a1040c9410b900000080001d64031105a580a24140300018440041000340500070300c00b814010000500140c14240b9280300005103800c6910889966074403100c003008040c80d00700125040c00f840c0141483c1151300d01135514100b4406200051a03050503c0001d014852030080d9084120384c0244000c0000407081d5138034000c2d40094400441481c900400840a4541445840100c9601c511000c05542d9002290f80071141c1c01440c041d9903024840c1500583d90301803080c07800d540304a850040e00c0705240385005004807024207590052041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 335610404 1250 335609154 335609159
    0x90807051206070810030c060206060f06031015030b030a2607110906180709090b0a060206270601081f060506160303020c0102160506070f08072a0305030f0703020301 73
    0x4001c02c05950104180c01c001140b1340710a4140220031071a68005003240384065800306445602168160054000703c9611040a440c0c204011303032031105079241105104140d2080101400c000c3c0c003095080054200050118800d0002c00e04000e10391008956468600700000d5880a168040c184410341c6d40203803038206444ca58038500f20003242500207115920700c1c8001130b4aa03440305000b404509422203000c40504283d1000740c01c1041c1c03806003201807410302018901908187c0f00030000c5402e540d005101c1c540302d0351140d00c05003c9902080c100e0200c1e4821030614800d003000380030700030001030300100004010440c10070080070880c0c032600c03842410702108116030f6980c04142c0b100602c1c5905101d10301e00da00d00d4103400078403a8a0002c4101e5001044140c1140c12030003849401d14014815a0780302c0d968044c0449441c003805100102080051001c61079061192602d070a05012a48808103011040c080040140c0d01750300c012030000350000100800030002107040c03074202c4c8081c1419403c550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 335611510 1106 335610404 335610439
    0x1b280b040603200c0d1d060a0206010e0603010207110f0d0605011511010c09030f060b0405181c09060c060b06070c052d0d02040e01050709080705 64
    0x12102144207580d006030404c48040c1d1000740302910200282010540782d04000c90490080b5541c904664403040e15210024480612903400410096251030031842c16048001e040d42e0099006224190000340009034100030b108089074114000140000414800200d0130006054039040c2400010f03150094040c040303070200c49071365204440040030103041c00d943c545202200010040f52041020600c00c00315210858070514000c00c00d8401c6034000703020307038809580d4401e03104502c0c220141091030030490040b0804855661034859030003200c0251034001d0303a00c02e0409108003045c000f020415107030f01072010410004e0000351142c01e42d00346500c00903160301800b0302440640800c04d454041e401141c001c0003042c1000c0800704a603007401e101001d00e5a28040341c21544036410494200002e0294510607521a99040541c510342583c1d0351921200b988594010300b0360320703220074006 = true := by decide +kernel

theorem cover : BRFrame.Cov 335431654 335611510 := by
  have h0 := BRFrame.cov_init 335431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 335431654 ≤ n) (h2 : n < 335611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
