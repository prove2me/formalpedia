-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3395
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:32:28.305789+00:00
-- url     : https://prove2.me/submissions/11117537-f35a-4960-8de5-08d0754daa34

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 610431654 ≤ n < 610611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 610432904 1250 610431654 610431667
    0x3070308070b04170a11070506071e0602310b160f0206190314010b0a02210904020f09041109010212070c1d07020c100e01050304021201020c1506090c03040b0a02 71
    0x5022504022a0000050706c04004425260b50800c229005814221344140c1009002d688d1001c00c03a6140c003019025030341000f9a0420081140c05840540c4c0d80e52000c001044170115a22900c58401d981150940b16104d01c001416142c90045aa0610a982440c100f100e1141c5840580c442c1241c012600103008001d040c0d0740b9001c00741c1103100307005076a6006c18602006410a03a9240c41a000044504801c101452883d80c00090090b85105201c1950660301015102c41003180145501e654000d80000749003a04031080b40000c1052480403182040620b1100c0e0707103884640601c1a0540c0036a00203100c0001e1110b042c80582070141c8903003044418a6100d003220f010300d0341007028a518000c110018400d006070103022150240006481c5031040002c08807000b00600b4492400905101000021500b9501c40d9403007050b0665080c0000c1d1350382c42c10881c106966202402001d003d07169024046160313858804006d03401408130310b0f400c0b429134a84ea196495040400360012400940c02c001c0d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 610434154 1250 610432904 610432943
    0x5061e0402061b03031608010b0301060206070f02010f02040306020319060b0306041a03031303020117091906232409040204050903071a0a0509011b05090604030803010e011403070308070b04 83
    0x114480c410394200d8401b0f02000000181040b101a0083e05021909100600100b98000f81c060b0780110680703031903152000750300004d030300600003101143c1280380001404004e11003181c00a5000f1442902c5040300b11078980000c4040302d60500401ea8589c5040000c942a03140c01e8000000b4800302d40319840d1600d08040000c0d1540d4007100c014801c404464000304159a0020740c0041e0303e851240c0860094030341075038000d03100c0c0341d6044407141c0080b8114042041c0100340e170183c407100d240712800701e0705541540d04500e0508400c440f403100394000c103400c20211001103c0b0030002894007606a40c4540c95a50810002c2d01c4000c260125500c000e00091001c940c10b41f0341407031205140340b680090703418501c09041c140d51005101e0240e036810481c0010304c4481c09090b400c0384400301c0c038100f46c0ba48001e00c00111148540c0d40064440711000c000440c541840c21102c40c12501d05412592680150340309054a030201c91002038035000091202d034000c00c00c140200c5500c584108400c00c0c141c00c1c9000f8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 610435404 1250 610434154 610434157
    0x60a090c0302160501090309121214070f1104050c0c15061215040303051501170613060b090a081515040906020a0e0a06030506060d0f020409090f05061e0402061b03 72
    0xb003503e99a446c4d112850605400540d0342000e84880e0105050202054a482c04400c03c83e00c4424204180901d1007805c0c4101c0308261425242c0c004070820231700e90941812441c0861007220184aa407905011401408540c1d08031008088400003030101031204c04400420f0301e1005003540c2c0c0141102c480b200d4540024000c40c08402c8a01c00801c00c24281070600404443e001000d030141c480c4d08144181c3c85a8014011112150703401103c0300f201e580301c401103000e540c1110f0901100c01c0c00c01d40080768131010311028015030401601c0c103000c040d680703404c401d65403040c2c0041c1141031741d003400c0410842c5017564291030741e0303035800b0304081200354090356030b01c0c1260701c10300041c40000c20700004c1d45081c2c0723401e0100c28018401382c40d00f0320481c24640c000490900c100c004012049940b407450001c0500700d501601d00425020f41c00308581e008a041c510061002428116218000c81000452480c0c1c04044461212030b0144030b5000f6540300ea00780015a031145032900654244045403d443c42e40400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 610436654 1250 610435404 610435447
    0x1e0c08280203030108120313021c1221090804061206180606030b03280c1d06090f1b1605070609050a081b06070c0806041b0806060a090c0302 62
    0x1801107030f0300d6140c02411400d04403071150308001400c08200744016400d13000505034006404803006a0001c401e0141c0120111600000a0180888003030525003e5005440c01d407440c42d940c0304400c0768010071070544040b9040407000401c00f00e07050005210f010301c64107032411100c0800d14006402d545a60705044d018841000100c10140c588034140400e96150103281c0040074150300807c01c000c0c108a40b65210a034030101488071031204000320301805000c21003540140307018a0010300746484540e4200413803038122a0b0500403002580410001e210a1300480e10a0441c4407440400c038035052a502c2c51540075a0000100d03503c0c800541002c600140f0201000746440d45030101c842c2d2616040c0070704020700d90322401c803075041000180c814010307164850325201001c96029943e185145400c6462203800d8014041d144600000c0004100c41400005483c402c2801002c00341c9a8071401c40740e841c3c108898440c0c20500c940001c0008514581100031007060505015007020480c51140420744940f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 610437904 1250 610436654 610436657
    0x6010305010510060e010801140a0e04050105010504150e130f0605090d0905060901020709020d090503180a050a080d111213030210020a200102100f0207031e0c0828 72
    0x14001d010b844682c52030351030010801805d0011200c0c402c000041c01a0005200e6410a150f030301c00d004051381c1e50b03000e03044050070150041d004181480d041050007013200f4000c5034000c0d07242182a41c0c038001c4000540c4111804106150340965038032440520f404810780048031010fa2880300b000000300140a2544203c2280000b0301503c00c083e2802000c08825500c49400b84c5c00801c00744200744d90203d50001523420140c0091398880300e01007050010411904082c0a5000100c0c0700051101c4450300040300f0b0204880c0d404400c2d031903104011081c9280e01c030300c1c10360740c0c041e01361581c40138041d0000440c0d180d2f20340180d5142c451010940341c0e040d4420b2048d5804290241c00620440c9040602e031a00c007605880100a126103c2d81c07145c05417485014035a850b6854200032408d41c0c4c0c0700b004040c1e0407121014040c803c210b2003a00000c081d402480b0103d000c5500da90380702d0a0840198030030200e20006907200307902201c10344c032910700d2648000400005a40c1c80341c003000d0448800a40151600504d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 610439154 1250 610437904 610437911
    0x311010212011e0e1b070203100606120e15070305070207170705010206091204030f080408070b0909160f031802190e130c03020f0414040b011d09030a0309020604080601030501 77
    0x4040303c0c0c902030000d4002030f071000000d00034400d03e80c42c0c0d0421988201c000400c0d00d07645a010b4000a0314103c02c0780c0c8114085810702101082c801e0f444080d0410f980304ca44020701c80300d4141071340180c0700e007801090355000402403800100700f50304c00c2c3c03c0750b5044405401503807241a100c4203040c25403242c18002003802ea1080d101000156410001d259004800b640a4455034240c070491302c0c80ca1150f440042c0c095550312400d8424407500800310b50040042d03000310783c004c690743c20744c1160641003580300c0c500c074507041c4002460008034a454802d800c0e0750759648a280c03085291054008041598080d003002d48508140801603c0b560028801079090343c60041d0070901d41400071009000040c030309284d84030041100383c00200c09844400650340d0403250965000c1414000c01c004040c0b01d0711000f5452060760030300050281e45031886058910f036a42c0702500811306100040d0034a015200146644d004000303407403038141b080d806125040d200900c02031500703079221411441c2c01d40a8000f9900c5075903 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 610440404 1250 610439154 610439189
    0x1107021c0c08330c07031403010e0414010e1f0605030f0c0307050d080406030f11070c061d0112150308071401180f061d011113120f031101021201 64
    0x5601c0f601038100c4031074880c0c010000c0300c2400c1c0c10812407005032030104460301c04143c03d000c2500403003003200443d0074403561070b480750f0703680d1084104044280c030140c90b030012004a00001d8132040c006d1006964220009040541102d20510140b400703110381e281c401c1e0760700c0c5400300c1c139640c062042c118910420401030900c1900c0c2400c02d42000072540c0514170403080d020805000401c142c0649040352414240000d0142955050354050400a080c4a5030481e000401d0307001c010365024503109460059803010b00781100a503108074181c003000740c65404a02205070326001080f864000e0008890034036079044405560fa61440b6581c0c001d40d10407103120240e50041960348000b44070f1042c8815a1001c2070314000c80d1500ca10310f14808002001c3c02503521030a8413551000810b50b8150581a400c3c000c01c030302c06400d0074036140f58004180e1654196110600041c450190450079a0240d801404200007040c0b1541c0944104c1003d081110441d5000d01045801d1144980c50900a00141d03030810311168 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 610441654 1250 610440404 610440433
    0x1c0b011d060a090c02010912120f0507020c0411040f0e01090513030c3011060108010c050f0a120f090201020c0d080d09050c10021e011107021c0c08 65
    0x98800d00441054140004110255594050709012282c8401c03001034044001314040f805041880d50140c01020f04d520300d200d44641c007140ea0074800804502c03c00c11610103401c00d0b01a20b100b60303005001640311f01001035183c506944042000c103071194a2030b107801c0e5140706e201d045003059404034665001e0b17040100304200e40707406400c0e8070500c101401d41002038207980c06450702c404828042c010800f00c40300703a10858010540e4800400741c400c004406060310000c0188050760849400c2e000b4019030380002040101402031041c0da016548070b050501d103101d02c2c183f070301c0d80000c404030f01040044180d01c0401c0040d4400c0c191888051507020400042c6030002a03e04100c40580500070912000e129000c40c0128060b40e011451810020560003240d00304a8a00402d2115044c0d005961070200d00382c06400290b980c6e640c10b019128902220000c02c5658200d50559070344001c0c5980c1007007242c0051a00c260031a456880380c4a100315590021303210f00c10455550380201080d64480c242c1c840010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 610442904 1250 610441654 610441679
    0x60c1c030504030f08010303050f0c01020d06030501020c070509100302060f12010308070215031003080d0239070b03151f230702030a0230010c0906050c03181c0b01 72
    0x80391401e003417101e5403447d40d00502511a03811703907103c052400b150322065074400390100c903104032440c03409204868580c10294002d601c00400706030365104100c000101c81c140110300500c11440c84403c40e00061841c1c003440b500d80d010002e09450038208101034915030780c0c288071260280d8060905540c0f00d550b64030500c103c1c0c550440201094640500401c084c0c00503410b65601600d50000440303845d0204207081030068003e1200e481122641400c0d07184c0b8580444c400b60851702005021005401d402e10050b54850556015401c00c83c401000000d01712902545000302ca25005411580310003c2c05080c0110718827440b18450000324101e0302c903070b0714000d01c2c02c4500c0c180d40c01c0c02800c0c1c0b422140d540040d030b440e0001140240140c1c0b03980d1907810f5502c8400382c101d003040d28150340d52056200d80c0f0015402450000700314808514010004140144602c0c141c40c00e4110300001140f0301144400c40a003a40700c9901003c0d44002036142e80304130380d2080d13a445450700d072141c600044a541019807802d0342 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 610444154 1250 610442904 610442927
    0x1052208060f0a1d03090d0201022a090601030b010507110a0f24020303011202150f0f0c0607051206040b15040602010f2003040807140303100509070c05060105060c1c03050403 77
    0x40d041c2040513940242c4000c0b0445020040854008400c0750503440140c2c01e20422418501c040c0c82d82c0195642403106a5603404100c42044611190319030701c0c1e00040d412168415513481c00914280000c600160150080500001c0300030310909945a0b56448005c038490305421034500d450401e59400003942d5003074441340e90041c0c41d0010394150340c10400d0780080840c201c90040d1255400d600c1020401c00040f00704c0c1c10001c600300050b13540d544181080da056038001d4000501511840b0002070a40340300310151215844920b40707040320f40d12030000b00400b8020002441303900400215448600d40360140c0100024101c0e40c0010854490703001909040b80c40762040c004907500381103000040c01c3c032138400b1203034086da120200f142c54000e2410040c5069240442d42c46043c0710000500600264044c46103081700c400300e862000d0359940c1c50b000c40f10141c843c0c1004103207070f01c0308005000f00e14081c4040d00100c5410f07005c54070b00031300c2d803040717050f03601d0324030000502095441051106155004580010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 610445404 1250 610444154 610444181
    0x106110102070c18050610023a090602070e0103030909020304051009060f06050604050a171905031c140c1e04090b0a120302100b0105090306070306050103060f0501052208060f0a 78
    0x1107d81121201179240e0b503601d14203132103040a21110101140c1c0d81c5002c2003100e030000e140b50840402007107001d080b00c0141d0107502c0251140c92400102e19006e4154503040e203502d82c0d502d110f203910300310814010703410152084610740100c007440b80c851104c1d4454220054000c100105140c0034a05c80b034000c070384003604107500608081000740721944a05c0090400c644c0249904002390361301c400c0807810314980042c0300c846a130003112860306000d0004098160044100d4040241c1d08000020200319800446c2c840b00082c0420000b40303400000c04060459900c225002ca109407a8201c1060307106d034811707005912036956076862104103080820001010f007807640e424003080d041d281c501079500c04410000032112510b80310f551079223074030a40c1030321a00b04d0040c003262054149801d02030040c01050007850b000a2038440001004090f05104404403070044c0c6a46d441c22060703010240d4482c0c086a800401c011080200083d41c400c10025188192101084e0440354203100c91000d00780c0303544412158 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 610446654 1250 610445404 610445419
    0x90b01060201140f070e03070909121b020415050a0906150c05100b0102030d020409020c010b0a05130b0409051204080c01090e01052101050a0b0312030f0106110102070c180506 77
    0x110105101151541003600c6450461300c65440040403964070031a2408990540240d000024104020344c100d004014030804011103890b803094002c0306d104040382e05980b40100149000400360a1076840140aa9120354921440c10348480110341c104046600120015035500820081c4d040104a81c001d002d400b49400100c4101e13a4542c0d66651680e01c2039504c102c0c2c2d80e0903071481d060780200308441e00300c031800009541341d40d82c44143c100290030030583d2101e1942440c05241c9030f46010620072003a141d00074400c000d005184607000c001000800300450b0400da03a80b4038800072990801c0140000403100481c59691410008a01d040140701c1d5000c6041c045141c0702440103c4210b10b0407030544405580f801554a11800c0d01031158500c2c001c158a01d5107000103206034060681c000348130070700c1c064044810800c02c0e0341c0c1440441c8170856901071603902d03610052050500c940c00c0010392032620341c0094248852a16030b03001070b03a00341c0d00180d045912440100031603a940e0103032a42c440400c03244003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 610447904 1250 610446654 610446671
    0xd0908030a05120c1e03010e2a0d060801020415121503060902010e040c270e0a090807080a0314010b0c060f09010e06160809060c071209030b0703090b01060201 70
    0x2d801ca000b030b0840d61040c41a0080052960101c4d0310545584541c44010395008001400403441554000e001d4158000441c40000300e01d07041c08000b802010b00341510b0241c00800c801c00b02109600400d80e80e0b0101925104000340d160000d0001c0c20181c10404030210080e620070001030710790f07540c0d10b000421490034942c290280e60945c1d1448412641c020202041d42c281c1440102d540700e51201109a0283c40c01c20f04651856110740348241203028990215800005100035002000151080b418040a00c0d00080c24a07071107600200059032260b1851420706086a841280c150820814200000c1d51006415000401c0e225121300401030101241d24100c90140e08549030940184880e110404000215012000940c402c0842d02500c00603240d140c1021103c99040507445c8425100203842c0502164400101159013406a01c40700030b2541750100c241c1e180741c025102103c400c01440010f89002022030b01071f1440714401c18545d0b50000e0001c174103252541c14000b040e003200045a00d4124071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 610449154 1250 610447904 610447907
    0x507150f0e0f0f1804050c1c140a0506040308060901140306150f03011401050f010f090e07120204080c010f02011b2312070f0c0b190b030f0d0908030a 66
    0x452000e6203059031420801c222180100b4035030701103284051380003031050804544180c0e0003071060b401507200e20b040d80d100d0b0502504108111311180459460002ca402c0c640001841c2001400b5005100d042034912201d030684038070f0704210b400c44d015030204154800704841071412641c42405000c0c050f0f5042d0404910a000c00d035100030044c1038501425610941c125540d5420560f41070103040100248000511141c0d0000d80e14420300c2854000c010002c01e091040d0301418155510380c0599071a80c2c070107490181256030158015000f0003e04c00800c0e44003080e4400c2c0d00040000d06551401401c240e1070700320004041c2c40d0320128030700071a490702c1440d2046030081c03c41850740090350f01d4030980d0581e91048100c8252400d4100c100e0456000643d020754000221a8030300c92040364071120460411010b0507544483d01400042c00c1c1e4141d500020b00006408080d0762034000240e10005109200c900400c2c80d2880c100340600c1590702c00f4a40010855000641d44041c0c217110303000d582171409840c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 610450404 1250 610449154 610449167
    0x806010e0c0a0e01030b061303022707050a030b040504030305010e070914060a0318050703030923010305040501180b06130b0f15160312060602010207050c0603071b0507150f 76
    0x5802e810800340000c019101e83c0329400200070450010700d055943c804814000a82d002948000c0740108440ca852071510300756078503694070002c803074030400c1d07510303a070700130381215558400c0040782c080c99a2000b0b1000142c99030f1254600c40c0303109840005907541495007050031801d006000004001c80200305000c416013000c90100041011342e01c0c035483d40044141580500703080d1130113120b0120801555003e210300040c4460403030b800b98840c41d03246621031500c10105003540c00d0040506903400450711141d4070a0340000d0b0321902400c00010340314a298880c420880000390195452020f07038003803008901e04100101440c2000050800c008096030003c1070086c000c81007440d215002c007a0403920350300d80120407540c444d03105030f002c540b4a0090b4500a00342d000e150b442e95000798503014000c10858014801c490b02c940e000002441c114201e0701c10401c00d50300042c400710400c240045000030148a0040788460f452145001c0e040103424100031020250390400014100680b1204409134240c1000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 610451654 1250 610450404 610450417
    0x8030c070b06033c0609010f0c14040608040f0203030a0c06230408030406090c15180b0315060c0d081e0606070b040303021b030714060c120402030c0402130806010e0c 73
    0x211130b144510011108040500c00d01207982c0ca00810007005030240d010b5000890501068401b00b00c01c060000040307540f60130703460b0b202a14000c2000123120103070107510880da00c144140c8002015885a5011900b1a0000301d58400811000e450160411540303004c3d03160300e00d04d24050100340c04094484139803051000743c0b0141c40b41400002007000d02019801044480b90050710202c8480d545282d81160181c00b074600100241481c106594404e0303105c80423b0840780840030031410f607101c08540b03014802c101400c1680c09042004000421b540a00204c2c0a80c0f401ea151a4418900880d6401407048a05240a000c801c4c0c2400c100720355442c01c0030781d6070480d000929400781d65258a07055009205101084680081000e000051301c00c0005c010f0070340500c5207090980001541c006a41e0f44c4409656142d030000007171040c03103107543c0107102956102e40000c00311012411000c020608a81c0103513074008010b120348006220840041044500510744007003a0f000520b840001c5212900950 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 610452904 1250 610451654 610451713
    0x17101b050702030f0d0f0e04020403030806040b031011121b040b160506010b0405030d0e01021c1211040e15090c0a2105180a020d030f020a08030c070b0603 68
    0x81640d00c2551020010b0702d2801c00382d9070448210101c03511015203840b10708540c4000090000c1f00320003060400b4000d031004c480d41500c40c499951918020040500091210346e5007510815400c010035031058014110400c1d4401c06041e940d041401c52606145402018502c5a64420302400d4800d0303c0c1c08101c40884000f03007040d03a00c078208411842131020f0107000181c02440b40c00300100c6c0103e040002001111411401c8841d400b01e141c0b400d03540c2a034241d04507405030304802d124021407045201301c81c01919a51415600d00b07991101c03a001203501c040e15031400302c4404a0b0503c4401880910250000072040c1c4124080408400050b0964402018201000c5000c03403048106e6002e60740c3d0002401401040402c1415a0f001401c0185411196001c0d549401003000c290703a000031601010f01038002d045e1a420740e18030b840c195085017a04414800718462039068402048101010b5809142240b407002d540f4a2a428100171174040640750a100782c0015404400c48009645c003491001c024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 610454154 1250 610452904 610452907
    0x303071a060a0305011b0305070f08010b0d09080412020f060c1216150f0b040c02120a02030c0f070303020601060905090a0515030a031101050c032e030c17101b05 71
    0x20311000c140b0041c0307554030040007903003041c0c0700f0300b10121480c00c01d030150080b95400300304a87d02d490040700d24004100349031000c1501c40005100c010304400040083c10411400420800d015070303203c00d0b240e84503038070800715a18140c100c4e030704602d0724105800101c90100d0b0030a0074105002c0300d441c0c40300389462012420102c001140c2078600103800c1007550741c9402110a61412007840040030180c0301c02e00590700114613102c004003080ca803900c074408038442564014201d07a1070b182c10345952035009604000961009000c204042c030820002014540d100350050322000d49180340192401c203068201e0014002d40b40360500654540049039030b800b501e50b2502041c41e450b11140003095090428109401d8040c2448020a250300056860b03580c005e8040204002d50765880640117601050752078502180b420b84400d295068020040b10040289801c00c41c1c4150791713035036551100700c0701d507003c800304440c030101005c0503080502c54030480590249060050302440c4103e140403520440710581031050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 610455404 1250 610454154 610454161
    0x60203030121080a050909010b0a020a0204020f07050607230301140415080111181c0f0303110d0504060507020d0e012708030c0d0e2412040606140303071a 68
    0xc1040910324858004208136540c0030712441c024501d03400642c070940103103440c1e000080c4511580d4110b034120340c510381c00381044111f80e0703003008041d5000302101901110240515030115000b40490381c00307000a616002c0c443c03c40c4d101c000031121070410031810401018001000840002c40e005062140c0440d00041e020318448100300c0030043c80e420180044d840c18107941e0104a01c20014515002d5003200c0344090b404c00b0080041c080c502d0005110b50304034180555002402d0403d43c120b00c035101e41008921442c0d2241c806c2e41c9a0000c0c000040050345070340600060103028840c0d070340c10070f1340fa101a00a020503250040c09607950014540d041000490200540f6007502510b0300110500c0010900e500e5030780d03c0505c0d900d80258419400714018401c05440c49801400c80f82c001540103040c1c0ca33000c0e14481020385845407442c50300d00d03111070708102c0d100c024a80d01420a1145110781c10006069060403011030481a0f40400c45010358003c00500000c44c89060552011099a003500b04081c0d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 610456654 1250 610455404 610455449
    0x307170105093c071202070f02190e040602091305100b030c13080f07290d09120f0e030c0607061512030201020705150f040b060f060408150106090602030301 69
    0xc510f180e000480382015404460701003184029405803079140d0301e100600c0d83d03402c01642244100007008101304280c260a10044c04d00b040c01041e40e019542c6140d841c59030b181c944c55142901160708461881d0300191003501860400c4641d0100c20748810300f0041840e003100030f10382514031405080390b110700c04000501c1d00400c4004484060300003041002201d5a0b50348000d82d5054120100d0165010b0420085107007004500b8200300c10701002481c82410785041d80c1c0c00303000d9204500780b1040544840558000c10000096241031b01099074804555008083c0010300c420000c0a03800c5c802d8200403076803013041d56454242d0b044143c0018000604855000c007403144a220b551268800c0c01000c204002859010360107006864010415510184103081c1c249070400c908803030030908184079a01080c003192a03902d400b80e028101501070301070b400c6141d0004070180c2056005c2201d55010210340c1c1030303c01400501500619190030b00c0303803601d0b05051001c0c2d100e0205000c2c00070814901e903007850044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 610457904 1250 610456654 610456711
    0xc140d02040522030806040c021204090c03111b010c03020a021b040e070e04030e040c050711010c0611090f030a03020c10090504110909070c052e020a05030717010509 73
    0x184441042c40d5103c201413401400745030048800710301c107915000790001e0090011501440400e83c0c1070b000742c601820648030200400000c42c5502c1007503502d94604500940e120f0003000c0035201c05030309012500c200e0318040c1c00c0d504030100c0101050300502402c1740994000400c1d4500d0001907018405404014000c076006154104a61900748500b240010308008500b03001401039000395903400401e40c4c048103000a0320054a00500011001c000300f00125441910040203402c05142000415005441b18026501841070360f0000c104009480155454015000c582140040e0080c1080c040d0f00e071406916903400c0240c6a010f1081c100444030f026110720749100145c0307001082008481000c1403601025003010790303020b010b808140c1c0424500b60141d60348001c41540b2100402212100b1400ca40384004d41d003400c41403905e915412004c6618440c0083c001d50f1049035202a240e24000000901420580129a00501401d0018030160f118169a90342c000001c000c0140411680b00821001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 610459154 1250 610457904 610457941
    0xb0f1309050a140d11030304030f11060a15050a050d121b03020303010302011103070b01180b0a03050a02031e0a02010e21071701151a190504030c140d020405 69
    0x4034002d201d0b42c4802c1015004581102036101c004890640d109910141d4041c019407510385100d030700c18000107002922410f4290800f41851512203101282210884d2401c2c0f0180c40c00c2070005e85805403800c3c00d1418032950780013482e01710703071003051070b450503021800c1d26001d80d8000d031025034011442100580142442004160a07410f011711040c114200251250020301080b8000b0342980204101840000b0545030115001050109a0f900e02821890034209441c4d181c0790310b540f0f40c0007680d602e68448086100960166016024100051041500700a200d400f038441c0d025281c4826410440e0019800d2142a4282455000001c00c1000540c02c5101d0320761172204034010801401120345d01082c100c0482e80004503182184d02c0b60100f16003a41c8681607400c4000807105010001e48410f0000008a424280292480c0075402402c0315420000604243c0100c4c0300040d04204000000d6002c0004000400a8250f0300c515100010b00402d0746210180c0305d0303601c490200c0c0360f4410311800e1484 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 610460404 1250 610459154 610459163
    0x12007050102300906130608011e2111030f2104060f030509070f0803070b06090c07110d020a08031306020a02010c02010503060a08010237080610021f06180b0f1309 72
    0xb0450b81d5510300030312407082405001100b0364480021107220004100ca002a502409031412044980100302c04201901c1c0a043e01c106011a0082c0433648061089061a44108024142c1c2a68080d0795a280380d26003803021202d10410001008203d90219040031420824907002c9890f49620820b149801321542048480040e242000514108004010700700e46120301c01c0d2001d241d465070104101d048007241d1801d0020010403910b030000740c03507c03480c24050a004040659644080c3c001c903410800c1c40e0498502a84001000083c15544d00f00100041c0b0b080d100410190100780d0000b065822400c40003418040702202140320342e61090031707120103803228000843d19403120111411107400420140107100510f1309504c501201c1c800a040b507982026103d80c2c001d51035000c240003d1051310303450a411806220394086c41000c1c0745509030b6201c6c481000100b892420320079880e4001c809241d40111181c40e02d03500c401991520754003002202d10840c0d1105420310082d0601d405407490030710051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 610461654 1250 610460404 610460437
    0x150f12060902160b33060d0207030f08010f0f090c050c010c05090f060c070b09011404060c0201080a05071706061608070b061509040902012007050102300906 69
    0x142030300200711043c1c0030180180c11031441074942d00b607410b10304014031320122003102000c030140720428070703441804a0391170000c1e022a281c0f40314030500d1000c0380c02001c800c90001c1c2107110420b034855440440140981010300c4070288051501c010814101401d104201c0410380700d6940c466224010000d50301241070410003844401c0c4031140c001d00076440107090501c145510142408582021000d8030f4402c00320000510b034490400f2164506500115001b9041051000c10b2841402e02140604000c04190302c0d0200441414400504850340042c0407900031072800d010003a1460f40f140b003103004c0c0c170780a40d01e10742c075500c0f640b01140e410f10481c804040f205055403a10390400143c10003d009040c020100e04403151260301c1048444481098094051441806603112602c0d10b0343c0212a498414140580c20145d58101801c6000d01a507501c520358104a0b802c0149580602c581c0201d2519180c030304101d055480c00c0304100c25002d281301d0780f01490104141001d07846200458101801c500583d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 610462904 1250 610461654 610461667
    0x30f060e09062710050405030403020d080306130507050306010c050f030703050c010e011e05070c06061202040e061b030a020d020f0304030e0d150e0109200a150f12060902 75
    0x16520041980c0050744840c4a101d440a004a040480400254907034007400d1340f102d090840034017038100a08151a64002084000011395440006a076140e00c02c1d00a9612807500c04200071503501c98906000109042c24200458141d02004503507222009003401e518030007460500e1031420f001c0406e10055440000b40d250305050300040a085e00c0e025000007031100b034140c494128280e030880c070b503140d2500410913200108100035030801c9034000c4540c50803504d108269181d0304182c0e83c0d00c2c0d01c043d81d448444052031055040c1340c0507131400103054400806060808525040100f059100c485d0070151010001c80e1400d0301c0e41d011110306207004d400554841100500c1400180c0c02176a049001c00c00d400c00811031803c00748411510720743c002c2000220b0702151607c000103482c8076000f10038103540e030780c40e4040080d000e50800500000e0706200482540726102c148400809a80c004034411a0035a48188034540d0000c400c10200080d41b5041c20311800c05510040908500e0304040082800030620 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 610464154 1250 610462904 610462921
    0x40509120d020702030f071d090123060f0901050f0105090102100204171e060a02032802180910121a1f090c020607140403050a0b040c0501090803070201030f060e 71
    0x1800343c4600803003c0c3c40c0c0c5070900c5403050381c0c2d070010751140300a10100005052051030341612115401032901c00007145c110191092035034001c0d403441ca215401080003003481400d0400d900c580038035940550341c100c0e455041c8000604083c0f041d24440f41004000a42502140d20a1110001c52121103406545030368680003c2d44e10b800c014501040301d449521200b246150401000c0c0510071912406050a5103d90f000300000e503100400700c8800000c800c203224113242458070b81c2d01464801c0c44006849070008080160f00e040d011000f00e01c110382d594203024140d45024005812514800c01207200a00c9915107044001d00d00d0808404250210003004030507035612a600c4080304501c0c4400000c55211f1044004030f5485059010043e484440040d000ca03005130320940c26921000c0100b130034240d80c1e986492a18010729803c071aa80f82d944140300c00c0122029101020744400d0910b0803280e0f04240741140d4038050413001038101038940201c01d00400f070a500c540c3c00342200302514030151411516 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 610465404 1250 610464154 610464157
    0x1c0507170706050f10090b0a031202071a0a0806090a11032509030b13151802130b15090a0b0301080606100e060a21020301060c03020601060e01050702040509120d02 72
    0x205030b44890603d40051203501c0c03051032451044060910b9003100750b0030903088100400c00041401d4004000000210201e0f00b0700510303041e4900190300801d42582000e038480341280705403426100c41c0743c040c0300480b08141c100300715035441401555444000d075035280404000c1c00241c0890109104004180000c0482c42e008210341140045030f0101002030f4908104c03a014420320001c0e100f80c84a4002c41c0030301d0f10b40d07442c03017038058041d040705a4202d6400108608560700e09c40c8c8072005441d0180b000c400c40c1052500b0703420502618500b04400119500400d02580c001105000d60320800103030303024247c0e103001c500000b5103c0f8030202030701c96031202c80d071964495040d0b444512814001d040900c3c00c1d4442c0c5c1744980000400f60070141403500e10f04081c1c40080351081200e1050000380100d40303034501c00d480514001c0c41e4503541e80304980641c1c00c0183c100711040c0c01060030009516910b001698005048401e0300780e0584000072581c1e61509880c0c14440400700d0940415400034482601d004ac940 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 610466654 1250 610465404 610465417
    0x1c03030f0908070c1d010e130f08032a0f0a14040b131701090c0510090302100203131d0c090103020d090b09010605010201050906060d031704031706121c050717 70
    0x50034010400d545d580800c1c2d000c18248510011046001c00184025200b540800c64203407140e85001110801980d686105070421140d1400400019404210b0300b10803180404070b0140c03040d0024900b101801d80d0f0700c01c911541558000303010200d10350b0081604010100d600504524160740d803038030701c90b4180100001d098407900d190aa00348001129069040c400c19080c654090190015030303191030144050000c00003c007000340100e82400001503150000b24820806032035020316591103000444100303880458006102d8140c08207a807108007101c454001c0e410500e10514240c50707018110048010f0711640c807042c0314450624050004101030303801d1050142c03446c034000703100c080d8a07803004901b01c5800b101c101004d58088404281181405002085281c1c045d00e000c8180d50076501403280d02003001d54044000520190b81c07d84000c1492400642040f070131a5600a441c94810420b0740e0303005150728043c5440070640441131740c54021011034001580c09244521100c000d03001c254500c0d001302 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 610467904 1250 610466654 610466669
    0xc0e0a0f060b0a0f0e01050d090b060108070f0f08061f09050310020f04091116032106030f2d1104051b0d0f0621060b1c03030f0908070c 60
    0x1078004540405a241610410200c9640d0180c1151118800300c6440c0390103d10701b41400010804402004110700a210b00305000d00011012414001e00042529200a1810b000c000020f0603108101d5032059a1140c0395140745406047d13925105c000682c1c100c51880c6d941c294456a0b40003010310b6400c040c502003100c0c800c8081d124031066150a0f0810f034803d4012404800c3c0080006100c0c400c0654452804241c01c14a403500b0283c0003814035610702c8420b20141d010851103003108034039841c0c1041251000840d007105100c45451a0b80340048081d0b151070003130031a078a0112060410f44690b000c800600c50b03040405424414900b040810502c0d10201c07a8003950810307002400c400c3c0b0015204084010381044245001d014900801c0207194600040034020f448480005140f51000240981c002e80040c4854440d0041e203041c400300e072a8984907074054070b91000c1441c800c1400554801c2e01e140c043c00c02042c0120101c900100419103801e0007024a080801e2903c18030450380704120603216030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 610469154 1250 610467904 610467911
    0x60e0709090606210e010603081b0a120302160209010f080106212006070819030911040c170406060e0106020f28020915010e01050f03060d0c0e0a0f 65
    0x21840284141c54081c010f40020800c45a0701010b1101d00d01c50342c82201030020f078005100880484641d003554801e03802500d41d0031020502d4104804400701c08a0b044685c035005004072100791b903e1245259140007410107040c1c0c0030583e401d00032010709120544070750062054550f580c407200314100d81c3c41c20740100c1000350720300310700070904550b140443e0491403103044020031080c407150750b1160082d19005200c609003442e40a131030020b071240000741640600c5141050b4071110b45820701415005046030781c004143c14145960041500f0b284c4c800130b43c0106030f030702059104c072001c4260344078a1039241414524200b0010007051141e00c0d4000750a0300c05030225400142d0303848800b26555a0740c10180c040c40d801410211400010b890440319944618042403111000c031170f0000b54070340c03a0482c3c000c0c0d030300c00414003004030544c1d004940c01032403502402c203241444003880c001c40c0700d400700030400d81c02600d00c0c400c00002c2c40b1402660900a1020009018151130030303160101c0600a0a54a058180d08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 610470404 1250 610469154 610469159
    0x30c19120f061211060d020a0206011809030804020118030b131e0b0105010302030a0e0a0606050a060f20120307030207170c0319050c030417190b1b0904060e0709 71
    0x1940145001c44009080e0440781c400300c0d8541c3c03251100d21500b913940c0b00f4010404a81c001000e4006001c10701340c03a07005020030350302d00007190f60660403402c1c482410a1900940c0400030740c002c118550055020328002196909022600f1141021500b022b8805807803241000b8401c1501c20041d02058070a032903690320304044e0314031400440e50275040246601755134401405603501c250302440e031100224401082c1c0c020740d412400d042c010200021f440c001c0d2150028446414081c0e040401040a49031040f15600350420062a0898072580740b5901c65001c00c900c0c0030300100b0032984500017180c6c00c820707582e4100750f0070144c001c0d44071042c04c41d2056030416075502e01c0070107001034a10080192000d0b45c5414000c110549404565000200900106100e40e0010b89400c01c050710103045042c04081880c0c070801c1c0728500d040088481095000526015000018542c441854210412121030306011880148005d003500401182d6030700700b45001400107000f641e011401740114682d8803034640a58 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 610471654 1250 610470404 610470431
    0x11090a140a05090907060c060b2214010807031103010219081005090121050a080a03060f08012a02070317040303170f130221030a0f0906020d05030c1912 67
    0x1036046500e1041604809410030090b4087e48048190900c18038001800c4405500002c408a039580350100c66200d500246502d90f001c644076540c0b1403d06030b007000445607d00740140d69120301d5404020101800380c2d0b803407985030f00c0c2501a00c5007107203240c4210010308503101008140c03d40880741b00c03d0500c7d412100143c1030418160a6058828814071180c02c03e030882081d85804084000032a41c0e445921011000f00706c507507000e481c0100c1c441d54081141484d0440004d41d560302078111504ad42d1410341c1901900a110888541814940d0f040c80a4160304500503420460550b201038400d108445c00d07030300580c2d070700402002564426118442c1c41150450541c184100807514440a210000081352446019200c0600c3c601d10091984014801243c124011041c01c080031640b15400860708102403a000440a000070f101860510011842c000000390f441c40706040d170209000d40007010400a034030744811aa1281d01211000806020024000b00b00101d880c41802001d071420b1040700803034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 610472904 1250 610471654 610471669
    0xc0304260a050304050a050a03050c01060f0e040f0515040501060303030e0a0201080109110702121507080c0301091e180302010f020c0c0402090d0209010623041811090a140a05 77
    0x11058840d100d0a0041d10203003070701c0e16400500306440e10312800741034500088080121300a4140b00e6604d0945918030b100040f403d560894100c0034141c1003030070062140103100158141d1064000c40c01d40c2440744036040140c1402a1718190f040c00c180140200014040150032102c00c0b40d129540402402c0c0921800585944450707400a0002d100400100302d02c000e950006007840d4003a8104528104140d130014100707403035100c2080301c9500100b5052107500316a201242d8490044e081c001c00c00e03d41501d1800135480140181d40d6003071b5490a8081410b040103443c407941c0e0a03403440400c901c1c94001d0000c024444652011030040d0308001400d842c1c00010f001741d0345003076403030742c0200f211405507401c0201035003052030100e070090300e0f01411001607a01c012400d8020f00140c0c4825140501c2c00d00c004844120503007000c03600c03503000c010030411105400c0b80c0740c004590f40781d0001501070080d1031400452103040381c2d09078440f110490124030031551121100c4841c004440d4940d10303554500070302c82503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 610474154 1250 610472904 610472963
    0x6011202040b09120c040606081f0503031b0a081204150605060703030209030a1a0f0109051003110a030c171006060804150f06060302120a0605030606100306030501050c0304 76
    0x10400502c003d28190070320507030098199042c8802c0d01d070100c1204001c9811503a542d03000c8800a2030000901c032740084030384283c0ca542c0700c490645000441c1810042039a81c8602004102d1409011004030801c034014040e0340d08840d40401150303910f080c0a40108081c00058078250703401e0950000c40b50281070341d03205000407140080c2c101e41c2015200c0d1410340003900b03c900080d4140c001c10500d0030008074840826039060300d03a46821100340c02d00e05010000f802050308803140103450103040c40300400d544d50039041120350010161070990703449401b280c82d0a4203580f0003010406020004a901201000100c6000b01e0f620100c0c1e03c00000d950040090321a60b00c9418007140e041c40204012481300b402d55200840300c9038002c11003494020000c1704071442e42d84002c0003e036020880000d560940341d05941c1114040c0c1061203036a0900c0002602c0e4140600030f05c0c0701f40300c0c005d00513880b00c3c0250480c074021501702008001528045800c090315034070450f8100d803403810416648042680d41c0060644 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 610475404 1250 610474154 610474169
    0x70302012301150215010801060609090903050906030a1e02041a030c0a0f0203040b0c0c0907080405120a1407050a17030c121012030905040501080a030c0b27060601120204 75
    0x21646006000d408061283c1411002c5014603036510602c80c0180c00c98500130308200d40001081860003070000c100300141e0304000080342c10143c4003c00f0035444010b451914804840050b07403502c9c3d00100764000c100366403c07021440d84e0004000c50f0b0f03d0450740540100c0d40c55041d001c220000003841c00020303110441d007148445130244048840c0921450714219510030b0307401201c1c5000d0311100d0708245908205070526581c2d01044806410341021001c00d9080302140c144018541000c6c1d4441b80c5414004040c580d01100c081010240b0381d128007889400140e50080503960f8101e142411921100c4c02c800c1500d115011145690341900c0c1c00c000c880c03007000309000c2581804656402d090024401402000e111a082d035004584000308a100030400c9201e51240845186800c00384425a03074143e0003040941c005561040210390480380f007a00b500c4d444001d2584603607520f015044160030401c03400c40c0280b00940b03040b0320007d0000d2020300503142601d80d00341c002e910703101c42000d034420b6029561 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 610476654 1250 610475404 610475471
    0xa0903051902130606050d0f110c0d0905040209100c030e1e04060e24010e04020c06100803130b07020a09050108150c040f061803080a030915020301031211010f0f0207030201 76
    0x50710903d5643c0140040c8c0c10420b00440c00c403803480600d032500e03000190108880d4024030800d003501c030b4000c0309150041100342d800703604101034000012401144400d8401c24040382d400c007103007014800d8034005400710740140a609140c02801081241e40030080c0018080c5142010205402000d10b60700c0f840740c066840d07140386030b5241079007044220360b40c1c48203a030610a091030f400c222661580040c1c0b08004542004084134640349000f08080c004650145016410030803044403883c601841d910181c0e00c2c1e644131156100c20500c08620f014150b03920005981b0300e0040081041c80c03010981300500d45040c2403d0015131101c40c0315034054400c078410321216450410017000900d00900c40e100d04001030005654113155241c803150001e503c18101140007980d03842c1c10000708070f049100d4100c3c41404480440c11076046598040c0301282558441d000e200c00b5001880b212502508000c0480348200740c140402c0e000582800042c1d0444c807401c502550038001c2001f06a84c944424900c2c00f512a040034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 610477904 1250 610476654 610476667
    0x9060e0a0b0105120f01050f0a0b10022802041103090d140a0e010210050103030e030f1506041805030408011e052403210a080702061b0a090305190213060605 69
    0x2205980313001624001c1400303205a40c3d1030356030082c0708944c400c00704070210b0706030340c0742076641c0c801114903891015104161840d100c03182c0c507500082c1e1f050081050701940d110600302114290820801c1400203503c60f0500080303c0d80d048840300514041d01d02e6800b16441c49600000039510a03448801100300c0c2c14040c400c0081c0c41c2e10444001c40c24040600648500c00d10840c84907060350404d07002500440d03038aa0861560741000c0104940280b030a0b40074007104007284d43c140c031f441c1602600e030509c22903d854200100700340c4c107c4000e40080d80142180ea40d00c0e03449110502030002d10420540c6030f03001c103516401e4203d6501580380b00d038801c00ea0824440e1000e03011090307444881040709402d4440c52000780040030a03801ca403c0f5818507002e6103900c55413050b000601c007036402003546085401c204281b01e1400482255681131114941c1e0301501c5072016070b8111200c0100c1e501c060700078401d9450285c030080640c405101e00c90300a41ea0819000448295071054503690322a110001d0410400e2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 610479154 1250 610477904 610477909
    0x3041b0e0124090b0705070e0a0e071403150f0108010f0e06060118050a0b1e04030512091f050310060f121107050706120509010506010c02040f0e1009060e0a0b0105 72
    0x2e0b54a05550703401e18600254544e000c1c41010780050300100c505511040c01401a981c0c1240340302e50040c80c1c1c0c2d5091101080e4403a0141d1076070100e114003441c5420350025011070365014060500240351640d034a200b1498104c641d03140c1100d081c42010201e510300241951140103074010710204940800c01803559488250046440e80d685d1030044032610240c54010071241c0d00c10154400030008408116101c40070380d0613007041401c186203180100759040204000192002c00c2e034a12002c81d504280b0b84a0355044003007203c5c01c10303541300010101602c0311200b03583e5801001843c000c40380000c1150620f52101025a10b0f5520140c51501050305d00004911f0034500340c209900c4c0c14190811a030808441e40e650030314181c030941144012886428032203081c0b02803481605c2e4481d074000001c0c410742c200361001030304104420030041d0060b901d40f00784420651903900503044034a408001c80da145554042100d00810f1211000c8a20600300103240408c00c10000340c008900e604007103641c1d12a4070340003c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 610480404 1250 610479154 610479209
    0xf120d0216060c0b19090618020109170c060f0c03030f0106230415030b0307080a0b16051801020f06010b0a09060512060d0f050316120f0e090702011103041b0e01 71
    0x3d020007050348406d0b01c500001c040b8002d86071000800051514010716510016140400f190031900a61140f4850902005000a0005070207002945c0d503941e56000c1501300903036403144946540c1540300000900ca542c10345910342e0380c101d407601e5581001000c2c490f000b41900703030300c0000b5a0050550520091044168619031703001c0c81c90007414000303581e620303180100781000445c1c3e21010300340c1c011906510034001450081b5610040403a41e44023085a81c4001401078054511221180e2500c1d80081c40780342d00030440911f034104921b0488200350703034460402013640d1003d904440010016000000d18a000f0000e072440c66072074503c0510b83d6551031040c0300d11541092010395100000c110940c0100360244020300104151109003030100b910350070003030b10221011070302e0400c101c0170303145031865154071468022000038101c910751181d0311107441c202c1c050311008410000100c400020310007000884002200458620f405110509030794440c00e40045070240324411030002107200d0403c200603800c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 610481654 1250 610480404 610480441
    0xe0304060e2205060d0f05030903060105150a082205071401030e0a0b0a02190207051915080c1c02031006080103080f03071202070822060c020f120d0216060c0b 70
    0x3170030705000143c180c03949100680050020780c0c1d00e0b0000600c010042c102400040d001d0181515400002504280310710384505c10100783c0420082c1a201007110782d0f0611a610310300c203070401880d502c44003190400c00d0300c640207449211041c6c40c0e108150100c950080c001d00640000c82805030104021980300c141c442074008215142e0241d080251002c60355203254180e0041080d50b004103903171805c013024092600c001c944003c000d240111001c01017101c01c505606403030100c511b03241c0c0c060340300c18203c0809401004a40312002140b011043c0603604680d029500c695504203881010a48e58441a034040600307000280250200700305241600c40c4800c0116084046c0b4900581c000e8410201181240c02035402100e1002d000201401498580e0704008800354940c0d2102100625040d0007501c00e002b00c10000307005808410100303001e503403001080680c2e4900101034074580c0039042c0d070003500e030001c40203c0224003140c0391011920902c11000001125800164400651a031880805a8a503110f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 610482904 1250 610481654 610481659
    0x30504050c06030f0415052509180f0b0a0815040c080d0801080d03111c110d0b031203010b1b011b11070b1801050a02030d0e0304060e220506 62
    0x1c0226034082c0d191800198400d400c8105041901e003002d1801c0c1e034051900100841c405030500c014031802200070b1400710500e80c2c480d1240b18245482d2001914400aa40e110030110b0400c1c00300d00442c65000d400c03102102c811000100450144501013004615590141d44125070022110843c0f042c004803074a5042800783c90003525075170b95014601c0c60841c440c07940d000041d07211001005164010408091804d00c00d0030b0038030090900b88840382460044002c8401001411020702840601d680c0c070030000003c481102d00d580304a2030a80e070307018100c11030205000780305440000c4485050041924181c1d107240040f1858980c0e07107582e00c407004031034000e091101c0d543e40d03801c046040c20312030006070300b0011506c2d010345190206110a0910130aa030005880d0310007040120100c04900740ca0701ca01c031509081540d02c030324030401d04900d1400380c24003100c620b92410f000a03220f50710001c0a4802c89503980d40307040005503020280940482c01041c5040044040003500002c0d07000b87e0459607100c50003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 610484154 1250 610482904 610482913
    0x1602010908160e252f0a02030c01090b030c0d0b0d0f0c0609030b06130209060403050304030506010b0406080a0509010f0f090605060a03050d030f02090a0b03090606041b03050405 78
    0x492050904040e41d0311804a48061480c104100c103650400000e03521030702c114031140805840865200030619000135150410654100d0b40c00245000c0b0068648458000240c0c2e5078504142c440966407402e0034005d910030f00c46e0741181f011b40c1d03203d03c800d5001d44040c04401c900b5521250001480d0390000f6540004007920391060354016280c0791007402032103018081c1400768100504104000004582181c001c0064032181480400c5a003164141c006005a07000300c03a000380c20082900a00584810581c0800001340000038010000098070640703000740103440d0607036030794071116100e44610310413440480c100000240e500443d540c007666008025400100e088015242160111120455160030080e56540b4600c01d02c000c5101c1c0d80e52145054030002e81081c00d5403600b6680d82e8290042804058589290300b84464403070f01590b001e807030040c003a071f44031a403264010102034004132000c02d400c1c0300e079800140035071034980124062820111110301c05884019021005000010070039503c0380708 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 610485404 1250 610484154 610484159
    0x905090a0f0506100e0c0906090f04060f0611010510060e031f0914060108060408070c050d0f0b090a172a01020304030912020108063601090c030e0316020109 69
    0x9181c81081030079209101818143c034020102102d4151180c0210154000c180308004440c0d141d24116039144604884080c0c4404a0380c000a0303201c0ca060410540090130700c000003800c41c043c84d10880950b191500d480166030b000c00b2016007201e40807144c41d084092100c601b01b1010380500e00e03404250364041c0c00c0e40c01045a5071329000d00070414024140496030f4400c0d800c0240a03e0341480020354440780c01509403949002c507041e5442030007902c094280751000a00400b0450034501e8403005100140043c0d400c04a10700708080b030038172140d8042d6110171005000500b018404261440e28a601c411b10141c0ca003403052840117642c0000b000440c0d0302542410220321001810180c0051040c11000941c1d40c0ca4289401000107480f81d11401107000100040030040c0c1c0c10600d203d602007020f91703487c000d00321041c034041c003807607000c883d028106201740b074113a034115000c4003c1038144c1e10100b13414802c074098100c080b0b084801c0c081d0003040c0f0382c000340300b4a07007086041c5540d039910600525140d5031503034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 610486654 1250 610485404 610485413
    0x4030e0103021b0d02070504090b0f2505070209070c0f060f06050d060e010b060a1e030204030b0f09120a05030c1e04060e0f0105031909240608060c070302070905090a 73
    0x82d01140f2040842e130000e14800c00480e81044918090f1409880030700010100d0390f5002c07100200a0110703c485000000010f070804d041d800c11466003004509040c0032135022001c064216030004600344c0c0180d21900000e241c090190900402c203560010007040d059109441e404010412006241c000b2521558000b03000d5541c01c41c00b10803940124400144101c20458aa007102d048041c0c1034028039060000b003080f15001980119100d00c01d5000117182441032500f100248240d401c01010000070030184892041d00d10b00851140c81013800315140840c600c05020840c0c02540031081c0000e03410400584500c4551000e4005401840d409145903800c0005071980c0d42c02c650000c00000d8214a61001c45252400d110152000c003070809501d0740c20901c8554000700e441691a0b03124035200e100c683d08004000c51001c0c525440d410079500709a04040c60a405005148105000740c8600c1c004103a40f840c500003201c0708194903400038080c0c60b14002c01c3d0400703007200401d9a085070181022940100703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 610487904 1250 610486654 610486687
    0x90603030d0c0e0306070f080c1c0504350a0c050a0b04051006090b0109030b040f02091014040b0123130b09090901140a18170901111504030e010302 65
    0x50304940311003030305481c0e43e402e040c5414001000e103020001d00f1900300003040d8226252030707003050342308000c079a45c4c0e1661100e01d40180c081d4285e186c0664603082c200800e00c200c0b401c800c3c1400c075810440703902c0d81d10310148451182e9407504d504401c058040200030b4800d40111100e9900707038441c0e03060b1400e8803100d403583c210b02501281d0580d22034016600240e801b1130f0910440014005030041045000310740d100003445510301d4000146080c2c410380100d000d120302e050607124a50f80c0100040c07a5490280c104041404003445140101c120b86c0d210300c81c10b80f8003802020514401a0354010f03144900c0c42c2c048041466072003810411440c1040b11072501e094890b4030717002405502d802c45603140441700070b125004000404640244e454144003100114140c2c0070340341c0200000d40301142e1020800c0106c88903c0812000600701110000b030811001c00c450080e01d40200240c843c18240c480c40c48190381c03560307842c003940035954a482c030014000074041c2c11202d80c0e4040c11314006044c0100c1c2101e40455 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 610489154 1250 610487904 610487921
    0x60b070b0609090d080115120527071224020a020105040215070f110307051f080705120609040609020910030210020307050715030e070902040f090e0309090603030d 72
    0x31031460a08001c5903060940c440c6412840700d00041005440403c401448076106000e80b0060030011258405c07510f20400118001c0030300200c04009a0510070303410b0406410700e0410034071041c41144d03051048440494183d00f100c4065620407444511950f0f47c4290940e49810a02a0300c8403030f03075800b012402403025141c1d0305440d0f0000140c0c1d081600411001e413a0300f50815207078070004c104a000140345c0c4401232041030ba202001c0108000c549000a050012a41106401074040414450f04460402101d100c0c800e658032041c1a6444a2004544c544a28442498144a060701203501d508103103252960281c000c2c60009102c3e13085a0010b0214203082e5111600314642d00c4040c000e40c030f800100c0c034000084c0350008510301b4034542e86140c0c5030003951040d0301060780b421030341d012858040e81241c15014100782c00e84030b06649038a03a0800079001703800342105046100e0740102d4605018890f100c1c591000034015428082c50f44100011550018429a01f50209010002ca03030381c02400307075111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 610490404 1250 610489154 610489163
    0x1011060f0f0f07050702040c020f19061104081b0f3609100509030c0703120908031201090b150a0c1502030f061003060f06050903011d07090906060b07 66
    0xe8a05001612001100001d00300146000e8000c05012186400a0440d60816810768020070062070501c000d80c28081030400c5ca1707085016814491900b6452110321041e501d200d04010440a40d0308240c074201800b840c02851803036400080400000c2c590b803003001d14980c50050200fa00702814001082c41c0381c0702034006410602d202400c0840047d410204d2400c01108000c01c4d048903d0507509003541c0c0c0c10b03c00d00c45074046682e0008584688018400c03035001d24aa001240c0341e00381e0300e140060300b41d14070750f195900040340ca410100340c09402208a81e1040c0750442c690481e6421b0001407001441c03400c403070540c0024a0610040d008052102070304818000351207004481c5890f06110325801c6582c003072411045e03c10001c010749480046043c07600080c00313951103040d422145a094000b404907800a08420750a0040003d00301e038402c0080940c9101500207200d0600813402403a14001c03040780c4c2520541100302d042c00081030951024460f2801500d021640c80d50342c0444419030703848400c0030b56 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 610491654 1250 610490404 610490431
    0x91c030c0806040b1c020a03060908191403010911090301060303030b151905031815060109090e070513061a04050a121205280801031718101106 63
    0x20340c06500064540c0e031001007a079061001c0c000c404002514008030745005d40e2100c520300210419500c44016504c00340d54070080420864610f810b00c004550000c1c440c0d40381c034450101070a801d0b10302c2480c0321520034203110612421642400f1030341c0080d007030520100c0d50000c0700740315542d240c0e80c0902071080198041e880001d40c06032750106000641840c045000203030700d42000300c80329101190f5035600a002a44c588152079440c1c1495040e800500d007820440240715071000c42007821401c40070b00d4024502620340c0c441d065030703a52130007080d100b030300803924426040101e00300b1a9043c100508100940480400299103440c0c04a6010f240c440841c94200d0040100d014030160814207010342c0a4000350709003080748045a41d50310043d81307072440c5180030000080355000764145021035580750030701d0b6901d2180c2e01580001c80101111000d12040c0ca448100500c2d2440031b100340e0046a903031500c040702080410001d0000d019450100385208410450180381002071140d09009150094156a01c044c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 610492904 1250 610491654 610491671
    0x402181305041401020a050f070206130807050a0509040b041419050102040801200a030f06030221010c1d1215010e0a0b031b19030b01090207020102071203080708091c03 74
    0x280c000c4a007100840f00b43e84100000c030029a007000684615a00b5819151f60f01c1d119807002c20460f00032203030a401005da4928000c14107030f0001c00e03054240c074030941d0b0740500ba6036900c0400c80130300000d1360f014100040040126003c20101000b103000e5a1542040b6003032888148180780c80c8200901c015101ca03503000c6014040c1203001c4c040c401c3d9103d1402500c060310000c40c3c1440c1c2041c8201c41c45103040c541e80e1581600011526000344000303680041510440d0001c041215401d406080a08815540782440001c9030030b000703078a19150345a030031b41c070071503034600305002d200011484071203c9041d0300c505507640d400c0412241c0101d000c0c00349404040c2e03103800e0902002003503e04200c0074078030035001607444c954464000c58840c800346c003084804c01e40054440040608020703550300040c2145049000101d1a0f4413903030001c101e031901c02c4e801c0301c0c0d0280d6245070202500c011440700800049a50005c1200e040c070900d2010b821072011420703036119034010700f11109545001c940d810042030b141c4440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 610494154 1250 610492904 610492913
    0x20f0d0c08190e060c210f251a0f0708100501230408071a0315010f1709280206090607020109090507090302130b01080115030b0a030606081e0a02040218130504 70
    0x517170402c0040c0c003043d007041008000c910170ba000c1c9100254648c07805625904500c51a0140360b0411a0040021104141d458514690243d41120b06440018054001c108250312648000e40320303005108405007694104001101c101c5840c1c0d050380c2455490700d60a00304071b9944002000241002c40040c405c80e4a0a1000c8005030300c1c5080400f1500c505004104084009005100c480710302417070415801c202403441a41d494041a0703e11016031251402c1001d18030b8000303003001e944201070002040c2c4228180c80310f9040010510b009421070b000303102801d10303810040007610a40384141040700300c4540f1140340303400b160412038660340080c41200c01041542084211900440040c081c00d010f411032410004c0d011900c1880717124034a0200040c40d048541c46948200710040e0000d050400701e07036890908801824081c0564030702402021800d0340a401c0078041e060102c0e540b11301138031800e0001d0f020840290040010000d0b00303100a500340585940c2c2080c0380b502541804400503650030300c1d062 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 610495404 1250 610494154 610494193
    0x3050903130f0510110a02090c070609110108060a03020a120317090a0219030515071101020c07080f06070c08090310060602010c0207061107120c090c020f0d0c08190e060c 75
    0x110405003d0001164642000302291102440d1f0701900c0c080e016403108100c0c130059204c1c0310800b0300714501e0841108100b007258031984c0c6081000360380b04125900e43c102000100c201030320000350b010b83c8881007008122072640340003851034081e042c064045c0c1420b00076604000c2c01210031640030740151002c0c0086140c01030381c880005d1940e0a0082c0d20605681e200f42c0d4400c0d9204900e1000b4100f24002034955105208075462078103407100940d202c0704030303a0b2441e0352403c090040c400c10b4000c440703001400607000640c40740318401c0d554804004003880c2d110701e1869481410500d8160084000c0c0040d0100c0d5070040344010200342c0d0000500340a00c982c001c2c2480d4450700001c0c01c101a203000b0341c040c032300c00060303407001e84000c00100000200b41c0d1501c903030201070700d900c0b08990600f400c40000c4165008180d03a18212105002d40d044d0758401031702140c80c0580c80310010807034503013840b0180e40300c0444041007820402e5410f0411520040d0701c00505c0c0c07a0058176201503180c4c00490704800690b800320 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 610496654 1250 610495404 610495429
    0x706090303030f020f0a051803010f0c08160f120e01090b0703050f0114010e06091203030910020405010912020112110d140c030711070e0403020d080f1603050903130f05 74
    0x5811420000400c007070f101540302d14000a41000000b040d0600b509408110703523413400e20001c0c001c12400c00c8000c03541015040d90302c600c0d80402d03d0400040c40c0c06040e4840c01040300140d569102016901c843d050302c003d40411442d110751079540a40d5004c5a800348100030700613008103283d122138509448010207450b401090462140305480041000c008080050701d070402c002d007448200015840042007480c020100000d51100d64007008a040030808030085000300c1000060b1060220200400b1041e807245c0c1c400d1500152854404200e0401c01c044025a000d02c14034056081040c000034050554900c800002171590000405000c04041403066684c01800143c01c080b0780d10b880444444540030040580c000d02c800c82c900c40d040b584040c03103000e0103003602400c0b6041b02d040170f0a00039035a200312196800424424030101e9080380d01036214501c02d15071150314124040c400c84040f000307000042c003456254070050201c90f001e00d1210400b0304c09001d210a00e442c0c51480c06040005104405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 610497904 1250 610496654 610496681
    0x801060f0f06050a02060f130b010b0c1c0804020607060f050f15040e0a02060c0312131a0606160c0801020f09271b0403150b01081012030305060f03070609030303 71
    0x404c410001d032900841c2099000307010000c07084c0e640d511001056a0121980002004d1103542000030402c1000c210241040d00340403001c44041705510102104100301c228070300ca001c240300d1400100180b600c600104051842400086040d80802c6803000030390394195249421034204504010641c12504011011840111401d020001ca1810700300c2c1c640c2a400c1020b8080d4000107414003c04108004840406040c079990381498600f4250100004004440c2152011a4000c1a1404407500c8070716a006c0c110040096141400580303100c00030041240080700c15050022f40010144022320242039500201420315948004a0b4100968101c0d401e6001066003e02d6900401605602e0803840d841f5500802c6000c100d410003482246030b006030352004080f010200c9442185900c81e4000201d03030394081e00c600100340c54400c0700100210460142082071802d0051041c0800d1207500303d00e030000000b804407403070410a000803a040240365003151020483d0032030100105981480f5440c0c946104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 610499154 1250 610497904 610497907
    0xf0e010207060906052a100b0a0e2d100e01290703020a020604060302070b130b2d07080f0703060605041401021e371b0801060f0f0605 59
    0x40140c0641600c103140903130410060003150345c08a601e1444150316a040f00c0821091058082d00c2815036074200301d580000483d400c002010a542c10081c80c0310056403810700389540a80c0d05c0c0c132400380d80d0300088800f00008001d200003001200300104019401004d102e070b00d01e9252401d201d65899111410b9109144844d500d60101c043d043d05124001005103800317440c40e6840e041410100c1c0742401c07841019604c0301d000103002a05541550050030b00324801c0b880c985803981c401e012036010040315440a0400341d6540b002505100208a06003140d003140001d6000648000700c1c0003052900c11654580031888250511035008420341f0410b901884629041c0141c5041100041407405036229a808801c04503201c80c17100d81c0280030f0503203c0030100b4091511400141c12669443c1d50103c0840340010000c4040b41d210a00301d410140341100700a03c16521409954138109100102c2c908200c40403109030021642c0d081c2801201c005040c1c005607940024146480c610842d00194444018005c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 610500404 1250 610499154 610499159
    0x601090b0418232b0507050601060305040606210204050901090b012d06050f0304060b041b03050606070b0105150912071409010501081f0510170a090503070b0411100f0e010207 77
    0x1860005a8001d2020141941340c0c0d18100c0c0c825501c43c041c500c401001401404008603500394075a208611407801004240541c6503507900e04501003681d056440311880e1031010546c0035080c00e4112135044039100c0000180c41400d40c0307800d000c580e000e8204940202c54102e07981101d075001c0f46002c5081c100c021260248500d4128090a240b0420800405141000c4001010303c034403540443d4203988068002e01a040e0710006038980700500ba6151400300e450103001c240305003072540603541c0d801c0c2d000001c0b0486908003410400035180305140d2260490f410005804c10382c40c0c0780e04400030000d40400400340e160410341046858410460001d0045850500400960fa40061015044902e8107411802030150b480f4154002c411a0051078005600d41100008503901a51109030341c49500c09800e00b07502d41e4031040081d01d8282601a103103074002e10035003003c2180150010b400074418040d01c1c0812011101040340185450a4500414020300c020060150060340d0049a0301c400d00c0500856030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 610501654 1250 610500404 610500433
    0x2215030f06090501120f26030604060b0901020d0309050a1e0c060e090a020310170717010606020a0210020312100312020d020d0e01112d0f0601090b041823 68
    0xc0c2084000741c0301386c550100700380c103001042d04c041141c0c510095500030001000c0074210265402507808034041c92809600003201002001520a101c405a0123441c5400481c00c0c01c07005416131803c1510f5a000f02c0704004001110220000c1e28408490305c020080040d03410b100d210341e40c060b440700082c803981032815100c80c3d40d80507440b075008420400050301d03501c4401c1940c07080ca80c2a0001500a40c89a22a0941e1040010003c1c01c96a044400c3c40c10000d46020070741c280c580a208810250307012992800052401d04040e4145d007406e403040b80d00348501140d002c440c0001c2503030003038507002480206005000400a41c400e1300d5029000030300414101b010002e5590b240103007100c040160528041105030701c031308480d40c0209982002c0f6105251038000d55a54410301c4048691082803803040d6003144140030403d00b047e8095a00070703050b603038a4001444042c041000740d0ba9405030399800303c009040320a080300c0c400c8030700a0300f100b804408115a002c4c0302c09100c17440440d050f84190440070700d49 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 610502904 1250 610501654 610501679
    0x30c0403020411090a0e150f10081905040f0c05031501031202070803070605060f010801060207140103060503011503020301050604060311060c0313150206010b03010b2215030f06090501 81
    0x590381a540043c24900c0ca5078412014016070b603140d94484d00500380090440b684807400c1d8022480050300200455583d0200840c10009004c0710f81c101c4003184544654034052205c840d13004412900d4025515000f6030900e00301c46e0100e60483e0f041690b168884140030949401f403014020581c028082c00603014042110b00005100061082c800b14410416562083c02804018800c0c1011280c5030981c51038610041d200854456025219440e518a11988100781c154126002074024261aa0402e01130110548425440b141410703114540045da5440c24442d0b20b43c11034501e000d4141141c00c5104050a41b00c0103461507219900b03140080c0003080110424204c4c009040751110ba43e2401d0328201030540c01144810080c00700341190000303600030f02c0540241e12120585c265840c03681c840300090728500003806010001d010078410314405d03021241400907050822010060482d540d00038481d02900751980400009484154051421100d4055030005e051050b90603c0b80d9810411002140f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 610504154 1250 610502904 610502909
    0xb07021005090d060b040c03060b03131a0f04050f2a1513062c041505040203151905010f120209060304060203060f0f011b170c01060317030c04 63
    0xe50009200c0c18119000318101c8400c0340c1c000d00a07400014041c01c000c4001c142c4a0205801142002c01648000d4424481c68043c0c3c0d0341e9071070032429901c450300ba0200f8030b03801c050121030301c1801a10920034001101e203074a204400c102d0400020f1701c4c3c00d1405604009101c41244450b900040007007044c542c410b8104401c500800094040d0780441800203144000b40100045040e140080c28881c0840450054025640e89071500a2540c084140303c110308200400c018900c0a03d800b41b18420345026000300c100d80e607100c501007440507103450004040780d10503996489015134058407800b103420900440d40c1e00f0841c43c400342d490300340b40c000040d00780041c0860040800c400c0145144e410030071941604d52400e0050f10683c2c032490030b480c100c00294000e40b2000e124110418000c6c1d031501c0c1409a0282c0344406030b68015030740b40b03441c4000b90f00310310f40e200843d525100505145002a81200a01030080c144400414082e10303608190140b9500e100c254040300c0c0003001000b00c0c0c08a80c0c0210b408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 610505404 1250 610504154 610504159
    0x910110a0c03090b0a02160f030201090e04060912050a0219020a06030e03220608011212050309030715060e01080a08040501210c0804060506100c170c0f0d020607090b0702 75
    0x20100c01502d0100c403c4001038115840d0b00070085440e9041030341c00142882c1520a1085811079291107582820710f81105100c0280001ea40a605010300b17001013000c103400c281301e40c07400701d60500a9900c80348688415110200021804500ca0b048070f941040a2440050502100c0008030042c0c0c000c106215150b004400c14951103c0b50f0701c070310540420880c0c080c1603400b407407004c1ca03180410320000105458820000054401c10010070090503003200080d0b0b00344c0c00180c0080c8603402d00c00c243c800383c100070071403102d03800180540400700c1c00151900440c10502e12001840c1340c00c0c285209440308068100071005c0d070147c2e03180d0001900c1c04048500b40c0300c0c2401c2c81e4403000b01c2101400d17003072440c030208800c02c0390502e61000c510b0344d013090015000d075200c1d0205004940c0d50704148441d004840c031064000590005420780030944410940000c4c2060218032071a05a0700c040b07952804030315000d5041d0a5100c07414000180e40e05125158200149280c41400b85207001079041c0140101c00c400b91 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 610506654 1250 610505404 610505417
    0x30b04080903120409020c011103070c0b0903250605090d020d08060f18091b030a031428080f010e07050d0e06070908120405011b060905060f0910110a 66
    0x10002c1d601080051034401c240112240e42e1611048102c01035080344035103400c0c0d0f40c200071041c16503d41a000b035038403c0e0b09690b01c192070440144c440c1c03210b400d00a0118121030100b04408280704460083c907105080c484002c00c100e4843c42e02e0131004607440200083c407039401c200045200c40c1d44c085519083c1c28090721301940c50392910400038149400000800d680f007001e03034440344c0400f0f040d484400d1050070301c942582c00f0300b814403c103a14203103c19414a98903812490034600028003d11104902e9180c8550041c1000f031123510045a0803c1d00740754440e940b180d0200d151620707911146055000c440c15507081d550b940f406640b08400c40b00501518140080070034001da80c2443d50f4400311480000c2d004a0f820740c01c208a01801d000d089019481050161207110090780820030b084030211641a920a800222004c0074400240140e00b811600d0740d4907031004a0101d40200b180d00c0c06460707800d40000b11824100212071410f0000c3d40b5400d64942403078040100f000e0328500380e070350340c0e0303003a04100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 610507904 1250 610506654 610506667
    0xb010816090819061a060a051606060b09090a0b030d080402041410150302190f0c060501150809010b032d190c08030310050d080c1504060f06030b0408 66
    0xd464880075900304500b0b52240601a00f0683c040b06090342140c0c1c0030f00e40400c0403200000f56801e40c407420200b4103400c50020042c2500b2148200d005001740050054220050380c1341c1e907a00000d0796216481400140804a011100c81c600303c0f1245070000d6002508114000d001c401080e00c8607080381d01d100511090340b0004065444a0300500a00c28422604c2803091038440031411070f201c41e60143e503850000c58000b94010302d00a108940341c80313010104102c0c0d0303a0f9201008030340d4240149081010010b178400001c0005101340a0a8007a0248103030580702c014800f2001003003443c00410350719151b81440f16000300b6072030109400c80040014040b4603070134001c0001140c1584d808140c00b10483c450441e01350600d50941402c084503603c660390480d150b50b80c401402c1cce640e0205070b5a0380c102e060700141c104603500d05103040e032520b28814202c1d00d04140d010342c0074508203400950882414818081004101b05040c407e52001401c20f4004016660840c0c0b51003a003110002c0004103c820001049c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 610509154 1250 610507904 610507907
    0xb090705121203060d0f0b0f09030a0207031e020d0b0f0c09091f1707080c0f013c0806010e09070c0201030209060403020d051c0e0d02060a090e0c040611010b010816 72
    0x581140642140c810042c0901d00d1800c2d80605100719a0740822300c2582000c1109a1004803c5881c000e1302d6500805019041d40c94610310070441a03210044a18103d805500503250002d0140da290b008880c00303091f038900380203840002000140071300b803c10740c1040a10001d80d260321b0402d41094000c9080d83e01181503500011203d0b42c0c58001c2801d0391800c00d210900e40c500090504240c50441d000d4540f143d20090921000b4401d0301c103654042030700011500740c09103241c401105030401d031410002000b00700382c20200340240c1c00e42e044400907100e0000c00265582105242035502c3d0305454030711b42882e0108000342110f121035402410035400040c420741541d150010b4502454000300104a250010301d0700e50303510420951140d5080b00e060b100c00c0c1c9024062640700380403590181c501d603c494265801c11055500c01c84440c000e01c440000003080b5003210200082c480d440d482c0c98203617214140000a010003021a0140b403542e07042004501059a00005d019000a68502840740710215140c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 610510404 1250 610509154 610509169
    0x1403090a020319050709020702062502060706050103020f0901030809010e030309030d2606010801031502071704060909020408030904020a1403130b0609091c0c050304030b09070512120306 82
    0x2020354180301d009903808460400c0d056040009200c4c1044803412070b81d80a0b520280c1c081c812010358045804d109507082020551310300c4c0710580d03502e0381c188101d0890b81d000440340d40288109403243c50342c98005004605210aa49241c210b00311a41c070050343c5143e48000b442d10454644a040020110451550b03440800036030389644001030070740e080f8a0705141c0c001e004d0b032110303520f2030300c3c03030001808040c03a04040180b0329000b01c1040e51041ca1503801c640350300b0007a0103941c865001107035081200c4c03404135618000103007240b1003030314825036203503c2c04030001e000c425507402450403d481080200540d1b0000011a1001d400580b000358981908075010b580081380b0107507090300400000100a01d12148483d89a400c1d4403c005103900b64458106114060204840715407240e070241d404600501c02400307080302d01540300c2c40c000d41020800e5580602310340140d4000c4903122560000e0107034400f810b00c600c070041d0100b9680401c0304010b05404030b5407070b41d0006500002e560700202251a03900c2d13511 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 610511654 1250 610510404 610510423
    0xf0c0311090105012d0c020604090c1b050601031b090c030c0f031413020103020c100606090f121b0b121012020307150210051e060301060506070204050c1207020a0302120a140309 78
    0x81c000c49c0c0701d51b07456480b20064030081a24500144805000345818281030510401e0680c100000704080d030f003560b660b5501410000c07140340103041540301c0020b0003001c030300030191100c05555021801c80c4203d0000380c02007014440b01e80605050121305000b00e9012000d555212000c480c48254a40440c00142c0080c4204044400305019041103480c03401850b8204000f21030441e80d640c00038640d1000ba00c0c2c2030365501d0190059080040d04280046495030f10569040d0041d4118981955903807801403800e035005081503580c0d1040d80040048100d0f4a0041900030b0010000101c0c1c068420360002c0c0c1c40b000300340030700b400e010007407030001416a2080180308100d04d41540100030380c1c01c02c60034a40300810111989403079080100000b4034142010b0154408880c0c01800e40c0d82048020303402c00018180082010119a509002610242c40000c001034022115030b005070600c902c860500a081c401444002e00c00048100010b15505900caa000081c0d62038841500d42c480d1a4102e8203424410560b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 610512904 1250 610511654 610511659
    0x140402160c030b0411041b0c052a01081b0406050c010e0a0f0203010f0e0c060a0302071506080f0106080c0103021b0708030c01151a070f0c0311090105012d0c02 70
    0x841c01008002c8200c00c403a00803030040c84407209a6428000300029202c03d24410070058810000042269001d00200107c00e445501030b1110005100080b0203460040a42003108134074000c140142540c21031304954000c100e141140b60407002090a03a005440317140304440401100140228042c0003e51008a0700a07a503c20790300c0d0a00d080c20041150b2100c0d4109030700c207510b40309080d503810001d0300c2546192403010014081c00c1c00348004000d02500002011000c0c15004c02c05840042d50704198181307100e2004000040083c01d1000702407070001d030300b06103641c00e130701d4050705000551000403018481c000900e00580d07101c041010752002903024407201f0b5224403500101040c48140032000d4442215050000c10000b03459401d44190b0600c248500400d6814003602026501340300b50080001c2400350700c141034040840c0c3d80d403900107001548142d4101e404007070100c2c00c0389400e8aa09005140901e003018642c0070301c040784244070a074811814118a540801602076900404506c091140c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 610514154 1250 610512904 610512923
    0x3110114040e1602150402090604020c01050a09211b080c0307050a1101030c05090409051e0304050102160b0d090203240105030609160b030703060b04080312070914040216 75
    0x10780403030210202d41030340c150210850261920700320902c001000d99003000c400c1804001c584580c2c0074002020409002e40342c20540800c0010b423564400d00490f40035080700040040d1001d440e00b8000502556146c960090b80c0b801d2602000441c0e110100307003059079000300004005c0200d86007220301072190b140c01b07501e9400301240200c240400810190f01144c051500f1010b401c00960044044810754084040441d0341800004260f091a0340195030081c452002c6a103805a46851960b9103114418841c210307600000e401d00c8a964144071030040702e00510a1065001d003020500d8880e40160100880a950b0340d0040005641d42040240104000d900e5521804002986800070b001c009002e224064840c0101282000308000b65903080400c2608503400783d5804c2c00e004004c16400686200c00301611180c1c08986601d0040080000f0110640156a60900501a82c1041200a12003014032014003010850314243e0408540065022140140d50748003c10f210460781c0407801c006408000d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 610515404 1250 610514154 610514159
    0x516030203090724110c01050a110c090f040c1508010501031505090c070209010f080c010507051609022a030f0f070b0a09022e320d060512070311011404 67
    0x441006960034001355035815030000a0400880d611540030500c14000384040107013a00701d61045004211012124050b14200f40e06000000c065203c165251705520308010306100400001d8800103000307080180e0404000001d450001d009808140701c2e4605054a408003110590000032807000076190003848650581000e04080d00e868000400c00c90041c0d8455001080c1450200316000446a80300002c19000012000440701500088000c4071f843c0700d001d8903040310b51000580200500b41040b80162941c0716441400101242c0e01d0788014040c010017122030a80700c0c040b007201c2e030510a284020b0b030340e40b082e00c210500c140710b0070310003401813110b0b4020310811820a400081c40075000301c8031406e0841d2203040c54190001c400465480400c4e000469009c1c0c40e00403001c060300203100d19140d504200c07203150420b92121070340a200221030f0f0009003c40c00480103204080103828281c0e500c030401403c0e034035180c0d640c810900010b4082080c141d2030b04110381c45030000e190020805500f0503241e65 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 610516654 1250 610515404 610515449
    0xd051b0d08090f0c060901032a021006060e0f041e0204290f03040b060a121b0f0515090a150c050111030c0306090a020d090f02120105160302030907 65
    0x4003030b20301801c240156040003078403020000e00400080f0000b003107907190042c440d005400800707240b8040d204420255090400d81c20550f030125031100c2d8142c000d4402202810403070003c1b142c250308240c00b4040a6001c03c0325540310303034100706082c44c4141e500050494015038075280036048428032041c0c0900004011440c00c840c106030784040500c1c0c038507038601c0180304980031071036010b041900d483c6184180b0004000c84c880b47d1000f03420000103000e102c0010b0300c4d0003040d44803980c042d0b01070b1400c0c0305060707414410703085c0144400c000380a20400001018200000910b0821001c0c08602080d00045450f0f100c07070340c40c3c42c4508000d1900505079031202e4031804000c2c103a24444402a00d195203041035542c103104844007102d200d448007080c228556926181048409600542051402a400e0041c084401d07001c1c8a8982168060190140c00d502d0354030401524282a840c10f03400e5904203024400c0c000d02401402920001ca1b040143c1c60780d481c03100031444c11300558480315856070303901f10002000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 610517904 1250 610516654 610516667
    0xa030504090c0203030118091b12230d050c0f0303070f0306050f06090108102114030c1507050c010f05060f010309020102071a0d06150206070e030d051b0d 68
    0x45032001000e21035002e802005a0716800240f0840041d040c0e030b03100e920900d8203103038441c02009200718199400035031245100780300980c040d00980d42180c8010080020b00080c002c480820104800656408070240b0328a26103031150504d044040c0007010442652880342840141c040c003811108807034882c0390100340181615004011100460300d0203c0101c0d150a026802e03420f0f080c00944803500d0011000300460b800301000700044114400f2400100b44850702d1003c503001d90210624035001d181c100d081c0b030080e0f40d070088500d2030654020821111040300c04502c42c031446000c0350041445590307680c829030b10b61041c81308010140d40307070501c01d00c005080d075881140540d805441c81e038044000040103401f1264020b0f40640036a00042080003402c4004c0700012551100384066428964411110002e03241d40d600488c003a005100310040400f42d0400603903038020f00914122080d58120000309440e1207a05110394100180064000c40c9045104008400740b0001403c07074000303180c0c02c000105031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 610519154 1250 610517904 610517909
    0x60f02070515070908150705090d060606110601030b011413020d06091b08041b090e0c15040b041406070b0a090212031315020a081912020c1005040507080a030504 71
    0x80030b0b09000030480300740c403c0d416101660300e00d2008012002e0518841c000b413903401000c001c200b1104100112280d01c1700e14000b40204d108000c04101d0360304000010b00001060103142c0342581c002070040002c1400d525005045444210f0410410382080011480b101c00b003080c4202c2150000480d20308884e440ea000b0021500340940070040ca403502400e8160030f0f80468039800c00282c40001103000b2600c03c01034800e240115241d0900341c595140303418000e841c02c59804450a03000850b0041c01810201c0b807003551031145000706450b1a00708980d8544501407409210416041e603003640080352100811903150b20342016202c006880d01c1c800301d2021f00300700d1600b28011034500081d43c04401c800025500000f401c2207040540c40d0070541824980b4005460110442c8600118080800c084500070b0070041001c2c2054036a021100b8405405c40c115054680170a41c0b04002404508002041c191207210700010f002c101c80c4c50f5414403e240541310307005405580112001c440c201600030000300f04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 610520404 1250 610519154 610519183
    0x2131b0903020a12030c0b07110d08011805190f0204090603060f0b01030b01020c010c050a1220030403020a0e1b0313141b09280204031a0106020c0d060f020705 70
    0x10f00c1c80d100d00d103101031029000380003008920742240744c00000307842c131101707503030058680c544251307141800c42d40d0500d0314842000100204603408010b0001444a170002a00410b00c948140203d040c40003042c030018002d14002c5c48501e5585815004036417294040300c004000c0500148995a02e03400c000004190003400c2128880c5000400d100355402801100709500058014240c170607000001925001d400741011103181c0a403040c031100060485080040070140d940c1d078040e200001c813182ccc161130749444800001e180e00c103100c200016905c14024a0548140d148450b103203482d050a0101811411580c2e201e8140020080000c003104940d18130000c540220b01034100c188511031381c80d403200d540d003454140c8607502c1e07481c0a81c02e061002c2c4242e08010796000b015100c40c03203498000c544604140061101c1900001e00b0414484003102140045545000c04283c030351500b54080d560380c0103140e24500540364403008906001150b0300490300090548402e6654000f540381c81500d8140e00c600410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 610521654 1250 610520404 610520419
    0x2090d031d010f0909200d2f1c020c071e0b0405030703080c120703020106050109080d0807080c07061a0901080f0a08181905121902131b090302 63
    0xd50641c401d20405400d80307a9925044505070800e50114040c05480240b0100740350003c41046c2c086c0342000c010160641d40c9040080c1028200b1019000b49400d0f901080303001e942140030a03421186031041724082500103c14509400f0f14242c0301c0040d002d0700000c2e0303003d40503907031001456014101c01110f0202000d041c0c0b180494880b030059046028902071182c06034407040d010310000705000300a02100342d03144100c0e103211540c00d0300140720364007800c000ca0042c2d4403900104030650700105035001400c0350078080e05c2220140f00300240740c03510080440341007000003800300701c2c485007480848800350f411100500110710142070094840080d10041806000d55000002d00e06501051000300c00da229409060171040b01d40b0307000c00035001085e2174150129134021115941d910061015030b0818594804180340e80351104212001c08608526109500250307110458034003502c03441810160304a0350b9205a05805207000d0040070740404040244108000460900d81c0240400e012644200c410303c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 610522904 1250 610521654 610521707
    0x9051008010323070512160f08010b01031b140d02220f08030a0e040f050a05180d20030433021603060b030f120c010b1002030304030f0302090d03 64
    0x12100710f02c1c28564810f9900543c5040c091840c001c08216400c010450844082a1100c0010001c04446a010f907040e04c0c40340c0301c01c1021560030b00514119a4003402c040101c43c6a501e0625441103017290400d040001e0300c0d107036240009601041d601c59a1810701d04644a00c854204588403081c0c000c80703422403084410000401042003080d0343c0594020b14091405c000401c00207454490b000d04129a205480364040c03006685203120b6207124a4600c0000708450034008401c0300358030356180082c10b2581000d2040c1034100e8100c1540c030019100005111009a01c4000da18114022900029038615001c0664001c1420041101003002c05500c3c038a0180794800711f0980c3d4519000e1007078100d0700c0000707400304040350140c2d02402d48a44064192894004a8110141003240d440c00c0e19031400c0000c280000b01410900c19401940026130341074440190060004c3d6403408000c100a040060740000c0b44201031007034050b2109224080c0110081e00b44501c0d000e81100f811a80d20705001c000b080700b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 610524154 1250 610522904 610522943
    0x3050610080307082506092907050a050c0604141014011202040b090405031309090b0a090c03062c0105061e01210b0a1d0f07090510080103 61
    0x18842101e140a004501e0a200c03a038451150350440350003800750012520f40c8502c5058410418012184180d074001a4080289006807110780d4280c984104c1a10101c0000803111400b0841500008181412500c8900c0224202da051141c64240c000790302504d410311040103034581d0301d19140c5100b20140d90600d00d090b40c050301201c03003101e904040b400c414001040b02071050040300700382038000f8002141c0c04407070074081128210141d40c100c407107174000038510046001010003840507080308078041c010030704191100642c07000c010b4498406599075544100030032041c544d4030001542d11039010301201600d00780c00c08605000389a2012881c0300140c1801c031941c4107100c0c191080d40c00516403814040041294100490b81c402c84078184101e1b645126454401e10003240314032066990040b90403850041440300b45251a406205100c100b091031600d059149580254020410400840c0b44e0395002d90440740c03106641d204940004541c0c20a4007590350010340581a00e010701d165003480002c9144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 610525404 1250 610524154 610524181
    0x308091e0a050d0807120c140304050d080901140a151a0d050a09030f08040201030e10020306030d0f09090b0607060606030e0120090409050f0115090509060403050409091a07030204030506 82
    0xd0017000111520000075031141c00303a0040c03020380d0f030520f0500404d0f000020b02c4140c80d0b00540c1c00b901d840e80046042890180d03c030000350707808900d10000b441a85081002200044009400b00b581e4070303125911450500e0351981500010100c035600d028004a19940030082c990240d0106140341d400c10000a0145603503015118400e58140d4440500c61035910088402242c05002281015205d090404c17038200204181501044003090060b5a81082000c0602d0029905c201c07005110718018501d0405801105079011900b001802042002c20103000900f41d204215004102510b852001f044086e0700d90301101c81140a01c0c02007180c0ca0318000a0b070200b01c1d2604100c000c41e18100204881403c0c20b1300120b680500c20001c5481e00c2003079000103030940394140605403252128400130020f401141c0600c640100702d99024001c203003810b8070f00a00c44e10840c05221038094032140140104242c029105060310b0058881034128240703550000c001c0d41c4284020343d05846143d002c03e210b001440d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 610526654 1250 610525404 610525411
    0xc030506090f070c0b072601030305040506030c0c03040b04170616051b190b1b0904090302160e0a0c090e070809120a032003130308091e0a050d08 64
    0x1011103800340d581000b03031610644014490001c202001d184440040c1c1c4034051503008154540b50035000c8880f001100d50414103400e1a400380359240c50041012a800170112803c4e036005603400d41d80e954800c4540d0745036100d00d01120119110000f400500b4400e020040d005650604102c10708d0420b9408030199114803d03229182c1c01c8220248074828580200001c00e0307007100fa108803886006801c26518100501b80c0d031000c61018004000e88100200e501d0810344c0500d001c1c040480420100000c02c80c3d82c0078200203a40240c1c2d485070b114050600070044003e00046404505810719240d0346024514a800e468a0010a040c071409403402c0e4012401c100035910480c500d04415a14600e0840301c1c403001624514503805112524000241050024522202e503030302e0208e0764403004640628010315010074400700c0c030303070900912684041d002d2042e0585501854403a54a031920842c8a040c032004160b5020003401d4200400380008001c6a05501140030708140d032004156410b06460b42c24044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 610527904 1250 610526654 610526659
    0x5010510020d0e191502060709060c032105090106050a15021f020403050d03090309090b030a03080c09040608010b0f30010207080304050c10020f0a152d0c030506 71
    0x6400c02c008a80300d005000880800144810a94040c2401d42e4551031040c0e0010308500a022100102075501000a66008892031030568000d500c1c00380010b00c400140f0900404011b80d400307501c100c03680d580e41c0407210b038040c1000401c510700b02180400e00801d41841080c1c00703241040000034419120705c81e80d40c1508596006000218082d2010034000040701900001040d4248030103c045581000a08640b115584000400f2011401c001c1c0c04001c169220340c10881c00c0c542d421000e51400b09041118a0b81410030070220f03101c1840010482c000d8101d0b10b50854613202002034000130540189981c1d0100b5151580c02000305000c0c03045a9220b10011102081150019a079844140c240305100d5880080014206002c0380e0701c800c07166000b503078241d406034000ca650030a6460f02d0401e0008408a40c00217001c0390140310000c90b140c031003169000c3d006420039002d0480070240c542007a52004000003480850f100c000241e0001410400074082200f49006450340c100d5021f4440c603400350100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 610529154 1250 610527904 610527913
    0xa0203070806011d0a060b130609050604051507050114190f02030603062d010b03060319030f0c1a01080a030212030603120f090d151419051b0d0c030501051002 70
    0x31401d0110300c0013005403001e216a81d070780070f0009060451102411141c1d242240800aa0380347c4039005142e090f880e04414407a1030304100402582c2e65908040c103007816868001c036228212401d2040c01845c0e400140200c0c00042c108000002c020300a41249100a202d01000307003d48405c0000100d01080b909190035500c440e0100d42d24050b24030b6000d4036140104100000c2110482c01848105000c3c5d00414a0307510110074080710385002c1c0241d000e035012080f604040311410342c8000b846800340319184400d0000c49038000c0140503102c00554801d0320782e01a00d11503035941701e03140c680c3c41510070020b500502400c1c11861468aa010890f405048010014114071043d20841003040e40159098070b51500d040020810b2601c545c1c49e180ba00c03e00800d607030244070075481c1010007543d0305c0c07050b80d2000c0c10243d01001108941c44d043c001607000e5011000070f071540d4028074080c14004036400076480880201c0c101c0031140f060b400807482c1c42e0441e41c0601140e6620800e0060000c8242c2e013040143c0c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 610530404 1250 610529154 610529189
    0xe01062703080306121002190f140322050d030b030d0906031104090c17010b0721030905030d0f1a0127090c02030304121b030c03020a06020c0a020307080601 69
    0x1e1120145402940091000d0f605d001c56821842c42e0104407945540708503000304a000401800e15100c01200410381014420f804003608000e02c9290341c50090402a00c02002240d00d02a01d2190a4000c0701e106624014a140c1c0c0d00f003465580034003019150000e418051205241c1c18046440d2501e40c0050321407174045410400c095006c1c2034204a2a280701000b440b0014040480340510034000c003040e180c020004102d26208038917000705030080c04950504105500000340784009400203901101e107081490f000b5860101e01800030b104000c0c050f44000305404481d00c03040d5010b0b800c3e06103d42d404000d80442c071048400c051000c002c2c618040b4640b0899094080454200c40d507079007180101d0350750307140d44904880003100c1003030803d1340060340701000f000100704091403000c60790491402c00300c2030b0344c449049003640400110f2004040185101113a010103008000d403811069002e00d007551141035450507103540705109003080c0d00c24403903804002440304000c2801e81c181e0314180c1e1402000017 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 610531654 1250 610530404 610530413
    0xd2904020702060a031e1805070603060b0f0c030405030a0819170a0923160b040305030f0c12070b090c1503060d080405030d0306080706031107020f010512010e01062703 74
    0xd0b040c1c515103410410340031446c0c48000e44142240ea62100741010442c003c14281145007042c50342004c418189440c109018011100b4140e032803010603035004a0303a601c0ca001d40c0d2410f602031580b1050305481002424800c0200c0300e806003048050250030041910400ca1045070074218150000140c6950300c030100e4081082600300c02c2c4000d0042c07103440004a51203000100f40c585600301d02a01741c10090fa14440c2c8030000650720020b0203030f400c015007007505545900340c5910551541c40001400012845150703002480058805146000c00725140c215604100000d10800c503401c000901030310b0710302c1001307180071280c2200308129140c4040c1035907245014007648841e042011382d0110014400052076550411040800201c1d0f55000700c1c44a103458899817616a40d0b40040c0141030601307a1011010300741005481c06c854040314103400c0052014010b0b1541d22508100901000120001045540303440c461581214042c0c1c1e40e0050000903804950348032212010099aa841b14035410400305 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 610532904 1250 610531654 610531661
    0x4170c0d0f080c060408031e040b0a0203091509160b0a08011701061e030b01060f021b010306050301090f0b010f080a020405070513030609031b030f12020d2904020702060a03 76
    0x201d204041552403e20790510081c58100f0444003180c151100100700110421103491042500c040b01c05240d94030300303060ba191700d54034000510604180381d0200004100d00d07010011000c4079000700702d021556040990f1800d8039890301c5218100000c12a038400281c640320b100856801500a5030b0301d4202d41d0030400d00c0d80006080c3e0080008543d01d680300400c1588070310510144d1800320802a5050034610724006c038600c1d00580c086024000b44014015a040c1c01003100d40d101c1c081000d1013540c10711028010f8004010a40189070950b1909040100300700c10034600310703002c41c002d41d010b40a980e030300e202c031500150060007090f40a40101142400504242d0000c5402104908200e07040065654502d02d5a0704c15a00654a064841121806141d008030f20f00043d11045449010604000d48000d0040104200082c04000c03402040c00315107038040e819241500104141400225a03802c120700070811107040001600711000d400c820701386014400c03560b00c20350140043d400c0c070403852420b40c000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 610534154 1250 610532904 610532933
    0x405061b030c01020a031d03040605160519080c1b0d0b060a090207050a030908011434050418020c061f0306020f0304031d010813050f070b04170c0d 65
    0x52000b8028001040c0007030000d0651501170307640000f900c80d801d2801001c416002c0812070400c0d00104401d1110301d45c0041118084a02c04042e6800f0581c141390561602c1104a0301d8400040c07680844000c100400f00106810481102201c1c001d255034407501000700c9040340c2660380f0001d42007100d0b00040b8810402580904000d00e040d5402c0d950700c131400d003079130b110b44c5d011601c81d017024941808064110400c174010342108002042400100b03081c0365100d49000e050703060103081a04510000401001003020524a5038502d05850010450050400d030494092409081e1002041244441807032080c0d0360940c048800606480e1a184e020450544003840b039103002659080003c0b0100708c06000502005282c902e01c40d5581c90a07080042040205404000303055a50340301c2803240c1da0b4051180e03038100081041c20001e041162070040d280c5401c19282d04501e001d55040007640b00328100181c011995482028136540e02c089041945400c6044807aa501002081600300402e0174050680c51 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 610535404 1250 610534154 610534207
    0x1020715030f0f060909020316030305030613020706141803030c12090a0507080604030f05070c170c1201090519120e0112050f0415060806010b13120308040203060705040506 76
    0x20b00782003030f40500f001c0d501d10341c0000701c1c3c2d55210341c00c1408505003002208426031038401800882c070f0840e90010b01074400030345014456100c0394a43c02c040703500c640c115910941c1c04401081130040400304042c00641c2140c000c9080741c8488045581403a011040701e2080d150411058131f000c254400203120440003034400d18a030710940c516100011400c10980b000703072401c08000c041c20324062400400f08610b01c1105410840184502030008510f6014242540ca00e8054440300074080c8403031614142c041c0300855485650040312201081066208810780b5028005941c1c0507241c03244151070100b00c41c41c000740001c2404c9480c041ea244102c0072030129010506d400e001005050455500b55002580c0341c540620105050200b0050b082c221060060713032110341400307224501801152104c2d03052245080d110707400100345051110f01e0900001816000c0b100c07035a261315a08000b030508000310360407400780c4900004544064014000e40b011a0802841c50780380c03450f00c840740c1c011007446442102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 610536654 1250 610535404 610535411
    0x105040b010f120e0c12030c060a0e0a060c03111602100305041e02010909050c09031b0a030f0206070212060a0506040920010c05100f060902030115050c0327010e01020715030f 77
    0x50240d6610540c070300001b4440f10042d5181c0721950380700c5003440d82c06403412007064504003a071b400c441c4002c9080070075160420303800120340b5501c12041e0050410b01c2c1560600b000c002a083c107546080c95421700615009440403010040f0a0600380d040340c1040da4090031131460300d000c6000030900c10511480300d070310600d005103500303a43d017000105403a400c1c3d88000d2060004140725009050420142958185020070035400d260920045445a1510300014280b602082c28100039900d4801c100c40c2040d0f40030f020b800d4003181d01d00c01580c5820082d68001c8405041202144440c07170103014003007903241c11203000540b0030207110220b26840340701c452203418070828850850100314241303c1c1540c482010100464494004e0000380125400c0750001f40d1000e105100500804001c880c0410b06040c1e9070600c02c1e81d650070380311114510b0003114442400c2400703414500c1f202c030207000d510b5040c0000a0b282c0d41c5492082d80b005a803521120b000d1000d61100c0719041000252180d040000400712108000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 610537904 1250 610536654 610536673
    0xd08041a0403050a14250b090402041208042c0105060c010b0d03031509050f0a050c07060207031d04140a1a0406140108070203120a09081c050105040b010f120e 70
    0xc60a0030302c00c4c00103071030300c003030100d82c500c1e030001c0c140851304008010310710840c2d80d561588202150aa200c0c001d00715480c0c00030400440c103458030350446000e02010503e10014a4041c50121415405801646100c2c407141341068800a8005281a040c2da44210308400c0d81c0e0818003403000e290000c1072413900b50f64a800030281681c0329051030703522281c020394010406040c0d001a030526104c5940c05600410329240400100d007032120b010365003151100d00080350f1511000403009007401001406821340d440010074000301a0458814149010400c04100c10840c1c40c40030882168550030b01c01101c56a40070000d09210050b40c4400c40000340c007480720201103654808101202c1043d00020190302c0c02c255500b03200e603000000d0300d43c082c020748021458484000700b5041480c90140c440c1c6001754a4989900800035444141d03a841001da0480349080000001e41c01d015203c28450203001c1d514015030203004c3c0d44951501082d040458543c4591280d88480d104014081500201d0f15406441d604 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 610539154 1250 610537904 610537913
    0x5070e0d0501051008031630020102040513020424140c06010306050a090f030503280c121a1212030705030f06041803080901060e010807060e0d08041a0403 68
    0x2034508107000d140001014604003291140484560300030b502c07541e1040c801d00c401040b410030282e2020ba4081c2ca1108002c131032171a4100c24214007404d464a8103070801400d18802d80c1540603208580e0111501c07180b581e100720100040344101d0040c81034407803543c8070743e1802c0c486418102081c0b01c00b030700c0c2a8103252101d0003140f11a0700300011031503083e0401001007090051500a45030040840310f4100240000c030f60742e468400300345600003402c0c820040000752545484e0f00c84085001084008610300c000c50320b0320500140400202040854020100724aa801051240e102441c40086010324030000000800500f50b0451401d0740540c8100400c14091082c01c9010314014a46030300c50301c0c1c0b40d091030761104420010003090381d4000d83c03800203060040c80403030303121804c04c641509007403c0946031440c2282c09800c19800250f2a6141c11303000261845000490300100c68a9541d0010791003421742c1003101e000c08076a0050031840003030106002c46025881140c8034012035081d4949829601d549 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 610540404 1250 610539154 610539169
    0x708100f12030f021015030c051e130207060219020609010c020c151c1424010806010e030d020c040c022a0d050d0c0b070c021806030c030303010902040807080a050304060305070e 78
    0x43c8010720039481e5040041042c00082305002d1b000858040324440300388000c100019404d040003d2260a035000c20003491a25941202e1101c0e0300020195038804180c410f40d10340c2000d01f03084c28014031541000604214040c030800309075200e6030f070140c2074014600c01007004520304c00540949001080041412104250380b51800c0e5620038103000c0350148400c001c3e0106008010901c0030f0070385a5a204940c0c0b500305000d0405c071010242014502521502d004841455407070004981500c117441e80e20404a400045880203250101e4060250180c40300c03049071141400580701c241c02400c0c403004044072601c41d051640407c4043c0031602e4010703a031340301ca500d0b0a28200c8ea007000b00e611440c1382c50520614551080e0312041500b81124068602e6001c241c2c81a540081e83c50500008808201e1907230301804801c280950040440e510303961a080500000e600c5481141c0c010f2181300800604d9a0011480100c8a9084800785081c28900902135024101c010440700802c144140c5188450b524082d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 610541654 1250 610540404 610540421
    0x21207060b1002070f090f0e1005010302090619120302210a090902040302060714011508030d2d09060b0405071d040b0a26060708100f12030f0210 64
    0x12410700368040c188460740412800e40000c5401241c0d0501c102c0c1c0c01484031034100c070f070140000038800740c20342c24003002084180c4c12804140560354468804515503040141031740d000b112004880e071200380400c9440080041401410340854004011110022006490033806401681d40000302c00c800711030040a0b5039450740b440d11010402c107031103642c80190174000e408114411850b00b41540c000503010f004144009140d45140c411940002c00d0a4200040c00c820408601c0c050b685c07160801e41e00e036005040b042c0c1c0040d16251152072190316040c03c01104805203401010044011710b2044080c0c071117a2002d07117000f5112185003e0513143d07407007803a100700e40c299200740010403602c00320303899044003001c1e051299040c0000100d2580d9842c15400888031040a02850394485c0c0d1030780c00d0400d01d0001c03088a02d02a50003084440b42d0028140f521400c0705807852100ad540b40c003289000d0a4480c05803d0015071003050801c000390082c11301e074910460740d004a603000c4040003040c00c103441444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 610542904 1250 610541654 610541663
    0x1501030e01090524060103230414100f0b0a03020108060603090c0907090e092e0e0a0b040507060201050c09210a050708010b0301060b0a180b0f040609080d170601021207 74
    0x2441c000c6040894a144260031010901c4c06001c14016105d040e100254603d00c03111044000c40080380c204880c0c19240d0341140b01d06412f07150350781845c40700e0f00000e00c60b1481a107000d40c108960080075180400b01001074903816160012180c075501c062208981004000c1c59842c4114000e000b242d9948030600c511038007959407100b041c203051951020dc10f4601802c41e00896116019888503803c1e90042d440c64215005140515000ca000b03200d03024003000400d010060085649400c00e000e541071035a48030f1341c012000c0750013056507004128201ca004a5942180600500c8000901d242c080701c41c41c0402c0d003040503c58060060540303641481c0103e07000b100c1e1a48818020000c01c0804c2c00b402444450440003040b01d01d240810300007152103213070440820070144441c4100c0e810040c0000700054a0f120b44031513102d1170844502c000d10b03880b0780180c1010a40c803210004110200083c0c2c1a004182541c1d148a40b4003070b00042e024aa102400c42030660280c0c1c9100c0080b500b07202c0142c0b404074001e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 610544154 1250 610542904 610542943
    0xa1101051005100509010c11031f0204150f081306020903012d18020d14060c04052b060b0a090e01060302090903030601020604120e0607030e01030606081501030e010905 74
    0x74181005043c4103070844a8041c040e0500c212403c80c2e80000e001c030101d5400c1040c9071884178400c0c000909000d032400c3d18046c1591031354007000e41c1d0035440c1d01400640780740011044061020350001c0d518190690560b5002620300c40020314010b1108200c0d404081c4180c10140c107008100001a00350380034400003a183c21070906031560408805401c041180a00400030800c0800381c0a48102c103081000d0041d0181c01050910001c1080c040c1c0c0d00454105600241c0c2e02c03034244003000405170780c018404c81e80300e03200c00714401000c03a10164000000d0750801c0200c0745440543d03641d40d4094003481116540c0b10031090300c00942c0c0409402424941203041c000022030f14214030410680020250a0100381da200f8400c00150740d0b000122079070829003201418041c03132600f5408407001c01e0015000d0350843c0c40403500200f09074020000d400c2c94082601c05004190b11031000320352452049030f40030520740500301d0010040d40a540200d00060484002041c5c00707680d91a29032030b04941c00c000810100c0c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 610545404 1250 610544154 610544159
    0x609022209020c1506060403050601260111160f050d11060a050f18070506190206180316110a030b091b2d030a030203030603010f0b090c0a11010510 65
    0x80525032040601400c80045003000000580240d0b180d5036590070324014003104010a6403a600c9100783ca00840d4080d003101c50340d41c3c4a001504104c0200d40b4800b1205582003451058040c042c021240150300c20140c8900341300105840300035004890310190f603545080030f070703140100744184949500424141c8804001074010b5001924000700244580340d2940340c8003d1141d14801405800d070010781d4500921611800020328909180440d070006030722420010f22050011200802c000c50041c85800f640d8059850b4020780c00c90002035401c0a066400070808000700d446072800b12980f8038050960801943d1300000841e8015929420a0f070742d21400004010800c4010042000542d06545402c071280d050302000c1000b40452142020b0301d201076011405652546210b68079208030010700700c0d00402660b09020791a42d1081d1039a0b4065420078180d0828024640280a040c2c03c002d0200034a594030700c04c120344a5000450144100441850180ca09a01c240107070782c090201000108451031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 610546654 1250 610545404 610545457
    0x3090b01171902030309060304020a0e070c020901061b240203150a15121a030307110103110405060f0306041d1605010804080307080c0c070305010b12030c0709090204060902 76
    0x8078560b4241486207180b0150078016200402590303048901a54903039102e1320745200042c00c00545802c0342e01d2a001c1e40013003040d800c0d4413440140485000341d960140507601d41c031044492080b659114480402c41c8204480000c0c5001c0d42d0b01c0400d01c56451010204101c40501001c0e17030b005503518042e000e1070505130031642c5030104002c401414021690241c20092120103894030400c401f000e000280c0d1044400c61840c0881441c151414004080d642d444039039191600c1700d003905c0d5445500103842e05c90070441d44002c0c88122000d64000501d01801d18850762030a80c41544001c042d55007090b04c40f81403104455134032510013454450100549281c60303081e19135010703031030081d40f200341040010b9041c000800d03840000c0b60381140c050f2401050541e42d04105001c1e0340710b0419141240e11500c500001400b406500c0a02028812285407600d04040c2d110a652401100481d44642d0051402041503002982c412103103248040c0c03000c505156a400b03954103e81154080354041c80c0e03454180401c21 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 610547904 1250 610546654 610546663
    0x609110309250b0a02030403170319020a20070b0c06010303140301030f08070609080409060311040212160e030d0e1201092d1502070b0a02090d08070303090b0117 71
    0x40300c01d00715644120080c000d0440b90560075104804850600040c0780c00764520a204550155400c00d00e000d0800c44c05500c01c010036402101c0e107850180c065808003520010714001c0364404525540d807290610b250388040074000c01100e462142d9489060400075105d20790001134819a0f080300044d0602d03616504019040c0204a007100c10079010810044c0005441100e2101c4401e41060354107803034080301d1410100a10f081c000146c42004049400101c3c0c81c03a94100714282c901c190380c203250000c104014081030b4011060071010085040e030006012212310b6018905010440c508000300b4a1620003281c1403c000a00c500006071110a40041c0c0e07041022903030310b828110324000c20108020341c4810240c80310607440b00306020100d0002e407201010b072412403140150000000e810003011643e80c500254410b0508503244110f0600054a00102d403081c0c942007400a003003540000c1d82941d0701c581550140710100d0034565a11034039000f10392682001e5001e000c00760411113541054110240c0b40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 610549154 1250 610547904 610547923
    0x30b0d0b2509030308040f11210124051903060c09051809060f070c1b080105011a03010303050a030e0105090114340905130504021806010206190609110309 68
    0x2400102d24041000903440350070980d000760440d1003010303040c54034a031034200c01240c070303502991084d4003441c4203a482c54400030312100d00b003140000b04401240c81c4106030300101c1c041d2180b04e43d942410405c0101e41040001d011950009500d10b0802c0c50b01c9076035034070490300c0060591000030041c00c01480741381000c5003050141840c200048170189041988190f0340c04009007101c07503000701328011800b0b25002d01507808545034059144421031001440e864001c4030700380700e1072003150308040c0000740e1b68030303a10040f200106013101c55629507800d64506980a60100800e1400c06a441084101c841c0c42881140c2c0074050420002c15021940e21403a042c5e40d8025080e6401c4002810740317103168048402203000080c0442400c0c401c0b00610510990700e1103c80d51205400034500e0900d0381017501664011481180708907581486141c40a640d0030314203808440f9280980d100b40049850502204615008007154050103d402611440618140c980007450f03a0100c00c000300601400500c1400140c64 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 610550404 1250 610549154 610549157
    0xe0316060e011401080319180303031e0209060d2706090b0f070c0303151d0702071d0c07110307060c05011b14030a0906021b1006080d030b0d0b25 64
    0x104d50420107010340703034440c0304120b14a405401a12842d010700a10f0000b01d80740d0f100313807005206070b80d03070a0180140034817080d000c1d886410340e01a00d005001070b1007a00e1175600c019100342e04048030040184010701c4000e040760307244240007001c03015848100c4642098035116000c0411480390310f152056500c072002d031810120300f6085080100460b80f103158007603540e80500c0c01003001405a0700450700c448060300202e442605000b00c01c4082034044200900130142036003107965840d66010388080e41071400c1560030364104000082070620031010061704259000324420403484000074002854408198403079804241c400c110340050040178481c0c446010800c201506c1e450607400e0b001030007140d14614401c88204040086000e060940d0301c0b10015507441141159504803614081514802505000040d40311b90090080a400070340100001c540c0100003d00d404512814150301405405203200d0b00509040048030225000b00946030048002107048100c07000a1121b00c010b1540c513900500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 610551654 1250 610550404 610550441
    0x509091f030f15050f1b070f0308091902032d16060212030f180f0a24021207050c0c030303010f0303030b22050402040608010e0d121406040e0316060e01 67
    0x5e14080c070316042560100701a6100d005182032001e8907200740c02540000341c41069400c00c1481059041018680a031192104031114813921002d410880001e40c9002034054018805200c5140340709403040f1b440910000b0944c445a1180300a9480c2c40d0809403605038076540c510040028640610407808152072071a01c5030b00d585031041070700701e41c14806442e00da400c1d1500c0000c071548a030148651a504800801a11031000960800d4103a04440180580b020701c00d2070403081074107800d4800c5820f003400311140c1000ea81e4600303e00742d5140d04004842c0b00c0368094010b1205156406000560207480810111120503045050040880e0b2a0010040c05000f03140c00e4081e044251448041c0950022040443c8694036071020a0140055610012885d82844203102000c1000708980303080061a503995001680d0743c000720000c1d10820340103100c409013401c000c46e10604264004c0b84000034680c01310ba14041c1da2412042e2910b030911015211295217084a4032400e01c203000e81d0400541c07228016 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 610552904 1250 610551654 610551661
    0x21060a0c0f140a05090d0c030506251d04060b030108011d07091e05180c1f2007081f020906040902030402030a02090114011209030509091f030f1505 65
    0x41c014955140c2c840e90100004284800303200e12070380c11101218809401c41a0310b448920740750000a0303140c0000c81c0d5500503070000549c19880e00b10346000d0b088040a800e1207031262030000ba60340203504603070207001d8801807000102d591a203003d000020305050b07585c2a6a0362424244034215401100020a01086a4000003840000003240d200762040480c0c0041c48000010301012442d00342c1d103a04400da4281410088c1c25144041c6006060304550b00391200320389400d08101d19000308180d0703011002110415070b10719a101c0d1782c001e4142c1c503c0e140440d080c032021a80c0302d40741c45410f0f4818601d65001011030345d402045450030003c4403010b01340035814854458009000c034083d82c058418443e50100005066590401c6250380c410740103020b580895840300202d407405000d10288038082402031202c070246818610560205c5901941c4007030800c0507201c00c100e4000000707031040c02801e030344802811540c2d07000020080290b01c02d46120b09401035a203044000c40d84901040c800591610042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 610554154 1250 610552904 610552907
    0x80307050312090f010c030b0315100b0714060a0c0f050c060601081504060e070e12070e0601020709110d0c0806031c0512040804030b060901030312050621060a0c0f 72
    0x261442609032a10b048a903a481c28511441c0a5898100d4805903003000218540719070981c4c0a03441a010680a40711001d203080f25a91590000399016031038400c0c4000700b0800c0d21210405812250300c0703202c00c003001c090b0b290382151511000340d031241042a980c2c4446600c40307400c10f440d082c039003c55080850818483c0c0c0041900c07000d00030001c50504c1000307800101402d10b00c5081a520410040c010412680c6403d840340e0740440c201d03030311004141500a255a1454100c501c601d0105600c0000e100703680c20000c180042010240403281581300301c82e40881c1c0085607010300000c078248180000d0710b901038600140180d03400b8031121700c03d10000606120042d200484c60110407c1b4007103844d50003101d030300011a080d02c2281030294561107031074240020007035020001c00c01c0340e0103507240001e152a104100403500c00203120040118200038006104000c3c56008950700400c020400450440d003803405450b10b03004041c001c056074025600300100c9482a1107032041c02d954911380017a403010413180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 610555404 1250 610554154 610554157
    0x909060f0f041502030a0b1c080702041805030403061b050a0215040c0f0f2306030f1905011212020c01020309060d0f0c0c03020105090102070c140d050d180803070503 73
    0x600e100c141c621100040c00d2111041260381a0743c3c290100310f5407441c4c101020802886080040f51145a5014080d501051504117006049070899103851070080164208001008201c5181da100d1402c1030021b004288144003074401540555030103d0390a154102a40300980c0f04888201880300900a41c500c0d03036400201c0c400f5100c4000c00d00c0c0301035240d5041c800121446a440700381c00f003000751004074115900b02c46120072203580740180042d40f41640300b0031807440b00180000d900300400340009840e1032440c000d01078019070f0800c0b0030844010203d50b804207032003098203c00d00d522810410380e403c11290880203440d68045201410500d170071b01000075141e100e03e41007207100f0200801c25202c1d200da0340d4051290f50907424420402c148107040d002c1c0c401c14003800b06402551810002441048041c02200c44590340b0440100d085070030308400381c030451900340f461600000040d0107840051401c01c40210543e4041e103401070b6440048440d0700e071815003a088107101c0d400034013165000960010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 610556654 1250 610555404 610555411
    0x18030914091603051801020406030c0215010803160804120305090f121b1c030e09010902040f030201030c1101061707170d03050402180c0310050d020a0308030726060909060f 76
    0x507000c500d40e05d500c0c3c1c8000500c43e0406885510354030000d00010300d00e800d41d10000005c1c2e11a000e4545d904000c00528895110901c00e02d400303a0010403124420140e0703080400d1001b44621046410952141c44a14980e05003420440c0803450000d04000d061400e038114407a6500119a4601140303c0c0151468032002c00c0c414511486400740540c840543c1d030101041c0c50442c1a1010b604445100c2c10300402801c01d2560380d500650308000049007050365402290300341c481c114214100c40d0710310703801140145200c48115040000158510c41a100e0038005c020040c14040182c40480303168039503940c1000344580c002c0c00c0c04401d049082c00380c00c0340400c1400000d0840d00740083c96546600105010812140c0202c540c1c886040400c240c0d840340b1005940109414403414450300e880d6014007140c4000b800d00690b0007140c2140400004000f41c0c000c50384010740f49803001da1400170404075002110303e00c401401110a44c0200160741c10003980c065802555440103103124241401021036205028 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 610557904 1250 610556654 610556657
    0x9010b0d120c020303030901050106030b01021603081309050a0f0e2a0f031e010f05071b05030f0703093b0c1e030f0705040f090e01180309140916 64
    0x1c400d03140e500c0c0030b5014100100d8014081d00d41d2480c000040318000d040074010080800c0ca8005090495480003c100c540400245810125503045444214417608800004640440303220f0012410704110b0080c54001d80a602000c5559550550503c6c15078281644407001a400a101c0401e041003004040b00f00084241540315401c1061010400c045000d83d195034241c171508401d602018081400104420f49400080001108201d0072a042c5c03201074807060000f8059900070101101c0305072142d40014401e5003100d242c8548184561800e8002d040180d0108002c03010401121841c84009100500358011402d81c056090680d04980d401d0f100d09007210b61151800030301442407040403030740d40c90055543c203c0c0d4181944400e00b0389910460721070038401c0703421011440f041c5c015826174040c0d502070141b00b20780900301146e04000381155100182159210700851002060f601c10300c00500c0e000341e50f00c5058904046601007990900c1412500807040c2e801004402942c1c0d4000c0b144160740f9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 610559154 1250 610557904 610557923
    0x80f0d1803170609071b020d1205030703051f03020907030b100c05060c0f0f1608030f06040e070302090c0a0c080a02150106091d07020a02040501141c0c0311061b0d0809010b0d 77
    0x9500214401003520074004240700c042c1c074000c22107140c200d0080e41c03260cd40380c0d400b840741c1d40e911030b602504103044c92002100c031000b50b041440185000344035590301c42101d03d0b0004000a01100180c4555140f501100120f0312040c444414040b0900c0f1142c1d1100300307011064900003000c1c420041600c20070840d100c03039920100c0c1580500720303104c0c03c0310034954020390f500f5100c1c01e044026031441281075a4480c40340d458074040113245500803c200c0105d98006041c0c0c1c600359900008118958007460f010f000300311280164900150201001d0100126154001c5c400d2742a1040040040c03001038000300c0503c0344908040044444801c1c019084915842750400c164540030b1703099190155540d8020b40c001c0c00c107000441c1c0700300c007500c407030a40c03108c101c5000303008010400080800035001a009054406114001d1012170348e06012401d810202030002494091070308075010b4074890454140a40c2d030055401d00d007041380c4c0801e0707141d00a903101e40200402c409081c000380d094140d074074000703101c00b03130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 610560404 1250 610559154 610559207
    0x1809010b120c012714010e040504020a0605030a090c1e080f03032d090c100c020901090b0d12020a02190b0315041104080109050d0c080f0d180317060907 67
    0xd461001d198194405901c00d20313080e441c0d03d09004000125516a4000781140e0103508052a09014140c003590700905010082400e0030000c0740d15a200520302e0074526100d000c807100040c501040c0da0014101d01d03035450301c2c1c2044491000c5419542e43c1c02403030594044402e00342d01107804011242c200c1c0b141b143e07030340100040c81c03101c12040440c103400e101411701e41c2c010881c00003030101c0c1a800845085503441034161484405503440040c10038041d401c160180c0040c0400035542e81f042400c6040204000d10302d08140c1d40f50842000d1410030f00c40140c00200c0b4020460401842c8503241c0740704d40324001c480e90b0601c11003c61501000749603245110b660132140c03225450326400b03114044c4c0c0d2441c04070f54507900c4c1c440d202d001c0c01240c5030890301441503601c3d241d80c5038440d14940040c0307a407042801d49050600003148846810507080e44592560307410544035107000c903140f20072805100e41c40b040c4103070b0282c404c1070108400043c41e9a008240803420003030b41c550b112081042c40c46401e02501640345 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 610561654 1250 610560404 610560437
    0x4060b090105011d0316080a050f010e0307110d05030f04091515050904060317040e0a201323040b010c0308011a070b070519031104060503070e1809010b120c01 70
    0x75446e01c48507007544420304c0101b82041c000c03034a1909680544202c0301c00340c0596402031301f200c15101d0f200c140340d001401908001909000243c0c9210b400401200c0a0500e54461a0850f44190307400c0c804c0c0034001408001c0c0008034041c11080011145104e0489850846005d031140d100d00c03050340c108040054000b50715500e41e80848c0140d80c1100202d8046542c0c00d07000c00e550f5101d4082e02d00401c0c10035002030a0070307801d80100a80d0060500c020004490344005052441e0005203401061007d910000716440001c10030000d08444010181e0302440b0803501844210307011082c0c3d403410030808040200c042500104000d04441282c40254503182d212402c00c911401010b100070548400b01d01440300056001c0003074035500c0e56807080c5102546003901c0a4041340d2100b211110440018001040500d0141014582c02080b6042c05000d4521800c0003860140c3d88080386008188004184045c0107400d200303810800800b0707604501040c0128000d1136891845071030a904128081c6441c41949 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 610562904 1250 610561654 610561663
    0x3020f01110a0c32180c0408010c051c18110a210b0105010801030f26070507140a29070203030403120f090e060d0311030c010504060b090105011d03 65
    0x1540c20182c22030801c0e848051501101c40301040c0e641101c1d5a1900c00c104503400381c0207040f100c0348000c3c01d038000030705e41d85410042031200a1052848010510000a06060038040c030440310b07149070b0f00c0ca5035a249907641300010711516140c1888007441c0989040d0380803443c091205103207030032004e130009259100001900c0444d03150450180d202e05030700c21040902000e200b04055030304c50700d044d000d141e03215401160716480920001d060904908c2e0a1000f14205220a4089c0d109600361620f5500158400003540e605c1020201c882c0d50026008000180140080d500c42880c102c0344c1880c09854081e00a880b01482404a400c403010940b1f240e808014813000c56600035806401c1d2030700c3c1d50b40c90400d11150788540ca075582c0440c01146c0c610b044a8400c16158041e5035000004042a440d500280500550310500490601c0449400b203a9103c0d410005803003000d8824002003490f103803600d400c40640d2a51220540105408d00050203a42e800c0407102c4030084c4206240b00021034802e000a181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 610564154 1250 610562904 610562923
    0x60926030a140c0312010305240406050a09080c0318040618020904020d0e0f01050106020a030914030a0c0b1803031306050f0d0518060702070e060f031606050306011803020f0111 78
    0x214480001c4040c2c0c0c020a081041b03040700d0098081d1645e0b030030030150341901075071403040d04203001c2001d40020f00007440c07503802680c22001d800b00004003c5c407280d41d07000e410340c400d844608055002058401c1000d0840c00052184001130340d0038010349180242a0401244c1e1600303800241d90049642521920b4a83c1511000c94402c60700340403105411241303944030300d400e008551441d401c11001017545400000c0c40301030f481e0306644001d1075515102d002419141101c1216606004040c18580442c6a41441d18040c06030307000a0b503903403d125242c4012031261211090302a80090256a461002e1903480d281152800d0400c0e582e02d813003068401e41c0c6885050640e081d418074081c244102c142c1c80041c7d07003050f0161001100d00c1070301d03841026a6911258403c04a000c0c0c0d1100c0050f503141411070b44a00c10810103012a0380310004000550b460010a4100d01e0008002100f048115a8024401540001c108003103401c40b50454000c90b211001030003050741413040110500324209010016001e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 610565404 1250 610564154 610564177
    0x60f0a020c040f0603021305152707020f0f0a08041413020711130e0d050a0203091e010206010b0c19140a0b0103060b22090516060926030a14 62
    0x407890300b00003103900800003400141d00034002c2c4d2a007c010340f850f51280d1402492001500b1050080d204108040c52013121144d01e600c51201a501c115080382c248410b0040c04903401a00c40e012145035680d240250341e800901d010f901516840c00440d1001048070141c8007502d410810b41074150001c910691000104154118130002c8d00b04181701c0c851080c2c1d207407010100c1d4965102205c403540f05040c0d4180004280701604078005622b1101c2c09180105802c01d002d005603400c000047c4001900101340c02d602450301203481100079840e690600c40c071030141003640704a600b40b0300501c504a0ba038103945c83c240b0255030883c1c58050144141040d15005100356001210560b401074a851f4500f03210038807048900b43d041111212031490141114101e500c0a41c02403185a016440c81030003a0989181c1a2200e0066041d12100042c500e120180603206540380c2d083d00c42c0c0f07420104010384c200c403181c000324120030501100e42d40c1c8000c001c4840420007842d01c48100740d1003441214241c41600c26480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 610566654 1250 610565404 610565411
    0xb07110105131119030c061701090516030c030609021c110f0a0c030e04060801020904060819240203070c140316080304031107080f1504020307120c0b03010311120c060f0a020c04 78
    0x1f5090f640072170344a815400c242007500c0c0c03990362285141d041d12000c0c1d80d00d4280310f42403480001040d1003580103210544081c41c0224003280d9800c2000201e03488009806101030291003540042c010900440444c0d00c4c05032070702031a105894800211901490a05400b0045a12054010b040c07040e403a084080340300420800c00540d80e9007016000394060b0408074000e5003070070300004040001041c600c8012110f10a02e8454944c19a660b881d82206441000581040202c428403480c0540c80070303610880c1d05032505106202039080804042c0d000031602001d030790040014080b1410316142c022a05544003000300d40340c0e2900d1800740c4000c404818034218602c0b1380c000c00181c5481c00924585170303848a50944102241000707009000d03031002c035000381d00359020f80710402c03201c18030310800c8104601505a03060130035120400340003103901c01c0c1e1081d54500d9160400e88494907014881c0c1c18907a200d040100100b603021070102e86603014003050000170741c1001c600800d480340240401100b1f003c0003081017 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 610567904 1250 610566654 610566659
    0xd0c05090a0501032105041e09060303110714130b1f08010609050315180a17040e090303070e040b270708160804020d0f0b07110105131119030c 63
    0x10802001c0c244800d50f920300c401d820b42d00d86400700170140c84164059550345450141080c100481010300d21159080c2d54404540000d06c5030300500c42c030303001f462296071094842c00240d00e103186091515041034828058103140e5800941c0c4a0917030180c103812050000c544803842000082040001041e20042c204c03c00b201d13016560b6201c01028166811038490f100c80a0700c540078155140b10380c00c4000801e40803d070210320250411102c2140e658034010859099949554500c40c8440c40241c04c0d0450790004181403110391003a409050344012400f000350700f103181c80c840043c05008602c2c41c850245507140c18130191a101c0ca02c10703040724044071002c2c0303d43e40607040080c2d086c548211a2240007034180004a0780941a600741e00c03d04c001c4aa945401ca510341d9002c101c0420300d4504125041d888800c0544001402c10094521072017454440c02811380d401100b01d42914002469103403405d1210070300d60700148420302615900e450a44010080da407010050704400b61084e0800707010f4400b4139200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 610569154 1250 610567904 610567921
    0xa170a11033c0a0b0f031005070e1f0e01050f130306050c03060108040311070e13020102070503062202030f030705030703090905190213180b030601080d09050d0c0509 73
    0x915100155005801c1c01d095484081d03865103a49080055640b000000c01140e00d4040e10b800070445602c3c001d01032100d0140e018002843c10070641d100d4078003141c0720b108000300f603500411609001d030390654410802d803070114500003040d4101a071400c144842403c800c03426900c110180c80b160300c49101c0e0581e840070016040901c4141c80e11003102c14900b0034001400030400d02c0c00b601d002c3c86041e1900846d9072690b83d816034000e1503a80e03003e14540b2404000042482100c002280150b04822a041544c6214000242494129081140203501440c180500c00601d91444285032203030a00d9000840b016200103410712818250b07030703140d91001203052414010040001e001492090710f82ca4030316a542d4500000365002140c2001e04528440740c07200c600310190f0000c103000c0c407400040d01c0310b40e521000e09002544d00c51201800d295a14564020507080801c0210701400420004240003001d03404000c04111150088a00440c64401c095040080d518900d201620b0001e103641c0039460316511 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 610570404 1250 610569154 610569181
    0x1c15110d02091507110114190306140103091101050d060305030d0b090a1b1110090312150e0114030708060705030411060309061501200303010311060a170a1103 70
    0x202c0c0c074850500380121048912180e411114059442040041c1d0391049400550324010402c000e800724100400c4510901514255040180c8250361000103155042086842448030501850307414180342080c014081610070702c030422088001d180c281c1c0d6844c81d00d222140a80f40560004010388400725041042012542025004100035507001c4919501c0d00c0d111070940d1881042c01d461003100c0d8081c00e85c0c0030f11400075007404491300c0003162103032481c0034882c50450f10368090503070005200340703940400340a141c0111000c03450421800030807107042c08101c030701441061081840d01c40d0401d81c44c0010b038409010b172400524210054480340d280440018200ea4000c40c0c08a640c3c0d0280c0d02201245d00d451700550340626290401814581e54005130740a007400d42904c0707181408804100d01620850882c034400300c1100510107180c40b54514a0041c034011072841e1428031580b800c0c03080c410000c2d8056401c041c8800c405043d6602038494408038002004000c4445444103800000c01040700ca00030b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 610571654 1250 610570404 610570417
    0x100302130b121b0d0609050a0b040212010e1203180601181b0c110301020c190209130b040b0c0f07120206060a1d040c08060f01080c1c15110d02 63
    0x840245490001030080d64581000000e403640806810003107010f60f060460004141a01c900300004400b0000c0c1c40d8286880c0101ca0100c5050043d40c0400c400c50510f441c58040603000d05001b40002e031039000b02c2d0783d1212020307000285c0800000c0001809103800c07046520040c5098000da4055503120441d00381200003040c000350185042408204003024021511680780b01d1696603444114015030703035110003038440c1601550564084c0a6040c807a8001e00a40c001d60003150b00012a40308a841031182c1d804000f0100c8035040b12908942001c6030342030b94140d41c000d03440b6190010726a9400d0700307000c01c1c1c0181d444a011003100070542604005030030700c0001c014200f6400b1034815540d40c800300401d40c5118080c03203240c00c150f44000c1a00e45c0c4040e44003078001d0f225504200e01c03591905005445d0840c102d8513954800500401007128138070910159454107000e4442500d0100702c0000c08280304a6140d0041c13094104140706074061145030b004014540401c607982d0394641140c10f4103800b940120303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 610572904 1250 610571654 610571659
    0x1003110628020f03130510021011040311030105060d0308070c1704090e070b04140111010507080115030b010c0b07030e100c030c051c02070327090605010e09010e100302130b 76
    0xb0301c2511103880002054503d51681710f60200c061504000c280b0040c1884248002c0561044010960f0304112074080d44c569078941a00b51520340c0c0c03560410000c810155030040b8000e0b4500300502ca1643c6401d28089012038060911031031b00e44581c80700300c895000c001805081100e505401018041e001c000920440d6199072007404000c1d0450f100c41c0c3c4070803040c80703143d5038103004010801c084400a1901095500141050040d00d03004100c1c03207003510350460319072001620341c800600230940c004a04072041d0409113002c12410041000203080351144040180c19900204000b400341c0d07110380c002c1001c641011040e100510b68030503900703020780500a450340100e400c104800800b503104105450211031071420020701903d5144117040254415034040d410802080b19017000c580300b000e8885010003c0507140c085481ca4448407038100c80031078001904221000844817840d564015009054070513200a440a40d210248003402a0007a0f0740001c1d0010306000c0002c0d0480350641c001c42c40e0325000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 610574154 1250 610572904 610572913
    0x306090b071d0f130f09060e070605090402090a09020c0f1903050906070501060503070f0f0b03011202040506040b030a0305130f030305030f34030c08100311062802 72
    0x11084240c4121902c2d0116400e0a05481c5800503203241c40751100814400c0504000f0039240ca1005035400d4a95901c46001801c1d1030f12242c000b080b0841c41010200070410026261315424694020098420b4944051040d5004110f008407581c40c68140d80c0100040d110442d601c9145048030350311081c400812407414010b00312404940c0301d10b0030007810425815035541e85824080c10400045030003c1d4010350b1599030f580d0010a40361002c221010107441c080c110308500c3d501c2d082030480380482541042050320014401000410b06524030f644105504681c0441c090707456101080051200440090b8140308081c5c000f021300d900300740145140708089a003045902d0301c840507009213a1041c44001d000401c1003001601903140c0e404082c5c0c0115140c41460305100c0c442d800c0e0340c824000080c2801c603099000c4900820704e03415106040c125038090805113003514102c0c0002182088505c40903040c0e410540310038250b641d07000c04841c0418806101c0182100241034020000d04204c104600940309 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 610575404 1250 610574154 610574161
    0x215010b040807060309050f0d020f0d032702011403010f030b0603010624110a031d030c0f06070f1a19290f0a0905091002250c0f0306090b 61
    0x4080c01c0303a050b00c001c07030002c01c03025190030710407070041c1074284041e00e80b0b01039000005801034041c000d0010514660f0700824514501e480350b24100002c803c0c01200b07061405001445901c00008100ca14584007161030101c0655400180c8581e0034400480c100001d000002044c0812024840c2e03081e00d004400700e1003941d440800307260894440e03002d1001c001c8000b810252003816402d075204030912207442d0008000c0400d400303103880c1c25050300084000c103c910000844c11010000384003164602140240f0040f2203500120700403070304080020b405248001089814401c3c44070b80c01d0707000d0781c1c080c42980100c0c10f00384544041950907074001d5800c4005900140f9186004d0180d000640c1090f00d07a0284581803074490301d2000c46a4409541101590046030099610111602c00920a03072001103420310b4504e4100e81031540ca001c8090916105001120040700b001c43d1240305640c0d40740c1000c512000e141001c0382d52000991003507090044c01c84d4040304212071a0031440d501403051824004546 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 610576654 1250 610575404 610575419
    0x51806040509010902030c0d06030506220c090c020f0313060207083903060a051803040b03010b0904020c0f160504060e0f04140a0b04050d03140106032406021501 71
    0x8034611910754003815072001444010a2940150341011204694074506220505000103403034860340151059003010041226411060103881a80c0304c4006450610714010b0b0303140b040f9400c4034002d4000c0a581d0720030b14103d081c002c00c01010300328035020440e6100d0300202c00750281440c250041c403005000310880020600c1001030410800c500ea12030204000c6071441009020003030380c00c0c03682c5100d03a000b079161180752414420700e40204181040031400c0d290203c0040c0b9401082d2445a4555000300000c01003111040240d1341520b00d1850302d5950b848003040010040c0c0203000c81035409000c2d40029000c1083c001171040038282049809000140e034480401c411070f0014850302080c80703c840002840d80707011010300b44e03009100c0c0c070903408014140803580345083e994590407103017404500709000c2840402c02c0080e502c0c80070b914040c4441c0421004d04842c5841c18482c1d90145070300c480010386c03418860100d05e07046c19140051900b00720f030307611802540c411142c000300403242c0c000400442d009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 610577904 1250 610576654 610576657
    0x30506160302040e010b0a0203071a040501110f0d20040b0a0e0303090f01080a2c25060c0c090504080d05060a0608010515090d0b011a03071b0f0c06051806 68
    0x80b03c3c4501d004c00680c2c6040c01c41203031680201e44600443c04100710660005100c49901c8049011650200240d0f10300b501d450790840d25408524100b01c2d005100f90600c112070b081c200c508089242c03801107074038070f488400040b80403505c0191a111480110f000f040401040010f000709041c0c075134407142504501401e050b2a4410f03001075540151613403032004495400343d00c00d650030840c4402d00044500c14001d5490560700c2d910002c00c5000685644600140e500708140b10403151078440002aa0040540d800207003203441c0b0603003050044440c114001d0150490240c001411080000c4c0000c0c0b40a00e0041440c0d80100e080620840c5420301140185c2008070345d60090364a03584840b03142c0d900b07000820000f80703005484004400170820214900d03464443e01114198421441c044955040248400104a140060b848000f009000700540c680c3d20008815044003c0042010382c08902d04282c8890305040c0000f500348060031100081480d0b200006100003602000c0208a00c103c007820003096 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 610579154 1250 610577904 610577909
    0x9050318090a060f0608041505010f1404020906030417071208100806101a09130b01020106120f06091703040309050102120705060610030905250b280e0a03050616030204 74
    0x501412104c14040c2c00c1c0070355495034110340521312004240c0e281c81030f13001c10380e00c00341c000b84400e440011040080143d146130014a8110454042d4200710102c5d012600c07601001f44050612071301d42c441e051074840000c088403800d6412507a40304440e01110006070100005032040440f21101c0d80c07000031001408116a070141084200407034180b40b80865191154802c002100f003201d00400003030040c1c2d903c0c500181490300c4000f0b80070601003400302c0060b08544140d448001d1b141c003201403240c005810001003030070541d8826400200c800341410111100000340e800080c00c16000030030300c000d0582000501b401c8420980c04c031280c9c0750340d00305250b00c14060810003c01c190b008602180c0285801040d0850341d801c3c920300041c1c011026180e844c90300032180521004020f0b61311030b0038103154101c00100003074004800011700d821860f51034503081800580b0180c80b42100d48001500c0144107001d200310500c1c1c01001c1141043d220701f059074031100d00f0345581405c1d000350481a0030a60003402510304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 610580404 1250 610579154 610579169
    0x1b01050a0c0203010605180a050708040f0803040c090203010e0a0e030a050909090c0613060f050a0f0e0103060905191503020f01050a05071707050c030f1f09050318090a06 75
    0x300a601003003940c2250800104903815502c0790400b0403980c581c003285000061524240a41c0d40c20b15910800850300090040c204110405d410000413960b8402011240380d440300e20f80b40da80e915810507a4017424144c109005190001000140310f80c4c01e985014060500041b0410642c1001102c0694034032504842c0f40100c0d40601040e8403504d040300a003a404181c0324291502040f095000039001d50225080080300f00e81c00806008140d44401da002c0300202c1c50034290700d008203107103016052134202c10107102000450300b003000059100c1d03002000201040b400500150a043d40302e0030641403004da10304040d03803800105000850614801c0ca00312600a0941e80304000070341c00468007a03204002c03c1d418050f00300503000c00125482d13103000e0160807980c00203458066074035115003480b0700320311600d00c60340c00a42d44000a00b000b10f40c43c08242142c0c05601686c83c1d0b18101e14010b482c0007107000c1c1c182e01020802c0360003540d00484207804038004840c50000b60b035890a6540848156004519 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 610581654 1250 610580404 610580407
    0x6202e05151f02100c09030c0806011212020f0f030903190b0604020c0a0b090601060e010314060913080409020405090105032b2c030d1b06091103030d0e1b0105 70
    0x1007044182c8505000060818819604c2c4076442080c0c06050b0f030584500400050011a41041807104000c0484050040e9201800d000e502d01a0328008017098036802408420800b141000514020001c14158056103010b9030103601011a000d6142d0300b00302143d60003070007441b5180391846422090181029405551088540c0321581404025088240132455621480c087d0f01c011071229405c00307100d80a108020030703540d81002d0009001176680c1802506050070f12142081e150304800440303500c0407043d5000c0743d10b0394610080d04403040350480e01a1884800060124100301c182c2c0080c030940b0002d941101d0903076665002d15540d1840c00c10034000901050440c00361540c04162005904400c1d1314111100401603056001400071400a0914480d903040b85801c0506007800800c220320018101045040c000c21180340d198104600002c00e059500d03842442002603010142d4039846019044035211300c070742c0e6840c00050607006c45e02003061003141040c00c03041c4030541340e502d50b0600696845 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 610582904 1250 610581654 610581679
    0x90602121605011107060218040506211f0204080c0a051005090409020a060e0301050a0c0903030503040c080601180f0605060d020306030c360106202e0515 68
    0x107842a03800c0e04003181d0039500c0740a82c10150321800c0207003035818001e04006070f545449422142d00c100c0d0032007510340250308003001c20001d036039140310141d43d404090f0000040303c2042c0050038107001c0c0134015a01030594044001044000c0ca6001c6e0058811030301c103c41c0510181e42c00c0048a0900c0d204250b40424464000310b9020310881c0941500d14010f40301054025450780010303012680c9401103030004c0c100e5034420105150900440d90040000740042001014000c001803841c040340c00044c0c107100c000404101000103403144000102038840a070348465131143c035120305403100350406990381400d01420915101d498801c060407104000d0113145004e00c0e00711244080d400c01055254180542c2201a020f0388400408400b214004042c4440806546058614031800400349000290350000107100b81038000c00a4400c14407441e0594540903040c1c4492031814440c03007100c81102c1e0710300b80240341c1d2203542400b15101404000040c07156655034130800e50403681d600781c0a9445603130708151 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 610584154 1250 610582904 610582927
    0x307080a0c02100314070905030c0d051203041a09011406100302121f09050c03060d0804030c080307020108010b1206040209040b0312090405010f0b0702211c09060212 73
    0x101040c00940c18101d5000304160005102c080401c082e1a000c80d480b140003040884002580782c0d480b40e46405d20f164030714288008603a980c0d02d282115030050038003040d510300f4803000b000a00d030b81100320046240d880c54135243c0703c2e6582e00c41c1071140c01100c410101081c1001c9041c060383c5c2c640719000308004e2a5658600400c211903904c110000107055003042030090641c180310103184142120703254110134071010200c90b24103850f150304c807190403850401400307441e55005007103a403c0a0106c42e03030340240646050103011840b859200410b0000c80520000302c404021000d018028001d03210780700940c0e42d80403103c03a1403084248021020300d4080004000e498250f01500504001403c0040c040300c020000c60b1510708862101e01c444e10011403811040c1c036085c0105405400c2e0866450320030381c904003c0c8030443c010000000d1107450658089800074800108503030101181d03e04039101030503203203508184078100d415500c00080d00d041010030301c20f000082c1e03039000c140700c084101e10b00001c500c207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 610585404 1250 610584154 610584157
    0x60503090d030506011103030906150f0a030f0201050f0a0c0203060a180240150e0a050c070807030503040302010f0e1509030d02030108160509040f060b0307090e210309030708 77
    0x50139060264200003051501c8040000d18454807800001f804981401d0072015a83c9811504491080204130000c6503161210305214003280d50201d100da944908078070041c0d4050040c402030f0403000c5800726200d0302d0305034130800d040019402039003610780e00c2d2200b0041e2000d0355603020300304044000140b446e6005003011180b80d003811002e82440d07142d024008181819003c80d220500c228120000078861101455110700d03a0103e0138280c00f40b6269261454003032005a0041a528100d550303070001036884d44010044452250344243c0580d982c1055203005030181d042990180c006619002000c0d44035503441c4121b1552000b0003000340061054440003080d4000011700214440c0002d120351035400c141800910f01a1041c0809444014484035500d5003207411036105522030b89070398052101180c400066511542c0c1c01c0300c0c1c04142d01c0300d800c0200780390910aa10800c080c83c5882101c40d07602d0b501003004541d44840b50845141a82c100030750440d81d00050b06d03062943c1d0802c1102c140016440380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 610586654 1250 610585404 610585411
    0x91b060f051216030e07090e07050405070e150706050f0a14040507051002010608010c110609120f0f07020307030c1403030c060609040c031205040f0602030c070302011412150406060503090d0305 85
    0x190103d41c171081c165a00b400c1019652010a07559261801c0040c5940e040c840c0c1400741c982030742c0400030f40c540144014002d0f80c2c5200024000e841001003040c0c0b4103480d0003154101a0041814059410100161503950004680f1074107030b10b152112890f84100100403081c000c0d034000008002d4a07081c80200102608900b0310344080d50750301d00b4001a180740a00131410807205e240c0720031664249108242d03040c40c100420450140d0494032200e40c007008400c090f43d4824082c9405c2584603c40314032000800d100b04a00030390f16210b113100010411007502a03070410760b00d14940c0c94070101d54030000d00d43c2d2801402003038405034000c5070009101e42010101c20781e20900480d80403500380d0741ca44610303080000402002002480000d828417526039420000401400340d80300446c038001d0002d4100d6140c4880340402810080e421007001e180106c00801d0702c41c0540d01c1401c841041c209406504040308030505840c6c021828540001134943c010b0b001c4ea0b20444110001d0890001e80f00c008600901009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 610587904 1250 610586654 610586657
    0x71701061206050406080304030203010b010c1e06021b06061002030406080402062203080711090601053702011505030606061207030f05130606081f0e01091b060f051216 74
    0x10b00c0006119550b13802500c000301600c02c0515039640c2940140340c06c1d00d0030703408203606204100300361000084014402181c0315140d400710a140d03817070900e80034000c1c0c45000d8800c0b07600204a0b50014000c1c80100c3c980303018540c1101c5403010481e076140266260700807071244d44003142c4154006405814424010b01c01c0301600051028101c482e0001f40000d880950000e03034000c0c00104002d000c00010801400303464504a50700906031903c500000d10302c6c460120a41310620070100c02880b80c043d071800002e1a665200200d450040070500002d00804600841c1c00e1a42c000c81000140e81c1000716070503004641c0902000d01e803987d84040d0500c0540040e06450806989903010354501a6038450700e401147c608070080d0380401c05051107400d403407003500184480c0e0031400205072130724012910204055120403020980c400c90081d598010400418050040c403802c0e07801c92400325a02e0300d04c0080e1649a09c0798203e200c0803e400301da0038000e510301e281808242c18045488240813825580c42080305 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 610589154 1250 610587904 610587911
    0xb1c020d02182e05190e01060c20090408090102100e0c01090e0f01261b0301050603070b18011107080105090f0c01120b210718110703030b1801030302060f0717010612 73
    0x594000900344a0260712408c0003580c40b20041041200c0d980c1c1d040d4031540e07400410f803010200800002d8207210090b00040245100181d400140d90090000b03041404903241c0420107070f40f2100f040b58490401046c0140003c2d1103240116485038030140c128028512407820b0580750b8200380d081101c03035602c022000212480940e588149200800440111a803140b0001e020045001c2c00e1500b507443c040d0045210341c22443c41403018811140a5070910f02e1205e640201d581000303401610b034075416145d10130755802007500c0807a0405054100c40d0007094010120741c1c00c1840713848500d85031507155104d036002405c003000e81c54907841280c00030140900c0050030001480041031035180c0c800101100c2c105240c000a10400641c0d081508200003040904014408000340b0302040d43c1e41d209071880101810b90b600d401a038035407240d020347ca00d03440441641044650b181c0c00c01030740e5208200c8030480c0d4461150b0015042c00c1c402d1034040c2c140b041c40504500d8503420600113461000d440c80403480160394 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 610590404 1250 610589154 610589159
    0x6030c040623280611011a15070b271605151c0603050105070e09041202030408030d060e0612060a27060f0c030b1c020d02182e0519 58
    0x18000185031030741c00020b03e121002e8640240640f0601807418200c156900d00030307001400301010144042c0400044815203503620341c51040388150b01403c01e010308604459401c01204240c003004c00d4116820980c043c4040900d000032482d610040703855201f041d241c3c0c5403401c0141e414111500c8410000c1031940f14140100c0c4090030120203c8a0301c1e0001b546d0b1100c3e0200107206007881200e400003000c0c81d00329122a4840003040101002038002000b6550558201e10514824001e84000e03200d1038050b40c0d541c8040f00c2101c4007a0626005d403925400b2240b012980d2481c103540034103900c0b15480050501c5990b0114914001e000e06080c8001d90034403500303000b07601c240c4000da05000521400000420607441d000d00000c543d42264590203161900403100d01d00e40e200340951707c10540040d8109030622051003c5078084400d84d800a410030850340320044603034004400a03203c2c0140b91401e0301449400c11050340b0000505045d0001503003c164240010b050418016030340104480640c1032859 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 610591654 1250 610590404 610590439
    0x1030204090e0c120d050f0c01090602040b070b0708010302090f130b0901020a031802062b050a0b010305070806010e04090c03080307030c090801060807150e0a0e06030c040623 77
    0x8211014801e5140c020078443c004904c2c2452660110504a4004040e001d990450141c802d200303000c05110842000700303080c14441c81c00d422465881e90302c0740782991225030f45d46050381140c0140c01c00301c8942801c0ca00080000b48541001c60480e80c004003d01c500d5212a0802600d912010b01000c0040740b40202190110301c01c0c1401074000d8a801e4001030361860141402004c48840c6a441d408402007101c9400250307031401f0907204040d0006d9140512401300020848010240100300ea020b14100400c10a00305520ba000c1810400d00383c83c00d1000c1d41d41d0351412200c0d41802c68a443c080b819018250b849410642d10080340c0034465201240001d881c1e480d44101504225018400a525034000803080c681c4050104020121000207002d003d052104080d110081030003002c0d50180740d415410304103132160b002001c100c1e6014107011901c076100d08041c41c2252040b100716019101c0c0150801d40b906051160038100c0d110103c1014036a0030f603055000004000c60b6a00343d000360610105000342 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 610592904 1250 610591654 610591661
    0x4020d11030d050c190f12020f070906060905010f0c14030c06040501020c0f030a1202090a12030f02011112011a0c0f010618051501082e030b0105100f0e0103020409 72
    0x1c02c0c60b8440355258850325401d00c0c908402000c05001e401206900d120003c0c0308100d4140d00550710903c0c4030607441e091032080345041c804070050007040c4a51440002c0d00d030384c0c0b6844031041d0382c0305947c0c0603030305da840b100103403047c0d18801c00e03510004013030342c2030307940402c50026100b24450340d40070a0b0b905d0500e410000a15024003900c06980c6658009100e41c508135040042131400014036001c0d40c180004041c000e440d20600c00101c600c0d9980005030f425031030b942c100d50200640403000b0503c0c43d1102d81d0400920036029102c01001540c40c1104841d00030b01c495044d1703403515000e80208036290307080100c8001110303800c801980791408140100b04018001b07103c048241818035000240b441c3c0341501c180303a00e114040d6980c0005152600740448400904d490340c01c0c0001c03e00b02032025444030101202441c5034028044500d204080704642401c0c26080000e0440303020b0340140c01aa40c80c2c40c00c1101d902d0910494030b0200f8002c100021102f070203040f64648061050400500346981c0d104018140e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 610594154 1250 610592904 610592923
    0x32a0406080f070e030d0f0201320c160f26120f04022808032214030c010f120c0f12140c1315080405070905070804020d1103 55
    0x85810201004400c44203020050f80c000414507111401a59080c0402e40311819140c02c40c2c00c0200a040b1180799500035040900c2042c0361402c407200311050b43c641c101c52445803401500000d400303040828079848034001581c0d40000b50780e400d140000e0b01551440d100d44607685c41213401c00300408024112120001411382500c41008078103a0701c1030f82810f0341c020714200500d54002118000d05100140e00d40c00c0390a81c1100386460240c114046c0f00381c100c030201029a2000c04e00b48000100092440c080c00840d085092108061103030f41e5440d115599802d01c82c064501b50190f11500d02d00d249580300381841e082d11995414581d00b00c000d02e0350960107950512480b0070125510a01075101c1c00c3d44003a00d050b902a280d401003040c00d0300c0c802200701480c400ba12201c114080440c00c0001030f507510b001440242a03d12a500b816048030780003900300d040803034040c1c8a0b40104600091003405a0082c0da2081241e5a00c80754284d80d26030030450b50080780b20058603500081a080d010540701040741448 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 610595404 1250 610594154 610594157
    0xc05040606020c09070f0c06050c0d0903110706020a261c0227182e0e310c080f0a11030c06030a0f14040813090204060203032a0406 58
    0x1040403103040c400c0136440948264104403030001c450522a9004112403001c6034040340c007189a444402504445008800109844610b840c4000301015001044540000e14020544000302d0752418140d03162070201a010340f426291101000312a0700384030400b2856110000041d0810300c1c80361411074030f40344030302702c0020aa82c00110001c240c0c100b52605000011811004213a118a00340442e0204482c0b400b4040041c0418021400442d01480d1102601c0041c034024180c01200f031341d0150503039420703208010300f426001d004241c0c10403c00009002e01d0525403a0301c41000111150b011030300755145030a40f02140c4801e8041002e02e0103125900d44042620000c041c2d0500c1402e00d0326104202504103072203a40200501d480c603403100002d0369845035012000140101e400f4a14401500155214001396200541040f0402510102030a080402c4070fa00310382841d10b8501d4081248120b00505025a005100280c200b59040520121071020403e100412840301c2c2d01085094109420810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 610596654 1250 610595404 610595413
    0x40e040b0a09050604060e190312051513020403021804030207030f1b030b061203161502070c0305030c010e0601050f0603091e03071403040b0412051507030b040b011701050103090c0504060602 84
    0x84e407d00041240132201e01c858442000183d1003698081d01040390686540700c11078882d000204554541040170b225030304054440c0c04400700c002c055000a6000c2c0c002240f00d0144201240b00c00442d540c0c88510031685500101031040c110780b06c800340540c0f59001103400c581191035440fa0769050f5100c50000358400d20100000d400d040701080b041100350f410b1104c0f642e10a010300740990a91114052900b44c000350404001c0f5000282000a0700c549203020f4070700c021000d40081007080c00030040c05040c22140080048851a46100791540c400784283d81e0310003c2c6043c6650745281860041d500141000100c81c01c104c0424102d00c0c14480e0050b2081d4190004141c031018040b60304501764805460f031018520345030030805080c0250180c1d024000c00552008541810003001300b0002990110341d841180c500e02d01804010040c0801e4254140035506000d450003a550081c410006240520340e030b03070050707682003a0044004241d1000d0507226900c2d64240082d054070b4920035040038000303940c080c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 610597904 1250 610596654 610596671
    0xb060a0804020103180c06030f0902030114092a04020904022115010206090d2006090d0318050a0209060402041a0a030c050f030a0218190812040e040b0a0905060406 72
    0x50210b0b03401c00c152182100c0c07003440000000702c46d5040f0905031b9a0380d080000302c052110104400810003810025059840c00d1090141281c681d15981d10501688040b02d04a0b107604c83e94004406179a54820410040811900017034a859000741c440c0d00c1024100508201078511501e062401044190a00810b1002031014215003000d0403401d0803000c2c00200501d04183e001c0c0340e075500100c5041c2d020800f00c48950000c00700007030388101a2031602c4003101c1c21030510613082c035207500c20004c0440100e4070700300100034124403514031003d0310350300070018210890b855028898010350060041e80d000b9420480402c461100107a21090500c03c0386103151101000c40c0003030b0440b14011241c40c18410103000381d1142000340000c495101c52406405038071901071010042c110001c540c0401d1307000318450610034294520440880450708414210f42c0e04115001804a10340300304d000318090850380400150104040451403504519824000290300403691241d40c1856415203040701c0160f02e50001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 610599154 1250 610597904 610597907
    0xd060f090b0a020a020c0d0812070504090b1e0120031314010306030210050901230c070608070c02090c0f030712051f180b03010c030905060a0204030201090302130b060a08040201 78
    0x7039a80480525021441d082c0b07030340740186d60b80107545a641e11070b08440000004008204080d40e9104d0080200c5082500b0020801703043c5030018001d0244081c5032822a81c21450043c48140d4501003140355101c2d044140c4004494070303a1007a941882c50b40104070a58000307032040000b0040c46801d62080412603003010484440803402034045410541030800c02d1015030781d01d01404c4001c4e03415080150b41e5040400050350340801405041c107101f40b2116603101d07500851001009403030b1003c802c2e1400c154940d0415113080304140e5021002035404040760b070060404000329904207215042c80c1d030130060031001c039002e2030b84219918000100101401c050440301030050305e4202444001c02030141d00c0e400b100c141e02e100036228200160b80c00c45a40040380103594001061480042d0080c00b1400004c103002d8054910094215524404c81c000038216070881d10a0703805995050f0748217024907195808001c1c03205524a441a121350b03442060541580d100030041206141c01e4a40d10b1142c40c1c00d000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 610600404 1250 610599154 610599173
    0xb0105041103010b0705160f0e060409030203160201090e0709060908010903020d260408031006020c031b1215151f03020309070305030708031015020c06090d060f09 72
    0x10490003241845500298100014240c0381035444006115454282c4c0d4100140b900d150612400c074210b03c40b50b800b0170202948541641a20016040600e1030f840e44010b01c011070b00e00000c0600160420b205880001e501c50809801e031b5401413502d40c0e080c0361a0b07040c6032402181983c2e0301000c190304035405c000c0c0383e421004120040c0001c10080000b00000c0c1c41c0a5164456603010a0420808054a265120503060706d850422040c00d0080c20034030701403400c201c007a441520b0700e89410200b1078002694910028a4901d02c800103800741c1000301001220642c7c0e0701405540c5a8003105e0f0a00ba000f17524020414040c4810451041c0d44150420900949104807047d0116010341a035019513a140c00c0080d85070462030015180c0148d43e5a120304186060ac0707042d0b08020007600002900c282030200c4500a14010b1b070380c0e03001441100b591410840444821345005038090381020110310b15902d000005001e20350000703021001001141d80c0d901080300c080003402252241c0c3c400d05001404a84d40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 610601654 1250 610600404 610600409
    0x41d010501020f070b070305040b0d0c020c060c150702150f0a0c03020304020f21030f0310050102071809080d0606050c0c0303031302130902030307080d0507080f0f060f15070b01 78
    0xc0c088040d00c24150b80e13224495409400c4003030f1400101041050701c07c0741103800403e054216030f07459034035500e007030400381c80e10118040051040d00e422014a01d00312040303415040a0800428688114220302034542da00140840103502458400f40c2c983c0601e00040ca2003481d5501004855140a103400d174100c0d0b14026a400c100f52040c4200001600d641e02e07080c031801012a43c0c4085240c1c0d04031452001c0e04100000314160101050075403640711804050343c0a0401805482201c030703140d4004a80d41c82c660302c614001c081c00782d005804a54555403180412501030705249260100401d0800d095881076405000095400941d4100c1e0940500104c1030440044000e503146080c0788101c1640c4103102c0e00084d204800b00300600218200c154406581250b02800f80c0b501c1d0702c000d040280c103607088003400346001401c12000403c810b111b1030040b0300ca2144000300c14082d07160003002c90700e0b42500030030842c0c0203141c1c80030003081030b500c1441c0c020b0701007c01c5402c02e542d100e00e0328141c0032001c0181e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 610602904 1250 610601654 610601657
    0x7110307030801091a0a0b0a11010b101b0204050f01081006061d01020a060906060305060906160f0e0d081911030d050907091e051311101103041d010501 67
    0x180885000241c0c007950b840e0440da402c1c80c0104003c0326503100c8940c90102901030f650711208462001800703aa02c0c1c80581182d00d81900d80008814101002d070382a152403542c6294881034403101254070b1409206040340720000020100041101540801d080710415034804140c110780d10010400320404100800007144040001e1021701d00d8040040c0080f42c1651350340d81c00144248130304600ea4403c00c4080e03056500301c84107000001d240c0c240b10000705880c2c00183c403540201000155007a01c0005c2160080007410710404952007400c6c8225034031000494681c080154070300452800d0360300d8240178030540740030f440c0082e507034100046032000c1100200000418844070a0301c1241c640380c00701c25240754552090011500303984480a0740d0030700f041c90f080b00602c00d142003001d4102d880348010460f00c1c10300b01d18040006031141d00303003001594401c80008000000090b81240f003418240001c0c402d8a403142006881c13000340481e00e5003150002e81025420420040320440c591903600605401004c01b03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 610604154 1250 610602904 610602907
    0xa030b162705120f07030b1305190c08060c040e150d060516020a0507090f0e0d0c0317131103010f0e160e101a0d18030206060402091e040209030312071103 68
    0x200c413105a00e45115200241210407070100140000b1544221040656800001c0ea80000403105904446400044065075011500840442e10343d800240346c3d40200481c01314079051501c2c2c070602881010b801001d201403901c5010358030301c85440d0500c9908902d803149101280301c1c64040307600e48140c50607804003002c40d4170090740c01001c9400403034100141d5101c49404039901b8242c40c0c0c0c141c090003100c10602440e1141d01c0300d84520a5001a86440c2d862003070703039101c4611a082d0b4417494040c0040e40c601842640b101c01200000b1030052550070f0030300c1c014002040c07464a0500010440e8240d42260405402c0100802c0c0d40c0c7e641c0000d04005061070072122400d509104040c1c010f07140007405420405840c080000c0c004c00d640d40c0039505a69081103003401805483c462208000e45024021005031040d00040340c1103180c0b600035a003164401a1050705030f100000546440022021403594115900704807000a0303441c1813008140c11100640110801c1c10b104200412819800d489000240c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 610605404 1250 610604154 610604173
    0x60d0b091e0d090605132c0109020324010c0803151305010b03060904062a020d0306050f040902060d060b0304030f211e06090c020106050a030b16270512 67
    0x4000d4000400d660043c074005071201040701c85404251800c2d081603440c41c8555107200401c03c481c815038144041c07c4c0041e81e91a0b45c4e10085403099000c155594180c00744180c40154044000d100702000b044014940140510401e41ba8030040ea44151034901c0a54010030030345041d402c00202c0c808009104d2041009198034102070381c0302502001d8507031407107000e0a9021a052101507084400c0c05900c4044061885442400165039480740014803005401036001e6402e019000348038500485202800b00114104000100030040220140403a80306805104400c40c4800600c00d80c800b60030000c0700c03a0340e20700b441d00b0041d01c442c0f60f80751001c042010315068241c0c2c20340300000990320085a0040400c80b5031001030135610341603000910b401013134900346000a4055171a0130130380c000841c0346c00811529844005000c0b1141403804094194044480482c4890704030900014098140d484c02280031324180340d030481d40c41040403011b0070b401d8000c20144464a04010200340102400004214190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 610606654 1250 610605404 610605407
    0x50a051008040f1202010b040c0815011110092613050603100b070f0b0711120c07030c030c1e03051f0f1d070e010815060d0b091e0d 58
    0x5001801400c00c001d900c0441c08001200401c101c1090b4401c0c0b0301000380d040480028001e10b02c060741c451060f81040b80c03152681d401852540d0007030507100c5c0c1c0905100300210054803c3e030031391221140d80340704aa01c04580ea40b85032040380d00e01362041d85885084010800318078020390800c8039103111440e04010001c0c10501411040007150b00950340c081d165030382d8000502c40200264460982c2807000101d100c100404a40510b2450b03104082c40342a60303e40c0142150003c04041103840c0f50741c441c650302c01a1030814806010710340c402c4001c1311041c7d9104e80d2079100c68081e0341e00403605244c0341c0ea02800b055040c003071004c40c0415507501482e003039403464848907030720030910400c1884480750031210320507800e91f60064481c400b80200c060000b0000b045038151182a0050501254001c01b0408034410301c214100c0d504a0310b404009114210034610544580d200280400c3e0b40031950f40f030480001070032500b415110704107050191072802215450504400304414500320b2a40050b0212450b66 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 610607904 1250 610606654 610606669
    0x610060903030c030909050406020903060a1a040b1c050a05010e1207080703090b190908011404021210050705040e06120d030c031d0303071b1a07020102190503010807050a05 76
    0x9a402d880c0c1114480424141614500d80e6034000b0400c0030f01304406c210501c42541c00070000d40310700b0f404451b03213030781c0b20303c801c20441c0d2810344541c07184c170042019503001e850117420051005500420259501e01310f034507101d80f0b03104040c4040340c050708007001c0c0c03a090140a101c0c6241c40010417001c0c00e456594200040414490742c075000f0a08000403902d8018103100b09032800152201d4a40640d507415000000d0201c00c202d20458000a07517250f0011440d014103002c1d07443e5008809109a010351604e130308008550b19240c280424620034100308480e16500c50007418020f030100e403607190340c0d6410128602030135003000303007094080c1041642d05052010001883c40d01c0144901e030001c0c0f5101414411009030280d8076030048000301d035001c03a8010f0349002c00210300892145e01c400d110700722038400c2c04980820068001c0e00d00402400070414000890341610b61000030351000510b0843c2040801103500341208918000500100c01031150380360802084000d0f2400705c4103c00d205140100040301c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 610609154 1250 610607904 610607909
    0x603090c09050a0e060711120f040e040f2a0803090306150402040504111312080a0c080c0615030c0406080316080f041e0b1c0911120f06100609 63
    0x32280d4840024125540f541c0c080f00c0300c844014281ca1182c10b040c540209a10900150604180991581c01407510804000c50b440104050701d9241460301c0c0400344c0e2540c0400800a0300c1c0032040d461350100040b0a908041c0340c102017002840307000082c0c1100250036150300d0304810b0035540100103004140c1e800041c919440400c2506030000078130f006021501038015070b0f1009400c01e0070010194a044542030140c00130b0010103100005040e40c030030b89502e40d940c5504018181050030804405942d101c1c0c02c2c1c602c5030b64003d01000e498040a003030428505001104c5440d881880c1080f4800303a4682480201c0c0030740402c507070034495070b4149994a41c480c4a01c030303e4140d02c1c01515400c0300401c0011420b4800304000b444000b601d40c5d9503100e655645130004400442c901442c07140104103031100000380c0b840880c1c00004944880c0c1c89011250007444c902e80240c3c1c281ca81d4803d1070f04180c4d504003180345004480405490103202d4aa451450941d02908080c0302c940c10050601038070f03900180c070408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 610610404 1250 610609154 610609169
    0xf020f1005030a051303020a1524090b0307063204030501020d1b05040608190507090e0a0212070305041104020301091413050a12141602030d0f020d050c0705120a05070603090c 77
    0x70010030b03903270094000d010f10415515488c11020305c88402c001015110002c40701194410300069a5004c1010740b580760324000c80c0081180582e011214103d40c1c030300d400128004442080c0303850711000b5102d032103030490351044409a4000410b086240c0340d5010310b0720704c2507804000040800c80c14101804901440c00381d02c08010702000002d910000c02d0340a881d84240110041120f0300389000003c0540145028590708040780f000444e19510540c402c88143d80b25044440400342c0b0f03006021005040c001d8015503800d110b04402610b15500c43c801140244849400001c44101520942c1d503180001010021101c10b4240b100c4040345020540351849a8000651442d52401c13580544070540c080c2d00300748403010085842d07040c0c070b1203502950010b175000310201d0b80c2c125022501100c00303005000d5003d0041e004002c450483c607004038007401104900c0402d407034045440300042240c01030b00103a01180c0303612540000f01445800e107c0040074000c02c2c43c05014604868403401d10170f10591240c0364 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 610611510 1106 610610404 610610423
    0xf0607020c01052535043501020304030c1104020a120b01020a0503190e0315040215070506150102010e0115030f020f1005030a051303020a 61
    0x140c010050352058075240c0300f240c0e5403200030385601310044002c0203054510300280e081807100d112035120001140d07500c65000000e860950b684405080c1c8403604000501440e90016600004401251000c10b5420750000c00550402000315520800354404824001007550150450113228003d9554516032002d0034100400c0b03200e170b42162800702d629005100d1840c0d085800034102d806050043d10252452512210b04550207800451403040540c90501e6819810440c0040c806030103030018106004034010b10700e608207000d40040e00c900310030b00020560072850001c54400c0c036800401e075551800c00b192031340c480c1c0d2410381000c0c5c095400c0c58800001c4240502c0f90041d15148080c40d0882d41e45541c60300f40c1d41003d02c4505903084021000c0d01912600c0b9000042c00d0724985a48555581c64400b500e20200c0f41d0141c85248a13202940746000800c0c0d00180300707050181c02c40b5034103 = true := by decide +kernel

theorem cover : BRFrame.Cov 610431654 610611510 := by
  have h0 := BRFrame.cov_init 610431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 610431654 ≤ n) (h2 : n < 610611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
