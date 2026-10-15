-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5357
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:35:59.86899+00:00
-- url     : https://prove2.me/submissions/c370dd62-eb94-4147-9fa4-ca4fcb521c3c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 963309352 ≤ n < 963489208 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 963310602 1250 963309352 963309419
    0x20132c1f030b0906101a0928080a020a09060b040b0a091a19020c0105070b060d08040e0f0c180d020d08030a0f05090604020d120203041a1b0c030601 65
    0x1010402d0302c9030f00520000c1209050040503090103605a03840720040141c50406e13002c00c0e0140409440c403201d0b055480850a103e80000e55440741d01d424510500e940e00c41c5400210784500294a1550034000e45002801584424841c0700b51246805901c43d1000100170030440c00e9049801440004d100d46044c00341d85440e00f84482c1c00c01900e80d00b40080d000c001c5007410901091303a50340070040302e150000b000d5280e90f07840060301078060080040c00d03072030030000011459207803000c000594542c04030b05c0d2561144ca0388507140c0c02c8030040e40c56418500c1e910b00000c50088406048444100d400b88601505204110400c4442e0f061107400702c0e002403404025800244603035000c1c6014141d03044c40402c20310302c1c040c1250103c550007044130300203070f2244092102507112048084245604903c2e0321881e03542c120810383c070794801ca03401084480c2240d481c6002215070203001c2c05000d03280301c054074076500003100346603640c0365941503103589504140f0041155460015040c04c1306440208c110242014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 963311852 1250 963310602 963310613
    0x130513020307171b13080d031a04110702030d2006011a180a06050a120603261204050c090105011817010b0d0f060b060c0c0420132c1f03 60
    0x440c040b030f000c2121394014240074580c014005200201f605107020013400003040103c080014000c04000d01483d80d0f040742259220061040355542c540260071202a00503160340204450200108241c20042c001c0e102c035100305010825604984e661041060369030f00b0152014400e900c5084e0b29a0321140314035081010f5211841c0b24001080c41ea1104c50315042c07045005005081e42500102c9110303d416404d00c001048440820000084c902202400310542d4101c0c112604c104030220760030030f01d050108010400d00251084030352009851030405c5903642d000544a034a03280c1318400581c0341003501406039010035002c1d69954140240045499042e14003c42d100d20611b5400750781d080c510b100301400f4002076009480c1020000e4955a140a800b01c81450310307502110000e5120b40e4070352008002e1002c0341c0050307521250102c400380da0385810700400700c203200b40035114540d0035069501d00c0d00c4021662885803070351845014540816070351103046040741c44a0701c0d03014206039094400003101141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 963313102 1250 963311852 963311857
    0x915121509150303030509030909010308070c08070f0f0e01150f0207050a0e1005120a0308090705060313030201050f090d0e030f0a050312130c030305031308130513020307171b 77
    0x40c40c01c2c0c44050905604004054130720050101e051980104240002d944600c4801c504598201c43d45549074809450000c01201c00380d84441c07880d00c0b4078840414a0709036003070100111442d0416081e02980e4803d07091300d00013800d1081d2038545120800c07110085000c0e070210003819545206440800e6240c90024000c003c0c960401d01c1c80d010054204401c2260600303421010744000c4600c80130010303801c04030756550010594020204090100810306001003040480040c01c0010035441e101d02d04070103a01d5488420040c182c006609010114030b1010007181d41c20301401e00500940381c420340d0158256020300c0c41c400c0035034041c810004c4a020318030082c450011920311413005140c0c0c0c1d00c02d003860716404940280090241c800203042c4400003611190101c02160b91600341181c6a81d100a5400d100c4100810042c020300e00c00603281e54009004008941510703000c0340e45440200071800d60304c080340001c68018021070503114200812140d040c3d840c0e41c1c04403640000240d07030b44110801ca003264 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 963314352 1250 963313102 963313121
    0x201120b0915010306080601080c01051809010b0c01380a09022d0406090603050703180302030a030c0c0f061d010603060c11030a020c0f010e090c0403030915121509 72
    0x2e09807003090403200d40e41030044034003c101c1c3c1030040a245d41050300c0d030341c1c403013071a40b41150512100050075040192581c0d0288042c00d0014480c410540c0c1d101d10140071a8400c0d0f00000e141d5103402580f108030745c000c400c0040d0905103045c400b03081011003020140d480550b00c94056000841c0c030400075807103485000402146c20007816003039841c0d0b44017180b030710b45014141d1031194921040c0f1080c0072865000c107913001220928036012606880b24403080d0002e045e881072046101d02480942002d01d40c000006216a052a07901000703c4507414500710703003007000c400c2d00070401c1c0c0c00b220941d40403c1503a00300280b40d1906c2802c0b004041110050207013140c402c1d5004843c120340318982282c01790f412240100c21302010101a52030007041410013034032030380010701451080303440d200c180110340d00c102e041000411014008142604101908010941107440110700003210008c1c085420544684d800981003550345034600074030f0441000d90080d144540d03291055000c00c41d00007a05010500030409603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 963315602 1250 963314352 963314371
    0x1802070519050c060a0f052802060411030109031d1903140606010c03050d050405241801090503070b0c0f07030e030f060121020a0f0807210209040201120b09 69
    0x56201c510301a030400107480d4481d031056000303000c3d040308981c000200600390304040c608242d035400b070480744080f40c048400c0c960300c600981c0745d10118910f4000514078061070096078031741d400114030000c15080e1501c0da08002d00042030b030710710801d41480c000610383c601d50005241466000d42c6242e01c2100800581c4280e07800e0000051070350501c003081c400680c010300c0078600a000806143c401800501c942c122004010b03548200041c284981407148003a961201c0c0c10b680d28200c5880301a0754482c1003601c030320420604110307485006100510030000c0740c0b54080040e50a14006d41c03105001c0817001440d090b00503000b08503844007089032400800b0720511907110041d00d138076208141441e0580d481804040d0381d10120051203007050b044071a0105042d44107014800c420306d0300c04600150302c20fa03c6014164441321000c40c4a0030040b81c0380e41664080840141c2c4440c006400d8169440c01510103504a2403480115016500c20202890380d5210b5260101c0c25640d100c01044090500b00d4883d40c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 963316852 1250 963315602 963315643
    0x503030702222c0d1d0109091505030c0d0209180a050709091a0105030318060f0301030308040224040b030a0e0d0513080f03181912060e0d0918020705 66
    0x404038902c941a030f81050b40d4800070950404102c3e00030f40b10481e5500e880000b40101c03004220103030700c10358120700a000741400c107001048520b0b000303030382400e070a0095a110b801104080c4d222810861822040030b50020040000740d2a02596500141c00e03084e8500200e02a45c013503036004c15010859100100020500040e2003001414032040c2c0c96204035032036080e0054200100306640d40041581c0c8800541d041c2803890b001d540000030f601c2d120391056150b1005010000005150700030100c1403042d1b009a8003840d80f51080d40091104509401c0060403001040c40117116a583d84800b03580e0112291900003003100e40040200c0c50a000c2c00d881d0000686d0000d001014070851400c0403004103117090042c800c41040b80816612406512402c040c0c0c006400d0200960f50303181c0d50f00c030400f43c140c20345071030b1804e40355000e0088000c000c034000d07201d2a08101a03802039000000b41c42c0c00c0361a4a0f520710035202c1c140341c0f1400005c003082c800c5440e03507078092000d1400318006114544004030072201801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 963318102 1250 963316852 963316901
    0x91207140d0c120305100332010f0c080f04110f03010504050120040608010b030c040b030403020109061406090f0910020f091f050d090512030c090415050303070222 72
    0x10310f0070300480c04001054200380070b025480c00d4454803401a40d501004e60454082d80c80c02185141c0d00003074058210803504940c0701d06960040d448813541c0b440c080010b0101401514064414a0007a50300b0541e5500580c000340c003003103e6444a8008200040c0b100d00b50605c840e002900391703442074500f0b0314181d556540b0550005a00d200880411404180b140c0c03d043c03401c40080d1481ca414801c20aa800c00040040c007401180c2040390080d06070184070303548030304250a000f8000c011040b400c8580501d42160002d45415203000707a842200001c0011105a5a8070600c904142001d0080d0243e4420044019903040260001d415842011078a01d5111303d10b840810094660301d1124450a505200b6540003241c0d200c411604102204580412190111310702240340c034504090b81c0c0302e0b1002c04001c0c0703c00c00c60402c00500140078211002c1c4000d003030440440354192400c4c46a00d9050b0300400240005081c04403005003401280d003004030428502111a0701070b106502d410844120103d480035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 963319352 1250 963318102 963318113
    0x607140601081603150e0a1203180f060b0118062d0207150c020307032f0a0611010603060509060603070f08060a0b0d0c030b060315091207140d0c 64
    0x54018580d080080a040850360f03502d507a80002400040c110514041e642c1c0441c03131054001c09124424407040b140740b0105420000c100071a9840d802000904101800380390030050001d9500040d0840c0020311740d4060b039991b50008009130b056103818850034050041c1c114400760b690400818042d100c0d40051070659441d02001c0c4e01d50081c1c9001581c0d80301009580750b50004d6510300f580c41441e18034001a03c803010648a030011001c1c025894841c640000c0100800403160180b40342c2c0c1070021a40301185101a0410100d01d50b60141c1c1104400200b0011039210b480b42c00c4662102c1000007459944a44030304056036412254070040c0d601501c14005a8201081403000405c0d21100c0c9c0d02490741080c01283c2c0b01c180141ca08441c1c16120100807040780c0d41c540903d502c0035880000b01c00003d44c2ca1504c1424508101d5060b1310a0007803101c0800c051031f041c004d01c1d1085c500c03980580003c0001070404036443c1c100450580d4040d120048482d0703101000c124034002840b00d511040e9840000d072606 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 963320602 1250 963319352 963319363
    0x3090c0a23181b0d0606031512020d1104020c0a0c0614210705190c0512040501023c0105041e0b280603081c0b0a0e060609060714 57
    0x99601900301071800003002e42d401034156400501403071243c01c614541400c503c503940103920b00340d0100c5141400000b4041c0d09a44500290b070501c211080c0180c0d614103504522000ca41000394200c08000d0010340094499504205006002040142020b1005810030304d403440c4100100d4032040c003820144100742d0400c0307180752080c0f0b00300b00c0c982c64903040c04114007503180c0254070111458801800b04000b18001d0065071411a084004101d060b208054000e007001398002c400c2c1c0e04c5003d90103c440c26006070504031800c0d2201a0002c0c2090310b00115014074041300840c00c03284c1010351016410344402010b0540d85102d480d1400400c0300d042c103040c28000b01940000e0119662130b0300120000103803041d504254854008680c0901106001c10a41084000b41246c4c5010500e0281c004c0200720034400600601402c0382c8103104540440d22054003280d4240110036804002d5003800c1004a083e540025482040580080d08005800d0081240b50300708000445400c1c00340d8001504800c0704020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 963321852 1250 963320602 963320669
    0x11040302103504050c0a180b04021902150105060408030405120a050307081b012a020106050306090f011b02250e04032c0114071b0b0316020a020f0603090c0a 69
    0x41c05c0030401d00d4900811101c5010520501e00e044c0c890742a400b040e81c49e5419a60542c1e510507051070491020407001b5218140440404c150354603007030021411303040c008184e60585103100029454281084100091851620f00760905c0e03105101645000071410310103072041c184609025900c5502129881d1741002c0c40c0c1001c19540d80c54021480784920071441c00c04000301003401c2e1100307020045031089015041d141c2005400d4812441800b9201c840080c40c428500c460030f008000e1105005106103025030804071440042c4c5c403504000c2c140c0507100c481030485005030380d04030035065629481c0307048041c41202e007500131841000c40344014504402c0524cc50740031000082d100000000b0010380346040d40d46411302c0d101c1d40807840000f0403d9203025044075021504009400d07640c3c1e0b01050300540c0c01252800c80000d5409010703600755000142584505500500c2c141480e0280710a000305a08000c091040318440c24844040300e882e00c014060143c465a40308101030385080160b11405070b110350 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 963323102 1250 963321852 963321859
    0x1e120313060908160302040b010315080705040e0303062b170702010e03031c0f020903010e030705151e1e160f021b091b03130611040302103504050c 65
    0x7140c42d9050440852070313206499040340d0014042c88900012001854000700ca40c403404020078002ca2308060008414044407401c41d000e0280c0320340c40c0849078aa00080d80d00e113400801e954099a030200d44111606520014016040e401d11100c0e12031030f040280d540ca41c00c910314000100e91065582c46002d0361000c00e07003500190b01d80300300c519a100300401980070038014603035035001e88031000581e9011941c2c841d1004000b0f11000c209103071070603100e50008034111100d01c29440d16294001241c104188036080e40074800c005c00803030a42e414000080240900d503260b4201126a07600b248070300f18603001e005240c00203000b45111000103016500802c4080701554090924040c0050702601100c02c011805d0359480540d45036040e81900700c1e4501d041000035036402104120502d80d1540500d41c94a002c2c110510582c0840e043d500030910450001a4000c0050944004201c0c01054049844404c404441d4003050210b46c480c4400e0590786c9141a200310301c5400d00c030510034100702c00150181c1c2107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 963324352 1250 963323102 963323113
    0x50c03030a080609010b18150c03180a091107031b02220c050f0403020d02030a1e0b0705091f09030506070c03180f060f02150a0501080f06061e120313060908 69
    0x40582142c210500343d4101d108603421038602c1084100e003811307200d07544c0241d01129200c4010402000311039641c5032f18a4000c242110f40014000c949015800c00d40c5945483c051600e00f40f6101220a103c082e0f00603003003200b103680d41600603120a80307003114403c404c3c0008500029507a41c20030649180170300940401802f8084001d980307520300c01f20340440394100d0380114105e2140c40030074280740c61391101900d0320000c4c011040004140d01e80c0d412000e44298034410056440c0c80003520f05000d0940d8040e041a4090380c00701070f20040403015824000c050900c5034940c0da49070344507440c000c402c070343e03840c00550340801c04410150464001c1d515078010a48840c81e69003400d213560100700c8103100700010000d1040009001c140240604c035001000c0c0f130f56030180782ca046284040508000c0c41001103d01c90381d500884031541c0071030928011711000f8000c00d4003d5070b07041c101c888038102041c450b51207079200708100e605240c00c000404141000780100020303d4078121010300120081e0b0b0041900741c00c035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 963325602 1250 963324352 963324367
    0x2031f0302092206020a020d17220609020904060b0301140606030a0228020304050924060a0909020c01050708060306012d1503050109061409010b0304050c03030a080609010b 76
    0x6207000035030311482018100c01100f000608089450001a030003419a5200042c64983c180e4003041980e03400403a40ca03469560400e003410749061300c8084541c0c0c2c02d10201c3c0301070701940d00840ba41211407940a00e0001c43c00c0d60442d00003469102040d40c045a40743da4681810385a402c081c050040044480054807035075250007000301e50688802041e05400070360008100c0b521141c103044007118003041112580001c6102107000c0d40e01d03849030040714030503020540010000903851000700d9016212581c0c6049154010040c404240c00c030451010520050080100c0c2640040c070181030324801400011586003410940030b0480c41c405025140640c224000612992110100c8a0a0001944000080c400f80d680300e01046203c2a041480070360a50b480c2001e441c1c0c3d05400140c160382032550100b2071180c2e100000c0110701c2c2c152000940200004004103c2e42d1062800780d9485030085060b00c03d030b28040e030300103429903003d07008100228200409112040c03e02d490440d0260183e810b1003460002d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 963326852 1250 963325602 963325609
    0xa08040308011203021203041e030f021e030702042a0315080c0d0803040201030902091602251809020409051506040513060c0207050a0906060e0d0201050306060d090803070302031f0302 81
    0x595a040905030300010100c0c04000c099005d9003000c089d0004d46089030245464000e02c41110501c0e13410052003a00b11521503200803104440b00103000400561400e0060303828400134005000d034441d01d924a035103414406501c2411a658081200d613400501025007200b001040141c0e900034601503403102040c4041d40d10b4002c3d42140c8550014682c90701c80e50b8500c012405010b00c0c0e500250040088414407140380003042450460502c181c09440011001a02184000f4124200c0b40d40210442a080007101a06415181b8503c002c4101042c2240290041001c3d124901e904a03000e0340400d9141c00b40c0d203400e98103039404c00300407101808141088080c4201403003c034400500104d64600b01810054002c201d920001c0002804925001d907803440841c0040c6110700c103030b03004502580448000d42c5071244001c415154143c49150940c1c4400c000c1c401203410013100d90520b1560748052070b010610407000b951190f11540d40150342c1e450900e550a4081352351844c2003400b10f07240a014001a80d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 963328102 1250 963326852 963326863
    0x906031410050d080c0a150f05060f060a050c0a0c03120207060801050f01030905010c08091b240705100c09170d03110708161b150e12030a0804030801120302 69
    0x1081203038030b4078107001141130140c00e0f403240c164204840c1c840c00720301004001e000320b81898441107c920400c6110302e070a1040c8180c420403282d9a40c8502c03201130030a643e151001c0503001c00c40140c64020f04002004681c0d520300030741403a0030348041c84544410010400241c5a0450703408c00d0780b003e0815145080e02c081c0c1211418000c0900c510344111001c03860743d201c1e41c040d84e43c203074004000b07105594041c03101405000c03058450b40202d6c050703205451030700f40c4a1014400707800000b4080c1200c0d000400032114001c1d03001c401c2d500c5541c1e01004030401040081202ca1010414400d0000e0310001e00c0e800549060b03466409059a01c1c0368172444141e4070000314214002c05840d043c003140081b20b00d80e43c07820b140300b00d1600804150000c1204485085082104101c1900c2002800c080c070240841c50884d9488902c6a01c004d98200600d204081c0d11a0750040f1982c00050300c0ca0001c40355141802d0f0458100840010015a0701800c01c418961301281550040c22414609218043d00d0f8a0007500c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 963329352 1250 963328102 963328109
    0x11d03040902071a0703050a0f0204030218100807080f07061b0f051e060f011409070c0302070509070e0310020915070f050717060a330b0301060906031410 68
    0x207540403c140082c000c0c0034501c00340400d41111541c88520f00824081e000702010341d01000c079203240c424083c1c0410801d10031a42034a400802d01d400007590704828141d14034000302050200200c0c0d03000026210740400690010f8240341000c0c2007244501c4a5081c81d29046a00c40010800100c049034118014a4a04100c25422140c55400600f143c2051071501607205110500280c8805083e068800045400c138003403243c0c4c284490311f90760781e4024a80704c004200195940103102402003100a03000340f6002c00b41c6803281c010b40b0b824076528000101117882c00c691840c042888100010301c00e15042c401144600f120100131424400800085154242c000c03483e82e804100010f445000e0011451403406030943c40403c440c01c054480030030526103084e02840b000b0070303c641c901040740c00e82c0320300074042d905499039400144050154550140c1110100c5100c078407660a02c07000c10203c0783c0c180154003a11041c1c0354004881e240c0b000080446400b200900c0d4404a1030062023120280d440780041207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 963330602 1250 963329352 963329369
    0x31c023411240a17010f0f12030818250e0f04030519120c050c060708090d0e0111010e1b1f0324120303051e1b04030221011d0304 57
    0x20f89040031802d5420044c220101512000c40e500002521070920340900c3c1030707800390301c101c00e43c1941c1c40f51001e0030b8003403140c13004010800040000c1c24450881d05000300c03000f503d070212021400070150001d07411162034500301d00c0c012074000c2484480210081d181e00300070480742c0362010307140a8800620601a095070385101000c1400701402d506e10840140c2d003010dc0c111020002405d080034040c11540c0070b4545d102041c0500e80018400720301070182540b02d5a407480191110b241003110446ea200d80c81c1214038140500c11500d01c452a80900c590310301b10014200800c00c4000808042c2240c9141d9811244120711040300080c80e8900702a000000c884039090214a413082d003440c82100c94000628800082c160044c00034000309035846220031b0710702a031020802074a51036512030740c4030b4100800b45001000c04006c02c001d2908101c0e480c85001c40c4240140c105a100c2c0d0014051500c0b0b002900c2c1403d9103c0340561401c00203108045407840510030710482c3c40084030816460b8081c41c0326aa91 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 963331852 1250 963330602 963330607
    0x30a02060d1401080d020106081f11040905091e030702210a0203150f011a07150608010c0903050606040501120314190f0e0102031c02341124 62
    0x900d048940c00070799041001c0000600d10f5a100c82200740d40c0c90f040505500190b08000c2c002802c2c100200303c0380100c00c601c00803c980c000c42c580010020780050b4542000692040200080c41e140d5440341c80e000d81c207258081c20816487c9440e00003a0b40441b03103910300c9a00200301c260b00680d15580d05040009240c00380040e5410380c1c01500b0300b0f01c90012030107074050181b944400c03002d421840c3d05a1040100f2804c045040c1d0b05c035103450078000c420801c03034007240b0780800024001c20040c0440081e42080b0f6280400c255442e181224251580000c0d05008208441d03812302c1003040500c02c0d40d034001410f9034200705640c0741044081c0070308480007001c1c041c000c080c1440020b02003544201e0b081910582404220780c950104005e0400000f1800840003a29840e040c0b800d81d8030100899950313441d241841908005000000701c001e500c4000110301070a0f010031111104c034880d44400303640b0b0300725840d410352048580c00d04800d8100561049489280d45017a1422051030f00c9200144201010201a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 963333102 1250 963331852 963331867
    0x240d05040f12020f01050f042a1806050306061804171201060905030d08010e0106030b01090306050403020c0901150c030f17010b0a09061409010e0d0b01030803040605090606030a0206 80
    0x41c00c4110314074000d0141031040716803080c0e0907000100c01c1c26024801c402005650b1300d05490b0000c800051f180180413088459048624904800c500040756400c1c01414107029541c818500070140b0f002c00c4124100c0e140d045c104100d16040c0842a4000c2c400d0303c1000902001002c010310f00c0000601c0200208001c0c50b4240034944000c0035aa5424100c0340741150b9541c42e103001034140d03840d9200315032003445241c80c40100d540c85060b140b03040b0f81c00d805040030680d0030500e007a8013424440d920380741040410407000002c01d945006160055020741c01034450850104180005488140c00c40440803d440031000e90840c0d22918188041c0d8040c5000c031640002010300720780441c2281c0d0000151352400700085002d000820061103600026207405160603039070501910084081c056081c0248810300408001d5402000c40c1c518004005201090420b100da88801030725400307070000d46007014040100000c00c5418444c854001160394000c1103039251000002e48d5803d098040240100720204646 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 963334352 1250 963333102 963333113
    0x23150f0d0f0f08070503310608070c0b0a1a06070807080d0e011b031a01140a0311030907091503050a03031e020f03150907050f070519060902240d0504 66
    0x44880e0f204039020360b1103640e41441303940c2c0c0d002440000710300c0d081d0f04540b0103100704400c040d6000500901007050091300d02041546c00d0240140040c0510004241c03003400680c20005161150703000d01e00010302140908051b00300e0201c002c24442c0141c3e01005148040342c058001d880211780e005102d640d0324500401e86001130880c51884090303641c20040c40c3c120701850850b00908201413550200708104000140002c0c12034000d2000b40440c0a02da0020b04c140307286001031054980d0b9040114100d0b8856a0f802d041c1e9004903107107602500104414004540388d070140c1c40b03003000310403030b00a4000c0c10b580b181134440c0c0b000c2e0b000605155941450403082a0b2041401c000e0480c200e0b811500c0e441017182915031940100e8401e0352107110b0f1103040c0f0491614014803800b5403840d0362040e00f0314990507a0102c00ea03001d00020703526807060703140c1110370405108440361114032540340411320035450703c14099403090191200c894045043c49020051200c442511802240c2100c003180c5610340f803d01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 963335602 1250 963334352 963334373
    0xa0b160609030302030a0c0e1c0f1b030309050103050115110f160306061a030708040f0615060f0306210615090509070905010e04020904030323150f0d0f 67
    0x10642801c0454001c02c1c9905503015604c43c00404e48140194000c5c0c44045034400c0250100d15070001a0510711003a401c58498244c5070701e131254110480d1a0030b5130b01c81240d0b07a80914420a03114142040034810554481002401840203003001c2c005941860740112510b4208500d402c10010b074803a401c260f524042001040e00507050727007a01c2d01c00c844108180c108018131f00054800d2401c1640007e204007a4a81001c1c904540603149400c50300e608008851340d441c007400039208585410160310210381184101c046040000d2103140b10149006000392844040b41c41e500241880c01000b0480c041612881200320b02c1010040010342c640da00d02040205103003205000e46071a1944040356001c801d510060240c40100212104079580799040400d0f42d809000741e0b540b240f0f680340406c0060034505e8815400500c20306022a0300c0300c0d440001c000c594034420819501403100710a2100c007811200d0f500c00f6500d401da071564040326050010500d010417002c002010b61900700c501009209034000c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 963336852 1250 963335602 963335647
    0x4081204051f0b010f0c11010e1311120601020f060103291302040e0a0510022104050c090702010e0c0d03090f060504080106060302090f040f11070c0812090a0b 70
    0x1601a003201104180d20b0050500051042c081840030014400042c06240305048465204c0c0c83c135011100e0290045420308140c400c83d40d007040b0341c4201c600e500a454040d01c00c400850000b040c2c1c4034820f00c580c5082103240a4002815504014501c048844002c6507081c10350b50051300050401a51a401c02c0741d181070712008000c030413552014004100810344025001a000315003c0c041650102c80903a00c411801030020040c1e8001c24060911029a801400c001d0400305c9201101d88a40d00040d40400d208903000c81c0d0a8000f003441070194500018003541001181c0b000700810440e890354035565411807910640300d0240848041c041522611607d0043e02c1200c18140701c6039075800340540b071a00580148480341d400c207900400c601c0c2c803d2080c0e40743c0640040c0034541c22a40e4100788001412034517600c50810751900840090095014000e044052003409000c1142c0e1911442900f4641d421b16807101048080000300b1160ba01c0803107681c140c0d0385a0b4032235a03480b4000c0c8040c8400010020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 963338102 1250 963336852 963336883
    0x40b090c0402120f09011e0c0306050a080c01030e01020f1e190f020601080d120b0a1a0705010f020c0307020105031e0c030f0f04211b0506010303021002030408120405 73
    0x115200c00903003d03441503000c0c0703030384c02c40d406a5611a550b0050a8a2080380890307501d071403014104814a2085d0426000ea486070300b000a04151180e01040051a080c2c005ca4110707401113101c45840c3d641441003030b601c0c824040086007408071740d01c0c140703c2c140700b0705409410b5044d0b00560100103031000c100b101c6090901e000c0042d040e80c800400070705440c0c4a240341c140540034050001a1203007010611440380740280d07031000c01080d07141010f000103140c2d12496980240d111000414100c50070800050dc0042d1602100d40b02d00d0f06242203429130b50b807144004412401886070308014400042944c85059090074059129582e5400200e40641c1030000c0d900d01c50200c00a1001c07408400b00214000d015450781280e09543d0482580f04803101a200140740c0300900501c0c1d41c4200400c1546024140c07507241c088055900d00c2c410b4111030018603800d44840d00728a00410406404000000c0720a01c402025030851815032694440d60080c12440d80c0c800750703a000010300b004018040d4800000c1d082 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 963339352 1250 963338102 963338107
    0xf061801050f0a02060105180103032a121107080106030206030a0506150d020a030c0816031a06030103051006050d110d020f031b0a050a0b0f09030106050604171006080303040b090c0402 81
    0x400d402503986a0031f21407140200450141c5400d100561140307a070581c0c0d010b031100076880c221214801d240c080d10181c0e03880300012174101c0704001b8502d908c0108400d201581c500f02052820722149081405a40c444c0c1c0b000c5e1f03d0315100f040107840d030b002501c2c0e11259034000001d10303990700350114a008940c0306210044910000b20890000c446502800d1082e517180c2c2d0810000d42a004143c1d024501501e9100c903030300b182c0ca205120035200f50498045010041c214260351070740b00e0301241142d002a04102e5441e0080492900c000001c0e1140c43c0052070b085034004490a01c1e52180503912080001490140504d4500001551942c4807521580b81c00501203902c00b4bc041036090041c2140c90301c41911640421000181030f01c5c0640c54441900c64a0345201c1c030f40459030520360815032003100303096055504c95500107096629103001d0002051082001c1c61000b4868440e02e04003045050340d064010300d0005c0520015a001003500e034030543c0b00d003c0849503241c071500c5500c0d1101040b05580c1c842d000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 963340602 1250 963339352 963339367
    0x9090109150510050607031d0a090603111f08130206091003051b0c030904091a1e09030406140d0f18211b1b030b060f0f061801050f 58
    0x142c0d01079841208120840341c40c2079291402c2052a10511902a0005980301c00002d640101c0301051b01c94000c00a09101300e0903038403a491000d8070b40551040e140500280c40d4401c443c2005102c0c14881d4500c2502c00c142e5400014001d012460041c0014091520041444045445200803115030a000600030440406074400080c06000c0803240b6010141d285c01c1c0b0317603600b80c1e001c1c403c1d95007003190b9101860900700d0758000e02004010b00c001c2503600c07070040500380f04802c241e21041402a0075070040c15400c292220103144200b42c1c003802c0d0141d10f038400c0108201d4540c1c040c82039000d03903c603003050310790724200c10210300d010713001500151820601d001c200c02000911481010466845004018119150031690f061240c0d030b00020107000c1360b80c82c3c030565510002480100d0006100d81a41d14058003d416074841020040e04100c4a484240061010501d4044a905c905c0036049480a05001c001c1c00464030318012140144044944864a039050340e0095094502c803162608800303445444 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 963341852 1250 963340602 963340643
    0xb150d020c19150507441e0105101101020c0d020d030e070515030603070b0c010510050d020a0b0a120908130e04080f0d110a020715020f060609090109 66
    0x16006001c0f100c5000d2120503400c03505007401032512480083e04c4010301d402c07240c2c0160304090100b0216010503c0c5034807940c0000007150103880b542070039031040c07052a490800e0768100c4220040c0d0100304005900c100402080d81c5140003c0c1000004d071600b0350301411284412070190103102c4d0560301a000b5900030341c40842d400a90802c03214116901071041c0d0400c2c0d8280e54543d0994007907281c100c50400141c41141c00c1c02001585c01c0b40c4040c04641d911359803540001070f66041504d480c08180d4485050081a0070800010f4015000480c5c01d035618040540c001000b0346514811108076000205d5501045405001000002d510380750090022034100d00d8001039942c421280c41820182e80030300401c1341d244801382c640c416a4041a00c91078280c2000301d14100790842e40c48048a65202c420b07540002a050014182044c019002000c0040c14080a050b049901c80c40d10800c550060854510046000030541e40000090742c51401d6600e80d0136034030340540074410005d001300c101401109101c24 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 963343102 1250 963341852 963341893
    0x9011e03030e12192f270a02030f071706130b0d031e0908031608041a070515070243080c0105040303050702060a11100605130b150d020c 60
    0xb0702c80d04030044521501d2021700340a105541032441c0c3e61008020010180c207003040e042084c0d14062803040d07002a0440c110000607501104c2284210b500441440204c102c1c403d900364125100c3e003080c20440741d90a240d440c0001d030007003465125040c0c00586034a903011a6000d9232007028042d144559a0026050203005000320403d0501c051f558801928901340c420759001c2d00b52810030024514200314a0100c0340303080d90b400d60680340b0360410040001e2030070403c0c0c1504407050079040c00c5600d524581c101981070401c44078a03070104100190801070416400b090740b01c140300707a51100c4000030300202000d403030400d0840602443e2800c1699094410b9020a1400c4220b03228041222062034225004450f540543d03c40100801d0b8284004130040c9041e5000d440d03e0702d00c520342188400d0258001900d0044d0645060b0131069aa01d0700340302504200e07489204404002209004500c3d4400103e41c0311001d03010303980040c0c03002003a44100841290101e401c0d442e003141c101c1e440c0340035100f40c012101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 963344352 1250 963343102 963343153
    0x402131b0207050a0f06050a0e130f0b03012703030209130603020a12050622051e0c06070206030c071506090b011e09060e040f020706090209011e03030e12 68
    0x148100880002c1034a0209001010345204000c0e05c0085440c1c55001d558a07000504004148030707c1e40301080070b5485603190004a44800c081c040b512503c44817582088800900c110f5000ea4107120016506010103504011000c1174140c03a6400c007007150604070020302610800551008828100d0440c005c00750700400256030080398080d1107550b440c034288070304640c58200142940c0015001030300e003400309141e4211064034100c40d001d2a00042e03544906291480030580580110822910351860040005a10440c81616060b240544940001e012400024600011003500140503010048150034101c080c10040a00740001394032012000e018041c028400760000e0302c1d1100d0011000d0070f07086001c2407504292600c01103e820b054040751006c26050f546078001d6229183c2403168800352004000442c041c000020b0076645501c1040100001030344041c4c0c240e0311140c14444c80b40342c1c220300c4004495143c1414a14504800007041c5444014203152030940110880d000d600d60003a11010503d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 963345602 1250 963344352 963344357
    0x31b0b1f0806070e01180321030f27060902060304050f01380111121804110d02090d0c171002031608040203151018060b120402131b 58
    0x390385514045a0300c40040740d8410001e10081e20702001540590080400300c4551911444c1c5284c070b9855030f002c000d0b40030006c4401d14075010004041e45070b01d44a49406002408414010600016010700615882040d10303011041d040d41060200485a07100800c40755020b0718042c2c0b24907041c01c046032582000100c42d242075081c840c1302100500252801004000d0880201014082036101d10025120f11500203060090700d000806103050104981589195807004c0117076100192032200d035503e1115601c19004d2400d103090500311130601c005841d800c01007001b00507260b42000000079000d400540e406081c00b2445c0307a01080d0080c2044100003141a0321080350150419031304400c00f01c0c401200d0011860074100008031419201f01000d9030494001021207000800301d401407000c4000a0729079400180c0704600c200003200c0f9041014400c0348038081c040003110b107489000348032403003681d00c01c441c1d00d01290002021950348061850346481c2c40403003040f031480310743d190342510f2190320a00d201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 963346852 1250 963345602 963345661
    0x916060203190906050301090c11030309010f18021005130f1517010b03070f0c0c09050610050a051602061207031a0a1a0a020f0d020d120b030a031b0b 66
    0x40b2940190241ca0485210740d036014510b030b2030080640003c000041904041015807e4001e00e6038208101542c0600140302c00019691032920124045900c80903c144145406034880c0380984d90f0340c00c69800a8509040c0155078a110310030381c5001c0c01e81500104d0f94240c041d180841c0d11600001010b010700450780301c2154144216003080386012f800d10810501d00d40404c000f600541c411070f1a800d07400407900b407140d061403455860701451401034111045145d074400070010305103000900b41e00f1080c13060078200d00c0c04018407801002c41c0700301d070f00e83d110030040c201843c0c08546030b02d0120341c2401c004040000c2d4908044070b004000e401130040c81104062070144c2070280b880c041c43d040c1d0494101210381d00e1440560110b00130180c1104100b0415070041c01500115200240102421000582c0c060410402c0780711001d80313400301a09149120340d00d0010445e0094500143d04038103650903040071100044000720001c1140d019140c0240701028003014000e2044110484000f40341c5500350981 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 963348102 1250 963346852 963346897
    0x8010608060303030424110c2b080a090f020d05102019031806090210030504121419081530030708041401030507090807030303050916060203 62
    0x42d9203000a51707014040a0006007103801c2d0340c0f1703810301004034110f030030340041481d9405c185100d19641109000101940141110f00840d540c0750501000814074618542806004080c1c001d060410003014004807507980c54219050024500001c908503500801000405e445891b00c0c0e070b1240c020105001c906414030703034111121008030000c0748810001806c06c1d0b0401c44141000c031052049280120241543e07603601000102010403100d000c91300641011804002c2c503c140310100b0080c0e500841018038004c140000142800b006104042c601e140004800c400e59000304514821454520085c821100c1c2d15030345142c00c02ea80c10311030260800f9440000c04a4424041d4510300d5079034003100c03c1d000e0044041281c42a1170500360080b040700840342801810f644003002c5a0007504010750103030081840360a0b56906004039540007019180c25260703140b501240b20341d5001d003800014203150310f6070005400010f04101d103034908450b812650304029500c0354065106da002d039040c03805800c5100c907450b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 963349352 1250 963348102 963348109
    0x30903070c0602030c0a03032c03030709061b12030e0f0d09050604080c0904052505121c122901020607020f030313020d021e1e150702011e0801060806 66
    0x1711302400c424000303064560020f680840083c007200d01c070418030210140b0180c03020001c0c0c0d140580b54961401c0256541d0034900f4004c1c203040b40b107500900c03c2110149000200c1410038000b82030183c1c0c451400a1500b0103424180c1c007030718a00c0e04601c00341c841c28500030950703100062585003100350758895080880c1c6601c1402040c1c404d6010b860066480100040c100d824096881c0c0c3d44030303004a0035119240019139000f210240003601c2c0e01508007c0141c01d0010345442c0c8a45400381303c091009202d891140030052403142c50160410080c04080f036101e14000503283c011000205400400b490401c0070360000c1c4481089900000b4014850100000c00c030074000200c00078107510301c100540c10f558601c000c408108003504012604a18220110801611f80c01c031f000c4120b1012007010b03109a4034040c00d01000100840101200f41c404002d1403203251070300c0c694040c000c02c000903503035560380e000e000598817a5000a1800340340d9440364034098005600c0380c07955050310b400340d41d0341303540f034032440c041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 963350602 1250 963349352 963349357
    0x80316050c071e180204060f0f171b0c01020408150411060706060b0307390b06030a020607030c020f04091e140f070906060206100b0a050f030903070c060203 69
    0xd0410a0380801401d00100e64001c00b1207009a850f400000c240d280c803441a00c800040c9201c603810042d0300400d0501c103240d044400d01d58441c4e01c2d032a20b001c41200d0910001c091014a501059464007040045040c0c10f980b409041214004024159580c040c0140f19a00075840786c417501d045170055101e1400c8404c148040c0d24042e540007101d41c100301188100304825940030b2042154881e070744900003c2c1c3c8a0703155014500c01c417040c0d00c1f051040207016941901815400303010001031100900c860780903011210301c0e0691207070001442c060954880300400d1402c42c14484c0030390f0010010540c0d20400d40d2084032001c810380300341c0c0d440d1440200e44e81444180d4904c6100242000440400383c210b170386450005c0040e0034000c81e0718003861804642c0c0c1c81d05004650500c907220b034208403000e2002000600076000107100f00e20041c10b0328504481014520300c03150080140b03255000031003041c1a44160107407450f200d944d86419549050041640e940d0740c1c8031184c22144201ca034000020303400d001005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 963351852 1250 963350602 963350617
    0xf030311100e0717013b01061a030c0903060412031a0108010302010c1115040611030306010e010c0503190504030b0612061815040506071205060d022b08031605 70
    0x1012241d0901d14032600c91341101110045965807400c000c2c50b141c008101182d4030f00d1090054544810a00c031810028000d08a600c031010707070401100b00310240004a421090703100100c0d8485d04c0b6120501c5c0200103110750fa15080d410700c216401d00081c0319549144003854120b07601d0401030a44020203112005845d00e04139404203100c1c0c070042000d94000d1072001003c61040f0441200343c51a040090001566406964100da001080a010042d0060310451480118000850a62500d000000d160640d0000c01a041004e0540441d040040410a5800c50b1602c2c414420030640076000041103604540702c00d443c201c9801002c01c0f03107420000442020190218054691b6a6600c24015111300d41c5141c0c403c598810780c20784c407501041d070303001041c05184900060007440c00e00e00402409520300d00d80c0f01c2201d40c40d05003404019520440c404c1e0810794190380400c0c80320420101c1c0c580f49614400e0049500d00403440e030201700004113009520a040c14031000d00c0c1d0003500d00701165140180070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 963353102 1250 963351852 963351881
    0x1606030e03090402030a020c0105161404030b04170d11091c02091810020f0c01060602070b07170c1c0908070b040b07020319060207030825180f03031110 67
    0x5800c072410513400441e0f10102100015180003d40c6030603e0845004681000980d1440010a0401584801c071600071101c1101c0d464107260450329900c03419100175000034a5403440650495a00c0140f10641c5c08002e1400001c110540c141c004a20507070740000c0c3e1503803049010300400151004130510842070250090101b692990303800ca03100708043c504280c03131003c512441c0401141da0712580010a9283d03241c01649171103990030301d405425507034140c10000554010307410a10501ca401d105586a181d00140c0705181d0240380f281101e03091180c6400318406008815400421451502c11410340211030fa445030811030740c0b5076001c1e032280140e005540010100308400c205030f030f0b0341d540509481e81c001402e4480002020080d60b131420440c031400c0760700940200380b00f0141500700090a62140c1c41c084011010000002d9010b14030705440d94607000d00c03000070b85010305824900325400161040340f59054000d034503400c000d01501d0f013902140040b4810034280c00303442c002c0350144030384540401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 963354352 1250 963353102 963353107
    0x16120306180603111219060b09130f08030c07060e0309031018030e040b191508011a0307030b03061f0803041412011112090c03010525120504051606030e03 68
    0x100f0812024092151381003d9a00c100c0f1070340306a0103e004034200309503110b210300250103100d5500303000500e03000a001c1da907502c1d9403cac0c40c0c8010403807240010202d15485840390740d49640340c1070350540300c2c0521100a00341d20310f07119081d0150400040144070364202281251700c41883c181c03540080d180340c0840e1502c45520b00e550107001034080c00c1142003424008001144054000002c9120000c0004014540841c218800c118840c00b542c508181147c0c03500e041401581070402030800e20940f8100c0e50f400030400000580644d100b03070b101c0343d03907008001e094039280d040240c122100040d0a2540d29a0800040c1002414200000450382110058901580300d0100c1c03808200b461100c0c0c400040f459501d40c500a50801120001800b00c00070003e2070150a040620000c3e04d45400c00002c9070007a850081803010b0309a01c40100d0025512072840c4802c940b14640007101c010782c80c0d2205500d984d007050103000400c440450348401000040c25071030313045a40c80400302c090f182d01084180064004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 963355602 1250 963354352 963354383
    0x10f0e0d111e06071704030504050f060702030d0305191e1e02030403030603121d10141303060e0601031a0a02071e02030c0a1a16120306180603 63
    0x10710350010201c0700c507005840e002c80a0202d580490a0034480407091508120708002c401608405c0764201c050448505115a250981c0e0240c01031003103000310f6108100401c501100340d99400200c1b644960b01038180d400224418801a01805e000d64080e6946921045200050500346c03051040303000038241a1203020021807503480c000c2c0365402c880d00b080b500284a601030385031140021406035200f5a80010060700c0d60502c40d01c6010000340c503c0800c90403e40034040810106d400c40031170042100e9011071044016015034000000c051400702ca00c101180055540704090746000403640121418400381000c1c01085448000c02d0000500ca0300d001c80300080300000c0b030300c4ca06600048400c00180b5003d4661201040f841040d48001540030b5600b4000d0110300b0144260052591300f5114032042c6804d24942c21410340c0400002c4001c800c0200c0d020003040c0c520700e15111032a410121500201c0400e031300c001d000e00700d5801212a1403441e08080c848024552082d10b044980003400c15561000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 963356852 1250 963355602 963355607
    0x2120109050a0b03070609090c0f23040815011701060b12060d0f200609030d21180b06100f03050402010903080a0216120803070804030908030714010f0e0d 68
    0x41c0641140180755403005030009a0301c04204440190200c1d85a241c0c0440c60101ea80e0305582149561408000241201680543d00400c2912040101d04042e10800300d80c80f40d00407082c007031948614450712031900520b01000690443ca8161691807000c4500c1000101206082e60310130b11410344528820130500b0006942049131540200e8001d00000d030141440e01c4611481c83e80071000c1c0e41440c4044486042c0c10700082c50849428415100315080024001c0000c0e2030f00c41e00020300041c440c2900545541940e100081d680d20581c4400411000d1480c601800390b810002030f041391000e5449020901d00d00d000000b16105030388643e1000390880010108401400d0041d00890602242d06408000542d100015011560095005001d420040c8480b00b62101e0741341e2150303000620311009040411010030881e40e10411a003085002d41d2564901144d60804985c40302c2440d00002c91084104a95900e00e40790381c3d61010002e1011070210308980007214990421052240e115050f40030b100c07330 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 963358102 1250 963356852 963356861
    0xc060b0a2114010609020309010b04050601020709020f04090e010b03190b011701020738010302060706051803070803060a1d07031805030c013e0d06150c0c080102120109 74
    0x20b106060161084007807100903403d4078002d400c421282e80e001310400000c12802d1060800013002140d091080303051a400103904c903410350103203030041c03600003807000bc05004240c110390081c0006c8500300100281030964174000c113020284680f04c0d008161307410207141000359a06003000d4120a02c0314403a440c0c0214502810f03450000100c15540074030a900100d14080b40c0407c9045900b036050304000c804666200b60220000f0b04161700503880d00051001d600c8071810f48070b14551002d80050661584a450b078040e1038500460902072000180c210b00304800d85020710b00414041d140f090003292070f444a942d4880c062590b0104291800c400541134078885d410079600f000080400c400188020b0300c41c12706652100322000d43c1a91203101d81c034100c4d15906000d0648848508604442982c24180d103081c24089107006846204042200f0400921a6200310003c1c410443e03140d403000002d6074050100030a0b0075050703416000c140b00000d0b10700410300032100784000600a0007496800c0489003001070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 963359352 1250 963358102 963358169
    0x190f09030f060603152313080d090b06060901020309041e110304020a05030f0706081e0a0c0e06090a0303081902030f0414010c140309120a0c060b0a 65
    0x1120966001021480394005410541d008890220307100f03041d42048402e02c07248500100c102c52030202500c4501212030800b00d08a09042c006202a03194111440101007000001400f42c91001880000e14078860780014141442040ba0103659980c0004000080c00782c010407601607001080f028030603182c2980491500c0a620b5682403481008110307020860300e00034040480b404000080c031042d4a0080c0c0ba510050004500802d04403000c0e0540c1ca880e08a03e2180c101031091800115100c1c8018920700c2c0341404544580050f02d1a04480c03000103030070301a00380c2c3d002c06d035030851080c0f0504007407007182c217019406800100340c0303441c0d03036022122040028032500380d4800040c1c0d0128910501c2c0001c1d0302a400b07410441130301c1e00309400c104182e980c116255030403030384c50051101034103a00b0200304034204048844640c2c80b5510421590b081c4402c08100401e5114002550440c1ca0340000843c13140750b02400d0708000500c401c1d0113010005485000710541420505180080d0446011495221 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 963360602 1250 963359352 963359357
    0x1a04030821090c01080f0910111b0a030c080708041d070314060108010b0a090911030609130b130204020d06080601150203041802090a0e0a1d0307020a090506120613020301050c190f 79
    0x6000523030070802c54000b20108002128000b0701a066002c07400b40341d1502c4062240500000c0846950103003a4540245005081f003201094650030f00950744180c40003050004c2d040401809a00c1d07102c0110b40781150b0400119103001e40c1da032030b03000d08200358030301c9880e060b181d081d50b590070120b421409405c107014007420800c0c584004103c4220600075000440c50540740507449090110400c1001c140c0104880c0458020320800c00c04601d200300c409410091d04c5110611400a81c00410042d01c212410040d845081c40310015000c480061507a040702d004800200f81503261940072601c910a51091001d0300c0550ba0210301401d00683c02003084031402070880420a0380e4503550b0383c5041c01200c0464949503030701040d2031028200c0c0c0b04491112003003805940380547c145d0000e01c3c03150890091030101560f440c0060b041e40c480c0a40a0a400c001038100d0301b0f5442e00c00780c15182c100c56840d049001c4e509090101c1d26503801c600030340c0c5958900d03240d01c40c6149800c003001c4502c800540054002c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 963361852 1250 963360602 963360613
    0x10302180307170d02060709030305030c090904050709180b040618021f1e08040303050a0608010f0e24010b160606082d071a04030821090c01080f09 65
    0x3000d64003004880014102c0050010702e902e0300d10201d500f0003000b15211000c0d50003e00c100305900d0b5005140c9001c0e242c0c941080b640702e8440d014041d0b0640200c60009822002502c203110501400040f140d04807035004609010b41c105540191101c00d850410040c0750340c0d06500441c0000d011500844503000054000c080000696000541c07405030b0582c6c11040310060421429240307034000d0012200e0140e4041c0c0021030029807070300500641c8004d00103020117565401041f4001c5464000308003d1000400074000b0410303004042000b40f0b01c0b680540f03010320500e0117079801d107042c0355144980942442000c1070603a1904200e40002c6c0d01502d150040151903007a44000503030103200f0200a8407162008020a4044007817402000010030040040403003101c000340110740c00052501c0c244d81d02c0e200002c500480c05110306240380140c0e040280442c5011407040c6444504080b0000705042500000220351507030080c00da2203510b10a01c0d01d00080f12500018540d40d42c41e80545c3d00300307810008031003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 963363102 1250 963361852 963361897
    0x80a121d120c06030c04030b010b03010e070806040f110904140c040b072405010303110a0506070e0103090b0a141501020c010302090f09070509040e160510020f06010905240d02010302 80
    0x4520780c2c01111710005856010405005002d04000d890740500000c8030b0442c503550400c110502c000c44010000300801c1030702c40000c0c40980316600101c24041c00c81c0c0301802561417042400c0000e800c1107070303000c0c00350785400c110b071a41d441368a4603c4d024890301100c862429041074409000c0d40c3c00410181c0e00d11500020321998004c0c0041c2402014204400c0010303154150300e401070108100506414656008090a5021a80100f50306410145608000b00d20b01c49950060f00078041350034000e00001070305002c1050030b031050341200c040c83c00c0c10300d811181580d8a100200640c811201c500340180c0c01a0035040040d4040d82c01402d916000403c0c6001c403040b2440020500c900c102c452000042010424031201d08090085550050a400207007001c3c5443d4000000a2010342c400c5c0c600c11458082e00e1a0014001d03c1a0030310f180500c0e00b9580190785400244001d0030040d18584030722079049071503141d520340409261070b116100918000c030707800349034004401035004007003004580c010613140c01c1e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 963364352 1250 963363102 963363109
    0x161205040e100f080303070801051002071a09120a030504051e030109121b050c1903080c1c030c020606041509140f07080c03130c0906080a121d120c 65
    0x4502c140d40008100d1102420300031003402c160f0b15640001180d910600c240091150000c1c2028152a41500e10b50300c9243c240004034580000d40c3e112980d601c200001c900c03182c5138104024500d04000340c0c0c400d94420b80400e00c0a5803880180d40142c0090414070046c880741c07800f105038000c1c8450125418801b81c01040010f801c40307543c803d08450840d071041000341e00c1074003c003c840f46190504c036540303038900caa619400c2d2507501c3e00c14038a2060034140f8403102070f00028950302d0043c40d00594080d8031403103071484181d5a00d4103c8586000b081402c2e07002101a0f10034024150b60030744030b0703020700300c1515628180805800308450b28213801c90340900c08240c10380a03101d106000350400e281030981d4180740d4049080b01001521b1501003255078001c114210140808a80c1c1004414181e1801041d81d41000b8036206101c2c0c005903140c6051074000204d1030400920305941e24014800d1050002c2c50b0f00c416168000c001c00145000c030440b40d6480500c2c0f0b8405900750700311880d04207a9071501c6100001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 963365602 1250 963364352 963364379
    0x60819021b15061c1704081f060b0d0207030e030f010f15060e010c081312060f0c080c0a050c030d060f0801062102010c120302030a0b010516120504 65
    0x121600000c00244100081e032080041100c880000c456104040c00c0a101043c1221041d00104074803041c04840c0c2c0781001495002c1090450031803041a89031903c4d50300740d98031511b40c0e03068030010f00c071004154405d0301d000b0300c1060101d5a42140045c548039030010058041e4202c800113a050000d1554034003541d403410310003904200d21080001a0800d1102e01c082d0441e842600b8011504020b510140041074000c0b41c140700b885000d081c01e50b525141c0d071904103c140300d425a040707070f220041540082c0030b601ca00072058525108441c01c0c01505440c0104c0c8044441798121039000801100c0407825500c0ca5500400659182c0e20b045458004195402880c540c8101a40700890f562001d04020f220a00c10244004d8070884009201807464400c3e003140d40b004120040400c521204248011607000d20046418994070070300b0b0489804081c00c0240c02908210740081065090a020031401d601c184211001689980c41e80c1c070803d0625110112122102c911420034048104800300303507410701e8000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 963366852 1250 963365602 963365617
    0x170703050a1802030730150f20090414090d020d0906020607030b0d0b04060c11011401180e330411100e130504051c020706081902 57
    0x18041000e003861441c04040315900001d896080d6200e0350410016034010078074204403041c1005000b03880b00c00513804125020138082000040194941013000c10114280005c1106040d50007001b00f14000c8085006440c43c160004500342c209507460f61401008101a001a40004c0d00000e004008074a041304245025207800e1030540c000346608000c15410800c444c0700301e14503d0414a00c6140541c003075a1188041c00030014151111108170660300c50400d0300d0201c40e04664035114900b01400c000340101050f24800d07001a07606854030b0081e1505002c2c211401250808028040c0e01e848042d800701c003a840006030b18240c48481c3e101b1403503070410a44031002c824000d501d503030320384031a4405030b0b884001a1a070b108080d40d00c1040042aa0160303091a10311065034041803081080344116a1038440100d16075001101540051960803a83e020a11851007001101c20810080c440405045401c80c01000140c3c4245000d11240b0b10518003113800c181e40200402902141001490680c2c001c800d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 963368102 1250 963366852 963366857
    0xe06240c0106030c1a0f032d070822081c14070201200405062d070203010b1509060a1103031608071e030e070b0424050a0504151707 58
    0x90b000c3c4240029680709900810600032040e502101d00d95040c040c0e4000c0d0400203c1190004c00080e840c00c107080fa0800e00d00034002030841c15042100c2101c12224800e460b6007001030145000102e000801c29030611181c581701c80c120f03d240100b59902130240d40702111400c019040b54110170b05440d4607002da088001851103c2e11114071740094028210341001c003d001e00c81504001050903801118100c8003621001c4c0d40040d51140c1284444419520b149503003114902c0f0040c19942003070060000d8035a00d4802c80007032100c541c8050800c11102004900268170349810044071000b40f6144004003500111428040041601480303541d095400071182e801280c118041c982d440300b1750104111390f1104040c01c2c00c3e800f03100c00250000c0454081200c1002781995080310011a02c020081d66000b00724540b03125649603110903e010868402110314407201c1d00190040105c20b00401c02c2d6a0742c05403503610030f800d10345030001601004000444817018030000010200c00340c0c504010046c403a05a64 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 963369352 1250 963368102 963368111
    0x1905130809060a17090a030f1713051c0305061503151210240e0f0412111c021c081b0d091a010501020703021f050f120906100e06240c01 60
    0xc0c10050141e110488000080064850304440d40c489d44458081d0414a00000c00c0da440c00c00c1d01c0c0051400c00d05004441d803a007865840841c80c1c5904d50081d038070840054034940070044405042058902003030b03070031455800f200d916031509401c0c1100751060404a08044449141206d03070a0350480e403440c03809201c4503d1a0070b03504500246016a20001e09141c41d94581700e113000f004140c94144003a00041c003051044a20340702c11849481903202000100d4142d8490182104d00402050b54141000015000f2420380451400c01300200550010a0380c50700c00700f940d501c101c08140700d10030320380d50310000106012410301c4000d40c1c414504618420080b02d044201da00005061041f0168841411948800030500043c1c60b031140205000f136150020000d090034450007614540609c0a00c6c02003c04049102807140030003a0500e0300540c015400c2d204162160003410131252030502503848132110010100d005418a40440e00c0120381d402e880480904420b215004141d0000e0700115403603454 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 963370602 1250 963369352 963369373
    0x90a06060e06090303180316080a060c02060601021009020307120303020904050f1509090c150d062c10170703020f0f01081308070b1905130809060a1709 67
    0x48529148900002c0700d00c1410a04400e0000b55070388110808120380f01c1034140c11240075141000400205075446010f86600780d10f5031441030355a811050107803420b509004845002c00d0002c29424011301c4103034060050f43c224016030b00003401c5c000030300f02d070035100b41c071400554402c08207148091140b190780d0160341c400c081d00800c8142c0d03002911046038521010144404d0b0210702e4110319826800351794000c0c8540d540306070941081d4000e01d00c9074020f41c1900c0208222040d6900030320502c25080420000d003a00c0d204a000e40c18500c03080603000c00c0c10441801030301048403a181d68060510032441c07076181d03101c40641202d1031540140d8038082e88041030034011440c0c046000c4004000540300902d450700c650000801f0044081c0c200303440c10500c1107051080c030614070207c2c1da0080e08460b03500041e050451a21485504080d40c0795610b900d00008680d46448064040c00c1c5941c0102210b800e045021003042996484400003000f4007103001c1c00d200003090814400340c0310b03203d03031406048034079003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 963371852 1250 963370602 963370607
    0xe0c2214090d0e09070e030a0f05010905061302150315040609020a1d09010b0c0a0b0f070e090712050a02040323163005060f1b0703050f0c0a02090a0606 67
    0x8034000c250a02000d4181c20f2200e40300c10340301561140c4146080c40d8010100703004a814161034440107481000c50900507010702505411101015114400b200d52980c1d910035400025468540020f60001415011004040c4104040d6411000174003030201081e903400300040484500350301504070340b80c02003404800d0940040020404018101d090300c204030b41040001c0e0021414054241e44100c00f01b01480403000400103002000e83c061040d50450505074180040c400341151203e0004d404c0301d000c0e00d210704143c1300030390182c0e521b901c55001c420300c031450200140000a001d0441c860f4280b200101058030035480041d00800b2048480e000c5524140607403c0104ca030100c10321040500800b000000441038412152154040c500c5a41007601002e402800c0c035981c0015020340704042c1409400d011150409010b0601c562500404814024030744045008402c80900407540c14400d90450b50a440b0042111004410a94504201645c001038050109072640c02866580380814410140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 963373102 1250 963371852 963371863
    0x20a1d0412090f121406070908060705181219080c0f0105190f06031a0708160c0308060a090504081e120a09021f030b0906040e0c221409 60
    0x55075850401101401c141c1c811208180c14403940000e0a034041c3d06405020079140c1010790512440c080d52001d042500d00100101a40d000740d00d018011314010a48041c0507004585000710b0b0891180662010b000820503124450400280c00d8085e84180190740f01102214130046c521418096484042c04501c4c41e28280c548081006e580c1c0c504000d100c02540c08514105440b001d0784c40220314844059a80009080d81382d000070f0440f006900b440c08844181d0311560f225010a90381d040e220f0381c81002e616202e27081340d520400412400091840443c0c458850944e202202501100d09030307550f10b10780001c84c1c80444040e14100c1001c901402e190040114901c2c45201c150700c05070804401010701c102c03114014000306042070369080745104544a0303001c0001e10021210011010900075000074020f004040700c40c45c4600741c2400060350f245403a2003190340040c180b500401d404840001400062020001c00c6850800c080404081d001031500800c036030890360400340c9605042445902d8a4030f03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 963374352 1250 963373102 963373133
    0x30b011d0a0504111002010209040204030f21090b0903030c10050103170903030a03051503010c0f020d030204080303040209310c05120d08150306010311010908030c06010b0304020a1d04 81
    0x19007082c09000200f000105107000251003260719054024074000c00b80e00a121f54000c0707581250011400009103c5200410360704503000f9030089151503072901c2c8022015090035400000b040b4281014064140d114000c2c2c2045180601101e180583d160f0103d8508a1541105a41c694650b80107008010034884864540c8100320042420402c542c40040d403039000345c1602a08156803440001c1c03449240ea103c101c41e001000e4001c0241c1102035000400d00c400750050070700948a5044c00160702c621a100f10307070841da0000055401d41d1120360070030510200241112080d000c041104031440180310b5a0f00c14480d20002d070a4100404501d071130082101c1a901091080034240403581000d903011a244540740301e5494411115511903091034021a6002d02040e05417081400100400114041001c0e4910090300c4640304d00355581e6a086d0384c0c0c4121004014640c1002004121081202002d1900315100a02860302d840e25030014005014401c46400d92020041c0148010f00c0f0020300c840d1102c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 963375602 1250 963374352 963374371
    0x5010914010e04060e0f1005010c0f06020f0702090c03100608070c060b030715020705130b18061305160305090613150608070608090d021f02070507030b011d 69
    0x2500d18084140d146035080480050500c00b80c0861050341da9200d80c4000054a20814041043c0c18180c1451401800840761100320a14030036010400750702520f8846035a6910012241c0c012915984640281d0800c42900115003401d1004800594078075000c04e1054034000c4040303440785403003100740400301c10a50100d024000c0850a020180e0784c8440a00810f5400103030110704403940d071703000c03e1920b0899440010013084800d40e64414590201c1c0c0340b400c9810813103a540154002852110886103080744266000c5c40c4000c9180682d549180c144d5030000c4001c0c01d80407200455024082039960071103841141c10704064008400d5071301446043c2d003202660340100340c01d00c2c005001c00705100302c00102408000c44c04002e904681d601c0c2d0030003406022088191080d40d50f0310240500311103016030301070450f40542d00d900c102191001406856010522803003804205206200320300a60181a040d20240a444030100100b801d90b0721980c002c00e192090444050340c20804d10003a0080908298078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 963376852 1250 963375602 963375617
    0x30507050127110f0112090f120518060c070e180102120106020d081605071502340c120201030219201c031524110c01020d1103041d04020a0501 63
    0x22541d070f010000420901c008400040c0040481c280b8008d40042d4000091942c0c03a0b54581150142d4008090122030300140c820b00c9400807a001000020b00a00c03068101c15801441d041041c425803030405038124102c680ca00300e040031481002c3d4203a901c0242c41c1805d0020400040121940c100620202c110403850000181e0401c03a1030180300b15a40703142101005004103040d818081c62005100600c600381c0b204566854111000b0f103075189880c404054022070030343c905d000aa801111043e0010740c00207a5040c00da0038902d002e000701004c06010b0f4101642480301403290341ea50080d042c100c19140d00e44031032068119813401480781000e4148084c070380100602d80c40c054100c40780141068900c2c10085959142c0003540ba00512080c1d02c41c02021501c0d05204041420720300c080c0c441c07445260b40e0380d6500da100402d042d50302d00b080904a401a844980d40c00210742c49221041e80c05c507408010b40c0e20b055030321010740000b40700303202c3c40e61100140031042c0011072030b001e49010010402800d0504 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 963378102 1250 963376852 963376879
    0xc0803270307211205040c03050f06070203250204022d0a080412180608450f0f060105030c030f0304030818090c090f0f03070303050705012711 63
    0x34641c420320b5840381c8003010a030560f44102405000ca0320b0013201c890204000501e8281040c04103078003144020740d9680521a040800d00a0108585201b181903400442c0340040c1740700601801421814501c42c3e40c500c907040c01005a45600003009c0340ca100704510000d0381d44d2441000c154000c0c1124400517407404105101c20590030240c040da00c1a04100728041030482030400b41d815604110340619480c0031082c0114229410010090045000303800d002702d45000d80c041094443c141c403c1c1c481c7c281d01c217440107400c1c18000882c10046000c1c240186c90900454034007480c0341501b06100e030413540d04440300600486c2410412080104812401041e0a89000c070203140c4034440c6020181094a00250803500141d2140c0e520310802009000b80405107440144005290081c1d82002d00c5050b03249050161403408503501c0100d0500240904511461907400b5141a449004111215526203040351601c2d03c6008044255040c0e6541e041000c0e196072400080003203178003039400e104200b41000310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 963379352 1250 963378102 963378113
    0x1202010c031410091109040606050c0c011b02040509100518160b04050d24020909060a0f0b0a03090203070602060609010608011406090d0b01091a04050121030c0803270307 75
    0x8000c50310080d20004800c1c00c0d03406100894072540c0780d81c0e03030000c8c01c000b0001000d0b9408030042510503584010b540350f1034011401140c4200315181c201d0352210740703001c414000d0724181d408980c2000d0a80119108040c0400003241030f01d50807200f04605904000c0c107840d040d2018440a0f84050075500c0c04010141002d0820015000e1401814018000003240104009070103180d00b408400360302c2d1807120302d20100c0c6c02c48040d42c0042e1102c1c0c0a010b1080200d03110341400010300080d2072410a00030300b46401c040c0244020b400c650a041c0405884001800241e10188004005041ca035809403409140c45000c2c07010300710044c0c0c03002c01081100c4004100c800d85100f02c501c4240c40480b191b40e41e8040c40300024401041c1c80e24090544074091000146111556100741114040e10407507010161031101040101c40b0248580456a07807610481c2c0341400d05400030718045482418140501d000d030341c07a50703645a00111a82072a40c0744030401c000843d06011a5000d11428440023035141c800c0f036a650 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 963380602 1250 963379352 963379381
    0x5030c041b030b120a06051902280507170405280302130e1b0a080a020108040b0c0c03041205061620030d0207060209090601050a05120601020a1202010c0314 69
    0x5450405070f48580844065a515000005441440c003c03034184049a0a00c81c00908064401051015640e0a0907040383c00c54001c1c0d07072041d40c0d050380c400490094041c0301c0c10102c00c4400d806040003000c110304000541154014030200c05217500042c1c6690a000c148103200001140c50109080300700b540e41c101d005c0944841050300d82c184d540404600380b02070280e01815610320400c08070301501680d0f00307411000d034012621240301110700b42a0503030384200540d2200303d8101e000e8002900c00000601003100100410382108204404516003d0094006421904180c0085868036210b0041100703202040015a82021034039000c42d00042c03400401a060000c203840070451005580b010810854090090b1034145681800c250b44c0c0300564a820300007035001c022707198800e941210201c0c82d65489075003515907401c5951250313840c0442d0b0b01c80e09240706000406550452151181130b500044407016017004644094001103230007880080040c06540d5400d9880840c01060400c000300007411505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 963381852 1250 963380602 963380651
    0x60501050109030f110f0406060c02010e0105180103090c0f0803073309030c14030a0915020c01050c010b270a0c08130203010e16030c090207020303040902030a0f0f0605030c04 77
    0x100f01c10030051700000300c0c0842803043d03800ca03842843c0010006100f6001034500d87c0d140d00c00da07207209010020303900643d0180568658031402480c5180314034540e502903071006145900401204010341c0e0b503400410806d824135001000303550000310b04002041000d07000c00f09000d4201c0f041d0b0841c0d00803950411848401c13121421180342e1101000005d25004264828180b030b04801c01c503180307c20340c0c0d01e959a6070f8081115080081c00c4880001a0200d090108600c1824583d01420b48108082c004684c690440d80f0700032019541c0302f40a0005594498681c3d41074400c1039a40c139001d03504070030403400c09840100301182c02e0307080c600c02e00c203210b0b88522030b160b0203890039200301400d114a00100f4010154401c0c4d00c80a4480c1c4401c0201e01e900c03040f988002c8034400c004004c0d0460319a82003400f41d000b0108029010350017400113102404058001d542e004d24043c0340003c2108800d80004140c90381d4400c00700c1c105507101d03003d200c241070030f0000302c01841341514180b01000d15401015001480c000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 963383102 1250 963381852 963381863
    0x130b010f0c0b04020f0f030a060c14120f0c1c0b0112090b0103080d1e050405060603070807060518040f1e2309150901271a1f0909060501050109030f 65
    0xb580d11907071440102d804a071b4015046889424080c5000c000034041920404040341e620200d04a0443c1600e084405403500d05481e03078095180e0420b80183c4e403402030150f098800d000d001f143c8507211903000341500510030a20110f901d415074070001d011940004a1a0740080c1003035100b001258101d000700381107075401050310341d65080b2954024000c003c2c0c1c5921945080ca0350402c540302c0d905d2030b046180114000e509442040d1180000c065030f0707103500e00c65400181c205c5001001024000c0001e40b103040c100c004c1d07800541480000117001c072041c0a0b0200d100580d600b44c0044040041c543c2a80c046002e40400c00049140c0358494082880c03043c0c035a0340c24040c2100045075801d05000c01e441002c1c0e916103001c4541001c4040c540a009402c00385025a04141e038980607410401041c0041c158016003202c6503507000c0703001d501c40c1060082a030200321006204001024124484810043c0f0003081d0010710111a89000010707588103034403544c100030090b00f050021500c80e0541215856100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 963384352 1250 963383102 963383119
    0xc0d0804020a1212080c04050a0602030d0b0906010206070c060b2e0203030601140f0c01060e0121021f0201151d012408090109020405040f05061608070c050309130b010f0c0b0402 78
    0x10186d41558407542d04195041304040d10000b42c41c503000005000180d0100e442030103848849418844861400c40e856801644510081415180104049a00f50340100c4011030782c41e040c01c0c0443c030422411242400314510040d640018501c104000f0010340020f0f2010310b00d10708001c80000c101c1e103140152550740340e00000b4085101c050400842d0085d122090013400115904c1001c4d03801e20009101c3c0e61030090a0242c2c4002506c00f40f1044242181e00500c42d83c11142045400540000f01e582c681e000c5d5965412000030810b0b490721580010590700c804c03e0045800020f04178a00e51060780045011150600d0780710309110040e03445c5804c18840e180c1541d466943c0c4200364058945080080c2d00280361100f40001d115084901e4001c2c0c40c02841203500c5a2680700c8004198541011004001010034001c540201e01ca40191140b16010f20b0480b41007264010004814410400018034041d590300d0040c145541c1201d44610602e40500341304c1d0b145689515000004078004000a2003401103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 963385602 1250 963384352 963384361
    0x3071a090703051e1c050304140a080d0504080c070e060307300510050c070c0b03070e152205041104060206160309150507020601050616020f060c0d0804020a121208 72
    0x1080b02031303840c0b850804c481a20700341700c0d18040d26652081e501500d215000a191007034885d070026818894170382c0548081e20301440303144c1c9440108000303002201c00010811050784030f0441009050044e010b01401002107040540805140800e141e2281c4500720082690848103080380c0350f4002c24030340c0504c0d001804100340c5072980c2860100703000420781900d00001d00400401040151000e580700300608141c1a441c1e85051a03240403c0321003100280d24000e80d1585820b0040a041540720701d0004c180c00c013251100310881850b40c0e50b031206881d007405842007007149810b004001849426a080c00d00e02410803000944480f4014120060000d43c038404802c014401d80c444803080360001450019501e030481e00c140681401c3d2080c8006208113000823480b07141c50001c99200b010201c03222000601c0c56801d22003060095107505901010900c0300804c000070500c60460700078030559540301c1900c0c141c410002d030514181c000c92841d00410300100d0000f02c8902c4a00d5508046003801007880d5203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 963386852 1250 963385602 963385663
    0xc050d0c0e0d110a0b040e0420031e060c0403050a0308040215040603050709080d0c02010e060f040b070c0602010c05030f04050c060a020f250612090503071a09070305 73
    0xc610100c2c0d000403201034a00140003408003424880b503030444269400c2c5a0344c40503100240168000c5d014224081c0000c038000903400c483d095050744208020b09151110306001034201480c3c640d01c46508000d491b030490303c1c00002c0c4601588941219811f50409003103441d01669500e482c6030003070501c40d80314045401e43d40d41d10b40307640e08640400c4034550703902e841e034030028050003054480002141510f800462701d20000b0800d190444001d9480c9071f4070084607001190f10f258030320742d00e54014000300807407034002ca00e135070090001e015a40c03030b0a981e1301020302d04001416103981c4028116407401d07104021981d441001c50350003010610403002603403540e00304142440503540e0003130b60000d0002078480c8596000302d501e0341445056030980d00240001104500c4400214111004408a0800c184602c90040302002104441d40e000010300140a981e1903146600c94542a250342105114610048103032041103544a10154041d000741e030f1440d40c0d09a030300c2201c070141000244210070f14008079030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 963388102 1250 963386852 963386867
    0x30112051f0c030c0c080f1b010f20040f17190b10060c02060d3c0c031803030b0402090a0e0f0c180d060902030a051509010c050d0c 58
    0x1c10315218040e64441c04141c24000c200010202000c40c0c10280d500f003a0714019203110081c0f5170008a407600d0f121000c0381e1400030b903200b9504500d40500a11030408a6002446100c5e03444144480000d0307110080303201856013042248145045082c108014486c48000d800c07940308854540080c182520803144410707082100d01d0140c0c00e0049004c6000790103200002200d24001c40c48001420f4081d501d900081382c116400b0140617420920401c090074500903a64413600e92000306102c054109441d000b501e0007040d0405c1c1c0c0f07000180c1d81101807440300245501c6181044491800c1c01c20040c540c1e965169204a09614046c0600da41c4d00849015900d82c9d0f01150300c10413006200004440d01c404800d14aa031007a18182000744050740010040c4040c02c04503020043d0341031110040b10701090800c11100501b00044605585070100c580050701c0402100055512910240001c210384020304000210000c14004a41e8100000c11032203640110480c0c0136560342e00000701d803007640c0140a45648 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 963389352 1250 963388102 963388123
    0x2404020706060302041e0f020f160609080a02060a0c210b280f09111b030f041502010c02011e180812040b0601020d091202010c060509070f050306090303011205 70
    0x1400d1220001010718100c803001c081c04040c01b410000c800310404c10f24100d01075074248800c1075608004030260140c40501c101b0580d48074042c046070110640e9283c00c100e412110030000541d002c002400301042c1d03140200400d0528070311349540d000d8428014140003501003980c0c181841d6a0700c00e02e1001d03807a41001000500401c0d41600e1000c510446820443c500c944170310140d0040141d000b040900c01402100741160320983c2d00ca0800c04041c440e109070040c9c8501841e103d10040011103841c402d0103000c1c00080c40395070100f9200e00d004080c080c0c25034101000060440e403400d020041c10401c441c6100c401c400c041c000011b1405e074102100049145403140c050050b00300030510200c220001010b0030311440c8616128002d03502c4041c01640e640c4101c07181c2801140d089401030000354450103e1145080c0149416060500c0303a85a010846031309840070107480d081001c05210302e407900341003500100402c3e1700415451803c0075070181c40c1e003c10b00841508cc211481c02e201481820007401002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 963390602 1250 963389352 963389359
    0x306081b010f1106011d092b022b0806030a170c0c041515050301031106030a140109060503120f0405102a020f04091112191a2404020706060302 63
    0x5561500b06d4541d0903420004c0315021a950140024480c82000c01c40b0580c0c032a50b04070f1740d205c1c0c1820120313007845004018010821445800c000d480900c90800300c550303482d40505848404003040c2900140007070801004580254010081c100004a0204d00e40070386c1c000c6001300688a001c40031030281030003511828183c0c898101214924003820102003001206d424942801c4484944001929640030920005c2c044545100e03005191b410640f0086a00c50304544000602a03030020181211403000c0c1c0040303141541c0c450b8140800c1c1410000f801c3c04424501446041080c161030038001031145000d07050107005501404024103000b07030300103550702c510321107010210001c0102d0020307091000c1b44182c0c401e043c1e0809580c070030306141c41247c03010340e084091f86800c0c00c0303140c0510031020f0291010303400c1449401c821016121742914070700400c500ca0b5400344400180d00405c480b013a0406020400c2008200c60000b02181000302d208005840036140035071a82d015041c040003d08142d80040d40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 963391852 1250 963390602 963390613
    0x3100c0e12030310120305040e0402040b0d0b04050d020c090a092117221b080d0306030b070215010e0415021612020c0607032a0f030306081b010f11 65
    0x1881d4000b20142d4441e54030181685545641c544034074039140751800014010440410003449152002d01c08650700500107003011505c880c0103804240610f0040b10140c5181e00c2c00c9040c0003c006c4184000313030701c58405200a003075500906001860213540070701000c0b11683c0d2030804000700441006017104010350b0750721039407164407003640140c0710308648000701801285090014102000b1048004041851503441ca00c202119681d80c2c404100304990000c40085680320000b90f44100700007100e01c0000340d680101d40e89141d860401001940600460300f5500408441c8000c07402e00445e072411100780130304884140d00e86007800c0c01c3c1c00b4050f5840c001d040b80001038141c55134038000d401d9a070381b51191001c02a41c120001d0300300d0b1540300e60341d001c40e80414200309440219100da0500700d40e8044281882010f6490b800010001000c0f90030200da1500b040e040b41e1f818035805200d84002000b5010240c0002c03141c400c80c00d030550354181d0b2491705000c00d0302c64a035a501c1c403a102080d0000150f03c00c944 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 963393102 1250 963391852 963391879
    0x42c071d010807060507080403150e0706020708060a1a1003290f01020a0c2d060c031107051305041104111b0304140105090612270a0203100c0e 63
    0x20003103400d01035550781e440303a040e0025441e40300e0021541e42130b030481c01450405003107176500c0c100a1011540f0399801d541754000c007c010707001404842c004281075001400403614242a1608000d40101030301045072030700e01c16001d40c080e102640c0680410403035403130f41b1181880b04140e004100c11751040c400b50007000c0843c04000c1540345a04501c42003101c20040f405040001241c1da0100030400602d4003c030803200b08100c044011850010110705111402c989031080380c07071242c4009951101c80001c81c4d0f1843c5006054015014003440404c9401501c0c149060401050b804001e1000c00d00a0595440000d002c4c4182205800300b0507174003c10900240d080f42c9001c01c496004402c041310f0825003031509002c551070000132502201c50f03180003620f4045600006682d41c4d0400c2609a41004003042a650b03c012040b454612496440651107043c00c140701420741041e61070b280388000c0d81c0c0485540d1016aa000070100c0b41d4052210000c120b103d0021740888429009544540d0414103444100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 963394352 1250 963393102 963393149
    0x110d1d032b021212060405010e060d0201030b180915090a1e0c0b070309090f0c090e0603031228110711040b040204090e01050915340509010e042c07 65
    0x90040c5e004079014071a40e41c03582c000e03110000c410768001341d00008040022005500941040c540680010a18040d1130160004021094003c582107030690300301e4104e00c01070240d50404150010140e2004180503500c1c4d5540288040041391000c8024a425100da01007245200f2598042d000444259032200707540d16014104150743e00500301c1403800c2000b8400240002d00c51030299042e1030703840b2500355203404001c5141d54400303082c071074042c0410000164007010400e111402002d007195200041d020b070364a0b1070384013810300091000440c241504c80f044040c0800035211110b810101c1090000344040c00100140000d064468100e800400d000402c50307115400002040003420091049a590140d03040e212203040c91020f140c00c0706440032500d00e0350180d140759813030071404030002d01c0100e8603020030041301031920120001401c000f03064032240d40e00036a01c81c12101c0039101408091f140714406591011860402c81c25032210002d180c451030b030104203510040c2001e89108071031401c5000d01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 963395602 1250 963394352 963394387
    0xe032a0607051b061903020d02070b010816090908040504050a062309061203030f040507030c0308091206060901090c050f03040b24060a0f110d1d032b0212 68
    0xc948a80301100305212400e0840071511074880c3e540e100015001700c01410380c0203401c580c842183c959400e00c01500000c0e025400350f800b8108840086c0314110300f03114103c5e0010141d400417010039041088030000960440c1c10703141520821200030400d651482044030042080f0b82c0300e030410078582901141036681c1041114502c0c00e05a403001d0362582d90300c3c144000c0286980d410106035100b0000108540144942190040c1c4241c09450307410355241c030b0342096074201d234000b99800304002444d580e96140940e0084440304144000d08040d00d821030002e90008814411501074544660080059074400e1301154086d5100e0b0040c0e5882c0d04050400e44842501201c010018540d40a01c1c65404c0341002e240c0c0b01d06800040800e80380c950a020120340890041c0d0f00ea800b880000d82d102a81ca10081c0f2400d100343c1e04036900e481c40807249003d60401c1c014003200c00c6019410002c102080940c40e0031540740018541490306d0300d0343c61518000c900c3c1400c141e01402044101203101d9110807040e006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 963396852 1250 963395602 963395623
    0x1005070503180106120b0601180f0e060d020d1209030510060503070617070e0d151a1002060a020a140408010f0c170f0c0d0e1c0e032a060705 62
    0x4030300c92140792403507009003203130910b000d8842d1010303001d000390300002d003c2e03480c07541c4c484010724000007034445082c10341d0130050540d000b10700c6160800d02d007404a0100449460b60061084400383c00b0003d440d0040f4840703507180e80e03001d0f2420013510440d944044c061020f020040d507021040721352404840556400900d12401554442c0c0a0344a0003c0c41910445100b00400d05284002009071143c030070540c2c0c800d1580031391a4001740809101e20101c0c98000303d411244444180c0400c0c22050a1207920305608001c81841c4606803e89408c6419540025070aa10544100c0016a40c600ca480c0695010806012019007a20005000304502d1010342000e800302c6131541c8207008110403141d080d90061500b25030200000c000c40006401c18280807006a04055020b00141c03030030b901d0b8141403042e1442c5c640b07602c000780d021080d60602d0285d4201d107943d0362015441c2c0400140c0c0540c0000b41c6903110054804003500000c0001c480b0141c0320000c0d00c1c01558000d004568845039442c1081d199109200c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 963398102 1250 963396852 963396871
    0x13090b0108150f0904020f130e0d11031204170d0506150a09180b030115080f030a051801090b041e151710180e0c01020c0f2b0c1a0f030106111005070503 67
    0x2b000035025078060b41d00a1680306a0001641c00d1010500899164a400038010303100c07030459441404440c40c3c040001d03c1082e503400b10105503032814206000401031240360701510002c0400c12109a507900c02d114105550307507801c0c14104108185054809480461041503041d4a40111500841d1001d4510004c0303c50303240030b07924054020000e003902c0c3c0c001c2406210100e40308201c18a000c40356540c0703c0c0e0500c0014100184440d444000d081c1c8182c020b50000045100541796052181e074408600d5401051002040f004a5900f4500200200c0461510410b459a06808500041d49100b04500a000c242c1c0615134103107180c41c440c401a0034512a108043d01031102404c805500c00719003200500805021034076012940004e100c00a6549040854022080c200c211400b00c01440f507882803502031943c0c01849070400b07500840840c800c1e104440030b10000c024245844030b0380d90950781103607404e0400b100780001c6400e00c181041d42c2c40095502042c90030040088007038000010318058500316 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 963399352 1250 963398102 963398113
    0x50a080a0b070504050d03050309011409160b130302011818020a030c0305090c010f021912030608030403150c0c021f020706140d050a0213090b0108150f0904020f130e 73
    0xb00741c1603d0134421406025000300f4120032030703404640148c0046420142c00c800004000b25194101258540b06462452050f04001c074a03980000d10012140c1c00b4090300704e0048e10740144441d030010408414030009060160b1242c0c0c200719658a00c40c410000c1c400c140d060400c1424100000c1d00a41c030245c10980400e141c4210903000a219200d418800e4001400400e90703210701c20015200c000d6901c440804600ca00e5407180b10100c4580142e4003401c0c450841c14400c0e40001c100a81601d0090b0080c04540d03000b407000704040341c2c80d003456102e0303000f603100c0029003508091000c94400031100400b80d00001c00d004a4a00c0380707611506c030a4452056400c1e10410b035240e41c0c044800404041d0716419000d030500040c0ca244c00554003058218810b6a0b005260000c0c40481e22111450384e0f106601056884000d40102d58002c441198040c0700d01071004294002200080c007030388240002070b03010310501c00c001411900c41040c40720901e00c004003140320072050076180e5405000d10044420450040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 963400602 1250 963399352 963399361
    0x1318050a0603050c09311a070c110a050a0e0a1a030c0f03010e070806090d020d1b0303060321020f0a0b01151b060c020d09030b0a020d06050a080a0b 65
    0x1c0c422101503e600c20090410101c411007044112000500b41000c80c40d0f039040820186600b8440c0d1203864855140c03015100d0301e003810f00074880e6003141040c1501910740c40422040d964000360300100d10b40e01c00c10240c1c030120104041000700c410303074200680011181c0000b149504800f103031248188011a418403103012580b410310031000540709880d03015806008a00b0b214940400c2c50f400c034490240c00007034084c4600380d5180c0f4046080e40200d404d034228130240441c50a090000c1ea041ca1210300003860a05466040281010b480f03c0000343ea030318100c04040101846a01301c170000b1508030300d00c41d050b0420600e6401e0501e08030b03901480903100300b403941d0f5100c55010400c0591142c018605e1500c90f1307c5d0030041c0c2101c215608000d01044903070441170410b4004580700304001c0c1c1c004e040001310907200c104041e2030017580b00c00602c24048404820030009071242030144c0c1c8284054001b6848000c0010440054060782d00500d50122040001151b5040000381100070580650302401c0307035446 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 963401852 1250 963400602 963400621
    0x306090c030902060906180406060e01181d0702100507050d0606021b06071406040f02010e0f09370905070b040f120821160f0e0f06131805 61
    0x3040b20001d40080e41804000c601d0300d440c0024010143d0040341c0030713021100b0350000404841e1150002c0d00070035000c040a800d2541d0046418240d024070305603585d4500e042c0044080c407000200030074440032455100090b0340301d1007031141440200c40e4841c1805581000a400790042d002100003d142510b03043d00068201d10018454404c1410b4400d10002c050000040c081a0703844920141d601caa100c01048042e60400c108851140c0d010f00881001c14040d0310004bc9440e02244885101d100c0c8044151241d6552070384094001c209113042c00400d5035880100c44140c482e0350440c1101d018407501004407840c0c150862082540310701d090380c031100e864070141728240c056400782c01030030846110148030108900a92a004e00d000d4408a401e01d0607210300c810341211003800c0d520f000c3c00c00c0d400f4010038a08a0140f100011030600748141e105007640c00060a0ba03c00303550b0b40e440346c001d0641d5410551a1002142c0070706042c21084105580ca41a52506003041000d04002c141d283c078001481c100b8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 963403102 1250 963401852 963401861
    0x303181112010b010801090f14010b0904110a051c1e050103060e01020c030f07060b0622080105130308130b092505060304080306130c09030302010e030c06010303050a030212070306090c03 82
    0x220f0503110480b145e401d000c0c0500c001d0061032010400c150340e40c1c0300ea2900f1901030320584d00810070030811070340d180a65802d000981c0d51030341200c1003c04040c40b008401540100036150b10120482540c1c035040c2c904040700d13000d040395602ca040170b43c2021030030089021403604040d060300e01503002440a10550000d0500300d1040b00041c11058106105e10481d0007840700c000d200e07990080b4000f24400752044001100c40d071000c22500c441204508403400400050584200241480d000810041c68600c04080c0400b95100e001010005207100094042000c00411a032a9030440319082d034516101b00c1980d502e02046020307034200340c07200c0100381015010704980070a0300c101410403400c0d030f16107075200211604007400084d0b100f83c4001084800314028403030016201880d03a0b50020340303403541c02e002e404c48503034030030090480d0010020590024000202d5034112941460919525002c2c1c40b0118002d0064105085045000b0010300c0302507940f40d0460300135590441030030055841600810740466 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 963404352 1250 963403102 963403121
    0x915050c09011b12180f0f091503030e04021308030a0c140609070b0901120908030105041404210c08070c0f060201020a14030613060902030a230112030318111201 71
    0x90282d03281c02d8520520902d80d411480f035034102c035440700b517803100183c481740a5903401c0240161f4400c1401c106441984c060101c1c3d100d46144049241030840d02d0040261401201c16409030341c002641c64a51703550600003a000b86040c205481d100c4d003012100402009404000361030a00310b058070707030004135000310350079000c0d0150f5001010300c180307001c00345041a01315881d86418090700f021601141c140c140a1200f5040c455440e03540c3d251b041100302300031145220095052032444001700800500e4080c1000c0c0c101e803186000b50703821095004100d0f000369208400070f001c0b0002181d00b00411a2220045080e83d01ca0440354903090344504040b0b080f40101c960203070011f480803920149058051005541001c4050064100e908521103a101643c220354454021607070300004204c420700c201c3c841e07002d0f41d0340d200b01c0c20300c80c0c0d80000840410b03444040c0510040500c06800000806000c0d81c44000303104001c11540114548034203042e480498500103650144440003001040140103200f09040e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 963405602 1250 963404352 963404363
    0x2070f02030d020f19021206040b040302070b0c0c09040f0c15030b0913110a120c081204150311130b0703030f2c0a05030c1c1d040915050c09011b 64
    0x4d8001255444100044400c06c2e40c0000324070940c25010781e070511403c0d00c10b901402c8402c005083c00e2400030b01d403601d00d6104901c029000e005640c1101004110070412030411a0307681c02036181c90520100140d10504000d150300b541010000704400035101c017500800702a1000c00c00441000c00348803480c542251880141d811003401e810010350301c3d040300000481c001e841000c0d116100c2004803004210f1003c01c1c0ca03424280142000089170070030161405400324400c6d542814a0044552810b100030b444403000e040d26180b055102100d24000e072420b038001c918100ca185652070380403075220b03403149000341d00003418403812030b0000c00940240c2c024041d044880c0c42e041d04084080500c0c601007a0b91080780303400381c8032072030700810010000340400002d50750203002c2c0840200d442041042c910f51000c010710803203c401c29900c450801c040c525000080c2c0e00401c000c20720386410b06010b910204049009864482880400d4a404000c1d180703481c400e80302c490741000074903283c80b012a00114000c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 963406852 1250 963405602 963405613
    0x6060501030c080112110919110403020102031b0a051b03010c08010e0a09050a020306100501110a11040908130b0d0608011a0f060415051e1e0c0a050102070f02030d020f 74
    0x20301d00c401c506179800b0b40503020590503404d4a10004075245400e40f50f00400724902e14507880945410b103e641800300c50a00b1880c5094515070010b900d078052046415000c012503030119000100600071002c005134044e05451100d4440d02d410004842c82c00903090080d0300c5c0c01115070005010344c04040c1038808601000d00c442e030f40c610046c0040c0541d50401c0b1aa0301440c00c0b8000161030030850b050140056100c100f580340d08000c0018140c1000c500f2200456101e0301205012810012810700a180151400300d40400a802c1581c00781c4903003002500c030070b480c1080000b401880c0710080c109981044005000c03103a601c00c1d005098034100018803014078503450442d080d5141c05040705003488006030105041a0350760901c07104010202402e41e0109500044044030280c102d114404400d18455686090001c405031801c4514041c55440f1001c800004100071401d00801048002c0c640c003c0095684035100d00e44520138484070902240280304a00f501281c05002094101292848030b00429 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 963408102 1250 963406852 963406859
    0x50f0f04170c031204080408060c0f0301093c0507020304060509040f060b040e040201120e0c0d081b1f0c05030a0b06040506040e061e0102031c0e0607020a06060501030c0801 76
    0x4031039074801a101081c903c000c211582d00340c0c000c845100c0c81103009246150b1201c2c6040c5040e803c0a000034400c600000007044140b2003600e150b030070380c0e0640780041b100003100080e803034032240314402880c03131040041201c54600c094803c0444501e22000c00c481c0046c0322030340740e000c401c0e80d0f2401940035900c0803802c10300001015003081e0b03110761030000c10100080348490b074400700802680d005400c00c1000460082c200819542c01c40304210b82c0d808200410007140b88098075040c2c44905070f1003083c1c0b09200320241c5038244070548084d142600c0f40c40d000720410080c60000c1554800d1501c0c09000f04220f843e00200607a6018801e40000038415281c952444d501d80740d400c0d0081641d1819503910801c10321011071319864210140003e0a0500b0b40300c10142070070070030010000d1090b20603000c5e002c91180041c1e0f440c0d0b170110544034080c05030103441003452403044030080036061442002503280b00e200208080ba0364005102000c0501402080082d59111401182550004150369020800100040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 963409352 1250 963408102 963408143
    0x1603080903030d020a021c05030c071101031d07030c09092406030516180605061801020712050309010810060f0e0f040f021803030304020d03031805030d050f0f04 71
    0x81100c8140103094030314100300280e1030780480e048541040300503803020f41d00c07252840d09000e400c1c0c48441c140c14a01d0552501c8540c20b03055105150000b0080701d0034100160b9141d00903001320444da07510540444540036181d1540340d80d03849600c030030f40304400c4a400001d4211a948510803086410414240d0f520035010782c108040e41c825540c048400b5a0780c800080803400510040c125607641421402c40d039407034006000480c2100c05010704107070f480d04008000c0c030741d1550211440140c0c0920700840c42008400140d0030420680c0c0b00395191419102408100321022008000c183c100741c981d000d150312480310043e424145401a08041207181d40c100c3d07466030280c0141d039003400c0700904801c1440c401d2004103050300c1c540c151810f151500486c0404500801407040811032409800560552400c0e4002810725203282901600345031343d450305004194000610b50070015007150071240d580c400201c0d844014007007240c0381c2a0121105022920f6100712a0700503010700e411103a003005041103080c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 963410602 1250 963409352 963409357
    0x209060403320309010306140a0306050703140109020a0f301b021006060201021806130302060408031201170c010f031b090e0a02070b040609030c02060f0a0908160308 73
    0x12400080c400c800206900b5561400c0e01d60098500340145071202d030070400250583d03820b81c01c8034201840e50140c2e082541c544207416412690000e40214041d241e400090b00202a01d030050411905a080049889a40d40d002440408425903d40600c1d48050343c0c03c84030004c07451900342c113203901030400740d040d1400c440707000f002c0404840000525400b407030303607499008010005020158000c82842040d240c0e0511031200205440d00084d17182c078098040e01da00c400780c444045446641c021980326202e000030007843c000380d40d0291046aa50341c40300409035803900000907100c0c1710802c000000c103d4a800443c0040141e15100080c06200c150740d00560350341c0c907003032015010150385540c0008804100380c81362168103038584130382c22418106245c0c0e00c40c4002c001c003103014507401082444001250001015400b030b402200005200c0110f150855900c030790400b010750311480200300382d100b05c4190002080c01d0308540d110383c0510b5903200031044d2a003145a15540810707035801307010004203012100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 963411852 1250 963410602 963410633
    0x1118070302181c0b07030e0c0d0f0204050f150a0605040e151512010b13151205070e090601020606010806012006010803070b01060306030236040819030209060403 71
    0x1c0b40781007002410100e0180c10a50300f8001c0a80c921014460502c40e4404800340c01103a036103800d1024501010f091075071020441e00751400f40305461038030380900c21545044081e055000b0710600c080c1c01c180804208078402075646980030348550030000101c3c6003070f4440344100d500e2903c400741450b25110b07604000100c010810700042c003413054402140d03520351040074044581035070842e45a203201c1000420402058010154401040202e20940082c00e01e29200b114080702d0306001c025425481100e850100d04542c014060818007400080b41c0c10428008031003070142c0300610150303a08001242e459005880c460b000c90304000c085555944100d4054040c40c2c07240c040390410080032128075103010002d81c40024141c20101c1c03103000700b00c41d511080740107010070310781480000d0440e0000307143d40c0c0783d05144603030240150b110307038185500c603450b0a074104050214502c480d1900d1b08028201e90b000300d40700708200b0100040030001902078801d0300c3c50418050961130405045540380103d01c5061003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 963413102 1250 963411852 963411877
    0x30614130e010c020f1506030a08130305030c030901030c050a0903080d09020604030b09060601021c03020a03060806040c05040506010c0c12111c060b0f1e04110403030302071118070302 81
    0x200c1d103244880003406000c80300d0205074004c003021000004910f00300580031400a1006040c02e0500c64203540006405140f1500310070086c0d0b841c1400080d03400200480e6100404a02021075040c20040d17000c000307424405000e80307080c03050a507040300881d054032504281502003203d10380148017007124600584190903180d080010100d07402d4000620320b030083d1f481111900001c1c070422003040818003c840d00444280010040603032643c0940084c500b010027840e00b003690108041101038403d4000c14000d16030341040e85c000341010305209070140500d0042c24055402d201c041b490781d512070250311038055001a10041c015062040c02c5035545c00860302501c41c415001152141565202c440b003484622005484440070900c1c42c102d0103507624801050300c244007080034000b56071038801044c50540e90407035540034030050f6080050000e201008882034a00004035020003019056801400e1703183c0903c50100344511341d5400c00c5210307070007a1094140405d000c80803401850190300508100308810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 963414352 1250 963413102 963413111
    0x31119030204051806041404210318030f02010e120f070f02090106091a031905130804080f160515070807080708190c020604060e130606080108070603061413 69
    0x4000050702e6005004402e00401c40a00a00c200c0d0f10b4107100f010b15071703d07c804061155291170348074620303000c00c0c448980078610f200c91004028240719610455201c0301c00c00440015851328203000300122100348415006d5072800c0c0355000726507400548100b062a80d41120b44c502040080c03500d180d60406c1004460a00d040707c9041b00503a904104a40604842e695658865107441003518450002141918000d00104180002d4003402c001d54070107500342e04408110b40d01c1d840c00c0b1030041c228002c009014a07502040209a000c1c0100c3c002d6040c0f83c0c60411500750307120381c0c00e1012040c03500b4414142d000c1d000c0d403507100d4401101d40c00340c2045401684046d0400b089601c1311781c0250b0080d0421201100c00099807100c00517040102141c0034002c0c60316440400042c7d001c90060320541c09140c1c1440140e01c0080c21340d669290b8450f03e11002e07100c05000c15a42c55002600c1c4503800c2c0180790a902491201088640c4240b0449080f68118a07a034055040d00d8014080314080e10480e01d0540740c2c49 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 963415602 1250 963414352 963414359
    0xf02030d0204080102072f01110a02030106080c0a050a0e0f0c0412080a0f05070201090e0c041a0d0612050607030c0507050d020610060e0a050616050f07031101031119030204 76
    0x318070142000b030041a001590b42e001c80d1a01901c110740041c407104822a444465004510f1240d5080e4601882800c040c0310043d640c40e0300c0d9240c4920703a1802075042d8207100300828000c1001c1002103449200350b075044060b42d1618200182c2822a010307200030701d6100000034141c40081114150031908c0e20308214030741500c4820b070030040741540000351040c0ca00080e00c0c003003072030340002400b03400d10341d91600c907092100325030000744030ba400c0784180001000c4030004200d0320701180701207c0c0208071810401030601800001031005030002c029a2a0040c609000010045460034444009030342c4000a08610303501c4010507030003071608200c0746007007000520240000400812a400211100b500102034070705d804407004034400f0700d84d00030f1000c01c0200b4220280c2500c482c0c10f80d105440b0f0498881e0b0302c500001000701001e45031060090000e12411204814480c07010440d83c0a5900039102c0c2450b00b4040300054094607010040c035900c40c03104202e0b2602c5059901c1c04682c9040c3c1380d16003d0704e0683e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 963416852 1250 963415602 963415627
    0x90115020307060b210703030f080601200c190e0109060e070503091204121403040b0706020c0a0c12200a120c08031b061f060c14060f160215070f0203 66
    0xb9004605c0a00c1d072054405005054220207818081c001e01c2c5031016007441d003070b40020603a880081d002000c5c0181740d120080002e806001c0c4011802024129403103d400c0015a0281c4541c0383c80ba44e80d5040500c000490518114043c00c4262100c4444034142900c420004682a5200030207044e9940103143d91745401442c210010001841c0d906140d05a080035401c0031201803000d10181601a13200304800c218500d102c40c2555070305904000d005071100e500048290600010040080041e100501c000c2880590140c0f142112030107203001d506000c0389001d002105a4201d000e4990080b201c407801c111101e1303103540c0854030034412100c0ca4030555454040740c0c5150422200c807120210b00c08145000c02c0000c101c09903009a0b0900c03011440c3c0980f0220f240301ca10103006403020001e11004003000e10480048648202c03a41100f00c500d43c0c40d104602040c0c00505075644180e64580180308180b030303440020b442c590920b80e034841000c90b86880c50140ea5032610312010b01c0640c001800800317007100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 963418102 1250 963416852 963416899
    0x5030a1104120b16091509080a141b0a0e06131a030c0114030406330f05121005130812091507051218060a0b090115020307060b 56
    0x11102a8009041d660340391160404100130503120300b001046104078505507115520030304440b28802c402c0603200b06c1c648112810a00340c0c1240c005d51041001c080c0410030801c0c081c041020b108020340f4800c41d030b1200c1c00484145100001680b00c0002c04040c007400103954545508804010080d03c070f0142c80700c03c404103560880c8415102c0020a8008200301c0c182803044428101007460b048a0761300f0f040003c00c000d404094005010596a01100020740900342142ea507590800509150b09108101e1211078070b48242c0200300c40200070110010301030509103298a18010070001501c00c06981c1422100146801072036003d44800000016010803002d40c014140030600b044404070624101800d03031b190901095003181d84100c00c07000c11602960140507520340c10591071214a054603414034bc00041d002506c100c031380c41d000e0102802480802e0394401010080180d42c0c4100c1aa41d4a9002c81000750b000c880d0405078000b041083d002404541c400044650000c141d40c0711596140c030702c1300c4d5a9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 963419352 1250 963418102 963418109
    0x40b0a05031506030f030403020d0618050a0b1902030601050909100b130510020a0c060c03020307151a1c030302210403050a0e0a051809070810020403030e0904110105030a1104 77
    0x20240301e0305201103420300b03000d0812000c2d05c003c015854507255501207100b0919070740700640903c0d0b440c1c440100f54112030050381401ca420808441940e6241d0503c803860850075a00ad5001114408501c150320425000f038034030440c41611030609040804d0140701c10014000d0000c40405011740c00812221603200152900d180020384c0c0c80c285c42c0c14042408126184c0c12500c400350b6200c41712980005589081c11415507100b403912401c0301c035440c039045e0302d1806506d00081c005031500030400c45182c0540d0090708505200c080c141502c1d80c80c1c8040c040b170385c24048071000c074504d600601d50020074042d400030b0104420302440700301f003401130b03070b14020071010169400c0703001480001c4c1d9100d589130b1041c2c20b1232000c02e046440114140c5810001034068000048410140c6404400600303076031130a11000e0000c10810058403a44907003507560030000c0d840342c0011004a00901030011482c01c000e0400d5204640c00758200780819000c0d40191101e4200030888403400d40c07610691180c0d88000d50190004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 963420602 1250 963419352 963419383
    0x2040510171b190b1c02160515010e01061809020a091d0112061a0a0807180e030d020915040312092102010806010c05011104081218040b0a0503 63
    0x60140d0020000442103030042828811030883d001554080c11142c494012503108401403913541c112040c0c41401c4202c0408129191407010030300d01d0048810380c03003590b00180705405480124007444480c00031b01400307005200a184540006102c5070380100340e8007039110b0780440a0940c565a5060f90300990380508010342c00280d0190701008241d030148401c218004503220303803a0466052035581192010401c1b4050030b643d455050320380701609203440d88242624060000c6000c5602c41c502c1558860151040012008680d182964010518072800503803a02e9100603510b400003000080c030103074000301640c0c1d5011400041e25043d1040c414006c0008500c103144a82d22224600c0c40902600c0682d80046243c464101400c0d080c8408a12003003512035090814400b1529040c0c012a419000940001c0c025840c1c4003599035240810000303041100d0582d01142d10025050100d030f54540100781c2c4201c100520f45203802c00ca45801c2c0c0100c1c3c81c40c0409880c0c422180d80d1036001902d0b1401d100b000900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 963421852 1250 963420602 963420613
    0x30c060f0612120403120c03050f030a0f1802090c130909030e030304152316060b04090605160e091513021c140601020d0503100905010305161a070204051017 69
    0x4100c0d9030302c00086c07040b144d8205116801c119890141c0107101d8013a200564410002c0052081841903201e0302d2484080c07c001c0002c1d4070008c013811000b2075084010b900c2074001c000099000c1c030042d011548030031484152000c21902d0319080d480942001d17001201030019441c00440503483c104054002070600314110401c8199019004e8042e0110049545c80011103a2079214190012011154000000c00601c80c0381800b50034101d00400015040380c0e8000d040c41020380030705c212600414052021000c614092440221095400c5442416081d070403010340d00019001d840c85031001c2d181e8501c0680080303108c1141d21402c8040340e200d6100424a807403220304060f2440c0c91445046601300180520180c14149040040d50303401c00e034030a40c0b0411000100042a4001c00403000004246244083c030442d612440c03d1521619800c15251100c1c6510300d000490b071030b803402d003c4080c24480900742c1c505020b5800340805084000c00104c58403d1600300003610941c1040340f5224410210003510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 963423102 1250 963421852 963421859
    0x5070c031805060a0e04110d0207021503011d07020a081201170106060915030e0d0e01120204030804151e11011a0603070c150213090509030c060f06121204 68
    0x10085000c190301c0d031295500c00c810500842e140c0100710b0350504200e0030000c180041c400005000380a420807071480704007010a80d83c02c0c101c180d4002d00006031080703403640340c03d00c0700480341c800d94002481600031101c020802c44880061084103d500710070070748103641a0f154143ca4003403041e0f00400074014a50003540c0100081c400d070600810f10769030f03900c0003800824034200c00140f241d1403d000308250321203202d40c4000414001c4d03204001150007002910046818480060120f6141040f1280440c0c01c1040148203d01d0074401c81c0c0540b540080601d050030f0030405110103000f01c0170304003000c0c000b4510480b2030702c0303c007809401d01c80c400d16658034106030b00041840703003134440c520140d5450051003070146120707540b08815660b00804e40e1900c1404120141012403880c0300c0c1c268505149440042e0020200000711001e5003038885203c401e2205443d05001240c1da031080d100702040e146c02140100f01c81500310440284c00060040c80c028040c0701c10b921841c1400c542d86404040c844000a040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 963424352 1250 963423102 963423107
    0x80403030e0f030607030b0f040e0610050d080307030911090a06060e0f0315060a1508040302010c05070816080408030d0906050105040605060d1526101802040b030109050105070c03 79
    0x40103105402d4807204802905807001c03070f641d0746001d080041410303103910442d0181d44850b20307030200094004100b48050180c0480064072038905881011078101e503844049068102510709000c582d03401102c451940d40e4400301100109a0650201c07218003440c001c0c40c549582d4403001c140906091030000680c3c80c035050000d003010a507641604d004107121500d0490715940802c0d8034403001103070401001030344e8400d130010740d0214968000c1c030b29118040205030540ea9000680e03510441c883d400800030b01901d034000b41c0340da00800304010003203101085051040758181b10102c1c156403003403800c0d0341000d07240c0c80303c0c50654200489800403140d80d240440240325040c0104c50041000b900e04029587c01c140c081101407040301c92001803503403111050070403607150001d544014910b10341900ca8126020b8419001100118020000b07445407910300c0c204040a842640740082d002000c480001801d54244130280c480001560340c155603404c00d41020610a01030b03035200c0c446641d140c0105d2450380c40c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 963425602 1250 963424352 963424367
    0x220501140703060503030a03020f0c07060f02060601080114040c0201090c1e170604030f0e041508010c08060f10110114190b090f04020d12201606030e0a06050408040303 74
    0x710100b60410108001c140c5000c811a585298589005a541c54402c0d10295041c405e0100f0300c01c15200d19580056a90b500c2002c0c104060300903400da6401d9110306004559100d400c0c080d10050030001d040286040c9803980c0543c2015030140000b049010751a114030510b2006170f82705640b803800049103031020b07803200c0728804068541401951149010441c038141d41d018010401400d000d201e840300c2100c6401598400c05001d00100306210092031041440541070320b6110303440c41e40d800c0031000500030307000b00d50701032041c000507040315030810a20f01081384130342c038030000c1c0018012803100d039400b90f140030f0241c04042820403101c9616424101c0481c2d00060000ca40b48941500d800c08150b41a07884880e420b800c494030111502c081e49450000841412444c070000704901040107501101030f80000781100b0510078008a501c1c00500c640c1c58548400d1080c3c108032000010380001d01c8200e010f80d00a2700c01160310301c01c803100307400590f81d84000c489007600c00351000c05000c2410410164070010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 963426852 1250 963425602 963425611
    0x4110d12120216060b0112090809120105041109180f010c200a02010c08090405071d0f0f15041a0903160303051602060c0a060e0d0c020a0e22050114 65
    0x1189440c00c070f501840001500044010f140d103841e002000c803941c0c03180303010845e40c4c45111810801c814140c601131000d54041040c090085070549400034000006101d011302c9140c11009104144d08850104900d040d4010040011401141540c1c10280420001c410040380c004000150300c3c0610070000e404064690506c480418000d201000174032400310700703100441d6080c20b040c484a905440d100b03460f4014902c5840e0050310700420000d2007540710102105490350a01c80c1c0140040000500803c1c0404045054100466103e02840e40c1130542054500c803c60400700d5040039205c605810007400e0035034003501070a6002c1441c2102c0c1c030b401d02c40d100d1a88900e040000c069850b599026000e0300400c0391450700d0026203440c00c0b0540d150802150200703803000703003a129a032040d072038060000d081c465081e104600c9002c000802041c0200c814400a640080c00781c0d80c81894440309a00d001c500404185420b04402c1d000c90407400900310040c0301d5840380d0000b040304030340c44c0900c000b1518000d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 963428102 1250 963426852 963426887
    0x13050315010b0a0c03020102040b030403120501080d1b02190b032d2d010f0f12030512131a0405010c080103020f0d060b06030408090a0e160804110d12 66
    0x80040100c104180b040f1460400b0a0420040095060030706a009000b5a403090a05850000401c81003540c0603500720f070481c10036101080aa621007144c0c541c1c6004125100020030f40c80150303030180ba418400c0364441580700412020019502184481c007803140b9503c01d8045000200602c4401828046441c0c00e0920421012140c251650b03003d843c1690090000c0034258080203101c03605902d9224501d0f07008603901550345030365944814007602d20b007907032003905e4298a0916003c103d80c1065178080d01c4043d012341d159424102003404018000301c0c0a41409908038030b003c22400000c04140464141c400c210513000741c2c524040c180142940ca0110320501000155001400180d40e16048104119402d855021811986103801801000160300c219442200401000700308040ca800030030350b9171070075608100040d964a00b40c4401883c280c424000341008801d01140702c41c883d40741c25500500898000501e4000c00c80400da80740c0201d401900c1c0711000c85500104141c01183c541d0005601d503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 963429352 1250 963428102 963428143
    0x3020a0b0a260c030606070b160e0105120a180b0a09030806010f140c01020d0504150c0507081c0b0d110301151a0d1104060804030206222303130503 65
    0x1040034442c2050300030441ca0315614084013050b15a19114141e8203003a43c0300c0220101420002c248003843c015262642001410a03845040390354480c4058441052095850b9042c5444510400025010256004180d040b00003c22000310305201e5400303000d43d2440b14005805206424000c068200090602d8103114840042c500d00c16401900c030003401c000140c00076100e0002d045d020340a403181040346142d05040c20b052006110140300e10007e940d15181c01080f00c0d030314141040d1814021200301800ca6107051094403510350305220108080e40c50b40b10700254070383c1400b0005990003003d501c191841c58104049444d50b04003441041d40b10340c0c1c40d041c000b400078074090080003115490741804130403035030101d51f035410003400350054000100c0e0411480d84654071148002c1500804850940040c420240496005000c4a81e00c007048003003d100030b0302c51455900e031a4100841d025451088226007010707540040c071b09202a11000104150714801345140070200741c82e0520403003207a44058901c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 963430602 1250 963429352 963429407
    0x70f08070c0914070809030c0f06101a0a050c030706020301060e0307090b1c051501060f08012102271305150c09150d0603030807110d0e0f0a03020a0b0a 67
    0xf00f24900360702844614000885030f980c260300e10b0450041c00800521845660038000700d407000403860512894500ca030f00a4a99038940d040060b20503901110310001104200c240000c0384550b00800d484e500c020102c91a0802c07542d50031040ba807090340802c001032110100c4042506e81071201030000c1c402c0d004107220407011240024022a403100c1e1200c560300c400850070040143c10702c4001000040201445001c1d0b1b03444401400303540c0304558280c0080c2c103003000402ca1078501c0088000a003407100c06016008499424822040c0303000700003050113201420b65200d20f0341d00c070700001e11031705014200708141030301c0d0f20701a85458003038080c407026405100100815040170400b561808030045032030310041c01603180c298145120300c2d030140707600908010700130043c590098240c600900c1995501148200c020282c0ca0319440d112585400107020042c0c034814038034002d40045030810300200445015035580d030000314070020a5125100c1500c01060400001c1c1d04040303091900c100690010010811 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 963431852 1250 963430602 963430631
    0x180f090506042d0b15070305070201180f0e07110a0c14010905061204030c0b090105040b0619090b0103061806061403040507030f060902030a031707020708150705070f08070c09 77
    0x1003050f103280e00560b591040c2d02c469a10301090324804000d010a9a80e26441818001c2c61075100880c10323408514a420b0521050680d0341107501200c070000000c481413400e1813481c8000c4d6001900140410a45c50588110f0081c18030166032014800d04e00e0368202442c01261040403000b2400031410b10a48a2007040941c07502c030125800428000100c2d1003036034032440d0660f00c0b1a0110b001400e00e10289003005a003000540c8968041da0240900860594070f4000300301e1280255607010741c42c100403140c01c1189684c581c021140e02da1050501051903a160f411004203014002d440c0b51a00d91200c00c20003415030403a401c0741c4c5c00064202c2543ca5450f25444999031480684030003070134100616140700a015140c1e019400056000b0140c4042c100c25007001044080b02c070b1701c01450741c8020808200d4190000841d10112030a4601038084011550b03581402070700c004003c40c0c01e0100400c070007800540070034032407207499201d2075203182c59406a040c24010b511080d08640342c0c15140c100b90614884 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 963433102 1250 963431852 963431921
    0xf091b2c0a0b0324010e0c0901050d0b1c05070906051507080d090c090e0f062a04050a0f0e0a090206040b1e0c0705030105100f06180f09050604 63
    0x860252010911641c85000700c1d00e00074030702c1c907003c40c0007400c0150640f07481412000d00e4102e50b0381640210403600e070f101f0424514410107640c24045081001000081d42d1540c100016900c00100a02d640c82e0f000056904c0054402904541d0b43d0442c003420f01c01d40781c1612520000e040b040d101c2d45044550030342180c142d0721491101601e26100480e070b800f040100d030340050504a9205038028003031903481d41c20340050304080109581c10302508807116620080010603600c03407185110403114072081c0c6c0411002100c0324810031001c2e000c007013001280036265504542c0c020045820050326080c60102d4002c250340c0081c00d140300c981c4c01d0450f017402581d2180d041d5800c0c1d03030b881d01c2e10f0344d9948446903002000d00036109091603e0140030804401c04500404c172541100c83c190000d00c5079540c0d423a1442030864803030150020f1a10b07124401c0c0410b600c15040194084451110034a5258071180c1e032410044e0b0700d52000105a0b10f6100700030b500c0c1002d0190804002480b8a0000c00152080e10b074103045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 963434352 1250 963433102 963433111
    0x509030a0507061b03060303021c080a20070b041a072109020312041412030703080601022803141e210109050f0c040b030105040f091b2c 60
    0x9400b05104040c05803a50000c4d0103840b4000e4030040c0d001c0e0310b80010340030341082d10083d0054000c0c3d590200c04003560040c0b141c8480c0103603449111316941c1010b40c2c07005000d820b0394000c1a1514444814076020250024104140510303011940707441c240c80e055004000748074201ca880209102405140c5400880c9442c400c10b0001501d1981c58101100c1f8006040004011b9418890700380700201142c00c0300d00500941d1500c44400000003024020300c82c0b000c109d0610b00c1301d580d108100c01d001007807003907083c01d400c804144143c07900321014190201880d05010312140e02c2e10801107907041015080390700c83c1650f1600f20070042c1002250080c4010041e0103210a075004840001d072070300081c078180b06540546009000e00c0702d5a5840b420300c41c00070701b421200c440400b844080414642a40081030f6001c8810a550071491031307007824248801f40903e50800c03000c03d0745a480da00300181c0100c8020756180a080011400107103001d40400c140b41e00780d001c4000001c184c992211490403000c8a00d41d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 963435602 1250 963434352 963434357
    0x306030f0812131a07110604060e0106060908030f09220e07050405060108070c0525050a050a032418050109021f09052202040f1a030105060301060305280e0609010509030a 75
    0x1340c0c0c0c0c0b03800054881c0d410301800d013251409050200010400c2540c8160b0000840384003c1104645504064403805c045004034500c1e0f91044c8940d2100b00c174610001c000a0030042d062840740543e068020516602d480004151140c035070503603802d032000c200300150003802d0882c5e00b0300840c14031b58006401c42101504043c20041c010440d10180181006600d00c0044038860115642c3c0c20b900c11100001110300800740f01709110040024107141c008004d00940380c0050700030356240b1100c0c0e91900a07000642000790043d07120b034103540440d02d000080b0001a4014400401d500c2c10510400031128200380c408600c45865503d0b1210940d800321b108025981c0c2070361003a0481c0700142e030180c032424503010900307201400000c02040fa001c052400b00c00302c0f644c1ca941038500c1e40b140c9202c0f00c0c1c240024010550440740500041048034407030b40080380c006810740207042440900c000c00031243e00403891444907407038035501144441402004080d501443c0c14000f0000703400c011400c55200d10440c40003004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 963436852 1250 963435602 963435653
    0x1c050a060302130f0905030f0405090603060c0f03090a050106030803060f0406210609020409030f0219031d060d0f0b0a051e010e0604080708070515030708160306030f081213 76
    0xc499081d03178012075529802904407600c402003515003c216501034051280190901008035404d410000745040c0940c511001752410440c0c20400061503400080070301c02d461081282d844085031081c42140040c50241a4407966458260240860720880c0d4190b64040c070b00d402010000c1503231808084d081c040325003180700704280450030180080d180902c4040c0d80a031401c03500e1000c043e00075460030200e01807502902d401113072451080441c00f18001c0081d010a658065144050854585a1206120050401342800c07455801d81040b554a85081c030000c5554180d42c1140c6d20300855000d00a050480c2e99040851341d0050007525070b0700c407451040c18403410201c00305882d994802900c011380812412650065500c0407040d03a80d5070700c1d1103001d000e29846100c20300034002110803280305051680350500035489001c88000b91115504501c2c0c1015950b0b400400061001011056018060385030036803140ca041074401e2104201402411b0010070030341c400000682d40c06041a040b4060440307480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 963438102 1250 963436852 963436871
    0x29010e0105040e09010506010f02030f0301050108070c2a05041808030c04081c030b120c0d06061a03010f0503030a020a14011107061a091003020d06111c050a06030213 73
    0x3100c0340601c3e04083c0d40080c0706800c2003001a8150700041c4182c0003681d5505c0d4980028805903220300c41c0380034102000008100500c610750150b044c1c1c9401100a10300319100796683d84070018103402480c00e00c80c2202002000a660070740e29180080907140466080010090041810740c410040103002482558040001030b44000c092054400404d120003da851402c8031010558820b400780d030708500400e241c0380040c1d140f03091144540c11a480400c000b0020385c02442c00b04106051440000c0740c481d07407030340404a0b028203800e061001c08d00d605040c40780ca07035041c0504020208a1904200c1c005d0780240000c1c030040303500140081c00b55410130030070007011000e550814050584e880c1c40b040d115100080b000c081001d039610044401080c82c4c2c00000c8080c00d6801c000c00e0305010750708002404880501030000d0310b00800c038030501500c1140001015208480004120b8011740da071804500310715194440021401d00a03c1c2d4081c1c05282d0810400b070071a800141903184228080a4003a5690041da = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 963439352 1250 963438102 963438107
    0x4050c0a02071a090406030b07020106090902090c03060d0c060f140a05040509180d0f170114011223060909062203170a23090d05130f0801090629010e01 67
    0x21840308001505c10b001094590509940c0807005541c036200561030102c001030f004c1c1083c8143e50032154000c00215080d141e4109a06054001921a56010007000e10f26800a4103074254100100104d85511881041c0701501a081e00034030420b4011141d010007000c91840d610030201c40913264211130180725030326000e40c05c11112030142103402c0548a44444080884d81040c960b00c2402c001e5503d140040c0003811103002984420302c50705c086049400060540d035030003251741640280e0000000035071038440d00688020340d0318543d84a042184540c06000c914100550895841564240102182d04180c950395040000307004c00c6180400c81a18140101842000440440e0107902682411800c1845004005080c0030001010700d03124504100c06030554402e4181c4501761750406012003a082c01c00645040c2d1250001450071f820350721001c240a0b0004138081c2c003a0008000001750340000c1d103080f9044500320b24507240b0003003902072048085406c1c441d440c041c10300d081c68204148054007005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 963440602 1250 963439352 963439357
    0x60d0611070f05010b041a09060906040e011404021206130308040c03060e010501050f0d35030108010e100b030309010f180603092105030408030601020c1c0204050c0a02071a 76
    0xa21500e0b4125280d000e20405402803a0940b5089801304000d81140f91101054040780d500b040d00304c603200000400b039241c41009654032820240c40030034240c02905980782101d03442e40e0356084040c02082172006506210030700e076007601e40c5907000340518188500e91880381960307240003d0400c041d02c0e000a08211041901100560744404244001d154440d24940689001d020ba603010300ca5200c0d00190520b00085801205030b00f00703211a0101001c1da400c015040c02d8452480b05581510a20311104c0b055903000f54001e00c00c000c00020f82d01c184818881c207098001446051150070420f0040d855503001c02280c03540742003402c000119205030801038030030340c9402c803d0b009440000603000070b1181c2c250b00558046840b54400d400c6400002003a01044801c250000b800250700b4000a8001a041001190403100500441c0d44000c650300003e080b5014802c500780c00040317052205001c60402c0c3c040c4c160800800480e0f00d013800c80203003009654801c00e1180d05440301c60128001c5101540d03008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 963441852 1250 963440602 963440617
    0x81e041211030a290606031614040506070b0f060303030f0a0e0c030d090321020a0f06090507060e12010c0f0f0306030f08040305070b070201050d020c250504060e060d0611 75
    0x40c1015900004e2403030b02d2000710a4052580520b84031000031302c01e00c0c0840c105c80c840d403544031203040743d01207010085490508080307441e411401c081001180503607464020700300d00e40c40740603190941c0c42c3c25403240302649000f5120034000d034801e00c00d0150441c12460043c0c1e224800c000c0008100000650441c900007180c9103442e09030182e03041740b2154613400f51005003170707078010b07a00706a41403550503402c6607a00c1100720b03039070060300600c0c000b000244844141032546401340d540420744414640320316040040326032245003c1402e095500515040598a8100420b0950001c103c0b03101140400391410450840b40c400b004000e8816a20280c020b512101c041c540080c6a014500c1c0e251030050b034968043d01040d1031030f10580703a0002d501c1c2c1d6201c04581000368184d40702428103150301021406900800400c0416015110009810201f6240f80d4074808061100384400e451614091204480701500429a0740c0740001c2000803c1d100ca80b010748289602001c00150700745201d003404894000e191 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 963443102 1250 963441852 963441863
    0x40f0305011e11270d110319231515010906020a0506040224030405030a03050f0712020322050106090b060909010513060302120d020606010906021b0406050d081e041211030a 76
    0x900801c0c8101d207010a000301b1001d4048810ba1110142001c1541e14000d5006010030895444041014901809291084041d01c1200c02403105242c00031400101202c42010b00c40c2d500d106480a513a100c03000c040105040e0029048210080d01c51f60380f0340304020000b90007003101c60082804001c018460315510b404918000e1f869041602d082030b02c03940301c1c000980019013400c022646403448035075098000e051a03103802b060075107512681c0000c0d40000b0901c242e42c00110222091851301da41001c0102d6100388000603140d030134841010200c550559650340219424840d00019803103200740c0130305540049990540b8071040351000c1002e08600e070002504000d40c41118500f1040004054034070911540980c0c1c503681c6c41d24011541c00c1010703c5417800603804400f019940c020754602007040340102800102da01f648176070108071041540c1108540d985000070340c4039032241c000e501c0d465415182d200e51a282514005036034142884c42c0c500a49003200008000c04550790802c4075050f0640e004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 963444352 1250 963443102 963443119
    0x150c300f0d0b060306030601170c1011070b04060909021c1107060f090807020d1103061815010b09090c040f0902040303030b030c01021b06040f0305011e1127 69
    0x449002803540141c0110103003142845110b01161900b41d003964460301d005401820980e203445001010038507046c404001c6400f1381904800191188100d0303501340720541d00d61501268001920500d0b0440c95800f01d62210030500c002d0081030740c0800d20310100e075000c3c0009612080d10717514030307481c4800e0340a00100303242c605924825503400904c09002200c0c0244001c00482241c2c070034203000d85140305070040191030204898401482c152a0000405000d01191440e807142500824680380c4d0541d034801d406075907040b030010002d0741000054124801c005051000354580810b03401d807400780030840b501c61101c8200255030031624006175070040030b0041482815540c2c40c1d9080b0700940c4107000c180d0000b0b0400d01c07407080324200014070507c5040b060340144480950b00e00a0822a4425a034003984a003040100180803440001c0c188040d40c020720000030f5502203002900740111a14809008090520800f281d00c07845400c103449400c002400f4030321342400504074604401c10002d4840d503010100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 963445602 1250 963444352 963444367
    0x10303140d150f030210020102070201050405130e06091608070e070804052b0e0102010203061305060102120315010924081003140a060507051e07031b11150c30 70
    0x803c246030b01100e000b505e0090642c0c2c80180c0c101c0c02e0707202e81c05000e8045074080004200b01d06105203444080d154400c4000340c180a04a81e9a0601c1c900303960fa80c403958400c03400d0b00340c080915801c0c000180b54010040540707528000c501c0daa0400005c0615092101810014051140c02d014640040c0480307400703400a0a51107815280540c94a004900014401a007540d0954014800c4a00942d03005000620302e0000a410001070300303004002c18110b003d108500c1c8402c0500501450003035410103140c05917400d00364001005031030380d90b10283da50204808000c0d07016104001d28000b0312820320b00070ad120394440c548885034405941c8001c00d20000b00e010803190344400719400117410300c60f003024000e688030044120389138000c83c0c04103040b0500314140310700d2425003413000b040d11600c80c0c01c04d01e002044450f00d860f01c0308a0040d09445105203603100c08060b1410360039004d00e01d01c1036000135040c42c8150900c0e941d9180c0302080710901496504420342224294218218074030241c024240da0340a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 963446852 1250 963445602 963445619
    0x90a0915150923091305100c03060e07080412120b090408030a0c09051e0f12030c010507021b0913080301060306050a0b07080a0804170a0c0515010303140d15 69
    0x96031003000c200074242c41c01c242c0345840500b00c0d1040fa000080c0303509225103540d108219005a02c900441d164800c182c070b1084000342c180160b03c99490141c50004030146000d0169a000e03030020701401c200300441d02040001000035428207a403005506c3c1c0680e00650713030070a1000905610a0b025400b580150800c010402040000c503c550801c080600045100ea101551a4403480c060aa40105c40c81c011043d54800f080700d03828815001418a400d08010f54082007150b12400041840c84d00001110800c80d0424042e20360804503078401801500701c00245407564508100b039051007001c2c41400710f0000500302891200b05504a501d16540c1c0d65a160060001c0c007491185900451141800103550b50418081d62142904160441e14207071002a003225074490050040769111700300044e1442c0600c00601400c0c2009071074a40381c144894500f8002e15000000141d030780c00000d010010302c0000c0d071200001071307441842410b15403220400c0d40d604014010510410240882d443c40000d9a1b00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 963448102 1250 963446852 963446867
    0xe2e0e04020307080c030408160f1e170f1c091a06091612050f060103150e040b10030c1805060607200f1e01081b1c0f020c01051803090a091515 63
    0x18451f40001140d40c0d12481e4044410711509009018cd1a04130350311460b400740403000346035460300e043e0514500f101da05901c41030102840381d82c4002aa50b0321004003000440081000e03008209a14140301e0f00d8688000383d00000002d0219811a5684040d00103650003840710303041648240701c0500440c0303042d58901a1102c01228650300213030400030590102c4141c54424425280179000c1e0645903a5551280d180540d006800d0303105c03500070542c00001281000e95144041d081111690704d80100001c01441a0b0384058400c501c42c00782005500005031031002c030b6a820502d0310f20005c0c0c4804203500020b070b80e20f500340d040c80d4000f410300c03010800031020101541c03800c00090320343c4046034650748140c00344c40d405056404040f4108006040080c0a9254010b440c0c205401c000b1407101c5d1003031002804c1c1d8000c100255044d070344030024481c1030f900c41940750341060b20080066080c07105001c00a10380040c148a030500d1b040d41e0b0381d0718030301640d14a001c0c0001303001550300d001072a2502050040000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 963449352 1250 963448102 963448133
    0xe060108060a091e033b0d020102210d0606030b014509050c120f0c0409020f0a0f020f03040e04060608030f1803010b0d030e2e0e04020307080c03040816 67
    0x62943d182403681c0542080f816581c00e003a501015000b11001c41c01e00c07d80c2c04040c4001e81c15031003015145170020740780002540300320780b1881d05152105d202180301c10507242707650031600c20326050000c01d102c0e03641d001ca00d1840c110707008600303920a0b0309400e644802080228000850909405103802d036411061110401142c0c607000c8100003039038981100751024020b158000700f641c008980800c4c0800001030640742c105c10127201c102d25080c0c1e5034040c8002c9a0100388842c65005000c01c411542c10740101e140c04200c032a500150240b10003200d07441d5140e201d00d0048500110860340843d0030302802e0303032150000c0e203980b804580c0d45011107403a80382d01c0e4200740307100c100c4141201d01e092990f08045c0203401d090f08015014200000b420303a0306564030101f121800340c001160718000d080001076000110607000d0080581101c0b024010f1008106604044030341e80030324010800c2c415419401040d040d40228404c209680700d0311107207088861407064882d20403003a1459200e04c0140300b1484408002e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 963450602 1250 963449352 963449387
    0x1e05160b1c2403022d13320612060c1b0106080c0306011a07060b13060e09120309071502240f010e0402011e05070c12060e060108060a091e03 62
    0x1413100151a5520b000c840100390701744500d2450040e8010f0400e8000321419840074100840c40c540386200421010011200e0140c04542d40e1703050b044036100b00014581c0002c01030307411f000c03c00c00e07014070380d5901c00010b0000010280c002904558a0500380861203c0580c1071000703020103035441001d84c1c3d9a80c1c0b40d24a041c0b01e0b009a100004840b00d44010454071312809903c218200102500d4580c01840741ea801290040b8103808600c0014031079100e1200a02400c0c8042c4819080840b5070a181c0251262610300303040c0c0030402e100342e03080300180d00e00c1100e1ba0084403245051032028200e060540c18008a4070341da0080c1c07c081c41e5a80e0840d0741034414480401d60000343d0380c1c3e4040c154480041a5000f0340480c16141012010034050111520031071110f0500c903103401c0256803100d201c12a558003d22006001c490510100310444c000c07000395866a10060103594144030410351914000f60401aa040da2540d0450410070f808909440403903000f041e04070240c400e810f028004119a100c140d00c4c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 963451852 1250 963450602 963450619
    0x1509070f0b03091507090504050a0e1e070306110405150a0206060a0303122a1205090c010807051c1b021006060905120a1e05160b1c240302 61
    0x41c00d0629600b901e2182075403000801c0d40440c03c10001c032080e103001d8100341c20800603040c0030070507403100d0090900502c03140f0300c00950100705a80305410081d40d040d101d070710000404040c0a0a080004240c019660410800640c0c101c8803c41c1e00340c10301c0fa90340410340062003880c15070180c41c20354002d0500039800e03809490f4555208402c02800030f249020040c041103004845100950480d40f00d6111803090100500740c00780007014074109010000003600004003070880c10101e44000e07010709038022a007807004001c0c520302c3c000041c0401c100102000100038000c100c40890240244071803001120027542042039180c1102201c2840080d0522080544508103603003d140d4802c1c440d8908a03403c2d035031182e03510f41c1030104120030030103c442008043d10400b0b80c860081031041440c01c4a043c0d800d9243c0040100c94500b160420001207118040000451802c000350321600048800003151440e00c400224480c0340500c2c01071100f0384050800440b00d0642c1c00001e02d0104844054034022241c1c0003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 963453102 1250 963451852 963451859
    0x6090a0c0803130b0d0b04020f0405010e06070b0402060a0318210c0b0a0b030c06040608180f0a02090901140f06040e0627030c1f0e0303130809031509070f 68
    0x6981c2d11526203181050341240d9800c0001d4804e541c06013902040361500403494a060b10001411b9070040d40108058450001d010480b40da040110a59107000903945242081616101c506007048020300c0640100000120301480c10700c00d03801007202036151f40b1803160f6030982d400c01481700c400405c03090b1104951190602c03a03050250880c000c01c613074051000d0320a81d883c041d081014145080a654142c89080c508079405d81d20100a440504080d541e899071918001400b2081800000c00e0160b058000050b600056034003c2004002e180e01550f0400071078650000f0340d40140541d4800808000d28a02071010386107103204400d000c0c4404440501545101da00fa15844202c00e071071b48164900d0441c000705501d041c1d840c008203c607420307030706603410a050101c00d1800c0c59011845441e003e03500e50028100e00207107108014a00250700011420352801c030b001084020052a070240c060b003000300b04542c2c950b8007004009401c01180f00580c03c14180741102c0ca0b03a0f005207020325544148900c0012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 963454352 1250 963453102 963453119
    0x231021e03091b13050f0703290423130308160914011e180b0702060711030f030a0e0301140402010c20041811010504121707020306090a0c 61
    0x40c1e00030742c122009810700715000200602d0b4071001e1015641c020b215a1080c2c0319085030f500c126481803800b01c103008081d10740000010125a680303150003400c1824032641202190001e4420140c4140070369000800e4180e0600c2003905450851a240350381c5e44207003c0103403814090b00c408506034442e441340145c50300e03003480c0c516840720b03801c44070310010707519240400400000c1740c40e5041415041c10b00120070405210b0f11070444075001811808030342d0022102c0c0030641c0003207101c002005c3d210046070400826078000352962040040180020680c040003240599060099860300110013040300c1daa5040e820029241c001507040092003135107840c0c0c07010320240721040e035144915816075a00e00f061752166903400c0c5070711f00009450001124486034840640b294815040c401654400c0c1613511903103450002e8000c0d051810321410084240410024041048407007841160303c0441c1400c14207410f81401c0c0c4902078100d010f5410312416050060001e0701050b4880c0e2540a13a41d0b03d0126178031500309 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 963455602 1250 963454352 963454357
    0x60a050112060203130503070b0103050f16060f17011509080706090e04050115062c130e010e030a0c0510060608070c030e030f03040609090e07030231021e 68
    0x103203007040700c0701501034001510b10303401141e00c400740c000a0300c4202c1d06038450307134910b07040f82001700c640b02c035018014810301004000760000083e001009003c0311010740341c81d00c00100c080c030421090000b00c0c0920b440f458081c9010358031501058103060300d03e40e510035080c05405400c04212000c06e0200c507001c12a001e003c94044250348135500c07139007004c6140040001d03c90000034429034865680b10060450340c8140040c02c0700410040da02c480541e65500c9400c440c0300840c1421510824440341605681d440e0300002020700c0655440001e200001c4141050150480c1c20100c0002e0000062544402da0000d100d410210300030000c4601880010b00c405044500501440c004940305c01e0005120510171a400c2d034110340303c3e1600d0101d801c40b12020902c0d014250302e45a0803500b01280601c1800e50050001d0700811480c07105004103a6600c6140d515a000f6000c064042d002600d1060900d03411168080c15603402c140104100c010b40507032241c002d4010b400791034064036284c1c0200c041222040103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 963456852 1250 963455602 963455609
    0x604060501091a031b0301030506150f03071a0705070e070e10022104030519030e0f06030c0a050c07152628020a0905031905060a0b01052802060a0501 66
    0x1454103812425561100d11074000422504180c0307040f100e030011706001c3e40f01550003144550000c3c107040c104070101d040020f0420350300500a812091101c8000c1c1d50009500045414900c0d101036030403003a00240000c0d00c0b17222030182451040120000c2c480c110016600e110350368070780d9540c03c450f0f203076801c210f1190051508200140c1c0580e02c510350000404810314100300442c445546480d60300d982c0c10342081c94100c820700c038074105e8117001420300da000f03019050501c1048a400c41d43c6481440003505c01c1c000900070741640700000c58620036041c0a64100d0704000c400d01d088841c10303981c490841d500107110a6161000031140e02540c070a15583c030003100c60486462120290b9640d480c0d01041341e000e1819105140680c2e9840917185500c2c040c070051001c3e0946580f500a00c500341014545448004130a071120703038400004003808500c000ca200d54010018010201d0348107101c800480e110b014280051580202c4c034010300c1180c2e415406500c04c08521a000e0b180c0c16070710380c80c814044074401d21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 963458102 1250 963456852 963456869
    0x20d181a0f0a180b16030f0203070903031803022107092a090b0301260604020108180703150f05060d020f1005041d070215060109030f02030a12020105060406050109 72
    0x502080708000340d0f40203d07020100c881c007541c14000c1103031038800030307603005880c101014803055217466003040c0d02d80139008010a07820b07010340c554103021a0041c40e604485c400a810890b084a01d0710b9121400c1494400458005180511004084010740c0700300c1d1548200c00d02c688a0b0300c0c00040c1101c200d0081100f8401d0f0409410f01702a0f4200002c20050f90940c82c01c000c1000314040807504e503003a100a1400391002801c803c481c030769a218180c0c2c101d80341041914459002e0700422006071b03485642c00d540302c5295008894410070400f95940b4141994000a12040d50584401341075042c5901030041c510a00406100c507440300c40a00c2145590341c1d40207500540d010000840f5400c0c200810796440c00706107081c600e0301c1da80b80e02041d5206014214184440d2019003800116503040180141ea410340380141700560501e4400a800000c05d44001043c036540e026a0300300b503560a0080c4940d0303c0d041105207440700a02c0c880240208000c4a565204510b010070128a55201e200c07601c00f0b940542 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 963459352 1250 963458102 963458131
    0x105121015021614030a0b181227190e0412110d180503100b0301050702060705090f120a0620130b0d0e03070501050603010b04020f09100201020d181a 66
    0x181e06895a0000d134052a509441007a0060000039030403002640710310b025034040e801c48620111120b08140c44040d050544a0042c40100d002d8169500d8000c0b9440c002c001100e810903841c0049441c0644100b171032000c01d40d100b4030014076030b6520309170503110b03900c5498002110307071800c038050710498414116101e007540641c848001c824000e0303604941801c90014003210903a61074000a01d000c0f5140710402801d51500240786460409005003504030b0482d0014104d0f03480c050200904500542044512801a400036049603072182140f2559802d1002d0640b036151a0314144840944030480380a201c0a20a054a810705a000d030180d0304428410721400410034a0006582c1e85c5030030901c1d2050802c1d0350340100041800c0c0c100b00034a1110b110300008507541c54218205801c407440f0304071142c041ca004101c2d403544620080116102540210348513480030454130401c900a000d1000c80d8800c00c0e00e480400100f0180842801e138000c0d205503414207161400310402da182c40004d4604c0d88401c0240c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 963460602 1250 963459352 963459359
    0x712230315010e0301060308090907020c03060408090a0302060304030519081b130b0c060a05010b04060519170118110a0507020d11030709050108013801051210150216 73
    0xe898030107550000c149022840b0041242c0003900f160055441110980d0001610390b444d0b01b0304401003075110310a800a0140d50881d0342c0400c0c2c4607440104018142c50000582030200d0b0317120b04210700030719000381055489140c580307805000c95210701e601000e203048002c495880d00d482412300034403410710210705104407803c2d15005d05464015404400200c00f41a0000c40c0481600c4090041d9542e5000101814107004602c142140c2040e04407140d031a000b08014440c40b504042150802c44052314404440c0c105624110b984170b03038008815440d070808200006040d202c08940300d0b07040d50144410428043c1d12215490a03202d4040c0382c0011500621402c030140c81e040184012860040741d01c01c0c081144800003a003030030344a0300400081581c0704014041c0010900c81c110b141c40840300c1104030844142905843c0320f113002e004101d80c07298464200996403041c415246075030a903c0500202c0d0908024031452641a8040c0101c0d507201480921b01d21071001400458500b2481c0810a03441e04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 963461852 1250 963460602 963460621
    0x31209060d1d0a0209010602070602070b0c0c040510090e07050a03020402452205070201021b010c0e0a0f030204090221011a0a0806011806080307122303 67
    0xc00c00c070300c9046075651900607070940400c207041070b410042035001e03100d69040d0f403042045101d41a000381c411540f084505010b000e400180d21030a4409407003100f03495001015031a03140c140301481294206091006014030140044000780c207035114110180010348210f4605640e4040510840ea44490080410009410164007e1080a1a242d0f5440250001200d4100780c156200400c0940d0780c210380146075040c501c10000001e642c0b044501c45420113a410000c0710a13011400c00000311981c0701c0c003040c1520700035811544075a5071b202c11a402107049100e040c1c000e00b032041202000c650f0b41a00040030303150104a64085e40c400d100707860314a034119000c1c80700604402c40101d8001602405a0460112000c0d1540350707103109600115401400c54042c50074480c3c07034000c1c0c07030091032200d9003400076540100c4c100e415204070341c0300036544461014940003d40216441120b081c007002900400f80420f085814444110984030b21420701d000301c201c4401c04144c81441d1103d031100b8404181d0122 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 963463102 1250 963461852 963461857
    0x20d021209120f030a0c0218011211031c091d06060d05070c1e03090501030b0604120c0509010b030702070506190c061506030902010815010c0206070f08030709031103120906 76
    0x200304004840c40012080c0c0c43c1da00e980e01a091201c00318400400341411482c041681c81910442402002c03001d5142043c0c6050a0110450041046440d040c1210064030704200d440358015160403c03407402070107000060003040b100d018030300701d82014250783c12000720118410340c0030f550302605092070000c101d040c0c2d90040202604540400454101080108032400b00844c0c080c00301c5103030048a40c4031880e0241a0040c00c0d4409810f0505298500aa035a030b5441510112812101111104800751500200c00c07242d0b80c0125038455442000441c40250701d201442c030581c100c0c1c00f211055a281c00c100320041c020440f148414101c0283c003184c040d4465030b008416035200b6035012680a808035400c102c501200d412a00000f0781e0b43e60300205540c0e101442542241d03001d103143d00c00024500000f0464005040b0290245400042c00d9082003051524105215003010030540c490070031401c024080d81c920701c41507810a6510401071141d01d800b003110340301340070301903442c130701e0038080c3c60901080e41c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 963464352 1250 963463102 963463129
    0x91e0c0801050d0812150405100b16140a12110601081c050c0a120201180b062e09050a1502060f06010323010e1006020303071409031c020d021209 64
    0x5080c00d0164617414819000414081c188000028580c0951407040c0401c80e00014a5030340b0a0358100e8080140520410440da003044401850030301411a031b0800541c0070304a078591201a20911100c00140030400004030703c0625155038101f1180c00006480307680d08402e0007500740b25003107114100d020900c86140e4240c3c6801030b040c49800d15000c92045410841e98101c1903800680410003240025820300c1501e000384030801406c0300400781d40d25a00040800180800d01031a03001451454201e03014124070303038540b58011118114096000c005000341a075110701800342d4080d1002048500001210240c007040581c020006079540120640c15500c01608607414555600c0076140a545807070350300c0001004000c031030303100c9500d85115101d52040040100344004441d0005100040e0b001c01102e41224652411010003441e0111810451240f00c0360750790f052042000150b040d100003444658044a10340990302c9080410030141c1c1c803a07007102c0301000388403000c0003c0074845c170384140b41c44280b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 963465602 1250 963464352 963464363
    0x10e01062f060901051503010207030903060b030304030c1d07081509040804151e0f020303011e09020d0c140c0c0112090501020c0322030f0f0f0804091e0c0801050d 72
    0x20701c20580701e541020010742d441c24403a5122400c000804d00103541003401c010080d40218a8101036842c002d01c081041d0100801542d1aa0080e103a0b03990101b041d200a1600700d502034a003203070784210079000902152407040c0c0c404206400292424000d01390503110307a4080464001c0906a10104201c80b28014000c4501c802c0500011503e81c2c0a030021860400013901c41c5180d41101100c000b91324075210461104120148000411155000c42503c1c1110516440c102c0d031280342c02c840345100c001c29000410403501c04a0400044000c40d00520035138603c0d500c40b81201c408004001d01c03117206420701403244d584150708e010420f510600d020044141c484c1c2c2c2c0014040740a0359000d003683d101e000010307082e0f440410440d100100074415106070b241d10000701c1803060300c0c640c0d6030365400201203006840200d07217013101c1d41408088171807255500c0d030004c0c01c250307226103460504009001c681c7d5050071a0100c030391014404409481004000402c0f5201c16140368030b0b202c20480442100642280ca = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 963466852 1250 963465602 963465677
    0x6040c270305030d090311030a0c03121803050904052a22080a0c0b0c060123100f1b0f1205130e0f09032802010605030a08040e010e0106 60
    0x2c10340510180101e01c1d140040854020102d003402040d0914669204042d600b04000d5a04250f402c0440441c0b083e9150401c2c1d0500130b03494484c480206140160641003001400d00b1908141e401001002c140c2001c8508002a03296000a1201074000014075011500e02c1da0384400c135000f01f074014003056041c0d010090801d88010220301e8403110903600100e00e40e403143e0080800c200d540c4812801421184034698100401010220f07034416041c03044445404201395030394110019201c00c0b201c07810001c0c1c05081042c04440c0b0007400c410740c01143e03c0000ba0542041403050442d200b04140ba81e8104485100c0b1030199101c1c1c4d440c201d040104241480010000d959203008d45013082e400030074a2607a4002c3c80d140c200308036560740b0f50041c801c1260b508204100c0103c20b184001c1c044080300d2456664454105824080c0e00402d59500626854494283c3d01010000c401d001003041c0c6071440861080f60340d848217110314144080c011480460260b0702c023080403a0058039050020146000c1c00071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 963468102 1250 963466852 963466859
    0x90a140705190801060b130504110c01051602010501090b011e11150402010f050c0a0b06060d021204050c0a0305120310030c03110103200d0203101a04060806040c27 72
    0x259006821203401c08103449180b000c01643e07001384240300060624010152910803c00c4c407d071040394840c05414426a40c61140300a030701103000640350742c1c4010750001c00c840e0418400c2c14110b280e40c00e507080c0c010340c240070002c9440340060080c03d40d41a01070b106d00b0002d441c070300c00c44621b018488035a4030800c0001002c00798080001c00070351565981e02046080542403d000061004580d4128034041c494104844003e40390300141e9000d650f0703001207180d103081d2a0300300001d05511489179400590360001c40d440007a00b040c40d05d031900440c0b0440481d0035900408060155a00f41c6100141264009590351000701d80441e000355030201301511810f00c200c0d141c1c0d4031b441d10307041141c00c29240c2c0d0074556030506280d601032040360703000000b000502000551703040c5240b0003881141407011000743c010002c40d501c10582a006006003810740008032040341080090b0400e5002403041400081200340400c4e042d0615121322801100b071959041002c3d8440300e40040b0a1090a56604041c0480745001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 963469352 1250 963468102 963468109
    0x60111120d0b0d0b100b09151b06090d02101401051905040c0e1305090d03020f1308030304021009050102031e19120b040209030c27130c0e090a140705 66
    0x8030490f51050014a000e0300701201850b0050003142c0107403005000c1000f06c0c03000c5640b801e001c002200503146149035107030000800054484d03045082041603200302d0b4240050480042004a0041066800c8034103d50f42e0801c03e109550020040390140881000140501d04192288001020b110b6a18240055440c0302180403110011003940004460100c2e64641c1d08c1d00f0002d9900035030700040d00344064100803e00b141c03580469402c0300c017416400195510301021510075a004844002c4030a1035950740c610741c540d00da0744100c508034450040005490a00c40c0101c0c411800d60f1410307030055041840c600d47c4a03000a003142c0c5035042056080c00708030034800303c07042d07103035007404940d03490b070061190407564501a140d81ca00c07010301ca82d0046c411601540c034001001c0303680d0301c02160454110000442200f0207668103d040300300d540090410451110240d81307146518512851650389980d9581281607602c9006072041003950f080039403c0b50100d94015025207486112400f0b4950541c0e890001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 963470602 1250 963469352 963469369
    0x180f040f1505010e0702030a020706050d0b0604090203091216030c02040e100603020f03191e15021201091b2a030c06060803030705040306020d09060c030f05060111120d0b 75
    0xa05103090b1204010711018103403140c4d003508000d95000030741c203115106401a45420581c018401009804900c80300700c1c0c12560403410080001034561640c554480804070701a500480b0556450302c6943c444004c0031540c10210f451840c00300503084100304081da402c442140c002c18013a81d03c907480c0c03003030088417900900c090b12040004540008a4071b03d14411722405c00c21604c4c003a4440e8121001e000307280510060070100840d4083d6070048a01c0d004804078242880f00940504181806c40064441a149900030a075480c05060341c1c4c6690383e42d035403002055807814124a014400d00e10507030b10b40207000d203404103100684810354004611010b6180346140820007002e40c00070320300206480511400744504000350040e140a9840c40c60f004101034203c0c42540b100600c201c0c2d00161340310354003640354000d00302694860003d000c5204400c2000f4041c11a4041200c815494480820f5856029515030240030346414090b244840300c018200f070721a0000c050541c2170302d440cbc005002c030f5540c07915007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 963471852 1250 963470602 963470633
    0x2270426120711240402120102070c21020109030f02010908010509070501031104080c0d15050c030405060a0c27050316060219150203130b10060e180f040f 68
    0x181401249061000242950320340107000380c10b83c018070428030581c500c114030940164075404e604d1074030391520f1010407e1050441484032a55101282c0301007000070003607807602107440c0c642e0a01c00e2403902848003080e8442401c1c000f03000c5006c02c0320400004911409000419005062803104640d64042107400e40d1022211802c2a800080c401d000c59078240c13003008013110034030300d8243c2080d0900c99101e0380d881c1081b04e65846402017180010400c842000114250380c0900c0301403015042a031800002600150780c104d40714060000001c048080707070702c1000360545080c0e60303480c800710001400820f405485000b0719505440a180402c15880400880380d1241801d01c1d60002c19180110013402c0040f010610395114403a1420803010030494004075600300001d807030060f81ca4982c00180b004d02c0e0b200303020051039000040f04100d0f4440402a004089510b00d45404580b2580201008480d05c41c05c0403541c00030080001040700150384188442d0b01a2091822400302045901c0fa464503e05066 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 963473102 1250 963471852 963471877
    0xf0c09040f0b04080405030d08090d0507022409010f08060f1201020c03040b03060109150c080a0e040c0e0102060601051309050606070b0a090623040b090309060a050702270426 77
    0x30201b1250900300003c2e05010910702d03010405041250340b00c0c1e06e40c0c5881c140b1504102011506009566641e0100f5290601c0305080020b080c428460b200126048800c94a0214407840d080107002400703402440e22513800204805001680d2004201c4008840c0100c142590360074042502a00b000f040284068840e5020498680c50108001403440c0740d1500428141c08504051601300c139081100321407200d51110503140c844029503030441d884811a00c800d0740c058104032078002e03803640080850810010a900f5507030190703140170040d120782c45100e10340420319003040420090030025038003a2390080002003245141c0781242d00c404c4010700055501d00c0045688640684c20015a845a25080d0360b031440e20303200800070005890302141c4000e1001c0c140101c0740001901c03001050040300c19100005200645a0303081e10002003861304105000c0f40250140700e50318904003c51f40c00b0900700300446510325040d40ea1940c0c0c4401d08800c04084000349200d240c0491503101100000c1c0840344c0601 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 963474352 1250 963473102 963473107
    0x2011b02160f0b0d090203152508010b07080903120f040e061c030c1412120a110f0a02030d020711211902030c09011d090f0c09040f0b0408 61
    0x1e400c00c940039862544000b400002072102044604100015500c104440e15000110001c66001090030300a014001c0c004401140003044a04004102c00403c0840d0102481c00442400c0000b51000c280030702980482150238445000010134810040c0344190000c1e00783e9030f0760305d0201c003e182c03d40c03c4000c210014130710200303043c814101c44019a6078000c00407560fa41e00e034010007210507802000303030f10084e08218060580900b4406400c04501040000300112100106030500c60365a031341202005140c1b070540b40f00842e01e4071a8078052a0000440401010b10b0000030414480d900c1d0300030500b080544c0018002a420607a0501c054080180140c8080488600c01c0c000c1082c8214440c580010364801c1180203281150000341c0303a09503008070390300c0c2044030544e0700001e49071000498180e51b22840c04000410b09003071001c000c00103402c00300e001d80c15649807035110f10b807038003520600100150f1000c04195102e00d09034080355005400344541030f00c0c5c01c40c00d0300c0300204100d04890565100000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 963475602 1250 963474352 963474373
    0x2010501080d0215010b0c19050c1207080613150f090b010506120103110102070b0304050d08090a050a15090210020a0201020706090b0702240304030206041104020a02100c02011b02 79
    0x14402c10700d2034200d03480580080e560b070500500e0210b0040c0140c07040b0101c04100c203280b180c0d041200a140d00c4803441500700c002c1043c40c1080d5034000480c0410300030b803140e5070003140c0c5000000301d034020340d079000c4050506690b44a40982540145032410717140418039030f810011998040c0f04901c02d504590748007069850990a05895401040e4030880c000e241c00c12041c1d20701a640700e20b990550794400404442d80ca10640101d2030490160040d401490000090100b000400102c88000c110291514038180d940c81b45d100380c4a81c24282d000d41355811040c400030005e501c00760201070301c242040f0009248070090300402c016000d120400805030b4041f0380d40600750340e0100054401029240343c80100301d82040d80c0f0600b00c1c000c00100901803640c1041c0100b000c00d41240031146140c200c50b0720b5441c0e10306418003d542d101c00b600e0694510a4020b216111400c1c180202c4102c1e0445800400e4001b08801c4001c0003800c0c0305010070110b541c0e901d05158004402005400d51200700d50082c80710300072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 963476852 1250 963475602 963475619
    0x70303032009010f031b051b0609100b1f02031b0607090303031a041803092120030706020d090f0e071412040818030607350702010501 59
    0x411400351044203101c150500256520500721100e10100f031810340070040c1207682c264090a694940500c020b1180108844210352000240070b10102c44040b0005840c200107071aa12a001a00c0c1405550010038442104078030300d8101c0b00400d0b101410415a00c400c2520280501c8854450400182c10004102d03420300c441c1e40d00030781c1e09042d45010b4407142c1403544014028840900c0020203141d140c1c844840d44442880e08012281d00281050003a00b41d80301d808110300003104030480200d0748520020403d40130740f10042081505410300c0d18000109a1a0b80c0e40c0f044003c5001200d50040905d6000d42e41c405000703940040100350014148400401d201602c2c001180c1c10901810808600800c100d882d00b4174031035003028407420b1109400d100880d0501c4244541038541023211462001d0104000c442d10041c1880e0b0b800020b2041c90144d50070405032209002c1e10404c00189410100d4a6010820310001300f50000c610030410b0703004105100d0034126031003181c0b104050303503544004001505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 963478102 1250 963476852 963476861
    0x10090617010e010b0303160c050406170d050a170c0705010f020315030a1205090102031b2103060a03060c050904050a091103030c1506010903060e0a060e0f060a020c07030b070207030303 81
    0x204200003400b10b0382203400804d03500c0c0038001c90003031f1681c000708124051200201d07a00d009494050004d00c1a0b945810341180300000800c0e020b80c5c1da228181d50b10014078891400d80e203041c003d603559101c2d01707283c03449506103004018118031020321003046000001182482200c501c40c800d1440580c49192185141c030b0441061000c0303901a4110302410070004144a90902c40318a103402c04546800f40139004038614010040349034044140c2400d00115040c1c001805458654640205141920308400d40c1c0316078041030701d049402009928080c00040e10941010886040c0c0d8a0400d06050081c00080e060702c01c2500c440c848c00e0707581d80075042070180a0b00207003030180c0160000d51406629004584d603501800da03a803105031844101040250b07103c0d040c218021500607500b0f22900f03c0c3c01c42c07002c0d00d070a04614202c3d9a81c2c50b103000b00000381c0011400e00014444034000d4600743d956140d0110282d444109240c140c3d008004000c07001412802205000300310a43c010b011490035441c0240854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 963479352 1250 963478102 963478121
    0x6063f2d2609060d0f06050909060901050a02070201050d0c0201020d060308040e0106210e0703080315090721110702180f0c03010e04080c1204080a030318020f091009061701 76
    0x1d541007002d0041611100110b82001c460580d00180070022074848000910340c682040382d203c1c200d141130040c90702c0001407090180d0701e80c40081010741c071108207880485c400c00f580240860b0051041584030201640103002542117030002620301800e0107948012245290802c640c101400b1400b8452603900b40720f01405003100b81041491410000090403d00c40714a0025100359110711010460000500c8100001e540c003080045d107a040c414420f0407003420300211640200d4181c00022142c178801c0500c0010050014001c0c0d03141c0c5400740e42c4034054081c482620100803c01c00c9418010f881e1000f4009000d00c2c40d45005c07020703007402040e14012a40282c5047c03500881400184161503407481030a0300154480700031940d41c091650b065040c0b4081c040140400b020204d00003564080100344850b40c11302c00d40d020800c00c400780302541300c44c04c809100070350821201200000107080c071144883d000800d0040410031160b440025206a800e590000880518a010b090b400c0b06000d001b0071908 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 963480602 1250 963479352 963479423
    0x50c071407120b09010e0307030806041a0109230d08070203060c03011a03190c0f02071e05012109061413020f04051306063f2d 56
    0x206482c0c80c14a40310600700340005000e035070010b000700f8111402503104241c54520042500d0300c441c0c060601400e00c41c5c0c115140703406142819041c00d40b0340f402c16802910040141c4071041c44c507040045e203602c5101190b1380b03140c4112102d0304000c07159461142c20350410f84240d2155988041d0b034418181807100140c03c07600002d80074001031180c00b800c0c00030a44401c0046244035200d40d50000602c0480c5000403200820900d403410440e40a40c0c85101510742a42c95001c403410503070b0b200c22441400c0d50b6101245102c54900c8001e021a40c441c28841103540c040c0000e9a18072040300500030110307440070384c4c21240540d44220900b80c5d0400502000c6d4050103400c04440d0303406503600890801c0395800e01c10380c4a00d940b5000070f10380c2104401c1090440750400400c00c007554444007884a030854880c1315081e600120121000c0d094207507031740402c0b2401c00d14441c0d0014a11039440610f000c04484254001d20792201d440c2280034030452400380c649000d102c00d10040780c40c007103486550121800d000d812 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 963481852 1250 963480602 963480613
    0x70f0c14030a0314091b060412060b040e0309030304090c05040503031206040f0209030c04050703110c1b060307020d0f09090c02060a0605091005120f0d2106150c05010609050c0714 79
    0x422150118901000451b40820312500201e00c600041540c46190005001a1443c03803500d0180482d50b84400c00045003542c00b001156401416260790380104001030f54075a00402040c0118560354202d00080002402c22078105500c40000a0450700140c1820001801361741c10841d82d45018051448440003071901149400c07513460101e51182d4000c81128000c507110004181a0392080d4003440704208001045511900e01c0c0307805686480301400d80300701d01c40c0800500f001512b0070304110b078040c3d921034000300f104201c181400d036651813104c1c054800340b100109000030001c0f80c0340684680859141d001d002c2618040f18803a00701d809903000140a14414810001106600d000c400c0c140c0710111401c2c080740040d45141440c084600d80044010f00407003c0c05a812608290304140404c9401c40c0f511b4100241c080200c11281144107441d01c40e21412045a6828010131004503810300950000c5101d94403521080192a001c0d41e081c0070302e00c0009280c4060251400740410a42c604802800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 963483102 1250 963481852 963481861
    0xd05061915020a0203010c090501080f060906242809030c1701090512041d070813030c1b1a091f11010606121802010206070f0c14030a0314 61
    0x2040c00e152400750200c22a0340d4801c840c0c0d418003c1103c1000c42c0e82c01802400b02640d103800040181c9024811207001c2002200481c85803003003a1901481039401410290b07a50340d404042010042a403040542848410700e031040351a166540244003900b641402c00305801401400358400004585041d420049003c50a200181000007070340c0c11100001c001e1440501c00a44042c018149170384010218032991403401115043c0d9005401142c40550000c0c401a60b0340c2e46880c0e041c001141e0007800036030f10301c000035484031507441c4042000c0e0081c90a8400b0940c69a1840c10201c1c452101664088030385000300805209201c52400c20b0904007031032820a070984001c11340200744111442a50a175402044942512038403001a50080e484002e108070b603641c0601a10402300104807950042c2050b850100e04d01264110803440ca0b41a4001c3c440303076841c03010465601103408852410003040c042d820b00419080301840c5c01c081c132003070061680c03601d000030050200c3e901c00442d101d1120b4003c0401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 963484352 1250 963483102 963483139
    0xc1403040f060c140423030d080a02030705070807060902041a01021f0e0304090c09050f3a0515010611070e0a020f0c10051b0d09020402070210050d0506 67
    0x120700042d0b000074041140403240b441982e05854003181d410601c040494000303400c4175414441e590240a01c07010180d00012030081c10340300e0045800180114007424041040b00d0f0380c3d82d0003198000010701e0040d080c03454035503410072241c2c8402d80c107450850702e8010303200541ca0144030309013607000751043d04000800e01100203501d520303101c000103c00c109580540d000400498002c3e0080c5a54081604d42e42d80d1248404c400410703411900c0c40008260001c0414070303040c035081d544001d150080010822409036500c541540c001400c01c40801581c104003400388151081030280321a104001812840d0030421800c2c0250301e0503071009080004080b070000e80d21a021030700303806568103038032451404c0d95048040000381c46403255118284000049201c1c4540340420a1700e0640101c0d40c0501040c1c8824210704001c1c00381c0300d90b520025000300010000d02c440d03640b00c0e0b841a0701c09480941081015000100504000c2c18901c1c041400001ca9594803c0b8031702c03c3c164492000c07a0014402039481c10300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 963485602 1250 963484352 963484373
    0xe061008130308150306091507031a060d0f06060504170c0105030c030c0c07030305031911180f090f011e06080a0b0118170c0d210c060e010c140304 65
    0x14090101ea20f0201d41c5500348800420580c48014046a02c54100031090503541e4100503603031889560880c011a198610a000f1000d60710240384001140311808410400c2a5210b090040681640c41000c0c00c04021580a41c03001403d0703640b03840344c54600e03141e5030705000800512840b00c1d9400c00e40d0103180b160f0700305054035000010301680540b641d40305020307070100d4850101420654890080000101755020004520540c2540c640d0500c030b12281502109887c3c481107903828641051098465a40c0e1040b039a0204000092031080840b1112000c24003402d002c2d0b4030716200312408070060107a080602080781c0c2c0120300240c5000320320300c0c0c400d00401c050381c083c02840c030380e070348400141c15580e02c60f80300001e9030301c950f44c4a9611107556009032080c0444403420711655006441032a43d06144c9034801600c41e64100f010f4003d09040c0b585079000030754515650304148440d0081510201d1002d21500d4880c0d80e0900000626020f0a02c016140e90800c02c5407113002c0305e00b0002c0000041e4001007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 963486852 1250 963485602 963485641
    0x915070b011202060f0408011a18360109030f11030702010302031506280201140c030a0e07060309151e0f0612050304031704030c0311010e06040e061008 67
    0x1200c1c00300701c2d0510010300f00c0d20944c1507031545010301040100d9001819070006844880c040460058149108140040140d030406540c4004810800299101000580490b84002000c3c012a41d6016030040710450840200403c0d65030b0b90360b51501d0041581144040040c040715041540c420038084100c19034034802c2c0c0400904250300840410f404051407051030f112107000a11454441203480c8102000304001c503032403850001440346d492861401031103a00403d42d0b0f01080c00f030a81c0d03110460b107070b1640d001600c01600e595992441a12840782484104041c0100b542c01141c0381c0700c5401c0c41444070300c180e030038180203524264100810070b0380c07480303d6040c92600481c0842c0c02d24041000000070603003940180a40344007103004104002c0048014800d5070320800c0105100d11800542d40c400303000e1400028511046500b017480822540301030000d1481c41494585d40348008c120205406130421390140b140304401c4006c2c00500e180400a074000b9203072602d4400f1242c60401b00800301c0011104c2c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 963488102 1250 963486852 963486869
    0x30111030114060d020706151a04060c1a07170106050906070f0606030510060906080c0d1e05030d1413050c100302040509091c02031c2703050915070b01 67
    0x69520b0540740d010907200101c400020031520b42585062040141144041102d820090100e02145445e025414180c1da034590b1580542400d0501c0d01c1031782d500344141c5041e40e484490201c82c0000044030103840d8450039180e41e40131f00350048005203100103603060b0412414018240107030955521140305548506030002410101e40416041000060401750005802d60083e010140c4402895821a0084403c007000030002c880c1c2d551466a04c400009a0301c0754031660700c1b00000e001c550001d14090103c011019110700c1e80200d5a20345103107900c02c10400301ca03146c83d02e019084058084910a9005041e040c1c25030901c03425030340d00340c0c40e0240fa80c01c3c20700c00c02400d0340a071911842681602c0207080e0142c0b1905070750400721690382d1380c1c0250441110300c03205140c0c0744010742840882624400075031038078109242041e03c92190701800703403010610300103010718010202da031060300e10b151aa54020b480b01035a5585100501104010206c000f81070032800f00008400202030035401030444840c0d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 963489208 1106 963488102 963488129
    0x150d0515070f0e0a171005070f090e190507090503060c0c12070b010e04081908010302011e0203070809010c1b093c0225110301110301 59
    0x300f41480d00b1641032003042001c0381c0c1c140c10b444007020342e41046e10400e056484128017220b000b00c800d00e000810410454821503000306c2d4801c06000344001c2c1c0b203d04d00c0d144080300c001c44002080020400d5840780042d01041c4a030020f41c001e0300e070050a0791207600703000d84104a01d410004e1290664041e0322400c07000c180c00c0c082100c2603241e02114402c4160320b80700c0303014020680148107490b850000c1002d0039030142c011114201800351b07600c4e00c440da941940001842d00e0001a003400d80e50103240300120301c2c1d0f500042543c815590001900c3c0c1d666000c400100c2300c86800c0c1c5030041520005801014034002c0300b004c0c40342500c244540c200110f03d9200c1042041107a900f4179410a100b9011002c0c145100d01181380140f19621040035107010709803a01d4882c3d0440f940002240403c2d00e50490042240040ca0180000710450007070100854585407440c2d030344010310540030f0f030600c030 = true := by decide +kernel

theorem cover : BRFrame.Cov 963309352 963489208 := by
  have h0 := BRFrame.cov_init 963309352
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963309352 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 963309352 ≤ n) (h2 : n < 963489208) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
