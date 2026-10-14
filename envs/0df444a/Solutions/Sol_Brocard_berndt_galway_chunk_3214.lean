-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3214
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:53.253874+00:00
-- url     : https://prove2.me/submissions/c727f1ac-310f-4601-874f-b3c54bec12d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 577877697 ≤ n < 578057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 577878947 1250 577877697 577877701
    0x20c09160309080705061806060102072304060f050a32190f170318040209040609020c010510050907020a0201030b060912070317090f06090105040b040321031b08 71
    0xc124003500c1c002001030b1080348003013183c509011010a056008030703800700096007208402a50542c17540b40842c0d43c1d9000d40c0291504001c034a144400c046805d100140c44020007881440000e412103155130010801c0c00c581050a00550078011005405488042813004000403a41c80703614503545000741040542d0500741c6000c1040c2c0f280c12080240c40c603e10032080320781e92689180d40c0501150302c6113052040c084048800c89200200c00c480d00d010125400c400454006018400031b54058942541c20980c1c1f51030004640171684080c10341c0e0b00800001141e14245214a1a055016600708901c01c07022001403000544d000203c4080050b820308011909080701400202d45000301c00441390480d82540030b4100d40c0300302040e000c2c10b0381d20030241904030b820240701400280c055103441d9600007000d46200011031a0103401b03040ca150701454528503044c1c4414000d80140c00c564802c8540c03920400c8220803600403000582d05041e80381c07504220300c03520002000d09801c8181425800d100d00d07900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 577880197 1250 577878947 577878991
    0x206070203030702151c090807030806060f070501050105030f030a080403031107170a1d010212160606060216050619050304140607020f15010302030c190806042001020c09 75
    0x41503c9055800501c14000b014085086101980c40340d030002e45544000c0002d00e08680540c0b0500318001d811420382818000d0680c1c05464144010f01880d62001d802e1017101e004040071401080344ca80f0800000ca44e552400c0d092514180341803a00e00b01640046c018050761581c0140a1940140c0501d0081010a1003200758006c900c26401c010340418090301c0030034203550420004105002c805e664840012211083c0d000020980e0f1102c1401604810003c0d18490540c0003d80410348500f202062007c446941d144110b840d01d41c80078016800c032211036541c010b80c81d10080c0080100741c0380b0500d400020100582c0034116020110140440800030400b03000d215443c2d054507517186030884007142081e03e00650303034204258800e40144101e10345400c8003076004104d80c0c103c0f0340c0a0018000c800f80c00d000c21003c100718480c125102c00d041000014011001c0003814000c50013050840010810706a0f4035440e00804091141503502001040104d83c940115040c1e105041c0100c2c0614000100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 577881447 1250 577880197 577880203
    0x3030432010f0603030e0a0b0414030316050c01020709090b0f090109061a0a05030304050607030804052505090702030c07060f141209060108060f0408371209050a0206070203 76
    0x500d04241541c03801c03840c0030401010b90b00c11000d4078080c0e2103191400480f581000040c01c018002c450100340b00744020000c038004030440c080720040040030340c1c3c02d01ca08103442c4681d0b4416404166055405040f142000d545c0503c80580606035014051041d41415110f0055595016144031400400c450000b2a1b0071029440100d24030f5002c0005d221034460004403004040c103561841d07119900c8060001010300d0000b003290121030000d070009090640c2c0740c80540c0c64041c020301c150382500030540c408110441c2c003031401000341d8001e203034080e0705818401840302090000340340c0c00c150f5000f00078050212900095034412141c0070728011140c0121f00300b00310780301e1844000f0300d40010000f140309074558014046541c45101e00a08079201680d85010060f030301c4c0c2050301d0140d000103003040072401082c0014001c00c40e005d40f0170700040b11030300c1ca80d20203101941300b1510b00f41c04c4810303141d814525540c040f86403d0400c0d039281d42030003424281d446007500c03100c0d02c500003441a040051140e007152418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 577882697 1250 577881447 577881533
    0x206131103100c090902071502070c030203030418150e13061b08010314011103040308101a07020103051b0406111509030c010e151302010c02030f0c04060503030304 72
    0x81e081c1c80c0c81c103100815a10250002c3c600b0980030803c004000304143d0490320070784a500340c001aaa03010f0003010720340f01c0001d61108c081075418542032000440903072010401440108100354401e5405019648a48200c801034140c915400c01b000e0400c11014100342021900040d40c20050040b6007010314040008101c40f614483c1c40403490422114038982000900e8103ca004000032001c2c4100c1d0300515080f610301007415055590103101042c0400d2242c010168021000800300921766220001c0510032480c031410364051220000741642103592500500fa0002035800315020744030181501c40001e8040c81c0034003000c1203a044114401001c0c100b0003c04200c807041815402420409035180c0c80e1740c01030901c2c204071f40c01c02c0301d8408018000154083c40c1074210410841c1600c031106d001100d51074190b4240d040007000000e070405a80e040c0070a40c1414a444010301d8141c000d00c00340800c0d200250700c8988a40c2042c000c00c0081188408000c5d0130b032036406400b840d904001e9075018801851 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 577883947 1250 577882697 577882699
    0x606040f09054507030503120c090a0902040617010302130b030316050703030908030412020f0409150510091109040207050a0f05281709030304120605010603110a02061311 75
    0x140301c0c0c00d00c0c83d0140907446000c040040c254414020800c00f0145503589005110040c02075004000c0f82c0524000c51300202d402c4204691503a1801110100141e490780040e0080745c1d131103600040070001d80350440d5205800910300d82e851903440d0b00d19000603840741c03190040c1c1303030070326886490b54041540c1c14000c807030390201003804040c140a15800e0440d5a2885801708501058840e44041401c407000805c1d6408c40d440070003400c0d00c0036056400c0c8243d00080d110007503042a00e0b0b6002a0004101c2c500c802000e48413250002040d01e0501c010344084070040c1e0202440a1410710a140030003284021903404100680b070260740e0700403e1078400d02c0d151458901070a400321080b007400c1000000b06900644c031160444400070801214040600b0b802880002041c2004820055510b420703814094900b2000040540c1c1c14607070703500ea011500c11142c4030200d030841c0e50b8100501559130148981c00108012444407400c0084038030004c1d548407409000c08400eaa142c003208801c000504c1158021100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 577885197 1250 577883947 577884001
    0xb01020721150e06251b080d09020406150203030c030903041517070e1807020f10090507090507051e0904020d09140d09060e13060e010e0606040f0905 66
    0x10700c0c0b0300d8030300007400f07903281114090103410003081610703680c039029907448049450a04200104440306a49440180316101e032911240a04000442c000c80c002c0e0440b03c1000c01c002c207007500a40b04100441c0e0b80f58101ca0740c1d40d0340e281010a10070ba0b002065a034000c00031990541c2e20b88415503554a180529403046c0340800c83c914440f503a00381c0c4410315a080a80e0b1000006c60368031490000d0312500d00381c0c000190080b102d03150883d0344000601085400503001d0058525007a01c03081e600d810038401444012030591074034410410054100701400062441402c10001c9007420f041c01080c9100d04201904840c140304074800000d80c10004884d04950002d00441d03844984010840240550660594100161600d001c003d1407011510174041d0405a940d07140da130b814411305517016503000d020b030303504510b04802c0341e49080c040d0b1044c40301601007040000100c0d03142c280c6510580b400209101d00030700c01031000f0007461120240d070f00280c0d500b4100c089a160307140d500c21940385d41e620340745110006c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 577886447 1250 577885197 577885223
    0xd11030d141e0d091b09020702011b1103010513030206090c01020c060a0306050405010e0402130c1b0c030f080301031e1a060415180606030212070f091a1b010b01020721 74
    0x880701c070550380c2542c403145c45060348030383c0c2e500e480404034050300070040d012540e8000d040c01d007600041d11041800b8070529581c0c04200303c440109007121401c591503008012409010024103804001c0554040c900f0301c0100000c110701070000b502e940301003401c0f40c0a11070101e48070382068041d80201002d40000741c410040d642c1e582d402045c14100588069010344c0e0809101004100e142c007914a005585440b40301d40d01c0c480040080752108420000d54591000c80c070084005420340346941d40c21401042c4117a100d50443c04c1c02c6101d240c40030780b900e5107107802030541400a40d44a140b00403041070140b0003a0150f6800c00401c0180c04c1241540c030380d5402078440403601803c80d946017640340d05000340410807143c95600c160124400e141c036030091404035400252417207100b40c00114442c80280380c5410820360380c0300c141085a045449005619402040e040c3c107403000300b110790441680ca00d00900807600c05200103034072440580074442004031848581d81c000d0b017038140000741c81980000100400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 577887697 1250 577886447 577886453
    0xf150e030322020108010324020c0a03020c100804030503070e1906020c010903030503010306200304030203031f05180a0e0d1806080103051504110d11030d141e0d09 72
    0xc1d40c0101d0704000a180780c4400e000c0640e21006000d0341d00eaa06071901d08880c2d00710380794061200c1c0103041c0124203000c85444441d40101c1c5002502800e5801c8000300200480c9141c0030f400d1440134a80d05010300c404004585c04650b00c110042d40003605418450b50781e80315007404942c01c0c0c7e44c011030150040700a100a80d460002440e0300d03011035100f0342c00d0700c2010814000441c1c510445200190004030107000501c042440c40c0d0140c413180400d07144143c10182610244d080c0c030f8204560036805600b01004001407055000d075a806405070803004da0303c101e4100000103202080555042000440050004190401580c88540d0040600080b5010842840b4004140c4444403a0b150f4003540e490200182a50040014078183d980c0103015000c0c40100e04660110032038010810744514802080c1c0c0412030b210f901511506034003e030704045200c8841c0e014189003040781010389080141d0019911401c40111044d240e60114a10150f42003011241e02450340b400740e070356941c00e480d00d40312100c020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 577888947 1250 577887697 577887703
    0xb0a080307060c1803031b02180f0a090b150a0f0902070c0e2a070f0f1109040c05010c0201020c1513120201020a0204111c0e0c030c030a0f150e 63
    0x1d598801c41c000d00844119883c02c80c3d00058610800305000b4400d641400000c1c06900020b000c000501c004982d080d0340c640000d24180717561070500c19000b5801d0284030041451220040d80042112424080b1a0040e034404520202c010200038616421203100e444c140c3d21108100e0007070103561503e1928a0301d4502c020000e41c04620201d8140810b450000303910300040c2a8032744240140b06200b0110681041008081c81840d00c0343c04010b8010090000028417425558585a01640f68000d00ca20b2611b898030b82c100e80020321300d1180d6841e604010000300b0b6020007409485003880e00a010150f1840184e1a0011080620794401d180c1c500083d8203442e54030140c814000c03001209807225903152400c034020310310000301900507000180030001504080c1c212a060520030220389103000f01110660042042e240410003080c2d445a14440d00320000304a69080a007085000d80000c8a01c400000e60320326a000340213140c80b90712081c0034280203180002d107081021503081440716140751610952 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 577890197 1250 577888947 577888957
    0x1427030c010806030c090c040b03100e01080102090a0b090a08240112200625030f0302090a1802072001020d090b030601030b030c04060f093b010b0a0803 67
    0x802845155502400d56204401407401030301d002c0c018204500300d800034046017010082003030700e40c0d5504102c0000d1400d04131006500c1010700c400140c0a15080ca80407a188440690040401e41c0c014400600960381d10310030001190b0601d01129a92000203012030860101944800030705c1c015407030029840b0190307001a02c0003c40e07510210701c040e0f8030780960b4100c1c50310111010309410b500724104c10b43c501d110b015020500700000e042da414110780034030a611142c5204840150b49481c400f030f10081503040381030b035000402a4207080d0304000060f008120113180b02c1c070071a450980044240024803c07103070b044418442d0800000c1500312440b08150701c41e1410580300c5030041c8212007045015901c280300160540d0800304500d03265444201c0110090060b048145a00d80500c0031061025941c2d441503200403c1d00d181c01e01c030f000749070900c004125541c045070240007004442d42e4600341001c124070240000000607072441450034590f905401006c0b5842c4c1070340c200c45180d90128000d0030000c0545 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 577891447 1250 577890197 577890199
    0x201150b030105030114190b01170c1809011202010e0402040b0c061b21061207060306090b030a020906060304150603030e09070c05070b0a020a1a040201260105011427 73
    0x10104808904101c1c582500465004d0007800143c2c05a03a5402e01c50341111040c8c0105141002501c0720071014041510400d4500e4106201e0000e054480c9513180503000403100b1040b114014a0b41c5401050694041542c1000341084607145216825560743d50640d0701425a6045154840b82e11000301c5503591000d41d0406044000710003944500c02a00b022145c56207209080607030441e5949035011442d84010304681c0e8032640c205205c0401c00fa0030040540101100d59000c9202c911784038100c81242c08102c1b55602940161004c00090f80b01c8003842e9800400c141c68040e601e07030b101e0502501854080141d2100641403c50010a0683c41100172144000c1112681b480382c65904064071244c991034801400c941000501f00320761042036000e440551454010313941103000316541c41d1402813000e040d2982c0c0980c108144029540c0c042e80d040f0080000d15600240550036480c0040c605005206040c10403004209541002648805880001c2d503071403000c1c00d2801c1c40554001012030300d000307a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 577892697 1250 577891447 577891451
    0x71202041703070b010e060d021003020d0c020d09050904020d1b1205010209090105040911010f0c020a0305071410021b01051c0501031509020a03060c020325061a031c0201150b0301050301 82
    0x11440c0750b076641d041e80c01000000c0050303102301c19a500303010780c2c03604002d039243c28580c1c01c2c80044424009400389044031000755010303012005100c0b5004d0140059030f0003041c000c0768280c0070400140c450401a072045500840c890122045e01a200443ca8000c4d410008100e038504103610200201500545001c0d1011281c030300c156a200d6003403108035400c10034042c00880a1306522a21940180031100306002c0038a00381075100c00c1600420075103030040d4003c0b0fa946d800600304000e0b143c103c0945030b4041d0012070f00000b900e000701000a40e0f4846400410000030a01c080300c1105a0181003105c0e2000e1a13070341d00d401ea48410342ea550703000706002d00c425070308003101c2c0c00c5c0300c414110b4a2188480e2198000c0c28402a641076071103010003040c40301c60117025444100a000e868820b041c0124850240342c450000405505152100580e40f11020030340b0001c0008d017142d0142e40d400305460240c0c81800128420140c11500c0032400740c203010084a01c404081c501c0441ea03068008002c50603a0320076002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 577893947 1250 577892697 577892699
    0xc0706030b100e2715010f02030409150e04030201051008070501050f1b060108030a182106140709031a011409130b07080f070903050303071202041703070b01 69
    0x15415603419441041e444510804440758103402a44050b40c0b40f44064800d20842d008480e202d51401698482552258880400c0100044494207510890102032800c1c4190020803040a9600d0055018108049458105980144503440d0108004101c00c0c0d1b0444101c1c01c0c01e0502134000c280c15541c01c0c2e8030761040f05000c9a0b0b8040040d41d0f03c00c64006940d02481d00c00d1490f450089900102211804a0000481155107410800c00300b0b020740042c2c001307541c0d190010040074081201d4441800e4075010300e44030800c00c7d5160020200d641c5142100c80310005041490070b503001b07140c0800c3e6400000d940e00c0600c00741c6544a0000030589200c1c02c00c6032416030032125403203100c3c3c82c00d200d081d45440303d18007030300014100700c020b094100c0390000b80c40801c00056619240c0c0f07281e0403600c0600080541e0100001100700803038080d0000d041c3c0c03c0400c01030b0304580764242c981c84000c1100090090f180503030801c01c58907604960003040380c020b10007140044000040c1d01c95125a206481400310300d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 577895197 1250 577893947 577893959
    0x60a0204150c170a0201061e0f060c0b0f130606031b091512020109120803040218070f1103070609050604021f09030f02040b061201080616082215020c07 67
    0x310100c605900483c0826031402038402540060b4000c076201c100715502d81e40c1c0080c034114465001c007002008150064070080c10000380c07071519041383c0e0003601004050100710000c80d007000c80351a085480384c182100725a44030301c4500300d60180700000411076032400100200b403051020b0900034203455043c2d50702100303075980c183e8000d4034078100741070820b021303a00001c0004a10541c40b80f040244181000743c00710382c4d101581e001d0413000c0d01b0b050300c0030320000040004518115010804140b00320303201c0d4426003420000281820510000f080501c0f03d40c20a41c41000c004109444546500c0102440b0410440ca80961152802d54007280078050500c03600342c08001d40d400e0444a018030b40c1c4c94141a07480c40d16040509000b4000a0343c0007660344030380d91600d4960303000030038400c0c008200e03074807507549400038491902038000c000720320007544070448030302e107a0707000340e10a07006211100b2001241e04a0241d04500c1030f2141c0d002001191119566080500981c000c0e04800c00a14256029140d44407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 577896447 1250 577895197 577895207
    0x703030617070608151c020a230406151b021201110705120306030a1b090212060114030105060d09050c03060103050a05061005100c0309051309050f030a210b03060a020415 75
    0xd003601364005032240c40441c40c2d034003181401b11101e0000f40220013440d83d070207881d40f140d00381a9118410340100e00c0c010815090a0154200030a5049c1e07221168500842c4001c2c0030503e0071038041b1a5424803044070095541740c00300d8290124048008003d201b10344900b0340340c544e0090404860328094030518220102002054a10401c2d0140240003200c14645e6000c4ca00314002940c08001e80354604049580d016500c0640f60402107000f40062600b41a0000b600c5548014108041c50b041040180400e0f21004d081e03a0400b040b050020075009100d28001c0d0410404010907034245c401c080000050040c00181007065900407001e071089604c0784040204440314134003403250840d0740c14000c045a50300c0f0751800300405001e031404d000803c1d141c42c0064010001e010784504025251743c91300c0305102c0103200751182651014000c0d49011880744004c1c0002c4120114000824164200d02d011801036400150786100018180c80062420303102c10701c001d401c103020750031003c44002c00c0c0c0b114190040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 577897697 1250 577896447 577896481
    0xb0909010611030d0612030e0d150e011d0105011d04030e0f060903060106050d4505010504060f06050103050f06060a0c0804030804060e0108100603020703030617070608 74
    0x98800041a820300c04240c8500c040d07002114050310040003441d507600740c144122006403196401c00c59980b845814000d1071040c8150b901e6100e2a5040d20f8600060400100b651901222401c0801d00b01c2107002e030240182500802126051304003181540c48103c1944164144c4240400c03500b82e10505c01c3c800c14490400729401001b14030071103400c440c00e2070320146100141500421161030054104042802e003c0203030312010100d0f0020503114901002c0e0b0080441445036442149508071000048610521501144038403a0070818514800228215100344041c0c0d0803030001d01460400f440d09000411466981030b02042c684000455258440c0c0a001d024594a504181454840504000d404d42c092075460060095103401c82c00043e801801400056009440c0d180d01c4625041d00640024100c240281c10042d01d03900b04401582c0000c0030700c083e6907080ca0016203c42851401341c0003801d0540040b60300792540004095007030800942c0c442655820340c0d403403083e0344401214130005108 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 577898947 1250 577897697 577897699
    0x807060c050c060304020d06020d0b120a110d17040f0321020a0308180a0605180c0a0b0a030f0905030a02010c080c12151c05060c040303142215090b09 66
    0x1140c0107401483c1c0100603540090005180c10403140e0195521030403030b40054215a441a192012041c2c686010b9014002d90780710b5030040c00c003866656503004110603c00101a10803256095080c052113100c1d81c44c840b00342804a107207580d07036840b1520080700d40460701c0203e44010b01013865a01c02408820445800c0c00c041c5c008040d400511340c1e00307540c5882e004001c8000d8000c9104402107200e401c10400c038295000d0640010f490804004540c55202c040200041e80c0c0d00c01c80343c807242501c50500500440781e1021580740c440540c08401c80180c104445a0390105040250502c18080084001e0501d45904d8000708101d840804060300d0b5064200c511745031003103090040c248000c5201000d141c0c455018aa1034040c164140c0c0001e1102c82c010345404000302a4460345000c10408000068000070400081c0782001e141d0380e0020280ea4081c2ca030030718241008141e11108079101d42c180c00740c8010703081c10a0041d9880340019400c085806981c10000385134480000340c03521080048500802d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 577900197 1250 577898947 577898953
    0x1413052a0d0f02060307050403061407050901200a0b06180108071e0e011716080613061404060e010f0506030703030c05151504060e07021b0102071e0807060c05 70
    0x181404000c201e070200041920185008a01200143e840c2001503200e024582c03215516503086040c4101140e4003140050703885156801404405d82c0c2260990b1000d81e001d20b03103842c1848110101c2420340d03210b008079080500c62440003400300202d2000062040c50f0640b01e03a0482d030341c90400940180c10038410342c04c054101c070402303021114546024001c00d039540a24420b0650350346030110345c00314090740403903030300704254400540c0b5150034460000e5a0070282d1000d82075a04000c001a190440681f42050180b000d10000041000540003004607041e4069042d4044c40c050130f245001d00860000d52003a5480c04000781c412040d07a00c11603000c0c4c00c028005004103415543c00b41c07070314810b0f031000b5103c9100f00c442c4461801002c000e08c80c41003488442c806405081c07142072100340c85041d04603100c40706499040240281d40041d95403004076402001c0c0c9150100c01e00103030305090b0160000041c50640c59480c1180c07204208528045540721400c0340e141036501c800072940c02c1e034505030003001030b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 577901447 1250 577900197 577900273
    0x6070e090606070c091d1b04050a060b03040320012a050f04080106051905010804020d0c05030a030203120108060903120a06050406060c26070b0a141305 67
    0x205200041941c007480150800c2d240c001c40d600c0e4000000400c1e0b0046030030b90346030900400208140a680c994403203c80004105940c0b000c29070700c00c24104544010300072580d60700016400680341e0805170061222404003a901c1c04c00d800c2c02480c0c815458101d0f80c10100441c444903004005103e80021904000c41f8140d15841130404290031400c165004003c010050000c64050080c00d4000e1004104140000400902d40002d00000c200030003106000129441001c004a9800c05001039120740c0c120b40d07941d641100f529140801d1200f98010b20b80600c180d1600c0d00030150000014880b4081c00e200607010b5aa903203045035520f8000f1102003d9035003040c403c40104201b100c450740c0c0c000008041c0403c0460710303480824100ea0b080d6000d04001910800711764140030b43e42c20010300035400c480050300380940c1c81c66140014445c90741e0081c04440c10318002416011541c1c003824805140c0b052003805402c1040d9182940390030304405031803900400e0812240c040c4050780542108000c5c16110f141a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 577902697 1250 577901447 577901449
    0x3110405160f0c14070e0106080708100b0a09030501060f08120408120c2803030b030604112404120b01080604021e19150306062c130501080c01080906070e 68
    0x600a03c504a90f110b820240d24210360009001c10700c0035100340c013100803d079854000024000c0c0c0c0d019104405014000d0207000000c1113905106c0150b600d1000007540d18154904110350850503503201920552a01c000803414400d68144501120081c00440c2e102623100881c00c0030a200d039106441081d40004d000d1003004903400c026226200d01070040e5821b94521000841d6409008681d1284400c8010f040c2404c1603018410031a60041c160014482031415039182c580607070303400410754850703000900f004081c91442115005003000038024903442e95541c2c0400d1312601d1544108403070b8600900004a4802c200180c010322a030340003410381000400300240541403078a21000184c125a040e40f020302140401c2c00600014058480304402001c06c00b070001341200c0f070b5500a0030400045041d0094003984411040d0b401500c240324290a03400b0700d01c0002d00a250708040d0841c038605110000821440215075041c1d41c4030280c80c1c004807542c506000346e4480b5012240c841c0403802c1e052040c455 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 577903947 1250 577902697 577902707
    0x3070b0c040f090c030f0e10150b0f0408151302060d06050306190c020d090b090409021c03090b070b040609050f030c0708071205060f0702030702060403110405160f 72
    0x2103040491400d00d025150400107202d0310082c1c001c0c19106803a10030104010f80d0521403c05214008003042041030b06112080792a0b4a403102014031081d110a00c140c540001b02c0315800007003449840c05a51400c86c40b60981190300584540742c038501075500503021108251000501c00c1030401c1c3c0c0050b400c14940c0c200100c541240800d103403842e90351035000c1015142000600e000f44101c0411b0034aa544000724a000da800641c5080d0854011201030b00365035410550400540750290f800c1038880014001150051001d103101030360048071003080c44600104490072022484c0240d85010180d0f45a00c802d500034856140700824410b00d100004e00410341c181d21120f040385c440d1040e20300c4079000028032451900111003080d515004540100925034080182074010100d0126032409030046484040c0c5039140208a503e8086000d800644454401e10484003d164024000b07078a5940704d080015a001c1d80b8513859006901c1c140100e8a9850120b80c01e000b0000d860f03482090304070304904200c0b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 577905197 1250 577903947 577903951
    0x312020610030f0f0b250e01021506031227010309081207021f0c020f061302101106070e03060a110d0b011707031b0c03020601121a07030b040e01060803070b 69
    0x3851841360500203000903d1095018014600e40d03c1e5a85807000050301e03c80c0601c216045502449000c0103140510398001c10b0165420681d04482200c558505001c40c1c1800340a074064542600001181c098440075540c04d92500e401070080300c072070f52080100560855000d404050020281481040d04409a02302c4040e840901d82c07050340e120303c80d400140d11002c8254403559018039240c140304507807150b04000080e40c41f450040103100e40e0034060ba081012516044010380030380580e0400a8950307005907080302c01d291101007103c02510f403a60005202000221070035100340134403000314400e00d020340140b140b030301e0340721504529124520684d80010700c0c0010001d8140312185d000b44400c00c0d0b041b4415445258580c50201c0c005588082042144042016180a0201c02600752000c2039000580078155000440001c00c2c09444e414205443d150514421110700412410000e90a5050f00030130035059066805100808200c2c401500381c0c1c03000d004407000790703106101003000701d138040d40600c2e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 577906447 1250 577905197 577905203
    0x4140604050a0f05150c041805010b0315031e010902011d0901063207020a060c0c03020103020a110303090f06010b0c060c070618030305190b0f0909011b090312020610030f 75
    0x413110645044e880c0601170040790010034a10001c1003c01400002c00c58003c07943c11440c030200015030410f960480f90b40000b41c010b011540b0780780e030a4240e0792400c02c000c100450400d040081601c0003001030602130941000b04a00080c05030600200385070300010744001c922001814814581e003021b1080701d1064030520f0300e2040b00380c1c42d40c000543c80304008015001410500d6200d60b501030500501004c0aa1584401e04011440c8011800308489a85110580342c0c24a00036a98144028080f200c140d001024002c49000000a006c1041c800180c05a0a4043c00040d40d5080eaa2000e445809008a0105840f1074202c0310014604440301c1000700216880f414000030300000c0d80724200d40e4a03031038210072404a940c8009001c06015034503495400b01d4103000041c0444c103800400b0445d1910700c107100600030441e11022408400d03007034008807107090055035103030220a604800100218503600c41070724600039041d071500341e4a1011801d14440d850080014640d10700e1a64bd611082c02009001c1d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 577907697 1250 577906447 577906453
    0x150c0209070806031c1107060801051e040609062705060a0e040510021201060206012106050a061e0302130605010804081e12070e0109030c05190305060403030504140604050a0f05 78
    0x4464510110741102c5d0099603515008102ca5a080191904040e0340051040c0180b4500404c031550f1003a101454049101202c40025003c4001040181503242c121104003402d0480c080b0b041050112142c030350369144461481c0d03111142d20240c0445801703446640c2c00400e40d030000d10141c08540b00f800e0308903100b28102e5000101d6180c024080307801560494060030b00080041101982c100b03da130b4050400001105980381c6144185200c41450050041003a03841d100010500303001680007000401c104280d218030300406106100d021200f50000324461006c0300c000e007440714558414503059038010b031605501501e40340c907000026005854007407000000402d81090401c08540604503000c403c1c0e42244440c10030803006040404049280c2d0704001ca040e008201180c00c1d107580004481013941d4032096120100c46085482d0f01e1174202406a03c240c1051008240c2d0660085100c0e03801001e0512044160751700c0940c40d907806a4014005903c690070070008203c4040d02050750911030340032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 577908947 1250 577907697 577907713
    0x10b040510050c011107020909030a2c03070602030c011805102a020c10031a04230903120609010f150c200406090204300507030c150c020907080603 65
    0x510f500b55000300c0342c81180000017182442c11420310000305d91304106140080d6041c0310340040c0c010b10044c070010405030b070505400c40102c00c040c0101d1010305030f502c019080c2c5400c9516254040e64a602064042c0710a41c41d103a603011a0100c0442e1114000d90701c840508101d125410a8801921000610405812008403480100708440c0a000b00c1c4014980241042c50240e0040100c030507413400924003454140802941d0062100d00d0a24006508480005640c001da402c00441d1a0307200c01ca100034440003101340705136850004040d040401405e41840300ba9a115818000c0e0b4800a1240e40400580c0b04018403661100034030340045100c3c00e181c0070f071a80e4107a482e48240a02c100b030f00e466003000e40c84500c03655414180108800b0f05210081540b80c9440c2002c0e1440e007406e55401359128030040020001c00100b00c5240303980c210b070498110360140b502c038140b60800c000e4034402c0210005108405020550040c00c261620940007010004590b941c0982600c0c03518000300183d40c54014011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 577910197 1250 577908947 577908967
    0x8070215091e10030203040503070f030909020d06090509010c02030403080304110a12021201150b07060603050619150b0a03020c0c030709140f0105030d0c11040203070f0201050a05010b04051005 85
    0x22021031880380980300c854802082c4014000301a41d800c005904040c0100308000100b4000011140359135800174000140b0701c080c0c01c04544d040746a4101d0f0850718000107282242c40a581c00c00429118051003c0210351a040c141c0c0e42200d41070500000560000d01c0104080380400c000356034400d01808508007440e01c2c030320008105842c103810001c4d074943c1d001050000d5080070f034102c81581403001d008001c0034107c441c410315610000d210700000354400242d02000c100a98010000540d0310808555081c10401d6138080352a4460800403102ca1508000c0303a034210700d28640b0000c540c1b0103d95180b4100c0400030440195002c51000b003802d1150308104003040d14100503000040203145d80000e040d078a0460155146c140150110103002d81d050300500c0555000304000c40c00715818208803001e000e8902c1c00c0c5c421000d684c5081a4007a20100403c104541c0140c210f00b582c40c895030007000240d0302da060b4807045a100f0702072280a440d09200600080c20039060100c4c008040d400c0260400100345 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 577911447 1250 577910197 577910209
    0x1401210e030a05030a0f11090d05010902090405011e0507090b0f3a060302031009151103160f020604020111010204030506040f0c06020d0c03180b0d0e06060301090807021509 76
    0x55002e81c009a000410070841d4001c501c40c00810707548080040c441401c2004000005018140c030080c840c84441030114104007007588010501a40039046070030510705414224020180700c2180610703e09900410310340f00b21203125851081045840f4210742500f01060603609800c407900c03600040004101160606c0385944498842d0155001000d1294100c40e0014200220082c6580c02d91030402c2c80600040e03030045040c210a00511302d000a00d000641042c90754100c404044080c507515002c85250391800f070f440110f103c2c404140f109640d650300548115405100b000c400b000507005000401c005603c148a445044000c030340000d420140c4980b2960704181090714203c4202e07180508101c02c0005c079211400040159001802c28820b130030002501d0382100d190000c04002c0b1950100111140c00100c10703003d030400c0000e254581003c9800100104804c0e40300c00c0c0f0511030765000402610307050003941c034141e070320200107810561076900b0f0018196010420003101c000038000040e16444d84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 577912697 1250 577911447 577911457
    0x70302152e05040f020403170f040f06080105040c08090a02010e1908010204031104020708070311010216030507021914090c0c030a020a0b09070b0301121a0711071401210e03 76
    0x40c400e800707020310b40400c0100300c0342c1c1c1440d40c01c01240140410404035401003201000366607503058450355103151314048041071150303811410103004031402c045807050b0b0101246059581c140c60806c000b926251064030792010849050f00c0c568041d406140055104841100b060034004c2d000080580c2c50341e03603c0340610b1050b0001c500176980407c040042c004110490075842205840440c5050841c0c2c4454450344a0031a01806110b40e4280740001b45100354101c410022685d1500480760b030b21032400801c154085c2034164490a201d440448005403500d88000441d12007454640a500160703041c40120203000b8807003544d1076010310080789900000e00040c211000c096000c2c01d28281c40b0328104011000181c8140481e6020500502c403454940e400c0340c0c117641284086042c20784030361405544812840310103a030011445014031000d240c12400003041c000d5000c00385e03075489886041000e03a0550540c1081d00094802d602c0c2211940c40e03813180c0701c2d038900c06680864007076080f00c401891a401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 577913947 1250 577912697 577912771
    0x43201050d1401060225080d08070507020306130308061801140f0d2a061b061e1509050402091302120d0f0e010216060e13050907170307030215 63
    0x18a03006d8444040d0380703a45007180c801a004103600c00e403c00385510364230200b02c04017400b402480404500c0050040090381c2030390354010100d40d10b520700109814025510035504901090449001c54440d1a00080c500d0b0030007102e00611106a02e4241000100105258066000301c101b1411a00c03e4079059460b00810f030146502c400c014100300c00b09180146240d001d035200030790006c018025558041080e00002c101036a00d41243c400070305000004280c1d406100301e5205921440b805441c040c1d8004520784800302c00e41410703c40c2e65644980540b0001c4500950103030045d000541301100c001d03090f102090006e000304c052000310b1114540303000c4a0440420114202c0880003151036407003120848815000c0c8003909000d81c6800d00c070741404010340a100305005040e00c0101d042d458000c164070006590540c1800641040701509032034002500600c100c2d405d0b2454403594400001044441c403543c50350081030700100d040c8500c1c3e03107010040c3c0708140c0c41400141d000804000360080140b1088 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 577915197 1250 577913947 577913953
    0x40b0d0c05091806070c023d021621052b0c1a18010c09050310060b04090510050916030e2e02090303040b043201050d14010602 56
    0x2003494204500c0c000e0040890300c10284120700360030501d10204005402032817506029142000710b00c000703003a001441c81a1255442c00180c800d4030417921980c03000310f180d40b0985049aa84403410201e0701c9103480181c0100380032910381c08201850140502114210180000250013041c9507910b03420005800403542061b0440091025070b05c0340e220725640020b04504214400840715a00c03041c402890a81340804840a500000d50b0400c0941084d442444800020030011080b020050b110108900079140203100e9400e00007004045849a482a202080e001a00702807504074990007614004002c0b09814006420000e006d84840001600580b07046103180d24180c40c1d0380c0000c1c204c0d0310b145010906580b28007102018070342400340c0c942d10f40c9030342c0c800b000c5c00b00c0c03810b403000c130191292120286c3c00d8803001400003070502c110000703001541c2420401001001d01078107182c80d000c202e545000c54800c81a0a45c0ca52580034038000c048003030008001207440da04030132801211010990007500560 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 577916447 1250 577915197 577915199
    0x507050c09010f03030e0d1e03020a02100f0201050a0c08011502010e0304090605040c020d05090618100f110606010e0111150901020a030c1805040506030307080d0c0e01110c01030b040b0d0c 83
    0x503401c4100014003141c21f4521518202454035580b1031003202c00110a00b8094102c440c0f001c1c50300c00d006070282690040c2c050584000c1074100141140811004000103500c0e00c400700d170811140e4001d5a003103844554540102d0390804000001049030440144155940c86200e254a04410710290009105030342002410519142c24801078400d07220414045404c024410410181c020090710200d410a0740c6c580e80f110002422407410351034025116501040700c500005451341c0c000c0700285140003e5076402e0b1481407051a1a65481d015120f0320b0115655000341e42c81944a000001240020b1504803502c00d5280b5004001c1820281c1d201d80c2d440c1d4000402c160b07001d4050056410960151401c0e4001d080030b01d8423612158450302a051149440780d02003519a501001681c1d84035030003903001551095030784060300042080d084480301050980f10150080d6006244042081c0e629002801400d400000114000c200c1454450352050750f40306003241945906024072007443c8a081208961 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 577917697 1250 577916447 577916453
    0x5010801020a140a12020c0102070203010e03070c0e100e04060609291e06090325090606080c03040b1f0e010e0a1b0503040f12031a060c0d0507050c09010f03 69
    0x10701c070a07100b0400d41e8502044003842c4c007540300000807440d201031040180c54855180200e400780c49034001c007940c91340c00c01002001444c8084003c1882c2c52041080005056407100c002c0c04501c1e00312005182d600c2c04640030400c2038501c1d4200c0c0d074028411040000c0068a401e0140c08940b545d11a4944005041e607003866074100d0f26030803210244049801d00b40000c03001c1d030310351102900c4201d82401a107000c1115007080c1c804203c103c0311480402c03070000c001501c0084400e80c010040c0b0503211128280800095028018070381c0901400d13940746080e02e0350341c0b952034446802c00041e10702c140ea1943e1520501c108500080300c0005082c501640f040e03254949942c809050001a281d000c03040c2c5407200100c200f4450000e20814031442c0e082c20364407a40d96090001020030850740141002c1403a40d0790f034007010340c564081b240c10030b240a000c42c07228000305d060000501070140c1001003035004011054115001d00050205a8400c2044580321041840420303035403103081e803282c03900b032221039014820 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 577918947 1250 577917697 577917707
    0x80a050f060c0706020c0106080d260f060d03020a21020f06060a030f03021609090b0a0506011d0f0307080705030f0a08031b210106021009050d0f02030d05010801020a 73
    0x15030319052000303195038242010310501d41c0c4524000100740039400140c1c40e440c191b007900306000070f240d11401d48101008404001d880d481007100c1c4001e5504050b10210b4050041d8000306002c0c0350110209002c80c0d0306c1c0814400707043c2d44040140c3c1540302d180e003160b0009111062540d240010328440300000050940040e1508502d840898200e8100d54100f00444c0c4400c07411104803908103d185113200d0050409901f0103034042000d205a190310b90b0701144a4403a90411500c05109511503141550384003c5602250000e644caa80002c00e50611005400011406a0b0001c24024114600084a417000a00c3d00983e82e00041d0790360041881080540743c1401640f02e01001103024140013211039461002d20300c801132500060200141c8001008101a0283c800308454000c4007185000078841c442d610382c0d804d10510006104140031541007500d24060454481d074044001d009030b892882080d0f034010101440c203000c5110a100003c1904000e008060003854048001640c690030541d00410f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 577920197 1250 577918947 577918963
    0x1b12090b0a0b01090503060114090c0f04031a0f1302040506041103270703121d040213080115030f0f020609180105010e01050c0c040e0c281401090b0c07030c080a05 72
    0x1b20036000b0a00401c60280c500300c7c605000c14084513943d000f56905694850303140161407508241580c0441c1c04810884840c80854648212101860301c0342d6034144050380308081242e272801d0f0303052062000001400c140d004643c00100080c00030503c010041104802500704030355506003100e20510385000202d02030388003074400c0240c0011300f000504589603d01c45503028440b4a04104c0a903030114408541d0104000710011f004100b07642e54042d03400343c0340503c0702501404403154070f020041c640b540da41101c882d08882c3c2c016442c44200507203031034070000d001d42e940b03040e03810100802c201040c070350b90348030043e85074040b1611000c40b83d41450001020b2080e00c12646040c403104001000000400140841c00741e94101c0c1c1c0840ea4400941029080c4141c0c6d004003a0002c015040d203d950518104c40c010803000458003104c1c84030b036100f89100c02000600c01041c0420841d800074000c15000300008d10000b5216030489030141d0380ca90394100b1060300755029500d19000400302904004081c04910 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 577921447 1250 577920197 577920199
    0x40507020c01050f13180504030e0a18020c0c04150306050c030403050304021c0206192a02060a09050603010303050d150e070e0a03140d09091b12090b0a0b010905 71
    0x1010041c640000030f8114820961410940700003c182d03906036050203ca908054030074062150007902c1106840005480d090b0b608a005c1442404212201d041130b0880c5001c4a035007490703c0e9150f144c0b40c003822000b5030040000c4001401198054882616a40158084a509200265506895820a00112000a8104013011500b0410f10000c244c0c07001c1680e40085d0122400a050100140c040541e03080f4150003c2d081500483c0c03403a031010180b204510031040e591034040c401c00010a60052100e2801d0080c407003000075030158005810040041c207500c031814140f0448458136500040c80c1a0000d0b030048000842c00107102802c00118064403071041c10641110030000e003046c900180c0078030000e01c44010010400c51018a81e0344480b000b100071a0842d4062280000d036141150300d90050607400701c08a00214800509801c4520503e0780500c45115464040ca2862504a03004e020f04070010300c2aa88440d206004030302c0041c0061700584a11100084802c40a8000741c00d00c030603036101c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 577922697 1250 577921447 577921453
    0xb07050309190e06100c170c0705120d0806010c06090f020a050f13021c020d051b0c06070c11030102030f0a2f07060213031b170d11010605030d05070204050702 70
    0x100403003c2c20041e840d41055044900341e120420b1031500301c03044000020060075046159580351070303d41900c8001d2210300c90040170380d180c1d2a00e4000f48044c24103120b4295070303164020003039449894804c510a6801c014149001164013030303541c031103030207860130032500352030700d4200c2400801103207801520b0300020320069640140d01c100718000541c4207810160031411864001a80c1110f244814441c0741c240b4412280454441204505c9440103190840c0c0c4254480b40d80b0b00072050080024003500c1e04250344000910701591000c05c1110103840c01901140c1183e0f02d140d2400f1290750a0010754469611170004a05501e0700303686010039a9054030340314034541380540850300c0010281101090050103004019940d5103a8a0014000c0c030400403540c5002003448000f00030400c040114885541d05511f4215560b9180d10480b900444030004e1110039620904401e08030502500101e402d0b101054000100e0a90304d41c00300341811030f030402000c00500e000458030114a418400d280c0c00207080d10003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 577923947 1250 577922697 577922699
    0x604081b070f181e0c0e1801170f030d0b0303090d0605090d0e0d08160c0e071805010906231803010f02031302060c0a06110901020d11100e0102040b0705030919 70
    0x4584800d134000390002a2154032001c505505501440c070030100700e100035006091901c80c032400c0500e41002801100304128500d200200d008900242c0c2c9100c90a085003d03501e4801444076800041010500d16034050105021040340f41c3c6e14242c4a442d813034010358000c100d40c5841c5c2d01d02420042d140f8400002d00c140c101584102c1d0f1549407001c2c0040386c0c440f8500740c1c0d405000d06420070704c010361280180310003008400411003c88000809010b0303581d540b0381c80c4a0740c00000182144540700e00400340000d49909041040900c501200e07981196144e104500d040d800c0849a0760b986d0000d4408900c648050320b0300040d1341024810000011100b4200310300b542000341d500d80a403060048080d205440120742c07506425002d000c2c070704503558003120422030b0401c201c000311019000408001d02500074480500c001a0141c0000c0349900d160401820f40942c2c1c800c4c2c8200107041450740c01044c0c2d0b60030301001c00e00f07c8003c40244410b90003140295150300743d40d020006240e0401c8028228194400b40c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 577925197 1250 577923947 577923971
    0xd1103190201022b1107030609030507020a060c020f0409080d0f0b0a06110c0409081b0d080108032b0b03011830050703030b0d0609060f0e0604081b070f18 68
    0xf8030684009013902d020684160300b50007071490100c50f81c0020382554a8000c1c807408058000c03006140b0b452003600c01020701075807000c060310380000a10001c1d401060304820600d043c0b9069021825041c0b00d0009241014240303003d40341107510b6442c03602070b05507032110540310314036220441c81d00800c81460940c0349a540e859895072104030b03054020703000310b0303e0703ca52104200d00d4401b6134698403822951418001c0e640c5680d5965043c81d0f00c64030021032170140c00491588004800c9131111b60001e000350094946c03032140c03180b50812001002d800750313a070340306001d01c0d03a40c00f80200d5000d81d4030799040c500c4020041c03d1000c0c0a661140b809240c14541e29502441c01d50361507a40d13072100b0310038149187c681d005c60a06501610310007a409070300c07090b156240c0040110580c05039241501035082045107080303000c1c8520440e581c0c0300b80492143c1c06900001d0000749050028101c03607207004901403520303c21014183c94880c95030083c02e403c0f407006406014400d59002b01c0007080e0040c401c1403107410b00e408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 577926447 1250 577925197 577925263
    0x60501180c120e190c05040b0a0503030702010f110d0203071101082202040609020a030516050301061407110d052a0a230a06050702011407020108060d110319020102 72
    0x8540321150b102c80ba9a00d800f40140100140740c1c84403404000018100c4c0b8200302211400c0c0502e130305c1207150407010011410b00c00d2854055034030250056251928580042d9151400c1800c1c0f00d04000d6080205140c9141c24401034044032080c0d0000c1d9201c110514200501001c002c0b22103040102000401c041007409400481004441000902c1034070841d00114010b0726140c1c2200d081c1900000b071500340c0940c10361003c0d04c03d1a54a000c1004401220001c0310389100038460034000035400401503007207044840c02418404e100d52110040c83c1004404507510034400c0f50140c445803c51580c91400d2a45014100c004143c3c541da207428890b504000141000401d000b40c401000f080c0c540341d0200034083c07e0320f000321031000700b9a07242c0716951540102350750f201c618220300107400300880c4000c4103251016210100d605858040066076160b0a01c600c1d013001e820161034804650002d05a2510140801500e207159880284403d924600000e0f00e4041c00311070070005075a0032822000c4010002d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 577927697 1250 577926447 577926467
    0x51806010e09030903060106170610080601050c03090a0b07140f100c170903040501090605090d0f021302040b04030b0906070e090702070f080d03060f0303020c010305041e060501180c 80
    0x124211028070385a150b8241e10b03600403070110a030140b02c2c1c0d00000c10f000c0c1d00210b1001028203003101d842072a43d14541032100440c110344810000c220402c012a90644c0510f02404c4103425000c1182d080c40070040004544185541c40718040c100300051100500107001c60a0089840c1c141c020180400e20644244d078405040c0f01460425907203140030230805100c1c1102e00800f900d40080ca4800d81001c1d40207580346d81c040d00c945400b14400480c00580302d80180c040d510018401001010902c05940316607031f01c0c0f80b000d90126440021011071607002d280520242001d0b02c1c103680d1042e01c860a61a01807200b0380040c0c1001c405500190130845d1681d4014218040c4c3ca07400d40304441207031148030b1305a02d031a019400c0804000d5001102045403440081c080580840680e001e001c495541d800c1c1b0010400715002c043c0068000301c000d03410301e5000fa001207170002d101d44002c19100c2002c04407003010520045003115a00d84500040107a03008455804000c0c0d840e08404110354404404013801c00340358 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 577928947 1250 577927697 577927709
    0x180a05180402090601030b0315061c0c05060f070506090d030b01050313020f030f032107090b031308040f15020d02160e04080c0a0506043809010b0604060e0405180601 73
    0x790000621117900c26009494441e101808032001034118200d60740a10100301d400301e0080354220740300c68161121801d000c01c05500801d80e110020b06080078440b0320b40c030120b0300e41100720040182c480050400c1150900c03071000070020700b548c66102c6400405560310b41641b0f504100003070044c0140300e2501c4682034041a41200c0454850011102003400d00104a5038101e642c000880c180c0d5060407001d6000c0e0400c000c0c442008141e03a9803400c156908038950064a20012091001501110500e00c01802050082e06030300c1c00c0c9079546a03501c0310070340c40b50820a40940a2030403404000e80421414076000c416001601401104010700100190944640007100000300003040900c4012400c03100313204603481c1500c0ba04142820203660b94032080d01c0c201c2d040c0f07032000ca0b000d405091030800c0408107000d0b141440702514001601c1850880c0c05014a6615582e5100c034280683c1c4800003440144501d031110350030303d208001003000312040102142b890301d1410520301c00d0600d002c1000c5040d104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 577930197 1250 577928947 577928959
    0x504060b04061d03190b06030303090613150c0f0f020d02030f09010504030501090c080d020c010f080a0e0f010e0106052b0f0b0a0209090a140121020303180a05180402 73
    0x3c1616568601c119040d0b80498050241c00580340074001120305058a0342d020705215030340354403401c051655a100844902485030804408641c040d0000300c022881140186501c00c9050400703d0300a049075444184800071821032103054001c19000141444120481d0021700346280303e404c0041d441e0300c40c1d909000503448000500141a0b8081c5080d280a190008020810380c030b900d11301440c1c038000b10300410f281407160a007142102032000801542102e01031b5110641c680c0c4084003542c9891020307002c0703a0384c6500c50200e014120810000011800c40050010034042c0f0703c00c1003a400c580183d04614083c0441071031039511a03c04048148880340091982068060307103042a00403568181e48c000c01103d1040c0510120003116000703007592640499080c1c0071034840c1140c4100b112404066a180c800c80080104088203100403a1080d502d81072103a406000702c0d07a400a0f0569102944d012200d0071040050070351418032030101c9000d04010340da081c0c00c1d0140c13203140e6007075000000c2000344110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 577931447 1250 577930197 577930217
    0xe2103091e0a06061e0902070c0b0a0815010c0c0e04080f030726150f01020309040c03020c1603051b010e04090f0203011a0a090929100504060b0406 65
    0x1003046075401d905890440001400745085480391166050307481a211a03003403d401040c1031201281105903900c0c0081d501da0075501d00040e200182d04400310543d4003132040e00c000100ca1000000810402c5d44650304c0782014a003880500b42d070010b04181c1c1d03504104100f11000c0000742c90868010a4900c000310a00290f540c80c82c1c015582c1c0728810704102060000b1040c000c80d9a004002105c6400314503441d4414000f000d85181c0d004082150fa16035404525003018495003425540d03000110010703c1982d250071202c002290a441001200c070002a134001280d402001e8113001c014408520400f2180505243d6121981d84d002d000790006019040307150558416801404524503164001d403051110100500340f403c40403040c04c3d4140c0c040c0d42084843c0d003580c11111003160350100700811640429050070a0500140380c00e0744100e4160500c029484015541c1d5801e5000c8821850300010f100c0c60981c1807901240700c1940028005c0d4188142408088015010303501030750103618106042d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 577932697 1250 577931447 577931461
    0x2030403020d0c03050a050f0f030f0d0f0b2d030d05030f25090603201801050708030109021903020a0903060b030c0a080723061207090b0a03020d0e2103 67
    0x34503240e00c0100306101b144a8042000000701d9010003030000031040e02c4032044c1c40103120780c8074403c80001a0003200c040001a0354000503070b110a0f84045840400549061540007046a18007030781c50cd54148840b142d00c40b5081040e087c201002d01c0710550150030041e40b03070040a4214000a8070030800c9840c00d0b00025450b2594041d0080c1d26501d0440d0b0b8240c41410301d9010b400407442d8081c008c006400e05896060300c6840b00c82c0e1480200201c41d115117400c0040c1c060041140003841d4982c1000001c00c50b02c0c0c0407070150005580030344006000103a9400700040060910448a1080340600d401805400a09500102d030303a011a5007102000c40c0d03001041d03000a0901c00c0c03113621190320440a40000c180c145000800e5000d4400021000380c00d508031a00081c0595861141c6a512039810800c2c103c01000a003040d90300301049003130a140c03a60b01d81f501d10740f03aa0031941041c0300003540400c0c2c8049500c11405aa0301c100c0124010f000c2801c81a00107001081c40202c605481102c000007048503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 577933947 1250 577932697 577932713
    0xf09010c081908070809060f0f090c031b0f15030c07020f04050708040311070e19090f03030b03061b07030e0f04020c07050312030f07030f09060203010305030a090f0602030403020d 79
    0x40102c500100385141c41d140c0101409101d0180c4400300082d2a40c0d0001301c00c2000000c1e2140504018200c00c03086e0360f0340d03a05900800368002e01a554602882000c1060780d02c1c20011100408001500001c12958400c00d1080c200440d5120610070700b060382120341550301001c1200c0e006240c401e13009541c1c030a2400484c0f0022aa400c1c8103030024500350070010450f9010001502452003070355520380100c0440151965110300d405030521418120700401d40c03805481c0c003401101d420090700400e04081c01d80f640701c0c501c500c80704246d01281d15040c610180c1d203018403050fa40061886102014603403145c0100429018100c03009061080d440d01d504c809580d8044100400f4400400942d03648500241e00d5440d07601ea807141500a01c42c0d41c5050500000041c00c0d00e2040128000c1c2110565405100700d014241c0f105480d0100e941e9085d442000c81e02d02d0005502840c01080215600c4020950040c02d81c205540300480b6001256000d03c8041e602000319000c9036011644240d4001c018184800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 577935197 1250 577933947 577933957
    0x211f0b03011e050612040501110415050c0a08031f0501091d0403090f180f05090613030903020925030908181f030507020f0622080c06011701110f09010c08 68
    0x944a0700102d440c00552100103545c42c800c502c14402031101d503104502902450007a40640e0400d0301d1020090320a01d4815005400303096440b004a900c2940c1c80c1d15105003d5006581c003050604405908980c90b2103041d8941c3d000705800e02c3c1070b40700c09281504800e4100300b0b02d1203080004c0c034803d01140c2858461102580030342071101c68000d001c1c0e59509084c203204414505e9418260400c1446213001405101d00c03880345d02d03000003400d40303540c0f4010356019002031044c048050290f8007002001503114003592a1155518090407020400800c160460042004852030304043c180050400000c1021003034031030503030352548c2c404064803444d00040d0070f07103a1561711070082d075541000107800c4036810b8006500500e21502035600300c003203e510003500e50004496a03000441c1d40048000f01403103a210107a140d41c0128100c0f8241400c0c20315407410610280e200f0181c804004450200b060000e100d244603602180075040d00c3c010700400300c161503000321700a80d414402c0c04404401032041c01401c0b90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 577936447 1250 577935197 577935199
    0x52803081812040914010e0f101505030a0608031608030a110d06140901081f090f052b021903020304030503160c0f140d08211f0b03011e05 61
    0x1540c0c041c02e0101d8180250014810b1944507420084410348a0002d84c0340f55060303400242c56a50036607130302e800712800071034050030080011600000000f420b602c0c607258421800495074986540c0d0504d40c0307203141a10f40f107411003d0a81c2040240780051030b2044000b55a0b103500000d0340e604ca90702d03c01d400008000c09200c1c00c55541c4006807401e140e40c490b5110b8800e032610480146030544601c800d000101400340107080071036004c1b01024084003409400c011000d620b02c400400c80801a9948050340e01a51400326025442103e41e261901042c0d0b44042e03c502603082000001014801e0007980e0348030b5400480488058038803400c1c03c0c14400d1044a02441d0404226550b80680650381c1d11400003404081c2c8210081c1c01c000302e8048260b000031011912004c0c0c0ca11014032036401005150790070640210380e0f00303100308005a1010782c42820111882a101500c2c10546045214640051400501c080b500038020a080c4400d515840030399054400402d902003290210b00c0c0e8481c81200e540d0056 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 577937697 1250 577936447 577936453
    0x50a11040b03041707033e0105150301022a100e0d080c161509061107060e010606170a0e1203040311121e160f0528030818 54
    0x1180c0c0790300303a100031800f0714400d8500344032a8200036484503260041800c000c0c001045040d07140200708401419045a9840d801c55101c400da2500c01426003219000c00c504c01070751a40100040110034419807214244282c009602c1c0c904030303d0380040c0c201c0c4860407152070850240c55954000208124001c4800e4072524100507842550080c1d95541e241200030301e00050054000441045075039040c2c0c0c2d400424540001c1da414007d6641c5894425070300c80140101340c0d900804000f290147c041c446100b1606c4440503500c4e812030901405a8550515005040c0c0c1800750030064103912542c6e041d00c030401c580702c2c141c0ca0340f10b045000014084172100c00c01c4a21458134000351647d032401c011030080d4440c2c3c03628090010803501c1c554446002104640c007000d0103000c005101c240b40e110610048803d00c820500d041d2902200d00c40613500801e00341c071108011141d080410000300280164201d41503818810619480e080b10084e07417400303900504004080e004100442004100d11903c1e00444082e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 577938947 1250 577937697 577937699
    0x61215070203040305190b0f190f0204090b0d0f080901050d02042310020d030213030c0305010b04060e090703030e060408012d0b0a151b0c031a1306050a1104 69
    0x2d50b01e402c14002a41e46000b0560602da410520307220200519900c101c201c1e44c0ca80d18418249181000201051500e120901c589020844a84902c4410f201c7d11400140c50381d0801d8906021038031068030303140c000c1640909040110b103400f002c0c90b0082c1e5000e0b4002c3d980700700c8400100c03410300480f6400b0b0300160000c203020440704030603103940200120540e07051074400c0d04041044480c22940c1c030030034050b800203842c40724007a211381c005000300f03c1e2085402e540c2580c1c0ea48c8124645040364401e85460355510743d209518074050040400501030702e16060b006d4203294130b00c6503c501d440c3c403008080c05100ca444104585401c41503178000c00d1140020820811808d0f444080210007182c0c0c407407030303d4100030b0801324400c1510500b6405007010303204200c160305004c100440c1092100d000001d028695070380030106804d00c041d0503001c910501c07801500c1880c610300700c0c020181d101461103001e40c80008100d0040b411715040c150a81d00031001160b00e884007611030300100801000d1003c8907000044c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 577940197 1250 577938947 577938961
    0xe031b0109023303330a0303031506091d070e06070609110a0807050f0a0e07020a0c230910090606050a020708120901180902130603050a14061215 64
    0x3c460030000c000d054403c48042102d040040c80c4001ca0b52440c0781171040c14046000c00c003200000710010000c444005460a24034001034540c3d0383c542c0218000381e20703441010700300070801c44040c00800c028204060150304180070714003e508078400d00036031800420002040f40b03101d035006000c1d016000d4543c40e0b0f10100350400d540a4000e45600340c0d0406080d410310380300b50a10003500001c4071505000f502c03003d41058100300550100d40282030f4040080e51004c0340c000d0f2000c00160265036190010040c0310101e10300403000e5000343e03001c901d80c052200d0603000040005140c000d20306030220340c04105551160035104003004590019540c06142810205103c3e400c84000c0007000340c0c68084480041d502d00045503188107800d05c60781440781c00e200501655000c0c0c9030001115140c29003c44010780ca0b040c10001726000a0304001700090103007070400040d40c041c460f640d040803040809000380ca09640c0030300403c10003d85000c2c040d0a112100c3d00c0e00140911031041c02c403500c8412200d55062101c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 577941447 1250 577940197 577940239
    0x12070207050d12031404150c1e090303080901060b03010b0904091709010e03030f120402030f1203010e090105062818090618150c11030a1d01030e031b010902 69
    0x512908003082c517200b24844041460328a10b480703941c2c0b003c14004005e185001e00c0e809021f418080d00140600009880108001c42c0030015014840c0d503a010760442c03850400070002c42001d880005664900352080c001d01d402041140e055070001c6d440c00780d403500c2d4071021a00a0501c2d4001030000c0d400400c011440303148140082250b000266201049405400308040c0c0781e2041070040b002c881401c000380c1901c1da48400790b550307000e0b00042c01d80b0b0300202d00080031801d250040150b4105500000014404995010742541e08214948000c00103807a0500100d1407001b40800c198000c808024200f07510840aa04043c0140c1f01c0c29081520b41e4a040071081e010b8800a00101c54407410107203c6106001d60118003101242c2101d1584204940d07007080c0f10091180d078400d8801c00c07000d80c0501c2e108030f108100901036502c00f5540c04195612164440200c84180408075040508040c1100f1201d0000401c0d105040c0070501c0007070160014000c1a801003850060003500420003c0c2050b0340c44900c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 577942697 1250 577941447 577941473
    0x1e060405061e0f150d05010b100906230918010e070809300f0706061205100e010219050903011a06070303020f12090f0d022b03060b0d06090e0a020612070207050d 71
    0x2900d2600000e0050031062b43c9284c01802040c0014034219070f05080c00c118603e500f2085800c060380d0901d00070f100720200c0c040d0001d208456024400080041204400e481c2c02160703c1456031400e55031505100041d00e4440032120804000340c07203409080b02d00880500c40c0e40d01401802e01171a941e50888d036103006074580100506490f0359103007000015109108102244141d40d2043c0500154800b0500240003403180c02d0510b1000d66080c4591a1801d0713040d00101c0c144812500d41640342c0302540c04250940d40e96803581000d000101002c802152190781c152004030b94103003405a10b906003944099030f0341c001c0d40071082c001a40c15040c030002c0c1402183c6a146402c400d000c0e600a442d285805030f9031150448884030401a800b947d01c840078148400e0303169200f9041ca40454803e560351102aa50340148150100881d520002004120741d14820b43c03000b0722581003e4607480748160005a1140141042084203c48400004040900c2808580c020744001400ca6200c099103090070840500c1e5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 577943947 1250 577942697 577942699
    0xb06130e07030b0f010303052a0a03081f06080114030f0d08010f0b03010b04030f061e0b04060e01050f04020702150a0c1106070c0504020c1e060405061e0f150d05010b 73
    0x200001003951144204ca205060b2901034661070326100c030000900050000040e08130740c2030f0307140690030078030031105002c480000c2c3d000f503a4154160820009003400650718602c407445105500c1002c01c46950495603943c111106542401019903a2002081c10000c9405000708076018484c20019850380100204c3d058891500e06999040e4507a002d00035980300a000c1c7c0c01c8260f1084c4402c1000883c050380310f0041e144250008621120b040c51803210021000b4002840680c07160703001913003410140318450061420a40e080e0321940740002041225904c82c3c181070140b60005004030642d1644690681d042d81113200c2d8036135404076040c0091012120f040102c91070700070850030325407901d4100306503011140c201c44580d8540f803404040100030b40c00201411460700840c6103181d07003c10050a01c1074101070200161659242910381a402e02030000c0074200c2d00c039490102528441d46048445900080c000c2d0040420340b540b0102c070443c800c0b8440d0559100021030400d600b040700c1900b10040f1000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 577945197 1250 577943947 577943963
    0x302130b0607080c0c010507030c082a0a0516050a050904081201091e2a110304030602041a030f150604030b0a020d1d03070b06040908220b160b06130e0703 68
    0xa03004503081c0c401c071423015000030000e0502c5004035240400a28011100c05840c580f83e0814a2804200c0d0a2440c03415a040d0043c52222080c05020300c04580210b41d0304451038042c43c14030b0300280b1600c4a03400b40500030f078a01d0000a042040b150704441e000c52184c500e080482da0b4550340c203400303056816130211000c04401d6040b24000214051028000e02e01548011110003504a00c107030104640c22001c20412083c81d40c0c0510b000a0004001960260718050f079124113140c2340c80360604021041002180e001c208100903490440c1f0240d0308044142c58007030105565800080590250f600f02a0a440c004c01c14002007888030750083c03503100c1c080f020a120408080e8034042c00c0402c0da95410809400801800d40050003880301d0941c05140108001503605541d22076900036040300f803030b104044c405a68000c00304d150441c2580020545e1010366403412820f542c0c21682000b40b07920090001c0845008100070f5138555030f49100799200400c0030032a59075602841070783d40c0030500c009d5031100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 577946447 1250 577945197 577945213
    0xe0a06090203070512100321110727020d0213080606040b03030a1b21110105090316021809070510030b0a0608062d0103050601180302130b0607080c 65
    0x10981d0094074865807141e10f903c2e0a03c203080d1445124100018103143c450303248600c011000814854003446d28541c001c0c140c241d00e42801502504450401802001c950301420b030070402c0f4014114006050b4000c070928441c9204030400600180c05400c02042081d0b0004c00c103201e0000c0142082011602d001044444076241c10003480110340c0740d00510360b050707041040441d086c28001d0030030f441074145641c01c12810040c0c6807140b00b1a0056200718000215914075020300d000c0e808808a540242c0e0b25000b0420780c1041c81481c4c1ea00d01c41c030460342c5405c4451001082c25941e691031105401d07003c1c50a8804d080c81c0001031152940b0b1755000d2144078090305100352900c2440782c03045a0107030102405200b0b085090100c00d40c0c104c0b100802c4294002460140900c02c424002000e0000003442130b145c1c1c210010f580005020303a50300901141c1049a0900c06800e00003030103458a0489030142e48040d10301003000c41c1100601305a0040c00e4001d50005030343e00030010408024400d0b81075007420340e07a10b1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 577947697 1250 577946447 577946459
    0x90e1b01030b400c182714070e040c05040501051206040605030d08070306060c080a0e130908090306060409020307090203191a03070501030c140c15010e0a06 69
    0x44524548140e0420070fa030055012009981615220a40205a0f04011959a2020301c8000500ca409031480e0030344410054440680200310307002c2e00300005002d80d02050070481100d50703000307030740c00d4900416508069044040704e030b50340030039842d10022910f420a4941081d025001754070810303841e070089141024075070101e0b1065007a2001e817070051391747c0d5103000500c02000030701442c09025140e109070764083c0056156010461480180d8103516185840c0ca402d0801404540701c55012409220110105a0000342002c08444020034242000c1261461603004102d14118110b0320b80c074100d1a1001c02d4040c0f2513008040d11010104900315021030380c45500f40b0040d5481c0020080d0191f000d0501403086490a4020710b0703000f11411f440b0f5444070480c031044070540b00c0e109592139030584c0341a00b45a15040030f2000d1030241030207080c10f10201c0c0742c2000c020400c0a01d9402d0040c0c580c1c000c608000b54100c10b1011540d61808440f030b00841d546c681411113410f00d810b40b80b10021518081001506c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 577948947 1250 577947697 577947701
    0x1403150c0403020d0813060c0b0f01120204020703030b210717150432060f1618090c02071e1a0306010e0301050a02180906032104090e1b0103 62
    0x205503115408641081d145034240800b06884403070072200840e09101d02c424845190082400030440c0d951841602c00160420a41c8000054201341407504088018040b155496030b1112941e6810340300140c0d22005414210000c0c0510686282e1080c81041000c03100a1440c094107440d09070801a1007a583ea20884602864100d0a48000942000c4000d00c00f164003210820350040c0203c129413015007440c40d030344a8803410b9400303c2011084641a403184000100070541d800803906d01150494108000c8822549056241b4601006401c580a010041521881000504801d01e05120605c65404045c0d00c5034001e001d0001c400082d21a0b81c140710400314031100480ea08058a06810300516222004980c002401d090510060300c10801c0c840d01c00b449018480c074000c20300161505801480d401c13000800c400030600c200e140b801130082640d03003c1695080561508854019036908443d0a0311074000c0d50301004995184c4000d1030407030380000c500e0391104252480c244407080709210054003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 577950197 1250 577948947 577948951
    0x1031e0816060b012c01050c070803030108031b0307030c0602030a02041e03031419120b1c06050106031103010e070c120c02010206130818041d07050a080d08040b040602070b01140315 80
    0x4601074844810071046d40204000d102c141405001d81d034542c0c0d2a801e40c50310b10b501c00c1e8030200c1647d000065000c0f031090b075a54981140d80b940c03030181d850200703183c90040c2054403542029207916070002c08211585840e03411100144a02d40c0e0924403010791002040c6540d039248000d030085011240d4917646410503a045500b244a0341189890714030040008032420060006400685a40d84800302450f170b480081d104061a0324900002040c1c8281c50804161441a400b03e02407508205002c07070081102000c0e07031b0650303200c03038004601c9660703042c1c048600710841200070340340020544211421540c04084125640d000380c0845400d600e0304036140001d03a109540c0601000c07420300c03204140456160180065000040000c283c400d6003803000740002c11541070f4243c0c1640503620800484c281302c0d482000510307040015001c1c01d02217600240440c48020b0004124100c102c0000e410400c080d4155102c00d604460b904940b580c441034501280110810b2482c440d1003640c00881000c92182d04141c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 577951447 1250 577950197 577950257
    0x206180c04060e011406031627080f010b01050910050d090f0b090d0f0e0d050a05030f040e0604021e1309090308060102011b200a0b0f1e01031e0816060b01 68
    0x4040d2305400003040300c1e0f8503941d01e0010304004140c28540440c0341e541031084080e02258010340f221404040e13105003120340c1100ca050600c0014410900300303580b1010126801d07045030800654034400f0311116401000c0354000100040c907082d480c6024880c0804c3c0c414400c901d058216079580600c5002602c805410a16000001d610702050b0007190400f41502ca548070720903011a10454425511541035410200354802c40e80c002140402011030304041c1150082410b40d011454820f0b040201e82c07286981c003d40d60150000010840f04130340c0034620a2000b040f580344200300c00d1641d4603000b0030391042913079558010343c01c1070307000782e50308000c1080c5080300007039920f0742e680214002d81c0d00e088190030700624009900850102801207003008034064410300306409005c02d9842c00d1041c8801305090121294100c03074441c001400051200001110000d00560040d00c1041040c80d10703418a00c00c5c46a1407c80700b40120a1a00b001a90b030090344c040c0a0036203070090580d28034032445040d90705002840d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 577952697 1250 577951447 577951471
    0xc03020112020f07060c0c0b090105100b03090a030e1201021204030806091314100f05010305070e0709050906041107060906112a03070203070e041b060206180c04060e01140603 77
    0x14500017403195015503900c01d030b06c0c200f120240c9059107440c10898421104034030680d441740708201d40340341c08204000160014a481905606142e4103c1e55184140500107060200306850320280703a40e54042c0f50a55032200000759a83c0301141c00340400764806450881c08100c1440200d9224500300286900c40c3c500c08148090a4030b40b85c039003810b02543d403000c14215000b0a040740003000c1083c061039841524144000c01e45502d1803800c103103000516800b01002c03035030350b0081c801815400b8040b0030031108225480714841c3c41c4c40001400070003070300081309c2c5400c1d000920314080003059081000c107180104010031064010079100e0009215140c0b0300a00003007110660440480203110035076080d425001224200a003a6010074601072660308032a10809d80c0c001044100000c0709070340b102c2e20b890240307120b4242d4582a00a135035100060300016810701442d82e944140d5500f0050460461001003003403200e260381e0221040461000e00035820078400102c185d032103908001c02124000d02014400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 577953947 1250 577952697 577952707
    0x203060d0605060a050a090e0d0e06031308120f0703051005100c080409090b16030b01320d1a0a0509070c0c030203010c110c120d2102070c03020112020f 67
    0x141802000018506540203030b19100c0417525407240e09022010f015519400244403203e112880e2070280742c00422000c002030420281c00b00d0f2201c1c82a66001032450124410500040c0b07011503107401250078140440281408106030010954001070003031038a40c804022640b200345c21001030160301c1c0038143d046407041c102c80100d1072003219074130800d901968805041588844183c41520101201503400c0c05854062010242c01083c50a4040d81c0c1800c0030042d078440701e0000707407801035070509400243d1611525520001900c14600210360320b05d0b01801c0d41c0c0c2580c1603212000b0105941c200e4200c052441185070a401c1c9200b098040d03540080c010162a40d031b01c0802c94040041c583c1c11904031803004000001600c0034000d0f0403d401046d121340c0c4440c48187c00300ba29210030107500c140304594100480800e1364000c11381410700030551030100300558000c60314000300141d0003841d40100d48001450b01c02d001c0d03120b0814007a0383c070236681c2cac0c407201c40b498810900742d009111644a0314201041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 577955197 1250 577953947 577953953
    0xd140c1302094e19030810030b0a0e011506320409020c1906061d04020a030602031f0308210f13020d0b1e0a2c1906090c05040203060d 59
    0x207044030902403811071101224041400c69040211301941c1c1000e00c107203014204101500000c1c4154498041c140400c90246580c503000c1c0b80c0407014200301c00203540d81201259010080d0420106d6421110781c510b981559020003e1411700039240004484051904400703181d000c40000101004046079038a040600700dc0c1c0d40b070025404544511403911031201003066904886101c04849809908009022454001c0130041030203104001d03108440d400040000580d03a607030000c400d80e500900f00680382c2e641c0528a0480703501da0104801c1c403541d5610000200a60032005000001c0c0d009202c507091042c01882c10030307400301654200080100c00700010180e42d0740e030012500060009041c1190900d10351222619500b06888050401c841c0b0088691300141d150f13143da8021882c290100003401c40b401860542200c00210b5800c00b03004115a825143c00400600c00e06070107010301c554034844140b519100810304400c041340c84546240340020706103041c0c030a4074807078200500000c1005030f4550f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 577956447 1250 577955197 577955299
    0x60909070522060801090c0518060f2803020c06010608060a0b1b0f06011406031f08100507020c090601030903031d01060609050f0d140c130209 63
    0x34850020400c0a02c5a01a100c60000007801c1500c0c68007441c544072410400000e000d07103016005802c006041a100040942c2e11004442c0d40c0c0306030000c5d203140700301148009101031041c5807002d03941c00b0000c514603040111800240c0ca502c10300c40221407803003c18020550580c050380c44400b0003600300c0720041080034054040d45501040080c20418603a0b11007826243c0c94010304031410031540f400b00703601700101d001c000700041002c0d0000100403562509003000742c0c9500c0310356124020000800850f4010841c044800c1d6414210a100c0c140c45842c0c150341c0d5943c205a41c0c0c0540b03250f0078580820384460010814850b06400034121100c1175950300015000b9040341c840071020107599050340c6000f00c11808280c10881c80c40c500109040346003010080225020b504902d12442441c0c02c1710210f9561344002d6144030b540110301b40202c02c1403440190034110318521068000300b8554074090b00d40040d80c0145031046048900ca2a0403c00280d40d40007154219080101c07104105ea01000024100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 577957697 1250 577956447 577956451
    0x1905030a0c031704060b100c11060d18050307021e0108070503220302031c0b030309040b0a0308030103061401060c030c200612070e0105070f0b0c12090a0212010b060909 74
    0x2030b0810541d40075400f009000200c10031075050300c0c074a80c0d420082e01d0301e243c6001000000d0380745141c01c40701814281c03a60700c0b00300c183d01e00d02c03032181a00044803480c0304400e4103c00825105a8500c6650b25143c5c01e005460f0360145208034441d184010880c406203802c010610280030041c1c1d43c0f0700441d580c002058640e980080e04000c1c038103425150203064194074007000704031103100c4d40c0034680b500c1c4a210060000c44045200c10708403030a001d64100c0e03584000043e55542c6030112404640e2147c0400815051045a0800b5200510000020007404620303000541038480c03030204a000c60783e98070b07411101c20003803a00050000d40780c882d000c03011070400405e03164041007180780b00e00814450700c000344061303200c1100120700c49801000c100b800c541194080a43d44000c0c2007840c548281c4d550b07455120002490018004080345011810401e10081079038000c00b51121075010328100304d0308850784c50b000ca820492107010720394084603511006008000940038050b05044c14026180c0c2002211400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 577958947 1250 577957697 577957703
    0xe0610090e10080102070312050c18100507120e03121218070b04060c020f030f0a060e191b140f0d02030f06190b010c0804091d030c070501021905030a0c 67
    0x110040450f0000c828030042c4080c9119464242d501d00d807030b058100039507000826502c0781c00303c1840080c5040300c030a070003094440300403920502c0b030042d010300a8955006140c40904100d030034901c0303408155000410201e50500c204d0880c0c1510802d00000841846040000c182c0006a60003083c0d02e850701d10360b402920a4884255000e0548424038408150020303449003001074107255141056042150f0050040c46088e8003070300105100000d559a00c1c581900700034807403039a4580c490321182c4c06000c15400b1b40b94400c000050300c13899040013560900040b4101d5a031064141d40020b601d00f4184410007446005401d80c516443e42c8001c1204036006124140e80500412040034404101401040e101e101c4640503882c0301c1141103001c80444800b41e495074144582d00c00c201d07000c0b40120058030112243c444002c214150341c0c140202019443c511805540c1c4030104a008070214041142c106540c020b07402c0300c01c1005900b10580b554102c407100070700650404c119081c4580d210350301854076540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 577960197 1250 577958947 577958971
    0x10f15110c09090a11061201050d05030412140607030510150e0604060903150506030c0d050a02030709050a0c0905060406030b032a01031b1e021908040e0610090e 71
    0xa5660041001030b041150711000540144079118204000c20958403040b00d030a0300c0c0f5a003801c0010b030203d824014180100b40c03007200a07940c6001000384c10403c680180400e0400c01da800f00003407174140c000312117988102d01c0500640001900300d5109108840c03180c6012140c0c2c0e03481c01d140408501049080c460410b04101140407013040c540c4172080180000d02c580c0e82d0f0341d6030300361a508001059580503040f03496000c1c101002e000e1140c1e00003541100844046850108803030061038a0391502050810094050041c4c6500140c0900c0642c0200e10420400905100c3d00640300001ca41e840b41501620381e210800b0b04c0107108651196011030101d007800307012580f80d9103803401c126600040002c3d013000799450400e00301c0c8803540c1c503004051031441d640215510501c5684406000030ba09582001301f035100044003503000c1442081040312069400c401d00d40580500d00300401154010700032000e15030104004101e00e41004405005e00005035901c0900380e500300080403540700406048814244 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 577961447 1250 577960197 577960213
    0xc0e100e030709110d0608030703093302060403090501020a0507030b0408160f11100503060d11041505040c050406170c0f040b0307090902040807092a080708010f1511 73
    0x1400030300c07aaa5941003520341207505e4498084401007621403a0f000385000750424000781d00001c0d0421098401d8404401f08959290f01d44800100000a50400c0c10306810842c500c42d618260040f41c4c00740968001e984508a19480d1801a82e80d1240031038018030f16031002d001040440c04070000305800601ca41a05841d084101801414003605c1942c180c072814030102078081004151401d081016009503000365000001c0c000c0580b07107010040809028640705d24030b0800308211659070f540d01e400001c000704520426144460342030425401000e00451600c0000107880780139130b05071340c200e42c000d41d600b80c04001c104014a50b140000f0788000d0444600380455000b0076030400c094005030451003c46d07034580c9401d0100400c00812641310100041c4100001d201d001004503207002528404070010445e40d07030810840d50348141d8180c1c0d034a02030a00404001c00b85a1100419000d440e15903110046662114030001b035941143c441d038000545245950301c0602e000e4403941100c80030b8102590018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 577962697 1250 577961447 577961459
    0x120d02090a030308070305160e121002160506060603040b160215160810360e010501030201080a0c050702210a03030509100e1b0a0305030f04090c0e100e0307 69
    0xd000307a400407004168041c0400c06020b0b403521802d507100d400c1000406030500c811201520100e140800c03176025040a85641084100800c085e201c0c1c014145421517407104c81e5141e071040205001030032611030060300c0100310705c1d107088800e6a015540200c01d00c8000c1e21400740300c604802d03020001c901580200303c007810f42e03241e82452540c8210b50360342070751f44104004040181100c0c2c00038000d80303045459403014045452180000005400d81c01810804985008410300f4030290034204984030302c3c100541c6400d47c3e070040d040241240c0c401c0e2106416a1209044030003640c020587d104005601400302d00d0140c941816108440080c40e00d042080d684582d02c0581004108001900841e4650041c044034100c00c00c1028441803450a003003244500111149483c0c0070081c1c0b5083d04014610000c07401c40e030380c0110b22001103500004036a42c6a0710b50703255080070741003441201440c80c50039501c403040c980101500302452030018002001c43c040c01d50181d61100c1c9828980f03825201d15034000c105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 577963947 1250 577962697 577962709
    0x240a0308040909110103090302070e150405101502030f09040902040e0105090d020c0a180507030b06070b0a110306030303040201031d010c0305010312030c090b0c100c0c030908030a02120d0209 84
    0x1078010309202240c050300f1814100480c12000c00f54504162410550001103a070210b00e0b0f8080c2c40c01c019800302d8075122071a080c0519083c0d052a19801441c11040c406d02e41c080c100c2980858081142c952103010400400b41d85900861703d002c680e107101004140410b24081d88440140e07803000b440010188928010f485c212030040350a8080c6d03038400155503905503010400c1c120709000450306102d855051500d00b05440c0120b07520038140a8848002c03e41890203a081602e900c080070b0082a10f4011504000e6400c1e13400f610369808051a0ae100b10f04ea070f40130101102d201c1c0d48064011450b41c3c50b50360046001788800c02e00580b420780400c10b0346070036a0082c05103964002803590b000c034140d411800c01601c05e03032030b00040806140c50190200703480f07604048004200c03841028120340b10707008807902c5404c002c152031030003082a1904030b030764901d036030415507203513810f4040e680d6016056200c00180b40d482c031440341e5050160b40b1448405030311640100042c2061103091901500305605140480c00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 577965197 1250 577963947 577963949
    0x3050a050d02070b060f0f0607031d03030f0d240e0a11030a15050f0306011e05090708070f030603020609060d02070209010f06110d0c020904080717090f0603240a030804 74
    0xb41c0c20315604180070152404011b0b038254003800300d40101030007200e2000039000340b01c5c5600c01010b00040410580c000d102a4800d25003062002d02a82c0d070751203404c2d0391040390358000c0400e101c00b03a282c0100107400035204065074150720061070401240904180200c418580001c103440c0070107859000e1842c9000051000e140102000040415000c6030040301070041351023508428040c0b01c580240f10103503500054040c0c112010740c08441c210700d1a050b001d00c3c89920f50341209410414840c248280941d00c249458031880255507645080c1e503010038210140c40345403101960016007441415440c1c40e100b401803c0001810305c0040c0340500340d03408180c02c1003099001007600380c282c100411640b074105a03004140212071010b000c120800d0880034140349544c88010340200c02c0d08000800700801c200846060365004402204035101204920700c1c40e43c8030958050096044080061090601d00162409910384600c0007008100d030312045088040d64000c0c0e04e5002c0400500080814a0640100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 577966447 1250 577965197 577965203
    0xd17190302040501020f0a261204200607030f050c010204120c050906011106071409120c031221040f021509090606040e0a05060103061511060a0c050703050a050d0207 73
    0x240e2030b685842d00180c10034050040c240740ca90007d4500704000323402105000d40110040c1e49151014242002030480d6000c0c1d04c540b9083c43c0701c1841800207002c00101801105040c1800005e0700040e45c1080c440c0d140606a40100031803804582036190740e004a010301445510301c00014200366a41014465246a058007036400c3c003a4010301b401a400d00b00341c0c2d80e03480402820714811042040e0299035441c100186050100094210810140542c41d001c9800d2840001c02102d811400c150344103407a10f00d4490168424442c00c0d042100c0b200d00d03842507904048691401111a1008020343c40d03004c0c030018000c440c1c48400380001c100507030380d82e041c141c900d40c00102c0b0355840e6202c000510410340e0020703180c0c0748074240901c400c100140950440d15031168644801041b184c443c0401038001d40b00030b230408540d240301921169000d5178048041d681006158081f503090b501d800126404441d81894a040052010015140840d002c0d800400c2184002d01d00b8502d043c0c0e81c2c5240c1012a008200c0c22 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 577967697 1250 577966447 577966451
    0x1030b06120a0507230a03090204050a151a040519090c0f030e0102040f032301020a050702010210051e0702160f0305010c030c2c030114060315060d171903 68
    0x80312a242c0c00b03110300e80e80400e00b4201a400b03c02042c1c407400280e01444542c0c2c11200300054803a80142c4241c03c9600100e602800500280c240400600c000d07240c19050180c0c2920b100e44002000030100d944401d00e11540520b03246040e0a010034001c10080c892441d0103c11000f030700006031000188036440c0030510f580c0d220100c22030841402400d940f1001040c0b081680144002d004c0305055801c07202c11250300000c0030110401013494001c1501864046428551020845a40d025003210042c860f03240f00f6070980d0b40c026a00c0502c0003c540c0140c0e00d074000d203841c4041800042490783d542da03801c042d542c011a4241d495400b00b444048905070405085120084020000c00c0300c24020540f486002d400c09105c2000d007000014415030700081740300410390300803424445425852500b04419103000e0f0092160781d481688407141902c00b076520301e0091003402d50880b200d4415001080c0a658010086060348440f0348860240d0441c02604d011003003001c102220002d10213002a95a0100725100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 577968947 1250 577967697 577967701
    0x7090303120f1d1e0a240905010c031b05040f05090403170108070512031206091e09031b06010e0a0510090e060103020a0b2b11180301051b1801030b0612 67
    0x101180c0075150010100d0030b036201d17100c0140020062034040702c42401d103180f40320341601c6070241d0102406014001074455441e01640d241007541c90340000035007010b00700402c00744041d1120308440c188114800c1003003281c5041024032052620b0350016070000d001c1e01d42051101050f204c2c00c5001c0341d0aa01001c242d9001201c10005030500381412050441e000000d1801c080c448400000c401c14024400c0c0d00c2142254002000035554814172075081806924041851500010340756481d4040120200c0034205110350000e0240c4c0000c00c40d050319400304002d1074a807514110304024003009009080443d5040d02c01051406140c030070141406400702c020051545540148080b003815a0001c114402d8200210150006000d01400760810b8080c9290b440c240800398000c01007106241c1c05d030840c2130008051020208800051340703180d00c1200204082d840c0c45c480c0e2085036841c0b10340725081d110709004401c0c5c2e0508040e40048148018107000c03804181d071170001483c40d403182461050b0303004280c0c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 577970197 1250 577968947 577968973
    0x12240f032303090103150b0d021305031f090206070209090c18070c03050c0307060204080d0f09030308130203070807270605010503010513020909160807090303120f1d 73
    0x4103040314690944010050303a05101c0741680341e2044004290505445e2060366001e0030043c06144010f148103850395071214114080c0c100030b9448103860610204900b80041400c0c9000301e81281c0c1241f200b03650b070740301c49004004440500107003501070781d22a1003841a0405a01c2d440341c001e206140b500050428441e1034001c010080c05800300f1795800b078a500c800c000d40e1540000c0040003e0b0f8050500540700d40c1d104458600e0b41c0f03c1d11000400e000d002150001300000c00240d1140f0404681c2c441c3c000ca0615142c0072600d917442d1384000340004400c240402d51240d081101e02c0da1180c000340075a407c0c2e60715507001602c1e1000503403100e11280d50365400c0c101a16503d10603400c118007000c00c1407140d40c0c50840000c01500060290921070740d042814604070078845e904545001c10007400c00c1141c0d103890291584800081e21802c000b04401d0703000110510310901c04501940c3d03250302d0701201c0061080c03d13840241501c400724881c40740d840c3d45003501490f106100f1140504540d004140c1310000c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 577971447 1250 577970197 577970213
    0x90102073f030305180d030b030a020d0b01031703092a030d05041409090a0b07110f070609061b060b06040306090c0503012f03040c1511010c020d12240f03 68
    0x2488034507800c00015280c00c00307040100d6046d401c4084c1e0718011550700c01120020781407440c02d400c025070000714003040004114aa00e01d450499009050600c800c01a07000010024402200d001c6038540110001c0e844950401c0a109001c540c0142481c07110715030f000c0840c0c41c00c5038026900002c6140810b04110101c1d106080607a9007000759425011403c040600c81d65903c2c4108004104d92001b04c00170320850300c50302d100040800303540e0440b000d41124603003191302c46d80907000f03c5d40090b0000038041001405400c96022410710b400c0c094807a021662030781c0c1e0040c4510b1548580c00001044000007140d09030151f0444030780180400d120b80c0d4900740806003104c1c007494030002116100b06002400502080c082504040c600c0340c143e43c0c944c2c2e24030304080144c440e41c00c00303117458502100c05c10b51181c1c82003c402c40840503070001c0000e01604030040c0e0ba200345030140c41000600c200400c229482240c0c01c000c16035103100c000150003009100e040f804550312900045850401c0200c00c0040c01514 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 577972697 1250 577971447 577971451
    0x60b0a08030901140a110a03030204060f1704170408010c02031305040c05030406110d06080c0111060912070501060b0703020a05150105131a1009030203010b06090102073f030305 78
    0x2000035441c00510300006801c100d030072084d44250320408070780c1d01040c034002e07008001b881352420140c2e80703010f82c0ca00d03015001b50450301440001076066840710300b502c0d000703007200c2e1411524001d80aa1a5a0b44d560b2021520081c4140d61400c0c0800c0c4800101603100340100c1142080c1500910344410744041d20484c159051f0f40507500c554100701400781c120307802070110703a00160080008a40e10340481520300b064030881420008852403da000511160007160754001c0c0142665044440ba0660011981d1200180e50300212500000708440300b2409090081422510660001c24010358400480400743c0141e2015005070300200b5030701c030070003c0601000c03c040710111071030f04507035046ca030100c0d04140a0200c10032240b65586111951a8048102000300d410300608607400383c240c07028020328000703940c40124000d42c01e03c3d0f07038514289011001e946103400d040c0e00800300d00f40340810341c424900e0000e651580b450503210308030010f5400d45c061072038a684201413141c07510026107001800c03a080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 577973947 1250 577972697 577972709
    0x30d061a070b071808100603020429040c020c0a030b060916021009050f1b19150302280315050102010203070e010e130603050703021f0509090c07020d060b0a 69
    0x410240000801c00b412258020f41da82c42c0c1100d00304036203003001030722a00c42e0308140518803d015840300c6140e0300d5003120058a00c2a03c01340403101084014545454042c00304070042c42d040c581c5000705007881e42c1710880b4101e00b84110b038441040e2201098400203d90022b0780c0c4a801d41080102070b04254042a8210340c400b218040380c04690038000303407603001401851300f4058403000c2207410f001c010400c20141c48820420b65094174490306400b1050070f54405480d001d1603045040301c11040b0721040680032910702c000301151001c1000c500314020350007200301c980c0d064000301c0c0000381d00b1780240951507030030701c10b8070b0004e044852100c00003139060350350340a81d04581c010810420075a40c0500c0b0f07160480b00a00b8002101842d4030f0018410107400414002c04030719188000080c8a0009442800c40340295402110f03011285442107244000b1000180410810030140d03100f81003040013aa40400300d04071442c2402c00c00d41c00501001c214450989484e5143c01c4168a18a01150101c0c01440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 577975197 1250 577973947 577973999
    0x2070c0f090e03040e0c0310031a010315090807060209030a1707021801061b0c09020a18050316120501090206120402090106091a03060f0402190909060f03060f0b03030d06 75
    0x110f04031850f010302000038146c4141e42008404500c07900d98040c100800740d0303440071081e1850101000d620388100e100b484103581c0b600341e071f98400c2c050f40400d10511603800d0308151024600121512407101a44c03011501700d40500c81d0760100c1c4040b41001c240700d45000c3e205d6502d80c0d03035580c00d401040300c0401c540702c1c15006d410b102001003240740d40154980100312500b0801d581c03218500e040c5100300f5002075010340719036400028556040c1e07510118214000c00225281c00340300340c071081030540d0340000076100401d02410303031024090300e0b60000005031940d2040c0000300d08100c0550200e4aa41c0111445158440c4d00c1000d000c02c629003000c0d11805001a89818100b0701d140144008081001805514800350004082540f80d1182250b070000c500c0098402d664500181f40e0540e56000c400081e540010203413000819141c001e80958001c881d00e0703c007448031403411074880100030007004020004075130ba11101c448481d24280003804d1004006080052043e19101c07001d0f1005c807201504010140c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 577976447 1250 577975197 577975199
    0x83712110105100504050a240f090e0c120a061103040213091e0501060807030b01030b0c0307050a050a0210060905091203102706151d090a0c0302070c0f090e0304 71
    0x61030003a80380c011644100c07804034180d124551000001c21380b09400e04c900f03080881c03444c41300001542841e01140c0f84446009c1c042a40d4035844002c0f1001030300607601079000280043c85915050610040c0120400255030078034560307558100880340000c800800c4008088204015031500141d40b10483c0e10202040c8034003101603a8903502520800c20f4980c41910710718200080c08030950044000c1c0c450300007240c503c0342c1c903802c1107000d40000341f10441c7ca8417051070016000351082000c1e41d0007115680c130303814102102d110081d40c0c2600550010300c110b00c14600d10014410107801090001c00c040d00c000255400c140540030b061542c890f0401c500307000308000f44641080d020700041e00f250501100c901f49500c1c0d031144040b4002c2c03022844d0300e40c1424401d0210b40324105580c1041c04031025102d6038031082c0d490300c08010824804004c282d012031044002850f1040c181c11100c40003516160042c50840350740c3d500702e4007004a0704040b84100d0340d404184580d18091145143d4004208021070a103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 577977697 1250 577976447 577976461
    0x70c090203010602010b10170711010e0f0f010b0d1101030f0e0a0f06050a0b060d150e07091d0105010c151e15050a0b0307030f02070804060215060109083712110105 72
    0x30540c082c0c05007040000cac9800c003151882082d4840b070b040203401d805480b12402d500305150b988044075400b02a0551030101c00c010103160503024a03030100d40c450402c84480e400c14005400400e04a091540c2e842e48a9a192070300c0f401c18800542a244500d904240c00d062a05003401114801885225040c0c98602a44007550b01e507000d441903a448801c01080a43c5203500044201c11180e004614000611051140e880e4124442c03a050320b0000040c83c2d00c2140101c24000c0c0d5880c00c0c8a11408a0b400e00565400315041c1005100c000c0040700011400c081d103641140d510320000403034052099503031000010144005203214000f003208031442210700e810301500c45000d120281c08002415645d001c108488001501561740d1070381c121402d40d0b243d690312034019440b01c0c600f800c00c41d40c80c0385d603800199485d07005101c030005603045840144100072039040b00c80000d805201003c04420020b84802c00d00000d6031710800942481380a10304102903441c00b01034180345d214207100c85c071039041400700180c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 577978947 1250 577977697 577977737
    0x9030a020d0806011b0c080706090306110a0512040c05060a090614041409130f0807140109051e070503240a090809100302120f0720060408070c090203010602010b10 72
    0x400f401803070318012040d681b4601603484000551055589000d4001c0009007507801c000303074904a034001d031401d100d01000a80518424800e00c0b1848005c00c905115610b000b407150703120b0765031151041d000041c0444d10b03240013504903000098510005516400207024082d442840c0c188014907482c1481e0a0038100141c5d0003c0303560310701c8818003519501000034110044d2032091403889400401d401400301342d50401030066440b0900654409120010101d60994140703e41c1c0106074010010f0004000a00c5417018901d0107501074007e144a6590085042d036000d1000402442c40c0c40d00143c0030101086502c1400e0400a02200321b0915000c1003c0201d00218200c80c1e9005d0115030f035009001d0301c1d12054009000342003e64818021074801c01108920b5020160302030801d1391290341040c0010304405c00c0480c3c00707140604040c4c0140001c200040c030301c20b000d8481c6030b100e56180002180c40e070b00450201e8009a11501c0140c0d100d00070394026003012050000980303a40c1c5020b04200c900f108000e44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 577980197 1250 577978947 577978967
    0x301061a0f03040510090f0b0915190b060d050a0c020d0903030509061603020a1e11060a1707020715141902010213180e0105131101030603060509030a020d080601 71
    0x4000c0c1e81c0000010100b00d000d0060000c050880e8004208100450600e101080c0c0b041d802103c000c01c0200204590480001d403045015020380d403400601e944510580c2036003041c266814142ca034a558110445507100c0300a00314840700c079000007a41d0f16041da00c0406444840c45071a046d5044030000356400759000300c0d0041940d40600b81580e6036540c2101083c81031050900003039003440c0c000c1c0d10701c04065004c035071090000c0c05040442d00704003548110098000e140c100007441d130070085220303e02c03605001d005080740c01c00c141440c030250141c180c480003130120225400001a040f000c0b041c41038100401d43d810b1480098a0440703581421508080402d114068400c0110703030040400e0b0581a200350101c40a13000c5c90074020001681c0da01b5100d08090f20500b0f4650307514204410101c010304144205481655441380e50b20100039503854800031030400300519410103465100203c04074000e402403d02604400d4000c6560344c001d101c1c02404c09c901d0304012410080c1180a001c25a82d118100c03003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 577981447 1250 577980197 577980217
    0x705010306031a0402031e0d090506130603150b13080d030b011b050c0415140402090a180e03070c0e06010804260c070902210c0304081c0f05060301061a 67
    0x2580f19110f6000081c503000009807004480c00568009424070b13500400e0707400031860240c403102800ba8480e0100304c1503010b80222000340e80420401001414440d4110551000da42200d4484e00382c1c0322143c49030a076100c40250340d540d0450b60070030481028104104014200036280801c4040e64942c0000c2642c01d001034401c20b04081c00c0440428080248918201003400034003c204400e600d071404420041f00c1c4c8146c0c411040306c00011002c40c1000d0003120f2180c10010015481d40e81403241c0f0110103800300240000c00c0c0c1d601d401c07000c1d414004100401000f400ba1001803821b074507220781d001c5981030003881141003044043c14400020036803c590448034007a80d615105200060070f18503024090700203040f1582c0b040c0c1c88002801c3c4055401001e04052141c03014010b01900d4821030302908060324024501c0740b04100180100361b030600502180c40700000e060b01001c4509a110003501c0540c034820510035541c0c0280045480c09100e144020068040100d07940021001103017594050b5807494 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 577982697 1250 577981447 577981493
    0x170c031005100e120c010201061403060c0a091203031e0b0a0e09030702030312040506010f061e0e030102072d023d0f080c040e04030f050c120c070501030603 69
    0x2d01c0154021000c5440f14040036005003a183d00025185640c2d0b602400b00c0c3d400340d460185c010400801c41d0000541c14000500105070383e0712182c18845c020340c0000e0b1142c0401001c15400300f15810360003042c150040c0203940c04250380105002c40d461001040600032901d51400e450000140c680c401c1d6601180d00210300d01d0a50340e141c500c000c0c154841c0c800000e505000010340041c0030149100058081ea000d00700321032032030ba00c13102c07828000c44460003820301180384601600030310b84840c03410004000340d42c9400440b19909102007400da80002804540404c10003498810303608404181600503008151500100745291b0049080b60350070010b04100a010804207200c0c81c600c5c40524540d20602d4242403803070000500000302280c02d900d64200018070f0402c042001314000741c3c07d032820b6558245285000752100d42d0103880300700d0781d102000140b000c148070551844034240400030581c002950943d0b40c903003207145110300b400000e8102505252030301c5070a00c00b04050300442d034480c7c00d8000306 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 577983947 1250 577982697 577982719
    0x6091802091f0308130e04200112050117060703060b040306022107020a051b0a05010503061503070c0c080f03031801060e040303020903010507110c060a1b03170c031005 74
    0x10312044510004603400940c221100c0c00010807000038005d000c1c880d0081e0303481c01c600da1112281450004145c801a008040070181000700520a0194180d040414105484150403082482c0160345090713002d00d801481c2c03024a100001000e001c0958021041d103820080f9901f00703075005000b40643c0c04050641c070b03804600a401c50780d40000b0180207230f000f031000040510341940e009550340d00a14003100e01c1d0140f80c5800c2504c04a50004c41c000c90030080030a581a424500115211b8200615481c0e025a01001e480f14450006c001103000d1410381e0745100c00500c02c0d082c09060900c8980c0540300c0e940c480d25030f02e06082404425240c04c0484902d2401881003d003440ea0b002d088103800a1184040200601c000c1682590042180c0d4405400071b000c40e40d14450143d501180c0c8000d1050203400c404450401490802c0040c0404d41107400c01450840d42174044080d42c00c0c8140088000c5100c2c0518107905c4000c500c4890f60012a42000924510f048506040d62030241d01c1254028646185 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 577985197 1250 577983947 577983961
    0xc03120d140606180d060e01020301050102070e0f07050306190f1a2a150f070818060732030105010908070b04090908190309110a081b031212010305010609180209 71
    0x1a0511740940c115009001040400030564002e60017842403501612400000090558a1100061041010000d445115035800ea42502d081d880206002d038041da80c0313000d030303035004154040e00030141000c201841c840608225482c03041c580c00f03290034803800c2814410004030b40b0098202401480034064840b00c400600d1000920741411a40243c000d50071590030031881c9144215028401c5100743c0e12038503603032164603118030101511458140c880d040301c0005880940100081380186004600300040385141060400d04803907000a502500100000100119a80070440801504000c00544162858008901d890b44030307911030454403c1e2517001031000e001790300b41074601d0300c0c500000030a1004c040300c50040c020300740000200d80400b00348c1d5200c001403d0800580040d42c0108000f0100d02c803010803400750030100c0001055051068560004007004407201410354071b45001507001a550441c90603074259070084d04417540c05482c050000810903a4202407903e0550107603080016921280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 577986447 1250 577985197 577985209
    0x90b101d15190e06031606020a1b23040509030a300f090203010606140901051606060803070606081207140c040501080304180b150c0c03120d14060618 66
    0x7004160302c82c94914000500b0103000d501640700c0c200841c2501c07035100d0380100241481c41c00340143e01c016481146101300084e020401d0140d409003242602d40d815035511102400007000d81c01401c2c4d584114030b210038180c01c080c0a800d07000422000518148005144010158003180d040c0300f00e10300144000250b03580341060402e6025500500030300064400c119034034050181c0d500200d01a610b411000503c1c0d40c85400c00814003907803030340300714503002c140d0004550300e400004280c1c0c1d07010070308081300b0009080e901c02c140040009202071a265100c6050450440702c1030340c42003007550454010704415555400441d1082a445072800581d000f1015210b481d200940b040d91303030424509000855035440000181040b240b1810081d228030004083ca0802e0f01e2400000315044164416266620f0140a001c0c0010448003008c0f102d0714040100040e2a0000d2640012407000b0001480300034030090b03004d514460b4040709402c184604058010801178494501a180d0f80003521010105a44d070389 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 577987697 1250 577986447 577986469
    0x1c0b2a0d09020d0f050c10050a0c031404081501080304080c010318050f03030118060e04020402091323060f0d02091305060c0301060807260a02040306090b101d15 71
    0x19001004902913490b10010322194040b0a83d02442260b01000c0c2d01c2c5040100c0c1224414159140c6040c4404810151154103100d0011010b004403408081a031b880303240080c000916052000b0901000070308183c440001060708001120340081005011101c800100c0402e1180d0a00e40094a82d1150010014000d58007a00400602400c41002d000c1d132000009941a1804004840002c090700c800c03580445a807807103000c1e500da40e03920009015182560240a042034051318031582c600c0d00300100380480d001019130758070045103980620020f61941c031060b6800700003506c1d1280140410740000ea60604001d10003481404000b000445080c03160181c0d10072a41d0220480300103003041c80c141e91007500300b40110b00c0011a0100002c02d064843d51400c0700e41c2402c40c60b880c0403104d00003114107903080c00401826900d9000c000c000300207001c91052051450269540f02d03006d0414100310070300012241e1011014001c801942c0a0904180760402d42181035840e400660002c0040410302103024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 577988947 1250 577987697 577987699
    0xa06020d14070611130e0c13030209040203011116030e04060509060d1103030403200a05060406111614090f2205071a120108030313031d1c0b2a0d0902 66
    0x1054914005521172049425941d12580000c480e90300d0304020131543c05204600c1500030504e00041000d41004412103420600160010070050013005280d03032a075000d0800074402d23072520080c070000c1c180e200c660303200c4100c2d08442c01c1c4081031070b0000050700100054180703031081d100e001c0303c8003c01c8a0510b8200d0164809010f5a442c1d580d81c2c103201141445101958a41e01d1400c1840c0b00700d0f10303000f201c440950320020a4541880e0810400f2603201e010340c0200700c010321580100c0720310030111440100003440070542100040c40640140006010040d00070340000416105000d100402203c1ca035a1030361f0340d045442c0d131400c0c0703600f0418a4881c469224815503800d03564101b01e4002017100810603002d890030001c3d0300da642d80303089070b542384011141a00700c403014081c840000792040c071081c808500569500041001860001800d01e4456a40d030b1103403603d02d070030607020088220004c03a4400034007030300000014010f00c0b000d00f01074440c00c92205c02d8100021036481042c0b03907500007101c41c1c0d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 577990197 1250 577988947 577988981
    0x810030b0702010603060f0501120807031101060b09030d030c1409130603031e050a2c030f011a040614090405030d2313030c1209120507050a06020d140706 68
    0x3401c01020340280042e00042e0b40c2c5500384104041c0d022514040d5504a48100444442d0070000740c95003804da400c031010407810001710a10b008a031300c6090140f00c010f000307288861543c07096914101450150010030903801cdc907081900c44003050f0341000c100d040c2a1001c080f403ea44070203840c0000d000c14ac1c2d80c86024080d51a280003c004d251b40030020103100c0c0c4000c841548040800e68054030940280c51401000a82000c08007080c00c41d1110341c0b44210407200b50a00c1c90164900010741081050803805d00181e66524000c0206000c84480348920354080d181000110f0508050b41e421f2040815010f002c0e080c044045410010100101d0710f0310100c030502004074001421011180c10950b00e0b08401008864000c52100c40901c40b1160303021b641901c4410032455540c0e14015802ca03080040414041e40510001d0468800b40d600c142c042d2040300540841070400d410840d2400e4660014821980006050b61405400903408481e007902c0a91041d00d80031107150100c0601412881d042c1c4c028 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 577991447 1250 577990197 577990201
    0x1706090c061c061503060f030c060c02120a03020109200603060d0c0803190e091e0402031e0c1014120a0219050315011107060e0315100810090c060810030b 68
    0x44d00096200c084d041c1640e4060242d5503403101c040441d00072502000c0c0046d1280c6004000841c00b560481580c50b1015044102d14221100002d060025907142900581d458814032030070071104090440360310b030401c10403640c003080c40000304400303020040c8140d001d00c00d091540300a20181900b200024031807032080340e50300e02c2c2c842010315100c0940258200810286a1080560b14141d884140f0038801d034050000f5072621071901003030003e4060000e83c1c00d4010400300840081003a110303061136030302038401040c2c15900303070040c4640070501d28100002c103c45c0c0072803403d6145900085030600140003480800c651603000c1c0ba200207218150407800c4803200300c0b90fa01c0f280350308a005944500c1d04401408080388c0d15500565035100d4030840c04480d070700090014080c0d28003036200b00d14607610103011105a14103142407520781c04000c0e52003520000d2801410032086a042019070040c0440d501d0510644a5980c1d400d9003581190040e40244103080e0000395243c0140345100000716000031701c076604c034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 577992697 1250 577991447 577991459
    0x160e0310051003060c08060105030402012010020408070e040b13060e1606200c04020a0e0909010212090f061303180311030c060c0c060a05040b0d061706090c061c06 72
    0x2d0001448119400da0400001400c07030313801003601510440060711500e146070340c3c07540111001011010000403007114802000c0e40c864007007104180690404000680e90340c03d0890349840d2240c160302118450703201c6030802001413000000c40f80c000040450301c405180c440d00d402e40141c8013048aa4030b951107000e01c07040c813a004044690085036841d03165103011030303a40c0c582152080b0400758260034552150303120f40e501381002e9004181ca14028a00b1003102c02641c0300255407030701b0648480310b042c0c0d00800c24400c048a000b4005800c502c04000030f02400018154068880100074504807d0008940c3c0307440c2818096003806204d5540e0102c80c503031030360302ca2900d118811642644e641c0288180d10648045050410880d072071240d1b000c0003030070201d0700c0e4810004954810310403c01040404c0c480000c1c0c0e09007450181c4002e848400d004a2214202032102a440c80850711031242503001034140440000e0101d0210040c0100342d5882d991800c200d44054680c16203014000c048516162002501c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 577993947 1250 577992697 577992721
    0x602090a08120322020a1e050d15140f0a0203070c02090a0c031d03040b030603070302031c030b0618130e030403050616030905101806020a05090a0b03160e031005 71
    0x842c60820555000619042c0c405940d80041300c0002508050226000e201c240d10303494422648191613400712031034588410100b0450764641c0401c6906007004c017102456144540a16503955454015134070703462600d100c118844600140130b1444044c1c3c00404142e215100340d40b100c0c807a6402a11900250400f490104000c1c5441c901d614006840c040c010500c601d0300304151885102128021750401c0d040810f419603aa2001e01041d034144210b40000005807401d01c002481119a04c1c54000b0105e05c002d03014007030b1203d01608502c03034a020001e411240c1c3c20403009044000302a95200b002c25203540c010742c0141308010910340305103c0030a00008100300004c00303900c01c1202ca400701180b890442426001e603241850020300f0b58011031240e61003c9610381c031810f00301d00e07448084091082c0a0329000101d912454039500000d400140758042c070b080c100107003c0184101e50b507491452a10322a48016441d00c800d0041c204404c01c81e00e0150350350200310480302140026010061401e03c0000400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 577995197 1250 577993947 577993951
    0x111c02090303190e0f10050d02030901061505070302011b090e06210705041a01080103171e0a030e0a120c020d051002030711030c3f0a030f15030602090a081203 70
    0x886079805e1003054529081c03100c075603c09040c80341c07180c506100e841c00081010303410080801c5000c3d965841c0006d0841d010300344160308540d080d02c0c0c10b0b60b104502d080082c00d40380140b100400c991130340480b07402651703481481032003103803d0a41c0c03021082e2a500001b41105580b4030b0074811052012803103001502d000320f001c0f070850b001100d0400005004118088034a0000c014150114400c40e004101280101141c0c6103c04c80350380d03500d4640300644001c0a8030001c0012a400c2040c0081405501c3c0c903014400c1e02d9024403010020201a030740e55580090034080d4804800400032061002000c64641100200c81240d1013001d49410103081c00d403100007500110384140000381110041d4106d248048200c0f9040f80c580005000c400700c201c120281c1c0c0b22000c03000c20407140d6844000417120411420200c3d10705400c0c1c000a03a03282c083c03020041c00c0d40d04901500d640c1e81d180c0241001c01e0000d0464900c100d0758030190160f250b400490004600c02e0783c541c0945002d0044c84039810b409102000114 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 577996447 1250 577995197 577995199
    0x30c0f160906230a1a0405040b0319031107050a0b030a270201081320090c040b0409050c0c07030323211015080109111c02090303190e 59
    0x10014581d2512100d0a40b0440e2048241d1540140300541191844400601c2000303406001d2a01d5030303680750750a100d481c40b050601c0340c500201080c140310500d030074003502468240880043c0711001d6400200100c24036090402000e0142d075450000b085041071105100a02c4001c0440d507080b9981d00b084d03070687d4005c64928036000d1902c04141e0031041038107124103180700e0041aa200c11445a4015101c1000161030821000074400b5503900151842c203106d0054490740e0309080782445800107010803020050003d03d8005070900c014480342d02d035841591700302c0d05070150104050b281c0c849034076211b2040703090f140c1c0503000c0c903a404028190800d81d81c3e001c2c0240c119a20400418880390700000b4001c1c51a8151100b003694040140713140d501d40c460381c021415803840c190043d030f21802d2007400f01501c3d24140c08502040b0040000000038813a21101810340b141e001d140150719030104240400112181c01c2c185d5011a103203c00b0388080045d40c004401c5031007e01c04081702c59001410040c0705085072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 577997697 1250 577996447 577996483
    0x112101061208040611010f020409020c0d021212040f050a0302160906150c0318080f06090102030105090106120f060b1b0a02092703070b10120803060111030c0f 70
    0x30541c072420a036124040c1c010282d1401d240c02c252048030f4800242c14203403920740d200e2408000307803c064801440102144400181c2d0340d8502114181000d01c1212079a095400c500303401000320501c4c104541c10340c204070b81c0403080c0340e5582c5822031000c1d104c4c1c3d8016003a4420f07032000200300340d000a18903940c506011129505a030756035000700241c2e1050301411003044181c50303c0e144c5003401001c41c040003a03c6400d0500c04600c06040c4c1423035041310b0754000d01d403590040b9803443c0c1101d028095185c221074000c000791725542c1418041003004806204030010051100707259940d9862560001c41030090f0460180581d59441c00c1440c0705401c012607103000e500d00e511203001c54800c00a90908003550140c560075003640c3c3d042c1c91402201e01150301402140040f14582c451030024002041c1c5588030b8000c1e010181403500c01302401e008513030054035000340c1d829441e601060310001525804107092034100340020b00760043c581140a5094010314a01c0341d05908032400070041a10342c20b001e031900c40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 577998947 1250 577997697 577997699
    0x12161418040c0e010e040f03030513211439070801060f0e090c0f01050705010f0603110d0c030f02010c060c0c0b09070605160c051503060f060c031611210106 69
    0x10460a6900381c1b801011544012107000002c0d001f60007460784850302000c440360765140d80d1540702611000d0004580080140340581c0e00d0b42d078004204031600800f1081c1075051591502d01e0407007180c60f251015107000348994014003020310200c4c806460140b01d07429600c0c0281e9075091180608074074003c00005807030060010840041c07110305d1500c142c5030000100180382c034200034440c008812450842c100300d01005208003080090040141c0c2040107000066420710358104507075858001c1e40341c01d202d00303242d80f0303c4000b04003a0f1400b2820790340c100c903402d0011452803006813110103d01c50010603860801c141c04070f015400141d40305445019004848440e52181030741621803071240122000304605000f0f0303040d4040e00355690401d080c4124806a012500c030b00002d0350030324880c101c901c01d180000042003864184142044441102521042c2c2003804218032540c0f82e0145103500e003911941120240207102500249203013074407000d02610400c0010129403c900041403004002c04d44c01e00d80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 578000197 1250 577998947 577998959
    0x1707060c0e030607030c02070f0e0a0b01090303080f07030902270a020c120d0e010212090c0319030305060409060513140703050613030302120a06030212161418040c0e01 74
    0x1c054080350400902a001596030b0348800e600400036100b5032001c51103a10f40114200320411048000381c60355482c040303140d14082043d41c041d142c0c0307600203504002e0000c0042000942020460f40c200903420529442d6654840b0128020074003650041d601030006d05c480720b40d150b0309410640600d540c1c07003828070490307542300449130907403254061000582d03010480080f8641c4500c0040c0245000c03030b180c0410500c849480107801c3e40c00490b06003520041031000e102440c0350400000c00c0c141d0301a0050003a10030f0700c04c9a41c00c06102080060141611540041d465035070301d40c0a03900c07184d8000b10400803811f0800c40da03501c00300021412905105030802e90045024000740711402c89500000900e866601d8000b1211445c43c480000c506054007840311006070103030445110b2182420381000201a440d41c01040b029100d11007403400c0c150800c0701d581180409506110060f034650388038034003542c6142030100d80d0303101c44402040f07000955081444101b01040d004813084030718041d1a4070240c0d890303032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 578001447 1250 578000197 578000207
    0x50d06180c0c050304050423040308100f0b0a031805070305010501140406051c140d0e101805100507050703080910050f070b042301050f0117030405090c071707060c 72
    0xb001c0c00c1980184810001c62510781c02c000071041010901240c402a00d10b42071440780c0301a01c0803000700301c10038100040505030072444801803150710a440c2c1401c1c0b400d07034001c1031440341d40700c1d010401d5100e034a09040c4194490b042601240e0040c11603480e1690303801d0840c02400203000360f82c94903c588130907000c00c0c03405006820a03228001c00007038100c0651040400c109150201c112010303400720760740203821127003403004070000040c0e9118103070700315810b00802c07955030801c181100c103026500c40d01030f141810500d5202c003a28400d4a00c90340448007124196614002c62134010014824a40040708111940b4064401d5800550b900400301d490048103945a0040c0c0d0407282c0320079000d000f03150100c5e4160a910750468003c8640103a070b07100070000c841d1050340320781131001c90341c1d1190140710400c0809241e40e8014002c0080695042e091090704640b248038511816104580c1030001c034503194000402c0f21042ea9101d21890880781258440a0a942141005580c850301e442c04e054640c0c2e00903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 578002697 1250 578001447 578001467
    0x615030106050a0605121b0705071a180f040f110403060c020c1302031506071101391401020412030e03010b1c03120e0109021c050303070f050d06180c 66
    0xd605c8490500d8102c00c000c6c0c02d0030300000c2211660302d0b11007a032403403c0704c040c0b0024100c06014a002d08412401e25480c21100c8603a440000c4114004000710840300c03060402d100c0c012002141c035a0003010714080054042c01411f0102c1c045145000c0c039180c6160b8214000344110f84c4550418802c0d140040c00580c0caa503001d465490300404100940030440d49241e004560020b03400d5050944107464001041c030580046600b1100b10000411920243da00030404402c15804461410008050300303101c4c0985004058081c9602c9a204515030100103a01d11090355850301c140003151600d070307100c03010144100e802600781c01141c1160300204407030406000303419010101501300b4407d0141e5084100c0f4940055070141c08019031640300d0203901516000394500019054000b00b02800180100600c55185000110304072040114200000d84003006403540b02c107190901030003505d91000c0664032489a840180f1076103240c05404214000203100301c1401c0e00044000300700c4912560010780c0d00309a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 578003947 1250 578002697 578002709
    0xe010e0f010905070b070c080102030a0b1f0f110109052b02150c0906090405010f0f0501080f04030f180801063b0601121d010b060f1602060403050615030106050a 71
    0x410402805403085d44801426182d218000d9920b180d5521520982203820a0307031061070310303500c490022000746840d99414024940081d24400026200300c0c01501c040d488121500a00540640400d9250001c0d13102c0441c0035002000d40c0c1492508800b0000c0b2032980d0b050714810704480c00349202c40584006448005680c951180d0909920b600ba4800f84a4001e42003580e4014000c0104850784d40f03c9014040c02480c09c980c1607103989040445007900081745401041c10445010100800c0166001d07807243c105805040c1101d03000c2c0c100004903140c0c0003206280254a43c10800084c03422070540c005011100c900d5520a1500301d106280d100c3c1c0c4142c1000040c1c1440b80b000c008d0b2814441445194120b030050601c1d20008020182c107800762540198000c000050f01040304120781003e005403800000c044565501d0a0442610a60305010342c3c1d000c0c8803412803500d00d460854a8500c100c8010b0754000007101c81e240f400c200350700170f0102205021400395003400d6001446013000d22074802600d170 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 578005197 1250 578003947 578003953
    0x306030f0d0c021c1a0603101a0603040203160810051510030c02030d06060c12030b09040803280f0c09080a0809040b060c0f07061b03110c040e010e0f010905 69
    0x66020482c3c1084032071801213804031820310290010301884482585a4912254000c0c00d1070400700709424102401c182e00c0406040c43c40501100c4200c0340341c1200c42504803519920380d220b5002103444d05240c0c40c242d000c2c1c480c00b0b090200b20301100150820b003007a0580001c1c002a9280c0040206c10900314000340c0c1c01c03082c1c80b40116100d41c026002020811a140304481c1450b5480000005440260340001e010900900b41c0c03106100507820b0030f000021980c10148002c250342e4000c500203000050024005d10804800329104140c6a0303054034400e82804c07a82c1f1102c450900159005114442602c40c62505d0105070003042d500800340c5a00b1a011040505a503840340d44540312640d00c001c0a030780e8481da0700c0e0034580055a5a01c05000c404140800515944080811140c900302090b0002c40c1841000c080c84002c42c40452020f0320036550614246040301c40d41542a40750074010bc0e04564030500388040c41c905410150300a030403080b2040700310340da5038a13110039003400c84d80a608090001c0d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 578006447 1250 578005197 578005217
    0xf0d06080a111e04050106050a080a1b0c0809030d08091b010e040b03011b0809210f0702041503050d0233090f010603060b040f0b180a060f0801020306030f0d 69
    0x215024000f54025601d11594902d07100429000408550090f08514013013180460b412849030303841500c03030f0b500000400c410800408038400300c0f62030700204005001041000c80440342002145816564141409800c40e2070040d040a0701a0014030100d0f40000a40714070f42440d09a8400d09080564900045c0c5990540440c41e600f8840034021110750940c0540d215001d51008546191142681c200e060350380d4105820060740c0740741054442d203104d441c03460040710040c4000c50303000308039180800c0080c03556907180111310100300581400c08110311031104c0040b00105019000c64400e61194090b800d8030200fa074110b1480f400c04c54118629a0380384103111f025500d40c12031040b42c507040708030072084070041d605c0f120720542942c8440e00111812510341030200c0c40c41c20240034242050b14041c005200d9113181c00086258078404640c844282d001c14000700c2d4448103c0d0340104050030450074005d001984414070035000c1c0d881520814042c0c410001d0710307412541c010421400b04041c03550350b55004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 578007697 1250 578006447 578006449
    0x1c03140318030403060c020f070305030d0507090e04140c061e0a110a03050a020c0105040501050a0e040b0d0501060f1409070e0102152403033105060f0d06080a11 71
    0xd030001845044900c000301c403014003034001000a400158802c6034007145140900d9002420082c42003c150001e40c040b040c10301c0040d601109403405c5130390702c950004095840309811640607a1a510540b40740720060280030602907500702400040f07100b5005c032404a20004180704541c030a0103d00e01070303048100140c1e02c80e03214550003455506491318000582500302d0780414108050000100d01280001038040c01d1903405200792117410f00c00b400d200b4103252505001810b24412882c50b00e041045140b007042456441d030303101f0340c013070700000c1e002c421416400d1a00900030700c10b45c014101e150351076420000c0c0700c3c40e0b6a420b1001000020300341e01740c1e5440d1483c0c1603a00396804da0084d4194001c8050088241c06500d100d28495080300c0d0b000030403406001c41c6002c003034a083c150726020740c204100c241141104000d40007000c00b842c01d00700c0964801d44d0192212082e99401183c0e10100008000e1305150b0750300040c002c07881c21319104010b007aa54000c40c81c0d0700d040d070000050504120202c10040c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 578008947 1250 578007697 578007737
    0xf0907061416020301021c0b03030307080a0b0d0b0a091b120f0812100302090901140106140c03040602070807080106211506091a010302070b04081b030a020c1c03 71
    0x304645641c00c2c1c010528164002402c1e40c21148221111818003d05903090700c8142c040c60106203c150080c0d1314604103034100030302e0408014011032401e41c82d00d1308049240c6914000c5110550400080505420010401806000820380030749404c040010044200290325480d441182c0c0020500200092555903401c102121501c0546541d0303800e03c210541c0702d8002c920306218088195507154040d0031881042030052015141c20300984c9040702481d0090101071145043d1151070804071003201440520344030b580b240044400c070600002c100003a14503000030740301080c3c480100540740340300c1d202c2614600702e0b0307200d108205200481c02c40e500c40116064004c0400c3e01d0003030682070501003911038008143e44aa502c00e4440030307602d000e50f00020464440100741c2c51000d00e800d620b004410340791685120f030050030180049000003990400c01c0c0c40143e9440c9450b02d040d050340e8840102900294541e00d02d119018000c100a02e1040c10100003d0080b1f81c0041d4540c841c00b04d504008070391110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 578010197 1250 578008947 578008957
    0x140f07080907090c0903171e09040b0411041401020f150a1811040c14030121151401060c03050d09110d0f1119030b0a020d11030f09070614 61
    0x1c0e45000e0ba00022410b06564040d0f43d03084079a6407030f5035101c18554901041c4a41e800308414169410030300030050150000d85c6828810080864001e443e02c2c0c103030001134000c0080071080f6500a250850b6a0b00d001d081d54050011101b1355010760080550ba0401688c8545c104100141560040c0c51304e855025540c0d0301c01e541144080c0c0c00090b1501401c0c45540c0302e0007003007600b5a155403c10718440f401d40b409001d1f140c40407215160008002050450403c1c5a00040c0208014a04000c802e40469980e090701154147e40048448a5541143c007414004281c044140400d1104070b0001040e018000e035244a0780c8e1381e241e56007030329000b4940710590050100e00d1003201c6042d0110080340c0c0740e6a8841c42180f199005160030b50340200c4a203022060545010305d01d90141c928000c07072002800701e080130001240d420070180c030380030369913248101d00030f100740d0b0741030221145081800700d40d10791450040c1d4031071130092201000c9a00e5a0340915603481851043c10002041598420035032092480505 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 578011447 1250 578010197 578010211
    0x20a0b09010b0a0303051201080d02030703110c0d20010f120b0a0302040218130c020d0c03050c1204172a03010204080f1f1401060309020f0a090c0201140f0708 70
    0x2d50041403100040311042c660f4020b0303000900204511a03503807030240c5001d0040c12090001e201d4842403160194503801600f4024003440040000c021010744148442c00c000f5200800780d01a0007258500400b16080002040261201c05c80b147c41c010350003090b04020349441521109601d9000855400180c40d05241050300000040e80c00001a00c4030b0001e4002e010607000c2c01201300ba04001031100c4200681c5d81c1d486e41605240294070340d540c000ca18100d1504081c54150781c1410f1a05003650280b03d213009000c120710079520034400c640a45805081520f0030161881c01b0f55144151807681c40741f01c21311003810f403509224109000a040d186000665002400150038169209001c03418120800d041b41e2940e00b1a807011060390306500b603491116804100108002c107080d88502042c1c16050007031105050b940c21101c402e554400c2c86089000500a00d801d1405440ba0022030160601007102c030003560038515004c0081c1000c0400c00c2c8594400800c901182c1d40e46503042761180c001034152 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 578012697 1250 578011447 578011451
    0x9140a03080f0c070605240303071203110c24181e2404140604030813020604050619120606050304080901091208070c0e0c07030f02120a0e0301110a020a0b0901 70
    0x20100185c9070340035080c0304580c4107095a000d026041c1007400b29009511190348260070400c042c0d0005010717201c603985100c00324640004c6141f410000c4001a104580c06215184201060030b01c02d1108400c80d0828100081c090b0103082d190081c10360010302d00b03580454403503040703043da50b034054103002c43c015003401045c8101e42044558100d003171400303a0060740c283c200c00800004c01061050a0381366440d151201401401c45107040d840007055214040c0440f4103920440403240700b55691241680d029240c005c16481d500c0d008400d0403c40d00040e02e41c01c001182d1018006e810039501c51040c0c000700c030b401c1d0b03c1c1c1904c4d50790b45541e031840c40da1103130300d545044c01815040465206280c40038000000d109126060340d8034281d00349481501c201c1d03408041d60851407010484030310300850a40319425894117101d000400350010a0307080c0215000780c500c502c1d8010805444007a4808000f10b80030909400801900540c184620410700c9030b1480900941c2c07040c005100010109007000c1e500150002c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 578013947 1250 578012697 578012707
    0xf06090d030e21010e0c0d061e02030a0e070605040f29040305070810290d052a0f061b01020c07030b0601020c1909021810020109140a03080f0c 63
    0xa8a400d125a041c8141d501644119122683c003440307010b202c40311090080030301c000010700181650804c4071004040f00c0d180c080001c80080c40c1e501c15500001d4820003907499250641c0000001c000d4401003140501c100e000c00500340c0d02480071641a0f40700000441c1c43c841c28000d950b90100020183c0c58601c40360010860070003e2079101403c086e51140c00035064640c5002100c3e481d08804203414500280791a40c5025543c0381001ca22203190200c0707400d41c1e4412914400141c20441c3c281001d051070003a07001e6500b481c60301340c1d181d0f1000016880c085601d032403440103115450300d4000c0f1054200d003040020001c52120716504482242c0c208001520b0500891181414040e1035441211281421014403d00d0742c0c06201d440340040003903918483da800280b031074918039000c030711031029850741c0010402c0511300404900381c3d0103600541003441001c90351000074000c044481058803801c400c0307007074125019404507260750b07050b0f019038501c1081d40311611981e10030740014024010754001001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 578015197 1250 578013947 578013949
    0x2a0303070803061305130605060102100507030b18150d0f140a03110109051b010c02150910021b040f02040302041a03010c020c03151b030a090c050f06090d030e 70
    0x10800c2600c40d1010320340300e08001d000d00945902d2031003102e010314105003c12200307071520400050b1813030b000103020a42e40c682c200180d00b0800c030101c00500090503c000c1203005034054000191017601a01c1000d0101c500e0f0000070b54441c4140c0f8048020030321040310740c01c2c0386010544960341e907004070a04e80b0103a02c20b948010096803068501043c603000000007109040d044100340e201c50300d4000007070040610039174480781c07255041c2c1f01000740115442c1c12504140d04c43c8180c41d10351503000e061801922410704002c155608a000031501ca018072010020302548003180d03505d9034a980c900500c48aa1010701040041c08034092181103240e4207010010240e5940d01031b940038000d9001440c01c0340c140842c281821354400140100c02c0d5400100300205030786000400e540c015402480403251900e540007680340745060501804070281011040c007e158100380d02100a07148112090054180d5400a1084d9045048503c550090044c8042001401d108001d034130311920a16018080c03100c1341e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 578016447 1250 578015197 578015203
    0x90601050f090904170c150c07050d0f110d031d3f040e040c050931050607021c08060a03021201140907060e0a3008030f22052a03 57
    0x407003550b1b00344e2000d60b030303000305008001c4590341013141c200307074145060140d8031016070741d01c00f07800c441c070810040509040c0518819034a40c03520f0400002039400101500c40010041d12000051010a24904894050140c0001040c0e0514190991120000c8081c48240c0c404c040418100f171540d058500d81120f0100f07a4000104044c1250400c4484241810b08019807031400e41c0c1c011a02803000c401c28089600019400a041050700051902c00d0741e8020307c0f580540c421704840200280714600c103119040b5004181c0d0420020317910390072442903c8120003100e500409030750f07403900700d4600780d01480903041040080703140391a0100045240c111410420042c014101c82850058028074018408507600100c0c5440f5036034116030110542e81011200f2080c080c0000c40004819004080c4035211043c04441020854021134110746900d003e08010300c0e0600e08440c04905500c98400a2480c082d22002c20361080d5007210007400b000e0402500101074654103032016640c502c01440300c0249690070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 578017697 1250 578016447 578016457
    0x50d020316080f01141210050c040329060409030215041113020301050901060c050f0102040306060e0901140403081b03250c12140f070b06090601050f09090417 70
    0x25090445000d00700e02001800c515000c1c24107441c0003108801008050941c804c1001019021981500c106a01ca18014946910140004c507910700303003c10010307800c000d44043c0003160b001340400342d0b441c1c203031482040d100181c805400702c4101e42e00c00851098200740d400700d58403c1c42801103800c03200b0780101c0340024034000c4504a6506a120b07100b01164206040c200110070f071040b03419411541400005000e01405008109c1040a003c542e042804820860308280815444c000c540d650344a0402d40060141c9000d414000392001000c204091814451715109021044e9212040d8859680031920b04001038011890f00c07048030003034000382c21140300440c01002c9802c1514212800290210b0020740b084030207100348840325a2200104040314103c2c0e000041d146881792486259203d546d0b0303a4001d141042c20044008183c08081140391ba501501444084a44101070343d1148011200b502c502450414044020300c2021401e0a01c0c0b0880d81c0c20a02c54042c01003200001c51502a05800c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 578018947 1250 578017697 578017711
    0xe07090e0a0501061829130e061005040b090d21050c060a0b0a17010f0c0c0c050402090114030408070615033f02010609020a02101a0d02010807050d0203 67
    0x2d61070041018541200c003842e001c1d05e00f6176401102a250220840140381c20034240a01c4001d42c404011054003c034084035400f80522910645140c0c03182c2e54041545000c50741540900f18003502c00058074011401c1da002c40e1004440107103444104400c0c48811601c0031022107501c5000046106a070a1864001c1304008955540a0f12062602030f09483c014010344045055403914804e94600d4480740e5840b000da9030700e400000101300000140c140144544105035015034900781c84607115aa2095860010702c0c000c03171581103244d448108010481c0304020f40c0c0781c0880c022010007000b8030100c9001c2c1d51f100f030140700301d0303400d00d4015110103003174074000c65005441e0004520b05004011041e80e4000210035020070003000c0c0b18030130b04050740b032521100f502e0307c0d030b211007600ca10f0314a031007500301e82c0140010f604203640313420b01d000006e503132515101000c611490a00001d041c0441e5050000301c6c00c50801080e00208100f15001956a080081c0902c000c2100c00c0010b007200c181c40d0700046000d682 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 578020197 1250 578018947 578018951
    0xc07060b031002120a0b060f0309030910120c08160c080f161703131112100501150206091e070e0f0a0b0118050f03070314010b01031508070e07090e0a 66
    0x40b01131044d0004240040010b400c840c40c1c0760079204503842e9202551064101c010381c20b56651500118503155015402c009a07002009403082030300203601044403022440310300000c1c404480424029581c0400407102001c0210a1f0550741c0807142c0b040c911400100c1c00f030303885a03160541d12080201141d000c5101c040f031a044482a101c2042170059942802100c180203c5003141460102c0144518600d5005030402c054520582015552400320b004040d1502c000c84c1c0340844e941e151400a4002449190000ca1307881507104500d60001c984680b042c00d0b41005083d0300700d49aa0328034054502561080342d68403c610000c64841e003598000ba0007124041381136042e41c5820031442d010340795010141810080b0700456400e05501c951002e00550700c0840746420f454034400c3c0441d1a20a15a1000e0b02d507071940c44010483d03401c107506c07440d10f0700001c1e80d060211183e400c0c0c0c1107070780769540d210306500e0780d01c0142c0c10411003a0000100f504007415203414a103d075aa0001c0d04400c0c0070a841005000b6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 578021447 1250 578020197 578020207
    0x314010e01050a12410d03060f0308031807080d030608190201050327030a030e1923010b1513051504091a09010608010303020c04140c07060b031002 65
    0xc03510800d400020211a0700e000f040b2441c0340d441c07101e00e0700c03165903501e54020a084c0300d204d486170b100f4801c20039003c043e569010522400202c643d03188103106852020a280c00c0012880c125444031440c141c0390401d000b6451500c9070b1041c00c103401101d8090000c280501030b4046a5003a041c0100300e08100e060fa004a0130740e00741130704103080011302103a100402c0c00721078019005036000303c2a254441c2042d01c010f8001080142c107601c019002c4c5503a100035000005082d648c0c15050f5002c0c81c46801180c0486d00c0c1e040b02d4060201012003840409031407003150302440b000e0280190000e000301c0c4331210010800c128200c02240036030b204001011030354640811100c0c590400320268200401c012603c0350901000e0101d244010703c624020006c031607440d00c520848817803003001220300380707030b0040c0049000c2e6940781001000050280412001800341c0a69020b01d031a0030b001d000c00400b400d20a014064650040c80215680004422120f00b038070f403404030f2103580c2d00b031121825510b149280035136a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 578022697 1250 578021447 578021449
    0x61401090f06050108040206090406031704080f1b10110601030c0914071d0102031c0209010219020f1e12161d01050613360504021f0314010e0105 64
    0x34401001c40350620a280280802c0903a0f40880c0050f00310b40c0550b189036441c030350440844c020303003900d4001500e040d2005855400d20620f00005104581c0c48405840c440410050b11a40320303680c40d01e19241c1040c200c0394140d40351034001450220040181000800c80280000913030804e03009074000c0d541c0100070311040010300e03040e000c1d82a15020030100706860746170074080609070140e600d102110b140d0501441c444164001c00072603000075184018146040c0d950681c01d4080e6120700c0d0210700501926003004880894941c1142005500904180341000c00f04103101e12241700e23044540b102d0300000e0940683d6141d00c40e0702404501210094568000a503211940c0c00e10b055001c1c00f0124044a01040361006002001e81503940c00c0360520f40c0e070049011205120542d41d046040350b54965a0894000c0030b0020801e0210600c0201201c1e4000450a45104843d02213502075004900c100803002c108401c01120b100002d81803c0000f14602603060030b40420500b40c000148146030600103000c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 578023947 1250 578022697 578022701
    0x3130b07081611120a02070519090b030d1d0103020d0f1b170109050603010e12040e0c16151d1f05070f0336110f0f060306060706140109 60
    0x5042d50501c1c42009101d9061182d640c80249094584d1800103c0d42c0c8014a209001c070a00800c4000d10f05088a60110700e01801042d041c441e1241c4103250614174035581c14040b5a0301c1c0310190b680c6400c645620000400c0c0b1700e52021072041810141d080080d02c0030f80001d8410514452034520b0001521301d00308001511941c180101c000074040c007594003003a45001c455005046d540507000118080d200c0802003805409100c003090020b014110030010fa0b240c0c603201900442d1400c0d901d54085403280b110321a41d5214042200c1c8408807078421030b0001c54001c00b1103450180402c00000f802d8581c81c140c040402d00e541024045d142c124405c242d401c185485201e05952007000410409400c00010240c040714880e04204d09041e162040c601d500b80c0e51403507050f44070440b0a1800b045104201011541801714001100c50580640904200c0c2c202810344d004403140c0a004454850510801c10145403c0140120303030141c02006024005905e82c0070720440c91003c0c8a500f04654188284401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 578025197 1250 578023947 578023981
    0x1140919030b040c050901212316150c03030b0d0803010b0702041b02031e07050d030c0305090c010f18030203120c0f0102070b07050c2109010210050c0703030203130b0708 75
    0x4130814001c2c0051150304004800c1c040c13102114814a482c250562400d0302c81606808002d01141c248584000302949c0081040c3e550302c03551004410030140c848000500910072408030a000540b000c24a00000e03009500040d00c4400007880359521003e907903a48034a50f40241c100207003422010500b4000c505290099a10f0801c010308002c140d41d4920300029501c0c0078403c8040380c4e4038080081c89051007071860840e8612a00613003568012580050301401500005c0080c90001c0d11f4000003d40480000c9901110031105a4840804440307a140c2102d042e00c0303100c003507000340362070490000069604120011000e4a0303518070549400d509000d090070f2080624403402903034010014980083d42c244001039100010381001c684a00070100140c0c517101481e0807103a81c0a40d101c1c125240304041e00041d00e0340c1e910903400ca40d6280d0340b0340b01c00401d8410646404501400900441c40000d00940240d07502003c01841003200c44d03107688401c04d0300902a00c5000101702c0346418843d4030413040700e00350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 578026447 1250 578025197 578025199
    0x100606051b0a1e020a0b0a051206033004090216050601050d0b06010507110904030903020f040c02070504020304240b01170708070f0320030a0e070501140919030b040c05 74
    0x120080c803615240e9900300406201801d07000342000c50b070110354a000f40030006d0501d0041c001d44038910300e0340150a641c003a84e4852440e007081d000084003445c002411100004581107441c5d0100344408240e0180c5104070440103401e8000c1c08089907410851000d00313070314001ca00701218010f1050408504048042c0c00c26070254010503c030001080c00c1c4519960003000a10b8403a1341c8040600701081018000742110354050410410301040c5984080d07520281c81c000c4540c1d9400700480340c10041180c1c007840038000517801c90710f002c11040c41c02c0da02840d0300500800c400716501e55107120100c8149001941101c001d83e464007020100e50f442040290800e41c0d4103a01380a500344020003400300b0360002c00400805c100030300310b9064a0702c030b80c00002e4030026900d4000e22130340c999181408036030011185401c0b000c1c60041d1000003480005151000c442c41030f107031080d142c0702d03213800c80c28154031003111140c2080940e5800c0040e0007981d203004000318050140d902640c1481d16014480c461581d01003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 578027697 1250 578026447 578026453
    0xb04052e050c0c12030a0605061b1203130303110705031215030307020d02060d0b15090f0f09060d062903010b18010605070f080408060601080135100606051b 69
    0x2e5243c46200003401041e2000c58000c058403036880040713080141000b50411764012001081e12044408104a00d051600c2847e0960300f01c140041030b205090f0004a4190003a8103202d241d03100440c0c0a40d00c181181c0540c0802c1528190064035078518562002001011000d55003040010002012a0407240d022003200034610b000b0712500011902001900042e1140d480000c0c2c44a0b142c0c080d034820001c4030b4003c0e14512800c1c40c500c1d407808440d0060341c101405000300751600741042c9840e10100a414000a0080403203440d42c1081c40442603060b4800c03180590390b42415180c0d4030f03400100c88540c41c501007003140c811414405250030742da0100025801041012407260000f07003010b026506454161401540b03940307440c1403082e0b41c102c403d240a4004000001e010070301000110303d0522641e404e8039103920030b1740d80744000300b1050280c554001c4007003906942403007043e640f548801424041c183c1103030929800c584180b4121002580314401080c00060290381010140040355410b00300380004d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 578028947 1250 578027697 578027707
    0x161a180d14030c030c190906020d080402093607030c05030f0c12210304060501081203071803120903030201061502061501032d06120f0b04052e050c 65
    0x10301d4450300010b4060b00c0c50600210005840d240510182c40140c04a00124400308014120180c07500030207020b4840180540d00d01d0ba038490740161250740c0a5a805030004d003c60380d4050022001d402000c582d100381e2000380350f5104802c12006800d40301d080415016004a40c903625003900d0003859036001c14000d80100956003c040008a111071076280240c608180480d4000c5034103040544281c00c14084154045142c83d402c1d000c140594442d62080d00c0401c0b49903252400a603407180c901c0002d02c41c02108100080c2c110381708a40320014002c8d2031420300c00032078803641c030910100e42208a04000940b019000c01c01e250742400b81c10020800d900c001022402d94080084d00c803070001307164000000141494a095920a42c4465845120180410307150041c1e8030106040941c4520001030303035410082c0200319070480c2d40d4201240e1394014130300c9000c03089030b6a401c60402c01c003c000b0380d401e004440418115500680c41c101c01c10020440c4c0d51120040c1c940220100c2d00d000d40440c1000d081409 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 578030197 1250 578028947 578028977
    0x10605150904271101110a080d0b0307030f031d0405070c030f030c0f05031b03130c09060f09091a010b0705060112030e01200a060c08070c08161a180d 66
    0x1c1407101d4550003c10ba0300c0000440c100584d140244070301020300611030321f1070020500c00301d40302410f100c03106600248a003401d50000c00d640c2da0407a000c05040910303c0440d4100090107052042c071206a05c80c0300c550a0300490740001e0440700125410030120784142218410180d0085c0307426008855421f08015280751403e0082c40c010000758086c0034480c0010200b0302000d40100d00e0010f01144a5149950b458440038010303850802e44811590041c01200100310203215001c3c29043e40e22000c2c000d44802e18081142c0b0140141d90000c4d10450752502e031000003680c009401d14041c001c41c002280d40c1c0c1a0030301c0c00514005c0705a100403a040d1041d18a03030300080c1e01400f0050060400d10300300240c002d40013242c005060360303400e070030005104140802d4104102c54006203890250b50703d592401d41e482460503202c0e40e06000009104130420080c82c050700104003402c101d903d0040103421091056480d040440e03410940c0d400000101850a0300b4284104103c0200c103124545403880500390091 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 578031447 1250 578030197 578030261
    0x210050108030423130903021501061209020f0a030309050114190c021c0b041a0601230409020f03060306070c03020a060b0d050a0c08100621020102010605150904 71
    0x102072912038600040000014004503510300c50648401000603082c801005103602c01009415401c90160084030227810312040c4a000840c100d0b58203444103140441100d0500740141807032281203a0108600f41c0c1c40300c5584a204080d03018510075200c1c02c2840b0708000002d0604400b0881c040200c000812446803190b01d0820903400c11001e230b0900484004152000480f4000000104c4000710200c02c0e00405110041417154003c030302500300e41184040d49080b0100f6100102c5980703022803107403480a800d98504c400e0003001603502c1c140c0c10341030a445411590907648803825103507007841d0100c18086a4130b0140010743e040382c1d450070190810656994040c0d1149804140500b90030781d5405034065a0f20b0742a4039406844c0e00078180c440c075400c00d1401811100305401800103910444042d9900c4680c14070ad00710680f441c5d01c10401700040c02100091000d400b07440c00300e0455484800c006039640710080207544a64049d12807a888205003804c1c00219240c5586048007500412808401d00c0000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 578032697 1250 578031447 578031449
    0x60f13050712061a160f0206030403050a0f2d111911030304030b012106060e04051b010c020607151514091311030106080619050f0601090608220303050702100501080304 74
    0x80219041700440c82c21700030500d11510310041d402100c000f0401c000c05034018004e01c3e040c200790315080354880f401c0c20110382d039040000007185880345d48503010107100c90303021400c041c8200c40e1504a4458100120f03540c20144510094045c2900c0345a0380c03010010300d0311411170040d0055004500341403540d10786085045040c403034481c21030420851130019000c10080c50600c55008041402017a07501c03000144800d5044030240c569000740c1c0854413000c3d24007207108852010580d00c2101c0c8910a40801500d54072003030040311480499084005001524001c0022030012104002c040c2403510704121041c800103075414ac0724000f80003c00a07100000d11406060641001a804020302d00401080c010205600a07203400e21031602000014403104688800c007098400c01800701c1e0b00c4040030300c00b000005640c0c544c04500140418801c2500c611004d950120b40403560f140c0401285144442200e10b041c0290002629901005030540c0c0402411408c5000107000304076942c07511100c02d88034016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 578033947 1250 578032697 578032717
    0x3010501050c10060e15030f0c0114040e0108070302010816090b070609020a0b0408010b0d0b06100932030c010c080a020304050406090e0c0d0308060f13050712061a 72
    0x80400c00c80b4142c0710400480c00203020001c41002100e80f14484501020401c903074080c04200031503005e01c440e00300440c0c001c1246071018001e24845401c0001542c16030703030480d0140c00310b030310a02c0300051808816010a0083c0207040181040c1e0303045000040c08030100800d5081d4041e42078591404644d8009a90b204440c591500755440b0030076450080b01805d841c8201075881061b1034400720725842140020402c45607098000c02c1140c4d441403c1c0300395450184805003048000304009561820032030350396041c0c2c0c1d034240b802102c004e480c0d082d0003000207041c40782e00405d500d030328852085030090441d1421f200f100407130045c040c1030b904a00080031660f03c0c0030010f240082c0824140803d9008006440107841d0051080c0100c1e0785a04014004000401c2d103402c6500c5021910041800c0241c5a80d18054150740c0e4202c41d903544100341311100c8078402a050300f02100c00d0304090a03040c02e12406010390616502c3c014030550026444d0150307915a00440d0351040504030007480c40c0804000c0b107100e940 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 578035197 1250 578033947 578033957
    0x30c17010612020f0d0f0c03061406070609021c120e030a060e0f1b15031905040c0308120f06030d1715040204150f1b140f01020a0c02012303010501 65
    0x40002e4080290080f21a43c0800c1a8045045980d41c481030304014101d400f0540304000c44458698102d00340c450611aa5905d541c0e034500341c400504000009225660183d80041212180c6a021a81e100c9441504c5081c1405aa02d400208074680380c01604280c000e20340000c0007805600082c1d103480c411400104030036551501052040c1c0c00b803010aa00c5020b81f01a190501e801d103c4043e84002540c0c04a44034840360500e080a40c2c8407242a240241d80340700c0d035010300c4c403592030b180c030024000500192000314071a200000003072107040042c5625007100fa11014241031406090b07110340c00144c10544640c0110074200320440d401048441544004107141016481e2a042c0c0c4405600e80036105800900016000c11002099220101e841c0110764944031100040321007255058071000d0301c4905c0d02c049031411000724200200003408480e4540c01c0c3c90300d1032140b03c2e00c21b08a0b40101480d001043e802d070068420766811030811501a100500315441c01030210701b2a0810b03102c140510ba041c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 578036447 1250 578035197 578035217
    0x50a09031710080f1501240c15020406050d0c0801081c090e0901020406020f0a05120304110d200d02030c1216290a08010612020705031603030c170106 66
    0xd24030b007040d84010010501940c00301c04091090350707110000440580d000c1e0003000f0001816616514251441c800d0884120840090210040b0740540401c501551011030444c060f128080142c0300400050501c0e81b1400d84e1031402400000175603080c880440c082c032501000400120740041a009480012410b45903042e5034005800c0d00d80365080d401c0004030489220421404001c150700a2094032042e400b191f10300d03072403803440325580c64004600078225004007401c41e424800b0840556082031190f41503e20b0301c400a00412480c60146030b01359649440b490400c1c2d071030302c21001c2c41d4407010402d50b12110010300d207130086903503040d03032592070340c000c070b02c2151012001c1c2814031403040445a08180b10800135a90404910075440c3c800c5440c000c08400302d03403440c0040c0301c0300803683c6204441c0c9400e02a0380c41c10806850f8401c081d83c403882c205030204680f90000d44280014003032030840c0c4020b401400020f007002421101c80c2c002040038003502901040b02c00081c10a1541100c9003860109500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 578037697 1250 578036447 578036461
    0xc040b0411070809010201141003020108040804051c020a0906030b0606030c04031202011a0603040b151c030305010e01053003300f0c09010c05030c060c030a050a090317 74
    0x100070141540252a0010030305008202400005001071344c1d090b8000e000002051003c2034807414151210483c18580070820130065004520860b0700c030740143c6005013002c1e038030008503816400d504a14024140607145180031890080c098034060000f0500802c0668216503030000005000f912181c410719004c000111010465802c0311301840d4001c200c424609081503020340a0040740f45d18258a004c9800c000140341066015240300f540c0202840205484d4140b403015034000d0500450780040071800d460000307200326035180750b959100b5074001805600d4005072000c1c1c44010f03081a07200b15006000c1030403004008400700c0311141000c0303905483c41c1d66901854a1031144814109520303618654040102e50814180d03808200c80034400f007a0796032040090740103200110384407a4107900a204901c86540300d0600259054850f104980c036004221461074030f414800c41341070b42d03001400002c21801540358001d403500211804020712220089a40241c407650800c10070b59507814140e4000b03205 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 578038947 1250 578037697 578037701
    0xf04060c0f1b030b01090203151306030b0c07060506030307231f0f05061f0c050a0503360105040603020304030c02040606030209011b0c1e08070620030c0c040b04 71
    0x10081e44403116180500c900c41048041c10100c3c84207440d034503401000050045024000c4074860045515410759035200c240801c8600c4454030100d03903001d03903603076004800240f140c0410340c082d100a9140e140c0b940d080346058003e60342c001b0460360080d0000e11488000031408101404194011210301010040180555140c00d035260359101004050800502d580691a44452030030440101c040c020380d85d5007010f01601c00e05c880c0c2c2c04d00414000901d050b00042c41002105203145c031a505540c2c035800b441d1141407440d0400300860503d40b481d16444400301d030404c4071105400c2d502a07144052a111840003905501480c03080600b0b01d0780000010f810181715081050240e80d00800404c080e68440d45c00900a401c1480b005000c241c3c400180b1212400d261012090583d00c02d40d0408035030305000e03442d8102c500044480c1c9600800c0200030035000720900080c0040c0041e0740c0d5280001400c4a41708840080100106031a5082007000c00c0958002058690013204141c80c04030b080c083c01408640 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 578040197 1250 578038947 578038973
    0x90c05091801060f090c0804020d02060f070f050102030a0608210307031d0105040203011d030712030e030301090e12070305030f07050f30010b0307030b271b0f04060c 73
    0x41e05501c0e203007011484d90b9908107a2001e031005c0c8074040010307a008800588003d4000e0b500650f01070b00b072600b04001460504000c0c102c480300100c502c1c2c24240ba81da02c0031070b59414554100c806075000700420017010001c1c440d14002b030003550010100c05404e071040d50001c9400030f8800160450020001d0000c42c026001410600c00505004040d84c0301d8041e0140204000d403030882c441c0d420302c6130410640040d10000490802142c01652400f8001d81c0c42c69800b0120041980c03e00d611413591840c940c030180301840c000c00f042180810502e100c40d6585003008604014441d0071001805410007080d480001d59034044050101030029407941d400640e014041c80f00d00710100240040e25444a201581d02c8165580040c580d100d04c10b201c44e15544000042400340c41541941400066200e030b00c06c0e001305402020103060b0004030034400d801010344407903030f8003800500440d8100344440d1801202a84d181400741822982c14150f103107121000c1d03441248a44400c103c00001400c080c0100906011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 578041447 1250 578040197 578040241
    0x2010c03050a1b0f0c0b18040e0c2205010812030f0601090510090501081b090108130c06090303020c0a081915151503020f030106050c0f1b13090c0509 66
    0x503c018980340086001d1090001103403921034924000490170102ca0640302140071100b82c81c2100200a4188801007404450188e12841840c003d1501501c4e05000721518071030800040d03250158181229082d038406a2007407000d40d002d88c0b9211b074081700850a0301c0c3c2000b84690000159155080103c0e42d5a10036080903601042c0e1484a0034015000381d883d008071542a00c85040b690f680707501c100c420032034000704c00070400020040d4140301d43c8075590055114031100c10ba40590105502c8010300300707604d83c200381c01003940480140141901002807040c800070403580401c050b424601d1894698003484040f010098419241c40104201d600b060209042d664a0030006004d01d1400580101c07844c0c401d02c01c408101090027a8000d00c00d000b25000200550407583c9540d180c0f4004031620b5101e9942049540070b243d025801e0450140100e948800c41480c0071240703404d5085c00c004265000c580d01a51903450603484a00007001038001000f03c82c4200c0f0390914a0f0750306a040441000c0c091100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 578042697 1250 578041447 578041487
    0x507020f1224071407172d0d0501050d0f02010e03031c090c0e01030c0b1c050a09060b031513140f0601090501141f050408070605040e0c040302010c03050a 68
    0x2644042c0c4000b1500340b06507a02e9803011200300300044044c5903413186a401800f000e0740d0552882c0311424280081203800000d03100361041031030910320361074680054103080005950001e0308544580c59405494054001207403000d44220392661646058088070f04001c1c18010760b0f03100004244d03403c0c03090340c1104121800100ca40c403211219100280b5a542007181c0c0c8180d011004101e1501540e8882d041c0c941c00400f8040309420710040d802d00307404c030300403030200b0100c158110350800b100d9004a43c01a80c4040c0c005ca8415000c0c503025094500244605010b03611101a00700800b00c0b00903200d42081c0400d04500f080907007411b00c804c406004521031f010500c46c03a0035240b9881c80001b010383c121554a001000707166200e21000f010301c3e283c0d15803240d1080e0344c080090041070580070758801080301420150700e01a40c603c00c2c1c5040c02e68960010300030034000b040820581d0410104154061503642405241a007076500290454083c0f20015007000380c0400c44d0a2881c0c026050240c1d041680e03111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 578043947 1250 578042697 578042743
    0x90604020f0c032d031b04090204030b0f150f060d0f020a0206010e1012080a02070315090309080a0c0b030c04050405160f110d1115150307060507020f12 67
    0x4059907a440b002d0942d00c00c441402c071440d001c8210302800807004405045192446c1c0703400300b0104480002010301054542d040000250381000c03840208015440342840c0d0902c0c0c50686030164040d07100a01c0171541d0310040128a0181d50307070303020510b10180c080790f5180c1c54882d0f02c40104010140c4015590300c1510004180b448981c000071841e040b030b00d113801c10400ba2755030100e681c07040301424422500d860001e41a0400080d410b0710142c100041035104841d00c113552070302c40b03000100300c9008c0e941c4001e65441c2c1c0303030081c1584640500094460714009010008440d40d50b107520603041d120f5a0010b42000c40400d488036103d500300e90007000f005100f44000d09105180701e40030031985504401041c0c503841550381c554080c2c8080720350302c0c44034005041582c4004505596000c0841ca004002d4000c030700c4031894404441c030055024504c00c0700503c4510b03101740c00740751410300d43e50416010700100340702071401030741c6402104040c10416038105694402c0e404259182840741c0359036034400b08103400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 578045197 1250 578043947 578043967
    0x10b0a02030405042a0306030c0e0c0904052418130807050601030309050901091505090601020313080d03050106090b070f0f050a0627050606040e0c0a090603030e01030b0609090604020f 81
    0x14611010000c40500710101c0d1710000b9803c9900900c0028840040710300704010502845406640c402080300f0b207a0f00d0600000300080c2103c50855501c038001005000c400003520584519100c0101e040d42e501c400720b074014100ca43c2e0480c3c01405080906a800c0303006080000040c1034641090b40541250102e507102d01d80a016030402e805090302440e441000021101c07a80d00604420710b282094200015080400380322104a0007428103041d488100302d0201d030081c1d0b40c11400020b0003020040c1a8400b480c0800505507031042c2d0110301003140080050003008941e1044480d180c0e4004007503104100720f80790001c2180b913202d4020341103000f1002e03e6414001c07a80c0102000032203a01c6000400700307041c102551040d403006e00c081c00c99032040000823a642425032050001380e0448040f40d00901c0b51500084440c040780e006a00242d44401081040681010000e0744005003400c0920a0004220104045000744102540300d8a010000b050b140e8a8680c120b5542030194072031a036407100300380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 578046447 1250 578045197 578045231
    0x211b0c2503020a0e070e01030b0d02010c0305090319021e030d0e0307030b0a0c110313140f030616020105011410030507031b0e1503010e270a0c06020c030d08010b0a0203040504 77
    0x25017081c0451501c9401840c5503119100707641044000401d8001c0050454004481201e440d00f070440c24040100401851641c0400c48281207100c90003031290300582038414403844031036070f15000c500580d1300c1503010810395011400701d0f114802454040d1002e2011400246025400e50000e0309200c0001c061028200664000410b61045034a410300f001415004a81d40c1c0e2041d4222840c0340032110030180940a00c00002061002c0018034000d041d03014000020300380740c82a2480d4040021001c41c050081e0303020b000340c03401040c0c80305442ca4107490002c08625040a560b08a104041c0e59600144040307020303a00070503c5044c20031190f0aa14402f960180200d11080c00051140d1024400b203490320070301804a905842d040702039540c841e1200f02d0b40e40c8913480701c080ea50201b42091125650101800c00c64100c1460041e581e041840349403ca01900781410341e60140c4c041d030000b104402d031164101110328115204411440c1d40c0700c103600812402d600441d040701c3d600504280d500d01d80c01c1c07221 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 578047697 1250 578046447 578046451
    0xd0213030506160905060d1d07030311010c0c112709011d070312050f0d0228020a23030d020c01141902030a02211b0c2503020a0e 57
    0x141c00302c8520380c541200182c0d0041c07031821144002030314440d00740140c0c2080400750282c03005000c0003003040000c440f6441d40d00081c22064090300e50100c80304005055000414a0030181d14500070001c07540190740050000d40346000c0a4000161007400030156102c0300c5030814070404051200700780c4011541d0400d036240041d510a9000d60030416100c03c01d080c521781c015019403021005280302403440e515048024442e041036010710805000d091001e42c0410010220101c68140c018ad9070002c025990449404041d2400c0b1911500800e40f001140c0003c0c0c0401002c0d0088044000160700300c1c0390200b0001c681c4600070080c000402c1c88100c00030346030040e05245000a0017444004804145407080719421102c42174040b0090241607605001030b801140c1042e040400035140c250045129030300c05522802031404203040f48108151038426400ba44911002d45100518100000502c1ca59604144100e0520050b90342e400103e0210540000d100855010300700d403114070b5990701c00100d00703013013 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 578048947 1250 578047697 578047703
    0x10603020906120c12031c06060306090e0a061e0c0503040c051008040b0c0f0c0d14032404200307022b030b0d061a01031409070303080c0d021303 64
    0xc00c00310b90a450500f01001c401604000240082d0503000300300303d100000c02400610500041054160b98289146c0f4005060b00307813800030804500d00f0314001c00325141640541091480e010025075501030205c5c0304004c039074000708040340101c004041c410b08518a900a00700b114940b0b20003889540d0080003961042c2d008448072207602d55150207002e607210000301144001150a00010001391500580b0ba80004000340b8035414a00d0f4028200080d0303020701ca0181081d84261091518164010010704c10599800c45003800c604040c0e400c082548c03510a07910840d13071310840d42c2c02d440b9203880d44100d00f19070200580302c0311001c00000007150740d44240d40d41780040c042e6910b82c00000c0c0e0040f4482c10002c2d000303500c6408001050b00c0c02c80051203100e11895000b040a666140030076a2030144540b41d8200141c001c0728000c90100140071111900f401d20080681101000411400801c24408032505420610b08039a9500401040e621600303003120305d500c0c4046034505605480540040a8030300c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 578050197 1250 578048947 578048959
    0xa091806170c03120c1005040c05031c020c040903020c09100510020f100c1806111612030e06040b0c0d0e04020921030c0601090c0201051b030c030709080d0201060302 73
    0xc910001c0d503110000d1211294159000c0d00103034600501c1c5000800412142e0700a40303110412441020095800694050b0703144030080d24180000e1400303000d030751000e00d004811159102c00310140030b501e80e011145450310642c1d48141038000d050007840f182502c810021f00c21009441c1c4184840c003c0c02550140c903001c0e000c82a0f030003c91900000e01c107900501c01ca401007428401c0145a007014006500d050302c00c0200c550103954072a01d21440c80006401c2a854107000c54118002c1140750001945007807042c04c40c282010420710069141c2d460f40340360145000c1200f00005800f150052080f0361100303030951400070308165080408518256040042d5030b818507100694400c01040c0d006c1e001c0f90036440488800001100030400080206005101c0d040e40d00704803458842c541003130300c03d0703105076402600d801d02030001e5542071080940c00308e40048140060389520000580e540401080c0d4a001c500c0080410590350041803808000c2c00104101d0314480750701c0d003000b8080c058500c0224004d00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 578051447 1250 578050197 578050229
    0xb1810050109140106021504110414090c010207050105030412170c04080c1e0d050709090305031f08030a120906110a03050a020f0913090602070b0f09030703080a020a091806 76
    0x91090f00b8081c103c62880d802020310f101c11499040c2000d20103070044500080344080c0320401e403250301401c00d64810f00600c2070120f28000e0000d60601403501c00640c1103400c451814081a0307080001d4a030803e030404035400000c043c500042c0e810100b524a00f035058107248040040c1d00c440d1720010019561f85800760b6204010395024007414134802c50f001814040203480200580c00c1941410a00074040d4040726a081c1d910700821040700c922102c123a000480002c1044603100040701b1500c500c2d010302c007a8070074a0303140c10b400a849003d012107400c02c101c2140c404d180c0c03240742c03904900e241c190810010404044e464800e40c015034082091500070a0800c1d00080d0350f42c8192080d2170303030003031841c0c0c04516000000d030802c000815103603a01c0b911a82d40d038145401041c0c1c54806042c60342e1003003103064110300780000c3c0c46035101002040707500d0582c010002200000c1d8000c0381d194114a40c64005a00d0b15140c0308241e0b440701c55038000031460824180b03070126201654101004036400b070301401c2061 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 578052697 1250 578051447 578051471
    0x2030105180d03060e190b1003090c080a050c1215070302040e06030105090d0c060f05010906080624090c0d050f060406090213061b0804030b060f1c0b1810050109 71
    0x241e06580715011003103485c000024100c803104c00d18816103900c81c0743c0000342c60010800080041c06020b1302d10b00042da9444801040007401440400a42500700041c14145015502c0d9a620070443c01e046d8000c2501c400402c1c034020b002c20940328540106880aa6649042d0b41d0080c025009840380107508408040858000d080c103201d5070b409081410064090194040416562180c1e0400222805ca03501c0c128800c20400038800ca0b40030f00544240801c101d850044004e2501902500038411164044034011000e00480f5140000000075141551281e50300e05c100807150151000ca0942c0c02d040204001c440403960011038880c02c0102e0b030130490310392207030040c42c1240901c48070210754030015601484128051080000c011405000c0e900e000d6500b65601d01003600241d104a404003844004c0c400d0350300d8000d02600480101792000218596040138810320f484c81c10707401600300d03101b2201250285407a001092620b060180448e000305e0490383d1000d009041c248100c4480030b01e842c2c0c6200003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 578053947 1250 578052697 578052701
    0x503040218090703060c050d1a030c1e0409030c1b050102060c0c1b04061806051c0b0a0e0f2e14150d020904030f14040f17030702030105180d03 63
    0xb00e8003000108980f50855907510002c04402050b901800f009100c075204014072030260380012441c8810502c1d0f11041981458a4440501c1c03002c2c6c411a1100710401414152003421402e0610896002ca40c001c21400c05a40e20b403180d88010b40035900e891045100d55603480441e4084030402e90031100c8613a10b020050702c0f5405180305840081e0000018a1b80c1d840c5200740461649400500019070070343d440d41c801b5903d45aa80511101c2d0752507034001c1040b4940303105a1a40c00c0300701b11070030b0f4034030315142d46001d03108800030b01440c0d407aaa00e80c43d00084140c10010007424955040c2143c1d10f0100250101860031801d0b0350003400c95480b1901445022003900548450350410101803103a51200c24400d00000c3e201d0740c64542040c05500301c1d0015a44041015000d64001d442e11011030a140c58000c01440d82c041a5514414082004101100d0202c95840440d40c44d0b1400401c5070194529042c00c612400d0741c0658103600302814016081441d52460400c603825508640208036aa841541 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 578055197 1250 578053947 578053951
    0x17070305030915090c090907120b0405100c14130e0903070b0627070c08030106090e06040b03030f0711030304030506010e070f020d0522150f08040b180a050d0503040218 74
    0x4819003040b02000345c58248200c50507000201001650780680d2505c1550b00405070154003964200382a40900c02880000d1180c0c07a5541c4038102c1c140030000004801070800d410410150461142c00030b4545e10102c92501914090203155503983c0d914140064502d55a0300100000e0340c0d480c13102400301c1ca0301c0c641070100c0c800060150074800601c09000301c00400c0d07201d000f440346062212032100e841c00254100010360103080d080e11600038082c1085100451504002c05041c0154641042c003190781c0c1d000000d9480c401400b00a55035201410b10300a10a0b13020041d030240c05110100d404010410040303800303416124021114881a40c410908aa04600100071080541c01103c80030980038414002803d080b4810715420107810401c4003004501c101c0c6030302082220340c24aa80c01601c951040a143d146d03e21740c0380c2218a07042c1074648410101c070180091881c402c140203212480c1209106144440741c000c010395500c40c1c4041d0300604643d02c201c0b0101d200384401d91210a89260b0721040324 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 578056447 1250 578055197 578055211
    0x18031504060e2b0306060e090c090111030c0706030c170c18090a0b010f09060203040b0a11150a0522030806012736020717070305030915 60
    0x154191034988070350008040c810031400700340c0140c4400c2c01c4150030b48941e02d0250140c0709103801d001e1840c024010101e4000307401400c00c00c242000f00c54600c0da20048401d40140e0410f5a2513030703030011100103072038070040114810128007011403c0b07580700d50081100c00841c0ea03c0e4509200b0024070a208450102c16610350180d840c1841d400304080000410280c94120605030411800701e01001c0054050322044907040e220031345843c1849502d580c00202c441501015040401d00c250520f140692240124003d8240e1040c01044e10680140714098000000c3c018201382d51503c80c060900030070341c00342142c5503851942001d001c610280f010f00254440108124481d0343d40c514650380031254410090402c0c1c0c108141450158020b40d45500408030368441541c1c0810b155192034546103c5500c1242c20070f52151101c0c2c1d800c0c0110740c0c4552000c0c2c0f14040310300016516449072506060300ca02070119003038940d1004c103e500c101900100114011100c203c1100c000003510050401c201004407115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 578057553 1106 578056447 578056483
    0x307140c0a05010c03050606090904110d050f01060b04141306050a060c0b060901240302070b0109050402181014030a06020c01151a03040f06140406021803 68
    0x185420486a0a0138009460120005448c41c0100c03580c07036028590110000d03040142c00380007012854001084100784400742d0030002c0e07482801c4c000e605115881c000000c0742f0042c4100954040b5070022200d1800c1e0301480c82401003030016821141c003400d0303d030b0001147d99940d4002440c09002d00d075451421950035402c000c05840d60103840700e405000b4020041c0810b070341200c001c00d10305003059010400040e210100320028456804040e00381078942d80042008146504101c2c000c0e03000302c0d940c04820070640e09407008002c2c00c1e507034400d8502c0003000802c0b019240f03c3c10818289002000c0c1c071307441e00e025120304050747d1040314120f0559541c1c6501240280080040c0c8000e880340c40c401064500b0040080c020b9480086c20203400d0203d0600004100000340d08103a2100003501d0906c14141018070f003501c00b07034104084408200ca40900007400e2070800007148601103944c1c00e52 = true := by decide +kernel

theorem cover : BRFrame.Cov 577877697 578057553 := by
  have h0 := BRFrame.cov_init 577877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 577877697 ≤ n) (h2 : n < 578057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
