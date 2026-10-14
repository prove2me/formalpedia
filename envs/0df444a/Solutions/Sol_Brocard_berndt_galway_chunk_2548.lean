-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2548
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:02.521379+00:00
-- url     : https://prove2.me/submissions/a70f4fa0-c80f-418a-ad24-4faf213b1f41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 458093525 ≤ n < 458273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 458094775 1250 458093525 458093527
    0x714100207050d062007050102090a170d0315080f0f12120c1b010608071a0705030406110304240e1f0e040605030d020a05100216030e01050903010c031506090b 70
    0x484e945811000003c1c10040d14141071400c206106002074002000660b101d03940480e0f0f0701000e050262540d0040c041c0e49909904030515070188586c1e49618600070130070152a8160002901c04410000026140d0802910090048074100c0ca80da0424188000c1c518420030304441c00c0090807c04850549110442040c480e65038464018280c0d805812001d4101401a0403040c3c610021310402020b84106000303854614035154050412003042c88151503080c0c020080c0a001900c00003c5074116040f608200040c11600b032030180c04c60146500103114104880e1034010743c00c0707400c0d60103e00307200c042d02c0e51f0004070882014000340042c0159401c0c000c4942c0c403100b4510380d010f100003003800c400040002c5042c94035000070130f0416844051140159200c0c0c04144104002071041740300f00d8020050031420107180140709241c140e82c184d0060144403104088044907440340c001c840c44401c02400901c02c1c502d0704031004000b4a104044008952448040880c010348118600802c0300e5540c0b03021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 458096025 1250 458094775 458094799
    0x6030519020408120702190e0a0e0f0309310f0606030213050603131718100e0d0215030f060a0501180e10080f0d03050a06060f080a0b03071410020705 66
    0x44d0425910500d010303030b4000d0b84042124184094280d00e100078000600e60101c030703810001c0e10681507440304aa00521078008410f0031300c4d01c82c800015500c0c640411940c021041511188864280940c541c83d00aa03010003400c0407100d01d6030f07800103403d21005940801c0350b05d681d55021012402840e01c0b15001800745002004a803510304051500301581d01d044040200e90345d030b10340f9210010030421502d00200030401c0a4408401300c40e0004401083e140031604243c81e840040122110b441c6c03146c400d400a0117001e0564840d84e00090600036108151030780c8e400e1224400403a0314044500d42e1103000c3c81500400c140d403007090300501e01c0d24000c84a110040c108031200c1c035900c50080c42108520541c2c00b000500b02d0081080f15400005074014001c40d00c464000142a81d000520f05a07102d81070a1041040c0b80e80882e94401c00c40652130140007680350004080060441d903038089a25100b400c4002c21114044c1070f02d1a0110022210740720054079001003680c0700d050503c0f689a02044150031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 458097275 1250 458096025 458096053
    0x30f110d081f081b060316032a020606210c0d0510050c03040c05030a0f03110c120706022401030f1506030807260f0c0a080406030519020408 62
    0x407260400710a02000004400d5001002c01041880c1e120f090703180d005042805801800ea5030384c4400c0309080d138032185140f0380020195018060240f84600300741c1c2d5808688a000c1000d5801d03007100c0d0310101c4204c031071000b0510080d5101d1080d00e4107882010700401000e40017a4111042c284186008080e0400f03010b04801c010840a032444165584c2c0104120140101c48511403540700b00c0e18400066101d0800703003006401d5a07941d422842c0298088022007002c40d058059040c810359051408030800d064155a6a08140074410495080201f240802107413401c0443c504080c3c4241d5800c4a00310441d4810454010b5145041180380010f45001400030400c502418801035010303424140c5590581c3d100c400454942c0e030320030f84508001184080810403807404030001548613040c600c941645c102c00229551040d0030400342d2030400010b40c0c0c000700405100045625401c02009600c1d00daa862024000d0311003203944903803464210740f610381da200307803442a1030589407424020051140c540318 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 458098525 1250 458097275 458097287
    0xb040521070519050307030311100c0518040e0706200a020a0e0702070806090a02100c0b1f0f080c0a0524180301022208070b07020d0f02030604080403030f110d 70
    0x4100c4545401c5501c02240313540f420050f41c0700540c4640c1d10b402c46031056a010394180448d08100900312400d0601c02081254000255a4021100019122002d444000290080070701c2041c55000c0d0207400e03400180b203504030803842c02c4c0c2c140f0030403024a80c06000e480b00d9100c3d84200802584001030007801e100c4040b06030b40302903002c0c0c1d81d40100c4840a4580c04507510340300c000c541c40c418550141c00306000b1420002c290200900c10b50510404801c1c42d962207022081c0014280034071402020382c66012800040da6401c002c0100b92080d1806580f100c08247d01e4400f01051140200c1c44240c00090f2420b2520700038240c44405d511031200e03140aa901d200b2075a1140c6a58640c0c890980b040031030341d540030301c0105860031044089a080d06080d25071103802003041d902a2507560084a010090313004001c0c102d408072941202d022000460a04e401c082e1203003020406501442a802040100102c14004009981c004d0319040904020040211070380750800c00c2860b010340218041480f10fa000d05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 458099775 1250 458098525 458098549
    0x605190b0c01090c0f0303201519090f0b1006020d050304050a120f0201050109020f041703070503040e0906010e040f020d030c05060c0d15050d0b040317010b0405210705 74
    0x40004a002400c03520742004c001c05503000b02c921413841060400c105900120201c00110302c2d51081d20b890f41c083c10744143c513a030801190142000140380000c0c110880700140c9404124080000c00406189040500032003000c850210340b50614000130501e02d02002044004980c4c880c0d0003405040004d42080302d1503000504100c4462007210041c800280d2007248588000b84142d41c1e0305a0030390400002800d40d07406900c1258600c0c8104025100d400d4480100e8050350701d038803544d041d007184904005e49180329031a8050701500000c85d0200b10355608403211070040005008580f010b988680b0403007005c650580b0700400c1d85004011840040c10000c620040d45070003130400344000380460b103500f07081a40c101c1c0c0c2140e50341c4001665002e202058450390210000490740d0b00240b5041c6400b2610b0400301c01c03070240181d0004030000701054483e1140c0b0458400429078000a07507900c400344200d6030001d004980c41900c0320995a40c15a03040600fa652a106400c028070354286080e0034000300c84000c2d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 458101025 1250 458099775 458099797
    0xb010e0901060f0e03030f1c060503060a020d1805060c0a050403080406020123061e040213080d031404110105070503041206020d0b010309020f060a0e041d1203070f080a091b0303030605190b 83
    0x9d07000000d003940d82400401c0c8600031851000d42c1d0340c200c00c0304110484220510500803580840341c90310115100048141d800b0101035050740e03643e448400f040d00c842c0510ba03c010a0b182001501141d0070364103410031404e0f40c5010a5016400d02080c9030f55191501c01c582082c2c02c814201110000715005e00190314203180050001450180d0301441d0b061030201c240c1011341240d000c81000c4866a07414410408803403020101c1c540c29051669800c840100d403521210b04002d4017141d504280441071003101e0050180f01d4592007810b120f0301d0241d01941101581c00301d90361038101101c500d0b50181c0500020140e0060451010000300401c0015941100340385800b007101c100324000b456191446030080400c400c4588a078042c1d07084543e246016078004c48180c0d400310034818082503c3d001072501d900350362507092654440c3c2d224850000100f4402c81d001d4803049610340e18500c0800e410440d881900d000355030500c03a05072070b9400e010408580903c400c01d0800016001c01a9040c954040c040c98440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 458102275 1250 458101025 458101031
    0x70b0f0d020a05070210091802130e04111c050d1103091003060f0902073804170720060c0a0b0406110c070906150e040b010e0901060f0e03030f1c 64
    0xb60b0041850201c00211000104074440c1e402d01ca2110300d04a072307c0346042d0380340c410351a041448014000c4c50500344200c4809142c8000801c0401002145170300d04e8080180c020064840189404c0c0303640e10450005942c2c41c011500b8016000344030f1040072101c440031400a62030109104144014007008407640c104059546802241281030340ba642d4000307140129000d031b100d0b00181044120a1140e44010658011121074201e25090020080a01022a041c441025a29414a111464101d600c07400daa8400080d5030300401c9007843e13402103815a40300c000e008900c04c0106000710340c45500e82040d61b0381c0c0160041030000e080500110780c454414080462000001c050392141e40e00071807000d02450b0000e51092151511a200c1e03100240310005460300034202e103c42c060000c400718030348103001e00e45800050030580d004002c44070340c4d401702401480b00c5603510a401031482c8d00d80c0b00134000051126540355454900003040d1022400380c4803107186003040f00c14891106a842541c0a0ba00c591 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 458103525 1250 458102275 458102287
    0x70c1a070f08070c2f0a0302090c070f0c151e0813050709092a030c0b07082106010306120804060509030f0a0308010501081806010501110114100305070b0f0d020a05 72
    0x9240d17611040c104081020540d83c0280d0100080c0e410394440d51254011040d0300410030150f079541c83c032250082c41c1c104c49203580b100b903410901c40b800c00c1c2d090050700a940c110400552441034103414640f500c2943c0e48c0d20059110428400c941c98114280140020810b0f0040340c000d5074040c5000c62000e2050040b1100d00b90764422150554810382d80580b59000000e4090300d56440100061280d0014881e102031010b04642d19640c030b0807039601501e40c0c071140101d074400422100c0e070220380342d050200c2e51084130540d40140f040d8071440100d030020f0000c0d0170814000340071448051016607440c0d10014140c1041d00303101c41280c6580101441c190716109100c0c6c08011100103104040440340a80d0b2000070941c103000015000080141401e2115201d80c80c180304081c2c80401c4090648000346050096403d2a0702da00b40035050303500b0a151ba0344096030600600b0b0b45004859001c80f4800c50030784555035612820001c1900414091003507410041100b0403084285600518020405040403410300b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 458104775 1250 458103525 458103533
    0x1032004060e1e01060c030c082101080d05041a0304020117010f03060b010f02030712031d070302120607020d0e0102150703140108030c0c01050702040b0306070c1a070f08070c 77
    0x8480707910014412042806200c040003d8083c040c040205048803503140d5407429100604884910b88040c041000c2e01400350304014024040380d4001d0038048164030020000c04440301c02003002c4c03180101c01e21510403524842da001d00103407400c55594010704500010950204942c962000704102e0400040c40034030240c001c40300c13110a001c0c08082c155202c071182907107006c400721107003004c809040c00100c40c440500e03142c0c000b040f1070406034092004112801c403014260040e2140702014401d0a100c5000a404e501000804000305c0b802180c250354507144030310f48c0c182c0303407130702078039640c0050300840031003a8010300030b401c0c1d600a00c2c01881240c0c04c41a81111100d50140e065503a240000e0310f80c3ca602035031340c0c43d100c4040c0c0540100c0002d0b51510702445000c82c0e039091144035840c103008000c2803001c03d5581b40d07070140c2a514400741c20b0390001d00d415071008254414001e01128032800c219074081646d103480c60100d22135440e50b00c4202100005040580c0c2c6254010101b4042250041c0d001c0001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 458106025 1250 458104775 458104781
    0x8010207080c01050105010c0c06050c0705040c050a03060b030f0115020a02030d0f02060603070e0a0b0a09020a050a1706030d0c0501020c010603050d1412070503040c0b070812010b03040b01032004 86
    0x45030140d49155120004480407500313461041c0c1c000e80c10001c50030b000c14041291003020710104c07956403c28550b5501c0c603119903420401107a201c564840c0c500001282401d80110003803a0318140c650381000740d15280e010f41d0b42c160100fa00e5241494181d000140300c00d600c1c40400d06140c190320b004882841030356a001901c4c4c40805006440000d02c01c010740c102580e01044440d401060880141a0250034200c400307100304802800c4080840d101e6402c043c4540b039500403840a840e81034401e42d83e8244200303000d40540d000c1740384034000456011500b100f1040c3c80100358041c1d21700078007408081c4200041142d003004c071030505a4055500300409034160200348503200c000c0d807042024007140c9426100142c43e02e00865158415010100b1480084aa0140c00e0940c8011141002c5859490300d00740030100100607040700096880004071301c020b202000024141030010b0f10808061a03803100c8a04183c2d00042d00c0050104010000600000d10092000c400c1400305485081118521900080c19 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 458107275 1250 458106025 458106037
    0x13080106030804030b0f090c091315051e010303090510210c0e03030f0301170f06070201060e0606092d040204091b0c050703080904090b0906070906020d1202030c04080102 75
    0x51502d0000d420001c00c400407400300da01c09802d0035140154600070380790710f0f101c200d0400b1061107100400000760054100500d04030109411002d84404030340d61280d110001d06c42600e2803c0e000080c008000d04104482580074143e0381e00d603849024035460702051000180d0001005818410403042c03086024414000203d5001d803004000f0a140504503000313000c2280e042021802900100030490402d41d40c0e1045a044aa0f1074680304260120882c0190500c1300b00b03134800c5660f00580707043c4000c0c13643c1500b01d00141d0b2082511140c1d1601d0b00000c0255a201d85801c10740c105041480034030352021303c40604043c41e0755103601104903245001c00035080340e0240d00200d004035a5a0f0503c0c5983e01c0c0400000410507843c2000d40c961034058070340c00c0e6689420b00c401800410700156a04031a01d490b0407e5251940c000642e15031130070107110454950804613040c200141d0200c0f40003d0700303403000a04464a2a094071612101c1c281c2d1010940a50f0004080381c00c0c4000c00c200000742d6001c00d00c02400703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 458108525 1250 458107275 458107283
    0x70602090405090a0b0604060b090d06020d0509061b0301060c0312091e0506060a052b05010203040c080c03070f14011106010f061e050d18061d0114010b09061308010603 74
    0xc1c00c481300c0c40d200b505e140d0040c20860280746401018814002940e0032a401140c0458204030b8090f414540280644118200340091604080900c031060b1400100c803070141d01c291814004c2c84e00b45041418040c0004d10610000488034815800440c0c0160040ba5541c1c1340c2080c04950b203055902c1da1030518030000f181100f1030240413070740d90a1260130301820342c00c1a0115415800d8500d0640004d012103151002c841c01d56040c840382c040d030185060013100195900a0095490f8a41340c10300103500005489484218001d109210115240124940c8103840807038445107085801d00c0203101818450104090510440e00ea020b4800030082018600034040810a014a14103001b00145441c0c882d0f05c0000d00c0541e480c10604100350000159001c040c640100061041d8071621f0040c0301054a520140055142520f04411892008460ba90b082c1405000380440061541c580302c0a0000744184060b14900b4050150289084401884841c2110381d00055540c7c848510500f100c402d640210303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 458109775 1250 458108525 458108533
    0x912060c0c070504060312180e0915070309030f180b180118080601180906020309010c030b0f0a1206020f160204180206120406110c1006050d1707060209040509 70
    0x188520700304501400342109680900c00350380b030b50b030392642c00301000300008080c4100000020b00c0c200521010b14000c0c14501305071021800c0c03505041d5200c0250106402d010440800000c00d400e0090080c0d04000f607160369804a03800c3c003600d0840761048448502400c14510980008a00c590040649009552224a0940260309800140071150703600c0644980f14460081040300d0b4401161540c115206401802c4204581400c601d00410102c0c90003005c1600c04000e1101d054815444024100c0c610b8808102c2c0042c00d40820500c1031030b814902c1e03880212154140070000803420041500c2c2c1c4100800740c1044c2c4d0b944c0e015282c5400c001145019a0515245c0d1425440d060040c80148050340400900182d625000b0030f200340318050300360100c031400d0b40c046020003115600c040081c40d199406940ca518803885560745403e142030204c0d04250411038041542e04c0c101c1e40d40b82000d0b60011401e040900307220582d02064000c2e100079100c42ea8203200b4141c40340c03114095613100380007030381c054 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 458111025 1250 458109775 458109787
    0xc030e0307060203060a080a2f040c03020304050c0a12060902030309062b020712181806030c0509070206070f05250b0a0c0e040905030915040302030f0a02150912060c 73
    0x3000801c2d41b541c4c0078662580c450702510001c44c004141a10000b4018540b600c4003011b080e014602c20340c074483c2110340107460078214a205640c15070143d402280f0400641d00a082c1c81e2040012140560045000c5541a00c6c001d4001a9599111610305840a82030301c1c01c000120f0f00055843d00030607441284c40a065404003452081211800058210761800310b081011f1034480c0d0180521001500c014891070344900f4005011200252000b40442604200e103c81c10100302e40c043e190354030084600100312000410b4034600f0a182a00c642190781c0148081d689121044690000499012041c0b0804010f00c40003100d20345180405002102903d801081162410b0700040c01c0c0202410141850440043c0030700c0d0740001ca40020010803600460111410b09120b42580320b00028954022101c0e40083c01c4200390074080c0080364021020b0710460300303a02821070340380d40c09d406c0d0095019401410f003c243d94800000740010b400d01410385411303400002025482d01005503405400b0300008a21 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 458112275 1250 458111025 458111029
    0x807020a15020c1c1b1a120408070201090803040b070b0c030f011403100f05010f0b040806071815020a05060106170415020f130e01090b06030a0c030e030706020306 72
    0x964005045803a541c00e9040c0d0803000007500c4040c603c1103544101c06044c042082d0031404807050301c1540d00401e03060340003a0341034014924134917a03100e19240801c0310b0359400141c1043c10161148983c0f0303d07006040742d603901c0c0d5840d04503610a92089052224019004c1010134081000d0400340254480d5166250310718140b4070245480203026002c10b520400820890701c01d116085c0f8112407254000311403540b440e0300003074288046510b1940303503030780b910909d0100f0613810b0f04246e04940c02480500c0f041078486406440c280300700d014095860b4020300210388030500c04c816400307664000b0b00c4545c4849494141c11010000080710010050740308840250a104041c0401401000300b8200007900d02540245a04000b0780100b01802d1041d00c041c20b2070352030740e0350740441c1c070218a9a5045035641e00c000c40c4000c2408458011001d41501c2100040f410b1162845002d1341000001d02c02402d540d610700703a1074041c00240018500f00b58495420588109080003d001000e01c01c410142e101c2c98891f00b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 458113525 1250 458112275 458112289
    0xc1f0b01020c061c0509030c030d0b10020106080304060c06110d0f0609050603101814061009110708130510051b07030317040303140f090c100504051c020d080702 71
    0xb01d89882818104004116504441c049034050a0030510108095550115550542c0510f1100050f1404001641e030724080107a403081c1ca0400e01203c0d880c0c0040b40c040012070881d61580118103285e44108000d004450181354940e6286200d0400071619080c200680c1c0c846400c505134010041d0340715416804440111f00609003d00005030080140f450f0420001e50365503121403200075a40d5858680715281c404a08006c802c0b01c1e00030f44008a514803050740c031940c0310400c8820000811070440003246480c180e00401d80c2c40802c2c81442d0303080142c9502d40b91003e9000444111000d42c908000040580703580f042c0035911982070303e4407922201115541c03004c805481e00c0c050350541012106100180c0c02180c1c0c03207412520300e00a00c81a94030f41c07800381c000b40760361032010b81d0300c0e0708150805c10b00c0030090140038880c40860301a920b5140c04041803100b100c07810407401c0c02081060205100501f4040360460f41c000400103e03407044560750b0080b0b03440e40c01c0603005030369020700020a4025421302c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 458114775 1250 458113525 458113543
    0xa050a0b160c020312070f060903080103231c020115230f18060d0605040b06120d0905090a0204090608010204172113180c080603030702010c06020c1f0b0102 69
    0x8100002c0b41d0500354002903d8100d1982a10286000411803134103002c510a5580e002c1580070300c00b00071960311424083c1c1245001d10084607041c9417283c041075175207034000b080e0200c1440a0000c0c80300030508100301002035800da0001d003c56584801070090814851203802c000c1119910030809407402d0010901080e6019400342d00801192030f1240d400d44078698000000b5000101e54070a94940b0700024411007c02400603102905003414003080c440d01e5a001401140101c800441c40720025500d1603c0740e00c0c00b04031601068414404000d5400e18010065200200c3c2c5001460700362a10301a1045402a802c40d43c620f079800715041c0403070425200315011800d00d410051901c1c1c246107290544040310040000201c034804248412a110780b0210b110150401c1000c0211462540307558000814588200c08001400d203400304e582801d0100480d450980c041e9a508609c0c046522881e01940c00300c0d034116800d100c0e49460300364520300380b00c0c0010300c100304a40125029818000081ca050001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 458116025 1250 458114775 458114777
    0x20f0a080d020a1b0c0609050a03050c010e030102130308040306060f24031116110f030d0c1703100e0108011e150302040f020d0f0c0f0c050a050a0b16 66
    0x210880808140ea20342a41c0c0e0a10600c6009030355550260412611014031041c00b00442da4500e10704410000403801d502c050300c0d903a607640d2146035500c0040110b80611840003421507080b0b184172488552060a001d84a440080d0002d45010002901400403805651094130211030204062080000c58000c1c41c00900307140742d10440c0703d410040240341a540c2600800c4542e40101aa0380755980a078002c100c000644680154a81c041c400100c0d2210008600c21502e005052409148174030340452021040324000d801011460300600081e5020b100b80041600c1c201003c40030b0311180810b0200071481069800a019160740c41c04400f164018010b0708140b07116410494402d504ac11010301108400703200100c042008901c440200c6400d040d56000a50000d0920a043c907104075581c0041000001c0e0007001c0051281d010200411100e58560323883c0020403014080c0c59440c80348980240c0702d030040c802c0d01d19801d11991041d160251042c1e0481701c0441c40c46c01c0041500200c1500d0f84100c04c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 458117275 1250 458116025 458116033
    0x30601080c090a090209010e0a110315120708031b0102040b04080a03080a06080307060504060e0f0c2704020402091c050607090e1b030907121104180503041503020c03031303020f 78
    0x10356000070400e440500800d102023020f400020b5481d03406030080000100502d80d540c3c4d99013040c076550f01d03000114140c0f0034014071401440d016107032000034100c011204110f0207141029400c510100b9440c0b0070b80d84010140d0340034000814501c054000034001001400000c02015496103005451103c004000343c00c0309250081c01c005042011045480b029809000000d907981c8514107a4000c0180540061492082c50b82c8a01c099800241b03c50f110b0404580c902c541e0102001c40400c400304601c1078800d41c5400902007030040c02c1c607030094000c00400030070a40441501000c3c640e5000c0300725000307581b103901000602c984d40703801c00041c00240c8100c0c410400186460f000070410760708600c1c100c225004001001544d21501803103c00003414460802040051070303414085040c5030644500c034880c1c1d240c00c45d12041d4a80040491455690100c0503605180c0380c10201901800030b80759042c03c0c16001c005001c4d01400602c001c511031500c15400030a030440710f050003464160141c0c0745c0062580 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 458118525 1250 458117275 458117291
    0xd0203060135190c080a030c030206090d120207030509150904060e0606091e120a140a02100e01050d0f0f380f03010e0708060a090c0303030515030601080c090a 70
    0x1c0420b0010090f04080c840600d850780c6482c00c4105640240c0c08115107000d5010913404040d8443c100d0b07042135002ea0700311a255140c510714a070f01c0386032030304510010400d446985422901c140e0094003520b4001d0401c241003900210101d8005607881120b10281c00e400681c1140600e0540b00d44405000d0a680300c030a0b40c944a00810418440c07a18180e1003258040807181104000e54245a00c0303960181c841102801000555503540100c42c2040b91455181050300111410006240d42d815070000c1450400d160050010395800c00d8013001d0504200302082060b017540030701c2c05000511443c40d00002884d840703010350721b4102c0e00800800c100d0784030150400002d5030300450541038441403074045040a00300c038100091860f400c0d03d4049425500300400c81c02c00a802180c081d0485940b0750540c2e0b265960707001a2800c41e82119402411412110300920210344170f43c0c8401c1c1e00c01c18000d200782030402c0142c0001c1ca4603a09911101095020300034582441c213000c01a030381c11000001c01844286 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 458119775 1250 458118525 458118629
    0x15020d0807080c090a030507181409070e0406140c09130618020d0905150105010807090501021e01090c09020d1a0a03170708130509010b0c060a0b0d02030601 69
    0x1010f0841000402e004c1401310240d0b4801a00e0b200455110003194015940e50302c10b0341d05d00807540491880b00b4544801049510452640c01c1d10414001001d4500300e07041014403465a00e0280c01a69000d650729205610035604a800d40c2c00340d0500c01c07500b5105d01e8076034100840b000d0180c12078200746007441010044560061141134501804040141e11a412607030f00000400a0050103000341c416620740301d07500c032150003209058803006e0781d458569036100c0000b036803400f486206142c0181c0c070003521050180c0214030000c28660810001040f00365094030340003100440d98101c2d80c0f00310340c00200030103103861500c03880d64240e03170320780031001c4d942e11450004085116520000d0490604405802406540f00c4101c584440c2e00c0440c0f01e88035000fa030402a20341c103080c0911030040c01c180c03001040d00341480d41503418101040006003076503580c1c0030a8202422158840035044100c4502c50070050f503041c0a114003802a1412100c0100000e65000c1c00c05280207030080b00354000681e20b4a400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 458121025 1250 458119775 458119787
    0x9130204111918060f021c0c39030f02010e360106030b060708130308030a0926090d0201021009030210050c0702100305060a09060305010c0f0201020a021e0a0c15020d0807 75
    0x401c10343c0e15468103d07c0c5020003134504001020000b01420b0103414682004030046aa0120a5030340c916525031303201201a40c49001d070b60702c0c0402b07800c40c2101144140107611401444c414190054210327400345210704001403a0f262442c00002500300106c2d41030000c5125a84040d0052101d0315041c0044034903440803076482e10858a016010507800030f601c41c520003101d2444001154014111a41c034640b400c5103800800f81640d040702c504958800c4040710126290302c002042c00188901c1e40340c58100000c1000e0a00c0c040c10880c1540108000700b2145400c612881c8070b4280250041c05460002043d508100d0398010000764415109102900258a51403d01035694080e81400542c948411000072001400c07a4802040e1f581040004070410106400050002c0103c2c0c5643c0e8041801d2401a0701b41c0c050740d41090010b9021850301c0314507007000414041c4131102401610f4441c800d54856131407a1859410031040000301480c91140c40354100045101000e45281107405802d00704030050030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 458122275 1250 458121025 458121043
    0x90703051302011d0307171506010512130b090c030601050321030a02040f060e03010b01030519020a0e0a090603140313092706150509130204111918060f02 68
    0x401451142103131520103451503000d01c03502e00904880d140d60f985d4071003003543d2004402c080914025500c164030340d41405240c06029150585405092a00c0b0041c030700001c8030001c00d01c098802421503a840400d940ba002e2034044c0c001c040203001603510b010141031400c0c1e0f06074400d034042d61100c112580c400c10207a010500860341422900c1d52515030391590000b03801242c00c01c0c04c10400174440000d2503500040c4440417581c0540090000049900040d811204112560039101100143c6040e212003a07500800794000d042c1840c034444210700c0007141495810f0b4100040d216035030350040c4180460703001605070812a01008514003c080c03405018502080d00c00ca10b042511001c1d413501c44c2c84032818101500c80c21801d200310101c85800c04102030011181003081c142c4403214080b40c1414402c0c140c611a030303082c1d4044003445400d60700307000050034a4080301000352400d0000c2f42d072800c850003000031080250769401541503940c5210402c03400042d4010f20901c420b0342c003200f100d2900810700f460 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 458123525 1250 458122275 458122277
    0x6090605010519150e010c051002070b0708100920040f03020103060b0f220504090c061103091e0d080409060311010807020d0c03091706090f030f16110909010b09070305130201 77
    0x40500030300c00140d403c2e00c501e48000300107008027520b2801b4600650301405440d07002c1c60481da11502ca420080d160144140c41001208584100500c1030440d690844640c5500300781c010351040068100b5504650400e400016084113504000c00c203541e414003501001d4020464610b02d00740e800110003c1600c11191200082825180d00f9480841c0040d00310008060190082c0410000c61900d1403444c08940181804100703ca04a070250300800400d54400e80000381480040100320180d907140d00c0d00c840090340d80485c4400c000c80c0011405009407001304044c400c0400e1080c158a4620388090306a401d9504001d4240100103481d5030005410148200e103041850500d010f030300381126800f2031608441c1c41d50150301c0c2c41550701c0790700142c2e0522400c00c803010395943c82522220644c81e403040c0b0244c503003d210b048c040070138802081d09101070128420540704c03030304000d044003181407107104907542e5080340d540301401d40d02c03401e00c14000c40c0c3c0701350545004c0106181c4010140540a110b14001e8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 458124775 1250 458123525 458123537
    0x50f12130b030f011502071d0a05090f122206120f021303020d020d061a0f060a0f080a0f06030606031401050105091b070b0c07210518010203070609060501051915 71
    0x201d45c500910000010f0280b4841003808900d1440141c0201f10054070808003403490540040c091102c0821500c2d082c4901c0009804d190300c6003201760020707400c60503c00d031114001600c0c49604550b1020714000801094a4031110b550092151100f101c1013901050510b50040203074024000f41543d4040c26290304071898011701442c0c0c008154000c05c1404010300140ca401d036525459a2505040500007030210b40e500f0140494001303115040c0510192040410054a00702800341e000d51034180e8441001840010842e20701961071042d555242e0050300d940782c1d181001e1060115009117400c240c49000002e100c00e501d40b030081803003050000d0411091302c2e909640028031350301c0c100031203945030b400c0300403405c0324100007001900e41d43c00504100c404508c3c00080c00e140d82d40e070603915441c04d4069154541005113103004c4012a040c86504241180008c10550740001e50510581380b02901400700020313950f04120074015400d0680100d0b4100b548411001c0203d0f015507104505682213601e014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 458126025 1250 458124775 458124809
    0x30a030804080d050f0604060801230c0715140717010608060f03070e060f0d030f140c010c0f02010614031e0102090306041b05090112030c050f12130b030f01 69
    0x3042d18061008842002c42c02c110500c0590300f101442c1d14011501154108122a590103500e4221282401a0381c48608000b844204819003c10425445940300c0107507842d0a60507664401c0c0100028403c50105a03100e40051081c41c030303840345a90007440e900f0f04000801c5001070484044c02c0500c00d0340c0820681c240044c0458a5010002450031070103400c447c2180d0301ea00124680900444e0b219000308080042e112080c94202140000140c040d2154100804418000c8403031425004c1081617400e010042c03903d1460003441000103078400f41d45ca40460465580c40242512400d611221001c01a8030380b0203826070300031903c84c44058103840c040720300c2c003204160140a4010300303d000c2d03414010503081105000004807102c94961a00c0464007400b6155800c200c0c5d034080a0060203081c41c4401d2407200081d011709680441349001c0d0701141c00d88110b9600c0c0a140c007203105580c900e03118020030491424600314518402070404004198198034200c840141c580b6814490700b06200c0314003500f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 458127275 1250 458126025 458126033
    0x2a0603040503120c1b1c0503040c1401021c020d080f01060215060d06050c04061404321012060b09010806010c110a03080306131a04090215030f07120b030a030804 71
    0xc80394140a9190b840d400e01c003890b01003d4940c80740030150f204180c4c0c9001b0120b80c1c1072291084a2203203901161900074182012041e84615560741d03040d0303056100b2000d1005443c40462040e0145c04490380c024000d040c203800c0020030321880903000da5044454180188059900418400140921400194080c2c0d4a000000b000000d03030540190105180000b40400322101400500982e260341d2038800441c0d14444103441103210b10f1203440d50b075403140030005010800754503082c102c0e400d208640308150314142000421402c40481d404000c200041c0c550302104000b801100002e060321400c40d030038042c040c00080d1a40310014a01410814210750110802081c0c0c9e123404008200540343c03580e80c0380c4074034061010740d0003500e00c45c0c4a5900056100d401008a018402012125803008402d08101600344006491140c10480c1d011240042c43c5462503041c502440c4140103030f418100c0d1904101e50060240c46d58074011103015420440c640c81141c45c0001c4102c00d082e8140340100141c0e4403410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 458128525 1250 458127275 458127277
    0x131a0d020306070e06090414060a2102010f03020c0d02030918090c060a1e0f1106040c050111030d2c120405150f0307110f0c0d0b060d052a0603040503120c 68
    0x301d12a401031401e21740404c5400d004103198443c10007507072010342b80c0e5201d10000354441000840b43c1a6413040c4080c0c500107503c0b40c4170010642d03e40341805420401e010500074200001d495101e80181d0020500031124902200c0403078054a07560038088503420484202d030b4403001f03400c540c203003c0c90f00000c014100c035200d0b0100e84c680030607070820340c001b180300c0c250b00811480d2624250740c0000e524035030319050f401000c1600c900481d403007221825094a414019038100e245010f132400c190000b4030144428645c14010072030038045824510880c04140e607180c0d5a060101c5042c6041540a480c28030010b50b41e4900301c5050303a80840d00080301408441003280c0d00d2007410704550302100044248070425420901030074620a8020503103144035800034004d83c2d80d01c1e03654100c0c3d80c48041a1044004030f8800725426030025400703040c5580500058954914146c058580c4a030790f60b841d811500c81180541814540d920f100700c0c0c9aa14600f080e84416a9902490b00020b0714106888003103541014400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 458129775 1250 458128525 458128537
    0x501050408060a2307020a03090906060509010c23030301170610090207020316031407090507121d0a031d01020c0f0105130519030605091216050c131a0d020306070e06 73
    0xc48100c07064135105c00029210440e01400300c011406104c1d02090401039400b550b01a980d05035195810300041c40011500c980d141c200960b4041068001c40c81c0c4d491050100c100030511038402181e41e5494102c100d42c158102c4c8284800d0b40c0c004205005255201e02c14200443c0c81d40d00b805600c4141500000742800ca042e5525180e608040100008200c0095108200903201c4000d890000e5521b00012042d280100e030802c000075004284918080d95543c016008446500e200140c0052550603162401c2480c150070350120b5606504040c114010040d1804e03103400038405820b101e02c1281c04141108540e0b03902d1414810f002c910301c0e802c6203030140c45d1001414004c0c001c5c4010f1400a2843c900d54802e80410f0f03500a051000144078184d0000e00c5803c00c00301034407d075117095010032140e0308120300e020040f102c1f400740c0c2c10141142d98868004040f000802d0ae00014107441200d0300e111039a080a030468040c0800c503078079030096900424039603441589418000401040e52002904a01c84c2c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 458131025 1250 458129775 458129831
    0x303010e0a02161a0f1012030201020705030406050405100201020c0304030f0f0506041b0f031509170304050705010e0f011403070504121b0b0c0a030f03020702030a05010b0a0501050408060a 83
    0x1aa03180c005006500052090002081562803002e844014040149081c01c440502200f00350006c00c1050072036686660008601a200050400e13030140e942ca825503005611500001d0360100703040c81a890708610026440310580002c510741822010304c0c0342c0328011840064801c1c1003008c0010180100312070754012541e8070400b0b8800500e407900c0e01040b0442e071000a5024400e0352500032841d003850108030380540360404403200a021105052a01030054000100d40d200b003880140c091402e0034038095401071303102d8406400458201000140340c041c01b000054030941917141500c800d0398100d1009040074042072040c40d9299a203040c182c030729208944c08100e140e20802e10300020321510150741401d81d50740b020000780302e42e82e0746079144047c0a0101081902e0b00020081c80019000f01c0f01c204040c807841c00c0240c100300e07442e00003d040444c601410b1b1210b0f5141c4000001d6032808003210409080b09003411400e05013807040007030b501e240040c00324081d195501407102c011003007442d100b07a50340b450b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 458132275 1250 458131025 458131057
    0xf1005190b0a032403110a03050c040c0c0b181c20013b06010e0c03040516080a050f0609100b03010b1f020105060f0108060f01092d12050303010e0a02 66
    0xe000401c0407a54854172098408540c41340c01c140303941c074080d40034108503500b000003010781c0ca03e04010030000300105488601800a04510300d0002040e202072603100342e901aa400c910344000c2e83d0103034101401c400c1907001c000c0b0341140c61441c6d940c0150940c14501d030748031860340345500704e40c0140d8010b0407151110007042c2d20b2040f411000d0510600d90340c0785071143c0c8203054503580000d2000c0d9600c0c4000c0c02605601c070b420314006045815004051076010703001c0c00032500546010303c20340b00c2c40c50054008401c140c000c00360745428084100850030300742d42c0302c60040c0b420f460905040d6817680659800c65146503200c08103e54103503425089020340e800024a081050031944050344910b100041c2080b000d5424940022070074600030705910384452040c1c5918000355981c1c3c0c100151544101d2415060000009001c14503018410300c01e140a44840035113803094120100e5008808060fa00c52510000c5e829400c100080380401501d04448107412000c6280e21400c01c030368088d0080303d444400c1015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 458133525 1250 458132275 458132321
    0xb07090801050a02130b0901080402120309040c0c14070f050111011415010801120f0b040302031e0a031116080a050c0d0306050f0f031507030f02030f1005190b0a03 72
    0x10256008040d21118441708900e40c0d42c5d0790b0000b042501800302c0083c0410f5449000602505056042454040480c0c042e245003010640006e0100ca41c000380000004d50600518000c02c2000108006011a00001444090b140951001c05e1403400c0c06140e04000038071000b206070100035002240744c03400280400d06580303000100034014400100f00c440c00580c50324000551610041740f2030070420740040d1501c0c00000181c1b20f03040c0c012400717882181107120801038020040001c01a1082c442c2c141c4a0b060f5072140c10620082c04d0707420041780030001507000c0000340100310641509005003688200c0680d120000c031a0262180c1c0119040300e2007900400da200880d07030b0790540c0314006550003240c2034060b803181003061000780e907075202d14641c01d548442c52629292002c4025164031801d18900422041400f4030802e090303030425500e1007101e05605007400404080640c441e005404265080e14402512240a100c2050f41e4854051700400000e42e2103002882a048503c0b60b0620f0050b07080124 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 458134775 1250 458133525 458133541
    0x903070e040f020306220f11090f0415060e04020d14060702031c0216020f0f0622060203161e0f1b060207050a050112020c06040b070e0406120b0709080105 68
    0x1000b00360040f031003030292500060075403810350001482001c0c4082d00c90070001056441d030f81d0b43d1109502c213440d9509001e006210300d80e03800c900244181c840159000f0b070340c2064948600014400141c0c0d00301d046c20440140721002c1884800c0b58090b0b0126125039110b511401d144184402d0110003038081c3c01120200828203400000801148099800180031400400001c004a0240000601d45106104400f81c003600e0710410f070910103880104040080701c40d400015400b548000d20100084d504840304103800782e94118481c2c02040c460015600e040709182203003182086000f4014060041c3e14071031420506450106604c0940c8442e110080410b54145400180907900c040381d01e60401030008900984086080c9048440c0a042c0840b0b060400005480303103148800b4500e4900c2c0d003889460f46c0702c1d90811204ac0a50b010350503440d018101101d00400040380e80d880a8011346c10301c841000351172041c40d1107d83d081d4210380700c1c035100e48580d40200d803240d071107a0004002c1c0d801c15040c01100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 458136025 1250 458134775 458134793
    0x7050319081e072a05010c0f051e011a0901140d150504031116060906050901021f050618040503030109051906080f161a0708160308010504180b0a020903070e04 70
    0x4c480e003040913009600320030440351140305038081c680c0058a00d40781d07480001d28910305920a64410000d5070031030b180c0c009401c55103030702c405210fa03000c2e074443da10f02d581c99a284814514a08056584c13503010760624501448001041030303018042c0b20041400c0090044c00300d1b104280c1319120700e052103641018203009000c40d2495110000c20b01480b441300c02500c010302d02c80002ca0b842c0303032100c425a0b0b203805820354035500f0400607076055000b0095142d602610030300000030300030b041180015042c2403120910841184c411588401c0c02c03190320601c40425400030603281141c16044000c030301c60761001c0c100c411080541c440c4450250070300b000401c0310080400d503130030350740140402c440098030312024100f00c4180920400c0c041c45070140042007100d4158004042070350140a00c1c524102411181041c8443d8820041d000103401c4001488149801d0107018045025600c85407540320701c540703d099100c4005840741c1c850303907400035112007a51028040980107041d81d12211040c4c0c030f400d04040300c407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 458137275 1250 458136025 458136053
    0x60d0c030c061206050301020307020a03030b04150b03010303080903070c122d050615090a0e030405030f0c010e180a0c090b0703050d1b08040f030215090f07050319081e07 75
    0x1444d00f07225001c1001d080c144245d0303218a4031607009019070301c0c0300e403401d40c0246040020b2503040380d291000040400040303100c0c14001e0600e030001554a615604000344845400707001100507420411208020441c002440015120342c1440720b1380445191504402c0c100c1a4420318480800c80f107030041c604100016400010f40c010405d41d015556040c40b000c165508914003035a010382150007003048000290701c60040400c0c5c0c1c0003240e1800d80c0f81e0000a00e003041c0c40e00100569031200f000c1c41c1055030f02041d00d0b5070821064440c603411680039110211410340040c16181e07050340d6030324064849486110440c0007000200040c03540e40e0700314140203000364800702480a0700b03810120014500e41005900702940842582c031141d183e204d55403184840c154006050302148200d14100c107402c18071340102801030981e20000c1c00720303051606445090582c582c0c0001c0c407070381210f02100019280e40c090340c613020f030303200c131a0540c3c3c2d81c0700100b409449010015942e081010110b00482044000c41070060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 458138525 1250 458137275 458137307
    0x1e05070c05010b1c060b0402040b0c0601060e030d2a020a06121409060f0a02070605010e060316080601050105090307030606091e0207020105040b070204090209071809060509060d0c030c06 82
    0x700052000c002c0c081011403841034042544c183c4508840800e0f000e50280d00320032001030000d0f10701541c4050410907500f00401c000f1780fa4010700300401216801c200013003103141e0b003540504441401e000014280300d41c203170503024680300b030740d009440b440c1d4242030310342d1146900400c88100796841e0100100512001c0108005886c5854035840d500c840040c1424814440d090003000b095942c1c1c4200c0c41041c1020300586015a001d02080000600f42c0c01498064841c511048200385402000c052a06060b800481c0701001e5201003030203d0b682c0072800074151003007800c000b0303a51516480441e18191160380064002c0d4502800031400d0f104076000030040500001358a0042c0310280c20080c01c07171150311f90090100c2e0041108002e10711141c005010011300040000030144950b07001328001c8a01100c0400c0020036040200141f0710f101c88100000d0301244e20200308a0341440c2c04100e607214040d220901c07407180f142e4648200700310ac00201e0301460b40314040c820700e20340c0c82401a0112540c0c0b60b09030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 458139775 1250 458138525 458138531
    0x7110609010c1409060706020703170f100504050603070905070908010f0b010e19030b0408160309080f0a17070602130e0106200a0308220b04050c040b131e05070c0501 73
    0x481c4200b0301c20540b40c10700384c020f02c0d0515051096403544020360010f20200c05100004452404050704071004601c01c0c01c0ea410071a4051414443d020590069608a0341c419880d00e020301c0078540700000c415040c0d410803100010140c40e28070041e943e18000d039200700310327642c00c20b01d1011864000340c0003081a0341017a201d04049810784001c005046511511605201681250030404a5428520a47c00c41d002c2c4a0b41443c011102c40c501c260103030301020541c04640742c6e040401858408001c0201c5003500032003d05209802c41c0e84100028122031002c5205200109900d0180072042d411a0303c0d5200b0f11007841350300c40d80c9134040c42c0c084009116010110703006c180a40300c01c03c0d450340301091031030381d40c0c000d0000895640e0b81038501038400790080002040d101452900850401c108524041c011811030b0303c2440c0a00d0842e140400ac0c00d50b560043d802e00c40e01000c5500d0b405513900e8403445500c000314404404900c80f80c1c40c861a00d40c0c0c0100a4117140030300156980040b5150304460003a0024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 458141025 1250 458139775 458139797
    0xa090f0501020d0f030f1104030515071e0309060209031501031b0b0a03090c17010f0f09120c05280210020c03030d0c0e03161e0b0706020307110609010c 67
    0x41e6200c1062030b4030703e030208a481400b5100d5500c02e900040da0700d039007035900290844002c81071840681058200315150f030b02c03c0240e40f000c07206070201e041d440387c040d01e0112490f40c02c4819051b5030010381e0101c1030070305440f42854000c12606030181d8032205c070090121118144035800c4001b03000420b01c8207892805071220046904c40c80394401e07100b40c3d03004d0380420f8a001d82c200c604400420b00614203451010074240301190118801501055061080001003660207036000040e0444149110b210011450080180700107400a0000e042008550804000201440c01e181c3e0410001c182001c03070810b0b14a01541102c1c0c02d4803249107001d800bc0d1444401c00401800a0380d9807020301c1500b07a07059009001071203001c40c654009001070811454031228104203000403d1a00780d4501102180d8840000103200354800310800c03070002c2d05201d05e80d5022034689441c26229202d1a04e0140070300d0740000008202c0350107440b10f5220000080b048420314900070f00c0c081c2c024640e00040900080c2c0b00c04103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 458142275 1250 458141025 458141027
    0x3030f0901020306100e06160302060711070311040c18080d1101410a0e120304110f180421090608191103131529060d020a090f0501 58
    0x2c1d40c0c070030b0b0f00141c400e03105c04d103c84101740c411595890a656006408200e4680610211030a40c0449071085d0003c084a003804c0c3c4001c3c080c2002030392059042c2d4841c29041000c56081c40c101502c008003520002135040b0001c0c2c044424140d110b03621141346022000001d01c1d95000610b0851460382951202e40c44495103044500f0386200c2c000b01d00144402c080d034261040c1d000c0c3c0b50344200b0640d9410b10390344074402d0742d400510000200d802624550f0741e8101034801c070009000c0c0904000300150300b40e1452030503a4803200c4002c46000100d001c0c2201e2801c88400303859090056030b074100950103941d02e5160518084503000244d04080a2180f240c032005c4407036500034801c3c0000c0e00d6203600d4510040c1e40328040c0808003010398074040125038a80c0000c00c0c42e44c810400a500448151009070b5104240303080055401c0040e0402c03400807490482038105c8000b0840034080300302200042c20701c603902c500740012440d0154903503c0801d42d1002490114254110b071b6404120b4407405104454076683d000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 458143525 1250 458142275 458142277
    0x4060215010b1b25051008091b2e0e0f011403040203160e07091d01050d150216020f030705100f0207150c0312060810020a0210090503030f090102 64
    0x451003512540501c030764500c80d01124068440c50011004860911440100c0d20349141c9021506064003400713050140101d040040c80310102402500303151544d400c0c5140c03c150f61706002c00d0440c42c0e02100f2402c1e0180340e0f4807054507126940d0380207481111144440c1c00418080d0040e02d103040442e19420401c0101e007410842c0c0044580d05071036070304032000302e1400b4440310f1b4070082080340d15004055012113151050002d131030140212190014480c50040300203403100125410100c0c04034103080306410400208078101d81900c3d42600c18901c03031802441c0c80344a04560120b44102c103400400c1800d00c0107240405680090300031100c0040307420000050585801c0c440c00b400e600721040d8811140814000c0c51200000c45071807045408141c0e4583c5074000010504001340009174120201200f45540004030000344c0f8098181009070500e400071036640da080101c08221015008126444d0150080c0100740308540000780a010401103031409a441c2d51040365131005c03000c001c0c03000c01c001c1e0f04144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 458144775 1250 458143525 458143529
    0x5030604031706010314010b0703050405040608010203093703171f060503090a110607240606020610090f0e07090905150c04030b1503030c0a0b0711070b0d0908040305030406021501 79
    0x11010f4699081203900c1c26142d00c4031006908bc00810480010243c0702c03413046000500f03000000507140e0400b40401400c002544841c464201040485031245280800c000c62110000800340e0700c5411081c6400d5411001188244400c09032901c100044e19401c4074101418400345480c0e00710a0381c5407032098820340015101160103070311040300f02e800950405960341c2000001000c2c14244420303903651044940c47c10203400b9038040141d201c02483c1c0c0031400b621001d0640d0340050819481c00820201e004c80c01d034414500039a44035071101c074030800c4c0782d80898030300804007044c0c2d200c83e6294048031024000d44481100e032480f070148142c0e100d400300b0440354002e481032240e10f443d05240d511210000d4a01800000307064503207145942c0c0c01c0c0e804000500320201d2490146c0501002030402c042e40c076030000c00000621140950303006000c44086209010b42e042c1950154a9680d080035560040550100041900000150102c284080000500102d0704240e080791500b400e04410350036012002c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 458146025 1250 458144775 458144801
    0xc192d0c03090803040f05090402010c41060a0908090a1d0c09091617040b161d040905010e0a0c0f06030b0d0b1302040f0204061101091119050306040317060103 70
    0x80405120900c1c004950a030402e00516145040b4203068640e605024100d01210740760001241d014075250001484dd81c583d41c0d8602d000a1110041207000d40d2a5803009081040c510780d5003000b0010028050241d415185c0c0140112101c55150202ea40e4003503880c8500301e0119080400003190100441e0803500011070181003540d158490b01e5281944c1010302c3c0314201801000b00300300680b000005140b610641c000c0c8c4200032a4204030b8228602c21800b841100d080200410042100000c0c0355200f91000100749d900003403c41072030038070714010094080d180e000390260501c100c050080e0160350006440d0306103440c0319415902c607800c0c3c0469035080312480c0c00c410300455540c0031407101005aa403041c002c085144624100f41e00007421141040140080e05070302050070301926602290a9000c0c007008002007111032140d03120340c0c00425403000ca2070312490194244800e503c24100c04030b0b000b080c002d0111000c0c0c0c202468043e0240103191110314000425000040240d882401404815802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 458147275 1250 458146025 458146049
    0x30f0c0e041812080703061e09140603280507030b09060708150105032e080111040f0b1b010c0e1219060b031608030904050c192d0c0309080304 63
    0x1008005465442c3c3c010480814140d43d000c0016001180b510300210119008c10400b00032818268007004031080c60481d90701014204040207080c2d00d00189031886a0721150404502540904c203800181c3d0324080000d0083c050800d00100b04006045402d000380724a0060360030965409200b190b041d10700b101c065400c20f0b90340031801c030701d540104000c54012402064003402f103c43c806d10002d1940e52483c1d03111480c1d40d084030820101c13a0a02c80c490362010104042407400d4517191b81001c8000d01401500a080380000c1c50025000c0011240e18840c600c101c000e02a440d0054030240110306070b4540140510101c0362540c0c0d81c5070323010941d4407600c40300003c003004400711601d810004120704030100d5050300c00c02801c070605485480b4044020418240119510303010704c0c0901040d11400341202c0c000305024801180c80c03140201ba4007502940d02c3c03030300038120703003416681b441e9070b003024003020302028000340c5030032500c40c5d005038413080d0300d4003d8031000c0c4c64070b07541c0f800c1c039649210b0341c400e042407059 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 458148525 1250 458147275 458147303
    0x9030321180a020f0f10110f0f03030c090d05160302040c09030812152d010302030405100906020f070f0b06010e011d1302030f09010c021504060c030f0c0e0418 70
    0x84c19820740c112a0701c028141058099241d4041440071200244160110380403079510b07400c12100300100f020b48550603028011a02920b03104690780e010140800005c0400030480080070348a100c42070401a0300300003210102c10f540e80e03010a4860300340c00142d000d2410100c003c0f5084d805150194100d03507121104901d0824400340540c0c034018003510981071507d00e40d02c81c509581d100900301d0076a0b0301d42c110010b034603104001c01041201610144038103140c010b00c00c20001c5080410300c01607400c8520070200b800c80d617500e05540240b0808414105140c404189801030004032500500014400d8031014140d4507030000544501100d440080e002860160b071017906800221040c0c000e0000c090800700010071740f0354801041c0d8000f103604003c1d042803001048010107090107100602c950900207021250018000c04d41e6200c001480a0441500c1d40008441c2c82e10a0303001c286e05605e1040100b04140c42c800006008142030038009119038103041042010072462600480d840c3e50205090031012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 458149775 1250 458148525 458148529
    0xb03011404091e050a021e130c05031f0e07090e0708060a05060f040e070e03070f03050618031902031305010305190c14040801061802130501050d0209030321180a02 72
    0x6144140c00701d80c103002c0c05c0c2e040001a111030203051800300301c080350110100c2405090141707841d280e1a10392152818a20786240d2079810808403500000c0128007107224100c0303810044c1504055500040e5110740003010061401d90140c0e441c42507401c031350141c0c2680c0d10365010485070200c2c1500c0b4550f01c80c44144080090745855001009281c843c005240d090a41c1c8070f4401c200054100c842002003141c4400003000e078038090041c900506403c080c11a0300e503045403169543d942004080c103103c07001c1401c003030245010800c1505c9889104540e140390205150303100944980040c803425081d50385100f00400e00f136001e4003c144c490b405029150320000c0386002a5009040e0820301c0c0320070300c081345401c03840c803000301802400030341858000815080d1900c1000364031000518031000b06c0341c1c414451080d0320300c0e142c0c1c1d1030000c840091803c00d4031b41c0d0a4442c507074024480ca803442036061000040c80301c40c22410700c03440f955201615015110a50740d0704281c429000c2001030880985d00100e0b8000014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 458151025 1250 458149775 458149823
    0xb0f07080f10090c0207090234050c0402070c051c06060f05010c0b06010e0d06090317070807030902010909020a110714280902040b0702120c011d0d050105010b0301140409 75
    0xc1845841201c051b203507200501022a4440402800919a5008030300b112104032a111a08071003081c0c4801c00a84040d15220386403009110964400ca40010b4420700b03010017000540b0240000420f8051034140c0c078410041c840554100480f03209003071400014004000020310b8040740c6042e15400c62038401507544000c40382c0b000f00500d041c442c1c2001c00b030304607071500104400502d02ca0ba80020304101c150801a0020680b03616150111043c4420000d91507488054290040038a09000c10181c0d480d01c0141c420b100c6580108200300d01c04203190740490392100b01012a03000d00400c1d10046130700e61010b00720350900c40420315040841c6032248060740360310700d581b03544403001640d03915520b640303495400050307a005a1204d5009000801c6407030544c54154000d1400c18406801081d6808140c00061b040c0314130b00c00c584101e01049014440962a14908248580c2c0e0140c000c00c10b940e110420420345420a00403540024a50039010015040500c110b42100d03410101842c1d00d2400410100b4003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 458152275 1250 458151025 458151041
    0x14040c0315030f0c1203230702060403200301020d0c20061b04080a0605160905030d0c051504050a05070902180d020d0b04050c040b04151203020a0b0f07080f1009 71
    0x19000b0135840018001e03141e015190f405a22035900c54407000d65040040c000d03191418090a0480c10400641005a0390401190f048a91000340104030b003500300c0c0c242080459800500390154000103500c1d07030f10b030419480300c80c03d04110f4840349000d060704400c0808c8100c421a0380003407a40030f0b40200300703184103a0500f400040c500703003000c600e40b0b621400b809042450f000d000303c819940752800c0c060140602c004041a03034845181c403103060391402c80001d9444000c4030305841031101040160003807001c184981d452021615030840002e007006c0c0391035680c07646001c01c25241c5001d0104c0110725040d81d030088800301c9444441e800d00f0924441304002012003d504100d9015052004a0001668881150344100c0c022009008480d18101c1400107076501800b6061141d0b150103107268050900a44090540c4d80400d510b0b03500c0d0a4030303e800d03850100c0421011701400070780c104004035022102c8901c0e200b8203030759956000a85a84901d000c0104041d1010780c26a10340034818003104c001c0d6444800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 458153525 1250 458152275 458152283
    0x2d060f0f06031c030501032a0314030912030901020c01081005040c0c050109050d030c090302060706020f04050a091a01030204030b07081906060e030d080f0c09040f0614040c0315030f 80
    0x6071a103c010590000392a118243c1400700b03488000420902004000c0407640c60a007003d080001c0c1d4489030520107402c0e903400b00411040e42c02c0080e0890800400c107a44070300074050080f64690340740b001d61594036003007882420700510450300142840c2d4402c19038103001c1c200b40891082818203190401020701085403804040004517082800030407002d0280c1c1e000f040c0108050903050442c12001015115010009428480c50120800040c0c4980c0200c030b8140b07800c2840143c95821862541c2e480c0e1195900540d41304180034030118807007850350300c161000e0b140d14030417034107880361500150241d008922001c1c1c085285c0c200040d40f400d02400032a03504c0392500840d00184d4282c9035800c0300f1103003030b600020006195460800c07402d007000c015078610f000b0701e800c040c802480e0094030007518000060842d940d0a401042e8011540c4a0750072111403810b0604050000c151034000a101d400c1c50710700e17001d10841c2006400c0c0c50990080c401d4150344d0045404a402060450301c44a42204612000f25 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 458154775 1250 458153525 458153533
    0x4090b0a0915050c03160e18100302150c01060e0412050c0c0402041d0a200706060302032e09051c0512010e010e010603020405011d01112d060f0f0603 66
    0x419840e03407107020310409002940986a0031b200d0305403215201e1a075504024440f00170700eaa8941d41e05c508600304c4100341002651b440c1d07510100315204208551380001e4220070450000b0a020790040b000d44100c0031044000c01800341d840c51075030b400400548025050748900c01e080c4450030b200310000d11403c4581811988441621000700341280e110384d11840125035461a600c070298036010300e46e0f40042408405016500149400c681d1107255240c00300e1a00e140000d1040c20060b483e0000c0000715001000c1e5142042005088043c03c450300c0d070001c4030140b60318005030a00000c3d1055200c1140c0140c020f105903107088003102880d000360841c18090120500c440d80700404181e0a0501800360034500083d0740d40740c011803c00507001a00f1107818103005000500950341d0101001114250a5505c44011250140161880c0c60000210000d60240c0408004404070b400011644002840c0740d062400d1100c0460a1712540180c1d0002c0c1c25803007110100e4800c0304900803030341d00010014159 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 458156025 1250 458154775 458154803
    0x612090a0b180c0108100501080702120307030204060306080d1e0e061602010f1b020f12030a020a110a030302100e01060e04030804020405061804060c020f0102130e010504090b0a09 79
    0x2180c1c0381c95007200d12401c416540b5118180d09101407254602d00b84003800c5c441d07014204515000010f4605018003410850341400103000d05108100b141410100d20308030541d0703400c3c07800c03004000c1d501c0360007104003181c108a400110100006546a03807010b9a0790f444913402000701d40501800815124070080014005428a455907400000c20840444002c112160b040d00e200240505104036800c90622440341c1034406001200120024040c0c3d040718004200980c04c030003e01803408401c0c01c020540310220702d110790a500000c3c500135150185c400c040031209c1e03100401c404000b2031b01008006804c01074040c41003200e95000f40c0c1d4842941400481c50706c1c0c4031441149044e500310b906a0004201e081880290b090911606400c0001a12002e04040d424800c51002060141c030062071980d551500c2c0c000705209100002c0600084d00080d0345c2c84017500300040403003a00780146158608480000541480d0030301c01c030490558007200a141903500c203a8403900921428034280c0b4a200081c03d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 458157275 1250 458156025 458156033
    0xf01020a0b1005130e010606110601030f080d0203010312090504060614180312030f010b040b071103150702030903060f01300204060927051209010c0507080f1b0612090a 74
    0x4010801d0031500c00004d2100100214203007510003561204042c0108400d918011149c041440740c10341c2d401c9a442010300b1070525011403148079012002c1c20042c4040000700c1008608003010142c810b82c0d5071102d207820b441d40c040004880c8035214100200741000301181c000f04464000e89400300f940c5071661040c1a4050110307081003100040502c2c5030f1030000400002c0d00303d44e21000d000d401d000d0308242c01c0c2814450b1000152045400207400301201700d1104074981c0c2c08000340d0340e4603d1030316010441c508085002a5803508400000b40c4240610360001d01400482d076180ca048500c240712185000702541c1103010021184210514aa24420075510160715980070380720003016290780014140c03120b01040003d061403503401c115a404042c1c0200d000c14400101201c0511003040303402c0d9038030101e50041e50180c0001b94000c0c8540504000024020b4011528041d03144a0070242c440c031101140107801054a107000043d4800340074003042c00031407c200b5505900103ca94111050b040c03654413 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 458158525 1250 458157275 458157289
    0x30506010210380108090c01080a110c0d030e1209030604110111010c0c0c0915030318081c02010c02070602072606091b0105120f060a0b0a0c020f0f01020a0b1005 71
    0x2070340c0054030300358420b01c101c07a582c841021580103402c1b00c05003000a084400080040e000501907036012070303c40f00d4551804440c1805c6403e501da00b0002c8450076451940064040c10034149000030b1400340070845500400260100c8121000003000f9040c00e81d03c0e40e42d4151a80300c40442c1c00e04200550417905403410091007980c924003a16200c044240301186051400c00364183c2040a109040c410140d1460803070007140c0c401e407981130406510300c0e80f400c1000c0601c05280c1e40010301034450401a44040041411510064020f030fa00a2000c10700c0d1207816a511101e070b210368001a0300200c4100300400003695100440544c50002e62802c1c0003030f801d560f02c1c4c0350003603031206a56041011300b541c8100e50500942c0c0c2442080c05c010307080820403110204844001400d8144c0700502d400058002d0751078985460280c4850300c6030b65100c400c4240005c040b00c4600008030300410080001700d41515180701440350903c4142c0c001c08807030419980d9205082000707008014103031f00c1c0d184041020341d1000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 458159775 1250 458158525 458158601
    0x901020714061f0303080a0e0313030c1e050114070303060302040c180f080c0d1703011818111309083403090e0415050f0115030506010210 61
    0xd00100403d0400b080358840848980c00040540545a082000040e802c194907640c0802408400070340c0100c1d1031500307419449444a440c50300703031482201100304201c1c200071500340c1e0011480aa40218480211034801c9035a000709400708141c410b05246800008005008051180c94085403140d960380c08907042d100110000c030041070340c0154100100c02c0b03441041004000d150103134004185082c2c800740e10b40000941607802810361402100034445903c0720810700c0c510404006a030b96035a60802d104040700100302d2a40581804a038022803008005541915604814812002850402007003032455500e00d041c48416186c3d0b001101140f2010003070000e1414581303c6c81c051848a00c11042c03001d040d116010082c0f0b5041c070442c80402d034403405080c1a910041c0340410541c4650820f4109014481c116200d181d0401c0d003003012441c1d031012802d040b60481c11010001c2d480700202681034520407909180140d2000c51486d440051540204034041ca0f0350480c400c80002641c01ca13406034181c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 458161025 1250 458159775 458159813
    0x21070303080411010305010f050d050f030f040303020d170105130b030d0201020a121406190f080115051804020f0111011103040b09030301062c1305040b06011b06020309010207 77
    0x16400c11041c0f10002c0c2000d0340140007441d08102940c1007105400001c040350180901a138100200d100400008202201400c0c01c09001c882c2c890007540345446043d4800e01040f0014001c028172004c50900860f401c86200c807819584444581c20700301440f2030645a81c8164007419110711080003d910184000d1030f8800c41c0b81e002594400340850b0251012003031131682c0319424900700002040403080301e5415004a0210707070000d602e5411800000c2c20f143c0320b4018080d0948000d000180000c0305501002806803030a1030140031540e00d1040200c0030482186c10102c0b4440680010010b1030721491400320300c40d0504010134103005019880303084840344010360160f81c038000280400d21295040c0a548642024000c610f1036040080042050f204a030980112503130355083d01d160318080034500001d000000d04419615020440144081c007002e50381610400800c001050403940300e81601444207040c9541d603a10400310380d960743d009520051019030700d55424040c130303000078116601d500618260 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 458162275 1250 458161025 458161037
    0x30512040f02040e030c06040204050a061d0105010807050306010c060b010210020d06030b0a06081b0406030b09161e0b03041b0f060f021c0c050a120201150b07020307030221070303 79
    0x6620603c000c642c030b400c2514005034024041c1e10705000000800551140c1d05443c0032401d900c03190441c00150030f0310f4000743c010311080c2c045121040310704441c66040301c07400d0b655100280c850450556072480241c6405000440614000700800d0058106901c01c250610403944500d40c4001c600c0308a822544000310800e450b10410402d00001d10109a00030908036010000180790503000c66480003140e11a200707840c0c901490f510705540c5da900c940000d50300141d44000d81e1502501c0b0300d8460180380500400246900004500d41092140020b0200801c800000e04a42090081801d98200400031030b6188104080d119918041e545030030014a2000640d03501c040c20040080c041400c0540c113881154400054101200303500c46030080d00c1d803007508dc0303002071800340d0504904044d0681005400520b00d0116042250382c15842050074882c8402201c90168a42403036103074600c038003503010390716034414201400035143c00d10130010359048500400342251116211142042030540c070039000700f00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 458163525 1250 458162275 458162303
    0x309010b0a1403030343022b0c080409020a050c190308010506090d140313120b0408090a03120804020a090513061e090c03051c0e0d03051204 62
    0x9201c1c1d60040900081c0480340d82d4000d048020996074000213204112801c0c01a9007400c1c80d0380034058404c110ba06840104258580744445000885100c55011006100d5a8180c059507920000103454150a2541703252926403070000407910900754180030790f41d41c03108000000700f24800c6c0c4010300318009103458082c1c40f440701107201410600344100300000341d0a00300c0c2980000f94003221803815075204803a02900c0e09240008100d640c00c60800003007861407a401e240c05030341e1002001e8007080c1c200000038041c0079102c0d0381c8900040703016400141005411800f140009101201504e03c403440235000e464587d5aa0700c50100e206c088950000102e0105d900748015400c0180d500d4003c1c111152040c8101e08001e005050705000074000074242995504a800001f080d10040c9003d2a22030071091041c0300060901c1404080b0034881120f00c0e11a88410098411400b802c5240d24107980c3c0710400034603413803400c2c89038590078400e049041102c1003109022100520418074015401001101c901c05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 458164775 1250 458163525 458163529
    0x807030302010e1c140d052401020a030c0b0601020c090403030606020c0105031e19060b0c0705040b0d1106090604030b0f060109150e0a08010903021b0105030402010903030813080309010b 82
    0x7800031440c5651680080c60107600104282d03840421102142c45d290310030300e401040b044454041c00040b030140d58207100620944401c2c4e190b261810142c20715592a248090f03800582c1e8800e070410004000c184081084c9010032819440030364014410b006440c248040b9400123620300004903012004031341c0ea20f9050042070b50401200303e15a00c207080140c03850404821210b104031804035918242003200300002c1c00300c1d070414809400800d0040040c04599140d078094486500124052181d500c0342c1c00780010b9901d0103010341c0900b4000031340320803542d80e00d039146c075440309090b102c0054004070100224403050b01c0d000000c1c40194040c0d1000f00c0c4c282070900100100401c0035221a0401824440601100c04001915000b403195404c161155101e04404101c069145078404d03102540b800141c80d00303150300422455030050303048400c4004039000700019580e500064502900141c0274140034400039000c1c1e1210ba402143c40c6801d8803040c4107a0b0b481b140d00d42d00407121036080d0b03511000c07095024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 458166025 1250 458164775 458164781
    0x7050309070e01030305040e0717090c090a02040b0f0f0c0a0b04110109030b150409080d050712111602030a020306071e090305060a050c0c01061d1807091d07080703030201 75
    0x19103070b0007611001c1549545c0300100640501d00035580f80c4070800c00880d07d49409000c104a64100500da00b840920b005108184c480052048031070103072103500300003004a003a610880d02591055035075581402240d598204841d0090042c0307202c3c17203004016540007d5410406080c03058880c82c0000b01601d030515282d241d1040d00064641401225041480045e80303c1c58155484a0010030407400d40300c1c0340001401070b24006102038480c0f4000240e4a011500d01d4105511a01e03c039205c400e5515072000104003100c00031082050603401c140500c41c450040014071424140c00103003100c1c0307a52b445800090502c030301036036040c011404800403c009a441103072140d9030b0140e1800d0041c449440c688440c2c1d2152401032100c4040c594030713000034401d0a41d60003503c140c08410300c002c1000c907890741c56090b002a0100d964034020001c600004e00c04004a8140c0e0800140c40c00203406003078601039030705001e828140d156074010b0716840341700f01030041c04002c10130007071074004001d0980d41d1850030081e0071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 458167275 1250 458166025 458166029
    0x309080a111003050601020c040e0a1a010f06090311061e1b06011202010804230a0305040806010506090303071b0b0d2007021c150c020604050709020c07050f0a0e0705030907 76
    0x140f6041208009150303801198042c0070480c10741c0d010801641d1000e10700c1c102401c4000007040c00401d08807114281c0010302000781a5001000b60085d00c03a210101540d400245101c001d0080f070b145200400795007003850203003a096440c2c0b816500541054100e07071a00d90000e44894842401e0741031142c0533200100882d40c01000c100d07035040c0980c03142c0e400080540000600c0540020890300c0c030f5220200407040044a01007150046d2070406e410361400800703e81c000d00c00c43c081c900c680c0c0000b1030706140880c110740c1d056500400071071800082c1c0e503540181c442240724086160100b200c0c001500321541e0b00a11141040c540005030b030608120302141580c007083c5032141010001d11010303005803910410f1440e01480031101e54091541031802c0f50f5048054680368000604100c001402d030303500041c0d0203000358171503011340f800d8980315144c800c101c0c002c80100c000f156120070401c000d01d06016041c6284502d010386100740164480c05d440c07140407410348d61000000e0001003080f600500030711030900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 458168525 1250 458167275 458167277
    0x703120b011d03070308070b040c081218012c1806030717010e01060906080f0f10090203030906030f0103031701060903141c120c05040b0f070309080a1110 68
    0x8504290000000d05072044949400200400e00c0c92144040d43c040113650010743d4003010032a80d5120324039006541003019101112400601003000c40c03001e17070116468a00807140d0303901a04203403009240120b540c4503000380e503050141201120099904ca600c2042d074030281583c504180041420030300c00d9803240512005104c0c80d0b5035092140517a00440c6c04030444e0760100e00104030503940b103400c1d401032400c2c0107001c0c102c0d882d10b17000141d040c5194111100f155500c1d400d5440307405e003040c0d409890b81d44d0650b01c501079400003150b2a41180b01c1d580100c51803400034084a061891000c04115140d0064891544800d40400100700705540140441050480030100c0e00d401d524104000e0300300c2e509800000c00c1612140d00e1001d41440c100003855140340540d420205a0f840c0c0300014182c01d050f984180302003414580c03441a804d02400071502203c4801082c03520b030420f080351440d42e6402c070b40360031000c001c54400e000544103803c026100400d40901010342005000204110309600b002c2e42600c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 458169775 1250 458168525 458168531
    0x90c18010e06120c0d05011e09151e030206041721070303020f0c0316060e0304081b040908030a0510060e21030405031209090105091902070305040e0705070312 70
    0x200c50b6211607050719454411076a506603a500c80a04a83c00d90240040441c0118682000090b0042000050300300e510000341da103985894580301d2240a441002d20389001559011104000c0340310003004014404000d500d144c03011a48980c0000c0643d88540e00c0080700c0c5600b0307010701c40b0071041805407614048004000070000444d400c05200b06004a0700b000e4189079010800912030340b0f04c00103d40c50065640183c0c3d1b0b4681e40f00d4802041c084d06501c0a4640320700d48601171100c110004100d070181d900e03040c024030b1850000a5842e0004240145050301f0580303943d950400a00414003542c0501614840481e0504c0d00b030142030b20401d520360100c0100001b54400e0201c9840340c064036074440410705e800d588110423802c1010f24511440d40200d4140c491403009250401b282d5020304400380382141e105443d81d03030310820450300c120705031206001c420148041c034282e40c0090b03000781480b51281c20311500b402d0703684280f03c00c0300300d00f2140000403d00002d0344c00101940103840e880c0c500c40c207013010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 458171025 1250 458169775 458169797
    0xf030f040824010b0f04030c090c080a02130e0c07022d061e0c1f02131505040b0d0e060411090f220309030b01030303020c0d0206070f05070f02090c1801 67
    0x2c00d110103018403800b0761030500024411150703882e91040f5030241d5048400c50304040d585400340c900900900f41d944000980c140040f8200307540794000c4900c9a030400110311486c50500718080821039000e042c1910241040088000507100c00e034811800f81d280c405041400d8032903d15011207000354854140c4248420030203444440300300b0b00c0c0980307003901034181c6907182c4074513015592629174031102d101d420381d0160101101c2842c4c503400500042012902401c1c225580751403e51000c01c610215502141080c00140b010820080141000380540f8101103000f8511070704c0f1b0b608110003627500752241c021221205500c2e083c091030f045e42240c10b80c1440c416a24081e1b0601420301103105407200400312460005042c140f00300050b0f0081c40d0440f2019859580d41c1c540640294001c540b80150ba0041e805060a401e00214803a8402c0c019511464070740c050790403040b200c82d40301400c1100c25800b03d60742580980c5804110034828400011b8050340d5121010b0705040500b18400005d04000c140b08807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 458172275 1250 458171025 458171083
    0x50304030f050f070f05030f030906070624180c02060405070e06011404090c0201060807031203091e060b0f0a18050a140709030b010e0609040b07020f030f0408 70
    0x1110122a041039444040003903615142c1e0814019000b100a244500b82c000f0409a55100c00c5a040f184110100c03880000340c00901622400f0f00c00d201e541c811000e00107440890036540107140240c1c1150016001a02c03c4201400c0c5180940c1080503604505030103c0212011807240c0e04620419000500582c0b82a68845513074200b00e0068807400380c04100424004e0f4051845240c072551000000364276642c6a4801034002c2894540c070000640c200030000800050102c1c1ea003041c0c9400207940f07198103c0010064001d8500300c04202c5203030150014070b82d8116048602c0c400010700c20700c00842e540380070204100485028021192260300b0a40041000c1d514100c10003c000442c03070000f1074160f0741e804c041c2e0001d011140c00f40710400b006c0010007190390780c03100f0007105503441481042c40a03620b03042c80f2090207008403996a0402c0e41000400c020418102c1c010350301500e0b91040b01c00803500ca40941e421600040d005a4460f6404541403100007001d000c00c40e031640800003590050080110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 458173525 1250 458172275 458172277
    0x90a060216141e011101020403110907050a050d0b06120103110109050f0f04180c0b0703170601140c0c060d0f06170c01050c010b060f040608090615120102070212011d0a0503 76
    0x710040400040303800c68051390140781040180c0901c2c0000f15100d568a040000a0410120340c080c4601c841d03100143c0101d00071401d85023001c034503580302400e20504000180050500d180144d5201c841840742890740303824919503030b01031881110010f030410a50000500812016000103129078250a1080103503110508244a01c04084802141c0e4429060301e0b00b8a01c1c0308403030b008c0c0100381010408a41038102170000e2400030710941d100840c010045030030009210003640d43c2800680c015010352848045600541441c51500c0152880c0c800c4000024541e0b40c803000d00c0751a0161103c1c09502c450b809482440018100075010301004541e6401c110b4450354a00c00e8181842004580010303a08825031106242ca0006410710b559402e605040c001290800d220b58400150681c001803444070000c500c1900440200442c81c64600d0040104503500d100105e140045e0742d424090070015903030741240900f0078080301000064542540425402c04118409140e200d50301100b111000504000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 458174775 1250 458173525 458173549
    0x10e010605010f052506050106020d0206040c0b0a0203120f01060e030609060117070b03040303050a0f09171c060f08060915040605060a082416140906090a06021614 72
    0x2140c0f04c1d503100c0341314a80c120b0300701c0d201c0e071040401c40b509400c2d01c04218155000e54141e8007560202c9000b0088c041040341d03604000c4030020b0080107084020041c010040c00a0080c601e01401500c1c14050540b02c401900403085a0799606e46090f5001042266003080340742641030401d074058026481e200143c00d0f42c3c1c00c4103105600c1c1c1030000a0041d0a0140c081c00301001a2151a079601d54070300705810010b000e000160b80d290b00fa1403600c1641a0380c070071203200b0724500f254480d042158040b146445503c190b00131841403901c801440200c580c007040c16124071030261907440c0351900554180b141092a041c0024000c42c000e90190355103044c00b14400040030b0b8043d42c40800440c4070b07903400d00884c040741400ea218446074840d003a03203100d1103114140d400c0c00381031003041c02e1005503481c2d40c1400500000740c50070310041000b4400d00c0311040c0c0e419000707207444c541c040c0420303240024003c08242c0c07032a203c0e8000b0340140c00c00c02150b10840500d0840000514540401c40b20510000e0002010305001d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 458176025 1250 458174775 458174777
    0x507170a0603030e0f0a0e04030f0e0904020d0204090201031503050a060e060106051c060e0f090c010302090f040e010603020312040e0609010b0906070317010b0903070503150f1f1502010e010605010f 87
    0x1710b0700c81440340d85565030b03032014041314050101142441e15000d016450342c4540c0b140403400e07000f915500d07410010720031072003660000e0461010392110f4003030000911100405a0400d6140c0012452000302001c0600040d4440e40c028641d80b111414000c00322043c213101211140c00081c0104804c5070310070290742520b00240d001c1c82c082d121940d44080280a0b940c070080b0712100789020400980442440179220f16500425200d07a6408680110120300c6400d03651648035210030094072150405511a60315100341d04000076070a903c03900020724000a1224102042400060611581802c9484139800c484140c84001080d411b0103c10101c7d40660360350b15000c1d1201007940c20505124801c016018012164100c0301540c5034120039401781e0001031654040e00c14404005041c2c10700041c40000884d032104105000d07103030620794080e8440d0103040c0e0401591000c800d40c031005581150000208409025400f4284100102a0940e8204010120a46d00d481c0302000a41d811440e042078918031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 458177275 1250 458176025 458176039
    0x60305010c0c0524180a050706031b020610060e0409051c1b051c030b0a03030e040b240a0507060c0c06050105180a050c04090e0a03031503171c0507170a0603030e 71
    0x40c5c0d030f92051401c006482d015116126100300040c5154140d444142c15000c41d51030303180c203c040070340241c1c4e0340c100070364001c0d4600c0900340302040304a00c112012020303a40010400301e0804041d48031a440c0c041c0c007003141d580d110801d054001d10190000f070182c0741b006408208010f40426901c44a49490003c40544c1c90340340c3c0707580302c07100052090b44125450500104941c1c5c0741034032810000c10038a500e01c01180242c2c41c0004a1019142c4018401500700114041e001e4200e0400284404c50300032251400c1403080c00e102400004410f4010101c0041d031642d160310440920341004000e85506074402030080626440092070704003043e03011540100148000701e41520b6200420b100b611980d03211100c0e045c60032114596400c4086020210305001e43d40034040c84000444040040c42030703101c014130b20052100c00031144894200075021010040040031076800d40c8454600c2520b1045420728000344070620100d1801f030403204001d402c547e552904014503411f640d8058158010f005040d0f100e540 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 458178525 1250 458177275 458177311
    0x60a02070312090c030b0a0b0d14011806051504020313020d111302070506090f07060e040b120c090c090f1207031a0f1303080606070303060305010c0c0524 68
    0x10140125000007029503a0410200c3c48500701091211424041241e42a814a001c11719400180c02030903502c000007010080c00d82c0c0c090341c0d00384c942460f0360303d2001c10f5505d500d0444042509428400141d03409010040342c0c0d4a010700c901c1c40c104c01c444050034810340c41402407184200b4410364200700543e06848141d494150760600800c909034041c400b51f80465158200c0c940c0d4903581e00a050301e0348c41402212110b84071030405c1501c583d500100300b40c0c071781c0c0400c20400025201c0c50400c42c49002c09000022407084200104020340148a0004000d5007d400106400d003003002038240d004030710316401418585808000b034031702c13111441d0141c81059410094003d46c0028400d1900866000185900c0700d51502000d0010074011280300d04101c1540c0c0019048502442220b4045581559604c90304d945510401840e03030080c54060b020540c0d199030200000f0307000d11541070034810549849101640c140b40c2549014007036244a29004400382800c5940211103d5191f0481e05c1b145000d11140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 458179775 1250 458178525 458178527
    0x20616020a0b0d0501050d02010516060612060204050321160212030705010b01020d0806090412031506020705031b0604050f0d0501063507050907110304092408060a020703 75
    0x841141806540070008000001c0e155441000070841d256005005204070307aa910108071030100c0003540680415030030400c8003c02c16800c482c0114107840ba03000020300f55283c80c1c500c0c0c80304c5401c0708111030b82c40d400201442540350800000d203d0688a58240001d14148030f0002c0d5240a819500005607e40d100078004656505447e99880190340e400c50792100c41e542400341c007030121490201d01500403540782c2c1601c00e00c00c50450303110740009041d140451300c85582c0c01d10051380744143c0d03c04040c0d58050f1025401084140c540060045074010700d10242001c007054186955030f80c03540c1c100000c0308580242d945400080c0c41c02c441c41111302c0c00301d0328180404125400c3c22031400411075403a20b54080740404100c080841310702403010714491022040e200302003400044446100c12a44902c00030082840d0810540358080401e01d4418602480343d8a694510740064101076005a00d80c400781d0b00d11910f2682d41ca008031001051812001d141821160301e1315030282142c0780058001510000385 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 458181025 1250 458179775 458179807
    0x1e1903030b12010203101d0108060f1b191b0215030601020a140105091c02210417030d0f200310030b07020606130606020d08130c26010c0c0206 63
    0x405160000b5562850810340b41b001d40c050500444601c52010001d0303040c64500074801a040e140700100410094a41503010300e03485030000d1846200c6090f0340a8014078007000e00140c46640712412014031002c8100c07501808500d80f010701e00e541d081c401040000566501d82500203103405407040140c0d640c41d0200103d0503c030761000040d01100749625010540101540558842d40408060b0b07525022907180c1d409801c0b101c0381e55a4010780c4412440c0c0180100361205840780719080702c0340c0e440c140e42c0b00c4034034040b000f03800141e10041d0804603401302c140680b40a48254070540311010461141811411032032540320110140b8090b01c080002201502640c80e808090368100b0700f0740d1154a0107010082d41c580d0111030b500c0c0201030023400c00c0312018860088809a07011500a030624006c00401210349400042200c42114807215000000ca0030a00403440035005a078912000c00d18034203240c0014040e24502000f841c0c1c944024141403d82c00384140300c101c1c0d41204e0303403959207d280c011940701d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 458182275 1250 458181025 458181049
    0xb1008120d15120c154b09091103010e0f1302041e0b04141b12010305010b0108070c173601120b10030b0d141e1903030b 53
    0x40301d111500d45050101c89001139040b110409981041011040403c54000124103c10321060404542c0c0c3c03100700d1045c42010310400c0071801e180240d1102031001c22000c0b0100c25401c80410b20030b4106110001d128000c018080382d410344007501e15454030301003100141e80241820480c2c00504042001c3c40b100d44d0f001406035400400511100b0707808800d00704940085400a100146840083d02e5141440e0003142c00d150742207414000d4031b903100034040c003800600c1203103000781c0501000000203a054064846000c0d6010b41c00020b080c22550700003400c4c0c0d02014006000303000d16184008005100307091800213100107051b8040c1c17595072040b4040300c00001e00190320000f455142e070703841206071040c0e13000011640982e01d118100c074002c1d00d07020407a0000341715181c000e21011007480a43c1e00076000b030000100082c0642101d19125202c001c0400f502c180b40e10050380004070b0600c0ba0303070944000d030401003207a60060201d411019135a601400410100103040c16242c0311240800e0340c074000721001d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 458183525 1250 458182275 458182289
    0x60409031704060f060e060102100b0a051908070501140a030c05070b071e17060618030708030c100501060807080405030421060608031608030417070b1008120d15 71
    0x1006050a10b0703c20041d00701e400c00c60401528040c800500401d40d801c40a00582c0181c02502036440d81c2a840d0001e031452140c0e140c0c000a101000140303a803105006a000b003011401401d507941d003008111800c00380f15030302c40380c100302c56580480c00e0b600c0c2c44002c4408003d07840c100060020b0b12080d00b40e03414058100058942c03a806001c20094540000701600c0d01c1654109100009104c0042a600c20000c0c01100c0034010090000400d41d003002401400c1c90390405a031019180c4205000038500700d0241c01a9065420125405840c0e013001c1044400c8017010003000c0c041581052002440d441c030041900c420015000c0204040c0a402d00444001d880c82d02d14021141d15000800414901312803c1114020b10b00040014030100200948208001c3d10140c00c03071901c180d840300390302038002030004d8528009030711400315400c802c2001880d5a0303225608040c0700b45001505141103282e00c0e40f11400c1394001d404078038480404103040301c01009003402e000580c940c0060300003008002540082c6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 458184775 1250 458183525 458183567
    0x60b030a020318062703040503070b040e060d0b1603110a091a070b010b030a15090b040f09032f071202100203040807050103020f0c0d200a020906040903 67
    0x9010340c06400643c4607107030004000300260240d5040c241da88004507030024100300c01070030940141a0350045819a0b040010403030f403c141c3c44400281c00c100c12540200b82806000808001d9500501c41d140c0d400036044134403421030071850300d034181100030040043d5407580084410420183c0254045c40d40c8080841c0142c0d1203c1072450040c040580c5402450b8413000e00980e0701c28090a901c1c200d030982603100a038502d541c0d1900f0002d20303039600044d18900d441521030031900303829090f006036400100310283c03001c18080c02e0030303052000312904004d10b0405a82070032011004641c110040001042a0500442001e8000b00d04200c51034115210303248503004200001803e152101c42841c0e505000315107520000460b4103040c1d94070f00c514810148640c00900f01005a90302a80c0030f402458540c2c80d8051070326280901003800e1036400c031224808191402c1c00d842c4208a0710040b00503421450000b03000d0115a9000540d40080091051f0b00c1030380c481101804051141c9040e0f04490003a01c81d00d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 458186025 1250 458184775 458184781
    0x402130f061101021305211002030601080c0c06060f0d02040504050d020114040b0114060712081006020109031202090604050918010f0501050d0b04060b10090306051302090a0c03060b03 81
    0xa0080380041c81140005840d00c60b00300d007411010710848483e0007540e09422401e41c40c00b0705100c03e050104400a040c203a2052040e0b0400c9001d100d10511420210401660fa1074514009011020003800c0c4040788041407140c2c1a164900050706508101e0850351164002080d5000414102c0181c8000350040d04003c00d02041110006ea021f103400e0054000b406030381444011000b0445003110003400c0300f500c080040000301520f20312944903003409810140b9080c0070f51249c6031004001c200241c0010a501c0400100e0000440054050000c9100130b1014440c691001480080125580c0201030f60010301000c43d66100d100303c2d0010480078204031418584801c180c441c1723083c20400c5200725404c20383e41030304609440c45402d041c1c603c01000c50307241102c15111148010f9000b00211001c554856807801c03180e80b071407220000310026a03184c5196908500d40041171701e9000e04003aa440d2000b10303060006075115114690320526200001500030400c5400320082c0c034107640015460b000000038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 458187275 1250 458186025 458186039
    0x8010e0604060609020702030303131a240a06021e0a0227010e040f1202150c04030c080106050303030c070c0e010303050c0f07080d0e0f03061305060a0506010903020d02040213 77
    0x352511581c0240000c000d815625240d2200342d119000000754150820000644c8216142000e2070041d402144407071740344090428840c40c101350540703160785141d007100d4940341c3c1e800789400708513900801551203414540c0790071400303903441b4261180301100c207052103c81e07980e008081001d016280c0d0020417001a0b440c0b00080f05012030010407129840d2225070f000441c1c0c0c0f00ba08440315000d19408010f03941600569203035400750240c01825941140560036600300ba0100b0441440d0040c0c0381d40000541c3c0d90300d146001083c0000e2a4003294a5905000080090307039400b00075654056a079000c0300c0e0341e80130365103000201d0a410350844414004100008410305900001901141c3e05c08011604503080107a0f441d0364860700c0d0311580c15181c0c08510790140b020f104500c81c06602e0405000100d800c004400081d0900710308803400a180081020b40b80140401040ba0a0b00a41c402000304214140040024a00201400083d01848140d01c00344210740b126030444500181c4001299101921075030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 458188525 1250 458187275 458187283
    0x90705030709090c020319032a3b130f02090f040513261b24071d04020307120b01090e0a0c1106070f03060e01060f0305090708010e 58
    0x11081c00090314a440450310505070310440c0200c03502a0010b60610000b00403081c40d2481e01d25104041503113641425903520050211410000184107040c640800901c1004117016003003000701d07800041c5000703007030f40c1d403c51081240d510703444480c4031080c184408000701e01c110580c041481400c1d86440e0214841c18007a80c05041c440108581116560704501c08010544000365448094015079952540018401c400e4040c0c030301c000c40f041e0302c40728641c407085546a508110f01c071103400085850807200c4c2600c2440f00d0064060469100620303980010111102e1210082138403040c081e03248100840080c0404221941c060020419075481c5000c040c02422000594007070900035041c811441c5440d03019a41640a95082c2003407a4501d98500c0f01c4400942011801081440040100c101201e4024050700380b007080f244d02c0b00f2901d00c00d54840142191940c1d4001c2c907a01c1c109000520640703034454240644c01d001c44c6400300e000d80300c44100358141311007640030241542c640303581c510395800041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 458189775 1250 458188525 458188531
    0x150e04050d05180103091b0b071b06050a030b0303090907050702181603020d0f0204170609030906031302030f100c0305010806040c061d0a0f0302041805280209070503 73
    0x2410780d401d01d4a0301505035201e014140c81d18480c1440c201070040f15520950000300c0b410700a040c504103031200084882c2165055030040890710710000f800f007080c80345506421406c5070524991000340e6240080c010410702410380307943d04044d116071724003e45039003c01c26140603c1c802808101103052414001e40705500808003240a090f1400d403c4261b00b508296640c8191001c1a4007440c103500000110029400454401030b0345503110240108480540301900c00b402205404a00c0c56480a15540c40c0070380052511480703910401c0021601d480e100c0569800c86076200300d0aa820850384002810302110a800006034411142c1003c100b60080d00501b0000d40641c8081115903251a481034070386034121005010305400c0c001c1041501d20034207400c80c5030b5480700503c04c04c80f0340000009442d0101d0340e02090010105050034410361505208810a40103449030910f2016a02da90302521640f180c3d0f170310310007a5000c001071810541803621b104401c07540140300e0303452840c0c00c1d5401350a41c4c00035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 458191025 1250 458189775 458189783
    0x10e01060e010f140a030603080a02032104020d030311070b04121803050a170c070605040609050906090a0b041805010f0e0604080403150e0307030c0314120a0504020301150e04 77
    0x510544034095020759800310000f100c9a0b9101c080e40302e42086440c0c00c2e4482c00d003840400d030351210000007007202000031b0701c0c40e08940e5002d03590318040311203002040c0d02240e0f0a0790703454243c5824403006130f845140440d1416450b003000f08817005001100302e00d0b40500500548400c0664082000b00b148402006100031659144d25668061440480b18200c16500004101d940a940004046a4101012044448002600742c030703090900d4190b50070216a580000046440401e080c401d0310f0300a12400b014000581c0c10311503500d0134100003071403884043c00d80380c2e15039a95a0b200c0b4194895800480340511060280c480b80000351030420300910317600000b40c0e072040c90b161030201084030204890307000b190491840f501349410340e15044044400e078295007291541d40c1c903c503460540c1c10f101a00015020f5268400c3d980750906014186000f0980e104114080800c007103030f100140b04500a4204210180014540d602c44c030129006010420400c0c44200c0142c0002130b03001c240c0a03d00340f18503c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 458192275 1250 458191025 458191037
    0x12050a09021c0f02120c0d0503090a17030d0e070b12010302131e02030603010603150e070e07090303050705031e0c0d0305070f0c020123180d02090105060f12010e0106 73
    0x80c40c0c010b02c50542c40d5004108400c0202100013500d40400701c2c181c4003090704250f4107402258000540440c5010104580d80d0300041342e400030b14504601daa070005c02c0c0ea031600324a14a4a079416a48a224645050f121541d46844008120300b01300721400281901010079555842e40c00b164040d00d400900c0101d00c20030070081d280c0000846802000301d114414510b00c0000300c914a100006908004c2c980d40d00f540d40c414000022448041e0119040d090030900064005007100e445400c000d605e401000d002524030302071001d0750340e002d000c100490381c052074a00c2d04c1e9061413030110304500c900c3c5441c0d00220f0a00750031b1540f988101005107125500c6078200c803c0221114001c0e429284210b60600103c0c1d88400d008a519001d411a1144a4414904460313403084c00350b039115091105038503c590fa8180414a0800d40d41601420b8440b0807044560402c42c00030303940018540201401064001e02000c6100d84041000c441a600c03083d5074004155903a44e12103048203071590091213580b0008070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 458193525 1250 458192275 458192299
    0xe0f190b190609110d1b050a050c0a050304150e0f0f01050c03041206020a0206010e100509040312091511030f0103060c0c080a02150a0b0a0302011b0602041706181c12050a0902 77
    0xc1d20724040046e400303550b11641c1c104446014240e4503508039012103a01c500940035100000303201807008102915039250800c03840721000c000103014059010046001c0c0360204030001c40c0da9034003041c00018003000d10701143c1e2019000d11040c1180100d0f070015045050f080c4091081241c150080c0c0f0b40c40c0000c0d42120000c0e0383e40c0100898050003a900a10074200001b0b090050341004030796980d100d2300030b05084203880b6000180b44d0446240c114240d81d0025404030b962a180007a014280c42c040f10100c11034118103000703c003503111140610000b885550348a03032040c0380f18003c03241100690303040381c00c903a21801014806074942400703483c460720617014400003411048942c81044240c0002030105000b9505540c01500e0210f0107084c0e1961043e110082100080e075280003c0c000781c12020305000f0102d4030400c0321403a042c4060720221401c13410f841413445000e40002c0c3c141a10380c00d0666074056003200c18090741d21162045002d5010f900381030811002c4840e5410180b9000d04c25924104405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 458194775 1250 458193525 458193551
    0x151c110c06090706091505040b0a0804050c0406031502160c03050303010f090507020a3509101e030c050409050a1401080f03040e060604090e0f190b190609110d 70
    0xc003440c0038640200c3c011a1782840b5043c0d01d0400703925460594100541b034540c80d44038005094000b25003160024030054100310410100703000e080300c80360054078140045811640d80e80e42c5c11984004e040c80a541c003255405203240d0000445003038076040684141003c4e12170a101d5280d50007405981031421008500040740e01d424817a00b44990322035030140c03203007007050785e2141c0841c40038132a4003010b442c0c0d004d61002103607070440d90418421801d10400e6555441c113000c0c060f13444206410ba03002d00802070346000003a100060b1440042c495803030009000030b05a4401e441134000c5821180c008d614000030484030300f0107940084074082002241183c26070740d8980807a41c030b00c1c00400c82c90058009200030050b095441d6590340c1c006c0802004241400e0b284e181c91000c44070100c144c1c4483d9072001c2510075502c0024000044120b6080c0494003a40916032134400500740b014018a031007290003c031074540368003160b000303801400341800300748480b090584910700680c0105001124091800d04c0100300340e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 458196025 1250 458194775 458194783
    0x1606020a0305040303050a021606090608101208160b0f04110a05010915110a05010207121704080703020114090708070501110c060c030c07030c0609090209151c110c0609 74
    0x140754580d032031a1625080d5070381282d10f0741001030104c00350320900c02c00114882000045e03402500d1340c2c0ea42c0c03400780361030078000031309590015114800544e4502010700c1101c044c80005440716801c850400c1c4da070350030280c007108201c2042c40040c1c440300d20001480365960703400c1480d50240340108090110769074044100100d400585c401c041c0800d5006100f041080007052458203c02d00e24140305451216803413070a420600512403c40345654002021810041c42c01c0350b50035014002c2c500b40e0301d00115404088100600640098452400442d8060405101b50807240c2c1e0f80c10b105400600c542005035055550307480a006910081c000c000c8040f499500c17030406620541800001007031054284000e0040301e41c480461154640010086040c0081c410000c82006501ca01c07201200d10b464154014030511072a003003410064010400a20703995103010a1642461801d000981d5941651507400c2c0c60b050101c200071041130400510312a0440c1080180015628040554203c3d030742d40480c490315 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 458197275 1250 458196025 458196043
    0x4030f0b040b06061602090a060e0408070c0f060c0b220606060e0103020f0d05091908030714271210060e060307120f021305010801090c0e070e0f041d160602 69
    0x41c69500c40240000b47c0381210b400c03500f10141d0781c000111603481c0c4901401d400c1c0c0480d81500c0000d03000401c0c100300a42c0c1c0c070a41004195074808400001d08005001f0150340c0524000742034a1018408940500100c02602c210306a000c02c40002000303840c64850302030021b500c40d9201083e03498902c5100c5500a000300e44c900303078025103243d01e005038640c5080700803c4090960075044c0309440066002100d010824118280510320107600c0b464540c100030b001e14200ca0030328104a20520030314800a50391210b0354031495052401100295a000c042082100c10217018030852281000411b030804265000100350740300140a1042a0b60f140d003455a903070035074030800701c28561039440700010403084074001c2003091005102c2c0640070b81440b81d4405450080c2c10062141e599041454100314005000310003c1c0035100f002d80c0380d0f00d030103203003e849450011303072860041c40912040d02680d900c660006212010307a86a600808420b0040b140d40d4184814012243d090708850205510303000244910b9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 458198525 1250 458197275 458197297
    0x190e0105060127030206031f05031633120f05040803062206150809060f0a0906060e010e061c0804120f061b030f02090a03140304030f0b040b0606 64
    0x200511102e00c04001030040615280f980c42611801000590382c850007140584643d00e400745002e4070301c10004801304001d9103e075100c0d900034001c0301e0094109403005001c803503440800c0b441201122103017040e401010941c0450b103200c45100f500031280c0001c0480003001c1d0a40302088940881102c1300100c032415507002c1d1406d4014000640240391a07075006000c0b41d15030350304403000c4480c08840700c261041c03a0455125540c0c6070702c840c03020030791103400c080d488403116008224905000b002e150480d84040c000350312890325040c049050045070b401400c02045010050203d942c0d41d6585c45207640c0781a601684598000a882007000d00c280c05059034031900b00103024609440c00082e502c0c00d0202800031112803040155500115507548201c4100904000084c12618041d071802002c0f90100d1060000d50340c03041c0f01010740e9844428203031060380d61020082004000d4480c5652541c05540d100502c038078020048801000b0384d00071628081d40c820301c0804440c0d02d88200300000c500513042050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 458199775 1250 458198525 458198537
    0x203040c0530010c110d080a0e0a0b010b03161106060103200c0c01031104080a120512010b0715050108030913110703050910030b011e02030909190e01050601 69
    0x21000d0301d0710b82c45501681c03100300c24000000242d055100407801d0210114034071039640b040c180301100d411100c0c07110407081e540c01414009032003582c00350490700043d1041c0130305596442480640300c000c01c070b41ca19458101c0c10203003207980d4810380c140c9940d10071034000da6111038101350414518040e42c0450b80c1900550090f18050343d800c40114018503211404c80c0070441000c03400d200041d80c407401885011b81180281080c5c400b407000140640d0510480071460280170001080290030200b418112650f0069103008503045c0b02908441038018884800c0114119a0000401140400051501b50300c50070b082082c04a10310304000c102e42c401d100e00401e5070030410000500349804007440074402800040010140010300f520308694000f02c90840102c1c0001405d1099868171b805400d0010286e4a0180210000320700020041280c062000c2c4080c0089104400d070a8028010380d50381781d00141285000d49001c081c404400c528080140e0000c074135000c00162114010300a00e4808d50041e107401e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 458201025 1250 458199775 458199779
    0x20a0308160c021e090c031b160228050603160c03140a031d0d0f0c0507091406100306210201020309030106090504051c020d080901140a0614040203040c 67
    0x1c40c444041e1400c0004124225000c64016555090803060303010091000000103990503050058009010304603004c000c00600402000e2028503034042d4584403440c0d1003d0f1200180080d1012902048200941c400702c0000c0c401081441090b114803a14400c030640d4889a58030380c203014040c40260b85603c0c1d035111403091340325454014555100f807181b103850300b01041a90744001d464250001460880041c7d10340b130008040c1000c40c3c080c8511141c0c0b020242003113203100d950241141080140c0c403001d00014403104e406000c800e00002d00181850001405801c1000045003003020086954510611211604d0301c1160311030300c241c006440001001400108010b84690a045208030040b41140f00400007140c290f02c0a000f0b18005040406011950707080c18641141055429000c001d001c10259200c211805d40c0020300c42c3c1c900d0000c0c00d01c080e0b1911800c2845014000d50182c5403844e21126060120034003040d0700a00446007100b0181c103d04403464200000d0348402d0381c0241851a245c181 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 458202275 1250 458201025 458201041
    0x130b01120b2d070807090902130e040c0b04080102030a05090120090a03080d27030f0804080d0507020f06090d05030a1a0307080c0f060703120b0f12030c0d020a0308 72
    0x91240000c001641e40402428080e104003a200300031101e80f80043c0444080c810f149410030410009000d01070350540c00c09189110071a04043d242c42003c407504040d03c085030600003440c0380c0d030780a4401d20150340d80e11a02c80b02118043d610543c3c5011482c0e10b020001403031140d041c404c045116502d080c004400c4c40a8001c548880e80020040369440503e113800000083d03086d400604a1405070b00000c41d1034002e05103901113500c018801c00444140210100d80001e91107080c250101800707050640c083c0e1114101503c45000d0301c41c462032a03a1400c02488005900010342840000082040340d4480e42c4144981ea150081c0340c0c802000b140f001c0c00419a44600c6400882c1d03488034001c1c071490f4075080700b0001ba10300066503000000c0c0741c100c0055042d40d424441a100030f22902170b50700b80d01d0305020780d170010a400501c100b00366500d99207052070402c40d40d4010660300380c040c000b0030034082008816041034a9078005003060000d03100e01c0007100003250000c2480090180c01d521400f01a6481b120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 458203525 1250 458202275 458202301
    0xa03020306060f060d02040303090515040b0a082505030415150605031f030b040b10051507020406090c050c0705120a0b130503030103060507020607020a020604090b010e09130b01120b 80
    0x3c00c40d40c010f109100b825030031452440540000c1d4060780d0b66140c2c040c68681171004045a603441601e000030200424807614102d0422690352a646180110340c564620049292011003c2100540340710840407038603005074010055805a0700070541c03004040e0f032208102084480751180304822040e542410041c15002c0c1002d503603c56001c0c1001c0c00d01941280501116aa603900f0032140e61808105010a00c182c0040c161391180c2c0380078401425a060400003040c1150030390194040b9840003505a0840d1a180c01030350041514540034480a91240c40c06455500720b03284003056481070341000585450000d4003000c92864440c00350418007495241c82400703100c010300c0704511140e10510080003c038208010b6008500035000002c0f10304007039400074103201010381340301c0c2198041881035000d40ea404e802c881c104c0344030b68000034042001d6001610301f00f51180d00a5841000b401c01c001c124510b10202043d420300c10030b0b00c00c10b16a06ca204140a543d0340c2e20f4003038054035010000494482e0103070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 458204775 1250 458203525 458203549
    0xa150501080a0c030b0a080a0506090601350d11010c0309020609091b030403030f0f05360604052803090513060b0304031205070c170a050c0d030501030507050a0302030606 75
    0x100d00810039002c105c01041041c07030f150340005030a6100c1c2007803a090210902c412600141010003030400c41d4907142c9401440b261103d981108000a200329480d04825640510398414881d400d5406034011214007070306004031081074481079420030202c811424400c4c440c0c1521503600502c2103090542d04400e0118040c001451081070802035642042c0e003038070074006944a207200c0e50300442d0081440c83d08000b5280c0103103c401e501800c007400e2201280c0085444120042100d81c17140c018030015900c0d9030f1000101140e1102070040c80e00744018807102266030154100002d548643e80c000b41006d40382c0c0e0003010340000c1c0000d00c807080103001900c0c00f01034102c10742d0100f03070000c601541c07940c840401c540c0c01500c3c2100890441107803a6003821260107000e500c0b4001e400c08d80d880087d9911a1040c0100030404801e820301e0004603070710000d001d407098460524130601255828a50f0301c00140041c1400c0c04140c1c0c0901c100c2d000011507141c000380c00c030240c0381c0c050040d049548030b010900014002003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 458206025 1250 458204775 458204777
    0x140f0a060b0309010605150c0a0f0303061d10060906020d11150c0304050c0a050d020603130b010e0411030105070e0132070b0901050609040b04030c17030a150501080a0c 74
    0x3003400060380d00456000d0b5000d80b520400015a0b9490b000810103000340c610725807040c0c1001403080c4000c2d8103000c6600c00c00c0c19046002c07800000c5245c87c0840040c130250b0044061072004e1000c4555902c01d011320148605e00c00703a80d40c1010354603030743e050354940c20f031f48910001a030142041c610124410025020845141411a09046002900d4a11540341240c20300c662400c04000c0005201042204440c01e08007540c40c03120050038140403c000d0a140300001c1d00a04000012894010030640e142d5440ca4000d24001182d5840b40c001148141055a003510a0440082407200520f418890140290380d00c0d1910501c0074075001c01502c005407031450b014a0380516402000b243c0310010110401030741c41c0c0241503521800c6180480c82014050070a100c182e00d08400c0004585900c0c40780c40d0480c0c2c000100141035a5a4a002c071110003141800a2004243c0c803001112058140083d50241d04840e2043c4201d003103440500d074680780780b48902400181b1941c040ba5800c10b156100212059017 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 458207275 1250 458206025 458206031
    0xf060c010e100f0b09040302210c0a11030601081603020d0602130303021011040e0c07020a080a0b070e0f0a090b031e070f17030406052a06090c0103140f0a 68
    0x803610201c0d040000d00340d44603140703a40f00d450100c4540014450084110b104442c940c1481c2000e80f0000d50f980420380c002c40c0e202c0d07140d003ca075000501c001c054480c2a5840030403200c261140c0e2074a00f403140d4220320f00358001d115160001c5038100d004681101003010301070000319200e241d5002c210040d910610140c1d10607a0803c0185402c641c0e407074000024500913001051750030640c417240000c84071051b01560032070001344414800c0c0459011159001101c3e88940f60300d800c89800041c450300500c2d4000451842407400f11410402e68041c1d00c3e100e00310940b20300c0355200e483c0c0148824400c07800511a4000d41d030f848107111403469944002075180f0080d0460b09a441112807104440703e28104094040d0b220070f20420161b070171640c2c540e0140201e14010022102d40003620b030b030b882c0580d004d4042441808201c0c00074020745441e00207690003117001c100c2da0300e000d80800f5a88440c0c042d114803069002e101d80d0480725500034052840386600703002820102d641c2c0d4159140c09144050640c2000c540c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 458208525 1250 458207275 458207291
    0x5040305011a0907021504080904060f062105040b040f06060b0703050301090b041104210804090c031d1e151e280506040f0203010b0c0f0304050f060c01 67
    0x14091050301c1038095001461042c10030b01c0010403078903810050240007150b00203025040b040c48000255030300700b41e10010194a85509800290181040343c0007101072510f0380200040e100d5104422085103021ba040c080c0240359038040f16820b45130b00321806801e00c90ba2401040003d00d0150745d08010b82d000f5140003d0458684079000c545500401c820741c0012408001406900380c1480780012149d01101e04015183c626400e00125004a00c80c669403040d990b4080c2141c0030340d14409810280d802200c035507885440d5090030340201048030365100081e16181c15801e003600c07048680710500006100801ca0300580800d00d09814036800c1c50b141c00c03401120300c01808102d80900341800703100014040c0340c01403070b00403182c03051020040080541c0c5030010b5400d040d54044844a855000c640c1e0008076240d83d914000c180076100f40011a41868030000000030301300b6850014115114036202903e203036000600401d590790049008540e1f010700104c0030343c2c1d09403808400800c16000b0382000803440b80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 458209775 1250 458208525 458208533
    0x9060406120e190506061207060809030904091514071215090912021b0a0608150a03080901020c0d020913030c0b0a0501212111030412020a080a080906030403050403 72
    0xa01601400001101030220740820400184441e680c840002da4178000c079407c0703002c04595903004501c500301c10f208652010450101080c4111001c0210140017032050b1006803030070210824a0046481071076113821f00c0383d1810100030048900070740c4a50707154a07034a0071030020b21008215942c490102d10703038840400140a113880c0544010103000300c0f40c4001700c9002d410003a00309802080e800c29142d00c03505500d0102c3d6100c823104d00a450442c0f410007010366910009042880002411950140f08003000104000c90040185407081c02a42565480321440085c858808e01000c0001d50000001c0d00041d01c00015400714000103000345000780e841c403203549440410100541d00041015110001488400c160514031100c2018140d0b0a208104403506d94a910071104808580000a00320036009118418003408406c0b08030201541da907141c1e908141d0081010f0b07014101c3c011000c0c42e600051000c00072410f83c42c840d801c403aa203450145e13540c0802900303500040c07045050010030b02010002c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 458211025 1250 458209775 458209783
    0xf090608090c1207091404020306060a180902040b0607200604030c030b0702030708041d1b07030e0f061c0f0c020d030b0613090504020108091c05030c0d0203070c030f020309060406120e 81
    0x6e03a1801da04040d41400d00505047c203c0042840d0b00401940f6410001041c40c0707020000340421980300000c46890b2440041e02503c200a0b106600103404a044410700c51360014944d1824170141c2c44841103031003101400f0080c0542d100280c03924484003006c001142020182c645d11145a20540341f0700707980303640c9083c4603800c01d80003900301040c6448045221082e81c20041d42001c2150500d80b40c880f00304850360058442d01c8002401c0015100001100d501d403c0e0303441201d84c5000f03192607101c0000001001600400ca4030300024181010300c4980106100d03c554081a003042e0b010f800d00d10a1542e0a40c05400303000c2c002d503008003003046807581d04140e0a103d0000760800b40408a510308250000601070070340901100c15641010030202e40060210078100b20002d40ca0912a071241e031200d804040500031a0181c428250001003000361055008081c05521446501c0d00503d040380785001302c1e40ca02801c0b510f40e030082d00c1040140645030003801c09080c0c0380400b00c4c000c513030401404501410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 458212275 1250 458211025 458211041
    0x70b25090b0a03020d06151d011d120106030215070c0506030105030325060c0801091d0c040f09050604030f140f030a0f09150b120c0901031e050a030f090608090c120709 74
    0x801e00da44550350200310b204504248c1c8024031b03158003406071042103075030072044401003680714140d621014215004290041c0c40110b400511b000c03280c1c0341003162041c081c0d0000c5800c80343d10454941c08a9035150600543c1d0588501078001d5007131180240001c0340b55003103000620325041c0c62000d4000050064010818240080d540e48145540760200c0c1106540c4a0101500802c2d00c1e10302c0490250400650340c3d0036040119404038400c03c0b101d0000c00203240300c3ca4060054018201080149a04012801c070841340030f5441800301c1c0704002d101c00450149001440f403004003007012501c5048540c014001946504100041c1c1d03241d140ea0ba0300040f040b02950300646612942820100c0c9420f0101440090849000d400145c0000c0b0020f8070f003240500004210220340d10384050522142000c038031300c0f00c0c3d00c030b8100d516000c100e01b400381006040d81ca0000009a9448011034270358410341c100d900584e00880141100c25280007002951050304035100c16500c660900050260308901903191 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 458213525 1250 458212275 458212277
    0x509070e0705120105030d0e0906041409030702091b070b0c09042d0e0309090c0f0d0623090412261602010b09041106070b25090b0a03020d0615 63
    0x90f0710000c1162020480405910061003500500441c4041503082083c15080c45411a10322181d9aa06030018009013818503003680c0704081c10040041150b000402481c0c0503008441141e11681d850301184140c032180a0003000042040c0700389400641d80c500850380000c6405502c50070011000c020408840500700385801d40c2240c005044201d0700140d035001c00d080c417101018040203039280303841c99907480b0341e0304454083c00c0e428000401140040b01130b203c0902030001d14680d01c0c1c5080c240b03640130f400da1340149040c0d400100c48407032403020300501d4011481d001425566650b52030761031301003000d03080c40402800d00c018680309aa5a0b2034001d100d010005003601b1a038002e00340b81c40039000d8004131031280d4043da8980b803000e0082e55280700d000c035805035103c0382c517109505d5100f000c0784a50148850050183e10100180a0130715801d52240c4d43c5c0481d0281d07001000d071130003103044500e000f407031140610380c0780c08004903142c0300d01c290010010f5a20307001c0040784c826600c10560401880c900e40d041c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 458214775 1250 458213525 458213527
    0x70f05010b1f0c150b0406030c1d01050a060815060a020d020f1605060a05190305070e0301110307030b041d03030115020609060106030c1b0c140301140a0509070e0705 73
    0xe07128500b4080c0c00c10301c0c2c0c5440b80700352070001d804400542586040c503006040d460f282d0001520348081500822a00c0802500c18000140d036032928079060b020901640750503848120340c400e81c0d21251000c0030704881e0020040944a4902042a0364000d000303005006071240d0385482c0241070300c40d03030000d261402c420f0740186149012504000d06240c1c40d61640340180c0c000f083c404d10005075000f202c2c420384400f00c0b24569a042c1250040e1b5651142056101804601889070300426800d540044c2c4282515154250314200c041c0806080b540ca0496501c0074400c18400700340c1041c0300350300c40e0f944104040d000140e40c1441d00e200c3e40c803800c00f0040c1018103a10002c0180701d104900c01e4006018403003400100700e81d042c900120f549804050207000304240d69141c4500c441d178407a45124100c07072a035030700c050b0201100e07040c894000210b90142c003410200d0a00491750301d080500c1f44024008410610100548400d00b04070007034800984442d01c80d1284440c042144007860303c9180c09060b01e51603503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 458216025 1250 458214775 458214791
    0x91703040b03070e040908180607020f10051b1506040207030f1d03060108060a0b01050412080d09060203090a03030c0512010306050603070302030616020615100c0c08030a0c05010b0a0b12090102070f0501 89
    0x40c88c00320f078001140c01a0b100344100707001601d038082d45480456013207440100c25403c000b000c96440c081c0d030b40210180300580c0c0201c1140c000104a175041c41644c4a801e8040355038100a000680c41840c01c0100016082c214400c04184918003c0e011000300c5011030070800e600c031000074540361080e000a20360350807507428000123002e5071140319200d0801b801c00c0382c03c01d460004403820303a462044004d4041d96000036050708004259014410301c540c010021902c9060402a05a440e1415941240840e1910703011545181c01041520050031a1141540281e0b0850f41c40741c0142c82c01425040d0107100301c47c07000c0300507641400018800e40221031a01701e00450b000009143c1800030381445203051710b0b40c0d190400c0ea16000b1001040c50003034184000e01c505149420750701b01d01194060b902d14040400e21144995000e441004441d00850007400141e09803020094102240c0c8502c206800d41045145c4950f0124100c2c2c0354030591000005080c000541c440031800c0c0350041e011103ca0b5910220 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 458217275 1250 458216025 458216047
    0xc0e030703061b03060e04060e16120201090f080309041112070206041e0c12140d111b030303061011060705030a0e0a0201020303060d240c091703040b03070e040908 72
    0x100c10841050304d0700340421860440e00c01450000908090940c03034840d2441082404104110103980d4081145000125611010380d8034800521804a0020318613000015800412012841c1075071000d2020b03610b42187c1070100801090101d10003240766006002c1c054408140186842c8640819006040645824031b400f05050f05d0408040f120490b01c04642400300303134000b0b820001e1b02e1418041050890071410014650144d098080d207107803140780c07071001c0125840440040c06500900c100d4840d20040d084800003c4044841150142e0081c00001e42c00e1905192000b401412070511147c40d0849010060402c039040f5954400f0800000c21b00c2034070300c528882c1d00d6095a50102901543e8950783c0002d489110141907540300341901c11000c028070116203400094000300000e404400103072540c200010340041040800802d2503d940041c03420403144403a0b640300700d0180950315182c1800842401504061300d003608001800c14444003684951140c41625030003041702903100c0c00c035002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 458218525 1250 458217275 458217311
    0x90b0102251a0a0f050f09220e0303062419090501110a0c05090a0b09010806040b0f01140105031e240402090105030a02030c19080703050709180c0e03070306 69
    0x64a41100001044a075801a91000010702c060504d46031483d40c0306149a00b001141c06001e00660b8082c400840024a59030b000c3d8403000d41000130b180c01d0150140c950f401c59102d002c202c44d80c9400002d0512004003031080d0403040007100440084081c2400910001e41041070744091004012aa80c0c250a200310340c1c00104046103481c0d48401010440170907541e004000c031451003210300a0682602240303000015410440782c080300030b80800015a51801d1706540da50b170a0381c098808204680100f0750690174000b16505840b003ca014081c100c000074011529130340004c04003c20062030001301a08041c5070341d80a80124035a01c0f600304407d0043d0000340426200240c0144a903204116041c440c0c1d8000382030305d03444114140d0060312a80e60905c508803074414014580c0000022120700d080107900240d102c0e000350a2660708205664410308141c40e9010b5901035210114520314250703a5800d50354000e8000e05030360b498100007145030318000c40e00c5d041c2c654000b2502c0c41e4817400c10440c0d800100d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 458219775 1250 458218525 458218559
    0xe0303072f1504030905060d09140c0918010b04090f021206060f0d020315040f0c0614070206090d0503270402040605043b010501030c0c0c090b010225 66
    0x240d40e80c4003044007203020380e551011010424880c0c80c0ca400201418000e104510081c003010f00301c0b030754800142e80400002c00000030201c885141c9040000c44403c3c0028052003070a0b006005605c0903102c0300b1606104a44500810b07007203648a900124407519240100c400561286100c45c1041d55030344100400621803a82c1e0039400e90000003005000d6403040c80c90100b4110694071020495220300100382000f00041088242843c02c03001c1c071042010001d05410000e0052102080381516408100e5aa05510000d2809600c1c06d000d440d026152180c0104803501c00140014081d40c0f0b282e4680781540c01005800003000d589900d4106101665030300c3d580c01e4201190110315003410b0040140003070180d40a25842803801d9105401003449096000b841e44410101c4080d4800e500001304060400074000d4600107414910848841c130b001d00c1c2140f082c01c1e4404100c3c5d0300c0c0c4e03041c4080380000304032070f401a031f0440c426407040140320307503180090728807000071540c18258080c1050f10700316008407a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 458221025 1250 458219775 458219837
    0x708040e1e06150706060803091207031101030515180907080f0706180b040f031505070c170f070506010321021c030608030a03050a1d070b0d0e030307 66
    0x4180031145581c4205105622031800c89001c6080d12864010445038010f140c1d00400c00c45c0341010200b20003100101800c1f004404441200c115122519080c3d180e001134400105444500d44841d43d0a600a400141e400001d20900400d80e0398078030b000a130b42070002e02c200e02001d50318000f4001d0940d000e01030440503014101c028008030003010b0b551580ca00003481404104803980200300c491a00c0d02d1081d900400c00d40442c01e4440352900050090501180f1080f41d2454030411403a00014150142c103200701c000c0d403510004400580c80d001c0600c2c3d10151017105030901086011540e83c00c1a015020060180009000da0f40c15441d00c2c080c40d5550030445004030302040603003000710741c0c0050810520880070300d044014044c0c6030019009092650002a124040451400c2cac64590680c4124890302e0317124414040300580720360b0320300900000e06104100f074200f210300f8041001c0c84d0004100d60448600e000900032a504034440c20360b0800e403801d800044800c4803a081145004401064503248 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 458222275 1250 458221025 458221051
    0x305090102090a05040905010608120a1d03100914030d0905060a02030402150a09030b01120b0a060b040605180409050a0507060f0c03030506010c0b0108010c320d0b03030708040e 78
    0xc6040002e811440904c6071a101d01d89640c0314100b00003003908000300500508045405a8039203056001441d0000d0003540d0006003940c45a0440d8801c07150410f42d261009800761406072029035101014000c003000a60300041038020300d8040708070800050990001e0800c001415002526119013042030142604088600600a00000d40d81c3c030890310f024007020040c0d4907501c800d40c2c40142e640424a50016010b44568800001c2d603040300400360450610854107180b10ba80c0e0031a00304100c481c1401a8110001d003800203200507809003004104140e07554440d40040300d0b007100014151440c200080340c1c1c1c0c1d04201d20700c40402c1010081c80300034120354208401c0405a00030001c0030511418000340c2010b440c0d9020981c1c03a4005c3c04050200c03508100054455a140d50441d4060b007141072070040011400d80039000c01140c80080c02410142e5082519010100d0030300401c038a4000d5000c0d4070600e0b030740301c0002c40c2c5540c080008012140c4207010a58131185002420314a10030002e08500da103940c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 458223525 1250 458222275 458222287
    0x80118020105161103070e0403020c01023c010504050307020a23090a200901020d0c05030f0c030d14100501081b0a0c0821060d0b0a1e05040606060305090102 69
    0x3070040c0a5407851945030100c25038041281c14182ca10504c118a9540c01d40902107002c100d40503007016451090340250201d89415008200482c1d40749075013071a2454110030000f00105039250090041150781c20f0132500d0160003a1080060308441c01030780d0842c0d01e544001005000c601b07140081e007005201d0702c040c503280e211018030622100c88156001c0c900c00c3c01400e000900d18002e6510480342105028403074941d0f22024008108154880290a405441b0389603070005c0c80c034401e415261409a0004c059801d241000e42c25814035005070a01c100c10740824004140b107208544a014840c0c1c403481410101400c01400c0009022541d03013000341008110300c10840c0d482c50406513580d400000300313042e96889034a05412035080e0802c1400400782840000c4143d1520107149015010380703940c00e8102115107981c01040024800c9040041102c01081c00103918201141d02220110f03920004100032920a83d042000b1110119000c031102992a0300911400783e00d4452151b0280b5100001c40c41c240c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 458224775 1250 458223525 458223527
    0x111501080313290f0412060b15071703150315041e08180a0504060e04020306010617070f180b0c060709050f040213030204050108100c03020901090e0a061701060801180201 75
    0x30503003c80e15001560005084821042c41001310340003810005220034441b402854004003074000803581a1084000300c1609600804100440b460b4980c0104060a00595403c44043c603070401407140410f88200c2100001549080c8080c41032520b04210b5004a8985482c0904c001108035005480203401c41401c1c10008010000b11010400c100c0040082d8100900014046461a400190b0010700342100000c200405007541030055100310191040d60782ca801c03045951103c1307400510501d0a211002c24080360044400c0f04a10401d85009405903070401c1e000510070ba1079a0000c49159800680c07000000c409100c41e5030401c03818604403081514050015049a969480040c07080c2c1d0300140c51041c000c3d108403c40003c55020300180000c2d80c3d500d0702c0a8030b607013981104001c06401c282c038807400603100748203c41b482003058481982060501403860b00c81100107090441141c0d0b43d00001c07403007103100c442c404d50350031a00002103461404c02c0700003400d5480080b00241d0704101c015580c4d00607 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 458226025 1250 458224775 458224829
    0x6120b040e24060109090f1e02040302031011070b070201091b0e10060206011401032909010e0f01060c03111e070501092102180c04050f09070f111501080313 69
    0x114203514010500000e001c1310b500090019044034080c40230001003103503032070496401810440340201c0544068400d0055900180c8458030728015240000700083e80000b15601003940d000f407214400001d0342d000595400c141c810203902260359440414404120b031b40113a200d240c1d4014008641d0f04c051070302e0000701035540c480600980d6016400714070b807140141d10a41c800003c810809102c0c4c41407504000c20b40d0f00052000b4800c50240c024000003081c0e9151030810b90b030041c0b90380780d000f4001da07181c085c0441d0200d960000481c00c000c0b80c010000910402000300384201400c0308400b03031071410750f4162030386000103580c8054188401104d040111210048094440360240d4140010f00b041c50b100180e00c96101111005000c03600c00c0c28040c000605902400590b1800d40d1101d200e2208481003042e0303580c00b281e0324800641c0341d03940f0020b0f01d0f201e0810300d10084180002c0300e440c005501080807007018240c20403203e070751011071124894000354040344024207082544030300b1044220419504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 458227275 1250 458226025 458226029
    0x303040602160503030c03062b20090c04060216030804050d021503150306070309020906100c05030d0c020106060512071d04061415040e15130212061504050a06120b040e24060109 78
    0x30840000c07054202b4100b413004100d100040c01003140d030592514126000b525045400380c034005100d44480004400060303000c0340b007680c0d0000d1005003014a07003010003d90300c0960780201c0e0400c0d03050b4484510200503a010394010070600c0c0c214012800340c40181458014014040c804140c04c104058026842e102e504039040041a1640099031000500c10b40b0742020001c0010590b00c40015824050002c81d4001c40003804584d000340141c6540c0d000854280c040c0030807a500d50003802012803151402180501c1c40d00180c50000c42c01c17201c802000030221030f140da00200015101d00303184421071401c8001c0303c0c11000081e011604150615118484003a4020035241c2422180860398215a403595144000c401200c4020f540e143c80b00c40d0780c0c0440102c00c0d1a110302802c0c0e08072901150174116015034048d550050710351100385180c45c0c0c0480310b10014000c500c00d61680c0d040d1280f242d03140da006010000410600800148c080c400c081d0314045186e00011040329203060501155a9001f140380303007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 458228525 1250 458227275 458227283
    0x60114040b03031b0618071d13080c07090f0908160302030903100912080106021f110301151209050a0204020c100603320303040602160503030c03062b 66
    0x1e080c4121400b0a00e1841109a4036100680d0400720103110540018520f1080c010006030101a00444440039a40e01450081a0030110306141c60301c0c808055520365030f0b00c54040740d07140a09241c25100c46210364000c855401035500214000c2c811048280185c40c0501c200c8182000700e4039941d00c1d0405a030050704410301c44d8850081d500401c0c13600c204141c504005004040c2c4900040e914080c80040400407011070301680030f01c1c01c251680c0c0c01280c1d03040c1200c01a801400c0d10b4104245503024404040d0041090f542e510401c5000300c06840e0f000c0e44c0a4203006003c2c3c54003c5032501c01408030403428140c0601c1d203040c50079820004501080e20b41980380c4c10750740562269a2070340d040b82004210410100d00078507002002052288070319089100d9011000d0304001e0866404140c2c0c000602613400840c00c1d030003000410005200c55004198070000321041c3c03a4039004541e01d41381198404d840e14114030801200380002d0785040c8503000500c18901c45002d203130400c3d481c07481c1d10200341c008002d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 458229775 1250 458228525 458228531
    0xc02030c1b010909020309031b0c01020607030b0102031c0209122808040305010e07030318120821070306060e01051c2a08040b0604180803070203090d050309040b0306011404 76
    0x148160f402040c502c0041c11003450b056440c0d1501602c00c994a41000803400400c20342040d40301801000801c0d000b6032070700c040c1e0182460340d9850a00380c02a000d9048210704501c0701304142c80e101140b219007032600010030300e00569901d540c10304002d4541e03010b42030314002e900b2100200031104142e0f5852919070030742c0710070300c00011240e080004c3c8902496002070159402e01c008013400c0c601c08605201038920030b0b1200074081c0410130420050300300794081c41420030115012000490a44405003c000d55048110001c06160708105c100b0020309882001c0403d072200c500380513542e045990b64101c42c0c42840c5c80760a08101d0310300d00514542140c9400000daa889251100c1051030107214009081d0030012400f600244001c02000d400c0b0450302610b1140c0480081010b07481c0901500707110702410640f90020141a1700d41c076490750b102528100640c4010040c00c4025207a020710941200d0080c2c020395254031380030303042c00309403808150f09621980200005102e2545003040613590070105907800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 458231025 1250 458229775 458229823
    0x8060115050f0a050d0f1107020609042a020f0a0c180f0204060e01030e0d02030403170d0c08090f0c03191502042705060303070308040320060a0c02030c 67
    0x10340e214031a00b445250b880c00006211040250094000c0c029401514410020024081801400c640351905283c41032141000400090718041002e0a4450f40040c40040d04840c40c0780b000c0e0504c0c400d0714505258000014074146900c1d0107000c0203840c00041009029010035995984014038418020484000d0414122140c01c000c21b0f031081840e4101864115a6903403035100142c118200c0384046030029091040c1111160804500b041001c44c064004500f45815560b8a80d523194041c8040c1d0841350080c1701001298401c0d000b085c9544400e5192010360307080c50211603082281c14a20f85e6400d07480b1004c03401c1c1907240003902518901042100e4003c0300701a01d0003070800061107016644140c0041b60221b1b81e042c4e4078490746041304494034a4561090801e420f482036400171290310303906800070b001100100c3e02980b000c5900074441d1a1180e00428420226000c400c504030f5075072540c2e0300580800c045a0883e2042d00c030040c003140015802e103200c9204056a0301d40b1515100015034021050b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 458232275 1250 458231025 458231027
    0x7031d0405040803100f030b060906010c06060605070b09190209270706110a050304050f0d120314090f07050d08090a030302010b040f0b09150109080a060b1908060115 73
    0x12810000000400a00040c206410b0405054200342c0d501d03040c41e1404600064842080002481103a40c8028105000d41c1c44004003e00c4c100010310701c40c14003001b014000d00007041403054101804c400e0712419220841820508044040103103288516070280e444100e00010542c80c601d40a5070486644a0598031101c80c100c01c021400d8000d5064208041c2a003040400820480140c0c0d00300e070348a840d003248010450f40c3c1c4050980000e0328070b130030810062000d801c0280c5600c880110250820181035120340c2c1c1d410380b440441c921200003a6451503000c10340c0b005054107582200302c0340c0c0100b01c0d55500e0700e241d9031510214460701d4461481819900d00704800c4030709444232828020001c403026640e905010b07010700050030741c492103145010a1444588442d10030620b1b030050190030744125039140100c0e05d040386038808100f41031000c0d200e00001c1c211000c1190055091280a010038110004000e211243c0d2840410498801401740284880840051854111162030613617058100e92854 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 458233525 1250 458232275 458232317
    0x90815060111010f09020f01021c050c070b0a02030a170709060e120f150a0203010f0315141f0e010b0a0503040c080a060e0c0301051b0906130f0608130203030703 71
    0x440c02c180d400e02840c5500003243e90702c512290781c0213403035081020000b240126203940e50303a11480109074842071002809407044e005050070b070080344200c401513900e4444201032500416501c03401a480080c4610056a00c011004102c00701b411454a007818003000190150b01140143e60404c0f42c034036001ca040355904100c03140c1c0900c041e0b09454204012500d40b40e20f0311580e640385050707001c0050108202020318400c9034100c481412810071024250307501d498a074a0b41c46e6603038410903140c02d2070401140c0b040245601507060301d08004108400340c00070706c045050704d52040d83e594072001e004018021102045031600c1d0303010315080c0e82da6039540c540010030845030780086510344100040401003081e039130303c1143c82003031190444400b003512008043c20b8550488008070090080c20001040c02151000340003080b9000f4419418410340c030340c50f103101c0802a40803000407031030300408005607a00101410f40105480400c3c81228589030082a07481c4500030005080010002e00d4942c1005404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 458234775 1250 458233525 458233547
    0xe0c13022206080610020a1109061201050f01290412051002040905060a08060411061b120a090501050310141531031a0a060f0b04080d0908150601 64
    0x84422044141c440b00010091101103410901901000040741041030000a07960140d42d0f2065034010404442801c0c1718840d4809040716401809016224056000030f006070352150885801c100c0e01c541c0740415000d00103a914440a101c0d0004450300d03900a000c05e011942543d001009820007046140303803040c0f170510030b130711483c04183c070210300421444210382000d0300400e411182e054151b9110312840d070300e8800030b4400a021205070f850041081c10600c010741800001b242a2449502c502041c1c1c0d401c041c040394803081d4506e80001c07080c00f5141c1040e402c4001d0b041c20f1905500b5440e00a000c001000000e02030b25400400b0714044808650302c400004040f00301c1c401400362542c151a410950407007200841030340000d1800c030050390030441c0b17801030400c44c0d030400059035881c8640790740c00012000c0641203444a94a500021528040c062400402002e101d0b80a9684a180c502503d0502803140400410408025020804c40c035000a0070382d040f00411007410240d0f146c0b440142c178002030340 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 458236025 1250 458234775 458234827
    0x90a0503030103080706050c091008063006070512010b1804020a050d0506030d0512091c0203190f0e010513031401090317040507030b040c03080f0901030e0c1302 71
    0xc0100b02c4200d000c2d0017458803440040c00182c42d002010210b9000304507105400c011064800780c919440750520a400440c042c00c460440307092404080c44540c202020580022072000d0240210001048107c1d030204d0285089814072645074004040080184614105020302040d0100a0720103903e20401066004208540c2d400341401c6c09411070b003141d2581c0d011ba41c43d1034002007450801013082c044d880b0742035031140e00c0e020071800c60b4540340c3c6c400703000807803a4418550140d8045465102c2d4200780d4240341c0084d5292601c0c04d0b10307aa0300d540c2c017234005410008015444003003580c05c000346484a034000d08046403501c14594110001e641c041d80007034900032540b09891040d12040d448929054007a9a404420282d00440e0381c1c84000309880041c150350200d241000411408807105030410700c203004403440076a4030340ba0010070741c01c403010228050000060740201c542c0c042c494980e41e0708041c40a054148001000941d20100040c500b001540c0c002030703009112406000b0710443c074455 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 458237275 1250 458236025 458236027
    0x60d080d050f01051c0209070302070f020a24090312030f0b04050c040609050303030609010306050c0c0a060507080105030f0604142514121f09080a0e0f04090812090a0503 75
    0x199564940e001c4c400c103809600c400040071002c100c0802c80c0e40400c0d4018040341d14980360b15101314000d501c4040f0540e0f4482d078020000b00142d031624039600c01050392040040c420007042c2c80801c507030541120454144400c0303490400c00102e421401403082c000350b00b40000e0521399040c090303015005188140e5485442c080810480320903c002420503101c0039540c01081c15210000d0555070702c0b064605640c0541d008004000045d0903400965001000404250a141c684541b0a18040900008849194840e0100045a50b10141190040c00c04a008103849002c443c41c45031586800f6102a01d903092007007203020a44010080145110407080c54000c8003410005485401201c03400b58810504941000000b02d00d84407070a4102c50340804003801c1c240700145810141840c1c0055500046032b110846c5d440807402c0032014010038070303403a02c5100300070b02c009080001440c42008400c0c821882c0403219000705000340c1c25562540c41d40034102806172610100c907031030704445030801801c902c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 458238525 1250 458237275 458237281
    0xb060d1404060c030204050a031e08070c1d010308090f0118090203010f0b07151a0909030d0f0e0c0f180126030a080a09060b03060c0702011701050108060d080d05 71
    0x594104064441c0c0d01400040100c225404000c50603031140381710303031030b030054803403809201080c0010482243e50302c40c0c1d0508603080c0e07000d54400c2100d8010030816540c44400440c10012412045c2035005207820813842005250704582d14072045e801411201f83c05030060380f03404080c81c0d01480350701c002c4c0038003808110080d50380c5800d0780c0040d600c02d00415a000c07101c0c1c0000640a040c0d1400d032021180d00169602c00030310208d4010009000446599004400e0381c080300d0081e4950301c0403140100190f0b40a16520f0100d031040c0010380f11031084039a003007031030510385580060f008142404820004c0798114004014100000e403558010500300d880d50190a0000a4203990045e244a00f24134031000c8103006001c14840c0c03504c03170140c0040480801c0204001035070800107039106081552280600060500301900402d00e0000100c3d842951140c00094860656030041190b80400741c00526400c204d40c10100000c240e0400a05404c0c0a00101103810b000c206400c4142c80500d0880d0f0810030482c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 458239775 1250 458238525 458238551
    0x30b0a03051e0f0c010206181006030303090b090601180e03040503030a020d020706111c030f0f0c022b080402060c0a0f1a151005040f0b040608060d03120b060d 70
    0x302c1804503400703901c58140801c029900104108140304c0c4160042d181c0c0795a0556036000082400600e44c146001d04034814a510200d4807450001d180a035030001038001107403402c241c0340400507201c81c603564020f00041003810342e5480300035448030220002140e01d00000c0d1059286000360782026905000102e01291465400603030b039190845154221440d59569500036242c84075000341c1d0410580080100d0801500c0403505d07808440260715000520855a80c01c4070204c031610072801524503207540e0101c5405904020140d01c2c207411102d21610015100919281201752425400901c601e900014065555103401d54000180280c150ba100f421145000d040004840400300e40d512046101c180310740394040e0b1010310072032490031400b140e03500d008200941c9248500c07003c0100310080202041400f0400e403103d0081050b001d60039210741c103100b00501125401011f0b01d006960000c0d105010990104d00307544420000000010070240c8a00821131510501040c41c83d840d081c0210040f0703203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 458241025 1250 458239775 458239813
    0x21020d0b01292d46050a03090f0503030f07030f0b0f04050a021c0203010509071718030c07170f0f030304060c0e180f24010509130c0914091006030b0a0305 68
    0x5541a10205607007222050404901c04c040324440c0001800030700091142c2e0b4000c4c0e20071189130f40a081440a0202180d584c44d00e1540200c650120f401484400d0254164050240e86440002610280010313040c24000c1030740b20141c2060b103486192190b020405100c510342c116800da03c0400a0350415020044102c0040c1d4030a21030305014811040028403194828100480d140c80e60f48001c0c0c20640300d08002041580900d4031090340c50004001e1242c0450302001079074000c022000c1a2240342034000241428442d04450302c0440380c005c8503800e82e40c4007000c01140c1e80310f98001000103040360300c01c03021100443d00030b422135007045410300c01d101c040d01f00810700fa00c11031690307480b402c660359000d0401541c8804480304007241d8a0b00541460300303600035000340411400191801c1c401141603410f110940303402c40c80341008503103900313414000f0184084024101100c195800401e42c00d0020308140c4028030b6214450805586407202e00403680e90502503c01140c000c011658140410000074101c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 458242275 1250 458241025 458241097
    0x1090516200a051506040203040f020402360109081204030308070507060c0e1c170f070605011202030730020310050705031008060121020d0b01292d 65
    0x44044c0e1080002c11900d814003c4074490350348a00960000c40700c6a0034880a074104004400b140e000c1051601e80c0c1c06c1092484c1c42d2001d6000140c9030814081e40000f4111b8601c0e90060007080e0000c50402d1070319603040f0111000c5a82c1403506000702d55481104890501400030010201420000c03007090740d55001409200300d40e02101d440d1484841020b16159074801003d00801031156103280307445028424000c0c1003445c29980440b41f8080503503495004481098100440303d04001100e041541010000780f00540110585079240c90800c0860000552071040d811110030401082c2c042107441c1400103c00350301a9032414403850804102c00381543d0001c1f6810561407c0c000c500182c02040018071074100c0d120400e400590020310450407611605c100000d070b8100070307074030b00740d00c000b516240c907050003030098680c403984800720806271350725400c103000c50104107402c06e0140396455810700074405540606460702c1000705000042d2618a402250365450414580003040c40551070b0078501849 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 458243525 1250 458242275 458242303
    0x603070f181a1003020307090b13060905030f03030f070e19150903031b060204080312040201030b09040b060f150a020601050319030903110a05041803020601090516200a05 75
    0x2120b81c02c26000020328425140480b980808055078000402c1d000703600a51704403d0910340240e0b81622042d07000ca240e44001021014030008450802c43c2c42d0307200e900710f0050f00045024080c1c0b14600301d107941c2d0b640006011400809480d50125250070301828610455803805407402c1ca04c030000020288807500c0318840c000020380d40c048548519442034464105580c1c1c1502c422092089204044100344040242150050b41c2080085101481000582460002e92a0170092880c0520006041d201240300c11401190054107200c0046c0b1490419030344140107441082d030081e12240003400015101c660641d145100250004403141d002c0742045c180c071010350450301e000d00c0050002c1901d031a00703030026000900500c000d00005894502800181000906110700c0035184c0c40041e04403400c040820f40500c1418041300205034061007100c0c0140b4150f5010041840c0c8a4a2040e47c03030f00005554082000203a021a02514500300c80d04203e00000300b209d4001c07000d0324005603203606c8144484 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 458244775 1250 458243525 458243531
    0xf0a0606050c2d07030c0911030103020a0e070e041a01090524030702070302090a090209090604230304170a0c150207090e0c041e0c02030301080c090603070f18 70
    0x8140207000e0022680b144003410000c056003400441070106110040816080921a400b140d220407041081010007030f501900c600e04c0354602e04026036048a0b0100700440507441c060004101599440310003170b08403031300d002c032010461f512841c04498400105c4c00c41c40c1d10514192008650403400e40502c42e03c40001e03220081015203030401c00c47d14904c0200700403200324482c094241ca140c20140615000440d40c01162261603ca900150305101e007103500e4204195202d510400358501515801d411144040140c0a00d0519031111038880030307508441d01c080b141036004a00d60100070000c0747c0c010034003201522580c03410700c140540c0361910264142d80c0041001c0300410304009140c520b40c2c07010750350303001041d071617140906000c0074000000e00702c4424080ca408421041c1c40300c0c024000504138a024020b040080d40040c070044804088650003194000d100612001d080010341641d08842280c500d03006a4901d0300091800003550001d0303044948039040020700074540743e044030302d01c00904014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 458246025 1250 458244775 458244779
    0xc04110409110f030403030914010c210b03250905010305030904050705270a0e070c03020f011401050d06020c0f0c030c101b06020408030c07050a0803090904120e090f0a06 75
    0x1c8068054070800c490072103c100086000a8081e500210806101d5041162500c4250840500311150f110040e004070b000c400c0105011207030f413090100396a9000000b0801089908003203560340d22503100b11080d040d0419611041d0000000f4460000d25440d0400e100704d68591030015143c5c0c0010610500440c146400300b900e50b0300403000d88140e82c607180341c0790741110400e5944481508507034603401e401230522a00407d000880108491090030700e0746950b20140f901e031070001e283c104814030b800c2540c0d1614401c3c0d00e040c0781482c906d904440d411218001040b2890401034001d100e41d190100032480b0380c8420501c0c181000c1540009240110b099030414007100081c4520000c140392448001810840b00141c1c40d41c00c1102c4503142402040700504058941410b6841c660104800c210709a20101080241d8509240054080e00350200510f0402502c200403c41101002c2d1005021a05010f0404607444c42583c1c1c0312040000140580e8007424807210040c240354040e2840c403541d50900c140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 458247275 1250 458246025 458246051
    0xc01080108100203040201140307031a0a0f14061201030b010e011a0301090f0b15042d2c0403032a1e0e030a030f080916050d050c04110409 61
    0x50281211104409090007245450b8420020f41c030041c0200d0600c410300c0c2d5200c1d40740551202843c0726407060f80340000c0c400c0c0820100e24145080f00040c0e4811240c0041c00d00c04e6429440240c4101c0e1600074640d4881600d080018005000343c1080c401d00c221584000428000d116503014100d55001220300c2d2583d0b00c0c0c44050740b06168214241000305010001005903c803141c1c4000003903860443c0c001110409400017503034260f0b41d501600789450011a092090150320000c180c4603c203450900800203880036810381d10401c09110303590030a0b02c24107610a0030103030040a15103001070b50704038074098641490003070002c10124143d8488821890140440300c0d41c4249030074a1480305840c1e400036482140c4441205000c1c10515000308002010f440d00e0a071010081c48480c81d2194540e070360406000040245503080041c8001c1c0303294090581c00410007100010710082e03403170a98000103904074506010303191200c0300828942051a141c40c01c05a01c90b060082e1007510300d4000c040c0181d41d02111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 458248525 1250 458247275 458247287
    0x3100f05060702091302040f020309100603110d0201210207030f050c060609100305120903010b0a120b0c04080327150405120708120a0201051803070b070e031006080c01 74
    0x911508007030100400340c05072a1481d9200e901c00200d00c1c0b18620f00071240e0114041c3d5960f5001c980c007140d000720501500d03030414000b1070341e00b0056980401c032441c03442e1510315024140b01c0c02c0354021030b8490215015640300b01451041102c03007082c03842c0c5501d4581c1c000d40081d031029509400041618001c46040741c8128215207800810f107000300295110706003040300b0302070302601c915000b008040d070010010ba4141300102c03031b941003001c1c403d407540004014542581c0c803041078284a420342d010706210b01c995484400d255250803090b100380366070700c400701250184529005242c861002055650000e075042011080105492100002da0314030704040c4803220b1501e548000c1701c4841400b052000c0e0904130034030040c0b20555411503450715540d030071b4542084150103c04000d0071002410800454090203040e070420101e4044084480500200645074050943c00924840340000400e91240c841c125041c0f82440c020305680c0d2000c2c607101803000610316489490030341e0207440194184c96000c1c038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 458249775 1250 458248525 458248529
    0x5070e092e0b0901031e060801020403060501170d08150a080c01032d020705010207020411040e0603150703051003120203040303020c030d02030a1214010f29160c0e0c03100f 76
    0x100382e85003400032a000541c00750030340320020704002100130702441460f407940c0515002841018001a1740c1e5080d0708142c425541d05070042d10720030000c2490705403010360000704540804818941013a02d0780311440d0701d40d440980e50750700582c04007500c036002c11b00a40106544594140903241007010b00c400c0310289050480181d801000b96007030101003804a8038580013400c0f000c2c46000010701e031007102c0e400141103544240816184220105040c0504905070450701d4000c00110024251201c0049134603541c884001d040e4010940c60340041380c103606910b407980018540c01613201d41c3c0b02c0350f100300003503698109110580c010711600510300c0c030504000c03070061349080310395010314036050030b84009907055880d40a0021401d03941e941340040c0e406135108840c0c041e080845101d02010301c2c240886454201110500b000e10441400c11100c003400807003150484c1090b42c41035006d0340a1828440103815003980920441e01061003000007904066001310f101fa40c01d04455079900d40c5441c0d400c401d0010324 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 458251025 1250 458249775 458249789
    0x1204180c0233100611010e120c0102090301110901021005100308030718030609020411120103060c050d050a050a0e07060f030b130e0c1011070905070e092e 68
    0x14540d1408048003444400342240540c40c0741000031030082c0e4514001210807540c00300ca00320300040034811164040f03165490340030244002d02640004900e110b84a204001c0d600c1040400040c080f0b000b64030a405941d60918001c000b04001000120081080d5000e1210381c3c0c0107001d24219090056281d202c0c1600a40c0440c1c40c2000b1325003169140c0580d940058818814404170221901c5000e4012032540f014500c510000305a075041d5105000a0350035060056100150030f212802c040c10000104504481c4c000f8404215000140800d0b00d075442081e9400030007600f80070402400c80d550341c1085000e80300c60b140c00c0201c4e41c02c0c6040d076921a030700d60140d4000200c0282d043d20080d4800d401210300103800030100703090900803448100458023040d4004019411a0041e4152407a00500007880c40c0c200d82041c82e00240700015a42e154203581c01400b10056444021900c124441d8040400010025020382d0f4642040b1451005440e6200b0400080d5160485452403075140d02d1040d200712812 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 458252275 1250 458251025 458251033
    0x50105100e10060e0f01032c0d030c021b011e1106060603090a0b0a060b0403050618010507051c110c060a0b1f030b2e0e06040f1203030b031204180c02 66
    0x11200401080c0f20400020a041584072352440301081000b810450180c0000020300743c581208040490801600ca50304c00c050501e46520240040d401140d60300745000110001e45403d40002d0050766604030b115041e10052681c0d0006a050540001c1d003842485444002c942c0156603000411009210480356207060b0342012005030009800040341c250404524580409d885d81c455110a0081e00076500075903856226000b480104482100d00344001403143c0000e00c03103031809a40c040c00e43c0c8580c14190100c481251220151a00076070b02c00320405908035030403607650740180c403965580c22007a40c004c42c6051071700540c04018984201a004401a000c0041c011291710031400d6000781000200750380c2250035100307859040310030b002c1340f1100d00103d600304024142490b07800074890b80c0131040762401500c04000500c400d070713490600b98080740c00003403040c03004482500d0300300c002d491090710040d01841890a40200103e07900b018200369078002d07100344182c10f44028000d041d41c0c020403084000da00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 458253525 1250 458252275 458252297
    0xb0a09080c03120c0c18060108060904020109050d080906041e0816050d0f02100f14040e04060e21090f010302090f152203030806090408040603021303050105100e1006 73
    0xf040c034041c00030400901c00fa10204080080881c03220b100490444030b0b595003000030030915682248030903400c541e064175101100c0c07500303074000303408810709000d140d20820700134691104000c06441120540f0340040e00458030385a40b909000f405058800c1c04001e50300b00c0700404203641400007128420b000105050841c403620303000c05c1c0148010b01000641d41e5801c410740d41400b5880f001001a4800500c1d950f0001850719020010160307100301071440001c00b4204030401c0301484001102d41c010780c0040001901007210a165841e103400207201c204104507522960034032105d050302038401844c0c242d07042030b25843c20302c0c0110200c0c402e2070320883e400325248400003654107042c080c2017034100e10110004d142200c5524506040105006115000350000700107108040d4450112900070700240e5019065052075900c01d105402180204820564041070f1080c0350008001c11000841c2c00000030019402d00c400d070540c0c02100c40c000e0264200c0e628001ca01c0c00b16066030460100d81e1035581e40781b9a20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 458254775 1250 458253525 458253553
    0x8100e0d0e0d03030902060a200c0315070903120504080601050108090d0c110409140c100c0303090201090f170c0f1e060702090f1f031a0915010b0a09080c03 69
    0x20059002c02d07400c060380d601d44040142c8408000b03104005807903d40d01c05131203915030305039140828040080e48035002038111038100c0d140040e48000c0e44941c00c90001c010b03607640c40102ca02c4022a800542240c00d07440101d0703482c4da0004020020f446031340f0192a590780e04d0b00010b6403902c0040e103c2c1c16207503220701c4148440c0381c420141140c0b598866443c2141c144802d40001e0282d50702d40b4410b46540d20202801050030004102e40c401c174010a0302c0d000b0100040340350250901010410140c02e0589a1305c08500310780c482c1c200400a0180c42c1c10139600b140c1c1300c01d18151000050301c05148a07101e681d41c000c1c060b00d880e03a0100485c2e0401003016801c01d2900da6110035000b00b860906030400d400b0301030100140d84411b400c6105d800074100202a41c41c06884001c0109640e007400441840d180c0824004141c00e0846828180e0300f8040440d03040d01ca062420740303070003018007010041070180c1001003820320700d100050400c00c0b6580c0e02d2009080d02c3c0c948054842d40c24150295240d841002445110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 458256025 1250 458254775 458254789
    0x10206040b011502120d0f050f0103030c140709050a05060415081b12030f030702070b0408060c0f09030109060c09080f1510090c0903021c050a080c030c0708100e0d0e 73
    0x2034180f91040d60b074140320072030601030381c1c3c0c1051045030046c2e9150001007116003043d1041c1c07540314250210009840d40341d5100a400c0030310389040a0282d50944414240503c01044000c0c014005004104060300d491002c0e0301c014502602e24603c100e09242c0b1030095404079980311340c04e07654060302918035044c41c4050100080e0515038015040000701413407070009030003030015006004c04005900d0b034a2801c81c03402402c14505400c8440c0580040c80280038001c4000340312640401181d0302140c0d02c0900c09020050780c01000c11030350349982468058401c12240b41c000c1c0d00e003030445856240c1860f499190355030b180d0201019040c00380e4004100c0280c0701d000060455008550307203801c2103000d80c0340d062400990350301e104490080354140c0320405c1141052580c4014803000180c010800d20003e95600d61613400e08800505400d030041000041c0d440c0074002c030b51440d00c4210403214166a0303991081d03190500000e40c000d26902d841445c068030b40010503c8510085035a0710b0110420702c2d10200582 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 458257275 1250 458256025 458256059
    0x3060406080604050105090706050a14070602091e040e030906030a09030509030d0207050f01030c0f081005190305060708060a270f021b010606050f031b27010206040b01 74
    0x401034481000040d81c0400380116800b0794069400490203140031010140f800742503038030400c02c000d000c01504408591108100260b0898802c00741d40d0f400c168144a0b003c5d00400008a03400341c4490360321900c1110842d18280c10803420740d401d100101185c800359840340151912650000d001b04001040204254850300b04103101c0d040003820f0042c1c06010910303200d9142102c001691003444144014a071040c01c10314654800d1074180614043d0102c006c203a0390700040c040301441205404981c0c045000040c01d005400c01800e10804c02c0901103074500c810f00380c1e100c240c6443c012480881c84403407044040c240b1402d0090151341d1841d18142c01c286520302c8003600c64001d06140d08801610011500562601031002540540c88d180d00080d021580100300014102c3c0c0e0b8545401009441d8000050f05c00c024048036060362250340b0311070310688030b418000c481074585000060300081045110032640c260468001c16074500c150030401a45c0e5210240ca0241400c101c28004120720f200e0284a615 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 458258525 1250 458257275 458257279
    0x30909060321070804080307080d060b07170a091a0d1404020901050d05012403230c011d04020a090609140102190515090601080d0e100f020f060c031902090f060306 72
    0x224246d512003601d41150000c800448140e28005078012181c102c40c05444e018007008203882d0b07e44061942c0f4a204241940618500000c1c081145010309005916080091592030701d020344000741c0450150441e40050300707210510789488000e080c401240e41a946c45294040c00c1c0348456400c04c1c04008403030f40a800200c50a41d2100c80b00b040480c000c1d001c041c0d26501d0705001c1e00406081d442c111148611b80c0e1000c0c9c8000d000c500c4840b0705a00c00165440c5800000e081164001c0003e0181d800f00401031200160410f0000a5104000b40c3c85800310f01114010b035030743c4840795128400e00c1d02904500344002c0c010703802203095080d40c1c3c002d01805002c0794071410444070310302902c0182d2614500111242c0078140c01035401008048401e000505480d080d43c6440c02d001c404000004500c0300b841c02d075003070401c00c600bc17070000007074020890125a0484031088410718035100c126a00c10340d0044582d102300b0628101e00803e802018001d43e24502d4000340f605200340201401d0240d0340d000204116 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 458259775 1250 458258525 458258527
    0x32702031506031e0a020f03010507120c183f03030f1e050601120b0307140a0e150a05060a0804020d0602130810180302120c0309060c0309090603210708 67
    0x40044016200300800c150702d0b00c0909002c5c1258010410308102d0542414040c1e41840708101005600111150326a04006800030303040c02c01c034000300c9030b00307a81c00c0b140d0039421103101000c0740d84442d1035452041c01880017409981021080e0001c8605552035240e058020075116501c0006070107608074041750a01c5600001d4082071045200003100240c40000d59241da6407003e004440d41e111200744c080d03002c490000e110042c00100403e981e00b41c00d22030404074140700c0c2d00c42403143c5d071056007400041c40c0360b04441d28141011044012800c0e000c0b500c00c0d1142c5401d840024103801c0100c10340d40e824040f41c99440340355540da024482c04030005001203ea2550030440c01d220118000340b0784000c2d001c100c0c0200405021070101804444080480c4540304036641b030900000385c1d00140c540c1c86400030300003140c1c81d424410003081c030f503000d99086598800c0c00400c40c0c004404000010b0100740070115810000e544801c01850b403518904100c602207503c14128100710012050000c112052103406c1c89 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 458261025 1250 458259775 458259793
    0x304030b130c060f020c060408030a14090925020715032003090109030314010f0302010507060e12092403060616020d08030906091513050a020a030303270203150603 72
    0x2084021001d500281c0219081c1c0b0407804c01c1d20340c104411440d15a003990311920b890300b050b4a9030361b0390194000503010810100000340314020054140c941c0303024042c0c400103440c104265404000040100542500203000c038920f001188009890022113641901e468010310400e84210054440030b030103207448520b621503480101e40c80c00300441c8200002c40c00000c402010b890018140c034160511109041030580051000440590901088981c2401c0c110f95429440c40c0100140071021000b4886021700d01891401300542c8000342444c21040362030b284500d6030102038201070700384446159030030201400099a5424840f00030200c1c1109143e07158801d0400341d001030006500780000720b4800c0408410f016034500100401600159014003911007003140300c94901712080000c0c070f50194510480c84803401d1000921070a0006070700070f004002120b8913810050060402c0c020b084407018444000d0841c2402c0c81d01d00040d455034018003a02054251132440e401c1000d01810b50395040c00381c2d82390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 458262275 1250 458261025 458261033
    0x12020d09170a05120a09080705031917040311090708070806011b1b290306010c0602120f100f080709090516060e040b0105090d0b0a06051c0c05010c0201020304030b13 73
    0x500c180c001d1224983e101702007070f401010740c1c0090b8006030382980301d21401d0205540100d8021020440d0524040e44080213041070081c800194910744520f050000d00481445842c0a00000001c0c0941d40300201e0b4031802001c54000d181140e501000809a0000c10a25131142c1d0080200c062400304203a02d200090701e8150034000c202680654000142c1d00402c020b40c10034041c000511000b1003a0700b8104008049680b01c0d100c000c0001d8100a884140c034010404241d0594000134550700c84440a454010300c0d03800042007d49204050b00c2403403c0025452800729400420342d4402d50180161629000c40000070304401e00c0100d80c14050310313801c0d1038480810100140100100d6845119401e2058240011540d054041d9410010104041d03205600d1781c200c00c0e40030a600c09500481603035180701d030030300500c102d411640d4001103840c04c6e4094551084d041140c1180540342103034840303070f50b84019900096080c100a000d1382050104001103103440c10940d91140c2000550034403a80c407a61 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 458263525 1250 458262275 458262283
    0x30612010b2805010c0b010603050907030b0f1806010602070302130b10080f07030c0f05071b0b130b0301081213030206040b030f060a050109090c03021606050412020d09170a05 77
    0x80d68542e0441c0320745000c010b146031410b80c0040c8005c0c203000d01d51611079118490300c40c13014002c00e41496103d81c0460f10f143c10800110000310741011180ca0b0608044240900d0103c0a8611005c0d950320401544450100130a0647c100c540e02e4009022561455091150328903020a00e10440c0e03036145146c54042d220150141414240c0340e603401040d15010300c00668046000e451081050700e003d24500715282c1029a980207843c20f03003001a00c5405d80d160003801e0507440c80b2180018000210b0014941c010080a8a03114020b003025100b9103440f801e1041890100b44034900060b400707403101c042c124000b58000d04901c4080c04042080b50b8032a000f140c00e562199210050b030700800401c014400c482e00505030b401110413100c0a0150346054002030059035103019951302181d0b981c10050043c2c0c02075040b0340c03040e4000d1420000c0701c031803802c04000070007040f0b4081d140102e0a4448030211840810510703007400060300d0310312900d030a000d04054401e410b600380351654400c0e02c1c98180401e500704 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 458264775 1250 458263525 458263549
    0xb0d020a0305010501061b0321090c0603051608040f0803040c080d020d03060e04050a03081509011205010b030a0305040b1b0f0105040204060b0f0714030403200301150803030612010b 80
    0x40000300d455403503c80010b00c02400c48400c200178031f07550890340c00029808219070562030411400e03a5102e14820a64030001e00b404c040013050090500b80004c0c00d140c0580009200311208841040c184480e4582600c002c076049400500700302007049130381c00148415029540041c002c0b80a07100d0541c9400c00f007842c102e101852070700540e200f41802c80f00c0a0b130602404016013040303a00132a86041680d610755850450610003010700400c0d100181c007030b19425072400c01c0d03105d008115083c51350751140b1031a5800c3d41c6900c296629401c2c145034070111700300018102c1c100780d4123940f800c0c51700b46002c5400c4d03041e40100c182d904200843c40444050580208007820b51078071342100000b118241441040102ca080380d00070401c00c54240111148403012109652400c1d4000010842c240c8182c03107110304501c110b81000301801603003940001402c0504034104e01d03122040d402005141003026080b00905460b2080400c107a104000190700c9051090038100340c49007031400410b888542500040c2000408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 458266025 1250 458264775 458264783
    0x60301031506090b010203090d060e0111090405010602010b0d03050a031415040b03011a0d1109070c0302101505010c03020c090c07150218281d07020d02100b0d020a03 73
    0x9042100c03a6074050700c0707a40014654001e04201c504034800020703489000e00508984246440304c00f03402840107907005410416007460003000003020034019104160004080b180c011890f250011980c0e50051264081c2440010714411301042c45580c200c44a0340f00700c404e00201034481030450344415040f801c1c540107142440201d140c0780b00b0082404102c41c425005988240e04000c0820103418900901250400d000c1d240788100801d11b0034400c450451410005800048060400070516405064414400c2c804d5080d03031400305142511500759020390300f00b03041d14107203003d003000103600032030302038405501c03078010350310300c08451000140741d010101e48442180f0400114032080225543c0d80340302e19600b0010450030300002c40d904400442c60305403094000d900b2002c00311001c034140c1c080d880000848003800c4601e26200c521140142c440b603101c0d006072002140124222900108185d2000b080d40e03030040000c6044145d1540162a11068450300320601c25a15800741c2c036141e110764051401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 458267275 1250 458266025 458266043
    0x115030201020c090f0a02090d02060d0b100306050906060a031b09151b020d14030c0c09151e150d051b040333020c010b01090b040803090d1106030103 66
    0x514000641805110340c100380c07042e01500c003080031540c030005080703406c076210000c016244c04036030010036104500303114080c0d4810313800b1408107002c1c61982c00c0010884010703164084d1860621000b42c0998000380207690b4000049800a490303814081d024000b100000c0c81c000c180004410304250711807012208100006582100c144141c2602e810084101c030307054a44a4240214800f000c0a20321200000038410a8900740900900c016030b6003031b4a001c1d440c2c0e802d9035a06d565800b01c09544042c0340d08064069000040000c901364030140384000039400203465200d40c5160b1083c040f4100072441c21403503100391458542d40d14a07000070050481c2074404240082c0508005404141480541a2418900074100028000904040c0042c8900080100c1300c0500044804442900d0f5012a0b10007011510101e000002c42c40150402416080d00781c0b280803020b0788404911250344941e001d00c11140d44100038021340d6040881401130381d1400341d858060400e20050000d01194001e80c01a18400c03c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 458268525 1250 458267275 458267279
    0x403020a0b010b0c1009030207031a040b011403030a03050a270b0105151801030b040e030d0506060c15060d050109030f020c0f090109020928061e02070e09030c0115 72
    0x5070700081c68050008148001d04181d0b441c49590740c1c4002c84c8070f0466049440b4500041098000c0125002541e8030130403102d0100480c6031584006030301103e085e50704200501c00050048208800d8455800010307010f5403400c96a03110075009000c000d485104201d650740f5006841a16400941849000400d5044c0e8410500d0800034002101a00411b00c60b2a003030001c0c0d08885645400c0341e1038090000144900c1540140040e0020300c01c0d400001e4003c0e0504000d04d07240500840201110241840300300f2a6450309030500ca00c9000c2d001585d22260f020a8a5082a4a03060411a071144c4020150181003805a07901402c0d9510028100c000c1160810310505442d0144a2a418103000365000030307000501c4000038406040620402c0480e513030000320850945c90303100c046200310401c0c42e056000000c00031131600b4121032078403c03180012130710035035184540f84d440c80b405484030440d03000304032483c2040410481003002070503c9c412071004006d07841d040340083c050008102070840640700c182e4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 458269775 1250 458268525 458268533
    0x80a02090f070203090d0305040506132306031f03170306030f03120c030910141f08060406020c1c0c030909020703021b030a02060304060c03110f070602070c0302090403020a 76
    0xc0c001a0030900c40245410070048541d6000060f540741c003004603510341e0542ca45080580c1c661080340c02450b000380c80012101d40c07011201d40303103008480360695841c02c1c0510000c02c00005103c0800380b140d021804001040b83c40c0b041d0714118400284100310000620750f40e640704e069015280c140c9006400b070200800c8081e15061103001e100104c40c0015528020101d41007010b1360354003c01c0c1d03074103101010004c10360340d04040040301041c4001c1d040801407142454a480c842541c116200303c02596410551780fa00e5100100840844481074000c054070703121666200c010f074002045803400e074421103a14400c541c220700041c0c0a1102643c0b2040c41c15020341c1001000c0c00050f400c0742404500403c460b5001990004407210010364107520352a1541c40e91001905210094402950284000c0203010500c17070a07a02c030b002c60720b0041c1c9040140c210845805044d601403002e0305103200905000b2030f400701d24a03400420310240701d11140501c840d100d90008400785002c1c0c0742030b401039015103030200c100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 458271025 1250 458269775 458269789
    0xb07060609110307050f03040f1e05100209031b041119021b030a0b07140a050c06070c080a1d0406080a0506151e0301150e1603020306090c090f0307080a02 68
    0xc0b449103614a10300d0007000c0a092440341e200102180080000050180082c6048554045912aa900484505e03060051161854948080e41c05010341404c030140c44510780f003140c4403401c010b00034182c6189511114281d040b10755060030341068842c1e030b812450025040c010015514000e2952070000003011009252810002d0b01c0420b81180c0d4424104594000540e810010b501c407200030403a1392540b0b1308640d620306503d40c1401c1d10801080241c4210307000000750034055540340488440d82d030782c443c01300c40c0b07103010000c0606041000c0240c140803503c9000b06802500ca4078811800045c04580440c040b50b450303034484a0940c01542100080060520072076801c00340229107025610172500c005050f03c0c0700118045000000c1c880c1b0b06001c2d8800303403c80074000c00e0b9100c000031590383e01c6d50361150580c02250000720701324141e05949030070760007803081c2c80c007448020f843c1502d0ba1b602d405480c0300650250800c60342c0207280c081c01036100d80c0c2c1000004068040032002d0049140c1602c1403043c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 458272275 1250 458271025 458271041
    0x312070606081b0603070e1504060201050603060714030a06080a0b060f01031b110f06070905030d090f0603090311010c120e061e0423060106140909150a0b07060609 72
    0x2d182c000e0a2100828801c888540401240490320b1503070300d0305e03124815030b580f100d1a450290022641e80750100700403480c0c0e011b081160300a4000340025560101059101c0604460410101d004580c22000a225244c0034552041c0288c00005003141c83d4080c075458888080e9088a03488880d5040000300c1c2032591001400e0002824240540200030a040d080c40c1c5c00803040d84200120031700c071201440c1041140e0018070080d0002c0c1c03001420020b200138080c48541c01441c0c00f0740704183c03400710014801e0340c0e07040440300464000b40c2583d040076005c134007400c0349440980030004030100800c4856800c0c85401081078141d11a0f605000b8010720740c0060383d050428880c0281c212104128a1058200300c2002c40c3c50032004002d0f0a40d41d518082d10700f190400401c00074400600340420901da0000b45150588010f40c480c2c40e000c42c01480800403602c15584c40c503801600940c0412000849d198060300b1181c40244000c240b02c0e101c04a0001c641c00c105403d846e002d46030001003001400724459803103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 458273381 1106 458272275 458272289
    0xf0c200102100e0f07081f090c090c230901090b0f27031b1c05011d0102090a09050403080426040e0a0501050109120f060b0312070606 59
    0x244c0d0311301500402c51507100f604404540c003c40010310116030070f28140054499028881400050158454101e80310f0011010210f1030705980d0180081001c856580c01210711444072081c250b00b0b0110380c0320305441f8800c11054010340d0b07000143c00c05641000200035983e48080c500d01c0d02c10320490800c200e10040001c501081e09281410044140b4011400c030ba4150614810100140440341e4007264800740400f190030355240b520310400180c0c0d0040b000000c0c040301400d0010030b020300d043d158415076540080e07410030030b2034030791141400780c802040100b2040c546a0380141c141d42c406040980140200c543d01803507040c4003003034202c5c21022080070540f1542c0e02c10000c0c074150400d4500c08481804c0600124465202d1800c090403180e51078007178400808107460700301070080c81600c00d880c4e198a9031000256610204202244109510603150b9201c41d076091910440f446600008 = true := by decide +kernel

theorem cover : BRFrame.Cov 458093525 458273381 := by
  have h0 := BRFrame.cov_init 458093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 458093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 458093525 ≤ n) (h2 : n < 458273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
