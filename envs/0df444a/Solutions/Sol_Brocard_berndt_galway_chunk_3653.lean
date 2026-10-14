-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3653
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:17:34.880402+00:00
-- url     : https://prove2.me/submissions/10e83dea-db8c-4e90-ad38-6c4320269d17

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 656834532 ≤ n < 657014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 656835782 1250 656834532 656834537
    0x10501050109150f0e12030d050a050c030a05190c030b01020f120d0911060301060f09080d360b0703090816120327051903110d06110406020a05070e01060c12 69
    0x1c004240d40b10300f0001c074801d0010200071239440b1540c105200840c0d80040c9500d50f2140b07008240b0140c4541041201d41054440310042011384a51680c04481460b0f200031001d1546030001c15004980c040d08281c4107428240c0076502c0d40d404030440c3d0351b25103458641e07001c154541084031650005e029402294501e00641c2e40b18070b40d401a8010039550b501c01e80200d000300d90040c2c0d0340c04c0d4459201402c5000383c0301c180c0144c4000d1041590251040044a4403e00141520508200740c0c501d4410581d201c005540000140e00d0b540f1048201d003948a004181c00140c01000701092030b001c001810969001018030360200c0038946004d04608840a0f01d04504020460580c841c05100041c000646111084807040225241404004801890015840000034040404c201191401c0100744135030405686400341030310380e0b1034400000d0007a850100044070000c42c0103d000c81e80002c2082a01e403151044401083d2184081d600d0075400b441120300048510001100095041c0d042c07081100150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 656837032 1250 656835782 656835797
    0xc0e041a04570f080606130606020a02010807030905060705090102100608060f0c070606090f140403021e030d05010b0307030c020f030904020d0209040203130b070c110f0303041a0705010501050109150f 88
    0xf000c8090856590754800401940010148000d5113001d403440f101c00e14281c90300304843e6151180182d100c110788007020b81444041c00000d10800d000e6000146181c1d4400c09a81c100e15120b0005055a0070000d04580140f140c4840340e52146c0c8544102020303107641d1300051404fc3d81e10038009240138002050b400c150301c408e01c0384800061080c0503440c00f500602202080701028140d83c001240d498406112140907000c0038030010039000b00d05580c4840013400c1d10050200a00c664503d03501c40e411015864900e00800011130022201c080c40c001d102540e41841000c24410049941d0300039209422184d400800c844800c0d458681d00600420400c40c00150824031008006030498108440b142480d002d40700d014401c2041e40000d66501c580141001c03689010070340c985540c1418480e603410300610005a2039240d80c1ea041003510001e01401044103040c00c400751115100b03406c00c8401b1185982003100100d860341c013601411f1300b50351b01c20300205c0103c5000417085510480550b580030510124 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 656838282 1250 656837032 656837039
    0xc1803021c050303070804171c0506040e2a030a050303070e0a093909120c030210120c030b15030703060b0f040608060a030c0e041a0457 60
    0x3d01c00f079032095000780c407101d9503464507042c40c800810211181c03100154040004180c088a02e9200e00e103036803103203c0c0020700c4c0ea40b500d020400408001940c009a403144480100c0d81c26400f40001200b4210318a60001c07800c0307030509042e070345c44900310b006010350410f000042c0b0f001d10900f120405540c008103003400b034030780c4c0e0900207045802d500e6012881c01e2140052031458911109000900c2d00e49010f805006109004010440c0070140a0706048110042807001880356100720708001d5074004140707072003651800e80040c0c503032103084074225a45800c005500151a0291103217080035400070301950050400052901170b40d60008241d0024182d032410003050544000001d00800d0300c410816607511070500b00301418501d4020401449801c00b4981480042c0300c16186404840b801800d21009803030b0ba10340003030840c1448401c40085001c4004002c2400b450040240842c3c0114135100310122070310050320038110310304540914085119000c40b20301210044030a481c04815a01d0251554a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 656839532 1250 656838282 656838293
    0x609060204170c01020a030f0c02030f0f2a0d0f150e010b18012414220b030f0f060301091b050103060503071505090609120703060c1803021c 62
    0x8141c0056142d90204003480c240e50310100140d01c5010001d0005249402142e500102500b800c8103105081008200c042821500d080014000c05050401a80c02c0c0f5808c01100f207659a40c42ca408a5203410507116881d80024903c1d61a6a0007030042c0116000d4003582d1121000703800104c07000c842d100c08038004085e14400741c2c410907a46104940000c1180c2c00040104403d0210704204151441c443c80c0041007003134039039403208240e24840304070310341b200780811030580b1454440034411500341c00018542000300348800320b151085607101180300c50715071901101d040e02d0000305c424285c03100440000c1583c41e1180c0480580c8a01d00500200c2d044101e907490340720280b905c110700d0841c02c150580501c802e41e01070003020003400d0107030300a003155450700200d03100100b0301c28080024464000b0303000c00d03107031112411074480303074000b401c4074003d401e007880c4182c0c1e24600340c80251181e82c5003401a0000303900c111b100e55406583e890302042c090341541c08001803401c91010f044181d04004018900190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 656840782 1250 656839532 656839537
    0x71209030c0f061e060506030420120d02010516020c0d050705210601050409051005061c080c0f070b0a05180a08070603061202102006010b0904060b040e04020d06090602 74
    0x501c5020040340c040b1074413641120b0a000041d1213039500b400c01d0ba0500090f200d0406481d4010f42212540e104284042450a0390807000b0001e107420503100c440c004005000041d1900903c52640d0003040340fa521070403200d4400201100080060700100038503152031500b082c03001003a501403003d03101250f40d0751001450006101c00ca941c02c0c4214a054550300c91010301c5440e00600c015101440000c031143d1703607241c482c44009007181d140340c0e640020070f260380c0b14044c090074000c04e022291688451581820031158200c034180006034850106a0710042d0b0001c1618000c4800a0160500341140501d00781d4003900480c1e6030440135501c4540a5401c5d80d142a400d100504404010303260150600b00c0041c2503c40395045080024292154000140c440141081c0501d02030310b0544c0840f2030066084408131010703460521503101c1c80d000858101c818030000c0c890940308880c03c01a580c0c1c0ca0160086600540c8940c04400d41a40d00088c00b5051410800c00c2d800d00c43c0c040061821000e0780c0d41030884c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 656842032 1250 656840782 656840813
    0x190b0301060e0102010e070302010c0311033006031609021b03160c060f080c25080903150408030a0b1c05030301030b01050609030a080903191a0f071209030c 69
    0x603102c08038681681d40c080c4522541030300300c100a000382c00e083d500040d040d02c5002c8001030400408285042100c1c0c024000d550020703d41d40700100e00034003030840c0c06000a1a0560490305c007083c08002c5100342c41c0002c3c00e070560300002200048914079004a02000350001005050010907888110143e00414401041204807050b652168500681045a4003002c3c1e0340080d000c4c03050204549501581200740c4907805442c140e001a030300c20105015500410b10755406148030082c00c6146010004803401611000c40149c044070210912101c1440882d041550003a00c840000c10100da680207180d0080c054800b400390107182941380722812807500c00c444103015030780b50300048018000c11050410040c0141b8089810f24201644400003c8d2550b160350402044c495000641c0c007050b45007403041d020441c40900c0070040c4003d1501b0a180b00c41144802d1040d4a01220000b0f050240284010b070300518103644c6006501e0040302009004102d12001502032060440e500700006101400c02d2000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 656843282 1250 656842032 656842037
    0x15150801110d0507020d05030417120f041e02180411100504150903051902190b04030c05180a0b0d14010b0310110a200106120b061e190b030106 63
    0x1c1d00b005800190031100007502c0c603402c640284680f81ca444d9401401e0b29046908001c42c002e0084803202040004d1180e440580341c40c408403c10481703840e461482d00d503c0b4038041c0d00410404860400406031300c8907042170003540110b010400c0b2200c9400075401d1540a4030800d0001000301c4d0100c0000e21240c500c40c2c1c40780008000080c188148031b90000d03881200401410000812415607031465140e80703902d02401e5214030816030440556542200043c144c0001c88030341000c00c4d45030703400500903a00c90300042e2030006011000042c3c9007015501c14450a4400304840565180c0c5050000507005980304140c0c84024522043c000c5403802001e41054500e6000000719500854141800c00251310300341240140f0380004401c229644030101e80e000f901354a880a124841c0500c002ca400c03502c0710800500e58a00400481c0c409400ea6010382130600940d41c11405a03119401c0204129100d06055002602a040c400355410a814a40010840311b0700301d00c080d54032008240b0b803e4000343d000200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 656844532 1250 656843282 656843287
    0xf181801030503070c0911030402100e060a09090b09040308130609060f1b080421090911031009200a030e1b011205011d0c12090714040203041515080111 67
    0x100300f41a110440101b0340345a0611140e40344a1811006010084c400383c09417444240000280303204909601031442c000300303480c0d03c490f44203400800a5510b40031b42000140f501c011610285441100a84500d5159540e2402551841d42d043c28801c103400086034996190380031100081d1081c040c260340e01c081d00e040003e51040700da500040090f010340c0400103000006c4140804508030003414040d032403662640d8002804289802c4403140f840d0351222048134600301000401840007c021070181c280d04e06401202515040240100c0b004d0021000e009100810b81103086546400035007000c000c2c6050014404e1080c800880c1020000072003a2444a0031510b0102e4668100924841d882c080407000c00aa6051499102ca5100c0c0c0140030b001c0f0002c0da00000d201207080c0c0d81152030000e10148819424101108600e0340d401080c040c0d448203200f0299582507d00b440c0c0300760b030f01c0b941c0c012285a020100e0509607000800442c181c1d190101100080440c046a01340240d03450303401080711040c4d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 656845782 1250 656844532 656844547
    0x60f1009080d03021806070f0206031b07050105040c0b03090a030f14120901420803132402210c011d0c030a0507030b0604151403010c050f181801030503 67
    0x5da0301e031a07504980c0c419041400354401151928029081e41607054440d0340c2e0b607448068503030180318080082c0011031840018131208100043d004640550b00c9500ca460700c940d00d481d0351010740d00049444032142c1d80101d1100020910030b460107004010541801d4503030503c0104e010105034040200f2585c2001c0181c18000e500800b40329014040e02c4a41e000100c0c0074a00c00000802c01e11441884445494a0710030b4504440d9183e255009102c80c00841c2e5540d05072402c40702c9200c505110300510403403464030800032a41c03d80108210122039034083c2140d00e02081304002c13080d4215464259940c9c0c14030605141080074410701000c1c00b80504248141c24080c00601d00d84140b0082090003078204601040014030002200b200f9241e00c034082041d2590380381c0c00700d0000e11080f0064540354017200d40001e214000b004a8060041080d8001d0048002c0100d0a54a038814a080c15100401c00c1040220401c0030401c800290280205030304c460030b40105441d11180c0c02a081030b0b509810000b02407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 656847032 1250 656845782 656845807
    0x31603031205220809130b0f06070c0e0f0a050906040213020c07051002011e0e0606011101020706020703030603020108062b02030a08130e090111040308180904051f05060f1009080d0302 81
    0x104103034641100248502e0140308040b0341c8c0210b001005034002c030004a02c07207003005484032003480a0301c000e2503030400f5880d00c1404c0d0f208640741500e00a5080f4a4a004200c2694000c500305100f0343d0007828000c11140c4011115000394442142c20100d0f00403002d01244d40d6403041100380d0443c81550021a00e030180407001140600a086c0c80340da864505400300a0400000c5251035000c442402c2c840814044400c4060192003829030007050144000740380030030550194002d10a03a4002c0e41c0709105a41c03107605011030a07039600001c1450240c0344010942900c8100700c66808184081d054403041202d0303035a0105990800c5240040b141900e400034001c1c803c0c2003010680c44040303200240100000d0540c0c558080c071403408054084230700094143c01151510b000d1441b003c03c0074108507050310302424044d45850360710307408440c440d03620388032400c840865000b00343c0114401016210b0000300c14081140d6500b02c90600d00c14400c00850001da820b00030b210940c5000d6003510090381d500403030100d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 656848282 1250 656847032 656847049
    0x807021c0302030a111902190314060709080c0307050f0a03050601082b0f08060414070807030c09050a05090403030e070b0901020c15072a03030e031603031205220809 73
    0x180c5c403070b910a61120600c1c2e8600d03000d1400c245e03019521810b40228001300c8084111030303508090003c05a016080394440d60014a0b80d114204556a1042064403001103a4541c0001180998507503c0b1500912003840c2c0701c1c595054240008100000351030f80c6c4c0d950142020000d90003140d440d003080c10313200cac0c10360324080048081516200e402e8003007030f035040d0b070141104641498000400c0142800500c40703844580c00030381505415030f00c00101e460103d02c000c0c000d801c200c81280c0064103120704002011b0080441c0c2c403e07110014003140071a0304044c140084101d00510039401c0545800b00e5443c2008140b100d49d000e8540d00004030b994100c0310001900c0c2542c080243c42c001c07602200030243d600b2048094a4883d90300136030319004800ea510110320b0034521881c00401541d071818000080540001c60103141485c254182c940c2075407050a00750003100544006004100008203000300d280c015440298480c0031070020ba00c500341d00c40340345001050040b070212208200000e0005503480c00900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 656849532 1250 656848282 656848307
    0x60325050a050306091e070324110f070b19060e040302060903071703040311070b0d1503020a0302210a030e01021c050d0b030a05011107021314040807021c0302030a 72
    0x1070041d41800641c595403061506c8400f510f080380c0180e511100101031014800468011101d40c041c0d201c840400400f181180c418000c0840c6881a850322003041b68090340d224110980c2083c1c1070030181c0c2c50f99850050000d10640f0700c810403800f08800780466128810140034042100041c600e410b14004e071900002404021440c1c0c002e105000c0040c10000701c103a010610b80c1c803400e0b16030315a440c040d10341c0c0c2c5449e5000c507081d008141d804180c6200c031601410314200740d00c502b80190100203e4001c0c11401c00d000281d045001c0080070f00c05420040c0404044104500005003000c00414802c0d00340800c9440450004072000f044014030343c0d0401c0f00c0a000b00007030001c01c4010040100240c401d105460ba694580d545486101d00595001c1c03061184d041e80150081c400c42480c050806490343c0b00003c00ca100345143c681d610708058091160060044800b440030344140c0b1070f6162101d0b0354104070b108991008421030001c519010f0628003080d003504c03e800a43e03d4084800d0040d284980e4883d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 656850782 1250 656849532 656849539
    0x30112051b0f0d0807021e010e010c021503070909051513020a0816020a0602120a11070c23100e040f0b030c060703031d0a03030b0105120f060325050a05 67
    0xd40103000d99224903801c0620b21003140c1c2c03206404602e241045041c019080080e40c00302801003500620303011054882d42000c0240d958180c202001401502c03510700040b0040d40040e5420710511000d5843d070020b50b0400c01609201c0000caa807808100243c0300125003070030b8000b10172100c54100342402805191928a426019414001244002000b070803006040b0b0760394800020142120700c0c021710041c846283c0200b42903548040380c0d00d00a00584080c2d4903c5102407600d103d00e00c540113400c040d01d016560100904100394a80301e600d2900d0711044142510064142d4201100c3d03a44250300343c20001616210744000c24150030402084682211b0f107034030580d0406e21072402655000c60881140c40084583c01d8131034403603040c110f00410b081c0c09103003047c0c0900c203c6261220300000d14159202e03c05d540030b1040c1e4003000700440e000c0c094414400500710481c4003140d800c500300c0707144c0c03030b0300480142c202c030094800013841da1502ca0003401c05451240f0011010302c1b443c00d01e412248081c00303094 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 656852032 1250 656850782 656850823
    0x50f01060e1308030402010c1b080c030c1503011403011e090201170105060a0309060b0901061e09060c060e100c0e1201090f0209090a02061c0b030a02010504051005070803011205 78
    0x5486600d43c91100400003070402844041200420030540070382d004042d00ca645808001d51244191591a1007544110340700c1d114404440f1307220b15002614080c0d60741c2c440a0141135900e0503100c1014030000c4140b15505548a500e5450316851003800000d0800020402040b01e544500014101c20048401086024a5000180400c0e180d00049590700c8009140001d0000d5403030a119000b041c0d028000b583c00150700e0b0001841540c020109254100c07500710a0121268a0000b80c805009911542c408070701c0560705a00810541e61000075420700c4403003540c01001b0310040081c02c44904050340d4012400640c8030440c181042500c550340c0329481002040300d00496150019805558200240b08204540021700c10500500c22803100c140c1c003801da151034200c100c4c405034000c07501c0080340d40304914201c2c10650900e8001030000f00b40e80c041c4c40301c518260420041c41141d0410a10303440501804100010000c0c000c0030003103000701107050090140c22024070b420b500b0f10140b106c40c5000e11130003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 656853282 1250 656852032 656852071
    0xc1a0c04060e0109060912020117070801030201080c031b1c06060f090509040c0506090a1203030c1706150a050f040f091b121a0301091407050d080d0216050f01060e 72
    0x200b07107800306803550291390b0901c0160601c0105c0b0300c240c034032b10707007100072038a00043c003002da80c00c40d0249040e41e1003626124015a9100050070031800120b591000d1090481801c000300306465004100400b085142008012219012101507610381c0e0300ca14002101e840d44e04040d1036100720700034050a81240c43d0005810991900707203241800d4041c1c94402d500c00901540ca595455030018001d000c20049442845450309010700103251441d55030f80469002c0001011042e0005a164810171005040c240c00707500c951082915a0071a0701060300740942000452000c9030218064001000d0321800ca050050070589508292060b459180449038000c3c40d207681056084070090054449421340080c04e403184005012001c401d0000c0d103034043d482c10000300203101c4603040c901d0801201004456945540b8010311031203102e000c1024040d503500340108200c1c076240c1c2d0005c000c0000c15080e40e80c542505501e0b11401c044150b03078010b015079940c01040144d00d140d42e0345164005140030000b01070020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 656854532 1250 656853282 656853287
    0x10c020309090705090d0b04060f0c021507030221040614070203070311160905061516080d201305010206010f05010309061e020432010c1a0c04060e010906 68
    0x240600a0301c00d2102c40d0020311110310540075a00a40d100500700807000d1194244915141420703142900d0690816008209404841c01a040d4181d050360040a8008480051654895029211800301602005070b44402242c0745060081414200d80c2030b4054102454a002180c002089e041b01c85c543c40ca00b0458816008800e40f5680da0305801d01d600001c0101c02d41c14206a4110000d440c218052070001c01c040c1c009030701061081c0781c1600c1c8500c43c031910100e9a00742e8001ca07030b44c50039042c2500d02d4442c0082c61040c042c02d101d003003030040071807001112400c03848144550302482c011481c0c0414200e1303070130810010030b10042c0b03004c2c00030304665410001c8022407d0380c1c5007d59414540c46c0d1020710100510b0380c3c440741c025001a031802040000c00c11004029502ca48a100351900c142c0d00030301c9070080000780f0001101140c1804080b4400c443c4019601c600c0a6a41a6140340d10f03006840802405181214820015483d42c141d8542c03c00300701600c0d240401e5580350400c40b500c1c00902100c2e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 656855782 1250 656854532 656854537
    0x307030c0e0903071203020a020d2a0609020d08072f12160305010209030d0e060d0b030a08030f010e0f07080403050c0c0d06020316170103080319050717060102010c0203 74
    0x100403641d444041d036101500680b80d0312031643e00a0500089000b541015680355000e861400807035405c0d00d0010f200c064040310807192350803a0703c640341080740406d02c607403148152410405110703c170040780020759a00082e02c058086070f0256240880085e0708810007020b0382e844805510b00045070440c010000200c0c03a05180a401d00b14000c14844c0b04032140031208110320303200d00422035070104201b030b140d00d046400703904090750007402442000b00c08980c0e64010420400148400707018241005030307407003000780070b400c1c0c20030966003601506140501044c000d5000358031500011140b542d4551401c42603409031b039001042c480751403081400780400550b10844440d003213505071a20399201ea107c078031901e0030156000a50383d0301074218000c90040100c5a00030f94455900303d60242d0140360816015203403011000c60440006142c0001440002d240e0301c00b44d42c1000f8000c66003e6020714014288084410a48400011640070607811518209100307000307070301240030b1000380007603444190003950320b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 656857032 1250 656855782 656855789
    0xf0a02040902040902030f16060201020406080c1b060a0e15040f11010e03070303030504060b03061003030c0303060f080309030105010b090a05090c0724180b011806171b0307030c 78
    0x8035180d402030402e564554000070419600102551a076102c041d56844d40c4d003c16510050544008001c005049070041c42680c00b01d540940310504282e4a0303001003a160740c4a0303052401000c07903420140100250809c242d170b100b00402040019203043d51130b511131509002201845005236510100800603102c200749264865200d17242400c10032850005850907803900e4602d64051281c0e1a000081c154036030091402213002e81020402d0402c41c0303041c103448000c1203488501e01c030380004013003000078840d0081d19020340c028680010890780725002c144480c62070740c6c0860581d80c401320310310001d0700e000c1c401c00e801080750746c2072503103008440c2012414403100c4c0d203d480e00c6001e0540019245d420381c1002c666241d50300c600e820807100e028806a40e9022000b01758460301c1c524cc20010700c500c0341000c10751801a5082078058419a203407800c1c01c604c0c0201c040c92001c640340c9400300011148085ca26030a03140c0d0210024001130002a40e0200302605011035041c0b00b640603080400214103000d5000c42039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 656858282 1250 656857032 656857039
    0xb041a0f0a1121091305010302010203120c09030d0906030f0515060a051603020601030302060106050a05120a0902030f0d0f0e0d1e1202070f06030903080703151d06010e030f0a02 78
    0x3000b100040c030604040003100e02c0c2c42d110300700001d902c0490000c0c0004151890b01101c002003c1144c00c0c0c620021901d09010003400343e8030820512a894002c1d504181d80030f00e82d10041d0340341c51041c3c00442c3c00c24840410705400f00f2045a000d1040c0e90300342c007514015800e9880100a01e142c4560f00e500038174a83c4060320301806000a6501a880c03103441110f8181110440345102582d0a00e00255500e5091000780e00501a0b88008500c651041003120b50307034403059450380d0801d0400e01d00c1c814a080042d00c0e11002c0c555865401005840c01c1c03001c032000c040c41d170b03000d00880c0c0e4441e44c0203009511500a1f020410040507894030555440c0300a40b100c09401c06030054002000511000c4044050309000e4070700136220600d01c038242d80c00110710068607100203481c817105070780741c100790180c4049080c001c0c04101d451000a000c1071080d48191f1080409203403105145583e0502d03058181451101c0e235040c4006c51041000550300942505500002680100341b001d603000107098480c0140c00c8000d20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 656859532 1250 656858282 656858297
    0xe1302060c0a02031b090f01031205130333090f17090607050a0309050f01021c140a1805030a020d06110f040b18040e0a031202040902040b041a0f0a 65
    0x81c04901000b505901582c0501114000503052400b110740105084540d0b2003000960006030300c040f22006418102c9a012010741c54034034080703d040c0d4294008030304e5028159000d10000002c0340c514180020b204200000000d00280601c0b1540b00802c0d03240c20004c402c03070034003420300b000944d2200d00c40c0280350403084002000d8452410f11825101c0c102140e6440b5101240660500c40c001c640c49035018841e8803804400c0e07a44209100c804901440650f0260b00800e026a00b900c0c480c40a5400b4801d880c581888101440e05070034880d82c1001403c1000580d061130705405080398543c0300c60140c00c0481c010305130325500d0350016443c104281f4000340001d841b00e040318030058a91060792184100c0000d00ba072502d441c3d8841740802d41101502c20b450743c1020211020b1801c1511811800000b0f03000545080c42300340d00c0649803024106400b014a40c0d08000000300a84d0601c040c101820040441d00d40c1c0f9494403030f000807190410100801400c904010b400005203c080031240404000d040019 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 656860782 1250 656859532 656859547
    0x20d0f0b1012090501020c1608070801180f050703050102030c04080606150a050a0203090d0f020f040506030d030207021f09151404060c151401061103040e0c03180d05090a0e130206 79
    0x2d019001d201400c0100c8d11070745690401508201d40207805850030203045542d481c0c2ea50700308a09030b03590400101c1c0e15149aa5101003c0b646d0030105440c8070380250100c40c440c0d40d076540c65070708a900460759192703a01b0780801c0900503444140300150304040c0131960300c101d01d40c080b00001d40b144548032024007444000960242e000d4020b00a8035220340008110800202844c1404100e1002d24902203108201a4002c40c683e4a0300740300e0503004100c00f41c000c00d624080c140040d40254400401a0303405240a9140c501800f0304481007081c7d44982d6494400c15840c001c10540600e55001ca90300500070070300b0380c000d8010404800c1e130b011500c0c985403a103009105400c0c00390542c0314403001a0403c5040c280c00150310300316420994100d41440c0d071006600e514680e00141c59000720301500800d01c80c44000f1403032003014200590780190500b0004500c0d04070140302d0134a000714022188000c9800401c001c82c1d40c2c80e20f18440c0005001608001030646009a511002e2241501c4020b102c1c1d8404034000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 656862032 1250 656860782 656860793
    0x5031509160302031015121b020a110301060f0b0a0206090a080d0908040b0d061403030a090b030417071103010c0306050f36010512160902070213020d0f0b101209 71
    0x1030000f4890001b40d842a02c100c0e0b00300030f0410344000111a010703030038180c040030812200700c07100c28440c0044d03005d0001c64a0f40d5492101c0b4200074004180d01d5900d4140100f1075071082188a030040180f121640d03070b1003142c203c0103402c1500042194415812080c544004114a003089825040005400003124901440c08030004c1c0210303003103903444040106c0c0008400030f80d0f82c00042035030308202d05003400303200180405540348034140d0385030001030800e2410085081c0341c2020b140c105c0e100d0031a840340e402c1040c0c0405280d821204040e248801021043c040d181428490105440c15a03e81400320320704000200c4c5c06100c004c0d0358a40903440c101038113000329072601c4c241c3c00c290400c1e101280940c2020204180540000c2c01500e00c42c2c800e440c1c58031a64080010729086114040100e50105468245107000a400002c4280e8203c60410f0040c0e14048551005000c0e1a500e40400103031080c0c1d400380c0d03030122103909860303d00a425a0310054034054100545590080807204046890000d501d4035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 656863282 1250 656862032 656862061
    0x603020c0f160b21130218010f0303080c0c030f1e070b07053f060a031e060f140403120e122d0418050f06060702010203090904030503150916030203 65
    0x1022013007420750301030042c2c1811002c900d0007114021104a1800d000c203d80542d10440300780316001c10f001445a081002030b008015180c0d0040303908540504202c49800e2817420359120f42041014442c000030030403141c082050100100786140402030703081208660b501c410714880036101201344040451003e0f543c545e58100240081c52080c2d021802030b04106d4240307404120081c4d00a224004038000688070309003440c1e800100d940000245001914810700040c000c40500070546900c1d495109990001c2c4042c05548607944240725036401d1445c242c1401442010340e20710001e5454189280512650000282c80c001548181e02607540d80c8991040d40070526484288001c140008180300406001c0000290045402080005058103084c00da036a00b125400c07102000c001350b031000400c0c43d9042a01c06031031840d106004807494a109640068211507044034202c00080c0008200115200003024038401e013030095840e000c15040411100c8400d40006051500301079010000455250101d203c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 656864532 1250 656863282 656863327
    0xb19030b070f0f141e0c120702090103030e12150f01090902090a0b130f02041a030f0f040303060b0d0905010b04020703020c040b042a0f090b09010f050c070603020c0f160b 75
    0x2261400c0d111001150b056904041c11000c0300307004072413802c0450140c0804996523640c2c020b06c2003516a00719a025a1000e400d01b16143e000000400740030100300080000000c00700160900308a00d1901100c290702c402c8058000c020018208041c4c5030060316030007152604076030100004100070700b140001c20b805034910b20000710100d0401310940344c011000c3d801481542c5049101521105a0142c00300b9203100c1503500317070068005070000550080790314100680062280c54042045540c44562070490340010305001b01c0340740e544c40e411082010911890618640c00e880a40c14030f0210b484c0a0f458221082d15680682e0302c400f0340c0812550f841e484071510031403d03540a03a4018030a00301c01c28140d0941850804100c084100521082c01003084004690003e904a0300e050800b800440303c8964821000702400800d00c0074a010381414840359001c1e01e00b583d00143c450f41800006454402101000d901a810050040c0c4c2403440c0344198100b50b030951807860f1b0707940d003007101c1801030820046c0c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 656865782 1250 656864532 656864557
    0xe0402040909120c020d06020c0a020409140f011a06030402040b0904031d041401180e01060b2d03010b22060504050f030c090a0b01030b19030b070f0f14 67
    0x801092401440c1d0014480781d0060190f80c010814000c0b042c2d130020300c41440a07500c441c61124400008615800905420f000305003902c07500d03412070707010030152040b40004680e1040b003a40241c20a100410030700140340d40b144002d114020034442c1580040c03070b420b06e0040c01042e000000405641729600304c43c40340e50303000d00800424981801d00801044854032110400020f055070101c0c1440c060050720305942c800c0d45209601c2e440c02d450b1502204a14141c000000d407180425040c1e90800c0c46001c004045200c100c40e41c034651504500c241d1113010f50700300e464907142d401d003c41c98180441074034103542051120f203944000c03040b468520711042010882c129202004041020380d4000080d1048540c00e84107201c4040702002050345849070703128115000001d12000910203540c2d508102c002080606000842074220740106e5600081500007407903d88545d80c0820401403801c282c542d010050b40b404500c0d80140c0e40b001018410200c401d0001c000f0044044145220f012040340d0290f0590b8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 656867032 1250 656865782 656865787
    0xc030301030606050a12023a06021e130311130c0509041404030f050f1606020a021501080c0d0606150c020901050118030605090f0307050a1112030315010e0402 70
    0x249040b01c05401a40501c6000340000f0300001459284040050740c020b6000340040010141417122010380018040060144006500200d4899954a01c11f900e141d014810150b5036824450b194000694400381c069202202008001e00ca203002c80200c000b5281e00c140b54036126512100002e0307094100700e003050324062402a0b510b1199400800420200c0801e980500c803555a000d0b07049001c032401c49004d008948100041106a80303e14010030a07101da4542e010705040041040c6d43c40d14a1102046582d140d0026205204a404103c00e6071041d21800d40d00c1050340c140814140c030752141e1805d141c01307207010414920812103c4c1c2c11030700244c5540850307001104950900240742c8001c03003405034040c05411001041c50f5100351103034180300301c05c0c1941c2010752f4655541c0500410006000c05a6405101c500601c403143c140003c0c0b01c59400384004145503091401d00c2420100105905882070030000d5640021007400300560741e00000c50107088000c1c00d015401603d49240400100341d01c940b00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 656868282 1250 656867032 656867039
    0x12200402091c020f0603190c050c010c0309060e0309010c0b0c07061803030501080c061e090d1a061f080411120a030e04022b200a0f02120a0f050c030301 67
    0x100c60310080403d00071601030000c81184805d000d00c5100c03e1702e162030640741d1400c040ea07188005402c070b080b1003d40d5141040c585001c0003031785800c5030f2400840500180d00d40c4c000c04188001802a0448000c0e444042e510340368161002a005c410201c0009110315000c0c0c0002c5d0302050840b05484401e504100280300703003009a4a07002d42d640390404210082440c2000216000030001100244070102601181c602600c0940c0041070049058821050150400041f602602d6040503964614890640c810350403041645401d6040030050200707002c1e024800c0820400171400035281141c404071b05095510380ca490418030914041002556005900d140b000c14400790005001c8024074020758810254410f108100000d07481428080c041c210180d0700c000b404000300d580342da49181c4804900140024000718010a9000701c40c00c0c10300d1014000c9118100d11703812203240050015648050074815414119403402c50040003640d404100400d51000351590280341100c801003054401c0340d441c4d6a5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 656869532 1250 656868282 656868319
    0x110f040302031005070807050d09050d0c0210030b0901030b0402030f06090c0102150408030f1801060b13050306040b0c03060d02060715140103030503010618090c0f08011220040209 79
    0x2031000700d02070300c035032071050081181e544a11401600036950304491500c03224403c0f909900400180a851981c070103508000820411034103144000365190b9881a402074010450901e24600c4000241818150116442ea40d1190250f040d254018502003107070301d650020030300e4440c02c0c500701c130b0152050400303012015800103550803001c00d0176821250200b1031241510024207003658020106002030000c150401426200c42ea44400d0400450409140c445c0d00075003900e05d02e40c09291205070000c0c03c400540b92469469016100680090aa0b03082c02d40d105c1921080090040e1071030710b07000c4040b90300c2d0341c1d0740203074074001d00c0d001042152204250304103100403000100c81034004a160a040c900821050f280e800e04a0f070705503c810781076a103801d0055540c3c151144000186030281f080c0842ca10501d480f0780a8210001c1ea204e21104d5500c04c80030f0884407041e0001c035640300d0340541c90303800501d9074812005035404692202c180c03490b010f40441d01038000e9561069110b200881401c80200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 656870782 1250 656869532 656869537
    0x70b0402090903210a021306050406080f13030c0615090e01051e04080a031e05181902010e0a03240506010c03050a0c0f0209100801060b0a0918110f 65
    0x18021180040c240d15003610700da543e44a4024004c00d1440702c81e001105010754481c002c1d034008045d00001d45425502e2603415400c070310503085000882c40100c0c0610140ba8001c4140d80c1c000726240104100b424800c2d114101c481c50301800401704030ba10601d001c10019141c0114024254200c01c545095885140d400054013503851310060310b61a090000b4045c400d0000e440b0000340011030000c8464441c0c0d101c1c0d555691090001205060b240c2d581410700100281c5540c19080443c40c001404c0d0038801e8040300890041301e10103c80307a01c580c024050090780303469a84801503090900c07100c034604082c00f00c0e0103102598005051540044804041407542054015034140840b500300302036a0380c0340040d51804141000640018411300203103c54074060000085034030300900c010b0b21141c125500064100034125101201d180b13100104009801003405100d010b02428600c490501c2d40c4110300800c1c1d507a04d0b11411481d00d001c20346d030000d0300b0030591003e042d40b00061401503558080100d00c440c6036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 656872032 1250 656870782 656870791
    0xd09120c0305010614130507080606070c03240b030a080d0e15092b08010918060905070501180e070e130c02160905130b061813030801150503070f1103070b 68
    0x60b1844441c0e004020b06d0342c8030b034038420195503c40c841203440d10010721900b03070003000d82220641620400032001c81c240c0005181c030348040c85c0910140c050b441003194203481345400198040d600038019540040e40400a482c60f00e2041c4000041c035080b5078545a00e0000080140f100c0020502c0c20320060650200d2141c2234080030120080720f0344026510101c20111280c0300000151007100188680c804070303044024500000c412515842506032101000c480c1900b0080300d1552000e01c0400076540c00070b07184501a82d4114a82d690240782058103900f07000001c20078010040c00f40c180300319650b02d440800105241303031070003007100742404130b4081d40c2d40c04415501c3c2101300a0340301c00a0f5008540c01814492002102d02140c0411a542c40e00500f441c0900800e50010031081c068002a110810061042c02591420f1400001e036041c003078004030042e00103200707580100c12202041a0090120794020340705140480f004039410300704440c026140304841c120781c08000307020710902c01d410200c640107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 656873282 1250 656872032 656872039
    0x506031015050a1d01050f121504020f040903050315120f030418020a120e07091406120a030f18090c02060604151413060509040807140d09120c0305010614 68
    0x926111132030f106040341104a0014800307180801032003d41424180c0000800e00034108007219821101400e080119000c00740c2034841d1014100f20640c0340c0005204202c03881a2010001174200341c071f00600521008004d12240f03403400c070004196455804d0340d4038401c41100240d900507003080b2069038482e4040d1198000300e118550000c00207041d01e100700c0344212115204c0c5902e00d51184003043c09005e80010111803030003003420000304070011703008841034100328096280c00e0b86002c0d002c202d209040005440340d90751100c0703031200010740c110401511031a003904105000e0950540c102041640315088182c24905003113451002c181c001540502840085409000c048007002e000c8600501e10700ca1564640035445001005040182a01d0704c1d124280401280319900c88010920380c99050f2402c640c2c10f40005100c1060180d40c1071012010700200002e0300f00304552071001084012240507514402109413030340c00400c00c5100c0030100944c2d00c20300a000703c543c2c8200111980034040c121070701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 656874532 1250 656873282 656873299
    0x40324050f070c0308091f0b030708060709050904050f0307030c0203010506121e0c040c0801030519080a030203070e03010e01060f06020303160f020f0709020703030b030f10050603101505 82
    0x2103003203018000c0741c0b00d682c0a0351a400103c56a4038204c8a5080c00b601401c51b80c0501402940307040c8180d4034054000b2001100840c5c4031448505242c070f800a2a0320861454002c80e0502002075070020038001294002c9604000f55151401c18900340300d0015804042440001041c90406070404418481c5030300840c0200040d56443c0240200d1030550212041d16411400b5801981950303000500a4081c90034103c500404400000c0b0b0102c071001811030300400c40044c0108100501005000c842c220b11444103121840c1c1c941c0ca07444170b4000c0a030711a05140d008000601418130850904500e00001002480740f5400c840d84503000b8203d502581078000fa0b0315070301064450000040704d0140e071020b20801028480280101e40c50860140004112b00403507080d90041c1c03404101c8240035000300c7d040180e0740c640515001e400c841c1e00705c1109009422901600d404030700d0100304090994801c142c00f24481d070711a00020b050400c070142d0084200c0c681303044170282400744201c01c01038030301c1502e0041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 656875782 1250 656874532 656874541
    0x1201030611090f0103051806010b12060102030a0f050306270106080a1e1a132408150402012307060c02030412120c140309040609111b0304032405 64
    0x40754428108481c0e0070a29003101c42d00b00c1c0d446035000650045000f01d8214082d9403011109003054402c4e031010759a20400b107200c03042004031b0b0840d1038104009000852401102901c0a0108c1001004210504c1b40110000e0295121040004180100f110321003040c251010055100200203010302c8000a00000c0043d548040510807902e181d0615040f2024550b56407461102074620340c120100c41003848412800c081d2600e4456913484514820081041d080b802d000c1401c051341440064601c03842030f141000300450101301091041410303200910705036110300050b14801c480701c0410110004002c1c003405da111501c806020014401c3c1d0301400040358244049a80b800b40e8080c03228031041c40159007001030048010b0f8500d80c500380c100341d58402c1050b1100e240390310580f11944d1b800c1c0c10000781201c041c5068031410001d060a035800700f01c2e80684650f024100d0252a05103400007a40b5080b00f800f01504000380c0e0019075009142d0ba8080382d40e6541d21106918042c1501301e402d00300380103c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 656877032 1250 656875782 656875811
    0x90510051906061709120f071e0c1403032b0e190201170f07080915010e011e0305100c031d01020a080906090c01200a03180819021011010212010306 65
    0x4401c1103486c0300f00da0305040b9000d0b20035030650300050003240c075400341401c1403000f45103800c3e407120610b0041c401101807916103401022000c03404588544260010001a400c1031030070003020661850308080701c4640350f064450400180b04100c2c801003181f2440505035090019642d8195034070740300f039a1b014070100c0845403200c0c680781c1c01d036080e10070644103a0029900314842c0341015403284502c8111403a0503110011681d4800007038014200c0300c004030340140503a02e10006002888400c4410b90001180b8640f266600d859054007a280358030340310025149001c0c880d400c041d5015002c035650251340022804558002e40c014003a030310110b512000040c228103c0410458841c08060300644040d400402c011104078000007403a900f03680c0748002d0400c1c0700500b009880c0003507200f601d8500d400d042e0304114110003803407940006030341d510165101e94051a40d85004030a0380e41510505d85100e0000c2054070300c8000110149559072021900008100861860398120317030044a04104140c0444c210b03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 656878282 1250 656877032 656877043
    0xf0606090e06100e060d08040f0302040b1e04050709050405010e010608130c0306090204020f0309070e090c0102072912011a030c0318010b1c060609090510051906061709 74
    0xb6a281d2003000c50f010041022900000c581c0b2440091414107944601d40d03e070951a0025040003249000401041c801c5051500c01c0740090707030044554603140702c104808100070500c52080c0d9800b03075440743c1c0030803a21400344600a0181130020001c1c0125a198100d038941f10100344074140c002400c05003c00c2080002000c41c070728040e040b001c8521802c1c156281c1401074020104101c0c0c0082d4200009071000060801560003110281d000c0c0036114540303081c400d9254030103010b500c0e00e50420002e50100f6030f000500380782101c1c00d460b0084040d00c2c0b818003008034200b00d2007121158010010301c80c000559603900c00c9059400d8488100074041880764181c41d0b50104441d100e4070800b0403c00b0902c84401c0081c48411141080004514210303218003003108151401c60030400c09543c1c0b100350040180307a0080340c0141000000c10043c3d440c10752034041c1c1d610b80035145051700c035980e08007068070041000701e8a00d481c05120f2050099030365a030001803007088850481401d04184001042d060000480c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 656879532 1250 656878282 656878291
    0x2070209010b070b0109020f0405060a02010905152a0904090f0c090501060525050106082b050a0c050a02150301030b07110318010e030607030204050a0801180b060d0f0606090e06 78
    0x80c14200350f0b00704146c00e00294014a02c0224643c410b20002502c0e60b140303001810280c0481e400451243c2040c80c16074500a01d151100060880140410216140103580b50501c0d50000c0710040080240001c464554413480c46000d0300142008444000d20060101c6802c620b4894988404103039900c41e1400c2c1120001e015807000603004001007040d4620300746250840305100700700d0285001035a40c40a08440b01544400c4054100900014005048141a4074250361401c80d6207080450103000511034840e080007071042c49041803403442070250800c006649141e001c1c3c41c8220090b080d408a81c01030b0000d00c01190310701c07000310000350a14401c0c0241c01d001004000114102002113003005222989494498108050288103041c640d0f0704200b001d0050420307480041c1c1c0c0d9401d00c0e00b48108030360907402a10700c0d80e0411007055094034015000540290f0843c448a8441d200c0a0015403002401e81c0040c0c00f50604000b82d07070512885030b00860403074001c0305080000c2c8040c2c0c01d20310380303a000448 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 656880782 1250 656879532 656879543
    0x30605040609021c022d12070e030d110a080f070f0b06150a0806221416020d021f06050d06240503030919050d060b01020d2a0c120602070209010b07 65
    0x300c07000780c0d04c0350a15881c85c0c000b2911381d5074200006001c5010601f4012900500001c0300c1503020700440c2010f001e01913048010380380030707500c440714824074a43e40c51458600034604540000d0307130303c449a0f44901b50f5042c0c9034062440d4259400c2404d05c0f008418090f103003217110301c5415034840c180100c4141281c54004083c1c5584100d036803148100000c555a41c1c60106011117107110613007006460784034a0303c0a0006c50f07a204e1090501c000c543d04864039003411507084d90b10400c0788a4100f1b4001a108210440400b00d0b00d080380321a4041c580075110541c0460f8001c1c41c401088008c20803641c22400e249115016426518a074000360350002108030b100b419015081005100c5c40e6041c46100c03030464402c190000f07030445640c2c10100d07203607400d8040d00395080ba039940c03034070f10403507906012400114000c0e10b840c0c10114210840e07400c0d1041040c1c0304480710142d400240081010800e00c10707000700009042e0208076403103410104007950040e10201c2c82802040700104e041c030008000d595003290090b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 656882032 1250 656880782 656880817
    0x50a050f06070c02100e03100606020f0f07081005040206120f1b03070504060e1f0804030f080601120e1f0e01110307140c150c040603051003020619030605040609021c02 74
    0x1000269114046e04942c20303014003550328506a001400d014071030003441e403640242940031400320202c0c00d114010079181120342012404012450002038402031034981036000044580351840011000d106030202d4160100601081003615400307581881c0c801c041d500d411041d000406420407006100c01c4070283e020400c20711090110611558520144020180c00c1c0c2415461002e0b1010103081112928000107000601308000c059100150030041d2209040880e0a070410303400181c0f02c040041c1c841e865056039000034103900c50041000c80110152060104266980045100d0161209014842c1c00e50300f4075008421406540d4200d0b4462010b9070b94200c030130000301c3e645040b81d50100b011011203205840d44009a15107071b2608500035031100440a0361a4500100a0186d650040c030701c41c02220502070030070240c0c907501c00b194100b1100d409000d5180e80400030550085c4150b400c2550041c1c0340620201d00d4048503401008402401d02c080358088142004000c26407048041000700c50380714 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 656883282 1250 656882032 656882059
    0x308040b090a0503100209130506031c03020d0c080106090f1805041721010602010515040c030204080601090606090f1a09011202161101181e03050a050f06070c02 71
    0x11840a4072036403034000c1c14848410b03601c400192410700c5c1d8003460411198000f80c0040c0030b203450201e20340d541d200e00c90103103c2480c18000013070700c1d86807203110303042425850001010800d119a04880a0640082c2c042080702e98100000380403010034020500410500c00010445260012141040340c0345080b041014400d2400004043e0030007030011101840d0890100c003000c0441405010188041a1b80c1d0385202c0b4050510b03000c44074180e2100c0c0a59240c08103002074818000460503030480c0c10b46000c58202241401100244255805018035025242c00840c008001e0341103002260f0880d039400103120345980d030000c0c04044902c20000c142c0003c2000c048400e51610280c9500501410440ca00014003030903c8245d83c040307039641141130110042c2004000e180d4014619a260030700e0101d22440902c4400f001c0042a80200d99182031800d07044596003142440c400e003c0c607805012307034200300c0d02841d00343d036a10008051000d6078000c600000b20814805c40030306800301d80080801c0d114800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 656884532 1250 656883282 656883299
    0x1b0f0e0a0b0109051c020a05040903020a030e0310110705100b101409040647090406030812090d02160b030a0609051504060e06010503041b03151410030804 68
    0x180c1e10501c0c0c14400608030015299407101a05c011800700803000c184500348520400c1402e0009410052240b46440c0f074030400719500180100003e41d2504100d000642c40200023440d00440100c000203550030704000c07100c001000e0026100151080040301c000390f62200900090364842d00200341c00803074100c54040c02500c00e0102100c10480c80225501d0036079010003007400d84a40d078014407040340c84420782c048050104640300041888170012141d21403014040c1c603240c0c000313525860003440804240b441075962140d108400865008035280d40c1c5000032011080074080c00c48030407155005042c1e40042c040c3c00806d180042003403090007906541d0a00d104940180c1000d8851035120341d81d1500406c41d04494032803c0c0c0590041c441c080d8240c001c420403c0103a8401d5000300c891011303004188035807660090107403a00a5032041d0312840c14603090124405d081c00aa1000d40501d8009106009000380d507401600b0b4030945598076161a501d1b41031000e0008560300c002400072000300020001602e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 656885782 1250 656884532 656884541
    0x6031401141012020a0f020c0a03080a0e1206090c0307090b030304060503041e0311191110020a060908070b090606031011090a0308031f0f0603020904181b0f0e0a 71
    0xd242c0c20101c81d842d007008030f103070f04070b07000b030803100012403100c46120115a40410102c65005802c0307403c5001141103641d104114010f0984203818002c8068084e4496034400d6400f00c1400d0030202118118680165050703911b840d000d0425010380665140410040c9041c0100c1c0301d000720240080d40780515000c0304407487e48c002007040c1c6080345d00948003017944000005018486010b9555640c0d08042003c4c507500b49016030503203180c042c201c21000800038501d03622070b46800008540b5520554490041641008000d8800511181c0780a5548040186903005011020301400030003915640b404d1700300c1d94440080c1c031000d40c1940000301d00c0c6542101078100c22050966445500d0904107030401013007004509400c100d03451000401002903d40d20b5240507170010f11108842e401c1c44d8a40040e9101c1d0100320302841d010140c000501c24010340b9a43c002460510300403003c0e0400d085617040000e048189420b0112407115810000900070340d0615061055603001c50381e42c100e0fa102c1200798401803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 656887032 1250 656885782 656885809
    0xc0e0103030801061209060c020c13020903191703010618090209030316140f07140d02060f070303022109060703020a2703020901030c0905060301021309180501050702070603140114 79
    0xc0f500c807001b200025000d0b00609965102c80c3d001020716031101010880e441c407150303014804840c03050000d0381c1641c0c0e0000f03090a07800041d441440010303119040c000e003584030814420702c9c440400000050700507408111520390745669664424015142c69141090388580000765034160b0090080c40a1000f0361600c0302c400da4030403c0c0c080404000052440c0c00c0c082944103124107a00040410400c85c100c0821520a0b00c40c110b48800f00c103c22540050f40900032585194483c00c004030300041018007a030304079010440a540c10344c2041454441076815001c0c110b41c0c01100740101c4020800680c0039009565225229450300c0403141c031103821501d40d098601e00c00010348006403c0010258840840090117140200e8102452070708154903c0181c8601404a5000380c1c0b04010221200040071070030000d84902000100d9140000d180150b04103204980144c029443c04062145c0190000f44080403141075031800e100b018030140107800c0c003070740034450030108400c100141c0e50540341503035480c01003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 656888282 1250 656887032 656887067
    0xa120206092d0913080301062106090f14010b1e09090f160c12110115180b180708070c062301050306040c0501052d070c0e010303080106 60
    0xb125142c0200c403041c0440032218240803034a0103041c00d40c2000300c2603035801a8105a000000642642c464000303200511400d420000c0c0d01c8070343c48070300c000c1d00c0c0510144d4010710014410103407601d038000d0003403000c41881540c40d440c290030345801c1100428218100c4444105140c2810104800c80354480b00c0c14261a46c4c45d8010462007065585a0350114000c1441c43d145480074580304031042c0d28000d108a41d1824007000d840e13600d0001c2c01341044002c1351801d0386401400c043c40040c0301c0740582171881c01d00c80c00640c100c00120380040c07400301100510408140034045050003c092107030307010018118010400d0031000159411340200011a00140b8500d484a1000340340d84841044801d018040c041d000c410080b01d40142a101c1d001c18054030307048000c0c1095091a641d405c400414511034203041c008081600100d6181260040850005035041e25045200c0030495800c0c603030150104940800d81010007080300620006000e059992545407840c003a400d10500790381e01c03051080001c0c80d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 656889532 1250 656888282 656888299
    0x7060e03030705010f0609060b16030f030e0f0615061c09020315090d0201110a0c0f0c0503030a02070f08010c080705160204060e060301111e0714070b0d0b0a12020609 73
    0x2030f000d22442035048401c52001400c00d080030240010380b0303015030024041660601c03460889003255003c2000c1164142046003900c1d02408090307010b80542c6210304030b13a0003284070100002401180742d42c45440000108928803620f08100240c0780200c4813440d03a0b624104641d00c21a1000754000c0c10131900040842e44001000b40c85124002811242e14100303401c980c008a810640900400c0007040e806075246003070000102e0020b252000010024003d03143c4d02c0554014442006a114040d000c082c013a01d90312303005200060341d550840d20038440c2c001810380e400501c010301031084078480d680030340e110085a150b129085a6a030800d010750740303404403032000c1800142e441b4800c460051411004071481483e10000f0982150038900300c224440408222406071280b00c0f0750955001c01c8001d5046403502e0141c1441d008601003482c03000c44500c00c2070700c04915860180c02500001c2c3ca0841c0c14044202d070001880300c400c1061151012484000b007540300145040030207401d55100141c40c525 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 656890782 1250 656889532 656889547
    0xc0904051203040309140108011d0426040509180a1b0f0603090312110906180d05011b030c0f14160b06040f09020d0803040201020a05011e1b0207060e0303 68
    0x100740d8400c1d10124003207800b22404000414100100c1c40c2e20082c01d0800000640c90003a0607103042c1103084d0000b101d664110002001c2001000045010800c2d80d00c202c0303c2c0888074042c4540e07950090150501c5250311300d000401d40c010128043c0616020070014080404d40c0b5034401092001602c20300c0f03a2100c0b040790100c0c064058001141c000c000c980c2d008142501b5505001d0719050104161006503420500404a0000c00390101c5041e07030000d41300b081d600d017100103142d5030248202d02034603440390881e0ba0410501c02d0542210183c06568102141000d161010650845400c48410702c08901e00300f03006403602c0e010710065110420b802c0022882d120a10510301030302600c103441124510030311001c1c0426800c0600c654000c0804000c010003025246400058401c0c08002d0018801c400000025045910a20040d40200e504c10003d02121106511209889582c5180b6826080c80c01c40c51410b0080034209540c40e510664003e06081d0342070060880781082c3d034803c6150144410802407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 656892032 1250 656890782 656890813
    0x7080a0810181b0503091b03010902040f2a0e09150d1208070c0c0302040c05190e13140402090405160f050f060901121806140402100206090c090405 65
    0x68003100d080b142c00038a102a0180219101d420900c200c01040020700c1000302180001071800e00e00b028600300400481d40c17a600003409000499402908642002144442410300da0003a00502e41061482c0040000c0c2406030014803070410706c4400020890240441641065240207410942c074000707071000030f003454002c180c424503600021500c0c07940c421882e90f02c160b8030041103a0044104e00d003c1021010b951516a0801d41c1808080d00c1647d590030712110305809101150b0034205c0d6444405c0810448d0240581506c8001100314080e580d060101d41d10015584100151664015200c3d40c064031180c080c8444000e000b4811034451041c0050b103888a0034040102d4000d003130a1000418481c140014071541d81c40c00701242e4010301041c0325040030350303820070f80c0c0d40c20811862000040880e114030000c1c480d55001c1d080900614030707101c0062080442a40002e11070340c02170b9880c000c00411404103d82e640c40868804c03800d5004204801100c1c64000042a005406481150070101d5201410b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 656893282 1250 656892032 656892059
    0x30907031a040209060f10051b0d08010303180b07110d06020d0b0307050a270609020a0c1406011a1b1507021e060402060702041b0305090c0607080a0810 67
    0x74a9209014082008514000b20b0460707016900340e0300407050b841c050010941900400705000c09012000c581100091011400240201140000c46c0c0c4584030302c00024018070303004c0c00280e00040743d4451342d03038038000c03031042c98400ca50f5180000d0740750a405442d250300064102158903444559a92807802042050000e400020014200080c1c40c1820f002050310306045940701c94060818014108401100034481c0d407009440a41003c80e02e180214040c1f0081c80144c01042c2c1103031002c19040e0071a50b1290320507400074890002644006d40700203110359620424030500c0f0050404451622144194402a09100845607040407202d21601002420031000707000c1c00a00b0b003450020801081c3d4100141800301088420801002c3d81c0000b426848030001000640a418002921400c5403101c0e40030011a41c206480301441c065a42802806441c0c02d0314445e03c0c901c560a4180d95503d03201c8200c40580e9800b84025240542c0c1d58002e4482c624002c101000540b410f420019900d07601992 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 656894532 1250 656893282 656893313
    0xf0907200304050a060305160c020321120604021602011d090c09090c07030903110d12020109020f060f070b1b03010608100f0302090a110d020c030d110307080c03090703 74
    0x3071030301d032814801801150ba046a00640c20181000c091001c0741c160381c0b144001000b16442d01c3c42d414000b074000b0a03d042120b85c1410480d075101c00c00182905c200318058103030310f0f0b0300130400c01d0340341c83d5402000164000d40100104080700c40540c1c2c0010741c042e03c41940c003d41035031a11118843c0480002c0c45240d4115040101c10200041240b95841d2203514035521194540e41e050a01811740ca004100c4071041c000285200c60b20046070005540361400f0902041d840760050b034116203070480090181107500c83c02c0f03010385d20490f030900d401c0c50310790f09803418014005e4885007001e045403140300d040b0b14041d141c06007580c4603804505a20811800560281c4900e441d81c03011810700600d500bd10445580c0b081b030030440110380500040c5d4a01700c045401c400b00b4000800d1444000218680710302c65005030800061001800b64860400400071f003015200380141003081860301608401c0038801128083e000813090b9000481c5903461a000e16041200a0100d03040d542d10382c0d65030001d4103026070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 656895782 1250 656894532 656894597
    0x70c0527070831060f0e03190e090403110606010207060e01140d060e2a0306060c07050a08160f0b03060d081e03041101020a110d0f020a0f0312020c0f0907 68
    0x812001130040c0c50250310071190501c0c1040040041040c1c800c0d0300ca0180c80c41c50030352415441d40032021144148800062a10700078468261410300703150250038065035902507030003405214006019980089500d404403031043c0c49082c603014610b0011158010504d511560859051010241d41001c5120740ca0141c240d040f050b801c40d0400a00440d5028400c900822140c1640110404c6401d054020350780c011710190b07038160f00c1d1180c9a040b0341c02c1045640206802c802d6603070b0002500c040c0055080102c81035120300f207075501d8442005000200c100d0044d4201c4000c1003002c60102c0c1414084407039924001c0380501e003032811803071003242c403200030312605450010f0110030f100c1407000d9148007a40c401d03000d000824180049560301d0709003c2140001d68442c02001800d03d051000c9204042e19050b401010301211940b01c013080400070060740002c1d00c000c071010742d480d405580005100c0c0c8180100400f4000f5510003103041100b600401880e5600b001883c3c0440116910100c551103518240c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 656897032 1250 656895782 656895871
    0x8090111010605130507051b031b0109020904020609030f0601060807030609050f0411060705060a09062009130605030d0c062f0a030908070c05270708 66
    0x1000062024090208180392a45411400c018640d11040c41c0c0e0742c0580030000100e06036640007020b4405000fa5070b620490144004c0850f11201c0c4044006d0207141c07000150881c0018800300d841d07007261900140250005070b1580492b01600e400d90140c0340300e00000301294691555045520700707082007a8032032400300d0510030501482c00d0b098040c03a0040d0000c1c2204022502e40051004510140604082c2c800c0302c0204e80401e05440300700899110300d070044111001c5040600c140310003042941003d44c0c441d880c00c03c00780140030000c111030080c0c1d41120901c9003080717106002c04ca03400b41d00f000b12880c107179585c400000d5552002c0c46038914003a9a51260040f08a960606e00305564041c54074400000c1c50004816522950324543c000654550f64480c2d100c4512090550080c041e800c4040c1084102040741d00030030089281c09816507906407442d88802e1001031590300c0c0305441007506a0000e40000002d680b2034802e044281e40b2001c000c03507800081e268100d4032441c0c0708240c10514a07011360f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 656898282 1250 656897032 656897047
    0x30a081305011209050d08070203130303020309121609020a030207020a0e090610060c0609050a0803040c0906080a030c111504120c0506030105030c1c0614010612050601050a0f1101060308 82
    0x45144403d521221034144620001e981d1025110404140d070f0a050000d5800800d4600c0d20030400e0f9426074990a1840301c0582d141d0401a43d43d411031024944621240c1d1050799045a010810307140c08804d6a00da90b02050800e008080070303420001c0c2c1102019402d00064015a980011100c001c0c02d04201e200c03141d0410503d55414240d00030b1101e00411140201000010741c06040034000701d4019400144811692a20900b000c00f402000b0b001100c01109000901ca1200300e110100c49183c48200700869641280c55107609583e8000307000318861003001d10202d40012914424014000d01b40c0e00c507040c0c0c00c005580260026000516103521100ea114208403420f10190080c180803201c4c18115850103001031b03a69030001c442603000d45601c0013514244c4c000461341c21000741e4824000d1040e080c121311001d0018209216680010ba01d204801041044602c40c00b406008103a40301d51404405a900b502c1c0011040d80d6042084407136103441350024030a00c18000918401c0100c0c541c0c2d07814 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 656899532 1250 656898282 656898287
    0x13050a03121a09010b0a0306030b07030204051e0f010309020f0a081b0a0f032306040312050a0504170a02120d020304020a06080f0403031d100504063206030a08130501 73
    0x10008a200c510000c6100c0c8882c1a034030041c040741110040005560f903424800021005014107900040040fa001400d1207042600f50700544260b4406035010449041999440788021040740c009980100a11401c1c01c01544203400183c903581c0081c1c4051000b290000100f803564005502c41c40c0c0c3c1383c1143d0a4215515010003c3c054040000c840400910f0304002c03a42d15025141e2200828100d0303203a00c243d41c0e6076000382c880c9a00b251030344140c031418a02401d02500d90741060000001c00303840c090004140c1d02d914411580106d4120b500740c81c3c03e10030803002004a62002140c00c1c00d40c400c12010411114941c001040c8043d2501d170090386909262040c131801e00c06540101c07003400700e00c0c030401a075090680075566202d41c26290218950f00703a002005108032640e0f00805ca28000c8000b00c958842c51a00b00d5400f03544107080070000040360980803480505e001c0522501821441d000d540220085840560040b4008042d01c89614042ea01c8032241e40c800700f62000e032038100e48030401581d078 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 656900782 1250 656899532 656899541
    0x606041a0706090807050124081e0c03120309060109022a10020d02180301020403030c0303022b020c0c01020c010f0311041728080306010c0c0302060d0f0e01140f13050a0312 76
    0x1823010070041c8034a81080c00d5182c40d41c0b4040c0c81a01c3d0720720300e900c02c07408481c41000200995580035007990348400742080c1d2100181d2040360002c4a9110340800002c0341e00d00d900c03c4885150a45000164804103103907448041000c11900c01000d102d00982640703500403a10090041c22840400169540040e81c14a0040e0031104070291090348184000c1004c01d8010100170160f5074035141c0140c0e80c3d08010041c00f4405040313581084001d4002115800c02c0c40e107680206003003a80d0b8400c41b8080c0000c040120323510540e55010074002040783d00e2030030140c0d019410881d03c805180f450b03141081c0d15003030802c08000141101a913590300c0b12040390000e5110000d4840c000011b0b800d000c060400548612005100280206042244840e0080203100300d03541040040d6900521a81e500c0701c0b51071071040a00402c6404400d06441c1110000a03000d0502c200b480c0003403d01c100415958982c0510320200c3c1c001062840f110703910600410000780140190701c609403107500c4030085080a8843d041c2240d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 656902032 1250 656900782 656900831
    0x5010e010c1202010603021305060d020111032701030b0a0303050a12060b030405033f06040902030f011505090105090a0203090f0a060c0912211808150606041a07060908070501 77
    0x80d0b127883e05201e0141c44180710309141640a0901c20710644421721200d00c0c0d441001c100c01c1c032080350810b103150842514044407a602400340d03814000091a0010000c84620512004010403420803500d0901402a50310348851000c8080008070b113035071540c050b0703440c0e4000c480c00c441c035402c00a0080c41003448106030b64400b0104a071002c100c407c00b822030895002070384111640315100720000400641e56508119202580501592a041410b001c0303640600402c0c00e002e80c030b0301d1032440c0c04900d034241525002e049900051594117a915070342c51141c020f46c0040c20380420b500a14000320014202006069103032482040e0004900300c0c2c60781c004280071040e4100754282082925002c000c00c00c0992017000561460103100d20700b00580307005551031410513040c0492403881010000b05400007107040154030a071014844070a90b9141c1c20802c092084d8040c07183c2c1403030501c100c0c21440c0c13014405032030106e02c503403000a04208203442d040803980100030f04443c941c0d1915400e44003150160440c80d00d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 656903282 1250 656902032 656902069
    0x60b120c0a12092d11100c02240a210b0d06150f0e011401020604050601120809090c03060301060f050616110406030819081005010e010c120201060302 66
    0x51400075000200b50700890540010100c0d19000b0400501488619040a1501c52500d92202045501007a00d13041c59000d402d40e00038100020b003e00e00c0c02d0851140c0c9010007550740304c0d5680300c866801c01c2520307807885880c0b03241078140400340d41582840000130404d140725078071104c40c50001aa040d98988260a803c840254101940700707425407034034181e285106510542c04a04881c100c41c50042001943e4030801581c80c951800140240d0045400390603186480109441c06580c07000581e51101c0907600105594041801044410486030f0801c3c5001c1c41a68840c1c606041c4000240346180b0540c5c54000301d01c800010700c4120301d403d1280b5401000d04441d4181118500390018407680200b4100615014a90f962032082100540c4045640d4100a108101072512810140e0450308070a08c4403880c482c0c55094044424003401c5682e108a68501312418802c2c10003004540c1d0000300c058060501501d600d007100018100100403801c4612640000f42052560040015810445107142e11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 656904532 1250 656903282 656903287
    0x61e030b0105040308071713050a09050609011806081b1e01021f090501090b040b01090e0307060b01030e010e010c020d260705071a06040501050301050f0411040e01060b120c 76
    0xe660030106550450350000c40c3d40761550101d082191040d601d480604030044c1c00000e0725a1071079005190b80e0306507507040d94203007a043e03200d05111013101ca042d95600d60101001004000c40800c8855046001c500d204000c24255a503031540340c506480e039507500340000b00d0114844d500381840d00316403504a0600c1c19003400512042d00103522198410480c1440e001200719410b00c40c0d0030342d00058800303603010b4001c22a06c0303042c1c10004903941c800c3e2012201198031a00005024009006040d201a17003100030703501c0c004059a844000b400007440c150305150b1a640c0c1c0b4015107100384510784141c00b860001084e4810b840e03000a00300600548200144401218180080ca10b106064407511800700d4560752143c440b003a0a5405000300c1000801090b0350305035040e8149400c4008601a46040d0340500680c1d07200c0040600341c440440c1d140f6140f011120000b0089407048070a03078601c440c0a0400112855011626404d44d031942e0007400071100000b030b400a401e903a007151b0b02e5011810029060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 656905782 1250 656904532 656904551
    0x1101050d0f06032d06020c0f0a0609030e0102060103030e061602090a0902030d0315092703030b03071205030a0c1509030207050918060c07020604240f050412141006061e03 75
    0x203941401c8030a0241000c0d07030200d04802c0d20b61081100d00c0d90044c8c514110b50010201c0c6c64a00b01418170030904500050201500d011a540006102c60507a070307168507003c80d80c501c0e0b034061203010382002c0d8404e1000001b000c0e0950150f2039036800b150044d0016900070440f40101e0041c1031502070a01c185104140c03501000704004a10750719182c054130120a40850094141c0c0d00c0414000c80307001e03c2170758510020100d00101500741c0e00140c80d0100503001c0d02d016998070340d4194103500c580c0c00c015044e03400410614807520721400300b011450788a01601991000003070007807000c80d00d00801c21409a408054240820715081c1c0086900c01241d0180b5034034007680c1c020894440401500369408a03101017158411556040203a60103456081072050841c0c91099020040e002030f9890034021560030002c041c180380c81181100c0540d100c03801c60310034024940d035808014070364044601195000303842131188014050300540004120a0391010400503004101901040c0c61081607018103103401c0548 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 656907032 1250 656905782 656905853
    0x6010807050a12080f0c0d030c020706080a05100f120201032702061b030d06030350030103060501031b0806060609030f0105090708281101050d0f0603 66
    0x800f43d030b032089440140d88100d858034084034096070600c0780042c10045041e42d0a40303000500018071404540e820b0010f0702441c6030690700d42102d8001d400002d082c50340001c40302c4540d0741246e0f03006030b0708a1240c0d0046540d1036110303118040390f0700310441c030a45424070301d011f540c2e040c0a081180c0380b04c0c411504405903003803100500000030060080c00340344042403690348403004910fa001501109000c3e030343d4400418495a0081c5594081140030607072103041003800c5c83d00e080c01220780d11111768070364144258140c0440156800380500714002d4400100101c08100d400000e5030003903101e407401184650561504c0304103207005440041c0d802107482d40c03c03c0003500001d645508950f094402a0f0f0f00c3c468000807a040024015020701d1940c03c003010301c05607550018006040310030040684968124165650051041740060051140b540c4040308001c60900d40d02c005814005040c030a05d009520074554060b180318805424103103680f460700b001446015030480070140f00040d851108020b00d61410b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 656908282 1250 656907032 656907049
    0x6020f12071221050601030606030506010801091a060c03130b0c030901120b04021215030a0b060f040213151701030b15061c150e1905090304050603070c03020601080705 74
    0x10704080814081c02d41c0a50091052892800d0b00705145044510300c1c41c01d80026000c150741c02c0e070019140c01000200140720748551401080c05030743c2e106440e441c00000030068080c001c083d0910910380d0048912965849004082003525100555112910403821007500103d40c1c1c41142a140204840306034034002200b241c4410009081880e004030780050300000030280c5004180e0424400601700042115442075148602205295840c0c03401050040c0364907200340d600c00070050040c1e10081b03011858403802c007160114000d44014140341c405d4102d0707410000164040b6003030407401c2da03290300015481010b0b522100d20204070718015500d59580d940700c049000740f240410400c00306207601155540011a58080c0d5030300351018040c0740481125000307000e080e103002c141c49072a032400a401c1145600ca1803003100101200d4000c8030210305580094800140749100c280401c00c0301250550792034004e0340c0a8101942c8251b040c10240c0740107880c0c01c0042e00b000019a00c0b0304402c0049a8600a2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 656909532 1250 656908282 656908297
    0xd021606051003080d02131508041719030504020324040314030103030905061309020a050904051803071202070f0f15170712020c030f071b0312030216050f060106020f12 74
    0x600580e90005042405280b0300543c0000803203a40300902007000640c0700c000b43d409070703009403400e2f40201006650001c5a205402d03011f00c000c403920135202422130290384082da10500190a03508100d442c07140f0030498042280c858002c182c40f84040c0002d1542c4452500301d110a0401214519411a1000303400b0240c5489814416800010070800311000c54050342d004141082c011354882d14130040c083c100e03812150f9a03e006901d800b0006030ba41c6200c00c90401798600060180d0718240720b43c2c1310700c080c030200d05e0b00c0c000651103611070005140102c000101c00400c4102c0300941c2890a081000741180800f807a40c1041203406031a00040550440003240c00003c2424401070040510b00241c01a00a641110030a4000491414034404080e4010300e20746200b0102009161030b03859050109030b08038040600170031060840002054002d900a04e54150040100f84844125130703183c5240900500b546034043c1c01981c0100460303031b0100316480b100341c40ea8020301190311207821111a02d00509a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 656910782 1250 656909532 656909557
    0x103230c0405040f1209090f060b03010b0304020a21152307180e04020301180302070e150319060c0c020102031909080607030c020d0c030818030d02160605100308 71
    0x2000b10f004c00041c01e4104854960004004038010307201c14000c0c15a80040c8603404243d81072280725280e07041c0500c541c1d8180c4660304149400c590910300c1601103600010001c0b600310440d41000318400071010228154100c0a9150b03580030030407441c225060346110700d405040e150503c1e0943c0c617040c0c4600200281803070000b000b00a60340d0ba00c40201d41114001d81801d203038488541010030103428000440d0311540c000d5000344250048415603855419070401c0160040c0c10a02c0c09110740c7d8840c910792504003030950202c03900003110000003410298214000414640381e00d0100302003103010301460043c182503080019014586030000b0352a44a41c404c03114120740d0001450000c1c50140904902501e100c004450691802c4240600102070642c000005440f4801140403014440d0091034400303581955659490703160300d5480d051310320f41140740010601040c4418503c03c0d000388080c110000b40c0c8281e104000d407883c1800400c840b405060001c1542c2614420710204041e403084503001e45100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 656912032 1250 656910782 656910791
    0x61b0207140d110103060b0711030723010e0f130e0d0f020d08040221030d0b1522080d080a0f0605060415030e0111040e06041803051318020409290409030e06030c030103230c04 77
    0xd4005214100301802280d8041c900c10390000c3c4040e540d50000c6180d410344007c074b07102c80900c500c06691040301103064400591040c0900003007103201e505816040f603c00707400c42d9200603503000c45141c0e00d119400c242000c0d6002245940742d00b50640290300035036600751078840f03124a11184205a502c00d5015421020444440c800035a60380000d01000410345002035651508456a004184e12416941c1c01034182c104100680c011b1002c0c8500381c1102e40040c503062030103280c00c590049402808003070b207083c15640c400c00d505507042030042030480041c0005590341c450030b100c241650b490010748070b14050b40c0780c0920b0404112240e01600d183c680c00d824070725107512842c002051441d0f82e46d0085140d15102048201030440302ea0081c20a41c0c175203010034004860000390161003001d08400d40d803c08614040040040e04141e401344100718000d181401c00100c2074404111248d00a90740340f840e0701e2000004005201c4010181ea190210320403264800c8401f881c0d5060341c035030164a9030344c8540c3d500c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 656913282 1250 656912032 656912057
    0x3092506031a04050411090f01140d020301020c0f0303010f0801050108100b03100906020a081632040b070302061303050301140d061b0207140d110103060b071103072301 74
    0x281d030502d00d0b0307240c4002e106010600d060b24160a800c052003940d02e0280750b0220200f0b0140c0c9480002c43d06032400002c0981c10344000780c08000d01400300c0364080c4d0301550301308003806800006000c031821601d540340041d41d895140051201500d0800e034004180382c4d00d044d0041c0030104000c2200e5120320600c001c0440c06441000010b4101144400441400c80c5404451001c011550f001f4100041c280d0316281d0041d40c80d4118441c0c420300c902c0160700090000c0011010806040050800020070320401100d078201c2400d0100050f4860b0300300390348132500828590200340d410498254400d0408103c0140700082e51307005002d501041c041c8940004e040c0b6810070b290740381d610050403101c0e00078000340301e281501c80c8200e240030301c4800f40f0710042c01444030118070b100083c0010301c0290310261034420b08114170303120702c900c0c4081c11440398105616454002101c48410000d00040e60044141802c00701d80441054034107a400d80c000c40c9140c6d0303d450300d802c064448140d110160102802c244050041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 656914532 1250 656913282 656913311
    0x60c0114010e010603140606162603060415080d050f1e341407050a03030f02210703082e0e01050d08221503020309250603 54
    0x200310805020351040000082c0510201c40050484409880400c151750207080070040c6c038001102e900c0d80026041025510515100e4100c04109004110518885801d0580725801075500300e102e098102010040c40144d08d402e00c6203030b8400002590200c0410726184803142c0701c071414012a402c1c0440420313041c40031441c54048500c400328006415243d202c0d080ca941c034190f040700740080c3c411001041c0d07a200c10306600502c004020b045009405850aa0365074a04248401e03c00a0050307003e0180005542c0d21107219a1010314441e80b00c120000600c0b01e0020f140c1010b100c2c1d100b0340c5401100c030302143c2061172005c407004036801d840d01a01c00d564041e000c450402590b0030542d00303c4000081900c40c220045201e9040d10468011504a6640e403800c0002d020200a006408900d0401004000041c400702e000da8815101d540203144507921014081e407141000500004203800204001030143c040c0f0141c200300b803400c10103402c641100c4034000342c40c19840c0201400c0c10782e03400c41524070030b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 656915782 1250 656914532 656914541
    0x3020a0b07050a080d020c011b0516020a09050403020d0f1409091e01090209030c0406051e0a030f030f0e270c1b03070318030b040206070809090f1501030e0c060c01 72
    0x3e030002005540c4181078001741e002175021020243d65940703002510a9061000c000455180d645962040e040c8940c840f442c0c0041e1103100070890717100c4e11031903002a40802500071310303100754025005042c41e03c00e4404c02811040c403001c20b031001c2210041e00e4410a03c00c003015541c0210060b226080c4075a900d5103140d514800c00c030f9040d00744104080000176540e482c0d400030000c0300d00c01c3c0e080d20440c420340824401036600e14090380ba0f02c0344015150719500009a0b20074040c40e04000d2500194070b0b41c079102e242c403414954070260700040d00760103d140e20981103001190302c46020390f284a90806009101f02900240c4070541c003000d482e0b00c0118680e074510b0070603588001042848040920918010701d42c1e02e501000301200072034640038040130501c0c80c0d0300746c2c02c084030707040360003541187d41c0c0d5401c004480c1d004003c11516a1418405282e554942060389841038102c2c0410b07242c1420b0424480c3c0c001903c091009042500f003815141c0303052804500340507a03a1060380c516451340b01c03a49141e405030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 656917032 1250 656915782 656915803
    0x3060604092a022a04020f0418060b031303110c0a0603091103161505070f06050603100c0518150c031c11040302130615091e03020a0b0705 61
    0x950520805080c800c040007400715031400c070030744100c0d1040b0003a03205036100c010403460564080c0711110011078100001e4401c04a4000080c0010b20308206101c80c544c140d00140c200c42100108468403019105a9209603400352580059036400c5147c0150740b031440c2002500010204110544045003040c4100100c41c1c080d000100240c0c001d035150440180141031000056841e06016540300030b843c200807550300c5038114200701088070241410b080c0091000d02d4450303401045410020300d000705100080b10000b041c4204408141420324004241c50700310311104504090b40b600610f100b6264100d004c88001021580030f180d462416840082c2d141c09042d1603903000c4d5040000c0402c12000c6c003100a16180028460a010900c000355810040301c50b12a581071050600708030600c00342c9804140100b1202d88200301282c81c907110740041c000b141031003500c075010812022040c00000b003405050f481c2c2e0001c480315181103924640000c0c0581d0b90034480d2200e86580040c8910501800b0310200126 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 656918282 1250 656917032 656917049
    0x150209040b09090a290c070c090203130b06010306260a02040e0a0203150103021525211407120c05060114010e120d110a060908040504110a020307030503060604 70
    0x52603c030000707903100e800d028011175040008003201c10f01c8a99250085400c40300140c20300c0c0c01c070750f0b4007907003208158021402500c0d07009400d07400144c0c040550005510640d032423414000203903401d2a00f8140808d015201c42c0c14141401002e2044240d403446084000414580002c80d54040041c09410000b9902c0c0c06500141489042c0e84400300004c0e0078130200e403095084888141202003164400f12080c04000d5116150300302c0d445241011401400c040710aa001c8540043c444800c0441042100c034400c4031007410755a2200124101c21118002804450421017210090219003803c1442a107400030203804142031103202c558030ac1c01c04441c4080d40141100d52658540d007260300070a68204e82e10b0300142d001a5012a641013a603c8440100300c454002c000504d1450410b90709511000d10441c1284034400710440804c02030301404840900072401e059a440c1804240400c1e24000c085c400841c820070840b00a0003640002224002d50300741c030304a61a41c41304400074102d03114641c082500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 656919532 1250 656918282 656918299
    0xd0609050103140c090106050d0b0a12210e0604050415050a030c210f0209061512150d03051c110d020901030f0e0712050a080a051305030604150209040b 67
    0x4011403004080352068022040b84c00c041d030000100450a0341c00d004000c0000d209000b03041d029030b4290455084000018044d05c00705440e61043d80142030140300c00d031400e410003001950480740e005007070394203d611441e04032503812002c0049a120b100d9481018005c5550b0f6141d103000d046c07811080c0014100c001d00001c5816901e06000140268030b00400d0841c184800312003d00f803c203500101545276000d503500440300b01c940c0030030a00700002400d058001103004d4807002e154410a00820f00b80090708089402805e0040e501c0604546611001740201030003010400401e801030305a540344500149990483c1e0343e80d24080d409008000031040c00e125000c10840b482803140d030043c01c4a8103080e030b410800307844104d520005503145404142c13402e801003001404880314444031007070894000c0c82115a2441c60350f680c15242c0c1d03c411840400514003141c000000140350207441d00074001180200003a0402e0703114a18550744200081c4e1400303900003011040c2d0307281c54001c1a07410200411601 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 656920782 1250 656919532 656919539
    0x131419080406030507020a0215090f03120d1821020c0402040311180610030c050f13050907051c0519090b0a0e0102070b0f0c040e0c0d2307050d06090501 67
    0x98207600640148000700e401d0000044440b88001240310000390028000c030258103a22204600c80c0d1b020505042c3c2207002072131400840e881c1041101e020480d12800543ea544e4140c0a12007100d4103140c2c41c00c400d441c040d12080200380364000d1500310b54080100c46090b074042800aa00d44040491101d400c503001080c00000e114018074494140781040d80c003010600071645000320100f0088401d039070b008000403030f19980035102c2e901001800f0f201d420318916007031603c20b4683c0b46401040100000303102110341030203941032410920f034002925040c1241018001e90940040c0000c10003200e0409a1f1040000d00c03810040e00f48682e845007644040004046505200c1c5170b0b0502211102100b5040c04401c0320145030500c03c944105030880c1c60b0300066115610760341c9004501800001000c0801e00002c41d414410703100682c06104641e246580d202c000006c0b440548035060603900800c41500c03035a0500d003038940c00e119404101d0b8034000f90b03a501c1d503480d540c004003129080315140314500750010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 656922032 1250 656920782 656920793
    0x1412070f0605040f09051306050c07020402040f03030f05030f010302040b0a17070f062a14030c03030a0b0a14010e010210021b100605010909050c070f0b0f0609131419 73
    0x280107540b01c59841c107031320700e450310f0007041550b00564110b86244c2d01c02129402240c02a4000d45e04241c84804952810945800084c03c0c0e800581080789401040740080080540002c1c4080003a03170541856401c0d80b4240891100c42d15051202138055a00c0e28032501c019694005204050420040b00000c50b203140301c0b071142e640e00203009035281c8400001c1e003c107803240030301b024403aa00d0b03c03441807469000d19080fa808100d40807138000c0707178480062140481101c42c01c0c030117824031366080c50045440c0c0c5401881c041c2a500340340300c1d40340a81c19180060084628108401c1c824010070f0a00154040b20b5900413441c0002c0e0380d14400c80d26102250180f4144d00602d0030403c120b02a100b16041c2448081141040750201d2007924041141c442007041850200d410044c0e025898000b42801e103a81074640f21025607040008036801c03041c1c8400c228900514002d41d44d0015410344003800586848045050050700700040940725041e141302100781181c0800800403400149002104ca481da2481d06 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 656923282 1250 656922032 656922037
    0x40b1e0717070e060703050906070807050a030210090b0708070c080408010b130203270114012d030804120f020301181a13020d0204150308090f010201061412070f0605 73
    0x1c0002a0800400b1031000c900c1000d0003121108010200f920300b17041a58242d629600c201d034515008070051010380081a494030103491540e0155020703200440751450b0003410960645481200301e4903209010002c1600b181c0303560381c00446802d1030340644d103900d00242c404401c541e10060494400140205086d0b106403c100f60b695000d8036012080c0c07800c18919000e078002191002040381d581e4107030410300040c0c1a28083d903e8101d000000f424038046601035a0a2008d801000940708007407840c0c00801c00f801c0002c0031122141d4600b203c49415540ca13404184036a00c035407160006083c2c0c1e803d00740030815a40040107a8002c008000760483c0604004d94004141c90a0b204101c0025010210541d241c0105102c0c43e00031002d03484400d429030820150b00d810440c26a0041c0d0741300c1041a000c041c080f0a0030240d8007842820307440701200001c000b807180310242640c1c11a4100a0100f088004840c0e0005069904980e2030301d8203903106910910305246640f0100c00310030509000a07440d07070031000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 656924532 1250 656923282 656923307
    0x10b13060602011103091b0a080303010603061815050609060c011a0108061c0f060e01020c010e160608010e040813090f0609060311100e040c170604050103020603040b1e07 75
    0xb40712108076104c40781100d00007101d0600164220540c0c00d003110901c104510398a08000f0801390711640c403800d10b1490340d0801d0300f10001103540d500060001d02214003c0280d1464144c00910800c003920199521000c03140c41050f0144170007080d5244907a944400342c0364101d8641d0001c1003480c40d1179000b04410b440241d503003070100303640002080541c00e254094138002c071501030f01e2903c650380030350701e44241105180007612085d03a242c40650b66a082800200344c091400340c00410b510352001c180d28140101008000804070a1180c100031181d08108200d044403481c045912855940703003003142c0148200703003004102d100e4048000c24604040c0c0e00c00240024240e008100250b1920341700340444803e40000f8003c01006202c009c41482d101c5130301d4080109615143d40c91003031000200b41a100c8911000c030110f19100d400900d172010205880c0da2055044030103001729451600451100d1101130001b4103084001c4001454410b243e0040e81c02c0d4880d01c4000d01d28601d030101004001c00810303039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 656925782 1250 656924532 656924537
    0x612010302040b01032711040c0c0b0f01140114040306052a030712021308191502041512020c0a140c09010305030d0207390b13030b040203010b130606 66
    0x785040c0341c2d4801e105170310b400002e008503c840315010401b040404c83c8110011030710081c90f000581d80b40c2d1600e000d00100d8441c40d8446525810032840c1c92440c1903070040c04017006c1011240104054041ca41285a52000a08141d0003103c0c2c00e101d11040d0f4885c58002400c3c007802c01f014085040308034a0310040e160406410310304042d8003220071542c944801d440070780c0001c80210b00b07038159141c0b035402405000490900b20b158140e840800074108004100d8510344060090380c580c0078401081c05100c208488164210318103410b010060180c1c00e51a4521802c10203000c2402034001101c1d4122b135030b900010402c0395010783e40d41c034184150000c21101c0103854061302c11070707090b42c0c00c01c0306105040e00d42c000e025604040d27482e00940000d4008250a60b800140c002176140761424a540071840012603030f880e44a0418103160701d07090361810341e006840710a010024503103004800b84070318082e80c0d8003031041c4401c0d89031800000d0141040c01c4407103500402207160807100e02120f0740720008032032064 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 656927032 1250 656925782 656925791
    0x140616080a14040b1302041b030e0c0901060f0c051c320903011401090203040204060509070e0103110405090907050307060c08040315060b0d1a0603060112050c09061201030204 77
    0x610000c0c20b40d518507252604400700a4003040000300c4040505502141d4030b0401d43e1611120380001c1e00391030824841026042e980d54500103a030b640f40c003c0190b80b490020007014038002180110f0b041c00c1c0d052107080700700704c00805020003e92007280d01c00c1b1040d420000301c4000070910343d15403249003403c82849020904214038024100d6010038940d074000200100d1b5802c01c00329456002e0a07911481d0800d91556a88201c1e1002c804645400c0b806004280720060722894148140400c076100c6030441d9200d500700d1010094480c4d404036246d82210402c0c03901194249010000c6689030089400c2a40c0c8800840e08020031000c0002d611300c02c50f8030880c03ca8040c159592000d6810380c2c6205000392029404210501c0412949007141c00901469080044c04598640581d58203400616826090648910701510124520b003e150400c0e0030132202e162550500070300184c0f2034100b240e5204052526180015134034210203003a5160901b000c2c1110f65201c0030a0070a00340500d09000880c03080e0b250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 656928282 1250 656927032 656927041
    0x50111030706090f0c081501300c12030804020901050904120e0a1d16030209060f07080c030318070f050f100e090c1e090d03050c0c0604030b040203150702030a0c14061608 75
    0x1083e0b140b5075274410140c241445203800345178490300b06800d540c05540c1d40404a00000f454a042d82c8958030460082c0d485071000d08244c41003003c0c08106900c00380c4a0410324083c4008100d20100e0791615040a08001011a070b404021074001c525a5002c0c1c0c0d601001200c810720b05208298265100c1d043c101e050700c1402c003108105400300d000308040c0640000c0244103090494410800a1010a010319001820120501c4010340766a200302c0e001a0418000b12802c440c21508212a00250446c0b10f0092061401e04d000300700d480c01d04e004200d102d101c4114081055500848a0300e10b204009429581c491400706034518107644050600031007034980b0011244a1810602600e0346908014a1a40040465181100c950304510f0000b501c43c000c0d000d00c1400da9a82d64000c0004510410300076105241c103004140c00c0042001881c02041007035070030071421940c08805c4554101441c2008018504d0a04140c01c1c40000314240c08803502c14070060141c040c4485007115544111540c071500c20382d0b074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 656929532 1250 656928282 656928299
    0x50303190e04020f03180a03021b012007050a08030a0e0904150908130f0503030a03020c191506050d020109051903060f200721270f050111030706090f0c081501 70
    0x1000e440c05030042c0c02114840c104072b5903d40e810a040354051400942e042c90f0b91240d0b00c0d50803543c142000050b0b00c204030400c03460030942e895200810500001d503080075041c41c4050300501c61121070501c100008400030b0100705502c000162242c100080c100003082e91868244601d82c000400890401c4000030000340000d004010300080e07034000f80c051400c00b03241500c1030300a904142d12a00d92809075200d0161644907a141c03c048440c0a080c445040c148141c00da1000ca40c691307005140140b2100f5929400350360007400c0081121010341d0705501c2d0b00c00b6900c40030f5080740c80750001001c403420031480c2c0c0c00108994102c001c40c40e075a0a030220145074104034001d0540b0403050014210410840f61184000b0b0721200111800c50f1800d140c2d002110b482a284160500d0510700032407041a07030001d10a03402c201d401500682000e003001240002c10526030b556901030308900600244d00c030b030f0a00081068019021554946c0306400d6800346444803806038542c1da48540c01e200021684000007803645 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 656930782 1250 656929532 656929543
    0x2070f24090c0e070903021c0204051509040f0602040b0f0403020a0602010e060406021e0307030e0f010c090b0913020403150b0409030e120a020916080a0204050303190e04020f0318 79
    0x1680031008000d000e150003034004074014010311031380034002d503074500002503140c00305c0d0b060b04460004c803116440702807841044102e42014040c100300100a0240403074a440e0119280d402c6500b010004050007050f01c0d004000c1e114a81104e40101004200c1c01000c0c3c5090019105903031003182c42d0390b101516100201d00b200d1501000054590114001c2004a1843c1c0d00070566601c51440850781d040340c0400e80101e030b5106440441c0080c2d170f02d00140a83c3c03041480b01010412801000b4088268031081c01000d0715042e0081441d4140c2c0018200340e15540c2071001c00f1810003c000070340d21a59203003410240902d4a4860300d0a041c03d00f603810a00e40752a11034651059410344940d00081040070500070b590280c02e0b0560707182d00c0303103443c15005a545c001c040b901c1429040b52001341403544a100a100100c00703071004440c41c0c01484203000320b50340441640c02403003402c0320401c801c54940c402100c24481030034502d50400d1000800051208110f8011031180020202c0440b060100700302e800ea444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 656932032 1250 656930782 656930801
    0x313090e030909041b03120c03110705010203030a0f1415130b0916030905011103060f06041a130f030507060807050304230c091302030c09012702070f24 67
    0x80aa03400141c000760783d584070007008401032850305c20f0407a180c1c2e940c0410f07050850078220204007840d42c00c004269200551000c0c0180c030601074a05189801d001035036900016058403010b41d00c486009007401c100b07501c01078912441410202c003a00305a0300220036180e0101d00075001d039107aa5084006030505001c0e480203400080c20758011507403025440c050410314000c1180030541c450f100792000c10300901811021452003a151560707410120200485c044454101c1130240384103110800c0340f41405003010700c2d120807041000350303980c44008410144881c69002121004c010220200901200085040940d0b6694441024603242d5050503280d501044500411785d601560200e080d0001a2500500244102c0c0440d0007810b48030b0000b8488a402320340e00349091441015003420b52038200b26070055400c095901e000954104070f101401c0d08041e001081c2c82c00107940c40c15540c1030842d811140c050790440c4a0280e0041680b5144281645045220050780380c82840e0700d1b110b0945124803c1300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 656933282 1250 656932032 656932039
    0xe060c0a20240f0a0908030a12061203020a0602211f060e31060b031e0708180c09010b130803041206150b160302060a0204060c0f140313090e0309 64
    0x83c880300d80c9904009511804410041284281c00003c030190100094050038485450308201c00d034100403080f040300d8a940c043c0d50501c5280c80c0200100780c011400000703042c0c000901580d69007004982620001d844090210340070b0a10b0100003841c50300007059000445c2c0101403000c025135880c0f007103e03079810100c1c20350340c00983d40b885400d03c030180011401c4902c48924510160b0000d81d012131048039440c2e8480c6200880000c1007141c208044d01c02c66848040709602e41002d81082c14004203296802041400ba50018001c62198490304022810207a4170080c001caa0765a116520185660804208902c2c00400550041207140002c001d40e400d40d880010100c49018a54403043c02034401580c520280810350000801c031021002c0040040400d0b00300c0f01a0141e81e24540240313400b0004004440d460310500042c01015404280304505a42100c071842d148006030401d40b0a4080c3e4054040c40b601c0005509014103202c0340e202e03c00c89002c0d0f6000c00c03846103001502900d0f4802c00105590 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 656934532 1250 656933282 656933287
    0x30610060804051006151b03080c0c03091309030f02060702061b0d111201090908040e09150f0915010803030a0c0c050106060c0605160e060c0a2024 65
    0x80d061144015580c0039010744220382d090728110700c92030b0031104540c02c0142c0c0d460038446000616900a140322404851207034030102d01c54625100100160400b500454910300002840c004010003081510498030b00100403040b00002c010070b1300e00805d4589011008111403002d40d6150342c0c0003281c5140300d0143c54000c0c00255031881c0d0352459403841e80c450050501c201380400f11420340b03244110038030100c4010480356a40e401320030300c1000000591150342c20a080c00c4240340081c244070256021185c0750344820b5426154584940c2c00d1103020b501220305c00d541d4504210305140d000c61658000c02d103602c00c2e1a054591740d200d0030110702c001d002d071421a40c810000b09041716800c0d4400368100342d091800c4a03101c00c6550741c1e01e0969140d5407003e800034400c42ca1810500484d4860130380c02000d0982809402649510082c02c80700310b642c0524824140400c0d0180b0810043c0503100c06181e1050f0351480010b0070080d00307800002c109031120700511404101000c0304141c8403c50310304000038a286070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 656935782 1250 656934532 656934539
    0x150f010b0901080a0c14030a05010e011e06081509090d0e010e010504120c0b0705010e0d0c0b070e0f03010603060e150603070e09101a040c0503130807050a0506010602100506030610 79
    0x80684410485c010812070344c0301203402c9155102c0f010b98080c5945e400c0204440d49880f8001c003041c00d042c1c00c41d0035204401c040b9100da4602d032a011004440280c14426860390790f44d285080300503001616550814501000c2007080c035400708112503007030819110784c010390782e45000458140d40180341c0180070810400c002c2c0705800b5032030044032405109400c42d903c02a102c61448643e0340200100721441d0b03444404600104205100c0040420b41e1460029908051502e80c200c1499004e0314000c02e00007080cc00d0481511140b03c981e400900c040c0003070021760f95a2a01c10002c041c03404550340036000e00324100c0b0103e024513624502640d0300038010a4003500f4850340c9441c444020340b81d581c0768891202c2c0c100d6030801c1e500651440100445a400c00724100405000c00c4d901d451900004000741081008901441180d02d25240740c0c00c0804161a141c8600c1e2107407030900700840c007421601c1805c00000b00964001062140700142980600c103c0c2c40700018959140e00036504021100c042040030b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 656937032 1250 656935782 656935801
    0xa1e05090f011a0d080903010e0d02030d0e15011e090c050d0501050d0b062701030b01140a03031b0f0209100302011106160507050118120f0e090720150f010b090108 72
    0x40c880039100900004058a000201600e000ad004403020b0140e00f01054610071070380d41c0c0c420a41d0b0100300784040e100b10184c0c00301101e41c3c180140561400c003602201c1400030b19140041c110080e00541e0001c1004001031207003d80143c00000c03a080c40b0b642028000306a60a00c0415008282d03880010018581c98080401a60101d5428000032401c1e2610800240d24604d00d2182c3c000c60090200c60019414000364120360002d500c44203010f060000740400c0069400103440034004100c032200b4038150300528004608803c07069010f903101141509000d6000c141315040401c0368400d8880300003185088204a0700e80c201103e03403c292048017020707043c00e00c1c0103800421a8a114400020b000d0202c4100300c92612010581a61705148405103544040e0700f090028030b9034866410480302c034401c000300003401c05500800200801c5141c403240f41c2d40d840d06c06031507440d0705142001d4800ea40c10403065118002ca080f40da0300d0862125600003d020420300d8101d400030101070752f07400c210b603a480104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 656938282 1250 656937032 656937037
    0x708190510180803010b070605060402130512032710021209011d10030f1104030b01050f06070803090a0c120209040b0c0f0408010506030f010b090a1e05090f011a0d08 73
    0x1020b991001c10040003440c00300085003e0a1101800754540116080900031580000d0489010724410443c000b0580030485101c011a0412a414041c184440760194210701540e1b610404005c150854001008418082c0341010801950b496000020004e0100d0303540704a03251003019440200700b010841c0d485202404d000114401d090311190181c240800c08401540441c40c0c006551040d10000446c180d001d0035240400445c100c1c2d0410341107482d82080e100f0184581441041c41c06400d01c030310b40714003040d120016002480b0f07a469190048001d03481d41000c0008071074000e1142400300300500014010500d440e0054010210380c0d80b142c0d0760151144014028070b29541e03060008188202e0058000c00c090300c0c400300042114182501414500909d540d410b04c00c7e64108084900c5c80c0c1c43d0035240700d500c025018004a110800c1400d04080c4c0c50a0600e449002400c0c03904001c0b22280c002a040c959050240c000c00c0804020141545225114400c01e80d1045c0020081300c085002c1001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 656939532 1250 656938282 656938301
    0x3080a050d091515060810121a070c1101020a0b06010813050d030b0a0b04051c0f0506040308040308090d05030610051c2903100507031d0708190510 65
    0x1000441820b55140c0280f0a0840303038054002c940c0f00c181c040941603038103464400600301400d0859180c240001c007030389205000d01441c40d48459446052092000c5c01c0d0b0a030300441000d0100003c1801c00b4030b40105141d1029000303a0344c0c0c5282c903c041415501c00200c01950f1900047c00e0b07042600c92000440c1c840b80301504502c8828a841d00070008a00e090005c9040315101e0344002410841c030005000c500101b03030b8002d200c0148180310030000c5031280c0e5000c440c2d002045078041a40741c03030740c5001c0c00c2e4030541d650b001c2d1030b922a2000308030802d038008a0040c002ea000c1e81300c0b5401035075540c181c2d039a200d40c070604200002e14280045000ca0a00408a40405941d4100310b07041c40c2c607000005000482d40b5680c894030588030070a04480090201c1310144003130007c070030303000e0000742000031950700d03110020403080d082c0c0d4660004030564800c0e404419140440c0a06171000c1d8003a040341c59840d074a90160080f14056050030001c0300c84850b5072710f1803140d4003001820104002c0e4442d030700182130868 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 656940782 1250 656939532 656939557
    0x3040b090c030d020f070617010915030821181c020f03030f06011e020c0f0a180b210c040203180604050a030f030b091305010b031204091503080a05 65
    0x7108221a69040c441c02e04240c0181c0d004107107801160800314504501e91b807020302800401d003481314a08005000c2c241c1500c450000108482c402c07030418805c418000c2e80007814482000c10f020281589020340400b8460a9803c0003251707444801070b40455140c01e01c043c0c1069440b088401030000c03e0b8180b1142103140b00d005940b6a4802e403918207085038001c50703140d0800c103c1c24080003095a0024910b00780c083c460700b82a0122045880040d5503106c0c034085240c0b00e1000603032a8038250b80c0380b40001010b0f1113074090041c200f818075451840a0300c009100c491183c4400d424004010940003980b0140c21010343c010902200c14200b404000d51000c5c0c01410030303c91400d10800c000a01f000750700c2c05544100c1c004c280041c001c0c00c0c01001004c1107000710041600784070507464581d542c005201e81025202e01c03100301c2418140762590040c40300b00b80c02d6415010303000001d4001c420038006002114801c9506110900358802c2d145030004881c00010840304051000c000607903c500040c111005c040c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 656942032 1250 656940782 656940793
    0x80a0f05100f05010807080303190203130c031115030c0a140903150108010606050f04030330020912032b060e181626150f04120c020603040b09 63
    0x10400142c442c18144091120307182c00042009100c100601300051010a01031411420725421622000120381100302a00d500071000c43c400215111481b81c28540c881507210070302ea66881c1031010f045030030503460300c1520b00002d80032009440b58200c034400c030a6086910716180903070100f618400503003600c031640c0070400d0107101c001d5201089030080005101c41c00c940558580540c00d030a590454204c1000c2003820320409446885030300c2039406072a0305082240c1144450101ea460081d8090640000c81c8900c0d69148082c020580c024003008d0425034241d001c4112105031a80c1c1d80c443c207510503103062001d40117a010181a2103070300507810f180711402314800744c0e922103a44a810042d6032161101c1000d00c608034150030100240c151044980c0176500c902c07807405004441c1402ca114140071703031210895205420030300a21100401c44034980d0302084600b030803000e0400281048600300c5003a0802402015158080c190004100e54010030a929554540ea60030361040d030007400c0344c442c9104e403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 656943282 1250 656942032 656942053
    0x20c0106030503220302100c150c180f03080306092a092b02040507110a060603120516060c17070f021b06181c0c0f0e01080a0f05 57
    0xa00034000114001c10055881d041e490490481901010b0000e0810b4554103c0410058682d020420ba500410b4201408100b05504200c10180c646040c20f059082c580b05000f078440fa00446085031014585001d1003102e6195041c00c00400b03401d000c080c001c01d0082c00014070501d000840d0701da0100303210201254010400324a29024540b200100c560b08001080c0c0c5882030500c9041d040800074800c1d04000d200400220b441a2914207450280c052600c40d400034165501a0038ad10b4002d200e038004649100c107481c00c11900800081c0011114948003c00c224200c2e0310071000d4506004161442450b0541140d45501c01020b003804020148080407140140042030519001e00c201515114600c8280b850b00d402401c00aa0fa0140032410f401d4064086880d2248415078140e0f4800070400d401d0140c82000048051404140032a812103000c1d0341031080010151a50303007140c00b40c1a8143c00d00361a11401d90480000740074084240d404007448001260b983c580e0189500c0c00346023039541e0640c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 656944532 1250 656943282 656943307
    0x60a0e0a0f0807020f040618090c150207030506100b030c0904110418110f22080703120f05030408120a06030b0a02041403011104060f17180d02070308030a09030302 72
    0x1081d080940712410003154900039410480ca0043c1c0252088504000141c2000c43d5060b25003850081d800c0c0c1c2031341c0c0300115001c01c503100e600b000182c03108180c10752150145000007551041140011640d5006000110789000c2241c0c03107a10a54254140c400e00f540d95948202050342c0002e4003c551085c0ca51105204450340100200040e015202131000704052a10002050f9010002416030032034040100508011031030301512600e5164050030303483c00001206810758403913503070860410742c0280c00c000010058080c03d814030031903868440300d068016461040c1c80d6404200d9010b01009030400a0705201402a000f082d0300c90418400040d0040d01c0303442c3d00405110846060aa107079000405004009020341e20700ca01e03100840c001e010300e00940204a82c103000c3c5104410500441d4243c00c00603a005079404a0501020078003545646090811400d51603d480b81600c81d6005070b1903ca09035503c04a04c000c1a41d410401d100c2c507684400700382c18001c2808000680815600f800007280d480d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 656945782 1250 656944532 656944553
    0xe0c0d021c0b01090501050406030905030418020a021911060705030c07090605011101061409040510020d1a0d03200313080d0206070810360e070611060a0e0a 69
    0x8004507000d03001491000c80e054200c0310412101c505001e403428040000780c0c0c6c890107d070103485c0f00f0702e00400e60100303d03d00a8030310300444d00155070072003a821403007280e040d1560182405403002c0d800c541114070700003045080c90201e0080075004903550b910250340c5003440002070041c0c0d031140045903d407a0342d1030000d500f421143e8001441c0700d921100d00700501e40e813042202c10598040c030300800600d40b03040080c02d201c11f05010b026000c2c6001c3d1002400b480803c2c0090441651501c0043d0340c0c458110401030020000d20640e031540b1044030b00500c803503091036031410b44820b9140e16120307481c1c903c14031100081e407080d54004416100c1000030b200c1d60030807112030400a10000d030060040b41500b00001e402c04000428510400c003084040241c81c8080054040468403021098421102c0101c5002d110011149141602c1011039000f800c000503a80c4c000d005600790807043e14141c0d0785444080712006079075600300105030320400106803d45440d50104c1900c0d44000e04071814007401d541c031080380c075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 656947032 1250 656945782 656945797
    0xf0d0507090906090216021c08030408090a0f06200708190b011715040f0206390a03030b0d0c150e03030f18010314010f091a0a0e0c0d02 60
    0x1080d081d01048804064061030024003103103001036040001c000000c1d102c1c10756142c006442542d910314818184060007203160502c50f0010304040c0c0d00c0c0707042c0c1088000780d8025594540a880c00031400140c0c040c1c80090312098801c030340d0700c0d22000c683c5681d04654013101c074090300005002d0070400090740c1c0010002104400c004c00001d40200015060420080c03405910404502c854003250010b5010041030041041e2100d10428030592104d06141c06800d0302d40800a4001ca030003e5a0048075213203036460710f0004001407100c0071050701c000700f180b200c02c0543c201c0c10044e440341c000040087d009070890700303020030060044c0c1262506038a9407038030703420b00fa0300012040300e9142d180d02e11035602c034040140d040d60960003189060112500c03c400ba1040144206c1c2e0140904071a5805a21903008a62903c40c1103004101e83d503100c18180d40c0d0b8512a21034070500501c0d0407081050100d000c0510031070911b00038103103001c0741d00c0d001c491f001d46040288500700c05042084450300801251002d404503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 656948282 1250 656947032 656947037
    0x60e030c040e0a0b0603010e0a12030e0709140610080c071a040b04020a0e01080a030305090a0516060f03091110200a12022e06050402070b0714030106140f0d0507 71
    0x43c000900702601100d03005046140240d0514030b401192040c006120180540e02c4664032420200320031085004100c0e5100114160103400400124045c0e00e070080040308001d5070500909860b40420410100981008000420113a00c002000d005901b0050310010780209420a801400140440c1c00d0010483c1d0880349042a101440b0039810052f6804000e0f1501c03a0325080310b541000d854964945940d00d00500701916007001900141f4280001315000340c0c841c0464030311040039111f8414401e01c0d4040c640c000b0b80ea043c601100350340b20b4082c0040c0d140d00a9840500b10341400184440c201840c0070303a5043c054440c0580224240c1c0000c41808200100080c004101e00d601d000c0c101d68034aa140c0608640c40b03410b1040d00c45c00c0000d403c4140502000200901f0110a454100548495800107512174030118040d418000040702881c4159034503610013809221500070040c035400203001d8140010180ca81003a104c1444d04001c00750100ba243d0103030f040c41200512441520f5040b90307203000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 656949532 1250 656948282 656948293
    0x20d0605030a14010c05070812040309120c140105040f0b070302191506050d030816020f01020f040e16080f0c090d05031c06210c1d04050d0e010801060e030c040e 71
    0x31056030a1003441031005803841c6c0030b4030f07000d86034070348a02ca400b441715160701da2401c800c0418200f5008594030301c02044031074411628500f0b00c2c2006d24072051548207015040e101c848010080390320400440f001e440c1d40044089071241052100d000315040300b40b0407019072040604d80d008440c0d0340c00220390a10311074800c203020542c25041d504103031661648032a0040c3e00c80c0a001e00002e800c1010382d5802070001e422403080c2d0101210072840c5c60048010707200a544001240f0180f021031a000380142c41d6000380c0c0058907120140001046842511b0800000d007030540880c0c000030000031015002000c2150940c03c0c5030b414800100c201030045070171529a403000030032207108800c98400381440d0681020401c401c6140000f0940c105112030944000705107004964810482202004406400c00c0048010200000c002c141c035104001d450944480c4030351306142c04400d200700c00d1101d04480680d142880c0e0b918103581035071b6404c04d00140c81c2c0d05009455107500b4079143c07071083c2c20030929240000c10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 656950782 1250 656949532 656949563
    0x50c2a0118031b0c09020706110307090801060509040b0f0c0f12070807030917160b01061107080307110904050a02090a0501140306060612130b0421180603020d0605030a 74
    0x109100102c1d04000540d00002c03003483c001c10101445a4100c6490300400b5a48131070031324100c0c000f44002c0d40c1c103801e44200030052000299018a400d13040d500ca5100800c1460b03100c80411455440443e0300070005983c041c0000c8882c50b200c06c156420000128000d81400325107001040306400007040c0041030502003081004082d0f001c8041c41d081035490030100400c11503511401500900100034400000001507807100c10b01c100e071094000b07240c00c81d0040c203036543c46a1004111010304a0720034603d120b00301001c1400f44010089440741380d03108003103168106c41e400c281301e001c060052040c2c406009018403800541c40c0c0d403646a118900010000845604150300c0013043c44102e00014001d9002c01c08106454845000300c403280052200d00309442c1c4e641074810040416002c0000b429140c80c9424481001445903a0320903410001d04000c0a0508012040364402000004001c0790400445e040105500a40c0201140e030000c0c04007050494032000460325000d15808121941503610740b83e00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 656952032 1250 656950782 656950787
    0x6270818040221060d0804030501060801050c0f0702040b0d0602030f061201090b0f0a0b0a08010209131406090907150509030d020606090117010f1a1003050c2a011803 73
    0x8012081080700c045040640c04003800311031030a0200c1c03044401d207014011890580e54036101d404120b0b4090501ca1703a90751a460402c0c080c00403840b40d00369641c20480460a245c010605444242003005505030078580d00360200006820038062041c0c0010058030250085070a5000540c03007000030341c48041c4141807220504c50741d40c45201107882a1f926180d51000015000814207410040044400c00039071202c5194400038080041c42036403024140d0750000d81d03410190080c00e075024007124052495051070b80003000b96022013404444101d40080025010710f406480076400c0112441111207954441c50402c8480109a69150128602241c141014501000345002903212440079100314101100407850025040c01194800904180d4981c0c80c01800d61002401c0982041e0600103070500d644100c0703c03801000b40444c054102030407401c041500900075640200e01c900360749882c0c90104a05c00400b54207003004142c0c120301950031821203071424080c00ca0058a1101740210740e1000e85400b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 656953282 1250 656952032 656952067
    0x10b03120f090a12060903091a39062a0901050a0c05030a20010923010f1a0415050114090607050d0806010210060e0c09060904060b090315090a062708 66
    0x10090110210203420145030090544105552b1281c1070751807007000102c454105900c036041a100c20030b08440701e9812200c0081d941e07010340c41d40244d01581c000030040b01c01a103100b84a80b001c03005410040a28071394403c030020000d500b51490440c03041d20303441c1e03225419a030102003041c0019541029003071900d100ca40c16000d900307842c01c0081240c402c0c1c40e41d03150030001101148090301c14100000e0b0200400070f401040040aa01004010030f09106010000c0c22102d421004c2c0164600440c4e2407007090280360101c19220305071110740090b440140c2c01c8645a0021660030341010082c030513600069400c00048403444404e444214440c13a1080c002850700c0659042071550030300349202009241c3c8801c00e12900001040ca005513160004e0010424a200d007800103600030345006000204100e0b501d000d4540079900b201a00d03050021503030300280e40a015141e140160700026000c2c0002007007503010300743d240590140030204121141310508c0c506807804050701c048a000130b46410094007a4070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 656954532 1250 656953282 656953289
    0x1090516051201030605420d050c090718030c050411030103030804030c060e03120117030705120903010b1002060901050708011d070e060a02010905010b03120f090a1206090309 77
    0x2041401c141402d204010600c0042c4006840e05640b88003140100c2020200c0707100c80340340100349801c0300030501044581100c5070341041ca80207914602e5919145410f61007010000c0c0c00600078044c10030310504205c02d40bc0d000e4603000510400341103a5100841846c01400194040e01690046616000030301058507018000c140401008000620020f0342200c0a80d41090f00342c81c002103018400c1c80e000c401802d20222800d800e1002050446900b003071086250305a07411081c1c0c880c083c00e4403041c03c175540c0c028044003c0041d0000c80e02418900b43e2403025080c15040200046400d02080340455100d203840d10082005070009010480d408409001380c640110f41403819035003940c5400b8101003440b00d01d0803d54038020354a03001c20501881200b590300c81c20b20007048695925402d040107402000d10f040300b1202d950900c08901241d18001c00c1783c656400e07800500c10300c3c1808000210103e1390000c10003980c458103005c0c000c02e400741107100042900340f140c00c000a00c1c42c8a41005000d0158030f07071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 656955782 1250 656954532 656954537
    0x510180e1b03150a330207090b061605030706050c0a090902090a03050d0e01080907050609131410240f0309050a050d050415020307030f08090a020901090516 69
    0x50512101c012180301c0702680d10240e002041c1c4a4803908601d00a0102441c8540d0b4418030f00000400e0b05c0c5901d8410303081010b0000120901c00106070050300810740350000c0f22015030408141001900001d03001030150080c000c180d245003503181425400003203e0408107484d01e90003c1000e070b04004903481580e400610003c40141082c42140c001030141066006440800b41c0100b100342084e254006003c0286034004c0a1f9580d03081c0220b070042c605040102c14a0000303850f0b6012502401c0080f603400e081d5600504403d01e01001c0d03d080c01b50b070003440b01f11620141d549030140341c2341290320301310030f80034050b1188000301940c46d0151016480042050180c24030880a00991030a500690304080c41031180c01c001c00c142d0b800c0d04280b403e00303203100805006405004510341c903995011004105985c444900c1131f1060303149110032652406040d03401001b090f1410110401d60f40103400041e0b00c09590012212000043c0e030220329202030a030300042d030554480d03051002000303c00c400e05540c01541e1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 656957032 1250 656955782 656955809
    0x30304061e020708090d080c010501030809011409031231090f1b080901090c0b190801030512281206080d0804020d020f0303070f0c0509040807110406051018 69
    0x10b450300ba084d4803900098621030519105041d003003125400544070b400c40c1ca80f00030007e5681d02e0a1121482d4011400c960010750707403c0300c1c044901d1903441035443e01c0501800401d0803010350440c1200741d6010300040c505400e41d0724844076000101030650049039009800700c429081c5020f8480d800d070fa0003154030a0285041c8a1808021109130303400300c900e40d80e9482c01c0c80541d11210320781030040c0b0801c6005043c5160400b00030440c104004014154841e450300d2143c0d001940020840d800202800018400e8204207808000c03400e03800043c0001100e07040c034221203400c0e1942100c40b000e5640b2210070101701044541e05619500e889400020b000541c042e1820010b8404014288040103200078030070340c03c5540c040195100c0395000d04032004094120ba81d51401400c1a0394411b00400040324034020860010481d424510f40c81c501803030388280210305011059481d800b00840100c00d580d001641c03036400068a540340300710061200c00645555404402082000080510b20b0f00035031002401d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 656958282 1250 656957032 656957047
    0x22103040f0f0f08150613020a020c09011a04030807020613241d04150503060403090e060a050904030e0411210c03270c060301091d2d0f030304061e02 66
    0x11a080417011690811810155604000900c4805050f01c1c100b52151002c43c05044154002030841e00b4044204d840c00d1980e0381e900d54918080c02d8208800120702010300c0104009040350f005081030310b20003084a800d200001041916003203a5501491080086410391051038540110b40076614506160081420144190701810b40d0518400d6a003d07580e60894080c0089403c800d06000e040c004040e101182090308000b412016a40265520000d001000c501c0500d080315411040301c201404042d4a540d0f00d45090b98000380105842c0c0c0c00c10745842c03841d14000042c02c01800e00321000b041400035907100003001c1c08040d400130016008200d04200b80174180003560080001d060b00d640560240001d201d000e40d003001d2044c0c1045801030380c00300c004542c41c01103070002502d0003040c00302c84000300199007803155140c504660320340c0801d000700720484e031940410416101500800741141c6c0305a01c0702107001e1540c0d0007114103480f0660b035801043c8a124203684011032006143e01c065040010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 656959532 1250 656958282 656958299
    0x80a0e031b0f0301021c0507020f01020310121109090f0d020105130f0c0f080109060c0201180212031b0d09050a0308040b1308030c0f190f022103040f0f0f 68
    0x803889010703407292003500703485000e0b0b07a03017501101d484000c00ca1001100303814041240010702802d989200140c002c4641503400c9240500c280d0303102e2800032190641040c50034000c1d480400103a03900751900b420600c81d00308143ca13440f810030f01070028032005044112041660a00300700040723070320200710390606090000e1203c90604441e076040c0c00c62081403900181c2d18040f1101d0103250710244030303104491b40004078000f040d0b000301c19060050310103101541c92500c040f400ca5201c1c3c002c070311491180c251700b00003608041c0406611340501c2c008682c03407e030b0072012004401d143c0350f1403110940c0c4201050400c03140c1c41150300e0010300b02a90406130301c034295601c1200700d000383e01130b1206402340820120300c403030503401d00d0030024480c62040d695140c842020b0355031030364174504081ca81880f40c04400801c4890069808111039044480140f01110039401c10520400c26811403c0c035100c000300103811070005000134001460012411506145018229041890ad603442240107907100d00d0f04000c4400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 656960782 1250 656959532 656959573
    0x1a010f090915150522110309100902011107140a0801060509040f02030703020a0303020a050f0d090603020d02040902030f010905060603060604030f021206070504060305090a020f0625080a0e03 84
    0x1507002c000810500c4500d40039448604050707100c00d40c0b140c0010a103994401150440048464480703005124aa901300001c2c2481e12003a18041c030103502031240c44c3d40150f2580d104922451052620844552884000c01e190102030303000001049032816110207a4075289107400002d082e200020300032a0715000000f01c1c25800200301400200503500c10004564040c407161029640c0109859481c40d140d050003980c960f020a02142c981c070810703031030700f440d000001528503c4000541da291343d1a82040c0c3d0442c00b0350042d4401d508156000e0201040d1034140e03001540c4540d031190140e206641c5040841c0040e948041c0900b40179401c00c00501c4000e4407000100c40a5a8122441302c03205107103803000c24451401010000d0042c01030909100f0a264031a00620807501c0f00c0c1c0d0b09105503100d101c00c107a103e10200100a500040da1848048282000320242044e12004407098034000354004c044100050660741c02c452500c8002404001c00d074010f9494000d1507020340003031002420040340c1240e080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 656962032 1250 656960782 656960813
    0xb010608090c040504060203061c082d210c03060d0803070e0d050607090b032707120308010302040f0b0f040f09060f0b0a0e0702030306060706091a010f0909 69
    0x22428000107040e40c00100459a00380401070020040d500d0a4101440203401c240e4850b8840c42080c0d030b01c0c0c0c000d403004107811551143c00c04c800c00d18241d10f18044410b07034254411300b0703034200b0f0740802940028003112010700100c0c0e461264004c84001c8021200450350002407058184502c240107100041d00c9034000c030306001b40e000c0805c569036210204107403888128401110740c030000301c514072000c002c00414054095078040d1100002c0a03162a42d1501c640000c45040560340300c8100c0310780b00740d0074000c003100c0b00042c0305054035002d544aa0700c07500346c40041d6030700b034020032841d000400850800d80700d140694881420100926694400044c0c2d181030844400b07840350351174219202118145a009080e6154070410411060800b81c06840180c841080c0907817240020396400a825020488a01d00c134050541c040d42c81c55032000704000c110382200c0d80079100c4d90354030220400002d88404080081512940c1070300c90943c94003002c0c001304644e640080c10024100710400300001c90442c415801c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 656963282 1250 656962032 656962037
    0x105040b010309052e09031209110d0507080d080103030f0c080d0608060412051c11090603010602100b011d01080a200c0f01092103110309010608100501030b0106 71
    0x940303021001207001e0641c58401078142c2c080c082000c43c20049050010540620240400811a80300041801243e1140602074049101d4078800c500448a43d031191501c42e11075030382c00c3c400d0488407021905c1c10700c1d28101103901d03911401c801e20940300e040003005110300017071500c54090741c19650001e01020500014030207004904c2440c6042000040a5801011b0488410009079681e0b0118039690f880c29102550300c03003850003008408034820b00883e0081d80a0192492840a0080403440201070301d04240c0381c00741040c88031901c15030302c0c0c400031402001203500804002c0d11041d070240c1241c0f900c20741d41d410b2115400c4291440c001a40c6912a940e009003002c50151303680300307155005030512840000303910b9103090148411106c4803000d442d5624441003215550b513a0307200d091303080300c000e03034405003000700e6084415140c03010606240c140c0c02d21a180100c3c41401c0b4100300c0b2610340040e150884265140c14081c40703030030002c00618404003040401407004c1d502d540c80e420314100b41805036030b04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 656964532 1250 656963282 656963291
    0x601030c0626160801050405010605041203090801090606050f090907140411070309080607030209031b060c0601080c030d0c08160215030c0a0e0d03090e1e04150509070608010504 78
    0x1410031201c92014582c90101d80c6026440c03600241e50108501c0360070803040403800034000450681424410300c2d060f0354440d11040e20f0f160510356000d51000764204210300f0030191603400f0130780c0e900c01e01a5030010342c071405010401c942440304004404c2c602c030064501607550b0740100600d0500c001400012125105010710307001c4058800f00d0082d1014540881d458030000030018100340c0e0204445044503a504107480d10342e140c071881281688110f04005078590303c030044480e0801c0c0e02c14200c001c8194014481031400b411542d07058209035090f40000c5031030f0800269400103040c01d00c25241d424000c1d20308980402c02581d60301605024030f094042d000a0303901c00d10001c5494501a60f0300348100352080c1900d07880c040460354003a07800f0302568400908105800c2c2c595080505c0928603a5905031140d034616400c05410b14220350f801080d445072100390a405085041d0102d070403074001d60262654807400070710302c0c5d018400c0d10303000360001303034103030b000c0c010421900381d0042900381034400840c1c0105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 656965782 1250 656964532 656964557
    0x4020901021e101d0a03031a1f1103070812090705060d151a070b10120309090b0f090c0703020a0b010b0304060b04060b09040504020604030807050607030605030601030c06 75
    0xb441e00d51050000e8114030900d44607004002400030b00140c0103101a0002e10044401400d101c08207002042c590000f0782c004c4115000082c00782c0c00401e60420300e024403454186107400085d070b1035103082c0b0003414903400a111a1005643c052880201540a0b9004600d07041d03040e640c0164074820106030f0701603800c4400200349501d000380400303001004014280740e101d030b079009074500040104080c000109904000c0000c0c100790360f20b075004c10742e0350001440d60801d400364540ea0005a070040010745c984203540310124441c583d01000707100702c600a680d000b07a40341c14080b0301c90032108840320301d9110303040c0000d018006a842c0b02031a9801700c80c6a6035551240303640d140692500341682030050a0075a103400101d41c43c54044040d40c1b0440c040c050601c111070b0356100788800c842150007441020741c1c00304040030250415403c5240c10070303c0500000e20305640c03501d4088458102c0c07030341144c86810501c00d2003034450b0f00d07004143c0035100850140016500d550b50303040100f1090302c1440300f0700012001c400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 656967032 1250 656965782 656965787
    0x16290301090b010e0f0d060506030c0306040503220608040b090a1b030b01050603010302060910050f04150e0405010b0415050403061b0815010c030e0d0f0b01081204151103190315060206130204020901 87
    0x90714bc10f0003808942c07890419140894480c1c02500c441030403c16004402602440310180743c104580d031076128001c55440340d031185040c0510080400002d07202c0d00b4119030000d100c000c6e445940f25a0040900f91032419442d149a00000603402180702c1d4070f00f4001800503984180450707030030260885084a050308100c0c410b4075140200c1041640b00080410001885003422482c904a62500ea55001e803690221003080112842070048100c070840a0006122000316800c20303030400c0c2d00605195040c04d64039558541a40c0c03c0030044e13280501c900480500341d9800c00111500318a02030b80c6585c44c0618000001c3c500b20035100054201312210210740314646409030703201a010f810040d0764641074070a040420001d942031080b03504d603103e600740b00b0106c0742560054400b62032800ca415820130394021404c0701d2060800319500ca40780403c10032000640d04003500c0710756817006da4902150030012402107403004002e6910031025034100900700450881952a200c074102e40c1214016111070008004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 656968282 1250 656967032 656967043
    0xe0622020a0306050109020717030f0610140417070501140d1104030203011401181a10050f0c0d1404060f031a1201051005010216290301090b010e0f0d06050603 70
    0x282c0f003107150100101d01103200303030000c05540c0c6c0225890718109000c4416150648801c90300715410320009408902d4a10b441160402e108503d450050100707c0d5603645400c2c3c0d40e002e50300200a080741c120041311400824443c00d0002d09003400d0003138211848409414140c0314084450440903580c144101006801c8010f40b005160007074020002419050143e540754403084c040c03011409040d100c0c01d0380c441240d00403d49004e80b8100e0380c0b900c0c6420801400407181040200c00c0a029092003030a0700c0c4654140608a00c9070740c00024280102c2445016001404019041d108490308000902880d600404c1c3c695082501d403038005840140d00708060f41c1486d0303822000303a02c00e1000c0c114003105801500014000d050b250194000c417030751134006903070ba040e00582800c0820305015081110070601920b00038811000424102c0c03440b0306203210311599209070440b81c4420342c1c80b0403078a0956800f11151075641c9090301c4941c880c81c0d003140015603450036150010042030b00c40f00056440d84040c4071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 656969532 1250 656968282 656968289
    0x1503010f060303050c0c0f210a08070309030c05150316030605030d02250501022d06040b040b0a05070e130b030307032001050103120809010e06040b010602010e0622020a 74
    0x81081000d440b0300d80100706078030544020030305100e030076103101107851f0100781c1e003500d0709005010b004103500e41042101000055000b001190184404050109010100030500540b1035035640d0103141c107514214643c2030726900014011550500044400029075084035003205810380e0611448000075000c401074000d070b030030142e014055900c203039100300c2e000103821118016185103403071605194086094800e1541c232515005034071400b00c2480c001b800a01c0340aa0080c11402ea1510480401c40c1c10700c1c121040c1e4048030484031282c1044180510382d64540c1e040b00c0440810b20450500542c010700c50708c1010002442a000c01d807400f4210310060b03004541440d000342c20f8075151034290601070f04000c4900b400c02c10b42001210100c1d2509018460641a00e03408620b01c4003015440200701c0f026600104091200c1d0360b122448200042d00308269441070b0b00c1840000b140d581403c200900f924250980e1581d00c5e4080000d011090380c18180c422000200000302c05154030882c0001070488080c1d07803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 656970782 1250 656969532 656969561
    0x3060f030c04090308010f0503030705070b070305040812190c21030e1002090103060f061202090a0302061b100903051207051c0b1e01050d0f060b0d060317070803150301 74
    0x10f825070030940c0040040c0e040398000300c0d030000069a6007042c90b8880c85000e1000b020364001140c00d000440e204800b91801c10702a181160034141c80f560782900d8100c500c0b410303030030074400800e0035100c50001440347c00c040c0c01e13645028089807103079a50340303c01860065140b4001c00754010180714840c1c42640150700203040207086a40c43e0340110805c400950045c03140d14002802d00300d000c10303a02c4605c0011021240035694a02c101c0b04001c00303000003500103020055000c51042c40c00800340e40c4440c0034011206007020700c0c3c02c03ca000483c03828035001141060f640642e082c00051030120760030005440003084a4800800c00365078090b03040b40c46102c2c9a90201c248071210307500b00c60700074055201c22441c44c02914120450b1820b80230240c40d907259207070103e000440400061180300c8054008400d601810705020496649403910866503800003070f0200c40c01d80d65400308205220000407002110b41c030700c01d02c0c245411071585900c0d2081c03200400c43d48480007050245d0b10181c40035482020b81c0180351 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 656972032 1250 656970782 656970791
    0xf09160509100806031002190302070206040308030a0b01110115090b04020d050112060609060b220317070b0c03010e0f1513060e0a06051c080f0c010c020f030c0303060f030c04 77
    0x2c840c06005003400307a98141c0070b4403990000340c005411a1084491321100c000e9881810169460704074003a60003580300300e0b0041024040000010146030185020305003611000c1791004c4c0d020001024420f04d20310940f55a8100510f5414110303400300b410741650888900802c040803400040f5010b482035514582d0058070302800004c181c03e100102003419840b13024180006545c1c1c032545003d0f90360b2405109500c61007000600c031510007a801c00b8424044400c012a600c2c0c3e900d45400070b80840f42625040c0d410380c0040d00e0006c028800c51060303405078091519030308550411024540d141c20080829a0600031071001c1039019550724140d14085800502e62240d0414450341d400c0a400ca40c481c2c00f40c120b01e039201042400e0f2007401050151400580507060b40c00302142c41480c0346000f000140c42c00c2c001000965112008007004021000b0100c001151914484500a00c0c00d44840d85d41c407115001808a544900000300c126034100c502214101c00706016800064140b40c003015902d50300600d403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 656973282 1250 656972032 656972059
    0x15031401050123182d010819080f210c12060d02030a021003151e0806040b04112e020d090608010b030705091005090f0f09160509 57
    0x150009810b84100001410b050650468445250050f802c00c06501119400c858210311480002080d40916808034070048890041d0b030412031540c01d2078004041340081e00040c450324508100161005440f643d4142d902074881d10348500f14082d414500c941101c0000300c448104406403080042d11400c0035030500503080003514070040b940b14a01403c05402200005030440c07421101030000c064004c0d02a002820696003040484620400c0711814103a07280315903a4246901c0e0b0100000c2d24102015066888554486174011649a407180042d50f00100401001800d0925400d402a91100038144456040320005071140285100080c00c120307040d080d141c800d2014031440c40c0d40d540540a4401d20131603584110f41850050143d007001c13030b0081c0010441c4a038008000c40c1e00141502e06a4101600312000441940c4079800036000100c010640032420300d4402c901d182e040d80c0480703650b0140365a14011071103212004000d070400341c56282d00c07818481d0145046520b21000101410a1101c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 656974532 1250 656973282 656973323
    0x1c020a020a090b1503061e1f2c030a0303150e0a020310230105031b07080403050714010e0105220906090e0d02060f0c040306060b030a0b0a0501050406031503 69
    0x30360f1119445210764044489091000e1401c8900448014021000000c400c00b0209000807404800d290015204032041e4001122881106005900c5940b58003000c003082010b0310780c0d40683e40c440382c1802c900c516807001d69170f4000f424901c0039916080c04540700003079a82d03540515000380c2c04440400c81d00020044010a2580110702c01c0b010401030f0700e8010380300d0380c0e203110400050194000b01c0c40c0c0103014076940d60007907001d5548440c2042d6101a10400441c4203507183d0440c10044a00c0240414180304020040c00107502900c1c003c4520503103c038031031000070aa4407128440300e05004000403110b65034490401c10782034414002040c106001e0b61000c03010010030b0544144240c0390f00c1c00f9810000c0032408181c090b44c19420b039008110070349802c402d0b0071602e00043c1401300c10205c10000080020038500412004014090f01b0715100c0c42c0074a40c1e0310036220f00c079094a102c1e10303288201b400030f80e80000c103582c195102403038001000c0d240d081c2c894902041c1a04060310b859110403801c900940c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 656975782 1250 656974532 656974541
    0x15020c070608012c0604110c010e0f100c020c011416050309010306060203130b0a020a140318010c0c0905060307080109080c0120030a0507050f07061a060c1c020a020a09 74
    0xc00f91003501d1260280c00801c0c1d451310f0000d0002e065003000b40c00125105103030a411050000580765076503464000c0e4a080e00e421600340c41c052031078540120b541c002d501c4806108000c0403120a180600c014100442e00a40320350b800d045060501902c8003601014412072000e80cac0c4c16029840015012142c1c0c1c1c20701d29075a40156100500280c106140480c0151021041e0fa10600318140c4504d01c0c2810701a404005400c1950018114032a0019010120300048105444851001c002d191b40300000b11502e6100303d1310380b2109051200c80091000081c08000f828800c41e080d20000080d10b8541800103800e103a26981309500c00d608000c1c080b818003d41c80000c28454480b0070080103001e42490314031503d440d1a04c0e11810070401480002d2001d68150007c0c1c1c0e00c42c03014070384113141c00803000202056402104041d10710560300d010003042038481071010092244121421810804072410060703480004039180000d00d160040c0031170209008200150030390780e0052452001c16141c068178030091 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 656977032 1250 656975782 656975789
    0x50d111215070e030a0204020d140f0114010f05031512030a090e0105010806010c080706060e01090209041a031b0d0f05030a0318020d110f0603161e080415020c07060801 74
    0x2903000c00080761045002d544001440c25001c4e0107011150b280340c00f000025044104821a00303511030a45103c07074500d000c515803203004031210b101c0246d410701c641001044040307007800d4103001d090640000c0468104040e242c0c0691005420401c030041c46d00890090703940e9410b02c08551001050303e82110f500444244252507200281c0e002680e601c0004558200c019608180410251810f240c04540d0a1001f02681c5000741e2000c5440c1d1740d10307030785440054400d03800700700015408501ca0b44c1a1a1034043c40800b11626550300002000713520000f91180039420248100035080040c0c000c01d03840d2401d4140792190080003102515059007026030701da07031001c0b4814000030720b00403c0b44640911070900c0c03000c117900a403421108003c0c5540308152026203040c01644140798008041c4a507881500551046140c0380d0886040c0302c000703d015080007404400c5420a8140d003e540800b984d01402481c4e100c0d40150013000e2014821908100034816520b07801258046c62171301003419900400c00d58100e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 656978282 1250 656977032 656977063
    0x30f010218030d080415150f060e1806120c03010911030f210a0e0a141c0b15130509060114240a09080a050604031710050d1112 56
    0x100e0401e0010182c40391000d032407050102d05440d0205000c50751604a0340003800e101d0800041180c0c005000b00b03042c1850341d10500504c012000306100c5141c2c880340280d14000b090302d0f4594003042c040c0705444884401007502d0300580e0104207400f20b0400130001d04601c04000f8008010108003804d0005010603410052030007440f4a44424076454000111040e0001d41044445401116009501c8081d404040c0c527070200450420500e1503940d45000300c100038501c0c0041640007000c070009000303205800301101d090030218251001c0200d10800f0b0b107141e00c403a500300c0d0107100d6000300c400a56034003903030180003036032915101c01c010368210005007882c1030361a490440c1d00c12406001c00c10911462032001c15404e050031141c461103051001c00501074450003410401c11960711440620319042c1c0040064500d98000c00c2400141500000090010b580c421019600c9240c104211034000ca618400c581c021410032407030740180300d43c00c140185444030041001c0c000e0086d580506a41c0c248400c4003030207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 656979532 1250 656978282 656978317
    0x140d0b0604091a1813060b0310090c06090b1603021501030f110d030c03031517100e01110412030302090901092306031906020403050f030a02190c05040b0f030f0102 72
    0x61072030494078440c1e682c200c58411045668460a405e484800300b40c1044601a0310b5a8042c2201d076001e10203e2102515a000010070701c0f0603081009280080e68051014000340080a1040b81001c0c81110300c43c848560602c2480c810070300e0b0403883d201601030022101282c280021003008281004256054041c03c904045a02d10004100301c2c2d102d00d4800801140d10000d103900040d000742c2008003805840748107000415540c039a0b4559007440c59010030703c0c6070425044045c0c81180d034441c0440300103034030340208100704000c8108080c40c4554000e241c001c1c3e140baa058805c05200360129000341101a0081c445569100070020162a400c41119048248030003c10000c06072007101c9440782c440280104007034010302000260200440f402514083d4080102101040303042000c1101705006400442d56180f044000030309000d03107502030745a84000d141254010070490040041528401c490000729030412100241c0c0641e4800e110507014010100c101803c02c4c010350151261034407a0080d41d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 656980782 1250 656979532 656979581
    0x307030f140f07020f010c050d110609061b0c1213061b0203100c050c03030924041101050901020114090606041107020a06081e190f0c140d0b060409 65
    0x75000300c00c400904080184000b00240c9080301c416258490b040c14000c0c18000b0070f0f03c905040100741c40f01e01c00440c0c5050324902c1b0600c01044441d6000d4010300280100381400c0d0681b03440c001c004207112203e6800441c0340001c0c69014011001d0101c400c08025954001401038441011035034480c41c0041811096240c003000e0403291140703019a07004014000794114100107000030306458895500f00103080c4207022000c40208011760003048218010001016004a0540c2c3d4015560901d050341e0001001c0c4000103e4850400e0841c0d01e00742400b64482d1a5200100e0040451070800c065002c26002440072038940854100c0c0580000c6c1c070140400350082c65000d0191141c080002c0d0010606041005140d1107120010741040010717100284542d100c00000700e280100340c4070070407031255003090404003c04034410b45901814110042c0f01444141030040c0891001240caa03041e0305000800e481d214030b5070351241055000c003c0c1007903250b070740751121035005103000c0c02c5102c0d100c06814400b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 656982032 1250 656980782 656980817
    0x6080c01021f093f032d0b060c151803040e1e1e15030c040b01140d27050c0d0201020f070609030611030f192c0105010f06050d0207140307030f 63
    0x4c0b41510200e0102c5100b504042d80040600c1d9480002d1b030501e903601c03035107044d850b0303111001090302010640013000c021204181484031410080c19402c0083d442c02100302c49400044180c40845500c0e640b001056602c110312511468128043d42c1c880c000c0b854104a158900443c528248603010b62030320045944054034a03c8820600218a906512600c13000c030441c03800c0e40080d11031120624108507602503403041d8103000d802040351100041e0719a4070410400240c008030401d00d050085c8210240d884070b803074044d2030f8071800140c80c0c041da200c0c0851f20256400ac0040d8801100c01e80c0407034103d80d68500c2c0040c41c1a0707550204954140c00c1415051074015041d01340d03400f814800108003155101d40e0b400301c007610072a469288078070307445200c22000850b203920340c80c005002280c1c0300741036912010001400c4170016000038200ca8085003060080742d500800307560000640c000016074400d054200486038036441c056140d02c51000081c035108141d802207860003210300d561544040c005480500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 656983282 1250 656982032 656982041
    0x2101020409091524210203010c020307031413030f022b020109120c05010c170313031704150908041a090a0605090d17070506070306080c01021f093f03 66
    0x1051084d036141c803410700400789110754a92001e00490f800200b8030300203502003402d603080620000c0140e000801c2090615070840b10800c0b08040303407080d8915012400a40c202038000314000502285650600c01003191641060f00d64112107101403910688060310001404001e0781c1e40c100d001030003250b0002449800c0b65142c0c4500e0f5444400841914140001121a1150810103540c4600c40140d4100300c2e1000340015401501e030940b240070132458604010b8842804502146c01c109401e00c2003001160b5000c01c6080220004600810134021034107141a07140a00d0b0440b11051080ea03840a5840c06944c0040140e07082c10707500c030b0461941e1228203544900030b600f045908503403d46814030018070b5900c0e13568044500715003454105000d40c2c0790b41e481c01030210b6003440480da881e88240184001000740b510600302c24401080d14040240d0075241d038480c040d80f0501020386801020f420405420401c2c1c1e003500304000011950f14500c0c405080800b441c4950b0740302030106481101d1a03600c039028 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 656984532 1250 656983282 656983331
    0x30623060906040903050f0703120e030c0706030b0a030b010e0703111206061c02030f0702100b030304030b1b0c010b0108010608090307021e0d06060f1421010204090915 74
    0x1641009603a000144009095a26001c1782002010812803101560000240c900d440c025520b4206d1140c06061460407550341c401c0c0311006600030b0009084400b00028510709075091498049503d0855001050700d005c9181c1000380354030200e80000c00c84000c0c00f41d01900c25a4035a4090146541c0c000c06203005114980761004040c07a4080055410304243e0005d145c0d00c60704d1303801c40051607212041f24040344c0064425000d0400240d0900601d2681006401c40341c5205100421100340f40c2c40001e0b60703a110324071000305605d2206000030700b06803003030031f842030036226400c40306a640a031410f045008000038450b980c086025640017191b610f04c2000c240e071140f1b05940040d4502010b0340c00300310340c0310003c0c1000551140500d10800703160b114040f641a44502c80c0d180891650304151070241949035a0b00b1190342039140e650038100641d02c01c15000f03000c00099011a41d410050040c243c0a4443ea0b007258980c1810301c0c030f1050400c03221850420000c20302c02000c00a08040042c405c2e0398030980310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 656985782 1250 656984532 656984539
    0xf12030a0612051b01020a2909031306080414060106270501080a15150c14030f0403080715110304150504081b0f06010b0703080f1009020901030207060603062306 71
    0x20141031584c1107810342540650030500441e005903225a0b115822405c81071506030003c0168070010300d04502003e41150050340d40030180d8104001c412075088807105605c1400e040000c41c00100d011b001c5a4103c64403100c0602080d03c80717070342c0c43d1700700509000c1c103039002c2e030f6038040ca50f07440c81b54004032070310707881040d030f04140d40710301180d25070040079809880100e128481e083e259150010ba84c1d070111040b00202041c540b40d03d5600a16030500400400c440340444400707400c204060000386d0700c1d0b04101e5080d21317444148152031b00c0f447d051140e40c03a1403095004101d41d2270601c004040a207040e0145114911842450440038a0b581c0b800f0300795002030b50010310f402d030203109a041240580340c03580322150030030381214849640c0e544107601d0020283d121118a0500160400c00d040d4021096688103440c0542c02000d4182516045100304181c400ca090f501e6000c10b4000752a032080c1c04030f810490b0010b1041c003143c1e40b2030420340000c2810781140741c442e581ca10006020f0110f030702134252161f000107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 656987032 1250 656985782 656985793
    0x1905070f0602030a020d09150f0902030a0201082802090a051e04021e0d090201020705030a12360e070c0b16020c370b03180f12030a061205 61
    0xd07610100a0340028211414039602407140c2c1500c41214425501d049008001c80d20000111514001c00c6882c1c2c04005191b030ba061a07055005a2000100101195828a00740946907110300b52103203c0700d04506040d058000000901c2403000d4a900039140e409400c6402000555640080100804e40d840303404020070034a0b1480f242c00c4c6040c2d03000e07100c140d6600e4160581a01800060285603100d4200d008866648601410039540d04003c070b200a081d050f0000c0500d00036988610301c052501510510030002e03000c405142d8035508200030b414207010700b10021400c114803690030140746518041c001c2c4500303107480010b01081c81039402600268002030103102030344070701404022004441100304150700c00d11466800588480500c44016100450003100b11003a00b001030821130100700420b078060710380002c14000311508804582d08a221a4451140c0310710340b0048500f42245084107101500900405040b0404e03442d00651181c4001041005280c4c3c66211045014800000241459205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 656988282 1250 656987032 656987063
    0x4060209061b1203090d210e0604110a050109031502040f0806061f1b021206072d050a1b140f06060d03050f0f040f260c010f0e1212190507 61
    0x18a890301a0352041400303071010401d6013206e1000c0c1c0f001011000c0c0302e582700a00300411b2024040340c185803410201c88441040f807034074000801c041414080909442034019030030001111660454004110140301652a541c2d18103200380c07079540845081c1d002d14207440e4000c42c1d84d0b1076003112801001d480c0e11030000d0500d806456602e200380c80c0d40c007281c0207411000c001402540c2000500d01c01c01042d5a0781c512038410f161259109524030031a4105002c54a0468000e1900038041e11141c0007903152a40b290203681d03e060203003044141019000a441d5a100340e180c5401082140036500c000c4101d4100b511000284072104510380d8025001880a100b100c0c562075041c0c00420404580224081c01c15840d0081000c1c020610b51102d242092280c0c03000041488000711003162a24040107002c05101c14070000c1e20551200e050703a001c200ca806e88103800d907a910380e1070090359000082141d0001100c0011140140d0004580d00e05c06d4000900e0303201c0040c841c408071825180d02a03180150b903040d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 656989532 1250 656988282 656988287
    0x60f150305210d06090905071a030103020409080706050405100c020f0a0b180d03060f050f01091502070b18091303090b0a125004060209061b1203090d 66
    0x800555804001008002c1290f10f07000381d006680103409500c0000605001c649402440c01c401030b8409040700907a04450038104c1020b4080d070b030440b03406603004a031101152400d4100c911800b40e004228a24140070701c818444009285d5142d5961108101300022204500b42e07030310f03240b070030501140303600003882440022410b001d0580c1112500c600c1011208980502a04000c00181c4000c002030341c80c04d08100d0b80550040384001040e003990600380441000000074010440c5e8058038850440c000002c40d2424800c00a0500420849040684031716100ca104003800003150901803084624102159145202c54009600745515460f0010307028904002d281158026640c92018000c0c07150f00c9950820342d03070144942a500f1142d507007140701400c0f0f1850520b980c95502101500e4400064100c05c040c946403a421803094410701001d02e0340c2d6074580329000e8410042d0054000f00d0214003200c00480c54807441c07813690300303e5054030060910300741c1e002c400c1c0c00708484183c4030781d00a2046d440c900c0e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 656990782 1250 656989532 656989573
    0xa05060315061209150109020301210c0b0706020c0615061209120a020609010509010612021504030812040507240f2c0310020a020a080f0d09060f150305 67
    0x1c0c1c01034029400d02d4a0b005082d00c140400702c848a03469002040d8501040100702e407541d0140c907221600314250750409003d981d005060180703440f904482070600c0702c140504076264500801281c41c01640c0c42c00b103850050040d40103804d06d130141b449030001040140a2800348800d86480160659091402c00c040c0d88a44090142045079140610324180091200e00002004001d070306400070401400c003052200d007160402050b07203005902d0f00105020b000510645542415011190b4100315900e40120365001e11941d80020800c5400040d112182c048d00a0001d105500039401e0b04d003041d99840f021050304040300d244401c00d58030804c020700c0c198060030b08510302e00680c3c035200f00d203400ca01042c40700c0b68140007501c8140ea5004900702d000c926040041b580500d00c0c2c240c007075050080f030000195840201c040024880e41e000700b030385d0380b04801c0c9100396183c115031f1050038040c41056041040060100c0d00768441e01d00c3c00c0c0021142010411001f200c212a80b01008001c8240c241207490880e1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 656992032 1250 656990782 656990821
    0x80105010b0a18080307030c02100806090a110d06120c0b03040c030b04111206101d18190609020924060918090601080d110d0503061302130e01050a050603 68
    0x1090f492802181d41202003016180082c0300e87c40e069505102c5004101c0b070b0a4070041c080b0200010b0008220481d1100c4070541c0d00410302100100e00a914140c5151960194031045800503281c0b0310002404075034500d400c06014001c0c0c1e40e01d2070141c0c640c1801422351100f00e0b800303805800c640204100052020640300d500038019605920500d600c440020f140d4602114022013690003181070100c1413583c80100c1c0018a004407020f07101c0f1294002c0c0e03502c90603004000307200c0b440a0720b40d0b008a40d0300c2803108100e6a01c0d01481041c00c22030a1402d80018568144140e00425009001900d08040c007440382110b00440d410308000710644c041000700a03409181a0f5810490307a991542910002c0a0414000e0204034080d1010b90b04041c09245005001c5c10041e0170406e141d07814408220010403500c104c0c550524120f541c0c2e540c2c01d00420248007000c06a00e48562000665000042501001600780c690041c0c0300340981e60707250200301850100d8001e40358415000c1011074450900341000c070016 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 656993282 1250 656992032 656992067
    0x2010c080919050a06170a0207060b090c070615030201020c040e01060911030f0f0f0a0b010e0d061e151404090206030f040b0603211606180309080105010b0a 69
    0x501c0c40c1080880d040d55010903090740b08450808050050385410341200000d0f0025150050a903803006503202c03090680540801941a4001800c0b403d00039143c22902c00e402000c1c24026450519181c60015640010f0050702c88502d0480c111003c22141122801101e80581c000d01e443c010003801c00006110b032804404c07280d0740c0c500c40059103c3c041d02881703407000d10032204c0e251240782c410b0401c10700c290002c084140d001204810880045004102e254200c000c400340046c410702010016283c03480c0c50324a40b13174000c0d40b64010302c04111043e0044090010801d0514022030941c1854400b40c600c0b801103540c2540420394203200c0302d088100901c500d040000c10110742d030101e58001c0b408030b0307005698000e1000c84401c104828820103076001360700302e0030550081110030260907901c0f605124040c001d800141c4001801003a243e101c02c84031195a0700038600f0040400000c200004860034004110041070903004d0005030310304103200f014101c0e00d24896071480c090200c1c208640041803032548000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 656994532 1250 656993282 656993287
    0x30c080711250302090a052208040e0a0603300e01031b030c140301030519060b041d0d031a0402130b04030b1e0601020c010f09030f0c060306061b02010c08 68
    0x12801c1103415240b588861410070301d509411401880140704005102c40c03016414102030240544910016000c00c5002d4646041c1c4100c840c607208099200d00d500034a101c0905c07800f40101e2215036407145080724032412401807416003141074509001c0b07107e4801030b00c41a41806070000350b4041c40c40401d00d5801490000390410b0300c1049803200c000d110400800007030b61440c2044c00c5940001400782e078403900009403415989540c1d5065039036803011045002030300c100905641046115044080c1010000307106001c2c000841c0c042c0c0480007601041c0c5a0307284620080c44c05668040d101d85484c004030390a40e500c14120305030a20020754800d000a0998841400b0300013100400100680040c620480640e440380c01c005100350302011032540b2a4130100181002d02010381e80005204e0311418080c01e110741e4034200502c007620300480540c8080c10880003800900e0400045c1d08050055030001d84081205684481c4100d801c0101c80307415456910101817002c2c0036600440412060a20a0101c9072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 656995782 1250 656994532 656994553
    0x80604060302061b25050103020706110d0510060507031b0f1514061c17040503191518140a061e0f02030919050109080721030c080711 59
    0x10703195800f07241c10302181c0c1940c010b01e0108070020700c105a032400c117407010a62407491010040c081180107100c0e142c1410f03800030b882400c004a50b08900314442d040381c10795486030f0030400d02c5005004101c0f10f190304041c40c2c510101e45c5a002d8811382d40025050780c1c0e5038440180c0e0200c0800c05445d420826528900705140480c00501d00e8085110007120001010a1005010020143d40c50f0040c1049109035042400414000101d00c1401c04d5160008100c24403e5404100891144030359004281c05018000d240c861014090301d036108440d228039940781c0c00307910340c1c0f4030101141c0038840e505d09954007040c45031020a8880c0c81c1386400c44200c01c1a941400016900d0350204e40c0d1541001c849201103c00599084000384505034506004010640c038520701180301d01c0d00c0c0c00c01400c0c48590700042804000c180324003580035103405540240d43d5540c4071983d04001c02014500759440c141801813007060360410f403107030241100401c540d442e41e41040e01c407090165900c2c885684250700c144910807141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 656997032 1250 656995782 656995789
    0x70b1c090b0709030c0518041113180b010e01080a02130b031c021c090603150b0304060605150705060f040809041104061205010e0103030e011407061a010f080403080604060302 77
    0x19000d4242d5469405a803840e516021014200030f42c403480c411101d082c3d401d46030284080d0742544c45544083c2c1e0500503500c1200003100f2100410358214410300e049100c1441c0110a103005400318010640040e26a98840880c00410800d018990440d004104800f005080c020004411109204008660b41c0d6005001c00c3c41c04040e004944240d010014580110640601401c90600c03074090268045e040a20805420a03c0314030421081654840d6640c0104140c1e10b6a180075042154000f036982c1058240580640f10500a03540b250f0400008002101011000c44002580c018060601c135501e917500d20701d61100040c0242d40c1d2840c200b2010109a4031803181d0444881c0c0d00514507126800c01c3d00040100c4000d180e418507242c600300040c031036266000140d07411660f051510130a06400130b40101c5440080c2e004c0b0002d9840040380c0182007100c0380e0071180482004081d01060007010700011901800c00008440c04100c06401040c00309202d1212240c1c0010042c0000c284180e5a6011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 656998282 1250 656997032 656997053
    0x70b0a0902130b100e01050f0d15051801030308060d02130608060a0903090e100305061602160324150b0705011508061603200d0e070b1c09 61
    0x215040030380e141040c10452402441000700c001280308100841c40001012840c3c0f00100007610050044030007540c01d031a0301c940200c411a0028001040e1603060f41110300300904040c120600100c0c406580120321400c2441001030748108408841c1c4c1c03903034655242034411038005007507180c11103240c003140009078a4400044115554030040003948520384690581000b0000d84041e0940b402c02030f074080442d51081000b0f082d20b030303c401d6010050319080d43c1c44900c0442c6034001031080c0a24010000001c5c40c2d544510590000c40e020b403400c070041c0208503103010556000040421103030000d42400c0000d43c468000e482c035480d00d00007601c0301441010a118011b1980231004040c8005008001c0050a010380010a2440c0d100744e00290304100840d521190b00070901014901806c0501c0d443d02d100c1d030003c00110b07800c01c036904c07800b403a0200c601d090fa03070250207041d261a0030980c0c480c950840c0040c6413000c03188004105420a240440030b5801c103440c0c034105007109170f03c03042101d0105420048 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 656999532 1250 656998282 656998291
    0x1a03060123040320010e120c12011b0f0f03060605180102010f0e070f0f0503120f130308040603050f01061211070c09060f08030426152a210c070b 64
    0xe42c5200401000005000031b0400664a01854150a40d940c9503180001c0807208801300701c516042c0c110103c3c0c620390040c2503007543c07140140c1d00a5091517555401c02e414070040c1803503981b0450040c101d10341c1076058445510621000070400c1021a0044591203054000344205200114207071034210340020550700306580c440e28940001504204218120b0b46030710049c4a510035042d061890040020b48603804180a0526910b00107400c4241403171040448000100c480500d0b00310795280e05081b1003d4102d800303440d011901d480c010491452a44041e14100c402c903595588500c1c07199110b907805058051807007800c1d9175040c4030800c0011123208200025003070880340050340e03d10f0804040700503089a800b402058000300001e200200311902c0301c803052250001440c60700748042c1e074068540303c503c00c003440e5518031072003d02c191450707502da402d101c0a000100e00c62903010000c039002c9044c490602c07003c04010141040b000d80907040c4414a034486140102142840e10719143c01e081c8610807034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 657000782 1250 656999532 656999573
    0x2011b030c060608030301060e010306210305040801020408150a1a060c030706112104030206070507080f0c01050f0a0b061c0e0f030403060c0c0809040b04241a030601230403 76
    0x18080b09500c0403040494009c01d280070b00c480392914800807030030010300340c6411101080c0741c505014075009000702c400408010000b155541d41c3e8003280d070349034001c0d07400740000001a01e021450310403041c050186401e8a41c155080c280303003c001040420303800141c0110250006000302d0001c0380301403140d42d000d82103188007996140341e201d60380400c3c1c0d29583d2102002c020f00b1000d10000c00e0780065040d07808100e5040c65507940c240d03802c1c0f410300c502400d01d8001d201c00d0001200b41504506420107030040000210b4103900b40c42da0020314058800100445402403010f120100c503024241200c1c182d0000e6005000410701c9064a1312401d212402c13031b003030b1400ea00024040081003654455952010b0720707407504012491142e40c501600c2e03c58500700358441c9858007010389a40d682cad50721502c0c02ca07201e01c2c0e00d02c21912010b20225116003184c42078180f02d045a0080c00b080506c0c80b000c9030b22818050b903d203489103614620038580f00b82c0602082402640500000c4000303190706c2c2054012641d0407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 657002032 1250 657000782 657000787
    0xf04020f0a0f03120f0207180609020a020a0b09030f07081b0613120206012105010b0405180606101e031107030306090c090b1801120906020304030807030902011b030c06060803 77
    0x1030600120015542e0003130002c000003c460380d0f034000c1d40800ca81c1c05680800d075240d413104102d004020050040d03500f00c96616407002034230b901d43c41e0700014042e0701c0ca48195040c5060f595051038858503401003404200e0809810001480016926001441d0800c3e025692007040620a01e000d850090304840f119003904400b80c4a00c14444141c00660524032288020601507040540c810407591061181181d40f10156055508011007900100020b20004c0c2c41041580341614a0160310094546107003078034041c541c080340c0315080c9403002e0820000303252550640744844410402d4040d060b00036000400d960f0301e400029000c3e035200140f4002d4000e54010603454180b0254104407505048244180302803114104050710482c4141c0d100301d80048040f0051030011801641c0e41001110b0540c41d481c0741000310010401da950107180194000e907a058560f41d6100c1c1e0950842d03a44440181c040761030f21540c0d080c403038162054043c1580c4203240075804655140d03150300070381e2069002541c168002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 657003282 1250 657002032 657002039
    0x4060806012d060c0809040207140106050f06071220010911010f0c050a02040f0e1c14040f23030a0c090b0604052103040b0d06080d080f0f04020f0a0f 66
    0x40c0d1000c015014121250050710514103c005020b90148460003031410130003240c00700a0b640d6980c144c4070f980b60004042c44a04c940410014000c14050240e244030758201c3c0c40d520810700f041c000351410f007544039001032200d0b000c180059418036600084680804000340540650344020300600c24103903c6544500880d04003000054501c588840034041004580010180030800c000f0354207201a0701643c0016140c0d031043c00c000e0283c900410500b01d184aa03032851b03d500c100c004138815299442d5130358aa4610001444000360f0310992103040c2a0302e50307400c024401130010000c2002c42d030498414181410141c5004a424910070490655295040e05001c0100c01c0d1a07000e08045070508460071842c1c41d003014000365504000d40d12444640407241d85001900c0800c004403809400d0042105840f075014260050180400c3c0c0031b544400d01036021205d000c9401154128007400c000c4c2c03907a039013603a580014038401d070500800a90388189070340c944100c0340d19080703039280c05419000f110f006030030306 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 657004532 1250 657003282 657003329
    0x20040605030a030e36070504091109120c010f1404150e1206090a061a03071503060806150103020904060302060f0a08010b07020f011b021503010e0601140d0b0406080601 74
    0x590401241c000b0603501c45c503a4031181601c00c406815841e8900b411686442c101100c8900643c0c01410f08185014140361781d02081001901c001e1004a4002e060f5044070b01d992601c0e1140340c1c2a1501003003100184101c02401692401012140c201c03109081644e65540071615081050b0b2020100340704403401411030804489034402c001c0020010403590070820000c691710320b000d0f0350280100c0d5403000050203808400100c200420002000c5501d40d5440b04912081182c001d07003480042481c15400242c01c000c045102440b0f21a9800f01c00d90341e401040c0194081c1d0b0169039015070092365000c01000613650400640f601006c000c2c4141c0c1c40748000640508100c07410303084041500300501501005039120041c0320078070a000c1c6010106030040c940340000000c000c2c0ea000b50702c4502c0e02d94001c000c8140b28041c0d4103d40f40713000c0494161701c603080152800d10900988000c4d60034108a807c9090520380c012030341c0314801070000171780a40d98a10b054100310080e000140030a4005031100103000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 657005782 1250 657004532 657004549
    0x7140a080a0c0c111203090a08060f100f030209041e0804080d18140a0305152707030b060f03030c030304020a06050f0a080727060906030920040605030a030e 69
    0x9080c405000100f030b446010010760a01c075014070480405410410581c01071054510300080507040d01000b945401d0240e448000441c0c003440031031203603000901c140c0030140000080340d408040409040d407e580070b00c251010020000e80b40c8201441d0582d050b4480301c84401510342c010405035488a042280702c80c10403500344201010051403000d2000b12a00030311f000e130111440c10307002010203640c010102c1d40e030500691014207180106007002e0900c070900c1c4503a9101c0c0e008100003050300c45001d10003180e00010701c0801604c0e5030021b101400021b9100b504160852401402e51003045501ca00091440e0310200c3e5107142d940000c014802141808000e0300080d069030b0030b14070700344107118405054500521050008010300d5201060100b40a03060070b0441003514080c4520401d15412054422492442001c0020b01c1c1018002400c610078071403903400d02d42c007090030100004101c001340400c4001c480c007958459529203001409070b500704181c6038201e00c01d407600040078014130f00304549003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 657007032 1250 657005782 657005801
    0x60709080d0212090402070c03050307030509040506150703081f2301030905031e160609030809120a200601080d0801060e1320030703020408010b0607170307140a080a 73
    0x65018010f100c0d0580f0303280065460b080c2003680c006840c3c000500f42800c0c3c00c0155071019040c1d00002801d2018954000014200c2260680d010320254031000c0602c00214120100c3d181362400507c42e00d400248207003070080d048140c0c0d840c4140c40d000c103660a84052409940218405810080041c480c60108040717000903000900b401c102c440900d8442d540c40348201881a60030180c6040d0206420000d08180c8002040b4580015900301703da240500041018410550100d81002e0004d8a440800a542c041d20030010400604060003000e0940b08108427110322150101e46494000d1114000c00c1128020140fa4004200c01d0303592a0000d0107404042c1c10503400c11038988203c00054660014103107000004a10008000091540e007040740403c0c47c002d081010400021b014031264960017400950300327900700802440018030104481440744c064000c0c0300e210608440201d80340c084c0b01035580200e0300d04054800c0e003542458842582d1003520540301060f01c1109004070702104e4810504078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 657008282 1250 657007032 657007037
    0x7061b2604020d030f1407030e0102060907050a0519090f050414030316051b01140106120b030a0204020a02030708031e0108030711040c03020d1103150d03050712050c060709080d 78
    0x107428540c01048031100358140140911480002c0800d1541c401c410424820013a041c030243c40744c94518000f000e8441013102c080c0107104040101c1c0d41018003244c001c080340c4c0002e000748038841c0381c1001e03c124880641c184c2010700584100010301c50000c0c0c010a5525081044002210b181510300850480c00484000b21a07920070300800680d1010a800408190041d081c01c40d2103611411003060342e078400240250032075007040d0b03a241215407140505816102d2a4481d401e92012140d40030742281c0e952a900b40d4503a00c651548400f5003040d030300402c010109031054901d041c80319211100182c1c4140e0310149104036070b002c2c3d100e1001680c4205e6014100c050003551401c60685c490440d40401c4030341883c0304603500c911210342180294111140784450350000e20805002011280c40764004070380005084420004000da940307482c0519000e4503526440b20380c1040440c0d01d80e1004940d92000b21014004100190031154404001c610f2060031700c0c1e503981d05103508203040d0070309017003200800707206 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 657009532 1250 657008282 657008357
    0x60403050304030e121006060e061804022d072915220203090c01050901020a060f0609050117250308160c0807230a050607061b 56
    0x40d0380a0304894000d40c1500d4104109000e40340050100e4081c0f100074000e41c420101c00c540c02c810941c01001c1104c0440e2a0000c01152020502c100e0788a202c248a00e500d091703064200451070715901908441121280d944e185000c2c00200319840b010703065520078900801702e10b00017000095040c0b440a201c20b261071020f0307080c801412032080e590181c1031002c00c1e0320b51141260651100103032880100c005c00030010324500d084450710700951064070008182d010769090034802e540100102c80000006900400110625440b00700c0208440d410440740591035070000200c0352001d00825010340303c081c6204d4042e2040d00d100524002480500c8400c42011541e40701c070104c80b0690b401d08036504200c440e07503504c6000f0407144010581d540000c7c189803100002041d0300000103140d600b0750760301600c2400340c1c05902e45e01c00110550f00355520b40c4840c1800043c400e60400d9170103041180e106000110343c42c443d0b010008441130841d0018000900c0089486404c841ca018600411003d034a44810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 657010782 1250 657009532 657009541
    0xb0a140d0e0a0c06090608130501090210030c090b160314070c03080d0507090e0106030b0f030d0903020111061501030e0102090d114615080a0c020f0a061a3006 70
    0x1130511f42d00404030200c10148842000600400b90402900d1540c02000200b201242902c007800802c20382c1d1130500080e1500001007071218110003228824184e001108400d0031481d5000c8030844504500b420309400e040c001d04001410543e1001d024511a00550351262540c8035907408a81004004c0020050903d8041210b04050300300981540c42600c0c000c00c0a6408001181a4003c1c0404058040c801e48020880c1c09038840011421390340700347d0320a000c4800070715016586c0c070f01c2541e140c0d410072040c030541c1c44598082d502c01035048581c9000582005008800148009003600c01500c980041d010a5030340e0f864400920841c3d01015400c000303030f04d0990581c008101000d071800d0440342840103440d403158007500d007442c401008c4081c01203031410a41000100714040c1a0780805030241884102010a40003056184c01981d00000078904407442c0c0d2105000707840300391100d92541504074640100c5460b00c4580f40c6854840c800710002c1c03060581d02100044801c02c528051603000b060610 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 657012032 1250 657010782 657010787
    0x803010306050c190e06090604030b0708010b030f013014010c0207080a0f0212030f0c190302060718170a050d0302040e0727030f02010e09010b0a140d0e0a0c060906 72
    0x7620440c0c4203181c120381400201006c240c061060100c0315900c00c9010400200300040d18080c17520450441da2221840c2e41d8401c00c0000310f01042d640d8004c0d0200c600300605c045d0060000740c00d05d18203a4050110603e008240882c21202d01d05004d0f11201c1e40d0700202440c01d60b00340100b140003100c0e0b10044c01c44030b01e042d00750368584480a400404082c1540d05050a40d61a2f110400000e0001c3c030503280c1d07401c69000a2402640b20400214440c010a050a00c0c082040103001046681580181c0011381c0c03400004c03260194108040c540c0c0324501c0b03c0c0400c0d04c20f2443c00b81c2c0c11500308000140b4a0070401e040070381c40d04207a02d8003c01018010401440b8410710314400d6030b0801d030709082600c1c15519807552160709941e03003860b025150000410000a002d01240948a0b240c002c2e211402e81c10a0003051001c40300c424000d042988204020070100244100600c0414001002d0140c0c01c000441e00304805481c0b490440e0045a80480150000d100c08001148000c2160307040032003040e441c00502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 657013282 1250 657012032 657012067
    0x20105070f02070b032d07170613020d0e0f010e0c102a050a03050414030d0e1302071208070801060e0307050f041b0315060309051b030a0f0803010306050c 68
    0x2000300c104804004201e2803141e8004506c2c00016000b002e606684222042c1396659001301e8492001690220201c3c00115550303000300c1c0550b03400752145000b4005105a4400b03035204a02c805c8040c1d66a8105900c040c000f4815109400c0100c000400c4141d810f00200d440d000b0b0f009209031107111405e24220031250000c8031780c00000c42441d01083c01c0c0148542030100140001005040781c0503d09001c0c0801d41d1040040c000d0f11074800049041c3c1d842201810703500c1d0b03169050103010032503040c0640010301d4185402c48950800903005031a10100741d584412a0f850300050b400451078000c1400809a001f03030009016004300e1804030600e6402d00d00081d62804503115407401076122400200c1180c4803500060050641ca010020440c014100001c004014100c880c50810107041004604540b00340640c18030f180e00140240041d07042c00b03184044c500f10032154a1b034107101b80400b2500054810010220850160120948070b41c5503080c1074040d82d1004007661001c00d030811071058183c550250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 657014388 1106 657013282 657013289
    0x31c0903080316031a0a0620031803010b0306041a071710060f020102040b0f0c010e0624040b030a1502090618030c01020c0a1403030904020c060403020105070f0207 72
    0x1103284a11001e0100701e9100c80641b104010345445a02e80c1044d072000c01020200d0103180902d05031855002c203080c1c0e5054034042820b04003529082c0b0880942c040c055016181c24030300340d511300300303803440102c403005e80d001c20311000c80d416a1240803103154100c101d00c443c2c002400c1017480780d40480c9480c071a4100252228441c0302146206000369412910501c5800d82007844510342e01c03401d45c0041c0f03041541c540d86c2d440780d60b103031303003020080d45005074000030a0441ca00c41c840b0034202c2c280031015409006900303061810034692000603911880a4000c2c3c3c3c80c100e001c00c92120907010b449690049030344070303001080c1401d415007400e45a010002048088420741300310700e001a611100140700f607950106100c08100011079100200d007400b840c00605407450041c4080c0045e00301d800c842d009040350303405441000101a024419260040c586081458040c0001da0000703540e08600e00 = true := by decide +kernel

theorem cover : BRFrame.Cov 656834532 657014388 := by
  have h0 := BRFrame.cov_init 656834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 656834532 ≤ n) (h2 : n < 657014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
