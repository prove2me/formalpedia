-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1944
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:14:57.451909+00:00
-- url     : https://prove2.me/submissions/3a74148a-ae3b-459d-8775-ae383edf8fc1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 349460431 ≤ n < 349640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 349461681 1250 349460431 349460453
    0x70f2601060f030e060108030409090212031324020a0204050403030e16060908030430081206010e0301090b0604050717010311030607020f060121150e01050a0b030a110d 74
    0x1e0001800c1d90b00c14121980c1e00d40200c42800d600c6400611140d410540ea05459018034000c4951459036503100200b950703201c914504004014030143d0b5900c440d0700c8005201c0c09050300404da8100c140c000981070050380c0340c88071078202c5415406800c80c08415420440a00340141044d81096200c0d81200d80500c0b060095941d8141c0f20601c00808071b00e84030000d4806140d90703008102c0c9800500003001514120352160354000c041c52000031500907182e0090f040a803203203c0161806001141510030326140002140c0150400d0b203500d0350603500300c8101804da4094041c0203150b81d04140c00f01d01282801d80200307810005504200040c001b2103154085802d100f64015070314019200191ba0b11814144100e58101c04030b44058605a12202c0c42035543c6c000611401c0708800d0094003070b035000a0450104254103030300c41075104100804081810140c40c0d01400d44459500e80008520a440103104101030303c44042c1c098000d172101070700d40140b442c0885001c0ae41041c0c1240c22080046c110181c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 349462931 1250 349461681 349461689
    0x605180103170f19020a0c05040e031603050f04030f0204060b07080d0f1b0201050406060f06090e07030b13020706061e050f1813050601080d1709011113060e0405070f2601 75
    0x10f12114a2609102c049041f5039800030380070340d10700603960018020103c11941140381105850902040520b41281c052103050860156940d000c1800320410a50800c0510f02900843e81401f01c40d40b40c014054840c880c80c20300401492041000d2078040065410203114400900f000144c1c00400b40c43e100c1d4034504d10400800184d560710100420040e40e80700341000343c0b0a01d5160a0740c0303424848040c10003000c13401604090589000005e401c00c0c0710785c10604c0780a0001c2c2104800074510450980690058007049500758185a000302e03a98000041c0c90309902d041040300b0720114070384828405802c1c207030740da92600180040d82c003003d524008500a4020700c0c54808510307503107500e41012401c192040c0c1210b12181c2010b0071411140d540301c035030350300360788030300504000c050303c8500056004100b10001400440d4002c502540155208540c08086600c280c4800a40c007404804100481d10101c5452011581400000b01c0d800c0c4110210041d24541c10698407600703191600c5109000c109a01c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 349464181 1250 349462931 349462933
    0x90602030a240503030a112103040302150c0a05070609020405040503030f010b0f0703081807140a0605040b0708070321020d1409070506090607150605180103170f1902 73
    0x410b14000310031041d9402c800ca16a01c0140b0708141024000f0340c9038070908040404102e03a80903d2510b06500340018450030014042007050980c0140d0101e18035002290103602602445000c0d500e5030030801c0d01d5a00c20340001c841b840ca042c60030741040d2010703004601c05594440d543e20102005840354828540200e004400071600d0789018211213016002c140c00c04a900345042c01054000d141000968402c0b07036060500c5c807a40e9a40700899040c400e04128038860522552000041594180000b40c40d00c03001601c85440903500c0310003d070740c90310551140d07007000b0004009d03480c0490b800001924000b842803918201c20845140021041c0144404142c0ba4550003c0d24608401041c86946101018090040903e241c4400d5a81d101c80c043e00c0341e80d001e11000201d00c0b51554400e1b00711000705034040b42144101e90b5011403440204a540141c0e40030f40c8281c0e610121000e400c000603030407641e0110402d10300450b60300000c100758000360880417210002b8484400200c0040a02109074110b9038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 349465431 1250 349464181 349464191
    0x60901090c301a040606030501110903030d020d02040b0f03010801140112020d050c180105032103070f09030c06020c0f04050903180a0905010e0103170f0301090906090602030a 77
    0x105050001448507030101d40c10402403036500103000002100065100c1105809212800302d605180010000700070202d801d81c54000100420041a07a100c001960b000b90000c001c00c1f800555440740501c10404115415401400104142c403605d4008108002c0310714009410180e44203c0c0c0342164020103203071801c4600100041c40402824461514513a8041c002c1140d00d5140003183d0100c0b520840000e0700030303104000c540080c8101042000250380000d4840be02d400c00341c1d005244400340030700845c0c1c0b2138050310300c5201c083c400015103000d03a410404010f0346913848166083d15200402c0014005200007400300001003004400401c000301425000307000300e4007242c070420956024000c0c01e14402c626103018030084d488004180c0da9100c6c4902400c04244030650001146140107600000c1d05509080011504003988007145040707074458a80d20752a840d80894110f02405a1a40200103440070300042242d81607541043d481640540c00018001601c0e40b00c18059a10449030b580d00c281d154 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 349466681 1250 349465431 349465433
    0x9030322051008070e0402210a090b0c0703170603280501090c060305090106060806011b0203060705120901020a08040b27030913050f0a0908120a0b0109050316032306090109 76
    0x12103d646400300b01254114500581007031840c804201403803040c3c507481d05000001e102075140b0744c2b14400c569001407920038185840c582ca031500303911481089000442070300ca40d41806e84135480e072a0141030010007402c05242c40410085118200090981058980740c058a02081c1d01f0b12481c003110f4025440c4241d4541010009816a4000b90541585a02d428403c0040c160300a00060f0008424600500305007041c1f03041a0b1038200c102d2010b5071601030003061012007a0400c008058507030141c40805000e0365440300d01401c1f40580321a00300801c001000081c0023a840c080034503070150b5000d080860010020f42049629000c54507140c40c0303540300060780c201a00e06040045417440011009000310300e005020700300d001c8005092441c1d0191602e10000410502c2c8090310034648140d40c50807441c1c40e0000400002e810152503050100340041e502040908000c0380040440416880210a05246a54030b443c80321220140ca5901d04c50184c080340d403110184000f50040c4250b00021036012a2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 349467931 1250 349466681 349466687
    0x12021c060c0206270d051e0d02090108060a1202090a0e03070b0403090915120501021902010204140405010e0601110c1801080f010c200a0609080c0606060903032205100807 75
    0x1444d0000c2610800c000c0c604001c0c0d800c005602441e0b01d0300380c604130340c9841280545070f2a903402100d4803611100041145802d018a55001d8112460f007603035030304c259440304001d000301c0244c03600881120200101c0c10201604140b2881c58100e0502c010001d0a0150210003a0848c3c1008908030349038405901408185944260001c0107032100c00c00030841d000100d0003510701d48665101d854900800041d5a0003070120a5064440000003035090344414244414020b000b513006000700c503000c1c045601440d2190816200f810306039884104045c1d0140c503201e0064035503180d00c50100341640326802105d401511807041c03000f0440b41a600ea00c00ca541007600590501101c3d1821a174160300d8284144042d581c086400d41488103007500c200510003100248608080c0c1c602c10140209007015410410090300304000c290004100c400e0742c10760b4507130034204102ca100d00ca52650b415441441080340d0400c1d070100e8040382c0700e0103d04100d1b8803981c0d800400c6503010840300e94000305984c0c0c000c0002c2590 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 349469181 1250 349467931 349467961
    0x403050c0102010e0c1e064317070f0204180b0a0c1e09080105070e1f020c041d010501030f02120114070804031b120906020712021c060c0206 62
    0x40b951340541905504000840e030802c21002c19801c0d8441080036003000354956030102c620701601d0b00300d900708000108001c041e003040b0204600c81040101224865000c00e03000310300d22120b0380a940c94202c1081e0710740c0c032089600700d120151502c00803c0007410041c0d48500c00d00000180252120440b058030303080240c9172507002003c062500741480080201c099008081903041c510350250108005e56400085810032095048004150b10340000e0100305500011008043d0500315000708103003d400c560041240791a046c12000b580c0103107000e42c42c0e40381c140c003c10a0303500104003c0352400d0351042d580c0c6c01e4410a034019a031481d0201d24030302c1541401e5658130301869040c0002d2008116042c803030039690b54002c0195040001c00b402107010584070b20384607405000074420040d01c8150508005032040e0042029401080109000244440c00420050304840000b841401d0503c07150b002d00044105a01c6100c641c7c10500c2c2d800c00000e038180c482c0112400c0f541d4010503240c580b094601d48192 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 349470431 1250 349469181 349469201
    0xf0a0e07060e04150308030a02031807080703110d0309231e0a08030f0717040306090c050a1401090308070809030d090e220f0302010e250512070b0a050f0403050c010201 74
    0xb80c8444045c404034032050100c0350041c1c001800180d881e0f540b18842c21400e00b0000c98400c59000b0440300107004000040d01100747c0f4002c3c900f0302d00e010311180811005c44941600140491040c103010468581c1d01e103002580180305071440c010801200340003c2c526006100c2d0513002441100c0078003558101002c03940d0203004100004c5142001e0740080411900a6000c018030840052100f65550380129050318001e5034811024804c031225450082c0714102d07a40174042c080c007555100010740b02104040004010750684800314018295100e0710855802242c4c00c1d1902c02c010014a800780c0c03020841c3c0500082c443c3da44601d1142484c501801002c400350401000c91800540d0000116030740190746409a480150030300e0700400e529099015081c4140010040d000389117071415500036806070b42805030500f1031140200c9031140100000346d0400d411250281d8001d66040c0054807101c1e00034482c0c103445090507418481e00c600e030828946e005410854003600642c940030095602401440100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 349471681 1250 349470431 349470461
    0x1d0307030201060f120f0623090319020c0d02090604020f0c07080705041b050d060f0603020705070905040b0c0a0905040203070507021c03080a1515030501080f0a03080f0a0e07060e04 80
    0x41304032510345140c0406c101d03401415a41da203026556081078a805080c48003686000e03d00b0484c901040c4040e1681c0169058000c444a25074006283c01d201003944280d08400034601e03180054607809000096400a02cac480d046035003001010620170318038000d030a00b810110700401015080440c614184440c60384018025820f001d030b5005000380300f0601410705500b03441c1890711014841c0e49400940059888643c40112038540441d600b03038190010031006014500302e030a01942d90150000319041121301906200e2100c2c08217103840724140003440715002d5480d01c5031005444400150407640f0070358032000400e10001b405411420503803080807e4500101003203130015056280504020801400708034400d5032451105001c03c0b003600007601a20442c4903825840c0503404001c2c0092100307024548083c4161070354200d0458000a000c40810351596032000c507600d8280001e512088080d011406c01c0b500e40310188200b21007088081d004018030794500da100130001040c0022181040107903660 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 349472931 1250 349471681 349471709
    0x13120c080a0f0e0d050102041715010308070f0506070c02090a0c140d1e050117030307020d050306040605090a05071b1703060105070b010b04141807031d0307030201060f 74
    0x1003800c0406440e03101c500340c24216600b0844100c100c99480810001c5540584200344060500c501580680103413150071a2200324000415070320b030f50b00e4003401000d4103016184801400010300d48405800d14038812080e50100741c05581d212820110211031030760008628444100640c608048000d401034024042003052485a000042c0002440980c8a1201030000b403050360b0420a40e10404481c0103440c8656081e80000d641c0101508083c0300b500400d4a0341502110032000c0481202e020b004290020400010103c00070359850b000108619881951600c0004082e211422000c3c821030039070500041d2440d140b00c0161074035220b4028056920142c1c5103080002c0e42c009200c0b20030382007107181c80c0d4899035840300403141e0784a0201c004011b40030b078100010349541300740c0250042c7d81140080940850289052080926169981c0f111540c101004501614002d62042c000d07944100701c0260201e40401d039261440d400400100d0041c0e6480908012001a2180050140c18008c4d00070320 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 349474181 1250 349472931 349472933
    0x912091c03020718020705010605040b0117150901080109020325062007030c0e090a0213090614190e030703051c0209100c12030509060a0f0209060313120c 68
    0x100030030404980d0324554004900900c107060003041500000c0158102126491441d1034008002c0d4010002c110351325030030043d001c66540b5080c02030000001c0c069441100f50740c0c101e20350302c02001d001742c528000800c074a410351550352242c100c203d0107800c000c0008528428075205040c0f0301210307030100e4406501c40921000003540d101490f4001c0700d1003450100305030108821444ea2640381d40001006a1040c40c10020802103280c00c540c0461741c05205000140c1c1d66050056122000c02070001c3d4040a0f58001c0c940c00c104982c01001900c2c0140c0001850441140d03040900d0350341602c50346d101202c09105500c20308114011400240d006e64003071814100b150354042c2c8a03003d540340c2c1950180d505841c3d00d074070948940c10741782c403640300400074030743e10b000f9140162025238143e5013940e50401400b01804002d00900469000702c40b50030090040c0c0d40e95003148401005d00d0024044842e40030800004103640750405140903500320f01ca10090f10780503280070175110704069009030601c40783c189144 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 349475431 1250 349474181 349474189
    0x9050f09070923041409060a021305011b0b07050c1e06040f170301090203040c05060c07090c170a05062e08040320010e0105070507050c0d021203040b03091209 70
    0x4422110020740501d459031020400c0d83c10031503051649a0400d281c12061a19101c1c4031989a01070000501528007685038141310009920490341420000b40d00194200429407240e15003107510142400ca9005100c0550341d001e06240b4180c443c040003445c003141d2029680000d1050f5a045d0003840301c4100d803500c41c80d4040752a184010805440540035020307038030a1042114001001c0c6000c0309e40d080d900e42c3c640861000030340080d102514401109000890503061a00480352081b2444004100030f0b0f01c0c05841c0d4015022888605042000d50b040b00100040c0b6010168015002c045e40403c4074500801848440860140c01841c250f202080b452007044140071210f03003049075031502e80a26611410203580c14141c07c0d203200c84000c541c0010030103802c41944002d03020f400320760090056496800040744c041c003a4600207015608000c481011610f45001e5a98031148041c01504141a50622050a42d04943e03c1081550800410001d4140c4c0500001d0100c00c50491800d00303201c0040003003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 349476681 1250 349475431 349475447
    0xf07170a020d050f060c0d1505030a15021603120b0105091507020a030f0b04050106050303091e0a0801020406081b1e0702040b092409072a080a09050f0907 68
    0xe4060b40034a00e078003081c00014401c11501c40c4054044941a0034452000aa0380c0d0208503a4514686095041c6c0345090782850700804403a0300400810350008561142401ca0007405151060140e0810903084141e9580c400c0381c0c111030281d11614a54204041d070384040d14602c410703d504120003046041d201c0da664001d035030504240c4c120501c1d1112114800300351580003e410140c60205100003420411005074103440c40389220704002c0c4141943d45046c15a0b80c0a060b4059a0000001c0310403010000d24036400c0910000003003040402960ba506010300b2030703210341c00010000e4071aa0070080141c00348004824442250f400240c0750005642c00305000400d04c8089916070480003480c1c01c01c0d580d964000e9414030000908440c403d00b0f01940c9028800d1080d04c1040420100c1000940c1c00d140820385584902c0382a19070f0b01c81810303280142400d8500701c000442110046141039404141048068020048540c031410101c609190402c0428403643caa01d91040007681c040040c110380c0b141d44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 349477931 1250 349476681 349476683
    0xc0e010e160309172101030305030c16080c030c070b130302280b030a0c020c0a0614160c05040f0216062019030c020712020d0f140f07170a 61
    0x18030044264442140a0303c040b050142c519800390802c40300000008000f04141c2004500102c0c0c1e00d080040e1041843c2c000344000b40108100b80001444c03610040f008110603440040d0180a84100f0750b503071501c0360040410142c0d2940f0100b0300000d880d80c10000c140141904401650500f60ba1008001d03105071107010090090040700d090848030103040480035508081c0080944110742c03076409059880c1c0045882800301402d00023030307440180c00400c041e00c42d1180030307080440160500b4019500008030440200e0701e07610401a183c0e00b01c1c0500884844240b24030b103101801132070001013209450083d04c8505500c4d00c10441d400e0b4201c1c6140e503240229501460104e03007442c1221034010400707521a042c5898070320004a09866500505400a4200640c3c81c100720000101c1c10132079aa00143c0150149004000c0480300075241c54250304e80020701c01c2094041111282da02d59000c10011080c0a40d150b022007918a05007009001d00c00107080420705481c41c0134840300400b6611490488 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 349479181 1250 349477931 349477951
    0x901032609040207030c0501050a0212010b0c030c0f0f01060f12030e0123030a0c05030f070503060f0a0e07023d0f141f0302010f11160b070c0e010e 65
    0x320400c014a60040d540c04201c000c10440d00d4851504000d4012079003402c0803241541fa2500049210105109a50b00030a9010100000341c0c241010018158170034901c103e000d100601100d42511800c000c100e16208a1001426540001040090941e212a0014030403201100c00a00444558074891607910b03405141c0740b40100000001650004d004030b0004030441c540c1341c0c580c00e0161440c8001d60084a03c0340041007240c2c080401142d2900040e646c448082071a0340202e001ca504c42d801079500718000a083c40040690140003500d032611a620642c901c81240d07040040d4150140884880390603140b0001c000006009441886890722090003008503c02020703a05a104040e070040b030300c1c3e0300c0d848400c0182c03400b003040801504108490102c91036401c6480d14854081c0c056450080b280d068603008040384840d00280c0e003408035034901030380c203100d407187c822402045051040014008050560340e1100f203401c001c00b03181c11607040614500d0f4502e004014000c3e101c0310709030744088020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 349480431 1250 349479181 349479233
    0x1706010b0904021612090e060316030213060b2109120d150306020c030c1e030f030411100f270e100b0f25050a02040509070503010603050d0806090103 66
    0x860700b22400c01c0c0315000b811702d01c0124081d01c09244c100003554141d5043d07200e1217450750f5544041590700d00c0e1540e503641b0600c842d100d0400060400700c0c094421215400004120f1039220100658190800462980c40da0403814481103044030075586640c110b100c0d94068000ca10301500707403012500c5000c280030301c0d0980c2c618001c6900050801c805014561000f07007990345510403c841503a07130700000002c030503078050343c0c020440b2001e0300101c4040e80f403901d5016600f00b415005045045400040069404000380340401e03026a80d0380d14600701101c45510350841525051100030018500d1b080c0350100601511103001c031503084142101c00302d50f00032040e05410780c0ca2078400d8110141c180d000d11030780395001c41c2c10700d6402000740142c17401c02c5d0141e44c490350b080115a10001c81c2d1111440140540e003100015802500345a040960710400340000c030b421066442000c82c0c2114425842591a0b0b0055000090080c1c0d00050300c1c2d400c44011211084294150b46550601c001210940801d2040c80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 349481681 1250 349480431 349480447
    0x105031515041103041115210601030902030a060c12151211090106030903020d09031e03260415060b03071d120d0801060504060e011101020403020a0308041706010b090402 75
    0x794224803000f040c80d00c10f298417030909140ca03808000020304240d00c00d000a80c20706105040b404161800e4801142c0000b40c80207512a9a00f8082c0003d00050b041545402440004d0303102045941400c030303c20403000901c100c0745d0200078905000e40070b00350005814000c2c039003a0300d62001c00080c19108a0b1250140e280b02c035250003041c1441c46100c064001c0011800024450341503030140500741d01035000d03982417000b282c03812601d42c103207800001c00e2810781810505025880c8100b000f1003901c00d05014a20b050400d000101c00e0600340c2c05200c3c646580000c000800c030850f034200d010784030b084400340165424110030001030b0000802100c10410030035809200040d0391496003140708005050080c40041c0070721001d0f26400401800700100d88650000243d242c0300781d0484c0e084903003d5480040d40c81a9400460340a0014200382c50507640a00022000d070340c40301d01d0807000b58840c10714143d40790302d02860340d904100044080000c5030030000041060007080811101800e034201c0b00141d4910807 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 349482931 1250 349481681 349481689
    0x8090313080330010603090203122a030a080105150f1b010510140d0804090e030a120204050a05090c27040612020d060c1e030606080105031515 63
    0x3912840d0049841040000912041c080024100c00385a02c500301c0300c001e0703040d04020b4208026803c0140f203076100d2004202c118400d5220851040c4000c080e2076140013074890071007003500301d1150758506c005491141c40590070035918100103a030310380002e9414041c0000014020090500c1090301a6048450305202e8a45040440e00f580c03034040105500c031720f4507040d000018096620920065840d03e008030b40c40c0e206035480e080866244890300034500c4004402d0207124250070300700b156060030500003c2400031483c00b42d112030381a501c0085480d41140c131801810b2614070201001814410801804035407208016001034800540b1040700d15224440d10140314411928040591881d8034416022020150a405407550080f201032040580b514400d58020824000013548810941149d07000a016070700280040041410940900a000c0d01d20351710b0881c042c40c0f1940041d0351100e062103a1303034009064a024020640003448420f1308410240d40356900078001c0c1d82039110404e521700039951 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 349484181 1250 349482931 349482937
    0x60a031806060803190e130c031d0f071a04050d0201120912090f0b030412050c0d0f031407050318010e031305270c070201170708040506060909030703080903 69
    0x2038001c4040041554840b00e25449400010390441d1010800b6081315589209180382201010002c00d4007400140c42e100c1d10000700380c0d140440051507151f0b400d00d0800401d00039503003650440c0c680a415465010a186800c0696903000410b5628160005060019400303040e1401c2d1542524005030790a414001611a00e1098a90070b04041c00c20440c42c0401401c03603550503c0c1c5596880c1c1c14002516581c906590007458001d500c0001020f03c00174000c02c031550720440c074024890818520303200c801c0d4451428002d03140e0204020030f03c06182c3d481003c1d410310410a4201c210301c142281810701d040700034900c4c07001500c41c0c0c602e41d80a000c500c400c90000e5020702328000d0b500b0112650307003007007818002d8240014440c41e032185c60035805c010070b00007400c2c0c00d421500f001045c0a6625907602c00c001200d98204d45000d90400c00c00c00481042400d025998034041e544940b40e40303c0519103480c001345004d500500043c02854a02c0900041040001c29281030a916041c03411603607803218052032440c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 349485431 1250 349484181 349484183
    0xc060109050618091b01020727021207050304050c01030b0f060703120f0b01090f0e0c0304210e0f01030606020c2211130b041805091005150102010b030c060a0318 71
    0x3180c50240704c284131001031864112040c1d0100442082582d034010780c0c40d22058440e91154400300107407010b080300101c56000c0500d401c460010308060056a150a1a0104803148804100e000090105003c01000080c1041600f468184445031003240450ba00a12950840340120404500103040600a20980102c80000b203420040e003280c080002c0b01a0200c1100580820700b00344c0042400d0320a4000101502c02d03042c0c0110301905c0b006040000760f4070041050324400104846040440b1000304480c40d1042c0943d10002c1070140c51080002c440c0c140d101c182e05151600c0020400c05401080c8145040c90898101030042e030b4015560500b40aa40ca8042402d803411030008050303140b035400342211517010607400d0720b41501c801622281c1d1055008928a41e00d00c4502c0548401490304010751100b08603058603d80c40390703104170405407074040c1c0c0d501c03080c507500c002c119881c0d5909104a00e9203040860041c420000440d010a00a00c18401202c041644601c45031580d442c049101485003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 349486681 1250 349485431 349485469
    0x4032f0a030f02040f0c180501020f030f1b010c03090201031b0e040b0102210a02070803180d020a030f210c150c0c0f0f05100b0112050a0b0a180506060c0601090506 72
    0x30550a42c0b000f0b000448400307400c0c80302d47c5145800300c3c40354030020b038107040040300900541c9800e075a00c041d42903c3d00017010207101c840300c003880c650a1a200b030041d10a070742001e8501240340380d030a100140998400365184140031100c0c0b802d01e0200ca41c000e0401c41c2c0c45009540c009000424400102d0500d40542148840011106100319250340660014800e04ca42503081c0d4074aaa16040e11a85900c0303004856200c4d211200303610311007480e0501a8071502031004000c901420741d25900c0842c038070385090b01038a41d43c04010034207004c400c011036031510710f122030300e01f10126070020358900d41c5416000c40213201c03444d955020712078440e0083c4105000307107401040d900c4056095140110030180403078400c0359640180c00ea0a15010441d000b00c02b903568050b1540510b1640d1040f00b08010303c07008010f10509034440f410240c11b61070314032008001e4401d040707180f10301c00310384100c04081d144050107179405039a0411001c03955107004200d5506450203408049080e4a07500d0015a442e02e01d8030303402400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 349487931 1250 349486681 349486691
    0x1906080f07090c170c03060d060e010504020a0b031006050c030708120a0c020604020d120306051e04050903070c0506070f17090102060f0105060301090c090b04032f0a030f02040f 78
    0x403801000900408403228801c0c20302018aa80c40304450a8080c0c0ca400d018500c0484041450010203401a42e801000034200700400601521054240c0e6241100e09521781d56803c140019820400300001c090445034884074a9800e00c8025540811082d2103006c0400001050b140b14041060084904580d00054100c0e1a140310300500c40210740150b8003291701c0c0e480c2c5403e00e05024004103d051041c0d4006140c1c0c040030540303032203000c1d448100090110805507201d0b40481c840e502e011122400e0b01d00001041c00d24440e11061004440001d0085022230b40148401c000044000b2582c8089d5030041d0340c0d140d115501460001c4030441b80030307001001c1c048400000360345440c4000107011207110982c00c07140c25031a0103150031110360b001c3c042d4640244e4100300511407403503617800010340346040e0328060003065511800000707550400d4000b100c100201d02d080380c0030741104181c4502580c0c0e01d009895026a19580040d1002840744002003070076803038000180a65550740d00c06940e407080c502085c0700c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 349489181 1250 349487931 349487953
    0x1090b090102090a08070e040303021b010c05040f0e010b071101141810050a0818120310080105010b0a0e1c0b040b07020f03070506220213020409061d190608 69
    0x20103500303d008554000e640f808000030300a840001c030841152800c1c03072081004d49458504402075800403d0407094041113492441da4003c0c00d101324612066156151038a9a04204503c0c10803040c4d94001000900581c0040c408411902c0c200c1e686640d000c64065004100c540041e42c003000d0381c0e580c103c0114004244500905160a0700c030403c10b8045641984041c0c00e0207050ba8540904480c100002e0541c20000382c1026403481220480111401213034410043c107440c9420690040720b40501603010044104095502405080c2c0500500000e01d414460348a000400190520b45000d1040300c802003903d59004040303502e0900343d50003039404141d52800d8204240d81ca2000c3c1c5011340144500380790249644c5000c010780e40d6056108016003640d4458854130844541c011031a0340340d41c080901c042005aa400001190101c030661000d62100e1614100c58100c86441c0e0046000705425020b2442d0744884145039a8030603042d08400503120412802100280065000700141d032094100c451 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 349490431 1250 349489181 349489183
    0x3030a0603050d08090d0e0604230a050109030302030a08070e040515030d0203040609030b040501020d1805060c07020109260115140607050a0f0f020a23030d0503060103090501090b09 80
    0x5401e8030b0003041126464103083d54101c0e04141d0844175120f040c1c101c4d903485c2c808148540850319407201e004101908040c0c5800c0c40b100c08808000350030b41e0903a6105803030030980c2094280a0001d003024240200c090b841d5490207074a074455502da0804020f00c0700001900140510100c001684000c2c1042109140c1942c080e0090005065558482d101b0384080c0861144004125426a642542c1d503284a40c81c1d40d40d2055680405481154155028031402001c1e451070320901045207401207801c22024214117256003420f0b009070258115000400c941c80250340c02c00003050446185141c07403c040e0f460070100c020300c0e0381902c500c0081c5500741001440698138126030303c1d050ba50f00480142c1030301c00e104204070a51080020081c12500202400e1020600d240701a01c03403103003d031608070310083d580d50000b00d54003e950050703060424000860017440c0d4503020341085002e8194028003030059985005002e6000040c8402c0c1015120304071802002401e40040d03c3d5158000c242c40900c0c00c00008035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 349491681 1250 349490431 349490441
    0x303090b070923010906030e070803031e0a06031e02010e0d050102040f0b0705120901051e03040309050108130b090f0102070c0e061806010c0611030a09140f12030604060803030a 78
    0x5481d421043c1900b00003082c00d401e044004a020507143d01100c1c9242ca070042e00036000500c400c80e0103000c0c6500c0003482d048148015071241c03c2201d809612508040c04080c000c00014200540461818038140009114081c00d4405000866000c0b004043c0d2440100d410203c100b44058000ba10902070718200705c41500640155180140c0c58500d064540e40f809545000380b80014000340c4c00307018440780082840c3c0c0240303002c03038061400902d40000d1000789106800146143c8403118800010801416400408440034010034078001c0c3c1075003811902c40709101e83d219000303804080d0b900b000c41d04001081103400384094001c1e00039501c0300003e04004480040503ca0811080320380d40020f4002e01e031021420340c2040808811a00544940c80111050010324008031542c0d0b998401da90314160071180030790f100d501081000300d5103c035646454500c1000c14141a191a8404502c29a00354400300d01c1c0c000b003410544545440303584490003d03002d080c5590080406000000a110100b0759035005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 349492931 1250 349491681 349491689
    0x2010e0606030a0201021906200406020115230a09090f1a07020319050d0609051501050f0f22060f02120304030516111c1a0105010504030b040303090b0709 68
    0x603a14180d84030001d043c2c0303610050310001d006030080d16081307071264640342081c9070301030040400207800ba00740d80303500141040180504440500200f01000781c0c1d5424082d0440b031880a0b8102c0c5402c500c0c2c17268490042040031005220303d0201080c440468a83c40b02c00c40c000e0094090a000200481c1840040f81c0e841400603200660f044c11031100060700204010300411540e4011441d00748280011650f06200024070003c1100030440c2c10040c2840d0701521014007a404400580d60801e0740e42802e004003001c4800d8144441440000940744030358040d60140404003400d1030b40c80400296403440300c03510680840f10307035802400c0881d919901440040301088113800302c40300301040111581c6180811280100000c00811048406615030302c0118842413081c88002415504d80b0001000c9900c295030b0900c5d03e0100c03101020a02000b01d0503006092107101445a1035414040020468031482c04080d00000d051030129003018070981c81218500e8014000c61482d08041c1d000074185000342c46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 349494181 1250 349492931 349492933
    0x3050a111b0a050a0503150709030c23090402060d020d060504050a020307020d02060c070201110c12010b0f010e0a03020f150a03060509091501030b0903040305070801050a060609230607060c02010e 86
    0x1181c01e003004040913040d6000140207054410460f0341041e24610000c4c525801c02450450000002da40b00ba90b80000d00001280281c140300d10319203801100343c0b40c00003948a03c0f94003060102580f6004d0449084074180c440c00b581d69920015090040c1209901180c1c006280c4000c1280964941d0b01071070140c6039541c281c88107408841c904a80e2040c05403030b1907030b5100042042c00300541c00f9883c00d2080820345000d40d0351a401180004a000f42e0000c0072424694441c07400703a40c540780621800c9400d21302420315400d5500d10401050071050680802801000f68a403140c406a50744010030b6030a000100e070342a41c490f8010f4008024080714803400f4000d405400c0810000400400c1c822010342048100e410079a02e16100d0600b04c84018100b002c0030301080001002286017803186030b018002e40e00000c9024184042c1041c1142d0b0769902120810020180c103200c1d081a003012004a15041c050704101ca04140380000d040f8401c0c2c000040c000c42c0b506c240c0e07440041c1c041d04580c0196020700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 349495431 1250 349494181 349494199
    0x50a021002060705040509060a0306090b250215070c201311070b060105090a0906030209060301020a0206070f0530011e120c0509041a0703060f0303050a111b 69
    0x2034003681e8800c07050b1240008a2001c1c00244694100030010317546c0a400205200d280d150b80c3d455010850f4445030040d82c0c10700211040003020503042040d5080e8100c80c10751020941e1814038000e48841507070b810905203800c0c3c0030210b0304840c4641204a03010f60040303c1000d01c3c07c152520070301080140312149004854000e00b014480485100e46500322020600051421003142d50f0200017400040007075041c00002d006150703064031600b42c0ca03000307400041d100080c0c40d403c41c010480e5001c0c00801079482a0300420180451a41c00320342c090b04206e241c24410342c600300c0310000b540d2a014001c1c40c605440030201803964804058004110201c1c002c07030700003000341d0700c5600300c2e45804640c10001000c00c3c10100c042007080202d150094806000c0c000c0d8140c05a116000201c0d000426902501c49941e07050404161022610701c580c0c04c0b881d1401c00704074581c5450086030028019210146c140500803401c09416805040402d480c1c402c1e2009807495080c054030b07a0400301c40c0c68103100d07000b4034840d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 349496681 1250 349495431 349495459
    0x4020921060912031b0c07180605040e030a02030901141908060405060a050306011a040b04090509061302010f140c0f1006060302030f040605060a080607050306100f0806060318030403050a02 83
    0x4800304c078018010407103142d0080c004c50600d02d040307900018080c80d06200b441c8000403501c1030340d42085104910000082042480c020803c0103846503070610742490342081207a02001500003040f5001e416080c20481005c90b000540d40e40b4a0041407500c2200ea0214040032040daa03005207807074403600080310200015180c080506c90042864040e0035010351011005110042070781d91309a83c405000604903281c035407100b10060741e17074205600c8500b52540f15000e00101020600c01c09a103c48103508400311140c80743c00007002d00b11008040000c1c00000048064208005d50460760040604d10132901ea4111201d0f98658902c4000c00c42600c1034500000405e4543c841d0003228050003840207181000c0d00d46485500c000d00015108907840f00c0080c100050200d030038000140308000755154a80c0300d01e400c5d0188401e4400300000d20b800c00103040b41c2c0c010607940164100c1d81018043c0ca45034cc0765619002c50030351070140324071185480d11003ca000020003800086080c1d40074030a640d207a01c00d41c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 349497931 1250 349496681 349496713
    0x5010f05090c090a0203060a03020d0c032907050f07020306090a0309090e1f0912030b01091202031905011808030414030c100902010c17090316060e040209210609 71
    0x22105080d6403028420b004112840e290703170061508410010030790680f582c0d49034001401d10f800d00c841103650079222401002800481b22000304407013000c01c0d950044420001006421038801401e100c00d006010410a59401c4c01c8001c0d130b8070003139015040b96080d0400b151001d540d940103080440024405080c04a40e100c0d4a01070100d0303418540009204414400842c42030131108800003c40e802d50b550744030004a08001a04c2d007054903142c8001812185083c0018078030340341c5800004406800040300b000584000429000c140254003550a4000080c07520a0151170103071110900c01400f24210760900001e14000c60250784501d2000c040700c200440c44a07103c0c0603583e15003100c0d40082420f041105c02c5030f04140600d0f8030502d0800046451540c0c2c580f0071035035000840c0249800400d0250090030208a050301c4041170ba4041c0d2081440c0810040101c0111141039014940225144503641c40c0c4400f15030a5a490307141c82d0326a41c0e042c42c900c0ea5201c42c2190004410700c2100c61b0144810340c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 349499181 1250 349497931 349497943
    0x30c0111090f01081e0103140705102717010b1804020901050d0314030114040f050f2811120f010e0703020a050912030a0e0402250201050c060405010f0509 68
    0x203000c2d000d481d00900110056032002401803065201003040c001480101002c00500c9018601c248500c030238840240d8181c91804007135400160040601030307443c000294101c8500175a800460301d00d03c1b9404110b08a1500f002c14540c0100001d89941703500000780380040d0002e0b0b14480c4290b031139800c40811a00038081c03490054030041d40207051040103000c0d600301100850070f07560003410311180d44c0d82e08142054590380268080d00066860810351a00c4d49404c0c040c0070350044040700240824200340c100c45d230381907001814a660007125200e114552a0111160311940340d44a0800c21900e2000c3c0e0342039103d548500301003003088800d580050348120804074080d058800903445008142d4801c02c00b41c000f07520129554052110600411440e2350b2544041e102e0010241c0145480e4152004040d00b00c00d9001c1c1018412801440742c00c80d00100200408241003510101c000403492500042e03d40780302d024ac403d01140210030410083c03010541051284200001042200e0303510f0341c140b80e403105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 349500431 1250 349499181 349499197
    0xa0e060301110f0a1b050319120c02100c020a0b010801060e16050901030f1b09170106060e0f0a1503090b0709030203031b1c0908060f060303041502120705030c0111 72
    0x4400c0c070606051070b224041481760b0010680c19801c011000b038544a00d075030020056150400403090248410130707800398580e14100804076060000152200000c0d4a0340300958a040307605564031a801b0507144204800682260090808004c65843d81c58a0307010345401c2c000d401d0021881e6010951015140003440341d445c10f159222402d0688000045000c1c02100c5144030585888079440b0683c222401f11000452040f510cd8007501840c14000c04040c00d07904a00c03190a906d0f0030000c002580e0070121003400c0b541d0803200104003078442000500c41c3c1d106500700c503034100f40104110161035015488101502e001c1e04d0699a1b81c0d4429108862541c0d170343c08020b4158100f40047c0000d80c0702101003698a090380c0342a10540b02c00781e0031400a120501f0209400103021b10420004043d080c0b01e020f40041c4014204c80241c034104c00420340d07a101d54070a41e04885548015841d069200f03101000c500b070403030040d59070740c0c00f240d041c07486c0c0d242c002d1924002194a0200c0c0d020f4800109000c903101a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 349501681 1250 349500431 349500457
    0x1b04050a030605062202120709140120060702071e0b0703110717160801050f040b0403020f1207060f050712020705010219030c110a0f1205090a0e06030111 68
    0x11600715625080544005029107410403411485c0c0d030180911103c034a1042c5890a00041c3c1b03456286401d109088800340554050110103001441010091503044450180a080154807050300107207040b28049103c8540381207009040a10502550102d0700d0310458490542c0f05c2003200d44041e40d0721458a0b68440c44500d40010404000081e00501c40c02c01800095020398000d240c0e01c06001d03548030000b10303140c03402d1b400c610b0510840403a80c6000001a00907240200008c2c40d0031a213845000c54058406002400c17401c0004007094404c000c1c401d01e560b5400705a425122500ba001c43c0e0a4003c008c0c1240c08a082c0800742ca802181d0344612481000c05640c0c0303040e00740e80710300150300a522003001074034695020000d00300200c020407c40200d008459900041d503401c0c6c01d400401c0e803c2c0e80c0340e1501241d005011843d011440c8009500c64283d0050a04102038100700800c0d1032502c5440c0c0c06039002600ca040006400349841010f51040700705800a001c004032030312046409206102040c044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 349502931 1250 349501681 349501699
    0x27140d080115031d01060b030a060e01050307060e1306080c041406030a02040b040f0501030f0203070803030c030f15030a0b040b0603071a03040203031303081c0908030411010e04060e1b0405 83
    0x405100c2d800606400b02d82c042003402d040e103a00501e17820744819401000400f03000100f40110a00c04e44a107500615a1028486255041100207038890304244100d0702005000f40d54801c50b07a58020900d054502010f60421040d692548450744540c0e028050900c1586440000004290f004024921403440100949050304e034660800000f030200c071103182d4029540300fa013000d0100051043c2c50180d03003d100112107008036071041502d40300303103604460410340061091100740181041502d40149400190003801c2da201c1e030f105507004103021a61a4144a003050a81c20f0005a800aca8000c0c0c0c010411640e0958642d000c1c1a501c2d0184d11880142c403400080840340e03034040002460b00305200400b070f645070a01c0d00c000c07110411502d8009480a090000e6911960b0015010301781d07192800f024240f100c80d001d46c41e9544d043c00010409022941103498039001070f8841c61110113404401030080041030b480c0c4403490402c8800701c40c2d014448080c0c006c01d200c0a07003c2421766044a60013003065507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 349504181 1250 349502931 349502969
    0x1d03120405120315220c080406150608010311031f090309210303020310091104060206150a050603091005070504060912020d080f0f0a170f060901060327140d0801 71
    0x65070100040e66a690317100c1c0d401402c504918203000e014911034650b516510907007440c1c140b08040711140c0300d08180c0042c1440c01042810340050405044a82241c4d80e980f440440102203030034110307440d040310744002e451800004e504d20180c3c014004903019079500443ca584070f10301c0c5142c440720460b81840c5240c1000c032050000b0b01c41e800440c0c0c000141030028125030350b688a01c2d01900d01441c56401c1c5100c0203c2d06101459040003030980c0b09a050441c1660303203048401240300141a401514019940000040d044d0742c800c02c00c61101c114983c0c010801454120402030058001e4020781d400180c643e0f4001400c1c15a1850035103000d50014290307165084160341d5000194070003018203440d06030510041e440005d002018009288030b540340d00101100f013080c2802c3c1000c00800c00302400c100c410900515460399090141982d007a800c0000350904540c00c0b0441c007001c0c2c030000c050080d0f21241030b0000c0042d03d520f0b2003c2003904100700c500c003241c8640180c13001d40c004d014885000c1c0300d508181c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 349505431 1250 349504181 349504189
    0x60409090b1b03011206021306050a080c0909071b021810060306140603060d05030c0109060506031f111204060903090b0307080f040822050901140607061d03120405120315 75
    0x1d805e9445200018581030810b107107204d42d0301e01940020081b450200d0201003498001002607800003040b45541d14144a100008944801c0508000c0400907001c10300e10061001c2075190020940081c0f5041c645499001d40811f455801c07508207048407141c020000b5014040e0045000b914032103500554500702110a00c0815000100100da200007880c0480011890500c0241603404255002240701e08081c10030301c3c00d459000d03020901990040f81c1c8802c4440c000846a9000365506201141c3c030410038030b4248160040e1480e40369088128801e2000f01f000031b40c40356104034032079181d0800c01c03561656071211500040301c2244c0801d4014000070885180030b651994841c1c071421895040c20845585a5400a41c0b06070742c41950b840701e4070a010310300e400102c281c011300b20111400c0c07804648001250b140e019403017000701003944440e00c0f0320401c22418000c154000500e0304486d100d0341ca024500603259000e441c02e40d000c3c0901c0c2541701607000c4800441e841121550b1000b0100c0c0c820300c0c140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 349506681 1250 349505431 349505459
    0x1a01021e03030c21130b01061706010f030b0a0b0c100203060915042901020c0f130f09060c120c031a0108070c210813051e03040302060409090b1b0301 66
    0x10400c0d02c0700ca035035403400d55203113038034600500d01c0c11a150b201c800140b5102e10b5080060700200c06108a01c400180360f9602d06001d41da00c081c00303280c401d02c0000340d8071040d400303400081a41d5074030a5007040d0101d003c02d032000c0540b0801d202001219800001455950304a20003954010382084000c030018000f141c0300e40c07641103602400b500000310b8801c440030308040c440c001c06420b00070040448280c0340c41e690420040d441c881040380c0c800601140d100018041d4004503140f5031070b150b20b80002d174640075001c2e400f6001154010f00207015180b101600248040502610a590702c0e1910085a208500c640304e8200726411164426041180a1005603440340b40140070000704a2800c43c1d080002c2c0c4940e4210703150746507c10f80c0041544a002c005407030030310014400404115450300b0b00d4003080d00010b400c00400c400c2040f1302d2031890428019400c6114039080a0f4000800190014617015254000a01d40e03000c2c41940c2284d0f12040e020380b5400109580c200c6403e90140018440d240300c1c0221 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 349507931 1250 349506681 349506697
    0x17030115140f03010905010503010b0111100c020f0d0c05060a02040302130207260a0306120b0109050405071211041811040513060609020405100f0801030b0c07061a01021e03030c 78
    0x102504208054100b01040d5100342c00502c0865140d4004022504090007106c1b00c000d02400d095204100584269a0300c0003840202001c0030344481d01551842d0080c000b14a10b001a01c00307641c04026609006000c9112500c0229554400c850001d04056494401d850a80358010852142d05070b000068001a403c100c00c15030f501c109960902084920031402200c00045280705151182d410704400f80890348613038014964005040e1714480001c00d100701c864151426010005000e0303e4509000d0301e0840a600845202c902e080505400d00180d40307174200d41031500f01c405000690408134a401e8030203001c4070081110481300d4064000c1e240640160358441501d41c12450545603680300d540c148c9405500400c0e0180d4002018001030522210042543d110b42c2407031503403512605030003040c4010511000d0070800050300810640c4040c4003c56100c190030400a0150400541a0f002c1c4030b8408040140580300303202082c0b00e01d81540052511382d1402c42c2c0598296922100c0000e810341c050b8079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 349509181 1250 349507931 349507967
    0xb2107020d0f0e030a0c09061a070212120a020a050c010c020d03031a060a120507140304080a120504110901051f0806060702060a0917030f04170c04061217030115 71
    0xc54190f50b500c0802800d00c0f41406002e4542c52503181602c000d045801507000b2800c000e000d640440903c00c084021100200c0d0f040d00d000c5c100314104107189080a104102a400e007540004000c06903950028461103101d00a40c2512080c180680041d40d002402500094000e0419820000828041d078450400307185484029040e61414100042050384100209804505641c64412038000113202d082d40c449102d0030071500e141d00080c0141003900000f0402407101c4000201400510f10800d01000e02c001041020300c91400d041c81e01004840851200c0760082e081c0c00300003c0c0038681601c442c02c030140035407201400040402411180c14000170320b03464001301d00300310f10001a21500c2c0104016200350303841c0c0600034100352100491610601d186e0300c0561090140d80180054142201e084440034807451000768060406541003265a2101b00d0b40280b400b000020109503208101c8865446501c10181c00d80c000102003e00c0d0200b0300900100d498a10365040f0f5050080c1d91004800c04880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 349510431 1250 349509181 349509197
    0x3151f0305070f180b0f100306050402280e0603150315090102030612120906070609020d08090f0405010e060d08040e07030f450803010b2107020d0f 65
    0x246969141c00b419600c03c03412910102c408205424120001d10f0082102c00418000310140000081203003400000320b910460004001002e00c6000727070300c58001030030040c205640310b00d0444d6080310200000620a400051003c5412000d82c1c030a80c0d03110000310008003031501750b8075119036145003403041400c250b0b0076100d200f550321202c5130318003102842412180d0002d83d5070b1400b0070a01c0411180d00d0411141da6028611600d410054070046d150451000d4030220744510311410040040c0c4802c14003c0d4100c1d14404000c07051008c030784010300c201c6505480380c00c0a115400180300407608244150480b40c0a40c40c08a0384c00d00c0c200d40d40040c914003849442c1d082c251202c0d50388885003002d0764248042992400ca10036856601e010300b00807043c007250f050420920204001c201212103074540700b03440815032030700d04403481020340c0032091940049040d47c41f5a11002c00070340c1c0360b009048428021184440c81c2104942c40c50580d40f03c3c00701075001c1d02ca0038403849001d94040420350110030500c2481 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 349511681 1250 349510431 349510433
    0x1030605060f1e0403260d1a0306060604030f0f141b0a050406030b06210d0509090a20070201020a020904081e030c070206090616030801030b010503151f03 68
    0x240050800900c0c50340586035200d6070702c1030fa240241c24052014141082c01e0108001080c3c500003604840001701d01e0030002041855400d00903486003908000100e4984200001d002c9114003041580b0072040c2c08448d2035440d03100402841d4001d40c40010811054000036100042c1030450006800d4031480f50000c0060703084250300e04219000950400f40c5e40d806203509564031700b60742c0a00040c02d06681c01c02c41d0b14110b494041c40c81c280240402e008500380301e940b02c1c400e005162113042c03803049482510110306111400401940c00807010602c42e0780010003280340340b1803038407401d0740c200d465804111600b010320303020701e043d03400c040400e0341076020b00400d006c0580c894040c0c492060b84039050305640c81d5195240805850118064050402414020061040d174801e0842d11425011906142c84d2074060b80061414400c2080d00129a031041141400309900800341605070385c030031103192010b42c0e01e500c2410b9440801900341c0d9410502100401d002c5047d10030700104e40c5040c00140c003041512 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 349512931 1250 349511681 349511689
    0xc0a0507050330070c021305040c030212030406030516080105130f15090f0c0f120f0f051e0906060f0d020907050c07050319080309030c0a0309030c090506010c1101030605 75
    0x90049440001c1c0b43d000381050f0068603810b6140d030000140c1003052400b012500410851007007a040304a101ea91100030905100781c0c003130100300943e401424070740d2441511022035141d401910890700842d0800d00440c2002c4020001140300d146940c2d540c4a01e41c0c40e0104000e044074003400a0280c0e159216000c1c0c070100f0980c00344031021200401d4030018a0b00d0224044221382d00500861911841c081001880b2503110b034245140350b8961404822030074000d100c8074010118031160040052501e40d01001c5084640c00891140e210040c018501018100f04050310510442da84d9282d5006080094030b18035181d8400120400064a8401d41d062154040382c1600d50644d2448e0110304080f900d900d0300b80301040121f025240a4024101c0d5101c1c01103e4411034030080f00080c652103003c1b00103025240c0400550704004002000c0301d40256041c107000c1c103030355118001039a076148007110209060446000c1c03a8090745040c0c0d12921000b0064079038100c01d41c940201c80b030406444240011741c81d95 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 349514181 1250 349512931 349512967
    0x2031b0f040e0106030e070e060301140103051e0a080f16060903020a15020702090c07110d0c0806072c03010b03121305010206130b1e25080c0a05070503 67
    0x110380512560300c82c00c000080c640c12805a00ca4410981022081120008045418811640e188910b00b10a480d00340009001d040f4400d541003400020400020903c9000291165002c0341040001c054106840d0802e484440c2064042d1210808108005da0112548020807845c4142d44811a000d401070b5508015291324801c158010782c440b0b1aa0301c00d00090307200c00300001c080c1910441ca000b80307075800b050502c20300400d403001c40d600c082081000d2018000d0080a0309400800f001c3e1484640c4c0392005c030b8160307507000726543c42c40303a000007807212805440652191004206054607030746603000d54450f4044003800c040d4055480d50000281034600304442083d01010b403000b01d44900e201203202010b164284d011504550118050003448801c94828601641c1c02288046030750343c2d500001d91072140c02d07011004a00f02c40340100810100303c0c00c28001040711805c2c00886607104640100d407842d805950f24840f181d41004000301890090005002040c030030401e590500200f6200c5d000030301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 349515431 1250 349514181 349514197
    0x203040b030916050118030803060402040305070b030a050a05060d020609040f050106030f0e060105010c03051b03040b0901020c0916200706031e1e05040f1209060216120602031b 78
    0xa4040c0e1400843d41c000c036200600038020a00e0450b081c01d10074410741c04503400c1c61002404200300040469040c0c1c9032030301100c02840d0071208890f922a0751703255082c1c8a610881c0d807102098135000119140b890903014a502404006041140da09140d40801c80160b1040c880071364403c0d034070810000e0880c01801014000c3c1071548001070790800d81e081c0d100a507001500030070b15507003004006020396078001c400c601301603401d407920700e8480c17101608142d40802c1a000700905032002040025070540c4a40c0240307541c400070380c2612840d00d038140900217000020348201e426240b003010011101d6200b440c1080f03490102ea80310044c800f040340b0b41130f810031005400c15400a600c0b030a808001080c4000310510180d40a1010002100200340c03522500d801001c0e540b0200f80c4450103c0d062020440c0c03079031640340d0000244481c001485e44040d1081c0e41131300c550005400343c01e01d80d40c4d22820a500c5030003160310700142100c6000403582c4040080d030006051707481e800940c4550a101e5641500540007003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 349516681 1250 349515431 349515433
    0x501080105010825060804033014060d020402090303160c0608161b0201030e060a24030b18070b030a0504110405090d0c050c1203040f05040b100e010203040b0309 71
    0x10b941840a52070501258002408100202040e13040c001500d56003060304450132407904400684070307441c04a40341d292000f0309040e994191809070780482d880150341c00c021448039008101c50420200d2032001080116003459000600001210240c14540c00818100704020140c910b8501c8200d0321208400c0c8420003580e029041c49410301500343c20141594100c0301c1004601c0814001c0780008205910700d169031520000c003203010004590090708031000030600401a0350781031804000c07036001005030101002e0b10300e400f0481c00d48182e64222104054980080c065012907444250b5031002ea01070643c079184901c104030000403008001d03000b45004915031140801c550805042100d030b4151441c2e13003580f20398948018081240ea00007109000480c042c2014400200315003407890414100c001c0c159000300c0da141000c694180c0c0400100155030540d031000c0640d40c0c0b5882400115158600102d4010705003200d40e081580c003032007900660100510443c6d251a403148811811500265429030b40c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 349517931 1250 349516681 349516691
    0xc09071e1205091c140d0f1a06090d061e11180906010c030309030311030106020309041107030509130912050903151b0901020c0312090306100b250605010801 69
    0x4610120b0140c15000041c400040802c400c90fa06504200382d008404201400001c0310125021152503050741c2d6110700c50007080080085190491000d0001100d0b684042106048101440c0c50035000f42c5101c010054030010441f0707459640d0500504d06ca0500040201400143d8041c3d08541c1c01141c00010075a21850b840f8404440380d03151000b10400305610408201d401c0218071b9038050440e92540e50180340208400d50642026401446d009100014200d4004004031701a0b800000034851075a040d5010031006c100c003859404580540b01d0300a001030002c0280050b00d14004105038000c410101c03000907440001d540706a208030f0f00d505000c3c0428400718185100f89014000d5540750419007070325144918000d00001e034040a084407400d12010b000c6a003400d00c0e4401c000225114402600b2190000354a421150b01604113000c0a4441e120301000110341c94040340501d8100c3c0d28a001d031a0500286800c800701d038941c104cc80001942001c180c2d2130104006001d500d0080c40c0b08800001c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 349519181 1250 349517931 349517957
    0x3060a090c180e16052110180b16110c090a0903020f0d031d1c050d11030f0109050610020d0f0e0409060c020f0307020127080a0b06030705010903050c09071e 69
    0x21849240008403414580204841c9240305000ca8910b00c001f00c1c001000481e070302c1c1405c840b4480404142d014000c40c5075101000008100500905558411600c603010780c014102e0881703036101c40010350950406169004510310b0300040d080b8406a80c4a0b0042c0d8407070300f2458810502e071903515134042001a4481040040400b07442c0100310221602c0700281480044003204410480300251602c41004000118070454001551140c0f14100e054200b481c0d030703800c1840c1d10411003042030046040444c50240454a1403a010030031000216040d000703010070390301000b0f054035040d440003590b00522a100030840c0c0103a840744120700b0110311515000501c00030281c0020714041980b0b4a00d18207620401402c00580e03001940c000700e8441b0300c411000380000d070011441e2807000c0c41c0c1c008080c40c425030441d0010007016201681c4180ca050301118107140d81c3d82d004445a104c6444042c140d81c1062041940a04010024130b03230004450408804183c25010040c4034485210400400618446a030b00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 349520431 1250 349519181 349519189
    0xd0503160503040f11040608030403050606181006030c03110403120f0e150702120f0706261f050310020403030206060a080c0d050f060f010503060a090c180e1605 71
    0x903540c809185011411840e09545204000b200c41c2c01c050f0601c40c1140f403000c03070f41d42e4640028015000e00c0c02030300e8546680e440d115076a5401581c10b1441000b2480b600601541d0105002d88190400c54030b07851801e1a1060070380c01170413002c44a900300b58139203085c2d9041c840345000901c000c520850501e2000340300020003c02000080d58400c0030420440c841c418182e4911648511503094419034550b5081c00b48006140d410589444a0481c0180a2050400140400c01e081114401d4840c4603c042900c81c5014510311145a840d01c08407040d004991000c41203a10488000b00010b13040352165120700000e49001c0103100042c1026400007014010141c1c1849402e03000842511074840c40d609028115444200030345445010b6041001e80303009000b03040180003212a801c00c01e940b52030800300d81c0602c1e001424060603029101d1000402d812034503610415484039080007a80e0010350a12644044091849030904080d6031a25024100c13140148074400444020551a01c1c6252500041c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 349521681 1250 349520431 349520461
    0x20118081c11040b0c0f060426040315051302120615010504050a090e070e0a060311010e100806060705070b03061f020303040b0703061502060108011b0c0b180d0503 72
    0x5020a50300b01524820302814140641e010383e801d6803c2da684500d65599030b14078100100302c50b44c000b80f09240500061044004200300b00428080d40180d1faa909888100303c184030710b120040c00c000e14100c14903101003403a402036400480040c02ea050048a91700065400660340e002c950880d08008213103d18000c606484d0421a03c0038241a410301c1d2030440020401181d0784508101c1648903003a4442d1024140100300148c02400e0340120b071400d20014502c020410b40c041150071035125180c0b210598041d5940183c82071004018003019620b0701422100100060320041d08441c5c18000e20000500130f2118030b001c0c00c4203101c10b58491400200300030f10403503100f141c03c1010014082d035042c550350100803260b22a8000d82c080c01c2c0c03900d40c00c41c11002417641e5070100d003410207640c02c190802a0b000c41d14a04a074501c00c000d2080101c507804000030141d00c1d020800100f21050980d000080414000719440002c0c5a80400742c8007070200c14508203a03420080300d001840c00030401c44034006020b0340c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 349522931 1250 349521681 349521727
    0x6190801092c0f06090a0501150506030a09020301020c0d030905060c03070c03081504240f0f0e220b100605070b0703052a0d0501120201170702011808 66
    0x6100b201c1c0e080401000c035441c000054000e0608640402c0e40403a0204040a5002e0940701140d5141c945200010748a13400f1840840d420f50900c9401d00c0c012140091740c0c01600d000514461554655018140c0189000b0508a0705950240540101d00000340300f10400d001c910384011400c02c0b02460034a040140092080088030f4080c4148008150712140040b0700340c2e032604100c042600c1c0c5c2c418070446e080010000c50341c000d00704600d00080102004000020308c2094560840e144e407641e00c2041f42138054000c0d40c0d4401010181002107501d200c03041a04410b03401c40305500540c000755800b40516506005403041c40b00e01d428090445012030040002b03009603d040341c1000780c0c8c0d565240390440d01070840310403d6160703c0407e40030003003501c0300d05011036590340030321422030030740c0308148140c120300041740f5468903000000805206580402039585d90583d92804000282c1c0e007103050381e4601400d0002199664504030300b0b40c08132a1403207000da5020705812034681a00b0100d01e040b191040030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 349524181 1250 349522931 349522949
    0xe250503150c070b1b030a09030215040201140a120f0c110102030603330907060e0a05060706180602040b1213050c0f0301091a010f0602031207030b0a030206190801 72
    0xc0001960b080e8095980182d400103e01045480f0105404c20780307810214601c00400001080c408107405503840000030601c66000c2d92074034506c1001000d14000c0448029011840700d0040201064004004188031025824109958100240390380c04445003008640309003581c6007019410582c00c55000105500c44500944c9180b90050200380c98000c002d40101c810009030001286861a02080c406141c2d04031152660614004485550b11502e80c80f440c0041104500c0b20304440c14143c02550035220040e020a00e0044141d595400801e90201c003102040518094030300042c4650008000510100c1541e58841403c0c0618443c0c0600290005100c100440410000204045004610081d04550300c4040341a00404640075081c040b0006042904000014541080a0000d603058820510302e04a200c3c1d00c4120603640c0b0f104261100003081d292000180403e44030350016092004003401c103018065030b03580451455000080340714234500030000407614091f404114207005003810f603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 349525431 1250 349524181 349524223
    0xd060e01060918020d020a0801030309051c0b0702190309030203010b01080402031915140f07020f1209060f0d02030411030105010b070308101a030a0501060807050d0e250503 76
    0x6071002c1c09203480c0d80702d1141180443c400c0d01c4801d000343c1d810381c0e462003030042003550b03a030442440080044c03000340001c402242c90340b20003180c0b90804c491076880340c42e8034181c4820194041d841c0e0800c481802060300046201d0184941c1c64001085005102c19100b516001d400c3c0b41584101802d494510f800603040021b184104405a607000644100310014402c00020300e0117a81880c004902950780c46103056070400f00a80c0031600d11004840c424400750003411a161142041261103080c140b4422604c0d620000c0e000c1e0750804202d000f00700b0004004c100c0751815415102c1c0c4c604540020f021009050b902000300000d00100e0850000c4140c0201c000300720035810204520b0460041c1c8401404201e0100c0c00075181001500c0c40c0c4000d8400101d0074102c0426010320981c4551088451411503810300f000040d40900940c00c00d40510303210b4991034200590041c00100814500c0c00000780d40c890304003a18900c604000e45001d45084103e8000b100754102020f2620f455034003030301307003412015013 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 349526681 1250 349525431 349525439
    0x301020a0903030e0a09021303030e040212010510230408010c0e09070c1106040e01030221060112030203130e09011104050f010302210a090b090c010e060c120403080d060e01 76
    0x19403a0150307945800c00088184002e00411021741080d040a501c0d00e00c0082c0d610b4051212500d9102240d00c03d560300921a140d0394280010b900540340d032082c0107054200140660b140010b10042007011920303101c407501c603035030310440b40003420300f1034800e00e1030b10018040c0300a007001c0c00740000c1054141070002c44010319401081248500901100401c10010549820010b41030345202c10210010155a191620380300c0801030300c10280300803807040c2c61001d81c00a0b6803444000650f91550501c02400040c1c0c0381111540e2580700c130b82800c8046000c100181592507101100c5440500480fa01f0300c001c0c3d1030407520b41350843e0070030802802850001e01c8100001c0d0b8914041141c4494203180250b1180380e204d06a031080c0703d141103501d014106541c104004000d859010841143c052001d803100341c5c4540c890161a1400101c00c2400201109010714050500c0d40060500d1b00b11141104c0040c24800701c0d1a515030002c0d0411503281000050a074204411030150700d0107841d00c1b1003c95002e500d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 349527931 1250 349526681 349526687
    0x51002030411240a1413052d010c061103070806010f050c10020a03020c030c030702040f0509100e0322090f05270703020901090b190602190c030203071707050301020a 73
    0x168142c07020f440f520010310110110710030a40d50b1070444164070711a171a040c81e2600040d40018901965001e070b001d140030b0445802c07000c0906a41c030b400caa949150100407410044640401c10f00c010340f0b03003035203030200882603078182002144618541d680358a20790402400042c0701030140c03c104402c0160600501d1741c400c8010480070744040c0302180050740c404420308242c020b4054500d480140c0d001c0480c0c8030190030004801011581e108540c1000103003034103a07210045420645245180750300140c0d01811b0542c00d0390080081c220501c0460381800c503a50466600400140100d1420809410003000456998000d0000c0001d003d1024411072611008201a00e00301948140003c441051009401b030400d01002000d1500942454142d43c2c46201d18409042c0b6071040310f00820785880c070300300da043e407050001040e0ae04c0c2ea4080c0c03900d001384251105c42d454040308103403906144410700200590b4200b022400421542d0040d5040c0c0038120215410a0a10361002d80a03900410000c058558 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 349529181 1250 349527931 349527979
    0x801050f030705120c0d1212060311040f0906060906061e0c03080c0403060606080403120504120c05030f0a030b100201090201020304030212011407031e14010302040b0607051002030411 81
    0x5580d000941c9111304030583c500075046084030380040c8400708280c00d002c01c000e008101d00c103c23500c07481d2811a11442034000c80c0c50794400074103031110f4207500e000146840c1e00114105802c804000c50802e000e51260000c40303001d130348000b10803645e88a04111260b000710a91200c408501030042c1c25407003d0354007800401c00c60f0002010495010001040d0034051000c0c3d501650b04881c0402c000e0341c0318000900f9a042c2683d040d4082000f591402809032541d018941c031655015108283c020306d6021705490611071103030225424002401a848e42d08010030141400e0441c82c1e901185113004038051007400103000480c4401c590500f181800503076000412102180c0d0f068803040302000c0c00c030200a00620000000542c81080c210a10401070380c5608005503000030400f1090230001d0700180e110440b108a209180702c4030141c0010800743c6040d80c4501c50f1030070082c1c00315240c000c440d6034850810842d800c031640001da020003808240101d08114420884043d50058401521116014131050f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 349530431 1250 349529181 349529189
    0x30a030c030c140601180504150c020f0a0f030e0316060806010c020d051e0c0a03060e1c1d040e0a020f04061203030e0d020a080415050f0c030a0801050f0307 69
    0x50848410540b24640011419410007006804101c40c03111864440c0d50070703c940c546e0036141d220720343c442250344d00c01d40303010710780c04100d004401510107400c1c4003070014900100158020617611030328220040c08480061803003140300b00a1b02d11640380160180ca10b04d040240240d10003d80045803004c14031005043d00d41c3c50800036203641e5284012076a00840d40f40013900440409144010444000b82e000c00505541c801001100d007072401a690b64405017024551103d0881000c0010509552040d410210007109075481c000326074118404010348411503000040c084941d50016050710461103007030300c04c12201400f01c00c4d5241e00d11039895240701c0700a4803030f150a103100c00082ea116480301e4010940b002d0b24070060812801c0103001020000e01e458118029040d205540d5031011602021455210b04a20f017482d04049002401c072040e03022038018030004000403110096440701074040703051080000d682e500003d01c8010091481070740414000e140020800300d00b503401298001c165 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 349531681 1250 349530431 349530437
    0x1f050a03080304112101050601052704020d0501080601080f0c0a0302120115090c09050405060d150609110406020d080601140f0d0216020118060f03020c100e0106091406030a03 77
    0xb0340c403982455450500f154a82c50341c80f10442554184800c20b0502608820321001c0080245a6988006607510701c2420344101000340520542900d1010603c0b14140c0842d0240c001804c1c0002064280102c4100380c000b141d0795481305004100c20707803003044082d030001d4049001d4032158901c0000701d035402c280784c003000b4418a12142d1460040809500a040b00d6103c000d08800041e40d80d114000146818a1a10005501e040002c291424603000d824051b01c0d02509040301ca260540300d108150050300d2946507040c1e00c40b8000244988140111203401400c1d4890070303030300c524007403000c0d1401d4036900348002480503503020801e150f0b0308400c403002700e00304c0c0c1c2c000203a69100c098008041e0748990031000b41514404644000c404c0c4c151520310110070f1003030b03c80310080540d08155120087c1d0a1280400040440c10b03000300852094010b41500034490301140c0340c0222002000c000d07166640c0003030041d60740d900010802415180503841501142c4201407006050400109490700840c5e4005028 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 349532931 1250 349531681 349531687
    0xb0f0a030b0a0e0105120601030203060f1f0f0f0918030f0905130501090e0a050a20030a0609110406080c1912050304090b100e0f0111070e1f050a0308 66
    0x8180207410148034190001e1201406946480710312031400700030b0050034000c400e0305980c1642d03403d0014006050700d800500408050783c80c0f450001154100030303c460b100340c0d003148031100c02011182c220760191804080d1484102d05118052002c884a5400480314505094005c400c3c0400b00d01c840701910307054a440030500c80c092a0a41c0c042d0065030116421410350100001e011a0580c0624107031040ca2005008020354071213107584d10720060310003400e0354110748100c1f4002008807415404c501056160b4140c20a07084000a04242230341a0948041d80c40f11618400c1007010346522420190442d420410103007040c0007295200407850105000d0300108202c030038043c0090300c0f00401003125190b007028034500f40c50030076100c0d0410b100d54110107041c8180e0315003034a8501d008600c0052143d40d06681c001d61030041281e844c0190105906005c2c1d0003140100401c803c1c81660041c2c4100301c042c50840c10110425110b01d0200040d0525071034000c2d2086c805540d070540b100c1d040326000484961 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 349534181 1250 349532931 349532947
    0x30402090a05060f09060604180219020705010f05070f140610090c0903060e010f110a1d0d06020d060b0c0a02180603030a0f0201110430021003020a020c0a2d0b0f 71
    0x1500c180c0c0c010704280d001c184400070b01c2701b01907002400c4541603600360044034140c000c4d0aaa0765001405102e0100f45c507041c1c101c80080c03003a8040c000b02400381000303c1d4810003d40b200303054a0059200c0e50303c42d03042941000708042ca1600303403600400c81e0700070802c080e0103c15001801d1400a01006107520b440d001000b010540c00d4018040d4100000c078100701c01d0501d18240c0703a41c0e503c40a0254082040c0035440a28102ca6544001d0342c0c0e07d01070070300e24880201e599018000d5209000c081e451540d03500d0301041244202c00078100401408005044031851801002103000c0d000a581c03594499201c10060280c81c0842616034a605904081490b0008a9416809080b05240e8041e80c0c4c4d401050000e2103003075004080d01e64180d44000d4486210031090020002c48010001a40140d01c8240c0420114841d03801070071361224038415101400c0f0b42000041c100100d80e480000e481e24040e4400070400540409188015503444000c003804c5d1404440c0e0001d0701820700b0f0000c05c6800860309817 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 349535431 1250 349534181 349534189
    0xa1b05060105040f1506020d170105011e021f020c010b0603040510090c0e04060204060906030203060d0323030a0b0f030303041e15020307030e1902062a03070305030402090a05060f0906 81
    0xc150780c1034917440156203588500000f965000c4000910700000ca1a1240d00042c0886520850507100c060303440c01c01c18400030712504055980014111304510034950341000c00d8001c0c1e0b004541248c0c406a0141c0d80c0c3c401140c0007425540d1007180a84036a40800c203101c0018400184118170001512002c241505e050410303e0500c0b1080d40039004400440b030400c0108000f031fa0091081d68100d0302c40199041d1103030740072000c80c0411603105412404c42013601c80803a018403001d820181b0b03900d4280b1003032a03101420140980058400d1450292250035801691404083d1210002c8094000f5819854581c48071011403280e90302c280c7c41007140060391400c2c0100d40b032091001c50b220110555880c1403855004001b403011110a940d0b90160848844c0600d400b00c0d099041683c00401d980d0078441010113000030b190340309070b0134808075400381123004c0c0c03026041c4042c110150081d16815200d10300360050200801004086031860b07468401007011070b40e02e40800904134041996000348603a030b0350001c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 349536681 1250 349535431 349535441
    0x603201815100e04060e0106050702130b030d090503070b090112110d0227150a050306030c04090c06020114011503020a0e210c1f18050907050a1b05060105040f 70
    0x554010015082c00c92049800c404082020340381610108042d980e01c2c07101009503c0c00707000b09800038100b00010405490114400c038800d040c2030380006503116055000a01c0c040e040100c1002042c100308003000246814429038000b0107603041d5071407405c0801d030002485044408500388600e59a80d0700720440c06c2000c0e05917070f1030f034013600c20840d96240000d0015405504610000c403528150b9142d1056a04003950403c0c201e0100440c820b0a00698982c10381d1660030003800300350148030360034032005107507218003032440c13958020a1094002c904100d07009081d2032181c281c544400e62007134010000c1108940e0403456150240c0340058403101414000c9a10013800b80d072a41c5d1042080750041001903002c14043c50368030b101000c991400000000748503035031617080c0a10944020181c0c0c9049100c1c0125000000c0c03088944007c0340081d21400080ca0104080c0c4141c0c0c00560003148210140d90001d81d80c048030003250403055016401603507403d5035000c05004040c02940c513407082c00d41010b016040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 349537931 1250 349536681 349536721
    0x912030e0301110318150c0705122d18060d0f050c0a020106060c020a0e130501050403050901080109021306180302030618010b091605130e090106032018 67
    0xd1045060800c3e41582540003580c4a072104401c0100f00a104000004e9000c05496000c41c0034031991344861080304d1310b400488080d41d180c0221902d002080344000e00420504940480c03500e4180780d14004105500c40c3c3e0041d42d14004000c129401c049a9031030031190f03403484115402c1d503030741200081400181c41002492440070b0700f807405002c80c28006102901d0703c00150350080000e0340e91031004998140c09004041e4124251030001c0c005c007000b0b600d45aa100740c4480b80100000100e580329400c54000301d40075000510b0116114506680c0a40c585005120030301c425810f020130083ca2210182ca03510800d000c0c4101c00d1070800c8031071690b002141c01150018141d84a07490040403a041086640c038405000d5442c080c0092158688124280c0c001c00304404800300c0c516140100f0b41c3c403035021015440303c04840c28800612030104250741403044c00480004130388213143d8602110310035040828110740d8024510080300540311102d40f007000c5592441140490340300c1070f24081001c103840130 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 349539181 1250 349537931 349537933
    0x51c020d02060c181f08060102010216170c060f010f170607030c0e030d180f0e0109020f090a0314150c0922020a0206040b010e011d06040e01180302010e030a0912030e03 74
    0x4145e900707481d4285092242e00700ca0b489444213680d4002c0124201d1151071081881d00114041c003a002c030b21001e4042a1009260160a10b046502e0102501c0c4c00c0080f6070711003002d50000d0041c4807543c0240910f000418000c09d5100f11003d9000502740c03104002002c020400d5600c401301c0704094400c02c0d07000c080c0c08016091701c0003404e0848004020810304d158104410400f101c000688403404412007003221190441441d00e0f9082501000180d40942c400e101c181c50300b0b00c4492903540d00c040c285002035100d0080400d203005030b440c905061140092015807404600b908111518540c90212044840101d4102e10391640741c25001c020320080400c0314104500c00300f000800c1c150001001d80c02240951051407140c0c1e0f0f2440100c1d10320209008014400080409132244054110b031055003180e8000c10224203040b00a0880f0f003182e201c162513074419050b101c401828590280706030004078004802031131400310f5820015001d045944900119010540e0042c018144100440c2d0007102000b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 349540431 1250 349539181 349539199
    0x12061906020a0c362301150216171c051201140a0506180d050c01030b061206210d0207090f050714090616051c020d02060c18 55
    0x408000c0d41c80e04014011200900d854a000c204040407090112120210000212000c42c2c401d9034a0113007200c4e6894070141e60f8403203088108601c01c0740030100d41c400c2034070401030280d0314005505601c00601d41250065400c403a0281515000031071204007641d2903010692203861000070124a8040c00c851181c500403108406010380681c0030009064650301c407044411582d807070b825030300c40002e03406200a5010741036040030003990902201603c4400503500381c5086038420540800c07040094140c08031550780100703852114642e00b41c416286004820f0b5080c90070003010000300c502840b40603260034450040b95a21041050155030610101c02840c4142c0c1c00b540b01c5d80c40084e5559002e8021070543d54104440e4400305029489400d12030040c036541c0d54685010b010300d030300240e1b10950880750000c40401c00b259104600c1c5400c00d040e0b500c20802401a0000f0168602000b0400341100f004c540103580080380480d030016015400c0981d0380b40c12a940c0302100c400711400b2200115294002c4441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 349541681 1250 349540431 349540439
    0x60906041701020c070503070608071b1407180e10091b030b0412080903031609080f0304031403090310050601050904050705030a05090c21010207020402070f12020d05120619 76
    0x40d006083c44c12043c43c100c44507170303407030310100740c1c4800881c01150005180c600010f07100b0343c8100e4042c021860004401001c0d1005a11104d6400042c10315401e07280e40b120b40e0420500380f000c240c400310001742c00c2c1c040000c0030b00481c0050300e40d1520b2014060842e02d40c2000414070241d420200618054a0803104d109541ca10380440d0112044405a4003400d0003011300f02c2060003041521320491030040510720f5550741e801902520b95070b050100c07082010a0401240f062010004100c03015001d0006580b25451403a01d0712441e041c2c840741c5005600140001e6003252000140044413000300c01c404541641c4540040305e26016240b2203552103030510050004560b003004c0254044c12003500f080c40740d5070350030407601c1d03841d0301100c030241e04900d2811400307812455802c4101c0a101d00034001510b0041c4540028041e03800051082d00c856107090241d5003048101426071681c81d500d0700240c13440014103440540710303008100c9000900d00030b2200050103541c0b0481c80d0b42403500301c00c131600f2240b038031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 349542931 1250 349541681 349541683
    0xf05061c140114040b0907032d0b030f0304050a261504030f030506031b0d060c210501030c0b0903011d010b0109080a0506060105220306020d0b0f010801050609060417 73
    0x1081c40744141038548849503d42c2410306010f00382401c00c01800c51056911200c504400525903802c2c042c466143c020450324400b01c01c841d0b45804150400c00c0401d00340302c8101051308120025804004550041001300540e4a42400c40001c90310040100e044041d02c14540d640c103000d00a164402902550823030384001210088031b00d0259020f560303131114a002803101a070444205992140d4560f021000440f9040401009100d00700000303000811961200c0ea610300070364159240d04000315066a403082201030b0002c00c0041d9218010000b070005500d1a00d0301801d070200f9005140344114001064192501c09420020002401201d184c6910400c3c08049000701001205903000550400b000214080e000030014025600980070300082e03266a401565554032001c5e0f504038501c2c4100003a244103120f42040802580211405070355030303401c94010301c201c4409640f864070400d6840310400059a00c2300e105419104143c92035030781c4400081c0061040d010725804111180d20040e400781780c90b28 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 349544181 1250 349542931 349542971
    0x10e0c0d0c03120c140a03080c030f01031202011e0507080714040902070f2a0812091207050916020105100e0402040e16060903060605030304180b010e130c0e0301060f05061c 76
    0x20007030b681c411141c0c480c09d403088100c0c8001e48001e403031000c8100051003c0744042480e4a5002c0c001d000020700700c0040010301007a10004071440ca0501e941c0c10801404a80194629074400f00360303d4401310000c5500c1c039072452030003240208406240e0204003002000001c903846864a904404003441340350024400050900059402020040307840c04001546600007440320105012004280d040948a0003400242c40309003030106031034442c1e20400285a1940b081e418050915180c41c1805181e03c003901a0035910090900c0b80304418011040011400c110140c42e00a0342c12a07000c100031143e0705090f45401c00140410400780c812407000114540c0103408401140c0c400c900a01c21103684808154507401a0f2244100c26154000c02d95200780e40e507441755582010504240403400542c0c0c0100c0c50800701052800c1080e960f62031551140b030b8101258030b140c2d0b00e08a0080c000c1500341044211414903c8c49040d0241e84041404041c0885017000001580c060b808200700004c00202007100002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 349545431 1250 349544181 349544183
    0x180f08010c03060602030c07050f13020f0301090c0f0f050c010914030d0b0909030a12020c19110405041101120f020f30061003020d0c02010e0c0d0c03120c140a 70
    0x303843e200b400900381c3d0010040e90800e603880c0016029081c40c041c1030003100c5502d9903143ea48406040340d42189025a17201504081e10f4007a0602e441c1e6040c10150003c446840341c20009120100f030042490a61102c6214041c0c406890901d4a481c9104c00f000c0c09402022002000b842e40c501c17508841400c0080a00300c4006a0700e000e2089a08020500c00c1580e000d4421b95100d40003004212661401880ca0081c2e00240000c010f00c4c1100d004495814186880d840344514040603484c0030a0049a903c001901e000494040005090075501d0f03400100d21001604d041c030409408000301030b101c550007101d840d6100c031001c2d0b41d6110540e40000b06035000c090104c04007a1000020200207400e00a800300b441a04044510b4075250003080180007448070740d2000425800300501031a00e4664007400444140ba50004502030b00d440d940f15081401e05400d86000d889030817010800300300603d41a40803603810440000b4086c1701c1041c202d0b44881c144101a001094a450900640b2000603007101c0807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 349546681 1250 349545431 349545437
    0x90e030d0e0609070f0b04120c0f0303020a020f041a090c0405040603150e03040b0306040f0e1005060324060f01021e060f0a020a0e1005041e080d0804050d180f08010c 73
    0x150303c40740490700604060003450681d01c0c1c02d00050180d0705000548e403400a004000700c00b02155529444448a42e15800840040e048080602c2c11800c2c104e500b0b140b0540300300c5061055244200d00c0d443d21100000419100d00c00c1000440c0c82103501a086074058a00a08140141a01c9041900c015406000001401842c05052130110b00002c01554143d030000c03030009245481d10000c02c000780552080501841d5640c006407074180e0b01c100300940031b1482d4514041101e03d001020035060000350303030300c01d480d0031022004240003502d0118200d1307001d803003141c15103403803904400100d01c1d08072101500000c03041c000c280b80f88043d9000030f81503c0b80340034400010803981c0b41444003060b402007034102c0c0049a00090180303080c1c40e110b0006d40c082d00317040c0343c118100f0755144500010f80300b140b4103c81c44a6011030042c05112420300103800c03d007000e0b00b80707110346052507618103a84004112000c400c002903603080f441c0c80070bc9115040028221507012541068030b03186001d00a0140380411008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 349547931 1250 349546681 349546693
    0x50613080d020c090f0c0f190306050102070f0303050c1e161202301608010e010903090e070306081b01030b01080105210f12121f090e030d0e0609 64
    0x100c0e100140c00f4000036805844260310341c82e1000c0101365141e0180401000d036000303211280b03d48031554040c0134140c080041c0d00d4043c9030100c9000d4211840b98014a0440d00511030a102c2d8404602100c8200c9615160241da506800c50300281405031000300e4080199038203107109007410000414064001600002c05001030783d4a00c080ca0748080204c00a4010348500110401c0c50b0041c8841603070428441d0b503132050704400100ca00c0c1880c2d81581018928a89000140711138142442551001c0c221b150007084a4926900c002d07141c40d10900c40c0900d00c8c083c560001e865117110f40c0109004221403002c4803284a400306848003540b800850b07550000380344c00e2191200b0341c803c200003070490b100544a03058039005408040c00071002c002ea20700807071203800810401c2000c204440c1480c0c0308041c10941d00c40500415001242502801610041d000700c940035040000900481c000c450f041c039000601d43ca0561261400c60040d0020784034030302d00d0102d40b042e0311100419200e108407040d200f901d80c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 349549181 1250 349547931 349547953
    0x40602040e0f090d08070c020307031209080303090604061d030a08011401080720010612050703030e01050705030a0e0a0504020d06052407120216150f03020c19030905061308 76
    0x42503900f152411610360020121040042c081c03400507422001e40e2502d0a801c0541c4d80105e40703080c442e607100b00c0e49135080300c08408031141c0c4908c0c070788040c1c12046e020b10f242d07050000105a903030790081c0014161b01c0e912040704c110085050700d401017102c00300c030680e070720756218100184c14a0700c02d11540c0c64410940701455030f60b40c0b0400d00c0504c500d0054841c8050f01080000342e008950944174200e026640c1c402020510448102410405074407a00013862464103500c4e000301140c90580307016040c01014410100051004002c2d01da02e01c80d90301e84500760804000000c0e030200043c3e0311580c0c00a2000403580c0042e412508914151401a20800c02441010100d14140000c8d10380d81050741d20103012034000a29190700c45050902644122049000c00040582940007650301003840840a1001e001d9244d800c4650355031160854101141810800514203403a101000c984008028a5044030002c050041041c5000340c0320150202c2d03283d0501f01800024007040e800b0700b41c8640300305a48a5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 349550431 1250 349549181 349549201
    0x1107090c0207050f01080403080a02090a0b09040c090b07120e0a031101231b0109020909060405071a0f090112020d23090c0d0503090d0309051c0819020114040602040e 73
    0x4180507046c0c0d5100c001d80c0c2c0d00c0e00c08841401000c0d15518000da02080b4011495491b0309038900a0180b4142d00d80c0d8035148442000122020034240f0720903c0f003580d80c204080b85040056654080c1c0101c10140c40c01c020502c12143c00d100e000c1c11950101c02d03110f0100c2805045440d40c55038801c03e0300c41101d10341100d190850041d00746030507907421031010000b0b204441c41c80c07114050010a0000049030308020360340050000802160501540d5202c001000180f150412000b8020314141030420040c5180b2442d9512070710a401241194100c0018000c030640d1080f46801c0c0c4140303c07004d045441306269005a000381a8034002c0300108030302e541c1c60041d0030580100d007a018034586c000031302040b910103090000700040030307200761841e00040c0249070303003034881042c40c802c0f481c826540d01c03103a10305100401c04e42001020500401c041c0d000411000101c8140c2102c496203403038400b001c00e2260015080740035001e000d05013002890031200b400204400d0b50007900955802001a0b410741d61074217095 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 349551681 1250 349550431 349550449
    0x60516060c090305100b0907030b0a0306051e010611030a080702190c090c05161716110108010e0601080103020f0303041d010e130f030e010504080303040506062704080a1107090c020705 81
    0x11540400110f01203202540230b03900c50000ad040c0508540e03d078907680c0d10b4020860b042202c260440703203104035240c10b43c1c49002105a002d0700150805407c460340110f00036540340116840780c0c050000000c08900d41500810403e010301101c00b064014200751840c00f02041440e601c2900c24807802e201d01e40038106c1c081d1082e01c4000051071007504c00c102007038442000003108000c05101a010400003514884500e0040780750280c000c80c145d80c0400340407000104041c1741640405501c0341510305200f4140c1c0d010840904498044440c4e4400512000c002400c62080c0e07841950000d451036040040c000540c0040780c100c5680341c0d4510729030380e9840780140ca648030480d00105220b01a07002d41001a0007441c0c8105030b00b04c18985107042c90f48031030500d441c40e030094506a5080e8490010048a40351038110066210342c1c2040c8188a0f1100100030b10410101a00080c082034010400d00c6a151040304000b0a01810b282140e482c41c0d55042c900c0c008007020b140a40040c060104041050704008800d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 349552931 1250 349551681 349551701
    0x1f05220b0411091509120d02190f0b0604110c100b090c030c030c0d020c0105060f151b030d090b040b0603010504030e1e060c16051207060516060c09030510 68
    0x810314040003c0108404070200000e1010105000e200101164650200c034490501c40c0c0b000514410410b100081d00d4918100b02d041641c012148081000501c80220041015030291403c042034403913200013005400480c0e44810982c0d408141c42c3c00070740c070001769010200b240304c20070800404c122052100c24181103580303a0392100c0800110b2035007500000119070055a145105007417441040050041e64007441e0590260f82d103a0062041c41c1c584000d50f64a00d2404079900440c41c410008036440368045d840032054568554201c1001c1c9030820b004403525001c07c82003c0002240c0c91802e0120060190b800b074684940280020f5440d040510a40d8000c5425071201c441c01e41c0340000300a1040d8501c050341c0100d81c1000d02d1700d005a180c42000c0c2145544900180c40a44c03003035100000000d00315441248110b0b241d040841d00c02d1070120ba008295400380c0713812a65000300682500c1c0c5100540c8004095a15103001c952415600201d4001604c1c852804c0d940700d4015080c00609070790101c80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 349554181 1250 349552931 349552961
    0xe04050705043231020d0b041e0b0105040306090f0510020a05160503070b0c2d0406030b0d0b04080d050702012a0201110d0203060a0f0e1f05220b04 65
    0x4030064691904c5220020208060460650300c0601807101c02800251501c511a0071a0041000241102503000310104030318155010030520940041a049030f501c10348060011f280d42d890340007034a0344900c3c03c40d400b642c2c2001080c801c2040d2031030702250460314000300b03603801d001d04040308020200c0c9008840f05990030355901802e00c04002e4901c048866202821100b44c4410040e0100081403000807030b00c02c4915048103600d50a0351100242d0000079010b101c60f100105016640c1c8010780401624280d904030301c0c00040200d180d07004070342d078501a1900500030740c140c1001c03c8108044500101f15071410644284180e444007036069080c0d5041c00380046126070f60350f1280080c5204900c100100d9005880007144551482c240818070307600865010301c00035000030420441e82000c003014001403200850400310a440d00300080c2140e03030b001c2c00d2034041000c140e0411920782c50b0400000c020349001800602c07080700c0108250480d00c0f6509804034a2030906050304450701d85889019004901e00c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 349555431 1250 349554181 349554269
    0xa0c0519051005070618051207020604090b1c14101e0b130623060309061b07021309020a05120705120f0601060c03090801020a0c120e0405070504 64
    0x10411020460044140c0b040040c10b0026001046180c0254540400032001d003603030301038182c2001c0d42025900303030b94041c0681040240d44016103070f180468081b640c40c0c81d4000b4101403484000742d000144400d181d103641e01140000001d100f181200c00840d2440241240d182c8202101e0364801d442c10782ca609610102d01c042c00e280c1d00d0405400c2802004001080e44425801e0b2120020454420b1b82182002da29172206134501000e06100c82822104215011400c602e481001595698001401a000e51144500d00d040c00c0102c4405d03900c803503500401c52410301141440140081801010036072162030300200008030340c14030301d00c19030745035180b0009000c9003410181400221041702031a031070070744100041881c3c08c01c401d10070a40030301600d940d08426074081d800c004004210940101071542d1041041c01c404e2600f02902140da5a4807044113000410301d001d050350a11410003079190400e051000300000103074031074028000c0e580e10030f0201c0d0151541c05107880480c41410200d0106108070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 349556681 1250 349555431 349555439
    0x6020601140d020f06040906080c0d0b0402120c0411031603060506091c0f03020105061504050306060f04020c06010810060b121305160605030403260a0507030e0f0a0c0519 75
    0x3000782e001d055002134511584080070b58081000c5620035880880440e640307110502c14410305104020046004851020b04c4c8802521000100740f000b0b00005c0c4200404c0003841441c0c1814040d841c02c803000100100420701c6030001c5110399a0049038008485650703d0481640f0500034890401a214040c0c00d85007081e20804c00d200302840603652612402c40020144c200094000c2e603900100c40c4a580045101d060000900464007020315928514590500c000d01050b140025641e9002c01d0844102c0c810a0060011030001d204150030030881e40100e60010603410400070325590803542e034020402203241e40d00103001c4a800f035520701d200e01080746400f10300d050320701e8103c45000c0d6010b03000b5240210304072401d005075200f09074003001c045403001c4200424150411444503c0e10140e204658441250081e040008031004026038040c65445010407880f502c070780d01c1440307007005450844403c441003d407141d40c0d9100c0c92108640d22006200c022030281407414420350310720105100400d019081c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 349557931 1250 349556681 349556689
    0x5010519050306010e03010e10050705070f020f12010f0905070f2303072412020c0d03050411030a08121602030301291614120d05060a03140609070602060114 69
    0x4050602410085c0400641907199000c0c424000404030f80d000130040d5084a0211200740c40000381003000f8410701740824000f041351b10220380d50490307046444d0b07241c03500300b000011306021400303810416661802d2503810700d42c038203940800a0503005604840740c8503918000c5500c1d66445014407003000b001e46030385880d4685d2800002074100340003401da80c4d942c0e803a00710000d01010551146041c2c00f052180100b90203400120a0303041c1c00f4084001d500d42850b06440729602c0c41502082802c2541c1c80e1700040c188038003042801050744008060794040040750030b2030400c5400c02140380241d1380108000c03607050400300c2c0b0380c0700d5803001540140d81142e10344100716428220100042500038a40744000615028010061100d09c841d0b14070402054821300344288601c0803680480c181d6401038001910010481c8165a10415030b0400031800c0ea50300c0c0081850692540c2c0011700c1c041c20518549034150300407800358810051b80303080301c40e810361320b01003207985850a12900001854610740078a683c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 349559181 1250 349557931 349557937
    0x90307020d110402070b01320607060f0516030b0907020604122304060e150417010209030a08070b090c0114071b090c0f020c0f0d0309120602040509010501051905 71
    0x4000c051400c803420b281c1000c10700b6a40882400c4503450701c51001444a015508815508840e4001c038200d09445d030b184800540320f186080440c441d0402203502c808001d025000010503000c1c503441071002d8100294181d0440d1114407007200406d04224000e001801c010b6036035441030700141c3c004e055588450b03c43c80401601c40c1003010802031901c140b541d50030401c010411118128110095540d03180c130500911845680b4801e500c145140614100e040e0208002d450580f40d60714512446001e028615a00900c121050039403d4014202d45034248030904d0050036080b40151056000c945c0d5503072403251590340300400c140c0412035801d1a043c02241e184042d09500b0b00c6000340b02d80710301d64070800400340d00c4981d000140c501e46841c43d00c40d41a60100c2400f108101500050002d030400d000040c4000b02c40c8084940250101d2004506041c4101c1d0304000903e03103c60b80070356900301410068065030080c0201c0780640b555000006140d440f400881d40c4d40301243d80d940040305502e076001c542a40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 349560431 1250 349559181 349559183
    0xe0c0d0b161e08190e0c120304030209010e04170f0f0904091a0702010c090501090b16020901090906060b040b03060904031e051309020403021302070507030f0b0402010201050a05090307020d 83
    0x101074001420000c6401c40203a0b640c000007616a5030103450903403090302440c54903075180600341d420000320986003140014000d594400c21248540280daa4800c0300d46140203642c0301a40c04814500001010080403504900481c010600b81340703e11881038001440d0301c030340300406030401d5003081017600400710040a41681c0b80b00602c08144045a6101d1040449640d41402c40c8800c3c40c20901c680f943d0240b144a409070300c90300300701454a14201c0040d21041440c46031101c154070020b52101645100d040c17599000f54000c00b00c4005507124071511004180e903c4003240c20914102000c61b000e0b1100041c4c1c1c04841d2601c60311860741d550001400344d400d0300030380b084044c0140389080d00071a0b14841c005d0401205036668854032040244d503240038010341c4d80c0c0801c1266104210500c00340e02c3d46405140003103401d400c00759861401d0b1910525284081e07101a003000c40180c1c41400700070f403181101d40500d000340c0c02400071380c45d01c540140440d01c0645801c034843d40b00308990070050911550040b041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 349561681 1250 349560431 349560437
    0xc0b0a02091003020c060a0c020a0305030901020d050907080c09040b0402010c060b03250905010f060c14070b1207210c02070503010c05040303021c02060708090307060c030e0c0d0b16 80
    0x84091000ca41c002c4079240003034010035000324110328008020003a56901c84076680c1d00703105105001030080d4070b030102c0d44000340c1084400800140c0d0b81800350101c403403e00f840101013040d841c0401440c1d440e0140c600903120a401005500e616034509480c41c54041ca03045525032106850315401518500c2003e141182c0c0552205011106560140038501400707100d001c02941001c4001540c01d10350840d03401c81024686890014440c084080014500396111801d1030034940085003001452000e464440030100d100300240440d000100740090800980400c800300302c40e0301c1742c1c141a41c884075043e00322900d550040103400d00c5d51380e4035004040802c885005440c0d110380c0700e8010a003950b1003883d100010031310000d020410598100101c080c00a03194019141032140844001c0d2182c03409000c1d00c0400c08460003103201c06505004480038103500050400c40441d00c940085c02a041900140340075000b21604071301181041000c100c00ea0750300c000c40d0000342d5103c41560180480c600714480030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 349562931 1250 349561681 349561687
    0x60804030c0204050408091306030f030507080d18031d0904120e03030f03090606030307030f180b0a02060f130c0902130e15150c2a031f18030c0b0a02 66
    0xd602c43c2e20405008900419103580d5a201110070f105101c4145c03121a0407003850007008002080c07440751101c0065034145480350b42c036415801c00f43d0803030040742c1022143d586000203100f2420050070004080d03a22070307110030300480501e08866020f00b00d10229030350080b12f280c0c001400034040c040040240000c5041000101101c6000b0900e075401030b20112032106800000e0100c01a070800c041d5910213011001540f411740c0541d0003e051031600c450b103400780001040307000d6411101c0100c030760140800c007140c0354540542c0c220095aa040680d04e405004038210702041d12641152804000719070080d20901803145003d400b04000d5000b84007440903c1400d000200308040d84036041405502111040303c01c0d101c1020401040c545410503051007203508210b1440c0c600b40120b0072218401c2030701c844e8550a40000d003003403c01c00070100c11a5140c01a0b91220440c4a030f840f9100c0c1041d010031320200504420300c0c50f0303402c2c03520b0b06000240c04a042a0310780400075488010350355001c1e26034900941 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 349564181 1250 349562931 349562933
    0x10140402030c0111280212030a0c110406120f030e010801050a0e09011b121104050a0b0a0e0907050a0305010e0601080c0c07091803020d03150510110d0206101e060804030c 75
    0x1a46224810900d01e1714855a421400e6180201c01c00c0341c03d09004014528080040501401c0c505c481900105030f408030140813070403540ca40e0322003401003d0318012402040d030300d0701e4481512409031400b2004691030305a0b0041a51040320321038161040940030920a80c10705110340c0f031101004060400079901d81c080c40b401c0c401420504120317150300351111380c003030344200310030806035a034038000030300300b44000d0108100c0b070303501c1d041c1c44011075a00c440469035801d80300b502103880242c80c032074841d0800b00c0030b030610202d55440030051581c6022668100b103a640c0700c0341ea030072483c4c0c020703180c0c680061205d0003c90018034a4030b000b00034101c5054105c98400c0c0e6580c074010291744064612083d0001c1e11500c80c0181034040c0015040c400c4949400c100e4040c0e50120701d000e010b01401880d0003000540180003a903030040c000000c041e00102c0c01c40302d8140107400000e54514007214000c140c118018800a001070740541d02d0744558500d519519121810000c040729070b4140200260100551002840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 349565431 1250 349564181 349564213
    0x3204090303020a270b09193302060118021626030910022505030d05180a0602030705070222290d020a090207110907180b2a10140402030c0111 62
    0x7012081a003940e40140c13880c0c2800c0130988d8006000c070385041c104200031072581c0407034810305540d500d000c91079001d407400740310310000c0c0941074100701404040c4c0805001d21951901414460359552030214420221311203030b104d0360000741c400c04920f52084d07005481585c101c0e0083d0410b42003102018102c0c60361040f11440040b894403080e0f86c1c68000042514404c030046c058241d010140a12102c41011a04503050b03984180308000f5201e07643c0032012400c254403420494000580080c403000b81c8110041c810320b91095944201840305281c4010200c4840307107220305516030068060b1544445240d04280128081800800c80e80100c5200703010945114038800b90201601425084602031070300f000340450950060910400c1c000e807008880c030785c080c2d11184c0300140c449a0091a0711102a08449a031000c4000f0880460034106c01189090315000a039a04002001c24001e002c070100c850041c40e11468195406034041e04001c1090800d9400f0742000c109041c0240b01f00c54041100513084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 349566681 1250 349565431 349565479
    0x230f0901060e03150103031e2f010b0919020d090204050c07020909060108250306021204030306051512090c03010e1b0306013204090303020a270b09 65
    0x981d002c0385512907071442e5401c04009800070404500c0d08042207506540340608201c5100710040244c10440d40a640030610a4094500701c0310070b862a01d007284603030501844080c9403070f01b80c0d038102d61803c1351070322030b51600030b1429003d94903005039984154003030206070f03000c0c1d4804000300b015991240d00760401a100c500c00c0300c1c4034281000280f91161464410442c5a03080901300c240303603038030040040c44845400700e5081c11a404901400e010501d0304907541c0340c1d000c03095201512951003c5030420071080c041650602c100c0c42658100025600c5034100701c400380d11080f0f1407044220030312954951800c03201d221600440040c003165842c8422100081c03d460b034a480b20b10082e00030055040315030890410309003054104901810a542c100f195484010305407465074580070000300040c0c65210300c0013030034401707142026106001e540720302c2c100540650b01038840031000400c12429000c090441080d450b07205044014103501c643d1500f6000c1d4084d4104403180c6030300c12071080900303800500c09514 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 349567931 1250 349566681 349566689
    0x605040317190909150b03060d05160801150803130303080a09141f0e0303040201030506060c06010803130b0703020604230102070c081c020c090a0906050718090204230f0901 76
    0x142c0c6000c44c01c201c1510705980200044880c40c01c00e08506001228800003a00d9203c40c0541e99055a840d5504040d0300c0e01c410140d29417050050b04501003030611064000c41d004182440c1c0b142500d80c0d031921031a50740e02c1810130070355081d01241803c0c00068031828502d40c00600d030360004a13524480d03031941218a401000090f01c00c2d0301403011424044580c08943d10000c1d20040104400362285072045e03124440180000d04040d035840002d000c5135907601c01d6405540303402d801c40c0c000f0340e1600e2600740d0740e6211a0741c503942901c2825000900300e86843c12100401d5159025200c191515903620320703c5007419045540e4004000365070b600c800024801741c00380a00a2441582071444c0081c11070902415480120012205458521115400042400c4d6200d41940c2c04c408503914603070088020a421071009140e07905003002e100c5e1640d80141002007504840f00450303451a0385008210403841144161084c0c0b50000300c10b507242c0070b020361603150804c002400036404d1103041c100240d144002600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 349569181 1250 349567931 349567937
    0x3031b0903020a091e0507050705061303081513050901060b161109010b070b07020c060a180b0a0e060d18030531050f0103150810050901020301060504031719 69
    0x3420001e51800c905040300074269190100a404112403184e0f144070200041207003125226000304813258070030001c50310081d80241c1503c4032414040e50700300910000c1c4905400040300440450301c0d0000340303088030401140080c0b0110f96044441c081501400009040e026155078449000500815000c0203110f029100c12000706078071428078141111044912010340540210300061001808541c00c8070156034100c21400b000340e4640070128078041089010719088040418008582500244240b980000c01590064001c1c0c580b0bc91800718061150b40381c0004a402000d100103003080001803640c03c0e002180480d40100340341240400700d004040440010300005691419002c0400102e80400055290251002c118544184140030340d0302032a44603252240b82c16046a020394007030b44807908143c000c88150f071380d5403a98a484003000d03500c4c002c003a8102000600d5800042c42224181c902d01c0c0c44050070213045455680c1c10b050200e202c5100010b04100ea6541c2d6848440781400000b0f07076907 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 349570431 1250 349569181 349569197
    0x20717010c091401050726071103010e061515040b03010f0503211c0b0909030a0e010305061e130608030a0f17060103050604111b0712050c090403031b 66
    0x80202100b030301e6031003402110740c145002e2802d40e9028049a04650b04170425440400c2c5002044510790384a21101401590009440c0100075215903c0013010808900030002c284034902c4003600c03500c0888603030042d00000c20b400002071030202ca0442100310742d02c0086060940344d040c42c500c0c56000b030300a621700c3ca0000380200800c1c64204248150440d0340c240305007540031031021031000b034040d03143c52080005281004041080c00e81d40803a03002d01005010440c80e04028140c9611307030744407200f0500011b680d04585c070629402030044502446010f090040100d440b04000001201c0780307402150b000c0e2110501d80740382c1c40c0500031440542050f5000d103581d178901c540c000c0d214100036281c50701444010503c44414802008845a0140302800c011485554110006006041d021030703c1045107000700b183c8801045002101c0b000790040011504042c1d11000c4070503480181600041c96a440b0070721540107800c1c5125051b170814882e09001c61107004000f09410810301c04407228000801c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 349571681 1250 349570431 349570451
    0x2030402030c101d120a060e160f050d0203120403051c0c050309150c03040801051909050d11031912060e060616050a020a0b040e010f061b0302071701 66
    0x80c4200114031200701c0c0d007100550502c40c0c0c06030509072411442c14000581da49800c1307150f15401000c01c00400000295814a0b210385810300040009000b01e5001d4818036504c8080c5030300340d034400401d5a103244c400c4840c051801c0c0c2085402e011510040740c0500030403100d4601007a4910190000d14422000384c00300c200644040103d0420b00c09081d07040108101c0564040f5001004480c10148165492501c016000c05a02042d11410840b58010b100c0000c0000303850906600141c01407140c2040c040c0f2421082081600740e82101c0d1000e00700ea0851302d03440210703d004825802c110213946041e00d00f4545d01600070b804256035100c604021074200030568a040c0c540c0d10950000d001140341c00c8000c1e0901c07401042c0f06004140d8496070860703840c1d0001c4148981040305d48440ea900502c1c181140341c07501c3c4e1200ca00e03049845580c400c0d061040010070724103005c10401c0183c80305591001c100e2031089080c403a204010300015015801800800301d080c01c0c00036070800c140f200314030010486010b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 349572931 1250 349571681 349571683
    0x604050405090328030e0c0604060e0102070302060426240718060c030f03090b06060c0f03030a06080d02011107061d0d02012702031207150603030201150e1e09120d0203040203 77
    0x103080c8200b11b464101c0c00c1601c85d40d80d50b00e0305a4050b00c0d00d40c6090301c075000070f000060303180c54032a8101039405000403500080c5580d007400707101c41c94401c0c1408251a20029407071183d89130405606480c1605c1c0050301c68840140046103540d000301c0380d00e4290005901000340880c40ca1041d04094005400c4100041c280364012264200040446ca4100100c004030345400c20389000140000348121400541000c2e0008100801c1124105036000d8039a20300300040b1120007818144034041040c080e0b800c15102082c010b1040500c90300d09607000500e0000c540e52034000801c907400c601e10300b9407081404e41c038000383c3c200007242d02d20700760790000240d40503000c0d600808240505070800c040008005054016240410b000c800c800790a0001a180c81300351801440070a00f1240c400c8015140880000905505400c501000365000c4a15034044c0c1c0c9425028003000c03011240ca120303200ae805441d08080c440b0b80040c941c40f0310340b0403e0300d02d58031100036240103544c0301100500c0c185070044184400e501c0c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 349574181 1250 349572931 349572941
    0x6040b0a080f01120f03050307020109060f0b031903050f07030c0f050d030f0209060d02250506060a0b0a08070e1918060801050f04030309050111030a0213080309060405040509032803 80
    0x48031120130020f40c80d03195601d4114072403121006003008008000304018034000d4010f25100343d072000c0700340821101080a540144001c00585110b1b00c1015400114100340028040c46582c01d581c98034503243c51520f1350b84581c0e000744c4d000c03401c000301d03100184041141d0042c001c00c15841000a8800c003040c500008050360b04014100040d01e02c108201842e55941302d0481c0d8003440c4035107000d80c45180e02d541010701e08a0b07901c014401c0602e07090b00d00f410400d011603494820b450031112440003580f41d030580001809640740c018007050401001c0b4000c98040d4004078007101006045403490168580c18102c0c0490b00d40c401c0c1900f43c00c0da600c00820080038010100605480c5008100320700d40221580e51010005e480a02807568074411041401029001a100020324540884d80c900303181940e84000d51204884100c401009040801c611a000c012240704d404010a0a41400d0800081100900000e4455410340c07104126120071400c81c00000a1184180030011001c1285840007600381d070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 349575431 1250 349574181 349574189
    0x50109020a050901080406060f0b030103051204061706032b110f0601120510020f03090c01030603051c050d15050102070e070914040f1a0a14090c030606040b0a080f01 73
    0x50050080c0340e2842d500200791a6540c00910304500541c507030f82450401010f0303d41143d1316581ca841800b0445070074000c01035048902c076404950010318024440b860500883c0100400100c810010010740780c1e441500e0341e0000f00081c1038604940342008440f9600c3c05c414081c5003495041d451198055400142000340020858098280004a40019516548140034503000d03d90300035800c60501400b0001100c000c0400d030800c56845111001a03001900200c810011603c9400a00c40300380d40b00740030b4003041720351090003411400400c544000e03900301120744400c01c000c01808182282482c5004600c07080d121284200350301c90801c40020300381081c0307030010b202002c0c105007800303a40780e4400d0b00704003220b03400c40c001d107004101080024080d10342a402c00e8070050500c008030060341c20681c1309944400040315100c501640c0e5000c1c1c804126007403404c02c0d61161300710000031b906105000007141c0c81000141201d1070103848420b22425500100c0700800002c98040c10450810400d0f42e1082c090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 349576681 1250 349575431 349575449
    0x20705030708190c0e07081b1e0904020c070b0d060b03100603021803031c2d0c0903020306010f080c0904151505040f0203060a0608061003180f0302010e010501 70
    0x10303a0800c0d5074a6a203012044580c2c0f10a110b410300b042c28800089480b102038100c861603980181001d82c0001c1ca525000c0e05d004154509001e0001517103400d207002c640d0350107006d01014000c400099545070035600721442c01e90300030f40c082245a00401c418883e82c80600b0046d840142c4400c4c10740e00d080c088a020750400d0795105404c10070704c40b2094091031403c08035441443e0140e602c40098403808840d096080131242c1601c8007140b004a1003090601b04140758240135420014004100440c2c0d2050940c0a107001078190300f00e40f00c0c41201b0b401c0d00810100107150400c007820700d6036a80400e10f8020709034055050b07404c111805002c4644140300001038100c1c122100e003d141000c0d1038000694030072140c80a10243d8501d103850701e291519a2001c020000104200b02c40da00c400c000c90080e5000700c030f0f80f6205003408003000c10030501403549180580b5019020082c0d009074240c0c1074004104020b0001d80024100d007144000505940001a0440c401d074008160180e20141040c25210180c20880072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 349577931 1250 349576681 349576693
    0x270b0406050a120f120806120304050607080c070e01061107091a040f0f020c01021b03072105070503030c0904142503150902030403090609030f02040207020f0a06020d02070503 77
    0x2d9842d82078030b00640b598003007020102e0825151541903640080c0d0010258082501ca1000d0a41c1080c151849000d0541e529a03c2c0c0317182c0f1510645034496406610341c0700d40140522400301c0d0f01040a010805000421038001d40e485904894000c1000d0303003c0380003d03a9a0107800c0b201c03a0113110440061171070340f0003408420b0b0903040c0d070030b411345c44e2080d40c9002d81d07034429100d50994401e400c09082e62550f510300319a03800c01044424003070f6000c800d031005404007010f456083d05000104071204c2a030401c580c0381a00084a003411600c03000401c203081000000d0002001180d41032000314081c0b100d007c91300744d0b00d6620784140020f80e00d085040c60a00251181048031444040c0e4980a42c8210b0142c080d000e03180f466000c0d0010405200300d60b100c11002c0e8004211061650f00541c00b0718040d03160484900c1e41d500084940c01c0c19400024404140d10101e03000504150f00984800343c80104114558100c1c4400b02d41c101125034002001a400b40d2094400c103501440b0444c00b8180503809004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 349579181 1250 349577931 349577939
    0x3010f170a0b0c180d0b010512070e011403030415080105040b01030203071e020a1401050a0b0603010f05062b060f060c02030c150c0a060b03060a0b10030504020406270b0406 76
    0x2c00308010040c1e40c51590009200c0140710f0590382c00700648100130000340340d11003070303003003000c90b020707090040a00984400040351a102c400140f0503080b11000510084a40e003401d503000421008400b100383c05220038000841c200c0c4d00c50207124040d44503541c0b006170941c500700802c0140e83c481c0d6100b505161040050095041e03102e6401004600031070201c410446c0518012480c00010b40400b411003d000700f0900003d11040d04894014801303d082885403001403c104680c5200038490410350600d252420005800e01e00d0240c60001101014010501050240900941441c10900c5185662800180308044001a2134406010217207080000200c00c0e03404603640d112a4108640b203020701c0e068121003030151204a44c0000701c0082500c401e18400e141400c003406041c21001e2190142000081d03901c40c0c6071190000c0134800421200c00f010000c0c1c3c00350010200540140e8001c4d40307400010034641d41035103080810036407880c60003110219144500045070490b0101e03600c42c0c5c0c20443c00b04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 349580431 1250 349579181 349579193
    0xc0306010c050c03032703011e05070504260f010204050a03110d081603030606081006030506030703020a081b060306030a030516050604030f1205010303050f091503010f170a 76
    0x254400801c0c246110032250300c2c1400c62400b00380c40500e5615100c0090114110740c01403400703401103540f800000e40c00082c07900c109426100014042e5505203140302440c0003059894101980103a040c1c203010385440d0b00d624401c4524620700390800384106000300c124080c440108401d15400b103600000318280f5040c01d0003c0c5080e1128403024000302403007906001c0c150b680c0f0b501d10f902c0581c00b800085d61100c103005034959072000c60b0781c2070700480d20b04030001813403a01070b144261254441725400d0380e002c1d040000582c000e000240c4507035010310a2000100041e140c200c810700240961100411030004240300f00e0351240110106a401401c06105011180d10001082c000c01d81d07050801e40c2d21480c821a0b0032000440011000d045480b40200703101c1850b800c1007003504103441c10b6a412a07054043c003424000d076032007880010009101040b5203121040c4100c09456041002031026503050f180001078103650700280c0001c5003140280e04100014178503505624890038107200075003504400780c3c60384 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 349581681 1250 349580431 349580437
    0x112050c0a030902010210091a0a0c0c02012607180906050d02010c051002030f0f07021506041104080a0c05190308040501050f2101060305181c031d0d170c 68
    0x2181c14075840d0850306086a0007444103a50311100c25804000110302404c0c44510b038950007014884d8405000301060138084240600c4050361002e803a09160000103030b0045501c0e20b072500c2081e40f0b605c2c03080c1240020b01701070110940a50001e03507410b217001801d8140746810144030351007030001c00e15024081055441d0000030015641d02400c1101d03c5400b5414043d05000196103070004103072000080005000e41136104602031444a0b12002e00f950b286641660f1360002002c80c08403d40031314000035070a1610303401030441c01416403805414581d440500514043c0151400c03220700d18184000d000a080c031100a0380b205601e407007405d04592841d01c0e441501c0c412401018104007001407174850014017402110741c0e600d00c0140710341400d20002c0981400800a00821002070b003050302203034800c034a01841464220b0303820060490070025041001c2c0c40e001d62680501070588030342d000580760720480030704160040080050000d6606003a0001c0410710500b8007030000195580911517404003020030703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 349582931 1250 349581681 349581697
    0xb010c0507030605090c03060a153203100f0f0b030a0c06052208010203040c05012102070218010f1802190c1b090606081006020d05160b0f060112050c 66
    0xf0000380d0b9218852201d043c0b4600e000e050b130300340c8212018480da1845075842441482e60040d07002808a03120500003080c42e9040400d80100800000701d890030804184003124004c1c8000c040355420612030340c8110982e103161030800c0ea900d50f2013145415140786401180948142200a44100350340d41c0e95054640c1907030f000d1002005004207484400144201452000c00a01c104030151581e032004201d020f50b10443d0125810040e9110014195000d00c3c07440d030078038803015481004c90040031403400003034028210503070748035540070031400181d05030408541c06080d1042c0c00070703207250920201182901101542c5500c0a204001c40c1110801000501348100c660380b810300451295410809104052480311040510040100040001441e0300200480b00d954540360b58a640d0480120341003080c0f48101d4015800545410203000d204000800e001d41c0b100d400504104c20035191030340403c0c001c80790b45034110160800e0041e15038201d4003d42a40780360308402e010a01d4105010661030055200b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 349584181 1250 349582931 349582943
    0x8070305250b0301090603031106090c0105071a0a1b0203031e0702031903020a090b041503050612010e07060e04020a090e07110f06070e011719020405220b010c050703 73
    0x1030055011000781c00d5002000c9440e511601c80d6100c9106600500300b07440103d010502d2480a1500e840e008629280300c1c07000390002c5c1600c0d0f8200c0006503540d40c80034501f02e035014554940790f04145000b002c80c43c0960310111000400c1c00420032440e2410821594110035980113004002e21003415900d03070581c2c0c105003540a04580c070794260581c80c4d80100c03054001005a000050b440482d0700d03901401d00a002035440c2c1c2151543c070540e00d02e007841113000b0001003450140e2076240190181d0030850304070030050301000984000c00807140c01c54040a1941d403e5801840041110941c002010b09040780e00301c908514160442d00098401d140324410401859403d50008040ba4014410520130380c40110a0390305801c145036809031150012160000442d00750705c03000c0503d512500071003000449079102512291225a040000543c001140000c080d400f00300102d810b803508181114241800d40051024407400e940c440207440a80e0f09083c108801c1c611000c0c08150000b580c2411650061 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 349585431 1250 349584181 349584223
    0x70e0a0b0a12030f020c01090b07060515060d0b100503092d0312091002071a100b120601032904090c03120918050708010b16020406060c0c08070305 65
    0x8010412403051640800780d859500c51140702455081410410034500903806d482900c00c4c11001568100945d0040f548c0101c418410040000c00c41d50100e500143d80103102e51203585240001010360340001d00c013800d4a6242d5206d500d903401c186900c0055205903003045070441c5030410320b4a81d100085840891900481c1803401a041c84083d004d018186021b420f0700d07a580c5e40024070700303003120080da1080802d20a110041018020b9842555080d941c410740300d5940204900e0100e01106010704040d03140b0415500c00503100d480040100719900401e0340400086c503003c00050222100c605000d1241d4460365415041e60521a591403c1c41100b04c03000680090a418000304004039030304000c180c0b056550182c060b042d0841c0d65202104c41c0128503941c0c0402c1d0110503810380b030702620302c0e002003018540103000031002170024104800080020940400050f00080c055a1440d44580c005c03071002041c0b142440824080040500407505c018140180356a44a55445418114055202041c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 349586681 1250 349585431 349585451
    0xb011407031b06150f0e0601050403030c080906130503011b0e1c020406090207141908070510060b0405040617060a02090616050d0305090604030c02090c0d050108070302090108070e0a 80
    0xb140d01c0d981c0040c0c02450030403401e070f44010aa1080e00260107100f807400c3d00c0002c00110030f0740c0322402c140b01c0c11048e55441d08040c03840c1c3e401d403a100071013441101c2c181010304c81c1d0105e646446000d080158100c0302d00452a071300c0d02c0c01741801c603a988074013840440c031a01110803205421030728080c0014001e4807040c99000032203100020f040a83e08000754030500300003001030b90800341d030041c2040500801c81e00845201d01e1500c207941c0c400e54107184d1005d08031340401001003604280039150351405071060b58522566000160100e40036500300721400304000c02c0a008500380b9101d80005800d5440d04070a100300081d940035500c800040480c5107150700010031141c00d4541000342c502210700381c02d001880415a2800c10f80780c3e0031000c240c100003460040044c102e448000342981c011501038580c1041c900d010b4090000145009000d009000420858041441d0b103c1c41003038020200880600821419841000803124060740103840ca98880c2e8420320020720302d100701640110403907100044010320 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 349587931 1250 349586681 349586717
    0x3071701020d02130303031401080a02090c16060614180105130e030a1d0603151023071703060a1211061b0f0624040e070611010b01140703 61
    0x2e2038100080c20360002c1203000800440c0004c020990384207480c01e00c402041c6204851400000b4441d03a4600e07800003640c1c01c050705080ba04142c0040c81d4101c580d145c451141403c0d0721032a00b040d4221004c44d50340d1410080005800c900710340b8040212804504c003500213000712414001806610301c213044181c00c80a420041da8480100c2088640680c4c0c0c80320703416880a40b01103400102c01c1c400c0808000102a44d2404130212441000c0c612144502852650103000280800d482c00000707203c01400310f108440007103811f011000442080c0c00350768405174544490150701c0c80c214201002028818003003103580399928402580e52518120407440c5290400c4a0411070444250760041000103040017000301e90301c5503030074000e20070084901c28000e1440090b50342070101c84404030000c800340034129000181a0240c24114003c0c400f28401000036419030034a01c25901000100d00c43d400b0340b580155003030103030500c0084242403c1283c44031801c3c804855105a4038000d003000a455a20201009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 349589181 1250 349587931 349587937
    0x206070504062708070f060e0d031b0b090102220806060d031701060c02031e1209040b0411031e041e060f0627110f031b1201031707020307170102 64
    0x140d00f014008446a940f10403540380c0714140100f21103840341000100701a401085014800c60000d402c10580030911340301105c0e50600200703801800d40454601c000407550500d030701401030450200040c1d44903481c03480c00d400303081c403286d1851800300091010011484041001542b001041d10003800760101482c04031440406810102c0700381421200200e001c0da0302107440c95403d8401d40c21100d2104000b402000d00600650f548c07080307a0300504509a0450000c005040c0e900405800440c400c101c940000b415604400c41c450515078000c010084901e400d00f03801c24519031640c5c0a10098102512108800d060011071841586c44000a45080001c1540006071581e41c4079800c000c143e03100c10070400d101010342140c1800401003900444044170718031a40000c9511001014a0140340302040c0610b07800080444030141401c0340d806007018042130042c004002e118034010030741d605515000303084800c0d0700c031740091449080c003004005880014009040d1030403520f62905c42d20703926040c1e86c062302c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 349590431 1250 349589181 349589237
    0x15060c030406020d080c190e011b060b1903050a030806010e0904110a140109090c2102120a0506010512040203010e10060e0702010905030403030c0c030209010b0c0d020607050406 78
    0xc4400107001071440e5020521034032240103036440b01c0380c50301c0c0d07a8105c111138080c08840995038002c01c0c6103005010b0040c10714555034481070410b40103802000000d01c044500200d0283d800d2921000a40a036240401c21000000c0d100240c4079035940c1180c85456030b882c0c00c0c150003800e02130b01902043e400d0b8043c00b484100d68800524aa03014a0b1901c0d0036614803500c1d03400340703010311400c410124000184000d502c0047c441070303645c1c420b09482e100351103000d0403095000500703100541c4840000440d1100d00c4014540c0c90b0b00b400b40c3d440c03141203150034200000800400b2a14681800d202c49a03034000100c815081d0950005d900f40e80300c900020740181074184403440d582c42a49500520006c1c16044074040b81c07049500d0b600103694a0106030b09031182c5100040054000b0481400020b00480c14410054018416011025180c1d13000c21806442078102141c140c2d00800c0c004c0d18283c0c00c001e12000300006101412443c1403d003000380044c01180a004d05000c074400408180c81e1400304521506 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 349591681 1250 349590431 349590433
    0x180901050912030a05190f2c0d052808010807140105031314010203130204180b0144010e010b0108151302120f0106140a08091603060204050102070906050915060c 71
    0x1c18495021340050440c1d001340d000000d018231302c111000d445007031250244c681c9000500316440c81c2d000100c40540c030071010001b0380a108180300354400007500c441d2000e42d1b00c0e52075038015541000e580134a442e41a9000402e5001c002103409407991b03119056980101660304084440102c03460300443c85501803c0c048045e610200c200900c001c03440d01041c800c24000d41e020070000680c82018150300043c21000307020780300048010090462071075010340c1c4055014001040300c1003194002504180007905640b940318072601441c0c1d00c80d400780314001940441500030400c444840001801070040208580642d0640c5c507005500740d191070035000000403540c0c20447d80d80c000004081031404041d62501c0016901c84000300303a840c00382e50300b0040c1810307075100c1a00708840c46404458510000706041e119008116a030100c145000c40c0e910081c503c901c1000d40c8550814000900c2e0000c103902c400612402c3c00410402034503145200e80d000180305001200c40c03051100812000d2080d8008207400d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 349592931 1250 349591681 349591691
    0x1c050c120a140403080403030e2403010e150d02060a03090611040e0907080309060904060305060a09050d180b0a050702190e1e071805180901050912030a0519 69
    0x80240c0d000040416681030b0702d54800981c0654001c88150159000040404904000504c0400e019246001c440400280300c4050940304464202d8105041d4400d40d40c203ca010006110b0710203510000d507804070b0600c2218600017400b0000950075000140080d020f00c2c0c000440c455a10301c250041b20740c0903080b2b80c00380030050f40e82c1801041680548a1600040d01c104085641058049007203c11036140500039414080d4040822483d944047c41c2e03903901c10303a13481001001030014040d00e446420803600000b550315071130800e24203120040d4a202c3c10170144254160303c004103039421000b591950390440c3d4481c01028425952882140c3e006944816a818441b0070b11a00c41903000c07d40300c190001950540391078a03110847c0c1035040c1c8040b0b40030304950000c1c10061140d10b144096038003401c04034074280c2d03503803001c80d403403088054090303028040e06c0c820880110000d004080d0040c00c2c00d801440b9901144400404034080038002c03000c4141c840b0040790510f04068038607031062800c20720400c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 349594181 1250 349592931 349592953
    0x1020a02100c030216060f140405010504020109350309030106030f06060603020702010c060506010201200a09080613240609060302090f060a1412070e1015021c050c 72
    0x140d50302072a1004549142441030351a6072510900903106400d4a02241c404108959600c40d400340c0040c00341c5e10880e680d12412225030801d1103d01d82e005500607000060542464000104402c07000e0308400c0c07201100780042d01402c0d1114800701d0300720115410154440d10700c00c42c01d60840c480c40c06150790541c242040441401811384001b043c640c481d030700070084030342e0ba0041a000e80c09106d6000c0c0c04100c2000c407510105580e03400140d40640144000641420364100103400700c001200d80f0625108049400d0f08034a40081605000c3d003103140050849140118410400b403d41035001050006104c3e940503802c11000d084034100307440007005000d901e450f80c140c0c20041201e840180d10400107070020551100316028041d006010182120036001d052885000c81c84101b00304070343d000000d0800402100d00706000307080203070262085000860604d02005000d50100742c01170400b10015090346011180c002801001013407102030b8894400c980b01d0419103031801501da28900e140111f40c1003071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 349595431 1250 349594181 349594183
    0x25020106171609050714091c081305010203030108030d0e0a08040602030d14060310020906091503040c15020a06090c271803120b040204170c03060c09031507050c01020a02 75
    0x12442d4607915000c00c420326901d405010558801340c0346603000c9001082440d058050010041a04500141100c201a41c40c0d80c1003072007280309076000313695903c004102ea000c0307072003021460002008248011829541000280b603141d100b01c041e000c4100e039a520403c184440d0a1000205a6070809051031321680c0d14a8003135280d900c098410040305152002c500046046d9004103405100003038010940004a81c103940000d50007203c1e40c0d988004140503686042d980c0001000d1003094000455441742800c1c580381c1c0310901b842d088049070900601c021f1130f20f590300081c0c1c85031103904000003080c60403890814400c4c96010313410500107880030031300d00300103800780c0314000030001400c00bc10015130070282100d40032980e04020080c002a00f8850b403081a02e02d076040b0301c88401000b04010300d025a41d000072001c214801c80c101000350003c0c1f40150b001d00d414031070a42d02580350030071039107007590340400281ca411003071249002035102c601c04a50078074030580c181d55945000308021035454001c00406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 349596681 1250 349595431 349595443
    0x3070b0a0305060a03080702010c080904090f02270c070614090a0506071809020f0d02130e060901030c1205010905030c010608160b1209030c010c030c03142502010617 73
    0x10020904090101e400f0f4180306408008580d0080c26090502c00240c7c01192903041c890b4041e02c001c4010300184c0c00603984ea12590b00307450b125490b0314045521500c1402038200c0000358a040b58001c2940e4030708a0725400c40c80343e5100c0c0e801a01250b80e00740c0b62410400600e00d152207445040c40c1760003040f2503403000056062a481c06101187c006d0798402e581107031448c1e40a8540624007500e02d03820440c010446d00504212483d5100c00c608001d054501b20040307030420108250100002d240800c40c0c0004180c0082e004082910a07200542c1162600b143c215824812004024076400d50b50701407010a42c0400110340c0d220301500d603582000b00b025070103000c240c098a1000e0060b6203401441030b401e500c0080454424070719060800d818011104410100102400300c10302042009204000003880780302d12481c2c480d20700260343d402c0d0030002021504c02c001c821800c880c3c9141031020144440c1074450806c19418410b21807038400c0c9804038090000b03070303200326a0a078250f0901840001c000c00c00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 349597931 1250 349596681 349596697
    0x30c0c030506280911010f0306180c080c090d0b042918010203040203190807050616030605101e050c03070501050105011701030c15050f030a0c090506070c0b13030203070b 75
    0x141010505a0021000300c13400d29200801c0c0c085068213003002035003e040f1034940c48010f8100080ea540c1c4d2080d031540349034250740209141e10766030b142414400b9040b4210702c1e00440740e45601810080703c030000c00c0c8038480103180600501c0d8103000050401100e1504242101d9081500c282854544280406007010076a030700b40c070006043c400480208014030a0303a1145400600810b881c181050341e8a908400c032040984031b650301007007a200820b008129282c050000c01d0444001c0a11015000b0100c80d10340d0080c0c1d11929201c0c40000110750302081100c09403c0c0f0400d883c841c034024040c2a229880352241010380b40c003001c6002418410306510040c1221020780356460060324500d0000f00c0714000f40402400c100900006000e0380c4003040b0310700c90143c901d040c4a0b2070310304100d400900c0c40e002101c00c00c2803503403500c9420040307940c04104e03503000b0b100550708103081240341e54030255409460f019011020501194560f100d18003591043d00440d0090250707440700351208000d1656600282c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 349599181 1250 349597931 349597981
    0xc070204150b0a0f030c030209010512041e0308060411030f0f150a03080c150c03011203051204051f0204060f050702060d18030305130305030a020d0e1e0f0105090a030c0c030506 78
    0x1e4806c65042c002d008865480b401651010724002c008a41071a80f0600035109a85070094801108100782d00060041c007110701a480701055480d0070010441515900c0705040c0c400c64042c82841403040340d42103541d401102518410360503507100030103001c00c4005034034035640c0300c02070580000500890b10010b02081c1c2d412401e8504a401d400c801111038403041d2102e400c50801080100500c0c1e40d20340c2c0140c030b501d03c60b2800300d24106149a1100c80000140d0301030f19240c1088500002b0061208803416805540420560800d45001c0000c0c01c2817140340505003d110001410408550b0340d00d0850b000300d08482070800c200c2e0014004241039803000d80b804c802180c40d1002013405400f03e14103017440c00780c0c1907544510316910207070404081d402024992242d181c641080058554080c00070800b00014030083c02e05901811006500d407602105403940c66915001c00d01c8910304000c40c1040030560103041940e44040345140c00c644203c0301d039002401a00401d018800d503420b2442d0f03000c0104071650 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 349600431 1250 349599181 349599191
    0x3010f081005070c0201140d0207060615020d0f0f090909050106050909010207021003020904230a0b01111c11030406030b1806010e04050612010203040503210c070204150b0a0f03 78
    0x5039040701103600560f483d0012504a004140043d80300f41024108250046112801c001480000e901640c0140030212040358880400f440760f080e007000d5442c030240740d5100400c1c1c1d00c2041480580300d9645102a00c0802c000002c083e040940251038000051030070380e100300003100d450b0505034000c00079402254032504460300071501e045014025124102d80003041120186009101a0700940c0008800741d002601c0381e83d42d140340050141604400c48121041989500c1c1142c1d00b24120790302810b110b418000107418410816000080c8213844103103032001001c00300d96240098500c2d50b4000206031440c0310009000c02c0b03c41c0d140e000308903680320a4920569480080070220310303c2d4001c80c5c0644c0018124a000e07800ca14085e0800b82d0444c0010b030003100c91840d50201c135800c5e82d004031004d888075400028181c400b505240c120b00388c000c00c440141c01031410800850400d52040e12006823040380c81d0540080825a056603c1d03006042402d0483d60303404a8130b034041d160700110b12006010078505 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 349601681 1250 349600431 349600453
    0x207050c03060c0406120b0d050604030905041e05151f14040605030a050604150815090a0305191e0f14030603030f0706020910050d1512060207050c0603010f08 70
    0xa4050f005400c40c2c80928146820141c0403540480d06c0011050b0190301c0340305c0440303140c40e00d1414040c4280554090841d506d0036090180907e607042d4400f602031490f2000b44c070070f0300d0500305408110350f10b8010089115103d00803d4048040d000d03920551010350100700c80340000c60104c84140d01d011503100c0c4040e81125040102d640d014030f214072000314000300005141010030b03501042d4491002440010ba05020b119100c0c8034007920f1700300e0b6030f003940081e07a02c00040640f0654203900007000c40003011007440c6650004c0140c0151000d04990783c5400f00322014044c0150500c02e801702481c0d582006e01024070707000400164200e8120808910440e6040c403042c814401100d101d10300141c02145041c0510711000301c198481141034a900354240282603003660b6a081180780c1c40b903203503641500c90492a07507080403104910076860301c6502d16402040780c045421100c1e244550001d01c0141c072040307a030070450f007880c0345503940d036910403030000c008078610003030404010644070304504032968011070b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 349602931 1250 349601681 349601683
    0x30f08041e09181e050708030307030e01060b1e2107030b04050928170a0807021915020318010c0f0207080105090303060d05100e03090f01051e091809010207050c03 72
    0x200c1d0308050504e240584a00314103400c44050100d640748a08220b0b1641550b0710403140c1540c00c25140c9100298079460064400003003409581e020301f0148065525082c84c0c000e00d601c016040503010010b001c804145540e04207004440c510001d00300001c1d500152409034030080080850800c5288030320314001c0450b43e4001c00242441d440c040c40d011800b0618400c0c56020b14074144144d044071418812070303010040c0c62074031002c0c0124915a40750b002b001e0800c40030203420082c10501e003c00041720a0300e20f02c08a5660303004003aa03c01903040050b541c0e2164407500d03c0d2a59001d1360001c6030340c2058800362800d85e102080c0d030800c621960aa8000f152110102401e0301d8052f5a2414243d00500c042003881c40d18800400889121b40100c40c0303a010800c4221055038440384450715a904045118460b0b41000d40140d07403165002d107095480c0c440866262800c0c03448484008900500100d01c195880d110b45501480801c1040c8410344d0500c1d02c07000f807034080e40c0241d81c21580390050603000790007414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 349604181 1250 349602931 349602971
    0x20907051804050c13080c15070b0c0702040b1f1103040609090518060106020705010f09060210090c1d041101090503030a0302030703060e071106011e030f08041e09 72
    0x807201201080d4081c00412003c0d01c8060040b0707a8000d001c01443d484001c201d681e131001040204080d0038484d81281c10010788d1102c103094a0001e802c01c004400c0003e001d4111180c0c8452880d1070705880c3c2c641c03030022070002c0c18040002500540d4111041d41d00301c0200c40d6410815405566035a0799404039209140c481c02248143d40c0880c840740000e10131003410b600321582c05101d806420100082c0c021030945040710a0340414003580080900b0711031941d1100c19064510594240240c1d81e07032078403c1c0254de602c828180c2401746076450fa0a40100302905c0305210042c0100d40300703402000701c0110f985c0040c180660301212080300380e803012410b0754000c90400b000c50307400030003550502000ca1801d0f0042e500080548040680e68a400300f83e840e00c501d81e0602400c4107079280f4888513001620945002010307004503554210204403e881603144400c40d405507a4029040c080b600d4540ca0004000d014541143d2110b240c4150501c42c03e2103807144140c219201290107005504040785c5c000d035800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 349605431 1250 349604181 349604197
    0xf010801060f030213270302060903070201090e071101110414040b09180111071103060601090b03010603020f0f04061707031802040513120809070803130e07050d020409020702090705 80
    0x200509000c2016103090811711640ca000d0b0340d00822028103140390500401d00b410720364171100440000c8103051542c1000f1031a03000ba80c16000350316142d00e940000e13007010361602c034140700168a04009140d8901c03a03c8080700825040c4000c0c0202c0d50185020300c1141c1050103000da040240c180e890440d840d240c01200d040c804050f0040403113845541c404401413040201080240d0b488003406407032110f40030b0040440da80511074101ea403100e407400f01800c2000241621781002100c0e9000d0100300c203078004603811140c480c00c0042e40d038802c60742d09990303a00031030f811009043c1000c200011400c3e0015015060144200c404004594681c1c10503802c4803c01e01c03200500c0c440b03181d820340041c14940d0016401210200d140401408035a548011100c032003007032100000c410310113101c1c80c0b450420004019040c484051801d03e11511043c00401060740301d100240242003020800441c082e400301c58403901c038080190341d116281c10071031020798040c0c00224003d0105c480000c001038401c0096a00ea4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 349606681 1250 349605431 349605449
    0x9060b12060f150a15022b0f0f020f070b0d0606080f01030206130b0313060c0302120c2101080304081911040f0f0e0604021002011e09080d06030602030f01080106 71
    0x1500d5146204648100301c5100f03c4e0800030340400402c03490400800b9045201080e40201003100c94404a0180380030440c1041c01b1100e42111910300c0b843c0c128043d00083d00841c5071074120a00545400c030300d041c150800d000e44c030b4050b418021860910100050070f0300d6008004c10b00142e96921412285034808460311000124118018001407030102c000f8a40c03040342032082022951508143c154540c019a0800081100407000104210440c09070090905a908085040040c540e07136030010720500400b00c0104a0700050b070002407000340c02c0880b10165a1980300491988c4038003080d5602d80c090300407000a0302c00d51075035011580304194000d40e01c40e40035050a060010020601014180040c0341991302610f56030110046555482206460090f4034014006410680188811120442054011641000c504042c6502c81007041d0f0039803176844a0000304940c15080c0807040e4018050406039250501d20000b040c011a60060742c02201c408484a00d1a644d403521703a0300b203510074811007001d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 349607931 1250 349606681 349606711
    0xb0f0114030402041b020105040512090d02130f0603050303040501150f0320060a030605040f021812030c0a11030105091f020d09060207060606080a0905071401030f09060b1206 77
    0x8580312038020703581081c0b001e000461001d0902c10b034001c00c01030f44550440140c0d581d000b00401e100d01000102d42c5644d54002d058680b0301c200010602d0902422800380c003580c0540c203843c1c072a41803540030814a1501d42000c00910743c4a01c2c1a503101c1d030040d04c06a680758200318801c1625041c082100045800d00c00d0f12007801451a41c4a019030083e00c40c04040d4500301c4858445251241c0c40182003000c0d02c2d070340c0098250304110801040b00c000b810303000612441400000f00104d10307862401c0540034122a8181002a01083c1c9031440c4114000c58505000f402c00c0c5500300910b4160fa003110440881c001d100b6a43c4507030a46981e410710440419000c00d1030304940d08414065030081901030707041c0d1000b080869654441c40189c5c0d00004040381c2655640a0800c84203900040c110b030005154103045c030042d00c0a4075035039650b00190060700c07240c0713605c1450b0b116940c0c029486946a54074100e002d210055103414560001c0001c02c1c90b5601410440725418070314440072600500c1401d96000d01c4c60 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 349609181 1250 349607931 349607957
    0xc0406020a0f02030a0605010b030610090b0a1112120103060c0203070b0726090a031b0807060b01090e090c010e0103020a0219030e0316181a0415120606090b0f01 71
    0x200c0948402c205907094007506078140e02042080c01524080c0c000140020781e40c0c02c1c0402030001c01c0c61400b401c0c80800441d0348003800f954042604840d010702c00741c0f810601452404915505045105504108000000503d01e055808068050f41202d0040030104030754100240d0990b102c2c1b0500340010440c01105001901d8207000d034a1121000030a503446000d450708040c402c540800055840e001c0c0382d800442c2c40020540c1c08180e1000d28800754074000b0039000a596100d196010741c02d4001d0040e52540600c190f281d00c5402c01d4001040007c0c070751407090424060464541c4080030b13100c0e0019401c040d4456555000b8003c41c0c100c0a1694000c0121920501c1c1480c100416000210300304903180d02020004d0350100000403180200710325400d00c8601e0030121704c06d581d40d00c0002840290504180c000c2100c607500300010301c1c4005560100d103102c00ba446861940c08540c02c840100464101c848080c4103095000c18199403c1e01000c02a29016604010501004212642c001424100780c14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 349610431 1250 349609181 349609193
    0x27010210020903100e0f03070501021306020d0206040818090408070c1406040918050105090304080120121807090c031503020603010329150f1210020f0409091a0c0406020a 75
    0x64100018006d580000e0f40000c3d0050841e80021000e0ba1b840e0f40114008808040403c64100105102d000924940c0c0309400701039151807004002030505503021921205c80d0007034200748069508010401d00da139207070a04d40f81038681c200780d109494a01818101183d0115503030301c0000d00380c2c0014501400c0515001401d4082d001c4078514203281c0d041003000c2c42c00603500340511402410b0b007174099030310b40381407074402ea0840e41d00e04412000b2060780c10141e42504c8000301101c01454280c0c5c810041c0e580c40d40460b011410020a035403070b0340e2052000c0058501c415601049800103941e80600c11502644510509001e1074000a540004204010000141640340c0006c014020700000004020740c1004901020412940800d84241700c2030303078000c641740024410f01260401c9500944400503c008141d840344407542c480c40096000800005682803001514000c0003e40c1e81448000b1152410240f503400102001d80703144003801c0820746454440f01030300d05990007a07004201c0d070041c179141c40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 349611681 1250 349610431 349610441
    0x23180921040b0d0902030102070c0515030c0f0304110d0303061e1404090314120105131406040c020f030408010b030c060c0c04150503010504060506190303232701021002090310 77
    0x11250f09692940c8410050700d007030010745401c9000c0c05840501d14500b01c1400310101d501c03001c804803180c1c10410020390600c4142900d80b13844000740f46030f40781e580740d150031100c80300b200d00030983c00a40d490314001003590580100d403c1d41c04249019205150801c14606800e4803405208200c401b2400c40c01d90038146507000c0a5424068a441c000a11041c50080749940c0146081c0b450a8243d00050186050450388800c036040600000c00041280d0340880d22003e402800c0346207c1d6880d40850348081d882081303020fa1440107241580e548554a01c5254000e080c58034040f400303400f80e0002d0b64460701d04941540c081c265010090300c0001420001c01004010406034141d100038030100100726034400b40324892140f41b0854002031103003002c5040100c28110703c100c90000700e90062062001036800344080d00c141e40301d10303200044011804080315071030160400c05892031220300b0b40d0f40480f2480c0700301d5102e41070080e002e4440c0343c135207056400b040c0d03c90440c5498043e031054141c090702d40001e5000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 349612931 1250 349611681 349611697
    0x1501090218090709031704051e01020102040b0f03060406050111030a050f0d1e0b04020408030405010e0d0602030915010602120f09040b04020423060a080123180921040b 74
    0xa460605a4000105150020343d8101d0004155040a004025615204c00641c101d100c1e800390803d841c1c400000c10242064401c0702490b00c034541c4c405103c0c1d0007501a00c002d0318807680f030152a07034012000d800450b0422119240301d24146071002615501035035541e0030420614024500d01980c42174240c507264082d07545c0107007004e02003010a0407200740f0712a02c2e8101c50720403402280e16181c030b0383e1076003510350440c1c41d03500c19841048104003c100000407101213400a003090a140420000011540c07205032001130070040c000020440d154001240c22111220040100912641c07500c03c101da640240702e2070603280940400c142c448041d40140940b405e118010008107600040760007040130307038009a0058641a07a86550a40344401d10524111819800e940642c18403540d000020720190046c4a03003c2e00d0704c9088000000c0c04064101c0f60981c20025194244021940e01d0044d440182103a90894a000301074010030482c031803a00040b0034500c540c0c181030429003081120107032903000c0301c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 349614181 1250 349612931 349612957
    0x507051b030a0224030a0e2b181205012712140c070806060f01140a03050c040305120301180507090b1b06190b010801061d060f0c010b0406050315010902 67
    0x6404c0c04a0118200540c429082c000c004610010104001803400455402480c054030558680300e040a0481003c0b800e100003a1030700d100010400806c400fa5080286c01013100d0b200449500c0060260540000500c0d25003102c8501c030546c80010100354400d490303080203010002410b0b41c000c10b03510030303003069000118075007100d440c06800281280c6000007590025196806c03c20030000c00d0700d00f407084801c12502c00e09044c1030078080f411201440e07204043c00e0308241551040810302d101c3c0c204040d10041e661200031540780d9030b1410385050710303908240308240010344d081c2040b0b030760b0300b0450007054001d03c1151518246c060510341010b205410181c860340c00c40040c860305400c3c50b081000384500800c0c030304140e40b40f06451188c09005842000c6016030502040d24010803c103030303000a4041c4c18500380c005145041802a0028071030b446480d64844004901052a03104480706610a2040c00743c22107080010075600c3c3c080c151160038140b620030034410008010031107030350b0a800901042411302 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 349615431 1250 349614181 349614229
    0x608040807031407050a0302060115080c03070c081216031812020c03070906050a0e0103051b01120203010303031a2d0a081903020f0102040e0105040b0a050406060507051b030a02 78
    0x21070f856290b0030a40b4280c885510500c000340a064040c8400c0e405002c145200303103242000048003808540f000342420315844400000101940d201d010144440d507449407011f651510702d1502e80c3c0c000b04040e1030f1030f016041c03030418000d4958000e21079028000000030410414181903100c1c0c2c00c201c081c00c07540350150701070680b08038159581800040040c1c2142d080000d5007038200000d1100310700c402c2d00003001e102800001071000c98800126106030b0341d03c80300b00c3c060399513008004803070720760315a142e40e48810300100002c01055090b4000441d65018020703008800034590003044096180007046403e0000c44400c40c071400281100314141184024241c0c0b40e00030380d24803080d450100c5080b20058603000004103032040642c10300c15980341c00905002503080c03d04194036001040700620a4611076a520440c0d11841d485030317105200101401841003141c1552042c1c090040d600558045406001d80803030780c540b07890361899501181d0000b9000b0300c40c034511395080c0001c0b1480014030020032000b00e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 349616681 1250 349615431 349615457
    0x16060b15040b0408010e011112040809060417010c020a110d0c1809140d090b0a120507030608010e01020309030409090c0e04080a030e06090d03020a170a0b0f030601060804080703 78
    0xc80d0080c001010200003560381d55140100d0355007100d4040c2d01d80140e41c0d05252040c40191010001e80f000d2400001d1410511384541c580300c0382c540305000700300c1d820240c046000500d1200060214802118950003400302d400340c800101c0e100c00701c002004101000d40000049a800c0c16680c600c039091080d0040c8042d981c44603907605189404e02c2440301c1181d22440d801d000c100c0a4542d240418151070028000d0306500c400150100000d8007900407000c0780460101c109600c60030301d44041c3c0c3c0001608004600300480d00a01410103030080400c250300b080914036a482e0140300300c030f1196200303d028505240c1080840805024051000d071032140c040c150210f21898501d0505004520422440c1c0e030720303440e003040502078074191014142030b074001038100851000007284010031000c581c40d0040c0d55072030051098a94101c224070413034002b15148108041d180a607403114502103021201d8090102c3c0240425a403098240164000609000082000180380401030800ca600c241803c002001103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 349617931 1250 349616681 349616719
    0xb1003060603060b010f0c1101030b0d0f0b04031112030612030c0318130b010c0209041506080a0506010b0c07060c0303140a1415010f08040c0506070305120a0216060b 73
    0x500c0d0003e94105030340703d05440707040d0780041c8540982441402c0810921070f142e101e1307462814002481d00e0505407501042401c5a4640d0114541e032030b40018860001031140c14140111401103404501041040e014100c0c0080006252071021940002d000d203196546001d100d40c03982580680d40c460720046c020450268007e00280c009503903841c203c9800040b8220811141c41142c01c202c07480343c0c1c039041c142815640c0c030a070122105901070364010890b807a6032400610540006014841151400c0c0c1c0c0801c0d103080108080024030301403401c0b00c4e89640c8a0300c00c0b8109101d050038078800769020840c00c1105a01454858205902034240042c480c0701100041e02030340412110700b4082c60b0350b202200602d201040000c0d4000813107540d641c1d001c010750070001e8259080c40c0100c0081c040340400140401c04050355000c06840b02421640e262003040c980542107820459822100e084510005a91035410b842035500840c545109442444102c1c1c40c0c03400100407000358030340c000041d0030014624100d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 349619181 1250 349617931 349617941
    0x30705011d010507050a0801350d0e0910060c060f0606120f1506030b1c030822030210020a020312040c0501030e1908030c04030f06020904110a020a0b100306 69
    0x1c94004101c80c5600c0c40055030071100700818241c180403051108004e0141e0080100d0305451020850010040044d00c1010501c420203c487c0d0728241070104049a4000220304903400301144e45903400c400445a041081c0312000b00c0304440858500e4030100314151146006e841654091003000408001c5044140280c800c140c000e00c012610310072503995206007a20032000d4a003400e810800024940c0b1600740d031081014403514007015100c0d660741040b6501d41c0c68192000c04040e125030f116004918014240d44400c81d5501803414071074000c80410441080081032441c0c1c103a018116190010703640b28006d42041000340704500c4188204500d4500401025000c2c0b40a4420b803081c051a0200041c25111524101078041c1c002c0c904803003603d40d40307283c40c0c00d026601040c055100d0340d401408840900940c0d102030500b805684c0101d09110007680140800700d003d850070301629103540c10604080c0300e103035600c20044e484070f4407650100b60940a0250080080028140107544e680c5800056078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 349620431 1250 349619181 349619201
    0x2090c090114161106070c0b0d11030f01031403030907090f0603020d0b090d05040b07140111120f01050d0b190b10031b0201050c070b0a20090a05040b060406030e03070501 75
    0x740007a0254402c3c001c0340344c000750f1112811a621860503e42e56901941c1e040307184074809043c840400c1c40c2d402510f080d08a60f004241040189441e0315100d139035110f001e0700078130041c4c0780101034500207903140401000316845800c200c00201000703484c11703c90720b0081452015101c0020741d5030b480880182d540c0e002c500011f45c06128807140e00d041c40e4031203605111020404005010080200b000106103104c2911515030f040902c04d010318003000c141602400c80c0089941a82000151541e084554807110034000d1542010380300250783c80358103001001003620000381501d441c103c0010b5440700c0420804081c07803081500070a2250304403001c10000100d00313840c100443c1d00d43c0103100d00d502480101c0d0364004c4403880240658100021040e60505c540c0b0070241c1541a00000500c0a10a0360040400d0724488009581180484540e810311b84e04444004d5105408103000041d4625103401031840c1110014a143c0c6414900308050f8020403810a010205000505c59400460420b214100c121 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 349621681 1250 349620431 349620457
    0x105040e070c0f141c0c1b08061003030e010212030c131502030d0f1401060f030e060a060518060a23060c060405060709080601030803090a060e030408010c030902090c090114 76
    0x1c10004400c11700b4480084101607100f14403012a2030700650019401300c145811240d590700c01002002c09651108a5400031300c41807080005101c1c9008001d03e06200f103034026500c2880c03242a51004980710302200da02c03032414145c10b20120ba030b10076110000340f5041d090030300391405d801e540b400c0342210624144403500c09070300003080380e00354901d050050300006c0b4074405081018290441a00f9641c11041c018141008290084015101e0180d4401d095400c00c40c000c0340e070f25182821a010141c140c60007841d02502100c0b000600502c0807039410350103424000c108100c4942403041038181807901994016a06c01d52461802880e1070f204014080029810b000e4101803a003414413504e000c1d8003030808020040104410002950041003031030640340c1c80041c9651366181c102400d880d03e406010b01030441c0d40340002000701c2c2c000001c010030413228030400034040d400259070103904540202c07070f010f50014034100019034050302c81c400800001c00141400c40000325012000b2011360080710b960070300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 349622931 1250 349621681 349621703
    0x8091b06071a180f06040f0317010b0a0f08090604083414190204020a0e09071d060702061207090e0a020a0201051312080712090803011a04050105040e070c0f 69
    0x2c3c45080300200c040a041800400988140841d165a2140700030006440e42c0040040d0504061003500c103401c428001940d02202941c541d200c405440d4403203115038010030044850803903c1c50258010303910502280026004980e41d540f80c088540c2e2012031190900004d400300e0480c002d14080079004c030460b10a0445129880b02d00c7c00080240321207081400d40c1e440010750310740d81c640c20b038500c0000f90382c1581d000da161000d448043d60303d031004800243d40000c42408009029603c400100f002d1000d4150b04801c1d00d100c4024420b0511a5000c0a500280200204007094031402245e642104540c501110368994844058400c400143c81d82540d40b0740002e00d41803084e03824041c081e00542c4160350520b03600c05581e00d4503c641e51441903c02400300703036400104264000c0084159540c0c20941c14405c0241c680380c41a078a03071090040b01c036003001c1103c10a454031004016603003522810385a1a15140c2040106440080001c20312410080c00310071a400048000c1251003243d8402d10300d80381 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 349624181 1250 349622931 349622941
    0x30504090e06180712110406030204020a020c030c040c0504031b050d1b08030405010806090406060803031521060f0901061802031909110402070201030e15100608091b06071a 76
    0x51005020700483e4480d4440b60082c01029051345090720f080768003600c0c80c00036220741c60201e00940242c0d40040c0d4807034408940303502d034141c0200e0001c0000104406070b4103441d201c8810041290065506540043d07018482400090012184d198103002e4410340800c0312a81c2e8030019408080d84101200d11800c60031700002c524000203082000f50103a4000b5600b8076007081c1c0020b10180001303103094407405190010509108190780001d000d007402e402aa036482c0390151940940d200b01c1c11500c1d0140b0680020319a02203030400c064045410400007920b1551a0059035510141c03010700380c01c1c00783d540c44100191540400c003802401903c2910302580fa0700c0c000c10300c0380d8100c0c0351900c3c906445040034040300004501100354640ca02044400680343d400c6800101d0050200d00408076070351007a160800302480c4074100c0c080c82103e1750204243c00b01d032038190172aa807080c20354032880540d02c035000f02d8032204907000c040110410040d01c0c5a003042e41580f506904840c5410002d91100c0c00841801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 349625431 1250 349624181 349624201
    0x50406080901020a050a0e120a081b06040809010c1a0f0f09010203130204150302090103380114010c080a0305070807030e031c1407090e061813030504090e06 69
    0x941d0101048008608010710042d02421501ca00c0c0500da08000003082c03400300303540d90b64541103c1d003020101110786e141894940400e5590021904044d0750948400600c0300180024070a4852a4070180d098204034500c40151881020644216114843e0345040b00200602907420352140240ca0350905441c10b090380031a11964000c0e01c10000c0364010820000e519000908410000b5410360b800901847e1360540a80c00980c207802c003c0d4410300c40b03800001881071072003804020584030401460308605a4034803102c2c0b44940c4969144095000c00100b09062403a0425131140106040403801026541c1d94500e1a42c0000d44401c0880d40d1041400380203035200201c0c030360004450400300200360440440995a0043c10300414143c8414801e4081135140340d0002c031243e140c1402c2c03c410f98148600e000d0009003141c01200210f016440000d0040d20300880c4000090200d4008008030344c0b05d092900c40d4070600e21109409000003080300041c0c04103948181c0341030440f9400a00600d080085282c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 349626681 1250 349625431 349625447
    0x221030a031509051e09031606020c16051c0c0e04120e0616061a030f07032006070b060d0b1305061305191b0b070209090601060f120b10050406 63
    0x40c843e482c903180402003146603141c2c101058180000728144681d0b02d06a1707003440e5104440180300c43c0c100c5540c0c00e8040101c15005401c4400c402c0098815110f403031040345c2558a080e208590344030524103040310441007400714408035980203030180801d40f601c4d02490310910f001a642250b01014240f000d1003d113602120350024820100e98182c81d0604443d600e903044a6001030240041d641d50001101c0d50495071041c100204014080d00c0b002c13005a1030a070b031a42401e06c41521040505808150441100e101010071054001e11003070400711183c861204120700242415003004c25069118089110b1210903885141c42e4030b403c0c5070750026440c0c624184400684a0f148a089000e0140c00107800850701d0a803070174503200e501c610b400141c1082a4102502e45032034019490103900413031100e0644c00146880d0b4020340704803503152105000310b50b407440248100000100301e5000110514800c044101490881003400b0a07070714620310005264000041420011500008041009a4001d405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 349627931 1250 349626681 349626689
    0x603040c0914010e160306080a060507020f070f061b0c031121030412020d0602030f070e0117010501051b0313080f1b0f01200c0a05030a0f0221030a0315 67
    0x2d0001d443d450302c03d0507945140041c00c40c0e43c000101224120816100740d009500a01d100421600710480e0b0341059001410b003a14a0001800303800daa00c00140300010341c00085840e0349413400021854080220352154100c8002d0800004e0300d01010003103055408400040c5004840030722558402d1010080c80b000c6a901065074014180010041e4101c0881941d08950480d14540e00100d903034800552550700e8800300426540c404003d001d100c548001d4603611a101e11f40791075100b440300700019105c5240e051090240010280014005035101e480a4041420a071a1000212369055042800e5400c001c900b42066415694200904102001a00c08644403074003d000d00100c605407090030841c10b41d02c03650244812499020b01a48514040004040c0c290b0782195803542c2c016059803103048030075202e0b200300b030040c20228951401249254030180d0107440803292042650a2012b46007408030b148055000420216017a40400c0c00100302c01e5240307503000203020045c403900d64a0103c0ea500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 349629181 1250 349627931 349627961
    0xf08010510090504050a020705060411181303141b06062806080c0714010e0d02010e0312060402041502030d05010f2d09060f03020315070c030f0306050603040c09 71
    0x6010800310b4005112009580c025100031800f44d40315410030010303105002e0024014401c19003000148070021a10010b04002180ca0b41480d046004207251401406d8941300c2d040c0071001c03890710009007d607017002201b07981d040300c1d5420040e003a4040c0d818800e69040c0410303207402c2202000303250701c0c0940c50741d0b100400c1100b07842e9100c2c202e52088140c1e02e41034020300c024081e903100410304520032201620705040d80610480442c03504040c043c1d01038038202294102c148a02403503202c9050040c028942482203520085003484e03010036241151a80c043c00303107504154200404074070340d684404408840d0032640c00840c0e5441000411008840c016408a44c2c04004581d041c021f01c14540381e0458140c2c244503403003042d0100744010000000240d4002070029150240010b0f44c1c1200030707686801c40e4022000c1d90b140f045038282001600d1400c84002c80061140c40901d40017034050300e001c010901c100c0c41c000440540f501c01103109d5a00c00d0310165605048103604220307c1030b503802683c8020300c10355 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 349630431 1250 349629181 349629199
    0x190f0609090504080702010c03090513020d05240d030e03100213120c060c081201170d02010e150c04081005040606090c1202160c120b06010207080703080d0b0405070f080105 76
    0x1c0c035081c01c0e600405d48000e0411901070802001c4c5880340000c1800343c500100305460f0b50a5010414000f0360040103410841400d0200003500e4074950326581181c402a2011840c42c80c0c9120308000755061000004c03018841c0c5140000001e0314200300c03514400100304001aa2540320611352502140c40d170748004042d074070501c8440000303174a24140a0446482d800e15103100710040c030349240030740905038088881103510400004c900710f00040003d6040722010a540c60308042180482c240e0701e6908419103d9401307400c00415491102030307542d41c00303040c3c0c00742c040c02c0640720200c01d030501d61070b070140240b050303120400c0c4001d04c50188118030050140714410401000c0d001805003800c0d520100c2854100d034082125445140840b402c224420380c0244441541c0752141c5c1e8011044240f804140c4940c1703c0a0002181c7c1e5000107030000907501110018240d41e895030b07441d0201c0303034021284806610313141d400540342d6448a0194038021101c9441e081960410500018100d030016440144201c6640c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 349631681 1250 349630431 349630433
    0x903171305150d0216080a080604060b130b0a170403021501090e1c09090e03070b0a0c08150d060c121514130e0d050408060a0b0618190f0609090504 65
    0x10204a54280e03c1e1148090703120301c4010354409070240381000107051b05000180d03982c0141e503c0003d070741c8540412a01000402d403500e4404031ba078018428080d0308811825400d0040e600c0d1000642900c07546032405c1d8900129820040101d5241075404402581c450201a02c00c45072805000d0301400d444c0780c007040520801d03000284c0c0d54982c00184c42d1003556a02404684501c100d002034054604008c040c88100da80f040403c0d660b41c81800155055541e01c00070072184455030286a100340c80700c0d55034a4a070349070107451800c05580a6100c55200c0881010390000900c0c030f0050003c005116114441805192101007040d00c034000e649440410800d0720900c451400681203041e01c100554218030800d1140312502c00410b05180a1129071240c01e4041400b568000001d0060381e1104003034135665214203c080d006c0c0d40a18a0341c0381d210b80c09014a01d102c2200b85c034041c102070001030941d6103880c0110f82444481e00140c1203105005070381082031103000d4208030850004c0c104c0c030504110501e01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 349632931 1250 349631681 349631719
    0x60415030308071419020105130c0e0c090a060e030c0d0b13020d150c020708030f070f150501080105091e0c0108100f060f030f0c17070903171305 64
    0x900e0000800340480c0801241d0a1403184400c6074443c8213034441c0710b541c0c6941c035180003960882904800010f600740300009201009540c01d10b6051680451000306031828000802c0b0144002880c11300e4419043c081000d040d600c100d520710043c64940ca90400300d0282c1c07000d00d800c000c500254140a5081641000c00207140c3d00005540f00782600c14400c00f400441c1300107810320b1a0110090000c440e000c14802000c4103982c48501071b414540c007105c20440d5100c41090f2a80684500b4066881041c00030b500403400c64000105035034429801102c42c038408003e020100da44c03e0300b1290b0680e56982c100018204200902e00341d0f030003c509002024030021080aa40d0f40c806103500303041208510100c1c54a10001d00b000f8040c21032641c030103078180d0b2108402002d00b0011502080001d003005000b1a804055100c2c103942c14800707030350700038008540a102c2a80c80001414840400558110001c003240c411103000f4044400301416a07641c019890484922100e0303500b120348508034603000d0500d0001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 349634181 1250 349632931 349632971
    0x40b03060c0a03020c010204030b011e030302121804020c1608030c030301050d02030106050d0b0403080f0c03060114040b211005210c10020d021203100608060f060f120604 75
    0x4100050300b0390b100c0002c0b0007100a80079155038400d0329030012501004000001d412981607904111000c0c1c410004500d01c110f0b40d50a5100143c050b1b0020742c0074040c032000c100c004100907202c43c514000d01c0c010300390119080340c1c005c0d5031490b903642002401240940c1400d21240091292100841c2094044200c042c0c5034481803003118420012100508110b4074207401c150010312b4018100a00c030240c60038005000801120105e001504000c00148400d0610300014000ca52400d540350440e80c440005568070600c441c4076003020746082c0030004004061000500c0742840ba0000600c180c0840000351451001c080c0650014a0442c0801d0000d40c6812000e0a15003040c0820300c001440054015414501014003658000d410f0068600754290009080ca100742010750031140c81f103121140400041c0016100e40c0a209640e102c104041031041c50700c142c2047d0000d0503001407001080002c0c82e1031b400020071802c00000403a100780400f6045503415404403041d10240b0200300b6407c1d81d41001d00e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 349635431 1250 349634181 349634191
    0x90f050402031b03311a130c121104020a02120f07230f01090c150e090103061e05010605072003100501082b030c111203010e06040b0306 60
    0x181c1e0120000f44481280301e412090f110f444611540d80341000e540c0b00035013052441081c5120380060100c44101003034000c0a0340c617540c11200c10070180c140359400711500017020b007504000d030419004842c0440d8100100c1001071010014099014419203004400e000150801d20300ca1031050107980e01c2190003040c3c610f003541604085907030768013074440252000d025403000549650891150f840d0810855031003010010b4598049808058061291130709030340119100621420414208201c6409407460743d4a2607011400d11f0035400d8012008501c4d020408d0b481940c80540741d101d034501d0f081e110000c110011032100030078000c03581400d40161151090190043c1141c4015605024182200d040c1c2050b51000074103807509403003482070480141500380181e14041c052407041e20741040003805200c40701d42020028004585000d2001c3e0014110b00e9400001c0c80f10f0f001c8013020640e0144101c400b200c013140f944640765410516a4032007040c00602c0e0314082c0e8944050000c0710380d000a03550341c2c06 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 349636681 1250 349635431 349635439
    0x22101081207050d050c150f1014180603010b1903020103060f2114010c08010812040303120c0908070306060e0708132406090905011103040327050a080d0e01090f05 72
    0x162000b62440c80c50f011240c1401c40e6440154406d0020001a0148c500d002d0002c02c0b01c007031030080c1c03120240c02c0e16800071804254010b903181403490041c4400d00650707a000f1401000020810703001008650b209200c100804045400a80e040c402c542e010300c2420068410490035610890170513a40c4210481408540780d888400176122400f001603910901d0b50a54142c402482805122074010788940000c5c0503100e40e80c00780481440390403001c0c5003500c0071a81c155454005100e2105000c2c4010100d441c601d500b0030070118004945041c0800081008600c10a00020a10b1906401b05400761002e480c41081103404414404034004000f06405040d0704003041000040750590344c51000e00f41c0c20481c01c8024280103002415000341d901c1807203801d0041f00240540744840048034a54401145c3c01408034540000d2411010321201010141d104000568614030b40c0700d0b4002040d40d400ba17441402540c2c1b0808940d140d0b680c2c0049030712200d807030070708240480074240100540b01c1d007482c0c0242c1d409 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 349637931 1250 349636681 349636687
    0x3020312030901150b1308031c020904151d0a0603020f0120010501081b06090d1407050301090609020103180c06030e0c04060321141c022101081207050d05 68
    0x10100c029445242c000c204c4e200381441c0183e5442c50700c5079542080a40400300c40d4940c50002c0c02000210445048040e0a40c071409a8088425090000d40001148279002540c5000051105140401100c050301c0240300300644241003840004100c01c000303001040c03040c01e2180402c016212402c1c41001e2410900302411104512540c00803030f540c0410201d0119802c2c81c3c00052005030210f6100c580b0381c03041c8903024407600da078018414244030301406c00750804410b23031000e004507001400c07924480300e054060700c0c0110390300c0c40000e0035104031030b40c00d40301c042d603c02060b011580c040c0b00d032004d9131412144510042045859a60300c24800344260402c2c5900c0e05e40f42074500a00b0f121136460b9005c014001c001940d100d06182d014480d0442c0b501f88a10180282045064051102c0422006113081700f00e1600e141c038410058030903103001e40c0e2841d0700c0c3c090048a050711400300d80e402107140328043d06140b940c5441b00680c0b031704480c0150310442c2c42041007964080f5001052502030b0804600303226903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 349639181 1250 349637931 349637941
    0x3090602070c060509150c0a0206161221091203020a0c0807060608010c08091009031202071103121303020f18010603020c0120070f0204150b0309010f060302031203 72
    0x4080d1180c0d0034024540148032001081c03c6400030080d00204c5416519500041081090003150b40715100031551140c1c0020083c4005103040401881d03400340c0500403524a006a554032002c40301c400c09200e0204506556608007808514907240621200c400248840181511081804499042040d0425400041450042d4000c0d08096001548031071240c0d954441c1d820040c00800701401015a20350078040050f802ea80316040e00d90099031030001601d0600a000700d5030004190303101045003405400380b0460300c0340c42c1034406000b445000301c007035071a03035480001054101031030000314001218080c06903005d1400412003401c19203030b05841d03a41c0e00300030b0300c030004003402c250b42883c1c0da4010411700003041d140e9158024141449515000b072060052441401b03240c1001c0d542c480d250300e201809143c000c14400400288040d0002c1c00020300c0a412410001401103290020030a041001042c0a0622030901c1021412034610000700b00d850700311750010340c0742c13a880c0c05025080e03200800868 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 349640287 1106 349639181 349639193
    0x3020c0a1e0b07060605040f0f0b01051305131103090a061a010c0b070e0a080a1a040b0601120219030504032607050a110d0314130c060309 61
    0x14644500b400c604080c550440070059420300d4540f0030004060b00c451240c06120441c403040480e40f000c1c605030000c141e070406001c0c0750412400700702d03034041c400002c41c50006641089800c40d412380ea41031001d034040c00c070079088120b48035000010300805420000798100840c0c86030006124195030020803805140b031a0340d220303010a007440c280200149200074429440b0314203007001550800c802d400300e04c3da0707442a00301501c141d1201071500280700705881110884038444210140c0c524159071200d80c2244045e24040c14000301c00e100f40d40c45042e68065400e02e8071070342d400104040500300e004000c0c103000d56064000c40c114401c1c180040e404c21006109940e403101c02a119925501e200b2515030348100441010018103003481100d00000740b044410000c00d940c3c010070f030000c0640e071030b10039520040d148952079520115032600013520003801c441110810f0800040c5207130030741464 = true := by decide +kernel

theorem cover : BRFrame.Cov 349460431 349640287 := by
  have h0 := BRFrame.cov_init 349460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 349460431 ≤ n) (h2 : n < 349640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
