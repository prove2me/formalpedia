-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:25:19.132209+00:00
-- url     : https://prove2.me/submissions/dd79e3c7-bea8-4caa-8ca3-3fae0bd41dbf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 727517985 ≤ n < 727697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 727519235 1250 727517985 727518007
    0x9032a060703051c0c14090409051603061401030201090605030a0e03031e131707050c090a0b04051e011203021216051b090f2205160e010b160206 64
    0x10103065000740d035a181c031440c050340c036000200c4c0c102d09921000f9161a00584899800c2007070100b1003044044615191840440403c014142041d8000d1160003841400c00c0a0441200000150b0b4000c504c1002001c1039828646441903083c0030103800320301c80b5201004941e110744020f40d0701c80000c41000c03481d400340004851660f002564111044021070307900c92040075150002a80c08284a1000601060a622040b8600b2034180c00d54456a500050010074440f00300725003011100040d000d1401860070384071030402411542ca080e84104c1c00c000115208102040300c40100c00440d54074620076901e000c004540300310103201c0850650146000d814260103401002e400d0843d8074143c1402d45500900c1c100d8103000c128000415009452101c0800a0300c0e551166544000c0300c400910300303520b91040f071001c14400d4040488040d0030004840c02000404124404840300340d011300f01646840340e120f504a0b8400f40661412010117102402c001411013601810003400034220703d15100c001d0301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 727520485 1250 727519235 727519237
    0x90d050709060501110304150305041a070806130c2a08161106040b1c1b020f0601060f020c0f0f0604140a0509160f0e100806040e0309032a06 62
    0x44407558080e0b4500c81000780356000384083c126045c40038003451500382010001080c041d01064000105660f480018040041d2118012018000241300212510f000c0340010b2507180c0031586030307000e495030810040300060140101d01300074101e03846602885220703440c462041001c0740c04440c44480003102140100b020f510040640f501100072808018242d814046000300031030407424054241000100205100307a800d40b007201c0390440c40812811b440718a13007000741000740065104a0b4207100c095984a40000e80d48507211180800d80700203a0ba0350103340c40944c10050308070056040b5540342512454008410349540303000610403d415254040030030a181c019400082049001c03c001e0700c29460030b500400c00400b0100c844600700e15003128069031740c41854950b1002d100c0050394240c1d0390b501509008100020107054035403112001c41c0006c103c004140c0e440f602440c0342c506400c101c400003104503011085e014005107080b0604501c2ca800081400b00c080d800907a0003801085182e0b1000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 727521735 1250 727520485 727520489
    0x302012003010503010c021f0e0c1002030702100905150309151305120a090e0603010608031c05010f150f09090f050a0c0810060e031002130303021c080c090d0507 71
    0x2811036522981403105160840e000580184250741c44541050500404120b015403203e141c20004906600b00f036101618102004080c1c552116151008004299000018100c214000c45010030010040300c0301344c03144841e501030207410000201e055900d807080d031001581c0000c401805c4688a03040c03100c0074445020242d410680074413092480c0003d01c0740400a08003060b5200000c1131a1035003450f000b40200c4020710642c100749150303500103104d42e0340c20360010b80240021000c0c2d80e5260003600703d190016a0035032096506038036210001c40c002100c1000e800942d0300043c0c0190f000b04c1e03070250580e10394540c601c41c01c0c20400400b6010800e4400e50291490002c0e45801c0480c2c6818140c2100041d00c02c1d03044010100300e0b008040000891012024008840a500f00034a2000994001c2030400c0c0900e00d854003a1400018901e481d0701444120f9001c0324020f6099500300212072140c1940303904d541e41240d000400d881c01040503686514000c0c505039030020800c8005844c1039856a04090240e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 727522985 1250 727521735 727521791
    0xc050109080301060906090609030212011503060b031204081213080a0f0c0503010507091712070803010302010813030503150f041b0801050613120609141b18040f030201 74
    0xb00040001580100907400944140d0421150303503428103000510949032071001a2103103401548a405443c401c4d400502a5a00c00c520075518580380d0810002030100048501d000788903460004140402100030f0346c007514442c4001d80358400307a0000451417a00006408a01d004900300c000690600070400074106d0b92045c0c1c00d03e240d54110342892240f01c0c079280e1285002ea4144402c001111707038800c0d01c800554190b4000b244541d100035407040d00d4860750b105501815400068490244425500a18100d9100342d852119690358031520000d00034803c3c00080114201f40003250300042d06a40480241201030021640c44003c00300040a0b20298081c001404032005030340030509902605050242c0005c3d68158540700b805032070000c2a801504c42d07042c2001c1d0011740340c02080040c0c1c100c4841c154002a9040c100041c00b5110b075200c6d55884c0046288050b03685640005081105454082c0c900307850070030006586e0354480740501c602010084085544c5c40300038861403404d4010481c440a00c0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 727524235 1250 727522985 727522987
    0xe0915030c03031b070f03020d0f060f0216060507020a08030a1a2e11120f091f0315030c0b031f090b12070b161106040e0a180809100c05010908 63
    0x140c4e03030685003000011707049680d0b02c445112050000d611a4865200c509070302200c515040025030910304002c10340280030140080c00010042205142480c0d210381050040d0310812184d29002020381e5142007441004007801d2050001803501005540100e04c04410004441246140d4000158000c00c6403000515003181840502070340340b03400c2c0710342c040d00035040c00c003108422580c940f0150703111400134030450748500c0003484c02c0055051030152000d200000e024185032508559190410001516080303001a1030a186209102054401c0700f044981024954821905011401310564401000001041c10307088004a540c0d00b00d00030000203104010001402d080040d0070421030a2580c0b0040507103500c56442403101402440c1142e80384925080d100e5034102c1140340c440707040b040c00c800da0740d440700d40800c00240041d40c51040611604d0303403e008000c031030004030400035814154100078060080c1840144032038144800841c0000c00d480c20008007220656840c1d5003500c80c003606c110382c1020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 727525485 1250 727524235 727524277
    0x3040608011d04050318010c12090e090304140d030302070b04050309030705090610032c100506060712030b0103063206031315110a02070609060e0915030c0303 70
    0x1254142c03a491280150109081e41000c0d200c560350b070300501c21035031070349181c020b082c0c0c1e0940e0080c00c180814562200800140c820600b030040c0c4a000e4910400e8250380c81c3d2300018880c25000b104403002e84a241c880000c2a03c1241c083c44048203020100300c003456802c004140c04600319400c9184601d104600641d0340764460805e160800c0116403003d4080c01242c0b0901420340d44503090b0100340e4205c0c1c5800207011543c00d40700141c4a114400c0d8004843e1014984090305001082200d41811508414800754540d8818050240b20b4540040d0400c103080884505080c070a401030061100140740100d0704503103402050185415540e070204140c5101e0b004a50341703034403c0d40a003a040c0b5040303c0c603604615000511984800300d4440040540d810100100c16080c0268046a6500142c26038170703440300c6214201030340e2112203005000201d043c0c0703940051140d02c52180c010b45900e01400c0711003582c0700c0c21102d8407039001420000e42d04d400389103a2080e0f542c03010005440300c0c2c442990103c00d410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 727526735 1250 727525485 727525499
    0xb07141b0705030c2d010504030213150b0a0503041407090c020115050904020607322b0f031a100207030c0b1608031e131703151201020403050304060801 67
    0x58100041c0105c51401c2075481042c0c01031000419100402440d010741c40308071004986070300c80c079000250300807070003141260b0002c800d90011030480021044070201c04d4403003e0440c880d0246464190018200f040000c0c00a8440070390001c41a0080b022508540d458503041c40984407035101d8140140e5648071105403c0e101c4144c594001c14040e1950081410b103a004500a03210f501c43c0a007442c580780c25014030000c1400750845008074050351201d042102c08610b5a10f03403040d01c041249001c40d0418481100420040a84101640d902c032200c3d98203c0b020254060080d17000c0c039036880c801c03030b075446506600c499001c19140c8460f0707030142601500b076240c284d1208400d80c0000000e42d1042c0291040480588841921103802c01d8800d9240e9a0700c44045440c40300f0000211200701c440720502c51080c2c00140090810313489034a1040c04800c02d000280414041220701010996400b00c40750080e0400d0001a0007030240e40340050703d03043d11780d02c07401c1c5950b004e0340c0404002905040104094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 727527985 1250 727526735 727526743
    0x10030b0406081212130f14030702040207080a170712090f02041409100204061211091906031404020a1403160b190c051216170c190b07141b070503 64
    0x80c109041800380b4440d51120510692410802071103090369580c107421f107200c100700741d6a03003560092041d03507911461b01c2d017a0405c1d0816502a0003007550f281c4141c60007058240c0c0a4401e90701a074a090a034044240320802a180c07900056403181c042c51252005a140e500813428a5000d4000c2c03040b040c2030940c2514035001021000400300b0740306000902c00e003070b4400d91005880d441e903a00824243c4108503030b03000c11320600580b9030384500b1000320090300740344c0705807854201c0e400b68030100000c10050360301d060040021603000b98400c41c0c501c0c050210000c0840d21103c0d88501508507444104004000c9420000d90382050610b03400c0461803408961010040000e50145890310313850300011644c0d150b6a0b10465405880d070385070041003200f0b408002a080b04010f80d000fa00c580905c07440c1d02d2580095074400d28007007034180103228402d0301c0a403840b5088011180c1c085400c810075980d92801311444066500c01c00c40f007040804c0500008505c158000448501c000082d00740f1519100402d0700d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 727529235 1250 727527985 727527991
    0xf04030b0a0209100f021b042301080c04020c0703061107020613080c040207120c170d1416080c03060607021807110105100314100c050c070605030610030b0406081212 73
    0x2c2000e1425900c01140c0d010070b0101c0c412241080c03030b01c1c0e2149047c0005000e0b046000031110980c40d08030350b10300030b0548492103d0484550006030fa01c4a40c5100900050380301c1c4845840c040d5106c40c400304001045517210582d500b07014240c0c0c070300381041c5500042241d07200300100c10308100740d080c0070301501000340302405503060f0440d811840e0540594820343c01c0b140300c0407140c05111188052005229009041c1301581c5070104645981b42c461054001c01040c0940c4a0119501d031100041e10302e0f5603040b10034034244a0743d1110304c0f0607034442d20364079035540c401044d0f42e0f00700400f44034100058803000c804603e0903284134501e090900c3e190344001c04000c595042c0742101e80c10141400310405802003003000350717a00030304c00c114203415495507a80742c4040c19507040d048a250080d0200c1b204d50110280c10018664030540c0d80c0c290b91650125a039000680705580d000700103086015105000380d10200341e10b5009000814920f54641d051400e05000e01c0c00c0500500000a402c0440d1000d203d0050f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 727530485 1250 727529235 727529237
    0x30e0714180906180a0f060e120d0e0616050f03101a0406110106051f171618050a0b0318071410020a1e231e150604020f04030b0a020910 60
    0x105c0070304680310310340c581d03000c220003601e15a5905021206c0f540103102046d106410340c1c502d1981c3e8085919124014641e10b8084030b580d0161101080b0b0806028900e1300c5540415941c0c182410604040c212190340041d003582c20300f150881c00040d01402414040004c5c409600d50151038a2130078000cd03002460701c144200035645408002d00403507495003124800702c1145001c81d2510316034440240d69014581095000c01101a820401c080b01810480c40009011340d490700d8001c9180340d19200400d005005072540f014051000b40301d10600100a10b500401619850b81044980c8150504004082d003210794101030200c14450307a4241060f00e1060001702c1d2000301840c07071550715000c655000380c0300c410a6001d00219000d007488507126140780e002880110f100340d420b1802c003a49a6441e18080c051000001c809003d0000d51000304502c40050b054100c040e0080d610101004025440715070300b040c1e45902804040003007040326a9280c450b241c100c00060341c039a0b4001c04c01c44048103040e0310303038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 727531735 1250 727530485 727530493
    0x120809040b060c070e070e040515030f060732030907030b1501050405060a051909180e1b0613030b01030204050a110703180b0f0a030c030e071418090618 67
    0x103050100011081d0444105c00e0300d50041d515060000c030b8442c0c20f0312000e207500c58204803c1c408051440c03600340c41241d00850403944141038007118541c07112000c4694001191410107400405100d07641c2910f05080301220b0b5148402c1c0c0c694403005150025907801072203034810304041c01046070061010742c020240b450101034249525000078141e200300e014041c007800c00460610310071400340c0140c0380300041c501e420008442d10420b0080c2510251321440080c10502c070004900300540c0c2c07280b116025071503030141c808030102042c00601214000c1e03a036a0098400c0202c4c0500022187c005000756200e00f13102102c1e0752441c0104130560700c000d4844c9000c1807900012508c4c21f13040c101240e43c5c00b5414180440d00303002d80381500e00f00c40007990090181c50740000307100001e600d6200c001c1190a10a0701c00300481c48104800724111080c0c0c80c06c042940d03000c030609000718140c48000448501c1c008061030301c0c8a01c0004510300e1000d042ea409802c0754802d5061089031091192a903e100030200020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 727532985 1250 727531735 727531747
    0x504020c0a02040f02090d12140a0c030c15050901091704140d060f05040f020111120301120c08030a0201090203100513060e0f06071805010e2107120809040b06 70
    0x4603140e48410200038400c664030803030013228000c030750150303101c05030700401c0c000e8100d4403401c00c14402c1d91030700500c2e800144c004000707042c4844402c087c1da00303d0440e5a655090690160340c155610075940d0010707600800000380301c00305803005e03005071442031110700004608550176240215020700c810305c0c010240c400c284024080b581c4544c0c85403403c01001c844e010014200d5081080040c82c14039510502c660170142001309004500c0c0c1c0d4046114400e0703982c01003011032140c440c0e407528490860080706a01c2000100100c0801e01c0e001ca0103035000b03849045580c0c1d40c402304140356601c62080540541d444080b240250325040c49109842c1c544014180000c0c9810001c0c050000780030303280200b189a0b296010300c610301d030402401d40040c000c00115a20b40c02c16880c05400c240c0d0000c0c070340000c203813650030200f555407040001004400000e42444101180000807048900c44141c591103103114906001900c205c61408800c4110b0140c9104ea540300c074580d09100940314081007140c0280c00030420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 727534235 1250 727532985 727533007
    0xc0a0b1e090604080709020405010e040e1c020c0909060a050106360509041104150302030604020f0f030d05070302151905070302090d05030417010c08070f05121807050402 75
    0x4040c00c5080e03a29907549408040014002c0e0042d0380141000e4840d194011613889100e074000d1044c1d6400341c94140301030035003004010039640d8910031030f2041d801910750318400c1404115080001e000030300540302605800333004100d6030b00080b1107410481c0e02c60360602c101d001580c450a030143c60949401c204081564804541c45050f08400c80841011043c2c407592140c80d07070094501411000b4040300440c1050b050108180b52011107041c400e07850300038582030741480e9060007000c89a010b4003404440d074507a003c004580187e13040715608070001605090066600b8000813801c4001500c4254480b452414000e00d044140d410000f000640d54090103000c0710310701c001c00320b03801b040702010540b6a02c03840110061300a0101445d0003010501c0c06200b0800084050019a20b203120302c1614103a2890000d400d0320130345a10031000c02c1100000c1a05c4501c50040e02c0e0300302d03c02d820481e2601c1c158a5082d4100d03601140e6280319500180d84800e00d580c800d00180340102004c4030258240481403203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 727535485 1250 727534235 727534267
    0x31e091802130b0f0424020f010b0a0302061b030f03090607020607080133031409010501050a290f030604050915012310020a170f0f0903011401080c0a0b 67
    0x42c1400420b004260813109549941c102d50141c16001c10703002101c0031074440c1c40f6100d450b56004601500444402154107803052240a8000800410003464039246800348242a8003004600300c1141c034600794002031100801c010300c003012052540f9075a034a880c000c840d050060207803140c3d00f150041001d0080c1c035580141d89505444c0070101800b15003141401030403501031a400894801141e156040e5003454240d0b0100740c00d542000700d14681d60707a41c1c0a665080315000d005440d882241c011040c81001c1c08000c110103e8101c1100d6100081075401036080590400f040c44098200008104441804c15002d0710341c0000c002002020041130344036144441c4501401468050720100c5410005035805081114401e04003411950410b07000f4600252a0400303001c1c151405500011400c0b0010450b008480c1d004070205005070408490094042459101000721581903484604584281f0000c5081c580201001c0d0002c10440c015142888042e000c15800940100018000b1038080f050403c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 727536735 1250 727535485 727535489
    0x3060405071b03020607140c060403030c27030c050102030a081906031a090114100909080d02210a020708030f07020703050304090209010801050604150c031e09180213 73
    0x1100460141d0720008120b0b0340015054807518955400a07100090503000310703055002d4003803039640c0c1d01110b0030500d5403105841080d503511480d0740010000b601091003580640d0000040749001d4244331070940c0180101a00b151011741c44030000c0c50200104a201c0355580c008100c00e001441c00c190318020003501510300205081d01d85444681c9690f0400180c2c1c3c0a0f5000d180d1280010055502c4119406c2c2e00000480b12a0055864056100051050f01250768401c2e003143c840ea40c102d60800c07800e0707409010382c0a422208000c06011482101e025800035050307004ca1400c0c2c005e9518001c0010703d8003507401406680d4031b036104018800201e400d05088990008011600f48013903114040104e10b0460f55910103082408040390224040585170010800d0644c00da0395440c0d80d90300c2d6001c11629105a1198041140408081694403401070001400d15402818181da410200359002c107201c42e109511340c0c000490b00703401840040561070702031410450000c411800c10105c0d100c50742c0855054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 727537985 1250 727536735 727536739
    0xc08090a020d23060a0c030905070612060b0c150109202a1605090115120b0a1706011212050715061d0a0915020d0f0504290402060306 59
    0x4088848240031004950b01000b0840d5840d00301c0240b07000d41d0f200c1d100c1d40265080c0501c5420440e4041e80c2c00c0c8a4056407003004d400a01030325a50349400819103003a11030308205025036803520000142c401256002d0019107100b50042c2c40000220350584a509505810103c0c1c020324040041441c000c9a089030305081800440f85907071aa2044c058415258507180700351021220200500c20500e00811117110003d0080d400f541d543d40c2354010000c00303010034050ecac1403401103142144a114403d10103204090111200050200004000314a00b80c3e0781d600150b030301004180e44003030746501c10001030340100380c0e982c07204d09290b815584000c0c180800e009480e041200108800061240d001002c682c3c590140070b041101a40c1c07110f04002005020351105c1241302004000b4884036000e00a4011041d80310341000b401200b000a001e0007500060368030304d00c0564510101c19030304524030400d030145004a52040900c00c0c1002d0400003c2404032103100144080c105003c010380310402600e070000c80c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 727539235 1250 727537985 727537999
    0x50313020102010b0303031003120309030c0201030b1216080712020607060203100902180901120312240b0c0712030e06030606250203060619030803090708120a030c08090a02 76
    0x200e0004074098800c0845096160200200340621324025215040460b0320a03541d0000320001800140c0c05c94102a901802203a00d500b4038800542c4a5408090034040041062204000720701c0b465103014045106559201c14180040c80103001c02c002003c004d2980c0d242c1c2e00c0316009150301141e428000c00000424550300440454494180e45260101910245800f152581c01d1002442c07120242c0c004501d020350014400031030883c50f1400000c2390150185c58203499000c1d80c0098500904012a0400c43c07103e4a00640c0d200c94240d0481400401e01040700548a00456902c01c1c00d000320ba6101045549044946400194000341510406d00e0f040304c00e59101ea8034003010580c07500c100d03a441001458194904401e0180c00203014034010300940480780325943d40014844082983c0400c2c40c0b0000c00d51008200190410008582c44240c000a8444041d60b85940e107140c20301803248000c03900c5000c03c958010991511901421100030314200340107041403031085440d0b01c440702c1d02034081c2c18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 727540485 1250 727539235 727539271
    0x72a02010516060e0607020304090b0609090f040c05060f0702090609040209040318171015080a02120c21100501180c0c12030204090b040e0607050310090c09030318060503 75
    0x2c1c603900414142d0040300945d001882c040500a40706c0c1d005000b400c1c11180707409a02c0440b070074608242c400300c1d100503102e1842a180c0074480c1c580804002c00c11074240051040100b400c1d15803c01920141c201e01d05100d448440b188100000d020005254500880140b401c1001690741c07400741c9500280c141c00c0c04032207496094407458101c82c1ca5040022200c00501401c2c400c0a00000c0291914440c04070030480841d6540f40d1703011100017031160083d258001907680c000741c9884102c07038000b0075107001120080c41e00500400c1206002100d0035072480030084140e524900c0074441480001a6828100059070418564540c88030b002e050501d612a07840e41000c24490103009159003140d0401c10685070040310400040c0a03500501403607400701d06164081c0400c0c1458000c3c2c0d54032307202481c060303c2556645503080b201600010b11192a06412100020b0401e6a500c05c01074410016035600f03d00a00f14140602415101c41803034096055042d0308000b00c076840703410789401044003100c0080c012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 727541735 1250 727540485 727540493
    0x90207080327150411040b0f0f0a030b0112050607030b400b0307081507051c050a0b040b0d02180a1d010e0d0f050901081e072a02010516 60
    0x400c03441400d1034030344540340895820040002003284580e105d100c4065411304101c040c04182e507002d10705241c100101e0311080c0e4480c03402c42521050440050322040d0850754948448104540a9100400c0c03e4603000050040c040140103235035203c810383c1018800c4126140100714002c91501c5040240d071441c02c0755080440c00400c441542d00071161041e0f485c000f034401c4510091200d550309901c030f441803540001d138034003020032680340304d140c0e4950001540ea81c0e040d09840707a03840090a4190380f401404189801207044c03244600030314158100061041d44117051000301d51843e4130311445810031444110044e0303101e550264150020035505807040d224491000043c10240c100800041c410032000079a03500c0540c002c0c1607a00844040719143c00d481c40050710360808138800003002030f40030809200554002c1a0b80380c1c00c0340e40c0c0c1019020f0000d00705480720504005640001c0050901c0c0900d0401d51200c440c1e00e0b03038440e0100444400c150041d40040c01d54440e240610981d401c2e0300c3c803088140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 727542985 1250 727541735 727541791
    0xf0c0702060405030d030b01030518100e07050316060311070b0a0915240909081204030203090d08030f060f0d030c06090203060c1b06060d030e0d020310090b010902070803 75
    0x10807000d01203170411240d124018011301030500703000380082d1415000580302e00d4403044c04c3d8107600082c40503081c4034030807018000190410000b643c1881c0304819001680ba1010030104d2a00c030f2035140300d500310310b04054004050310508035032407140709001d000460108078024921500020000b80000d0496180d1a00344220300488400f0303591517142101c40d55200001c0d00b03050464424450081e0300701034454025004460000d82c2c082d2004500703000d160703140304942c0059500701d0b0003801101e08008040c00000c030384050300c50088443c07250120a210381200c10419054111034220b0b0f40c540050744000c042918000c280d00050100b02c03140481e0810300034294800c4090315000750540f485450b02841612181c0e01003400c03002d212030b105c1081c1c1c0c0c800300702107081070040c14024802d030a40c0c50f441c2c4040724240c1403061386a91001c100380350b00b40117030390810031181e10302000c000103d080250345c1459105110140e00245015004200c69000280820200d0303038030802450181c05031074104142c817101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 727544235 1250 727542985 727542989
    0x901050702010309060218030c0613030b040f0507034211070212030c060906010501140c161e0909020d03050f0c121b010c092c13020405010803030f0c07020604 70
    0x1d85100203200580700c0c85040c40007d51034002c1d011203401100c00e00a0064920540d9038203d0761400442c07040c0001544060401d0b0031034040c2c4e4100c0501852a1150346c1000e4595008075003034042920480f856440d01606421400400207007508e01d8400b6411500480030300c940b4565419a543c2400c0b1405c070600c8090340c1a40d81c029024030071710705110030b58944e664452031031840103214640c0050751071800054058180c55040e582d1143c09442d9003400015500109050303c060b024583c02c4410504800510340000c01c0030516110038203c2c0703509000c80d030f10242c0d0008001c4905218032100580c54a1100604003a450710b44a0f07940d0045010480d11030081c481601118040d400758500d1f011950400342c01d103200320000c0c1c907070051600c1885508031a1078803126008961205010461000390040704044000d070b80b2800400e80491030303031122002400b100d2044100c450501643c00390300301441054050080b120081d40755090442100602c0030300189507002c400740c000740c2041191144016200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 727545485 1250 727544235 727544243
    0x610210e030903011d03090126090604030806010201060b041205160b1c02041211060408070314100c080a090203030f040612050c18060d150312090b0406050901050702010309 76
    0x45555418003405440ea0b100c0c00d5818425800c041000c13506641c514034141d03a40d21040021803a0614910055495421a81c91089407800e520b0074100303840c4c9003408444c41411000080d080920701460087e10341c8401131308081c110b83c9418402c0c044900d100341114107440c50101d500d00c4107000c42c6021441c0c0040440c040d502c1040c4500000390044000001d00010215000601031018880c4044012400303284034248050504a0b0044c01159101056603100c3c20082d03c0c591800e03031152006890468a0352007208d99118803008400081b5041c041c1500765070080c0014040b9044685c0014010140078200081090341d03071094001310341d0b0401c100c40c3c10f505042003071030f00c0b0f42d0395440103031a000d14040d001043c3c600b0320000500c5800f101080365421442d190507807400c00060014000d0f0b68010000501d8a9070b075410644031010700c0b0440b0130008511810300618641c040120007042500c5641c000d058554040c0002e100c030384e070440240e41a603d42031030450744404003400100d02034180c090000e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 727546735 1250 727545485 727545491
    0xf0c09042f0d0b031f02031003021507020414010e0c0d1b0e130b09010902180d08090a12050c0d060b0a0807050118050f0d14060f01030b060603061021 66
    0x10300340d2001000e864030061803501003020f4041e102c01c0c19100c0e50240030401c5846041c0048800d841d0071a0f001d99007111701c002454080c0c5d605c075404614100c0c4e02c0341003440c0d6504040f40000441c5860702980c088009201100c0303072a54500442c4800c10705014040c40105c2c00042001c40c0203404660040f030016054241850200103131001c00b1780781404d0b042c0c41500403403070528240d1580682e070080e005641c1c8003418030306c5142c0c0380c802070600039080500800000b0000701340c1940d25a85411402e10102d006801c09580ca1a890041108a0943d03a04c80b070751111441c41500080b0f04041040814030b0015124840950024a462401007030700510440d409450303200089002d9000040090507504281c907007185150880c12462810021441071646c06140040b0345a01414801081c40440d845582604002600c00130803e081100407030b134104406241e2001007090042c049a603030b81048082e90498030318202940460890262580d18000b804003601c20300350080444e2060f5800c3c3c84200d4010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 727547985 1250 727546735 727546811
    0x160b010e0726060909070b0f090405060306011a07020604080613030f210e070f030803040b060402030606180a0f091d01050903070f020a17010f050f0c0904 68
    0x280314400d50545200001030400300701d0941a08410102056080181041861564880007041880c2d80700030003403100da004100380059000d421001411a070084880b2550300e400c6445d051000301c4000400580c880c6d80044010091480d450400c2c070a5001d6111081e46d546120f4000b00b107051080c3d030f1141c0c5862058004001c148e2000e07180f4440c17018820f0352100143c040c040d004070b89086052030071100310342c00040d00700d003040040d6020b480315a50000658503200d40e140c0540d042c3c1000c5a000369040a0000104410014156852a8009000c032011800c50800c240420b4003030061000722440301c5580521441603036100744114000301843c2050350900d94031164030320090254103c544016558812003869151018000c040c40380078404011030030301c039081d00c64034a28101c0c80020b03a08850b50540c041284803400c2540f45002c500d0500103c2c801c0c1519211034200d4100034030061080310480c0c2441680c04a002c122604000c00301d0380405c0c0b46592003181ca100900401090320300710780305042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 727549235 1250 727547985 727547999
    0x1c0806012607080606190c020a090212090712030906051305030f0c030f0114060621010603060e09070f05151603034a0a0611191103030c160b01 63
    0x203501c00d104943c1e40c0507207600c0301020311655018402111003d0300c0e18400d501c103400d200e4600c03100900e000401000c1e03101c1d40c5520340c0e0201c1e80800c03011400c424523001045034240c420840100205407180c6a044d240400ea00d00501d0311826004550030000001807584216042d08840005401d00406440820307a40c41281581c44480c0805180603001d02101c0505045040c42130701030a910700c2c0c14101d541e80d20101048441e03400003a40403040c840707410f1000844e84011180502030041528001119400d00001c440a0b1070014051003a6500038030040c0400300f62101d4403000c40308140c0e1050143d00c041045401d090144200e20b401c1c0510844042c405c0c1a03140e0441c03890036481100400790710804c1800310701c0020740214181c3d14040f0403c2c92502001c2d09080c403680300ca4044e4251251700446a403207070190345241a403140700388404201d07102000707200c01e800c03c112070040c2864090b980c6d40b0451140c5a000041c41c1c58148a00030800c002d603100d15070307420040d050b13000d08140130f15a15460 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 727550485 1250 727549235 727549307
    0x6010b18101d03010207080304062f0306090c0331050a0804090e070b121305030a0f09092a0c08040308040f061119030e1201050a0b031c080601 63
    0xc100210062042d154880d0f410184201e9140c6034100600d280b80d640c554031010060600e034601030503003118403000711110f20541080109000851081c982e52806e1410811580d02005001c1c1c00800504000f48082d0b1251003050b40c4010f02583c0075944420034030080000782e440e0740c4601070110b0084403e15010003820b50001c0058403141e03a820001c01201d0242190380b43c1c010300821a080d54100001210744e401c02c40c1c1c1680c450102d03d81604107620070340e98281541c1104c5107800c007040c542052000816002a00e0201a19a240c01000005144842128860720340c40ca105034a80c200b100c1132281c60b1181d01c21234001d0b604140380320350b69580c03440c1c010340c241e001d40310300c5542c550603141c0403400c94494003071900100a600014580584011781c040180350301c91504030306103e09441e000e500c0352214405200744400b1040001120f1a0140e1000291802c0d40300c03d51007038101c04441200c00d0801c0042c1400e01d80d00746040c6d004d50740d03a0783c01607070305c11191110740041c0d6020034001f01500e01100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 727551735 1250 727550485 727550507
    0x60f01021f0f1401080114160509030309060a03021306030b01050f0c071205100509030a0507060b0a05090c070c0812120c090402040b09033702221410060206010b1810 73
    0x40007005a90400c29403407e828074181c480324500150320f14020407403849800a070800c0000282500c0c031740045800080c103182d200301c48010209402144074205944154490001000300341414410b580e9020002400c62052200c0842c0245001c07034900c030f107a10304100c154050040e28104580400503424002d9451880b2142d10844600306800560034040100c2911080e18481c1c60303145c24031426540b085d01070000b4503000c54200f11418000101e91f1f1301d41080f40c3c0111440181181d07669514181020040c0c516000b41d01103901111006490b41034080c121381d0f481d9115080c2ca46241c81d6031304041d6013449180c40c400d074490700104011030441e940400900c910b000460440d850040340c0017080905100c0720a40c4a010301480d213442540d00101c41c0044600751000303015060100189070014440d5400c040804042c40d13032910549490741c3d034680699000000b85a078405000d1038144020b60b02d40050142c4900c405d40414513a40381404810f00088000e40101011a600c14172540100003c8241c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 727552985 1250 727551735 727551749
    0x1060909050708071401140901031503060515041802010e0d0807080a09080d091401022104030215030c042106230c1204060b1203070b040308060f01021f0f1401 70
    0x140007405d0001140d0440c1d00800607111b1405c41c0c0003546894002d40c025a9546050584483d0b01210b580080c8540c40080d510072a0005020301703140100c0d21200b091100245e01803841e00350200c910044155038940929424070300728045241160200b01c0390200b205c0000c242400203c6c2c5c100401004034090b1120000581c0c0300d41c4403c3e5100c071925900c5000710602e00108050b0fa4041c44424480b40e280c041004040c0101d450301000e2000001c44000350310388040804030041070900c11481c0c94800f02c0c1000400340d0b03000381541440343e040c0c040c51140b842100d4503411030b51780c9662401d20144e80107220903041202045250300b81c904103101007604e043c412040000300c0000070b402c1c000d207400361030803031101e10040c400c01c0c5c0d644c0e81d40e140106101301c041c0780e0092607858442c10340030b0100b00070440306108028904150a0518000d00801d10141241e440382580d200f0b0000c0c5039a0005031955801c111820144480c03201c1192100103040c1400100e000d5070400d04200050500300d40030504807506 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 727554235 1250 727552985 727552993
    0x302151908010b0714010608100e0c0a0612090201120e1c1b260f0403030909230604090506390306060703020c04021201210c120501060909050708 64
    0x19440c011140d0540900400481c440203209050100d0300605480700d0020f443d2000154046d140c800315440d2802032151600f001c1d07114012018041c0c000d211100b0100005e6405c03000ea80e0400303c010b0074100c0700e40b00e000e0b03180d587c03841a0415a8414520b02c0e841882e130304010400b81c812303840d50300e485130070504d010300c0041c8601111100c02c030700c90103a41482d07800e60462810a6006a625603038484a000d19100182110b5040300407006202d20080110400607004190b450b440c521740949540c8107540041003551410081102c149030310071225108010444c208007182c1e0b1000700050003840d17404070180c0640308413810007203a032400310000654900d549014600c80344150b06004400c0e41e00640c021940c0c402800403a0450074290060031401d0310074010754003030f540c04601190072078200c50301e0081102d01c440010854020780307420305007101080c50710416409003c2d8171550308141d9540300d09800c052904505606000c4c0c04c0d071201001d021101c8042c004d480f01400d02d80e0340d0300d03880d028150040c02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 727555485 1250 727554235 727554277
    0x105130e070e09090604080f0703090503151014152a0d020106091b0c02011b0302010b010f020307021806060c030304050f0d051801080421020a0302010b030106031e0606030215 77
    0x134001403d500c1030781e001c04a903103011100d403411038198010703040c102c0500042800c045955901401042c09046010b080480b2a18062010100c1101141d200755112100c25190324825261080e4800b401708113089210b64030305400812100d070344881585510642010f158082d000c110200c0d03503c16001866000307110480c3c541200504032a68222132100e42c41c107000036110300a0040c605c440741d40d07005042840d00d80c0c030216080e2000d0381c1646000c41c01070f51b4503405280c581d03801c003042e9803a49042e80f0003142803551303c1d40841c4003007109016442059201600007001303940d81204648000e208001507035140d040c18030741155201062440c03a941c034042c20120013140c0348101c060703500a07102040d8504c800c0940c0001034400c008090f0040c0c0d01001b018030f84501c20035011410030642c20183d030086c6200399041c00c0c02400c42e0b00e0041018800e904205041021580030700503041c0606072540810107401681c44d100c03004042035800250803060504403929421004409042c01a1000b842160000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 727556735 1250 727555485 727555501
    0x2040c0203040b07110303091012060f0531021204020330250b0f060108090d03021606180b060603010303080c03090c0a0f091a090103020105130e070e09 67
    0x1008034010310f00030800601940c4040b4603807100884c40c2c60740190660380f41c405c8800216801701c40702c0c2c03041e0000c6108405d407034030300500c24492103004140e50f4038102c0d2941c0c1454001800c411031b0108040340c1e58002d50805103500c4068003c0300a04598000455440d039001210800d40c0100b1581130b8824001c1200c08002041c81e9103a0b0b190848040920008015040f200c110707150708030f9121202c0041c80844030700b4240b070074130111200d00e41c0944ea400311a40b925040000c0c5410700204100d0411045c1c81c00e200c07040a0000d5000c00d0042107040160701d44411008601303503141307114406400c00341040d51044520054445d42d5402138050a8040c080e1b40d80d5209001c12441300b880001c00090302c080003e400c9401050203960003010340030584076650b1803040002c0e801103123500540c00040c440f0b0b20804c050a298030410401e000c1000960800c03540d41c07800030341b295805100190602500041e12444544207010000190140303080c804c030f0905042c60014411900249028003030f568400100c3c00305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 727557985 1250 727556735 727556737
    0x1d04050c0306132d200a0e150f0109290a050406080c0f0703140d0c05040602190b06010804030203070b01140f0315040305090d0c170106060f020d0822060902040c0203 73
    0x1030044448000f40030f452681c17000c1c042c0c501c171380454109041031440040555562440d490080c02d82c000c8000850402414a103001c600c804030081c0300324444802104140d8000110000301c0e92005601c40f0700e12120400c101e28100740071480c0d00b208d20001988405143c01101901c150752042e41d4444107a50790340c014190b180304080000003501c400b4862940064452980ca050000c00184540e09100c0007c6035034017641ca4113400040812404142070200c0b586c100803020101012034132080350ba03182030b01d9002911101810160400060400150500d2300070400c03904010341c444070041d03407076039110704c10700d0001d00725062140301d0801514500d81c103240c0020b800a0045030011009402d407607558080c2d550f54031040c60140c01544501002c8042274400a000009203003d0844100b90040d20355042e0843c0c6264218000384403c000c0c030701c641164000350101d04028141040300098503036240440e40c181482d031012001d080400f20180412801d80c0102c418076200b13540501c8986c2c1901c0301a40c603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 727559235 1250 727557985 727558043
    0x5040b091911040219020d120b0f04020a0302190201060317030f0f1009060807050a090c051917090d030f18060f0f0501030309150302041d04050c030613 67
    0x1d15465020102180402c501d1101c00c0c0740c010801454043d44030000381c0300e440c2c412001c40240e00595001401b1581004c0b04011a62044408004501201c40020b0fa2044030a428074042e0f940414064902c90095048039020545040100c07946d0300301842c001c1c003800050004854035505070717603002c150300c80c94016203000d02440c3c0b014160f20358441c1558150707004010a01d05c0081d00b403400c0003c10f20818072904029104400203420ba0318101030902c001c18085504c8403240700d1030800c8983c40182c0c810265080c045c03903024501410417004108548000da807502040250139601c040c4500503a00107102201c0304480c3e20188031000c150144403081312100030410480010201c00100011500e40c4101c402c00c0400800050401482981000300c9034241c00c01c0703000c20410742c1d050142045110407202160880d103425450a410703d00e000140980001c2c000c01c0c0c20b0031646c0800c0c02c1020074800c00442c01400b0f01110720300c0c6402545100c201d100341000743c88c0440301c80000e8040303107100f01c5013002d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 727560485 1250 727559235 727559263
    0x91c0806131505040606030c020c0a0b07080a0905060f070203010b010c02031f150b0a020708010209010c0b090307060f0f0c03061d09070e190c03021222060203040605040b09 76
    0x6214025400c40c0000d00304036039010007a842e00c1500800c80e0743c2c03544155005085940c0d40000e0041a0700c0700a031a014018680382d206050b0164100860000d420440c2e12095014001c261103004d440310030789481200b0303003096902070004149911072980002c080e1807564003c400a100e0008000700540c0d40c00400300000c0d40540103118400035090102e14540005480c41c0703400601c010400d40354500070318003504011341031040082c11409690b810060749001d0f140b60b0000b146030090010001c0c004040c01d000040c036810070100098030b070310b005205607407a103500040103129060421510600030507a4000f1402a685000c0078400403600c21b1003603606880b12403d100c40d414403020004a01d804009215032414800c03a0800302d130b913540300110140503030b800312510505186070ba1510b6042d42d40100b05a000c0510500c01c1140544100f001c154004030040102c0d01e0244400f90f0400d850004040d0180a0030b0000060004100607680120300ca24003e0164001680307030b280100e51240c984081c0300d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 727561735 1250 727560485 727560499
    0x603060a020c0c0306130c06051801180503030c060402010810030b0c0906071208090111030f071107081917041a0a0216060c030e01090f06180509091c0806 68
    0x361900d449074000d00c1d41a0035101110360481d06400003e1420008449417080101990180710400a0441c05c0760301401c65810460b00740606080760100005c1c00410031410043c40c680000040701134400c004002e0f00000e01601c7e604d100d441d8040d07607614020f075401c81c00940500006401d10070300c40081820303070303500c440001aa600c036562400340075040300c1d0761140d00c54002c02071800025001c50040c5500607140c2c4840c90300d0714040e2034031800c503140b003070805405481c208100f041d000540f40307002d540403840c1d00703040303099a40d003a031814030300305660300000c1d018403824500840410601c0096251140b0901c84015002040d4030700728000d002e548503070400301e80c802c0c10a21079904802c0103840092400e00c101d501d05a04103c681e03c0b512882d034010000304e500c0c40e900b04207140d808402803e0b01c280a00702525160b241500000c500c0b00d80d4401c0d0390400014849840c40b042105047d00c2c000c003401841416241440081203442d8a070080c2d03403024204054001224050140c2d0065115071760060840e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 727562985 1250 727561735 727561741
    0x50a050904051005100903150204030b0105060d06090213030c090c0e0d060b040c030506090f060604180204080d020c0909120906090d0210050c070501050f0d20040308090a0e060306 79
    0x4403001e0078001c1c00d08011605a100e0100d410788400c581d04402007400c0c6d441c5050180703035042021400401001280030140100320030300104925001d424111403003a1041e603543c04101032850000c21140d000104038500004115440481c0050084242c4c2c0c020406400c07296a681c0000d0b0456107084c0c03030a07000c100883c0b049809860640e8801c003099000b007101164201c00c0351b000030301311000880c2400100365a10241b01c001e0400c83d044551002c11404c004555040c9940014010300a9202c0c03110045400f141d0050b007001c00b501030310010301260084401d079410411010b0b4541000d48042c07409401d02200040581e28005041003102051083d003a2500d403c1005012407640300c0714001d90460756155035280141c80f003000340040c1d004159600d540351507070003880300c0c20610554007203810048144803e0400c0c41c0c01c0e0b401c840c2052001d500c0080c00054010010790780f41000ca604089120000c5400024041c595006000110003211015001a100c070401030300010250b035069059030100c400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 727564235 1250 727562985 727562989
    0x408060a0c140a0f03061203090312050d0501030b0115020d1e0908030d060e0108030c060a05070c05070605030708130f030e030c0a0308090f031207030309152a050a0509 74
    0x4040300a901518101c8915404200703a4101c40d40030344403010006072403006110301e0b5a4507120360000b50500751f980b49050302c3c8588000340050f00fa03010140035440715032620101d882c000d500315042e50078010001c0c041c0b582d507410300c0707407412a0074800d08020284030302c0400c508038808103640c20001c28a031100b80e030800404898401c40c03403403030084c1024040d1180010079110b40170130150080b00e5103180c01064540c07d1a0843c41110010f274040e906a520507c070305480c014001c182141c0c40380000d000021141d50b0007600311400c1c07001000146c0a401911008204103502030011841341300e550702c0d98041d503242c0980c1d162003041c45640140080c1e011303841c510000f92140750784a6110070001d00301c0b01d01c41030a900180889056500c101c440300000200b50420b81000c620725045003500720b02500b0b400c3d0048000090610a1405c0101007680d14207406041240c551428528092000010011800000540621078920f071f580c600c500814201543c2070380e0720440445e5522246640e80c1400c00d100042 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 727565485 1250 727564235 727564241
    0x6040509010209033d020307020d3603081606060501021b130608030f120108030306060417120a0804050c0a030302100f0b03030c0313120f080c01090b100f0504020408060a 75
    0x749000354403000309040104264040c0d00f24034800303041c40011f0303480c10b000c0c03c007134034050a1203145010f2011060340c00084606d04580418204c04a6011078150864158804680d42c031507040245091000318070440c10900c3c60385500461440f0b1042005100d80303070300059079980e491200c005e0171039004041003002c0e820304090383c010030440c011008c101c680c0c803010316034250b80212200c0100360801199503090000481c04440c010280207010f94511304241c5d0201d0308520807030044180342c440846800980f044200040501901c414000079111440114001c0c201001030b076041c0d440d40700304800c1000701d141c03103901241281e42c11380040c028014002b903001d02034440c0942101c1600d40c2c407649450640c41c140000c041c000c10b958040e42c0c1d620450041d5081204268126019403210b504200c0002900300f5094071242d80c120311900d44400000ea150707805820760f0500100b100c0110401e104500e1010150700382521441c404401c6c40c075403264140b1049008500c40c900269102d9000315107225141c2d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 727566735 1250 727565485 727565533
    0x3030405030901052a060603010f111e16150e010c0e09060109030503070813080f280206070f02031b0607020f0d08030c0405040c05040506031920030604050901020903 73
    0x1e440110309040100211200e4000345c0c601c03001074014a04001d081c0c40c0030f10031119600d103940010405c0d00c044646800440c0250300ca0007a5805421900e90b05076501c031030680320070120110354801500d2080ca03202090402440316070b5145c90901100b01300329641801045602201903803460843e465000410400f088058040d9043c0203034014080701203501403008240890003440800d6a0b8901d0501020854445902181294002400e210803134000800d1103034004441080c10215101c2d101940c2000c8100c1c940025840080050301c8402c1111204905c14668022800e0f186601015a440750217618007000c6161b02a408200481c01440c1c07000d0b00c0c40d80317041d010f0807030f1780c2c041d071160f90707607040c941c8281d9040aa9000205040005140c540601c1c850000d075840d20b9820705140101140302400090b04500341c4100c1c2c26084281c1944aa11507e00303104658403903510801003405d2100d55030310070342c2c8160145003000001103180c4030500813590116000b038001c0c450f10f1507802034504004990 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 727567985 1250 727566735 727566757
    0x301051305190c020a02030d020d0804060f02040512010b031203060a0b0d0e03030408030405010641040f0e15010e07112b0e09160c02120106061701080303040503090105 74
    0x4040c2e640039030702007031048206800c11900240600f4000780100b42c60000104000011584a448042c03e82688049855000b560003003001c90b01800349480030b030184c080d58010030703001010241c4580101005420002d130805080e030664026180000d09616140710031522030382c01140c0c0e100100420300c42c0000074040700d801c1c1c440005a04c00781040c1a811540262420748a1401c00300c240402d200c02031140400405060010410042c0c40010750f000d1020f00040c00300e88080f0b600e00c80030307843c02c0c0d170b118001141400410400c042d03009501e5810050481440325115845603542c241c44800c42c1050250685000d86041ea40e9940c44c20002c80d55011272400d107036898003804944012202c00c246002580d84141d800501d599900da65000380800e070140c141c01d01c61034008003400700d0200011a10b8040c140903207416140e1940c3e600211303100d0505015035181030b40c60018001070080c1c0c8034650004100d10b054030025543d0f0b232070440035901d000559016040350000c0100e114150300850007481c0a00c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 727569235 1250 727567985 727568011
    0x10c0816140d0b09070201090b1501030b1201051603020315040c02030d1509050f07080402120703021210062306071401021317070807031509050609070f0b0301051305 73
    0x1e00401d0040075000010b0041e04180c88043d42c00003407401c503624940c4142c3c0751008209a2240751617a010342c00c0301030420307103502003c802c403d03407175900c6500860030b000c601400b030160000800404900810b021141d80e44e00c54020040b0020b040e02ca070003144c0c01160620310600f2180240d004100c001c01c220413855043d48410880d00000c0e1205004868070010172021503550700c0d1a20141d0343c1507800050854480f80f1494041150703150300b16110b140c0180d0162000950300c101c4004092503c0c100c2d0b000170390300c13600720b007000503828130006264190b50b020800140416a0386148040d140c0f469500e060910035038403004001c40e8240440a07200686c00394200c400f4000301d90000508a90002e01ca54007000766001003400300001d140380819000c007100c030040c2600c6107080c41040c0c40340d525000040000f5480302e013043d9551200d8004801c00c0c1d0b0080d060350058109180415522402e501c0b903c241101140fa0026030340b8000320a480c100d40c40038080d4010141100029001007500620820f40001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 727570485 1250 727569235 727569257
    0xa0c03020c0d0201091e0b0411130e0708120903060c0d0204120317061c0b0627010f150e040e1e2109030c01080901060e0f0f09010c0816 60
    0x8030801c82000c0011140d000003490405d641004452034241d495070090804a965460001a1200c548254000d40220110508141160000d021540d050303401c80c680e24189400c88088010224444003103a071900d0444260481c0b82d0b00203070683c0102c642c5030ba4540c0009000518000504d0010f0604000c01c020061916031a0228034404100f115002d40000e0b082e9121040b154250303440d160b81150040b5400300c205031a141c028603010351040301c0144094900070116440340c82d030003105d00c2d018005108012600000402c2c0800f0751809103c0d1350842141d168000400a0424201081c001d40d10340c0d0328640d00c0001c100b400041c0444004180162040140340701c5000400085010401e207040054409940c141035034581e0040d800401e50300c1c60700700700503104007030f1b0300060300032800c18013820080c0361552002c040760b0040007690301110034541003401f0801e034211806d60551207a800c1c0a400d0102c0d40f1510f820908840c10381941030085070050001c40d55001c4070030004070340c10304a1325220009075 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 727571735 1250 727570485 727570507
    0x2a1110030618060e060901080c01050d060e0a090215090105040608181606120e0a030c14030a03060e07050309120d0608010e070305070e15010302031b07050d030b030c06030a0c0302 79
    0x500070700c8810b220740e444400b80803142d1158619500002e0031610f000c029410301c2e080e2911251881d0040d414800001240c0e01d458141d604840020700484224080b24038111102101034400400100d20881c00c84801c0c404d00e0304100155a1085410f0f13640314141410000c0944880300043e08440340b43c10707464031040c51351104110b038860701e4020303080e200c05c451f14007100070b0454452341e5030700c1e040316042003c42c00d01d4070781c00030780720740c2e031540518042007034440ca0b003080c01007030411203a410b5031800005030801c0a0380d015006041229010341941441c0c0d03035001c404640a0100b07880d890705c550070550412008003003100160010740d203190400150345641d20340f1642118617007440705a036508020000c0081c00418442840201200c6941c0782c014a409015040d840000c40c003030b90f0505501002189020205440c2e500c020f4a11000c010b40d1900c0900b070440d0394101d80400b000000e41000c26003001800c010a143c1c400c442e015100505546031091418098580e00100100f019402e21003d40c04c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 727572985 1250 727571735 727571759
    0x60402070209040302010615020a0f110a05101106060406030503161401150815010303080a0f0605060403050c04060801060501020a060203061201090804030c1514070318062a11100306 80
    0x43c2c0c070079000011003e16001ca6140545d161125181c01d5411142d4804041416055544855644801c40351405044c032400074506103001e801594000c5c10032404514030316048498600d411003004111000c0c0d660b224204030946e0780ca80401007443d0002c0c80003020b0030380043ca00000ca90303c2580d942200300203c0c2c40741c500b111441052003000150720081003040c4407052000d400a5408a01134a10641c11610054001040681716002c1940e564081c410490030320707130044014200007041c00c0e50701d41d900d0804d80d0b512416003026601c21442d012001a42d04014440c0314201d81c010303005419900806d8440ca8025080105025000b208581c8441110002803145054076072290034810303103803800d5003012000981241c016a480d409102c1510207a81c0c0c000802c90071607a11a000d8981c0c0707403480d00d02120715820541403c4400c030300206020039a250030218400300900900309a00d203540310b000200c19407100c051009004514001941e00c06800e1a200c0a40c00f2000342c01c011601c80d94a030404000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 727574235 1250 727572985 727572991
    0x309010906050c120c090f0d050a0f20013906052502030a14160b010b03061513030618170912060403020c011107091817030705030c03060402070209 65
    0x143c040c000074000620405034140a80000505001c04c0c00c002038070000c583c065000640f020b2280d4402e0100c0c2007005070403c200c1c8112540900410034455942c640940a1040015201d0030319200c60300c50400d039403040c4905000403c0304480500b48402030441c085104400311181c01310303075007040c008001144031401468054208580c4400c2c6050030f8005103010120400c2d50001150010403a03030031002d902508822901d000c91100d40c0e550a1103000d15650000c480c003000300702541500c00002d1001000d009141328540641c2c0f0002c000c13600301c1d00034050b8818109003450a42e4501d6052000c02c00d41e0740312000e9440703000c5042e00ca90203191a10401003030103009442c2c50040019074201a03040c05900c824041941100400740f034106540c0294684440c0c04042d4100003080d6100d10a00340c08002420003820f0044007082500d41514240444011041c4190313401181c00840e800000c2d0080122445031a041e540e607030a40c1c95280b61103100b84e001605181d8403036000e105600140c1d41d42200140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 727575485 1250 727574235 727574251
    0x1103120703150902043c090b0d2112091502090103180c0612050601020312041b030b0105030724050a0e090109020d1d12222616030206030901090605 65
    0x81d10b420300c0a06007034041e4101b40702800c2e059400000d5581c910302040c0082c15200341c0e0b040410010140e03404a07508440d0b41d02c020f8160b0941540d0240d006014056144540c986540e541101054209100003507a0703254900030007110495900422080469001e024000d605240215010802d10300c0c1c1c00c038130320303056006030754050320072000300721290704000c8100c0407038100c0006000341d02d040320001c0d40340e0084445d03145465800d4400901003100702c1d0701003070700e003100c00c1c81e400f080580340c0c00d1070541a0803d008050081c41100c8010036031649450340c10783d00ca60800340d4031104d6000c200080b6019000312502c0d00c01c0c020320302d8421900b07a0f20106818040c2201c110016210072003819103800351b070701c002c80c16180380c102c1024410507554080780c4078100d074030005a443d5079201c1c14000301449500c074000040001c0f55041001c20011010243c882400c004030f000b02d1400c0302c1c80016030780c46003185100358021881c440c1c0104010f080203c06140c0c080c10603070000a542000342c030344006540085a0302c00e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 727576735 1250 727575485 727575509
    0xc0a030b1c031d010e010f050a03090b011d090c090402120109050118110907090b160f0302030309100608060106030c0201020c010608030c070914152707110312070315090204 76
    0x14441c0d50030310360300d00369200017403030000000090080003a241400350088030b000c010300000c2e50b5081c1406500000002039200300007881e15070350f400c50240002007011381109403040c440701082c001d900004000c0641c1c08000c18107080c03500e40b9401c010b980c840c5810030907215503d035901d00c40898000c0c42071131329160381e81000f44045640c41c500f41e290700083e041c015110b60050428414950340c4a5092416165046200340d0b45109820301c4040c4100900c0005050310520300c8291304041c1c1c00700c040c60144505038201c60062244141c02016a0064000c1c256240e008400400280e482a0401c00040d40c0c0c07400011300c1c3c00017058801d800d60700315070440395440e8000100d602150000300f28140c0205031060f002c010115043d0a04103152401800c00d64158044040c00c2c9041d554440750714201c03c211100c1c81e01c4080448104001100003103900b680858044600200420030110403101014060685003030b0039507c85400f9401000092601d028400c1c0c5098081800103491008101405081e41c1603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 727577985 1250 727576735 727576757
    0x70b130b0c1912080708100e28020702040b03030f0a1409120f06100b070210021c090312080403023408030d05010515071e0804091a0103050c0a030b1c03 67
    0x94001324020f03041e001085256801c001c1d6031900d40072030707406845803200240c00c546c9036081d2004910a0400b400280c025020464030504503080e402420002e1080c0d60901c48442040201a128040c000c062141130310104803801d0301510404a007825440300800c03c41c14218a14007203042d1000c91051480240c0c01900640b4040f1010040030394008009441c031031500d424541248102d0040f00c0707000340a07680b015400b5034003034000c1c001d480a004515412030040300d98403400401c1801248810741e009281c0130b501d015080c3c8250400c902c2950107400a00ca0340d10301e01d0046c19a140d004481206c5982c5807021869400b10200c4004000c040400c021a1a101d4031031b000070884906900540c402c404030401d5031145400001600c250380d401c42c8030a06450050382c05481c021252040050002c04006800305008201d41d00c400d00c403152100c8a8200415204015802c4072415603210806000900001000a00c281c1000d4040140600122645900c00d80040740d000d504450843c0130444500035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 727579235 1250 727577985 727577987
    0xf0f15020d05151009050111032503030b0603060d0b130204052707050a1a0c011506020f070b0d0902041b171303050a030b011107030803060102070b130b0c1912 70
    0x40c3d0304070081c211800d10340d480316030001070902070403486280c3c10700034840c09440d108141803043d00d885000014071090345c00103109c8208520790070168100c0209142940303001c0d043c1801e034296840f40300050000803211840d074940d120f03d00c41c0241007800d040b240d0402c2000580f59030003040c0c019400d83d003000740603070f110319400c0131904101685140d441e03100c404100220364441e030354803045070340000d043d001c0d030102c01041c00001e129074403044016601340001003c808030100e10030790450301103a0a4031250361a100ca0b2540315241c40c440e03551002c0007400b035651560303025404040f0151000f400041c416101042503611100c0c61340110000c203080c00768080d25481040b5807a60b0000d03803103500d40301c0740c0d401d40d50140240c0944802c044c00c01d5559400e4114590255500b480e5110000c1c0440300c540760341c0c1c5801c40e12580200c4105c0d0041c06040400a815850f80043d034284c080d10070300341c41d5124148242900725400075840c1c080c43d4070442c4061003030140c802c02d0ba000e41600036240070b0a16000018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 727580485 1250 727579235 727579261
    0x1140a201e010204170a05030d05040309150504050a1d0403030b01111e0d0903050d0e1804150b03010204050f04050a020418060501020106050f011704110a14040501050d0f0f15020d05 80
    0x1c86801c5c150054225407002410100848000240e0071200145503100e5040460381094541c00030200f07050301c80111021190410046c00c01c90b6800c4505112960f200c104041c0005c4040c1c2d0400d0602c404c40e8042800680241c00c00740b088441890240d40c494030884030f840c0380800c1c15520345402d203801e000c0546254030505c010030803c04903080c080c1c001850741d521540e95450b011181420811030441c09505a0345140d071038807140902c08020380540c00c203818200c00b030020300084181c64600d80413030f4070007904040c02920100e0300018215920900080244009401c005000011240d0708010109140701008010501c110300c0303080000f6840c0c213080029007120b1082c0c21484c400c0c030140c861200160380c03044410000404031100410306440d0b83c5410721703542e11200c1c0f002e64000030095003c10644c40354200e0242440080320300f070145903a2401440380c1c00000c00400b60441d0b103090080c0001c54030782d25240103e58400d1601085016000075190201d070060701e000d060f0301d61207005016003112603034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 727581735 1250 727580485 727580519
    0x10020912010c050403030809031c0b0108060306060f0d05100e070e0a0902090402040b1f02010c030605100903171e0c0105060a230d0b010303090501140a201e010204 72
    0x3000070800c6680b4000d01800e280100e1000600700000711000403d0304505101391400d42c02151070000c1500c1410002c040504541c801d101d0014440000040181c900001c40c04e0103202c1c007811100c1c804501c0014054040d82010303080e01d2501c21030b0000813403115244261a503210203080500312490508612048481d40a80790700c48007824124001c0c0540da5411540b50002c5d4101e0b0000307030011032500400e050000c0d19940b80d45904000001c90605501900081c0034000266400c0042d1034880c420050039080c400b0b048070000306000400d10004900d00c0c91060000600504c40d42407903107601c3c3c2601060420729511038481404508145821000d005d400e422240407035201000f00c1c208800d0b85403111740c0c081303181c2d810100380c0d100ca9110b40b5004425800c064000e0304070b40481d178581c14040c045c0e1405120359400501c1031108410900040e0301561030400041d84c581c4880402c0c11309210131050148120171890107081940b40883c14121031140c0b00003070160000d81c582d8584206800302440745 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 727582985 1250 727581735 727581769
    0x2070e071e03090c030605181c030221130c05010302090f090a06090e151e06040911040c03060f080f1002030a0e0f010b040c0e030c13020c100209 64
    0x1405002a0056456070a40d120800100c10381d8540d9a0300700c001d01880480603100c400d06107404018000366400040c42a60800c0c0e403d001e00c0003540321aa503a41840801b81c42c0000c2e40c1c1d000c1030400740700e40c008050707603256101c01c2203400c030f40e10b07030380b0745c03800c1c2050b51a0115051980c2c041c8007085980364a050040c202400c3c1141811900404644424241d021461086c81c1c2c0c600040c0071403100364081c0014050b0100b08110302e068003a80709649010000c484001000c1910010340c1100314400c0c440b40f07510207111204110344a0754284070244c088010211880d0140241c1d4200310784483c45410070441c010741c0e0206013189404000c080043d00e9400c2640e254000440e509508070000801c01040c0d503030606d0050b5039648140f501c50042041c24440303005ca0040340031501403030708150003035510418120390411010242003016100320040050342a00741d000030354180c420b0701d41346e886c55515803003040000d40381050600c03500c3d09000f4000e05035011580e000c9241507440c1071a8805401d02041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 727584235 1250 727582985 727583009
    0x3130902031006090b070b18030d06050f040501051809070905040b06190501050f03090c1504082a0607050109022d090c040e0403090305070e0a18020f040f0219050702010207 76
    0x70505e01400602c6011005400b114000012410032030201c40152440c0d100a020b41e601c07001550041000b402581c400d1038444c0b101c3c050040070526240c802e40e4121480107000400141d40800f414224004c000c04210843c02080e0300000c101096000c0c044c8202d22400c40c8040a140440c2040680a0b095000e00d1b21080c2e0500c084c01280d801030304031104184404c00964807a03643c40d01c031031303d4103040e0325509030420340c40035610301c4c0800c28001038000c3c1c55900041d9118801c510220004680310469450480c0400e12400202410300000400c859405003001103421202c1e0b40215845844c0c0848049016882c5012407140302c000c1000502142000c50340506141000c82000d41c01e0301071800341c00e40d150291008101018003a81e07000303000310f0f40304054a1000d60303101005109980c04840c0303c0c2d140b074142041c0d50032070070010700c1d15407000350f0040c01801071511150a0000030100007601da0340d1241d0030000c0640b80c01031001c03000710a00d1310f5500c3c581d0716000780c80020b05045880c2d01003804018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 727585485 1250 727584235 727584239
    0x1e0f030b09240c1b16060f030e03090618090103050f011d07030201210c180b130306020d090f0c081501030f080a09030605240604030305030411030313090203100609 72
    0x40200340345421414000f001a1580388134040d0141601010009903c1c900c80c0f2240349110700840c840840894010780c9502e044000350010a600b80c0c3e141d880328020940080081c12582c1c0303803c0001e0440c20108402c0c4450050640c80030840c0b1606c01e03041034891381e000c1514806065000d000e40c101c002c3c0820009815207200c001216a070b40083d0200070706000c43d004003800c1da01120034402d090820540b4043c0204d44284a025001c1d000d0300040222509008802044a121040c200d682d0100303640c1c0c2c18a10146551a55402500044070440c815500c41d1400780100d14205d091010241c01440c848400034600ba10140c54800003c00c803e1031803410780c004001042c0503043c1039003207981010380c1c20780d22907082c00d048549107407a41009004500e0301d81032100003608080f0103420080d6200e810204c001c241010050035024900c00140006d45c04c0001800288081d8415454800050308887c14110822a8119240569005004125030101c10440a062140a03070001440300b0b00702030b51258 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 727586735 1250 727585485 727585543
    0x1008010c142a06041103010501050d0b150307091e050a0603020603011a090406090c080106050309030a0c02060d050403020d081f03020f010c060c0e0a090e03041e0f030b09 75
    0xc0694030440b90400c0280c40b05401d082d0403001949021407aa106680340d0740b50a1a00c81159203100c00c01d14069860800081403a081028000014541080420006a41300700c003014104185180046c1c050003141e80014003030400340202081c40c0841c00341c12030104810b07203a10045620081c118401d13507051070001c2001d61500d104603415105c0304a1003003800940c910900c5000d2003503d2035a130b04103140120005203081e081c1c0c0300102d40790042d0b0b82d0030000c0c1d9842e2000c844a000540d06501e0b282c2040004aa00d1030044c0d00c1360701e0140c8050206800e04a907840828211141110140c0158200b00c91000c00f4640c05582c0e503500076401b02440b6030028a04021303405512141c04024010310048261070740d11303030040141c02012903200c0d10900146001c00d20082c901c01d5401025030041410000104842a55000328070301520120010760a0524044d40e0424132960704a002d203401e8070442000c280e89203075262041c0070394003030010a0014201b04444518000c07055694001d00444e0a01031b103c50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 727587985 1250 727586735 727586737
    0x90e07110c041131031a061207090c0216080303092a06090103091709030d0c0506070507150c05130e0708010501180b30040b0103020603040303141008010c14 69
    0x12200d498680311550070002d00d4040002c1e84c030748009100360580c00300001040807410700308409141c4004405c0164640300203210b191440d0401d0341441e034200c010b052005091130341c0b0100c0d00c0c3d030991040b9260313880c10100026046174142c224400e660800410000e12010401290890404a07403a000c40c113050200b0706184429188a40c074841d01d000118094a0380c0f0a4103c49041504110701101c4025826503120342980704c600110f00900035100100b00207409a016600d03038a4102004e44000c0e03032a248121419800b441c41210741c5540c1c41d1680c041c481003442031418008d032a44400d0354a50346405081307030f2010305520038500d03d140300c81009481d80e03106c3e40203811100c0030700b0003060a1040c0035088048a400d5084403500d41e2000c0b602c001c59000b943d00c0110083d100344010b00c0c0300480040f01d1980c1c948c040700e0117081200720100420060a08034000c0d40d01902925002500c210f4498517414070140503912854550030b410418065104203100b21201c013000d5040c4043c22020801006d801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 727589235 1250 727587985 727587997
    0x25091a19022a150a0e0a06034b05251d04020c0d030f0b120604080c0a02120a0b1501120b0312040e0a0b10080406050601090e07110c0411 60
    0x1009200c04070b00106450b880e4407110140c200c0203005813122080c2c0402011565160314941c41030f03081d0380380003401d5802882601c101c00c1f1b01e0880c1100c203140d00f140700b02041403210811101c10441d10b005c499849070140074858041c05646021130903080400f007817441808800102500040503c940514a5401c4a0440c80391b01c076141d03000007a503440c4c000103402030240b084280050f00480b42604296503040d030041503441c1581c941001001d00b00070a100d0701400341031800c0003da11074000318011400e0113002d480e103c0e40c16000c840002403190701040000c00d0305a10802d85501139010b00d400c00c080a003240e9400080c01c1c183c0c141502403000003c00c0408541c0b804e0031030699403244102640c40c00d2010008051025420564803076481b103031103130004811154003500901d094980e03012440c14040c0c01212084c959290102ca480e1612502c008000240166040c40503a400004030070f0381c11031366544108555101c0c1c150825003a40c01c2c0d81003119008442e4482c514001c800152259480f0a4680c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 727590485 1250 727589235 727589293
    0x10801050d0309090c0e13020703170c07080f07110102010c081317030114010f020607230c06010b0d0c080105060d050c040e10050f030625091a1902 65
    0x59046142e0809480905098000719162410b24014440d50780d0401c00d98042c552094130130b0003140c11700e1440d0404a004664004001030705072586080411284407802d42c020342130011441c6071541c0d507a031391820b0358002e0031440c03081d00011a0350b03414012086804200013400380000d04c01040e40010092003107100a1003400c829004840340d81c11b000401156103403405503c000345e80c2d03d58541c9464190b0314440030074140010710400f202021184046000b81c02500365403104d1b4054560502102d0034a02983c45040c000234052003026400401000150300811182d801e850792211030440900a541c020395920080c01841d4004001940b0b03148211ba8400f004490005201c2c1c0701d100341004948115884412480084010700007940c2d00f9803094022914102d5030790058003900d509050721034400f201d944503044404500101d140c480703070794a50700380307607075443c008010644030300b804045040c03140680b02e560000800c0303c95000061000e003400d111014001840c41003550f0b10795090424001000c06 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 727591735 1250 727590485 727590499
    0x10608100f051015180e06150c0c041808180f0a230316030308070210050106020a021002010f020a0c0b1513020a03150305060a11040b090d020f281401080105 69
    0x13807420b20800554615032056214080001e50302c0c0200c00781820180c90480c0b1a040c03c4211b10354540300241240c1403c03c1c440003410110300d200003000014800005640203c0d0308240d5184001145c44006000d0b000d40111125001c103000000e00c03506400f15400c0501030fa6194200740120003038031005080c01c07803002e40520864110a0013103810402120304903404030344865004410941c00483c5203101e42116800c941103001203640d15000d4a1081c800c490141c0c0051095001505001400948001d014000450321408006012089910210303509002401c030b9201d4501b00501215220b4000f4000a982194681208002507944000c1d40035480d544d54000b8100543c1c50094001c0001320103052042d01d904c9680703051a5498110807604180400d1a280c14402c0c103800000c1078806555800c041c041c02c1142910502114110b031840c2660b20481c1c1842c0491595134400f104031520309442c20015102400c0769070391640c480c1e80d0304204000a03a00f540c0c40c07101d0b644504400d04480040ba018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 727592985 1250 727591735 727591769
    0x411040b07020a030209130605070216030b18070f03170a0813061103070c0506100b090d170a050c0d021b041e092913030f0908010608100f0510 63
    0x20000380f410b40c402508080708400b0020805001c001c03c540721070081c07805000a6036046001c03a1101c0c00301c4020203008442d00310500100d514440015803014115843d800c10b05c1c0e454804920b090082ea024080481085a082c410020461103d0030280179544400f4200f401116025004c104020080c1c0b60306c0b1034018800c01880b0090700215048401c1c1c40c01c1540e01c0c109450000e00c02420381d042030350144039040100e05082c0d03031010080b0465030525005070410001c00e003003101003a0440303000c1e02c140344046000a03018006000601d8000c400313807a525034860107409051304060003c02c3c18000e54004254003c0240500c0704210422401107600080c1c49840314200620080d0f403016042034580340000e106c04201c90300c86900000c102d12100d4500483e000041c81d100d990040380d0218074940b041003042d00003401569485100782003418004120b54480d9209801c45405c0d034802c2d8a5076201c1c212810007070141d442000c01c84405104c00340014038040c000140442007030310515449015200708 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 727594235 1250 727592985 727592989
    0x901150e01141c0b010306020a0e1206040b1f150f09140d0305270a080304050f091005060f0715050108032b02040b040e0612060a051018020310050411040b0702 70
    0x3582d43d20356488040504596140d05000c4000d4201804500210300c00c101020b00782c0c500034030b004081000000003008680e03150b13a20034814150203814180d01ca0581038000400c000a040300101900810980514130444180000c1500d00e01001900620110700c50078043c1044011141207111000d554a104001c1e031480c2c00c603414072842c01180318207220f00d00d99600324a400124000c11a03001c41d0110f40040d01e8034121512441940b06266000030701019104860400c0881550b22035512051040020b949402080482e848041e0811500400280100c200981414071710f5440800721010040c035818007031220b540344550303c80c640c601c40b4071001c00c0aa9012144500890010309102036449a9442d0000d802c0c9811038082d40504030000d41c00180c0d142880000c2c00e20b000207550040038640c640388a42001030401604540219401840c0442e06c8009800d104a0b00b45c4c4407032005a4924003d0341000342044107803c0f261059040401c1c00c820002ca0300d051390180c2d80c054a0003a502c1220b0700c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 727595485 1250 727594235 727594279
    0x6121a01170705040b0f031605040609210c03050d1206031502071b060f12020a05071509050d080628170a05070e010806011208120405030903060901150e0114 69
    0x4040c02d003e80c800990303007403096a0b0a000c1d40c040c00b00340d0301951555102000549e06401140034110010f401300c0c804000e10061880f024180c940342c0541100000000e40780e05ca0365130f085810a65140d03210b0703507196100944c461450f10510700e0304003040089038256a21001304071a040425244103402181c2d18060080a5402c4880e484850341a0540d841e62008050012010306034800701240740c8048051110081d030003103c005240e141e80c0c05e8030340305281d540c150f54059a40d091000c610303500d20540380010b40401030000401c541d501c0701407440c40c00c81c04000c000d03d0314503070000030b90300540c9205000b204000c42034820348902c5c07001e2a481030000b0721060303e00640c10300050404d11518030001580c0402d00b078a14140d0b180501928090780c0c960344420b010603402c6400818001c010480d040d425070181c090b95810601c030300c0640e4a42030050002905c0d243c41582d01e4034290f5591014013030044000141c610082803207003d000c0c01585000f0880220a0701300940300e0082c0c00b4040c62210a240d0f0103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 727596735 1250 727595485 727595489
    0x3020108090f0a23030f0409090804080105191b020a03030c170a060305070e1302130609021b0714011205090708030c0d03050c0403110d1401020406121a0117070504 72
    0x50120360018080381403040d0502610b000200740311100e26801d050813a000710480f0b81c4480180c4503540ba0074541080100141380380b01d41912669424800030410402c00e00030319004074404c4004221030404122404101c41d20548003817104d404010b07a060703481da0046401d5035160340508000450710b0020b031003540d0b00d00b5240c1c41c440882c5120410050843d407140e0001d410b80c0c0c0034800725400c46881d428007420700d030340a0b201b585890305110700710801840c00d208102c10504140c00003048036940d0ba01040c003a40c01a00c180c044d4005801e3302000d03402010000000180480c10880581da244000060404031140f1480142551139100140ca9600c08025000082101c00d0407255514101d40032152102c1c042034140000900b0100414040510b0b441550706603500030004a20a921070320410210100503802203030400100740310b01090900c02e1020f08000d040781d031103c81c00342d0003001e442d004444000110b50201400040c070b1994503680203c020a101503940d107184800d0300c400ca41552039014507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 727597985 1250 727596735 727596763
    0x130f02041121010801051e1b0301032001020606010909091a0907030611030f0c0a0e19030204200901050d0906050a1b08011410050d05010617010f030c0302010809 71
    0x148402011408180103aa0100b60820415481e6216407400e803d8a00a60390030101c08020405140c1c001380e0b908480790015100308070021000a00d40031144103802c241e01c107440c131010580148223130b4491420a008405024805090704e40340107070001e040001380f4091001c505546605040030440d1042d041c501d5218804414074407450400c983d00d0f514926800100c555500b010040c0f80711001100c01d5a001d4600c5180300411543c0344004218680c00a241280400c940003015000984410310102d004400b907802c00c0113824118014402030722002c00d4001c114410340040f002120407000700760355417a8800d290195580c484240304c400980b41c02c00029103110710340010b104001940d60b000c1000c010707409039180881001c10400f9204180c0921540d4280b901c96603c854203460225080241c54500e41001d50410980c041030200726182608801d01244542d0119105088044d1180d801010055811904c060559945001c2c40c0d01e50720009050182000105840c1d140500a4810746200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 727599235 1250 727597985 727597987
    0x7090b0d08180a0b040e04150b10021b031b01030207080d0608010b130c020604020906150c010605010e10020c211024060e0909070305060108010608070b03130f020411 73
    0x4950030760b00c5504100105540704414040c0c0014020142e0010703901114079051000001c0e03540c40e00c8110741002d07562644040640e56072a06441661010b031003802c80300060313000380980c03490108814106010502c5284c861303030141080061468014104094442e420b182c0540c954229290003a074500400300055041c0c0e0802c0c03400300391000154840c081110003254200940490400c1480031202e0000b000350050f0020b40018016042c101030340b64002002910120b881c09400c00600507540005642004694440104001d15070f0f00001a08a4000444400a003034440007000307503489010040050241070b14030340d89845010240c40d40400d64202000350b40284910800c120000c1442c845c0130494000503115a9492443c050400801d5034210b456800a0321490002c002000c82c006008440d01c1c8900d90780480025014405c09008201400000c6411420706005600b0208a600203092041c0148100050700c7c40085540c0f11458101c010024a0000c500201e0301070010a80b450982840c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 727600485 1250 727599235 727599247
    0xa0c050c07060f08060114031512120c0106050604050310050907030f29190f0e0a12020c010503040b0c0703022e060f06200106050a0303050c0d08010807090b0d08 71
    0x103000582a038043c0300e80d98420299541d890300540d000c2018455941d810a028800607685a03507040c1c0d03003104054010301100380920384018040c034201e4070680802c00234401041100ea280024000c0d80041e00c81210010705003400c01e008283d0380c0100500d040c4031951110007189146005010480183da08012805400089402e0803080c81e200101c00a200100030080c40103640c0c1540a40d5008032a001131841e820b0781010460800781400045000025070b81c1c2408030701032902003040c50f002c4c0e441944014140c2440d0310010381482c1c0240d000c1418410108200700001d1410b9903810b03072003038000200948070483d0b0700701240381000c038058461100340d0000a0300d0f0b00c040c1d41d070740c4a8506c9a403803805110058554411003107124452003030501040001c07841c1c5102184010380c917800314581000000e440380d44d4000040c10410759070320a1340850320014080b0181d070010300c0780501089141c00c004805500d0710462a559902c644104030104e695004a201d1603540d020401400031b4002c0100354a0301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 727601735 1250 727600485 727600487
    0x161703010b041523070303140a051b0c0607082508220203030922090b01170d09062f030306030c101d0409020303070b040204050604140a0c050c0706 65
    0x10b441400380e00c0311a0383c1c5044880e550b0703100e4094484100010803841451926201101c006904154022400d054035044035100d1481401c0155214142e10b030004070300e9080c40d4800420110b40d40c111801054030421203c0e03002e0400081a981200180c6010380e610f0f603131004812801e45034000d0300841c60b508090054006540041d1280c021140d15a4907507100c0c4401c00c502d4140095a07500a40640003403064440626100c0c10508000c0c01c1034460600107151f00b4100302c1203e040c6101110340c48400d134014071001951554000c018419070004009a98020402403c51281c40c4640020840e10340b80d010414801d00450061624000c2d11040fa800b007003004080c1c5075003080752041e02034811242c0703501261420a203000c00800254540001580c080030480c12203000303600d400c0e03070001d455400460068408100030413a45002e80000c100c2418188100010703908060b090302e11460070403540658200e1103220b82500f00119040025603200c0203041940c06000b91000e00c5c4043c0182d4100080007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 727602985 1250 727601735 727601737
    0x190201050106030b010e0904330917071505060402090a0821070812130c030609061b170a0906150e091204030204021c0609140a0b06161703010b 63
    0x103201c03143c60034401d104e030724401190800300300302805502940480109003c260031340e908020940712004102e40444d04071001c4010b50005c01180641203544140b0f500030711045107034501c400324203688010f2400080c0e4030341c000000c0c9441d9402d00110303901e070701040d641e0362682c1c11101d4001c8090b0181910556803e080c07900c46075055110800003030880b6101541e881c1d800212050300da07028042c40d00f0105000840103510a0081c100c6048a90600c4210040350800740c3e03103002544103100202e0701c01094a0b154041e40c01d0a55200c5008145049940050b40c0002c0c0d039034420703006482c040d003040d43d8000008016103800d6001603e007510700b01249800705055400c00c0b050b10400303120704180740c40c0c480800380e481e40030003242a03803003c1c01d000070700041c40d06030010000392911800c00c1e84160700303c44400e41115156400302556540d140181e0103510031034000e2a03808107500008208200c58040858031500c079000d00c0b95000b450700c8414104000d81160002801d0b1801e580003a00ea40c2c41b00140811 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 727604235 1250 727602985 727602989
    0x12030b280302120c0604031226071209030203030a0b061905030105100c0b010302060d020d0c0906020d08061c0f12030504030e03010b030d050a0207050d1a0606031018021902010501 79
    0x34462a0f0b1036074142000010f0b4880000006050b03207103441e10b10303250310030343e1121141100104206211131450600604200700b26914106441407220304054402034526007540302c0e4865114100110400480c3d004004e807580248a40e801003043c6234803030002030252080c44400d0030201924048010900e03440405103050314400e581c0803030741490301c00e01074500c110744950060141e4491401030006082c0071001d060200c032000409410185d000c00b444007a6002c0c95050310006004d01c03010004a941080900d4452055060110751402c0c200d003c24900c1d241c69010040e080c201106040820100018402c00184c0040140214811404005000d80020348050f000141c1d00c0031480c0d051f14042c4558000c080c4010000c021410500e80c0554070f41d08240f2055056000e10100096161133920900b07034281d2003a24000c201c8a106080d0303101c08000a00603500440051080010100715074908605076091920312041c15200016007038040e02c100704042c01c20130707002d98420f00115015045281 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 727605485 1250 727604235 727604239
    0x2160902190c080304020f120114090d0c0503090603040519080d140f060f0a050301090302030c0105070201020a022a0a061d040b060a03020c0a0807050f0607050712030b280302 77
    0x10041c6040d58121420109031501900181e41003020a006181003002d08405c01400703030040e0024641000a18211901c600d0094814404101041036000c414014514110183d0508078880c117055201d46549005403e01d80b4090500080441c06002040107840f9925100f40d00c1921000c00524001c010381c1c02202004038401d05014441c010742e00c100c8031151040201c0c014101d17441e40d910b0100682d5581114240f50080d886000204243d2000e01a0030100c074041c1e0001c40c0e840d0b910344a9142107901c0200580210f910522044000903408104c11320602c0020320b681d4900e0640d400020410240003250a9202070b000000145030b03500510450b40c44640c04012281120b1500d050100f603035071940009901075010011540443d0190340036000c449004011195a156550b07114005640039032026a5a607005400b245c90202080011580c40010f500c1c0040c1080c8059407544521010740b5405024103407100d21014240d1a00c07400c0e00061a03401540310f802c400300f001380e10041d50031400164 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 727606735 1250 727605485 727605517
    0x51003060219180614091311121e18010f0513020117010e0c071b0303020a02130c0e041d1c180e3904061b1502030702160902 55
    0x2c030140f01480224422a0f5603501d410303249905c0300d005140168055640d05034041284061384500440038070580d4556481d2080a41e99110900c0908245620090500c9400f098910240c11301c542c16031150750708401c103481c515190303003121034502d0b01400d01210340c881c07601d2034802001400c031490144600002d00070b0326000324442480c0da0041c8071820902a421148000c000400d41c3c01254900030240540500080c5004040805d07804c80003803030507130069006138480c031003100551604100540302110342c0d0307000308002003202c41c010f0424581480b0f0503100c1c503602c5240b485245480c2034101d2802c255942035484071940c20000c003441d2040580440f00084e5040d0b1300c80a180101440c1d401a1041e200190003540d6804000102c0d050002031652a0110340600c0c05501051585d2a8840302036001d0705079881d0340c100710004004a1074080c2070005500784014210103d2031000781d405984503002005079032030b5580241a460803001100018000401000c0012180440e0740a0807003280d00717031052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 727607985 1250 727606735 727606757
    0x3070302071404020c1b060d0e030304061407080a0906060503250b04050307170a0206030c09090601080f0a09050708100608370c050a0e04021f0903020103051003060219 74
    0xf1000b00c3c041c002c041c808541c44000c1d4070002d0503520100d180b03200d0340200b206181940c0403094101307441c0da0341d1007410903074404400c0c032040107c18043c083d03941e036072280c110344641741183c1e008100c0712011303184806c210b1b903d240010134130025402140140c4000b40c1122101000740f03038043c0305807117000b542c1611045841e00110b00c0c00514000c950842e20001c004001d0341c1e0800da50881200c03100e248000844c0300702c201650040e2502c5001e1071182560960454803035918900744942160000c05443c10050b105081101c2a555203009580150b40588000340614061415610b068442e810608480c418100c01c00307001d0a40780c1003c03007591014000e803901c800403403051000a160504141e0750000d2129071407075121400c000000300450242c41c118020590b158081201503006400800da0110f00c502004254101a41800c100d03030308004034120580c241000040450025000081c101500c803004100c000c1500d80511014640148046507920294865084c650040031490f10101d501c0d0812 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 727609235 1250 727607985 727607989
    0x70e06060f0a0e03280308130b0702250e1f080105130c0906031101051c0603120305091204050f132301170703080a031d030315060f0d020a0c05030703020714 69
    0x300190070741621285d0101901143c1e8142e5a01c1e200500e68002d042800d14404041244050103a0256030b658001d081240b040d00c21880031030420801c819004a0034210400146182d0001c1c0d5a200b01007181c1d00080d404540101180c3c0030003a0b002c0d01d640e600b080c00340110503003c070b082222082c2c03042d00c581d21074039034968034841560380512010f4298201180b8412503540039100501c400707606514088040102c1c200a10f04882c955002582c100c0a64060b0311691340c1c16110706608840743e00000c00d000c1e0062004200300303101d1801840d029001018184110380c443e41101180c0e000c1c03075503092214000300f0100c401903203103002c0c5144071038501000019003540c0d201110724181021402621156013140c40d00c901c1079200445c01c1c41059600d4074804c0385102241c0545519032130f01d4000e95036a0038070034002600e224130f03411014401c4104018a000d041d02c208c003101d0281c2a41f030005600e4180c81d000c01c1c1c07046241c0c02405004c5002c0003c0c00d104041d800320b000c0003502d0b04040300300c80341003680003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 727610485 1250 727609235 727609273
    0x60b01030b1912050f070b090a1e05060906040504020409150b12150d02060c013612140c0304031203090305090909031903060503100905070e06060f0a0e03 68
    0x1c5240b032001c11046080c000032100300c0c1440c10140c0110b085900409034019410b10704441a8010920f0a001052845140c9000003007680100748050000150519100b640200004030b0701c50309200700d2000445005036200c3e4420f45e002044028011034403290b6a480d00c038068a4071354281d02d0b01c82101100410ba02c17420100b40c8010000c840950310b21656881c000820a4905904150303100f10018403200042e900e840c001c00f5030401740400410714410031190071926001c3c6125004000c1050441241d004000304002281250444401c56054005030004e68100d401182c04d0481014000b5240400b4500000104111303071240b10314002c50624804124202c0b40c0e0308a00400064041220303070201d107000d108054106824409503458210b418010b030344082452409600402c1d140d030340411482c83d0510401303150440440c418003101c1d20230755803291030340c0b40c901034054000e0a65003c41c1d810f440c0c88040c1d56030310384850b100c00e661f100140702c00303441a014900040d120b88143e844d400b20b0414074070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 727611735 1250 727610485 727610509
    0x13180501031a041104020a0f0207080c15030c090301110a0e03010c05030a0c0915030911090403020303070f02030f0703030b090a0e0712150213030203060a0203090601120807020d060b01030b 83
    0x20500014106002d500c03025888019005880d00790841d8402c2006503030303920003000480361030b0300c3d204410140100068107040d404d90124685030001c200701c81c003d440b0001e040f006140d41d950356550342c8c1e5654940b0700d803030702900055582640c80d2400c108101340040c2c1c0102a40050fa48a500c0013000d1b640426090712111000200011010300104443d04140d400483e40b41c540390604a80b442d8540080c0c40c3c3c010070315400f01c0002921265908148130f85907008142c01071003503406820b5407074251400380d03403031102074041e034100400c0941582c0e2071403090090311a814880b06526564040c0b40c10000c1c050154001710a124515080209109140318854009000401009002d125181070f4250080b0f2540320300944641c810307072002c9400b4024038402480b8600702815400d40144c21801171518013607009002050440c410014402c0da0000010440d04481c0039030303099180b846d5503107440030260045001c0203400c000040845d404021494001488110080c0d070100101d5060501f003042d400e0803d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 727612985 1250 727611735 727611743
    0x6071101022b090f0804150e030c0f01020f07080106260a03030513081c180b0f04030c050d08090d02030a17061c0b160e1f1101021318050103 62
    0x4500005644036a41d400842c1c40381c0907000007503400481c0c48442c8500350061044411003800601440009007aa801d40e01c1c107811444d2a03c854031040c0c020179a109802c4c2d04075842070a00740e4400030341e07030704c200f00480c80011a02e0642e40301c169603001d01d13030203040c9030b00507035400c5096080080c0f805054610241170140003000104900c44590310b00360020a4003504520354041d1442d01c030b2020640d10350080503040940d40c042168100c1c00481354084400c90b42d403620110040e00352a001041d0644545a0000342150302146a074449113402c1d580d003603900d2070040032401442030040031a60840c803d180b050000f0420348090400c0b68034220780781d00c03981450001142580718140000c846003400541c0c014405840707400040c40452419101e41c4503558100e0320340021900b04070b40e041141c100118400c1a9042020407030210300c0010380070816044c00d9401c0030944075542102c0e54803c1e0b4054030202c50203802103660740014055661501c810b4001d8421004040c61108402c2040e446050304803508 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 727614235 1250 727612985 727613017
    0x311010b180f04030207230306160c080d090b1501030c0816030f0b03150703061d060d1b06020a0b01081b011d060f09011707120209030703140607110102 67
    0x101c1882c44641c150160050f8214801c0c202c01140c041d580700c17041d0300d0b0450070841d20303c02c0d00c00c0007003054500f2000515826034a01400c8800540d40e820201b03007400d00d80d00c40394094031280b0510704c0000500c0d200c440584120402d02c140701c207950f803141501e55003071400c2e60180700c914655002a2010001a80d2889030640034044540314140301e41c2c444400c5900a001c081100401400000e00c0c07c12000d000380ca81e54295414070080e0394041c0302d554001d2485650718070324411007000c403140a00000380f03240d004e100e0600d6a9003c0091080d40c502402e81050541040c460312500b000350b4030308102500b114640118000802c12050000b01da42134468110032050102501e5401159042d0198011000d031060a450803d60b03a65460080c1094500c94010944c861070800001403072000350250200c2c05021001c00c0c4010300d5800b0360054480c02100b07602507600c079207040210f480d140c810ba00180c800380e5a10450440d001b808941e00d030164005c0e5403003800d950b0180440608078410010340c0200048 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 727615485 1250 727614235 727614241
    0x60f010201060509130201170408040f09050c0a0305070507020d241b1809060b090406170a1e02090109020403170c0d0e012c030f0c130f02070f0311010b18 68
    0x107566030712400082c8185030007023541348809540031048409980071101003901007418002c64100c162004020020300c242070200e401d120081c81c05900c030300a450000c164992001400041c040e1045a007603c0d0f0252805003102d01e03078202060001c91440c0c4a21607000358211441108080f4007650400c030b2406000c260140450002c165506845440e40c0320003080b83d280c0000e0070018501c83c00e001418456442343c0c2d242000c00c04c01c021114203401c1001403003224540320b6100c410009002040780d6000c044218030f24980c81c0740d01c1140400501c001e40c4500300300c00100e00107015401400440f44180a0b0700301c400f6011180d840c242c040c4803890201a0300002100c00c0840c0300352000c103061001814085401c5c481e0038608200222617400b021615031b500304000c101400c08001801e40e514409025041580c0c202002550f83c0c41d1401d0b584079000d803a40100c05001d2950f904441503103900010031120f01006203006450344100e01e59043c0194030b402c840d401e05003001c600000d80c218140b400e6000c981d0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 727616735 1250 727615485 727615501
    0x207030e09060d02030f07031205040b0a080a0f0e161a07060c03110c0c030f1c030203060301061203080f0109050609060613081e0f0d05030105061b15060f010201060509 74
    0x40700280340507441112a051000036071000c0c0714a03aa0300307041101900f034603400c0d420002c1501015079441010403104200400a0080e44002e4551b1700c55186402c00080d26001d084002a103582e02c8441e0b030007850b0440d0304141c04400070b030360f00400000d440c3c80c41965503110100071800c030080c8020041410301700003020003d07000f035000c40305014042c200000d211407980d40502030350700410480003403588951502c070140d00d406c0000405201e000c0005159034517200c0036100d40104d1034020803061513000b001150581c3d0b030a4021002400504141740740c2d0322500e040091600500740c0f10031300f88a03641c1001264a1079175005071482100003412000340791704e8a10500101c0c0c1d02a50002d403080b45d0b0002e0100d03030318170240a03052003180702d06020085008404001c81c02c0c101c00c0701c00072140394400d090041c1416004025070f41103420440d022611006850740144410943c8000310982d800744102504c1500c29a000741d90240c40f05460411380030260b60010ba003211960b00510317a003c2244c0001031400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 727617985 1250 727616735 727616749
    0x4060512031b062206140c1c05160e0117092d0a03141e041a040807060f020f0706050403030912050c0f0301140405010b04051003030c0201081503030c1f0207030e 71
    0x7035071150b5800101c514056500c10301b07010096581d0b082181c000105e8488201c003078030111501803a144410841810110a65120b03080340c0d0031054244a070081c0d000b242030b801020313903440868101e0303901c0001e803071b050103500d0b01d03103160040b841941c48143c02035600283d00302c800c500030a90320b07600038021494152026580000303a9160140384120401c5003010500c0c1c8145014043c080d844041c0f03032102d041c080c24441d0300d100701100f2103c80001340010811001d00088400c22950541007590055404e85022400c2c690784960761501d6201314135000880541c410010001c980c0a40c0d03c0c402100d4461090020003a44200b01408903800080b00300200c1c5400d40c400c0b1004040100006101d500c01d52079100550000c0760181e43e1079555501904550419008580c0d0100c0c18090306501c950555501500c800700619000c2d04010400740001c11600351480c000b07c444000400f100c2c0c80d550b07402881565510442e4a07102c11840807091015a40810f000390b81d074156054031103040b0780c0c25880070f00c154 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 727619235 1250 727617985 727618051
    0x50105121923011a040b042a050f0a080403120e0c090c091005031e0103020d080a0203040e09030a121109010c080421050c010c0b0604090204060512031b06 68
    0x41e081d501d8202c1c0c4980c10244548141082031100d40c2c400400c4103c2040225030005160358007450502c02c140d0700c0c04070607001e1303240701c0065500042002d40e40064125204c0c0158240c102c150900080c0101c61180c004400500c218032aa543c0003620b4407a50f0500b05568480744046a564403c4d41c0358403091a00c5140203910529024070a42002c0c0103030001030102e0010030384580070500c00000c1c0149104d0081e800e1101002d8800c0310b000702d501d140e011415040090801401c1c01c00041003018800d4400e0080758010900b680d0100f4850074604612034036075100b244044082074001585d40302001080c054554000e1580c00d0090421b2952001510b15006400d401c81341c80304104404030311105425244680d82000100d6280c0042103071800b6842c0030031010110703040c01031030040f0b113002400501549910480540d030104540b0600e01c08100601001c0d00040d600a0f2180745d20350040d100040070300b4074414001d019045454a1200c4035880f100e058500e00c5906a001d400f54408030040c0c00d80e824 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 727620485 1250 727619235 727619273
    0xd0b131a0f06271b0d0e1204060c0807031701240206010614070f060e01051f05030307080d0e250e040c0b07051002070614070e090a180203100501051219 67
    0x31807041ca03070404e002c1c60390280c9408041700c4d0359945d40c3d8030003010412040d021261380c11400c2d4501401d04202030310708810190010f101c910005034007401c147c0301d450010001ea04801e6800b07010758403a140e03180c11000d4840300818241214001c00030380761002031202d04903051911b0312144103000301c0b400701440e4001d07101920390810348529000014500d01c114104500b4032800061039040205003401c5440013040f00c0000280c2502003808699004022076440644c40703070043e91b50300381c0030201c02d01034078680c2001040d5000721128442010a541c034008500c6403c50044d001c00758655003440f00d581c50965001d4224041e916003440700804540041009500800c1100d250040000b01f0030241c0c0c3c05184111241070b1a101a001800d2440c40f119030401c0d82d50500c592204d1851021801880c1e0081c50009072a45494a51080c0107c030911111203a0700642139a084005164803c0f01a100a20400340a0215041400404840410410204592000d80021450350383c1c03109001c003803495100030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 727621735 1250 727620485 727620511
    0xe010201020903030c0109020a1e23120703020a081504080a020c0a12020a0918020f0402041503090c0b07030c0f02031e0a05060f01050d0b131a0f0627 66
    0x101c05903400c0005c0e01c02c807030b076032000811f0001036031062103c3c61790198801c0c03407031660201400d0120405c0002c00426074a01c00f40805100054450080c0180d040301d2009400c14044230400c180d030782012038080240ca00a0b6040404580c0e0740400b242d40d8220f0b020308646600102c0041000078554200410a122a610456200c240e5810020f501d1011039400751070b101480400100c11410401031100041400a0040081c000c0c9909519014030114030024840c07410f101c0d0000a942d1580d05560141012840900d207030328100700e000c2d0040550210545180103508800144d9040c0c003001c48901d541e044d0b4403402c8030f20f4150782d400c0000000701c0c1c0c12070b8507004083c44804001b00840d07016140309100b01c003e03c604261400d140781445405010f26000c200c5e10302c0144415240c00d070056002d50340c840e401400b15070361007011a01f540c00f0681c00034140c40b0040b100003c0c0c03006807907406006403810000145152242c100f0441c140000200c40e183c0c8a245c4280040003500101c0708650041c09840c1c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 727622985 1250 727621735 727621747
    0xd0b03030a090608070f1707030e03030a0b04110a020304050603130605040803040212070602120a030f0e2506170403120e06010f0b0733020f04031515060e01020102 72
    0x38150340250070020009940310004104140d070141d00e01d40c01c020035060407582d10341781c40401003410040c201c0c003a0054081c6030110f04001d00c2079000000202d00c04040d284c807130801071420009040101c842d9840341c0c1c10b011901983d68503950490303c038a40c2c6034004500c0c04e0301c0c15040c05825003004004950b903961204550002c1001030082c0f0344511b2154002c507591f071919204200c156038205000800036400301c47c090111a070005181a0780c0344080d0501c64442140d800304401402c1c800854298481c10441d002c940da5800151804560b490f03650050000e84803203c0b100380540039849840c0009589050440c403201c4842c80711900903000307242803034548048000b00015141c90348044100c0354400c000400c01d160103500355001911160101500d4503030f058886070300f9040061701500150806600c581d900b90001205181c0703062104500359100c054030160003005410601c81942c5400440000c049039070400e00c42c104902003040c1e99101100d041420445201e0450f01d00e41d410340d0750030060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 727624235 1250 727622985 727622989
    0x5060924010e18030403050c1516062c0606090106050a0c0609030921050c010f121a0d060e070603180b0703060b13050307050d0807030c11040501080309042f0d0b 71
    0xf4406580118002c2c02403003aa5400d018274001d900c40c4a1024001c28401e4041e91801c40504944080c1c000101040d0300200b03069601d03076560500d200e0780d0105001d8001141c402408510542b042d2401c4880414070703a6121820398482c031076001c00c10000b40f144005070300003800c940e2110242c00c0c040d00d030500a00d52950889048400c5110016201c0e904460f0101e040110401040181e80b100f8a4a071003d284003000140c088882001090255619503d08408031945200c1e002400100204059011459414800002c040b80c2c40b6044071401205004614207000c2c1c06007a1045602022030406c44110b42c0300c41e1500c00001e000300b002c26846490004560b50003801905a00b40042c1103410000c0c50101003500c0c103174884d84103d028a080c2010480801c90b42010748441c03e41604011031000c500e4a8680140320000704d40e268043d01d040b0000c60b03071010001c05410592019070342045600b00089644068186240b61741070700c0c40098005030341180c2c4481c050190100ba1a030046021510301c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 727625485 1250 727624235 727624237
    0x2010b01020712170c0a050f03090a06030b0301140c07050c03061e090c090106050405030105011a0423030a06050a0b010804020307140f04020a0f1202071101110c03060405060924010e1803 82
    0x5c080d1000703511034460b084c24400b0600050002280c0d882c011450f0200c1440401c51a1805114070414580d4440c0d40400d5a00c0a400440c80030407031607540200d031306d0105161030044c1c1001100340c8182c4524001440c075402c00041c428050300340440c070064031a2200d01c03149282400104588071a005103200003000da200d0b148101d010f422242c441d503443c6c90411092600312441684001d07141c0c030682401120280074101160f0a840e20702042c0e1099002a070018000010300d168120381600c200b2040300301b4001d0a41c000c9015040c451014040c04422800450701503c058030040d50580080c0c0e0f040200424869480103400c43c05000c85d5036440c3c0390000101280c018085100c0800c1c101d42c14004501d600407032040c0c00440c88070b030071401d003c071588561034800e810680d82c80c1030000311030302346000c810208194114101c00404442d058507240c0b42150325800161031102241c85003d07003c003151040300c2c10b00c419200030424440a1070b03180000650310210041c1900560741c02d00c20042c2103580c0c0c140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 727626735 1250 727625485 727625497
    0x70f080a0c0302040c1b14010f06051c020d08040b0d0608010e060c0d0e0718180809040b040f0f0e0705120c0405100302090106090509011a0d050612070f090c02010b0102071217 77
    0x1813046041f42c0d48441c3d10380d00b5140c4050304100b04520b0b0030320a203c80ea5512609420301240d4031a5a44807842e6480494040700856501900088000c01c00084148400700241102050001c06008256592404c1801e9518644980c00703942c00920010b0000c880d240040c145452480c0c1c408134600031642100303400d000c3d260704002a10000c1100750700352200940220b4400942140e881800c0031410717100cbd0881402514100d521558840b054887c40f5a90364021000555041408000458030610080700800b44d103500e80b41c0a01940500040d24a03010300340880001d5804058030b041600c0104010042034000c200300200e40d61541c001c000b50721108600d40c0038040b242c841e400c103242090104404100140d01c1100104241c076501003011039841c0544000d40c51011000c5444c6e107602001452030900600403036a01d110b106800561001e240f03542c03100311905030004204c1140d08034412400c3c0c50324540c02170f0250f40300800030018222041c0c402c8200794010b40c504103861151304028012507000e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 727627985 1250 727626735 727626743
    0x118050d03020c03160303082d0115090801051e0c0f071a0c03040c0618030615030b0f0c030103140a06050a141303140f120405070f080a0c0302040c1b 66
    0x10350f960440c1c60804010503803880405102c01d42901e4035555004184550041104480d540100b9600c45103030b41c03120203564004000301440400c0c0d83c4504d52481140307070b280043d070000740141d00000f070b8020b0184100b50203410800300c01501c407030703d180c5006450000600707410700720308040099400d4030441e9405070020611503e0001c1101d0f0b01c45040f1600041c01406d06034a04030108240000900358003641011205c0d14241030741d881c10480d0f0709003010b00c6154406410682410540040c20b21003810210640f031140d025500c050710389111380e1743b00d69021189546115030400050000c42d038001008661622803004440518540781e403000140c9000b41c4842c050b086d1500c10b0800c8034a10407955a03804001002d41c820000d80a490013005103405222070b20700e0100020f0003400c00c00c07060080321000340d040e420901090425141007642c0355258441d48480080040780482d5140c1c021403801c810b543c000070f40111480c00c43e02000001d001c00380d0f0741c40a102c50018840581c6001d1100702003802c0c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 727629235 1250 727627985 727627993
    0x6040b06070b2508091b0d02090a0204090e0601032310020f0403140a020307090b060c0601030c06180b030a1515080403020613021e03120d0e011a0f0118050d0302 71
    0x10718105400c8401d03c400d2081031120301c008001d0200fa0014071681058292000030742c4640320600407968612241d81c0207900008078404010810095800a00480d0207060b0108503140017045003a440f40002e02000b411414803080b011a80b843c0039070f24605041c00c2d03a054618100f20390030781004980c440389100d1109500441c040052107100c08070076180c0c69054018121014083d40003a0f242c41e410b0140800712a50345c654040c2d161201001e40c0c01d8962040c04840325540c690410340c0c0c0040d42d44c842e0a00242c0380113402141c1c0d03000070310782038129441d201950342151036103808140503103554100300c03201c1002c00c0000540d4920030b00c0c920301042125182c06400741440d0a0090030103400500c03011107440040901c20058444011b408001010302d400a0f44105c0c003800001d082c0045480c55184c41403012030401e00424580c0e0140031900142002080784201c2d9a040c1054204200c81665110040e80d05040c2d4039406144101302c981c0e94503000f000c000e42c4510020701d5482d9464400d50040e44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 727630485 1250 727629235 727629271
    0x5030402060c121b0712080328090f0203070501091503020d0b041d10114f09140109200d090201030605040510230901030f02030d140306040b06070b 65
    0x24080c40480003511040d00c0c1b88041d00182c0d150013071f451001900c500e5006140c1c1c0c42c04210502d004102071440e0b4401d0b4000d003e2402c09040914812a401005030b100340112000041e0b1503006e0740400c403c641002c2e894902030280b41ca410390080d000300c0e05c00b417a1117441d56003000d4140d84503c00c140241e9601c6084440e4804515646843d110a0b102441c0da01860b0035118111540c01400380d6441d891201c441c445207803900b11107070540725510503440e8404104054007000c007030340c102c200b080f03030400d8800c10510342513461a481c0b094906009080600c00002030040c0302000060b044500c0c1c1684450b112400400c912000c0b00300e0380d0007110b00f90039a607583d907520000c40d81e16000c1c00005060484051059050050007460100283e1081900c11a00110311000b490100c490b08240742c8001065900a5170350790030803c29003d510f40d012882805049907120405005803056202940740c0b00b10300e425076a644042c4801480c00b403450690040c0b06108850024007100c1c840c0d0311a885525040c0b030300b01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 727631735 1250 727630485 727630537
    0x230d080f16120c0203040f0b04170606100e060915030709081c0804021201020705061e04050a02010e0a0e010b04080f0d0512131e031101090305030402060c12 69
    0x90701d151820020701c2400410a41d00240c40c03030451050420004007a03000c24000e030700e0351240398410b80d400d101d041c50024141003540d001c0c1040b41d011f0f0002c10700d07082c14610b006464910450340241c0c40040704014410751342c0304840c900380781e58001e0507152a11203400c0000b20742c000400012840104000100f0802c40c0d40f01e6581002409248014030012030390f480d150342e43d15240d80c2c0c1c4d4400c02515038001006e40d580c24001080c542d0301c000007150b8030303840c6007007164840308126100702032414458665400d200007811443c0c410b40e04072002d044c41092607801140d00080e0904840d600c140c12610105000780b0080406000b0100001402c1d92a494202d140f424004030311140d04450f04111180c1c1e0415800104075020050541c224000c966100300c0f846440340300301c10000c3c00c030f104c0f11018440c0340340d403a03400d51002c2806600c5205200d0141c0c440c441c2130780d0780d4440050005009002107001814042e01901c5884074440a8401d406440300175140310b508100c403440e13030226003482c00355081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 727632985 1250 727631735 727631761
    0x327021c1a0c041e080106150203070803060102070b0706051501051c0b3606030f0601060c02130903030c2a030e03010f090f1202010605060301180e0d0e040f0e0a230d08 74
    0x8c5c040307200074150501060307a0203074481c050480c01600310271000002940070303842800040098502c0001c1241c8401d12424000d00918080340c2e00c5104008a00030b0002941c0540252003900f45c8046400ea0103401c491846000380603541c03c59078101070310b0141500c8010301c001e05604000f6414882e02510100b9a8504c44c0f05003000e00054003e812078a54801500c40119031207040d80e41030300b00f8442d206283d10200d00208041d102020040d03103020440c90401d585a085502580100d54480040d0541801180c03100182004d0022843c0c05c8005981300180c001c19240c2050700000300000746140d6088401d106031103401e44112000040c2c01d1085040014201040d0b04500790380c4000c1043d94103140c04030722188818020038401c9028010b02c480e050341580c01280320495041c041d00c2440024110240c401c5074203012283c411400d18000300b000102c139100e2500005c50920041a162095460b099003c045022044005100f00c0480350790290b420032100381751030060b0791035003c6880d05140345100c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 727634235 1250 727632985 727632989
    0x4090209030c15090f06090d021c06021216020c030d1b0507091e0501060f0c050307060c02160e040209040201111203041a060904050c100327021c1a0c041e080106 71
    0x6c6203100340440784580e103402c80020042e070303815109400984a41d204920840207541d40c01040c040c00019404a05244210404d0140c5100403010300d02110320103059844240214841e41c1540c00b0b8050104002d2003041c103640751401c43c94440b0b0100041d915a1800d1080a41107108210740b50480c5410140900e10303201c100c50b1041350100800c0d4140200244107051400313068080184e00c1e80c0a205015003402160269a8001e50421500701001c001a40342e103c1c0038545481c00c0704000c070008110340c882403c6d51095074000c00d0a08956119401552600d600c0d4101c0302c0c4610070907206503c041464802140694002c4004204901d40180341c50036600008020500582c100030500c0006400000c900200d4503013152001c040c075900e048200e0041580b81d0aa189841c00040140a0080085100c02c00b090090329510305894281d80880e180d01c1c40184010314200b580205041c0c44440c000695070001c050704446403030311780d592910b40d1040c3c01044404006004090041013050824421000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 727635485 1250 727634235 727634239
    0x121b0506070225060509041407080f01060f141b06010810050c0705100c0e03070b07050601140a090216061121360a1a0c04030804090209030c15090f 65
    0x2100c0d103c1038860442030141d102d144240308020480c5450381e03450740c10050441d006500824224600100c00412840040c0d4241e46e0381103101e4000701d1070920503803501c00901d265490f45240302d06501d1703010b003ca07070110f2800505250a0599070300143c10074000b1a00134102c100007080070104200c070301c3e801c54001800c000380d090f408108440000c3e502094510259030100c800080c0100b04510584161466004196050083d50300106040c5035260141c0141c5000d803040719440d0b0780b92607101c0c0c0e4003c02e07480d216074480382c2d480f000c0003051082e030001c05c0404125941c10030062903e9039001c0903900383c81d00035001810003280c1c500e0b025104180a8100c5a031760b40c15103440d800c14103811100120f00b80c005030140d0301d481540c09000002060340390741084010040318041402810008c4010200c400c000440c4107800340410350010f0802c0071346040d2030300001c0700c900d003a15044a1070003d50000036101e0f09405803141051050746e84030403000c4602400e09045a5840307070541041032040d45113025034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 727636735 1250 727635485 727635523
    0x3070e0a0c0c1101030c090b0307020f0f0f0616030e0709020316140307030b040207170307170c03010510030b030604121205040c03020603040212010c020d0905090f04121b05060702 79
    0x2c03000c20110100700e042c0407001e0900051400700c400301240d503c0d4142d048103040e40000000d000c92242c0c001510501008101c007a29000a518110f0540342e1401030031a469960184000c41d059420680041c0100c2026040015082c022504100d052210551120390826408020498110706c0380c10402001e0035507107044040c450884003040d10030b000c06016603007055524404219151144d43c1180d541e2071b00849000403040b00030504280e140d03c21986040003c2d440264000741412300c001250140c200010b0746811a8284010b102c0c1100e1864004003c05444070300d40780c1240c80c2030021a020710b000c1d8403044035401945401403d58130012503441c401074a00001c01000c501c01509a60039298100d80305030b5242c68900005030f6900b111444100e0a500c0d0038034070b50f10290000b40207180c58100c1d403216508556114100428503800302c41d003c8200304034000050019007200c0c0320b85442e00036801c10b6103440b0940801202d40416802080f92030b079024500344000c03a43c04100c0035072002a190418 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 727637985 1250 727636735 727636757
    0x21606031a10081506091203091207060206010e060136081906110f040b13211209080706022d1203040c09050c0a08010b21100503070e0a0c 61
    0x90824600401c40b08a110741800c04c14900d035100e10841d030f00b000c1c000707140a944011540283d0b031254400400c10b449000703028000800300340c01042c05011164150003505a031fa10300b01d20720301e81c1d1000400323440c1000b540e039840d0401c1060b103010303003021003801561401d140340240b080d0540503030854001e11a41e034400c400b801010b0011540701c0d103219610600200d20010000c1c4080342c0703801071130226400c000c000710b030104980020038060400c1e180c8602c00800e005c1c2d5100000e000078149808014040700198010b9008035110a003840000456440d140c400035030788684441c10035140d500041d0058006014002110303200703119030001149465005100001070040e15965240501e6541000d0080400080c06000c0c07982580802400010070134403e03403a003410b425180d6030041880ca4045020000042003d20108060758600300381004a030300303220b0f050072101410500003024901c00b000b0b1041c000c0f886440502820b80100229045440725003017490001058400380e1007071200300720040d682 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 727639235 1250 727637985 727637987
    0x30807060f020d0c03050c0c1b2e02070b0702150c0705031b03010605030c0a12060f050103080901180513020d09021201050601021b0627040c020c01020d08040c0e07021606031a10 78
    0x140c80302110810700302c60101144c130400709240c200d072b4017a091341500e800d0142e041e0311260310f01c201c82030107101e82c2039480a94407400341440a0264003400b075086840d042658002c070403940000c0c15030410600441d4802951400000c0c501500401c0004044025003003010f21800e0901440029100c11000313408040f0251010602081345445a02840b03030700001d0031400d124090b0300040c2c1c40000004148602d40c4c41b403d00313040c10307400041c9140c00600140900c94a003802c0d41c08010545500610700e040d00031a12002101030f400c4000d84c0c0c0021980d5888100c0107039184505090b45000c580004a2a842e01d0b50000e070911034005c04402c01c02444212543d0720ba46d4903011181b107808042c03900101c02c030459660803004071102000741d801900d042c0f000000315400141c0061190400da0032105e0381044800b00300c803641015280103010200b903040c1070140c8064200c009903ca44a84100c0c0d1100c0d1081d443e2148807201c950107800443e40d140c1007a009801d940e54110020302d02078410365103003e10800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 727640485 1250 727639235 727639243
    0x306041404260c101104080708060714090325090915110a050706020a111f0c0f021b0402070b0f0906060d05062703071104050105010e0901030807060f020d0c03050c0c 73
    0x250003c000356485a506081760424019200540312a1089502c02d41d20303080131715682c03c41030b100a408601e08088030b0141001040440e00b4809015014000c1c0080080c0e908000c4001c0240c0340210211450022900141900c90406014000e104910502c05a68220022680034401c0e00701401e0701000440c01d016003260072101601e500a50050b0b507a8402d41e801c46401300f0040c20210f003070058a24102244030154190110401011820040d61a216801795081c2c6050150032001d40c01c08104204280c402040340c0034200301c0a0005842c243c8181d8a00e40c0c03042045941c0ca04183e8800240502c0c003500f008080e40c414801d40b01ca4000500544038681d44010040020000c0c006c85130091b105181030111301c4505a02c10300c03c82c1d80f070724104d01d004941c2c00c0c0810501402185050000582903124480200ca182400341c94401c1da41d003540c4851f2503540c03000c0c00c00d81c2d042e0b40f5000c030a68560360350301c014000b1409140c40000c00c4840300740d0041c2601c00140103400000b0043c400800039820200b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 727641735 1250 727640485 727640503
    0x5010308161104061409150d0201030e01060f061107061d2202030a0209031b010807121806020702034b070621060b0f0306041404260c 59
    0x81d00740708109402e1800c000804001000c0c240c0041c2000400a400d560368043e05820a800319500c44181d0b0720711501808110f500c200455001802422940c0036501907030003c841103112800208072642c075400c00340305030203555105c0000540001d50469403c0300602c10000544038614180312503c4401098079103c0001117016481a0b10208614103803a1015001703190b00828020b0079510707031800e0340804000f0742102c0d52180c001d0154182801c07810280f80d03407440d417143c0705840790201600c500c4000c0701c9140c1e1031580341c03c1c0d0035551845035801055000760030500302e00c1b411000d0f80d54086881418100010b005040c4084401505280c002a004903005103074482c50702e440d6410141107040f800c0d82e14003220f107a84258010f111010808650150400420703903008110741900501da00b03503010455500f4841c64001a02c1407001402c41d0181e0001150085001440801d81041c44116005810000c0d682201d555000b060310504220740100100e149003415120642085190790240f03855410304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 727642985 1250 727641735 727641757
    0xc1b0606090a0c030f0603060b03010b03030c06070309020a080303250302070c0e0a0204050405010f08060106050a0909050c2703070605070b0408070614010803040e310804181d0105010308 82
    0x148401036045131182d4440010300200417420f20036a03541c1d043c040000c0c411303c140c0342c0c029420003082010324100001210001340b03810004101545c0c94031021001409000c02c100d07801b2000d40000510020104060350061104116a440104004c03007000840d80e03c4441c68002d040c01400200c01140301c482e04c540c2185c132180000044ca61350751020100912450700300603482440d080001c6142880c9405003402e442089040303a0407039888110070340f184c4c0103030300b9a40c00180b4650740034441548281c1060340c01c000c0120509081c042d00b805a07421101d03000e00d0400c60100449074040c0140307410002c1030010525401d0140c64240c560f15200d64032040180080c142c0c520019030482004096400080c030448683c45040c11941c44902c600d80b05d910610540e045071006030301240414000300c0c8140d02242c020f080d1541c1c1b0342a0705001c2d5004440d0384d03a0584603202c05001c0003600c0c3c900d5034500c0b146900040c4001400301601c1511000080ca14002010b0a030300d00001800001c8440b42110b410081c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 727644235 1250 727642985 727642991
    0x30318120305090d0c17030d0c0206010b030a02070f060e030c011506050f0c070b04030317060402031504200d0b0111060f0c1b01060b040e0f04020a121a0c1b0606090a 73
    0x2a0800003000105a441b240540024410861049001002030250b074150a20280301e00508220200c0e51144280220384401c0801c2000c41c40c10440c0341e005210703044c82406515181180c644035041182e25a1044480540000a54500c82d01c0c081c0325842002c00c030f801c075a0f2030141c10013100074000d000b80340c0c8184640d400081c405039142c4080003a44003c09104074100c1e9599144d1a0043c08000000100c0141c020031601080c211f1620340207032171154000078440c440700e6144004000c0588181c4881c202e407000c08502d40b11401d61100c000b4045240d024002044154014000400d1012444880c1c1000e800030020320001d41506400b00b50050029028940c4a04601d01c0d942144030012010b040150301c1c044c00006d07a0325080c0058811a4082204004541d5440340b068105031012030b0029400001080280910b500b01391621520341d0180100c2c04d0032103c84140c50f5500c1d501a24080041c400229600d141d10050613280340e5090014000341001d1308010700810381a85024001401c500c0e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 727645485 1250 727644235 727644259
    0xb042d060b0d1413200f040614130506090a09020604090606030c0305010b18130e06150f011e1407080a0804150b01140304020d080403031812030509 65
    0x50180c1010000d04504800140c1d90380001d200a0020030103c03042214044900c000a4404000c000e80141000d03080501d1203180d66241041d9a98031000040899100441c5071030f2104a44030791044074041c00c00d808a101c010a0004100301081c0848120222003a061108115464070341e0102c26130400010a00030450350200d01c001807050041da0800100b10b8039040d80020155410b410016010708552420003003039888804140161041481c5028120050f80300c500b0ba500300900c581c410608481d40024175001d000103400d00705803003074440c0d40700305803005006107940c680004901142e601c00d08003040240490301051000e1a00320600e841400840d0054810781c54007030044608840d030005855658400c4040003920b042d8003a0f50980d0900b0584c50501000d078200d2051208080c0140c603590701c2864a081800c603190310041003203030030864a602c908006075075180680051803103610f8103a1030b481c0187d901021140c4503030240b4624408450400003194001c02103031900381d015180310780317404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 727646735 1250 727645485 727645571
    0x6061303110604051509011416140c0d060609060f081207110d05160501030510050402070507080312071812020105090a0e0c040e011e050d0303090209010e0a0b04 71
    0x8043d40d072007540c0040344944200d000c050740030020040150709882c0c180284410045800441c010400c0d60090303a070004161310046081595181006610303801118204200346002c120311280200d001c4400319110201808203070903900070800545581e204e01c1c00e18500d0302c0c1d001552201044601c44031100f0001d240c10a2060b4050561034581000c1c242c80c11f1700b4a40d1404a07590300c8041440742241154120105080d0700c42d01a82c1d00130000701000028030790902d01040029809042c0440d514452610001a0090148090705080000301c45405451400c800301a100c04038000072100850740004080c0a443d20301042070442d19020b02e049611820b095001c40ca03198195080700414503461410451041040001002640c99016501c0400c5e661401c441209050002215010700c600907014821410700c41540312903c0e0181c50041204a016004510050320a8000100c00e00d0480304000c20b11480e801200d16200054404000c08400c814140600c0302c11a141d1300c03203205809060721145 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 727647985 1250 727646735 727646737
    0x3090d0f0309020d1203050a05060618010c170a11030406170a020705070801061806031e0c031b060e03060412030509031b0a0201030e0601030804060507060204150201060e060613031106 81
    0x1103030f000d01046118401401c110801c81700c1c12003079000090410b000034014241d01e010b503a000d00000b41c0380f2800d1240440c844013001c1540210181004841c10380507010900700001c501010f614503405664030285407400a10728020f008115030203034000c010801c01d03541d100031414070507404c0c119a0341b2140c40b88910b80010f80300e464000b0f48944204c40d008101c1601c19441042140d00300b808010103034414821100c255203440c80f0190040003940b4148044c490003a40c010340c0e01e4418940301050a80303075950342c4030a03510490300000d600c00c8601d0500005400240000c608001100103050030320785940d0360000020012481c40801d0303140c2d404110700c40c0e810000d83d03c1c00c0040a1098130110105c2400390740e110b42807041a03001a040510040d112680414010306807a0040d8546140504281040c1d49550219030b00b22162a0b003040001507400e6030060003205c8a00c07513400071034040d01d080b4040c00e080c00003600040c415001001140000c072100074480040f282e000240442c003008900c002552 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 727649235 1250 727647985 727648001
    0x141e0a0b030f060108061b03041707020a060e030705090c0910050d230a0b030a0b060a03060501030b0f07020706051803070f170f0a08030a051b0406020f07050603090d0f03 75
    0xd40304881400100400108043e41030340c84200442d0820350364090b1044504c661001d101d16804000c201107004105003061000120040d10315942ca4903180741d0204078044c05c10f40c000b01c00074500d00845401c030700c0d00b485014000c1c0011900040309050120350314045220700d40a8a20403403400c1c0342d050415000760103a440e5003032031280400c01c2620405420583e8210190348203811460303d8006a068041751061003002c1d140500100015842d641d1442400701d0082e050300d03030180344454000b00003880360086034080e602ca2110422182012070fa4211801009414881507410035030302400f0b0b1940c0102590b505400c6a401000106490b40100b07080241715080f20000c91700b13000012600012074090403100c04400720840d03c03980440c003203031074451410f4800240300c1c00082010403401c80198000c0e2740c125080d1800c01c01300c10710340000842c84d03038040d0f40300b5000350300504200c41a41718140800c0780140000e0320680e01d10b01d8403501980e15049607680315002e0001000c65442e80301d01c250f05c0401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 727650485 1250 727649235 727649239
    0x703021201020d05091203070c0606210b06040614010e060d050703020a0f030c020304060c0212060a0f0605040b0303030105040903110102130e010b1c1109030a0b010801141e0a0b 78
    0x103000c0c2015032060780070354009501e40312a2414040030a503041d0000440000d042c922070707060b90a645407001d04a40f18469050140c0700161548000309618200006d51009940756151400d5a00e200e03141c035040042c03000340a0340c0304e585402d100700020b400c511700846c04040c0901e0140c00306900c8900040c983d0149104040c001490981040390098043d4014001c4103c40c1d107c85c0110511200100c00b035030142c400401c0103030420320007003148a005080303e2440174070050281004902200000b49852800c4034202902522400b0b404101441441101d000d004152414030a01e035000380400c0da203100600c1014011a03951841200303151107580888a94460540255a240d106022a045a000d140690105e4045070030000403042401d030115403451560f0181a070280002c080c00c28001e141c0351600343c09240b82004614040e075018495a0812482036020840700e5040140c03540c21100300081c0c0741129003041c000e00c03205098411001501a00e00403003030050b0754a035083c41c030181100743c00303032a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 727651735 1250 727650485 727650499
    0x108130606030b0108070509010f05040203060609180601030510050d020d030c021f030c031e1a0409061d031c020a140f0a020c0f2821031e1e02070302 66
    0x100800103e003004504854814084882654a600030005e02c00801c0c420b901703102c000088100f01e1420150069940113070010b111074200041d00002c905010144080b80021420443c2004403940e0148600da8124100c2000114442e00340310105048410484000e4400c0703001e00c40e000105842100c02c0515540d020305200c003101208046054034120144040c1c000c64100041c0f00d060034420310619031151002102180c0c4040310b16003020040011005540543c60084101c0d4a21340f030743e000d048502c600c210000103804250080d5910000341414500c07400303400402042c0f110800344084519103400e102c0c40181e985040720010f4520020203040c46215207030100e070441d1149a10380c06001c841445400365404c00313110b4010496000c1d100300c28282e11000d01c0b100340d0410b80440d1940c011030044c000542e124070b40c54071244421050064100102d07105440c68840030141e000108151b81c0b103002c1c08120200c0010607002d41a10481550921520f440c0d004000c150f9208116690046030083c00d85 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 727652985 1250 727651735 727651739
    0xc04090618110304110108061203181e0a0320031e010507030908042601051611030f16020303090d050106060207050f06040e07020a1707020109120c050108130606 71
    0x403036540c8030304200070079264076107142070700395050000072a4402c6601c401c1c40051009030000544485030050800380e0442000d0042480000c0c1c01c0000b00780064181141010309250502000000000035042110280c0c0f407142e20700311a140c13040b4040980742d100030985681d440c0503e088074100c00321040a035243c811802070610304020201c0c40119606000c000344142e139641007069098a060321070082c0030b403404200400211807c0a0b482040c2c3d0b540500c10300c540e808590082c1e09454040c1d80c980001840304201307805603a00303d6110070400c50b40c20091420f00751080819511806107904514240050642c0340045503424000c0b0780b982403000b0a800c001c1d0781141815070081895000300701c054482d4a00c041814940300100c2134400100810b890319086c02c0130702c0101d42c81000790a070825440707032800700310015000c1250b50402d1920b44003c0d80d15150700c0d00005101c507440e84d2103441d80150941421005c1100790034090305858007030030049aa91514154814002c802c0300000e82214070306040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 727654235 1250 727652985 727652999
    0x11060112020915210f01110a0906021603020f0409060911041d0319021507170708090a0314040f08010b0f01030b0607030c02030a0c06031d01060b0706050c040906 71
    0xa080d026000365120602c90303070b980c0040f0202c000001e221942c4030500c011141c900c5021042c441c0c500700b655505031540540b0401c42142596079010294242d110b010600541081d030200d500380051400b44001d02c420890001540c03658911804041e004260f4114001c0c00750315190000c4100e9a4040020004003103241000e4070f2421460900c40d06c02c1c0d003852494440c0b805200d01d021004540d05000c2d51622040030341e0f4403400003500b008241540074002240c440828108280c0780b1134810ba032100c110b42c01c5480b541008945d00105140d0030b015040060021000000407a40391035545800c04003406c0c59000104036103400380d540848400c814284021400e810190412032300303410700b52540c41401902d440150b094036102040c03650400000e02080020a2150021040450010703040c3e944850203920742c01d07403c03c2c060700000c010030348500513018900714103c1240003849030040200812820101c510100c0c1c415000080c0c6015100c8020810402801d0101d03030050600348010000c02e81c0d9200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 727655485 1250 727654235 727654259
    0x7020a140105040b280306050a05010509030708060415140421020c030105010b0c0f0c010804230a0303140601170a11041205160b030f18030c16150201062301110601 72
    0x703010900d1043c0e00e170300b480c69030307001e0b000340015030354001c1c480d008142c2807a00440d01508007040c0c44e40e0610441c040050200018440300340114040c9840c441e00305512418441900c0071401a00f003820300d0b107003c200204000d091280c01401c0d9008198801c00009a0200d20744003044413484e038503501e40000011010b25141c02890484400c100f030300c541c11203c04003117894a201d0012075022a01502c00a40003e107014060001c2c055048203c194260005503400d281c251134403400c502081c0ea5100248010209032803450340f0032800d181008030b1804903041644900f001070215072403581c44009840060a800b010707034003d00903600c41d0442d0400c940c102543d0703403015079a41c50300d179505c80207020580c824907074210f030311440d5039142245080c4c803140426110702c290030750480c040307001c02d011070344003000103000134225546800200301040b4100012903d03420750b155400300c19a8900501080b42c4545030156043c004203043d4450704600500e001614004203a00214100d8002e000000c161810881 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 727656735 1250 727655485 727655527
    0x3020a17150723031918260409060533030901090212030a0905033f0d0501061e1d03070e0f0f0a020a1d060f0408030403060f0207020a140105040b 64
    0x42440700d5020f4018000e90446480c00000405540702c00c2100c4080350701c0316200d0b1f40072210301c1c105030900949600d0000b1035400c5034011020f019142c8000300141e10307201500601e041c10200c3c900001c0c83c108542060303450241004004c4e4850040001403401c0001c0d840000400c0d0003818214100e0038084c03100d41c50354000b402900c04910310001c0442c03030b4240040c0a8803540307110700300801d9141c0c120b494448150305210994080711340c0d50105842d0240c2da140500304480b420280810207504000000d000d14800d00c542e441100981c2c0c50321011284c0c440c071041c880e0f51640c07030f02e40f0401c464100801d04140740d0b5000310200440c1541030003061100c5650252243c084158801540d80b1040f031040b00f43d200b0901e050000a000c10b03001c1c4900310300b101c1c88090859008203900d240440d400030164154025500406aa400100b402c000344806801454800034082c1c01c1189401082e038001022803c45000701d40d00039030600c48101d43c5034080c00032500a40b610000807511021040a21a400c4002c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 727657985 1250 727656735 727656751
    0x3070c0c1d060a090504050d050304060209040e010f060501030b1e040237020309060301150c050d02010c030b0409050d1d031b010e0301051b09011404060903020a1715072303 76
    0xc00000204e80009200d054011a849070240000c103442204c11a1203030009002a11300650800450380313256914450009410a184004244440251031413401c0340c03003e034072841c1450306010014409982e41006041c01ca4001c0c9044d00301c40400d4008100207007c1c2c1d0014001e030112100d074550f948560510207008100511650303101c1110032607800c98aa00441e407805030003010a1005002c241c1c0ca0b0450100d203d01107140104403420309486040c80c10180b4040314025035518034840c4045981802140c503044ca0680d000e110389100755642a90b6122200038130303810004040444c0c00c038803060b00c03060300320090b0040c1101c030100b00e0807074058a00641100c01602084608113001111300301070240300d104040401c01b15050031403546000341d5035072020610320304000c131b03504160030342140d1000944081c14543d9144c0c4040c600754414458940c0b01904100482d02c411800661a50000244002c20040c003142c52601c54a0b00e507010b89950012950071321050420031440089081a6030265101d2005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 727659235 1250 727657985 727657999
    0x20d110a0c1d0106020703020907080619090e0f0a0c090b13020409050105040f0c17150409082d030103080904060302180403020c060a021929150405010b03070c0c1d06 73
    0xb075140181e03901c46e0940700094200640c40001181d1034042e030440c550200005d088245022120600803524903980d40210102559880910b1400e100c100b0201e51000010780c0105220f10b11902e404400c0800ea115980444c2d0310785594a407942c0713480701c01d00f00c45101500150b44440d111015000600001d0203014082c5140051424001a25000f0380416a116403541c011041c19034484103d4072000510356014914036401c18200d50b01d6038401c3c0e01010380920344154441d130782549410404400d880301100f4107024007085001d0500b4860850741161381c01102c1c1961196850f0112300601031982c0040d6014000140c055001d04e18202001e01c40d40c8a5429541541c40c510100701003405200b002d540107a000700c0c3d44104401402030108034540c00b40281d000120700388080d08080d15004500340745001c803040280220b862000311011001a0100c50134802581445400e00c000e01000300040308108056403a0014440b143c040d0300007500120466804003600070101c802d883c10240d4041c1d00800e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 727660485 1250 727659235 727659239
    0x60f08010c080c0f09090a110a120e0609030417011b020c0a0509160e0310021b0c06250606150509120120030403090f0f05120d020d110a0c1d01 63
    0xb004813080c1c20304d881d82403400c051210b8144040e18000810000d0f40d030fa501c4519115007001a0701030805071030ba0390f40e10701302c42000c0380054040d22241c1d07100000d607600410600c48600b40100554040d02c598902214045495201440c003400807016140701c50a602000800f180c3c3e030105074228550000c0c2c0c1c443c85096900c5c420b1100524044450500594507604400e451505c1511400f001d04e0b030080481c0ca040341038044420881e81b040d40c50b4042c000101d004010307106000d0143e03000c901d000f16003041c107001102254196a541c0440c1400c840c60408078407000300040d60f841440988401c0800100c01c18103020b000d00541c2c08020b80c2c600c61444030090301070140050159030090204a085051a446422a442c1041e04054400c0f41404005d801c041808400c0041e6000241184101c03882e103145004280038807181e044030402040d810040c6030750141c0d43c0010700b6a50741010791074040c11203003014151608020460f2801450152585000120200395103990110014010b20301c070b0707d0366 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 727661735 1250 727660485 727660501
    0x709080c030c010e041a04020c21070308060d1a0a05011707030507050f01050f1314041a010e130e0c03070b030108150a0b06030403110607020d05040e0703060f08010c08 74
    0x2c511400711a00040c1e000c2d050400b40d04054005510800a400c40744e4a03c09064001030240c0e00800501f00e42544020711f40caa58002501c25020b0b1a2010450545440c3d0b030340e140181000303001030a071401100d8607006241000060940c1400c5000006240e100f1030804403e0040901021721403484031108007004045265004501c0c039007100d40c00001031034401e2074203082c454615841541c1c41d06015081c020103507070040400c014440a038100306c08400d0301c0c0c00e25090a20420f081384a150080385010b00025985400da150140101d800b400c00707901c00ca121f440000d180507038001d883d14040d030921211b01e50710b01c000200007104080803402c0c4c600103a02e58480b140d580c0030034810440203074041440750042710f0b80404600d4101446510114002d01c281d40840d50950054404400145103030440c0c0c5290001401000e0b04006148050035101034118802403250086000d508810302944010501c00c601907406200148084007041c80300940c0da1900c0ca000345805441040402d01340c000041400d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 727662985 1250 727661735 727661743
    0xd09060911220b040b180a1802030d030f020c01140402120a0b0112230c0a0b0f0d0b0315071101060e0124020f19050c0d05060c0d140709080c03 63
    0x140d40244800600d02540c2e22000028088080310103400c00e65400e8804a6030b1079914030f021801c29000705807001400c200d492a8200d50a205040f605c402c045584200142d50209003080c0b1b448640c40c01140e948880304000b40284200207000314190720341100c201c1c10081e4000c04034451802100c80d440451042c0602984070000040020a01c202c2c1000602200c644000b42d081068002ca454044542c141003000c03200107950342c0c0111245d0b000c400024802d00c0c02d06150005410ba184040707007042e5081c0e9030601c49000e2a250300c41d074140c07140d0324040310340c40c02c1004132904481c0c0041146d05040c02034000c2d026841c100c10300e4402e5428468080b58103a21100054121100522200303440c50980f546d403c408401d40081c107046005003c1241520b980411a50240e2000f6508d41c6110400303a180580c41c01919040c0a402a60241d8162002c00c17404913215601640c1703005941d54407000113811200402d541030390880d00c80700c40c1c818455104d5200308800c007518011000c540c0f0003140c820801d0307a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 727664235 1250 727662985 727663009
    0x30a14090c100c08210a0c0e130c1e0c05160f060804080c01050f18071208220303030c0e04050f0604020c12070f1115030a050c0d09060911 61
    0x15481c140c0c808050f2282180b095030600038542c3e9030924480c200c03610140c0d10ba041481100600300814854000d440c0d00c01c2c034041c11905d04060005003425000304900c1e00805004658003550340303032600d0390340e401103070f1000a5103588454001201e1940a02504c81101290169135910510980c5850408100011b1007511500d56245d15054a80f220480702c0704001002100c006005010b0890101c409000d003d00a2407180141803c0340780c500d03040c0324a0304002c00208107a5100040402c00054004c2c130b1000d4286d00400c00d1540d41e00c880e591800b05002030000074442c40b064440020515a159214002003072940d41c072079051403801020042504e40035221480c04c140d80d90b0124502d1f140035070080114012400039511510020003010200c0e811590041d038500c0d0a01d1003010030400e0a68440c1c08460045400d1501c1500040b0447c1c0346000c0184445c0e03002c0e0355030300402d00003403844041d26004413180c9414407003100c051824070054208400104d82c2039000c101d440344580303048150104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 727665485 1250 727664235 727664239
    0xb06150c03030723070206070f02030a0609050c0406030803010b130e01060f080a0902030613022b1a0f1605041503020d0e0606030307021c120c12020102090a0303030b0a0b030a14090c 80
    0xb0400e001c4ea000c100d001c2c2c0c4601000c8504227002c0c252440141c60600c101d010650003150002a090780d903052090819000c28043da1059142030390034000100e185084e039065844808407151650031052003203007841d000d90481103103118001c00000c0c1c25944840c06404400c01c0d59218440c50703e56018030025507200c0d90000b54580c1100d00050305400c0c4072113170189401d0004010599642104081c44000010044c400120185e0941d100e000e2280c80c402c145401c03c07200d20006c41d545054102081c0140000d0064009010064240004584110291070103405051a245040802c0417800f034001c0d44003603841101c80d41028036104840c003000c62520f02c01c240242c00340d03203414060303800c014403503a00f1501e6005e00906280f400e40459031800000d42c9620998440b04600802e6040c0260300005c032441c2003046a004100c2801d007503da6442c1c0300100c80e8035050105040503100c000560507021030700800b151400c088108041905a41c000e10402c000d00e00c142040780e01c1ea1000c817600c071072105042c1d0fa = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 727666735 1250 727665485 727665487
    0xb281e0f1208040e070c0b150102010509030703023f09040b030f030a030b0a150302030702070806010f091a191a0403080301030807020604121a0108030310030b06150c03030723 77
    0x10122903c110500e17070120311031406800c080c03c2c907034896441c840c06641e41e20058000e850540742d1960248200c540210745400154100703071256074003d54507104104400915a480521156802c0b00c5c2011020741070400344501c8000101031403041d0311038000307000a9128500f8801c0c80480b42c100450440140410440514504140f031041540600304003400720ba0032161901c000980d4441d500e8112045440703d0789c0c096030b64101120020728003a13094100483d03a42046004001d4003010114420484c1c0710304401180000000a55203910f00000303e0041c0c002024108603041c50481100040c00c0c1c58441d0b607400d00d042c008007071002c60780c0140e0100034494041000148080340b080750107000c0c0c8920041c8864031705600c9407040c4070401c0307070004126490907011000003d17034104403850300c0c05400864000d60030b610b44021840520441c5c0e2001030301490803c0040341e4592604044204400200e21480d503456200b41c25082d80c0c0c1d8021100b0000080003564400c0c11180c406003100700c0344c1c441982d09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 727667985 1250 727666735 727666739
    0x2103090c010f02100207060609060e070f1412040507050301060b090d060b030a08120a0f0902030c0f0f0d03050705161203050f0706061d0a0b281e0f120804 68
    0x1902e507440038900b50800c0d4850301e104103802000300d00007044010301c18200803554901d04030201c4152800c030340140e04205c080300308003c034240d40180b0340d2001d0400c9142200b4586580380c0409002d10415003140c4200c1c17004002c01c400e00030300065150407544140d00130428185c0e07880a0300c15500400403c0340e80010718210b1140400c000d40c20034140c40c08000d00b0f0781c0c4698010740d901c4013151311481120000c0c04800c0c080002411051040b18900b00301201d082c01204069400252101c0450501c680728240c032200c000096120745410b00391025024045101a411504000c0c0c9160882c81c811140c6110382c448c1640310f00b80c101c1211003242e140c0700410802142540e815900f940065088a0310f0f21400c0c400e10000c03400303a00400c8014149692800004030424405003a0210000c00086106090080780c440311384a40343c1101c3c0e01401d0203100150f901101802c003654030555031012032001400100c1d404504001c482c0301046a680300759012141f655161540352610422001802c0350038140701c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 727669235 1250 727667985 727667987
    0x2061f14041d060405070602061308072d150615110c0604181b0518040209090f0609100303020706140705010e100c1815051207022103090c01 62
    0x20404080c600070804540d02c1208080016806640c18903104203a10600c14001402000e110100250a140c409400286452074034541c034a10170000080c1440c01c00100d18050040740381b60306189015403201c0030030882c1d070101901c003081a44079054540d40c018007400303070101650b44581001c036641581500485201048182c074054401d1280340c0060088442402c03403641c0300e000910241070004c000b038100b9800c00246504546035001c00200700d07060454000411034000d4280c445140250040364800c03001d647c040f80182c0a1b03c41d05940000500052080c0c200c0704280d16845100c040d520201d89560741755404a420001c1c1c0300c05001368002c11024000248103624100c460303a2443c400c03619001d171a41e13900d802c492481a0b80c88070354002460844181071a40200b18000c4128541152a1043e151450b03844003403d110b1420702442205008041e03601500503a800c158000c02c21003841c1c540484040c1d1a080d0950844000f01002a100c036400c80c0c041c0c00b81c2e402014810002c0501002c2400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 727670485 1250 727669235 727669259
    0xd09051507021e0102071e0f0843140f1e01050310030b090109121107172d190809010c0813030501140105040207053003041202061f 58
    0x10303103d8114003c8a0300441d04c030444003480c25135021222400c0107998070300841d441d1400150f4000c458250040d280700b1541c80d112240380080224041e95903202c030b010564000d1256501e843c00d900746034203c00400200e4070480550708810a00981e200d0b4025403c4a082002c0c2d481c401010944d40c800c060005a4907510a070091075102100d2142d0105440d1651108000800d040300d000006039102c04640d800c05c1014407c001a40086080c1113015490604d54141c840445001d85444091a00c442042000303040081400010218101031881c0918820381d03c0b05240302c0f181e4075003500c80c554140c1d01c03400d01246926030075a0071909182c1061500f03001120403820301501900e12030b80074000d03d00003c1651b504c8400841c4540000120b114454101c81c060500c140d101e01d2145106001410125030301250310341d8008844001721005054170450139018407018100c0b01160b4070b000c003c00040001c00e2200750000140303038003114660b40d60007000d407000c2500c000803000024100a000c1040c0e40840f5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 727671735 1250 727670485 727670539
    0x10e06030a1406090d0201050c1e0d020703050d0b0118030b0402220902040506060903070b160c0605090f0f030712080c030d0606110f0706050306010c050d0905150702 73
    0x1429600020550b840b200d01240d0901c4903442035820140a1040580040107030914a481030700013480b0615103403001e010710b80240c600801000c5072072b02d05c11406030164404c482d16200b03500c80c2151200f030740341001011500465004001c55107803210403605580104581c1181560003d0f40340d04072030950b50381c40700140d0301420481c0c00c401c0c200a03010203818482030082c07020701d00c450002000710442c01004199800517081c1c5004078402c0201d485142c50104500050356900c4041650721001d140c059500c00303843c6000075003105501d03100841c01f65401001030000d5041295198440d06080c0100201d10f1170805440da4075910080080110607078034940008c0c140e000d41075041c1002c2c040c2c0312080c2154070610412403c1ca594040c14400c0b075030081901840780c03401500602000c4104030704582d840981d8000c40060040200001d00b15a108441120410340e02c1005d4459030648000094045141f50080c240f2480e80c04640e06542c64003a8142e40c0d01d580c008049566802c2002c4007400c821940d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 727672985 1250 727671735 727671739
    0xc0f08060a180c03060209100903120f0c0b09061801050601090515130906060201110309070504270309091d190f05030f072d020f03100e0a1209030506010e06 69
    0x204540b04003282961440710300440c0115805070392650880200321441c01740d0300d41c1c1c906201d17443c5c0b41400807460441240f010034840c0d090003e4815075402003507800d80c1d070070000203000200031030410548900124603a0301401c141c08a4060a816961089090751011652140018222141040103280c802c007006000d040d01200180b40c60111140c2c40c0c400030305a0041c64526880391010000942c1c240b14030200b1a40100c400c038158201460752948a604900c00c2c1881151500881e5122107240701000b491840e01150002d012035052401038801001b0344264116540340514007060388600c400e095500b419003101400c00211409000c54043d9111072043e2000300c40e031180301700010010001460350940c000c0032513885040b64500100300040744c1411451254040f500040e59001e80c81c01d03a03500590448100c04420400800301c2d141c0810b0032030b40c0359880c2c02c22040d102c01c5000864004001ca02903203c0d6070a81008000130b40303c035030141c40000c010303500801c0104602403c500f6102d41200e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 727674235 1250 727672985 727673021
    0x1e03130501180224430f0f02060409020a080714031603051305070b0c0d0302090d020405060d0816032c09130c03030305070e040603020603180f0607020a0c0f08060a 72
    0x554412004085034044143d260a90b00340e040710b440fa1841000d1009217079640b00b4040c8049680c0d03802042002420010070054014000c24115034070343d4107403000fa08512400710b48400c4003150040003844159484000310b4081d18242507070400d000704880c8a2035007040918041511428120000c06c002040b148009548600007000a04144500d000400f14410303060b48404030b000201c7d08100e054407488050510400950905440d941c10185205404843c0020180c0e101070104e005000d40e01c0300101040400980740c00810400b4120018030b50081e0f40b901d41403e5034500d0380210540c210074003400100008120a22450891405036200098903840018003459944040300c4030b1071b42c1c100f00c0200391207104010000b50f101d02d64132108031003201c0c1446202c1c55a004103506200c05007182600340900c00c01d640380d841d0208a001d903d2040801103400c40d29082c04001d494102030078003210700000f02c0200054540400d080340c2c1c03c0c0e542c00b20262145449002507a00180a9907886040c0b0b900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 727675485 1250 727674235 727674247
    0x10e0d140706030204080f01020a09091e090b0106122901050c030a030614030c130f14010305070e160906180305031602100c1104021e03130501180224 66
    0x303201c00030052103161000b688860500b0200da040001c80c0b854850168130600c000e802484d40040240304452103032130001004256a04a421103952074002e070b4900c2c605240c1103000b0001072842d00d034101c41041da01c5403000355060a00d80107468a0f80c0000900d00380200c40101854480c01601c510008141042c510b00030305400c20900710741000c94042c02090f031b240000c104030a1552000403002004401501e004521b1f031001036035840c031040340800c0d03299036801c1292078a420340e4011042010b07e6412000c80790b9403440c1641d41c07514180600200000c5910204100d41005511941c410441c1d131103401e4658107110040711012007592012480040f014000000b0507820f10007850008c00c1d43c4444e482c025094014400780c001c111402e101008030b011180d030b001c11180206027500c0281190090f03520300b280b99204400d03150034006924201000030500c44021011404c012041d80700e900203104054042c00f0003899104011406504124505202d80f5113540034131044808000d150142ca04080c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 727676735 1250 727675485 727675523
    0x9010306030f060e1606021c050f0d05010911160f060b120f061014090415020310032001050409020d0e010c050c0721020111070b030408030402040e010b010e0d 70
    0x15042d42c006840103550752081443c0c1d42c4041c001600c1c110048076000c00074500d4540000c0d540d1483c031000e006956480c00240750464030800448001c00302402c80720343c0703940240180500800c42032084075461490082e14071010100700713041c3d900c5044140c444202c02c000c00d03203400c4c890080882d011150260781d841240f80c0c07940d9040078001c0711f030750715030080005007000341f9003e180c0311001d06086107148080c5d500704207001d4032810110b0a0402a200410552100c1c1382c07000c0c0e00b11461486a0310540040f04001000700041d0440e0708403406992070100c4c0500d080031700e5204914100701c2034001a403c000600105016400034440b584900d100060380284c4089c9450840d80c110f8609800a031002801c048551001c1050001034043d40e002c648101c003400c040313442c1071600903000130f0501c555500c81050040c4103024030b030000c0034007401c3c0a07a02d281c20710340300c4819801217130100e01c00e034a000c07042003c1da6414884d62406c100306031507000c1c100e0080410002d400c1001407040311121845040c0d070360a5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 727677985 1250 727676735 727676753
    0x20f030406050411011d121e25060801030320010f0f0c1e080c07050f01050403030c0512150a230301051b1210171e210901030603 57
    0x92400303040002a14142441e020400ca040150701d10304120b40c1e903120f68440194141806d0b14000304407002c5c00d42202e10786c00f01c0c1c1013400000b101048061079913031b21039400343c000c204a6500485503c0d80744403007400d510605140341c014040c17080003850513401800001d003c2c1940c40315020001001090740803900001509494405a501705081d441d2500120403d040340246404071560741004040220303050030014030903904c0e0740d101c42086514400f143c100304c0b68000300e908080e0403505881e45046003521941c007030407080d9000c400291a044480c50f009105506603070100c5030408070700031282c07110100501c03002807004101da803003211000d001507440c441c0951000c0e40e5000c560310f4080801c0c150105407c541c0001e10f002c42074107040c030201c180e0620000484110241c80302d01c03003045845071900300011800a4000c000e0612108429010b10000007031140c0c002d0306154400d040c0c04000c04100c0762110846490b07504013a10354019420000d40f950050034200740c0c18900041c0180c0d0b203403203038948 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 727679235 1250 727677985 727677991
    0x6050301091104110909040f0f0203031306090504060b03070c020f060c1e0102090d0305030a060e070e030607031808180a1e060302070312090204200a0230070303020f03 74
    0x35a20510720040c40320b0501c0e0040c41144248004610700b421041e1700841c0300c6040082c0000d142d0700e2101943c100700700c0c81e61405000705402130200c98440d0310303044501065070441d008520100e121190005864901406060280c03001005060b0440d100c4a40a5401c100d4030b080803640000403165550345e0361102c0c0090000f104203280240821240e541340c00c200b071040d800016600f41d0040000035a5511030301c111000090b032614007503507296607000580c80141030980200a00c1038140c5c1c04e000e0150fa2200c1d211250141c100c09441d0350b170b2145507095085070400702c40c0303400041c12440507001040c04403018068944003d4260301c405481d00d000108000030540090007200b800e2110618421120141c1c84050a51806c0451802e01036480103031000b01d620900c204013585a0769040e0031522141c20101c480d012402e008240381d4449141c41c601c0d500000b5110005100d4019000210650008681200d640a035022241c49040e00d45090155111000590516800f0409100c4c060168001544 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 727680485 1250 727679235 727679243
    0x60b0a03050105071d0301060312081906090207060b010825090801020a0503090d030b180406090632061810080303130c0603020306150c0709111801022a040605030109 73
    0x1141130040c00250170500c3c0c04080d070318041d80c135100f000d0002030502d040e41d0300c40b03003020f003020101a030302d201104405200e1050030f000704504140c00000c9109082d0054101ea920505003403207241043c0c001110780340b00c01c0b00d42c2010000c59480c1800c0c1401c0c241e003400c00b142d00501d400e003456503c5100d69402d80c5d00c862404000104000108550050300740004541e108240c034003070144039034400000764903c100040303040d0681a01f8001c142041420340c09801e00c6e80e0f200d030b0701f07100f10b40c05503034075141c504010b20604882054061549040030050b665541c0b1030a070091804014000740f104c81804400018881250017103425000305042000b08003552048408203000c0565600526100c1e50004560b0700c410141401402800715503691214401c0008070340020090300c801e070188a103443e25610303a000e035000628204002005596400090030580503400b039000030717648801d004a907600750400407030882c1100003a42e80500c00b0988207144007003800410100300f060710340000908454642408407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 727681735 1250 727680485 727680497
    0xa0212160906050c0318012601030303060803070302100e160b0915090607240f0e010b0901081905280501050708090312100b040b280507060b0a0305010507 68
    0x1605241d803010303918010700b14500d01541451411a0b8656a0b80120038440390882c0401c568416580d00c5191a00f10b000240b0030111041000041103191001c02804168002420150041060300d000170850f43d240f0303855402442161000e54001c0004c2029100e0074180740140928a0400f0300f83e250008041c04204003000e80e030350b089200b01b150321076802c110304a480e5010703c121a100c0e910701090700c12082c0c00000403031045040c0760440c0c40401d45246000c0380070b8a00300b8410340300b1402d580f00c031816964a43c000c0210031140e034100000e845007485580400d90045045031140d0316421200d4944074031410440320007134000800041b00000c244005080d903840990398206016003401001d800a0302d80c00c251009040c041074964591156180d43d0722072604000100e040041d07040a80c80081906010741625940c072201c0b4442158004906240303640040480d0107040981d0600380d0b00e2582654031107a01c0d111007a035442002c0c000c0001c43e282d011044820000226001380180b03803017030007169100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 727682985 1250 727681735 727681771
    0x10605030a1416050702030f010203090703060b1203030105190b030a0e060f09061303090e1003030f031104360b040606020705130e03040f080a15020c0d05030a0212 72
    0x7241210200c14104020310380040038014001c0e00c40000c907445841d07910b00660303640c2917400880e1422055240d042e1790342d071002041000d1428041004400d5920a16040c8000a5130744204224201c0742c42700028190030401c01007120703140c41074104007503550724014405840e65652400c04960030448146021507124000e000d1400c4050110592003c400c030300f454138900b44401900d075510401041e240a07078a242c20090107150141e8a840d0050100040707481152822100b1241348070600d12048010482c0300e58040a914024011034580c04903c076502070034246002590304022034940148015100c14500d617002c28001c050250814401ca0b50b004076284582c038081c4021940341d075000104542020030b06000c60360b109080604559100240402d01c840014116030652150384d01c02600700310038032000103181030081141c00c0c0c05030296440241c0b543c1800080e800b83d101d202181009604015004a5140e0043c405113400401848005003020010412600a42001d03201c2441d100994011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 727684235 1250 727682985 727683001
    0x71b080105010905090a030c080d090c03110a0602070b0d09151a0a090c4b0201060b04050105122205010b100e130c0c02060a1101060b0a14130e01060503 67
    0x342034022140c1c174000d0100f08071a0310000c1c80304c0c0020400510f00100040c00341c2c078050840d0803402c0310541001c00c626095070703a440d000050200c440000d500403440705030005842c030300100d0200111861000c04900e40110410320200906c0c80c5101240c82c11803580c00d0202c00b400ea88a01003081158440e07505080407000200280650641d009481c110304003600d10801d1540010041d014040003030308001301c3e44250780300683c0c034480d80c006040c3c0311220288201071120010820b00650445800801a00f6102c100d13070210303803013540035250120300704006183c1c80b00034920070f05034010b1030010106403034100c05c4070304070000030146000c1e907482e91600107004861810103407040c0310958a04091880101c24808210f6010203002c90740d90044d03985c1000e1048034080c940f43c210080d4001e100f40d60701c482900c80540407402d040e8588815610302103000c2601088201194046641c80d1170b2001100c05140041010354003510140c2403043c40c003c000110b208000c0000ca002e01940d8441940760702d02244 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 727685485 1250 727684235 727684241
    0x70e0a2c0f04212109020d080304030e0306060f012106080c0f0d0b190b04090b0f1317090f0a0e0405060c04030c150e1801050f060309070902071b0801050109 69
    0xd0144242011200005003113411003181c0e02500ea414824030008418414150014268582c02a4000703c0300710001c010482e0380b10065215038800d48038901500440702c10f15a40f940112075850300300c3c003101c1c2c4a0800f1b40c05401141405906c001468214003007c6a0340ba040e01e8042e400a1003a90124405550f80d1515040094400105540c55006d0300300079202d544038a2000f804503071502e11015949994104543c200d51103c0e4030182c024001e09225240243c0401000c841981410301d100b000326401c0305034402c42031070b1250040324015a140700c003440e200d100e5103c0c510322540f014070102000c105440b441c64030001070a0385600100245080d040c994186140140075401e0420200020300c0025010703180901554a002002d240a83c42e83c40144e0300c00031410000c0e41e02840d0b51907c1003900e08540c0989058075000e03140c0c81c07100e60140044c01940c2c00305907041c0f011500203100511030f40d8901d501500f040c9001d160800020203040507400b552044640085035141d444100500882c0d80703c1c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 727686735 1250 727685485 727685513
    0x90a0308091e090a110d060f050405070309171b060f0f011203092106050f150303070b0a09030212070b07020c0a050906010806060903030a090e070e0a2c0f04 69
    0x1000c03107802c200b0001921080000c1803190f9984d6280c940600d410000c00c2a5665540704150400180342c031022101c13001a400d1040500c1581010005102d10380710307000f10b83c403540c1d00040e6005140c0000980c0d800a420a01200ca1001e02811100c0c40b451810060340f805000100015021421b242310004422081600322404040980300c50600082e4802e000404a50b00300040c20305400624015903089013129502410441c148000d000c150188054031030f00495007082e405100100601c02e0540781d00560202130100800780b80050803904450700b0401e080343c403e1056603001038071030060842c1078010b4641569481c0c0d0300010090903a80400c5120b074504022204035922500d4040020716140c4001c100070b04022000b0042502510362106890400c1c03401010340389c4621207100e006000006900c510300071981d1800c00300c1d0015018048010540030090b245545813801d1891000e0400390b286444242e107074000e951406080e0840d81c035640210706149500f0420309042c103040c1c40560380c2c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 727687985 1250 727686735 727686769
    0xb0a110313061d03070506030f15091501030605010e0105121003061b17010509010b1605010606030f110301080604020d031b0309050108070216061107030605090d1209050304140402090a030809 84
    0x80c05c401e0029a840005803607001c0140e0350080100c0d0307580003040144c044c9011400d5003044013101405801905000d4404400741c00385c0e010442d00d41d88400440b44221250304e5540802c40400c104242803031082a51a4030684010307101000039503d0355544102c07410b04411101c10082403410810150b8040d02c2866500507a0307200348040e505041c001074841406104408a0300c100203845c0c1e252010454440c074020380c004008101035a074450307014010300401c0c000c0c0000f03e4500100c004079585ca20095906940748400200442c0d03645909207c000b00c0c4d030160681c03d201c140c03d2491850801d50314083c1010340b00ba518400017620f003c00140100d000603022000b59001036501e0010350748003412445c2160641d1038088500c054409e20581802c005420140407141440e04200400f02c0000d6071504840d0320759600c544003c11001c0c40000c0340c1c4c4c040c00c0106107804c10071041103004204481980d900000410040c82c10341c00c0c800241210b106a4001c807010a000729002529203001008440000c5071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 727689235 1250 727687985 727687993
    0x5190212010e03370801140d15091a0a0c1b03020d0e060f181903030906050915070b04020f03010923010e070605070501150b0a110313061d03 62
    0x141000b41600d9018040182d4a80300d5804121140c100044104840c208401030510460725500e46004000d01001d00404404071600030140b840750901b000450302254220081c031001d040780182000240c43c3d510420b42d42c95201c00c2d0a02001350b400458a402000c1203100061001e00310b65000d0000c402c2c4400c1c902411000340716000110350041202516030640785840030940310107400040c046c0c0074207020311800d9580452004041600c0c0c0206000518003211682d160b0100c1d4039043e45480e0441c00000c0003c0e0f03c6840400000e80103001901601d900241400710140380400c03100072365003012009503503401d40c8406100640c2003c80b008619031605070700030b0181d100c0c19103588100300c02d0404d90921504001040c0b0324110420b40c0a46c055928003016940c41c0340c0e07a00b2009006800030038059613103500e0004111448011610740c0303812130740552034990034070507904010307203924030392403125011408200101007413a026100030f90058a0180c68070040e103000271200e107000ca00302c010b40d24003030b40c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 727690485 1250 727689235 727689251
    0x4150206130f060f0f0e010603140c2b020d0321020f09010e030a020405010806070f08070906030b181306140402030316060f090305041e0b04050d0606030519021201 72
    0x600350b00e10109050300120041405103207107801100918640c91880b940501d401e0044200784010b4018800f20390090050303044c80d06400110380c0d110443d4099a9621030250032826054601082082082070744600084074a00c070a41c0106800340ca41100c103c000400b01c0082500d1701c504080901e0031900e0442d81141450b44a000c0e0382ca103445018109418000c84d405c152030f640d50301304001344a541e0b0142080c052540d4170b0241036134070300c0b003907070880c020a082c480e0004900d842070604c14411003680d5900c2d190245010b10a07001003054141c5250402c80c406d201c03142c0d01e041050b50601031035828030019621449402c0c004115003641c01009840400e0906100c05a60000180c030340f003000361110900d0b44c46480c40d041c1e000f006801c520341c03c0e035802c2c8038003402419007081c00b60084803941c990801c001c1d80302c0b086412803908940909500c4040c1480148200d00340b0130412500d191042d28002001d684a071036840c0340080350040c1e504071409056080d002c6040c03179039584902031140002840051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 727691735 1250 727690485 727690493
    0xb22031e0305070e0f03190f0201080a0b0d0b060607020d0302030408120711040c1e0c0b130218060a03172503080105130f0e0d0305182505060415020613 67
    0x198085840600c00d0481011102180e901480050640c078928041182203c445d4904417141c0031a400050b0b02080012f400660003c01d203015008901100600d44000c100745542ca00105c000c0252100c5d07045081440404016195040f8103078040c0e020340c0040d40c581d89482486c91a2008801d10342c13122080a11a250005180071003072011316400301c40224070b03802c104d003040300e07440d100248200095181061050680350001c1242c00301901802c071015550383c4542c01d6880501000d4070007500000324100751090300100360b129503002b4800030260741c40541c0e01e48502e88440305541c10321a0392040040c0b080c613043c108001000b45d864154803850703c81d011684015202c80014441c1a0058500078040200c00949a204140c0420f14280401c06d21142d202e0895031000d12400d0380000c07034076010205000345101003c031082640e00307200800c1407071010b803845054008012258100460030300c00c00318dc950b5034040980080c2c84c0c8842d41c0d016040050304000d14005003e008141c0b03d02c0c8e10460034001c0303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 727692985 1250 727691735 727691747
    0xc060a0c1103030a020a0c080d020703092c090c060a031b11100c0203040b12040b180307080f0904050106051e0a1b480e040b22031e030507 61
    0x700c020b04c80162030fa00700d0141510302d512070b00310003082c0b41c5000600e80d902e6802076014011140c000e60312408150f4a5501c1d00300c2038550f100c244081141c0c4117200c0107030001c488410381c0c0d22100100580d2074020303c200104103070740c12014150010940341c1041010b020355003540341000da8204c0c5400004190a920303c1511784131207140000c605511610f6004c0154000c00031280189407514048ac0d58000c1121194000c800560b0119001005000810a00803000201280703880d141d401071490031035541d440c0115903100410142450205000281040c0e0341d5100d2a8001c03c92600c1d0256540c90701c801d02d480c0e03d0080074800c3c1c00800c040c44100e4a072640240f00e2141c0c0c1c500484120f101c181c1508003ca040540a1a42c0d252010801d005411134481d100c41d40d10a40543c140b0301c108a100804040c8244034680036a0102000c400c1c00180071804549849411000076142e2000640d5003010300200020702d10019000706440c2c0c601b1005c080d000d09030819900105250400481c24a0200200381d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 727694235 1250 727692985 727692991
    0xf02070c17150c120c19180e04150e0a150b0a08010c0203210f010501200618010e062a0714010903270501030c21060e07020714040c050408030c060a0c110303 69
    0x8201c1c0c7e020b54000c858081107490400341130f1480103548680780c613140400300d140310444940d070507078140a5029000d61000440d02240c41c2d00c001c0b4200361010064030a0000d00c0b1164095071702c101e80b590000f03041c620030310400d4000402c42c1d01850395030f9244000350b41c20307550542d641420280d03007204201c0001c0000140c3d9040d0f0b00f09192a1292421601c01e08d00c00c80607058051169000700018803050b011100700c030740e0311569200e0080c4085c464290425442d04011102412080c4000783e00d024450824200783d01e07501b5640c0200c07400c020b0f1680710307070321b28000c2640c086035960755501c2004141034102c4150039105250907001c61480781d003000c000000000368816507042c0354894030b030349280500541c1042d009030145556115081c1e805502e00002c1c00c00343c0f0070040c041030440041000b03580301040c0034003512071035248024400841c2c01400001c245402248040000c1440702264604052000f400e035403108200910907070418048600840d0000740d524028420328400c1c40c40105404405d90b64 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 727695485 1250 727694235 727694237
    0xf280207030c0615050109050a0f090c0c0506070302041802090d0f1e0b01050a080f060c0d021603080915090a0201053a0f02070c17150c120c19 63
    0x18951405181c00e5a048000c041c000384070701d05000c040c4c3c5070100102c1c900000c607007003640e43c001100e60381d00510111800c18014042079140103e009d00800805070000c0d110b038070140c03230022141a0b8640305c02e4109002540c1050000c0d03000a030030015145c80204081404054550443c85c0c1041d07a40054030340a07008500a0130b020800b09204180400300c41180447d00c4002020f5480800300d00e004103006c1e0090040511178a005c04c0041100c284c00589050204c0200d401084135442c1d040128049401c010485401d084d006c000da2812071041001d0b000d0b8052094a6503940c2e41441c6008604000308500c5649d44205031400300401c00c0000640c0000c245d8081c01d000d960340b640400158650784003410302004000700c0c401c8030130b12078003c85c444084031407205a08201260110703150b44107034859100040c02505000409005c52030046903030303200020f4a07600729800c005400b160070400c00d208580a4900c11408103581541141100085a004600c00c5c402032400c1550b01d0302d1100c036807003440c3c038234 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 727696735 1250 727695485 727695487
    0xc03130906120f140118150207020a0608180d0c05010e060603060c0c07080609160e040b18010b0306010f090c0207050a12140a050d0e1f080702240f2802 67
    0x406000100031300c1c40313507206140000c0c81482d10174810784030180e00c03801d01142c486414003807994074851103209503400302c4d070b004001120041ca8200204e40700280a00341c1d07400b13002c0d84c1001707001d8900c0c20017505070010301546841b00b01d94030608000382190756040481c2c00507048403003009202e503804903e141c0c1c482840b800303140e110088160700b9441c20000f40c0024000e8032619040c403510240c0002e88140c2c0641c406181c0c5851621207a04803022101030300c0041c0b041041c00040384240f60151070507902401003000001d0b0002e5402c00080c41c0040c00c0c0d012810165011606001500c181c1c0036400007aa03450006001c00c1c1d01c0c080c0450384068551150503011400c00802c5000c11210070320000b1a14000c000310750700c1c1c41d1070303003489a2107000e100c10600c041070011400c000c0c0ca0074410200c81284400c07103005c0c40380c04800181640c151000030a89400c5004035803a2900039046090108007208285c2c4941c03000d03186c070384070841d001840a442400c01d100c0c0926130800d070541003001c810144504000c05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 727697841 1106 727696735 727696763
    0x60408210414130902040c230405030309040c170c03011d07021c0e0a030506040c05041e090303060e0f04120f0e120c060c0313090612 59
    0x241884044009030032494a021002c14036007840b19907010135104440c2c4d0014084660700d210b00e1000c0b406001c1c615034103100c0c2042c90303540400601d80d030520701801c0c400080d030749019203030010b8440c1c0c0d1221911011a4481e8040303040003410941030000364100f2a545803420b4000f405500342561100c1d031031080600081c01032034040d4000e0f8000d0071900c0716401c0c03000030702d80c0d0155a4100307004464140c42c006440d03038280f0710011809400584001e060524007690417007007507449644500d09103050807030418a08800642041189d1500045840302c0340380c1a00540310b668404803800d10780004000414158050040c0b2581c861481d072541000310000542c1e002c5858510715001400a4010f81820709108002c2074034508400e04039200e03064620700180c0260301416402100ba04003284407501c1c0c4007601c0a080107014411400c1c000941881c21600c1b480025540181540824000f1 = true := by decide +kernel

theorem cover : BRFrame.Cov 727517985 727697841 := by
  have h0 := BRFrame.cov_init 727517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 727517985 ≤ n) (h2 : n < 727697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
