-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2367
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:30:09.210581+00:00
-- url     : https://prove2.me/submissions/2703dd0b-2993-4543-a726-62f4813f02ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 425539568 ≤ n < 425719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 425540818 1250 425539568 425539577
    0x60501050301020c070b0c12120105030f06070e010c0213020d14010f030305300106051c090b0402010c0204060b0d0e07080c0a090902040b060d02030a060e01060203090108151f0f 78
    0x11422500c10001d0302d0000c4400446c070703450701d0740c0700000c140b42081c0e0300250214038614007080c1c0d1100314680c800942c0c1216001c900700ea91940ca110320040e19000d04480b90300108100030707540803142d401004541e81d0380e88010040001c01140c41c0b4030310100e0f04110082480159218460004003a0304440b0170301528801c843c10304281e103180c0d0010071754403c1d40592102020b0a0041281644495400c2c004d402468143c6d11525a16500010b20b00e401240114011540342c0741c142000580c103104a9002640000e0380d0310f12a038403900151100c03d0400030890300305036035403000210750f1641b00c003402c149080b0403000b04280c0d4800c0001881d10303170103411404d583d8000e0340c01d000c0d80e6618000c1c520100c1d000c1000106080c2400e000003001080d03513444554001900040800b24110303260700461040c0c0c0349110400c01d06440d080115140c0d0424065000560b01c1005600381d2503011b41d081d141e0041007103e90b48007408280e00030445008100c405154428100c003c0c0170007441e0001c105404800b00352a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 425542068 1250 425540818 425540827
    0x30b13050705061914040812031b0301030f12120e010e120301150c03140f04030308100302060901051308150105030d0f080106030c27080d08040f03111905030706050105030102 77
    0x1190342076244000c030510031007609000c400c17912041941c0090030180c0c155100108504c2d41c013a195407080721815503070100120001c100316045c809407416650024481c0c0701d02c8103e59101c844085481c403040c01400007410b16008007500318001c40522902c140004644c8003c500741240ca0810f00c820501d440030030a00051000140704203a6940e824100d1410b200c40c0c03507240c20152082e9a00760740f2002107031030016145480e09002001041240d110760354051095486820b10103c80d611408002d500c210b04120b40b0301150700c00d1001d814944021034981950f03503510024a807804901c40400c46c40010581d00400c580d180c140001c20016045050075421b584c0d0145000300307403203014028072080c582d5a00c45200e410f4031452000100f000c8100c0c0340100241d02d60300d40701a1803142c3c400d0316014883d0200c83d0408034400c0c540c40c0d00881e4014842a044200e590b01942c2020307802905a5582c420012803a09036011800c034007020034020400346994174554100070054520580003203020360700401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 425543318 1250 425542068 425542087
    0x406021201090b0307141f0c0f050d0f0e0102060622150509070203040e060d0314161106070b060904060b06030f0a060905010509072304060905030c03120706020304060204030b1305070506 82
    0x7c00c800e240c1d440507503000100c000c01c03403400d035840540440c025000403880030215080100000c3c0b04001207003151102c2d1018105000e046858000c01100175005030000f102168090a0002c15001d201c4610558154002040800f030700445166080001e240e8140d60380400031800d001182e5900b1061500c0903500d0300e81800c04080010102a00f0b040c003034031016000c1c0041c14031815914051510a940140e40e4409014a031030303840184c00400e0f1941c444801d08041d880c0352400442d1852030f801483d00d1b22a66400f4100f16155600a2041d6445a100c20300801c0581e56031b8021827184168028008040c208001004201e40c1e490308528041450b0200500141c0e03909100300340c0c4800649026007802c140840a441d4502c40c400100e4035a000101d00421401d0b003141c0181d0990740e054003110341d113040c004209683c811180b4200485030100700404400701e6041e070001d541c064000c100140ca0183c3d6076441080320380702200d9800680e041c80140508209041c410359005140440c5d16500388100307803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 425544568 1250 425543318 425543329
    0x605420d0b2208120f070306080709110f0c03040617060f04020c0726010f0b0d02060a050705030d06080f06010506090d020a0b040b0a12020f120406021201090b030714 73
    0x90480740d00e28604a03400d07140c5401c4103030040503190348800210b0b11140e4480100b181340b00309981840921078454000307501c092203403043c80f0407118908000d00546107400c08044c0144030345c840b00c10808100308000f40b10700300483c005020704005d0304029a5102c1ca8040024419900b0b42a070b03a124095000c180001503494040400180c00119001a907030ba0b00009250324100d2070b81c1c00401110340702e001c0e03038000d880c01d000c1c4000385060301d0000780722002981d00741c0411594008201540070b10300c82c00303400c050b0810001070b1900600c1400e001d0300d080926101c8601d135800082446071328946482c0203000c2284203100440262105034000c01c41035040170000303021406003d034010301a407206090744042d0340d114048a401401031543e029625501c4410309100e80d0b20145030000842c2c0d540b2841519030380648211030303c1501c00411641402c00c2c11909680c014006001541c00325024420000c10740d109103842402810700c0000003a0981651080c5401c16a4651011280510703011030f0029503104c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 425545818 1250 425544568 425544571
    0x10e1f110a0813120306090c0203070f080313240e0627120f03101d0403031a12070f1508010909030207031a06010207120503070605420d0b 61
    0x440c100160266030301400d2007828500000007a0004102032101300314240c043e40078074140d4600d0340003480400104181680e0303900c58140010500c1460901c024080b404050255400c0020303d4400c1c80500a29105c1c0c0107038070b003481030307032202a0100381e0359285137006480b488000002d4500900b4030f0b0328001000401d1a0444030b8201e4000015604081c1c0240c028031011000c80b041d1194035880d0512403541129541048607096950320b0300c0b11002c50110305000c0707040e011844a0306504159959650100d01805124502c1007845a4180012001e6920031000c0510b003c5218018100700349404260303186000594030111071001c0f0b03800d216841503880b01820303040d41d12641000c01d841e40c90b807808902e00502d543c07020705624410042c080311022000c4506001e08001da003103c00840d02c070188641180d204400090081d842085510001038007070b00031542c40a110700d4004681d0686d0082440291070070300f800c0307050030303c4a4a40e40c1c5406595038140707030b402002e44210030880b159541d5490801c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 425547068 1250 425545818 425545837
    0xe0f010b1c03022505060703030b0f0619030903120c050d0c050f090411070b1306050c03060d060906060e070c0302062d130206130626011a04030203010e1f11 69
    0x1442c098290000e403013180d2a000419026001640c1c44801d420014000c0c10489600e510420442400c01171030318007041520103032500f1422010a00c058800250001d01007014101d0a00410500d0568510400d114040781d074002511829510320342d03000301508035641c04d00c8a4090020900850700705403401070a031201078500f5940000ca25120b5035034031005014903200204960020810029003c01e03010580c1d290798402c044c14805502c441e4102a90390108503000c07070300410042d1068002c176509400201885026000c00a802074a403001301c002158211382503000f00302c0e00000402003580c1001340c0d6a03c142d110a9908118203184203c8504c01e43c108140144180c1400200382446100c0f03034a03048565004103030a60700d001c43c16034490f0700800d9200d84c2011411008d446215030003420b00c1889900b480e601e28a040d68200088051510302c07002c81409607036405e002c0032006840074880c4000d01e0b050000100390f00f4802000210f4079210b100154541c03181411201c000b00140c07141603070000103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 425548318 1250 425547068 425547103
    0xa03050d0507051006060201060602120901020303070c1109040302010209030f160e19020409090308010e060a0506030702011805010204080c1807080a0f1a030d030204050a050603040302010e0f010b1c0302 89
    0x41c0d00d800c3c010315180c2c1c81c103e00ca140b2032500c04001540c41c1c05501c00000c0b00d15517000d551900ca4041c9500216000380e031810341c056041000010302142c410849aa40c4903c00c4658507231042c090404a02c07004400c07503003100940e44c001100c0c1c03000d2404001c2d0300640c4e40290001c141920a1190040c5034101d90f10074445034024a80114100340004940403001242a54046480d150b4403c07000300903002d019001c2d0003082000c4000320b0354038001003096204513805030510144030720309000e000950340f0040420f8110355807842004075880300060071000319806540050303206d50030090740f5424001500c0e4036902c1f601c140d46441e41e107040d004d80419841245428500c0041d81c46000c22030161400c8941440001d14141102100005400c1c03c2030540d04160201c4c0e0011040403029070480c459401b4507544440880c201300035074503220300190307409480303840003048100801034128508500d01c903500180d039456590600701c1e800c1c20640340e030380754810100c0c0756860851070700d000c0c1d180c591030092400c005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 425549568 1250 425548318 425548327
    0x3051203090c09070c060c050405010206190209030a110a1502060c0901031103070512010b03010f03170f040b0c06070c020906040513150623151308071805060a03050d05 74
    0x1c101c1409229588040030b00310f0010361504a030300519410070000c0c1102c42d586800315100c5a10301c24410741d0150399068005100c20b0311201d110f0321025803c03c024440c0300d80c0030040040e0684080c040204030310312541091150140d4282007280780d00868014840c4100b40031114207856070700040751034000407280c088030303560050480100c02915085407822030406000041c4404907610000034641c0e142034030950080c80e600c50100e140d580c4401e200b449400300c01d20b4070510105005d242e070000d0019086504622b80b18103005012803c1d0441c0c0e100f01d40011020407101510402032014a511103c03a1402041048103640000c000403000b034040f900850ba580f0000b40c01420410b01084456002009008045840ea004601801381c80c080c044805108461031080300400342e00c07030089144004c141c41c083c3c1281c0202590a5041100305070300705002140d0000c0c3d10ba005002060107000b40c403030100c03155000451007100344e603800380c05540500c1d01c0701c0c0300700040380e40400c0f82800600a03240c00c6a44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 425550818 1250 425549568 425549581
    0x10c021c0806131808031503070b04051005040e0a0902030f0106030215070602070512190806060706050c13030503043320060a0e0c012606041410030201030b040603051203 75
    0xc1c0808400004d881184194603010b1080b600007440c4220906003004000070000340c01e05480762410f114903103401c002440f05000c60310703243d6921200aa520318295040c2170ba03802404d060304500703030b420304845036035880c0b03607803d5040500051240e041c044000344040c61466004c81d011441214580c40030303040100d1100204030381c03601103c0725184c1100490b0b441489810340008268001840224201900700340c1071403240c0210001032181c58000c0c03032203060002a896017000790000a00020b4000304c00c0100320010783e040035140d00598040e07030041d920707a4100129000d92055202c03100c04181858441c51412280a10b10f501040c140791402142c1c041400d45001c01340b1407000a000301c02c0c09180208074440c0c0e91a030013001f942852404540c00e2400050066582500da288507800c401c940030f4a01d1040d03100002400d0b0003000103480010907020401c1841c3e10114152103268441c22606420415581e06000750100c1d100c080f181084458590381ea580ea9804021107504014113021001419 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 425552068 1250 425550818 425550821
    0x60e060d15080c030d0509090717040303020705011103130213020f0403050c0306061008070f050d0603061b031518090f051c030b091810020c010c021c080613 69
    0xc04041450003801041e448010900040c003080c010000c8610546000648600c4d0026000b2554035003522018a402e03060300030702100403001809130007441480300100b1180310a01090314401c078040d0f0340041e01c80c45545411030944140111a030120030302031041c443c1c4209640304088203558112940c801450000d030552010303000b410685c0c240030074081000828040040303220948200220706585813a6220410000c084600c400030000140d00d110020b40c1c520b0044201494500030f43820070506000328481c60f401990000d400031985107071503e000e10f5950202202c194a00541da06003444034100720003019007050101c0c0b195a08040f410440140d1142042e03002d1040d0316080400b0322043c0c5a641030041c0d652000140b40c1d00190845240c003200c10f0b01c603120706990840d00605491058440b400080d80f90b803011101194070380240c1b041c11140c44214401010469811800802e4603030060002a0034601407035200408140520000800b4650100355603174404000c071005403030804070300c00071070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 425553318 1250 425552068 425552077
    0x60f0e01022d100507050a0e0603101205010605030a0317100b03150a0f0e1b0705030403020603040203030c010c0f020c0111120714010c03140108030901020601150e030105010b0403060e1501060e06 86
    0x603103c42c6480240f082d15507200c8000c01e07810b0103545403104454211018403220344021506070103043c00104041c080c144102e20151421070046002003205903c810000342004d0143ca0f080b008076540b04441c0080274030080409030301c0000041941d5289290490b902c01c9480000d060880d0440b040906020329501c048196000c1c040c5000c0d01b503061030701c4400081c9104411355240c25082581001d062803c0040300455042c3d5030b01601440c00c151641e070030b0055940001d40201e91501040c4014072081900741700350200c446035680e8142100c60074904c06414021401d40c114100103400307640003200341c00020000307042c940c0b0740030720380da1880c1c942041d1441d6014803400e00019403c03c0c04840400c0d0340760700500b80e003010400381c5192a9a8403049113542e403040d1400c07070b800740e08101d00400202e40c201002c2c0786481250304148103109200d00009003110001d800500712008049418014891244903003a036007c0010002c4c07240f10021407810303141c14014030501003040b682914201c6075490380d100b40d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 425554568 1250 425553318 425553343
    0xa0309050703060c170408090f0d08030f040c120209150a0308040e0601020c010f0e090a0e03070c09110c151905151e010f030b030c0604060f0e01022d 66
    0xa8414940b245070000180a0b64200386001601c098215280c0c40c1040503154041d56211032134074500314980e4184245004001d0003154000d0302d140c00e03c0042100c5c0b400851003085244101029860030740f0744102e400e0400e0300104622182c0100d0000103031103101c3c40c2500401944500c0c18140d50b02800a1000161600003c09015000c0340001d10020406c4d0032600800098095400001800c001103542e41d000024101c001003448100418600f0066000e13a00004546008280c0c000303104100c03813466001c40c0c412901c0001d80c5504120381200b500c03418040004417403031140741c5800f1b1107099a0f40c041000f91364500e00550300204109002e10702440030b04041c5004140715614100540721300d5000808a458011a5201c0100c1000034401d0719040340e011058403500301c2841c2c035280403001428068103883d003600c100290f046c519a600d50191004000e15600d82a440c2c4540d80024020709408800b14190351001c078900d0040254030705d8031101004200d0200700b01c0f40408285a1030440c103040b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 425555818 1250 425554568 425554573
    0x21201061d0f150a02070314030a05030a0e070305010612030801050a0e010b0c0a020a120506330402070213090c0b09030606012105010305031306090f03060b03030d0c0903111c03050a030905 83
    0x121300b02d02da00480d000c41144c3c018079461411000c02408940c40384203a0b0320f40c2000440400004e201800e25074407a02510703200408940c0e4607a07c0f82d48290031520703290400395181107100c00400070140d000c02c1481c05070409032954050140781402c6e4100030030041c09400c8070003501007034014606008024080160b03070028000c00c01a5600c2d040d41c000c8202e6000d0548a6000f100c000a40445101c01d819025029407411010741c019803034481182480660718003944984c081100f2401742e510100700122035000c10a00180e255540d2604400e601c200758001e602d28030061003055400da402007000c581c050401c1c20701d480910710a190b00d401c0701400c0f032189030b015840c010000c801c0c06070020140000c40001c034012242c454480c101542c1510341031080300441408800f051000848607048100200405001c03282030080ea4000f03403091715940c0490100064901100f0001c0c0545d5000c1520f403120305440003902052090001648a0829280581400310000784002820310036804400065000360a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 425557068 1250 425555818 425555827
    0x30a110a1a040b0a020c07050f030316200d0507150c0807060b1002210a030204031505040201030b0405060d03031508100b091006120c0905040f021201061d0f15 70
    0x1c80090900041d01d0640301d004500c80040d18056441c030880b076a011aa500500b200340ca401c04012440302480040fa070140001d000b00240e03406527000740982c2510800c7d011030310031840d03000c0801594641150500c2000300f0b103121000310f10081030b0001643e0825055588502860388281d404048030b0600801084000238207800f8001190311903400141d003204c1248819881c160100d0f80c60503d51600d040a85070075107210303a503c1196008001d52001d508026081950b60b4a03489840d60b01885e1240045071034104110071036a0601c940f00700b520044030200183d00b081001304403902000c100003018581d40764100c01000c0c20034410840100340c1401192854002c003100d100240c500d4450141c01384d15110041034072181004520b80c1554403e907104140718020078407500281041c0c880e03030008d00c4001c20010495441d24001d01d816001c1d03e01c00581d40d01d001e04019001210140d200404001c41001240021910007422a04141e4200c402001c0b01e006000081c3c084e0402c1c6204a00c3d5400018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 425558318 1250 425557068 425557103
    0x106052b0e1605030d05030604140f25090512120a20011802090a0207020901060f0f03050c03010614040506040e040c060c022d12100c0302040503030a110a 68
    0x7040404561010000e8441c640010295444050414090143d1640100d44000300d040c1c4194080c56109000800100c0d5a005101d203080b490b90094480c014518200c10130040c8a00c034029011007001184258910b20810320b00004000d1446401107522a1075800841d600c842c2d8200042030000404e03480ba9560307035000c080b000e810405c2d5038509214400e007000650441c1d0030180302d00c0c147d5600017a4111110b05180c0e0030041c4501005145411440d070030f00018001da20389201c014041c00540d294030a12581c0c03450054900e0f1498498003041508002c2000034042140051703d0468541e400e00c0015000c5c0c9082c2c6644501581c0c0160f60046004140000c240302e5541e0310314001c03402504071046054a842045801d1018507601941010000270400c4800440c1803200010b1102400c0040c2e06001c51800a0388100c10341e2840c0905500203181c01445413600d11a12440c82c1d140e040c00c41c07074140f4180109843c0e00508034900b0601c520101519119401800f00c1407485602c00c082c11030940440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 425559568 1250 425558318 425558321
    0x90310020406090503030903100b180901020d050606031303120608161410020604030503130605070f080601020106030506040f110907020a11010c030806040c03021b060108060601080c030106052b 85
    0xc2c80b030480003400c0031100190900340402218400308000d4060b20340d160220300642c0180c0603403000144c1029508000c98894446401c0050050172410300140e40c559217802090300f41c0704050700b014840c0c0420002d200780e48810440c4414803940c14200f12081084540d01500189510b60107100f41c2c0c007440009000202070524003209580c0a0f2942019010b001e1050200c2102c0484802e00036911040c0840d000c20f014501a5500a503950b02020f40d040f4156124001d80d41c0c00d6552030041400c04060ba07412a42102c0e0301a440744082c030081022038615211240d844001400240800340510000001d10017030343d4003480040300140c038048180c05c280d54020360743c9a14810a1714080c1d5840541135056102e1242e1000302ca40503503943e5443d88480041000038440c11b0785101c1410740c200440d982e941002039446501407003004c06440e0f0341d0b141c1209941864002000c1c1410403011008100300707030410405807419214a807a10b00d4803200410030103151440c1c0881c00c144c0284410b0b82241e5404200e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 425560818 1250 425559568 425559577
    0xf04080601030b01060306060801140f040204080615220504060b090403050403030f1701090c0c020a121103010c05030c0705010b06031018050405030405040b18130209090a0f060e0309031002 83
    0x150f414030740943c0e40c8500c22000c5540d01d0042500140b428401000400501c40d2022050280185016110280500005c0032039010340e100b0411500a0350030464001c00c0d4840746a5040c1c2d003a41c0150545003c2180d1701444803015200000b60b030782e83d801040501030b280c0d000a0408002030502c1099041908002e8070a4010748000c41c00941d1204030b4110841c820041c5c0d15000101c2c030440c070056420180440c014050b0b5044403401c10200000c5100581e0350b281d40c0038018100a00c6590110621b410402c80340b41c1e035a00d0090090b1304020000d0300040e401400c0320740c00140c088040740c40b6509481e0041c090304000d0354240c2d22440110600480c60100c80e4144111503625191031a84401c0720804c40030790303100b160301074450b40041c001002507061640050040c80401000b003241e13994040c10070004240252510700f07c06141c003030480c00b141031a02c0240c2e04210b89030018070003603006545508000c10b03c04402400644c803503071040c8482d50104141c13505810020152038000404d08500300081d0007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 425562068 1250 425560818 425560823
    0x1c12020d06210f08031f23090103080f0c030705010c020c120607090509070912050d0206010e040804090b0f100f02010b01091a03071b03020a0204051005090703110f0408060103 77
    0x80da45a8481c80c0040c1518010300c0d80400d500c0c1a583c00344d1102501500024000c01c10024200241200e090032028000003614041c03e80d41c4405116190001190b5074806501c5d001e81c200c03c0051010071034500076681d454810b4900e2a40d03c100e035850a40c110302803130700028007035801e01c2580d004050700821010208007056524014245001400390340d50304058916201061031010140458104185c504d0340c4225981030800c0310b181e8031071101e024202444801e03591a000400300912007036060009a00612140390f42c001981460f4440350543d11072403040c6805a035403002d5803592030303c071140e034007580d00401000e043c10780e03044283c05000480c8070b004035001546400c0c00c0d942a98042c500c1001074403250940112048a400a641c00c290310281003182400407044c1c003801c101c0c80b000000c0754898481d501402c0345460620502c002d036a40900020361480442c8000c7c007442d01c625168179884410f43c640862070003561881c540291180c40e40642041c0360000c0c000c2850800081c155049a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 425563318 1250 425562068 425562089
    0x141005060103050a180303090501020903070b0c070b04260a0b150307080105070c031b050a0807110915062109010204031401140f09030904020a08071101060302031c12020d06 76
    0x540d801002400c80b11000174508100351800225000700c0e1003030b0311107803189114100040c644440e5100180c68080345074003420307596900140c01084c0c403106000321801001408503290130710781080c0c0c0c0700c01041da8802c99012010010001250006001c01805402c2034004450f00450b040c400b0980107032360020186c060003849011000503500c0e00501c1558800e103401d5031a84807515041c2c2e8111800e8007503d0f40c030528201810090004143c2c01e10521101520070b144080d03996401d4900b003007000001d18542c40c402c190034030400c810602e080249004000b01120340302e1755444070030241d01040034443d80036400e140b10f41040128903401503004009503070207111207c186c000789a5040c1e0130784000d250750103c55607841b0082400f81e40041042070b085001401070701c0c00c204410f004242241c01030245100003441440503c1b00950708001c540e00c0c18140c1c2d0000380210760035500820394610107502d10110884103201c0b00040310307101d00e03a1000a84148001555182c00c0044604007410b801e005909420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 425564568 1250 425563318 425563321
    0xe0403121a0f0108010806060d0204020403080d090b090d0909020a110f1006080c0604051207080102030702060109110306030a0803180106080c1810031707080309011b0216050d14100506010305 84
    0x3d42c0220030301412a081140141040c1e602d9805000600c02d4110003240c21540a1102200090100e406060490003410001807402e0290511421600010707040c048a50804059640c3d407a81c03154024040da01454005a03880403018012600d001d64801191a83d019007103905650141c04900c041c0b0fa0f14040c01309010726500c0d0405551101060401c072640100c08000402030350400c80c4103070750742d0948030f0144c1c1e034042d42d102e01c03940c00da0f80115142001600280018441c42015203c2c403581c210683c0c8150303041d89000404680d60b043c2a440c080c0c6585000b00004003420302074584848200e2240300203000340365607601d09951b81c9826240c00c1c1d204c0d02200c80c00d2820702e0300e01c982e120f200c0d401441207001070070701e1504c030407180480c4201002d0b01c000d030400802000c284a10020340c0110044000000c9071300d090350980f2407002209010318210b4200040da03109540101d0b003000d05030713001182c400d0500c400c0b81c545088108004201c00005d800380740f409161446c016441548a06d100b03890a100c103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 425565818 1250 425564568 425564599
    0x200a150c06061a090f0a2c1303020307030804051c09080114040507030308130804180f05090c220c020607020c0f0a0b0313080f04051c0c0e0403121a 65
    0x159255980003030f0b0f0b0880030710003c0d681d40b41c2460303044010341000e880c1078001c40e00c0d0710032060407848145caa40c4000540e001c020350a00d8075484d600b0b610950260680c00880382c41d983c0251244501640035080141da080446c1c1441828400441701410340c1ea00740c082c3ca100181c001d09000300902c1607594551070804a9401000c01c882801c0c0714030b034008041c0010700c0c103543d81540c4404018002507044082000b00b10001501c0c0340080015040c00c0041c01c4100480001c0c0c4000d54048803198800c3d070781031405200c00000b00103044070800310122450b805000010401e19040c001c440a00074034242400d00804107241c011031840e0040c80154244e8840d0307a4448107009080301d800d0400342d0007071442c0e5410000108400c0c040c603004559a6281c608071000d680301c070394950700111880f86d0350707410005003040a850220b11103c13092140782c2031081c004d51141c640c0342c81000a48108035403007001c01d0000c0e04151145000d5420036107500e500704001c0c0c00b8482640c21525035207540500823121000d14190 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 425567068 1250 425565818 425565839
    0x90203072d050d05030f0d0b060703030e06060f06090f01120c03090317041208070c0f141504080d0903020a06020408010504020a0806160302090607150506090f04200a150c0606 77
    0x582d81200017107103880c400c4040008158031000d82c80f1400c90307a170f81c0b00100c156603500052840702d00235507004c40e140740102245d5003801e4000d418140b0449c3c81010141c0643c03604410748a0449080707421082c01c850501c01a1000c001e52103007050b1451601008042964069000c990854026581c400a11480c0090350840502c1928003a2004440c2842885107500c41d2040035032040141c0380490559203965034100c0410a0744000320385014a02c10001d4003000d080118052030f81d1400010000d500b01500d5040c4c03984a040c0514808640f920b440900341402005440c3c0896840f41302195034556035076000d80205400d8034101c0c81400880d40000b030036170700080c7c0c0b6405003454a070516009901ca500035002944100011a0000018818540841c030320020203641e42161620100c0d01c0e1411008200d003195005101554901d046000c3c000464030340701c0c41004890300640010032031624040080c02030b2204e0782c0213000010b032394900c40701c1850380098a09680e6110700020700c1400d0f10754a1840 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 425568318 1250 425567068 425567089
    0x509012904021c0f0c08011a07032d1101090807020d030e0a0e0403030b04050c09190801020406031d07081b010504090f0e0f0c0f0d020604080d020a03020c1012090203072d05 76
    0x80323031440c410042341074183c0d10002400b0007846400e041034807842c1907022030003c020a907141603030f0700014000000929004a42200300c030644400030401c10703030517940d0f5902500078050f029000d4440304803150304060042e804402d04500040000c600c0304d590780720f002c1202c0001c4500714000381c203050341c10b0950f0a0900a8901406e80700f1513080c180702120381440500000c222808130080191500041d22120a02c002c00c080c4c00150b4012685610545c0600301c000703007070b100010155000c03a904001d209804902c00e540760999400310703007040041d00c00496050042e60030002032140382c2141090283e1280d40201c02920844090f1070fa82c0c012405113a89030030340303008000d400990b61520301c806031a000d10200c4090744010019401c19445101541c0780c42d9110780c04002580c003075284e070000c7c19010083c0b41c03045a01100c20321082c80444100500b201194410080c5494039503140c0c0d8110342e004e10404000c2c225a85419000070092141c3e01c0003204503002c0600b0b8100c0708140490b050502d80c0514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 425569568 1250 425568318 425568329
    0x190f030b4b060a05040e120c0d02010e0705030307030807050f040e040203160f090905010e0303040308010503190503040501080c0d090b071106091b010c0c03080d0509012904021c0f0c0801 82
    0x20351503603c0d11302404044e040204120540340600840e09003550300c004080c0080030440c800410300b0800b0400e010b800c40365a298a940d25500c000c04c108095030f000801c40710002c0c0d141c9064966a241c0c42810f58090185042c5000e62040c00308001c5600d04504081c184103600840460307800e420083c41c2d81403c10b2302170289928504c1c0d0f01d00140f00e010110b420030328844d44100b000082d05481e1079400c50842d001554100c0001e0b10b0341004204034a010850780302070441078002000103840175590960b0300c1c41144180d42c14004204001040c10369500141c4481ca0b01d0840180300f03001d40c078600307038603003e004844082c04074000780720100c0c4070071000544038030459180c8018070441155140842102d80485001d504005460321500000380418004000451280120a40303641c010b1341007400741c0c2c800515414050385044500c0d4003050a081c00d8245500180c005413450041d44c002040113849000940011085c5690055a0042040d8070400e003880780c150007000104808003040790050000e1048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 425570818 1250 425569568 425569579
    0x3170a1530050c040c0503070c0605071b0308010504060b04030203031206190b0d1802030606090a0f020c0c0f0414010b0306061c0506190f030b4b06 65
    0x74861184100034400514241026840400a03810039108089194180456641c3c12285444506040501544400ca000381c20018114036112000510240342c150000d0412078459010852190007107190000f40da019101c0408034021030700703014001802c28800e45001d80e280c5500001d82c404c10310169425070764001d01443c64410b132030010030407141001d4105a4455500d400c601c810121001d400b80080901e1000c260b11032980511000c202c415000d030324200c8801141ea543c0041c4c0d8081000d59001500310b030001101d884a4458100030301c00c0e450a5280b1910000308035810700c03400611000456000c81d81c01000a90000920065510104031034100b0340c44040140600c0c00303840e0282d54440d602401e61424a81c1c441600e0040f2071910000440f600e0b0384000f440142d08094800101e00e600342511030404a1500305100b03c00001d034440500b00e100c007280840c0081d0f5420300c621160800322000501c090000c0100d042401e040320700094540b52040e0076400413446000c2840c0d2061400905 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 425572068 1250 425570818 425570861
    0x10212031317160308090d030b06030601030207030c060c0207170a17071401020301090203061e090705070302160e250c030e04020903011103061905132703170a 70
    0x560030442c4036100b040c042064000e1103480e924004180200003064000d0740c410506081c02c02e095800c011599242c1410582018210107082d2070f60310840390032031030a20340140e40d08140e00307003101c0203002400c00401160030400c0e15440158005500e4064805464074540c68244c001122030b9200c0203840000c04550420084403020b902440107071888038000d5441e04045200d401d030103401c80c0d100340c020304000380e070101c140445410081000060301200c0b1039950009648040000c0301c42800030180020000006920b204151080c8a07080c1f501e40719100a0010035207404404150040803651107441c018003019110040380788981003010700da41a2030b14052080d854404540f00008450ba96070800c0c0c003040a142e0720344092040c4404108107080c1152a81070880c100b0500400340d0080c8002d045030b003002880303e070f610b403686188250f01c522000a01240d56102d03c41c0a48100782a4655038221003140e00103040d004040884100c442d103101035020358803002c040040725203005981801041109 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 425573318 1250 425572068 425572073
    0x20702151e1321050a0b0a0b04020a090315060e040b0103030e01050403110907141207110c061b0a081c0b0409030c0b04050f010c0302040810060317090a05090a0203060102120313 78
    0xa4012104003229403c000d40d403105403142480e001c0c8420f411244000364808011861005114020300890b0840d403c3d450703e05021401808150103010103070041048000340d034006005071f1b200d500104240c582007102490503041c0a01b109009110641c0854013004801d00c15601c120300711000e99a0041c20388004814041c140918003030010b00701e509003d083d64080e1918126800034140000f40444014054684030340c00070404c070040c09103602d85502400b40d5042c1680e9503001c1c4c0d0f401d001e0b0b17005450701659510000d40d1824034041c502414028001901c05d420507606c008440401400110500c801c50110042c042190034201c0040e000580e000000c4001402c040310441d0058021800c5452001411008508480600d50003a02180e800141044000c0080c0700415150030300140411000b0f1079074070390b04d000c5050110840c4007005d001170061869511030003907c01510028026049a1900346d900800035401550300c04d0140c4105c141c0a48610540300880b40b0403c2d12001c090240d07003066 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 425574568 1250 425573318 425573339
    0x114030f04030c0b04140d030e072318010311030c06031906030c06180e0106090501141e040305060906010312050a0c02030604050d140f1903020702151e13 68
    0x30707104508110300708200c03101062a03580d855018074090b0a61074500288801200c0c035045041c10101c043c0750801c0c0300040c1031003001c00c50004403900141d0313a01811559220456948146056081d0700c0614140c0401250048500b03480c10b0340d116404c2d00d0550944401015607402c002c8919907070280303003007000500b01d0b80c1101d410104282c0d050b101140040c2c40c4e0380d9041543d64070350004000500f50640c80b0340401c3c180d05144c0c1c0105002c07002e0700c030b040d4100b9000400c88852070255905021705060400301401c6450308503002c10158100e400c0c0030103441482c00c030b200c1d4024441901e007413045402048400710041542030490341d00400690608010410986054108407800c40c140300070450b0780d43c050b03141409031038412031045026042c1c44002100150070f807500c0300d5180c00080c8044c0b00300903000c031003042114400c0034602406c02a50011500032030180c401c0e03820082d00709107000c000300800070443c1e000d41040301c00441c1a95032840301030340700d008501910384212510409031030104480c0d80310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 425575818 1250 425574568 425574571
    0x306040f061b020d17010f0b0f070501050a0603061b080f0c0c06091c140a03090c0504180b07051602150f160605060f21031606020301140114030f 64
    0x200c0e004580815850b0740d0506510340d5000180242c0c0120340250849680000010304100c0201450641541000e4003c09944614000e444850b64001a1600343c01c10441c182c550b5164080001d00c0a49818204080540014031080710f4003070412650038018003407840700f41ca0111050340c0c3d240481e556581901d1035104060240060000108017601403c2000c1c054588500c42c0b250051580c96a150403800c5484280c03421101085100100b02e0300760174140701203884910080c500800d00c0e10311420050481460b61b440158480d00d0514091250340141c0441301e501e40c06500502241c1d92071420982c0c0b284524805111071460110b20800149091a00108000001c4608600345600c03000040c1580c0d22110b110798808038000c611004100560090030317800030085c0d44031801090090040b5080707002c0c1e4089000d16140d135030b861245000c4100180e4007001c0841103960341c40500f605002c000dc1d4000c3c051100c2c00100c00304400c1055004800c41907406100c039080030310b580d0300d4140081c580d140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 425577068 1250 425575818 425575823
    0x22b08071413030c0e1308030705190806010f18051e0a0e010f0b0403020d03030b0d051204080610030c060807020a02060d0b03150f0a150f08070503060106020c0306040f 74
    0x21038100000d00404501e000c0c0c035041041a40b00c82005086042508001d203c40e440342c41c21010b03210405c0900c124a42a0104003a84642c01e0303622038692200950342400b5040701841c0942203030108407401a40410300324040e900a803500410513005000032100b03400c1c800ba0110394041d0b614002c21280c2000c103602c81654030403100150100ca0028000740810b10550b020901c0100c00c1c40040c404c2d9550241e82c00c0007000d14441e000c2c986031650f03000c2202076030010400b070107050780e42c1c1460901d91116690140d400340c0c480d0540c3c5096008940002081e0028000d804c60741c130070580043c0c00004584030b4142945d4211143c460898513006040792000c800030281c1c2d085014901c01400142c4074140581780e8501d10040101d034034041c010906d0b140070f07201c0f1081c9040003400410303ca15444a055100e41041c003100c404601c1c816140094590b00c5503650140100041000300090000c50104000040d180110150383e5266031307919040b0f84c0e5044440a03c1d50581062003c94002000d00e030140d0010f03031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 425578318 1250 425577068 425577077
    0xc02010507060f0914061302060309150109020d0c02070b030c130f0602010603060b0603040309050f0a1212031103090312071202120a0501062303150603011203022b0807 74
    0x41507540c92000ba02c110000f41c4101580728403544041002000b500300c202c0c001d0740b0003000d05140048075000c0ea08005a4085c8c0684000408182960340501c03406000c524003040300141940e440308010025440741c880c0300e03942403a120180c00fa01e8804030b071110880c0e40c0d43c80300707508584404c1e1070b91190b0341c4080410422450b41040c00164000d141100724014040381d000083c07140d01d5810507506035072928090b0f91003540208200310000c0c0c1c02820102c1a81d84c10303034202d2040100c69000c2644c02c0041e8101c400e02d8020801d2180400c500d07a0010303c2680d055a0f424030004611230344445280c00103a0f0100c0d080d40051107450040482c00c10b009901c0596844c1081e880101c0007080c10407170784140c2d1a580d60310b400c2010050401840d00915004003180c0c5000302c105006450440e4460901c440746c810a41400404a03ca0141e048c80700b1000000003800c1e10340c0c1e960345900c1c1e0040c0000d1040204d025000b0401700155601c3c1c0702820010003040c01c4505440800304a8040340c20840c018461003c2c071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 425579568 1250 425578318 425578327
    0x307030b090c010915020615010207050301090b1006030b061c0902060a02010203070e03070b040504020c07051504060201200703030e16080d09090c09030201180513140703050609070c020105 83
    0x6116404000e028205070340c09410010300e90400144440204e40001c400c03030704200705064525a0004000b680802d583c55100c0d9a0720304a00100e0428a4a6001c0f0b03515600b003a00341400d21001041043c05100500070030602e03540d6403170301901518401303101309500080500651000d6114694549540c5401401c001031911b4a540000e032981c110030340c8600182c0d404000c2144090f04120040007204048000341441442c0000c80101c51180d4022140641c0e000f040d00040c6000030040c010240000522400c010f40e80503440c00c040d40c0061040c10300543c03c0c40071907200180882a0303050302c0440d8540c0c2900d010030546080d006000343c0702e10414244140816555440c01e0840300801a14005000d800003142002d8003c041b41e0050700311b85005031819042031811354121004004036035080c01c00709407070b07190641c0c5998201c515502a0b60400c110100741c034122400b07a446030810302162111810b0b9502c8440c0200c00300c0300100d50082d00b010300500890041c500507185042841d1052404502c0d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 425580818 1250 425579568 425579573
    0x60e09130c0e0f061909020a0201020d020a05120705160f0203150f0a0e120403060b060f0d0605012c0f0415080c2403010e0a0e0d0c02130902030303010b09030703 71
    0x40070000d40c00b40000740310382020b00c1040800da40c8210b0304203a0848888240c01481a809680c6024610601c50115400038501d101c041c000e405030340d12418644000c40d21229100d41c0608144e0025a48203540d0201138001008580035001f40c480134096a48111510aa180c3d1052116484050243c0e418495601e0010088604502c21441400d04c0d40b002d001c2c034281081c805095440640303e40c2d501d0313001041c001c0c1644200b101035a0072290007200128030311180c000419014426900700c03401c00000010344100e0703d8030030b8014104079642070b65400079040d000d44952501c00402c010b2003056805408503041e407441d100049200e580401003002030042c0140780318090300305c0503511800054201041c0100036281c40041e41d40d0f010900e440803a2428024071500c0b20610050048140119200b00841c801001c60303400350424441602c1100c00d00d08501c1030203400c40c903403148128810200385020542c115024020050581d0f030280c010350840c0d01307203c1d07580707010b070848401d680c0c1600c19220000701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 425582068 1250 425580818 425580833
    0x4270f060603021c0b0a060308070209040609080d02040e011a0a080c0906160b0f090a0b0702070b04170705010e030c01031e05010f08010b040209010f110708010c050a0315060e0913 79
    0x201140302c00d8541210840c2c2e45002132085e24001d100040e0245805c500b040801e01000c100c9004540c102c0f0410025074503440c01d44d00a103600d02c00030703203241d2000c5494001c0207001c0d0b0092041c1c0c3d1805078a4030040c0c1e82c4900f01c48166900124a220706241800002d41c0e0301e005001080e000001000e260b818084040302094032074128821202649402c1c01d828000e011510705901d030030049201824860385400c0101e59515a0094070003401c01d42c9000004040c24404e1003079801514210700301a5460780c1da45c1202c9100f004041c000074003802103210001c1c2541c0500c50321b1540307402c050007030000076800000550080c24041a1079003032407201807258620034003d2151601900001b4819200305052070703901070031a10042015401184100315803601c070ba07008000c41e40c600481d4507024131840f40411210f410001107a00403049982080c184a515540000c05002e9840495908100d81ca103e81e03100d054940d0f0300e1280801144948000c0e820500f0100101680604005003042c26850380e682d0790030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 425583318 1250 425582068 425582089
    0x17070918020702040b040908070f060f09060b190302090106181206020c0607030207050a0611090a030302061b03010e010b0c0a24060803070213182004270f06060302 72
    0x100e079400103500301149018070400f010440b0684c1d0070411441c2d6961007440b28810b03004003411540c4200f01d228200f1400340c01c5903c0c046c801d0507050052907078034035001014000b100c6265100d03d204c000c60165a200c4c0801d400100c0350010402d5603507034604a02070f07403038038006144520f40321401d200110b00300d01c82c1641010b10300d1151100580e10450038007100d08090000d05400c1c2050b004125180100f20005600540180c004400041800402003101070520401b4a49500128070060000034145c012a540d0b109404103e02405018150302c9550907601c402d0040d921920200001030081c62045d0000c0c0c40122401c000711000d0255a444c0d108405a00112001e519140003000080004aa004000007854060001c5092800940c0000e440c84103424000a4a56071008509034410954141440e1240c00c1754a04125803200b0301100210710715580c4a038099800c0203440c101001e0584240c0c46040c0c4000c490b142610400c0c1e47d07421090f4804fc1c0c0a0304c40c41d40702c2c078001c405651010a46e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 425584568 1250 425583318 425583359
    0xd030c0228170610060f0509010512100305100b01050706050c0c120c0115030807020411041505040e06010206040203070605031b0406020f0106060908101104030f1b080d170709 77
    0x800440112400c62850820f00400071001e0241940040101d1500030f422000c1098450401c15101d80248004130390b0390107880486000e00c20120188640d1849000131178081d00e000d107054503e149071182070202034807003c07502c060000d4800c019181c00304174030341d02c16600645500c403140c0c500030500c1c59081c0740c42003c40c0305140400340014029150102440b58500d04603229021030401071841c1c4442026008010010f40200c3d00d400402110000a104503000f4000708108081000c020410040140c5c215001b404c92940071000403c00340e60000540c40e1086a0007070082c8145410144122019003002e06110f0300c111540a45100f2403040c0710151000d003100394001c004460401b18024207690055024078284110301505220b5008081800d6001d0540b00d8808100300c080c1c1c6028500a11a40e48040d1001400607411410080b2b20031404030913041c1c031030b5802c00c4a9100c10b8003980303c04110340d01101051301c82e821001040700c04140b40b40d20054500b0013540359a031741c0c08040b568908003240c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 425585818 1250 425584568 425584589
    0x180d140304090501060804032c03030d06090b0a0806042319050d1409011b0b01121a1311030114040302160e1b07051c050403110d030c0228 61
    0x380480c2d000d5115a0303004000c0c0e80f070312041174102610f015200c0c070003504100040c1c0007140d04400c2040c0b40b17581c0341a002c0b000541100d42e94417101144d07c000303100c9400b0b0700c800c00382002503201081c5840d0aa100544940760058a0642ca0b641d6818003010000540310f9034a07090b00d040e070081034009000d1040d4580c0708032842c0307111840e9842d041d4100418103003180d0500c042e0718020f682c805240c0c1c0070f03030b160b00c4428207014003d1200c415502405142441006018a00106c004103440d403c00c171610348164442c0c40c6d6403400000f865030300140c01340212004115450345554100120b140c0d4488400020400340000a906020580843c40500102c500f0f07005a480000b4a02810750040020700040038254400035550410a0200444641000c2652400200410000c0c240282800031035600c0403002c0903070740701d2440303200e0160958000c2d1000703590005200c468405981800c05c81500c0207a41541e400d0061070b025820013244c15061045034596454019a81c1c2d500c1a13860015000390104404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 425587068 1250 425585818 425585827
    0x803011815090b0607200916020c040513060e0c1309030c08030417030a0506040b0f030604021e1003050441030906041d0901060b180d1403 61
    0x81090400050500c0000040d192403841e8600d0a9100160303001e5416407000494140903900000c0d4aa00591030090110909200303120040b8400000030003a080c0309503038051290380c0d642210b907020244101c401c40541c002c019000350b075140a80c00a41d0103080c17095400b40c3c0310081c0c0c450208550460385046000e6000007d14200b5280000840410040181c0c0c24444101680d40042840ea01d44800078100d18001c0040360030045036480700c40c488096110740a807a0b00c0e00080c01c0c40903010554084d80200d1500380000036605100c11607111a504c081d00a044545856007444507014424502040050110b50030701016501c642070043da1122540d00413486061500380b0780e580040107401c5089215a820707948503591503440c071603506500040c0c0a802c01103d1965091704500c119504030f07030311200025011441d9003000095901310b0443c5140203046681d075000544c01c8070028050700e5610001440800314038200140c00d0801d20303101408030507450100355503802002061440030388507070b040402d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 425588318 1250 425587068 425587079
    0x40f090f0c0b030108030a26041b08151303030b06030c090a080604020d0816020307030b070206090105010b0904091a01030605090f0a1a04021917011505130b0109030c03080301 77
    0x10079040141403401081807465140900c5503580b40b058100c03c4050000592901c1c1d04000301aa0004411901c40844c0c181840c00e45049125090866a82c0c9025045060086649803000660740d02071201e4070342007482030703e507510f01d04c106080c01c4100305c0401d83c0380e030080b090b142c0f03d2101a60240c1121082c164030b03210000b082041702ca5046d00103843d5684410104000b50744e0b41007440312000d40042d0030300d41d90009445490844040c00401135014416a0000000c00c1600524244119996402d0f80c546840300d40020382171b01c600f8850001c01c110240250341c02e5240c42e034001e4103050701c164080b60182000b0100d440c8804000d9005445956507101001190304060100101c5050104040d200460066484404c41e0010142c04031a03051100d00150454680d00039900b40090a1740400300d02c00c1d40c0300e0140711071444500b0507003e00c2d400d0000040b060580701c120b180075111300404041c40c1c400c1e00a003001c02415041c5840d4100f01c0000c00c0080800e10803220b840142d8014900c580e501e60601 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 425589568 1250 425588318 425588333
    0x3090d0c15050f09040507110708060714071110050d0608030a0e0a0608070315080f06060109120f0f170c030a090f120b04020111100b03010606020a05060114040f090f 73
    0x4072603007003030141c01c02910000121200032511072403001c490025241d12401b4044a41e00050312551910b032040e0f4001045000001a030f480c89001959605400070327001140c4000131b030050030030041c10000c0284032624286007a51200803103030503510b403540c10202050303d4442510300d554403080c155000065410b000300e5100c2e0f40741078034244c242c0e005515580790203001440c140700105548101540c806486606a18a0045000411044040341d450304044082e054071541e068400302d000c01c91604002a01c1912082c1301c82810380c100c01c41000f00c0100f9268000c0d09410329000f02d0342c03001d400c040d42605503052000f40c1144141100210385421a00102800c8071900e03030405000c1040d6110104400c003a92500d040300d26501418a040588071440141c9010713003002d100e92410300400c02d1800003206654010079406504400034000c440c0d49200990b00d80c802814054601c2d00030707000500c4221208050105400e40181002984000c8900e00c10200c2d80e0019040360480901c1c40e0890a0090380c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 425590818 1250 425589568 425589599
    0x2041b1d0301140a0522050c090a051e090c0306040b0a0c08010b0403060b030f0d050c070e070203032a0a030905010510210c0b04120c1403031b03090d0c 67
    0x7078000f0001e00e10f10240c00d114080d401410742c07490540b604000703111704d6103008114040c1003944003103540c00c0201c0d00c0d285071a0603580030700328080c2480d440001c00d041ca03a8060b6500540c070340c1d8084640001030b40707003090214400500061080c403540300c1142d07141e181040f46621940c0681d00d500d5040c10079070302d540140c03126000e03580d0806c0071400040c0484a006001c860807a40d000e0000550600c0b02c1740403038100440e41004504500403003410407140e03608900148a185010803c0c0c800c0984c90717071410300c0282c600b40d9004c801030307009000060030a803105150101150a4074502c40301c648605250f070400750f000d002447c1c0003076114100710080010034060030303070444000a650304005090040d600749400301c03204000c4c0180b08401010b4144101c01c4000e6010340304003110565141d4442d9001c051040d8039690466036050350a1000660101030031840c6e071540001006549450310230f104c1500700c01d030321141310700303850000b0840300c038642c0d0f140c61140c01d5583c850759081102c98544404224280704 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 425592068 1250 425590818 425590877
    0x3040c0503060906040506010620071401030b030105100303210507050a0923090c0f04030c05091e06060f09040f1a010c2d020a0b04050907050705060403080402041b 72
    0x121300f0702000820101d0190305540c0a46440d2110f01e140c8555030b90043d803007540b80f10090003200f8002c14005002c00d1035040004007a01e01348150b07040f2000b41403c80d03004803540311540c3c905400c1400064030400030b10041d0000c3c080042c4400c01040c6400303088801c103944100108000007204405243c2201c000b100804598603181c02c0102001280800400c60340e05c1b551080758600e00207202e1810a4056410115040000d180c1300c941304d160003482882c15000e81442046443c000a42011101d00745501c1c250000814400c151240024000341c1e4101c6164502e003050103200000440d2941e1240e031280f40c1c000c00000c510041a514200f18402d441b0001504220341e1001d4000401c1030b1024014404030381c1d0400c4d00251030900380074000b40c040d5000081d88202600400900c09055030050f02c10307104110351800d960707142c00e44d00782e500d1721840c03e00410607007201c0000340200e8000c0400591260010b88003090303060100315012040c49403111480081600c01e8240300006064008080321883c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 425593318 1250 425592068 425592073
    0x80303071d01120903110706081905012102040f09060203041b05030307260a050c0118020a0e04050a02040e0d0215060a170f06075f03040c05030609 65
    0x405400020801a0600200c0e00915100e040c13400403d4850403044a18007a0813058403d4140c0303c001c000c00e4034030203070b440c2070003480d100605115018003480380301e040741c501e0704010b1684400711200da62980074070141607a110340c0d84d4550038100e0505000c0c00e015184100d2005980346446d01d41a00b4154041031680d0510381c0c807181c2807046850000407200f000c0d42241cac415080071400c00d11000000c44808400c0c03043d100c00300e01c180501e60881e01404840c044640240b1020441962100000d807441c032001c1d5012a42c10710410803862002c0076690030a0045040c0d900014440c0c001c102625251000042c1e0307035104100240e0419411700c280c516801c1108104101800c141000880c00d4849015006c201c4d1007440c090031a000307040000050902c0c80000b41c4002d440d109d40c0182101c07205104d04183d940581c01c038040c4400044c01c03003001c04030188294400d03000001c00f1804036515817002d2842480108001e8041103000c600c060340c4502d101c3c5400d0103d550605041c135080c850040c2c1603427481d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 425594568 1250 425593318 425593367
    0x51f1b020a050d14071505040201110a080a080705220f050d02060708030c0d05070309060b2e0c0c090e01060e16051e030f04120906080c090a0e0108030307 68
    0x140b012030381409010507890b0050a00d204000740b403140f0b200b40c21004020340d052251000c28882d040d04607d21540c000d0f2540d0b0350706401920003a031206541c020080c09040304004000140b8040d16019401007814a0402e04000e009a80c0c44c03150704010702c007604078805d4040c0070000c0b0507040c0318440103000192108004030300140d001c82c40d1401003c8000389104404400560712034000d506031007a0345051748013840346083c007403005002080030600a1711003e00b458000c40d403900b400c01c035205083d9080c264602e0f26001c807200c08441c008420f51401e04004941100034040b404c101d9030074029050744840018140f0881d40e00a084035061b600c05074074800c5013000c000c0e40383c0d01e0001100640c0c2031418402c0e65504000d54038071206d005106003080024004c0217010801aa1806a41c450b501c07030304400c2605400c800050381c11010510506002408080000c2c5282c68a00060015810007400030070800b0b0311044c1c1e00300b000b10240c011100b070b45e00210801c642c00d076000404a4440c0202813803174000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 425595818 1250 425594568 425594573
    0x9150c0b15150711130b10110307020d03111f06120201170705090a08010b01090602031305270106050c06060a03020d0219030206040f0305060f07021504051f1b020a 72
    0xc1040001d0380915403002c5620f006000a2002d20304480900408041004c0c1d00c2a80c80740040070383c104005e00401b48800c00324100c5004181110b49402d000c0001c60400116600300000010f40e00001c03030400c219503044240401c405c1000009078641940c0304002d03c1c604134141e50407101d003640104200c52038925a040984d820011008442103018600d16995075042e80a40f000d205030b4103a5034000c00e6580380051441010340c0600c104004c00d907070710ba0364595544070403a0340340640c0780d40f020000fa007040104005e160111200084003c0404101c144249240040c0c130741c15002d1303202c540412800500e00210f8030040c031080764821002c840242c0200d043d0340200c1c500403401d0000a0140401d410b480a0f8101c4900207000110360041505954640340c100122032901143300403540c6105a02c0450300c0800104a964442d010b00c0e4000d0210200090030b04000d0301002c1d00a50741405403440d1001103c4d000d15409401044440003c1104200c50b00004429201110000b0454000b003848000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 425597068 1250 425595818 425595829
    0xb0603040209100b030a1e06050f040e0a0506040803010e0106090b0d020c0c04110d0f050112080901050c16030b0612060a0b01020f1609060806010f0501050a09150c0b15 74
    0x400035010b403210b058941d5656200c0f4504101904404090480841040030740359064104200d00f1007030f4001c008413903850a41150986149000b0103501c407000390100075060500d1751089507084046070484090090310380b1a2130812109940540d840c21001005000050b04564041d0040800c0d00e041a00705241001d4580705000c0d88988202850700001c2d0408020020001d0400c9110002c0c8100a8000101502081a401000e102c2105401c02c100c0c46c141c415144039090484840e0081c44910407040d580e002600d070f02171301106052040612003420484401c00507030a42c07807035192041c0e0742c0d9821420030b14103034000201081c1c803642c02c16040c9001c646000c14016048510920003181c1e0702807100060342040c1c001010f68805204124484541d50345d0308801c001152035a040c1004040d4440b0880390700c0b85024003c0c56020880003400300444c0d4070510040001c20020b00e0107555051310356030405084200340b542440040e0012940300c05200e81c15111a030442d58174407210f1000c441a001040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 425598318 1250 425597068 425597071
    0x71e0516260f090d020d120c030e0109051c020402120a020904060b07050a121407031805010c05070311040603120215061e0904060e03040611011107020a0506090a0b0a0c03020f010b0603 81
    0x20b01030f81203070031100219200c440c040301940347e01400560310203141200003020f6130f000b0070080c0c0000d0440507031708445500494044084e04c50181c030251940c3e0640781c0060501c3d074040e004a803c25820803001c0b524000d4840300c0c03401074910640140ea291030319030070001036446603001100c02c0f00b010850031000800020f82c01641990080c20105400c004c86400c2d00c1c42d0500301403003119071000040d1802059031003010280c0c4003080c0c22560030250386890044412080d07032180108154070021040c0049401c030300c0b800030a003000410108076980c903a50b4203680f000546421901582c00208180454030300782c000c1c25400042514030307a107001030f1449481085450b0004035409500b031800401c052100a810086628880004980c0d03115500e1400410302c840401c40c2d0306955203003005c0d0308114000d10040719101038008105c1c0c0b02042c00d0208006c4240d01c0610f00710b40c010403501d00051000002400f0740b9074080151102e20455405085c00b84c28040b036038010060503450070060341415038030703034040d00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 425599568 1250 425598318 425598337
    0x30f0a060e07140904050c041802091006051e07050703030804051b06090f010309060525090602030f1c0e07050f1c1410150617071e0516260f 62
    0x410094a03181030080c1442c91090855400a0406c4000c150141040c009c1a003424800e44454003940d43c2c90581c2c04e0311481ca07004030310004800f04504500002d500111a4603000c00422580c034140c03541da50705161a8041c1c0c0304071302040e000c10400050100074031604807000e019100c42c07000504150300140052160140c030034481c85200404580907482a07228001042c1d001e04100910b080200d00040010204981c60f01c100c000f04146c82c00c0315115050241c200d5407250000d605204850300d01081d00d80100490031001c0d100803070a4980032074140203104404100001401e9000d0400044c00102e00546c0420750160000102e4083c140a00c4140c140c415030708459495825000382907a5410440110b06812440d03052840c84a20300c0c50107c1480220741440e195280c0900a90107800c00001c000c4800801003030340e01103400c1405a2008010b80c12100e2490514907000944c0d001c2d42c00422207540550b0150202d5140308141d090440c41440f1100500b10302d10706011031605250218841c20043c2e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 425600818 1250 425599568 425599579
    0x32d070305130c170a171306180e15030a03030b030c0f0102120a0e0307060e01030b040b010816050f040b0d14011203140d05010815010510230405030f0a060e0714 71
    0x503c604a4014446004e43d00e5000352910164090300c80142050740100750039101d0520003d100160150040725042d0b841c1450322010742d190383c03424111a070ac01400400341081e14004010001a603034040c003007015030710300c2a14006014a88030044c1842c0c08904421a0b0082420400500e40c80c0e0700010f01d4075100c41140320341c03690f46c01605800c84d203031400090000e8161054907008200a508505170700310241d0f00b81d07410040340c2804810082641c90214a00c0d0101d050340b00030485c81013045405010380f610718200721786040b02034901006d15900603480580807007400701ea100145090350046418100d07040c4215080d40d414041c228018a0760703028010184152410903100070424001910780710241c000b01000650303550141280c1b00c04c080418006205454000414030740780005c50b052006041e580c0d6440c048048401444205920103e1101000c1041c000002d1039601008807104032040130001e013850030400e1400d141910f40c440082842500038a800303200c0072031100c4518a504800725203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 425602068 1250 425600818 425600849
    0x100807061202160f0804140603010b07030f0c0506090a051c021e0a060501090f1d0c01050904090b0403051908070203090402070602130f150504051302032d070305130c 73
    0x101c11043c0c10650070001e050000c11500101030044e84000780040342d03440b9825042ca00403400c04c000700c92009003d8980d01c680c0a01c80f80340442d1182c0c40c0344561040d5400c20028200d403d8540d0761034441c04850603106548890308010401c001484940d24244000700480803000c1c0001010352220580c200c540c90b461144a10115001c01c20072412140380e800600420041d6100d07200017018090550b4448120790602c80804640300e80700340841008001c0301c002c1d0103c0c01c0c0e00001101c01340c2c0011202a40240c0f00d00540c80400c10b100700003070040707110782c880e41c0c0c0c2c030002c241c141c011414521403002c0a00411000308042d41e900441101e0404001f26401a9140802d02d481c038000e0240e48108142d01700c4550010070707a101c40480382815102e20007040a511494110115180c3c4501e01499410030005100d80e0504c0e00150007464100b0000101c40c603424103060602800c041c12f11030035070302d4454a6001c0c04203658051160b20341000f403070121181e00c6c1400340c079098210740582c401d82000324240741 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 425603318 1250 425602068 425602087
    0x1b02030715050d0504060b09060d02180a150b070506070228020a03140c1c02060711060f030f06011d0121060f090218180406020a0507060c02010203100807061202 71
    0x8089407516043c0f258200042d081c6810b05800a051000300a4051000031011800a03d1f200c40c80d01051a4000d001c1a40d40b81c1200c0d801004e803c01401c0c40d81400d0300e4252003024046007450302d8020b8108041c0785522041c1e00e040c120b01c2c4c0b0401034044000d5400480d2030110040715244402214403001c542e9041c00c00031762021851802c004e62002d8946800580740b81c0b501c0744040340503c1d46c030702d0884416801c020840c40e249a0202030706c000a5004c20100010b030001021014803003c505d80c010b094a04102c0c0d00307860007036507030300440e4010304412032141041850341e002201d20b03a0844090745103601440c0e0100c00a04003140c880312030340c0041e01001c05840006196000940505060011002c800d40c0d00c0241001a400000748e0310304141000c1243c08450401d804245054040c042c0e082c0300c60307200ca0300d40400a510181c0700c401000301c1007003244080390990252030540381460b4001662454050050f034103e40345030f04020415000b024080110707079070018003800000c10100c00142c0e9142c668 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 425604568 1250 425603318 425603327
    0x50603010312050f21010902040f0501080a06030204050c071401050f01140d02030118030201060b0c1f151403010c0f020d12062c07080126010b090907061b02030715 72
    0x2030500310140c290000d01500c585881c010300e25a801c0c0000005d541603600c6102180a81c040c50081003101c0a2212082100c0d41c410f80c6501c0d008104d00c0700014103543c40c2e40115003660400c03920400c00710800501c25042103505070080ca0310280700e000030411410302a02d030150003070703040c414140c94407070308000b00c0084c0e40d855412040c0c1c0d13a402802046030013004208445203000f450000e0300594641100000d91403c10000c03500201c1c1304038007902100d5022048008803964500c0c1070031541d0340d100ca0140c50450f01c44c041901828441d41c640c0741c12242101050b00391100030030ba400030049007a188058854000072400780c10307546414020170f00354908605034020130032580118200d98001000021503462054080d21140004145000d556251141510640d100307100d004070100701b120a9a524074004034014a1011051001198008820b030000e81e81500c19a4050b04681100e4030070000c19411241c181c100601900d0414001c9429030000b03504ca44603449406040c0e40e1600c08012010301c038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 425605818 1250 425604568 425604577
    0x307090e101d0c0d0504061a0618010f140a1e02010e0d300905010c18031b0905250216051003060b0c073023030a020a0c090605060301031205 62
    0x1300300b0704000c81e261600b000c5001e010011403c01a1500041c880c641605080d0116021924800c20158558207c4801120b01035205c8581c0800c0244031845502e41d401040b0040814103150b540d201c0e000320b20385e000d107044d61161400c1e940c150380c5000c54a400c01903001c00c402c011190b890514a0b05080301410460f08405044000f0038014a006a070320000000d5520150426000343c000f003140e18803410080d070362250071098440e10203c40c040c1c00c20005d4200c2201c100900821030410812aa0302d8040e9400d0780c00c1070300e5501305542d162100342115950030340e8424006000e88014500c0054018000d40c600c411030180070b02869a00441d2481c00d03010390080c400030a40c000c0016503270001000100d40391a51401001c016428244924849400c003088d00d15034080300040040700c00c1d45540c0e90144c03e030b200021a0307400a0100c207004010340c0d42440944003206c440d8018040450842c90300303400c1140c0302e42000c18442d142c42802d001c55100c44040d04e05595103c020036954090000f030586181c040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 425607068 1250 425605818 425605837
    0xf0d11040b01091a070b0108030307051621020c31232401080601120e070b0408010e060105090c04060c030903021908010f1e0908040b0307090e101d0c 66
    0x801d1103189130190003800c0100f00403070242c000e80c42d046e603d0b400000e441e48401d40341100003820500210134410703118180d540602d4451750340e07001d1020004e070700240e49040702c0d800d0310050780000001c1401ca0402c0c0300700d01511995410120b840d03c07146140d03840c00c2d060116142c0c0901d651610724085120103194904060404200c5200141c81d207804685401440d8101c0003a114010100d040481c1d40100d00d054004c5405850b501894222009188001c4c0003000001001c0c0c0700f503602c0041c111007071100903c06002140d0000c284031030380012207442c108c3d042e0300150060114000700014000e43c0c10664054030703907030700e401e400c2c50855060072104041c068001070342c4100035441100b000702e140c040900465100000a000803203610701d10400b00d481d51000c2295010040f0102c2c00e00c543d00c1c0e400591664031805c5800d0a05458081c03201141e04203c83c8400070400d44802030120200c4050103540c000c90b40c101100030716084c00c00c0c010940407440c1405d0142901c407004101c1c10400d8200366004040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 425608318 1250 425607068 425607089
    0x7080f0301050a060804150e0a0b0403030c02010e0a110d03120e01020909060102010203040c0e1806090105010801240905132010090e180a140c0f0d11040b0109 70
    0x4585004410354001c0c4141803051400907000030ba0f145c02500c1c01d501c81c5030058400300392028507001c0c0c1d6018001903001301103280070f48411440020345851180b40168081d0740c00144840c500d86001e03085a00fa040840495440360704c0c0a4001103000e007014200450036140055207944074901aa030000c5503d41943c2c1c0c2c181008170b00e010401056002e07000039442281c0741031a989841d801a8202d2000351006018035501d0301c0e0a00c445110b00d0201c0c0d4010501345000f80750060250411030a188080d9000d505030703511b500040190b072000f40940c00c0e1050159042c1c130701c40f04040c021030448d80454400e98505689490006007024018414800c1c01e903080070203115040001c0c8083d00321420504902441203048107500110301e48034810740c00581d151383c1e8014400c1e4480a102c0c184034041c48440355501d03c250510080040d0780d900300c1c071000c03c0303450303001702071401c4d10304200000c104581c6100f90045240c902d0f810b001c01c03a80000d15141410903200068080c1030000100d483c60441c0e0410034003035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 425609568 1250 425608318 425608327
    0x2040503070608070f0906020a02040c02031303060203041b0e0f06010318031806140d151205032511090402030a08041503050a090c03080f1608040519081e030708 71
    0x203d0b0042805481101607540704c01d48508500d00c01d503031202d002d028420040c0d202c621a80e0050415901001800146004681c1080082c8102003104034103608202d4942c1e8001c010f00c401c02c00d41b5841002810b02c200f8400b8246402c1034116104503a000b4500c0c8110558100402c9542c0d00a40c4003610207030641000c0e01814445d820f01030440700b8070b01c40d0303800c030040000400900913200b0403a502d40c014000c4446494a1102d15080000c4d200c202c00c907245101981030005506007c00c09074056081c40351020703640340c840000d600655407030035403190304a6440c40c0250ba00080d9842003510800c2000300c0313160444d030711a4004a1700c1c012001a008008141c0020701180005200c50b00420000545c0d80500003595507140e28000c0d5110008002c01381c00c0c80d0b0b0428030024045c2c20250942e40d17866201181420400406500010a62142510760041c005024401e90400a0b07508040c03080b00d070740c0079541c0c920b840c3d40e09603242101250205000105a000c0c1541c440070300c1140e000d5500054030320b80b207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 425610818 1250 425609568 425609579
    0x31b020301091a0906040201080a0c02010e100c09080105070903020409140d02030301080d020f06070503131b05040c08091e0a02120f07080d090509060d020316090605060913020c010204050307 84
    0x3d04100030014074032022a100040c4c0c88800001e4150f200c1d0b43e041e074505607a0b80b120b052170030141040d016207400b0355407101e1114001030000c05c5800c54641210b038021504441c4620050a904020b400c2881340740d040c48100300049402c0144201201e03810350b80040c2c0a40a42090b09006d940d8a000389064019061000d0455038000051816511040251201c400001c54140c0e5503a041004401180e0069800295014000c4011710b0340030848418840c03a0404940d035005145204015400c0b0700034001c0b00921a50400b80300324172801d461420808014100071a1456540513505032069a61003207141044804400303110000c041c6a028240d441d0f0030003014825510b408020b443c801aa1003501e00028811100240d07081c1407200940b01e01e00c0090904060005d01d0500034480c1d60400c0e10404140b006072010051003034210203c0300081c40940c1040e40100a661066120921072a01070180444035580c584110050311000c031030040e994480868080d0182c019a44802c0c0c1c54054041d00051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 425612068 1250 425610818 425610833
    0x3161e080a0c051903020c10110a030c0b01151d01210203220803160e091806060105041a0310150819062d08030412030e0307030f031b02030109 63
    0x141c8070340261140484c01441404466464542c0980143d000712000030306030410144004200744a49808198134401049943c074020b42c4d69412000160748800c420700703014444002a0150100d00c0801724103511506c402040c02400b003010031014401c60100e0030b0700b03a0081c017400044440210080600c10920034803d002500211a145020b1511000e4441c40901100c50803603501d03807041d02c01e03041d40c031034400e0301841d0400400f00c0410301000b26a440c04540d21503122500c110001c0c005403031290841c007816820240003802c5103040c800e05110a004c000c02d0107d44581107141840410788030303a10340d001101c02c0d510f960700484180c00b040c440311103002c1c1e0118406100c0c0f0340c00064051501e031180e2220044400e14411030103440f12070101c00314296144207018116002064040039607a440d0001075082d50300c164440d0444922003030051003010303008888a40703070300d2044014090781840e645a4011075100e52500600300114141800640c0d282d04020b0f4940a070040c1c020480000245412070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 425613318 1250 425612068 425612087
    0x1200703020106051903170f13030614100611100903080105270106030506040f0c081605070b06120703150507080a361a01090e03161e080a 61
    0x24015401d0203c0443d8506022481d2201054400b2000c14160b283d030312140e80c0e001c50080611503e0303404200f281d0800d61014064822030003510483d282680c518039042c0100d910856128040d00b56440801030b101d100b060644045410714108001c9803858198103030305180456072060f40c5246001403500900d0750001155040e6442031f00d42c030b841036801f040034030803020403501242006103d000041c001c00744240c200c2c90300301d07002070004115000c11004000a451940c2600400076091a0410128601c098a10001000705040c200d14140c11521000540c40380100018000d00361071445d400d07006010003405d40291f4000802060200310901800f0103844c09480040005844c90086900341049100d040091441009446904000615402c0d4500c075400a100000d00c45036049801007030b0955403910002010341c0700142c5940c141190002140c22070300440c40c0c03039802403283c1d845c0c01c0e0b410075101507050380002192200b42c1c40d000d141084543e10340c100400503100415101001c581050001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 425614568 1250 425613318 425613323
    0x61d0f271b0109031e030e060c010f06060c08090f031f0c0f0e060a030b041b050309190f0b0903070c1e150203041418070c05010509060403050d0e012007 67
    0xaa04100d02440112120f0304a40005020b0304600c03011094020310707070700e010f5540c1440b80c101801c0303400300100003481503005840f040c4521794640e40404102903c0b4401e40300074180a04251190b0302990310341000310300030326040a000b10000545a1707a159170412401c110b0000b03030b1068400032003000e1a50707001b8180f000000f034085010000071840c1140124003810366000702074561070400070741050031005454060061b0f504a07035250200328629400c010020b2005503180c440654030b05000071100e20f800d07102102c82156002d240c1c0b820000501405c3c22110302604541c0074041511802d2000b82148903007000103140038081c0b00e0020700b40789060041c0712118182e0b10b4013066582d070341c0c49040e0840610081800160000c0000b0320108680552007800420003511060010680c00b19a000f400740a441d18400300d10000f00b23175801c004d8240104d80e4070058200c06040c01d4102aa8040c06074090f10f22000851911104903111a50096004007a40c00301e1121900c00715140e484400f0f400ea00c2316009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 425615818 1250 425614568 425614603
    0x9020f070b1506030705032814130210080a020c07090e0c120607050f090a0617010b0403030801030b090c03120a0212160f020a0803030118061d0f27 65
    0x79800b41c000d28a150740402c002d80003600e0f5940e01581202c403584020b050301075240040d0302d945602180b10a01c0d9100c05800940000c0002484044044c0801d0040181140d0040320b0641c00041c0c54200300344200c144e0a00380b100c0c040c1c0700c81d000300d00640903000c502c0c1000e00c166500040c03500380c80c0c2c100d0460a09000306039079090200c2e5044c0104030f400b494a265081d8090008910344604c5840101104500b00c0d04543c00d240d440000500170020079440080001c0150084290311280180414014501c0c6a50146441d25541d005000d100c41484050042402c0800107041104240180340c190070001f400d50700180078880d4860b03816000030b07900c0c60040c494002da0300c14040d02c01044231301c00703944005c0e60010f04680e6990561b42a41c4580101e0300208a0017000840f00804c0020314040d0a0f030070b0040b220404484140412100594420081d03600c000320301203a401740c0144156000103c2c1d034070708821507848401c25914401130340104c80c56011400c001005c00003000c1030510081c20488403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 425617068 1250 425615818 425615821
    0x120f12020606030a020906120a0803010f060c03020a02130219081519032312040819032f03040303080402030c030d200c0405040302010905010f1806020c0709020f070b 73
    0x4049035215000c99200f5010ba02c1302d0303c100058034140714a1075001c000182031585d412200490141041c2403508203c6031700c031000c4014010440c000170490007800c1c4d245803501c06174509442c02540c54810321400b074001d5a042644111001490b0100d5034941e104158102c030034009000000c0c54810216000d82c0c0a507200d0303c2440462408142c41c4500e0010f0604e4404098103540f6500504030030780c14042001295210942c120040a005650005034103850a40d1140c0c030780f1000d40c1c10a00100c1088000440d0b100e9400300080d00103001e40b402c1c00240d01448850002ca110590006100120500c4648000310b030000c01c05600c400e0070f40c482c92090f4241d031080c580c100c0074165034501404210005c620604052030301c08401e0307181e00b056140c040044404014007000031408888041c1d0302600142d450710081c40500c4402d00511403d0700071600100006118a0944075524000c510006c2403282c00190707000284008000f0711000d0095130b8821035a0701d8a03100100415881280c084584501010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 425618318 1250 425617068 425617103
    0x818060406020c1005040807051c020405090610050a03120509180a09031101060803092806171f0501110705031501050907090308030c030405010905100f0e19061104120f 74
    0x809880442d2207c80c010030116007800c1c100001107032214404582d00c650410008056070701e5001303a600600201002c4e195604020407190b003a00059000b80c5d000f04103001d000c01c0041e44d1b410960355150003a20340191900500c41c005204050201080c08158000d4002d006490600b40e00030303a4450320a44440740c03c400820002e0342601c403944540040c582081c810f5070703081c0c2003107000000013081c498110003200400c403000c29040912500300c0d0780050500c21080f407525080c03807001a0420300042296000800c0d824100000b5106d901442d810080e1040c4820344256042280034007601000702070310f40c1b80f00103e1041d44611000d10645100d080c502d030100e00c601c1d008140640a49400126040c9550b03140d4001000d581e0016004a56941d6584c00f241c010600900c0b40300c0d40c142e80c090010074910b4000780d041e02903d03024640981d1b2900700030f0083c410811003a0b49002c01d95885072010a4860041146d04203901030755001e100d001d01401c4c44801004400340e0144881c40c860b48000d4040030055 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 425619568 1250 425618318 425618327
    0x8030d18020a060c2301020315040b03060712020c0709020a021c0c0f020607050a0302060f0601030c02060a090c050d0813120206070b0a0f0c0c0209150d0818060406020c10 75
    0x10540030b9080800010700340b0080d8403d0310b14202a6003d02c014214201800d031044054000c03600c014030560758084244120412040310b600f00c1c2e090120790a20640c0c0c2d41c98002074136520007826042c184600160007103d0707414650181c509640103039041c0c80d2415581d440c4c1c080a0350000d1010401401903030b019007605490a40322111007040c13035544092500c1150b44007031802c002404181e900000c284034040c0080c40402c5907860080c42940580b005007440003980b20a41005041641071500b48000294840c1d8001200b80d802020030300041000406814030021070703c815000301c0d03041000f00468000b0301ca1240c0c001d08a0390a00313440e10640c6980e519403110011a8400003d41c0304008100300d20110b40418203454000c01100380004214a1216004040b59508000350740442c040310a440d055140c5501c8036603001501c03000300310500000b000003c00803c00350b40010b19146010405a0007001d40014280d501c1c0c3c1c014100c2a80e5517181c6034007a655010a100007445000724040001045125 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 425620818 1250 425619568 425619611
    0xf11070501060f0915060311040b1c1a150d020702040c0906020708190f030201060905010f08060c0c06180f100f05280b0f04020412050d0302070b01030605060d0204050108030d 77
    0x1c5d01c0b040d0b00013810040210040d120b031318212160f040d820b00001c109450003034010a054801d50400c0140c05056095079010382d0090322500b92030070041c45009419454252210048161a0181a80e284c002d002141d000f40100040a50041d1500b001a10304a802804140646403181c08a60551366121646990740c00130700a240d4416a0303070603158002950880012405500ca40004240039071104020703411214241d01a0005036101c0c5010010f10f101808500d41040401e580c03e4a8004010945655024058021512000040b4480a05001c1401b52424a01442e000c0c0c0d20b50703000c081c89034805007001642410f480c40c500404689621001c001030442e11a0760944400d82030315420a450040680c4050660810340f46103071044503030f886100810140201119110040c10a8140070b0710740780d6a1850386091610410107140450351660300340d41100e0b80240003051540da200c0108089042110000303420506200012903548004400340403024110311081260328010504511500c18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 425622068 1250 425620818 425620841
    0x60606080f1005030a0f020d060c0207090c050315091008060f10080604020102100c1b060c081b09040c030b130c021902210c100c020f01090b0d0f11070501060f09 71
    0x151020f17900103401c0008a1002030300040a10061a4483d21000140c6500c0c0c502d020050304684028800030807584188000c0ea0450714029080d4507000e480c0c0c0c82070800c2003036442d02c6000c088000640b0381443c20035040207031102006692103400e14802d0b44000c00e5003914084101c040204010400c0c4000054180c070a540503070007004141c2428404100500c003004d42c4d1401c00640400702001d0b140c2c0d8400481001d881503800183c01c2c92541c9004002c5000544080c181d00c0c01a90154002d584c0c0c01c040d1458010202c2d00028414070015054004145c03000d41c1d150022095101c81d0141101d940c8103008101058003030b23400c0100190007030031411100441c000e5010031590004840f511041003642200c1d1403080032511480b10b8040012850002d24a4980000e2042e40c2c0280850030f140301441e0701c62a003030800c448040c2c00c02900324458029003000c0c4510036540c011150321f0305480e07046003044c800f02c140c3e5942d94202c5418258081c10580c0036050039080202c200044190717461203480e980e0790 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 425623318 1250 425622068 425622073
    0x60c0304030c090b15160206130303050d050a06290405090c07050606040c050a0305090a08041211010207050607020f0d0615030b010e070801050d081309020a0f0221090409060606080f100503 83
    0x206d1040c4106050a2404c6080e0f0300940309200705540242c1012411010f1130090704c42d1070300d0768007800034041500d800030904803809090102c00c01c451900d011400d050011141100c1000d4600c00d40400070f540240d500c081d44c0b261300c40d000c2c81708080c8040000c103002d501a10513030302c1a59031a410b000030f4480c0110044005101085000610b500c41d50186070082d01c05016290466280c0d00d0f10511608aa00000c824240001d0f925003088410000c40801401c2800501011032504000400c603006801c030180c00740314046110105942ca24140c41045988150300300700001d440c1020704044060b5000c203d4440c6178207400481e58182030607036548906800da0ba0044581e003018103006d28100544006c8903001c030244141c00f50460015500400303031119550040e203c040c0914010241202e0300303c1c480543d0400080c1240d0001482c805c0c03100c070042d440742d0690b00c9410303001250080c003100c00c0c041d00303240c07070004007007030042d4001502402108090614001d0751035408220b81131b02418420f00f50f156 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 425624568 1250 425623318 425623327
    0x70c030e0d052e020403030201020a1128054602090112080403060f0504022e030c050d060b0d0506120604020919050a05090f01060e01090b060c0304030c090b15 70
    0xd542c852400e083d444002001281402c2c01000150503600103401c00ca0160f5004142d610a20341d10070f14880710811700744008c02c1d1400201000e01d03256032065041d0502410041022004d0200421952442150044220344448102d290300003010445641e950320000325440c00105071104000c0d0004510340080080139207911305040103d1074206104102c4011005010010111345244160741c0000c0340c40341c1c0032420349018810000c0039201c1c2e44000121840500780d10740041d14010059003514400d040c002006840681c050b00c0900034a120204001d04004c004141c070700b20301f0b014094000342174905000980300c2c0c100b00840380c3e00c0c90000301c0c5030382d10001c0050050300d80651042c0c0c00c5100d81d103501c9a40c41c85508440b0558204a40b080c200c913856005020711146c007044030a8541340600b000304800d0341048070091001206105442d03526844200118039a030b03d00d8121642100943d00312a81c466481c40d00d20b03075017440e134400d001c0b2480c0b41c8003080846007046003001201c05c02200d50b00e0301c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 425625818 1250 425624568 425624593
    0x120301051e1c060f05010b090415080a050f2b0302030406090605010803070c240c051002190f020102040b07020d030e03030c0a050c04061401110a0b070c030e0d05 71
    0x40401d05050412980c00040320007680e80c9400703811807001c07081d0522044010740e46040440603180b92200d060540c40c58140100708059080d815504024130849000c541030030b41d1700c00c82c8240c8040e608216818018417042c1000c006001405481007900c44080c0c0340300c03900359502e2542240d03c0b4a50002d0000540401260941c480e50086920130f101d00000100b110705612a081100d001743c0120a603580009618424030204900200051005014490764514441c1a13142602c2c00b4a0604061100300750000c010090140240804601d05100840d2030720116803030000b00b40003035010100440c410442e81c502c00d61042c002c46043d42d0080a5043c90f0140300d9090145003400641c058041124030119000140e03014401400085407041c0209105806803c00c203003841100b0700520320580c500344040128104550800700000000d007003000046140003c1c40341041c001d030354024604460982007219150b000115402620b0103030740c551851140c1d1005001c110003074450007400d16401107040001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 425627068 1250 425625818 425625829
    0x1e06040b0103122309180103031d0612040f02100c050a110402090d0b060f0609090f270601060801060c051203070c02150d0510060f0c031e09050a060212030105 70
    0x2a840da6600c2c04a2201d04040701060380001341c2c5000200d1107a000800c40c4051409240c0f0300101c02c280042803115501d141c1d8080c02100001d400d18036680040904041035a4a030402ea4208440083c150000352801e4500304020034102c0c04128450f03402040440740072032080300e6403903d040e44500102054615611000c03070701c44045800342d601035020052180651100340342503281600c2a00651168100201000b01e10920a00c0e1140540c400f4045e20303141da680c884000340c104507203a81c0d042d01c0d62204070450841780340404503e54002c51b40040100c10b0280081c1d018102c0780300e85d941881607604e4403011a843c601819014040b0b5001544180b05240c1c480002c5401241c0341c201001e0030007041e80070171048468001ca04c680c4044c0802c1e4044002414022298000e50800f44412036a041c64009040c1b81f420509903003c001c201d490182c10140030788090154400760080055542c2d1003032600900805003070080c1401804060b50000e00c0e540001411919200302c17102580c2160708140512170b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 425628318 1250 425627068 425627093
    0x50a080a0f060b07140606040e070b0304050a14160504020c06041202071206050a0515031f090f0b070f050406020c0114130806092406121501081e06040b0103 69
    0x401242d42c07110009191000c2d10000c2c0381091042c0148085a03c00304002070410f00c00800e418000c50820116045c1010080391100596440d43c0f16140c6a40b55801c1252030400c0c1c2c0348004128140c90a90720702c40b4900041c8400c00c04d03040d2285103040303603181c0007840182c1c050000706140e070741d00c0100420700040d1310160b5002406501d1044401c079969400c0340b2018158101e00540351541e6400510a4203030305ca000d420b030b000420a1003809003010600110303644001c0210007028400900711404110703601c07500140721081d0808491154202e83d8201490411400d079035000204100a000d014480e02031400e41d002c5500070380240620b402c0200064920b20000030814030081801c01100e0040d51201800d14041e0400000a040d00d140ca8004249404859640110403011700d20b07015901d51040e40c1041d9020350142c58407000c00e5505810a07180182459200840b10b060038008110558002b885d07009040041d03003c00308243c540d42c80d064444a00390b030050602da92400052011941114a46 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 425629568 1250 425628318 425628341
    0x504061d010309050d030b031c0207030b070c021f17060604052101020a0e010f0305090606101b081309050103080919090e060f0a0506031e0102130905090d050a080a 72
    0x11440c2c1c84144d03600c6081507036100c0b00d600403d43d980c0410300700e808c1c1003084d100ca6211348056940d081c420158042c5d66540c0d68803000b02406441c42c00604074504c510305501003030303602074000952089c2c0c1e50047c60f10700030b0f00e140e02400a4120384043c00000c0b42405c0c0e60f800341c0c0c400341c401840e041c00c0c40140498080042c0102040100c0d02000e8940604244010300c2c000c082c9030382c2c050200600000050082d801480c00381c1c00c042c2040140f01c0c1da03400c085030158202c03208450412814140000550701000501888084441c0c094003440030303c036100000b00f80b0046042c03054a9a00e844400e9807007103440a01010303041207414802b08519040c623841d5482170704030003200203846030b5540d001d640940b015900700c01220b070480414070072111030765914503401c03410040e02402146840d40101c0d94812010424035000316000075a0040d110080d4100c0d6045e00c100300707a48109503150721220002c0c00d015201c1000a200780040c4c3d681c41e5104106483c0c40100655501401d42c460f00c29032006800154100d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 425630818 1250 425629568 425629571
    0xa0815030a1505061801121119060e010c021002010506010311071515030f05030405091302031f1e050603070f08030a0302030a0f020403030c0515100620010203010f030606060504061d0103 82
    0xc0c2c14514415a04600074007c1e030300f1544844da02c0346064214008090b1110303018070703080b10303119040b0307028074660000741c5079246030800b1240710f00801200c0c95032201c00c01a401c40c11200304180d21640c1034004501c10ad04c21380301809940220540303a100c40c411200d001c0c120844d89e01550282c2e020f250402030120030404034100c90b0075125107450294845103041140c44d076100040410031410401e1340c050f0b101700c3c100d00000c40880b0580110b070302c40100c140c0c200c034040c58071704100c1c0c1444425404074003011000601110582c1203041d520303000f8001a0703080e521074447c10f11300040010b20459203205490021b0b000d141006010001503010750400781c0b415031500c1d2202080300302529a803014000a5000c1d03512074400ca12a41890b6003080c00b45c0401c01d03000c2d44030f2030400c0f075802d01124407903080f00c5c1985811900e4005800c40b50342e40481008000d955940004000103244004d030719120140d178090801007060300c0d6102c1095a15104034850b0303030041480c40e16544001c1601c3e503800fa014a006050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 425632068 1250 425630818 425630839
    0x20412080d0608030f0f180a0b03010801060b0310090903020f0d020d020f06250903060c030b18090601140d051902010815011d0d0b0406020c0c010804080f1e0a0815030a150506 77
    0x508c28074464100d40981d0102000400c186142402100001d04405a4061660170b06000e098000707403060017002104c41e1103445580403d81f0030880c940f00f00c030401e000d46241d000714220003901c0e82c0300c2059801c0140318012012014810100d5001d0050308000035400e54541140030380030000084501d040140028000000045640c60088807940f84c1c4540c1e0004201d24040b0030403070300c10344141c18111800912004c104001d0000611241500d01e210309400c8925800270001c0c0e02009401001083e070f000d40100040000d0342d60b155140024400d8850750703120ba0350602c04036041c4803800703e914002010910303200182101d0f86420502d08074003411304013106800343c44041c3d80001c00e50301116019030002c0c0c01d0b0050141030004410b0a482407038070b4034440c207184c0c035001401d001d84000044c030030400150100300a19000303494644009541c402d16280c1080c284040d220741c800301c440001800308540042087d02d030100f003403420150b002c0b031100541c01030b10b51840000c1c4002040150031464005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 425633318 1250 425632068 425632117
    0xb010f060215061f02100905330606030604021303051c0206130201050915120406060501030e030732030307030c09051c110402041806060806010c0602030901020412080d0608030f0f 79
    0x35202141d40188c0c0204111504002d020004107800320084007101080c4c04041148060740b244950080c01c00c6403016100c0e140c0200250003031042e042071a04980c4030340c50002c20003102103028611a4030320415071040d01c501250a80e00c1d03400491342a02807950b100124401580108040c00c14142c001c0d00711000c0c0340400b2000056503229085500598088074200002c00c0440d00846020f00001e19080c81600c01da00c52560352405068001812403c21903d44034000301a9046d1030941030110090b008202c05002d410364683e0b10607a40040024244442d0208441c02504084101c410203001005900c8031507961403040a151031088404c85c2d141e402d0b0340320590f10384c0040c2010b081c102ca25943d44000d0010300c1e0048403a2a031180c800d1200c0f480c03c011543c0e800c406a40b41c4580c0090300941e0303030394032150418024462504032440c905144041718042c400c006010344000520407004000352900c1d856280e41da406603a100868804d4100951164681043d015011078148616000a19070311075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 425634568 1250 425633318 425633321
    0x4050c0a080417180f060c0729040e04140106050d0201081003020324310302070e01030602031e010e060f040b0d030c0506150f1c0b010f060215061f0210 67
    0xc6004031008581c081c040c000e07141007020700403400c0084518916040c24034a5840c0c13900012702c01c03401c45481804042e880840c580c410349080d8240d00c1c000aa40d036440760005414104180e505840c1c0040c80703041c408035a0300510941050304d00041c0061080170b0140d0044407000c0c0300a1502c17020b051742000001c01030b00d0401c403207418030b200a020080e12590110100060078001414074980c02d40396410004076030500480f0120290f9044403140c0d9502140c1001d80ca86101c550150012402e800c0002051194582c05580070700018840070b00c02a911351800b88030460b0030300031050f000040c94042906840c0c01c01c0d002c0c00c0d4030302c09400070844808032070000390518021502039021856001d04842081814481d05a00c6420001088649d004400102d0000c8507032400d41c0b805007001706407400e4420211902d0b059819880107440740f842d0b0311102201c010240b07911610015101d010140000343d0000080035110702d1b005001101850110446200c01003c01d42c170500a6000f042c5421076803403484d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 425635818 1250 425634568 425634577
    0x30a060b010e012d090b0c030301061d130e0106050d120305180304060305040809040e010b010305090c0d0b04110d0302071508090615030106081f050604050c0a080417 73
    0x10000003515100000001d84a000007082c02d80c10030248100844072840d0081e07001c9035001d1180780c06140c152011006030341004464010300d0300b0610100300d15140b03000000080d030695590359923900800800308038000070400300b24502540440a441c049030080c0180d400018440d21200001c50000e50f075201090070000030300025140024440ca11140083c0c1500a180d00107038110042c54800900805290b141e0289000340300800d030300d48000c0303002c1c04480002d9480a0302d00a00402c040d50100d02203034000c1860074a403d021a04120001ea022480803071030fa04602d5016045080d141c069540b482913100c070060013212070b240c02c5d40b03c1d805d080d1100000f4410710707842500108009c80c10020010003540e20880710804000c4446c0c00c10001c0c41000c2203854108611a5000d0702003500e0200190240c1132070303000344031548120a44400321a840040291000c3c1403000e003001151984020700c0b099a84c11038807000440c1c001c02984490070310408520b40d1250003400d41000407100d0321405001d0390320 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 425637068 1250 425635818 425635823
    0x7140d090507050f03070806040605040c03021c12080606040b31080609120f0a0c12030f0e03040602070e04032604050d020c1311040e07050a08150d120e030a 69
    0xb0600a1080c1c0c20910024158040b04a004250b81c1d842c1c104040e07500c4100510042903961100c02080800014a0040380a9a80104100c6d40007810380d40383c851140d40850252071440340c11007588401405080980d00920000c0c1000b4605402c00055110310b50000b843d002001c1c0c150061b4450217112714085030795413440391810842c09441e00c0107282c03400a01a10020302a0800030100750f1191001c1c003100c00720380f401e00d1480c2d150f09401c1c0c0f00361120400982c0107080403112446035506550f0580c0f00044203101c400d01000082c4048130210b54a0041e0302511002d40d010f26828004400c540303c5050344240320785082c10400c0742c0c405101c2007080098800c484061000c006210400c40d09000c44002410a8401030200c0c0340c7d807000241c0c5035607001c0798642e00c0541d101010001501c00004440207045860070590050030120070090181e40070b8241800003542c11404101d421480451426030304400070039094082d40c903615010301d643c2c02420030805014485904010350749080c04034811990 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 425638318 1250 425637068 425637073
    0x1908070e0108071a070204050915150a0f03050a02062b020a0809030a081b0d0e0601030209010e01080d030c09120308060102060a060308030a020f070b0103050105090c1807140d0905 79
    0x14580030300da40c9008640d0b00a200401e02e030794504c910411144007075410301d980447d0081120b0b112103c0c15810f1041c1ca0000d46201c02a400401411481c81125034822803000e64440d0301aa9843d10030008d079100c6400002c156811445101e000740c58250f0141804401c00074010f0303841114140d002c800f0216103015805029004189400559084505a5171004114001d90318000445030010080d030401002c040109040e035500520050805050b601c003c1203c16081092070702c0909000d80e983e0f024030040303108500c3c11001003110500007000504850380d0000500b0040308540056020b404a2a1002c007040600c2e10001140f1007600e6001000301e0198035929190304010000a0900200170404a00d4501300035042001880800449510001d49280141c03280800b1464021070310842c1005840c6c406014004000c0c0401940070a0061540200700d0302c0070f5119206100385000c0c902c49108604850f040060410350040101e48080d3300c0544c825850f201c481d0584808079503903c030042e5035070f6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 425639568 1250 425638318 425638321
    0xa300320060a0c031e0c0203040b04090501050906040209011409031f0203040510050c2d070804170105040f06150302100e010e030304050913030e030d08040b1806061908070e 76
    0x160440e1184550343c40e40e6190611184980c1c40b10114924840040d107020196540004c80d01c40c2e00c00e0080c0c80c003404014030880c1c0d0b40d030351f142d019101034a0280141c80c807842202010a40318a4140700b03ca910490603141c100c000400340d542072150b0f13000100b074a50140100100240e481034207451030a407800450318016282c0c105404c25901d4841c890100d065101c0c9030000b4401981d9150040e40d8038000b82500542c60401b4042010480700d00c442c1c1d4103206910046036500401810714081d106643c0780b100c0b1504030f0010410300360300303a40701550060002103207400b20401045558019500c03080c8904101c041c0c090b50796000c101c0e450090340101d4002880128101559070748040d0314071403410214000c40c03c1908100020300030325000341c048070700c40d80311100b040c0c1090301a40348880c207440c0c010309039442c01041410107441c0d24801c5404403003070032020001a910042c88181c80c20400300c40801441e9a640d07485c10301003000700c2c4850500031a1001c140028000c102001840094110803060f04101d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 425640818 1250 425639568 425639581
    0xd0603020907050c1c140a09080a03020703020310110d0c0c02150310141509010207090c0503070f110a140c0301060306090c08030307020c040b0f0909010501050a30032006 75
    0x141640c0000f1402000000204401010b41c8040e06c080d000d803840058035500e20303580000340c030b9042c2540d001c0401800b464014000741078001c00e280c3e007205d00941c07e031560300318403800680403500c050b017829031400014000c1603400100b503400714508007403904040c9411041c9400144220640150498103c2d00c0003080050103a6503600104c018140118800801d041d21000200d0381e0b44a40052000000c000c900003440d0780c420850680106240481001b141c1c001400040050340202c9894000ca650102c0c0040c00502c00c450213407400c00c1010203080b4900803a990300440c00b9102030206102d01c030f6007200c414165001e10455000f144a40400582d0035942d103800d0750302092660003c0010b40050007000080c98010810b9090000201d6001849003080c400003140700c00300034800b03500310b0b00740c00c10081d0101d415400a030684500f140c8010314035035560316245180c1c0710491101c94031843c030002c0205881001c0c0030825658424141915002c42e43c18440442c410040141c0300c9030352040c01032101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 425642068 1250 425640818 425640823
    0x608150a0608011a040207110603130b06010f0203070b040c090608011b110a0b130c090c08160509041a040c0203031e01030b06010f200a031103130b0d0603020907050c 73
    0x2440804000c4c01104c0d0191042c820a8402c0044180607940004991040041c284c02118400c64014062a101d0510343d09041c500708051000310b45141080e00840e410358000c08072092070714125030055103040526a41c025130300c0d0000d007085480e1410008041280019800b8801c0a45500d2000090500c01c0c03003100c030301e2180c920001e031050140d40300900c40381030310101d4010b083d20b03084100200d1940351801024102881c440014000000d0344102141404154012120b826900e540e54801d070703262100c80b00c0502d0030300310000010030000c01c0030741131a04003500015881e0003060218a24210304d4000315055842c1c80002c040103810010403c6500044072003e4046150803200084140d030469640a001b24805008076041c450107412130b50424ac07140c0c1072428039074098a4540b000409480400d0356824407544220081110f03010542c0340d8120000584400c101c4100790340d12190702d00038003043e50f5031200130080c9805031584404401f580304c0000c03207030003501c0721f13560b241d551400c5505807030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 425643318 1250 425642068 425642081
    0x11061909090236150a02011b0503070e040e012310050a050d02040219110706080c0301210b0903030403030e3007050a080a080702070f0303120608150a 66
    0x20965441030004940f1200140d1a452004600650001c81500c610480d0040c0d180383c0700c90301e980000c2454410402450382009451416440d400074460164590141c0d03070307180381c01d2850f40f0000c2d50520005181c9480f55068900c07182e0090400500c9d09941b04070300d030a584265419006845070000c241e0607220104128540c45102da5590903000c0e410240000c180180a00c00c052141d00b5000c4800d040d550750303504071140c00035001c060203660310441401a000401c10006500306000715040001c41900540c5414803038500500303524034582c01c112210543c1003681c44050700b01c0741480000800140b11850361405242c410b801580c6a25103440e0090555420b00140e14075074002c08142c0000c9141c00341020209c961210980380d0041d41d80c1da0000e2240511075001e021841803007801004d11141500030724400c011a41c940103199211101640d41c0c40841c880e010b1080070140d400c10100c0d00c5404092002c1054500200319682e44103107441ca00803e00346034101809c880014021400018420b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 425644568 1250 425643318 425643329
    0x403030807050c0a080d0f15050306090307050a02121c03020315040b01020604030806121e060a05040c170102210604060905071403180303010b0a1209020d080711061909 74
    0x452500c2d206414803074440c44c40200007841100b01054400605c0b0040c2c00007140c9020040041185100029000301d85201c1d511410780039000d10310205401300f401004503030083c0e40140042c1083c03071441d404d0000e903514140545865004494503180c80004c1c05410b410ba00020340c2e005600e90138650301410401641040c020720481c41c201950026076000f186403507120b501401c1a4a8681c2c0ba903001c1401d040481c41920354030301070400c2240141c811408014a21a8407600b1902c0e41d60701d039611281210410348018200c418018810400c08045000d104500c0240400140c1050350085c1c8442d5414545080304050500d028200810b905183c403640b0010300f81d01005002c10306284c42c000d80707080710010301009400400400143c421041a199124049401048980e07a603035030301a0300f840c1c3c4c018109000c00103036040301104403405d050180c1d2450302d40091400c07845c1801a43c032a031441e40a04c8080314075490450142510f5501d840c080d002425044c1e00c5242c01502c000c1004000d108640c105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 425645818 1250 425644568 425644577
    0xb04051e0108030a3f0e1005060a0e07020a3c150b0402040b03090a1707031e031d0601050109081203010b070f06020d061a03090a0201030506180c0403030807 69
    0xc1610710755001172000d00c1030790f100308481000d4007880e481002030b0105010405400c400707211891002001d542c0682e02c003004040a860001c80324191040c144c820a03a202548180c0d016014049041c59281840d000303952401103030b41c10b56103030741c036640c0c02070510341c50740343c039020b000c10480c2c0542c0c0859807025001000b0b1000b00441c0d8066945817405800072442d0711501d66103500d913443d1074445a04a501074100101010789a02c0c282c41490341c3c034a01c02c8001c4900d0111803c13041c3c600c0400da400d40c0c0603c0c0d80b54a45030103404410503056480c030020107040c0205a140c55000c89140414054500c1410381807001d004075604160001d402512158403c50482e401612042c0c502101e60302035070705488020011541d90703203050500c840f85286001d07006d0905840000c1e6120141030a0707002d98100c409400c0500101c2c4101c0c05022860300044178056411f4002c810510010b600c00e9004e0b40d40f086e002011170290075505109014550400c580310182c5510020342802419004105c169002503946032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 425647068 1250 425645818 425645827
    0x603010b0a1406040302033703050904020d14040507080d0c050c121f1b09030f03031515050d06090b0a060804030509040e0102070308070905060714010b04051e010803 73
    0x1203040c1c02a82c1c070440032944020000e10344030740e54920403180290b800500b119003600d203941c98002003000d80141038400d403034140804944078505a44074000c0a4058880d203040003403030014040030790311440c840c2103001c2d0303900b2005202480854010303000704d0290005206d03150038003425034602200e8801d20014071410405100008400140c00051000280d66036118130400b80c0301035141c51120b030f00d108182a4002d66446115140742e10121004c8092820314140761040c10040c1e5108a01e40005800311009100140c0440d000750440f0402c140e00410880b0140d80d0340000c000c5014a040c40e150010f1400903c009001d117680c011000038005058041107088030078400100c06000e40d2141d00e041c00003c01c0041c2c103241c064001c0d6041000040c205010421106169500035448440d00310b0104100030b0100300106d100314007030030554a001d4196850021643c807115421014159003965640d00c42d240d40c0f00c0e40d2201d000e07940c0941090031200d003980e240307807540000c2d80e02c050b081044903910502 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 425648318 1250 425647068 425647091
    0x901050a080c01351b07030f030207110402042d05010804140313060509010f0201050f0109020d0603060f05061f02030a11010905070b0a02010c0c0c0506090315010308030a05060301 79
    0xc2d188a5008090074483c04030b6010250001504450700c03a030010580e2560200003100c00240d80141c81034204003544c1c000c8558141c180d00041c010700c038001d000195905c0412a02c0d82c0640d0080c1100c40c05071100070700800c2d04d01c0c00501603902c980c02c45400c04202804c0315070b412004610320b0001c52007501149000c581800002000c1020041024020142c44c1407d1140703801c1c03e10441e4200702c940750422003031588808000c0d1841d4000c0c0042400a000310326000c0c0e8891041c411140601000701c01b00c082c3d6407034110004042d400c018002400180e8480d800000250b07144a21500d080d0b0905000c2142e2600000300083e03106030000b018a0741914003600d00a1036804001c8400112071410718006031984c0c940e0060061888401c018030030300c01c205002c24611010320107403011260a5009008400e00800210384283d001c0d20010320800d4807070014003c0f440c0142c0074140390301000e070886070099010b0f040707028a61020307401034601643c004280803070008035004540c1d001b802540240503140400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 425649568 1250 425648318 425648323
    0x1b0503010204360c02010b0f01020303060108010605130815010303090501080c03040f15020d091b06020304050d05010b0d030e01080c07020916050f0a0206010e090a020105040e13080c010b0901050a08 87
    0x407101c203064a807040c0c52800075400240c121603160b201c83e090410401400e860003a00800042d900203100b100c1d01015004d4a61000003128420381045e9030703004503640707040b605071219000b0181200802103540008290f00400f0004104c0720481002610115403445c1006018132080b134120504100b500410020503181200450ba00503074054004205a0300d5824100205500f84030030070725081c00080ea8442601040e0008100c080c010501403000d1f560201304030950056612851016800900042010380f40c1072500c40e1001d4001d50011490f05440da00140e034040700000d0460108900d045012099680030512135804140000058135001040c1c00241d02c890000f09a100714122480d030301a4224810025500240040022545c8400740460081e4440009025140007002840700187c101c80000032000c1e5070a070107071a02440c02d4248040101d15110007025200c988102c0008880014015802014501400c2c0000101450034400700b00340104107a0000e8442c1480b00c1d010300061070003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 425650818 1250 425649568 425649599
    0x31b1201050c03150301090f080702010e0f181504140a06091505040f0905030a052104020d03050309120d02070b070207080d03020d0b13362d1b0503010204 68
    0x20802003003c20544c070030009015201c400c000402d800c0d1034120600c10000748070084c1102a00c03d0301c980070101c801c041840851480202d41d130758040064164521450080c1c48866000410140005600c140e50000701d02682c203214103100c1c2e4140100200040c0403580d01c50700300a8101503000b4011003084081030880c01d00c19016503031003103580300ba00750100c03107540c3e0007074103916817020a031383c1c8a4050a0002e4010340010315801032081c4035032100c80e4100e11207601c40f4400d40d401011a80ca40d450750310215039680004120b00a90312170710310141135600b243c01c082c3c40058041440942c0d110301a181c000181d40c000b406040c20340d8030103030f028024444045842850a1180d190040c1c1703464a00310b03600c02801410401980005115030089001140341d0418aa615480d0a5551000c4240800028991616030480544500054601d8005100c4070240103007884605903025092100c804940345002901070304a60203c1003c8007001d00100070000b007c001c0c04101c00845c28180b80c0f00c80c08240001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 425652068 1250 425650818 425650831
    0x809030304021e130606021608060108100e030409062310020c043909060f230c03132103080c250807020a0b070206120a0b031b1201050c03 61
    0x1580b9007900f4113910b45444400400d100d00d2014005035680e210060f48840500a5206001050b0314001c5010900007c015048415484c0204030f840b01c0c2c2502b0100810080e0345c00e0f900c82c0800c00c00010099428040c0c0000f42607401e030b48482480360304010202190821070b00341d000f044140325107e81560003003828141040240c5004c01c800320a002401c440601d0b43c07201c52a05280b00d03414a010325000f1100740841c100035264612515114501030f5540d5040000070000543c245400200d6982071071480c801c180350242c9824180029801161300303680200072902d001c101401020855420b00c94103c0c04d9940145071804e00c0f000403510002c0c00b010b0010800640500b0001d4900040241d8184e003610009903c1d84040401c0c1c80c03440c20300304940c0a050181d200302000a804611034000c8001c41d03220940c010041807400c04032460851446500410920040d42d603a2182c0d4041d803405c1c0305005003200d0318902c81500031000000c0154224024405484030fa00d81401c011412000d030040341d41090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 425653318 1250 425652068 425652109
    0x121506050a03110910051b03090907051c0222050108070f0804050a140a03020706030203150f010c200a1e030f171207030b010f1218020301020a0906080903030402 71
    0x720700d400300da00350f485004203103504170785445600440f082c0d214002d400a6441100d9880c41182c5160040b0341da801130220260340502e0007008980003500460040281c1800c0c102c080002441300d070344580407a00604c0c801003203035401518040030a003031500103e000e44000d09010240741081c4000038003550141818405102c0c004001ca414440c00300400300c40c1c0c940c403200400c3c10100443d5010f4480a00c10000c5000d0b00c41d908002c11028040c0c02501e104200b10794a801c0c56143c0c0300300700111410714499031410700945a07520070104020b180c0c261401c030301c41824200900403900c1804140981036001e600c026401201ea2454100c4000082e003c694111039000000501414140030449502180e5841c1810028070300740d410265900305880341001d41c0b000c02c0003010703500041d240c0891131060380e0001842d4120344000400b580d07100c100034079007400070500300c005145e01182c2240d00400e0008040782c1d00c0e03641080003550203043c255111080001035800c50505a000ca17100d01500c0c921030306c045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 425654568 1250 425653318 425653331
    0x30908090f0415060f1b051921111204050604094212030215092104030209061f080703020f070b01050f04060b09040f02090a06121506050a03 62
    0x5a5403908610703542240c00f4141814a6030714200640107550045002000c2003403c005012a008003031030565206030007030080c1c200c42e80700300c816506d01109034404440724000c0c500b0f4540203450112121000c10780755107a4815803c58410032914145104481d031010b00001c010622460f250074080c2d500319244108081b4503410892211001203901e01c0088059043c0c08404169483d01e40c021404030040244001c4059500d46800c1020070410420107005603000d440b1030460701088101c0c0c640d1000000060710405854140101c0c24590b400225010b17010300070078140150310b004249903800c000b0865042c0d002140100b50a032202c4018110002400701741c40002e001700c0d0098046a501d088250006a5250319510300024420020b0041078058032860040e030740036007030500c160b8007034409046620f41001070303075001c02003c0c1090f02e0760030601c10b40a015800c02c47d11030301d0152018061945070094001444181e5804440050014840e00c8411001c10801c02d0f4111048a0005003545400b0822 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 425655818 1250 425654568 425654599
    0x1240b07060b06032802070f0b100f06030501090e010c0903080c0a06050a05090f010c05120c070c0e0a0e0a03090e1b030a020702130905060606070c180605040b0103090809 75
    0x1411080714243c1c000c0000004c0011044007035102c403800b180c0303a0105281c40061a5104001c034000e20500405a1401400c0c038804130340d0500589900060340c903481ca00d6075031907100341d01c9a62020752000c1c001c01d0701c400c0184000500ca0180c0c8a03182c001d0703030003040b2402c3e440074001c1c610501448003604180300010742005002050001410083e0000c038240041e040501c505001810101e542d40114044c803440c140c8490018060045094015070f9840e04205405100c1c0b0ba0303840018015171152682000100300082c11041d10b0703c000e1030407850742c2ca1a80713404e252600c182d541380800395909401c2000f4860010b9084520401a507140781c0c1c102e10035903180402a8082000d41d4110a4800404000c014580355030750028000c1c54403d44041c48141e8580482600783e07081000018082d400803800681181131600180141601404141590b156180c401d0801c40b1000c0080100142c3c440a00b40301904190148031680e400030700c1c04005c84030494481084074060f040445208107004156800d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 425657068 1250 425655818 425655821
    0x20606060c010e030a0504030326060f0d0f0c05010f050316140c0f0c040f02030f010b030402152101050105120f06030102070803011206050124030b1305040309030501240b0706 77
    0x49040f24a0110781c0e486103000b00c0500036800600c011400680ea03060248001c900c02408415120848045036855031a0300c810032503c000c0070304a207608100e20340b013030380041403d5501011405010b4859001c2841c141000100056003400320481480f000b00148940114003194100f00c8296910303100e40c007884c5080060f83c0d240700b0741980e40303614425140c0751000d0720070104440d80c000d40215001c002d4540c00c10040001e0b404105c0b50410340d5106100100034141e5807100642d401440141070f47d10b84051012030080c6904043d03086c0900704104817000741c0100307240c6841400741009003061410b010700340c0384140e44460003c16a580713100c40e1002080c42d940f02501a6803015a0061080392a5a100c0043c0f050190208a064401c2410400005100841908000ea201e0a01d180c1031b10001000c1c00150041c007800c0b80d8041d0041c06014040517854141d108180c040d6200ea81d900c4440c03891824820700b545c411114984c0e0704803800ca40e0328a40e04020501c00100c0b4982c101c52600c90b0240e082010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 425658318 1250 425657068 425657081
    0x20f1e012a03030f0b0109120b06041e0204061205150d170c030d11040f2d08031804020415110a0602040e07020114010e0a0f061a12010e0403020606060c01 68
    0x5120740784101100030180c0540180c80d03c5080c04c04100400e4540c8001118462000d2046602045102610300f010503020403510f60711a2000d40041501404400805803400309040c1c40183c655001c5814415560b1140000d002284440c1003400b6074205a8440031489104982103440740450312010020080101c5c000c0385294035601710607031510308182d601c54407903111341c5a25015528007489628280d0168041d00e007500c1041400380403541c2002801d0038541d070122130031402c0d0b85004070200c4078248910b042e00c1c0901582000303551070360380034060000014400d81603180300300e005100070301400709006c064a501c5a014079101c040c1c050302e2040b1a080c0310507407002400040c00040c020403075810704d032803003401415503900801104040e4015006242c00a001321b000c0c40b415071010a80300461500605800d00b0381c941d00180c60390f03441c020244d005e0b000034080e072900d07000070840e240e80340d0800b003a00d801482d250442e01418a01a0b800035260b110040c542442207101064040c0400025031142 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 425659568 1250 425658318 425658377
    0x140306060d09020f100e010315030320010e0a0602040504051014220c020607021203100b0711100201051812040306090804090606180902161e05060408030103020f1e01 73
    0x80e031010f0801c0d001001c0c01d0030890306c0c0340400e00304040100c030460149024000c407034141d2b0700c3c64601ca003000c20720341c090308100040548664a030056038002240601c10380c032880e8461440142d40302c0c40c2c1824001a20401003010801507114101044040c0903005450603543d0b0440702030380c01060413800c2005410b083d00d0f4900d50039180003144041507030006406d50040000e40c0865000229094401845110459a403805026250404c00601c1c03042000f50130000c1c403c5817640341200a210105181c6100f20310756a0060b03445005200c0c12220381e881d881c0106200f000986a0f0340003500b60941a4400c51100900c51036443c0000d07424402d04405a4002c2c20100e207051180d5652401e00400098001c1c0c0a070304000410074002500d1200e80c8219001052924100c01c1d8848980d00e94140c00940305403a88100d51203004000000341e02440710b1485107124402c0552254114014403103440400d03030215000710501b840c09244280710f10007070301c011102480c1800b110514404201c03940c142c4900074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 425660818 1250 425659568 425659579
    0x3071443031110091505061207050d231b030c06092e02010c02010b1c0201080c04180608010608010b010c062007060c12110405010302070c0812040303140306060d09020f 74
    0x1500030001c01e00300344080c1000a40c030070b0295403144030800c11102340200302440e840e80410002c00c102c1c01c00b441500c080c179004500001500c0200455010550001141c00b485034002d0b8804020b04c0f038400991403094613069008141001d440000f0038006d20400c1401c41c425403132481580e041041455007002800c05650002c081c0d040362442c041d000c2c08510010a01650070003200d0b20090030180c5150b200e9040303138240d0080e00c0070240c005403180702c4050603c100400c2d0410003c40c45400c466986698140340000c0003814074a848402130865015401c40311559060507180b41c580e80c0c0c4a502d04040c903070086800207414400341a42005e07000040508609081c0c082040e009100e900d510100b5012919201c1c0d100710450400130008658540c1440180c005091109124651280d4050a030103803080b61030f84062034841aa80e490715140c18599503480d10300113001c0c4209a0301500000d600c4030240311560a42c00d04c40c0c002460760241901e440252a981e410381010b650303a8003030042900c00003400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 425662068 1250 425660818 425660831
    0x321060406090c1706010c080f0a0309020a1706010e0108030417010b0a09020913060602070b160b040f1202030405090402040921082a09010503071443031110 69
    0x18080e11a2460b41200440c920313403000068907950040184240d41e50b40030f000e042c0b81050031f00b4a24641d4100d0461034080585d02e4a0355001608c4002e0101d005d407030182d00100c201a08034080c103180c40c005800c09200140e142004002d0300c1c4000081d1800d8a09122055081d01905d103540c1e4010300001e01d03002d07400001c0c2d030400900d4000725030003440d80351416510328051400c1d030b500e400b0035250180f2500006038880759041040c010460f000d0300c4d15202d0405502e030b14a80e0354440559110b001e0390155408941d802141e0708204407c1c0b9034201d058510b0003e90b0400e4036007c00204038000040019008a03161500c5100300881844202108024140325118604144000400340e50085480755003900304160005810481040740152038030982000900c1e00205c1001101c0070307000901150103000c2c13412003080c0d081e00000c0240c14210086901c400301c00344c0b80740d400011400603070300040010903500d41c0030b42070181e000250116640c0509104d100c120305880c1c4d0030710307200c094110610f02900d40074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 425663318 1250 425662068 425662091
    0x9040515040c090623060f0d0603150c080403080c09211e15061c02030f0309040501060c12031e0c051902010c0c2607051509032106040609 61
    0x281c105035840c14808001c010340b165956501c00802c25035107200010005e4111074a440c01c080100882100014900d0030031180000c00d030160303000c507042140e0103403a01203249424201c91061f10809407141c50318050070704050720083c00d406c070041c014031307686400002c002c071858403200c030b1000d0080200c01d004103e9001c0f407000c1c0b40d128181c1000464250440340c102941e12403000030b00740202d218000021141d80c45920030055105e4046010314045030032200d4200143e6000d206845038641480055607441c07000d0010031040b0fa1058000c0030601042101060125001003444030440d000c0b4140000c441d41005020002d604d04103400700111428104034030b06180d0b03c00301500070790802d40c0d14408103214918050b407d803641c1e404a80000344c0400044008907920000c0d01d86820341031506219904403082000752a0362080000b90b078581c4c032030703100941041601c0701c405a1060114000d50f080c910031555902112a42c4004000b529070300801140c501e517503a600000083c071a104041110744400c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 425664568 1250 425663318 425663333
    0x1090c0320041a121608060f090118030e0409060c05040f14030d1b0206131404140a0b0117040c0f0b190c2310060602120304020904051504 61
    0x1000c4416084030800c802101d074105401604500d001449425010448a400344070001805000b102c155102c2c0c108140095000062a40c01401c0714801170001c62034001c42c040922080907110301c80c0350b894001109804c401c4861020503450381440c1c8409500c60460000c1c0250204048c040c183c030385040d040c0c0c091942c0000c010411130314550190881160f03900751000214a201d042540c040c0c102981c4a0380c080e2050300030b0400c000d0000c00300b4425408540100f52141c1200100b840c110300d00100602003911482e0404007020001c803400c1c811100000340c00d034907021029009641554494902c0200340c2e0141d5a51015400b40c400c84010030300d070a0030324414014841c840c0c560800c940e140041450708411044070a41804255244035240040c1d00c112401d003450f00041d0f40060f80c1d602400340030700d40165200d203207800b0030000b044820f214020799006c407803481e84980d05542c0400c050000340400141a04d0b80540c048682d040700b6907490030070500304142c005030501c01e1381d464401c1004000c0c0c01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 425665818 1250 425664568 425664593
    0xa0902180102070f06050a090b0f0304110f03070605090a0506032e06140304080909070908060c04140603090705060d05070207050925030e01020d0603021005072301090c03 75
    0x8000e00c144001051001682c44070300703600410034100d580c504140f1240e801000101098940e034034140c208640c0d42c010514413600001400842000d000003400248800d1001b610b10707021040300c1d008180c00c0a103001a039281050312610040c098042003100d11540c4220b0b0308401000c1c09083c8075a03038941a0186440c001c10300007030b001500079042004404502266a034001e45d00251105c00407440c007440800c402341c200030811500305600f000110426201c02a45134060700458030780c2c0610904013001203082c50801007444800e99030611041091806a000b8690080410344107541d0f20f8440300c42560508010b90401d6401c01400620401c1c0244182c6c851441443c065080c1e40415880b41d0070480c035114181d40107940120030941c51201c540c2d002d5070007950b01c80749040001d501d40c80d104503542660081c5180c8e030302444d55640c0400039400d00317018181881417203140452414101d556620034004c1034449810b090760640000341ca400d0802d52062000f141c0208800709100d41d02d2400d03140a010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 425667068 1250 425665818 425665837
    0xb120c161a0f0408040e09011b0c0308010905070f0c0501020906030403050c0c030304060804031227031205040c17120f0307030e01090519020a150503091b011704020607020a0902 78
    0x440c140040d5115403807840d00d6000c0c3d940007503158500740c60040012000c50024007501100e550f01c020000070601c0c1180d00d05012136142d22011140840c0d4140a000100c0580c4204401070806040022440c0e10500d01400c0408a081080c2e09a02504040380240a40a21b0940181e8004144400e140c3c00101400503e1501003c07144c01c6408501419203900a5116120200700000e01007400039002d907085040301990f0501c000b61002c0d00440910303c08502000c3d01c101d5052801070103080c5944140c14090407041c200041c4124100380e600c2031815045407088601440702092042c03103103001403244098500078500c5842e04e5250b50300d02c11450b40e10a68101d4046480c02c600e0400b03018040c09018280e42d04400a40340040c0500300c901c0200c41d00c00310403030b800101c80380041a050b0f15800241610141a943c035901d9241100a061074201c0c0030303034070216501440c400310322140c0c0d015124800c1001c800c0c6c4030502d541c86910100d80740740501c0b44001c1d8030941c4a000840d00394840c0e80600304102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 425668318 1250 425667068 425667113
    0xc0d031e030b15090901061101020d051501020d0207081c090b03041b08062401050405040f0e010506061c0c0306150c0512070206030109021b030c01150501090b120c16 73
    0x21004640103ca44076025425030007080761401089000e0042c60142d040c1c0b4201000586840218000d1400b01e400845a60391110205002207411356410000c0645c640e00c13900050020a0030141065940c4048610f2004840801c44003209802d108403290030003407030080150794a0381414501901001d0081401860400403103900003861800000e03d1800ba01e2800c45401c40c1030f4200c001d441180c00c05c1020741c4e042c0074081100007402c0d2128443c0c8150380c06100c00000d410402040b03110b00303650300035185a00c03445044c012040b4041d6506040a07103141c1400002800c01e42c0d445040d80980025440514100d4958151507c903d03000314000010381d100e80d094440c0d8116005244125010310003000c0c1d0094001c1c130040c05407690950040c030058010b21032822605100c203a04901d143d010b0500400e290b5104c404a8030014401040304001d04803d003440c0c4400b60078400c6201c2c144c040d014410744012000e0000c107403000c9070729040b5041c1007403409502201c0d18140c1800c12410951146c0d5683c09c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 425669568 1250 425668318 425668339
    0x10305060a0c0e0f04150f03020906060703050f0a030612030c121103120a090804080a050d08060105030f10031704081903050403030f030e071403010507020f0c0d031e030b 75
    0x2890a4800c0c4004020261100e80a00c3e0140d010300005194500107550407076528900d41080c144d41000d01c0009144004020804070f00b14814020540360280009014202c1071003204c00098010003556000e01810305481e0f1188085001140502199401a04070344003c3c0015000d050b0300100f0904110301814080041c014420f10840c0c081c5001c14840f0b205802c184001f1403c40602e0401a420994446020038a10015100c180c100c0e030050380024030b076910001e164020040141314010705003446003030a02c4640b03802030003c0d007244070081031354080ba103011001461448800c045207016540014148083c045031042011860b0710a010384029440303503200d008d0900c94101e0b54015031540c140d44150500386182e40540d01c0f401a41070680a1644401d90211501350800441d070050070500f210004003010407090600b1100064407080464121021050a00c040090410302c01d000c00e07502e954035075680e0f0508a490310799840141002002c040300e6404065070517000101207000454046030030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 425670818 1250 425669568 425669581
    0x60901031b0b03460908090a0f03030f030504021806031014071d1f200102041a03060d030806040b060c1b0a03031704080405120a0b0c070b010308030601020307051501030506 76
    0xc003070180c03220303001d1000444410f80d15100e4101940951141b8030160410030b00c0c00c00603a10910681060000c2044041c00700141540445034041d19982424104050305054002c911140d1100c0c070075400c2c110aa50128100e82c03400c10800010119000041203040303221016460a00713810b0320701e580000c1c150b80244091451407080018102c40007040c1c1c2c03e03001d03408009410841600958881804040315800d8550170340302494044480c110000160344a05000e0035034000005039848171081d003c1441000038540301c88548240407a007500302451a9911000000c020341010000503404c03600c04203003000d0040c40050110014170f0082d08440112120400380000141d8910001d00080c504c4030a001e1141202407645402c00e0155182526183e115404100c82801d800e510208581c0042152820300600f100031030b81103404079034641c6c60180b41c0c3c0c4a4903448801800080c10b44440040414500e030f008104850b0032546c88021380b46918091031070184100b20900c400d813200e010340d0000498 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 425672068 1250 425670818 425670901
    0x703170109020c030d2a02010603031205010510180b04030506010509010509061320070819020d0203090411120c04030312060509070e0307030605091f05060901031b0b03 74
    0x840e403c0004505100300d00c2070060140c94402c4480b00c518000c01030061a003181140003040c2c41581d6000480e40500c5c51030001e00c515580080e0314a003178a0880144201e95542d280250308103210700c1c10011031011076034040f01403222075126060200300060700004000020a10b0ba040710012604060140c1ea94410302003803d1040f10000d60054408030010b03030700041d96000410501d086c400440004c5044030380c1e05102e0b80426010b58203410b011450707030302941011413074a68042c89440075040310b8000c5500650350f40500c44506e4030403a194420409000320080c141d40c0007841c000c3c0100c41c2802c08107001100b42e0300a02040e0000344403501061007500300c0703006100843240003814880786c039525008211042070031151403507814019810004007045440c040c01d802421440040d251500145001288807072040202900d841d0522042194680e0b0380c3d0b485078110ba4000b4070360342010082010540c04425a034100031441407011040c04030040140040060119030b02e945100711b0714030a0f01c00300c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 425673318 1250 425672068 425672077
    0x34a01020304210e04090605090f0a080324040207030801031713090e0f06160e0a030809060f0d0504030c020a0506031014061e090405070512010b13030503070317010902 74
    0x30205110301e07054040000c40f080d51004102c1c0d441c9401000584110009400e903055000152041d603200c5040c4200c005040c0031840c80c440c1c2c144014180305209039503030415400002e218824010031400d0180d84001d107403a0082179a400200b045550340580d103006440384000380001d50380d4940010042c4107040b0300808980540d0101c42804400614000700400070740740b86501c0c600c0790302071954107150841c02000064040c548419144200b1900c05400414209124410501c1078440c0c000030000300e43e403001182e25404090703841540d11144541d040c4060b1159500d41c00186140030f0408c0145948103c040030142e2003112070342d0f507031a03541c420441140030581340c0d6160361b400c1e8141000140a550740b0400880e601a01241c2022590702e062442c001032840424502d0b00005401c646528242c42240c2c3e2003110390038280c0c2407550340101d010800d0014084d9041c5c007100003a404043d000140c40c1c0900450340801182e07910065454006d000044104134901400b10f15400822640214020348 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 425674568 1250 425673318 425673323
    0x303090b03040f020409060216050a03030e010b0a030615030210030f0b1f0e0a0911250335090d11031e07060b30060402060406034a01020304 62
    0x5090f039107400b000020103464200b02c9642c0c0c3e08001f0700001080052401c0d005900840160100f8840703410090700751040c01b0507046450340340180700c01f40356803022003100c01da03138000400003418410200c521400c58980d41000c0d6221003580d500024150385a0042180174106840a110004200d0284181c05002c071310f06201c0022408143d01989110f40d001486240006044040042d600d0490b0300440c0e0f511b128520f45001e000079110070008461151340c0b0a013800d43c0a40311816441d880c002d0500215004491440034400d80c0144c1000400d241501490402020b80e410380c2403800c0d5503580c4001144500b400b2a54103000f800c0503002c040181c8500035040405c0d2080352210b010452741c4c56100c1ca0040342c9031581c0302140d031007541f40c0d80801618200e4052168201400b06411403041010900402549034410402c0000680b80d0380c051764221541410007062040460703031945c00c0b0043d05c0d62110405c00582907254004d45002d0351780c1c010150001c1c54001a8800484440e00341d02c402c0720b02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 425675818 1250 425674568 425674583
    0xf0a02010c140709061205120c030301030b04060f0518160f060c0303091b0608010b040302100c050f0a050c040c1806050705100c03051905070c0b0a0e060a060303090b0304 75
    0x10402c0e0940382042499581d05807000b054031410402c003112070613001184101500725100042080400c241000300340d4051042d418a0350074513003075940b4401400014600d18a000200d0304100c51a00850a00e80d540b5000340020324080300b18512100c11408684521f2003001800b103038140454100c10203641e00c0074519012681031560558064801e49411020150f031004ca82c404600044030140d10300c4005051041362034a003480c0144401c0c01a040b985052104104c00c200580e15100e0014845006040c082070100e400d09007179050040010042c0780c14060070000104008011401c0380308844203d404004000d250301007122812160150f0b0002c5050b545801e04c001405140609800c038030843c100c0d4040b40c04400c81d982980d00755107802001c29190008e010100106100407440c09081e55030401680c07408040c02004007003a804081d042d4459403010030458056030704034540c540049011100300b0705018010500a140a10040d80052411080400c260782003004580c0501c2c0c00900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 425677068 1250 425675818 425675837
    0x50f0f04020f190911030114060a0c02040b0d1a041b062102040b0f07060c030c02060612010204091a0307060804030c08030915040f0203010b01090b04030b06030309030f030a020f0a0201 81
    0x244400c400b20500d82c429900c1000d1000101144203000d5603131140500e004240d00c87d45440004103c224440f14907030b02ca10740038803521580390760080c0d040c400035404aa010079007050010209070307203a00c013880c090951a01901a04005058003441c54080c604c80c070b4401c0000d60000040c07881c607000310b000e244000340780042c41103460410984a152101c6403c42c0c010304d4580d4602d995540c0303a03c2505115000d03c0085292010f02c40d4a2241a5030415242070a010b5028210b2000f525038000512907445445c0e1200031880710002581a03401031f0400035010401110070613420310312504800d0101d0b1292244020119081d803089414a02840d850703111084e00711429503e620058200a150703407058485c1b888031441c540075160b04e8a010b0760040045411001e40c0303005040c01c1d0f44149400b5410b01070109810054102020100e8007100e8010581800c40c0d200c6c80002130461103400e410b1941881151044800044040000d0552103255000c50710101d03040640e15031079250015001e8041101e045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 425678318 1250 425677068 425677099
    0x8040b10181d06071e020102280c0507080102040314010c0c030f030b09100512010507140c03040503100b1305130308090f0609010606020f0a02100f02031c050f0f0402 73
    0x8010078a61108011080c40b005160360b11903261020071503010740021818048921000d5001050100c07482c0036100a41c82c06502c0036011108616002824a1200030800390300e5500e442000b00303540c031550000c00d94050994a4544034043d420034001600c1d035191100c0d001d4029001485010a003c4d0386480d0202c83c0b00e060788040c0d40d140300713026941052544a14a039410b5581d040e04c040d101c0c1e800c000011241c5400c240500c4204d8030f00d1500c40034541c0c51f05c010300105075044090007498070120181140e50790000e55002e4114041c9500958051160007805030305507413181c120313099152064500003c0c1c8035004014809541052f00c0141d0810444205000424840e615a03503101500c50110341d007a0014a58151418200b101d82d480d070f5035522076040c0309031541170100c0750b80850b0b05001000c0650300c0e90009410118645d01e442e003400004000901e1f681d0080c0280d03219007543c4508045c40042044800f07004c0c201c00c80b140d0380f91889080005500c2500216690b0042e90060507040c248840e15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 425679568 1250 425678318 425678321
    0xa05040b0d111305010608011701020306010e06091302120a0e0703151d0a0f110307030213021b07030f0c050114030609060307050d150c0203030132040c08040b1018 72
    0x2c2c002c15400020901111901d03210b00c1c0507442c001c1c01540d4443d401c56140132000310100301c080b034000ca101d9004009200c03e41c0e0b44900303410910a03045036038581e03821013900080d490b041501d94003e0814004038002c0c008101400300b4078404c6109001c14040c43c28000343e003544400c007030300000705110b080180e4213010192651140c3c10b0719503103541790781c070640e00c03540c48902d42108110100d0360428980504002c00c4000140071080c00002e5008088180c1541e00243d0b0040d0381c1d031510150240d011076684040b00d490081810400400c2c804da40143e80c80341000007a241d14014152003916500d10006180c1d44035044900030f00c02608840c82c11034840c0c0003000303040ca07809411140e040c42020008102c580daa1410903500e64032400c19004070010300d94010082e03d2402600344290742061004200344549500c11403845119841c540c00340030b0012502c031003a070641d0340b007044d0003910b0444050f41c440e422458990141e40503948400d125559040d403e20f030501103005038510241052090a0f00d840c45 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 425680818 1250 425679568 425679593
    0x1410090609170a1e0c08120a150605090d0204181203051e160c1203060518060907260f0108100b10030b031e010b0901080606030a1103030c1501050a05040b0d 69
    0x40c030786881429a1741d00e40013000e070081519110755107444418002219524440d0340040c81101d11074403001460660041c0c2980240d91510307000e1040c0c440000219a120f50008200390f925400000707804200d41403508500f40d1080150000c01c0c500f50104805c080944807800c0c80469581c3c000c50190f45030032155040140100880c809d0001c480d00c2503000604e10a40303220003955550340080c0c020700e400c0801c046144810391403004040a00140b01590303d42c1342186600c00c11504101800c0a03601801e8004002c000c5440401c00480e0003c1c00b01806003401202c0c100d500c94001c4400e40310704914584111030b01c0307500c0c40350702100c1600b14074041c2c1c6c0241c000704d0394074900030113a0720078000720806288589103403400b11940365591840e0302036030700d455a01da602408050000302194604140800d07503030f000740003010380f0718080c6140f2682e8990b0100211101044034800766000d0010007005290716581c02c3c010140b281c6100701002c581400c1c98441c09480460007010b81c2c1c041443c0382c4401001020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 425682068 1250 425680818 425680877
    0x307020a0314010f1103160c26071a070f030e070e07050903010203010306020403053d0209190509220605100b0f03090105010e04020d1410090609170a 66
    0x403681034100641c8981e200d5a980c00011000b042d40c1e80c545524401f11130070740720300c000c010b1002009034a000705202c0480001000c1c0c2084400440000c2e80120003a540102c440040c030b0000e40c91954241204042840744c040c8540d602e600c20041904502030307084c0ca0907145c03614616448880c0c1000303000940305601f50031004c1401c1507440d10300c03010080b81c00ea1b4004d070401e64a82c1c0e00010700700b0400200f081030054030464101e40c0010340c0fa00b040407503d0022074134004680c503e01000a0103c0070020b504413069124020303c0078a00118801502e0704c00461031280e0351280b408100014034543d01500032084901904060141c41c13515650f030b0500900c3d0142003048032840c002d40100b02007000100074060703a100303482d441d82c43c0d240c0415200d0075188140c01146421205d00b05210068a0302e45082c001d85a102802100306903400c159146484484403031041c1d258240301c00c4d4001d000c01076000d0003009010f001d84202110500d00d4021180c8614600f50000070095900d032541c0f0b1068440d00d00314542c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 425683318 1250 425682068 425682071
    0x90a0903021c091a0705070b0906040b0c1603060f060603020a140d0612032705010e0616020a090c14070c06110a0206040303090501030f0e0c060a0509030a0f0308090307020a031401 79
    0x39103800b108030502c2c070300342c0c1031041e8890000f40741c171300b0310108100c082c0040042c14480e03481c1840d010b02040103070146204255215078003048410345034009001040710301d442350121141541d40c034100318010344021303080d0010080c9410f8000c200342d4030030700132030f500440329844883d40c1c030380d845000d001103512002030111210703a500f030007103143c03070642d0203011300c840c00faaa40000c00c004136510020480c0800088041411511a041196980201c01c1c0a060442100d0281d12030003401c4411411040c07181000354007161405010441d8125507000e882d414220703585481c1154071410b01143c091040c00c0020708009072040b0b04010881c0715035103e0070983c1c214002d0321020000c540c003250b80c0c1c3d0029001280440c081840502c0696410f10444030702003460001409100516109551146a40146c4038002d010019018150500071811145103050146c1103035404806814810607550340244105c0002d03540c08041040d4200001c15100020340080c07510320070510b10794812480c03604483d109401035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 425684568 1250 425683318 425683337
    0x110613090203040317010e0402090a020a0302160501201e0f040b30070c080a0c020a090c080f01030c091a13090c080f0c061e0414090a0903021c 63
    0x511500255014a100f0b41704c0d11a1106800c01c140c400c1c4005801444140d95880100400b40e90351207011500007001a8005a40c0c0d007451900714040d02c00c404c14000340082000c4030f4002c1220560001c4a0120b01040d91040301c20368001404e0a403260118401d510860420300f003030b0301070498005220b0840d00e054100d19003a80c480000700b840d0082403141c0700b80c0c80038040b00550340b0b954000070040d030a0008500d00051501d028040c001948018001d004020085034501c505801100b0040f02c00da0020004221107aa9020901c0900344041c171800c00122000301140c100c0100c1d4107542e051b02e42c0f00c4074899a65041c944820300804848075000a1240320141d10900303034903002441004c501c0454804500c1178110b0504622005e855031095100e544040c4034800149004030320b05288502c01c4a07071a030f50304010706522803e03d20680c112030b004400018005600002220f00f021410070035a0440d8241d640c000e100d9040720058840500560010000640008111241142014003600341035044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 425685818 1250 425684568 425684579
    0xe040b01051e130603060e160e03031b01060605091f0504120b18030f1b07050301020c0f0c01051204030e0109180c1202090d14070801020a0801061b110613 68
    0x101c0d860300c1c41d10345542c040022108610080d4111001c041c0c0007900b4180000751425403400c6010348014520f10b404901c0140e10040c0301c0c8039051145200800500301c9440380041442128480b8402d0441040c030f62070070707800081c454010410317668109030082a000143c0032005040d0700d00300b41641c14008002d002c10020440c280c2680c600c0d41c80600a401082c91440c2034103440840308a10300349444c46038420b0084140201005086448418401d07080c1c6003d64032034100310f0300d4900c040d04201d034554000b1a20951420000407000d07502d81030074044134121480f071801510184103150305100080f10000010300800d000d0070018640b410185010302c803190399070240c13007800b080484204800302d03151741004402c254000820403440003504411480c000d440400500c00700c003518030060040c1b86407111400b131170740140080300c01844104000d40d5030f8405000d009003c400d0034060600410f488051010303144002022001429030f000d981c3c2c124485000d02002902e411502c030800d0798014100b0301113034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 425687068 1250 425685818 425685847
    0x12020409180209060d0b0c07050304030203030a0203210108121803071509090b03060f04020d0506010806041401050714030c0f07120e0d0542071e0e040b0105 69
    0x10211400a00303403482141881040f0303a441000d01113074442c1da1004030f404007090409010ba60060303003d89480d561a129450a0b500f1409103500c080d5140c007002c00c8244585070080001e2822401040b840d001c013840c120741f03441740000d0030301130f0842d9513000c1094549240781002c0100644950345122401b507884240c00a45000340503000500c2170002066a1003699800c84016005404000b8060040c040c10780302003903840400501840c095544a00401c0540d00da4030031840d5065004000e03a8919070f11075510720b0f07031014281c1c3c080794061414205060361020600c01e5034024012940d4032020300208402005954102609075054050204016804076001d00b008180e174500c502103003c103002d800200a451441455081c41c010400c13140c40100050000c0f07801801c03070407190703401c441303086c64451f10400c40001360700c00501d00c1d8545c1d50038101104d0050110f0384a952240d03500150040d046031505140301c2044001c00204121400c030275954640303138000c84104c500c1032600c20300f0440b8416a444 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 425688318 1250 425687068 425687081
    0x70f12021f0f0e0a230a150902010e0904060510060c120c02010513030b0612070b0a03020d06090e010e06180705060f0c07150f03020403120309050a020916080610020d12020409 77
    0x544484c1e910101c03a4a1012104000c054103406034050400c1000c01e031500074500c1c0741620451f034150f688400050440e80582c03020004c02001510110007441c0c0741ca402002000181c036003000300d0220040004455208007041c108956021046000c000d800070030540b00c850110300100c1c180107003401440c03140580c55003040b00030740c011500e00366181845804e12882c016952001c00981e00888401e000143d1003408860900c0f0492400507035038031a03400039034000d0002e50020440c05007002759524180340d0540090381030969030b40940310070340c81d081150f00300000303082425502030b0000e01081200c0d2030310202804148811103401841c02c54002503180c10010141c0001013451010400c2d060025400505c4000d202c84034142145880d085440704441d106421810100f0151101c0c41d400402006024506203540d028040b001a8140494031007900302514013144001050300300001c04500c1c01c607885503000c0009402038810410303500400c5175400c818901078520a40c0070440010107001d94818003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 425689568 1250 425688318 425688323
    0x60b03130c0b07230c030a06050105010e0d050c01050c1f060e1315051905070918020f0703110f120406090b09010210150803070f12021f0f0e0a 63
    0x862161916240e0701e40600e0b60880c0d0922036050001c8000a1803240d088140802c2c000001420301640ca11841d02e048005254560180559220700e0308000301508454103030f80e42622920030240b0b45c101407182407103003c2c1c40944944e0102d094121954018802843c0c1c0142aa00355100410030b0204050000098108154a41d0b0348000400004400e8042c19800a80265004491344050b4131058044402103d0381c0c03000a903120041100034564070288034100034846828800391612510107010102c1c0351044000c0140d0040e040c40e0241920302c2200c04088a0010031030520160340c50031112a54a0200e0070640e2080c111083d000d41002c12805a012107409203103681c032410820024014000ca07400242c0580f01480301d03130150307a0003285c002e4501d4148a80060307031041ea01c202c8104150568400e209900001032608203108000c200c2c3c0070341d14024480f00e12400d400c40412030351021104900c07000d41d0a40c0190491070862034110350402080d0b0f20010941d401c85030303045400c24a6001c0308 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 425690818 1250 425689568 425689591
    0x30c070803040b2502480f0102010b031b19030b06040b060301120201081f08071d01030f08090d06060b07021306050f3016090203010f0e0a060b03 64
    0x304001c503c8070720000c5400341880030584440c5014150081e43d140b804062003d100d00000b83c02c407103106c06d403004a4002d032174030340c0c959241410a500314154400314409004d02a6000944108144d401400f0703401d50030380e002d0020000341240790401c641034007440e500241d0050300300c3d06c1801c0c2c0c0d920707414a40001d54050f0f0782c15101401c01d0010042100c4441543c503018840074001005091850610ba104668081c05d01d01110b648288154100d084c03841c260700c060860101003c140303510005100b00070f4481c0000902280407002d90514540c510901c801010290901c0c01c0c0c400058805014040420001d848900b207104159244000d461003034010320b003d0003010421005628000f03005c2807514000e00c90400c031050412000c1000d284451100d14001c4900004451141b000b09013103148000301c010080d1420708000441c00d4540048407a85a0445000d80780428400c1152003200d040b07030a10800c07013464901d0110786500030540105100340c056900c40e4005041c09001c0c005500c60039080a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 425692068 1250 425690818 425690821
    0x20a06090906050d0c030f050f010507030903020c12070501052104060b1e0901061b14060105011d0a06030c031517070b1804020702550b030c070803040b 67
    0x41d01c4100c41c0d440d0301242c4103608408260300840e01c0d100180040e650031034950884030480d4103000746070151a084500c6151318003c1040502d942c59030151000c284a40d00b90758070b0010600070003060080c0d02c4980010382e000150300304110342c040c1004202040c881551090202aa515a100307250f00c200c0c0d040c0e03000c2e03486a92100b80341c0f405003800001e00424a04550b034141038400814013130324050040c0d00034031500310140700010302c07550011f089480c1d11141c18616015a203410645422003031140c9400714003d1200d22a440e81c0a505038002514082d0241e403010740703030842c11006000d010380c4900174103031342c3c11907800d00780301180540000d09618048000c1c050002080f943c03600381d00d6030190361164406d012128540302c1016918070030750f10850b0b0142c2c0301c40c41800010b0303041136100007504024800e0300b00c1a00784500210103c0c00c00303071400500414220302c0c40c1508400c520b017807060210f4007100c6106003e101c0140d0042c6400407402c00745181085038646c3c80f815698400c1d07806130740c401d00b44030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 425693318 1250 425692068 425692079
    0x5090705040b030a030210051003050111070614160807140c0a030e0105160f2d061506080a0f0204080109050f010c02030418090303110a1d120a06020903010207020a0609 74
    0x61400e640c442900141381c04025074500940740d410b00b0404201e405d8498021842c64030540522801131070700b0070020030418040b10080d07181035122100c00c451440c14500c505c0d00347c100103900c082c0320b0b0a203161403460221031000103c5008600402c25014480c0c4c0ea030342041009071000c09000c1200160009150340841030501409c000c00c0b01103070904100701040b0090302400f41e0807800c1c888981c803c0c03200f14050420f10703000b8403441c90801d21a6005144500455048480c0c030300003031805000c0c0d01e04004245400021480c848180e000303840206034110082040e40c002c1d58000c544031101004010f06268440d08002d0075164200411340c0e0b19840030305810780c1c07a0b80a2140070ba0b0160640000e62900b440c0440e020303110f0b158014118245c07079a412016003414000d4002030010b0710b01c0001d007a81d8044001d4043d08541e144180301c102410314a007001001c0c00c0c05513464075142c00ca000101007a112645e25000031b544408401501550248030300130058582d00441c1015102d603450b0800c2c1e007820702 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 425694568 1250 425693318 425693321
    0x70e030a0618150203070512060f09070216080a1a09070e150a0905010e0105060a12061212030905061807120b160f0f050a020c0a03060509010e06060609220509070504 73
    0x41600e004024130400c1444241c68001d0100c41d014440d06a2466640e90340100141c503200411095a800c07514a00410040c0c680c0410f18802c414280f204007410540c0300c10b25113903202841d0b04010092102d000800414010180f441e607842100413040368005030716407400b61407904c1c090304c01440040321800003403110314101d9910310280402980030421580341500740303180c022040c4181402103000080c282c403c68844c42c0d140030b10055103241071140a5071503052110385c0d45552030654050303058038252170209120740500104150050b004042a403203c034030585411418241806407440b8490700020f003039400c0280c192072276000d048001008d1612010b021400611040792204004507006907001158200c0174060307a00300c1514185455442c1060f05903d070241c0100b4159000d9506034001081221680000723200d071000728003d020004500c00d005964400c1a50001ea018009003c401418100b00d4841800d20606400c0407212515804011040740c1058600c41c02c2600103e00502450034a03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 425695818 1250 425694568 425694593
    0xf060d02130c0e091303260709150c0c0608060a0f0902090a0e0c0418060513060303030c050901140a02151306060b0a08071409060a020303100504060e070e030a0618 72
    0x113a03407450252400f40001120791900110060601c1101c10303910000c0213500c00415403004c0084040112810300100c050180c1031548610b60507884034402d07040900e40700f100850941a0301500d150241d60800000f030751081002802c03d07402514581000481c00302110b040c400074819100d0041c0c0c5c41d040c0b407040c056120510b4009810f0307545181c042c0301c10f0b4000107040b01d0446503d1061040000444110f2902a0600c0d0340b00d070340d20003000e00040740c03400500e030300c0502128480e440801c00ca40b000e0400b41e40c240640301c2c8503400305110b045446007400b4031600030901100c00b441035400c4503900e2048044c4100c420f40e5505070800c161500807041004038801c0c20090500303003050500f07044140320000c09541004001200700031040d541d80204480c0d101c10340d400380300010040c0d502d4074a0b8080c000d40e25041161050010800540005031034102072180c28165075a0355008650395840f107000761191481551002c0c1c00d40b00d18065100070460a201d001000d11110304000301d6001c8034204103000600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 425697068 1250 425695818 425695847
    0xf0102010b0a0902270105180103090b0c0a02150603101a0d030504030b0105010905150a031409030d0b120a080711150a02010b040b130b0312030c0a1101060803030f060d02130c 77
    0x1203907940017a0307138200c000d0701c0b0042da5030500540b28100c1d03000102c018290b07295004140d0b0b1014000d1065500450002e000b2608169084600d0403840c1d8620880340c03a800c2e05d020344c0541150180349500b98042d001550074a40c2a0011703100d1500b80008960b0542c0903090a8001500100f070500130007501c6080300b0b005042c00d1804443c03041c14800010719104e1450004001418002010030140f802600000b13408400c1d40500d0b0040d141c01c4428035100e6010922820b440c03807800c2004169803400700314580c0d500d50840010050b40c10300b0703552040c4a500c05002900e07482c0d01d402c500348859a92640c1000c250640910283e11045103038406420741b50065000b61145040080346081903e0b0710700040e01071031049401194082c60500802c0c02c1449000d0003a2080c0c000208000100802800600c5c00482c00e65603501c59074a46210305080750f43c40c2c050000c06030410008100e900c029090750b41c0d08000c4c0148110b41c840c030320b9800075446a50401c50001001c0c2c40d48104540c2c550003030044040d030407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 425698318 1250 425697068 425697127
    0x204170307080301121112011b020604050717030d0e01060f14011d060d0905010c0905010906050717041215050105150708030903091002010b1f08060f0102010b0a0902 73
    0x141e0354500d840c40c00140900703e55000e5103e5200107000020382140b04c100341c0944403484000030132030894044c0a8581c5d01000b41b50810b03a11010061001440c2881950008060900c480c1050b074030401c0c010400c1028401480113110748c8a084010380305d1442d10021060000440d0b80c40c086242c108004160300004400c80c015078a002d080e6005169901840b594054036002c1c0080c2c540001c0c1603000b44440010383c1e92400481d60100181540b000d0840301c031544a003480181d8481c011540941d05025400000d1030611011000942c0341401c00443c000c4190624102500d501d28801c10081500040d103142208241c120552400c500c1841c1c00b60009030307010380d904c80c15400171034418803e210000b08904c00c0080040c1080006000b80e512008005004d00c042c03851504000f070207008100d14451003881c4503000a5860002404110039011858644940303503901c01c0100100c12050003590740c195525100c0d24501d55a0300c0308441c0281c031914100613101c90140c141081c00580d541458000030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 425699568 1250 425698318 425698327
    0x40612050603100903090f030c08070f0501020a0b130b0a0912051305060c0c041805010c0503040201090608040203100606020304231c08070b0703060602010509161a07051002041703 79
    0x25140895070000c5200f2030741002c1042e00300ca05d02114103200d01c0d404807182000000000c81044140204001100e40760001c40b0490340c0c4509000e0350040d901e00c80d090142c0c0c401400d400000d1500c581302d0390b00c840d01021342c980008540e12018161001240c43c000160764826040b410031071030582c0151805082e14140341801ca4a00d5040c410840e18061207100b064041f40783d402800e02000004000e203405007041c04411680002c160003403d0280045841c0c0d400c3c01800c200f52480358003a01d00ca02e4050759400005880d2150903070300d102014006980500503003002c148211128020b03103006003050740c02565164545059081c4000900045030942c656505800000d41e4940c3c804c5c9518030810320100002d80c01c42d2418210718454100002c01c030904c54001c0140d00da400d0b602410032909141c009004950b03c1c1121380e031302c4501d000d4030715611644860050128074268200c07800e18504040d074241c40e1640b0394071403034a8020480c20a0a0b45600000c0034005a209408075101e0001c0381401107040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 425700818 1250 425699568 425699581
    0xf0c0e090c0c1f14010b030c1c0e2d06010302030601170307051b090132040f020d0c0f020d02210405280b0412152004061205 55
    0x40000d00440141c140224481c040c041090003402c410381c1001c903044110641c14802207029141c45407180300368210000002861070040401c8910454104042c2c500d80005910150ba40003d080d140201c015922018407600042c00c12107504015159240e12090070a4900f0307c040749011003e03904019081400100010f8400080c82419206158003824000c010305000300d146004d00f0002178000d120310701402410b42c0325058448040072041d140c0c1c000c1a07032906100c2241039043c4000074442807001c00241c194800e0b40000b21315130079005101041e000b01401c0003c0c16070f0880041c10240d55582c0c1e455140543d042000d01420000e0b500140800c61501100079444038261a0f40b000380205807042c089090b01d0354002c80303014107001802d0303080420a08041100104400c0011050b00c03918550100e026880e01040d10110391340c051040d041140603543e143c0d16004002002c00d0341c0c1d0388540c40c282c0b0445403061242c0052040000c026211450000000e14965a01030000c0c207881c5480b00b4001e8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 425702068 1250 425700818 425700829
    0x40b1009090f0210020a0203070b120f07051608041d0f09060c0307081012030314060103020f0a0311190c1b030f020f0114041206110306010c0201140c100f0c0e 70
    0x1440e0104e034a40109251900180d05021403c10000e5040c0908400803d106400782d02425048881e41d8603403409607181c00074250034a1042d00c1c1c45002c85c400307001c11a070901052440e412020311486003241015603445441ca914000b240508021103148002c1003411901420003507449994080140010f00f0a204203010910025084004103d0081c001503402040a00b11100421400c0d500300004405414020001c0510a08103900c40740b080b00851031030b600c41e00903548000c40e031907000c5181c8125160190001c241014030100e80000c20711000b2545101040e1006809500382c540a000810500d00700b100b0010500048480c0c0400c4102032022a91000a01d010700d5815240c9005241c038000040c0e6054a50201c1d60f02881400100420402000459141c02510800c1c050200a0410012180034007045030420f0000e40180d400340b0156201e054145001d0607280e5010380741c01c000716003160800303022a03001c40301940c03900100500a10f9601c1121622002860440342c00300071a0001503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 425703318 1250 425702068 425702093
    0x1050106090e1302060f07020108090a0b01180e070306150902040e04060b01211b14030a0207080f0a05070201080a0507020c010e0609040e070303030510081c0302070209040b100909 79
    0x12a0902402c0004000d10a1860307000c00380c43d00242081c4d21240b09100510065019090803400501716502042c503c1c0030000b010302c1b04c076520403580900ea82c01d02400c0c2c00703290b40034645841a640c4038800061010f809005070070117140a45000305920300c1005040d0000303045544142d251a00c100410040c0b455050032850708254801008a240098040100c454071202031a40340315040e01c0a4440d9500c203030394022a000d14146201801040c603c00d016034500c129001f002c2140101040010030500031a4010f107001d0703100b00e00c0142440020844c0c8000c1d50800404840070a00010f034407400d56822030001c0c1e920508a20f4103120521b48040025254074071205114144400600107181c681c0c0c9610507140007400c017038000c0100c40c1c804203885540b40c60512098020a140c600494040b01c03200300c2500582d0798000040c205068140c400041d030a54007441142015030901c100c400580d10f01d04114082c40c02070801c14101d0a000880c079004004d076a011010a40c80c06c0f54803400110142200e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 425704568 1250 425703318 425703329
    0x721060c0507170715020c060108011113141504150207092318011503110a03030f080709030c0611070b1602010e1302040e07080615040909061506050403060e0105010609 74
    0x15511101c482c50b0000c5e000780d400c0f030341603103071030004c00c5148610704006070f0b50307041302e4810000707211401200c214820316110341c2000143c0c00c10010b805105002e010072140e0b298000141411900075035415031510290469004410761b1100c0702c08282403a40d040050320054070360240c08101d41c0a440b4040400510908d0055014101e040700103900320550780400240d4904090081c003414007801e1b10600011594081102c240b00f40b160410a541450b42c40c00e8140c0b54551960402050000c0040c0c450b660014140301c10007030141008400a44040140c1d0014600c68a03060703205008001040e04007049500825042d6005001c04804801c4c0d18005c80003154081c02c2210012443c800815100d140c41c1d00c0710b0040e41c0c0002000182c050440104078859061943e27012407030b4031440d08200310307620104044d240c1d54000780418442400c46a0001e02401d214001c0000c0820101030410340f68030f00784d40104c0c00700304085001c0090111600800c0d4407107080d00020003143d814814060050300041c040d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 425705818 1250 425704568 425704613
    0x3030f0e0d0b0a09080418051f0b160f031106061906032310170105040503030106031a040615020d090e0403050c100504060b1806150a020721060c0507 66
    0x10601c83c2400d0740c030141130300da081550079580b507451f9140d071010b00c1001c44401c2d84462409002031080000455491545200034501002013031a0190302d4415820990100209003030000001e8000340d41112483e10983c801c0d03e841c003107030740700103641424120b006048a0043c00d90300d02003001d02ca0752486120940b102414001040600c50485050300d0946e004000041c1d800103061007250107624031101e080301c01060702c500314029410300da1400d890381914000c29580c020300041c06070720301a41208003552000e020203a0040d0308200040c0c00e0b145154041602000050344080410f6414000b8280e942c0c0c00d410007250aa15000c042e140d21540108050100a03011031741000c1200144000b803a1610707015418025400d06003044001400d4441009104030382c4202400302c04050941210b205001c000c0002004840ca506d60302c1096100ba455581140600500450501104003501802c40c03400148050498001c1c40c1c51800c49030024420f03000d005003400b0f50380008a502c601c0c8401c040300c5940707 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 425707068 1250 425705818 425705821
    0x302060a0c090305010e011401081603110f0619020d0e0f090907080d09090b0103110703080912270409080304080a020304050604090b01120204050604050603090f120403030f0e0d0b 79
    0x90803100341d800b80d00300030442c0d420702071106825581500203001e0350f1111482040d090341c0e11a2200e030b446640c1c0c81488110180188204049010394030707180b4a01e0006066444000444000500b0550140754040b966060076881c4c504110341c10001080c4118403820220390034540760000440d6020389080540c8034840c61000940948024040c020060221a04459031000c8009016288003a64000c0e03010340340c03810740407103410340c880d00a50b215001045050391600100d80c804440c0781c400107102e04594854940c0d140700da012503034010700700c0d080304485401c1c240b00b040b04089041c0482d6500d0b03a200b00d0410450700042902042140c4c1c0003544400c81a41e41c1388880c07801d90071802503034003e81c2e1000c0c000c00c002480014580140d02020001d0b80c6070b0000401c2c00820804a00440c010ba6421010510062189052843c0116081000d0b242260080707600503c0141c41c109400285802c0f5600c089410800c058004d1600c240c441d03842c0c20611a004c0218001c00c5403004030301400341c4031602550 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 425708318 1250 425707068 425707091
    0x90a060509030f0406020619060f05040903090b0f09130501030201141b01050f0405060a06140409020406080303040606030210020a031b030c0b070206071103031303030b190f06090603090302060a 85
    0x1c03c0301c1e400b121510042c0d8030f860703684a010307450700300032582910003803595150181d1420709881503c0507a4106a10701c000c25040100380b0000f400f051400301c0900c260004041145490180034007604034111000305e586c0d840900501807021300350101811005c1c1800c1c01400142e07017000340b484140b003e09621036183d80341152007a8112224a1250510354649414020454003000c1d400d84074034000d81c1103400d03030345981a407d4100e0b0400d10880c87e40b20300300c41c403007040b910f4950000c4c0900742c0018800300308180c4544010341103030f1059400325000c40d620b00082003181032030480c0801d1180203001600702c22503e07490241804640d07100c41042c80007402080c008041c0620309400c1f40e280c000841012601c0c1108000c0d569803c1616000003207850b9504045980700004104e905c6003081d042050f02d1500d00740da0940140c81c141040e2640841d0b1501c26600e0700c01c441c454103008203518031110b03844528100c0c000d0041a0650814402c1509010071640800d800054541d003024524000152001074407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 425709568 1250 425708318 425708323
    0x6050a120c062321061c110102010905030c0d14040e060904080c0d0c0b09070f03020402071a04030c210e0906040f020c0102040f170a140304090c26090a060509 70
    0x43d503003481c8030000841d40e000e5016030000d007080d038214018461401c98070789008100d44101010140801d00d4480b0f200200000c00240c450b031003042041c0008100d85105581d19421900400d00003041e5038030620aa40b0b0142d800400c2c210107030007000350a0b18150030000c08100412004007440d00603400c400104040200d09411281115600310544151494080000f0248400c17840181c41664442003c01c02070600800c1c2101280e00341d00789507030280d1540e402c0c0006074000c820260340d83c9040040382c0c0008060040407c3c400c0d4865900c21115044030b1600103040b00c1c3c040040015000e82d03500d10042039810245030320f030080c8201d5000080b80d4907030f0001009081011070901c4080c1c0085901c1c3d51800054000c0c0096841c440a0000e1054072841c401240c000d00b0018040150302c129803410200300d08151800840440307800380c03403400303494110070030968440582c800001510b40445900100404c5003468541610b154100124203050014a503201c525a6010381850395800201d940310004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 425710818 1250 425709568 425709617
    0x3070c031205011e0509131b050306091f0b01120e0f1f0b03010209060a110708120a0e010801180e030702090f0601110a020102150403050909040606050a120c06 70
    0xd071141444150303190030341202080c1d00804800c1c0d0410501e580420a850904941c0d449560740c6003c03099481c8040d110101c3c183e44070140300039a04d48001000c902504d003440f1642c0f00d00b074002d0003090300c0b0400c160440210f540c29121000038515044401071940e034411008105c1000300d110108514040c90580360824401c9121419a449640b100c100c8810301401030b00405000c0a20800c40e0408840c103040c00d07480b8211042ea031264041100000c036501032443d012084610303800300c0300010b442e6007413039107041446d402c491510351004c1242c4050592080c1e041d8800c04007032802030390551420a82d1080d0b940e4641c034809000c6d0700c0e400c002c04030020410948402c960020070150050400030b211078400d0000b90b4080c1d000803070309003a081304810009105c074034055060340145200711600c02d0141e84840050012010880108664045030341c4090a182c09030b030080c1400540c040c0382104020040c1159404005464014096400440d03018851780089803480e090070b2004c00a06641240d11422 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 425712068 1250 425710818 425710847
    0x60c0904022107020c0f0a06031e020403150614131a0603010312170f01030f0c0503150610210507091d06030d1d010c050319020a02030c0603070503070c03 68
    0x501504144040304044405802910103401750707080805007800f8005640403011905070400c00030942082410320a40c0070301502280003000720044016a1100c2d02640e0207984141c800408030a4071040e10303070161103801700074000103406620361080080802c507900015421210000e5950403113000e004003c65030305818240003808250340c0d68403441c00000a0780c0000303ca034001562200307000340c40c20130000c0e510b00849a514081950360301c0d540c2c45150300c83d00d6140480c0c0101144000040e6500d040245900c0005601d00c0f010b420700d064014030010024076803403682084044405a0250000c880e81120285200d200204c0c0036542c031801500c090546500c0504018a400040582c00318585113082c01794004505490755030180e641d0480748030310a1071450304507081d211180c0d10b0702e42c029158100d0031403080c802e407410110f03001004040309076118007071405600f01c0c51384841145414011f11150000071034100d0b06504203001e00514a01004090a0900a040d0b82c52030078140030342d000c84c80c03544 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 425713318 1250 425712068 425712097
    0xb0a020a020108090106120321020f0f0f0d020d14061c0201031d060c04090b03071401030c030605041109040b0603090601030314070b180d03090b06130b0d140d020a0302060c090402 79
    0x5626103070040440c60100c03c1c1600792040070302004019196402180e101034500c00301c433810516281441c1060b40c0c808080140300c2d00c030400c400035000c5039500240c1240405500d0001e4404c54840240b0401c600040c24144a032960390482503018280300344c0ca10340141c081ca030000760b4448428000c004922006040981441500104091904c09400400945034000403e02c0b80c8540f81c4207041c1d69800600803c001641442d000d01e003d94826030110b50859800c0c60007050b100e58030004201210203c084140e510301e800542c031807503800c20380a02c00480f20300341e0f0103138a1454107031180c07a16120180801001c024441707070350003100762062085e140c4482d0031510010040c18011076408940d1041d010440c1107002c0d40301c5080d0910b002e442403401c3c2e20b421025a0303803031b943d54504010302032060f240c180740e02c5941c480c020409600d40e080c017403655500c100004428000d415280c00e00e45202c064a40003150702c812811030000341d000c145650040865010700351201c3c0a000094042d002d020003019044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 425714568 1250 425713318 425713349
    0x2d060f18051c1505040819020d1b030e090118140c0409110708030f01030b010b071a0603120f0408010b0d05030a05030c09090a06030b0106031103130302150f0604060b0a020a020108090106 82
    0x82000c000a01d80d051f04645010240e0420341002e0340c480c070b01c194090021902050400500c03646188c800440c040c030034503005440d8035a2070000b0741d40c900283c0041c0e068a503e04000300b100d0380f0503c102142081c8111900006240525221020744a01e0055a6109031204180300c00d0341c89140c20785140340d41c4007a409440385030041005c1c007140401d12042d04d040605100002d0a04100c44c200c0b58407642059280b40b0b0407000f0b4030600360b00003029009a81511521a2040f111240304d0040d25800d01c24042884d66103203007110351400d58000d04d210a00c11003400c0901000920000126001900207041c442d803030342e03502c00c1a440d150041032a90750308806144104190185e00358003120650348640d03580c0c0110703600c0700400c8049038909a030000030303264200045440d401c0280c0350444120710910403113280008035800f034094034106561840b000000d100500c01d0b02e240c14054440503003446004103090a440e80802541c80e5000c580c00f9040c40b05000c00b0800c140300079003251018003844007000000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 425715818 1250 425714568 425714573
    0x702060a050d0f09080304021018030b0f09120a03050406020409020408030903070b0a0906080408070c0305031c0209010503060910230312132d060f18051c150504 71
    0x40c1c0d484200b10804442c40c0c280910300b01da00900c500030266030005121804c595480c0d003030281d0141c550300031605003d40080e02c1c840c1c44040c2c551001c040c5124181500f00e40c01c0c20a000d01c203080c40075000400303603001845c40c044403140c1c1d08140c890136106481c020990381c450741415002481150000c80704a40000340c0481d0b4038200000a103903038901901101c0c2c0f00c1d41e03030320f0b90305210340031b00d10b55840005c80300304040060030700c5280220b81050088811900c0c02c0120b5498940307094007940215420b400114022000c0390107448002c89000c0f0000c8150b2a06140800080c00d030722004103018031960031040814115101c00e0716800140c134200501c00c0300140ca40d00302540034070b41d056060307110307210740074190301400c00040a8034417103403100d20350409050400800c540c05241000d240d2008600010705250701c69543c500480040800d51515055070400d02001050140043c260281d83d001d2110704100300c1d1512640466001c1d559000b00440d020799181c00300c2d040e5200b0790310000007410035091006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 425717068 1250 425715818 425715827
    0x1e0c030c0c16140906150702010e0d111504060c030302180d0302010e12090a0e04030c080310061707080c0901020a020d0b010f050a06020615010c051507230f0c030702060a 75
    0x142d510404181c3d10340c4000c04104001c0200072507000741c00c440070040c194458a202c1c0c02801116205051000404070080d0110707944124290055030b00d0b840c4460316a5950401c4c1e17070380e9072204595410700c074a05402d004000d86102400c03c4000c01b01a030002748002d43d1080d80d40421050b8034002e150071101002070500a01800041c2039848460207102056000c0002c1901194000400a05007007500c926100203007110000040040d000d1100d40451100080c1d01c0c81c0080d441600d00001000b44242401402400501400d42c188034043c803007400d0103480c0d90072415003640324211821270741e81c400c200c8004030700704a10040c00a4201c1c4290026004115a4401315810781c1c01107480000019038540030001c082d003440c0f1541c80503030041000725550a82d0121265486d0506040c0140c0501c030640c0c1e131601e0003840c05031200b400d80c003c4040c030010640c040c014210650400020b109d8480440d60f504030503208002a1140e001c80001d0882e14058082c01a5425250001c00b12910f4a0741c52300041d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 425718318 1250 425717068 425717113
    0x220204092118140d03030605060403120917031602030c0406080705040c031811010c0803070c030f0207080c09131205130911070803102c1e0c030c0c 65
    0x100403488607a07481501d9901c82060100b25051401504400603043c424410002c2c0b921034140c04040d02c84c0b42c0071a2070b4803080024002540b01d03c01e00202209811801803207101039801007400340c1c1e003064210030544070001c29112002d141c0d04100d45449402d200080c030382030242402075006400c041c0002002d200115604089980a4800b4004026013800c11070440d9449000010021040305181c8041410303039529800c040da040c180b8029819440c1c442d5a15a00704503800c40c0062045142e44e401c142e400480342480f00658002440ea190505c1441911043c0302c442caa0f026601a42c0018124a580c940c0c400c1101d4002c20007440d1041d079044001c0003640091140c20300300802c0b090000359078405d0320604504401c1c1500040c102245582d50700419403000d48540702c409a000004140d070140389140d0107031750041400702601280b072080340808000008104451040050070001300c040100580564044107411480d0340d00d075507816402c3c0301401a00602d995621602d200c00c4803106040380c048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 425719424 1106 425718318 425718383
    0x270b130c171902031e030d1404050d09060509010e0609100203031b160807030c200a2301120605131508030322020409 52
    0x900d4820119002001d412150645161280d907081000820003480311011101c41c0c00c0c81e40010f074a8103180e100070781d8010305c1010f180b00010020320848401880e15181006a900c00d0802868540380c200d41c1100d46110f842015110036005901080485000d9903030a85841100c4004540c0200c100043d2a00024144030007017080da43c9442c0c8417a036800c00d600a40d124942031111700c850000c003198401e8010010041140c3e05000340d2201184543c2010113956104124913007200c481c2d0020001030800c80a81803a94221f03e01e80449030b25287c07080311906141511458850081c800078686c0081640025103c449154091260340c0c0d100c84d40030300001105592900030425030051001045e150a6030b40c020350078541498074444011b014501e0086041d4504650900f0840050790140724002e56203100800031036640e500000c519540c8403815036205800c001e03800400d541c008a00 = true := by decide +kernel

theorem cover : BRFrame.Cov 425539568 425719424 := by
  have h0 := BRFrame.cov_init 425539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 425539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 425539568 ≤ n) (h2 : n < 425719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
