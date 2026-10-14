-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1799
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:43:01.95299+00:00
-- url     : https://prove2.me/submissions/fbc7bd46-d9f5-4254-98ec-3dfcb05d2a3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 323381294 ≤ n < 323561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 323382544 1250 323381294 323381323
    0xa050f0c0f090c0c1014090609011b03050901020702060a35040201180302030111120a02090a050111010b09010f05030123160c140105010e101203052a030309 69
    0x500d00034030282ca601d81c010354480c075261480c82c0e603034000340c84007445c1043c2040808031032410710055030700e0382c1041c541041c0100c054031b0480d00b0340c4c0c0311009520700340e0361074002c0900c89480703003908442914400c1e00500d4005640c3c00006141082c2c1e0b80104401e03502c84220400800c00f484400c0c01203c22074501141c01040001c200e110203206650b401c981484041c1c0f004e41008101c03400c0c50122103500d1f86403002160700500800500b035094a01d02d1907504030600190381d25100c8000070308000380c180211200c8040041200503100e080400554074851040d0611003103640e81c680c422503644030b1503000ca010740312117003148060924000c101400e482c81da10814401480c2180801c00c03400b1080680d5811540907505c1c040d401c8034107001255404050720002c0c01904102c0000c5c20720703c406521075410380d030100b0110003030796a43c403005103200350350352240c5904002c580d840c64010034450006451410b003134131602603450102900207110b4425002011509030400800d01491240403c4040ea40000300c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 323383794 1250 323382544 323382559
    0xa1203090224221203030f020d1407020c060903060f190507030906060602011803050c0109021c05061e01030602130b07050c0103050109231302060a090f05090606071b080a050f0c 78
    0x61130703401d030100c144640d001000d06859030400911850b540d0140c41004a119404000d90a100c0c004906000020b603003140160058a8034560581001030803200c032110090b00620071034071010050080610020440171440240042c147e0101030a4082d007402458190fa001c04d0301c42c054105441110790b01e62194040da0700d03017090702da911082007051044190705420583e898204120000307001d0102c20340001e6001030042c0b048911842025103162085024408465459940503401f1543d020a1034120703e1141d2050010000641c203500245074004909422200d030035035424642619070400034048070260001345500c105541d041c41500e00401c01850140101810040703030203410301c40e61940150800001c1c002070340740c2a0460300300c5055035002d401340e965101c05040090010850f805040040c1a102e5000503003481c2c014070f03080c040c1c90020301841c6044400c0d52040d9405040c0810380c10400040c07940016070540c28000642c2c02d50244014000302c0380c00c0030313600c2d082000c0c00c403440d40710b000b2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 323385044 1250 323383794 323383799
    0x50f120a0b0a0e0c040c020d0c0305040f030308010f09020c030315060910120c030b0a030f020406030c1e1a0f03070c080c030a121b2601030819020a120309022422 71
    0x5d0003c2c811003c004a801c9c03e40d600c6c00f550404450390702ca15041042c8588401200000305a4007000300d81c100e81904403242951070f201c040480692042e445018581c0d0f00600119514000032000900010001084186400c85100100304403140d2002c1749408141c9060715260121214000e0b0420040d0701e280401108080800040d08942c09000140050304503c3d0303544215200c991121001c1c540104840d43d20a5941101503080b03440140d5801c06c14549403000211001c282000300c49009000c2d24030fa044c41c1d020010315070507420050441081055404121000c2219100100782044000d006155268041c0c17002401480e00111020440c510300321904024020721845081604043c2c41c4c8901c90310445224008000006a80c4591740741c04a80008100640000108070540000382d200f8500307664980c02340c2e1501c0c0342242c050406904c0307864014400b0303c640c3c40410f5480c0300400c3c10900400f90b60310700130703507a8601b2440003091800290410300f4110360180f50350000c03281101200030380d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 323386294 1250 323385044 323385047
    0x20906030a021509011808071a04030317090c040c03020c210904020c030c010213030b0c03101e0e0a09050f0f0a031d04021c06060306050f120a0b0a0e0c040c 69
    0x300711040101003c40c010070a50116032040300201c1c181e0f00007400c5448102c5d00c0d40c05041e1102075920401c148080401c04081d81104007505880881b038150700c450071001440981c4c0c000344d0400400c3c98075540038802c01c0640301d54803485035400c0d000d40d540c0c1c0141c9591449c00241e1800c00600807100b035212403507890103140902c2204507191024190707070242e250102560310b10b08d14014220411059400424000342c0c5400700c50603241180c0c0207641d0f0001a40b40e0214001ca40d1000303941d00d060b500000441401410700c0e0000804c08906101c0910361290360300c40383d4082591090302d90a4200e510703045080701744201081070145072410f59001c0c10039036864420165841e040b0000040520a4081c10103001600009141c092140090803d6580e0000f040000a103c074281200c0300c4418034024001c500340c0e1081c89240b09440001e4030100240406604000c0c584105001e446050311564074542c000a000010301401005d40790808280c0155201c5258141241001580d000d686014489280503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 323387544 1250 323386294 323386309
    0x70504211718100c0203060411010306150503070c0302100606030509060f0c0d05042102012c0a020108131704090c18090903021606020709180c050114040f0e04020906030a02 76
    0x8003040f5540000360f20380b40c1c010740c0c0014480704060f40c540113980400007400700100d10b0a50303e24003681c0030080310303850b07490714080361200c50341d900000b540a10014407010b01030708132885850b000b40121031036501041c4c88142510816000703280026110020f1110490f01048201e411040304845111549403404141c80113004400000a0039902c03480400c0500c03039406450000710824403020750342412018000781c0a402103184240d558101e603644005060a001401800c021300c4801600e15203519400440e9200c502800d83d007582410b90381440000fa860700240d8440d01001078238503403501c3c07401c4000c3c400c44814140ca1030520801c000388142c0301003081c0801d01502d032050b40c002b909480e40c3c1000c91400b4810412990100810b074004503044c0e4001032076804540e00c0c2e05052101020403d5500d4480c1141880241115490b0f48248101d40c018070381300554410403d0000c4c18240e541c0c0da8000c601442d603010b1000c1007008010300080d402c0401007183c0c015002e03801414648516030118284 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 323388794 1250 323387544 323387587
    0x180f122f090a09051e0d03050105091807081605090708010e04230d180b0940050412030b0a0326070605061c05030d050705042117 57
    0x14a10001c00101010465802014580e0700300080f594103400052191051205e6110100d01c41d1040ca5074550509129000d41030503150080d1080c803481e1100e0301c1c0c41518130100300b10080d103809568070103d030381b500800c051407500956494040d42c5929041c02c1c40030051000d010501082008401031124084200045400513801150300304a50f19140140d09c980346c3c901c0461105000d04454140e2660384202e111818000200101d000030b43c0d103680003100d9202c1d90f00b08035041080040702900c6010001c0040c01080c99050881c403900107400d00c02a187c4c0748880310105129034400a11003800340f001c90140c5a40134600f410802d01d00614002041003490740700042c5008500e03211038101551110240b10b1200880c07507002e846250900c0c0080107008220b40140c0150a5a454803140b2a19468040c9529400c400503519000510300500080c04004004030306020040200158822001107160545030b5894120302002c4054a450007001c0400d83c102c05141c541031240742c50180c1da002c0803402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 323390044 1250 323388794 323388799
    0xb09190e16031709030a031706030106034e030507081513020d06030804030b1605031506070804060519020d0e090411040504030903060b040212010303180f122f 70
    0x643c0f11002c03215112442031600d425014050b8461032130030103070040c81c0c6a24000041d2005209551100141400c0315080d11014019010440414220064031551500606500c40611204072020041c80030044150080100400c1e400007411183c0c55242c0320b0a034010b0080e284c1150710703081c01c20034540c400d4035003a88544a00924208481c03000401d41c111526a20414400d00a00703540e400c02d10384a410501c0f0945040d5500000140e842d1055204070b80140015140c0c030342152108040321001d0303001100216005102045040080f802d0400600004d0510750340d06641c0701c0707128090022004048201005561000a071074080c2d43c0c00110140f44030b103045c7c0d06001940d9407400c1100703410298420054210780782c04240030605601c80755071400e80f402014103000e000701c11800d00c4200e106019844404540314401400042d119001d040203981d0500b841ca001252182806e00c0b407071400707034081e00440da103d80141c0300f00501c1c01840f903104a03c0d001c9507042a400c1484041022030b00d4a507131807 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 323391294 1250 323390044 323390063
    0x1303030f0504230f010e0307020a0527040c0e0c04090b01020715030b03120406030213061805040905011409010c09050105030c090904081b01020d0f0b13020d0b09190e1603 75
    0x9000350303420130400810700d403968028000004600030075510f80d405518264020300c265900421541007402c1c8000c41d003200e864030341012014010840c902010f003c1d104441c0351101020010f03404403246d40791409684804500765581d0701d003020100c1100c4000c8451415074200090401c62001071320050f40350180941000f203070b400442400203040c24003003d20011041c40c0401c001c00d00741c0e03043c4e000e0010101d01002c8480580e132100410780301c10041c00841458058a40c109019904142d000030b100c0d541300d90000319180701d40b42184914420201e4410101d69500d010640400d5803080b0000c1c002d00d400c1c00c2162175400c1a41c41d8400070f200e41c1c4200e0f4091440f400204042060720001c581080c0203101400150482c8803101d80c0c080d62003440f1211840d030500104000d18403140c4103085481d8001450304840011010480000e5080303900041d240955500841743c868a45a07405449150403120224203403000c00c0132901110241608a249540102010a42005a800c200e010b6030b81045011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 323392544 1250 323391294 323391353
    0x1e170418091101050d0908030a15051f0e2d03061b18031c021b15071b080f07050907051213230c2d0d080408061303030f0504 55
    0x171006401c0b882d9008100710000010400202955400505038409408400c000f81d55540e081016260f03110031200d00716114650120b1087d805800036408018000c1d0011203040c0720301540022165804039010b801c01c00c0e050049180b03280900925034058040d480501008468280d44103290154141c000c800d007582c2c040c0c1c00a40d603420020340c206250b08000d030ba84800c0c24400000d4a5080e00381c00c20108405282440c0518a0300350344031a0035008800815040c002136881e0504c020860601c2c28440a400032804540d0100c01e01ca107941c580c00d07900c024440140760000381f08406600902d140200801886000490b007151001180c009204400350413010085040c40e0191030380890003000c10301c80601182d01b1401d004102e45065032720845156010f901200000c1c610002c03180e200140f5550508204400ca240c401004558a40240c50885c101921849620300c0d09006450350020250155122010154140034075002800804011f021a00303082d80c90418203040283c0b1010380701500c0d03a14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 323393794 1250 323392544 323392567
    0x7050d140f0f04050d030f141204061d2413020d02060309010b030105012606010602100c0201140c04030209011e06030902010507050106060f23071e17041809110105 72
    0x350b8000d13000041204c00450420301d8007601c220000c1100a0101e00c40c0c0e500f01c040a1040d40039508403185d171120982184c0d841f0b80d200d80051200d440381e50484425484041041141003009116402203109070004084028912a0307181c0780090250064118103070705a0016144c40381d03c3c43c40241c4c1665100d46039200e80d100280900111050550958030f00b0700002120a40c0300c24041c0c0d010341c550281c3d004503011028040e00d4902c2401958050381c80345410381072080e81a8407414403148a8400064400a800390300c504c02501910034445409000c103080c029440c241107124010601c601c1074810f501034500d051021000c141c410442490341d200c0640c1300796400351040711101030303000c2d00070001c4549070b11000e007102d02a035494000062b01900281d1854078402d11400c46942c0d900038940c2002e03c141e5410b8918000c00650350303c1d225880c6860400078940c904c406142c83e24201d4840d8649003000f820141c0c441c0e500c00801340c0d29050200d84808200699078409002000386813841d564200200c9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 323395044 1250 323393794 323393797
    0x10021e03040609120e100f0c0b04110a12030c0f03030902091006030e0106080a11010302040305030c07150e0f090411061c050906010321030b09040807050d140f0f 71
    0x12605401001042000300501a444501103070310600000e4015440301c00f04484200d40d1482d1150030800040701d40c80f0190240302030301c3d62141d15107400640f0741440e94540c1c9032104165000c07500d404000704000f0003450203041d00400f80600d2080c5c1c1d900890280c9000f05580e09035007001d0500070004ca400d00c10f051080e08a840d1958010700030500600307040c1044810380c20103103d8813000078035089503200c0c0c0d40c0040c0108000c07180c121006003100410740c0c80709500f0404e004216410715034200b00c0003001900c02e001804a1409840c05444828606242c900f500e1210195210400c080101c85450942d504040480480010b64403804280e03100d113000b80320890b000022030b900000c046101038404801b90802c1ca0841003503442844151540442640c0d075941c00c1c0402044006003010112844000b400940328107001841c01240040d4007401140d91088160380c141c4880400042d0103041c080200040c12000c1810720b8851628003c55114091a01a00c0c51007100c840000444a064000000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 323396294 1250 323395044 323395087
    0x605030603190506060f09010503030406030f021204030c030f0f050f16080c0d110a0c1a2203020916050301090207020a05040609021902010605010e13090b040b1005060405031002 78
    0x2150a0a000d6039403e01c40d81d02d2408403403031403055508020f02c2e11203060001070350f8102c80c1c1c003030000c504041c1064004e80c0540100200d54160316800e000c42c0414184110300e060103030b4069110b00c030401849080080003035030000e8648040c80410714602000716404801c94503d02040b400c402c0e1500c041062310758142e5000c1502074000040465030030282a000310f0b4068074a041a2502c141c5002084041503c03515600e0b400b030310303c030219101005809888002e480200041c1c20501d850008035a40f01410701541c400100707000510301a0030710441c05c01280542d0401c01c0302146a1103a450800001c00703074801402203004042d004162582152503200c010805070000510a01902e511207104500a4008410840d800b0415106485c6094018410302003903510603507822403a01013120610903800e0301500b4191925a6402810340468003e0740e807280254402c840c804441d00305461400310f010794581040344501010482000345a90001e59072115602d400310140c1c5506c50402c4160000b140203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 323397544 1250 323396294 323396323
    0x2d0b09030909040606090614030703082a0a2a03080a0c150c030b0109080d0311040803070b0a0c020f1903032a0201060b03010e24030d080103020306070f090605030603 73
    0x1009000820405400c5170090300c80c1e42c2030410030b4503542c0448040c1000c90400554058010b61000c0c00820200d00c001d1170008000ea9251103503000011880c101c5901d04002c48000d0b400c00c40f00c810030403803804104210940307003e10b0308100c800040b01b9004041c000c0c2c400180f40d90400a02903007250300a007a03806480d40c10002c040d071340340400c00d480400391086891440c0000d161003110301c800c0d13004100364015100c03050020200c48481c2ea000350000d0081d03549601400d0310902002070782840801c001c100703041c0314041c3d070030b001d051411101c81913a5904103104199040089041c90181000400c2d641d600c5499602ea4600d1205081c141c0c000c102c440e50f04150140202403581c1c1c40c0304401106011080941c1c020017a00c0d46e90900304031503020a000b2000c540041102185000368408205010034803051a01000250500000303807401c000150624003007001d500040040d0f02c2d040c403980350310140600b00210800c040c0203000b881c0c4002c074000d900600c00d020010861585003007000d045094401d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 323398794 1250 323397544 323397559
    0x6060509180601030b0429030607120906110301060203180301020918040c0e010e091b0d03050a090915030c0e040b060d06060f0608090c0406060203043c032d0b090309 73
    0x60a1010684007c0301200380a80c20035821030025070800141c1d9610803210743c1d80302d0300c0412001304541e01034903240705d0588070961524017008071207001000560007855150010f540e11502012241c45c24050541214481e074414031500c9810784132103040382c00210300d40b8003494040c1c3e51031a0070560001950840d1051045401c0007207068050991054018003915040310240b8490010299081061aa0f104e0304080b0003014500000d020344003605c0c500c0200e083ca11402521503025204661000d0380101d0807403000780003002400000c64040020704181c1c0240909890240c40f21103200d103000d0700d440c0c0900c072800c80300300c10700500d0b80c020750103000e130049040300306595a03038014035814040d50041038034082e0142c1e1514074039262140c0f50884042e90043c5080a00c0e0000d1f0403600183c10703115034000100700780001a0300403c01030b01280003030040c0d182c590031400c5050810103561152840c0c125a01c50103a20038188042621400a01d035000d90603078203d643d498910784c1180201c003400ca801c40c1d40c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 323400044 1250 323398794 323398811
    0x2060d0204030b041a0403020705012f100f0b0607081309060b09091302010e060f0d090609050606030d05040b0f0903010f0506100c03080a020903011d0c0406060509180601030b04 78
    0x24036140c3c00e0003140a860441c442c110091460107682e0b40940700240580c5c0206402c0100d0b5005410b10500c03520480c2031100c00760340161403582c5018040c4058030041d00045504042d8401a00c5008519022104100121402800032031228819005c024010500100da0f6901f03c2a40d191010090a080c100501c81d80d60f6031076814032250492201139102d080500b0004040c05807800c0040c04207a016540d0348040710681c020b210303460303210300510300d00a18104061492483d0314002c0014283c860100000e0350700882c10b04e01d05011380600124480e80140c000d08501c03070352107010750381501c3c1641105c542d6049069092900c6110b20b4407116050350a0271080480c0700040c0d4800c0f4400c60050300d00c080301b4000350108039504620054001d0108034842d0102e120703103095602920600c0406000003824040041001c074540071499180b4040b50300002c0181e542d41401c1c001c00e001017415042483c20001c4070710000c0c06000140c2041c03290f400005000482c940e2094005a0b050300c4064000c008400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 323401294 1250 323400044 323400053
    0x2070303082202150d060509090c090402130903110105071407030f0c0b07081005060c030d1503171c0501030f030e03070b1603021207020a030f1a150909120a03020702060d020403 78
    0x40040c0407101305c07030b0310f0060006038a081110050344101c8502c2c000d8500c51403100e08004428202070801c1c1d0b0803a550090480c002c280b10312a05154600076156800c2d130340a840d01c00341c00d5a100038010130030400e08502c0001510307401001d88291135850b007080e00002000d28421595030348200f01c0600b20307558442c20721881540098a05000c1c00304617207403281d02c1341c40b802030240f184615501409a90b10420400c0a074940550100e01c101421550f00d0000a40d44d46661035850340446040c8113644000540d40402c10142200810740001542d00b8000d40d8516114070001500520300074040c80304000002901355400c3c441c00c0098414150019142e10401070a90301c2a04200d0048015215000042041c3c0760724809072181581c0c01002c3c2c980040c00c50f61004815038200d5811140b00800c0070031000c41400c05041148035407078044880b00301103101c0c010821039840103000401580c010182d010000304200c0201c40030010035043c05a07483d90a031010404a100c2c10f5012000148085000310801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 323402544 1250 323401294 323401297
    0x115030227100206091f0b0907030c09290706020910030f0c02030f03010b070c0b0a080402041802130c05090406031104050f100510050f0310030b070207030308220215 73
    0x1500a032404005402c16080c141d0342c2e0502510344891030790284015109640015240899010340460081610a016804102c8068055421078046500c400151a4103a813043d4214000c105c1d400611418040001c601c0070407800100881c417031a00001604400d01c07400e501100c441501c05000000f8207030342500b005008004030590061400e04100303034085000e1000090710f00305031201c0c0107549164a401d00e08a980e42c0301410490706110910300c00141c000d4610b0140c0700b22201500c1c1c4031030a1506104000880d81e21600016182c101b0300b0400f0056203da00401012070841d440010341c50030003c009a60500404400c194014103081012080200d404181103005c1c4080d0380c18400d40d16907564030280e1030030485485074001514a0b04001034501601c0c0340314811b0140c01d1151929100d118001e10a6000312000660340101c44010020050300c2d00750b0359882182c44c80036084403401d5550041c0a440042c04001040044083e02602c80200314081e10031241d005100b085080d0048108820380d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 323403794 1250 323402544 323402617
    0x717090105220e011a0f0c070f1202030d090806070e031c0c05060903041d04060605041107030905011103092407140d1d100c0605010f2301020601150302 67
    0x660740f0310300002103042d0000000d0901440d07101c009410310010481118590300920040c880c280f148010002d04016038501e060054100203142c0990380b0a01e0040c1454080010703913000030412140010030410b8800305000390000c41c98585140c0315259500068030700102c03c0240402c4034507055101d150103401c0700d08801054450000d440c0e403a5641c500042c2c490040d88a4000010319241301480c2c45092110304550051050000003601074403080480d041722420400d07400d4014000617244140b42c0c102c840140200300c240380c000c942a1a5110305a02c3e400782d9003246006d020f510a0b1b500c540200a03074400c0c0010b0000c40140e8450b09141444205021103000481e014010440340189292081e4110f403001c030320314103400c40c9140511090008c24a146019881009411451200004e0540c09868001c00850501c01c8000d41403542c105149140e080d1440f900075600385a41085980128080741150704081245110103101001074010f84103020003440d0300d9070401002d5a0409511034184607 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 323405044 1250 323403794 323403809
    0x20d05011b110c0906010e010c03091212030f06030213020d06090c0201020a18060206160203130e01090b19090e0f0312010315020703020c130b0301020c01060501030b0303071709010522 81
    0x20403107521084c003021030029181c950000c1c05e0b0320002c0d0210b5006030380f1003820522078600803c4142d43da801c0d07a000c07444594030072036003440f80300c55101066505004404002c010842c0401a0340d145500240880c00c0885c480c4c2c0b80070f030300802c1c020b0798442c0c640e1040780284244541070161418814000303000b98469030700b16012442c40a180106500c3d130b11074030b5059030000d4001381400c0d1503240101001c803c1d942d01000842c4170420948003070302540ca02250042111070548422541881d00c4401941c58520b5018094020320714860301150708e09140c08122200e8000c002015015030204030305041c06262070141504c40041d01040032018102224100d0340070f0740700500e5011003946680d003a4898120f0190041c3c0c4003d411002c0c61030024464003542110b11300001b1740104180100c0d0aa27008030f041d620190350740e0f0400301310558060003001843c8100314065842e2030340984d50f96482e6804084d001e209054089111501079008400f1074980f080441031a4400e00ca07a600e020740c059040d8014100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 323406294 1250 323405044 323405053
    0x3141204170706080714070c1805100603020f070209041e080c0c0409050a020415080106030b0114010c080a051c05040f140f340816050a0e04020d05011b11 68
    0x92010b100c4d0f80f02e50702920306903984180e130060513184402c46400c100c4081c3d6910202d84800958541d090b03400d008000c8034040c0106180c40c0c8084140e0f0800c260f640001d05040c010850030a0a0005400326400e0690403030b1680003030385030350030141c1c0c1802001e4181c988a0381002010703400d00000d18045e00303a14458a044070119406641030205480301500001c0c42ca520260740030005240913080303001d9031821903a8101340b043d95031340c0250075a805684140d40c2e49036003600520400008000080102c4c03428217000341e17006403035039900540d4858510160708000740130500030a80000c00c195420360010050741404503041c28101000c6819140034129091115004200c891840120f03a000c1003200100180034424503822508128003801860005001103105240e106042c0c00e130104405400004001c245034081c0713007050b948c000159004144507001e000b404020500c1081081caa02c6035055507440c240e00701501e02036016007040c0705040c1c071440e5040c4159100c030b5031141c1000000003e500899 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 323407544 1250 323406294 323406299
    0x105010f0302150304051c0518060403080301180f020a0323010b03011a0c0703061418030307031a0a06050a12090804150504150503040308090c0a031412041707 70
    0x241580000d9201c0203402907092291040c0e50503e42c0003441d0310a00810a0781c2d50342e402860762540300c5d90080311400101e0f8021580040c02105202000d280c4e07201907e050b840c260854685010754001445900352203031800309070750820740164002c045c00d034240340000c0d919508040030207006000e0711483d1a0380e00c0d000002d040c00002a0000c0141202c502c9a10350b4075503403c1001103c4141c49184c01d2148040c001c11405500160030030004000354041c450008010301d000d698102e603220b002d000d0b00c5907140001004008030030040201d0340c2161650600042c4884105014854000d03102038040d0301c800d501d00c0029000d40c2100050a1f0700d851030740d4041070724280c004050700320303014600043c000700d0b8103010500c035090301c209003680010114203116003040e99400130046400030200078070002a0010050200701500402e0349500000584003801c10b180800000c12201030040c48041c0c121400a68103100c0e02a05118101c15600b102c14400c3c0d0f9183c41e0030300c05014982199141160b8030a04200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 323408794 1250 323407544 323407559
    0x30c05031015020309120d02062d1801140702061f090b1507151a1c081b010504051207020a060503040611071103060f061c0c080601030f05010501 64
    0x1280d104110041441e10000d090500401129001e488418154441003200030103941c1d03030365084040c1910074001003000b01718140d4000e04041c4082e10440300482d00050400c0550122811136021988041d1924440e0b610750074040d4210710028410407642d442c0c04000100c0c0b034009000070f403090006808494040e11181c1d40c032950400d22134004e819400c4050020710401151360041801c0f000300074081d04900894240030086030744070003c22901101b403c42340701c4124446008194004140d01400403150030600007080002042c00545c6181ca038441ca000340802020101b1740d01480c1c40d52810f05110035a02c0f41c814000c06081e00c0c207071490f22920300540c800e81103550443e140b2aa000d845150000c0c500b500c1501d540c1c0002e00100da520340c0b030f41c42d203031503d0700b80c0300242c11168082c0f4103400d41e00d05c0c00310501d814040d000d40142c00e090f281a04114180c1c5a40c03044000003d10340e050900401c2c5a410010042c83d49500060803d0103140c0000040c03294108010058501a038000c000c603907a1000d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 323410044 1250 323408794 323408797
    0x30908060c040b030c040b0a020a0515100504180c06020706080f0103121d2d03070807150c0c03050706120c1e020f0a0b01150e0f040203131a07030c05 66
    0x4500840c0c400411083c00180c0181d400307542c000c0320030184e080c10aa06c0c0d00c0440459040640c0303501c0140d0001000c103080c00b008011403140c6580401c124061030401410703008203c812805003078001c43d00c2d4941d0f0b84030b11114103440669644c0083d04908031703179228100291a406248640750026400c04045181445d40c2e84c4194100c03a84400446280802950b0503190000ca80e070903500301180100d40790304261691800b030124a1210306444240c3c041494102c0c0d00050808103140c02548015000d000f4240002228015280003140c01d45441d115120101c0300342c498194000c106894072a40003080000000388041520708944482010f07100002407001165060002100010442648800301000500c20a16140282e105a4026070001840c940c41c1c86076070242140c3d0211000010000004c141c1d681100202c907601e85558422160380c001102110040d0080f40b15503400800700310301c2000b650641c1d00081d444040084640d1000c81c1030024524116808804203043c0300703600401c18807800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 323411294 1250 323410044 323410051
    0x150e010513050103200c0304061b120e04020d0e070905060306070e0f0d0818150a091e0e071d0d0210080c1b010912030920130203040f03090806 63
    0x1070039206150100440160000a410121115900040b03aa05545c601c00905002175804c00659980d132510800070301000c10b07001c40c0121407604c2c208000019034010007141c150652807070490450500c69001a000b84507101180f200c10707213445c0544003040000f0501e00c00f1a082a03000708281d58501c000d05842d140111092400201c10b2441c40c071403072402150720480828090040040101c40d6510f000082c2d000200c00c01030050760a000030440d24224000c0e00c0e00b141c484003094104201d0017000303000c40b02d080c055000e02d0a100c22b600721800e03100580c148000d2607208143c004508001001405500e00d104940b1098200c00c9510011820a1080342074851340c050040300402c080c0b01c000311417803d030262081c1d1034490204100309903113001480c415150040800009042e51052424070702c40801c03080c1d080c0905081c00b40050124203107041c1d0070041c0800d04200aa0101d0100004001c60801c022a640c40d40c0301005010500612b4940b10303451910a40310290603540b6025a1a502c50044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 323412544 1250 323411294 323411317
    0x31204050d08160b040605251b1a1009110a0507030f030e121308150402010c061506090806152d060408161505161506150e0105 56
    0x900a150000702c607400205128005100054400b050f01c0c2d0700d03050028804d84043d0752180d02c1e00c1c280a04c0c00c2c0000c401c50f1507401000c080078010191f40d40c2c0900071601e40000031010002441929042c46401c10200003424402c1d96429801c4c640305243c03948034661406401c904501e845400d17824240b00b8000c6a00c035168940311117047c081d43c2e650865110b00d8103180c100070151aa03407a0629240100320350307a101035a601c0726a0305c5041d087d03024116803a55500605050b8028011200b0711b05800700c0315500a5028601380801c41030382d04021001d04030008041504624101000526643c00311210701a2100c2105866940d100c010301d1a150317408c4185e03541e134000c3c8608201c80300c038006460020345403c1c0141006e00b000011100081d0242c0103a0302840d55600a03c3c0d940c4100e401748004d004c0505965012a414010301510040c4940655500c03c541d8280009260301445007442041045d169514810302c02d41e92207a141e6003040131fa6080c0440030501008003004907600035000c0d1200105003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 323413794 1250 323412544 323412559
    0x6020106380919090524100e010203040305070e01150c0512030603070503120d0c0807020307081b060a0f1104030201140708040803030907060207050a080303310c0503120405 76
    0x604402901d0307101c02d90040d40311984001d0100e0201c031404141000701641840091186007442000071504040c1c008218060003644040d1120b507140d030411040040e082c034040780d441e1540f90050f4034510072600060104d200e4400c0c00540020401e07945030503200e400082000c00080e40b80305076690300c2e10b030b50010700540154408080300400003000d154030100040880f0340c03444d510b1000c00d0401e009602d034a00b50342d0002a071082038914030f00614001a600386014203891409400094a80c02842c030000c02107070000588280c52121021118000450101500c0d51401c294080350014014080074018603410008080f030303030105100c141c034201c94041c0c60722540900c0c1d074001708909520414007161102e4051001158080080002d10320500e2001c0003058203604111000c1c1c0382080300d6004030b00c10400c8040601100e00c01000b50785d0082400001e6030600b8669040d100721020f0210b1800c00281c882c1c1c0341480511544801d0201216015825900200500d0700c1d04034680c4150301401b82c20404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 323415044 1250 323413794 323413889
    0xb010e0907050d0509100612110a06050d05070302130b03061021020705011401030813092003060d080c031216020a020121140403030b010c1e02060f0406020106 70
    0x49540055038007170308031003c0c3c980c2a110400c160b0122065600284606e80080c1007150400504040791006004200d0348500210b240c14401411032003201c94100700c0d82c1d202c0c0041520240290181e42c0e2000006203100019a1140e030030b003000746c1084488a01c1042d046030b41c00180c07070142101c1c14a024500d8505800a400e501848001c0e51000104440c1176589182d101411002c2c0250345000e10b114103485607541007020140082c891407038014804080ca0032030b00580060440800d4020516001d43c038a0b20396440d40005141404403d5002c1c19088000400b5240341c0d1021000f00f00610119100400b035884083c500d100c1c4000a24001c00564000070b01d240c003540c00390f4a130003d5140d80e0101e40b512401c480034aa025605d181100308251407d0f4030030301082603054019110880b4003072a0200c019102c039200e100e00f450302c004a1244d0703075a500c00542c05540701c440c01c8031100c400c092034841e9115520f040c028000c01c114450081e1005101000c242c8450011105205031424481e50a003040c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 323416294 1250 323415044 323415067
    0xc030b091b0f0a0f02100c05090d1511090a0e060a05240c0a12020102120a0506010201020408010e0a05070f0f0902250609020a0b120c0f1303060b010e090705 69
    0x19403400c640800809201e0a800c000c0408020f1105844982c1c3e1003a02101c01d0380701a03e00040034000c0031600c0c5c10000a1842c007584003050b5002c3e00800c81e0305603030301c180a0400c210f07242d91580d0580410b9003003907003800c4002079a0004206009068600f20012661103c003807410303003000c1d1001940410101410810383c5064420001058110605181c81c140407401c06802680007800050b00d5802c446c500e0024080014007007844207401d400250b141c01400c0c070ba03038044484010541c601583d0b0321004241c0c0ca9100350f068801400c0f0250003004660b46081400c0d641d101140011945e52054980100d5407411004507181290005210204090308022a0300003a41201e009500c03812070f060013000314204400c00c608400c42c007418000901e82100e00521150311142d41000300551010000086e07281074440708a540040f006102c591240e00100f800b09080c410000c200040000d003080c08018403680b0f40c42503400e80002d0701c0f81314014000400b4805443d00444501003c00c005005078030110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 323417544 1250 323416294 323416321
    0x90f03070809041b020708010c1b022b030903021f080c09030a0b0406020717030c040306050a090f1b09110415090b0a020c030c06070b04081c0903030209040c030b09 72
    0x18100200042900e0502c620101d0100344c020b054000180d020003c104050b00f401e100300381d241074192401d508110300f01d07140d10011412040000307000740d85410242601410b91500c4254900703100740d1040380f008150800800c061480d00050348603814407040d2806031b0303150380f01d007405560700c076101c6040d61740d1040703100d8441e608104081c075023500074410b10400003030100520500c40e9110301130042e10340481d804c2200d101207080c850b20350164000c02c240002070201405650031240c0c0803802182558611141001808100706d0041c03064481003130103002c01905035521550307820204404649a5650240f900580c1d400d0224440e01c0b100420080c00301c0b0100030a4010f4103030480c03d100e203900e41c0d10300c201407265000040c1c890068028000d5401d80e440e0901940070b00207000c85d10141002050703254040d001d10042e00003031083ca0300149010582e0b0b0788610300031034111001c0c402c006203020780c20080c011790b00440c2c0b011f01c07a07850046200310180c006e02c110000c0001c0640103805550702c0799050720701da = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 323418794 1250 323417544 323417557
    0x6010314031207031b030c141b1605011701050d0b28050702010e150a0c020a060606020307300807020c03101515020c19050907080f090f030708 63
    0x164001040342d00210150307080a0390242c00d9550b80054070740c0424003880c010300030100c450b104250400222400265100442011003620400c211380d44414105400c0343c2031503a140003120b20b00601e4000b40e90f0303003813035402102211001c0c0c0300c0301e0b05000350064403002000709004ea60707808001d07980c441e00440c481c4100143e20900f0248080c0c1c1c1d03101140350104042c0403a201c00310f000707074980c0f007004545076080c0039190400004000408a800c00c20460024900d4010440b41a003541d9032000340c0c080b842004003464054010000700686911010029100e510110040e40e02401444918042c400e010000044414800c850000c03001071451046030b004101600c0d150851040c41c5403031100d542e05000909680746010000203d400d00c0c540c1000500c00160720130210881c0203004a0001500422115046030044808684c1d00032001004850001c841d00720325000764100040080f4160486141c03401104112113401c010b40d00c031000a42d484184030202121904140a40b000044400b80581079 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 323420044 1250 323418794 323418833
    0xa0b04020c16030203010608030903100f06031403030703050c0702030d110c12100c030b010203031302030a12110c040c0f080c0d020c060117061308030405070f0b07050f0d02060103 79
    0x15007200c0202031464440a0606401c2103400c01c0020002c501e800d11900b00200850000345003000310500c000398582140c2d0082000c004c0e11002c41003c030720010350201000d194400b2410308901c402ca441c05949400c2145e1003004640307014081904292020181c1d51484e600078028000306580c80385c21078501128880f61011407080d145003401e02e40d11250443d2200c0128002403141030728556000b02030301d41c5e000a05007410b10b4030300314403516640030085a0307101d02d1303a5840d801c00c1c030034610100707103800000c0a0203030401c40140d0054100715844a2001c404000410031140d000c880301007003100311070740c0c102c000b000f041d9044404c4c00307800d010302c910075807007802186801e00741034103149014242e07400f0f0708800d11950070101c014070082c40d030380303070322380207200000c0011710491400811088a60b00460320140c00c2200110006080003c00c100a801900e05000580080c80c0d68182d40029600001d00480c1d16000700205544420000180c640000180750b0003480142d203103880c2c0c40c00388908503a5009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 323421294 1250 323420044 323420047
    0x40c03032601060e010e040c0c0f1a0f0609180303161b08030103021008040c030b04021309030305060a05181503070b040f0504050112200a1d0406050108070b030a0b0402 74
    0x7840a0349001000380201200c1d20380350241c007400d07000105103401c048002031103186400c920060300c0b0791000c1704451141d0b00030045100100507091019010104c035070050703180441c080030824405103d110b801c4c010b02c0f041c0d8180307030301352100c07405000b141003004280011980184009a0000156a6102400001d504228600110700050130540c0c8a050005076038443c0c1c000010811800c240c4061071011803149409183c0e800e00d5a50310819001a00c8080c2201c041403011606550b04c0c030741c01c1224205107080410050400f40b81c0500604011140d0344c4c4030f000b1250740080c0320b0a010060390520719001005a5039a500c05e06400ca4a43d0050b00b5940c0612030b011011464443d180b008001030010104801d880620340420041aa001600020b40f0030304d01c014640002900d90283e165610b80d03400b0780c6501a5440c4020840125161780652840200014407031950501c0c19086800b43e070081d030060041d80c0e200c9404a54031a81c80c410389500c403008000141024015a001d038184890060016 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 323422544 1250 323421294 323421347
    0x702090613091b140102030c0d080c12240d0503030f070c080d05010e0a0908071709030d03060306140610111609050702010e0c0a06080a0b100c0614040c0303 69
    0x40b071041c3d055a04900c11460712005022441c0b103a2102e0031840c009100071460003128181c4d19864402e00001641030140c1c1c58089550312202800341c802c0401c01d000c0c00c0840349015050140040211a94840c0200d8030742ca800e00d01e030801001c1d881c4650340000c02180f0f503442d001e11400500e00d0040c0f5450411200c0040172001500f1440180540c007208000841c043d410002c04640449001c1e01d0a03082c64034100100b000502220196021150000307881075401c0032a4242800360b1140109007941806110140d0301324981560000d01500c4c0154000c12070442e41c5210300345031240980720654001008030500303061611454082203806030590a40301c80c40610414015603905c3c54102d0b0030182d840b08104404140d09104400003001d103100107020403008800884e0b0009a9806a1001c02c540700e00003441d04071300c82d003005000605c050900c85e440710545000a0824510784030031a0f41c28180701b000d00c400c223443c1c80303800e000e1500b20142d11110351440d46c0540c0d0102080110400042040004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 323423794 1250 323422544 323422553
    0xe060709121707030203070b10240905061b0c0a0302032e0614030c040c0509010e010203071505070908060609150409061d070f15031d030a090e0903070209061309 71
    0x2c0c0c5460f900c01d0b00116144c680c0ca26140301c042c032000384250a1500d90340001c0028501c01e9000e00180c20592700025251055034a0881b02800300fa0041d82d0400800280d00340000c44980188844030620b00550b810070311414100184040103200103075250340300808421880f160441c1c040508140c103031034100f480180d4502d0300b00381c42081e800b950007020380e585c11500c0e0341404d12507659550400c8030b04000d4400d0030348024241303004140d50355040080400510070b541e4004c000320b0300d08540103003c600300c04050030204030141104a8800c8000784408500040031007000032102d0084000a09003803142d62400a42000040c5402e02c01d0341c03281d166115400824060300c034600e070398100e40481c0e80040344000201031500c59180d0113440200c403a02d404002e42a0002d030884920030746031402080c5024580c0440d400700042c4284101d19000014081300705a07000f218590032101c8c0800c56020716a16040416202c0c00742800180d04007100400080203850404110000a000701c4800500c250850b100c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 323425044 1250 323423794 323423797
    0x6040b37052b0f0507060f1806030b0d0c0e0601021204030f0609060b04021b0d050a1d040608030d020406020d090b0d0915020708070501051503030d091718040e0607091217 75
    0x2000d982c4c6410800f07080c0000c0360312100311500c1c803c4a04010200340e80045445203c000719214410400da0381d9628103500751346004c03803d1a007070b80010410141035221081010045420782d00c140c054030811401800c549120000c0da011260001412000070000e42c64410103170045010440340d095031070038078001550719072000d450030100d89090043d80401c0c04802130314180c0e904035044c060000500c03036200210307400100c1008280c9204401d0000304070100124024007004d81110310680030201d0742c11202d500b142e01400458819900b10b03400c01e95120000d0300e06d1001401600c00c80c260070085240d01c0a8640c0043d090148200038500b100c060200c00c0d82d00726004544110340940700062084244202401840c0d0031600b209545072110b008000040d41e248503650341c810317049480d41400024400412403172501c00b0f42e9110342c5551030041072071640b40c0054440c04203110314a440894000c0300000100f15204060036116802024241300c0e40c0c0e0240003d2000071126a407e1001c5105088034440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 323426294 1250 323425044 323425073
    0x8030a2a031401090e030d09080d0204080a0b071e0c02030a05030313020906041b18050a030308010501020d030507091215060e0906130b070806040b37052b 68
    0x9a0004040070001070b074495140c0181c1c0442c41d81030400080142c603a001104039140f10242002c0001ca02009141000c61805856407400c002c0c0d1010a000030418800b04007281ca0781d01c50b0600b04907a41c0c2d00e0405803244040412848600ca040708a0b0b120000c0c083c00b04401c00500040440784900c0003691510b281d944101da010bc0720203000311380d910450600728600d03038101e2405c45040c07100c02c1e03240e40c3c0030b0a8581e0079080c2c0000c004c00d0103485001c0c4035418480340c029103006030070659181d03242e04016140d01c40030b01c505030052060028000f41d0340c1c802d1003028018442941d030020050b20f402c4800000d2a6030000170307140414031000569568a1a201c0c640080030801036601903481c0c20150f0074140740000304030f114210201040c4e800091800042c882c6d000320213081032055a150800803500415105002c0d039045110081a00b0040e4010400407079915801c1c1c80140d03141d60010400c10540c2c0c4640705032908270741e107180303135001a02e00108012042801c45481b81d00300e200303a803600d0703100c0c84400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 323427544 1250 323426294 323426297
    0x2030904061502010c050708030c030717150f0103230613050f04121107060c0602091c02120a2103021e1215090a0c02010209060a17010806010308030a2a 67
    0xa84002c490103070203000321214000d040c203240341008890780310b00c0a1880010000044c0071400000940914019034103980c1e03a5100d60900102454483c9000b8002c1c0703164a001c0e889501c1d515031540240d1b100e402000805e125a40305848191244140289140c03009040c1990007000c400c0c01c800884035910555204083c415164036040c1032a00f004590100d90002090030094880710010740030300001080d0302140d03403130724026620081506081c0000d01440001d03603409516114608440c13010082c13204c079894000c442c00501140031050036540d401d040c21300100340a5000480d411401110003841e07000024506000d0320741851f101580402540080c0d580d1088200494000081c4600e074001d558080340401007220144020b034001070036074100070090445540c452a403400b429200390180c031041c402c061704050315084c809002034544500e80801c01859100e000002801c4040040d269048a411504240c0f550712043c3c10140070344000c902c9244020301802c4203451506140c420280d144205 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 323428794 1250 323427544 323427569
    0x10216030207170304060503010e0901021b01020a03060f21050304050a0e040b070201060b040b09030a0c090603051002040b0a12060b0a0906200c01030207020f06030f06030706031116030203090406 86
    0xc00c4401000610740000319412548180000c0c0001500003085905440041c690700ac6a690740700e0b101400392003001c9941825401d0040088440a015006040341607100c1d1400d00c146600c543c40c0c126409a54860080c000c003c01034100c0d403c0c15081c614a110305d000b03030140c3e80b030543c54101041d0403504513070106c84c0c207000e14010001441085039115400502d14030080c00510b10304841e10b001c0e4055030003910b01440c8002007006146d6000c20210400c207a1042000780d0303030f40d6a500f4000060080d80b0054401340a0f1110b8140b009034107100320b6007030ba03445280070360500b1800c8408031801c80004480302043e036514032000c140080940c010f0040036120742d581d00d458600f0903030001c0c404402015001f881800580900f80000c0012800001d100cc0070720300141c403890b0314000505d080e1b9000c0511a0091b00c00000c0c01020000a03110502c10344042c0d08a03002e90380d0701d880440842c2d182c0115040d20740818060414040c0c00b442d84110640d0092040300c1c10124117a0000342101c08036486010f0181d003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 323430044 1250 323428794 323428799
    0x1140301080a05061f031112060a150602011104211e022e080a021309090c050105120f071e09140f030703060c11030c0304090501170d08040203010216030207 69
    0x1040116800520090581706010046a00314155412404000c3c00090802d521031000c0e03d82a44030240c1d1681c050885440303060920348400241001103401c00b4090702e5800101d80e240c014002c020139404001e18580c60a8640f03051026480006080c1c2c800d0004800c60046c046000445150303e6165a030401102c222071920400080d4201920b404003040e00410481d1070312085a8003a1252046138180003005641740344440b03000784101283d12400242690021401b0002d641c001c0c1d0b0104e00c10036169103095101d4006480340d000310340100100542c0000022140340d080c0041680108940c2400c0300c10050080444200100e92116000003c4502c04104031804071002e034401624015500706034103140d05c6c40425214261808044e003020344030b92420390120b2040e00d4854010500c0019a916000c0d507102040e204d902c01d02c0794510050a00c4c00104400a0307014030b12000c0c5500d1002000100d0361444141d030110b400034400e0364155424400c9022003c445241c0340c0c001031103903010704420350 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 323431294 1250 323430044 323430053
    0x305100f061a070201080406061205030c0d08010807062102031509010b03010b09040b180c03100803040609090c02120313020103061208070f0809041a01030c0c2001140301080a 77
    0x42407588074030001e90310b03498140b42c011460380894001d01e0702071174103514540d61420034401a00c9550700402808000340c80403000d00c00003001504802082030180c5064404250044500a01c2800b94640e15044060100040e6010741805010501c01b145007002c00940505680201e03007040f6021000850346407882101454000c801034050100b0118050455060103510805800b03281a10790103603680711680742c83c42d510502050031588048490034054076284140c00034582064405141400c5400d03400b040101c80401a9416a00b103559210141850186000702420362014a0000d5018400540d0b5140c06210000c6102d0f11824440f07480210451000500311142d5500c07462240800c1001c0000080200003152407142d000310f003007901d444041c103011265128101189501624001108480e40c1d0014030b10386401c80241c03810051300440030002c1d610f251607440e00405c0440752040280000d0148000400500d0041c908000300907040c8801e0905544203070400991a88858500e40800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 323432544 1250 323431294 323431301
    0xf11160b0304050f100b1906090b070204020706110c150426090406030302030c19080301030f0201091503060603051503150c040306020c0616111f090515010f1505030115090305100f 79
    0x208005038a0101d07d850000010161055030294203030644000503038100b5076071a03806680c43c0c02d410040401c0058620551110395078060140242c0a002e0301c0c0c030140d04c031a404029284144d80260341c3c1075080e1801c08410048040741c01c0c0f80740780c461060000155907241e5100d04009076200360015643c1e100b414088a2030305c038119404c070740207003684501075000900b80001e9a044950040c0e100c0103416135480103a4142465030002da16103161062400310041e4103421040171248603440c00c0149881368090400d03640450f481c01d0390127500c80c4103816440018075550340d600c010103420f80c504050302c81d51000c05030390100301030790300f41e43c891014046004003155660301d003800a42002c00e00c54480340700d0991a05a4004103100e0810001e106403c181d400384c101d160300c5035004054461038125040c4883c0d101c102070003600d0544c410302e90080360f152400d5074000c2c0505020345529045030310b04942d178100404104a10b504000c0e488500000050080000380600c2846501c081901c000440c000c8044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 323433794 1250 323432544 323432569
    0x80a0f150c0207090f0207080a030504060c050a1b2108010f080a02031e030424030c030203060607110f030a0b01060201201c0e06070f11160b0304050f100b 68
    0x101854007000002058001942208a0b003841d4004101c0160309000000240140c01c00501407100002c0c081b0300f10341d49980018441c41c81448100f018001010b400c075882c2c003803008200d001c214904140044240f01000941919115800720102e48407080c42d00320f40d00b40d00040100200b003c020044c454803801501d42805490a0b0005119110302ca1700007a9030b0b5403405070302a00040303402d140464081014400c40c0c0c0a002c14071300c0d03291a8852074141d007207040b1031a080385001034640110b040d05584079008490090000806445c1440002d0721032451103820041079581c4140c92200e202c009440034844180214010302c1d59129561410002900b900d610b072010040714102d08103070003140c034000e8040d42c413141001108a00905040c500103c024407812120030001c0c8140c00030072811035171140c0380c00c0c4101c0060355058201d0410300714450b61a41580190510402c0c8080c06120890f480c6001d941c0c040d00407000c0341c01c5241080d44440c101003d00c1d4a00b20b0180c2c8820390003010b410441c40030540c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 323435044 1250 323433794 323433833
    0x180e0d0e1212040b0715090305040510030506060d0b18070807171e0718030b0a0b1509090c07140d3c14030108072c06010c020a080a0f 59
    0x2952802c560300481031149000c0d020603004040354040a000c00000c80040f490b40080082040792501d04000e4519081445001e02c600c42892140308c081d40700303000c0e1500821014001c21300340303a08441400040e0282502180d004441e009403030700400d40300743e20b0741c1c00341100d516411114104100010117011145203461b02400070101800802c600318a54003003819103820f040746032b40d240c44008032a03102840075000003c0c8184034012060012228405000c1c45003008100901d51594050040c4503215110844402005000031a21401d00a140035803080010010038600b080e00e42e1081d045070820901e004a0780e0010a400c02c4203600b115400c1d00751225511104400c44541c40000d40d02c804200403060b0611002c450790820300e01070308042600750a4000c941d0340703030342c0c56181e850380d070f0031240c030620030000500801491003034082003a50041d041d200300c407805250b032810300649414041e20000c03a00400106000100080244004e0b00c4203442200340308440c20701420400203c41260030b041c84c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 323436294 1250 323435044 323435053
    0x1e02130605190804020f12010c0306050307060e151c05040203060606070b0403030903052109010c0302072f04060909060c020d0e0d060221040624180e0d0e12 69
    0x30041c20300521900d11010b05842c0003103290303a0b6880400e0b550721400e580aa0040200c002074110144190450030225010703030750070000ba580d5a400c06540ba0407a10400c4049004402c5107211070038850714403603008100c800424500ac1d0226003000c0b503a640c443d00c61030810343d513209020441c0750602c48a03070041380864115083c0f200b540c0303668002c0c40340640020140f595640111041502400607124912500da805004607480181041800d210449030380300154038008280003e54080e02c240c1e007142d86c00101103500c02c2c0c1054140100740c010103150060701c855490b85081344c1c0e0380d6401904060100e41c40085400503051500c01d0640d2411410300b02550418403c0c88420760f800086000c03610801c5401480c0640c2d10304204009200d00d50051940c02000d4032803d000c0c0700c0d80c9a03c50300880c45614200103407203500d690001c0d08000621800c210002c01242002140c03a0b4520020400c40b100398002480c10b6500c4026140c136000884810201d0050040580c00c0e2070040c000c42c684040090240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 323437544 1250 323436294 323436307
    0x7060e0312030a0203090f0f1506121e03070503131508162d0201050f0109020403080a03050402040212010f1a09090f040c0807030b10061806121e02130605 68
    0x1d412a00009140710001640071001a88a074410400700c586034012405032078a108040908503211556408103c3d445a142400b0501609000401d250310011240140240c8100045190f56044070003220250314802403201d1004520248002c050a40c6100c00c083c01051038000e103000c402540010510501410130300304082c5800210210800d0b1000e490309010a03100c003072140b0060081c02d131698031074503800540d2844403901503002d030340641c50032025001942c3c0d071443e902d410b0703100c0d5000c01440000c06001c00c01e4464040e80003d42c01a02c010800350408846500f017403c21074003644400c2030003400d1082080f140c071142c01d100d00ca42c01391800440c0780081e5180461410000902881c40d504490070015081c80b02c104030b00d9001d0980a0305540200d80d5900b04007442d02010f580c442c0410184180014001e8000c21007400e85a1041501801c0c0c1c5223017682c1078070410b10102d040c40215855880b4000d9104040740303441c0701095200300041c0c03110500c00d115244044140c114805102040100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 323438794 1250 323437544 323437573
    0x1b03010b0a150224010e091603030c0c030506100f0632040e090102091c1e02040f060b13080d02190204020d05090f0c0f0a090e070e010807060e03 64
    0x7458195480d1048040030300803002022072030440e0300380740100881d4920b40b840382041090146a03040300c031400740c101071544900281c1a1260100040c0140c0380d50300040c01c000003805180001d01660041b448030603555a82c3e01c1d020704111085401c0508460540170520a12810506c110060000d038a050001c48040c072002d03406605181d00c04070703038a079540c4180301d40110031102120301521803103195001c0c41c00c014003114080d400c01ca00c1a4401c40400483e200c0001341508403610403a0060102ca01c3c203d4070b03e02c0075401808994003a40c001e0b468403035401d860506405070100814031910800e90354505559080600001071b0040d03810f0790894808280986d60008a412800d0715204032040e44441d0f52000400030b1080000c000e104604210030485040c4021441100489568041c0c502d45d169010410510544109005900602e80032003408100115444508a100440100c4041d291141207500d00003800740e015200c1a48a642e06102d010340c400400d040440d0142c2c01800c584906050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 323440044 1250 323438794 323438809
    0x61701120f4b110a0906031401062702030403181716030b16111005040201032d0b010909090b16050a08070e0f150c0c030f0a0308060d141b03010b 64
    0x8029025a00900f0840a207582d10341c002c1c002041c1c51403040101568910f801d95014090200100083d40f03000d40c0000c04904100d181400c48409044003062042c04070381400080d00082d00650410040310558111070711080c1c03050024005442860400d4200c0d00e01306442c06124001107a20156925010400145107400c03503608818485104410101e10300c404841c880d82e18103aa200b1482100a000c203201c50a501160143e4002e903420b000d400d03600c100d810442a03501d20f240c0d000705026500514417007520743c011802c554051420045082d0fa40340d42d102512800c050903610400400188075601d0840101d03c0040031041c00c0460030441802c1f17001e402027a005043e4814007031040710010507603071001001d22070054001c2c02040b008001101005031904285110f660750301c00c50054070107502d0006982451910b072140140100441564105c1c0d40719000b424094220000258000004003034001401480f22654000c00000000034005200006a440001d0107a4982088a1029110403a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 323441294 1250 323440044 323440193
    0x180f0607030908070501090c05040605121b010e0301021903050709030507121401050907080115080606040e120c06090c09040f0f030e21010501061701120f 68
    0x1c00140107403440c10520181c0c4070350342c03005002d946808490001c0140603ca407805848041d03404110140c1c4a0082c0b2100880010702d10103194002c82103030481005904c251341c8070107011f01d030501c402d030300d0800443d082ea000300070354008000300b843d0141072203941481b526034070000524200104c5855a169683c5586031400b491110101169090061200c0704510300b0311951900001c205a203080c01d0030684540b400d00605003154200100003200000803c10384040d141c24401410091300c0740001c100c0107102000f88081d0300d0042c0500480c8801c1170a0240811a020802400341480c06001c0c1604010340700c803465209441820a0101003800003041215041c0e000c1945107501d1400d050954546150303040042d40042034212921544074a0f6680d0900d180c4030700000c0c05a41d0721410f00b034500c5c1c1c43c900e01c2803516280c0a4010854900082145400075004003c01040d801ca01d8441c50034103008400d0356600d0440360f42000744008081c03090702080003292464245680d0442042810b142c1f40742 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 323442544 1250 323441294 323441297
    0x1502040f0b031f080a1103010608121617070b1006050909070c0c0f1d070c080d02090402030709080d020625030b120f1005061c060207140303180f0607 66
    0x84000782503060205103c6440d500d424604055195944000664410001100b190200d8040d0043c40c0c49040c14002d940603141020050f05c8900e10384190038180d5004291003100c9a01024040004548a00c0540880c9568200255501c000d075041284140d00d0140504ca09208a140c0070040c3c07950110a484001004884c07856603501c8000741199a10b1050307030050300f9040c0d05000040c6030400840184c003102c2a02240c2c1c47c04240d031080070310301007404840c2c460105402900242c00600034100800c07103400003241c0181049018800b06040f6003084852038042030a95400b03102c680c2c0e04110f4a01c105d60f051005000d68904100060543c03c0352070002e4510007002d4400e55481d0b4003a4100e44a641405401c000c070302c0440c0f1084a55480c1640014501d0f401004200040b001c1d40d4041c0c11710415014111060000d040e19050300c1c00210880140c0d040d540c2440700c0f00c0003462940c1201d040c00240344c01507480b8100741c0090000c650b04200c245540e5403161004407900000400e80981c818030341e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 323443794 1250 323442544 323442547
    0x306070509222408010c0c1101080c0c121b010e0c01050d020408061603050f130201120209100c0201020606040c0e0405090c030a080a03110708031602190f1502040f0b 73
    0x101407010b01400703240362044814503071000b64204940c10b081c1a0002c40c1e80d9400240849907800c1800d4480154051018055070303840800904154011280a81c0101c6060b9505240103003240b00107007007281c20b110070680f0180c002075054011486000c402d1642c810040204134004d20101050350b980d0701c484029045c0300000c038082100719120341c1500c1c000d02505060b10120315000419246200e00c80d4200c502184c640808038a08441e28004030b407042c0d42e00156651074414507001910500c507103042840c15590200113542d45600c0e40740e100c0c044020f1640380e0b0101d8030120300c000390809400403d024080c40c900a241c070038045e40041400c0c3c9030b507800d40c0c0c00505138440d6071003241440201070846405201c1c0b40315140c00c0061800007019140b0b580c0d6810890789601e420b8030b2481c1d210700003010f441041c0910215413030078002c400b115000c54060040301c5200b041070140b480c5011000e0000c0c2ca899a90030100c406201441e0702020075644062421494613040c450307003c2604500340100c1425280 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 323445044 1250 323443794 323443849
    0x150409020f060a020102091801050102120c0304031403090a060f020c040f15030b10060e01080a0b0d0203100c0e040c05220506030c03150f0f010c1104060f050306070509 74
    0xc03041d0051440000141c09265607815480b00640070b50b200e10a001d0040f541c04880502860341d02001074140c90059014282d400006103522a131a0070080c90710500340010800000000c0301071558150107441c800241da210040e280c02c00400e00c540b0b07417044040c800341c80c1c40b810100707902040c0289032803411940060180301d6401c4240081080449040000124181c00b2042c4000b42d02814802c525049015501c0c90f15007000310f840c0c0380409845070218940002044021f40305400040742c00c0009007101d5950305060300005c1c5041c05407103c4c1a50250350308900e9040c1d0360301c0402114144010740d028031070701c2c0020900400500c40c280401142d900c142e40e140c4903090500ea41f2400402001740461703100d081c56196400c1c0381d4000d8803030980f00020300061413858140700079410110500140410f5010584d00c0040d1000101c440045803101e665400c18111a6110700c07914020707290007910b085030182080301380740c90311a000d480c0340705025041c402150607a82d4040c0c0c0301500310403043c036070140c1f80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 323446294 1250 323445044 323445049
    0x90c060c0c090c0206011e050603040b06030309040f0209030706090e010b030903130609050f030606010905090702070801020711040b0a0308040317040902210114060414031e0f0d030515040902 84
    0x705190002002d240c00c04800540440d40059502e0594081d0703050000709109200842020505c030703101340798120100f40001030102d118210000c0e03012202400392460850883d00181c112040c2c0881d445035258081048075150408002101c080c0c505400c0548074941043c000c9e900c9810144100011341c100080003680c03084050040d507069440901c1e20703200c01c40d29000082c02c104668090280104003e00310f100c2c00345030024400d0300810781a15000500703400d01040c0140c0c0c240051560307040d446021400180d06e2000d01c01420350500501c030428161400c40708010540d400592901e216405845e001d20105110303000321005c0303d5012603007a4103102000b082c140b807130107103900030103e01c0c1c4045405290307080c020760614420343e00d80d00c1d1302c0f400d40e80b100000c040c081c40c00b90800c4c0e00800f00388018080707039a80da00c1c8060b10302c07001821100c2c10241c02e4001c00c0505038020b0072140c6a001042c95501d021003c100740d070b04489090805001c1d0340f0f0000780c005400701c0c4038041c0621403511400c2d40405d54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 323447544 1250 323446294 323446313
    0xf03140304050a0305030405030d0f1e0504150e0f0303070312020d0b1f080a1112040218090a05010e030306010806040c0c1506141804020105390c0103090c060c 70
    0xb850b0240c40b10707420a641381032403900e039082842007500a004190350329941510441c80d8817140070160b101d84000e000c001e01c2408840d12201107550902404000104000106070300c14049901c041c1d41c0c01031201107a80a00460881d510f1005000394018001440025044102c1a40009443c20010303220400500a170022704904c13600a508181e241c0034110501c0009048025072032000c0d294158517860ba503d4080031108500102d544000060100b8241d20a00411840c0c2160000717004006451010606d003230540c401380ca0510b01680700c0740315241000801c0c05004902c54218000d541035180500003c2d011200092609104569402c0140d01341809043d034000942d4000b080e58500200700640c1500404031070240150000705100a00710b6850b042d441e0380101700503c2085c5103e9200e5038015591504461001c100c0440803003100c0200151010884c040c2192a0b8009020f01c00704008040c186030705149001c1c1010708141d21540440c0c2c41d20b001c081194228a000d5651451609151804 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 323448794 1250 323447544 323447549
    0x606030a0f110c06130803011a0c070605090a06030b0a0e0a09050604080307030e03030408190c050a060902090a180809060f0d050f01050306090706141213030909060f03140304 77
    0x4a40c40d1921012192501002901104083c00200c441a480e12600c9079860b41c80740c2c034000d102030b0b4100018400c4915140020421008020842d070400150400c001d040c2222600410300280020401041510381481c09400404007401d08100140d100c0000c80c0b081700c09400b4510b48250303c200402d0300408070b50300c42c00c11706801c07505a50107402c191402040f40d07030080e502d4000090511800c0c500c0c00101004880c055a8441985450507499801404074418103107482414020701306c244a000c500244244106603104d288006001c456a05c10011294000380a4443c081d24000a0744407402c210b0031080940e5400c03d400782d0b00e4102c07500011700648200c0b40032600042001c40c6400c1480001c1e00950b0080c05408001d400c83d80c0c0710001c2c507503140c0d81200c1c0c03840264011181044642c0c0503e0101c98010003a030306252400c51440c01d902182c031010380390f5030310035214071182900f803540c80108080a441000c00900800e840d04200060300043350001a00d6016800c281400081040084600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 323450044 1250 323448794 323448821
    0xe0d03140112030315150908012012180f0307060513020121110d0902151207081b0720120304030605060607020901080703110103020412030e01030e03310e0606030a 72
    0x307a41101d10300030890200f51050b2042d40d07080a0040c030038860700030304800603405c13514012b506299541040c0b80c2000c001608004050150741c2c00c41c400301a05008900b104190240110740d242c20341c1c5080340440d14014590350300c00c800c613849500184ea00500240030841c00351a1131600c00048101d1000612801c840342d440054001403a085642450b041500e8480c003c5441a5200c6281600d904003849805400e940d0031301c44100003203145024000381c0ea00300140010020f102d03542c15104924640c449035045e90080d101c0426031603035080c3d081003040317010000c2d0b96030b05001c1000000d444c0d4038001c42c04018081d0351284000b485540314817059130791290f002400d1144550307482052940307442c800d010070386510b48076139107101d02c07035010780211070482c1c071b850354201981100c60301c0840302031440d0040c1a04054990407020005c074801c03c040d000c9048035041200304030784030080d5503040051301603013481e841000170001c2040041010920b54080c0007a0790f0345603a0707900d01019078000d0051030b80014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 323451294 1250 323450044 323450069
    0x90705040e010b0f0f2206180219090501020607050c0a0c030c1d0c09010e030c10080106180f05090702150103030c0b091504030e030109060e0d03140112030315 70
    0x72100c8005400015070054141c9807203840315000303018403503050b08011000307421034044080f400e1030b01060340f4020044502c42c1000030b882c80c0ca82c4c02000071482c10600b180140c0e0340110b40c4201c0e65110070610b02d0090480c1c203040d0207861900c0d00217034880c0300003409030041c4580461101d1500505200c4500e40692000c1482c40e096103031326041c03035070f0000d9008550500764640c1d03050b8a01d0030031410560082c044201d600d400e0082da0001110312542c13250f04181c242c080c402d070a10154680550808000b2980d0326060301560404500804611062504800110b00044100002129543c0c0807003a6001034982d0f120030354a00d00260310f80194a030b4080860340d500c000000074076501120400d11a8072070000040c2688950f02d080742e55905202000b4640c21382b003004200028000c025071503044501800106800e09030740c071010300700c0b81c03d008100700940181c80c0c14004c070760745482180808000a640c041541d410445110070200241000a080c16510905a40c0e10348000f100840145008000300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 323452544 1250 323451294 323451311
    0x1506030712060507020105070801080c190e040609060e010207080409051e1501030f0c0f030f0e03041202030d02010203130f021302160303110a0c0f14120703080601030b010f0809070504 81
    0x80280f0f0100c0b022001940f0700342c041401103105100440c1254400402030004120078000c00142c10040d03105480c0741c0c071044034001440b446602d07560384151300544001501510b64240001034900500e090680f03130b4810061040010085000c0e01c05540c05046c002815507103010000e0030b941c2c007001072203490110300b900300520807451541241041c0002e03a02440010201c00c005400d407002030f0250004201c1c01f03c0b142604c3c920a038070200104051220100d08811687d1800382140d109400c4003e003846611011015030a040000341d9030581c007407008519528100c2202c080b03940304000020a0022140801002d6680301c40020765951145507045544508040e0103c12034000d50008501007810805020b00000d912410f8950b6200d40d41c031800c15074442642c445451070b08602088814000010890ba400e0104101d409a541082c8411564892a500303000d05003003070080206041604101c95105681d81c04000070600300c030300c0d05049000792500c0308840e05015654015940103890302014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 323453794 1250 323452544 323452553
    0x902031608010b03030703050403030f0201061806060311070503030105010c111c0b1003170702030307080304050601060908070b0406051b0f03041e0f060c030c08070b01031e051506030712 82
    0x90204580d07281c0d008012010880c82819200d0042036401b4001c03c0f4140410000b003402120703040c45283c564400042d900380c589420204003144d940e100102540c2c1da85040c80543c1c8c0510800c40380b5a4a10780d0641410800d503240d96491005026907810440c0220058003002034100520b8681000100701c881100e100030803000141c1c2000400783d41c807650b2800440c0c654103441343c0e08015a9004030000c00001c1140a0412140e44200b0b030890309072004000100101e02640701650095100d40058030143d4034105c030081041441d900000a250032008003084882c2a000c00c40d0202c601c10308250340c644240e20111602042c00d841d4070032541c0105005644449408070050050740e01d4118401c2c1e01540705440081e80111078050790200364465003082c00210302031800f1059071442860b00ca18011000c1c0e032201d9054000002c00c0341c0c1195080018410001d05501c00c24800c0c4442c0620801800c45449603950707621880b0001e8081100e41c00031440507101800300b0005421445560031825609190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 323455044 1250 323453794 323453833
    0x181908030a09120201170c0c030c030d05180a03121b030914032b1d1c0c0803060103050a02130e15090103050a06020c0c0a0602010c0e09100e0a090203 66
    0x702800040c81c1002c081110808865042c64094040e0b4405031508000c10140b40c02035000382003250064000e00901208103001c00041040340350382800345488040104591080d0340c40603200b0b1410749281400701a6501001510004450705403810350740286400041c980200001981c0c14000005c11407482c0080e45c2580215280314840c012000361001040c031125160701070920103170300b805031000d9096441c080310107900d045509449400208040761382d91241c042030b1001812400b40d00082c1d005800a900888111220318181c01c020000e401c4640c2c3e40003440c0b00c014202410303da0b9500104121080a606545c0d0600d00030b00c895218580314030b07200c0071440f0104e95580c10201c81d01405040c0307080c000c1c492030407290b102c3c0c01401c00c80e03072581da440040e4008125a071514032900c0b4a0341601c1c0c1c0c541d40c0c070f04010f165075000003400c4001c03441c0c020300d41c0b020400c01d107009401d410140402c203420441a0400c85001607005c40702070316006d9202c0050074802101a41c103229000c01888444a10741 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 323456294 1250 323455044 323455057
    0xb060d0f14060901050a06140c010507180b040311120c041e0e031305060f0d06060503040302150105030d03020d020c01050f1602010603031e180b13060203040b18190803 74
    0x1880900b0b688250800181d500240260f507000420160108000c9009202c205001c940c0880100c0c100340c0703002081400c4440880700303200055a00c41c0c03003600b4500050401d03005010a510800d203800d095840f00c1c82c1d01803c56000c580558880300700680000414042c0d154281001003060000200c4101000890410650411030591402d00300301c03022000041101c0c41c05590341c0f1500060f80c81c1c402040003d0b00070002849081d0743c00c02018420024a10800c001b601e40ca88580e5201d04190070024030300b8020710041285443c5440041c4110365000580400040d6140350142c1d44416105500001e4051344820003507540c20300d014007050030b01108009104050050000079001052038089007030f15164031002d40401c6080150540000405030000421407032410030a01740405810485400002c0390700801032328101298210700d400010f074105000b4042c0b44000c43c01c003400c00e0404030301803203445140d0460005a003040e071550745a600b00703081000c50280c0852003060b60741c410726031260f1254 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 323457544 1250 323456294 323456321
    0x50606040c0e03070e060111010c0807030509061005100309060f09020f012a020d02030615041a0603060d0501110309070f0b041d07030608030a02011b08040b07030b060d0f 75
    0xc501c2101520800d00c240d1400001001052080e19014800b902c09601610f5203041040300042c80d11107a609006401148002d5501d00450340341c030340002801c071000986000c08540010b800c0c48103070040c80084409070743d0300b22014401135903c1c0078140c2c01066003280c0245100c2c18a000103405000d50391004182c0c5009450407041001c060b00110344041001564008003a100705204002c41440c440f11445988090207101b0780e002c0640000340713404d5044138007111810052902c1041390806000d691102c19060705911a40c0c1e04090028845000c0202581d000301c210b00004001e004094003c14031380360000b01c01682d241043c13481c0c03544600c0e460041480301c843ea024002400c514081c200c90485054080c1160201111500e01441075000b802000401d5202d00c40420901c0c428001095140c10907000001c9809071324000401c04408034402d2000d000ca08001c05c4041400110115800800340c030707000812481c41c0001400078021002400911480c1143c440c400a00a0b4000544041e10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 323458794 1250 323457544 323457551
    0x1605070311010507030f0f0c02060c011a1f0305091e07061403060d0809040b100302090f0a0605120702070b030414100c021207020604050d1b0905091518060405060604 73
    0x20700555907841048001000141e1981943d060f42d4855444900010301c9850451854112034000940e107410004002600b03941d81c1070190001049025010134018007a175440801c111014209081140648c150000381a11000001c407003541c144a000b18031a141d040e04c4200c02d19160b101c03540c2d2a224069400071481c1c688403410804115400d0702d200d1800140060a004940e40c2d894525401ca040810f400a40350f0006826940d601031080b8441842940c00503200d8560f001001507200701d25138024002e800d5048148240741d0b0006c1210b49c8040c810018020311346504904921b000e903640d1045006420202c10b000400001e40c000715040d04003e011100e0301c9040b000307120b00f22125003002e0750159003d0520048000c0c0010054107207640020032a60030641e4032000b149145207501c3c411a100903820017100c00d02200e0321124006400035071000c00462070310782251541c2d0489000704207910000d020010340d1081d14000c042403080d0b0810309031001c030b080600d070140c0e54040030b80d0394a106504 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 323460044 1250 323458794 323458823
    0x3280608030705100902090402060702040e060c0918041707020607050109060b040606030c091e081009030206100614030406090f060c0306140619050c030a08090c06030c03060f03010216050703 84
    0x18000c80c0d40b42c54004001f0030743c030344031035081200305d9201d0031049800ca510317000e0705000702c0024810107201e1b0030b4141c51260b42d0383d100410080c0300300d400c04101040301c024a080c03101296080480d06000d13082c2c03540035540c0c0d0b003403800096554001c07810001d025608000501303003040410780002422071401d4070113000254580c4030039019140111118000181c04600401c40f00300c6406282d5000350074140340818140d22980a14200207010043c503c1007601c071080802007541c100700c56a40600b20450601c5a01e05140700180640c0340001c071040d20f00b102002090900246a10000005901a40c0c514000001d481c2503005000c8402e060008603241c200005010306422a002d0741411000340200d190004084001546c080d011140c2c0303003042002d00c1f21143c4030004000400003942941c0f11101c09243c0424038a26103494080118010074003031051142d1a00600241ca401c64421282041c3ca0340010000c40c1c0203004103030b103206c0b54540c1d08940740140040440e94205803401003900489051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 323461294 1250 323460044 323460073
    0x703140f0d0b0105040504061205070b03010f0b1e0d14060a14010302030414030c07030501050703060303050d0c020a2001020c120a0b1b0a030515120303280608030705 73
    0xa1410030000c0c14410088195010480d038402c0000b200d05040041c1405e8507100400e048880a81060f5002044034050009008042080380020031f00c4000c600c0c82d540c1491311118100f80b8505c160359142c5c6002c174a10307160001d81e0041031100c07100000503030384508080304580060003007503031401c1c2612816004100241888031510040d42c424261030814124030100440c02944010015030300c5540b8900d049a0001040c0001d0180708650b4000744051815810883c0c210f035005000102850301d008001c10002e07400c03c090710300d02c0000c840001100615054180d0800780c1a040c010060b1100070000c0c200c90314080d8102c3c039090401e9085415640e01c03201800720310714065040310403c3c0d12905050000170300c81c0180551000001c40b040805007500c142002c0b1541052047c500802c4d02c45040040d80015500d040c0340040e002c6400d1000c40ca04244881e4036031201501140f5510110041d0f140b946444000b02440c1d20b511079010000c1a956203480c03a10f81c4c20101017120103001c1c414004142c01c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 323462544 1250 323461294 323461297
    0x8011401020a08032a0301090b10020105271509160603090b0402100215090604060b0d0b01060f030204031b0e18030a08071e02060402010206070c0c12060e0a0305070314 74
    0x10351151100f843d54441d1080f00f403c085200c00c50395070a507440102d007603881d40e01d0f17409140240301411021842c0003042003081000782c107155928007168035000820000c0e00c078070105070041d414030b035817141034131001d07d504681400300c45003503640f0050b10881030155503140060349a00011501c50900d8200351204800c4040d6500104090300d441e0220010034090304c0e0021180c3c8038505140101c401005041c064a5065141105c0c1009140c100008101c1488075034001c940003c0c2040f55a00f04417040c0d0754400b00d02c0a41806448104050b2140c400b0000e0b0080d81214051908881000c1c800c202e2400d03c0912044103000e600400e6141001003030b00001000d903441104005040614244440380e4030880e0140d0005100208010036141001050039290030540040306c11580500b0407850140006450800040c0c00d00040110781c200c12008a4040100c0106940301c3e10314900b100c41841c18040041d01c3c46410a50b0240150403100040540040c018581c02c2d22a407901d40c0d82c2206030341030040a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 323463794 1250 323462544 323462563
    0x70207090c0503010504022809050901060801050618040e03040b0711010905010210090c05090a0509010c0806101107170d0f020a0b01031e05030a02010c0212091c0501020f0a0801140102 81
    0x80b50b07007400180002d00d03050300178110f043d0540d032400079624203158000105650035241c402c0400d039400c0b018400c40c1810140e56014002c4d5041c02d80c00c9500d03107008940b8134801e810948842e0542e0440101c1c1942c1c4541104e07080380b411600303c0c2c1e2983c1d1600c0b05001541d10002c411199031020781c0416041c6d50145104004491f016000380071010b00300504040a040d00410849208030a080007090719030b5104072050041c41400e50008180c40d04004003401c40308070101035410f0292a10420006964a860407440d0300712038a4131040300c00100910518140c950340111106102120756055036160015005020740b959a03288509035030b0400080e600c6000b0200302500180d04600140301040700c5111561465a142001c0c0b07184840360f858044c2560400c40d001d0300140d448501d036041d03c0f44d0410482d00070780440501c1510f00012200015100c82103000c22249081c11048181d00b806030a60540d0100005142016610400c002c070040581c0000d0007822400b201c48107454510b13510020b080201e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 323465044 1250 323463794 323463797
    0x24030402060d0609020a030c020105060a051c0507120515070801030f06050919060c1d0904060506060708040e061f080c030c070c0905010303030e12040501050f160b070207090c 77
    0x145444540030310103903038040ea08001c0c0380d5843c0c00b0001076214043c0b001301108080d030b640024030040c2100c0001e080d100041c02d0342c4e22400812906000c1981c50703038603030858460145194115600381e89052410030026034060b82020108030810401d0040100f2100d250700340d01d0000d4001a40c4d01c003825103000c1002c0c00b01404000c0070f042c0c9600000c041d548010f42007800c07a021038250f40c1011403180b8088070b000408070340264481700c03c0701c1056045141c03190001108441282101d005402088041c14014000307091180c03a0004100c0e181c1318001110007258014030b107146c0d21a26507518100e01c0f103099a80c513016a0307586041201091100c04540d103240080e607516662600d54140c40c0d025a00081c050421040c403c10000c07000600c044400401030004e00300100c0c20390b01d9414003400311018442c501800307410098050300c0058009044071300b916030034204581c44020f28480b9a0090041d12802c40f002102070346042c040c8207030024407900c00d0304240e086610039501d5280903000c1d100d12400e583d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 323466294 1250 323465044 323465047
    0xd0b0a020a0309050d11011b121a06040b040f09050403080601110304090e0105012d031707060f0f0522150e01060f080c15030a0e070302061824 63
    0x122045059001000c030340d020361a01042d800081d440d0305042003460003601c4003003900300a4505201c2d1080c001d280d0010821034100214480d6410090408295021610341143d980ca040944070307400048a4040c0350009070403592519229401d030611a801401402c0300c01e00c00c044001851000da0003900d00c91a40b541e108106900c1d103000545240e00700d11211501400140404603c3c0141c612130480117420300700000c01c0300d51520724001e64045a55072a02c2217004240c51021100c41010092070449502444581040844d0b00301e118280c0078400000b000b40d401c0a9511004180d182c114040c0c00e02d07110410099516039141c401c2d281b1780301310b40a101140030443c5043c041122600b550407602c82c1c3e0040800d245028034541421140f5903003202100c6641d1304818091601c0030040039440d450300f96511a90b08001a210342224040206003525494030b4106103c568072061009000665018080545035164280760286440840c0707903d0340501c0108440104000c1a902070070701e0907001101c800e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 323467544 1250 323466294 323466301
    0x3061104060c0605130623060a030201230c0109060b030d0305011401030903020f0a060912090311040504020402091e01110714012a080d05150f060a0e13050907050d0b 73
    0x41c00980b500030041c404101e00ea008117004588180030318070440000ca4280c180d003864480001c11403410142285004000030300041c00144d0704a01c91030000c0030446041c40390352640c07658501480c8a14480d501c1c1c19402c000310722041040c0f6070080d250144c4114203440c004400321000b10102d81d424803404100020000c03450351154042d80c418140c09002e841564138020020364003518120220000700d41c2d41e940c9a0521007445403c42040b0044141407034002202440c507103880302030644e08160903208642e2a00460110750351036048903040240901061040e60400c200c0c034059507500c00341203011a00826189009500124a501c16100103101071b45041706101c00449d00d03080c1d04200c26550b1503020307848000900441c8103013004140f00c2e071120341e5210110031140b0f0075100040d0003003441d1512482c0e00b000f1540d5101c006000c0c500c098600545592000710101e032150b0000200f00d80003040c116229074a4103403078001500c00c1050f00200c80c4031590300c00510040c26126100904250181c0c00030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 323468794 1250 323467544 323467553
    0x2070c05010e180a14042006070b0103021009090f0e0c03031312060e070f031205040819081308010f18020109141504090c020706021207240509030403061104060c 71
    0x11550851300090000401024007418000f800c54151025290b84c01c010590454014594501942d000000d4503002d09120013a566801e03084818000240305070908103000e0022841021014000d1031044400c1c40189100c084502c01004441051000c0b0f01032a1080416402e00000b11007a00c01c050320075030307482d526051000302e0040b00c3c000212111a1140300340c0c122030000308400000340003e2a00ca0789854074610b881907984103c4200780047c008140000c01101801262004001e0500101101001000d241c001a54401c410710150301c1c460540700400c2140c41517000d4071504d501c401041100d4280602c10354001c40b110b80c00240043d80e102d205009003000e1900c0f250040308007404443c8491000c40054029070803580003030307240c0390fa500030070f07a195a410002d180080c03503180081c050030b0107001081c1c81c2502c44c00c000541400e80080100e0001c0c428509201e080c00071101003080b41c1d040c04040035840c0e522522042d1030780d86c18800b1800b01852800119401ca400c0ea85420f44403440e55680c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 323470044 1250 323468794 323468839
    0x50d06050613090305130608040b06060703030f051e010f08120a03140a091b18090507030c120302060711030a1209020904031e02010203090a260a0302070c05010e 71
    0x600754024003600703034000e1101c031103020300d400461094941e691118507914a00c101c0d481213500c404100300718035003400040b03010306401641208059484c10f030340c1c203850f0030140c0180400d64803c0c5110307481d020030840319001c045000c01d4a86003211650b84079903a507081260104226000d24505500f082c999052034403400c4000340210421820040760040840d00e090f4600c0004a07403450015441e02500d4040246100314040c240c8070f118080c0404604000d82c145661140300075800102e84c4d2034488000f40300c0c0410000b0021030b4030904800009460350500482c02d030b100c1c072048000d07104120200c1c0941d4003d20490350b00a8044000b10704040901000301c0703d8172107515120750425660082140035844d0361030000c0c4918066216020706d80d55241d02d98264003802035250301164418010700213140c3d40440d5003414150885000404680908042008944071481d80411000c3c001800c219654240e005416443c1c0a030000716101c95881006441c002c1100d45071651049400342440c42030300c06002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 323471294 1250 323470044 323470051
    0x3120d0504021f08070f0201021305060f09040603050d0e03070623041e060905121905030c07121a070c02040903030209060c031e1204080a1e0302090a060801050d0605 73
    0x1004180c4060588400501103082e89183e500095030030307003c10050640151640c0004000c0340f008502d07220506100200652075402903074824440000c0450115000005403000c1c0c400007001080020360341e06e8540d071f0380c500003403203c2e005c00c075652849a4140740c007007811404c0b03850a80300c04505c00401c059212105000c5041c4000c405020711010410441c41450103202e10340160074251030034107003000a070040800380d1046200c2c0f0290548520711010205078040f0004204802c207505100d80c9ca060b0341540070313006400b003051160403c0000c0000a2002c00c08505002c0c211100d9108841c0c400c14000c000c1c225500380c0401e808111110050074a944980c04081c002d290050518000000094540d0f0003a29010b145510214180d4229900b800c1e086118201e0410f125103028100e0030b080e041c03120700801c0078083d25004180404c0ea0390299004030b0f809030080000207802c000c03240000d0001d4114441c680d0103415076100100c0c040d40104d079914181c0e00010441810408140e5400010f0007009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 323472544 1250 323471294 323471299
    0x30f060301092018010612020903030c06130c0503210306030c03070f0f0b0901091e12030302030f2410030e03070b0717010501050412030507150c0e03120d050402 71
    0x3010040041884000301881003c1c08800001e02401c85108101c0c400c09480519035000b007012004100c020341100100d246550803031009a00c4840101c0040d045004250321100309014280811001c80d0303090f030f126407695100c4c01c5900e2400352150300385581c4003140250b914110281030310b446014803840000e581c2c040e00c000d00b00c4245880c1480480e0070406c903135002100007a407a07501071100b10010400e00029001d0147c507035060189140c0002c01c1d191017882031070a9505003010146e1917611201e4010081c0c101c1c0710402e03c40c25000d00e0020000e51084440318481201303440860626442d004107599884165080c061903404824100f181c10941101404289079546002620411043c23028000e0107009111303144c5180303030151014188600040381c0ca4960300005005100603a000030070741d8140ca80e007e040c4008c2c0c0001780b5054455204400c80548000000c140d21101d41070590490f403e55180c3d9a190769242c9903103400e060307a5503250b400c8075014100034405403030130904075403040307a026000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 323473794 1250 323472544 323472551
    0xb09100b0708091201060305012931140106110105040b0601050c0709060330050a0c060e060907140406060801030f0c051804030806011b0303050702100c050c0606060403020303030f060301 82
    0x5404d025400c440c0c4c1944100d400340d454540407003801c0d0a03654020541c4c5080070010700c0010080c07000684411000e40303402e10304000503051089012841d02151550221100e08029030f61840d500300060354401d10800c0e0000307103140c012030a80d0700c041c01807502540d1302201810f296294400103503480d801810f0000e00ba4802c07854001880810307809600011402516a039441c40704129412a00c0c00341401d00b0803602400f8055007074100d51010450b00001464900000c0c10362251400c4009041800031310003503445001d0a20503c02000f03d0304408560389094005001c8844a09201c1910313182d02c1408040b55a1500410120f030041040e01d60f168400c40c0510012915100000c0c1044010401c80c04180c03061403c010815400000d150f42040003402d01c0880c10f161801c10392141002030f00d00904240e00c6a0200d4020303070082050600350041d0801c10703c817144103404000c2164206a03001840f034410b01c00420108e0410400b100d003a660090301951669948140d146aa0200646402d030190741c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 323475044 1250 323473794 323473819
    0xf031002040b030114040e03031b07020d03050d1407020d0c080906030709090c05040312030c140313031b0203031b030405040f060305011415100903080406030b09100b070809 76
    0x1098402030014120030a070442d00c81d4141030b54201000c00e2011094016494603903a442000d40000c00e4a6000c0696088801d00901040d00d44405010700c070802900501c0c0180c0e01c01c105a0440054094801140c2041002c5120905500c1fa4803909031040300c050b80190070450100ea12440a03030507918001c546852030044000040340c8598001c036000d10000d405e0a10902000310140659240e44103a85017060820b4110784030148200310044005091582c2c03000b030604d540d17000300e1310400390f40c0450341040d84910b006045e071107010301105811400510950764503030050000e842c10811468029004605050004030b000303101000d8a10401110306c0140b1000466644a001d54105030035144008929545140741850940780700c64031040001d4801030810100c15141c1103210a480b0081300d4013520202c5a410a55600946400140c00b0b144002030126485401d43c01c038460130513040d1340c1c486c0a540d0f10312200498030140d0240a025100400c107040102e007018003e440c40800040c01640a8031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 323476294 1250 323475044 323475073
    0x32c030c03120108160510050711031c1106010b0403230d030f14071d0d0b0a02190c03050409050a0e0313062006010b031e010e0f10060e0f03 62
    0x1000642e95a02071400a4014801d500c03040c0310441d0322a0301c4001c0e05030320908080008240c2e8541407011402c000c800b090003c24814001c002840b0224050261048a000540c4168048a18844100100d1100580b2207040300001440a048072000000582410308654400c01c83c8001007145800104581603915101c100900280b0346011403501c0005009248444070703001c0e203420f82a13030552080c00b107003005801604401d071440c603004803100c00d290714200f8800085890900401c09081500c030706007003000222031540100500c22201e480010402c0d1350240c00ca4068182c003000900041d03051200300501c00346500119040301000c3d10120300202c0310fa9905245805c9148411100e000d2548100401500301c213070700c0151110300078046e9050340618045c55440382d046c4591040b00300c0010006104807138400301c400007060419480c0303c0b5540d446092180031841030b50a590201c441d2404a0030b2050000745500c22100182c5032070170b11aa207202048041c40ba004441c07901350191030642c0f012070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 323477544 1250 323476294 323476297
    0x41a09011e081e13030c02220e011406010c0b1e0420030609030f0c0712080a1412070810030c0b041701200d0b06040b0a020d032c030c03 60
    0x4103940c40502c1803a01c40304070280c3c1010385851610082c60602842190030100c54034504113900b604109030660f21501c0880d4018800e40340aa001907071100f0b00143c0d4141d0358010740301141850f00248405908400448030046060382c0c2a03012540300c400328800600c1c80400c0644c010713814025800070300d090b184000c1c00d40c1c0d130450b001c94003210024041d985d00c880594000c05281c40a40080005207403441315999640b246034200c54240c400861902c180001c10044000909a0b011640e0b0000c0c0c190316203071015030802040380e00403070f4074856490342c3c101c0b013201a2583c04003440c00e12541340e02c840b0b501341c2d554800075040e200907000704440840840c0460140c90b008024481446603a10b1500040003e901c030100e0800100d0313410300d0120301000001341884028111034080c61079a0343d00060450f801081c80304642600494003040010b45011000c1c054128000c0c15000d0b6144c0ca810110100d0440703a0b180030401c2001e0581850f5081080d03101d1180d0907a00300b80c403c80b0b00d4003480603c20b9265 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 323478794 1250 323477544 323477597
    0x102070807050f07030816060b0409030e12031c1a1503061e030304030b090319020c0a14031002090d140615010c03050f0703050d05040308010504050606041a0901 71
    0x6200c0d00080c50020000100034181d0418000e80141904030b0542e80c50790454441c440c0a80c240c20503a40f0640e007413211a62154012440090042140e10801d15014150503000d101103845400d400c0d8079044c5102e8040226908250038900c03180043c45407040b000c00504010b244684140740500f460700c050b031502c0075001841081e10b02995120319000c403c00c01402d4600580c0102184600d08140d0240c031b00200b910240daa00c2108408141e4039503031228510700400e00d5804181000741003a11007603030007280b00407800900342c03220400c00b9154005558407908030100c42d5050340c440c8280710000381081e0b001d445810f90042c0b9080e05042a40c68507800d141500f59010041c0c1c00c91000d2200f0344010301d00c0884018000c0c00d03c08924103007a1400b5105028208200b901d00f903000604404045c400c008032003030500180c0d400c01640c00c06080090031103409020b00f9004910307200104d207a070300d0001c058404613003150840c0e1490707200f4040340c840c0710f4002c40281418000d0000001f58101d40c001c04551a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 323480044 1250 323478794 323478803
    0x30c0a0c120c060b0604031509020114030403050d0c110d080c0409020c010b03061605042c0103050f0f0102180103240b0d0b040c0e012d05090a080d09170f010207 71
    0x64403603d090000481386145015803060000300401c0000640b02641c0c0d48100701c1400b8005291a124001601c00300301790040060b212000008100806030800040c3c800c080f40900100004034044409655241c2c10031039000c0140d1203230120800c0548a50740a03907101d16180819030a02eaa65290141a604021101c0000380d4403100f04a515080802c81c0303562014181001c030030490361000010b1b02901c558001d1100c6620824221840c03000341130000c041a455002240300d203503a4a040c0152620418000305100313015a0b180c0c80c000700c40500a54400e038520382045c02c00300d2400401035005084039101c60021329100e1200380b405903400740d008001004400b030015522804460b50000302d030040e1703610503c594a00780000f00441d82c020000c000c042801e0071f1031825803601914941c02c0a034000901820319526a8865203101e034041701510f200c5100b1740302100740c1511840300c40c1e250658020007000040c03210608000c0346020700302c591200303d45001640e2004000060850aa81c82101c0544 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 323481294 1250 323480044 323480057
    0x6190e011805060a0608041704050303070804090e0f0304180b030109080a1b050c06091306081c0504140d03091e0f050603040f0809010323010603060b0a05030c0a0c12 73
    0x2900c9000e66030340090221901d800130ba007050320140544101070300c05403249009840c2c200c0300c603a0900445020700401001c1381c0d01c0c0c003058074044c41180d01038054411442c0c240f0381410070441000520301c4201404101031814107051140010038034645000b0442c1654641d40300301c85a450a214101850f4082c00c8c40940e640d12401c0083d1003400003104004404020452440128401203481580c0f040c3c200c032643d64854a031800180010004504e4012103447c10340c002075040c000040383c1d22003024015981400d41100700c03055079140250720442a014580107110465031a10742511400b00d8801d08028034029142d142c0000716007102c52814041601c480c3c800d101040310002d50308002c0904490345882d515217a9038080c2219051000100b405e00085846402d0380c0c043c1c1c2040d40320307060004401800b0502100c0108259800780b04035004a403a00350701060006075001207030038000503901e41d649151202d5022840c250710000c102810070502403030701c0000032070010030039440d100a079179400d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 323482544 1250 323481294 323481329
    0x906150d020a0e030f0705091506030f0406050c07020d12022e050a0c02100c09090c051b010c17061914130204080703080d020705010203010e04051504020906190e01 72
    0x41c11003040c60840c2e1384258840c000303001c801030000032140d082d11801c3d21000e40d2626840d0480c00c6224030f0702c640c0c0c1e51040000c0100b040304c405440e1030911841c0580010b100548419040000600c6400d0f80607410603c41c4417604041040325030f00c003804da46140304071011283c407010309900b00041200504045010000c09048c204080d00945400140403c810488400b450788069900c401070300e031407141030f521924000c83c040d000e02615030040c41199402d00c0800d40c2c03508014295070150072544980080380c4000740e07800c441445111110300807a100d21213480366001e9483c0380c050000704200e9020b5004210420520f038076450301c00017448504d140902c4522644208181960000101940c0342d1040c0420803c100c000151101260b80003007030b5642d03409404400001a21601c40c0141c40d9600000001a01011062441c1d02c1940103e0503154400103026008007620402d0750080d41c801091400f0843c42e250011183d1400701c542c1c004d4003046036507008410f1101400342e01180c03540c2210b030f004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 323483794 1250 323482544 323482547
    0x604060605060f031504090c0603020c060109020c0316061811030f0f06070c020604120317010f150e0d0b070801081b090714040b071514070e0906150d020a 68
    0x448000d001c1c1102c034142407480304805040b440c0001807800c100c4c000005028002ca44881d84210912034009078601107243d2200350140280d4044134525182c2d100d000000540c824040c800d0b0740045141c00b001e1403820801d8a030040502c0b0003a1000ea070400d075100d99042c20a1340742000a100d00707210f14600171249084004140c10301c480c040d24607082e6081440f0000400c603010541907403000c2a0f007071020318107050340041810303401503421003015401800010f070141904079000914101c811840346415030307204d2961140b406031610980080e14090200d03240e41501401c00d50225480c068982c02045120f919101103281d41958074802041e100001030000040a100381c08508d0111f85540814140540c007041c00100000c0c00c000070400d130f800304860711443c0c0c14104d40041c0313000e40e041da8480d1240c0c20024001400a5001550180340c445400b454000000c82c0c0c501c030318180d4031030304200d0030f001c1d090040346540141500d0f405004110410300c03201208001d0003031565540001038888800c40300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 323485044 1250 323483794 323483801
    0x2130c021f1b1e0315080a0602032e0605030601051908160c03020a0b1b04090b010f0e030604110f06040b13050901030c090e1516120506061e040512060406 68
    0x42010400000400c480c2100c40100c030340e030005001c4c6000103507203040d0710009007807848070307004182c19000d104850302c03d21a00b070700a9802458030078002524040398480c06a81c0026102020a0300344e501801008098041c8014560181c01810160300d4200400a018a4005485018808520080244007580e50346c01003420383e2034200d007492781c41e4080c2900d0180d40c1c1c1c3c80c4501e004100807012000140403140e0054400e900084c2148515100d984503501d100207070060307200450000350700100c91400c19201d15152925040040c1c060072450703c80d40c45072103410b0503142c0c07803981003860b004045105465140081c40200480c40703050340c81f211001c1c1e0140400d9800d5001034403a144a10052002c10000041b02c01110780c04070000412151121100d070030100c0e02d61087c0c8681d082070741003040c550188403001440c1ca04981d03440b510820300c62602c40c200c070016610941c01032800d0000310031ba8000c2c00c046610080e0403492040c00e0903502e10008039400c00440401c2040d800100c103002c00c2006501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 323486294 1250 323485044 323485091
    0x19031707210206010f0b1e13080f15040b070f0201090803070504090b190e040c08010603140f01110405040209030705030a060902030609060910052a0a1b02130c021f 72
    0x1013401403114034080c21b90340f0364010710654003104040d60200f10145280503003180c10b01c402d040310002505944045654407507000d00c040c100300b4015004054441e80701d002d929071065500c0710707004010751561001251281c0300990440150b40d82d40c107061001c50a01409075200e080150703521542d850500c8250360a4a41c00044d8a01801d18210740c2803603100a00d10040907101188640c80495461341480603600c4596801626a540707002000710600401c0c2c1c0340b04840581e014200c814004510110740d003200c80c0c007402032025000c05d000c107120030b140940091141e0b03c07004040320f081c16203890000c0d0901000080848034240d58060701e030214201401042d0740940b28074060400ba15240c400203845107199000681295540c40000d01c498410b11207110440e00354100307001c0e542c80c490100c40080d90100c040c1d400854461038040c5001e65205484615041d405041089035508001d030041c040d2120104030020750244641d038546003484e40b04880c000c1000800c0104031100c00500c0c0464441114 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 323487544 1250 323486294 323486309
    0x5070f0f080a08090d080301030804060e010f021f0603140109030f0203030c0306042a0309140c060403230303040f060f02032802361903170721020601 66
    0x15034104484840810010b035807582200000e550f90745031100003204250b5980f001002c81700040004070074005420058070035202c030350303d40c00d00c8181070100546001506008500040c1e02401202582d80050f0851020125600c4404503003a1707166559600851032007481d584003695600580b5051641c00380d0b10940c0301f41140081c51450802c181900740314880109a240119110185035442c1441c036400c1c07104108002110640410f06c0540042c0a03022505081d03c046880200800803544082303070710400200c00034226460145183c0d00d1a04a48000010480c125510440f40c0110f40e010720040d4030a61046c20400c81385645407402c0004c0766803c681c0340c40c04038818000c0201c2000405e800644080740000031510920b8081c02403406403148101d41420807055070030702040c114020021180c415614030001440400170b90034444501443c40f84442c400c00310300303400c0010600120308000c0d00854250340528260f62600c591076441035076100861681000d021803500d0950500040d405404c54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 323488794 1250 323487544 323487569
    0x140603061303140f0d020406050a09090c020709090813030507090606030b0a060c110a090b090109110f032a0d0b04060621061e05010f020102090303250f05070f 70
    0x581c2c4000300541c4412080c4403402000280c050b400032080b40076a00304143c0d0750b00c1559074a854150092107a000309030020040780c0c480801041c070f01c803c1d001d80c0395210240e0b401403c1e400d2501501802a224191054851480c2000705074005a07207904030601450044006081d000d14101c01c2e103013102c0c07641d4400f00c1054601a000c08041d0398075030320710b802c50b001c42c641420f1601c0d040c10228032022031320190650040b440ba4000500d0981600315288100d000c540014060fa81e418100c000c1d075809803503040003124104408060021070101541e0000d4903454036841080c030364401c845240e04120000400018040703100407a130411030150803600c08069405110281c42c141001e4140c052800d40001400c0d00c09032000509411544040010310b041941d09c1c0b0107080010003901026600e001d01d40c00200503c5c00d03c803005005000711109080007a0056141c100c9140f007005841481061184241c0305040455001c01d84400c2120505401407000d0505503250480003c00325840f6403000d00401e14 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 323490044 1250 323488794 323488831
    0x1020d02190f1b0f1d010b0406112a09070f0207091e0911120d050301090207020f04020d15080a0c140f10080114150702121014060306 59
    0x49110030400e0103a03010340801e05030685850084600d49075460b90000c0f50b00156800540030400411020840d419010312003074500418070445d2001000f40940074840508010412065200c0d81c40c00c1070105524041d2814082c0000c403042d00c03c01d1a241102010600504004a038500880c031541c00c407a1a0a00128880f070124010b51103510310321400e04401c5d075503c400c280c20b00029201c0d1400ea041e510040140c01c00504d49011004a50074500e4007510881a8048a40d100044c2d461509049074695a00b90ba107001080c0b000fa502c1940201d03049565044084003035142c1e400600341110200b2000709918500c4400c40b011880268881700150b80502c0e00c440224181407a25801d8580c0480b521250a0b5440c2c081209441200c040d550090006011051115070041348281600e44070040c4a4540c840036081260b075034107441c4d034503681e540d00300140da0040c94007000c44046900200142c50380549000344100441c0d2005809020407884c0000b00191441c040c005140d11101509803c8420301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 323491294 1250 323490044 323490073
    0x1d040204061205061609050a061106101a07051014060f03070612090512030709080106050901030c060804112d15040608150306010902040501030e010e1b01050c0609060601020d02 78
    0x4c0c0504281c100e030018041c040e05007842419010040d00011f011018070715035403135005000d400c014840c1c522034000d0801050b0164405140b00084a9468a0300320f207100000c0300504031603000f500d00f103400d0300ca218070000d001c4109010351012404607008129903460104240800c000c080c10000388280c000d49000d00516800082045105408030340c00a110310036031a065103890703581c81061042410110402201952081c032031400d40314003100a20a956550090244007442030100a003006610f0005026807840f80c0403490b8410301401810410707400302c07408229150442000400d2824a0300e510091050900a420800c0f0209640308002ca1040c0c40e00c1c00a030b800b49002c3c1d1401c101c4a074000c03408110904c45144402100201900c0c0256502c0030420003c0d40941325540c0880c2c14401346894410042c401c04051485c0721020303092044480d90100b0301d142c10400f03114103101c0244501c0c1003a002c100903292081d60140b000b0203880c2402e000192074080541c0c0700804543c420084a030000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 323492544 1250 323491294 323491303
    0x10b100203030a0b1c060228020d0f0219030f0e010903152f13050909061801151523090d0f02030307110a120c1203091d040204061205 59
    0x40b80003e0f1404104e40040c44480e290851909090341c0c00d40c408007880005d40c010203450382c3e00111900c040f50700c1039292519040941c54400960000c0c0901040e49028030403e40b00301101d80b0513500d555010b02d01011000c01d904c9016400501240f4058030506d8010701108104502401c00d645400e10b940e841c040341d80e005100c0c1e00c0300329484030001111401c0c030a2408854400d20110304501403a4405034400a030000a980c2016001c20f0742c0001d41400c0c0b0b01d21590141494102034650340e66009001a50b005100e070704021950b5907183c2c01209400a0060b142c06000501c4060034840d191280052019a20319080c1c121403400400110b48400203000b21110281c0954241001024508045480b94209040030b50907010015514082282c1d0241852010500f140c1c9084043d440718180182e403400301c40c00074100d0142d800140016019072000e2518640700740380500702191100b2191941004900744038251003408818881149000c0c01142d0103041e04d42070511640c0381c19181c1c250f5a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 323493794 1250 323492544 323492551
    0x1003050105101a0c0106030f03080415090302100507090815040b07051606111303061b0807021011070804080708010f0b01051903060302040e070602010b0409031e02160e0108010b10020303 82
    0x42d0b020010384c200c104042904104001c43d00640078880212207410003802a0004503011078074482910000380031488248100601280c055005004110075071140e9001441c1c05040c1381c06200d40f65100142d6035200b003080d50032150303080360300d142242001e103000e041001002d002502840700a0141510100340002d401200ca50085000b04e001811096203981c0c6e407140c0f41404102155a040100902c4100c2e0090740e00000c9038480b059030a403622204907071880303050312610b0042e0404030141040c14800e41008030f0448441c0c030090328042060b92602c03800d41c020703403240c043d9421060003041105d800b8403501d000ba103134821060140f0800748000038482d1242c0c8028080300c942c04007142d10038034440ea20a40c05140d000d4010008681e5130040656104030a1040a0066080480e0142a0300b014007a0307158056054940c225201c0460702680c3c11402c440d0a160118443d00c2c50011782d540c50018400014141903214840a50510003281d0940300410500c5010b100910765010040f0707400401c40e0303031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 323495044 1250 323493794 323493839
    0x50a050c120709050307170c0d030e04020705070b1b1c0c1203090609080904060506180d141c14120a0f0e10140132040f05100305010510 60
    0x3a41d4940c801503a1100300c07a0401030b014496810041f411103000301d640c0e941c90302c01c00103c07601c8085038410002c1c980c58030003000b0001180000e2040d80d42c2020380103001e00c18880c80581e80115100c503020350064002103618402c584424400140c1100140014a4422141050614515203400e0058010084e100c001400c107142071804e80c40180c420b40c04030521941c003240030701602c1e5180c20b0100c500e8110603441d501c901d281c510001402d04d0004d0441d4180c2c0c0300030b05141c403d41482010000050344a081c2038400282e0f03640c0100d10f04105004409820790045501c082209503007100034107031411603900001c000410040360705025070001405a04c00b102c1c07100401e0034034480c01058081d0a001004000700d00c07a403c401d5901e2074440e08915130b0040e000714070314904c1c2e03070350b500f81d42d52100207003140d00a00701f100300c0d0482020208008080d49000181011404e98000c100e4201110000c803105003600d003c90209000304074003070080d143c001c003854078034034400b90820041320800c0310300c2480d40a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 323496294 1250 323495044 323495077
    0x60705070f0b070f02104203050303090c060901050d0b150a020106051e090c030a0b090f04150203010f050f030f1c02011104060f0503090c0907050d050a050c 69
    0x20811241c0c0140020a5501a40d400b2850a0009000d00b1130204e000c0144094010301b00041c0b050203281c4290500d41d21403405244c14502004403c0f04145091a081d19102059050300e926081c21640041c0c001d40c4250001c0d5983d00d040d130304080c140300700910310a102d82020000b4074402d070784c0801518100040108001101b00800c00000c10340700c0c5c41202e4030214400810951181a0190700420480e5010754440300c1445040402c40240100c4440095000101c4004140300e0003d100245030301039550080020404001c5001501d00c000840c0c5190011015038100301c10006038800007030f0b140420340f4095085504002e04150401014000c60780500f5850007075132003e9504100c0030a0b502c1110080e030b40c00403a05c04110848030040f01e8420055820f02076440070068031502250304aa52650341c4121905c203a020440e1158005880358125100300d0401016503078030050014020070803a203c40b80d4030031080800b0010f940780103007055038841c40c1c01d0030804044c6005086031300301800d82c00b100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 323497544 1250 323496294 323496307
    0x10b0a0b0c01140901060311030715110a050a061a0108060f0d020d0f0b0412080702070b03060f04050f1b12040f02120706020a03111906020c10020d061403030c060705 73
    0x82d0042c40305141030082442804140010044194000c0c0c0582c1d0082488030784030140b40d020b06549062074819403240c074061100715210a44504141842c0b00082d20903502d01c11029142c151800c04591000d9802643d40d42e0980802100f4219048050001b800d11030800d14101c0001022200d80c440414081d0f1100000b4004540d01c8108042d8111340c403400b25000900141000f44031000121012034070242d0440e6912402801240c0321445401998020f102807818012600580d070409045190044215025901181d0b103502806114140240c00004a86091901c0107010800005407040c10081000302021381e0860522583c3c1c041d400c05043c00000c8502d00c045000d8620b030460f850524043d041000c40c00300d0b400b0902030032030381c0039550341740c3d50349441d14480f62240301400d61541d80c14403113540080081c421350044e290603a0032405450407800d152200c07009980c040820060b00596a803018031a000402d1202148914140d00450070032805c0ca01d019900c0c41c0140503c0180400031825 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 323498794 1250 323497544 323497567
    0x21e0f0d0810120503070201091d01090c0c1202100c0306060801090c050f0307090801050a020301080a021201230103020a120503160c03060e06040c06020d0903140102040e04150509010b0a0b 83
    0x902004000801c1c0d4580f0030708250428a840380c00c1248101c2c0050028140080d80025030b01d0003004038030400605080e03a0f441c0c03d007444018040d02c3c4d401011b1006c8101141c0203c0c001002040c02200d864025041c4070101d0342085044440341c0484005051600038203000640c1e00110031410344911160000c0c203c8121241543c0a00403482904038000d000010016280c1d8007501440448000c0710007409141c40c0d134542c01050380024010000e05901100da0365025203820600607012100c040700000d840b00380d100c40200303001010030407503201c1030b82900100114140543c07100d00409486440084010b01a62115103c1c81200040e22802440300b28550604c07102495000007154044010000c01892808030740d199881100d0030fa80106400400160580c00811526501c10003540e401c0d9400c0e003035a40706652100c0c0815158910365003440007050001c8001d103002e01680c01002c182c10802ca03820b01c07640690764002e0103040c0c6641040c1c00ca58654580c16220400d1f00c07480e2203460f80361500b0501c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 323500044 1250 323498794 323498821
    0xe030405060a05041404050c0702060912010510060806120303062e090303030e070803030a020c0f0f031306021c120e0604060b030c0105070f120c0f03021e0f0d08 71
    0x100941c4094001420101141c010000307100301c81e804010203e01441e02e00070032044075030488200b14200001c0242d0801841c01a009000b4488000c007003031500000051100e003190801c54601c2e601000102061002c550081c81150780000101e50028280400851950b1280000340425008180c203030441440f045028007104505010410701e501580c0743c0f584d004000169500c800e8002c0b03490103072402c0c1c4100002c1151026500800001d51468452941e414002d5020a0381260b070390050f0441c0540c2100c1c00e00c5540e4035052000021515440041020b0351040d06540c8854203560240d00700d0007a44520301c51199000409061410706460003124400c00f0385013211100141c0c2c01018100810006139900ca00d144400070350840700340c02152001581e0f503115110f00501100c0703c0083da24005104402d01a21100b01407034003180441c42c03542c0304403594400c2c402c1240540c0010210b18543c20920503244001c8007203e00074401c440180c8607440c0c541c00c01c0200300040000a5000985d070121844 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 323501294 1250 323500044 323500049
    0x101505071401140108160302240c0106090b030303160507020117070c0606050d02030c0f030304080a081c05040f02040507050f0a0909050c03190c031b0c050f1603060e0304 75
    0x20940784a99880300206000300b141481034441d0248042c000306022100003085101c02d01d0071640d0f02085829502000081745080102c180d600d1111101100000d11000c0641041d582c61400401c00d00d003002c00c24810b4802d0344000c140240c0c01401049a0241641a24084440e007403c0065440303865000403540810200540c9040e80ca2040c1480421344e408209007140601031003040250365192000c2003440b41c41048080e5065010488100e418030308000c0e0824000c0004003168507080e515903a060525200540581f007201010900303030001c042a02284201c0c004d0000c080225203011342c0e1740302c8600c801103c064019540c03100081c459070301403011075030b5808a9030350381c44e241c03288207034010035400940c00341c0701c030170360400c3c01041c003054010781070340e00515184981c81e1400219121031002070480d070000b6810951074a500030f0150b55810a0003e55200550b01d0a90486035414480c5c50140000d440500300c0e0f225854840030043c80c603a1840a41750301c46004a403e41c0c1710a0582e1440c0a6038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 323502544 1250 323501294 323501303
    0x4020306100c1a0103120908010c2a050a0302030d050c13030605060a09050118140705160f0b040b0f0601090303081305010605060c03031f0609050f1305181510150507 73
    0x83d800481071042c0c13881500c1d00701c02503035582400c07203880340072481c26500d140e07200101051000406521101c903c034140f5150100e00711074040e0120143d1202031403e141d030300065000d40c000103001902c00f1418094544d0051101d4405458a900310b1143c2080b0b0426100c0500b82c1951440860019038446071482c004158000701448956151303080c00d042440c540c200b1a02c810b1419650b031a000a102c200d6074840c0d1501d495490518002c80c6603001c4008000c0001c4642c110740b0b245010010380b2200c03072540241e0061449088508c0c2c480d40c401116030b40504a281400f07500f203c1080044d900904655222044d1010036044d03425030b00d403040c05403540740c01850b880100070520ba51001e800001540c45442c40c00b44101951022031001c0901c13140502a480005003d003805211a080c517000a545a180c09480207605225813070b030030030480341e0a03a0840100700c11a281c80c05020010040c106400d07608040d1040103091a040c92503503444280302d180c032006000c410f040c0001c2d00450503109140d400c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 323503794 1250 323502544 323502593
    0x423040b03070902030106030f050411090402060f12010303030c0309050606040e10110702030c010c0b0604021305130b0102060108030f18010c1e021801180b04020405040c03061404020306100c 84
    0xf5a6040d4001e5002400f40038006031400308800c900c0f902d1070040501460b00894141d50b608480014004100700c000d0050382c002c1420894803900b01110b078005c28829a404464440d0795045140007025101010140070406050000c84408501e000c104503030010801c503800101c032104251140e0400f000107a07000066803400341400c03101c080d20340081c445148210266800840103100554074841c0d00800942001e00100004507d41040c1d402449801d464000c000080c968407000a00b102820040001145803220303440c0500c0d50b010444140508841405103041c080300844403c42c6000d1807404140414504e990a08240d005e0240c0084c1160400300700c040f240301b043c034200c0714143c1302d031800c07170013140851134140700b02d5603800304581660b031012000c04c0c0c2c9104020541024100440c21658011b500f08000609a52a84101c07144000e480c0c4020404c54984606078800321702402c080c901540c01041000465951000c3d001003845070b030306000c400070801b81808001000c0e030101511480e582c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 323505044 1250 323503794 323503799
    0x1a07210210020d0204180501060f081003021021020301050d060908124006020315120d02060c0a02120705070e0414010e0a03021b010e210f030423040b0307 68
    0xa03d41c004209954902d00c1d645a20300381301041d0b80845500340309a000107914034001102e16803207145503540103580e24141d541c0b800d440e034002030712004200d216840840e801920302c100704000c01002c42c6428082c40411800e40d8034106c04110040703810400144015030f01c4442804220014040d0345002a04a260031002d24204144075403018000240c08240340c44c004100403c080080441d10714000071210060500559075100c40113904050803590281c00c0c1c0100e88110354540c4620020012502001400d01c10800d07100030f802c03d0300c054680103150380208a2005d00340d40000d24074400d600c00d44581e5039100054104642418181d07002228420210340c1030000780700902810a4100e1030213002009030b811001165582c4401c4d8420003005a08060030300420690786440c0700581c0c20040c148440c500d500c000001d1040c00c03c2000341d01008407101007010310314004010811103111081e00440ca881d05022080d90290190300c1420814003017402c2820349600c580c0c1000b180000c1c082c04032003203641c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 323506294 1250 323505044 323505067
    0x1b0801050603160807090e01021905030a0c1e05070519060c09060804030c0206030a060317040f080601270b031506151c020a020c09040c1a0721021002 66
    0x101518601c0c880d01c03800440d42c0c83c0460002c0c0f24030407140b07400b00404405142034000000b13889039000c2a60155400c1c8082d0300780f050312501103e000c494541e02c495480c03811107021421105a52000e0081284c0c42100207201c91604d401c0700040420fa0800680300d20780342c604603240c20805c403d4400c85001404e000020400540c006000c00c41141c0c840d035260585503101260407600885010300012240940500035041400003550071211416001c103102d900d135154440c00ea020041060002d000004d800c00c800c4102140e000040c01c0c002000e00001d514003e90b540441c440a00407064210750307200080c080c00e03419030003111290f8010f403c1d90030015010b045000c0006007112810b016600880c00a510380a9448c110390012110065070103010750640074007070094000c3e0309890258030940c00b40c50620356456001611481c8035800c14500541030404403603941e88030b000303c0301d02290280310000c000b41c545040c2003507040b00030f4001c468030614080c0407481c0c8144105009020742c400a410316400c2d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 323507544 1250 323506294 323506301
    0x40209060c0f061b0a21020d09080324181f0602030c0d09060c0b09031204080307120b0105030f060310050a060504060f080a02150f0d0902011101060e010506071b0801 73
    0x700c01440e8141d420801030041e80d0f004d80308800ba003000044400b100002030740040030709201d00841130607006007800901403012049585d41202614407903c040204510aa024510564400c682c140103005240565001c260705261704c0720038440490104002884505034a00082c02e0720385000c698224180d03035282c010f51607501006c2c054042c1e0080784140c81031300d8080c603a01c8045801a40c1d441005d010749880d80c0b44081d1010b090401d00f070108000303e200c403151800000c0e00030b60243c2c1e01a5628148002c3c06000b502e0421040719415003413a0755410035a070010180c0b1380c403202c000240110395440c940064107003000000076143c100d180005200400000340c1c860015120b080e03e0400c200c0741c681c614000c000c9841c5c4140905548001440c40050074181c000c00020040f400780c4904240c0415201d12140d080b40c0c2a01c0c00041d0f807001110250760b030142a50f04410b04100c02004828100501d861000307505009282c0a4000000c0c2c0c4404c0210003002081950420101c02c040b0039240d00100b8080e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 323508794 1250 323507544 323507551
    0x30a0b090a150501050d02120915071814030f0a0309080115030b04030f050708071203060509091203090c0303031e010e070e01030903030f0c181a0702040209060c0f06 73
    0x4180c1040010380c070542920554001c20401241e28984501c2c0c4001100c10350b204405151980e0b809005484103e4004001c2c54001d401d4a0090842c01001500703d01c1c428000800c18010040c01007041d400c401200d41001c810790b4401c43c401c0107800d0001000c245040c903900c1c0010143c2c4100d0314201e0602d80d02046030300581c0c0c04400244101c00e40007401c4000303e0031a01002d4082c004a002140000c0d0240402c0c400c210700c11704045046c124203842e6441c154105100980d0a60548002407840355490302c20341d40509800c88084415007028102e00d50384800404c4110b208220000c0490b2a03040108401d02c40480300034112075907131038400480c4038a80035070080000390144107400810302c02e41006890f40f060071290380d1041007040d103200460180000180030b0301495500c031141c40d801c181d2400349411319000c54a5000c0c1c40c0005040d24981d03900b080d8401900140d114024055241d004000c0700c98064040301e015071100b42440014202d84030303210104201c1d1040410011402c9404280c0c0c511 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 323510044 1250 323508794 323508799
    0x15060509060f1815120601030c061103070b100909051e06070f0e0f060a0f120605060f130509161407021503040c03060501120212011a24030a0b 63
    0x850320780320184040440c0c90140694004841040d0b0403800640444666104051100540c4404d0703803030380828041001d02020520580000c00103105020340e01929200a00c0c040c038200c1c00078602d040915840313014444000380f460550101180100101802e0980501007491013040f00450502d07005540e545010042052404940300c174070188039001c43c4852103407081ba2284480154042011140200c518040303542c40003c1c18094100e586036103001d440404195141e85d12035081a000240801d2565617070300f950141024024061521454165030079041049403042e2074000300d088940c004110798011582082c4c1540805c1300141d48403d4000c059119911206004031644188008520400304081d4128000047c030150242c0d11600855110b4000c800b0b811032540c4a42d2248162402030303100000000d08920f040c0198509512502d41c0000d075038008004a800e1360b0b12144180c5200e00080c4c0c031440e1070039040810145240c2c01d071150500210f0b46640e40e071609410020040460b01206030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 323511294 1250 323510044 323510059
    0x2040f030b0604092301060806040609051c093b1e1303050306040902040e010c0e1806092d010311030f1011040f14190b0301061b150605 60
    0xc5030740c1080d110700c074003482c1c0020b1651883d806055440a803145d4002c0d1182030740d0f40c0d0781c80c001054802032243da40168420000403c0300591802d18500d0302c0e040031000c010341c0c0541c620f81200d9a42060806040b01c80f03c080c0c039042c4803059845844100032454204140036040000d88814484006e0b200d0300c42d9510505100754241d1803555041104c000f15020780c86465459481800310380150080d56018500030400f103096242c907400f00d0b094070504420a10940c0d101e441e542c059a4100e034455a403a01c096460f601d070b201c03040e264200c8001000e00f000740280c0341403011680c05105101c081c4086e2960010420141c01d1824403910314080910050340d910001641590743c1d031070042515010410000c00a01c1d524492048010041105046040746010300b0000069840790304200c260081c6003110b0401020004081070141c025080707030740c80c00c0e030314401d24080c4070940300d6506490541d5000d01d010321900402c980714034580e2106100107001c0318038071800a10104e0007a00440207a0704142c42c0c45 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 323512544 1250 323511294 323511301
    0x403120f02030304050a0204050a06030f0c05040f0b0904061107081b011107050d14040512010603051e0604080a0216090b0a0503010213140a1d0a0501080a08030705030a0f02040f030b 80
    0x101d840c2c1c08159130051a41d0001e01c07901c4007503d4141c118980015480e00300003112540c99440085c41d02034088101c6240b114a40d0030002c51405101c0e0720040c910f500400d12074900014005103105600520051080f03603150101c40045c803000041e80c03281507010503c0d55491028600ea4070712000c40401c0e405c2c10b58280b94204a540080c2000d44200c103610400401c015964000e060380da100d0041d041c40701c400014040012559603503421911114000000001d030316041d41003503424684244804039200010715050b80c540100020200d81c019005401d0940341c0c055000203e042403003482c0601e910303c0c18500b02080002e025803091030307040422282c220101e6580c030145802e0740034110000b0302c5424090810890002040c4407260223520060003040e1035034650340c48159040a902548142c4030031041080040d4030188200d5001d08100d50062404481c103a591500610004020f2030400801102013200b243c0d03203803c0344041482c044415900c40b9101d400d240b032000200d12041c1d5418040c1c1c00030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 323513794 1250 323512544 323512547
    0x100b0703020714060f070308060415090b030c04090f15091211060f0108030d0e0106050604030602030f010e060319030c0b071e09050904081b1b04110316030c140403120f 74
    0x115008800c1d6590511b04020090700c00b40e40440008100c0d03900700d0346a0001401d180d62040c006000b40c03905400004030309041c03000340b5140401c54200d5501862809091202040210b00c0007000b00f940441c0b0400d441d00d110005202401701c62030000c102c440000c0c92803804035007108501005042c1c48080350081d5036074814081c003022007031040591a400c10407a4080407101500600c8441d070f55a4004035081d66550082440c56115510582c2d90b01ea000c001c0c40110200301ca0704500602c1c0010a042d52820f2140000f929401750200c1110200341c94400c0c101018000c06412146a070070280700105850a0a8081c0c444100201c403680c0d03602441d000c8000c501c0c002c0140d1002e85101034400c41180d5556960744220b40d01c0300703000440c2801d0313024508203101b204002941501e04408921000f0303842e081300b44070030750301c82c40c6403100811001d204006000c500003401d4004410240790216401c581070300291080b01c0300d01c010b200320f003400150100900407a0540e000c0001c2403950b500306000b280c0e000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 323515044 1250 323513794 323513797
    0x210020a030e0915090f0603070f03050c0d0611070f0215040602070510031409030403030905040b132d0b030708150c070c350105070c0209100b070302071406 69
    0xc0c045902c1103014052030511881d0b55601810035049540703c3c980d80c1d000950316140484881c00c018a01368200000d0f0301b4240908401071800420646030f8608550320240c503906500140c138012210113071160140600b0b40c00426655200e10109540c40c1e115052a84050304201c000782c1c0513050100c0e008e8000d8400f513040f241101d001d9400381c180e02c0d0420b001c01100503107845800b020191240c2d00560080ca20002d11801404080d00860b0b65910f5450301405482e5030b80e00a40c41646421840303481600c442c003040032000301801000900540144101e015003201d05030740455028051002100141365034040420004110211000315540301001da503200f007000e42090f2000c0e40880415003407942d1001030030342d1074441c080f87c0882580f0355104c020400c19089030341c4101402000e000c2ca1210342c85110507c08035002000384102d103000f28018111544480c0024042d207e00b10000c0c020b000051002c1d8003501c0d1390742d003595491085043c025601c0d0385902075508007104140c20640e140c9000b20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 323516294 1250 323515044 323515063
    0xe0a050901141203070209071706060f0d0507020703080c030703030509160303180911030103150b0f130902040906060509090309030604030c051e0d0e01091805060316080a021002 78
    0x260400302c840b98207428441c032202c42c4149221507200520111005035900441e40c2d00c030320940e41d0b800d00c250201c0700400c640b91901811150003040b0401040c0c6210401c181186c00210740e03000e0101d800d0711000c0040745801d01c1544081e028841c04a0f010040386da000c00245440e5001ea5400e0000d41c079920141500e851203103d202d040541ca6070010400a0b0003165a545030ba074900011440080d0b4440120f419900b050b405100107540c00401071040145e120002036a001c003028040120381035070004a880300c114103481500c280580c12010004111035003020240f04d5028005001000640c500703c006021607004843c42180038100107480c5110000544881d40e0009000744a140c9807a1000d448500c50000203992500030841c603580b1290700c540c125562012030740018104919000801010300d002c00042c1410440003002c10094a140c1913501170360241ca01c0b2001a440e10f9940c00646000342e0715003a48030b8160010000240c0c00804038600060314001e40e8040900b054034241282c503083c1d840e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 323517544 1250 323516294 323516309
    0x3150a0b04140a090507020604060507020118020f030102071406070207061e0513050301020a020c0307060f050d05070318080a08010b03010506220b07080d1b0212030709030f030e0a050901 82
    0x1400100400b01c4031010740e1460980103003240b032200e92030300240d506039402111401701680c0a8003e0100700310a5206459001d0280e100800c00c0c0200c21500055420701804040e05c074a8485201400c540d03400e50440341c0c510750140e404102410011019601c82204650800241c05858000140240079a100501501906a24481025030700c5002d0342d05400c449640e0392102d2048401250300c3c0c13000d00c000c0104070100d400826070a00720314100340c9081525000081000790f4011703542c10b0300b90403030241e5440390840d1070040b07069038070941c08400419051280d09080b6030301440f0101407001001c0100300382d07130311580d418200f07a0700d6030320070b0186210a00c926500550104201c092440c20045020003000803002c2048100c3d07520503c15042e80c200c03d506481241c1e0000b10b40c1454180c900c509035480700541100051020310380c901a45444980c2c2d280f0703402d0000080000d4078a07215100500107550f1000d4840300625060400609402440ca68140580607205000c0348929084400d14100c9040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 323518794 1250 323517544 323517547
    0x10906082a0301260123090a12120e070510031d071706060a0510111c0503042f0103091b0905041502031303080903120103030503150a0b 60
    0x15525101c9014941c40380012800c5005a40107800c1c824560080d4020020f605520300c003003098141d019110002c0c0c2016a1403a03260000c0d090440740720183c520b405044800c40d0b02626510604c0160812007400c500800d05108030071118400f41e00403445500e2201c02c0c4100300882c0d140399000030741d43c80d000c0c0600f0785e008104510756449188aa00178510451001126078008410440f00501e00b80341600007280c00810301d000c1144420080144aa020000b203844400961800c80421540849010311004012900d07240d80c80b0000100941c555a49000650f01c0003d03a40400040c840c1d0001d031400c4072606c3c7c0704180007030207403203082c60038010140380d405020620b4500d01c015401070001800403107050400804100000f0b5416101b000141100d00f004100c03850316280c80701a00c11500500c100c0e082c811300500400c1c8041d000041401903160a0100180e11102d8020780341d03004900502c201100104008010180e2080266019010034000070000003036040c200090b0310004e01450b0142ca80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 323520044 1250 323518794 323518801
    0x90c030e19020a0b03040f23010b0303040b091215070c06050106032d15030f0204060608011206090c0503010e0d0306080706170c0418020901180b0a0c020301020d06080c0f01090608 79
    0x1c140081d6045481185550000300ca10754501031640c010100c0c200805001c0100000c023a4800c4c020a2032014046010710724050604003048064080d480000340103100300d0915070346c100420402810400050401d034085854100c800501e500d80100c4210760090900b800064814081c1c000d07076000c0c001c24178070b502030030a8183c50700312541301002020055680ba003042590580790040000081c41c006e041e1a51180c076180180025902240d100804101075140100b004d00400c054914034558040c0c0c00dc0303200707449030412489440d69900030591651034a00c81194aa000240f400c0600c0455101804915500c00c08982c0b509498482e410100e0b18612000c0b100d0b000fa400100d9000d00400c1a05042c99154011500c80c0c0392041c3e0040e05060740082c0c0c0d19031940c0c02c040320389010700a402a540c60a41044101480c4d801201c1c04403041c0000e14407c01d0071580e0a4055072441415080c080202d50798842c0b1f1607030385504100760b41d4020f10401c0d4002e81c0a51048031501c0603501c07607889200c031685 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 323521294 1250 323520044 323520059
    0x40303020c0f010516030c050d0908030307050d020d05011e0605091008090a0813060e0a14090402010c0b150a05100206220609030918090c0618090c030e19020a 70
    0x801180002c3c1002800c01c004c9440d80c01c0b01c01480300c0980603a4072aa6a03000ca860414941454540700c0d00c144046031004000403040002104d80c0a1190b1400350786a9092882110280c080c000c0c44140d03480c10300f00003050205500028031b1302070036800020341c121075030b9040544940c8100452940c100c6660801c0510450248404c960040d000f03104880d00112540c441d0160b03074000b1814004029aa18000c12500b0f500001000d0031100840c1d500d1541482d007444841e010001c0c050182c040c4650304c00103015a8041e015802070503400011045036898081e0180c0c84100c4804200f51242404107004100d609045840d02064241500107040c20b0721201c83d000318418400000c01400f010310200180058400e0040045041c40781c0c42e10300d010350604844001c10111650340304111450309640304041401c043d101c1040b224581025815031031032000d0800c040140d90001140e01b0308008141c0078803036040d40040303100007202d13098604501307490640d04c040f03808402000c0c4d0701600807007090040c3c0c1e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 323522544 1250 323521294 323521309
    0x50906120309040501090b18010b0307030905030912070f09110306040b030a08120115020d1e030204170706020c0a0e01030209220b100b0a050f13050a030b040314040303020c 76
    0x35806085a00b01800d900008054030000d801280381c03144c460907000010305140000505201b00c0b55000d00466040c080251414000100a20105901c6100e1003041c020240b0855042441c090b02c2c0e05c03800c0303442100c1c1654a01040c4900c5900700480440024a081148501400c04408018061554441400700406031107001900381e4140038401703003040040d03a00402006c030b1410782d4540100a614000052a9112160b0725400c15900720140340301d0701c554882403d80c1c1d800d01c1010790700a07030030100f04110000d01450b0003200d11600c140040900f043d100080c81e5044503455403c84900302818030a21003121410312560541e03440c60310041c0011703c0d2003402035901c04165481e000400c03e5841c48802c4600c500d440c16514400c01d003060000c20415241c03145e021b0060081c14a00d00007409600030240d02c90b01101007022040801c02d40848041410342c040100700003810303400c030f4035141e040c01108400700703540803408504400d00b80b681c6201841c050b00c0889030580c003e0044020b140c802e00041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 323523794 1250 323522544 323522569
    0x40302060702030708101b0e130906060f0e10060e0319260a020705062a0a0506010b0d060f0b0708070201030b090a060315050103020f011202191e09050906 68
    0x1d4040c04c4404280c22000304108210a040400003045004884c0c00b00740042e00c800c0004020081361800031081615002c1c201c1589042031f07040004d17440d1160030240001c00c3c441c0c01440c081880084005840402c840b0880d0189071300398590244580d40e5841592400d00c003401144d0160000c082400140c541340410301c4140b801a00c605c01080e01d2009030030500111004041448003002c15025800c0c1d90400c000c40c050441a252035280500b042e4403050010b480e901404544c51101b00c204c140d440f42404407000e071540c400201c40623540c490031040c249402c50342103c0a040e1070300ba80003880400d14650582250115140d0500d0a2165110342805910031074040c0d050540304c040011140c0c4614030600c0c494041ca400010307000e401d52411015804403504081c000307070300341001480135a845000c5444649824240220040c0252102c900a8000c56007411041040141e0080b440c40d003240c40082400000345126610855825041d07030110140d01a080e001080240040d142d4240613442020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 323525044 1250 323523794 323523799
    0x9121902060618010608092b02010b03212104111e09010b0904090c241701050f0d0c03051b220e01020c0106090b2e050307050c0a0c0501090803040b040302060702 71
    0x84240d0300000050300c41344070301e20f0f04800c110201100340d4689d081c8075641800c4411006011000e081d0701c00300a84c1d00350149500c0d80454006500d076210492001c2ca2480da03403c01200440310325007400e010016004201429000704840c0c4400002079058100c00c142c03880340100080c1d180d034203091081e84542c008901d12a04503a46503d50380100d0720800800b0020322001c01c02a1038580d20900d01c03a02d04050000c004280030901e40108600c080c0300802d641920710a0b1003483c51142c03010f0004400801d00309002d003c10941e200d01009001000c10702c8030029000d402019440b80d0080d041c000f101407900b50310760400720710441610100e01c503504500c40f0b10340d0010001d03081c400c440c175405003142c4055028400c00355071503c4030011740c103050685080c00002101d007000c1101603624150703c0f9069081100040040c000f00103010140660181c503008280801100e2440d8601d261050040d00c0714002d0a0104441d000c0020b948200042101c05945d10483c065051900d90750900c8100c1d00504d50481c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 323526294 1250 323525044 323525053
    0x11250c122406030f120216050609040e01110c030d0b0f1e010e06130806090a031b030302160b060f0303030624040e160f020a1205030912190206061801060809 69
    0x41030013400c00600e440d0090072106540d01c50000040e142072001e055405900c0408070080003155144010780e111501d00340c07004151100d40312081401481c0705982c01c0d040030340c04221404288000409401c180900036020044800c00900300702c0c075103502c21300036030740800310040000e4090b2152a1800c034001041c101848001500000034455401c020199819952810030410010104200d00da4100301c0380400b51441a040da03c1c010110843c030850208000d09003850407003090710030b9046584404404100c0c04400186203442d20a500003a5005841010014501507a0389030110440b405900c00500c491011001c101a0781f0515030110507440c06941c040c0000100c510000503407910075002d0241c510382c05020354601800c18a01c5143c0c00e03045600000001d0002504020015000241400c2c21502e958070f00c12030920380321503200d400c41c89140c0440d00d12a0480440605003400441d41c00b61095a03550038207001c90025a0074149070090803141c0104040e501a15903075401419100564 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 323527544 1250 323526294 323526299
    0x60902010c060509010b01080f0708041407030c0e040204051008030d0c050c07090905250e04151506110309030a060914060c070201090b0306011211250c122406 70
    0x1402203070400c59134071101d40d450ba01501c03071540e402541c003548980060512071481c02c02000c010b006600040c40241074651031103402e8202c2c001000090000c42d84100030300150f6454010f003148461041d5022406241010007040305600c810344e000003030f01c803008001e504003508007088102514014a284d01481010440380404d01c2c000d00603035015115101c40482c0c0b0007070324502549085003405441003212010007100c03c01005003559003084a424241014854031607061940d2407105010315548106d180c00c0c0c0c41c003650343d600c403c0c40b0120f848a451300c0200303107002da041640300c0c407500c901c0b10303415000821b200000a0480d48080b122038010500c9000c600240401c03a031400d101914401c0d20400b001c10000210341c2d110007500050002e80b000703142541003c8001801409802c10708805113a10381d1140040c0359684020744845059881101c0619a01c0400200c02e0440169040d14081c80413403011501d01e0382038101402056001c41c0068000090648520320203064502d070074005916503000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 323528794 1250 323527544 323527553
    0x90e03181026070e0904031b0c08010219110111091e0d05070e06100c02010e03160b030118090302070b0c030d050403020f1005060d140f0a0807051506060403060902010c 74
    0x8003182d200d0100300301d4460a0160000c1c2c40411044509403042a0407010040003c0c1e2199000c0050310a04584a010040d0317840c00d640030400c907800a075045d40c400f04080141f04040c030310030181010b458440c5004210115540c40c04d80b0700440c404060300d2420031900c40313141006d6014965802c5590003600b1040c00c104005120b01d01803500941d0705a004080500c007440e85034880c190048803c8a41003c0b150382001d01424060040d0400703410b000b0300101e0700381d007518140440c804001344c20160249640d02c030780c0d1030321040d0400e02a81000d103107a0030082c0d40c1540544a5100295010b80043c052145070103410b2442d50f20020710510710380400e01000c1024001130123420b00803840303038024082c5a03500b1000c05162142c0a4a00b498250822052050b03070f449160b590055607400c4046407044c5240182c4061030301c02819580c1d134061003140305a106104400c40a000003910a80c1070b070743d045541000d09180000705540040d48124100820000980d41d58810849107106040080f254a0140c03107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 323530044 1250 323528794 323528837
    0x1410053103060510050907030f0b04050a090c05030102180d0302100f0f05060306070f0e01030204050a0303020c12031e070609050717010c1d0603061f030204090e031810 74
    0x10160904a1001014000c0041d00c2c0160b44d0321020403408085281c0c60000060825540904401c05043d0745d01e119164400150300303e040c1810000c0e10a000900301200480001d2800d603d054443d07030480ca8001c1451b140c103008aa01d507601c07140c040c030700b9070020340c3c1044440c0d10b0b9004110150f1240004400309407080d40201032880a60450024541810004034400d55000400c220b102c4c3e040902084000b64200c8801400303940c075031030003481c410820b030010f800a100d0351704160390040e091000001059400194a46102410b07a4000e24000055560903500d010ba011400840e4113080025606400000c0240407814005d960210306c1d092642c4800d8241101900311200306040c40206c0c00b840c0a090290368591074003443e10341c0040c101141c50044094003201c0c0c69100d8080017012841654880002c84001c4100143c501c039240d40000000e00254082c0c421140c83c02e003000c120080c10341c40802641c181000c24982c40a20007620400c000700c11002d07012070001d1004088800e4413891070b00c04c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 323531294 1250 323530044 323530117
    0x70506041b0b07020901091a0307080c01020f03040311060717031f08070506030105130e030301092306090a0914011503020f0d03050708030a02040302120610141005 72
    0x840414070110245a4070924074450b0708405200301d4100311001c010b0b1a08002d180c112a801c21001036541000700d0803000064030f40040c06d91600c200d22020405803404034008800c2182602150308403032007000c00301d403240690312003d85158081803285010781422001041200c1c8252000414480000200c61481c0c00540c0c02d6002c07070084c9401400d000441480c00343c0948240c0004140c4c0b00c2c03038000011314511050140c0c2c0d0159a409249080342c0d80d480e0080580c07410300d0003d607030300e80d0b0715811094000e08103c415003141707240840031000c0100307032801ca47d80100f0015003d10090354400c2d409c0300203410410012190742c20f03d0300d03074000140c2c8203100e80342417000490050691240303980104000400d200c2c1240c0e1044640d911030400181d044402c41b00e070541e008107182d0301ca13594403c0c860000c0c05117074000fa400040e10320982d00480b030040f90840c401c00e104045044101d48030143d66a101c0343c503600882d085a1a150503484041c0500050240d02602e0b01c41e648000808103240581d000d00b60 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 323532544 1250 323531294 323531303
    0x30206070f23060601320d02130e0a1a0901050f0a030519060f0501060c0f0c0909060501080609070303020d0c110d05010507020706031509020a180f060207060c0c0608060607050604 79
    0xc105000d86581c0c0214054040004218075046d0f00d80701d8080c042201101c2203402607094400200074007040d110f501910120b010030f0600d603c0196460301c082400341c9040795906041441e0044265440308100388541c1c500ca0080c00c2500282e080400703001c030600d4103030540383d40501440c0001000960030003601c10001d03c4c0c3d401c203101c001401e15010051b102d480369490544c90629006105103540415864140c0e40c0251501c4104c10301d070306061001c03004a401400f02e09083c4038048040c04040c0d00058121030b00002220801e90700c0324030702070f1240c0340c6010080058200c2c1e00b0007148180314071540743c281c50040b071080310518020800035441701541c07003041320241d4403041001501c540511100f0014a03450030241b1980410b045d840342d503405580160a9080d50100da0603000710302c40c046452080604000340306035152509108113801d000d070701c50580103204100000c502030303208050340880c0662201c00380f0080b0303041440554100c400105407a42002081c001100400c008015107030045009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 323533794 1250 323532544 323532553
    0x1c030507030f1517060f070e0a09150f050108040c0303081509090a0516080d1805100207030b010501020304060c080304020319030e01020c01050f2208011112010906030206070f23 78
    0x1044840341e80013000100019203500072004025081c5000d41e00030740e009155281480c00004128009042c0400c107411034040c462030160308014041c81410840b0a42c5c2185d011200101d40d160011696044126401808414030300c0c0100002030141040310b4008000d1641c9000f180c41071004a00301c08000c540201043c1d00c400264814800c090100d1440144e040c54082806400e00c4200c540d2610584400c2d0100f04100c41401500106100c0c04c0340500300090902040000c1240029074030340d01c5000986165401c8400081c07150300000c00c0320111003054650210405c10303520351903620341000313109903010b008004415001c10026881040072620a460300204000107400081c42c0103401c0341c00c0c07814414104400340c0780080640079a80e104500ba0801c1440c0408205204802102c07503211681d50b40c05d1541c1c1125104032100504503855400481c000d507a23a0350300d5541d066074014807010350410800c20220011464450016000500800d1400410704a03c100900085a8000c41400381e410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 323535044 1250 323533794 323533799
    0xf09061a040b0d11060717090907080603100b1201051f0603060308250b01081b04020301050a03020d0f020603040c0305010e0615190503011104060f021c030507030f15 73
    0x8103000500c1410100352800c100d46a03a5030042145503040400251840c50416078003915a075403881200e80042c1d00c4444815070030030000781140d00fa0091002144605100800200c1403480785054a108401c0117006006c0d00d035813414288001c002c0400001d8200d0012555100804403d0207031a0040030400d184211104410482d500c1e4039000345c1055040505040040000c1040d810a882c010b00424160030b095195080040700d20a640d800c0c001c00e048540d0000040102012600c40c00c0b50300e110380c1c0c0c0c5190b400d8510801049100074040c90360f020890a8007440035050003000d003450544682c6607125491240c0d00040c0c41600104e404980b082c10080060080110a0003000c9115002900500c62402c1080500c102c1001d5502114040d0080d00c840000342d6280e00c200c41c0c020a405002000a003001e90106c01c001c0e80603000d000c001c526414601c650051002402c105a2001d0400041c10410100c5085000c1c00003d0401c40816440c0c004c3d0a00f81d219621800081020344217800240c0d51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 323536294 1250 323535044 323535071
    0x12030c1a090f0c011715090712060e06090c1b0a08211b0f0913060302040b06030705030106180512012403050c04020906071a0f01050a080319030f0906 66
    0x103901c05103400440d0043c4102d29010303604000314040203000d000c1d40308015541d041110b00c07041c902c5038405500c440001d06114100da0030500400b681c0d90440801d110940e2508004803501d10181d8034650401c90480005e045007486a0103000c0e1150000c401d5800004c12102803450305400e00c4049d1201480001c10240e02203207040b07070340008074100204403d0780c40c010385940b0b940d48105141501e120800501d1381203444500c1c0c00c0f2100c0f007200030704000200c520000a8001490680003c0b030042c0e2928510081c1840c4c05000d581c8074407080c3d40d0b420f1842c6e0911408543c00300400900f81ca0000540201240d01d0b40c170302c1c038900300345a140000011144401d4070184d0040142c030550b0301c103400c0c040d8820300105101007802488a0383c00d45e00580d4401c1421f012400c240300e07205029201003810004401e0450300c550005006402490f181c25070707070b43c03203404000c2911014400d60046510400220908014918100d902070b80d15040015817201800002c4c0705940f0301d820216130081d0345d0030f078411001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 323537544 1250 323536294 323536303
    0x6050309060a0e0c040b1207030b0f09010902150d06050a06260601020d03050903121807050603130204090203070803030c0901021b0d261204140d0912030c1a09 70
    0x140010090022680c208450382d200e045408444e80a241c032074404c881e05441e135460b00045200b03000c0c02c50751442d940e8184200c035450280d03000145000705101280d41e4000c140a010103058004210864a070390310003180c900c640c030406249030066242d000010701c507680c4104801c0101815140d001c0c1522500f1200165502011442c50072560481c0038048142d82c005890742c220552418005540e8569404003440c5000f01292440002c4548081040480065062086031004c0c0000c0340e46240d11402001b210340002c079401d00a54442410a401528164000b07a0350180042c00b43d0f42c07803d40307941c01c042c156031088030181c0d02ea0400040d00c50095a0420180040780300708803030565001001d00000720f400a1840000c1c140c10100c1e82403403416020740b4000f91840e1b6072012802d5072600301d5100c3c006800000c4600380c4407180d10003110ba15414000c070390110404260358031a00c50720b0801c29981e80841d5800070a034100500b8004040014016012158140482030b4806905103050000350b03140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 323538794 1250 323537544 323537551
    0x20c01020a170f0408010e01020a0206100b191b06021e070503033d0603060915150212160c150206061c0b071812051509070e010605030906 61
    0x440d40308007045004100451020065000600c829035034401c0384188400f02805282c0100c1459440c01c410202e00800540c01402e07464855000e446890b554045c4800b90030001e0310410500d481c1c10005040c40001c0c1e4001d0340840d12650420440d0300c3c0070480c2e94100010483d4040f03501c280e0000e560384245444200e1048800c2c0c661450a1900754503a45881d01d0f0700000e0411091044031801c200441c52540a020b82059018060803407040300c4038244581c61002885035501007880d0520100c1c1051440c0500e1020f141c0c0c88400c850350781d1034070003452400b860500030041140103035140015415940b9000304450410010846605c141c141041c0c052a1029880311421000008001d038116401050442d03121000300c54800001c42030041440b20340520181c010450b151610070061015007004800385210010185040e019480c1c6106004170205030350b001c2c0481c0d11048881e001c4c0003c1507000c0b5804074589085c0d5546c1c40c0c3d2201500b094407002e80044012400200c100030b5038120401030241d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 323540044 1250 323538794 323538797
    0xb030106080c0d08090a1508010e13020102031c0f0f1b0e010912020f090108060a05090d0504050402030a0b0406080a03020f0a0309120302280224030708130210030903020c01 76
    0x11040e80c0c0000180c0142003a40001c04020010680a500b075a8006202c0c1c02491070300031000b4807c05035100108100400d00502d19103680da9804607012210703045a90040300da040e0025480c1c401d882031040c0d03038400d600c3d0500c0d030107645521066001c80e2982c0500e81d040044910089410724000b91280e1852440041d61070070088441080d0300c00381c1c0d220707802c001103803250200c0b040c5502007070021440c1d42076007044082c0c00c80c060500001d0003100000b501d61060b0002c20080100c2d4941e00c610940350300304e0800400c0007c5090005210b40e02e0207600964200b030700302400080381080b20020500361030003644141d1b5181c00a000b40010301d40c05114400c420760060300a401c04100558010304841c1b1a4065101140310411a9408040c02007245288141c02c030b8000300d54500c4403d5800500039040f030720803030040c50307100a140c8000303207009500c5048401c002d07400d60840d944e6800440c0c00c00c4000b025404140f0800c01c010f00541c4072100000c00d564800d94011900403181c0c20302a20304404c0b4442c1c83d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 323541294 1250 323540044 323540053
    0x19061a1908012003160e06030403050a0e0a0b0d0b0a050a0801020703090b0408030f0a021e0609070f0b0a0807020304090e0705010809031c0f020903011b0201051e0c1e0d0b03010608 79
    0x20762803da00b904403603011494800d05041c1440c5403134205c41c18103200b101d039500244000240800d040c3c100d030103000b03034200c0b59442444113160301050220704140b0f0f2007420200b440600a1508040c0c864020018070700b8040c283c120600d07a510f002400d018100d40c00b052969500103100420305511014074805407201c0354246103860b207001d00d0907070b69218203200e09540c03980201e8422400382c400c0c8060808058802c131842c082c101204109500d521054610091510030030300000781c60300d019103030a000c81d052113000e681042001e48080c5c0f50101c00030300f00001c42c00700b0800450400302034031034240111031844c014604030742090005400307000c000e4001001a403081c0803940007420403001c22928401c52780008a144404414100080e00421141c0b80d807550030300140001840c04030001c010101c105074000e00c0070391111900004500c102c1d00e4400c00614010000035040540c410003004000c40055058a01055404a0403c1a004940c01e000c040d034031400c1420f810b141c24003802d0050304d017200190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 323542544 1250 323541294 323541341
    0x191503080901030906020702040203090c0a170c040e1204090204050f04111e25051009031407031808010b03150709050112060806091e19061a190801 65
    0xe1030034081d5140c20341c10035484a615404100382501643d1210b980540255100e05201e03440a807941700241e1114080c000c0d0b0000011400c20341503401000b80d194002800c10040d0718000d0001502e0015401d401d80c0c8110035100d6880001c400050004007806940142c94604110411554558100c0311a11030380c20030280840402c0382e80121003144400320760f11803141460401c030025500074445030400310b56401e8180300e07c03c0b03290315010303498910800c250b0301140014035004088409401300070300041d0054405140207140e100c02440c049020307007400c00f0b96980176080c411019000f07401c1042d0302e945030860046542810440c0c1e54051609203c4042145042c000041082c0000c1c85035504004172032840d15031100703d50b80000050320a08003622264500123554030f0796001c4211a45100242d07001a00384120000b10b0a4684001c41d401da007013101c2d0060f01c1e0f4101424802404a440440504c002d0041e9a43d84c4103100309580240d07105d2050314681b8034818211040d2540e5030388000780350700c001b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 323543794 1250 323542544 323542553
    0x14030105220e030429030f0112030309020d03031b030603051009080c07030803041b050906040908120712060905010e04140304091505090a0216020103050618191503 72
    0x3442804410600011440c00052540c00e0107041e18111a4005000c00240868000e80c80311280010f040c006074140a45e0710130901144880c8804c40d40801645054030060140f413201240c0303010314038064500412114800e0b0001035006241142c11408030707a50368011a5481014040c0440c0d142080c141049103615588400c0c1d250f080e0000d00c200b403982c2d100c1c0300c00104421074085c0c40c0c14001100403070b0031464684ca42a070342e0745e00a403019170b101c01c040c001001c03142c160b03c110001641d50160a00c0069141c182c2032001910386000d0803250210140010a0b800700ca1544142c4180c1381c43d076442104038440325100d001c0340d079540c004202050070072005010000786000303070325045580188103101807080744003528158020f540202c03241e141048510744002e05c50000880a4031000c40b4040380d00e4483c0f0003000100d1041c81e00108101e010740c088007015600035480964000e501604110201c45140185e40941104032500f070144540080117a210559034400d8100e1103101d1707070f500c64240741103881d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 323545044 1250 323543794 323543809
    0x2100228020613060506060408070b0912070803040905040303060806040b01230d110409080f1306110a060b060408030f0c0d030e1507050409020d0e0c01030b0a0b0c0a08130614030105 80
    0x3e0181006440b10049500c0c0d859850444004090a40584000c0780e29454095490391021200601c50f00c00010400009500424040c0032186113100440c074080c94814944060302c03006106506040c0d4421000900501c1444014441c52040144070080d6040c00707041c1101300707459802c13204204210003052841381c40d00e02441e26442d82240f07940910b0001c0c0c200003405400c440c00000e00844010902c1c60505040801501388d0140580c4000843c40d00e51004441c0105006180000c0ea80618841c1011031170a50001c0d2500501a001c2c6103041e80711500710b861544500643c40c1070140c00580d25500580c103205981001c810f5140600a6240d901041c2d41c0c3c030200d59034508812030021011030f008a0003a07085400a007000b40d8190b40700d58002c18000010600844480710a01501e6400d5141790701c640b282c0c0130079640080150f00f2141c140714115225400031f10780c4500d18841c0f49023840c0480e000402516040080720b41a42140c2d0030542c0c014199480d50046400e00001403005010a694111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 323546294 1250 323545044 323545081
    0x703030804051c020601030308090604150902032e15060f0f0306031a090607140412110406030b01030c06050a12020d1508010e0d020613030c0201021002280206 70
    0x15116000740c880d81001420311580710102048200603161160600380c0215425048900948807680e00c2d41e10315a4441e2603440403a00241840b510f820884000c00443d03003c4c0c51202c0c000740448515500e009400420400100118000c91a00000d5100e41c139000b0300031541c2e20b880d0700c100703000700358030707009014000ca00e5217010f450500132460700a11001d03100341c2c40400115003109800c00010b5458140083c45e9005540e40c20b000d002e00c00008205900a201500c0e211407024200703803520340760144106601044203801c41e035400307966250301c40c00e955602414015500034116a95254514905458501604da119100b0b112083c81400342d956041391118030304500c1c030000941d603900e0405d0040010b2254200103a80d40c00c01e50b402040701d000550150800c864000101c80b900003d20320180d0b0303500c600711110307500000d02210303c0c40041d215243c1f10710788500c1030045031140c2400076108011703138000013000d80c01c071804205600952140f9a8060301d440360b0b180003403c110704013010000c40600e01e00303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 323547544 1250 323546294 323546297
    0xc0e0f120627010606170a02091008060a260c030a0309090203130b070e040c02280302010608120a2a060b031216020a0b040f03120c0804030506040b0711070303 70
    0x400c00c11050716507000d5440706514020b008000d000e803034080c050300c0040400c00440d040d81d4118001518a40c240c82104d5481d00001e100c001540400901100d15007001070103640c0082610000007580d1030300e00c81d030200c00040c1c40c03003d814a2424422040c6050041e284251082c2e1204100e440030a4002c440b09050391400e42015070350350740384410907900f0150800c005089181400c2000311140c2c2c80034502c1d1030848210b030103200d407004c4030004036507a92829080301d050751021481221800803400722205698880d0001084440d95480d10074100000e4981b51504403e00150300d1000d6030b03000301101081c0d0301401145481280d14001c8404040795074200400c890b03030f900c020703402580d000c001400c12040c140d042940c1e40c4140400e1a21440000d1800b24081c1c000351001080b4075070080281d0b42032742c071111000103040745562221030343d14509240d00300c00e0003840b903c0d08010507440c100030406580030382d000700502e08161600590782180100140100f1030880c0380755054820100d552400c403a0507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 323548794 1250 323547544 323547571
    0x33e07030207050603090a0b0604050712022a060712060f12030e060a090f08030414011b0b0f07170601021c0e060309060702070e0403020d0f120c0e0f1206 68
    0x1516040e0b01d001c0c8160090350f4408004400c0251032100011184034461082096000944901092200780c840540d0810081802d8a254004c24005135000e022034004425154108041e9082d05c0034451074002040225508240c00b00030b00a6000350144094a0f02c1c101c0421040c0c3c0b810561009003082c602408203922040c903201401d2510410f84d05280d01c00040006030b0b50400100f010b45030680603c12026036809011000402c00f40210503601111480c22400891b400a4001112403c5000d042c030018140425000004280f00d0603040344640f40c1d18100a80c1c40c1003c0b50f001e801c1e048803540032900250f00004000c50303a60f01149513402c10340b50a0740d01403106040e0005540c12400703050290781041c004402c106409400107516802101d9035001c2c0c075211030b05e994106075041e00843d80500540c0c861001c103041584a181c40b00341145552415089401c2001c80f141c0c10380d103412380c0d4640041d0342c03a81c044400e498440603002503200101c1d000d0080580e1486000d1300c607080100f250044021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 323550044 1250 323548794 323548807
    0xb0f01030f081c0c030b0f0d080904090f0605070201050403030e01090c1e1a07020a0501020a0f1106040b0c0114070906140a050c030d0e01060f0e0f070201150303033e 73
    0x400d1050f020b421500e00005205641c40c0000003001844034084492007a9406081081c0c1c2d41130840726460001c0e08000464034140c14401480058503001c2000c41d014022200b041d000310340d82e4031510340600c00942c0003045900345403c004090312209041c10180e030345840c0f4103000013003024641c01c084501d110041d03a44207400700d1000484c14051341c040c08942c01d407a602940c100451a001303201c070341e108507555910345490340c00480c0d40d0700542c8001020f4400b20481c407000700d0051800c040d05040d0042c280d0f4a803584401e1720706116001040080d03110b0f0344418201c18680d00380c44001c5d50140307a0b40f4080b0a5985803900040044002107440110502c0005203082140d104400300d4411084040403a40c1e55411704a200004283e07007038102d14103500c0c060001c903800c03c1004d0258100d800b9060794241a4071550305e42d241d9150082e004005541d0382e000c542103201b081c0310100300118000d840001d5110f41c05d840e8005030181c0214512882c01c240d04441043d20b11500c1528110560030a270f450f1510b2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 323551294 1250 323550044 323550067
    0x3010b1c27050316151d03030c0903010204050d030c050601091e1d031209120a050d02031f091d0102090321120a060618030c06030c050f0304060501030b0f01030f08 72
    0x428511380c80d4510740340801800c144281d41040842d889a001410840051012490020760b12005d04c0c1c00000d400070804034001c988001d002d4401d030030005000500d0a0346e11000600b40c0752441c001240850407070031081042c001e090020f28010710848c1410f00484d20003030203803500c000d80700c500720326455510300341104800e580001005694122000b00d03030f1b5405800c1c519440e288000c40d01c42c10f051080541d41c141e1010100c060b45c107580c0268072103500f07010b0305a102801940000b809112400d06082081d9a1000352a03102401061034001c00510214885402d100104100035620580d0780104a00e140d0b0307890004441240000d0014411500030700302304009854030800c031001c2401040b450a002e198103940d88140105d0300c1548551440348001044200701441520010744100e140e64801c10032070b03000fa08012800e0b120f51800d586080c00b4150340c12555001504d080d58526500c00061081000e0071120580155205014517040d40c07540e61041c030583c51522006041e000b02050198a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 323552544 1250 323551294 323551297
    0x3051b0f0307050f0709060302010207170c030d0f020d031e0c0c0f0b060f01020c130234020f1e0f01030f021809060105120c0702120303010b1c270503 66
    0x1000403401d503a9500308506000744d4480d04010104880d000c1d103600028050f6992007002c04403641078004d005818901001d0383d500030b00e8400d19441900613883e4040c0350b43d4040c410103001c01081c1d1220113070b000c15440024178080a419240742410301d00070380004210203019480e02d2a1405010100780009191811100c2040f0410010300c0c000250b200c4508112064403114416482a40e904c0a0f5090590049a541c3c0038001c2d80c0e17802040c640e80a03042d50790303107800520003401c5400351003403c03a10106c0a0f800e220314200121003c004402041000c51500119901c0aa0412500700c1044402019a03180100302c841c0b4091081a2070880340000341d010b41c00c641c1104442c2007045403603a40c411052000d400450090b24450300c16031002070041c0d03000e90309030b40030110319071101d58084d5215244d540840c0c0c0b005d101039901030740f01c003991401154100b0045001e481c500741155240c42c18000081b040400611142031183c1c10100d0a01c0031031080d0240841c402030500840606259509080341103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 323553794 1250 323552544 323552563
    0x30c1908040b150319051c05040801050c040303080f040516030507080114240102070e090a050c040c0c1403160317061e0906130606020a02181003030807020f0102121e0403051b 77
    0x402d10901781f80989960014003070030484032204001e03c15a66140040641445280001000b2a16800104070625420b0f1f1301560300505c601d040300e41908026691003c07010440c0d0040300c03d648184400d2080300703028000c040302201560400c1d810b0b414030715031010910a0200780e4600d1031480001d1001c0307a80c400c020030001000c401c1a1800b075804c200c2c95064488007000f6040c3d44910402940c20801d050034450018046c40d19039400038640b001e96a400071080c601a0580824402440118a000004440c826200780309445030006d0340640d42c8000c0146a000f41000d10482e0a42c501150800360340360b18902c207407412500182c1d250340d40c2c00007950100c40c0d0811017030418a0208003092481c0c00048020086001b00d504028203807900358041d80313101c070864404401d03907035112040001030f01503c0c40940144003401990503110319034190300d089800040c10442c0c554600c03424041005901006c02c000d83c550711440e800d80b444d05450141031480750200d01803045800020310340040c1c02c248510f100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 323555044 1250 323553794 323553823
    0x60f0d0618050f0105061606140f01030210020c0d140f010f060501030f0e0304140d080a03060f0605032a040503071d10030c0506030c1908040b15031905 67
    0x28031521180c61605010454100418007454107001c10402480c01c041107048400c020a2540b0f480e580450f5032070310850a05044a0381c03030316100410000b91142d0842881003440000714140c0d50b143d4010040036901c1215039100355003005074a070b41c181d1075400441041c1600f001c1c0c0d8040c0c410940807241c1c80c00c10400032a54140d4a0600e10703218840e40c0d900120122202680c0230301075032051016840440d0100301148100c0c2d40700b0001000b00e40c01c00200b005251500800035003012086454518590740051040d9000070f69410085c0030010308015444043d0401d89400e41c150f1605102050301c204480b401c0c40d03180c00d000c040c0d90400000801c121805444050161902d8030745c0c82e251101341e04015500a8950000c400010b07000c40004400d030402c40e9000141c080c1c1c0f143c5090203000440d072010b88820b0030140c007044041c00c14405a116048008110b0f83c803c10700d0302e4282840422140050038906450012903401074040d0303400560644254403100c07408840140b00e241c25860821440b20052 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 323556294 1250 323555044 323555051
    0x80c030a0b0109080a060e06061002070312050f0409020a03050a090209040f050c0307060e0f030111041a090402190e01020f0705060d0f05250503010302010f0c0512030112060f0c0e060f0d 82
    0x1b00102e68200b00500c9801404840040e141c450400080720303a403141440040c1c1c0030300c40c100007160398030403142c086110030305003a458448800c4052005521607008071032403540014450685692502c529640074440180400686c00c040d0700051911201510281c414000c895187e418000180980207459400800701d400d1140d0f50309018044149000c51386100310070800e00c0350103604041c0034071000c4a2161600925040c1012440510b40b00e00030ba036140b4840741030080f1301043e01c0302c1c801880074a40080403070b4000d9031010402005007440f51003660464010081e0030742c00150000715401a20400c0721340f1031b100c03699003444000500540e5680e01c139250a00e8144515003446030901d403500440014038081ca500c05040542e0781e80f01c2031100900081000d0740081c60540314101c0c0e42c0d0000e1107030040d10300c51020b1002c03072040c90b00203800c4011100540719209080240a104d05406100031480c00c0c0714104500c000a0081104442501d000d40400a088000d0b00094400c54001540110040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 323557544 1250 323556294 323556313
    0x8072a0510090e09210702011403070302130f050405060d02090703020903010b1027030b1b0c0604030207090f050115030207050a06090b0f180a170706141006080c030a0b010908 77
    0x31036171142c8400c5000360700a83c6024030702910302c2c85401c558196406858480381d00d58802c80c0c06000741d0005210604155080c062505c0290142100000414002d0342559142d401e207c00c000c102d4401500d10b6202d48901d40100005858032400150300c0491401c00503106c0e480c3e04042405008240704c0c11f64407045807407044443d03e800030b55145030744140c0e060350b822075050f580c0c101c41c55000313a01000e0400300c1510002880e0b440a611080140c0c294145081c2c14010240c50321403074214180d60803405a041441c09004030388480c41107030b440d80c081c2501441207501d428011203125034100c03505002c050300010342000380a420012181c080380d00904c1000220040d0408200d441410303646209403049034404154802c070058481b0200300c060038040e007946500c80d514070111040011320788801c0201070041601080a903c41e1210012110070340c4141c610f40001c0850342c3d00c0090700b29200303020b03c3c40c090000b0001d0301025030703a1040e0744010010301210490f0058030700f0100b50788a4502842011044e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 323558794 1250 323557544 323557561
    0x10f0e01140705160e07052b0f240b040909061103090105010303122a020708030a020106050310060803030406050405010b0901061e020606010c1511040308072a0510090e 74
    0x151344004900302c24102000381c90301e420300302c00301c1d050b10f2050001d001070154140e00c0c100c80c2000701000041d80a20303041d4009200f40d4005854840403038100c21656844017070b041800c0004540d40a0b0350018612501500704100540c95000300c1c00b0700d0440554600010f0100301c070a602054080c41114107250f1a890108075180c042d00c0240021800208055a01c041c0103c143c09481503240a06c4001034201d6081400100500703c0c030300c104411032050540004621409100410f1880e03103503400860b2550405052500d030410025071613440c00c1c54881308126141021050300d070041d03801000864640c13245c3c20414050b02020003000d030300404e45c500000b140c076003042650746800b1070231200031561010795201b030340c841c04100e4086001ca1003160703880b40060701c0d0301c0140e203101180c48400a00301c440c0380d65006407600590011510303020b00056107001d000185850100e000c1200f19101c110001500104064600724400c0130301640c02c810502d01d00034019a1000050a0f110f24040081e140803800e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 323560044 1250 323558794 323558803
    0x2030415050f0d09120f08040803010b0913150e0c0301030c050d03110312060915010f0509011101060323010b0d021c0501050a060f080a1a040317040305030f090a02010f0e01140705 79
    0x5c45502169600c150040440d008820030340c032860b00482c9003810b580c64184130580b1035009000c126071012042c40a581d07218070303c0c07040443e1325029a1256140d00d00707110b1740305000c43c805042070307117480018001000040d03030308031002d81500e0041e1480c2894104034501035032403a9601541181c640000310340c4403008000714026600c0b40c1c01c01c903001c84d00c0c1c2d1100d00402d0b0204074407854041c0002e4900c2000300680f0b01500c000d041005040c9065084103510764500e40c00c440d0700381c000302d601203040c40c0c0c0a5051580e12019400a50781c2000800040380c190001900342aa0190024040d00400705a04403503072868070b041d000650004024842443d00c075800100401c01c80c0610800f0712605c1c00c01160500c4000780540c07919905c4401c100410140c000186203207075000344100d0800c42d81da030001708544411040b09004601c00d444454503810f1807075602030803000007040c0c01d9983c0c2c085c10762080540c0c2d000d00701c00544030460900450540340303640101c84171522009420448076000484c1d1080280024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 323561151 1107 323560044 323560073
    0xa05191a0f150712080606131202060d050a05061201180b04050c062106010c0506040303090c12260909180723010201050702030415050f0d09 62
    0x800c950303942c0d11800c0304540d41034452084d00d0721603801c1404550815012100c1c20708100318401c5d00e20a644c4148078211080c414544240c056440340800c44e19a1711b003810701031000c1c1c50035894030720261400f994800e01410a00340300b4501c0a1041c850300c24040c0d800b800340740800782c65844100303071000040d2007940c450141d1b03c8840710540d110001000b160403010340c61104500b81c02807104500320010000e50501c0420081c5600040c4041580340d801585410700280000007410300302e131425616000102100461000e0b5002d001c0400c0301004003081c456101071855000100a0617917000780a50103400007004800300e11086241d00480c1c8041c3c4548003141c101940e204013000950b2110100710b21508207000c54460107581c280602a844421400114505072030700c0d81500600002003155400c00030080350b00740040b03002104035018408160411300620900703040074240da00000 = true := by decide +kernel

theorem cover : BRFrame.Cov 323381294 323561151 := by
  have h0 := BRFrame.cov_init 323381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 323381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 323381294 ≤ n) (h2 : n < 323561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
