-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2813
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:49:06.157584+00:00
-- url     : https://prove2.me/submissions/35b092d1-6d5b-4ca4-b3c3-2ddc1e97569a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 505755395 ≤ n < 505935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 505756645 1250 505755395 505755407
    0x30c2b030914030c130203100305030d09060e03090102030708070f0206070b090124140145030515131a0604270210091d01050f271e1501 60
    0x403291080d000044410300a0380c54801742c520150352050050380300d666a541c0481300b42419030024000740070016012a00340f999505c032080c0030740b04003020480601081e05071641c174003450b46800c6c05680100311b580d000c914100301801c4050301c00d41201822500c0c0c1d501040c03040d0410703042200c40d0002e400c24000114001e025843d8031b207040d001405d000c82d181418a15030906148604951008100d42011140c1d2095218520180034503170440300742c94034403400c445a00c50a0200d480d881c1c00040c840c2070b200c426082ca00049030307004401007100504114003d801100c0c05088000a41c004543c06400603103080008514410092000c1d0603034a0081c0621041d11020780240c107203c4400e400c1e00c00d41c81c1030203001c0203682d60140c95145c01014858020b8449440d50b0700116046404c50b03150a4408000d00203250694800380c96882800c1c0e150030901003240407600b105d1a01c50f4142c0d15514841c8983c0000907400040c003482e00220220f150100300d000b21040c0c0d1403280800741c0c0400b2902c1560001c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 505757895 1250 505756645 505756679
    0x1204080102070c0915030b1314030403030e0303041d07110d08150d02090c07022701150306060f030f1b08150616030f05040527090606030c2b0309 64
    0x440309111100040d5145809545c840c00010030005030180842c0d40440d91884540c112a48804000c144510440405a8a0300288801c900081050405227182d040c0401030301c044542620744402812403d0101c080000300052044081190503402c001c0240384c00c20070b004c0d48a0260304d910040d401c000b98102c1c042d028882c02540589081c8403008016124906659031281c038545065032150258400540000d00c44034040c092003103421840800d05e50304448031812a041600c1d000100c0d001e012040e400d8807a103104440210b41000c020300b113101c0c06604a003030060902880011968140c1d41c0001031080d2800c2840c0009030070740d04004c203032420910074003801c0300708440050902810f1908a981e00d03a001000034100410040c40000440c0502c0c01d42c1c001d030800801c140700d030719200c0b108a0046001e0741c1c0f82219080d14030300412319165002c80d0b26801604090301510400c201c1c58144104500600000c401c12030030070400640f0303d58985980f0031010f10a0780d0f01c1416a01e450540301c9045201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 505759145 1250 505757895 505757909
    0x1b06020d150b0d02210907060e0405060105090d0f0206130801051305070630090318051513080f03031b13090f0f0e0606030d0815010503091204080102070c 68
    0xd000c1031041099036015200e40811611015a917004500300842c41d4019030051040c6031520384050108030500030428400796901c956070481c5da05000000c000030f49000360740086c08680c0400c16225982003602e0b00c83c0009004000150540c0c02c20340c04281158400703141802c000114140a001c4120203018842d00424508440011118540c40f20b6448804a1203940240800b028922018000c49410700844110054075144210298441c0d00003500c20034034101d0004a20041103009200d001d00f106095036800351190188641103000301c0480d0780954003080500c0300024001500c03107401c00101c0038503a01318000c0c6449080c10104401a03a0600b0b8080f10800710902800c49003856103012001103651607100440c0b0510501e080000070000004070b60b9481e0300344090701044d80000200300340103000c164100d816052014104aa40c094181c41449141003c88c0d03040c4899807081c0050f64005801034182d601e11071141c503c106c555801a44a4440307a5000301c0c04e00c0034015501e039540d0003030041c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 505760395 1250 505759145 505759181
    0x70b190b0603040b01210f051c051201060f02120c1b1e091914010f1505070602030c0927070f0e0409060b060a09050307240f1b06020d 59
    0x2195613660460700b014000c0003a01810090210500075000c0500d520443c2c00c90401d904100713071400c0c451380f10442e2914403012028400c81d100011481032040701d21819200035801c00603401c0c99011620345c0c40d410004011485117400b103d230035902c103d00424060040100409200140c46034250070072917400004c40c4205800108603006c0c400c0c0c2d01250b401c0c0201122401180d0ba030b04854621081d0309281c1909120345400320241540c1c990000c040e041e940403c4890344650717500c0c04200030402000c40b1460000710244407a40001e44141c0245800100100c510380c101010030020038490548040200c501c04500382810400d9001c0c0a0a030390811140c0c50702c00c9401080c41d201501c00c80c08902098040c0e6a00d240242c2072003410b0f8400c1010074030040c0000da40380342251300180640e0f40b03402601e1203402184800521060724000311519044c4c42d82c940b04280130040b00540320420001051400d00c00d441c04080d03e68101c0d12044885030740715840045e2030340b0540900b41c1c1120f4051604174040c1d59 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 505761645 1250 505760395 505760401
    0x150206090303040b09071215050916090b06070203061017150f0405071509030309080307030f051e1c0b0a050f1009080d0f0f0302070305030103021302070b190b0603 72
    0x103008411240e106821003141c1e0340f1501d80403150361824604e40e120f01480710081416404100310a80b216101d1020783e0740c1030141e6216075224585506200030304000070710075000d0400c00010702d90051083c0c1d40000308a2410105030f174004c00c5c20b0110490301401150b0344400180507004408400c1902183c06c0e41c002c0214101005d03240940c00d4008c1c00015040414800050400200304000303809800e481d42030900710b00020300050402ca000340012004504401e80c0884c0c1c5c0305001040d80d10070b41d05a81c1d0025080080c04080c1c0b80c591003840340d56190000c07443c80c810103000c400b004000340da442044103100e00300801c0740c131011a45124681440344088105c100815540e1080c541c070342c044c2c21180c40b00c0e00e031542081603c003200180e2062029004035200d5183e407980041c408000011180c940030105a44600101d003284529480180480d1040c40184003505022080121000454000518041103901c1e0000b498208941a540320800c00c800e1201c481a503008825200c1c4041c0c440a0641c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 505762895 1250 505761645 505761661
    0x180510091709061903150603020315010f02160e07030b030d0f03110d05090a0b16051c092f10020a08030603190f050615061803011d0106150206 63
    0x1d01001503100d00700e0030108481c44990381d10001c540c822a00040c107001c01d48000603018019098400c0504004000c80030000b403068028000c581c45191b02600c050200401000152003410050034800b00714030540900b5000c00d13034001d0b82d05015082e00038900300c1510300050020265010259640d0182e041007907004004c941100c400d1480150030309012411806859912b0f01600407140071a5002e0304000a02c8587e20340450013401d41c0b802649505401d036036042c50940f1800c8440441c80c0042c008211541c0035004055081ca142000c841c0c0210740400349855412004800d8030380c40c00b0f900001e0309122141c000f4807056100491003034444100c05040414040e4881840d9031010307041c9030000000419543d000c0c886186c82410b542c000400703401c1e842c207122101c00810741e41120703544038501c0407030001a0b014100056452008000c28502490702c29280600c40d46920141c0d019920390414107001075500c40b101c19007201302d4000113207507441d007001000f00f1064181c2c910f042d5040300781404815 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 505764145 1250 505762895 505762913
    0x7140a060c060b0f0303070606030204140105030601270c0224010612050c040f0e0a061409070309110303041508221212020a080603150106020d0f1218051009 69
    0x1482d007028000a8890a0f0008900c0c85000b58540a0b458000092280700700045d55220a041e40d0003070300d0400c801d110200c0c164a802c40e080c0030b00c1d40d1652080300102700041a008800e1b0a01248c0a80186a0740d100443c3c0400c1d44e07969040800560858000c0c0006580d54082c40000031049049186d030551400c5c2020313182c007032907100d03816026454500007005581000b04560051440380c05400000b65500d4080003003010580300303243c00381d00f0305000181d0704002145042d40c03604000c150f000c03940c0703403013009400030021914110b900c03030300080419000e43d03400c0c4007610050040546140d0101101e030380041c80c40384000d000800042d20800a107988101d8440ca5030152540301c50300c03c5000718800390646140c0b200c1506d0801c01400084c000704010f40c00441c09000d40c2c0d0940407600c081805550b01e904080b0240522001070740b01403080b40c0c06074850740603600c640d00340742022492103a503c103501e0103462003c0b80d0021820700348000f203002c100c02000308105013550b20721308200d50161582c0320703520 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 505765395 1250 505764145 505764167
    0x5071203020a1a2a09040b0102070305070b131a030c0307030b040911031e030412031b06091104021c020318061303080702030f090402070215120414150a181407140a06 73
    0x21b207581c0c02900c4001c0c3d008108107005940c0101c215401581d4500c09001c2c03030307400301c1904012003440450000e240e400c0c0541c5503c0070040010440d0469072031003268001c50b08014815030400d51034050300390450315188603110071903004034812100c00756504d00f41482d022190384240840031900e61007202562002c01a07030199000d08200310010030316404c3c1118007062904140c0310400d610485d81041010b140c2c4507481c258070645500381403038500010042240600119a0078104440c03d605425240660045500c0142e4146c401c01502d0140c14043c03400004880440ca06080d81c1032860078160032540c41c641c056420f1008524014541a40441d01c0c0901c0003220300503500415603200b1591031134507a0301d01248240c072440e1188240204201e1895050398203444d2040303d80746c1010080d40100e200505203254140803a200d03180d0300c041c8001090f040760105410107000558500049682ca201495500c00c070000701066410480e0010301e201c1494a03c500c141042c2e8001c0100c1030f004002203c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 505766645 1250 505765395 505765399
    0x2010c050a140906250203010b040b0f12030417062a070b1905090a030e04020405010905131b0215010b070201120506011e270305071203020a1a2a09 65
    0x344825a0001081d40c900640c10031125078082070381205c2c05040c1c41c02200415600884c000d00140c0860410b200c1196000808685c000c214000001410300b440000d94107080e6888044034a020b0340d500500b452582290300125064002209002d00a00c40368030310542044039640d180764100d05400f845140740708000c8020011310200000540340d0950320314021910100315400e028031706e0001742407030b204c03c4a40401c50100b0341004424609040902c20b51741540c6040c0c59581c2d503582000c04200b500602c1e8241c9219480c0c403888840030072015005031100b03d41007900204152001c68845200d40001600a01c488100c03c2c031141b0302603030b4050304500c1d900044143c00200394940c800100e07072a031401c2000038298019818050030340d41d400380e2000c0316a1543c0903051034030240c2c0d01040f43c0218113880040d0a550103024180100307481e4001903600d091083c011107400040940e941d0560340d1007007091001400c0d50404103c542c43c036034482e6a803100c0700751944030b0440a015021060a006001d4124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 505767895 1250 505766645 505766647
    0x150c0206061306030c060c2303180f04020a051b1c05030405011b0f02010c1115070c0c080a17070b150609030105040b25091401170907050102010c050a14 67
    0x15a095103d520440203990001c030320414164540074040c148040c03000301169070042d41442601d10b1030b81c9000300402c0c0f031482e4003c6c5207000e0705218004039840310004034907480207074007441c1e24440d0303214802003c2c050050344650f41c032002526090084d400c2100b0460701ca90700046842a12409a06801040b219690030326070b40b20389540c14868010401d0024400b0b04040c1e88003c0c000d902c3e046034103c003081c05164024000e9031001c1400300c682d1540c074071100d407040d0f20134220b11500c100c04c0c02086d640011140703410650f5841645030703000204c5031940f010007503801c41100c0009104080360080d8140700403144851425040d5900c920481c180244640d0180c4640000310005654000c204c0b040305030b00800034021400c0c07504003000e0b862800d5800c418880e299000742800350041620006046459407180031006152460400011000850b9141003203071201e5144407119030081d41c0c60140c05000d00512005091100180c00c4a902081c14024000140481c0340100e5100b403655944070080034013a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 505769145 1250 505767895 505767919
    0x20604032607030f0b0a0f030206071106030c041505070f020925020c0301050601020a0b150a0f0b193002070602070f030e0402180105090109030b0c07150c020606 71
    0x41c0070103003a0140d8031800881d81009002040d80e05400c841c841d07031080d80040100f80d06500c00c01c49214164820901c440c00300305010005460326902401d21580100e5000200c88007013400100786a1040b501069240408501448540c410040000c04111282050340c036180035501d807804410400d01c4005d20070229140001c100420002c10100000100072911001d0030b01d0000103520350715080c1c0c80500039880d08002400c698400100720329119044079504010391076046d00e60b4411600070344400e030010200c0d00006080310480350b132800104800c500b0b96890361581440c0c0d80e805040148030074100490b0400e0140c024100203080c400d071281c4011008001c42c040324100d0040d01619801034036091010a2840a12502e1078041030351030b100359240c15901c0092001c202c100e010341d2500c840d101c4c24800035810a540154000c1c5440d01050400094040d0340c1c0d03882040b00c10044490003454100800d40804012558400c05035050301c90600740001c8086240080d9284c50040906105180c4082c1c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 505770395 1250 505769145 505769177
    0x60315051306090c110f0a0f03050c010e031b0c0307060504050409020406032003060c0a08040f0206120106030605131b05070c15170702030c0c010f110f0106150c0302060403 76
    0x10b14003c2c00e0000007880a8080d00c600901304020010120400b8021002c038840004c5001c90501501c035403084040404075007944044580350024000078200c0d42d603465031803040d0303001000601040e03030506078143d000a01240005050500340807040b03021350303c01c9109008094001040e641510016034001900070658000580031b42000d50001e01809034092000f40c20900350200c0b10800c590550841300786441d11000c0351f1091141017080c02c0000d410001240006100503610f0802c0c500040455003440f64500c10004401d100ba400207003c44d41d079130020041414880340301c1081200100c020006942858200740946c01c07049186010404006204e0041020000b41d102c0505030303094001480d031080d54000b900e03002400d00c3c074040c80b58180340040c80701480041210406001180a045600c0b00b000041d25040c0c43e0082c00c5003400205040d50503256000c02c418003071941c4800000c03c02c00e00c2e2111001c10b0040180a5004003d00c124071400400d400041d02500107a15160544142501e03240c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 505771645 1250 505770395 505770401
    0x60c0203060f0a0b1e0f0a030c03021009031505180304060815030f100509010621030c4e02071509030803070201140c03100905040c031b0305070603150513 68
    0x31190710440345c140903201000c1810400d0742d20700c0155140c4000d240300e14100041c00d10700c1d1100501409044a05000504104524843c010110b007428400075440707684d6900350000c0e805042c219140c2c0d4508005028580301c005280340d555650246240c40c1c20050000c1c0300320700091118400c20b2036116207411a440404c8880d050180340750075180c405104a03581c0300540801d40e60407800e5800e200d4007142420009042044116545640c14481d07034140c0d500313548600d10b40100b5100000c3c1190f0800d552020440f1080d800c405441b030b6a0381c851400e0b0050401c0402600c0303801000c5c00190083c03607031180c00007043e8040d100d182000712040350b0324910499a504d03444c0c100404403003001c02070144440d0150426184110700e071484541d80c0e07443c80785d030b40d40078003049a03485080074980104001d6032031203900030360300640110303410200c4e161079403070b41220801807000c03034100016106420401d028052000300040d051a24003030101072000038007012a407103e4020030f44a43c0c5122400032810740c0c194 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 505772895 1250 505771645 505771661
    0x190803031e01080c130f060902040801060e1e1311030d0f0f0c0b160309080a050a1101201c050703020a020111040b0f0c0f07120c060c0203060f0a 64
    0x40112540c03440d0503190002032180c07440e528100e1220250022410360300215001c1ca84c0b0341c015122040420980c03502d44090300503003110384803255840c00d001c260890035000070030103070400d2400425a24940030001c80004401811403664a0780c214440086596008017580c00ca6100d416100540029042c2002d018480c085140d616114a0b81707100d0400d908006480614070301034940c1c80384140201c4050fa010301a11100174920880c102c0000c0c80100c0c4110202040c4226180010342d459080c1d848030090747c4498281c1010480102c0c03184800e5a000550010390811407000707010303200b46004c141c0304c0104024210450440046003404480b84029910181c0c1d620101341881541000e80c00a0b0095210251400055090a010244003914201102d089a2854181500d0b005418141000c0c0390400c6202041030301940700c0d0203003521010411100a085901e00440680e080383c5080c002c82d1001e64820401e01048286250140e40e0200d07245502c011038010f1040643e80b0740501030020880b04c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 505774145 1250 505772895 505772909
    0xd1403030a050f070804150f110403150522030f0c050114010e0c070c180b0d0b0712050408090f0105090a060c02090703050115110c040914010b1e19 65
    0x1008100703021071540c02c494000d0452203042c001c0c0ea00d030414101c403c0c4d4021640500b028281c880d05005d000c08940c00280800c0307824400181a0a0800040500d9030040d40161810310080800c200b91101078807596800c120306116001001c2c40b107106100003040564806814010030b02030075504a0b00611080441d0303540280204440c41a042c8180320026003070040420001000c1e000403180045030701210b280b01c3d0401e403010415807600c40081013000148405e40c8181c0c0e2110f0204103107843c3d002425048174800d6803c1c194615122800034120610315880e100018280720a2001164a080840340400c0045c1e4180601410820040e143d505c02c0480720f98004140400000d074441d8411400601c07a8800c440d5130b002c507254104100d0a5a40a000f8a01c0c068021513511450502644403020f08482840507074441d903411000150880300c41c4003064407200b18800c4002019030080c40307070160340355003200c0051001d01c810000c121540041c52909000e4211104086410295200c800000b0a10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 505775395 1250 505774145 505774147
    0x8042303160b09010f0e031614010603050d0e0301180f1110050d0509030c060708040c08030d05010801150b04090e0a0506011205070f050114070317042105030f060d1403 74
    0x303145030540c01108221103441c0e1551a0203c0305c54171665500034600018440303401542400031803244503541d000d9450044441582a02141d040c01c542805494010340c0150040c1101d11810310018040031104c0d440e0302c2c801d03450310b90204c14800d21900340401c0d0750380088180a200250307250030b0445c48514030150b0741c4401500403481000b0391100040c060040890800c0c8855202c034004035560740564041c10509070001800550b100f0302c94070790141e01c030340640300030020780d41d84900301e504540c0305040802c031254480c1300601c81810240030346112200b03542910300482c0e2400004d131072540110b00400f01100d0703d808030751000d01c00030001d4000b13450700b00060740c020b941e4941071100140e16091f4201c1c2c00d8028541c000803d03035403210604c4115001a111082d1051240c1c103201c0e0307194044d0600300e0a11801034441102402c1e400203442c40b0b148106110702800d4603500310043c0501100c282d520400c035040041080b00d10b40340030041e8100030183c40a1401039103519100c081b25401120701000313440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 505776645 1250 505775395 505775437
    0x20a200d0606050325051c06020c012c06010501030b04090611041d0106050d0c110f0601090609020a1d011e0e0406090227120d02011a0108042303 64
    0x849510810440b40210f088034860507620708080c03000c0418035052007017481c40410403c10750515154000002c8100068902c40040aa1383c940880e0031000811802da913407a09000d000100064a038800e1101440b83c2005c1420481e0b0110340d81c0605010750307030405031207182c800000e0b1200d4101c0710286030f125105010102292410b210346801520584110001c521800b01e00079031003160702416103100d691014079021140380803d01800c01507064000300103070714035001d1052205112881d000c284440c0604800c0d490007803070304150740c1030341c11119800c0c1c03040149544040d00100000c490b001042da80119107424600140d413500d801990f80144540d1a980c105c01c0203500c80000c26502c03030b0840e07003045880c0e2209026802c81c0070b82c2e580750922414028141100d11a40c5008a5400e84014121310048906c0c0704407034100749000c071014015070344079080403051540c1010f0ba549441342c00c0c0707000700310303460f1586520035000b850103000040307541071040c01c5400c032405004641051502007040c03800300e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 505777895 1250 505776645 505776653
    0x8060906130b0307150e0f060901020318010c06050c070b0702010b100c0c0e010e01080f0a0209070c051612030305010905040305090d08130b040315062d0806040305040302150307020a200d 82
    0xc0311b10364854050720784090701c1ca20703182082e2000500103074004d504140e8010035001840c0d4040484506001010141e940010708070700a031031040403400031031515400545422854518040c01c0c14042d0b904101070b420f25a2140e400003d00b107821480c100c01c250f051400d00c0000344001d9002030b0882510200080345290310240100c0c125086c24003103c0302001e8089125441d02c0c01160002e50000740800420384c00d51140c0c22214509006000752201c1d10340c02d14070301c0d212003010381c840b4420440061000d01415010310415006202c084014009843c25a41c000e05610904900611900d01c4240c00c03000d10480d030060f1901640d02c5210044c42540314403200907903400c0340c0300480f400040380d06c0300d100400399070040408860079030b080c0c240418801030003c8010300c0003108103000c4907001d40e000642d441c0100101405140640c0354244d803941540107004011440a000443c201010000d001c851680000c1e43d0861036081030120701c281000030344c40340400040c00e48044d400391b01c91385c00c0c1c030600c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 505779145 1250 505777895 505777907
    0x12210906130612090b2707061805030604023006010807090c020c1f020c0402030f0114010c082703100f0e071d0703020f0d0b0108060906130b030715 65
    0x282c0c00507110b4a40c02c0c1d43c0110150203680000c0f42c001c02c0180c080000c61507a000d01c843e0841a06200e090149656040005541c54803a8513807061001501d040000c101507016452080c0c045c01098001d0111441d0079008220099001c181800b107080e0803128460700c012101c0b03403480090320709606603115565210380c0e01e0356410031030103001b0f0300c90300d40f00c1d000004600001e10740b12105005070460200030700000d440021542e2000340c000035030064180d60340841c1d13214030003544903a4145070204c0c210750404144114034481c3c40d000906000a590781175006c150500c090b03803d09815002400c502c00003030100b5210f002c403010103164061250032041d1440b04800e80202d0040501c2071010000b0800810400303035201203510035540d83d02c4d00061801c04103420103403030603400310042c03c0c09031030140300e02a8010344e58401d45180300309554888490700b0b55a0701c5856030b82c014104540c00c50301c0c2d003840c0f000100c0109040c403031000c10907900c105000e5952814820b24008000d130121140302103054103000707022 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 505780395 1250 505779145 505779149
    0x80601092c0a151203110f0a1b1401081b042601060503060414100e010506190b0a050f0f0a091a0403110603040609080f040503061806040b090106030804060f08061221090613 76
    0x2102c260007900a4803d10441c00010458a40140d10b00144ac400c0d0015144920080e1120321810040340c2c4200b84400100000c00040a02e51000c0d007081d0881d250440ca1051010802045039040006c108001d60340000e1050700aa001b100c03d525000b0004882c40c45c3c0000b191010102e0707030404410b500c0034034041d40110310501081c1c40300c008030902d00108d40000a01d078051301e518040140502c2c4100c900c62030151100d03281001d616417510848900200c0190402c404110004081c0b000510081a100a080b6051600380c04000d040034159070341c0081c11050680050b00841c0c0210024090100a400c0340340066000740e00c0b01d9807180c4400c580309044d4050301680c1c0c028401c0c00041840d04401c0b0304158074083e55140540b0140c4c40f5a524051240c4011b0440c83c071345d64903910084040b56490000b4001801c0c00d480d1034501d0604420080c101d208000d2401d8850f03003410303170210060540421000500e0010010240c105403841001050341d0040d040c80a1f0042c4012460309403610003081c81d401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 505781645 1250 505780395 505780403
    0x3180309031002121b0a050d0612140f19030e03011b0e030f28170d020301091805071503110705030d110a0e01080601092c0a151203110f0a 61
    0x101c03680d038106884c00e0080f0111118103010f00800903880d80c1407287d00074001c0ca10300040007181980e40c4003680042100103a80507030750701b03a50344a21441c4000422011811020070f10240094030210f00300c14420342c2140b0710103020310000070000d9141da5401e41c400020039105c6644581d00c3d01d44490001c011040603058203001e07218405003802c640c180054090a02c440c03000f941c00d6000103e203684c440d500b007917207000c5840d111825203a5540c1c1030008041d00c482d100381d41d0016120362401d52641c05442407070003004032002130711068401181e00440c50703805032041c0700c519a480c003001c054110003d01011402000d440381c08a040400c100b00072006280996004100b4009100180e001c0d0f07459204405412000c0384c2010401f829070350180d00c84907440355050400500f8180d0b60b0969043e0764482c07515010403c0144058800c0a8807903c410541000c01c1a03010004a0130000d401402a80607000314001c0c8803000d002c0500f010302c00e5005400c07407003612080e16075088007000710b55039480c150b5030211 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 505782895 1250 505781645 505781677
    0x7180f020a0e010e03030c0c130b060408011e140610180b09090c34020d0602090a06090609270c0206011518050d06090203030c15010e01030803180309031002 69
    0x6241445e0000a6840e41350140c0003500d00c4010f480c0421442c0b001e49007030040a80e0300c40040e44002e99884024000914003080041403444e0080d03112170300031064540c0c907400c0c07070303e4201c0b10540da007034440701c480d4010b1040c1c8031200c6281c1455816204441c0301c4560300b107580c00c640408a46415001c0242110103c03d980a26030740e1100703400480326014001c04032079201140f0462007404c0c2c600d4100762214042c500d40c415564003458001c80c00402522000352509500011540d105040024400c0014085464079038800c9081c010000c109503081e02c110802601c500001c00700b038400540e00d56803c11040401044200d101807406500c50f40d0910800220450042481d03075518043d2102c04044212801c0d99140b241c241703010442c0d0450501000d40710b071640c6e0981000162000c000401c150516800204040a45031000d190401e105801c4458070030120300042002460359802e50f500262145d00b500c1005414001503440c5000f10300415606206020028504110660084c10741c5541c1c00040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 505784145 1250 505782895 505782917
    0xa02030f070806071d2106060a050306070e030111070b10060906050417030706060e010521190302120d1e020901080c0f0c010204030c0501081807180f020a0e01 70
    0x810303201c1c4240e20030071886030480c000258041c1e1080131846840e2000940e002c400840071710200f050104845091002c00c5c060341c003140000e61007000b4042e8090701c00c541d1810343c9424040425100d41002d00f5035024000c491504240c00c0da0203410201c00d165003410710395124541c60424901000096490303515407000307414040b403498030a2032800d0a075401078689520703261404115100d152030035004801640820f00801c0c2c00100c48d40500700083c581ca4920400342c0d410700040056008071686c00303820070092030283c80c5a01d40c001c00d00031300544c00d0180c00101d402041c00c0507820040c400191600c0c01400003801880303198181c1c00a11800141100304080c01c2400c694401240306440303110b07002c6030090300042d140511060082c41482410f94802e400d0120740400c031404d9801c2500100c0345a000c1041c10b02581d43e01c1070765a6885944254145a0441c0199030b1581b00d0340e090050081c86400d00c07002c40300e502c3c0c007504840c0016142900465a030408000c0040c14404e01104042c002400480d070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 505785395 1250 505784145 505784173
    0xc0305130b010308070c050405090f0c01020c0117040609080a0c060c2f010608010c030e15040c0902030a0b100c171801080402031603030c060506091005010f020c030f0a0203 76
    0x25140d00e80d4001c041c8820750742503840381d0710f00e07030000481210180305260b80816282c880d80299405009010000c14022010410407810440c00a850604551080b08080314980e8041c403005021414000820f2080d282c170300300f61010f00006c00b4041c244c840005019114907a1082d80f06403424010b030801c001b109030310242100d403e520b000030010340004000c0460000d2661001058401070303040d000040c01d560300c0d000c03103094510401084000c80d540702030305040e80c8000d01060581081c0d5901100c03151400341e54082041c9101d00525a800d0b9000c400100c0e2450a540058041031000304a15110309a0400050003c4500c01007100c1c102c0024404038200c00111042d186400b05042d910748030f101100004641041005006030b07414444c030101a001803900da02c0a1010714001d9030b610158051038102602030b95405000d0500a22101007080304d4000241841c0013a11001d29003d02a11010442203160030714580d1107a525002d03038104c4020825001a54100040c401c1d804e482c07001d001551 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 505786645 1250 505785395 505785421
    0x5090705010519032012010902042907060f0c0e0102010c05191b03020c011e05070b060d02120709140103050a0320030f070317040c03061a0909010c0305 67
    0x10030305000c51070900c03040320107040701c04440c1c6040100345800600d41c42018880080407400711208451613000044500d22035240703041103405401507040c154540b03403400321a00c4008031410750819034111040c9501c082000340c84c9c125a41950012030501158200320000307402050704889110101d02545c3e01d24000f0f500600030100200e041c2e8485600340f031207031a00400b01038001c80b003007400c12100c1c24460020718500840245102e019900500b07007a4041400940001007204511405e800900c104042207540101190441940f242111003036403036503808504c1c510103550009601658004000c41c000d8000546d21048510f020f4040c841205024103100100c102808003409607002110030030b021038002c1c0c1a030b40e100046040032103651041ca08005042d9040201c8145100720005800000e06601c002d5220220048001c10b40c800c0c1480c0e600c1408540b003502c0000c0405890b400d501302039404c1c640001c64014000340c5910f81a250036511580200200c3c00d40e1000f00b8601004294100803c035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 505787895 1250 505786645 505786649
    0x20d140609010b09010203041d160c0b1b19021b010e0307140d0c030f0b0c0c061f0902040605120f0c040b0d1b050c010c03051003031d090106080a050907 67
    0xa0300d50000c40c2d0900d51640200d81c04013400e1419880100300020314400380020034045c240707031040c004941e400d00da0002c0d4611070720450518100020000e0150109002542058024100e460b41000342d1420102e4001c0314003c0001503c611003441001003d01a0003003690403550031220304030414024050700642c3d06290340d41c41240c25a0042c2014840b60480d040104001d240003400030b5240a40d41d512840e105446420440f413403d1115010010000d074030300500d8002102e40c03081810152024400341d03070b440b8024a042006400484501c3d10452001c582401034a225001551384986643c0041c2c000d41c061070100800b02410750016010324400d102d024011514105960310b4913203000040c54650b00f018009034041c40c0e81d071103809805124002800801406a25840d883e284010440da003105d180e804c40e40c1c00d240c1401c0c200803c90ba980310202c01074079490308000c0d00c00601d0320396030380c5220203001c03d01c0d401448460010507007036000400c840c0b2400601d00b003030100d556182c14442c0ca07480d0328 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 505789145 1250 505787895 505787899
    0x150a120507120b0d02090c0a0801060804080703230a030b12210a11070e06031005090d110f061015050408070b0f13180e060f070507031205040501020d1406 68
    0x41d030405079080d0725080943d0441004040e030a00155640001e40800c0080e1078242159500050081c0c1803034218003454010210b0341000c401502c0c05842d0380c00e15120703404c4000d04101d000f5017000141010500102c5214007000c10b1140c0710081d080c4060006d2518411280c40380241d001d0110f00c100340006c040a880d50303204010210040900040355041d0400d1004006221900c14449141c070402c0102100420500d034012051b81040d400f4907041c103644454410160381400100042c0341000a6004000003a030300c0e010102c4088003031031500b407084400303078100781b40910000d105102450b0041070342600c1c1142011a070004544406403000c0c0320324801c01420303800400081025074113441c0980b4250280c60352013803900100001d405c00009880c2c002c3c0038401c1c0344d00a01c4802440a1040c0301a9451580c010700890030211405496800010007010810500041080c01c00d841812000084040710300d040c0b140c1d05043c904180030f03400c50864009064a04580407600c04215140d1030300ae1840 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 505790395 1250 505789145 505789157
    0xf0a060f02072304050703050f06060c1603060c080f0108190809030d020d090801023609040803013213022203020a0504020403080a050702010905150a120507 69
    0x9414015a802000e901211040d800b0302200091000154480b403c5403030041d08244248401000c2040200d40307000c1c05000802d450102003000030030550304000d8006400701c0c1d4050303d03901000b20170752070a60034a58041c000c80c1802d1002040200c1c5401014510040da11000c0e034070380c0d85d043c1c03080441c4800d00c50000140c1c0800718000d140e0b0700c441da2100f6454002c1801916044409004c42d103031001c02c0e0800720040c0d10030080859025400390710718025002c5400203501c3c0020002d6000380000c83c10101071000c001000c0f40c0d00e10200400c2d411419800080c140100c24a0a8240306509030400d1003188203003480310418400c4003003482c07180b21084c1003501400e00e9030b0300000280198482400788604040e03508000c041141c51803090040c5080300e0131483c0031026030452050007031178400303a80082d000e0390040c4000e10006002c4d41c1070f03814100c014903006480c0c0c54075000403210b007401a4880c60b084186203400441030041e00c0010203980119448039491107180302ca00c0804c6540480d994000500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 505791645 1250 505790395 505790399
    0x70c0b040b06010507080a050a081015030203060a05030106060809010f060f0b16061a03250513020d0504030309141506150d0c0f0801091104030f020103020c010e06150f0a 75
    0x101c0961840d00242e040c0741c070f01e041003069039880d071059000c2200e007800b041c00410054016035110b406154892015401208440d00e01612540e503d680300d002d078018590040001840d90b161485120010700e0024000c0c000aa500c1e880903100c00b00c00d41d20080c82c1d509007000002506403034011082103607560f5200d115140d180c01310b1181181c1010901510a0501f8000480852030b1303401640c1d0f0920700400e2451040941c3e01c2018a000b41009071800740c40e1503440c4038007201c580b40d1a004110b403400c0d1080ea07490007a40b54808000d01c202030312440381c14980014030040c1136141d40b0032035209106144690b4110015403119030707280302c1d00c0790400385034a10500080c10350400c0407008400014414200341031202c16481141036405001070100090f40103044c5007030041e80403400500401e0005001c00020b009580f500546100300d000181241d24545510003c5900c02e41c119003100520000130003006030301442c0c181c0c031080280d800324070302c02c21302d100c070790440c40c10030b402002e100002011041118 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 505792895 1250 505791645 505791653
    0x1061803020f01031409011a03012901052205010305061806010e131d070b16080a05040305060f0a1109062a030304060608151e042307030b070c0b04 65
    0x300120b00e041e810141c0b00c03140100001024001d04c4e0060203401c001107203c5c000c00d071280486940b6450460311a070704040d203210b00d8081c1ca01091140d101241c141a05040303841005035030300e100d02011075100307041e86200c807241401503114440c140c0e403003640d050045458106c2004849075040301c40c0a032540c21034000ca0503940c05500070681c01070020306070035055003c81181c4000ca4841e131120401c40e1002d00c55082070103400780f1049015054192165052180800c105180000d000350000c00251000903401d8150380180d0a0718015a84001180c11078680210201d6032802c05468103840f5505000101e120403011105454480c0c0c3d0103000c0c20b0800e206e09914140851311041c0450750381d606070b05484440c2c2010b01c0114407842c042c180110b41c003441c250486241510000044840c0e69214052004189119100441d10060314a914040740c65034108840c03101e804a02680082041100802c16040c012895030300301c078001e00c03c0c0700c007664a0034400d41e51600140002403103903610100140000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 505794145 1250 505792895 505792909
    0x501030b0631030302030903100e1b130507020c0a06030b061c09120804030f02010506220b060c0703020f03070e0c280e04051503060a020f070c0e010e0106180302 71
    0x206185076400544000d854420251070b100c19001600142c0000031121034600701001042c00e22032841d00100f0402904404568036403110b06420b0201c0002d8000005491b95071004014002801480c02c108038184204069501c1c3d0100407194040c003074400f800620725000e445031a41e880d070b0190460380740403074a21061050b0000d503a50310101c260342d003080e41e001c64021000b40c1c04426094640b0406c0742454140541404680e0340b01100716814181000300b41d48960716145602d90014280451199824103d1800b61540c40da546401c4100070502d034140e4080004c01000f124002e03182440c0345440c290030305440e000300b40521080099001c0104041400400c02412403944041c010310003202006030076441e5641c000090b2000511a860aca1064034251141d00e8000081600d0250407a200d50b003c240c981c0300007410f00584990120320b0701400035440d0215411694809103c1003000d8640700b02c0d041da0308007800340c420000300000000c02c04900400c052340920400c4007c290a81d89558200084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 505795395 1250 505794145 505794187
    0x4050d0c03120903200a0203100504110d05030a0921021207092d09050d180e09010501060f0f05160228080c04020703050426060708060306010501030b06 67
    0x2042006032000b03188420364400c05504911035540d076402c1c0307140484120b0300409050680c100c641c0100d040b800059800080c1216540c5d580e40010846540741c1c100300206400f604022a00700c44096415010017001000400c2c0b4038a07103488101941c0c4e125810160092629000c5007143c821100c512005403030244e0300b88200456407022070b00c2c820384401180058031a8110010b510700d00141482d0352081d454890791a000d9242c0d02d00300600c81d41602c0300c40d92600c6103c260814028039414201c3d01103000381c42e00003d04160180c0314818100300d002e1174024002441a01c00140c60741a02c1d10b5014424242e69650711001d649090400c00f01502c0c3c0c94488509640490b40a10300704903e10340425101382811012000f810325218192a00034401e0900c0c20704200984900d00c1084580c2c0007a81200c00c1e201034507400070490888441801070151175482c01d05100f19144904010803c0e074035408150507100381402d030280c0f030082e40e8400042d81603600c410045544079800380505040329240c061800e103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 505796645 1250 505795395 505795397
    0x50607080f070c02280b042c04050a060b12010606110115050303121023010306060206060a09090204090609050a03090506091e151b06011202090f0912120610030504050d0c03 76
    0x202e4941d81c20540c2c00940c00781c1e10480b50410428451004140410310304123502c210a001d48143d49010340e121902e810f0325000007000349a4469544869454400400403030401c000003c1142c45d8440c603000e000000900d0f80d4044a47c200155118100080c03081e801c02c403080074005600b00115180094043e150040c25a000400c0905002507030b007800b009809a004102c2160601e0101d01100050645016410403010755004006101c0240c0301c03114101c0c201d4140034000a405011403000a001d41001c85003e482d0320305009001c8203000e00421440019072203a00c89407a0f0316910400e100d440d00030721401d9580302c40d642403104c0f55414115210170350705c0c000900b0780450b414181c000d484550040c0380020209000a80c070f07080b04010803c03540b805400080e000d500030000e40e6001405019008000c51300a640c1100421482d07503042220716801002c01c2c1f13186407509818460706441040860700f00e03100d10a8104d003103481c14024403c660046030040040d10941541080c00d4070710403403500d000c0b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 505797895 1250 505796645 505796719
    0x70215030a020c19140105010b0306040f09020d03030510060c02030a02040218090a020a030c030905070506071a190c03090525090f020309010606260403050403050607080f070c02 78
    0x1149942003030003103401d1151030000b4012456240c0c200722414402030320740042c146e0701d88801444071145980c00d596000c0000c48003c90742c3c0c03900c20800d1010b060300304002900140e05888020805825411980c0f241558002d075120050351200c0c2180c1d00303540100e0107501600318010351400b60400350018040365000c502ea0043c25420700f004500460300884004e98980d60204000b44100d0f49801000031645003480c0511000031b03641c82d9551a826141729461003540c000400104004107180b0031003222030b8101c0300a05a180505805042d0340e070351801290403e02e01800b00d000c1034081e224261016030030800602c48841484903000a565081c40e00480c2d02c01058000600d0300c80502688001c1c0031a5000541c80f13040c20001d0700d09546098004006224489000040700c03001003850750145240702c040362546403294182540c980c0b041c4d802c0605a1300951003003241e6543c001c24158080d9696442d01002aa04c04038100c1c0c1c50580d492000354041c0d1608944014651041140701d1401103000d005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 505799145 1250 505797895 505797907
    0x1090203180a0f0204051005011b110303030a1a1c170d0207050c04060b1c02030615120402010216081e1c08250e0402031b13030b0606070215030a02 65
    0x46880d00165050440741c2403e500004403c6003041d000f4560021700301d0b8a40300b8854208400070304440702e06010903084601c00c2c044501402010001c0640005001d8156a07032410040049401f0f0110440c1d40780c0c2d001e8512184640c0340c182000340e8865030101442c0141e5000381030380d82d103000040888130740034034440a101c40852003150f40300404a1520860080001c4c50520f81444203842c101c6d848805207078014009000d0300d82d200c80c80700c0b02d1080c0d4104010307070784da035031400103080c1a4600304550841a0042820090ad40081d0540b90117a8002d030210b900c2031039080e27400c2c09126568000c04c04290082d0510850b10080010b800401c0d03075041003a5913201225606d04400b901109800c2c0b40046c0c0c441d0305108240000e5100e030460b5030280d001d004a007501541000d01a000e0003d0b000380920390000005001490031759400c02e40285d02c1c401143c3d035103100c600e40c0351480c2290105840c1c08202001054091514104803003020b54041c1c40c2c038016400402d003076082a01300400909055808002c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 505800395 1250 505799145 505799191
    0x18150510031a030d170606040605070221060a0f150614070f0206130f0b030601020c010e030a1b0911120609070c060905010f110306010206221b0303020d1701090203 72
    0x100000141c4c46a81d04001e80010340300d0108840c401070300a60140c9801c01082c00f809520030b0440e4156a01903e480c03003240c800030b0400c0201c221010300610540a10310a02403520450707004218026561402402a80c504d041e1481084d4542d00c1b0b49804034a4030a44615100d0420028000c04e03800794282010540c21900803400e542d0155041d10007014886509219180300c1c922400c020709031211f8840d05501d48100080d40d00c40da122111410300c081c0c00b2105c081594100217084040794011b140c0b80e846d0450710400c5d810f008882c004d0700143c0e814040c031115403020381c1c01505d882c4441d04025201c1078586105018030b42d1400307080e40041101c540725000100c2c0542c0640b601d25442607000143e5024243c04c1d810031595100340d0481160400c00902c4a603a0b40001c5054005a81096034001c41802c2084603031032800800c0c0c020501d41c80744070f12092800b481038a41045034080d409407102089060740444401d1800e80c02040c0301118a8018031941040354091517000290351b0b03281c0e100c41501c40d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 505801645 1250 505800395 505800403
    0xf060f05191a0a0f170d0c0b0a1e09120e0306011e1d060301050f010e0402010e0f0a06030b15032203090308121b09010903060209061318150510031a03 66
    0x10002800c0380d069800c1048031081c0382440c1c00c817003101004e80400c03180c1400040002d52000300207401419180d0128035800201d034072800d4407040700141d11588002000805001e842c1a0f10159240c904aa600c00c1419000c1c504403030392090003e028001603820140940320088940d1121a0410106c0b10003090355803064640c0403042c00e225202c0000b5240920401d42940d000402501d1340d0816030004003e2600c1c0f01c04015080b50742420643c001c1d00207800803c0740050646009a40710302c5107a80051050b0b0584c2c003c8101c1303202070303070100b02d00f001c410303000091880305450240007088a007155900d00c1c00211840380545100c0d241076a2030a65075220072180d60042c2e08046840402102030040c003502480a048401b02442981030034201e0354000a4076004d842c1c40b0180c841d03900010b20860f103923500001c542c51078003000e00031211940c0f903044001d645040b40d443d402d00c2c0341c5003a010f20710009524402800300d40000348124100001c11340114051312006840d030207410303242c10741c10310103035004c0c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 505802895 1250 505801645 505801649
    0x1b070602071a07020d0201030b040b040f09050609010506061207110601030c0806090f06060d110406080f25050d0615140102070e040f0201050705190f060f05191a0a 72
    0x58000c207450360800c600304024550b4080305a4000c030040040b42c0043e122400104640d0b602400d0000303104a100001c1400f4200f001e02450717125190447c488119102ba0f403220344a0b501802c02c59100c0c1d03945140c100c0c2247c4050314100d600c11404c0c0940003140f590125401e82c88503480c90b040e40304a02c00a0301d0707881c1900a8001719170107018244180a100804c1000390350108481e00101456010b00c2c51190316818041d01a5010b2000003042c1e03002d00c5a450700d03104070080b01900412103980c2e940308598490410b03141d8500b0340c0c024603da514800070888402181c0c980c0c61046a8a42c901d0101048010514a24101d030f140307441c0c8403840103000306071800340e00034000500d0b040303a03011030a0002414030307802ea005948048808000c2c40b0115030150444408d0b5582820701659844d0036080a17481c2011000700f000584010400036410029038420a40c15a44592130920480d05031341802815140c0444011518a13882c0100d60303203803600b94120503549851000019001d015100104a4030b030b0040d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 505804145 1250 505802895 505802897
    0x20121020403060e0d0f030203070c0f051005061206060105070f05190b010603360210020313050402030121261c050c0a1d04020412060e0613081b0706 66
    0x10070200140705030b038015034200000e460050111444410800703000322003040c4036030041680c0800000c0f01e00740191400c01003aa0000600551081c0301c2c5461561060b040030381c03284644c203100100e003c074103001800b04c91809400014104981c0c0d05001101c40d5004000d0a641d442c040160020101d503060208c1658841507880c6a0442050307801c060314280c2043c0c2c00f1608240c900f10044842c01d9801ea04240c11031260840582d040f500030f018100354803006c00010f0340c0800e09141d000310b11038000004180c80c5a00e08844500c69a0b01c0b01040102c0c0000d00c5001e030303010f03a603084036046c40c0740b40c1180300c10031441440b201500b0900e00c0d130590a01d0449242058400e44006914041700300504050440e5030410001405246060003580006c0c1c02a0301400042c031012048401444920780c89603102400c024208640341c1e42e80f001820440020058155015450002c0e0a00c0c50103010440a10840e002440c5c041400c0c1d055a81e144268418603e406101400030700c203278400c61040c07007028002c2c441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 505805395 1250 505804145 505804147
    0x1c0504230103110f090111070e0903040f0501031802060a18080a0519050c27190f09050705120a0503042606010617041505012309010e010b0702012102 66
    0x311400160880718104840380100d2003c1c4220b400c84002642103c50609007072130b181c034013180184505407810b1915040380458996031000c22441c00c1c00000680104c400e14084c42001e2640c5000550403910345504030346400707014041075000342c1440c1c8000c281e508424608030140c005c495001030108030441c0c2010245820001d010401d0000800c01c3c41307904103418806000c08150f550703903141d80b40a144140c82c05040710719210120720094120100020060703201c25a650324000442c0b071038104010030200c2180e0702c0c0c480303a110300d4211403141e6640c8503404401001c8040c10300081141820340c0426641640c0300d075520182c00141b0074405000240940c036800700c0c40500c16507614500304444031144440754003c90040140c07942c0f1000a41c2562030240c41c0000c642c4403410188420b4071840c00841100c1d051000004e160082c04a1380c0803510980e440000002003080d081041c0030f102071240e07000d0040300000500c01c141c030302c00040c200b15205040c0310020144144100f000742104004070703020664 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 505806645 1250 505805395 505805459
    0x2090102100203011508040f05060412080705130603020d02090d06140f04081204020f10020610080c090103060b1c2d080304060e1e01061d010303021c0504 68
    0x1030104038000320045065030035401c541c140999407031072404084500c01080200c41c04542031021540301c050030a5000400e071010781c502410810790186042120400084452000a02c5548101c090b0754912140003c81101640390a80803000794020f0311411420a80c20890f9944079624000108401e5101d42c401160042090581c00c24003000100082d070041000c004000014800c00110f4192585c01084c2d0123041e16030f40041030529440030040c9030006401141c00c1c00762a00000c00c544a1440c481307400940c0340c3c17508400b94844404080301078000b00c004006000244003a081210203900c058040160710100405080f031034071243d6000d6803a104520705508490016065000c5807100004815a60f5201a42c1e0200940710040020344255070360591002d0311081400781c031080c850a5a8140f800a50740010705009015a11504006c107461180741c9504188102c8841e040320b41603000b6105118907107a2004061010034404002c00030200000326855088280b0f17640301d60400424000101e03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 505807895 1250 505806645 505806647
    0x2120c0402071103010507050f03040f03030f0501030b04141617010905012d090f030509040905030415031d031917013b01140a210b07050702060322060609020901 71
    0x983c1c05460042004003c000d027103034405080301140c0c0c00030b6005441c442405003a0802700e00420121200540c01c0b418200000140041d00000c0c5006600620104040c035140030045a1340700111150b2400c4003103403420405c0401d00301c00a00c9444519a000401c2d4400c0c2c6079120b5007100c424054103a00280100e40b52480a40c4064540304903091084040080001c5a00c507e007440312010801801c01500103504080b903183e80e08410202903020080300d80307980e12035100303008820307010b698800024900702490b14800108001020380348640c20185190030f100c4440041c1428000446200303000900e400300c1c51900142e04194000d28204c0e02d050549621380402040c1c1320200020020203100d2581c0295201c4003603604c85045810b08000d0310904400900031400d60300059000d419400e90040c580601c2c0034048a00b04c6c1c00900c01c1140314401c0da2528019201805002e0010b500700703034240002172400101e01880d0020540c2403c11850301016035485038284c44031500104001c035004120740002d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 505809145 1250 505807895 505807901
    0x12040309060807021207030c0c03032102132c090a121806050c0109080d0605030c030703242403060b0d1e02061c0203010501020d03021602120c040207110301 69
    0x107880c03149000303215401c01050003556910800c0308000e0070032000030710604142c000c1c3c600c8000203a1100700520060f99a040c042c154425100a114050b407408803d40000b40a0348200c800001d04941d24143c0c0d0f50401d441c0c0d956100307500c1083c01410003007000416410140d90000c5204141c81030041240000794a04101945c4008211710117000c1c0c03a90341450711040b1800c10310182c0c1c071286441520340350144010b80c09850800d00c00350060400050f1801040c03d140c0016040e21800d50032070348001c007a0070615540c2c50361440b018042145034480800302c8402411004100c0d00e403942c4c0840d844441c1800100e0f03c2484a240c200da1180c442000c1007000700034000c1c450f407003001300c40c240d02d81c50791900c5017518100d9402c8925035a082581c560170441d51004152546025035084901c809000c801d14500254400c0c003600380948101e42e0005070135803003802281c00e8400c0c48080280412403560078040000055080407529009003400d1108540310307840940b903810300605e640d00395900e100c03041c5821 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 505810395 1250 505809145 505809149
    0x5070815090406180510050702330907090e0109050d02061308070f0206041d0603010c0c03080c1201060c03030b03030906070b090c1c0b0f0402150d02190504090b0f13180812040309 79
    0xc0a8030000650001d82b1440d486103404092414208480d561880d0085003818142e070490b000252030400508002041580124009841002283d0060441d444c09907501e090031901144240f200c0c000380320001b4540d4020b401064442e402e5941211074541c0060a2074015030403003007400402c80400c80900e0180b1030419006541503000304240c440c400310050800a0070300c2d000e070505c00aa0007094908041404031818406000b003910403650711108000c0c00221040400d80020b82015801c15240c5008821111304c404c2c01400c40d840c02d900d43d071f00c0000340c250003030100340301d170041500c50f4003a9150300c001085440c01007401107201407002d1030800408030010704080f80c490203500070000185c03241074601c5904407480100d1078035524580c1085001e0301c1429011a080b040e100b01a107815500040070304107448540d0800c4c0504e601c804144031541e00c0e004400c40d40005d0180b60303070803500342035030001508022100240c007071803e16446210031035203d084e5010301d03001814200f00501d98410384102c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 505811645 1250 505810395 505810423
    0x370905190f0c0e2806080609010905010509010302040f0e06040605061003270c03140a03140a020d030c1407081305030303090606040b18070305070815090406180510050702 75
    0x100d201c540d02001486811410700042c051041c20f0102e0352504c0c03200030080c0400614070503900d4400d03101c0c8801400f4090584240340251030700c500103d0b589100b80222810381c0d00103031440c11142e00e15000c02029042c450300440096039504440d060024050002d280303ea070151102061600b04041880300812204003010201441e00c02c1000102100d400c1d088440111000021030b80b00190810045036552680000c1c40c0e120840c000001c1d10401080112241e0b010342c407250b2040d01000c2c2c0c1100688611000e010050b004071200c50350b100d00a0740051140135852800e00000c023a12508910168000c180c1580c42c484003054550f946001d4009580182c4030642c091400c0d400c000d660b96070f594901600740e9102e41e07204d0202c0501615100d0074000e1490001a0202c82030034a104060020201070300d5020016603410b001030065400d2401f0b11012000251001c0c8407680c40b901d41000615150403900c011604907550032000c1901040404084074418034001081e0a100b080a4500402c03054800c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 505812895 1250 505811645 505811651
    0x10c080d02160c1508041515060c020a0f06020c1909090614060a0501050324040507030e0601050a0515090310021306020d0e100503060112020a09050f370905190f 71
    0x4040f58010f0b2141c0c3c001f64081042c0c0f0000032241d4a10300031b01503529503295500c4001000183c016485504020700c1802640c9031302d105070316085080c03181d00d00c80c02040c015910806030b42c94142000c0360340c02012078003400722118850321900e000c03080c0c600c402c03015900d4589540400888040301c0c415981c01060850701113240b1850280003030706901005203480c801030340c0a520152089580781c103145041c08010300802840c90305520140007404000001800c81c40b0311800401c4506040482c6800c1d60310041c00c11021302810f612410055010f90780d410b40500a950410400c8901030002d0308100a000c044031000340c0c04c0210007860240c00f08859001c000d40040030b49082d444881520444000c10b107420743daa50744000040c0c0c0c0c03041038500410f82161001901140441c1d0105100302a00c008880415a92500c41e0400420242030f501070840102c48400194444440b2001e0710044245002138140d1246ea4041841c201e8800729800045201c62444195032009240700d01507090401810030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 505814145 1250 505812895 505812929
    0x51e0406080103150b0913140622060b06030405030a0225090506061b060105040c080405070509101d0a0b22050606040503010e01020408060f07020c010c080d02160c 72
    0x20208001840040d0105200140114014081c0d03007180d54400070180040c55241001094421002e0380d03858240e594230480a400d8800c1c00e00807540381c0c0138024580381c0382c03070840c01c0c0070520304400b1040d078040b60105e41c4d4610103102a181c010183d40324a0013003010b10780b075101910300a030411168001407187e510300480211a455041c0d400b0006462030480d00194940e02c0d003012980c40d115141400744603146000c458000b45034001002030584200f5941070050070054a420b56140324150740050584c0c00c110400e02c06410081c09996010f10b10b6807800d11042e50741c82c0c40040301c04102914880303c18003202002030844190082012441e41611607503c000b00f04001022006804400d9820076511440820001e03902e80303081d07d01a01c4c0c0203000b08020802500502e000354441d1049400d90300800300040c030030780200480d80388120f150390050700d09034a01100465460480840480300e40600b840782c600b045030284003501c0710310040e10b80240d8400d03440c1060b0560790b4265100940a110004d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 505815395 1250 505814145 505814147
    0x31905070303120204121101110a0f0f0227370c26010807050d020907030c050d020c0606011e0e06030603030918100902040b16030e03060106051e0406 66
    0x140d0803260545000b49a00d200350a8003400383c440c643c092420313004101600070510000110400c10903009072204044040212030182c1c4500c0c86900280480300c42140e4417010941d462442024144018240c1405c5140e40890206d20142c911b000c10254401001b0010030705c07031207612100b807a41c2c0403180e200108402500c0400301903c010300a8400c85c0c0340c400d407100d124001e8003112001007031012030a030300070f003840401c0c50400c02c00d00c9690564412200009400e0400303243e0911a81c0e000b900c050526039a0480c1600a0120701240c4010064208581802a0550700c042c02000c1f04507009045a400d04400040403d145191a1880070300c05641000c481038210341c0b4410280e2041d00c80a0b108e581742d8002030300758007a114050380c11400144c17944c1c0c1c84c9254407880c0707440b92490f107c03941160360311084140300306d0150380640750042c0c3c810403044900e200c00340c0144a45601c03d02e04081001c4507000404d04000303007a403204010902c04101100584048070703d140170b0602c10007405041c1460000c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 505816645 1250 505815395 505815403
    0x7050c062202100c0b01081f1b110709140103060c142b09050309010f0e0a061d220b3a060c02030301060e0f090c220b09031905 56
    0x60024842e0000c1c060445040d80505090040b1356084020740c4070960303440440541300d41c3c4854a204e04000c1d420040034840300d0307600c80c500c0d200d030200c0c0741c1e100d90000058055610150342400b0b841c007440b500d000085d00c14542c0c0500000030360044540d0941c1c0d40b561a1140a5810710b11031390b81030104502e41520000c1c44130041d0341c4022224440e02c00a1040c24003050105803111a004800b1410500400244203000004003e198000c4c3c0e038901c10100d90040c00c4458100c2c0d4521203610581c103400412040f8460340401d1442d5190a010030300d0241e0245c0040c510b240c000e40a01d1441020b8644580200703400e2148002c681e606803510000c000b550100092001c1c080d000d540311084120600484070941d043c4400c5000e60320440c104095003940c08041d64903082480303400006401c9d03e200b080d460030701c65507203c404c0802521400e03072078443c03c919100c150029040300482c40410f401615003234081800b0840140440084030341d80308900c0c0181814618001510000c1d040582d03081000100300007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 505817895 1250 505816645 505816711
    0x7020a0909020d08180301050a1406061201031113020a0807090609031e06020705030301060c0510020c061923040b0105030a05060a0b0105040e010e06030708071412070b0307050c06 79
    0x101d52140c0c0e41c2c062500b24100381024103885c6406602c0d02040050032a925400340c02c01e201da850380a01c095072180b04001040c424050100d088604c58801000060300c03548510411120050005580001401c40c1314201d8106030030704000180f406c014408800d421180348805080c05103404c50300035045448a1100c202c19045824104130514140000c0c00345640c10b40c0e42055008007681c1e500d5a407000c2c0103007080d0207107100780d44601521071980e8030b0040d00c2c421102200209030182510b81d582440a090540d0501d0404a409848a450310200e241c5a800b0944520302603c0000f06401c00781043c900406058001501030760024501d980841c100191580e88855071080c040740005248004031904c0c001c0e40d0200501e0701140002107560000403200910582080d0704455500f59560384d0541d50301c0c0984980304500c12420820900340c208080b85091001409046440469607414219080d0303000b00d070004001a070100f02080180c40502a8580100d2600c49516000b400d4548640d0850424 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 505819145 1250 505817895 505817903
    0xf08030403200604080a0614150d031e170a0b1503040c08010c0e010f080708010513061703030601090b09060a030207060902030f0c03010e0a08070224070807020a0909020d 75
    0x1241d840c42c900e5196a00e8810300e24805400c0d961141d585000b603030360303402c286c100072124207080941010000c808416400c3c402c1c10020103d00b41614850240110b07004104030a804001c2c00c1b02904040003d0558030140d210714a40d2210100c3e40f88850a27070407100c01504000c06036051940030f100c141d03030304003624240d44e120360011942d81e140ca10f00403401c074480747d129007250350030000001061600407804050241e001c3e20f070b505c440c43c81e01008862580003101c010340450f114600506c00c0d410503400004410018803000a207003501c42c204401079607021404a00241d10010400646590104001c0700a00218110702c2c20070000400185050160303040d0300080641c0030404000388400d030703040f46c040c00340c000c1c054400104500c1665611100f024001500940c20540b907040d00e844009004100d05400038040e50900c099079080200022055488000000ca00c0410303d0a0307950754030040c05140c1c41092410b13501d0001348103011035980070b5481038070114901120b01c0090b0311005a0400f02541c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 505820395 1250 505819145 505819163
    0x80d0e0604090c2006070f0c1a0604020d050a0b0a08030f092b03020a03080c120f04020a1d040312020405060904090525140607050a08030636010f08030403 68
    0x403042120300c244c12802c180710b0b8000b411100c035190fa2000c10058004d08580e69025a50466202c0c10b8502038501301000381280103c03010080e15400c001d03042c3c0d4000300000c20161601a0110b0084207454003034440307810340340e620b07042e07146140f03003e0206100400034000036601705a040c02e050302c03050181d480c1da1805003801c030181c2e1001d1490050b04200d540400c0842c1d40107081d042c14000e44d1004170800c1140420900004102081400410748030086003a641040036035841401c41e01d00e03e00054402c9802c0a0f03030543c08100180243d00c0400c2c840081100e485d101d1034039003402042000c000c55104041c40c810001804240c80303081c125044400280c41c0030030034582c2131400f540b6090259048146081c80c001000800e03100b005403800413a10411803c43c20080e00101300079480c4030703140c0001c0c130039882140c0300f80000d0360001c051a40f00c940145954400311607055000e5021071501c500d0350380880218400204075400d550360030f007d0013001f01400521410304826070307a40d1045002c00380c400c0b45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 505821645 1250 505820395 505820411
    0xe04080a110c13051005010509030718110a0c12080114190806070c051e0c010c051c050712030507021e0111210906190203070c0b10080d0e060409 64
    0xc002c0041c104030040e10b00401d4001c020904070090a0680da10000f0690450b40000c02d503100b0003da40362000d00401500da6a07141c86a8103041000e1040342200302c03a02c40c50780350184280310f0702800800781e41da26514022249403030b00d0680c1c2c260300c4030710a09115081005201030040041c0e41c805600c4184d4407803166200d502e800d0105045203501089040c41000c081084040d40010300485441c030420407a40c0110300b401c00c0029291540c0781c829041c0c0d00640d581d07010381d031007030011000060141003580c80d440701c0848a0100e480e8010216408603500080c0a003c01c0b03d6802d8a0000c0e9a2601e0104002d0801d0703e8025143e07074280382d921400426200d40381085039820343c00021340340e14006c201580e50416540958003000a440c1c0098200d10300000182200404075005204481d010043d03140c035052100d0100081d00040d05060802c00589030200c0050308489026000c0d4004445080c4a14689a1410b282143c1c1c9940c42c0c007000090045285c0680b503001c01c0c1d80a9451070034011961403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 505822895 1250 505821645 505821677
    0x1802070c03060b060c0a140d080c0d0c090b0a020a0c0e0601270e01030b010602120a051c06050306070e09060a0e060402030414070f1806180e03041e0f0e04080a 70
    0x40501401411705000d120714007810410701c3c0848030114070940b07040d22041c1c4641e000c255003003501180c0f410f08800b001c000702001c210550380010500c07642c42c140f000d405074444440074000e8004050741c42c09a0b128544550500110010100c010484400c03d443c50b42752a02c0020304040480314516505071020a4520326210447d40f000c0242c038010040706000d680d00d041030901400300f0300c16540940600d40d60440e40007000740849007027004580b550b40c6841500740d084851040b56800c00007603181d582c030001c2000e603000c2c08074174003481c92507951401152501c020001e902c0350143c14688038841c1d000342040306980000216a001e64102c9005890b69070314100718610f0038000080c0030b1140281c040c04292035010764000700c25200a210210540310300c0850030b0302200e06034000d9162060450302d0000907811641c201c0250308014209883c101030303039001c802d990040710300c4403040d40845545c1c081c498007100a5400d0300521011488007074504150721040c00ca40b00d4141c1800070002c95000e142420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 505824145 1250 505822895 505822897
    0xe060117030d0c11100207020f03030301050a1401170921180111010f14071106010b0906030403020f0d020f010509070e0609070903021302070308090c0303030a0e0c0411041802070c03060b06 83
    0x89044d2105071101c0d500e6441950000b90b00c418000c0744100802100240c080c10000180e038180c0e0f0000c0d00d1500383c0c0d0b041004030980c036002d20804c541040780b09588004000c0c40c80610714083c002d071600400403810103044200c040c81b101044403040e0041442401205480184403840155080c2000c0c00d40c034140f042d0040c0500303e581c01001041d0b08010300e032400541d21011071481000c1941c3c50320007002035802d406481c0d003820710030801045c10901995080f890031800854001d48240111105500b07400f0f40203003002d83e10300394a005608007503d0030421060a0050a51080c041d0015003a0641000c1c640d0340211f90140025014405020010b20701a0080041d6000f0b90780090000055a101d1700d03084002c0c0d840404200c00141d1424086168408009124400950010055429030340c1b0031001c000105111092618540f18103100040c560700d4600c154403421803200f0f49140d407541409003d00c81a8100311203003003490300c1040074202049148983c9800c0e40d03030181e004600d0307807071010008442d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 505825395 1250 505824145 505824167
    0x1d0d151109120c09090109080712020307020a180f0501150c0f080d020d0b1e12070302090910050108191704030819142d070b0702010e060117030d0c 65
    0x80400402e200c441c0141c00156041d0002007218021015520003030b001d42a1202000010311410341408003800040107c001040b400050784101d0f0300301900d580015003240ca403036000000c1d041c8030705604200031010340140c6a22054288081c400303949464114865903202d01064000c100c00c07030b98501c0070015002e0f510b5003242e40046050341c668540403808802540318400012074180f0f480c100d20700c10306010050b07486060007002110210707040e403014404d00c048a03160354011802200c002000507542c046040d030140c100000102184070704403130366904032841a080310031540e100b02056002c0e0900c01203e080c1c1603034407000211080307014406102060055410041a1200c042401c80e000b04100d01003035280c0c91240d0f03801402c07290320a0207658510501040c18603a0f5440036081070041c3c0f80c890040d01c18140603005d1803030408243c50310400c4500039a40507005075154000814091401c0014901400322403c041c580a250b90202c40d58a12417903032075241c140c2c0c4524001144c0d078000c41c42905 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 505826645 1250 505825395 505825399
    0x20a020609041506020106091a0108060f12070b0705070801060b04270501090f05010b160f080c0102120f010e13110a0302060d020a0201050f01051c0f0c061d0d151109 73
    0x2658640790040e018000500130720781864a04445109c1e00d01d01101c03000a849410386903508141c4907a0140f00c0b520400c2300f10b00350802410300c03034145450000c220500080170045035140e2904803e00c2c00c9810074000358230580550381020000c0c800c00102da42150b048078543c0f103211842212410704e000101c16000000000c0614000000a0780a1143c10560b4109a00700040080d0f03a00c94850380c0c40740c02010700065214a04a50f18000903004000125032a800b6038085810b10307100f101c06500f6070740b14080c5080758090741400c3c00f2100c18181d810a01400740300c100c0e8292031900d160079000401c188200a82000000c1c072903040e064640084000146401911413903440008000c024041c6d480019504010b61a080c009142c0c80c028084003170503544020b01e00250052381540c0e18810349404101035030400301800544002074600030f4464020308264a440b100820075600071041408081021402592481000c00002c2c8407502501448a8001c0000902661134989882c06006441103d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 505827895 1250 505826645 505826681
    0x30d0b0306010501080118091a06130e07151b0809100c030509060d1508010203150603060f0d02060d02120103021c0201170c070f05010f1b0905010e1201050403080411010f020a02060904 81
    0x140c03034440900405c2b4410354043e84c4e48040721650382d80c140c00311100200060072603040410148401e502d542d0b50b01201030306501e0440043e29510203500d00c512203d503000c481907100060380980d00e00b03000140304000382c040e04125407001d881c1d442c040e0481c442d0300308540c82030100049030074004c155544103044104c000b01c5100000c0d6152105903000350301c25140300c4a15545046070ba0b01c185807040031203201c1d00000d0319000e101c0d48403006210f2003409000301241d06c480107005043c2044d64a2001d880c240d8894101092035501d18014080c010310071500803e00d40300405050341c09070360080d0703811450400350300d0320031000d50f0349a0b907950603401403540c0281113000b00716000c4180706d015000104000c0310001e0800c00454002c3c1c4154040302081e000a01049840d40304001a6000d900d00700080ca001800031130540603000071407403c6500c1140c045006c03900c7d0a05000520202c00304c00c400d10384080c00c00d0840c0454020010399500922a0003d118031000107841c0180c0d111a00110243e101d071b44911 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 505829145 1250 505827895 505827923
    0x40b120d0c0501060510140f09100c060c030c080f060a12081801090f091a040608100b092205010b040212010e130b0117070506040602030d0b030601050108011809 71
    0x20103180c201c04041d9802e40c203103a000f140b14544544000040d500315100e100c408000c07515400030382c0c4c028000001da505002c0c000c80b442c0e40c44810649032105c0c003994403a40c003590380e85800030841301800c60350010545080c42203940650880107076900803503110700d1000d02d5650304000071107440541e00410f404903039820110b0200101c04001d854808810352460a14105107001122030014600c00c01c540342c0d0764080104803107400c0340c1c09002503500b68610742c0c1050244401080035151154801c070b04940c81095605030607c21b0b8030a85c0c01481007100e1300007050601030105e46040140d042010540803130040d1590421109501611303284e44050300543d2900145281101c0d80c5a0034810fa82e0814501000507580c19074458285400301e40c0200f045500b64208034404d012100f0600c20b150f92841503000c0420329a6404010700001c0c0215402503980c0c0e24a1140441500d59400601e4002d601600050119a801c102c00d0b03410340b080c205040c11341088190403d00606010000500708070111820 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 505830395 1250 505829145 505829147
    0x40f120c18020408120906030c03130f0b04050c030c01050a0e040f0501080a02010207060e060a2a060b0a2408130b070201050105120313060f020a1e020307050d11040b120d 75
    0x500f044a018a06030307198203c0e8258104d00c10701c07a1060b20b982c41841000082c10b015040070245800c41c1004240c0801102c0698600c0900e80d206441607030b10405c01002c20040100410810040c16000d4020307018002081c00046c00a000da200305e9818403242641c130201e540c4465000800301d2082da00c0601c00c41d6503074000325894807202d140c21b80c014007443c0c06c045038881c011080e9801000000d0600392403c00c000108480b51440001c0d895082210401d0110104465914aa941e20700940300041c40010000800500641e0303a07000c10721144803445100b00203000c0300300b91700c0040c00905065907159122500000b155000002c010802005501400100c65056000c01e0695105940400031041032001480c1d0b0b9010389032000b44503140507070b0140b00d410f200c2d442204002d00c0d0303030040380d003124415554504416011982c814200403811044c0e819440c003044a040182025150024800c4864503a940440200105140036035154501915541c40d80601178850021701c100f44c40b05e640f0030f490 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 505831645 1250 505830395 505830397
    0x2102040b0403050c060f0304060b06070f0302010e0106050102151906030507090609050f0405300a0e090f0423150a1a03031305010e040209030f0a031103040f120c1802 73
    0x1003a11248508068130043d402e1000c2266003090186410b64110399841d81c421018240c1481e286030419018840000012040c0380c0c55044244aa00040741420b00000c0c030900316002940b04034115446000142c503400f1500020755048078a03141e2020010043ea07006001070103955000170b10301d01c91079400081c8840c0681c4010241c64180c00d0500040d1503074012440340d0401035401a040f600a0140c2c01482c85601420030b5100041d06440e00c016072000c6480150b6030040e10000d00440e1078044421602d280004600e0f81c041c10701000f01e01c040c01e241d04c2d20140c041a6940008240407140011880000100300d48214402c58407040d45152400400c064041c20b04203401c8c60040700e005006100341e01e00801030301c030201d02c080720b4060b1003850100111b504501c52000c040d0059400c100940d035035242448440003100aa00080003402c0442c5002003442560112001054005010a000b0701420025200c03c5905003c0ea00c40454280e04100c001008164031400011511080600c1c900c0e410f50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 505832895 1250 505831645 505831649
    0x122d0311060610170a06090e0f0106091104060807120c09080c0102010902090a0c030e0111034303020c0706020105150109080304060804050a06020a0c0c1706072102040b04 75
    0x24040da1002d888100c1404600d4800d141c1039404568184140103030201c481c084194040032841010900d140e44460410440301540c00420300c41e040b99510022101d42405580014140a2820001e602c00180401560301442c029030f010050841c02145181c0c0c032420400984d031b1000c0d00200f211443c9a82c025000b4070743c44c406c541c00b50041d540b0503409980180b00708806150003904001c5940d68150b6207000501244601c40e040c155583c20034029040309224030114000640c400d140e0324106140010611012200e0b441020304080300c035541a40c460103a00b01c140c241c1020b850130880400b80069019001d000c01c0044a803003071840000f10030740e0541050780119440b0035199995240c0f400115810120390040404c1035104010821869104030a159480340c0244140c50321805140d03a103c0581c0c3c040c51440c0000780300e034800d03e418428811003240007000d40200c00c0b50052189a44152101e00090160051281c4000b061844401140324145a0310721108219130300d644a251041050b000f41c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 505834145 1250 505832895 505832927
    0xa020901201c05070f17130f0305060c0f180612071e0c0c210507060f1b02101805190f0f0e040602070201050d11120a06122d03 56
    0x318075100b8030743c0104111a403854002031030544420190300c503040d10310700f189155a4070304c130200041c0300a10004d207582d02c050080d008241c5070440c514213009207414000341513044c036200c0c00c10514200c100918102c038042c47c182118000d01084100c0010501e004282c84c150940505c2c0c0c04208407140d0001e01564003d0708407039421400c80b410042100c9103603140000524005240409012005000044112950400c2c0c0044419501d40d41c1d6541406156030004010981c2c43c006500c009030070445440390001d07090345441c0c0e0b00100d500082e424011008400050054408104882e1038800715058060000640003440f00500b50039070f18941c1c1e1613403062440e005885500403800e000c110408500320b40c104c400ca11ba80351180e4441c3d0000354010b40d41207050107400c12414101400ca405003001c0360030303001007003a280c0c042d03942a03582c652001000c1e595203920341401803145001d24490414056008400c1e0300f4005283e08a81c0705001000da00044c0a07184402400105136118000d24140048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 505835395 1250 505834145 505834183
    0x12122c041e05072a0215040503031b01050604021e0a090305031b01051303140d0f0501090c020c1212070c0b030f070f0e011b03030b09150111150a02090120 68
    0x103501e101103c041c0d0f0030010910f10010441840000d03140c52503e600b00e605d888840d61f4603040c2c0d41c000291031a400784a41104024481081c1074000743c0a00c903140d8440c0f002e94055103010b003000380a080d42106500603c02e52200800e00d080792520640074800516413050889544000d13000101580b00c801c00b60042d240d41c01c0c0720019441021980004480a07456154984040d2910b801002240c002100e8002d01075a0744185000a0842d405414024030802c48001404031114500038108040d000c1100e01620a5580c02c0e55049030000d03411170b41e03e5841d000c641d02c5402c0303407508100510580e44030060390503000c000d0041c0c02c07002c061043d00407a000d842d901c18000c688a81139883d488245040344c007045542ca40d15010143d002107056045109260015810307405030b0000d9480141a81d03040102100399820405d41c0d40c0010744556044460401024950641d07501d00d000100e0040040340b6035600400e05001c56405800004d4020180341c002d0301d444046145400e42c0e601b407880aa52141034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 505836645 1250 505835395 505835417
    0xd08030105040614031203090f060f0f0a02030907050402090609030f0610080a030e01051c0e060105120102270307050618040506010503130f031812122c041e0507 71
    0x1003200800090720030085d02401c07003041000460101600014420a603600542c07400c7c2e11560740a200c00c6211b11010150400b183c00c1181003440700d180c0081c14856514410030030b0124a1800143c0c81741100c200300d030050303942c00d26000403c0721806143ca40640500c198040440e0181c3d0101c2e409224032007000f4214080e80e0786518140d6500e0724044043c0c0803400860421243d07500c2440202000c09071850540d9007001d07002c03203450484010350402d001d81c2c0c00010040c130451420f4841252a2403000b40254100300f074182d6102080440c000d42402c0308506100e007800c5540b8288007580040900902c5103071103280e443c0701210f0031110a071259100e9460400040d1996010710142c4c1c2c09101c41c1100302268140c04e0b944c0c000c0f40d000801c400e40c00e11043c10110051001c00d580068050030440300081d0f0708910324035000300c200e143c2c01c0c8220203000002944500101100000d0f10001007500803109110b40c0440124008200042c03542d030b0841d4048803c1100c0709503031380140c0e018000956584100f10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 505837895 1250 505836645 505836659
    0x1091406090d080106120612080901020c060406020705210613060c020102041203050705160b0a0306050a0e0610140a0509090f0f06040b0a090c03050f01060c1205030705090d080301050406 82
    0x50b40c1002040411594001444110f21408400118a80b650030026030241c80fa18154030607404d500c0203d4080000042004040d603040c0310210303a00c5002c1d10468282818910080d4503480c4d280611030003010800076403803032114481081c0d41803d04100540700b41c0e0500c90b089035030075005008240c80c9103041150110940d4814421141103a004e00d00f0348c1340300d8100d650b00300c40940c032003401035640b4428451221403110b40c030704265004040e5011855520021244c1c068107031141c03580901d00c502c2d1085000c00a51000301100e0394421407c41f07028482102404c01541d04c1e5840884540c0580400700d2000c03e0560068018071450100310340750000c503602d1200c1004c600342e0803590650943d0075240843e80f5814650049040880c00501031010162170f126810200c1d0114199400061703120401d0101902c0c00d01c442502402492030072400211850b1544040b03218490740300c00c01c2200000c0084d40072031141054462569000f008400d40700614200006503400a00402d44554030302100004c800b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 505839145 1250 505837895 505837903
    0x507030507090f061709241803030105030c01030c050d05130b0916031502040305030d0615022107111c14030a0e0609031f02120f360109140609 63
    0xc0d4503c0e9100b410420707607600d40304020314000d090046d06110700b01402141c89000500144812000d060000561400d500c00c01070392174003902900c80c15081000140803a0f240030660012100e004c0c01c012400704a001c504a0300c0c0c0c0300c0c03556485012490034045c400c008508100e551174660040b202c10341c0f0341d1140b00c00342d03440e9148458201e401031250642003001903601100000b01d80307200500142441c0e542c0e00c4e551304650005405415084e9214020b114940905000407042800780c8000d00260b90179400044580f0510404c81c0e8400c400032990700101300348c03004c214000c00e4015200310380c030603a00d81d402d0516011407042180c0c0c2210001041a240c0000820b50308070b50013940d02c5c00320b118000828040f1030344c002204940c060060540700c1509603000b14040c0c8051110103001a0b031948000580b5001d404050030030103c070a503103414444551300f00b20800d10540c1480300d4330000c007034004601002c8082d000490b00e0555003009009414084868030322000d94440401781d03102513855000694031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 505840395 1250 505839145 505839149
    0xa0e010801050105041a0904020d170a12060b03070504170a060603031d0f01050d15090e0f0c0108040201080604020a0306090c0207140307030f15180c051008090601061d040507030507090f 82
    0x40012800014050310f041c00c4011006406949442500c003507100034440741d82e01933000b03600030840b1f0218101c0c4003451445944003d0100041c0c00c0d045040040004006101d079100b500100c032007031081203001e000d050101b0300c0340b1540010308004690356890060600000c80000d1814191080e10b10f41c80c5003480c1c1d0325600c43e540c2c141c0d13900e0310701905211590014079249082c0702c2d11484050b008180301c015403241c1c80003501200700502e0802d141c1d8805915195518140c1410040520103110042c0d82150f070081d00000110740141c0c403011a40001c070010a00c42d0301c400001400c01101202494012031741c3d02c240d4503c40b0300b19903850741d903005140d40e43d03459202c002c00010b01450f10350041544148416031626100c400400d00203500030900c4c0c4a61300039001500c0401c1c07860400c0085103482d0b121441c950301075080003203c918151610700d481c2c0c64140328400601c04640c20340680c0072103150810b01900c500600c104030506100c2c000800034141221804080b40450402085488880071030f881 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 505841645 1250 505840395 505840399
    0x190501020d0c0f2a0801061410020c0d030305160302041a03100e070306180515120a0f08040f06022a180411130c020304140a0e010801050105041a 64
    0x80740390302000b29a402a0385509403004000040d46100080c0d241400d144168040405120111104521410000d04076071008503d6890420200300c0801c1002d507040b90418102c84c174035204000380380e06a040c2100810786980c0580043d08010070540c05903c9540540080fa070380e07614903813803214140c6c01c0788158020080310032100c012901c440d2404a00556024098050740c0d445160740c1e40d035007000c482d0241c600302d0220b500d40b07809100c809070003e120207000450840a00031703401c00c3c2201e09032280400001501075010804002005081000b4840210f540284030b0b941d120135504005403260414081c0701c0804600781c40000d181d40c80019445003804104811281c5051038140200310095a4643c15410041d12404020341c50740703100312140305900420040703e1421941301000422030145442c42c451616025a03189400d42c00010f880c2555084030721030012154010004082c80c146034490740c000f03113402002144008040d00918120b5070282c80501030920a40d074508000000d00c1d40140d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 505842895 1250 505841645 505841653
    0xc1c1107060203040b2b0504061406180703240e070201060f120309090504110f060a051e04030f1a0703140f041a070c02010e04092609030102030a060519050102 70
    0x400103010a070000d01301c546c0f00d1510240744400c40009940d04000380c401ca10800c0d603540c0204414040d45025180c42c80d0306d2001524082d141120001d5910003004d040c0200300c070010307400505018043e07485030903002c0d01601001c440210301083c45141d2019030294404144011010462540c014060201550124014501c0036410f00700c4244030525003000550803c0314004000504111901c1441d0099004022541810802d0300602982c942400000303400b0300d070100320003800943c0c03240c00d80e070301d801541c0c100c0070070441c1e0600d02640b240a517800240181e0090f41546d010401240c0e0028003104c82903081084a42d2036200940880340312030310f140081440c039270005040005038004070380e00074070851030044900c980050480307480d001140c102c00031420380d072120b900350f60f001610100e500d04111403e01183e20190b41310100c00740100c192031011280f034034040c20b041e91100e082ea00c100c0381c003030b000319102d1500030254409001c40e48274807401112007071483d202c1c0114041016003960f0060f0000c2c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 505844145 1250 505842895 505842899
    0xf030405120307020a090515010905011b0606050907030608061302060702061606060305061b0304111011030a020601230306070807171918050d140c1c110706020304 72
    0x2019907001d000c01031000a0100f00510401070f0f4900c0c0860010b00b2400c00300150b00e00d0018200a0b0505030056803a0501145c04410812681e11031102501c0c5110005a00082d0000e89020700c0a01155000603600c95600c604104c10031b41d160b4000d600b183e1640041f910581c440d41665290400d40003c040d400c55000c0190b0400750424100510f803120701a4640051522a9203424013241c229400c02ca44039003104080c820441190a10400030195030f86205141d420544c1c2c401e41041a410802e03030055101740181d40c403050182d1110007140140009032542c0b820440c8000791a014240140c11400c0d00d902d112230203850458280ca500c0340d40180041c44240c1301c000c400d8920120040c200b030708006d1840c84144180b00d02d02c0066000b4250880101d00703106181510314243e4103214190307100e00d9a40d10078000414030014015152480905107000d07a1501e900c065141c62081803401d440e58894040c2081f22119000c003d0f00c004821075030b80411018180203c907403242141e2040000607401030000f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 505845395 1250 505844145 505844149
    0x6090903040920310f0e060d020603101d010b0703140f0a03052e060e03161403060601080c0f090406121203050c070b0118060801051006110f030405 65
    0x42c541c803010000400c0d0340805410144800d9848401314110b2100e1521215030038441a1800720548000d440c454842d180c10f1142140360b41d07080744030f03003584200da6502140c403688500540000755034001c0d2480341e43e49401d00000c010000548036810030f506400c06004c1058018407031b000d05945070701c20020b240031960f0f00c007219001d81d12508100d50305000c02c41021070540000c010b024115040d02d001c1003c3c50056041d8280c0840c05020b0601c40c0144a140c0051442582960080d5181400c029007240d1452000c6803406c1c006450011070303422120300125000d0400803440c24104022002c0312101d80d611001116100d509840700100c090050040c1140074409502400368018098400a03620360f889140d404100340e0303802d09486403804810002e603441c3d494018254008000500e661505401c0c0e99640c036442c0051260780008408589806428803403038100c00c0c0100240c0000703100360300301a40300c00e070402d107503201c3c2070041110001030500f0081c01090300031034861a41c0c0074504151900003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 505846645 1250 505845395 505845401
    0x6090d050a08100503061e0a0b010c030f17010f0e0604090b07031d0d050316090b030705030408070501061418090d0e03031201090b1305060a06200109120305060909030409 75
    0x44503400c12003d1010416031400c210030340c451300b040454400c1c0d0300140541c08804081c080e02e1b007480b541c00d140410407666000103485201c10391500e0700d00101c2c040424116054071548a082c41000350800c00028a02c03500c420035800d80d81c405d5000704950b100e04080000b100c421100080003940305600040d07619000b0ba02074824565024046041e1308000301c3d10714102405500c0c100c0218034044180300815000800e000c052b5240c038200300c3c4c2254200101c80d41c140c0002003020f07003000f50003c000341c1044205c0e4103031603106510600a221064641d510440411402451103010f50075606690310381300041075007903000c2c1c031174040540074504940c84115000609515038682621040001252038031920500c1030003451352010010300590f016040108000180107030324601800c12061009640e6088000d9084910a0a200203001050011102040d40f100d07151b10255103032076032000901085255001d07505900da41d04101958a21041102d441410785a840352540305100910604010b80c2c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 505847895 1250 505846645 505846651
    0x91e09052706090c0d080d02030604061706040209060402091509030c061809010605040e0f0402030f070603090b010f0303020a0b0408040905070c03170105010e01140909010e01030506090d050a08 85
    0x4035041401000503a440751061001c000200180d0000c42000008001070254030004003084a040807451010340320440c45000300f00b12012420b07400030100701c1c50313a1541c0c0024014991607501c0c8880c1c1000140c101d8071340400f140c050307005601c4007000175194034040c401c0302c0c60440c004003599810615521503246070740100b05d40c65018030840502c9103895643c0c0000c1c00b42d41c0e5483d03200100c000d15003000d0004a15041c2d01620505c40d0a000a1088868000c0c1180d80408220108a282d60742c1c0d000003460301101400c03211030343c0100800814141d5041c0c00030700e8510b00600703102c5020790340c0390741881c4a00c40c1c510014006070002c12a000000d1000440e0079005401200b100e0300f0151a5060a4100d5100b6038a241c0482c891540203003c15800040c17004c89c0c040400c08030711140d0315041c000f91825407980040740c10448011040c07100341d8003907001d03690404400b40149200e982c64100c1c2d0800f981007800166540c0c85014001140d4603000900312840d01600d595071410b041d0009801e44480da805 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 505849145 1250 505847895 505847911
    0x7082109040609050f100501030c0c0b042303040f05030a0f0305031504023016050a030906020d060303201009020d02040e0d030b010908030a26130201091e0905 70
    0x10600040c5443c0b45005240c015003000600f007400d41403103c00340340e00b2000d80d4007035818182803a828046982d000305113103040c150800f0061015130307241e28001e4a400341000200f44070a4201c080401650400409401a500e07800f5a407841c20ba2944c0405a840340c20350801000304001c5a05480004c0c851000f543c0c21440340c43c030080b801e60044001805a030015401d5140c0c05c0c208480704000d08075101c401d03501883c0f03d059081160b0503c83c0c103507001400806028030920a0002d8071009046c4a54044030069410500071902c0d280030800c15002340c5100e00c029000520840b6254108500801d881180d5843d41401070580d406070000d007001400070608240c1e07022300c840e0080c01c0907031120301950141e0910303180a04086560702e5070207403c446580306c2c01810010402000e1060340300010031140440c420741000501c003003117180d0f40e89031011010303900352805940c1c40038081000e190010030400c46200b601c5850305a900da840200e4604c1d4400c000300c0303003803103d00c000f0020a10503074440ba81084403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 505850395 1250 505849145 505849151
    0x106051b0f1c051e09030f010f0917030c030a0b040b0405100314030f03040f050106150504030210080903091201150b190305060303030f0a2c0708210904 67
    0x41121507081c03a006101a0341e00c0e8005215004015000160007641400d10341010f608101520702401071143c0e10313416010f1007100000e044591070f5010043d0031b550f01490f030000e20018080700240c401500700240c0480e00901c014100034544031100742070b40e12031210ba500c0caa056588800d01c035006403a131030000f80d130442d075504100801c54031180106803040c0d1901020f005200e00c0d620b04035001644500390012603801c1403014500882c801d4048980054100109a445040c503090040c010205a4842c4881c01d41180240c110a60081c010b0310499008856440068a04150660b480201198030000070f400800100e042c030300e801c95450b07000c40312000c000a1011400d8482841020385a004145441008915841010b60f804030f2500382d68181d2500340032509080d0301082d80ca0002030320b444441c20141002410a00d1190310201c445103140f04050b40c06000b00500300c5590501251040450080140c003190744400010758280b40c0700c2e4403803480214801d2213003007407098100d40fa03110f40c4592 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 505851645 1250 505850395 505850437
    0xf040b040c0f030305030f0c1e090a09150608090a020f12010f06060c1b060f08090c090708240307050d050c0d0528080403110120010c020f0f06010605 66
    0x285841804000d50b00c03c0d00c842d0340c0c80c100104038041e1510001e2500b10148e00c104000000c00000a02848801c1a240e9125846010100c00540da00d01031360485c00086141c084c010000c81d00d120780c0d00045501e2900c3e03100ea1503c4901c0f01c1500d6124001c000303908440c1140d00e40c0c1060a0610300404000b8595000150115035101014140d405c954000030008100c219120b041c80220494419a400d1400060141c41d103050b0002d0a91007541d000f031801e000010001403445482072002010814000b04441c0705881c1c80b2101800300b56041e11415840c0300e60000081d10301519160398480b03500c0080c02002c3c0c040c5003800304540203540c40001c8459000300b1400805644071603809200031031144024050707140314040031031007600c5200e21040c884103148421001082911013200c0c00c1e2234100180c040800340142c0107a0700140c000d5510550080d0103c402d4460b44010344c006040787c281542074070002c02d080c005c1c00387d03500d08041e44585a600240010010140104000c0150111069074141507103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 505852895 1250 505851645 505851659
    0x31b070b01090506010e031c080606040f0605070605010503060402030c06130806010e0f090d0f030911061662070302010c0305070507020f210f0d080f040b040c 70
    0x40003030340020b11864944040c800c00d50b030803015110403171806078010600d600a040f84d180c10345140b002d181c401c0c03182c0306000c140380d51030b5941240c01921840c0700c55201a80d42e0003005109902c00f600540b030b054a004004282840c000c1501800381d50000d00034003401c1a014200125039000408203c2145807a0340c0c00201d146043c05414020a0030045044003450510146da051080082c80c008031a00480c0d2140380494000002ea507009189150004010200b0b1604941620b0f0000d01c084c2d02641c04105c0c0f1a4940d0300804090b449442440c0c019003c400d4805440348a4203602e11441144130426482510701600001684844100500460102c04025110b8030030460008206032002000503448052603024007401c0140f040501d4100013071300e058031009000e8001c0030b070020b22a81020754520b50941e16035880000c000d0b886e47d441c41490b1176010391595203004800c4504103d00030315650a00050281c0802d51007501c410203140003a0b611943c7d50007a030000280100c502d0458050046114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 505854145 1250 505852895 505852913
    0x20309130f061412010603021f02010204031a09120309100b031e0d2607110c1003060f0b1206090c0f0304080403020102010b09042409050d020102190311031b07 70
    0x107107103920b6a4014000c060090100b500130442c2c480856030304142c0c0410060b02c4203000311402c1f0200d010b0f401244010340100b24061300c0780303620291011665410500ca62000703180a9405000f0300000c4a6a0781500141c03000b6501080340e552110f5000f03140a0906400a90002c604606000b020340311901c003084206814070b54907041c100c0e02030f4805000d03c0d0f402d54100560420742d80040108280159900507030601c0117000034038810800801c4a07901c0380c0414100100c1d15009030042107910041e0015900900620b92481749010700c0d031100200084a282d03cac030855141307809000001103a90743d0309050040542e03000e0f1880d11000410000155081030300d2024502440c400c40300e05030364a155000082c01d4540d46010309109001c01030a100024043c503003130001c541c085000306440603041c0500302c002088183e0001d0700741c1c0940d01ca40400c5035419030003003000011001199128414001045044411a074480301a8250800201e076035520040d0f1034224042c4040c8402c1e04e0084c007550380c1440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 505855395 1250 505854145 505854149
    0x20d02030109080a1404050a06030e1507111e0706030209060c030a08192c070e01030b1b03100303030b0406090915060b070f0f0302070b03150109050d03020309130f06 73
    0x40743d0b000300d98107030308a070700840000301112002405800e09050100186420f041e0340704050525545000c20703802c40d03800f030003200d010301e0610810501c0392402c410040e00c1181403200b255080c0c01603004c1402c1c0f03a18410050410549034200800c0421304103503042c1c00039801800c6450f408907061001c0080040100001c081c05807440d80c070b40c2c055080c10440c2508110703000c0300545485040c10941200007150044010b0a0403011210001202000541c54244045500041c0e5981c452000210a000c600c442250052420144454200c003010300300320030f98002038804401b0908929000c0000c42e11a0300207140c1200000c000080040c0d030307012804122031074034004641c90a001d078504050580103114040c01014130701102032400450765144003035000c02c40c40051240035130f44e031840c0c00d062003088240040d010089525903281401c0103d6204134900c080c20074009821100701041c1030902802c0d0742c1f20190f25400540c00c0840c114100685012400d8003941c45545e90211040588610302500c80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 505856645 1250 505855395 505855403
    0xf01050403080c0f0706261b070f11091e10051c03020f061905091c022109011d040b03030a0e0a0902190c08071a01051009060516020d02030109 63
    0x780948900110f082c0600740c2e0103541403012504d0447c0600a018100d03608036210000c00c402103549800c906c02c3c000d40809500c0e1b000c43c00100e41c910400c0316450081072041e01811442500c00c0543c0e0030040000c40446900710301d020742d40d24114110042100395070308451181c110840860312000480d0340781000e0300300c070480c849805c003040041c15010f00013030341c6612814014001c0d034545442d1848038980703402258011140c0e550000b40c5003503000e0111044d070003164014a4402c1c440130500942c1d641d01c01208201061012010051700c1208404860b04c52406860313000e029008441c2c0e6050360801100650341080e283c400f82c03504d9a07002d01c01840030b4440760b00c82400003080e040501680031511341249003d02d1040008625010f00500c141410044615001c4d02402c120b01c1e00600c02e000301340c002842900d0a8800c1210381202e0f00c4a6410b03584107441c03402603110701010488080340316100d6800410b00400c840204841c1080c0301c0303d982e90001d441c21400320660381c08603003110344400c0b040e2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 505857895 1250 505856645 505856653
    0x3050a050c1c23160f092601020a052a0c120f0601030305040f0b030105060d020c15010803030601141603032c0706300b0d02060703090501020607090e060f01050403080c 74
    0x861300c0c400c4482000d2140302d552418400d1401d98000141140d001800340c080e0b038100d600c030310500c205081c003100f0b090030114100035515080641400350254000602c074103108915000014600648100c01104020311140105a8035401d00280030038401090084091402201d02e50143d1840030400300e8025803295440d10f40c0e440c54804000d40441c40398201d1b002c51070301000108159a200402d481e418812004010782d201d507080900c03803030075a90b900f8190244000c01d0000030340c0c0300c010020398414034080c0c0b610081c0303580c00c0311302c0059441052940c0c6e01c0f21007442c4202c0c000c688603a114014008090021b0400f01c00c004016004254114505c4401580015428080d042d440750000e10001c0030402441e01c0d0011003171390341e100f42d0010102c00c0481661060178000d943d0321511000341d07254014000c41c1d41c1ba41203060060240f4994001d550161150a0200f590b031842003201c402260800c486184560b1100020044c10300c807001c20b4513040003804c0c4008800f06490600a0641c070b21268014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 505859145 1250 505857895 505857901
    0x409060903170a060f09020f09031618020426010204090e0a11100f030506220c090e0105030c060f0d05010f030512070305090d020301090b1603050a050c1c23 69
    0x102e481d222004045000c2d40d424214200300303401c4100c4201c0141e4080b030740e015840d50b012400200b46030041c0d074035541d414811001c1c0d0038200f00e44500c0d180309540034260060032601c0c0886010381644618400c02e04007812040f517a00150000e00c3c4641603684051380094a407039542d8241c501918189111601541c01c41146c20040140c2150650000c660664012840342d60f84040a030030204c3e600251018140c9a0303000459560310150f941e85801080d410800b240e40843d51207200505140b00704e40d020549a0742c3c0032138105196460326048580080050110038841020b03c041a081106145c41d55001488040d10205c400c3c0101c83c064404141c1c58103541c0d146041041c030b00750800c0c2824070b403480c0402c4004003280d48501200e04445007560b002c40d880502c0d02c0801d0040071203600140100780d00360103000e0000706215407030b591040241e5062003d074807004941c03030843e0029901d0703405030b42c420018080003004641c110341c032445c8640c20009811a10f212907403030300c2400c0b50f182c4d07041c1d0640c01d00b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 505860395 1250 505859145 505859177
    0x3250801140c04090f111b0114040b160201060f0303030606080601110709020d090b0103060510140904020d050f06070e040c031a0d08040803040b0a03050c12060616060f050618070804020f0409060903 87
    0x31309c00b400414002d0302d071102d0603c2d480d04950000060b14615180c0401061021114001d4000340000c004218100445a50b81d060045c01400c40e030084500281d0b40d400840d64a40c800d120340e0601e02d8a102c0035200c0186031900f210020341c0030a1601d042c9940b0f600700303980402da1040e1140d00940c01018040317040d207400d160f182d44003021500640000c0003d83c401440ca5103840b00f420b9441941500c01c8401004a420300500d00f41001c50403410500c5014104180c8a40c404201010580207540030312040f040041e041e41915110860102810300c800500b9206107403074591120030b980214860352629845e0544070341558019004805c2c0316030000b401d9070480342d00d4494640c1c00f0380c5c040c00042c01c1503080010800c1900b80a0300c540c0c0b0030800454032001655100b081c3c44507495024a04000000d01d41c82024050a0100c44071885141c040c1c0d401c241c01207030840b01c903205161a0b540e424666a03591300b00f002051240034185c3d0419910022080041d407944030300c00300640282c031001404403000003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 505861645 1250 505860395 505860401
    0x240402030a0606020d0f1b02040b03030a0c021009060210020310030c0312020c0103020337020c06010509060a1d0408090414151203160203250801140c04090f111b01 72
    0x4500030031070303419401b0b51120303072085e0801c190782c100f039801c0161005503000040c0a0103090300c08945c1400001595118150000f070700703e50003407080c0c1e24840500a03030030003920425001d12800c000740e0040c440c0c0c08040c1c0c51582c021a4040d61000d011000d040c0c4130f441e40d81803418190400c48240d000c1c1da01104425404000404100d0001d29066145113009001c00301d5581c42100304541d910045401c0180209900201001c1d40ca00300404546074070f100c50410381d40b07140a01c2007034069800300e000b1034100d00380001b8001c103030751008807400895490314003c0500b000e401441030311000f4051160025991f00c0e80681510010440005003040c01c1c0a4980d98000d600c0300d440611658040346200340203503010082d80c4900428400c0700110403a1070021070b0814015081002083c4550030805158050304907403a01a0b600110080295401c00c0240d2045a102660422510901400200864245604a183c0200c0d12803400b140d1800c43c217980c400d4a400030038094084502024105204800c244 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 505862895 1250 505861645 505861663
    0x1080f0606100509220204051503090c0907090f060305090d0207030b0a020702150f030912040e0c0a0309170c1b090a0509030f07030c1e0b240402030a060602 69
    0x1024040900701030700020b0b40074040c031403118203011012600c1c2c0065541c0c42c40c42c401c2054204000c403000800355914500a5102e8004d45100b00162100a041102c1d820140e92044840b03400801c6940034440802c00040710007400501000f813003a401081c080c80712800ca400800540d2004140b074241911601c0c10640c1c40e855040440d0f01608040011480da981d82a0300040d44000040c0d503001320340007244842c00865201241030b00300090442d800781708000110301c1500028207450b000b8400103952525845070307120328803d16400b900402c1e80340909000424031441c44d410b00042c2c422803640c0c2c605020320b00300840004ea410115190800840500101c03145089004c4601a6000041c001504e101400b0b054808001d40d074200043d0303403031000c104494008008048042d251215450020481c0090100440b126140c188100c00c0100306105441040b65100399490395070755421306481040c0107800d03101c203100480c1880d581d450b6240c500c015070080048071004100d803428000c0203440d203a03c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 505864145 1250 505862895 505862923
    0x52419030c0c021e0303090d0b01090b01090806010306050a0b19060206010b0a02032d2704020306010e040c0207051915113d0e0106060906120902030a080a05030108 72
    0x26642d004010390b80c00300364059485001c91038401000e01140801e1440c000d10180b1074215000b01d40c0d5206025100905504980c052041403260103610801101d040c600c0344221252a0301480060001400c1504019417100405074000340c1d15400200040c0200c00d4400d20407031840080b03405100d0303d80e05010841c00740c56024003851415030203580081d6a407190002c8071011070396060031070460043d0302a049440c1c00d100c80340c4607207400f44000e5444034401e031000080c62000d0104140e0005051a00035640310b101c0517140c00116002400078030011b0b0456942060840c096080046071139a6428030110300e1014211201c81e4803401c01d00a40340701c00054000c40103126000070300500781c440026016004034154804403064654421941d0f8595607408192481a08480c400101c0300d86180c0c04521502c064000900c0704942d81e40064560384410301501000071078509104c14171940c41e8100504543c03000d411640410466154122150010b0080d4000100d00000420038040200030f09041d241135 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 505865395 1250 505864145 505864157
    0x41e1b05010e0319080c340b07080703030f0c0f0219020f1009030b0109090302010c09060503010b0f0408030a05070209070905060d0e030d0624020c0a052419030c 71
    0x2d80002542c80780c22840c50410014100085010814107405503103592168004443c80d0000d407440810b682c03000103a400c1a0f0828082030701c40403103502d181c5042120285002e59141001c1511010619401141c00794203058039078a80c1c8a0740705803441898881040c0d42d803180740c0b040c11480000e0521140450a920100c6401e4861001d41e50342e82c111103030070b24116551b0000d081240320940d20f05010f644058903031070700f08000094010030750308203d5041344a82e000f0803882e40b0901003503d540c1450702070200024400e100501c41282508001d202c0a4406640315051507501e1a91501d19440403001c4000510045500300440c102000016008102d5050891400d800c21000c1280360040f030802010700c0c1c1d00d510744451103907414812501024181801442041c1c0c592942418588410800201601c40644501003041c03020403a80d4010800500c02d02c842c510742010081c0110f541d140c81c10300601002015040b00c4803550003084200041c82c0044000100d070312000d011504a140d1801c107000c030f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 505866645 1250 505865395 505865417
    0x203220f0605070507050103021614060106080a050709060f03020f1602010810080c0402031801091410022506020f22150806041d1603120e031005041e1b0501 69
    0x4e01040480c1550400c1c84c005869a4640c0c83d400100303c829a8080e04017550b001550b01921800b246082c1601d032541c40d6030080c0d0b00d43d01403c070700b1a2400ca8808000801d072160130b10000c2e11510405050907242e150150521521813550300c61640928400150380185801d20b404550b001240d06901143c0d14500c2e042c4a880c020384551580040c0c40541e2140360f0000000d07003402a0f012440c4019400b010080248081500c0c020464a01c0608185028800d02c8080030290b0740500031034000751850707030f4100e0049801a0859a038814484000c4a103260284980c1c4010111b5030081c001d2504503c4001e20301c080c000055003a0202d0310b030800007070f0310900d14040fa6026003183d8038a0300b00c942039400045402559020008070100041c0181890003501440c101050288036982d0507a07000341d010044201344510282c507500c41c05c05503a60560480b517040d650403852503101d560705c44e016503841101c01c54011031451401071031881c1144c90f21003403c0c03061070300307072101d04c04d100540028208010015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 505867895 1250 505866645 505866653
    0x6180e0d02100b010c080f0304030206150109171005070504060e06030408071b050a08010b01110607020d050706110301121a0c0f070f060c05120c03010b0a0e010203220f060507 77
    0x51076041c8504100740c41d1200d002140c0d05c40c1072070f2600d03540c101d04106e44815528a40d03000a40c4103441c2580144917501c040f071f261401d003403001da075045e10584a080750140717014650100005501e10b800398138021a500354048820b2400b605100311141c0d520300b41d0741c5040040240454114201090251030140100400584007500300c0e070000ba00300c1000c482c0c00080da240c403418184140c0182d034222034004800288910b05420501c6240c000340c848900c01441d0940140c2d54400c100c8224005038000c1d1108018903006600a0042034000c0310085006012454030400710b82c07080c1e00c2a114200d0524548003840409150b0300c2c4c02e8001800d00c144103080910610f00f4500a5001d900040c01e00011003104000b10511500d400d140d0180003031181c1245018003034078030340044103844072002c00c0f8000110403041020441e41039071414031040703042414110007102d81c0b1051003400e07410352108200750f01c1641c0090004030314500380300d01b42e1075400d030a2801d180c0140d45140c1c4620103002003808075a0000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 505869145 1250 505867895 505867903
    0xf02060f09070513021309150e1e0709030605040b0618070c11010e030712020405090a0f1e0f0506070f020109110d0c03080304080a0f080f070c03021006180e0d02 71
    0x140c204503461103209a020800700c00034031444040074001b0343ca0641c0002c050307485801c40d94500180114034001b60b43d4805260444050850b1000c1e80c01a41d131018203001e4200c21485900400545446800c60b40c03a80c3d1104d08464003a02c007a1802810081009210b03e841c15242e489010030300ca01100500f05554081c00c0e080840500a054814051903611a644188120b90301164010101e5202c2696282800351030030030100164016400c01c000142282000a64000300d9a070242d039401c000c0314243c45404411305503155100c0c172904c15100e501c1c0421028682d115100e8050301c046c10480c1013480c0c0140040c2140402c441c190b9040504450104039903d00040c1542d409032a40007408280d80303003440391030303505400c001c00501c000310503c4240440329010f008500b06907183e1805441a140c2d0175144994100e94100e1401c00c4600000d0303081c0d01c1500b000d0145031103401210742400741110108181d0781700b900200043c0b1024100301d040840d0f07601844400c1901440605081092040001d40b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 505870395 1250 505869145 505869149
    0x6150c03051e030a1107022d0a09020306040506091005090a02041a0c070911070204090f02040c0309050c0f030706080c09041103041b0509071b0b01060f02060f0907 72
    0x14420448018000d25009604882c2e82c88241080c039055648040a060300d0358100362640401186004203840003400120200c5280b43d40080c049240b9100320b4202074640e00d01d00c1046214820006c1210300306489040038100540400c0c50050b03124a808002e100440743c000382210300c100540e50a110320b803500005403c040e60f80c00c0d01c125101e44d494080041c00b074441c0368000300c01e41031000038441d0403c00c504081d042d01008141519000c9641c1c00c2000191000c4606a60f001c0ea404c2128070018680760f405240343d5449202804400c42c22074001404031110800242c0c007207a00d81a13024100034060124003200c860840c0c45a07a038107581d401081e41d03080d541c003d00041c842e402c030120310f1050883d42a0780464200801c01d010384100c80d110500d07150415102100c140b1b07030b080d01c10078608848401940030f445005d0201d40e410f65403c48115020311140780741c0789d4441101030340781000c6200b45400602800ca69103c100d40d0b08802c4d6802841d000008215400d103e08090501408a0010a070041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 505871645 1250 505870395 505870397
    0x301031e120c02180103120908010c050d0c020f010c03060f0605042d030f03050406110a02100302090a05040509010c0e0306090613030e0303120105040c05070512160c180507030615 79
    0x40c0c007040c3c40803d0180000c0c1038072042980f10f150000041243c0001408101d40495a440910fa0354620f001401d0300d5184000d84081042440007041221999001601c100700742c1c4120b5465181c0e0144141c2100c2e0300c125050300103a150300060095043c0200041e0042000d85400c80c5000d10301210b102c541d80130f0307030300480602c1c0e18401501c2070038140d0803852002c1e581100d0354032052030343d41ca00649143c0c132510411000c545004041b00241502084c5072080302d4000d0004103018150700c00807002940a490480d0344642c0d01480404d4507211031003020b204514000000172a15807038040076100843d0700b03205510907800901006501c40011034415004138440f20a480703100c40c0340c47d069500d9500d4030800c070f40512000c181c0313042d184003001e104d0341200d0058404101c150035100c4200d8451080480181031a401040651030321480e074030050211030519900c500b413503231542c0c0c0c0741c5492040661001584140001c03440344030b484103100d110741098050400b000124500400030705000510003000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 505872895 1250 505871645 505871657
    0x609060e09041b0e07020f10091109070207080d0306030204050f0c040e06060f0d1409060606040b250803160504050d080901030b0a06020d020715090e1009050403050301031e12 77
    0x4a81c01141044809040c1c808844c41e1549441d9000a40d9200390f6880000c907032042164150b8010068428280308940121002c840c00c02054140804190701030700d1042180308114001031640381c20301c005180e02d03a6564000c01d0b514036600420090300c00141004070140c82d88410700c42c414041c00c0480c2d0490b00c422060496039543c500000f070305405580701e05101039000003002d194246a90f404039543c210521042285915040c0700584e41e548122002900b24408100034408000d1400207407440844a03200181c480020329512601c031400c1940c111120f0801109000b240a8441c80280f8609028508281000c0c50100029600088203402408240000401c80c0c05a40b0030380080c1080b04001c1c00c850b031550750b54080290380d040c0e030b86d041d07c00600072040c3c00700c1d103148510b42c5e054000c40107030741c0d0805a5041040d40045803e000e400c031b4202c64040c900005921016000b42480b5a00940316141c80350700d541041d4a020f2407014003408040c0c525021600010741d1210490140c4029162003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 505874145 1250 505872895 505872923
    0x22d010c05010f06060305180607051605160f080724050c0c0409050708010609050606041a0d1103010f060c0b040b0709120506011e030b0705030c070b07090609060e0904 74
    0x101c2c018021a01010b02d01810000080f88868040d0403450288421000200715003501e5074040391a40c1303048d66600300040041044c100c0c20850786d408201102c0c0a0025a20703412441c1031040c0e103e8007940e11446220640035420002e450f8180400b43c01000400c0782074120000c010030080c0315440700040d4030140303d00402c016a00480c02c11503650000000f0380700f00003110030740c2040ea65818507031203640034039805d007070000c03a030040340d405201d000381c1002d44480c0c1003d0038401102d4001c030485440300445803061048984004281c0521401504a5600305a4a50501d0400c0f4281412900308500303000a000f40400010045c584140c0d000380c120402c001385480d414070407503406003103a001c2c8141c0c2202070340150600c0b5001c220302c0e040304c1c100d040c40f030054000c8000d0701c1035091041c44003600503141308000440040c002c0380115804003000a0a52404107255102c1c40c031210207a58501c0000c40e01c000c1400490307000029580a00380e00e0601d465000d000f48005200c030301c00240001c0500d4081448 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 505875395 1250 505874145 505874153
    0x8060f0a020c010c0e1914040903020102071b030218060d03031e060b03340c15020c1e011104050409020609040c0c2d080304050721022d010c 62
    0x5581802c41018000d224603181910020180d4044040b494810400c9012214280da80a400502228200802014400450b00410005040d80f84065003995000c05c0820001120034070240c0720403800000390254941940188514400d206940c0e242c000d45607414000a60703991200d5014955043c0307404034031219070020300c2c00200103030782c0300b05281d034207003000130403a26501006540301e6052101d080b8902004a2910b88060301d28000054a82502c07505502507244108a007110090040c0c280903011410324901508a07131101149421a41240c1507200310b901c0039181c041c094004050090120008100303411850b40b140c0c2c41140e11840c0d0341d040020031034688000359103030001e0062042110b11041c0e00c3c00b401403440c50780f0413201c1d4440d00d0300a081001c4150030341c2d101d0a4103088038a4a00480d5138480f4032691018101355800d1040d0880044d040480d00300302c1d0340c460346200321180404d016105106040e003002c08920110ba1203c0441c0e2212100b081c010410450b00740780c00400381080d801c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 505876645 1250 505875395 505875397
    0x40b04020301110408010207060b040b0a0509090732030a110f0a03050607082502070501031e09380f04021210090c14030a06021308062e08060f0a02 65
    0x190b0310f001c0c2500450009811401035000c3c00d011400303000140f22201d81d8a04100031078150f0381c503559205d9084942480b1605004200d01d500041d41411902e86680383d01081c2040c9400c013000f40950100000c001001100550310303038680c000240c004183c3e13000580ea54240c5114a16482409081600e41c0302d01a680e0b4542248000e54000003a2a02400d000c4401410701c0700c21a40704e80f60140c0d5859183c1c4e024600240100c0e4070319142c1c00390402d90300b8035004601030015014050100c9065508000180b0514490106858460103503507000587c816141206110a103043c04c0308030440810b42080460361001090b404400007100d05569a210b02c0011034851034024284450707c91100204849401c0e44d012141c0700d0b0080c44e03101104d5540304010700038440303081001c0360550440000140000c1042d0007521801c5205894004d10f95140d03411286840f0741110101083c4a000c40600390034412000340c2012403d60704800407403d4101b00049a0703405010741003a17241c901d00d000090881103954 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 505877895 1250 505876645 505876661
    0x20d0c080d290306130b0c1c0c030b2b150e030d06030b01270c050c030c0303010e0a0209060f030903070c080f0f010515010c0507050a030c030b060117040b04020301 72
    0x8007040b20751030200303403a1565a0810610880c001d00ca4400840c2c061000d49481c0c81e02d0301e501c110002619501c04421a41c66000780e104200103c40146070961600124014003010301840e40e00002d11300c03581410445d070402c06400c1800c5142c2c400f040c0c0301d0f80d164080d008018454000c4d414180c0681c030244008024030810784141004c1c00041462103c0c410070b0340254003101e000380300281392640c0381e06106200002c425542e04004051620180891455030000c100041560403d01d090010040c6590300307581c062070030300725250400401809a0f2803c0500290040300000702103003003810207400303d120351082111502403600040f0000756100030030412242c1c41984104041c1c2c0550340e610000e50703202040f0081c00b1350b50141e0000c200c082001446140d00c6170055015198049481c4001902e44040c0100d080d1110b000b000320114041e02d401c0c4901c1d00641c89443c4802c8951b1841c00e0000d0400c401500c0307170707040001c83c4940c405003501c1c0b142000e41140c0c00c01c00d10030883e144c600c0000d005040389 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 505879145 1250 505877895 505877921
    0x4050307121a1f060f080106081320030f010603051f020408011e0e0f061b0f0c0f0f060103020a0323250603090c0e18070306020d0b01020d0c080d 64
    0x341007000044150107202d034034a20b401c2a00c00c01072070344030301045d82c901c0c89101d402c5c1c0c000b68484004000d10b40c452001d080e082422802000401111034640c0b10f26034081e0651450351a240d002985000c1c20708100e990720207070005008020460079651402e89910401c00982d00c9020322018080c0310b14029030450700241b001a00030080b0302e02c0d00f04502004004403001d60b5507945031072405040c02c0d10101d8084050200003024064603500e04400520382103003481d851941840600144045011010040403407540150050000c0380d180103c040c6000034862001c41941c21020042006031178520291081c1c0340c1c80342c220200e01c0c41210300114103c2664080040602ca205494a4186c14000a00080440501c80c00440e65120281034042d10702d440c03c02071001c4007180b400c2161040014603240c1008007001b0803555600b15002580c0341c102550002d0350041c3c2e001a002032a0040c510030b00410450030f0010b07050240884501600e00c6220074000360002400160740401c2c60143c1d03001003001008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 505880395 1250 505879145 505879193
    0x3010f0905100f03050a0b15090103080d0f0501090614030d12180b0a0504020a0504060501080f0403020c031f15060509010c06150b0c070f0b070f020109051210060b0405030712 77
    0x103241889640c5110b1b540003a11003030b1615020420040141c849072100c038401921748c503040d03440c554404505a10403410011500e0340c2d11003003a2030040a00965000701a401d5000c6207540c18100d0041401241c0d1034000d100ea03200b14070703000045030491340c0c81201181031080003e15003108004149000d030b5891000300000036040410140851031f5101d03602407802528400385060311513040c4012280c8601a01d4041000680000d00c440c845100300c0b607000d4420710540d45410340c640042032429800c04001c101c209964041c00f00445424031034000c0d00d50051402840703180c17605101820394801d2806031030412100f02c8102c1d00b401210341240c2030324010682c0010071113640305d02481340c40d0056454100140580f40c1c0028030005002690030940d40700b110b00798900b24031a40d601f02c1c079070300102041381171003686a40020035545001c50812600c1c100c0014001c6450805121400c50318940c110308200701c0144420300031914001400d6098813040044400d000c1c6060804402d01c000d107100e400e03d5030b03117 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 505881645 1250 505880395 505880399
    0xc0e0903071202010e01150803120a020f070309090b0105030f040b33030c1e090a0f050c0901030c02060f13030315060504050a082b030906110309070b03010f0905100f 73
    0x3074150302020517561188002c0100c28801591400b90305241e03c140030440d0300600014000e26051401203410007070310320b401490b101c9246203844094104c1d80302500400c08454040201c081d490141c5070344e101003460114511701d85020350300340114024001074120070180300007801106181c01603c41c0007113102c40b0100c0f2040342c0504030b1520700c00c211969000b0b005200301030310703c3e09000d920304100c5184035010809500c48041072042928004280c03a000301e03129804103000707141520407035004a00c4c5802955407074002000250940d0f0444036500119441402080421031100840a80080003282c2ea507000108500f0101c015110200c42d018030392810301c0001554680010040c4220b42d000c0c0c6500340721595074062180ca500e5000c100c078069100c08082103100809400416580c14100c1c200018405400d40f40d080840c0c40e025007190030040004184120700d0707c2040f2800081c00b01c1031945103990f04012803040050158402d403908151a600801c558001620a41d00901500b4906501e865 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 505882895 1250 505881645 505881647
    0x120302270924180730020f0f03040602030103020a080a0218130203152a1c020c19020f031b0607050c090f160815010c0312020d05040b130c0e09030712 66
    0x803c29100c84c804901111031060000404280c40003154082c03001a130300080d030895007980658400d0707040c11481c1d4010060b0314182d4810801071342c001d9004007801a1658114814422440c1c50354100d00c1503039101121000041c0d440e035110405400a10024440544406001c462071007403a00009505016208045503071180c1c16509a01c510503030140002504203858030505d000e000d0440402c0025030030000003413207004280c00c0445414641800610b0030045401840c1891740b0b8030041014415036140340f0f425458101420030099034110054103c01e01c10310070f0031405040120149018041c00b04520092000c2408420112036025000020742d140029442d01c10110844880070141001da00c040e4406200c0d5034500d206445801100f5040b503401c00040d80c3d215500300f011001c10890010001500e0081c0c00071b1319032030103007540119890906241c00245510300511900c3c1036600000c0600125101d41190012204603d00d02001c0b501c4071214641140300e581c070082e101488844502e5011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 505884145 1250 505882895 505882939
    0x51522110402040807060320040e070c082a0c010807050901031806091202100c09170708030a1706030111040e09010e24060d030f0302090607120302270924 68
    0xd8031001c502548c0034081c01558941c1d5002c1c9018a008c0c140001000410b424000c020814102e4001c6d11094240540380c1d240c5800503c2d040804001d0408034030349860480020014550300f1002401d1003406850320840050050094044031810980c883d0881ca01d801c035041d03000812990440703c14404c0342c4060902444102105c41013400501c500d10907031507940c0c030034400c0402140c42580c50780c034200c0c40c0c00c243e0b48082040450580d454000c4880000c0d40410030401422822500d85981070a410312103148400322030300030096802130741012005490341a40360100c9066507131004000410344c89881c0f840d801860302a000c80b2181c403590441600080c0c105003c0d014003100440328103510381c1d806043c08002c0801c01c0004000c5400c411046102500a4002d000e010070050110303410070341c45450f00448050300d915140003207030780001c14114821801c180c0c8885601d40c80e160782a125a9040411000b500040020700c8140c8c03859034018241507407443c00503401400500c05171406095440765a41c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 505885395 1250 505884145 505884161
    0x4080702010801120b0106030203040302011b1206090b06070f14060f10080c03060f0919060509070503060103200112150e011202030a0b0705090d0515221104020408070603 75
    0x70440003030001440004000704c0003102c50340040102005e918201054010303420240044081d55260000142502d1b5617190886498046139184079007124022410780848120350880c004090910045c00d900c2d860b5401221425644a480800071103840d05002004100345182c81c0001d0140000f03101c0c181c9502c2a00c0d03070044903000891b4a09a6540c4980c0e66200400c0a0301a09030b0000300028035401d403c3c1d60000d91104d1030900f03885d400d02886080000d1200c2d241002c80b0007981c0e4005010711004100091809050150001c1c605541141c4a0200c040302480481400103000c51646180341d119180c4008180c13182c040030301a850042005190251403401420f4000040f4400003d00344245848180300c10b4000c0c001e80380302c844507103070561100d030018403807030502a0401003180f1a880d80180b5407c0300d80200003030f180f00050b521040722026400303004c0c2401088416450282405400703601c800b400c3d0303c00400a80702d9001e001041c080c1c05164000c00701c0d4010420001030b150703003503048012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 505886645 1250 505885395 505885397
    0x81323030a02120901081f050301020706020d060608090604060c0504050a0b180102010c09180207140307030f050a1d01020f12070308010b0c060402060706020c0607030603050f0609031c090503030408070201 90
    0x208103940f2043c02c00150003015001800142c01c50701180300d41074042a0540202c800c80b614501464035100801d007a68030014045030a158000f440c012106194424140988a00c0c505480306040107905160354150203000903041c81d41c1c40c9000400b0a000c6ca0444004080107080001f600341c0d2600c0f00c5072141c000070004811072010307240b045803643c070610820700c5440558440300040780c01e00344101d0300284e6a01484000325420410b92001c03440e00c110301c06010804a004640d03c10840c0b5004001c3e01d111413098041c050300340410010a5089035030400c1d101442890120a16081c1d00100d01e4030540c0f04d490100740c0030b41c1400580728070b008030062a0240c004d8850080a9a0f42c0d030030b50341d0f82d00c00c040c0c01c0c43e1030303402c5400803800510f040e400501c03106000b8030000d410f141031501c065081540642d08000400c0d6100c208104100b804c3c0070040c000801d08001d000726190030201c440d00ca104000324144038020034004810345480980c0301d40603898000702201d4591410340f40c100da640c2d01c03001050b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 505887895 1250 505886645 505886653
    0x10b030601061214190b0d0510020403151a01110a0b01030503041409010302061b1204080d08010501030b0a140111120a1107180515121506040b01081323030a02 70
    0x214103902030003880d902850ba150240b0007540007505c0070340018402c0310481c2c0d41c050148412040455002c0000340003401c040f07100143c4e01c600d03528080c1407800340445c50178002d9062074168400c00e642c800b1150359003030080c20b1001c00b0000303800007242008500c420040000b01800e00100500c440007024101780c2e254180d10000e920911003c02c00b2030042440020361000c0f00b0440707201e40003240300091407045070103012245845541200505190000d0308100c410303500000c0514812a84001c1490040000f800c0800402c400d07080030401d02d500324001c50104403001e00800301c0301d91050402c01101c140841c10707034412161800d40d15559600080d1148000b55a03007540c1d81490741c02180325401c40f2407822180308200170120b03000b0040c203030003010800c2c0e001d481103080505840d103800346005654204040c0031801101204241c605201601c0341c0d0095281580701d0030035907009081590004803c030300e112008000f41c07900300c2c000e03241e0202520071191549068502d10000001402c10391000d60259 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 505889145 1250 505887895 505887911
    0x10c29040c061404051002070b0d0c09050411070b090304090c030f05011d070807020118050a1a0c09280329160c0c09061d060d1211010b0306010612 65
    0x200e801049880c3c1d20500e0001c10002007050349003500003800e80e0707806c2e070040e105526507441c081c20030381c2c004c00498404540ca4001d82101190300c900c0603000344c0800c1340c003001000200d4032621858081c20070000c0000a445021070301d80c43c2e0801c140c800401020313800f130103414100307c0d000300500803450310384250904010010400c1c0000100d41e01c8003261007004100c01d66035150044640442c06030222047d0356035050f0100c8034401150a039594580a0001400a0141d03860b024490444469407100d441c0100002d001d00603d010b01151000c88040700c023906c407c20940e00900d9092141718603105d203588902c00020801c03504c2e070394100c040580d03803c007455610714150544042d006d040318201644003d514580f00e02c140aa071201c15210300034003800601d4bd40f103d0581c01143c0a941101c00d038540d410b0b2070f0601400c404980142d00c54030036260503090607600d5403103600c0c2c80a0100c0000c01e1001801141c04c560341e00354850300c8013071002001c030307402542e64407400f03000c541511036098007607818a00c0e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 505890395 1250 505889145 505889147
    0xa0905070f0302010215041103101e06051e190801050f07050a0c0f110a09021b010204050307050603131e020f040c020a021512010b18010903030203040302010c29040c06 74
    0x312000b01c98041c2c024012a103104080024101c100034001c0300d401c3e482d01140c1c0c0d05038500b000341d507620207400d07240020030070064610103091203d8561103004403030905006114075251030030a10310051102401030715003100c02c1c0c0000d40c1071098040f02910b8ac1080c100010300e0300415040310703014000810b450081130320354035070840d5180314603105400486da14480d80000543c61101130700c17046001c1c8075001c4c03400d400b84002880c8183c20340d000140da10b40203c0c003078400404081c6860704a060100003146814a0400840e4076102c0d41e115051080f00c011000417114810002c0801c2100c2c0e002c400c40e101091032540046840103038500c10380c0150008103421801b814544180600ba0020760024010f042d43c681c00c114505400f2540021406414442c2c4a4464811100c07a13010344600d44c6c5c01510b0f541015260500b00032144c05683c10403514180400c0402c0d00401150140c0b50203103400c080c541c10714103080c2000140c822100350610200401090703120040807019008070701c5032140c2140141d813418 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 505891645 1250 505890395 505890419
    0xc04270804140118050d0f060510060e101d0102030412060203011406180906030c0d0b090c01030207170315130b130204140f19080a0308070206100504090309050303030a090507 77
    0x120700e80d042102440f0034002c0380b61086d800441e69208414014980c496940c4100039140c080e0341401102c3c891117000d12065800c0007144009542c2074659162804010b0001441ca855600030002040c0c22880c1c486400d920038400c480241407a40c2004000801a1030148002e6000344aa07451b102010198402c40313140183c00c80d980540d03003107010307445070111a0030000c2010001d440f490f85071095070f006c600e02c4d48940180b554502c4c0522040d201c14600b1001032828002e820f0103150406104014000001d000704488000b560841c0d44259100d40c5ca2401031161100a401d030a81d00500c030040c0002004c0d006c0e080710b03405150645041c610800c2c08e440700c90a0340124060074883c03000b0701c1800c01541c01c044141849a080007000440034240c00e01c2c54601401d00c030b80100300b103030700a00c215005058200050300e80044182c80208000e00d0000da80f6000165a80074240c030594a0f50f03124002d00d0f108044841c0034020040c240c0c0d075241450358084004048c11441243c940c091070f0b00008580609403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 505892895 1250 505891645 505891667
    0x605120d090e0103020d11010210110a03050a02070807030c1707060e012a0f12050103030c02030d0912030c02030f07170c010509100305042d14010e0c042708041401 72
    0x1806500350041c1b60b030303130b401c10000502130001d0442c49082c0039441c0e81c0082d070107410b940d400c00c421400c0d500c10501d00002c059038070003400d050700e0500400070900041d82c101c1c100d945558240c5000381c04050706240c00075502102c910b14208223100490413005000e4107130702c5078a0310140100204008003c0291140f80c0304000c3c10030000b0031060004001d030050244604d0504181c080c6003509086800b43c48540c100c03032080c1c2040e000203501e035000b1011401c0c1004a16080203150410646543c54008900700e0911031403c014100503020001c801192410800c0b10300462488040d61091916003c590881e410448542000c91040203000d104a500602c11509860f2001d00180030002c8142c0069015040c083c00850740001003101d0761420135142800300280d18001070f0b031260000032030304000c40704100d4604040b000340d05d445540c0007059000a500c01d030070720044d02c010500b0055408400b009003002040d111121241540d0302080040d800010400e940310010461000e40300500115503104403c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 505894145 1250 505892895 505892899
    0x20f0a08011202091b13090509010605011403060418080a02010b0108011517040f0212010209011211030604090201051b031b07150302070501151707090e0a020103020c010605120d090e010302 83
    0x140340480ea2000201e42d4144010002c0c1c808076140441b041d11480300288950f004d100d48030b95490a1160440e001c0c0101c3e0010403003440e1412200ea801e0154160f07601c00508140e1055640c2e007034804c144801e03840341d80300540e00592459103cac4036061300039001e0181c50a034940002c0701c850001c641d41c010002c00008520f620340e50665460a02d10303000c0c10301d800150050b91001c1a1016010060303507a030780201e2074603c510001686600c0914000b400304424030441d045041c0c202103c000040c25108240c980c02441264041201c48440c00181c41c28410410a0142c40001090914000c4e00c000000d210101d03c101403c1001c61582502035101d5113680280c007190203104140c100c1462190b000b61004d6401740c00009600303251a951000c100c1002ea021401c03003115001482e003400d109010038001441225424444400e0f5a104152610042c5d20000d0606901007034040780b1480950090026100c0908624002200900c0c130707654650a11003190002502c240e0041981c08241d2085030480e030380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 505895395 1250 505894145 505894159
    0x5090303101710020f040f23043305010813030f0c050321040615151107090f02030402100f0206070c11090127020702090a020f0c01020f0a08011202 65
    0x1480500310345034011480451841c03003120b1039030f91180164401490400220040d495595203841003010105d0280e80c4a15105c0304040600ba2030002d100d40100c0b001c210071500003d18521052b03843e01b4001190700004060817080407411990030701d051240040d12f000341c0311900c5da5a1400d040c041540c20321900100010450008001c0403405920220700c0248039800782ca0500c2d08100c112100d0103581c10861002c1003d400070301082c41128800c2d0b0440c0c40c3e429401294460518008524018800703a401c41005080715094404880501010000d01101541880808030025404029402c1a02e081e03210b440e406400c10705860152110084e103881c15009802c0c207603105001074074041415681030710440e03241c08005103d5605d03010f026020703242008045810180c00c4294013403401c50460410005441000316401682d07512012980c4030196960140e540c1c250894100d0282c01040c1d000d060a60001c19450b22800070200035103805407072541ca08485a82e80c0c054040560317400da81c045d4020302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 505896645 1250 505895395 505895399
    0x18200a0308070b04031b0506061f14130e0a0c11030a12051e0f040512091c030e1e130612121b030908061503030d020702032b030509030310 61
    0x80701c441c0c407503031260003410301b07a00d280c01c8425003010f0340c1d501c00002c0714180c001c1403c1216500d0100d80501d402c20807a500f107108215088005006100ca0500013151248085844e8460b000c45000050144c500c1d64075041c2c107030609841440151030b1003104030000c104e1911400c0250800001981ca500c42c56039916600c02110400304401071401910640503204204480d5141c88008480c01d402640d408540c1500c2c0c1c41d09040c06410a141720b501070410745400c00005006a40700c0160051802e9040ca01c0240004141340550b00c1141e003412072504920f00c01005003448246111501c280c07041620009031908460102c10b088580c24013845192905083c0d04c0c1c00031801c0f480070030100d1402400c00704581d2280000704072200c081b8200071000680383c8e41051103482018416180c0040c00685003418070443c410000ea00c81c01220b81101d0500da002c00c0400c29550100180c0d00741845407510709610111900000780000e00743c0840f00040390400700440d0b84000000103c0384190101000303500824 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 505897895 1250 505896645 505896653
    0x10b01050a0305070306120818010f1409040207060507021b0406030308040b06030a0212031b060405060c0a0e0616030e090408040b0702010905130608070602070501080c0d18200a030807 81
    0xf400395010190b4420020a031f284200f5410105180115441030710340c001c4000c2c40005541081d0700c01c1c10001b0081440525680045082540f101d040d1485030b114015000030074003c2c00342d5400a0102400e1809014070b454010034501d181e500c0d5004c901c24a0340804003448244c40306444020001200e0300700203004104004600f40e001100141541c15110341900080c03100a074991581c0d00e40c2d0030004000c0401100f201c0c2d040c1c04c031a41400034066900c1d16031581a00c4010041288582c803600042075450f00344120080c0301700d008000c02c0c0c1501c43e41c01d0b51a0f003007911400c0c0c10071408039240c100a040c0c94a0101840c5200f03e6103c0700151a090070300174100030300d4000b5003003207042c0844844086195a07540d034004141c4c0003003003c00103681d4030b052061868510298132200564000c410140043e980c0b05201c0da50050340a036140d5a28218070301a02c0041c0585046500f2204070030b170030174080000c0c10103e20807049a104415071590421010452200d0a03440000d24134101001500c00103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 505899145 1250 505897895 505897901
    0x108010c0906030b03010b0901060302030613090203070303050f130f0608011d0115030b031b030c0d031b0c0816090606050426031209070503011a060d1a270108010b01050a03 76
    0x220304c0240000c83c0320200600445d0003c1001c0c3c00040c0888e0700801008a1030500c1a044c90444281680611450169401082d103550b580d00002d0200440040c00d01c00412400044807504c00c0310b001500a0782c1d03070301c40b41002c0020030b50090303c0001d000032000203020058103030540c0352156155611400780c0d02e04482030320740800e03000559040c5900c810200b40660780034407994810030f1148a00e01c1c08261120205030400c061382040e98480c1c40e10002e145c000c00d0340200080414121002105082e040c0303801e084441d80007590148a0a10400b0fa00c0707040f105804140104403a8901e509000f0340340c03244025600b9004030701035512a40c4d00410300d00031807800f4062031075030850310200b5241703403500c1c40034200704040d400c45200916501206d81000b1900302440380c01c2d503059480b80d21b0800c040341d4130002161842050252001c0c640c44140414000789001042c04c84448002c01400b124101c00b8070460844040740308241d407100d80c00b8000203206206001d4441140380513598a442d001041c0410703401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 505900395 1250 505899145 505899161
    0x103030e090a1b08090d0807020303070810030f0f03170c0702240307051c0b0121060801020c0a0b01123302070807051015090c030b0303040f05090108010c090603 71
    0x1042d1680c0c0420741e101c6116094004a0825136107158480c500a0203161420b207824400c1010007401c401000016503000c415280c00c801c0305d150000c0c0c541c0329041000c0502c003541c2c001909407107026002e0010443c040004800a500c26103420460f0703052000c00500412048412840400e02000140010310344050030644002d18080c5c8200120314202034188584c20440f245404100000390500f0f001082c0f02c0b10240340200880300340036150394480024a0302c1000c4010320b840c60b018203c50004080b9642100000e0860000215102c4504611242d0f41e5444003038240d800300c03010b03000454400d00088410020f2600480740041e8a0b407207440c4c0001200107040070f000c036041a0802a2031001460000301021f0740104000d9460302c01500b0214201142c144c2446101841d1100c00e882e0910360f140c80c401101da002c040000d400442c410164050300241800f01e038580000a4080f07080070342c0c3d00c4401e0a6510944941794036a0f00c80245c0342c201d507214080348002c201e0035042048210301c29001120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 505901645 1250 505900395 505900411
    0x60507020303040e130b100f05040c0507060525020613031112030c03040614040213021c061706011208161104020a0e03061e06060a05040305060901020c1002030103030e09 75
    0x1142c160780d8051684424801d5a00e194180e1045c4c6101007440030b0b541e29190002100d100c0503c1d00351400303074000b030a080184940c1e0f0003030340c5035100d2046441c06401580c9030f46810260903c85403620081140a1402a40c040c4200d00b010902c60b910381c80c40051454171440c498103c444a00d10036440075205425842c44d4202c45204841003564075010680155001d4002000300c60b4172401c0500d0b00d5419a0464000850b45a000004001c00360391040445451190001001651282042144016500204259a031142c148603001403c07441c22084254480e6190043c1c440c40e90f2142281c41140607200009400710005220708010b681046800c014140c2c440d11400031040d00700c00124027a60401c040c00c0000c80d00740c0689d48150308052000540c40848081001604001032081e00e06120000c0c054600454001c681c4000081c000c104640c050350700a000c584891411003501d42c041e40c009403110000d8014640350b84812042d60007502d050340c0c0c0c1a240d80b5803401008061200d81d13440105510 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 505902895 1250 505901645 505901647
    0x608070503150924040506010905091905160611070b03040309140a1802070204060b0412030302030a02070203030f03011404060e0a180c090e060c0f120925030b0907050a060507020303 80
    0x110381c0c4010071040c0782c4e4403003840c80200400d240c5070a005041900c164401003050b0305200c204680464040f5806885c442043c540c3c003040d0060303003011498a180c0c41d01802c9030032104000441c1403904403082110703002c00b1800f00e54410792074200c85610340c013080c5d9004010444100e024844030b040d000036024001c50190291071034961301c0300c44980780a0b5102c0c010803c00d5001900c007056062a0040c03e003d004e81380c0d041071409207002c02c0680f00c03450a1038042c0030140d0100228000d8a07454044621a580090480340c917021a624400380940c004c0c4950382040c000c5407107608690504cc084d01c0c040b1451081010b07400d5a5016225000e40080100c4a00f05124040c2a0001940b00c5590700d000c0c0070500000695600e22000b5a850040040d15508140c00140314085400c5000c05c226145040d41340f12142ca46c1d210401460319258400403c03c00c442050240368490758a03650f1018110b901500941d482034441e451203580741c1c078981c010b441d001101c80344140b00c41c50040d4024603605201400b22 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 505904145 1250 505902895 505902913
    0xa0509030303070309060b0f061b160f0f0e011809030c060509060604060914070e010c05010c020d03110a121104050d05010c030b01050301150c060e031305030106080705031509 77
    0x19086520456080c1c3c08269508415428403403d84150015207100707072030004840803260002810b41c0110300c03c0311035951005419100313002c028462046e00309000c1450011542d201c074045103c0280324041c40352144040080014141d84103481541200c2c1c40b82500c00c13516140f103030801c000e020711034410b406103c0714160800000b481c0b0b103d098032800e480707005401181880c10801065410692000303403441e05111550581015001c521a080307a1241000c4d0800000c120069600c07042e6084003500030351800400d22030b015004143e902c0e01030219541080031a02c48502d140c2030b0f0086d5141540016800f0320b02d980006250303441411b0302100c0c0000070303060a9a03030b000a4040110a54212210b03511800e004032455010b0185e200110000d003041415581400100d400d04a500b072429000c0102400322481032117195805660052103001c00d6139034070384d40d0662170a41c0b50054401c0c54002d61074150000358805020507880c00b83e0340010702500c40b00f504559500f40305140a080018903001d903a40c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 505905395 1250 505904145 505904149
    0x5010804081611090c071a0a0b0607030309060501170d030c031113050907090515220806040b0606040807050904020406080f100e061e130203010c2003040b0f0a0509 72
    0x1c0d0100d401d10618008915001c0c007020721044d840040d20324103500f4014443c4800290034141600700030b0310143d050007030315074a51012002030030400c1111508224005140310506074140c10515203980641e20a00c801e9076114440044500c0c1020616440c1d0171a4a0b045100361098102c140c03903403028900411682101003058460764040b0341d90080600e040030040005003008481198800c21030705010414610f40400319181555440790381041000c0040c4100001850305c000000b2400030818034919291183d25031695014140e0702a02d04505040c0000e000d0f10b04041150f050f40e0700c502c05041c0c4c045c03609040c03001c140d8003d1320499100761144c0001c21001e10400901030300c4280301008012050354442c0340d02c21541303004040c3c8200d0300b0203802c10248070190007440f000e0000002e2452880e6950314440780408002c080300a5255091802d840c0030b080e4041d00320010a801c0c003c407441c0d07448840c1c038119642e1007548668074100d01c0c2840807145403514000a407032440d0403410114948000303400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 505906645 1250 505905395 505905427
    0xa050604080106090b030c1c0c120c08060a0c020304090c09241e050f0f09030a05030c0c0906090610140a05040f0b03040b0a0f1509270c0501080408 65
    0xc2601e4907036440c0020004a2402d004d800485d410603805440d20009100c003182d0303400c4488070701e51000c5400520700010081e40340130000c01090380712028000118245058618040d0901c06d9500610500c40803070f00e0100b640c425985418404d800551406150400800c0500202c02c00344043c070403c0c2c5000503811038490fa200c0e01d0803007035501d9540c0b6100c10030f90280c140940f50301555a4050041040a082c6400100b11000041e01d00030054403000c03101003030009442043e41d043d4150064814141c1040302c000080c1c2050813200080c1c0300c840081205118601c2400c80e056640018440080745090412040790f00e003c0b84145410b2201c00f603200c56a00c0550721030190b0500280300000c0410000d10040c41303580103072014591591460a2a85620300100006000c00e0810707a520140102102e01035808521091102c42e52460400d0340c43c4094801008412405041241d43c070444000c52030040140100c050362258844030318500303003001121841c400400031a0480402c11040c1d040080c40c030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 505907895 1250 505906645 505906649
    0xa050910030b0a020a091505040308030a060b1b0d05070c09020f0c1504051c05031f0f030602040f0f06020d0509030a0c0b0703170723123903060f0a050604 68
    0x203d00541e40e003c61240050008480e0f62042c4800b0a40c000c0c0c0080c00c1da4010115030880b5000f18009850780c4450001d20000c14140c0e0010812100014025540c520f05515801c400d5205205a50f100a00c4490a44440c403400800801c01e02d480c21046c0302800d4030380d0160542107840d02d01281400c1030461510700d015011204040280c0802c0c0411003040001c0020f451541000f943c2c2c405805074480c0081d00710300000d0020781415a0100039114a011b0100c403c80c001c01420005241e000e9484c14607800a41c0070b8040c3c5d1850355041d05010410650010407003088490a60003801d82c40551070003100c2d19046a50f015a050181c24614404a25140d41c0380e00500f00b290140350b691410b5247c0581801c04050049036450411810068095084140307082c04050711048090140f0500840041920400700f03039001d20b8071400c0a1082c10511440214a5044000f20211000e018440c1c1d40000b1201e5180c03010707a8610400c0040c06500344401c80d2500c4800240040002d2a01d5a001401c01e801c01d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 505909145 1250 505907895 505907911
    0x102070218010801180c030308041104051e22080d0207080a03051503010c020c0f01050f0307030e0d0309020a030204020d020706050a2301050d0204020309150a020a0311090a050910030b 81
    0x1c80c0062110410170f1040c40702e2a520862030544228040d916060542120f100c007070240301c0c2100c0046c3c10701aa0808224804c44002c000304a1032409003a003080e81904218481008500940024010681414880102a4544542069032410ba41d9010590b4402c864a5400d40d400f40415000114a403018101e50078880e1800710759454862010070303075011041403d41c0700360305003424502c4c69134000c50301044001d025200124007100c8040161042e20035412140c1d10030000208100034694140d00c220940034003107064ada12074180e401c04070241d41952001a510501181d001c100510f8585d00074003000e18511070150a12038280c4400c02110b20403240d140742261203c0c44000320440f003445550980211403298240c0f1350500c008603880004c1680000e001d01e40c004041400803d08100315461154881c2d20550a40341000303044010b90401030480021a09100846004400b045c0c00e03208081400b812003043c2a1414040204001c00a40561512620300341c001c004194280202842001c0c0d0b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 505910395 1250 505909145 505909189
    0x181f020309090c2805071b06140c030d05100e090c0a1e050d06090c12031425060e2a01050301050108040b07021f0519060501050d0e01020702 62
    0x6620a0082540c0700401e11502824104a48003800f00032142000d595034002d10201e50311100c0580c261414407038410058054154030341079a601c7c2900c842c0769000d0303c40545e45c01003841492544a80f20780201c01c2e04e003145400c02d102c60810080650311040e880100c21401c499000d40d0f80020241001c2c0596940380c59030840342d03640c80301c0c1c10003d10f243c00403c1149101480713607000c91f14050039189103000300343c13180c0c110380c00c85000d00c00180c1106c101aa00602c02d21160f03a5100219250705001070320442c041140e551158440e0082103042d64507180e90b00102002c2d0000c2402c103000303403d04810040741c4c81c541e5082c480d01c000c0e208000307a032a04081002c0741c07610702c2c2d420740d07110004e20000f0f818241003000803c01030103140d9220340e01c140c102e9401410710b01e4648403d9826410040310440400c030070050300f68084005106600040c0c014441d02803039041303e01058080000781e0b103c50041341c0c04207500b0484d001601000d41e00207003116844000040c2486c03c00e60000302421605403102d1680303e2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 505911645 1250 505910395 505910407
    0x905060a05130614090d02042304030206070e090103020910150306090e0331080102070b06120109080324030f07050901120c05040c1709030c07060c08181f0203 70
    0x2800d26804040c2102d410130700192180c03800039440c90b01c103244c0440c1c010039034000710204540b950381100071354286081402c9903044480c0f1b10615030560442d001d900510450021408007401078103841e0390000c015003c0000f40c0e0954090012900d0b001d091340428600b0108002a9000d036103118a020020555000c118680f0340700807d42500d625070046422500104003902c40150f21030a001c114441010480301c25070030120102d0003151540c3c5c0311030815400040c0810800040ca14030703d101c0c0c030080703982d41c0d6014100003006003210242072000b4550794003000440e80791034404200a42a044161000e03082060600210307060411038400120203600000040c0900d2600c414540e002d402c035010f12920160300340d21030b9107040805100d00760080350b6400750110154402e86520101143d1942098a14105507160a51381d81c40036080d020a0f0196250105040e4400c030045d41400303401c07007102420038200c0c40d080c0880741d0020035010340c810340c600701e0110384840d0990140d40caa51030b60040c50702e8207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 505912895 1250 505911645 505911667
    0x6030e03131523030a091b0303030c0909020304050606060f0c1e01050c0c070501050f040905040f11040c020a0605092103040b10051f0e12010e070504050903030a0c0905060a05 77
    0x2d10f89103406610240112040c1e26001689000c0d0303584a140960080f0f40c41e51141000750303010200361011240a26100c60104c00d04d80c00d60080018104103076a000c40c0c49656032056812404103035801022030700050041441442e00301b0181c14500c4403002c0c0d8920b0444400320b042e20f48804074042110a800c0010b411900702028441c0300c0e84281c80c3c02c8641d29280006014070303151401d40c02514180031012a01c490103030020000c0d078010b400000c0042085081a080038034a924001da030407a04050f08015140140c1030a006054001e519500248404042540d8080c00360034001d0039100c1d0761041c079101c0c800111485042100c80d040c0c4005460b80c070f00345403e12062510340100080d603082ca214071304201c19210340300b03100c4005290440342c1d451048414011241007689000060340301b04281d94a288a81d0194480e00302c02007024200d8440300d0b44d0700e060009542c0c088500d08034a410501c009040749207540c02030705410002d880c2c821621500c03034000484035004401004000707500850111081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 505914145 1250 505912895 505912907
    0x60903101b050c06011a0418020903010e01060b0d02250f150b0d03030e01110c161202060712020c0907050901230d0e031303030e010815030706030e031315 68
    0x5070380d03035250007880d040740301e01043d40d1820184296a10041c2040408500d00d004d0021b403000351120110326542c0c4d40382c00007040081c0d00a003840c1d5229520342480b180a2107414400d076011110012109420951000d6036400290810003d0100300550101c403500d01da840d00200c1e80c94548186006105031503a1300f130807219071a411080c0c8034400c0c548102800140d90340b00111801e02e0340351501241c0d0b00e031070041c114094403034040f0503a01c1c0407000c00c903004c03210804102d4041c080c0c0e14115082190740d80349400705818060031301c0a0340000c400c02203c40850a401c9100e0720b00d2031140101c03001105c119002c501c100b142121340030b00150002c6680310f010742c1d1200034405c1141040030351014030340904030942d41c10f20669040380300300380c0d0b030b90141c5485c03c2090040e140d141251a00003420282c0e82d0074060040b00c05288624005845100000d00078499000700c1443e249002d070050a4090a0003410f6000340001c5503e04124401070001061412003508410007500d1046003003d40e040180f1805446 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 505915395 1250 505914145 505914191
    0x70506070c150908070b070c1a07020d03060e01140a0f0b03100b0c060f070e090f01170a0c0902070809120d02010509011107120908060906060108150907030b06090310 73
    0xd00d4203003504440800d04e150281c6424030780114440080d6100d5250070b40350300b1561030000303188801984121080901821002c0e12540c056020f49003103d844000c2101122030a0241c8903051801c400144069441d940764203c9106000d014042441d8039554000171841c0181e00001c482c1350000304100d41844e024405d0401044079405050800507400301301d40c0c440300000c4c40c01c1c40e8820035400160002d0b100740769032181680040c1c000806410200000421007000340170f2a04004600885e1050a8100042c0982516006207020010a00f000741c02e201945c054201515041020f020034000307651800c40e4541c003900070400a00151281314000790946100031701c042e6050b4035180a08000e01c8109040340e8940e42d00900310620441c400f0800d5942e000343e6005000340d84141c8007048456100022032038000c400c241c072000030568810032400510741c640103405400400b4100411a6140a80c01011170b8800003400345080840d0640440c0c80c247c241110700d1005a243c180d41200581c103140c0c1034170 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 505916645 1250 505915395 505915433
    0xf0e0103020a060f0c03080604021c0902090105030606130c052715030121020d1a180a031713140109060f110f0c0a051608060a05010e011a070506070c 66
    0x20413038640040281c24541800c0340036080c080d10f1000920550745c1d59044800750b0011015801c86a0b2129100c08010715501d4030403800740d2286030000c200e80c03500103482e5114443c02003900d80820b11540c0c0c500003404545c1c14203400e124091001c034a0101d4100c400b52143c4c07104016032034460040e20b04200c465401c42da03400720006003c00043c813403c2501049489501c901c0702c04c03446500c10601c046000c04000001c0a81001e1880e0200030f00a02005034a81c062606101c00202500380114440e844032140c03240140403500040440e40c00e43d0b41c4400840e84100e41070f261100c0e6001988800504801402202030b084c0d5462500b0340410030b00b0710814010b514080c1c000c1200c04403501e6068801d00c603c00c50b62419100214072a604642c0c20031099030300c1c2e5886405c1d0391409811041c00c0f080211240901d03c4103009050028901d07a030740e03100701d6040755003a0b00e0054480e40392403580c00100b00c204040d08800c1808201c001701050341003080034000c8916a4600e0070307074030960a00c11104621a100c280c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 505917895 1250 505916645 505916657
    0x61a01120b0604060f0c06050c22050d060504260c0f030408030406080417040b04030b09190308090a0804031208011703070209061201150e090a020102120c070f0e0103020a06 76
    0x104003030b10341c0010340d810345034141000b80c2e03250100d51040d10701130070b581c40050000e400c0208002d260046800540900c4880c8a10000f400d0180c62005003460030074041e664110110072583c0001c80c5260b08066080350040003121840b0460f4075408480d071040341c1c02e962104800003030f114034145c4108945551070524001440c202070500384082e4403480b0750311910040001800101c1d003805102d000780e1214274103441c0459034075690740642c64171640240c441945e2f58074038000000d200c81c601082c1400c0e01303800c1e030784503a43d440c48940c0e080d20424405403016495100e0500c0b2030f80010101c000034400740d0301582282100b41e04c00e10b4002c0c00868144c2040c1c1d200c001030315942030440e81c00026101d0842c5c3c11200110181c1c0e403400481e0a20010180820340c41d07081c8a40115140e4044840700c007981c4907454100c1c400e81d202c081140d46d82844400090044c1c1c01f4107254500b50f001e0001902c03015021805031030b0741ca0341ea04070101081d00aa04040d00405c0040010411442c6c00202280106040e0800c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 505919145 1250 505917895 505917911
    0x90b090c10020709020a110307060e0106091e090c0506070b09060903041511280605070503090307080306060c06011512060315020d090204020c07090b0d0b06010c0609061a0112 77
    0x29200c0f001445409a142d40104490004c035000d03c810380e40d410310301000c481d125000d40c01c080340a00003003070401d07509500c1c0c020085610320303150181c44500e1030b10a180c80200e114041c0c04400400c1c088809450790f10a546008c14030360f03240390091005601400d103040300d03800c0c010801405e200000c1c0c1542d07503941c01080100304000042921002035580e90074035007030f45040c0c0008a03041c00301d01100300301c00701e0f81a4151040c0528100014803000d00a5204200304c0d622040e06a44034481616141c0d6a030b4014041c000000c0c6030040103590181014088034101400040d5087c80c010080c4c0084210303012250790b185049521800c034480805c03004100340411441d6031201c07042c2403009100b0084031500000c60307d59101c0d41360441d0000990190045548030340704280d00d80c0710708650144030700c1142482007101d480c6c54007050540500d5044100440c41d912203500540b9501447d80c0c04854603600e070583c00000ca01d81d0f2160b001d0040750b000861f041d4030107480004014900c4503004211041c41c001d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 505920395 1250 505919145 505919147
    0x90209010801020a2705061303030e0307080c04020a0201180803071403130201080c130807050f0a2115050a0b041b140d091b030c06110a24090b090c10 66
    0x100104007600119845c44072140102c0d0301144581e908941e0b0000000141ca6051220f882c9004044a001e659010440c1c03060100301602e9030300f01d2048030310b203a121075644507241c030301640108028070241c000051100c4a0070102c3c415240403020a441c01c00e0003100304814650000c00181d09614038001c4245145010045070300c0607104814082e04000441d40040c1800040000301c58803088645541d0102079626040540d5400c0075004150040740060b070401c5032401c00c4001002603881c00d04208403841d491182525608040304002ea0700a01600c2440400600b24460320340100a480e002082d041202024070058031240c01029060b0090701e1540c1100ba544088030461700000360020550f50f4401e074520350080c10340c0c601c0291074040d10b1340d03481d04041007480e0850110fa1082030307180c41c0103680c1c02050b03603142d88c1255040303002d07004640c5180005118100c540d488886040c10308030303078240000060048071035041088540420701e00601000140803c0205070500d400c84980301c032050381e490 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 505921645 1250 505920395 505920407
    0xa0206011d0a020d02040b03040c150e09010311010e06040f06090501050408060f15100c1101030504050613061b03020702180601020d05030a0615020d140a08010308180a0603090209010801020a 84
    0x25540b1940e6010400b41c181c012160100e030300401e007011000d5142d090074244407507401c24910521018a02d000071005a15001e1100600000341c0103010751101c0c0c0c81c0d911590410903410306924100101000240c5c1d2a60700d01c40079001405070800c080c030120742484e5002e041801d054001a060140500c02004800c200140031548103801c1500d031100c80e01c44000b41c00c507024040c182254454501c051160030254405016440703540500100700c61514964015030485400340c401a000d030308040d00081207030084a040088140c03013480700080740800c4091800e42c540d03600da54400001c2c1c000600c0c1083d0b02e0a681c500001a01c65004040607003054000070b941c940d40110610240000440050300c00342480d807214004000e8524412482500032000035200c5230041001008614000343c100710804c03038801070b648000b40d140c8070000b00f41d0039a261915540c0001e04411000030030440d83d01c116440740052900182000d84005c103010301148104404103034140c1221520b41e106200140b5650340c050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 505922895 1250 505921645 505921651
    0x2010c18090b031204090e0606040c0516080c010507050909071701150302091e0907020115050603040212120306040e0c0f0d080c1504021c030906110f0109080a0206011d 74
    0x2040080d010607640c2c003280c1001c1614407100d000d0b01001c903001501b802c4940002881983c400142c031200c0d80c501c1c080004541c011441d400028005100c1241c0d0098054103444000c0c0c01141202d043c40a001102030958a00322100c10015001048040040c00c280306801d8100005060880326009510084aa40b05051180000c03039004002c2d0486403a0080d8111a404080074040b82c1c0303000d0404030006003108510f07040b28010035100c070001d80f040348117200d1001c010781100c005118142c648003c000040c1c0014205030303481f2101e1180c006000c00101b150400300322007281c295440f0f00d00141040100c9503031009045803a040007088c841e0b681e40321480b01030119021100100c0160039410b00000c03900031700b00c80f201284940c2480451010000c41d402e40700c4c0c0c0c82200c2041088003100308002100c202cdc09401004180d26500a104441c00f82c040da00640800404480d40c1002c0210902d0a44034040c2c030540d4203141c0061004040780d070612905002d000300c1050b0900d01032a540c3c01082c0c0800013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 505924145 1250 505922895 505922909
    0x3060702210906041502060106110a030c110d03081006051c0c111f060902070b06090a23090d02030c07030825031e0806030c040504210f02010c18 64
    0x241c0e48041030907080d1000d840182c0005010306072140c0c0c4400724845540daa241c00340015114100001840074803c00c9140d40c1c05241001a14030b41c10141e90540b03220905110484048a0340158900c003074407180d00d881c1c91203000e0f98034600c0a080c06100340d0080f2945801110070004e0811010103141102107080d40c1d20000311000040c10032505030101c038203a84000001d074640c010350401e94059070607070045000950030035504100d0144c1c0d038900d01e800c9201e100030060034201008002100c40c94040c0002d80c0c414000c007004649132402c01044282c0301c250002d10600400ca550030f020140781d0404c450886035140340011843d20145046055492929100080c180c60000401e540082401c90004c00a90412842c00e001c09a40340380180c88010791090940d1500c41a0032000c03103291040740c02c0743c00f800e406001350002c43c140c08113000142c80c0051050702c00340f000d003118400e1600b446071816003c04841e0303141184100a41002825100340b0710540c801c020746d0404a040701c60300800441304480704 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 505925395 1250 505924145 505924183
    0x621060b0f0a1208090405070f030b0102030a0806090406090804120b0a051b0c010905070603020403030e0108060108130203031e120109050c0a1d030619151a130e130204050603060702 80
    0x89103004d074100c1c0303d200280c94011341410700740915290005810003640035280c605000020b003150049030340780502d07000c2200086005010940c40d0911281d20303038025004990202d83c0e074071161140c00f00e5a01ca50711001ca21000c56000400707005c0c10034507443c0c02105079a0244014100261900030f585040c012584200b83d00180c00c0d40c8000c0c0940c04001c13140c1d0701a098070940c96a07044050000d4002d48000c2c1c0200e07a2690422109602c00c1c0388040c801c1d601619050076a85600c1109142159840c0c4201c5c1c140c801040040c0700715084043c0401d102d0101355165070748a034044080d2a503650180e00203c52282090103012105050702c0942c2d0040301d8901d051a08650302c10540f110300c0c42140a0503030103005450070f100180700c0e0a084554030040381c007400d104040c1801c0c3d002c21400541e02c5440942c09900418004070300140e001000d0f8041040c5485a1550301c2e04105080d20000342e44030115038060141990450509016041c0e0040c000c03006800c2e1881c024002940b00d8107840c9601c804e0000b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 505926645 1250 505925395 505925429
    0x51b030312070801050a050303070b07030203060d060230010f03150621170913020c01091a090d080103080901121509090b0105030a0305070809040621060b0f0a 70
    0x10200140c5032607142034088030105080540d0050f2440c04280900c074002c008007100410281000411101e06680c000b52845403542c03228021002074201a001aa010510b0818034010525a0001d040c800030b104552020481f140200c40d085031503060194442600500e00400c8000341040300380c0c04982e0002c194222400104002d0340c001e1005070004d8503912503003a51203808001a4040c2c90020703108403000f2281e50456400c0d80c3c80d41c0250155aa0b04c80038800545a0a0156070040c224900e0400700120300302d00d040d60341d54881445190591002c5032000e0400210b00c2003040840c07480d00301402c2c07500c110350460b1950011031248c0500b041c1030201c6030020140c01d00195218850030562541084038250b141c20140010784040300741516032642c820700108461501040045140c0d5058840c0740c54074a1559541c0302c2a00000c0003a9031199407400c0024a4001d04c1c0342a1504000703071400308640071994034042040740c007080700c814050f60a0443e10680760b128940360360155141070302c2c808a212 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 505927895 1250 505926645 505926649
    0x618130602070c0e0601020c0303090a030f020d0501050c03071409010c030507021906020a050c10020c1003111306080a05040b0a09051014091c050a030c1e020d02010b0d051b 76
    0x31141c210001c101c103543d0301d80000c4910300c40c540140100c009a080e202407014036010182d03240618409558804103200e0304200060491072b040c02e0845c4040c0104002152a80310326085410881c0d0402224000204011040b5800403a0b80c2c1e80d0050b0180090400ca14000000e09003084810001c06118002500c04103643c2c0d00103018481002d20309000e02d14070f4035480001d4440c03c0056003154035104500150501d480c1942c4c42010100aa40c000c14000036190100f002101000e00441c007455520f410a40d042900e040040c1410791707003803500a5516180c044002c000903801001c3c41001d80c03a05043c030001542001c0d2840d0081c0c0e0141c004905180c581c1000c90070903131418040b00e05140b6050101d28500841d0101900c1404c48a0030396000d819240a48200466010209000503000b007182d90003a5000b9445501c01100c20714125000c62060b00e9046540e115081d200b4015070b10a5103008600f65090060f00700440302034580030a10542036031016540c01200849608079510010308140b03036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 505929145 1250 505927895 505927897
    0x4020a0e0a06030209010e0f100c080c241e04060e03040b03131208040308040206071110020f010e0c06250b040b150409050c040506060417010f050618130602 69
    0x61001844444500c2e6102c1e00a4003c3d801400c3c442c0c0420024a1562142e103083c0450070000c5902a0a241c0c00700c1118808030b030300c5004102c08032401d00301480b44841202041003003021042d4003e03080d0340ea40c62a02158440600002c0070240302820810601344040814100680c2143e4040740104940070801340e078500b18090b94100c00074000020041103108642c60720b20b082050300a8083c0c1615072141d42080301d803140c040300c02070081880000420010300385070000348203482c0217062820f900c107181360008805071104200900180d11507146040044000c0c0b140881140c1102d0003040840314400100da054005c80614400d48200150024a4007400b142242c004603800218070b0514075043c40d140f110004141c0e50203103089a22a00340400d410207124151005400030000e2982682d010100000b03407100070074007500050184400941c0c00c0308409102e00301c110307610011454101109908003120390040c81148110b440083c020800c0040340da0180d000380980b0411110000302d0705210300070f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 505930395 1250 505929145 505929167
    0x2d0601050d0e030d0f0203010620010b0a09020a0206060102010c02071e080604120f03140402091810141303080403054e010807051e04020703021f0504050c04020a 71
    0x3001d810000b8440880e500031000b40840440420104030480d40307a0138140072400240a0309001c140d03000100013003010800c0382a240c03001c140001280400c40c160128200c00c08a50150800603004034407680540e8062240d01d078005c9083c8001c0019001c1c07039034000d40c2c401e414842c000a10303d0380140388948421b0800950b0103024240d040702c40506107842d080e5040ca01059002c40061100884103031842d105c2d025040c40c071160000d040005488a400300181054040c007040c00460440001b070340000c809010a001d103203044100000d40201c0080380e80000342c4001d2032000d00c1e8509003102000281c000b1070090b00190546001615a910000c070100c2c1201036440341c207082e1113642840d142c4815045000f808414000c00040d80d24410380d070005080701070a008002c3c0c81e400561040c08a428001c202540800b0994500030001c40c112011504036130040030150016080640f01980c52002c40000d0300181407680750801071032505407519a1180748482c05188200d1700022090003a034800c1c20a03c50f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 505931645 1250 505930395 505930417
    0x4032609010327081c110315060c161701090510021b16060f0309052a15040501020d05030f040b040f0516050405060f0d02210307050d082d060105 64
    0x502400a41013001d46500b0600501d0070540490401c040703903c485001e035168200c907407800b25003152a801107511086842c0d98032540c100344240300581141d1420490b442d65440a01c60034040fa6040034048600500300a12030038260b81800c15050000340c0004415540e003458050041c0c444500c50b00d0040f0400454894802a00c110b20094480b8001442000c040303c035591541c2003400300e88841941a0303064004054034941180d103002c07c0d4112040c8040c1c00f142c0864492611400520740060440d2644103446018001c0101d014070655030100844005001d45041140c1189400c3c0c568800000000304018240780d048800f150401445410205417180e101d000d964664810143d203200c0080340c0c4c0b04081c4640d041c500400d14a043ca512100901c0703e0143c40700069111380c0e000d2180305130081c001c40c0307401420700010444694040c8064880b451180380607106002d032542c00200481806402030b5542d800d0240d8100e1007a268031160401c0d01054510240c10750f584c507005a07018000d84044603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 505932895 1250 505931645 505931711
    0x20c0319020d1722050904060c0318050102180a26280b0c0a02101d0703051014010b0301030f030201090501020d20030702030405090a0f020a05040326090103 69
    0x1501003100c4034040c2983d5107400110300c14400884d4040c02050000d07109071074010410300086408100d403030700501543d00d100d00f8007046e01c8580e202c075440b0311070014400b61850396010a00c0d42088128208004156001321100c3c0000303800c3c00c400b200d040c0b40501020802691850850502c814140101f000152014003075080204a40d846080c07114100403040305c3c94a017440014002c2e4ad040d0055882c0303007070903034000d190350318010030620010140155181c5690319012076484298074104450806984030b00060f01501030b2004649040c1e4003032400c50340c101c010481c014406400b00009490450f6002006d0a29158079030070144c1c010319103c04041d1841d400001c040341d080282c1d42080380d0301c1c0030075905100c00c200e000040080c3c1e0b000a6502d1030040c1c008000810140c58010240341e00b10081e9040002d01242a40030842207a001250500118102050070011700103440045142a03043c81f160019040150401c22034511400d810309040c1a075070420030001c0480700c143c0314072240d142d48542d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 505934145 1250 505932895 505932923
    0x1360603060f051b0f0a02160b190c02182706060f03010b030a030806150301090606080702190b0c0904021c240302010f0c0503030f06040c020c0319020d 67
    0xc1001e40800b907220445503003480041030080022241660b61110100102030506210f9209041640e0114881c0d8045204000441e07410042c1e002200c0024030040390f4a51382c0700021060040c915144c0403003401402a058095000350b22008242d901c004d1100300308032000c0e50b48400f180c84038007814444d21055909401200007900d0009001c50041000311079100050040c84201400e8600c15a06281c15421030700303010002900032120b42e60010b80003030900901d800000807941d2560401d030b0200c0c151310340754001000f00c95000031016800c14014030140c2882c1001d00a0040420780118004150550800028030320340031000645070011001001596204003122003081e088a000b105500c1052812441d18040200255540d440c540c410144960207803540e0019915a0380400000c2d051100403001500001c45c181300943c843ca03180103400300581440c90074401182c228224807420f55202400c12411950b001034101c0c00070482166040e03004845101040080b110100b0007400c003000301e031359 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 505935251 1106 505934145 505934153
    0x10216080711030327062110050a03060b040609020705070e06180a05040b10060504260604080d0e0604020a140f150403061401360603 59
    0x41c100540106010130b04591107108803000a41e07174440c164281380d9807216588254203007a28220304041c8034030520511307400000400b80c810100c110004546150120708600903200c083c0c403140d040c9649140100c00303444803100442c400d504100d0003291600c003500c00d454500350000020b09006240c0865411032020241080f40c01c100100440b0005004200ea140d00030b0080321000039840c501818032042c1c0b1003001c1c15542c43d4048000742000f081d9800000d0300c050750f40e000ca40244003100d02e038020f000c00d991076425041900a01040000340300003a07000d4411064045001e101c40d980300b448160701d0726422200250300088a0340c05210800c040091680009809055455201445030009190042100300205070800001e02401040f6990103144d2030740103001c600000b0765041c20580700105000000d1007540a41c09043e00c074621001c52202c2d064002007080400c032007078603814 = true := by decide +kernel

theorem cover : BRFrame.Cov 505755395 505935251 := by
  have h0 := BRFrame.cov_init 505755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 505755395 ≤ n) (h2 : n < 505935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
