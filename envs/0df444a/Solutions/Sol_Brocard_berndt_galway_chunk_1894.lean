-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1894
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:03:54.334328+00:00
-- url     : https://prove2.me/submissions/62b72264-b3eb-428b-a634-a6eba923c86f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 340467625 ≤ n < 340647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 340468875 1250 340467625 340467683
    0x201080a1803230409020702090a1e0e0c130e0712020a03080702040207200310020f090409020a03140d12140708061c05010515030a0c0302091b0c0a140304050904 71
    0x1100d4013140004100f081500070b0101c451007110702c521140d40c0c0c04680412106501c40d0400203c40e0a501002185c10340d40c071408003c02c3e05000c2c0d40014030043c000c10011210112904070703030b558032864044101c2d070500002e0050aa08100401c6c6c0c20110f4000880c2042c0da400040d04155001844c0340841d601c56046607455a030002c50122150b0340d0180304002916104200c5003e1300a56040703440c1c00a26100b15040c40c8038144100381842241c0050200401d50190103d130042c03c800401300200754142080185200d03400014554042503100080c00e0f5039000600c40406410801d041c1c2c003007007030101c40903444102490000f01036500c03480010741031054181200040b00c248079150041c0041908134501c15001d02c40e40c0d04000d041d001c28160f80d8209048040c10b200d41002e070600042c41c26803030594000742c011036040d044030708003c42810503911140301c0a80941c0f240b600300c0704018140d00220784d010340c040091410540740c5000300340c541900900c01800600110300d10101202c0c14648006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 340470125 1250 340468875 340468937
    0x1815050f1b0a120c0213050402040e100501090605011b030e0f1504030506010608040503030403031e0507020f06010b03090c0f120703030216050f100e04060519030201080a1803 77
    0x44801c80105006031152444070058501c1c2d010b062484440d0790040b405200040d5001e0b10109403c02c110115600504020b03004a90250f200d1046241c0c1140422005000010032840003442d94940786620342100c486501450502c444600d1110078011400d00c0020f0941c1c060a04002014030040041c0c1c4446092205a034040d0090205082c202040806001502d200d0000c0300e0341030362607120a490b00c801c102c9008003994400c000050000b480303500070201c10103800e030241d405481c8c90b0b519602070b00c100f21104001a0301c91846c00903882401c01002e4014044107026170301d50304141c543c051300c07200410b40a0b40917400700c260824051303c0c2d00440e642d1117a148000c2e2003d191f2285002512604543d08131403001507036400110b1140307400c15031506d400c5c400410358541005c1c10300c4152064115603680c0e0b0b621070765410000038a5140c08807990804041110342040d050701710720000d000024003402050100d450702405000b081e1900d082d94079400e80504115124104510b01c2c010850303240100d800f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 340471375 1250 340470125 340470157
    0x20a0506030a060e06040905030403031112040e16031b030b1207080c130204080601060f1b051c050304020a0b0927060114031302090a200a1815050f 65
    0x100d201d02c019440304041c0c1e01034162078038058507090104015199264030181580e0420401040068000c404180340d02240000756888a03000303800340945508941e0290400340036003003c2108800385030502c401000b04904080244e07080200069003c45142c0d02c1f00810b05070340c0c11303074010f01d640c4c0c0080440074103844000701c442c016101c4d4002912001300040c20340c00b0304030031480c428042c4054000d40f4203030340410009010b182e190144c203e0741280b901284034144a54100c520a00041292828010078022002002d030002d980c1440124103075406a11410040140140710040c1e0b40d0001c040122514150481d031189100700024620404060305150074032022591083da007500902d21902c600001d80f1025034090300d81a49101d54481101c1d58042071190310050801464024841601f10400080000f81120004100f0b4031300300e010082d0341c64602c40413445000d07160784030401000c1300b00c041441c1c10f02c00d0b01d00400a070700180c0c85001c00007444408244040801c181c2001e0f07480702411700d2095 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 340472625 1250 340471375 340471381
    0x212040501090c06020a08030408030a02190c02010f0302070c12081c0605010f0504060f1d0303040b030f160f03020f090d030509011107080a06021803010528051909020a050603 77
    0x150080800700c004031036583c0c4000000503414004207000070700c141c02510b8589103130f681c1e55070f1119650000700600f01c10350b801d20240d80400d00c020a091035800c2d036611f45111041040c000946100111704a0604240c0100841800200000c2c8a00704032210000915210718003841c2c070022500612090080e50400315680a407085881e400038421100700f078842034850841d4403000c58181c8114084d01020841d9150301c20341c031305c3c403480d203003503c110300f464144601020010010b41194030543c010b50b0500e41c00700500520040f65128280c10480740d43c01001036001454025158143d00d00181c0c0515501041c2072094800000407919002001400c0300b80064051402501d20340042560900140b621a12985d4040c070010303060041c3c924410040000e0000c96031014081d510484912220ba003217580f500f03070b8944003401054065041184100741c0e51060302c40c60401d210049001040f00307400c00c000c0c8048549203100300f00150a115130301185002d280d0000c1009500c4603400305070099800410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 340473875 1250 340472625 340472633
    0x3040315021b1f09030905010f0e0915040f0c0206040b0c040308040b04061e1409011106070c120f21090f0302010b01021b0306010506031905040503090907031e02030a021204 76
    0x108080f4508250312180340d804818281c002110303000c050050214040d10703002e00140d80501d2500440760761038031700080c09060b0f8001064442c1400d44400b03c030f800400405201c0c0d4a4a402694503040740c1080c208070401c807a80c0020355070070300900050020700d54500420809103020341103402640d00321102a40e9180c1c0d03604400c507554003500c10340700000da490701004641070005c9460001c420382039845da00f414003050f00030a43ca50001981c1414003515420b05050414141300c01407044100d91a030312000d02d018105207040e031366001400c00401c4a95174a0051481c0c10800c0d602c0d6452002201840d054040c09410004020291014000640002001041640c1500208010301e000e81c03d076071040b4104414000454950403185525811a5005000e917040110103541c0c4800c400f60310100325801540340c032048620a94041d00d403900f002407000c141d4101000e40c0c9402c196585420800003058a880752204101c41c11407100664001000c9a030700c074000c5e010345904106240d101121401d0502e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 340475125 1250 340473875 340473883
    0x190b0301180b030d080a0f0626031c0c090b1201062a02040506061207020f070e0f06120c10170f01050d0807021c080d061703040315021b 60
    0x1203090001c124501260240c06220301440510040140080404100c0c00c1016a080c400c02403080035a43d5407401001e0041c8114060b5000070201d11854404c0400d0480340782d8186650351094251545c010070040e0039080c80113101058840c0600300000f03800c03484030011210700e03240d83c3c00401c4204000c910880d0b011060000541245c241c2d80302d0784802840c2c01845141c0400e944012442c940c690401203001d400c042d04141e601480c018031040c0b40c5040340c0c1c40c1810840d401e50328a07006a1084861000d0304204014a002806102d101e410162030841071032041e925005042900a51006031040c60380d100410400324000d0000b0034044000d003c0101c000c094014889504c000d81c851500401d070140000d40c10709060311800340900e180072205443e0400a90f110007000c903003011001020500702d12903070b042402c4241c480c1001d242c0d100b0030f0a681c40e05856454205481c01c0d0241300c0c50982e8084004100c404596001d04c0d80f90100303410b0541c0303000034040d401d0030403110700788070180040347e540c085 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 340476375 1250 340475125 340475129
    0x905010602031305030f070e1003080712111504030e01030f18110a06091a120103060902041d06130302010e1617010b011407080715020d180b0411190b0301 68
    0x2003080f03806140c3d42e60801d1751340c008109100c049500101802c2c0590320b00c102e00154414060b219081b11290340750341e1006540c1c0f1824040c0d400300e050250030311030743e07502030801c08812810308000c0c82001144c0024440d002c5002c2c0005040c003211120303620940c0d0017900b001d141d000d040711080001107000f1420116061038200205c44e0001401480400d07032811030030317200a807680c44d07840310038460a00d0080103c4690f04415003003084028032a221005507507440c0b0740c0c06580309941c04640c0410520500c000c0d03440f80d240c03002e500a8031940314078544c200001c215900600780e1009a5241c0200e04050303005206011803400c03580158080004981c05e0100c136030045a0305140ca0718002201d07a23800501302c1d14070b000c078140001c8110410160760b42034003000d00714080c00385c1034181c81e001c4540e90b0f1700310b1300041d5081031000d50303004515500c003001548035000c44050b0400400f100342d480ba503100b600d00e02c002070000b801034425000045043e00c3c0c840d120700b00d500a4500541c1d182da220489007c40350024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 340477625 1250 340476375 340476397
    0x91101020c04050f1f030f23030702090c0d060503150103050d051905091210090c140f04090f0c09020301140a051c06020d11090406060c08120c04090501060203 70
    0x8001c08003605003442102e2044103240fa40308030913250414808480c840c81d003034119518411040110100c0e00030440c1d540c0b444c0c424000005803041c03181d6007100b002d01892019440d07405c1400f145c2c015840b410080daa0246491291079521624441c0c0000101950380001d40c061141c81c1c40f4200c840c034070b56030043c1a030303015000711940314040d044110396a00c50f119100000380c88040d10607401e1030007a000740c14a0f0000805d004482803118001d02d00e040c043c00c0048503041d4407100648140907812040b040600300f02c1b4543c503100109400420141d43c014490369000d16595440102400101c140303c0c030203194011120708040350354104150203500f0a01900450360081c000c100f03901e181118a480403280c000c1e040300c0041a02540503200310165510903210941c0800160f041200c41340720301c07221122030401c010344601c3c03100b080c4002c0703c029030814402d021030034800030041107514003030351412151503910500f0f030758485900305058080c079404200c0460410b0300116102da00800509003010718 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 340478875 1250 340477625 340477633
    0x2f040b0a02070311122e110d1401050307030f020409020d23160b03090f120a021005012d030b0c044104110406111b1c050f0109110102 59
    0x25182c2041076174821580f1401455000b950600441d014981031500004012006041d020801c020700301d0680d101c8001500c1c160b07030002900c0d038004080c1d01c201c450110181012035002d43c1441c0200307a4401c924003028000090100c860021542e0700e802041d8503603030242a804a083c0180b8100380b2566041d404501d00c0d20361041c031001403d8000455a120b80900c403c41c195661030400580072540c0058818001070095450340b4458003400c01c6452a00414201c15595840303460784000d0818007a05840b91031f0500384030040148004111180308889003510362108034403081e04100d50340c51460790004011946101c09c00801180c1c2c00043d000304c0e4107214204a540401100c01440c0c001c50b0400d601050a818070140001e0001500c01e402c0000701030400159030250b040c1f9180550016071101c0005801001403031460401808400720380407810103650301202500c800039030b0900705a40462941501c88120006200d02000b401c221105104000c011440550400d4080b00d00360241090140c42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 340480125 1250 340478875 340478903
    0x603020108090105090a0b04050a1b0603060b090a1a070f1a0a0902030a120c021c060b010f0f0c0c1d04021005180f060f0c0c0901092f040b0a020703 65
    0x2c418040c040c41340c01064090f0220503981d64482000200250054456100d41d1035100006804181030103200240c0b040014501c07803a2201c0142981d1083d00101e01500043c450840140ca603125074600f40d9044040c0d411401c0290f40c0f03400b65a004035003000d001d1130301c0d030908903092000704000e1400900c14517101004039694412a1025201c42e4030000f50103078807101c184408540c8501500e64049250f1174141400456030b0000b480d210311b9000c0c4595280d081101010800504d8071a2101a48080c201260242d1100201400002c41a401401480600c913003c90030001c5201c1d66001402540e10f01c1d058000c1c2e41c40054a000348220b908078003c1c00c2c41c0464598a0f0f0144081e00e550035085003070312184d41c468409214400003409000c54105a00b0320142410a40e03070300142010314022002070807268180820041d86030b0044e403003280128601110078948076100362505807010b00c0301c8101c102c0f600602100054a1095031701000031442c001c2240300401768007090050031640034103a4a44112 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 340481375 1250 340480125 340480141
    0x1060b030105010804030c06061703030610080c07060f0f02030106032913090804032f2d0a08100917030621010e0102030a0509160b04051509060d0603020108 69
    0x40320a000345408520351100007800244908070b100b440b03034420540070403099942c44000d00c484240740540001c03501302000f00310460401d03404905d05103640c4e19100c0040d040c02c02c21a1282d01c205100540525241c0001102c14505034015020300f0f80c0d8000115903a40c1e40b41c1006005215580042400071205545191007008180c50b180152600070841d0040310003019003240100400b8a0883e0352440c01d00000010407151001180d03010310014200d51000302841900d1611000c841519100c3d5800703000c200f02c0c1d01d150602c0900040710001c08601d02270ba0140000700c1d0304106a003d407105100d040700708003144c1c078190022110309106c0c042e075121a44986c0c150250034001166001d8001520303030906c0c0c118035501c84580302c500740d98800000c0c800b162410800d080ea802102c0210826844000780042c0c02800c2041042400c02c146294034490308040c2002c00c50f01c00e0744201c074840c100d11480000c42e943c00200f2500d01c4030b0010308084d56030ad59a1700307600140030240b00a03404285e40d503001480310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 340482625 1250 340481375 340481377
    0x9060114120307020312121005060301090207060b101e03020f0306010302070201020a050d050a2003071e0b1e1608150102121803060907060905010c14100902030c04092d08030a0e01060b 81
    0x1442004150502f10f07800c00907da002500314003000d03508140c50309600100b580702e0004000e0b94400c01e80d80d00500b80300402c00e05c400701300102030300c0d41058810444d84d4010180002902c0d048a0700b440c01594501036400100d01e000c0d1980e02c0603015000d804c0d43c22201c0c5400800400341d60032245c860b070340700c9107590340c100707404151102c0500c4040e04200116800a0049075030780c0b071681445981e200c50b0301000d80b10002e0b0307210b088071440d8584d40003500c1da0300d14003031618a0f260700030340c1d0858415621a030510010f11140014006214000159181000c1680240b104100c000700001c202e03500d4030880d9402685160104491a00030701440003c9821900c0100c1d0141c265083c0ba292001140e01d02401141e1410070800300b52190541003a912600c580103021004455131710314004030390140280100b5040805486526205500e46201c10000881440030984074280703814229003036001c94452a071000c0c104000c0100400000400c00105002c00ea000d40d8282003c58001c01c4501d403544509155 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 340483875 1250 340482625 340482629
    0x10519060f060818010e03070809030606092202030c060a050d060537030c0602060703050c190503040f05240a02030106050d2309010c08090601141203070203121210 72
    0x11007010008210014144c0d50300441c05900c0c0000801c920819006800c5030404402100d00c0c078000139401c0300700d1074208801a08003800710385014481c148880103601a81304052881d0b8643d02c0803010358295a001d22145100c0b44000d03201c540e0321100030320000e08961003541d0440c076540c6403480c0807401d81400e0900c1b130490300710441c0070144182e20311030390560504074030364810402d4401f40b00030001901e0b907000a401410140c0090296041490014090b1003004012401c419170900c2034120107400102d00300e00000082c10459034913241d0741005100340c031081601030002e100d900e8240120201d11205904c0005203074185103032a4030761020801c140d1100780300f500b00040d401c1c40454050340d00e641c0440e44d2451507180401d1642601c016040c80c00300101c0f11460243d40d102454600550031003500d5a1060784440074011542c100f910305440c0c011000103180c06911190710307000703040c44100121799004e5001012100d90682c20603e050250348101c40c2850881d4280002c42c076545142d440c1601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 340485125 1250 340483875 340483877
    0x1e0303090d060b03030a030507020d110705060c0c120a0c09090c210b04030e010e01020a0b010614040801060f180c0f1404090614100c111e03010519060f06 68
    0x46401126030401404503800442038a005980700e00c000c3d25580c040005211780560360700d012946141215019041035200c40c4c1d0301e01802001003a00c41c00c0c40d004203084d800e561080350102d444d03010080940b86407034118080c040c0c010191980d41c0041c150000f4403003618503c03c501c002034054548602b81d05852100700d00a1044d410018184007a10081c85d4005815454075501e542c01102a1284039440205880030380103d03418a0720f80c045968015a8021403040c05e0005103103148581ea25101c42d0030301481501c0470401000700b40405440c4002c100c900502c1810024425140c07514009401c1082c184580403029901361040e101c0402030380620342861406441e03112a041a820050360503600a440400e5907202c10400070445030031500c214000381030000c0c0103148440d105002c0c440241409540581841004084480054600b4141d0920300100b566034400d83d001407081240c6900c941c041d690b505500f0603041101400c0900a12500c0320700326841031154940c0c80321a100b10034401c4c09094 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 340486375 1250 340485125 340485127
    0xc19060c02060307121406040605060f030c030c0c030a1701061704020906030c0301061413090b1b0f0414091501020a0803130b0c030106020609161401030f060f03021e0303 75
    0x14001d8a841400346a10440300e0506001c554949002e0004590781d80c102424440b800070f0921017242002c1c0719a1004d000306850540c039086516543d282c01d030100030209044d4400000000d25003029220a03140529401c400b125256240c0d510040c00030406805075405007400c18000160726403140901c10030300d403c8040000d072982c48503000d000e10b104004100341d81502c2042c0040d062520244030352801402e0800f071268455540c1c800300030310a0f110004400072181091640004204514216070f042240c000c052600c800c00142c0e20725030750103000d00f9032201c00d00200b00020412034402100316400c0084400c000540c2e280811a0200c0450041181c01a40081d034a00006082c1d28011a00056910001107132038910742d441c03e180020440780190345c20000b0004009441c0c04000154000c0703803a0000d8120408401d0000d6245000c61182c0094840d824021041c00c1e40281e01100d84901441d0062000300c2d113498003003500c4591840200c1c014084031101f011859000c8251490346180140a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 340487625 1250 340486375 340486397
    0x302090a03060f2004030b06030f0d0815091008060603071a16020411071a090a291513090503030103080f040b07150c020616080a110c0c1906 62
    0x200c0020a80402d9a580302c96498014074413040303050014841c1500440342540d40c803800c42c6004100c148010b01303c0d0307010364407298400c03003840746c04161b0441c0c001e2185014555583e8103443c00303032090302880f1503a42107000c440c144209000d5108078403041c1c0300d00700c048070301540380c01041c19030765401841180c5110364441c02c01601c200104004002d004401c841039007060245030001011a903840c0081903a1080025800c800c00c180744000c4128651103100d818160329060501d5600c0d251740400040045c402844170143d2900d04205040c03122200348a100d180e0b14008402d00500c10180703407594031410a00e2522044044103005444517550311401450450340385030b84048060b0003080c1d615203c13210500c4080b0b882000340018144183c01a5868110001d020460340100c0750000501e00071500940c0c1040b01400c07064101c42c0080e0b00310b140c0b252450b0b0318070040c00000d21802c0e0042e0011400000c0d40414820001030b403980005d4100e54090b03860b0403000c52090081c243e1312030b10b0003140b00e4000c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 340488875 1250 340487625 340487633
    0x16080604030801150509150702092406030601051216120903051909030f08130905040f1b09061806060207050102100e0109020603280e030904021812060103060b010302090a03 76
    0x134890b10480c1030550415482c0b600290412100e034801c0750541001280380030640c68000c66007a0080414117031a1451a079050040050001c500d1a01d4050300c40040414000d900c150221800c115a4094040c031030708003118200c00248a5615610002d0220f500d044d072101c0007172090f0104264140c49482c50583d10309098000321070030300c41d944c0521101c000000041075079110403400c803501c83c108903030b91883d82d44803821a590064000d0000c01c0d150908000c00190b510440c09003d5410402c080700c50305001c0326002d00c04520360400002a0b08000000858a4002c0048600c601c9080d0082c01840e8541600300c2c3c3da8925031080314010307400803c0ca108402846c5c0d1200804042d00b40021405581917004601181d100343c070290030322100c05162074001c81003d0710aa19002035990b0500c404650040910340c1c07401040d2100703225680c0000c1075440e143c0d080c1000d000e1088007810880c080305188040545a1f0340034401035a400381440100c00c1c00f50b00c24401c540c08000002c0c060b110060441d22 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 340490125 1250 340488875 340488899
    0x30907050f03030c060103050d020d0e130f1506050901031b081605071e11040c05250f03030509061003120c06020d0f0b01020f2406012016080604030801 67
    0x40c0c401e03050b00080004c06864101032140e14080c500440c003c2143c0c030a20100240303091a480080000c01c41c091030901c4196448000d502a040c401c0d00022a240011a6107003000381200f11111241d10101400003820903005405810814026202040310790000d403a50740b03c6a100c5102c842c0000c2c045400213420b050b40015000c096041d61510b5400c110450703580d0340040c0e045400800325001050703d03070000c20100d11105061404159411300080310307507a001030090301400340c00c070101c0e18001c3c041c10f03c03803482e803501007641d9600070340b0070f00e0076613154200a40181800e071103088041c012a40001e100c6015540200c1c120307a440000415800101c58003110b1900710b0080032900d040d000c01800102d001180919140030720300a1000a24907804400645044484080c0c9690754012342c40c2d281100003640160380ca031000d03250481e000c2d5550300700102c031700031036034002480303a52400d8840c43c60703155000071120a0b0001586004402c6510360250395510b8400b200c00034005003240b0014081c03e50310300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 340491375 1250 340490125 340490149
    0x402060307171e0109021218150c030f100303050a080a06120b01091d0a020f03010902060d020414090c270d05100c030506011e0e060d0e0d0503090705 66
    0x11a126481070030694050024050940701840c902403180102c3c41003030b200805107401445806801c62030305080300214503030000c0051172660801c03658603c95400c54800c0c000610400400140c4151610b0a04410303801c5410544644052184400000d00e02c4000391810320282ca0b05503c1c1e0301c1c00c0c6015480101c60013000203000704a159220b0000098203a291440c002d031081c0304481e036100d15030421502404441d012495404030000d480d5240000d08408a50300d40d51720340580307400700c0c90300c4150701103800b43c483e0b0f000c000e40106001448a0800d000d50707001c1e00542e813036209100c0d1030540704020800140e40c241c40b41c01c4043e01c20081140031025207094204100b045849800c2c91002c0500056001c4088800660b0305070441e00307600c3e844081d1841100180140350804001d1800d00d030300024280e0609640500c908140e03041d204504900400425403000e00050505548404000d41d00028100c43e0000c952248503442d004031006014405691203414004c0c014091240f0b88010083d03402124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 340492625 1250 340491375 340491377
    0x21c0f09020102060c09190305011406010806100c060204032f010c0b0705031806091014090601050904151b08070e011215120606060f05070c060302180307060906090501090503060402060307 83
    0x202042107e207036010048400440c004d44c00081c54011410041e0b40004004142c281000062820081c00380c3d104d1468401c2c50515240c100140c8003580b500000a10584c1c001418000342c003141c1c80c0d1a542e002c40c021035030104011507229400c1100006482c44003048100a15081005001698451240700a941d0200079000102d800020001c40e03107003010401d0701e0a805d1904900c0c44025001c00a004c0e00c202240d11350141c4009140280c5050748400c0d0601a0710300c1a60760314080780034000400030b0302c04e5a801d01041000403a001104a11000ca9004800000300740300000103041c880c06103082c0f018029041e1103140404140009074001480e642d218113501c11020003011942c00007645407103125510517000015000c0c2403507006040082c005240808110080118100250241c905e03c01200e40900f805a280c1d41e03500403c510703091080051580521810800040d00b41d4000400c000711040750f00d4100e00162203600445d8000700b00d0003150b4042c1d01c150081ba0040c10b0240c001e591040035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 340493875 1250 340492625 340492639
    0xc0e220317061f030b0a1403070506091206160306060503060d1e17030f160507020402280315080a05030f1809042405150d15021c0f09020102060c09 65
    0x80101d4220444444414043c0044d54414945140f41041c030480e00203848910340d01340003460746000190341c44a07030b030046600400307011030b40350801d440d13402a810400003908262200c07440c0c512243c03041c0c2c9011004142c00203081ca1000a003442c081d40840e409860b0183c000c2c80391114030f4a484605e40f94441e03036580c038082803a40c00000302d0b04244140441038955009203540341490017a42c2c440d00c5001e842c40c840c00000d5040d9101c0f603a0004100d4503160b60644015898049420604c10002d002508808010302d021008212aa03415480250701c420040210b582c20341d101c141c00c940c0da0355840b0000300540c2c4100103034160135007420090080c41c04040080e071281d46609001c1440c00c031041c0c0e4121034600f406514105070000341c00c1d05c01110032200908000d286170500110050442005a26000705d5140384c6400521001f001e00d424a080903220035592821001484132021018456998019103410b400e07002002160040c03c600540590007040f0a44905c505850070b5440f41013031305e501c045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 340495125 1250 340493875 340493899
    0x15090702031911070e0105210a06050a0c030c02060105060a030e0304090204060504080d0e011d0f1e03010b060333150a0f081b09030a0c0e22031706 65
    0x3002844850b00d010a982d5503899400300100d02468450180c005c08103510404006100c19294180c4100b031800c01c908840407005010300000d41882c1400c117025001d18146010004600d907250411042c103956507034100304805109108036113906d000e000301039026004012000000d0f10035000016000c54000949280ca50380d98a040102c0e80239520540c04100007050800c80c4220a00558804070401d0501d0008070400100007401020f440308841e507160480c1000c40c50588038a030318607210445c068400f0002d4110810800149040b80c10320500c65804e0603038a113818180502500d0003440c3c40e89220f10b020480115101e400022440c00e00e80c0c42d0384451003841240e44101d1806400030346d1814050b66105480c0c0300a00c041c51203040071041c06072070b005200c500c414180e42c8001c00302070110401e80310002000041c1c20300c9001c85014001841e00c40c004210014016440c5e405518031851078545420b6145000b0560500001c0240c0410100c261043c0c82c5d0707160f99211031b40035400401c0302030a04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 340496375 1250 340495125 340495147
    0x9010504030f0c050c0415180b090103150920030709060e070804030215070503010914040c030201110c0a03121b050604030825110606030705060711010302070b010b1c051509070203 79
    0x2481941c2c40152500c07e090013007140c9400940c4c1724514941c241e4090000003400c1d030109052a0042c40010044582d0007800d01e982c2c1102c4c0d118514442e441401c0844a400c8641c20565514010340e00b14800d005602001505620920849c0200c0b80c1899003600d0a5440720070a85840300c0080c000e03000c2d405442a018215101000000d128406a46815480c0c0d4180b00180d070072290070082c4640341940b64024000402d562242c143c0450f039091034a050040071004d0064240100da20307505400409811002c4204101c200d00000030f10091b5032005a41c920b080e4a07600030aa01c0e030800740454003d01c010501280c03040c0c215030f520514480419100110000c000f50041a0b40b603220000280003141c400c0b014141803142541104045008010740340c10301002a505104085004000d801c5800b4070000c0e80e4000e806580925030002040c0d01590381d22080128150b000303480e003071b00441103c690f03c2e114210900c01c4500a80900c100c6403c4110440f0900440070801781001d0254070060205035401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 340497625 1250 340496375 340496381
    0x2100911101713020105030f101203030f0e0706051803030405061605010e03090a090216050f100510180c03110c010b120f2805060703090b09010504030f0c050c04 71
    0x642203503035034004003811114440000b640041e05801070000810011409030781d03c282603940001001802d4a43c5880e801215984a541c0d175019000c016690b080c407006060301344c0d000349450440c5040502807042014102c54403180b40b030113840080344050004c0340e45012040b0b070382c0e180d08501504980c90580c903400012003a400c075000c0074404a814842501c200202800381c800382c02810f40041d0b08103250b00f40081c08216503409240320300765002c1590a04181c0c1160b04200c1e640d000300640f080c103190540080c2d101d0030900c502c0f105031401c0901251030689401c01003400c0f100011107040c030f40790400c03002c0805031044107441d40406448004500311044880010071000d1880400040c113428013100f40400240840d090102603048042035030051b103070200382c24949100c12a6585099200d20004214031442810702400da4030030345040000040e010341c131a0b00301501400522046039220f10402e42030380d8045600500081c40410341c01e44541c0a05484040d81e4450b0b029104a540c00f44041003c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 340498875 1250 340497625 340497649
    0x13f02030a0c05030d02060103020303031819031e08060f010e012c130b06070201030c120e060a060909020d1e0f12030507020f06040b0601050403080c0f0d02010204050102100911 78
    0x42d00da000400c001e00d42000340c0c92800d449400079000561441d00043d80340c0c04001d000c40502c4c400a0800100348009100c0a114088505107440c0304034114100100248138550311440c000030b521071221030607405141c0c0144100e8000b0010040a0041d078011650b03009010003032410b011035403941002c600c4080040e008801c501801c2480ca030601c9204010f03820352008490440c1525080d003029482e00c40c501241e101c1d54081c2404120442c03a11400c035003e10340102c804140914103442c5188201c0d000c103086001e0f1500030400d010090301c4174084ca04031010584001d5005110244076000070320101444070602d070102c0314941d4a20340350b03156910980190581110349042c040c8081a001d074046c4595a04445684000e106400341c6071100750f5194030140020b48040300c2200018000e80c4940200c0d406998080000784c1c03a60040340b0040d07582d12440714484001d00032911107213000b42c81482603c0071640140c0c014a00c0201d544000001040070728829202c400040d580444251034054080c14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 340500125 1250 340498875 340498883
    0x8030109021308240619050d2409020103060b0a12050703021303050703020a120803040b060f0406080a020a0603050717040f0c0b0307080a092117070e0306013f02030a 73
    0x10011005804d21200c0d80000e00061080c42c0c03070110b242401086015903420f50300107a5900f4503d10080c242000002803150aa0340000940300400e0f00c040400c2d0042c00909100385c030140441038540600481d280210f001617400540c601d01c105007200c001d0740000c0c0d04000103090051130b01e400d4480c070340c03558130064000ba11998007e240420444c01c0c074414078401050090945020b039442c550300c1c0c88544c070024002424201d207c50208400340e449400c3c124951030010b10030803120b40c0e501503503a100da0040034140e1195242201c00150b1703a000b8003072030f4400c029507565110202800203800080c0000030f00113850b02100792040030005060324208030050000c544840b038980c03500c1000280304000040c1f054010a0030400c41e8000140296074510030201e1542c4001c000c21042d41d011a60383c0e540d804240b220100e0102404885a04140d601c0040c4500f80c0503941c10b070384c884c026070400c000fa02e60100d02c01030114034160034100c580f2045005030481c4441c02c0031070f680789800080c03400114040a031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 340501375 1250 340500125 340500163
    0x9080607050703091e060f0203121302091e06040908070219050a14010c080d0228260c09060d060801020322030e04050a2007120c08030109021308 64
    0x3003e2540154850300202403503000c01074140800c40c0c40200b4400c10f07100d10310038031950407200800d8900074001e41b0140c2d9098070040c0302c0d51418100388045400356450590055108201055841840302c594003494200408070180c0c5484100500004021030304007650f07403110a00110005948090014510201186070901428189010098009020361101c9582c180e00c040760192640c0020000000c1ca0300043d04903251003008984001900c15001c50007040800501c4403030004c2903004040b50300035055910880c05980200d03200300464203080355042200b070041c001407a40071100000f40015039000e40322505155946c4040c0c8198bc1907500300303c0603030350080308125903a50002f5054a084c54070031000e40c2204080e0300c0291141c0707058900c65000ba603c40c800114880c00c00c0c2c020301e50803000f4900c98040450143c0100d4100d40100c0002c075201528040c2e80081035118120349110107070040e100301d107541d02c0d06040030001e500c901064072004440900000f4500701c14800358955406020f201c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 340502625 1250 340501375 340501387
    0x50a0b0d080c0a151401060c0302100c0306080312011401031e09060b060a08150d031209060204080a0b060406090203100b0c0c040e0f0708030a0207060e040906180b070207030210080402010908060705 87
    0x40d00e0117201604a0300030000c000c02d02c40040795002424200610000c44001450b4101c41c2c403c4014114680100f15030b48000074412000e044242580c80c104d40114003860140d0100350011000d41c0c0e001c00903066211600c01303184410104640c00054424801c880000341c40d014480480c0d13a0360440e946200c0402c035040c00b0040c504030910051071000c2c40485c0d20364050304a9030380240a0720f0070405807081080d9112031107010420154100c402900c0c20310120354801a441c5800b0303030203940441341140500d0414500092040343c038001d59016102001510454508003103d02c901c1d42c12084240809204164914030242c8407440740c00b5551840c44084e01001070700f040200d1803c0c0060348525519801001444052940030a00300c3c10380c0d61a243c001624940180090f026000b60040903020a05c2d000e2408240c20603d584201130790320841c1008255a09d00b0800da84500c41480041e4015100200070580e103885030001e25031051050524a8881d5110756100d13281c803d08a0318031001c01c00000e98 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 340503875 1250 340502625 340502651
    0x609041b03050a05070c060e0c0a142103030402130f0507030204060806010906270b040b0702010f14180414041103010b0409170a050c0d0201060603050a0b0d080c0a15 73
    0x1d12940f01d0701031030051229060080009142c031103076107005001e660380c48000308010f00d402c1c02008003580001348616140354481c20f000103c07481c0c0d07526203841941c03103907000c00c42c51241c1c0c079441c80580c200c0310145046aa41c0e80901c420300701c40701001442e9940e00e000d0301c82c2414940c8240c5005011303e035001a00d80e414000d010380000c00140550307041c44200c1d5004c008059018410080200c0101e84040030010f00b0404440d00750507642100f8420b14001c80c0102d940ba2200d005400680c5c003da8400c126200805401d0b10305220b40082040210030820145c0c0b03001c002c00c000844c10880c040c0c000104c00a10070b0129403102016075040b40c0f441107400203200d192401b4000d4618882040b01d00b0801410540d841807900d00034034852807034100d00400c0c28029140158140d8a5800801050701c1c0045011003009009081e20700805011130703d00700c08180001d07154420800000b40103812036040e800f4640b507072041c0e500a144c90b49018492211050001808140c070302074016144a00440c010f00281c02c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 340505125 1250 340503875 340503881
    0x2240f070c0509011d070f03270201021e06152b020f0609010e0f01030b090112050106090626191a090607080a05152808010b1e0609041b03 61
    0x11107205d041018408804203840c4080205400103c982810200800b0b42001035000e048a9002c90300040071100c007040540079a0340d604c0780c0c440e1007642540d85c1e07144c035072400e4104c2e120100042c003000e43c030800000d9042100c03580a500281c900400950503071881050004000c4810400c43d50b001601c03031314490440c100754154010700e081c1292100d080007400ca00003000080c01c3d83c10340c0e11030000e091402545034040c0d031181800ca900540398921304d68560200d112000c0d480281110590b2800000183d224054840c540a84211080da030390384450117841030540c240d05840c2c0081500500e10391040f10002d5001000c8100d100d4a4504460010001c00e400001401410001d10f50082010071900b5035202e550705501410b50000000d458503007643c0c240c0a01ca00c4d100e25600701c55500740e0a0840922481c2641301e229036a0507406086813103600b81405d03101d4001189801c0250641e1207040078054142440e48050003400f800c0c1131032014130003d42030b9982a0645040c020003541c1c5171800a500d80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 340506375 1250 340505125 340505129
    0x15090b070819050a050a121103090f1204060905300709060f0e01260d11010b0109050306070f0e09040f031202070803010b0901050702040c02030307020c0d02240f070c050901 76
    0x1081050400003904c0001d022031007100894010001e0482411154240d00d520401400d0710840b480e5841c1d140c0307000e945a489001ca1202d0b64540f06600c00000b4141c04c0204990645a40350765601609203400203101c0401c2c411401ea001010810044541444003400000300340b1140000400c612460410440111182c0c1e400014102d45561018051250340b2802c4a04507941c907046c003008911161054508401c15240020082c000c0c098a08050342d030102010424000560081000078403000056444580c1032042c241c050304031a0002c0d10075070040024036400c900500384504444144000120011002c9404a8624405080907014503902079100c0302d00c100d030200218038020490700c1e640d06038001480b91100794840050000c0305644688180d131905c55019000b80207551a1940c0a074894108a40a10051280030300c8150145404414181c070707250050540340d100c4508071031003220240b00410b5058025410484552a0f035202030080c25120b000d441c000407400e04000802a2401c03042e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 340507625 1250 340506375 340506377
    0x6060e04060312080408070606060201050109182a050a0e07020d0503071b0807020d0f020909030414121e07080c1e0d06060b040e040611120115090b070819 68
    0x1c40500001c0d07160002c0010b10410750424241d41d94a6142c818420300c81c008005100c2401c0c240c001074034540541040e41a6910744000f40000d000d0722100c1d41e010008498094241200d80c0c5055018101c1103c0a401d07030448002d00c407001b141c561021554101980d400302c43c49084000801402681c14000044400c4081c5001c62035070600242c0200355014071991007454070b6940148804209040045422090b8041c0024462203881c0c00c00c405a08803100003a0301070000500041d4590f840481181c09a50000844048030002c10003401b502100c0000381d1802403103024132070a2800300c3d00344c4075042d00b00d41e403004121140c01c00288038281820901c0c00760042e010303961105800e00c441c10b0b6001121006032256240300b00380c0d0a01501810341540f03c1c2c2d0501400203404102c402005603807510075402580140220407981c4104c1c65a4400c2410a20507100602c0040c0034040701d10343d801d090044145000000b8544030300c20701c002c07540580c0d01210082400528a0920030940011200340141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 340508875 1250 340507625 340507631
    0x41a0720030619090b0a0f0608030c070b090f1c050106060e0a1e0f06021e0a0314180306070e0306060d05031e1c0c08150a0302100e1306060e04 63
    0x31400440e940e0761010f00310000b480800400d15440d1815a40908060380c1c00143c0342d0401e05003a40f01400130408400d0040c5161304203140851001000011240c804101c0d600a006092814005180d260065101103500c0b40c04000f074041160780b4524101140e5000401241001d0554a800c1c0e003140d1181c2c0c402828489000c0080201e030391200f41c2281220b250041b620582c403418218590183c0c025042040c1c8884c401e040401c409034005001d80360398070540281d00251086000244e652802c480c00100001c910544109055000d00060300402e00345001c445808100b01c00002e040101c02c9941c8030024205402c01040d9140400c03440d608030000381c42c40c1a624481d922842d88a11540c040c400c540000e180410300f0a1040c58102d03040c3c048065011034a003000140a03902030003240b000040045c0c08080400c03d0303403141c4c20400c1c2004e0b80080c03820185500c1c1d0b41c203103d01c842c1151145010f209100c050820b45440342e404400083c07400c0080050110300f0900007620144240002e14000c0346 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 340510125 1250 340508875 340508933
    0x6040f0623091005010203030406050717070504050109080303011419032901050d0b0f10080a0609050c0a150c0309030b040f0201080a0b01051611030f011a01030b060d0b0105041a07 79
    0x18000c42180d0b00503420000120741903030340cd0350070780e400820140790410340b6901e0400c220300103600001030415a002682d600040a9840080e40c2c0c2d2404280105510030012428001303091512000500022031001003504c0c00d195030703846001599288030000c0141e00c40e0003641036810210b50886038003600c81211400c41040c503e0301e034006d40d183d006080f50314011000c004282c4ca80184009000203004480446400c00d0131850010090084d070750f422211441a0030b41c1140ca0300d082c040741d100307880d081141d51140000d002d9013215003000201d800e905022031020040041009000143d105600550704514044e24600c001840741d50000d041515252034600720500582c0e2010407103150400c41d60307400d80c58825504007902e0001109140d01c0c2d152007420741304500f80d2410342107002e000f000d151a64032140d8103d00194145d4001504242c0c0c040c4003080864050304113a07005540010040c507100342401c3c1c546c01d0403582882502c030002c42100012450008200b44160042030920f50300b016004140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 340511375 1250 340510125 340510127
    0x70f030308041416090b09220308190c0507020a0602060c0723010509060901150f21060204120b01050d05210d090f03020c041406040f062309100501 65
    0x19002e803000305550710580c45081824001c2011071a450b50159640c00c0d91903030751100340010890101c02d03e0061000c00b0000b2601140c031015002058010844400502d03940c1c0c1e01210a09401040146c40400c0200c0b0b03680600414842c00b5201000307521941d644008900401040381c100341c1c405403c55100008200030b20f4019010395025503444050180c10603904280404e4003552180144241d61a00e8100300000f8000180c0f58003178150900200100b58410003d109464520b00542001c00d07c200810040890b01030350000c150b0149428042c5818403d58950061364007503030101e038000301140c00800a000e12000c40c40d00502c0102c1e01c800d12450281d80361625001020031307120a0040450004c0c0425034040c0c200d9001c3c0c90341e07000400c500800c91a0000c1094803400040c2e00500c0f03031f884410082c0c1014815210b00e5102e400d0003c550743e60300300401010b401c0e07080d503181e00c0544820001940304c0f07001c00141c00b500e2010040005000e8441c041c000045ca0081c1408100c901c0303040100201d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 340512625 1250 340511375 340511387
    0x40915061e0207050d020a2d060825030902030a0605010f090501180b2206030c0602030a1d0d08073c120302040e0414010c0507020a151107080c03070f0303 68
    0xb0307013040d584c2e20744002150000909021096100700e65021004840a00070043d824144884207982c2411010039600d540044403106005c803802440d20440ba101904603801ca00100c012a004600d000302d070600d440c0d8046810528074a008031a65070b102c60040c0610094a4605000703003401000030403c0d0362401c0d011414400c058a5100c000c2031341c1d09848569503d07084c00e203166864556005203041980340c0d080360b00800c81c2c2d102c103850b0300d641c03124041102ca101000302c504c10304083c2d551311269500c00070311840180411800d0350703004a144005500003000000070b80440c03801103101794501100c4040c01004400c0c0000103605401c0d15034007459201010841c80080b164201d03150740940070002c03609400a12440d0003c83c0034030050300800c410440ba1b070400416880c07500b402401040340c5404103450328052888000d5002c106a2800d2021f80c070326400710319900600345030a900d4400085802414100340390814140364010b003400708182c0c02c04018600042010001c408075136407468400901d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 340513875 1250 340512625 340512629
    0x405100c120e0c0d0507080105061804060e07050d150e160e060f06040905040312020313080702040b0603010e0124080106051b19060f02030c0f0f040915061e0207 71
    0x840355162032140681c2000c01820385a0f041c06004000c074200181822603680c5024400e100d025800c100001d003003802c1c40084909040c842800078101501c495030366002900c0783c1016042a07120b810b0000a40e03503030f00800381d00f50b180038400f850007240700c00000c0415500a0031003070007254030000d040da4080b12004018402c4805601c0b4882c0b0540f0fa8500189030301c030402528a901007404900810300042941c0076901492007034a508519103d4854001e050b030204407801111a001b0380c0c44107001c261191300034500144028000600401131a002402a03002031701b01c0c200c19a003000c0140103406144241860780b83c1c1507070004003804020000100f80107814040c06c820041c1c0407071142c06015030094609024820003040c0c8814810a2451009500700018151030050816244d2014811180b08a9010f115071011041c42c00880080400c0d2984c0610080c03880d0107004c0000140007085489000c101781c10729582c01d2011464004024144032603400000544c50544d103810031b00f41e07000140801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 340515125 1250 340513875 340513907
    0x6030a050c120c03121206220b0f04020403060b03060f042102030c1e070b131401230403120305070905011107030b0c030402031e060a02090a1d0405100c 67
    0x12842d4030181450031111000381c052181e4202000c941c5140c90141410303508900c07908a0b56039482c1c08002c50311035400200030f02070004040000844606401c002c43e41c000240c21807500c1c500000101c0e00301ea002d40e00940b00303195102c00140d642d25083c05020f0304000c94484103500b0742480d03180c0529490302c00c80d259002060b0040c41c0c40c9018024010780d0281090001070301d20080a8260000380481d80680e2201d580c001c0320f502140d11201f100584d174440300c11308000c54510b810146c4924010413640025411b0101d101859000400029424418801030034401a10f6610b907181c40110070140400c2c80e02450b050404004000c0d51040b9041c04841092070082400b10782c8002c1d0300d081c182c85402c041c050b94012010482503a00d810021401a403081d012198503200741030508c01c103001d4800180e60142c010101140d03a410a40d000303405030620041c941148a0380e2048007a0000b01c084000d00d000c42003c40400051007801d01c81c0c00380d0901c100308c0903c0b84028038200140400102c40c4101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 340516375 1250 340515125 340515139
    0xa0503060d030e040e01090c350705031c02010b010503090c0103091523180709050901060b04030f02120303060303041e051210200d020a031116020906030a050c 70
    0x100c241446003c9005868001130010856405200801c0303000e8949a101651300744411940000c8442140400625010301010703c0da86414109a4141e101080e1112140440c440c001022400b42da050014002800b43c1d2010f001500c2e03a4024007a09440e0461200d50502c0030074010000c4820010642502035802440c000698604510744021100f2000e4030400e181c030f10b4000805110400d0007400020725600d003810034060b87d0b03450b03100d03030000c0045a203003510ba8110190070070070010a034004030f401100c9032001107070342d45d101c4940c0d0b9040d42055005442c40c5908500303280a60074100361390002c0034580000303980341d490418080307a030b0b80c8a20700c5050012021702d20190003018061807a90302400d40240304040481300401e0459031401c92942c1c50341d000e85071465180d89404038030700034060400c0c849060790a0900c0041e100c1c00941142c400501415110300d01c002828040c030700100000080003607680340c0f801946c01406921034008108030f010758400c0c8203800214800040007020640111010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 340517625 1250 340516375 340516399
    0x9010c11040f050c0a080a090804060815040c2a0302120d020c03030a0b0111010e0705090a0e0106080f07060207080c090c160506070e03160603231602010608030a050306 74
    0xc1030003000200b81e400702c014645000c0c040e801c480100280022051039555461a4807080c41384002c07240002e1009140c0d1104000c01c11590f070050000a506c0500300a640720201000d0300440e003900e242413203035400030b0007042004d402c29411f2250803ca01c3d204540025980003203640180d922804900360110241010400301d81100540c0c04513504c400020f0162612801c00451100c05005040403507400f0811104070342c3c8940005201b0b0010840040e4010030174070b854007082c04a4020041c048075206502c640d054030051500b40207100042040d54001e048212044030f03650b003000e103a0307040b9508540000c4000c1101040015410850b02c2044a407290a515000c102c0031403032240c903c858a6500c040900314050140110354548102d146845420f40d884c480020180c81e84854400300741285003068040c17240070f21070f40c00002044544041042503452802d200184804101c0341001c50300078100c00c2d5a403040e4280111401800d6000045040040d928400740580c0001003030103005086080c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 340518875 1250 340517625 340517629
    0xa0c08090a03020604093e1b060907170d0905060a170f040c0509070503040f032619020301061d1f170709120213061d0108010b0102010209010c11 64
    0x4400443c2d0083c0301030366603a44d9904e00405003840075800c0d840e00310040c280030710402201051700052030104034181203050503c4d400c45000d41202200010281041c1444e00d6102801c09c10780c0d0103004004000d2981c10300c4d0016017a2040c101c4415400250400250408500d40040d480020384104903403290319004450001c443e4220700341103c0c03032048008000d2000b080c26608415000c1e42c052049001c1c05602c5a040c441d015105484900004e00200000f80101d000450102c039158400d01e005000c42103035601030b10503510f8040c0c0c0c0e800407507808824440740404240341c04040048441d819402c56151604c05020410502008500702e00350540b448040c0e5112841e0075141031202c1e500c0d04050719100002020f454128955049041503a0041781000303006803051402c4540781407035064070100c20fa081c085500d03203440d5240500b40e00ca0202241070001218424219150360307858142d0b6601d00002542940e16103040340d4117591042006849a9078448183ca030318580048602d0503003c52180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 340520125 1250 340518875 340518889
    0x3240b0f22050c0d0f02040303050712030b270901060608060d050109050304060503090c0405010e06190506030f0405060f0f0a020307021009060b01182d21020a06050a0c0809 76
    0x840c16a03031031818042140d20035810f80540025019494104403a81589050030128403407400050045030702440814001a04505c56686101807440c3c042900003520010441000c0c1c820203205944042104814124180c511301d243e02c188000000e100980c6410f41c0a8054400601958001e0452038502803d100c1c09400402d00141c1c0075040ba6500c0b80c0c0c410740185550415505d202d1503004001640903a8503142c007403141602c101c0c2c0101c10554403804200090090b2525101c0d071401c041500012baa940d0b1600558417860003d41c18800914107841d000d420240c00038000d0400c000c9903414003259815041010350300100b1210010780d03a0305c414609918104004000c0c1c01414141485ca5041250981252507450001e0b03c0700c4150080c01c0c440c0020035a100c5c0500c11118003100c00007002c0d40840a084140ca034006000865843e4036601028010102151154542080d502c014011420b140310b444000300140e00d0014280b001c2e2032001444280f035810043c011240226980b00e09a036a80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 340521375 1250 340520125 340520179
    0x31502070f080703080f060414010b2a0303070e0306160c06020904050702100f27080906070606050a090e0319030e0a061e0605011b0609080403240b0f 66
    0x1955483d01d6004901d4000c100351000c03508480c2c03040800b030120705181400e020340a505080700c08200300c546c1c2443d0840ca0309070800484040c542e210400e250f000554004d084079241800c01c0003866807450041c0010f0882c1c603403104018002d901c04010070142905823171040040c8200c9240c0f44c10720701e0190900c64041d004076a42190701c035142c94103110005400244440d079401903800d0902010340003682030320448130801c140c4610120b0556007542400300c1c01c4040c6c10080e01c40ca0802e401e00a0b90004a8500e4000c2c0c401150710580e80d00c401e01c4a803808850f00d8005141c0b4410610a40c0400c000680d228020b43d8034402d410400521102c1c110390194201e402074040c1c003811aa10064a8104000601090131280702488014089800b014126006101c142c400c10703107401e04c3c1620150b45208251400c4a02035845a590303210002c0042d080d6001400118041c0403000e0180c1c0410000041648120020040043c940541c00c21281c0b1143d00000c5400c8007250f09080f007020051303aa19601d2424 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 340522625 1250 340521375 340521383
    0x1309050408090913050f06090705010c0204020d02030708040302010f0c1202070501060e070f08060a030b0115050d05040309080609060124050409021306020d050418050903160303020306150301031502070f 89
    0xf107000c0101048005002101c3d05002c1d104840d140d080d03008940e41c0361803055480031116000140140a154000c001400c8020300c00b070801894000f12200d0107049800a840304400601d14405001c107040d4240030707401240f00c20800070080240c411802030304840c003242542c041c0075000308156091080a40c0110b005154040355004140340c2458014050b41c00140c0d0480402da0082c04100281000980042600d6108a061000e039017080c021070001d0340c400f40c1801c10000104120800c010711406441e0141d8425162000d480d810718240c1800c2040040c1240c10740e502200042000a0810040b00c260f000030326403404c191403240340c0803201442181c012501250000501c02601c0c1d5154490b0800c0b90100d41c00e0311800d4010b400100c03524855480380c3c0e01c0360820f103444402030b451580c0c011508840043c0072030f4948074441404003401d040d50003050300801c0c1e010080004c2d0b400d0122541c4040301c00090720601d03540c11590f80e0301c07141d00d45580c4000c0c0c0c10340c0451290100121a00703420452508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 340523875 1250 340522625 340522639
    0x601050c0a08040918020306060d1407031112010e0d0509060c03120f0603060f190b10081f0602071505040e0415060605180127030c051005130905040809 67
    0x72424445007541c414494104a80d190507042d82c086918418240c1c030044e4001c0c054042070322601d00300002c05855802c180d83c1c0c850308024401030420204000d2009510480315207110b4000c10003003002000802c28500c1c0e59034140116041d030b0000100e041c510748144c2d4200130340c40300f0002020070200c2c000c0b5518000544000158038038604c0c110380300745129002c0600c06690700d50b20582850340724002903031119100040c4402180301c8007103018001241445014000030680c103000d0005d00201031001012000c03404a44c240315291400c4265503220001c810301c20601103140c214004c6d601d020612401c07035854852070072515190300ca10f003100c00412091014028034209410703e40456220103010407595482c184002420502640c20f490001d0158141c210350201098010f40302d81d140000b802c503504a115000740c21280424061101860081c1e01f20a030701402d01e0144600c80d80c15107213220900c0414018900c42075a442011419103545180c0402c944d02c1c3d520700784100c0c2c000c0303541d103079803110f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 340525125 1250 340523875 340523893
    0x120304080708012703170406151403010e01111b10150806010501020d0801091802041a0312040e1602030c150f0a0908040605091201020c0d020f1f050601050c 69
    0x2505401c443c41c120003070700c000c09100b480c01340d1400d2400c0040a008000c14070029412075150919000c5a030702038055240420808900c0440ca031107603415401c0b0442070041c00518401c10f050902c13a280400300c14000030030045111040c1e03d1001d000d115020706c0d0404034100500304104090100c07030319281c21032400307100c958440400d42d42d40c00f8040c010440309200f804000120f940c400034003c091441543c48120440e401c000c04000605580302008040b00350b02161000181c40c3e600c01d1a04010186442c5414421043c0416040c4200401d042036664018007080c40b00c0728100c81941c1d04019000c030400485007964209a0a50007840f0014605001d1841c407194500750302480141305d0380580b1400f444554a400000c021186094800b4080007824407050010501030030041009980003466413803000c2c01210020b09a901150030360719550080406803950680411060001e089414050251801d010903a90000e5084042104819880308081031982e4021001c0701c45400365a401e640d2400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 340526375 1250 340525125 340525139
    0x50616060e031e0306060a0f1707030509010c080606250b0c040e070c03020a11030309060c0102040f1203020d0e060d0207030f021603030804110a05270a0203151203040807 75
    0x107049052288520a0302e07000e0308003c010081c00702c905c2141c00a000e6400d1088240088a1454580c5121001e01c0f403404002964241104c042603c42d41d150b40e00802c4510708010300307501752580c00d0401e40600c41084240400c0781e54443c1550315000d08802c0000302c00f0311b040030f1010b11040000c0040c0c4401c1410040c48070300c3c0b080400070002d403501040c2d079100384c2c4c6400504640300019050046e0068021134921000100751140b00300014078010f00300d0b41404014800206035501440c0c9408044c1e500040030083e140c07403411404000c001c00044a0b04503981d82e10065110400c001d1420104140c1e0300d41e030b0019585003400e0b103035030051718681151544017500d805400441046201e6015100b4070b440b2102400041c100701003500ea160b43c0f03421480d1100d54401001000c594141a8401c03109213002c6400e803509690503024900e0418441303400c42c2d4614005040c407a0203040101042d0040041051081041c40329098901c002d403032180c01c681c1c0e003955482c02d40c0502e822540c41406480700001d040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 340527625 1250 340526375 340526377
    0xb07020907080112170919090606091d071704050c1f140309070305030708030a0b010305060609100c0b07111002190c05030706020a030203070315030c050616060e03 72
    0x544295450012a25071620070388614109100d40b8000e001e030186007600141aa400000c4030903407219002e81011156400a4060b0012101d12402d1064010b4100014010390140400920442c02c2c10341d0703051304008952440e52400d034400c0f01c05a0486000c80c100d10301c913000f00c05084a11140c07102d01070805191482d04e851165071401e110740c40000310840c600100b041d81d41009003450316090f003001004003040e81d075604000c003842e07a06d0051000000104105100424402c1c3c405d010035692840c0100749030003160a1880803504042c0b801c4200a01c07620741c8000c070b844d07021040710b0b9011041114801152070322100d1000400100b960405c1c8046640c205041e1440380880b0426102100c1d00c2084210481c000e1800112151642d03620020b034990103035400c0f40c000c03800b0300241d9242c11610741300c0a05aa1007800f10700c0c00286d00000f0012159414494500c1a0304c032000c10711541071440e01e456030340b0f05490140354882c550008107403c1180e40f0800c09035016030300400a100180441c15103c0c3ca07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 340528875 1250 340527625 340527637
    0x1309020427110d0c1b051c050406020c04050402030309040e030a02070b120708130515010e070c200a12210f17130b15100306050604030b041106040b 65
    0x1012024a140740d561811501a161042e501a5905030424040c3c40102c40540400c0b12100b081c40400700b40c04103d2a07580200e10061801030008185145000401200c00200400c8280030454140000e1054035404500c10240c4281114082019101d030300004e070461140c10140ea9109181001c00c011300040030001d4031060341144c003541c440302d0766903010790054860307684210041c1c000a000600f10070302442c00a03800841e40705c41c0e110410303203681c0c40d2440c00180c6c51902d1018601d0a004001000c0381e1503a081c0d00bc00b5500c2d0545e460b800c05d6980b210711a554040700c81544031040c01c19440c50305d0b20030f15070005104030102c140d00c1501c5d030300b00340d900001c0c1c0c1d0807410b15040c151b0490801b118044d00c0d000508030525035400e02d22a20134940c1e203401c904058003a071088000c5c038028102140b0b46c0030071180100c0c014100c0845181c4080d0030000d0b840d648258010905040c90401c024558515080e00c00b1680c01100c02241652a407400c00d01011000f80ca00f5030000c0042804100010f030f49010700340c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 340530125 1250 340528875 340528919
    0x5070f110a06270c05130605060d02030915040302070306050106090513200d0501080c092809080315031c0f030e0c0607052104120201030c021e150109020a1413090204 73
    0x12540b521b000310174054a40b039001c1d207a00450100b1600d109504268019644003601d48140d03407102c84180c1c026901003c4c155000d03030042c2d00000302801804441e10601d40180601e080c144401c1e490b04010450700d81301c503050101c072165107100b0780401242400103141400608691980c1d2282c50101e460020002802000e440d8450030b000300d5518141103d580c1e000b811060701400c11000101c4020080480394036681d011283c1b00c404100000d210240518021030f96072080d41c0c1030305c0705a0185850511441e8403030403080040c8881042c456008083c48a0b044040d140109003407180b51403203803030000c940c648035401001c006809400d02001042d2441c42d407004401404004030300340411105401140604403455231100c0c00040150f000740d100a82080240c015500805000c401c18103426a146101d06915046041c00070601760101c50307040d0141080c00000c500381804114003e114a501080c0408601390000d1940002c0c039410f8035503001000c2e0703141c0079580c1d161229606200e00f13505c030741241 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 340531375 1250 340530125 340530139
    0x3050c1518010501090c020312070318150c024b03030603100605060d0c0c021009080c030304080d080c0f030c04031a090c01141c05070f110a06270c05 66
    0x3048942403070046100c2c29140364019810102c040b10004220032018009105155490740c003348080c00c20403a80a2a0340075409914071003034103d9450042d9002015000b0464110718024050b1a0882280031300d410200255890303402c0c000f401d1182001201d02001441e05000000d95100d240b000000714854030007942504c039450703a010200c6068882c58018658000c50600100f020300b4802e0303008103c06402481c040c58408442d8000c591000d5141c89800c000508540f806d00180b60b00704070b0030030041030030f030015071070710303203010f90751610f17030103141410b104002003000400d8405180c681502c4041d001a0500c07581c905080c00b2400072035005100445000864041c403c0800481e8103241c1e21400804d070240c01e0f42d4210f500112020400d001c400501201c00340001035600c544c4185030701142043c1140040e4506040c1000303403110300048049d030100083d07403809021201c2c0110f0518040c50340410007140d4461103410001d007a8121000b061700d1040f800d20382c401444504e1181ca0100d0704140d07400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 340532625 1250 340531375 340531379
    0xc051e010b0619050a0903200103050c040f030b090c031e06061806040506130c050414060708190c0f0f1407050307050d051c090f05061603050c1518010501 68
    0x2c00030714060030180c0d4001d15004010b0308609400b80c4010071003c541ca20780f0240c200c0c0c69607101e915a5003615011035014000d0031986005580500c1401d801814070104141011b14088450300c007480f4500005090034011030120310012000c0000d19561600281070701c2c110040c0503135400c110704240900740c00a00c82d440101e40a814064031250807440c2c1505040d03080c0ea0b403039040c003000c1d040181556070042d9180c00030f10312064041c40750814151050b603410340c0d2a45041071b03004101c070710348030224440c080401106000070381c5241141c181e90443c803d05d14401c48524020760b0003100d18200a81518825401e000811040c040031003110340c4510713005114180450810340d986c11150241d590503a0080b0004c1c040340c40c0024001c11401e101d28121540c000080110003030751400e40d070704c040105150f0b400900a2001980d20180034040603130b8243d09058850b0400e4040302c1c030503200070b8180040014044154041800310341400d42c4021f144400c1403c0200e4501c0c100d03424950042c010703520b00400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 340533875 1250 340532625 340532629
    0x12070503060109150903020621090c03151315061e050102060714070812010f090b0609060d0e061501110c0a0501080c04170102040e01330c051e010b 65
    0x64900900c410f95618000c0f40c00d0502102c80110300c041d0700c00078080700c05400001655003100905c1e1100030400a80303a0703045242c50140141c0b2020b0403a031065005203851001580f030000c0d810380c00340c1c2903418100290711802c4200b410b1200c03a98000d48001c000718111007000200b070300820100c1d080c041012900b2550000c0f2140ea0301110300a0700c1c01030300a41c0c04152203038450b41d10100840c1c0c403400d00314645040c42d9280ca41345d074404119410681042d20042007180c04c0581440000d08503c0c0c004d2259041080009110380f007407a4510f80315040105240c03e07079510560061604811000c02c82c2c91504100c240481150382005403280007826810b14840c0814021440d01c2850354081e00d40c00c03459040c4001910055030080107150410000d22002840d44032000640100c0241d0b80f00059a440c189042e046911405800200c01000d00200604190b04400040048403030b003045020345108a600c011903a00202d50409806442880c078503429103100034404503100c40048008020728031510701 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 340535125 1250 340533875 340533877
    0xc02061006111b01050d05040c1a040812030a0b03060a05040b1006120203130c0b07120908060a0e0c061206031506090c030601020a1a0a0c0503010f030f0204090602030c120705 77
    0x8040025600f22650302410328905404100104030141005420580710b0400751046500803201a2805010354804004a11701c01740302c8030050140304992440c160603c850a5542d181c1c0c982c8081441c0000000614401041c2d400860f104400605644c418280101d00b031000c0c1506940c191018030076040410768402144040800f2074180741c5921208025010210000f1341000300b0441e0b058000004610000d0105500034018215000783c0030384820035800e180d00340241e905010303420312a0301c01050012101c0000d00076800004000040741800030b010b0070504000301659000c1c0c01071000f182d101c0b06c01c80f008514a119480980459900008900d0351121555059407603903000fa034a140400c0a00103d480155400141030040b40c0903c04155500010659030341c40745507016051009201c411140d90140c41818041c41c83c0c01030555041505d030307000105041c4002000d496a02d900701085445903001008070720341058045440c1d2424020318440b9511001c40c4800c0c0300c1c01400000c03500c0d030043e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 340536375 1250 340535125 340535147
    0x6110c120f060c04120206030406090c2304050114060702040906060609050f1009060804110a030f03030f0c02060a2c07170a0b0606090d150b0a060e03030708090d060c02061006 77
    0x80d449a6200811b40c090001560000d08182c81040c1c513000b000010554651429000f8101c10244480d0509041c1c4011422010203650380d00c15420940100700c031100524180b100c42c0000c40e14103503100010302c0050001c113980c40c00140441d0810000003121034100500104030350301500c1076861140b00008110703072810030f40b02c208003140700304009004191080c80f107242d01c940704841e81d0400e040058002030312044540c2c0100c6d50b0b4494008240304255240c09000c01c0c01400ca041481454841072000e03441d400001c240b1310003d6903400c010036101d5580c000e05445011030030111201c511702003c0d255180d40d42800f64214480380c104c0140503c05000982c0a491a0080c00031515030321820704024207980441c0c2d109a02c800781107030302d001281d044241c040c0d034480d00f40c0740054061440c0f4148000f80c4d006901c00d01c280a9007042940003900d010007103500d08e962124050f03554002c85000a540a401700502400a52070150110851a000190076003d41c0c491540510300030354900c41142e14003100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 340537625 1250 340536375 340536389
    0x50c0a05040203101523070311030c060103060b0102190b07020139030f021b0f12250b01031415070203090f0307090906060509061906110c120f060c04 66
    0x1015003000fa00da400c1800c0e401e503c2480c5400180003001c00030501d134400a00078101b0441000243c060100740d000043d4074001e4500002550400d14900d0000740c4484e41444040e26203515414201900d80c401c0c000c80d11294401c481c0042950a40c3c1403c402e080b00c11a0004095803828003000ca0750780481108141c0402007001c50b00e1320300c007500132401d078071881c480300074080c181c69420190000000d8006840314083c1012209134814500110341d01d08040801c2422030390304816903044e802060081201c43d802d0304003032500d1121a90f0040042e80000c02c041c05481c04040c2c400207c00c010405450b0041c849000c011501c1c0b903179076941c0070903401e030090303840c8405640108807060042c2020902c40c5800c0800405949506569a400f5010750740ca00310121081e643d1070f1000c0c840380c81c1c0741e15404d80100040e10b101c00d40b59103046801c1d00080d202d004076000c3c003c0744460603402210421140c2405000901202000380e86003031715079a2055151030300313800c0b0300605000641c15a0500250f83c101e07000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 340538875 1250 340537625 340537651
    0x510090203071a0f040608060f19050607051903180f0b030f09070f09022d0702060310180c1b170c03041d09061803071103031303050c0a05040203 64
    0x1500b203c100150740e081621054036002071050001105441001d88014030030340d00c86003082c3c60180104800400c0c4800441d109140d0901304000d040744840d803000076034506030364541c1d445440d42400740c0307410007008240d0341c02401c46008a04240d8400443d580001e00045210302140d150480103001c00114041d5444d00751040c0000740e140448029032503000160038094583c40717a101d43c40301003814000d80141c240c250300004c0703503a0800c2542981e80190325030300c204402a0200256441c1c1e0902c18000064490040030020a451403108000c0c10010400f008145000c84080104000030f08482c28040e0049400d000c03585140680005820043c1c2c0d40c448240d0521020495502206e0f0b04100340d1409148024400415003000c5035094102c28000603681c1081c520f42150001d2522500402d1644410080c103101140180008142c03030030903a03c0b65490520355142c038082841c40c051104410600d0200e802c0000c00e110002c20520805101622070074209900c4030280816032109550507030945403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 340540125 1250 340538875 340538879
    0x10f031a1e06060d060303022109031b06120f251425050a0c050a150c0321050f0901090203030304060905070509150f010309110f0a0803070305030103051009020307 72
    0x6800c0749070311090041c032041c2402c58407a40c000480e400398000703c0140e804000c40c04150260080d011900165800c0c1451800d03480703401003503c4042c00d16507070f025039402d1410013200c2e544035030540d00c1c8c25070314a03603914080c640340300c20900c41130003500c2e00040440c0070108200b0f910381d15a641c80406105445018480f00945164043c5601c00180c25000e600650040340c5542d003000a041c443d41d0150004003e0b000c400d003465050781e81c0550225116921810341008210303504041e0400e00d625031b0074003222000148c1001d5030f4901e04100341c030b02d00480882c0c10480a408942c4a203001303100d072110b440401c1e61040609030882d9039408000e94036500510024000030200e401c54200c1c20700c030304e081d1610075a03648080340c0f9600081d1f40b04c1303a008481380120b2003107003480311079841d16003824a01844104060b0300c950304a40320200c00280102465100070030381d0380b90150304000810900044942e2034416040061464200780822256409640d0700c440884107039019003040c558008000e003a4081c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 340541375 1250 340540125 340540171
    0x30f050906071107050604090f06050d0c060c05010209041e050601030b2d03010504050a050607090b1902161d06040e120a020a0f200103090305090105070f020306010f031a 75
    0xf84a00ba84030503604c20904041450303107541002d8401440320100c0032400c50082c09211040d1225a0890b5001c0d403203800f100d00218500440130800c94025080180b20481c1604115001e03100384000781da0440d00300000c01c1100702011501c04408500c580040000c2d48500c401181035503000e0320010780c0220050848c40c1120451031184840140b13044141c9030100c2003402007401c0d10021a415242c1e608584249414030000340070380d50340b05410b4905401003030f0901d16101020b0190816858012013141c0e1946c0030103000300001580d070807004003109a484c2d84e41c080740301e00700c880540e081210800400494240d00b0140602d221a009107001742c08410300e200d96402054000001d010114401c42c0020000700d0f4001804810a030700400c0603419070500c00c4c008040032498098194101440e1449070400300764413006070303071101e542480c0240d5243c446040200c03e0004078403001e581030240304000108900c1c0740381d01c0030803603111b402c0000f00d420b40c152a20100420031a400c6151907200500c01002f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 340542625 1250 340541375 340541387
    0x2090a1e020c0a0b0a0501081501060503180a0b040c080d030b03030f030405071d060405160801050108181e0f12040308070804030609050705040f09020109120609080a050307030f05090607 82
    0x1240c000d008071000b00b00c141c0c41e112000032045e1918211540e43c0d41c014003017032409009003414048c0c480050149540b5020008046202c02011000e01001a80c1c17400740c5e140c4180400b00d0044d82110207020141418109070045460501c1035074814818290007800050290003144020b14000b4091802e0000e142c0c2c060483da40020422105d03801307240c0002c14440304c3c00c80d9018941c03541c40302c0040c061408105000840f44064101240007a802c48509a160303400315a580c1924000e2802100ca511050035842c1e00c43c9920b032007403074a40646918a030450711400d0600d840c104500089400c4026002000e549507252901c0768584048100002d0010694000c01000000d1207158040d2800d55261540c908a400c0301c0d50440d5070350001e038801c1219140c1170141c0c4c15801c1030900100083c1106500181401010303208290a5104000b608024421103502042c01d194200c011240d03180d81c0c2030801020340d41b0440300c030000b1900d000303401d140348181841124495000040200900d840f080801d441c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 340543875 1250 340542625 340542637
    0xc031504030203090603040f030f050403020f210312040203010c051207030e031e0702010824040e03070204060f03030908010c050307111006080a200f1309061802090a1e02 75
    0x2544030421684c162038458500a51149004842c040b01d01100f602c1d0041c8042d030308680e041c00f001000d100500150b9245da510082c0721800300e0704030b100800d58000910140e4454a885181408080784184000b204003c030588194400c0f00200040042da110917200c60141404a034003450007200014005030080c2d000048248141003182e040420f1025503c903c12419800a04864000f2807094119604500400d070403941c0040348030000d180e0b103a8110b02080419a074640700359140c0fa0400c14002062040300c0500c1e40140081c48015280d400d00c05908000b440f045000802070100011080418811070300c80803242c2e03a400d1b143d0b841303100c412203003001800402113041c0110603989021180e81e02c6018002c01201019010200d40b9042110f580d40500810446032821444149c5246c0d452110ba400c10050848124548052540460b401024103184c018200340c509042100080c1100400404980c170031030713110145585a08001c415201210b610b064001000c80074000d0340c200c0e41e0050b1003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 340545125 1250 340543875 340543877
    0xd050a050c070e0c0c010b040b0f01180504050f040c060509030c1011060115020118020a1a0c0a0818011b0b0c0d02030114030d020609030a0503060a080a1a090c03150403 74
    0x2003495103c5402d09490002560010540e4400181c4c25940070390030700a20045403403c8400b0060750111501081404141d0a8020704021015141e03a15a802c14902040941005442003115107040c40c2402c210741000e86041c1c0741f81d44005c8000070680c0c4104229502c85001070702400158001400344131401c10307103102c010140802e01d440340c18544810002e4500804051840600c0e000364920040c0c211904480100b41080303006040d6000f584031340074010700b02c582c489807220085420104d142c42c41c0c041c42e2100c9100d401055075131014000c401000d4881c582c081c00d01800c0ea50101801076030000e001150001c2d48810051010010800b614001070307000c2041a1038501d1f008850b020501217900c00d0300809041140c956104015080801403d6401e24140c00280240e041c9013810595030f014200c2540d0406c01c00000003030a984620381c40387c3c002c0c0b01c1c60080320001801c5180200b071820542c1c8224122810400000d0b1900e080000c160081030005000fa0050100701d1100c100d08200080044d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 340546375 1250 340545125 340545133
    0x71e0c030602070b0103060c090f0e0a1803030204050102161202040906020f160510020406140d0f0f0b191202120a170706050c250c08061302030c030d050a050c 70
    0x2001c1403840c0018459544160907011096040d494550100c940554070102001700b241410700c5094840b80420303042e07070b9400d5203100440d80c84107001400342010b039005034040c8032108140404c054141d0040d0080c1c400036000da440400c07142d440a56550401c5c41500f60340d10700a4900800340c10140d11983e0110b01648000d440e19442090030000743d4401100c0440868100340c0c0002071080a004249003018500c00540c94145050402031000014501c42000e4440014040c8018101c582c840d0307503444c035450000d000e040c000705030210003000003001e0640120101c450b104180f030898143c14060310344c104820b48944116809105602035136002100721440303041e000d0300c046074090507588180001c00c0a100d0f9504040d00d4144251072018051880036002408000540003050401ca41c0ba015440000c000c061007508010942011a6201e601140166400d03c40080f1500032561070460082c1c0403101c040d10361001303141e503c900c11b081d200006042405500c101038411030007030000c3c5c20210704803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 340547625 1250 340546375 340546379
    0x60a0f030e121b2d070504020f030621010c1d1219020103021210210f080c0102070b01060e04141506030c0d0606020a110d0b0615040806040f1106071e0c 67
    0x2222080420304180c0c402c9401130024144c00d103405c120000c05801e064a00b0b43c1801d10000c08a81c0901000d000726128900c0c40340d001c00b184419028a0031600700d000000d1102c2580820b020f40ba201110100906000001e2050134003402c0c580c00140c401c0842e0380091104480c20341c440f03600f4101c0380c841281056001c000c0078900200c0d0402c114028084d00301110106464070b410040e0310f00d5081a05044003140e01d0841d03020417840071316030b0300c02a04500e40c80d0b07850403c441c000c0d00a2041200007803e080b00180086407147d440101c002109400391400c01042e50068044c01e00f802080b284600707c1d450760b002d5031040e42085000f550b009800001d1090518420308040c900380c070f4071500a1401a03002c08002d00a100c018485200040b4090340d0181030030100ba02c0f132007103104004041c4c1c2e0180c14184501c040300d108003800c803401820124155001418030b4905100d4203441580241c078a4005442c0c0c0c4400ca1038640c04803104254001264410550701902003480c442a000c2c0c1030341e1030341c020341c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 340548875 1250 340547625 340547653
    0x1e09061b07170c1e030a0507111c120c050606040905030903070b1201090204030209060d02030715080115050f0301060c0204090f03030212010f081b030c060a0f030e121b 74
    0x41c07580d00e41e295000280c5654802c02c04903d0f003154904c919900510060311240340b45008000c0746c94900041c5491a900c0d1201e080c585050090243c0080d004298030740c481c801040780411007005580302d050440c2401d0010a401c030303090001c100c4003401c0d9403c01d2000c40e0040c03510741e00c00081248a2001e90b800c2004003000a405c20700e00d6030083c4410103001442c50001c80d02a0125405040c0503d400c6051908680109004040080225014107800c18401080d95001c000c0000207000f070320300d588103c11070454000c1c844c40c402c0c425441544c0224030386040140c0a07505070790424140c1107140307065a2070058111003601804000340d07001070b52002c820010520511417050303040d000e41c41c09079a51001654000380400140c1c410414600c01c0e51f424000b41d68041070001100c8803d04810200e180b041c00020f0410b141e01d04501d51100000400d4056507401045980c220701c0d8907102007044007410006141c030303030640215449a0602c104400d917680c2a0140d81d00c8820300300705003290501501030403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 340550125 1250 340548875 340548893
    0x21b0126040b0115050a0503060118090e030705100c1e1202191e020705010c020a0803040e342f010f18080910020f01020d02031e09061b07 61
    0x280c16640b0354403140040c0101c40c02d584100c40d1482c810f28100e4604891000020803600001c0d05141c1007044409010701510740c4c22580001070580c100c0108206580710040c5c0ba940c0d0b0100000310750314040d15030f290462200520426218800c035444146100f0410415070401741620301080e414807002c42c100c990036111606c007030803074000c10420f03480c103456910324081c0c0005000055103202c0382c056080700640c154003080c180d04484080c00c01c482d060b085071001960144458000340074070310010800054000902005038052851b030701c080310180d0302c0d83d2405540900c0300072840075411081c8007502c0d106846a5000d0031200c42ca0086070f207151030700c4100b42075070409002c2d482c1c00f6070703440b08545070103820307a449540000b1980c1104184c0c44006a5907802e8180507102165205002d190b03101c00d4094000e2211502d41030041000319603a59401083e0002504141c1790b402d0320052b11010a022a240e4964090180000000420050b6074100400c642146010511072001005100100000703405603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 340551375 1250 340550125 340550131
    0x3060d0516060909051b090301060308030a06050a0803070f150906050f060405090f0c04020a090e0f01091b020c130b0303040b0403170901050403110f0a0305011506021b0126 76
    0x190055641c61400b04000d2051409400910b03029144c0000c0c4100c0400c40030743c54080b0002c13181c11584070341721a40020300409590b071015007805c000108010082c4000e40c4450151002100d070140d800d42c441ca0381683d83c3c0a900002004071300f0388078098001c1400c00202071008800c200d000f08400081d95039070790580e1001c2e100c0d46140021182440040c3c5400d001e0a680410700800900b075503440c82590941e03950800104d9130041341e00188200d8414450860000504410000c2c1c0704a410b040074407003032002e001d2094026032481c00c0342c0740000e44c4051a81c0040c185050340105615509401000314258070107202d100400c1d80c4a0310508251000c1c0040c10080444183c055183c03899814410700e10500712070050301c5040e0802080d441c682c1c2240c01d880c1520b80080740b14510200c840c0101380048121000341c2d07400001080c001003080015000702e42d1500000840412442d41c0791020f03680e403024401d24100501d911145400381d9441090b8528080c41402007003280440c40342c800705c000c00026 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 340552625 1250 340551375 340551403
    0x180a0308030601081f0e100e0c03070905010305010506040509180105010b0a02070e060919140a0f0c020705010905040f1b030903080f0c0406120b130b10051303030503060d05 76
    0x4810820b1540c0c000e00155031203091880c4228940c1094041420035031500d02038004c1d00c0c209280425104940c0d11580c0002c0c110348001040329050482e07604806400841c2d0401c0060000000400c042d44a0701560b4102d44003c0d00b1503041904000c04c20194440040803c07482e6900f03c401481143d4013405001d0007401c1c11020640d41c0c41c00500000d007042101c3e00810002403401c400c1c06401e03125425115030000010601004441c50320112001501c03103101c4051034281c000c018410304814940c001460841400c10400c1044e2a2402c16030b11144e852251a000c20b40a074010415801e040d0080b164801110f41e00085100580b0f580d2442004c09089510009544142000c209a0070081c210340005640c0305c0403ea45c50140c0d0035040c98480e0303005080401030a00981800800c1c0303031300310304c00700301d4010240c0a1600b004081400149460380b5558442d160603960b006845000310100d0f40c610072400000c60109045484c10f803060380c006021549c201c020ba0440c0d4000c0381c0d05102d04080301410b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 340553875 1250 340552625 340552627
    0x90c1c020318070b21010308030a0c051b030405040c0e130e070506040f0302030c0d0f120c0b040f0308100f09020f04050d05010203011d160e0111010e0102030f010b0a090605180a0308 80
    0x38045160303041700c009801400002c2c010051020411f00029254008503c0002065880d0041c6080f60b19010361a102030070a0905510011200b20210280c4141c54003500c080100c00b9100034200c0b160181d0008842e044003450030070303461285482d0019030303441c20032000b15000b4907a650041907255000c0d52154450611600c0d09008500d024440f10001c030800311140c0d4449900794403400c1011000f100014000039a4120300071030203014a1100b000190030082c6881c051810707040a54400181420842c00100d004002503519030007141c18000751b0b900c0c0b5884170f040360b0501d0b9204009600001008000084c14440029180d03034413030103111402d11840002d0f0300e03545418080c3c40324150b040f4101070a85160410081c007600d1000710b0055001d0f49242000c01c0d03601d4000141c88140c0c40d030206d1f000740d50805a4241e05018150000c0d406420140403103a42c031382c0d9440001d8500c2c0618807058002135602d0b002002014030440150504401080c005824101460002490049198011900307600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 340555125 1250 340553875 340553887
    0x80f04061e1a0111120c15010305010f0506040c0c030302030c0f300601140d0f0216030215060d03050318150105030d090f0501050a030f050901050402090c1c020318070b 74
    0x142e2440946180403e0804030480d00c41c001850b40c888a00800f9045130150109400582e14070400c42410000795460444001d03584038240740f030181400c1c00d03000d84203d04001c041000c80c01c0911074844803205603a180b03050106c05540c00c4002c1d520181000d142d4540c140f041c150492840e900510301020380040070700d5400c2001d11800303803410038100580c520203a41001c100301a40c004422401c081c42804d002565640c030100c1203c000c0100103d014680c510206029804204058900314000d00a03000c0b1b6103615a0300c01d00664200003142e007035810401c0852014002070085010f540c11080417250075000c80da42d40803041c5000080e203081240e000300c0c03400400850400b807213800900c0d5014603002c502142800e0501d1114280c0342b01c0e2504001c800155108d2840c401d900010480b581301805011505104003c40c1c0a04021350303003a84100400c40204440130880b00031241180040502c18400d95508400c40c1e000390401840f00c0d000d180c01c01306480012806020340030103044442c4000e40c5400d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 340556375 1250 340555125 340555151
    0x1003060510080906090309010c0f020102010f2d02030112020405270106060e100e090c07060e0601051c03020c0d112d0303090a0308070c08030d05040b060907080f04061e 74
    0x40c0c050584e0011b6002000035244907680490600045500301101901c6545603100403401070076054070310000300e842c15443c600100111160401a001c803510847d40d560140e10301d5108904c402e1046410904030810340c4e000508242d081943d0088000741038030400b2406804207008030000791981c0320680d42d114014003846401905101814500303460311614207101c0710001c1c0100011142c2d161040c10010700080481e503981040310b0010303910890034403848001c80b801a40c0c50030280642880340d413070216071481c040c0040303045090a5825030700400f002c0100d1000e1022181c0812810740716060b84189070780864588004414070054200010109440d542c0c20103c2c078500e600c2c07007240c404d8008001c4c01c81165036800381c20040d40d801414140c0d03a2407941c40c1410500b409940410100d00020a8011042040f42e000c284514003881961b400e5075640c03400c2140c0329404843c840d000c100c140022500f030390614843c180d4003d01c00e01001440310405039000c41e0701c1c00341d002a14082c42d10b0304544c00d515 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 340557625 1250 340556375 340556383
    0x21905030f040839091801020d020c0706081e07020a0605180606060a05040614090a030506040302060105041401060818071203090f0b1912020735030610030605100809 73
    0x8051184e03d0b00d0000501d1054110200c580010a54400d0f011580490791801780341009500da011160001c642c0d0f00c0d60781084101941000544844d14041c00c1c10010303249003d41c031543d22440e1040e02c41e003419102001030024070b0002130180b4003140704065804c40007031f507548105801101c4903801048003102d00d45015140040c0188614003641e014000151502e800400391400d40d030403401c102500542089500400303008540c0304551100e0111070000c180107010034994007a40c020342c04e454840e82c94006202c2503c50680000035004402801000842d110341119074201418440c2c5410307460015900314906a103c0d000088800303c42c50500c000c148d00301c0c1d5402c0080503840c1d103003040c0928000300200d6501034a03200100707400c400d03561881e440d03125070074220141c510039000b1500d41000341000c07024820804041d1038042e1514074a10000c4071422001d004007080e00003007604c0d5641e260148001410040302e0801456142da4012483d07a4442c080f4440c0044140d5400e00301d03291a14001c1c1c90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 340558875 1250 340557625 340557673
    0x6050402030a1a0a080c01030e01090b040c0e1008030a0309020d060906020a020706210e030c0304030303060512161e0503120304210915090b031f0510021905030f0408 73
    0x1107034404004c10000c401c800304030440522000d00b80001d410700e07a4260940540305805008158544000070041042030f50340001069824890303522101d5501c030714044a040003030380110202c0350701c14010424000e110703400400074113101030014070400c600c80d50380c1c109035054800c040b40d030b4607008a1141c81582d8100a400300030411441c11010004000000544428140c840400d40341d031520030740c3e13500000420840f18660621012a41daa5949050060041059008840c0700701c0f91861845882c000010b5101d40903180e070030444110300d1a080e840300b900c101a5140035180c45d00c16800182d21740d001d00900c040483c00b070744210341d2440c152802020319980d01ca00400c10514406103585034541c480c0c4490203488221103191684c00d4901002e40e10440254019250b4013400410415101e21040314280103142d99285940800e072203204000401165061100041e4050b00c401a06022182c7c1380c0701c1d00310b000d5000d0b00c0c40d24100042d03401040d03101741c020300650790144441c10406000c01d641610 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 340560125 1250 340558875 340558879
    0xa0b040c090e0a0c091406090904050c09130b1503120a020604150905030706020d180f03090b21040c0314060106110616030c030605190f0801020c030306120106050402030a1a 76
    0x804081d0100242c1721351581d008912807540c40e40044000c2c2d45804c81103a5580000602070105464180f4103140c2d0380d0504031f000c5004030241c5000c60102d039030030f07081c4008295211040c0160b56948070082c0640400c403203007060b80b520030528042000d026410083c48050a5070780500224039050404581c2106c5003a05010700d10300e03140c03806020880c04416101000e52104000da903c103442220000500440703506a20840501c10b51541040440005407030414072070b403600711b541070342c0d1880342d83e01d03000d50284450841000800007607405d0b0f6500c501030b40103100d1307403c14949a880751280c40c10507246a50180c8603034801c0005020158000003000c4078090b40500a1442c0d203406650b0180110754070804106054440c002409500e0203a00050081e2002030030b0001420300000020142c032142d480780e1001900c404101003004101030003210144034800c001145140c9860003401002e510304011002103540c3e4180204195035940000c6010f25040840840e40e1a4120fa200030f0804080c0600740c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 340561375 1250 340560125 340560131
    0x30c1302071b0f0b0a02150a060302120a080307032c0106170102160602070305091009090c020304081b030a0606080a20010807050d0905012c0703110402030a0b040c090e0a 75
    0x1002c8015004a06880311358a65a850b10b071629010f030325002d2503d00d180c01140143c002c010b89141c040d440941102d00072030300951184015402d0b01c0c0ca4080080c0041c04011041002616450003904a620300c442114502008030440320b85c1c654a450701001118081d94480e0000c111804e404040082d00410800c02146084501040c1084c201c9901000401460700403c81100741802002901c4050a0250540b2140e00c1c0303202c001420901140202164180791007800d40c100c601c000160340c25150103000410700c0e420b40c001c6007001c0007103259050354140b188007080d800241060040c10001c00e2a0760040ca24003a841c03801c140c01d107036000d2540e20b51031480f11861f05640e80c09101e65810240c20301340035584103903118640002c0c200300341c0040c1056003030541c02100300c51486005100341d40354084036280742e003410300d0407919210744d8403000e0014a0303c4460803409140c20b5008640041c240403000071840c15645c041015101340300c281401103803100d0000c122104c0011070701580842925020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 340562625 1250 340561375 340561379
    0x10906050907060903030e01030e030a03050906100e27030d0b01020d031416091e0e160504030303020c07030b041b080c01021905071d010f050103061d0402030c1302071b 74
    0xf0000451484086c0400000c171181500590003a031107118001ca80030b003a06e58031f8240c1c00c40580948403c0d00c6070b020314803c00c0700060301240d182d020034050700c0101480103000c0d21070f44040e036550102403101c00c1040d07106012481c131a03030b420401002074110003170020840f08030100004e0b0034139005a20120030b050500c2000d040f2842030b100301660007490300c0d1079010090401001200c0c1c29206800941a1403280c8000d641c040003140200402c54001501003000c40c0d0b0b030143c0c0000c0011b01018040d010940902c0b040c0f000901a0300546102d01c1280201d500306a500c7c3c40302c2e00300480a8409503552038240d44603846000298500704090b1041d800102140c02510000035562030424807000c600d6096115100100300c0e0030b04c4000300900c0400c0c015120314403002555603c4160a1050103551201c070030002035554000d028034070840c1c00301d038031407500c424003d0011003900c44c00500480e40740c05a019070300302c0307959600030848042c03030700c43c1c0016210701a0b0700e803403603a51409441038080c0d81303d40b440c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 340563875 1250 340562625 340562627
    0x8310e0f100335040e100803040302012604030e03060901090519020112020a050a020f06090c0d020d0f03080621070b1b0303250c170a0c050303040501090605090706 72
    0x40501200c0e4810000c40030000406032040702045070310300c1100103c03e051075080079607060202800a0b0350203450003084039107039020030382c0503801da034070418130560814041000558000c5030b10840c0136402d10841d01c10245003485d840740c840d40864003140403459130040c0c006d150408001e5039502c4400c10008114030480340d25940c0e0b40302880e8000212010040d1360340821644209803940c131003032008400f99240c0307044203c040c01582104c0080c0005104d02803420070011400a0700900441020b405402c2c181039002c14024078917101130044e81c01c20110a00000001c0c00c00c10b81e000410700a40d41c01a260810f842000308201548205140001c0741c100900300c000710101d403180403101c3d12a0055030b90360740b940b0302c1c00c01414404204c0481d80400300070001e69000740d500604000f40c1e580382e00b0740b4039a1402820340300c82100f004050400100049640b00d0101c81400510034031880341003110140000d81c0e40c0626580c4212022900750b512901c41c4410090180595600400520044e2120303a091400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 340565125 1250 340563875 340563901
    0x2251409090c0609042915070b131707030801030201110106030809040e070305070f0608010603060b0306152b0c031103070320070503180609010c08310e0f 68
    0x641c443c851a00001c46458650b50b03507001e80e401c0440180341a40c00402d1044004060354a8640c0a00400742044102540340e03034070040720030242d400081c40c4070980301c8103501d10040b080c0d40f00444a2130f042c8201111500040406840c41d2403080c2e0300d0f60b8180d81544001000b05286103920030300342c0c1c1031100c2400002c1030f030b4040e6031041805890001c0c0e00c0035903179016482c06c5005e5001034118001d00303401041d283c1402054405480b40c079103824080da6a55102101280c0251240c0c0b41100401d10105040f8909481c60521aa100800803401d1280512400031050184205103074201100103603c0c0030800b03140502002c030302c8942001c000e0503100074258181031000500340010141e035481551f611410303a0400c001520749034040701e51140702e10b1401959990080101d80480c084403001d91a06160410445150b01e87c1a0b44080b20303c19290364584107030b00840d2950b50980c46084005001d80c80e44903030352a1055012501800c0c0d9440d0820030405643c01401c0d107403050500c102001b0100030065 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 340566375 1250 340565125 340565143
    0x90b0906030c07140d171311281d070f110a050619140118021c0e15010e130b0606090d061506170a020a0225140909 51
    0x14800503600d66400d401c0090340d1103000030007000305051165850044c02d00040700e0300441c507a0307202c07120442c450403004e40c3c002d0000c03070702c805200e100760300844c0000d81d40305c42d02e50048070064181c511065002880c640ca081c0168180b1824002c080c00c1081000f030454440b0f50040751001807010281480341c1c004100352410010001070001d0445c0e209908601000346154040d08602928420b0901d182e0300302c224900d0710228400d180c200340041e442c4000c0148200c1c1201c003d0f078200c100b061580c200c1c82c4040d42200780034160001c50341c50083c40011260244c41c404101c0500904007050001580c0002c800301070b0019030b40d0007102810000b0300c0d40700300c0311510a40d4005412400540d100000500c0510490080a42100041c0c00480c200310301500030200da05040d0341c0310340314280c41d6032040f501d50501c0700040f844140b0103c040391095040d40d008001e400036a105039141000c0e510410300e88a1552941c2861034101003034100101083d0307007102c00c0300f03620842d0540070609000c01000d40c0c4d170b04070b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 340567625 1250 340566375 340566379
    0xa121101080907150f1d0f10020a0c0b0333040b0d0615080f0a0305030c1e03070206150406080a02090c1c09110909060f0709120819090b09 61
    0xc1c9020800442c401c10864004040010a42c55241240c0c1d00041000c00042c40c14000308000c85244a0100100751a001810030090501d10041a44d00100300c00d00e0342c4102c1c02c80c2075002d04024032020a4508020342c018100078842140d40e828488034403040c02032030010312040c100c94090300d84001440c844102d100c9400c1210040391180c4088001044501030110047c40c4510302034400090141c408a0391003204c15200640b407504c0103a6440c9a15800002802000282d0402c0062002641c0070041c2c01c51006e0391031411000c0340d02480c10a1a940245d5900c005a4440b40800400b180d02c0d407c4009030210658092203c43d16120781e480d5a45610704000b441610064005100b00a907a415580c030440c41342c080b004550941403040c8000c4c405808240c44001c030004821940742020800680261000c1000b003006958421001c0300b030507030180c003202c10815000f00c001401c095900c641c40c1a24000c280c00c590751744081c2ca007500710608184551050000202e802c000700c0c144030064400c19082 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 340568875 1250 340567625 340567637
    0x20a03050a0302040f060c050d0f0203040501050c010b04020c10061d0601050d0b031c0305060301050112260703030605010f0c12180911090306070509061e090a080105060a121101 78
    0x11803071096000c1d01032074000040c4540c00e40c20010707041d1380c0a12000b00303250040b0142c1d652400300040444020854208020241e40208020481540700d41c00420010f8202000018100700c0d110000c2d05a92041d000301189501c403501851201c00743d0704c00d02c4001c060244000d2a600740c001c001c00c840c044020031141c148003003c1200540908607800002c13070920002c0c15a141c50f625a100c01e020100600c074083c0c0080d103814001411820140310b040c1c140d85000e0083d5160740459641c41e907141c00414108840801c203130622945000001c0c010f042c1d02c900c02e0320081640f0b8100310004081d2211240b4003410854040c00200100c4c240300d00c6442048020302d8041180e941c180c142035507120895010a81640c588191010740c41d07500c3c4080d0802a01c01c034140e40c0a521440800c45642c010302030041c1c0d0246040250001c0c141c0342015a80030700040003543c03418818003c0000f440c00c021a40030490994598080000c1d40c588010510090907980001c820340003916103441071084a101400c1e810300c09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 340570125 1250 340568875 340568887
    0x109060507060b04090503031e09030304110303162001051e0919091d0313090f0b180415180f03050705070603062303100c05160f02091501020a0305 65
    0x542034100f038081c00e501070014000202c0601e01309903240e10456601004658000d250148083d24107503990107802210025820754580341c40302003a016460706410741c9840100011241d0303100c0c90501d000308500407001640d015081940c0c040d494198545483d040080030840320b40c4405002d4540c001517040d00b110700351104580c0005c40c80c62050b80c0c03201500da601140c00000d1218654120450701403074009210310340c03500c68000c03a0341c9004030502d000030491601010301190b000d41e4071580f240c0514800108007a41c41c0004605100782801e4030700504a280c404010038801c00b01c803191000701e03079000d04201494401c54041d0300c0b40000f00008100d07d620f44108d5061602c14016255407a8000d000d80c4e807016944c90f00600246a1031003449001c003286a03072000504640001204401c20190107040085202c4140304010455100361506100d0b01317000360f149104540601c4040c141c45000400314200480c010840f910200400400d040d04d0300b0312101400366400304401203042d90500301700e074481c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 340571375 1250 340570125 340570133
    0x4050309040e0307020a0f080a0b100906030f02031c09050909030c01050708090d0e130519020a0306211a0403110d0c0b090d05040b09060c07080102091504050109060507 74
    0x88114812568094100303601031110381c030b010000b403901030b10886082d01c0555031888240c90f1111b0612490000d40c200c3c16503140802d070402050755100f00b003505c1e2007142a0f00d80000b0000c4a400d13070800d40c0e4401610360700f2000c5003020401c601c0309107101c01594186035251fa90050401c0c0241c09151300501714000820701001040050316214221040284554034080ca4014020300301201c0e85074072886440d418042e07043c0151606907072414050051000b0715800300d56100984000303400a42900c210100c05c0d00d0b25038203880602404a42550080743e024607004030300400c510a0003c50380c18135820254440042c2406041c1501c4100e030b1891049543d0301c41c01c0c00c1e51070060648011580b07020341c1800c44500e0760b0008140300345600ca2000c02c0415103803080301c41c0e91080c2001c22540072460401040c0402c0820310003800e4801c000601051800304401e0b903041c1822000e91005a11360b401054681c1c080c90301c400100382001d88a05024103152411000805d80321a0388500340a02000003180b5081c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 340572625 1250 340571375 340571377
    0x90702010e1902030a1e02211b12060f07020f01051003030c150204030507060809060907051507060219140703080106030902010c06020a1706010201060f1517070809010f0e060a05040503 81
    0x615044500505070842d40341c418541b1000040d000c9109505140c0507010000740b018005c4a1150000000c0203910500c0003509005110846000d600c420400d500d405603150030817205100c5d40d000d0440e159103050041e4040d1509107500050307010769051404015483c04000c0301e00040300d4062420024603207490404003950703029515910700040c0005404018010001060341c11070300b00380d4680c119917540d43c5a00317448030000e40c0d405425812002d4100038a1a0100203403000b5003c070b0b01c0c15803501d842c650f54882207a1082c03082400222400c040d01c0e5800e6040b06540088020000e6400e291034066580180712900501850040c0b5544142e50300070b6900c00c12100242a84c07000003117640f0341c0070b03500103080c1c4000399182c40221102840014025407040c0585811500040200c524141c00c2c084440e014081404181082103d11105442c2c0c0c100c81180703080c025866911481341e641031501945007502c2c50041d09000703071800d21194072109400000c465520218820340092182c81e545041406c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 340573875 1250 340572625 340572643
    0x506070f1403040605071a0c190926060601081e0a110708030a05010605270303070b1e060607150b0102010e030c0d030506040902060a0c14070b09090702010e190203 72
    0x1042c4030124001c1000798110004050305401307050250401c02050907200c00340e80301110742200f181f80c203000c02e8000c06085105101e0181207420480040c1e601e03081340c08401402d0f0284d1000104041222800310003007800419000b88080c6410011440e21409010428182c0c030390301c004801c641400508110f00303c1d48001e406214414216654600038204029960000e86101c0c8886250500024041d03000e4030494442841d401c50003150b04180c0c8195031130b1f81015000d125054041004404001481500c0d032038400d044400000c840d12010011301f4542c0380d00140b4460265804118030004a50007404102c1e0400281d480491480010720040740500540d00d201c664601c008030718841c0b1030001240d2444a041c2c01d0382c040010340d0f1071404110544a941001035044401008803581a17440350034100d0035140144200e0102039007207000b0350b00c0d26607550710582c40340d030b808104c0d80490700c0d004c41a81c1e08490544028002c19464840ea580c90b404603c00094005001c40302401c00c6460900042c81 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 340575125 1250 340573875 340573913
    0x9030204291f0c1b0f0608060409111306030804030c240e100c0b0f01060f0e09040303090305040b07030824030d0e04090b0108010203060a0f0608130c05060d0c03060f0506070f 77
    0x40e40e11102c0d0ba02142c0705000309800714449400080c4207049c0351040c0c2801c0b07030300319441500120260051001100c60100c80380266901c0d0032020010a04600c0208020f60bc20304d1035194952419011084855060407031502c512061514020800e070b2007401d00515880850702c5c21031031900c44405884034020700f040103281540010802401400980d03169040781c2d041d4072503130710a041d0000c5c203d030a14100c4041030b601034201004180800e2099001c074200c0b5101cae0502c246403030340301c1c3d03080c4000760040c440c01c60000d440d08040101c120003440a50b440d048030007217080c1d188621000005d4a0342c0044003044104a61615480700c2c1e903656810801d04542c109602c081030b9616582841d007c0e40c82110b01d02d0281000e088005103c01c0d0f6030303116000300c60095541c80c0680d2205c980c03664a0312a22501a5040112000042010f65884005000c2181d181c0c00c0024007403590710000d0140c980a034046513a08100400400030f07916410215050b040c2e121b00b12102003a0540f4000c9030f84080c110841c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 340576375 1250 340575125 340575173
    0x405070c050a11010e1c1707050304090b10030902031e0102190e1002070303051204020315150a05060405010e010305041e0b091216030e0109030204291f0c 68
    0x4028083c14101c40e034140c44003030385e820301403d01e000700380720080d4014003814031118896490100420300d5042510101d0760b0280c2594a0021151141443d5802036040314620315540d10701d079500345c981a198405240c01d182000d02ca4210141c002948441c1a03000d0180f160030202c0c0c28040f035407020f604a41c91200034650504c4201c40c1c211009003000c010038071240c0504c085503000c0c0041400026079104580e40356583d5441d107052108800e05100c009002244c140c4180c068151600d5035402500c0e210b00700c0000d8060314060000c1c00c00040a900f584440e002d05820001440b959a0180401c001020203080200c0c40f0745540c07800100d09001006d00c0041400901e59030020007103941081801404894100d460451510088040d58410300d9045210940c2103117101c00041d026250807020301c0d005040c00e4400030b541e500490155103003000301e0410405800e21104800851450380c00540303500b5148030880140c9402c502c0102e8986c00509800d1007203c209040030441181032050703a080b542c070300d03007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 340577625 1250 340576375 340576393
    0x9080d0914040921030f09020901031205040f030b06011b0309091a030d0c0b181b040e1c110a0507030807170a080f01080a020102060105040c140309070305010506011d0405070c05 78
    0x3018032809010000041d046c11000c040403010b6021f190a52034000302005000d900e50760710301a0b01030601c0b20301e0091003000e0000280c608900b45080c0c0c000c5000d0181c0c00d060349040da0005000050341031004291341140c03807641c0003182e4001c40c0d0f0700640308008070000301c003010600c00c0d00790f01c4007041e03a05d54103203d2441188078071580076044030a003510810352204a42c40c3c4002500300c002c940e44000e40260b20405411074859414000300c2e4010b00081c200060303840200c07945a0a22907031302c082c5840d8940c8201028509540844055803407143e86000d0198070310f10b6a01e00e03446801d00e1102608000f404260041805074580c0c500404820040100e955203540050144c00b411045901c2c00d49000d0b40e8000041c00c04003c076681403100d46c141d0207080d590b130070181048020004040700400304810005015202c0c41044029409100c03400001c0180c1403551400500b5200c0042c05641007051f540c000c1409042c1c4400041140f0b40304036004251075a800c80200d8500e0b000300805001d40c41a01d040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 340578875 1250 340577625 340577663
    0x12030e01022701080c0d050c120a0605120109030518040b0d0f0b010b07150c18030302030309070f0b0a05070f021005070507050901180f0e0d0f09080d09140409 70
    0x9055241c150400302c00c420492401542d00480488121010800c1000380710303001e4250b80c3c0000d0348014440320503810f120200240c0303c0b4004c0d0450701e00c41c94503941c20051065140010072010070426900003072000149035a8000c10f5070085076030100000c0517020540d125076669400c0100600f20281212071104110f0906206002c0d02c56416511826640c0c004905040f114007221205a00031007544884071300c001000d40101840000502000121350141c290341c45032803594401507019a00a5889041596055041800981c0203000d08501d8030801c01c0000f40c05002d0f140c04a8082c10100e40350035090818803841988030741d000398001081c040c040d000340e400030042d10740180100d08507584c56498506200c2014400c1c020300c542a05065807480c000c8480b5009504441800040490550551443d2602d00401d05c3e04a0002c83d086164064050b54001102001001094010117220090303d10150115169009050001c40c00080c008400e803559040203400991010f148280d07044c1c1101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 340580125 1250 340578875 340578907
    0x10806062206090b090a0315320903040501021f09080a03050a0b01020c011416050a060e0d08010b0f030c1c060527060d051c1d180412030e0102 63
    0x10310021900c07091000c90110130b89410f0b140e0030400540154403850039030701c4480c0080401e07054102000d45598001d203011500100b25007040714403540c003142c00050b64440c080c0e090b80040c1f0b4000c4981c424002041a41c0c0c0c0024036181b035142401c500da4038502d0f442080e10282400490242c420b150000c1c0d1405420b5041e48118821071840c0310411a48041320012625080000d0010b400107000c48814180b94803424014001c100d205101d103d030454555a899003410513601055844580d60484000440000d01802c428403501b441c1c03413505581080300a0b58140944250f0020000e00400065803040c03500d8111070303000e41c0c040502c00d03414861500c0800604000e0040c1805440c100f0110a8800385429801e0022000200180705a559042c2400f0007200e03407113020b07030f00ca12030000045001c500e1111800b4012001d584d0b000d1040c4441c811960b4540700c1c618010740101d207601042c00c291408000c10980141d40710304013401504840d1340c2207010380003428500c28154400540316059482040b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 340581375 1250 340580125 340580129
    0xf0606031209121703070e1203070b180714062503030f0c0801090c03090b040b060a060c033213030c090e030a0c03020102070b0109020a08090c010c020108060622 71
    0x2664040300c4075100c58032241400900c0f44000d10400081c2004820115590007450344064645440c20029003480c00041032402000c5c16400c031500006031900511190701c00440e441107010694008106903050030390380d645072038410315111404e1051004880c1d640c00080b00c181c5100b103e9260703031043c060382100f01100c200c000c007207000c02d10340291300819003810f006004007018540c58104c40741c0e107400500800f50107c00001e008150f6905078903000584186240d5014502030580c10b04d0a24042c410700c02000d800e90001000e1002d400000d0700060303440103080c0110a035180e510f054001001c1441d4258040e4a60180e40d4071002050842c44032100c000480100d030b019038080351515039078991050132220020480c002c250420060714081c18011055917840381d219100051400c41140c07a40e82c0280b1003a0424520f640e000910140425031060b075440e08042e50401401110084d200007821980c1640402814081c4810004108d41d4403081030359010400d00880304140c1040c080c903c01c01180078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 340582625 1250 340581375 340581377
    0x203042003010b0a0303050c0f010e0a0615121b090f0b01030f05100302010804170a03060608060f0f2209050c100f02060a0b0d050d0302430f06060312 66
    0x208469651070140a6495100005481019124210340f0100c0c0d660340703e090303540005e100b003040030203100d20244509c401e944110400f8026030619460050203075000302c1040c00c9d420840070028171410711000a0800700030307401030000542100c820000703a11100396a02c8081428940ba043c4a400b480c03503000410f030305a0990741040788a0000100500311601901e41107104141c401d42032005501403035545412030b00071000071001d0901070402000035440380b490200041e881c1c0301c042005940000302560400000ca40e210011041040451503180c9445c7e81c551164031a18015070540c00c0b0142001380700c21382d0703003424030203600c142c203086a64a41e4400c45501401c0300bd2a40c800d4184140380e83c1c1c3c12200103601400164503100424809440c1d04081c003980008049242c40009500300145104410107407005a11400f0680a500c4441840c5c1c88181d242c1e10188512420200100c08680c0c002c5440301020381c070440d0a0804001c000e000030320092555107402e002105110310400c03103105007895 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 340583875 1250 340582625 340582673
    0x112050a051f0b030114070c08160309090e0c0d021e0d0606140a0b030a050601140a18090b010221090604030807060b040903230c01090803060405010f0531020304 71
    0x1500c0113240c01c03a806480c0c401da1451590f0041824203120b0814601941d01400f4624104080348419000c89581010118040740316000c081000c10442d00074519400c0c1c1c0718000d00010078421001c20040200780354024410729080e40b8007403c4800482c0030041d000800b90120380c50012600d044802444c1901401c01c0d0212000705445c81880d0501100c0f040d1011484043d003151141c0006002409000e0192814860bd0201c4c5100191140000d8058040c041d138070600300c1e8040b6207810070401c100b82c0018110b2802c01401e41c106980002d54155444c24040107002c41050041d445281e500990381c0d041d6010030001000018024a00c0c0070b0560f0901410742040a02e0852781000202e4a40040040114807000c13800d5103000c004450707000c2010040f02c4034a1800c410320120303a0031148154000c48105501000f8044141001d101c1c1902403c400c0d075195080c81c1c149400180c50070748503ca04407404800c10351081c50301242034034800c07404000410954982c1801d141c14080b038000c841d8000d0131000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 340585125 1250 340583875 340583891
    0x1808070513090201051b0c120c012703020904140f1c0203030103031d0f090a02040602070b1201150e150306040c08160c0501020c1009030f0302070b0112050a051f 71
    0x5a11942490b241d0584401d450031240c0b9180c02c480080494101400740640c1810000a440c2c000a00080c1c112400c0036151071030040002409091650442020031180d0309042007625062180c5201030f030b5011100d21015564500e401c1c0a2000f525a1451250003116001500c0da00300044d2009468855007d035510316000000c01c076544d000901c00a400503041d0392070300c0d44aa40c50b40188040c904007600c200391552a03c2c001c1800700000355030b02242268002400c209140c0e0502a000142400081d6680303014402d00c0035201208060180303c20a07000d004400e540c80b80a0101110048009441c80900b0401d290410542d60801caa4082c029410640b000b082e032072040c03500c2c1e0304c500305074a6800402c8414210846010b0310323003681155a0b40d42009907a910322410440103410228906d03000c10100110b15008041c80c0c1d81c0c0c1c111005041c0103004d4140001d00c0d404a450658680101608400040d801d005142040c4004e000d0030711700404e07030117441102690320607200c0b50b00c040343e05001c0c0103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 340586375 1250 340585125 340585159
    0x120206070203120601110c1e13060509360114070305041203110403061e0b0d03050d05040c050d030807020106080a0203060606030711060f01030b0601030c0206040f020118080705 78
    0xc4144610300d4500180000019081c3d1b00800b884458001e4990850f03052101401c045603810880701020f60b22400c40400f09400c520f028100c0704a403e11000b02030200c540f500d40807a821400180800200816981440710107840380b003410303080440d548044126a07401810058000c2c8004c010640c3ea051040300002d1403180a402500e000e5903212044a41b5000141350031402400c440c400c0c00c11498041100002042e203500407001060404540c4090b0f02d00032004900803540d00504040c064030085240e200840e0b00141625940355915001140300d680314502213580707113041c0d046280c0c041a4003134000140f50780540aa032051f2003903002085440d0315501c010342c2d2024803801c000c0d8113611a00c009209410b00b6809141c00c61064180801510303060300d80d41d07041c4030044900c0301c1148070700e500400610024110301c5070060002c4c02c08000340b40301540002c0d15407500130030107881c1c4d071a8454800c0031a441442c1c03000720301e00342c8051004000d884101460702ca00040c42054443c040400e5650410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 340587625 1250 340586375 340586377
    0xd0206040e1006030902090a1104081e07091812030221090606150d0b040f0606020f10050c0316020a1203060f0803030702030a0f09090f0f051021140109120206070203 73
    0xd900101007080c542d030740420300d02c060a1101c64041030342794180000624101c2c02c010501e00d440001080d4040007400300500c5192020b41c0d445018054101a40343c0c25042001440c501c011390882c0d2810440c4d96414010340c003921440403480c01d10b00428461400b00b40d0715450301d50080800c4010384056846000400003800c6202d03842910120041011880322803003503029042c00709001e08049004485035040e002120101d511a82c0540c115019034640641e0038465103104403041113003084a400d00c1003031980703503000c0203003144011099500d160030624020041c1c041c039564060074090300754018680050141c80d8034840c0c6401410083d0700072410350300c00310030b41c0d2141000382d005600340b6081000880d4000080603001050103217040e00840c64000138001c1d800c1c454011200072503107091145801080302e82c010400302d0004401402403110b103109200308000d00e042111304800780303035041c28505107121903030ba026a001d43ca440200d0302081010144614807000c16001e072446650360b18002c2c0c1e10703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 340588875 1250 340587625 340587641
    0x73009050d02010902090a150305030c160902040b0708030402210715020c030312130611030f060d0b16050903061005010f0203070507052205090c03070803090f0d020d0206040e100603 80
    0x48059808001050000c7c0355001070401080d1656840809a0760b445050039540800158100d9401001d1106444506a803202e0010f1444807011450503207031443c90001c81c014a1002811080b0002c0070505660b20b0071843d4800400d43e446a111a0000c11740351940d900e401c2c0b0031a60015120190b00314504d001090103030000d00d000d4051403400407a10010000894014020018200c4100780800491494030414103401c070301941d195920308000b541c400c0011b40042089114000d46410280080da210340f0300781d0070450140540160084410040e05d81e8042e030051030b40c042c41503000b00103031404810402011904203886030701b01510b418204a80b28400c0e001c010b05580d0080c2c40c20032450618100c40c040303607880c41c1c40c1031060100d00450304003603403401d4501c00040e42c0100340350070f0a490b0600101d001005038030025860403040070080f0b00814448004148241d002c80560020340d110500302d0400d00b07030300400a96407262280d540102c502d2081c0e80403089840202000710f00107009100c0c50b00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 340590125 1250 340588875 340588879
    0x30c0607021002010e0d0801090b0906010c0312020f07031809020301050603040f0807080c0d02070501030204081e03070611030a0e0102090a03080304050c0a0b040503061608073009050d02010902 85
    0x86461655028002c60400d00080c075811503686400d2102e01c941c080c0404040e482907641d0ba100c40c0d500d007140c41e1042c2c0e074988140601c02c8030b101051145036030300502d04541d03243d0f05042c4103219840c610f50110003070140343d8804448500000f10f450030142d00c019031090482d0074010040c99a620340c4801070480c0024003403603410020400c00301e0007043d40c1e0480005c8013031089120310324080c56640c0b450220b800107560040180c4c0105c020749442ea8042c0082e00140200703280071802c01d458000120342d00c59031060900020004200c1a031a00401841158203c03a00310005012140d6150f0140c007003a030040360900e181c5031410b4600d084111041c001c80b6420440108500c00480c103503102e5034520b910103041114140320f000a112015102d482e4103e000b0405882510b460740e00d44424103085c50402404d440700180303441d03045542550801301c83c0780c015813035240a0028401034401c018460004160b0701d640384491106022403c907442d0084005241b20720165000098240c00580c00d0f9256410002c2d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 340591375 1250 340590125 340590127
    0xa32040b120906090c010c050c06041d06030a05030306010f020a0215120a231504050c093c120f010f0f0b01080403050c011d0114060319020603070e03060703060503010605030c06 78
    0x10940c03240046a0895022303c081c0c0d541400c40c180042c2d500c2d0702c15881080d43d00341101c00310403102074010b00c0c294405002d401a101d1184243d032002c0d1240304c010315407414856a000e100300307405d100b0841c02074035a43c003811014150080c5022000c0c40c2d0030074903e05407003410020000d1155403050013030842c0e5222000341013030005000c3c140d902c5410b0004010b801e210000007201415607866000e214043c01d582500d07555500020004d10a40180a02d955010301803520514200d14400d80c0b250814403c048416000c24503040000900300c51004030f0300000351007404c5000583d11019800901c0310210600d0400001c05080c0d00e007002c0e901000c00d2a070104404400103008a80a50010841f0147c05c030000205005c03d4080300d00e0304c800304900018160741d90700d500403030b0080300e80c1c0060300544210700600c22540010b644140d00c02d03815800034003901c070120110314458000c425900070100000c054403218030b003550000f40140001d1046034425070819000103210305010a541110b902d02030025 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 340592625 1250 340591375 340591393
    0x903040503060c0a0207030b221b050a14040e0c0a0305010b100305070509040b0303040807080c0a09060b0304032a03020d0810061b0f1b09110a32040b12090609 70
    0x200da43c500002d04101c00c84444c081448140b105403003e40c0c2610782b040c240040803044c240700b4007070440f55a0304043d01413a40325205015201c0303803000c0f00807840b00407200824043e81c3c140d0302030f08000c6202e40e0b05400c41c2400002204100041d04200c11001e801c3c7c0b121540001807080403403c1d03e00c20740c1c01101040f0200700c510454101900a140c0d449000b4040302d24103039641c10050b00c0d0904a51140c241c42c0c0004032200018076015803070000030704104409105246c00d0900640c860304c001b400040900140040120514a011040031814080049850030f05001c604010b91100c900a2310343c000030345400001607510500328000c10940d142507507180710380c2004421580c05107500f4181a60000003180c1c180d00064501004101080011240d11070300030702e0314510401b41c1d66110400c51840506004108180c0d602c6480b034410302280c00c3c4828590840d0940380020020300c600c0380306400b08000b4010400307421000007485000c84085e502d0380307540d03030f15074007107880b01c1c01602c1e1046290028415 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 340593875 1250 340592625 340592633
    0x723090907090b150327060106180504090203120703181d070810270203010605070c0b160305030408070c060807021014180f1902010f0507110402210903040503060c0a020703 76
    0x4941307071b0b107107050100e02c0602441010b00e0071409070700c0000040c02400550051020360180c5900074602036809014002c07150317000a440b8290300d11046403500c004600c40003032520400a81c0007440d1a6000d1140b4140c9820f0240c190035141102d02e0001c865080c081074900313114400c243e1191074072880040b010b50901030b00180b81c42d503030b0540b6621048103c9130520312104910040d402006551036a90783d0740440d24000380001c2c210b41c0180c0752540c080c00014100c040302d05451040b60381c0f40c41c04030303520380d994640b040341800b034040046c1c559010034201091903a0042e81e00340c050328058080702da103204441c0001c020b803030641e0315403c00b5641001c04035603551081e200c2c52035110100310a03640d1a6407505491403a1600310048101c9048a00b01c004056580001018080641c1483e0051802c151501c82907102041c0c200b103180150350001c0c0d440107104450303610303025541043c0801c100c0c50070a0442a07940741c0080c0162886402050b000c0754031441c82c1d00031030f0410086030b0042c01c1b01d54610b4036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 340595125 1250 340593875 340593901
    0x615010809120a05090406140909030c15060a09020d0b150f0d0f021b060a1505010e190503190c0807150503040201020a020603010603020d0b0103020307020723090907090b1503 77
    0x903540180b100501560303005d0303600c9006240c00381c568035142d0740d40b1406442c10443c003484090510005078000b041a0318041d40c01040d5034000c0c009110701810207440303141c0407895074510360f40034120881c4086030303404801041e508510002c00e000c9070102e0380c00b504e010341c8212610038180c0d444103492040005006111954221303100e480001d040c01810810003001941100c1c001e4924204079421003010400d2030186841103042810440741c00d940131350304040019014006001c3c00318402c4440b208201d02d4045103402c0c1202404004c2c0c01d482e042030442c1c15014101000180481349000c001c031010541e20000070b40d42003280c0044004003c046108201541d050348083e00590450064040c54030142c2c039000b0081d07000f491540c0d40182d680e10012185c204440303003030701254100342c010400d02211907030004018050350b2515002101551142000d00071034603103005882e801030002070401c001310764040b40e03001c1102c1040b1402e2145994020821a4115081480344100074062001c43e0201d61a49 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 340596375 1250 340595125 340595137
    0x405010e0d0b070c05120414060310080d020a140c03030a1202090603010311130515011202090306090d0f030501030803010b1b0f1006080a050703080a180602061501080912 75
    0x280c01d84118401c55150218001d80c12100782d404a6406408001000802c0010001014903d0010341c242410080c0310000100d910000ca0310510300480400c101c80e1018440c04001c040c550111889194408030203501c480c08004d05503000d000e0160340158070100414205440a4020044e5140140d0740c48141c968030580b100da0b00b0429420301114540b0b40751140207601a6004030328024000750010f080080b6208502000c1c1d591908110510000707c51411802d1001341c000d0816405184001c1c0c0701d54024091400180da1511800050003000440403801e862a180b0642c0c500048500888055040e070302c080c80005e0038100c0030001044800301c2032010300502101140620760300607820306428900850841c2140c99038000304a041c1c860b00c10f42c442c410080c01d0080240081008544400e51980054031025200b030000160080403580304070b05032116889202c49401420b078a0340780080d5100b00807102e510108084140c0d041071580100301c010700c00c504040c014414044031005501860700302c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 340597625 1250 340596375 340596379
    0x120112080c150604060b07050a020f0103150b0c210706021c050a0b0910050306061017042022110d09300504031217010803030603010f0606050405010e 66
    0x520550110403020b101012805069200503050390403c1d00400c001c480c0e4903403203c800c40d00100a0f010004102007007560b5141e404984440c86483c0000c0140c001e42a4008000c2c0d84402c040c101254249224000d00010030705241100c41101e10020100d41e141192700c0406094076007885000001051600141020000c030940c840000b056581c0031000c0c0c070380580b02008160b89035800b100507800c01a60190303101642d030700c802d5001454040403035202c1c48007808040c092100c40e0401c104181c00b030307400c0040c03080600607a07030014038190030860101c568007104800903008100c8a40e47e1440d0020700c08071808080c8104e14000c944007400e043c0141000b520981a0450030b1220b100c0310403440c0305600203a402003603c00c43d1122901c000c0044400c4102800b880c0301030344003a84582541c007005072015681d0111504071100704e41c0d041a03070942810b12994400011000000c0380341203010010b1805604190004d10011070f4403c1c1d048141c9a40380a103000180d4144010007071584201000c605105c0c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 340598875 1250 340597625 340597627
    0x20301060c0b10170109110f2b0210020d0e01030c050a03150b04120b0c0f0f07050705090a0f1d0325150c020d030b0906121005041407080312011208 65
    0x140d51100c440d903100079400308050b65516242c000a000c1484090300c2d10007c1280c905c0e450606110001d100c40b8400d21180c0060002e81c000709002c00c00f111441004250020901544d00200510080d620031402c41888005201443d40c1e050139402401007401b11295031715664100034514000314020180404660740d50030500b2000100c1c441c10800030b00207010300140011000725241486030780400044c01c8100c0820040100c0741441503c4000d031052902d10042a940d5001641002840e10f002504099070046030f640c28808008074940c0032032244507008900b40400c415030300003240184030300c10b21100c2d1034108109560721080d1003040300b41041150071010340302c48103548a500d00c0040108401d0511942c48015801300340c0c0400c4081010b00041c5024000100000c020410382c00c0c010301601d0040301c4040d2a44481030003130100720340300896600c0800961070b2900f400d0580c41c80c51003030908103001350003010030407250100407218a48881d281100240c0d00e0080103420ba0500b8a0041e190800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 340600125 1250 340598875 340598879
    0x16150807030b13063510110f04060314060607030e010f020f0a06021312120c030c0206030f04021507020d12020313090c02060106030e0d0e040b040603150e01020301060c0b10 76
    0x4000d104400c05040d40d056608041184021071503003840c0082000c002200e09841e503d41c0768800001e4a240740784080c000030540c7e40341030909170b9407401140107446640202180100381903625905c42c03440008807065400658071800c0c1848514881c01d000940000c1858038140002d5000d4804a21031000f644100e4004510340c031012400d083c070700c2c542141c0b10b640007d1a0003c5040242c0400c0207003c00350448800e1940e16550f071030110b4030aa01c00342c144410b013044201418010050101629006480b040d070300d24040d0303429125140c040703804038862811050300c00070200d1141b080c2c0d003405902401da1450700d2655280d11501a06051004085101c100714041100e10100355803c01049130110105001408510107401d0100581180003007624202c1e100c084420001181c450303400050404040b10031031100880c01816007003000c142c002c1e003803002c00810024100e04520806103010420002c00c655190316500740d04c020300c10080010007071845200070030000d4104a4001e2601100c4440841d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 340601375 1250 340600125 340600159
    0x806060c0109030c120e060301121719020105010803031302061c02120702010606180e0711030a0f03150f030201140d0f051f0f0603020702060403020a0816150807030b 73
    0x500c1040d011000030703113104914005c008520859020080003070070b142c050940003401007001400305100f04c10303050040307031081e03018000e10000290b0030b00e9425030415525a400812400034004901c060001586080c000040046010041d40d000d500b80d0065014189415000c01000d1740021780031312042414500d92144050300e620042c160f200c1d121000000625001e200a8210341540d404001446050b00301c1208000c1c81c0300d05002500d204010741d11aa8640450448006480200d05406448001900045540c220140700c1212020f99028090156008a00c051000c0c084c850020110300e0800c0c140010340c0a9241210584281c080762420161100042400c0d0354482d00c0401e01e0681e10000e203d084031030013401c110f023208500c8a45c0c0c90346282c68501c44034604903105038410140d01241c5030342150741e41c800f00c0c0c1c019500103025010054450400580700c0c10703003003410f100c0440d29480021388100002e0340310044110a40340e02c06c00d40c1d81c04100358090003179400c0f9280e000c281c03528190300132 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 340602625 1250 340601375 340601381
    0x5041811070b1b030408070b0a140f0a0b0d08040506070302120414040c020c010c0308060d0f08040504050714070210090312020d03050702010b0306180307080a021b01170402010806060c01 82
    0x28007842c6200c1181c24140740703046015a409148290701e501c10810440070886070b0085544803035003c40c030041c007503031100361490041075603280400d01650f8041c1444000010350b180d40d801041209810000749001d5000c0100303a2001c9038000309080c20500041240340380181c0500180d50081c01590072501c00902d60042590007504080e5907500c01c80b50480315401c0030701c2951102d0001d030009000d140003c80c000b0b00f90380200c01d40141001040c000103502920f908a01c2001c15600180440c0650300d24074110109822500895004514000001e600c0510070035108114480380764545240c10055000c1c070080300c210200f410b0920001d00000000202c3c03c5071034030440040380e806070410b44402080242502c801402400840e070512580c40c0141d170307010610f00d070022a9156181c0282c142180c4450840c040c140c1c1c00340c101c1c6004190f0140182e0003045400b00d4408024843c001c140c03c980055480b2069130300100e046000c170000080065000d103e0003078114000400c07103404c002411780100d00b9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 340603875 1250 340602625 340602637
    0x50d0b1b070807030e1005030a0b030f0d02010902040506010503010b030403120b060406020109030e041506200d020a030809150f04030909050712050a020a080403080a020705121b0d05041811 83
    0x8110000a2100c3c18980d11403080036601e00c041b10580d012800c0105d008102c0d00020b0a810070107a0743c1d1004d2030f207603501081000d4480c404141500c00400e06000c7c064001c2030241000da0042e810040040c0d9150b01c20b5040340d041c2c2b803850b40c2c094103544817610115818075a00c0c28198445030354424110700b550300c0c00301030700040c80c1e0ba5001080b4985146001400b503040003420601490400340000716882d081d010030020b584d01d5141c60881c1840d04c40d01100700078031003940722005000341d10303441107090f601248400d103c0307010b038039980151b460701d010043d5140990111065240b840c44040b8080046071050150003a000e0b19245541a0b10303000f45c1340072107105643c40c00200f00884040014040d05000f00c4e42e00503d140411402e20000c0f18001c0c041480081c4014200320003000041c540e00038550544480b9a00201262403044030200803801c40ea000a20548602da05030039060000800090780540e8618555115030800d4a094680701c00381c0d00c581040d02a030b40d1154882e102d1141c242c006408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 340605125 1250 340603875 340603883
    0x2060d0204291c0f020d090302060702030a02030403030804081908060a0801090b0103020118090501090b090c18060901091a03060109060215340e09010906050d0b1b07 73
    0x603036545070411000c01c03801e44158001c0707440307800c0d505100400c0380c210540e8980c952a208100400d003190f90f60000070104158a050300b1880400c5081d02030040da803060343c1e950b20035001c42e041901c4411702680da0b4000c140c0c061006070b04c10881071002901c14160250040d218480e098203003260201c0450400700c10700002c000040d040c90800c00c103403074062a00310003410040003c12658440d5100d114038044d05010280c107102032640303c00148414251f02c1c4e401402d80c120700f04441c0d40c45840030009840104a80d0b8429922040850030b140d04002c100e42c04650305d0b6483c00400d03840541403110708e801551100b030600c140e8100c0015a10314814418201f01c2a01c582e150341d07403a01c0c0001412415031504404210361081880030440242d038800c0da40c200e505400895000b4554022001c200e150030740110110208030041440307465041026400003400440303400c2426070321400c40c003081354a94490142d200e03540040c603c010034100c10a454200351f200075152040b02c8801c6031442c4031703848684121 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 340606375 1250 340605125 340605127
    0x4050d0b1b0a050304140a020d080306030c0406272306031c05030c0717040e0a052811040302150a08150109210b010f1e03020d1b0302060d02 62
    0x40455180465854100380c00d00041500b0312019150060031400b000307000410000e02c4080c0c4c070100c1d0a0410610781002d600031b003441e120021601c1c04000c01e400a54610380a07100354840e01d8214901405108161180800c41070b1041e803c3d080c0c82001d010429040b18a031a07540e000341c0081501011180409842c201c0c0918074605045007814a0130394600c00307100196a80703458285400d584241107a03005054000070945500e03c90030520203a05102801042c0d080c40003c001500e02c240007643c41c4030b01982c2104008558a41e113a03103a416465100b21300341c070400741100c440c200020758030821864512001c80e60900d40c8135804104050880384080103050800300e0014003c42c3e201014540c0402d000481030142100440081c1200d02c081c0520701d16114ec0c20741100005440240188031180c0103c032189072940e540200d42c0c60145c050046100d07000001840402208108070b400e0f08884c1e0260803281845216183d2180344ca000304407988802c515a00c0000260756050098498422902801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 340607625 1250 340606375 340606381
    0x908180a0b0a05030130060b09060121090c0815180d021f020d050106091a041508090a050d03140a090201120e01021309090b0f010e06040b040204050d0b 67
    0x5060299500203661030360100b00d400d0019901200340c0f4111003500c01c25024401000160543c0c000d034a550111000e40d000d2890801c0c46599040130202030410380e02004942c440034011108400384d81501c00703400e80b0140f48181e0400250b480300345102d00481488980e1038640c0c54841c00c15001c400ca80d032581c0d0000e01071040840301c001c02c151481c04160000c150b8039030038500c0603445040703406950b40d81c0340620480c00d00c1d110b120f404445a000c1c0c03c8004000315a141e400107040071401b402030540c160141c5940b0426603004008450640d0a0007500820900c0c480c1012940c45c0402060080d09004003414000000c0081080440105141e2804a8280d04041c2204400c000082604030158201250f00740507036082000101d003c103c160010034119042d0740020301a00c0385021511b102000c00200040c00500f541c02444820b11a0401131403d407640c4c0314080c0109001c0c05a20241e540340f101003122850298800d240341003016001508060307403070b4005204803000900c01d842d403400741020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 340608875 1250 340607625 340607629
    0x40608010f150b0309070311010e06030702160609031109060102010902130603170909180f0f06420a12030c020307060503091e0106170a17070213090204090818 70
    0x1251000e00700c450300c6141140b03403400b031440e40d60300c2c40c7c07002402840343c0c2c85a2001b83e0344140e0300c9044001c0301800c00c40d903074102448000e540c1c034030f81c1c4080e8940c3c1041d10360204816200d6040c03401180c0d04040c240e070601f070006003000038400010f003605040d907681d40c82840040e210b2400451043d08161780000b031a6265080c158028501c1c2c0d4100703209100100422444d0740e03200304a0383e40051a04505181c04040b294041d4038210300040805c01d281319000c1c048200440014801d4031580400d001040c00c0d0b10348212040c030400c481f03800e20300403008500941c1040150004040301d12040201850302456503036418025415101d20103400003004442a00d0660404016020092916180651940c50061619030b00c0d901640c3d90700c000d20100243c032241110094010202414620031003180402901d001141e46a0045030122001451002030707500c0700c0c0c4054140c980c0141c0103031010021000b04600e500082c01820802ca03070043e601c02c44400801c3c40a40a042000048010100700c003041d40d007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 340610125 1250 340608875 340608911
    0x90302030c1b09010b030a0e011131060804150612020f010f050906090a0f06030b10020a051905010e060103031d04020f0f16170a0905090403021b040608010f 69
    0x4042c0c1c0403690090400b96640b2005622411201820002c0c1d460351243d40c0908003400350a0310b000400e609224011943c20800d500825000e4054841e00480000c2e40d00107003140b40c800d01c04419450402d40081180314000e00065a005108483c0d56482c843c8012849040b01d01d66080612940c0000e1040400c5003840d00c2a04000d020900f41200300e242c1d0000d00034103070f226081806010716008a8011159200c15814001030600304042c005204e8485900130001c0c915403007904d00c1420f0003000c8e581c00c6400450700442c0f00d90000058143e000d069119940f1700c10309401c08417a01c1d0342c0c8181020800c00c1c1070004e00d020710310aa03140700034484660003080d0700080e4a0081d0780700d18410404440c0360354148007124110280c03601034548400c000b40d442c42034000f04200161038000040d09a550052548005007105403441c1c440441e900c2d103650a00c00300031003c1b580140580c2c000300a86041850100041000120051010421940398180c250030344d409002604149919a40340311000b40c0010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 340611375 1250 340610125 340610143
    0x308010506030f0610170c090406150804080304030c0f031817030301151b06140a0504020d060f0b060d06090c0e011403090102040b0403080316021f0e030706090302030c 74
    0x907551801c0d03090800383e00c4500d03000a041180b0441241d00340400c00c034002d1052080103030920842c4c80d0703146440c00c2c5004460380300d0110b41d0300c00d9240910100f0480c2da101041d0040ca0101c1d5035002c290b0b5120303602d0681c240c0c8080e20a9062026140c01c92001407d103c100c4170700a403003591400f022a00184c100501d00d0000d401509526030302401c0514016800410380c8d0448000d0031034114010300c0240280d540c00060b0400c0941c0c500510b102034144010f68028841201c460304040c5038031f5492402e102c08590081c1d40095100400352090004200603420601102c60400d000248500072200000ca20fa030111880440142d20741508021210f128416810507036030f04d0421842d01010500024101c2c88220140300124030b0102c08039251140035416180030b010500f040350340c0c507612418042881e400499414500104848914650910114580d1310030f08420b0301c40540240a0700031600503282540310300391503100620031000400c0803800703641c868a000f90040d55503040b0952a180c1040048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 340612625 1250 340611375 340611379
    0x90201111c0c140304120311011103070e0a091a09010e010302060a0518040c03090b06040b210f030703030b01020d020607020a03030509010e0109030e0f09090307080a050c070603060303080105 84
    0x420a01c0780419050a4810640c01d40b0300c0d0004407082c0034a0322003441916604940d120b03100201d80880c50454103190b01a08078000d848600d500e00c1200400e9007600c00c14483d84901d801e0030720204800500415919000d62002444003030855280c103500411201d00c000540d00313021481e1104070450a00802c40360141145034001c030415810354001c24510301c40d1110017010071070006040d844041c2d1f200e42e120001c120041c4180b00c0c0c07000d07201e000ac0192003540ea054412030114400324940e4905441016810b1102500d100002c54a81d10308100342220104454018080ca40030041e10f418148010000f00e03100303440c00210b071818400028540042c95401e003003954040002c0c40380241d0002051420251b140c500030401c0e1f42c500706150b01415003442d08410940c2000c50207020036410564144c40c28105440391001c224003001000f0701160180ca6640c8590410000728010034009002001c841c4400c1c142240ba00e082075100d0751030302c1f00f2584000000f0340c1d180014070401d948041464010181 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 340613875 1250 340612625 340612633
    0x4060305130f3c0305090a030c120204060902090a0302060903030403080706050901060b041a070c05062b06050a090c0507350306030303130c050a0b030919150b18010909020111 77
    0x1168064422480d4020f406401d00001040c01c4246564500e9910b000c4d650101603100b03a5070b070310f0700200c03111042d45c001284114200035001c201210f0a209513400b4440042151001c03528640901c403095010815064140c0410400440898418002081200d205010019051130820000340c211420b5811109401b0010081008180702c0c0544500c0103010f100c00c90360351401280741c051612190782c1d02c0f16410850120710100c880204140600f549542114060350340c2c41084040800ca920703900031644d00030128081800307048402c1c4c0c001141002d443c1001c0f840d224458a40c8600014507030000000098400452a030304d00504508200010703c1c0383c4a5400c60074140c0000340c0f42c2c00020640803085c6042c05c071000c14001c100d4620340c024040902461410350321340d5403619445d4800c4403142840d101c1c40c04540c106c0441030712107001c40c035040040b00c41a9041d540c03c42c0d000d40081d0f103555a203c40b81c1c07940192918196841e160003400e207640700182d1010369100241c2418050340044440780c00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 340615125 1250 340613875 340613963
    0x60c1b030c0a0b0a050d0b0a1502010608070614030a0e030408070f0902030c0904050603120a031a030a030c08031003050d080108161a090409060c02010518030c0304060305130f 77
    0x1d0f00643c0ca00804a0404584800030b4002c00c0006000003401140d008481d542c000421007100c1e91424800389031540240a11510380851640d01d07503540c4078000c000703002007c1a1070000c80c29400307541c0002220b240800c0d6121810b41140c82c5810641050b9281d41019108209a642d0701e48010f00070f01c0344071001e40c19480c0641d451602409041815401240c55000190081e6403e0051300b40321030020381165183c0b0490340005000b44004014004002c0c0d034038003414507500d000a10200e41d44d034181d580c0d660074001c655032503a923504042e10000f4110800754010001900034020048030082d50340d10b2900c15032409032070614080162081d07101d540f0306080d05100c04043c4c3c880020841c062900f005684090803808100100b98402000e002e5a242c804001605a410340140e401100c0d80c855000c00b48200c280c2c215100d2091825403801984101300c20080d181c040e410141c3c3c0070307003420102414203440e52201135125a641d08122a082040c110000c0c040c50081d020302c062940031060009410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 340616375 1250 340615125 340615139
    0xe060a0f080c010c11030109150b011b1e1505040b160e040510090906060503010e1b090411040c0221040b04090f0b030307051b04020304020d020f060c1b030c0a 70
    0x103186100c000d410860383c41914810302030701c01d481180803171002e4000c0125204605002d004191950001460036040c4681e141966200f0a25442040c0c00480300c005030800517650483e401503102e24042d0076a0b41c011400340858040c500c00341000c01d50f0400030840c6d113032900c0c2c00e80c45d01d04020002e04c1a0140d4455264a4a90100c80071511030002e980015903038846c0b8034031030f001d29115400800a01d0800f03108000308130300c83c0c001004550083d0001d11086106ca2407603522441c4c2d040419140c8078006201120358508a4103140e0814010101002c0d41510700c0e010500341d5a0004c100005030b400340c1e850006007155541c400b4016001c04191500b02414500603501c0c0707200384e21440203101d898170290881c25800e64404106034030000e00b117940d20750203468013a0311050000b060300d60860700c4603500e1096042034001c6910855009140c08904078440e8200100500385da20303560303080b000a1048070050801004000f88660a80780d80e400303040b1800f004c16141c102c0594844d4010001290704100303107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 340617625 1250 340616375 340616383
    0x2061003210201060b0a030204081b01170703110f07020306070504230f060c06070215010b03131a07020a0b0606070b060616020316050112050705040b0a0504050a0e060a0f08 76
    0x280424075129200c600703204124050300361908402c10560000a01c203480a805d0f900500c1218035580580300c185045500c0807440724204a400d0780803445520b0841d903c8100c0c04e0505501a04074140010342c40203007004001a500150100341e001480010309800394601001041c2d80f02d0001d140062070181014411070f004120401580001c580510074410a643c03041c03541d000050000d01000d45032400040704540d07810055032420b000d40038a6110740200000006680c0c16500b4040d40940380d03460348008880480f9803510306940e04140400004a00030000601d10b000744032035801440c0314031741e07401c5c5040308030406401184508020402d0750005246403c80c258424005c60380c00740c0b40d080f04011000100c140d00b070300941c1030089040c055107012103242c1c07400039100c00381c3c0c465040c60250341c100c10032950141c8004010840071710003040490342d000020403e03445249486410702d951703800881c410035141d401c10500c40d50341008202d140d00708200c1d040001e01c180c5080260302c03481d100c1c0c0341e612 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 340618875 1250 340617625 340617653
    0xf050102190327121d3007060f27080d0e1c020d05030c06010305010f0b180a02030c070503070b070f080f060f0d1406010503010b01030b01020c0f0a0314060702061003 73
    0x24491241c2c011400072420b031850303806412002d440c06109075000c0c1100d103180348003462944201b80e010150303020103003000520381e07058030b0040d19207141800328003100303aa0b43c102405101100d0400c0280c14031619560990b01c81c028003800008140c501d44804e005440d410828103c3c40c00b61418400249c0400c004480c40f110681c4c0507104d601d2500020b052180c118495003190402c5841505c00000c00c0100551150000d40d620b0a4104804000d0504011400c004081103032903256864002c101c14811650007540c0001318004814548146559018250713002030b4406c0d610709040000f00a41e0039000403100d20302c4042807521000034a0800441c15401002a00403070140400030000072160302c43d9031020f2050364109480c6a0000701000d22030b50360b041c09000300c5010703508201c1a407d280d40203001d944040d0384160081e050480748081405220548507400c00c0e4005020107002001c10198101c010481c203041c40a003465103001c1c00081d03d07280c4090310b9038014070b50f9000c0400100381c078030034040c03a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 340620125 1250 340618875 340618877
    0x4090b0c030a02160f05122d0d060308091507230a06020c060411030304141225090b0603040b0a050a1d0307020a08060601020a0f05010219032712 64
    0xa107a8407141001c0b4003d0190100c11052592014040001d00410703410009000f07100d0001c480e501492114018402d0245c1d0070480040750541d805240340020000184a107850031340251350501201c010b0000940b00142d00c256419980081c108119050652000c03001e20b0b840d01e52286040c0d600d13951090a20501000c00343d6032500303000c4da00784944d030038041d4070310103500000207649071020b42000603120300c415074003143c540a0055101030241008000c1d50219003840d131000c2c000007001802c1c08140e40b120010045a4000c1c0042904140e9400f804020284040001c00894501f0580b41070110390031400e049129130814010400011440e01c101d0383e00c82c0e032049012816444071200070010b010a0000007089403001c003d203145840000001d011914000c0380c01c00440c5940d200c1e581c0d1545070030703a10140103811038803c00021468002c045e200d124807074000185010030350740b100c401c5603401020210020b038449456130000d66070080030400804040901c40500030141d070b030b4103001100c440c030004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 340621375 1250 340620125 340620127
    0x6050a0b03090a0b16030b180a0b1201020a021e0703120309030e03070e0a0c030e0a080a091509061409180a060e15190303050f0304390504090b0c 64
    0x505505040c0444031150f40d04c502d041000341421840c4e00390303085001c82a04002840c0000f89041480d0454082c03810f5038041040700c0860b01c601e0000b101802080e80215003100040b03c030030644102c24801401e61070501c2d40503019109590300800d82c0b140300c004e17820030964018003060002c18000e02c107080380d440313903424001140d00c0c0c82c1c9000e03101f03003d00b0100241d02d0700507518001040305988640a2003822810070400c110904100e080d0115000c0700b00c01032855010482100001d03640400400320701d0b4450a103c8040c0b66550440c0c18400ca20803a40e00001e05680402c121180d00b00490300d441c8540d2134006070400a4480c08139000d24140341d411600523802c54042600f0324903a500041c050482e807200280c0c0b0b8a030400007007000280948125010b2101c12406e0724080b904000500d05a941c03541d40c251528012081403001600064020b0f15003154014004078401181c8580004122910040d0310701051813032801425100c1c141d01950086080003040c0c80080d41303140c5c8032640118001016 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 340622625 1250 340621375 340621381
    0x4050106112d03120103060c0512010504091704171912181509050f09010807060807020c040e1f060b0409020c03070516030b010504060b09061b070603020a020f0106050a0b03 76
    0x101120304002695503002d0b010010b100036440f020020b0075810f9074010b48080c03041508258084806105800028601100e880b00600c960b00c1c00e80c0004c000d00d8000c641542d002d0414030098220b5501070307841314004100c880c01041b0302140c10b0003038004106c00d100030180118081e46403009400b14601240d400c00c80d043c1c1c80c003280030340b0024200b400345c01319840c40c10340546044000303440e50016004a40c4208040004180d00e03182481d00517050b00d0160000d0500c0628009084e558040090405400d5000e0700c0c1401000b922903120340802c0449210003442d44440401408a0440c10740d0b101c0c05109091520500500225008403002c03108000d03001a0f41d81501842c0703c0c194000c04d03038014440d0280003820342d6040111020107060700d01950071112645d81c1d0f0030800c01240c480f4031801040fa07c00303010164844c64020080e0034884280f0b0b8070700c6101014510101e013841d4480d040640030039400310f8010000e40d810000c913220701117988000c005035400c15000680748035151103440c050782d01c00000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 340623875 1250 340622625 340622683
    0x6030c0e04050c0d0c050f0d080a020c031e21070611040303031401050f01140f0c03030103170304170702060909071e0c0b042409050102120a150302120102160507050405010611 77
    0x40c0701c00c1c098104200b40d030ad4000715240203440781000c81d8424440d100c0d248940510841d0702c080480d2001003003000380905206c21381030901c80c210194101d141600140300304008125240260104030541100040e521070451901404031904c521a1402c0300110300010301ca903843c1d50143c8601403800b402d140100d91443d5002c04101d20403c80211190000819402d5440c840003019506991254040039800e00c00b10300140d102d4041118090721102261604d50b501422910007041014000b42225281c030300c0f4900400c1007560113036901c0c0000744000300200200d00c00c144808045049601d0081e0a402c004e407550025030700081d0019040185c001d40481c0c040c0f04024011440c509030310018880c0700120b04003a0700039041400303071000c1c0502d8080010f405c1000341c4181c20b003502104145004a60854003407041805102a84117002c0d03600300107003e04910058409600c16101c0d0000700045800c22081c00103880c1c0c1a842181030041c0c4004401c00440045515044103540b80030041d0410f00001d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 340625125 1250 340623875 340623889
    0xe091e03070f0507140d080405060702130212010e0108120d0510030b16090e010b031f050a0f050310020c030a0e0301090b04060533010e0406030c0e04050c0d0c050f 72
    0x200050442e42022080000c01001084e00d00840ea440b00c00c400842e100c0c0303400d03c2000c4051110041c005d40d01080140024134000c000381054500191016800da48014032030703800c036840f4501c0711581c0c006610041041032031190849006d0400000038040c0c0702044c0c4086001c5000c0c5210ba8a42562070324000307038076250008405d0004607040340c0e000c1c8450602224622000c203804406000181071400041001c007103040440e8101c1d85510700c640c1ca181d981880c0d06011903541c0c5041c94280282050000300c95480203014000303042c14111540a1510344802c140c07411428017030b04031034240144120f040e0040d001c0b081d80c1544e105070070500ca4181c003000000c2c5c010701e051540100300700a21340078030043c051140d200c14891a240308080e00341e21a0b80d400340310000140341403220b050250390040d05c441d5205156003c0ca404004c2c00c0481c4568036903503188501481a04411040b02d002d1040006100b01000303040c16650b81914a4003a0001540b03130023880644501480e070180d11b800102000e607031a002c3e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 340626375 1250 340625125 340625137
    0x1203040f0606030311060601092105120307031a151b07030f030305060906010e0f060a020f011109010216050f0d02011b1104061e09050601020a060f09030305010e091e03 74
    0x100100290b0b6243d00e0050000300b8a4200c00b03007288121400201d07103502174088041903c040101039075040800c9451185954140c00741242c0c6402400c0d20f50502d0f41b00d29001e94001c850ba0b03140420180c031001004591614502d42c451b01c00e60003c2c211210131070030001111400251b159404541c013031625046032520b0010b5000609110740142400189030341a48414003a413802c55101c603c54a031100111b50013918400a558816000855920075281500050100242c2801274415203007a10000b1800c68002c0382c4110004280000d0a2141c0c2d03905002800c010450781c0403035034a0340d0401d0003140c07942c51a2031955019800c40311000065a01031059404030252048004d8040160392600d5801c0c51000701e501d80c0654140b8802107407006020341c1501440c24104c0781108046d2802c8001400742a0140c0020b05600500c142a4041400c0d402402c03030302d17440501c000c600c0c41d8851800504883c4e05a10041d21f9400402c1400003078800071a0703454814407060300c2c050948608900e407d082d0701c109 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 340627625 1250 340626375 340626383
    0x308090f030a05030403050c1f0801090f090c03050a0201030c050421140607091e05220605310c052d0d0e010b030102090a0314070902070311060601020f1203040f 71
    0x81400010400b001545401c12407090302c180840c413860301c0180b00152700503a0104041a411801444140c0b4994807296101465280200712007806071115129000383c0d0700242e81642200c4080c03419940c05024030760a2039550700e406490546001913070500d80c0e03c04074403141602c9041a040c07007840300c031610002000e105c9c0b10548029091003c0090107003143c922504003440c8040c0c0e0152035000c03040319540100d401c040c040c64624181d01001124180c0070410300d82450b0f07a103000c0826036841d04100784800ca11122803016842d40c079000c0403030051024102d890682807d1084441202d6848402e46240d10140248503100000424180c944c005540404500107140800c00041620541c5c0001455a012000030000711443c0c030309040c280e20647c41d0032604407070140c10410000300c110b0500c43c885400402510485038075055000d040e0791000d081134002407401d001c0c0c110078080501c0444e0300031a00340000c109458444503040e44801014086820400d4048002824080608140d4035610b0340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 340628875 1250 340627625 340627627
    0xc03040b040b0c010c0f020a0f080408011b08090d050904051009020f041404020708120a0f1d0f15070e03011b020102030405060a050c03040b191a10090308090f030a0503 74
    0xc815610b411a0000c9031000c2196081c40a4081403c0c00380e40c1d900d0740803409501801c41d41c0c1c0c141d241da00c110894a40201c4488108110025141000384540004403040e194007480d46a9400c6008240090150907040d4a8004008910b00c81c2e8100c03040328010f0380140c2d070101b101d03610054904a8106c0e913070f0101549900015400241d9121a0010410344101c0c040c1100c444100c0c206010803400b070803c0061010a04000c004128001050b0680d40b204643c100031076801c058005041c103a0300d081d40051800c00311070092074403488041c0b050014001440c2d0060006a1035014500d140720005001c0100b40b105043c10ba500c180c5080d0045414502d0440f041c100034080510b00030b000790f00c2210141c0c6c280c020b0101140702025940529801406400c01890442e1125202c02045100c040c08001254031110000c0704403003090300403608180d05845005001c010084140101d120b0345881035000c101c02c1c140180300040c00c46003500c54922050b9403100f585510a0b01180c038009000c10301070010b00c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 340630125 1250 340628875 340628879
    0x902090c03010810050108060408070215180907051204030323240d0515070c0f120e2d0a080703110a05010509030d03091b0801090b060307060c080c03040b04 69
    0x4a030900035412110001d080700c04028010148008030b800030300411103d50441001708010030810000340c144507000510200d44800082c90003079403a80701114540d80c0303d0480b050803840b4601010701d1640100c00781051441e0101e000300380e2031200c0700100010180f55076003501e000400f0b40d1880c031010689546403070710b01d1030402e07080c87c04002441d18803e4603141606036549240f070402c0e0642c60300e03440c0d010b00140a4446d01020400c007041c0b0050151041100c0c43c000e1001286a5400700301ea250b001d0b0001116018400000404044404004901601424400300c402c0b00d480411070003245600400b040b81900078000040481c03040e80d2001003948120080031042c0100c14800c82c0d0041001c65007201e4159840d401911107006001420307515401c4010b21000780340c003c1d04111002c501c01c10000c0b260704c00c0311802c6028400d46030014020f9079520003021080250801940740c01013002c90042c04d0107450881c0007841c030382c2c407036200401d4030801148403c2c00d18020000c0d07901070035203907074016150b82d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 340631375 1250 340630125 340630141
    0x4051b07050312090c030d0f0e09010902070510050c1204020d08030903030a06080706080f10030219030c0909050a1410090b1608040302030306100e03030301120c080c030304120204090209 82
    0x3d08102e0100b00c2c1d240c1980085004030000143c805541e52020f0007820310020f40c080241c0b45502c16840507006d01501c03600c00181503480c0503903c0c2c042c0c20801c0006072207003141c1c181145006200a0004400340c034010500604034014825611881c007190818246562984040b441174440d28400400f401c80100a00809510100296101d40d207080003c002c0315541d0304c502956002584174940210b1010750100308045941690191b00c400c0e100d02c00c03802a03580e58017103403900404003607007180c944140b0000e00030000d08e420034000501c11642c0030710040c58141c5a9944800307844500800201c5440c203102d501c01c0d4148210880000320303050070028000d140c04c0504a42c14112045841d208401c1c441c5d40e549800b0b1500f50340a6130309540194116980c100600050001d4807107843c05201c40c4410070081c41c1c2e0104021806410a40342d0010200c3c010300c1c00d00c2c0362884d25080104660000c42310142c55440000580702103a4564103509004441d50020400500c49204065045403142c0b0800c90b0342 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 340632625 1250 340631375 340631377
    0x9060904060e01080f060103111201090c17010c0c05031210030b010b030604051312110a0204020315010e10020a020103050a09140d0206160c0b18031201090c05040e0604051b070503 79
    0x1e500340c4c3d05030b0b52204980c04550f40c55507003d01000348481c04211b030904c090300b0070303d4428140507030305d5000048050b240c1e140c8036034480040d4800c00701c600c1c5a80d080c00142c5020b0081d2070161205040510190040b0343c0ca5640301e000e102d0a0070034261181c400210301281084035500115088801d014495031540b06221a9030310480b142070150742000081801040900d5259900d642c01840840c6507003c03040e000c40d02000500e40010491107a01401009030307440b0b10085009074460740b4001901d40d0000c0014110f0070032100c1043c400c410703461810b00407680100d0080f07410b950902c3d001802c0c3c0d0b190200100188181c08000d8090041e034030b0001c01c002d90001e5035180010440e000c49545944400340d42d081c1c11140780500e0b000a0b0320095250018040c86181a0818541000c01148030901007110b861034002e42d9001c10103c40b8440100602206882001d49141061030710b24603080c2000c01c800c200c0700000c2c02c840d00a030359400008554584800790640302c1c40c10280744650350a158240241e036 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 340633875 1250 340632625 340632629
    0x133090f061a1806070206030f0403021c02030c0111130306020d06090e010209090105040204050a0b0702041803090608061f05180402030a0606120209030d180e0c0705151b09060904060e01 82
    0x2040000010640f40e46004815180c80503401010340380741d590b0700300880942010227081103065210f00c1c07280c05001183c0e448107181100055008540300c407211046c1500b5140f41c400d120024610810180c080a440e140325141581d8010f000980d440c05000d040700020180c55001310380003850f0200051003501d06400414a500c0300301c1d00107400d0703601e1b4010402284100e10699074043d050b0082007181c4040b0101a204890004000003203400380010100c040710b1981000701c2c0003a4690405204e46a0800d50a541124054401c0d1070441100b06611100d030803800c0a1600b84600070940e880c55100030841400061009041951030781440f00400018004a005081c04500380e540003101c003c48034402d03582481c07401402004001e03c04041a91031070300c1d805101f00101600e00300441d010303103008000d41c0203c28611b40660b69144900704581094121365404041e00080c10901c0724418084194841c824015244ad80e5a80501400107003e44502d0b10300342d400c942401c0b40040c00550391042141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 340635125 1250 340633875 340633897
    0x90709080c010305160c0519080a080c030c0711190306020309100b03030d0c1206080a02102d021005090607030b0108070c060f02070203010207050133090f061a 70
    0x181c91500d4001502924070403500720381d015040800c145140c41c4940390802c01c05020f4000d449030b2940c000c03005200079800030800c0d2070b0800001940828654803d028942c40700c010307100c1606500b401420a010b43c86016030240150040b5200c0c580662b94501120351840c00b80007810000700c7e500c0c0f40c00c4019400440d0408124020582166507228203400382e8131300c00000401540c9400b01c1c03c09407500070245004140c0401c031140c1e4410140e00b01a2003040c000d07002c0c100c005c10350001c882c0704200741112450154001c20061040c19001c00010440504070304040a021010006a2407401c91034500d02174001078003141004148107410f031003c111135004c3c3c0700f555800c4c4040a217050056070703040c2080c0d601d000012002043c1801080b120342c0b1070000324008220252600340d4540000f030990f00030002c01e4501e0b0355900b40100c1c120708140c03801e207c41b81e404c02d850105000d04546c00304514285205045036551601e038901403665081d03204402424008884812121844400003d69008094056 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 340636375 1250 340635125 340635133
    0x402070212100f05010506120a0e010902030a060207050709020702090411120a0b0402090a021306030b030c09040336030605090a02090108030703080709050904080c1513020306010906050f1e09070908 87
    0x1b0646003001d4040b60309089a02c001900d242e1601034000000706a400304491855585d40e11510040c0d60922240f00380500402016032507a00300c1c108541032040750750000701c1d030a02c1000168010784900107529801604031014800c0030150401150b2040500f1100180b0b601502c1175100c1002298034025024034025250a01c0740d50f50a04850304911500041402c510407900f82009000c0c440e80280030b25100140c1900c1070442c0d003001281428006480440c00b080c681e11860089038a03108040050300c02c0039410030441003000303a00d1007a000d11400082c241944407000503000360000c020007008140e000e400d500d41d541e07445001c3e948075041080704500189801020800305841111001c0964000501d0f2903580d444a580d03d0110f076100304255400e900912117114030729045020700506c900340510700900054034a2040600f03121058102ea4482441c06d0800e120a0f107070710222240c0c190080da6000b402c01004142c003c01c2e0b402c4104050390000c6030604010055510141000841344000219 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 340637625 1250 340636375 340636379
    0x31e02040b040303090b09030a0f05030d111903060f09090303180609021810150c120504050f09091e0f0a050d09060f12020d0f0219080f150402070212100f0501 70
    0x2184147c80382000c129490b038000c2c812a00450090603a0703a660502c204101c80c90800f0300c0c14050291004e000d40a0a9083e011071310840882409075090560102841c00300f00540c201026191740012501641c0c072102d44e51280501018000d0740082d6010101c030f0b9a81450011038035154000c0d00078034008a000d2030b05900d031052410321011b103443c02090072101010081e41000940000e10324042034a00c1040050709580f8042101c041c00c250700c0c0f042940c0c0d016661810001404500005001e0990144003c00b0070001140004100c003000c4256529801c210703468036114452034102032540b20103060181c50012010410001000d11903c00c0d00d44414912590703034801234a803030b8410060030000c00e54440c4070541d6944c140d4001c24403058a81000140304081034039601c01c982141010cc2d9200c9644501041d23a41e40000400b5846414400c00411343e19142c810006510320040d040f0340100c2c2c012445400315910702418842c0313600b004c01110340000b8070810751000760907105c80e8071120528007000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 340638875 1250 340637625 340637639
    0x60f0e0103050a030c030c1509020f01050f1210170c0418050627150f0f0603190305070f030e100302040627030f08040e060405041101031e02040b04030309 68
    0x245040301e82001c054103001586840903642e19840c0c85084040008540c0c055000485540710129440703540c240019083d02584140300c000303202d1014950521000b030101d02040c80c13070f10b42146e030b2540c00c8036451003054a400c1000c2d1820a601c0e003012204044d5080c06c88004440090f0142801c0b808440030b0014036660048202101c0c80200003410343c0d045000024080e088203802101421411542c0041181c0e1148001e07003003c18a2080d035040b06d62150502c05002920032020f0b8010b0348008489840c3e08025000036500c410070b40c040707001800d51191303880c1454080c0c8245ca804681042100c0c041b0800ea15008048001c04104144145041d582100689100e0b00c01c1d1002d880860b112113501208051a500950b00c86e03015030343c520141c0c02c02c0400081d0b6100b03c3c590410f48690b0031261214101601e45803100c900908031406240707402c040001054030045445031100d400e0a00107002c002030034030921000a540591392050340000341c00102003000c01c000b003085038000d90b20103030000d0700c90031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 340640125 1250 340638875 340638899
    0x30d1110020403080904051005090a06141801030f060e030a261501030e01090f03051b01090302060c0f09120706110a0c09020c03190207090e0c0315060406090906060f 73
    0x134120100521103669035041503400f4a0700000da0007070140c401c031784e2840059601c0b0812103111700c00a888480070070060584041118850000312800702104000f241c1503804401e05200c050a203911560070181440440d03400410b0500a41d0140c2e0382d150804013002d003080240400e100404503d41c0307050340840010716410b50160b9810203040307012019080044000c0c00315180885115540d404e0303440005850850425030312440394590f292034900d00f44a01240e2207122010001e664148403d070800070f5404104a54080c5d140d0040a880701d1118406103542e0040d680c1498100e0015804d0383c082103c0000d040c011150185e482c0700c82c42c6810345034113440e01003404c0000d02c4081800010b2080e5070103134010f0001c2200142c102c03030914658000050724070350071a100c2c1c005030304501002d000b02061805107a10110000c0c00401e415882a8003284c0d0f81e0f4500c66660140d00c20400c0403800e180d460741c0156004080d200c6050007001c0e62801c1003070042c000c5105059118040800c0040c086550107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 340641375 1250 340640125 340640129
    0xf090c020d030b0111071d09070e073608060c180d17070809040501170a020d06150603061502060907120c050627030309100e06040302030d11100204 65
    0xd03000d026501c0c0036010a4001d000c1c82445541840040814050300920402c0444010072181c111a41c0d64403907a8651001101c010b04081c03500e410200c8280444002000380e240c001d6103030320304209030541007002e4203900300d9000244058a100740e6050070402c0319001002c0709455240d03080da00d03562200381c0050030600c940c056881c03a4983e9420a904180b0304142e040c2002d40c050031402508400075003180585501002c02212103641c0401e4a030894105072040c1400341680c640d5006ca03e80e0300c1070202d17a0792202094028890a103039100303542000450380160728444a90700f034405000e501c894014002e01203078028007404258003000080081c0c0300141e00c90090a050b1b01803c2030600f400d00c5e00c62400017420b015210021001030008064403410000c108009140428500c4c0110585030601d0035010500c856109038401e0240200c11303070744e8020345d800040160034400040540c0401041c1240610341c8040c0d850f000d0501e8406459400c00305601140c41000b00b42c3d807190380d50b000c2e840100d005078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 340642625 1250 340641375 340641377
    0x3041205130e09010603080c07061b0f0f0c080f2406010801030311010e06010f0510090e0105130e0102031e0f01080601090b0402160809040b011103120c070501060806010f090c 77
    0x181c0d004102040300c80d2000c982044140740003141103034407516204400d91005000c41416403014070108401540540c0e01303d0815003d42c055480c0b000c0702c1d141c24420300e4000a020700200c2060102c0c0c410003ca81c00d01c000248080f40a50b50055001000b0a84940c1e0a00c00f03002402c800081c54850416808106072044105031110481f40c0d0a544003101d42d00416200146659078170641107041140c200591070003007d0b042d200010a078185418070001010700070b040340620000e400144810780c0b9400c0c0c21415039a0948203c2017002000785050041d001c00b204548283d4030002c207001c400c15840c5541100010004070003485504c85071030000c0e51501c2482040c0c40d0b500085c0040c49100504e810030300242d08010805414042034958024440a0758034040b1f5051000054000c1c0c0e600f414001d0307040c01c03070090a126422075006510325442e0711648145582000d0044000f50700e030020070381902e021a8000000308036081c1c03100440360344c440007030183c400303641442c0400040081860240075018222 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 340643875 1250 340642625 340642657
    0xa0803030f0a1e052a03061f181211090f06040c0309020315040506060d0c0b07030504170607080604091101080c0915040509060402040303020a03120f0f0203041205 72
    0x103020061401001d03c4962401030100c0c0c0c200b50401044640a81400f5140b100c0c985111100d51084650881480b01a8040b440e041402040521382d80e501c10300321708004003d4031340d07107002640000310390051300c00e007046003a0500303c0404514140489400c1501078880d010703125501310a4810450403034021034525040d000c96100041e40c50600740c00003590a078541c100414100b0f196400203007070014000d80c241005145400308002c1c09401c000700c9400c550b054500716010003154807181094400b0340142d0001031382c001192810584074500700d60003049800c1440c0c280341840740c0860780b00d48041e070310000091075040105500e49488e05c03407000b8040d07000b440d2600e4420454010f40d201e560080041c030f103100c810300c88140d0a41381c008102c607043c800020034076076803030503c4108a581d40340074015502552041c802400080c0d0000744840c3c80681608144800820b0703a41074001400d9060005414203003813400000b8000c4258015500640c401c1c41600102c1c502417200f101d550103041c22180c07010302 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 340645125 1250 340643875 340643881
    0x30105030d050f07120804060f050118090c05061617030609160e060a170c0f0a08090304030501150603200301050f01020109060e0a02010f0207150e0102011d0c0a0803030f 75
    0x102a4005180c8460f00d03021650801a0b130b03445c1c01440c07040b0818410702040b0404100001c00c0824070416483d844401820002d550403e042e4200f440d20300326581c10400c1d078a407840410b0090310781c6020f00428004015a03564004207011450140941504079440800d904a0168044408095030f1080030060001c0809a56114000780c0c154402400a000d02580c044900400c0e01c4400082030030044a0302c40e09505411803102e01022300000b030040070006070030b000c040c403042c100c1800c580144c035031403611502a450b0040003604602c25903200400542c42c080e01709080c001c00450f4001115007645082204c5040440544684201034841601041080005003c40c0c581203030070103180b540602c000190f801c2d070f41e034a2004407030422900304000e92040c00e240c3e08641e40000e8000f880340035840038200251404440080d03e580c0b580d225030521040140d4940140d00c00d510441084400c2581a4503c9941181064031040000f01c014000c1541d050301007109003000080304d005468008215545079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 340646375 1250 340645125 340645127
    0x302011e0c061a090408031506041802091503430f030f021606060605070c0e070c05010912020f03070b010e04030918020c0c09010303080f04022205090c0105030105030d 74
    0x86a00009008104010107143c641e440e264a07842c4114403070042156a41440441c8a00c0390304a030251a106440400040c0b120b00c151050003000c143c2d6600c00580c1380e01c1c035078002450100400140d2001e18001204001075000c003034001400c01c0c07500c1841280102040050502c06124a0002d508041500041600d4030b505c00d485401c40e0f17031500c4c500007034503508041704101643d002c042800104510391601e181480068801c0714018030250500e00d207410070380e0b0f45081c00310754180300300200d102c8004000384402d40600740a402d5564490020001c121043c9001c0c40b90f544006907000042c4503085150010384000011240c00940088044019a20f804030324040340c9002082201009203426000078103035003110820364044200301c005602c440c402c080d110f180a0407400d6081c400d4007440010000b181e000b62100390070040b07a810300100760340c1d6400418050114600345900b180c00418022038100300540c0402c1c0a07864501c241d400602c2d844004503400e0200380a80d507403580000c002070100d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 340647482 1107 340646375 340646381
    0x13180209131a090a020a080108070515181c05190b0c03070e060a02010b12062205010615080f06040504050c01050c0c030708070302011e0c06 62
    0x1002044000103403074110214214048556454411008aa440420540c0300d2070191040c0300900f804a50140203500182074040014083e400225248034086689400c40d94020b00d4038020044030354005900c0e50212f03542916203002c60803480c0c002c0e00c030705c0d014084205035940042d00705181805c0072070900c0c1c00008000f2102c044d01811600142c26050102c0d0410469002952030303a481040c280d0b011241e2400b1590301030800700e0030b160305a41c15000b024401c14207459820703007510811603050b0b50b948140d860900112001150052074000061480c82c42d901820010032800d0f03031190380b02c0c0340d040010b00071130020703c0000c1000890300078003610b50b030003a00a840411452a164541a0310303080b207004000d042100000390500d070b4490412651034917800c020b003a10045030752420700e0b0f0780d070741a540701c12408504040c59440c040940c80341225080f04850300c5924004020355070300002 = true := by decide +kernel

theorem cover : BRFrame.Cov 340467625 340647482 := by
  have h0 := BRFrame.cov_init 340467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 340467625 ≤ n) (h2 : n < 340647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
