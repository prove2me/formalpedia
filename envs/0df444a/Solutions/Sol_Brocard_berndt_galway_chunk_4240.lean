-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4240
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:58:38.168123+00:00
-- url     : https://prove2.me/submissions/4b39fbb1-237d-494a-ab75-1f13bc64ec34

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 762410071 ≤ n < 762589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 762411321 1250 762410071 762410107
    0xa0605030c0a03020a0e090f01060b0903010c0e06040b0c011119021b01091802090406030615090603020d0b06031e0c01030c0206190f09051203040302120313030806060c0102 76
    0x140203005582885246003450000c002c142da4002e01080b14185c039104e24038100303c0c0c00810400c1c4500402241d131090140a000d00c9000b00080000319444c3c00c0030104050131155806180302c180226100090102d4072400700390790403941e03034a00d826110074062072401c0c05032500691007100725400003100c219042c800c07440e9a07030340301079a8200c0306103806182c0c54200720750659518602140c4680c40410850300040c1814182c0311541001504008121000c50290740140d001156002e40b149052100741900300010300050500d07842c00c2c490540b460300403c1c81e00694007409070894403600001409a01e00300400700c0440044880714045104050300641c48110084960780081c0c10b00d8000348d0b0f4036200084150050310700101415000030260b1060b4001c0c0341841c030480c40180c44800ca070340818000c0c09441402c09c02100310710343d6880c0502d0003e081944094510340852410700a111003034803407a08154070564581030002d03031901c50000040300c40c0104031032812950b0001900041403c000720b42 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 762412571 1250 762411321 762411329
    0x1203030c220f0b07020d05010e2a0f15070503030c0c071a0d0905071a040f0801020c031b0102040b0705031215060d090c0302060307020706110d0f030b0a08060a06 71
    0x20100951444000c9401e601c240d114244010300c1d8001c062100401076401803c00d684014201c407000031540e5191401d480c40d98210140703941011540d00f000a02e0111501041010038896550401503075000a2a00c841000000e000e500540710465045100c201100c502d6604802160340720f18000360940320700e43c40700014403507502500c4000030b054102d040038965000c2a8040003414280388481d8072005220082041e506480390036400170f5091945003d030341e40350810032190ba644c1c0b802c0115119a00c01c00f680310840f2a881081030402144010003542d030008403080e0f03184650310110904501a0049410418544100182503802c00c04004001d20314211840c40100d4a99156014480c08240c010040ea0304210101300340c000c2c1d04c1e0230740d1010301d42a11070360301c50400303d4590700441c0c101d400440d581c40140e40044401c0c0310168200d240c40e8101c103800001071110310303401c01004268840800340f074824191503129884403580c80d0002e00380075048400c100c43c03051034004030343c001810303503441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 762413821 1250 762412571 762412597
    0xf12010f1418070c05120412020405012301112a12070e0114040f021908090c03071a07060c020105070e0906030a02010c051906060f060c03020c06091203030c 69
    0x181250141c01c01e02d5041e0104000312080c0d0841c0e40d6102c02c2a01c3e0403a1242080f02c05000e441c6681d041450300f04050009010045d03642040926188140070840e0410781060305503c02c00b0b030f0760048040b0041034404442a003803801101e240040c60140f454064500c500081d0605000040c0c20140410111549441808c66024920010115902d61a600c0d180a101d140702d007040010700c141480309a80710403240c0094800a1551207003a02c038000c90300102d1041020454019030b80c1e511650041a0f030f904443c00101400307140c0c08640001c1d568448610030000c60510200c60201d08082c04000e4034800e681010081c4113100c040c1c5402802803804540c010003013401ea055240c9607041c8414000c2c03007654041c1c003c0a1074003807a0015a60080c0c00c98007254a8070461040c02d0088403ca0550224107100f000042030950400110451145094010008000d08008a0000f00f68006270840270b40006036034030303076996144c9004a800000200401c0d0381d41d200c00401d2045445035a03008045c1030034440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 762415071 1250 762413821 762413849
    0x5190c030209012f010203180d0809030a031a1002100606020f0304180207080d0603110d0803040303090809030703350a030519050903070203011401060c080f12010f 72
    0x1a100350220701454148500054401610149110313510070300e00411045014140064400520a01d00760380c01100d20302c50501450003071030321440c403c01c0140400c40140c140b005032840c5c100c500d15602e01440e0150400c1646501c0d695215450100e4446421400500541006041100040e50351181e031070350810030a03d003080000304030f0b201041c2c0c8000100f541e400365103864540040341c00030140080410030440e03401c00905002401050003040c1d055a21500444c40520f103052008400200720741d442e0082e071215240e40d0014020408a9901a526050006140525040c4003070140600060aa0948140580030003400703140c2c0050002205c5204089042c0c128145041840b075403c1c14551039141c0083c071541609a00a801c1141d10155102080d290f92000c1b03082c0800b50b074010303070380d00486820002d108420341c00c00b3300560035070165008004040d949040002409a650000080d01015001c03030ba04250109aa08171410f42c20002061100c650715200030705000d440c14410300c5a141562 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 762416321 1250 762415071 762415091
    0x70c03061b031b110f1608160509010e18030d020c0610050306040818040615120b0f060a030e011409061003150c030f0906150b0c0606040905100519 65
    0x24041d4902e06a10040c141d40400c8881d80280c0359060320204013405801011580410f1035820030500241104086240071914a06014141010040143c4001c0c01c404c10109010584800303818034112182d581d02e185a42d43d4511000342441e81d1981c500100d40400600f201300c0070880d4001c2c105419002d0b05541003070300c585c0c0451444800b00c0c840d15400d6002040044c3c007294041c40a41000c01d1107180d04038010342100005403c8a1058111102d010b0b902e4241106d8182d02c501c02c90302c420800c0000b003101c0820440002c10f950511034030b8a21139100081d21101e05442500700000400090b80240b1140c00c440c656007164000881e40403816101d10f000260140d14010361030740c02c8a80000c43daa880700d00441401003c1c224810305103042c151106400000442d80d4400c920a05000d00350005580310100507491140009912403510500c0070701c0380ba5005807000c502150080402c407400a002001032070110300f4118244840509107141c6000c004220340b01542101226408000400400d212 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 762417571 1250 762416321 762416327
    0xb0d0c020616050a0c0503030708011a07030c060c0311040e01031106070b010e070908101d010c05040509060409080c0606010212210603030d0e160510051e070c03061b 73
    0xc860003428120042c03042010039000f00020240340706540b03490b0703190b0746450b290503140d0b0340103a84020000314240010002000305078400003c0d11181103589240100382d49004040380460100a06640d03074481a00d02c001c0c0c040e50100031141d0007400002e481d16658580b95103804024801614001800050051146421000c07602583d074001d031550a01c0e400d20f0109861800c005081c081440ba00440205001408000c0c00d901e600040d40041034004030000181401c007141c070b087c01c0c4513078103100b041d1800c103802c00182d6003600c81c20f40320489540d84410015010b050f80c00c4000c0d204000014502d61181c001080c420f120350002c2e022a1499072450741c14290500c5185500c4002200c02c17441401700760300003c4185e811040c018101e90418404003a00710885e401c0ea48000c6c1d080d4407010f00070300440410241c00b40103050444120013900c840800140c00d600c00d068194544038502c41e8005503d401e40420742e4485c0ba00084640b840d15140d16050004058550307240c003002286041c15181588 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 762418821 1250 762417571 762417583
    0x90708092104140a0b04031e080c0a0c140d0311100212010e150604060507050a150e1e071a040b03150405060d03121a090f010e0f0108030a050918010b0d0c02 69
    0x20201000d02d113482c1c91a2208e80764900c1c800e000319494200240300c0740100300d0030700140080c501400c000c2c0c0750040031850000d103402c5459002006211036000200a96611503401d0f01c40710b90182040c0698850f40c0714060700303065241424041140c40820f0442c9040344501c0120b06030352441032204456101d40310b01030703250200303055030710b40c401030030001405010700c20b0011301420352182084911602c015500c0070000405184940c56607680c4072810941804100407041c01c1303606603003601407101d800000d0a41c072550307140105805007000384031007000d01c0d8002c2308440041203040a490384078148400784803c0000c00d19042481380d400e04000c01c01c1443c02040108215074180c894002c0e00702100e00840c0500002c44881c0040c04214a0305052601c0380c0b190640314400c0c54510079031543c101150905c8101004d0000442140c030304005000b00c82c00001113610350b204070f0030090f48500503040040c0401d152420441154030000000084001d0241c02410314500445c40c140300000d100e0794100d903903003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 762420071 1250 762418821 762418829
    0x103020616030c060e1b0d050601060c020102120706020306011116180605040207060e150103051f2304060605010c03020712050a0c06051801030902090708092104140a 73
    0xc820001403244100308044010118031078100202420400d071100700407585810342e81e20080c0c206d5003501403070f882020304464048030f0840f284c0000105c1522910781d02c2d0414010203040c0f14610401c1b0b801c0d60b000304196003a2080d818115540c903a01480c09401070341054800d903010500b034040580080c0004180301101d0b0541203605951245880401c804c40b980980718904016558840461541c4460004083c0140149800b03e411065046400d00e420100b08117440308440d14070042c1b000420104070039240d031100700582d2441c0715100c035a80c1d0003024450701d40b100d07004041994582411a2903d03403442a8042c540400c07086565100569214a001e80000c0040e00000001e2000320010100d1400c0140901c00310341031002c49030340b6033140d0b0314107800003000308074040740b140802201244ea5041100c402e103800c0c802842180e0104081c00700180903801800003646c00601240741c20012040401074104808140090740784500d0030585c0705009418405500d44454061814402100c10803a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 762421321 1250 762420071 762420079
    0x8010305030d1e0e06090d090305060a0e010b04021b07090218041d0a0b040c0f0b0304030807111209130e0a14190303020405040506042a0306080a0c06090905010302 72
    0x1c00070b601e030b500042402480814021061200f110020140c0b0b11900c3d20041390344c0000c24090a01549441c0f07070003c0d01c08808100607003d0000e0000070741c041801ea820034120392003c1121041440741d43e0250201c0c0071040d8201e4400702ea000d40c2e42d40207000410710300c01c144041e03540c01c3d0f4480c94a10281e1107508030654a82d00304c1e41c0c52280a040a6015008420340160011030240d43c170271400c0e00386075410400b03440d00307109001400b0900603080041401807100d00030348040c6a01c0c1001d11400f41c04000c1000d030502c003100b400104018007c1c1c14984003600f9100545108840454801210b600005280d5000321800101100d00080c00e11503804c020096000408407189180e4074801d151180c1c0f440104c0f1402384c0000b130030303c00c5609018094024030a440140c3ca580c2000d0602003180d40007091240318604115406100c010b442d82055142c0405ca07403883e03010111001c0036000f4101c1548051031a1290081003c00d000442d4100310641700f00c0c1d568211656514654801034460a000103948 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 762422571 1250 762421321 762421327
    0x406021f02040e040836121203040c05100c020a060311070212010507023a02070801020f0a0e041404140a0f0f0201020c0a0807231917030a0c060b0103021c0e010c0801030503 76
    0x3541f90498425101010a4040f18405070003002070070381c107030400d4404031030146900205215514100c0c502a10340ca00a25103400c40200e40e0300003400d081d0340c5118071811702d0360f583e40382120100c6030802c03540d586401400340e14010b0034060b00c05000741303412101c03403005020300b003070f0315182c8034020414400102540400f41d14801d580c000c141800610040301100f90302c45c0340000034842200780080c1ca50403580814181c0c46012250003d007014010880c4503200b41d10b07005401c1c04001c4640042500203401003c82c60340744000c20b142614050800c4400703803041d50148a5071003001862010a440709200f0381c04c0c0c2d503038490003009000510165020362001a000701d2030a00040c484081c4001c010301d181c01c10001c0100e0401c003c503449441c54054441202151407040c0100105e6000c00305000c41214021860002c0c420402854002c080f071000304010344030044054940e20076019203461481400d20400b4040840f51402c004159121080d110b0b0750038008184801e0780140c1d5050304881c0c1003c040c2d4031f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 762423821 1250 762422571 762422677
    0x1416120210020f0f1b10060e0609090d0c1103102009010801090b0105040504060806072d0507060e01050c13211b0e01080a0312020406021f02040e0408 66
    0x104607008405071442807030080020a010b018100a481b101d030500802c00505a41028245420a50003c055034045c450041c240f001d01c07580000c00c0140d03803400d4a00151004528648820350200c01005242d040c841c007100ca40c203255060740652a0040b070080c081c040d8000e074180142c502d0140340107507808200c0c0c1100403c940102074001c03d400442c145000303441d0076140c00c0007030102c841075000005a07900040030405d4060304011000760300e45683c40c40c500109009a408001030044410701c504000740850001d0030810301350000960401520000d21a501d4011480c48180d04aa8918140110301140003d440d504407029007440f00c0d00d12408074040c5103640c50714110100554800d401200348443c000a9000034041c0700c9001c2c04000001e00300850303880c280240804030a0040804062042101b000401c1c1c00103034030621403402d02c0200c1d442c901c13001120707002800b5652181c041450098200420080710400a115200100c054a0183c8403004021002e150320341030a41c91121075610445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 762425071 1250 762423821 762423847
    0x90503060a0c09051905150d020708040603290607060f050a09021810051c060c051c0b1c03140406090f080105040309030618020d08090907050c0d1416120210020f 71
    0x103401f01101004052a0000a0180c001260300404043e03a901c1c0000c0341c240b0400c0c4d4580207403030b2040166081085110114004c804404091218141c41840c1c00103070131003041803a0304440040003940b10708024920300003500d40d014012121b0200e20404000045601c44001040500c2c0900310f0080b1100e85241858180315000221003c0c80b10300c1c0384941240000079075140a000ea51025030742d556501e8003176507007034009103002441303401c1a9603041803a6407240780c554580f00c841d080c4d0910504001586541015694081e060001e080541800a4041042c40d0801006400c032440c0c1c501114440d0390703880c002422502c0076a0300130000350700648104042142d81e040251200c4240381c2c180300c4440c0e1540001c0038000c0d00c6900b101c400d4000b06001c225031034510481540b02100b030911610300000d0219036030300c0c1c806803003040c414051006000c080c4d180c510020b43c1c000490f59503d030100b1603941c0c180002c14901080c0c00500501c00c101c0604c054102a000742da80001d0114200b07414110401200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 762426321 1250 762425071 762425089
    0x10b09010507030309080310050f0406031115070209090d0801061b020f1f0c140703050d110c220614030a110409020d0f050d050a17040201090503060a0c09051905 71
    0x5404061711130800e000480c02090040d405150308005641001c0d01d41000e0000780741a00a5140c4290b2030101c081002c582030561320010400f084410010390707240f44042c1d5406014100c4080e401c49180b10800c41e40040002d1101010051600c1e5150180c0ea5204211198480c40400341d01c400b0810b0603400050510360541c42c01628014803400c44900b500a04400392006010200c5c00030f42c40c00c00c01e10500000c0c05c0c10410258000d0701a1034602d0a617103d840d41d44640501e54420001c50104003115a1001e104028240c00001c11280720300f10350104141c1c070700007041c4191650038608000051010f80300d00a880300b140014014200024458442007a6842595071507500551112402801669071080309490b1b64403c030303011307440b20502e0305000745080340103024001402001c01104002d00c0d006020300d500c5080c1d19008403800d0b5107900c012902008142c0c462601840b4000078010b401c24076401075034501070b80355103c182081d030710020001c1e4049407488807892411880c4081c00942003d501d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 762427571 1250 762426321 762426323
    0x9100b0706090b3103050906032a0a020606010207030209010b0a112b17060409060b03010510080d02060f010e1f0b070201031a22090f0c1409010b09010507 68
    0x40082d41c807039203840344014401e08441905000ca0000c000d0807240203000481040001c03103091203a00220b00340d81c058042c0c0700d0704014610504022001a08512500c60840c0048480c281d410441051910301550b543d002800c080c0050b0041b200020080c0d440042d00004980d00100600f42503480e10302180da581c0e00003213034541041303013280c41144511001c2100986030f40f035010606812181c10010590402d0b100d02020040000b2140c8000740c071500701103840c0e084242100c00090385695881c080005102154407207402d07500300010840c0c06643e050302c5008480d5140180e4111919800c02240c84020071501081ca544900c1c2c0140600c43d113a0650b02c0d440700e8030a0b0289000d95524511404071803260340448901c1a00040e52802c5503414024050600140300d050320781550f1a40029115003c507210290011848107006842220f032500414031a5801006920089007641003102e881512802041c40316100c1d01e070340381c03001e08000010703504a5090101c0541020f03141c0e40115015404100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 762428821 1250 762427571 762427583
    0x201030e0d0c0b0711060916170c040c0504030f030c050706091802070302010b03070e1b09030a0605040206130b0d0515010512040510140604060b0a090303180e0108070603050609100b07 81
    0x44001500d017000c2001c01d0040000c1310042254298858283d41002c400342c003d50314512940c02c2140780d0000003d481c0b42c0458080350041040351503002c003100d65000350391024140f600505103060a16811084000b041400394094400d41501c0342800e841c603862610800d407031141c48511005c02c0465560141107900c1c803030701c00858140d03000700c00030b454a0840e0f0482c45003a24102d06008050303248c0e000450300c918a45400074208401e8000080d02c4140d204000350a054880000404560703800d000ca84402e9064501c0008164503248044925044007030704140061514002c50183c4484130498142c10ba0144c0d109032506511595405101c2c3c1c0c0034000300c0d200c1c46600c0c642002041c850259182261002c4826081403a0560401c420385105920441200340100185c04042e640003610b10b0681f9018105450a000090004407a4800b43d9124540002c00a0004a00340c0c1c1f01081480480b00302d0340d818040c0d520760398200a01c00c607056810302000030380d0b00000c214982c101000352902d180544 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 762430071 1250 762428821 762428837
    0x180603050106150201060501090e131104020414040509012c010e030d0209041407090b0a090506360d0b280e12130e09030409180201030e0d0c0b07 64
    0x103903460303007516410f4000b120074141d42c080803a00694244a540d00904091900d503d00500c0e0450140013400c028124406950f00314228034144400d03220b0920000c48054011035549554103130926080c100103880600c1141840003203015038505014411800021580303501c943c00d01a000c0d078800c2149400700e1a602d540b00e4906521000e400d00c0940502200b0302d1015a0300c50015080001f00e40d049840b212150344004180003405512900c800c05440304a8055642c50f04001d40644403000350b80e00c500e5020070009481c80740810107940c1d62500300720347c2c074a6590f41401006000d90080c803a07010980c018a2000121011500051100b80c2050b4090b5800350385290002c00002c1d00e4002c0b0514001e1203072551154032000c3e600b003211402103404840802d00f0075110b02c441030300b00c000c0c900c2031401d03a4080b2804280403140520841d030003007280c0c5804200100100545807001c6076a20010390104c1d1070f211843c00400c10119403542e01660382c0e03492541e1200c07181d8a50305550030207420101000408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 762431321 1250 762430071 762430073
    0xc0a0216030b0105040506030d080601031a0919050c1611010306030b1003230a0b1b0703030e0c041e050a0209060d050a180201020613030212030c0703030b011404180603 74
    0x10003030200910301540d2280035035030408061000380c03039014061034080d074170000d0006801c41d4402001d0790800c10900c0e003c41d020035080c08991101a0303200390700e5400403000c81407014a0010032010a03a114000300107200b15562000c5180e1103009a0b10340c3d00c0e911200c522258000b50a40032342c3c8130444414100015441e031251281d6034203001c2101c080c6482c02d19844280709000b500b111032b0300a4100250002ea400c44940790460b100c0c602070600802036800324000c140ca05c60f07040c800101c01740c510403103291175000ca410b0003400f90600b0120305c0d085000e2020b0211103030410307001d88801a81c1c5601040c01107103500600c01e0060030020708440c01c480e400d1000e5400e996500004044004400801248034104a1036134021079158207890003030241c6d903050210041c3d0b0042084d80d4401d807000f10003034090f003441c1402d2b401d10700b5069030030f85401000010800c0d0000c991014002c4640290b9040040540100040d11604102220b00044540521040100603403804454524000c01c10001c00ca040d80e03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 762432571 1250 762431321 762431353
    0x5161202040e0403050d150b0d0e0705030d02100b03062403010e0d170c09100507050c041506080f01031104020c010e0a0501091a040b07030b06090d030e04150e0c0a02 73
    0x750f5044000440026a4559901e00d500402d07024090751082c0050300c5c0c0c41c114801030103104445100c0c0f0816106c04540220b008244012801000b000d015580c2458502c24020744580340440c9000c0510301d084091001c50600080f030a2144800c02202405044402c08010b4454090440302c0d51645d03c41032404041c3c0000d1001400041140e29034505203031800080d0152910b0040405c00a5001800050000e55428204541c1c625590808940d41d2010b414000d0402d81e40004d4142c006c3d0804031640d0746100141d000381d0444000342d480c031441d512364042859200340288009030049000c02d240721070b2032400350b00500c2c11400c0e0300c0000413034101c0741c00202d040c50311420090321187d541d8000c010501094601d5203203259005445454546082da43c0c034882580041c00c14420907036a14050341c2c05803541811145900c00003890250000c4d0545401417802e2110141079028600780324414143c400d5000075076095a414881501707043d650703a1040c0803c0c1c0c01040d1440c08500c44d01d9a030b0108062 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 762433821 1250 762432571 762432599
    0x80603060a1112280203090118081912050103050615091e071106010806070f0f02101109030a1214040812090301061e031205041202010c1104110705060a0516120204 72
    0x140303044c050703180d02e02042d04608480038480c1650170749000c072000c000043d0301481294607450409440780e292000810086405100303990458042a1804001100340800011030600c076040a8680c00301102d0082e05014440d441030340c00360a141407508125040104504085034400c81c43d00d01010001c00c0b5054980c500f180a03404560281c00c0401445803c546c4122942c2451985044c504884280b20030005d5440400900341c101450703607400303646108409002200c0920f5001000c4564140c0710342014008034100c200c0309000720300150000d00464000009803404c865441c0c025082e0506494100042a4400d140845e1305550390003000c43c5c0510149140503280c0407502c0002c2c5290304500d00059a601104142818484148070030801202e00c051240e0b200c0b942860000e401d401586004210740c4240040164001d003030440d4015503106550203000403500910403100e544c2c0720088000111401510880c00704041c404499000a0140d41d00140c1007200d11b50051810390b0302d16078000810 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 762435071 1250 762433821 762433891
    0x61c02090301110c010606021507051c0603030503070206180d1101090210110f0a0b010528090c1806020d051b160915050907030c09080706080603060a1112 68
    0x4100031030000400381c424800c14002d0941c5000038a03202780f11051038107a130070008040300c040040c00100c142d13028040204440001200010a200341d80d143d01e000340441c1c1044616100612604001615650302500c100c00404001c001400c40314514520842c0c1805019103030078155902c503100c0d034005864403c207203051250650b40741e4045403510440070b41091510720f42c1a4155004403040d20100c5d22040302c85044840840720500e0b490044c282c95110030000002e144c0f4181c10403000064400c0c00c0e0381080f080c010140d990418145021a401c0881d40c12502030000107900c00070a030070145000d10000e1554408240c80703ca40906110340f42c0b8075042c0700c9100c0c40010b8001c0700e81004090254062102010f0100001c050658186408039104c5e0751b00401440400d07440304201108240034000100c00303000082c0aa804044d00d0319000f600403074007560514081c2c464a0001401060b20340314481c10036801010040c0741035415100c5811f0508094640840c4581c1041440e460b800c001030110446 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 762436321 1250 762435071 762435101
    0x151e0b070b070f02422404020f04150c152c21040812030907050619140412030e0406120c05040203091207060e1b061c02090301 56
    0x1494510402018070303070340308014420b56009480040118a5001e0b03003042002d822035214800117043c441513041c8640c85d19a522400004000f03001520301300d8400f0ba1015141ca0369400e480001c280d00340300491042c81e100f45029102840188030341d98890980303108090340c80c40c0440e0400001e403221030700c0c3d00d081f10420034090755038410543d003640403842c2400c001003170f89841c0b034a0401c102034058881c00f0140710781d01c00780623854550f810581c0c0078081e1000751441c0c034102c54003003145c00d000840540c800c2c0c404c50103604c0341d190001281d240c210200c0b1410010310f480d660a82c00442c2095503456aa0b0b031608852010601010554001c103820f10f604690082d0f82d1001901d2900342400100c82d041d4002c014500d4080c048c03032011500c040041e104440041ea401650303a80c40744805810503401061240000c640050298244401c503080700381070f44040c0041c0d411407500c1d4507184640026480a00e50404800d00c0240c0480c11404100340101d501902c0241c03400034000c000a0844c1c0d0810150098 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 762437571 1250 762436321 762436343
    0xf0604080f0105130f02090702010e010207030806180405300a0f0905270a0e0d05130b091f09050913060f181e0b0f04050d03151e0b07 59
    0x1041c20074010300b90000203950122558000680301c2c0194200c8041d4080d000e031550070b02150445200f58042c2181e0758001000315102ea080745401082c0500c20b076a410300c00c1c200c4885000000d00c421031410700031540000288481403040141d0320300c10980d032401580c10324958410010000241008110001042e0f603800789400000c032000d485090b07160402d40c0a0b26004004441c0f001511003010941d03107800c183c1a4913075403010040c5010b8805040510303014040d01c0b11b40c18080e80c10101811003410903003180c220194945442c0d00303083c0035000c0156408402400603031060036031045200c1d601c500529102c8502c0742c9680c04520805020385680041d06c0a100100b01444420320940440b000c02450a01c842c0f42c0c00c204500f8810700c10280503204040d00c0482c1910070034109048891282d0001900c2c200789803003406460105c4003142c06035400d014050f1246070041c803134480d01180c00d100c2c140403640349041060400c030005c509100c4100340e64011101043e0410aa0b01604010340b040f151845 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 762438821 1250 762437571 762437593
    0x80f030a1d0a030503010612020d0c030b0913050c0904030519020615030609060c03090a210807020f0601170102040f090b42120a0b040c1803110f060408 67
    0xc08500040c1c0844402d41051800c2400070380c0c4801100c1c1141e03190301e851030302c081d40003820100074422140541409403905131600b00681c0c043d0419180858203c41041896030382290404014a44000013089a0001c070b600850300d2074914041a001800b03450081d00300690740b003c1c107030342000344c0b1040b03c09607014030704100e480000701502d5500c4c61410b6000e030038a400c0890302d2070f030f8505002c0c0c15012900c1d400300000300b90250421403014909d0b0015903030708007074018aaa284200c5c0c181d8600b84001816100081d080500008030050042d40010003840c641c1e207040892080e044550f02441d407a55001c200010745000c00740d0412015081880001914801c054204118600d4206010141e00581c0c4075800c803203900d030f032054948200c22581c00408a04420a41d460b2441200141d8021455034400c2c8002c00d0b44541c402104060192020004240601800c0c0d0303503032452642c40f0401c910011070601c0020303103030080d01d50000d00240c000e030409401140002d8240c0c110b504510015801800c200d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 762440071 1250 762438821 762438851
    0xc06111b0d030c050d09050a150204062c010c2102070e1e130c03120305040209090c0f040f15030f11040c0504050d02010e0405190506031b0d080f030a 66
    0x180740c8030480c2c02c0403c05940092806000d6010302e054401c0e49035903c0420788103010083c841c0e00c500580c899000c41008440c016036a00030340142c020341000030518104981110004414122011841d600040d07200d1000001101c00c500c044c9030440f085d00194401540c2501c441c90b004d81c00003030a4000e80740d0789081c1201c14485d1034000309600d65085081c41035504e4840420022a00f00071008003032940d0900a0501c040340d0505940010112841c08100e561940c0e4141d01c1b09006a200f25000903103611a24605651015030300c280507802160888185d00e180b8160348100115001400003041e80c1e0543c401c0383c00c20300c0c8180d100741c503521490000030040096070010307510b02c0036003254100418480f00382e005240e4056805058051011b10144405581c028080e4602d202001031040c402c0e4540701807441041c038400000740107401e080201007112841c1c0880c81e0601000178080d41710b80d0542440400a88110420060700c2003038081001c81050801400258400c0b01c0e42000440e05c031424500c50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 762441321 1250 762440071 762440083
    0x5010f0e0609040f02190e010f060f090506270d0f03022503150b1003060f06032f040b120601080f0f04200a080105150d0c060c06111b 59
    0x7600c111500c20411000450b24401e00c006540c0507511400c100c0f018556680c04020282c01903c0c1c0141c03084000182501100c0070b8405440304c5030758555000309103070700540d01180c00740a075691100d8180320b82490305456200301c100880041e00d480c3e0f5000c018001140c0c81c1420b0500503121108201010003d041d01002039a80000092071040c100307241c0e542c41525501400e00004242152400d130310051808150441000240c00601c400c002c040034141c090005c10440c0311307103078500e031000d400040d405000c0e2080a80c0392a1001c8011951200d00084183c2d11564480380c80200405200208110001d140500130009440301c52950034100040003406401c00201503000244501080120701a032641f401034110382c0c441410440012504c4569003005001011160400608040051903480542100b4000c00c101031900f14809224800c1c00f038001d040ca400984046000f0310204070040c8175070031066019000e140b0009680c0c00301202c80c41d03207138810141f4824007100c8155005104070b080c403034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 762442571 1250 762441321 762441331
    0xc170f1201030515062b030c3212030c0706110a0503190524030c13050406180222020409061205010b01030c09060e060d0204080303090705011409040216020405010f0e 73
    0x40c5001c4400003603141c11b0418001c0c0e055802e010906945004250184100f05800ca41c010078400c4696810b042001d404400701e9600c0407140d40d035401d40c2081d8440410489181c0684021242c510340e00c4d040340c038034103074041c01c000c403505559400d02c084250380f00c2d00500b00d40074040d503034540d0f079042100a080c40c0402075803481a0303003840d0109002e000c284241c000100001e441141c10212040b820000b42031803d44000250000480c60144400741c40d20b03803009129902c54142041404510381003020100c04c03004000b0742001150300041c84285d610964000007075010b850252178a9110841380089e9615540f00007030500941c01198100282030107202c840784001c0c81d0030486442d219400402894007440303141c060007000060b8407000c2c0c40300403c643c040000742205542e25507850508642c0c941c030840b0907a1072070203004408640b5610882a0700520040c3c44606408e0008030310410000398040d101e02c81400e54801c24100041c5c540e0b0103900d00030700c1c080c01d40e0b01280d4a000310442403032100400e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 762443821 1250 762442571 762442579
    0x80706111b0c010c030c1406090a0606080a02010c02151603031e1a0f0109030516170304050117071107150e1f03020901021f1b0c170f120103051506 65
    0x7429100b180da110480c46400d035014584407a40082c1401d0440803519400071003481e6000315000c120301c0120005005000c18031452081000b1641ea015042d1151f64042d0000c0c00034551100c00e801500c0e100203080b04180d00d6030801490569030103480700b400302c5503860480c042901c2c2e58215200f00100300b60410218850807061142c05480f200781d0680e00c1c9580c0b0030f940b01d10750000da10840340c2d2040c40501c001c1d59125003207801d400b45202803c2101d640c58803c8195045001e001c41d40204008802c0e10210388041e1592128008038110a500752907004041c0d8040065802ca80301e14a8003c200700c00c0182919680ba403040007041c030b0001c00c0c0011405225009541c1021082c90700b50601c90050a43c526525005844a0700d20340100e0170450145485403003401024015400314441c0da020042e455104550410f511480240c07d427208c40d4002c4000d4a400809101c51003a105580020442c00c002050144c1c5084a070a1108101103403c1c0c00a8403940c5c00781d6060320f202c010a00405820a400700e07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 762445071 1250 762443821 762443833
    0x105070f0f110703080a0309050109060b0a2106020313020603040c0801051815060312180a050427080f0a0801051003060e190b060703080a0b0a05031504080706111b 72
    0xc1d0320fa078a041510006010740b2000815011192103503200300c1c80180e0081c0240300c215490b0500b000038000388075000380308842410001448800c000d1800415071181000704040c1d001740e4840c50001d420052402078840310010340080103a484400440c841d5100740140e550640c1810f10560031250005c0040070040c2803000f024510305000540140700302d00c035a401091079507400f80407904000c0404480c4811030b40c041502002c40d4041c101500c031140d016184c7c00c022956902c01c1000b41d49401400003400c130601890002c0303003101000000449401035103141e24000c90040d8403038642e03022000440000b90a80014096031404a00e9004602031901d01480000e0902e501383c4440000900010b00c4800e5115100c0070480264208011520004010315101c0d0003505000e0030104003100c640c91454504401000d880c82c2c00030000c0d06442d0301278014641d014000e03146460b9484041c1c07094034052814400c0e04001000c2c3d00071480035040741c0040688410b4042c3e401000301c40c0035100340c00c00750081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 762446321 1250 762445071 762445097
    0x906090a02090c0405030703080a1b2001021221010807051f020c0409030908060f091b01050d0c02010605031c02031806090409050c12030f070809030f0105070f0f 71
    0x540100c925404403001c418070340b10010742c0305403480340e40d002ca501400b860320004140b20026003e042d125655456061140307449182e41d41c030b03c1107c090004d12011080c111a10000b45d140c007808002d00d8180102e4254030311044403003040e6040f1440711074060424003e0349821244243c1b10500500c8400018024541442c002030f2030809908075800d81a40d10504400c0341500c2009020540403000d0010061004123090040401002c0d00030100b4601c03a41d0045031400e1315104545101c0d040b10809003240360702c00c109800c5030070300940b1264100402407058203103000042c452078030394440580001901c03c2c580814107080005440108100c08000c104220007140c001c411a40001d000d8020440c040c0303c030340300140482c001c0b5070905401a20f0509440c6c100440040d9400e00365508503200d4140101c0307a4602c1d5640e01c10494400302142c1b040c030011000030f1240015040c4288001c09517101c10607150210707070131664211242e000280c040400a50f4144d002034032104800100d02e001000e250704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 762447571 1250 762446321 762446323
    0x120408030910291c050109172b0207060e1005060d0b1f08010f050f0901020403020f2b2901050d23030d0603060609090b040b04060209060f030f090609 66
    0x681c642600c0701008081d0f10590980d200c00c0d032103803142e0904981e800c0c1900c0310b0904500a09814808440e0b00c24016256041e40f40b02c82c1c2610369904100311101102141d0704100401c03045c15000e030400300c54080c40018002080c03030045000c03c20042e4010140c0e940000680d10a41d04090300d000d009428011079140401c21078207055610000d0303242d2031400d60761009180b4082d1061940008015444c00941d241100c2d1160406801841c02c100e40b2501612644282230803446181b10095200c000945144030504044404109036103c6504410720f22940103a103030b0140704540021900b01e031072040d081120300384a600001c1d007841c48144a62140d0b04140114000902024028101c0e84c240104000381d440160003050b42e54801c84140c2c3d403100e100709000800340034180412030304903092041c04502e5142520038000c003241c1014150103252540e490b61035101c0704c081e0043c0e40c00c1c1e03000c000300c0b0481d4941c100285612101990315982e84c0ca400c44000e019100080d140011a40049041c0200c400c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 762448821 1250 762447571 762447611
    0x8011a1005180a0308030403030e0d09080a06050a060b0a08100605040b090402092d01170403091701060b0307051c290d020d121805011211120408030910 67
    0x41802809026442d41c0b0018281e4640340d400107200703030300001c1080105a81034201080d03810300f030402c466810341240015944031849000714401079010700002c40c08106203822250300030118960006102e40c0321a1000401d501c4981c1c03050110701d0160620160040c00c1001c0001843c103840c1440c2054141a1041c50f1841100381c520b114940105482c80726598040e01e1081503102c0560101004040d890080c0701080c044281901140340b07000d00006c034240c0800058811645076035105102c03407d2017100c80d6603810580c0366121302e40da500000b15142e04088020340c003d04050b151592105054560f04c0c090f0600e4421a00743d460601c801d00d5980e00b220b1003410403146005081148400c10900881c1120358450340180d401148a18140144860340c4100c01103500e060b80c4002c4000c8144d44c554401c40241e2041e640010050071080420125540c44400040f594100700f901d002c030042d130401601c0b0f0050f02c040d19040703000028444c00b040100300b1549130a071403820034400001c402d12003251b968 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 762450071 1250 762448821 762448837
    0x20a0605030c1215040606020105041a041a010308191106010308160218010e060d03090605090d060219030e010606020304090203130507080f01140603060619090608011a1005 76
    0x100c008004120b00840320400c0e150f2900010342e200b062440c1c4402a00c0c94410707001c009a000702e2410b5400f040311403041c06034622480d080785240f40b02804001e103540710700c1c00081040c3d8160030b8680b03040d40080111010b20b4021800744c90400d8450140340c91075a000c4450004030002d024141c178890355500c0d0701003042411030360012a00c1c0d440351408402d405984811580081d88108224a0000c1851001144506954080c80f5900290b55504e051103030245407994040c0115428020801030940300e500180007100c40034113030350b44040742580d80c0016a0441c8450540c41126640003a06455051180302c0369403140c1402802042e00e401c501075240c1c816401110440b0b5000000212010088208006050340c44411101810381d14a202ea031216802d103102400c0e9400c0c43c0480b4400840c0e244040c2c001c00005010b4101a02d809007003288099610564122100d41c410300040c11404510404c8014000d6034004282e84c0c1c0d182c603048038007451240c041c43c4140c064485d100716090f800802c1c0d0b6454 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 762451321 1250 762450071 762450077
    0x209070f03020c011d120f030c090d0b090a02090f0709060507060e060106081e0705031f030b0c0915032701091e11090610050a0e0607030c12020109020a06 68
    0x500206044020f40b18402ca9643c807582820218050000074946009070000c1d500280c46000a09159403400c40c0300c0d65181418002060010614140403600140b1250600403c400a90645031303451104002d0111a841216017040a0400950034030541043d80300f415181401818500080c002d8801c800c580079900c100080822f1000c10845c59902c4401c115002d0021240190b95131000104050802c442406010385c00100f0300d0303040a080c10b2400d010340e40a4564904541d54003ca41d950100340e62a800620410f000c800030100300d5040321107001d048000419a80c40013904248182d01b60020200000b0070300400410500c7d044900c1d41004c49401c1586d1062036915031b915243c05002d41100c058108219245e0804041e5500385109007101d00c281c1d00d031803c180000c000c02a40a10071916a9080510b02c1c5200c582141b040e0018840c1f21618240311080700c27014008105140c102250440200d40010205002c0c0b0041c04406460980c60b03200034081d81ea1a0703408244414001d110345014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 762452571 1250 762451321 762451337
    0x1a0c15040b0109180b0114130207050304060908120306092802030105120a1707020a1d01090b10090905180604050f01140907060c0c0b0309210a0903080a03020f03090106030303110304020907 83
    0x13003231b610b002c1800c86190030000190b456491905102d9203a070301622500011580c040c900040740c0401203074000048001080352815a5214411320030790a0008100848080c0001c5040350070320001440968805031103240141c60750706007018000b40c0c510a001494103907021710343c050001100307003052f1402c0c41c01c000c0409403603000d01d01c0468140960794220300e512803000c0131000e20150300301601ca8100c4a6030081401980d00c0c1d28248154030040b1008200081d02c408801d000d03d111a400c2300303402200355515540e0041000ca00c280c21b02d841540c044880d0b4019020301e100e015000d000e20700c00c2d24809034581c034990406d03203031181e91150144200820710220000e10418002c01e0100d003001800e09040155a1340360000354580c6441e8030705403a42c8034804403480c0d0224106490b042e140000d24688504100908540720100c250700400210002c240d02040803c0d25640c03204c0145000f403403c1d000105840c4d00314a405415101564550711086070b05104110269035400d61150b0081464100b01c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 762453821 1250 762452571 762452609
    0x50904060f02091002060405061e16050d020703050301180b010903030e01120c0e040c0f0e04090203030706021c060b070b060103051302100507030909061a0c15040b0109180b01 77
    0x6402040d0055500001c800c130310310f80594022603501d00c40c43c443c406440740c541d140d4079007000450108060062040260002841c86610101482c1c6840f24078248281082031a03c8214180d070b0202d00120000b44012004126201c0001d1000f4075040c84820140a683c0201c1c0c002407642c4241d20019003004032030303820555107074051102c8040c9031504000c248450380418101402c10107142039014001c41c9081c1c3d00c410000c0c032454255090410581c2d5603441d1030031010810001e0458030308140d03030500003003200301c00241e00c0788003c200f80b0181402d901d4010380b501240303034100e998651001c08200c00c00c1042000064003801c029a00c96004d08001070992584005003941080007500250890020906036a003e900700b00507250040c420b86e681c0e00010340b0b0315070741d0085d07400900c5140300840c40319996100068540e0050002d14440b0411208001e404501e1141424020344060710400c9145005000310200ca000781c2c14020044501018150015034500d1008001441140c11124488400c54 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 762455071 1250 762453821 762453851
    0xc0a21060f060e18010603020f21191a010e1803090d150b19050411190306090e0a020a15090302030a0606050108090f030d021605030a030905100605090406 68
    0x8030301c060205003080400d44035811401e589030700755080454640f1030f400c60b40c00007005004d208291703640544640340d2428050180466034890590420201d0610700320499940c608120402c02551030701044214960fa40c00c20b0b907089410390307440740c03407207620040140b00e201f0103200825088805036042034809940d040700d203800c41c003c07009510b901c0000c0f44000b00c240f01102d10070001040b00d8640c20410620043c080080021500f00c08046404107a03000300010b2230240d000d0a0040d400541c01032a010511030b80a059020112a00022a964100612080000f442040d08400e140c500414089150303400041640d1021b100708441d518035203144011180c42000d98100a550103012180c1d00d44541c039126015010f140500c0e40010307103280000b0103070f0200003403c0c000894000301031442c06025444080280d404400500a040e4600d001507000031002c0000340740d03030001580e001070581c1e564580746040012040c08000418204401800969507455415400c41d0740304600054690b40f211641e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 762456321 1250 762455071 762455081
    0xe0f090606100c15050106110307050703021905281403032208010c0c0b10030f14010b06030106031401060509010e0123040f0e01090522050a0b010b0c0c0a2106 70
    0x4c040c019140b2070300c2e405842a4100605031041c58985a0310f4401055003a40e403801452005491544103110800c0907040014085107031890300d805d40145161504080382210250480c0e031540200154000314842c02c882031014050804100760340344c2e4000140001c0c0d500c1c016980a6144100c954a6003003408403040400340041950300000d01268a080002901c030700d0380800152608000b190016065042c89500304050742e07400005d40a2400040c0c480021102c0c1d8110408065941c03100b018003545e40d200f01450080c002942c020403040003000c0c0d150384000c0c040e030080c028045d0030300800060703a0b00800c3c44031450600b131074260b40c04d1210b100c0e00884140100310502000318002000300d22089020041400c4d035001c0d0030100c0e020303644d4550880448004558102c2106c03540320b90124018560308a04450038001d800b00e40104455440704d01c41c02000780e00411100c2800500052f030840d05105845046000300c608480300742c80c1c171812985840d035082a000850344145011420480b580d804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 762457571 1250 762456321 762456323
    0x2100b091608280e070b0a05071e05100b030d030c0503060402070c0b030117060c0f04031401020c06091c0e0a0303200109030509150315100309050f06010e0f090606100c 74
    0x40b0320f03441c0f100001c4031000300540b02080c2e6550058400100f0100425000c0b40ca1000c090354401c0d11b0000540c49400000f0401d008060040c0e00c4404120041181005601291504c900c00001c00102c40001c041c54045a0190f207814507081550b00c0880382e410200f541d40c4190203882c0580d69443d145840c0b40550102d81148000315404000030464a01c030039017880d900c000c24000c881946e1034800704400580100458002007000030001480010200300000c0180d200201c005800c199030a1003103401c1c800c08968001503544242c40d200a00480383e001c7c058050183c1c103000c3c2440300ca850105000c11114000036043c00b4200d25030620801d0911190030b0703d104100001c2180391490701e8000c0281e4131520400b44a00f03030441c800c4c14a40e0a5600300c0340501c8152442c080760203120f806000b0380428900c0f902c024580e440261501148040c4400c400307843c508005840f542d81070680307402550340050044030350b140100c010844140340008106800041c115014440d5204070481120041d8071008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 762458821 1250 762457571 762457621
    0x60a18030b1b03011206091103010222050d0819020c0613030b010504111204051908070b010b250512040b0c0601090c050a080c0403060c02100b091608 66
    0x107020200719072038000c1e520180c81d090605840c030701c0028a8003082c020741d40003c890548080c0090310320307800f07940b001e4401c200300a070104100002908a030080e103901d0340c00e8808801205540550103408801511040341c1055940640341c035411078034080c8062041030039082000c2512854000c00603110f240100500050741e62200d0a4111a14080c0344002c5500400c00c60020505241c18000c2c06178400f50034030060300340000301400c032107081e4003d0001d0302d8030300403154500d24080c003a62101315064026079a465445419140c0b01000c1c84050340307c2c0d402c0305000e100c202c0300c00209a1661401d070b0059000b51001c10424188035092050000100b002c0000001c9e0004012481d82c0140c941074a042d0140c440b180e036206071401c195241c221011001800c00c00400080c0c0d40504052504900900c00c65424940c481d69050700b00e800c610724a40250303210801c541c200c1032860190f80300580068032180f6003400c0800425030303000781d10181c40040c02120700000341c04c003040b910600380c020040c0e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 762460071 1250 762458821 762458867
    0x13091808041806061b03181505070302060a05061c0606270b0f03120d020c0114040209150607020625060b0a0b040305030306190e0a0c08091902060a 65
    0x20710300c1002c8042414020103801d060020008440c3c3c0030740d0041c9010300d050900850f001e119664105c91000c00c100344003c03003101e02c240126660302c05607051040454075881d8560707120624107021349802e500034a0009054200402c018a60b21464464607040e54555148802e02ca60340c98490050708054103ca00114981c0c1d62400c542c00c00781c10300380040c41402c8000c000c1c81c03004105000c2044905030f9140e4055004045c02d882c034501c490700800912130b4003440107080041c0c82d400b00e82944c03948110002c1484014041c8000c0d441c020725401c0e0008040103681c02028110300c046552030141744c8000e0710a144c0421009a2155429801409640300290501040c4001d16180700101901e601c480c4c0600a581004140800f40c00111401d49400030001e60560340d4050070800d01c50b8801c1180c2c014200218000075001030701c12900d900031000c608012030b074070041400003010082c004007100520744c481004410404841019680c4064068030b00b9603030740c00400c509941e49100d6030020a4024600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 762461321 1250 762460071 762460079
    0x180604080604111224060a050d060c02010c02071a0a140d0c02070626090c1f12090f030e060c070e0612030c190201120c0e01020708031309180804 64
    0x14070301d9103103654000c0710340380152000d4030580c607034034288001214482c040400344699817040d80300c41c15501a01c000d004503d51178a54001c1082c00d14011001c03111280c03281d014800503902802000341c10480d6200800c880c0303180c03800e214074945051700030f00030412000418840040c4a00c5103040c0d402c140145813603590101e99405001801d04883d1100140694207002c101248102c0b40d0300c10000b840c80c201c040480d49900c2e40084602c0183c02241280b05d0032620645584a21020150072046c04090b644803040700e03000a0418400b45c40c59400701890421400c0002e6401003858031490380510f0421791198284001c1940c81c45800989000351003140c800103052500d101905100c0c0da02600c510f480358103140d4425507a0301a15003911030b50f03040100740100810312012510300c080c0c0145082d9018524164107982100c062140000c0042d0700750220820a580402ca040b00500708003005500d801c401c10103004655095000d07881a0b03d8842036401c0303104038100040310b041c07508156211341d1a60340b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 762462571 1250 762461321 762461333
    0x50904030e010329130b0d051c0509060316091802180a030203030306060c010b1807081b0901110a14160e01080601030f02030a06060f090f020f180604080604 69
    0x6040340c0d07400039062040c5035400c1c0201c3d40703c01103040c0301d820020504c146004200101c0d008030300c0d440c07034003595904031202d1240d413030406900059000301c024003000545020004107016401d1008800e2000070400e00c07215894480407030382c6c030071520102607030640c101c0c040031116032890f613000389240000c0d5070790702070704c081d4680c002c2050b101020081512a60654140140c2030300c9403101035419042800081c0c00c60400b440107203410000f49000080c4410454006254030305403803030014418100c6010031030340a4021171000d4011103c48102c1c002c1c02c00c0b00126203024810003e0140c1000324018022070821001c0003035032401648030002800342c81d15140300a03030f500c0c4688071980c40a6045840090810404080c80741070703c00800c050204d603820750701c8940c01401a460200c0c5c0510660140101085407489400098203400100100c072900c3c2030554000e584108568610136841040341c1022a42054220307241d1000034036a0701d1a400740701000074040e01540c0d001c4256800340b0740c200010884 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 762463821 1250 762462571 762462587
    0x31216230d0f090c0303140d09080406030f0e06061c2001080c040303050d0b0d0f05011d03040806010e06031f05190506011b02030c040e03031015050403061505090403 73
    0x40541c03020007100d240c03201c00405450103d007000c1c00080c001032060010030b114a0b840820500e000714424913000107103200300120b541030442aa20b845001c1024030095906006a260038103840c07030240260303107620141c99125000500268480d440c15040800d0848003403000c900619000a260065142c0803000c8008801d00e852119000980c14400100580141d4098034140da070540d0320182404880a14100104804c503107040d030101800121100040b0b600e2010342405102d100045406803000c89403614803401d83c0c046170041e42042c082403201500008a079811203ca21840000075265500808d007070902440000d00c81200000103907038102020380145005980403d078200c0388902c18003800088900640b00c15001510901c4e0304d0300602091030f01104003d00003020358a2842143d4002001c8840b80c41001c41d09400100c00c02041c9001c1d030743c070390380149421454058040c3c50040020020710a501004020940c4e8441580205031005404800350a014200c01c482d402e0604024100741 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 762465071 1250 762463821 762463837
    0x9060d14011d060c04030f150609090f030306090618020306120f0d02070603140114151321020a03020d0f02030a230d0e060702030321010503060903121623 68
    0x1120300c1004c1101451100122021290410004402c6074040d60314000300c5461043c2020b28161604004034908007148a105402071103204d685031902d402d8600a001d44d90705511042c07200b490542c00b0402c55207200038050a0040400c0010307507030303a180d0001440381c0019071242e603a00e2003200104809000c00041c000c1904c80c40d502111b40d11607489200f1001e840507d56022280f917102c40c0100040342e6000c10320140440c004000500c021ba400c9120845034211012020311000264010401c40c004980a10901c54280c80c241103080e14580214000184c40d101c024002c00716104080180140c110001016a0b070007002d485a19641d03080dc1034241d06c20006904200d0b00303c005250b140b1400261100700b203041038485040c02c1e442c40d010000c4540011314213a1b0540401c0142198047c81e0b6000390100b100c9950203441294104400d0500d1322400424000840d4010444141c0010b000c02c841640682c4040601712180d4030500111501c151401002d568250703644060303102c2c0082d140280ca021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 762466321 1250 762465071 762465073
    0x307150203040c1202030a031d100306050112180b1b03010e04060c08061e0105070b01080a0606051e091003020603091b0f18070201060b030405100b0103020909060d14011d 75
    0x140c0e881d1600141132000c03910b0000c0d4540d009a110100080c0603440415212080810a1400004180120b02c00d00e451078031100000380e45590902680d0b800c05940741001094070001c0040303c43da41d41703202110048900207441c407003815000801c0c058070800c200c1003e07a00303442c0031501d80d65104121108040161412030349181800c003a40c0c031031403185444501c510b400034500b06940004c070310100c0d40d4165141c0c60f20b0400500304961004030320400c2e1101e0003410280000c108142da2410120101c8400e80c0200e07110b04050a034840b2505141c400c112072440d42100e180742d40752a089001c1c0c900c1c241e640c0c4000d400c1103001c0200141240085801103019088168000d510b030038071010440d00d50313601440d1a03400482070201c104c9089113145070982c0565580000940c5989074580c4138903681041710200c072154000e65051130414424050000c08040a00b4213505104041001a4414030014009402078012108613030134042c91402ca404c441c02d0f80c40c0200b01040180c64200c000d106407040040c51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 762467571 1250 762466321 762466343
    0x70f030807051204120513030b040c0b04150e01020304091e0e1c0302090a08010603050321010501080c18151312050a0b0a060819050d0e010f11030715020304 69
    0x801c1c06001118142c404400b0014650b81d1580c0c0e617004800000110f0740200a028004551480021000903010314012040c82601d4039040c5000c2d41c1d00d02550708080961801400304110000c5030a039940070002d09030900020381100d900040703140d0f005640c48801600d0a0504a0b43c9900d030740604a460151149424002c00c0f0910304030030b0782c503d07159200c11071828800060001e100d2003580500416600200f1034001301d40c0c0c800f0020f094548541007692070750000607460544541030704d010304484900c070078080303040d41c58000040d044d01c074020110700c0c2d1010001b58520324204044c0071406903074002450401e5060702d40160007103d401004405032500e20143c0b001c6003140d444400c488803030340d20500904c1c401105540c0d065906102801441c229030300e0b0400403400c15028807844124003046001d010803c40181401450300880d8013040b020701025084400107a68818089594030910b03003002107144840b5200149180301d0904080c0c100c00c0342c80d903a902d503050250021406203008540d1001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 762468821 1250 762467571 762467581
    0x605010626061903020301020d05010e070912020d1a0c13050d0503071b03170a0806040507020a260d0e0d050a1d0f100c020114040807140303090303070f0308 69
    0xd5074030081c4084003000490707900011103a180c560014100c50203100e1024020507a60303070101e420b80e08203191031040d55403038a006104d010b0024580320742c000040c2c584a1215440c00c0424000104141340103409910b01040180c00d01c0900b0a14401c0508082261080c52501c0d04150800c0d4110b0b80707a089005890a00004403490441031030b011150300040550328044455441e001417143c03d400f010701640c103039000000850710a64080842048100c4059602c403c00c4c03400502c0d00400501c0c042c803035460708040c4022180e00003088911140e100c25407041c0800120104c0306807602c44080d0144101c80090b140b00025455044284171004400480741c5003a46500d003030700c0900840d04018001a004503010707003d03a00b4003280d03a00308035010b04070010290740b401c040794160b1001d108540100e0407070184030045503807010510b102074445440c410f0619050812958488155100351620411510982a440c0e0b40600403604100401001c0341d40d1040d451030000241c001117034060b0041412a00028 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 762470071 1250 762468821 762468857
    0x120708091e0613060908031e0a060b071212090309090c112e05011202180606070b0a110a020d12060303090603020c0a02060c0f06011421120706050106 66
    0xa103000c80c1c00024007420795030702030b4003900e0400e03400068aa02c0d0f16452280c001c0343c00b44000b075001e40c0c03140340aa001001c1e060b120b1035071081d026003c4c0b201a854003000704000c41d0220292020982e00c96101c0348807094064044880c919a5101000d410f40741c2040d000415400002400c2115610101401203607500801500c5e5a40500194001d80d00100c0503c9070f0390f00d0001402c1d00744d00e010b00e124100d07002c0032000c40381115030913003028a81c0c60060144109502c1e048078050040388016088502074500100401c001c2c0c054400001c10000721000070231516041904641e40380c0d6200c3c901d86840c0c581c0e44070002e680d0000c144821000c6010800c164282c448580114001e9a400d604c40e00a11362a0034403ca00941c407020705403040b406140400307001030f541c1400500011900c1c41c01420012026840d080c00d103041a408001040d012608141c1180c882020151110b00702101e485a80d100c242826402e104441c14001c1c450040065444100051544090b05031580c0da5221403960f6800c030409 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 762471321 1250 762470071 762470113
    0x608010f1a011211030109020901021b0f060f0915070c08151602191118040b0a1503120903060b06070c3005010203041101300212070809 60
    0x403004602480c40441194060104121008030512001030483c0c4c40b07814604858101fa00072400440e00062064002d6134100460307603107452084625003c01c040b00b40002c1c00c800c0781e000c21b0b07402000081000b041c00e07440c04081d51460076014081c05c400000250300021680d100920403114025030380801319414a00149500d42c60a01034a101c585484007401004200858021102184100b440c07121002c5081078410007000e10601403448450040c004100c00a03401190402801160008010100f134044101540040211071b00096100ca00e43c07003004003003140e4102070911100c58105c00910b0750701c05034400440740030340b0041001410a000308000c51250b494050101300c1140805d22141c1d04001124440101120980500c81c1401c0319512003440700c56420385490754040304100038000c001d5100e041c3d4940901c0c0c0b003004883c15042c0c243e042d00807040d400b42011203410f058205900c0c0380e41117946803014418026001e03d03000701c00600c0d206045600c075080380540c00b1710b00449541030b080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 762472571 1250 762471321 762471341
    0x4060b030412140d0e0a02090106020c090105060a020715080f010914150103230906070503090a030f090b2b0c2705060c0d0219030f030207030e0a090608010f 69
    0x100481e181c5040c0d078111510946014165142c44040020700b13581d220301d02c1180c0f80528040068414039140d401000100382050780500c05641100443c3d8a007560380400c0c45041d11411030300144c903410001000c900c1d02c0b215400c40120840360208036805a50000242489442060044040b503a218081d901c19a2461401d08401c911180c002c2000b6a08954a4015900040c5400030b0104100c111040074031070f04103011440c1c84052820310804c0340003404060761241590403c5451070810b0600e650307550307146c103c01a0410546040c000545445440543c0003011100701c960744402c00d05051010100c0b1402c0984070748008080601103801c3c4d540580d0150060b60307294200b0440240c0d290b460768074440340740da994aa03054071020626580b040094044410b0b101c0081c0b002c2219140040c6ca45002c41890114580290980c207000950041c40c0502903003240c540541c9640c024a01940c1080d05003011030340c40f0003010300210345e00903240d00030812125880003d000c04a00d5040940803151031001d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 762473821 1250 762472571 762472583
    0x1c052205090f060d0b010603020a11190b0403020f0132060604050f014104350109151512020f0d0b04050a0212150601030f061a0301030204060b0304 65
    0x1c00208001c0c40d01c0302d0b80d40d000001030408800c03036465540b0702c41e000c40241c00c2000440d50218850490a50040811101541c680000c00c0741c50b0700151460b05100200c0f0b0000c061402d0003000401b0107109120070b01c0c403108910000e0041c3c94155090b00890500e042600c0003a400513082c4c210350481440310580a40301c050102072406042c401030033800900301c00424103201d00e00440136080a403e00d0050b2003180d01c0748482d094006103600300182c0d25000950402030310300502081c03241c0170100e000c0e00314400019103220f00340d848090070b444054124110404495103060400c07418041d5140d1035001c07401541800300f0040c80c429100c10300d690341c64098030740640c1603000c02c0401800e004581c8140d20030002c01c188440e503850398031500c07050812607007101c1541200b6490811410102840440303200000050f010f01d02d640710701c030a18400c1c024002c41c105a100c800e848040d002640c8288094034034500d2002e0754030b10140615140e0b41c800c0c40120b0045140400005900b0a48003e0b03a0003664481d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 762475071 1250 762473821 762473839
    0x807021605041d1506030d2307060608060a090b0606070f08070f21031808071212020408010203010e01080a03090b0310120b070e030318121c052205 65
    0xe024880149042c0c1c4080040c1c0200d99070f294241801040311504900800d0b50201051404200381401c181d0400012028881012810006401c45113034543da02c6e000480201d4507032a80b4104000a80b82980c0802018060041408507090b0240c01451200d0b0051009000c0c1d03031110400c0c403441e4400e00e2006800002c2e1f0340102000034100d1402048030501030184400300c040c064640744516048004090034060300d0f8501d980d400c5401d401740c5003015542d04c140406a00064540712854410150000c0c40d03c5204d030390460015010b401c41148814000108545841c1c440090700d00079802070054004401000000150840c2c000880301c43c000d60581c0d03101540c500d41030310314803641c01c0a03001c0340da00c5410800101d034101a61142540040c001c0071103000c541020440070707101602d90488103001e40c00810060b801d00785c02c2002c14130301d003e083d16400b10740b10707040d8921402c0c131508000c1c1d86002c14002e4070700f05007180c1c840043d001e2030021140d8402d0041c001503840c0c1060a00f13108554204c0d50034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 762476321 1250 762475071 762475079
    0x21f0e0102070527151215012304051003061a01030536030c01021306080a09050303070c05030903150115030213060e01030b0a030302071706060a030605040f051c08070216 75
    0xa0103110741020844801c445d11401c07900c0003903104c071041c4841d10495440703584c040c040011203000042c0149840b620034120f4118088d00301d0300012403155440c0c007958880000c1041c5088154480b4000d64100204228411f4103030884144229a102c126000900f07080228040f00346c00128911244d0320b507804000d2540b40c4c4107c0340390750b21590074424541d00060004a200541c213000806407801c1c16442d10000e5402c00394058100c04c0302502000d0780c246000c0741c25001a81c00011a41c1002090802500341350041c50701610354450072032040e4040c084e40040c0c061030900e8402c0181a542103008801e00d100301100110124050180244d84034924140c0070400c0038090701d500c98040d41c2c18500070546c9240035022441d0701d041a40210016130000e4010001d41c2d242d803400c642d115020349d01070078050800f64001001181c1030b0001415040d0b8582c041004c01c2100c1841a11090340724040d81c1c84031060b003640004401d85c1c000e442c1c02040c15607001403481c920100359140051810b9500070034003410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 762477571 1250 762476321 762476389
    0x24091815010b03150312030403091701090f03080604090609230a1e0311030304210f09030803180d02010509010c080106021b0114120a060b03010b0d09021f0e01020705 73
    0x707070054003901400342203054140c0446e000e005510650007a00c2e1882e800c2c0c40e180f075840500c03d40c510191403591526000c4800a00d030307070952640d4540c06141921040d2a0030000400914900d0802800245005800c1c010451042402801c81c0c00c11707103620740e080551140340c68950240d408000c1504c030301040302013003940c411040403043c94041d20b4004d003038883d491851407855005540a03180c0c08107400500080c0703609102000c0d0003540d180341802407001c9034840a000e1b07640a000007094541c1c0407000070a25a05100c5003007a1141c08821117041c01d2480a0203802000c0599882840d5400c12102c0c03480c05000c0c04000d812200a0f50040402c1124160042c00341000c822b83d541c10000e00301d942041855414000e045151003d1680304528180a110324040321a180e10041ca0900c0c02d000401600c600c590948209111003030002c02c80041c1032000070721f102c123102551030410701400c7c482c101040e400045040600820380840b00c4181d29081000300d04003140c0001825889843c0d0800f120b025 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 762478821 1250 762477571 762477601
    0x507050403060203151008061f0f120f020a091406070c030f11030106080d090e01030506011a1e0a080a090c180b040606020f0717030324091815010b03 66
    0x540b00c0101780c80c1c58031040003950f8180c0c204d10000005681105001d910719101980c441d10700640042e0041000503210058003600d2072014000c18880142601d11400710039401503c11181c030010b00b1966a0896400a80002d006005190307400840d10348024450806904071071382d4a8014001c1c460003440d69545070a0031140d158110b584100304009a003660700c090050b0b402821032440500407595024200601d141012b90000b0070780e0342d9540042000c10030105030141910000900408402151401462144a440c42c0c054880c08010303460220501d038007000d0114041c40742d440c1e2495880d040148000e03100b1f4810003a00c1b90f00010020401040c0100303c1030200c20f0070712400319048000388001003c4514603070108026070000f00e0f0f6480300400c1442070101411a1103880001191041c800598a01004044a109203580110b06202500e002c0c02d42c82c1c43c1100511640c6245015014200e0100019080d80140d1199510114580107000200b07030584c1c020f07009090031542e0300310074110044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 762480071 1250 762478821 762478831
    0x21b0109020a0e190504060e010b030c180c131401080114010206190e12070605090d0801150c05030d06090c0f0221090d1b1211010309110d2003010507050403060203 72
    0x20540c2d84c1c890410702003034003030746200e540184000101046d00750300690075a400f0889581c881d03004440c40d50f00c0da035505c1c020b03a00f03107070740c00b03c520421540c99100d41b00e02c600c12006480d818042d900d0000440820f224800390042c0002e90b90310320640d136200b090406100c1022a064050307041140042e00c1188502c40014450b1079000c4041044c0c070728403225908080543c06000c2d24031000043e48402d12210f8000c483c1c0040c1400c000340740b490500d540003058511306001d80c0c24522000801c2d81d03101442079240505041e000340070749650b0421150090014402d40c403074140580c0c01c02080156060148001010407400b81d0080d052a00604805205010700646114000038062007580d640b82c81d10154044424400e001082c4000c200c0c02c04008442019444003074642041611031000941d0340e91200c2d2106420300b13000c0b48841140c0b410b00c442c5031036490203640143c020401d0409010001880240c02c11502462810030304401c41490309a9604407045004680100030130000903940358010769003c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 762481321 1250 762480071 762480091
    0x5010b0d212105010e0f0f0106050903010f0e0a050d0513210c1e09150b0702040b100203040306061403070506070c0b0703050306100f140a030e0d03021b0109020a0e 72
    0x41c0c0c4801c4502e03180d00000c4036082415a103200600070080d0150034250888044c0340308980728900000007451080c81409003404000f07020600c048a91425080b1003480082440284522806984c0345507960780321113820b80b1180700711040028200d00600c100ca1800492480403090b803030500804111984141c1d00100350011703181081d00200712205004005810040440290f9010402c07100010720360f2078200a01140c0f134050080d01c1c1c0c405a0144200b1135124040003a02d030b1029000103001081101c1005030000b0b0302010b14151300c3e601000600135203104590802c0016102d2044410080002803241d80540c0300c200207004070302c0c110b8054a00c0a00c99003129205c03a440f4110078500d500580700480104078040144041490900078106071100645002c100e45036000c500184445126000d000105100007190030486200c0d0300502412000c00044540115000b40010700950014a80140340c0d02d070703001d017442100c6042c080c5004043e001001d00f00000d0400d8505902501d0240443c811 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 762482571 1250 762481321 762481337
    0x618120703031e050a050d0c03150f090c020105090c120708160f0501050304050a0b06150f0c010b010f0c0303050c191701090627020405030a05030705010b0d21 70
    0x19260800540000d9031081d61005040c26441c04142121840d035814001881010f001514400307900c80181c3d03004a503422000300340b002c02044250001d00500200c0c4031501c0c0d610001213000728441e107101d400c82d10710f008104440307040380004900b00c410035200ba00941c2c0100762000c256140030310901550548070419245425504e020092510041e040c40c0c20b896810340303800304410034030302e61048000c08080c284203143d440c19a0b6982e407503c280007001001d21030580d004c03c0c0c07191a0034840110403404101441e40d11500d01c48032009640020350b00d0070641d820301041d0b21540d4030410382100e2680d031549660b1011019079a0a40203424001c1c4001490030091100b2110800c0745134080c403130000b0940781da2800da051003011601407a016040005480d043c50410412846541e6103941c0d21012454250418549400500081c1c4120703448240e01d40b1419404405104000c0001d10820303208200800c118000c0030180a108400c9400140140e514044034005840340c4902d58055030409140801d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 762483821 1250 762482571 762482599
    0x12090102120c0d1e080a090303061a031503010b0a090504210509100806010c06020733050a0b010503060d0c2d0e060a15031e0b09070305060618 63
    0x8080e0040507400700107901899036842907a400100003202c1000c001213140c2a07108000d800351003600040c00c400c1c0515614445002032520079071140000e42940d540c109015141d001c60780000390400c0e03541224000c1080002c800d54036052251a0703031a54040d02034800240b60000490044c440100140d4492481c6503803405108190708401c0c00340919500c3d01c1d603c408504c0c05014085004001c02da060020705024400030b0ba82022154204c1e60781709101503503c0c41c0b507242440c40c2d1061202c4002411504107050b5814050043c51007030f40e00c485103420056070381c0f584444000d855010b860b040c04528104045460341c00c040342c05403845405509200400c55407404042000010007030f41081e25440700045010314509801c03020010240341c2035070030722030502c0000a8402d0f00c451143c0311100b1100d8004c258014001e0b0050b021040e800403003595042d0b50360795000301424920407050300c40c003048400918904e0107031150724001c0c0c4003c0c020b1800d10b070a0f00041d0700000342c40007481d0782c499010344101c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 762485071 1250 762483821 762483853
    0x13052b0803040c2111010801030308060f21010204081213090e0a0b070815040e0606060a02070e0709030210081302120709110d060608011512020706020a180603020c12090102 76
    0x246850312100804241a249070a045032159070720300905040161f01170040021aa10a001c04c0c2c1008080741c28902103682c00700001c07020300380700e0112115410700746507290303005134194040d108980d40384054400609141131030310030301d1247d9001c07030710780d08407484040c008859103621007498141c4150840e14542c0c401e031600902004111150750000b4069403c0185800015614821601040d90140300040d10006103548420340100b8540c025078001c2064005607108024090040800c40c040d40c186091000c0c0040c01140c20340400da003d0b0545800c804d180900c5842110311400f40c9030070203880c140d581d500b08100d10080d0389091031144030749070010410003000e108070b82c6007524500d4640c5d41d030300001c1e079104290390740c6074002402d10048500400180c800703d2403540d030f0b0101a05e0600c40d40425128901c1c0203004100b006488244081103803205d580c3c2001c1c4000d03140480c4c13801c4102075503481070700b01c003680701e114103403003885d080003106420002241000e00340c0c0360014010781e4510746e4200050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 762486321 1250 762485071 762485099
    0xb060d020c0a06151a2206020a050106210303112205120c010503040602091926010608030f09030709090c091b0f0813060213052b0803040c 61
    0x1210003504080100d20401090b0710843d402160031841c484001483c1204070010707400c411020828071790001440000104032a2040141d102c0c60a104c81c10180d11200000d5451250400482d01903181860100d1850380d2001760a9061000a41703540074144996400c070b000d0214603030f2802000c8414814441d0351604090040c0303180021101c89150a403400c4108415800d00c0307000e0f80000d82101e01c0f29511070340d00000720303603205402880c0540e8694282c00401c04010f101c0c01a4101c0d48800e0300c000c5410302a03002c00c03d1103010b01d208030005001119003507500f2510144a09070003540100401e80c0e0785a181e87c00b401e25070600a00351494950b40d83c2c00001504c0d01f5190443e405410180e0a0006920794850404c02d10002c01069030030350790700003000d0111010b0030358400511128600042407030f6500e0f203240c0052a4030039810b645805043e00300310044030060050602c5008480008101c40c850088900c1001341036046940d081400c50319400003a0744054000d903804981104080741e241e83d0304240e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 762487571 1250 762486321 762486337
    0xe030c010e0106090b010c081b150906070306180c030b04050901090510061d04050a022d030309060a0503070c350705060a020c1501080d020606030d09090b060d02 71
    0x41441c070300880616084404641200c61030038a001c25604070350740d1140c80c40708181d62111585545070084800203044940740c00103004280b00300e845644400360f00074107850041c0f2200c0c00b215841d031107100d400c0e826580d0354059140c0c55980d40c0000c1a084c046030300040107883c8141170004444000d81701240070703108121009040740c0e454003400070030840d0801c4204080c9005000c1003050b1800c0601e0fa0402d00841c148074603102e600e403000708050005c00d010350814994024058912081840c80160110090b10325039610f40c1803585448641d400c5c0442140c8034642c006260794a881c1c4814415202500081c00001c01c00c18041c04810005c0d070700c00208032000345020b80308035400000e0101c106440c00211200010745505000c100c00140000401c01d070800c0b4280d20241c0c0760a070325100c261500d2840407020522102c50400010022400b0580304100741c2d0755801d5665603030366142855036a240352002080069180441004140e005922400c0903070f20081515203001d10110090050760000c0c69 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 762488821 1250 762487571 762487573
    0x207050f070303091d06010e1203120a1118101107030f0b0c0703020309040519060b0c10090b16140d02090102060702010c091e0509040305030a0b0a0e070c060e030c 72
    0x10070b000307050300041c4540040c20450002c0303041400080340c48114410281000d814011001e811815a54a44240621842c42d00703040740e440e440b27000748809a5003400d9031100c025501d45041012050b40e0b4408440382004c200a180361000d07481e0703060041140044000a0400041e91154600d03200244401001503003d9403015920040b54208141031a1001c3c000d00c1130700314204404800a900401501c00b1100110b60005003543c0307002c07420304890418642c1d180740a01d800000300d10b06400802174a0f100310003a00b12128900c07140c852101300c0d00c400710302812440c05400094050742180f084540034a08034500a1400304100c0030103501600501e07080381342c0c0b41e0041034286103542d0400c1415403021140c40284039858800c040644105191300400c441005031203661241c0c521014880d000402020b4110a40c034501418010456001541da802c1054148100080380d0319010300c40e00203680c00c1c9400354120f40c4a282090765100102e800865585031103e008440541003880074142841481d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 762490071 1250 762488821 762488833
    0x100305220f020a060c050f010b090406050901060801050705040e15061c06120804060e031203160309020303070302011407050906040501120f0f06060f1d061c020703031409030a02060a020307030207050f 88
    0xb1a10721f00300a5000d01c95589603250400c40c040310742d25040c2040d0803036080540041d045d110f00c10071501521568000388000e43c2441c042c041400c0e44a0010021500c20200140c0c4903200c00c0c90f100c04503820141c550398401000d02040d15011840c4400c3d4042250071400040c019075640c9602c3c0c466411a04266402900414200101a000710500040000031009840c40c05c40202210301c0e40e01001e064000d0b031528000324400e0703441c0658440c1091a40003021252100500d2070000d02034000d90f02d0701c0340c0c50700f00b00001c24075550080090b5081d58600802d4641818113200044403000d14411500e81000c2d115610510000d034544640c1c415810320041c003180490621002909502c00105075400b00454100720307e11079200710b000b82010410490300741d07540c0c0c03c04200010400035036680fa00e0025200003104070406800d907200c2c1c0312040884450103210b07920040101c0d22070242e4106180540c102000181a8219030703401558000740600300103082103102d03142c4da852d2810303020080155074004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 762491321 1250 762490071 762490073
    0xd050405041d0d1209080c01021e040602030405010c021818010b0102030a080604091a010603020315101b0c150c051902100806010210020c0a02100305220f020a060c 72
    0x150003007610302c20482540010401d5000c1200359507504003401da00420510a501c000518125000b41c00d00c580c22102c03044d15500b00c00c08150003580b015280c50f01e449162080300c01d040343d100341641e044070368a402450500e0b140800554090011170402c0741d1141c0c11081c00150b491482d070021780601e00b100d02c0480b040510349400c42c03c40c0c081c0788030b00341558014084c4180c0a49e01100751907011a05072070118441003d840c04c05004502c0c0100e003104c00d031681c40003080e455415806540709104101c5030700d0b2960310620902000030700b000c960400082e069801b010145a000c17046065140c8120b07844407007595103a40e082e1100c5617a21003c000101100c0050041c41405c0101034a208851074005881d4141c0c2e500083c405404802c0540034014000c0004100f60700904c0043e441e044602c0c410341d43c0e2070103006c0c001d450f9803c1001c02ca1042400c645032840040c030a05c01c46100b4020310b15540c581e00700c100340000011741411400c54000528615210068403078950081c0103203401d440e000e10318002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 762492571 1250 762491321 762491329
    0xb1017030c010507051305061e070302060a0b10080f060a17030408160e070c11040504060507120c0909090807081303020a080309010507060b011701060e240415110d050405 75
    0x80134203031404108090140c0340524524040d1a01100c0d4100c54840e950802c7c404440b02c004442d90180318196000b1034107105050b0040360040c41100441d90800855601c001044110402e50391501e00041d20200001d030005280131034550890b100401c487d403516901c101c0a1500c068180058120303400c049020000c400040200605000c80340385408819424007550170814031004010001b001a151085001d100c00651180d045d48030240043c00f041c43c0500703001000c0c2c0802c3d944000014080d0042162503103541c0308010032418150f9505524610700700b803000241c110500107983c900410070a407000100000020289d901400e511061500e01c0c600400010300304e00c2e0300056039600104001c02c0d450703078440700315140650b100d28001403072404200102d0b82c0000040c0c810708148880400403070850f400900d0f030480980215000041d80c2d5280c001c0400b0b54445140c4452303c1c1c901408240a0781628803001042c041461520410070106015094900621080e1420110798001020310003428 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 762493821 1250 762492571 762492581
    0x901090b43120501051c0f15140604021204120504050306041401110f070308070c050613050c0301060515030603030c032217150405010209040614030c01030b0a030b1017030c01 77
    0x8214804002c1903145c400401d40c40c3c0c00d11103121030014500c04440c800c100056404051aa40241075190210324061303081d0000c003044070301450701000d081c0020b015860309000b01c0d01901914007100c00700d038481d13556a100300c6001d03118840138050240008170fa01c3d01c081000900c620f01400020b05690100e070309c0f0038210b418003d803868820b1810003190103880c03007860454004a03811b00d0b0000465031030600c00c8841001156004055009903030510600303814080070320701d1090045040c0e035541000c24081600700c03505485920b40010040c144005444038200195900c0100601500d16007850248c03460304617801103569980d401010000d8170f00301000c01c1d104402429004801c1081805c10400c074656a510703140d00301d0039074980e1100080c1000000c2d0140ca1425101030000d0180c0c50321040500300170881800e42c03600030b2240c00b54081c8070358440c1c06004118900941803804890a64840840e00c41009020240f89036450b0301c009000d00800d41c00200f410182c070080e64454803260310345d600f13440c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 762495071 1250 762493821 762493847
    0x1d0901180b010f08120a050c070f08060a050604180206071103030316090608100b03100b0f1b03041202130b0a0f0303201216020a060908060901090b43 66
    0xd4844e4001180040e030200c102e800030105030907c6929010000700c5640307026440d4014030240e58200703100007000c45000a91900a640086040c8141c1d03454509000032203061591078001141410006405030800343c0c018595940140310700161880c000e00424510f0740143d606c0c140b00211640360103421a03028907407c010708411301d4041e40b282031a0341d030650040800c0c011000c0b603400020108000102030a00c1c8001003400241d51030b158a82460f040c0c2554002c00310580300b001410700c010562030070100481e0196101c0408204500105030203006d54461038811184001c3d59803500b440556540d03510840050050701c541308646411841c00404541150b0781034500602569201d21a180c804962000d0310441c0880071621540070040361a445030a41c10701a42200f0303405000f08045602c40441015618650301b11010303500d800e1b40c014200e40d43c800780600880d0b072410204000355920903466114201c400c5e066003685e80d0055809003019124040035042c2c10910301103214150f0040032030f020203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 762496321 1250 762495071 762495073
    0x10504030803010314060c0f070605251805030703020a2108040902040302043801181403070f060807031518050f130b0118020f030c130b041d0901180b010f08 69
    0x4002c08d41100380c3c590084d854014481600c6400045000e070801020032080d040543c0e400300a90050b40f000382030b80c42c084640342034010921101042609000900320105c95003e0b086800d15440c244441e0510480d03901e4990b903002442c003c45010500c540041c1c0098010084011399582c80c52040100300d407680c600c8101b030444d4582c034111400928107280c00383c204409009643c08540307000102c40c80c41802184030b860500100b004902c0c1148880555a010b0b002d0303040700c1035640c540030700304a80300292080c1c0000450442c0020728192183e04080c40d885840b4801c88101911071540702c520030341c0e010041100c15569010001c060000909441c1c001c24105000040e0001c1038603461764401050140c071030b0807060034040a0710321f8000e0707048480c10082000c2e0280c990a0828802c002c9600607100c0c60000012100041940c54840007110200d440310418480021101849209011002001c0405035542c490740394100000d000a0740d0b02c61840346203000020b40c10103140c100c9031200e6030424002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 762497571 1250 762496321 762496327
    0x3011509032004230105120f10020d0605090702010c120e0316080c120406030e0c0a060f0c0b01090f1a150c0f19050c010e0a14010504030803010314060c 67
    0x218400580070141c4110445034141d48074410b4022501801400182d41148004100d10103900c40a0505143c10313280101d07090001c400b03100b400340342c2d61480c03038030480d42d82c0d0003100102d030350320a5982c0148051030f01d000003c81d1070340d40c1d8400180030042c1101c3c0000540d440c5e0000104903988072800c541070300b5962004008a42e1145902a030324041c0c000c403a02c6101404803410144582901a1085900502c0480d0045500c007c503194690304140304800200307040200c4903188001c045140c074910340010305110400c0b850008220340010040c0880001e0200d4102d650001c512504001da002e0401a400400c061000004d071604842c43c3c6440400c080440008510f12940c1d9442126640e80d0414045510352180c03d5880c1c0c203043c8a00c40765003c9200307005240341d8510400505003d003502450549041c0d072001c400554560407901c140c1c13944014800c000307211541115428040c404010316020381000e03141e568441c980c0e0300a030403d5550740b8014000d0f403810403040110030340c4404540c1ca1181 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 762498821 1250 762497571 762497573
    0x13605090606043b030307020c01120504020306060d150c020f12182101060603050604060806060a15021f09050d0c0b010b161506050307060906120c030219050301150903 74
    0x445030300c442c2c2d4800881c486480040040e40340c4d40349008016042c5410b6a5880c100f0034800b03507462130744064440c040782c1c8610034115142d1092050b54451500540075144941d03c1c8070802943c03041e0745004680c0c035840032071041c1707050266100380020800c881d0014501840e10807405403a01c010000319584001040046006903214400710103100d64040d140705d400f03800243c2d80318114603c000e40c506425803810b03500140c031035031580080340155015501000782d1521040c210752101011200e141e00501c0140d020042048020f064240500c46032040d135000300f12627226000040f042d654030700c0a1300d40b1100c15038280304d024400b010521a1506203501301001c1e507920702804190500c1614410480440c06000383c20b070b18403802907000da10522030410b07410b4014980c401450907028540c0244104003012031443e02810011080e12190b0311100451510702c01082c02424002c0c074900300f010b80900c012003041c06502c080211003111500c1c4c040d01c035070402e18140401241418184104400404100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 762500071 1250 762498821 762498851
    0x51911061f09020c0a0f1208131e1401140406060b1c0b1302070b1b0f0f031005151b01020a1704050705120d0219030801360509060604 59
    0x202c42c9040c201603140c5030740d400601d040a28103070024004c1c0100c00c0d081d10800541d4828185081240d4403000030548a01010b40900484560000c02100c0d80110306015240a01c41c030304800d911805a001d45031440302502070079910501c034115020100030040c0310800c40c0070700811340503040d00c8510b68142048112405d0786003038000c9c24100d0070b41e03075904c00000b2a00c030724140b0350454150710401d42d0b0715806ea1a0843c0080c2c000c498010007280c0828082381074462010444000c00819120103051440008210000c1e03440a00741940c40c90059000285a840c7c05420300c01e18198500c0303042c0ca654001100c1c0808491111003c012070b4030400c10080907980080d0050113035807001400e4245955640303080e514002d0709401041d0700803a280c207a403114003400103802d60803803000c1d401d4490b101c00c0400c641c15542c90004004001c00c0c0200010300c0600101040701d05440300201c907a142e05c1801040d100b138000030080c04601c80c0c503210320030450750100c1000b290341c0020080e00c2c1000390b0720200041c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 762501321 1250 762500071 762500131
    0x30c010f180201020d270e0108100c121a0a120b070206040201140a0e191517060409021c03020304030618052104031e0302070f2405191106 61
    0x50028000a8080301049051128007455030300380041041300020f07240c0d041c42c1c1d014402441410527604c9041850302240032075000f040b83d002c01a4585054100380c00d08540d000d4005e0035050f40c0b111014103050a91a40c1d6120f100d00145240303105e04090b940c060a1040b41140018039040c1598003901c1803000603644444442031101c54a0801c03619400c100104940070902c405c0029808550303000748600d640b541d00c40c0d00b005c0301e101078100484082f41c800261205d01a080142d00c001060000140290801e9001503080701e100a000c2211981d81e24a0b5040035422a003090340140d001040a0080254910400c0802040c6448143c13040139243e03200c907502d21801d0032440b4101d03032004141242c01c0d00b103015030b00a50b9010420045003409500e4111007161200c01c107a0062241e01c40004120820640c200b0a80c1c810302d00180c100d05454090803103041c0c505944404000b410800407031241d0a20302c510001c0346040e640d142113803003542401450712501030040c0300350114070400c8800b540302c03003800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 762502571 1250 762501321 762501343
    0x50c250b060108270c0102100e031b0109050a08030114010809031b01060f0303110d030203010b070b0402030c0901140907030c0f08060d0c0305160f1a0714030c010f18020102 76
    0x80081580c0c0c0e1a84200014041014407580c2c0c01040075640211321004900d07910812400e07421607000d00106a0118143c0e0210000350409820402910b07900d0000822801800304582c40049044407050740d0b5039252500c0d940c03054408290110061100745000442c0040f01030091030070003d13f0424215040e141d2044024041e8900603500c003130440c614081d04000024200504095521507490402414100310302e1207081d180e000c1d0210402b0a43e001c2d00c20b42e13059624070800d2909044061744c401c1c1074104041c0082c0d030b141c030440c613408401c4d640d209200c03406003003071103025035801002c0c0085c080e6804002c1e1040040c14103040a1081c50b46e8011612203001070b40d450044202d0b290755012232001030300f0200160024208031404001e200e0001403880661500e54a241482541c2d041042c0000b0018041d81600d400c110401411562003040940400c5010b060038011a0072078804443c030790341c03041d81d000b040380e515030500848466252040c1f4102c2c09104900840d54162540002d4a0300c0f041c001e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 762503821 1250 762502571 762502577
    0xb030706141602121b090c090d060b060406030f2d1109031603020a08030304021305330f0f061207020f190b060103021c0c0507020301050c250b0601 65
    0x268000c05086503100410b5110740140c4044031031007689985036142d071150b4101d41502c541c15040c2010504008181038400c441a04440d07082402d00420001e00070807841c01030301c1c010348941c0404216619040144000d107129140042d0312180c8034100f6007a42c0d00c00301882180e410b9440e4501200e83c060281c03044001305000d0000e0455007050144a49010b4035440320b07058481c03418081d442d040001e50031002c0e40e0003140d214050780c0c0c0d500ca446603644000c840c02034010182d07500041c140c3c0c03200e03002a90000c0d0802d207441400403501928039028504540c141b030300c48152480440300c0d0300b0030505130501d101c402e607642601c60030054045000d52103440781d01e0f03030060240400079140c14800e1103100070302c20600c810744d000e407141c4001101c1d074142120f00954400100801003440e640c0280700321800003841804c0f6021030114111a03000614002000030f0174824100603400040e034080c401e05114a220800e5203881c0d4040000c5043c0301603000c000400b03580c0d1032111320700215000c40742050b48110246 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 762505071 1250 762503821 762503827
    0xf07030f05090c2407140c090c0904230916080706020a1b0e15090601031b0c020307090608030d062111010c0609080c0d051305061e040b04090b03070614 67
    0x4132005104001540c003041c20305070108240d000c0021a07001200030700c4110040303500c1c10b0120000c1044200040c0c0c0c900700002001c1248140703508141d0400003a43c034018407250880d0000c0144100c21020482c1d00b0b02083d0054900f0964041d60002918080d0020900400b1a14100800a95150110380d00a4041c4062044000902604504e918041d0070220000c54150801c410302101d080c1c14a02210700c108814000070f40745510070f01c1010701c955445210000c2d0000030002c1a642c8101c1c8890070390301800b6000c80402c2d14840b42c0501001055040001d40e5110482113804040711581d800c1104d41e000002074010b0943e00405045051503004440b240d081c000c6540107941c1001540001411a801c05120320244080a80501540342c40340003503820481c00c0380d10882d4140b040d40800e0303024680014044c095410410040c1c808103010340e001c201600c520180e5440260001c0d031000c5c292a500060502000d6040d004d48100f1340000d40c024040c09081030009017070480d400400000300c00d404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 762506321 1250 762505071 762505099
    0x30f071203031d01060312030c0302030c070209090717031308190b250f020c0d1203090201021e0f100203010605030c03090307060515040e070506040b0306010c06050f07030f05090c 79
    0x30302c00e00f50600f0f0b1910001c0000d950760707140004402035041181804a490008044040f50203070088078407400008224600e810940e5003000800d040141140c5c500d40314458000c258a00c811403401e03c3c0710b03441c900540d112408070710090090040c1d50081c0c05660400316074210150130110505060503030041c2800d82c607503109030381a15031800313101464401c824100d088503c915000000680a400c40d80c0c02d4a02c990041e000340031510070003900041004182140708103640c0d101b54040c20000748144107440165030341c10950078080e00c01b401d05802a4109100b0006200002c100c82011858119020343c10b640c98518094080d020080031035012040000000e650480f080c01200c403902d522000821140c245044021401f60803c4240c0d40143d00d40321070743c00b903508000b80d0f0800f110001010b0901d801e0030702d4441c440da03800113081b041c14040030400c914002101303030160070722942065810740c001e0725001e88020141d50032050061000c500c0c11040c00f40c0d008000c66003064061068544181440031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 762507571 1250 762506321 762506351
    0x70c05121c0507080709030605150a090c030e1b012a11010206010501090302031207020a050315070216051f02211803071d0603011118030f07120303 65
    0x5a00300e11414000180d080c11002500200068155504820405a6a603402c2070740e0503082078031400b02044501400700001640c5030042c6910104500350040c6060801c0017084440c1d0f0290045140152600c0000780d0f0580c0c148240070a00010f030b0b0080c0a00c2519081852100c182d00002a04014014a6000e00710b154440c8540c060740c80f5403812015569035052aa130760302034110b80304e17006024201c0000360b1036104000c44400d5a4009001d00080040c481c04484a03a1028108a030840b0080c200018240d4060107402500b142040300c0b0b0030b152911410003801c003038420032048503c001110003031000b80c03200c2c459030140b0004215500b1405480044c203902e003640182e86200e910b881418811001c0262802500c00041400b82e070081107a40d0008041d180c196500421450880c0b02050041c01c010131390354950016805800015040c8841082560319070200710380c290091400c400007035990404100c8454400007d4001e4845213042030a000c1c0006e001403005405c00d51a40038910311010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 762508821 1250 762507571 762507583
    0x10c110d0b04050105060103061e090b040617030d1404080d201303111e13060b0d230603060a0b01090839060d0c271a04030b070c05 58
    0x5000707031400c00c080c54946415030190404803401c600113800e20800151225a00ca906465115001c4404903502d00307000f02c2d000104170320681c40e80c1c483d45032035000814603070250043c1c0904141c00b000c0d60f900d00624100409646568040c00303400704031034041001244954003075a40c660141034001c1080d044005482001c0c58000302516a00c080019a460002c888044480c00b102d104902001c001d025100070401c1140306003251030500c0a6296200b001450f110014000030080904002a9151550309051568008940c1c200a04d9a030b0503407a80c441029a03040c400f03120003580d440702e040c039080c1e010a81b200001b1305014200b94031640d0f10b81c010380c011513141c00a070207604210b41940e5112000c00c60211230103210f03502a452188082085100b45c0584403100641c090001d51801280480f014001c1c00310030307040001c100f0421303036001c41c170b0940c03401c5042e40b0403469a400d200e184c2040e0110070203031a00000d05520410800040000590104040d45e001d141c604111507207000506041d41454 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 762510071 1250 762508821 762508823
    0x31707050421170405130203090a020f0a030501060603060e060d0f060f1404060c0318030801061803050d021b040606020a0602031003050d1d0130150602011b0e010c110d 74
    0x703900003840d5186060343c015200300c910480b03008114160f20f0900b20300328801078440c007541c4e410000801c8094103141e04407100020010704001e00c0d99607a038a0b0f640c2141c0c095007103580044d17140e110800101600300e1685400000071608550032071125620340700c500c109510f004244944490004004140c00d502100c0240e030604500000da150510380300c0c004024100f10000400c0c60040003600420580450840182d455240d0b0071103642006000d403042c440d103421200000301e0442001c0f0024106100161540800341c0041a510030340e222001c88800e10460720500440c6010400c1100c0c13540000c1c0d0520b820f0b001000140e0f203440e10084040071800d903400180583c451041454586544201000704d0801c01400c1d4088042100c001182c1220210310142c0c8410100c517580b41c4003402044c031490035202103010003c1c7e00104150008440103135036100e0400350350745100465104403503000c030004404880c43c1054611581000292507044c003040c026002a003900240501500d40b0f1400d82c7e001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 762511321 1250 762510071 762510083
    0x190f170712050c0d0f0b03060a090512031b0408010903080601030e252103091409070e040b032d010606231606022a0606040e1606050304031707050421 66
    0x4450185c2c4103170280104451041c082d00c40d6000103425401d0600c126411690300070081c0030a03524003280040c95402c0034104541c0d010b41c840040d5989483c2000810040c0150b40000c00c41c4ca581d41809402c80c2c0c001850281403504140d104400030102061510b050071410b941020402807508159001103200d400070403580b00480d840380c91681203000400503540c4a640d8000d0210344500c0303842c503410000b13968941c0024403003000c6000103004c0c440320300d174a2034080c00c0060344007540d0300021715000c00c1e00a14030206000000c105103808042580c9030030209110000c0c001d442c035004005103000f00c43c1c101d00000c002d520240c41410f2041d4800c407443d840450103480c3c016605030a109000f50b10686540005440003283c2100800c2e0761091909007101890282c0415600c690070b10001d0f02610310020303100e000b050034002e400d06820000d0005015640c0e030b1581c0342c0c81c1c10701d4083c103414084010450030814070f10400400350341c00350841d810b42c7c0080b601601201c4000d900ea01924028900003891 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 762512571 1250 762511321 762511331
    0x118200406032d20040f050d06090c060e03010b040603051203040212070801051e07082805010e0702071a0f070809040203150f0a030305071403190f170712050c0d 71
    0x122503242c014950100040b020311408100c0404d06454500c6948104040306a130000708200d070b4540301c2d10074061180942004a9400429660340000002d1900b0000109528108a180781e0409200701c6102441c20346081010034155281c1d203694034002e588070b0281c20310000c006411501d0f050a42a486e10200040301c1030300392601c2c3d060307020380b00807540c0d0030110801140902d00c100c0c10200150080030309031103400c2a6210381380403800b01d9800654003441e1060000c03110743c40303e40324810f0500071b04c4010000d6919041000000b400e0400a0388150702c03d84180d4103541e8045505c0c000c5903801d8120004080c3e591105182024440c01104103940d8003070706c040f0400c04408580342008000c690100e8040c0c00702d801013410005402a81d00018000460a0010500041d070f0040038018207082c00c011030b401c0052407505000c3c40c809000c44800041d40400301c100c103980c4c0081c2c154450340088007040b180c0346480d1a004001003407914820341c020361500c0126011000d1501241c000c503140b8141484 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 762513821 1250 762512571 762512651
    0x2010302070c090504051014060405041e060203040c080d0207060c02011701030b090d020d020714030304052d030714090a061e1d09030a050a0201020d05011820040603 73
    0x402044400380e54901035019154511407407880b8640503902d10460000041c0c80d403d007440000d00d000cd10403500c058180c120200c48105101c05409454401d802c00b503604d00e05480c201c0c2c0c0140c4207500400c0d042e0700000d11111120703008a1020140c0d8810700d00024044078030700048070286000c404084081200c0c038008410701015203500d52141540500b00e402c803040760301c82282e6520071f0050707500058126910070b219210701514100301d984002012a030400f80c461000031039030303041c02c51058001220304103e9010044d41100d80020720100f01c000d8a843c515010340500a102d000354143d2040c20804002840d0f801d10394005000303031001201001d00907508502c03851401d0380d58003e00710700c0c0c1c921050b080c0b0040c2c90550100c1c0b2400e41d61014500b01072201905490715008415141c06654081c040d0b02101c090600c00d950007088002d00c02905403034243c0c615400c49040302c0b10301c41105800e028072101e0894207812641203078032600c4e00041103140000002c030110143d003000e1580c010109000c007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 762515071 1250 762513821 762513839
    0x1050a0c1a010e15031908120f180319050306040207061a0315010b070303090507171e0a0f0b130206030f060901080d230408030c010f0b0a051c02010302070c 69
    0x15058501c8107450040e25119031140800c0000207284084d810382c40360400c1940d004105180046d41b52040008a0400b00c0e044010b0705c4c1041c049030b80300394080e0040b01b00050b1507544120982440458805141f6001c010007080d5400b020a01003e4184800080410469244c660448400b1078210034100b003114841150300c0301500601050034800e1141c0c03003500c008070003a044454100c40703039074450034500f000c0d547c2c09802401c8085001e41d00d600a0081c000b4951000030b141400744400800600101c018030440d0040c0001141c42030308550744011b07850400a1146d2000e068600d8006c03042081c2c9690303c0031082180e81114000a4201d0b501006000340d81a022110b180190002c80700f5150356a00d40c10440c0da00c012290380c0000044840001c1903d8035a6030386000c0c06c5600d211001c601c0c258a42011790f1a6902145881074580c1d034070189201404114880d01c4c0105400300d8001c1c070740c1803078240001c9410f0900084001490079a08a03041160b02a50480d88810392110754032031540e035201504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 762516321 1250 762515071 762515123
    0x7050105240418021912211d0f030708070b0702040e0a0314070215040b03040302100c020304090f020405090103051006050114121503030d1509020901050901050a0c 72
    0x11280d00d54036180c0844030300d4a409032001c40ba006824100d40ca01da10b07001c00c0000740603846004103d0000c10400300d081e02459000140440c0240e940f07002c0c49060b01300c47c84400e401041d60b10100504100c00c100f036901d07144000346090100300d49042250305490002400c0000c03640c4842450711a044002580000356405828030034021202000540741400d6010b440f00180340c07000b030015800c2100c8043c0480d408002d484c00c940041c101041200742001031000c2d582c4241c11400c0341090200c1000101a810050a0a00b02035007006009002034040060366a0190b402500700307a0b52240b01b101c280340a1a4140d03402000014840c0238076581d039082860700e50f9100d000744016103041c4907021400d54010342c084410501507441d61807421440e4603441043d62000383c0700c000000303c540c011004039030302080542513684000380000394140780c481c0250754502081d4850f820032401801304241503a000030598002403801e0030560ba40f00700101b0215410042d801000f004610a80c903100395000fa50880 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 762517571 1250 762516321 762516361
    0x1110a0903051204060206010501080406180609020319020f10270302120303040c0909050c100801080c0102120301032d0b06010906230c1207050f0d0f08160507050105 73
    0x243c414080c54025241d003184114007802000d64844001002035500c512032040d44903000b0f9400250140c40341400c0c5842900130081900c0c06601e0f2007a10303055141c00c0c0618110075450200c14100d07a03855602040d0030b85049410340c2d100d5058410740080311800350390251828a21406800c440790001c40289007021194042a402030b1442c8044611141c000406c880c046c640000204250514015030680544030b00c410403103040c005c006107448103440d8030401ca5103412090b01d440d0aa5030400841d05d150180b03401c0340034119446194801007842c5c407403003200d0660b0b03003007403d581012002402c102909c003524000d000c2110f8502d070b100303820700c040e0103030540c0540000d0761181c5005170340d05400c4030600e4540c20140078005000c1c1800c51191800e40c010140500c60205460140c101150743c6032068000345002e40e0240c10019082504440510510603400a281465078151141c6031004145010003400707118024451250003012501400940318860b43c000002d018515000072280f04800324010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 762518821 1250 762517571 762517573
    0x1060e0f0f07050f0f070303020705030307090e06010f05030a051506030903130e0603033103060f0b18131b08010c030506150d0b0a080d050c0c0a030f1401110a090305 73
    0x110b49240d00c5501161340c0409007025840c00d14000c034850810f243d0000c0004c50a250b420000d10700000c03001e102542c4a0141501c2c0c08600030b107841420342c08010010702042c1004143c4028218841c0c00c20180c03030308281d28000c00a030954803200d05aa803101d441192641c86100803080105a00001008003607800a40d0a0002803a40d5602c1d03400058000340ca810358540c2007030004c50740c2c155160b505003c0d1814600c11952500d040740d4481000038029800668040b078440300b445015100350301405c4136500c4190b03108a5924000c942d0310352a1000a418100524031031126030060180400d240842d01400f1904005a00d507600c002d14000d000c4901090301080c223100003d000b1b0b113000d125450400c138a51360030510b840100218100208000d040c1c50f0345c402c6003c03902040c212010080d003101c075203076501c4d42c41c2d0780d02c0851a168906500302e6442f512410041e5010b01c00520000070f10030016500090290800442011480c0507007080d0840c5a01c0b0308002c03c01c0307003206a010942508481c0540 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 762520071 1250 762518821 762518851
    0x310110f070506241c06060e10080c060301030c1e031b08150f0c0c100f020909151813050a0c1802040b040e09070807030b071e0e040c0201060e0f 64
    0x4040742c0b480b007206070b00345a201c113002e2a042c079240c6103002e117445803511403500016159192400400c000748142c0e046c12014004000510061008000204540604032036103811980355070782d0a10009a03902420f0100c0c0010758904d01500c540c448504040c0d03600c0b4248501f03050f1361441c202d0040c2700c24410703a51144a0002c0c182e0100d04510501d5015104400c0b4a004aa07200c10900d21030764001e203014240e40c410010030b280c024100e1b02c150888909410300150741c80c103101003001001c500180c21041920041c000250307417a0782d04450103519913041000344080c2c3e55541900c421180c910480078080d0700071900c00c07008108940c0d0000c41a100000f5901c2c0b110705140b02040100d025601071440740a50070482031100344c903402036455108104800319840f46885540c0c2e98100f0076240d00031140400b0380401c0c480d005030003014041082020b8203c81c400d450340c4d0720001b85040313504e81d5030f280a596940e03e4200e803c2c0c401c0d0407140213040d020112aa040c01c088010b140c90100455113581418a00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 762521321 1250 762520071 762520111
    0x20a05060a02100c0216080a0303051f12020f060706090525140d021806150c06072115180e0d050d0204031703090f0c0310110f070506 59
    0x25039140c22090b5009140c040101005400140000c02016041d48186184d80e58203668000d0300030090000b1001401025800746000303015248090000c0d04035001d0fa401c4a070410301038441900844003134007644600880c4500210340118000d80703007250080d0000801d00d0500896030030001d0454841c10465262400728070601940303848440d2041d1007603040a20800c010101c242400d1580c44004161003914000d5500060307886420494802c4c1107020181042501d00e803000d44d5030000c0d20703500151454500040c2e26592130300e1008214a0511109084940300850401d044c0c00e1145440d50082281c0b1100451807490300c0c004c1d20900000e084015020f2115042901961140b000c015005180a4624180549440c0c110034030701e14407180d00b88030000102d483c4000304508440c00500043e034a04043c54158100120003c50301c0301540310320706900464500060116070403005007400075240007900c640e089280728203911034000300808507a41082c090301180403805400c912071400e5649200f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 762522571 1250 762521321 762521329
    0xb0105011407060209130519140103080322080a05040e0a1104060c060e0d080412140406050a051c020909101a180d050c0a0e0c03060d0203120f07020a05 67
    0x145180140700c02205200482c001410354024090100b00282540e20f41608085040700710743d021120072039000c000c020b00c3c8904d06000d10a540398038030324409031007445d81961522a010b100203031030503a00e0000700b1b89001d0168554210550f41507405102c09a4030614090000c0480d00280170325542d443c18040894a0651580319141180d0301d92079015040c10719044054804a8007224169442900e07a052044070341d10600100300d103000952544099400c0609010300f514907082c58107020302400c4099a4198042c4400b030b20203d6007149042566540310355400c40d110b001d01c420010358901c0302800c000b4a0f91142d005040754400030b59000500d5074501e403404081442a20031220503d01c0d06001d0a210750b040001444115070002008903801c1c00e58000c1503441c010224140c410b42c00c840c02e009400d01d03200500c3c4008084031105035206040c010ac5101d90761002603c02d600c501c00c807a1140d0110f4605201018020f20111550351301c48015100e480b1340f075031202c00201c1c81948800300102c3c282ca4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 762523821 1250 762522571 762522587
    0x614030a020312160f2301141501020c0909010b040c0c0b0c0306040207020d0b0613090203120a1403010b03060109050109140f120106031b081f050703020d050103030c0b010501 77
    0x2070010002c00303403402c0a000b603520b503902c0b030b61071211244500505070380030611842c142c96005e881522002030b4650041410841881261131800380d6134188400d410140e200410f00c1c980281c0035070303440002032981c0c2c00140e207001d0485000d10381003d0b9040c1003003141c0c841980070642e0503800391070901040f5000300c0119119040108010004a01c20300070650100c0440d024690081000c0c100519081490f0002080685401c00131580076000750100a0603080440c21130020141045c02484003d03040d60020351500c0390a0428034040c0008216840460300c1800031420300006119030315900d5850f51503281507a4002c03140c01d030106052a030b0000e0300b0352160074a10704980c41203240590b20848142040009544540155802445031442c030311680001c0c072406005510520a0301c944541c8001c4403601c10a80d80c0c0240140e030448620544199800d9412150503a80d43d80d0001d003c0d038660809400034025038090710465403410001004041e0044822a40c2c3d41c000c84034003045a84c0c883c01111401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 762525071 1250 762523821 762523823
    0xc040c080412050c07050409062c0d080603010f020a0807020c010f080c0307030e010216020406090b180c160809040509010e0c0d030e182205060f0901140a0614030a 72
    0x402c9240140e00502e100d0340203000041000e8081d00c481968a00024040d2028a0700c25621180d42c2c01e21010250401c0180c03a41800d9000314010150148105a584840c120030115091000280c000707845079500f94085c0f8803818061404648a820351000100841c070f04544a4015205001034040700d0f60048840703000d060901e40d50b0100d2070b61156171100143c0c202a01c1d1009040c2c50300781d00031217008280080d00640c000c44070b48500010542c0100800e660460384001c0881d450200c81c42902d84a2902040c1c005100940c46801500c0d8140d00c0c81882c85580801b59409060303a100c0010448040c0003407000f80e0046506200e5512140802801c941c20019180b9065202184100d0300c0d05000180401c0a8028145045003420000200d1460000c00000ca01c1180c00401044000404040c91411842400c94070800311000b1769110341d07442030082c07c0a01c04084100010380c0b0140250441c440070200d14054810034200b110603203018042c2400b540c0c090410038080c641750341c2400101d80d0107103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 762526321 1250 762525071 762525083
    0x90a0b10021f0c0219050d120905030a140408100227090601120204030605090601150813030e131d01051f030b09120c252d170c040c0804 60
    0x9079480c603940c400030042a400782e0154017032000c014600310541c0c0d2024511034041c00190015082841c0c00070300f404d00140d8410443c81c0303040c548101041002054a0327502a090500e90308254a580e801c1e41c6c1030081d5400f1810750711444076103c8200201d80c010b0032000d01c40302540c81300e03000341148045050141c030040036008110080050319640c4101c508000c48d400440c0c00600c0c1640302c0e10b9840c01d540e402c4034604c44640c822030042002c080054800d2000c00c06500c5d0442080c1040c000c0a800108041005010004003081c04001035842c80000d0020038082a001c01802c02611403011750a82e919101024075460140010440c0760410303c45071500c0c5054030801c20b902d0540d5601500e410300179000b00b41600c200705c0a0410b05d41508002c20202034048010a4642e40c8061040c000400230a113215100c10900400c000d0240b68080803014854000c04044082c0203d48180111428680c001e40c02d103d40d006c0000b00c001070118100c0740072402641d080c4240031042505480700e0360103903001459 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 762527571 1250 762526321 762526363
    0x141203090112230402100309152003011d1f030807050c0405011805280b0f0a1815050f21070312080604060303140d0902090a0b1002 58
    0x590700c51191a000350800541c000f844803180c0016103c2142d5021002e540c4601190a001c194585166040d4041d1324a00e07003403011310401c3e945c500300400100064014107485842e02501000207540558044a00f41040780e04e80d030751031030110948a420310101741041842c0000c20400301d140c0d0f241c4d5000d0310071003101e440c4461542c0e403440d0007070f8000e1f6000d45450240000768800c0d40e440c0c0c043c1314000c00c008070355a1680c3e191441a48102c402c050040e00d49104000d0800e51015259260f802c0304191102c0c0019082d0035900c045005d4900034030850341e210b0f43c0f504004c1084402e5003d00a80105900c1040208603589402c003400902c0b2400b905500c0303c8580d0070304401b0301d003022050600310354503102e01203d0040d242440349841c009401c115150011450b800c4001c0703901c003d501c1c0c0d02080440e8240800d605d9034801610710000a1802c48041800090407540012540c102d0b698013940070340742074242d20f0300c4184a002003070000c001e82d00c2000f407044009802440040c84017681e0b804503040076a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 762528821 1250 762527571 762527587
    0x50a021207360302060304050d1403271c030507021203100b03061f05271f03021b0717060403120506010309021903030e0a0e150f0d0606141203 63
    0x1e907144810100b42640340b02024040700684809000d58011442400101110a0320400140c043e03910f100b001041c0b028140100b102c0794800302c0203082005854400c130404644542089800d0181c4100d0804084004040003011140c0c10f903c000e2180c032055082c1c1e1300c0c0e41d00c0001c5840581c80f0070745075071286940041c001d120391810b0000454119100a1868150000c40c00094202c1d400140f10b120100c1d1003c01c408081c1101c070f1003001c07110300341180701c4082003280f10001400212040c2c001c94030100160b82d0310007054002e42c1103481c0f81c000004450000003205241a81d91100c90203000c513900b0480317541540000740003c8031401150301d03441d04604070348203146600041000078074043c1015269120788025803256031b10340003800d4107001a00081e5046003000381c40b404880504500442d68000101719155000c81501e8004004c4214206410340890014025181c025403155222000092040c1044095444542141d0403061011145048801000000c01180400e41d5140c4c008001040c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 762530071 1250 762528821 762528887
    0x61c0305041e0e0106080619030506130501021e030105031005090303070507060204050604090f0501051516110a06120e1b01032c0c240403030f050409050a021207 71
    0x81411465010342000c0781c2c0e5070f010345070801802a84014003240303a03032041c8240390400500c115002c68101035083c806925566a4a640324401480d6201210340c4240040c00c010081d01250300301c1080bc44d500c40200040d4112180f5944280700342ca1080c4a000d4048040c0d9100c1d0080b1481005020040d6055a44d0b003601603d0940c007414040761066800c2002080c50b507038010241000e8005600300069072401e44402404940c8103800040c820784c1c1c52000c81e100d40560404072040305c8200d071440105c3c214649042030703019814800031580102010400300b04254088140d411035480b000b020f00c58108080c0e0605d4541c200f0b10050361050044649503d155402900400031030707031443d00c890f00041c012045080e54403c0c1c400d00c0c410103400040c0090000e04e03008899100d0301900010400304851812801e420608c1a03110003030a0100460451809901501c251030040c02034000911891401041020082d17100f00c07c280e401010817404190940d01c81d0718040b281124440500c10800407241c021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 762531321 1250 762530071 762530099
    0x91504020d140607033804020906040b0301030602300a0c051e220e040b0601140c030723070b130f0810060b280c0503030f061c030504 59
    0x5075141d951880242e4a065030400c0841d01c2030115913000903411b2400d4240400082d0000100206078841c60702e49090840c24070029032000f501200c006170345840304004155580a103030321003807a100700440000248034880c2c004105081c07a000c00d246040d4103104e12210080310001240f004d10f8070440004801840941c881032403c1c00c541010303030801c2c0505003298071619a04070f200e00b21000100722688046681d031981c250b500e114424001c920b506101c00f07080c1e000d40050001d040381044201090141c0d025400c1e00c8803101050030b28607034a070034031090780b550f071b0380111800c40e601c00e81440c500030001040701c00b002d42103040324090110715103400442c0c08070360010202003000003020a000108044003000120050000070060318500f1800d2486c902100c04c0380d40201d0700d29100300030ba440d140e000c102c40e040180c0c0303080c0041405d41282e0001100c5003580320310001c02c14400041030202401d49441800e00c81e0740c0c222151401c40c00404c4484920b164071400007000f1a0081c001401045490011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 762532571 1250 762531321 762531323
    0x80a02040c0c0605070c0210050915130e010e010312030b0f040c03061d0f010b030402010c0b0709091a0406060e1806060904060308031b0f04030807020a05030106140306091504020d 79
    0x1000003040c103610350f07800700c0d201030700e0500c04100101c0740d840845c24110314035003000c0818141642031017a103001007503e882d040829400c2604000915114000c0400000f20240000c1e10516500d51784440702d10810920a000c281c0c1e002c416040000e4006210b8004c00d2040301d00074240d0410004124244009030181c100458141905c5420220b4500e814481a0744d54001c3d951035803940b4184200054004841a00141c031114020000c100161741c000c0002c0b54040d5100752840220f54800004407026452a0822041c0c5030818a00496206c05141c0145141c181100d042011a903500c4094940c42d03c1003a046810404540129031017a4240000c554031400190010f880c110501d0009421138105800403900e114011091015011078100c4008040141601d10f51401a00551a0741c0f0f60040b8803000744042c00001c3e141e0f04548075000814000c1c03001400038440f20380c40303d00c0d0590020071912041d01a124801c0003c803140c1c070000780f88404032911030454005840d02c0d024002c0254000300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 762533821 1250 762532571 762532577
    0xf02011404020a2306210108010b0906062b0f0b0103140105300304080d080603120c0a0606090c0e010507020907050c160e010e0c030405060610030b03010e010f0608030301080a02040c 80
    0x2000c044e01d9100c5000405448000140b0040c20418403c01c20107034a0040e004041c090385040710201c01501c4942913260041d078111021b6890781c0b0244030000213020114101c4503902c0400c9444a000e440b55000500d099a030900c01b4851500100011802c40c2d070800344100a80030b128004000718107010381c880c41a401900085c080c00003080340409079243c1200101e261980c00080d00308940c00c03041c030581c190f541092800241d90f04080c0e00095403a4060310428185040001d007527804000b0402402400030f510000603c486691149400c00504583c0640c0700428164240301001d58814000c80d07103a980d0003800e40703160344c886c09011601500850040304041c80b44030543e1689800c00c1c0c0ca800d000740440d08407030440e981810616006402c001d009140001d1040c0300340400103a000c290703140e002c0c1064444d00781d00307042d1803070803000740805010643d015480c20b102011526010b4124414001001360103001c113507900c030f040360368a00c0248604951500517000210051600307402c1a61504074600d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 762535071 1250 762533821 762533879
    0x30e01090203070e1005060a020c040525080405121e2b0e2406041509090302151518040201180e040b060103050108070302010503040f050d0f02011404020a 68
    0x540441e152503c650061036407000d6100800c8110380d24081000c01801c2c05072011400c1c80c1c0d02c0310001c0e58501c03082d40701500c6661200b000401030071822101c2241020040d0205025a010380d101500500c01614241d80c40d0040c2c44c91182c00400b20313000c840d43c0014641409428480440103903009800a203400d0600500b138200a14188800c2102e0705105618600b001030500d07103250b181e5103012221000104032124000e9111a00d5413002324040c0c2c0010103a5021801a203008119545183d080c0c1006424070f1074103503031000381503002a513009080107501c03042243c0c2d01c5408418411040c01c005041d0700c08190341d200503030f40b4603141c0d1964000c2d01c10b04145101581840003001c1c0300f00700390040c0c40e4004d551000c00c0305200c0c8090f04541c104000303080420072941042810781e2074604600000e41802030000101e0100302d8074643c0202d0b416000030545220220101300102140c0d08007010700015801c7c000310380504d110324a0158000c0c0c2d03000342128251031401d40c041c0340496102120a80f402c40d40307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 762536321 1250 762535071 762535073
    0x2e200706091a070f0201140f0f0403031b0509030c0901080604030f050712030c02010b120d051605030307210e0d0e041d0c0a0e1509040f0c030c061403130201030e0109 73
    0x40740c2000d015100f02c1c2c0b20001c220160b044002e08440c0c580c4454a0502020024484a0b00c6401c54040d04400318256030305240c0d8440c00d096024101504607401e425500d80e2851440c0c41e4030401070032880500300c095445c00b440343c20800540080c00c1c0145459600040046030000c0e0140da2211092405402d00d0741c10000d5a80759031030701125240c19140800e842d550352029840e0f0a110341c58005a0490f802000e2130450740070320750354400ca86290402c6c4100020001d0903035089070085031049501c42c048942e2850001c0c0028030a0390200f5207482108070450710781c0c1582805015000d000c1001c94000e10320208a400100c41c0c0740211802103070070a40c0c0382440c03c5500203104004d080300816400410300c107240b101c103009280320564804c0f10001d0b1644103210305501c10500200b5844800c607005e00c0e0a03180c85c00d0401c504a100900208030b00b40402001017000030001400c1c4c216403581d101c160b40e1814001480d1060b100c01c0395984400e92100034100010b45c0260703c544075900e03890000040d41c2090b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 762537571 1250 762536321 762536363
    0x305040c030f1209060318020f010306050604120506060303070f0b060609040905062a03010b1b0616020c010806090402012001150512010204060207172e20070609 71
    0x5240e038180d8022610503c900748558010502d00d004100600c1c0400c01c0704100b00702125080c12542000380308d5201c400c0d110749aa0701c00d8002c50003a2900030111503403150f40d2000115a10400c80341241c0b5400340e040040c42c1032901009851015030401c002840302c40213a40e80c1008400000c02440c5d008009004011280d01d86110f1101c040d0720a0000b00618101044000c1d1340d0305000032400008080f01c1100381104441a013501d04443c1402285074442d075841141daa00891107110484a510a5400700032083e055a004029120815001c1d2401554140b00445103020308903007440d04101c0d5070022400652084809407241c00d402100c0400280b41e18a50a09440142c82c04460b8824078060902c001d10303007a4a85419100441c000714a064a4000c020351600d01900c1032009130f1103400f000c10040764042c054201c56802800090301204940b0135400000f25002c1080c103080e0785080302100c20090742c0303100f0990321000d0310b4031142001925034031440600b0b00c0c01e40407105085815840152050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 762538821 1250 762537571 762537593
    0x1090b010c0b1807140a030605090307022d0603010311060304110301050720010204081504080706110703080618010b0c1905150f10030201030b0103020c060c0c0c01080114010305040c03 81
    0x100007004541c044410f54040d01d41002c03900b190440c0310090031504c0460303a4200300b04084a5100401241590b214a081030450062880203904040070486e07494001c1062a12840080703406404030741c41c80201c1050103024002400b0040005c1e2454001440301e140c840007071540940b182003445030701001500440d0944106a6110011400d01300003895812401c107208030403003c0e48002141441d10b0b07c22059952900180c100a840010340c01047c14050550211000c4a0700280300f400b0000d00d10301384c3c5c2a1a40b2040064001456400c082552490324400304045040b00b200c0000481c1d00700003202a4a50017910b0420681c468174491054a141c8400e0301c092441c021405006000810310041440e41802000c008070402c4001c1007200b001c40e00c00c840e100742ca40a10f000280000c1010048e0000c0c0b080b002c00100e5071052004104074401020001c06040d514801910003c8585400554025100780240042c44410740030406855200c4d602055020303001e1502c01d03103415980d807580c1d40121 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 762540071 1250 762538821 762538831
    0x1909050c1207060e04180201110a050607080121050601060305100f080102070b09030c060705070821060109080102092d091f0f03111e1c0b10060801090b010c0b 70
    0xe0003807071007000f40b1904601c043c448204141c0d0144500b0080f2a07040181007820304c0000d0501c00f0944c84c3e2803002400b00811011581c1c04401ca0305c9505050b0f40150000c002442400509680381001444411140d011800225070010082420341d082c21320903409841d004207400c444200a101c0042e510020400306030051090400060f41c48840781042c80d5040c4000b0504543ca5008002018203168000741441c1c4c003a0080c94200c3d15402c0600d02085144142010700e81c179031420601610300c500d10140754901410090300c44016440c0d40f4541315083c4e0052440ca0380d485445034107a0303a02c25101140395031250209100c4240215108400654020010303241840c0e07610b0316519440914000c030101400be880e907001a400018a03580c0c80180048440b8030203802000c2c22000c600301c140f09e0048800d56031070003c010b241c1c500d40030802c030501c1084400080d1101d282c0d8401050147c000c044400c0207840055582d0307000d6030f0910008801410001c80741c2c6042051140c07003034000c900700d0000c140c095 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 762541321 1250 762540071 762540073
    0xa030507110906030d08060409020d060c02060a060b090d15320402060d021321200a12031b1a06181503070b0708030115081909050c12 59
    0x2810160400c011072094040001e07020b034002c1e005102c455a00022100305a003603502d0141c1e0590340b64000705000c0c000031903000f5000030034454150200078054001d92515406a42219255510b107402e00301a0340d034a11480225030010000c400960601c51045900c96003d40c19551075240040036040c121a400c1c0642d8010748103100d86071102e00c0c0100d10000c80480d090110b4807482c00c00f6000101584141c0e6180e10138180d0008207900d9800049108000420080c0380030b03106c04d154580302400d0084180011940103152151143c1803851689a0001c007920181c002c0e014503040072003c03506004000015814000b044020100303402e00d40000380c09030351140050010034603801150300c54004010f8080c40c0304410307a400a01840c422000603c0d400b904150b42c903801c209100021a080a09a410101d02984000340300814000c1c170500950488030189a9603110844210044604110946090701a440c82a0711403040c50300c690070418405020b2015500303100001f4000800c141400d81230091a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 762542571 1250 762541321 762541327
    0x3060108090d0210091b5111100f1803080a0203130515220b070c061b0e0108090106052211030903030405070609030807030f030e0a0305 60
    0x455a1020308150041601d03001456240004140a0f44070840c218000311016a5020200e0910845902101c0c014405142010f10346469400400d40ba0588905a00c1c4020a490148071032903038a04451000790050361400400d44900070b100c00200b602030000303d00308001c1c0380e17040c000c5c100280200e003000916654002924100c0c030b40741c1015101602251004400f520710030b60003294100d2178143d40006048001680da036504039002e0411006c1c1e0502030280c3c4122071424414040055070a8001c0400103040040c210070141030180114401d08020320705010840800e11140c011425140e6240c810180420b0342c040c034100c1c603040040c0d071502c4100000e441744070100a958101501c01d8100c3c00e0f0800900200782800701003190f1a1101828000b0f000210300036031b281c0c2d1241c0e4094943e4a03c180004c41d40c07800c1040031141e0b00c2e0401c1d60261b031203000f101030015071240280c40c00c2c01100e600c09010760520b1101c1d18155540420040d50a09054851382000f0004000340011031441d03109445240d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 762543821 1250 762542571 762542581
    0xc061311130903260a0e120a03090c090207020a14010e090c07140609070b07020d0203010203270303010e04030804060b210120040e04080d05011220010e1e030a060203 73
    0x855600280d6502c1c114401307282001d00845002541c85038002814a80800c4480f4400340480c60540d40131032074120001d001c04c04000f0154940c0003654900c0c02202a03460035612580c482c000c80c0b159600095001000c514200241e007890004bc04a58805050000f244911103020501900c0204c3d49840c10400001b1088100014982d20105101da107400407c401e00e403141d805661445c140c000d031a0a03a802040090031561603451340b100d0950302034000d640328100725a2000c00c445100d03000e00700c910300281a100585c200001070728100c5010b21601d0100d91034540b0241c44150303010300160707100c6071038108411303868480c0800a0841c103401a8811041c184000d540740c00c482003588000b021116004810300c18800e02e03c103031400c0d01c0d02039880840e951a20b140c81d42440c403d01c0c00e0340b4140742c00c21000107070060005803440704807801245004480c1110071085014500e039040f4640c0071070a60075281906081c21a081c2d4629480c2c541c1342c910301c2c5055000649855054070b0102c0f506a00082001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 762545071 1250 762543821 762543827
    0x9010b0a1509091d06160e011110060618060c0201080114040e010e0607020d140702090712050c120105040b010c110d0807051e03030403080a020a0909021305150c061311130903 77
    0x3641c000c6c201da0304407101080070760004080d0000701560f181004010041107101d00b00502c0b2900c0c180d6212803003042896034840340600120703d481c0414458058a442c0025454043c2d055100700540c16902c62401742c5c00c240d02e2182155500d4151078005039200c8440075080f509100e11941010540e000b40f41910300014000d29004035000e001c000c10120301c0f404620f1307103114000e66900a50444450318180d440306000c40301c8200108416030003908143c00d00401601040050800c54600760101805a03200d10034030080c3d4074260310341070010f0401c0301c0d8500404c4103405500d0740124000c00c0700e0319074085500da034052038101c8079040e2071540101e0191042000c10149001344044114003441c214505620701070003c6200400c0035402c81c0d000140c1c4207259110b00140e1000e44402d08085459405c0c40051045008041c0120f5002d500100710a1103c05200c000340c1c0c0e6851341040042c000c40d9110100c4441841012904440f200401011611103544030200409406c6900e1780008d24084682402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 762546321 1250 762545071 762545083
    0x1e1806051c02010e04050c090a0e040605150d02040e0313030615050d0210030e011508060717010803160f061e0b01080403080711070915050909010b0a1509091d 70
    0x34041c500303070881d0a00140d8102041072610b4070b003128001055581d20290729a180300c1c0c0020250b100c105da00000c6140c07501c8240c40344c05240a40d0041046c0da1340c0c49603c4003492011006683d1000005144500601d065040300c400c624030f0005903400d00f44480c00144800100b40c20031078400342c403003061071744082111551340010441150005002400e90700410f03424040e6288034420152100f9040800c00025001641012001641d40c201680d0f200036254a551043e40d4100010fa450f82d002403800034080340c6031381603c0d19800510310300b03000000f0080e000041c000b400c9524506090040300860f040c0c1c403505407048140c40660304810005a1840c080300c00102e4014188221402072201103079215085c19400801350410030702e10342c1c0c040840c0e07152402540c003d4020904000b412410b4448501242040f40d10a030341d0072981e600c0c0c80043c3c600b40e8888501c0e4581042884000b000030340f855040042c421103041c1804880140c890305001e00b0340744c0070080c0020407400714041ca0002c000400a07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 762547571 1250 762546321 762546349
    0x90303030f0603080f070c0e25110c060d1413050d0c030801030b070c02221107051b0d120e10030b180a110403050c0114131e180605 58
    0x820002c140c21650741d45031600400e103681a08500100306a0f0802c03254501c001c001d0329514580c41420703d0a003440c8011500e5208a12560300e65146411100038040c1d0782495004100d000034005c9111850140011a0000000d4202039622006a419003042d500e580d68010f0344418141c681c943c2c52410b00d1440c09801a51a03401c008107100c03c41d012031350141026065a500c02e0201f0004d48420200b150318400103900654400e41003100c41044480d4500608a01000124184441c00c4900d850340154010703000b0113051a0010700d0100c8000e4012807c00c0302c0b0500003080ca01080010341c41d542e60300410003074904003080e80c3e18480701062410305054403103844140303824041c082d20140070820120345403021040d146207610209801141c42d812088080740140c4440351170715503c0c242290303a000b601c0d529a0103d00304031400980c1c1d50760a4101d824035034685402101003842c01b08079907009a99040c00741481041c00c5408038180d8030a24554005801106002c54400c3c10103003009050400c10803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 762548821 1250 762547571 762547601
    0xb0405090706080c18010e060d0f0504020f040e0303040b0714070305070b060405060d030c06060b21130206160309240f02010b01090905040f0503160501110307171b030709030303 78
    0x807801c4812100b881c5d14401c1c02000b032074041e06100c410400308015001e5401f803650402d0030700351109140c0c4002e40c030243c4194002c0b0740c1c0022201100701804111501d11043c0d4600750410400540801c100404d400d801c00d4461810104004a015507152140c0009108030f0001d1030020b1034a060107149071003141c0010084500300b241d424448001201d4842559000702444901c2034040309210b8141d1080004004120031a0b81d1021021600034500a60080c4c1d0a644101207002c80c43c8c2e0200c04240401480e8050071240c81c01c50030800e000361f00b0003034100442c100031001c18040b0b001e00790b0400a100030107503030800d0603082e840c0c1c0c80054a400790f00800d40c1c085a1604410540c0c5a070322410500440301c400500203055243c0c0d0800210114a194000d4000d01c00002d04c04c1007058842d00c0e00b888907010350000c10400c16072200442d200e10003910440c2c001201c900140403544540080c55420a0310018104001d6070764080111480d08112040404584103600030414035415008440a0725507600c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 762550071 1250 762548821 762548827
    0x20d143c071b080c011e0905030607050c01050a05040c050d050c1905010f020604021509040f1b14030c03151201090c0f0501050c151009051311040509070512010b0405090706080c 78
    0x800080400c0402a00e544510380001ca1070040c036401f80c40e0840c05000050181c0e41c0034900b1400c06402e40d800140080340541c40c26000031302028041c0308840c056640041c080b545503107008100910301120300025120ba005d801528500380d6108240c101c000c0c07c0d2004000c03c11458100058064072000d054401550041820000181e032201d0000011030910a00c5a440d2245000401e004109141542122501d4540b42c080c1420001a00140600496584110004017201085810301082d035500591040c1800490404c00480082c0d20120038003500755200100d40348401c9081d101014015150b09405600501ca00e030341d010510030140800b0300f0301501d025122a0400e55844060b8040360810b8465000b02c0da0764198501140002c141c2c0000a020030700384810304981030070340f094003100d14010710440402c007410a03008945c841e801c2c040150a031589441c090000f151803a840340c1c0c100d9541c1e6182041c1954031889494080c20315203000300341c0e03207081c5540a044624040e00c0082c0182d028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 762551321 1250 762550071 762550093
    0x60e100b0c12030720030408060c0f1213080706050103030807020f1c0504260c0f0906040c1e0302070b0a06080714040603080307020d143c071b08 64
    0xe842c009100802019039480e9942d03401100c1c40c03009030811400303508001c0b01c000a8030320000050000d9074003000a803031642e1180003c2c5940c6100b10b4280c1440e18074184005819806500c035000c0c1c0c0070358500f9045100d001c46030303200082580190022074a840d0b0b50300044c420715900c4025182d10182d40d000418607030781c194100e141c5da892000343c4030410410340808441d425110780c081c0c5006000c002c954045aa000305600c80601c240c540202c17a1a01c85c140f0b00840601d4402241c1898002c040c000122540701c2d0b0040c4009407541d01800d01c14400202d102070a04510024001c2e80a0703140d44e001038aa10070b614021090f40005440d0700c9040d07041080c24482a1008613080b801c41b03580f0b0584108460260010801400480e400070348800700200800010540106980c50180c0c49a40c40514100c05400c0c009118007034601803282c1d54118490143d03800d0110608100640c0c08080403d54860415002050035480035000715003902148440b402a003d000050702c010b4140000030b02192a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 762552571 1250 762551321 762551323
    0x12051e100e1b09060a090c080106030b0604031a0901090c081b0415120f02030a0308061f0207051302070606090c110309090f060d0f080901021e0a061e060e100b0c 71
    0x4444615101e54900f901103081c80c0e441c0000c0b10005c0c00c040c039050100103034000380070340804800d10900e00800e04241401c405440d00c1000c0b50162a8001000c170b42c8080440100449004000d100d56950b6584000b1600444c10300c000b068020480038000b4103a194651344404e400c4401042d01501850a1038902840703503585034102415504400c00700a070031318031030402c426869078803203000e900f501031107032850149a44201d01511809094911200c0c00058020207849200e01d06d0030f90713006802501d000d00c00b500d00311446014038000c028002d810545c05844880031210030754820030310302c4c2d50340804944407070b001481580c446403142c0180d81824a4040071490610000b840060a0b0009c040058020754038105159001c83c0c000d1070707500003102c040c540560305038400c1400d6405841401303480e1814900303800b06140724240307040161403903445c250b40b014007400810300006403082d002c03c2c207405000d145208000080903032102404541c202501b0075001e05141d074000d0001600d04000a10709424 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 762553821 1250 762552571 762552613
    0xc070f02032a1203070b1b04090b0922140c060f04060e01050c030a121b08090613050a170c030c0c040b0405011d061207030803090d0f0912051e100e 65
    0x500070141c0c031b0f155926041016902d54005101079031b880d42c0803d02242d1381c0c1040d0f02c04012480c003624a00d806072520288941c0c152040c001c0c0d40c0507107400f42d40c400e0000d800c0a40620304854050121a20b24102d40006aa01c0c0c0000c0c102c400c1c112000700b02000060b911000070040b60b0400e003002442c10f24242c0d1050b44a114a0881c42d0511002c1d40403640301c100b817a800f16402c050100300d6035100e000040801000c914094403880454821600881c10b0b5076908000d0a042540c4080204029251560781042c08182d14107500603106041c8508092030600b8002046507924040c01f82c0344030318002c001c00c012100c0c1090441d00072440c000061012100584215581116041c4205410f5803090000b40040d24a101340d04524098000b00108010401000e5405a00244291089050100001c588501c1481c125000040c40700c0e504200000c98015290001d2340603005403a504882e06002802448404009102c0c55020f03500320055001144104a80ea03ca40c82c0036000b00c540f00311048401e54 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 762555071 1250 762553821 762553823
    0x12020c0604120f050d1125060f0e0c09040f06140f01121104050a090507080304030c24050d0e0d0906021501080304051c1e0c0602150c070f02032a120307 67
    0x540c1c40c594455580e40c0c040540308200e40d103411859001f014842010400c506000d82281d81074140301e62114460280d02803515a10300346002003500310641d82c204080700358058403e4480340c0f07207140417101180701402414080e51500003007859500b44009100c8101d041648002079074014030100c0c0000815034140c03464008821100030405448111003600208601c03180102944030311100011b2282c0b0200140049a000305034109401c0d5440c05110354881e010340d800040c082d80c502d17064811500850140a400080c0040003620f507614000c418609060070300e078007001c600703101401c0101990401106117001d00b10441c10845501d017600503640c07030080c0d0103024454410143c01204201032102c02c850881d400c107201056040302d05039a1b441d40c8a0811003070302e410600b0300021503c05d00000780b00343c81380c600f452221460340e108140c046594029500423940015104041c07000350743c0400000c848603100381100c522080103000e2420b015122404c0071401143c0d5494810541c3c4804401d880d401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 762556321 1250 762555071 762555097
    0x309080405010c0201202a0f190f080309090901150612240302010f17041e060c1107050a080a080d02310b0322020112020c0604120f05 59
    0x5460610043e034180d11820300d9074005c5180003c006d4001d0100013003d100d0881455071008140d0704410603035840f62190100507400140012015005081c06103221415451442c80c4076038650719580a1104600c003a0302800070b950000c10000c10f00d147c8407080c250441d881d80c2c02002011215100700c00c48170500d03c1003809114400e0401e102c000303040c0d0000120f08098401c07035104441302030031405041000d808140d0000d801c1007000c1e0000e50180b00b1072001100403007078105c02580c4542d0b03108840032005043c0046122900320501c0060b115000d060800c1a042c2c8981c820542480c80c0c05141c44a964005441280408001c010702940425203600300760b04812170550741c030070b003200d410080d22076103080c20b80c0343c1c160502c5030081c00f01108111801c2c10031490f00804c05561030312145468003041d10301c00340c01c0e0960300c400048080030100e154180ca206040c10508030060701400e80890700400c20321011b94200c2d2040004004103e800455901c5c02410014045454014014540d0040c0100d50b085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 762557571 1250 762556321 762556337
    0x405040209070f0e0a1d01060206070221040e13060f0b0f01050c0c180103050d030c0504060f0311030106030f052203080714042606071d130207060e0d030908040501 72
    0xca1445000300c00d841d40400340c240c445d10ba03a12031516410914800407440d00340130010003c5142072010402e9070007191264001e0010142c10300c5c0c40c001800c0108000403000c00c040000240c460114848a449840342c5118110a268242010800c0d9980b10083d514032500e0280c00b503403207507070741841c60281260038039100c6c0d1500955020240342540c2c60030840c2e8440c071040500a24820014501810307688140d050386e520340c4003200203506581e00205c905c00422403d00c002c0c00704a1264044040250a03403901080800070803071196041c0d402a0230400009850380c00e0001954010302134a034120081440600200882d21401e40400203008030003010403c00c0d1010601840c41002c0d0600c9c00000c0d01a8181c0e116034401181280e00342c120060800c2e81481c40c04440c84140201d001d034420202515070540095840007185c4060520b28005640b0401030341c502d04201030148041e200840c80b0b20b400040c1002004903042c279055035200300b1403c040c00c005d010070004000c03000340c0303040350703020300306191 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 762558821 1250 762557571 762557597
    0x10e0d140a090e0906090f032502010c0b0c0a14040f12080c1f0c02010c020d1101020c03160201170106052a100603030e2d240405030705040504020907 66
    0x10201520f501c0300283e07003146010b200348418046282c500801c003602c101e900c402d50502440d51a40600103040d500d0920403410004007042000c806205140305260a54482c042c503274802c4000c040a84a02d9030f03450000c106107030816000070002e8181a6140d07052401d0510b00482d0b100240010f00940500030045800d01042240c500c040c3d03528a01c040c02a101002084000b64054164118008500301c3c00d01e01c440c80c41c18018400c48105551035030141000d003104100c141e8000c042e0403010394032594208203980140000780041c201c00803040304001c00320b03001400010000010710030304031040c081001c01008480c0d0048201c80750345105a034083c8000140040240101c40d112100d99664000c16003c46100788240d0303c520292403090300d4a0940001c03020500c450360301c218001100c141030b0070746400600300a548104c0c18580e0010100c10034500d1410005260484009142c4103400c4007040a00c40303840c050140f403000d004c00b9542001149096000a000820040d005505022042d80100307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 762560071 1250 762558821 762558827
    0x90c030f030f180a080a03030c0e040204150c020613031a07020309030618070e01030b06040e011109121207200f151e031018090b040231020309010e0d140a 68
    0x4000300f10400c01d80e642c6e100c00d41000b40190400404107800506001481c2c5403501d080e200f603c044d203d810f084200f080d40c02c40340036140d081240c441643e00407418049010000d201e00000c802640c4680b02d400c8804025203000084010301610b507000b5500240603409880e1000900f055100c1600340300b900705500703490310507070034151541c1102c41800a010008030038071802640f018007802055600304210000524a1822035800c0503014010788800c0002c0c00c40c904d0b02030340e0851075081c0c0300c003070369040d6101081010712540031040c115011002c04115440050f503029010302c55010588a03001568400c0d400100344115004200e010a1400702e4413502c9a00c0075001805041421003100ea5681860384000c1c21030419842640090140541c1d240710f01e85084c01001c0800394001c0d01c82d00c0a8403694200440c003006000705100d2100c600c40e608412030100040200c0b0382040400041e41c90030260119402d450718400007000c0c81d40420300a40e026640034803064030300b60079042026142c40ca840011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 762561321 1250 762560071 762560089
    0x1c030f030f022a0c0a0512030d1802120609031614060702330a02030601050c0d050901090b0913020309010e030705070e0601080f0703050a0212090c030f030f18 70
    0x80160a4808191568024511280a41d80083c1a0344100c4102e000060040c0c3d181550f5a00b03d802c403110040c20403041c00e001405103401076000d0300b901d003822070100c1d032841160007000b54000306070107100c0200d00390306150303500003a440c035040c020388a0340c904688259528410300b80c002d0b40389050306000b8018802a0100c1d020101182c401780e40c81d600b00440c00030f40e0741c021040140803d220074642d03142d10030f504d14070002c47c0d940e039507403040c81c1030707448003440d60003900010074490510008000c502a520740034041c988c0d82480548645854244150005003c034103e42c021560081c0c0030000f59002e039641c100981e0802c00c2042026a0369030348c00c0100b90152524012108043c400030a0000400c0703800310750402502d0448250310070a0307842e000110380000c2e0a5038020300f0308d0b129101040c481031080d00440d9004116010240c0707800e650150b5905030b4941190705a510340c101b002c400000340313028014106180620401141081c01500302004d0920908075940600c800c0d104000d029900c0742004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 762562571 1250 762561321 762561341
    0x1030b0306040311060c040f18060f0902070506010603060b09210f0106090b01140d020a090302061804111c0b030a06020c03030114032a04061806030605061c030f03 72
    0x207461030350420385005003211075a803550340c085000e51400940d11a0174842580d080703039040d01d111210b481c07910740980c0d000d8840c00b0102c2c41c02500c60b00c010440928280b9000c0052044410040e60740600c0e04009092a0068109000701814400c04001b4101208103030f6003158400c44091440804410709041c00d00c0001c00950f1107401218405e001d0300ba01907020b4001c41e000c0f034400b0b00c91807018200442e03000c00f1880e811207500e1401d0048000c2c04035280c0c090319407080c2c0c508009000d15200d13000240c0341c1d0840581a85450b41000403170b540c07418a0301824401a4250b441d0714109070001160b51542c200740b604169440c1d50f01c0300b41165695080004490894000303004550b140100d4500c10b8403940240183e001003540c0381039404040c140084e115103031402e00310100500d800c1342c804101d02150305211041c0e00548403c40840c0342c000050783c4000d03610380d80100254061441c0b524406441000300a14810404020384000000300c1c07081944025070702d0b19126a0300b040f00b840680c028042000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 762563821 1250 762562571 762562573
    0x110a0606090b030f0a020907320702030f0105070e221401061d0a03032708010213060c0b071b1a100510020d030b04020403021305150d0305070f0201030b03 68
    0x100050590311651200c01d02d031078150240d604c420300002240344c0d500040c440c001c1d045046180041c900b035100e04450146940148602440c0c00b4280003000c01805600789c05d00d6800d0800074840c821071604100160181c10b900000340950f1a00303a1740645003180c441c40450181a0548030188821031992203a4807481c0da0160403c03c20138001a02003e158090003500007041841c40f0300300301908000c407a10709a180c000d00c41c80c00241195000c88004070700001c1300c410389048145403100640700340b8036040900b8009000684682600000816003160f0b40d0200e814072140c1c0c000c45010a05600c4060f42c4040c00b400e141130015005082402208a20800500b08030080350501403070502404299010f218010060030b80d0640b02c80400c8030311054180070320096844410450100f80c040d401501007100000d200505299407078001c103100041e0104109441e030781d503004005c0c0e00c1460f903920400d00c110036140010a0042c0e507402800903c15540013a0190381528895400c5a12030f81210500702d6000e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 762565071 1250 762563821 762563831
    0xf03010f050901050c03190c0c14010e060c250f0f1118091009020a0519090501061b08030406021917070203130b0f190206090d0801050a06110a06 64
    0xca00d04000c040684986641e9424400811101c003c2002a0390007100b201c1d804003034100c80c407141c07030006007080c1500c40107200e17918a0700c8011410290350307200703400e02c0c0000114a10340414a52410300000a00c1040603003c24401d00c1203603035000341740c144000300d9807100c154400d002d820320640402e00c4080c02449044a00da410701000b04102d0400d1940c48140e44c50581c41e90000c44100074201d00302c580e81c0007540407200036500341d000b5422110300350780050280707154a03850b032000c503002c00d606460001803212480380030003800c10300f80701c1c0500400c054031f04040701c0c828006040020900001e8050321650010001c50103010259049800a184204548000d00b2291001810103071000140d4414218007100041c807041c000301c12100c64a1002d41d200e01114280402e020361070304a1018401600d03405d1000903411814507400f070b01c161110350020003092400c144000c0c6055590182002040039000040100e91100c004500680d000342c20251984501d407402a0f181c58071010010300701c24144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 762566321 1250 762565071 762565091
    0xe1008090c1210090c1d0402011e11030315120a020612090c0a1401020c04060e0610030902040510051c050c010809101b030e011a06030606041a0d05090c1e0f0301 71
    0x1740d200d00111420701c000c05080201d40c0380c0801c0040d004540203400f2030400d0407009001c4c6184c00c1c00c0c45450b011410030034040042c003400304d403440d0022500e81184110103600c5003281c3c41c2c0300d2290070610f40708030020100c1e540141e000c00c07124062030041100320401500458000c402c148403803031704040050301604146961740803e035a0b43c08072004003400340c000e002c081c0200d800c046c0261410743d440d110255106440784010f0100650403182020105541c841c030600040c0c0d0382e40100340c014002138082405090401c003c00c00254010320304c03542e50241041c00d60380060000b040d2144038160908103000c0c250307101196142000e0301c005140283d13501d480314107809401c2d40170b0805c025104681c0e04004220310414401c1c201c800c0c1325411380700991810030395421440c0a600460b40113601910f900e080940d140700b441d001420030091520480000700d400ca4082d840d902ca09a8002001402800718000c1c120110f16001942040582421011503406141e07840d8640303407481808010f4002c000304415 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 762567571 1250 762566321 762566333
    0x1203020102031005060711010509180f01141909110f0c0d0305010603060803192006040605070302041d100f180b060403080a030e0109060204060e1008090c121009 71
    0x2c55002e41c20811165000c2068140003041d1303500c0715801200a107000403407c005441e56081408480d42c810f502226003044890702a540900804c101001e4000b99410071000890100000e496079000d039842601c80d061105030340500d181107075140c0e2000603100d1407401c940d41045c40362002c0c82044050004810a50483c00250303000062075980e41000300380d807511805c42c00d5540071311480905a20511010701c004901c20150005d91400d8108110b1700c100c58020200740418000260b05a9009001000180407880c080c03241d1001c4c20b481d046152600b0956000c030350200391050b10f0100d800c28800a2614112450042d0160155005030a021642c0707400c80003280301981003120405080c0b124600386410103e040d10700340c3c2d034401403144c00e10403610340072030041005c030700c905446648500c2d43e040414128030050000d0712140c1e9680340c0141d004400d0125854103400d181041190b50010000c10ba80c0c0400e4070105120100c6a904040030070702005c525081000c40545541807602019000b0000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 762568821 1250 762567571 762567577
    0x3250c030206120a0b0901080a030e0d06060b2d07030818032b020304081209031201030317090d0203031501050415020f07091a01030902181f050909030a030e071203020102 75
    0x201890b810b00c01790704410103000d00204203201c2e0000d035038440520140003d0140038041488000901020100078450f102c16050b0b030402d80c802d814130301c80061181c40070703a8400012404180c900038500c00381925031509d00c3d418030605002030104240c040c00f24152070001ca020340d5001d101c20b02200c4c4c41e9002c0440d00808000c0d03013100a24005280079164118261078025030b4400d980000010381400310749484506407000041110341540000c00041d09803d80c20101e46003e140a0384d19901c2d190504800c00e1020340300508203600503402448825411613000041703d038481e0f081d10501441c080c00d2801600c0c24019a049910005035070149156000d60005015885001c50b40c111424150340d1104401110354481106801c941c040000e240254021b80140b4032040c4040c01d8403940c65501e84003110286801d4910105102881145558804001e0010405058202c0300601141040d074007581d83c0e44030fa82084010f15031210a02c1610b01c50900120000b404031000c0b1006251661800a000354 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 762570071 1250 762568821 762568831
    0x90603211b120d0c0c1b180e0715050912010b19060e06071719020d09140d06090206030f0901140405030a12022b0e03250c03020612 58
    0x15040241a8504070000a250508a1010070740382e460b01d99100d00c4080904400c2d5503c0d07040c406100e12035400940f0034007078100039211040303000c1c40d421f09095a0303525404040d040e1050450800b2128001c049011481004907216841c07281d5a698000000f0741e19030289104040e4403881c1c00021190000041d00025821181215040b041004018420314a20440e0240c0c1000516059686466060510090031594062100b00d40c0c0c0b400d0540c0c405219901c0300b103400074104d140c0d0116100b016010450b070300c0c2031030150400c02900d60800526004c0d074500c1010f04d610414549514405000c00c42e40b1100c0291740142605940f0f24005001800d010004e86400d913084d8a840308170500084109941c0d0301880c1e005025510740400144100c8030b4075042944001680d5003003005003504a03101080600103a44c85072090303050b200701d442c00001c4070700101c80040d054204019540030300e4996944e200c2ca8442c1c80180012201850411001c2c015040e00003d4101e0400600c84071408400b0500d94450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 762571321 1250 762570071 762570097
    0xf020909010b0f070308060616030f200c0f060c061f050f0a140102010f06060c0311011808070c030507030809030c010906050904091b09091b03050a0209060321 70
    0xc0c0d80c0d0320b0004106100d8205000d90055043c0f0002c2c0010b4841c044903074212400030b1416081c150340f500384107000c03056084224080b81d40c450021074040d4008580c0710140f210340b1714404884c4503005405494524109149101d4145100d000c14150703280800c0e502c1c0e12143d00308039220351602c101041c0103445509503003110388044d600e001801d803510f5004000144070152039604a84d15120312011010340950b81d050555403540400a2884010301c9082c00801c021741d10710f0071114507400c001d405802c0c92110300302e07682d05248920103000c15030140300c50380940c09100f9a030f07190000d0400c03840702c80b0243c0008185025095000041c40b1020300078010000c0100c0c10345074151220710064551105030f204807000310348184110581c0b45881d03400388070460300a00d0340070fa0b000c0c40501240103607600768110304400ea50341c00fa8041400b00c1c0c83d0301c030121740e202200a4522103045441d40d43e82c1d04500d83c0028452080c141c0020a9500c050001c07607098120714900c014040301440784454560001000d420312 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 762572571 1250 762571321 762571339
    0x60f03431b0c0f08010209010f05030406140f190504050703030c0507080105160e01050a02060f0606091807090509100b0304080d0903170a110d0b0a0b0a080907171b0a05040f0209 78
    0x213150740601c201d803a074404c140c403100103102c090081a1110b0300000c10983c1e0301a507419010a011500071042ea204031044084c0203a58909410288080110056a11000c1e441c000402c0002140006c218042e00c1c1c050611051321101441d1080c6404131542181c0d120354204424004080d013038031a2a0750307610031900c440c00c0d1a100b030f000440c4d490050002e1480180e11007400304240540c4000c1881d04001c2c05801246050344020108000c2401201c064043e881900104996903900c00e0b000b4000d410202d40280321070900140b00c4810315503502800f41010400000301d000c0148140480303a102d21512000d00607000315080c00781480883c02400c1c002c10310301c9000140b00c203606215400103140290070050800c102048450020701c81551940d800c00f04849012844060101c043d05c110b0403246d07100b480c03070324083c4a400d04210b890303404080c0d00c4001c4400004a000c01280c020056a0300404003400e002c1200c0c00980780000340da00c0141c215144c036081c903607a04102d4008000500c0c0c1039540c158 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 762573821 1250 762572571 762572579
    0x70504051320012d08090f0d180801050c070b06010203310b13030f140115090c1b080306010e300c03030f07060209060f03431b0c0f 58
    0x340300580d6119042071443c1c882103070141d090243c110250450841001c503060f0f0b07803c03080b0503841c0840340d1484801040009ca10002d1850486111102615500009001c07078100001c0059550041c20401403c0d110410001800c1c0d91081055422260386e410b000b50100d481410001d04001070021251189100c048010500c4217060b401c5403290340f030895215110b18510388641b035010002d010221900521828040c458030424007401040701c070004142c40e074051400003900c044844004440041c414404040e00d00128004600c101c0300e50822001e6550b5076401c00121190003e4030301d01030b4048408802e5204041361f00f1107521040700e8060489400d80c0c1888943c2e940d0b6010030250743ea05034400c0141c0710900301c40c40b02070b2030003d100c1c1c040503081c801d85030009035a030b0708950098840c142011041021000c0442c50700da0900c40412540c484103182c0540400a00000360303c40700c41081505070407031080707100320340c001100b00d2840100740600707141e40717041c407580e8102c1d200d03204568082510200e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 762575071 1250 762573821 762573857
    0x3030e010c020d0e0a09050a0c0f03090203030d090204020d05090d0e0102070f0501030915020403240212011e09090515070206090312190e010606080a020c07050405132001 75
    0x3400d2107516800820b01200742c004100d5160380c2441340a80c0003204d144002401041502819000700c0361030300c0c00319030150203440050000030388a55000415080c410010056280481121040c0907807110205182100d0b00204000c2d20440114004291901d010030080c01004a900801500c060340c0c2d801ca80f4041000480c0d40b50700343d0207984111844020100110740c00b0758480840341d0702c16800c90050919020004049800070f500c141c485110f040c2c613180030f200c1000f19482a10880200c21410000542c0907000740f01d105004022560f2803111f041c0c10900340c80c200f094005c0950843c10f204203105443c00985800e115550055529450130200382121300125440f481340d000c4000540c00d0160b0a0a11100818081d056851010107002c00c0c1303070309030928000d04505100340c10021075003c0ca005401060400014000d100c482d106014102c0c5664010402c1d1041b984c040301c0c0451192121450070284100907000141400310081003030300b002c41014448680e0940c00d807258281d808181d0085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 762576321 1250 762575071 762575081
    0x3091703030105090a140103050c012c100315030c0504060602060402152113050606060c0d030b03070e040c141503042003010c090807050f09070807140301030c0303030e01 75
    0x1060550400d0006002d60b0401381c42c07070340d0700c003c458402107170540e141281e0681d20b01e02a001580c07550402107120080703581001c0588001078030801b00d90402c52401c4580d41c951068804060b12640540010680d0a48a0340240a04805005071a00e00310399910b0000c500403210700c1418001ca0a02030700003415400441e04605c559005040d500028080e200003120320340c414210a02054000c40d00045000703800d85d00f4a00c940d814088000f01414181081440d002d0300130b20041c0704034008c000c8041e04c03000105504040c0b4600d4200803980e903040390000f0b81008603907008010031140140030030044c00b0070f401d6500c0495001c0c402080d00c24400c841444900948e184009100c039008101080001e58843c00e0303a14505402c6500400100a410000742500c1001c4203150009120440600c103096050201c0c10040204648400c1c4c210001c43c003103070b103000b002000f00090243c444005040c0d030340294255100041c1d01443d00b5134039038591071706a022303c12600050b030000340781100040580c3c40510075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 762577571 1250 762576321 762576359
    0x9060e07030809120a0b0c090102100606230c01230f07090e071e020106090c090e0a050601020f010606020303070f050c1506030c0303040e07111501050d0f02060304030c0309 76
    0x25440e0151041c248900300f1400032041c1d002d0720455101c0c170049442c0000d541e01603403003c51840d0380e46140400091802d020446140003e501e8242c00b00080344d00860482d17400e00e100000400c4043c56040d11049500405818243c55400e01c480410850380048030140041044ca011003825240c04110600c054422503103880402c2c1d541000307202c0312090307442c03c42e4002442e10b082c1c40360b00c510121a0f0141c240f1708040c100543e440e80707002d00141c41d0ba4010159051468982442418a05203254601e0036000d0004002680c1d913030045103170390b4428403c04501307500709002400900d5032070b50003d40c0e99008803080c2000800d103124201c030300340c0b1400440b61203c030100000c128002c012804400a03407405880d01d540740c4100758115510b5241480070f0300041c9204280307046940740c00c0740c1c090000400607184c61601d070041d86000074050389115140c0d05440c0d0641c3c2041d2042d8541c9020801c180c0b035030101a6022701c2c0030040104240c0e02801d42e55402d4800d03541d9010301a0b6580074002c14041c1a46 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 762578821 1250 762577571 762577583
    0x18060f0806010902070804031a06151c0506010201061d160504030201170c09040e0a1103031201031410060e07031a0f0114040f030506010905070914210d020109060e0703 74
    0x1041801c3c0c680d000340c45468010f0854502d400d03600ea4910002003224072400740040c0198003040b1403842c05201d010149503000d001d41e840c0481c90395030b0182e031400e007560038656a07a4a101040d2164403d5010101070700b50320b0510112403580400c4d00c03600ca8811100e90b125080e03507444602180d0301c902d05850469074180c44080e90510918154101158010a440d841202c180140d0030240d031103024005122881e03401818503101039080c02540100004a128080e900400183c101c3e0756030220036a044a03042083c010102444042e210304255040d16003640c540e00f0500d001c81d2000e90740d0305842c016100f41d20100041f40728010307010515020b045020b940840100d4130740085501504104000030040c0880c1490300761100307284242d4030500e41080d0341c183e010368014030660307402c2e00c24507030454602e0512495803072501c0ca8900c48880b90998007030181036906581ca0700020040110380070400c80c542615280c141c0320380f0082c0200009441958003c0c20700007000200d04000c0765103815650051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 762580071 1250 762578821 762578833
    0x2151509010308070312060f170c010813050309030a0c050306281505060c010c1205010503190302030910031a12060601030c0c140d11030c0709050a020702090118060f08 74
    0x144880c001900001d00c185d0600403584004616482c1d0352081202800d01e01d000e404901d13040031841422155200800241d0b54082c0782800c0082c1c0e0440030300c5078001426a050420000036250050940c0031b16049590148102c03c408000c0100c015607800c01e07143d059045440a50381d844101491a004540c2000718800101008040c0e200c950400c14441e51502006103446640b90040342d80c0da44184400c51030b42c3d54a00c0f104010355804440d1426004aa0000703000a506000c00a40c88118112041c41202c3c0d0725116001018000c0c01580c07104d02d801080c40c0d6004550b0040500603090000d0556440000b40c0d03000c18685ca0512440d1884504a900618203941e40c2d01c015802401001c81000611103030f1600640002d600c0706120340300c403400c10090032003072003100e4029200b00c410020003240758105001e9001902030002e2307820b080f250845170101e15525012103800003031155840181d04000e9500006c0785007440b041100c4c01403101c08000704581c1d651120904003042039405100410f0300a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 762581321 1250 762580071 762580073
    0xf070f050c0c1309060b010203030103051b13360c141804050f0d09140d0c0b121e0912070510021209160609062d021515090103 56
    0x5440942481000e510444405641610029900c00310302d10b43c518881d07844000a0042040c14068088113040a000035801c4d541103648a584a82c024036007045201026a500b8540780c0d28080b0062008900da1303001c120f903561482c220582c414021440e0320306011011a804840001c590100081076089002d080060341032114012110350722074402580f02100c030300c0040f0403890f40d140250082e031049009000c0d60300001c001c0d6050031400064a020300411003010812206aa1a200b070103c2080740c1c8800405150b190640a4a0454005a1300202c020540c0d08041211441045c05038481c3d005801c986d001003214904400c070100e41c08156a0408982c00e502c40f0002c07006464050301c82c0f801c1d0340150740d1b9403c90740c080340c028460350007a584100003800101e80050002443c1990340c0c1200c6080c550600c0c802915015143c8601c1040126100440c111091040c3d642d151240c001d510141e4103111441000750b660030f01500007181800050040703441d40c1c0ca003184203040500007520600e0309070b182d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 762582571 1250 762581321 762581327
    0x90a05090c041701110f0a0f0906050a03021b0f101a0303090d060b09070818010c0203090d110603010807031703040f02010e040902030607020f1b13090c03080d140f070f 74
    0x14850103030a1079921601c044038204a1740c00a040c0d008050158030347c41c0d801030700c4010241c12010f040139050002403d03040c068a07a201d401c03901c03c40358074200541d0b584a4040503040350360070703c102c0091600601d007a4404900000c41d00351003908000c0d0b010720501c2249882130b0241110500c40540c160b0041110000508010301c42c0e022842c01000b001400e001900040340030750314211034031400a11440c1c10004284074401c0039001000511008220003020904040e50307a03c50400c3c403511444650314088100708a10310240040c64001d00410303202d50b034641109036a0851030004135040b540d8140d000c490030a034207080d244284d4120641c0c0d6a043c00507001990900e481c0b05400f90000d4480e00c174140940c408201c0a0302074040da500811200f07403903070402d0303003000d40c1c83e803d40c02c10400c010700e1482c655660340032041c0702101541c1300090200e41840c0c030300c2043c141540020600c14011603520885859076002c0307a144404010400416a01c0c100924a540e8003101e903500030524440b100c516082c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 762583821 1250 762582571 762582599
    0x1020c0a1209091103040b011401090e19090b06030c0d12031505091501020f03070f0213020403140105042d110604320f01050d110d0e0102090a05090c04 67
    0x1505003400344450340ca5200040c03d45504c40340e003800c0280d00206220801c071a4074446401000d030b820206411118040000300180903901c42c10007050030081c0400d52058904941098580d4249010801590585030070392803020100c600f41d00c030380200186a5828140307109042d80180d4040904180a000d10409030024180f9294580040002000c080389039103400403614014004814071003008900d00c80020700e000294140160310360030a01c5501c0010b080f03a00c1980401d941224900c21410a0244510084c0190350010340400707040c4240c05550041944400c0c0624010b403422041c5440c042c00c4030b038848040c000b4403010300c500314401c072021070044038108a0359000104824540341d940c81c0c00b9018005601e072254440c4181c0308c02c6020b074111000c9004510201540c1e800400e40382140064501d003e4000d4040c641d5072500006480c1c09031840455003102e0f0b03252010003a03103000401a5000b5000008e42d140596480000890189440e0410354455824116018940f900f410304a9981e01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 762585071 1250 762583821 762583853
    0x905070b04030c151b050c13060f0902090303070210172a03090a02040c030c030b120d180305010c0807080a27030504120305030609100815180706120e01020c0a 70
    0x43c149140726401500219601ca005001d03030018600303545584100441230792000d10030341960789006810825010108051403c40d402c0810050700c0f202c0c0304010a0541c41041402075120034200e4168a5954102c2500c80300030558105070185640c8403191160102004414020810f00200b0344440c03031103001005503440f40c0c0802c19100360443c01d41c00300302a60780188151000c070b40c0b2181c1c480d40f1107516105100920000700e49103a00b00c6e003016006501c550484184404000700d81034407262064100030040c000350b40c448000c21855081e0f0304000d0800c2310607206a8002000c01020600141c0766008040020000a0f6400064046498102e8089444e5041103040c443e091000044d080e005284004111307020b43c80f0156245060010400e90320300c01070031004d505054403000c0c441c1c1c01000074990500d444802001d4004d8542e9011121480e1010040459a2042c880013107641c2d0750154034002c40160f424001c2c0300c1e4284a03543d050a03402480c3c00034210f42d002139000300200e070700c02551107861 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 762586321 1250 762585071 762585077
    0x807020303090a020915120d1206050904030c0f050a050106090b01080618090114010806010504060e1605030a022802163c060201090201080c03040308060f030c0d060905070b04030c15 80
    0x40716414001ca0101d47c1801300302d00d03981d0400005800c42c660024881180c614480c1410400242400b00050158101400140402000c000340a081203031040f03890503400d4202c0120b444041c0c00c3d02d00b081c00307491179000700c03881d29043c00303c42440c0354041d10442d4002c0c0b0300107100911801002c0080c5e1b80d1403100400040d1550349491030500000380101d546030103020002c003d8540303581040e0910081c1c40e80c40d0300c0a620000c4003410402e01191285510407480c225140041e640d44840d104c4801a0281c0d40404a801402d6034030500001051207907160710b04526020790720307401c40701256404001c116108180141c084170010340044182c20402900c1110500150044145006812980405540c00420160f9500d110080079903070003682140d40320021000c05851458155401040103202400040c080e20814402041568062044d03804603840942402c9040c01181030080c054804800300b52100c3c040c080b4003048141541d0100ca0a8903008000100803504e004074000c3c401488640840030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 762587571 1250 762586321 762586351
    0x2403060b1219090501050f010b130b090f040e0606090901050c250618150510091a06131e1518050a090c0f210f060513050103030807020303090a0209 65
    0x1110368544503c62810707001d02c3c00050385103058903500d10005010b80200f941c5210511541000440110580c8140e0305120000c9480d81601c4004c10b288248440303015500c01e040c510b04007142c8500190003807040408480000664036040c4526088440a617044080780004210307000d0001c101d06202008503074a042194000320554559100700d903110089049481c5a41c1510824440d0318200344150440b0740c6020400760402c8403084454130050700c1a02200c3d925541002521400340202c2001e00c0d801615541d0350300f42c00c44601c50744062034082c1c42039000c81448004050000f10f100b01c0b0640700c0c1e0000c5010300c22a000015915006140c0700300b000b0515100d00030a198450440ca0001428103450105000d02e040070003501c503004031600f020030800d86410030310480f00c4000580e500390302c603017034001002803230400411f000d40504c2c1c204a4000034040124902100303541d01541c102c9000f5596a2001c0c5c45111342240c5900c01500d861442c1d50007442c0b401c0141c81c05141194100d600303040250780b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 762588821 1250 762587571 762587611
    0x280903122001090302060106021b091506130b0301051003110706021b0d020a0204180507052808150106180510050403050d02010e0607020a05120901090f2403060b12 72
    0x100b0b48420203000c03030040e00035000420448d0b40401c0100f09546602c4100c0c10320300910b0010403541c0e400200002070390400300340c00c80c0c0c40791211411285200d8180c040111343d103444403210840341c1c0c001e1003450300480c2d16400c0c16103085d102e441103052501d61403140c0c40c50011583c44d0709002e50003103e24a54040d550b8110300194030002c00a4854002d01078000e425060b330310740100700449195070002ca61b022080340303141c1300284010801c40181d0701c2c01c6900f01c01150114070304640001101a6610b04051402070100b40240d0010707090100d01c00c1c80801580c141c0e201c01080301c044580d094a512503111070f900c02c2c0524980301c4591281d04102d8030b002d07400d0950301d448007807400d80118004070250355106c1c100065884140421070b40301c140c40c0001c0295180a03690259241412030032030410100115114533030741c0c42180141d008050350010202d06948466240c40022810041c1020700303201071503149111030003402000100c0d5203a891080c10030900b0f0800034010b9600070b011181c01404000c0e184 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 762589928 1107 762588821 762588823
    0x8060a15030e1e06060a060306050616020609091e0106030606050a05215104091b050a090533062809031220 48
    0x5910400a0b030180d0400c600c1007034403d2050030440600078144070016045024a1081310040000380c2c0c0da84056045401c640305036030700000c003403040d2048038000100c20701030f40740090400c51910740c008001605601d41292071160006041c00070f1482c840c00c059941c0d0141c10b85003030400116080c10006011130090440e00d804110000900b080c0e01030b1032140c410b400700703942c0008881500f000810740c0c8911500740703c11b0035211260603140d01c02c0c030400d01c603044440c00c040c41010900000c10005201007201c2c00c80d182e41068039481d800001442c03070f40c501c0c45c1031a80c030799952884c00d04000402000702810b074051410a4149001d000c8080303100b0540d92181000c02502107111810280c090255130010092960700c0ba102061000d030404041100d0020102d034a14061a61141000141c400b90b60a01020700b0502007031500e90782d00342c001d0445880741054002c81020b6041082c00079 = true := by decide +kernel

theorem cover : BRFrame.Cov 762410071 762589928 := by
  have h0 := BRFrame.cov_init 762410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 762410071 ≤ n) (h2 : n < 762589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
