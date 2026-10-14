-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1489
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:13:40.467685+00:00
-- url     : https://prove2.me/submissions/be483e52-552a-45ef-89c3-9f6156d5fe65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 267625899 ≤ n < 267805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 267627149 1250 267625899 267625927
    0x7020c040c0206010b030103030f09030b2701020309151e161713150b2d0f0f0d0c0803040609061d03060a09151a04050603012304030c060f02 62
    0x5688441c9101816296044c0b44041506010600010b000c10258007081c0c4d90140c05500c04002a42c3c01c41e4668880346010b1510300c0c2551502c0d0040c00410760040c1300f1000d05181402900c0c0109070b40340141c58a58070850100041950003800803144004921a903960045005066400366904e8a424030860b40b042d4005408410006040600c0040440421101d40c11628882012982c00b5001d44442d0071440f40a030301600740707180119440403201580e110040742030507004840540c200300800c4102c08040c1000644079030b6494a5411201c10108882c10345006058103090a110b101884066615410709602e9600703e80c02c244042160344005200712608203c510380b00c40300d03540c00ea2900a0040001c01d85402e4064011402d4945500e9040104081c5500d40c40381c1400c400f408100e4101180300b05600450314543c00750240c1d14002c0840d0707290806001c0c07130050064800c50390f50b00803594100848000c000600c160100f0a11a20140000360399018140c031445400001684610982903550 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 267628399 1250 267627149 267627161
    0x10317070803040f170a261003141c031b180b0913050423030f0d1a04020f09040515100c06020702030118140109030206060105090414010b1b030901050405040c030902040507020c04 79
    0x180c8802040408c02019800f8207010100b0f036607101d1806002012000d080301c1c175004200d47c2c40030304811038641c040c40341907040d40214408112148500512440b8123000c0e101102d2240914140111180060007400402c400804031104050010351040d00b19400050403a40c080d14100c40c0030a200b514002c5203411041003046041100025514240c01c4010b9402c00e0700c505a4842d00b03903901c46282c541200380d10000300745101000b400541da1500a059840210b0b4403841c20b051055107410003241e100c064501e0f0390861f01101030001c549072550104240c441c0b0485802c01c80e00144c0801c81640141c60a004040c3e075512590424540d01c040f0380380c2800e881c0109049500141c0c074100c00310010076800941e0b16040542801c4c0030369078090743c1c00801e001d4a12800000303940d03110000001500e5030020000c048422841e420308410030340c82100c45440c0d101e16425a40011001e010038006464954845a0760340e0b0542400603141d0380c1340d40800d050300c02c1110083d02580080300409000e0a0500805d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 267629649 1250 267628399 267628457
    0x30f2c15040b09030609030306060a110f10050717190b060409060e04060b0105030603063904050307060f020303010302010f09240806040b011d0604030c080303010317070803040f170a 80
    0x7d58114948000840e42074000c940003d0100040005240c4481c0e200b484042841c036541d000742d8414409c080c00c9200500030a4a00d00d00140441d8007100c161403000c51158009c140c9464200c031003c0900f00303680040e0034503081a03607100d50100000142c03402548120001480d10400c98540392034541081821118401c01e0305050010030002c01059070b40100c3d400c2e602580d0781d514200c107800e903924038603150081100c0307080400d030381c825a44183d00c008402410407514102c049034071050321082c00b01c54503006000c80d10090b0384144014001903010710f04000d40174003140740005100707035075400980c1d4810099815810b0424039203112441c0340c0d404221940e1040080c1ca00f440075641040c0001e0103800c0c40c12400102c03d0030300311100318640d510812540255084280b50703908075150300d159030300e0781c3c020321044400180c884164030341d4007038041c1910010358002d1191400c66540e07445035800140246411540c1c0e45000d818007404c0301031100500103072446540c880010f02806258244908600009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 267630899 1250 267629649 267629653
    0x80601060c02060306120c030123090703020d0b0a090f2015040b0c0a0f0b070e092509080304060c02010314040f0f0614070c030f2c15040b09030609 65
    0x10840580c0f03e410440c0e40040d010344e5542c00c00d482c0c21200904105052030201d07810b5080c00c6d8002c0c07803000c07a07008500741901d03c224030003465181c0003000c070f96407000d0b4840203400102511880300842c1e8102c04050380401c85000105004400b40d9400e1124284001e040721006283c40d4858990307501180d050141d01000d0300c590440b407102810741c0d4140d028620800c002003a00107840301068130240a05a18564007480842c503090640c074000c4140501241e00f40006540801d141c012440c0c80c03006a401802d0b070a140910b85104850785d0303903910058001c103c0500161310000940603908000400041c00301d544c44507200007c0e40300043c2030742e40205010b070200000000b404080303140e41d04980400e0741e10840c0b0f10030b00d03183c1d17186c480d011784904641c209107152141c003003040781a0081034491484e071181c0e4500d000c10389501300645121401c0c0e25a41d20a2180014001030296041ca8841181000810303010740c048900074820b1403980560030410b5144070202d00b0440c64241080929040007803440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 267632149 1250 267630899 267630917
    0x1514070c15020703200304061d01090302010f17090d02070503012306151c0f1517010f06080a020a0b1804050411090f060108071706061b061008060106 66
    0x160080c80c0030150000707449031640041c2482c2050b0182901c900e800404240403c120304e20300040b07070340703981207031091502069210031440d00982c8400b2051102c030b0b0741612242c41150950700111900ea0480300417006025201c0d808904480102080d00d108144d500b0003040403901d43c81c4003d0803c405580002d0090307040c0341c4501d44404002441141282c0b401a010440d1342d51400000c9581c01c451070000c0141d20001612005403401c0785100021b100b004006201416141010404807901d0080e00c0010050381101072041010f10301c61016698400400481c40c030320085861400c94040b81e00c00042540490303021011401d2568120307008000c80340f0607a0415481081e01c0307070751440703588055100c4c40e511000a42006070b00490001402005042403c59142800031000801c00c1581c2980c089080e0380001050140b20784107400e0650140081c0e903a15450385014003e0541002c000305100258040d24100340050400144d4440c08203414000300d26850a0b11442c100321068101c1c00802c88105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 267633399 1250 267632149 267632153
    0x10203090a0905060f06040618052b020609040213080c0604150c03021009050a150c050d090c15120608011a0f0a0329100e130c031514070c 61
    0x81482002c0302e4240e8000b040c6607071071800090044a6000101e03a0140c400f0030003051199001610702d1180380e0710b0312031410860b2200104030240d4030014103010550940e194648050710f0301c0311100c3d552440604442d007000c1d41500020107a8100080c048014548403d04125102c4108041003d81c1d80c142c1e96546010308080c140d500c0031407050440c50a1050220784082054400c014040200005d000c00b000406000c0c0340154454030000010307908040c1d40c618600a0080070b00c9480e200d4cd540d62240380c0750502038410040076196440e402d0baa0584282c4000400c0380f4940541104001c00382d0304d4010b034055000750a400c442c1d19400003c101c0e0300d8140c2c800080c000104091000000072600314140007600300c009001c12500b80c00040078403c0d490400740c1003111090034140c60700720105003500350344c1c4c441c50a824206a54850030312400c0e03035080400c8039441d0b0751310303019031803402900044001c90b01d9840c1c02001c803580748540c2410a035a9003061070340c0c4448140040e0004218502129080a25 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 267634649 1250 267633399 267633409
    0x1c03020a030c031107240905030319030b0d030503010e071706090a0f0608030a0314061003090804120f030915080c0d0e012a0503240a05030105091b01020309 69
    0xe035002400d00811807281c10526010348100403502454a0888040c561a400e0072208290b11003040500a090000160416802504104252540500114100003e612034901d03180100007400042c07513912002c841c40b0b40c6601c994824114000d4031502c0c6d4a52500104510001c401030400c0100b0603070b40b00b07c4503031094407407649420a0084401e03070303900d07161142ea0320000c11300c400c1c0031000380b85051800211510040090040307445944c808025040720031995030400e079002c850159101810095030180c46010f40c1c030040741c290141101504094507003208003041e446c040c6081c0c440e0110326161000309688565540003030f1000c52565002101000009807403d0b50103000041140e40c04141085203061661080d5041034004d0000d0106004071000002c80ca40d2064501000080d007142e0800c185014104580c0141da00100001c981060b4040e80100341e07142544031039010040307420008540c3c3d02405003501401100700607141c60444085810503854503000c1d01070640d00180040545950b82c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 267635899 1250 267634649 267634663
    0x50c161b050d12032d050105031c080109090606050904030314161d03010b04060b0c060a021309021818060f040c14030a11070f140703080706150902040b07021c0302 72
    0x250741004159092030a900c01d05c0b1283e0b01c298044145204104850b13501c038113070801412220b0540503940340415141811070300c80000095140890351000c0100728818060307012005060040384001076098031003000410340790b404d441c1600000d84540d0b10003ca01002904260000d040c2d40c81e11000a0340d00d00007800c2203206903a00300d4406581d0120480700c0c0c80030b410092440300d009204102d0591611490001908030140c010841e103c0c16000480f8011544220346d0034171001643c1c54001c61030308c1c0c1030710081e51091290001e8040c01007801c40c900d4545603204a144100c0da4841c80725450010305009042140d001014415410300780d01d90341041d00b0802200c00e41220a02182e038940e291301d491009086441c40b01c415018000449000780312050000d072006500c5070b112201040100c50801d0354925003408003a006044c20070403880010100d5022400035140e0b001a203420a96a00794241243c10a50084200c043e000441004610380412100044003406040703140c2c002a649000b07607102c1c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 267637149 1250 267635899 267635933
    0x13140f0903090f0915030304081b09011a03090f03120103060f15050409050715110706030c02060f07120e010e010e03071707151107020406050d021003050c161b050d 72
    0x30000401c8881140c8400a0100c04001c0e084039566544d40c0c03e2240e034ac4240240b40390341c40500c516411181c5c034003060024100d4644005002d840c98044d8040d01c40c03680702406940151242888103044101c0520240410035058003180702c0390742c503604202050710b035541a603010385803a00d81c03500074030840b811440081d103a043e5000511210715107812440d100040d081040702500504509100d1039100382c2d200382001c0400151800382d540c5d11415016291100000701c0941c02c07100c00501e412107041141c2da8401c1c4a032600d0356150580c0c2880c001202c1d03c00c890380030036035114040e02c19980001d0181840c44050f00d0000d5141c0b0100707845802026812a0121080800000c0c1110920071042209480e00340503030000c000007503002100c2109030b071122800728015402c201000900346421400151155009032020103c03c0a400c011070080500078100d44034150284032901c400350b0b190001580c602e1103040100306201c20240c040d80d0740303c002c0d40030501c01d8140700340c07413000140c840410b2000e40e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 267638399 1250 267637149 267637159
    0x100914070f090302060310090b0904050c06280207061805090a0e0705100c1a090318041e06031a2a0403020d0b070f02010c1b0213140f0903090f 63
    0x10000348000c40b40e0041d1a803001c0d50040b130100500074800403a4044808640c1490b07010842c20f513004d01440031442088034090420340000c1c0d01021a428184010320381000311a030004629840ca000008500401300b0300e52005070700c4140700303008103500f20300b107115501090300207610400c0c5400001007000600610380800161612200703000ca02e400c104200103014024600c4488408100c00200310300204070094a404100100310350049001d40e0b04d640c010f4407660302940c5000c00b180ca03c150f40d680302c00801c0342c01503a6003659840380c0031100603001403112502000305646140d810078000d042410ac11481540c45060140100d44003235601c5500e60300d111024418402c00c1200741125030703000d99070001c1e40010074030700004204105440c2c2e1620400685d15640b01c00c00000d41c0803400c869a08a0903000f0658410001210082c0007844208040c030040504000889005090301941d070000070303d4924482d0501440a4800f00087c59944092020011803d003e01c2e200065459182d103100c160140d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 267639649 1250 267638399 267638417
    0x90306060103152d0b03040c0e0c1605120c01021804060b031f180c08070807050405060c0f010908070c1203020a1e050d051903110301060f1205040b10091407 69
    0x2075030008100955405034030344d145941d40e170365501c2c0c030199600450b0200e40303240d250b01001c5607259451180703074011450000d80500300204c00800800b0160102c1e0700765250300c100322401640d5560781d001071001e001d10000258607213a0192151a44043e20680284500d04240050001d4102c500940380d01003004252001c0c07004a603140307a586030350389800c0240c098500103000d0019042542003029040d0701c580e1500d400f55100c4e0030031142c010090303a20400140d400c1104100c0c0f85443c0003d0070003640c21070140c4032881c0100946a0840c0c1c1e0b100c804581d41940810207209100e861540716000740140ba03040600c010560354000c0d00c60740230b04c80042007040519034280b01c20007441a80d416036075008088641210002901030020780080411014440000383d018540900c02e0065500c02c05501c038490b800d40e403c00d1020b940e05107800140c8410441412102283d1056600070903002700d000d020341c900a801d040b0248807200710581c0103c240281402d030140001d2002c4070300740c4d5021400346014981 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 267640899 1250 267639649 267639689
    0x6050909030d05062407120e100e03030f03150a0b03040b040204090f15240f03020904060b060d060513050f160e0d03050306190513090204020f07050309030606010315 73
    0x14031746801d40c10394240294054200150010b01c0001c111050103807845885a00c2000422a911900401400e400c40302c102c0f2000c0352540500c8400c0c220807001815a0708243d5020044500c40d041202c08007040407000e41c014030a4107080c03400101903c50300100c50700d076160a0701e503140d6001c1d001e0f00090040b03a0340d90400d0f050007040c180e800c020941c070001540240041c40d002c00040d15100c6c103407184042202541c009840c5030030340c10508803030300640210704503442c0d5020449000c030003c1042d00c400b1749880b0407241700d0b51804010300c440040444001030725414007040c4002e403032009508a1110b8600001c5c803842260610fa115404028120007035404041c11908540802d45000c1d001e42005c8091030384401c158110002c1c5104440130b030348090600703018840b505070703200f6544111a0000e4448600016201c2150800001c0f070340041c20152070700240341514005c9502c030901c00d03a030f15040030840305032030324042c0a00b50701f200c82440e080c00200c88800038000c8592180c4556240950b1400f9001a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 267642149 1250 267640899 267640909
    0x60503120f030a1401060c0303050a0e0a030302030a02090405090d030606020d05040b07020f0301021303050c1f0f02011b030b04051e07110c190303170912030a1506090906050909030d0506 82
    0x4c402ca5042c1d002c10344d541d444002400c2c3c031101c0740044000c641800000f0742801c40c203204800894400c1002042c81c2c00305a00d080e070080d440540118540c079020865040399454601038203018035810340003425035000c3da181c010304440c00307900558115000001410f1280b6400029103007a14020b6a004c1c0e9504000d100080c1d40c03001180030950503500100d00540c000381200c20003c201e901450989142c0c40148041200d5001281d07000a440c07103500140700d038100e116060060905105000008986604a1038800c2d0400320518840020341c44003560021420103016440d0400324005209a486d0f51140c10030000800061003102005001e60b07008100c0041000480c00517140a0190b0010512160740c05070762581314002038012843c070222a548041c49100150310a41118024102452201300490142c0d4000f611a00a07262601c05401000390a410b030b000040a054550111661a002e000015035401764090351188485804002e400f0001104071000c41c2c10140001074107075541c0e03000a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 267643399 1250 267642149 267642161
    0x40e0103031d041a0a0f0e070e03150903070c0819031404031a09070618030f020d12030f0c0302040803092701030b0f0a18020907090b1804060503120f030a 68
    0x40e6129060a401244c100d4200b001e071042041c080d01e65021894950400c0c401042e524814681c08850960000340524810404801ca0650080c00d40380da524203101214102002038030040c07440d030800160f00381000100040900103006500c060310800704100d140060020b03084901030b090164007803900e01ca5600318802c0703c0245074010100d0a0072940704100d115540342c2120303560784e90704c14810b010031182d004070392082c80c0301c2094943e00840da0440d0b07280070002005071400c9070070008506007080001d1a601c3d50585554160303070001048000802200c007514598038040c2c051510400081c03000d540003000b181c1001c54180d4080b070b009901c0b0050f01c881c00d01c03145001080e80c0c01d80da002008001c51201018007450b201c050180742c0e0b032100300f1444202c4403400c90071010860508941001424140301c10303035220b881c42c1000d01c1c8241d600d50310000f55034081c0720a0303ea450b2410303403c07010501d0248a600041c21060b002860030540c4000c08031030b40d11600c201702803a000c2c0440003403250004c0da041a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 267644649 1250 267643399 267643457
    0xc0605071b0c080709050408030a0c030204090c1106070f09030b09030904090b0a0c081015140c0c0102070806040b0105060708090402070f06050604050c0406180e0f061302040e010303 80
    0x2520012810b06003a4540c08403405500c2d494041d0782c000207450b107513502541e400340d500451000c0c696103648000f540100100c81021052603000c2c400091100710a10645180482e903454800e580c04400055904182c00105503006204407244001c241c00c0d40034000c4001d8940c860a959202d807940071100380b03035001d00441240d0240c184142d01c8100203c01120b140104110782041c00900c50f2003000744c0300c8080482c1e2100e510031a164041000f0f1041e105e01034111302d4507080c103c003540c1d418801c2c500c481e4010b4050000c59407000d003180e1920350741004000300808102c17019086900f01541d0b9140c40c5c51061280f103200b01d070042032010600c0801e604031011207900034001c5540304494a030566901001800c1034690740d00e020006610340c01d060041522031909021a5480c0500b0140c013074510350030059101c8a01c02c0105400b0070503401d0702c11801d0003100b014100a00500e405400c1110003454050300c8690180140800c0107500050700c4a68152a07241c00c0040e21900b00c940c82c0180b6010380584 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 267645899 1250 267644649 267644687
    0x6030c03060207051e0d1214181e030703030e070e090105061f0e04020a030f1404051905060f0711061303030606050f090d02040e1c020106060f0c060507 67
    0x308000c29580141240c2e4442d40c103803071658140d00303a200c5d820b54445542034025002480060078091103034405540101c0030110025a45400c500040407503441200e0180428003420340e042500c07003042040b82000c0d4000c1c1d0318180452045c0e4581512800b07440c0c1d008041c962079888100038107505000d488003400311002030007000e18000304024040d1000742c4419005001e24022080015602e16000504506a4940310000a1848203000007584100310110405603141c4598000054a00551116140007001d081c0039060500307186007091210400d600040a0408203200082d50110384c566003c2d10141c48000265103a0400f42c904184c03002e9406400d01400041080e800e4458182024150181d9400c000c4507884a4050762188280303551244400b005001c0342c5100d00d010443d00c800d480c400303000441c44400e20640c0516017064104031826120114410608072a424032030f03000203119514185050a404150107405860b078004080c01c01ea0b19800082d400794001c5408030310031040d0001e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 267647149 1250 267645899 267645923
    0x2c03071703040308251202090d050309030705010314040305030a0f020c011a09010b0409092612060406030215070515090c130e0303070513051003022203051f0603 71
    0x4100451a441102d048022a03008008a16081001ca09060740070440407110a04050750341c0c801d850030784083e0b403018001a0204a08009521524180c038080c40c07250780150388811000003014208201504128101448c0c2007070301c2d4001e0244601c0641050301401d2250340c07510b44420790000313016034440c004c410038000507054181010560100d0401100b00814013011103802c000c01000620a10903074400000030320041c410080a0340c800b41e2164401c1441c04181c07070180c5214a4041c00461240c00e00c480c000c58502013424100500320f61001048030104500c60640d800034640e03d008120b080e01100e008078440e0b040100c100284902d18922082d5464907103801a000382d03886a1250009006040480c418100300c001400b808000c411840041c41c2181d440407422200c0780c108a460740182c14200000003615120300c05078048020095402503a1100318025500340c0703030400e1481501040c03454208101003000401c480c40b22190301c00400380344001824001010340740b01d42001d000424508 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 267648399 1250 267647149 267647183
    0x907050d020708090103050a0b1e01050910080105010807021501230409080a030f0203041e05160905060103060501080906011404020f120a0e070e0412050412050d02060105042c0307 79
    0xd40304200307091b80c09101c50381d1444000001d48001c00319450300314110b1203041e10104c10f00809088481011300d0607500b0458044002414522f20101c402c01058940c4014441542d016040580c0019540014100d00e0028001500c1105052181004441ca00e0800703806054160120049408009206004994407410002c400f0b41c0408200710119152290000d40e01a150098030321640c0c01200305107100385c1d91080dc4074a2864102d08540c28010b100c02840c1200019070100007502000800090170f2416500140440707940ea000300e41030248585c2002440700e4006280f5054aa1803c0710301421004200418060700032030140051038007020500d014000e101c130817035a105000e040000d024840341c00500030f0716079406005601005420030b0004020800c0708240309060281f529109241540d50001c0140b0022224000c41c0d1682040f240781440346c3e8100000350140208980030001d050f21010441007646100015540d412504c10280c04120002d00544003c00e0300090fa201c4074907004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 267649649 1250 267648399 267648413
    0xc080a110706110703060513020604060305271903020106050d0f0c121208040f0f0f060c050301050604030f050123092a0103090606170304030512090a050907050d0207 73
    0x60a152181c0c071401d10009101c603c12200c1c0d00d6184a4003001c1c0ca00d44c0e080d6242c46014002c02003190301c0b002c00128001d40142c17101e000800080c00d865900040700e00f450300340a800100c041d40d400010341241000003103841800300c2c4501003109400420707800c41c20545000d0340503283c00d50005501800342092603003070010081c05403001c284500d0300140e40348e0b250040f010f40c1c0d03440408050240407000c414416170743d009215213074016000d21001009402c01d6500d85c0c03d400c0f8120001c4660341051010b40081042d24015074241c61030034203019055604010210350680102d100280ca0a02841044820f120080d4484641403c104d5920040040c10a82d51000701106070342030a1644200b0750242d00c4c1847c44050f2000301c40300407030b0ba60070030500980110060301e5000380c1554030070f41d0395400181d8406480d100c007400c0380c00780700a15222441c50800368100b00c4070701c0581541030010401e210f201d6a803d0074079025528200c035504901d8039041c0b01100d45010340044850480d1000461500b0711241c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 267650899 1250 267649649 267649667
    0x90b010207090905070b0f0909071d180745090c0507020111031902010b1002010b13020714030c07090c0c02090f151801060807020303010b03010e070c080a 68
    0xa0302203032080c81e80c81605000300c4418800180c43c9801c4030b4414404480d0550050105882c2d441c401c2d402c00f800000010800c05050711800b01007814482c450501c4519803495020040013190050301400765013010341d040c40c100900c0e0300b0411440040b05003c1258624803000c40c0c00302c100786241003901d80c2c0e419016009440402ca4049818406c001074840901e00981e03408a009590380c7d07080c50383e650b0041d5607032900300c00141464082404041a0900403400082c0d200d0115070001c10b5440700c0d201445080c0f8011a407060441e410400c6c1c81e00940c55110ba410821401444010b03035070486800d22540d50f040f940c074150f1aa00002440c4601c84400040000591707401c81820000e500c04044190b44069003c0c070004e400c01100000030300c92400609050340d101481b12841ca50074203560002811080c4041c1814000248007001031003031981c004009075000d009030004520f154180703424103940340414443c0036920010b48000503109803041c2000c0d5445c1e540f145416459180c3d410024102c030903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 267652149 1250 267650899 267650921
    0x30f011a01020c330409020d0903080a060b0301032a0e06150909131401090c08070603050903071b0b0408061605041a07050a0b0108030d0b030115050108060307080709 73
    0x45590b91000c1c06181c2007030b02540003540300d031408010318184d0b40c2031901d141c02024030481d084001d000c0040c0c00c000034001003048000f90080040c0008180c9409012140b01030a00c0001d18908013003409030340960002c81c0e0540f500301c0c44042142e1044c0b602e40f5030580c199013009902e003204100005481c524600850300810045508100c0120580c032815030a011303a0500642c01171020010509035254070802c00010790003491403428000c9900c89282c2561152081220140514141007040384000d0007888040c0003540713828031550403e6090580d5074018030074090300420a80c1112282d000d03616544500428201c0321241e21a55141181a121a422554980d61004406c1020f240520a100b100e043c0c0d040b5070710200d030340703444420f080c2600c2d0030211007268103108401c68400030854070280b07540209407860003180c0d5845400105019100b10210072402a030602c40c6a0036410f440d00d00c801d0541d007080ca05050344c0c1e55040000703440c2080a80c8412100d0207940b001241c40b5030150800829030b8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 267653399 1250 267652149 267652153
    0x302100f1209020f010804060608071211090601021f0b04050c03040201110601050121060e04080a1715040b06070f051b01081015141c1a030a060b030f011a0102 70
    0x2102441d0312a042e125140340003980081d40d01d43c262103943c000c1c0880c81c0c206014110001e002921840542d191550740d40014400c1141800300b0401c1280b0340042e0441014180d40c0c02c1c000741410340000c0c3d5603190140c1c003821f402440c1c0350340401540d2968031186183c0ca0003842840302b8100510346030415801036800f030740002c203281440e00300500006005412a04d0603540c2c09070b03c10941429001440401012a00b8981c9170000040d850f00010100c0e0b000b14094a807460742d44012844c05030021b4003000c0e050010112034410028a655103c3e41c040840e0030640d00420f0078034a03203002031080c0c07164910081130452102d032180180040003e0201240303084000310300f0700f0300c840c03001526441403c5034010100c520540d401e0020850407080d0708030131151400d14120b014809410030b00c05411403450141c08004c42480c42940741424000d403110744251007840c140e100c1107040480d48607288400081c140341d45402e032469a40e14100002c0c02c0d554005c01c020007824180c504407030640002e5100c07041c014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 267654649 1250 267653399 267653417
    0x5040b030610090e0102090a0b0912061902130e1005091003021302090d0c0b071104060b1206010203130329070206070e030309040f0203101710050c040302100f 70
    0x18203001441e280902c0010307446040c05840c100044019000740c41032140d007550284104000380e101d2008800260119284807911500d80000388044108907004401c1e1603032182c070501c1500c1c00904802001c00070380260259843c1c69005003c159080540c1c400c48181c410b08013003044031502116141c1c140d0300e046450202070b40b40e00880c140b81041900010350302800c4451243c19011070303507009002c140c0f0050440301507410f940d02d03000b400c441d80380c2c85460240d50001c2e1800800c84035100c1525080f5044030100b04640c00c0c1808503420307019407690a00c010051a0209141d6070080080e103020105001503214010307202e10f404054240a400a40960440c404003c880030480e11040c07441002c4550060000c4d56030403a04a41c83c02d04842c01a030140010014149552900e0095950003001c0c081c000d607a90411980b05000c404280d486481d4000c491404000348000103e000d000481d2104000305003511503280445e514860781d80029401070f2002c0440c0504d0341c02c08200051280c0a44401c00b80c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 267655899 1250 267654649 267654671
    0x603020a12021305130605030604080c07120b0601030207060e03030112030305100e0415020f0304060506120a020307140f030d080412140d0509032110051806010302090d05160504 78
    0x1603000c3d0307481400c1c98610501c030a0206081110030050400c01e460804904030755140c001c80d0602c602505c041d60061000161000040c1042004500a00305081c03412841211074071100788161004e483c16040540008000080c0895900000c0b5021800c00649540e0350b5644009030180107104021400700341850000380c44401d1055556046800c2e10420b88000c1d5038540d80d228030f5907002c0342036071400c2d170742440b506420140d150050361040f4407030540018a81011820081d580403c0c0d4bc008416901164103c001030300e0200b00f440441e0001c81d24222541072850010300d4117100341c00c603c1e800d480b03074154204420307030310845150186014400740101501403880880390320161900c3c1505112042064034a01d150300d5224643c8650118103036400d203c3c4104803016494141121a41c14290403c1800f4550303817012000402400219450945110200d0500c0307058007004154605055000c075030808140c0707540d581c01c00042d034800191404100c000c10036220a070f81501500303000c0da10b00303854244 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 267657149 1250 267655899 267655901
    0x51f0c050f0d09030c050a06061802090d081b10020d0506060f070f080d2406030218120703230c12150601030e2e050403080403050f040f0603020a12 65
    0x52514803650034500d0b1022040c0441d000d070201d44030440800c201a06a00c010079814000d00048074800c3d8000300f405850b00c110307901c402c801c1e8008041254810020001e49030748403920014400e610855550700c602d100c452520b400084551105520f00610303541d04201c0d0b0807a40103108580a98000f044907803110810b000e034501820044200c0c009003002500003041d13504042484042c4141c050b545011860451441a03a4926000e07881084c0144c81040ea00341e800e0780b000c0040c140700d04e4110b092040e01c1c00c0700c100c0449c45100d03042c0601c159040001408005100000146411000030017010781d600f044d9004507205896400e40d14095542054000d1810452551500141e00001c100c940c442640854040c20042c10300c605041c3e075050000e004040c28086c0500042020400c0e42c04004080d02c03003c2d892038080c001c030707581614100c1000700094200c02c0079500a5014503200752105e805261900e040d100e00d03042801101e8100800040f2558103400410446400d966180c0c3c01120180c01d82e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 267658399 1250 267657149 267657157
    0x80d15030512220902120105091e06121608010b014b0201020a03050c040f06050d0902130504050c030115050415090615080f0103020307030b07020109051f0c05 70
    0x51540e0000d00400b56414690b1001d00b030300e03051000c401000c9080d10a110b0040d106940c0c808440c02d600898291440707071070351443c0ea00603e000d1326241000e2030840c00b8800e0b203911800f002c0409001c12008500c450300c1340300000c030001c21114101c8101c100101e042c044441e5461003500300359801d000340106a544036440c0c80004002c440540d4000340030310a0703840b11400d402d0400016100c107100021a03100000c500ca2180ca803225000160756000c0c00e20001c09a41c00140101e2607144200002c1103100781c109898800ca40540c9001502d6001c82c0040030043c0c21000800b0303500c12021400d40021403807680c0518040e51188049030aa10201c0040c142a5452240d00151a680c182803c201038182500082c45090308011000e0317000b911580b0540841d50302d03030002007502001001c1d0180d01c5411422898014502c0c03400c11100c0e40c595400641d45080501000745029140008204814000d4020158069100d02610004d142c1c003070340303c2078011003441c2c2d03c080303581440f0020240138080d004071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 267659649 1250 267658399 267658403
    0x9100509030a02042f0406121107062708030708090a2a080604080d050601090b0304030e0a05060a1706060c06010e0912040902040302130507050901030b0418080d1503 73
    0x142c400d074040d603000c10001780004000100d0a00c5504802c852000e524100c00200c4c840c02400031382c40d0350500c2d01c002e003001e603c1c01c20000141d1408805002509444007a01c6009511140102d82c80e2306035010504e00c181400150300f83c40f0882401d1204121000ac043c621990169507100700c0c0da9900d0720f03560742d40d8411103000703803005070400c4403071410784900101d6000c820301d0406082d20050351891400d2410300100c609942d005000308810a07480910301425410907404d00e043c204160414400c680b003480003500050900c440142d000c0d003941c0381c103801d6400400d0003e2401b43c698002074806840001102d02c854002150140003844914100c006d4820241d010001818541e00303000a450359020040c100d00791512a40c485424042d820400410103400303c0c03080540c8451071481805600607030160031407a039a08102c20018a1503101098803101d0340b09207000f0480300c0d048030201e030003406524120680d00c81e400317030030500784621400185000740c42c43d41c0070072180c1a040700c000024017542c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 267660899 1250 267659649 267659653
    0x30506010503040605060109050d03080a0c0801051003052d161103120402040b0a0326040e0f0a0905100b0a0911030721060f081b0108061201140c0910050903 69
    0x3c5804513000713601c110383c80b10301030600301025600c401c0007442d2001d62382c00c1140010b001c001000490b408074015080b5030100740c20242d5240d4100f00c001014001c00d0304004041540c2c1d100000e0130820441d4042074004110f0703400ca650035844448482c000d21003245e0b51a86000480c240b0600584a40019403000c0c0c40352000d1402d00f2020101d14100b644040d00c140d03072242c3c0768080403000d603481c807002400642c0b040e002400c44484032030301c1071200126500030394140302c81403108000e40201c0d00ca045070b000301700c2044d0740e049070b17242180c0c4030007441865009005489200b1b40a4084025940a10645541210200f03032079a5a032102c5404d40e10521443c0c11701d14403e001007000c030b03409141c081c0c0d00260706114808204000c031540004540312907000c518801280c0004000203d014000c440c4c0000443d400000e1905034800044d2240102a24007401041c8515032041001c50030340c410800310601000b041e0040c1072030140824590802441c1601c14089270114030f440c103020740115000d003040600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 267662149 1250 267660899 267660901
    0x10212090d151b0912050a02040c0216032003030708190504030f050a060b0118031407080106080a02030f0304030b06040203060d0828020a0302070e0903040806070915030506010503 79
    0x7809502802420211800d40080c810954018110300a44401100f0f03071824500620000030000c0594a681e400414010001c50702040070880104100c0215a01039074041200103003101c08a00e04217800840c41c0326800c0540c408020070940803400c2d04100c7c0154030091610350314008160320b1744200c010081014034100b0048101003c81c8031174242c2c0d100b031400e05c40c0c01c1990387c0c0c94103020841030718021903080d00030ba02da001c10802d41e84100d0340c241c0820310b00300100418071010700300002960b000c06421701c040c48009008544007040b10318081c0c892040240581a41c42c0c981d00d5a5808059089100c0d028245056107260000000e6800f2283c01c040e200340c1c00d88035002440005c3d8000b500441d0000c190070100c82c00305001200600ca610100020811100e003001800c104840c01001d010341150004100500030940c0002c180040d144111524425a29064107c03444c604c903580c080384050241034100000035421481c02d0040301c0316010000103480705108100c045070b0b0100c0d503190104030140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 267663399 1250 267662149 267662167
    0x1c0503040b06010201020906130504050709031e080c0f1e030a08160e090c090906090c0d020c0703050f030a0206010602030a08070c020d0503031306060801020705030906070515160e010212 82
    0x1c0000360410818000140b078640f001000c502c1a0340400a000284a1702c0401006913041922907250302910340d00e032510480c0c2c21070340c400f014100c0108440b280088090f108805000c0980210b036a0140340c01d080341c0b000c44640e00b507103403204414904c1c4503801141c4071400384c10080100854007075034420344e10400c0c19a145441e400c640300d01c16036400100020b5030031503003445d01c6d0300100a00825036985000e44504120342003043d17030741c00101040d0148110703800b40000030200c17074180d400300c0e03000c40d80c09070b00e894a45c42860316110307596002411610850141c0a02c11401000809422103684d003940c145a8a0759001c2e40c0c4c0340320b07804a000000c0c05c00000030302000e219110010707880d44010b050303034060b14041d107426156400540f0f0440020b00c0b118a9902004003500c40c2c60000c100c1c0318025400d145180e01c07116260701a400f41103001e680c0018407002006411b0118103580041c610b4045d440e400e190b08941702c01a914034182c0e010813040c6504d60701c1c0d0b40c00000c000d00e85080e4408007034a0b03c6441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 267664649 1250 267663399 267663413
    0x90109020319020f012003030c0c10060608190b03030703080915010305070b0a020109061104081005010f06050c0a05150406140f061017090c0a1d0c0f0408011b021c050304 75
    0x103112143d0714010708091100301344024001127010b10810800280c84d00c0030700c1941818011444400404645003080802c111904a0002c3d540b103858941080b0060150b02054030280080240d100d605010000c1c28034109a0840764144c002c405080440d4801160b101003c041040c0c20b02001d081d90784003401c01c1000000503030041c03040014520000c1111955070762044266220b0f07084101074541c02003401d1000c050200702103c44208a008144201e5142c90b0f00800400e000e805034a007044400140d8000656041110b20455940f003804c0302c0e65408010b1181c2800c0100307480031218541066407000551041640103405480c1008107516503454400421031020283c600d14002d10810312024100300c10340c010028410100e130302c050301c0707981110010041006000c0c1c00c042410b40418444004584680c10f40980c0080340c01041c40e5a0072129609030085d00599100b004550300300006541000a041c0c603030f01d41100b081e001c6030201100c111100e46030100c5254540b00007181440010089181 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 267665899 1250 267664649 267664667
    0x60409060b04050f0103051c0e0d05160602070906050a05220b10020709230403050c070b04060513060206071b110a0b0415050306010e09040501060e090109020319020f01 74
    0x20032100001c21030368160101d400e4a07411100c103001007203500700410901c94107200140440038504100390a911010380e0181180d6280d4500e24050300e44078010b5070410804020007050090382c2d0708003501041d92000700940e600403e004850302c0d03a04080740002c0034108516108150350340149074503981581c2811035105841c0b5409090380c41a01c45a05805503250440c0c038411804650b4040e101c2a82032030301c00340566651000c4071105080b081483c800c500c181c0540c05400550601d0f103070b542d0343d1001144078541011904045004000010009034103600880104100000151585100c2c0c6d40e64200782d842d02d03001c46810001c15058003050a40401e0118400c6810744141c548000203e07910700070690100d059040001030240000c1e0034449001e09004130901c5e0b498524105140d03140c59800203040609429085004590740400b041c10020207401c240050060012566103e20b8016607007400380142003000d0740240990034042080e505840c10454078541c000c1c29608101032450011104141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 267667149 1250 267665899 267665903
    0xb0109050a14011203031506140f0c010f0b1e010906030207050102071e150903020c01110c1906090807030809091803070809040605011e03181505042603060409 70
    0x65505003035081144010b046a002c1c2034000c601c040084a0b91502408542403c1d50007020f0403803000c001c21000da80030701d00c900c2e1505203120300c50b110030b14030b0b034440c030b080c00303091030942c801d500785011005800320b00d52015550300c50480f90104800006802d4000b07819529003c2070028840640a109541c081c2c0c0083c01241d100710001890714407651603c011079000d4403103a030342c801c20000e074640a01a4810714041c103c5c0c0710035801c00400080d6030f0040d603104414440745042c0180c1350031544104506012001914001a2248425001d00810303a44d030300485028020218514402c0803400b200c0004c0e40105595002d0b0489107841e10310410032050f20b030000d11528106d86440d94104603a54203101034070119200b140d002e03403900c241c4000c10050340c009410043c1001683d00521030503001c1489800c0804401d0704000800a103a1340d015440030125803009000355420104010034501243c2c0000d01c901c1c05030310050008031455820303011b001080007110079980030620224a05180076440409124 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 267668399 1250 267667149 267667151
    0xd050403020d17090c15040504060e0615041508060a0e2e0803042303030406180909030813020307051818010e032704050a0506040606080606180a0b040f210b0109050a 73
    0x556108c0019090352015004001307091204800e002c1c06044c4030401000c08501150024103150402c441c1001001011400c6410401a5404030b28543c0b225007a42024001d01e640201103441d03c0910307550088511040c02c03152540030f0b0380303002904a800000030300703980808010350b10302440c1c120205089a0f09840f1952035841060100703085540c1017004200802c21510744401e08469520170781c05400c440d9108405407404c242e0500b001950141d0344c20350000788004111459007403400801d1a104080d0081c68005402c0b000d0501000346c00400f01d072050141d5103800b41204c540181c01403c1c0d4020030b0200c8920752091200820311850202035168101001001e40c0320040c00c200001d0664000b07560150100703540307005100d038a0600d070080b0742c080c20f007900304210282020070100307040313200e070340e514440ca41000f22a29019179900181e200091080010b260348a075112521071505401c14840c199042246444051a108020405182d03054103e000a401603182211003409803070006c012804403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 267669649 1250 267668399 267668407
    0x1005100e0414070e090f010b0a0b1c0f0b030f010e0304050d1407030c08060f0f150f09040303020301051f0909020c0f010f060602010606140f0f0d050403020d17090c15 73
    0xd41c0d020440d8000500082c00303048900d041c000c4545082c00e0030075003013142603412326111441c65154485c0003400c5450300940c0c507036074181c5610400d44150515040d08000380c101500d001c060b070101d8110001075035044003039134490401241414202e40303104a802031150400c1c00204007602d0044450a01d050240f03018103d0594845a03190500000382c00071241503941001c1030041c1402007083c0c55114040042c1e00f412810300306810703002410300400c55408001c054202d0107440c0c0390a950443d4103d4080c03c24007140c2803624014019400c02d0081d2400303104d20000d114590108084620500300c41a2107045a50703081c0040d5102070340c0000405003035031050449030001c0c00d2091149038040c501c0c10400183c42e13410300c40007d01350b845d1588010200102580c1050703143c1170180440ea103ca142ca01815038524215501c14682c0c0100c95030b01021510303000800003850b8011415000d802c150342c1e03895806407800cdd1750200c04000140c0720305405038480c20f0f07091001e00b84100d10100c441030349050a414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 267670899 1250 267669649 267669683
    0xa0908160b0403110102032a09091015091409060114030906160203070312020c071d10060503040809010f020c100e09100812070609080403030201020c1005100e04 71
    0x94140810201e4001c2a9281084145a40203030700c1104607540d030313000703610f03604011080c2401000410001016440c1d004424660400014100ca5510001501c200e0184c0ba242900c900040c80e01e11540045400c06038051600ca4800c442c00c4003030b00c2c41c01449200b62a8000d042c0140c074000140442d0510902808c505c5814a503000503520800ca454000d08d103a01c0c00c01e0040802d1607582260100b50340c01440440002070f00000428182d8410300401038070341030743d0000e5a103000e5990748118107c116150343c4000701c24074204840c0c801c00c8082000340807a85d480c44200d4852101310b40151151b082032000103c10341c820090442030390f0705032044270382a001400010f03440c0c0e04041400e6021403e5024448158100100744651056011800000c11407900c180c40da00c81e10602085040a0fa0000d99441000300c15840401e5164100c404a40c81750b8036031034068000e40c84132540348418820b028500c10f43c6103141c0601446103c01c0d1070020402c603c0c0c00a4840c0c5400003500890710f60049603840c0d99 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 267672149 1250 267670899 267670927
    0x21061804080c0d030b01050a0518040c0f0305011415090102010f0c0207060e09060306011a040b0409060806100f0524070b1006110c0105071a0c09130902090a0908 71
    0x40541d0140300780981d954503610078035140928011141c01414180070405507a80e170014142c400d03005c4907080280e40c9000300300701407049034a646929607003d498003982ca142d4a6108004000c20401d07600c08204690b00ea10000c01150744462080b036000051046c948101c1c80b029014000424042c0004102503a121800c44246c0310540010001640550740c100101030b84910221900042524001100c0c201000400e80f1100140141a074a44031002c40c031107100300d0001100c00922000070200d844e191100310342405400244540e1002e0312500d400b0030003940a1810920131240da68070582205440c0c0703003d02c10328140102c201100480d480348035245e0005182c009201c400d104044010591411058503802840307182c20120410428620040d01c030314000500700d004540900740551144481d01d84800c1500900b284499490300e458103108040000901600d00402c040350755002e44092040c003c1d00310340c01c1c040c01039401103000020503501034141d88607482280c09010550310b850500c60b80f040c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 267673399 1250 267672149 267672151
    0x20f0d060c030b031e10090222050f1609090e010209060301090516050f04030201030b0f1e0319050c06070311030c07030201033b01061802041505210618 67
    0x2c261640c520500501d8240b1081c0361800b49607641041c0107541600789075440da061284407a10343d558400041c19580d80118441041c086400b89030000b4a1804011001d0a800e03245103503514015808960040c084500c2e0b5000007880d90789280f005031a2080120240412411190455500308100140c80e01c5100c02035001e8000c050300402c072800c028000101d03040c184444401000014000001c446451000b200c0899070240303800300d0181c0e10807001900000e444620241d120041d01c4c074500745048000e1a07800301e848120150386001d240d200701c0030181d1040708401041500722022400c028030b8410007800c0303990702034944151a071f48a06044c40c51984a20b031301c7c141c107610410040003103680c5030160416030744420b8400700166000384092041d22074900c0d01589001540d08400c220410254010402001207098842c5581c12040017180203621600801c810b600401031041001c50248007214050710129903d440c4844081560a0255030041c0181e070340000d4000c88020011080030002e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 267674649 1250 267673399 267673421
    0x70e0d061b0507020310020a05030f06040b1f090605030606121b0412060507030603020d0609050109200f0409110105130b03071205060a08030a0e1c110a0f12020f0d06 73
    0x401d683d410703a401010b103841030019a1102c450300422445404540c03000c05c1d80d82000031500034003050b86a80002801034038002c03248a40050740305004c06000000c450310a039161200b903c40e9000baa0300e4a43c212640e20088038680d03000081000692660300d080c09100d41d2109160301a042140b004c224030b2045507120794009041c0580b80591a01407200c14032520b908000035080800c542443c5074040b07181410195800b0740515a17032a619400e1103820341180081c0f50303000020711131030f15040000040c0041d4402410b400f4201c05648141941098410501c00a0b04660002c0c81030319241c0046843c3c5c0c0c0100c0307280c124511040000180d0028003009140500354944600c5130002e001000d00b0104d0b50001c00062085002d20010080090080201c446081d80c41c41c201045040c02d001107104083c4408607106010b60050494051105000c0780d900c541d40c0403105104d06980d60000d0f500c9625080c010b10160f02c1072481654014501030414032000480944a0316034226a034890f2012035440440e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 267675899 1250 267674649 267674657
    0x70507030c0f17161203180e07020d0302030618040f060213210f02090c04031e030e03070614070212061317040308040909051504110a0608070e0d061b 66
    0x828007009824a425003c4a2400d070001c00145000114040c059043d40c450341412411852a0700103142c800c0d21054100180861400344103a43d507110519a058119003c0005015008071030010510a000302c9020340001001036500e243c1a803482082e038038024104035601d000c288d107036800050030b500151022038441c0d54160503807843e00c89030700304092207a000e400180d11000c0c15800040e40c080100405160155000703545a944c2c2900111648625040500304c0941d0a84c282d480014800d0110746680c40b03a47c465031604094002e050f96a5014040c16001c101821032a0074820311040180c16014001480d8006100c0803648241c03d021082e640c5542800c91120792005015880c1d80314980c1000501d2480d240074a152212007080c001c5000b0380030707800c2d1580441c00c2030240c100001c41d030011203070350302c0d065038209860101c9001c0d9100300d4480c0110b44428001031224007a00c1c3c624071400190b162811800303c1c0c042000603171440aa8102d503a04d0f90343c1ea1034a08260b0b03100d404038401c8807030b4507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 267677149 1250 267675899 267675929
    0x31a070c0215030f07080f1605160602091509150306151602101107060305040c080313030b0f01050a03140106150f110304080a0210020a06140f06180c070507030c 71
    0x14400440c13401840901441056818001e60b00ca84050035070b0301500050003c1d00f0720000c3c10302107609205105001c142070a004540105100e140d900805442c60704551143c0e8910352000e04000d41e001d0b40b01c1c103d03449002000402003248002006581c020b4004100d4100320072494a09034140d080900b8005608600000d11011820048000042e000d4182050b034400701082034256030b00e140314010301007095100d0000c90100802c1c00c03580720180070706009480d2200b18101e101c1040c14140e10040c2d03041a00d0701c0100303030300c001f40300842e5043e43d0000d02010800350858482c0c02802c030740c0201e40030240d981c94000091b41500020315040d1440f465440465864031440d004140401610020750550000c0004010120300040e000c60311990640742031aa060003040280d051002089015051074100840402001801100e482c41894500000c0714640c5544041c0240030801b2042e0704441c03520b10004c200315201180107019560b21601c100c4070050f44030b50328000b8681441d4050004107010b11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 267678399 1250 267677149 267677161
    0x408040603050f060303030621030705150a020f0d09031205091b01020f0d110307140604020406060f020a110409083903040612020d0c090303120204031a070c021503 72
    0x20294070f80000e449801000e5906112002a40324400076001521884601c40e42540184114280d401c1e6002c661084d00e44400f80d50504a40702e18a03584008654620b02c00014007080d42442038843c1c43ca0311000035810802c110445400400850030241d0030b205400005038001d003210b020b820b1041c501c44000d04402c82c03032007440c01200004080040c2c103540003495690b003013202c00203151400600354034050340c041c00820301060079480741d914003070004032080203107980700704c800107880e80250320a0343c0c00c1107019030390766045404140c5803548800580203150000013040c2c6c010350039101c86000070f00000345e100076990355200644c852070441c0352170051400071405a00d40359040b240501151074104020f1140c18082035182c2c03103103003c1d5100780031203136140b02504291603041c0c540e142031440f010081801d080c403010b040c0c2c0560f8403088000510301c08034150700b890305000b80d80440c1da11100d0148400710341da01d00d04204800501140030007194081c40d00140c0c0d20015003040152038210019030b2800c1c08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 267679649 1250 267678399 267678401
    0x20a09050f0f1e15041409070302030106080f090708070e061201020a2307020d08190306060e060d020d0c0504080c030a0f020103020c01140109020d060e070c0308090102070b0408040603 81
    0x1205480c41440d02e00200b0311035803141540aa03440040200300d00311412030b000040d03022510003420210010700481c010410036030f14014038403000000c941000181d070301d40300c088007a84004d005003000925408003003640071030f00c00000c542042104042d141004d40b1008105d2800440382d10100200086a06000c0c5034208407810710384007022640250f203030501c0010301610444021001d144428110f452011524003540c050f1481640d000304040078240c242e04101025402244d5180d0403205500250708d4481e00905c80d54088464644614141050441c20081d0340d40103c6450070032a5001c12100380c44251078072807400d00f00f503e40c94007519036042c9211b003898504065401f40c0654003403a5807030085901214407a0703c8507030918015030341d0040042e0140c090031441ca021942c8040c1c1000124801c4081e40150070403030b41821081110390303a03c40d0381580b105004c0e5441004210a02208000700b40308106032a840b400c0d65002518141d0342ea0b8070b000c881441145c0076141d6a80209003880042e40c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 267680899 1250 267679649 267679669
    0x509030d110a0804030c060e030a030509011d070b0901050c0d0f110c0a03080f07150b03190b010603050403020708030f130b0720031911090c040608070e13020a0905 72
    0x1d2541960034000d100d503010b04980790280002d01800180e516003c1008499080440303082480803d49498a071114130250142105640e209019400d20446040001c000e042c2c55032401d11220080446500c0e107a51490303194080c40c401e6041120422807a144401c00f00018080d06000f40e4078030943c842c030154010032520702d880880301faa41003c800003c095444101e0075040da50010301c0c007a96800d5400380000700b4840d41c0401017004030302402c546480001e0354882c0c02c824405500b542c04c0600c1601069201e00c030105c100400b051004001803000c0d603c02d5100c20745c0b2611900403500055100c10740c491031078000303190f02e1811410025058400001a03103c1d10020058401e510b4200ba904c1d40e510483c105100610300c102211300c0b40c2c080d13010350b401c100786e1104d0007040d40c046c10076003414240050120303400807144d4007410440000c1101d079000b90040306c0407a20f10340c1e550401c64994003000c0b81c480641c1220f40e035000032503515401c0500b15030b00c02040356a915803103584000d49080e007442418a1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 267682149 1250 267680899 267680921
    0x4030b091608071a0408010f14090f0604080d140c03040201020706030203071e050d020a032003010b12100312081602060702030f07020d060e1b06091003090201120509030d 75
    0x210700c820060710300009120415540050b400d0403100a519283c0324590003540d100100b50340c02c06e01c5081c40f20302d0780e601400384110a82c10b101c0b140c1d503811b881136a9031071a41e0000f11559010000007000b04100102402e03080c6c11444021031041d440d003d41009000c0165060082c070180041400210360b01004200001c1c40c080c1410340c110318001801800e081068490401044425802c2d40405813150080b98010411480c0440d295005214000c00070402217440011184181208000707403e445810b82e4100d030301004295113056a180180c0c4a0004041c01a0280318880440440007a1000030b4010b201036095991600a1410b03060b02c0c5c0d940c12030744c3d0740f060079900920180415141c0c00b0080301c1160341c4104080c1e03510055440860513445040d071010b41010f1402d501981f004101140c081d21150008103881d035000ca4003000c00070b1505c11103416552020405a101180d64025003000c000140141407540a100d03054100034161102118580000d8200041c02c604401641c030030058503031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 267683399 1250 267682149 267682183
    0x4080d1404031b020409050f0703020f0301090b06120106090603030c020907090e010501050c16081c0302040b0301090b030102090d0501020a020106060908033420040b0a0b0c1204030b09 81
    0xc285074030080e20429a940f20b14140c410b00400d4070056490355000310100d16409001c40314035010404d203150b00c0700d2041c0000c903c56089014051500d240500943e0001a0045044015516280c0400c510702000100e6081301d9521003800045400c0340e84a0100118000c0d140c105402e20305204202e5140c800425840c1804200032040c030000450354801d9040d1542820890794801c592000e961404903001c40095641e42c00600201e01c594000c500040d40005c080f10036200c8525030082541079004501801542c08014001040b00040300d4012044450018000600d040200000b060907a94200b000340c60341e0790001096014603a0912410004112524000c8031290500c00495260b00c9402a00030303058010411441c64950b025092507000d00e603034101402c90141915040c074810250154010001100c7e000d10100e41c1030500996007500c40c020300e40c042041c02e150190038640c0168100107254454001d2032280300d04010700900c05503000309000c01d103500d0604946841d2068064011201c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 267684649 1250 267683399 267683401
    0x1b0f0312010b03070c0213020c07170601080609061f031a0114370b0403032105010518040503130305070306060504090510200301060807030608160509060f040504080d14 74
    0x1c81d80001180c05095044030441c01405407000087d000e809034056128803030145100005250807086040e0b4840d00c80f600a4490aa80c2c07401001d485180807215003101d60003510000d20403804814012034848088401d0319140340d2030b0344803c010046d08110004101425100501c02c0e01c0707200c10181c81c900c0040365401001c041c1c00603203007000d40c9885603031103001d0b55440500f091200d6030800c84020b04000d0480e943c5503956410020a610704c64100c0301e0341c0e24400d200c440b0b826040d83c01002d058400c0039005040e10350140f011039401c880700074020782d4540018005c4809102c40d41f4440d100540c0520000e04400e0700b5801d105044410307e601c164452031921001e03400060011500c0c100100411070000f4480d410080410200700c184a0b020700103160010001c0790280d008281c1c0d601485617075404120241d00c1d010155a0390058044605414022086c10401f40c036012148503803100c0d01030901d4030b00300b140d2004102a900e0655044030b60b24030115421030202914402d078442c18030002d868040c030b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 267685899 1250 267684649 267684661
    0x1050414070b070807020a051512011d070f09080d090f0f03030c021002100203070f02010c080c0d1a1507030f0c1106030a0212010311030d021507051b0f0312010b03 72
    0x2d580706100d801400000080f8098056507240111000101000741009150388001010b103050383d0f121419000d4007180410011940310428080c0103040e0802c01881c03892030b00c0d81d24042c0c3e01e1a1582c02090100000b03141c01080400f824400e0042d41d0b881500d80454581c20300114060005403904004c45101d048002000441c2e0f00418140202d601601c0b21002440f01c420b040b030801e00380602804540340004144121180d0001168130300c0d1000b507000f04544049550100e504e02029516030b0a038180600122441480340c3d44040a40746807804120114229840400c10342102d83d42c0300300b4250008500f81c420316800c03207400421540030749061081d00d4074680c1d03894403242002046030f004844c040001514000594111040c0405185c1400c03204d694030315104401840c3e01c0b07400c1e8000e025042582e40800c0c000a1410080b1500601e10302040d1740d42201210349400c922400101c944001c0c04c1034030503100c24003c003a03442d400040503640e1820f6500c2805440481a88500d60303140c010410851 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 267687149 1250 267685899 267685919
    0x60102070b1e2d090a0501050a1d2116052205150607060f0b3309090c04060e010e030606010c081309050105030f0703051216140105041407 61
    0x20103005042e5403241c440f481d400315114103400c900700c944103201014a107240032090745005000401c500f2184c25400a460364011075603801034031100b0000c95404d1001d10340058030224403010040d0060100c880d246a070796802c2e0f8060a6000705030311144c001000c0c81006113500c03103500c00904410784400c0d80d0681503510b1548003901d60041ca03401c595071600880c64000c451203020510900c01020b041d21a222414014000e142c92900c074500c807440c14070a00010704001203070306141d00c85480c2c1d05000c010141190004d400551a02002c560b0f01081391140130750b516842c842c051641c5150b038584036400c0c0080a0088503070000071506024810440c2102d0740c3d800105030b0350204084c0b0b8031400110580c500080c05005040302c0c8903c0c070440314408201400d050380214103e030001c0342269541d81202d80748075100d1402d40005002c07900969651100411698001d00c20b2510905000c02158003e440d4465480315650700e501540e515942031000380a0650403050030324a4050181c4011450480140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 267688399 1250 267687149 267687187
    0x106090302060304060507030609021917150402070809060a11011103040825061e18050a030c05031201090603020f220b01050c060106020109021509030601030b181203060102070b 78
    0x1780b0060704c80300046c0005200790000e9000f050701110039500c600e459800c00c81b0340c1c051115036400007603e140600016070201003c00d4010320085c0350100720440c1c0d00041c4400303940001d034199400e00e800c0003154040d031104802041c1c2112980c3d00d07070078541080b4580320700f0b40b24000108600d40000b80b080c8008901001e0440383d01c000b101c0381c00110342c1c0001400401030100000082c0005d4035140c5459140b50390702e1506001003407595400c10044555080100080c141d003d000b41082c1d007c10120b2002074054084448158041e0085038144555142d10034185002600060f001549610f0100110305002d0b2005400c03505c1100d40305410001d0040351710003001c4a5284800c440d4884090050300d03400350f4107c6801000681c1546c51541c0c550740064003a01415008038000d0390780715945800095890705583c0014001009000541d1071a100d0341e45c150400381207072984403031090240034080782c00c011944440c54151688c036124a020303800a030400f00c00f90320070300004404000d00900000381810207 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 267689649 1250 267688399 267688403
    0x1802131a030f13050708061906080d0315090905010b130513061a04050a0204080f160e1008150603010f020a08060d1a0f0412030905061305030d02070f02090106090302060304 76
    0x41003566004400581d0a60480d000344c41c0e80901a0f002c0744059021401521403000404008140c004d2900504101c1c0c90318860081070707801505203881814400e401c1009101c100c400740d2051640c03110000e4040750440e80040360b09079502c100c20f086a06203004860028405100d00700064a0f0810b5000f00f180c034031250040140d036850b045034612440c5071010b0702c010a40075008104615001240304000d6225000b0304580d4031805800c1206c0410024010724500c10700804e10400340d03d40b800c2101e412001a00b00406030f0001140444e07101c1007005007550f10b50080291801c0b1b801c010b814142150201008209280e00401000c02000d0300940b1031078001e24103546901ca49074080c1010902e4150880703840d6111130340041480440074074070f0401030099005001040e40c160100c001941100c64031000104035800c91000265070510b2070b1116401a80280183c0c0c2c60240c811002070100d030311400c2d0488034481c02084020070b40c00c102840c180541407504052000c00cbc10350300051911f000003040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 267690899 1250 267689649 267689671
    0x1e05092806120615050d0c0306020306060d0e0309040507050918060303070c0602070e010504020315010c060b060c1501080304030c0b0c03040503010c090510141606061802131a03 78
    0x4400e01010040c0e01030030040075000001c00000d0b206140260183c0781c044c1080550440012021410b8502100030130890395000300c03201c145914540d43c00d0040d400003018103501c000b0500c405c6400548500540c458130a0413400b540c0e8a10800701003100f120300181001003040000c1c0010070f10b42c0c895100d1854092884a4403d0482d6640300003e0718521500700003c099000780c2c04002441d039000511003050310820702d030407409030381ca0f8002d010403400111500c0005918a10006040f540642c01404083d030040c000411032075108000320b1007540c4100012901548001040c4070400501d440c16800341c100c04010310701c0d042c659180c1d090019600d0140000d8000001040c001c080c40030000c0f00c001382005002413010b264100c101900d00e910500c81d01e401030300a890b000603094419913119288102c140302c1681801c00c6151035028000d52100c04a92031035071102c001c1008001c96040340e14401c0209000741e681c200329644c2240c032500315407040d88607608240f8070012031403440c03054035444045a54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 267692149 1250 267690899 267690961
    0x606031e03070602070f0b090309090f040812090d030f11040303140c0d03050a1407020a0b060d1407030201090b040b04120c05040504050a120f12020705070509011e0509 74
    0xe00d0342103202da01401400c45200160190030020780403c2d0b02825030280580c0b401c50f0313543da285d540c1c49129500829034000c8007200041c414600007a082604680030355503040c1058104c005480417403109590700c1c0d0407a881103124070b84e020340c1400394180d605e0a04001748058a00700382028410300407804000c090210401845a4840802c01078400310800401103e0b001500050041c0c000d040c140c4903108050705007007640d4980e07078000800d24013074000ea500610055189442c0c0300c042d210050700050780b01c1951610003011507410b00410103114501d00213404080e245200140030203460354049010050240802c000c08070710741e030603070f0111043ca10301c00c1110750301c0340380c05219007280390010795009113824140810f01a0000b1071000040c41fa55031885024003000c07040d01c400d02d15114100028003a154440104c81d417980240a00f18404c00848203015111300004001c82c41c01d80002441040e000c0882c2c400700e040b0003120004007800e40c0c800340c260801038030107185044401104508501c80d10b03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 267693399 1250 267692149 267692203
    0x31e0f030f1e0708070f05010f061203120f0608071d0c160c030212060402130506031009210221090d030c050a230c030606030307020d2907030e060603 66
    0x40d04450301d19501c900c09a0ba17a07803481c40d005088280050003910b1751b40ca4581e0307164407c1c51500c40c1c181a5900c040700b2022444c01a40c080380d450f8100c60703020050b9a228a1140000020790042c00050072001d00581007140c10810a0702500d44d4903444070040000d03013402c0c03025140510040f035154140c015000b001891250502010440301640001d4021a503094421234800c1e000c121140210b1003160381a070100a220303405030030f84405075120340e85904a41c203404590300b015032000292501c9030348103d60200402c1a1141060b45411a80340560460300903203c040d61007041988503412030084041c104042080800d0303980b0030090008091100c41d06240c42801420049405500d50100507420300400344400c4070050351034601804128401d4207900e104031300e400700300140f0640c2d018001f50f00309001034081048500d8100019076a0f8050441000c4880110040c1c884c0314842402200c000e0303040c0041d00070119520600c3c1500580c0017841800300565010868003042c444007c00020b11031410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 267694649 1250 267693399 267693457
    0xf120a11070f0609140d21030908040e01170703050d110313230a1503021b07060201021305030109032001022206030b030a0b011505040302031e0f030f 66
    0x15800508041d0b40007203001402c168070410503800d80d0704038046000c0e880c24035820310140340d0250700001c2410644425141c542c490341480c11400a407a03141c007055803502d986603051180d00541060b01c0c192100c4005020030b404c1c995940b0b142d901d41400400c80300b03107982c86a03500c45041440c400c0c10890280d041078040c5004001356285900168010340f03031079a880311602c0460400e030301c0c1062030f619041803041c0a0702d803041040c01158050249881c0c80010307035104030001c1d4402c982d4090719407010b240fa611401d6040002001801154000607138038070310704284001424155100500ca603040094004c0081c1e4071050078000008040380031101c0001601c1c09a019001e1442d804418002d40f0700702c001e07240d88400c40c0c5000c46e0490346042094030640401d02d611080c80b040060201500500104900400e07142454644845481c0c61824151030b640000d01701802544da41120880500ca0080300c06014001c44c00040c400c980194500a80d9000b003074003e0282860545800e05d5000011040c8208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 267695899 1250 267694649 267694663
    0x10804080f0a0c021f180e0c0a090b19080109020304080702011d040e0601030605010602010e06070c0305040e0a021306020705103203090105070c0804030f02031f060303020f120a11 79
    0x2005001c54226002a040417030240e4420103040f000416410211000481441c1e4820a50304192226407041e618004510540d80c4259070450403c054018000b403640c00d181d0213001e80c0d51030441d140f00311401e681c41c010800c0e81c042c1c1180800520400130f10001660702011a9611907081c20007810b04280c540901d0480c0040802c1c0700c0e0801d062540c0384040240c04109a4140c1e4820002080a6621904202e081360400504100e03994001004510454011903074695800e100b8500145820b0300c9140d01822060300b55402c03091a41c01081854a802550500c000a05400c3c4014980d4900d400001365601c0c0d45e000000c0b0510021407000181c00042180020903000e111100c02170005480041c0f80c65548200c40b0a01a5481c110210f5007503489850602005078001c48078604213400c5488101720790300c604208036498403074001a0b071f400344075002c0d122003401030310358000800900d58203012307087c013208020040c802d4100c8080d804040f0601802e403031029040789070060050085050007460050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 267697149 1250 267695899 267695903
    0x60e011205190509070302090f1b0d0203060f19140d0506040f03121505090901020c011d070603020702060403170705010e010506040e0d090e090705041803080105010804080f0a0c 78
    0x41031104100d80b1110480d01e075060907007250420403880c0d803101d40c103a80718249800001e41c00a940000300d601c04109140e1203412060744e01310b20701480403402d03000149500101e1035580443d004000c02c28645094001c089081c03905480e1900108400c2e2400303034400285000c0e01e44040b0224080807100c0d12602050846207601008440e014109400c2c260365280c030704101100010f82440c80c0d0b032000906030081c0d850380000042c5441d0210f0030281040421040101080110b650a122010127600d00340105802149041742e500c0c03005024804860502046800c02d0050500401c003000050315003d00315011240c008800030b0000c0440203e1315102d12501401071b01e40c3d82400035000392444c0641c012070080d641103c041044100c0c1c2020329803a5a4244d0b54180811030780300741006440800300180346e1200121040c1c440b040c3e101c90018044031015600a016841100c000c1000c06401c60700c07080c05000c007428008524942507480e11601e106994104008078400b28810034801c2c09410340e080955 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 267698399 1250 267697149 267697151
    0x50d120f11060406090b1f031e021c03080106140405240f09040b090105030d0804020109181b0503040c140301020f0f030405061f0504180804180b010315060e0112 71
    0x401c0c20306040c0003170124103000303982c030095480114a483c5101c1521a980e4400d00704905d0100d442d5440d0088447c1140d821100840c400c100341c0703070043c3e4032003104a50046602e61010103c039280d040c020040c0905030420300c20b00020b000c080408040c06070659003260f90454a40070900c91400080384000002031a40340034200c08102002e442c003000c8040c04803440706407010806101401d0811240500a00c15180c0540050469660403480340038500d0f442030042c1841c80c00251b0b9440c04c03040c2001612111140981d8509407000610520320061007805058038220b802d50a19480349000889580701e90b804250a034032411a00b40ca003034054807041802003500315280c3c801820100c100d684200c0e000c55072800f030320001a42d5a00640d541613607608003940171504503800c03c01804004e00180c100601c00c0d044050b11312000504400087c001b03040030410000c600c0c020f01c110700060714030b400c00140c145070034a0781000c2c9400c5c203011130400325481482d0207802c0d40804001a110f180a11025522503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 267699649 1250 267698399 267698401
    0x240e0c0d140d02060405010c0804021e1f0201091a06010818070b040b09031006030b0a02090112090501021b06042001030e0114070e090402030d260703060f050d120f1106 74
    0x390300851301503c02c0e8081c10083c056034007840422141000107d0b0002e510000c1c92a1140d86107000c2e0404408500003e001e841d8414500c8001680c01b0000e040da110042c0c1d103442e01c1d0700412510b5140c0f00f0140400070320032103241c2403040c0043e1034944011701c0c0391017800c0341604100200c1d604210050003010102c03c8180d0743c6840d130310b0704d84469002d0500d15001f84a0404008040c800c98851502183c0d000018048242c44407901c000180d404508101c2c100b081070811202c0020803840340140326407107400010780c0d405601d82c040000c813401e9058000e16821040030003011510720000422840189a45980c0c216030000040c0c005088100c07042d04a50301e050240100800100c0714113024034510307114004c24003c0072080245004084900a4241d004102a0890b0500074002086600403080f1010380d0084005807a4844144c00c0310001c1c00291942801c003d00b24403242100050030b016520044c65800c992164130000058000c0320080048000c000c0500e20b11991070f000c4491b81c603005443d81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 267700899 1250 267699649 267699673
    0xb0703020715051306050315120a0512030105030c06040303051c060b0a020a050c0a060210050720060105090f07020d0c021302040605090a0b0a090b09010c0204020403240e0c0d14 78
    0xf440d041200d800c002c0b20082400400c4050103002a00d1280c03204001c2005610010030500481d5111100c9480719031250f140910002441071010341003042030042025141c1d8940000c15281402e0030440c20701906c1d081006001290b4407100708c03002800e0b240002652440d00ba1060380c010030715a4090140c840000c5155019585d0200b044150076011f403044a44814008082041e200407034424079015038040c001d0b03001103104982101d50310030402d04100303c100c0c481604020896085080001c91500000300600c858a031440489070440b00c03046412919141440c400795445103080319000510100c0d00e81b41c0110b6031081041c045401d20500c095440300d645400160107904403180841c03050324200c0020441c25100f400b55035450109035910b854203450041543c01a51141c41c0050420090b13581410151711503000500080d0710130300c003036100e2012000203e00b040000c0c1d00c96500590802d04400c0c14600f0010344055821000c640d120b210744000d10308820703a00d65004640402d4001c440c54440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 267702149 1250 267700899 267700907
    0x1b030209070f030f05010f0302040510090e0f101820060a02070501020c0303030708180a0614090610080309151b0c09090a0b01170a021504060323010b0703020715 71
    0x180d181d209443c1072104030a103c10030815100d003401074070450245010100054035117034200316040203402c3d803074040b401e0321088141c0c185ca6582c1d403410306130343c42a050404a001d00304003c012074090503004010000c1c006403040c030260440940540f8010ba850710b8042c0c0748107005810f6031110401003034643d031503000960203900c85070302c0c0c0314241c09400b400c1031441840c1800700c11280329070741e9548d03040c10b42c1e036840c441d1480d20303058030070404014802d540d0380074002003540c032481c1280900c07540c000f01c00385401011585804c00c002c00c1c1180c252000001041011000000d40300c480c2003c81d05a0900303004003104034170314023030030090340881c00c0c1031b100d600c412140110341080d0001d000d483c400d0450f0b568100e036560b124001c10004018030007100040042e941e203260304040c0c8444000548180e25042d03000106444283c10b41810748020000c0d0030031001fa010711400a8505032a040c25560b54114111200540d03030500c24034160440000d144400c2600c00d00c0200c0142406018448200c03183d040d00030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 267703399 1250 267702149 267702167
    0x906240307030b011e1d07110604080d06080a020a09020a05070215030711060f060d1a0906060901051e091315060608070e030d120e01020a0201020d0c0807020a1b03020907 75
    0x4607092000115030034140d0a4800c510040c0d400c000e9036421502d01464201a21040c014a0281040008e00600c2c81e40001485040e0056004400d41511070b01480c03500e408885180c2d10580f8558012504400161a010221000c8078141400141c13140b0324401d06951912450b04025440f000354030000000130390326006503000d0b281568460548488132508540d03a08415600e81007030f01403000024140340f0b049034100803076520882c5042c0c62a08403030004031100400740d4280490303030804000c0200d98180326000d1801010129000f0000000b000c04000c01903482405840c084c1043c2400141540811f501804d07106501807028040100d01c8a402c0000b800310b40500800140d200c00452103452056070340c1d00313222500030003500c030103c0c0c4035070280c03001c1c4120420320341050780f120507464001c0c50070301c06040a080f654002507910980421440101d45009a9000502a1400c14000c03d103600003400c084041e41702c3d4182040c9510b6052500f140b42e40c50f40025480980300c810485441e074002c1540b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 267704649 1250 267703399 267703409
    0x904061e06030c0f05150d230402010e03240907030c030317070c0b01061d060301140306091203011a040f0f170c03060a020d02040f08070f06080906240307030b01 71
    0x10034459615001d800611515911a107640440c0500b030111b00c0700561b100401b00444050b02c0040c003031030560124408021090521040e41c1588402c0000307650300100070b1100d1220440140801c123031083e40002c0507240c558842901ca00603900010b000400800c10710018640000613132554030303901d1400902400d0068041c40b040c010300404525040c1c0900d81e00c2c07405c030f54030040007901d41c1e0078114204c2d0030310704030750000003010b03200402c400003074a88400031400707004a884e60680a80c10b10b800e0503c1c2c0100580103d00c0c5911201f070300c152100c521010340781942c1107131003500c03c1030711001900c040d68004c40e00810500e41104400040090340b0608140840f0020014035021031002c8052540306c030f240160317441e0190001c0c2c000400c0f03c55a94001c040380001002e00504103070f120000ca2075070a001f500240c0c615400031105000410000496030700429040c134258066142c0714101d1900c400f17001e0180201c41000e01c036a8107400b00c2591130301c1440180a070841c0d104aa4a0030500d4050000b8443c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 267705899 1250 267704649 267704663
    0x50f07080f07060e1516050105010501140705150402010909060b09120c1f0315080105011d07090315020d05190e030405030a02061b030a080603070f140904061e0603 72
    0x1203410310940850a042120203d13210b00d80000c1c2c00c2424003050711081e80882800036020030802403181101c000d0380c08075501840000903190306000016003140001244003225000034410075002440c00548404040401a040703001d07910707140b00507a0802000d40184410a00b05400031410592400c003074418054100d03802000c1c0700701c03900550303103d03940401c480e48c006009044c0010b0031410b00301140d43c148654500040c0481480000305080742c001c4c2c01c2840c490351900010062007244880020070700740c1c1041800614205000f0241c8801c00d41c1c0300050013103200e1984044646800c1d81950301001e1a1202404545015800d50785040c00540800500c64909810750790340c20320000070303142500c070090000c0c460700c1029001c000d0079811450400108050045840101c080103101800407185680c644045a01b001c100b01418017450ba04100e0400d01c42610400c2454682e4681d0841000203503002d40b035a4946041c01000340042a1034001d00403084000a007000d1442d40c800c1c000c036405501c0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 267707149 1250 267705899 267705913
    0xa060f150602030a0e0604090c1214010e0f0411060d0506010f0f02030414120307050a031d060301272c011802100203070c0e1504060308160f050f0708 66
    0x100340c290148050080c2001a40240042c5142e00e02404240c2a40d0400800a5041c140c3e2100e5050689488400200c00150b180100090400c0c05001e0044040036145050525604000d4130b9004184010980301403000314001050034020a0b1000d90b413148006040c89a80b101e0744006440034090680301c03540010b441c003c02c00381d900c1c401c0501007070f00d941c541d01941c42c003440e041c5c40d41d441c181000d114640c021400340344070700000002c00081c00e940d441080941420307095800d02524240c030000e940e440c0210841c1c20703c0c0083e03564104807415552422071141e4404010049419050303022541ca4900b00c0c80c3c4980304c86052050f40b0802402c2001c20b100d01420030000961724265003181ca41941783c108108900c00c011300e4496981142c492452044900301a800e8583d0500e0800b40da21a00d0b00c6a4100d0501000316401d210b4240300000541d0288165403441c1c2d2540480d214406140c00900300d44000f1804021102c81c2c40c0c16010f13000310896014918072001c581d10ba428510580303440e481804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 267708399 1250 267707149 267707171
    0x304110f010809060109111911161d041412041a0408060106270605031b0307080c0f0405040207050f01050105031204090c031812020d020a08030a0f0e0a060f 69
    0x898180f06440c50805080e060f441d098042000e07002c10744600010304401e014074282031b541601c040750302e400c1d1a03440c4000c1c011154102403c00d082901c0c8030480c400f032180244080c3c2c01c000346d80c04040c8800c0010300501d03505c60419a400ca01190540c18560007000c1999000c0030505c009001074540340070300d0701c00307161040b44503004c648940d00c201c0400343c00000c010081140607002201155124011110128100412200b00d200007500720b00e01149002c8140180b038000d1906154000d410a40f00764514241004041e003a0340f401881842442d8002903006c41c03806408080d1030013400040c209544404440c0b070411b86900e83c104600d00c5035841e01000161301c0c0b800003040b20303034010303075031125840d150030301c60698003602e03923000d0003010305464490300020b0707160b150b0a4042140c02026030202ca80c69445c0000d00341150400c64108640c401c801c00740c08100900c04403904808908030001358500e6001002d0b014001610309082030340160500b401c1440901e4005180c01640c94030f0403c20304060ba = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 267709649 1250 267708399 267708407
    0x72a1b06021f0f1812030e0715030207080d05090d0305010810050703060504090605011409043c150c050a1b050a08040320010302030c0a0c050a0206190909020f19030609020304110f01 80
    0x614400301840e400b20204005a40034200300c29500c09e0039160243c0b074207181c2d80f51618190300014410f58015070700d000b0041c20901c03e01c8078110040c42c0e0b20b01404039525000c44c0c15950354010981c0b001a564a00100f0030b20360080d88840c0007440b0290061011040320704002004003802d01c106030034006101c513241c4d0640b0b13000300003030300c00c5070f010040000c110304a0b0702d058a0740b1040710314060300044d00d2030581c00d1071542c94609418107105902842d00402e05070515000d541c10321004009201c018070a42980540020913000c00d4101881c0e114444041070a255203800c0304550058820300300040d011003402940c0c64180860705200d01c5001202d229940110f0403848100c0c0d0380c891900c8103018071801d0078803c5581000307060058048034044040d0750002405688512482c02c00004a00c52102c100c80e0031070600801040085021400e02c03c4454103000c03a849140d0500c80317500328010340030070b40600903032056000d0303d1003010440d12481c042ca44514429084000c491003001c48080014040d0303c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 267710899 1250 267709649 267709661
    0xb01060f080912030c1c1505030d0c0c060c0804030b0702030408240411040e0706050306041a03121b060c040611160e072a1b06021f0f181203 62
    0x1810400380d04c1c6583c3c60300308082540000d811113500901c0c404843c86030891034086c5820001002c2420002d161030703c001c051801103603281c541c00384504c485401010a901e1580300003160007508051740040e6603842d00a207d88a281c00040c12200554280070000c1c2d40007020744291240c11040b96078440601c00c1d0b07041c501c0c1c1c40400e560101c0c003d54000500007640d2144402c07446401802c04200407260704022401c0ca402a0000b0000135404010001e0525081c05a030641081d07150078176510881000210f5216090320101809510002445c01030f040c1040400f65000d82003542690401c2c1400e100c0d81c8400d41c407601c00d0340c00180c20000a0f160b0204040b9031a4000d922007a1503d0080e1f14001c55981510b0008100b201400340c0d506080c000c1d1110148050302c40b034403402000b61000b5803131a00c480300d081350b103140210000c221003081c42107540010f05018030000c042e44400040440c45082d901130030f43c16401c0312680b4202040d1245610081c1181c52819100b0100b00c94020219a0100d00702c4803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 267712149 1250 267710899 267710923
    0x1605120f0c060d0b041803180806040b04051c02030909010f0e07031a030a0b060406090c05033106021e03090d030e0a080310060912080405120a0b01060f0809 69
    0x1c84062070311031400000515950b04036030300c0410240070a034002800c81d5a150525080144084040c804141d40018005d80d1052400d02c0000702e541422021036454000600007808510041c01103010f10808001e05210b180342e1074030059204851030380003500c07900300005003030040c90b5100000c030b440504c690b409400c0d030320790001c1040c01c4c0c3d4038080304601800c03940040306d20414005a511401c0c0e14280000701e00306000701d0040c5170504000061004840442d40306121f0340d0b00d000e8501080e9030703010701165000040b1004148001e0403a0700c0101d1940d01300d080003560342e04070b40c0307101003000f24540207000883c0c565200743d2a0703080007000900c2684011150307000e0f15040924071696a03402940b001c1a500c00300c104540440756981c1c0c688815034019251511465107092042003140e40c800c105901410182162500d4491685e442041074000c50040b03921598042e00c5a100b600380070808140320030713040080010103503519240070702082d2400c0c610308006610880019807000c0d00160f0001801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 267713399 1250 267712149 267712153
    0x20f180d0f1203060e0a0603140c030d11100c0804030e03060708070c2307150315030803130f110411040b030703020c1c0e0f041406040b0409051605120f 67
    0x8078080d40c0311010201215610340a140e5950b43c0411356808400016120361090100020405d00314213240c850a100e140480003141c2c0211440101524089a24405555203091200c0d610317903111405800c0407403117030181940f00e00d020300c0310400e190712147d03080c0a24001d813600b05e0b050320000107051322030300100c1d210b1011032588004902081d1180c1c90102d0304078029030088001040c9840b007400400c18a0700c0080103580800020300c0b004401340f41d04031201459081c02c0040011403ca1400f40450901c030182041c0008000540410185001541b10640c810304001c0200310314580304ac0c004103150342031400f841c640b400c147e0907049084221000c0c1c60142059038250303901c000c0100d002c1c1d4800402095540580b40c182841c40c041959207940d20983c47e10b4840c4200000014080c08101d00c00c03409200d582002c203d8801180d001e40003c0d00003d083e60b010403551806c00c0410040d2580120042080c40349425003148440b0328400a030070356004135107003609000711a046030750b208901c000c80403140d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 267714649 1250 267713399 267713423
    0xc1508040206090406030c080a0c1d060d0f05030a12050a090302030910030b03031c0f02090609010e0312041202040501270902010c1202030a09050a060504050d06090204020f180d 78
    0x1510b455409016100001000440c5031900c0c1c0d5604901c0b60305541c02198668405035107881041080c0c10382d40060120490507901c0765958980e03082504030041d0289009a180540e040207004403800f4035a403050300242107a0303031941854801004d41066501080c1620b1424000c618254440d0003800c140035016401581044103080400c45401e07c0c404141c001d26a80f540c5a0f40349403000d0005e0030f59481d400c15040444038a0309102c1041d509040381310604d1070300c10410100140c1c4e810007660b03143c4000b03103402c181c41404280031a1401e50601440741001e030002c0790002d0090300380403051172003600c00d0300c00744500c0c0d0380c8510240007091480b00c4c05203a03035540c4410382c1c3d00f01180c2c5d121000d00d500515151a000100351a030a00311161421010010b0b08002484c1c801c40b50000d100900504098503c000341d1450b000c8000c1ca2402b4600445105140a02c0004184006074103d01d140c1a001001190b56003201d0201402da94130510341c00d20b82584002c0100250b2904007810303410150071403040791078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 267715899 1250 267714649 267714653
    0x203031e0c04081903090e01060903081b010509070501030e030a090308160206070f060509070f09020d060305031908070c17030c0c2d0a1a04050307120201090c150804 73
    0x15490010684441d2003010b02c00050182002c100202010f8280080c81c03520f14158200145000c1c26a041080a42d9240c03004006441e0b119401c0803c6942129590703850714103124441800da440c9008001d20380d82001c0c14044a80400300b45c00c422a042600c0030444080222105078880c0603001444020481444040000c84c440c500140f207500185c03880c40c40a03001d282d0000e0389a0300001d4003600c240c501c040b060401c001452164580007841040103126183c6001caa60399041540e0142e0400380c0d401250101020741140c101001071540403090320b480c4d0866035003400351012038102120005886e00003082d01c050055440c5031090303410075031f40c61141c1a1103141800540c4090100c5051a608004900d41014140207504c20b07040101ca01d4041e110700c4011a181d0503415403510700352600441041d90002c0d0340d20000e050b0025110701035030303180e030340c0d07410003509500903e48050b04400d0030400b0032000a9041d4403811900d840340b010070b601d50b510344903000145031140c903108000c1a039030008100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 267717149 1250 267715899 267715951
    0x5150306093910020a0f0f140c100e01090b07081e1c180605100303081e0f04050f12190504050f04050604110408011a0102010507080403050a140315010f020303 70
    0x4400780f2801151021030305540c81c05240b2500420a0f03079038891001003031080041301444442d5140c0008003d190300b80428000511410461404405000c0c40c5004024140d0042101500910700e83c84074686800050503e0b50440c0e0082c990b03000e89654031952030440384610310a40e030344800d0107040d440380c0c01d01d01003040000744881400003100001c0c100d5214000348090050b01e01c40c00048241c40c110030329518018106840144c8074689264150306001445d0480d0018507502850310074004101c0d44407030030f000e41408003640d4151494020050b14404040c03010000300800507500b100c8000200822000303d5860150b40280c961241c41810140c0741407503d07070081c1c0c8e00204010000200081e00e0107007060964030070703400043d40e079442d200c400d80128801c91030f4003400c4d0f20a000901091802000081880000500c002c090000200c1c000442030704c52108600764480e00c0c40c9156480c20504481d4244280030783c06580040c502071034144555201100b5680940c021800c250035400381400b2442c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 267718399 1250 267717149 267717169
    0x3020a0b0405011b02010921051c18080703090f0506030411040e01060f050f09010b0304020d06090803010603270309170c09041a0f06030c04051503060939 68
    0x550b9542d00d40c142d031112080c02c012800c405a540d80c00024007a82a071900c3c0c600060151500702e00e000080400d1154640c11400b05c646403d4650780050b600801c80300340d1001083c1061700b052110f000c0d520050100210003004000560194880500096860307400c1051040e4900407242c0003582030000c200001d10003410f203601100c00810201e00101503611090031a91158000c4c080c1000300501000302e030800300c040e014022800c1d21032508075814456001c00601c00503000030b019140344001e140500a0030f50005010740e600c401c1503035aa5035181c030700501515940000f00448607200079981c0140f110821441a6268940c84803460207290425851500c100c2840040260003210389080c0c0f40d07956481c0c0248207a101d40415500e079281442c5011041c00002c0c140e5401c85450300078010710ba41c00050420415000701c034080b400c0d0b55481800f0010b58400c140261f094407801c41070000008001c01c8103114611044a4a228030840340444080f440c0c0d0f0b0002059615851810071000b810045c541c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 267719649 1250 267718399 267718403
    0x1e140616140d0801171b09070512130b01080d020a03140d02041e0503031c050a0209040e0d12020a1d0a0f090e070e090c010c0c1203030902100c03020a0b04 68
    0x2010300524107001c5400c101e40448030100041104006000c100f80c025030581c61091044002c0c007030502803021401505040d420761710310405204000a68041c270450485a201f03048080d25142410544c5004845000124003141c080451800100e14a040054444010117242d0300401d4400c1c009d032400d030307540c29034220387c00444501040701400841150009100814140e242004205104d10000c0da60f1003054002612130340080040c0914003a26114860410780c80d000c000402e03441710485207001b803244012540d0828205684042090404030700c884244070941c80303100751960700f820680c040b44202c0905a012071068064500103e1480e40a07408144001d0705481c011502c82298254080e031aa00280700140c99080030041c83c2c00074040d0b10000c0885260030030013401c0000f03c036501da2112020351410404000031900c2400503c90b44c03c0003e1401250700c0707040034918103000b005000002c82c04d82c0a82c2109414401036481030003c00101c9406501420f4148004d654056034071901a0003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 267720899 1250 267719649 267719663
    0x50601030b1206090c01080601050301090c020a060c0503150406050315041e0b07090e040804120309030c0f0e09030307020a0210050c011d0d02010b03030f0a0c0b011e140616 76
    0x2110100d9140c8460a4101c01950b800801043c5400071a1034a0302804080c5d690401204100748281640c006056070f05444a840c1c0c082000b40016034128a84070f50b40101401740fa040142181300d0940000095010340806401c00009246420071300007500d10511810750543c0c880344085c4421014200c0c4190810b00c01d4022110000d01e00446800d03841629a0035500d140031002803100107070b0012500700c02480e5100f103c100300d00d040d40350484540130310b20035401034403001042d0380f04042c894400040915485991404000d840d82c9088400c0701a0b4000c000400e4a880c011818901c00001a20320640b016801414003080c19800d004401110040c0e0209010007800034950300c1100307000d50401d1034801e174501480341c00d5203000249440b4420303010f0419a40750209468440c1c6000c0300b10303010300901e89005a0f86440920342140d1003510b0303070b002030160020328001040c04035005594043c4c041c86044032a041c540c030780c2d44400388580760079115035100000b00141d48510150501007d00c1c1409406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 267722149 1250 267720899 267720911
    0x1d0426040e011502011b050f0403021905130e101e0e060115090e06010323041208070c0c031214030c030604062117071202010f0c03060305120d06180f18021305060103 73
    0x8041608482c0703c041d071040d1550f6070cd0b000d01c954208802d21410300384d120581070045109603419a07844c1c05040c0042c4082c0781d05ea44045030100070b40c03d0700041c00c0d00410720400034000b107004004c1e2511001e004503036013200440715074001c0798890100c0800751909040c84040c95100d41c00150003c040b035003074038080142c484034581e003d019030404c420311950042c24424451a01044000c02e00800240728200f4040920405408226190304d41d01c182e130360001481118a01e1603a0540306038041510304d2188440c0002080400d04458010318060f00c0160780c2400042e44031721440703889141081032101a0f41414119902140ca2618884501c1042d41240740c0b8040a40e00c811166032221064400540c1d12100e0010160102d0b1042201f1181c10b4070382041150f00310b0b91917548034411901003100017000490003103803080042c3e00040050242400080d1301d98100ca4200c2e0240465411203882c0b94601840c140202180c3d4030f202d140703203600400c50130310320554406d228000c0202800603410103541d60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 267723399 1250 267722149 267722153
    0xb03071110020408120f12060103110c0a0b06060a1d011b0308040201090b04050d060f0b0405011d090c01080601110c030105070302070c1d0426040e011502011b050f0403 74
    0x1000c20749840e0600d060250781d982c240499203103480700d00301c22480c040c20104481e4001c01c400006858617131880054094640e129040120090404600e9100070000d00050300100c5890015900150078490801120f25549060411106000e08440e040124180f00c5210a541544000b008282c5005042a41110030030001940d102e002c19142207000c60b1540003480250340c0c22403c54001059200116482c0c2814000131600c00d0404000051025484010040700700340c258004101032900a0002c010303e6940d225165034103026541c484401740480c10125201c03003004150040c01c1c01045c0c54a04140e2203010044844122043d6012002e014024100d1a01c1c5d03001c2c00742600070341c81a540540ca415150900d50354002046d03004c010030803215074803112075610070454190300640100312055868424500010400c2401084216081c000500031031560321140700e0505807041c03600302c000c0010324000140d013240d11407803c102c1e282100008075008540f00e40020094844042440c41c1899580e0f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 267724649 1250 267723399 267723403
    0x3100323060a02030919050304051009080d05030117030406090b03091c0e030d091406070c210c1502070b0a051c020d2003190e10060503060112020a0b030711 69
    0xa0342c0c9100d08079000000d001041c0001c010420841100d402250080401d81e5646a40c83c811780c85041c0c01900e001c2e041002c001d000744113000003080000c05407407002c0b00003131008010358000d00403484141c1514551911484000041e0b609486860711420a0340f0f003444110b000d02c1e00002d000b8505881040b03200b0220201244e99606010125104c02d004510034000300f41c1000d031803044610820070140e000b0000f00009885000502005460301c903600d041600f1b040c89001410740040440c00072010b07421a28104003502c43c5070741d6004984d0a100c40d519400031459100c13402c800d9100582c0891410b11500c0a900020b0001020a060007031421802c2c00092420f00c54100f4500303c40b0354041802401c55245009148030320300084d05181c6209855025000c803800041e150110a000b130140054002c80583d00090001c0d040404503522101c403000281c2c0030707180c0350192a0203801f40c00000141021000e412082c1da40d0300a00d029001c0e1304021011143e60401000c440400152007500c0c400782d001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 267725899 1250 267724649 267724651
    0xb04062103140903100c020c030109030215040c0e010303022b08061207050d0c030b0a1b1110140420030c1e0a03140607090302010f030e010b0405100603110310032306 73
    0x4071000800c0c0d0b001911b00107800e01e003000c91180d002740d042c0803403140000d90110b01003000383c0f400c0405214644503402c1a801e20000c1350001621154610004414950006200007a90301000840f28941c50011052444c03540340c002400302040042d00401c506141c5041c00c0e1107006a18821a000280d8440015502c0c02e07080038150f8006030401000e10a10905010711513002c008400c0900512040901c0001d42d44c40d18501da20406c10982070020040206108030300750034071400c1040c4402e07011a040c80030b45150650703003203410030024000500034040c212641001240d0080140a0030752190060140f01d4140f4402c42c0e0701d108280c1c1145074103950380b00b880005180210460041500800c02d403903e044c1c0094845070500c20940400c000503030f40075081b01072048062502003082000c20031510f01401554140d1076005092808000046110010300800c403000341c2c1d03050001ca1221704007a40d903071100340c2d00c1112209480c101030000c03c19030415002c058040720210180911142c01d11420410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 267727149 1250 267725899 267725923
    0x605030730020a020c031c12140109020d0b0f10030b0303040f0909050706020105040b01030609110d080d0c0804080d050c0c010e01050a0c0f020a030f020313090b04062103140903 78
    0x2c0d010640c000304a03070410981a2511054004001c2c110b0f038a804551221100b050030300800c44204002c14003640b058005598205074141c440c0c0055840c0c01600001e50860b0f03081003201858030ba020314003454003401c450b245450143c8030724506502148100c02505041342c2241e018070003044009140a6043e1060b802011164400103000840d031800e141052201d5001030110380c10b001c24030012490207000344e41125409007000600b041d907813814440d0300b4400c1c2c5c0416845017150b4810300030b001d4088014605500604020088000121426101a50190760103003042c44180441c1c1c1c1101a10391081c1e4001d1914803a060030800b1310440c107801c0d01c04259240c42d441e5180d00611484652038043d414106006051001003102c9031003000355280071124020701040807100c01c100c00e96000b8070031100130151001d600f50656450f114001c0182020600c001e01640c40d24000243c43d020074901100c001c03074080d942000c2000251811074594145200304203565004015462065404120418941c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 267728399 1250 267727149 267727151
    0x3050708100e0303010e060d030e21060106021912180b0910050307020d0c0c1502070e0a0203091c0912060b040605100f180308030906010e010f0605030730 68
    0x1d004512242981c0308a00642e11560041c001808802048624035070b200790280c40c0d62107004078078141103802d040b40d81c5a05820040307110800440303003080404190001c46c1c1c041241d2041c3d9850400320381d140f0b03121440100802e0301c64100000507502c2d0002e000300c1034003490104103007003509183c504500749952080113035000000e10100c2c903041081000c0740a01540c100f003411031500200c041c0d212001c4440710700c2080b0139481c14108000a078074044002e8041981c440c180c41d1301e00030019580e501a4081d9100b5688401d001405e901a80d0085921035a5000b0141c200b01d0b107002001340050240025040c140290300e0700208265000342c01004140c2d02905000c151600382405020884400d600528068400c40d00502c1c0d0050300012849041c04481c6020004074414200607400f9440303503000108540800414802d414500042c100e0684925203940d880d80e981c1d80002e2240202c19204000208605100041d038240c000c0129070059105041c01c0030300907480c5a0000605040078030100101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 267729649 1250 267728399 267728413
    0xd03081e0f091005010605030f090703060f1d060103030923030109061d061b0c010204090207060507020d11060f25020d0f030b09040f03020f0d021f02130501030b03030403050708 78
    0x600c02c2100ca0b400114040f01080994140070340140b140c8002401e0500d090700c0b200205488550400c9207000550b0481c000300301a05854141d48050b103c01d044802510452200301c46040d2404a0641d040703035419140c140b0b80514200b0184035080410951003030b44000083d01c000ba40c0c03003c0c021550f905200303220020721413006170300007084503106000e1850168069002c000c2d03041038551166003400a181c1da40c40d162100244058060720407a001070004500101d407030301c100551500143e01410064094917500b40741c29104032200600355440441030381c0101c0108510402d0b10340000e4014a80c00c22444401d407075201c00820312404402c80b140103070300003401500082d0b48611006142c006918003840300c0b03410000002c640500141002d040c900b1050108001c06000304642c404150702001600d0444410341000394489064012602c000d07407a400d1541651070461003120201040b0060030341c0c0440c10400110010030344080741c641c15100030400800400c0080201c0070040c0401c4c0f00130150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 267730899 1250 267729649 267729661
    0x80f0a0c081501090b0301020904091b06140909040f020907440c0909090d0e010507020105070b0907120b0a060b0403050a06050a0219031d06060d03081e0f 68
    0x400c81568820311440d003005000101c60842c1074070090445008000200d1044169400640240b1601c560254058a0b10b0700c0c12040100181d83c4c002140c14410401c680180e0b02c00003642c00803603d480e40320781c40701c0c10409040e051a20041d00c40e0064080c400300d002420043c1d01003020100c0030744604003c07035203682d40d0307190b0b888190380701c4100c00402c1202101e2941e20188140900500e11602c00314a0b5401c3c030004000340207010a0b9080440003e11240a906029045503203501001c090030000881e0051114034079400784d42114501381d4107a4407645401c3e041e0310b85004400d005090380071140140c0340000f800c9503014402c81000c0d8001ca02090b100d080046440e4111881c983c85250b00380302c24441007011800c08106660180e80040002c035241d503800f45e1241c002e220f2118910000300c400840b606030f06a0540c081c0c0c02080381c00b03034201c071031a1400502a0395040e040b5402c2d0350026500d03c4150000e40b082d0072858002c9600000d07042c0d11403810750b04402c1094100e41c914205400c260802c50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 267732149 1250 267730899 267730913
    0xf05040b0309120a120c1e03091b06050406080a0b0105040e040c1503140108060f0c0a0504090204032d050d200312040201090e07080a110702030a120905030106050604061107080f0a 79
    0x80c0f1200c0b141807c2407000000f0f04888501441e14250001740741c0d9801640050013204504060170b6501d8203001c0d250aa11104003801e142c005000c1c1c000011061000101041d0561250184c1c000c0140c4406050628151131100079440082084620a1a000001600901000100d81201469280030940c500f042c041000042016401141d2030341c891400d10000c4100d080c0c1c442d4000080d1000141d0700c050030501941d4501c03480c2e106138400340c40040e0020900c00a40210001c00203006024045004064650040c1c0842800081c103039410011010084038068100520340601845c94038080c20345829105003190818004403043e03403c00d0007080111360303000c1d100c08041e11007041c82890b5410402002441c07036138010b200c4403c041c0d6035880d00709042c1d03801c800c1e504481da0080440e0311400a81c0381c440c0500440703200c0840481c1c041000401c0034a0103004d008241d80010302030604292808804070340b0583d01a00c1600c1600a01c68040303400305007030068044402910000b001c030b401d103c0c98059 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 267733399 1250 267732149 267732161
    0x3030605040c02030711010e030a0c030309030308151008060112020c0105091e03030103110604081c0e010302460804120c1110050d020c070f05010f05040b0309120a12 73
    0x82c110f420400a1a0000f60300805880c9007241c03c0c6040750a0201000c04240f418852190240070030010312000410542c0c000700d04002e60b0b100c0d6440c103095840c0e40c81d10200c500880c100c900c1d400036024520381c0c0100e1184004961104051610703440c94006019085d0490703014040006059450740100102500104044400481031b03c000b4424800490319203a00d901043c00010b104441c860203c00c09079072090103540290100b441034400c1100c4a04042041c6620312490001154200c41104000e40c040d109a03503244060100f0359107090100c03180740b42d4480241701d4640c02c0c20810001c0c6ca1002c0010403c11200000640700c8421030309060820480e810f44540c1104204001111000000f40806044099424080d0740603100d401c120482501c140c040c4503400c101c031078408901104010400213422080f1040004100101600c40c001104c0d2050061070200c0800d83c1003000301311140d41600295440710000301aa104010714907881c8041303030302c10142c5100041a00302c80450b1b0f070110380310781 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 267734649 1250 267733399 267733421
    0x302040f032312030406020f040e090102070b0612030d0e210a080f01050a090c0c0803160e0612071b05150a050a0b010e04090f06060308030906091b13180303060504 72
    0x519060f9007424a85099100003040142075039004180f06910000d86020b960141140b41c50b401064a4208105030003504422001d5a034181540c020030100d0814142c501c92944032100607615021104c0c40c018040d0480c207012504a2046069000006180100103a80000c4610301541d50b4042c60300c0c0100010700c05810100d1031400480100903541d19a2010411210454004905044840700590340c10f0580107002d40300f0706000040140c40302c0010302e4500400721940300c031000014038a06000c2180a940c00108180000300007003940c4900903880820400100780c25030301546d106594050505000480b41d10308111040d050068200d81802400d5002c940e032407080018040303a20000f04083c81c0200c2044c0102d07503440c0d5407010701480e09642c41c10203410140510a041d81d0341f401c0c000755031003284c0044c2c0310b02454011402001c1c01051400100ca400b140003200005007000f0001240c203045025003c0941c1c9220303019400720144204401e040c000c1d00c2c001091407400040c03100b80c079484096 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 267735899 1250 267734649 267734653
    0x50702070905070207151803060203090118020a031b0902120a06080a02030703020910080a050a1a07020a110406030b0a060306060807030803130f1a070e0906010512070302040f0323 79
    0xb0450302c1540003528004680c21111248842c2c000401b060300c0c01030300c1c4d00070351941c50541035000c0140030301500114000e0360680002c0103400200d040101011489840095000d03800d0710040002c180c20440749825000b90541c40070250355035035483d00417070b8866441c000021100c2c80030040140c04501c22500200310130340c041c195403840d9500107a02c4920a010003440343c10840007282207841404284005450355104403020042d440c109965103851403072040b142190070f00142c6480f000b9840041340116005d400400300190940c0d03c071149030460600d502d4000b80c3e9a4400804914100043d82c013035559440d000400d079045040601c15107080b0380084d000d03580103440c100000b4103101d040b01d0740300030600549070b88c4920741e1820558500a42c1c0b000760000ca003080a4500301e52001c0c8481e03005009a0f01c443d001c00c581c40d4144810108100d40d003501240742071101d0311142504410b20355001701e081c0b400601d070a03209c01c509400200e43c0d40003512640316803002000701c00c254020340400c0856800c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 267737149 1250 267735899 267735901
    0x108060105072604030501020705070f0515090d080703211b0804140d020312010918060504020d0b0c1c05090c061333030e0606041815050702070905 65
    0x10020707100c0d00c03601d44014141c414040100d41c1074548503840d00442c90346881c0301540c031aa03a09105001c1d402021082e1143c3c01041c1001800711000b1a281044440103070002800700300b005400c0a064102e07410701d80c0c1002c103103411a0002440784000304600e520139110a45d50454050509500d4000c4056812101d85800420a0191010340307a0a1a590151512620964461030400480041c00002400c280f2451408080694021004d82000300c0300c0340e0010750302d030703070b2242e0000a0380c981c1c02c105440140c40340c48074004500507805c0160302c54000791250300e6a94150399403808003042201c4030301c0031315070110b11484483d61401c00344001c201e0000d0240030608101000c80d858459060400d845403c0000d500b2240402c201c0c0342d00c005096803404084032820304201411003420540c40380d0501007a441c07030f10718114028460041250500e0000700790681e40c150601008268250400c0c449640c00040704c000a60520141004c03c1e0750154046140d080514000c0d1400310150414409241004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 267738399 1250 267737149 267737161
    0xb010203031b0d0204030b01180209130207060902130501080d02030403020a050d050f160f0603090b071101060b0313050d0801241103030403030603171804020f04050d120e0108 77
    0x305580c0c00c4034007003140384442d0810380c18800c624807a03000b00d001024000b040020a000d24807404170b048604a02e0104c24030b5069006440481c4104480a90710201d00098102c4a00841e030261650307911400c80014680300030740016014010f06042010b015840d40014041c0342c000b03200c506513803407a03400194103081c02c50340080c031125214002c141c000c40151411600b440004c11050400401c4e01c9c065030f40c0f2a8100116000402c1c05010b042d604034140c040000d00e180c1300e07208100b031154004074800443d440b18002192512002d0408100e01e40d00d5080c042074404041000b140642109600d41d04e002200746002f43c00c1240100c80d4030103104003140100842c0c500c01a821070203103040e860581c01e05040c854251030428140724420000e02c0048204803c041d0036a1141d01500e015425400c2c04c401808140000391203551248400c074a0b11160484181c10960040c00e03008401e40301c068200b540703c00c01300d881e50b04031f03450a490b40740d0b00c000f144c40c40603001864400c00c0d24080c640018503207018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 267739649 1250 267738399 267738403
    0x50702011d070b0915030106030b0f01140d09110402040902040e0a020901080a050a1d060a0501350a1e11010207050d0b250f0210050105010e011805041b02060a0b0102 73
    0x40c0301d600d00c4803e00041c202d24680c2c3e64408101d1040300580d02070707280d50311007400a004041d0318202602a10200301c40b0104e0b907009111119006482800c9145414401e824a101818a80004444c20101d004426009607294005000a003402807001a21145016411422240040d002d1281e05104000500450340e0000001e60b002c640303c0c501003116114038003280000d203001819490b1a1514070780d048001e00011419500800c00c072203090007540d88a120040d012860502c20120b1147e07183c4451101422007814071507140c181c030007030b80c240146030340300c2d21100c1e0f004420581c10764030340390120401c0000600f400300c035180080c4014080d050602002c00c1540e03410000103040004882e001540c584c3c2201c0f03808060041c2c000d419001d10410700c401034400b025641c1d168025000d407070009501c0203820b1007040d04840f416900c2182c14102a4019501d0080101c45840311451460003c181a00d6502074060301c580283d0200354100f0302d5000090130400050282c0c501d280c200481c40c001d0b40c0e80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 267740899 1250 267739649 267739663
    0x426030a270c0302010c030e090c0315031c0e0109170f120a08040209180d1808060609061002030c030403121101050f01170309150a020c030d050a0305190906050702011d 74
    0xc20709146c41c6951150406590442c281e241c210307801420042088107041d02c040145004070b010b150220b400a2041003050345134000603064900581140e03079541e03919449004800c60f40e00c01810103050541d01c1d05408811514a480f82075441c1d803240850300c040a20400c10100030305e00100007103080c080d46c020001c2c00d1000c06800648282205404280308a006400818003082d115007200c1d8142101c5402030314442c40106110810584c2180000c0d0300e8101250f0310740304142c000c2843c0e40316079400c4c00f0000300c241a41d010400714802808407021040c0d04000410145004d070300c000d003000041c02001090800c4078501800c55134181001d0040f480c000342c090505441d44001c0501500d03140f403110030700d50b0280c1643c0f954080f9040310228110a81d10000302501c01284c1c0c2921010b030160001c0c160307035a00f80b8030b0910000e1020001c05080381e100c0c1d80b01d203400041c1400c0b80e4540300502414803084e02c840c0d0710155007807a5954107101e11f558091060911890300c5954401449545100c503c0e2580a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 267742149 1250 267740899 267740903
    0x5070501030f0e1605040e010b150c07050312040e0a1109010e010e04020a09030614010806180703080c01140a180809060d050115080a020f030426030a270c03 69
    0x5150410400e914510390803088140110303008569202c250084001861380d80d03842002e0080b0700c1e0010014a040c1c040c00f8840c0c02420103025200002c01c10340711a882e070b80c482107500b602800b07412800b242c0790f50180031629032000f0314014580c9840c2807019800c040107001e0b101c06582e42c46e02c2107102c4a000801c0c1951f503401001d0030418801c089050044e10141c1c82030b00b4681c1d10510000e40381c0981c5400c010b102040c1ca0141c001001555484080706081d14000e0082c803019601000025005070241e8841c01035000c418815242856603d5031541e905810494503400640d44030b026110305142005030440e4030207094041402410303003150012001e803078a481c015042c840c0001d42d11005486460031034014203d0f045c010002d035a95080c1509101c03501400070000100386c1000b003500b141c44c82c000e98441c52107882c8850300d161035542e5000c50200d04966007800700d82d003e00c044c40c0c00c0342c03512001d944a0a100c1c480480c6084588079410311b104041c50302500800390006130100411091030b4407d003a01e07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 267743399 1250 267742149 267742151
    0x103021306090617072309100909060b1c020906060d0230010b070b060d0f0506180d0513060818030403050c010306050904020f0f01050d0906050403090e040507050103 73
    0x1000c030140d0068502078010845240c00e0140005400c1803401c1e100d0801c1382c02c1c409a860050300d03120725150030704101301101c201c15800a501c01852800010094200d4040b1005012496483d03000300709441861000390384081c0c3c1c4030711510440c10106041000c268001c050b180316010076500080341120301500c464040c2e10013060840c0c440b043c981c1240e03e10316107400c26611800c10880c081034805200000103891820185c0009603a44400c029034500c3c80d80028084020f9480d01c0a00100340a05039050750320314100544540802d200348062800345c401b03039201c1d130399070042e2080c514a4002c2034080c20042000c00c001000b612000501503105a80c06441e0101503915194512600c04a05580d04000c0313000c0000c0c000200200000d02101c001000c2c0c0301400318582d12030800c403004401701c801079003042400400200d00e00c0c1410742408150414140b0f242049034800303000c41182d166203001c40360310355140e0900041c560010880b000a1050b400600c0741442c165680c3c035240d44080c425203042c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 267744649 1250 267743399 267743419
    0x1b04020306131b3c09030b090f070b0a050a0f0c060c080f010807080a110f10080108010b0109080c0103090302241009020304080406030506150c01021c0c05090609060903060405031c050708010302 85
    0x1851085d0003120013160024a012994104403801c0c0e901c0b82c040702040156031041c0c1c8000240041c81e01d041e40c280209548800b81405050341084e10310314024840017081010022600300020150302c81c030403803191280e8038000c46180081c1c0310b08003042c06802200ca1580001c900b00001d80b000a100c0000c15481900360028854810108003584201c81c049680462801c0091100c26401220345040300e503660001d0000c0c00400300191410201802600515000300300710094550094120f00d401034883e2045981400950707d40c0954686018203101c0c5003440b03481400a40c03054000c1c551701810507440c04501c1c40c207041c3d840d00360070310582c45023205141d128400902c143d41c0e62213074051150301d05090345e1750f540c5150042c40d000398010b41d5602600c0700b000c61503412400c000c0c030604800c160b90340c0f100c626164420701040313070580000d8190b0b580a101003011042c035442c1403008500072403150b002103450f9800100300700080000420714525451501341080421907114004604581d0142c0f101100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 267745899 1250 267744649 267744767
    0xa0b0f070c030c06050a030c032a090b030c0703140f070b090a0218060915060f0c010605061209240604090203030c01050907080f1b04020306131b 64
    0x14002039400500f50b5299680001444c80e004002824a50003131303501002900812607050f811100c44c0d54159036101e80480c43d0f00503c2603181003182c806092400c10ae0032183d030710704203d40d4a900c101c0740c681c0100d5003c40d1040c2056008102210b0202e0040c05150802d0000b11000c40d55004241c40a803a4000007004600d04210501c03003c0b10280c1c01030b000024411004000c02c4c03402c1c0040d100039000d021040000380910048841080c1e004200a210300d140ca900c0038441e040c4c0da001900303600d215540ea6580010306598140040001c4805146030000502d0007000300c608040d00b0440383c07a5803100e00e082d4480003043c40058184d018a0482e80062022000c1c00424075600424000d00b08541c0380009100c070403100001c0d503201f10f801c190116085545005c0000e5243e280b0b00781d40c0c80d81003040481075011460b080e005141e002002a101d1a001361010340d49106980303022082814000300490860342056000c03096901460032407080091148100e141c0368460f00078078507214510f91451000c248 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 267747149 1250 267745899 267745913
    0x4090305070606141f020606040b03010b21160b190309061401080615090402041d0703030306050a0f08030304150f061d150109030f06200d0b0a0b0f07 66
    0x119250001c404100f02c03500c0742c0300d6074407a0802d402c11070b2044040341008526020b1026842c41010f1455001e132145807a64800e0002600f90308401c4c9615540787d041e00b50480d11b83d6996014050b40d1540200b69038407805d9001400c1c1600d0b5035103980ca072320a40006003c2ca003150021580c18035198111140752141c000c2c42100284040400200014245a070001d40e510518480030705039007909050f1902511032114080304c1055880e10303560484100301c0010054034096001810001d6020164200c01a0601205003800310542040b000b013a560502030103c0d00341880390030040c090f02c2e0304c07004c0c8840c24a00040e43c0d0303000003040106050140e890405100d0041d070054051102160006c1c4280c0e80c44907070014801e1441c030b611124507243c00b000180186a8031642c6c1c0700001040c0c4410200a0440c2c80d02c401c0f0301400da03002e8820507210b0600104052010805c913850301d0b02d81805a03115120902d290b0103407156159054070861483c0c00501c44940020225607031403042e0350340c1c1592442c0f6850420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 267748399 1250 267747149 267747157
    0x10308070302190305130e1003060506040e0d0f08151f020a080d06080c0d020d0f05030c030310061701060e1002010f0f2a0503060648061504090305 65
    0x400000b181d14111404c254201000d000c0c12500c004a03403019a464128070018036400302c40941582c10500c01c204003080095020302c2e0084809400420405c0c1022051032401040900401c00580c00b4022200c0c59075000780019001070134032031455411454500040c42c2101c4001500d1b94084c0e00382d030183c180394000c00c954100c2550004032180c45000054901f4020320b207510488403107000b0044000864901030105d007511a50040690b109404a5181c0d0710706a40500ca045170305210800c05102140f0b410400b5501c1241c20400c40d203201d42c100b820080c1205012803500b510326420100512543e90403c0c200d41c00500250b803c00c92100e14114124054081c5090022040c3d01c0d00d4523085d100150341e0480044040300d1000c040c10b04030003003400c1e0108468039544000003242880407c11034940314009240922a50300144143c07480c49108040d0541101c50207100400750355041c1001c120f008240080800d50b01c80600b184e86013688002d03020140c00e0075070900c117960794042c1404260194040e2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 267749649 1250 267748399 267748423
    0x809010e03011b020f070608041e0813090609060509060f09130219090506030d0f0c060204031a0411060703211e09061109220b13020d06060801050306010308070302 72
    0x1901c100d03da0040181d102c0c01e5000d5102d449004080c0f0100319640100792082c011680005010480c01c00c0001c80c0d0b1006200c0c40040341e03004401c204c0840e5031807041c0110400303811080c0300060090318020842c000c0340c84552210740505015030401100342e039400d129102d820001d90b0741c0b94095482075a046004c08403404025484401e50400e4200d09000030503000a590b40600f040005441d2801050740d0394543c4c040090003d40d4050b20482000d109001e0f0060700d078450b12001d0b003441e403030365079403040700d64001414844180594200010705c0000b20380603d440c48180c5802b40707883c3e81c1e52801005940c900c89076082108240a11140b1070400e0f80c0010101c251104000384441102c803030850240400d0700381a15401e09101a8880d480c40180c110354100310000c0803000f20350300070000d000550f02d0740fa0780b00080d265035494101450700c0f003040708000342364601c0700180e4401c0c5640a00c0300321207141d0010810041c0900041c4134940700000d07582d05681d0006a580c3e191b280c02c0c031741240750503000b002c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 267750899 1250 267749649 267749681
    0x150f030d02060f0c03040b0412020c0d08030405060612030f0f0909041b06210f150f06091d071808120c0d210e0109020a0b04050a0806040809010e0301 66
    0x4888145580070030210f000c1c0da0a220240220746549810384450300007a2006802c15041c1c00214000400b551030850110400d070040c0c072410303038009000581d414a019000d84c2e01e200f00200300410840b0070301001c1d82c0500122401111007400805040d581e00811810142b148000192142c0d084c0100080e40c1e80b803000101841203a107818a0000714900070076403c0a10307070101c81c00c0407800d01d0042c5a81c001c0080170300203c1c0744920302401e91102424000c140d200e096603555074160141c01080d00410090903140d0041c6880c1c618100d00117211080c3c0381e1084540a110038840c84002d0521060a9044070551030402c1a0350005c65090200203865032010440e44240803c5074140c1075414040c0402c042080140da148070030590b0241c90304c1005589044082580041040c0e91003155800440d951045000010780c0b05055404a070240390035400c03605155001050400c498904000090080c1114a01511450030540c5e02c3d03940502a0824450501883c0040d44c0e500b902d0035806612000c41c4105c2c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 267752149 1250 267750899 267750913
    0x909020f0409080a110a02180c0702032505040b0303042d030f060f05060d230303010b030405010c051801140c06040303050f0112020319031803060b09060d020108150f03 74
    0x2030081d0540d8820100c01d03000c10780c030301c0e108802154049444410247c004e0203c04a850458000140031100101911000d060034052100507840802203c4200d00024074202c00042da89003042e9424010713640030912803400c00c000f0714100d403004016a402c51300c01c80b0882c040d180e020000308640d050003c80d000b401c0418000300005002209110564903070040c2c9080029034224a40b210a60342c0c110303115908494009400400a5424407101031003a80840304003c1074110040480d007554400c0c2d10842c500c4001000307000034408207100e0381861703a07507905102e4074015810320022944d03480700d40c81302d05010075041115810146042140e0191540206a416515080c500603005002c00e44400c08078032088800440c205c1203c0f107100300c049800400400003070001e01c40b01003400300e44810850030004c10380d10941d074850440d42003401444c4149400f103a001e8200301400114040104860710460700c0094007009030760041442c0748c12600e001207001c800080725000c603111504c040c10160b09445441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 267753399 1250 267752149 267752153
    0x151203020a121b06150e06060a27030f1e0c09020307050702040207030c0c0b0a02210408060f01090e0102040b0a0c111c06050114032d190302010b01020d090909020f0409 74
    0x40d000700401c1030b1012019028640342d15080d06c020034100c1e145608000300b0805401280e006000150327404094a542d803d4103000c6000d80203441c2c819500444010404140c42800c200142c2d100500d00090380740355079496825900c58920b5148148107901c00c00c1c0d03001010501062151080307071410740d0060029940d4a146240c01411f840b0420010f8039203840525011401c0311440003280c844000d6a8003c1015898241ca0680100005000050682805c100c00034018505001240c8a03000320a0220200d40c9004007540030f40381c2c0e840f0300a41d41e03441040144800c02135002a02c218005524244440e1071041c944040c01c207030039900d1613910102c290741c0c04800401c2c407111007120910130001804281d0741c450425410580702803015915402842c0c080361100e0321030f078401d0403000681045800036070086000303600b4407020300d0172604070407003440103182855024000c203c0e14407028402058110190031004101070080d024181c011074482040e607095644032411982031000007041004100c0d164 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 267754649 1250 267753399 267753401
    0xf080c040b0940030914041a010509040902030d0302040501020607020303010e0403080c0d060807050f0406080709020f040b271212030703060e09030403030e09070c060906020f030703151203020a121b06 88
    0xb44229600040d55980424035810700d4000c40c1e40030303440c000c05510702c122300c0401510389802081d60b05811940d41c21050340943e80801c81c050010105440050342c9a007004c00090034144007c14031404d41d032081004004c5c400e03010100650098161030489166128004480c82074030911055000c010305001c0089220f071030216840044030011500442d0348401c0e00b0520042d214240300e5807050b9042200100204170325078005142c9030030414422880c160b26082100d03003981081c09071a81d1001000903196020240b520b00d644454001c5440601e441142c07003420b640d9468827150520148000300c082241107000e80c0022018004200200603689085001141c0d05c4e009440b0139400150301c0302c02000c950030b00c450b01c0c901800c656921075283c804d0070707102d82c8050601e90b51f08940481c0d00308140c20300010002e0196000d940d40755004206410348501caa80781040582180c1000580d00700c031000001d400281c100758040e032100001c81f038501480e005541606000000c100c1080070104503004100031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 267755899 1250 267754649 267754667
    0xb0d15060f09060b0412030e03030c0a020108010e220c0f080f120906180d290702060603030a0e030a0803040f050d090614070c0f080c040b094003 64
    0x403520344000c078a0351007a110041e07514038491400d4044c000c210520070100413448981c0901c0c060b003007458003450031001192443c0d002021400154010040720001c542e44500c0701801011001c1108000341000181c0c0307030350100390000410203124040300310010408408101c0c1300078000010306006d9181d5580340c042e2070321416402140640250fa210440c039200c02415561884805401076041c00d0a40c900880c00407282012554807014469509000030942c030703405412203400841891812501e41100854020050000c10a64118504004194800005507200440c181c5040304108000c40c003c01c0c106103540801600a200010802092003e0120014035443c0303e0070842d130000781690411204800715010f0f034400280c032903404842c2115030501a0005902a084040c00c0a43d0380c002054240003981c40080a03411858541142e0318181c812071100100c00c0c0e07884151032402c01c41c05586e04112180c5900054406001804580302c003907107591000381e00d0301c4400c07402e920074140a015588 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 267757149 1250 267755899 267755909
    0x301110f3603190507051003110a050d0c0906020c060d090b01240323071b14120702090612030c030307021005360111071101090b04180b0d1506 63
    0x101d0044003c0140d00d80b0a4040700a5404c00c0140c8102400c3c00100b00034040514101c40400d07441c1d1080c05071480c8030100400203000d071900c4d0941e9030ba1500d032580050b92403010002c8148484003108010241d000f043c544001c11048464580e105500c032441d100810321094050311901e04840045030f0600b00c468201200d9843d0079085034243c89607481201503824014007100f0304080c600d02c100d04220602850394001e045e42c100810f11626401d03401d903540700412815a0854204552400c3e0001d050000ca400c05510070380d0240b620625801191581c1c0c0050701d25030044035500e2195443e103000303209031005640c00c01d0940b50790b4240076800a555969112031040310070f01e480e01040d9941640a174404800800c080c207181d650202c400004410002c40b0540c0056540f990307518282c002d019002402000c0c4940d0a8141c1d404101000504038280340e0803451103148100802d120503407401c01103c0d01c0411030304001c00d6103448400441c6010713181c40c4009010144d012131810349030825800c4503060ba9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 267758399 1250 267757149 267757153
    0x6142d0c0a05160806090c010305070c020d030c031d06070f11060f040f0e011815050a06020303010e061002031624140703360c03030810050301110f3603 67
    0x2a0f2154192911454250380a41095000c00c00c400c45550098016950002003410006c0002c079441d008552000a0080113f0005410310203007420507411114002d0750702c50b6007444030407184c0d40c00c01142540c882c4c000003070700c008070300e942c0c4008000203d50078444804c40a0501030715034014250380002a0004d0213201000c0c03a0784030020460303d000c01421412501400700000000d0083c0505100601600007542c29050501d10080b681d83c4895018074000c0c4408d900450340c1e90b1404d0000c2c030320410040c050910038106020b40e0040640e0001c10b944040c0c2d100e0044503882c088600d40f941002252011246841c20340c15034100a0b40c026a000d00600d0000400105d150742d28080220102c0780005210b101041c8050f100e402d43c48201140100d1710b000703500301000740c0121600d03102100103299004030006035000d42048031440380540440b000b030005500074040c2640e40c4110300c0050080c20009018141c0c08101c00c80c15406442c80c02c00c005030702c03c542900141c44003400d2800481c034000114024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 267759649 1250 267758399 267758443
    0x70806100509060a14030c0a0b070c080a12120b0918010509120f07020301090611090312090306070f051b0606011407020a0b030403020a0606090606142d0c0a05 70
    0xc2c0c24070b4100ca903c5240014440c0900c0c0b403d10050184022a26819a4040c40354a0408207141c40e40a903000c050240011110340321005868010712400554004400c29007101030500c001540c030120a0b105c581040c208081d6048464160400400320b19100d00c0d400b8020710180250048020442800c14001c60000d002a58480310000d80e0340d586000024601030301006144407501402024101c01c41c0300500200d004495600c910090f070b4415203440400c0f9034001690109441d007040100000c51a0f200c5c0d9509081020300001e4070303240000d040d5000e01180d54081517140d44501d0407200d680d110038143c05035404102080650b10032003200c040d804200c02c844103186a100e007401340c548940e801418124001d0414002e84926000540200c055114025070390000983d180107444c0a000089000150586054801030600341c402c0e5001704940307800c05c046040c41550b0108452891804004040c01030510740c202d84591003980e43c9001140a001500420041c02280040c0c42c0d0b8150310801c000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 267760899 1250 267759649 267759659
    0x6020c1c0906080708190e030f0d0209031e030306092206050108010c09050f0d06090b0f07080f040224041509090e0c030601060804032d030c03020306181807080610 72
    0x214880a56080144146e10552200c90b180e407508521201840403007600d0a20941c2400801603400204600402c036070041842000c0303090030800e91840701a1990303042000801410030a03240c1c4009000343d402102003000047c0722210030b091001c1102c00c07502c01815181000c0c18010010b050a00510f2a0f07542818031503030340d881c0324031202425130740011302c41c0d050b0800403001c1000400c0d41510850700d82e40c50b0154000460000074044c4d1050036916038070803051800c07540081003203100410550318840c40380240000350f210581c0304c0d00c03030082034029401c41030540040303808a40280d80c00000c12810792664540c40c01c2e03004003600b0444d0708481c02401944603071004140c660b07411044c0550164414401000360343e00c5031000c075400c0b50007410803210140207170391002440d1003d01c519001d0900340074800c203441d1b80c0c1449030303440142d601d140071801d5042c00380010300c00090b554151054510250041b507880c01201e00103001220645017140c401641c1d64981a88501080316800c00c400308595000070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 267762149 1250 267760899 267760907
    0x1113150f0e18090705060c150702030310051e060d0f1808030712060b070804293405011d030301180509160f05150f040306020c1c09060807 61
    0x300c201d00510042100711103421150824800400b03201c070901c280314001906458503002010122580c0010f8555901e2600044484040250036502150720800070050030100d40034901d019100211007548000c2c00e65011242c02d8849886c03d01c1d0312400c00126a0404061a4000070f503e07061508244090903405825010301d40301050003410141d800c00004070414070a482074140711140000c00550a40c60302d009041c59041800304841105000070b06002c08110141e14070742201155100d03080758900c0c900445003034003c0513008204a9030840a0071601040000d0f034000c080c4003180c140d0000402070501c01d000c0d0a80c42c10402098041e080088181c1c0c0005c011a0305a8000b5030104000d600705001110081900030440200c85c01107031122040041650120030003000001107041d1200e00300703020083e500352180e00c00807105030b0400288112750001001e4400300c03500503600584034140c1c03a010320b05007141440c3e100003039207017400c105072025003040c0b2000a80309a542e40d6030a960380c0817802ea07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 267763399 1250 267762149 267762167
    0xc0c0c040e0a06021e070606030303050f1b09010903212303060108060105091002010e0f0102090a0302060a0c121d040501061b020a0f080c0f030607090303031113150f 73
    0xc0715600711000640c003081c1c00b0b400404600420000728081241092031600c0d03540c004c5801110745544800081041c036625000d010b4000311409900703030302414078840b04c1203010504554010240c00106449145a009a12000c002c43c1c02106038550740c0414224140c16011001410000c60b040b40340d401800d80154003510342e07900d03140c4241455a00c8a0005468980d0000d100341d0421a00308000e070585e4481c0c120101a01c2d030190004205a1540c4401c2e6041554051003418543c0c4140596505533842e5402e4408507a0151500c0da902d0006810448046640300409041a12100300005032240e100c0d64070704407091400d1200005480c1c0800308000d4031028482c041c001007045200244026410074241c1d00544010124078850b41d5031401c0150030001a44506025001060001c41506201c0011182068214050801c0c1d1504174006007803810f050001608159403044c811801130b561008848001150074019403015940705024024000101e44210006100319103074016a03014004034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 267764649 1250 267763399 267763421
    0xc040504110a0303120e071206021315050306010f0f02070b090d080408100b0f0d061a1002010e150702190606050d0b180a031b020a03020d0302060702150c0a030c1101050c0c0c04 78
    0x4a19088589e44485c0080d40050b1402e50240b00036160008407142e0500c015100036031251213441d12442c0c190000360284e4105416007003404400c080740341880c0e60100361001034a03d1030f0405e03900c0310406030209841001c003500041c61a400020041400400020756400e0400c200d40309000341c1500800380030007a440501ca940c1c00c41002d42209002603201e40001c4450007044002d40f800700504030010b2101d1221202c40c10141c0d5580c541ea51724110240920107100c42c2800091000c1d0800c00c00086d03664440c10146032070080426080000c020b0306821540c010000107140e09a907400030300b8501c402c0301d810b4401d1a141500750303414421405022400c000f00a4054903188043c2460110801104032507500499000b640d40c00d01100590b1500d550000300c2e030096005011030310700420b0203441c280614880070504d0f404607003003020324030140045810b40d01d694a0702003102003620000341c42d10080060020095401c0504005001c1d00031405400488100b40855080c1c4000800303000840c0d02002c0b079 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 267765899 1250 267764649 267764669
    0x307020307060804050109020901090e010b01031b0c0302100c030f181106031b030109060e0603031314060c0d1d0a0b040b070809090f09011a01020c040504110a0303120e07 75
    0x801c4014000c4041c144d10074000d10010032440f040f42e00241080310260002c3c0c951580c3c40d042e0401c200001d1054040c201c0080c2030400142c03030300d00c03800500114214030f2202045681030302c103010035109200d00c0016407007025007400781420700364000c0d0282c011204402c881a281884908c441c804125244004d150042204901a50414103108031948001c1294045004240c1070b1407800d02004002c41c000c007012040041d00c01d04212202c1c0000c0341c050000c0303100381d009100a03482c0300c0c03200303013448121081350382207101c14030105020846500400c0c0810210f40505840c4816507074012080034070f084054241c041c0303860442c84c2080f0030b126050086546c0c0110600c82400121001030080540c0342c01600c0c40ca040c242c0740800980c0002c0300722803082002e080c120500071414824010403000ca1104070403031415041d801d000035604c1c941084810300c44da4550002c1810b0001014040b0351a10010780040ba89684904014182400311036802550720f2a003c6103048010000c81c890055400038a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 267767149 1250 267765899 267765913
    0x8011b120c050903070815010f0302090f06041d0a020a0905010f0501180f0b0406080109180f06061a091e030d0c080c06040606090b09061507061b0305010807060203070203 75
    0x240000207010418503981070001c01c10006034182e4040080d08010501240205940031014105411a2070706a105250354001c2440620059841d052500d50080c00c1d1009295039031345280008018088600d4182101d12016882401106020800480103402910640c00c216903a5070b051080701c2e008d2140301c02c0307000b14807018007080d0710600e0034208443c8180c1d800c071880c50f1108800301ea440540c1d800780e040c1410001d41005659007000302103004001c00c200400442c51503040d620307018a458003004040001400598040203900d41c40900640034508a00d85c003070880645500d0039a0058604502c241e012a201c07003840442c0401c01342e882170002d005449004401c0380d042c0c0b0307452000041241c041f6024000c04890200800c104d900c03c500030400462844c0c5440000c0d011558109c2c2c80320702030200c0004000300d41e103c0100606c00040101d01c810758131902c078180302d802040b0b81c444d0700d0304080c003064113016682c0c2c1c1900504c1c1645c4140d4256210203988070416030303030f038031418000a4050704944 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 267768399 1250 267767149 267767177
    0x180114120c04091505090c0109060306050904080a05070507141c0507050f03030d1410050f09150a0b04030b060306100e130606080d121b140a140a05030108011b 70
    0x3400c005032051180313842100e90b41e20f140c15082580c00882c0c000c10700e03900902090000b581d00c8807540d0000c00850404011650800012982c1d03810001d00c080c10103540051082c50300c900c11001c80b181d07141c2082c00d840d441a100c5030b080c08840d400445407481100d4402844500c01c01e4100350340c0300c40354400300a20b002443e040038480d19a8071900c1030b81c0c0c1345c0014804114600254050568405010344440380b55180c4000344940001c040d801c82070095181c21040a103e40b01c44170020b8128401c048442022042c0c000014444800c581014414003c081000410840e070140c1b018000c8408405440f01030761024401070b10040d03103206030b40070b03c4486008100d40c4800b110051505c1b500410000c110700d900c0700560751030400312110810004031005d080d004150b146d8030075140c001151104621249040050080c00f519030305030110700c005000592041241d000318116001c03000b090019540703410800724068070310f802c09d1194907555424185007030380c0c00b40201004800030f842e0703485d142020110303d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 267769649 1250 267768399 267768401
    0x201060519230609090703060e070302180111010e19061107120e04140108060405120a02100b030a06050c0d06080a020114090f0303041205010b03061611070302180114120c04 76
    0x1c020010b800483c2041a00c03140d464641c440c0c0e200e0075440d28041055813070a680c89140c1c07000108140c2c00c052050004180700f68100004010410b024a06035122100110030b60f40141407111050040d8441d803940c41c0c510700c0b001c1600391b5110740100d60400104200c5000d00903107105440008081d80c2c18660700e101030030f0090b0058041030300c0240c0006120f00090812010028080c0c11030512544800300700802c1041c10482c013004039050a96141c1041188040a96501035150140d04060303101c500c000345a4800f00b0244500f5508001c0c14403044c2003901d4196055488400c0c100070050600b1400705c2d0b03828000610006180e810b944112100034a4901001b850300302458459000c900f46204000c0c0d41c0c0d003000544041c0194038041d0f500b002c0d0619140b800c440f05400030310300a4100d0410002c034070389074418214004d052800c1002403240700c03c0d078180c00c1070b025804c002c0d03201e1605005d80706413200110640c1c0c181d4a640c010071010f03c02900400c441e06550200c401c00641c00688036500d94249 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 267770899 1250 267769649 267769709
    0x604110f0304140a0305090310090c05060a2d02150613050a0b04050901021b070302060412031e0203040617190f0e0a060504021809070303030b0f060a0201060519 71
    0x10145404a00c3c1e580440500709000384c3e80683c00076030040750755500c6203024171011404665100c4d0400548180d41d031241081419441744d18402d90f13000c941e02c3d4100d030090264022000c0b100d08031800d569800600e90809403e8070f2074070801407040f5120300300404160615103007d61001822040002c01c52144035000c3c0c68024041503111351240610100f80c0c03118060300c2d00641042c0005030700c1d0080043e4148081c00890280c8580d540504810405a111305049905480307140150120350441b070300f0182c624441700c15030425083c03000b0001d801c00c00d41c080050002d80d080d6607604030251440c40030700c059400c41034501080710229001550381d1a88035600049410401240224003950058411820200e1101c0306491864aa200b04804c44c54141301100c51401c4050356100181024a81d0035a039038800c0c00020305159403140c1c20b40c43e55980d00c000403120000101803550f071340c048d010000e02074501c510400b8002c1030701d07800481041d0b40f440c0301001940d22212036210b00510050280045120b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 267772149 1250 267770899 267770903
    0xb01150206010e0f0709080d030b010e0d020a030204050c040f0f030302070609054203040b01050a182706020706050105040506060d0b0a09390c0b0907091d01050604110f0304 76
    0x46c20b4080010403100034000c508900040d0b450000300b6400040024000c00b804800092107240c14410400c0180d8860301c0b1001500d4040e1800a942d9a404901000d9840b03150084c40d05100c10720340001303103135500355414000e50f442582601c40c01a41d9010946901d4030a0140943c0319045440d482845d41c0081c46c242d4921007040307401070310500703084510640d0329903a14550030a200008108018440510b100314014507090790355074111441c00c0030906c0f0341003c00d2030010500c1e80b070f8440750342c400c18150955400c011440002600c1caa07400c2c0350000007507020f03040803a500c604041c000161481c1611810b4440e480c00b074249841d203003c19103454000c1c40c0030003406500a004010105199a80d0b1080c0784c2ca49010034041400c401c0b040884841602c0c040d200050340d9501840e400d10388580c841c6903035003a40c2e0700c9820b014042e242d16210900b08801900b154461038030701542205110110075a650341200d100c0b0080107283c5a100034070040c0c904916812260510411012a8a00914006562280c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 267773399 1250 267772149 267772157
    0xe090f0129030703091103061006080a020909010905090105060d0b070c1505041a09030a0516020319080a142701110a08030f060d0b01030305030a020c0106030b01150206010e0f07 78
    0x1090141c51040030380c00580310400000d41d5400c0d41d40412625030f8494803522821001003120786040c0b200d1071190314090040c881044140e4001c00e009102c0381d0103a480410008002480d20360710b0b06800c2c80200401c913110407076503007440d0110340b19007008120700016032b4005d8848680c0d07942d1a90162000402d1900c215518108401d17018078034292485842e010b144505045602e140340b01381c4281d210782014005c128103030810011004502d80000c1210b501c51281155140540d02c903000282c140101030900e8840d030b1070030a01200400401000801c180462500c402240c10305221840b100c03030090100c0542c1c0001801d07035001d444074403a0746245000c081494080944041030b41d501d8148940844111403001c408420b2018185003010250b5000c074003552012540384143d100e0340c117524411310024042c080004003203568810740303404580080c1010002403250f6541c03450b0181d2108024812140080c8814010f5032101d8800300f1031174101c60211400341601c0d155807900300d115000c0540352034240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 267774649 1250 267773399 267773459
    0x7020708010614120601060c11060403120e10020c090f040501090c08100606030203070507030c030201150b030402040b030a0506070f0203090a0b0c0c1c030c06061a0a0e090f01 77
    0x2403024020701c400b400c42007803150340c0050068144a07036204000498086a0089801400300c2c0c0d50200600d0a0150400c409440c000d070203001240e0705200304c0e0805403e074401d030703212a00700ba6041880c80c4000a000da030048070134814330b0001c90b01d9103c0302c00c166a0001444021032441000f583c60290098010700000528640315560700c1d0b60f482659115009540003000302c8240b807031040c4661340080030306040642c03071454a040d00402d54030944c00010240f01d00c90380301d00c080c940300b5809840a1901c84902520b01c5880e268510140c0d042150100d05c22418200744410505022a000c0c0d100c50703001c0010f102d5a100e9001c02d848040199951b0380840c0301c01c0c8008c2e0403aa41d07100c85800113014800c002e95550060341c51060a040250110303d0040c0502602034071140c1025203500300d02c5030149031100080c0300e03c1c50480050407103540420b280c00101800100403003100401401070f80e80701e40b03d070b603040640407040c40031820080b40c0145581041000421180014064090300c00305941c00461030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 267775899 1250 267774649 267774659
    0x80702060d021603121b08100e0703020702040b060f031315050c0304020306090d021c030f020f0316110c01081305060916050d15021b010c0e010305010902160308070207 74
    0x202e030400e982c140301c00f8103041c40b00401d0540107614100d03811140b04051040c034030130103450301ca0000e049440d1020050440b001a040e4040f840003c2c000c4c4c66202c014032500d040c81e420040203908440c6041c3e00c42c03803030801b940380c1c145426002c03501d41140ea51485401e41e940c01d00020340d89001e200c42a180c0342c1c0280b019881040080c03149a120b540504006a140d01740390051618041c0001d0003c00d041c0c0c85110351114480e0000750102903260509481c0c14002e03041c6030201d01034200f0b0b0700c0f01c6140a00200350a10004400c0010314440d000211000d408140203800454100103108119101c0d40c0110104c007055503c00d20308198005054113100d0303600702c040d6440c1d61501400316103110301c9030007150100030f540c02c2807410707807000b080c007103c0403440001652940d282d01002c1a803c120603560001c2c2d0381e141c521142d0512406146c14600800c6100c28840c0090801503c00c42d1903800a85032100101c3c000075280b082c1c0e00055900c46080d02150501e0f40c0c160354405c0301800400961040410000e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 267777149 1250 267775899 267775901
    0xb011403040b041505092a06030c0705150c0409090609081603030e031c0b01110d05090102010b010309082a07170105060901050321070c0b0901091e03080702060d 71
    0x1004900c10021003003103281508220013091204012504194100814480444d100183c004d98036a6042c100e001e10071044100c01c204c0c84042c00034150810750100c00c200f0b1101d008000741c032030507002e0401c0d42c5580c084000c80b1500b80324100c455030031250041c00144503c2107564440c10100d840349000041d21030303094440800c0c40d007100c02039001ea002080c03001402c059140c000c80501d40b04d00d034025814020031402400101d0104403008550756038403814251182c0c1300d20f22040542000d041030741c00b0707201e20350710080c42070f4800008280550708088460701154400e104002d11140c004010300d0034010010360315001d03d04511018501020252041c0d0003042090021000500201030a101200050742d0700d03500303666005049510404100e0010803940e200070555246505060580301304014200d112415a4003c000015000300b042c86404100ba016140052070360590980315424000e0303503003900618023500702c20201c650500d000c00810005102c60701812071a44014100d9080c00307541c0d10f03050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 267778399 1250 267777149 267777151
    0x70308071b2601060f0e04020f040c02061b040b0f031003080c0703030e09040c05010f020a0605070906020c03011b050c010b120d09090507090b0702060d1113210201030b011403 77
    0x1040102d20525107100c41c810300c0040b241c141142c000340314103440e0001400012817140301c0e801b2030f182040d00280031542d960990304044c1d40c000b4001c00c01141c206c40020343c0e03804d0490301524980f03d4107610401c0d140d540c80541d000c44240d10326203840c0034404c40000040360006003010b00440109540400003c141da000b410460860754000c21140d0b186040081c4140006144240124804010b101c0400d00100c1e898080d2082800c3c07000c044048a1412440d214288078003500041c030f804240041154041c0a40044442d40c3d0f0071034181c81400402c0600300d0345d1030340710403000d1510034000290850048001d031040c42c1d00240001070325503509000c10b500d9150100d468000c0e03003103203c184103e20b070000340403005401c5503101001a1b00e8404005011071115014a07903a41c84040b800c1401c568444084980c0001804030522a83c8403111a810094010352020b4004c41035484011510591170180451003603459031011580c5a81380e0010b4000b00a01c41a160400484c1075800c3c401c0303c0480b0080d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 267779649 1250 267778399 267778409
    0x90f03070806090106051507060b011b05010b0a0602061009110705060c0406110a05030a051804021603110a0203060c0d15060503040203070e0f040b10120302061e0405070308071b 78
    0x42c241e00c0ca003094000b0308551958000a12603407040da92426201c440405544542e50702c4540003407098501030045e5601c4192001e187d40c0e01213500d425404021043d008420381071380980c0c0050200342c417000b00340c3c0c0360700c401c50b4401451241c6c10000c0107540c01c1c0d074001c0d6451200e1420400c1c5007603415150f04e410502c00712522912210002800c2000543c069141c1c2201d4800c50080c0882d0026640c0e034585901c00c450001b806c2001c0860003003258428802c5652952400400131507803813140b000000300c00c0000203002e80100704120070700c40110360b010908011440c0d00401801c500d903103129603004503401100c2e102e4900c1c2c0d40c135406901c044594400a070044c0905071100e54403407419204240c580b01d03141d0000c03204202184180490207070729140f4660080c1c1e01581c01c82c032540d1000958001802e5980c0000d00d0a070790b2080078414182c010856034000c030040a0907003002c52040c6060701000b6002e4130000c3c0594040402000425800c0c8080c042c854422000700d814004403e070180c0b84036482e5082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 267780899 1250 267779649 267779653
    0xb040e0f160b0307081b04170a03030b01090b0901200d17060105040b0a050703023c0a020303120c090a0b0a080709080d050c01060f030f0210020c0d0602090f030708 72
    0xa0003404000401000c005100c4403079003601e14a0840130042ca041c0016100b1a0810038881c0b40300e541d00040c0040c2d801411520a903082a0144903000c29500c244c003280c140d010a103002c1c1202e807154411420710003030b40c6415151070f00e860031100045540416003408400030100d900e4141c98540070a005035814161513503205220000011302121150344003400391418040304000800118036400c00b0f45050401c98100251aa11141400e904100084502e0002c0c011180804c98070b5014410a40c8621410100c840c614003145440e05960741c6c1c50120302941c584d000b8020507442c8130508034203a9001c1d02014a590a08229002283c4858043d03006955124008980d00d41c000b0352115803564420f6091500126503850049442d4441140c00845001c001c3d0004e0701014492094026000801c071071020542111f6070383c00c0514203d15030075412442040c58042c032449951000910a60406004018005e60f40c0305030342d884000d6202e1005a50010403800d442071060742e05009440041580d040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 267782149 1250 267780899 267780913
    0x110a140c100c030c02010309260c120708030609060a030b0c03040b15010819090803011410051e07060b04091b090e030909070302040e01081c03050106050d0b040e0f 72
    0x4100860701c09140603001c1004602007508000c00d90002d842d1295540a0030002280c100701d08150091680210420540010b103840c0e1040255503840200aa0b044580a0340d00941001031404aa8810881c0141144030240040303002c41c5080c00807540c01c18001402e925013982d40341d0b2034009200f012030f0340700a03050001c8100300902125056036070380032090540042002140400292296102801a015491200341354031100103283d44150366140e00980c425442c0e60751040561000583c0400c42d600410a00c52022180c501030020383e400c00d40038081c0d020b4072201e4100c40382e04036009004244c8403a619014004115251403299640881c0901c11642c142c20380c01c800342c0d0817190103034010344410b49024150100141c010040c0c070080e49044a455480e9200ea10045000c0e008030780001c19010246c01c0001864480003c010f50001d4039090103a0301c0448944e8180c0c1183ca0901c21a4007240c410081003a03106040e500c05a01154010000125001089051460103039004011089c0d980034103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 267783399 1250 267782149 267782173
    0xa2d3903020604170c0a1d130f12121815021309051b0d02030604200d0504021201050c0703021203010b04030201210f0b19030f0201110a080d02072a06110a14 69
    0xc5e441c0c99100e5694210030100c6034290f0740d15454020305d5100503100003400801c01c903e0b14411a00440600c641013418411554400e101e2085411100b00072038126078000308000746d5440d2130003070f0341c1da9807070344200022994982003032432018080040080c1090203c80190b40b0711890342c800071303008030019032130010784901e043c0d02400204c1d0110006c03c903644201440d001d1448040008540e140100f441c804952078940340b0110ba0741d42c01c04030441120b5424002046180b0b04400058076a0078060341c210341c1705004816421050344803e000e079502e406800c01c81400075502540d286584000e0a101d484000081041c4040403503810712440d070109a103491030703c0210b140c039480303008040c9040b0000f11561450766461140108600c07100038180550000700043c0c01205129494030150040082541c514039007081c40d00940c00030108982d102a030307001180c017182c9203e1070a010702041e401e02000c000d050440903030320380503500444911481112503120000b03044240c05c042d207060020003840c58800744 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 267784649 1250 267783399 267783449
    0x40804050f040b090112030e0402030a1415030c1c0605090d0f02010513230f1005010611071716260a2d3903020604170c0a 54
    0x14036240c0b44154240020711810b50b540125442c1102d584024010408582d4581603811800400c0c400303610600c00702c10081c948035260440490480c4001c00c140c41c07036982884105c052203200c241550198407a0403000050301380003240c00c4011344002400c203041643c55440205481c004c40707001425810400c101031149400a400a0032500180000e10140c9070400981e5108150380c10003500c40f8012501580c8080d141c031041600482901c0241c4440064419540e9030707907803110300302210040c904070000030964880d14200030070148400c040c200c401c0c581842046d044038a0f48000324940a40407c0240c000400c100c0b140080911514500c03841a014280c0d1002d1948003094000c10f8214034800c0c40090301440c031043c1101c08003a4018602506244800620309401000038060040d400c0c01c01c044d58090070b0074101c101c0006081c0018078049154075100e550407480001d402481c10703c000c0c000c0c3c0201e00503040c26484400c00301c2e5008054040040c0d411181135002c00c101c101c07018800a40c1d6401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 267785899 1250 267784649 267784669
    0x22512020c03150a09030c0215040e0f04050307060b0102070906171e030a0c03020c040606030519063002060a2a1e03020c042c0a020d0b040c03080304080405 69
    0x403409402d0143d030181081a02d42c3d4000c0c00381c00b03043c1c0daa243c070b901018013640d07281e460b07190041c1981c0d0004401064512140c0d10902849104016040004d01528244141c242c4100c0d0f0040c0950b0411007540e8450024044070305010b415401005004200b02003184a040d00401c0d0784504854118000e000c0d00b0700300254620000c2c0103900200f9045000c01c800401c031390034401d051811180314000750078202d08105284081550150501c01e0000b140d50340750b0480c0d030040d8181000800b090000e40c3c180000c40c0d10910031040711183d4801040c0300400f200701502d08041e90710000c044404c034540d0016180364000003002000c42d00e0a800c0b41442c81d00d00f023581001e8142001100c1012600c1c3e02c5020085c9013640d5540f00040018031144201403081c02030071000729001d4010301c5544000e0380f0340404d03420001400d40d501107032452080c00403c000210628040d4020740040a606403544900c05030080040041e640a62001800000203108200544c4280d0203080c055840382e003414204820303080303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 267787149 1250 267785899 267785923
    0x1003060516020703231005010501020d020a0b071413030614010e01050a171006030c0513060308033601060509090c01020618160305150606040f0902251202 68
    0x2012409101c2a0700018403205a80d08171072080c10782d07a440c2240c0000100040c80500b428003500350f9207104540c090708030b00e040e031b4026020790300c00b9a18060201d9880c200d0000c00350001d0350080100e50200c0c003a1a070700e0685a401001c2e1890100202c160400010340d07540204c0343d041e9181305c2d00505030600c0510034050700040641c00b825515010020700800d00600980c0b0303103001d0003080599a2242003007280c0c0348032004007003403208640d60f041c213906941d0701e4841d8030300641c0146251100b0407013511420040e00d138011000360464464007088101480c040e07a80803804801070f4004c0c00d14140590700c1142c403000010020849030708003024041c4207240039200c1c00c01a80009a1100141c1c6c0104882343d020f000039074030401806281603c28034202000300c8500440c14144004418001d020030284038444016007541215166070382841a10b115910840b0610340c1030034424044144141c000b0f041d9020007129036085000c1e1107a2034107000302031401c121100c1046943c081b4407d41c0610451407208 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 267788399 1250 267787149 267787171
    0xa0515060a03080340020108100806010909020402040807090e010f06140d02150a090314030c100c0e0603011806090b1315080d0215010506070c09020306040b030610030605 75
    0x60710b107a50351906800041c1400803440305c00036241c284007541ca002402151704283c084880d10305503208150500c04800400d0380081c40e0000024088407031258200c0481d030103100140308580c81d090000000b0f2944010407a8499000c00000a03152010442c000c041c148a40c1c0001b0b04a002c0300d103c03421147e03000c0d000b04825003003030420080050130b80342075803000c24107681c000400040d900c00945036810060b601499150040740400d80c103a8094060816244503007150b004401c00392041039641e0007002c16400c00f56028440641941030540c000b8070003240c1e01e01b0080310440118002070b5003038100b6040064010100703042d29150142a00540f40204011b003010440183c60001040b070720034095040780042c07a141c604092500c440b0910780f2004100b40340646000c00d04144000f0345401c0d40010312444241000c002140c0d920304030007200c1c2866032010b841c06545c1d18006040c0c000c1e4000a05003030340301e40c2c0c821040b10151400d114261203002841c800720b440c00d05502d000002c55078040e19024040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 267789649 1250 267788399 267788419
    0x6170610080106060e040f0f0e010b01260403050f041512050f0408180d05100e0607080f180a050a141b03030306091906060309023d0207080a051506 65
    0x2940101208008405c10b0700c3c040703420580350308071502800400780180841403a10015440b03643c3d041d8850035001c41c00340c2c0c0b44040309030088016216203c070300c540400401d0244021900003805840100348008450b0825401c16944502c42e41421070103030007010104500b101c0181c1406241c6c811039510a00a050180040c02d107034603601c16500880c06072030b1a116090241d08501d48d15002c000c5c03e9940d000046400d008694540345001d8102c00910340c85a210b1040070504181c082c9504601c903002d5066400c1d01e40c1e48400501e4040980ca440604e824016441d500010890130711401c881d0b103008800001c0c0801407a54942c0c9461180501d06520300c43c0c0080540d40d60344d000c0121b940160003101d01c20340c44cae260803090501c03d50007203003c602d142e480c080000a006400d5080104514001c07038546c5c08a404401840032040c00d070390f90010081c0d10003088100c40c03e4a451948034561b2092044920a54942000901e41244002c05848903401004200d02d40c01c101d01d1311643c07003c016243c103421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 267790899 1250 267789649 267789659
    0x603090515040c03020a1d0601030b010c050111070c0b0403081603110303180601060e03070302090408120405010b01090504020901080402040c0e040603060615030908030106081f03060c02010b06090a0303110106170610080106 98
    0x403840038040904154132030184052a0780724400dc0c09803a6004002003040141c9480e0301101c951104400305d90b65070f000c00d800190b0000c078100f901c0c01c0301c0d0040c1403203181052841d04814914000c3d6012030038002c0840c494103c4070810409948a0712103c2248a0010981030449180031301c140c0c006c900f0000e0045801c2c1e0140c40c003003000021290b0543d200c0c40740e61220700c2c1a203880e00403d840308007018000810003040c000c054100301c000c10f000381c8500c4005074070351060200b0f81c818120060f01107103101000c613006044c558000442e2041030f01d0207807200c0041800081c1500d0007039000b07032440e603100d03e01401816044840e502c0500e0031824108a00811a81c1e070140030b000500c11401840300000004071100c6405210396907000b00006002d02c0d203070700ca1030010300a203010401540190318082e0211060706124084554500009001c0702c940344c50340e94201e803200c08130f0442d02025500e4100010b42d01c0e440440003403600505c0e002038102032815058000030b4000e617600c1003405a043c15000c101c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 267792149 1250 267790899 267790949
    0x11508071a0919060905100c0210022112060603090604080f0706060b0315040501030c1202060c01021315020604150207060b0907030b040f150603090515040c03020a 72
    0x4031a001c0c0c410441c8440c440c507403800c00d801aa01e249801124440300207240b0320520043d402600c26503141c601500b81c0740c43c24003444412940a031000714820382d221001616128035003050065072841201c01c8450445c05482001c0d0003084480a4180d0110311080ca0a460901a983c002c200382c2d8817909500d4054440c07503480c480900007410141000840401d12a1640700702e85215802c03100921840d82c1e070b401d1441d2150710840700d0440115406071007900d24a003d000b943d048980181c0e201c400b0318203000b40070b4002c01c4200c004a074003c0003000000d80215081c00944160801e190b4400d2035145441c01c140201c403204415402150000302c00c020000d20b801c1f08200001c1031604d401038843d80b461031320200030803060f002d1647c4020030b1000c103e01503505403c11854144151003d1100d00d0400d00c126046c2e0301d0710540c0c19000f1205140512805219038821050240650211403030303082d141421030303a020701c140ca041c2ca0f00f00b5010350038025801c09444a80040c4840001d240c90108080c075160317 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 267793399 1250 267792149 267792163
    0x180b060d06180b1203030402010c05071502030301140102010207020a03031202042301020c030d0206040b040f021206010f0b040e0109050403050f0a030501061814010e0103110f1c0c02070b09040204090518011508 92
    0x9c0c1444280c000003420b100d001c00c0004094040d49240810380801200b0195581d002403040d490600c0710300018207219481030080c0c8007a04c1d8080c0c101c0d1111070450360300362407a0a00421a400540e17090200048070541900c1003c11004034500c0302e10706080240009051802d010503141c0a6404201c4852080745d0001d180c13035000ea00000c40076182c2d2220b15002c1600040b01002940c00b0b4501d04410b2000d81c03000c10205d040f650649200c580c0c095944521342528000c40c49a81000100c035001003000340c034203801866000780b00781b42107403800f400400100415001481d060340060f9507400103016540c1c00c00817002032070300c90b0202c010b580c074644040364004002c9030032054100050506c3c003410507402908078248003040b2301303205512110003100a4019400c41180519903540c0e50090300c904504501c148501c58000d540902245800c100345081d203644087c041d40d8000e6820040000c112005100d40390013a40080240d110012103c103405007914004070b00910740780103818041026040001d00c407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 267794649 1250 267793399 267793403
    0x170603030301230f0d050606030c09090d08090a02030a080a0e0613180e10200301080c10020307080d0903080603010b091902090a0f0501020610180b060d06180b12030304 74
    0x51412081801d0120b01413019501006400c4071a0f4a42c01c02000030100d00759105810507011103258802c0380d81086440001034903486aa81c1140c260240c403903110b080e171340358000760b801704660702000c542c0d000c01c1c03a140c0b003500d05891543c1c0114070604413943c03254043d2901c10b4111105410b040c0d01d0704e044983c20b0468400d44918500e050962903508000b41c002d50032030442c140907a4494120191030030043c2c511a801c0b020400019122101001e284c4000c0e24140d40e1980024a5030300b007040280400e0303000181c03c010039444103206203c0080d00d4400104007010724807101080e401c49500d0054405d4002500c064403030f905142d1a82180e84801c0000d540c0661503a1349110303114201c8103444000c1c41042d075021f4011a400d000402c0c859200da4041c8100c3d00280c0c00c0b0380c01980c6804014050f038245d40102449007401d101d01c5809488150807401d00801c00a10903840c0598400400007218071a51000c2410407040e49860584181031040410003002a6840321414848840c0d04d5240e210003800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 267795899 1250 267794649 267794699
    0x30a080708100504230a0501180e0601120c08030a051e07030e01050901030f0e1b01020a120c03050f030a2a090306180803090a150b0627030a03170603030301 69
    0x50a040d0b5041c454070320321000001600743c07518145504101b01610090240d459426804022140f82c2020392040b0703d064281d080140038140d0070300001814441140c00f0948000400c80c102088065051006100741c105544030103581702940314105091140d82010081010402e0001c00c001c42c3c0c100301c1002c0c07094400d1134000c1d610001800180c0040001030138441d01d081c43c4c412919484640001c204008079003c3c0a1a1410000d40004907910400d800004050084054240c03242c01c0c014001d071403110380310b0b0400070304228000354433040c290001c5944500d9162a10900342084256840c21404010310401000f40c050072003e01900180c2503100081242e80ea4090f079103000400c2286540005034040d0f036040c1e0360704000c106655200d544090903101090181e43d1500030700c1140c421b1042041e4090021790070300c2d000f0f4001c0043c8142ca19100482100c2070403008180f541c0502c1080c4081d4400d840700902e0044500c03100100c5100101214001c0d8400c1005016070443c05800400e18011841 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 267797149 1250 267795899 267795911
    0x30c1112010c03050603060f0606040603091502030412202808030103120e09010518040302010608060c0c011d1c111b0907020a020108060f0a0f0305030a080708100504 73
    0x214268a11400051555501c0d000b54464041c0e07164100714005c000803401c40d049900c455620854144007902c056a00100800041100d0b902070f030480b0740c80714041c4240c071121798840245582641d104940440e02c03502510344c0160f5603070b0003444c1084501032804038007101c0f40368a040c0c0390b0307130388031400408105541060120f4003280c0c90104034000113520048480e2607507074070f00c1c000c45520b40d913039441c40108405680c0c6842d64180700803403034100c0c1c4c00149005c02d4003928090824419402a100780c00b15500c0e4070012509040401106014105400e00d06030350f01501080107003122000c0815a80010420a0008154000280340c0c40d0f008610b204041007110038460075603050307845c41b0244c001405050300301c00d03842007540852401d81070190384503107441d43c0b07005040781c0300d502444009010510017008071b105801c0005100944440141c00210310a858091100b0503140c103a02c1120300d680005010b80d6280d0b070004090780c00c44d40d0344c10841e030581010340f4110300c000c1260203240d02503540e444c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 267798399 1250 267797149 267797183
    0xf0c0f06060a09090c05040e0c0907020c01020703060504020d050706021c020a021809070e0109051b0705070605031e090c100801031a04080d0510030302161406031305030d060311010507030c 83
    0x400d05800070134000303200700015180310781000d271100c09084280e882480d04000291105002055942c0d20b814168041c12545040d96a008001d05020b0700c183c2e0030105d0041000009a000c0010802a0500e600109803142940c00030b2800e450a820b00c00c0b0031500844003820058540d800b03150300d4803450040c5103205549000303d0710706c4c1c0300860b03001020201c0320000008a40e50b80354042402051640c015a10794402200c4503001e0744200000181aa40445800c0003a80e01c10806944c0001d4424061800c01e40c2c02180c99010560903a032441440c1c0082c441d00f942441c080000d08140601130600030304039895501c5695548121015889420051344000f6042090240494540c00d68106e01007125040105075003803001850f001c02c5000d446407400d0110451616207145040310340901c0700408414401041c45501e4001a00006901c442c000201c000203030248050164509000c00000309149107050120b010808044402d061110400880010a074400001b0604030b41066040940c1d2402c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 267799649 1250 267798399 267798413
    0x4050717241e0f040218210a080d1416050a05070f0f05100204050f04090501020909190c0302040e160c050601081609051003030c0602040b0f0c0f06060a0909 69
    0x241c05880c0e805108082d1410461040103001c910209040e1212000c120f1004180300c101d10034480c2c10180102c03843c9100000c0e142c4402000d20090503075403000c10018948982501c2c241c0f2200c0c0c2115144008107254000920b01c0c030804102c8842d200407074105050100c044400d40c05910011401c210000074081b2590703001e4412a0040ca60018984845076140d0404541f9181c0c00c800445040c000e101c080302010f40300b40291819180e00900443d49045d84504000091590302001c0f20ba40d5003c3c010704d941540c540182c1889007a084030300300c41128045074a80c3c02c8424551145c1c1c10b0500c1840b007880044003041d55a68031418480406004100002d01035a40d030796040c00050283c40348000100365074901045400001842c800100300700f41c0ca0360002c0054034003c030740c41c815401207414108003280c070880c0c07140b0640d4001e240c01450b00e41c0720500722302564403400c60352000503c0041c0082c0c0c0404100000b03c40400784001410391420071078000362100260303101d032040481d140d101c81814003804d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 267800899 1250 267799649 267799711
    0x60905010c060b0a0e0106080f010f05012609010507020f370f0312060603060b0a051309060311010906030c140306060c01020c21131a0906120604050717 67
    0x402551380070355554402c14031800c090040d0400500f8010214a801c8071310721103507058690380103041d44001d04000044032440c1c1c0442c2000341c900b10401c2080340881d280d804d0103014520880000c240c51814001c00391400c0310503a541c4942c0c0d40400f0b00c000c2d18080f5900905284013405441c0206000c6640c1003410946041c0030107401e446414100104154000b5001e00311601d80f28400e1000c29554071007175007180c010380301d25141c000e810400d181419118100601814005148481d030300d5854242c84012a01c00d500100c0e400e010103002e8004940e04201c1d41c1c001017100f49070034803000c1c51994000308000302201c02101c0010001c8045401c50350b0300020741720400b05c80c8000f1500d0304680b504107a0b44403461145030400e0442c56607464804400c1d28122002180220701c1c10000c5890318140d41c0c880031017611504a03a0f1402d011500450360380034001c08015001c0020480113040500c2000100c5070050032100134009029040c1e01442a01500d0380d90212800102c1c8030321880c000828541401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 267802149 1250 267800899 267800921
    0x308011a0f030906010905060d02060d0f0603141501143019020a21030809070f03060207060b01051809060a0b070b0103110324061302030a0b19060905010c06 69
    0x1c004410414481400502d8a04841c10f40d001440292a824241f107002200c424005e03411000401c181d42002003d40c00074841c100b00748000160b240d03620b441e2180480c5030540c684c00c1d00c2d0400d0001070182a10749500c01c0c090b00450700c0c0200c070390702c0601c0000c0100c0514601601000d000710050320400640c84004d08030406c600041d2012503005885200659a050004900c00c1040b4074003c41c6c1c1124003030a54940074111003000e503911480762000d481d81c00e0018030040181c4901480422108290940e81c1c0003103208060168648107546080780946a5084029040020501480401191f065402d4141080a459594a86d103902c004070b20903810700d42210a0040c0c4c0021403404100ca0210b1842c100c5c1e0140c5034080300fa600c04c0b820552a040c40902c040c03000b4031988003800a141605401c25003016000701100442d10800d0344001c00c1c0d13002244c003400041c5d07071655081514206218410070b0b00c0150030301481b41c103081c040098181c08243c080e10381006001010b040400885d5803120391020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 267803399 1250 267802149 267802177
    0x81513020a02010c170c040308030a150603021c05090616090e010b040f1208030c0f0721020d05040506032a0d0c090b070c14030a0c09140c04030308011a 67
    0x28010799000b80c06090503002d0728001440b110701a0030880310b0902d0580c026181044064506840c41d198151281c00151080000030303610398038000300600324004800280110707140941c84d038266401050310864441c070030402d800e081c10100030840e84003244455125299803601d80061064a50031261440b868010400c0075500c2d50000c90f85000140180080303c1c00304154084054940d6410b10307803040340700c3c0c0040c400c3c0f0040c0003107614000c0ca480540b20480040c40140c0c240940d80d25282030854a40003601c0300124010310000c0c0c03403981402199407680e41405c211b842c003032a10011801a200c003d200c42c4108034600500b510540c84c20400050031a41000300c0c03500c2d00c58814100c80203265510724000400c80f040780000d1610582401ea40d5110b03003115491440340e1401d441c145000c00b610074801e03814003c0e00210300003d0040c3c0072201c040d010031030002895559800d121200180042c00080700400284010000280c0c40003040e410348e010395104540d061640a02c001c3c1c0750055912982c014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 267804649 1250 267803399 267803407
    0x31302030f0f0f031303020105280815010309050307061d16080115140d0c05060408030d051e041202030d0903031b030606050a03051302090907090b1008151302 70
    0x3650001c0c002c0b0301800507000b03841040342c224040650b80c0c03140c0380050200c0c400c201e6042001d90702581c003408002d0380185000f0003002c005440840b21a82e807640030008241d40c0000d100000c400b0107030a19110200382000c104001032034889a640f800313101c00003010a901e510190114a550741da041407401101001c40725001021b01c00201c0c6007005e4010314ada03540c6045030101d601e01c2e850712101d0880700c003180d00c559800500014840030074000c140c00d903084040c1050004e055110400107000510306940a1601d030380c1042c0b0700005641020703000303c06c0182da1700203142c080e105007000541c100394032201c52100068040416420740c001c04034040c440518100828080c1134058100808004010780d50400a08002506400311160b5025130000a2024801104018065480f06400480c00c6000e0800c862195000406540003252a00001e4121407c20041d114544c080c6080750b060440d4008441054100007d25803035008141007094200080e2901107034031000400703a04002c6100c0c0665407 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 267805755 1106 267804649 267804673
    0xf070305071709030403052a0603040606030602030709090509070b03010b0f04050a0f08120f0702040c030e060411010f14090d03110a03031505030c0a050603130203 72
    0x9010705101103050603500600b480e441100c850b4001c580c1c45085261a40c00c1c00d40c410110a404400d0f040d0300190780d40601108002007400345d070b0441c2c8a541d6403d000010301001c3d03001500e0244000705206415074000701034015141600010300054803010191991409a0b00c00c081480034140014004140588020708000e01e500508500381074807000040d0020555610040040c2803081301006103a00c28401958a16112404581040d00981072003150384107001009224540d86c01c2111503a82c0203030b00400c0c0500440c41240c9031482c0902e0091380140000f805580440d1920141c0310b944d0348688075a020b50030000702c0007170812840c081840f01c0302c48a00d404400707201d400114070f034040c5810800071035654001d0f079000ca01d690010440c810920140e070800b80c0660802c0e588003403542c030341c110404121351080e07511550326610b130501c6000b11140b0440c029414010b440d40012 = true := by decide +kernel

theorem cover : BRFrame.Cov 267625899 267805755 := by
  have h0 := BRFrame.cov_init 267625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 267625899 ≤ n) (h2 : n < 267805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
