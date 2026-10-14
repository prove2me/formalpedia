-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1932
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:12:42.706028+00:00
-- url     : https://prove2.me/submissions/2265964c-169c-474d-91d4-be497bff5eb7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 347302158 ≤ n < 347482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 347303408 1250 347302158 347302169
    0x1206090a0c080c0a2d0b041406030106080105090a0603051906050601050f180f0d0602040302180f0a0c0e0a0905010314030322020414070309020406050909120306191509080106 77
    0xc01ca0b18104039a42c02c80c107001081104181140c00e40030217008100c910024000c10541004585803418241c91600b500744025a90b8040c50302440104400e69104503024115041074038645e0301034a400441e000a4100358202421912440802c0c0541c1048400c0030080c2e98003c480c100116120100111150b00ca0103450781c01ca1903061040c2445141580c206000900f0000e01905a03036043c1c00c08512031400c0400f060312074641c01300e000c20560401c150606503601e0107001c01c2e002d9207045d0754070130810440070b44007850b5075039203000d0852044e01036045c4480064001b0320006555071b481c07103610064902400b040b200d16818001c01c1881d8100001600d001d43c1c0b000e296410034801e000c0700210500c00c001c20599019484d001d0702c10303c1d03800595a00e400345c0865a408a19400307140140800d903501e07503202d00e0040072000204005980f01040300e40900d0240c00c010742d44c4e500c2d4100003407502c140440740c0c540351041030f260014201203080520604014280c840c0940300b95584046401c03a651032148 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 347304658 1250 347303408 347303419
    0x10507020a0303020c2b0305070f3f020c10140624031608090d0509060706020912010501081209011704020414010b03010501120b0a0b091206090a0c080c 67
    0x500000f40030b13030080c04061000303c04507030700d100401c0005801102140140a0f00e1540d500320209056818014650b0000340c508004007505920500144004243d414412a1983d24005a0b0204800c00307059620141408035003041024540c008100950160045081038071514840b00c6030008070380034940b061000780150002603601c51040c0621165003200120103064445d0500400d05e005002840c010710a42c0303800c0d1045054288054501640074024075600d03488400448801a4480c048841c1040151075003500c841003460100d010b801881030190340720748810503802a0240c150b002e82d04841c005012118440d0f502000d00b040c40c403aa11413240000c061040c0218002001652580c00c588082d0000618100464004104681c03c0e0070007114114000b004021540c2d1103203403800a408910010052080391000145c84070384940b25040c85030303c000c01d101140d0381da4007048803040c0c1c8111080e588145422803000c2c1d21010034140c1200c50f0528000701146e59400002d400c5000d0b48050023 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 347305908 1250 347304658 347304673
    0xc03051306050c0409050a061a090a03030e03070503030409140f0411040203040f0206030708010f050102030408030d0e1c0305010302090f0609150301020c070e090616081321050c06010801050702 85
    0x75030402400c00140b00c4030520304108000650300c40d0a104c0c440c440c0692500001e0300a0400410220217070001c00300003040c581c14043c95106a841c0c0031039400b269850306201101c0079409000c02d081c0841035000d20b030300d400080740005410241d608028022400c60485018999800600031369840068a000d40144e40e451070107046428150300030360b0030074081e86140151240903800211542c0c421101c1e2800903443da00100000e002c03040900300600780c00d002a500b00b03814015000c0e80c81c020038018200c1941c5070b920003910a00c06004124a911255100c550a804c2c0944060041d02081c4030403030061982a001400d07013945844440e004200040059050303480d0311030034454280780e011746954076541c01c001d9031002a90400c10341b03004103004440201c461404001050400000410f0f01503509200d8440300c3d0440d0744520016401034143c405461982c1c1c19080c80103c1d2105108440130f1031004010b201400d42e00240a007541102c5042200c101e6a210800c031402d90744150380e03020245e4003042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 347307158 1250 347305908 347305913
    0xc0b030405010f09060207141b1c020303071b080a020f040203041103031803010b030a0506040305030405030c12030105040b010c050c0123030115260609090118080d0c030513 76
    0x1001180c005000d40000304504120742500c0d0100d4014040c1103411a43c000307400b104104c210f14030419000000809800d44414401156071110b00c48100b40f8420132000c4060f24000456500113042c0035000b8027240d4071007d05160044400340c0b010840c1540c00c04000c0005915032001035031300c3d14264050004070281601c0d900384006500301030412696401d40007a903040035107080001d030001c8880081e440040d0b050400500d806c440101d00084e000307410006094000c07400c0050300c2d0390015403520300705580ea50f075428001d041d401040c4c8049a50b001c0c0d03000c030f000c100c04042d0141d41a02da003240e04010009110005540c1d050402d035000701150410000000c1c0340d805080b80328801d460f5400556000300c0781340c0308180d003584240c1050400800c0ba480380408280d10030050310020002c55000e180910f22948a50411200240114444c00308a00012030390102034104040c070701166001031000301d000340b400080d6900420280444240b5012021802c24420300505006503054902c4840102e845d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 347308408 1250 347307158 347307179
    0x31203270307060903050d110f0403030c0203030c06010e0412050a0e0603100f03051510060203030115050403061d0f0c15070602210402040c050901120b010e03030c0f0d0206040c 78
    0x1005658864007080c0014404600300303004d100842c5200396190782e501c03080c08040c24201d80842a8000c2c25050611045410036440e8040b00c1c06c0da60141065040c4000f01e04c0000d02c2c42c41110b400550b1070003404000102145664842030145214a6605103030088545040b40c0e24001c4405180c0000d000c40750691b40c40c1001c000454014151450179006191144071101c100c100701e510840d040d920145841e182111420b00300d0340c02a004241802680b071038100000d5903030106009000702441e07030107140816140200225001103600800504c403c010b044080e085505c20400c1404443c00b4074094441e4806010950004043c8014914805081b0745c3c180b0242d9500410300884606a08004506064000203020580d05070341e04a590ba0901d820b105000c00d9a05405100080c400e050246030071981c0c204c403160340301c00c5041000140c89028038004035043c09228030426018040029074100419000c1080b501020700c4104030b5040c035102800403a582ca070103c0340130740f80075422035003400b425401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 347309658 1250 347308408 347308471
    0xb04030c03020c03030c070e0c1e130504091412040503070e0a061d15150403031214070c030201140106020c092505041e06080c0d0905030f09031203 65
    0x340b0448440840300e02c0131924680c80210703410300c5648807540c2000944110741a480d03010800c900b201d4105601400c0b110702010658014116020b0b0202c1c40e06000310007200319800501c000ac0041c040300f450390920810034003140746008103d0140c04001100710044804850440d0750103402400c40c1803400c00111803081015041c0c220841d1989000202c0144c1c175024003044070781c40b6003001e140f4182880300b868180c0f801300415000d01070103030b480e81d01c1d0030b07040003a202140e4250074401c0b40b44aa07459100020201c400302071560020840500810640c1309c82c51a828900c281c0080040715040c041c1c44104210034880d040050b4400460034000e41003902c003880c2c02058501014000c0303001075203001c1d41803014400701000250007180030010040c800f01a1100c0032050b004116030703142400c0d0014081c8100801540c158500002c03036422081c140d50090080c15040b90690b600e410005002c4c0380142c2c003d0140030300c0307403080c0740c2c44410b41c0e2004022280101c0c400720600c0c400300c00180404041302036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 347310908 1250 347309658 347309663
    0x4050c0a031113060e191a0a0216270603020303090d1505130317070e01140d09080306040509060c0a080a06030503070b0a0e03160212120408061603090b04030c 70
    0x14003001c243c0e0200e50855902410480d22084a4020000e051244248000a9021140355909030410200038050a0250460401c0388407607580c5507003000c00c1c0e240103c0100d00c10040d8807a2000012400340c0c04003108014a060300c424000304010705400b0044d40c03e43c0c00041e625401c100f00958107480d100d900300384014400c00ca6041410410103600c81120400c031150b061100b130b2814034030101940b102c0c9401c02d0355162460500030b42004a0010320800102103030a050000001b45d0842802d880e00944240640c080410b01a58020b40350110f1103401c1505c0c164000c90402002c0781040d400801c55602c40d0440d07100050403c8201207044403542e2011b4081c04503140e9030000880032480174001840000c1c0620004003007030034442c41c14807c03110240c2d45801b403904144592004030312018100d040d1950110395140c3d401b2640402c050400740800102c0e440135100103000200d460003c6411846900c1c0341e1048181c84241000950031b481440c00010100d01440c0c00040000740a054404c90090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 347312158 1250 347310908 347310941
    0x90f07020c100912020111030301030309080c2704061104090e010e01020f0706050606070c09020304051b031218090403020a031101020901122307030e160b0a230414040b04050c0a03 79
    0x2040c4c0c7c40801d0950b8000c0c0c00c141c0004100c0442801002404c010448041400b6240d05140700102c6080031030152544801015050011000c01c040c0030450300030001c00081422507aa549613524101d4000340522041c0000b15428071046140100707040c03090300d5290b50f1254000e07103800003039620320380100700c01040c0c0c540c800380500110380460640c0d016034003e000c1e110001a582d083c035081c06880e0400b11604801c0090703500c1c00a43d040d84000c507403602021181017805485850104400e1515024407403401d80040d041000c2006041e800210b01403518003d444001c14000f807504203501788d10032191400c3c081002c800040800c036403541c0c00b0750050303a64214048264120805601d100b00000d481640000f61914002030315070105105500d02c85400c01880500d0fa46008c0318140e25000f00e44070ba00c140a840c01001007420003c0f14041344103e038131030300c02d55030795203900404164029050740303280a00c0c544103124069062512030384d1f006d00b01100c10503040c444150790840107440003011404681 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 347313408 1250 347312158 347312177
    0x15021c18090515030105070e10020a1704030215040e070c03050c01051503010b2202070c031416080a020d02190302061902010e0a0f060515090f07020c1009120201 71
    0x418040400303000d0031226a000c0b601c0e0501400701000c00f0081d0b103005110381d1404c02440021500540d8503050313100d0a032881c4000c8419050140c0c103041c000503000c0d1150b0000c0c1580e04a1440b614010710949108440401c04500c0016541e4114019401650324051904c0702150206d8010304031002a188207140c51485c003040341c44503e09540064a180301061403c18000741a8070302030064410782c420035241c0e880402e82c50b1098042120008a45101a903800540c0d14103100581014038040d5030003080c0c0c100c002c004c10641d6030341d4040d11200e070a030a404031040030a54a50100d03901d036030f540c1c000300b8481701203000341c08006070442045004000008103010000068030b91030b024007150b0070b04252044480141c0700002e4250713800041100083c0d0001c2c003400000494600400d07045c5a08007400054598070a1003618282c90603032041c0380e00107012010080007201c0286d01c144217890a40c01e881407a411002801920704440c7d5604020500941c000c0c8a10100315400c816010700501d81051b25 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 347314658 1250 347313408 347313437
    0xf020714061605030a1b080105030d0c02090105060f0f03190f05060303090108190e03070501110f040b07020f0402030f04020a050f010906110307080a0206070807080c0906030403020f030d0603030915021c 89
    0x1020511400080824911801084140340901111814540348d0405400c0d5100c330f50f0005a64038414000c0901c6250042500c003400b0040d90190381c032145001003c1903903400c0921061901c084031400c007000090810024042c4405980180341c0078450103801142000f14407401034440e010010110000d80080882c007490180c4580100c04485040101655442015051090030f5440c5401c2141506400300a4030351780c0201d00c000c032402c0b01c1c15808266154000b13440054010008020a01c3c0d010740040103001c0102480304809020314030848000b8a080e80d11010b01c000e0500101310f0501088542c1030400c0054001d50303a002c17002d1610401d070303882c248a80d555422250050141c15005074007000812403500d403c4100d20707400c0340c19030034141c40c0c2e854080d480903001e20403554114020760002c000304082500800194040b07050a00c10703aa01c030543c2440782001824180b000b540040d03150341c400640c41080c1100140c0819059000e003280d040e28514507421907400081c903c00304800490806003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 347315908 1250 347314658 347314691
    0xb070f0f030314150108010e0609060d051501030b090f0a11010c110d1406131e030c212a0b060a0e1f06020309030c0103050c0c010f020714061605030a 66
    0x1c0350f010080134130b0076405120f0004214100513009808820445400e010040d81c2e5601000e600c42012141c01c40d07a622503141150400c500400051015a0001c00100800a500074098841e000c880102c5410319000c034400f076502e0b091660085c1c01000109145503095100b01003442a00b4000c0503080510440350010680d804001c480c283c4201c01704036154a072a0809201d030707580000c60b1003004000b1084a0b00c0d110029000c4c00c400ca2100c072440241c2d001010f0081c4264194180c110390301c407403070038800d100d00726048180058040c0003d01304031040d40d041208020007804280c4004055a01071050781c1d132003c4800024068550000300c000c170010381c42c2c103000e0800b44500c1500304003070400c000c11b01c0b4a00c0034001030780200d402e5400a014070030054500088031068100c0920f00070a941d11401c002c10300318440d182c500365195080c081c0c04040799030030380c00030b20516224030052801041f410540c59100c020580d100b51410141d039138180d10441c4500c0195401112030b1f0000074824844409000713 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 347317158 1250 347315908 347315911
    0x9151608070602250b130c150c03031b080406090201050912101109030a0605071e0507230714010e0909060906010504020a050901030213050904030c0c0b070f0f030314 73
    0x90384550002060701302c100d08200350f01d907960b090841198081ca4103a41e0721a40e058000c0503c00150440c6074140107001d102031008005011144008504008901c4001c04980000000f540420b007049c002d81c0d1908001a1042e03103845280d500d50a150b103850b500c8034013804040e1002e9040000510000308070382da42072001c80c840502c120080c45000000d0500d4005d5429100c042090044148440003040d1030103e01d8040f09544003c0c000b55903551000d0039644c0ba0000840302450024400d80201341640000040c68294000c040b00c9070b2131680c0d6803100314060918000c3d160544c1100b042003110300c0e420b030703080b2207100c805041c542e040e140704001094081d0030440d40490558819001c0c050442030600c8154098081502d0662400c0003804010b8000d10402c40414109540060948520381110074144043e0078011b052040901b4181801401184010010742d40c402c11000d00240c06c42d42c030ba08882904d61b00299138801c0386500c0e11031015800c440582a81131544075411291021061007546 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 347318408 1250 347317158 347317163
    0x105010b031905150402070f08040f030611030c09060f042c0702010e031812030304030f020d020c01080105042a020706030e03043b070206010311060915160807 70
    0x1922458140c00201d601c0301c481c51502e0350503141c10203014103111084021198418240e81c05a52440f0901d0003458400308114064018200483d0108081183e000700d6000c40c1c1c05503c00388050001465a04000c1c841628041681c401c03c2064980e6810550042d1545548e131640f200c0c2450380c0c03aa440d50100c1d0341030700c6c0a51011a00001964604a017900e412742154a40c4001c03c00c8110081034260f4910940940c241c03500c1d0b60104070502c1c2c5e0741d2600c0c0c582d80480c408090701d441c1e0800d4500a0001ca8481c001c003805802215541f40200e44002403203030781140140d440c181d1a910305001c0c80000d1105118021221424091400f882844031a0280030842e4603030080223000c2c90150000d04544450651410513002080200301c01d400c0d15040c50120000c2c20f1130300842c40316003040c0ca509152260658480c1c00707074000820158540104480d81220b009840000302002c807082007000714440c61500c0c0ea4040120050f0480e810f81c0140640280c41013180c05c410042525122442c80d80c01c629000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 347319658 1250 347318408 347318429
    0xe1e070e101208040510032904060512061b0a0801060f03180c030c0504060b030a0f0207020a030317010f0e0a240305031b01090b0c2203050c0411040b0901110a05010501 74
    0x1003141c0c6c2003480d0341c1a054801c0d460104101d8940c0d041c4040c4990a00300180c4039641c00c5c400c111201c0c2d41e076030b1080340100b6004081e080c5074101c858005c0e40b924800c8400352900c2c6180443c0a10b15a0094211744551050b035403490a00d80c01d04000b51500007101481d40c3c02c1694a520f80c580c00004440c442d00c00601503101240414a50300e00507640745495081180560300b0203608100315201d2005494201581d68804940043c40d100441e0090240348800303503000c07001030000810305400203009075403c401406e03c608282c0e01e80e4440d0004080030700c1001401e40c0315100048030f850700d990108a1141c6d13005001c1c40312941c2035004003220800c0782c00c103803415040040d00c82c210a80020490a0940e02c8000a01c9400c12a842e84000d170302004262442c00b810002d407400d092210607424070044000100c80d2031180340c0340e007000742c0c6e510130566046003d40d00e442c140c28003201100d0103590841d002000007e140442c0318004480403650f80c500740030300c1e04c02c45c8202c00020f0000c1c004ea90107020760104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 347320908 1250 347319658 347319667
    0xa02031b0412050105060103020c15060f28060201020a0c200402030a021309060f03120c0f060b1201060e06190b03090d1706010c1e12030e1e070e101208 67
    0xf040303801c6900280481d414113104220303861000a02090349041300341650f005041135515580812440390aa50325180d00c20104060352145103455400c1d40b022003007060003040b40a481e504143d08030b100b44041c800101d0b10754066030000424142210080620740d8040200080780301020905030f030016103042480c075030045120490b0206421155004040380d507004c0c04041d181c03600c1c49012060343d0002512001c0440001c0040502031505c4d010782940c820031481c82c140841c1030200c000c00340c0c400c8580c4900451010036491680500420041e1a40030394240e000c0d4031b07100d00704002d141540e00d24041c040c442190000e024400c443c040c602c9908a240034002c104d6500ca8000d11428118003214050030341c1006100480c1da1004551090b607900c030300d6043c00702c08010380c2c030f10b54841d00703c0004240c0404164008a80d0703506800548003c08076404481100f401016480b0402c0305406030080c281c1d001c11420898a8101180d0a41003c0d141d4010081140c884510b4155010a01400d44102d00c0004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 347322158 1250 347320908 347320913
    0x30603010b15070b1b07080301050a06030524030a060216051908030703020306182a0a0804080901030e0708030901090605090310090c080109030e030d05030601080a02031b0412 77
    0x3400c60340c035408860110202603140702c00982c5020b43c400c0038003400c4030302d40002c03c070b40c5407a100540242a558101e0351210500e24204039981c0c1f0902030140a1507061000081590080c0a02401040901030035114403189494200c94255911407155041c880d41841030702141c4030340f0050a480d0b001e200081820061410100c2c1381001e4501b0f00e03014084a00340b000d02203455407081c0e070307001035581c903016a0300d45880000400028001803042d40508020051040000a40040642100b00110308080300c11641e080031010b030181c030040f00c0108101d100002c0c00a00705600401180905040020782a2841d031041c3d850400c040e004003c056100141101c00e66812a009030300505c1545406450f00f040d00020940710f200100c80c40300207e40f144440d00c1005880304510f8050020360000300500c00c0c180c200280403d45e20020140203002e0144490103182c03003a8100d0307200d007806840e611500e0b1070303000b1150020b6200a01e40c5908500d8190701001c68520307000100014600d450300c500d0315400e01e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 347323408 1250 347322158 347322161
    0xf030e1527010911010503070503070f0203040e070509010806030d09060e132315100c051c020a020f04090c0512070f0e070201050a140115051e070b070806010e040e012003060301 78
    0x7040820b0612001f80100046654850f085070740c807615518254000d101c1400044e45140120f401c0300e03019010802c00c11007890b600501074403054600340d0b9283d18075283d1500b03040c0c660141e0300010700042d940c942c0130b12005025603008401120041c00d0f8409410889003084200c0d09500e00300030394600100445000101004502c0f500303c1c506042c00701d001d050100c00560b03160b0140000400380410039140105008044c42040801c0c061000104000806070324025103400d8904812840f40200c17904004050a0511840009660011880e0301c0d00d801c020411400340380d000001c1000d4850b030750010528400d0101540b0003814540581034981c10102406825190010a0702003140c1c507000c0301e10301500740c64912a044030840c01409005042807a02202c280c41000c0c024091110440060840c002405e001007100c980100000101929400340842d1202402e54041d400102c008500c0d541c10b1802da40120200680a000000c082d2280812481210f8419a04801c2c410004c8200185810207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 347324658 1250 347323408 347323433
    0x705031b1506091611060f19140a020702030307060603050606010e1c060c170c0d0e0f07060e0f04050a050a0f18080304030219050106060f030e15270109 67
    0x1101c4822090b2900102298030381a0003414003180b4403100c800c01070070a01036140c0c4c402001e0342006170f505503c2c080c403050f482c450b03094441194800071000c21a0f2500424812700000b5456884580450b45910203080080c2d000420241d9040c0010010f241c00907805102d60001180704401400c0c841c130f40140050401841100072074018144090321000304d03601c040420401540c441e90028042c0c180040803a5410303000a00d10034a4040c00c0180329040c40d00c900503040621510100f44062102d8010a87e00e07104182c0070b41100354440c0350709021184c09114030314107a03071002d4041020305203003800103816507006803900e07400155071740b052000c41d101a0003504200611110140702d09140070510030f030417007281180a4944480031002c40d08145c802d0042c0c46950071444030041801031b050910030700030002c40c481c80c4089000c160325420102e0007405001e0003d5140e1001c0e00821415500f503003a17202e00205030340c2c1c60310380c2c88002d00390300142c02c00c40b8541c2c0410200001006240c51900c05c0342000c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 347325908 1250 347324658 347324683
    0x6080f070c11010815130b121507080604092307050306010602190512030c0d0b0a0f090e010b04051603050109021305221e0b010e031c050705031b 64
    0x11200804020070b00b05042e0300d0842001386450140c40d5a900c1c8000c186641508800d40d04c84091449448842e070550440656420105c80410303e201501c440d05641364054000c281112001e0310010795000d00074030744207920140c098004540c0e002c0729034a03100c1d04054040000520b118405062072036003802c11a0318003a01058004019650500c3d038080c0d43e07031414600c12428504414103020800005002250403801c020301070984030304100303a084040d03801c04007004051510344180058540b605940f2041140c0306caa40c10880182412031000c0030f07024009094129641315452841d4640325442030303038814071301010002c6d032251385030301c00a06480042c2d000080300c900503c1064040c0b81c41308669412101c0c00c0f11000d1031030041060030140e0f440c6000414508615002d502e11088522100c1070700c142c1311640040020380201001035601e001e4400040e605540040c6000080b01101201014040c003141040d0341007000941d40c941c5594060720b180204050010030016104404000400c038281c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 347327158 1250 347325908 347325917
    0x20d0606021e03430213090f0b0a14010f050109080102090604260d0504030209011d0403111e07062a03050a140d0903021018111906080f07 61
    0x111410202070392401080c00c1441d003074040346500c900780856600440510134845413101c0e840001c0002260b003092044030300781c0c003681100483d2955000284030300c400031940b0007200f80c00c40c801502c800840c003200801c8030140c159204445005181c010781d00c00d000b04500701c5010740032403d0000040600c412907001943c00d07801801003103c207a81c3d640c1540d050b6810b00900300c180c449a07007480014034010070880245806072080d0014070b56800340c01401130780d000f0307903a100d031b2a40d950122081e96058940e40c07660250340c40000c540043c0c42040c004550245000444840d0b100505550700001462442018190701103482003210640001412030515112005208001d8030b9040903114401000401820070000103030340d19016000301c40301803a080300c03080c505483c1c4025101210040c04003010507000f620614101c4c00001c4118014070500048111101c03105447c1035890f800198501090990701088800c0c0080c940308500c58030070000c200942e035124030b034109070b4900203440d40d01800402c00c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 347328408 1250 347327158 347327203
    0x70207033c0b0406180201020a080f0f04090902040b060301030308130c210b06090606031f09060305010c03050109020a0c0f0203010e01111b0c01050301060f120c1205060604030b0103020121020d060602 88
    0x144c0c1c011800b927079503503003203454141e17240d0155081c0c07a0182b003610b1000c0c04074140410082200c2d00160310851105100b910104810548842080041e00003444002c00013001000000d8400e07079088007070404580708880d40341e616500c42500d5801c001c12840d0700080c15800c44500f0046c004842c090507080034003556114058100340b1f0100b90f8502c0b00074000030b07020031011300071030402e18002027010041034441d9007002600e440b0318011b4040d0240d150800002401c003000814410890310880d1030710399a80e110180307200d4a5950f132895600c4095401c1e40d05540c0d843d4007500048080c0500b50702d441207480391030303640c0229440c0c01700c4001100b0240c89550340811414480c0e40d8000e02200d064030458140789150200c01c03042260080e0814079030208183c244400b45880c01d402c58214045074000701d030306022079a11842884214040c41c840900108607807001000554015442503c650140400640f1801c91410718803060f03038000c40328900703025524801088155414444c5188216080c4040d5018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 347329658 1250 347328408 347328413
    0x2011806020a021210050c04030308160e120c060d09022d010327050607020d0305040c050f0310150f05010c0507090509070503070815070207033c0b040618 68
    0xc034042d510380280900042c00050100c0c0c0010440b40700c5110207207a06018619240340040029000b0784400c0b03010509080c080341e05000e103503802d4155621140c1c2d0328840e941144003000140120010232030b04500820664440d80d40f121002404501000040407410302c00301c1c4180f258a140400b45094843c80143c0354030341503000d80c880302d01d0741c600c2468003007814442170800307110000f40e0580d41c41c07450008030210010881c010900502c1022241c0070b89540840f500025001e23520704842c01085072512141c18031661600201c0c1d1200031001400f2034910101d11040380080b100d488145403618182c4e00010456484072a5a0501414080c6800000300c200c41d0389a5074bc5400358000c2031601038a40d000500f5180c020003004000303003401800c80d1592a582d4103402d0321a126440c10141c1900d12600007405c26000040c400101d82e0b000c0d17045c070116554408060111440c1e8540c1c209195074560f902410039802e00440c48080b40070b070404400c4c3c0d050500e0b02034110350080421540103000100d80c1c001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 347330908 1250 347329658 347329663
    0x706050408100b0f091e01080c01080f0c0c0d090e010b120a050603030c01021201030b090705010c03050a0207090c020309030c09102607030308010f0e011a0c0a0503160201180602 78
    0xc06000303800b00400c0f0080c00340b0004801066801070242c001e03d0010401440009540d04c500d100015120740019990f00d0f4a140340d12428540c4401e800f107465000030400c0203000c503100c56405280c5c0340c02d4038181940710b209035003018050283c4000041c0b1140050002c4a10306440030300604603281c0f8186417060459820320b42c2d41c0024041d001007a41c1c1c9000a19035182801243c95481a84000b1036450b0003010352102d1100c400e0100b40c619078003210015069240015050003036407016100d80312145896a421542503101f502094214010200d0004220b5194012000c071071146802860302c41d0801018589041e03e40301c0e50301d01c03a4044900340042101d11001c0f0009456401d40302d604811242c1600280b41c0f0000d45024500d03100b108000414154880c88040c1601d12080122812694441450054190a004260b8101c02910750400341c59201c8e00100009141c1c4d1068800c20407042c0c0354903041d40c000c2850044070000000a02c0c0866a1040d580e150401ca241000241203081407c004e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 347332158 1250 347330908 347330923
    0x906090b010912050f0d200606011e030603020d080a020d0c03120e0c0a03140d0c030e120a0b010b180406140d031e2a12140d1d0706050408 61
    0x120b1034443c50070fa49060141c01d0044012084a590441c0c0300c08186040040100b0fa4465110302100c112050302041508041030041c00b03024140c1d00c175191418402509800121902080c1c1c041c1a030f600c0c8000300503180c10242c0b016070b5005010080c0c41d90840d590280c07c0180d0f10510784104500c00003000300107038004a41030200b0030300d400c2c0001c0c40d020751408246401c595402081e4003045160300001000411030101110460400598200c844820720070368003400c02c81c00c001c0118410b0b15568a9605098601d0315640c400c100466408c8102c6d40c8480500a6003070300034140085c400150000541d01c00d214217185c16805403402c1191a24041c40f20154514038852107110b0903090741c0c0107003898482ca00300040c80607a03000f8501c414201c9607000d0310340041ca9140c4148061076250b00707002c0c9100c41007034000c00754010300300000d001c001c000b045500030340720032050440341418048860041001e100c1c0803460141080c182da112a510102e00707292180700da0041e41008020001401610400309484 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 347333408 1250 347332158 347332169
    0xa080315031c1d1201091205161e0f030305040b07090e0406180c0609050301051008210c0307050c030f01050907060302090105040302101d040209060a0c0f0605100906090b0109 77
    0x340c8404440c0103025550341242d03010f143d014010038814140e120301903000c410050f10881007560710325501e400a0b0f54600074030010f441040c4c0c00300c0c0000085070f4211000000c040b078504138510190281e503075010b05180500401e400003903486080004100e01003048580101c0b030390230b20401042c1b40142840100000410087c5841d843c1c800c40701d030060040b90560107003a403100001c484251680d20007003800d01280300e2540b182d800c0c0310114040e076010721140c105803a9a4400b4107184040410050081c0c10f00c1c00c80218940020450010850707401d00c05015007a105801503c42908c0c0b51007018a0308052039502d1802e80d1601c028020940d0001a210045869600300540c40b0b410110040e10a4000d980c03002c1c4d0003126108156100d5503101c2e2081c6503588052980c01c2441c0f141c0018081280209214150002020481808480e0240305814101031042d80c107189007411380d540d80c6041d11400da43c10f4040585050782442140d4460003001c2c041c0c940c59504005041d50f80e00024281e04840c4903d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 347334658 1250 347333408 347333417
    0x1060503010b0a120b09070f030605011b1407170703060e0609151e100512280f080f071406060f0f1801080706110303090705040e0f0a080315031c 64
    0xd8208004c19904030a80c8418010701d10780092515000180070711341e180b00c04c03000003850000040307095800340b80060350b08080c261880c00ca03a21165203040c0800d901c0c92030b85c1c8503032141c0c010000340602c808015411101c940c401074242140303146454029540309414002851b000f2400308a0300900016011882800c1170541981d1600c5040c20040ca403182040ba0320a840a154100002640346a06020172682d05445013018031220b051216103941015601c070400c1c2c0c001e18503a4002e00607400d41c0440c0d180c040d0326043d400300144d03519504207030f1100301c00400c168404100c000a100c0c0807440007032050a900098032b070354541540002c03a021017190486118880344034400826442e105205002415141101103143d6199514590b031080c60b13104040000c6c4030300300303a5459084080185e80c0074006a0b002070040702d04dc48d0410014003c40210300c401c1c0d00c0b030b51110383d95481c070400c24410240d000c0c62103c1c0d901d04000140604290b40110510700960180a02550034611030b9020171080401c2d290 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 347335908 1250 347334658 347334677
    0x3150c0d0c0c1b050a0803030f01060806030115080f0c12100207030309021e030f0109080405360403080a02040e06040902060c010614130b0a03260409090b01060503010b0a 75
    0x1c081d50007038400000500398003e00c0f951402102000114142a41e00444040011543d1070304019031300e220031500c004411150300700400100b40905203031a0040c0006001003048414000c0e0700d05600c206a005072600e5114030100703201400244107100c14400280d031084500880440d003070b540c41c0e0348030f031170315101507400100d640915220340e01c150507070750b03006200800038016206003160048071640514800e003c5da08080c0d10705801403203001c1e621a0712020883c2004d2802041045611520041c02c01010f40150549000e10300304500e803c508420041c0c7c084241032504004109010041580610601c1040180700d0541d00b1007081d41c0c0310798202e50103d9088614408616603000d6540d07900726035070038104003042031030501940c0301385444140e07805507001540c0c0030842d00b40c4182c3c1040d50b8118209003010b00204141450034a08608007001021709080a10118a03250740b082d0711030903425a65603004000c0042c0c50001c60b004000c0380c41c01c1800c65060040741c0328544110380441061041890 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 347337158 1250 347335908 347335931
    0xc0b09100e03010f02120402032b0e0604081f06050303070f1b080106090e060604090f02090c1903020406030b01030615031503080a200d0507020103023603150c0d 71
    0x401c818103818001400703540340c00042501b611003a2050b0b80880c4640600701c60b080880300224900e0444000f0b0000512440c04081f00c10380d181281041455040b8400700320100c0d001d0420003410050802e401c070b10091001e1040ca1100880b40d00350040703807080d001040040c011a2006910303d21150b0010008040d02c0407030007801003180e03119449100b0650034800c001403810344581c40b03c0c24218520059501daa83c582003000f040711001c1000401000b003a021240240c2082c826490303205040800d07803440c045003d49200301d41006e1061302d400103034000505001c101d616001f0207002c410207003818054107082407904007134200400e07294008c1596882c24000c0f2520320803d80e500654001402079603c01d104d0100504409581d2500c1d4240c4d007902d84410061740c2c002580b0f003c1c520007960759600349807969004501a5210351000e09040880840c5000e60a5103683c141c1076448000801c0c0f6154442e9005050a007403404990005d2030300c0f031070100002202402c00701c0d4500c040700c1600185245084 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 347338408 1250 347337158 347337161
    0x8160b0a0e030709061e0b0d050702030706050405060106090e1005060309030d020706061d090d03020a1e0e01031a030a020f0d0c090f0b0603040809010815060a0c0c0b09100e0301 78
    0x640440342c0c5071143d140c00141c80210382e4000410740d5000904000c031900130b0503c6140340b000c60312a810380303050200045020025140c0c80260000c0721841a01c0c40c0076425200c14081e1041500d003640c040d0880c80040040f50303045040c1c0d000403d0074164124041c83e20005843c44405103101e180e000320030010000e41c443c0c02c18001c40e40a5040e6050841d2240000d0a10710000c0070305004559a0440c80d0482440d140504401c40e8860440c0200800b0036240e0301d80100c0194110b0310f0134005000c001d00004400b40214080c001d00e0020903903032210302980c81c00005043d51070300500121410f000c05584910740d1404201e1800d46030b01a03070407040300c001d404041000d101c40d03814049e2606203041c07404640d6007140d800c2651008031481c41807040c03000c00d10402045100075500100041400c02c49105154000c80711143e00c042d04601100d1a24a200045902c0b0b030311146070280010a00c1070040104108605201e019101400c000b40c00c0900060100b03101d40f8000212405005002d40b0700c60351682c09 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 347339658 1250 347338408 347338427
    0x9040b040215040b03060a0603110301122f09070521060d05010606021b040501060c02270a0f060f0b04060c051015230603060409050a0b0408030103020a08160b0a 71
    0x203241d0710b5030ba15a0359120140498005884907841380302154000218188070f8090b4140303201c9040052451a4600201e45080300c90942044035585403d582200018001e22101c06a01000f90119000341c00e40c41e0810a075500018003180510005015a0036900d9100c03090184c1c403085040e0346c3d581c646aa00000d0340d0b03140c0700d080040103582014400300e03c0c103070b0100b1401c03505160f0a0609203000751510400c010b8a009001c0c040000b0742003050b003070251821402c00c10070028211800e0000496a1440301c1000310100c40710705260751503890030303040c110702407044030300030801890403d05171424041e0b075103903503c00c40c81600d0800c442c01c8a00800e02c0400c0c44445ea001551200070005400da80d11034054850031303172003114080c05804860600c40401104015007140f4001d103400c0c80c50395400c0402c001881484026142c5206030401500000c4000d1225405140940c1e40c071030310780d8510700c10032222542580056170725412802403040804d0051480409903001003407610b0f1030b4944050b00320b0b0349195 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 347340908 1250 347339658 347339689
    0x7080c0303070215010e040b0a0b1207030503370302070c12030e0103061508011e09050a020405120703151a06030a050f180c040c03060f0305032709040b0402 69
    0x10000500400070f8000440c10302d4500e0b0058886040da9841001070440c10040760040c0c00071803224001180051603521454010b031000340024241e03964481028601995500216441d40c000110141c0c4400c20850f210240c054280003000520000d25100030902600000d120a154002c1649401c001c0305440c0d00c07010704a40104aa903d41e11401d0003070100d0f48120107a4046864a1400b04090219900c0340c1404155038440c103100c0e918140c15a00b1080c80d060300d815042d8208000420100203e000d014094503100754050f0312907007080104040741800184285c031a5000c0e46e01080010061a11650142020100011700150348608140100e81301e95050b50300200000c100010141326501c018042c000c005d84540840d41e070400806404080000090107603800b00615945510300394010800d4444589408200582c3d203a895207052400ca0304129104d400120b50b441c1c650b40d60705c0002e2901c003002100c1401440050011880b04503025001030207038405a00040c1c01d54441c024541d41d00340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 347342158 1250 347340908 347340913
    0x20d020a0b0c100c080106020c12071505041806060c150204051807030b01030608120f0c01020406050c120f04140a151d090603120a0c120e040c030e030f07080c 70
    0x6240507855150f0a1140200300078901d0045503a07020792182c4039403070585200da0020003002e4000d008000e10011800041c01292048090120750f80c2034030f2500801d0340c007140c1c0301d00392910304200d41c0c19041d1200c2c540d844801d03883d10a003000030552112140f00d456820420031400d80e9003009846020748a16007000c3e4001d00c05000c8909012000750041d4410b4500d85e03404c01039407040304011415100580300351009980050660704041d05441d0040c460011a410020300e030512061219007640c021b9802000410743c08150040000703024090014192100d02c20a89003082000414406024a014041c820303c0d07280e40d4600d140d190001a00040c10704510020600e0103240d20040404544210741c0c2c038440c030120043e05060820701c810300c1c02444000c0c041c05c12822040c440144607000316907280100020444a40e011503c07880640d9500481d655800034840e900c007080c4800d0380d64030a541c03400c151401003a00038840c17011094620f500c4000c10342d80c0e52111030b41064501d6020340c80c3d03aa4050b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 347343408 1250 347342158 347342167
    0x70b010e1015082514090607050a03020624100302090301090b10090c030204050d0b071404090218190b0d060317070314030910150b1206130b0607020d020a0b 69
    0x10364201e070b0940e104032a00c00c407500c4078a0341d034811580301c040108002c13004180f80719200101007403104003a1601150180103241015075030b40350103280c134001450a4002d6002882405604059114810030382c0303e9a045262440518001094103d6440c615060806074042100c00f842e83d429000012415001280d0183d1810940700b0300350303222600c1c464039101390302c3c05040019030741c0039000b501d0840d5002400703102a14501d403181c2303400200003001101040300d4144610b800900f140058400384c0b400032401a01d0781143e10020400f21150404648160003842c074503880c1a440c1e107408000c1e6100c204000e9110a80740681c10003501300f1790401485010340301c0c2d50803503021608001d001c1c840c7c001c0c2c4d14400d116040300440c0100d0b00c429181a0f000360030601d0881418123003034101b4124084030072142c1c24600d5984004491a41144803a501ca80064400f8800702d1f24000300142940c0e060100100a00801540010981e1003000c00003402101d40106034015982e0303284021004120061016955 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 347344658 1250 347343408 347343449
    0x80f070614010501030e010608070902090a0518100f0510030e1903050c01060b03070c0602070c0909060c020c01050a09090b12012a0503060607141e070609050303070b010e10 76
    0x610401d010f000c2c0043d180213004000c00300140030300000c0303400c0c0c1d10190040d5410f000b64100654802151070703401a2145c04005496198102c1c03041e503501d00c03941d00054904007041c11449880b141e9008074100800120180120354502c1010801c01d0340754280010010b102c40d11060804484400e090480d86502c8140c500349078000c4020161220300c0c2c4000c100785621a074007060f4034002960307880300044c50480c0c0b07a8005a0540c3c010250640505215220f090f580d0543d64151241024100c80403600d42410740d0000b501000000034400090914034140724948500524540e07292180c1440c56441d041c0119090721001c0200450316140d030028840c402c3c40001608200e2403003402d0014540c40704650017a00d504c241705480c040d5200900c4c2514008041d02c0340c00004103c0882a10240216100d01141d01103005407036001c0040100a04070003031421001802083d03040d4003983c000e4000700900700029102178030090540c0c555a00f421705546031a515221040030f60b401084061a00380c420700340c07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 347345908 1250 347344658 347344691
    0xc0c1c02070815070f0f030b1309060c02120d0207020a03021002010c1b0f0b0a0b0d06050a0606050c060103060e0f030c030d0b040b0a06030b0d05031b06061804080f0706 74
    0x2070b40e00034421101000340000500c1c0c1d1592003100c0b040005074500c001d90420b548203914294034a0802d2030045404a00400080e418120280070756036002d544038000d1081050b07a00072110031b0342c82c600240060701155680b00c0070b00e100307800e4007500156000801e03d046585090380d02000e035402800c0480e01100c120800790090411000600102c4c2c22841c4120700801002ca200b401c581d0b21001c1c5560031410340d942e000c15084058541c00000b9280c0e0b000031082c1e1503205d0a0030f40b803401440049441e0410742d95800c100c1c1c11980241d01005420025260600c000140550449501135000204074141741585401c00b924503150140d240400503641d036160b000000a000511602c80003000100d072032004100031540282d0300d464012140741c0c010490f0900980c4031040c03122001d032000c40c84050a40c1d03581d041d80d001280412000b50000d120b003211180400c107080c0d0111040e601003030503601d0420410710320140108004d05400d80019080c2e40444404107640c0060b510000c140107200c4101100c20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 347347158 1250 347345908 347345923
    0x2070803150a08071a1b070609050f010e0f030307021302030a0501050907021e010b03150901060b03091b150a0e030d021b0d080909091e01140c0c1c02 66
    0x1000c14224200706200d62406084a1003103403081e20007003448034602411034440007182d090405102c40d00380441c070001c0501808030341c00221030601506069003011009040100c0c5508500d015182107000061039036041400400205021104140e00480d401c0c00203140d4070584c1340003074016001c0d029461682e502a0003071030043c0400c007001e00c0160380307a805101405d10300310b5100005921a03850503428a00124071a13208110940001c1a44a80403000c80d18010143c0003a030b1541c2c02e0700e030400c13100030401c0c1300380070140101c020b81c64a1400d104609550b141a040f1200160125001c0611040e40d10150300103041c50411070070342c3c2c5925070100003601c503c000314100c034000d00965040320040d51011464034049400b00480a030b241e10b003072080c00355248400740c0880742c0800c20803181e101a961990703000e100d82100b10007442041500d481c00c0300b2032a5441600c4c0116070518a01c05048030780081b2083e030221002d000e02e525520003c18240c42c0c2801c00c0668100e034000798016001d020703400301d6500c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 347348408 1250 347347158 347347171
    0x8120411030d050d0504020109080d09090b090403050403150b0a12060c08060a3602030108190b130204202505070506070c030c090207110303030f0c03090a0602070803 73
    0x1a090003011092580300c0e10800d01e2100003030001c104450742003241d030b80b00d181c0250041c50003240e5282c40b001d881c7c2c83c00240f140b106010501c00c05041142d260340707010740c1504040640e1a02018100780d0703030240c01070040340001000d1091240c031504000c1c4040e0700081814600520105030180e850b100040191480c14056a10504000d4100101c134001c032180c80c002c41000e07183c1d06462b032800c3c0b050800180902c7c01241001c206416140f030712240d4014013141000a26070042c2d880d403608184510381403120306951200ea601c035000344040350a40610709ea0007058020400340030311040c800280104881c80b160300707c0c04802c1c031038002c1d210805000303001440019071003a61410b8008170042140750762840e00a0103603101c02340a000c18185030001d044c101d803140c403451010766101d82d9184640ca0160701300d807841e00c2d80400d201007400192000c9500d1100150091440c50510058035940084020280258100c1c000040381111404200c40d000306c6401c0380c0115207031003482c60204110750068448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 347349658 1250 347348408 347348423
    0x60f04231b0d06152d09080303090631080a0c0f05012009030304090e0f06070807080a0504051b0102030d090b01050f04060b04090c02070906032603100918081204 71
    0x15003243e4068004514a1051410f0050398005107400103107202d41e030b01740620200320182c0070016171003400700080c601410240f00940081d250101040c984032600d182000c054040f264110250900303074008404219402010719681c03a118900182d4a5001142004080d00004100c00d005d120040d4061507981009110100d812041c03d17000340070358018090141da142c1c008000c1002034000c1341d8882a080303070390300e41036810819840c45050309059044802d07001040e9807000b0080e1040d84104030307692250007100100a02d041648500e5907954061440d01309001c6c055510f8200f6070300800641d985050500f106119426480c40e0144213040c0c02c3c8903c0c0d0107403d100112603640d01c0c280c003402098075150301c115800d02c0e28104001016081d4005c0400a41c0500c0001003841d401c035000c4c1002540c050207408100c9241000c1d55458880c0c00f03410303006489420703c14401050149100d600889034040004190f249680030000c1b55113036088001440d0a2000a0f00e1f4051041c400a21b8030440c081e511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 347350908 1250 347349658 347349689
    0xe0a0c091a041514180c030103060e030a050307030c0903050706020f2107150209031209090f060306060d0203100c20031e1b010e0105060f04231b0d06 66
    0x2404180c400c10044a0005107502c07005000e4281541c0841001c0343d8001c09452602000040707100e1819406d840b0b0404c00d03440000180148201e5000b03080c080c20b0b9000040d860005190401003840c04040d00c1e5904160f1290040d0228901c203c86020286811800340e030760343d40d0341d010040c1d0785041d2851002250b0080c0c0b8040d0003204070346244140010002c0102920301245690764540640e075555800343c1c81e84e424411031107152410411940701e8124421055940c0d20100100080104000c11080d02c01c91140c0800c521928080b80e2240c1115054604000e284800d20000381044900d00d001c0d05190319024660700490340c007443c0c0c041c08000b90002014220800400141c50344911418400c90114011074501040303001401008403100d14202d0604118180110780c1c2034468075a2074803010703074503182804058580044202c2c1800341c1102c08000d922044843c02c1500c55503804016205035500b030015040c100900c2100c00c900a40b0306505540c0c641d0301300210001c09d260f0180e002c00c040e0050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 347352158 1250 347350908 347350961
    0x1020115050607080c12070501060609120f0803072601030c0b04030809060a1103181c05150a180b0f0a061212025b0e0a0c09 55
    0x3000c2600303541c80034001a15181072619460b00c641d0245900c00400c1c45502010740310b2100740300203000003610136000860110b142c40c00050405609401110758564003030f00420000d40049003c1d0603042e4000b00b031a803030b030ba070b01d91090769420110b0b80c9501c0c103098501074050801240140040c143d0340310300c01058101e40c44005418031400782e8080145441030810640b002483c000e006040c0f0a4a1032070500101308640f0002400d5030011090b044410081c0040400316103170010100c410b84070300d40724a003c070781c0298a42030b40e11018501c406a0f1464810301098403080c06822944220410740b5141c24292103a18240340c488204684a9506d4041240801c4a28255000380340403641c02442c41c290a0041347c441e01d50301105517041130254451101c51480b5140280995101d41d103140f500005075180420500e4076404c1a586030071020060301107510003840c07070300c408800445480080042e0b2081c0d6500c40600d410303038911010305011000d81c4000f82c1520345401501c0c6c22808998030241c0c202800307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 347353408 1250 347352158 347352191
    0xd08190c02011b0206040306060608071e1b0f02120d030b0109120308091005011203030e030702031e0a0213020d0e0a0c060c0303020d090f0b010b1e0f0d0f0b010201 72
    0x9103000707000544807055801da03503089000148001d030008028a02e826034036603030f41c0200d40740b551102c8081811201000311070f07500100400c150700c2c1101031000c5d008202d660000c01c0a80344084821800212140c80c80c1071050202c03600780c6560340a00310f030584030740741c1007059514440100e000c00081d051040d6110325500c5103c0000444a0880c00300010080030387c7e050340c40040081c16141da40c03041500c1d5004201d224003e860003880744558905003e4140d00b001410703524003202030a583d5004008840041e2400111804074003800c09070000b01d01c01010507142440904078001e5031029220402d003100c828503a0060245030b1540d1070401401d0f80d400300941e1104800c0c0381c050001d4080f20b8042100c507014580364441a4441d00c0c00614100492000604079521400143c07424843d00c03030b03c44200041c00c0e54803401341c141c0090150400003040107052409043c0307164a41b68400c0495a030080001c0c58040e00c840e81c04108051082846280b10500105400c205180c010760800103001c001c048003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 347354658 1250 347353408 347353427
    0x319031103010b0708090a030606050f09010b0f03090a0c0e010608150102100c0302221706130206072d0b0112150209031e1f020a050702010c110d0819 66
    0x4000385045a203441c00003c07081d0810402614000410046810150b8481d1148805184942000680c1c1404c040034450041280185140261584c0005000425502054810000814485c583d895a5500000d4180312078482c004006050f1418003007103200700703040414141c40d05d90313403051f0903a60303042c40520351600001c52041c090b800401a1110402c0c01d40c000a46080c0e40c0e0402601d411200701148288072150541030844102c803170018000c103041280380070500c02c8001c00400080c1441d5034513124420003c0b00080c0301d00400510407040000f030410310b0a151852003180007521400d02d6400300701c0c001d00c120403200e034000c5000101e0520175101e0012000340e08040000e003002c00320340506000b0340c4401d8000c0d41c07611030301510039a80d528003c5a01d1518407071a005c1d040d000402141c81140f030402c1214040c0440c010311200303a240798068151350b0b0701e81e02403800001000490030010b06060442803015001a0810114000c1c043c804004255815140242ca07041489200084800210307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 347355908 1250 347354658 347354681
    0x50c040c05071e06060b0d02070204050f100e13080301120302010b03030a050a03050402030a06050403050703080105010306031218051f0215010e04140f031305040b030726030f0408031903 82
    0xd10342e2291252902c84040a0b05a10805000400581b1083e800131a034115110711107060750000ba0950440c10180541c40e0800340a107240420344c24203154104084583e4014008903101800001d085544058001044950444200b980d6035071030340b050200380044440194095030070001c8030301e01410000120b60806400f42e849609100c1003030740c114049d02c0080c0090b80c3c03610032110000042101031240030300851198031116a15607030b9243c040c004000582c040307410715203401000c01c01300d01d40d540700240501d1140303008096525441080e0b6408641a00101d800041c6440c09502040c0060b03058001c03015241c00700c0f221380c000c400c50003480c2d2009000d96154007040c140800c0c00240c43c16030b100e007040300410a403000285942c801c80d1a41d0022180c00d004400c55407020030442c01d0501c2440540b00c02a405010f1990420407800540060030600d4111426542c0c42081004d0092041d1a050b4101c9203026607101c0d034503601c2a950f90480d4840012032400200c10601070781c0a846a0b81c400403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 347357158 1250 347355908 347355923
    0x8060120070510020a02040f0b0a0905040803131e140709060f05041808120f0603010209010c030806030c03071805010806070c0303020a051b0601230a051509030a050c040c0507 77
    0x141042c0500007030341190b0101100b5840780395100001130740d4500841001945042d40022084001d0040000d803441c9035108881681c5000140404580064212a0f100c8280e0003407440c200f44501c0c00a01d08924a075081054540004148041150305026040b4000746c42044845003038685c103180c1d044581500c187c01c0290450708081110b81002d07003101002105000c200780d402003403034440c0c0d001c039030110b0b2803072001a94002c01c1085c18100c081c1c01c6500010183c000b14105803c84001031302070231024002506000f004030026241c3da4080084150002000d4151160196a090090320405034903169010315410b20001017016074001039000e20800d000e565801c110210358500380c0c000c1d8410b21401e010003904228801440e94103000e4a145888034000508071503262030f6800070180c0c070280d0074440310006915500b045076500c076284015110103c41c5000c3c9051007600040091081c103100b141c06008101e1203009010000c102d00b06009804c2c6d6003408000c50000c0c0850362481031303420041440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 347358408 1250 347357158 347357173
    0xc1b0b0f091902101404080304060207091b0c0c120501020c0606040e0d080a15180f0b0a0302040506030f0a0308040b0708070f030209010207080111180a0803120403021c08060120 78
    0x14a4001002d02c00e1039031030300f0514407421501d170704aa40c6034000e4000101c0e5500c009030401095038108100b20080180c48010022014141d40c188400c6800385255010407600c50b034000284000c054144000702900c000d00d0046045070302c0c10741e01030341107843c41141c00e001d02d0340010100c0c146402280385032001d260140c04114981e0070141c40c1000040c02c1b8010690f60b41d10b500c0720885d0548018000f401245240188042c600c020705410b030f500b60080c41040f51309103070340e680194903260500303407c0ea60b04613004103c9544450100f841c0140d4485000080c0c07044801d92400d150300208414080ca021702c1103190283c1e50000c082d21000745c1500c80388009135171504086140782c13103a405000d404174148103858155035514a41403d4841e058610080e10704002551070b01610503400380c4d012440191088110b80e450030740c51940300d001d41007140e20560056000142098408d1110020307004480c000b0010f01070b4150401041041d040b68100d001c10b50301710101807184459011509000c844a004007104c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 347359658 1250 347358408 347358413
    0x11060c090d0312050408070203011d0c060a050d052521091e050d1d0a0b160f1101110f0a020f01020c0301020408010506090c0a02100c1b0b0f0919 64
    0x15081c01e0094042040120036200341042d01e00070240100d000d80b00b030316101d90300ca00416084400d5126112501c413200b40c10300c00d80040200d080134841030100d86413500d8a00b682c2c01a50240704000c40848000d02c2c0c0700810001141c2c2c140b56100168060001d25208058600c0c00d8400c032619468420400d00d50380041c00d048585500490050352256414035807002070442440d8042105040c112207540100b0441d004641d801004c0c81448081441449140045c102c04036140c2a12409a01e10040e80094800e600c002161110b0746959030000d59240203003801e05241c101c00f00451b64003400541140c607515480710000413a02160b0001c003001d4000e812003076080040d950100717450607066000341c600303078107440d03038284041e000410381400041010f14040f020092068401001508515024032850950540c0000c90300040e40800300c00055440d0000000d46455070141c0481111601c45e0780d82400b040301c8202c01341c2c00768690bc003049a043d2589040305407a1031207402d000100d9141041050007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 347360908 1250 347359658 347359669
    0x3030503012907050c0102011505060702060703020c060f0c010c050720120a030905040b10170705070f05030706050a0203160e040b03160303080a02180f040605100c0311060c09 77
    0x241001c00061900a0b02c070614000145030003400c01a04c181d007020713542d03110380d580a01a8a06007010000000710403410324000584500907841c010b4011480802c1c03001c1018020440030146140040c03440d070310782d11185840300c102e51004441d0010703942000640c0c00b0f414060b9050341d90095001207804c56940050028041404058012550040f41a00c0f9288e9203034052080e4030045000340d8544000d64244070074082561201c08456014004041d011000160700c61884200741aa1030b0140729141c0764000c00b01c56901410310050b002c160100c000c1020800000b00410a040c03180c0400d020a580f5071100004900003143c200c10441c055a41c0215964814070f4048501080108001403881070100800d2500461000318081124095003c1c000d040d00080d40e1548000321140079803070710500b4640e044c1100070584e10240990000e40e1110100d54540d0071076006032901a00030320725151a04d6004000803101c0400b640815581d01c641c48020102050251050061b00b170002d1600c42e94030107000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 347362158 1250 347360908 347360939
    0xf0e0403050c15070309020306010b030c250218091e030904020a20010903020f0c0d0609080d051f050102030c0d080723190201140c0309073209010303050301 69
    0x50b45000f403020903035121035881040c502030380035568002400303074952040c940b401c030060b00480d4036040700b0300c100980414844200c41500e16803044024000865000003a00070555420081d4801c402649070650352180b07104180c0b0810440c0105c3d81091300c00c0115000a007c044822801030f0800c100301d00841c14281c0040640351843d2902001580262040c03000c2540d54410440e0300707944501100091540c10890104281042c0d0040c0100c9034400303000031a16991850000c218503101c0c100031051120304025946140c08480b014070440c0b07019140610041000c1c0c160500b00c1640d0074002c286c0b9440003080e02c00c000403110081072110044042907500d0f1a0080008003003180d411040b002c0d6207402700300c02e601c05018541c0b0680313514000440903001e07840b5584031002c581c5071050141d006d81703003e0001d58001402c00109a903907100c0703070b070304500b00030560b0030015140e540038280c48000c0c8040f0b45020009034a03040d07400940090401040402d80303081c480a000500284014009a40c08040c01e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 347363408 1250 347362158 347362177
    0x1f0605041406010311120108030703030c08190b040902120a020901080703020d061a030f0c0a060e06031302120a03170108010e0618150403030b1e030a41070f0e040305 73
    0x4908007444681b000d055440240c0100d449a0800b060390700030982c0600401820100e07605040c80140b510103003541030003110b47c91642000da2981154046170f01c2e60b034820b03692240c0242014405055038a4101d035100309a2a04070300469242d00000b40398800031940d201600d038020200d001c00002c2e5102d58010300200b580e00141d019080c41540c1283d5000c02601c8403110030000504007068000b01040020b0740580d00805c01d01c00d850004400682c0e802c0201e030b50003000280c1d0300354483d0250010410f412030700d81c1844444d1055202d00d5085c0b5411480d1031007240c101c002e50110380c1ea00c621145099a0314000341600c5c560054000c81c0c500786100311002c131424a008100c4003204114038940c07442d03080c150340aa01007039130b803003c0340281d08200140d20b010420080c0c81d8080b00000c071022036175070642d40e5805440000d2040482400000c40368040a107031203081074160a00d009510380030740400305001c401c1114480d03000c00142048504c01c1110844610508580d00e60b6140d0320203842c25071021950 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 347364658 1250 347363408 347363441
    0x26070b0612070e150103090210050a020a0b0a150b070209070f0e0303040308030a05060301060b0306040b04110f0301150c0515040f0606150306060215130804081f06050414060103 78
    0x54420700408020b1503000380f40448004070380d41086800301440903801e1103840d04050601420f0700260311680c032140c0c01c0752094030301140d0342d150115040b802e01e51310080003071640c02c40380240b000440301030300101c440e0140303900c01c0300403030b5078032210754160b0700c00c040c8002e4001c2994000aa011400f070701d40e0800460041c03c5c111106105171000130305540c40364204442c09200801072060141d0a48900e0341d00c140140c00802c640c604018000c003213400010700c414820fa8032090765030255113468100d40b0f030403500c4004084e281c982070b03089040b464000740100c0c548510002400d42c542d5100390001c0840640010242142401c0d002d1000c240c040001c3c8203484022203141024000341d0648520402000c2c4d1901c0408803200052001f0103079501940041d007158002c05d010034003131141000054000c510041240712000c01841d080b000c0707000d01c3d4029046800303000038030060002000c4001151803001081046001e03203400400080b24102c0c1100107070480c08100181c4c2ca94007070b500400340c01d84070030781 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 347365908 1250 347364658 347364679
    0x50d0b0d150b09100b03060a0b16060e03030403120c0c080d0501030209100f03110105071e03080105060a02030d0903020703020a0303030507120e030306131d030408010c05090303030a18060203011226070b06 90
    0x3c0d1009542c0c40444048000d80c6221a042d05002f0244280c490030700c02c51001e94554282138034014402c0110105030f5900d55640d03040750b11440c0c007480d40c0c20f81140c0d00140d85519241401d130581c0050100344000da020303029110008040031070701c20a15054502580040c808a421512502d0340c03182118112818044c04220070004156140c41c000a04c1e00007416054000010b860300030500141070380564011502400303000446a0080242d503856142e2a100048a60680c2803c0746071480d280d001079000016018080181545900030360700c5280755407241103990f00c525100b842200c00ca2075002905800138000b084061611043c442e4184901b104042041c1000892905100c800340e0a8150194000a002c01c4481028040c079445200d441c10114182102e00001c240c5a02c8018000c6000719650901070700d8911408152068280e0440d0b401c64481da122910340210541d0b500302903d03200c09510b070a010f410082050500d2040d802d002c11402c0ca0f8440d0382c5e54100001c054aa19031201c034144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 347367158 1250 347365908 347365919
    0xa020c060313020f1c02120709060b0d05070e0607020d1401051e090f0715031b0c030e0a150c0206091309151b050d0b0d150b09100b03060a 61
    0x341d809442c2c09940c6880d007400510411068004a52099003e013181c4c540b240710005540d088002d80300c0e0181c54145a416000b4901414000c2c80d40021284500d400004291580b0640c00740400c094550402c014903103413914251a08500c082805620070810091540182411030500b5596441388001c18102d04184035200d0130b5840894a8420030f501c0040307900c0351540114180c5400414a04c0980900c00741c19012035100c845501980c2c075070340b2400b8000d41e805c170b1180d8440e0400500841c00c2440c201441e1000928007a500081a000200131010f443c02d14544401101c086800420010180c0c50403100191043d0380d040d902070b680421705100310009600c0345e0301c04601450703403900700041040041c9000712440d5034001161009524180b0000c2c0c040100c17035131055201802c0d041031038071181095410809094080002508280c1031a0007500300302c00300f0b102d034003e0f1039642014032410902070700b4495a03010407a00045c81c05080780d0200f00d00900e07840119005030025040800c01d0b5100c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 347368408 1250 347367158 347367169
    0x60c1207031119050924040909050f0a06050415142d0907060809060f040308191a0907050c030409020f041d1009021801111c020303090c0402040302150a020c 69
    0x100e014400300300b0001e0039a00350301d400440d65041d03220440c406c9542888010603a5490702560084082241d40c0c0d050700028840100a80f4225500000456110345298a0321201a10080c2c5044842000e05e07240f2641d42102402400300c1c0d04142088011a69128410304031400100740c4071088401c0414903d00315048a502110701c1a00d000c0002c00500d480c0c0030008048a80050611403140c119209010302c078440301410340c1c1c00540624007a90039440303c2c0c0c4030300d22002ea0866800c0c1454a42645940568040c0c05100c03413040b421200070b0099510010165801d1080002403443e87d04100028022100154080d000c01040b07080350505258403984a0403420600300049076040040e0001c01c4041484142d110003c1d200b0440700350304000d624a00071190032a001809410f00290070b0041494460400220050904455a216400b204084040c0d16503100b960402200c1c00b807002426581e04250085408480e030282002c118112040030390b510542000c00c43c401103000c1c00b4015466a81da0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 347369658 1250 347368408 347368447
    0x20d0e010e0604090b100c03091a04090203090a060e190807080c0f0708070801151809060f0b0a05040515060a050409060b040503010e060105010516170a090503060c12070311 76
    0x31840c009010172900080200303801c042d100c00d60030000c071081113800007944002c1000440c0d00110450800000c51a01c030342482c01660840c07800942702104000b888500050101400341c05085c0c100108040904082d407640b40401e4286c461118180c503101c00600300400910f0010f00410b400ca04001c860780e51182089110140074bc0e0329440800180000e51007030100400030104040200302c803561241d0382d01e804240318400e13050b0040c800701150171181010b802c00400303190b21090410000018055080050154500b103d0042022a001040c0d5003020711415014201d40042d100300b00c80d00d8820801c03654070405405041250510000681005074010a400f4111100c1c0c001d44480c2060141421925010380e14512035200c0401080240d03000401c6a45c3c0344550003441c0d6040400d4201080d400201a0b404140720b50700007490303a00d256103d0300034010b0710b508a0a440c019164405083c40c140101881515444482000b08800e40e0183c0d215900542c2461011810a1501086d080400e40b030f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 347370908 1250 347369658 347369669
    0x103050c12010f0c270806060d0812270a08030604020703050c06010807171b011101020f1602040507170a0b0a030f060f0e1603080307020c060c0f190201020d0e010e0604 74
    0x71405e9035050140740b24070540260300d030414200c4446203072041c2031b035880c100a070210380500c0c00c0701140400e20003071a0072030b202a046040c0311141801c0031000d40c840348036041c904007411041007110014028020510309110f5400040321802e43d110281000300030360280d10100e05008007004806104c01080c04418000d08000c0042c0c008036241820300440400c51402203220750304820b6200c8808034140c07810f00c56080c005e20340710300c080d490f9003200d60080c4115030f0031143e0100003051015000d101004002c201c1c07031096809011607142c0c41030a0325012225040b0301e50700841c24000a0101040e0344c015299980c006003210440e5642e43c4800c00101c0e52181d0503640305407210b0500c00e0400260240314410300c0000c0040c9400b020302e60301011450003500004000c07100005c08100d0f0742d0b01c200807500707070103800810466440c10402081550381081344c5a041082c040c900ca000c0c646089031407007008064060b005407026124898044a108214045042c107001456616005544900b00640080d09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 347372158 1250 347370908 347370917
    0x7231f02030901030f09390e06030f1203010311040902040c05091e0102070308070507050402030c0409061406030c0a210c0314040201051207051e07030e090103050c12010f0c 76
    0x100303000d0004003a01d0f909201810806d04004540000030b0200c00440081c00f02e480540c200e0004254000c000042c03001c980d0151a94000d1012501c09404500e0328041c00c000c8044a1140152200c40c94071652124481c61046400344010030100307821b21486640100d00030400195142c89600140407a00d10401070000640040340d00901c07030604e40c514049452519281480c2040a900000d50310304041c00014042500401c404d820402c0030080c000140c0002081551039180c010a96445500684202d50805081c0315000036100d151460341c2421a40203003000380b4550b0307070780d03070700f40c06684200b500c03100f000007030001005221504000410805006e6401141901500c1401420340c0c02c40c5180b0889054882c040c0300c0142e82107004c1703d80f0964411034042080d56014001d031500d010388042103d030340151070f2290b8010030040e0005e00085110342c480c103045000d250140402c2c00e13024000182540c0c84861101e000c0d2400792503640311040c0820000c10b0b018203143c100002d840000e880d00c1c0204 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 347373408 1250 347372158 347372167
    0x414030a030507030b031203010611071208031605030702030708091804032303060d0f031806020a03120203060a030b0604180503030106080f07020a110609030a0b070f0207231f0203 79
    0x907902d03004049800300c5c114001c20000380e060081007000d02c81072141806200c241c003070640c4080002e008100080c4220300000b1000c0e031140c103280e181940125035041709a015044410381c1e160103031060b42c0c060b41c0c01c0e6008506043c841c0d51020f0090b0702c190061980540f01501e03e07281d080010b4065480f07140300340d4552440d01d0341c444e1030344c132030203402075000c15104e42c1032080201366142c0100102d078540d00810368401940441c141541d83c1001c0a2a40d01001c203001404200181c000541e002d1345840b9603100340044800c88400f00172404142c41683e40720183e1401000842c15912003940c110703500800000b1000c400b00c030491452000c501d012140c90300080010800079070000112640421030700300500c102e01e0b0013031000b51100c082e0300c00205103080300452148070341c40d402c007605c41075000541140d80b5400ca03400d144120200c21072f108030015030307121030030181680302207100400c0768480c2c440b503031600c1c2d0814821103442600c0007240b50010244100155188205803000c10700001c0d54000e5547e8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 347374658 1250 347373408 347373421
    0xf2d1e1a09011a010504051c06090206070308070207050901050d060509030c2401060c080f0d02210f0c130611010902030a03050d05100f050907120614030f010c0503010e0414030a0305 80
    0x2a4980f80310b419042c400244401c0003540c8580c540d40b107188405000064104610f4a08a001000fa298000c1d40210b0041052020180c20282c52402407506400302e0716815501c0c02040380041090003819001101f0504980020740f09811068225040c1c1081c1d80c1008110902c07985000c011100044d2103111540101c0c1d20300a04802c3c41c1e0140019150031300198038542c4811a6602c2420120f0384000c100040700482d503846a41910300714060210b0078170000b20b120007000020441690320380040b401c03a00110303100042c0d000032108292010480c081195103081d5081d02c0350814500580d5680d500c80c1849001690700303014001003188680c564139182d450b034204a0044440041018009881010040c045e01d01c80ca02c00404542040703480703040c182c0d900041240d040c0c403100d0140c080d031410110003148a24040c0c0034090120401c2c1c0458455101308150a401d841c25561204c010510400061149000820700154442c1c020703510200140b1007100700900c0e590241030088002541c0d40e091108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 347375908 1250 347374658 347374691
    0x12031e05070c020103050f160513050a0603060315290103060b1303030f09081203070203070b0114031513020405180604241a13090f2d1e1a0901 63
    0x200704421072154a65032a023000e81c450366500b0300c111f56050150100d4010065558100b184018000180c008400c15944440240c041c00c69800700712581c40c446082d103840d00c0300f14402d0001003090300440500c03400d052500403900d820b03d04192410543c5420011515040c81401041a1100c01c4800800c061842c00c0082c52040707180d0b5894200310001804008803140020300751000d081100f90700d51340740ca9420b401d92440c071aa940080005800e2400010414103107841e41030941825001d980305061002c6422410b18000c80e03401c11095008103071754000d0b0070558001035104400c0c82c40801c00c080152041031800004660858051100c52821096402d04800414800704022810700c80e14094035540900200203800d424041e40080b43d029001c08100e41003d0081d50700580b014000e901d42d424a100203601900d41440040007000d00c0041502c600e01155070080d070800841501d68542410032815070081e0748080d100c5204a07a10068040e4030030f0a018003c112007000080c0400c09041e0f940c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 347377158 1250 347375908 347375911
    0x70210320c012a080703060e0703060801060b070b0f0903040e0f0402010e0607200303040f090f06061106010b070206090603150117010b1e0403081903060902040312031e05070c02010305 81
    0xe8911541a81041d811500f01d90010114060030060f481c1e5945e02c0c0200d00510344c5034441c0490307600300c009100e039460b01684684180c2d84200d0090008039112608045544039402c40104030380c203000c000909980311001e90b660400d191a0a03286800e0b40c5416400d8080003e5409503c042c20031414001190f27002a801140c400d02624080d0030403ca540701c507110ba602030784840c410740310b00003603c000d03581e4180101c80103050f2640b21a4661038171180300c0d10040201e1800c45006520b820008160325000d00101503003510f0740e90080c400c0d0307807c11811001c240c10015080741c0008003800501000c0d9643c0000e14418284001c0454030324140d5400107150b42042141144100104801441184060011038841038040d1800c846d044118002000c00717032155500240ca540e0010070301f600164094140c801440c92199020b01c0015290140e52040b48598440144241340910401d240d1034003c0c1c0003412001200da009000000c0c0104c82107050b103030f0844446000440c0101c04134219a0188a502d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 347378408 1250 347377158 347377181
    0xd0810080106031a060a05030f07180e1e071d150d0305160c0e0a02030f0c09030a150b0a0f1e12021908010f020304120203070210320c01 60
    0x28000e02d0318513102c0602c14181403214007088104480003509544550003280e00805001d41110348640b0900074080d101d905500402c110b01c43d18625800450340180079440c00790320309202900000d000e00c1c3e170710003c00308002d031000b040b401416000503440f50700c800d0101d0801c090303a12007090b61030072000c200c0b10007103910355491041d07043c04000408681c0c0042650340141d000a11803294882a01f0103c0b00554194000402000184100003590312950003071405942800a8103140c1c2d110142d1800720340c02000d200d29059405400200040f0b0b9900c403038a81d020941240c0000c40124890110b40f2110b001d8115549860041c1c004001110080c0400c1c022400c1034406002c2a41c1000e0000c5159094190f0191084104252014a5101c4860320300c00400b42c4200800c010f5104954000c0a0b400c01c58098903a08046000c1c1100c060000c8221403507164020b000d00340c182c2e0407800559000705442c4034481041c01c60b001e604807802c2d40011500000724540540ea0321604a50319190a660b8040f080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 347379658 1250 347378408 347378411
    0x2040c050703080105040c0c0209040c0806060303040b1813140405070501030b130c030e0307030906090f060509090c040504110d1503020607060504030203070605190507030b060f070f02030d08100801 87
    0x8200402c1c1d01c0f00d00241941d40484011a01c015022401c42d00c12a4000d0701030f50080900051004000000e190b041c1240e0a2006580c099501c0204054490180788079807600c03a20b003004030410f0006034080d0700d051004020501e09034009071840304002c40d9030b80e5500182c00d204000c1032000780203082048100030503090ee414802080050041045082180701c3c40660648072160b12151070f00a4100203c0c00090390704403515580b0604000b81461620b02c182130101c3c1c0301180c00f00e0090403404050090303510f1615410f14103446003091100c0d11030000c00075003070b90303500f408041600c4d42c4600401007030110340c002084e1203100b24501403085544118242500e022002c3c410401600c400c010780b00d0b034039000380000805540e1404c0590a5114144004050074038050070060030183d504515502c01c03071741e10010440e076520352030107070304076984446125031040c4c0511130709004950120050140c507106a0300c1c442824030550204e4649424195443c001c204e520080105505c06402e844009048a500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 347380908 1250 347379658 347379667
    0x1e0519020c30032a0c030f030406020417070906060201020a080f04020f120c1e0d0803070507050303040f140a031e0228020117150103020d0b120c0f0904020f040c121802040c05 77
    0x1640d60b109110004198000208c00601400703059410b42c0e0040c41115081ca00c40c0c5403a80d64562141e15a004041d182c070311b44100030070601d10520940b10705042c942c603210415150384500003500b05c40240100e82c083c000c5030b05808244c80380203402c1c03d10400c0300d004000084481c810070419100b55006503140311040070700740322113a94003400040303144d81000c50280c1e40e481d030f400c049510f88100b40010b8001d01c000028002040800102001c40a01039240f00340c004101d0031800380c554024400140010f203501e1807c1c900304513051080c404000c018011a4000d1580804d038550350201c00700300e098003c0c01d012a040640d60800c00299040c2c06079840c0035010b18044d9a0b0b410841554400d013410941d0218070044c0189842d40280a20300000f09409489151b1200783c036582c05804241c20b003c0ca42030244140c140c00d00d88011402a50300400d4001e844814500384401410403c40520410200b8800020400014400c000e0141548140042d4250160044c0400d8404000d02c0800b080310400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 347382158 1250 347380908 347380927
    0xc2101061a0a11070f0e22050604080d02070204090606080f031e0d0209060c2b050702040f1805240112060902041e0519020c30032a 58
    0x8048440d0300a4a0030003001e20583c1c022020300c1c044e5290010314000a0320740012883c0d00a2208461144052590305c83c21480000760b905c1580c40082002400c43e4409808900024200000340818804038440103003000c51079000241910803c1006031f07101552140207100203d01031002412034040c3d80c0085107455130007002c50035030340754108418108000110304407010b171a6580444a41c00300092846031030b80800b94051b038407241a0044000d00c80c560b040c0c000d09030b60003586290320002e9561a101e00700101902400041c00d43c0005820405135118410394041301540c25403900c15000e0b07401400c401c0c0d103408007081090754424002c8240145540100428a01201b0760390300c15500c41c9000c20504000c3c400703d00641401d01c0b90304418141e1f40c49120819003264000c0d0702c510103640c1480000190f41c0704001c1203103e01c440320002e9400103040580380e280c0c06041c07041c2003e0090b4462901091140780d8544540007540c650741b190403624012a04030740c000308404240122090910700d07162442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 347383408 1250 347382158 347382209
    0x15060d0515030c130c180e0603010e0712020603181501030b06030307020a060e2b0309120201091a07050102040e070815090112050313061106010f0b030114030c210106 73
    0x1031018050380c036019800e46203481a804003000c0c840030346500340c0940e1584c40f1f17504c4641c0308588044c029031800c1c2e81e83d4400038000a15074122450310482c290072140640911241e03a00061005244054441050788084001c00070138030a0a0101200109035040d803074240d000f00809400c00388a5441880300e0f401594444030628100e1781182072808042c91840d000c50100e410195807544564405100c14030b5600ca01512110b54034802c0d039038800302589955408044000424000e400100c12013414403540f905001d5034005110b80300c1c0302904003196541c51500703a074000c1d000390000c401e04405002036640c11488a98102c801c00c02c40203035158440010036000107052080351281c0c20f007000d802d01842030038411100e150000103812841c1c1e0741c6070b403c09040c03880c2c0004400d4480c881c04000186600420401f03070155183e5400c03c1d032469107030a846000f91262261095850700a0340149145c9a40d54068010403a4800e440c0444d450a51001d09084a1065016420ad207041510521603030108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 347384658 1250 347383408 347383429
    0x2060f150901120221010c0e030106031e050304030c090902040509030c0d050f040f140114030f010501050a050405040507030509060903070f02190b0c030d1b120515060d0515030c 78
    0x1000f050f412036807841c000a0048409558102d2440c00e000b03041d880310340c4042d0041d0008034200c4d01c039003c082e000c10303092608130f4503035100142030041303500c0c2015a920036035100344000500600461f41055180d4079215107030b00240e4000c051803541e98030b003502181028020151b004044001860034a4100e5920a172100011600030041110015003449170044040c160340290000c03161002e40680c480844440000c003884c189030207c1c01c07110a022505400500b10381c0718003c40c8800c0d802a0346080010344441d00500034440c107010341400041003d445601c9218131036403240d5008030f254104120b09905142d4064070007505030300204840004108145000c1e01d81c2c81d4140d9400001c440b1011007c103500c0700c3c43d0092500050001103034400002d0001c0905108440b01c00100182c0366403c50103008150807030000c10108102841c072542c8440380c0d40c42640d11401108100264480c02000a01c5d1940001840c0e681541d075101400070140894140c032581c1e050a500a00810f1810740009208586 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 347385908 1250 347384658 347384669
    0x30b0c0d0f09210504080a030203091f0c0809010c1e0201031401060c110a051c06140403170403090f06051314091305100504110907090312050a091502060f150901 71
    0x44050f42000414414070032a030003406180143e0320394800502d802500c81c1d0040f07503003c1c40350b0044614440101806a074a6142c84400d4171490031150003551100070075000889014103000d44000144042003028210b000110303541c0e002c0710030050752031002504551460720284044c00703540c0014405ca5401002d2001459081445200c2100340c120000782d840300030f60001a082400b2282c2001d085407203040004007607200752000e0000352062a81c024003054111006030003e844403000c0f20703403041c041c041c1c1c98209000c5e103840b0700903688074408010340c0b80c10341d40644005a0001108900162001054400340031081a401883c6100d980080c0c06c102000e020a0200d103007280c20b2400300076040113074080c0000d444800f81f100340360a0910100c030840a420b8907014100d10400604070034402e041010941e9030100d12200c2409001000b21419000703442c0c02d000380312500401258404110420302d007150203590042040b4a0b20400500e0f82d0720020701003c1c0010046041e4101540d41d05025505460 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 347387158 1250 347385908 347385953
    0x6092103192a0c2105030406020c1302070201051206040902100216093c050c0913090b24060c070f061b020f040603080c0f0c030a1e0804030b0c0d0f09 66
    0x1454000300140c000c13065400604074840050006010754010841c030f000c0090444191042071800c2800100384e20400d14001d0010b402005620700444203054403641041006d040025600000c3d07010450301d80c1446030070005070380081707420090701010050103409401e640d034007071100c03104130003611401540c105564110340d0f074144503002c000044001c41c003002c0c49031250700740614108a0300c00c1407280e101501150081040c010300991050640c02510303040f943c8481e03111410b9a444000c03041c141e07240c401200030070300c445010350b003180c0c0c441c8003405000900002500419142070154580109180d120340d05200515a480c5d909031001511501030f10b0301a6041c2c0101c8a0b02030000d0b000340141d4100400b064000f080110001500040034884010010202d904609101d01055501c40040000404d004008a48461aa911400c0d54007800d80f081c0103942c103080c0c50b0750b2071b602e00c0715044400c0e590308500410384802c502c0503401b4400c1c024070700317110404c408480d030f480700040c5142100c034222501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 347388408 1250 347387158 347387189
    0x10509031c020f0d0507050106060906050d05060a0512030912060c0a0c08090a080a0c050910260d1101110f04031e05100603060b06092103192a0c 64
    0x940c003c0c040000ba00c0c1412099400d4410601c2000c0c2103601b099030140c405618014020071090301401c1103006980e01c944855090040340c003281d8010b008010b1203c0d40100b186000002e5035242c80e01300404e020200b60280d0f4680103441301340010400990100511548000103000030814880212040f1000d00c1c0703407001c2c0004580c01c2c9001a80324914a00b0b403c800d076800d0001c0c140310041409400d407880303074101d40311320341d5a45c0401442a04c00c0e204890f2080d6a08010010380d400c040c1c03010103241c0303200001c0c08200c045145c0142041d1011b00200c0c045100450b00d854000c3d0288102d00582500c522000d0510345220341200c181d00036400002d01c0e40480b0310105003840721804132441025401000c03240c2c2402c00700394035005000c440c071044401e28201403d406041c0381030390954000181c081c049c034161804035042c002411140c0404240c1c81d01040001440c51209883c20204c00c06142c0c0700d0200740028084055280d48040901070399400441c40000001103004034050704507514800b100f080e1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 347389658 1250 347388408 347388463
    0x1809010b0a260f0118050906061e0409030302031806160e0f09090f0106090b031005060a093206010f0305070909090507060f09030f0b071202070b0a0b01050903 70
    0x300c10390907168010700c02c410081140c143e540840090589011555400148242c0c00e2110182c0d0001d849510543e0402d00005140b0b043c0300758503043d0854521100c081c1c40784c059000c201240d0071810b054001a80000030440760b01c18600070107019401c0c100080140345043e58241006c1d020288041c010060024003658080d07031110309648911030014100782c0d1300e051000c0807644d100c0025040452030b50a140c40091491540d105d00254074201901822402104891100080800524607544100300d4000451003042c244281c80450382001c000514100050195500d1280c25808544040d4407980030001d1990380030840d00f040d40e12034100401c280c1c45004042daa00d41e51074200d045242d15100c499824030400040c01400c0b1101034076140441d460307044003101e0b1803d51b8080a0080c03c010140d00c1c000507a080e0342640d000500d4940a005104192491801c3e40c0c400501a61002501d038280b1003075840780c1c42183c4d100b4109003007007071070320716010301280c1c5684445d9003039010301106503a107494 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 347390908 1250 347389658 347389697
    0x30309090f0b0310090201020c01020a0c030209041a10050f0a0311040e0102091203070c0602240705040312020109050105060108190207050114041a010f1a0313171809010b0a 76
    0x20110b9006044d80c0e12000c0007015400184910314060780103100d4100044555400400c40304251038100110340c0c0740600b56000d20605c00406030049640c2c0c1042400b08030403034070216825000e082325065503040f25180004108018220045291140481d0141000080c030040094009042c06a8000c2071929200821500a0158507800d0b80c01850051a001c00c02c10048020000c0314442e05840c40d6064540004a955640c0000c0403030051200c10740c0a5040e040ca9003006e0b50210b441c0ca0f00314602503e03552000124000d034103604025030344960303480d800c05c2000e004241d80f120b03003840c00524520701024900c2811115861b030039903191340044d48005010080d00082c0d04076000503810718042c1080e103000004443c00805c03541d001210b58002080780b0803011b50041c100c0302a03807503280d000d000c041c42c040c2d401e42c000b820711000155041806c3c000a41c1c0203070800032491007091080d0b10381ca46110102014403480401c18840c0b10583c00610407150b00e1015900004003038640714220054443c0d03980c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 347392158 1250 347390908 347390921
    0x603060837080d0902090108010902010503040311010b060f030727050409060b06030c0909011208070605090307020a03060606031d19030c0507080a0201030c030506010e090c12010902180604030309090f 88
    0x2000c00c0b0001986041d075001c1500b20030062482500d20034160781e40c0710b00725401c070341c1101e000030b0000e4400c00129012134490b00c0507100614946000091070000794000808a510000e09803c119801204100d4800e402c8606036904194001001c8884001d9881200c2d642c281400741ba0f214903940d0305108140200717503014580100010b0041680c0e030a103d184090a0f400c1000c4403032165003000d001007194000f1055010300300d54407100c0f86040000d80d0790f5800103420020000405880140700c1040503946d0307004110021070113104c00240352400d08000030181e813000050b01d40b402900c0121680c0c0c03124001444412000d0505148103c8062450101c3c3d4480712070a02a10354460360a010488201c0441c4200e0540e200340c0742003040d60f8151100350705803801114a10302140c10002c580100742407241520358048803103036a132490308408034041891b03000d00380c011650303503a40458150b100004a0514102e0048202d4041c2e083c1b501c0c60f0b40080a04c2624080c0000c0180c6078031031f0341d008a601d90001c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 347393408 1250 347392158 347392163
    0x50d0e0604050102070c050d030e091306180c0b0c061503010b270f0f15011b110a050406031e060209060a120b09060a0e09190b010603060837 62
    0xd8026041c2410001c3c00f03074000c00340a6074034284003100001c00b4a00100c902d10790382d40c16152042c0b01180181000a40c5030014040c21602180c1030540000602d24400e00708540d06408070000b401505041c420b01081c1e903a00705043c0314204200350494914000340072940070108102d00102030302c0c0f020201c4d014020250f282500001415200300d0342e81d03141c901d0944c201c040d060f000402030303036241c2c03840d182084181d07000000400014041505001561600c041d0440103041581a44510380c50320624410714540550324440388009105040c500607000500030407040740c0a001d4981540c0301c980310407990b90503000c0c00030300070f900d03072800c01070940c041d5600003800501c9140c4540d1b840e00094200c00349001030000c0300b40303407032441036080c17401c0b44440d0f001e604003609468044c0c3c18003d080c0c01644025110300980d220b00442007603d100908140c01c8220b100329210840da502d00000a0281d5441e90488103140d00306800e4108250b004007645a080a480241440003450710b00e021044004c420002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 347394658 1250 347393408 347393413
    0x72f0303010b1b010b06070f03090506160308010b03162610050306090a030503160e0607050c131407051b01050a0e1002041d0c0d02041805060f090601050d0e 69
    0x10b5642c0251010784410700c50f080750f0030f0100401c00081e070700b01d400d845504c1ea408a030611240010880c0d540005031120300c21704142c2041a151400280140c005600241c00030354042c040004065100500c075006142849a803805c60425214120b011801c641860303080004040135681004940410300c2020400f54000200030b081141070848811094003400c2d00038494007000c16028400095060f210070f40542e038150858989191100c084c56046020303204200d5003401222555413200c0040c0f0b03400b4415001004021070072400e000c103050b0120304402201d4074003030000400300d41c20511260300280c40e207402c903929502004100001464200855a1503283c0020440c401400341d00c5031921070b20307040c221400c240901115000b40e104a00910300c184003088402840086210002e42e08401680074807402d062220ac1c400d4101d0704541d001300200c00d003010f441d00107540c59102c1c803908040103442c4d800450079a640450800c07480504900c1c100b22001810108241140d4007001044500006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 347395908 1250 347394658 347394661
    0x20405150a02100e06060a0b070302100f0906060e01150804120f03020d183315080d020c040b04110909090f0a0804080d020303011203032301121505072f0303 69
    0x307131269245000c0b2091070052070105000b007200c2505000b5a0300155040e0300034039051003c0d059440140503103a1900e40c29940b01d8900b200001d065000f01005031a0100034500d9961611406004840c217409006081c0070b0450103000105012442d51280c0e81418141042510000603003103000b845041003090000d89407040c818040702a41031207440741e074050900152030206120304901c58118151303c0441d0340e07010181c108081001500140801c44040b1902090701e607445690f60700b0000440030100050f04540a10201031510344520306180300165020024114025105040c6208884200c2e10500840c00050f100702410042400a0281541501d01507400340c80c3c07411454201d8001c1d00806d0003005100074402d440081600c2c101c400070380c2441884801030b10150b005103609103199050b50072101e15600100da881c01c0f064020300041500d003a601c0301600707100c00307505503145d62006800d05200a000e09154044d07440030030f0300f6000d00105108100c030112054521600185a100c5020100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 347397158 1250 347395908 347395931
    0x1b0d080d05150f1008061201231b03071803140709111e0c01020c030a1e020c091807080118140f060a021b060a0b0102010e01020405150a0210 62
    0x400031401102c69042c04515895000700304000f004219030700c250040800280c403441a8030440d80150848070281c1400c002c010540b0046003590083e1a40b034040800700701400070711402d541c42c190352126043c04103403160392144250100340d21020303104000300308400813900c0000244c09065401581c1c0001c100c6104060722180d02d841d148180701e0781002e145480700c494041c1d01042d00311079414a43c1082e281d0180740510790200950019800c079010b543d8240116003074814108001c042c0010a5214804050700c4003424035885c841d80041c00c004c40d003120a405442c2d840703060019401c0741650405070715075050040020f141ca0200e038032121803507091080f614815103400350070452041c00303100812181104509020364031048144210003640c070040c0013a0420805130301401c00e114110841c0190000300c10110352804c1410703207450700b0895a0344003001043da024802c0140200f004802541460300e0300d000200e44d0a0040d003000d410140000f252510140f00703000c1407144620300c210800162400703a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 347398408 1250 347397158 347397161
    0xf06051b0118141203040209011514030f0f07020a03021c021f050601030e0a030207031104180c05031c09230a0f0806060607050618070f030501020d0506010905031b0d080d 75
    0xc089a01d03080c042e02e13440f004034651203401c49210300c0c1c02400512042e482c0c072548805c41141c964a040800c42e00c40c4141031031081400042d80031b940314032030713500e550308004405130080a0050412070540d405101d454002139004035000e49028013030012820303007401d4040d040c2d08201048044c42c1103103441c0343d02d0000049182e81f04d9800340c1303401e9800704013141940710460740c3e9041d45000a005640007004c10000030700c2280d5102480344003e8400b0404c265070030307a8190003142d00e40c01216848202001072140c3c0c00d08000c4241100346204606001550f07841e0080d0611a050090302c5002c0d03441d081c2c110450240001d0034043c0325009c0c0102842d01e5484410215080083c058a6801d0003280045801488c00710140c8140c150004080c102035100c241142e2004013909126100d280110000040c901c8010401e4000447c041c4001582da04189202c02c2e003224001892581070108145060149441c0051034412100213026528030305c202a0300094041c000510f0002d2008000082c40024500035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 347399658 1250 347398408 347398433
    0x12020406030623090c0f0d11090102060a0c14090612091608011e09020409290108010504050c0112060801020d020403030e09063003030403020706090f06051b0118 71
    0x110306036034103d809844095141c5002e200c11003680b200d18040407a48000c0410000c0c02d983d4400607a040c900035680c0c03441015181c5801d00e9031071036035003c1186000343d6010b000003a0b02c103c03001d204000781c0c01d0410014260310004d036809100001d0100e40e060954840c0e204032102e150b0405200e8003185000504a039032074034072602200c030078600d80900090801c0b0500075507044070000e859005402c802081c0090080c0790203202660b105440341e5440021410100c24400c0108841c060001512513112108a0090040e4804040342c2c0c50801000f000c6080440d502c21400b4007441e0801000c0355040c1c00502510094203c449654400185400981c800b54001c100f200e00c6038a03080c00042407081000441c180444030990003010003110352100d40e00d94031685083e101c11501031118021a140b2030361840e041102c01b200544d0111400b030080303542003640c0308001d14010484032002d504100b00140700b40101e05d0005641840c2486070309a404080d000040d4001100450030078427980c5052403800040b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 347400908 1250 347399658 347399669
    0x40506011a03041a041511090109170604020f210d0f0e0f0f0126010801050105100c080304140609250602190201090b0412060501060809060f040201120204060306 71
    0x601e180c0469010140c00a880c403c0b80c22030500848150104074480080300014021550460102c2c01740400701174500c580900815030403402034030350011400150104009807c071544845144500001d4020002800c1d548a58140e640c01d00c400b04e540c021843da460030b0507a106030351440706800070110200080200700500d4035500e16042d0a620402690540c601509140e0041000030b0850024100f503c00c2d01010744062411130b01030000c0750340f003c0c41b002d83c8202c00441044070000400220200340602c50242c207003212445102c0f1045c100140040701171182c01000700c503010001030240030840758100e4030205180c3c00e50f40c441c0740450300d240d21140c2d0008011890000b800600d0340b0004140742000c2580c03490b0700100400c907800c0b50a00b10304160045d00301e04020b450744000c60b1954480002c3e20081080f4450811a008149060020340c0c038140c0000b0108003480c020040d034050001b41c1d280d0000707075076a55030345251610f0004a0f107040042000009083c000100007a02651582c8264101ca1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 347402158 1250 347400908 347400929
    0x114130c081207110906030a0b0714040e04060621240f020c0106170705190b0a0207030501230402060a0c1b06030e03040605070314070218010513050c030711100504050601 75
    0x2800c03805c000a640d01510710b00e40640c080c030203080000d000c02e025030785c1002d540c1c1490804070402041c1d291040e030164108482d550358840c00d010400000e8002c081c051b10390808a940084903c030100c05019002c250301906031184005015079820381d0f02d03120810449540030078806903c002d10804042d6022400c00fa407550b180410019042d8040308609094008000190203498030b440100642000d00c40c000003843c04440c100002c212880100402ca01d0350141c0281004a00d5401c1203821100400c1c104030f6400c1c9a109107049201081d10707240d80c0a64111030340360710340181c0d110450b030210101034000c0c0001e1031801a00d040e05010905402251a50781e03051110300b0350310315110713228081c0f8402c140200b4014098000028019008000c0040301220a0360404205400254404410b1003903280f038801640c0040c4054103044501c040940300c0c001081c46030342441901c44c0e400e440020324410412068000694a80409020b904000c01a08000384268103040c14604d03100c840a103e49400b80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 347403408 1250 347402158 347402183
    0xc0304020108161d040e0a1112010c0e120a020306010e160e10030b240703030b011b060e03130e221208070c14010c0207080114130c081207 61
    0x20440196507000d00d150355a500c1c14881c039010884d14484130807411694844d440f01c1d000c13a001c0340100080c42c440340c000d0903000703100140c041c28003800e9802c0b00c0b209481a41000a01c520242d009100d4402c619001c0da43c00b0704d4440388005060070030702007280096141c003c1d0800000e80c2c09081c86210b00646400304d0b500c0d41c03602e20013410b50f40006c0d03880b000e079042225403441d089590700a900c004000403000c1c014010202c5400c200240c5020496080108010086000e00a155043c41140c0f40b5031300a0a004100c410300b0443c000740c2c015410380003451591205c2c4034540c1e000d000e00c19a032618009507800c0c0c0602e52586041c1030050780442c0d100c031100c021401c03280c400c521003034082580c0381c1e0414800c0855245c66401240e100c800149030000b440392441c4e07007000281d1034841c100203100c441e5000083c0351001071070003801d14605a00c64403c0380e040504a03003041c400c550035550402c002e040007541d404e41628001080540f558000381d01c074042c5451400000c40c14100030049a4800d002c0040c02c13 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 347404658 1250 347403408 347403421
    0xe030c25140f030a0f03020609010507030e0604020405042a080606010203071a1017011d0f030d1505030703050f071e03020f190609061206030b06090a090602030c0304020108 76
    0x3a60382910a00161611403142512030303082203100390341c1c6040d019090300d101c0f02640d00c50302e0803c449460201d0041e40000d0070014110020310800380c014050345400d21514201e01e41072550703000003420180c4a43c0c0d84401103404c110f035100c03240c1070400148410b01e0449002c8801d00410141d1485048103a0084400080c1c1030340c408000c0717480661b030068800715052a0181203a100c1d44d401050031107000020340005c80d108043e00010003a00d40c000c03001044084a41d4403c20f211011261aa5655804400624100080030080e255000c810f0100010501c40ca00c0079000504000d0b40550703018040d024000c8244000451946944142c507800c8809480d6220403c2c910a11703484541d024011100d102803006140c14400c03c808000300421520300701c4149e00215a4012040d0f204801203030310500200704507608440d03190900e0300304000411500d0301e0764440b00c00d071241c01068984125103100000b145e0b4412507200f44601a08044115107900e0081c020018a510555081e808916a440040c60 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 347405908 1250 347404658 347404723
    0xc0219050a08070b03041e060f0923030a030f0b0d1415040f02040c0e0a0f06171303030c02030f0c01390509040f021c11030f0c0306040e030c 62
    0x3240c071300300720740792645c4d983d92580541c0c0d01303031808081e41102c5401e1390140418486d02401080645903c40001d410446c1e1804085481e03941500c01c40c0700204140082000c800801692038240e0f031401c011404103c000c11a100400986107180e07070001c254aa4003061100d070904000c109144003007160380c900803a040411844004a0b00240391608076116040181055008240901050308040107104162000200300c0009900003800c07001c81d0f89010480598051465008005030240240300d6080004200000c00a030400c094289030b200c407440e8200e43e00c01c00466521440c0c0c80d00454a90f245440014060581890100c05c8031511014001c0030303010700141c21085440d00820b901c280318040c001999113400212100e64881d60b1115510760003449400103202e54039034481e8207414240c003400200c04440e40801e040e0790103181172080000d038059071440aa0404208903580e900c9035203400c00039001d81401e0a4041c0c407400040351700b15185000044040688003902040040c0864201091300c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 347407158 1250 347405908 347405923
    0x702070f0b07150609020313121b020402030402120a05010902010207150f03110c011e0c030203090d0c0623150111030405060d09060e1b0306040b15010c0219050a08 72
    0x14044841003100354006a1000030f075400c2400300607800316240c0d41ea00c807a501260001c481055003c10951001c4042180641c42944011494180b82c01d2403d032240c0041280103503040d00074016640000071030305543d1043d000e0741500c0011011108400030900c1c03c103000e480d012004901500c01c000c030214041000d800c0000d1494a0750303484c900340c070718051800c0700680592520360f20408020005900000d4003070040c1030071031203103400241085c103014017520304840054521804040c414028030103505004940518801e1440c54804180791480c1070140c000c1085602c50f80c60030b840031110302d643c0a00c2604903486904940d4014038031040380c100658620101e01103161213900f080000348031a151100c050200b002d00440006007100e032647e603c20480d40b9043c551000c0e5482456522000030f012441041080010b81c0a000141840c0c1d86180f800d00014140101e21440180c4500c12648114a00c0e880c03e070b001407a10b040a82902c8070445204030500503d400303032603505c602286400002420b80c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 347408408 1250 347407158 347407169
    0x280807240203040b0a0218060f07110307030c06050a18030c0305100902060915040e0705030f010603020c07050906040905060106080612011413020612010b0301051f09210f0501050702070f 82
    0x100005d035604c0114070025441402005400341600c03400a50350348030b0201a1404003604044a1f5451407681004102820801140b070b100e82c2c00344200340009603581c0c1d240403c0ba084d600742907480c0c1005507015a05920030384510f1031461180d9000000b8807a1080d01c44045038014002c2d201103407603110b1008150382c824076010303401c00d4040012108a040c0b042048101d0b12100d040d45013001e1f03c40100018401c410f0b945100050004404d100d0011842c50180c2d004101c541000c502c0d040e18042990388500300c9110315031040c1e21880005030107403915000900c1066011051b00d42e0382da110900505010015201c06008505618140c0c0307001c0c0341407051031182841d13240c041c1e64a60790801300414000c2c00c1003080780c01c44414044080039201d5800c40c05d01811500e6102e544960411061048540c0240c09004c841e203150380711624100e40204501003903818400e0300880d0401a00558201149102d00050100d9920042c1005200044d8082d9003d0802030342911602645c541c60b510241100d130180c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 347409658 1250 347408408 347408423
    0xd0c060c0f0e130e030d0f0b01080906190b041d3003040302030c0703050c030c01140909090f1002070c0902030601140c1e030a020111040828080724020304 68
    0xb10700c440d18000320014600030070311002003a2200b01c84d07281811030f00100d810844098075001e03a00101840e41c060308070f06040170310341140d0a00e8a11100c1d507540c40080c04500e070840603924030305d20309005504640801000a08140003692805400c2045001030b80b8001c0d02c103010350242e00340442c210703901a06500200d0340800303202c00042da000130016400900210154441085a4002401c05100b800021805400a0f02c1455070000905007840890701c07003e13040002c6200031001203814030f0203590041c0c00c1503540390170300e54521070b40610f485060041c43e0021311981010040f024644d40080c840b95101d000030024881e500d080610590001780c0f40d450209115010500c12808100042c2c8041c920150440b150400308003d5046404140080c28295400c00907412000d10b409025025a1001440c940b80c5440d180030b500d107480703459415038907015000f00c0f40c501d2541b0041d01403000303003aa0800c1c1c2083d074172007240c58844258034100c1e40e02c201030b03903802050b03500c1901d5074804d43c2d20482e00b1080e07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 347410908 1250 347409658 347409677
    0x70b150621090a020409140105070314130f08030114040b0d050a0b100509010b180f0307060f0201020f041710060509040209040615230307081c110d0c060c0f 69
    0x6242601da5001480006544640041c04000d85c1c0c4602406008600070b845c00150501c502003110300b9100d008041c5000e150900b080303c00c004242c0c080241e0b0001110074441c01c7c038450f41c07525a480308140900a04880004000410071140c002d00030b283c10213040303030208583c60031031050100102c0903410140894000e00380c9080446c203010011039214602a0300d000c985525400000c02e030000c05c0c0c016109103200454401c1d910011489038503824101228449901c0c40c0040020356644054042c8500304900d240c8245207690007501071302d00c40e2006003803103030b1a1515800d25070244806860020301da4860040020301103403061060030180c130380242040c1d01703540c1c9035000d100b240140500210740311607031031140700f085105c0d02a40341c01800100e242c40091450b0001a00107000a041200b84aa004400308104d92400050100d60a00404054145181164006540800e0038884080a6002c1d402c441c138074043d8041024074620f485042c080203912140002142d40c9040b104000b00271070000c05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 347412158 1250 347410908 347410957
    0xe0406020a180605090913020a05010f050f04240503070f03050408120a1d070b03040b060402040f080c03070b0408030d1509090b06130b18070c08070b1506 68
    0x40041c41d50410505044241d648082031070302003001694060b000081d0042800b070300c0c529214820a8004040846c1413001080ca9000103c0048403441128140900404104055401042a00c80d6898100f1781d07a030300d0f9580e448411000136042d00794054844101590b840c03020b4090800e5034000d4031a99100e84051036415420b50040c03102130f10940c1c1e03c06050007511816101107191511501a900c0c0126920300754101c042d40c00a00703c186002c064014110a019500c03410381600c1d8000e4200154400f80c0c0c4455012500a01c60341c4c1040321146900f04010a00d94800107500b4000c0c407081d002c982c0c566581d171482d40024010703402480e809410800c080c1d00b40c141180c1215441c40031400001c00030b90740d6190704030102ca1003818211101410030040140300d1412121882c900c1201800c103008110003c000074506d014158641d80c0fa540c22070740459810b03842800400806540283c03205e54454a906081110310401c4510907552580c03802c03c00314138104082076481c02d140c20004070b1140d4a148 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 347413408 1250 347412158 347412161
    0x1050a0f111c1d0604060f180e040c15031a0603040203010f150602010b0901050303160501060f03030e0405061002070506071707030e0102070806010f0e180a11040e070e0406 76
    0x740c072120568842c450451001c200400550b4882d042035803074480041c40c1840031603524100d41d211451291009000401c0b0700c0d5000003019541da22280f400d540d0542441100110006164000b146500c0c50041040100054201d08034203450740c5e108603d406043d1018200c00380c80c0e480c8480303091000c610880d0303000c605003100503540241c8028000700783c008030390085508542e40d000710741ca0300100d400001c0190f5502031040d100030752230035604c2d4a65907041c000801e40da0701c81c490040c60282d1649000340248035081d4000d0700030340b400451103110640d0f2030400600078189100302c140705524100110b5141c2c40c200300074400c0a0b0454014100c1d084c030301410013503150040b03c4190341c807984200c00c203196203185200620704c05103c2d8032507120ba038107080e000a01d09013880d04100c0c00c0d030f07001d0170061007444441428101203905801e5604220b954038800e840e4640150458400e131b0744502400070040140d203103115442e144007600c0420109102d030208650710003252250440415a000100e00424042d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 347414658 1250 347413408 347413427
    0xe0103090b09010b0a060302070b13140307050d260708090705150309071a07080f0906070c0312030c080c0a0309050a1407060504081f11070b0a050601050a0f 69
    0x14140059405a1078035400440101160b0851250359a00025035003481d00142c0400038040070714003113080520682d9503a003906c074044c002c0c0158160003034208040080513482146442c0e01d001c1501e8944e421071402540c2da010020341c03c0b01066060b50000c1c00001408900f2081202e162000b660343d8031082c2098410a402611501c00d44c0559403010449444a24500702d00751843c042c00303580c81c90080030040c2018040e0b0001c01c480410114101a4480b042007030364840da82059050b541d400b035180c074017082e500c502d410a40e000800403501006000d09510800102d038003810304500a0b61003030804408072003c05507080d01107081000400d42c804011005010002c6640c280041e1007107050300c55501e0024002030403120030086a0060314071031414801c2400414440c2001c2e030429092510007500c91200a12001c00d0000300c1011004080150b00069188140c00703070840da0b6803000b4200030716800000c0300c0e030225a42c10600440c8682d44a502107c04003041d960300c06140c0f8081c2001200e40124 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 347415908 1250 347414658 347414687
    0x4171218010f051908090d050306030604080a17070c051002090a060e06040512060a2004060c030e0406060c110904020612040503040b030a0203041103070303050d020c251d1006 77
    0x9114120844151000d80d480740600d83d01c178902540740c41d45e8000e143c610140700da641000428410302c15640c6000402c0c60304035a028101071703118241e17590111075510189144004015410041c416100c2e004000d80746a64020810b4403c29160b58030786205034820165801d412260700304040102030300c20f440c000d1120300b00800c010b103000d07503850004400210800002c030083c1c21100512505140c50b104010554900c0c81592140e07600101c100c0c032450060b4840d101c1485031a26581d400c040c400c1c200070460f80c0004004000780340c0c8969004190340b10714403080f904a02c88595103003492909540c960320841d401040340307107003840d41c10703d0081d1a20080d208507010320080c000883d81d50f10480146100310949500107071a49030a0811454034085003c040340260000a41030010a90040845003200b490a601595802210401510308080f00c1c212140c0300b100325041c0c0c402021203003000342c02c4410400d050081001c000e01d4bc9220720030b0030303500c040b0307840d540c0c08003008020300a50807819541c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 347417158 1250 347415908 347415917
    0x42a0c0803070e04090b09011514010e1c05060f07091403061303022107060b010512041b031b060801050a0612090c030b1f0801020703090e040503040b04171218010f 72
    0x14078540d9001b281d00e40607500800c503a511000b1090141d0324440c4980011f0403c5120200242c401a0001c0e00090510a5040c0a401e201050b0f078081d008011200344000e40c0302c01114450f141c001079070111550b09464240c0000c80348880029684403141110b5a40040100680841d0302d820210355000b0010700c60440c15030150780e5501101da4002d01e92940e118400c00460340e500d480e2440c01c1d8040307a81c0c00860b00e0600500b804050341454012284560050780842804103240340303410065900d9803a9800249056109402010035007240c40080c411a0344a458179402641c89004200d61720700140500000264030360702600e0040100d4004205840c09058850b1089451f0344650300401c80c215a000016241d80100c62070721010440303c4801004848021410090303a903500500700c928070310643d025003407210045030a000303050080f18010110141c03d03070b070754590300c0b0014510100300034603020003805098240921304088004030744442c540d15040214044a1100658130750608100223000c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 347418408 1250 347417158 347417171
    0x110a030806090a090c060518010903080702040b031612060c0305010605032a0703110d032304060b09091b0105030402010923100207091503121409042a0c0803070e04 72
    0x7082030594034098006c03607031040e641c1d1131900051401900300c001c01504100441c1e9040002c81c0700f03d01a6010356038116004a4018007550001c0d01d050280c021440d80d41c2c4402c0000230340400300300e48401c8040d20a12061025000e10032081d411a9002d10894000c40c41c2000081c00d80030041c084240f82c210881e50b07004144800c641603114503040315a04902103107060729010616981000440444901c030300d4103000d0100400c12900c03030203004032080c0000b040041c005c2403c10401da0850118001c0c0a40840c100780340101b143e540d280004803500c20144885408030803194859002c0320300c81c03901078450744103192401c203100c046003003140c0c100520750481c000d030141517540c2c100c80d5600c4035581c0c0e80180315181c1401c1c1104101d40050520450304607981400f040014075000145403c2e42c442d09210640d040b20036110300007031148c00160350b0710600c7c4c01003050f011302503d6a201d00903000d4101d0840c10b01580ca030140c0c0d85a8070408041c16005060002581992142c807030500e0b451070180c07020816 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 347419658 1250 347418408 347418413
    0x5120f060f2a031906270b03031216052502041509020d0f0207020f040b060f07060204060909050f0a0b1207080106090b0a030f020409111002060601110a030806090a09 73
    0x70042c4011007001c0c07803a0000a21108a000844240510380e50710300401480f407074010469084094503840d1111a80003043e55001103595a002c4e40e90443c000d4180c940d10788000100c1c542d080011282201d2480441542e00020380c8030714160303041c45c05401c030742d09041c0e05e24410320690401401c408070f0b80300e91a01c0025110144003c2d07804001d00c000400580c440c0860301c260310944400b02c0400c0e141d00e10510003500540c2c1e035001c880c1e000c841d003654002401c01005002c28411b1290308014142104000360380320401540380d00030030480b81c0550302c0c0d44109482e044100150384050324a0700341c580d205c40205801c1d440310b0b0b011000300e10300102a540310161131550b260509510f603201040c1d41e551405d0420079190540540d050024007100d11741d2885003540d8402a100c088035402a005554036840744040041d00501c2da1604440180340440d540010301c3c009646400854a90340002c0900741e06403084800018032100b060360507200d1180b69070b2407a0600014501c0140080e102c04e0311901800701 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 347420908 1250 347419658 347419711
    0x607032c0607020d030b0913061409070515030403051b0c040e0102030f06060408100b0102070504110705010f02040803070f0f020d0c06080606040b0d0e120408010605120f060f 77
    0x164484000780600303203400c00010b410300e01c80004210906040800e071144a80c1d030254050f0b0700c1400130800e0040540d003810054000c110100307400030540800c6061004482000130740c002140c101711810700446006040100141c00300303075001030202e0400c4c0310700010f07d80003003644d800d41c0c0c4103001110440d80c2c0840000d010b54884212010180e540001400038105241800301d6001d082070321140d2034180381c402229940da00c0b90a2442c40c41d680c402507545603a209102141c01050010b00c24003074140d1078104241ea540c0300050440c5c8a46c0307000b8200c524590b00c0d00941b0200e4003900041c0d420008240c880704026100c1000460301b0744c1ca6103404000503907442d840020818020746080701c100341484409080840b000d031800780f05243c188420010501442c08a440b0744880e80d20114040c01c59400b42403034030150441c1500b2000703000c1004540c003001507010000701c0328201c80d960307900d103664074550b900c5007014038000304250000740014240114041703201d6048504201c4d040c5c20098005800803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 347422158 1250 347420908 347420981
    0x6090712020f030c0a060c061d03030601050a1407060c0e0307140609060f030f2707090b0126060102010f0902060415140415031a09041506030b0108010203060103060e0108060703 78
    0x80118130b07c04240da041c499180f003180840d00c43c00c3d41b080e41e0142e40c144883d90320301000389000e04000c8001990340e05248950303012690004000042a1a2000351420780040d00c2e64541d60300000d0341c48140140317285400075641045989111124601c001641c0920144d640003c0b01307190000310400610007405030314401903105a000e414600054202050725010049500c007103c44501d0100c0c6243c0003c06001c607002d4211504000c0000e1000f000030010313100d030f40800025200c4240c2034200b4400c0c6071204901207118140076802003081a2000403405c048440c86040603412010074441841062281903030305140803103604043c903040c083c603045018180d2194102d50360503100d81641c2d481da59014050000c1004200c030f200c110641004000c20042540100094015a00300900c490244000d61000d405142c2050b842c224941c0c503081c2c0a8041d520966605000908c3d000000884824107a0341702d042c0c900301c0c40540310ba0b132140354086025000804441d0718070011340d02103907d148100b80a22 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 347423408 1250 347422158 347422169
    0x6100807090803130e070c321c020c10090e06122b0c02030a1719030b03060a02040f3501090c0506030903040302040905030c06010b030906090712020f030c0a 69
    0x140ca80c4d500f4249160740c0c0000261a12060001400c0d80c42c00140804c03280050880b1001610038040c289803100d0015010f00d103074a88201d01078070200c034a20b007440c90210403040c0c0c02e9401700c9414281d05001e110f20382600b07000c0e440c00180848810b101010200c0c0503590409402807010510b102459001c9040403c01c150075510f01f820780c4000503d10b6006450b80c5048002c4c0e05004400c0161074000c00e4071800001c0c80200208140d403441719903250020706035907100d0041000d400003c500c0b0344000e802070840c0d00c4c4151080c0b040000007020301c0000e008640c10b840c1c01c041e01181d050718020404070074180320610b03000c944440c9a01c0c5c2d040d4282032818062000d403048000b08203082c160030484d840d00c81c03940005008900800401c400564000f085a04403641942c0025803812141042030550140780030b030076198024500000741810f6500e01a500444441c002e1b5891616030b1142c0540e80c4085100301d5225102d206107907009490001701e5611701c190040c095444c50342c0480001071a458554109 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 347424658 1250 347423408 347423437
    0xe0706080114090606041503150f3b040302030403020411040e0601090e0106050a0c0506100602060a0b0f012d1d01020102070c05040216080d0f0e010506100807090803 73
    0x1080080000c40c10101c1c0b50805880c043d440e824418007050580c401d6016242c080002d5030b114001d00351083d84410308078445001c0c9000e80070f8480c0f00030340d0302070f000f0b118101030b4164035040321100e019049602d2542d45900c103070050000c40d0510211140c0d0300014010b4082d80028400040544c64501038001e01c0c03e04d803a0030b0303503841d070030710950041e0700d00302802d002e0400480000c184921a45030740c070141075403114101507481d984c804504883d0700c02808002003040c004c0d041806115180501e041d0140c031100d8007560460b650300306226040350250066540d0140310580001c100b540105050151071840304000c0d102e01c0300d10030a4480c0a242144e06000252500d9240c0c3d4141001030241480305900744001e600c1c2c0274403074a426a801215004041c0714660001d00f401c540360400200b040309550000441e51241e4410012100034000c2034000305416042a40240e250728041c441c50b84a400b009040c0714002c05108000c07104404d00504030000d010030100040f5500e2070800c040c1840304000f022 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 347425908 1250 347424658 347424661
    0x708060907050c0604110d060906020706060b0708070b13081902060a110f0306040e071e14060a0806241e040501021c0c021003201602130e070608 64
    0x103020400030020844000c00c0014058812035800c040b6400f0303003068006003288600325600c0000760107142203d0004014901e008490410450190040d050950041104000c401c0d620101d00140744101d0307100a041c02c808000200000300100703240d54100038003660281c1205419035544a041c0d12072141941c0d000c0d80461201c1440340e04002145e44180900e000344a5034083c48082001c5010701020718051220210008220351180c0c3e0103680041e0707204080750002d0766596031402400b0040081f101c44035114080106203e0703102d50a0f0040f0720307005042079203800b0007a1030031101010f01a01c11940041c50b01000c2e01100c40264800702000c11004510b682c032000d00c0410700c81c2d401581c1e04440390355020b0008021903a00814402230641195840040401c0303550012101c40c0c0c03c2c1400254850388204030a904960b056101c00f032440c03241c01c50a20341a24800806400f4000c2d50725418450984103d07200050038410403090758082c8a07c1c001c04c03840c03038020046003007250541207036001451000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 347427158 1250 347425908 347425921
    0x602070c090f0b030c01050412050a0209100608011e0b03130837020718020c03031915080c1e0907050307082401030e0f070b0406020c041802091e0708 66
    0x103d000c04a0100320010044985013200103407082c0030f1171080024103000c0c21112400d0110502c600e69007070b075001782103017428505201000e000c000c20b402440001100100003203020720600c058034015820703106908010383d181c0602d48850f60700050841643d8000e6001440006480801030000d1425008030700710340c01c011040b080c410107040c0313007419505140e00320320080e1540c01081d000196120418800d00c0c2403612102c16010744202040c5404501c0700100b040a00711410000911400d00032109208852501c001da4842885500801c3c0f459004507601074224904a0741e110038640080c06131106841910000507018181107401a01240001007009403459000d414036a2000e64901a0503048541030500201c3e42c0e00119014140340c0e075402d40c2074a5040820641c80f00c9d981040407a01190303202d03c10444950414881e01016105800300324840c0c0c175060269090500080c40d44040d0200c2036020804844000f60004040e00100c04946804000c24040c4503c10859030f102da010504012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 347428408 1250 347427158 347427161
    0x302030a0b040204050906060703051306030515060a020706030510090212040c0b0a050706090201050c0a0f0b1503060606070212060a0504170301050f0d0606050d0c090c11030f070602070c090f 84
    0x1954050300c030b00e10400c0280444e981c0c0112468000d071055480c2901c07000340d403806a4191107110750321210003c04c1030002401c01e82c5500400e00c02d055240318904154104824000b05004200c0c510b001350b0081003003070083d03c1c07181d40290b50040a004503034445581d500c88c20022640303c060f6050000644104102c00c1c0b014080c03141004180c0e508100d8584080d284005246004821005100e0358445082409581c8204155180fa185a4007507030300020341440c00004c00442100c0072182c0358110000140e000b10f0007440a0b0b203c40000e009480749655807010080180e00c100d0040707a2050090184900802c0d08100b02441250021400501340c1010309294103d03400920781c42c0c4a0700300c200010310907a11115000c014081c4141c0d80806500c00071b1914402400441c0c000d1034000700001c03400001d10001102c403000710350560b03400300445850940102c404002800310124694010441c0d0741d10b24038000002c09049000b01c1d801070403d54103a8038002c81a403603038001901e607601e40403e0900c0700c009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 347429658 1250 347428408 347428421
    0x40b151909060f0b070f06051e09010b010311090a0303050d20040305010e03041401030f0e1009140105061011010f020f0408060609010f1a071208090d09080604080322030302030a 78
    0xc541c002810001c8695681c2c01003c101c41c0010724903032312080400c01c1240c01d07240c2c420501100650072016458403600c000d00801c64103a040b40000c0c1444221030302012007508031483c3c0303c2d0191a100d072180c15a00e0582d600d034010703644030011668035403110760125001b5501901c81d1602c0d1208036680c80c954142a400e4420b4901e84884139041040100f199100c1c1c1015a83c00880c2820007150f0031114041803030050884228445030343c082c2e4010020124640c3c0d10540400f840344407115a02d80c040d02103039080740c0c0304840c0303d600003200000001580f03008100380303481c0202d008004164801410640310682e04090304504101c50f001c04c0a006298007030084c0e5602100940c1c9980382d540c50280780540c001003038441c54902140e2000b000e40c5081450084401311a0001e11020601d50b030104000c041c44c1045400c040d446c019448080802c42c840e601000448103860010042511a901d40f0951540083c02c141c4441250001106450240790002c104148c041e4500580381e01d801c41c40c20f42034500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 347430908 1250 347429658 347429669
    0x80901020f04050d060b030105041214031003031b0c08060f16080c0f0405030726030313061d0f0106080606030705150a02160e0406060905040b151909060f 68
    0x18001c1030510406801680d003140c070101e03111300000d1300c503040100042003d80540da8065003444104024400302c1500b840c8200355598070289040c5a010b00e20445001c190780082c1d17a00101003080000c01c0c85401402441f4040c81c0c030f405807411040e5030306c8051500a030b02c00c91550300223008000d440302828048550160b800d4410840004a000006100080c01403aa0f80004404034103810f800300701d08140c5020317100c09012244416140c202040d0201070a100000100c90400841c01c000e45010040e280120b455210481e5921541d5a40c94080c1c1010f82100d0341ca81c0c0c6c203611008801c1001c1042d100c4d05d0081c20300014000d42032130758490500c0b000a050350b000340d200307420402603131b101d69a11020042da100b590540320000c00c14100d051400304150020080000240071415440740b81091707015a104203020400f2554036071001c4150340702141d02034030b2045208001210300c071050070b6140403500c008000264210700d0740016100040140c018041c0f1503510a0306104826100b13842501924 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 347432158 1250 347430908 347430911
    0x14040605031e12160b1b0c03031f06020a11130501060e0a05031c0c1104020a0f0206010905190c020a0204050a090b010812041a0d0f140703090b0106030b011b12080901 73
    0x40b1940d0240c40b0a41d12000030031034002c5100040114100386106c246074001c1d602c6a582d201c03841c0207416a240c00a6840403d003460500000c40408d40e0000240210340003030f00a0004401c154a400502e54480359065030000d0301e80080c2280001e4a01c0b407640030340010b03121340f0b00f82d0500c801030104c0d1480b180c0046000f5401020303d00c0086002821403101c40c1aa450281d4490406140c908840c424241c0000d030001e001103510511150050441c0d010341049600710b5101d6030b41c1d40c05100543d071041d560141c1d008141050350940c48501d4001944480c4075004031001443c065002c1821500115030b600105036880c4441c84c2002500304826004200c000f0051203440409107800c8003d110b00d02c00c0303101c1041030035810031040901c7c20031f80d6100000c0c044100f103840315401c0b902c00541040701e1241c02240c0c441000405443c043d20a403150313503400680d440c0c01c9a0903c0000c1d0001e0108403000d40c10b2101c0d240c0c8103200101c4440c0d030141003511801c0402c201c01001e4801910840014000c100e199 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 347433408 1250 347432158 347432167
    0x100311030d120c03090c060804260306010c050c0d0c080f06090d0507020a120f060f1e0b0315010807030b01062618030a080105100c03080114040605031e12 68
    0x10740c420502d840d01c070904040001e0302044000294000c1443c20700050104281d40000038516400030115481603002d01882944007220034500d21540140580380000d000c010b0001c2489944910720501e6858450812603081e0520f0800042410b101d1032821a03400048040c240807040f414400c451290007000010318081c00c4c000c0b0003e4440c5000014603040180102d1210250f5590a200900503c1c208541c2ca01c80c450900340140500328055090314264141502e01019404500c14004a845000c00b049010310141100390041d19100c40c01d2a81840758015405800c905184018000c18241d0000e02c1c0f9203140d45851009440141c2c44070041c00211081d0711102e510303243c0c045854a15031141c1506542c1e80c4c2040302100d4008071080801131002256241c4515002040c45060b1785040b919121a140d115400319211040742d10001d0024a003040100100f403460100006e01000c01440464425182c20100b450b28000c1034100c056000d0401c03c81e0003021043c8202500008410426880c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 347434658 1250 347433408 347433433
    0x302010e0102040e0a0b1503091b011706091807091d060121030c120c050114190e0a17040608010b19120e06010602010911030a030f21020310031103 65
    0x71504014404400152030f00d0041c00151f50b0152200c403841c0250302d981d9100e083c100e003e59521401030483c85115a00c00d4038142c0384d58090750003c0300081040c0c02c041c20701d94600050101c1114054160800445080b00f0103810390b900b80140000340440300302c00500d1000d2905405c103001f00c196a100420340101c00140502d04a0704c40701d684101c41401410303c0034003035103021125401d100c0c9000d02101c60316610703020f10541c04511580d41c00d004d50024402d1400010301880050001c0d00c1c42200c100ca9060754a4402c035443d0408805400300c44240e40c04403481d038403248001203100d8062002a18001020302c245a0481341c01c602402c11054103d0a10081c0300008074143c0240d8021030078800b03020207400da400c0306600010802c401d144199040c82d6503d0101901a001140048078a04901da9101c500c1d401c00190441c0015090759440c1809469500151290500c03000508a2010150100c044a0030710303000a600415501c1a0100c0031031660801c2d414400168030b07694400d13003000c007070150b9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 347435908 1250 347434658 347434679
    0xc0e0a1202032515050405040906050f16022a09040b100e010503030405040908091806041d030921010c020607110a0f020f0a0f0b0a0e120712140102030907030302010e010204 76
    0x1913a070f186001d454400e00c400c0054034240500d0f40000e6100d401c12032000100291034000b2400766503a03900351040380c3c684c1035401b0f08042440c0040c0006034070686102000089442c01d94910806a0804103c1450050041840c3c004c0c219004d1725241038000501c0700084480c803880c40105042e80018000e5410040020f460780309611441d840390ba29040b00d4000d000d0003030122011280000e00d45801c14145010500d00220203c0f95144954a0b001541c1031215061809404251600001d10b29203100d000800070703140c030403034460982484080c1060284680912400850180039001400c0f80d1902c0c08000703008101d0408451942d8000d40c400f540042c41050b024100d440d81107400c0c5901c1004d07180802c0d0105480c0d84030221209030f0880000f146080a0b0081949450652f540420000c04100f403001c3c0f2800e041c8200800e40c0281c00400c9500380d560b0700c1038415485000440450803032038210310709a8200361904003160f00f2245007003042503024491641e04c018000025030525280c14000314 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 347437158 1250 347435908 347435983
    0xf0207050d060b03010e071a040b07080307140c01020c0d05040303050315130c080f0a020708070f06020d0e060907050102010e0706032f070b0a06050a0303030c0e0a120203 75
    0x40c000c926007440e030810003889030002c42103010040c0080051114101c0380a5441c0b070540304000340489505032008401a15a04885c191007070742000f40c0c5002c0302c1b9562134066030710050150701040500f00c0c0d0b1100341c00c684002000d41da000d2100260300c80042091007420808100c04810a122041204100081d00b02042c1d07903101400022800c0354001c2000403130580d03a107a9118054640c981402140c100340c00c000c0f040d00500c1d8406005d1090390342c08a202c41248215003002e03042e040d0034406072000030881000082c100b44a03d1015091140d45114181903989407450a04a50880010815400003c20007600140802d1000f0301080c000c00161a40fa1034841c001c42c0101070f2140143d00400c14903044000c0101c2d2821071680b6100c0c4149189400741e0843c000886402c0f240001003840d00300303280100307000c0c1c0d40020000ca81840c903568040e401041c2100072442840703540340a500c3c240d80e6082c4064000d00d421002056200c40c184109410b120181d29103002c0c090501d80c0402c0b01844540149 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 347438408 1250 347437158 347437169
    0xc150e040906140703090b150d0b100e0f04020907080f060d02010509060403030f0f030c0f0c0317010905160203071112030c0313051f020a06020315060f0a09060f0207 73
    0x522034446062007000f078000c5514001c24900e00d0028080c6090b0f050340000340050084040e00d0080d1995540102c41514000805a0104041c0f0b03060021841c20319140e60098400c043d81c1e100c01e69100910956100121100008035010804100c1542002e084195014840d40b400c1c2e09a46054040004880d0740540b034540145044003844c0210b9001d441200c400e8400245001c3d142c0b90340c0d2400410040c080d454a4000581c0d81800c02c4a0500902841010b014541c4400800c211900382c2142c09401c108015000c00100c50014141d002c44914024040c0c4255900400d841c506400b140080c0340505030b4440455004222081c00b00c2c806a1081103803540c01c460001400d540151101d02d940100c0c50030151901000078a82c42902041a07107908481042e10b6104888103d03680003680d0001b240d80700d20258000d803d261000611650003150700900d60945140c0c0601800081046c54105500a60565600040c03241c0800d800880810040a503468162080402108004d490b000c652056 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 347439658 1250 347438408 347438411
    0xf010206130602163c05060109050c042309010611190f02100c0312140f0c04120309030213020309190c03140d120b220e0115030c150e04 60
    0x1a0392405000e5507612000d40190a440044114100e0902c41a900c107100c0e003c03036001c010b00740b40c2d04250381e05c1c4100c2c90303908400075048070b03840c1c0f02668004c0c0c18000c01c6a41d00a008110124214102542c40204c0c0a81185103d5905002400f07005951070180c10220900c406001d00c5140f9030700c002808000c1c07040401c80c281c8929490300d4034000310b8482e01002941f01c0c802e40c1070944040e504c1500560440c2c000da4403205003010110142d4200d42043d6130b101c1d8a000c1c0c2600081080001ca4100c58002001414a501d8199140f80d50303105405482004c4000a0882340c013003040d0704d000c050241d0740213002c21045255041040311302d80d8403011141e0341080c0b506424035034014449002c1c00381c001590801ea2860707014040305241c0e03489280d841c80b24000325503207042a041d41140f0740700c0d0070003050b0b01a000d100c00300082d0034248900300c0744a1004e42203d446a801101d481710a0043c04050400c483c0d4159a10341036140064051400e40c20400220442818a2032103d0748006c100e054074000380c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 347440908 1250 347439658 347439667
    0x110403061e02070803091b010f0c030c0c080d0e1c0b0a020403051501050315011a07080c070603022805070b040516030503090a081902040e100e030403020f010206130602 74
    0x2507691400101032011400d1000c1411814028008021842400d0140c01d07210a00484e5194540000b658800b55001460740001c600113140948018032602c0c3c081e0400c0400d9070890343e03690049103000d40041d1172a4024070040041140c0292814121500407221a42614102101050240c0d503030300c40030f441d50080c000452101c028071b50403034000d5a08a01511207038200c081c01a950b0b16001c1c07240c14000c3c4110b1964510740c4040d401c01f541030301e07240360040c500300c241201288469004000c00350b0b00d25400308002c043c42c600400c201d800500c1562009a00c0302c8400d1301d01140c03080034409002081c03ca0342d9040e07902c5a44a0b08640c5280d41c48140c26050380c5450600900c0c101c44e003542009000c03030246000c000d10100001038210302e40c0443d810400951200c001d00d0721076030050030003121000b214081000611301500400240d156010468040d811031200c01002e441c03402d5410891601300140910a50400c4141c4803038001c02130000b4070090604041e1f030a8150035605004d80160790109 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 347442158 1250 347440908 347440931
    0xd0507090f0803040e01050409051b151306020c2b140d091701090503070b22030e03011b0804031116170c15070f110619030b01020111040306 62
    0x2500c04001d400c100d040e9480e01500c8200b190f9683d4031030700070600c4031540c0c41c000291b140381a011703400701c50750300c03d0141444004281031900301c51074003420309520410f65103188040c7c81210b00580088558440075203109880e04002a040821119071070f0f01400289004020001ca400d141019845030b10550598603081030a18520f00f181404150b012801580c8480c103d20b0352207415101030341d1200e031410f20070030052800300d4202c0f10541402001a00309010b19000310b40000369860f8850300c542844050a0184044504044031002c0b0480220f840c01e8080030082c04e00344207900d404422620021806901c0500c050318041c0c0041c0002c042100320800103510a0061082d0f00c4e004450b040d00918442e29180ea03040500035840791141039100c1c088003500903142c12050718110041c607801152400d861030310b030601070280701d2400303980da41c0144408840644945000f0a140d100503107101c0030340c0516080c0201034800250480e4116130401c4d401c01046403502040300c0440354040c000180e00b03d14031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 347443408 1250 347442158 347442167
    0x20a03031112040e0708090705130f060f030b1e01050d140a06050132010f120b0604061d0103050f190b09100501110a0b011703071407060908120d0507 66
    0x180403242c0c185102150005010000300543d03406001d09444440c00d030365480300c0c01071380c1c2c40262241e990f00c80d02d08032043c607520003158000c02500c0c41c61034010540680360200b00c10b4000309948110b901c0703200398081241c1100e138254035404690b40c0d80c099000551500340024000707940c410f00a814808138080801e09007400300b140c414816031014080c8030399a541c064040c40100003000b61181c05400e151100d0702d501c074004d010702600505031500c0e908524040301c12030b50021856000c100d11542d403a60b40f010b5030784050185c4014005540c6864071080d904500d4a03030000414013280c145402d2505010600c0d01c82c6100301e41c09100c0d68000d42e044030111143d00003601840c20703115001441001030007250a8401c5000007600c40a890301240c000190b6000f540e07401179000040c0100ca40140140200c0e110240c0c00040b20091030300312170414402d5100c09004401c8804008255805a1408c0104540181c900d04c0103003080d1300580007101000d01c03004202e10607040c036031086560316000180c00c030307009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 347444658 1250 347443408 347443423
    0x1a0106050c0c211c09060305190902030724140a02150601020a0209040c03020102070e0c07120504030602121b1206042d050103260d05060a3f020a030311 67
    0xb00e038221041004d100c00f0500140b0204c8083e1000155001c001040880c00f9008040c010721545c902c10b001c2d11b50b4000003800070050080700f00c0e807602540100044038142d030303000060740312098041520100c10b40900500482e02c40c2c0441440318605001500507141c0220300d47c141c2019480020f45140e40c0d04004134285680840029403252070b580600c824015a03407840b41c1524401e030200d030b08250711200071041e4038204441c219000d0400300003450001c0d442c40c1d401700d4811100c0c2092420240c99a4070301c4166000710503e8015408103804001400c9110401da0180d08860030740c0c0791808030007111800340107100802041c09261205064505220003414500083c03403207000c1481200c50034103200b0003415082c0300036101d8615004030b1440c8000b4194040b40e80b03c1d5114103041c50940300d416500d014010082596034840340c40000052184c803420400a081d000c607030009407480f03110082c0396003c50f02d4017030700310503400d010811500183c03603c0320b969042d290035092110003080e07862601c0e45807542c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 347445908 1250 347444658 347444719
    0xc0e09041104020f04031103012d0f0e0c0f041a011103090303030702100c080106080105040905070806070f08010b03060a0b13031707020102010b0118090b040e0a1a0106050c0c 77
    0xf0004000780fa00c0c65041c00741080e240310304420024407a07030f40209400e072600c03502d00050020b4254000740707018034440c142e00210390300d0101c046140f6400140c450201d0301140d06050050300110141c40040c90704102c1465000c800303c80030820390030400015008100700c90603180c1030168002201c02e964400b0801d0b50f000d07600080850755685020203000351940200307045409118204000a10740398001e055a034140c60040e03a81240c10303842c01c020400030b026220030a40705800781410201c0c4031003007442030350b204540c6515821001c0781c1640009166920580c001c8644e8401030090121560748c1042000c2203600e005007983c0c41e09400011106000602d42c03000700b4841451580b070324020f8030312000c0d280650003600200442c50b82c40c001511400080708030b0003104408203006000c20715086c1c0c0402084440a080000d807d144c4444281c40e050000c1c00c01d450124000740c05a404166800549024059a10700982807080303034865a41d0741e106e07031000c03141300f48421250380410241000e1442034804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 347447158 1250 347445908 347445911
    0x6090d030201021309061406161703070f020106080601030f0c0810090209012309090a080f130b07080f0a0c1a070206060402070c050d26030105010e01030c0e09041104 73
    0x501840e010b4000e6004106000a0011421000402c4259489003400b02c90844e00d0f8410319150300d80030003120768001c8881c03141040b011500613000c100c030209403905140c580031800c0d80c2d80c104020050204a400b4003403504680c10404240400e00c008250745045940c0548940712000d001d103400c86110800b500036841306d04c031f03080e00f000d8640700d41c2d04951405402920aaa4183d0326030840f801d1620240010100074828096210314a0030801c03540c59101100d5410750701d001d4010307070701c10350640e110540340380a070034020640a604120b40f1519a00900000c0c0703e5510345a210f03a103002c070710300810405c10380510021424000803030041c0c807040490340d8072005114182c4a030b010719400c030000903140751300140300c0c030400030762281014170842e1135050700450b9880f282480c250400c40101d00482040b01d9400b080109400742d101c004c00700c0012584c05418460307d07581403000040091560004c0c5504040c2450541d50150750882c5082c4018007054821202d40d40d26402c0c0004880c1b0800401034005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 347448408 1250 347447158 347447179
    0x606121b04110a18050906030c09040c080109060902090601020a0302070b030c0f0406020a06050c031012020315090601170c01140a1e030902011b080a0804030e091302130e06150609 79
    0x65500905444540d04d141e55000c06054560040c03003d566401c407400b0340c1550184000041c14540526070685c01031041034115a81521070540900b5111030020071550ba6481d0f8091b0021803400d80500b40d0f004500303200a00c0241c081d901c0c001d6a40000e4407032102d4001001010800b880c0000044038001d0801580c40c070303543c5646480095a420360440c1c00e546461400303000c10408444802100e0190703030706c4044411480d003400d240c1020130200c1c030000c03685440359a506010030078046074581c0c1f02e00c41d6040900700310361520750109102442c0144101254001480e02810740ea00198000a0781054915039500d90402500c15610b480c0c01641c6a10105101c00031104017660540140c2d10440c802c0c2e80da85441d0226000010b84120301c9000184214010704c40e034544c640c4100b800e59400f078003a180121001d200d0001061034003070141d6150000000740c464007000d41c106050a1441c1c1080c102c810071180d16040c3c902500c803400034011459624400e4071180f519903506003a6494075800130b0949660 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 347449658 1250 347448408 347448427
    0x1030803070e0312040503010e0d0e01030c02030904180213060515070201030b030703050303070906050c070b0913020f0d1b02060402192616030b0f060a0905100303020606121b0411 79
    0x1031790403900c100b512079030034a14075003840d24020401960392120b83d16030003680000c960064000c0d1001e03210b07039811440184980c210076640e5003c6c0b090b0001942c40040d00e8003515005101100b110518040b2569040c02400c10980d02c907007034519101c6d5000307613649468100c14401200602106d48019915100f001c4010060210100081d402203509803598a9a659a04020f840303e00500c0c3c5502c03101e030000301080003c0000c0900500f1a00c034000d280700001e0301003c0181d4200d07000302c0a1122004808541c0022481351840354041e03041d100c10218280714030300d003002503482d0402000240200550011920f0455201110308041e010021401e960723144e00c1b80007100b240c403000f080405940f00d040104a50740001c090311406030790300122070f10419500c102104480c90800b40c40a034100161000005c2c60019074416140901090903d5031000d501e0350600a00d0302c90040e12241c403c0d48507111408020030000340000461010342e0800e40190b4034000001c0051032070202400c03000100143c41c040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 347450908 1250 347449658 347449693
    0x121005060f030a05070306020c031306021c0302041211060f0c0a1a0105010504090513020604060302030a06061b0b04020d0602120702070e0f060f190621020703050301030803070e03 79
    0xc640c90a440a618420000d801c1560f207640c081400380190f00a110207002203000e68008140d1001c440702144d160082d031500c0520800c40d581d00c01001070300040401c0800304094110b08041c8034441c6015410a82040c600c01d55503992120001c0c15a08070404210300c54960209030344101000c011010b890b18401d40c01503803941c00345041203d4054004060303c10240d0501411410795106035030341c9007402d003010f01360070040030003512440304a9403a00310754005940d003400900223840640d8000d620ba080c410f05002c103854031078002070103100b0684c0000456002040900c0d10b07064002c20000b9040e100d90010441c400e6202c0d42c00b40015000140030002d03c1800402c02e030161001d6402c41c0d2007181e40d0500b240701d180302a120502d180c03643c200816460714120510f00c0081700300420555002c03c1100c445031900030160700840204060078501c0241494840c02c000c0030a01110041d8600003150364000c0c61403005010091041c0004400314112900c550740d000300d0124081d0864445080d20560f600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 347452158 1250 347450908 347450911
    0x801020301090b0f06040602031204030c0209040f26090402092209030f03050601020d080c0c0a03080a1d0705150f0d090b0c07021012091a0402010201200414121005 72
    0x50144aa0501110303131030601d0011103040b91a50b0380594180601444008400e2201810640c2000840b00003100541d40300400240124411200c0154a2200f4501200122803d0038403071034030b08009006c2000800854222a42c45400320380040e55406840005200d030b000e032041d40e0072403400300380c100c041a0350680e001c0d0410902a1b11002c41c45000508110261a012900c840c0107801420f0543c012900808009400241c0c1c0501103051000304031703110f86454812041130b03001032120004e1012b402d420744101e16000402d0003e01212555a544441c0d0341c80442c465980203401c00003810000c684c0003c20355500b04811180507a440d44c00e410741d040075000303a4a040d0350400001010070103a1210340111184140e02408010907462855400e4a07070f002a00c00000182d91542040320000b96148424a803e141a8a0000c410304150000900f140c1481c0c4c08080c00d60040002108035480a500b42c408541c0c58001d1030f4600c0398218003040c47c01c1407858001100344905030b00f0640404050b080355 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 347453408 1250 347452158 347452181
    0xa3311010216060b0a1202130b041517030c25050a030c06020c18070f02010e0312220302190203030d020c0a06050901020306010e0411091011012301170106080102030109 74
    0x9001c100e14031404c101c841c2441d441342500c6c401e01d00000000605210550102c002c0c46c1c0000041d5410b00a00030038142c541000c01c178240784002280500074510041926880588440c004600742100c003500e40307035150340300344002e0b0301600d00c02402c5851100b01c1c5180c4026010151060b1809643d920344030340d000100340a00d4015025404c035440070f90400c4441017001d00300c441c07000902c130b0b1246001038400b0030514000000315505c5a40654144170b00b00020400c1c00c1420028403001d18000e1300c1aa001c0c00300203a0301c84211301c400501d8001c40c0d40000d0401c401d51045452101c0c0c45454400246544030b2038000381c0c4014004900144103c0002c649a0452400340c1d42c140600d45c2d8649050b400c07032208a8040e40403c41070340b1050241c1c106544000321511112400c1c40c5041c0d04540000c2d10842a4002000041d1881c0c002c02c060910078002c8515807040c1c1402e40c206070355103000c0806051814001c42c0039080d80145c0c0300c40201000d40100c0b009004c100b00840d03a0f56103c08103000603003024440c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 347454658 1250 347453408 347453411
    0x30a050d021507051903050601021005011409060303070305042d0905070e0111060c09210d1205010312080403021f050a06061b020108040c03060203150a331101021606 73
    0x100340f00d019408070303103550b42141032030403415541200540040602404007811840b41c10251001124a48102070103020b1419501c044140024100002c12900403d598000c0e08280044400a500101542c003035401c0c000c40c0c5030035003601c4500881005082d040000d040c0d155000300207001001d40d800030707004900da5940c0d603c540001000540f55404007074030500d080d602c4080010491842d48014007403020005204006403d150500e8010b003400145600304650815001c00140c55002038120024118501c2e00307004941c5140c645180c100c070001e41c500140040302d000201014401d10509411031201030f03000380c80c46410314607200100303401c840d074084603440c2030000700300035000c0c0c000145c200603252001450b100c055801152141400b4104840903007010001100161031400618482c140c00f0b00912a150710301001c000d080400c0d03a115456403103c07215100d01d800c1400e03618460f00903019503105400d0fa048a030071110b40b50100c1082005500c04510340301c20403100041c400344039004480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 347455908 1250 347454658 347454661
    0x18031e1703041e12110102041a0a03051815040812070816050f031b070f0b06040515060a1107050a0303120e2a0402090409060b121b0f030a050d0215 65
    0x640f06203060307120014140c1100c920000408611130346884a183c4005c0c3d00150816540c1c0100307020901e9100135011030351b00d012030344904881c0d03d1301c1529480140204a0744580ca00c004c0040c2d1030b1100040070280c900003c1c0b001800348004a41141d880b1460480700000c1c0749801800202103440030f0791440d4000c81907034019417445220741c05030303400003111104207859500c03244058031b00030f07070b8010703140040710404e1082c9008140b040105500d22406140c1006e540d00d07101c81004102c1d480103020626540320505800c03030907101c0d10103a445d100154100507260107402c04059140c402c0b41c2e445a036014918110200406034001e881c6910003c80c4101400000c5100d2071780f5444110513040514504101c800210b5440b00300c00b51052903410180c001450b01800350f0200303080e0380c170350202038500c00d865104002240c04d000316a5203941800300c01401d2020314645c0e0003180c0c82741c45900b60b80b08003101020014680d401780152070140d907100e070884840c400803040194407103c24006501c400b00d458030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 347457158 1250 347455908 347455943
    0x110403080a0c1e0b0f091c1b0f1202010c03141f050913030e0402090913060609020a09080d02060405030d0b0a0503010204260703050a12052a0c0118031e170304 70
    0x29599041d1450722400c2141f603034a061088901030b005550410100c02c2001d149408900d101010880b028051031b111003100d1181080a42524030441e0088100362910540ea000c480403100b007030342c102c094002816101903d4200b04603a0740f1640d00001d038032130007101c140159850b07403601c0300d500c0c241f007a125490591042e03000c004c00c9001e89401c01e604081d142c40003e0080d00301c0026001c00510803400002d0300750f26200c0a004a80045200c00c000c1280b8607010700040f40100415121120f82e840144a80c1c40c0ca039442640382d02401511201082d01d45103104041ea503500084805000050b00841d01c07130f941d4034401c18035019054142842500e214505180040c000b08000c81038030b401200910080103146d489800e80a040d842020070020180300e440600b0074200300c40c05d064106c0030201140e10465070100c9007400e898801e5141071083c09244501106005422001220781149500b101e002d06081c0f0340a080c558000e004140e0312403026007628811510000d5400796024102c450244550701303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 347458408 1250 347457158 347457163
    0x3061814040f031404030507050111031e09010504050411220b07030c0206041e051f091a07172113020415170a06110403080a0c1e0b0f09 60
    0x31040001809080000402081c0300110b5a94841e101e4900005070304101302039440d140d045500100caa50b040004104115030380701e01e07010a000303d5030024500c1c0121601182c040f0545540d00980400d6011410203402d0380281c054500510000c0c00a01008003044000c2155a002e000040210303001c0c0d804040d144078108403081706a0b0202e10703503203107840e405480688080307403000c1080380e00040c100000319080c103510600b0f000a003000300080c80110308200410689854210341c4142c18901013000c0c016076944031350750f4000c1b40c0e04c001c004542003951005100442c480d0350700141c0f0004c0c00c084e1241540e22128020209030240e020311550518030b0340350116041c0d1050b94200044002840103802500c0d140d4400020029410140c000b0184d4a18507028100104d041d032640c903402c000c40c02014401d15018258400c500200340d0382c80e0904603580d00d0250b000b030304010000c019000502c3c0c0100011807140160030110705200c200307062058503014508ad00d0407100d10350845800d0010900342c0cae000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 347459658 1250 347458408 347458421
    0xd02061b0a1b2301090506090c0a030b06040f020f13050402040f06050d141e010509040305031b0d09060b1906050412080d0e01090b0106080708010e090a12030618 71
    0x56031035044070000760850b035510039041502660081055011030807207002c03c0d02c0c0031840202e2980081800b8009060042c188100140406026001800006130300c2d034540b51100103a070ba000305614400e48814012400401003619004101440021052002091030b809844a0300c004007215201c0740d210014802070b8021841215501ca00d000030038000c1c903000d10090148100041e0001038030202c20b0100e42d00402c01a2084500c01094180d940b4100001611440c09032400750f94546075030405070b8000740340340f20042410100f00d800c000300080f4908200200c0350322001e0000d041c0454003860030148001c004010303109210b5520000c1500729035000b031300d507001102c406495541c1000e1910f2082002c003440d516040710700300c05c1001007044098980c800e481c04504100000580c580c46441d284001d080706802c1070b814400c0e542c08200d074566004001d24159024144042003a071a5801c0c03983c908030400c927008203d11002c2c44c08100c3c20380c0c16032000040740e60412603840c07401c86600582d0100c808 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 347460908 1250 347459658 347459677
    0xc03071e0b0306010c0b07051c0504050d0503190c0f12140109021620030705030f0c01050d0e060f0a0617030d05060d080414010e0603060913020102030c0d02061b 71
    0x1104904010707107168100659801031040c1044040380c00d45540309080344000b01e43c1d80010401c0828035180c40602c51401214450035800104010b0805458550740c9001d00c0e113102d001c000000000031005095001c41400d00c0c02420010f102d0fa00144601a00840c00d2442d424006225284100c1e102c050500130b0030103008010041c94556400e20350b0340000fa501002d00841c2031045c100d03080b4005849103c0c11503220610320150501c2c07902c1c0742c0030541002e030164040c0d48030358401c00c0303d40c1344000041002e0f158032509003081691010f00040e1400a020149a00d60a5000b4a0108500c2083e080d4081344251985141080b450362030b451000064a48a1001c4039a54014880400d006480c0d61046400000084c00c0c511403580b10390300c00e07085a0042e0030064080c00c40009100181d40c0120600040c40003c884c41410740c50407c011807141d00c0010030380c2c0fa81051007220001135900038030403581c03d04540700a80301c10f004022070180d50303081c0540301041c40c2c0c03803d8120040000c000c0c0096402d01003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 347462158 1250 347460908 347460959
    0xf05091c080c030a0810050a230409140105060112051035030c010b030c0d020913231204060c0822060305040308060d110103020a0314090c0307 63
    0x408110090301000320000d41200c1c20401040b030040079290801c041c089a420b9030791003203418504244011441c138a1139201c0c6008500f001000e009c15104448407070340303051206164000350258140054040e0552020161160452403159401184190816841000d007038a072030701c0c00c8460403508011108200e80e1020103c00c1c41d0003e011807400490b003946600c07100d85243d02c0b444405100d02d0030001070081240c1c01c0c0d61000940100603007081c01403031003900b403c4003e40242004080400c00340411504000d206102d9100080e10f0314900ba0403608010750002c1078204800c01040d615041da86500190b0001486203195090030660a00103c0f82503c040381d8a542c2c3c60b00d1595140006038111001b5001c04140902d090030004c031800c0e43c1000202260f13540411517061034180602f00640107008030b800307214080345c850003166444182c01031194085c41d0050791650401821401010715a40c51401d003d18041442440000010401d00c040000c0b0103039881c26a0350100d070303007150304560700c1c90f4501c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 347463408 1250 347462158 347462179
    0xf040b0306310b04020417030a0801080d05090d020301090b150f0a03020f100219120f0305060a170a02091006080105090f0a0c0c05010f0f0506010c021807180e070f0509 74
    0x56405811183e92032002500150410340c07548041c11111603001050800c40e440820401c4080ba80010300398014840315024007000c44612000910b20b100d140341940c000e41030320100e24110744003540481149a00a07005d07804604001010110450403107892b00e00c00c0d4034141d209200d9180c48000001100d6000b010b050b030f01c1c6440380500207001d100c03c0544007540200c0040d4894019448072102c2c0070380c4034464452400c10100409040d07043c82c81900f2042615100c1001959205c000000040d159520b004250354082100344d00d10341941003100940104100c014081d00810b40a20182070b03400300d07220412540e880fa0140108940120f902415079480ca0340420b034403100c1a44603c02c100020b2800a051140a40b0f4044c02c0d00c0c40070318400b081075560017680440081d0740c82070b82d8000301c00b40303005400032200782c000407801c0b41800501391100c0c40f000003242c0203500a20310481401035420b841d082460ba19503240103002c100302c5001c00411402032100c0407047c0b040085a404280c02402e81800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 347464658 1250 347463408 347463499
    0x5040c0503012c010315060608010509280c02010e0706030212010e130b04080d1d0703110d050d0804050106120210110f0f0a0c080604081c020f040b0306 67
    0x100101d030010f030071805058040c01c3c4a003030803018094041c50150520861301e5183e40e00c14812100d50743d000e003040040d03910061140f60359002902e50001da50250302d02662044909075425511806e2080c44107901d06011704001e69010740010f410b50300240140d070340159483c2400d030305a110b24080c4c035480d4001c80b001032001d07200c0f2400d001c1d04000f910310501c01f034004983d101c0240f00f0090740c094071710310b0b03000c10007a4042207030b4003416040700b625280744407025016000096455409000050040750030071850240d9032140c62021000940103000c550140c0e039142409030015a06940540e095403e00700082422415007008020050f07000d0312440550400001c1110381780f1504c1c44c01c03030003070143d41503641147c007080100c4072000c88000301030080c0ca00c903413600b081504945d620045494000c0e100b00004110201c0c00c2e103080700b020300324034074070120346041c000c00030b00c03580f14614121040864049080c01100c1e02451040c1c2041e50008045814152070845590020402d0400c2d51401880f0100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 347465908 1250 347464658 347464679
    0xf01060b160302011b121506020d050a0c0506072106060f120f06030c080c12060105120f01090302030d05130f0314120108010b03120406021209010c05030a030b0a05040c050301 77
    0x10140680300001da6070540700021148816001410b00010314006e00d05d00005445205004c0d000c0714480c4600c610a140c01006521400c00d807103040d041c0800401c2082582d40078443c0c4120483d4020266034641c513200da006801074140020180700c081d00c80700c140840a15074481c14050710020f8a5940780085140001c440c0c0d41c0c504544101410380302d0040780312200f4036001c0d28028500c0351203807241082c200800c07a45070510007108c0900c1048802c0080456000116080741580c1054500c41302d00d0f003c0300c01503440e10501c0c0c6a202c40c1c40d8a80f60204090680c00700190029401e404001d0015840b2040e40c0405001c02744009400341c0c58800e82c89000901480711455800c0c20b1442103400c240301c07a482c40c1101e41c8c090380704c00001c1e5100c4905840c50300d4180140003038902c03e0fa508904060410030300071340d5440c0c08035410001c10700020f44045160300655240c10f003d030b0701904a0340e43d9581484000e000d0300b060103090780182d02c0200c02003035074581405203418461050390f40c0c03425070b03180032070682 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 347467158 1250 347465908 347465947
    0x4061815030305390c090c07030507140708030d06030c0f0510030e0c0d06091109010b1204020d0b070c02011202030702030f030406090209040c030311010506150a09050a060f020f01060b 81
    0x180c0005064001054828103240d50302440d0404c03a024240102c002020b216050b000180a04810003041200c00006a084016280b10941028180e000303c141038070b10518040003070308000664440440d903a400b0310056049030341034901c2090891212913a40c4486030600d442c0c1d008960303029031300103900080303180b0991000e03081100c40b004980780c026114010810070a0f02680c16600a0b4a80605d001071001519a48580401c2512404580d41c980035461005000f90182c800020808101140c150f680c1d05c01342e20b003084c0d0071102035466818101000303418280025412408030b07403040c41010402a0610a40744200b205401641c54044139444144907540010012554140e4a4002101586450031034501c1244a80340003009641541409491003445801d400c140382e05180410887d9158030900d140c0c0d002201c0747d001c0c1c0741e5182c001d080da20200181c0100740c10042e00c2c00c0004045038004070710b6150b03080c01d40954000c50f460144070750070384174a40209400070804010100115010802d0781 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 347468408 1250 347467158 347467207
    0x9040203060102011b03060807080a030f0c060603080d09050d17070f050d06030605011a0415050901030b0d0302010203061507020a050907050c03190f0201090b06060d0b04061815030305 81
    0x391045d040010425070440722a9214002a039540040c4211207040003040060800c800080410001c82d9500500d81408680e040080020949820080010356044900910b611200040d1200314075940b4000800022070250744910400c0a0622118000d0010091154a100001c4080d03981c00106481e60340310603e00c102080401c1042d1030651540703105103c0611f00c2548040b03042d5141201c904440030b240d15038141d40039020030080090b50340940d07035003e89484605045403161640030050f4003c00819071030079000840a15041704242e4194000c43c803407041207500300000480741489420340c1c01031050082d00440590070a0095140c402e0200783d0154580c505145420725200c002070540d0000c2510031140c081c15403504000c0b80d00174081d140000f070144002c00c14038080740c803402c10900d000792803240202c070300040d10324510741140c01a650ac1c1e000507105001295a40d6580d1148040b25843c80d6901490840f2080101c000b0f10b02c5001184d0701075880c1c506005900c0c0030300d500300d42d000441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 347469658 1250 347468408 347468411
    0xb0a020a171513060f0f231518010212090a0b0c0f03070b09071d0f040602040512060a0b040612080306010207170d12060602070303180e0c031602010209060904020306010201 76
    0x2041c0c2d0039a60b8040301d8103128851440468228a40500102c0038030050704a6a6141d850381014040c201d580140d12022030b00440511104101d0b0302d001c0768001c0340f68070081d04416000901c141c030f00c0230000c0b058020200280d003128415604408004528020511074540c4020a50810003c403244800030707200b8101c0c8a8103840b000ca54130395007030b1b20b076500070a03040701c140380303c1410418564424020200108000b00844146d2042c46407001480600100a804000406804103060080a506840c0982400380c481411581094a01a940c01045038100e0005042110304c4130541454003c00003100c0303041e001c2040c07564160303540e841c064100a240c1c030704504c82d0f0b00c4001181ca150a0300b0b007120b8a6484041e042c900b40c0540300800c2c2c5c25140f13401c03a00480c00c20100b045050390000b500d800300d035014030308094405500881c4018800b00c6500800000f4440d030107005001108030010f40c0500140799100c00341c540c60b051309a007070b402240d000b80c1e40040280800d42c01401d09070001c541c0140c05200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 347470908 1250 347469658 347469691
    0x9150c0106091404050d0806010c020108040c0503010203010f05090615030613090813090f05091903030e0f06190603020303070b0606090405010b0d151a070c150c0b0a020a17 76
    0x101c203c3e03100510318880c942443d000c2c4018800140b00300c80012855103003c082d54642840003030005800064001d04200c1d00707400003410300c8000600b210160030020000c2d5500c0d41e40e51010700c03001d4410b006a42c407482e161070120750a8904000c17044035400c580841c05081d541e4007010050706c840031103d184102911000700750000b411140003440e55140c1845040348030f6003040320481c01c03a0040c1b040800b204e80f070725060040712000020500301902c3c51070032009140701c191604401510000c00e840d030452040414141c3c08500100790184030322a0b44d01c0102884c3c80103400d860903503110f1b03c00a505078004204140101740c401030840d512000c0685060300e043c819001160844109070301035441c480d004111001c0b102d5043c0540f059030085079607020391031750030300329062a01e40008280d80180781d00000c8074001c101d40940001d0050417001500c2072a03000380c1e040030703142140c00c0344104e0701400f48d81e0004100c8102842034402015980d510070040c0803001c9100c0d452440b01070720a540d05100c041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 347472158 1250 347470908 347470919
    0x303030b03070b0a031b030209090a110c0a0b061f080106031d0d080a060504020c12090103060e0f010e0a0203010b033106090b0610080a091b03080a02070b09150c0106 73
    0x40c88055402e50b000508210028020140440d01c41b0802d010980100803001d01d07903981c2c0c5626600000c01060000340c040007000c10086c0b910a0f084400100c0c000c08140605028a98610910529041c0c44c1303c54140c0510f90418411400341c0010b03070101d980c0000501c81d80740300380e0009014140001148400384c0c16211a20316180182101d1400142150100820308016008010041070161015400d0003402480c5031740320707100c4041d044411040480c40c4045684650054001000159107503140c0d41070013001c000901c4e800340141294940b071540860124001c9101303c1e030480301c0000c60342d800d50f200d00d000f409a0b903150000c1500340303080c58084d9014610300d00321040601032052400244101e000d00c1d00100d5600300401d160b00c541007000ca031940c50313030f000a4400d50021540c9000070b641c2d41d561a08040001c401d000007000c0e02c001c441c0101c01c2000100041421190340c0d02120300c000d9513404288910302c60300d40141d070065080005041c0c002900d001800d0300d80060303400410342d070f038544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 347473408 1250 347472158 347472179
    0x10020a120e0a0206040905060123070605130804030c090b0102030a14070312020c03040611071401210c0c1e0213151707030213020a0c1e060c090501030e03130303030b0307 75
    0x760443c51066940320180950356800c0340c800381d001072b49546200b044000d0002d441d0f03800d00901c80090041030325000019945c001e00c006005e04079601000d030300d0300c80e505c908141c2100806030088144851401488042940c00007080c0c518901a86c1c1e00e203003418240d1620b80106800400c0d040b020301c182e0303840c2181c0d801700900103440c40c035124034011600c0b580b428030000c1c420040d030107000400f908012028003800f41c20003039404590700c00782020520041c5031280c0c03c01503400922407400c20b078607140d169880d02e5070109045200c5805441250000c11150b00880c00c886542c0400940c0011007450411b44511240c001d1144403e1155101c0d81d12541c03800355014800031258217280d190404142441185040f5111212088c90600300314100003641e50040e2035185591406049040840b0841ca4840320040d4094880713980454180100c5622820190080000e400b03594003007803c0c0120b03080c041100100392045200f041102c40522032071a10142e0091846855060f010701507242e0200d5040400f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 347474658 1250 347473408 347473417
    0x905010e0f0709020421140106030c060e0f10030f060e0c0417120304060b060d140a06060c03120c030b10050409140405030717091201060810020a120e0a0206 69
    0x200016200c0c01c407001e181e09041c88940d0300800c0c40203106200501443c0004081c0c110b41505140c10141c0e01425401c14807007410a81000880035030070407102008018000c5003a60480310f41c3d449032408002c0400402043c40c298084403070b046011580c14001c0036120350489410502c1c40e4a00144c8940c44050f01000c072002214a014143c200040c10460040c00b11014001c04010001070041c9042c40b10900321070344400b4001a200ea5115401101550703502401ca815a401c081c0d01000080031741c0414420f6004c08803a020203031840d11a0014000d4010181c180074a541941c03110703480b00f0800b0000c0000c110b034000a01c10103603030b02040071442c0c42d40f04400d201142c880d203a00d91079511301440300060300c14421118200c0c200e14424440092000003e80c0d400c5544600110035111030003141b580c03240140c61151781d04c100e00c4a118514140103501410550741a0030990b11601401103055050344143e04c000000621040c0080903981010f50258500c500e490f000d480b545003860300021002e401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 347475908 1250 347474658 347474681
    0xb1c0501020318010b010206040f050111041701060503010209011403100f03051f0b09070c11130e060604061d0403021908031f0308040b0a09080106060503040506130510020904090501 80
    0x600005100d5070f00b803112004811031801074020301c040306034040003d40313130000034000400300070101c80d2110400c5400c1d044619505a4030b1001d589131569040c000c2c4070360990104604a03540380a00114540c20107000300d40251034180c50344c00d40d0640114100c10305510040c2202e242c006031410101c2c180c3c0b0007124410007540514002c1150350204030303141301d06590303161481c0303a06464078450384141d40b107406205074000c0c2582020301d0101e00c0e80c01d145680400ca0381c80241d100ca480a260450b421080e4011440d68410108640301c5a460b4001d110403600640a0f0401610400c4089500c1c00030313a440d4103900c01e1191050764210f0a024801c080f07000c440b800100c50f01c1c0c0004c000c10007402c0d0749508070030003075040d5401c00c1040c03440c5072a014040d10a9025070064a50005a8050341e940203001c950010617103c07000300007069070783c00e004001d9041500c00301e906004030400300d401000149003542050742c00c40090444c0c000c05c040c0d004029070103002595041070b01c0c0c00c0c0c84004608284901c0c0803407403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 347477158 1250 347475908 347475911
    0x3160303060806011e0f080d03050a02090a0609090608030f070f050a08030c120a0b0d1b08030f03012612160212010b0405090d0c060e0705030a060b031009080703030b1c0501 76
    0x79004010405c10001e41d4012441c1041001010041910001542d40028040d4100000c517503c9200500f006481910400c5c2e80180d5820700004d08c40307602a00210032100c014400b000300c5500c0f600c5403034a0f4400c0500b18880081e09000c00000310788042a100070346403040048a001c51443d503201c12064201b1640c0c8401b540000c09e4030360b40b0705880b0b091564040000d040421501c1011000541c00340700105000e031014a21030004a041d8251401400c0a001c10200716911440b842a40055a034003d01460485c0b140070089034240d114060b44580600f80a4005020b8155620784004420703003051340d66243c0e801f0244c03d10005604c0c2c0041d11600035007071350000308046003040103000988801401c003003000c0c0c0c84500c10540d4182d00c4442142680c1d440718010654800001d801407a1000e944c216a515018007140481003110503070290000c00740907402d81e4a00e44001c0c403a0b00468049000c0600b01e640100f140800280c0f00781d01510b01d12100030072030b811031084000080000d0800440440f62603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 347478408 1250 347477158 347477189
    0x70201090905040515040c12080c0d110304060804052b110c13050901020d15090509060c03070509030703120504090f0501030206071202030705150609060406080316030306080601 78
    0x55034403041600103008442001d1001c3c1c01c055aa0550305c901e6081e990040e03403210400b2030100701003000508010b194090140c0403081d51404c0c9491950301c08425002140b0401c0d1070403482d103028100019000d08000055828585010300030fa41d4000c00401c119114012019061080120358841c0c008902040c000198401c480c02d0010305007040c0c0d080705a003154407840c3d08110f01e03610f03040240388505102c1008203040d01e51440c454060300809c0c2c469010282403200c030300c0361070303402c0c607034150440700c10000600c05501c5c4c01c5003858803610252100c03005144100005124507000307a00510500394081c0440381c40e039690f501c5001e80c009840d1582c02c00a48001010048240c10b030041c00590170499501b080385514603400501c5038403440c0d200411030f81980200c8502e442c02407054401c90394114040e110304d0402c4108000e00d55008840040c0f149600c90003041050030301d8400e600680e200400214a8506400e400035454400c928040341056143c00002c80c402005210880c001c00b01c00e0400c00e0b89 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 347479658 1250 347478408 347478413
    0x3030f12090308010329060f0109030507090902031605030a020405130b0406022d0910090e010801141302101d0a080319050a0206011206020423041b170601030e1207 72
    0xc0080921a6021b003083e0f242e101400c950302c0602c036034101d982214481450f858400050300c1030319290781702909601030010005000c0e0540d800031004a4422000d544000402c0d04000c0c9242d2031034092690140d025540d91001401c00740c3c0900d800561044019428404c0c07551408182c42084038101e07074a035000f00340d1010b002100b0015810480d1140d140e070740c03480e1500c100c290850203142c064901c103900c0ca140880d40a40145070f140007910407c2c0381f031074041da12130300c2c101e000c0c20f6610422001d040103000020500014051300845699000380f2414404110b200119200700c030356003844013040504c01d009015035032581200340c000c2c01b03443c1c003540d01c032030305540c405214206814107001484800c001e403203483ca60103e05207064540c8219000780c85001c500b40031009008580103007650b070039110407140d01041c0125000191260841e01882401c07166580704403019448144000854841e0500c01801400d400e14598014010324001270048202907000745010040011210320060000ea010107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 347480908 1250 347479658 347479673
    0x361a030a110c01021902010b01140304022b120e01080105090a0e030c150907050f030a1202010605060d020c0601060302091c02040b04062402060f0f070e041b030e060c030103030f120903080103 84
    0x10480424206005242c0713600044ad000c1d444020802031040c81c0c01138245150340c48a201801c400e40942c5687d000004c20340c5400002c10840030013010204020260a2802d0344c4980d00941c1a90387c040c010112076111040040094500203801054600003030109805200c806c000035101445006c400c40040d00b01000c0403800d2401c10341250313000740008001072519480001d99104e029901940720140030106450803401040e007030b001694400000100040140000c0c1c0150422070000c1c400e031446a66201c00075002c034070a4000090300146141e00300c0c1040269159107034041c0703002910104a0315003001c0041d044501503000106100262544400c3c00e85d8800303441000e80f903490004001d142400d00503401d42043c01041441d0700c5500c400001c400511448141d1030780c102c0034000744030f485661100b41400d45081a082d0300040c1c90201803001d40c460005000d40940c4000c401e862541c1d00b551000c69403055a000d8480510002c500b00c0b000525003441001501c41c0a035560b0100c40d4110b240000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 347482014 1106 347480908 347480921
    0x603080301090212090604020114090411030c07033c020309040c0203030114011409040b120303010905010303080a0203070915361a030a110c0102190201 67
    0x410b280180c01078254809030100c01c03c03a503504c2c86034240d95840e00b100d01a000400746090111080000d074020480240007074004540d005802081c0c05040d4410354070240607080c001404d8043c15404040c211030144455600e03002c4170368074008a004800641903000350103d0028440d60464003c10440740001e0016103303000020f81000069100d420034469441d10514100e120746240d81315003220701446101014140c200710004041c4801004610180c0750080400e02e61840c0f010010000380d402000c0c02c09005c2215811898001c1c44110702410040c04213006101b886a10740e00f06026005403181305c003180c14000039041c0120352041c0c0b4240480b90f01403801c03080c4008030719550314100145030300031080c1c08855500d2141154071000c20b116840340090900c0402d03802d00068001d03a514800702484141042d4103166241c0c2281e0050700c00d0700202044401c8010f0752902030141c40f = true := by decide +kernel

theorem cover : BRFrame.Cov 347302158 347482014 := by
  have h0 := BRFrame.cov_init 347302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 347302158 ≤ n) (h2 : n < 347482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
