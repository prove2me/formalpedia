-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0401
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:37:24.599753+00:00
-- url     : https://prove2.me/submissions/9304fce2-dc95-434d-868b-b86e77ccfe81

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 71942448 ≤ n < 72122304 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 71943698 1250 71942448 71942473
    0x3040b060303040605041806090c0e041103011203030e0715111219050915040f03051603050a141009060614040c09050d05150a05190204080a0305071103010608 70
    0x801400500c0305110764070401040c82901d5110044d54101d4041e5940300c040840b07000c10071400751035250051000c1c149004100e0480ba0f41c0030048080707208003990f04001082d40d070840210385100901030111078001416103400000d01c2588010700c01100c03201941c00301d5854400b46008010306205c010700041001d0032012020710140003200380790f04034501d9146401c0740b81444810300c4101d401c40b2010710402042c143c21a41341c0003182500302041194207683c60b034507000001c4041307510b4003042e602803003070300c2c0142041100c800221040c1c036000002061141260b69903010507500e000f60318411406540307044442150a4040d803010700d440f0f540d0100d02c40b4140004250003c9095085602c1581441364644080e070b002030320782d4161070b011745c0d10079400d1038107041003032030100e02400c0912005584020800c1031980c99204d01d0040b018810b40b00316101030240c20000340c0c0210700407001103070400900c403400640104002e103085c52158500c038503000d2113100002e0031602a46e004c0981c3da000754039007406 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 71944948 1250 71943698 71943713
    0x4030314040303090501081302030a05010509010b03010e0a0605042402090906040b01080f07090b0d05090606090708010e100506070b041203092003010b0303130323061b0d02070501020304 82
    0x1403085844000e4101850b64500800d501407030711801c1d040c880c06501194040d6040c101903c00ea03a001340803030b58009410702d8294001e03c800c582d0440c031946820b83c080603916060042ca00c039469254001c3c0080d060035150b40009010260003180c10b4413084100610303c0c1c01030014640911401400182c03640404000d000201000030100c6100c0d030b2405c400c1460f2030380c0102c40c6135045649440f00741403a131745044c402d0b1140c180c6600207080528020401d60079814194001600c900621015611192290800d2028009042c1c42c0c3d00c010403907600050181030402e13689180d014014802ea000c1a550740c9020074040c6d442464281c49201d0168200818007504e0054100700889500d42000081c1d80b9880b4160224842a44080180401e40018503a5039094000b0000c01000400384c3e940c1e90700b40c071540300b804031280c032045401c0d8451240308032180e10f2185100b580c4800c00b102910080e9107c24032000c1000754072703a404881c00308c14020118041801c0c40908203242c41a4001a030341d0a00d03041000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 71946198 1250 71944948 71944967
    0x12020a051605031306110d0f090503070e10240507060b090408071b0503030409020d0207060501230d0c15020f0d11060c09030c06030a09020402070f031806020601061b0b0c040303 78
    0x800380101c4c404007001091002039107d84040c00c07132402640000d01150104e40b40800c40d80441c1c0d051203424800314001040302040c0e4014a41408540480c6a0b20307108581210114110840098152076801c0b00417400f0342c004206261080400265021018000401400f416182035a008401080380010890620803180a0b0444030803070241040c03034000066038a00caa406643e0b032280c1c001c1075403004200c0d01c2d01580c0b41550700c00d0050280b90307158403042a64510391841c04202c06240d805610003410880300784100182c000c0c20406080341050b4600300c0000302544002d04503c036400c036091000c5030600075003055018698407052015082c003221450060301424654000408120740c41c01c690307002914514030380c03003511072039125034580e14440c00410301d00d10080d42050000072210100b15000c031036000654480e455401c9107000303c00560400f441d05006803805039001c04014040c0900442c0b901d4050041c0b0070703080314610f034140e8680307500e0034080d191100005400b08081c0105504400000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 71947448 1250 71946198 71946209
    0x30103030509120c0a05040c021504030302090a1406031303110d02100b01020f0a060b010207080714010f0c050705060306040213090504030e01110d0f0c0f0b0712090312020a0516050313 81
    0x42c4213a60b400310004071400502d100f11132056a649079200d025600a00151040414840d0340d0051483e043c01c028000e0360060281a103c1c114656000c9a46940401c0e901c0c100f4001806160540c1d407044e082c00e141e02c3e00c013401541400503011780c11082220070083d607541007c80d9030203401043c600c41c074600c0c166402d480703020f410b540000d03103944610030700010022a115080103020070300ca01c0c82c400607400c0c041c8a80003e10343d030203413400220713401a2420581900c030700c00380d8a00e29070840262013100e0841905c10010016000030608224514210380590f030050b0000b0070043c40c285920455075034524913a441207401301c1d1540c040205064104401160081003802e081001c0c2c2412220076440c0c48090052500b8000e44420403d040340c03050602061a40c2c0c01501d00309903003000c0c102544600c400300c031002c0010329140c0e11041c90440c140183c1c11a1640b54490b525951088040d950180d00500655030801c202404050a440a21816400700da4000c07005540d881d08180c0c1c03501c640c0b03003035034020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 71948698 1250 71947448 71947453
    0xa06050a060914040b041b05070c090504050a0303051513060e010504021303170706050705090a050109050a030b130c06200c010905010c020a240207050a05060403030c060e0303010303050912 83
    0x100001c610003ca02640c4140440740040c185181000040c000d0103042c990b0782c44a104400c40f000203580103c002c00b00700c1d0182103482ca0442d035580c1c0070302c144c440c100d80060864021006020009001e60080c60f041790040320340040254507a00450482ea046003403c80000d6140d240800010800441d1507002d003030143c909518001e04030101040000a920000f45007a4002c1d00000007180c01100782c608140d481030061100d42080e0b1801045900b1102259207e1103560038005041d6024410000c21240b01801039000d151440d190705031800d000610b0103d010008c0c4425800140b608507000c0c01804c0d0b2038541413241085803c030a159140c0384049151030380d1101d0302000e21a1380007207045003258424a000551141c140c40401d0044000740c0c0300865500c180312031501c410800309040800c030803480c1d00303d54a140d40c070410015030b040b4030b12526400110400040c40803038400c2c01401101070080202080c0030422003601c1e861139009a205400050010407816030a260103844071140c0b100c803e00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 71949948 1250 71948698 71948717
    0x20a080109020904080a02031608121320120f030310060c0b04120c060507021e060408041202150406020304050109080f0606091306050c220b0a0507030908060a06050a06 74
    0x119101d60f0024001074017444021071a680c0641c820002c6591070311214000000c00b100c40d01c0c2040313454001c130303100030b10410061000520102424100a000640040452030305603110707492a04082420820117070440030a444514000380b0800c9020443c0030302d240110f54a141400e40e4481007000d5800210411259141c40408a00e04071001500b190f00200c4100410b2500501038545100d100e500800399400c3c10204015240c0204581c5022802c201a5255901d405241540c680030125002010001e0511041c414080313004d0450014900c0501801200d4a0201e00c8200311340056200b400140d100290610039560b000d80180020f00740f820040060241c9070090503150580140700c01d00400400b00066510407503030f15425602d980280c401c1085003000385c11800c0c160320048a8031600c5a4400118900c1031a17503882c14101c03140040554205040e0a42c107c8442e442031300203408028568a02081580b0103120484c02420b40c543d0014001d0b00e09010710219440d107900031000d11080381d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 71951198 1250 71949948 71949953
    0xa08030c0d0b010807170c040905181902030618030f040b03060f0a0303172208070615030f0f0201020a12030903110106120201140409060305060708090c01090324020a030603020a080109 81
    0x8880c1201c2c0b0b85030141c2c1a95552681f00780003d002e260710416103141024244040301104244c1a03108501040036201c80c0b0301c070881c00c00d40c00b07088807000a4150384403600180d03440700c14100e0400e0064441080ea481c0000e141d0155009800640080624280000501c14546010010b07035000c00402d440c0082c40701d25680b800b034060050751030300350003001c00000003611902040d1840034103da440501c943d180e4030750b420001101d810540044510b60702c1e010358901507554004201040780c1e882248207034031088a070f950314460a51458100d05504c1190f400c5c0000074855030700b00c0742c1c0b00090342c0d0000300fa0085040042214002c4548841e0700e0b450080c05003c40405a603c1d0780d08a9020308200e0048805072500c80c4051085610101d00d6a00e440c03004001c0001c0800d2031030080d03541c0ea5030304403681c90b0b140519445484201034140411240942040001e035003403000e19186941e00800d682e40fa01844000083e0b92048001400103651803100b03100310700c0c01000311005404107070020003410740d1a5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 71952448 1250 71951198 71951207
    0x31c14060d03030b0310060902090405060a0e010302010c0302010b13051e151212070303061707050a050f0607020a0b0d060e0609040609052503020a0803031303030b030a08030c0d0b010807 82
    0x400c0041e0426444d000c4100440c1c80130006e0381202034684908201c0b055a4407560002908013001d524807803800c203c041201841d00100c49004c1d40c00513160140c05900e9a8019244502a07860441c159500e483da07a9080c0c0d540d103c0c00f0000aa050b03440403d075031422415a11a4001d116406a4116801e40510a0011040c010000d00600c203a034003103e030382c0da400754203890a0381c5a840081c02c1400010081d00305503042d00003104861046c148030f1200701100d040305840b982d450243c03170341110142004100c00c0c50280d1042c0d00058010780b50303514080302130700895207034a947d03004034442e8000004c10881c41c0703000e84105001825480c2903103089061050001d040c1a0010b08013030300140c0c580307a4590620205100d044690b51303038452689507a07140700b520003900003410710090307115240746540080c1102c1c0100890317105980c640543c000c0e511030b56038103500a11508100d240c040c45080d07401000601280002d6000c0c003541d02d081c1d511489490a180c060300e11481150381003018860500001a800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 71953698 1250 71952448 71952469
    0x60612060f092109030c0816060212190903060e0a0510090302060c0904060807060207080d05070302030a0804110a0b19020d090b070611072006132303031c1406 70
    0x20f0000c4880d0f00e030b000400719054100d0f504042c3c80e00710348140001304070000103580b503449484e0980115950f40da4441c280d80310030030b50041d00503460080240c00590418aa0000619034060a01c0421103031039403119821184542014003080c0c0c04215410140101000542e040441c3d200080c0400c1e2000d640094403694054001b8030050800700e400d06c078581c1c454102c00e020700051011110441c0d65444020760b641280c1c0f0803848280100c1c113456245a118204840c00c4e5a01500107503d40b41240008a561990042c010f8984841c00381d40d1020070303075032912964001c12000740200d80f5402c5062443c003100155840210542d480094081401a04000004200d0351441803139500d40c203850503c0780142c0020000303003a00781c40c0007502070104039007244515031245607802001d007150108001c1c0305851042015100ca1205945000c101103080e00c5c001440300c11801140882c40e1100d13070042850f54001c8011070210b400d254844c0c294020492040250000642140e54410b0400d240030600d4031a5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 71954948 1250 71953698 71953733
    0x120e0a0905090a080f220609080102070c050118080106090b0414040b0c0a0c020301060e01080114070503011401020c04021810030504030e0603070c0b2502010501050303090603060d060612060f09 85
    0x803d049620082c05d406031101c0b02058130001c0e1010b03d203020a801200024000c610200d0280440030801140510940e0b01150b4000b40c0f002445013070400642c1c0c804c0e82014a0203091107a144c3c04594200700780501001808000b070302090601210040006a441d00300040301d5882d1900100008242181007182e0404503029010b0754444a41a00700c61103c540c6502a40540c206040042d02103100e082c250b040390b0030b01c4000c001040c402c90841429110980c0d610000960a01c018480640c0310005036010030300c140110344110480e41d02044c103070b800078120003034555800240c04100f400c009240d0f100300700c801c0c0b80400c1107181c6558007514800a07010034601540c40440010801405900718290841c1c020107081498540103800d10b00302080700c1d51a82e50045a88218800f03d4014040d15050355801006141400d40b01406e02046030070042100d540050941c081c0310200d02c1a1043c0006040c202c0d00b0700701307070090340c0c03c011098540e40340e1459041483e01c014680495103030380b550b980200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 71956198 1250 71954948 71954963
    0x30f040605070c08060408030a05070e1e01030207060e010b0118080304061206170a03030c0c050717120c03041a030114090711010f09020907050a080114030a120e0a0905090a 76
    0x3840c1004600307100ca80d0444c911a100d020144400d20860b42c0245206080b005000d010568600c2c40848440c406000101d4000039441c000e0406401900d503012003016040c0360060a00140da1104425a000d001599446940d29401000107503804034200400c0b06101e42d00518491602c1d20040e03072481548100c8040200f0360926502c0c0e40c0f15a0000f50040901446200e06000350103011921002d0f04d4000701e021a02d0b0624001d207440c011114080f000c0e0304503000e042030a14110703203a003880000000701d140d030703001c1c00004110728001a406407001d1105280210b072603600b08481d04281151908142121400c14401000030b000b60800700244844161140b4031f8a449006082c0c504524400ca520400e500f0f0413400c0d050100160b10030305440c0c0c000c9500524030388408606a60500c145008540040c0a80005000000ca50b1540e0a5420405030849900303040c21740b608003042048000c0440000c103140809d0042d450f007400d10341c0c082c050300758080090b0300306010b041c2d6a030a0704090081510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 71957448 1250 71956198 71956207
    0x90612090203071a0a230405040e03070501050711060a110405040e010b03060106030902190501270803030f01081e03041203021006080a020a2117160501020a02070602030f040605 78
    0x1500e0a110b4040204084e9181300b1003e149080c40c00b641c3d4000401e03540016202c3c40c86041d10095041498030302801640003149418181410322011b00003c42c3d54980920040003001d00044091280610401c40ca50342c000d8650120540542000000390070700c4100e500306070a80604101813421641107e100300d80000395111550102e9000d0075800401e00d42c5401440000664181c2581042134000d100320380565070000c6140c110a00e400c254004c650001d107004883ba00c0c0d00c03840500c20070700c4030b080d60107102c0825035944140b861036204030f6442c880e02010310010400035004002e5926034044c801c80c600c010141400303141d65039010324803038501003020201020080c14000d00ca0187c03003416940e014005103898881040c0c0d5040c0404040f0300550003403070b002170040401030b46810003620ba0495403144099948032850751015a01170a0b48100c403c20080c1a0140d01d0000e45a01e00d201d14000b5840e02c05c90440603080258990013074042d500108014542110715008840aa500904010781c59 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 71958698 1250 71957448 71957453
    0xa110706080f06032409010c0c15020313061e050105041b0311121617070c0b0612060a060905010803040b040b1608071407050d050303130809130504021009061209 71
    0x10700504c80d14044800049030054940c000590045d18819080d0174000d010001c540c1808582480d1002d50103442d607440d15402031024030940d0002e5820072080c0e0208100e4030400d84030300040b80e9100c221300804641e800078040308409107002d094014441210704109810b642080311900c110307000315000c01c065403042c0b40a1880c103c030301550700400040151007040c2c42d02131041e88002d20b6892104012039600d04034010342414030320700f00d403085116a4030b03c802d940c0d00d941d0b0008003080c00740c5804d41c8007004643c40a19054100400b600c9800c2c03050010508500e1310320312000300e40781070300040f10640082006120b90b00000e0111403c68690321405560381c40d182e9149101e03c003002d080217090220008119041c00030403150302d604038110400352084590740d0020000000047c4070f00a100b90400e04c00501c248180c01145c1400724021000f140c904140300c8002100700c4c0d1440002810a03941e4004e110540c2440145040c81c10f000d410b1050465042c003071701030001107070907250000300c0d610380010504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 71959948 1250 71958698 71958703
    0x50c030105180718030311151605160831080a0201050702030c03030708130501180303030e0109080f0d051e01170715051b150604090201030905030706020a110706080f0603 75
    0x40c2e07a13200102d030300030054484c9002000100d051540c9201441541200f28042e000c2c042018040c0c04001c00000d400c0700110415103031500005201000032492120b00004121440003c008410001649072429000c201211409080c810070340c40c1c9622081205100000000032030111141d02402d00ca5240c0c0c84610000389403407201a2429018000441d060701000a00f0000d8072103049851000c580d0300c0c0d110340044620180c8030341c040c4800b2001850410100303000b9480319801f804040c00106240c0301940741c42c2e42aa00000e14500c05d004000380d08001440c15225064002c0051b008002100c00021502c01c40c003641802741c45881e1059060a201001003004038cc00141447d8171144135042c200a0003801c0b94104240c02680c00fa640000c12081a8011800c0740881c15640c507046000c0c1c54040c00e0100034006204200d043c1552102d003000450010009840c425203c1c2c00c4c05a501c1103040130080c40d030400c0aa0070b8046a01100e410b000c0c1a40164005902001040c04181190303aa100000d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 71961198 1250 71959948 71959967
    0xf0507050a0f0303021b0c060a0c060b040e0705010e0a030206030a050c1c06030228030308060f03030c060108070e090a12031112061207060813060608030d0b04050c0301051807 77
    0x2c01d10165000e09008041e099000340001c6409481c00f00746401e4451601c0762115451a003250748000700300400d40d03585015009003803c0e60b000c0c080020b003543d90344020030115200a006410207620500c010042e80d07920921700da490840c00d68034044101d1540c0c1c085500c1d4000a00a101483d440350300040711a26410203403a100c2c4059521103440c002200e0450004010724082070b40100c412500000c4000740030500d0124102803402c14252540c51518211903e43d00940002ea000c011020a511175540420181c42000001d20281040b540752500152611210341c5c444c1e50701400703a6081028440d00404d0820649400c00c10b06002c15544001c02c80007049030351b4001062b06400300b0901020072014206a209080c01d0300e0840d035520380f0081899a9211500c218000151844001814964180b41c4901c00c540b00d40b00114000f074840000700c1c1140c00c034284010316941c0c0c6503040d40b00c519060007160b0b042040c13100385600c0d5504000204000081001e41c0b4042c4504607000b00300e00921070440007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 71962448 1250 71961198 71961203
    0x30601080c090a0e0c3303090607030b0406080a0605010e07180e0a020706060e07020105070311041e08010615090609230d02030d051206090f01060c080f0a0c020102100501060f0507050a 81
    0x50749441e075003100d0b0403003210742c264611b901a110200f004a144414104a1b0300880d0b4036801040300369143c04045024100d02c110a07504a80c44600011700044100400fa56540c4a2000820f40758148841e200c0c11a000600780c9080000700c55140040350030142c11101500c0005c0d1503100160349207181769000e80f140d424001c3c00249807110004403400f0303445032540130349155402030000e911814400c60036546074020f184044c1c1e508010800400c4003180300b046802c41428010140143e0302c4c5003841c04c40301381d6406003e110101c0010303400e01c00d52003182c81000d0318440c00c14682d1a410510285103050300c1440741c01c101e1a90b0102c00d83d060340c0f0041c00628481e401001c0300c01d0061003c00061913600f201e400f01f2421000756010500380d10b050750809216010800c000040e40e803811360212581c003200700d01038400c41410802d2001b0f5100d898014802c031502503d9203241070180303200080c900480c0d0745040401c1440c003c0107120380d55003e02c6071a00b50005207482c40e200d0986080190500b01c8183c0300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 71963698 1250 71962448 71962459
    0x11030412090527090a0309120309030605180d080c0307031e0c0918060b120705070b09210a0e13020d0e070e0906040b01060c0f1b05030601080c090a0e0c 67
    0x401e07508043d849003000b00509034002c0040d0b95203d0401e55a690f0b119018000d0108070f5000303051080581c62114451f0b00d900a00d401c0309000d0396621800d00711941950421131303210050065143c1141d08004142112901d032400c204585000b100b20110f80c00003514041c02c254654140040810708003800845000541c0003c20401036500070180480316144510260380d035681125950500743c0e80315401c21101da64522a1429815002030079400318001c000000340700040c848031020402d0220341c60b03c2910035000800944007100f21502c1c101940e006004041502040400c04099004111210036401540e0a82d40203076800303401c60180c0a03440030800107130701d8a40304885400e0005046821181c209412214030b45415800c01e8482004070703000362401f940c50004000651140d54000241ca0203100c180c6680180da03034a519030801640c0f4030b00c0c03507140c1c901024400745c5420300c8001c2c01441308a0017000001c10b0307180400e000030402010001780303c0d0b90f0300c0c0d058007910007070004000c0b86200414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 71964948 1250 71963698 71963719
    0x31e0601030912030c031512021c0c090506031b2103190203030a0605030706270f06020c09060307140d060f02030f09070504050606041806090f0e060a110304120905 72
    0x1030003002001e1a05d00c2c0000039061450704859851610000010344009011600341d070403081d001d01600c0d00c081c44005810304801034540700030400c2c450300340b80a03045900c00801c05041040c201840c0614074020004103040c0000c0b1911030395191604a603070080ad01c080750500d0a206410076007980251884400c0031b40c1143c190149140d03020000f18030a82d401c140c1000343c180c40300c050640e503075103e00404000ca0b1007030b4010840102c1c015800c030380500165031108890303038941c10701c0275000010368403110159201d600841010b1500e100c03101e502400c2030f07005011007480c0260b4142c6182c0401d01c1240100e1506071403c06000d0a0b8020210510ba00d0105550724103180c880c4c00342040c0102c542e4100c40c00b403480d011407189070501986004041c02000a0309040c01c01011940f107400d4084011103040d9500f90000c1c000c0903074002c92844a0004c05d0000d580440c9251950070568000d1880b100c0c10b142c0701c10400700388102401e803a045038003c4c071007040e1841c0140e8240c82100d156046254000143d11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 71966198 1250 71964948 71964983
    0x20d150c090603110705071e0f03060b0907030e100207050109020a0e060306091203060f0f3001150303050309030408011104030314090d021c060f060f050303031e06010309 75
    0x520008441c0650780130802a02c040701002c1441c0100c25000300b103504550800c1011001e0f00c5081c40010b07c1c050480110396646984d1840100b2807a40b007110a951100840d09580c90b1003060f856000307010b400d05101207080400010f48604500a000307120a034081a21020310070300354446a072036640034002c040d01c41d4840d140007191070002c076002c9120b441158000340c001d100c0455240a00c44c000d1101d0b50460319104104119246440700c0f4a0700400f017000b006085643d950128451481c0d41102d441c4400e801c01c040509080303030000a40002ea05214402031a440c00c00f108a08594052404586989940150500b14856903005051300d600f0031440d010003184d14070050003120700ca40c44180320218000d248001350b008208810380e210001c24aa40d01508041d000caa012100382c20a0306044d041507a920400c4518100c00c54401e40d17501c20b001e100040e10401d040020300b000320010760951810034034a0003c4881c54030044d0114001c04040346040e4001d0300440c1490f030b4809400b64031040e001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 71967448 1250 71966198 71966207
    0x307030906111b0d0507020d031101091a0c0a05120705070b090304062c1306090c091d0603100209030102070204020d0506090106091503020705030d0203070f020c060306010903020d150c 81
    0x14009018034946110300f9010203400014580c0361502c0c261501e9003819001c2c0c00308044505144029000e0148011042e08000402e00c140103a00d841000c100c560585019a49544400001c1c1042d0442a04109100c802a00301051b1200c00300600d444140035610302004640340e000c1c05000500d0000c4003024003c00f4407010003d401079403490ba031000c41217820800c01d0071813140c0d80d0305030402c0c2c0301c0b80103c01c0c8618140103a203405410841c1002091080e078070380403034048485903032400002a001030300500c03601601d28071444038901410a084403a05200c80001d4840a561040881030355000408514a0320300390140c95000d900284219280d1084009500c080c3c00d0460302944100358140000ca8841d00500310302003980c0c80580404503292440109070004d610020003901c65100030300031080600707098001107100f140c0c01d580d0b8003030103484e0100c00707450000428401482103500303000b0090302e43d03801500b01040700e404403a01d6680d4802801c008880002405449907114104042800d80d65080b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 71968698 1250 71967448 71967457
    0x30b091603051506091e06031213031b0305030306120c090a0209040f06080c0d050c0d030509100201020a121d06010303091403060f040204020705070806040302010f06050d0c0b030703090611 83
    0xa030355501156109410440c5c0400d0455900100c0d2510315001d040303403098021050f03844080901254021050203003102c280780c010301502c01400001c0f250510030410302030170520150740030502044201c1d0640d0b444a8a074000280b400307014000a0300301d2400514104402c004005001d40000882d050481441010351f02c08a087d0340550700700414401c0d84452842020100c0e0058005000384040034410000742078048003095844d4820f02c00ca0706416550704001c2c079041440b80d142c00c3e540d10304c5103050264003003403155040706591051000400e00d640210100120380704010300081c19035802e141c2c0121140a50b5a422814490000007208143c1c0110309802658040203c51922403000003c00d607031044203c40c0c81248a050300046001400d184c3c0161130003a2043d4280c951081c5c07524180c629202d011241500140e450b050300d4680a01640309041c040c02e4241e610074580481601c8125805105202d0701000103000000202d40c9882540a10107039503004405001001c20307000100c030103400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 71969948 1250 71968698 71968723
    0xf0a030501090c021f1a03030f09010f020f0d08060103020c0f0d030609020906070803040c0e130b06040e0307150b04090602070203010501080304051c08091201020a0905090907030b09160305 83
    0xd0881c3c08440c060002800390350304801d103240b00714900c105004580107400000b05000140340c151044c003010741d406102401403644180829600d13401800c000501c0300c00940c0d50300c403d641241c1b24100000030081850300001c903541c101160389465080c0120000d1180d840d2068a0340540c42032900080310100307000c00e010303500380c0e0706000300340d03c1c0d0510b1001c0b442549101c99000c9020883d1000140c0c04e8070145a100e40102c1041c0c24140d40c03641c02100000c1e013150b03d1000490310f0341c2c12104000011b5105034111405075001c02c02e2800d10011190380b4881c1000c09041000401001110010150819006404050000d00005002d803074003001a400000d8102d1107075003054004110440008150340c2166001061501d090b0390300c215484003800804000d0325644010000000303d5107611182c425070400500006036a2810b200008040d5200740d000b242c499513940c4d0500250110004111041d20f07007026066680e910f42c3e4403e145012a00c506484100d030301d80c02c000080c02401b1031103113403910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 71971198 1250 71969948 71969951
    0xe060307080f0610090e09030c010c08010f0b0a2106090c021005090303090703081602030d05040302040f0905030a0f021504030203040608010b030105060a14160b07030e060903030601140f0a03050109 87
    0x1180c10b410804025007504d603160025844110402c4030345404050340e40c10081140903207151040c8840c1990940f0000300d918004943c0d480c00412441c600d004503c8020142d84e8007140c02c1034001c200c010103240745076491001040a841e0500c114558a0307000100405801c24200541c03150144d019407030b0785807014840b4001e03241c540000e48403800401100d10504e41000944400b80c02c50b0b643c108190030050200550801710740c040d60050318104031310340c0811100d845083d20b80c0d00d18810003050b1240310b0170340d4040e03a00345814000054000801da0b5540229410040500c00c4895000c038030340540501404da180c00c2c41000e2005240d0040028401e50b005a520410983c0c1c035402c2440180c4403e103e060780124007008082c1d1503034810b603031802050703a107d02042c0c540000445407521200c003070002600c52072803010902441980612444841151440103000d0503e4460000b640740d000040141e8140000040203128485000084940c4007011000e03940d22019056001402040c09016444015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 71972448 1250 71971198 71971201
    0x60a1a030a02030607050c030d0e010621030903080c0a0206040308030402030105071b0201050f0c0a03030b03010506040c0c02040203060a120305030a0b06040b1c020409020703030e07090b0a090c0e060307080f 91
    0x28140841c0032100341d50098010b062989420f90201c996034810442c0305010b000a10a801100b1310300c0c02a44042c0004100200340c0c241058220320300c45410340d080340e50200301052100006600150036500700c1e0b421450b003944404440e424182880b521040095101c01e000801104201d0720401450256000b0790007002195100790064554009404011403820310100d04000198414802030a15600c91084242894402c0301007a00e40420325604a0100342c641d40d000070300b8103092051650020081f82d040c0011610038070060400c0101c498003900883c0c0001c0003480300e03150280040b00800764003801c092400b9507824014030035041175800070440e9042a4000401d49414406c0c0c4040d01c4d6200c1036203180000662075540300c030b010040301903802c640030f100015800e0316910240100e240243c90108500310000d441600386036070303600804c008d9888c14440180948508044800343d031340e8001d000039103203440b450a80e0946408030510364004000010808034a030b010b420315008204401c0703694202d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 71973698 1250 71972448 71972501
    0xa0509070f0b0a020307020907021011040b0406450b040308030a02030604060f080106030605010e070203271909360305090a0306021b0f03070f03030e060a 68
    0x84503418032822500150400041c00581c03422401031000715454011a40b4001c250f0303020403003a40c3c0c210741007409a0811880ca50740807226004d80d601c1c081c44102000c0c5400e050142d0751400d0b0156020782420845070441041800c41031902074140f03108403081550400504184090111070442a510704980a203000003078100c0700c00e0107607001e03a540054070900b19035403849038000941004100550003626074000050040c65140440090490400041802e500b181808000d075441a402030391554091802c0181107640801615420003d0201c1481d42020009100d40c0ca2041d03d0034007a07202d038029450b07031100c00c14540f81a040b58408a0107110301800105600c0724000381216400d20121140c100345003080a00a004007694401d00740a8241381c260700200d18031001e203030000c039041d03036000981c1c007007088892a81c9200003034048010300740d83d0807648280ba1680500500105140c0b120700f15001014020340101001c40c0064007114443d02c1c014500304041c14094a86220460744940031072134 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 71974948 1250 71973698 71973703
    0x40f08070909050303010315090f11030d17040303020714030d06051203072015030a0203040308010f0b1903110a031a0d0503030f270c031e0c04090203071a030a0509 72
    0x10ba0b070800099400d40c2c1c0707503840740107044022191103c00b581c2d58003002d034006034141050041e503a000b0140c0c40300f02c5c9440001d03d454030854401071814080c107510348843d10098100c0c0c89902c1685440c000d40c07900030500c5d10a02a0303420b124405d5207400042080034a440455010b5000c03104100c49032500c03c02100c0000751a4428024090940804c144541c9000360300002031088490001d4840e4403e114144204040b0390001c2d1500c030181c6400005200c18990b120f9610b03805010441008819189860641103041c801c080c1004000f40c1030303410000d2510b00030b0b400840d440401c6040d0566850102d10014018001d804081621111680260609d401e00241c26918143c2c0030004502d5030f241c0c9240b204449030000d011014210b640b41400706c000042c59400c0070612000030040c012461124201800d100c0120b0307150014001610102c0c00307030140010381002c515001d0720000303200c1d0a02c0c0046400c00019401612419106d0001d45100041d151700540c800d070368506c4108100e0b1210ba03005038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 71976198 1250 71974948 71974961
    0x1050703020408030a0c02120a060902030c030607021c0c02060301080f0609070609140406090e030415050310030f23070602100c05070b150d140c01030c2106080102040f080709 77
    0x40084c1d1003402101d210f240612840082640024001542240d480e00040e1800e100014110b6280762182c6400d803c506041007424442c050480c09080c8502e4084002560756a0322028a00c0100583c03111040f500e001e5985040000c1c2c0162002d59a9a1110f445590311080340c68600d03010300c203020010301d032420042503440545d003442d581c0d16103940c50724620038544600c64116030741c0240c0d1508001380030100307885002804901c98000c0c0d038480c0e1801c0c0040601d100751045100070300c0010001c010003080d101c00e950b420761750b100c48800e04016641c2004004018910200c01c1448104000d034007601000003032100445e41943d007120540b00322003a950040d55a0314204102064081c009000041c84603203100d580205810041c00e41110000001081410501c5058480311300f010b80210340d6103c00d224110b0410000e0030140310a0006c601d004001150040f06668002d03900d5403075000c0744005030403890050030786200941d00c0f070751140e40300c10088465108501144c03044c4017000900c440329001c8c56 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 71977448 1250 71976198 71976209
    0x80c0f1603050702130b060f0c07090204091d0712080705031e0c01060f051f02031903050f07031e051506030114100215070807030209061606060909050c0409050c0a03030f02010507030204 82
    0x15081c80514081c041c0c83d0b030000041d01209024001c404038103000bc0744042d000500300c601000c602d1172407c000e051b1191598141d40c04243c0c200d08014055009103803828940b060340309584075a80c040340c2c108039040d8000c0c501640342016540801d00520111a03001c0d0a20155010081180565842e0362885030b114522940c2c0e04200703a00c0c5191f228081c0034000d8103480510b40162032800940040410215461076181c0001ca9501e03c1130140214a4410b071a520083e141010051040351040e04c6040e2115120030030041903c802c005803001e0282c6910500c0510050001c1e9101c3d61070301d50603c249030024044600481c28100d0040c3d0079407000616280503070030403c200b00d0316110840215907640006024000303040e001c100c0307040ba64035040c1c001d0400b00841d08902d10910341528091058030000d070701929103c1e0411504030003141c03000c50102c141e039008550025080a440c0740c01c0e0b081544410391581e01514409001003455000740b07043d800543e250340200447e81d6003207030540c128012402070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 71978698 1250 71977448 71977459
    0x30506040803060a03080d0213050126040201050417010609050c0f18190611060106050f09011b0b041a0a150315062304060b040501080c0f1603050702130b 68
    0x810040741111000b035400240140190081c1610794542a00301c0d0b200e010002c00d010390014180041a41c0e13850040041c110918004600d040f032403514400122148030540072a00c01c050214013107a00643c01c40d0000c0c1192107040b00514007100e00c06009100ea441844d44107800e01e40002c0120b2612411500c0d1143c88030041c83c10101560841444054407111f91900600c03032484950f81080c64820520040906a41b00841c03100c4a10010303042c994180e0113501030003410f210420032944210281c0c1d508420030701c0c01c0700501100c24a112448440e45002501d80c43c1c1c501c0a0001b800030300030500f844403d65210801c1603448120302d00f01150801d0501c03c0301d40907548001e00c000362580e07001c028a0741c80114045a869100c0c03140100030754001800c9050040740c050000d0450400d07000b400c0c0104042d450240c1414038104c0042d0803100001e08401c0c02c0407000640c1c001c40180d000949030b0603d26041d410152107118600a01035500624050781308401c1c01e8082c5c4280046405090a4441d01404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 71979948 1250 71978698 71978701
    0x51009030b280902190303120c02030f0a050a080c03090718090c08011a0411030a0c020a12020601052b030f0c0b09060a0e07060503011208041e050a080304030506 71
    0x48040201c0405060a0300301d030a681600c80e00a648032011801c1c4044001000403650300d01d00c1040000180c482103003e00d6200403c081011a402007420b02031100f1503a80854280f0319410102e0075445020f451290034800468045541c0d0390102c0600b04a00305616040d0440e11003401c010220301044840d0700990b407103a5818484261840762000880d0603100e404202d910141c2d503240c030491525002045942e560300f014403003007044088102c220003c20b44040000c0c0100210224151100030203940d0050340fa0b546408c49244200171005030150080080c102040386d450b4020744480f0284207091151044410006a400741010801c0012002a24540d5100c0341c580d070503140c603041e404100c03080c403400910b070f0304c00b240c900200d046c440c4a1101c060000c1b40391006500e4110380f66918622500c2c1c2c45008140f200d00e40100c00c0303c1c1500c2810341c00d2884610245814000340c8126000f5008104c0c1c40b020000301402ca4001e04015980110f90f0f6030441510386882d00d550340101d10028203aa44402c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 71981198 1250 71979948 71979953
    0x1b0f0708070e090d12141807050105090f040902060f0301030803070e0f09130c0f0e0910020c1510090e030304021e0303070201030e01090204060b0a0906020d0906050a02010b03060712050105100903 86
    0x100b180c005c0060401c02007000000b040410b007044a049550340041c844104034581c815905204101c090712003400c00e1400c0403000004540c0c52200d9801b0240600ea56071015000c1d0740e5440300780c0d0304010b2003544e0700b592913840f481d00003420b42058680401155903c50303481c00500d8400c050304c62404001d8804c08503983c5d90410007085812141d001d41300d5048070040070646011840c1030a01a010000f002d0245007040301c045845e040e50000716144191043c02400b0100002280f64119400c0000208001e52248905800500b126a2125640e10b02d00289000d4019020000d148107500072200d0440c00180303004100000c0000c220740c160b05070030421900c0019806640030546400c425000022242d12650200d400c03201103030440500f00740c010a40344407031a809504000079000710b102905100c11813180240c46919280034500a00502103090340c000b074800d504c96411051300404541c8542000f02c03003d04035000740752000d4520f07030824001044509111100f503001200c13680d1080029461134 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 71982448 1250 71981198 71981207
    0x3031a060a03180215090307050a03050304270501030b0702150403050a0c0809040203040501091b060e06030408160b0108121e16050a0303140105040515061b0f0708070e090d 76
    0x34048001c00e1440155030f5805601c1e0307141200300c41d01000402c150f59622242c201440e00d50540e103c1403242510003030600000c1d80202c1074400b00c0303901025418004080c4003440181d0013000e060041a00d14100001043c403840410711802507126400b0b49800d00400c40070344e24411403c40300940415002c01a2004840c40b17441030705d50f200c0c02640ae45040102d2100001c060b17900c00c0e1410385842e03440d03200182c00d000310382d0500008800d01c0041621040c1c90b0942c0523206541c0203210328801c07407001c4001401d0080c60f200f1950f92158201c45071801059518001030b00031001c1c003401300c481c4661880381c03511101c00401c40c0c105941011180b0101c40d401c8681214541c041001d11403022440c165060004004006070a00e8512903100854201300c0800d0b0003402240c16442240f096013040300380309a9054044240e40502015588903a941c03074210a4007842890304640b80f80342d48500c03000e00d05000e6002c01c07250b05642c213032810782c0c42c0c4594031908105030743d009460700041508003140b01040310340203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 71983698 1250 71982448 71982461
    0x4210f0207031704050603090d031b2f0102070b150604050a0302060a140a09060315050f090a020c0d050903010f0545010b03010b03070609090504080408061303031a060a03 75
    0x3d4000c0c0902e0f0070b4680e00030540c15001540c4082c2e9a600c4412076219282c1c250040c010303182c1d076002c1c419200d81200b480082001804035002e541c81e0814046070075003640420001100115410000d40d503c80580c0b800c010090b400321200320130841e102c645820503180140c111000c039103000b410300d000c5604507001c200c5161b2048c0ca189050249103000f0b090208a078002901010301309443e00603810345040b401400756038046c0c000c0324142c2440c000900a0741e42e41f4101503945e5405540c1640d9660724041407200902c140841901c03584111004814403640c01401001044c0013a002449600142400c840c1640c00c00c3c0d07400302c0207044d040c04800360000140041044405a0740307009901c400e00707983d03007490403503418420759059440d0041c0100324142401103910046081d0010048503203407520081070100c8502440c109140c030f480c0400c0034802c0380801c2d58081c040c08003c3e503402b8101440030500e1003400d44e4044000ca4202299004c210340d0301d803041c01ca01c01016015a01c0c2c02c40c02442140200714 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 71984948 1250 71983698 71983733
    0x30606220b0d05010531150c0c02061602130504080a080c04030204051e090c06180d0204050a05010e010608090604120c050d11070f0302030a020108090a0b04210f020703 74
    0x100c0b000303010800074010103001e000d800702d5212141041c400b0100c6e00e121144420402c00101d100c0e2100090500018241c440c000140e0000380224240001ca030001c2000d5006035000402040301c0c5040341d4030590803181c4ca40b00715040c1c40ca011823546000c0507a5400c807000346c8000010f100490100c4e010b141016402200d00d0305051420780c41e0740c0000e08540056a004081c0c40c2d881c155801001d120042c81600314902c0d20041204440c1100010128840e0b034507000740140810070003680039180c800020040660081c010f00103460031a950b0700c0102424466000070b191160f000084440c0509080d5016987d40005045140d4580d00c41202d0703000480da0b003c042120440c0740c180407803028082542c1c1c4149a54440c080c103000c02115500c2c144c2e25411410034a0701041c410401a64002000c001d0107030f081c00e048502e0f542e1880060b05040d04800040c1000103003108101c2080345044a1814410f00e88208004440c04000222000201e1808210141e48600024404500d000200000c15103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 71986198 1250 71984948 71984959
    0x30115080a110a120302030301030b0708090a080f0d1e060b0703050702041e0e0d020d0905010e0d0303020c060103060b0910060c0f060e0a140d0e030601140406120302030702030606220b 81
    0xc1c0d13503a0303190b00030113940c0c2c0040d001600048010300400c130040d4005504404185845140da09110b4150380c0c450082050040c0f240d0f000062540c65400e440d41070f50010207035030404100c12002f030100580c141c151220603004451406802045000881c0c0954100c0307030300b66449904000656081c040103240301412b040c601c10350f00d1b0b91800107080e10701400148840e18400350845180c40391020b4a0110380c603a002041c0508102c2c00d00159034050810341200c202200c14402e040ea0508066000f8170031340d1580403075030103044004018030200d82c011800e903c4040e90310358219a24510201d610b50807074014040040c100361030b10707400315054101d1985814007850000401c0c042142071030380350100c00c150496009061441e400030b50b4030701b4454089529468101896101c00843c0029101c050501a68024401641e800416038442e80c0c0004090180c01e6108078080c0c0ca42d0902940d60b030030481c4100e12270303c138000000780c640c00c0450030500c00400c0d0701492460002c10060a2000e0480410701c1500079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 71987448 1250 71986198 71986219
    0xc06031006080a0b130b0a0e0105060a03090f0515010f06080f0103111516020306010906051f1421090a03091502010212010b040303080c0306010c0303110c0d020309030115080a11 78
    0x141c0c0d814100045e801c11030880024032055003030504c900c1005603840740a4511101e40100301644402d01140c3e0806070340e240000d00920107103040d902541ca50500a810362003840748880c8500309441d0458140c443e5020100c00ca41c2da1520b003242c9130384c0304640009005c54058010000a010300c0c06c000c80c4d1480c01024000754001e005051401500901050755048180040c444150300302400790700d0241440b03460030301484d4241000b05088000c0e40c140d5408080300443c0f1600a82d1144c0c10903640e400c03400e400301317580341d200c00e40d8045002c0d0f01859124140b560030000c0340c000c000c0041c54601803541515210b003072516107000440b07a142800c01d04000d40d5003c00402c6680c0e0317040c0d44003501030701455850300d0b121800c608000f0820000184802d41e00b05d410401d018107030b0f030002c40190720240e1618000c614901302d03040c0001d00e402003c0b000b00a601c100300da486801b58006c40542207104090b0001c100b0f0b895006c0202c1a00e00c030350b102c1c0403403d402c00c030611f501140920541c10741c84a4050300c0da0509 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 71988698 1250 71987448 71987471
    0x30d0516050d0e040c030603020303090f0d080a1d040905120c010b06030c0a0212160809040b030f06010302100e01230f04060801030302010b010e09070807121d0c06031006080a 77
    0x1c201a4180c08000109901c503074000c03d2406100708286405c4c64a0200885411940429a244184070030760b4801e1490541401d496500d100c039411f14980e00101351a10340c4424130703015250380150041d00e900e00001110000003030801d4400c034100c690700a0001c1c10448114100c6508a174400076210185540b5034003400e99540300e001c0154090404c1c0014030796514940880242004032804201c92a40410044a111191514440c418240c0c000e05810780d2030f411280050b0080410b585150b4044c050007047d050f124801280071030482e4002d03502143c00c17401e001012191a800d0100b000e01250240a4100b11504081140e40100100b2410340e4940050b20000c540385030856401000051104001803042550a01605541840c01e0070444281154080082d814480081003101003013296400689450302c22a50007824110b00b101c10000c40a188003c01c1c520410303049954543d03c503840f50301c052410042c04403480342a40f0141d20008a08003501224a0b04000d4a014505912401090031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 71989948 1250 71988698 71988703
    0x30c0306080d020c030708030f03150a0306060b030916081005090a21110a1502090a09180b15010e01080c0702090703061e210812012c06030d051605 65
    0x400c0d40c854000b042c0784c4107581c0405203413000b907802ca41240d81043c04101a445100815250000080181c503000c8030007010100d003240a49a1014250303506002000508841c1d020007140103102c1c420643e02440440d0701d07006001c0d0210b108101844c1d01c4143d04520081265003e140c0000d42c1d0030580d6000b140984171040400d040041701c030544402610003816664104842040d0540d0f08005405154402d44401560321040c2c0c01c040501c68000030004182c1e03842c2c6549101030404100d0401940010b12041c4021041c5a0340440702c402d030755004a94000904210000d0f0450140d44050b81d01c9400c000459000c1005001020001c006004180050751402581e61180f00319960010f4000d1802d420882e20f01c59000c0014000c045959007071003840328201c02045d807217250100403a40120b0030300d1300340d10900c1801405080c0c090600d0000c03485800120303c0100440c80b100c5181c2e101010402ca0f17811105060720741c0e03a410380c480c80b0041c4001d0b000340d02402d00746240611040f4580c1454a0b000e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 71991198 1250 71989948 71989963
    0x415090507030c12090b0a050c12010807140109050d0807080403150507140304020307090c05071a06030d050301080d14120708041707230c12010c080a0507050a030c030608 75
    0x4a40c070f82030b07118242540f054640840c4039032031005201c80384503619100e11182003d0f0000c5c0140d526100001c0c01c80394480200c6001c2176000c001d0070a50b40c0d480d140c1e00d85800c10350107543d03001050050f1000d9a50b11805042d030955600801e10888040d490382c44a24030380c05668126103000c0f0a02000000c0303a8036007407501d01d1400960005c1014540100010012247c00e00342ea500798800384184405078030002405426615400c00020300011229030a842c00e018a00c0c2c000c1c642c15440005450460400940b00e0094034141c04a803052000054240c401b400240242060307a48041c1c1c0b0301104920503a510200652900d900c0c91401c50041d00745100c1010403103c40000c2092517041c0810480024241441c1c03903104180581070507416a40d0159a145061801c01444070302501c074a207815050040d60f02014000340400741c03403481411001c0c043c00d142c2e504000801d0340240090348a06185c06503920900e030b1551900c0c50440f80020940040410050031801c040d0b451b1004220320301c0800559 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 71992448 1250 71991198 71991211
    0x1a0d030212040e01080607091d04050c0a0603091a0912030601090e040809031c050a08100906081506030c010e060706090b0c04030b0603030c0616120f020403030e0a1404150905 77
    0x300d0f0542c1030100342864a00c000d028801003004041c400c2000b24100381c5547c03d044200d440300985d540382c1d420140d03d00f02d1031171402e41e841304c418100016032940580c8100f50152161b4000c076009041844c0040c0c07482001ca5041c3d8040d00504035200c0c1651030f2100560740301205040074000700b501d0703000915211394115802c071002c90000803070b41654582008040e441c444191080f240b92903492800030310500034000d105090040d00808a50300079141414040038102489041042564425900e541ca1a544112854034007050021a1a0b1304012405801100040e1a5200384031542c00c140612540103400a1b80c0041d5074910844c0042d0081601c030307010741990714001740c969081d400c1407210803d015201d00d1295004100b440c240c07502c040b40c0960310a400e0280c181c000d515000e0140c44403022052041880c5103064826407104920747c0c0a041078074041e40e1054010058082888075448603030140d400040450106d50380f9514144d000300100350b44111310010001d580e0403070356050707402c16180c0c1d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 71993698 1250 71992448 71992469
    0x706020c01090f05010f0c0e22090b06011b230a021e01140702030a0b06150403060914010207030e04181b05190f050603180f070312031a0d03021204 65
    0xb00f0144a400d0149801850b20900100821129500c001d0814042a0101c60140c2000380031610741c09645210b1650490300c000060050b0103080ca070404020030f04403041c80c0415820a10119850141c40c50708504940c8139404264070070300c0d83e441d17074108030013005254a640314a50000c00184caa00c2509010500300860203104800c4120000d00403040030303c000c4070150303c01d0001c5005030b80c0001d02d1000c1d60742c2004040d100707521085e001c02d02d4070032000d9031340c0c0819078002400010421280d001e4080540610440b1701c1a0240d40700c8a8244c0c0b1841758054005001c2c00a41c8401346081d921408000d038401d201001940202d07502c813079484000e8400311560300d00c901c1003004030342403200b40f004540b140f0001000c07600e070402c00c130540c0c0888039000d918000d48000c0001002806442200111906400225a00f8070355600c1c01d19643c42050204444201c00722101c1e2a11034000d004203c2602c2c11140d40c03151a901d10014804a0310000700709074118030a190034031007000e22000041c405802200070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 71994948 1250 71993698 71993723
    0x60c061d0f060114030c0102101a0607050705090601210b030309100905030106090608060f040804030b09060702100209010e010e040f02030c0a090e100909110909030c010501120c03080706020c0109 86
    0x3281312003484185424041c0c0c003e643c01081036070707010070040300707885001c00c0000b181e00000344e5070381c0741d000d107070700d045801840004400041c40310006103c4200c1d901161900d01c1542c60400455a10565000035007410f246071042c9400b4500c59040075041d44406802c5900f4440c41e07400140c8024651601c81d00490000b000501407400c00f8060318000d41141c1c03109006d50391801041940d6810018500921a000c420101e4200109001100c0c001c0d5005002c020060803c0e0501c581c032031406640180c0948101f81100c150100076000707645900d10140c45d9691140000310044d21490401c903500c41d80540e40700c000c1d05e0301c19003502c05540101d0030401c80c40c0d21080c942c10090302079002030b00020714410012007001007061041c0403a8054803004200419980c409140c4141b140420030045540078443d24100030072500004003801c00c2110b400020310007a41e90300c0d2502000d502c00719010340003140b200410305c042041d01d8004d0001c984141d000600c0c003062942620708494030040c085641402946 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 71996198 1250 71994948 71994959
    0x60f0e150906011a0408031c1d0c1e030303040506040312050f01090218090109051e0f010506071509030503190b100f03090f060609050709060c061d0f0601 68
    0x100165512292000d00103560419000869842d9414400d040042c0803150b00e0000c1985448262002002c08108076038a4400810b070703440d4a43c3d2008000d8450f24500b58095800101c0030420350b036800e061030007500c132a00000e0f00703000000c7c03905d4044000c00281240c001b20f241d14200b004501c51400354024007007078145450000d011441114105413054206420b01040b200c1381c1c41e500d811181816001660303070030303009840182c22141d40c100307550101c100c5000184420301c03500000e2280d00f0416040001032030100c0e10704000b92041d130b103004e09210200014401414000001d08200e4060303000100c2c600301040718503064814914007100010000700911101804150f02c2900201c0b40c11424440881c4083c0403600b02c5409000c03010411458001d00c50000c2c1c00b035440361007004e412407a01c0d4205080e5090000286c07805111b2034000514000c0002e11041c4150454400c0c1c4844e03a4903000c0c50243d545807203014080524007d0004001c1030040001d0310420043c000000350500c0107050740d5071624 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 71997448 1250 71996198 71996203
    0x12f190b0f06090f060f0d0510061403120f09040204051201060504050a0c0807140c2e0203070f0305090106050603010e0402030d030b0307030b0a02040902040b040f060201090213020a020a060f0e 85
    0x40c0c90700f801482c00d20306000c441840041456404442036078000207803c4d50b10001202100305510140040c010459060288042a0400e40949851003121811440702100781030383ca82034400c48003000c180a10446c4419082070b002440c040200800160030300d91150001418800544408801a07549034810032550800340141a0302000e0301c042040840480c05000e0030411000300154100b11413440041d848000d5070741556081d10000c1c0840384a581c041106003032080040d0a01c590407140c000096485a015001312071150070f081c1e035410b81e004400942a80a083c01914881947d500e4510110703182c0c6034840038600074480f4038100c0c0d100e030600c2c0c0107160034024480c20340c1d81051f0401c80c40c54040e8030005400c1d404c50b94010340160315a551031070301d04000c0c021a0000301c0c003180000343c001640391035039010b0000d81d0100c0d1010302034640e0b41c0406908a503509134000350060100c07080140441001e42c0617042c4d50800e0700503213540900c07075500c24045078541d821041351a07076120b1840700203440c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 71998698 1250 71997448 71997451
    0xd060b0408070905070302030f040807020102011b09140603091903020a0206070b0a05060a030203030406050a05040f080705030d081003030e01030b09180f01090f0609140703060911012f190b0f 84
    0x546c2421851070070207004034070280800400150240200140f04021a4401d44c8040d6420303001c01103480c0318a8426a0040101605110354401c4141003400e50180307203000b201b181d01860b2640014052429503540e18441203440325020380550044140800140c0c42e481c000300340e620f01c21041039603d4500b0704036404c100e890107010179000e81d41a0707074244010b0310700000b00c1742a2603450410a44400300c01c001181c3c01d111720340100210310040000040c0a80c40080c1060554804030140c41c45d401d103c03141195400000c5a01c04000c0d8494513013080441d00404059422200615010031688103003004245001c01c01c0e1802c80030580c0100c01c0680a02d403d021104030495100003e110461598451100c62005424090501580c40c01024100008900e4154903c00d040d801c1d110748582c0d030f007041801003000300025070706c00c0103406100c0881e610800391072a115114000710f400403454441000889900c0741c0b006a40c501c00c01c170381c281c40b22000313a00d010340d424070032699400c1c1c51504801c00174100c0320 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 71999948 1250 71998698 71998711
    0x91317040528030b06040204050a080a063207031b120606020703020105180d0c08010e01140c0706050a110c031806090112020705030f070f050607020708030706020d060b0408070905 79
    0x10b0410781e041c800a04040c060101c9403c0107110300c03251102d50004000f445158885540801120030001c0d800c0004900e18030154090b02040102c03407917110320050500007400e141b500d1700c0303540d0003500002c02881d1203441c0c115501d4134001a003e465011420b00180c104120400410346050684044900310b0140c000900102e00c00f0b00000c616590018215025010500c130540421014043c90f82c1c41d40449183c04030b4000109070041a80c50b03c0450081100d41c0701c0750390550905030011035080c05450a540500c0744034684c05d2620140c0d85600b00189000b0b003100030810340310341400c2e5a44445c0e03c00f6000d0344144501a655803403c81c01907010044001c130219000e11010702c0704c140c591303800804c022483c5589100c09643c8100340e1600e9802e51040c01d422820b07805000c50383d038003480310000c20345114601c150100d42e81c90700c2e000c1040e695442c0314420940c29600411507400021301d030f5000781445440c90800491201e8842c03100d694241c0150300151960740c0100c3d006c015046250081540228 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 72001198 1250 71999948 71999989
    0x5061002070f06110309030a1505010e01050f100e0316170d08040201051b0d030f05070201051506070201090f0e1909051b030a06050109020414040e06060913170405 72
    0x42c58002d800d540c1d003440e0720403501885080c148803c854003007802214a000d80043c02e03222a010545000103070100c1d0032034008401440d107400803506120420744d050585000a1100c2c01c4205d403e404c00c001741800742151403c018002800b0703500368408020211443c3c010b0604101a182840c00c40d40102000d6802c0745401ea10502e0305010298102c150380741c00580a291043c0c1d1004503e0300b4902e081c142e146603050354421442c2c1078007026030580c403010014134980428030213500c0740300c2c040b802e941c821b40301d40e5202441052600c0040c40d00c1001004214818148603940070f44c2e0304c1d8400d44850099010500807203061003088131211f1108000c9c4940e408100f8200701c00c10842d11100d64550700c1c0c51040d9003180c1c5c001c03c2840295401c003d04003440364013007402d004030741e11950403d010f0742281c401d1840400501240d03007514501030081c0890704210030004c01c51643d6400c1003286c0041c0113045030b60b003162090303030003808140b241c40e03006411000001060b6440b840c080030f2103e04001203c2d07160081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 72002448 1250 72001198 72001213
    0x10e0a0b0f0907030503030901090303060b0a08010504020c010b150703111504020d0309052806050f180f030a0807020307051818010221101d0406050403050d050a05061002 75
    0x514454030164015964056207070840e61519005481c006680d000501944400310030401c8601781500028030040c0300350350510410f55145002c40e41805001000d002103085440140103506146d80686145200340c1c0011a014114602042c1506074480e95050011000a00c034000d01d500b00e02c0c2d5950b40d080010090035042c8042500052901d80a4002807054014110000c02d25100d414840c01030007004011074040418804100d05c121100100911050005c4c0b60004056005d02c080c0e54080d0000000705141c00f4210202400d160020004580c0c40321180740c098083d614100036068001c0e02c5001c42a54404143c01054501005544018402c90308074107a0b80c0c440805100315508030554645000d06800031320003050182c0038040c1184400800c0c40c801c1c03420710b80a00e403010301803003401810781326954480d002001b190244481d0440c1900145002c5030000d0b045902244e8468024641a41004860102a000d4442c2621115400e80e140c1c000d0000601e01030a020805044500092000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 72003698 1250 72002448 72002453
    0xb150102060f07030f0608060412090f141309030809010b060f0711120f03040e150d081c090f0302010b01080411150403060204080706020d03060509010b0708072102010e0a 75
    0x9400740100000e04030445140407071120750103a040350f0700389016144140002c07501c8030003280c1e45110403101607a2040c10200000c030050f0003900e0290644020b443c40d010142d0030500351002c2e1510000c40c1c0c54000f03034050550010300310f0030b200b04e0841501c87c1d911200c1c541044061035081d28030700507019118074000c10580320104003520480c2c000d107600460350100010302c50700107060f81c0072131082e911032406981c80f0070305840c0e0040014000d503400c0d98004200354032413070f603503241203148145000d800c0300b074020b40740010034018409414245603d0b40c424a100c40900100020307101e0400003100e600c9060401130301015028050f0508103d02803800071428031741900c031144420810311142d406000468059003601c09003c045402454100c80155516039039084030031741e01d074040d2161a0041c0034000c80d071440d152080c00380c001110b0000304030701c007264208030401f80d5035481050100c40da4101044800f00103400e000c000c062101074040400d08600079840c0c0642941e41813800c22030682c000d136582200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 72004948 1250 72003698 72003703
    0x15060306060904051504060507030f05010510180b0706060302040c02030306090a0e010b040203160216030b070e0105072004060902040b031302030309030610140405010b1b0309060a0c0b150102 84
    0x780050300302d51942040d00d81c0c0c1802e41c1030141c0751000701d03c0900c010b420041072040c1504114000c0300150780402c004043e841078030045640a000e0b82d80c2c0800c0c9855900300092103180c80750400744590a150f50038035540d134421180ba42c030445040b1545038580d9030400540c545482550294501400503501e54504100082c3d80d41c0b0005103440c01c0907646200501c80402c00754480e504010740507104541da8141b02407042d0710940c05902000040c45a0004903481c040780d0340e40b1400b205d42c0044058050b03120b20800f9900008172080c4581040070520180b40450341c0841240c802c02e84800c41075100c043c82d2000c3c881901c14903040450010700400041048000360341c00c40341d1181e01c0b40c0a0b03105509151000a045205200100c1d03898440c510501032100140c0d405142194400c540c0d242c502c0421605210a1360b0742481000304490050104070360b1103000c00c800c10104604003007902d03c1c0c00c82c0c03c0005290703600003000000000720305445d80c104122075100c240740c01c8403040c8400004210345c40300003507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 72006198 1250 72004948 72004951
    0x303060b091003110c0a0b010f0504090302030f0a2d08010b04060504140a0e0108280803070f1205090c031006030b060d030306050604150206070e09150604180b0315060306 75
    0x504061392108113843c20310225058070b04000c103042c10394031440800d080204c05140c2c01c1c01060a130713000d0501c0004480c42c00303118075101035906802850801c1440b041c0b6420035080181c10354148141b01c4c207030720b4403c95101051800ba110b0000720303d1741c011501c00d0061542205801c41d90544800300010701082d40c000080c1c0381241d05074104442e003a0301e001c011800550782c82d0302c80d004003031306c200002c240e1800205601c100400035041100c0a9032036080c00d00c070141c1240801401840c003c1000c182c0e054401d46c5281d0100019040c5081c0300f604001007001101d03012200301c020340d0050501c544036480c050102810b41420744100b405014195150b0f4004c10383e02801680c032640c10b0380005010036000740c000320020030008020680311961110155416002c14100700014000d04000803510350003104407000c5031802615001d581d82e03448641c144800c1c01d0000003580910305000006404201300074100303c00c0c0c07c3c85004a4000e1036071044c146441c4a420008104130305660030030860352000a84039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 72007448 1250 72006198 72006229
    0xd05070f0e0d0503040504050403020109021302090a05060c1e0102090a12080f09030f03040b030105040f090f02040b1c061d030304030f0c0c0b0a08040201090b0a02072303190303060b09 81
    0x80d84102c402d49080b52031449994000b9402c682094204400d060301903001c41c0f0254000d0300c4030700e0072a0300201c280080b44150350560341c0c000d411010030f008600b07110b40a40b4030011140e0454841c0b41504242ca0740c02100007441c0040b5030340002d019003da0801d04600740040c090280304a0703a400311650b40e00e0b140e0162280140034031001044a4160303030b800700441407a0700780100549550f15100d04800203190f009014040c0124100a09030310700003024422012160f8212070909204815542004050000c0400f11075102071f014646000e002512503541d10306d5807107050000740451101e035031008512400180d13052290020300420002c01d130000c0050303810000ca403500110141a038602496007803980c3d00801e000341030100d1040348594001c1880c9024a000b41c980f405895950030300c9030b81d07910800e854000148c00140007004500c070115250b218405007000c0c0f44540340030f044082803514068a0702c0344070081511802d07409040d014440c0601500c08180320034076240140006c15462503180044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 72008698 1250 72007448 72007459
    0x41d04030309020603040311011103040f03080703110d0e1b36090102030a050c0c070303052107121104052809060620071406071b09020d05070f0e 64
    0x9040611076480a2419a03008240c1610f0741400d040040c51803400c151003100750340c6860500c2a0024412040e42c0c891743e4080c0d545801881c05650486003a80040e000030181600e60b01280071240303400024020405403510001103008082580518000400c00c1c4040c110b0b04412004500742c80300000c4483c00c8841d6042c1e2504200d244030000003440104601084404480c020b005c110541074000351301076082c095090181d62690820032420340714080e02d21441364000181000024002c10107000407290790650704080c58040000c28096000850f01480015881540100000100e11a41c940740e81c3c1210724504040c113050120380300100640d80002c8100d005c2102b60f180703100390481d040c05084610000d1140980c0c511000e0644c0c81103480b0754078a01d4031a0000608031f1400500d03801160b18000f14243c800148805010590380004070035503412040d13100401d030b102000c4204034010250510010380e280d400390048000c440001d05254104000c84125400386035010124100c1000100d94 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 72009948 1250 72008698 72008701
    0x70e01080c0906090904260901030c09050a091a04060e0702101b0302031305010603110a1d0114030f060108070f12050604060b12011a040e06090613080d0f090215041d 73
    0x7402441300030301a10781907047e6031b000d150019004824000c0c0c50480800c0e00e05101d9500c80000548103030400b4050309070404030092040002071100c1d0411484400d11540c8400005200d102050594505411884226000c0c00510811a030b04002240e14000002010040103004c0d8251043d51803918102074105a00440031070b28a0700c841851112040d4003074004c0203142c4d034034905070f44220345c21084a1720810300d202c0c0014094000c0c01600c1304001c00314000c540a60f00b0b0420480c001c1c02d0700c1700480c0d018030406400c0c3c0d072818002c0001e40d0180c8111002451880d192200322050070808e0f402c07000d070b108801141000002d00004001d50419404940411404000c1d004a030640303141d0b08072200c00d50700380858464210240d050a0200c4401601c00380b00da8000300b100f01d070b0b03141010750350342031150300490004e81c61039826610030300868465207411b4a00007191101c10140c50640d0aa012584d56035252042140b6180c14080700c110a4401054106403921040c4a9480c2d139500d10031200390075080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 72011198 1250 72009948 72009953
    0x30305030601170a0b09070c0507090e15040b010e0106030b01050702040f0e0114160306030c060c0201020a080f0309070614040e040203070305060423070308160501060e070e01080c0906090904 84
    0x340c001e040c038200030a2903000c0c0c44c4c4812031802602c8031141d102e020700ba4600202d40304034031504209044c80d030050f001f44202c40c03501d0038100080c4640b4052207400d019540019000340400c00d50b5a00850248003100c440354140301c4010300030782c0180c3c80701050518114080070503981003810b8460880d01210000340440d1400303040d002030146d920078917602d1751810903440038074440600c9207400344010584040010b4565a0103800300c0f41c00740406001d110312400d0403c47c60303101c0c8100d541151b10600c141c40c1c22054a90300c4401541281810100c54840481008049101004003200420301c03032408030b4400000c1c0b05050218803890080c115008070403400901551030401220004603846800c48000e49024180500742d56082d100c0d03180c101262a144000000c0b0000d108016a80c1000407103190038130122418460f92140402142c1d29503c544001502158007042e00748140c6c103603215600e0a274046400103004420050155074052000c0c800001152502822742d0489402a98491150b440c0c0d030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 72012448 1250 72011198 72011207
    0x10903020301060621051e040609081204030e01140a050703030e03040620030408030d02030601020c0d03020601080d0504210f0503040f0f080303060d02040515060c0106062304030305030601 83
    0x540000e074141d07090002c005810780e4800307600c08510901003004940d54131000e00c070400790360042d20040943c2e058140300b080030700d60403450a900284121000100070310980e5801d1114ac1042c4590031510380c2e00f00800040c15040550130704100070900c1d002c1007080100d0440c0003d0300540d00d00604100b00407950f00e041600951108031446031100880e902e50b607403032070002c04404900229651140360f40a4001581c00000151030598040c107014608082a50b80070b1802900010080380c11403180e1052881c8646440201c44400350180d40944072a40c144002d00f403902c00ca01040703608204080104220304408400b00510009403e002890030b02c105050894921a0452014020b0700000600150304040d00b420042191480c0e10000d0311107585161041c0c603800111382c03064200402d942104d00500e415400250310142c000244000c08034001d000c1406500041141500c981d518481400b07c503070001c01d203030b129914181c0c0c015140c0a2142c2c00340c1141c0118030009003480404030204450b230f0b018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 72013698 1250 72012448 72012467
    0x7090e1308030108010e070501180e071b11010e010203090a0e0a06031e02030d030b060702010c1e1a090601050109030f08190c03080a0c091a090306040c060207060c0b0403030b01 78
    0x2811454407075131038440c1203000703210a03113000395a482040800681940a43c40544c40125041c2d07040c0b408600c0c02049140318007004203600d0400501c8201f40c0030f04018103411040b850301a4900c159070b0886031002400014000c0e40d0076065510030b110300222940d4003051401500c200348016240d503120840404040c4c4030036040182a045071041074041c40c2e05030070b01500001e00840880c0c84c891a0440c003a012900c480708120f402c0141004654055406802144401ca1083e45076500ca840e142c444102003030459a4225485008802c02c0003084068110707494000300980c1c09003189500d40b9001a200c0452440014a04907804504c0781c01d00080c4405d542c00d00280400300c0c000d0520101000b003001d1495a011004122442c0c08030b48104401d10644902c209203403181c1d0f02103402c0900c08042004080049903400c038040041454a840902109028a2060b03456414039820280c01900300001508200b04100e05803e00502142d46d41744541e0700709400d4100040d01c00405401220b08105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 72014948 1250 72013698 72013703
    0x150f050a1415040e040b010e04081204020121020405010809030405030606120705100c03020f010c120e070f030f020306012301030902030c03120c0c04020705070b090109090515011707090e13 83
    0x4003041c0010812a030054a83c400c40c4104406c04407682c0b100c1d02007031403c100b40c1d0050300900c418490ba460080072008118ac00c140141400c80c030034406003002c2c0d524603035140d94a42045801050401155800c60170068000183d1000346040c1414040402ea544000802083c131074659040d041e107483d5010b00c07101014000282c101c1d0f114942c145805400100360600440c0144907002c007060103181d0600c54907814031b1044d038820f02d03104c640107011805032281c440ba2418500601200044060301181e07640021442451a11a030316040c2c0101420944141c0c016040f00309480454240035003860102d09002100342400601e580c42400460300c1d141d00d4004141d01032107003405240c0c1c4424944041c0c4040d074a5103080301c1c0460780c002c05110a1740200300000303055030301400c0240111003d410180c00ac0c5e074018944480950307915039560b002d4031026104440e017080414009110b551b44020140c1401c052101528124205007000909008039445180580fa0724074020411440110203010100794 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 72016198 1250 72014948 72014989
    0xb070c02011e030605090604020304240e030d09050c0303040b040620060403020c030d030c020303010506030705130f0306110301030305070f171b070e060310050a0b1003150f050a14 79
    0x802e000000e40180101e0081c180f0800a0b000045c0c031034070b414005c40e0311403680043c01c092071107401c17460b410440728104003590003191074161000c10042c0410141ca0942e000c8507011858030300300d00707140c0c0c1014488688180290400c20040c00707400b030710b4000c80303084905524200e07800311106004641c50664640013040640a04000d01040c19400523540300c3c0000c04a045e40da04501000007a001c8480300c46041c00540c000384010811458200c000d035521040134108540303420301e0b651540f124120241c00c10301008403610018024800305114000c400c050282e4528030395410340d100645103002d000340042c481c0127481d44407002c00150403400c40305209861040c80d21a00080b8002c0e08000d5a0003d00c2180d02c00c100e0002101251031440d5800340340302030302a00440e034440d0208030262100500351150b054881284107200d88802c00310314403120059500050f050200035161112980503488056151140f26052000b583d0f0450404201e501411200c8007109403070780864003195040c00c0070041e18 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 72017448 1250 72016198 72016247
    0x906081f06030b1207120201111509030c070f06140d0e060a020711030a0b07120b0312030109150503030a03020a18080105160206090c041109130e070603090b070c0201 73
    0x5a0b05604107a0b140c820844600c00c143c400501001e5585c9910302c05c0b55111006010750b00e016502a01303840c24050320b00c4d019210014840511011040002d45910589600010303100000e000d05100e24000341068882540c0c0e5540f40600082416005040c402c0650200050301011208180c1c04103801d5845201561290f14000a444000b07410282c0c081c0d0350a00c051200d5200741c070b40402c040c1c090943c407804803480754036582001c48050407405080c0d030310b01c0c3d40c1d024100e0076079800300421618004040019582c9604214a56041d00c10341c5003030040c400ca150205016a0780c0200c150f51070300c03081c0d1034010f8603101c0b004011039049803c0c0e88240101401070300049119141034004c10b108003100c013041d1002304100482241d40c1d00c411030381c640c0c0301e400017900240a4501600300d15280c3c0607188030307142010002c00004624403a2018001c4101d0342c1d0b042003841c0410b0500c1864000d2400b0304042041e03142e142c40f00f561405000f80750900f000805141c0c5000c6a010701602d4800c00443c2c40701b061b40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 72018698 1250 72017448 72017459
    0x30e060307300e0109020901140303160b04020a06020a121d040e0c01030b101202130b1c060506070b041509050f010501030201021b031f18110f01030204060906081f 72
    0x41e15111100300003031810080550382030401409418845ca40c00780c100c510b140e00e81800c07000b610000350030141d414002040440c1c8422121404005082d0241b51482414186403040040f00040e55000c003007035401503817000c000f1960403282d1842c1c001c824101000054070004d0641c1c41000d541c4210359005260102d003c000d40b00000d41e035035030381e030081c0ca04104801801c4100006030441200041c0012098100c1e95807412081d0050200f0090014000f2039203034072807001400a8006107529214480d07144902803022006014540c000c1c88203490b0940351280a4070740150704640180040c10100100c00c00f2004207007680c0c88a000d207278014040d1480e8040d40301416000c1c2c0310a02c4140c0c014460041484181d95111000f802100b8005008114a2000c00350207082c00f4030560300401210313074810301000600200c50629010500c20b0b0604480f42201c00204080c040a0b000c44604051042c842070002c0340d04164001c0a48013141408445960b0728411910b200044542c601240014003100144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 72019948 1250 72018698 72018767
    0x5030706170a06080307120302040306020d050a0b040e12071a01030c06020f07050618210705130506060405010c110d031d04090809270408030403080c0304030e060307 73
    0x4421200e00401e2150320340c1801402643c1c070f20302600d185030304100044000200101c00509105030310303040c0541820356949518040780c1100440c01c0c4456110300800202400303512640c01c1e1150226810490302411420aa96030780301a500943c59480007e0741100f0301100c00d0400b1080c20b982c00c0411815a10ba107400301215510344580c001501c40c0c8a690b00c21503c003c01c500d016204c000e0042c0d41071410700c592a0188012400b000c0d60010b0a4a400e91400307000090010040c808110090603a40d1a200901800c80c6d001881105642d203408280400c40d912041203404481092904c2003e080c004e0400d80840c04c0343e19071260348045100384500070150010100650700084241c0c0d0a40c105446c800d1106032400c65600800d075010820044000d45440006084e03603034030b4001c1140d84010082030400300c0b0304003510140c0d0b01710004010001050707840b41280358000402803d0508505180d540641500c02c085006845180040001164280704410000c5986200884200c54080c0380d03448a2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 72021198 1250 72019948 72019967
    0x18100c03021c05010506030601050706021b0c030d08010308030609071704030c061d06010e13050a0c050a050a03050c06030a09060218010207061103030a02030601090314071805070e0f060405030706 86
    0x25102e1044030002e030001114412103040f14405401e0a1841c7c0d21000115415408035104407005a030a003c2aa40d90410342c03120481c0c03981000003070003001d00c40c408051901412800302c500b04030b420780060002482c01c005883d040701080c0c848041c25120305400b50f8851048a04801c030720440c0310200b0040c19031003040c510400d03005520802c50410103080d5413030b03400002000d09100d503001200411281c640c10804507032002c0245480406105160303207660170410341060035100d0004170070080c0041d00c0e0504004004000864000314032600d90b82d900e5444000a000c80c510515020000480c0b0042c50f4000c1c0d401158814400c540d901f070751101c2d0401c0344a06203010760040c800d8043c04a030711030080089640000c00e000040d8196a640344218019600c000e019070f0400c5a0094001f0008145c004045894401580604140c6060452010701002d1084102c1d290a05140c188480d00e9042080c111a204003640c0f600401c00310700d0f012800a00c40c80e03001d19050f1142c60000101d00341c2c03201858 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 72022448 1250 72021198 72021217
    0x30201140a150506160b0402190f0e01050301090c0303111603080d0c0503070527100203030f070f0507060f0b090903070b0c07030906110703320105070818100c0302 72
    0x1801c1d1600c400c2400568001c004c001702065580d00c412801185c0d6200d0165409403000340382e1000262081050b481002207544274104600006d00103020710741d100303a20140502402d40080206401c1e41c1c50307062400b1080d200103402c1c040091020a40402d0500410054401c0c05000484403540c0c0d2820600756070103a402c2880161810349103100c807900c941d0032240200402d07031b5403a04002190000c80c01f9080840207040c0003002041903507a2a8a4400382074070540080d070061b540344d2070103854140c0d22403070041041c4100b14004001101498102061390032940d040107002448484060000000b010381c221066800000d0108200680700000010150703540b00e6104e642d004c2c2c54005032011a80520b00000740480e0306000103000d601d1140c0542c0c0d034040c0c003490490b10816a030b500c804528407071014404c201c0c0d03007045104108400500c100c03010248a541e0081150b4601100c00601140c03003c0d00031f450300c00e40e4403810200d50508100360a540c01d040c5504104014400034081d00951101707214 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 72023698 1250 72022448 72022481
    0x71203030c030504020a1e080607030507090b070819030207150c140f07030f2106030b011707060806121b090c070308040803040f051f0e0d1209030201140a 68
    0x1d524158070070301802d0700507a070242c0b07802082070a0413018400d81510741c540040400f401840020007410400001c0d028080a48001a26040402c2c000f800c80c0755a41260f50b0003081044840d00007000e01e0200c46020905000001c00181050b200310080c1c4204200600075099202c03648071003541951000c0b010480c0743c2c45003201c1c0003c41c0c4a0380c1c0a40035101407140400414002003001c42c0c000c004461384480035190241c0c0385a0f042801c9400c1c225032041c08141542e455034180100005c0404150141c20f032131507518011206640a030b907950441f0701899040100007008642251a40402c803036006a070003059948001942d008004006482d5031094440d03640d00c0c0101d40c041c00d10800300d5201e01d405945401d216616500d03000000c0d80080c000b101e0800c90500990080341060284040d4194820044405002000070401c2901c4840c0e100c0b03015600180c400705400342e0446035203504031700c0102d8003282503586410140e0040c03000c18130164901c01d03440100000d0604550001000740c80d0008e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 72024948 1250 72023698 72023711
    0x513080a0615060e1e0607150605090612060601032a02010e19050703030c03120608101a2b1703040c060c0c05010815030d110601080c0d1502090307120303 68
    0x1c1c220345014004080607049010680a8254030034150417035480c421000d00002e02d0400d5555680c511920b11100c1c0b51606a0354640900161a1008919401040403179028820b0800d0b00e141980310700e0b010380101d040c1603036903d14808076405401540b803d1441514802d8000d034800390003a0207098a407452003914000d01401c58400c18000220540701e81d00f010084c08640e081d650b041c3d5840541e6403003a814061001564100d8000c103010b688094551640945010b54500908030180c4e0036451000c030070700350b51008200883d04c0f480c01040b50740c403104440b074004030620071101a4401d01010042d06141f4080007213801c501c1c03401d0013140900d1094500a04130f6035240400c46219912840050001040d00c504010030f6100d5a0140e0300022100ca04e40c0f21304802e10000380c646070795584c0b43d201003103a103030b20482100e9007400003600615081001e0400040c0490005100b42080c40b002400003501c1e203440c40c04e40b500c4da4140e400501c000f03002c440c80144c44034200225030850802c00c400003070900c00e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 72026198 1250 72024948 72024959
    0xa0503030a0b030c0d05030a230703090806071119030302070c0303112104141909050a1d0304062601030b0414010c09180b060409020919060206070513080a0615 70
    0xe04061700e90000b010b10f04042d200350040b1100381e00d12502049035585402400012140c40300200101d0340f007512072505d520301d02200142000c0c0c00824440034841102208010f400002c240c1c80d80a161403480c0c8420401d6038075040e0024011054090b2143c1c05901c2e0101c20150000c441b890442410741c1164120a0040800c00045669a48250404109000401451000049403440c40c5c100034044004c04074407a034081d2403c1007941c400c03141992240c041c8036200b1402d1040c0402c45901000ba0014424041c60b102e42c0d0340b10300d1007002c0400071000e003100d651840c0f19410702002c6c0c0307940c000e0441070359407818840d00c1040c060310143c50000b4001c80489030307014148120803005c060307503c0e8940324620b82407201d4440c007203150301d415501e40c80e41804160713982c410b402440909150000141c40b540c0500c10f201070702e4101e00a401004150701801e124968000821031303405041458144e0795001c4450210f020344195038030803241741c070641008a0402c01160046440c000040d54440784060f90740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 72027448 1250 72026198 72026209
    0x504120e0616020405060f0904120909270c03020603090708011a01020d110709020a020f010b0910030605090102090409060b18100303110c03070315050108010b01050409020306030a0503030a0b030c 86
    0x3020020118480b62401c2d40050806400140e80180d00170044541031004078082000b2050803a001c0742d416441215050520341c100a0385c0e000b90400c48001c1003481c1c4025000c11003075541107900b00303040c41e80042410810103d81d80d1500039680c043d003120340742c2c181800701d240d4400039802281455424540c43e040c1c200e01034000eaa52840c0160b00601201d030b2a00700c10f03640d0f008441030003034260165000100c2c0282d09400101107500c10f99000b801607100c44810542141e000c0310f805841050b2030014801da590f5140060340582e500a2400220fa440d10500a0b009224103640f0940180c10800d0000a00819030f120740529031055070303881c01c4054820700030110321070202c2c1d292855815100b01400401c0c800e001c4115018030001c2100c0d080708003078000920317005165101b1118880c42070f035000c0600010b4000c4da0b005049840c02402500c40c180c001900074040e40c010804c000e6408400103206075030803c410030940e5009010380340e8a042100401d80501540c1030182c1c0a0321034484040f8403070904 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 72028698 1250 72027448 72027457
    0xf0e010c0b040210022d10110306010f0306030c060c1104140a020d0207020d051e030a02060402011209020405010608090708030301080a0605100b0301060206011403010c0f140d0504120e06 82
    0x220944401d281c0d220b500300036404203070f1902802180309a95075a01050040903141642071031003504001c074015000c54041c6070000701c02c5200c800740c0c200150038509258100c10b9075001402402d0494400d440c0039070840003010a98400303041c0826202d00000c4030b9400640e141c0e007541c0903008031703480c5101034014081510003c482c14800c0b1a541d071b00262001005a0143c05040402d0101600d8028603800061901d6500c1000742e4407a04405120b81d600300640c401d080e20b545505001e1030a045100f0341c040d40785d500083c0040e042c4241d9402248414400d0b40c00040201d6005004004550311141d000300039503070844034070100303201b02e079004a0710b400300109590403120408010011002c01d590b03404050b150103020074205005800300481c5051608019501919059009103002e6151149904c040d030b5480700960300903403514550860a0f42c1c440e000081604042c03c24040101c0e4942d80d281182c860449020211442c14041c00200070760340103659000c100c540c4d1801c140701110010401603216 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 72029948 1250 72028698 72028703
    0x30c03020c060406020906120408030a051014010e04021c06051504050f1203070f050307021305070509120f010c02010605150f03040615150201021b0304060518031c0f0e010c 76
    0x102e0360000d07001860540051040302c001034403850810803c0981110040803e070ba084801c0d04006c02040003011041c420203910102410022480d00e00c0c1956035445015581c0d8890304110046400c04c20540315074048540040704021000060904611194010a00c40c040c0904c5803a41804000050500d40b06480945000602942d0302d6650003040280c44521881d0440c524003050103404003240301c4804c24142c0c5400792000e13558400ea184100054140420a900702081c42c01d0b0610600300c0d400001d035034400c1d0099480c040c022041c41d0540b854840e0307011a100c100d6080c0780c020300c80301d64103400c07207403c0703403070954062541c0c2c7c4001110740180d02941c107200f0703201c0a080c400176001c11503d800150003510b80e0b031829452a80c0300c280200101070003429100152b0b40004811620038680d40703c0042801242c80a10f00340350078458001d000d8410641c84680454609100100c01d50703040c0a05049950312141040e6641d20550014000088014111010403124940038503a94080e1142d403d4495 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 72031198 1250 72029948 72029953
    0x201020f040909060608060c0a09050604030809060304050a0501061404060b030f0c160c090509060601020a020906130605100906080703020408070b0708160501020d0b030c0a09110c0607030606030c03020c 89
    0x2418142c4101c001d020140041d81c045440b0b0f280000c080400740000c0d0700403024010607550704c9200640144c150211a481240200410802007001c129280c0580d04901c90440350250740b0303145c5060051816075403020241c16540783c08000a941c4e000700e1020000400e06032414814280d8070040c4001740d0008880e0121005040b41c0081c065124000080910240c02405189100b14549130309003007244030f40050b0211942d500510480c1241048020351044091005051328030003680807440598018108600540c0c0d040424103120369650400c00261038090112400c518101d0801060a800c0303110720400305020f00d02042b80076100303000302e400303030740c41c03480202685440d0650404540d440b92105807030740082403140d4460315601600f0348d1003c1d40a0000940c94000800881c1d04441c038040080c0e100703a00041030360fa29030320745044600071924126800600580d00301c09928980c4a00c101c10210782c01103408000c0000c2d0950702280c290360884d6400c10240c005904168100e114000c0e1560b03656 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 72032448 1250 72031198 72031207
    0x702030607080619061805120d1412150108070f080606030a0f0c03060806070e0a09020a020106030219060311040b070b09010b03030c15060a0e0103080304030e0d210201020f 76
    0x1c0c1e01849140b0f4010002a0840c00401c0020602082400f07035900420001030380c4543d8542d81d58402d01c401c00151030121090180060301344d6031160350305031101d01c4409100003600301ca1000354800c01602c0000344a590144014505a44a40013003411043e0399408140380300c0109500710320a41d184551413150761101c08054540d042041050341000f001c0c4541151581d84044c80c0c41514090459a43d5031507c010402500b030100584c1400802131a40080040b8001440000e070b403005007050842d00c80e07182c0169101041c040481c09001c543d08042c1d001100884405102d1910050940131120207079020410220b04151000711403040388031b503201025080c4002004181c29010305500a01ca000c00041e0462508020a040d90450751817100300f60400055101c0d0702040407403160340000f01301d0700704484030304007944029070500c18000a0040000031000904060040390020799900004201039061324107480c00412105000300015407000e4a40d95180600c2e005000340c81d400208401e444d800c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 72033698 1250 72032448 72032461
    0x20a080f06041401180b060916020316050c04110c0d02071d060a0e0907030b06030c1c08160f03020c0d2d061103101205070306020f0c07060e0f040207020306 69
    0x884a000400314003550380d00b081c000c17602000580400c02c1c030b2099150b80440e181c001d0800031007000003854180402a02e4200f001c416070b0200440d41c14407080c0c21802e510794514140280350045002c5542e81151425401c80c1d0480401000742180c000c1000480c0c41491025508a0311000c840c81140038030380000c0607400c20400e0100d0229800b90003c0c088045099841e4200030082c50240c51000791500710940c144284201c0d030101d59807014054008004120f80100401c5012006060b4480b505856080c440308224a1004503003452a031003010380c42d40801030401c0a4020034014084004d03115032082c50703485050410b05048042d070025907040000c032403503002c0740007026120300c0a07100782480589900011050b1003551071162144600381d0b220f00e868118103e10f202d1541001c1c1144002e00b5049000403800100348060b030740d20507000360300d45059512407039440c01124001c25060180710004100039500180107481c0c3c40044030b5207420001803c0502049210300c41000c0e40580101e80000c0c80c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 72034948 1250 72033698 72033713
    0xd05040503060c16050601031506060e03030409020a02070b040b1305042306010c06050a05011508010308040b18040f0c0318080301090b030f0d030504020a051509010c06060b0703050403020a080f0604 87
    0x1404013000c0800e0b802c60542d51750385080c150242c004486030482d4418484004105104081c0134204a040130301c05105000d001903501d0007644101030f8540d8001400c01a40d038828460b450080c40700d01600c585a98441002580303503040002a481a203402c1100021305240c9406118072242400b1041091313420041e0090751002002043c1078180180d2200c800001600c03446882c1c41014a001c001a043d4140024200d03003804106181c000c20144100510100c0e50b148100c0e022141c0240d151651114080c003d8814803842c058a40c1c0d102d803034500c02c12510500e070b400c08404140c031503a041204c05581c1940ea00d129400354009041c1e03c4041c4014004007c0c181d000d45c002440040c12515060540b90140f490a034149052a001a480d07030140411401c024003918050181215420000031642c18081914004e0040490400000809a00920005500ca80c000e4040d22040c5a03551070f04e400d01520302e41c0203120413401440c803c80001505000407403841403034102500980301d10384842d1076110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 72036198 1250 72034948 72034957
    0xd14131101021603060204030b090303221109010b12060604060c0201080a09060e0706020606010806010c0f1502030a061e030305091009050901030c051201060510050703020708010218030d05040503060c 88
    0x81c10340c41490a80742070b11074070211500003184581c0001d690b03141546000352070b000010f00900d90179402401400155228407080c40c00c0c240300100710399503016880c203024074800040d02a158205507010000308a40d040f041c02000c4007541200c01d0380c02034440c030007032107010720483c800d900004c0e1044501000641c802c80006812100808001c0b804002c203440300d000b1150005010700c1c1590220004100860701070114960140c001d00f0700c281546003050001c0e1413181c0c0c0001c0205600e12400717030ba0341002100b4030319011142040c04c046403245003011072800100400e01401c0c03261342c10688101c1d003045000303d035030b8260b95055441500300340d108030071f1201103044600e95030140100e10700081510744170f0030b10441c001d40c011202c00d0240340c80c1605001d02480c04c2901c121199040903001e12076034540c0e42411020300302c02e1400c2952088070b070404904001151f00704a01075400010303101c0c800620304072030301c4003110200c0c01c1e02e0040c002020300b07880901c41c6105080d01900400002030451101c50081c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 72037448 1250 72036198 72036233
    0x5061503011214060a1d010c080a0b060c0a050c031e10051312030f05070c05071403012a08071805010c110d0b15040b0d02060306031c050d1413 63
    0xc04040114001040c04c003581160000e0855030f489032011054424490030443c20702110f802004480c050341c0005140000040803000342585601c2d40125641b01d1104464035210104295001c00350149000d50302c0c0e5000c0c1c0c1c9180d00c00d104064035a0706c480d201c04c03c1030700c00000c1c4000500082c0b401c00c06a10103030170010400070f22a111050054003041101d441d07050080d14030b58000515250040070a4216400504070030100701e40151301070001500003401c00207680110040410802460f40002d01500c040c2492140c5178198a03107001d0100c00003900c0003005111390b03e402503680d80e0f1882c104ca406910200c2c007240540b8281d010007895020301514441c05020b0980303e4204015100414542c3c0c550480403560b104854041241e000d4040a0840741c0c100201d40174081c650500001038416404440003920504000001c10b1031a81d0810906685034035a0b9601c02c040181c0c410301804a070401141d5111503410070180702070b00e9030f44e0960b6611800b5540b110764907514081d00d0350b1030072000d01d9580c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 72038698 1250 72037448 72037463
    0xd090815060f030d02060f240411090d08070507060201090221190308070e040c0c11040608012904020313030c032001061a030403090e0406061802030a050615030112 72
    0x1002c4182c405002c0448000c0d40c0e0307001042d0504100340b0b00c1c4580e01000307104c0811002c11050030b010b41500c031100e04105800c100c40c003140424124006284e20312075003a00c940d1200d881c51440c410020350001801295019406640d20300b6070328082a800d03074291000080d4045041a1b40051140f0b100306118024094031048982469858a085080039a1510242d01040c2c0f00c9040214460303008400e0141f0800c1581e0602c60711100d0072002d05024a4000c0041c1540400075424459445030b6010000501e11038000340400c903580c810005a20b0040d04403c1404c114520880e070707240c2850f000710380c01408003010501e10201075880c1141c0c0e1034100c01d001c4bc10041088006940b900203092144c9003da030307000000840c149420034030b44180040710346590300424148208408a600140d00710101c507040d00e02200141d032580f61000003030015811400002030704043c4508000d032591b015500c50607041004018139242e00b010009440c001848a04240d1401c00052180c000103103032080800e4802d580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 72039948 1250 72038698 72038719
    0x504030f060b0d0b010503010506100906050c0a05010c030b011202070c090e0c0d050d020c0102120919030b0718050405060307141c080705010c080108060a11070b0f06030d09081506 79
    0x9900142505013035031241c02500040c0010b2500780304041c0c06c50b504072604806c800a6a0003d000d2032140e12800003800804159000c100c0024444488240d9210000300480301d061040a0001c00420309914002030403440d00ca4a044414421110490341105007041d690749018001005000687e240e985035000c0c28031421419110030070460f4441e84107201400c1191801e1400130300e460907020f0803604650002e501008003208032400c40352000f074141e505200e03050b20940d01000000c40c682c401043c4000c610200000140c1c0b1520400ca0f031924109003000769541c031001c000c00d680c0252000c0b581500310321420018064407040c55540440301030a202840703454028a029054240c40003502c0388400081c008041100a103c1d4440540150400384425410003844940d41e00b03005041914440d507a10507032491050302800d49010707543c0460482072618002c0450f030780740803094485600030301c0340318103071007a041c05190001e040d02c5000c0010083c3d81160000009241809810590030006489 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 72041198 1250 72039948 72039971
    0xb040e040807060212150d020d060504020a0b0a050406020d050c060a051f0602010b040e0102030403020d11010912031a030606030c040506041508030a08060901140d051006060c11040c0504030f06 85
    0xc0c041e1021304880765030a500d04000c3c05246c41691015546c4218840003210780169203070392282000d035401401c0090340341d42e01c1c80458900400c83c1c0140e03a00003404038445d4003090340100280181d558030307030a8800c01c5000010654450260340d103000850303000180020303000c13401e032350203a0381c032810300710b0482a46a03101503c45902d5080b900090f00607511284105601c7c100b5000310741074907031103500031403641c60241c400035124502040c912040001000c01e103c1c4589094002c403c00d2a00701100e2100c82c051640090000d0086000411081c0405440c641803446c0109101d0300c81c1c0030240c05000c540d40c800003044014100200000d40c460703510700041a4940071010302001600000004582c2c4d2681040050040d100041c0702920525070600107000e5109a14222100c1910035103e00b090343e055440d011342820f4140441c03a201c00e01c1e00d80c0000307029502075441030030316002d01c40d05201c8540e40c405120a4654039004480455401c00c0104009500c04214907802c60051400140704203000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 72042448 1250 72041198 72041201
    0x302030a0603150c090e06031203090a05071211040501030b0a090c0905070c21090e0408070203010c0f110606060a050a020f01050f010504110a0f03020a030608070b0309060708010b040e04080706 85
    0x801200902e60340c0e107a1940c501a00b1100752005802a0040341b92035181020000359691111104021800700c00300c041540900108075000595a2107000d48400948402c0c0e4000303014440c027010303a00304440454403401801d140c49441d042c1c1c1c2d0816001041d030703610b105045c0090000c80f40c0071140000d038100001146505031003070601400241e5110f507000c40d01800c1007604c40c0042c00609203503030746c01d42c90790822a801a404500712041c0700f00103c0a55202c0c241503204d070054480280d015400c1c100302032440c56000b00c00313595940d005d0700d0f0a90740290590401d5a94a41181d0464105508112010704140288003518641140c0e2044650586450500e2401d5520690300d88100035403400052180b0702d0a400343e050035200b8000420308084500d2001895a02c1c122110030034954000340c1d221801e44203800c000060446542200e082c9903580f0b000344107c1d0b0003220b1016840c05001c001c2400c4070700c03400030b8074121118601054241070910000c888552006030040319094401c000350000240325 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 72043698 1250 72042448 72042473
    0x3030705030d0506011e0807120e03070c03030329060c0a050d050d0b040e030909060301180302100f0b10030e030d0c0c020a050319060506041805030c1c08070302030a0603 75
    0x301c402c0420141403e030000340c803c00e07580b80888640403500140c0c04c0032030b911100c641d41c884000e103002c01c0d00140260644004111407042650240000114402400042d80e006401c403807181d0741c01c000359180c910394001c6458010761040c41600780040c4029040c603004003e89400700414058138120101651120716010031003d044020503000301c0c2c500b00c084614880c051410000780d80c140450408602100d44071f1040c1d6521510580c602d00201d40151800d61000080603c02501c8880903d06804c3c06580c4007400100010154141031011002c403080d401015103800c0d01401302419421070050075405041030300c0071890039100c240000315145085008036204c038078041c4c079102c1c1c030460b00c0c1c01800031205103504101c2c001e034440d0384c0208075460074150307041c40310b5000711001800c1d445240004015000d0313288403c1c1c5013130006169105204011006200d066407200842c0c50f102c09002d4030000c00700c408039804010855040006483c01d009070000c550020641c0000620241c4a40d2003a221803070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 72044948 1250 72043698 72043717
    0x10b03061003050d05070308010510020c0301020c010b04050c07020904080c0a02030616030f050906070e0303090303121801090201050d090303091a0a0b06030903041a04090212040204050c071101030b0303070503 92
    0x18506002c00900c2428000030182c0d051134034249103000380584002c3d09a540610500340100e411840c1c561041c2d100740508400c00300300070000c0d503a0b000c0104085029185002c010342c401c51405012883d140d45032400ca69075580e001e0200001c59030341d0346500f079068004040d0780740345005003032405005036824018a0310415413200803091107078031a01d00808485040e5010203210f8541803e000c4002d0002070065070101403483c0100d030400d5021f010034294000e01110701e8140c0b1000c80c050242d034100000b00351103008544860303c4050304800c415400d81e440701c50060302088042113400800680b40c0c22030b1715254004e0401151007802d5035a9801e000300381107220380da80c0f40010280410b983c40303070160b84490182200c4240c114140260080c0e00c030f106a2284001d4503c244003117820f611030303a0040d50024800680b0841d100c0c0d4006c403040700b1581c01110b00320321652501c4005440c0341140e900351408590002c0f90880101c60400064005050001403564184014800329000a40801c001e251412 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 72046198 1250 72044948 72044971
    0x50312070305040e0702210901080402061308010e030a021213120614041406070c0b130309050306090a02010f0c0b06090903191218021f0302070213020304020109050108011503020c010b0306 83
    0xd01d03001c84840e0f9030341c543e501418810024980b845c1c0c1d0000196400c1501140c4141e5502c0e4ed02c140e204c088140c0f41e01424065003001c600011155000c0050101c805464003511002c0280d060030311a136100d0201c40e000395100da55418070028604c001d1004001d0701c50340c0c2c0001c86410308003d080c00c080c030880b000c580c400031071050101c40f95400c0c4802c50304103585081044c01e00303146544c1c3d542c01c1d500007002c100d6804040c3c03096100341841038007070034020f007000f0703080d09d8030382c1070090351251104a0311034281e011076600340000d00d809201c0c100354030582e9000f140440c0070792640d80402440c2d1070301602d02d800318070003844030007590341d00ca8404510314121515410380c1d144c410300300681603956105400003014500180307040581c45200704600d40c120410b5154601a0034000c003540280600d441c003035088103009200c00621682680150b0145000340c8802c000c0d03503a101c0046591000900a05403103400302e44590340c6650084c0c000d001c002c00d90b00008a61458201c0c042868000c04849580208 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 72047448 1250 72046198 72046213
    0x3040605150f030d0507052805120f0702060d0b040f0207111c03050705070807030b041a0c0d0902131407090b090a031218090b03070906050312070305040e0702 70
    0x41000d203002048090141c4410442e500d405000a84503181c0207140000d00000007413100412805004400782ca03003010071480d0803021080e401a200c4048654125120301c900d106510030417040400b52202e41e120204402c0c5407801d1642441501c0e009444d000400d552104c8501d0310b0743d9920b01807501103c1d045140145c4840c058280800600308500b80d080c0100304841d810307a044450058000e00c400d0301820002d580381a10700d46645402c00740c4e0302100706c43c0039100f40030040006000c40c450043d4080c1e50b921406010342200c0c42031414060380e0110707030300004000280c0c003a41e0310381004a400380000d0110501d410401d404400380c03010401c0a42411100e081007081e40380c0c20880e02006000c400d44414186588071004c80e000071100d0001909200341c0d90203a00489204030b81021102031100003c400195807404454003600600a800d80310717010741540412030003c81d10900c0c0455000070000c0c030545020200303803035540c0e100c01029400c0160802c008180600e0066442d40210016401000c0d034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 72048698 1250 72047448 72047461
    0xc0f06060816090605090406240602060a0e15010302090702100e0c03011514130207080703020703050c0315040b0603070302100903110f1e03010b0406030b220305120603010f0203040605 81
    0x240c42e8580c010f84403c0f8a8410184111b895a500f040e0303000744d000000141e455030100c0311041000310682411071481c203280c00850358a5000c1038060050300103ca0900071070220250320358031116403070354544005400e80010000362900804d030980050003801a1a4021080e8154500355090014a68110383c4894599412400c3c24031072070031803807224500c02d4020380c100b02d808054002c8507007441d84610020031014600002c81c0e811a135071581d00c9052141d40d21540d1a01175291142440152030b9030080c0a400c0c0b2040c02c0103d2404410b10709039030307484030543e1587e95044100350702401043d0907104039003001c0300680700d44401e1214900e85403540c0890701c0c138600d07003075a001820081d90f81c015a8000c400d05015110074941c45000854902c58410b41580000841e004000404415500a050040c0013060221034030ae440c0c080c40000c00b0412402c40180181d16900b0809140140061010400c0d0912005032070402c0d03070040c000400200e60403012840130b00c140d03041601e082e1085ca40e904180182c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 72049948 1250 72048698 72048733
    0x70f11070b0712030b0a090903051603030e150106050a08041412040911091005030402040f06140102010e0307021c11030109060c1214011a070506070507031205040b070c0f060608 78
    0x1880282d00c0c4c2400820f01c008042415156940301b150314082d240c034549400c00d4090819507000c00c405101005151741700d41001000341401c3e1100d00b41d10b0249181c5140c114a9550f841c0381038640e65106c2a25100c40c20340100c4412600a2060352aa108600d80003883c0354140510070314074940460718ad45030341c1000040340450780c14468041d010402000403a8561300c80b0030009460342c5407410196102ea855001180281c02520769008000e49042030104400140b0622030f0b000742001c1e4002c01038800c2c13100c1c600b95288110b042c0a07500c00740c1c442070920404140465002240c2c07281540c030344d191701c4d03100100b820358404120407100c090b190140403c40d030341c0c802490001030f110040c0034402c6c0107032804100710103136041c06203523008040280340082002c02427085405c0030b03622030212405480d04040003084c540009800302d000070b03001d08052030000c0c41800f0302806140c121601c1c0425481d200400d4451000150084404400c1c8004a0011901a10490300200703c0100a480d024944035800380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 72051198 1250 72049948 72049973
    0x80703031d0c0d0204020c1509070603060e060d12020a0501020f0901030513151104050a0b030108010605091506031801050406140c12010e0408040b03040f0201090f050306070f11070b07 81
    0x206580400c442c00039503030b01ca40f409141e590b0162070060765001c0f908035050510500c4e03007803107060710101400e000c6074440000701042294040c2d43c00300105900ca291010541038140c44442d031003400c980f96500402c0c0440c10500078480355004841000c59980e95840c00e82e00005012503400502081e0040d403541c050040e02c0d4050000f4021701a28040c568070f020100318140700c05404190b503080e4041811090305c08482c0034080c01802d103601c050380e40001e10001e42c400d0103205025401c054002601e400e09201c030728000e101600c0e580800e80a04020300440d500014060440c240b01c03083c84400c03ca40c20b105050046000300740c041a2120044041801c844000d061060160000c0000c100c0c5400103a0819054803240d690161154607241091203140c040c9800c102c4044400100b1b010421021800480d46c45100303072200355100c1c0c4e07603100239002e460b42c40c45001c0e0150009800a1825803141c03507142607245541c00e0100708028604100c0745004569082200050400642c8100380b0141e000c1d0107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 72052448 1250 72051198 72051251
    0x1020c120c07050402030105030d0e010306180f0b0108010305031c02040b04080a0c0b03101215020a05040e0901020f040302060901210e0c0906010f080709080d0f1b0302061302030a08070303 83
    0x17586154980400310381d448294421420411018800880c2544c1c429007000c0000e2000e50380d440e408042030001c0380c00030700c183d2516141c2d039460142d1038504c07940201d40080c100d07074106010f181400312085c0480041003151500003a00380c3d08000c045103040301940548058800600201641045441c043d42c4040044e0000c516804046c020441141d0107a0540e800340c0c0c220f104201c10314551441c26256620b5500f101e07500c40350020890510460703000020b00129019882020030315200c070f102a07803c030f10966140d20740058082005001500303044004200e40744041c5006410302d008034807055241c00070400d038603003d56100e5005c100900c01c100700c010001e1030103d584000500301040060154500c5000307440130b010030040014040c2c2e0050865400030000181903403a16008160300804403143c845d0b000c40402c4240300703600d845140c3c1e880404401c950580041c1092f448807089002182c1090303204a0b40340c414500e440c00041d0510001e0708541e0701c81d442c0070901c0e50354504d00f004104001d8000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 72053698 1250 72052448 72052451
    0x1091407230c030c0102030906100f0305060c0306010e04090302031306090b0a08130506010915060c0308060108060a0504020c010f06080d020703120309021e15090a090c0201020c120c070504 83
    0x340000c00740154076001c21501c448003060365844118003000c1c11406002ca140440754804010440c0c0d140e000b20700745114001c15400220380c140c46103032422103240a0300025085602080c0000c0b00040390340021908100141000c03e0503410160001d805e60784007003c02c41c0160000710301e001c0c0751034071251218054055802c100fc141414420715024038040e401c071040c200005540454085419070b00c66031006500715060b19050360f12080180040c144280041c00301003402200061102d00c10901c120703a10368196a550003546030100112424100070308503c1e448800d199001600d680e940c8020600b081c1020008134a46203031100c6e20040351503580c490b240c00c1d040030070300c07050140c0d0201e15181035a42c0a021100300d1071880d03004400410030420b0094001800f0525545039040c0c9034407588900b04201e5042c150075500315100c1506024145a0b0f503002101000180400461600402801c64680c0b0006041020f13581155103010160405040d080c84d0000319422020010300420740078000c02e480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 72054948 1250 72053698 72053717
    0xd02031c02010506061606090305120c0301030302060f070e0405040c050d0318080c101407020a0608040b061f0503040203121c0f02180d020f0a15020606030a0206030103020d150501091407 82
    0x3280c04074030784521b0010308040da01e542d040704241c06101551580120340c0c8034007110f846e01d03c80555107a802800700340c01605c248000540b1131600035103030740e2081400c0d60b980300700051640b0a11010703080c0a4000c41d0300104000000c103454942d0154103004c03500a944000650f9000d1421201c082d84580108a1139007080070404a59102c20031020100200d43c0b400c070707141d00050303144000725002d41e02e0000c2d40003074440c40000d2500c0d80b000749607004602480e00302c260742d1210010050b1b60200740603420490000c004280c8141402200a164014005402d684062070500f00c0204541d010790105500004c400f01e80c5114590300784504440010031140c11854039540c101d4600b00c2c407210440ca5480b0704002d1043c4000c54543c00c91005445601521031070480f525943c1900d410802c400c100401403017101c0000d01c413898001801d0164980140c002c5d40356900f16006d01c15400074022050b81e000c1c80c0a00d800c101020117100f1540241010440008c007210700b0380b4200203c0c0000b9081d0700411190340c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 72056198 1250 72054948 72054967
    0x603050d021b03150f100902070f1b08120904021333050405040b011e030f0e010204031101030504050a0b130b0c0310090b030a06020315040c0807020a03030b0d02031c0201050606 78
    0x1003107681c01401d081d07445d425503500c110f40340c0b111500c1600506111800071540404000202c005c0d40c01851181160b031070046841d01c0c1c0e640280c0094400c030300f00b9074444020718501000d150000c25180030081d102510b010a0720910000600d0b80740e1101d08031a0072030f8001c001061428001c100d00c0f81441000640b5032005801c010030328011405400e10842d52944500300e42d038014004245040c1850170a102d42c07940080300a80204040c003a54006242441c41e48501c0d002d0610071141a264450000c0d80f400b44514011070081100800840301032003044060004240035a40ba1481081c0a0320004040d000c40d00e458014640c000c1c00c00711440100f4428040b80c0180d0b5480501582d82d13944000884001d5100040d10b044d0070b9840c0502800d20000030f01c005d030124506a800b00d080d007501d080c8010300e0000401c46100500311901c00041e0894003155000a100b030700100d40c480e000400204902915400103400c0500d003108040d0740c940c45029240985030280034290740410100d40450600f940c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 72057448 1250 72056198 72056233
    0xf01051308041a0714010b0108060a180213030b010b09010e010309030c0b1b0c03090f19030b04020301090803010602060f091603020904170f07052e0b040603050d021b03 74
    0x3c0c0103041e140c0d000c01408032005404078081e6844190007529a448125680d49000e0003060500c480500181003540018810700b8062002800c89003c1c028044044e140319070b9207402504400c044006500d00324900001146555006902801201f400150703190141800905510710f9035500a041c503007403101b20000300350459000507480e6040290040c040e13669040302e48250259582c40c01c00b088010074074141d20b6000101400d010703074069401d06c0510071031030200405072182c032401060705203400e041440003410f55040b26400070f1000d0004180c85845641e50410307038100741c01000060384101c08100d400c003511890281c015184c8009000040185400c020b0001000d01000c0c0c0108080f00201c1d082000680c0348001c2426002c0302e80e500e4140720f1543c450740364401e40c0c050f1001d01c110400318112510304551074032086d1440c0c0c0000c48094082c24040c02804c0c0d0300a507180d00681d41c05001000c10020701c0190b1100a2a901802480b00c902160030318042107a90040c1c020350191031640c080e1400b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 72058698 1250 72057448 72057457
    0x60812210c04151103040f06110303040506061011010f0203150a08030f1809090a0c0807081c0e04060308030a06080c0d0204051317040f0b03040c050907020c0901080f01051308 77
    0x40ca03c2c40400c40d90a0542a00c80c000e110030220242d200002e40060100c00d0303a6080c1040c0c0340f09a492518011803021515664007007501d0140c081c0d00003502103070840c6484007072031011880c181001c6c007601019000080c215144040122112a000000c0001c1080080043d503002d01c000c03500821030700d05141c2c03c556280143ca003400058403001036645a0300411250384070390844010105421458008415920b0380203d10741160449004400810740c01f4000c038111003070390102e45c02481a07800b01c120300d504281e00915107000f40940c1c0b941440032a10707940500e00c00385000c0c5501c56a40d05010705075008550080d8841100c907009184140c4013a070b0b6a02089042540403900400c6648070301100c500701e11413809d00204458200850802c44104020203001150361011000040981d5400251110720046400624031012000c0501c00b80c502440c2c02ca411607941d02c12902804240c4011804842080c0c00c038240c10f034030011000c0c00342d02003400384d10fa000408943d226104d021550321a0083e028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 72059948 1250 72058698 72058709
    0x313080115290d020714030a142808070e0109060c140c06160308010f0305060402011805040e0a110f011e12090609020a0e1603020904060812210c04 65
    0x2d2046000000100580c014401148425106030b610940310079040c2c000c0d8440d041c1140c04525074040e09000391404801d9800c641c0f0717031740c035000b01407801014880d50300d6100c3d00340720b881034480d1550b404444128044907110f41c60240c49218013410030302e80140ca000d0b00080020704100503000144482da07403254520b440c8507401411821822412250a030612480c2d80001e600144c0c0416249400b50990200c403041a0007034840c0107081e40c031449440e2401300c1900001d48680d01071400700300154460841c0340100d00110091180c0a0789810020301592072400e655103940d07018025407400d1220400510b40151011150000f6410041c000a40b401803403800c44132602c60410503209620b801440540303100c14140f20201301002061034440c000b403441240aa004138503035400407d0b20300d100707e03905000310342030410890840d00030501203001e1342c45400713032542081d152036002498813010004080005501d01c206030710b6154076070000c0c2c10a4030741440e41c525191848148507400a070702080b42c00340c0c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 72061198 1250 72059948 72059969
    0x206060315162001050403020703150902011b060b0a0803040303020709021305120a082704050601021e07050d0c0e0703050103210c02150406020f060405031b070b0a020313080115 78
    0x1100044448900150610051041d5085c10100002c1650200340401901c0c0b08018000c8c0480000154400b1500e2200000740401c1c0e203500c05014240c140c2c2c840c888411311621000c18121003050208980700d01a902c91400d503030020500340105501441040c010300f400c0c4e130085007064407040c43e50a034400c031807207901e001d40b01d1601c0c40710804506006c61014182c10030341065a60501c5500d80503000044d2140d0300f008060b41310402c081d4980fa000b0b2170b000b011b0580c010701845007a410042c03403c4244902c1100300d0f0bc18410000340031b80380e030b84400e900c080c050034001050f030307103454a03500b40300500030300da041011b142c01d0043c03001070081352807103c200405174444000300e07011243c03d03906d24001200107584050b030a40c00c000c0105980c002803044e40c0c41582a507120a03000002aaa621020395005009400c1805805101c03601d0314034410a2641d80300440300b01d240c1d102146504c42d8841e81d1801d0041e0000115100380242c04282c04d001032000d4402041300b0150741c20403014070609400740c0351a04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 72062448 1250 72061198 72061217
    0x9060114010512130c0816060513050306130b0906090319050d05040f0519021309021f090302100c0f030818010e0a060b0d080f07051c020606031516 65
    0x20391240c1c0940303c55080300302e25031a41d4100903000d6400072003414001c40d130041c002a4045022000880c0b9414000b25003541d801c202410101c3c02c3d24181c00144981c40b070b260aa00f00011140e5042000c0f60044141c440c40c5290440c540c07c09000c0d1020040c0008843d900000a11036281800021182c0d0321050528990150950200450319803007085101409141004c05100c248000850b41c030200c0c9202e1030465043e8990704070a0342c0900007d400180d4044d41c020441c204d68080b980040320640d20052040c05c804295031800c02040d245071708000700244040d01c0600c118185190906600012828081e01300b40040c1d480600440754800010700f00403034500445c0340600c041000d0100d1560b50302c0240030510180c031620344e4130003a00b1429103d0908000384031600f8140340c01c0380c0404d550008411490b01d00d0b8000801c00c680e0000000b11401c2c45034400000001700d5801c0c0343d01c0b400e28203602800c49802c00508142c50690003c000c42844d00c62141800210801c0c0000303010808458140032458 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 72063698 1250 72062448 72062489
    0x207060f11042607032003010c0201060501050405130204030b0c180307030209060103020a020c09090a0c050a060f08070c02060d0f0c030c02030313020604090e150109020702030c0d0f050a0c150503090601 89
    0x34112030782d00040410400281e04506c2240302c1e6001c0032a0301050300204141d4080f01c504a0a03160a4401d8034085041041f0901913401c01c0700a000e003890b00d4003405842d10341c2e80e54528064640c1140c024002000c049455545100300e50250044e142c000c400400e20541503800003007800102414442c181640001d503085450b00034412607000f894014410065480d00f441200d1310707002080011143c400980b04081060301d80340e41c2c43d04c1602c00598034102010b240720400d6a2a42d0040d1915080c0000c0400c81001aa648402040944540ba4010801c409101c41c7d103025214401c8a50080c0341c10555000e003c00e40c0001540d07480311000030886941c07040c80c004610123208980241420074240710b80803120490001e0440070100f202c0d00d100e03909a0342d850a810490042450007541030304100d803210034900d40b00c010900103601070b114200e41e0304000d5a0306407410f044800c5c200c0780318400c0c180420a1014091011042201a0900601c4c51604c0d074039207901c0d031005000720301400d07413840044480c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 72064948 1250 72063698 72063703
    0x51b010b03011e060801090f06110d06090204031103030315042f04050307080a0b010e060406150807080a1107171201080c09060a030308060112020d0207060f110426 72
    0x201044040c0080010205042081552268403e00000e46605040000646020520411504a4000c00c0113240c11070969a250044d00c0d10310610040d6501c10703c0f803188402d900f4460500149140500141e40c1d43c6146451130920084032040d511031741081c000c02010444034003101181d075104540001c2e00b8000d54410101210300c11059814030001d4020242c401c104007002842900c0341103040722255551142c10603982c50641100400f06030440c001000031000c00303107000360420030041c03001c0f03040c589802c004c840311101d64289000155041c0b081c06a9690400c3c1501c3c0c2110206406026039540780c249115184140d0b8801000c04411600f200c00c09401c84041c0c400f90a0203001070788455a4562182e9074503591001c1140c030800004020481601c0c0230342010342229415100c0c0702e10346e650380e00150750b04220210140c2c852502005055108030b0a031004102540c499040080d04111540010307084078205008030909240c00c020500a4a0246041400c00080c0c1024002c0c3d590820171040d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 72066198 1250 72064948 72064961
    0x9060212130314042612070c0302031207170c120309030d0c050a05070b060604050604150f0201050f040209060111011d0f030702030319110105040605091b0109060507030c0b0106091e06051b01 84
    0x22807001190300c7c001c010044a1020840e0f00880071501d0300a5141895545441200710007008003102c1d0300032035554080380307019109981c480000e440d210240300460300c1040d0b1007140d02c407070b554000203100284000b092040818840c0103290150034084620000342080c0316101015141c159900005051540c46108032006044d000e440a62a20780d2070800540c1d4521070141c4a002c90740c0320341005121441440b4051240003125041d100e26110340d024840415805040340e030401200f0901040014000d000c0c120403401b9690413207008202c0f0319425820250400040e008940080048202580d00001951186403458040c01281550a6000d483c140004520034100f9401c001c01c000074420307da40000d110304007030000d8078031440b0b50542000007002c20700b0409010542d8018144900e610620140400750b00c00e040183c4a140291601d0301c1c03090b0700f40d0000c40054402c0703106000d40d40c84040d29a40820300d0050501c0644e06101780600140244050100d91340303005409100d58410941120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 72067448 1250 72066198 72066223
    0x1109060703050417030307080c0705010e0109050d030e030c0a060203070c060c0f090e04020907080711070806090708030406081906051801090e07060e04090602121303140426 76
    0x9564400c400d00c0c0241039900584100584844034109540c480040481200e10880c125620004a561000c0c1c2621007600100310903185507580c2c40480c1880042480307002c8042d07004c1c0c40104691083c2e001c006081e5030706c0c410144145c1d0424031070b00c0c91205001075008000d65212a015031a640c1d10441241e40b010007840141806040c00081042107030040f800704001c941640d201010a521812000b40e60b5030156402500295a000007a0ba05481030681d00d030068001d241039402182000701c0d030744c07500626070460400d43d046141801280141000391100401d1548040e5040510b00a17000d070100358014880101700f2100f0100300758014180d030003800a4500249600303003509014a852034207110901950a4092614001c5010f2060000c1c00303000310b94141c0d540c12000f6240c10b09000144c07030720310030841c1c1e21602446168002c40c1c0303d05600384101e40000317620010800d681402048002c00c03c5100d00200c0c81000240001100d050451a50121300324041c81598141518203180400402c4030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 72068698 1250 72067448 72067459
    0x100c0f03020a0b011e050f060706090302071a120702060f01060c0201051201090506040509070513020f0405060301060503040605060406030c050609180703022703070509090109050724080108030306041109 89
    0x2084440c0c94416a192070345860a450b1032a9032034006000d4605030344801148d00c08010300a2900107003c641110050f0b48c4240b0684d5206941c420111000f031440035106c3d41c11802c0820b01d03030304564014880c958051083d00c01001281414000007100e441c06000311001c010300b0884410079640603000b25035040d003115041a18a6079030b80000d0f401848243c9000b4807860034680428208070002030b080003030307410040004200c1440812160025801254425000d000c01cbc030001506590724405580200042d480c0c80c1e5503450302c0c0c40c00c07030112440100001d20580c5004030500120705400b41d01d0080ea042500d22541d95409072001580000070089441e22200400b020420038075856009042100018006600700005424082034000c855402458050780807040030030040c901a2071250b00f001003200006015149a1500c50410201c1c3d00304883c0130480d0103c1014110050440711240406403030a1082c5504252071251a4400030b0001c030322032a140c4000f0002817071494215007104000411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 72069948 1250 72068698 72068701
    0x30201050319110f0a020d0806100e0a0302100804020102100e06070c0204180c05130615050f04030515060901050d0b0105090601020c0301060e0403080108030c0a0602180405070e040506100c0f03020a0b 88
    0x20b440c00140c2c008484170b001805151189201c980c0601d598a008a100424481d10803c1210b802c44120503000f032500e6110301131000010140e21452480300e01003075070796034005691a041c00007900d0102118006850240b5028401420210100e80305070001d1242c50141c103240180e00019000d0100e140c00201e9600d030768a289000c22218903401e800321442513039621300c2c24820300c2d11a400c40d0164440e0518120b10744c40c84200301d52040d4006c00c401e809600e027541c100350301c2c1e0f01c1d480e01c1d00108212f4a14008a06001d00c10903150240445004180844121030410880c0d9078082c180a0181319040c0244015000304d5020383c000d0120f1481140c0180007001142d41c0d41c0b9080c03841d007000f501d069003c1000c4400200d035814000c8111080c8034000001054000c4180d074514000b907005800300e061088620305266611b607101d0103014055215a5124428504090100800c1300d0707028101a01c41d9008070f45080266412889900810b42c0251182600c4030b01c0d0700f0180e041410350000102070414010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 72071198 1250 72069948 72069967
    0x3110f040e01050108071a031f0312020102030108190f0210030f0221070201020306151c0c020f010605010504140d08040801020703081509010612020c10020d02120f0103020105031911 80
    0x103001030b040b161501d01b180e5025549884040c0604454841c141a4000400004080031070710790003000d000c084c6404802c8210f41d82e840b1851103c1036078080e140103035000001001016030800c0714458044010165100411559a8102443c100c00c00000e001e520295901040d00d4065401001441440b03041903680b0141ca2202c00d66846540e1800c6011100b800c0c0490b007164070502c2039034481d01c8003400c0c43d00a002c10303003074000a0303030440090740040b83c616856000101d406401517081c00e1000b5001400202d071403910702030030348080341c100504101c0188010040c2d860510200000c0b402c0c00c0e102e04601c49100d00b010905407040f80c1180300d096000003104010540e0010b0080c0c4034400903804001c0200a0500304032032401c00303205d10030000e03c0d041021002e02c0e400f13030f00501c0300501602c00c440880c072494690b8000d0340c210704000f518065000c02d22404850400190f50343c00540c2407170703c000a6040d40e001070034900024100c0503541100c081218010001984690b031405450741b1003507260340c840d9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 72072448 1250 72071198 72071201
    0x160b100b0d06030309140a05010804080d02040f03030809060c030c0a0903020d08030601110a0507051018062303100911070818150c100f060f030803040b060d0c03110f040e01 76
    0x288011000101d2400f0001201800e4106146a8980042c103247c0800c1c0b0301030046503d000042c00580d40390004010400d010001880144014050390758010661850760401070038500e030003010840782d604140c0c10080011404004c5031b50000c0000a195110311400000321800419504001e41184a00e4400002d04c00444040c40c890f5201341c0c2e8400152103840c0850b42c032480c0411000381140e005140600003481c0503861440c08290521700700502d40032201e14803e04d03c825500c24070100d0040c0d0252580c1c0303881c50304000c14044101452914504010241d400220309500c1442c04560340d450801d80c808007030350b00b00c0300d8054100607019103807081c10b22111140d14503e00303218450b083c000c4aaa40081c0c8010a44252182e001c01818078480c2c02c5a00d017002d45107038000241c000d50390b0700000c64032101e01c0301e60f8409140250f406584030b03e0f103072602d02c11140000d041103100d9180c1e01612000246920090020703603070300c112080b200311035140c08510700810700101c0c1c1d9030103402c2c910b0401d0b01d010b05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 72073698 1250 72072448 72072461
    0x10030c090209190b090402090607060212070206060d03022517010e010605010318140705030f030c060f0c07031103090a1203080609070504051c0602071a0c160b100b0d 73
    0x3200c180c8a028248104440d840c041d61107504c8a2410502c849103c0c1e103010380c058010360f42d0140926103071a10590f190003c9034804640710300030001c01c4051103001a410040141c0c0041306071140c1114007500d13140030303560740c0300014083c240c0c400d0402074064051100c003440e0018045807180009003c110310815000e09814594a05503600e885000a81076100740501110344490303c00001d03140150344c480303c442c2240d0075400d500d10b110710480040c082c1c404014038003020f80305e14080d640b102140104982007000c082c20020b00b06c8243d00030310103c0d603810011120398590506143c454000b080f014603045001b4400c145600c00310400000407079100a404c080b100901c2560b611030150317640000c0082401081ea500c0c800600184003d00c81c40c14071005101102030541c4511054181d256941000d0b42d010101c121142c031a40b40c8518901d04e51a00c82ca500706441c60b210900305a1700241e09106481ea101001e0318490455001c0751205d0760744107a4801178104800c94540e950300031101000603040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 72074948 1250 72073698 72073717
    0xd020a03120507082e140a050a0602190606090c08010905071d011b08030112050607020601030f0807140609031c0b130905070b0304050604030311030f0a0510030c0902 73
    0x104801c22545042c4140c500c50b02da1900c030141151244607a101c04000001442d00300700031905001400070004905200080c41d00c00c0b19118075170940418447c100324a0b92060f0300030910b000d4103100c06500403442d010b41c010024400d5102d018a03041c250701404841e8001c642e654039001c2c08602017a806a84681078559045081c4080d88030b04c00211044a1b01c2ca00b02884040158400541d030740c0b048000804510142841903a030204a4a80c2102c9a00a034001000c13690448610341c200b200611029500c5400d500103007009601d1900d41d4403140c404060000d1401500041031002c2058035240140c0e180d0141088400340d10b801c50041b5aa80c0c840503220005001c00403083c88501d00d240941c81e024400600002c140300440c07070021001e000800c0c82140d03640604071000c00c04064402c0071f14421030140c3e00a00300d1b4242810042c040b50207139a4403a5265004204005559000724042e81c1c100028035000a200e56454030110340005081d0030087c00312011a500180861458000d401c0080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 72076198 1250 72074948 72074957
    0xc090114060f0a2606010c080903010f140103032006072102120406050a0b06122e1a03010308033702030f060105030105090c090d020a030609110604050d02060d0e0d020a03 75
    0x18400c03486440545000c417003650005000040000006480300e024140b501d40c013900220b440210010030805582c2032580400300d0181c090010014103501683d01c00b500500700c800d410030315120721078043d1914030040ca41c0c403d0180144050402e0740114050501e108154903085441d10004c14403204940400d4030240c1c0c409052401080f164041032240081e00d003001031142c0d28004107104076070810400142070214080e050142d01104403052040e0b01d508140101c0340385400c604090b507000610103620061543c0c12000e10040c00081d1b110012241c000d032064050030700c0401e10b10f00c0d94006044105811a803613106511542040c006500554041d030441c100080d05542c842004684900092069680c403c20310008101a00140c0b0010146c114001c1d04c01a62605140c000c6039501c0002c0d0300413603c40d640d85c400d80080c1302c007c040301036041d00c0480fa4103140515110000d140c1c1000a40c0180c41200300184040c1c0e062401d40c4194000080d440989040220010707002e07444290107841900805e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 72077448 1250 72076198 72076247
    0x130611031b090616060207060509060a05010f0b0a0302090f03030406030608060105060304111318030903031704050d030c1b050705090a02090a0e0c072a05030c090114060f0a 76
    0x90341d1041c280e90403400058003040c10443da851080c00241c90844040d50314560812450f03000c42c03003038040c0c1403080005000500d56420140c2c640303030449205034490f42c050703080c02900f03201048041e0200c0303440d203000d40b83c00341e166051440001e8a0181c10003001c0c4e03041c840004c00007813541e01a00401c0850300014180c3e1266030380d4400384079a40c842220000c08e410001610b58002c0e20700392000c01030003904c1314400521112038494008003c01141425808100c143d581041090382c019100b000508103201a900320781825540c4646e280e4180c8084010325403111a81d035042032040b001100c1c030280002d607940313036400d1504289031107030b0342401858011070b1080300085030020310380210b440e09440a070401c000c0c2071034095051610386002c0e03c0350320101010008200802e03a0000c2050126000d075252400301690301c4c140440d0001a60b0100e40217820421031513040350381e1035100f03d0445001070001041c40306103400041c0d29200d4101b20390b540c1c05011031503004040e80146542450101c0c072100e034404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 72078698 1250 72077448 72077491
    0x219091412060402120a05010f0b09220204051b03100503071e0e04030504030602070b0f100608160201061505090f01050c2a060a0e030712050304060813061103 70
    0x10003994944101e42d0102000c14010f0030450320390b0000d60010025a0b218401664400d03007500c0c0703206414551191520b055130820f2070f004120740e411041e030304540301d01701c07651123581494500000f002034440c695810005180c080e040e1100005940e08107003880d92803502010201103a45140140c2c1d0080c0b040d000049520b0240d200e19400102184207041e000c10700d041c807880249a00204214100001030000000054a42c0045d15240d441114990442d1070503180e10014100020840500c1d501600c9081008a2700f101d045a0411020700100042c050311250690240005a01841148202450090001ea84000900b500440c04c943c40349501103040e00460b4039028541b46004580c00034003030f5400c9000384004141101c60004010003004c3c1c0c042e00092003c0c0c02294070075000c210703002c88112451a0900c03000d000342000b9a6803d042218503104c05550340114040d48084c011a503010074100c0c0710040c811700c50564048402d00c4110141c0880a0903508140c41e0b1180640008001103407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 72079948 1250 72078698 72078709
    0xb04060510020604151808090406030f080903010b0103020a120b15160302060708060f010509031f0f0b030303070e01080903040b040b04090c030e060c1312080307080a020c0703020f030102190914 85
    0x101c50610101d072000392421b079200c0b4442603021219140d8495a18040040000e005909035015980280c6e007840d201e0760201c0034942551900e0900c941018410002c4001e440c1c0c10401070051581c0802001070310814000105500c0c00c0e08100d04408820301180c4100d600d000012203441e2144254241c0e14551107212064403030301001c1e1260b56010920040d620120751080010303101002004044440b01903103c003560302140400c2c404c40050303039103c110312040082c4038006c1c0c0f6910311060f8011407a51603c041700800307802288583c02e0420013083c0200b20740311001c0042d02d0141a130b00c9116540c8540d141c00c010305a900c90310994585504092061001c10f010341701d40200c2c00300c0d00c0080c101507603852440307242a500011401c0c2100998800c0480d03a00e40b4060b190705c42c0c3c5d1003a100381741d0300c2c10501c4024021240051070300164034010008051950000b00b924002c4a5040d151b4245864444001901901032a28848200d950540115090740e6200c02103404680c0d2505111210100d10001d200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 72081198 1250 72079948 72079961
    0xa05070219030906030c0e0a081e1f020c0703050102030a06030209010806100323011806060b180108070c0209040308010e0a0e03040b0a03060806070203040501030506040506030d030b0406051002060415 88
    0x1404107003203c03000c221060080d000b68041132014500540c862a89200140b902e265903003003070f5050382c0460300c85258810501440014144100d00a1071424611074000c50300e104144848c50110381c01043c440051001007088001450340b050080d5180d260544100d80140260f00c01a032080240da800018900c00202e4801d01503603050750b8600486086464003002078a000c0794400e0034001125034a51100d4080c81050305c4007503507a48210300e22542e414180180c8280d0342002c070040b0410488003182c8841080d81040c2e142c0d003070030311008540d510001a260040018806900012210100400c2561150400b4161030164003284005e4595a809004580819980310140e0340704000610002c0b441c0d1000d000e02ca0700524001c2000c41e12002c1e11402c181d02502d9002c00340c1e2001c00c040c4440e42e007501445500020585d41044035141c030038002591000070202c1c1900b415a24040500540c035560403490103042c0c0071300082e282c0e41c40315500a640e050b04480640d071400c0c220072000c143d50304601542 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 72082448 1250 72081198 72081203
    0x60306150d0b0919030809010608010209030d030b01020a0f052d0a0215040b220b090603070507060902090115030f0605030a0210030f0f090203010c090608150a0e0a05070219 76
    0x4403040d01c41c1d41c403041c8140c0040c0410100d4410618152202985005001182da209950380b1002e401c08400f51401d4907120b811100d05070740184124650703620005a0074403462003e24002c90413950160050b800c05410403005403980156202c1c100c180200050a407a101395002414071641e20300301d550340c03441d42051a004607150007000281300580b400d80600d0600480c051107107441e05a031520302100c2640030741010111280600f010004d07203110814254000e180c40c002461802400324001810340c44000e01080034000301065500901805130310030350149074054990526561207258684100c80130210027400207052081c80740d4008014080e01046540c0640140f00010082c0c0c20880b5903500802d1640c1095070710041c100f1513504034060408ad4044440001810100900616095401c403c4841c0c0900000c1a0300f0842681e0017a005035002c5820710003001407803022000180c500e41301d6800111010340850910880c0c0d07411b43d100500441d1203400f03c40c89241074240413200d50000e0b0802 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 72083698 1250 72082448 72082459
    0x200102010501272705120f0f0d0b0a03140c061905090111010213050f060a020c011d0607080a18060c02010309030309050d09030203010f1416110d0806030615 69
    0x102c0703c540448064410780041042da001c80c420b01058100042d400020903100104c0b03401011800c01d119040c000c0c0122810711400b190310740a8a040d41207110b1154101da8024100c2c005a00c15122149601c034007a0988010075244145503241024840f03901031807600002402446040319161425400715940c800941c3d8034001840701700e40068465402046c00b80d030512a1000c1da00c0f20201080c070060641c410900315030f0000034140804c1c00807451180c15000c0c0134090400c0f203600d541c5d40019404103020b1017440c3c81020102e81034212070b040b55041082d59002400851140f0070841000b024000e060072542c0c031000202c1c90301c2c2900103801c4ca030344503420114002d1170a00c000b551080e0000c44105000341008141401d5540c1c54034505540600444005210741ca400d00071442c0c28001c7d500344405c6001c06002c01700551481c5200b0050241000b001610348003180300a483c043c4c9402d10b159210002a10704008019801030b24076a01120490f1103400ba0340d00045169104180512030554091f20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 72084948 1250 72083698 72083729
    0x5010504050d0b1f03061b0309080d05070e03070609050f03010b010c15060e01080109020f190b0d1d0304060207060206040b070e0a0e090a0510060b0f0f040503010603200102010501 79
    0x183c8841051002d04514404a4241850b10031081400a82c4008501c6001c0016498001e900a4039081d000b03c86900704041c10616031102140c21041590201d0f041d40c1e100180a07102c0034800c3d03881c290130703041540e05401031000010b40260402d46200440c4e2041d25001c00c2a22290105401c035081040e880b800301e864030095030f01190396041c03040e0704001c0150000034070544801507110b8a50b003d82c040081c1d60344501840782107003040031241210040c02e4502e50301c414150040c84000d0017850060307081121012801c0c891412680d084100701140d1180c403080c5611071028540c2d01ca5201e13000e040d0142c0320341500043c48620005005100b15000b443c075810030f88a0f07002c00c8420001c0080c0c0305074003030300c2e405002c034143d010905604e0050144200412800105107099410102e40e1041e141c00c643c6481010490f26420104a0b00d074412000c8404d6610304800001040d6401076403c4140c1642c6041004401c010a40c510b03080524282d98001113600c0c00503004909880c402d0143d882610100701 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 72086198 1250 72084948 72084953
    0x60501051c03050f070510061419060e150406031409030f04050405190507050418050c0a0c02010203160f20010207051309020312090901060507170702011403070c0302060105010504050d 81
    0x20b01610082c50305080b62442c010140d120750b07280004882d0502003a0765284010441b03002740340782899040328207030b641c102c01c1101e202c282d28410045211740e02c1881100d0108540380e03610f1210092084160481280d00c4545032a80203000b0035011004c000c42400e507001045c80410700000b0383e04004200e0315098641810b010900002e400040d01440c440c207101d10740031001b81d1040c000d035841145030740c1c0c0f0035440d04d1421070000c0c000c3d0161000792140328541024041c0c40c079074040072504480550f080044100b411480101c0c40c42c8140d114815404410003004c4042207540d24605501600602402144402200507046c41107068a06c0da409a4000b03103040000b42480e040d101460940d00703000089100240d0003280c10b1000c51500c1803c20320002070044914a0000901c40c050801460000d0030101d07681c0da512034045401071032040101000c504041160310800241a1034940c84250030344900780f4000141034900030a6049001d0700a190010589500c60746c107407401c540004103080300c03000058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 72087448 1250 72086198 72086207
    0x12108030601031d01020304060c030b010f050301090b01050415020f100203061e0a090f0f06090204060518130606021608060907030b09011107080c0606060711040203060a180207060501051c03 84
    0x1810204060000c00c1810030304901b84081c61040d07003c2c090100e1000c100110080441c2e201c130100905015801c50350459080e404010340e07054031050350000461041e40001a150741c0240d0307000b00f222a4880304040e01141e40401c9040c00002240304541c0420585200c50050b408122a0340382c1001d0910549900000c0311994507002c1034025182d44001c54460034048240c401419210745081d0715074400c0c0015201c3c81c0700e910000c202d0380d5000c40c00e15040c010010321511640c0a901c550819000c2804002d55a600441c2d50304c418043c4104100303a82d0782000780d1641a541d82d001c542440c001f400250040010403668400c070700c1d803005000c1040c1141d840e00c02c0d0711005000340e501c96585000b00c01c5d0b1500d60000800e0a640102000c94440b0300450a081c0307082c0c40208800c0c01b03000d0130b0001c800003e0071092100001d250803170780503031a9070784e030b40115003011801d61007201c10316010b031140c012180036a030003064203600884050103984e0322201442000040c0c64492030108030004146404a40304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 72088698 1250 72087448 72087461
    0x80d050f09010e010c05030c010c09050306010f0b071e060f181e080405040e070302031e030307030b010e1305060406080102070b130f0b071206080a050a030f02070902070b01210803060103 82
    0x141817002d80500161181071864000d9462820300b45e43d141d40c80401c407a000300c0310320014078003240100040d40c101140c120080710b05201d4885a44c202082d0a010840c0d40005071407020002c0f0b00210501001d030034400d001e08500207400311042c0c85c0600b1440511548400040003940004404074182c52380c5038911501c0c1451031040d40c25100502000c00c6030341d0380d8000ca440350040080200501070440c01010700300402d8199403030380d84007030184894000d01d0210540c1d600241c0740c24002001000d840050311000380341000590310001d460b5810341c103a540c1d039001d60b00880054a04010168495280c14201d110728003002c1c00785000b000000e1000381142c10200040d41c404c01011210800641d147d0b80968802d58215011481800840c0d0382c0e2082842a03e0091515500410203000245c40b16a100c644511020b410041c030040c0c1241064000c00110740200b80c40441195240c5190401000e0030b9020700070161003284940410790319009040ac07400c0000d400504413865510b41c1801174009091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 72089948 1250 72088698 72088727
    0x9010b0a0506090f1201050906060108041a060a031202060117071206050a060302060c0606040b0121050907180b030f0601061704170f18010f0903060b0406050a0b04080d050f0901 78
    0x1400865240e6640390104020388045d200700c008286403c1c407840d000c0c104a001098141004a00800c00c07011031001091038140160400d04486c171511b03034002254413003105400281080402c2c00300c80b00950b5002400c24102c410101082c28a15a11070810707440d014140b191541d10000c0300d50003804074071035500c116000300500c900000c4481ea00e41c0450700c03e07000303604c0641c2d85e50400b034204001c1d0304060003a001030300c9003481c00300c81c0346917200d681440e124518140c083e51295540006001201c08101907009040000c40a0341800d039082545006048515192030280c05032a0042844040c0014124103890007501c841e000e0040101d141104c428006000b913452080c0c0d80c10181d8801c4d8441d0050284401043c1241d6445000380140480f156013495514104507045914118940e07002540300140c0f07170310500128880e0603c2c00003a018241036009203901070a405000140104404014070456580000b034480b081e204a0703054802d40980c0d060001200000c0008500c50362080e01040003c40c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 72091198 1250 72089948 72089959
    0x160c0501050f040513140405030301060306080c09040308060d050f0a0516050102030a0f0201110a0804020f01021b040b0a051503011a0301030201090302040504050312010b03180303040f0b06060c010203090d0809010b0a050609 98
    0x800c510b00c11841b0007400e0380c042d107183e000000140040d82d494042c45001c0c00501d801000d030280020041408600d0003070014041000030400f10300c02c0c0c0e4809401200c0203410104a4070f2042003c5a2181c403001c451f2011212403061601100c04000b00c0700b0076604541058000c0c0d401d0001c03000f42620072840011005046540e2012461a49000d460103000d001c007035540e07a000070b850716205211085541c41350f1681503501c00c0000c2c21100c90043d41c14109a034003914040b601380c400e000482e4242200b42c0149901101a1000c1c054480c4124055030403265006004000c01600035003192940c40f00303000c040e002640c01141440503040981000c1e41040c40366080782d1404005003c0b5a50004c3c00b03030050702d0010000818000307444034000c62414401c1d49140510320f1420280e40d4900d441264400c010507a40f41c0400003101540c440302036a4816041c3d100956071b0385884105282c4800c202010000400c00c03010220302405014840d8402001001e001d11110724100350400245811140005a05c038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 72092448 1250 72091198 72091211
    0x11107060513080f010518150415200721020303061e10030c030605101e1704030504050405010e131103010b0409050a120c0b070c030311160c0501050f040513 69
    0x580c02002001080407202d400040e41d0305014150a09132070017034812000ca07508c00516031941d0440240303407640281d4046022400340060341c0081015210141c0106a070202004549001c40344070001060102e210b485c01040c06e503c100c000b214401c94000d81940168000d0001400c03c0c00d05c0312a4001c40300e0840c403660700010484001440e68502c02080000080c1c89040d441d451a4050080c00007410044030071605010900c07100601c20031100030a991205444040e003060720b030066912284d8041351a04100c2246401d0030302408a92003449400e001e540303400000520b944076501ca25001b00c205110082860240d92900d814410103030741c940754903550712008505650303224414940c200d07200f2009032000340d0060500c9070515030150440030131701040072140c0e4001f0302480104c3d9404012400c1244051a59050840013800d0801d12a031030490001039400e1008040c00380100014800c8100c88107441d11040111980c4c0542c0149400d00d540600c0180801d20300601c036000c40244c0c0d00400201c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 72093698 1250 72092448 72092459
    0x4030f0c0605010303020a170a050703050708040803070b040b01080304140603060a0e0a0c020c030105040201090303140403060609052203020c04180503040b04050918070303030f0b03010c03020301090b011107060513 94
    0x1181c401303900480142e1700ca4210030040003040c00c1c020ba814042250f42c181482208900030f0440d10035524010104040010004100081d420555015103056403c41c1d88403501380c80c00b40e0458000307883c2a50200040d50000482d074000000300e4040c0d40c0061000031042d203010b001d000180e0409400e075035000c00d1941c004592155070045047c0718041d58100440d0056400a020303082c0000460f0302030082e41000704210150341c0005040c81141ea16140c0003050051001c6200c2c550b000301d81006045904010300000c60a0780d40d000b0138001c4004200c40024010302c100e805c0240f902448008016800041c0f03a25403e242960148a6119990320b200c060758069548030303070450b442a0084044500003250502c0b0a00340b546071150f10071007000f90b184808940c660010350f1000386201c001e04060300d45c400300b01d640410381c111280e6440050021f01128904070030240103034100b4015207030380b00c1c44c10a401c003281d0b00c01c4902c03042840b94600600003c9040840803101d45d440382044098401030b00900060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 72094948 1250 72093698 72093701
    0xc1e03060a02030a0c0801080303040b041e051609020306090c0306030c03100e010b0109080a080a050c0d0e040c05070804170f15010503060c071e0323040e06120604030f0c06 76
    0x4540d07103000300182e0741d00d03207072460208980622140c0d100b000718074401030000301c000008980e04250007004059642c1d03101c1c0390181c810100188410001412294140d0421a0000300000c1c0c0b40802e00c0310315209600c60004d04101e01003201c1481d40f0607030002c007240b01d17121440019900000301a09441c031440c3e104001c2803a24000c171200b103d0a9070f5600c4440340b158020b110741030071000240b034840c1d000f9140045003665403914000261000350000303103040c1c2ca40e00034800c0300c1d8100720500c15100d00840c1d82d00302601e844d0301d00b6203850066041c0040d007400c0034441d400312100940c0c801c103030782c0c105401d01c0d81c0100705082540540380039100c1d20384441542c8000b00415802d002c140a40d244641d070400090500b400400741410120103c00d01080001420079003801e200c2140075029144e0003405c9040c00c440c40d4840c03003503400f05800030700c3e05415402a400700601c242c40303203612021116102c0e1014402c1c003800b103070703007001607a000078000c0380000707108030008601e03045646040703000032200703440b00b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 72096198 1250 72094948 72094951
    0x902010e0a0f0f05010305010b1902071d0f0f0705040623040305031b0303070e0910050a261506060d14070804050c01080403020c010c030c080c010207140105090c1e0306 74
    0x1e080008148200b03c4410b001202c40d020384070078a801c0c4415454111814418015060f142c442c1c0564085e0072100ca61003000030900034142610401d0882074420741854405109480d4000049030160018020b00100100c0e43d00a05042d0b03036903407425241800845007014405100c0182c580007207003098101c13070341c1c0c00940061402000955921103020003440481c0209034100c0b07445070000c0c003c000c0d0042e00001a40c43c4088103880c3c2c2c0f000f51761000601d1160082d15000180c1c08039545001240100b95502002030803108003242d030110602c5400e80c6681c0322140240d10340200c00e1070780010340c41d09101c1e003d09078601e40e004000c1045c0c8802d6111554252080300c0c540c0016544108000038054100901110b60b0300a0030440714505007a140291104003910f210303414816510a43d004051080d112a000c0c250030003141c0341c07140342880c0c0042c0070754040348044d40c41440000e80301d000c0c0326040c841c5a000303407195401403000700032030000d03c00700c0106404406000e4101ca10401510780f400d00011f03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 72097448 1250 72096198 72096209
    0x21040b0c07150903030e09042111010b030303010f0b09010909020403080909071b11030307140106030b091605040b06070204051614070206251403040315140a0902010e0a 74
    0x810045040144074501150341c90000d2040164140d810001709400c50703009980070745c0c20345149401e9661401c0c200e03c1210301c0b00201c0342d810368003e080c40340a688000400203851100000f8030505c901c1004245d40d070302080c0584d240014001204106151400c80200a00321040c1003200c034807541e4400800c22600700e603005940859001403c1c031a0f40c070b0f180c1c0009a204006061080f420012600c46c0c00208480300701c01003015010100b1500b66540410545080b154440444072803901d400c9030b518060600c62104031481c4483c078001c00c0403007101060748a4043e42010503081c51078a003c01f08806010b080040320b402110400444000d6240c4d4041c4034440c2c482c002c503136031807100c214000500c100c0d441c10340c15090f070500707200020044c1c0ea08001c5403003450a01d5170409880c07060003011008074201c0c100003405041c15170105044000d0110151041b24092600c2001c020090860704045e541428500f040f061895000620360324a20350000342d0860040c94158043c02c200300c04203070f0701003858004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 72098698 1250 72097448 72097453
    0x30f0503030f07050a05090f030c060408010e1c1706010507150c0e060c070b07020a0806040309081225031707030f0e011a0d080702030706110d03050921040b0c 70
    0x1c1110391440103005540140f0649405442e08030307800c00041c100d014803001c8174424080094070710002d581c01c0240039542d050083c10b02c0e590390b60b140d41d11030080180154010b40c1d4010502d0019001c0c010b440d414001e41341d69160103180082400c0300c0014040d0081407141449014480500441e032000080a01400c080d00001018004800c010300713005480a130861054100700403240e40c0c1640400c0b90000c81d000501800e846800500c0000d009025903000300e4000e100e6801004103169220f040401110104400d0b83c5107100c0315100291244540c00c10040d00c003c2603102c80c400700d43c056203079880700340c003d1518800421001c0b090000400080c0c031030500281e03d8030100c0848480601c520301000c0084d000030410001441d00448500c01c9802070715202c0e4100719041c4044c0055103046512440c0c0c000d069500003a11004050600c105081e0001018420719514080481c02881010b008810394401000003c0b884d141042d0002101c2804024a11003840f0014030014100090300c0c000e0740c038002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 72099948 1250 72098698 72098701
    0x10080c090108030a0f0c02030a032a020303040b0901021e1c0207030512090111010905030307090503031204080f04030f0c08011118060706060e100e10060203090409020a030f050303 79
    0x1005498668004815442600100e0041007603110010854550300410300b4a0b4480411590f0155814018070201030f400d8000c6440510405520100b03102c0d68000b1520302e0541c440c400b94104801c0b00303240340c0c001e4140c0d20411040c0089508071010344000c0d42c0500c112031220310030340101101c0200d600024074141c0d01070780000e548a0b00030121109811100e10040c01d000f8695101c8545c0d0340c1e800c0601d4800c008000411800c640d11030864819a40b81070301c000d000c01c01442ca8032030341da607000301c401e0000906105000301e030714a4084100c0e0118400a211030055032550b40b18002c0c03d90150036400c81c4c1c858100f000000050144910910282c012072400f030440b860112042e007500c4007906841c03142d241c200010310030190302030000c0b14040b800b641d20f940c403400185081d4004146542280c8160070540c1c080200c85107a5907950320a40d15148008080703501d03010b001400038105405601d01680043c0400099401c00d507000034811400141909100c91f42c903219200304003413400040c0c2d1550400030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 72101198 1250 72099948 72099959
    0x20d1a03060a15090c0915050310050a080a02130b190302031603030c0b190231120623090a03180b0301030308100f06110f0d0806090703020f0310 64
    0x20030340c08002c8050911a60300d2051801d1422655030099940c160382e50088103400b544601700503005840c0e841c04007510203c0d00b2002030250740003150b02001080c41d40382d0104040c00c02651110843d00c101d80101400c5000e07900300a58a901d168000103110703614611a03665556020b1002d00121a03081518502c038158018142405421a12440080c1440c8010400a40e220000b0740e112600031440151b41c1d1520940c002036504003805000903207002150100100c0c0401020103445d0001c04103e03011108603200c802c0002c0368510801d010300e00d129120002269142e0080500900708049150340b1140301607015045c0041600d207090f0640c07101110504050b0004544500300440703000800204d86054a11b0a4500c01400000c1c05c02c6505e0b00440c041d61071803400a40500b03039142280078601e485000041c100c910749074588031b040c0f01d00b01104401c840c0201e000740c4080810b036a0f207041c641c0c0728414441441e90241600040560800c141440503202c00c000c6d5018040c0222400021841d02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 72102448 1250 72101198 72101203
    0xa11070f0e01120506040b070513140108090105040b0106050f04031209030b130b010302042f0904061706070e12010f0609050703021204031107050603011d070f1202030a020d1a03 78
    0x16000f01e00d0503182c021070391010440c0003803031641c0300f070b4002e241034010b540b83c03082104d01d4001c0010035030180c0e61524001c2180944403a5032200410281e941141681c0c4425005003660016a0007400c0b140107200140143e5114000804e080d2201d504481d14003540c03651a034040c01d100381c0c80180040c0211070300340200010f2621850f04101c7e81483c80124001caa03c491307160b080107100080c443c80c1c1d10f05601d201140540910280040d01d480400c1c034115100980b03c3c1545d100c04a41446946031280c0802d180c88151410350808403560002c054640d9510420f9802c40494a0700d81c0e8402c142484c1d030340c0c0b6201d0902900054188510300801c007246480e5030b000a07240c0150401e01814014044090b4010001d10f03215407250b010302e04003000202c800d5981d400e1141e640c01c00b81d0841070000c00440c81d041d071a40b03040c90342030415060200903907462208440c0418604014000140100182c05181505401940e04509502c90042c5400e42114008080300c44c903c031a5141440e40d0000c0980300c0c0f405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 72103698 1250 72102448 72102451
    0x1c0f0506030703030f031d01140103030206100e061002030f03070207030c060c0201020604020420041e06110d0507170706090204050a060f0302040f0f0c020f0d0903170a11070f0e 78
    0x58000b00030380c500b9940c000d01010040210f49080655882c610703600504503216501c11070304810002c2220850004094070b4080b004d01043c3c02501c00c40c00851600e0b081d48141c0c40840303152802040440d1148001c009110503d01d00680c1180320600070402182c148000650141102d50002d221040ca14900b164440c0c40507071241d400e101c2d8640910b00580d0700412070744d6029034100c50008402d91040b070012a410748a00c0c4071648108080360103d1161a006203504242c030007260302e9280d0554544040740c4a49101001e444182c101c015521106030207000a488042c5c892005640203001943c15501c0b590488039041d00d1003038541c103868003541058802e503a0020003008003804100e007060080f944506146c40002c1c040ca69403504100800c409510034105403219034401d00c000344c2c0c10b0308004e60781e201402c8024654001d0114000c02107008104110881e40d0255420315000f0800d10360300c5254110781044828021280700715409481d0500c00700d00501540c4803000c4206052080603c5c0c0d5200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 72104948 1250 72103698 72103711
    0x203011104060f12050708060607061103070e010305090105040201050703080705090d0b010608071701051c08040306061a0304020d020f0f1210060503060103150b0102150a02030103030e0103020a0e0111031c0f05 92
    0x2402081c846c01941c480822944000700355080c940c4c4000c5442e224004000308101080852030100c14801e59682c000d442c00d000d440e0990f000d2101d600d03454005800c880c400d0710001d001c00c0702006484006805035444c2c40d44034281c3d04000d42482c1808000c5101e076441400105c65248400740140300381900a45c00302d41001e100e1070300d00c44480c030110642511981c180621441181400000b041c04000f51805a507242c1c0d00c2080d0a403941e03900c0ca4450091b00450042c2d0454020203c054001c0119070030949210745d070000c107040c500c144950280405c40c1e0740c09032169049101c4210711074468648011850619440720004c0401840f04400801140c81e103400c0b55109070800001000491401045c0403280802a40c1c005040e600c4100140d04e4400380d208408070580d121010030000800981c040c504980c001c0e20340c00c03101d201d5040110100d100f45080c10001c20156400e105031540b181e1800305500040004403450094000c440f0b0886000084c084c60b000d6840300d005240128080c080c0c0c580141c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 72106198 1250 72104948 72104951
    0x90402060d15060323012d0f031a040b04030309110607110f03010b010806041104170a050d0306060c150605031006091d0618070302040c05070309300203011104060f12 73
    0x240d040f141e0305d9840c0c50601c90354442241d1040f8051085807030310105001c818881148202c940e96500d50340d1001c3c2c61030b120541745020803003420400b0514844809125a42c028520862070703450369429001084081c40950304030303440d000711b0090b54407041c0c01042594014080d00d0a404010400c10a400010410043c081d034140301e4000c201da6004458550020700440b000b240d8103240601404482c020b6501104640404803c24048080b0219004009030b0154050742c6a02000300780a44c16505644141c0000440280e00d41002c240311826140c60f004141c1804128241d55100181c580081d40d002003003001d0340c0d03440400200909102d01700d018807804181c54041070031811881e441e440010031440040306503c049040140c014000c00c0090f5900900170000325544110080c401d400082c0d0442c04561314000103c2c1c03483c088072001071400703070019a00c0124160f071940c43d809031130b141204070b81642d00c495010501c005090007410107041c055551060490703a005009040100c001c03480c01308107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 72107448 1250 72106198 72106241
    0x5071e14010605030307030c0203030702090705070b01061803110a08060a0b1305132d0804080606041e0c0309060504051f0b01020303060f010c02030d030b0109050102031602090402060d150603 84
    0x4d450200580d03500c25054140044141c14900210381548202c4070700961018282d0b04011486400a0240000364011244500b2680c0c90301c106030ba4200c0c1502810541d80034840040001403100c0c000c21003a01c034090043c44080f55100440c07842c0501c03c2e1010603d040e02c812480b689420104601c0004100fa05402d20150404a1480c2110984004060320320a5a0650080c080c0740f2282c0d210541000e018146160004904001d095030b0458000d0841078000c0e02c0100b041031034036000d83c1e10000250b0748400c9140344003240400061a0201c00e5030145a20340000d9004510a0f2017034504c69400f85003c4d0039940c1340744655401001d0b01200356210030b464800c0c0d011107079030300205403544041709031000d074003d10001c001a142c0c6403c842c4025818418141154031b01581504015421602030301c4030325815450380c00581c0c582c000d05116007045170311485090003501d03200500a82060001d070a540c5000f06d00e0072190191041d4102c8994146013001c02000a194035209207503014603107907a0801e41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 72108698 1250 72107448 72107459
    0xb01081b0a150c081b0a2a05060a02010608060a0c030501081b040504020a091e0506122a18010e0c03040b040b0a02190305040c060203190f05071e140106 67
    0x9000603048642d00f00415620400b00300303c1010100d607410b242d00341e0714003004496940415518082d511080700c40c9059031350310b41004c85200c0e102c000b0703500c5000b00240b2030341e040c0303014031a058001c40110411507488001c00038014405006141c000c0600c400c0206002104540c050191001030740082d4032580007000703890260158240000b00600204c07004501a26940001000b8006a82111804500d0083d43c518011891291b00608403002ca10903c901d0346c9060030000c40c42c5e0404c00103640303908811120384500c0040c090b500502d051030318006141c4c4803910003056601c040100d1410851846c40700601200380459a201e0703024000031441469490301e42c0ea00300e0f10306006003005082d030030100007259820020f40c0540f804800d40c1e280701c0c0780c1d4180350b003c01805054182c1d001d0746e0b10070716584042201c51020044440ca0318070001c80302c1c1d481006c0303402117030064100e1101004000d420302c90030000840004103190b50030480030300448401894205014072212104010760140e16081d01080b2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 72109948 1250 72108698 72108719
    0x60102061303030f050c0d0605010e1018080a030f0305010e04080702040207050a02041b11010209240c06070f0f0f081f0b030412020f0604051504020402070b01081b0a 73
    0x240200441d560306042030582c54180e025141141004284038101350801000e049401c0190100e181a010140300e1940c0d41d10043d80e1a458501c1a51341108a08801c0ca00c041d011b0a088020208048070343e5034256501e0104d00d050280303a540480001d4040e41104400d20303031502a01d4054581c1d0b14080206080c5580c445803913110b01440207000340e0300418101c051140034002d00c0a00c0d074000d44280146001012400c2600c1d044110b80b80c003082d42803880d068004014400d807840b151000e400c072421400185000c4034510032404148240c00c00802100e2581c14043c4440c9005003601d455540b506850182d0141000c2030901c000c00400c00321340300000f0111f030710020701a08018840e6411016440e90300008016612a80008a210030300205000400c00e000340c1d03e000c10f84069081d1b400c22154850300300c0e08e440f81a40d000e0b0075580030146071000c004c130642200c3e0300184010300040c90888030f80c1d100150200241c0c08601550003450f03043d200015902030f10000c6040403529800001d040500d0541c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 72111198 1250 72109948 72109951
    0x507060809100c021e0f0d080c03010b0903070b0a0504140d0201090603050a111204020f0d05030702100e10091404090320010905030409050a1b0f08071803050c0a0e06010206 76
    0x41c0190f46408501d80e100d4002e1004070b5007519422038030032a465a5400c0b1980d1505100e6003410a40b0902200c20003080c07081c04040c1c010500c00549514692070070100c3d4a05802541881e540350203030400010301c1e160340c4030041603012041d4503055104c5180c0600700c40f409040c600300700c0c0074200d410203500040c4c3e4810b85550036a80b15041c001a180c8400001d40000d1514040d400548a00061104003400307100390741347d1055100b140c0b02c0d500350141400380b06001d41e40001c02001c030b52060012038014900004204881e0740b8520f0720141c11b80b100f0001a1500c0c0981400034041001e00c1d001b880316040f005400c00d4004020b64041c481c000b01da9500403d07024400c0280607010003400d980c41400e00080d0446000e60740c0140403a6152038031480d1040003014190303001e1050614000d100c1038400d900d4944800e400074962039201c4c82500034142501e201c1e80081810007000f2030303007146100d44441920802e000d94000c000402d80ca1490009101152406411140807400440b00b002401c0c0ea0014645 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 72112448 1250 72111198 72111223
    0x2030f0604090c0b0a030603060608070803040b0a030b06160302010b03190308090c0d03050a11120412021807050702030610050f011b050706030905010b04050f13021201020f070507060809 82
    0x1c0d90020300d060004450f580c503001540300700340000f1a40341d180d9041d0400070590780140803c00142d03a4030903865039160102c2c42205040d40042c441044042a1100584480111802c01160410080001818075801103004000c034540710018201810ba09210b0070080200990050060148407124201d14203d0b2003801010049048001035017030354248910180908064109055541c443c6005030040e084055800002080699040c010343d038001501001c203004441e0f107030701d840e0801d204140240040082030340c014400250240340d1180f003901e800d1164102ea510345446102c280304140c24054041c0880c5548441e030101808155921100743d107a0510900f801c446518000c0e4056180c00030191000c1c2c202d0064110001e55590160860b800c1144a10001c0140743e060b0b10801c4129401929550070044400001036030346910301281c2e20004d80000c0c00031581b010420010307400e9070b01c00320310090784880128840d0204001004940b014001d2400c19403d180f400c02c0003a0780d11884081207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 72113698 1250 72112448 72112451
    0xf141b03150a0302060d0b120c1302090f12011a0f0609011b050d020a030e09150609010504050d06060f05030607051614012c010209030604060b0301020f070b01050a0902030f0604 78
    0x9511075946030100d603001998090030303460716806843c11400060800d07204541c01400c0b09048084c4102c3c0c0403608400260b4024440e0301e14032014050040250000040729030400000d000b41800365990303100c02007000600a0000c10410815030700401441008160180103031400210b608180c1d4452003692012402803030079003001340c01031400800003140f40c40d014085000c6c001d5280400d950220b6000c0d040c0d80240c43e6081c1840c1528103204490b002252014040003409d80701103000d18041000b0200b15805250007420142c40d040001c40000400034111641a40c0b0581000f6810002d844c41c0000d00046010303002a10700b0301c4006d84144139800c03064120006926148040180950780048203409403c02040500291840e80c601c107494580715565505000c82b0007822a001402141d5040c80042d014105945960303980070003030103440400c2607140d5000c0c030645150f040c00e00c02900503940100405103c1e94500020b00c24048116006440e0960040007000460350702c6040c81c82e00250203460 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 72114948 1250 72113698 72113731
    0x30309230d0f020d05010c0e06030403050306010f020708070b030f100302090a05060415170610060e010e03071a031806010605160c03080a0c02041a0a06050a020106090f141b03 77
    0x281051000102c0d18025032020354140c00c4814008154003500300003140f40c5a07000c0005030b4004101b500e0004441c0180000c0341080015541c3d40306480380388082801f070049510094440740d03010305008a035041000b10000c003104000303440010740131503034124240c88011880c03d030540d0003084581d000200b03050085500c800c0455500e40300c90340f09003042605a1485100152180080603100c010f07550034211911503100402c0d0040255105801110841c2e140e803050001103000644481c0c0b11100015450f01403580001400b400200900420307001e1281c441e80e487c0341502c1c10f070405c00c031500c0300d1140c3c650110b0700511450b03400c40102d8a42e11401b03d030320440282136141c00501e8070a5908001e2080f03401050030300c41180c11a4121040d644200d03000e0000079040492243c1c030040385003410340d0058884d2420030515010750000c00b00c1482034800400c04c10780f00c56207903007918400102c2508059460782ca00d00000203003400c1a40044682c50b83c1c0380d19108204031440b443c080a40044040c801d00c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 72116198 1250 72114948 72114953
    0x4050706080c070203031201030b15061617040303030e060a2904090f0302060118090203070501081f0e011805090705012007120501050121060f1e0501030309230d 71
    0x181683c041c20390040c200c80c0e80b59901c464080c9000c1c1c0078070040302c07440141e01c046021840b41000849408401a20706420140d041840700c0702050003403400c0c0c54540f584800d85208108100003000558007a032404612412030313498807480e10788000c1409104030700d8008101c41c03210044075801c00c4402e00022901c1120646000100141081440141a02c2021680808154010901c43c9c12520031004a4000c1400c1050300025200c102d036000390b264010440611140d03009048180d004466030b1001510013404034540c2d0742c1c3c14403503089004603008d01e49c0100903032440d0007210701001a4000c402c2c401c0b4100240c00e643d40303010f94080c040c14081e01c8514024091030210301d00c078080c10701204540d440e07a91208850b084118562041d6801e50804002262590202d11103150200e03003040c800075900303225184c0b4401480721210082c04540c031717400489400c6401107500d240c3c0d002c4200c00060389500d1890301070211459603000070500f007222051009031160841c5003150b0b101c01640c225200e4016172 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 72117448 1250 72116198 72116221
    0x309071d0a0504031205040c080105010b0c0312040c0f08150606180904021210050412030207020102030a0309050109060207150f060b0a120e0f030d060801021e070c0e0a0c14030405070608 82
    0x100101703c0c40714a00410030051284c20000802115008030003040304d6601e0716080c040030f1150390320141d110750081245100d03414582c094140d02c240614450022a500d500d03103003805041e00d41c01004c10f03030304c0b07007081454101b40c115040b500003d0480f200c3c0c5c68441da04a00700311025038030014038460032858002600b5501c4c0c8046002c91179100c4403c1e5921391090740303000c0e4000e19043e83c050300c00104031803007400c1e054024801c482c90303103070140c0095091021141e400c81c0901005807040300c043d52202e03106400036809001130180302d84079a050005c818002c3c0000b0f0111180000a1149075081c40c400b0091100c14400302d80d0205618640004003414030b5001101400a810014085104100d0b182c3e50410700031015110b2001c3c0560240040c60391192200d00313034001e100c6031107000c04041074a0b6003280318490042000b98899405004c90307527540c503050300c10b80c6400c42e1000c90b01c1703403262422011107500c030484a90308080281024103600345a11241e41c0c401d1240940400e11000c1000301d001041d80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 72118698 1250 72117448 72117467
    0x2040b120102030907140604030314070606080d08071e090506070c050a1202090f01080316150609020c0c060c0c01030c110f0d0e01020f0a080310030602040b0309071d0a050403 77
    0xd240259940e052941a4a5a80b17040f84190904200445061444d0b403418104445c110783d056034581d40e8000e03095241200d1a485124210780650760b60000003500102400060b40307001403504c490b00030345081c482c041c00c0c50003203003207040c580b0800d52501880035030045a4502511002d0302c04544031003082c039201641c407511360442540074038410000134100980e07115615200c1d1003520b411180703884050803468000000e018040040d0000d1190f903009150000c8058074050081105584080300c00c2c0c4418100c900741d0b0441c0d0203041c3c00040240c0d241c0d4003004141041ca0042d12403030314000c90584006c1d00c65808007802030405445100000c0d07074038452041c10f00425020740c1503407090071900e000030340d0341c080c86070218021450794015003c035980040f071101d50070002c0002a03c080c44160f40c0d8020181d100901001c02802c0035440800400c40a10140001e4551401142d9072030400c02246441c04010f503010310b900c9049443e0304424204d401c0010b94009040302c9002c54a51a036281c242c59490340c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 72119948 1250 72118698 72118729
    0x5181b120c07120206040506130309030b0702070503070506070f110f060309010903080a0501080d030507030204080a051605030303070c0b070e0402030a0b0109080309061b07090e101103060d02040b 86
    0x9600144044001d403600108080c600c210400d6200c2c168600050340c46940c12580a8400d404c000006103804070342003807442c215031103883c103056196201c1d56062101181640c1d402c005030f0000e041032250741010051000179000440b41682042ea0035034504c81032031614880100050489014880c040d00e0354403400700654801003c20352689441c18050307000340741e41d84082d0001032082d004070f03d00721554421141030304d4030310340a040c0b02c482c924016009080054404803c0507400c00c00059442d0b014071400040601c1f030400ba1019a5a461700f540a03241690803480c0720341c1007041800f500d5074111041c24031071540031642c0407140e0768540054980c4619499030903006400041080982d40065000c0710140000744c82300c0c004d161320307031910507580e001301500b094201004210090904240018a0381c1500802e400c070b40200d80c880640d10260b03144082c119407240e22402600140c0c840358000c0b4850305640201032401c610307114000481b200854040a80201d030b440503141c0070340d11100a40b112151 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 72121198 1250 72119948 72119977
    0x1104030b040521030c03070c02010c050105070509010206010b03100501120e1b090709030302030d2007080717030405030f03070c170904060602010b030627061504050105181b 76
    0x41d00341880d54a85a01c8609001580c1c3c120728101540c500210949005019014070b6034156981c03070b101a60b1514070b28a0a80c18403021040c6013000950900407284a4a65503450a841d02941070001e0303d45078042c2c11048400400344104980c411f5410345200c1124802d1801c0b54415030f003001030b80000c002c80784802149004000310300c00e110031a40300030711811806852480d43c070340e144901200e044a45010080045c1c208110124000b04180c1215541c00c0780e0a000d03440040548919022a0744004011078110201040b03a10038401010009140d10058001c183e203540b41651350541c80740300346040c00400100120108103210310030011803030007542c0104c0b41a001c03e600341001f80c0d6078010341a080c3c400c5060050201e2450300c1070050383c0085d03502400504040d00d4050501080c40300034010080ea900101c141b104450204118160043c1a00300c507544140041c98280002d9884c1604401d00522400d1050440740c54800340e070fa03901c42c000c0000021a15034207100184240f181c083c5203090700303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 72122304 1106 72121198 72121201
    0x90906011112030f060f0d03140708090303070c0e06030109210203120c03070f1e031a040e0708070f05060706020f072001080108011e1104030b 63
    0x241c040d00240c0b12644084015226203800c1201c100b00c00240e50780600c05941001d401380c5220b070300161521840c0c050140c80c05003490040c4000300c3c8d11141c0004417a020b10a004003500c03040f500060aa9580b01164102050030308028000c0c211041e24000c08920b2915051007110900780e0f104040d80c00c001d83c00c010340340040641407906804e42c042007102103c444d074080f5100388195001c1c03164540724200107000409400185154200380481300c3d84a108030b54615080840d5640d4600e0040340480d10344070400c80c1384c102490b484e074025003032500039000180c000ca050820f50362440701711076036203584441c62607030007803184207454100c00c00f004003030003250094004005521602d08194a029443d64813003034155100b250400745403510034014103240d0307440460240102144402440440b408450341214010010941780c1550baa41d00c09415910720003091310001d50304007124010360b = true := by decide +kernel

theorem cover : BRFrame.Cov 71942448 72122304 := by
  have h0 := BRFrame.cov_init 71942448
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 71942448 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 71942448 ≤ n) (h2 : n < 72122304) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
