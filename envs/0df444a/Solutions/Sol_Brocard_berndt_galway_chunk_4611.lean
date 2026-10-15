-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4611
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:10:30.583593+00:00
-- url     : https://prove2.me/submissions/cfc8c45e-a284-43ca-a326-631be2011202

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 829136690 ≤ n < 829316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 829137940 1250 829136690 829136723
    0x1214090d08250c051632010503180a0f0b2401021e101109040c05040e01030209060d1a011706160305060102030903010f02070c0b0f071e0f030c 63
    0x41280310300240380b0010307034a4441150180500045020188034800740e4044107290680100c0c9204213501881c5484500184803240b058040e445d6240109076501124601d4010702c0060060f02c0003500150550950700180c4501400510943c02407a521044082d26442282000300d03050704145c61070a000751502052240060724004041c9a005060300a02140803050072035091003844c440c2c6400e010b005407a028840b00056105107401d200c070941d105030701c0301c40130800c0c403084904401e918424404100b20030300484039800141411658121504060f03651000080b0703900e400072800c0103217401802918039010303265240078541651505241001401c000203c1c8036030710307441a9034001c05e11001c0600301e22080e104c1d4000c035620030018011a8a48540640800e00310765000746200d0344158042003407800c100050310400000c3c04000c8181c2d0401440764090a128812418010010340710894415000001000e00c010056003007401c000000c0428100a0490700c0922001c40b91035020040901 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 829139190 1250 829137940 829137961
    0x40b0402151201260d0f1103181002071509090b010905060a03050a1508010203010f0906060519030923060c030709050f030f01021c110f07031214090d08 67
    0x524032810280406856441d10402c000b0f4005901c080c030a80070300301074948610031401c00c11a162000256100b001401080c2d40003420f81201007014900d03078008002000c0341d080b1403c9ea000c906241103d42c04040000c1d0601640f038090746a00c03103100181c41d005911401d58210b800c0b00c2c1142e150302c106002c0c07030740400e0045440304024040d031079009600340010b0300510321980c4501c0d4882c280030000542c818426107415140f1225500c440c900d40c0d00040140607804072111a0320040c40030607802d00c41d140c281007001e080382c003a03c6801840380e4030144c1c8104403540b09030020080140c100305c12480b42c8410300060110001c640900f100b061041c00c2c0401c40b440c490a007200e214100030b640c0c41900600300010403101003060007000da03140c41421806c0c1c03005c410a100030490190031080c44c10b04c02030155aa8404d41e94840d10a081100c400c0c4000010a00f008048843c01d030741c5403500e090a48024120440203142d05902405081c0d11502082039000001070741c0104522203441e01c000f103607030300310381c03003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 829140440 1250 829139190 829139197
    0x50c0102030319020913050a0e1006080309010507060b1c031b1112010608060c03061008010506041401020a120e0315090a020411070501090318090e071814040b040215 73
    0x2483c4118100300c00e02200100744e001d0002000d0003003e480581528040d00000d5600950394203c1682e52015240301903e0200039803983c4100c014010b01006240000300c5860703000d8102203506010b0001042c604101a69012050744440105075560165400000808a5003425011000304043ca0440c07004000301d20b0040030401d0b0310003000000750500c84213000480c1d4880082040d207649030003000c01d40601c00e101043c40780c05580b81c3c20780c8034948501040f01da030752809400d0050190800062000762158003c8400707480741e10849607070078164100100c1c40e106410a020740300c104a008800400c0780d10128110b4130140840451703060112204245192010584582d58694898103201c0014245a0060000004a031503100d040009a484850075103612107012030004045401810280640d004400040c10f40751800b088202c031007070005541e031b031178500420f0380e4041000300a00c429001038100141804400488540c182041d1408074915501545d00700c1c4194264094107800d0031820064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 829141690 1250 829140440 829140451
    0x304121e050d06081b040c0903080d0207050d050f16330e0111070f0501020702180f010b16030e0a090c050405030d0e0a0b03041707080c06060f010c08131a0403050c01020303 76
    0x42080c6540c01007200501f1015184001e200b4080000000704043d44043c050248210001503524041450030906244000b5030b05c1c01406000c0c4592803104051100351009030800c107283c4440c003101c5090034040e1191045101650405041d8041000075224401c0b500051001c0e40c107102c0400340740c0034039099603205e130206030150308140803134400701d100c0d02d4100f001c180c0a4000107160840b59004903d207070403605a01902e04007040280500c240c00c5c0064140184648000d10703041440500c03115111070303101c44c03001d07042189842040805a4078445200010440d0980400c500f6414140c00f41007500207101c1e052090190000c9034160a008892508a1075801040202d0640c01c0001042c01a0005807050314048181040701e00e04440d50030080c940745001d0030f42c454803800072450f42d5181242c004c0647d8000d504007092280c030b0b40d030001c0e02110b013907a010701c6c0d00d510341c0b40303907503883c80341e41c0480e0302c103224202064000c81200c014071305c010b000f41c07409601550303100064540107a030303a844140e50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 829142940 1250 829141690 829141723
    0x206041502010e071a03041a18070e0705180a2111030f06070807090506040b030a0f0911040c03020d0f092303030c0714010c0f090f03080304121e050d0608 68
    0x320094605c40c820700441c1e016229800c01052000c2115200300c040c20210307504003118503515859100c40208204200091181c0d42c1d01200381c1c9080f1500400900070480d5103041074003c42401d864907031b03601200f1005050340c5a84950b003003070041200305045c0c0042c4e1094510002c14003404c00942400320f0a0b2a40e036400e800200040c2e100d0b150221101c42c0c0003070510040001942021510740e0750b40c00280020f02d807061405e0344a08104020904035800c1d2400c0d107550510303240718a800a01c01207030740f00312400c0031500055000341c500000e030064442c005800e0009460803909002c61050b6600c003605240c020401c3d089081ca190380b10980b003140205415406038800d000103070704e107400400200446440383d0f114036034455024517400e00351200e0703484007400b10b4403d24804452944c030108100040c0f5200ba00d2007205440e6031948043c0d40300160000c1c0400944c888003001250003803c4681001d02c082045400441c03c0b40c000510b0f80c1c001e00e403c012281d041000010314548000b503031f103c1c645070240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 829144190 1250 829142940 829142969
    0x1410051e04021e010212040806100501020d020c011809061211150702040b0a1223070509010902030a020408060907050916020627010c0c020a0f080706050708070206041502010e07 78
    0x4400d440e24820703030f220f0641144210f500c000c3c20b200da541d01401c024a01034006001a04000890803480c2d045500403904541c0b00107548403d481d030008004210070400e00f0000a121401c1d402c811000d05250020100a0f0900800048008030404140d01c414052100d40c1040d1010f2020000c8034200c0300088109100c09101c104003502d0554403940306c0d00401404031001c103942e82c0344069000e000000075100d200700942c84100594518107980c0c004840540505081c50820000995a090601940e040c899001c0006201445550304a602031305468080b9549031030316902c1240d0705e481c04d0142900450040c00800c2d1301c0d269054181c000c0000c02d401414050f920f00c0c8000340d50f00080d003001100c2250400c0f4005800da403c0c8030b003880c030040c0350f40ca0000e582c9040c0148800300b030325680200c100181804003000640004144202034a11070700c3d10660340c81d0a030404003042d00824101039071200000400051401582c00206841c40094000b4001c103110044480d880b045103100d0140601c5000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 829145440 1250 829144190 829144219
    0xb070f060e03040e070507030e0a050a1403190c090f06180506030a0c120c0803030c030f090f010f020304060b030106030203030d1d1603020102060108060615071410051e0402 76
    0x107400074540802100c08503030802c0e684800d082c00c0c8800503200f0320041070000a0007818583e00c41d048900c0d0b410181d410f51445498503000c00c1483c016031045001d0303110406114011644c0600c10504200c210388640720003112a4100044946000e118010394980f406608040300000713401808101c0e104d50401040d500c1841140344050031005000c41da26009090042d40043c184090f02c0010744084002c0d02113109582c6030594420000da08060b200398418003c003c804002d0104507a0300c6120901c1103d040d0b01e07a191014030380984660700610a50804600307844a07a2654041e502c01d138003911090100d454408207050032502e00340400394040c0c10030410f1000300c980c143c003e680c4a40c4802d11080002c0001e440c1a41840440f9440112070019407004105640c0c1c1002030f1800761511501401c00d07070905ca000920403100503854142003e80110314079042c0b0100d03043c404003014151041d01c0880503003080410041004407055030310900796500c0754850041c81a60300d0b110342d45c090030144c1100c0a0b0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 829146690 1250 829145440 829145453
    0x10090507170a141503010c050c0a1e0506040303050a0506041a1509060c0c0f060a08132a06020d050c210417060a060501030b01052b020f0c0105010b070f 67
    0x61180b0812030722104034020040859110901c01c083c1c0400c40c0030041540350825094420304812241042001d01c01c2c28500d10001c40d0102500b0350002c07100c1814000755a480842904c5064060301900501080205060705a00310b1442450440c4080040759196401c0008465880c1d0055140c800c20003142d00c81c500703099040d9521345803c00c000700d0608080c1000200e03207500041e8407040c10342200ba413000080c20181421100014101c62090602d440070034001c041800007007000c4450b4a46c1200701c0300b031040003c85a407054520360750f5001c0c200d1381142240f82000d0640f0850006108504646003135900c98025241500e1284014000c0143c0300000e80b44400014114402030401c00c200004458540d10700c04510440c0c25400b80050f45010b442d4a0211200c3e50310081c180750a01000369000d030703404021a072200c2c9101c09092076100f50051210f5120300a03896882100c2c3c40021099100d0040c84040e04100c1c807110001c2c84140e0300c0c1c103809016809400310007482c03d99401441c3c0001000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 829147940 1250 829146690 829146737
    0xf0806040f06030503072009130f120e0901080708070501080621250f030308130605070215090d0903031407080a090e09010e10200a020610090507 64
    0x400800106541c10003aaa040468005500440d11a0300001d00b6804002c0348820042c200c1500b1110960002001008201d941e18010284548201d40c804a90308211400c9555003041d601310005c41a0400340385006010404c00440c070501c00d015107400003412804c0001d0500035540140081e141240c07415005441300711024010540c0315000700504980700440d04880d940c0315411100400b0954085c5941c01d042c0056041e209504c91102ca00500010110890007002c5903418644441c055075441c1008807007401c6078a0040c100c0c4e050905215072141d0008a114000300700746100c12558442d00380d03241d650402c180d072540201c4d540203401c00110740250040305c18000c40424181c604090342e921038106610180000000c5056178030144010b050028201c4d501ca11403030020400700c010584101d0340c0d103002c10100e400d800c2c1c039034800500e11420724405e00f400c4503c001009071903451050f8065210364044940b8810a42c01000008124465000b0301d4081c500f01d0302d0b121400c40540c103d0304004203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 829149190 1250 829147940 829147951
    0x24091a0a12051f020a1404050901050f1201050c0901020c04020304021e0604030501020301060221030601090306020d2a02150c0915041e171b060d180c1a0a0f08 70
    0x56119140c3c45403841021080554a03c8940160b984044080c050700c0d0781034402c100a221042400240900c3c0c0366400790906403a4102d49024840000c0070004031100030003e450101c075424001407220071640b01d8080c01a10609800361890700044205100890000300c4002e980030540f4101416112180009001c1d045c0b00a8030140c94a07803292500c50a82c0d1082e80058016400b401450034000a4404842801d14403131401615504007840001c00700141c602028040b243e00040c2452030000c41d900c401d0034200c01181c4600540e00c1d00020300c080f190313901003003405030055402c9584810000a0004c0c8100c540d4140c0508040c06901440040d0940c4044603040035010080400c584511200740a503084600c4c803d200054244460306c03090b10985001e0511a5002d80c1031803285400c84081141d000078140d4410383c80d010801c25100c054103031507600c2280c41c0c40c2001c0700010b00600d4613411003652041256003070340c1c001d82c00340c90080d44103005034000064041a800042c480c0306000d140e4014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 829150440 1250 829149190 829149193
    0xd0f080f0f160b070306030302100e010b0a500d02041805012403060b040b1008090c150a20060c120a02031e040624091a0a1205 56
    0x40c001d000191032a0340403401a051603800c1c0c240780c00800c000b41c40c0166000c0394524090100c10315540d00030303540c0d1075201c0c04460086d0303c4d06e0915080138401d62051402d050010302d440191540c44500b0807452003020b0419800c00c820b104024003a903e17110044541890948440b80b07030f060040c0704c2c64801c0c0c8030030140951181d180c1c4680f40150391980151046030fa80182d8001ca40042894003508480701d95112004070312080d060307070820098010707003c400c5a42203040400c01e013045a0005004101d075090540c0d0101164500c0030076107a03c0030410348106851400c03500c8024400d01000b181503110010200d4003101041001c1031144103600262a1852021703001d6006000402d203541040000c0316410340c40500031501440070130000420507001068032008616604020210b000c7c1d1409000d00310701c2d608844008501003082c5a88169050b031200c1405602c103003040c03945501440c405129940c0c505003000a407402807696128a481c403480c00600c0b0241191805a00c0c4400c001d00e1348041e60385 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 829151690 1250 829150440 829150447
    0x230303070f03051b15010602190506151201051303170408070f061806021317120a02150103050a020108060603270a02040212010306270605060d0812060109050d0f080f 73
    0xc0400c20004c250259161780f0031070003250f0404d08000c4c6446a002011441c00400302e8005010032008296107030010344a2860040000d82131010880d500d02c14100030150350b103030804012815030014080f40071107100b80c1e00c4160316030004d100003100c82010b40e0060000c550404c00040098450b41c0840715840c4100c1001c141403440c800b6000f4045030100e010380c0c600ba0009402d9030130041c1c0390300134000340c2128214001d070814070845840e5504001c40c400b0845040005254901c0c1c2e0081100c0b690601c0c4460b5460030940e10707441d0050311498042000c80c0858031060114071103203444426a841180e01ca5089040348045c84001d070403182c40d84130784800034007400c2e45000141c1ca070350000305040d0440c0408864294954a810b20450710b4120003403034200484c11000c1c902d0640d01400440040c1c125801040ca91540c4c800036910700d48841c401456500d0014000054078611070b0781500c6440f0988980d0701042d40e031030921050014941d402090b48016044800004200c0400b5100c1d04807107940281c20f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 829152940 1250 829151690 829151737
    0x100906021b040609150302010e040e03030a02070201050403020a0609061211070335090705040b0d0303020d180303091a100303051303020d051006061701090c020a050106230303070f0305 81
    0x41701d46400503409422420101842503580048414400e2441035400b00100c1070a54041900d070702001d0541c0034200c1e0005401e005582c85401540c014540080001c41042c1d07071000c0103041c14020f445440045201144030741200c0c04980300d44081c0b002150000751030103202e84c1d8200c071880e120220600c0c40220014800b03001000e00e404090207000b0040402c0790074181043d503589804540d6100a110f1401d1098420947c0c4603240c58828079580f50a0142e02ca500890840c4094414088620a2540c28a490009240d4581c0207851401e016108001c204052901c40354081d500072a280083c2c0c0c0244103041001174031540c01030a680003201b90100b0119101c0c5d0024140c00c10640c82a20a540429114800000d0512a4000400070360030841c05443e26150b20107800c0c001440346185441d074500076080114024020091841d51203002001840d803240d02262050146a400342414050001c06da81c95090000464450580005852a0891461341c0880701c1c0c0c1c1c0321400c8105000c0c1410301001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 829154190 1250 829152940 829152959
    0x9060c0b2a0c0c01022113080607020705030f0a020d03110c04290f03190519050304080f03160212190311160e0a05071202070302060105010e0405101a2205100906021b0406 75
    0xac0c0203005941c0541aa80c1c985010503182500400900b00345070041242040181d948803072400300c56074141890000d0f0034408008034200036091804580207801c21105040a220089010486440100100000300100424060500d0030200c1c0503030140c0c44804000c1c0c44100040700030290511a90072106c0c80788241d05051000801c04004603a140c0c070106050188101c00d00015075102c039410006d5080545046101b01c00c0d4143c604003a010300d440703000c0c0c0c458810061009281c06201003007203280100e00d614005121035480c040a440320b0155400703d60003418046050821607101c901d00389d01940303403414038500a0001414420070700ca6629022000086a40050842540280c000d071045600d000005807444002071440e81c4550b15000402a1480e841c0e41d044040d2100181440c1580312018506031140c40385040c580f10500c41c001188261108690350307403041d00c00c2036500d26410f00c400d00301600c011b1214000e40000d608002008101078001042246543d00024008118143c1d25860b54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 829155440 1250 829154190 829154203
    0xf0a020a09091802031905060711030a0f121503110a12060c030b09070807080c0f1608090a08010b030705030a0b0417120108010b01030b0109060c0b2a0c0c0102211308 73
    0x12040c501c44441b07840c081c400140b05250740001e80381004a0043c0040c01c40e15100d00c907080c03800040c0040058644d03c80c3d84200410044604805020084101d0300c8d1100c400302406072000321580030034920b2034090390400c020508110b9002480b1010704c0b10340d55030b03000c0180000c2d0301c1c520209541c411100c0307030325616680711901420403a101c1c84103c0c20540d074002c1c07841100401d0241441380030000701420b4007a0004071030701140501e98000e10003200d0301d45081c00e4031819214650100c040b800101e184007040d441001d04000c21000c860f1904e5441c02403607103480c1280006041d0070310030360004000c1440f9030024030a00c80184142440d001e144003000144030402c1e00702c0c074a943c1d910340c510780003540c05101d82c1404041c00d00b4240945441c001d80180300700c1480780010811005040402c030500002104c0368410104040d1910401d01030046800e4941c110540c03043c494840e0301106c400550000c101181c684503c140b446500c0303400c50510a070a40e00080d045440301d20348003030000311b181040c01103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 829156690 1250 829155440 829155463
    0xf19050a0c0b1c060302010c1209090f02091e0901030f0309090c09030605070c05101505120a031d060409050403020a022112031017071d0f0a020a0909180203 69
    0x85a2a200d00f115024082c50b66841440080e07840d0800901c0540e0b00880035000d2142d104500d44003640d050b50088400c207186503c8a000c0c45e0070520030580300521600a07210040c2c1c160362403c00c21884292561412015840399600490701a0041c00400c0c00400310441113070017410014000f594800c0f20808641e01c1d154840d0000305510024800c014050065941040261820162002042d210241c0b94013240d10600b040a0b59607144212400f800100704004003c028001c0c0c1c1c0320f44045d140f00f41c44480b0500b0442c00980d210070055002915050400080341002d80100c0c1003900b0507030917400030315000d001035080d4410760b102c0b0001695800c55002c0111030004001c8450701c4094262f618040440504440ca400144100008607003510416400c842092048120060090000c14200001d94000240113440511000c1416107255488e074001c6c06285000300d02540c500c0d4205049010724061140010600c0c8001c201c4654950003a020100b0412403502041d14540c0c0002d1821410800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 829157940 1250 829156690 829156709
    0x11703041d011a0a1e020708030c03070311070f12230a0b0a0c0804230a14120406020a0209220302100507020609061303030621140f19050a0c 62
    0x1404900f00c0700b1200500410511a420b00b01418400b0107032030000310103c025990140305100ea01e0551080001e0346c001d100c04016aa035405104610540f40e0348500c40507408903850101c064044480041e5881c00c448000c0848078506060001c6224040050030f02980c0741d070444416803c40e50070250400c0001480b8800a003803221440c43c00e4610300d40700a1a00781c826107080042c610083d0081501c0d940242c5c0581d02d418080006540d41c0ca640d00160303480c80f4148600c1140380300300848015541c80c0101c01c942261181d07241164503100354072079400f5050058002012003801820041060f0760032021803e80c19002e00b05003180c050703007014080c2c81600164010049074280807040d11800341c101901e0f1002c0c003983e203490b060980da100c2c0007520350350f000b0742ca03c901c0006141c840d034081e030040e04036000040120703c2641c0e0328a1012402600c140c0c0c03440d12206210704031010009403086c0810034200505078080c007404000754908200a801d9a06002c0c0188640006803003100c8400038024604 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 829159190 1250 829157940 829157999
    0x50a030f21030c230405090c0705030310030c1a04090e010f020a030f05100312210212010302090a05040b0105010e01030209030307060915020a0c0b0603030705011401051203040e01170304 82
    0x9000400788000c000913a80703220360200d58081e81c9000c100c00c41c0c0980e1010b84000d01c250301c1d00001c0d00740c1c602c1080c0001e4242d000200601c020721209444040c1140e010b85009202a51102041c00e00c016090301e401a4400040000308100d646540110310b00d1415940005205444610000160382c0041c50120000e0b50394403140170030000c940f01d03690300510350701e1032068558116510341802408000c419814403105c810140c20010070f00b600c840c11140103000540d107441c00c03950201001e11082c0012031141c04001c000540d068503611549208580051001c00e1507403800005446550a8800213410107400b084015059101040103040300c0d8801e10001684014608140e580358014012880c81a4010466030741e4190303001069108aa400c40317182207460702c6100000380b46200f00d40c4001c006500740031085940c03803225800a13040300c0381518100b06010380d0b0b92910ba03d074030950040f2117020030a10014402c083d400c503a010109180c80c4120791070581c0312030b10840006484d8490002036420071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 829160440 1250 829159190 829159211
    0x63403020706090801150b03040f080712090e090a110607081908251409030d08070201230f040203010603050328050403081813020406021606020601050a030f2103 71
    0x180f000e0700810060000300302e9189049090011106d5511508051010210100b8103000c203902e41c9400322a44080b80a80c0e6101d1460804071101e40504003101042800d0750004002c2c2e40480c000340318624034809060a211140e84600c03408400031a0140c10842c00c1c080100064041d50023400500a940080c00c2038a0b0403c500030041c0d800100300d00d0b420300700014800000c42c030281c440c03c07010509040c04030b0481d59410200e48507000e2100d1050381403240b420340721005a000001140280c1daaa4020301c03c038242d50050308009035008150804506140c0e0005a0450a00030856000b030b00c000e0000c10745942da40c48040c80c582151403401d00041c41d45c440c000b6083c41c0441034038010070480c1050f6042520396104c00700c0501548100c154041003411503009a80d035480c08400a10700952021074480b5191031009645201d40c040e003d20300c0081c000086482800000c3c058129030740100703080e440b0790071581c4203190320300c400108403540e600440c10a42e40e40c040040c240014101554005102c8018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 829161690 1250 829160440 829160447
    0xd14060328060b040908160308070302040510111501150905030109110d210216090b0906101b03111b060a050a02070b07030e030f0c063403020706 64
    0x7000504480940380c00299080d0364565418184440e0000000207079040700e4000b14014044000c1c00901e19030f400603403501c400d6022109010000e0203552015169602c0e050305400301d100d24003501e03502031a0228030802003840303000030000030404c0c141500c000b10282c9140c2c00c2c02c058280c003d82c551030341d109044120268041203550085c001140207101c15002c9449000407a09800c507800c0c01129036550300401c0c464801e02c0304240d4030356508207010b603104044d070081d05ca070351340403100c00c0c8000103281c0062080c00901500205107001822408291540f00400091241180303c1206001e0300c46809101c0314146c0d902500f1036400f82d2119031460782021489403c10b134000101c0221005000c10403441915580c00b40c40006d070b01410607035503511480302c05a26040480e40265a004000a0864101035211802c05480042602103c100300401181152224602d650303480e001030342030210a0402c642940c00403041c0e80c0e43c001c4469407a03260011100c0c4080b07403450660140e40450810000e290380f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 829162940 1250 829161690 829161703
    0x2060f07051b0a03120c120201060f050102150708100f0e19091211070e010b0403050c0319063206010e0301110403060c0e030a030c05010b100804020d0302030d140603 73
    0x70b15880d0365003800e40c4002030300600241c040034108003800314520901c14042c0b80c1e06d0480030703000b8a98007000100c25034000d0180025025040e5101003800000545d0750000407009504203090f07501c0b10107659000d10481d1500401403100980d007042d04c40004025984001d0000508008020300c060b42c540400001e9907181c40c0c191120300303941362245000100741c0021310401d01c41c1d40c1d0301d448058204029025171800001d600305c62092100d0380000103203214110700501c21a8840c0f01070310f840000e800c00305a200c3e00503208a10031100c0302190040011060360080340f01c220210b50401910301401c0c442301144118190317007926160741c481400660f60b0000c0c0b500d050550308400a009540c101c0720140300c03d00582c0300c020107881d103a072034903425180904600810854068129031591035141401032142c043c856095a0f254a081000c10003030030808580078144150340c43d090f01d540c580b035091010f0580d04100c00d0302117000a0046822054090044800503c05088152030a080160070541481c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 829164190 1250 829162940 829162963
    0xf360909061103010305031204080d02040905060a1215020a2309011206050d020906032407092102010c05101d06010e0f06010f03110a080703050601230c030702060f0705 74
    0xc00d00040002906c00012240604a14000304c07206469516080140780a40c030340c540001c1d4004a40400d9005060380828800e21040301c0317002c40c01d82e44282d086601d10050001070914041461003484025682d00105240080e500d001114584000b110000d9420440c4601510038000101011070b5a440240712a100542c0c6404000541ca400c001820701e03801290000e009040301000544555800d01001c0f01100e500c28581c4111441e00b94103c030354101c21240b42011070592480407520420101c0081000101510f00b0f02400440c0d8006640311302d85880f044502e0f20071a0340003110700c9501e010780050914080c202800f0556403484560a0090580280c201a22050704024000c00c2020645800240070b02f00b1004800c40d1740c0085024001102c121040c02500050640c84c65601042e03880c4100c4081e541000903071140001151940180e00d5181000e4075000000c940300060600104450044c01302100c0c607000300c61b808a1003942000750302c80c0c140040800d124003445401e0080701c0904 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 829165440 1250 829164190 829164221
    0x120105090a06180b0604030b0103030507140c03210d1e06060219022205010e060909010b0a0306021b060c0d14040804150e031f0c0f36090906 62
    0x1410010302d43c10060080000507102521040640140c0e103911040320040d541041103e4001e68503824040c00390350124000701c0e240005c4081c083d5100384049840020510700801a140c01c6010003082c4000050f95441841e01c010f082106407410403ca104060610342511145100c240310340346450201d82081d0f1101c03040d501b00c82c00c041807041e41c04007449130043e07044801810105000812000d50384914640017241450040040360907011001c00c2403103004101da00016950b1a08180c6084e0343c08038091680001e10301100744001061034000d040601080000182c0066032558802e01d4900c081d40c03c21a0201c00203802c00c070003003640c00b035001c0341500508000c1e0681403071744d6021018815840360307601002403002d5032513840e48101d030171442c50800103044840c1d80c5084c00514000b090040000d11001b8035000d8004140d40c003c0c2d100b0024110161a842c403410012400f04603e08001d50780c2c035240c52030201107400c281d010703d00c00d02c0241074544000948039644c0c0c07405e80c007120000800100712 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 829166690 1250 829165440 829165451
    0xf06090c041a120a08030703021c0c0503130201021606080907060203030c07110607020a06080a0c110d08040c051f08010f050a06032c010c0311090603181002120105090a 74
    0x2982d0003071460010b0303180076078044140300421a4200c4c1403000b1550010500c010000901540e203078590003501001c40d58000c641840d080c68410078044134811030340800810018000580e031303600d40f501c00600650060041c0c4208a41c0c03984c001680083d503400000102d0400c40602000300c01c1000341801824071030009620314146040d580c081400b5041c0001c01020202003404480e80f0340406442401e41c1c090001d820442d220100942080422102032640f5894200841d10300d0b44104022000c0c1d040000183c04148004002154011802001a502050540e40008158584810642c1d911250119414a980d19904020301d4003406a02640c1d04c8005450144401e03034401042d0b0f42208d440c0d08000820a90380180d0845a90134080100d1041c0080c0074101407058041d080320303451424580c0c04105826034156014018040d180b000e58106c60248000f070f00d85210001c2012408400d04216504485684000016a40710145002d40841804e00400c090300b4104c044903040b5802500501c80c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 829167940 1250 829166690 829166711
    0x201050c07020a05060325120c020105150d11210708060115051c0e0d0306060311030f04050f0109050c040e030a230702120106030b0c1306200f06090c04 67
    0xf9a900d96000d00c074481d06000010901103d17980c10502d084950040c140301c8071190b5004083d03c8a5401003448000e1810481f032030040303601c107108a512610030900c003079020566500602c0340d0350f02c80c00b50444407030241000c529695960180c130702c40c0c40c400c040c0040d100c00c83c4210b075050800c48682d205c2215680050014401448204c10b00d080b400c04928000361a0501004400c00784074400500c41980c40c5864607901640001003608092903480351010300c6036590b0780104900720340c002105644040d405002003400b41c100c0c2980150002c4c020800c903004901941003841c00c44a400600301e810f40e02c0070041d413496080034042c05890401c45000b031400c1260103403001e801c06003105034008076901500e00c001c08880d140740982c0d500720340141011091400145046000745190302050302d002e6078400c0051115400c5800f00c3d40c103210030b000c840c3c1c44a8a0500c06542282680e890030b0f48504142d007500085000422820145c0041c1100030142170810344c0d80541842c1500c40614056800c0800c2d030310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 829169190 1250 829167940 829167949
    0x3010e03041401090f0e0a02030c210a1d06060f0f210c011e081f080105180d0c06020d0f1109010e040b010c0b100801020c07091a011d0a03020402040b0a0201050c0702 73
    0x213501403204500984e40e95140d4ac8007001c00c1c070075911914036010171484141d000545414003d8401c00e0310075401c2205001c0b076010b0703c03000c1c10400e0084042c0d91141c0000b42242c10021460a25514060711410048102e6400100600c4850f0b60350b03001030300d0710381c5d03601d0011004018422901e002800c000031240409408402900c403100001c2c42440b41076404940c03440550707041d252003410010840742e03529441c2c40100b8041d0000340e03131800944a4a40001d655094080750746001a41c4a440303142d6402c4190351744138043d4005c82c103000301d183ea441910340241b030214020b090a5000d14050107a030340300d1503c001340082c10296a000e000760715215651400da41c1207100d159680f038020141482c0c6549800c400e04c03103c003c0d6004401701d940003103444440008005608003d484503042c050100032400c42c208406c3c090300b4426a40091049010514030103803182c80c0781c6054074064800c211704c43e103a4000c079090703a01541c0801e002c0040001d8541d9001e5080c869250482006100c40386804402e40005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 829170440 1250 829169190 829169219
    0xa0314040b03071d03030f1b0609070e100f0906150807140c01020f0705010c350601110d0f030b0a080a0206030711010e0105101e0b0903010e03041401090f 68
    0x43c1c02e00182c01038041551150910b000307541d202c01011280e88103c041c1350590f01790000300207001c00141c01d4402c260800004580c0038428695030703004020091400000c895014006400400614414813020841c85982c508800c042c00042201003050361801150b0548400341c010b6400c10000040c0c288262203501190345001d01d06540d01443d03c50100e203018500912030907490503105000082e18404125040d003107500701c034140c7c4d124004400c41c00800445045410b007821128000b00190749240340c42007e440941090741803421002c40080381080034903000040c4811320102c1c40d85191900100d80c180a101480d000950b070030f0347c40e14901265141c0e202e000c140c009108440c04800940442e1048000d200700f101628024007201401180540c001c0c4410b07500d4454549176120f000c5845548031030352180b6032124461610610340b403c0c0d0260200e820100c40d20b0b501d0754855403500000c00c020406400600b8442c004a40e115000c40005080361580380e0181c00b8110103a10100031070795550540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 829171690 1250 829170440 829170451
    0x615090121060f1706011a0702010c11060706090507050102030a0903290c040510030c020c010f0203040b0403051507091a0904020904060e07081005280e090a0314040b03 74
    0x180024880031003280002c0e060a07008441c00d40003808002500300401d510108003056540141d421030b90700c8200c4060714858101e200e18001a040150600551149548840d064041d262181480c1618000200b803507101580c252000e07902e84080105021060004c00700804090004500d00440010003170302181c000d02c0007600c44044068064442c1555108810b00f07200c49a68080c0c40d8074103042c00b51f0030750700640226030040000c94202041c55011748a80e220407040e0307070010309003002541d0045a805e100d0560310803c5020601000030b0509000c8060009148154060300e5a08903822901c415080002c2c078141c10410104010003030088a0012070410804404005698400b801e003c00d02034030928000c2500585000c0e00004e5150311303c004640a40200e580e01c40e030036201c51524030840c3e5403600519510410250100501958064140e11010446485c00d180540e54000d020900b40c4110380c0501107412410301141010360151150581401c601c10003800d280c280703081302c040c90000619 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 829172940 1250 829171690 829171727
    0xe090d120b0303030103080a080a0207080313110402181816050a050c16050306060d17070f0b040318080f0c040e162d0b030a0504140d050306150901 65
    0x4051000c00d556008201620009022030b9507030359580c94028483d40c41b00300c00b6000501c4482c08035035046a240200c501e5907400c90700301410b50b1984403110200c0c7c003503401c0444202c0c841c440307031050f070382c84078006804114110552003580908820a1000c0041d0892180704880b00450800c4507a0a043c03070203000058191409903220402500d0aa41c14841e0300405201841074019020412f56600d043d02c040e80c0d41902541c405407601c005001d1900e9a101c0001c041300d01d80d200203040400c043c2d0241004034040c1d4014501c0700c00c030f0340711400c400740309403825070000300d400c10080b80c510102c2941000801019008080d58062100407a0701c90300a075001c3c510582e142c58138030803015010030070084a096002c40c1c440f02d040e40d54844203e200881c01c548807400c205003030301c0c007010030341c0908100490344a2103070a4519a42c1d10b0585d0000c0c60020030072525006500402c5da2040410071041e03081d6200b070b40b00c41d81d90382403c801b0040034040e110708080c19000b00304540360359079a0007803080420204103907 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 829174190 1250 829172940 829172957
    0x109021003020901090305030d06030303110313060e28140f0c010e060c060702010605030709020a0504090902180a0902010e040c0e010c060609180210020f070b070c0510020f01060e090d 81
    0x100125200005d90f4805001444003103030040100e14039078021800c80f8840d41f003c004503058648403040c1030000722040305121449a00711000718009802043c540502001550040014850b4a21442c2511603410800c102e07880c1180082014a001006c2000c4540c3e008000103070715139114a40c1d80002031a001d040280141004510f078032a90152103029103d18199000c03880c142400030300822031403180e10710a2180840011b01c82d03410b03208403680040d09540d00d510b41400e041400014001844040760450b0000074010944044065114000d010000021524181c0303030000600c00c00c3d4044401303100703a103484010a1019006030219100d6031b401c0c00c00041548884c00d03d0700007421594862010b02c1d0804001c5985090b8003d08030103241e1003160000f400c0d07880418126030f2040c03100041000365010183c1400b881c2c081070f001c0d080d0580310710200d200d1b482c0c8680118040300c211410840141c0c0c803002e080c0b02407160038020030003c3c0034182c441a200303191500f08180c4e034240c04802c1e102405481c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 829175440 1250 829174190 829174207
    0x9041407050409060b0901050901060215130c0810050717130302150109091511030c030a0b0315071e0f030c090504180c060207240c05070306050a0e010902100302 71
    0x180000d0303000740801481080384030b05604181000c1c0ca8841020392048101d000041000c0c503107140c1990503545150700130314850903040c0600c52804800303005850650011460700e000140b81400c04d90251003180060001044040851419100060034520a000175185050050580050013176440035040941448607280d90030140c0c00d005440c040e40031003840540003c11141c039203411000d019803190302c0b1901154160300240003294504010001e07080000c0012076044481200038581100300c90b24009420400e03240000c0c98081812040426076000b90f0820102941004c141680c084440080315030010080400038900d0b0b60302c40141c1d061554030410183c1c013074031034041c03800a80805001080010b40e0014034042410f006402121140b00224011070814400b16008080700d4110500710344c2c0c40c0038400020380f803800100c60340082100f40e0410f0000b08004121035070083d1f001c2d4400288500f000100d102c00d4591070600c1102c0381e03062490400040e240e82a8006080a00f8680140c403201c1d034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 829176690 1250 829175440 829175443
    0xf080910020901182309130311120c01060512150a0f1509090203010c050a0c0f082101090b0307050f04090204231f14040c090f080a0507050a05090414 66
    0x140c5040b586003800302002103030880c0000360030180c000d403806541c40305000e110108600541c04656802510079550107c0e00082d025040061445220805a40c2c2c020180c1d510403c1c02d0b01b20184090b8107a460380d00400450070300952081d4488500d00150405013141d10f1002c072130050141000c0381d060b59030300a0009080d0198000000c1d91010400f54403c1543c44407004054400300c80164825481c08003502000d500400031248150724585824058248944500c05100b0108100f6030780c40c1410050759402907002441c0f21440300880001f401c003035041c100c03080125100181000c0c0130303921243c024070807a03071454510300e940c2c481200c000c6544030151010030090140c0400c450003030385000d2814403000301c1716802e09120354508190f018002c90f04e01c00e2541541018401d200d10440c1c505d080080742c1c10b158104c610b01d0140d07410074140e03da50340e5030f262118074119440741c442e80d00305440c9001041000d1007180010001212074101d490304100014440040240000b040900c036400e82581441c1e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 829177940 1250 829176690 829176707
    0x15010504050402040b180a152625080709090e07030210050a03230406090c030b1504150e0c0c0c030a0b090606032803020106240f080910020901 63
    0x8000c1d02c20341d100c0d95510881c201c180c1152611082043d60203010084500301030959100b00c604141c0c0c1140040c4240d8029641641c00f05a82c40700c030500510600860454001020f01907403501500e0070540036240c015815800701d8a6400f41000000c5060000c00742c2e0100c00d00041d1b84400c02c00041c660741640701107290008a9100a4004010402c0e142aa5420802808115050303072000c1c0512011102d80760300c20000200b50001d8031b40054040350220300207074040729400d031040c0080319070241c503030710f0b05034040108617044180210201c60700c40c60760600b4000c074001c6600003541c108000d410085005050b10000303000c120013100208800b6a841010002c2c10f20082c409029500000410f080000302c495048400400c00e201d403c0c007040030f60500040201c900003000e005c00ca8181e02503000d600c180c00070f039003080d0219902c030348000c5004002c0040c0c4007408410b56681d61008a0a150b0107004007d0050207402400340040801a003a03402091410512a181800603620110000107850020703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 829179190 1250 829177940 829177949
    0x5190b070e190303050a1206030201020307230708030405041a03060105090405101506260408030a0b181005010801120209040618051e0c150315030a030f081b0315010504 74
    0x41100d000003411781050062240f001c040e901c0c206001c071040050410795400340300c002e0050b802042000c1c0881c10442182c0b503c0b041001007a10710012440c0081d24060941d080800039800000f0200a00d282903ca007956000c034040c1048001c544040c00a1f03200c0c1c005103e4140035810f903c00080821000b80720b0004117a9540c0c0b01044103c5030b910248034042283e00442c008541010030100325018020616208491103000900381035499668910342a0409040c2c9840c10380c603101c0c4040181d40d00402692582c00011458002c1e00d04003c030140c001840c1d92095041c41203400040c40f054110300b0b0f0300040c4540507905c40b005a181c500e07080c402440d422491200c3c070148440a4010008041a10b011419001034003c010500251a258440c1c20741c0d0762059000071003400391800c10a810014540c0300e00d41000c00419078626002183c20310b40810021400a40c400c1500300f4082d8010000c0b81c0c0064542e500e8516007001100c54040d10311001c0d00c640d0400c2d9904c1c80300f202c282e02c2401120090b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 829180440 1250 829179190 829179229
    0x15090d020303091c02311d0102040e04020a1205060703090201050d0908031b040f12050705220507020304030b040807300215090a0305070812010f0305190b070e 70
    0x40e68150342c90340c80980b403d404138410401c0c481890120942c049a0009211b0000c500c0b0b818546c1c260300050040030300724811400e03ca4941241c002800e000e1025000418407014032003d1850030744100444100b5582025001c49011803107078010910004186038404c80c1d0f030900003281001400141d546000c1c90a05088681c148040e0744200a5000c0146000c1c0b8143d0b01c070560182d0b0301c0d82e05600b05005600950501a03400081000064007100310641f00c01c1c002ca094a035440e07212408205032005040321004000891502c9074003180441c0f0400f0f900186510280d400c0c281565030700380840c5005407006d0a60342c00490141c05000084800c1000681c0540c1e4010f0307131102469070002d0b2401e840c00c4950260144100d91403d101c0e03800300081c483d034400030140642c181c142d90300752415088500c06440e016014450b0300d00c0122015135803800790041603c2c000c080f528500d004e91400300c51403904d034074200c62041840c00064200c2e440581241480c00c080b054800c40002080d042080243e400290 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 829181690 1250 829180440 829180459
    0x3161106070f0e030d141c1b0914010c060b19061e03060e04060c0504090c030b120c0904060203070c021c0b0907060c0314190f090515090d02030309 65
    0x1560b400254600c510300442c1c903030303c01d80d80ca100205138035030301c25400c0c8001154990441c90200900d40d802812100324000014400c41c40d1401c102040329113000c91b070b01c20800c02905102d045500420320100170801d199050b000c00d040341000034842c0c07038481070007001e01c1d407950052403840c2c1e90303814904130301065440d0031040156240c900030411010901d0150002c2d1640b02140c03100341c031a029010907501c10010b09000c6484d95524400201180850482040380074040450900254051841e10741e980740e40114600c4074080800c4417080e0050302644141d03101d6a501182e584981b404190300035007212005032a56500c06060b00d1113400610000c2d405004240c0c510050b10300002c0125a081c01655004902da0b5084516599003040d40500004a0421061400024460344c1324a90004440d07110710f0406006a1001201c580c03562248030200d09942c03912a59140d0081c0c852009140485003256400820b640c0c4c0540c0c4d203d1031044a0091150a100005549080040748c1c0b41c0b54014001519 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 829182940 1250 829181690 829181701
    0x4080405090f010f14060304080d020c0708030a09090513110f130906060b040e160309020d050303160305060a0501050c010902060403150e01140f06010c4403161106 72
    0x25414024000c80215078813034840481c44404103078000f0840d11016000520b03545440c0c40381c4040b40c20100c041c4012903020031156000c0d5000340032007070080070b0203c0295115a02080d002d028518035400c00c005141c40e1800b086041c29200000074030103034228460704410482c00e0081203a243c02200080c0d00300858001c00e02c5140c03016405400c402340155410409a07483d0b0092003024411072150750400351040717000c22013600c0032105111207418142400034008000d80c1c04140c0004660805132000c1e0000300c200140070209480ea0b01e2202480c0ca020815840c001e000617001e80040e0003514100040428041c0c0ca0341425480740c82c8450b0002c00058460340c1d60f20380145405400350b01202040e0401c18840051134050266040c0910a10038200c0341e981c4114200c2007030135000344898100401807070344001092050302c50410030030f061a004a40d150051040076480d1684a810b003040b841c2805014002000306010307241c0040d0480300400010312030503822030744885000c480c4003250107500d05009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 829184190 1250 829182940 829182961
    0x80124150309141f0e060601050d020d1802091810020c0304080124080d12050c09090a0507020f06010b031506070507060c03200c010807020307050709050f0906041a0408040509 77
    0x704031450404c2c0740c8400e82416100c80c0103403111800d034003905a04c1000031900542c021000781009099031640142084d11705502c001c25945003401c0c0b00001c03880e1400d4031056042110103e544403207c0920768981c04101c1040390360380d81c118650b0082d107a501042c0c29031003400078001caa0041103484000c5c030a4003401c41803441d421840608034210716603980300c0060020000706405803400f413161510107410300000c00c0c44000e030400400400d0f080000700f200d1440c5503607901059000e00c00c0214001824540002c002c0e2418030183d078a0a000c2e444032004220228850b411070b91301c40c0c041001c01e410030b80c00c507011810341d029082c0020700380d020f040ca01042141d03010350310b44181da0090f5150b5106030b102c50b9107288201c62000c4100d090350082e10f4480660750050391040c0d044070f25441200e2038a030850b10307076909011040c1c212224032515481400380d8544400303023540e0001040f10281c030307a80c200341c0e03100e540d1480500c039120070350450400041c0078040c610741034900070100038007107064501d0315199030b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 829185440 1250 829184190 829184203
    0x105040b0901061d0c0a050c0a030e03010b0609130e070515030f0106050306010e040902062b110a09032904030e0405010b0f16060f0e0708012415030914 67
    0x28200e41d8603003030000481c016011013001600000d007071100200c0c0c9407140c20f81c0e10b03a80007046003024004200a00701007114100851401103000b6030301d0521010400040500303481e00b142e5128450a4140203c401543d9520f0000304d600900b00310000e80808040c4070396081503120703840240c1c0040c511540329610b0410f40300440c80340d40c1101844c0c1c5160307200d14094a03640010b031035117030004007540510541414035502002030940014282c1c0d0030321444802280505800c124888140080084607104052035409803161042d0030307080c00c1e414440c107030300c0040004550f03100250420004000c180d59060b00c1404028130081d1505421206150908011b00050303080f1481c1030040b45450300010702d450100e01036490506038180703641c1c90f08076503180f140d081103002c01040d40e1081e0760b41546070110f010b9203d42032480340c11307401178001c440c030f04808103086500030122004510010031040710300b00000e8121405075802009039000110024170100c0042402080c000c0110104d0b100b550710b5264001082c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 829186690 1250 829185440 829185451
    0x80d0302032d070320030a05190608070509010815041e1506030b0f04150f0608031602150c03030103020409150c03150f2102031002030a0c171005060310080105040b 72
    0x244080464002c22680c0321103000304040c041709003440443d0035281503400450b0014088103441d08100e118004510445004d507211203c141c1c0001410026401c01c00855401000308034041c14441443e00305410104c00024030013405001151918240003c150b0382e40940550458920251400c0070f509020080c65540010b9820000c41d4000a00381c07455090a588200e512400504814076a260f1810181c280c040f440666140c4a070320204210343c0c10005801c000500f04103640c0300420714014000c2c076001100765084c824204004135600342c1c80000840f0f044a5060342c0001e2401401e0604080d0400070707803ca1f0f6400e40c1811411400c007a03054000c256814520099001c0746030b59205c4c03030501648580305009000f10000c000c0001c0b80440c0b4050486c45001030185da0100080913103d0701203074800c03243e02e45d03450f580c4d90040c7c03400c590150041000350380345160714040c0c0c00e107149202e00c20328a0b44074052185e000000000c00e0280c003007107010000c0140d000244800d00345860712014240f4102d81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 829187940 1250 829186690 829186697
    0x606040e0f071d0606190806012006040303061e0b0310030602030f01150507200303120a0606091202031b04021b0a1b03020d0b0709171c0504080d0302032d07 69
    0x310743e040c6080011220346031160005481b1401d5040400e44186500400190510094245180e511105008142d0b4841d481102610540c5014503010301110030079080030b0720700c894602c00042c00c0440f020b500ca09550250311125103c0d42c81d45d0068641c00d0308c07908020003803800841032200000032034400c58180c0d90351128403480414400f1048949009040b40075040300c624801e00740c0a400202d070348842100026050307034078222a1401c0d035090494180d4050a00b955500700c104103251b441010040500712841c0805210300164000907030f1646112010a0201e84410301007440d6503d95044076020700840844611140b403010a0030b48410500070140e4920000201d50241054681807141c1501d0b03004003961917004207031302c5040411a0040082d0284910322001240800c0d43c0c0c140c2000c080d009000820058445a10000140d44035207203c405101083c80103121034207012a801070f441003103140c0141c0700ea442010440386003021021f80704030b030001503001c24a954504111248580510b84 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 829189190 1250 829187940 829187999
    0xb07080c2a03122506200d0e0a0b010603241211040b0306130503070618030e030a1226130309170d120b121f06080606040e0f07 56
    0x42005400d03109441c00300c00c00888403188440c80388841d000905019005c0d0000186055040e1002503103400805003800d035500b004540c13060100348500544402007003041c00f60102da6100d960710700d5601c506000b41c078241a228000b0f940e20a130780240058a4500c200101214540e403198100b03580304a00000303807030105030314500c40300d5414540507100c00480d0141c010301c5255280015840140003078003044407240410001d40000c2080fa002c2d0401082c0200e0503c0c1c0a10703201e18010b0107030000d48071410f000c1d401c010304242c046070300302e1100780c2c1c0079141c0e080491102042e641c403240242c25080e440c903130a0301e220307090110346100b0501c05000a03210b070700c03646000d5413030301940818039451440000f025401b0710a031054140c0b003a440300428400c8090041458112400010440d0003080c001100b56400303c0401c140820701502d41026002c88444c08010780b6081000203919002c0c020100d0340182d4641400d0040032008020420044480c4000d986486454407040200034541403551040c422101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 829190440 1250 829189190 829189213
    0x307030b1819052a0d050c03061806030c0f0a050604090b0405060a0b03010510031803030e190317040f0b010f08010c03050105010813052d01050f010b07080c2a03 71
    0xa115140c0540f441646903c0004041c1c00544c4a02010342c44600070250300b441060480f50b4240100d50092840d0084103803249080d00521861441d1141c041c01410005014000c01e500d01280c60034002c40f00360707a8540c1e00103511700400c01d410a00d50005420580c00640000d02c0c1800d6031081854010440301440389803564820402210864001d004841c0d10130401044680340c40039510610486504020500c42e4000038508191004508164086621a0300e41800f42006201c01c1161141c180e14144041c101500c00410b80440e210703400381050b100034041418003151407140444140e014106094a41c2c40d4003030b0303112000c0b951052050940c2001c1080580601a000301810388030181d685950507525041001004185000300383c6071400307400030800440741040034941d8040e000007483e0400c100300702a20703421502d008004020204528005008100e001c0d0201c4140399002000716490b0740e04080140c2c20800b61301180d2000e00203500d030b100f100680b0604040c2d4801822000c0d0354280258 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 829191690 1250 829190440 829190491
    0x3030304021003020d09120e01080f010b074809021c090f05010507090e0108030a0c140f0604141510061103090301050f040213061401050307030b18 65
    0x64800942c4046a48103801c03034a48070394050041c03070a4801000c00c0400d0340703031203401c0490307c9148440005918002109007650b00008015001b20710040d50f10125850100401360601805500a180490f44800c244d18040692560100003404001d26050004c801d2218440c1e4407102c481940c401501900002c0e240c0250f2080da410b801d64215081401074002c0591400bc010784401200d800901510307000100c4e03001d10510b44100113035103031a4503642c186180b040190074141d20850250f401041141034041c0e00c524804042948810704520946459a03001e04010b04e840e08503151f4031a100812082c040c01101025222a800c0306448110f5254191f180100804031442400c48441e03640070440a482410303601d01e0980358109490a2484000000342500e40036a01145e1b0501448180025490007440a83d0110f01610b0104100382c81c10086440710044c800640303041c041d000c40046d003668040e8210707a100d128000c1c00021010805454528045000d591680095108031142c007000c003403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 829192940 1250 829191690 829191697
    0x81b03040602100e07030308090f010c0f1206081002090a03082a0307020906060d0608010608070302040b120606010513120b100914040210020705090c0703080a090b31030302180303 79
    0x40b01d401030b24035181036407008c4c1e40c0c200700505501c0040c480c00094407080c807002c1c440d20710081d40366501c000d0400c0c3d810034003c1101351200705082040d49004010440c620f0001400d11001096403c0962034441405c0003925994042e48042c00c40f501c0040c9960944580700e0200381e5114030380c08000d0b5001c070790011081d0b8a004500c0003e400c9181d101c04100d00e8a0a000a40740c05051204041000f81d1035000d80c6081d281c1c10381c0612041d60101d10300303004510b441e018030500514155107154401c1960b140c5640d60b0a80640141e05101c400903940c0103003089000040090210007a903e00170001ca854801003070b08003164000c0866100e902c02248407080740c0642400d01003140f9500e4102c5d15286c08021400e03c610002c6802c0d0710035145c000840d42c40d41800c0c51720800c0151419034842070304d0706014181102c02000c1d5441d6600d008610350020b1a000242c5402c01c0000d803040100c0c080845c100c030f80002c400d00c0884a0148030702420403c25505400a00c01c104066030725001503061001819038a00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 829194190 1250 829192940 829192961
    0x50301030204112a010e030c07290d021305040c050706240b0d022b0606050412080c0a05060c0705150610080405070f062601050105090607081b0304060210 68
    0x1804030700040f401440e07183c10300c604ca80040000080c05014400181d00d5a4400894011260030288042248060109140b81d00000007400d1030001e0070a00d692030b80314401c22090001041d0f01259803040f0340c0070808840003800000d0001c101003200f402e0042c3ca00d401c505011521241081440c41d0401e05207180700aa009081581c0144075052040d0f0101c00e400c41100300a1040d030a10540b50b1341029806031014046410203540346c11841041208150352564014105101f0104802c20113422003102d03140710b07140c01401017a112407041c3c0c01903081428000002d003070703072040398180701041100c4801084014822030480b030005088410390500c992040b1a900c1d446400c400034a40c00f58021100d81d40c2c012f20940603103484903102c2c038141340103550b03a42215000444e00145004940c0345000c1e00c00e2401e0310440d503010b05c0d40c58034000130640c0c4a0800414001d0781c021901c84104074900c0242e5040c078201c904d000704c482c8600d140c01e55998005200d40e074011710078061100034960f100d01c1841840c0d0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 829195440 1250 829194190 829194217
    0x921060b1c2901171c1209060b13020901140403020f0f060d0c031e1b030e0703050a0f02010e0306150120120a08060d20180a0b03010e0d021c02030f040605030103020411 74
    0x242044281001040102c002340da0380394803002e03004001e544900700d1841c1c0851002005881e4441c45000603c0c44ca1003d8200080c0401000300380003607075462400100c00ca00071148103001e842941c000c1a160700948840810542c00e102c000c2500c0e603055001080b8024900400001088032003000a0640b0785001c0041c1501c1c02180002074818881c0e00000130300e4074820100e07000141d89a44113480c102903d8000d44011001c075a41e00215070f40205d50a9218000310002e003094140509410080c00001c0c4c8164148444c108030400c080010b5a2515405030102c01500c20343c0c0003c1079000000e0384028541c00c002507000d80013802130b140800d0111082038008544000350b0080402c9268103007825002e40381e10010090307450700355010132210350b07200d100210b030b01140060346802803500355503640c010b040845d0484135030610400e0380001c82c88c50024280708100410031703180406034190b10480481c0c50003004005000719030541c0003070003035040b20300c256000c0244210340707405904036008002c01740d0f410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 829196690 1250 829195440 829195457
    0x20a08060f06130e100b030f060a0b120610110f03090301110a080c160204020409020d0e010204080c010c0c05091f0f051f0921060b1c2901171c 63
    0x1030121313501036680c2c0702140b021065007040c0c6a0045600d80d0b001221600c540078030a80400c0300605010944000602400300510300308540e501401e090700c0402400d883c0110502342141c407106225480400c0d04261503000d41e4a405182180c80e0f48030f41c0207080c0903010750b080c1b81c41c0c80c40c0c00710200300f00d50110020740c1e00d001407501c030014001401e9001803100007240c514606c111001d669544010802010700150050b603402101045000b030b100811012002a44144020009224041850000c00d01c007460b0100b00d40841c0e2524104580064101d5504141c01e441000402030040e0b46841d0f110b80c111481850107542c84505c20071115440c024983c00815601d1a940c1740030488050f03411507403160601402140e1035840080380c07000b02070102010740d80c540410009120940c40740f40700e0000252001c80303070118510070902141c0120760008100c0301441ca291030701580d407500140f014165030341c04450b40356901e00c9d21009000c01c02d14401034600030901c100c2c054100207501e60180c0d0640303443d50301c02c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 829197940 1250 829196690 829196699
    0x50114031b0307020a0605190b0f0906131b050928030308150909010f3206032a0108090316061d0f0d180305060c0a0e04020a08060f0613 60
    0x102d030400740c062000d510440381880c00240183c010340d03204854060003416050b941c034a810742500d020014284c06141a004402550f4641c054641d50044003aa820b0000041700c906410050400302980401c540700d0188640f21a9407001c0141450482201c010400d1003041146a00019221020700d41908020b00c040001070700a155050740700e4000d45c1004140c0413940c01103150400101e51902c00d42e55911058051554540716044400c0c8200700201a680118075415000201038183e0090b80d040d007000041c2160780c01c016110b0b40c0740f0043c06030030444041c0310f4440145546c1000b094080340907840010383c840342c00019030b4844400c59104075201100b0b9195100101000b25039201d600b194502c0c4900020070412404103060040c200520405404500081409128031300b5a0aa801e102200700b0104400141a80d04150707184080e60352014185015100c004e01e8452950300305002055241342c007600214642d21440c010b5a082000e8406202003111070710408070342507500100301c0310511 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 829199190 1250 829197940 829197991
    0x10609050f01050904140a05011a03041b08030a09090f0e0a0b0907050a06020703050c040b031b0109180f0c080c1209030f03010f1503110d020a03110d0605011403 71
    0x1964120181425840c2689620105003654941b00010390703c04042020310040326001e01c600b80c0140300c036901d509094401242c0c902150b00c4090f20160070320f51900086002c04d403103d026503008201d03040459980c3c1d400040007034005041c1c3e10031900c50910702941075031a0034460141000031003c87c40a0b0120f490070b0f568283c218a40600603c40520504c0008030300c544420742254064000c540052040f43e241d40340c410700e00040c840c00d441c080d904090300f100d1300f5100000d0b442103180895207240180801c2d40d004965030300095019040484519000503110180c0d42d1040b106000038120a02c606143c111080d01d03c000b084d51032414540040204010480c0b00320b00751078100002c0415645012204030400409401c00e800c20ba890802804003000500d1246414503540002828103001044001d4498803540c000c1c42004032800e500010300c06d069a119620010803d000d4200701c0b41c48010b40c02c403401c02800c03107000e5140440c50041c0714840065008044e6440361213000d2090a41049810030314 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 829200440 1250 829199190 829199209
    0x30507150515040b04090507050607080909100819021f02010906020309030a09170303010e07030f0f0203060f062a0313080a020114120a1e0f150e01060905 68
    0x9589110050052800340d003014001d2902407801030381c00076110b185950400003100d4040c1e08052060380380c00c00100000d68042800d0341203810445000d41c40d000c4d54100101a44100d01c21243d00018030b104100d407041019450005540c0c070076003115054101c0030407241c0075101d0304801039803180c4841c10381d6080740042c4516440c0c450a502c0041340b0129660b60f00710030b0303810a440804184c0c0000c10100c00c500c0d402802c2c04000d0a00c000c8440d1114050000941c4911043c000c1413803110407400029482402500460084001d90400304460484044104020340058805a10480d280400302c2c19610b04070007a40d404102c030580340c546100784c041c28401600701a08082c503290000340040341d042c8a842c2e0010000b412040040c0080001f10300c001005480d03038158280b44a01c080c000e4844034545642026031242000c800013034903440028803076140061000c81816441c1c208081c2c202c0400d01d40d0412219148040e00809041c3e45843c4a0700004409000324000990400002c03c5240f0f07022082 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 829201690 1250 829200440 829200443
    0x1d040e010f050a0204031205160b0612060406050f0c271c1101030b010c0b0f040305090a03052503021305060d0206030f090c0a050102070e0c0c06161d010903030507 72
    0x40c007901c1d5016a5080ea0001c8900c000410782c081420014030210116803501e00d2414138086191003090701000c0c103081519100902035101d0f15000460719110354410b00744184502040728600d20f4a40b40c1600a0030b411210140095031240205807291520820b0700d60180c0e00c0300032140014051119001c3c0d130061094000c3d40540001c02d80c1040031a01c015070702429000c0e40204c1003a180c040000740944200340c0b1410704020000324900c01084403545801d400845201d101119511076040440311030048031025680f14010040c008200301002442e603040100c10342109200b60106211240045258403003e904846069121011003a0030b40c055544800c00800d903140080c4030b0740100c1c4c40d50300103c40e0306407482c0005080c4400300d041000105c03d46102250314802480c00d010000b0b4845ea0288190b9070545643e0002c83e011003480001c0d19504502041194031030301d01902900c0100303007040100e03001300c0c203c11414014028840190081d111041e165480300a15550301107405600c40e450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 829202940 1250 829201690 829201693
    0x151a10030e030f190f020610030f020301061a180a0305060f07210218151b0a0209071e05040f061209020901030b190207020a051504030515040606061d040e 68
    0x80014410f28900291080700aa012150604e10580c4805004031542214107015035118004100d10b12007501400b1003603e6001c0440c6052071000d07c04039000d00303415001104115625041d4900f900300c43e0000d4102d0040c991010703c0c071003098074140b002030180340c000540b65400100014412000c0107240a80008542c42d00c014100b401e0340030480121018001d402c1c000340c00180011003100e01210103400c5040481d100a0289164941a80310f445980c200104101e0705140c201070882050100d10fa003e0703000f420101c864075190308000c0c00301807200c510790400c504881c4210350302ea1042d429201510f1480300c01126150400f00e0070394401c25003075940d2000c0d5803502076480058940b0200b45001318440d2000c0942400e0000c060b4a00b0a09403000903000fa1041c0040d0380940e07585600c82d001c13540309480d000380e10403440d04110301900c2140c00c080c00501c141c00000c0d0030354084119451255000300404c00840e5203500084440446640700e0b080300000c049010682450164000b00c0c0c4401c40341d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 829204190 1250 829202940 829202947
    0x2a010c050c0c0f1f050423030d030f02090904060b04051303051213060f0e0f031206060307030e03030f040203100c08190e0f0318030f031b19151a10030e03 68
    0x461040c00068682d00403000400200302041010000e80c202003e150441d0041f0108802d0403000c81c0ea11801000e07074100301030711044007004110f031a0b4101c0c0e03420600a40350b40103d207018200000070b01501c1501c0e07030241c4c0c60240000c4180c45441f940920356135140c0d50342868907921032140824071a0140c880001410352080300400101244114601d100314080d01081880c0b0042c01c0e1800e1503004410f29025401c20003010030114000d14440d40e02c1141120310365265110404200e0062068801245980c8030000c00d00034208000c4103401d108520071400c072030055500d205100150785400040742c010810000100758044010150900c5c041c1001c000001d6000d0003c18041c603101b032002c40340701c940d0000901414003c8607032121000c80b400690080001c00d1890035800e540380301d02613180ca122140714070020f00c0103000b80682c51000072314200d2001a04c0060030701240d10500c64000f480110316007171448040c0000c4c5c80c9204114a8000c01d0f4003181000d00c00d054002d820b01c0c60083d0f8441c0401c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 829205440 1250 829204190 829204219
    0x5091e10050d031701050613090e0f01021209070b070c170f0706230a090e040309030f11040b040c05030a0207030219080403021203031611032a010c050c0c0f 69
    0x14501120b070b940269520000400e02c03c6103210a0803040e00a640102802c200d1484001c400641c000b08445840170300084002c07121302d215040400d115031950b00c55000089a840211400840501030001041a00c000984e00d0406c0300c054410398400070481900ba000800000c01d401000c0c00301d03a800002640c401ca40706542490a0002c43d4001c0400300e0403442d00c40c000d40705030800d00c0014501c00140f4034030b040207500d405850b0611b40c0c8182c2e007900c055130000900f018460700c4004002e5501c03941039106a001441e01400d03c58a418030135014510300320559030b10b440e15009007050324400d500c2d0580b543d00e43d004440f010358000d040541c00c0d4030034011008204a40e10a04001700c50103a0b2a6589640c1980704206504000c181411070540c024403d005003450110740c12402002c03103003080414112020031417811401840b09150328003900a0a0010803c06111240c040505040080028041207034047e1058069241c1109a5510080381d100903800c0c00103c0a030300c0c01005009480c0030000c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 829206690 1250 829205440 829205449
    0x50103150504030507230106060e06090f01050f0c010605120102270a0b1c050c0a2a141f02120c03090a05070305010c031d06070c08041502011505091e1005 68
    0x10306c0d010184911807a0755908040741e003072040c18003410f402d2404040442804000541c01c2c0a1500700303611444c01200e070012568003550444441260800f862034541a0081e003030790003402c039442110302446d01c9180502188506200301c4054404480040c01d8940d890500c1290084108110744c0d005004810089420300c40800a03003208554132200c0100b13581003401034000d03614080c10404040200f0312004116582058403260b28075224030104903203100f081c0001760420040b900281030710584680c600d01e07180300410010501c0b140c0c0f0665208da01c81d0014004100d1150800c1e0512742441070002c103005101c0c05008542011484046a1003141107882d12400c01099034403c4500b80c0d5039400c0e940507203416009110f00c05110242805000080c0040340c1d845050060440d4200043c541e000c204000c0888240d6020703184041044003010b541c101d01038028155074000d50984a030000c800107030fa00e03096055910a0701a407040c83c4203030500108907402008003900c9601111801500420039440c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 829207940 1250 829206690 829206713
    0x503030403142205040c0c0213050a0f050405150106020d0f0c020a031a190605010903080304060f05151f02070320030a0303021803010c1b0c0308030c1c050103150504030507 76
    0xc040c03d60b450040c0303488200000c9600c41c1001340d013480280005407000d695051248a20a2030103140400c440e580c10501900a00301a8103461115280a05200c20f01c0400600071a40c280080200070040e62146c0b4241d030390394415003260000502226000c0001ea11510011001d640f0240110004035240c1d655400301e070f000d50303c000048400350341c00c0240b1030001900340444e241202c03008100c003600b0300f800201000c11900020f4132110000011a0400810741e0004020103001c40041065013000c0c030154010199039207240f40b040d400b4141456000c1142c3c07407604540c510715002000c2c0c0600c0c40e130312101007a40070000d030a0b035809403000416450720144401d4201620a950059481d4101c00355148001c0c04440e016020368500f2003019400c581124400f02c1c400d82040c0e071317840e640c0413500e0302030404100d50700010640e82c0d02200b4006009450b00151140c1003400ea0324140d8082d82042050807120244070261255840b0740c020711844d903040e80025002406441c1c06032402c2c1c0251a070801110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 829209190 1250 829207940 829207987
    0x1f080303070e010219050c0603070c05010614180603150601090f0b0901032d110903030d0207020a12170a050d09150509030f180109030f050102030702011503050303040314 75
    0x80800a0b0150150780c140f0180078030319070350512000d44100584506568000100c007a50003004000f02041509001d168101117469010b0000e11240d0b86698170782081e5000c1034090b0740a00e00910700784254403050341c1d48922403107010f401044000065621303e0303258900900140e060000441020800c140c06461880280660201a6070780c0e805034800107044507484040b07490184000c0402d60701119803c04031075801c0c1c0d2010801308004000b440c90000c14403420f60000d505100005a143c01017209070098642617008a5188009550b41d011000744840c0604000380308101040d15034a103850060060103011105240c449d05001005080d03208031360b460300d8192400380950b550f00034200c806001d0395520656100180d400e01c8001c00c0780c11141e01600c0c150501c2001d2103062010301d80d1003007483c1c000075500402d10418425040c20b0041c001c2d0b00c10360b00c0400650070302004045c0ca12624aaa01c2107030380c040004c61841d919910111160b01203061000300b90b0740200941010310714290b122000f20b1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 829210440 1250 829209190 829209197
    0x827100309050c1509090c0c030a0909180807120c0f11040c02010b010e060f07170301090b0f1c0201030912030e0c121c0905150409050601030e061f08030307 69
    0x101d080d070400500d0007540311101d40c80380c10a51840304041c8401015036003078207001d40340c070005900c6840200659000d0340182c54620700c000b09036407849035441421101120a4a0310400002c035088001d40c01907203000234042c2c25410100301d1940021003074000044080c0c0c0c00d28002340d882d03503140c0d265246401860030584008000e00304000c1e081c0380501caaa90040940e0000300b04022900b00013a200c030407a002c800c0c0c440c14000c505034070340401010441c3d003043d910260a9945111416101d8400d400a004920007a0320b031520081d440e081107203020a420b000101260200104800f0008417050341481c200d0425440c0c41454002415070310b0400c404004548001c540d5210450641346091441c228451081d0381204040010030004508800e035180b240306d00318a0018403039415508100170754085074010030031900200840150350054800d50b01044024040354494000440030707601c18912030403081e00440041510318000b140210000c44030080690781c50390b41c07155554116042160f005012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 829211690 1250 829210440 829210451
    0x2a370e0f0403020d0903020a1707170a14030f030c090d140f0f010b0a09090302210d05070f0806090a110711100513030b1b18041808271003 61
    0xc240d014002d0104c1d220141c50a800030a01e182c001800403803091288008607030702114801c040610a102c10300103080c02c010011004a001003040f5a00c1892903802d032034010a08043c1607480002004403801c0e40c40801d071581c19501c511307a648080e503004e00d1003d030380010600b15003c001503102c1e4003403524072a618098a182c0007072a841c20704040ba154000f0380c0603450002c8001d0f00b96642d482c15000d8503a002c10001d00001c6a2400742d2a256030100300040074108880040d204c208943c004040d1081d041c80240f1544d1148002a1014001c2c03c0e5090081012003002800c1810030ba04225407150704407501040c200c0d070442d0042d00301d5000c59015030f01c0314240314241005013400803041d200800c952909a203010400d0f4111400074200740001041074148101040410841b070b2610300f04002480c601c1d555804012045903c45006000e21900031801d00c2c145880781140424103110b540c3e0000b1031145400d43d101d105041e02504503005c0002c01a80d80900200d0391034008601503130000d2901e002a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 829212940 1250 829211690 829211693
    0x230f030d0210110418050a0b030a0f02152503051e07020a33020c100f03140601020a17120c0a11010203070f08060f032a370e0f04 57
    0x43e11180315050034a92010802042100c4000c0e8103819070301c040364400180740e00c842018802074403020b403103240d25210b608009024416500101c6811031300c2100c01030300003001d03144640e81500031503600d04c18201080002c4e80c81c018510366a204200d202e0300c2c045107080400c1c03450806611101c2c60200e6140000b060b41421400c00180c03600207008084c50801440c00003204610005081510390100c0350718040d2100c0002d8020801e011094a000300b020b02e803200741c820014561140009100006401d154096a241d60346000141c040e6006a0142a06642c03546030540100b44800044d0840c03502000000000606201003600800254100a03500d42800c640245081c2110365030283ca43d2040050021098000042d01c0112401d800c0c00559039031503200146441544510f25505800b450344450880511009150752420f03480c41e040210105100c1480102c55848100070f98981e01c0030520141c4601d100e0340b51901d0f881c0112144100b42d240d082044102c0300985450001c0da0903c002d010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 829214190 1250 829212940 829212973
    0x402012d020109020a050406030c031e060606080610030c1202071403030106090303141c0b0105160503040501031505130e0f1c030c110d03050c0f0310061107230f030d02 74
    0x400521b003c80301489594215206ea01001ca440d2000801251001c41c01605240003500004003079074002104100b0380c0e68030319003c0c055140440d01540308541c8144440442e60003031048147e65940c907a55036001c00d0380c101c0d8030300085d8803030171050300d0303160f407096040f07043c220204001c5000c2c0020b941c0764035030203142d4a405400d000030b485600b4900d00003406041040000d2200e05c00780c1083c00c08000c00c0f454a0000140c4451180350070080142c8406960401401000801041240c0e800c1c0d0f0204801e40301e851400700c6c0751460380142540049140c10820b80c95499401c02c04045415009840000314105011031a280303199403c02d003841c480031040629942c151145c4c00c20107485003810804200c1c084c0313203140c842e00360864400505544a0115500c1e001c213006946d580f0601008042c1e076418920401400001c151143c400091701d000304103050300c103001c9048022203002d10000d070084181d10344c280d0300c1e1901c02c40410790019200c2c010300100e683d00300a05070035401150090540c02080c0c40000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 829215440 1250 829214190 829214209
    0x1208040f0e010e0705130e04060b030c030714040e120a091e060c02090702070b0c01020c0712020a1208070605241c020f0a2c090d080402012d02010902 66
    0x4580c0080044010403000d0300d00840a03900070303454500f803a40c0e800c2d01512200300086c01d070007007400c603040c1308100010400c5641c4040c00307114080f0110307207050401104040c2d41c0c011602a880004400a0300c090850078180c1003040041024016a074a08806901140d04c40e040b8011140011741c450a0421172500c5003014504885000ca070020301c0b0b2810007601520340b11103203000074000c520040002d08014824085074010742900c9c1c07801d6603901006001c0c3d5020b0f400c203d6540241c0d000752500018061076402c00b0600084e400350040c00902e00e031072801085511040070030340e06003a0401801e0005412845118807a000304000702940d011902e141201000c80002d80e180610424030303030403100c0142c0070711280c4200d03811520404040e0b080c00110710724480036400504030355010100c10380030010400d421a103948454000c2003140d5100884680d90b0201c101051021582550204015502c110303104028034a2680620019404c502140e40403295581d02000042c2d6640300382d80d0840c036001c0d070b04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 829216690 1250 829215440 829215449
    0x3030712030e06330301050106020106030606300503040e270f10020d021c0c021005060a030611090307032006040e0f13120203030a0e030a0816091208040f 68
    0x7000507291001810041c0301000302d001401990121221003440c0c803010161380071080280080c03140e940c0d030b0b8070f003c0d01910b801e020440c1c01c5814183c0c081042310070b0911030b4102013000c40c6088420340500941d54041c0ca501e020565241c08100404180c03042d90042d0140100482d1100b0152a0011030140521845034240000183c1140c0c851f003041c04800030344020303ca46070201c0103a96161000b22040244034051400c0750076403900381048404401035003c00c010b50110740984007100700b205071407c1211000c807942075003c0c42040c020b101142003980701560074400862054503185401c1c6c0002d103402840c1d4002c541841c40382c0c1c0f4010082040c00c0b00060254010340d605802c081c2462501c4011035401800c4100020003000001c448420009100e010290082485140b200d00301d8002501c0341e000322080800c00c0d041c203991800d0401c00004030b50600c4010360b165802030b1660800030780c18108100d5007108122580501060b1344040503445541c05200b0544a0b5a40b458040c0381300c88820203901 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 829217940 1250 829216690 829216693
    0x5012903040b0402010f0e03060405030d05070513090b01030209041805070602010b0906120703080f030a18020f01180b0f031902091e0402190315090501210f0203030712030e 76
    0x501c8005001203009030f4009509003030089403d10381940880d0851800d0000c40d13454411023050205201300400100000d642d10b84c4107000c10b40e14500166050710804000c584603880884c020044034007107511040600505250161800003440d0000d0b00741c0d00300b610380e2401002661442030801904019190041001740006d0041006a200161000300010580e80c0210f60984100c1e014403014004c0c0409581d004038413940300c40c0304602081142e0811540981940d20f0510f140b144030403024040fa44c0c03107038010101c1c88441c50b04001100e0002c8a2903404980c88020840480c0100702d003009069060525017456407289090403202c0d0341e40c01c8071407444091600c100809001074461480d90200c9405103210b800c0f81642040c0403400911030403200900b9a0000c402c44007280e94160405808a104110510704450300e4990710411528213100b0349940d5500400d0400112100000c0618600e00800d04004a46803540119044d0f90203d4400c48880c03481600c0300c0b0306140c240c400c04030950300040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 829219190 1250 829217940 829217947
    0xb0a09050601090302040908071b030b010806100b1810020a0204200a0c051f09030818060615040b161a0405070b0c012415050f190c06050129 62
    0x1c0081c01c0c18816000c040e004940781d000e2074040c05403d40440349040d0780034041502510085200382e80400e0300d40012146400d03080c0c00004c1e51500062014001d241d020701d00004103103001c089604580c0309081055043d41e114017803625660300c510745004ca0114640107828508a28410401280c4545040f0044d07803010743c800c074200c40c1c070b05016500042054101000c000c0b9043c24034034a4101e550304504900c681481000d4001130303d5400114000340b0a494012041d120141229114000c0910042e415801080041c8591401254843e4010b183c8111245007580701c0455000b83d07840104904045890422054100480488100120722100b2001c46c0c940c2065915252648041d200d44c0040340d0011074001d403030b44820b5000185645041c6408040007040504400f8000c6a81c42840e4000800c0b2100c181c505014404071003070100f211004a24002c5c0c80003400c0d884e40c807107643c242c0822412072400f00002e091885440e010381610100d40d0104081c011480d100e48100541c1c0d030281507000e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 829220440 1250 829219190 829219201
    0x901171609050613030611040b0c0102040314061e100b03040606060f0548010506040506010f1e050c07170c0a03030c03120b03030403030e101e05030a021c0b0a0905 72
    0x84ca10301050360790110010801010342c0402618501a82d0007642030361200003001ca60f1030070158014000c4074400c0400e08408007004040307984070b250484040d010750300c0c2440400c00c2d82c4000e4004a030b0014104c10640c0259480d000c0c1c1d090b09420480d4200c03952642c1d40c1c001e11115400c104c03014800e0b840d601d8103a181156540000c3d6020065480b400c4104440041018000c46d5102851000400a0b1a40c60401c2940701c42d00f0301170401590100d01403440c2c01c012605552084003020f01a01c4151a24040d4010039007040341c0e44000316160108000d0144020540480280702d000028203221071164001361100c0009070038041c5420030140700d00c842410400010350003500d2103001e00c2c0c0508020a00207404040d030780c05000b05c098402c0c0e26001c001004410907404c008006a1100241c99200d18030f2000300c01500c402c40f6007864611515030b40070a40b0807443c410030007150712000d40c510250600c20ba40c040c40806a40100451614136124802045242441003102000f8002c0c400300b4483c2d401d21 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 829221690 1250 829220440 829220467
    0x303100e1b03060f060d0b190506040e1503060f0712090308270d020a0606050411190e04060b0c2406010309050a02030709090b0702030a050a0509011716090506 70
    0x140705a29140c2000302c00104250f07100d500f40758903250f0103480d5903074441d00c00b4071400c020000c4030380719440341c03c24208841000341c5407035aa4050700c030003034421480e1600302015075840402c020a0800c03500c040d54020505074506020440c05503030180e099590604002c14060005081002d00b2480340d840c11000340c0c042503104680c1900280c4142509401110712841520040e803213141e010a01e2003061910690103600103004c54819018000401a81d5104d20400c41030796100281c4a840160900001d4041042c2c0346160259600d0f905024201d2035424001c1800d80b0380b035a000b0800d0728800308440c90b035039600b40103194802c415008a00c03605155081c054102c1800a44014101a03803100c407181001010400c015a00780c00408980d1503076a181080d101030000e00c0400c80d0401c15101c0401c1d00300740008250f540c00c044949442d401c0c070814400807034240c0c000ca8401c504000e0000b2a0040c5080702003400d50080424041224014014031000303004421030ba030055029500410984401000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 829222940 1250 829221690 829221721
    0x70807020705101803030207092702010e0a03141f0c0206180709060e0703110f040b0315040e0c1f02030403060c031409010e0610050906040c1e020303100e 68
    0x40b507001034600c8103008111001c613514101030551900050000c42403580004000c01101e031105014040001c1b540c0180d96200b5a8808103224046246030000066000e441c405007003a101912400c6d40741c0c0c2e692540352514565424000b0140c00240c1a41403100c13200e04400d400740c207400018025401d4a00c40290754220041c640300c0c1c5003070002100f40b41c0d980240842c400030b00c00500c06100e200d032980c084a640480903540071010a16205c87c5080100b2010190741c840140d00201d43d042918007a100d855580c8020a081d155904518070000b180c0d4840c440c1079082210500100f461307403007000c244081d015424110b50030300f42c121030303071819030340d50000850b4107590f0b100320085145020000d084e000b5003041076080c0080d8030341d44200b248500301548030400f00410301003150f0403500c03499100450b550541c010503800c4210913000030380c1c82c1884e0300a11402c00c42c0c1d04d822425000441c6000040060803094400160000414002e000320a1a40c20010b040d1084a01c007890030000382e00c002c03202 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 829224190 1250 829222940 829222949
    0x9150512031e19030501080706020105010803031801201b0102250213090f1203020313230316150e0307020904050111030408210412031a06041d0708070207 68
    0x810911180c01da40c0d03148066480a401003050050000448003001d009001c09001f58000e40c8a00380000850902c14050641261911409540340d911400102c0710300720901c020b51401756403501c42047c2c5045481c031888910071961a5015194510604c0400306040c2002403c9100c3c0c1c018040c031942404010032011850402c8a0403044c20141c91010854115844411040300c1d8644043d400c00c1c0001e8030100d55445200e00682089115150400d038100d001c103451054460010020f80d000190b458018503429400030216030500400741c0d00d40d240395902002c000c1409101d820030703507070030071078580d9551103411180081031040d120f208210a6880c0030b02d81c0d0107407142410001007402d006003940420601d000030300311070b40d5a00c1e2501f004183c1e50700c03509148401f210b42400030b5642003c0c90320140e0042d640030141c00c0008403103403c124058640d44094041000111020f0401a036403440100000c041040c0f007900c030b1107510301c1d2103c0c41c800000c000400f40f02c0000d0030800c040da40413540109a0f0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 829225440 1250 829224190 829224217
    0x2011815081801110f09011106070801030209220f020310150f0611030f0702130c0503060a051e040f0609050a060503010605090403141308010e0708070f060c1401150915051203 77
    0x120034110040b01d88c0303a0440700380a5280a0401404062a40444014181ca000381c4018891752038104590000409211700b0242000c003000d80c880024a0300c2c2056a6040d00040403544841002a00001140c0300390b14a0464000403030010801c0da0007401e411401032000d401c09180100b20034001ca502c1c1e00c00c440c1e200a0292000030002c04554500704881503641d0a9107003003080d5801b4034030181c0158000e480c1c0301d00c00d41c00082d00003410301c3c1c425001d40c41d40c049a10301c00240142902404042c00d051080710258031b0b1180c4001c503154034940300300d07803003210201408074105142a05040c00c462141e00914001c202000030000800d400101c5584c162940f0354a0036034580303860b10440d50702c0d01c1c250045260b0b94200440035080d980c0005002090310000b400741e4480d5945d83d004402a030045101d090045849244c1c0580071616121014075100744030f000215031016003003420301e0000341d2504210955580c1d48031440700c0c030600107003641c003412054514110000b1020440790762805800a40101e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 829226690 1250 829225440 829225447
    0xf0e040603081204080c1504030912021e03031e0301241d010e061c0b04180602032215050f13020d0507180204210c0302011815081801110f 61
    0x405c07a4180c200c1b40d210702010103030703a140681c1130034a41a0031000c0e40d003034000881034480803400182c6036110560580d801006010794001c44c0d400981070007440c141c850f07131601060258462041110030b5506005a0014489550398100307541c41032206e007071422450000c18035841c450280d94100c426281d005200c10715035007117820304c40012180180d00a142e03981152000c548180c1c403200040009100030b204802c14403a212565081c031045841c9400d43c7c90110403140e00501c04180250b00460b040708001360302d003201c510072212208404d940c070b007812a0a05c4150741100da10890b1442500d40103000d030745071541c5e28108030ba13992000c02c1803100040d100c2c0003d0000841000800c00203280146694200007590403000e103032300ca0003508140700340c1c403060211003518080c20301c1d0540345589240d030081c0820111030442d001164100141400d1174601c0c0002500440c0005e01d444100c088003e01d5520100d041c6010b914805411400c40b40b0045a030b8103003032800300e202040c1410344141c1c070741c1544034685 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 829227940 1250 829226690 829226693
    0x9120309220e16051201090507090f0f06260a0b0403030507030e010c09080c01080f0a0506060403050f0d0e0906030a03080c07080403110f120a080d090803070f0e040603081204 77
    0x600544400d640b4030303c2020034000345081c12031404800c440f0100c40070b40e1800c5071500540e0070b0310a480401449500000d03000d10490030503902c4000d64110318900003070140041803481c81101d4081c3c10500c8025600d544040c00001c840b1203561130500708034054042d51080e59544176228901620007414141c65400042440c0d209602c04550030007094003c0c404c03003c84042c058244c40e003a02500110f4081c94805000c90350042d03150b039008079400b295041c9666180384d01c0000800780500200c0e4003e42c00c01c4000302050040014a80d44888503019005420502101815080d59030031010b004109a008100d0340d980e000c80e00307490071501801d05000c01d03a5400141c2440e072042400040010307a01040100a000c4a01e045a074a0b940039103a804107140d40c00b08010301d01c1030000581e078145d441391005000140014014041620a03048c010031074299568401c2d20b5900103d900e900041d01ca2048000c91a178481d1481000c4103041d10200b00b0740e400c50310780c80075030704c0b0300000500d031401d01102240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 829229190 1250 829227940 829228009
    0xb120303060603130f030f09090c020309040f061a09040506010903050c040f150e100806042f040f050a1103191d2a1909051302040501080309120309 65
    0x41031385d00c40000710380c1214515000d084030342d01c808081d0000c0c285050124203252944140d40000400f900258100020001007001070041a40a00200d40d2540000550807490700c0800001c28030481010751101240d806120846000500342410410107480c01c10206802240c03500140509407000b2031b030f44620003e070320050038406040000d03d00009400185408407240300038002d4560b8144c500c0c040d5910011035540d04801e94019090303444483c02c01e2881341680d00c103d0a0046684403a0f0080111b01c400101110348a07036030b024101d6220020440013596512071002000001070700da600f1410700c1d080d60084980700410f8401c0301a55a5007510403100500101803044031020112604100e00180d40c00c900711110005004010482e80e0329076141c03818642111540c248030760810304540c5810740b0140607000c0a4030310003500c0340203139031413015031207500130746010706684001160b41d0780640c0140b205859072440d511003030380c0003403044240c240e4880104820780f0780c82c1c0c290000380300d44006090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 829230440 1250 829229190 829229221
    0x10c030b060a030203250c110306010803040e0a0f0207080405030c090103200402091908160b07061a040e0102130e0f04030503180601090c260a0510050d06020d0b120303060603 77
    0x43d840c0004081480da26547e1214041031800d10804070008000c003007c0905990300300a00804011343c100340070030303c4039020020042d82e200461a0000c11601140c101100403a480701005880c0f11800003028006414104142c07002c08101341c42101c45907140d034664081d07640703081552070b1000318060000825540c6540645680c120010321807410030514103428071001c8114800c07440a4000e0280d581c08a0040c00d94000407200e0140440745001d0095461000804e140304072210110740c050081d80d103544407489000007540380040016540c29042182d20140c220641c41000e0080b4420b04018080c202200302c1070b001039050418580301d4464140075031035a01c0280c0b956034588101e000010b13142c070a075080300700c01e5a015110401305409003030703034440d040140e010348114850507400494482e0380360368441a800150234440000c140e071620001046a5540041035405070340205841c84003843d540b14100da00c11040300d14455200725244201d88a01008150a00c55100031001a40040e500f2016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 829231690 1250 829230440 829230481
    0xe10020106050424080a03050a030c170a1a0406080717010204170304060807030b1f020c030f070e010501020c031c030b09072102160b042909010c030b060a030203 71
    0x502841000c10040311402290210322030318100c01904c0081d5a072804250761968540507504d480c50616100400d40240007600030907401c002c0032541c602d0180703503003071400360246030301c4003012a1617982d44044040010301c803d4585d100d2031400340104078005d0700280010443e001c4c00c0100c48281040c1d00000d009010740d6001d01620081100c00007100c0f074001c8001d200781d0760b06490f40c01c265161030204a04071850305040720b42100020540ca040c60345140c10031854a0728a104444580105901090030301c05401c801100651154900f44100160503034020301420003031004141d00c455030b10009544c0c4041071003040042c40000f422404a5100740c000c0016024042c000d024203040c40c1400400748510400742035400c1e844880028001001402218a248e0b1180d205034402d410607200d4264030f003005401262003444107004140c01780041e102c1c850007100081604126032405440e05030035244807071440010540b0342000d9485a5841c0c0051728817014082c0b038010303100e944800c603514240169290 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 829232940 1250 829231690 829231699
    0x503040b0403050d08010609030308060906042007110d08031803090604030f0203060609010b0a2007030c0819050712061d060711030c1903090e0108060105040e0c010e1002010605 78
    0x5001c41804800180c0303031141903aa0366174215507030341c5210407151002c1c640401000984003502061152800c1407800c0d030088001000010304410f800da082c400c1600444103540b4265010807140f083c069071810800b11000142d440c169244010ba455600364071006055600307006180e4594001c0c0e080400503900082c0e0042e106a6542d500c134189000d12801008040341b0030300c6050001402c50401250941c101e5070441c00c5141401d56a24043d1003c10380e60041010b401c18160748020442010000500118050182c40b0811030420f807525080c15900711b01040203010303800907400014000500f00044a01080807800c4411192500708043c00e90742d0030706003100d10307800380c003031000200440c0700c40c0104c800c0c4d1103102c1042120b80340c2c81d4032405188410308294100c04510024444010f0360301804a20914211080c640c40c1d000d151074081007a042a1201c2c0c1c4440014003c0d030500d232040c0074000350000000c4c841d10000c03200081020700c080e00c550b800b0700344410400b007100c1d00075000364001e000000e1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 829234190 1250 829232940 829232947
    0xf04030c0b040b16020a0f030f050d0626030f0409051e040302070e10210201030b12030307122702150a11010b040203010f1e090501080d1d18040503040b 67
    0x10080f0401000380c498200d00070038001c01c840d80d540001100008141e2040204112030b0654406490344171696100c0b00c20703c5401c001482001e08203100710030180c0b00051401a118040040c4000d4080707542584841950042222280501d4000305850440e80700d1740d80030407580c0e2146400d840072564035a10044000078a005e00c41015000f003000401e807804580a4803139990303030070100e030070008051040e030030030b8a0b444501c505c0b003280c07101007254181d0042c10701048100d160404640c00180120000100b50404810300c1fa2456100d1060641180082424001d905000600d0503c0e032040420a2030003440303143c590f800710f407a5401c00550880c0710481c65901c48140c030401900228030311034041c81551034103011140601c0c21340700b0390381030302c2c280b858582c48941008041c0f8800e2025440b41c1441001055000951900c24011903007c4c00111028001039411410090070784002a41850303001494841a0045526a403c0001404400031032600a60722141002419407080b038214802420001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 829235440 1250 829234190 829234193
    0x1b03090b16030e0a06050f0322080c10090b060409030c080408012309030f0d202a06070c0c080f030301050306070e060f070203010209040f0605030705010203120f04030c0b04 76
    0x140705842082e000e41c60b0488103003941801c01845807194002c12020400a0054103800c0a454001d5644034030180107591110700c01860407003180b1081e1000326a6102c00080316408031005100c0a10310001d20354081c0286440c2c1d030768001c81454020020350080380e0f9031100034249441100c8504c0c0c1744e604980c41c15603a41c0c440c3c005074080d041d9040040705540d2901e010580b2071103030010791482407440002440c24880000246d461541c8020003014680f43c0f50b40004091090035508101d80e026500c440310350300c0d00c8071400d1f14140b60185080c10035002c212480e82081e91004110143d020107503140c4211100301c2441e060641c5116074010110b01c3c85074141c080034105000006506031181101241e0103561185021549a01d80080c0c0f1500400203011591600b0602d80281060030b05c014005800c0ca0700d19808030382268405030264581c50384510301005642024000040688828406585000d2013858081d06107900074280f640821a00300c0010141841940c03e440603a0780030b07207840d0fa541002d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 829236690 1250 829235440 829235467
    0x4082512020f04061401030c110a06111209011d01152c01030b01171b1309060c0306090f020406051e0c07090c12060e131b03060e0105011202011b03090b 67
    0x417035107060302103403408030300c0011940241c99a014601c018001016001050b0f52901c014041c12041c045404400380700800c02d40d410502900e204002c01700000851142d5130910012020803c495182d41f0f9142400a000c2c0c0e0758071000540681da49240c50510b003810802d40d1484c01501136070a807417903032851703000407003000009580b1a0482e50b0360711520074140102070100751078601c0007100d2401c10540500e0307441581041541001403215038400000c000002e41c9928007901c00e0545030100003a66520113100b0060300348150a020b00603c01c0c2181040c1c01c0c80c101070220f101e40001500c030b030715498191480202c1d082c0700300d400c056007003070940d20070603503480d4101d010301501c004040106500010084142c2c4c1c01c0e200b0501291491480505907484001c14040080e01c00f84050764100c008000ca8003880c81402c1696000b980700d80400107070307840c01e01b81e042d0848a040e01310781c0c0c954450100480150ba80041e840c02c0c1c2506141013814450781900d02038554030055441820071850204100641e1000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 829237940 1250 829236690 829236719
    0xc022a040c0801230d080c06093c0c0604060503250c11120d02100624051c050705040314060421020a0807060204082512020f0406 57
    0x24291030610901404040a942894090140c40700c104504010990210810000a004400040c00607a0000741540b680042035001c0d43d1200c10781e500a40500250000400c0f14500842d03050907421031000806841c4004080700940701c0070f00700c113150000c140402050000c0e0020701402000c582e5103d55500c406040c580044540d0300c00c2c4401041181603c0e01c0070304044112965643e28942c501d0155a40c0106150b07186800c40e410040c1c1c90f09001610004101011500165800400d000084414400141c4401d5007116409400c01c1440c44541101d000800354000e9050409648410305407031071004c14030346100e9045c1000d0034030080c8951950004000c0090740c0c021404230321486003003a90150740e1502660f004252020500140d42410b03245440c20482c1d201c01d2042c1c1d010200780703032104c0180c0d03000f5803016034089078006030400c0008400c00c10b2030000242c041a0070005c00c0800b0032942d000c2098032501d420002c00394101e00c02c558500b4241511003400420401050343c41d00e5948003402c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 829239190 1250 829237940 829238023
    0x13020a0b0403120f050f03130602090a081c0302041d0403022109270a0506060403140d170903070818040c0c0605060d0b06190b0a0203090406051c03030c02 68
    0x900344c2400d208014428801c42c2d100ca400e01502c00d1a54407000322480c81c451942e0410f5454603401c1c840e41c003107079aa01d0020301c0200480001444400d004d0403003200401c0c940c040180606d403040004200b10401d00d0a40c102008103080040310642d9541130070303420040001184501c0a0390503400c1c140c580140005000300740b1040e10b143d101402e19003041c040d11643c01d041d80341c0700d000110000d894240c11790405c541c401000341c4035074105036880d80e444a0b441a154400340540c0c000b82c03e40d942442d0b03c20b4240682c01500380d1034103950f00b86403e0041e00ca2140d0300c809007100b000080e0311503203c02084e0070940c2d0b403240900201f00e440542413009090141c0c44404482190a2201040c0c0320302d0040c1200c0681c070741040d84040240c607288100802c000300c403050200c86000703035100000c900200340040e103812607564014541d10280903041008842050b000707244121103055540c03942e50300104948220035414140020801d00c001c0060745441c909507144013104401003c540c0c440040c0c14400c16084 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 829240440 1250 829239190 829239197
    0xa0f06060f0f0803270a0e01051f0c0305030c040e04080705060a0e0d05211f0602010603080f0a03270516060c0b100905040b1909080313020a0b040312 66
    0xa0b520b400e940c0a12003024441c10356207900a01588000b04101c0e08902c04103912400d85800b0450201d010500002081e445180b0810304040108151309050303019901d400740311084100b4441480101412808108034080c04204004c40003030010250b000841d8040c2082c1e405210f020f250528200a895104036804c03544d41c040c40c008580011000c1c0071b400014141e0304c025000c09102e48004880907002001c040c140c001c4455800c092404120760310364003c9021a1307d9900040881160030000c400e1366000a04583c034003107041000c510010280c80020100440352659110307070b003100302c01070b00001e095810201c20701640114a0107084001070b88081c4188160703036400c82d2414010500022038840c1c1030200741c000030800c00081c06954030503800141624440006501c41214038129001102c0498160032004180050829040310004c0c908007100f030107101c8400b0f03658960403a0300016201c0c070186050400110215595190840085c2c820010b070340d030f1030f10750302d0624403080a082f40500012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 829241690 1250 829240440 829240469
    0xa0b0412150f0f1d071e090e0102130b0405030601031e151a04090c090519090c030308090a031d03030c010e0102040f0501111c030e010c0c05010f0207021e030a0f0606 73
    0x40a0300800341318068181c040140511910b08508100c424a2035503d036140182e60b00808200b0850700d1140c2070049080400058490600c00a03601480d00d0315004002c1c0c24000340420015a900083c0a6055a900c00c06005800d0b400b810304500c400182d0b0802000b20015809098481003036910030452096110f24285100024134103000441d2000a400b07000207104800c00d10507100e903070304055080140a00901500000f00100c4022215068411541081c01000410034144d204809681000000c40a040030391442d5a010704040b600c0451104110a20080c80c0e6040e9414815a1170310309030750000b80200e02e0307600003450013980240582000008a4a03021806520442c1100c2c0382a4140c0000e0002190604160051810305001da030105501c2d00b548801224084c0140590000300f40c030360f1a501110b601d4a9405d40300142c1000007454414045803016903580d03161948405d2034027505a6042020101003800c3c421400c2000c1e00d00e0a0440140c000c12085900c0340c02104c0c40503241406 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 829242940 1250 829241690 829241711
    0x2012607120213050d0f0b010605090102070e060d11040b0303040f080d02060103022b0c060203030f0f09030a12021209070e01140a090e0703060e0706020c0a0b0412150f0f 75
    0x407401405514900c00e4007040c004c0c8007500b00468000e00840c056000030100c115281d4034103c4610003600702354000390b004106e201503544c0410030b84020705805109444946003480200c0e40d428403020018010419a2032114a9a00c5940c0007469640014054035a110784448101070307c0f1109204900242c442d40721268040361000c100c40307060b05e03401440411100c9181803041c1c109680b0b080603032400a00f0415440c0000d0743d090040c030041080c0e4001d180c807031a1004400098200040c2141b06414030380c2c080011444020085984c2c8254904044d8012812048800e00070700a00304106036048032441070048039140090351070f08a40c0c250b9074000c1260380702c030620030841562801081d00454800418403504200f50000404614a00125407015580b0b499400a541644403c00000e030030001003840b0450741840107184901d402da444600c0d1a19084400c5c03050301c075a11888404912440582042120185007440154403c803010b022052015214000800226100c4d0079954a09821440e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 829244190 1250 829242940 829242977
    0x210709060e09060108010e04110a06030905011404080a0f020f012d09030e0904051c180b09060d020c0307050102040b090a0504140703050c0706020c0a02100507150902012607 76
    0x9200f00c3c1c06a60708840350340f03481411042c045020b0021101c0400c2410207118680301e9800220043c22950740109501a035070808608458222100d8091015400100404194000201c4450500601e828000200006012404c10055208a07000b035401c003080460b0782c4524a69a0000c3c4d440a2000051400c0c040d40c030300112a8030380d0f801000300751002100c030301504e041d851069006001306c00755100f8498183d05000400c800728802c0001c030b400111140c103000070710f0005201400c00c01d46594907080494000a103e030180c1e107000115150005a20740021205100b0760380402d82c840d00039900c4a840e95085040364022242c444d0045101d03030800141032410f405103400e2116045104603036516050750031000b07003200a0040480c03200800c4900300266031403004000103101d00000d800500f07942c0c4100603c04201c04000010003805200070302c04604141c01c0c60f00340c10203103000020411a140700580345c131142c0d601880f26102c0600320f4100d58100501201d0302c40e0340141d49600101e00443c1c1300d030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 829245440 1250 829244190 829244209
    0x30c060504060206150f10030e0c04020c0a02040203100b03010609030b0c0f07120905060c100e01021c0c023d150317090301020720091308210709060e 66
    0x1000503030141c4c0c04034004000395459410312000c080c0405403254420f0000c503a21607040c600820000e9a0b4410100880c08117200070114000104c8081d0310b040e8100c141c01d175640b1040c92010303101f9a40000880c2e065070510184400500b5070609482d00c80d81d480e540540600110b100c240c50b0320b41120006a4100710000440345480031641e081d0342848240c0d100c2561014841c0000382c10f220114030045a00e40d147c0020b840031284031001480d041c08a14800804e45808000c2d40200e6030050000d10100c1d581e07001602040741d600540000c00354a1100100d292502c800d1302405000b960440b150011b12040c0d441c82200100c490003d5558501c124012046a50400000781185011441400040c4540220300d01c5450440b000d0b84c14801758100090072603010301802c45060040c26204041070524140b03104401c50700700c0f208409450241c070841140d0b00040b100520915000a14010101d43c9002e0000c000c0032212580c410340c0f40503400078150007480d0041c003002c00c00101c81000c2510704030040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 829246690 1250 829245440 829245449
    0x17010b010e09070302071502030c0a03150b09060304060b04050708041a01030819050403080a02030306031005040c0b0f16030801080f010e1002030712020c030304060e0d0806060a05040302030106080601030c060504 93
    0x90b628036618000d0440c0203400c103040c200e030365020800f5281000b041e40d0000d0350281d180e01d04516542d824070703000a4100c46400d00650118103000d80c040000060203000d8544400e000c1c1c819599940d030703a00e007540040500094041d8401d00d0304091003d950781c04480315200b1842480f00740c211284101314845242024403004010300300402030659140150303040f1b40c10150450a20700d003416220350b9065011f03007080c0d00010043c3c1c4040100714041c40c0800c240307000c01c640f03050b0400c6281071030b8541403510151070041c04100c000c0005d5006a03145460112550240c030145031804071951490002c11030301081c030601c0c0746c900c54200040c200744c0d010300c140c425509841c0001c00640403200010700280d0802001780d400c1c8a9403106d0603440d194580010002d900c207400103186d0b28541860060102c65444103125119881050b100203150707004008190060400c4900c079072034118448044a20344242d801c000d415500b021000960001c2c0010040c0c140d0344900d50889102c1d488200c1120140200e106 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 829247940 1250 829246690 829246699
    0x22120f030302090312040803030901060f150f090909050606010f05120117070f080607180e071d04020c01020d1a1e010201090c1202120628020702030717010b010e 71
    0x4940000e8041e50081002d854040e00791407811610303010000240c0c20503809072020707400c00420451a40420710614015101c0100d00749505420241c00704040c02c10400c144051001e03441c0e4134444103001c1c00d1020300800440f1824403501d0024507007a500c030035040d11144d01007000c0e8108405078a0040301920fa42e010a252050010303881c01040e03400344400841107821501800c0300215040a1488040c00988801c41c01400351b810038030b00052100c0c00c0760000340c030a0785d81c10030140b064070381d0300344007a0b00b24910345040c0d0401c4504210640c500b14242c40f02c01ea0113440050003d04403c0190050318800320007101c10002c000c4003840202d1072401d1815072079440104126040d001c04900c00310018008010301c00010300d921143d90718103c2d41c40a80021412165600a580031450664180381d855401c580241881e4101a0104d007825055071402c01a20041c0c5070340300701d10120541c1991030f05500201107600081e038408000f0b40015112203c140a5400c000040340030307502882c45401c0840b001390 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 829249190 1250 829247940 829247963
    0x1080a0216060b0a08160f0b090a140a0506220b0403020f060a0e060336031b12070c061d01050d0e0c04050f0a1a0607060908040b2212 59
    0x240c802c002011181122507105400d40400b00750389800300401d80e0300e914000c407000061030034a116102e615400b517201400040b002c11000d1500c0e11600309078000c035103028180c416560120000144558040c0c1c0006800c203001203501440c031100c00b0b282c003c0f207100f10740c0b00041941d16010911402d100d02e001c0650030140d030742c250191a050034002444c01520600c0d10481210440740041c44039401521030030501d03107000c8001c061008500350744490b42404800b00c02500c020011002d5202d02800369540d41003242c0c40f40044110006020118191141705502550380304c1e0351030302da02461554000c0e1400928000f920fa401f021030f03550f042c101513505031141c038108036200007140d02411004508011500405400040c0c5071218080d0038014810000440a10f2412880c0e1808841400c240d0b0200210034100f02c0c916a00c0326011a10156001840407601d665242002340c510310541c0c6c0311076182c680005860741c198001100e00c41c00c40840906240256581e07440403070007081c1080000e4500c0c060031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 829250440 1250 829249190 829249193
    0x10080c030a0f03140c030405092410052b0c0c0c0b033102040c0906091203050c031603030c0503040206030f0a181b17030d05090c0402160201080a0216 66
    0x3440d0402c0603846882c0c804500181040e01c036941e60880d9415688036030002c41c0070b01940c07402c03ca640d13a002030210748070660829030010642d40180801411802030300100c9842d200b0030b102c0c0b000c40724402c044090000b0303043c016000020f00381c0034018005119603c1e00d1100c1e03148900c60140165101e8003c860350714a6824078140385060741c17024160440700541002260b050014044100600003110114a4401c8103180140801d8a00c0081d9903c10400203110038444ca54010780d1400640e1007000482c0c8126203a0b280659540c480c60010b124680700114010f21800140c4a10b0340c90715210f9a4180b00010240800340c2e400d00007a00e0095015005200041400794107072120360340030302c9000b0085042c1c1030b080302040e481400072409481c0144504802ca22007030a4000400050508658400c5c481c09800340254582c081d40e1001d000c065154000f140c15100d04108017004803000800855903860826152041601142c2089003c0340030840002d0800d0074901c2070300d83d0400c4084c3c4404a0340c030306c0e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 829251690 1250 829250440 829250453
    0x60a09090c12090f050706090f06050904150f03150207120513031401060e010806010b12071101110318070b0313170708120114030a11010c1a10080c030a 67
    0xc008407008010300b0248a607000c81c0700740500c500c5140034041a484180c5141070031803c060803500031000380720140204102004088180c001142c2640c80c155840c3c0c0c0c022070000d40645a100c04c41044070680e0100401c182454001c0207046a1240c1103403a514802092100260b004a20002d010307042007124a49026004d50020b20016101c0807030211055201d5235400040b10f20b84880321002d039503c0d0320910604280032456400b4290b003174010106585000c0340340d10b981c454086004005120240451403442c0107507588048059008020f02540c408400500b8254001f1a44442030020b8015480d140803c040b0303400341995140c2035030070700e15a91402a00440f1b4592070040b10505182c0000040b4410b001d0060110700340700c0c0c1c1c00c50381e544c004405d0908204d10180c02640f404210041c10340c115607000100c405003564009a000d5800f401500140e60f52460340b200988140100100b4620040701e10507042d00c11001d0400e01c542d202e0b00d410f400d9941d90036070521560158020703690180071451 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 829252940 1250 829251690 829251701
    0xf020a0b09032b060801061a0f0c101b050304020a030b060105040e090601032d030e0a17010903120b010c060f0e0304090b010212120a0b0a050414010f05060a0909 71
    0x62070303421240b074559100c1440c4441600d501c400c08015029010324243d040302c1c0d01640b002418210000d1210030300304002030043d0b811200004030782c6540000c001c2060f803819000e940982000030161401004002016000751445251141d40c0030080d002034541d0901030000c0d24020794028101c1c10245040d9034070340d80508406400c0506010007400001001c1c4140d194643c49901100041c20482d4510b250030400819451200d1101071071080700c1c00d001048070346820b090550145030100b04e4202540100d407404102c2c0c0c002d10030f020b46081c2104084001500f048803440d00c00d60b504006070300755001d50701c111340c500107000740010008000c1c0d80c003050ac5600400042451030b0320006906185613a820f245501c40d0b80090780b619280e4884028035038051103915441d0903e056031070f20f8610000c141e9441840000d00d00c0720129038038035404500340c441010300400f421000d0b0040200491410016038010000d10481d0020314207002c01180070301703040d000c5c0d43e0660308a8451098103030402d03520101928 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 829254190 1250 829252940 829252951
    0x70306090e150711010207140601090c050a08060d061406091014010c060e0d1101051e010b0d090203070612200708030a14040f050114371103060901060f020a0b 70
    0x262084800d0005136080c8010864207100d006110051560106070a00744041607128509243c40c040d218110150094111114040345d8600004641d0350400081d990341441000600071914203002140b000c102c40e11580d009810071903050026944004400b641d0680c123018580185241700708012441d40107420383d0182602c6034101184e442d4a50000a162451030b00f42440014140d0322500a100d2080c403400307801420030181a40c58001d65403406041003418820404a8200003d00801d421140d0b400009255802402c1c1d0711083d9581714028580000702c28002032484c9000c091360460603100d0f00036102800003402850403c03620740c176412140c1d04010902d2240544a151423030284500040103442580319688400c2140d0243c206282160002c00b40c0e07503181c034550383c2444100344034003030461452820032040e15809105188038608485140d94004c5001e170520314000c0c801b80c13800002d5845104150342e0038050340c0c0d130741c8011203511442450060260b040000c01001041040c903199030b120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 829255440 1250 829254190 829254197
    0x250806011d0a05040b0f0402070606170a11010509061216030e0307020906150f070503070b0f10171905071406070c1e0320120a0302030f0313080c0303070306090e1507 73
    0x1b024001c089003d0303a00008049500503034409c81404070b0030a0705540304540328010300600c0110421ba9078000a084180c01c3c0c181400004100070000d13076140001c850700300480641c00703111801c10f501843e803a11f000210140c086400c001c143d290181000007504c025540041c100c0b0301f543c0380d6505200c0f281442c4d88005405010400000b902c0c0254100141b8007103100300001c40c1c8d6025581064800c4500261045546c42000400d10007a041d42214181c162481d5116010145d0b4041c0907a501c0c0a4284002d0703001701a40c112040c090010205c1d441c000c0f0b80040b280901005009002c11901e4030a1000c02003403652030920030701689040e030b030f1030080014900414030341c1d0715100d0300c6401c14281303005043c00030500258000c1c2c0090408440654071000c0110061807007500560b0040d4482c0103480343c4440ca0200840000c0c18a0a400c1480c20a5a00414000e42e80d0044e0000d854980e4000c03034440f00400e040c04d0002411025911500b41107000010160902101c2482c140e451009e015091700c1c00c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 829256690 1250 829255440 829255459
    0xc010201140c0f25020a0515191101060b030a0509030c06070e040f05010e1911070303050406090b0702060403020609070b04030b060409020910060915080708250806011d0a05040b 78
    0x40f800d005a00c4440da400d1131a00001000c1c25204001418030103401c0240954414580d0301103a00d00181a20015243c0d00301202c0d100070a20001c079076007a0a00c807040b0300c6d50701300340d00003c440c11804010340c045c0c104203000b40081d596600075140c5e80e102e40a002020b541c801c00000d0201c510940d00030300c5070340e0300420109070407003045e07892010345100303800046040d410702080c44441c035810140c0c058807030005881400380803082c0410010900800340040c0905807501c0004041003555800a0b5116610040850041c100408020f41c3d840c021a406c07009840740c8404201220070011300d21003150440003030030f0314050459556092900340900055001178546071242c006a680740f8525114101890180e0307020740c42c004005110b80707040c2c0d0103001c00b006441d90360f120003540320f000d595204200c0e080054003621012184400543c10b000c0c1420020a112100c92207a54040e940c58040c8400b40e85a0303900c440e00e9072614500e43c9800c0040d40d4010602e000030042414140c0001e442e60700004c0c80303180b1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 829257940 1250 829256690 829256707
    0x616171312110c0a060207090e0109300206010f0b1c0606050903010b01230c10020d02030610050306011d010315080a03090b0403201309050f0c010201140c0f 69
    0x2aa01c01011507002c40c510340c2200096001c20000d6040070441240d20380149450240042d4032002a0300954106c0354544076403110000d030942011260716440340420340d8040601e42910901081d04c880c0c1c00309611082c44014030b03207100088040c182c030300b0b6004a842141c94800c4107401544000301c18896a5054506101c208029100e020001c0610351030300c035503d412120402d82117072a2006802e05010040d04417050744406501036012030a4485403140d40c2d2811182c0c0c0f01e10701000881000c0641e4000240b403c10000c058018500403001550319040e000708001d41981e950000710782c41400615809a4051700c1c030407000c4050503168042c1400509015914803154100007203400c01d0300c00b03030300643c4e068080551109804004114410b0042e061500715601d0078001c0c010003c06401c8199655403040c40740ea10803650549151742c1600800c042040ca00e400d40e107074880b00540c500180600640000c1c0c2c0d50041c000c40ca50500723001c2c55480030b6501c040e9583d015801030286030307014403000e200c00003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 829259190 1250 829257940 829257953
    0x150c07031707020d0e120a1a09030a12091b06260105060a030c0e1c0c060801080d0c0201030227010909110904051902070b0f010506120c0306010c1203020c06161713 72
    0x52047d401202d903607400c0a00072280c00a031410142106002d60b20410555003841c1c2e01c20803043c0210701c10b00010618515509003010803000c601d003c50132031411240000342064120707207800300040740c4904c00c591521040c2d0801383c1d4240300f4400c558210f1401c2003804402c9109038480c2d007880326a030800d202071900410209803020f410100c4181c41480010251042c01a0704942e18002d00845c41d203801346604094407552580c1d840959901840245011136007103a003c0d805880618400c0c101c0d40e81d00820041100f91040c02c529802c03804104500008a070283c442e0040391002d1202c0c3c4101c1d4074160f641c509200c000d013401000da0300080840d903103411007942c1d580004c0c2402405071f802c001c0c550903c0031504180d504180d0200b0b00c140c0c41080000e81901c07009500c2e542c0040518a001d840303030b0794140160742c04403461000500704400301708004005600750b8080c00d91084e0010844039a580d6008401180740018114007011441c01104203000f00b1104004070340c080135038040c0c7d65030b6021070760b40c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 829260440 1250 829259190 829259203
    0xb0a0305030f09120106030309050d0314131809080906070c0308180108090a0b18031c0515011403011202061b2811090603150c07031707020d0e12 64
    0xa078514000107103d59a529140401e020030781d006030000c002d0365203507540c0580030001c940304c0c26000c0c9070380360b26010602d8001d414500380d40400009a80c0d17201c00149100c9410020b5000c1d08001001d03610b07006041044d00c0c42a501510b138041c94203490300c44441c003084201d80000000b00c03003080c108003000c400641c5d058043c00c0380da4520022010f24254110025011000090031070001d40e00c4017585001186d104030a80b1b401c85d494102c0503d80302ca101181500b10b1040c01461300001d00180e40070200d007016a44118820b944201c40c00035030075100401164603036280c0350a51034a02c018070040c401c882c0c50220f8132100c1840104028a00440781884e0181d04407086d580c28591780140941303001d8490380114001c00d0119004805811804994031412110f01040d03c03035024103030140008026490401c0100340e240d2031800306902e80c0c507001c1c0c0f0300300e503c2c0c1c0200d0040300043e581c02d0340b00ca09030139078940d4035001d00d5240d0003030001008805421034651b52032401e11070344034840c1c40035140e1030040ad0264 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 829261690 1250 829260440 829260457
    0x227040201350a05070503070807050706060302060c060a0b030c01120f06030b160801050f090a0c0203220906060e031209040605060c030a02010c0f020c120a0507120606080c0d060b0a030503 83
    0x30b030650b4a81203c103182152401044603080c080b0400401107034941c0302ea5070742d9003c511401c0c103580728070081c20600000d20301608025080080040c08441000001548902c20165140244a05d0700304a003490340310b0403680d218501040780c3e0707508041d40840325081080140c0f2010800500e07640c1d04c0d00c41d8032071a00706441816840e070903680f041089582c040b0765503000d4102510100c0c03081180101140111000408520040740c3e0340960a10f9030b4404d004032003003440b020701560083e000c0036140310008283c5d80b280100f294a000070018a0314081c0021540c0868024081c104607444006499815030080214030b50086e0781381c3e80403840c2c0c1c0e00c04000c0c11841182c1030082da143c521749032001c6e00b1650150340c49014401c21442ca555031a0b400542e11214450580301c5850340404104200d01c2c000d4010801019401102d40102d400003021301ca84a60902404c01481310340d540d400d5141d220140803a0003504001c401d807d18002c41d02c1c03078110350203410014008000d260740d2a11380c01d0075a0485c441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 829262940 1250 829261690 829261787
    0x330b03120403140f071d0601050a08010902031024020609161a0c0111190306050619020c0a080f060f01060e06160f0302010b0a080c0d06050903071e0227040201 70
    0x1c06c0c0302d44119241404d41c0c001d0f0282003991505074242e101a00c00d500522500301c01039000000a00044034601d00b06000705103030050f503148108101e20413440240c84a6110f0014805c0200046100c54002081202c40500a00380c000b040e080c00d0505080041d1b0304403403410705004001d02076807100244182841e07443d0807c2d6842d228401c26900000c0010003860400405003024014001e664480d42110007200f13380d09100300d000b03a00c007001e90400c0d00e60107495a03c0303c2e442c00c002403880c03404660581c2034945d00e81510307000d41e902c1026200701c0e84d080c062080058507504802003e8200b8800030f2030360204800c655042d440f0705644100303034403050040840040c0d444000039910b9040900504001e401480050305109681c0400b0814541d103840300034005a0f21000840d074410380902c1107419a075005109000444945c01c0c2000540544240032405056041c17902c000650340668140c40b000700c0340e2840c651a480701e03001152803c441c030866030000020601c140070400301d41e41c40140c94011144 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 829264190 1250 829262940 829262969
    0x5090102071a0d050c031e0a0f0f0e1504151523040c0c020603240904050303060f0406120219090c02010615020105070c060504330b03120403140f07 65
    0x1a040f043e034401070041c00c0805001d100713001c200d1498103007501d10b4101c40e0001d441c850b030b1000000c3c03000c2d0145000042c3c50902e00400e100c2d00782c050350003008132000c01008403410f00c035040340c6d51200303c6411200540423080d003180e04c0140c201c40750008903410b1900d42c0c101c4a52601c540c3c14820100d02150454501c132480340c2c45900078205800b0f40001e1031514100070259030030a0300803604620008001a6203031800c06003504444802104a90400c0d00190129049150500d80130b6902c2e030095482c1c6102d0004c4204286040c5172500640c81901c14a249421201b600d40e800c2c00210100000e6541c000d80c0c05140c04140401540320309441c5449503800890a28a0308444440302a036031002101103905000c06c024445800c00034050000e580410300288559403420b00c21615124010f07125031940907540c00500440c4c0c144407009010441e018100203c01d0040c04140e42c45007805d4003018180400c0c4800c00c080391143e0b00c14420b00428005031104405c201c2000e038100000c50300310350801e03040e04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 829265440 1250 829264190 829264207
    0x3060a150c142d07170601081207170715051302090912040510031e1a0a030b01090213030b0403080405100204050d0f02180a29090705090102071a 64
    0x700315440e282c01014007900412180c00400c1c1d0040f1928140000c0002c800c00d5a01e0b0181020003140004001280f010f580349001c001040e502c640302846146544d100381c0b800b030190012080202c0d124240c0c4000c00c42c4030000301d180c103143c81b900240004d943e1304222615010003a00d150080900c075890181004403520071520400c454008003030810707005503101084040d80d26605504407801da902c11505001e140d00083c03030880151400140700c0c841c1b14580320440c01e000510303802000101042c4080510205500f200b07000c014007040c44040c1c42d961052004105c605134580c01000e0200c10800240d400360384a494014a50909840440c00602c0e500100018040140000c07800311440400a51401c1c1c58080041c0c000b0403103241c09403050100e4160b50f01156a404620301c1280400340c070000c040d29041645200800d21102101d03400b40628040407031218003551030127500000248200343c0c0b5100d004085491303412220909056104449c0d0105507507294080218143c184400400c2e52420342 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 829266690 1250 829265440 829265453
    0xe010914030a020709290303040305070b18031903030b0a030c0e09121305270f060a06090605040e0a06180b0f0109030201021009081603020a05061e040803060a150c 72
    0x44d9440910300034500b0010005102d0160b5004100041001c801000e400c0d00c080040d0039403040380c2c40103055104e1000009030041292025000300759100b59081c0e01340408000b0b041d100c00800c0c07120912014010380300f000081c0a81d12060341c2140240c00807803019180e90b03808d401e0141c17942007140c00282080800c030b1203003801c01c04a514040d50208007410404a404c0d55000700300c0e00d004991241840e0207020301c012044610280c0802110803c0d4281e03230134256114491400203a42881c043c2d50420008a0f1039402480f050040781c00b5035807194079003032900600c001c002c2c80281c0609003c0307031240e00020b51040d12084030034407a20886030001e541c215040401c180080d10500310b50600c5a965010030240c1e03000305134111001d02c16500800c40d6a1246449000c40c0716808800050a80241d18102456400510300c0101442102290f8568035842902d90340b142c071100b001d445c454031340c000040008420030701654100300090005a1100d4590090740040f161811000340041c0307002801d0010f0104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 829267940 1250 829266690 829266703
    0x4030230070c05040c030b090103080c0a0b0a0b03060901150506031008070305030319090b07051b1207021e0d080715110d1b020c120a15050709090606050d0e010914030a02 75
    0x10907040c200047c40e114400324854544c144009800440c01062822001c20244a55000301d640000041802e20b001c1c1308000042400701040ca000740320342c2000415030181440303014030580e00300802c1c009052411042040c554001020b000c55178000d80300000d210441048a9400b0f54407030800746440c5d15115480b4140021451680303001c1c6424002c840011584480c0303421b41001941c50b20030b6950501512990103490310402546c00751103034480c0441808100005890074038403c842e190818820800e64000d51071290715002d071300201d601018030000d08400020000d01d445000341c1050768071450100011902000421030711803000140840610426102d06c0c0904000e00e44d007618842580c1900035991071021100fa80100e10360b9501008030320082218082c510340c0000e0288102c03194501c540d0141c041601c0e0b200c0483d41c0120017242010341801000d06a4410b5034566040c01200014503001e010001850344c0e507035507204400e1740802c001c03640840310f024004000b1503641214030f01c0280fa112 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 829269190 1250 829267940 829267961
    0x708120c1810030e07060503010617011406300a0b0405090a0b090327030f0d050f0a1103030702010c080a060b16030504080a030c060b0904030230070c0504 68
    0xc0c0304018401030181c181c5500c1d9288035003560031080c9006240401e038002c10740c10b800401d0038840d460340001d001d41d01c0b800440c16100c07990707031b2208020b02106224013250020701690095403840c032010081400c100e80941104642d0304000b81000031071200c0c2071200000d001e404000103c20004100c00455180108100207405803000c11103494540304603610b4054810b001854190741c00081160740c4c1c800c2041c1e5070b40d44140d15001000807103005510101200c40c4003814003a001f004020b480c00ca00128550402000b1070322514070301129024000d64503030021030140140215682284c100541c200040c0d4416440354000154003200454050302d8080010003100d826810100103201c03501081e41901c040c0000450f02074406103551a0680d80340c0200d0300710400358801c0b4041402415803240001040303c0c060042001460403401c2400500401103a000d40940c1c00040c002c1540441010004e1102c40301460050180314003890524142d4040130040d03548001288003440b481c50a4403d064251 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 829270440 1250 829269190 829269211
    0x160b060901030b190623180c041503060e040305071b0b07110315101401030b0d02090411060a050a02070b130b0328050411010809060105040c0e0303070812 68
    0x41d859a528405000b60003095840e0f00e0050200042440001d5000707680a8003490710f0141c2550038403aa0303060751500524411340304101481c080601c2e001c12a04990240c0c1004180600e0036003041c24140ca101950f00503c0d04050760745038001760511501d04504e000742d219a4865136510014207000d98420110303a07010341c042c481180704118116000341218825580f10b1200b0074890300b408006410540142680110900e4507800c001520303902100240c280d6401c0f4490079240a9010300440c1100e0065aa40ea001000c408011015150114040b03600c1842a201b8200230f005100124859410103d82e00d0007040c3d004c034160b54826010f00c900c01c00780011440d11070810442c81208102d4005903c220f00ca100c0002001c1500d01e880c2c42c0c10b0305203080580720f168194072140c07a49500145070484090f94900c3d0107251590940d0310034960b042c02101c05400038082d6074208420071006007045246c100a01c814001e07809410785042c0b02812840b40900788054a4404140c0701000c0190001c0c40d04d02d82 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 829271690 1250 829270440 829270459
    0xf0b010e010806010f2001020c0f0309010503060d0219030524090c060f0417070f0b070b24091006090611030d1d0a200a03020a14060f160b06 62
    0x41e6400810103510201c2481c16000c211600d8009990b4501145012101c100c3e000d001c1502d134440c150002d007081c44c4200d04941011804c003210039140d00030059118001441000841d07101c0c41c0c03003c088a000c500003090004603001e10904c103041102c644c1e02c106c0d0355030003450070740c20651240303a1001c40554007403042000740d1400302c0d442604d803201c000c00c80b03100b086c02140900201c520141500c0140004100441e07841302110312182d0354400911503462074802a02c03000c207100e030350002a591100d6011201c41d109459113480c42c0300e20341039010305114a546144c0d02d0035065070342c0c4407100d00030740b5000300d0341c03180901f4002c000b0110b144a420038003c3c018042642502c0c0000001213905800441d14005200201c1107000c01d1140d11400d0404040e114600644003031081c580c00c0208404608a030360010310780e014040c48400030040c400690321400001080007480000c050959035040010712161070310000c84078404c8190403454080c01003100f000c04880401080041c416004882110704016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 829272940 1250 829271690 829271717
    0x801030b090304050112240b270d0201030b12030a0302090a12050316020f100f080609160c05160b030906070203190e0a080123010f0803071b050d060f0b01 68
    0x400d4141c0d2001d20b80e1f6610b480262508030b1841480d1100c001c1030222012299541c1c001404640184d038991502044a40d10000c80c18901802e00301c01500180080d44a18203035001500240124200c0da900320041c08406540013000744000c202803203039602d005880e03c801005000780c20200e600111350050040304110042200002a20046001e24079680c80200c030324804121140070350903400c0d8004a0614896001035082402510f0541c1c0300c1e66103503115580e0b0010003c03c1c038019100820100c40d4000801c206600c161440c1140b240200100c0c0c00ca281807284d1602c0202656111658655020040c00800c540c1405425044150b51000311b050004002c03207200c8003005181d00c0814800600c44148194650410520083c00d00c08000c10400c610380c030030201c18880103180f050356101c2100c004603044c2d820216903015525800c001394240390050b41c07000050789460107200f00440341c41c6800112655500d0760b282481c1d201d420017140c128424000380082d9420f1411311418002d20b07011058 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 829274190 1250 829272940 829272947
    0x1090204061b05060c0711032406010c030f030f020f0c011d0705090a0c020c450403030209030a080711130e0d0305131a010e07080c0904051b03070801030b0903040501 73
    0x1904090361000d42903075501b01d840d20000c9080d42c155919014000c0d400741c4a01d0741c20030b40c1012094980b50300700c0403090351044011202341e00002c8008010807001040c02d0140381c420343c065000b503100340307000510300441c5040400071500164403403131143e91200d02c02c0700e040a5001c0304403078256558004008140c2000000703408641c0c0107240320882645c0300344001c4002d00c00c0001c08034484019103414001100805a1103101d6003091841207c8509424160304003420546820300003660310310303180041e40f40d40e60f040b030196001701c1020364180324560010f0003162107070700100603051156071510140d030041014040e030107500300a0540d800c5c2c0703080b005811100011545206504207841e0001e40e954034251041c04928205001508170513503888e002c40f622885800c042c0c103131044042c0303940680d5124a0111031a140450f14029402c0051041100a04064204c1c58000748000707078901d682e200140c84031106800488050000820490040050050403104160800c05800c040c514040c20000040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 829275440 1250 829274190 829274203
    0xf12080106141c0f05101d04060b150a0f0909113c0904050f100312051c0506040c0e100c06091b08060708010311010809120301090204061b05 62
    0xb0b0807440700051090503858402d020b0441c6400c504100300306400b03e2126600081508483e03003500190040301c081640942c1d9805c91441c10180000c11646503a81c1da41e145c041c045041405d038010000d51a0078042400315805480c0301d02d1f00d5691600301a041e40c80007003512000c0d42c09541a186404078403070011040c10100da05e011041103001c511391900b10490078103154003440107402e0b01a003000b1820008141001402c2c90482280c2c1844562036234089803006030400d54001c140540c60b60010000607101c02c2e290380f003403202030805504090000c91115130702075a0040390500143d442080090b41c0c60a40f040c0e50740c141c410314100b06a52240350204032540c00441040341031000704c11407101000b40c0d5400c81588294410501e4102324103165090403411a540035040d0750740140d400069056204000c2c0a04803a00950304c900f141101d0401900c141ea8003410424203070044a403119a0032130003a000f50300034860040b00681d00c500e4054014170701c01019504c2d0b6603041c0712034940e1010800024a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 829276690 1250 829275440 829275467
    0x30f0306050a050109122d0525030b04051c050a030e06060a0902091f050301031a0408030402011b120206061801080601051c06050112060f021c0c020a0606030f12080106 74
    0x400b4168403a04003101c0ca1500f5901b402c200d042e441e1f082d030564000d444200f40304588200111340d0507500c001260704000703501c00e0340724600c032040c02c00070404200b00e0424190003900074015251010a002d070301a6040070b1040310000810400510031610562512400c9112021080602902c1c18100005102d00a16100b54460903401180c4d0340c08503941c02042413021400c2601e50059400c640102a105810902c42559180c2070000f110703c82003418107803113210f60340c0941042c3c030303540c0e440d401911072220142030003e14680400003000010240c140444080f01543c0080c00b0360b1800d08100500300024144004008444074010450200005402410740300b00b100c820825141d5100320b40002007983d80040c0005003081c000042e20500014818040c5006480602c0105580350441003a84a21200c0f80d15103240c982c1d0010028501e0780c840b00d601042ea205030b0f1004045138880300162103154100303844c020480c501000410547c400140366529080c1011500d644c0360ad5005841180010700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 829277940 1250 829276690 829276709
    0x11060a14180d0f061103040c23191703070807200303030408030115031a0103150b0c070e060901051c031404121104020f07060e010612030f0306050a050109 68
    0x81003000000d65581d015040749010309a000012180c1c1000200c0354103802041d51010b151820800310700703450400b102c0c421500103404a400c5481c060342102204584502d1031480407211000ca00281e89155640094030003420082c100c084c1050446035404086480ca4041c6600401c180c0001840c00f106a840c502d0300010105807100c48005143e80040c0201c030344950502000081108210071071000d14140c030100b00c480f03003050035040c02c250203d41840c0041b0180310504608044698403070742200541e071b480749a9145145070f03030f00c0789201c06800c1420a824617401c049024824845e00d07140c000d5000104840c000065454800400d20780e201c0341c031102d10b500009604034024140204000c3e210b50241c402034540d40c0380c1e1f581d8840f02d407040b8000110303510004020701207050300d014000e4a44003600400e45510340140e6545540040014030240d02e035a54070b411000480c00c2d900412851898001d80721018400d03a0110028110b540d55041a40310f1023100074103200360790f8055608400e5900204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 829279190 1250 829277940 829277947
    0xd0f180b090a240e0102070b0304060e0a0c1811030121060b060406080613060320010e03030c01090c08070605090405130b09030406030e0105012d09110711060a14 71
    0x7404120062095005000700340560203008014145034070150321804255611107400050310801246c40d0fa003e4400c650940760244041400324032140c0c054500c3d0103c1744212031500c505541e032036200f0301e8642d101102011a030780d0f09940c1014035000b15000c2c1e041c02a04145550705150b250005400801e80d0b005003100e241106c00b0800c0f0782680003c000d08402080152a00d40e03441d801007903400c04550352800340444069a200381501030107000d00750ba034030120000388000c050b80f25840c0d8002c55078001e4104140c4241c004001d440034001040c0310243d402c000f04030b104203030a007520038420359400100701f030340060410030484c0c0c0d0180588255000071a004030310340d25043c0074142000c10100b005860416001c00740403d07244000010012507520303031428030040c0038208070142222024401c2c4411000002c00c580200d170044034909000d8602c46094003c6a138031620b00c0700844620445040040c0000904e00782840602000020211001c44002c1d181212103a030081c1b105003c402000250500070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 829280440 1250 829279190 829279207
    0x5070306021608030a020703030608010504051e1212100501020d0e040207060902040c020106030201180501080609040203030f120a1107082a0d1e0912030507061d0d0f180b 75
    0x480c0b25198582c1100031182c40e801e2801d08100258810101100401d00d40000061585018024688119007210247ca42005c0226a2103410104174031003102c0760041c2900f103d481c0d05000080c10035640d60319841e00741031408188124807070259400050543d44400011045154420072110b403074181501c002d0303265402450710b40068026118025800380c1001c4400124582c15409001241d00036a50410440c03805e41ca81c80c400900350050b00c0c0081e40e09800604a418002551a041403000d41103d14040d140d00010240b5045072f00f03440301c141e4482c001c0c0700d0344800d13500501001c010b00c0701015140c00820703640d030f460354030500c00111101d8014100c0618814681000360241c000110184c42000c0340118000b04603401201c4002d00d200700450015407013600c00d445540a842d05040d080103208003648094546412051003101c400e83c84150580111401400c07812540d81c0c010700a20a101e100e002c0903000e03411645c1c1c19401c2056000c0f80b0145c801c070340c1402c5c0c0308558803640400d0703031040003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 829281690 1250 829280440 829280467
    0xf150a0c18061211090f090603030c0601081c02010c0818011d0d03060905010b03071b060c0e12010524061e040e0906070c0624030c140d0507030602 65
    0x94528088186840c440002c241c1e401c0403200345060742044080000d03a200100351203030350141080068000d8960b2652001d00c0c1400c00009400c11001006c490500700c0c07040d005440c01500341c00030902504000294420003034103c915104140b000d000900000c41c900d10b004202e114010455807051038040701421150901394001083c9040c000c8142241d8030340c84910503614400101d040001924003640000d071a041445454181e07914290356918640f920b41c2d0803603124144501d1401030142d40c1a500b40003480031710644d50104c1c911340700c00034040c900d01c0400c20b081401c602c44c0902e40e410001040510300080c260040d080f448900040031901e049030206651740200c00b2210314102d01001507440c079400342e80180048624800c00c5401d80c2c0e030360301c4801e03444000c00ea40303642c040f452082c4500002619908410140d9500448003c1c080340002104221110145d10580701d80c80400001c0c413491180c0380ba0000c01c0b001c00d82d1101880a141d0740c455503a44410310000d81256404122980c400c0c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 829282940 1250 829281690 829281707
    0x20105033106020418140106051b0a05010b0f09040507150210020c010b030d0c0506070e0d0605270111120901060510031a04050105010c0b0a0b12060105030f150a0c 72
    0x10340d51207107604500c500d4820001d5005000d219440d92282c9910142d01c006400b858100d08440c0c2c9180110743d1030098151040e40001c0250b0f051022201c8680d644044c08020790064140a00008600b100d00c0005021800d500010110b0103801140104804210000b80d00341c1101c15102c51f68840b5251036a040341486280000380c85c107280009628410703840150405451200110f007582d040fa00a034009641c0100d14010060654008100280049001714852100b012003d0640e440340741309079603800100e9104480c55400da9004d10180f44090041d02006100c00304090020030130883d00038105c07015400f400c2c1032242c0d0322406200040d0042008c2d0000750041c1405042090136089090000d0081e0582280d4440047c0c0007400d444158540b03405018101c1d501a10b58600400540c1c840003020342e0010001448103484044482043c1c8442940c1c20034546400040c001039410a01014100107001c6c007148001d900118841e02ca075501804001d03000071501c100044c4104098409075003d08 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 829284190 1250 829282940 829283011
    0x5131404150b10081603022502010309020a0303050318030a021b0406080f0f0d0f1407030e13090501151a16050706090816063005101802030402010503 66
    0x1805010f2102507103400851260007004100c0c1114403046118000310124092008a40601c40302c6914000104912916400842c1c2c01890301088040032030300407a8071030725254002ca0000d080001040300019420b126030114841c02406180340c00c0503000001c0d0358140c22840b0300041d40503510303c40b10f83c0d600e42d40a034004048980690315401c01c0030a640e0f0b103c03490780700078504500865840009041c030401e0300c0a020911503c44410800c4082c950780260340003140201d0a00000c03a91070b400070382c1e843e0354120312001241400300710584a0b103071840c01d60b516030b401078020385c8801c132050000e401d661200a40074198a65202d480d0401c80e807940c11907506000c0301400a00030450007040042d03000070309078142c070035000c21500341d40400d110518181110b442001c001501c041c000c41900043d50082c107000e4800700304441700b510035101c140001c40d82c041d2409011840641410009038100071a03c841c8620103000440c00c500d41900084d005100007016100804c0782c20602e0322001a100350100f0410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 829285440 1250 829284190 829284199
    0xc0903020a2706151701050913060f05091b0a05090604051e0115080609040213020a03060b0c030c0721021003020d1409160b1b2505131404150b 63
    0x542d44103100032404000c02c50420004045464441c4901746101c42281298009070a0540301c4c1e0700c0c240746500c0c20309581030440c3c0700c0340c407040c00c003100c2011402024011055000544018101010740714030003218600c4142c0141c20090003000303983c2d1550881507010350140c40100d22030f9a20515901d809400e00072006440b141d4800110b441e0400c400c2c0303201c10000746c1d11051811f172035480420401c4501110000e600c19800b509503106140c564018003c010381d14100401d009444500c2044c00303070010003408003e0360012940c540300381404c004102c020042c503d2030030304184000c0e00000749641d003c00043c0c000e01603020008442c91180c0d04031000d440c603604d4100310f90b0301e48d070102d51014041501d044034103214100c01c9400c0c0606140c0043c4c1122820b10000d0300e4454060403410001d4214030700c4101c01e00503045040c42c01074100080004030707210031424a070454240801c0010f9110725000c2407160310300d0519131480f80c0c0c06404485800c0752b08200110f0b41c09030b0f24400b0001900d001c0ad64140c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 829286690 1250 829285440 829285451
    0x2d16091205030a03110c0a02040e101d39010c0b130c08060c071103071d01080106140a050f030705040f0b120309090105010c03020705041e0c0903020a27 67
    0x40c0580400030b80f00080c5150740030301c00c1c0031265040c41111301458800c000f45400c40081c0c4801817820390b00401e104401c000a032a420344080d4508401c9542003408841200401c14100220040501040a030640c0d81e14151914501042400d041c098140689803000c02e052480240c050f0300a0442e26246039210001d0100381c54a4555404822030500c4101c640b061407a50100c0e6041c00401d04900c0784804203581c03414150240c49812210603815011038050188800120784c1c480324030380490115241550034601545416900703421035205510111036070042003204000c0350f40301400c480c01ca40044a0f8405402c04c0c01000030306042943c2c4c000d591051800c40001da0044c0103811070704007030100322151841807008506103900c0f44501030619074003020980041c0503960003641c0004080d40a48120b42c002926200813070211445041d100c0703a1000071303901c200c100c2c6445001e03032070074541c5d90314000c1040d519650202e9400b000600540c1c03041c2c143e0072004500000031311104045441d803076409111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 829287940 1250 829286690 829286693
    0x190203070302041502150a09060b03061503192f1e1311160c0e0a1a0d0c170a02031009020103050105060f0d0924052d160912 55
    0xa43c49841082c04070501d211403035031194004604450003a02c848642460350b910324803030340014400c525080703c52607540d03d24540c4540f0100115407282c020544c2d404a2300c8114030805140c00c114078005040100e00706002d23030006456120888142800c000c440a0620000560b2241904502100c0d500141100d40030400d509800c280e500c000b84040d64a60380c01c400c071036007900a490041003003607070406080008503201d9440c0d40d5401861801600e400c00101d81301d1030200d49241043d01e880381d80c2c94844460050307040800c03200b40381c22030701254a0f480402c03282c0e561191044903880b540350800b1704510700300440101032080c0f82903194000c003592030306001b141440004205a4405078006440d001c0080b90310300b04581113076000c4102c0200141003030a28641074016010300c0f08112041803120350705562182c0221070410b90700d1801071002c04c8501d008002c40355550b80d0f040030344a80c0a04c415010200c1c1e090101010707008a00140e41d40b044441110080c0d4082049500012590b13201d40304a00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 829289190 1250 829287940 829287947
    0xa030516021e041b0507020f01052505100e0606042406050c1b01120c0903080f18030303073507090603060914150f101709030c1519020307 61
    0x101c60b28122000c000703081e0070201c400903600e41c000f11140403401c204004405464000540c0390341890514102d0328080c1f520811441c20b0301d0980ca100006461a05500100041400100d40081a20a04001d241c0f0350000441c3e440c2c0c0043e002070300590740c0e0031881c44a01c000c6c440300e100c0a400300c4030044115607035031401082540080c0082d880ca004884181602514040031034503400b90583d0748102c4e103001c02d01308038010000d10640310700b032003a0300e58000001069180509a184c200000190311510f003098181841e904810806100340c0041003045200b68004001e611402c50202c003410f80da20015008102580104d500181090240030030420250760242508044d140b80380d40a11032980ea900c0340c801620b004104400313401080500044100c41c10750340014811500810303852a0301400404034100700c0044030b403800000c1d001e02204806144642ca00c0e90850744140080d440c0400d022803685c6ca03507140407488805030401c00042600c000107400c404510034000d42e41156203041600014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 829290440 1250 829289190 829289239
    0xf0f05070b1b0a030e060a0915030605010201050a331d010503070609182408010605031b06070210411305010f0306090e0313080f0a03051602 62
    0x11001d142c4264802c1000d2004980700c01c0ba41e6054440c003042030b22220401c42d00790402c0b49040c08020307189000007041010029041020000d9483c00600d80c2c0c1050002400d440b00189080c62190404810b203420070200071400b1413100c19645480c100c6540d407020200c012042d540320200700c00c200b0030a032440720740c1c2c0710240c2d0480383c0c110120340c60241e481205076140c05240c4104070310300c948010f1207401d090094100191a09034647c000c0d6400900d501d101c440f04005400803040360790743e014140507a060411810349881c0030000300099002034100040d24902ca0110002e018503040b07182d000c0514040c0c4c1f00100040708100d640c0182c4501000fa00c1390f85207261080d210011128411929200c10950445c0c61080c8203210540c8810301340300054502c4604500781104160380e80c8000a1402018401d040e00c515010700615a10045921003207410102c40c2c1018107682c104404060f200d2000040c9110f1240c2c0c9414403a40320b481117100306042416440700650021504080003201c8062030038034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 829291690 1250 829290440 829290457
    0xb07060209040c0207030b0f270a03090504180602070c03020901031b0603110304022404091505030c060a0e0f0402040806270c090c070c080f0f12070f0f05070b 70
    0x1000f520100c0c0e18101ea41716001d200242041903940041001e203c140c90030207500000a03c09010010803900a030440c1254404a04941da04003d114000f016803113002d0710020311044800b071085141d44090a61072500c0750400400444d030016920042200c00ca40700790007150020801092903035a400e19800c1c100703100f00590040c41d10320700080b0313580b4083d118180d0004044046203085030ba8560901400c1c20503854482400101c040300c01e10702072a5034000300094603c90fa000300c2c2200a0541c00e1822001e542c00080c4650010418401d80303031a030720240d94060780d0a03d070030814450741c08041005034100d40c02460700140001804102c407800000d400c0c2c01075402070514100910100220900c2151003096112140c02884809616141050000d50059201d403c0a803501d0301320394500480c61040e51159105400ca149003080c0460180250301f44038a003d406405c141611250702245403240e008020701c40f510303003204d0005203c00d034848813040c1c4d40c1c41000c076401170361a11028012500f06458 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 829292940 1250 829291690 829291699
    0x190812130605030c030105060922020a181d13020d080304050c0a080d26070206010e090d0f0309060f0501032f0f010f05070b010e010e07020616110102040b07060209 72
    0x3000503124491421a4400e1500102040c2540d0030701c0c0402a06a20024090307600c112891a82c40a4004001101c540441500801a560034400d140501003510b21408000c170185605410040e02038450170103400b156000c03c0c007201c1941c600307401ca96101d03c0713410040e40082003089810304000002000f540181d000d141220050031042040105040c418000e244198001742030b01e1000310701074100c030003010b0440744864258509120a245500b9402c9503c4401688050010411008060740c070540040058000c0d0021001c2c0f2000030780591b444a822000705a45c4811130700030b0102c241c2c003088031100e001b01d0a00155a490901090702d034081d69078614040c2d8103200c4600806501285540c44c8140a80110b4403400190700640764142c0410613001030080070800d1400003250184030314060b1513400c0361000d03a54106880014803000c000c00c03002c1503502202c02d200c3e003101c8104803011801d4991401c03e041030603026850740a40030342d40c070810a1102c00b0601104001c0107401510b002030081d074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 829294190 1250 829292940 829292977
    0x507210201140109093c0507170a080a0f0908010f1406010f020a0609081c050a110405030a12031b050306120105070c030323150307050103060b09190812 67
    0x40e4a1080350310f001d400400701c20402c4101c01b00131000050740d06500600070340d0800c07040300b80c0200080c81d203010001164640c20845045c85400411008902d0842d4600000c2c066100c080d031f00c0d0356151040804000600490050914000344548881e10240168100078071260180416600c00781007000c0711070110788080c4000031459440380c0008680341c09107600a0407010802d4985100411101005035210041002141b0040314207848181c0c024030541c000150628150b56090111101c2c40d9009441800c00c001c1009982c0c3d0000d00140c40c0380e0004a02a07152402100a5001f000c1c441d07522520280f076840ca060146410030041d5224400c25203080c084901c81c00e82041c00c0700d4040f00d8490200302c0303400108000c82e210380d022041c000d4034441340d8a481c2d5171011a0a00000b01100c4064842034000742441c9181414880000104000c0c00d0901c011402c00b40d0104031409103800c1c86015425001c9013040c40d1001d4845a40181018000d65400c00c1d0f88056049041d4401c000e121030144540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 829295440 1250 829294190 829294199
    0x120f2411030618061513032603010e061f0c0b01050603072307050a152406050c010204051f080c1611030f01050c09040605030a020d0305072102011401 66
    0x1882200e100b01001003004031640c40180c0407007070f440c2c0040c10880d0040c18500700b0009060031030005118440002e10040102c0d0300c0d624104608480c00031881040d5141107410b0010440403400341ea044d2041e460b0550981d507074060214415600c108202d0088404001c4140c0100c2c1e0000030b11010300e1300441d010002681c1758000e0023500d101c00c0c0c940400050034104100045820900842d803143d0814119914112154507a10310300103c0101c10340d100e01e610b0445009020030351260b2070702e161565070710b03408504c0f40503003650340a200e521425052180c0054001407168082d4112000f810006000b44941581a0940c10a9508501500c0003044101003c0b50741e43c0c07440c1080c1d42100400051135002d071817042e900e20120038100d038045609486002801d152085082c06110b1040c810354010a1316914114204030665880e030380101e000350060007c640c00b680742d02440c81c5040c4d405051082d5210303a40e18110101c01c110500c003100405080c500030128039419040b000b030012034080000d107240d1703d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 829296690 1250 829295440 829295471
    0x100b070b060405060307120b0709152f01021b010b0a081902012d260a05100e0106020d03050708060f150408030c011e06030804120f24 59
    0x604401422404100000914038500340d002142c0c031900280940e11a00d03602d401995080090300d6080740c1c03044881c41000701141e48518088020103142000c04104420960050441c4040446441d00075200140300640e440c40c15030021070301c41c1603000031580c030261603550302100800312860340655420200040d50303900e003070180001a103001c0c40c003501000d8140d1201d070001054a20f0100d042c440b01101039406c8540c1c2220750081200d0f000410a58403014a1008200300c59006000f0181c00b40c11711842842a4500b40c0150701c440c610320000740ca5111648010505096035104010f1081004000f00b040f540c08940b4150010385903c05108540342c03401d050354124000ca84c40d1350010303425449600c072071074680c508080c01c9290288840c5890307240c1c40b13001d04607404001580715a0b91242c881d00d8054200101d061072180c0380300b030200000d03411070703981c0d610301d1082d8403900c402c0c404110008414410b1605528003015032083c030b00040c2051410040b55036084500c81588050b1900c502c4031421200e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 829297940 1250 829296690 829296697
    0x1060809070603020901021005090105090f031903090f0501020a020a030905100e060714011107031202030c0f25060e100908090120030a0c0c0603150504090227100b 72
    0x3006005040181e042450071002504504d43c03540c114030480220801400881c8221030168070070300d002181038503290750322518003040d0f41c0c4280f03c50341c01000303a40c0c940c408039000d080b0107000c1317880c3c0469158182c0c107014030800016080513205520000e15810115000140f801c0b610780719455282c0c455039250100107480d06681120404038540115280b21441c2c00e20040403103a100b000d40d02c3c1c1d1882091800d1b0300f150a0f6860001d04440b001039602c06140d080f00e0300b08911400f4500c103601c0c628000b40d2151070780c0100042d00750b08032404111340000c00107594803241c00c60031540e0451241c185c50b0a2040141482c5441ca81c0c0d14047d0b091b00032284000381c09a8507807241c0000a591401003200011620485080c4000b0204003103000500d0211400740002c02070040507030740d1180000030070f04080d65000030340e50025060510307000e41404d4002521600c2c1040365030460700059184d4803800482d130002508150110175080c0b000f05218100c03806149e15010750081b103000c0200c03548500282d0010311 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 829299190 1250 829297940 829297951
    0x40e2a0f07080906120109061703031e270c010e01020109240902030601030807060617060103080315100906030609140a0906091506050117071706010216120209010608 73
    0x30108007040c042020100101801500500140d01e011030f404050b0220300c0c8280c11403422151071b80f9040082540301d410221450822101a6240d414212040850301e5503500301702c1c0701a0961800501c505410305450400300c0320f40c0442c601b2a612038009079465082c1026424082001640781104651051082c9644d0703a51000c16513031511201d0303000c1c0c0c50f09000c017495405010f4680b0f00d01c0c4016201403003050f0085110702034040e00c0d80038500c0e00405448042e0080381007a883e070402c40c0640400001e1a80c1140c3c0c00ca14a0f81d9651660404007040d900c0c04400c0c80e03081201d4080c04540e181c2d1012014040b511695010008941ca400c460380566030404d0000001d541482d003c01ca0540f10f60744504017482c80303014002003080443e5185c00c6104102c03c030800840c0c0d0746041c100a2940c2002520207488078013500e0491504e03000c8005003025608003500c1c0141d01807140054aa64000c008441d014440c014000c05d0040e5034080d030401c40600468100d010702032a00001660b14081c07445907002d034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 829300440 1250 829299190 829299217
    0xa0915051f0819080d0915050c07030207062616031118060d0e06040311060903091309020103060506030112050c0f01051209010b0a030803040605090604020f010f0203040e2a 76
    0x605032502000c84008541e0703c2624084020421144466880c0c841c11501501c141400da401c410498031080c01c43c2d10048c40c1d00e01c402020071007400000d5011400005035011410318580030084c40361816910a8800c5110390a0001c20003405840f680c54903020444100b01e603020310000300b6200f101015400b0315816104540c1c048184400c2c0b51801d540034002c40f206811000a94429200140340381c143c0c151010381c003294810444015001052046c00e501c285280015460301445201207404810b020204c0243c0565500c0760108581c42500b1820090070000d12407512940c5500b1880050380503807500f1502c0e4400c0c01004146400c1c813054600c09554140c5400f4100032940c2884054030200910424280d5a11038104800750388030b4075076001440c010026140c0381d103460300e402c50865001a201108580c482c80400c00143d0b11460007443e00082031910411a921402040c0e20b1400382d03401c06269010302e00200508814445450112140c0c071001c2004200243e151091842c4a1003441e100706 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 829301690 1250 829300440 829300453
    0xe01060e0910150c060f150f0f05100309050f060103060b041a10030e100e0309101b021017090325031403060f0409140d030b030a0b0a0915051f08 64
    0x35004113025400e21703010705800b081c01e0103800243d0703084544220f04800080701d40c100c2440b0020702044c001001e00f0700462403000c140e041500085200e0307043c2031b48108040d12004981c003005028440342076805505003c580399544c6030325100c405808401c04039801140f030100b9140260480d101312503401d10011f0701c0b5804560300e41004074090100321010b41d07024400c82000c000303861414480c20481c1c1100070081e60f10303500c0c4c030401c2098482031601c1e8141040480d007000310742202d011803100120359046071303007110713559560780c3c29907c4041100964115068070010001051400300007002c0d5194500032800580c1001c12007000d101000100c0940020500740382e41c071b0446825001035401c590000d1030284003002c0352001a05844243c401151501c0c2c030b80c1c214204880d000c000d81801901c0c6401e050000b6000000443d507601c00c0048041c01c07400b03030780c0e002c02e80300c440700d5200309081f5030042c0000803200202500440544401e903902c184403900018403102d8002c48441820a640000e00503060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 829302940 1250 829301690 829301729
    0x804020d0206070f0b010f0608070e130605060f13080f060411030106051203070b0105041a0103020706060b04030c06120513030e120706200a0503040302090703060e01060e0910 77
    0x60048011800302d030492820008180410a6903000c2d0108922500c104440c1e581806201200d140740b42d0310900a0040c56001d0084498010b0141d03001c842066910009010940301ca01c4042d0045602c442d41020300014150f1508169000030144c01054492999075540c0d104515956900e1504813040590801c90101d000210000b44c0506507210050000c9000d50301c1d800000e070000780c0000c4824a44d400090b501e81082080454180101021a000c004446440c50119041c02e2a051314030304140d0300145000401c240d59114102802c0c8120b80151659140d180003400c2c492140241800b1900242e00c03005441d100380100ca105001c170229840c41c20000d42d801f0760b0f003d18200c0480317a01500d061032000880d00c003080003900801a0b5038400500341903040703040340c110b0380e101c0180d012600500c0c00b690100e01c0000890381200e506a13075a00b055960154210002c00c90380d08606180f030100e0000050040c3d0240382100d0507003084031400c069072100e410300c0000f80102e01c101c001254983e0380006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 829304190 1250 829302940 829302949
    0x80c03010e1c21020406030c0f02060708070309140106120507140117070e0d0503190c021509190303030c030605010e0d060c1101290909060c07060b030a03020a020f0a06080402 77
    0x781c3d02114000d1421a40391408001a43c100ba045440040c2d55074501d402c445610180c071540d00305603400580690304001100500001000704050181a207980124080005142d85c110a401003d40200b154507107aa60110f2000400710342910b240c455020f0105002d48240903044141505859407050200034110351000160010054018010030517001c2809842c0c2e01034940460340f080028568032042c0052502001840400383d0042103070950540e0010b0b04c50042c42ca983c0818802c00c41d0b2a02c00d02c07000a2494680d11b0071030906285030440c00810075030035411030200307001e01d91410711800761280d00448210600c5411141d02c00c40c900b40b070f0703400704006070b010b036012080130b00c1c0c442c1003580084009820b45442c0d44809000e5045200c084000c0c0042d0b4042c44c120100490710701d521ba08154880558a4801030000400820300045a1040008a5003c95889440502a80c03c40c114905020307490b80e42c07444080e4080c200c03521205500f40f90004041080d503100d0b4840400c40d0319aa020301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 829305440 1250 829304190 829304207
    0x30c030301120f050d0806150405010c020909071203051305061815131d0609040201050d0c050417011a1014300a0c03090f0f020316080c03010e1c 64
    0x590300f0300c05011405010403003d1008200d241c5d100c0c1c58100d0716081070302c2400425969101c88040c0c040050005029680c0d00400308000580c040340d81000b56202c42c1012401c01d0200c0c0d10a005107244900d111080503081009004440b4100071060301803591041031050511400e998442603080e21a0040071500e0400014941000b1149500741001d1001c41084c2e4111001d401203850750b4041410002c01910000b082540820301b55048202d90408ea40007800b24000c0f0456101500e864100c941c114605c01d0007a81d00400507010504800340c900d9480700d000b442100c1c41803080144410104269080a641720b0300e090f0b604d40e079012131821810301020b9494100c125000c1c4011200321071582c0e0140d4150103102031b50281001e5903920704083d00301504550641c50030600385400d0011042c003040e840118040082d4001203000507910181c40001d0400e52844210000501004004180d00800060280c0d26207400c1d802003100540100103c6e81d00c19036048000051401a400b900f0128440c854a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 829306690 1250 829305440 829305443
    0x504060f09051903021219080a171006030c021c051804020a0f0f2615040c0306050307090207050309042c0d03050c0903070605030c120f1602030c03030112 68
    0x7a500c038035152400654640c01040c000400005109400d0040d0b140800c3d9841b84562280014800804d0a210345003150007003031400b814003100031501c0f9881600900c41d41c4c1100e06c00310700344a210300e040d086108142c03020b400340c040000d2a004410000b0b030b000140440c880c5140403100f0301417481024041f90160700c00c4081c500380200350141021103480d0303400030f4241c5040e95201e10910440446000b030100e104003140800b0804500514581203041d0201d40940ca0a15228200559505520450480141c600c030035080303803400806c07a42850385640188203940c0201d05480e01c81d80c0c0d6503d560180d0103841e00c0905640c104200300001454251321002418041021408411402e003056585c082101c0404c80f900c1d0304042300c1c01860552510400364003000740007001c1d00305031207500840e545200a00401d410703c81c000010941000c00303039040e10812500004099036510785091039a003ca04c0549a00580c0c00612000400c15400030042e94030301d428a42c011402c40e0302c2d101d50704091795403a520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 829307940 1250 829306690 829306697
    0x8161406031e150a080105010312020712060213030812061f020601050f0f151e04030308061005040915051302070f110a03140d11010506180415050405060a06090c0504060f 75
    0x102c40c140390304c6041a1100070f0030010000a202e43c9942001c001c4900741010a00031508031000600a0040d07421362008041d8108100685a082a0344551071461240d00301925076600410701080c0794200c1d200c400d125002c1914442c140c0603608404082100d2031255a40c05a0032610040c0840d051880fa88010740310000d1081400d00341c5107012510004101101d5203841e4400110071141c14404070300300142441250302c451030140345450041003e14085c12591103002c0c0c411003803009a114200f69000381c09403d20030061a9203148607000031034210320502d80204104414181e14014901c2a100030039040395000350040380d103aa60320001c0c210300399842ea00003100ea90210100313003e014100413a4045000922a060700c8502c040c001030910303043e050700c5a0400b010001940c031107484240b030000c0c140c043c3d0b54298a952408502c0c1072004101107002070320300b00c01c00040c0980095110b00900a1030000c1200303e4580c040c40d002c0c3c948a05507200414000c10003007144610890090440410616 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 829309190 1250 829307940 829307971
    0x30106050f13051908010c0e010c120306030606060c02010215041a04061118120f0c10111504020a0b030c1207051b0609120301121b08161406031e 64
    0x1d0000d0112052041e24101e007004c110302c2482a28002d100740382c1f11902d01e081003018840d907400002d21540045800600350710300c0c1888040e803640a904003e016542c400014442c032510f520700241880c507008416070062082c0740401110308800c86c14070b4010350300100f09420034400e0f249280350203030001e801100e2003966151000d0181300802c01404a0b840402c009980d09072844042004402500d01c1c02c0486030000e10210583c0c2c0400540f5481c1ca040666042130ba10700b600c001668810f0700090358801c240030740c000343c0c2120500c0ca68070070710441c0f00319282140c46441c0c1c1c844500c00c0c0000c640800c0785460070461313a02d180740401045036000001d4908103203000752402c05084241e81d0004901619030020040c851383d10800e01141c4160b000d504a288c0c110344c50094a02964600e40d80c3c0a0282d0900500104040310342444140140050a00b26240c0c0741c0b500086060000807440b072400340048100d9a01c24a140c4981280d005a000c12081500010040306204840201a255940314800311 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 829310440 1250 829309190 829309199
    0x30309040917040807230f01030509070f0e070219050d0c0c051801030b07030e0a022e0f030b01030207050a02090c091206040507080a080319060e15030d05030106050f13 74
    0xb0000e002425072403016200040c601180c0780a00002c08000c842d0003d030704514624185ca8284c420003220741d00746404122511900c05807400c01c280c2d60003081c00e0750032881b00803ca09101c0c20030240585090760840d511048841308522100480c002d004049410200c0d0203030441e44101e501e00744035405000c4c2204195658000140d80c94102185409009092030040050005221f2400e03070000c0d0500342805450442421345484200c60b0708003d208a000c034003806c100c0d01c148a00045090140c40342924940c80d0200c020b09002005001900001e040000025440d4840e0081d00c1c0d4141d8420002d00101d500c6500700010300328001e00440117042e0078024101966107540072170b45100201c50240c0703030f18145420542c1c10246a90412141644003d008030000341020049a50001081640009045401403041b020780a039034007086008684000344210301591660041880300101d08a5451070110f10080d101c80c0024403407079000c40c0c0180071003096112170000800c031000010009001007a00d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 829311690 1250 829310440 829310483
    0xb090618031e0412060e011a030d050721110610030c14030a06051003030e400504080d1b05040501140705010903200a02060901050c0c100f09050405060303090409 71
    0x468600717664503038580c01d89040b03401080c0310b00240c20505000b101da025910102103a034401c1420411020000001420001c0c400c0109150780b0300040d00d6038841452004050040000001024409041c014003000c00d0000b00c610f05043d007160303800440c1d0b20429180513800091107003821245a010b016154001c4001807407032185922594911101c0c81d031183c190f080040c083e9807000e56190041d0200f00c545c201484c00b103540743c0302ca80c00a10b00b0501d6000c0040e02c010b420403200842c00c141310f0801042c402084051406410b04140000d001c102c0c3c0c00a28402242c0c840d032411038100862420032060000354401e80c0922007034109120b10502d0070016a49960865400b0403098002404640b03924809410b1307005a011401403050041c04005090f0300050135034450300900314184100042c40358800c4105018205483c00c0003041c1c05060888024083d042442d440143d00c00a07207142d0001ca11864203204050203018040c00a40c1056180024400280040070b02aa002451107600703019a010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 829312940 1250 829311690 829311719
    0x14131a100e0408070507060530010927030305150d02090714041e1409040305040b07171c0b0d050705060a020c030703060b091e0402130209030a0b090618031e04 70
    0x7079664806039103584621000510207000440327108030340c8040100503001500707810507505441003400c000400300e02040c0d09400c841d41c03814040c4c031001e40c914103190925406070301480c45004240c0c06030740901e080e0b408000041c0300f48400250f0102078400401c0000b407142000c00644010440c2503880c00d031702d4100160001c049610030701081d2000043c280405401d0501d40d002c0703910240e80c0a496400d050760013402a0050b4000c0325102c03200417442c40140414a8607000c5003121a241703241c0d4541c0490001400f83d550420280420790410144400508043c211010300303e4201000d840010304020421440d940800c0d20300382103200d0005581400c1c0c0e401d002e41d40043d881450005214021755041c042900e1004000f0340c07684042000ca00d00e160140500c3c161702543c1140d08595891001c020b0200900a00140e103405100e616582030400040300341c03190080c01d0b04812519a0740d20f05028210741d5800745500362031604188008075000400b80f00f00c1030041204403056003880c3c1ca40000050101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 829314190 1250 829312940 829312949
    0x1f11070f0c060212120705070c080a021801060e060315041806110301060507030f0c320304050d0f05010605030610090e07060504120614131a100e0408070507 69
    0xc0c900049081006a0700307000400815190000d00030305280110103120500500c000c940d044260300d000504568420002c403646a03a100d18804109625800410ba0303d98081e44100d024044100303500081d04c0d0441d0060f070485185a6440400800c0e440500105410280c0701d5843e9034840000042d00e560307640901d0050000031023104000d840d50303050603015035401003800c00711990208014000164060210f841280d0182050000d2a008820440e192100c2e100d02a24559014031032104000400482d0340c000c0300c02c18000804140d030345444036180c1c070403403180d07960040030ba8034400009028000c162003c2d500600c0002043c41d510b00100307081540c1151b00746040c44480c030090140316803038031510802c4240c403070050401d903003401005040d51145006090f5125520404030007041000e8020b0000190120b10f000100e060400144400000d061002c90746801124200d01c2c11000c0340181500c19280c1103000d0782114a04059041103050260090354942c2c02044101e011039410000f050091 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 829315440 1250 829314190 829314203
    0x402070507060f1e17060102030d11030117060c040501030e0312041a01091e0f1104030c1d04111905060a110d0c0503040b1b0f150106090302031f1107 66
    0x103600c0303500041000340d05444442806101c004d94031480e590000d1480c20543c804800440300d911000c006074914024490000c44441c10b141d40c81601161810203541220007003015901000e40d0546115156407046809104070741c0244810030156200350441c00480c903130401078a2400c403601e0a003650261045030140e6501400c10400b100c031802d800c00c124010f10401030104110600742c80d5000d02e02110050901085450718010000c0014542c841c2031002c442c40300d031641e00c598926003075044c0c11181c070401d040342d0640202c0e202444004011a4840c0d07900041600c5400090010480d40100c000001001d00551010108481d22000d0080000b42110340310841040c5031110f403113240811500c204001c00c180d4506c000300050000040d14103582c400c3d82e206d80c466600c50070b282202d4512403d00941c52059045400f8400720114095105220842030520142e8940205941c02203607440000c0d05a4056039065a00d8800b040c901da0340e2a400810124500aa012a02e50346400c81e04060b00c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 829316546 1106 829315440 829315457
    0x2091e03070f03230102040821040b160506060402090d020f1c0305030708060d1a061306152007032013020d050901060312030b040207050706 62
    0x680b00801c11a10314036580d003003c042007001140e210a03004104880c4240f582e106008980540d03075030500401c041e1041004200f10404000c0d1240f00c000c00038800414805180802046500c84800c900104041c403400c1050504401820361480b6600c1000244003d03180d090801031207940445925861030780b0500402c1e4042c4181070030768001250b1084210030140c002001e0341c0101c00e942d81e2a07109a540c2c20a11403e02c000036009021990380b884010344400c2485801d80d40078401404100c00141d6407840c0382d00759590340e00100c414004c891600e901e03050380481d8038003980d515924084000c08014040c580c40d42c1403400040c0c0303000f881007405040f07440340e5140c407000704030060600f4a070031600030070b81350003034011544d407450441c10000410701590050180d64181c82c3c00100e0844030b0008128254018074515002d40e0f0840c4c3c003881503001003a8107110081c010b040c00c0c1c80310b405 = true := by decide +kernel

theorem cover : BRFrame.Cov 829136690 829316546 := by
  have h0 := BRFrame.cov_init 829136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 829136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 829136690 ≤ n) (h2 : n < 829316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
