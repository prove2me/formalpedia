-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2132
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:28.782892+00:00
-- url     : https://prove2.me/submissions/be3aa996-371f-425b-b772-4713673f000f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 383273381 ≤ n < 383453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 383274631 1250 383273381 383273389
    0x5100c0f110114040e130c0b070f05060601030e1e030717031906140d08040f120507120305040303180509070c03090b130504020c100e0d020f0309060406030b0d02 71
    0x200d0a6001c0c1200d14031400300c01d000108104243c0011016042040c40284030a0704000704003503100f150f0700360800c1961041c1c00e003030001169540c0903154020000030f0340d208005a4002940f40c0030301c44c1e02252840d0721524015001e03104801c0e140c2c9085d40c005941c140f0000b1007803841d454030000c4a41524076007a140d4803401300448401e112014031503800820b0111341760070800401b9480e070002c0c20400c402400c28240d814018a00e03241e103440384140c61641018440c07204100c03001440600320307400c07107940d07a02c0307801186000404094544c1e000e00340001442c441380710074048010381e255171440e2070603046590945114044249294a0074046032020aa036141c8400141c01824941c861034050b5801d0714005100c1c818a1f00004030218007408102110400c80c003560082d40c804840240c1c507804d80c8000589080307110818000c070700b428500e40b051191008607041089200d681d00341c81c0010a1126074a0b52403080c006280c2c0c12040411040049500c00d030302405164000030208425060690009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 383275881 1250 383274631 383274653
    0x60318060106021f090314091315030b06030102040806010513090501050f0f1005031e0c0307060806130606020303240d0305030108010c1d1c200a05010302030603060105100c 76
    0x1041c00f41c2c0c001c800e030445044542c40c1081402505000602c11034010781e8004090703404e605078201c0307184404112400c481d03031800200442c07101e40c1c010400a0b034004c00c100d4800d89000d8802910301581640110742a0b04041c02241c05035601d42d0010041030b46410240546081803641c0c41114aa44040f40c0000420a0051900412100d001d0702c50074102000c10048444000c0c0c122644030640700800c01141d03e010484810340c10b0003d1203400041ca800c100c0310709052a24010341e44c540101440441d00e150420710b034500856059030760448250079000c06d501240d000e0300840d005a0300c18000221900f030380009002107034224041c0394040e040440d0105244011202048020074030110040c0090321092140c20005030380b526000c2d40144100c1c040000e42a00b004805005549449041d0f00304100d1102040103d0390000200e06a12400c4030103a4480198140c064442d00341014001119032080c002c3c2da0180c08004e000e007401ea441d18040080d0701d01451104020702c2a050352510100e000c410706 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 383277131 1250 383275881 383275889
    0x9060a0e0604170a12020312010b0904141f080604050307170c010c0e0108060a03080412051207030908070605041d1b0a0201090b01081c0e0a0f060c020405010504020f07020603180601 80
    0x1005000130610784000240c055898403011075201b0b0109405500641118504543c400f030381056803406c1392400f10b070203864000d511011041e040010f0020740300385072410341c1c2c50182c10205903400d40d460f9500503454403010344000e8030300e500501c0302d0408620200b0209000302607043c10517241c1000e22494070b0959101c410181c0124a00303c00c2458256004100a42e00080c01c46404001c41c0c11959002081c1c0114010113030602002c6011000b00141001070020401c4460140c0752207803d1440c2c01056480c590085201038003c203400000c40b40c0c06502550700303458040c0b0851405c2441d224035002e0488009040045415448908501827a01c0368000c4c00c01d20600d500118031401c0509119a0510046c0e008198580c48120143c019264001940c29801c2ca180751810030030b190000040d00c080c1c81ea40010f001c40d110500b0010f110b980ac020341c2d05880d4400d07207042c403403680e845081104034001d21b00861000682006207000524054004540c0042e01400d105141041c10340550324240b400d0300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 383278381 1250 383277131 383277133
    0x1107051e04060806010807030803132117010b030c1305150711120a1e05030d051806010302100c050307320a1101030c0e0d0308100503010209060a0e060417 68
    0x200030303001070a10780502c60180c80c07464014096945004001030380c485803440301920300b0a000c004180c421020101e0084550f4111000000c5060100c13a2640031726151094880400c00c80c2054202514104403c94126500754240d64119942e50b90200d145a00050050912081c6084c02283c1a6105948110004140d000240e00c1d482d15103403401500c001000100e12401003060b104c00805c0000606c03020203a400b503a030b50a02240107142c9501100fa41c100148940400300d1504103082c0c959003c10300c550080709150022039031404a6540744c18003800083d410444c0c01a4030b04036940a0f03100da106491150007201e184c80200c0c0c071241020301417006003458210030824170b184012140503a90031481c2c1c0746030141210000c00d50342c01c2c001d5003c008141d410b050720740310f014440f14000c2c80c50b00d2114101401c003003001c50705c0d864000c00801044543e114030000b600c001182c03900741403094584a05024014514100840109031002d1f03414404259009804100201c1c0310804c040980b028820240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 383279631 1250 383278381 383278429
    0x13200903390301060e04031103070501060902030f13020d03030e2d010c0207060806092206050601090f030510020903010603080c03030604060905091c020c030109051c1e110705 77
    0x460710040c2080d540c400502c00d82c1000c000784080200d0a07096500036500d803c1428000e82103464840c107600400001400030752034407100180a00f5150020f40c03245e250b409400240341e80e980c022030046400e40740042d41241100d10710b0b0000074004d5000c0c05003041d106d4101c6111011804440050010714942228a000c40c190798004440007409503040c40c014500141030214101140141100e400400b007078410707000c0c0004510103200303100390b204003940c2c07452900d404040c003401c2c07036030103820252510307800501300b80000206042d03517120010a0740d40c4040580a208001e04820f0082d400c90b50f5459815541c034080000058200801405032103500c4028640303134a000810401140d4140c0d110f005c0c2c040c100383c00c00401a001080d212050300b481300440c0c0b0074a0740003070205c2c030701070a00d2040c0f0f805601c8d15156030240700002510406055528419040318288a0304c00c41d885d58561a0916109000040c0d40341410700680302070840042050890b00002d5484000613070f024aa10b04145a00a01c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 383280881 1250 383279631 383279713
    0xe0a0203010f0203010e070c0204020d06090b130539030906090f0307080403031b081c05130f031d130b03010c1e050a0c02091513200903 60
    0xa015490000c46400b20440c1150314207031440c01c07810002080c880070402140361540131580c8a90690fa000c20815104001300380d15001d400d002001d0341c464081c8107990402041d451300205020f00d0344034885078006040804020788020102100110b5200c00324030b00d0f95012114001e03108003840c17091207420000c1c00e1504056803041d090586a223001207041e0020009840440d156104407800c6039894a071010b5200c1e0091072080c10f40809010040c58a9000203800410680381040c000048842c2081004a601e451034840144001010002c1003041140d06440109006001031045c44122912904600360701100140c5828840c030f901d4059642d540c46601c0c200c0c1400d1154949090143c10305c806c0d1100d0604140d01c803841040d0700001040360004100014520458840c1800b03a070140035805182005d139001c030b03031031801038003014040e1400f0060f100c00700c641401110401040350711221081c0d00404490f06d55507000d55460307030301881000c1c0c2c00c0c1c8c2c452080d54642c2e501c414107003010300c9090b081d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 383282131 1250 383280881 383280883
    0x1b0303160909060806071d1302090102010c0503041502091216090c0e151305030703050d0212040b030a0203070c0b040605070f020a0305040b09032503030e0631090e0a0203 75
    0x81e540082410915104081c0040800000c20a4000c1c8007030804002c466001009a1030074202d9100320394203c0091408200c030307101260003600c03c14000f40c009100510040704119010300046401405440443c00140112036075540207040e130200c0901040380390151200010300e00800d40700c490f0035144411008100d600201d10543d68006080e10b484601032400381d0000e038502c900b0200c45c5048010000c1c924003002c492101910042c500641901c0680d507807414141c2d1030742c0c0f501c1856005402410440c0ba56120400119026103501085042c29074071032054601c029003000b00003105000ca00340040c80800d9040445500c0f85d072190801080c40d140a035070062a0003030000d15001598000c080e5500081d801405031419110301d004030944031015034000a03c0c05c841105801e070b40c15411038071403603e440303142920740a40340251030b07088440c1803070400d101c000c1c403510100003400007000040c0a44040001071000d007000700c2030030002000d41c43da24a2403c076102041c070494140e11442c2c41c0310071810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 383283381 1250 383282131 383282147
    0x150e150f0c041202040506030115090e100c0c0308040c12080702030c1e12030d02040b0409050106051309020306010c060c050c0c121507090312050405040b12030406051b030316 77
    0x240000703101d0401e4504000c2c140402810b0100038441c0e619800010a141c40035400202e48980901c0c0320100e01d95902408c200400040f200c0c248140200036040120480c640100b02c40514503981e0f4860030f089944080342d40300360107081258001c0c8454000290301c102c45420000c1c25000328200c85d85c8001d1841010b1510340c00c1c4074414014015501b1700a001030a0a161000781e07017040e9020f00000698007542800d44c0315042e00c0d88007140c40450007184030340b4545c0281007500c0e41e901c0c0411890b41c07500825a0300b401008140905014940028003103270503aa00a590400018100050754030070359a10401a140d00c80500c1300000d902181895171030500308000d004003d010380c1d0718001c88852100c010b46881220100808080c170400200d00c1b114442d042d160021604120750113a07a00400c0002402c582c02840b8147c452400c2c004143c815281c07081c5182030700104030006600d4645400c8017910356401007107011861400301d01c0040b58000c1c050000754800c0c8042a01c01c28104a07449000e01550 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 383284631 1250 383283381 383283391
    0x19020d0c0f030c030b2d10030204060f091212030b030f0c0109050f03031801050f030f070f112e02040b07140303150f210a020301051e04150e150f 64
    0x500700307420541c00c4d4484100c4030036201440218040d202c002c2c41c10010481000084294109100545003500070340d01d50b001d003040da0510b6640701c228031213100c401c031903180f4039004109040ec0001c800030005000c1c855404149010b13400d0104e00c1d290404002400c04140a0000d0035903000350641010a43e0f00040b281e0252108407040f85d080b10061020943e40c2c0036011305c5100d0103030707000001c409582c0544250703404410b204002c140c0c2c9141c81e00880790302860030344103403001c20440800320382e030b280c0a8448684000303007242c002d0134810740036824611440c1400c800782413001e440e070503142c4002e5010700003031000d049600c0701d0039a260401c2c5066024070100c1000e0003a0758200b80103000c1c41071008409a540000d086890090050010002403010310403090140421540b80580840408021030340e80ea00a008600801580e510860014451219940380c0c09460307646c14001400103120900c0303c2250181c40c1030024950307420006480c901400002c5006203140494100704000c0409540750383c0c08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 383285881 1250 383284631 383284637
    0x1170f0c0f012114180309090432010f0b0105090f010908011d10020406050f03060a0e13060b010807090b0f040f0b04240e0402030603150c090103051e19020d0c0f030c 73
    0x303020f5605e039482c0c60b4000e464000b032007103000e440824103100c1d2116401155a41c41c026264810009001c00c0702d1030144903490968550810340c0c24050b0f40d0182c800c0220455060f11454a04405c0314104100004400e40c0d490501c64200d10102d400c504c00d20440d6010450741d441c41c4404014a540d940c500001d03c810035031400c2c01000b00780318503607100c41a6456460b004a1164503030326080006103c04038a5042015580c4480f8100546100e14001c2040800c0c0515010060711116000459940c170044030507001141d0700490030410709a0003070091000c0c1f505015100c0c1040e8036900c1c803403d041616442284001408501031100741d8151049090307849500d24071941c044070050010f4064241e80540f503100e554007000103039240e1000d200070700c45a4052a1090b03401e162039402030b440c903000b1003640da00107880c140c0000c000035912100b401e22899406400410351340e83c030b0911403084d071203800611007481c1c0910070103181001c0c038002e0401c0e410040d11420f4030900744e000f005003214500603402c010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 383287131 1250 383285881 383285911
    0x30705090601090b0a021002070b0109050a09120f02160611060c03091203040302190c1806230d120e0108070302090907030209060c0a080301170f0c0f012114 69
    0x8079070f810103004400c84d840d03002c0c1c1580701c80c103010050781024080320025895070f00014141040102c6c1c1d00311203060361103a030b004000700c1d200d6a250400b02c83ca40c0c07a004207808001205602c1060141e452181028011310403603015024162603030b42c21103020382c0000003080f03134050809a0440c050090942c01030b090541740d819450804c0401e0342e0f50381c0401c500000841e00001040501d882032000025602d5403140d640440c0e0258132b48420702e40c42c40d2080c1c0321522207a101040c1c56106d54003d07082102e4034649180003296810010443d0811001d40665012188004420000b81707107041c900c0b861385007510350842c5414038000260030044010014800c151040110384583d07a9482d56258101d003a42c5801610741c11101d0105441d4800c100c907850207449101205420441408015410707a10b000c00f50400100d0540f25180e581c820f82284246076420030200c0d86001c4c02d0441806685520514090110140c20140071040703a00c54681b070140f91380c90b0080c200d001d6904108558000e6501c0c1c0d02c26036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 383288381 1250 383287131 383287141
    0x210702100c110d11060a0206071803080711010c02100f030f02040806041103030417010b040c0207060c150207020a0e09010b0906010f0302030a060503120409180804030807020a0b0309070503070509 86
    0x202c00091a103140f403040d0400d024503820f100e0ba0526544602002a1102e652018031080c085d5035110201d41360030004502294181913509032842910490794000045801d005050756040f0b0784400c2c1141c69030401a0b41c100340d00250b601e1944004410400ba2501e00301d150400500a05540c041e0314104c03059401000200407810001030f040c0c0d0300607080400000042070703000009080d4400d6a000068044100c0c4500710180d1041d8020341d0681da0844d0100261907000d5803d03138454109228240104104441001c04940801c0c00e180300c04c0035842005240442c0e980c00074001c01860382181c020040100308200121009100300010308a0449000f2650700d00440000d19401004d0f11000806402201240e420703801078002d4400741400400740e51503128501e9840110350000d2140d03030744c25810b250b100d022080304102c1545d60160071a2405181c907046403554545903008541c201d802c20312500b4000380c51080c00d030245000720004005441d0180c83c16041504d800142e0300803174401d01c08441445 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 383289631 1250 383288381 383288393
    0x602150c0405011b060e160504060f06050304030e0405150117040c050d060609090f021509060405040b060712030617010218091f03030207060305010e070f0809210702100c 75
    0x404442c000d20f04100c05840d0aa481d14491040000043c1000d05003441c00b0101800415030884441c00314003554a22941d1b441000700355000c41c414240a68201c4100b4094648070350b00550b88070340a410031003100c1d04000040b500b00d400868000038140310407008078881e5a8412401754902c038140a85140c141010381382c0709000c4001e403158030301c545004580c4600f00021600000018800e0f44010400c1107080e0809007a1503840540482c800c0d00500d079000703584111207003a2543d03494080c000c141014248424440240890704a03180e01801c24800c8100184048a48404d10041550080b8169142107030400002c0b441c078541c800681d00501078184188401c0214bc0910a01110310559680756810b89056101505034409240c4030300c008080309054000922004541e900da508124982c1c0e0382010500e0928140c8151740010100601591030a1203580e845402c9030300c02e401e482e018040840000315445011040568820000c1414030551500c40030150208545041203e0b02d4006070380d0b14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 383290881 1250 383289631 383289637
    0x120f031a06030a0608060907051822020402220f0803070b0609130c060804050c0904121107171f09020d080f040b1b070b0a050703140f04030c0602150c 66
    0x14041c41000c0001141d0080e2a0008001000da0009803003441c00c0c190368054440e0340900505000e41140c3c484445c19504811405121301341291000c0706503604030ba03481c074070b80e0200c3d8020b0740d000d5020700000d00c9520124540c89100052001c407030614038a41394880d89044c2d2903900c540110340082c0a101c0200c0c00300c44805ea4400c904071182d101a41e510460b404110f41c2c12000074081e68801d03100820040e03000316078140614002e000701c60080c3c080b9010802c7c42e140031600100600702207000040f00034010007034403e171504403034213030781519440380e4143c1c00502d00d100703c0c00313220360003040c80c09841105400a00741703040b82c000d024070600e2001d40108041c5840807100900d400d100003603c0089078010030030f881c0038000c04035446940740f014001c041c0c61110000c0307007403c3c41d000317098001500303030040c90031180c0001003900e50328144951520250b80360130962004178803154082141500b40c0c01da03500107101541c03007002d11005140c1094002450b004080e684841d0f0010b4a006120110310003800b6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 383292131 1250 383290881 383290931
    0x1b0807080c0a11150c07061116021c050d021e010b012304031a0a051005100309030c02060301080d02060108061e04241a0102030f0304030e0a03050604120f03 69
    0x2202c848443c400c0035500d010340f10424071880340900014409009104001401001d0003640c041c0300da5010358034864010321941042c40000464085070200604102e045090f824115415050140c2015124981021801c44441c001a0840140c55030702c1101b186044840c451494004c0013200351200001e4002d5030314001040e80540903e2075442c040701d0342c0301100c2c065584012102000e20300140300461103003094980748074060402e40061102d51a0a410104640008181c0c0300030800b0b03881d0036001010154015002c015202c031900000d0b845440c0298000c2407620300070a040c1d800da000003401e20750180c1000020f900024180b205864503543e00c0b100000180c1d00d21901030b02d503032510300c484803550660050800340c050394092a00840d40c1c42504d04582003500c00010308041c2d80120780302e100d41142481c100c0c400b880410301180c4502c0c0c0d04e0324255070103480c07003820342c1d1207845403403901500b00c800300d40c03007001d01c7e4044606503406900c40c3c045030781c1c9040c180321549501d80c51401070024164 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 383293381 1250 383292131 383292137
    0x912071a100315050711150a0f060504020304050f0c0a1a180d0c051e06121305030c01020a0f05040e040605150604060e030c1f0507080d1b0807080c0a 66
    0x308041c40190594000215440011029812441030340c0303c0c06082d04540c540b000ca00520380700b01c0107100209a860480700d40c4030703480007a651400800401040754904030a00700d40e4a540c00300d0070352602e10065014030b0041c0001c0030843d100d00a414540034000e0119402401c20740c2e010040482404110540125482b00083d00c0b90890840111111041400b10340d00030803150326203050208401344030b01514805d0b076140c1900131201c034003a0081800300c9596034001008000c00c031010440c181300765803c41401114541d41d00840c1e00d406141da040031030034420503540014400d890315000341c0401c5035881181030403410503207801103c104014005102030542900c6000148009151403014080180020281e54035030f40c45840082000401c4032125009200300100040d0b00d1410000740202c550304400085800c860044080b07506800000085038503000c02c0c00078006110060081d5504100c1e0780c1c5100c520083c1d480c1c0c0040c002040078200c44144042001800a20510f01c0c0848580490b141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 383294631 1250 383293381 383293433
    0x5192d081b160303110601090c09090e010f1e0b010903120f0c02030607020109050c0f060714031c0507030b011106010515040f03050618010606020a0314071406091207 73
    0x460602e0601c10010b40b4441c0c01405100c011081581201d80b6044281c1e0f00400c07105d540c0e0300c40500301d04a0b12154101d5004c1100200100100c10744c940124140903008000490b145811000349016a0107961003460012890340b21980844464840c13140291400d1901100840c17071034450fa9401c2e00402032403003c000f1400d00d207101d030500800c16402242d40c003030100c0d9850301d0314660003070007442900000c5641c2d010f4581063302a00d808006a410454010522444e14444ea521102d500542c40416031b1a40000c0c450020391a42c2e4046c82414131600b040e020500e49481c0740300604465291052605005054210040090f00000c020341941c0c01139440020050001c884010301c0d0240b81d010122011003401c1c084100800400c00c94041d60002c0700e580090384144010a007a00c440d07025102c0141e1091109a000c2841000705016000101c0c02035850104039480b40d000c040d0540c3c02d00f4085611110600444403410028066660744084089080000c141e5801000d907a10801e0183c240d10a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 383295881 1250 383294631 383294677
    0x50f181c02030c0c010e030322080a1a0f101701020c011814030c030a0f030f1514040618050403021c090305060105040501060f030905192d08 62
    0x304410820203500404021600d8040c400081d540d50220f00528103500800c0d0b801d05413940200006005000e0040246007484680b11110354032071b0b030140400c031042070b004400003100502880202c0c140c03030045080d4101c0c1c01010241100c1040701a082078500034000c0100301d1000f845603003043c192184001006034165514200b58060b025080d680c00c550751070000c2c0800d811040d1300042902c9480380550000450390341c030350240c4a00070f4100c91001034008101c5d80b0b9031f030b034421806880e895001d4207002424008066007502110714854501040c001000010b10290107003030441094036104980c14070025003401d581214070384916540b044000d490b0000f090400d4000c0c030412a12904250a50040b885420303401071022084d0320040c0d4050050000112f42400c4c580140c03030590304640c4505140355210b1400704d000b00022107040d40c45001d02c0404103494851442c43c000032034010002ea1341c450000382148488007a42d071040403210b075091188480021032550a032008419000c20b450400042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 383297131 1250 383295881 383295883
    0x1a06031b0405042a0323090a0c1706090c0102030406120f020c03031b180d03170117160f181103010608040b0a060602061603090b0a05040213050f18 65
    0x1507a0002e40d032050030310080c50500d41c5200107410301d0041c0c1100e5840200310110050f012251808a041c0702c107088100c180520005241d181c0c2e07005015442140d180d0a40d13130304d44244001d032a4000c442000202d00881c84e19078030403c40b00750440c40b480b02400c811001500040d541e40b150340b24040602103e501c000c0da584286510060350720f617040b8002d40d92503d03640b0405489500403200f4494401540340c01c001424041029160066000c814501c2c8540c8803604200301c100e21004120708104600200003240445450034900030025400301008540d441781041d410442d01d040714003140200c0800c00c00c0310300040081c01040380c0e00d5203080c1c490200e24444c0000030f440014a5250218000400043c080c2c1d0700410542c40b450040c051141075854130003903070080e01d00921481c001070388000003180e040d25200c51203000030000c1e4140081e991a241d5107501c1140003c482da0078206a4817000c00007541007814040b002145101c1c4100400c0c504a90001d540c0e21000d4550303809581401454804100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 383298381 1250 383297131 383297137
    0xe010e010f0f090f0909030f050f16140a151a0d06020c070906030f030f08060a0b0d090606080f16061b1104020c01050106030b040c0806090402010203190804061a06031b 74
    0x10341351004042280c80c2c1c1d00c42005402e81400c01c40003d507903407007000e00c214800c0c400d8980021020414901e0101e00742903051600c0110003040d10202d1428010788035040080044608040c450800826440d4034041d1003401c813400c0320101c1206142c01c58801075036aa4004030220607a40c131000c01600c8120048100d4544142600b041082c00c1c50454040b05101012441c00030181c0700e0360f181c18a41030300e00003c40c2e424400703441d002c1c0c000d90500d109202103844c500181c1070113260958001081c403540e40781c2c1000c5e078140390300190142d04410075804034003c0070701140c964152142c0403521098078144004184844502909403103413100a09031040001c0380f41d003a469801c1c014029900c0c0c401e20380740940244028490300d03002c00e02d0034045103054200383c02881c1c0fa2141c42d41f0340c9120380d91413030144682e400c0c00600c101e0440c0010448598000040d00120304500016034035194030380b0f05441c1c548200d80582c600000b6a600d00804003000c0d54424080b20390012885408520300f481e244070300707035030b1340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 383299631 1250 383298381 383298389
    0x60801091523092b0e090a180804090608030a02030d0c0e0d0501050a06140616060b1011010b0a1202010c051c0c020307140603040803150a06050a0e010e010f0f09 71
    0x102a0603c110a200010b0084444130242225101c0300c0010124200490140c840000800c550400481c0d051402800c142c1c1d2000e10481c1c045040b10a02585e00c540f0038101004031490b160200b03052000c41c8992148c440a00441d0004516203004410065664010a1200392040d51a8819815050320403a50000789070405030071546190300c42e14180c1e000c0d000840c2c49240c014075110b070028100210b04210901240041d00c85464260500c040350020240c108054828545030808800a5200c0b80f40b40c06802e001c596030350140b001c0070106942500c105c00341c01880f4880000041c844489a2000d0402540c0d09082a1608036047e04c0c01030306064140c049400c40407000482248040c1c2c1220214113150300c00c805035420a9180d11a40c809510f00c0740b1000d0300401c040c03001800003000c200081d81c02188154440d42a0f0405400003542c403901c81d00080d00113807022401c4501260044a01061400c007420b0141c401680c01000030820b5003590086010001e1446904050700c1c06a00100094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 383300881 1250 383299631 383299691
    0x60f010608270a0c03060b0d120e190618060c0b07202d1506040506060c060a02040504060e04032307060e0705010818060c0711060a030f0608010915 65
    0x1075241000703040f144c803030f10050b20040e05194202a0918161a40c2248540e0040d01500020800d040c1110f070482090b1200d030f0030500802020300341c007a801410b100180b90555415850301150030302c81140c01080e03406401400030811b440350024a680b840646d2017402464840c3c20181140f41d46980074200f1200380165004444503206000d030116110300d1b511302d00d801d038051420194211a5070398804071203451100036107200482c5d06490a03410198202c207009100703506100f140c9581604014040d902c0200b80303a80020200900e090a0040c000102800c040950380d034078042d140502182014003911442000c10344030002d00d203000105030380d107560304014100426088007001a94820103400740303a007c101020006201d44500320301403401c40c02e22401034141920380102c42e0740300c1d41140108481072110a031011200c0c2e224200a811588815640400e0f500340004848085800e01c2c2c225171200c1c3d041c00e540301c0228407410482a14401c034141300040401416099514403804084e0201c40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 383302131 1250 383300881 383300893
    0x4050402070515010503030c060a0903020708070f0f0504020a02150a0e01020f0301170307031e050f0c030d06060e010f11030c0a03050c16050a0b03090c030f030705060f01060827 78
    0x140310b4001000d00d190041c01620907841d9803a2800c1640d06d000380c80250700607034001400980c0b00b240d40d41041103628400c1c01151002c640321103040c0d040c0000c0f50041d15414241c45400c1002c0c0d014164104000d01701510304500d000320f5580025100d01c42d14402c503000700030b2907001c6400f41a1f241d00006112170300710021900c41c0b42e41c501400f040e0703000b8418802c009014805078404001c0110444550382e916440340a50300c030070320301001d0380360354003560031400d0000510400310302c0175034400103010050102c005556218001c0c8008401c484150300b01e081040b44111b03403240c0780c0c0d8118a051447ea201e50410045548440310000c0c17441c4103540c250440c07401081c4280e0101500038019010241c01c103401e454904140d00d19214580c05144106030b440090030900700420b0604c08011a0491010001e035a5000402c4022038038011006d50000415400013800f00148001401100c0e08600e10416000055143c20340003010103001400545a0039096140b9898034524001e08003080311480b000e0720b003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 383303381 1250 383302131 383302133
    0x50a0c05100f050606040803091e040f0605011101050108070501030f06090c02070609091a0d0213050f01050a0f0e04110105220e0f06032508030d02041403032d0405040207 75
    0x10748041072030081c07081d0030032004c02d03002d10300402524151401240298200343c2e92a00300091510200ca044200541c180c4914000380c4550040d40d00d656400e14020600314134100005004907503c000c810700c00d03454072005010f14480840c004040300c000742b8002c50f1110200c55190b0040c0400c0e403040811520b007807440c0c0c5c401da40201d01c0b00101c1e0074585569800aa80c0e20135401650b004030380c6407490b590449014022443c0c1504110030b6240060003040c41071450240000403108159406211805050010012841e00359009000b500044024402582c43c0c0010765001c28000f4200901c500100d803440b0103540d120b442a40d980704481e039041c2680582c10114280802c04500444190421086c000754410500d5090180a688041e00a000400c9030b140c1010f82c031421540f182ca50968500300000c2c91400810140001d8440110016510b52400d0410310b8080d40300034000b406a00f041c13004020989903c8402c20000e14901862800440440c1d5030070202d1040e600503507842440410208 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 383304631 1250 383303381 383303413
    0x5010506010e0a06050a142703010b01031503020603090a120806100c150e1c0302031005030d020703080c15010602150c1606110706020304050d0f0c030906050a0c05 72
    0x240c06020280c036028500e4a820040c04503029460084c034000c00d60130010340102c0d51003503101000740c00804500303e05011580f03042e00782941041c0c90440d15000301103001d5043d484c0a11074910700c175000742010451100b0071400200b0101c1c1c148000703885907002200042c10700c641445001e03069540242d075020052210800541209030658080d80904001c2a804940c103014505c0f06404541000c801340300712802d404040c003c1d0a050f0400721860003001280302d50b5401091203200c001c8050348025890340b400100313203c07030381c02c1c5944524826400f049040032551b4000c248482620f40190b80165038510007001c2610b06208810200c0c002720001000080255010601000c171000c810901c80e21a150f901e03007002240a030307400644030000c00704604000644194012841031104058a60500340541c035450200d03001100c040d41c044d00064400c0c584503a0021380580c8164050406030081e00c0d494074002e200782c0c00c82c0100c0e03003408800910007010038010b050498103a680310046480502425420f1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 383305881 1250 383304631 383304641
    0x30d0c140d110c0402120a02070606080f030a080a02030f010303110a05160602011a0f0f0a05030a110a06051e07020f09011e06020703050d052d09010905090f07030e190501 75
    0x102c0c070b15000d01510904586024000c9450317088108410059a03201d200c1448001d40c0401411a80907a0b50040051850000c3c040420790729000c00c007030341d00c0f43d4214101070300320403004080c0b10b00c44c1d20410030407110340c01c07025286040d00d40501d0804039242c101c00540e8500503100d00d0140260bc80c04003071001620720207601c0d9081d94259030007801300354402d81c4000e2092220803041eaa0103032a200e42c075001c604161050114600c4000c0c00751144580c1c0d20007003070501151102c155a028086030091403076003005071461001740a1071070028644040d80d103003d48603840e0303c0c0b00200c4002d40011100d00b55034800c0161200411f004214240c10f594960141540c2c10702000e81036000401c040000034001d0021801c807048a805c800502858044910304503036561085000c10903100607040c5c1c0310b0701d0503003031000030300c0700e260503d406039990180700009408540540c2c080741c4100e001c08100005000440b02468200a06050101d08010940503040c01c141c1058245443d0300804203583c02400015088 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 383307131 1250 383305881 383305907
    0x3030e12010e1c0302160330050603010b01050301030503030a111902060a0f140a050403050c070f060201050a06140405070509030a0606141206012102040c020a030306050609030d0c140d 81
    0x1007015507019100044d4164018156088801d003411910b0b00f001c02c0c01820f8814000800c29001c03203a20000402a903070100b00300c4010104590340d0420010581404d111311a0b411409090082c155891551190344e60700c0020004001d094503108034501c111901420b6071201c0b81c0071940c21414052002000750707941c1c0126041d24500f4140030f0400c95002061040d14054002c14002011540c2c80c007070b007000580f001420440400204000c42d0f2411101440404c01400320403400055451501d24000d0a541000d04441c143c10710388181040701502040c0000c480280c240d070302044c03903580c0160544247c00740440090b0940280301d0468100046503010700d050702c8580c0385039820504404140000c0d000c00003000804c84c0d105500510040000e2141d1042c4c40c7c0503800c2009400c4003980c04a0b0940305413103820805648007d01020030103030180104000307054207076101030a1100c1200001e1750340c100801c40a0600c14880c5e80b00c01071028001440e60481905412103e404080010040400d021485 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 383308381 1250 383307131 383307163
    0x4060506041b03110d0e071d070509010e0d020a060504080f010903051c09020604120b06190603020903190b0f130b1605120f1b0c060103030e12010e 65
    0x2000410a291900c00d401c5118480032840441082c00c1c40c065009082004071118144801d102144294180d8026140c004040c1e002801200345801b012a00f100d2401c0c0344105410700c40c500f0030402541c000256408100240f80c030310b803040f10240201d0b41c003201d0508080c0d0414040b02010031100d80080080c001c60310303500200d40011196010341ca080395002000200000c1c420440e20026144e100600342c0070f441504000282c0000650006003e0350190380300c40c41d55107050400c4001c2c013541200480d4864000c0d1030031302c1c250a180c100406008120700524060560104460250b6142001070820002202d01c84984011407420550b060180c100d4043d440c04843c5400a032007c071140d050024165400180b030b84081e00e98500b501c0d9000c81030b011200422406111001c007800411240a0103500112003c0d05e55080592800c042d50041030050030f40300e4402c00c5130066152000546504403500f40c03424001c0682c0304c7c070000d1b4652442805540d025800c0188891001001151034108403103d41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 383309631 1250 383308381 383308391
    0x90706110f0a02091b031e0108011a1201060f0801022d1801050702090a1b0c08030a0f06080304060f080708190b010203090a030b1006180b0f120a050406 67
    0x5140d40c1c1c4000c0d0710100000c98001d0340c03200006003003101501c0d80044401010b44e55500842280c41c14070b400803180c0c030041540b521900c0482d40c1400c9400f601402c8884024031480e6a00b581440742440323201c00d0a0301905440d03000603600171f029406200680760903040c0400e410f503500602c5010790815860428118601180490b07603056804030b2561080282c1d4099007080b400784e8204c5551048441c2440c10300a003006450010303510916964030a4040c45000030f0102c40303035900503800c1d0484246d590305001c1d040c3e00d0360010034002c00503030744d100064000210300d100400e0f140c03001804907644403003541d00c804a4003144940d0401c0c0103082d0f00b0303207955500c0c4107907680d4841140e1201c0e00b690010715580c0c0f00c1d00403154525a40e00075244103901801141e10301a404008034500c20096801915030100503010310690340800e88a00000300040e1030308541100e58040300101c0b95a46100342642110700181507182d0904500035a00b40d220042e0380e0840c5840c00d0355100010f49011981190040c1c500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 383310881 1250 383309631 383309657
    0x503010c03050108100b0409080f031902041409100305031902060705090f040b0f150702011106040308011203180e0916080303060409060b04090501020418090201021207060f05090706 80
    0x9200700e504903003110005041c03290101100100408504201642180e00e60f59010040b43c809d1005040c031072010784600341e80e881d0040807201e41121442ca4410350b03a00402c0b0421650b10b98190030361440314120b40c4140c158499001064000e922980002c0a9000205030f949085038070106049803030303a654080c0c2d681540c80c188219103a1284200d0194054031044400c0c0150500358050380100c640030380f903941c192480100284494549010313036000e030100040c401d400c40d40e028025103868a86400285a00d0420b5074014161110500174010003039440c0d0880b509052141455a82c0b0b030070388410b10f048441e00c5032080321a821044503500814890b101c03104c0d5802002c1180801120f1000c0c01641c21511a6070400000e4048004140c820036142e0300b0b506400c1d0380d14881e110300d80b4400d6000594692500d00d80400c0c6180c1d081a420043d843e00c1c3c10030003d41d80118120714440e442c0c5040c144c0e280d034a854244014104c003480045042d1404003003083d01070300001e0390026190039455110107003041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 383312131 1250 383310881 383310887
    0xf120a0912091a0a03020d1e1404330c020321090d0302180315061c0c05010302161a090712210c080c030a0e0a0b090904051011040503010c 61
    0x4948242c08056410f20004210b00ca518005400103056034540945000300410900303040c0c0b0761041c0c629000d407001d5425085d5401140c07040080301c058809480d02140f816031038085804a40d040301d040d40380103001c25040507003450000001040c203184002c11201800000c0207549811a82c1c06810381420302001200407150341d04e4161081e850100189040030b103c00044029400c1000400200103030071099158590f814449081100003103080b601492400d40100160100c01110f2000101194942c030404100c084e60481c0546001f800c0240c0d946212142c104e000d0f48800308003505060307214108802040c0f9468050303000d054201c0849030388584a482c1c841004881c0c1e640185122451040500c0e009801c0c001c20028050030709202810702e1190300c581c2c840d507000c03031040710b91a000050a501c2c000e400c40401700c3c0341c1c00250b40c3d02c4082410698504102d10400b40c0c1140f20303051480024040000402400c00e206403039031000d002440ca1005d403c0500c2e041070207414825403c0034003c0d001e140c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 383313381 1250 383312131 383312147
    0x8070f150e100c2112270f1a0c120601022808090901030812010906060906080619080a030305160801060503250c050f0109080901050f120a0912 63
    0x140c002d018250703903a608581910050000f09003212125070b0300c0c03207684030700941c2011040403224035100c2101425426900c0800c480c140c40810f146000740c3c1c11080594002a0b200c500000c0e40452022146030340380c05d03d040c00c10b0883e00c41d070a00148510812114041100180c150758000038402140c6032180e00042e40c54500029280360480560048041c40004005482c00360700d0082c14020b260078501404241840d07802d03042610601400207036802c05c854980005c500401c00b0320b1040202d1414104000d0007048540301e00d0040001283c04079401d41c5c0d9051214401a82d0400503031900b5549098075070b00c2d001d48000540c0030914000000e10040240019030bd081d50041d552408107a0a148040d02c003504003601c00e800030079504a00c040c02026940394068076018a80b6094a54011b03031600b00c0c0360409040d00ca0000381d0512604800051014041c0e440030a000d0030100e4845405258002c90750040c580c0703c0d20414a0340c820310140c00380c2e550010a4890085180e045041c091102c00d540001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 383314631 1250 383313381 383313407
    0xa0f15060302091302010504090c05040806070804020a140301151403120c121b06070e1216050f040e070e0403090506120c07060204032108090c01210608070f15 70
    0x56403c1e0000e41c0104000b100060780350320504040b41000d884154041c1220114402000420b4000400340428501040400e60041c02458580c0e8203103090f60105103d80d01d80c0c0300303249105c20071003084641369900b9084401c2c1251100c034003603007281e9202c0d141158154556100390003402000c41e4000341d501c443c02145c12441095000b05141160a040850640e108200c0c0e1410310f00904900c41c0001c60178032034503004800f256140e10039070950700104201581e22070000100750b848404100204903c05103004100c400481e5848100c1025038081405004413400a0810340202d26021989019900b2260701031400f07540c5186903aa01d88003440607070700c83c5a000880c403240c85030025140341d0340e0301c1c000c4c07250714410078015041c5503036a40c505c1d0750381d0303540f480b103490218006442043d4140c1c4086c1007640080703e4401008054004400a00700001507042000d150070424411140701109402c072800400c00d0104940c43d1996074000329443d5900c3e030162500c550701e2440c112040b580b08195110300b039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 383315881 1250 383314631 383314639
    0xc0303050a090f08180d0602040509010e0402011d0f06120a180201080a090206070602070312142a070c080a03030c05030f1305010f0203070c0209130302060402010807110a0f15060302 80
    0x56603c2d16a85400d03000741d019101810525085800b17261911102004110b105050150300c4500b40000c1049c000416008100d82e94821000c00000d42e03884004030b119040c80c90721424092075100c02140700d005034100481d03008100082c07082d0110011030800c5101c0e5070000c1c170800c120180d241c51500c9076541c200707002c1d000800f40008038660400c1d580c80800103c0c801841d02d80780903115034411080c1d0304586003e0300490850400140c0751101402a04640070100e01007054600d0450700103a03070704d602d20700b01e42c1c407002c50b94403003103030b400d8001040f56141604a50003c0d0040d03920040305648003e00e10040f4006800d1444610700ea90080080d030740541410000201c0d42d43e5420150200e600c40110141c65640d215410b001c40c0010501c000d5010f44001d5a41303100090180c0180b00300b00b4006402e13030140c98055054480800e07804a40e103600103034240390004050315100b900f1106101c00700003140321401031810000401207444814000a031045c4070040003400112902c40c2143c00b144806500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 383317131 1250 383315881 383315903
    0x100c0236041a0709030204060b0702130506090a0e010e030301150917070504180f110117010308090d032a0308010603180809150d090209160e0d0309150c0303050a09 72
    0x1280100c1400c80b50f002d485840c040c45450399a800050a94030158412240107a0004840b001d42c205a0410140e1a00d409020b00903420810080b40314464010101903c0035502c5401356407500d001e420110b80443c01c2401c8a44a5031a00d030904107552503140c102000c640002000581c5130030135044000c03001080c102401c85149480c00313010140402200b40369081007112140702c0003841822402c00c2c8503000300b00c3d1600c0800c60b0b00004d00401038810300041d0780d400000c0104001900380d4222440d229060f200fa0414030014501564a0745046e00280d03107408458895500c0390001c0c0841401c50741c042d681d69091640d032140250f00b140c3c000b2a640c00f42c0d01d0482c0800307020445509c004c1525040103000d0000c4c40961580030700481d000381395240f032000e80700c9201805629003640c1d0207030802c0b0703c440d2a904416609101400941c0d082e80410300072544602d0b480140b5010700c40010040c150403d1982505c055050020161929803c040707010903d01808640345c810584518070100b50b001c00d8600b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 383318381 1250 383317131 383317163
    0x12050703030806010c0f0b06030606030109150b011b0f15020406020613050f1f060e0c0307120908070311070e012d09091b05041a100c023604 62
    0x41c1400d4010070b03d41c1807040d205503584c0002c44003a00080002d00a40c2c00c1c07001410440105030400c4e0010744424441e0303042080e0130340072941d102d101e1119140007800008040082c0f00068a903068044181244d40d00311701620001d0165501680c044603205100340c01181d411049140203e01850180e900164400e00004003e148074141c003180050080040700e00c158101d4501c14607000d0001a04800d00e00280a003500010240c0200c102802840c800c40503545001d200040ba81c2c0002007084040141e80d40180702403424540c004103080d034021114542e80d080d941406041c10201892407030313046c400e008000440080c640416811388482480028545e4400d218900030403d4070140440c2e42e2801410004811440d8030503080e05a1264680c400f03007500007040703010400e00c940d01140c00b403802d10301c204441001400450784003040445080740c004110080c1150340d82e5540f03a009400c002e07100b8034205211001c1541c85016507000b194020006901c1608072400c10b4151030060001100500401c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 383319631 1250 383318381 383318387
    0x501121a0a0b13060303080c0a050f0304080f07030804110f010801060c02010201180c050126010303031e0f0501090b04110307030c020a052b050c070308090f04090602131205070303 79
    0x1d03081114100c011810088400000750146211041c16101d81e640d2075080040540108080ba4400000c4503176500340710f02d0b60000351192103079155442c8070341000000901042404000d81d0f4896080880310b030b0701c0322982d10f005400c00348240c3c1e064aa0303244056440d1468075085100b158110010394800340507901e031000c2030f03074400820741e401c90541d520380443e1940c000e4082c0700c0c0741c8020302804080e07038214a0034001500404104e41d4005024544042c3c525500c16913a0361641100e030f05160025400c0c0d921402070700841095407004030460300340a54900b01600640080381030b41c05582c000c00044840a040104540001281d840b0100013440010301c1e446c0254809901280c203401541d0a00200ba0f41d03190401d101003100390a2118010041c61075800102c1d0040141000e50604910380702c0c410050b075542c0c40303240c44001d000c808000f90112090700d0b000d07680801686c014006200302800f0745000b2019420440007841e01c05017070040082c1010b07129200c40081c50b0040050030206003541c03000c17 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 383320881 1250 383319631 383319683
    0x507050103050a0e0105090a03031503051b01030f182001020604141c020a1209050904060e0309060d1b030b0904260a05071101050f0a1d0303040f09050112 68
    0x700d0843e50740c691580aa82e2001c2c010382d031042c2c400c54090480903a0034a00075007150f40c2d1180444103a244d5080520008030f001440b00c3c4845200442c00005290800040b0050b000360249440d4042c10720680c404c81700b2040c0585004c8038851516540c80380440b9803490500b01071044210b006a1008001c034012030144144450a0155141500c8034580c0c0068002510302c000c5000c540164009558442800203c204030080804903180180c0d07040e140c0340c0040c080c501c0141020708065906c41c0300d00b00002013001111241d80014008a444850702001180200481c5503000e0f80071944c0c4085501c0e86200784030b0031402147c0200314a4082d120f030b440c1da40503d01700c4055000090209070210508100d2803002c2d105144150340c4103a643d4045142c01c2c105240f4941401e414008107110080028098105403074034000036250951024130422011000c0031a44110b0a170140000500419128a0881040b042d00c00242e010722450740d944114200189440d030000e8800b8800d9041100c4205040c684 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 383322131 1250 383320881 383320891
    0xf09030f070c0b040602030304260a030c170903040f150f1805060304080919031e0c030b01030b01170a11060a030b090108030a021b0a090c050d020304080a0e0d050705010305 76
    0x101e82c1ca015220b90728901c03641d0081e00302d20007592010040100300111100d5458003030300b4894118603001d100100c840014041e6009070b00506031030380808501c20340b0030041c1049048020000d202e05040044041e03440f68018011241c204c0344901010662888800542030169040e40e213034176051202000c00c54420401201401a410a61800181c26655032005d14001d50040c3e26040c0e4803080001000600c81d00c00d4405618440444800c0020030005141d02e05205c0e8901314039603541d0003600e0080c0c00600150401070503d40707040004018402120784081c160360074126841c1040c4810b04413140d48642d030380c0c80113084901114540f401818038901400c03002d503060401149a00e15400041d100b08000d81012800750720105004100e05c0d81007001100c0c1c400d410451445580712103020451000f010700503141c1150301d64480500081c4a90704680c0810304503078045482e0f00b05850b00c071740030fa40000c56040c0052103900f005400740c6421300050b90f802e644140185001032078000158090030000380 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 383323381 1250 383322131 383322143
    0x3050c0304030c090c0e090f011e090501090b01020c1210090c081b01030c0903020904121704080903150601080a0c0509060417061e010e13060c170f09030f07 69
    0x10020009403803c0396000948004003001c508641c04040080501d1015030300a0310a8a4003802c0c40381460141d034030306054481c83d0aa0b00b503407659120340000e1340803660f400300d10014940000000c0d851003075808604400402d90070740c0c6410020104024a042002d0000d81031034019002c204a02e640c103910003848030740704202c848107455498000074208041d4802044d55002020000022036900d4800c020700726215003862403082e425074006c146080c00061000700000c220b01115241640501c10712120640c4501c180d841900c1c143c035010b2030356000303200500c1c002d119017a0349a042c012200f101c20f2007004c040c2e503040700035900c2415440184c4413003581a01881410000014a40c4030100200040c02004d151004012000074601d442d00800400040c40500c6100298800c840f240c00d03182d04540d601c003461141500d4609001c18510241c4600500d0b40d4038140aa0201c00d03080440e04000b42c20004d00070a0641e5255205e00c0404000ca500020a800c10450500a07281d0240600f883c580202c0f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 383324631 1250 383323381 383323387
    0x3120c030902100e19140d05030403020333040209040602031b0c0102040e09010902010507330e0c0102120306012105040302070f21020609010e0a0303091701061203050c03 75
    0x34010400112506039200f0014802a0b185801ea003400b042101001e042103c11810300b601c0c0084000f800c910070017520344540d12480d03440e0700748801003080e20040e5400400b601c00151141c0e15030900381c0c000114908416280700c1409218810819181d03120ba5006005441c141d0b60302d0303482c480290300003051080c402100e292b844100e602c00c03801510815100800040c5d4030350508100d5103410100030329580c0c00c2d80c1464030700c0d00140d038008140c40e0790348da02a09030301191424400301e4601c8901c111a41980e84400600c0c0c0075000c110b034020464440d65038041d01c1592041d14012130b2100c0d518021648605020800701c0c2155101d4900320380c006038003003001403c0d11180e400000c280e940564041e00140d120510510010584c210b4070700051000c1c032040d04400290400c0c801c00303000030b150041d1040c00007188200380c1e17034043c1c3c1505643c42401420402c01540ba03203405003244d0081d0140455840381c4a0410448881c14072420094442d032403104580e00d501590216011740c030816001600740824 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 383325881 1250 383324631 383324633
    0x120102040b070f1a0f0a0e1b150d09050304090e0d0e060904020408011103040c120c061d12060a060f0f1403010207022e090b0306130615020312010b040303120c0309 72
    0x2d132070301d24080c0c0f03501030303183c041380c2030000354081514940403a24115800011307402c1c2414001240d00112000c0135242c40445070b003090b00c0c00c9114098800030300707196420000c030a0100800440144240e802e1f00304100031031031400010980d5101804407c1020482e96a9000c0c0300c1d1a02c03001402089000520140c80c19468040803800d440003010710b2014034501100717110411951016140242c038841c402801016440d86071003255a00c0740c8141c0e02032080181c0c11558840c0c81e0569501c202e80f0140c004201c4030381144289a4860088480740b0a9510380003000ca00d01c01140c6480c000c8800c00001203083c1c6080c425110000300c8d880406035410740d400c2100703000688070340032003002849403900d0200e00c3c0c8003289031000701c281e03d154a60013040a907600a0000c12080b00680c0c1c0c00c4000bd80d211041c801d05003121030001c01e003a410007a0f0700d0000c80303140c600d01c80c0c0c000010202417022068103801070740c2e6000444c0060040e400300401064003070000150300605070b800748600c1891131401041504031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 383327131 1250 383325881 383325923
    0x60d1a150405100302030601020a080304020d0b07020610090b030c060f041e080f0c06120907090608071403030702030d0815040912110a02010926030d020405120102040b070f 76
    0x64022600d92101190030803803440d000081400102840c1000d6145190120000351200e0070324800514011010021406545804404a060f0360388540300811604205a01039680c400494402d4100c00b0880300200b0b0a008034022141c04c40c201a006040513800070042102c1500003151100f440c00c000d10000814031414030b0502c0303144400f5400c01c0412170408100700e050aa030901c002c0c03120783c06903401082c19119207040b00e056200f00ca031501c507607807511140c0500f8000984c0c040340c01d0504105000c11400004501c5200321a038019020700041c411905054890055401c040e6040d00310300f80d0901e10034050241507501c168601c1558110007a0440050304841d038805061390007080ca03440d40c00c1030581001c9421790040d03c0700000d1a091425500080000c2100d01034401e00e61510301c4902c40f078000c079030240d00710703041d50714140c039124400d582026001790000e215940c4030b210200d0303103e18280310620880d4140c1e1100c4100310f1914041e601c0b1807c00329022541240c1c0b86e10021300707440283d04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 383328381 1250 383327131 383327149
    0x60c07050f030a0f2a080d0f0c02010c0e0109181e18060b0d0b060609060f03011d0112080a140d0507091724070302090916021209060d1a 60
    0xd403901491007044c21802006120512000050303041d02034601c520000401013100f00f02c035405503c65170381d40d00030050343d000352904003551801c1078205140c1c064903a806405c9600c40482030390340c0b01c0c52202400011901d0103250b01c140b50380408105140c0710381803a5500007208428660906038600b06100482c0000c039811513207089000b80d000621344080054501400c6403216040750604450b40058640005582300030300184d210b14030000d05d688081d241ea4080d240c281c9102545261030350703507400e507801c280b01c40e030007209820110b00b90010800c0307071045023411400c6410107016801c00f05007800c1542c00742448103420240762428400e40280a04070301800d0720a510645d1066280f0b450580d4003c0c8941c618050041c5d1500321000160b00c100903c15107104543c103200b1880b8058407081c000790000d202e45616281c002030000c007013144100e5061100540c10005da4215a04c0c5c0b107414600108901a00030055801881004071416250950700b1501c58140c1005a13202168619070000e22014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 383329631 1250 383328381 383328397
    0x409061b03060e01090603080910021603050a020306060102030c030d15031502190f120b041103090a051912080414070603240e040f050a05060720010608060c07050f03 73
    0x70740c659200b40020509400d8007401868024400c2c00800e0841d41c07545001d020f007010490207085000d40d1112258804c0044c0d0801d00c1c6003602c8942e00381d4990074410703140c0e0f00180d0300b07038080c3c821034012924651000044600c044d00c0403016504144010300210040d103601d0075155120140424044041480e0341050143c200500390b005a48594500c01b1071030f03201c00002004240035242c50070048803074215500c60268aa00400050701c1d071210400100100004e00000c02052008410400d51100019240c00107a010303004540501c891031a20498694405900410f220030120040b54054015034105030814480c54880400e024400c072014035024895029500090f106e05070303483c410004401d64001591801820508a42407030f011581044c40a00020400140204c140c410b00000780004190f003541316007900e801c2d052142c0c0090020b481c1801da0345070b241c40c0a40c041c084120500c11034049500d0b403006405a40d440d03c0c1c0d4656681c02005050b038443c000c2c0001a10010f60500c0100882 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 383330881 1250 383329631 383329637
    0x60c03060108070c020618040e0d02161e0b0a261905041106030403110303360a030806010e09041a160c060906020c100608011109010e0409061b 63
    0x1914000c4001810880003410003400d00c05248041d10150f01d8100c21113040500f0380c41d489540701e00283c0400d00030040700510030807070700801008124980c1e011445101b00b081402000c3c100944490b0a81c0c2815440003182d6000e49460744208100403009000c2c0207820202d017004c6242d81e8041d42081004016494501c1102030103404002c1c004042140307450311650502c500b0802403800c1c1d51000a112004081c080c4a00d0300800001e0070075100350b81c9403c1540c03401c0180e940328207140403aa50001c001206490846050903074000c8980c0400c0520342c4078031038450017410080520784094694990141c807480c100001c00c984007245840b0046064003942c410742d114181c03041c001c50192484070016052000100b002010701c070b851a1300c84004400c103a080040061030310010724001c4001c1c0f090103841c05042c021034008151800c503540c4507404a5452034020b00c030807200c2c101092282d00c681d18005000c640121980c40050909030b00541659115402c00039502003403864108882c00310395805400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 383332131 1250 383330881 383330887
    0x32206240609300f21091d06101413080c01080907152f15010510110c040603050d18030305040302040f060e01231504030f05010b03060c 60
    0x5a658007a05a800600e60110b800600314281c108064070610603150a2035103000f100d040205021094030001c8007903a20850036030068803050004942c034100340001c43c0104514030301c0042d40340400328400c00200d000201a00c0c0700c3e590082000703404000e0302507040410104151900c107400c00c1d44001d10030a035005100c154041c1c40c00800c0b038540034400340c3d01ca040140100511013440000203003031007581e203c400700c04035a201a007021607060f0780b41c030050500b218042c502d54032000c50500c0c00802c0116100e0617a118400b5102d00c502103c5000c5c4289504202a198078000309881290f03524102c40690b0142c50800307880b480014161095500309803080d80003083c4429010350480522500183c8e246840c462162a544001d0840c0c012444007034013880d00e0b0403000111004603440100a8030002d1680f5a00e940c4421030b43c090215a5501c0300220020342d821580149099084001c040552003483c0740307024155501e820034407044000440e6159215070042c420795400340000e510400500d495292 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 383333381 1250 383332131 383332139
    0x204110403020a0915050d050a1a0906100e01140d060608061e01050108010608090a020d0c0812090619021f05040b0a051902130f03050f0c0603220624 66
    0x18103c040da480301210354075000d00ea496001c0340500701d0017110300407034030801c2140b4203003045810034034240d0000b001c080c260903030b000c040d00720303582c805005042450840b0015503176807010607000c0119004501c07442c00d00034010003440c60b01d81c0700c0075200b00001e00075a0008841c1d40d9810162200e9030040703c0b41c0e40007038007042440b10285c03441c480108407100051116514000000e824000180910400c1214050001e0703d00802042030b900d1103030b4090807000500c0c40604005036620854001c249640c010383d0f4012107040e42d408140c4404c900000c28080c60446840304011106150603d01019805103400f9040c80d040a08015040e2012407d40413600c0d1900c1d140c540b850141c0113205980312b91510050003c030f44181c00f48070000c0444404010381e03800c0c50040d04200160700381e1024503142c0d01c001c004010480040342c03030740c12911014115080c500ca280100141400111440c0034429000480075114000c5004000b41c1c0314050315002468013200403509846403210700d10307080c5402401c04104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 383334631 1250 383333381 383333389
    0x6020f0a02210315010306080a050c0f0a08150711030a050403060f0501060f0c05120403110307120201020a1203140103121d130b0604090c020706110304031a13020411040302 76
    0x41e4401c960740b409403400041d8641e20784498040a0310a040e641d8083c0c00352800380c0d00aa203c070002e495050304407801e000040c640f1650356400154501e010f84111004820315040070b1030200103482180001d04160322211803a4030482400411030307020011500700d003101302a01030005011000c60b80d620281d61305d08505056099684403c140712005140500400101c0c0c3c1c41400980d12032102c1c074000b40c000c1c2c4181442450000403004107074034120002400401c1042c1500011000071042d0700f542d140c1551540407808602c0d40810203405078000b00324140005144058201c800482400c0c005003243c4442d2006507082c009820840f6018268091182556000713514250703018600c50307001c4012030030707880420a140e51410700409419107442441249076900c1060344c0240c07485580800c01c241c903ca0009658000310300c268004191240d00100004101200311000d40c1e40001f0300240400c0c1d40480c65100c000000d140000b001101c04680d0010703540c601580c400f40380d0b0300501c6512141580104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 383335881 1250 383334631 383334643
    0x5040c080c0915010f03060509092a01050f130e040f02310906020708030c071a040209060108070314010e150616120c2a0605270102070306020f0a02 65
    0x4510902c096020002ca200ea031901a4034200420f1030840100740f40c1c1001600034118a801c40e962044c4400b04015015a000401441c40600d00e560714404080d6010b02c02c0448a41d0300031a40080d00c208107104d25649024010480314071740e0040260030030356480604521840c1500c0032031704984a0080041540340100c2d4115100101e410484c08290103100e0101c00d40d807150410080081d11a8180760511200384d040d200100e40104859980340b030480d90350a09940020005c64850701c1403000990307481c00a0745582c1c0b2a0b50b0192401c041a01d4400064601030802040342c0105925848429000540002034174028012003c04081500b003045852170f41c1406d034101d450047c4010b2000341d40003000070300344034407040d00522440d81201c5400f20445900303d40c150050243c1c0608110a411554100d09252940c505c20018030700607038881e403046400344110680c00310380111030040b100885981c4010a04440014011030b40d42070703629565a01a6000780160807601140410b00e9810b00d80c043c812 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 383337131 1250 383335881 383335903
    0x5010b090f090f1b0d0513141204060c0f0f06090501060518040f05151608060108060d021306050d051005090c0303041401180e090d08010503031b01090605040c08 71
    0x10251071840c15280c6180f4141c0020404902c0b1448001a00d811100d8041100d99200014206000510300000e91078424101504125451102d00035000820040070806910a40d40d00c100790345000e00e070450448607140d204c4000d80d4058100c400c2040000c840c0300c05500f500c0c0c811b030f4000c512411203040007400c642040d40320901440d881c0c501d5402e41d90327560201c03d070f10030751013040200151040c0c00c0c010728000740c02040264411400c0203124141510300800e6145c90400d5440400954880004448600c03007500c2441e0004541946580103207014183c4a80051144000248540d5203030b000400c4034420b90b100b60f070b050b0042e40312102d4040c114015290b108403108002c22400200e080880c0d80c0b880749208180d1340c407001c8544840141c1c0b040181c000404980418100c0e03981c0c465200000855080e182504144a007521030540e480c0502003260403504c0c02005182041052a8121041107203803401c03181c555030310700310000059001d00c0b402d401207019001200205040160701da140c0040104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 383338381 1250 383337131 383337139
    0xc041a090a050108101109190314070e0a0c120f020903070b0405100c050f060106032307050a0c031b050d120e030307110a02030106090507021e070902090a0905010b090f 74
    0x1404401c01c0060b440300728641c607080000b00c16581e03402a03407050164041e480d0f807050729021940c0c1c181c0741388c50440d000d80f401a0700421a009400a6050369403005124849080345907500180d40c09000740e01159448120781800800410240040c0040710a286540c458660340400c40442d83e041c1007003c01c1c081e0481c842920b184c6414600004d070072158101c0070303404001075480442d04000081c041108229003c0007203440a50712114040c02800c00c0c101c58a07640f100d01e044064041c0b400d40039260044a60b41c6070146424042a0304584000705204140d0910501d07250310300341c404441000c01c1030346004401600085403e500c0c01401b40109141c40c2c2d01d007a060800304095071a0200842e50041030303c1c00c1048400b000043d4090401948036030196043d40303807070741c0010a014160042c4d031040000f942500e030024910101d1003182c11849542941a07803000c04144255409a40100b4141038010001d0f84090343d01d5000c9019074009070000b442c1094045120941824030005104549000729 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 383339631 1250 383338381 383338391
    0x140102070308120c04030c2408070c03112d15011a0307030e0f060703060605040810021303080c03070c0603090230030a02153102030c041a090a 63
    0x2880c0c900307040c014580f581048075914000b003506400c0660842d0002c43e8450400703242c0c66a030349900848007510b40801d4040142007809840700a124602c010701c500056102c25080c01420707241103c0003203405500441074400c20344c04e42c40c070803002410300800700c4d451100b6068203207500400074101308e0100d0030b10381c9400c241c4005101414440d402680d11200095403c5d450750b884100450203070401d4820540907006036288120401e801080d61440340c03400b17481c00d12903a80ea500c3c04440b14441da108140868010380f00f285c0c00200d280c1c00810310745c1c1008013090f03922910794441d245503034042c80d040c094503800056a4410032210140400060807681001c001c00c004540100b482041504190030780c2640d8844100c42038140400d690540201c0041225103840c0b0002c0080e540b9510192803203d13440d00200000c0e4403250b4000311140300c0100982c00c0c0d5502c000422610302a0a89020881c2e0501954920791a6601c4500c680c808007100c40004066003080ea2003030000117040900f448400d03074240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 383340881 1250 383339631 383339633
    0x20a0605040f120813031a0105060a020c0f030f070e01090f110417160803040315020c210706051501030c0207061d1f0921110114071b1401020703 64
    0x2e182100c048070380d203500a0002c11494941030055120340602c003285000c007584040144a0480408941c01680003211240c0c3d076215405c201c083d0161440905c016442071038840102d0425130450100041e0203404c90342c1c0d05030f00480351800d000c6190415151080d4000041100386028001d440d00004840000c10241d502d075080300103140f141d4042e030b25405040450068141c402003225400104640d44139080042d151080aa22a80584010303104800b4009440b24484114421550700d0340100004203954072583c1c10030108040400c3e401000242c05010600108220740140d07440b812030286003084561804002501322100700ca0003034210352181c035082c4101c940045c012421096031100424640c01e03102d0004141044c1201400004541c0c1c05690700c66507000103d10007aa110340030348011a041a0180c64079500c02c04502401361581700e800c40900d540908a0740d1140030403403803140c2c501724044e198400d00c0d50807800501c0c0341d142008420040106101c0c41017040500c03d00c050112640382d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 383342131 1250 383340881 383340899
    0x1006080606030f040510291903020d170a080106030516020607080a2c0d051801050706180c06020606040c170601020106050a030b0627040b070203130e04020a060504 72
    0x1008003e00b002c40c0090011800703100c0c0400003c2805544801e0138421121b210089600d18546558a89100350300c040103540d0b5807605101007080c03012a001d41c03d0360a883c0d0b40821000783c0e5104401e5601020615940f180001c40000501c0c0c2907400e07446580c0785500d480d400404440004180384001241000500801580810301135000000380c0b41c00d8100391a140c0c0200c0c020998140349401e0701030b00340740031100301141c0c048401040029505441c0b0380c1c040442e09a03107520441078035004000ca072026004403503000d034000c0c0499a0042d200000c100d291840900d2aa220a45041c2c0700b0b100000010092242d041201560044080d1400c1c00020300b03460700074101d80c0120001c400900346140009106910035400f1200030b00d030007000c840c2076035603a0a050f80c0c000d00594080d80900302008041303440e80e8401002100e2082c0454002402d41e0306d07502d601da5000805800e03082140030030001103a05c03803202100c034005001d40e0900c480301c1e4101841001aa11203a600003828058148003c2008601c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 383343381 1250 383342131 383342137
    0x306050f0a0b03040303050a18030201060815070203070f05010b220605060c150915040311011104060c030503060a0e07020d02100c170a0e030a050301061101050615160f08031006080606 81
    0x140c91b080200d0243c4801e504c5001402040130300da50556031815000c0e051503030541003917007100c0909007540d901c1102901900380900042f21002c0141e0f008208000000d41d07501c0401040340d01500c0002141785100d070025511068060412a420103c86581240301000d841110000d101c201c03801d40c0341c20b1820b202c036030300d407065040201400080000095101e12080c0000f1101c03024890317822500b0b161901d0b019150504031001e4214035843c0840c40004c03803800d00101d0707040c0d5800b07449111510382507542c04c0320950b000600c4150406e8541d0000a0300c05482e0f00b5450003a030054000e0401c6803102d20000b864084400000c2d601e071402c4c41c08050300b1a4000e003020385038000007043c0100965072043c0d584007610300b0390040402c602c00081c448411983c01000b840c140c1d00b0f69902c0c15040c546c184038490a07202c040d207180e540b000308d44403800d510420000007040c0b1158000d94940b14100c66469481100202520660b01100300104108110203110700800107840c46041040041c01c2c5000805c0c0d040c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 383344631 1250 383343381 383343383
    0xd0e0f0a1518020603040c062304090509030c0a0602031f050d0303050627250807030c2a0c0b0c031206060403060903171528050d030306050f0a0b0304 66
    0x7036070300c01e0401421403444440c001c80d20f40142681d41e607414546803d032403900701480703208002502c045459901e80f050b0b017034041102400403440c078286810800584000e10700600134038601c0c401001010344000b41844000f1040f401400010b0f10313464101a91102d440d089804c0c036041c030342c50020a010507541d550b00c030a103103500740c41c000480b9a07407600170031f8080c02109214000c40c0350150040409000b58046540b04504e03841c80180d003172508282c80c00e070318010720070030802150800e0300181d0664481e600130316041b00b41d460a0074801545c004800551607441d101d80200b407801601c1d150500100300c2805c4018104102d01c14500103003401015220300540000000850050b03000c11800d0740c5a005813009140c01030402c0001100620340a080418040001010203c0f20380c00640102200e5a08280c0c1d00710241c000701d03d00c107400d80d440c02d888030910000500c2d411a00e8000c10f69449140c800107103244a80c500084940c20070040000f5542065200d034071032480d0070414404004248190780c1c100e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 383345881 1250 383344631 383344673
    0x40503030d24140a0501031a010f050409020c0303010f060f0c06021303140a03020f161404060e19180816050a0b0a0903080f07230c030d0e0f0a 63
    0x800c941c81d010103440c2c0d0341d1120510300452244001c030300c01140310030103078a030f5104460040009944100560603201c034400c000c42c0c2c0c401c03041c00d0500c0650140e5401110b6092a150062906071204205003c07604540601403a0f83c0c80400148101d99190246002600c0b00b41410031481403080b10003000c213500004024a00343e00030803041c461840e054a0400516442846580c01c5100b4041c0c0c5940c456041c001a0f0051040703000c0c064802001080b2480000310310b0f180e003400306040030340d058070304020719007210380280c1e8030000064010300d480407450203050310000f62622008544a00c10541c0e0808c60400001c0e0301100f9840700064031601180c8081245228008442180e0b0400a0903c403070b4640c00303401c1c41000340420450001c40da1020b040103110307888400d500c2d00e454040120310682140c800d008a00e68a82c120700710046c8486038888118502e040d14035205414080c2c0b41907400614000d440c850b111200d1090307190091104417508007600c4010114201c1507243d500f801c40700980d00e2411 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 383347131 1250 383345881 383345891
    0x3030c03041a070606090f0f0b06181201020d050f010906061d0102010e060c1e1c0e160b1c0203061011012306030c0108010b070803061f020d14040503030d 68
    0x100b400d100c0e00342c0c0d4080d9080b070700070001c01d0382e02c80400d000303042d00b40489075200f0f1520b0880d9501c0c60041c4201101000c010300514240046601e80458a03c64480015400100c4c1d0039200d1013060300b400140074541c04402d0224050400300480d51010b44181c205450007810084144000781c0d1042020b1541c14174412031000109003600141d00401110b0200704030341c0a04010000c0128610008100310b102c00030100005c401c2c0e0b4081420355024040388010115259031560f8050500c941001c1401c284c8642036841d001c010704c9121b80f4402d01d40c0e0007403a2401e000f080d00f0840c811200308100500030000703070945c80d6140c20341c002042e0401c1c0e59420700c2488030301c0c030300e120302107c0940c41030100c084001c0d940441c01c0c1451114009258007201e03908d100e403082d09030001055104000c001d0499111415044c01c0203400e5a1b141616080182401e4000c4424614500c60b00403040c22650184c10a070040c001046140b10010590038030a40300c0c44114100b003108101c183c40c000708a8212045003007000030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 383348381 1250 383347131 383347169
    0xc100908090603070e0108010b160f02011e0e01030b120a14100f0b040606020d09210b04030810091b120e0a0c080d02070b0d05060d050105180c03030c0304 68
    0x1495008400c0e40300e8002c81c0102c10842d410f03410181d000d0201100b602d070088641c0e03a500101e12140300f40031180700c001e01e015104a0001d070b03620103280180741c41414140c04038200103c510f587e6540114840c00000c2c6403290039100d6503050701c0f4445141c2c509659010a40c446031154507030f01c00c047c4500500d12800c0040320810f8142c2030005003000119090305100d000d41d80c20781c5102414443d880244154903200001410500005000ca1480050303214060468600408a92881c1e4440040907540e6440814540040c4000f040e2507ca01c0c4a5100d0034154100002c2039108161380fa04201201403030008804c1071080301c42050130131940e9903d04080e41040303980c03540c80a800e003510011014466000c40d901000045d503403040c1a00c12107400c42d81c407420b10082c100c0e5515018480c4800c280f00c1006102c00e8100704ee003005034070600183c003448044a080e03803814212481203465421082d200744d0700d0746183c4004c1c094250040d204600450810101c640400d0b224801c2f807103a041d080005001640e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 383349631 1250 383348381 383348393
    0x60603042010030c02120406080c13090203010b04140a03110d0807020405010e0f07020106050604060f020109021009080709050606030a0e0717030a030b0402070c031119080a0c0b0c1009 81
    0x220710005055030151199002010300130b40710300e02c1c025000d80140e0030840107168104c4281e0707049800c00d582d040f4694480b80d11010440c1d000c3e00501c1d9030b4003200c01010404610702d000841c02090327142c3c112603503240f07070488601c0d240000020051180c034504108201042e00c50a0300b041e500012128402c00081920300408035210300c840c0250890b0070308000050301004485a240308814280f081b40c455a55004202c0c22942d10b0301900d54840000d0005000700e9106800314000300c0703000c2c0000162414507030001125141600f5144001419500c814000903500303200e8000204940c90040c400750a1410005443c0e0100504440d006591074048403000b0074100075030802000481c448103091900300600d1034507079029030b00c80b42c082800c207810070000b400c007842102d0b511900000c0c0b4245050841d92000030407660a12026407101940a45c21000e03049014004002c14070072009120201d03d61805005400e4103502c441780703100d41031095024002e000315461000442145002440351003500e460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 383350881 1250 383349631 383349683
    0x100506131e051203041e06140906210402010306060306140f0402130b250209070f03021c020c060a0504020d060b01090e04080c060906091e0f010e0d090501030506060304 74
    0x5641c0500807511516440d80c0101c000c0064540c1c40141c1c0407400c4e840703400f0b22070f48481b6109420001d055000e00e07000b96803401c4043c1207c0d560040080307141001e1004104116403954806444411026003803208541c0c0600c80c2c0720051000e0309040c010300785020005980300880d50704046c05810981c0d0724264655880d81241c45038085124040605a12201d0f03050040d0045004000c807001520304955105844844070142191b004282c1512030740d420104444c103c4070380e5180c2c0140750b000d0004201c0c42c45980922200300c250a0320042c2c403440d0072128145801c0c000741a50104134944810320001d0f03242ca030181c0f4a4541c01401c040344401010004940c91050743d448081c40007002c0d000d10040000c807030020591440d800d011180c0c1713603d0b480300d4252200710aa40950296100c901019500940840800411842c2c071056801d2a0b131003101c810f094030208485000550811500060720070340040301030780900402c1c0b03020042840c2c88008121544406000a402d108000304041030040d0f1003000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 383352131 1250 383350881 383350889
    0x31b031d070f05010513030c0b1b01050f070c02040b0a060c0312020c0c010c0507031a0906060102011b0e19080d0206071812330b0f090a05180d08100506131e 69
    0x3140034003a030b4884000300c082e082800d00c0d100082116140d01c2410ac8140206405402040014070094441c400d00303540100c04007100f281c04c561590700e1484160340b0b039942e4200900c05e5803940201c109003490024440d21641455480152040c08109a031420010301d001c0c0d4a0820700302240540c2070760030800e28003251507000a148510220f90b80c80c2e00e02042c9841400340281100310b42c034640320180103a00381e400c806141844880c50703c1c00c4020f514462180040327900809405510a0381c4403c1e084ac0c101c10b0f031500880d4440c0d1003003681c1d881c1186d041080720781c40349251400f00d004036416101c0e02c0c5d840d800c61082003940580c241c64482448040103541c024030506101c08005180071504004107444803661000d02c16144c0a0100c22a0600030a00301c600080144007040316900c0503d11801440b01038160340c602c41440300c03840d40541c01041103109112054441d12151300c0c0c50764003003140130010b17005280241010300452000c0c201c150624030559880d400092424010b02c0e1030540000e0b030030380c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 383353381 1250 383352131 383352143
    0x5090111070b1902150604051009110702031c0806060a050904050420030307170d09080c070f05100816140a03020301090f0203040f12031b031d070f0501051303 70
    0x40008454500b10014015103101d00c02c1503107000d0041400344c0c0c486030503074018407410741e101000451600e06580301075804241d520000e18415120000c4a0032218000381c44001e22000044036070641c0380030414924000e0054021388a20301c41900000d00b0980060074050007090702084010200f030140c000d80d0062400076104110307900c0c0078201001c62aa100c950160b04050b0710300110840d05000c800c4030303052500000c00142c9119204200c4a4503403141081301b84440c0e40340040300c0087c01c0c203c01003106c160a940206202ca007010314400c41d04400740d106c20720071449203001004440d01700420f5a40011041c0d040a6403c2d00c0000960341c00d8119042c80c010b400303001400c01a0144c05601843c142c1d50b00040400c40b100e401c1c03c40c1c2040344001c2d5009013280b515004107a0001d642010324941c148050319001c50502c402140d04044416861458004207071964640c174640071070489488400b01240d40100390142c5881400741a600c424080c0318100440040c0012100070803c00c403030001c507031005e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 383354631 1250 383353381 383353393
    0x90a14060418021902060601081803040b0f0904090c0e2d040204061509031b08070e0903040915080f010902010801060f140a080108210418090204050106030c031104030c050105090111 80
    0x4d00d000391035101c00c844290105182038042124491099440c909804824000310700d000e0030010644046e0300001c003004012082000a9004c64a83d0700594520300d21509900f00918281045c1c2900b050740200400c076072500c5501048210201d010248894820f442454a2a0707256800071030082c19090f00903188800c1c5030450066400e40c01915a07044900520010802d5000304110b800c40d4002c0c0c4c860607119a102001c107000c08054654401e411400040032645010f0b5a003610b402078030030031744030000c0c06600301c04200920017050004028034003000d4001c101116140d40045e14114040c02210100044156036240542c01031500e2182d14039100902c0391550303280b280050103100c09025558540c01a075192980381c2d4143e804014000c4003001c0150308050800c2c15018003070700c00002d1400150b032105020009030b1500d10030103001e031003030742d0740419030580210300a426241c0882d05011406420007041003c101194600c1082d1402464020390760808000100c036010b243d481e00751034a001c0d072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 383355881 1250 383354631 383354677
    0xc1b03030601032702060c070e01030602071703060a3506160c03020a1101120c08010305070f12060203070e030313060f050a0206060409021f0302090a1406041802 71
    0x1026600c641c009030b03000d0240d00301d032203800e491106203072000c040f41000d04c8051500502d0a24007030803404c0011000c4803043e0750380b07440c0740841040070382c01034036242d50025610382440709090712506d19920080301c0390700d5801c00e1004207035100d0b120b00c40c513090340c150769403003400300c1c05c103104550f04a02c0b16802c0c241c035440e17650b40059160842071fa0550060540c0504c00d0b103c15004400480d002909034014041904090315402a10440c1c03904582c100304250313101c1d2141c1400c034401e10f0301c000341c02d555094070382d030440c0380c0380d031034803580c1d0b0401d032402c1c012442d003007100a481020244180340c0c025000350701e80e04c52010554055881004050f4580000300380310b00a605000c030031000b03c030046d0f5201d440d5a0120b02e400d96983c4074810311400180c2044001402c542800d4008a01c0e40e48094441d203400c0c081c10829101c550200440c0000280e000107441d6100d16040420402501d40c00e100d4003101210100056007d101e0b501c200c0240d03070394407501103004110076130550f4a0b41d501658446028802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 383357131 1250 383355881 383355883
    0x30e030109062703050a1803020907170c0408101a220605040c0813030e03071d01140d02010804110927011a0609040608010f020301031203050c0904050c1b 68
    0x3c0d02d9803101d0311400c640d004450030541880c1c507000c00c641580b01d06144c1114401c007110550103074200b41c0c400510400c0000b0068544180061040c8e11542d1940c03c00c0c468000c440e03140301e80c0503000e000d007014244402c0c4050003000c181c66004d48a40c40c00015486020980303682c200130a800c0c11350f4010750035107440c0c100749680420058100c101d04c1c0c0030801a42c4400c01c2000320390745807804a000071a03010009001036440c0c4000d95290b406418021100510b600000746001b00c207800003c408400011103203851059020640e0250102034869045008a580171411f2028815806810001c040010409014a0480180310004c01034034000d040d2134800070099030301c1d8040340014000e500d04002c910752160103110f18003025141e81551074404042c501044030641000400a6200350b0b00c040000c4c0d68a0240702c1d00c030030860030f03a402503202d61441c100010070100500301c260905080c1010440203500d00c00444001f03100859000442e40c6070030300d600000c2e0040d81c9103840040030044804802d040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 383358381 1250 383357131 383357141
    0x1e050c030a062a09030206030a1b0f03060b0c0604060506120f0a0b0c0c060106030e0c0a030507060801060507050c040c090308070b062b0f030c0209011d010b091c030e03010906 77
    0x90342584400440741143c001907859142c4040c0b00f0020340c3e000d8050005240000040d0340200d00300c0c0740031803040c2c1c42d60b00d0310585188907601a80411a0358001d04040b54240c0181d10040030000c95950070039000018081c2c6841006100502c020b95072000907085503600203490002c034040c082100c140c40068100f040c2d544120720000d0358407203407020000e06c410003514200c6206120003005010140d1070103800360301614403051028290f018400000c4400d80318541600c000b540100000c05450b0718200b00a0007020040c0c1200c000c00008000c10720100324001200c0200d903509440c0002d5001c03140d8411514400d00d600010300b90702d000910441808503c800072401014222440c11600c20981c0030407607081070000c00c40806482680b03101c004513582c85070102c481402800c1c21407c030f030016030010700003400903000b900701075294040c0215007042d0107120502400f099420945440e061000181d120058880350240c4070304500c0002007014800c0401044115002e0000c1c0070304681c514124010380703 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 383359631 1250 383358381 383358401
    0xa0207030b010603020d1103190506010e040e0a060c050702060313020604150314100501020703061802030d090312050a090302130603080a09141009030b0c0c0a0b06100801031e050c030a06 82
    0x50906103030324030304010344003264022a880000b002005007109c06820250000500c000d0610600c5000c845079621a400383d10760091541019200e02c1d04180342010403a0304a202041c2044003c1c804040103032203c0c000c4a82008440c44000f208040f184005100e6200b990060800611042039802c00507805420000b00c00d03002c0c0c410b5510560303038401a901a001c81b8841d041c0140c0c0845410008600541c0c0040c038030215014019881c0340782600402d1a25500381d0a040026031011010402c2c81030444e60381220348803c0c5012464956809001407410040d400080d100c4c040c11509440046034680c014002182d01070030254903000701da08041d10050043c0710b00c00248500e080e080c0c1084c90311900e8a501e083d03440e124030a0450a6840c0c5014445000b440741b9a030341000c00c40c800d8501420000c044020703204544004562500e081407100e40300c00c1d002740205201c810740050000031104103e40700004017652540e410000d403400d09611f444500c034201601409044100414003030745400c46020a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 383360881 1250 383359631 383359657
    0x60204031e020102120912160608010e04020904031b1a061804050312040f0512030703180b0a0509030909011502071a070809010e271e0c0a0207030b01060302 69
    0x52014100d05081c0c498081000900503003141d060402d40040c01009099448009040820380301c99400c2c0c803070710b03120380034442001d07140d5421700070882a644040f04902400070403c07c4402410642d020a6000303001400060510109401e031032640380301420880d0185400085040c84920000c81548002c0c1050791321324021040340b0003168144450071035035401280c0c004000d52502100184216180304054012034100f00c15580070404640e080010392245145860400c1e034030304110002508481036007515007040b0070040d00e000c0218004144e9903a02c241102c90206003551010714030703410f40c819100030960082250001043e4080c03d621390058282480e000c54040d103444420300b00074842800d200e65041103003004821b001552b51401346c01c40c0f0b0010305181c0031603050040090a910703440303480441c2c0004c2c1c20083d1454040c1d208115070f00441b50b01c0381900c0c0c0f115171000c0f070005a1001842140f10980000d8404416031007044424002d41c0c01114514165031501c40040103507002e8041d038114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 383362131 1250 383360881 383360903
    0x501051c0317060f19060207050f010807030f060b160b090312070c0224030402150a0f080c0405041404030807090506091020030c06090601030f0b0c04090906020403 72
    0x1410014110512406415032030340004900c20810480b810a00148400d4011803a008030000d10740711400300440c40d84a0200d2508802d00309240240350105990081d4480c440c011002c10090344c120046030380000707107450301140c241621502403018103410b601803440e8120014182440080803440502664481c080f10100ba40b2007814055a90080e402e03140381e403e6000011415650080e4509010b0b80c1c4050411180c080d1107910f001c4154011100c5071030500d800008000451409110100700d0311046110305041192820f0024140342d4064104801e100500000c2a10140b03001c4c00d6030700408005005010200301348500c2490540d080c3e07000c802042c420070214035058016108202036800c09012581094051000c001c6842c0c802c8a990b0300744510691048040d6041c0a060402c640f0048000e6036120310a4003124a0001d00504002036500044014000a80550101c03112242c200f1050f20451722241c0c1e099141d4420781c2e000c11080d91420083c0d0082220580207001164050450054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 383363381 1250 383362131 383362159
    0x14010902031c0e040e062403100e0d02070609090c1101181a09030927041b14330a17010506090112182a0f12020105030406020f0706050105 61
    0x1041e036060410181039a0880ca0026880029104207801e07c02c030000140f04040702c0200110303062800d5105001c200c0e5445e6074074103885460412800900d0185807000b0309541e45401c800600e00b4201d4001e80301c40760740340c03d090711446110355000d134186815480200841c0c0030b000c05c00340f60a854441e0071a41d01854448190344489840d1a043c4140a480042c47c030340b01c0404108450f1810300c400201100300301800c241140d040030708800744918884d0f50120581d5100c44664100b4455984c001403021503070f110946840d031210307090000801130000000d0055007981c00e0040d0794000d844513500413500b01141c9800c1d5035038030003100c684c28100c0030344a0325184d80707070301c24404641302c0c60b101c190201e0b020183d0300d40e005c81286e103c503003400c00100c8005619000c660b00d100311402d0004030310b40c28022844481c501c5400f202030032030051400908003081d251810030180c0d80000300507800b82c14041c01000003820301060341c048800d40e2030804a5540da421003031030480001e020a00035207016107040d2039080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 383364631 1250 383363381 383363389
    0x10c02190305070611070501140a1a1804051e010203010614040e240307091a0f090a0f060905040f15020a200c030303040b0a0b100c14010902031c0e 65
    0x40560555181843c11140303458600160501000450700040e04010341c10224030f080c482c0b9090036040320f500704081d040002005040c2c4a000c000c400e607480071141440e03015507601c0f030500c906840d1100e2206140d03580d820114149004164156481e0711555080f008002c1e041d030095060b02c3c12910b030142c91000b00030301e21201d8040ca00509103100c64240100310039550402a1034840c40c43d211404e1600b81e014000b10782041e00582c00b1a40c0c2644901080e2402d44500407410035a61065540c80740c10034045002610791800a05164030140c0e603110b07100c2c16141280c102c5806002d54200a0000b4102403802c6804207041c50010703203010381d8088461007041140d0088038290305540d82c685207023035900745500d8a020440c2241c0b600610842d001000b181d00c0600103544110700a401d402810310740042d64209131000902107d10070000c80008114558101c0e16440c40c0d603800c5414803c01c40c42800d5140d005101030100a0f50600c41c81402c50740c0070500c9580300140b00036503600c005000d02a84144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 383365881 1250 383364631 383364673
    0x80709091506050711040c0f0912020a0501050a11150603060a060b040614040305010f0209090702150f07020a020306040b090c090606040311031e010b010806101709070314010c02 78
    0x600720040e559181040454440c0010300221070265082c19810910400014200d071180d0090b80003184a0042070007a054000c800980200588070305825071030380ba5800100070144600403141803040c04108100142d2003500403c00c5000300c0d0044500348050b1003000b194225080361402d100e4810040040d002500901880084508402445003040d0403c24250341107040d00d68441c2240600384400000f0071400d00680810303c40c010350050350703055050248a1408002001001507500900c0104000003007400d90176400503155200500c00c1d00c40230b03001c0741404004100658184115400d1005101400351424000d2500000b02c07014803510f01d0911100030b40c12140c1700d40c481f009000810114004030083e004200f0010141e8119050201d5100c480600d411610a5103039994803500b451540c201d5021908528225821061142c1e61500242031080074000d46035080c10920101d12005020800040655800300c003009901c4400500e0500901c80d03c4001001486180607040e600c030207039085 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 383367131 1250 383365881 383365901
    0xc0915020d0807080a0207060f0203100e010803031f080d1d040c02030706050a14040507050108070c08090f010e04110c0c010e090c030601050405060a0f080c0c03070b040813030308070909 82
    0x2882d00ba030381c807018280c4040d04002c109802d000e408100400004807540724289040d1810070b0016164148400b50740000b0071aa0018400201058018010b9000c008156a8030802640c0d0300c1c3e6940101002c04800d4041035880240d1511a4464089455404c01081c1c504c20907000741d00c8203090006401c00c400e80b280c510701480503800400400c40460700c40d810240e801204588080ba001d0428429900003030320480b800da806801800050106682c4451800c0d006080d03441e1054240e056511503803120300c50f0a89041c45103482c00c0d400f8083d42d00620f661b00c0d24684c0200200321120082c1c0d80030341182d0210f00020b01600030710704204c06a60164821000c1e020010744186d0343e036a612006034480703030300141195051100074000001e60340d0300e9a0080c0150001543d900061a4181c1800380003421b0107048900318a40901400c0c07903880c800015100c0d850b07040394071803000340c5441c103280500d4401c080c0210f2940044400c08800d050b040301e8000d000c1c880d140e5504034240c1d640e00c0070100f01c50003240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 383368381 1250 383367131 383367137
    0x3160803030402090a0c0f051b060f09060106081519080304060c0506060915061602060301030303020c0d0c050309060a090506040306090b010b07080d0b0f0301050a0b120c061218010c0915020d 84
    0xc014000e110308081c11448002c4051894504071342000a40340c0ad5003100c142a40c038541c1010041c00b10014000e1500500305401c009490341408002141126070081a05000d4091070f02403041405064050000501c5c4c00000c1e250b5542c0c891400400000d1144000e88051181c04003003440c5040020907c0e00c0b6005440200a03018030580c1003050340e60100c0810290307d64080b00460140e03840600450003580b00b0384005a03a140480311441c140188003c0718002c0c0229600d240001c508080708603078414004584080d9070700080c09003a00d800010707400ca5608903030041804010012180d02002005000d8280c0e040303241c1e40d41200b17000910810400422050050000303100f00d000302d8008103041680200207607036003501c3e1004242159001c0740c04491041d1148480704c40350804058241511420750050059144000040b550911513082d031030790046441d00018070041c1042c44042c00c22081400244410600410020140e000602884012174001001030703036400e000096480305401075803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 383369631 1250 383368381 383368397
    0x2a031406090f25050712030911060a2f010b032a0d062306030304050d2003070303020604020f1e010e1306030303090b0c0f160203160803030402090a0c 66
    0x54949903030030b42c0c060140c0078003a096944018140100c0034441c81c003c3c0c255a01c1c5612007000b070800011002241254805161900f203000d00800c2c892a005c00399000103941150b43c0d0031100c8400c980d5201c003004401510582034030400b02146001c101d8061002d0700400034041000d2030020140c9540d50180c840651f003442a40301c00c025500180b00d081a02402888091007000300c0d2980c00643c0d03a030b01c8401c2035410180001c20481c0d0f052601c41c03a001102a0003c1d41000e00340f20100783d0b00c04890001904008000204034100308581d4020013500402800780c0300041da6914010350740c1d00303058038200c1c4202c0c2403140b80c0c040d50900b12810003d4507800d182c0300c2d1003a048500151b40312031264007010340003843d045420211030b42c540075020003184030b640c000600001508115443d100050105540c407c4100002c02180070790900b6140c01c003c0107901c500300805207100107483c0541c1803080700003503902c1c0d02d80080e0045020026510841c000d403007286156941801e0441110f50300d07404280410106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 383370881 1250 383369631 383369641
    0x30f03030c04150212030403170709083f0406030b010f1d0f12030d0605030102031003031409100e0118030203030f0f0417240f0412032a03140609 64
    0x1040d02c0101e40c41c2d40d401640c208485e0440315400e50b1344101d0f01540460402d0320301700c0014020480203a07101d41c00786882e44038113007031030711550300c0d8004c5440c1c2e410720000c1d403065007581c040c09070306080c00c0c003c0e14116004c8000caa080316141ca03400921540c030110345840a03608072940141d02800001c000e80d618044000c0d5003d50754004400c02c08180741e00310741c02514031055500c41001c0c070801c1c200c54000542c0c4660095000c0c0c07050b07505541145019900501c1801300346000b842c2c0036000d403a0325003451100240c0075030011400340640c40506034012040c0c1d2035060b401d900000e5040100d90203907201c01001da401100400c03161040d12000390954803c01003000519031b184042c182c09516603043c645002c1e40c510500210703800000c0c1c88841e039041210b04240a113042144203100b07841c1e14461700414a080d000c5200c8803040104003030b00040a9a804002240c826405141032082c00840c6401e80801103d907034196180280c0c918002c07078076050b4220803c5d500a8452442800014485000d41e560 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 383372131 1250 383370881 383370899
    0x5030a0807060b041e0b040b0603040204020a0c0812010e071701030305030907030501061e05010c050a0303020306040912080121110d030e03070e0406180203061501180b0405030f03030c04 82
    0x19005a562903500c0b20056a04e0f915030185202c07200500e181011241200d128041c01c4801e10f20702e45100358904550000030361501c0c0c0590740e0194048a005885480c000d100381c039403c1e1914401030040b0800500e0a9050301250341d583c0c165943e10b54880c10981c0c4092081d00e030119805d014182d070802d404010400217100d03000640c1d008144600352600c166880d81e1b80d600b0b460542d00f05d4802c00440039a0046040041038003540141030910700500f0f4802580c5800ea1a520f0300d60015041640000009071252219080703860203a80c0080c2c1ca981d90a244080142681e20a001c0d03104141c4e0000ca01018410414501d418619040550030101d00500c0e010003915421414040f01441b03e094800006590203104c101c00801030180d14803a03619191500344111900b1840c1c009000802c03e080e4409620005400d0f43d025040e05403094200080c0b40051b2884188041c080c1800028403a000c81c000c1d5202026100300c0d04150300b180d0065015540c920740300e00086445003011041071008111080c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 383373381 1250 383372131 383372137
    0x607230405060304230a0c080f1f0c05090d1a01060201110405010c02120102030702060106080603070f0306200a020f060a0501030b0f070309080d0902190f050103410a0605030a08 78
    0x26107003507080170140c003c0c1c150b03070820016142c2540c014031407040130800720000748040b02c1c00614a9018068180c001c60840a0940d07016040a500c982c1e2400713086815400fa0048884100000f040e0301c540c2e020310710b01840e0b00209c240b0801c00050303c0300c00000c0c5c020300501440740a000251010341c140784c01c20004581e180001c860517a40004144288030003900203200a500525403a8094800741d8144103024124080c086c0541e4080d038402441009a80f48150183d82600e03801303400071900a00e010790094046c000e8941070400004001012110680c00041e8074204000c95401d03181207980d1700003510100c490034400905034104c40710000d106d0240c40031722142d210609081c001021412625101c9a94000d0242802e440340c2c1c1d0b0300d20b2030961071708003500991928117000d5443c8007424504404040c0d02c003442100c0c149901c0302002c42e104d00e094842102e00300003a4034903102004406110744200d0390608040140401c0d40408607007070452134000c020544801038010700d15641a82d4452505074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 383374631 1250 383373381 383373413
    0x308060d060609110a090f081e01021b030301050102150115050c0a0503070605370b010e1c0605061806010c03200a0605180c04020f0c0607230405060304 67
    0x30b03921540420440308600c03440050b00c10040304143c4804a100b0090003501c110340000f030340d00314411030070040c0c0c05c4002030003140200d41c29541c4030700310842061325000e0f000d649400746034044000050b54030f285000010718129402603007140e14500800007605841d000038003441c0c2813050608980c0c5c210a0080004103141d00252003113030780c28603041e12803a0a6400099084800f81c2c1c40d9801c0c411100340000307224061070080b88000c0c04500c0c0d003c0034101c558183c0000041400e03281c02014030325070301807070fa8002000d402a140110104e04065800602010344000b118410b142c030b0007181d05400c1070040941c01b145c650340300c21103607100c1d07a005664440d8807035011020052450114441050b01c41d8848882803411001822003251504d00a4140e40c0000c00e5025244a59070180c1d00315400003070750781c030f11480c107480060340d8000d2034461640718800c030050744407640300301304c180032001398015404400001c00c1c0311200030324a4144c2d80c01d43c0310320540c03003200d500203c00e00100d00071480d560300025540e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 383375881 1250 383374631 383374643
    0xd08070f03020c0a0b0304061b1b05031e0d15050a0306050a060f090e0f0d091403010f0c08010f0e0c0307030b1305070f02070e010b04060c0618140c0405040308060d 72
    0x1010003000580c03150221781042e00141000700074081044018002c44034117203000c40036241c0710300720140e0041c800c09140081c12518250062800d0520105000720740000d4907200c032020a40301c00d03424108255124020fa80345051500c03a0318401285442003403000c3e504c0040c03080d5980ba1450325810050000a0011045103a5910002400d1240c589040c001130400d130901299466003120140d0401e610000841800e802ca02c1c00008075590000107102980d03003003810003441031030074004a401845018400e01c2c0003481c20201c402d404c0c1e04820664103c4d00d50080e41c0000710b4841c5064408458180c5e0388146451042c00070690050080d0880903410002404821080400e0300030041600d00a666940c04a2840e08003420b8165040c0440005404a039011000741c3d4907080301d0074850300c038501c14002008102c150341801c11003e500405481446030700c0c18504445942442d40100702d041050030401d11a19070110050705060286c140310300c1d0142c44001107503446400f403103c0c2000b10441140c41c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 383377131 1250 383375881 383375893
    0x1f0803040305070e0c0426210301091d1b1f1202090303070609030e0f09060d030e2d041d0a06021803100203060301060e150609150a0807020105060d08070f0302 70
    0x401541c058500d240e1440d04440ba00480000e0450b0342c06c01e941184011030300d101c031205000300740e0300d50421079046452021001488054690070806802d090700340e201003a0041c56420341c1d0580e0301010510890f1010ed40f414100802140201c091001d4030402c0400304003140c039000c2000c44154007070b118a55001c2c003502d03e4803070156900030850754082c07003c8000c118803201c03201c1c039410071101c00304801c101998540300d10300741440062000c1200d004010100107540034101416141c1d60340f441c405a80400110448a00484001c4040308101003500e010ba032500030502c0c0e40d000300c0007a5848a0056102401e44080c00d0388611005c0d5014a081600c1c140c11300d4200c56161b1005c102d4406a1020300200503101d0410741c1c1014291540c2d42c0c010072081c5031140511618540c40140a44107120840d951a6a0301491005c119000c5000031200c3e0407241c089480107150350880744c041c2c40354110340e0081005540d203078104000e40c0140500a8005102405034100044620b49401c00d514044e004840d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 383378381 1250 383377131 383377139
    0x9050f010915120b01020307030c1b030b0109020307020c180f07051911070503030405152b020304030e03010e0d050715020c0304060201050901060e0609060d08031f0803040305070e0c04 81
    0x928030410051400089940845803070020152280302c0c0342d44c409101a6107000c002d601c00502124504078003621101c028014008040350802c019401150301100d02600e560351514400000e40003255000058052001099040d1030401030055443c042540c8c43c44036034441100803c0c1c03e85c4000c1881c03050210401443c610742c4988105001201941d039240300c03c2551110101e420050346611490103544248400c1c09103950300b5011140c441da131900c0c0b05440744a0340307911744d4602c18221540d40c1d80c80380036a0050070785400c5c0c0d001584660302075158480300340f4001050500300e03104001510440d030021401c01c00300d94490401082904d0140711851001384a094800c8200c3c1c0c801e4104c882203070300001d8108040758081c06040da000d007403030000f0000d140c80c01a0f01001e420380201003d03c2104810001102590f81c040c0b81d80c19079810044150300d0340f6040124411040e8032900b82d0550b0864500d0020300210000100c40c00d480d8003801507c419440d0079580380c0c5c9244003518032495080c0601000c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 383379631 1250 383378381 383378399
    0xb0109050c12041b080f0705040e07150e1f110a0302030f130f15180810020d09060501031b05040e15130f030206010e0c0a020a03080a06120c060f0f09050f0109 70
    0x10050400c110242080c1006c0d40303459854001954000ca000d5070501c0140142110041000030899200c4644100007460f460000c40e0705803c6104410741c0b040c00081a28000b0b5000c400100d50307052241c48822502440040003a0b81c6c158400c801001a401000350448011820010340510400b0702c59044006490b21010305030000d194112000140550120040c0681d000c200032178101da01e5240e92104130300b8076100305d440307080030070f03a901950303800040c02c1802203903651190740003580118080016503100d150089640c4c1407a804007005501c01e20300031905113000d20408505030b140400900494407000d1150032103580c010b14041070800700c01841004255105c3e0424041480b03a0f004c2c190070360410540114550025009034802c800900034140016000299a01403d070036050461003960340203681000b42c4030761703000000c480328400108020041c941183c4030a45005448150060901c0b4900f00d8810200208010002e100c01c1401c20490804054013420b02c1410f00d04007100e2500d0745811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 383380881 1250 383379631 383379683
    0x5010501051903150503060421090f06081801051f080f030d05090f06090a2108070309061503030914010c2003240603010501051023070204060f030b0109050c1204 71
    0x43d240094803107401d40654114180040b080c4004ac24440001070401c00700394000038103809000203000300c00d0003007400b9082480004406600e46002403280345060341000405020b1148042d40114490f00302081c1020f020500302c00d4404040015400e2080d291540400b03084087c080040b503004026030784000c014103101d154800c4c0c1c25400107108015880ca805460b040c4034a1300d184081c0c051207440c0c20307126070140d0041d0700320784180350101e0b4002060800000400384000c00002c03611600c0360000400d030f040703092001201d400c440d0488001e0311250041da444402600300512803401503044170b141c81c041c00d8000c0c407603100243c2150010a0802c0400040a05100d5921103895a00080018030311707003406500d001d0300c0203070f640c0300380b0300030082014003a141200d031414410720009180e042c24420b0755080c2d499094009006120301d036a140c07280c0b55982c41c1400281e51801c1c1e10300010a007410300e405103c0c010320450b40ea003407805581454400c02c2e1500130700100c55902c51001d121803400003140e82 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 383382131 1250 383380881 383380883
    0xd030f020f03041b09050709060e0a05041a090108010c08010302101404060e030d0c020102030d24030f0b09060402060d0b030c1305070e0114030612030409050108060703050105010519031505030604 86
    0x6043c051300104452404c148407207a110540c100d0800007008081c1c0c1e401803400c802c039070603070030188403190358000000c90000c45904500c4c0c0081c42c0680368484d000301604144024030f0103070740140080e40c032100c0c43c81c242c40c00d8207500c8002c14401401000107080c680c5d000082044c83d481c007201144411503290700113600ca40c0c03000c00095950b29620180d071034140300c409258811820206006442a40041c0d100d00031041580007965844d4900c0700840700d0042541ca00e6590383c002c0c4101c894481c5450b03440210060021345d1554040300008400074400615140201e030001e0002c1d080c8040e4902c9032010f402c0d28030340346425000c2d04902030100e44588000544080380d4000101d441e1a10030360003800788a081c0e844604202600e0300130281c1c0c04240e41120f0300100203070b40e148070020500c08020b107548a1a4072a00c0c90514000c000900040080345590240c0c89035501030056981ea940111200e00172200d20f08440c00c07498420117007150081d80000c15901c01e400500802941c0d03140000d00344081114 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 383383381 1250 383382131 383382143
    0x6030a08090d051b010e040513060506130212070906170a09030522050102010c0203041a0c0a0f05060603010b011718071205280c0e13120e0307060f020d030f020f0304 73
    0x11300003d103617000300340c407100d9000c10340e000c21252529031542d0aa002030072401a00095480c03020601c51346171a081c5500c0008440d10640d6151100c100c0300e04800d0382110300310006907400b007000c01c003640700c0e0f109581c8403981d10010381000d0702d4403100c9500400c0e80345000c42c14002d0801c103000c0106604c40e4021411014450301c091081e103400006825034070804e0103002150010001071240301c5810f814038404004040089881e400012655450210040c0d0b019081c20511502d5004102d000200036204000c160000e000b910510b00c010355104a0070082c5c00b403031062240000314110302c0808010302c00448036084901d40f9544140200c844401b0b82811b540a0300686d0070700f000302c4135001030078010003280c09200404c02c1710343c0c407103140101c0b140c0648140c1304001e10100d41148206030024410304d800a54040c03414a500d10701419206412a0950090090500c00034005026620385820010681c0240071014950b13202140208032664102003e10b41c01d0004c0144000200099442640b01d24 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 383384631 1250 383383381 383383423
    0xb0c0c09010905040213421406041725090e01050105090430090305061b040b0c01090c0f05030c01030903120e0703080f0c25030b0711060a051501020606030a08090d05 73
    0x1400381581002283c200b000140c3c0e408d11008480d450388012101100e5038504545070a10342801d5a82c1402024003c540400400a084022240c0000f5a040880300803403030400c40010003811031030984a007485890790002d507900009021030807210074407e4003801c00300f0000815050006c0d5228804c418204603001034000b11040c41046002c2000a411203080042c5000401c49450071042e43c0c0700e58000e00f92900e0010481c01c0d02c00d80d09421212215600c42450740e20182c0341d0303540d04500102c51041501c244628807074018594040d2003200075450701640c42c0c100c3c0c14202c151000280081e41c01e00019446040400000306141d0307005400c0c8130304042d1003160794204000b08103142241050318a00c0d4104803a802c2c400300500510740d1012030b94000110b403400c2d0b84036002500c100308a0030510000d8011402000300c01c044d2944030511480507035050300c070303181d07440e400490b0350314011070f103980d01a03010340020408030b031800c0007800e00140001c0c2450341c0d04c2c45030b076039003030510780c00b80d900d4040040c0007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 383385881 1250 383384631 383384741
    0x51008091527012f030403050c120d15140f060306180c09040c020f100507050405030109060903020706090f05090a0902030d2102121b040b0c0c09010905040213 70
    0x11503084030000b110641e4410b41009000440344c1d50b20000d003004041c0100000ca800c0d03410390034441c403450103c1c85a00580c6484000f009074010780807038001841c0400540c9004500c0901d00c140c110344103031004d403000d0950045002401041d42c0041c01455012910088440b801c18880d4145882141c400d100300e030b01c0703070b10540510059540d00a10750082d5004403008000c1c54500092100c00403014000c04201529241c2065171176214a4118a82550a0116038000d001458000b03055652281d42150440c0355241e600f2140440180615856038650b45001c03c4240b5041ca201d9812446880300041c0c40b000c41e07400a4030740280c00841c07502240c4001c4284e41c00c0704511400c0e0b21004c0000d03405601d843c10000345400c424100501c501002507250540d200070039000d009603000352042981c00c0f076881c12442003007a901ca8101c5505c80c03095000c0703000854503002500030706001c0c2d54007601c00ca5411034910081c00190070011400c5007820070010000307040b0500916007801f04036a28000303500e85120707 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 383387131 1250 383385881 383385911
    0xc0f2d1e03020a060b010c080d0c120b06070303021c1e2003010504230c1b0102093703030915020c010e0112060b031005100809152701 59
    0x2032026040e0000a00026600880e030080303520800241d0000e4001050001000180c0701e0344801907000c0c009060200b564000754103035902c41805680c00c0e46a40d13103884261b9040c1c1d002d581c6072002c1c450300020300340b04240019000342c000c0d0284411610f000000d4403210b050143c00c5546036100c2c030a080c1002400f214a41c1d4140c032500c801c904074912110134003044a0148010740c401889481e00956480c503180e42c0b101c0c02151250900034401503104800c4c10f02c0000c0d00c0e26030f0401d0b0742200c03064034074aa4082060f20144211407a10304c01401c01840d48524402c080f51001c2c040c00d00c48500300c8060b10851100c142c1d00e01315000b5511039280d0312009804c01b40070741420b404494405041d5070106140315805da030407c07000541a0800d180c03000b164030402090002401059201ba081030390003100b4070044071040120750b0159607041c0c84001c10803807400f1045070610000d40d564801c541010300210b064050078002a603104050a241c4000d400c02d41000d580803605c2021070407100c0e55101c55021010403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 383388381 1250 383387131 383387153
    0x3090705090c09010e0d05240106090b030f01090e0a080c070e18210d0e0a0515011508071b05060a0b03120919050d0b0702120a0c0f2d 59
    0x80d411448900f844a0392002814481101011510a079214030100e0204541040030202070fa030802004203100210030340058070b92100380211030101e8040340011410301c01c0300055074440e054407055544264078290018005003090107403651140a401c0748a404030707290000801e000d4085800410701541b820021912a103000f41101c00552504040490303128000510540e190b4000d15030340d0200e075000b03604210b147c42080380e10720400313041c051030000d28080811880c001c1401076065889002c01200c0c0304003084801d01406014170200e44282950911556106902100d00c0c2088101580240010300800d98108000c492030390020042001c4582c07207010760002400c0030f9000306407614022403104950300607410b44c41c0c0a50300d41040964207102a4500d403000b0540541144428002c40c200034564001c116184005441281541308102d90118100e52400c034030303940e45040c2c1074651b50750800d21400844080c0c0c0c401d000313100c60b00b44008080f031109016001c03040a08008150328070700420b56807 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 383389631 1250 383388381 383388391
    0x2060a0f0e03030906220f03030b0105130f05100c030c060c051b0c0a06020c0105090616021005030403020c010c020d081606050a0614030705060906070c03170a17090c0409060e030309070509 83
    0x71b960102d4440014032400340407003030154141000300c0e203207580c0c100484071806000001003003a0452840010250440e40380c4000f510029076884660709101c01040c8c0d4406140ba500800041440190501240082d03101105a880518229140401c400c0e44100555045140944c02d80c00520000f061840c154007442c00038041c0d400640300c40505000041d00c03a0250b2510117004000c0060707078840720401c2d20041d80080343c2c0100700340004444424010003a81085400301c000d8032419001c0040380d1b010750f001e2078140c2d0780280003181c0300c2c01c00e0b40e440c0b020341c001c1c520000803203901420b8000018000c0c000d00c3d10030b001e0500000340040c41c0140c2001c200f00001d585c07a0007600101000d001c151100c500315088070300c056070002d60314049480d194401d2005a031021348004858800c25140740712501c010100d240b03141d038541c2e0b4010a10340080c0300c0e2810548060351568400018075100d818181c115042031400380c100000e0880079441c02d24110f030300880e010245500400c000703003c1417400440c40e581103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 383390881 1250 383389631 383389681
    0x5101d0109080d11070b0a0309031404140103090501181b05040504110909030409020c01410c0c1603020909030406020631060e01050109020a02060a0f0e03030906 71
    0x1514040c2c0035034554039184020400c0002c0469500248841041010018401582d03860340c0c0d14076601c401002000618001c40000f41d8240001d8100f40703c0d0000c0d1000d0b00e000000103c0f40400c80340040d0000c240340c000c22519035480310100c401013100006561092401441c51a03080e100d9403a4140d80600c0310340119100d54540420710010440744d0034082d8100809485848071a200e00c1113031403440c0900e03407040807114000100141c3e065019080655044107070b8400d5003c29502011031a005400750b44008049034240143c0304500b20320485640d0042d07007001c141e40c5815410b4201a00704076224118a002060010b000c00460804400065001c1c0c00c42000d9410241880002515144003401d926030091024050080500787e001012604003c0c0d0314440c0002c01c184d2a00c0c20181014004140f030315440c013400044c44030100c0c002c4901224143d8054036156032450400c40042403200045c0e04026a142e24100581c2410002035004841e000001d001c5440e1600181c10011a40b00b031070106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 383392131 1250 383390881 383390897
    0xe1b18060c060a20030a0905030f0d060e0a090b0a09230a050c03030301031e061b20030c0705041d0601061101240902070303151e0b0f0f030405030405101d01 69
    0x5030138401d5a820810240c1c4c085000c44a504141e455030040103013031105140c000801c1c0e004404654030160480c0c0020100941a131b9401407100102e40c00780c280508551141030010b801c0c0c1000307a004070f071020b01c1100e500303490381080032245202040da5001d0040070780c855085081800742c20407108500200403802585198150398a9540402c90a00c903d4884110300740c4010030010f0540202d04030b0440c01c030700041c400c071203828001c00300910394440000e00b6480c1000b512049074007004071242d400c0b81070001c016503032401c0c00f400018403010610344e59048100b42c0141343c921080c05190300902d144e0b50f0b0b9500c010b07200250282100e1080507000141182e08404000301621103a850b421128500780041c1c503145641416405400d0344a0400c03090703010345401241e120400b10740c00305240120703869208400d888504c050f019224511180d00c240f4002d200e080f17882c1d4002c1c801164490712171390a49052959880104403080c074050024404114100e98240c400e04880908606809003440c0c0848 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 383393381 1250 383392131 383392181
    0x12070203120a050706050a0603110d080301120602070c09020306090c0306011e051e0a0207060203120622020406050712020c130f0e03041503060e1b18060c060a 70
    0x10765008040880440c2100c0811202c11240c0208243e50082e60403200c20b2100d4079100f44208000c10644c0030072214101510a410b0450500d945840351840d07004090502c2d41e4208603049c980c01a50302c00c1121b07165020400c2e500000c522007640d100421074a400540c881c100030080102000d0300624584a600040c420040c9603a4001403002030740b0b0449590a911145504003111036100c0c02801c817214000e2640b440015030351050090810001d150301740c4248580b40d041c00c980381e100d41c0d8446020103080401080c0780d490109101a03203004552080e81c0e824085690383c0e02641c1080c1d21243c00b02c4d1300868000c040c015480181c1d07a0880d00e502c06044044801d6000811a0b62005051808a030f80e507c070180a05001b0b51120641914840071244c84a96414218001e80c01660320440000c0c1000000140280b00c103030128000c600e401600e001c1d49060190282d0260065143c22000c4600055042060340f100d5008060400c1e1000c0601128501040b50308242c41644031442d00075204a01814 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 383394631 1250 383393381 383393383
    0x3506010807050c0a0201030207060e150103021e011d010203190210110306030a061a04090809040608390d050d02060c0406050403141507080103060b09101815080106060212070203 78
    0x2d11303000d509080050729441b903414603500a160403411442144102101e00c01c600c41310542c468101c91080350709001401140c040fa009001112804c58040fa0004604825a40c0007102003080c0f2101807040f00e08008413817589c800094900300c02000580c10148a0202c10703005070140b6006c404041128074510b040c0000800d40d40c1050f01380207007900d40e42c0c6141c986c03150900001c04245420080041c048000581050b002b681d000258092165181550019400c500814000c22030043c03200300315107111100c1514200900e42107911600b02d043c24443d11442e5940011103a0741a000340000d00c201c145016010303281000c05070451006840501041012a5000084405503680001d82000a4040c0000300c4e2800303800b150b10811910b003040030009499030103100d15049038000c074000c0c0000f104c1e41091160b02d007400c2e2a41d408210528005004c64065803900c200c5202c4003040010795a21b4103080c10f161071302540c201e03000c2651201c004001c0c0b00d0341080560000c4002c115418500f108950000e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 383395881 1250 383394631 383394643
    0x1e06030c1205090c06180103050f0412051602150405090f09120d0609050106031b0503090a03030b0f2e0e030d030903090e15180f04033506010807050c 66
    0x7075161621000018075030340c004d018904600b480a04030a80750080e054024140c840c40f01c2034180007038a400700040810740715042d4280103035045141d440040d0300e0124100c6540d8080c40070300318804003000c0000b0050300d41074030542c104140259000d8a07642400c00700414500043d00583c050071528082c05005034010403100c0c1b5000b010841140d4070100034803180090700e256071010030030368500740c0000f50154160b00980c0e0003aa0015407000201e012040030b80d6907001c1501e1000180e40003103d0200024041d03800030209060091001d001c0c00d00c43c0c2c0001c0c0880d5001242184240d031000014a0a0022018a500404010306000501d825131002003541c4180003000f410800d611800310b071080c140550604000340040300c60a40345450302e550607420020084013018000c0720f142070b100413203444000100703024400e082030410043c1c4076900c3c00c5421401030300200c5e09504284810040101070440115580c19002500000514088002500c0640d00031710003024050100305030f405243c801300d21 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 383397131 1250 383395881 383395907
    0x9020a21020a0e06210a140a052203120b060d0509011b0306080307060908120114030c090c1b0309130b0406060203130b0a020c060c160611070308070204090c1e06030c 73
    0x44c845d0300341c1c4d40c18a40400380140d41b1494550902e080103114066000c0e070001803181e41151030b230811061907510031145940b0901c4010b80011004840100e4464094004200f82000203000c01d040c40043e45815046034400d4980f04144d80d52160014040e8460074048014290941010007003145013a84490b280d1190303580090a05079240b5014080111110a41e0724841480304091025078654040b81e400c0302c10200143d1080c0f1620070407807a1850300c508003500c01e12440241d9401e00d42890074003120400c0c1e03110b00c0e8519002c20300859403281c5070001ca03c003c1c0740061740080303080541c21050001700d4000f50094400c54104100c1c10700c541e210102c444044540d0180710b90f0303444106010807070a00e45a03044056001c40000cc006d00c480303400041641485549081b4008400e5541c1c00c1561480010100003082da000b0300c3c404c2000c02c5805002d0001680084c0c008a4429800e5a03024403103d083e4000a4809400086000b030320416414075001030030b41420704000004905c1d1000c0c040380304c4241 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 383398381 1250 383397131 383397187
    0x905091c180f05031b04060f030b010f08062203020109050d030207060f0e1207050f03030a020a020c0d170f0f03130c120b0402040b010e1201020418021309020a21020a0e06 75
    0x2400300701c0c6d8440f83d00034801441c0c84d8003001d800303d4685c504030104990a101c3e9034010035000802084002c40440c3c2c881c0a004401442d4045252a400e10f58110b106081d0a80070355503114044004540705101e0b04246044540d401030b40c03403c1700d02c0d1030307001c440f902d80f0440506854003140748400d420000d4a2500040c0c19051161212060700d82140350070f40819003d40d00380030100c01c0c0700754a0b240e0b8003d807000c00380ea80c00f519049045102400b20341c5c50420f2000d0300044c12150290008286200201808a644811107192051004190703240340e00985940b80c10109000d0020705000010302c01c00040d01c1e400c050481c8100e81c64a60304e10083c40a00068800d82c0d880340410503681c0640c0804031f0120000d010103080f0942064018000e4005100780e20300444030102e0b1140c400344620898044000d9a02840d43e810304041c00c15000750041d41c00001400080000552400a9096403612210040d28007583d101003a0b540203001840721030005000748020301100c52009100700a11403000c0f2014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 383399631 1250 383398381 383398423
    0x10060f08030328090b0a06060e03100213090501030c05040b03190204050601090302030a0c1410090b0f0705030d020409141611190b012d0905091c180f0503 68
    0x1004444000e25103d040400d42071808500d01d0401450040d614403500783c2013420440507540f54402e681d20301081c221250b254109140300b00f040e2002d0344c050074034440001810146181c844480504030f810a0300283d40a400702e140801052516001c1c0207081d010507405045000c1011410840c944d0350950024417903622100021704c1c2344d115640120055030000c00b00ca4008030be03030800c114100081c0c0580d00b500181100800c00c10701340314219010384401a5141403c240c607100d0741807a00d410580e1921020380c4200580c2d40071a5042028040c0009015401651280b804036580c04940100c0d030f00b40d00181184d4104040005c1198402c414074102e803d0064200c4090349005007006516040b170207110a105208400744032004401c64181d51404290a0026034000b00142914400340c2103051200510b8806208103031091300000c4d00310b0311702022206108418090103211140f141c0c0e908001814030141c8a070202100c180110040080c64210b2483d20304141c04240c8401010010010401c1c0301d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 383400881 1250 383399631 383399671
    0x313020612070c11010e0f010e030c0a061706010c082b06141e0913110307030614100e010501200f0312150306041202160810060f080303 60
    0x500304562001c1024080000e0600d4482d80141ca00b40510300d0503186010584015002940a162030f508100001031442e6031942145004580b44601c1c2c055068060140d60120000c0d5241e541c80d207400742c5401c0d12000c2c10380c20003004100c04040c0050609041007200b481c82d00103e203420045941c8600c201e130700d000d0f200c00c110251500c46408070904051192a0030300000700c011f900e6003000d080e217204441d5070040e541004007041003070004c05803095011010f03401041c91800c10190001003944100c1c209030b070003030351080000e0424480d40c5c0140e417500d80700c912140e04015061941c90388401c803440e002000d241403020000c1000014040e0b941030140000031302d10301c400c0890740ca07000328901d0400c80720344820300d0304459201c0d003024400421300c0343d04e0000308903252440001100c25500c06002001290f80c5ca481e223030001100305e42c92505500402201500088112040101400c00000140143c079414414842141e80a5122030480c1d040c00d0002e10134211b0100840790041003404405145680c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 383402131 1250 383400881 383400889
    0x30b04080c150103030f1206050a090c0207081009020a050904030804061a040623150d110c030d0507020f03120f0603151005011209020f0d030306212105031302 70
    0x2480d0b029007803020000008240d44002201c9540c9425940d01042c0f51308041c6441c1030b10914000c003640f00c4c2c100c5005215240766988021005450751040710b401d1a0360384080e90920200005885140e51a8404002907040005802009100036074003000686030507107006080301006000108076640750140301421030070300024403d007490001d2007048102d81d269800b09141c140349030010b08002d1424221f981c02d242071100c1d039640b4640000014034043c111071920000303000c1d2a007040515202801150345c6c00200300050311000701181c2c40000d040c2032074080a444c20b502c2010b0f03110242d2082284081980b14410710320741000c148020310324240ca401001034182100b003c19158204161400c22483c1d000002e12601100c0c000e8985484460b01042010700340d5990080c0a5007100c02041e00b00c07002c0c10030904050303455001e860f0005205032200b40b01559541880d55821a40032a1010001806040c1c11000100d414480c031184440401840240c100d000c000c003000c104000f140b01c4242992a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 383403381 1250 383402131 383402143
    0xf090a150608041104061a0304060f140703110306010e0904050c03010912031a280e0a0c0315030b13030302070606300206030a110c100203060118030b04080c 69
    0x30111a09400036865038030050903a1003c94013907030181c4840c0148081810503100e001e003901c01c2c88400b440031200c503c1c94607513154000380085038080c0e51220301c01e810450034072818200201a560b0100c103814594001000c1d280c00d880340c0b1040803410400d02c5842c0c0e1300018000c1c8059800d451030191070b5500d081c840d052516240701682c0ad5420804442e0410000c5502c01c081d4540741d44040141045d0b106d0b41c0502448812030054000c1c02844041011810120303803045960408030110555688031061101c2000054455140081d2030b404000c442c59010f018150721055000f1010f4101031450f15220002c080141000107019085000f140a05101381c040b1804150411001d2082a50b1142c03050451141540084d42c075030b220000c0100c079003000707400d09212581c00401c1641103445851800d4000e01d1000c4064007511010400c5054005d0103014002249a00010041e100d1400d00e001400d005280c0c401c002c41e50703010010500c00210100c1c01c194110389c0242d9010b45030800b045496140079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 383404631 1250 383403381 383403401
    0x4020408030a0c03020d02060412032c01021e0c060403080417030f01050a0501170a0c030e060903040f05030f1002091c11130e0303060d0303090c0e06040c0e0f090a 72
    0x1c000000d552080c80e0300b200307a01884500c03d40c21074081a007084400c03a101d18060307400402c1c0319450103000d42d0040c0310390048038114004140100c048484552100059401da114001c00c0f650081000c0d1080c841c0c10812504907943c00b1006458a81100742258845400a2004040c0002800410180499546c45e8000d030083d114409036030f402c0000103694402000d00c9041d1103825810b40114455114843c4111519000a0b03140b0031921180d503601c3c060f0402c600701c402019580e4019406d511001c0001c00e0054000e14041d683c1c1d6803e240c410441103481d500818002d45c000218500d642000165400303030080c90980c0140c8400c06140001c0c2446200021424000007000412007400310140c10340c0862841140c2c424110000989420255001844100c0c41c41c0c00510010301c0b80d00301480354514085c13192500259501142d641d1311224901600070994500c81041008200d081c18864414800041d0900b030b0386008a03080010005d0b400707541c00b14040e0780f1f1280030810843d16900155120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 383405881 1250 383404631 383404633
    0x206120408041a0c010518030901031a0a030c050301050901180807020d0f060e010c08090a110a080303101707050f0607151b1b020108060904080f040f030203060f010b09040b04020408 80
    0x460b00203000d0183c80d040f40c902000c6951900c00414481042410595400f034120300c05107080c4201c0c0070041d8001c003080b09118840d0b411b44414452281d65000e885805107114080f208921805d1400780f600310740000b8440039031603140890140b405407000040050301c1d503001191356a122802e101080303800d102e5584c020031120a15805500308071050b0088504e91382404000c00c0203404101c1c00701e65000303060302e008445411100c49003010840240d8074861100001c0d000d07000007580c940d0117500d140d0085400715407405c1203001c14801c650301450660440300035500105a141e042000003010700c028100c4c89841170720000f03080410000000c11861402130048420801070544802803840d09001c8010f00f00040e0b0208140301e000303140c4071034214405d50180c0d5070f440e49640b20b1041c040b0444010b00150340044003840200c2103030f0b9035880100082c1c02034140300c03c41d4602d10320502d4130b05140989180c168202020041c070406840006840200c10201c0d004181100f501000c14024410307070b0450f03605 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 383407131 1250 383405881 383405909
    0x20d060603050901200a0e041b031e0203070504140418060c0e04110301060309031701060c1709010804020f0109180212060307031110141201080c0d020612040804 71
    0x600c1c1e096030185204982400091081c45c48222801c00f451459410b48902c024092040600d0305210300680207000001030700020300b2041d840c0b09030b10310305030220740000000c2d00d490744c6080c200c14034188548141684042036045061070346000d0100d010718042c134602ca0302c1e80038201d5400d603102c0c0c0041c1c0d04c1071680034400707898035214245440a00050380b145c00200716800d543d0041400e103480780c07001a102da0f58101c0c1c150303428448110041c0a00000a4040110100380d64441c3c0d08040141802024580c035002084c0c606413500c0040d8040c50282194170483c240030240d0700da40c0088116600641c102c80000500413944016119189290861041a042130f001b208030b40350290300618094084894008690703035810308066683e0312a00000b05102c2c8a18224225410020320400b030b00036050510003040c1409000d50070a9410280307043c10b01051040040000c0907040c8601c8801e01c0c4290360b10102030450340c010030070780e21130700d000343c213507014a480020207100858090314050048560300c264 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 383408381 1250 383407131 383407139
    0x102a020705010e06182817162102060c010606030902040e0c03030703030203310c05030d021509100e030c0601050102010c120218030d092603041701020d06 68
    0x1503989000e0141c18082203910300c00710080c4c81c004040d561868502d65841100083c04000d102c603d00e24001400901090401c0000e80c0c40380c40c00707050300540000510741d110b00c051074a09603e00300d01c0741c1500c104120030341420700031f80001401100c00180000c258074103007034035840071650910840c188a17841c1d500e021808588158503801420526008541c1444010100f1080c02e07250900782e66a5603140d0701c10081d89000034080e8002c0c1d035011245621035680401072007468607001d005004002160114004140104098034550801509083c0e004218220409401035510b03107030168409030440d460000145000c5040104040829050006102540c4040700c0c1e07a95a8100c58440366050260000200b200e500c148a40300103900709a507a0300c00702804483e20002588044e50005903041c1d03c078240c1d94551010420549400e5844e61040d4810780350100c90f400a101d162030900040c4640c00700300007050000020394042e11403480242c28100c90050380240244150100301c08080d0416000007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 383409631 1250 383408381 383408383
    0x20315010603090b011e0608070e09070305040605090c0303040b07020d05010603210e01120e010e2d0c100806011707030c08070f0f050c1e07150809102a02 68
    0x34048520138440300d190380e41c80e000d04200b060303503d5203c1032440d4000300742040a6440f89003001e40001071070414103d0000c07464003282d244042143d2401c0482d40b03038030034401009071a20034282c0c0072103904040d001c1090f031240002e0701ca00c034030301c0383d009440000b24611040d95a40b845c068000c0c1d03030083c02040f141d540c07850050180280d110821030f0590040410307040140c09102d440c20500c005954205400c1c0c020001032004010901c0e4850440d03503a0203050411840c100040d120429403401d4000340c3c11080140803003841105060180b0341d03080b803d00944c05403114039541802ea403003030901e0300700e603920680106c1703a0b1006000101c1c2889508024405499015031044c2c0c00c190442c0e13175041059a03100700940780c001444025100007810221011095440340c400341040c84402815100900c0c0c000c010302058444000c2220000d80140a04000101d0365500b0701c0070b811070034149040c40340340c004446a1942100e0462040217038450111744200b40c0001841542c641c2814040e22102c01c14410003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 383410881 1250 383409631 383409641
    0x230f0402030a0b0612150603010e070f09080f0106080d090e04080705010e06010308030907050901060c02040903030f020d0b1224070c02040212040c1a0f0c0a02040e0a1703040b0112020315010603 85
    0x10203484801c1440c600505010042342d050741c40c2e0000c18426a2101202220181041c0c4d0501c010005504404540c4020501c2242d00211400c000455200d04000304541090340d07031542c65092202c1a01d04000c611101104181d204c2d802014058586805040403405401c840c1ca422169005810002c0304004590b40694001c0d1000d004803602940c5600030311418940070f0260700301040c125084880140b07032079045940b195100740f80c086140d42014040500b070307030404040c40180e180c580a024126080540b62942250700e42401005900d10744d8a560b00b62200750071034500302104060002e644180540302400ac1c0c181c0c003410855a0386400054420f600c0350554080300d0065035040006044019040401c1d007030690320751118038150300540c45294590290303603a00c1550191640d09030140ccc2e13032881642c020055007c06090001348a29004082d81c00b0241c0c2420441b9040c000d03c00800c042d10362050544480c0e0902e103c0da280c560001902d04420b40f148141031a0b070030000807410541c944c02c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 383412131 1250 383410881 383410891
    0x1021b0a1a130221011803030e0106380703080609102d08060406140901020c0706080618240103230606040b070804230f0402030a0b0612 60
    0x7407607294400d8195450603401507030418404046022031601510308400b500d180c020b103481203009210340c40292103003034980801004000d410b0004640042c16050b000300b1460002e018000c0005030704012881011440301ea0507a44078555101c101003c08059680000c00400980120750b100c56141c43c2c0205800320881e00b041c09142603074080303603000c0e0409048000741e88403803018413400d182a03c01d02600ba02040c844040c246041c0000040c40c520a10600b1b0240340102c0021600700320744d410440c1010000f42040509a02c100b20f07507446000089481010340b1890300d4180e54544690740007030407114805841317510101c0c442051140c1010710810080d00881a544c00c0030101144500550884400c64600107841e1030620b80c08036082c010070161680b00000030711540c1440c0e268480095245c10110045500260009081c000400c0c817003200f01c0080c8201891030940d980c0e04c008103080c40b030aa40858059900031010440b840c0040e0040010340c40081e150644420244843e518500e0301034603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 383413381 1250 383412131 383412143
    0x1b0601030b01141c0f1a09100f0e0a02060f09060c06040b0615030109050c0424090501030b09010504051b07080901021615030b120a05070302130b0a140103020904091a01050901060e040e01021b0a 85
    0x11270301446890780074600c0e0155403135014002c9541c0d6034003400043d03880040004485081004400000e41d5510007030000b407984140103110030701e040d02e03114000c400094501c621078a500054688038110000c1164151903141d070000c40c5544a003044045503004581095041303132010705103016030304044410141403d415681d008a42e640c2c80006401701c0f110405040d801c13401d603000501840c00c054210b1908121064500d0703a4181c59640b0041c2c16800140c800c84284400048409896904100701100300310400340c5038038401c0c0340425915248420600c000141603c80030614a6956103000c1c45940c58081416250b580340c442c50616241c5d01c082c002284584ca000400004801e10341c41a515041c002510409036907007001c0080c65280140c0c540141003580801680311544c440d80030f04005544614800c101d9880c0c8007107414401341e416040b4030302903800d03440104006903200c18403100b89001a40c00044510b0b1707582603a030191040742c04041c0000b4003044040c81085000079450607071400303a4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 383414631 1250 383413381 383413391
    0x705071505090a02061c021303060506151c0603020a090c081003020a06120609060e0403080703050601020303011202010e030115230303030c1b0601030b01141c0f1a0910 74
    0xc08910880e0360541c2c5000d80340d0b0195090500504140e0010031a811440c41442c003a0f17100c080b801d5050b0b0344501c0303080c500102000010030422003140a5107400030012a07036071140d45003e4643c032407980247d03801e000c031a4000d0000c404040c88958010405113030060300e00b200c010b032204100c2015160141c0c0c1800040c18681c006901440c40030500e41c00d50b68018154070030a46442011208a01561901400282d070384200140d07040040c401c0d00010005c0d1160a00d5518080c10082d10f03100c4c000b418542071500b80400c0104583c2c0c080116410340c0c0e1000351811546103107000481d42a0708a240a50305503117080e4480c02002c8003008810121840c032400015880100522a4519030840e100c55415500c24408602c0c0ca400c0d51002c2c0240032022144040b83e414102d449074900502a817041d07500c0c204650040c1300c134450b003c0c40903103c1b000507942a010380ca0440500078a41c0b180c980060f100785002440801007041504800b1107454101442110b00e0801e21102611602c0ea840d00845261a01c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 383415881 1250 383414631 383414663
    0x106140a09060305030915040e0405010b180f0402090c0c0615090105030d1202090409050115090b0d150b0f09092b02031b10020c0109023d0201090b070507 68
    0xb030003141c0c25607600601960415a00100303122400c40401600500140b05001c0412070003502001984103500034000840c001c411001440807801c031103a1410000782c0c0030400c2210000d042c112190300150305840880f05582ca042014402e030180380c0cc21142c2d80200001d102d5400784a82e6020110441100c0c0001c650340e941081550301c00c04030f5412408240180200705503050154040d00e22003a02130804515000c0c07a965181c2102e400c07015a4032250060300090103511040e05c42e00400c643e09807154005941e498507580c6484c008401d03110310041c0c80d00c542d40440d0711607035100d0120301005040940396003010406143c65030085e010070800d403101000c420940306007180b980d4816a2883d006145032102c10240b001441d4240e105100d81751090401d604a026504e00c01400e00007842c01c00020049224410030002241495482e9140084455225101c144290b1030800810181440c101c907906201801d0340034001100300645010029000c100d202a0031000801003607100ea0391407410f12200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 383417131 1250 383415881 383415899
    0x180c090609091a040c0f0305010507030f200d0b0a0b04150201110702240f04090501050d02030607080a09080f071b0819050a12090501021b030d0507060902030106140a 73
    0x164280140500909043c0107140c41034101030580c12034011031070340c9500c9455034900c1d407084410794011a680e079500d004001381d42d6450722504140040c3d280051004c49482880c0d003116040c6110001c0341407800040302d01d99569250b200724443ea1010b02182c0c0f001d551808255020b8104d4031074030410050048401a60f1441846200c1095801c108903a041c422684c0070702102d013080e44072440f1156000709210390480e85040c05084000303079070507e075541c960501030b0005c196032042c1d11507030045c1400006100180d07404100e80d035000380a0700d00382030b00f03948a130300d1100603142110020f0000a030001e01840421000002011590700403008045144a44020400d00380c56512941c02c0c0d0350805041c0707005143e00020500d620310301a404442410001b92181d01c60142d1600c0001c0200719504410012960180b041d000d0070300341d10000d0281011280042078a408044847d10f00304200001c070340041003810b501280a10742c01600810075642c8078640c02443c0e07a00b14052600c24920024001041c045d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 383418381 1250 383417131 383417141
    0x906051201090c03020705010e0f0d08040c09050601050409020706150605120a1107060e010606021c05090f0114070b07030f0905100c0c02090702030a1e21180c090609 73
    0x580c040c6520640c0c0ca080034020081c01a00c85400805408019072800300303800b40600c82c003903140000580f2500f1190b60ba054030f0a0140004d00c0280441501003001248a402400c01100c144200105265030b80100403242d03031046420030315001d440814850306011203544401c0c90305c030303441810405641d1154400d036018051440c2d0316000d003101400141d0f014200f82c008041c5009000409400c1401581c8c076081903603840c42200c00240e5441c001003100c10345c1000f400f806000f51100c4034030100c110340801089c41c17262a010a000e109030a61092103644111611107160602410060325040e06181802d5007580c142d50b0380c1d00090401c00c00e442450414444c00134103592010050040b032080c145410044d255040c200c90511480f09511005610f0300060a4031501e8294090343d0746a408080141018204400d150819101c1c03901441d007194006801c41204030040b02e4480040c89135013a0034024007140181d2840d521002d00c900c6d001c0119403d10a0256900d01c0c1c414031145131280b85681c2159 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 383419631 1250 383418381 383418397
    0x303150e070e0603090a200d060b1302090607120203091008090f1c03050c1e043206031801060803091503070206010509040f060c05030403021507050904020f121006090605 75
    0x1800c1382d50000001500138201220481c66560521511120400003a0b028490305a05271002e546803440240c681c0341284075030b100d207108c4010031810141080d010803406e0003110b40040803004041c0d440c56003140204141c0f614000c0c010100e02d145041520010b01c075007401d50344100d261048145200c2c0c0a400440c03050b80d904400701d5402080304121004034040d140280c1901a01c1c1800c10034051504071482c0040c000c014081d05d03035540c442c542012058000b07501e00d00c0314040b454000a041000450011006424a0441f001a01c036120740301075010071010b00356940da041d0720b410800602018003001070300c10200c0c105c44440c1c0103091320803084040d210494007000140c1041005000c1460b00300c1791303a078115010f400310aa0400507a0340c0c1108581a40f02d00c4404070b00b0200c01c020801d64108503640c0c20040040e120a52801c040c140985580200400144126004500c1c1e0310f120003000c041d1000c000c00f0516005003414607039584c10f400c103454090100010030714500490800d006104a803824 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 383420881 1250 383419631 383419633
    0xf020301151505220e06030d11060a0509010e01050115111506270a021206060c06010603050919080c0d0809030304110a03150f0501050f060f070303150e070e060309 72
    0x129405021181c40d80700c0c0d4501305492030301c002442c41c50b8201101c0355010340300d1403c4005041c01d0500c1090320f031003801000d90081107000d403207080802101060168000500007004141501c41c030b04070038054154160b80210035841c140000809200c00c07111038480030b43c40d8443c951320140c0881c019803210000c8422040c030001000101d285410480400c8600020184072308a411850080120124201b41e5800e1203581c1c02069456142070500d0503280c03c15012558246000168041e16445100503c220014543d5a40c0003440c0540140529801c0360640810590100524504000660410064160513105da9010a8001c0d4010f644441c0118070f800001c50441e81c469603488031a040c1c0e00512500704c20981c4001000803100d110800c00322001010128080740006140d104903041623000078400c9001010f5003805031200001c0720146801d100c91645e0300c00c0e150a041d00501b403c141c074048280e2140400280000381d80302410b000d220290340395058076022508101c840e02054505003d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 383422131 1250 383420881 383420909
    0x4090506010e09150109140112020108070807110a0b0f0a0504021e010915030207060b101b0c050303030c0a09120209280509012a230403020d0f02030115 67
    0x2e25416094680d5122008004803074280700c0300302c40c0001070a03080e80700ca000c0c9a110000a1055550300c81202e025000c42090031551038801c2d00005e100040151214043c881407034045185c5604c120b18203804400090300311045100903150410703c03a402120308c2444d8486080102e00e001045000d40c40c00f6540041019070401c001c00440400340700112502c0d4140103500400098151141607504d40e19512510b00584600082c1410800c0c4e40040640b07600c500c4d60f6448500e007030703504512079800840d1031014003010301c580c1d441c15880700041a004282d05103c040100032003150f4140003817186c200c8503503178881d46a0b640c0300c50414003c1e001c107000350b0100c0504002440d00c0310300c00c400d0410300510403503d44500000c030328810469900752500b1000365120a000012400c01c01e401411180e210005110351120441c0020701032051003900310f14240343c00001003800454002654059071700140910440541c51a00c3d05121001002c00c034003e50804100040c485820400a82280c11078108012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 383423381 1250 383422131 383422139
    0x120e0d081b07092a050c1005010e070f090909050f0a0f17030105030c04020d0b042a02030c0a1221090b010b120a0b010216030c1a07051002090a180c030b0409050601 72
    0x130015007000c41030401c00070300b80b01024005100f08031021407900c01032400141c0f9418441110b840010051901c0f040c0b1a21300145120290300234119812148075030000a01040c481c45c16030b04064034582880710b01e01c50012082c0600040307404040101e813090380103103524072384c00c1c1c030744422808244075455140d0032000300400d4900b0b043d0001c00c4000241100000e107000d40d000000d08a80722044002007095080543c4400b60a00006400000b4440c2c0021820410440d440700d60703c1c5902e20b001410744c0ca00c240070540d024004c80303034000c511000a407203051005040d0b06d082c00070710f101c410075135065040c840009007216115080320302820030700080c1c00440c1d40306c0e11110050402e41c5511070451003040e14503051f0180f04850b040113544103801201200d8600300f80c003054060201d00c000d88900040003003100181c00050400401e0403814000750300c80100c10002050b0489560040d1034001d501c04480c41d00d0321440d40b2101030041991410061600c401050001320f401010004005901c4400140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 383424631 1250 383423381 383423441
    0x5090f1204180f02070f030e0d02210a0506090c0406050d0201050d110f040306140a1b1110020301180f050c09130902060f0a08090604120e0d081b0709 66
    0xb19001c079640da400b04803d10002034800499100340020f4864112480300381041540c400c003a15075610007181e1a0303010b1a656000200111944003001c100350707803070180c0c0b440c20301e10501c801c4880d140c1000a44003c0e1400394010394440b10401103041c86240b0705203000c201c030b10341198500b0b49180c06950345420b168040c030132a002016001550070204000b88a0b02480f40800401040030314441c401c0800c600140c114140c0c0761560160110402a080040c16001e84034007860884951a071442e00780038100350745084070306200c1d020404110700c0e4000000420701d1042d210494408000c001c104020005083380101c5c00c440043c0e440016070b110410100005145c503000035400ca0503241800224001103900042855001070204241e0481c04640c104004e41c20a55080d4080e00b040080c080d41e107030a907900c801c0d000b064582482405021424181d464840c030300441400c0358446d80d1300d599071340081c0c10307601625840e4076090703aa4410303014085003507501401103049129840c15079824911100f0841 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 383425881 1250 383424631 383424659
    0x80403090b090d0b01080109060b04020f3c03011502120f0918010e091b2d0d050304230303090f180a050703050f0f1609081005090f1204 60
    0x320740c04030803841c2030004501c010304d00764020440000001005841c52501c0e00503200d15040442c800d07881404040c041c005007600300c45143e84c03800c41c4801070b400303ca9042c2c080b80b02c0700381030780b2103070101c010322229045041d00040d4140d030002207020045003a070000032a07403240104004981000300744280511420010050316071080d0007081c188507001007402d04c0e018008242d0180301d10541d0a41400010b40090100740000c0e000708101805502c0000b01040d9860034684031106038241d0054075410403071065041283d841c00047c01e6610f02a80d5003043da0f0f4a4009029482d85100300070140008184c0c202200301145078041c01030360074044540308020010300788002540c0c10040503000d600f010348011412521800404030005564203210000074100c0c1d01c004c01740303c0704692440900010325032501c6110f40c4400010181c002642c9221400c84409a01d948441202e205c6d200030001c81c61140e030400c500c20a802c20884541c180c0c400308041c1d82e03071145108410301d26810003040c0603c87c240703140303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 383427131 1250 383425881 383425897
    0x618160611070905090706180e0c070204111b010b01030b030c0d05070803190219080d0506040e010e030d0c0c0f0803060303070c0305010b0102010b060315010503041e140d080403090b 80
    0x240d03001583e030341c801041511400c403078030349058010820502074140c0107102c8035515080e481e120000d590801e60b01d030001e031001a000405000c004a43c6c0b00440d034880c2c10202401c0020301c182c546a0382150080400c06519100d0002c2e903500b080d4a05445520034030841e000711a00500800030100c10390700744040030001c0e110664040c0615a4007180300790041004140b201c141106205100c40284c0c402030410980000142c40071001e818650045003a401c240e9800c1c0c0162a0009220380324500010014071710562003d0346942810801c0d80180f0001c806003100c11041c90090105101c134520032592402130000080c642103601211a022072240c4006d07550092000d806c4034035090680e00d407035490821503070040303986a45805a0000c41c0d44d080c01900c4520606880582c10341c00c1143e00f1048031468162a2410000c0c040002001d2201c0504980324006c0044401c05a030649400e041100020400c4840c1492040710001c4820510402c0d41034070841e0940d80c0d000c20303d41810b8185046a0002e00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 383428381 1250 383427131 383427133
    0x213060c1103011103040c080105010b042c0a0207060e01050103022206051903060e06091207020105040905010905040308010803190c03020f011415030309030703120909020c0618160611 81
    0x1c028980d51402d1003150b034030b2072800c80e8650b1a480d00d407034146060355a580020049034141401080420006d1055400703480140440d8044900481300d41c140c021020a84c5030b00c80e00ba88010302c421418160300502046000f021300f40403c0403142c2d00705003601c00a101c02500f040080302240349240701000c40c0f0002c50344920000c14030755644c0300003a80d101052003140001034a890010010031115110b14102d2002c040d003d0280c501c0e01043c05919980002d2000e0b5040400140c10011a0b21030300c2100d000c7c1c0070210f02001103503124400c0e48014030044034120040383c50040082078054001064450380101c10340045d0424441c040d048400310354808080f42544640110450705610a00031807007a0541d01814680501d0000d80e489010481c0200c0c49001e504100446051030300c0114a40d01580e420840e201c04500310b00001710340d0440b40707511405e099803010901000403000440d9190045041805500b8008044d904650b02c884003c2e0703452078828044041081440e005501c143e294009000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 383429631 1250 383428381 383428403
    0x219140c0106081c0815010f051c060305190804030213060b19020d0c03120b06071a060108240103090203010b04060602010525050a05090406150e130213060c 69
    0xd5250742500c4254011441c150000c0c1d00302d441500000c2d810b0a200220303031401c26800d050100d10269040d100c11081c5041100119124101600543c100d882c030700c04201c03618600c10000b1548000401250004603a10301404954107900c002c45e5050b40c601a4000c0c2c1041e00e464a150f00700010001806011000f00e6210840015014041009880300040d007800c610b440c1e6000703600003814410007002d1581400520880140800c0c0d02c0400302c54441064400020102e41402c00201a1300500360020084406807001018441340d8141050040c90281c80300c81c280d8803481c0000c0d61a01008103961505001030030500c10340e62007604034000c12800500001480c0c00d5880109040d41c0c21030b0001000b50703456a050040b043d1074605070004101d803003e01501d9070040c154004013035128618403542000000304030601c80b6030340ca88c030090042058000146009404850160050500c0380100c0e01c6042c0e0311428480035943e6000300e620500300c820300c9400c854140701e825a80d00e003100d130007a51040c50300c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 383430881 1250 383429631 383429647
    0x10905151c0203100c030905100e0d0507050a02150403030e0913060203100b0301080c0108011403031603020c03010f14150102071503140103080421020904080715110406090801021914 80
    0x240c4216a62541e85d6030780400c00180320b0030b1003490441c090301c42501107803078005558041100400c0b109007043d4140f0700320382e40d5501804c05529145840c5c00180d44102000c0c0a540901c94803401002200c0c802c0d120600004216010401c0d00c040071030300001420541d41200000807529801168485819010014110384031a1445180e4100340c011010590019801400c5503800407a0a1300525081c0e4040da008455040400d031a170113001110340860040001b04010140248801036031a48003030001c01c101102980341e8000b4000d0140c450306e500011502066034200d1004e0030003d0140f060300108a42850128044070300800c1482050425aa401c0e41c500c255050408090007140200003040d251400c1109c50b00010070a08a9002c0030141c07a804840161103060a0a501c42d802c11062512859982403200d002c0c2c0904015980f110300d4400e0101c83c44003000c0242041d40c1450780d50110464480458608078864122034108121041408a484501c9015080c414810800b103160809100d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 383432131 1250 383430881 383430913
    0x20d0305180706050c0708030f04150908120706051e1b040504020c0609010c08090c010807050f130f05010c1a0a15081f09032f15010905151c0203 64
    0x183e410041c0040c07000500b650460710100f003400050402071015514000070f403441c0c480f092245200300101c001060420820442c0a9a03005008007000000d460701c080b400c0c000c941250340b203c102110902e14000206114408005480505c880e00040a140780d4980f00b00000c400b40391441c01050841040201050544950000e0440c910010f8014411420804422800d55030500c90705020014201c00f0004c0c90303200002c0351040c600080c2403903807080d21212000c07030f0070340b107402016020900009449040d800710350b014182151000c25004030011703120401110744110289028160a411401411030201e10309041c5030007542c0d4100008070720401003540016070309194441c048a0704032103403088a0710b58112903440c0e20b02c0d072241c0401100350030380d90107054000c402c03820002540003840c00441e034002e4008503010041950045810211828002c0311841c2e82c2402081715050030007000c01c01c44e9a40e90707520660890014581c1c120506048002103010305000c2c01640c0c5449030082094182079 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 383433381 1250 383432131 383432143
    0x2040b030a0602030a060e06180714040e060102010509010c09060806030703020405010b0a022407050d0f0213170c01020a020909030f0301060c050d0c0c06030902030a02030105090102070213060501020d030518 91
    0x100c0b41102580742e141c41041c3c0d40c1110400e50249165028010400000341e85440c02010b42001d01082c500b00740c0c1700d1040031100f0801d14003190464640006012030601c0d05128400d100301c0c000d80c000d109550300c0ba24030034241c5421a07585004207415040a100050146094035801480682102c1c3c0c200c0d56500002d040c0c032020380c0040d08090000444d800d034250f045c488000e54104030204c9901c54112070600e44106200200070104000010820901103c00d0360410842405954415504c4841c07010208485503818400c00074440100d0b00c0e0103040400c08900c0c1510322505070041e0200c4c140d540c00b80114210010a13405840c00208030404291543c6000785000e40322954414841e500285455071038207a803006200f0034020381d4801400050800d0290800b951821720f4042142c12040c0302007440d000d022140290706500781070801030340e034205502a1070524001c480652210b81007c5082c070845106014860041c0c04c0010102080c6001380c0000e038102c1c5080f4042507000c8170000680e41000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 383434631 1250 383433381 383433383
    0x9200a051c0206120915070c1205190810050405130609050a05010c02010b0f18010b090a03020a030b0a0b062113020405041211030c190302070b070804150e0102060601030902040b030a 80
    0x3c13441400f40b00f945181040800c011740c80009444c2030905190304060034105c580704006140b01d60001d03642d02110302c60300c2524405c00e0142210f54034503c0c07003c03028101c0d00084404a2441da6580300c00941443c00740590750060800040741004109961103440c060003036000182c0e00c80c4543c151f84000150244501c003c1e10409900000d8071a0123502044a4056010341003441102c0741c542d400031400c0f584103514119000c0011407540d58100c80302003110400b03550b1019600440003a000024441e03850211071203128440001c008100310342d82040b9282c045e2940d895440b00342105000c15000e80c880209801503c8020b900c60000c0c020350000b41983d0049500301d40c0d06400c2c840b10003e494002444503044008800550f041c0301240810699918200c401503482c13044c0030303003d001814001c2c80310001421101d030707580b0340d101d06508200090f68081d128407800021049140481144070301151a42c01c6016030103040641c41d100011005170904c40800d030307441503462100c04026581045040920317 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 383435881 1250 383434631 383434657
    0x103021e040305070501031109041e14090d0203070308131509110414010815100e13170306060306010315050a080d08010e010303050703051c02070609200a051c0206 72
    0x540e042d850602c0c10143d9a620140c103250800002142e40c0c000601951075205044ea03000408401100390048440034605070400c18130726140e0294028001504210712031225401150601c0c24000c104a81d030784245c41c0c0c05400100c14801003120300c0c4080369041c200300c0c0100e41900e010300076418039070106c07415581c044a901044190b508294105400780c0301807030000340a079003865803601101545400714100402545040c0344001240c5100f9031207040064055800142d0081c03a05074002301c1000807075130003940d080400a2036080070069070401c4034400d03030015150504640b0744100540180c040440d020502c401625000301d20707920f80c0c1d014030004000d90340007482060007101f8060b141042c10b07000070081c00d1140c1e005102007900042100c0403907034180ba0880d600c1c0041c0000d0a41d21031042c41c4218610b0000170324005010843d0400007809014046c82002180d0410300440b1040c40c103100241c1000d10000c00301711500d0441d000e8801c0d44003076100b11401603440d81c0011b1260780030496010308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 383437131 1250 383435881 383435887
    0x50c0c03150f1e0112061508060609010e0c0a050706090213021b01060f0302010e0619050a030c1e0318060504060212060a0e0a02130b03040303061502071d060103021e 73
    0x68040000c04a0b80c011010021000b056056030603c1d00e4414014000e10074131701a02c1c035824040010030782c0640c0c0302c80c0c001950f1001458691200c585c0301c04042e140d035445101c091002290381e0b050700361031754000c103021130500d0300d809641e1100341c920307400022003070707c8a698420120016856801d020800803460b0a40181d40d200709000c2494003044500200816a161190520030403802035401000c4c0c2e0740901307000382001880d01c00a0031602c200c04034001540c1c0320b403460350700f404d401c000500942d902a032428851a821030304200c4941c400410070485040507400400c01700e81c02130f8011240410f21015902c4282c003030b900c80509aa006550445040cae500280c003111749200000da00b034020008031402c03081180707001d0704a1b464003800351180845039400100302108410003115000104591444240c5a107003906000e0001c24040c410003000f124034103204010544041208415103284940074865010f0390b0100814800c0f0040600f4181a800c02c07200660000c24095803151592f40f8400c156 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 383438381 1250 383437131 383437141
    0xc040b0d0515060a060e01020309150c10020a083301020f0114090106050103020f040306051e0403020a03180b04090e01020421030908061e10180b0411030603030406050c0c0315 77
    0x3d0b204c1c40b988120304102c801c6c07108440310703a07000c0201ca03058141241c059078000400b00f003040c1c00348103444d110b102903c03c0c2c9807a41313010301164015051095043d26945044d6403103540d58150342c1d0241002c40210445400d2080e10002180320380140048107104030fa20164420001500310750214100d14810307411042004400c071000d01032070000e00804c1c07030250b0910404a04601d40c4c1d0150340030060907141c40c1c40c002000c0c0c90920b82e0034030340000e0390381e00d80031141002e080207900d50000b60f000758002070885101d540c2d64009400000c0c110303a20056103034a13240c601940380c17004000000001c0c049540030000050403a8a40364804103540355102c24030000801450090500625a4425220354000c58100044c0304c00c501d1000003c0001c0002e506201d90310401100d041188641021a40d001c03070407130304003640ea21a80305100c2d02c030090718100702444401040009a000c200c40440c1d0641c010002801350303034425009002440c088204541000f1800b500182c1040c10b190b0b601580b501c0380d202001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 383439631 1250 383438381 383438389
    0x213083a14030916050a0e01050d05030f0d020304110a03020a05010f030f05100e070207051e13240602120d20040b1801030b01171e0c0903010c110c040b0d051506 71
    0xc002044101c506e003e07036a142c480b104505140c1480380f00d10a5005560340400d016041c41220107009122005680e90b15080d00480000d42055034256000d03001d03000984054100380c4003403c00c3d2078008002c203a01600e44401180c00b41c1c1c0f0300000c03104140c1c0325030303032403110603442d0090500a95030540f560300400c0c1404100c4420000c010b242c02d0842d03102030400c020b10345600708d5240941c0034202c42040700319404404906502d907810703400d040c00f914056003501000141c0c0303401d40b140070448800401303a558510b0126602c02004c003070401d11034402c1003541080401548003c0c00036031009114210209404004a50303904154007207200030300c0001d44004c001c003072a1300006903200d090030108000700d42000028407109100003003100b10341051000c5180c040e120007908000001d076558086061824a041841c0c2e50407107081e080c043d41c00d11488412443c040c20700c001e003e40600c4020040c0c000d02101700005024443d000503004000340c1400008a03a081c000c0340c900c1140903401d03001c0c9061400c144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 383440881 1250 383439631 383439673
    0x90207031103030411010509010302040e1312020f060606031314010911040603030c0f0816030905090714070602210f090c011b080d0b040213083a140309 67
    0x508070701d410400c00c0100085560440c186009420300c0c1654881c903005005a00900c150b0b0071500a8208050030001e80c562010900742c034492265000c16841c01901400741c0c1e981c030764542e03849a00e80008001070814100000515401042c10400e280c18184503124800c00400d2030801072001e945400106041c84082d0140030a4200150b4080041a03e07680b0010030180007050b008101c0786000006405001000040d5600120041643d081c42042c51401804041e210f06c5001d0060701030400144189000360b850141c076107109a0a10b14007840c45d580c1e0b900940c8450b04013429040b04480333000040044e2040355120785248001d0500a060104c0004d10b003001c501c0c1c3c1a410800310304112144034450304041600664014200b64444400c4841440a810480b26894209201107900f00140c444800d8030411a1740304401e44260202c42144030407840410b442c0304244840b40d5460000740c245011a020340c44000b4542403a0b01a404842c0510700c0c1d000780c03441183ca03480310440d031613219810311403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 383442131 1250 383440881 383440907
    0x6300a0516080f090109050115060801080c010516030203070c0e0906060405150f03150a0917070f1104140c04050a0b090d0b0402010203070f0b15030d09050402030604090c09020703 79
    0x101292030146114024860000140107403083c0c0311802c00702d0a00a801d41203007455a92040090160762600c9041c000d20b801d1520420b00040c0c09040000703400180819071405c0a001030355404d00d450181340fa1135580b00800b64049003107120030131101011496900e0442c024003008052a409420301044481c64014040e055a10561518003400f00b000700911034031410450a88000706075059130300c0040d040c0300c1031254401c0c0400364202001a079007041c0e404480c4c09032182d440036081402c01403480c013143c095010b0007080b00355041d03685c80100390002d5526014040c001d0000c148142110f41000f075000c820342c2c0c10651200c0200302445540b030100948000741814082d0b4900f0f010000c00094ac001c24507100c007078180245000484e0035079200b4021507000d2504411205418002c61405d51040c0400711207c62088000c8c40d40302c0e0032485d000c603440201000554aa50240e803c01041200952002c2c28041d03110396144003c00c009011103401030018502e0480041c0ca60807182000380c600d90340a20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 383443381 1250 383442131 383442151
    0x702010209040c030e100e03040305010603050a02030d1e03020708040512010f0c0e0a0312091d070315080616091502030306090109020f1801050d0203010e0403181406300a05 76
    0x601700d211a0000100e05011002c1d1400c081964107958240904500c42c940000d8070a500303144022040c400d001800300c5074588203034126030420b0030502080710100e541e8100320742100c942010354440075219070007507c1d03214080c0f025039180540c1c800c0002d0060b6030a8112541d5070b5100c6000d403410074442d00c2100c01c810031504021411800030400039440307040500000301003591503020099001c4c0326400510107400d200c254242e9550007540c845c100243c1c1100c6980010b800c010041e20508400c010300d004503580107000380000d880d402201d00c040c1303822030003c0c01005036140340001c14000c4501d181d86403001c1c0350007640d601d0074400107016881e281604061540307401003200b003006991500443c4d003451440e400550000c200301004a88600c84d48920400c41d50000c000440c0c03880d41b9110080c099442915150790f000c070140d07500c83c051606c81c491b00e81242d510b1105c007905d604201008000c0103003018501c0382d0030400000c018050491030b000c1840d0442e2030b0310801c03400d410302e40b18058200050f64 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 383444631 1250 383443381 383443391
    0x1d07090e040f02010212090105160501020904020307090816050f040b12160306050f01031a0c0715050109050f27030405100906300b010c0c060201020a0e0a0e04110d08030702010209040c03 82
    0x20700080d18500c61401e022800c4514ad088a4050003001c2d41580c0a08400410030340d50390406040007080c00c6924080c813401c501a0303083c80300b000222100403000b2100301800c0d2282400b48141000002d0582c00206a0440350390a02c25a9010041c450b007610800201000081203081d820001d08442c0b0041682c00c507810040018004103081100c0388059000c0d06440c240ca950719070207043c280d405004e41c0100845100a81041b154550b03421680c1654594441081155a00100c526100f1400d840e92084100308148990411200348511404248200201c0b481c007075460011580900c0000f0780c440010b04158810321246a1098080032100c020044913030b0b45144002100c01e5814580b41400745440d5103001d003045a9008204200c00c05030004038904549035161800f030302079441250000005220403050407502d28000c50031505450704101802d0b0550b4a41d5070b10119030000b01401c5500043c04a2040b0009a12030021441401140c0c00940c68165a400b840240d855010100702814180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 383445881 1250 383444631 383444647
    0x14010b090603061303091203171311150c12091002030c0d030f0b04020a120c09030c140d0b090a02090711030a03094205011d07090e040f02010212 64
    0xf080c680102c4040c41d100e1a200140c6000e44030200079601000b502e1640d00c2d4a00180741d0400d14084e41202c3c0c20030f1103103141c1e50309010b20340408080a0003c2c298100d5171807001c020b00301040040310380745410510750716000780070032200e00d0f0030303001c01c0781c6144030400044502041c10302c9407142c03001280740d000550510248548081e100e411012a010806550f0a4000d080100a8008140c5950f018004540d00c0041d4240280501c090009551685080a000c04e020740d00c102c2c11001140e800c1400d02100e1030400c001c02e0555842c0855003544068502e145c4000703c1d403000c030000d0085241300005e0a610900c3d2041c4101d0b420010914030610200d444101c1b249400480ac49a104440b1304c0c0001c1c414a0303070307d440300c0003c540c0e040720a80e0074012000c840449502d8020380c0841c800d46244001811024000441981c03001d00440c603160703940c070202034900803100c3e070116002a01814844409600c0e060810fa5540b004c41d015074421003d8008182956014068010080b801c10311003445c20f400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 383447131 1250 383445881 383445883
    0x1103130b090a170309120a0207090b0d0b090f0705011b06090302120a180b09241225020f07050f030f07150f02030307080c030c090405010314010b090603 67
    0x2000401414000c031100025521000a0201249490340301080306910500c00126095036001140c0324412071240301180801c140c20041514560505a8014507503541000b410720040c001d00310342c068200040c0420000000c0801030002c0c40381c8202001060b646282900b00d0349894050b0340800c0c14407004c5030a41c1003941c0300c038520303071100d030f4001001141400304c91404a280a0a018521103075441c04541c000426910154510340c15080301881100c064076001d080503588240f1211507401590000c8243d0100340c1c400c50001d90b2194801554101456002c4284800d0070031180080740c1883c4030794840b16070a038980c0c1071200000620041c00e62544e0641c01075079400d0f0500540303118400c00e01c1c1d8007820355800c00a0280c15900c40c4192111140c0c0d80b154a4000ca4120401c00c0c04202d81034138003400340b480042034902c00c404554030000c0355110380c8520b80980d400540840400101041a4841c2d07443d20b00032a402584107480000e005102503211a00b1111103284403031059601c1003d1101d0703a60 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 383448381 1250 383447131 383447161
    0x3090e07090e0606120403020610061e030e070b0a090609060503060a030b06061b010c08010e19110f071b090c1d0103020426100204230a0f1205011103 66
    0x1021070032102a03c4403000100303070340111200300c00c2802461040104055010034400c2c081e115500683c01300740d0300ca6905880d4400d032142408081056201c0c0c05481d54441d400c0050311031420000d403101c054680c031100c0e8280c0d026071174020104e142143c08000d1035a0248141c001030000e443e255081d0b0030000001b032200e65003444003400004064011460340d60ba803e0481d542d0301c440c119007888a07155181e86902070301e190b1003c4404110510700018141512a520300e1050400c0108000364482d80b8030f2600060100080308901c4040030700080421154000003800f0f160f0048280ea100590500030704002c0408540014000c903042045440109801501c4400e84e14980101000141c0901d030048000740602e0303014003507000d041014143c02c0c11200009043c80090b860035a5110030122400d001a88114400c04200e0b091403920b4160195142640082010005182a071000d694401c205a02c403c1c1e1b40042c40c2103016800301c1010403000b481f44000c42209590303c103046250504d0b119401d01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 383449631 1250 383448381 383448389
    0x120318070e09150c18061b0604060f0507320a020606032a040207150204180b010509010f0e0a03120201020a0e030c0d0b0901110711010807181802040504051303090e0709 74
    0x110f018505c400c299624141590b4a095a1621300d081e80191084036a517a0101030310141c81591a001400080d40c007140034607841012103842e1000c0f020f0342c04c1c1107003140d0560443c2c04958001a1007141407401400c0c5d0040180b01c441da4004c02550626500301402c0109a02500c242402004c80315094060150810f29511408031001602c0d070205041c040d04a030600080500d42d94400100440d445440c100d0038054808800020403030500b41e940103403070504c12600345c103010424000e11a0302d401d11600c075500314020b02515a003001c5980b607442690300f915000d29480035035008074501d090680e2101038001c00d070104900400543c440f2001242d190714080c000940441454800103030983c8003504401c85000007441030030703511101c13400c00c581070503804804035000a015001203516a48500b0070707030072480b00105c40c9607510340c90020221200c0310041824200c964080c00300013010398039841458030814900241d00420300c4249001400c01d681ea4000d8078070342c00f4140501440381da000c1400004e071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 383450881 1250 383449631 383449657
    0xa0804032112020f0c012a03060e01030209271b06040f06081308030f1801140a0e10090803060301050c0301080706030225030909180203120318070e09150c 68
    0x5510404045440d032050305e55842c030300e60030040118800d80e0007604401c400400c0090007414082425012016180780b80f244081c10f40340b00e0014000752514180e81c5070000d038503204c500902840c0d08600c00440009151521054110994003085c810702500c00100d10507046401d2440c0c1418101d0307000515000f0300441080203940b000060102280d42003c0b11203a4000c03203025280d00d01464410300c90070084844030a90501c0120464260303805000b2030740100e41c1e8440034035003a9510441034004100740141d07903010b40b0440b208543c04411a105c0c0c1c0e40c070580502a41e581d60303e0907505141c00c0d2030024120311502030041004008240000c1810015214681b40140c0e441d014038a0210110761002c0440342000c0301640c0308810182c00114030807ca8210b140b0034819404483d4620440d2000c40d240650160000d42403000e101035110011981b2940700500303061031068a01d545c500d005240c0c1c010208543d4088203006461034200018510380355280d11a11321450240da00d0141070055083c28041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 383452131 1250 383450881 383450887
    0xc1a040809030703050d030b0402161b1508061c050613051f05090708120a0c020a0b0a02060405011b090501080702010b130b0f030c0607021002030c0a080403211202 72
    0x41000d0441110203090008003140d030019200d0030080d0701d0311607005484002c030b840e224190419050a00079550f00c1280c48000c00399013500c6884001e01303040480d0841445130440c8401260541030028951074400d0595207400740b902c8c20342c00384a1818410b0140c4d80e0054003c000350350010780005285948020640e00d0f00307000382c540d80391070740c50710145c40990400380006207035521000030f03603a0005101d04008030072644000da50700d0b80141c45000e996480c0880c0e217820001c0049082c001d246061110b403015010585081c0c1d180801c0600c0d41080d41d5107001071b00a8014407080c40300900414030031480080c2c02a4021035138210241401040b48500c6060082c1c0c103000844060007035120404844020b01a4001c13281d90001c14001008600c070110320560000d180d09000782030001d0704450106004c1c3c405e03440c1c20540d40030411060f29481c052070852008008003294190b081c80642c880600c20111a500c9600314a020300e4000d4000c0340d924080c0d0200c1140d0a041c40d408030140c80d0b400910304006a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 383453237 1106 383452131 383452133
    0x30c05190804091e14040311030c0d030e0c0d050c10021b040908040b04090506100302340503030108030c06010608010f03120309150b0a060c1a04 64
    0x1c0035205200500040a0a9100c0c841400d2a002c10141d0040790300c0e44a0706943d800d002d2403030444010010b000416800c41c25812a000019000c1d60074540041d0900d80d030f0f211510394003410561100c1001c6160f8070240081d000468002d0301d500401c0d8014104503582d01c01d040810fa00a807072103050802c09620100310b40c03002222000c00300503255502c0040001620454000383c503210000c01c0b0002e80d50f2040d6005100501000030040f80c24503000c1e0411503507035001004041414010800d0130b41e1042c464520020b00080e551143d84401400ca6840c0c21044001000400d240310000001c215104000003610140506504440f07080e03803140003c0301c90318001e100d15080038503602410700000b64000c845169110780740c9000a0801d403ea15191a0f403c95409400300c900c1c1d444044068a04055003240080e003142d0618140e0010700351f036207403005071882448101d0081d4006c0420 = true := by decide +kernel

theorem cover : BRFrame.Cov 383273381 383453237 := by
  have h0 := BRFrame.cov_init 383273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 383273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 383273381 ≤ n) (h2 : n < 383453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
