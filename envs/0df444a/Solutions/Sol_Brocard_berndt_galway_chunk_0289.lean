-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0289
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:59:14.995266+00:00
-- url     : https://prove2.me/submissions/b80d4be3-009a-447e-b3db-abad4bc48aad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 51798565 ≤ n < 51978421 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 51799815 1250 51798565 51798583
    0x705071208071e0602031003060b0108010302100e060f0c0706090b03010807060305070201020c060412110303100b0f0c01060909020a081903030203060303040f030f0c170712060f0c20 80
    0x14038502e0258255616200c0646124032480803441c3d5800b40000504580007446c8242035a0741010750940c5541066015500c40000450500242600500150700c481d40711580001003814840c810324580b4002c262240309005041c001c2c3e1b0300115501030180c501264400c02c45265030f4a0000c55911449049601d00c02882062041d80c0300342e40811065010703420507640040300340001070800300018a035034200242120b007152500c41d900c80194920360041c03102c9425a9451004500b5072406501101d01c07080c06e0b0145d4641c4400100b541440300c0b06250403201b03840c80a038000e000751035440c600d4001030300403650120b01c01c4180b200301288045000071040d1601044d030320300891145598401741d0080d400501240e4050204000c08540a0035a070001401144103c42d101000052414200c104000740c0e002035907038003c46900300b1101000040d103041900c045036400d00c21803083d484c20030010061004044401d03810032401564098004070106d61001c0c440c107545031003042c4844410344032107243d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 51801065 1250 51799815 51799823
    0x10b070303060618210b0406050601021b010e0f0303041d151512060a05150c01050709030b010e06010c0b0901020304060b03030a02070902030c04090603050a05010606170c031005120307050712 84
    0x210303904100c4c128245118810950020540840d40c803174503183c0411440e800c56040d1a8030781c485051020a50341000301c10b407840620a07901000c400c0d1400028111201d80f00e11510500d001c90401304203543c00d10441c0c0c002e04200c40340c40181c0107207111180e207100040ba040020b0601d08075105101e400d100e101c20f100075440d0283c0c0b510304101190740d440340300006081c03660020701c50320010482c0d841c1e1014a511381000130180c25119403440c900c00c0e0a49000034a507400700070f040002000000c0d030049149046d591200344034886a6108070040354010710381000070703081004070400d0102c1802c040d40118004d60041d207042c03000c0f034600814542d41c2c0c450301d03c002e40107a08c100401c0289004036030107160040702d580c81140c90700d40c0da02c5078131040c0c0f174064006458a421085a65040000920840b401481d090500c101030107031041d003584014100415040201a0001c0010000140d503882c42c4050107000303101c11880b044c82615295290000c4034211007612031800b0128582d1428140050403540c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 51802315 1250 51801065 51801107
    0x30402061207020c041e060f08120703030b060307030b0f010908100c02100203150112060501050a0f0302070609050606040608070f1e090c03051b1e031e010b0703030606 74
    0x100750200c00c58840002c014504500480c41c0d19400395840c1d0203280340000200c0414484001c00081c207000b1103403d68000518106444000c100d14400070821a107034a03c001c0e15030b41c55000301e0800354044c048035151907034890b5001003008202038250303220150f14003068521418806050006454640843c02610050341c003020881d000610103802001000c00903105403201140c101d460441607030029105010341c6211424071028950b40000d4601d2981c0e8149002d121180c640700c0042e003584034002c00d40d0204034100036000360180c080c4c0c0403519500d03840b4204101d40901428100d4440101743c0c0d14034071035030516a0009240400090300e0060307801c114113003520a490030803004c900c4c0c0c06c0b030002d074011107030210b10000e801c1d4082d10078001241d5058502141614001403980c1108240c1c030a40c0300b4040c014005a070000e9000d0f240010b85041c075500c850354070b17103880964482010744495801d03480c40e142000030034070541501c00381200c1c6100341c4040c4000340c0c49280c16100d1030006081c031044600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 51803565 1250 51802315 51802327
    0x40f15050307230c0f1e03072f06071a0c180f030717010203070207050904050303040204050a0b0409050c04050a0603080a1d0405240609010512060a050907020703060b01020303040206 80
    0x441801c0d0500900c415540403458113541d682090b0409481801703403816a000480d49401340340c40c0c4000e4041845049002d185001555619025882c0c0ca44054184d40b03032078450b49284890f030301030b800a01900300500140d180d0340d2600e040c05008018000b0310084030000381c08107100d503501310152a028420884105840150700c42840003807410815516850300c81c3c0d100004070b01d1038404005465881e01000580d59140ca814003030701d008400e601031130191040a00b0000400c03404800e0b40c2e003055044501180341c0c0c84200c3c0350400b6118405c1520303809840d00410100304040090030313280d5071714150b038103120a95a150b0000211031103444040c01041c2c0030040c1c2c1d5515481071076691032181d450b00e1507a000307000036401304049903000c681001400185074017001a01540d403807507001e903407802c9915074030300210030300002d01a0080448a5000315407440200c0c10170b503900c480b0200a444041c020401c0c03454900c00081d66039109100076070b0801e25000344403240b5480401264426500078103407a1801e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 51804815 1250 51803565 51803597
    0x10030204110d0603050d0e060a09090b010c08030c1b0c060702010810091509050a0b03030f0901020a02150909090105060922020306010801050709060c050703080915040f15050307 78
    0x10720340c2020304404000c01c03001e200d0000d20720031400030354080c1004004500c0880c2000d008001040c1c0924030034401400702155050707100307000c4401c1d110880380124045001100503507c03003580c250300a0071f015010080140345603407400030308081000000c0c5005181100c0c01c1164403440c10206039078001404000c03e50240d405099103030b0700801403951440c2610707603a00310582141d10036103c0f403d101c1d544039410070005201d40600d40d00045e1006d0304102840d4032100182e80d0b0300ca80920300c02801e0740412118801ea00a0105a4002c0e0f0007803c20542501a8482660280d000809082c0b00e2031030307040403a01c0303104140316032842100054111541d80c0c8400c000c141d03440d00307501d04013825100d6049441c001610180001c80c002d0860f4000442c40f400d0070640500383c2e104c80e403c50800c200314890a04080340c00002e8440450f030b00001116912240d800c085401094a908182c120400000b0001000c95601e44000c0c12102c500098a410303141a00e000c4039644800d43c0d20300002140d0008207101e00f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 51806065 1250 51804815 51804821
    0x2010f0606170c070c0806010602070302040b1f110f010f050601090609080706080a0e0d0206040203010b010e030a14030c0a0305040608010909021e03030c0a08130602151b04090603140c060310030204 87
    0x4038061020b171400f0540c0c60004078a00300090300000016000245e04104509080c0500004000205c1d009a071900c12001a41d07900360b02225a2001c0104000210700c1d4400d0520125280301c0c0550020300c240d01c184101031000c0c040a54031036001465030200011610f00c034a0914040c1e5001d840500030451038900b04595200001c0c00075542c0d56900c08200d030000c8020024412038405a070042c00f0740b46001e004044c00c465419006d80d040c801400b180200035900802c10040300c44e032182114400c0b0009905080c6980261210800d075441281e194030249034008029100300c4185079151a6541e88980f820401c0d100d02280007500051140c40010240f61912042c540404016089904092405050300e1500b281031000392819680014001c81c9440b90300010005000b56000506103014100c8004640090040054505c420b500d0410030702d500e4103200300c0d801852070082c1402815100d050000c11300300e0480c0452258419003100c40d00504020050f24850030488418600c130780d180d5001d10010b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 51807315 1250 51806065 51806077
    0x100b1e0708040f1401030b030102030108030913020c070b0d05070306060e1e0a0f030b0c0c0a080d060302030d05040e0610020705150906031017010203090a020f0d1202010f0606170c 79
    0x11030700c0500c000f040d14200c003d80c510050a040358078007113903186000098111103d0300c0301c490083c0d00400c0148000c0100004032110604150740c43d1801a10156560f8005d004c1d40c0400c800350f0140200003d94080340c840506503180d910310003006261546003081c0c00b140c09510440011804161400c6403d03d411100c00c079200006e6904403074407480c0c000c0012222443c80d0003080080701c1d0702000344248130301c0b00d01031684803621011591422180100c6c140da140f1150500400304140082e80403003c1c45550002401968080c3c222203a810b282032025005400c280240800c00481d400000d41c0707480c250304040c4030100d0b1034000c1e140080c100820b0006001005d410b00101440c02c03c0600d03c6c03602c030707040154410001c0b504030000113420b000d003a03030240c0340808000319280e0061092080c407180200d400a01c050f0304444507805164035001141e0403002084000e01240b9000010440c100d0301034022209a920540d010004ca5817144001d41d06182c00701d00070090990321900040c41450850002d11f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 51808565 1250 51807315 51807323
    0x1b0c0501051c050a05011505030408070602030606040b0309010504060c0f091701060e0a0b01020c0d1119030f0c140d05030403060b040e030c01150603090b070c030e0d0b100b1e07 78
    0x3a010680c1c11010943d4825604100c100f41e54a00410034a40c00130100350022031a854514a54141034442500c20302500300080c2071541c0c000045131140d82d481040b10010103601501316183d01d011003605000388000c84041e1038203420403c4105215100d10390b00c10505006480f100b001606051001c10000c030310300c040025a40d83c1e460046003840341200a184100b00248020a030009007500080c10700007a50030260180d03000b481900c000940302c1001d0940c0030000e40f040f88a24403900b0000c03250015035440541000706031000d160600140130641026950003014103c80307090031809003c82d100e01e062001d010741e0014401030001440383d0b04105c00342c500003030001c01d034008800b0300681154400d500178041d9a546000315032604004070081001032406040401c58124107444035004031000411480030054038403442c400300360080a001100710806000341600450901c0e000044110030b0702c3c0c00b81e4444a40000190202d0076004035484081c58503542403004050010310510360700b190804032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 51809815 1250 51808565 51808597
    0x31506030105031f0b0d080403060c050a05031530070b0307020c0402030a0e030a1d0109120204050603100f020409050903070309030b130206070c051c1227080304061b0c050105 77
    0x14046d0360717407039413596207501403030805a540d440d610784001140d108259040c02c2c06414170408488507004000e80c3d512246192010202c1400341001507a04c00c41c0c400d4000c0100300a46444120000d085c1401a90b0704419045402c4252504a529118001299a8801a0b000e80d007204400c1c101074001d1600122000000b04401c202c09801c1803e40c0c00c0044a00c0008241b07000c1101228065480b040300703401e0030300b81185081d0803c42e22004000b1880e401a00603511200030800d580c500f00038040202202c1102003020341d449a0f4036402951140c811b00542e50300b020045003043c1000b20499001662540b10050141e01d15504c046207100d00402c4d080306078030300c9849000580c89400042c1081881030310b50003603290510040246a030b04010044640070702032521302d000034004560954030b41885081c22950f0000400c3c04840c003070f00e030001188511540316400911090000003800540346140c480489900c0c2070701c0e4150900c400814054003d40150360204800d5001e04010040c500420340c1d12 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 51811065 1250 51809815 51809831
    0x5090c010c0f1203140a05010509041205090d050102040513060f050d0f08070c050a0806070c0b0a020405030102070b01030201080606160303090303091e0b060105042403090f0305031506030105031f 86
    0x3002001103803007800408030b500c9880d214180c0e4170700208540e03c04400d20b801c121a5051001013406d50000610080046140b940009100d40c0100265840100300601c643e03c00103d0b03141140c042e412500c1060300820059034400c0700d2101d86e00500003900c1c9480e01074080d451400d820422000d480b404180c54482595088030082014a4001c01e00a8000d081c4e1f08420b030b1600742440b85004c031070b070b200da4001c1c1c2129041c8442940c0c000e1040c6002500800800700980b039140c000c80081c42158800303030381584005500d104100542c4240b6040300d000340c80300c3c80031f9a00c071000d004581c0b26064400e504080480360b0403001034041c6e80038001a501074a0001422040356848031006074075003a034550300c00c203070384080d000f084840484550300c11001c2c6000d50070140343c0001855401010106c0600f141d01402c05000201c0c404e91040003503a0b046400c01481081c4e038103005d00181c0c41540c6e9100703540d40d803000c40c00d85801e042045034100c0342c02a0041030100e004c05405c0b000078201d00240301203107841e1307404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 51812315 1250 51811065 51811073
    0xd060f060f0b040305101e050402030f1e011103100603110d09050c0907030c020705150c010504120f140702010c020f121005060a06090608071e030507020f0105090c010c0f 75
    0x405000742c06030540080e07580d81141071442c90602c1201c1c10a583c54205032140d58040c1c0e02000784142d8908a5001066540ba2440040d0408613810a00c44a5110b50740f403815400722804030817410200800003c000341d082c00490400036110450310220342000d510001c00401c0d02c80e9000407056441f880c00c0700e003005011002c9009581e40f400c0240c4e07540c0c1c041c5200b40d81e1881c1200e203103a04882d032801d0070401d0441004019495144500c01c8902c50010070042c094010310410444000200d020001c02c110f1a1610340509648007403801e2100203098003542041c040c1c000c0b000c071410b00e0314201c0d1729800c1c10050341c01102c00c1ca01000c03040b6001440590252081e80320001803060b141c00200150100040310300d40c0c00d00702e0328014104c0d4415000100e0400c600b942208441c000c2e03070501d260003070300c0350b9485005a9a901180d0a104082d00c42c3d4501110400d926600490042201c0d03802d540445004a810500740c4006890481c250b40080d0354288140d0b0003040c400c20700a1041c42029509025511 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 51813565 1250 51812315 51812339
    0x912071104050604060e0105100e1302120f1003060b040213090b010f03020f070803040f0c030303090b130c090b010306080105040506061f08010303030506010e030a0f0308010b090d060f06 82
    0x582100c400c0c103003814080007840d0078056070f58011004e03507003048281d00c1c00341310b200001018801d541c05940546210100783e4420480d0516000015001100000d40c10710840001d41c050b0140b00303400d00410b4040f803000e8110b1000580540e2038102c1012082d42076803541c400030300a00c050198810350800c0f00000e803008664000c8000c080a4000194501c0c07003a0001d0310781c13284519600201841003110902c0c500300c1a05952006801440564032642ca901d04061400c40203136024246140d040e400004256068100c0380140e48580803000301522a12900e02801c46400320041000700006d505000704001c40d800303404408030502d404070312a561104150b00f181c00607a001e0340c49070015010000d0724144085416030100742506588280350707103400d00500051060100908154131580442d040740e12800c920480305400074103688420900d49402800b00034952812408181d05400000702840018240c900c0c48070081c007002c507282c502e60f5889005041801a05251a654060109022220038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 51814815 1250 51813565 51813577
    0xb070201060602060109020c0a1104060e131a06030c040507090b0a03050603330a09170c0606120d0c1712070306090605010c0303090501140a0f18030f080912 69
    0x5000051020b0801200a003407030301c140c0111900078010492000c041d903000614012994000303598070340e03000900f000a8081c2483d90310241c40c050500c024410801140d503849803800303200d03e8400c1d442c80c019203c41c4c08c2418044501b03607451703045280a00d0507414250444c07030b4000000d241070b17012292a4101407900740c024045100c0043c0e524000c00605013010040341d0703e20080201c80344510015504490030820300d0704000c0318040c00d05408039100c1c020507084240210350010000c005081e1200e024102c0d03030800d5100204c18828080482c8080c14140f0300100c2c5200c14601515042002078001e4035640b00304503040358500414081c608112a019005c1c0900c088240454401e0307041c0600c000b07050310040d030090f8099a1510038104402e0ba0400440840f6503450704020035014100d05009004060301070240c5100000742041007417001c0c0941c0f000e1600040b00d041000f0705000c01ea458003004045c2c000c02004510710855040056004e0307911250301054060842d049041c9030b28204056030004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 51816065 1250 51814815 51814817
    0x10080f04230a020a050a0312120605040216051603151107020306100303110d08150402120a0209040f02160206031015020304030209090c0d020f0d0b1807050a0602100b0a030b07 77
    0x1c502c044210300c0c084554400401c421124000b601f802c0d034a60425880d4161102130074451100ca4003011207072035800401c000d2100a004540399204034400c0c59a0480b280c404942d00d0003a01d04241d16194040c140c002603c2e00080684042402510309900800c5c0c08042892006410b1060300010f17078040141500c2880c241017070803a142d18500d03018100c00d645000c040c055401c0030140099503581700c09000c0d4400c00e1041969910410b000c0400d00911610f1f440310910030fa00d00802c00100e001c1d400400021809580c10001d86090900032801ca00661154080400c0344640c0c000140c5001c2000d9070300040e11645a2809581d03034200803000c0f14141c1000b10140e00042000c00540c5001c480003030b40320010b000540180600f11303000403d03c42a40768024070625801c00806d00e251070b07220b0000d00c0c855000c0c021b01120304048654131074603c80720701c903c03100e88a2040007090074240071514604a5119800a010807030054180314003a2039113010360342c1c0001a030000000410405101c0500490f11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 51817315 1250 51816065 51816073
    0xc0304060306060c0308070e0114270103090203070905070908030703030903020606040216030c03090803040f030203010c0c0c06050f2803060801050603030a0503040c240206010510080f0423 83
    0x2405001600782c408542c8100d091080c039100d500082a00041202e40c04501860024203e001100050380d01d01110421440c1c40d64002c04e8640c210f8490000403842c1c44a0390804142c084014001182a85d100300402074040e04071500c03c1000540ca038020a801c04a1802d00395a81343d00e0f00c25040c5103400200003640003d8541205600341a014003600781c01c81c0c01038030154500086007000030390301d0400d41c1c80282000804046003060501c1240315101034102c51080d25035855489040c2c0703411f20b42c0b600090b48203518007440006102d004603a80041e40f94030804000b189880e05038107441603040450034080f082e108103d12100d104408042d00104206100030017811418458000d04035040c0d60001c020300c0c1c1c586028407602e5603000040d101080450720f4456926911450114040c40a5a01c03203511800c030b50600c0039889004d0030000300d44008660031196503070390352000c1052141e80000c2c2c40300800e0210f000f190038030903d07060300d95006004103c0c410781e64800b0095407000b00181c101a220b5504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 51818565 1250 51817315 51817319
    0x80f160509061b03070614040c050f0310020307090501201507030906090b0a1b0203040504090201090302090f06030d0201060608060d0609020d03120b0105031b0a020f03121008061005040f020904020c0304 89
    0xd882400c1c1d0b0107801d40d00d0101f0501e03007540c581c100d00d5154020700b40b00b841071504c0008543d0b0204591100c00705062002c1d512030406003c080c100390340318080c00b0301044500700010440307486205038802c0155000c0081c00c0034003644100344c1c10480090020300415407240e00d0310012441c14051425210f10031034150203e85000b030b0003071003119010b014903800020740000e07170400e50380e0002c207a4007603e00c2101c001a10b1041d40c801a5881c0750f542c0e00080d04803c554082025051141801c03904c60001a4181d07400302c41122812805c0303603654000d0b0008038030420089511400c12103a86a4018400c0000041c86403140d000100c20f19842a000c07000a1504880505860020700801c82d2400003824044d00311f050600401d150070784890b200e00c1d0204000701c1d0303058180b44200012960303640800d05407980e5001c03082c007014410904603013a0b1010743c800580090b0380000000c445100d00c0d09007001042880c200302c04c00003d82403c0101000840d02400700c01007560f00c5100410700e5003410402141d6840c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 51819815 1250 51818565 51818573
    0x1005040b0f010618050103110d05010807050f0306070813080d020d0b01090501030c08040605091504050606030114060303070215040b04081509190b0a0914030901080f160509061b0307 80
    0x100140c0225040003c606a201e9000d40848004c60a6031401d00340850000340c0d003201254a07005900142d41800c0c1020000140098041194010390340140d500018000703680061543e01c02007510400700140c90900010700e0344d495a410729441e1032217821414502000da07410403050307811070181e00323407072075500c0f81183c1d45036030003012b400010042800c0c244540e5108000281c405880180050300366502d8400141c8810800d01c04201c03020070038200848c9a00745800d01940d5968100c424078020f41c685034010920403141c6030064440d4600030001c51516060b907003884070040c00001d020011610900c004100b555480010b880900200c0e00240a08408103000034141c0c10b000c0e007912010303084541c18095256464415400c41c6070402440307140307078494071040300013445003820203046184081704c214030440000c0f00606015509031785100d9940c440b640314400c0088103480b640303044c3c1d166a001d40e1a0314015000f500000000610541c24020f13484030003045550300c00106092900006001c00c100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 51821065 1250 51819815 51819841
    0x1905011d0f010602030d0207020607080a17150d020d0c0801110901141305010c0c080303041109070806010219030e0612040c0909080405010507110a0b0306010e010302130302010804051005040b 84
    0x8076107488940038180d490b00384040e403207216020400e180340d900040c0c20790554943d10201c0d0f0100703034050700b180d0b034608040c0c10050208040403045070948100c1c1d00840e11000f0700f4160052420401001034024483e25070030405d038544101d00c01c890070f600512000801c81020703c6001004500220a2a0341d41240c01c0014000346000e84030400c1c2c40d400703100130f0341d4024007c502c0b5001d8510a01701400c80c1102c6040ca00340c0e00e1500d600c40ba15501c0004108820003010705040440100c040c1c1d50021151600102500c0d24003003100d05a006a01031003c20039418050905080310303500a05007140a0002c400c0071481c10b84c000c0e405981c586500d0320902042107100e100c0d190040c0201c1004002076010355640c0c00d1903102d54407459040200100d138032403c1c4a010803650040840007082e0303031250360352102104919001125a140803032156100c3c0031942d4024000c54481a80100441040701e08550040d01d96003400340040c2e03103a03c01d0710a20310040c900c80c441e0074002c41c0144124400c03490803041c50121 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 51822315 1250 51821065 51821071
    0xa0912030e0d0903050a12110d030614090402010c030509040603050609011d060c070f110301020a020a03020c0f0a030213020f0a020f0705060a02061603150f2303060c031905011d 78
    0x10041180d00c01c0000c41c102003805015264440e46400a00040e00021502230380d035a8450b40f02c0c0d02a404410a002d40c141c0c1c40b003811505403805641180e801c01c000c0003143c24084802034007180f110307000c01c0c000074072842c02041700d240c0043c03001605503100d0300c2d45441c0c0002240d60900d41e0b9510481000c54401d100c020011459640e40142113520b40f401e40c11b1258004c0c4040182211900350103981003001c0000c0c0c0421545000d0001c5440e144902c20027907403100c11910079070242c01660031209050070006d20405802038040c0001d4480f03407840e400d000040e0040d802881030750741c3c00e025203800e05603c00c0c0102004019940188014401034002078206180c0d079128900c1904204041d03d201c03074002c01d6103680500300450000449134034080a40c00390403000c9003142c054074207880c04500080100d10110076903e440e900025108241042e01e8a4403410000c40340d071640c0100e0000e03000c10032041c000d40e440881c1c05000d102c580f04400108003925800e070800d12115a00380078254840400c00c82c01d50f8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 51823565 1250 51822315 51822317
    0xe0d18050301020304230c04050403021c0f020a020112090804031406010b03040213091103030a0201021206031b060a0507060609020c01050708151203040e070e0307060c08040605030a0912030e0d 85
    0x114504080d0703500440038085032034891350209132006e02d0950356818440c0c0c2c000e0000c060000e102078030381071800a413510055001c0034903011031582c03505403161103180990f10000d825001071000300859001500c50b8a481c00a1400040e11a040b910008900501500c0250300c25046602504030004a203030802c4016040030404510034002c0001517500c92110103610300403418001010101e038185421040e078040c50240d054800000d01004443e81540140000303c9044044e000d99241e81c0200b544903180c400151003001e861207002022407600d0b1009000c2c000c0381d401c3c114580384103540c48070182d0f082030f809410b540d40e010400e0020100e0078084c041d80403410f403410700850310300f075101502420340401400b03009040104008540303400c200101c0e00508852900c0e45500e01d46007000900c61003280421900a0103070b000c002070b0103030040c2c41c1d00800c2c90340f040c0c440303080c1801c0800445031504002c00e03101c50b464841c082c81c80401d00c1c1742c0e4503508081c0c0075038001c940110000e184501d41016000000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 51824815 1250 51823565 51823567
    0x4060507030914030a08180d080901030605010e06030402060f0409060609210b1801020c0f01050a0e0a21091212020105060f13020703020a0b090705010207170d0e040e0d1805030102 79
    0x83c1c1103560200d001c6a030554005101525000d810b4081d0301076444c05070003d03400040c5a00d04c0030a10800401070b007521a02641d041c0b241603180e8004441c2e089282d02250303004031085c00458014900640a42103000c0e44e4401c8070708085d0b0312a500030945401e9405080490302002090081c080700310080003900003511580980e080d8107075284c2c8404400200210085080742d00301c18041c10003901150360100510084911071001894a07500800080d1507100c129450021083d80c1d407100443c0943d03800f5005100c1c0c0c2840680795110b40c0d03000148000d85820003100c1f002c04a084c00807a5100c2d0300d001d01038015111144080c030b5010303003124000303040385103e8800143c0703c0f00c45980b10341d44105c445132112405a12076025146c103900d88070340340300001e001c0c08a031000c100000c00000350a8040321026800c03103a0380b035554120f0340c9241c0344c04401102c030340d0000d21000c2d043c940504031a464800b0b01400000d5204040d0803281e003480c018003102800201604545024034030074128140140c00110021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 51826065 1250 51824815 51824849
    0xa0f090f0305041a0c0307020111120409051005030f060a0902011403040f0510020f040302191212121103060d05100c020102090a090213030209190203011815033203040605070309 78
    0x1c0346d83e805442c100904000303031104103402c070f02c07000d00000540b48004a0310715250780e195010207018100c1102e034100001c4004800013814500043d401c10490469805000207854000e4600301406a6840580c140aa41d01d212458444140010742c4941d00401d0b2010800685150040c03e0140c14404449031500511501403030f016150304450803254102e5022651280d07513144a4000d011b01d5124550b0107243c1450241400780d0360501034050310032a81c0712401c41c0707107110300c4404841821599007804e0704240005910341c01c007405504036240c0100120342041c401050420165546143c44000603500840ca00c01d5900340707940c0303203030251120340400c1d4100201d40c40d641808404600c00640f10301680c00c0403c06a80d502003040100c182005015956581c47c0c0b40300d1504500c208002598592402c82c51300041c00c0e088201e941620303489aaa44002e9007080b00650250303040706200481c24184805d844440b520410040006080584420b921280c0c80c0c10050081ca5883d44084039800d410b03100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 51827315 1250 51826065 51826087
    0x90a020109120c0e010906170105010f030807020310051504060501020a02090406020a12020a080411180c2a06010302091003030e0603070507020d0606030b090102070b0a0f090f0305041a 81
    0xc41c1c042d901c1495410014100c01d041840180c083c03503012803030f0903450030008110b01202d07410144c1901c01c1d0302c4071130348454005200c4a00720f030f5092050584002825005200050b2840000d044e8030380001d04a40701c0c840d030100b2a0b02240d80598412032850440d4102c00740504080c054040104400d00250200e00d01300e4010031880c0328010001001960300050100e03801d401140c9054034891280c80864452010800151014400759810384a001c1d42807140102482d000e0405890440d0036960010180c0300c5004413074040c0c000200e8404012011051100070078540c200701400104040700800c2154514018807901d050040c0c40d25003840444035041c00448c1d081204450030300703010b5840f2030342e0b40e44001c002c8035240a040402540014040c10250a1080c07607080350b400d89001e0401c0904a440349040a401c030f104100740101028524000181101c0e19544034a0f40306048040100c0d1940d8150723268285040290343c102d01046011a040c800c90301290301d04414a1000004107181c4545140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 51828565 1250 51827315 51827327
    0xb030c04200d180c030501050c0304030c030804170c03040504050105030a0506011406090909030c07081902010c0f02030d0906020d050313080d09060c05040303021005060105030711010902090a090308090a0201 91
    0x1014900580055001420751107039109100ca24903101a41c110f1007030600c0e00c641981c18601c010345540d030811022548000840701220302850381500c420400d0070072540c042d20b140d035000f40107076840c00c3e5550644503810300d4a4000c0195038110300145075128101030401041f10810307002540241d10008500000920001c0d065040d03488092899100d00002070001c0c032648104109180c10001d00d00521060400000c003820b4261101c000392130303100d9207810103d42e4035851f000d061400e401c2018408400355020307080e1280d0f89070240c03121911603041ba4000ca071620300f51031380343c0e000191900c40030484298103201d20001e10b01585007092643c01d010610012a0300b0807080a051070100245110036406194401e1100340d034008014401e5121160000e000303a00705110a4002d800348c0358215580d96101d1003010300c6004161506411604c03029030890f4407020b8806280d480e03659032079130100981d83e03054240b0f1007500c044901007902c0280d440c008100c00c9001d004507510780c0c84030395202e00503a0004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 51829815 1250 51828565 51828611
    0x3060903021c2c01140309100903031a0d081b03040b0c03040303080708010e04020906030f0a030e0a0509041505040201120906060f08010207031d0d060501030b0405070f0e0a02070c180b030c04 84
    0x1c01ca9101d1f16801c0c001e50504050302e2040c41200c0c64082d0100070190180c0103140010395503001c54054050700c40901c0b025140205008200c076908103d0151783e00c4000c5950b80516400707504980c281038849003101220f50103851000110b501c049010000c050784180b001303512215605c3d2070007036540f420303181d01c80124001d080284a8004040010140c0d00c081281c9601411a0021903082c0901030a003d8080300c030315920a8081d507800034020940d420032030440d9000b940c2c801c11000415121111000040030302030401c80c10010001e442d848075400324050408650b0050b00000380751864030b00c403150145042e6120001c181d00522114020035000b2003da8007010048120221110100b000101c1052009500410340f5207003100110606c205285064885c40c401e4044440d100d03120000109540e566110f03415554281a000980e008525000703002201d1040007007060329911071420b4115003000e2001e0f42c804503550004001076203410001a8100c0b00c0903a020440014512545031007040c0d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 51831065 1250 51829815 51829847
    0x8030d0b060408100902010309150c08150310090302070b04030303060920090d140304080106090b010801032102010212012310090302040b06040803041d06010f0903060903021c2c01 79
    0x20103803e030559009400c07000d0140c0d0300240710352043cac1c402a90880246a115400b0300054420000203000601400310385c201ca54006000703114032000f002114000d001100000c90842c014507030005100030042014102542c8241c030040b485030b08200c03024040315030032490140c010700e05420060b07500d40444221140400b05035003c0c100c0c002d00b2b0401940468111494041501c00010b000074003000c190301ca20280c607400c01003401011b8040004554109007030002814a0344031303403c0034118000014106e01c3d000464000941405481100720200e603200340e1000340d85020750070755aa00281c0da014142c010a108444903800381d84c2000b001407050b003d601000340210381d1141161403580e030329800d44008122400440b981d46884101504001400040c1001a40301d54004280c140d8060065000f00030a1540d0f0105603601e9625494098031400c0000da0950142d00001004094610340710031624049440f40080c920100d55034400c004001501003500400e1b11354407401684e0321000d42d848880310 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 51832315 1250 51831065 51831071
    0x903021807091a04030203070504020708031303170f040219060e04090206040b03100e01210f0f050d09081501080606150d140604050f1b16050708030d0b06040810 71
    0x210740781902c034550240c01c50008200c030030182e0403015080500030310a0303d01c00c2d13064a2003140e0700c00901040c0d00540000400d1f1900a2001480c10340072901007035000c50203440e02c100702d40c07001403111000050684002c0d0340600b1074000c00c0107600f46100f045d24118034248900a03642d184ca80c00500d041c00b10301d407080c03180380c07507a16000a6540d83c81c1a1030103042c3c0f004603242d403810600400c1d180b4003004d10601054041a2000040c0245c03076150303084503c0e441c1c80846c050401e182e610345a80070030424045800b14070038401440440d00400a110314090f040c0c41d14500f0300d09159405286c00d651403885100e4010b00341c01403002d10f9010070b00340e410040544400360521a5000800218024a044107091500d4864610f0500d040c00c1c1030b00d40920400d8808102c40d449400500c2c01030003044820401c01031403c060414100354075402004a4000090460311400066a84504080013036000400680c00850310a60390101e41c400c0041114044030b0040c03410f46040c0842d9100d40d840050421010743e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 51833565 1250 51832315 51832321
    0x60e0a03061401060e0d15020d0f090303051b040617060a030b07030b0a060305131112150613051306020c0705040606022b05090618060a051909030218 66
    0x654210000180d40c0c008000e101468006500088242d024491000000c0048004622509028110f684442c0d0041ca4070581c2c03801440841019522080d9125403095035800400c0d50803080348200c03100d16200b03030b8020600342080440c1128074240b2061401c6550410441081030130b4011105004a5030f403805c0b0b40c1d45550ba48000101e82103019800036140b14058410420703096499030040c90a007504681350f12585885c2c94003103046034001c6400500041e0402589008103800c0e038414902003400520323244641d0320b640c01e45810028a00e1424101144034020701c4002d01d08110380d5058000c2d094810403080c07611540c180801040302c40c1c041c1140da400600030040360b105119076006014003400502010369a40002950707003a901c911703145e103400070501c0540c42c40f2025100e10302454055450605000340401088031903804401440d01c2042541300a041c19190032001d0a00015076454080c0c440da07040c0810141120301450311420040044014401656440488000c10909903d0420156 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 51834815 1250 51833565 51833569
    0xf02070203071a0901030b180717090d091701110c0703020f03010b0f010503100f030c0501080708090c01053001031716030806190803031b030105060a0c050a080d060306050106110601060e 82
    0x713504981c401036108c0380d0750104070409402a4021071030100c0d0003100d00c41907a59081e40343d207a60785011128001100020100312400314116004200b0100a0001680303803001d0f4070070912584a403070b01440c55004840c0070019072400b241c61400c801020b0b0002e0050250750b5001814000807030051034180003003c80441e80c4030410f001d010300503150001d940c00e6000e03101d0a180309003140313901c0f8450000fa005400240c1240c400c246a5018040e034000402d601780b890380040d00d06030400c0b55685400d00b00c80f2200340d68441d09030440c2d895101310380250f880c1941503003842582c814403450408640d0703a00700000c10210b80c4140c0e000c15000d4040c03401800580303c000c006981c010000d1241852840912070110b8074200100045000340040c04000101c4c22100d80858114002440303284d51105050111180a034040c0c0042074001d40314a0640e90022456910182c10360400e8110f007040590313a05d801d00070410310b48540390140c0514140100c182e45180d1204c0e46d240030501a0704100043d901c1000c42c15 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 51836065 1250 51834815 51834829
    0xc1203041406040503030a050624031803030a051609060203040603020d0b101107050103060503030d1d06040602070209070504050d0221100516090b04031e060f02070203071a0901030b 80
    0x5807030410564070386040c98100703ea565081541c084800900d01000304a947c50807016903403464107800e20140070030652001c540340d5600010040071075040307100500c0070700700003c0c0700030362064002c00400146800c00743c900490030b60f20b00040707009200200e0800d210751600041980d0888115103009603441d60510309080180c40241c2c0d8a81c0c105c06140c112406c05504040320b000041d0510040381e07140c503540e100440075181e00e48580e40d0190000c00c13420000321100d40000d24882d001840001c0000741044500385040e804540c02d8071131542c0172401c80c08524001c6400358000b1103900e4000c1c1040e04140c0004c410003010f030320080c03007208036101040c012401c41880c2c400704507149055842160400554001404003191884100311044403007a80d0140030711005030690749420011420141942d80740132a4090b1100d20130902402c0c40700314000074016009000c2c03640300780340000d615008907205051811042c0c0d0440341c140314980c03000d4140d9002001c103490312540d0074a40840c100d140300300480c000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 51837315 1250 51836065 51836093
    0x409090201020307080403051b0402030709121e030f030e010b0901060507052104030b0c0703020a140111030a021810021002070309030c030503040e07030905070303030905030c070e07020709020c120304 88
    0x1640e030120700082440b80c0442d94003404527180c19000d40c2030013140700f00002c0344421281c0c40301194800005000490407152140c4865108180c00c4204100b01e203051040c200040c00201d0003d407080c03d042c031390207030b044c0242c074100744a050003486030040d040001250300d0814083c0310100040480c0d40010f1000c100306402450b4076142044d00540c40041c412035207a0710074001a2408180780300400c0035060003504a0300c5142d0180d002d00a001255a01d0790020000807d20f09503a640310710840c01101e118400860041c4e980324001a505e246040c00003443d4580d0100851047c00200002403106801050540034004141d60050769180245015242d0b075150340c00103004070940000202c00c0041c000000e00542d1403078551a07071145c2e41d120702102600ca091030005d03c0ba800150003040000c0c000e0300703d425100d104500303981c10405401035151402c111580260500a00316060041658040c0301aa0140009200c01d500d402c28002c00142c0c2c41c428000040b000010001c0045c05002070f030040040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 51838565 1250 51837315 51837323
    0x1e06011202040923070605040308090111030403050d02011409010c0c0602030a1d0f0c1507020609010c02040c0e1905010207030809011b03030603020a0b0304020306040620160b060306010b0409090201020307 90
    0x111105200c5018100404e82403460041c882c2c00360104100d070103682a241241d80c031081192820350200011100500c540d0000c220910040c040480010070912046050005079400014070003440e0354027013406030b0050800c1520f40d01d84a000102e10703510000640d803594103c80056541d0711488030310740003005200004060368010411444d08517101043d0282455071083c101c8465179507440c00c1100280c003440c0b0903602080308000000050070100d0103424506c4050401c1c82440840f40c011400b40c40440b0791010008000070b5104110389068500c3c10001b48507008110003440c10140041e50740c50660002600d96140410040100d81c860b0400d402d410809080e161140d04c01c61a018000d00941d0008074441c0002e880046501450442031f2485160000d005041c56103941e00d80c0f00c02010540b441c5001d580305a621981c0c44056540103050620402980c00c200d6002c078103100c40d036010003400c0d0620a81041004201c8071000100341c40a4a500841c005079200706840181c3c618071405d44020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 51839815 1250 51838565 51838583
    0xf09041112070503060106020d0516110a061205010603020301050303070f0f080c0a1106030601050406080406060b0316080c070f0308070207090510140103060602030a0e04020d060905091e060112020409 88
    0x48140369002c600c40048507015401c48000e82d88642d000e80c0c6a205420b5a03a0003c3e00512141a404c40c11202c00030945000d14120f215440210300482d85d8070216410110200380c25441105d6071000d50720404c0c4c01044180303070450841d410100000c0d201e2240c000e01a2614001320604810700c0600340c1c40411256110000030340d500300380c1c2c2d8050f8446140610aa0704c0b00c400300c04da00c59500740082280c2c824001651824601420180e06440303405c1e000d0815a03d260743c500011404400b54001103008101c0790305200003a807803200b0001e000d081c009004000c07041046c01540001410781503031445082d41402c0c41c0c0d501d60340b235010480c036003c010303880001c10b142050203020b025000404039400b0b0f201c02c801c9401505640d80b0064054444512403900168010440026110302c01c58042071035020090000d0724141c0c80e20382c1442500d500b0340007011b209944a0502c81045010407841e41148a07101801e607420005002c00c9484002c14481ea0340514604618502150380d1b41d4090143c0c01d0344222031b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 51841065 1250 51839815 51839839
    0xb0307030b0402011101050408031303050c0d020c040b031603020d050f120406080f040201020601180902040e010204060f14030105010e040e01090605040b07020a050303010909020f0312120f0103020f090411 90
    0xc000c81c031426101640401c840b403008084028042c00742a1040303803c813100c00c0c03650b201e03200c03000c0400c018140180c040242c2441032110000d810300400040c15042d1340202440070240041008232806200707110b100750300600c80010f00030428940e640860350100c0b010800100642071041c10701c3e21000c0c0c1e00003d401128045816003108030040c105644182c0c0c1e170042582e462042560544105982c0640076034043c0004100c1c42e0704003540f08481003680b01000c91a003101e9030100301694000e13202c6031103a0750042030034491036511089240c5200030902e842020f16041e448441030510060003041e041002145e1841c6103a01e0b02c2d000054034020f4080200201e00c04c07810144010b2105450448150985802141c0c0442c4000381c0c0712540c54101010350700c1d41c0d180c060074a000b000540f6003207820035442c10300602c980e81d09015403414051485405070359481c4c141a00480302400610000d81c120b1608014005a25000c04001c4101317001d942004180c1c6942c24900c079200104162542c0c440603803408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 51842315 1250 51841065 51841073
    0xa23030303131a06090610021c0518090115030b010203090607050f100506062a0607020708070506120a020306040f1b080c160b0c0c030d0204150207030b15040b030703 73
    0x12806449000380350440c401c03c541c00d4080042e80781540d44036404280180814004d1406110a0580c441c041c0100c841101c07960128090710315101449070081000803400038601c07a0411115201c40804480c005001d41c1810312261032441ca510b240020075540342c0704010943d001708100c0e1081d880042c44103840b2000c610740a9641c030b4403031080c0b036840d0045820846102d103c40c010a030282100070031690030018074510300030300721003040020035803055000c00d200e103007013018001140149801c0d4040e2020758140b0010f07a250948591089018003010444824191031408419800070388500f000349c0e8035228800003074080e202843d1305070740c13607468800d5058603400340541c2400e1a600c0c0c0c0d1685003807a9515403041c2028042e00c00d5028100e40785461040000b98010800c07640151045909414018202945491a0012281d00000070390003e4180003031a11256070102a1110340300070301e00f050031513640c550404000340c40c0120450f140c5c4c03a400207603a00c43d0002921150060101d0b21700560fa820 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 51843565 1250 51842315 51842341
    0x4081c0608010b013917032e1701230601020c040501080c040207031403091b030d0e01120f050f060406080601080607050702010306050414011a090a23030303 69
    0x45645501d61800d04000d44550151030035280301e58003440f1505203940c018048410300e03600d801c0128002000a035010000901c06c0b41410512010303000a1a12464415030001503400c00c10721030b450b005000c19190342d070b00040b010710009840a04207030203116100881e01c24090a0000c40c0801d01206601400c51340c1340c2114240c62080707509900701d5904036562018881255000c2c000c1a00c00d42100c901801c080c10300d50002c185207882850115551001c59110b20025007094541c4050b075000072150002c0c00800302d2040c2080f04045003d0503d9440120300503140404004031941405920445502104c00c0303503109410700000d660043c030407440c003036200e4100c1c0c00c002c55103207100318079295003c101100300061840c1a100300e00000c0090342c8503080191603603000040c04070704058a40340082a2a191406640c04034090504020343d2075050404804501c06042c00103628000e0070f01126a2550f5002d084008940100c21b200760036400242c1d13a038201070b0299640680500c0004240088415084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 51844815 1250 51843565 51843569
    0x11010e10020a061811061813050601080c03060904020108100807080f01060609030f110f040912081f12080706140a060902040e040803061207090b090604060e0c0304081c06 75
    0x34104128a000e54465004000601e102c054044800a032000c86941440b1b4000e06030320803000158188103050341e001840a41800c1021810980c9030b40c04e001d81540c00a6506800066181038241140382440205012010007003000c0c0c104030040c030104109040501100014012400640c1d00007a01c91411540da520810306d461010341c0380030b10010b1014070510280c41640c0d8013104d00640b041194681030448198001e081e41c1c040d03c0c070403845003260781c0d500c40d400c0118441c1c2c1d00c0c1a031140d03241002401e02003004124101800441b50000400061855443d0030380381076001a091546d464100200d8a004101000303001610b4540b40340d03100158840030034412410b0207020701c81c10352140b003080281d01441c490f001da09402c580200e80040d4944001c0c56104401070003000c2c4030360301a40360610308030300b56005c22170031542c4100c0010942410010207502050544090120b54a042081c2030710f082d0040550350590300c0400450300304150764003296150302c130301c403403c004140c680c2800d80000c0400f8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 51846065 1250 51844815 51844823
    0x804081c0e0a0308221211070f08011a0a050d051c0215130c050603040201050c070b090406080c030a0803040309080a032c030606040b01170f100b040305030711010e10020a 75
    0x1030000141d1500c0d07011117078041c4861242805040e00510380e40c6d14071107104c1055400601954244091980c02c0030007014005005048a500d80c0038a0a2074540c00c6a4020020400048940c00e00c2c06240d1144004e0004035007081e03a0703201f0050203d0515030b0a001c0d540c482d903260919071001d0320000c59400620381ea42c00c41c1840e00c5940b00e882d400c00044d8483d510003001019031050b05001c00280c50024041c42c1d002d0300604100f0f1400340b9241101c2c0c1001c00300e4000400d00c0b0000b00b18810385017014030982e405400076000429950511030002036640358501001001584000001001c0501c1a864140106202c03011114020414503015000c190151000910107602824240c00140440c01061a14034080d0103018107071244024800548440c80c030340c505118100186034001c0300003604240c8a180340015000d582c2c18400c002145204460f805255005428441031010030000720880b0000740d840102524250020b00058542d501c03e410b605502c960020181d03000c507034001c00c030b0400d9980f207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 51847315 1250 51846065 51846077
    0x70201090636030203030c010e19081608090604060f020d0801210201140a05030405010615050301140a030b040303050411030d0f05030907090203010303020a060c03020403030804081c0e0a03 83
    0x26900300301d03080c04000070003042c102c8100c002100500c1c10b0030003040c2e140442d02d41a894158981d00800c0c80d550111a24041c507a5440d6480c01881200380036400e114400d01c04414140c00ca552144503da00541c1c4420b002c2c2c4641c88001c0d81000b0b0744400f1036101041c090700b5140c541c0d90301c0340b0150402c034100c000d00025006d01500341025520030312409051fa16a00c4421104500700112210007d0b107884d4201c1c1441400f140e0081d8413402240940201202035445981d240b51a107401c5081d03c009600000b0091640e06d0903640c225000342c140d0303054401100c0c0380054542a600002e0f904800c1e43d001034508182001130009065142c0c100c81d20481c021800030341c41404010615903141d103600800c07000a100401c0b06600944981c00450b00071000d80200ca0075503480c0c500001c101d900030b80c021009039110300c84110030462280103000304000c00c1c1c1000c40c2003d1031034030040c1240300c0090004084d410009401c1070010042c00c021540001d149100f080f240001344001a42d88004800c02d03004520 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 51848565 1250 51847315 51847319
    0xc031e0d0f090206041412060115090e04030e0111011103010f0e1303080703020d09051c11010606080105040c170103060506030c0a1508130f0606090b01050a021c0201091707020109 79
    0x4040c000ca81d00c099020b4441481c0500e03040d401701041d6508188698441e5100c03203001387d410030420041c0d0180c040c0410070b41403500070b420040c0c180f80b090f80c40034000b00c200d02c04002c08a0341001100f60400000e00b0881604401920030600510120b150054159404800860402c80803117144060721848d0789004120344034820042e8800c01304c4400100056021800140d01d01d200b60040e081030500c0d04004140d48005945050601c0c1d8038500b002d01d86500c4100e200b404030341c002440c00303262210b8002001316034203004001307000c80c1e0b050149034002d941f1a01c0c02c0d0009072003410090003210f04d81892000c00d503160300c1c1c10009000c09458403486480394070890641490007000c0c0c90201c0340054070201500c181d0ba84140e803c102e004100303d0000e46c03581030000c04508103940b1034003101c0c8108030006820703091000300011600c244140307504010b0280031004070107030002501c2412000e8109125200244440308902600340e2203002080c091fa01410111449800700103403038040c0c03007626100081c503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 51849815 1250 51848565 51848591
    0xb041401110a02041503050f010903080c040e0105010507030903081306200c04050c0c0a150f0501140904050f070603060e0c030c03040602070c0b0315040608030a0210020c031e0d 78
    0x4141c0e0403031040c0d50300500c071070707000525041d4402031036400b004031130044072503891300c0e06810642e290098810b182d4640341030b5020107500c090400d500000660800d0b00b41402e100521080b40c1c01401402e0500200140800615004c1e001c003d00031544034109035650904040b02c80b07030030001482100c0c045103003003a846600f11424040603054a61742c400800741c4110b000c040101814014228404203d41081500000c0c0020f111400c101c5025004980e2011211424501100d40b14103080900d68075110040c0a10482c805800d26030010440c0c00740300c247c0b02e5041260420104e41050600c0e0300c501a400104030350140c000a08941c2d038150301004541c3d83d240f0607400c40c40f0480b000c5504c43e401700006000109030b98050201913000c2c00c0d02c07020654803140b005415502c151008507810758180c0004003107141c240920300282c00007001450403d2000c44c0007940d150310302c45018850513004180702030240700402c2628609147c2c4010352a02c0305104840b4000e9520104001240360f0404034510440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 51851065 1250 51849815 51849827
    0x60c0e040e030a050928030b09120f0a021e160b030108030403030f0c0c06030501091d12090d02210d0302070203030f0319110301150c0c090507020a0602040b041401 72
    0x21120000b55141c040c240b0800c413910b03070001411940c030500c0000424505100b03851031404080981c0a2803003941e04500b8043c1c503030000100208031716403050385400080b0340ca22041e5090030001462490300e5203030044069003402c3c1640907011070150303001140342c402000010601001250802000c1c100c4d500d4032403004440c0300c00d0084007000d602c10081000080d00c25245031544e0001440d007220707005542c3e40c4000c0508a281d000c2c80000c3d4a0310010f00c9820b20502c5801c00300d01e24641d816010010a1010a881e09a50a4000700000340401c420202c1d442d50710302030003d1940200001c240904003510717060009140c0c0c408040c4d07840344251903507005001e0704c202d030440d940040055050040306001c9800c1039000a216616080d0010728420700b840d0180909942d2042d8100095282e6042000200160107882551010444070003104004540c401c9140010317180c2c48840030032241d4039010b05a1500412200040c1218400180000c01006480141055034200d0b9101c40f6201220801140d49c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 51852315 1250 51851065 51851081
    0xf07150c050601030f0203070b030c09040c0c05101a0901080109050c011d21011802030c0402120a0f020702150c060f0f1501120c080114060f0d05040501020f07060c0e04 74
    0x6500c030b200144046003200c5a04c411251000b41103d046640700c2c0710a0f0303129003055561022034000481c482a0514003401a1954101503103080c0b0306410305510346603600c840e90f00b00101e40c0d5564200c101c80170003420110854480001d441040d017565544d80045c000d0800c0d00c3d040d103440c01203440c00d410b01c0d803048100c190440000d182005010400d2010416906000250041c0ba04a40800307091a035030f0a010724076040302041c540840d1154030b0f0048c1030a0883c200d20a5209500c10010050b51010990040380c110032a00300015101d24280f50400082c458032001950081c00466090107010701d0300e0003883d107009020305503000e43e25640e00c5114286800d440c16410070603842d000038100da80b404588807046005140050307101c0c0e0301c058641c00b03da0341e440d0010001400200148040c034051307810001142d005a600c203240084801d4210003501500c10341d40c0c030300c1d61144041000d00c042501a1400148261012a90350724640340641c001c044e0401c0c400082441000030304110314180c030515030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 51853565 1250 51852315 51852323
    0x9060512070e0709030c080d1706210106030228080127022206060806060708070f03050904020d05010815040503030a0b210705031b01090b030402010507050f07150c 72
    0x181c1801c1c16003014407424014042d01c1005240366001010a625620500040ca048000751004403404000281440000000c60740c00040071820b0080c9503c03500d008001140342680c186004000269556002d007a40d64400780d4051050004060f09510610246036601d090f11440340c4416964a4000d0982e01200e403840845840c04910500761044504241c4440384001c00e01c2c10408403440d010b1101c1c015094035007007aa41e86580034082c0325000186543c0240d030403102a41440031503070310940c40d48607201380140402d20b00301004003090302800646000400040c02551a40300240c1900002c1000340701e00c2071140300e0f410440c0c40b002004040f0502550308000a1495952060071200207401102105500301003600d00c1503944500c2c185035540084840300241240d649030504042c034220201c14503001800810003400f1582c4c0c0c0014140d41210301202500c0e23140d60311800161054001e040b400303030050003440c200029003040032a200e02500c0d1015046d94154030020303004c50782d003462104014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 51854815 1250 51853565 51853573
    0x1b0c0105030601030911042901021c0f0203040e0106020a0c090c0e09060a05040207050a02090601090b0319020d0e162c0603010e030a0e1f05090d1401090b0109060512 73
    0x80c030b055209400c044030720f50061007070341801d04000c8003003005ca0b55020a50a420030349407040140085807850442600d040034401042d00c00e11100d40e5500d0049000185018002241e07080340004c1e00034410b0b00c0041120002c0d5101c2d540e0f5640002c0c0d103c03080072008584c032022154002ca500c411380d02c194024100142d40b4100e03803421480501910320300c082c01e2183d100b48003480004465546000402c441c2d48140050003080380d0302c0c4148210201e0150a41d0f05004401c0000d01c1751042e01c105603075021f6042070b144044200c01b00a050028403c1455078610242030000800c030314040090031180003108a40d02c440d00396940d042110844c1881c0390b00501c5000361507565001d103025154101d800000c020000115000300d14103152455001c9018000450901c5404c1c85d254642061250035440300c0420403000000460320051403807040107101c6100d049005e0015007031044001c141030f00d00c01040001c019030080c034104818180c800744100703c0107074105500405e41d401d000c8040110809000020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 51856065 1250 51854815 51854821
    0x608070c0302161706010815040b0a0603080a1e0201021c0e030412050a0308060904020a0302040504030e04020d0f060f03020a1802070f0303020307030506011e051605121b0c010503 79
    0x12240699201801e074110710810244444841c0315996201c0100b0300000001c107052a50100d113410301005038465112070f000340300b45422024085803416441907100003807914943d180c1091100038240c541007e0200c51020420621140d00b00d129041240d40c0c41401e0005490b403010100c0c241e2141c2c1c00c020f81691201c0711004d00189454218000c130520410959040a8403200d0f001d40543d1016000d031556400341d4540014945c015038690340054040d2210700b450301c2d06401050b201c034400d00c8001c0c0075598450004c4c00385441281c4805a16000030300955490800550950103081402481c007801881c000000980209001c00f11003203940c05010014a503203082d0380c0300c3c0d03044000b010b0362017510780800229000030005107810028500c071744c60040c2c580c280103000508441d002480d5505002604440300d00a8050840040c002c1045203001580d401c801c1030380a0044454060003020383c400c400c4d5060500b810900502203104035001d8400e85c103031140000c16030f915400d550301408600e0401c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 51857315 1250 51856065 51856067
    0xc15070303020d0e07050109060201020403020f06070f020306040c06020111090904030807052203030311090306010302060d0b0306090106170a030e01080c07140607030e0f0c04050603210a18060807 86
    0x98142a0301074140142010610014071050380d041c40c402da03040d5040118180110368008170900d01420f59031008500b054119400308a40d060401c03503262158102003030711001c01c04c004007821001a405019a94103080c03c0ca040f0915484134001c4801550801070000c01c031039248010346401060085c81040141c076952800d482280c0041c080e80d041020801030800900701815824507041990800311300c030240b45042c003d00b11504071900050450042040c0040c80c0d400080440c1500d40464405641d0002c00d952940203003030403201542c1500601d000c0144580741980810304841c0e002c80b100e218a2004410039484402083c0020082000d640f44085154803440c0c4042e440200c8200300c2d403528009072905806078403604440a80303580080d080006480d41070140d1840c0c01d0030a001440c051100420b0980c640b221460f4481c000c030790b60800510940c2d0300304038070b0001c0d00c80c006030440c3c41e5020050000c9554411400400481c407109140c60b40e40100741c000c8400c68501c2d0381c6006060b250090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 51858565 1250 51857315 51857317
    0x21b10020c2205060901080c090a0f0f05040b0603030705060a39090501020d02150a020909070203071101092106200405011704030207031509060603080306120c15 71
    0x1500208600c00c00d0200340302a100e1000a5800030591600c510400c01810061420f60740010225405941c5d500010400c000d000155056011802c85001549640c0d8548000041000540100c505424000304204410a40d40b01c01d000d42e00034203c101481d030360042456541e00c80c1140c0100b55501c2480000d12007000c66008454299101c40c0e942150f404401c0100c0c0002c070608020050a4190f07038048900603001070341c1310010002800603010ba0400c4010283d140c50002d0040d110b0a8011320004000540313507070484410040003000d040003810300d098000d5803504082d0044803d10784880c5801c11660140440304115000c0d807010078512210240c1c2204100710300e1804a84140d00c44120b5102d030402d00884a10640c00c5070030840e150f41c81d200004041d0181c20f03500d020506204402d00001c40d5010404209494011400505100d44100f50030020035000070302400c02b514003540481040711000046004d588100c41c880080c0390444030154aa420b51111a9400250660070103c1c2c011124 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 51859815 1250 51858565 51858589
    0xe0c0304150203070f020d1707030e0c0d050705090c0f03010306090303140a1b0503041e140a0602090a0b13140d050f070501170f1302040b10030905010507021b 70
    0x740c01810644500e0311060103a80007a514100818252400080815410044110181c5841c5001c010038501d40b03805002044014008004050325800180ca1a01d030421400c804000043c1c108030a40d041420023079100d05081c040c20f0701c00c18212010880000e0802c050755404803109400710314503481c607502c01c0c0c01402e06d1035049090644031509815600e04601c005840340000450106003034605255801c180e904a031410024030030706100b07010125404861f00441003481d0b00541041c006281842d1103140601c900b4414180714800c1000f041103001e80141c64180c4042d9014030585032a0700c04c0490714060103041002620f0780a03010402d035145100e00742581100036001c644180d145894003810500d0484511019921468080260f56840302110b0032001a24001c00000d08040001e41440071001e04a40a0b02c01c0d115404400d6503a075500c2120803600007002c0c52012030700350001a025240c0700000752201d52a04000420740c900111303017140c98815010010780e0708101c00d070030010360050300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 51861065 1250 51859815 51859823
    0x5130b180616030206060103020703050301140609060403240902030c13060902040f03050c03060402030607080c12011202010f030b01020c0118050402040e04060b04060e280f0c080604060e0c0304 85
    0x900d11940661501002418410301d100300d00546070340c4070f04002c0c3c84d0420251417541010700c104010000b00303a02800b500d0540380001306103003040071135500141ea6806000d40325603218800040c00810004031724000a1070b80e0350011801d045680f42c4001500712821210040d41580045140e900c251400c0c55420f0011030600030000f400e262036244903030490300141c00c0342101c02100c04007402030110400c40072410f210200c00400c000e2a25a01003901c504001e482d070401c1c072501c400422218401901619030f00d41c4411902011981d41f060700c400985850b0100741c2c08111042c07404c040301e5120303001e07504483e401a00105540411032004480b286014186000c3c0311108040104203665103000a02c010284e0007a1040941005c0c04c01904031142c40840902c22440d01d5000c200c00c84003600b501e41c0c020f07112030314071459026211810010861141c1304d2810300b4505402d61042508941c40b00c1c10401030380d62100b48594a16007403104664060282c2c5017900e64000010700f0300d806031402954000e100b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 51862315 1250 51861065 51861097
    0x50d0c020a05070609060806040e0316031e3501140402040b0706091407050d0221010509061e06030a0f051501140907080f060f0103112805130b 63
    0x1a42e100d103401c0003984d070820380010b40550303000c002c410352240d01a60014030032102080b0b02d43d0580d46441d62445440403882c91607012114010501d4001c1c42c450a9007403a144040e10106071407003001304490048025804070318513006000000c0c2801c01449203041c41c603840d09440c01c4e401c10444c10f0401400c41a07a641c425004c10012661404140203881c080d4402e09001c81c4e01d0600340340000c150b007500c0801a03800e40c0550340c20044d65803201c01d640d2446e50159581441e445240490314510742e58103c0c0c12506609000c01d00c0201d11000a030a440b6141031210301c00306042d0080c030f480d4405025034100350300d640400c00b414013040813074035611101c3c2d10480440d0710210704000c4080300254240d000d001340550126800d0a0350401c001e103c3d90140045c58039110a1620204103000b07000c000d0441030103106243d4a40c490369000380e01000a01d2180c5c1d505549070003110301852007081c51940c841300f00030004100c03050414065010f88044440200340031782c150303042c00300f1301c2041e070880382030103403d210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 51863565 1250 51862315 51862333
    0xc070203030c07090b01050c06150d060216060c05041d09010e070e0105040c0c0206070f0813090902120105090d03090809060d14070801061b0203030d050702061008070501050d0c02 79
    0x180400041c041c0040030780240078420b1501811364103c038020307165503042c07107000c000440104201103206644a581902594120746000c00481c20218120000505042c03000403280c0608030a4402414102c4c4100400d100d002a0807104072481e014601c142c250b810b058120542d00c04040d04446079000000b10700006051a10f90081c6181901c01ea00070484514501c0050006081ca8014440d00d20303014206070440801a0340407441503c540b92010b0007030500e251008040140d6002200e24840b00c0740701c91350301252a5074001380100480b5204921842c05000b10345060507040c052030384285542c1c000341825461401c0190003500705283c003114a5070003080002c0b0300340c0e500300150009400001c0b0002d884520b951540301d40a030003070f2002082c042e05c0d900401c40301d5440400014007074518501d050110b03810b84086071960041784600c210403400c0c4401c11102650015942d445015088401a94559194030441c1c5520b0305009260005600700400d1414002613002a0211100e81c812144110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 51864815 1250 51863565 51863569
    0x6060103180b1b070c0f1d07051305030f0c040f05150d030302040e0708070f020606060901050f090307030f0c0609030b06040b0102150c190e06160201050417240403170c0702 76
    0x29104050442d94105203a070280411801b42c1a140c001e48a5051004104d10804280c007204003001480002001700020300d01003881c20b00101d0780700522010701140c0d49459904440c644483c901e104560142e1f15100800c81c101902d40601030103040c00c21522401d600704a02801a5400e040b2801c7e018190204000600c003081c12050038818040d0340d46075034032030620500080c0000700c050306680031980030f4000d0244a0b40d407142200c111a1003400c05135035403c0c8111a08005001300206283c0c540100c10001040c00819038001d0b09003131082d030311008420380780d80040e07402c0d50b082d0001412424014001504505255011412030b601c14011507222420180c501c99050320210b811441e14680498600708141f400c0c01a00701c10801801c0100d000d16444003c900700380074514a050281d12109640070559000d1000c1b81c010b4485812081010305010803440e0b9980300d000e511001c01c502c1001c038218103515108546003d0b5a2580c1c804900c480034110001c0c000301c0c00303440d14125003010010f030310041e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 51866065 1250 51864815 51864817
    0x120030705030a031a09060609040608030f04050102250905040c03020324070c020609060d1d0304061b020d060b031914250308030a0207061a0306060103180b1b 70
    0x544910000c0d60f41e00d10b0783c04018180c60280c42c403c80071000e00754850401d5507445103010390004040d12001d84409890f400500680002d5100c5607550200107415001c80283c00d0003071041c1d030001c1e000c44044910809240f9001101c294100d484055034402c24400c1c105c494010f00e40050040c3d28a0b030304181c9903000a41028101c1c9002c4c42c80050a1080c818a540120308290340607010741000001560f1540114295200704442c1c03030310403500000c414040c0b50041d4400e1161a260582d03124080100c0d41100b03540754814010718010a080f10712226580094081c2c0b070b54090b9003e0100320400140d5a00c0e58045d0920302205079060040300c034066441e180845401c0e8009000b0b0785c2c0a52404020f8a40c40d00317104903140f0a42d83c1022006c805600031402690420840b940440e90079502c0c5d6610781c24a000740030b05400149807a040911646c0c512442c103880013550081102501e4841d00c507040150100c0310426014100010717001201d00108004100407907000142120215455440036507149403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 51867315 1250 51866065 51866077
    0xc02030a0c0603050f010503070605040302010315030b0c070c0801051902070c0503011a130b090c0a2a061803020c150403060504080301080d05030403050d0c110709060603111602012003 81
    0x44ea64004018903944c1c030602407070042000303070003824903541400b600900e580b24600002c0c0c14940c40c0c00b6101d035440501200d5100940c1c00c20001c01c05403d1000c2841d8807544620400e0352a0f402581003c625a0410720501f03014012030154840c0031210b000040c000703500702c5441034800c06094840040c075600c003800707000d10183c0e15030285d0000b002c070f401c1081941c44a02c804104604e103440301c541e2181e02c82d0085283c00848014030b83c0d444400721042258800c0d03001d00c03d02002082c2e1140c181055210020204c00d051184100b0b0103100b4101c4403180c00245056005401a40909e59102c00c60400000304451140740382c500b40e180c203840f030f110001910b030160350481380391500000400a84209000e082074101451170000d146003440d40300100b0602884008008441e502c0038040c2526000d800e10840340000d100c00e6651407956111040c0081a8501c680e81c042800c0417402d0740342e543d041003201d18444a07440a0000d242c42c3d50011915140d01c9a00300e00da1007900e00719072052281c10002740030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 51868565 1250 51867315 51867317
    0x1110f010e0f07240c0804090903080a180203070302061b190507050d080306061c0c0f0e0303090a0b0f0f0c060103020f0103050903070308190207050c090915070c02030a0c06 76
    0x10710071050071140341400551044c0c0310300703c11400d0001c581c124008a0b140301c00440c6402c070710010b0030381841c0f00a0311596110440352403405040504042d0000560f0380320700c20041e820024001c400554a07100c0070001802581500105002e100510701034018150718404060080c110440d249411440c0c048000306948180b8041c12481c0c040003010400840035210554440403000030595480e200f9000150680f44110804203032030710340900034007011000d040d800806011806565001900081d02c0800d10000540102d2a82403075080000840c6d000010103004401c2003440c09140c0b4000c1d42169103a002c855508202c0004c2c040050b1004d0035000100d400a0b00c3c80d9495131040010100040548605040c18201009143c0c04080261040590036080c106800d50b43c406040840021312203002d555244040344030410700a00040b01650104d09440e0b075110340e25846041541d400070f400c02c128241000c50300042e03200d0f22031145505071501c040e044a131034561039561500c038007550707401c444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 51869815 1250 51868565 51868573
    0x9040c020604020301110c07090c030f0f020309071a0a0305180a080c070501020d0e040203100302120d02010e30090402030406020306040b011e051e03010906051e0f01110f010e 77
    0xc1d45028460005105440d60000789010000600c86823071711141d11030184100d644858020801e8003c0d0400c1903000a0b507801003040030b465271140002904180c840030702608c1a54008129000c3c203116000c0104103440c851804c2c612144400c9000c1e10300108005285c03400c2c0c003c01004000204400700340b00c1e1080c80341640740c090200085190074030383d60056045610034494580340940055004014460568001d45d6076034848010101d50b50984c0c2c0000e4212903800d0307a01c03281120200d4804105036040d8020b100712000b41900542d02c1800382d0701c2516210100b1251340e92103072113501c0c0001c2510304000c0581080392100000f0121303003080700c042d0f546d17503000000c01c01685418820f42c0c4480c28242040c1e852080f080010400351514040c104045c0000012503040070301000b5094a00c8501c0020700d0f50750380da15008404040c0c007040c42140e0144141e400c50401c42b04ae1420b55803a54540a0011203008044000441d0452a01c124120480c065081400c4000f14280200c0b5000d1000314018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 51871065 1250 51869815 51869821
    0x1021216021215070c02060702010f17010b2223031c05040e09150c0a0908070902040e101d070302070b09010912020f0601051005040f2904030f02040f0209040c0206 72
    0x54210f00d03000f010b440400c401d81110f440141e40d400e00303440c042602844c0030310390180e40c4071041d0380d20040740c421071a9110f0032600000d60202a0310040040b01d00e104e01c404070036218110750051418060007a860744600124a0081101c0b80e2070f440385514500034203c2e01400300041040d4030804d034014400002800c002020b0103254003508065820860307481c02051349400b0000c3c00344030100042c004001c08500000c404403203d204007448400b038054102a903042981c3d0303541c07141c002e45c80362203407180901c480300c00642c1042840164004462200b0340c5c0400c0c1412400d04200307810402480d590500d0390074481c0314082642c2e40d04040c4a030302131100010391000c4600300901d0704103545030002e00710740c4080d412402c2c1c48400701d1111f0440b24151350035a201c01c445d043c10343e4180603980141d88049494980041c0c1840e0a000100d0640c201a20440c00318450a01090082c031075404050844241c000700750f4014105a4040782a1002c100300050406a0b00b00000c3c041e95141c00c4034400690100f418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 51872315 1250 51871065 51871093
    0x409090c0608040b06120705061201030c060c0302030a0509030316110102100b06071b050409120f1b0b0604060306050109020703021005041a0712060608041401050402010212160212 79
    0x22030150000d0b0404121901d895a03e0710442c03a00180840e029500220072100342110802005000d40001025180c652403c40c040012080b02480156486c23901000d001074050b005484c200c54141d0140d018510f0a800e1850944d50390340101c0d0a00d402d4802041401c4042c21030174924400144126000f107401c80c1030340002450b184030b001511501c5880c2c001003801a98a1301c4c210740c0004d50014040e00841100d417160254041e1a501842d0843d0900e5552002c10850140041e540318082d190401004409841203c0c0c007120f81543d01d420700034555600d030100d0300301d4074180d6110400500106100352640d40c2e100541d407080c3c0c00700c08441d070081034000406406101d419488242024200024030f8240c9481d41ca040601c42442a201404000300326032500c10003160b688040044803d00503107070ba03500000e003400750031a020b444140001c0c091040c2160103000740d50285405a0007480552048114400a507000c00703007040c60444464206401a143c4003401c64198030b400011f0b00d0400d0110721 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 51873565 1250 51872315 51872333
    0xf110d12020c0405070516020102010e0604030503011509050904060e03090409030201020c0c0603040c05040207020102160f210312020a0e0a03081206030303040c060c02040f05090703050706030209010801051311040909 95
    0x2800520960800c81089003c3d41d006c0c054482152600d45120a8051076000513401000ca05644400d5409910104401c4c5034103c8020741c12550489a05129480d0210046030090a20700903071743d03c103005002040101d6440c0d00a040c10031404000d4a00d415144030004003219201201100580d4020071071110101c0c0601c5600807411040d0b8400d8a140b40c00c1d0341d4800051028014544180d50210704c140035a4803c0200148540102a2440905407102a07250801c80305104410400315200340c00c4002c203596560321441c20f039140d00c41001d98074501a103840650031103042c0340c3c10403410204a5046903680c00a0500071030040c0e140a55030400b42803040c40307095005060318000e034420801e00001400442c1840100c071001d10f40741040301c486100103806400d24000045040c1e08141c01d01c80002d0380400c40c141140d101d20308542d4540e60741c240c2035043e4001e603510a40401c164000404c51801c00303907081050072014034000100588140b910300c2c05600030b0340002006550b02c503032400030012021 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 51874815 1250 51873565 51873583
    0xb031305070510020a02091e040f12030e19170f031501050901020a0303051302040c08190501050d0f0507080708030c0d14040306020c070b0d0b01030b090709030f110d1202 75
    0x3550307440c1d100803d40300c00ba54550400354000e0240c42c0b048002109400038884403d010200035045003001e0405080900003520150815100358100200416445019119400f48030342c0250152005440b500d5403040c55040100050350115048c03401c100a0041e0720008281d0020b800b006a9140d0920503440c240d040c040c41d00c1c1e0ba041c4001004229000d03038000958100340b583c58540498999100e010300282141c0a010083d00507007008482c072011a085610300e4868100a0010040c442c5201d003090f041c1c0c1c8081c82001c0d0424800144a000301d0540c501c001035a50042c001c840d11140e603580010300d40715260380940ad480c0c02c0841e110075682020f100003500c01c140c03441d2050807044210344d034505500c194803000300fa00303a00144625001310301340401802000010146a21840204040405404401942c1d030009240251088a40ca000c070103242c0250403944c0c0c0d8001003801c40d611141e0300d10b5000002e444065600c11814860f9544101003142c00b8404d41c041c90000340d8071100a031a144040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 51876065 1250 51874815 51874819
    0x50c040911120f070302040306141905012301050906071406010603020a0801140d0501050c0d1d030301060e1f021c02011406060f0f04030804080c0d12050a03060b0313050705 76
    0x1c01c400500b855a0403070660b000030001d09045081e8640003000d40c001d100c0c690005002509120782007484241407101c443c41114144e00e45030329030807408181c008442003402161368083c90074600418180020071003100421040c1000d906e001402ca0018032150813403c82151841c44601d114120280c041c05202d004002508040d41000d040c0480503004000c14024445141140f0038018030070ba8801d1a0300308044d07044402004982402901503000341e01600c03116101c1400d109030b0072910a45184a4042510442d001d50f0850b400d00c001158500f140e5508580d1184000c3e4280c4403560000758180307203400c036503001090516002050756110703800e203824000a69241440c2640b503884400300340c42e400034084a41c5c9540d5900345102645d0b90080742d14000c402c01d0003041c044100181a401032081e2500d079000c68442c18540010070600c40540c0780010000c03404008070b451140d0140740035204440c498100440c0c00c58440c241070308035410480e03150424104808462050020900407a0003424007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 51877315 1250 51876065 51876067
    0xe040f060605030a050c0904030c0602070309060e01020304030201090e0721060501031109011706061b010204051804030903060f060504140f060111030703051b07030503070501151d0613050c040911 86
    0x4c10748966464020225081d4080c8041c103000404241c031680307060302c0242d4040802c5488410a04000341021454007416010a0307000407030b283c6641c00041a1030482e64140c0d0317101c0701181883c0206034201c0b009040e01050001406105050140300740050320340201d0f96200140c018130700000107081d9141610f510f204014108072800d41a42c1c0240c2e4031450b01b20400159080c2d0f12842c0219016206140d1056010b4444901c041111141074009100f103071011a42460000e20703258040f10000c905880040100307240c6d0f2400c000081068102c003004402c031000000300d056032400071130243e64040e1500009000000e08020440c605011181e410007800e20b8659180701c20b82d806907940e441343e0800030301400804a10400e2026014551200070707612042032790176403540c0e40351017592074106e040704a405500700741c82d40c84507907400c81014048500c1510600030110500d018134407640c1d4081c10040d044a144d01c0780c80704410032070181078062070703140d851240d0355898907400d1001c441c26141042c0c02844 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 51878565 1250 51877315 51877333
    0x61103010b0f0307020c040e07180203012403060503060a1e09050c040902060403021504030c08060f0103110301020705010c1d0303090f040213030b0c0d050708071205060402040e040f06060503 84
    0x809080d40d100e240c03200e40e043c0d941e8580320350603880d044854029070750040c100035075040b518002017021400caa400c1c40055202e11000b00341c030b100f80e0000740682c038600000c50303071660b08006c400301d1100f1940c2c0b621300f00040c04a0300c0c0c01c003090501000300c0310701e40400d40f115242400c80d24821400ea085208003e820130061600b40e0b991a1100c1018070481d01c16912100404150354925080b1030003968010660364141d82000b0500905c0e80003884252004026100006161100460000d110340015100c0d4032032a821a40c4620740c10440010304e41d095035084c0148000110240304144010100b80c0300d05484400c0b103004109448103218444d40660014003c4519a450301030040d0f91450007218007584607400d0030103d0500b007040d03510240100d0000401d104003584200010084214000c1050111760340c0c00d00c0554800406450341c82c0050508030081074a40c80c10750010760040801400940b4141da10103c1a666410650702030b102081c181c0710307101c00c204840c418440140f206030f0182040d08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 51879815 1250 51878565 51878579
    0xc030b090705210c0f130527011e0e1005120706021504050c060301090b040516020616031803020705031005040807080717030702010203060a050a1a090d020402070f06110301 76
    0x480b1400c50640d40494440114030107880013010f48409103500c1021603100c00c01e905d01104000c010303118040c020413882042100100500390099002d10308d01d10800f010780d00c0d000051005070301d52110310180801c007a4022464010909440340601410305c8425802810700041045070340c203500d59080981d1003880308102031070300410750850300c00441d6804c26481d6210708200c0d0500b220072200380e43c4070000100100300d07419503510101e0104400e5908002c0c03656108030070180c60000352421405a840b040016075000700700b00350320700d013900c207403801081820741c0380000d1000d0030341500101c002d6084400c0030700050038104402c0b00c052960340703001d01c11400c1546031001a440380c60000b030802d000000307068040c843d402c900401c000d00103003007241e52890b000f03000034001e41082e148a44100411080011645440141e03074040c0c1c0c055403580c21410340e02543c4c006040d84555000b982100d40010000e01513502c40c03026040712402032080101114080c03a0810071100b21352603c1c12822030501c0144241 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 51881065 1250 51879815 51879847
    0xa05010810051003083609040b06121e060a02090a0b070303110711090708040b070509010c020306010603050108060901050112080304050118060209010201060501110c011b060c030b090705 82
    0x1c60301e800c000080d9900c481d03140c0402d00b205a040507010b00c20020301c4001c0a6103015803078140300540b01008140d041e0780d04591002000c50b607070442d4460310703e0303002ca400300d13008118494102000504800e0500d5001e01034074200264240d510041020806411a0180c4103009099020314614401c40c80c081390710303000800a0065004112405401050540425010394400c022450320342803880d80750401c40c5046054544c2d171504603409030640700b020408032030190f0704150180c0e82c00411102c26560710002290681c010f03441e020304200c41c4004040250f10140030050107408140d41c0402c0b01d604201590b4034010000e454000c140c0c1c03400e001040484601c00551900551020b550b41d520b40307484c00c12601401c48113842ca80e0ba465802584020030001e07a008209000d4281c009002c0326070b86000640e4030b403481030060045038001d015023440b190f12801c5108031412005a40c0c655110403601c0c0d0000315440c0d81c0d00308010039075400d882c8000b8941440d07810391101341c500c2c09910f09407001795600c042d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 51882315 1250 51881065 51881083
    0xb04020915030601111902040b09040506010927080307030b1503160504081020040605040b0703020f0d0203030403140403020607060e0f0d090f06050708120901090c031101080a050108 80
    0xc00010003c02d00c1a845442c003150030500c0141100c1030344840c4581094500a07400f0100d05c43c5103401011603843c14088140340c82180c00c0009020141c0c60801100054002040c410002010f07016290951300b0401d03040b03200c42e43c020702906031603240000024003241d0500703210600ca00d83c0c0004510702140c141e01102e80c0407c006a00301c085550010080c0c445000da80c0008070315025034255142e020f04c065005101c00c04a25007464034440500700305000c0c070300c00d40c021040066800c200a1280807a0340e00101141413103441141d60380320180600030300340b400380d284040040c1c03c000140800d00d94042c00340040394100c901028a0640f540d0f000559600c52074100031b050984890400416090511007003502d26618030a5403503503080c119005150006c18040c0068110030300c02c0102c2c10074803070320a448645d584200541e103005240f03405828003810080c20ba403015900c03241c0190000e140c600d204002144a20f081ca000e088104001400c0e164004025540300e601c1c0c43c0040045800c00904840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 51883565 1250 51882315 51882349
    0x130905060a0e030d0504050c03010c08060a051c060c05030f0a060501050d180804060c050609070506091302040f0b0306030d080702062d010602030301050109060302043507080309040b040209 83
    0x500c042024a82c0d8114041c1030340c5030200324a0b150070401030101c040303004002424200d0003000007a07400c1000381c5020340f050303070410741044514009002604044040c0c0d00740117002000107a1124460303403248240e0340020031148c0040c0c000b20500180c14055030280d038000340d40d200705229090500c1c00003030460007045414000a030b110a00120f121804e00c0c10200d015411444a0f41d407070740c89600240c0381014480c0115203a1186100103045441c001c24094180d92006160b00c2c9401c05c41410001d040a58400000d5490381c200300008004455204080091150087d03003030310703440d19004050408040c880c8110030b1004402c10014026808182598441c0054100148441104a16250002c40b07070110a03a40c07a841c00c0042600d075000006076040f2030742642c030340b09007581350311041f0140e009512420030f5482480c1d4440321004500030380c5403102a42440039115140307200784003518201c46070b48504025000001d8072100ca040070701441c00e03440300c151415450556084003180e4250580342e00c3c29 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 51884815 1250 51883565 51883571
    0x501050d0308040809030d020c13050903071b08060709060e010203090a261002040302040501080d050d0f0b040207110301051509011406070525090603150509190c05130905060a 77
    0x3a00300300400081c5e440c0c0c03c4000e030441707940060048020751380b0101043e03494401d01c1005420300c101034540c003401c0c0c46080340c2c202440c14008240e40700d01a14049100321000150140004a4079590401980748644910340d200d42d01a131034901d01134045d01c40701d50b8090441d0410030000e03d5a44030b5440740340444201c0b050360007241b400f00c01c0c84507203d04980e0203007200e0f000d580e0001641c0e2410703401400c1501d00888041010303913038540c50f80d40d039002010b001202240051024a01003e5035500a01091000344004244c01c400000081c0403a07005000460f805c2d00c00c180c074884242001d00c182d135401466103000d031070104120380010306a144144035075200840c1e200fa0440701d507140c4405a407261079010080300c071610003003441400c01428100a4840030001407400040031034460081e6812a07821080c1803208003000441040601001001281184941010189058150602142441d0081001880003400e02007004042500045c60780001070500403040c003c1180030918030341011460b5400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 51886065 1250 51884815 51884821
    0x50a05010608180106150309050c030a0510090615080a0c06020f0c060705120c032124211e01060303020303060607060f0609020322030813030302070813060f030501050d0308 76
    0x1581c0036100e00c6e0010940b25601a2581400795050f8010129940c412810742d55801507044c14140e6034044031101a1180c0d01c55440410b0300d005079809003640c24066040490f1020080325882d5010243d075002210325801081960240020a001a030180203d81b001c0e049040d1031402c0c266a0744a1740a0741031044500040d60002c108040101c0c4c105002e16250707a03502c49081c1c100b103940301c2e00b0003101041e44652140a68090488540086100e14901c011020045800c480e58400200135552207580100560450108035011014580c0e0a91201070050107846120703a1910180310100c40c0c103102071380c144942440001e40100640b0760004054800e02d46a480b00d0400801510141403608072241c503041d000310703110360300b900150710a088404003540588c034101500c0c2442504040080d00203a0404080307045c0012120240300300a000703103805070912005442f40d004076800103003002c4444005000400500c2c1e000103410008681c1d500f0b0801840d0700d0540840d0200c0000400102042151000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 51887315 1250 51886065 51886111
    0x2010f060623093006130f050a0b040b060f0108041205030903071202030a030b010e03060f07020a0b09010603110d1e0f05031c050c0f120a0204031208060103050a05010608 75
    0x6503144035a000f0898604195002002814a0689580b0a40b10320b221041058020f42c0005c81d00d015030b0352185114140c078415114074800201662003103420b409140e58803000300c2c0c4030055190169000d1034106e09a810700e4410042901030401606050110782c804000c00b09021510007a9508000d0030495500e40d12001d0313080c03c5121b408001880d0f912034404400711941d00102506417044161000c106100d42c02c1c00540b40108021b049941c10781c01030000032402d0005181003a04991503004880c8440c880d0360303401505840445070803c25a41d034401c1041030140c001040380441105a40c3c6045000c03191311041f0a99980c20301540c2c120140304c115100f00081008455545078118044e03030303103966003007200c141d03185001c200e090340c00c60510000c50106803003001110044403a88090610f0704411036030041c0c1c440d000402d001e00382507091200001150103905200d41c0c6100540d682c5001f442c0445c0090122000075140d991000e11388401841f031280c102e01c0080c1c0166617140f007500181d101c1c82c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 51888565 1250 51887315 51887317
    0x2010311070c030b011a0a0c03030204050d06090209011707140f09090607080a0209030706030b0d02100f03140105010905010e041b09140d020d0201142802010f060623 73
    0x14204a0032000022100d0920105081800030740384150f11000050740d07140e405c002555078030750a110140f1030420490116038041d2000340c48841c80307418094146565403000400100d90144160746d0203483c0e4480004610b803004009002d070100c030351081d5118016071002c50360341000c0e0003014020307001c2c24240000d40d130754520070821510b0010b09030010b0349401d02c078240d181c0d041910a00042a8600081a00900c5034005d030740189038084d005103900c52603d141280940300e0380e01010b4004021f07180506c090703111100101030008541d1180111240d00c610300400b02c0d207030b0007000b810700c4544600500150707a120403500304640003403030300800c420405000180200703d002c002084a2007031209402141c1e42005081c01103032500d1860741d1016840c64140403070b071585504000e500000c0d03081c01e40019802005800c4c00a400300d81d83d24109603152048a4107183c4200304664490702c6c00326458112542405146103840b0441410f20400d071400401030824400c1312000d2031a802d1004410000e154104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 51889815 1250 51888565 51888581
    0x60d0605040f0615140a0e042304021504080a06051801090308071103030405031912020c0304050406080307120f230405150309030316050702090a06080c031513020103 73
    0x34801c00168003110b484000502a138421030001d501c0c942191503a05000e09140e6170485200c180907881c009903184100d4548426003a0b40f9406070f51510180c41001943c6440394201e5a1070300c042429042c1801000000480113210300203100d810041440301250100740b0b515040d0b8007100115040d1181104000c500481c0e240880c0950700e4404002e003810ba0100740e80d40540503071740f960142540c01c0c00f0b49940b2807204883c0176080e6802001010341d0789461600070b207036084d6980344c000312402103294007405130380c07100166003c01d43c00400c0c10721103031410b88100d0b0010309011000354035083c1c203a1388400040c290303a0fa01c40240091485d80070007050003803005074452050058621458441503000c0e80300d603005409207a0203043e881007503400100076402107a0191000000440c215560311084d103450400c01c230242001c000090000e41e0058640c58242c030b000340b42800b8045213084c00c20256070710f07010184c00100d11035400702d140711601040c20164207800100103070342c110102c011400140e01418800c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 51891065 1250 51889815 51889819
    0x30e010c0f0b09070603111305090402030f030408060109051003110405041104090302150705131e0308040602010905010b01031a0f04140f15010201060b09040c0e0a090204081c090302060d0605 84
    0x32410421202c0b00400d404003540d000f40c504006101c1a4007c000c0e0314002c00400500000c0584000e1090345012900c240d80544000d046074400f15004c0405429500541d0001071194814001480b0340760440c0225a03000780100c10301e80341c09245485e550156080828018000d568840104007403195505441041034005481813000503541d14000395102d00015030000301c0c4060300049002315200708219002c0100005054200d1810980c00543c40800188107500d40c480505001001034480b2020340001c21440d00001080015401c200382595222031b44541094034000c5004000c1643c901c014041c1c180c2590320041c210881c0e408640203040010203403110790402d40c10080030b071007561012440740c0c00142007140b01d1101000164240e4200c3d000e41410101d0a204131012401d2036401403800448900d0040e040b0070100c0d0103e2914140c40c1c20403490140c00013010701404030104040b480c4902c544198000050681400030902a06404001c0c850754000800b180704800c281c0201024001c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 51892315 1250 51891065 51891083
    0xc11010c05070b150d02151c0b030607030e100c02010e01060824010b0a0302032e060f1403011202120102030a020403120c11010e18090d031404030e010c0f 68
    0x203240501150450351084a12100a000003071100c10051242c40003081d0191203140000d04941c2080200081c0500c4100e82c1070060240f1600c110318015003212108541c0d10000d00030400c07000380340c10000024989070515007007004032504500300092402e000c80710760100203000e00701c80000f02c1c05420340701c0d0040710325801c00c1000300d081503001c1050b4401c5400415140803104444200045030b5000340306900002400b4095040030350f009800a43d808150824110300d07200c00030226111251200c01c94000703d1507809418414942c0006941321003813001d042850044c1035414070458548030502400d250040c01c4040c1c46d0441d207030040c0116070000740100a640301e20f000d501050080d04148810340f400202c0c0e00b01d913020540241c280c80d0b100d5410000a040b10f0000c01e0043d1000c40380008029005201c04c0c120302c045e40c080e02c0107103000c1e103210000b51840c201900d000800b41c0b800300000c622500007000500c0b000a40003c0d9884a0100a0a0803002101541808805a0240700e070141441c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 51893565 1250 51892315 51892331
    0x30c0306041e1b0503061006090303080c0706021201090c0e0906191502030a030f021606150504020403060b1306060f2a0807030305090102041404020906091816080c07060c1101 77
    0x110846900c00707513402a001c4a4a0760b581140c6001c9117071552042c4000319503030440030300c086482484070640c02480a205646001d81076543e20341240d100c45200c031040f11101d03005112440250060301c41400c03481c40c000041e2200d040004c1c1243c10013070421885450813542c1000d40c664600c0311000285031035002c001c1a034844c0c101c0a502e03640102441000a440c00c1d0750020220058401e50343e2501001c00c007519803a1069032141e0050849a01200300881346180c001515500c9000074405580b080301c0103d074125510302884001c3d1400855050341c2400c1400c00d000782c541c000003065110b001e43c80d01410103c1c50032070075140444e404440200b80d81c55041c200091085880c02071103694800d94003003200d0350341c01070307000c1c00c0380258000c0203410644921259030303c5c9070680181034642c0c4010002454070031604009240e10340111190b01c40f044e0007400b00400c0300705054540040c2c1210381090300003440d2803211041980b003064401418581c0c0c48110a001c42e100b500b41e9043d1100c49002045680 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 51894815 1250 51893565 51893603
    0x60106090e06100f260a02040609090515010503130f0f020306250509010e0409060605120106120807051509030c070b0702030307060b030a060513020f030c0306041e 72
    0x3616070041000070318092010940360709000c8180721a4142036544d40481d0600d01c8000c58030403a030414152134002490364000030808000c00f1103401203003114001a075403481e11070060000320081d88011a1340c1d140004000300c00e4100040d20b44194024a0415a40da480e5038188032001d10801c00641642e00081c40c450401880580551030300e80201c048903003503074848101044014113a881d520603c02040007404200d801140074041c05601410010b00c0204c1420108040700d16408003039640c903031104000c00090804600081c120b0700068028030809040801071162502030550041030090005894000d1200502280b0b801c520141c0c008600da0070030b140f40b00e640341c1100014081c139004812001070302d045c02d40120303011180d0240240d418405945c8480c4002c0c16002d03a542e8041c01030042190003d5400d1080c03034400d0030004c414450000d403a005205409100d01680c600940c4020b454034030b10355002600d10b41c0184d0002811800408811085200c0d000800700100b9518011031040421 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 51896065 1250 51894815 51894827
    0x90207060614060a091401030905010f0903140307090302090612061e060102010b0306040602070c0b040b04030b15060706090302011d0106051203070b180a02060f1210080705060d0e060106 82
    0x5541218403600c6110b03011080140d0b0b842100403003408100390b448100300000f5034241c491110070050600090b01c410303940700e403801e441c1d81620030018070703030fa440c0f040d010144c0203421005c00c07400502d046821850000b038060054419804007130710801124000803640e070345040110300f0030394000f0241d070103500380501a46610b00c0c018142c4264440d1100004003594414480c501180b03100500420468656480360402580020b0b810359071501c02c0d031000708035804480c00401c000d100e228551a330716855400e142c0c0140c1c070040c00d040400e1030242459451542c0341002c1da15803a411080000d21000c0609c2c0990041000e2454800404030b15010410345010652069040f64030646200c510a0b004ca00d071680c407442504002011840d2001c082030703ca4000c0008102d200007803804803207240100360005801d0b40c01c03200080e441a1000280b80c4110b1342085000c41e0003952070a440d240c002d0814240c181c44020a004003402801c0c0450040e605514030b4000b440c90900b00000e8410ba961100c1005102c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 51897315 1250 51896065 51896069
    0xb0702090105220f0b0307030804151b1203060302210114070f0503091f0c1803020112020d0b09010e0103020312030705030f04111e120703080304020405100902070606 73
    0xc100240400058642030140d064440712951105030f144284250140308001d28010309120300c0d003940ca01d0000d0407510308010a030060b50003125010384991410603298180c140040c802401c100100941000c03582604a0401026502094404c04102044000c030000c2c03e9550019501c544a40e00c000f4211150350071408002410700002d11400f0352601c1c5070180e840040d19000000f42c080415814480d104174091500034940d80140c5110340d25110203981c620f0f00f541101050659101d101c2c40c080d5401000300fa07640c07215800001011803654001804051004402500b41c3d600042c46010b1200e00e5400000c1e920f034024140c02e0036517190342c05810320035024007080b800391080c2c0003264091400c0c5429288136401d01c1d1f8525246907200c002d09021060041c00c1220400c84000d41d60050f691940c00006080900c050505130300060710f4100038000c805480c07c50300c41d0b04000000d00c0841c03520000c59500507015a03004c280c644954490b4048a042c80e0300c8401d80c248045014001c000d002d80260003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 51898565 1250 51897315 51897319
    0xa0507020708010603050a0b1b0301030b061813030809010b06162a03080a0905040c080906100e0103060b0d02030a030306061205090d08090111070c03020a090204060807051606060b0702 81
    0x61007544035a04182202e030305005c090315541c058424100000c1d8500c0199a00440100c0760044540005411aa00350400c1c0c1048524217101c004110880c1001f20108149518000917162607041c025000c0e060314a420794080d003085107240000d000071a00f500212100c0d040608011742d2001d100305402c4008071011030454030703c000074500614420f061051030b50041440d0755080951480c3d55180c2000e036009034141e90900180c1c410003d80e9584502c0342031200c40050701c4e40961454143c0643c0d0414100600540d94900c00c4441440b0760f070105d105c00d6054075440100003602500c9003000400c2c242202130025414828107610a0030903505030002801c481998846600784030b0300200580035508101c3c0c440c11076500006100205504c94507210b40c0040d41c7d1000014084990070481100364070101d003e450301c10313141400300304504102c46114000c00d103240d011820581000ca000704104006003414041002c00b142d0801c1411010074030114450b40003101b0402d580d0b55610340d04041d04030150a80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 51899815 1250 51898565 51898573
    0x318030c1e010614060a0c02150313121b020d0501060302060c10050604020f09040504030c02040510050a05090603150c040f0303110606010207271e050f15010e0121050a050702 77
    0x44c1c295800c49031402c14400141880c0c00c101d42d0460846892410000c1a40d201c441c6145102c51114a18011801f4031144201405940c01c0c1c0e0400614800c2d1000c05801008101043d01c9503480200710003101701c0d0344c1121503071074640c5c0c0d50a042c0c1c050301d242d41020303611010020707460070640c02c0050190a050040c41081c880f555a050401c422405070003441a544101041113000070314099025a90003882402d18018102060300480d003181e41c215024600c43c803212405008a00d8140d00c082d0007480100c85580c1700745042c402080d01c8401105210351507002c0140031503c00000312041c0c2d00588040138107002c0c0c4503503d08005003549110400c48501d8025403010070000c1d48046a2142503030075244c90030700c1d80c01400d5484d05204a0041400f0121562900c0c40f4492658071200c200e0602c1d500b00010502d42442488030180300409800050301404000580d68130340d820071404040a102401c2103456051040100d560034080c902c03c6440c1c840c80e02e000c11180d00281d03030140e4020304c00c82d4211 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 51901065 1250 51899815 51899819
    0x6031719021b060a050d050c0a0908060c070605070507060f060e060d0b0c090307091b02070e0906070509010c050d0c03020f01021201180905120306010e10050318030c1e0106 76
    0x1a030b140d0402441d01035104202281c106202d0400800a00414040d4a042480c007100aa55003044a006942013840e29000043c3d0789041680495090003924000000c1c0c20203041545880103140304241c00142526140c00009030000c0c01001a1060150842001d000d58900382e8110f8005003140e0007a0039020f245000821421308181d03010002196001c00060500d86522031640c120341c00014819a062054200100b040185030280d25009000c030002404041c03003000010741030081580190b11011340680801c0150f5000240045d0403001c1820640d40d1140f4401c0100c5001c07901d140003a041d88515044c040c4c6442d8008803a42c1e0040c0654282c400740c501200c0e03094203034420502e00310072a200304401032100841c1c10f52800d0030001400300009006000350b03585818002e4500080610340b2011081010035600072480d80c4080b402140c180404001c1400c000c0c11500006d4629903241c1d4240c840d00361207110400881e100140040e049036500708680c281004913a0218030000c103a075081c4040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 51902315 1250 51901065 51901067
    0x3180616031e0e0d031d101d06030610050a03020f0c0f0706050901020c01030b030f0d05040801110415030b0109050312070303180302060103030c05101a10020c09061306031719 77
    0x5240c07000040100320240c8202c3c1038500b02c40980c5400c9520052840c6c0c2e5032a800c140e45c442040f0b4094411944a018200402040140c40c0c0b25100d044940504020400c03c21385a4030101880a141d4250805540700e102d250011802401a42c86091501900103180840913900040324103104550004a4000c01c0d11050111050b00032141074601691040c14450000d43c083c0c3c10070b0303c050070301030304669020645030261890700000141070380110b0390016050100c14421300850109400345024103141c01d140540b140c0d855410140c030780c42010b95550101c48141c1c460172440d4020000203003202e0034400703007025201e800e6014250480105e8a04030400d02c000c1c07551480701c0385a54140e009404607078699202507403082ea00715011216401100320441c104650303031040d80c8404006120400e240d00c04101445110807001a5001c2503602c181c0c2804071590f50841915800201554034203100c00c90a0308103005400e481d00018140800b84ca84001e02c003404401a110407184658481e00700c000d5030720 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 51903565 1250 51902315 51902327
    0xc0703031e14031b0f070807030207080307080d0b0d02120105060103060504060503060c0a14040e100b07050715140c0102030406060e010308030403140909040c030203060709060203180616031e 84
    0xd80003502c0d40040c0300048101e020091344000d6014000c242c140303070500800308032040d9440054100c0785110301080c0401070590400194003c2d188100044d031600841e5100e40e0403d001c2c2406d03103145140c80d0a0645880c0d01e0b198810041e40313038041c0203a032084d102c2051441c064001112050300003032501c4000180d81ca0203020700b00c12038001402504540e19102c3c04030440780d01c0426800c2c10700440c18040180e0046200c000d1009141028295100d42800c6004018203603859005110210003405040b010400204600048452a42400c0d5281e8201007090701c041504049079042c1f16400f241134044d048040d00298403c41c4280d104110a60b25280626002d01007800050b090000500000e00024051024152604203c021503400c02d400390000408050b000c0358100c1d0f581e808010100214107003002026001080f6003041040070342804030080d036034041c8408408400c200b145040c611078031520210340e1404035005050103003c0302814003a20301080c9801c902070301c0e041e000c0d00b1100148215 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 51904815 1250 51903565 51903587
    0x61611070b04090b03070f090c02011107021f09090204060e0a08011503030e0d0b01080309030d030b010f140409020408060108070f0f0e10080d0e0901080a0c03080706020c0703031e 79
    0x1d02103003000d0409000500401081842d940c0503c503032403000c5400d200e0b04c02d40724000c002c020380100396224903c2000342500c5e10354030303080410b60040c050300005a46080d240c0d4014005003c40c1040880030100807203403d4002d502211001d48002400320714250302c801c840b080c0800075139890074010f544440881c00c07100340180b01c5014000074142400020300c180e40714280321100030480c0c01c4600654450700030b1554203034050340459000007400c0e025420280040e2103c4000f50404010400180340007900481100d2030440c1040001100144481e600c0030949018006000c81151610f0310348255039520031003801a15003600c80d00000055141031400d8100c156184612010703103503841e00700065440c0d43c011f003141404104414002c1090003040141001140c115516040c95440780f030f050001c1240184c1000d030840c0c11400042d00441d2003162a54200d90340841100e5942400c0d04040e0028001e04041c01035034002c0d02e0002040c1540020000041090030142c1192001c00d0002039410010388 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 51906065 1250 51904815 51904829
    0x10c110303090303180309030313031a060306010501030f18060510080601080304050907031b08060a050a030b060603040311060408031905060f0418020402071b122a050306161107 78
    0x2000007920743c0c0c02d400b0844000700c5c981d03400ca90500b09a00002800c6400101c4540501d9a03562410024000841c11806050302141e400c1c07046030401101181d224081400345c14180b44c6c075009520143c0390a43e1241003000e4100f008200d0700f05407441e00c14040d002c1a500c01c0f00c030340190030f8041410400850402d0403140c1450045203000c1c508030500c492107400504090502d40e980c0e200c08000c4040080510240740f035952405e005281c450104060108250805401840d00c9207040c0001803c00d510581c12140c103c81103030b1642d5503407400f223900c1c0c40d0300810f07012580150703c1840100813041c4084e501441001d4400740301d81c0c11040c1e8072001c0358000c5481039031000d1034140c400320030300b0280d004010540100210038800322141d0081020381c0d03c103032070488050586190900d201c140c00006400608030000f0305207100e0071140c59070081c030240003481c1b01c1100c603c0714080004010008440700117140107810303201d403450311030340e0704c4650b1500200c690f0203c0c08504402d80d510b480414200161400c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 51907315 1250 51906065 51906067
    0x30b01020303220305090301051f09060605041a0712020a02150702100c030201110f28142803050907050405070c20030f1b04060f03060b040f020a02010c1103030903 72
    0x16000b0b844400d15169000c4d01031140030400000203803801e0080501c12400c1400340d5540c00034180f248280e03008a40d020035182441c00c0d00a0140320751040484040301d480100118400f208030071038900070f1059002c002c2200040040317100a45d500481d0010005000300c1d200f00040c0074a0703903c0942d5103d031380b000030752044210303400e8001c283c05041410242801381c03000081e0700f6001030040d110f5900071018800180e101140300c00607040300003102d00e00c480c0740f030030803010386070141c0d1024103000050b9007056070080c0007050382040441c0d80020115005681d070200d4803039a858190240082100750340c800c24901a405000c15941440d010307990141a1659904031602442d4a0706100c1400e89c1500c0c40a420f4841071841d29941c2c1000914070320072514001d050b24005100940d01022004d4681034081d030f0802c442040019200c010307000c1120303000a0041044010040080c0003009520f444000082c0f001c149405060342c15448620405040c5d160303c05c0f0780c85500403d40c0c1c0ca000443d907810846e80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 51908565 1250 51907315 51907351
    0x80f0c1801030e0c0307120b0a090308131a0f01050108091b0609040f0e0d1206050102030d0e0f0703030329060313020118030602270a0e060a0302060d0b01030b01020303 74
    0x12207a404080b009207440300741c0d80113412a80009081c20810390008481201c1001040b0a011907800d41d00d40040703072801f0401441400756800350840320010040c858510210b540e06050068201c41c4650302003151b01010304510302401c10031460342080c025140000c000c10000f9000c12400115100b000325503c01020002075100c04022141d0300221085400507101e0f106291034510314000d0320314203050b00c000742002c4c01080c04002e041e0b850006e02003a80324241801040541d03000300131540401c072202c03030116200206614481c0340200030600a0240d100e0320200005040e8503a001d000f5000c0d100500c030812605140000001e4051054807d601110820200b40301d03696000540352a02c0c8181004410345060070740d19080d00c0381c25481909c105400040c4c080030b414443c07981825030800c00c2d102e4905a5020030214400080b6801440700c404807920114501e079a0381c1c03d03141e009650040c80c17942e840341007540c032002808407261182d001c2810070954000d60341c004400d03207200c1c10b50301328000b016030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 51909815 1250 51908565 51908567
    0x203070c1a07050307080c0f06100b090a030b0a0501030210030e1902030708060103030c030f030903120507121509110306090a0b0d080712081f0e0c0409020a080f0c1801 74
    0x926200740e12035a4090801c0600700040080c80680b56040c06800d050391a500d000509a00b0b10000300d10403801c90b0011404c1000400445220070161030012080301e0f00c410b1b40d100401c03c0e0002a03000500030f080190100300c0d41c40e0440c0c00040c1682d1003603581c0d14840d00307020410f6054507188000498170750890000710300d880d619920310250702d500080803606143c2c2c2d245141e508040081e00b081e00040c1c42d50300b1403000c0c0b5401c0342c0c1d48076000c8064501085640800c0d01c0040814026100c4006141c0d1504003141c0541e1280b0221040c40301c12850800c12011034030340f15801c10580307108954401e030808200141c15242e020540b03205210103815400e06640707903a024002048004441c4c3c0d4040444a86400800c64074006496082d00c01c00c29000d40110121000d0b0848400409103688040c810175115034041234149041c0031100f5402c1260b020740c4600380001040c2c09103400201d19184007060011300c050f4403145441c040e100c10344021066031150503100091740b00f2000110039035009132005120035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 51911065 1250 51909815 51909839
    0x3090d05010b0d05030a14040506030f1005150901020f010507020c06070f06020703050405040f06080c010e0103090b0c0301031e03020a11041515020c010e180405071203050a0f0203070c 81
    0x4600c11800041c0e01c1d03250030002100d0201c0002c064440d58008605640c803103420480c0502013080b20168282483d29000020359a807000414004603080850085801d500d20701c60050050080200102600c0380c480c02c109010340c00030644540103105403200720560007011b204207409411185e000d0400040b5050a002141c4e020f00c1d011545e041d0414005000b20301c0a1000c0c0c44000d10070743d030742961640341c801048241c502c02091420705518040040090020000d6814070880c02802d02e1019000b0000051307005081c0e0240c05040c54100700c0c1000040c004041c01541601d11903203840c80e0081e071030b1001e50342c09056140c005000d640880300d42e2010a00c200c1c800d0300800750007080842c0b209049846a800a0081c0e4070011194a590040c40c146680510940c4c1e10418203203092810000844002800f07280040540c00d5031840310004070b800e000062007410701402c0c8100001c516050180b4000b00507900070b031800c02c0001d0f08480c1d0030304090f10200c12200390781d4001d604142010300700b0303011170301c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 51912315 1250 51911065 51911089
    0x30b040201050f0c011508060f01031704030f1110020f070504050a2a020609010207030e1c0807050c0108070c08030f090102040807030312060b03100e090102070606032a080309 77
    0x41c06403d21020441d89001c0000342500004031001007000c0100d5003520886000640004029130410810008445458000030341101e412121080410141c4089012503100d2504003502d8103c078403104809000d120200861440303400e0342c9658031201d81080481c0c43c0c41d120b981410440e0032000c010070061410340c1045070020345034100010303244c20a0180b030800210170140c0c0d40d10384904500300d207001078043c0711555100c0d0052000391f10340407465400038005031034000c1c414031031600c0c940344150020540241d16401c03a8088000750340e8110a00303000e9502c0058803071503800075000070000b44495100e988105441ca50100c0740742e08607220060600c0917118000d017501242d40d400d020000700b499003003095200030741c026100c041844070301c0b082c450165a641d0308583d105910070000e100c2c82c1c074811b940a0042726494100341496895140703545000e0301c82d111000d4112810070300c0210a00c03202d0a48040103900905031001c09501b04040755280b000240301c1c484070b40e0014400095141070040c20625 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 51913565 1250 51912315 51912317
    0x109090c050904030e010201050106080c070305070501020708040f0e0615070602070201030e03130807140a0605070f0f1103010506040c0522090e0601051c02090a020a0e2d0603060a030b040201 84
    0x3005a01c410100d003541a080b01c003a000120b1282000b81c003540c0a00c0780e14003400162924108516001c54010306921514a0007003c212002841c81c050007401e6041d80c00c0240d10800030f0340cfd00d55844085004181c264010389442a4900e4041500c82c506074020380106484110002d04101450300da02000303410104d0309905142e00c2e107820540044051009109121000714480002d908062007070345001c00c1038018606000820303580710398030341c2d400b102c000444a0768940640d6034181803402140741c0d6010840200030450002448080148401c0310780c4c011003066000700035903030302c080070842030341e1040240501240c0304009020303142503000c003400600e84e645806002c208c0e0303854403404102d403042d0080030a5034200340014080ca1a160f400c031f01d000083d903090141e21286a800103850508007810100c0c1c031650020301002c08a01403282c04e0401c200043c414070030f455441842c100706090450f41e0340380d02c1c036071205a01c909142c034106981c0540c03c0540710340038241c15a582c0750760440014000f64 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 51914815 1250 51913565 51913583
    0x611060609061f0807030e0105010503060c031b0c0309010318111005040302120105100e070909020a0c05030c061f0305030d0b0609190f05150a0c060e0f0303190203060306010909 78
    0x20030600380c0551140380f00c0c1e21595440c00c1c14074100310000c0494040e0340840130141d0401d0010071240d030b400580c01d6040400c4021956482d114003005803d203c00b030501c00c02045102145e110707440031010010308016007007070301c003031000f0303000c0f15040942c10440e00c5c401031549903100c0000c810303400c1081c0e5600503500315080ca542342c03d460743c002075421541f4000c2100f0f1a91903038200f090294281c204140109000d00000707410741814580944080018019031300e640e680840c5903034009100c1c0002e840070b5070708074068070707075440c0154002d40d182c0078112100d12941c4001801102c501004055840c00c03607400602441c20f01c268070621001900c00707480c02030ba01048c20300c9811015907506444259401022150007011807804125a22507201540301b5803103001c40740302603403501c03410004952002c1d945281c5400000300d42e02d0030307400501300e054102d0344502c14400036060105000006500550100c10402405e101c80c0c1140b0701a440304851541e0144c200400411011a9503082004401e104520780307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 51916065 1250 51914815 51914839
    0x905100509151c0602030117010207032007050d2915010806060409230601050702090103020d05070b19020f1606140f03042009040b07050703020703050303010b040f061106060906 78
    0xc80f0350b16030701c440554a050340000100042d10000240000652170b41000b542005003684024080c0440c0e0170030024019860003031418880300c00d20100014000040100401c403496041c0072a40d808400064046110700c400c8010b150b0f401c42e42c200f48505050102060705031455401191901c002418403a0401020700000c83d140e0810f0040c102c0703240c280011101502181c5c880d4110814000d401c0606005040203030743c0140e01c40f5003201d4152a010f403045211941c0b00d18009103002069481600e02005c045103290380b9200280c07070610403404540c00c446e400a04112016200c03103120182010541e483ca4042103080d00400340e0481d205c0c7d00303961303046c1000d840d00700c420302641c002c4034111028a031003040c1c00d03052115202c5264440c00280d130a10802c1c0342654030494100e5003e0502b41c1408404a818020184208800d0000d11b6000082c1d0307031a03582d1174a20000f9608140510190714040c000c020401c1c0340708000054040d84c41314020899511103200340442c42d40080c1007150004400201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 51917315 1250 51916065 51916099
    0x51005120102120c280912030c0210080711030301120605060102030409020406030605090f130816080c0703170a020706030f11030f04030e04020913020d0b0306040804090510050915 79
    0x10b4441c031404c4040640d5010b0002ca1310070112042c3d900b90f941350081549044040d0792000c0c3d06015141c1d4042c2c5c0c0403001c2120700b010b4911b40c0d4141d800a620910410005441360790040c4414051040c41d22a4103c0000398945181c89000c02d00580b2004440c3c0704498010500c0c0760440758001a042c01900d203000d8940986800ba41d0050f080100840d441d80300030007843c00e10302c81d481d901c0301056030429010308280d6280360f00c01d00c941034081c21417100841c515144001c1c0d401400011507003e00b0055a4108140c10140c95404600c4180c1e00101e51140091035521014125640c03c8001d502074018a811b00c04258014601d408600007019912200d200b8100b4501d40114062080740b03251100d00d20b041d00c2d004084104140c0c11034080c078018031040e00152288000320106030042400940c0721600441500020710102c000d8036854172800083c8014483c11000500a8a240c1107003407101d507940c88116540d4421038800c8a4010700000b0003d4841d50840700c494940d000c0051500c10768a00e4048 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 51918565 1250 51917315 51917347
    0x4020109051302041809030507150f060315050c07210e040905010506190602030904050c0903010207030c03030b06070308061c0c060e03070515030601120b030109060b010f03051005120102 82
    0x4100207896030300050034403503256442c080b24a034221718103040c032411001d50703801030050040f003000804114012889001c805201c2d0800d00380d940711014200a610380d681881e0f05d880122601e6038071823a00e084d0116a0703ca062104031111103401050200104400283c124201c9903000b030310b1001c10103020740c81c01e0340e96980c5c0510a89603000380c0c004506401c040c420083c9419100076040ca038600290300400a41d5008400e95140e44000c94001855a0b01d02c0f180d20304a100d0010b04a9145d440024204105078101060141c054041c0ea030800800d0320340c00c10310940d803049075405000302d10900f000881c1031074000c1904c000c10848030110004d000c0c05541d001c0d8220b050741c1048021900f084101945824200000001840304881102008080001d559420b200180015040154402d00003851034030039080500b11b0b40010b130003003002e40e0050134008001d00341d00308054006142c105481e04414400e008881c098034503c249865950f140504015030f030900c0c2811036030301d55024444e42d002940c2c010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 51919815 1250 51918565 51918589
    0x1020418050405010e070303210e030a020604260403080921010605030d020105190908070b07020718140a0f09171902120904021303050d09050a080703030503040b0402010905 76
    0x48001c6040d08142c0341603030a43d2608908203002e40e01c20242000070a91011019240c54400e6440d4002c411102c83c0310000303000842c802004901c0000780c2a5032050780051013a02c981d00030510760300001c010050040c0c0c000c400d50f5148010f4541403005202290a01e4028800440c00903d14003902c03d82e20800c1c0c40301903e0700c20a481c81e0355140010001d07403d0901c00d40b00482c3c811302c000c1041e031501c1441040441304608518551660300e413050010041078104a403600d940043c0c244800f46400e42c4025515481030041c20079280d03000820501c81c0800c0d00900500303007203a2444542d26680c604000d001002d04080d442c21160710703002c1c500045080181c00c0c1c406412054640d0341d07034585425401c40000c01040d1046d04540c00750300410f10340c0c5202d0007a80c604c3d450031200540d40d000c4021800c000245240c0010b000341c020840748500031508510a40c0484900791800ea15042d0303100300300c589a81287c8400b0380130840400000d4002002c41c000164001d105050180c039050315203001c140c000f074543c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 51921065 1250 51919815 51919859
    0xb10050d05010614040207020306041202032a070b0705100903050f0c030409051e040f060f050a0b010e19180603050601081006080a020f010f0212030a0209130603080906030405010204 80
    0x81c5814044c082d5034020f1810801020380e002d51422945a0100c1e503551001000644080542c1942010541c402e0088408280301c0a0044d182180e84404805044081b60745444662040900004480801a040e0707139055400101901d00c22440742d103510050106030104a04000701089a0340c503110301c800c05000e0041396640110b071202e00b0000d28030121240505503c0a4588210706103003405044400d0315442540031280d014000401c4c035180c005080c11801080c1418180020046504800d522540407040240e8075014540f417070780180042050001900501400c01d203805024480c00800350542d44828801c0015030071303030f507a207505050030070030303042111b4a4126066402001c00d1a00a000150500c130003d0030400000340c0c001030f1003030050f0217040d040c419400d002d540418001c0c0b001c8021400840c102c250b90380352034001c0e08020b6112415581c403e0400005981c41407240b0311980059070f40c40441245010110701c01c03c405a04000c004235680e64080001040140c0000100c0a0030300300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 51922315 1250 51921065 51921071
    0x10f02090a050915010f110a030c0b06010804030801060302070c0807030302071707060504120f0203010c0503070306061805061605010f0912050702130203090111040e0f0c0403050a0b10050d0501 85
    0x8100310740d8a209034007992080c2c4a28042c0a00300451007440385000c0403d003007141c00b02ea00303214183c1d041c0800146508180c0079404000043c56041940c41c00e619109084200941d40c4a030019224020152800f900242d0b1080041c800e860090b40140501406074082021150380c443c1c02d9490400a03070412001a040000104040d4118110441c0c00035984000351000609094004185002d94841c07503c5e41c0070741c58030b22070900c00c92079528401c00e82c001c1c00900c0103142e08000035001e84c0c03080e54100c0c006032138050001402c512510f81040540e8003800089a454a04400c0200725040280e040d810341c0400d880110018109119040900301422404038565606003020b80020200907010428094100710301001a51080744d50390300654a803400584a480d08503280e030041940c400402060b400000c2e011a41c2c0001040140c03080aa0b0109001a0382d100340140000d401240f10050642d071040300364000080c5000499a404944228030414032580d0700000b418041c000c03442924141d42d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 51923565 1250 51922315 51922327
    0x30c0c060501091401050109120201030b0a080318030d020f06040b0402011e0c02010905040203060105030a051503072301020106080a06020a121d010c020106060c08180402030f0708101d1305010f02 86
    0x1141040300341c010b106c242825030103180391200009110704d001400034100340d03886541154a13968100004003038861102182d407030b0500801388a95070000c403055244a882070441c25070380984001403001254150902400e550b458556030031504600180049040c007000c00381409008010194407000081142d85070015180e11340005818280c40f0307000309014030b004100300181640c000080340d030040641000068240c0e04d002e1902d41c0340c4085142c29525000d240c4001401407015080b240d146074000d800d01001c20440401039007220603610500407142c005544890200c1c20540c040c00e200441401c240c440c0d040382580820440d142098916440010351111959010091082c1045001280000c11001e4180400a0251650b401009080c0c1030000365035030460303c200781001c10080000d8025922070800300d40c0d4100010085540c02c0004034074000003560200c080c02c07860111120302500401441c11441c100c2900000140a82c40582c1540c1c00400011802d1055030a0400da0b0350f401600e4039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 51924815 1250 51923565 51923591
    0x160305040f021c3c020a0801020d0204090608060f16020304150807030c02010c020309040f02040b0313020310020f1b0f060a0f0c05090a120f0b01080c0a0e040c06030c0c06050109 78
    0x1031014000c1c501a81d01c1c140800304c030900c0c62461480074103007403c40b407281d14510b00c00a48001501e0300f11550a500105660350a60540d030050700a8429920b42808099101c08110356603500c100c440c800400070303460100e0200101440070030030445940c4150317032605c0e440d81c40030401502e19000320400070780e9038000c000d07456078507100d00080780303c440c80240603030107031100001c1d941d010f0084d94910840c0d4a50000c550098240d041303500030407a04a00b5a2a490445e100800c3c54011031401e0b03019002d07108070f50900d40418030071504001d111568440c2844200d0090f05000c0161112100c040d206900c0554a0301000308011881008401c0e000b144030114995240d05440740360400d4130500405200c105280d50b03410f5a0071041d034198041c041013003012418800d1801607052005000b4001d5100003040c030301408031321400c0c500402c0e40c440101507901d070001604d100d03044802030180c0c25030078000d100503842908090281216858140c0080405440d2001154000c1c2e108025003960307101c1e149892 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 51926065 1250 51924815 51924833
    0x21305100f080a1707020108010501050306030304080f01060314070b030a05060d2003011a010804080315060309010e070b0a0c0f0302010e010c020a0203060606090a030b060103090c0902090a0e160305040f021c 91
    0x101208044c050038200c4643c0042d1804806002c2c0d039041c4a00440065866201001034030000c5c03016904803480780d01d142c02404d00800b201d001c1941c46140c2c1000010f01501300140e8030017100d4a5071403c2d4916604c0d084c46c07a0043c40c024085960200104040c1c0c07000c0b43c00b4494a00950501c90080112100c1d140d082500711750700088949440f40d002c4c1144d070303e26a00442010f5001e604042000d540381c2d509101540e0282206042316404640801886103242055200c06180c0103000c04540d860f41e1126070461007401001c034004005881e14902800007040007003205003c0b4070034000843d16119400106080d1450034000c54016408048201c0643c40e003040440c3c0c004000346d5195180c00c41d040045510407417035020140140004201081070399100f0341c440880150030586510440340c9507822900079501105083d88030382055a0f0200b07004589198450048604010078242c5482c16174041d0040c0000400c02d5555803a00d81c4030001507260340e0250300e409400d105203500100300914210003c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 51927315 1250 51926065 51926093
    0x60308071a151804080d050403050a090b0313080d0605060a2304081c180e0708062b020f060d020702120105150f0f03100b040f09021305100f080a 64
    0x700304001e07488034250301d03507000c8940150f1034580c1c403c146035114106415144503003007500310842e203848100401e0650002c01f40c1414829079507448451540e801801c0c3c0745000c11f80304010703c0d101c11031250340090265002401e54202c10100410065510000a82c080d0000442c000205083d900380404000324112042040086034001c1401c150a140156544505a00e444844461412541200030b406100d200c40e0f004681151003145a49030501c9100410066428201107800c01002c44e0035440c2841281038014142001c11040b2540e10500c514141003005040e40c10043c03c189006450300c1c0c0f840101001550641d015a40700c406206000c1d100b04c1411441103940d161009208054055094115802c18101d940f9003d900650740080c0c044600a100c8a40c07621504c1b60074003450455402034840e58404640130010180b0110040c002c0d60105407000390700200b1a482d62001c05941d6121a810070451031010728140d4075000020300b00020750308a80c2c1e29034045d03a881c004101d040b150400b8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 51928565 1250 51927315 51927331
    0x10e010c030b1219151802100e0306060103110405061801090812071b0b1b010b01020a03020601150c050a0302010e06070c0b0402010e01021606030902150a0f080a060308071a 76
    0xd001180614680d80740c2c40414444a1081e1101051300f041c005000b004059040c10214208064200d20400c1d41d42d440d040c007001c0f4012a1504a43c0c51194040c80800580040180103440300c0c0da00c050044000b08140071224034008800c1c0800704e0306d81ca0356405828414220f00030a0701c003074814800500380c0201030340640310990040220320560071089040d2151650301000c034a6800700e4492925160405940141c400b107000030404014000d030004a01070000c2119000f007048903400c2e00126244d003048040680580d015100400900e8000320070103500b0441450716004100450b5601803c02040680035030060f03460302c003e26660315082c80156080161828442840c0e1403a517550000c0300c000510281c1400820a504100381c0d00070700c514440c6c50104c0074580300c2103441b81c101070020050518280e016541015400e03e0708640d0000b02c0345a40c81540b600c80c5100840d140c00c88800b05d00920821300700707464420000005882a02401d2845e100d880b42d2401d0000391000030150090080100c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 51929815 1250 51928565 51928579
    0x1503030d060803030a051b16080403020405070e0a0f0506070201180314060709060c030c02040c0314011205010b0d03082406070308010905070c0209010506210a09150b0307140111010e010c030b 84
    0xa82040c07d81d0100c2d910011002140f41d1b83d81c01604011203140100d81c07000e50400d0a00003002080f91344240444440501150a440d80e2601c410010520318040e004160700030b88204032030405507000744c0300100c5008142c0207241e03110f5107035520380440c01c140c2e0440c1c051503440340c42441981904409604042d103054a0074107400021518000c3c010819000064052980c0342e503541c500e40d20940000c1410701d4510b8007024030f03583d0b800c540041038071428070540d142c2d4604454405a407420001d61588540c0690301c0342d200d5241d00d10403003001c405031001d40400000c1900e001d805034450b031000d08400c1c0d01a44420125614180404083c0c8a009002c4420404168806001a0345a18090341034900c01d0b5446515950784452440306202803256000d00d003202038080010558007900b1213801103210f1442d0450041401a451055442680c2915415000b04100344401c000b25031030b00910725014500300303104c801400e02484c21500e10009a08180c0d444448801c1da076a090b0050800b481f82c141c03900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 51931065 1250 51929815 51929851
    0x50d080c1c110607020d080403020102160c18050c040317070b0a020904050f06100e0a0b0708030a060605040e0c03070302070b0a0605280512030f040e0a050c0705061503030d060803030a05 82
    0xe441b459107116140034012660301060038076100354140d40740c444042203204048021030500500c04d404a00c500ca54a220f1014041c3c8081d8060054034016080c02100c50b00b02419980c40c52400300116000c1200c01a0a00c04407010401e01d1502c00c0c01585250380060f500d400070414081a1140240344842281104081c4020b41d10f41c42c4c401c08041e8902e250583d450415030000622100c4103512414442002083c0081400800c000039405034810100410800e503540105446a01661048000c05510b080c000b0302d070b04289800843d0f11012a1600520b40407159448400c80401950901d040307035035980c018402c50610540441501c001409078a101d06010304507400840c4ac00c0c06240d014061244803201c40e00c0c420002d45001041042407a9200c5455014014130140200d94855040b420003010420308400b01d0220707103610b80c01c00c02502899681e4651084006a02104030303801d40310030091804d000360540304100207041c0e000051079907403c00320902000d481e405890220445146090 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 51932315 1250 51931065 51931067
    0x5010e06030c0f010e1801080d020105160309081e07060b0609031e0c0a0305030d0b0d080306010507020a0e070c150203090a03080405010e0118030f0c0804050d080c1c110607 76
    0x1203449003000c4031243c1c0342c0560340780121000c18001580c160411042c000707550742c1c00e941502041c16510288200c685030460240101d00b81c3d10f00740c0e40d070f0301541112142031019500c65040031000ca8000e464180c90407000c0070b014960010034400e4100300d0324002c200401084807074040c0c42800001121070a0800c501580040d03211710b98030000004400c0c1d0640341032170b9070300184060780300001d0040c0000c0480b541ca003096a100d034400c0281520702c51038404499494504000c0c001210f9812200c1c5a08540d074100c0156190750012100f640c2c803040d260340000310100c058191510403002551030100b00322907860704801e12060340c43c070303070302894010b104100809a001490a80c1550940741200a40d115810302a005042c42001c28425500381304644200b11454844003a00c03900ca686c403501071080e40f4400300c40d10301000c84018034511003040208024035203e0791007980c1034041d4242514105078154034524004842c0c40035403a0040c0c4651848810360804400c90304400401c020f4895413a081c28 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 51933565 1250 51932315 51932323
    0x60c030e090f15031c05030402010807050c030417190c06020706050702090604020f0d02040e10080f150a0b0415030618050601060c0c051002060603100c2f06010b090405010e0603 78
    0x480c4043c0404405030725099a03408004c08284000c20155010801c9401e40c1d00130100c0d4002c0702e042c1d000c55030510100b4185d0348910100c44810b51071501450802e410043c451a08416440660000d803085080a0300c06014090020700d200c0e10540c40840102d00e00308000c4c0c10005140d21844c20b004043c0048400350303e488110580c00a0211401691404149101c2145000d510074452800c1d10200c1e02283c4124035600850207100800e40d807101071652074a110342e40d01c00100c100d54182e00911984000141030480b06038010080d04070100b0074401384c0000c1800c581000224201d6810b6850003001030120134031403000e550060510301c80c0400e80603143d1070398504040c40360340d003048100c500003824041d87c0c85070400980b4000f01020403c48202e0700c0250340b03d038150f621750301c40e000d0851541d201e15520310030031510840c161241e00c0c801c1d0341c412806841e0088010a50540e15002113450300356001406820301801e003100c1c2a54452110800344404c4600c148c02c020420f50750039041c020b00e654006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 51934815 1250 51933565 51933571
    0x50f0a200c070f080123060d0b0c04051207090b0103090c0308030403030207080406050304020910060e130f0e0a12051309020309010908030a02070303140f16090f060c030e090f 77
    0x100c40650710704058500d146000380c243d0021980d5010000c01051014040d00458443c091010150b541c1061000d1403040501007520501d03440f84005441000140400c45403913403200f403582c941070416a503200400d0a5441c0c90300c0c0c4541030341000c4801d01c01106548078001d5104000c6c642000701ca8556503620450566a02014004400102c0020200761080e012560060760090f00f1300e48070b650707132030002c0c01a800a5404034807400c810700000303000010140e030b0b440440d80385940b192030f000b80450500c4100c454000058080640b00c0c10340d04010081801341c42c210b00d4081008042c90100c0e07052201f03004030f00c1c55400c5c0800c5410007460700e1044929403280180c980c0c00c0401030f904d8460a01007401080410801012050b001c02049901003050b03010300b01d41030081d1803e000c3c1a5000811014100c000c0720094960b200074004941000301600845908448034100381107541e807603a04910841046a0004c400030b0801034031003040552280141c08414000d0300c1d42c5210342040304030180051401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 51936065 1250 51934815 51934871
    0x30603031c060b0f0711010c020a050d1401050103110111010603030503010504020c0a050a030225261504050307060c0509210c0406120b06030f060402090709080d0201050f0a 76
    0x41203050107410035980c070160040040d40700440e9503800900b003160301c030f40080d03805880a0f407030780c0c0310b644065000d00300b41c1140c503500030000042e29040c0010001c1d920346d008000c1d14281c00b462000d80103000300b44641c5d40070318041c030348101790a50500001081d030b50302c40701d603001207074103250341040000e400c00e050300d0545008540150302d81c1002c40d03241d850704405880140040c4a003031551400d00d40c02182054041c0074030001d200d105c9054010f9051040e1491140f04005561004c0034000701d001d1540000c100c600031007e0300d440303200485010708110b03019542030340e0741d810006140040240601c14031aa0242c5401c2035403c0020003000610500100b85000003514000e81051400050601031042441002442001100c3e101c1808100c0c922582900301d6940402002288981c45d000800200d003080030720082190703544542c02d00842c000c0242510050040082c408a403907582489206583e154a82c000919440e01ea00040b903419005003154201c0c4d840c005800d620303107002c03541c43c7cdc03014198 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 51937315 1250 51936065 51936097
    0x50403030806120109030f020709112502030a050304081905060f0a060b040603060f05040207080a11070f0b090307240c140d0507060f050613090c03020415050306010b03060303 77
    0x30701000c200340c500c3d5114000059480e00d1280f4040540003040e240c011405582112081921882d00e03804541304c1082003420180c080c4002e002c14001080420501d0006d42e00c1c01e0301c0c1020175070201e85828503070f43d02140c050b0408a424092030104009050008076a0000396a40a1254551325140c01c000f4100d4000034500784002000f10381e180c1c0280008040c4402400c2d034803659040c00130b000300014000c5200303880c2c0007071002400386000d0080e906160303008003009140ca04981e03019940d207000207250311018020789000081820700d07400311070020154030a837169540a071400f00f50030481c05820500c502c43c030a100d2011003c041110214448a107400d0106401d40c0c02e080070280c0f00c4011031f440d8814030890011101c1d4075404806062040d220301414090100d031040c2c1e02042c4c41081754141c3e08005802c0c0c11042c0b5500c42d800c100c0b212801198588400b41c2c598022500b9150400012040c0b480b80351000c000c4c6060400469005041500034141075040140009840e4440d0070000c04510320 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 51938565 1250 51937315 51937321
    0xc030406050a1410050102101103010608040614010902040311190603020a02030403020d0c080d0503060603130f0506040c080706080105031207020102070b0a0909060e0709030b0702120313210504030308 88
    0x282c0c03580080b0702603503c401000c8141c54a00344460100140f03000b100c2c014000c4c1101c488207104e15005000d140300810035981e0540e8203000088495481c002e0058401a0b250840814460300c41c0301014041d1000800141c2d0b204c0c19800e11500f00c410100155004045c0e20003241c0c00b0009504944094954030316001d80d13107030030780142240b840c0260f070000303540200040104400c10034080802070440361000145d540500c50340c40184d8290000b10b400d55002001000014807104136401a001040d11030640880600b020b5282c6c28604002240c040706c020000000c14020b06008000020080c031107494007141035030501000c651107101c10100316494410120f00c40c1d04581c003c0c4400c0c80940044500b03d5140c5403502ca00602c590f0580c8103120791a45013540110714040740280240c4503001130303160001a20b141d075480c24480c0600403d1101103006007010541e0310680f88004500035801c019204841c003416003010340c10300d41c241c14000414524800000500d980100640b011640c00d030821555a40d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 51939815 1250 51938565 51938581
    0xf1e0501120f0e03030601020f0303042d1a1015050d0b040608030a0201090c060e240d15090b0102010207020d080307020a020d0602070b1005030a11030a06020a09031101080c03040605 80
    0x500c2100490707818242a60f2601e818030000144d8403400c8246d0072900074002c08048952a848140d401620f41c5600641e40301c2900d00e04040c0e40c3c80c1c1224100814041c19a42d15030390510322401c0400c2501d90801d50a001082508803101009040c500195031104852000003400c14407420250140607030312000386061680c2c9540c4280000c2400006507950b1380041d1708001c0c02041a0902100e04c1440007401044c0da81c030131071104403014005024200c019000a2104005001c01941d1120b151401c1007503403c049181d01800d44070601c059980d07001103062239442d2041d14a06002c031411a807041c400e450150b40c2d0300261300c3c40d6641001035265a601c4056040b420f0510403030002c0e42140003c0d00d60170810909a000300149409800145156121f464180e0800009441550b41c540e110148410100d09005d00408003540c0c010b04407180085603907148400c0e81c014a401c0310100e000400704005009808000d0156154246402101c602d00144520502c0c00081c201074040c6640d000010405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 51941065 1250 51939815 51939821
    0x3030118110c03040b0301060305150a0303110a050d170a020c0a03110309030601030305090f0301060302091920040e0a0c0504090b13050a051014030c04090c031a010f1e050112 77
    0xb4440361030640c1d42c1c55842d034071480304a0f03000b0b100f4030300002d20703141c002940b0342c4441d0404401002c0003001c104c46030f0b26645003111241e80c03070200f0030b8850140603c410700080c0c04210441040d00651141701d421340c50580d483c180e5590041800481c03900410507a1190040840d6000b02554107041000e6007510f00c400861031341c040e1507031030f03038243c8075a60002c000d02da009005080c0ca070604a07200c00d5504204001d150a940c0781d4800250001055800b00f991b4011b140400c51035902c502d44001a00b9100852041154002841100c500e400014040c480840024103c40e8030256541081c003107800c82480042140c0701d01e11a044040f580e50100104039510740d1542081a01c110f1002d01140c14030b024000000c01003075500340782c0704c00150000241e11104480c005070700301005002d00107055a441c2800003070640f4001c1103d505410175000f20016401010032080380d05184408900381d030401c80614a0000c6d141c000f01d4030b4800314413030010711514061581040d07030001c2c600100e1109000d20401d010f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 51942315 1250 51941065 51941077
    0x4080717030f030f1501020309011d0301020d0f140f09060f0c0d02030702010c0905031908090303040b03040f050714030a060c1b060207120c0507060f02101b110303011811 75
    0x800c02d000410b010110194003041ca0007a9003a40c0300300f0204844100599903441361200a60205c1d84180e440c0243c60652400d1840541001d400585001015586642250044245068141d80d41c1202024110b486007446920490f04090f601003818050481e542d140e500502c0c107041c403000d5200184640152000341d03004d08200280a43d02c9003003844001e8040c0442c9148040001c1c40c8030400203981c9000260300044a60303032954001c400b1459198010164444d5030b140303400d0f100400c000228491800000c0d4815400380680e60301d4a80b061402c2801c104450f4088425a451584410710b0396030b0108800c01c1da0f540c003d03800100000500410f442502e01601281280040201d060b028000c0320380092010b1849414040c076070016007d410780c0d6924000b04054010740c0540360034002a40a48001000070165004454003030307100341c504c00180c0f45003103a0221320318141181540b4094000e5040d0400e4102c07080614110741c1030a21783c030180382c1541400040765440e40c401c045a00c407001e0403161 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 51943565 1250 51942315 51942337
    0xb0117071a0913020901050904020c1629030402010503060108041a09010f050c0f0708032802040314012703090312050301080d02070308031603020d1e0b0103020408071703 75
    0x748581540c00e0946542d082280c6039030081c01d00c60f90f5000d10803401e100b268000c803016100c040c100032030b0360140402500808494034851003241d1401100020110003080100104090210400704803600042855000145410040c1080c01404010307a0020306403070f400328013803030020100d0703a40e030501000c0300e820300e00724041c10808841401503072101034001f0000340c01500c0050103191036040c0070403003501c074000981e140410309102d00c000003450000110740000d5601c1d043d03e0ac000d4800c202d142d4800a0489500081c0c0e0300040800811082402900010380080000c00c48175510704441e0551040c405214012075408040510405004e29103400195402ca02102e40742d11007101c014020b51320078000c0301c11620401c40e0008019100040b007400b40d940c4080414203603220721540824000241d11034005154082c4880144602248140c1c03103d8040360f011034418080d0400e07804112104180d07514100341c0100020311030903800213681c038102e80070302d40612481d641c030181d8582140102e0021034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 51944815 1250 51943565 51943589
    0x316120f06140f030c0a031202120c0102091201143105030325090603020a0908010e0d0f03020f0711030c090906010527190e0f0105040b010905040b011707 68
    0x100b14140e9554103040b0b20b5406031403414402d59001c0806658010048100c0d510840e01642840041c490f410442e0011410b070044030012601070303a0b20a040c1d0400840c410301a0b60102e1081004d2401440b05c0c9103401039100204007503110f40c82d00700049600104070580180105142d441c1083d00a0303000707101226000007070b00d05141035291031500c0f030b4000d807070300540d1445410804040d61541101408a401d003030b00e030b202e1582e2030040113034040d41180300c506007441440000001c0c41c800a000743c010300d001010181400401100000e0855502d640c911070405205006130111103035282c040b82c0000d6003181c2d01200b00442c03100000d141c142c0c04103c0f00e41020785c0c0401d005c2c0c0c4580004185051b21022030360200301c0ca0390030080c0c14803e04000c08544006061901051420003104030303041c054480054042003038904408403030703d01078241000d4103043e9501c1c020841032100302c119240c09400403801c2032000342816240c89026103418010900012034a600f044900002007000c0801055592a15 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 51946065 1250 51944815 51944819
    0x102030904090b0a0b0306070807110106050603011203031109012118050703030e06031005010c050709050702030c1b010507080d14191803021b0406030515010611030316120f06 77
    0x503d00030700007581c030701d0b0010341442480d420130b1a01040700c0d849030816a852242c0395803229001c0f5403030454515548095560750b03101140640b46e140096001e0441010b240f03220200301e00e0018101c82100c5810800c43d03a06000c882d405a91007004840f0750522000100c01342c0f0000d07034a5070024540820840a800c600310207032402c001003c0780010450f40a501c480340550f80150030701055100c00c1f180d0010080c1050818800c42d80600a28044140120116150706484aa800702243d0f820303200100581d2000c2500020008100305041e0000c081d0507501d6090014940040d0990240b0003004003162800324881a0840096003d41503450032046080c58601b0310543c6040e13000f030b5054041280d542059039400b2903202d881209180d096040d030080401d01d1004408020131000004180e52140e198600000456070810501d000081d5030140310a183d45002005801402011400602a0414000c0060b943c0c028980904443d8143c2400c10110f035500c40c003a00201454450a2400b924080700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 51947315 1250 51946065 51946073
    0x405060c030c070306090c12030c020d080c0f0610060e0a060302030c0c07090b18090c01050913020c0d0f090308090405040f0b040303060512030c030301170c090c090901090605031b010203090409 85
    0x112400040c0221041140207448034040780900302317814400b030082015860090014104070000e90081402408901d00301038000d0541410322003100c043d215254801000e21182a8000c212800101860304015411802d0100810103410f100c2c85800305040c4e0200c0000c410a94200c115540f84d800b0805517580030f078668150000422007800c2960060180a1102c08501e440b50300180c0640d42e078900400e62005030500442f90303540000f58158001c41024282c4149041d940080c005a02c22039019060815880e1401040a1009a00c07174080041c800e00130404034032004101da10341002660042195940d81c100030200980e10000240607007044400c10090583c5580b0050540350101c44005c0c2010b10102110781c0d038001c01c4a0f1700d125800401c0104017503000000622481c003d80d500b0b4071401010030b000180440c900b1a410f4000e0800000d100205240868155003d0580d82600b008000d0519011a0380d91440c0d282502911200400b288510f80c0200180d480d0340b007004005020701082850 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 51948565 1250 51947315 51947321
    0x31317030106030f0603051b040b04020c0c0418031d0f10030b040501080102040510121112010e06030106030b0105090402180115030f060e19020d050c0703020c0d080405060c030c070306 81
    0xb01e810300280c035041020808411502402040f81e4014008101c0808100840d945620031503441e20f500c01d81c0c640c4070381216103da0001e0724403056460040e084108405080c00191013820b80f107007141e4410340f03400305d000a401a6021016580c44e15000c54072107440c0d030105034100040c07030f18146d100001d041d03806686681030304418288002038a00744070590740e8008003400d0380a5400742552140e0400300b40c0720350324030071400c0c9600c0508043c0041280010240040c0013980004030417a000141400103004804041c00d8258108000750001c1090901e903440d030581c108418001c0c1440342a044000c2019560b40380180001c06080c2c0e034503c2119651886040c003407250044111000c2814041210903428180c03207500221002014100c20907039030003e065000346095148501e00d41c2d400d02401e1244c9440f4412144100c4503007004660752005810081d240c2000401d800d44140703071050021700020007601c1074404880c000da072840e0b1202c241140245c218050201842c12034407520000101380501d0360 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 51949815 1250 51948565 51948569
    0x2030c07060b090426070204060e06101409041d0d03060f0603090503040504090807050f0309040506030604050a0209060d020d0c05150322080c060f01090605010302090904080313170301 81
    0x1c881082910885020300483c0e08080301d0140880744042596050020192900300201056810030340c5030407400c0e40003408a03162604075401c1c0c1800e500400c012030030130107801c00a070241c508004a0840802c0d2038480c0074450300009600a41d1108002d4008520f60060700b0b0420215105076081c0e1400c10358000c00818070307441100c905007003400000980070300a02c00d5040c01e81d0810042c51406081c5002d00c00a4102620221040413080111b4400f041080c043c81c00183c05070005199181c51a10802c810340f03c0107050705d440394204500380300000700001003802603035506482a007029920f410026400d88030210000e500310003140025070803c03a42444182c03d0f130310300300d52074200c00c90440c0b01c0c05041e00045500c0c446203421403180d0500310140581e4040d0790740c814030301180f03441012403203207081c44403e036503000d020880c0c0c2c4010b02040c8d8460003810040c0c00c003841c0c11130410002100140c034141000c0c2015140d0b07807000011a01001000e005084160b030000d1074012510804104603101e0b500034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 51951065 1250 51949815 51949823
    0x60504020f010e0102030910090b0d0203010501021605060307140913020909161b170a030b030f061302010804020f0301090b040b0601090501090e0a0b030f010603051b01051c02070602030c07 83
    0xd0041d81c995507000b401c6042c442c1d00c1c1030b0300a50808010b80203206c400c2c2096001c40040c003651350000500340702410001e0210300e103042c0016031694500300c000780ca002c070720703000503401060005418400d0342c81e106d05503a445005440c080303002e0381d00c8248808180c030800c0080c1d5002003003c05460035400854000344010b0f0340c150762000c8544d90368450191401002d015110002c0c0b503c2c003001051a0800c000000702c14001c9c242d004490818a04078401ca0380001c094401294a41c0b802034080e14041c00b4860f03100f04480b01400c03541c0380062603034460745014107000f414080c3e81c0340403405645813400c102c005100003800030045643c41d81048030021008030b40c2146c1303800d190030004002c1c7d4890101c180c00c840d41038481c01d240303e0401c1c11440c80a400102426095960740d504c170346403541d0030001070040002d20000015050300350304005060010242a030240290303988000b40341030744e20a0440300e8824055510401d440000d400d644003911030080003400090002c000d03c000c0d0a40c00c002417030b0303039481 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 51952315 1250 51951065 51951079
    0x2206030b0112090b010612110301030606150206150d080d1104030c080c030c120c040501141801140d0c030c0603051006020607020606060c0f1e010b09040816081606050402 75
    0x250b034800c07109880c11440010114560742004004541c05130502e06144440050042a041d100b00c00c030f900150000d91003a01c8a54442030100000351324140000c41d0700e8176034070140100e0702d010358525298003211104240515030110001c010302007000c01344c80000503c038009200da2079280c450440148c01900055485400c4400c000400100c0001e04c3c840d0150040c01520240c0c0042c401c01c20310808003c00d032046030082215800c0d85035208c0c46180e010300390a8000910101184007480031400e0781d404040005084400140701092030083e04540900c01200c0d0003e01205500d003010751020a9440100750f0f44c060400031500e9038154011034410b80340e14001041855503040101e940d02010740d04100980c112002040c0d00d818480d004014100300001125404030300d03a5032040ca0441000702040201c00b0113070a4190f40b80b0280280d40e0601021200420b450130207843d450102d200e216045107100780010450400c028030f043c00e403002e040354800e80003060300e45401d10502800007101c0480c4140c078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 51953565 1250 51952315 51952337
    0xa02070b0415031a0414010602010b010504050f090703020403050303090d0e010302090609040902060408100e0105090a050d110709091401050106081905090703020904121404060c0303022206030b01 86
    0x5103050390100c84070701062800c1c1036000c0d001940105034006140c08a1900680010382d00d468038020500c0c003c1450010030401e600d4030ba0001c0c00c4622940100b8100b000c03c020422440e507034940901e191440442e103d1007191503a840583c000d100d5507000410030300001c030400100a0011070720f4501110307203460b500c154000c007100440c05c92080030040c0e42e008000707114520050405a02c01240d07580b0283c89985015105c3d180c003458070262040c0305210540300c103d0200040c2c400e00030075401501800c000c11900e03016544454a495500704207500b04204d004054000e0541080b500d00109108401008030484504000c60300002c07070081e0482942c24000001000351099109500c5006482c039000701680c00642000007030200500148441e12a190010000d6a111100103014620a0640b4109440504000340100d120302c0c104030748800e0144420000c0c00d401a01c4001d0345a170519006030344684490b800b80071852449910482090005004100c1c035070182c0c0166a44502600c0700d0742504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 51954815 1250 51953565 51953579
    0x6070e01051201060e030a0209090c0a12020d0213020d090f03020d09060917010f060b0306090106080903072d0c080f0307050318030a08030a0f05011401090312091205030a0207 77
    0x110a440154256442c14401005030710312a40442d419a100102138032107080c20341e000560340c10f400f07a621850742c1d0012170508401e0b290ac0c2d1404001014010620f4001028580008040d0b010012029004000300c1c0701f0ba0308084602da040320040030188004001401081c00c110b01403400c481d400318054866a040d0301c013058003403255035045a079155100040541804a0300d0f10500c00030005884c0c648d226000e1300140e40c01400390301c0c05031044405d4a9141d1510404200c1c005d0340c10fa020030b0074801d0603030500142a0700801180d0714150000c4180c20318800340b07072080d0215140e00b40d000b0000c2e451111010100f020302c0315180102c494a0003152489183e0986441e03c0e0300ca02c403001409a40100030382407000c11001f0b400d94800e038004085c0c0350740e054a9160781c8180e5104940b001d48841d0b542140008402c0d070b510486014211041200340302c40c0030840040c0c48540c00713010107040d1440500c0b200701c40c00c0c403440c0340d45c0c090310b154440c02c2c211780d0581c0b6000c1e5607504520855000341c021468085500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 51956065 1250 51954815 51954817
    0x4030221071403011d1006060513090b06040306140601030c030c0e040f0b09040c0e0c04050f040b040216050a1a10030b1302060a0503041b0b070602160c060206070e0105 74
    0x4000034101a0201e2480e04100819005201c111030780c15540311110348104811800201d02d100f0a454040c040c207014010304c5c5000c41c5e11580040d407d215052025031a00146070300f0f03000c1516060b03240040d01080c81d00c00544280120790006042c81c0c18204560f040204200d1054001c4d00300b07888c14006500c7c1c413801a401d5034000401d250004018840724034483c83c00f81c005120000414400050085101c404030b000c102080780c0565404204490400c007500214281c5603000d01c010300f0160500b81058005400b510f0301c0d8501030b110390703114039040310196101d0b81250448110020051400c400500d0032680fa00c03d00b41065403d5105094a103409880e600030a0380324126105c4002406030443d1b89411210074085e21503125104a040507000603140d04004180e5a19503499198a0f8900381c0741c020324074113a070074003000c403000444400c21107003201d81d06503040030b94009005603c0d0380e11001d000100109821002e41010718213540018401e0700440d9080c0208001d40d42c2200f5445035400549075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 51957315 1250 51956065 51956119
    0xc090b0607020402160f030504030c08061909030311041d01050a1412010b03030304080d1508070b070201021002040905070908011503030f120c02010615020f07030206030402120105010902040302 85
    0x84104000d000510f82039004003c2d84102d0139010311202603546984154084007038080b004154000f400b40f0622a40301700000c024005207008105500c2e208840c20082e030311040008403165190030404007014003c1c0c0280012600301030b85035031106d40d51186030601301c4500441408052011001080c14102082c00c4c0301a0356102f80c3c90246001d6080074408072034003491200e00d00f5541c4210302c03241c0e0358060005600590248401513181d00a0500b0307841107070742203501d669036810405002c00001c0c1c0e021031108203c0362001c04d40c648034941030005038241508120301c00d0701d9a00c00070700882c0d110816031100b40601426562081250f854490722402c0310141100074050304903904040000034402c0244c2c21580e916481c0104605000f1041101540c1d0583c0c505000341c2d4581106200c5680003407014044008144010000d000303c0a0002d5281c15403408081d0060200000190654071070511441c07014110382e000700600d40e522607040300290800e0004a11980c0d41c03e4000d00c020a00300c0c1170f084 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 51958565 1250 51957315 51957319
    0x10e010801031a040c0f1503050f1b0315040204120c051e040b01090b0c0607020606010905090a02030703060305030708031506040b0a08220303060f060201141503070b0703020a0c090b 80
    0x124001405203240890700c0f0080c421280703c4030440700444c1814540f0015070040c103940b50b01c5200940ca00d1380240540c1c000600c0740308003c116604218141450b042140400c0b0301d5100020f50320f4031110219101c0910b01d00c0071302d030031600002c1d0000701803240c851f074043c429008020500712140c6590400c0429440c1c60b100070022606c40911407402e00d020384c031801441e50141000e0806682c2c56403010f580d07402450151740300390010010008419010711505074060000d19007a070400381441e000035400c101c082c1c07214144903804400244070318000c1d40300f02c000c0c5401604413901d84003140340c0004542c0c000c41d59800e00169030341c404001410310701c05940c1070b580c09021560500024160031548031000500c2c4a905510308440f021090380b01c000e004000ca8065a0041025411f1020203c81c403003045e403022003107a240941082c800703400d4200c01c0b9044030210060201218900001030300d814800d13000000c2d01c9030001035000400d500012001a140e00c2595a100c0b019039074400702c4100d0b40040940c035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 51959815 1250 51958565 51958583
    0x110a1208070b0c0405060f090f210c040203060d03030e070302030a1202070e0c160f20180702070e09120f12060a030c1203050c0601080105070809010504261905030105010e01080103 79
    0x111041c1c000005d008c8501001d0600040105c5a03c00180240e81080342000d120034020494212000c00b0300407016440001c0d2020b52031030804101151000c00c0d20710000e0101035039558905100030f000d210403070080d074006040319000942810805507000102c403000c0098455202c0014480b162400080d100360b035095591420001124000c00249003490012201d00c400502e10b0f0b0009071100540b42ca0812070525925180e501c0a07041c407984000511815076110745403006c01c13049030b0380040c00e0800e850b5400c3c0000d40744d03219200e01501d0110040e59103049158082001001000c88502514215500104100700e0b520b8810600442c6003e0340005401e5411890f42409881d80c04418076804500c24540385213406c085c4c06615003014002c0c1c1180505944400a11100d16803001d4036980100c000d50003046682001d1307554180a02c1400c56520004018260307802100000300c00b51040c1408a440c03010b500703840400000c080354003d001701804070303061400c0380391039500c43c15119050782e9110f0088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 51961065 1250 51959815 51959827
    0x50105031504050c03010f020d14101e08010912031107020a0b0c03091e0a0b030919110909010c08090318042406030603030801090e0307110a1208070b0c040506 70
    0x301d03100581c014425036803840f40012440803a1030901ca040c1060031031007001601c0380a160b0040d0107960181050200410006041c400e00240110b550021540c0340d01c2d414554800094041e6155842d40d441b40109500c1c1c800c502d414044408000c40c500030343d5a1301000301504440c800807140c010110040d41001e04c160381404412142401003811392104d4044078140040c03000000d10940c00c0485814003504e045450391094108401d03a00301030030286509500350714041401a690728070010b81014031983d81c52085081c8407045040b050490f40c0505413080b180341005400740030300f10302282000080c11b0440024048100031003079591607201510740070401000c040400c000380c20929006404610071014030454400d942010a0041800d9140072851510303508002d0410386051340b104900301c1c00c1042e8101c003820044204c41607640c0c40704000020307480100210303601001503000402c0c03400c0d802c100c0c2c00504c0301c90302c041e22a05109002c01d603219030b681d950741d420342d001d24400c054001ca400e21078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 51962315 1250 51961065 51961093
    0xd0b060a08070806010306080a03051b070b0a0f05070b0f0402100201050c040509061906230403020a0e1306020c0f100b01020c09040303091704180908030106030b1302030103050c0306010905010503 86
    0x5840c4d00000d051401148603501c410541d810901d102008902007075000a861103c0d4151590000c1c0c107050756806480d13028604205083ca42c816001c4402c2040210400448640e0262050b20841908410460300529085082d88400c0c1000e85090380b0604200c10701007001c41c4140107951041009c843c0f8107040601d400148005254090251907004001961214000741c04104800050140da03465094005a1100e0307550650300340303101c104680000300300920140c1c0b108902e860071a50f2219891140d90ba8030300e584050b24401030401403075680000b03904580c003c400944004c074415070300191925000307045034250072030340803241581c05a04850300d68030031454001800ca9000b40a400d0104010002d80d42c2e00c3e80d064000301014280000200303081c88080d00309041c1c943c184000100810207808151500740d407600052090a04060315003004d480b16071100501200440b099403001d40d1656100e241442d02e803142c14035540d000e88104030000580209600400f07048a402a000d002c18802c1e4000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 51963565 1250 51962315 51962327
    0x516080a050709050f061207020c1c05121b0a141b0a03030804170301080d0e03030703080a020309010b09040602090922020d02012a0b0709050102120a03090c0b0d0b060a0807 76
    0x1045a106c081070010f801e501c05210391280c4240102d078003034030352221100b04108480c041484143d845100100b446000a2400901e18448400d480385880d1607d0000d64825484019108404000c0c0249119882001641c3c1000c40c0d0540e074650542e92000b407e500e621010558090810b50f000307454170380070400300340240704185d00103020303d002196001c5080c007201d6265000703910035100c66000b4500301d005281e0150702d80401c068120b003e0f524000d619100104010301c0601040c2c2c203182d001001c2241c62809600c05840714030041c01500381d40c40e15040000003074022000c9035010744c0e5038100080805035400310455443e61100e00642100f61540c080c0141d0101c00e00d002c07418016044840807012900300740c2c0c0e044a81010751039204804d000e213401c040d0288003030900c1d000d12115030024400703a03070003203041040a10782c800d2441e142c0c0318401049002d0401c41d01c000e00014240080860300c030105c0c0b4003c5c41c028010150a01040040f4402d211651103a56601c01c0010268400710f1803c1d84142 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 51964815 1250 51963565 51963589
    0x9050a02040b03030909150103060e06011706031006030302030309120a08010b13240311190c1704081608060105010f030e07050a081005010f06051902100516080a05070905 75
    0x42d0849003072804038401b0031100501515011003040209248011075a414041c40e0b015041d803050a41d4030303040090001e0081c4d86c6080d0042e0110ba00030001907003c1e20100249802101216014406a556400d000c0e45070303402901c40640700d0090080e02c038014280303d0700b00e4003080590707135540240381e190941400b1305070000d004180c00c0c1c580b200300c0080c101c0010302041c040c500001d044000e26004044026080340d051260714500e0303940502529031214440c66807090b4800c5d00e424202c2c20032446180610110900303a21243c40b4240104001c5100c080c00500e1000c4000c0c518400c124882d00e0300c1140e40c1c1c8640c2489110300251580800100e114800d800c03002441e1818412125042d0701c60300000ca16000a412401003940b288480c240010100e0042c40d004085040c001c1c2c0c0140d090130b0b0024801d204500140c400b10050404c100300840c0300b0072003c280224000400c000074101600404400354039201030900141070b02000c6a000d1200340b040c140103442944400b41c1c0d00d450071040c4001d8030524 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 51966065 1250 51964815 51964819
    0x901030c0b0c0a05010204140405060d020f0111010221010303020f070e010b1606090b061509060d05040221030403020108010b0a120c05040306050c03160804080d0513050d12050a09050a02040b 84
    0x1c00c403d02c000381d000d0020300003400340c1e00420310881e4000010700040b6680148002e01c100070040c00800961200c80c050724080c0000e1034400b00c90702085000741d019215006121f640840c030290700c0240e17070303d0b82c1d44600e042ea0300c80c1c0e00351804a040002c401c1d0b03a80e100e501418850030f07442c40041003000ca02c000203000b60344040c2c59603c1060241d449040032111411002d0710280440c40400502d4030301541c0d51095140d20104040c1880c1a840c0070a0080c000d9a4000f5121940c50000c41c0955a50084d01c0121030171072080340e020100c84495a54980d0071030b110403408180d209001084451001054414038901031355045020f414028158018241002c0d401052181c20040840072070180e010711803040c3c04005030650f0b02e0078038803400a400c82d032400c41e000c10006444180000141c5040456181d605006d03c003003a80c1e02c1d0000d4007006060350200042061140a0300d05c0d50680c4c0010369124203640b800803c00c0b16550b01e506c9941070310002000103140741c00a81d401401468264400c2d0101d80d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 51967315 1250 51966065 51966073
    0xa020303061e040e0d0306090903021903030b090a02090103110403051c1e0e1806100509041d1606140f07060609020f0711040908090603041410090b01050901030c0b0c 73
    0x34041822180501c03e8298135030455020b2140c5e00d505030249000800802404001000081c0c0b0020749410104003941da10303240c0e1051001c10300d4826001800f00a00007880301c0402e0502940000003903010002082c08030341040c1c0b0a11110413854160740841f03070004081c201000081d40c1000c0c1e030080031001c6105028510300031804d8a1104c1440030300c0c041841d03c0300a0501031a50401810340e03410303200240ba81011400f002003546a452140e1082409420900d45030046440001c0213840c403184400350302508071200c84e0401d1030004103880d00103000c2101d5900c560700c6400031100105028802d1145c20801c12075440c60181300b000a1000c94040c1c41c0000e0580c1c2c4541000701a640900c001c81544840803910206104d8000c030340c0c2c0d1450004a504024505440d07540c12228040c2e00940c03485904040009000d1100b640da540c52103410640c15507205620260800c002412412000d0f2090404400041218140140c803107068036045085604031030300d42048503c0c0350340a10014841401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 51968565 1250 51967315 51967369
    0x2010210061205070f03030509210d0905010318050601060e0406030b0108030903100c0e040209040209031501090e03040b030a0c0228030305090c0f011404051201060e0702030a02030306 81
    0x564800c20000d064042e080d0844202c250400c649005426005a5030030880900d080001a41040032104288030030781e0300b42c0e48100c510050260751090861030140602620049103265a4010042c009135642600c00b084001e8403c0c080160007088014018002d600030030041c4401c60188450f4100010014030105005e500c070707035500fa0382c01c4080c2d0081c00560320120300007565140a01452800c40e14070380301000300344500d860051042c141c042943c0e004a0340041c0502d1180c40c1c64044414034a00076003280e4a0040000b43d441c0e90384070034407480e0b440380d241400c1d41b0074800c408011501143c1e0b21048150454841110900060884c81c200c0c0c2c056209418a60000701c07078010309118480c100c0307941894a034402d814082d00b1f0f52401001c003441c80c1c10840f081c1100c2e50f1801c006a01c00c403420319150f8841c62400b00080400c0c8100d4216540c480d83c149203454cca22815001141600c080160b400034503210840d090b40d0382e010340013580015801c1440002c82a09010175a403a40705030100510001507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 51969815 1250 51968565 51968593
    0x2071203052505030a0b0a120303110a0c0206030c07050105070906020c030316021201200c0606041b030c0207081207020f030c01050301210807050c040e0f12090a0f06080702061b070b04020102 84
    0x4a115131025030b012841008d403505040e05440b800500c8206100690b00d0030300180d000406030405120300a1140c40e01001044202c907401003510b07200c0380e00078000c01c40c83c00d0000028058100a01c0307450010f1240c0c80342e2035207509003c400e0391a40644d050f100d18500d1b40c180e08209140b40240400c4000707658458140d409141e281c94135500300c0d0861075130280c4d1140c01c0017002e0304102005040d40e0145060100e0041852949410b40b41d101d001031a0004a82c40300d035800f01d007415036550041050f0310800304640c01200510005010380ca200720350681e041c030910014103445140784c044a03800300c0c0060004205607050408a81c10406140c0003190002c041c0b41d44000441d0460b030400e55507948040c10a001900b000c1c4526004004d0640c01400100f1522094550300c0e9101881c0c40c82c40200403503154520b49030300b07010601401480c0154410b4545401004010f0203048800600510130f25011403a0301c014807601d4900d00d580350315524500300c0a40c0302c6281528001e003040381184a069100082c0c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 51971065 1250 51969815 51969829
    0x1a011214011b03091104090b0708010503070b07020409030917030d0e010605060912011e0b030d020604020310150b04350703031d0d0606080c0603060d02010f0504080102071203052505030a0b 83
    0x5107210b03082380016404c2c500317002040e40d00c058004500a602c003400a2000449110036074500503812100441e10850034502280c80240650081c0c03089000c9614101081002001920402c06c810702d0400c1401402c0c0707505401c0c2c030b00310320409400030410446d892660804490641c0786004c078a0000c00c2460107056020314050042e080f143c10590b840c20b4021a510701400b50000d01c051030f100074030071401d160300000d80758100444546003059031140401c448581280000e001000840d66280d101c40d5168050000ca143c141d407220b00750f02c05051400c3d03000900203440d0780868250740003010210304641d02522109803c4003812944041022603c29a17070341c5400800310a442640b000c6009440c10030341f28503090b00341c43c00e036100f40400d00c00c004040e1070761007202c260b4580910300051003440000c010340d114800c68100d101154000100740c03092054400074400c0400d5642c0c1c1c100260754840480724920b03c1d0240f000c2c8043c0c0300c81844213000d10b100e00c001d9500320301c05002c001100d034054000180c0b1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 51972315 1250 51971065 51971081
    0x31205130806040309051008010603150b040e091c120c110303100503060a091707020a08060a020702010e0901030206030f0601120204171608030301060305041a011214011b03091104 79
    0x70550085082204250788100100000c050a0714100e00f44101e441c00603003500d005020320340c10143d40e00b4800c0841c8580d0070300000244070705c10b20582d1340d54440f2032501585400702da1280c0d942c1b0070720309107020000d14040041110142541c4540c04a40e82c101c40402500d10801550b040103040103251018004c1130000750700400e80024001c140c2d610340f0040c07600f0848010503554641f403070400c0080205064845404092022101c0079075a0a440d200050b624170064100d41c00c0c0b40305501c100f0200314480e50041080364000d88810b1070003c80301040240610090000030340052082c00442d1540c900c180f0250b070081c2f4141000d0750151030840ca02412a00a0380c46294620103140090500417424401e0458140c130800312188010706065401d50340c0d21042c41032100b01359a401c005000c0c8541d03090a40d40302e02045c20340d00c400796500e0001840381210920300340c032400c4c111003643c80c00e444144035809608a8140100510326440001580100840d0005450f42410000220070300d60f9688a0710712 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 51973565 1250 51972315 51972329
    0xc030c0e0907060305070c0201030f060e041505010b03130807140303071206080102090105070803040c030206120a0b220902010c020307030b0916030c0b0304020d02040c08150d02090103120513 84
    0x515072034005411440c100280d40684207142c81c1800307200001e9805182034a40b29020f00f030110341c00d60300403e00340040c02154042250018210240400c22001c0e42001000e100c41d0f440a01039a620f41d0680d82145c4020366039484a00e010a20b10000107124102620915005074443e540300342c2d40403c503504541c401c440503800240d0080b043c0310711455512540010300004002103081400180c0060260f124005002d030004a022000a0402041c04461006554090490b81d1034507460586c49880d18406e4547e140c296003840d101c1289401c052802c00301c1e950441281e02c1c51504910a184000d0090030426410800502c6030440562820403205004512400b00706d60b043c5403a00c600d40c240b60310000c1150007510600803c10100749402107940030f98080481c1190340c4c0e281c0c3e200040d084900584003c0d001418080c261b500150408020b0740309005400aa00403982c80004100c40803101240007540014600c006101040c0c0440c090b92403802d19041071440c14240e482c0001101d5540c2d40051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 51974815 1250 51973565 51973589
    0xc0221090907120606020109020303030622110a0305070305040201140c070504020c0304030b071403040b0613091a0a020408070306020309030c0f07180524010338030307020d0f0c030c 80
    0x4050328260380302d0744c80204500d20080082403190f0340000c0c0c603440060442441002c1e492210f102c1580840082c040300308140f2410002c03503608201c0c001250f0804074007403000c24540000210468082d02581e4881c50341659410644030b440b0b06c2017500c4ea00aa10a08800d100300480440c590301d41d40300070401108250021910f0300e05d546046103d1040041600c000c0141403080100d02051460a07650829404014a5001c0e512000400d1103a03211200c202c8005050015580c28403684150f8a145807640b05a02c01c450354889421406a00c540c0c402c0f003440c1d910050f020000319595501454000c1e0420f01641e2500301301380035103403604003541302d00d4000303421481d030422008031070b040e80d402c111801110900c4286003010180c2b100c42c02580d40320010403085010303d02c2c036038400e03404011251088541403c00c40c101c2c00a90f00c0004903403c01c0ba00d0300c080c0303d1b8174202ca4a000001d40701c070641e0007024000c4130451941c81610311106900c0860f95910312820100c00508000345042c00381682050701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 51976065 1250 51974815 51974837
    0xc08072a0309090c0c1203021e040b1c0b01020c01030506130603051501091b080402150d0b1207030c031b030204050c0a12060e130305070501050c03100602010c0221090907 75
    0x14412905128500f8052201c07407513002000400280303880e4000f101c0c1f0b003001621415000202400f04501d111014100c0c6000500402e46003110000b5080b41e0b41910306401c0204003400c506011138020703400241c0540d00020043c0701a6200f5005503510101c0075008038000c2c40f0540d0340100b5140e00d9082202c45801c51160480d010807600e0425004102800701441900b0283e1480400070350070801c130301c007080031400008003551580d0000b2883c0c1d20324160400c2da91a294642d803c02400c541100c144160749014089005603030010b04030060341d41020800a8461941c0e4407001d003100140c801c4010000008000005079a4a100d050321a00e00e440c0c0c5295500b6400000501441c8118000758007140384c0b45c4140409500418116480210b0741d43c601090815810305a40900802800070403540c00c1c50200710100041201941c01080a815214601ca449000603070030f03109a0270071200140c1c020864209030700240c0c44542c42421607000c006140424213030104519130000c40302c0c40c0c042140a000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 51977315 1250 51976065 51976079
    0x100905060a020708180102012301080d022a01110a0501020315061215040905010914060108120a0c0c0803160b01050607050a020f03070806010608090607030c08072a0309 74
    0x207078401c4039200c04500d810610b658510150003440c120155800c03461020882c2c59000354000c6020f032203403460340c0300603a0b9004000c41100f0400d005050a0b4050b2158407200301740000f5244c81c04800d00404280310700e60800c0012400d105021b042c0d4100710b200500a440f5000901c81611620301400001da07032445e114146901d8440c0c80340406024a1007008003440040c111910503130080448a0070441e00500c14001a001c0c0001c0c0d10054469440c0003039510811107075946040400503428241c5101c1d13a44c0b2442d85445030808000c200450348204640e5220500c200d40d06c00d4450310802c0410303295602c4150081c41c50300911a200c5004402117041011b000f400d1b2001801420704890051410b581c542e1226110307410040002d0190048049591440d0b6090120034081d1559008983d125030b5900001000ca920544115202d4000d03c070108a00d980b090250b81d40000f40d075150200f41ea220a90304480d0b81c103038109042c0841c0204c1b008034802031030706000c08207030398083c0e641d1040140c10000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 51978421 1106 51977315 51977323
    0x4110402040b04030204060602011103041205040902041d010803480a03081003030f08060a08030d020a110304031106030a0f0f020d0f150b0714100905 66
    0x207022078500c2440003d8422130740201c0c2d0901c070144d03031101e040e42220071081d040c040702c00007000020040342c0740d0550700940203d540341240c5003650341c0d2a24001c0380c10075041840d03203c414081850309400002c06886c050428cca001e1490a200703104144840c40114050542000980300d04110032020701c4465040d01c85c83c10b202e45148140404942c0d15120b01c010100c4c04100100042001144846034200c20f40741d05440b401c00340e04c80074400751002000101000c0c1c1c08411010081802442400548044030840c0400360301c07038440001c01f0740480e085082410300d0380d0040c0001c202061040c1d4030600034a806503105503a03a140c2c03071940400b90440d117001c1044282003007030803a0a840c2a900604c110b40c10702d45e0400041000c1986082520f01104041c540e081d2070400502c64580900010180a44107060110b800c0034043d0005081421019401210f960b0b256424010300800780 = true := by decide +kernel

theorem cover : BRFrame.Cov 51798565 51978421 := by
  have h0 := BRFrame.cov_init 51798565
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51798565 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 51798565 ≤ n) (h2 : n < 51978421) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
