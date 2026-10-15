-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3919
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:03:33.019723+00:00
-- url     : https://prove2.me/submissions/0a87d67c-1860-44c8-a5ef-c50ae1afae4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 704676258 ≤ n < 704856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 704677508 1250 704676258 704676403
    0x30c021c021b041404030f090902071514062809020f190801051309080c060412090611030a080414070b070c0915030210050c0307050606040e 62
    0x11502e4030180285007042e4410b800d003030456050222480307031444000c6440c0003410040501107150903a40b0400d0185083d80c00038554100308646039007980c02c06100c4501ca9050001d00c2c146480c01046003000341c4682da0780a100050052800e406002c1c40b0055400041c8075410b80304140c240000509034501d00083c07400c25008441942c40700b03080101d1740105c00750726500710180062640141b1007526030314107414005445e114085480451828a4201889903005071061270007584100300620031403619402c01000c49585081206543d21011980540030b6900000d16420400400400e144a80c644542103401000041180664042ca09d440c01100e58011180d04002207405018412140c4c4003000070300034a101400003174041e0003a20900301d803030700000b885030000d101c02d090b8092003a401d85480b0701a50080305d41c1d46500c1e080080d40c07018201e4030765200d0760514034001d0000d200460502040e0f481025000c0c000c0404281694440034580d0802c0317180f805145c0702d25011140c240c8085502170 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 704678758 1250 704677508 704677513
    0x303081806100302210c0f22052d01051905091f06110a17040b0d1b0507150c0c020a031203060e06030309010302090f0603010b19021507030c021c02 65
    0x103146205000000041c0e2981100c92140d54a64000c841700116001004010403200d502c584044440095903804244800400212030a110140e60b01c406600150003800b24070a4000d05c1c000b805240c01d94140103d44c20351058410500411250a001e4402c9960090210703003150200d8845021030202503003180c4410005c02008095020105440d071044068181031411501c078140100034507a507540a04001800620100c0341e00204141c04030694018021283c0281d68480d0350007541ba002c0c0040301c624070200e040361420704051a002c0c2c01140c0d40386030703c60100c4001c0390f00c0c1801d40c0e0041c5a207000e8902440012540c07400142d45007a1143d011318402e5240302c101c88201c2c60010105c5525030081301c86d682c05013050001c0e61f0340000c103071540d0745000d290245c3e407904504041190001c55101075904002c0101c00460b0743c80055019214004070850401c0350340c06421805c03a80c442014825200704003681010801c8c46210f070b088984086201d004641d8038143d44410441e465011811140042c4c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 704680008 1250 704678758 704678791
    0x6121b16030e030a1a0601030e0d020c0109090c1416060603060e0c03010c091710060f06020d05040f0909060207020d050106060e0d020a063005040209070305040c0303081806 76
    0x1900000102c59140d801c3e0000c025000c0c09940d035260540442d0088207010114000140349684680c00281c0000c1d4004185e4000e4041c0400180d600e00d80080000c2c041910701801148541c0d05100d030029490460b0784903c8220707003e058414465001071030481074081c0d298407610110f8114010302004520038000000c40c041e00d54990ba05004a4000c0e151199043c114240d034456806408503064130501801405040300303e1a0880ca081c1c0003400801c25031341003803400103440c20201d0503d000c441a1342c080c0c03541148102c800310389034400c6000303841000000039400c0c44220601c1d40311002c01c138427841c00149070040540006030803030000d28049905039140c460903c42254071808482411406884c8281d0340e0480c3d60014003246a0341c02100200b00c2440044040100700a0307071070000303024500c0c60354441a50048410302030001220140c0c015241c290126404500c2481158411358218800041250840d50111440e076030203808480d241c11800d50701c0000c1042409075a010340c0c801ba240300c0e4030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 704681258 1250 704680008 704680013
    0xe010e0d0521040e04080703091707090b061e0301081c0903060c0306030503070c05030712020607200604060306060305010e010b160203030f0c06040c0503010e0601060810091b030609020906121b16 86
    0xe02c852600048a0340345803014403c5038210008004064cd4200f21000c101c201c46803000c1801d07405190529200e12119510180d4040090760045050340c0d014802d40d00801080c00c05440c01901c005504000507200c02da04001040b050781c405000c5060a2402040303407581d07a00c4851540d00a5002510023848484041145142c10440100284400a881e0080c2115600000d90700c0c003907548003a04406c41c1303580700b5040b114030f04444034100300028401a120b544400c0020001c0002c0d014040200385030000210360380d103401c43c13241e0403218910003040c50440d2003403242ea1041d4108600300d17050b100612040c40e88142040107000c5001000d00240300c145842c1c10081e1b400300c0c481d48034a009900d48054005405d0340481d115040d0744141c20320305ca2948680c00d0054001800d0750210400b02d1528405409170382421901d8800d00c5115a01444034036200c0c0c1d41d0500f01c2c410a101254000c108000d40f001c25209031400c0750340000d408101004440c1002c220390301d103610110f54510f80c0769040b03004804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 704682508 1250 704681258 704681267
    0x3011b030b10081302011101090524010e010513020c120a0e0310050c071b03120c060c08010f2601020705031905030118090f0609030e010e0d0521040e04080703 70
    0x40030002454184070b43c4c101405250800c03031031044080c0c1084682041c1c0009083c094116051060b84a02180e5038120307101082c0c85203080704180504447c2950000041150b00550240d0595000a00c1920001c605c0c442c1880250301c0304017214242e01550b198041c41d86008006050403018580354141110703240c5080600300182c000c503400d4250310740380034842004400d800791802d02e6440424000c15007240d2468442410356541b0040410520192240701c2c50352060038898290310071300c01884891119002038840110074040c04040341140f0130208411407102d418008000121054a03c562905500290990b8090041512240d1002034404c10034044603460100c18202840c0c03a50071075042c0225010305e50a01d02900041a442c0e410100502c60b404024442c1154803041c10003145a152901a059200e90347c4001e010808564190400d810324240355009194000c3c041c14030040c40101c9200c20300d601e0005008118824400812030f0111050003038025401080c0b071075111b0060303150041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 704683758 1250 704682508 704682529
    0x60f030d120f051614041a0909090d08190e07030c030c0503070b0904050705090d0c050a060212091c050a081213050a0b04240603050607030b01170603011b030b 70
    0x103480c40e100800100708581340038400c8004140c9849001c41c0b04000c0c4480c403030702980d0820446540c80521070403031048104c0c02042044c00540e8440042c3c0e0740c420000c1d446111484411340030480b0a00010b10b0000948954100801d40d210300180c5503142045040c45d01c100360704211001002a0405d00601c0300b85000000200320450041050f9030900c10804c01d079000341d07440709000b99280d402240c10706004409039045c181c40504095880000b604003451420041e00c00e990103000030081c0428500c0c40402c43c07107c0c1040322400b003450142100140246021050600341c0b441c1d0340200003800294003440548070b01401081c00540b1800486035034244060080c01c400a103845004801001541c01b0420760f50b40c0e5046112440b4540e80c0e030400c054000031450443e98490707880b880303a482c2c080d01c80d1b111400380e038014002c0320001e80c0d4040b0240c08948940071010b0100750303401d0744041e6110b010890154001006400416000c01110240c42c140f075003510880042500c1d070483c68800d040030008007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 704685008 1250 704683758 704683781
    0x2030d05091f050709051c0b060105030105150c0309100801031406190b0f040f0204061b081c0e0703060b090708071b020303040506130501091203080c03060f030d12 72
    0x508848100c60800300202c0901400c041d0b541c0d4403640010b212a01500b140d07001064041c280903050601151680c0401000c0c541c2110000700e944049003840d4401c00549050716000f03846004004000f10080c203050f00000c0310082a4801001007981ea81c8807000b01920981d516101c0049039411403800f2108844230f15a41da1061344400d0410000c2140901000d00540c0340b00310006902a880d000301d2412400c4800d2141c0060426a20744910f5100c2d0340180111081d50703640d000980002d81c2c5100704800700540180c00c040041c00303203122100c181f000209e01c49407a108002230380d0155809084c00c241c0d40d07900950f003090b034070000200300c0c0c2003030580d255000b4aa40b419103410700d0140000380c4400c003030408062444690306508402c40d00c0c100115400b41c180141543c2c0c9951504640d000702d0030442c0612030004000b58400900f003812607000c001c04960507150314203541e07105400e05d0314940001340314681c4261411425103c545040c0204910052550380c0c03403c001201140d16170640755800305a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 704686258 1250 704685008 704685013
    0x602041d0609070c0203030d020c0f0a350a05030907030b1e070e131d010f0b0321030408070f0b070e0312180d0314030c030411010306060e13020d0204030302030d0509 73
    0x4e200503138000c0125130104000c2e071001600d89100e00300181ca4000072946c50100c2f4829030070440c0c2486881080c40d007a040307040c134090a580c1d032540350041240c00b103600c80444852040c0031503445103000d4800b541d8050f0902085646d0705990361035644a40d4000e035500341c7e03411103070310007007940214071400700d903202c4000d08012400a04900200d001c85680c00f64004050350b45441d00880201460141000300e000d0100a0008070015003c1000070039400380c0241c42442961040288403013440401103d1a0740f0040b01400c580d1107458000681c2d010b010121007000b601c000c1100002c507044070300c138040c01c0c1c540c1c0d580000d215418140b6141030302070388125190a00034042c0c0c0e40c101c54071142d082c80c01c1a0a80d031160310710ba22490240c1d0125092117107103840046c007004004400e103626000e18030560080155503003542c840c1c030056044500901403c000078820041d041c001d801c0810500d035001040000062400002515080c1281c06c180c104900580000030300c118690302e50f0280076000b0b201c8001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 704687508 1250 704686258 704686277
    0x31208060f0409020f04150f05121f0216060516110a080f070b1303090905190209010e030316140105131217040b0a0e060114010c0602041d060907 64
    0x40c854400e440080380c442d0b922500c019045444950a00f103004038043d0003440306a8002000b0a890401030003089140800c0d11000140c2d40340074031030045040d00c10030107401240d40240700c0010900c010348407407107016009c11407401c20340203a8820350b85180c002e0800182c5824207180c0f03603d04915410043e4100201112054040b003c045041050141e101002da65a0716000f00092100d00030607901814401c0d01804021080d2655480c074902e580c07013547c45c107029984440d425012101c049e11419980c41d04a01011820300c080d500074041c5840505000d40c259854400003461a4403010409000301d007040300c224100105821a400f0303500115000303001c01c1c602209241c024896000014144001041c1c1d83d40f00c03103000b41810004012009039080356072503c1e04082031203074000d1f942c64918614004482d085102c003c10f1460580c2d407040044201000ba07580110b80c49060500181c444940c00c010010b141c5000d64403000300c000208440b03402914041c001c012400c42e0044c042000c1c40440007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 704688758 1250 704687508 704687521
    0x9050c0307150c0314040f050a090c0804030e030c03060c250f02010c021801080a0b070503240301021216030b031501060815130e07080c09010312021c09031208 70
    0x10640100e038410b07140010080442d42403c861700c0c100ca010701c2416650010300404c1340341300700300e1041c20768405640300c02d600d503500c400007412104c0381c085a000090f411808540080d105e9031411210303200040c01c17641103590b03400009007080001c1e5080f14401c10005140c5804103461500c00f100324040c05036000070398103640c071100440c10003520001c0c100201e001221003190f071049101410115451003410003980c46025155540d0307040d000c140d403910721a800080f099440340c01240e2040325542c0200d0240c138001002040040c2009003074580c955003c0c84003800c01003441501c984502c0241c501c03034040a18200b1b01074111040e881074035000f500410007900c03810b80564520340c1158018500f200681d580c5591a00300201680e050540c090382c00180da008a1301030350041c95981c5441c0054500140da40c0f80130720303504c658040310b00382c211850301d00400104a02032001c4100c1030712801030342c1803100281c14140346004805404c0c008640750940c01d205103d080c1c9151101c034842418454002e04010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 704690008 1250 704688758 704688779
    0xc0f0111071403030f0a09030618020d0201030b130e0105150108010614070204060504050c070b01090606020705150732010507050304140106030c0b120903040311130e030a0309050c0307 81
    0xe00507801e07001d80302c0b0220a07254500700200c03035044500000140d110040400010101c0080d4401070740c00d1400c200360729040d481c1d00b040100e05150700034011240d0b41060f50054000d0110310350300070f13804115030300700f0340e030341240b07030281131107080034040000380c0c51401d0001500d0140111404c1c0c1e040200e00001488030a4201140d04001820454020745a40d011f10010313029000c1034002c036030403d0500b4240103402c1036003001380055900c100d6240c403542ea2104108011030360103100f40390050788940c030204039030700700440483c406000044000e85000071070344400044c03100c03022205d01098580d06801c4e51200c152080c40d501003600e480240800e081c00d00d8018414040900050070b01c01c000811000203110950201008585c002c80e805400f55a800e07044806811005402400000e81800200d9111002c022503003502da00c003090f0006040940180030709110304110303500e0002e655030086800700508101901c0145401e60313020407500c007a464464240780c50840d02034041d0340098070070720014000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 704691258 1250 704690008 704690023
    0x1b210a02100e0a140c1008150f090a02250f2d300203030604151d0c07080d1e090b18011104080a0203010b01050301060e220e0c0f0111 59
    0x1400703504d0300d0b1141c1c001c01414600b00c101c81660101907080c003800c0740358001070303c60300c600d00203040b0b0054285804280107980007a10503182d404404107000030b02e1000300d540588001004042d551009035001c8001001c038200b5104280d0f8407502e01841c000c108418001085912003a01e5503401c0c86056040384420509000300d401040400040950101141d009103024649440710b0707107203081c081000b10081d49030351050b96020f0040307003084030480e800b000e5226448211019010000362159110084a807164806012440c1d0208100b06040100740e04502520341c3c075580580000d8401c41c002010001102074055010905080150070030114900c40d441561040d1a9225144901c14150182d40100303544040442ca100004c94082407040c40050301c2e802c03441c8242e0003008401441030041d145030009215070000520342540706c490314100000380d4494030300b0070300481141e041821800d000b41c46811020450b1903028100a030400d03d048031300c040c6140000c0c00d0050146000c1416030341c59040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 704692508 1250 704691258 704691263
    0xc04030f06200a030c11151603020f030411040501091e0c0e12060103020a091e02220e0a06090b0f09040c03080c03030412090b1b210a02100e0a 63
    0x554041c0002c50b5002c18481d0a84080e2011803a50b6500d40306402030000d040c0c4c11808030003d001d04045142041d0001020a1446107000340d0040340c1da00d141c6c0b581c01c1d50744c200401d4070405409100140b04a813100d400740d40201d02c40c13500c003c0c03c03c04980c01d2000b01e40050303010171304007401d044240b5403103084401c125105040500c0c01051582003004140c0d541c00c211194150032842e48007120101500120f00103058a108a9030414519034a1480b43d06032241418101c0c1c6200d882c0d9000301401c41d8950003050b03070004031003800d8500940c0038554520883da5500509098009204100c00de041c3c51241001404005504100001e404c00c0822184111007640d14000e420480202e820b000c4640789000c0190390200c00c1c81d94031410401c0c0580c80350800e40f8129140000000f0181c036090060600106071090541c00300c1c108040083c911010666400f599a21b0340144581070480f500300d0308211103011005200340b42c1d43c0c81070001c028540300d0001b5800203464501103c2c10100c25000c04d00e0720940b41c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 704693758 1250 704692508 704692511
    0x905041d0d02010c0e04020a0f050352210207060204060e0108070f1b110409030521060d060c0212070b010504060b030601020604121202040e09060c04030f06 69
    0x30340010020840003006018003103510074035045545841d415041080c1000c1503a50700391090b5425000e0009a006010391140410008010250f8040c4203001541c3e10040e1025841d0920190002404440e02402052000021a010b0301440320701c010344801d140c00d540c04240503050100c0c010061030006480c01c41d9004c1800115040740f5058150140da050230740140342150780e550f6034080a40703002c089081c418041101c00f030000740d41901812842481d042c041e11107848400d55540d460b01c1c89046040c08640102086555000390f03102c0c2d00c200324049100c4d440c2c003036030342c0c0c1422881c07501c481500c4000511460349500b048041c2d140d0551442c1c01c00c1d407240d0b0204080014031416800c0601c82031400051100c007145050601103294280780c126501074604015141c0c0310156030405220464645016034030440210f0005640b81480d000011424a000d02c0c1054014811105030b0388654805c00203952100d080c07056104040c041d1a41144200c03203040d140900c1d5a03126102c001141d0000b4200a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 704695008 1250 704693758 704693771
    0xf1e0302031803030c0d050609010b22210c090b01210612030e0a0509041a07020c0607030804052812021005190e0105130f020609032a01050a090504 65
    0x2004005409103400b0074101030b6516443d00c3d02d009019600b043d02020301c82410000442c0880c140141100d0699941099662410070780c590b0000c403000b80e40e80242c03058405040f000961005011070032195181c00c1300344d10140483d1b4280601100507039004801d040d0b291001c0b010f902e80c2c210841c51034403480503014002d1154199001c0b001000c03a40d00c070460042d4054142c0003050307404a000494901c1c101c0c0c0c0c02e40504d480384188107220004550080045050701500d031522403c802039a9030025542c411621108048008150704d80c001c6c003000c401044100d014071080040034031010300c4009841c841024a92405684100341c0701a040010300b004190903042c0f00e800e4400c4c01b01d40f05d000012041404a03003884070203050b420501c1c91120050b545020002c11441d141801000c0c041c515100710b10700b03040003039213500c1000810018220382c03100f007c10101d1855101480129040007e4030b448280264805152480000158410b039040040410048000c250014881c0e41559400e4400082c032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 704696258 1250 704695008 704695021
    0x80a0c051819030b130c0914010b13180c02010e010c0807050307021005070c120804030e0f0109080a0c0302011407020607110409060f02040602070b0424120e0604030f1e030203 77
    0x200b030880c1c1001d44070b100d10104201da0041d9140b100001184203c103006030840e62011060215251601c21141001404004002c00a019005809032581c1955030215050750b94420310300c1960210207940c0c620f40c4684c200e020994082c030641c1007008885000303100e109651300e0003c2c5003170001840281070103404030100c3c2040b842080a01c01c03000c04070008101a08180d100505580035680040700e83d982214500401d82d0301c50060f00e8000c44d85901e501c0c0400c0d50100422070201ea01840781030420003141c000081680003041030080d0709000320b24070401c00303045000040c4030600380341d0340b458082d10410030301c00107031244001c65540700c0c3c02881c001954415030b000034010f088643c40143c40e9600303100c9014080c240f1640100104d4003923800300c0d10965500c0841480d540114030404010590003d01d690740c28500d03002c02240140c240c0740440d041c1800221000442d07030502c3c81710324987d024100b00000c242e08108507070800449410060310030700c0310030f04104c40102003503458000c058010000c0b80c80d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 704697508 1250 704696258 704696299
    0xe150a27080703230d050a15060e0d0b010b030a0c08040503030a090215120f07210b191d010e04080a0e0616050f0705150a14040905010303080a0c0518 66
    0x505402c40e0500016200b500d40c402403140c2020207005c4540b45001c0c0490000140c5100d110002003a6000c0d80b4181d5103484800c2e121110302c0b0340350581181c0c460b40c42d000024414201d140c040d00c5d01e000340a8403070422154600c11601401001e005121010341031001068000042c1c944c030400c40d55000c07812402d1440800c50b10380d40149206003260f0301060111041c813005040764800c804104110b511903888410881d0f1200c0f04144005680117902090641c0c11170329006045556030180003803050700074078519a0b090a1041c0c0c05201040c0c0f43c403100409940090003214010481d09055410324103003520b4050540c4951080c00d0f0134442e03890f6100400d502c40300e050f038100342003076908030550342d082d070500075200e51000d02501c406008107071002c9034510308250341a031004032040a01e800c103d03001c2da055039002910b61509008850611000941404c20702070280610f03c03943c2c900c0940c1c142050828191340d0703040300c1c000912200f801503c000010700761403042a180120340080010100440f0300d42c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 704698758 1250 704697508 704697527
    0x61509121e0b0a0b090708060d02090a020909070f0f0201061d07020c03032113080403030f020106031209060e0409050d2706090602070f080606060c010e150a27080703 73
    0x901c1c202ca180204019071145603c214075a603000d40c0c1040503030382c2c3c81c00d00b140c01c040c00700c42a503803000300040550054101040182d81c4001075074401407a0043c0c150000f01001303400c45209001880c07070078021240940c0f114600042c0001400203000136428a81c3c00220100e40c1c242d01f988156003070001800c420300c20000c0318861080581920355442a1110301004420407540d8000c40c0507800011914464582a0380d030251b0350024092428181140c0d001c55500e0018824002199225400440400d0600303152130070050b510745503605a036103004c60261000307100c6090140303c2c0d45010400d802040c1c1c040740102c52a1407928002100d00c0f03960800c1c6003c90710040700442506d0b501007000ca520f607001400c0d0401e98800d83c080b5109139648a0103421440038500402d1826040000400d0081c01c1c200041c0405039240c4001288000a0402aa02d00001c0640b44070004a40d0b20078802c1c41210b9125641c4c00c40d203400180101007045101d1072094411411000f0b10407180000c88a00381803080d106070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 704700008 1250 704698758 704698763
    0xa061b0b0a020d1d03030606091f030c030609020a120b040212010909030905030d050412080c0102180909010b030a0b060103110c03030415051512030f0c01061509121e 73
    0x1070500c00119002500030520485680f494040801c40b0228844403410041800d440110319582d036075014400c3c650021400181c0000304000c40603030360b01a0080207462540c0b517503400102141406801000d41d0340560045404520420001440d258003241080f0244250b05001c1003000384100400c000303100d0040a82400f0b9440e02c000301311b9800940000140a010360780719440f1035158400c058540456a00b010003141c4104420070403086281001505140960030160515248040702800c0e41e00c03605640c41050400da0030030310546007000c8001c1d00b00b403649000b049005580800b09a40b0103000701c1c090a11080c0a00080d0309a1107a0400709148200041c82501c40d0010940c0c19170b25081036071308854149055014000100a61084c0f9204403105201d0751300300000d65050040c038203440c146001190008004102e0045000c000804000c801c0307000008401349017803060607041c000070741c2c28820080940000c000070042130030b130381600c1c0360030810f411500141408501c10480501200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 704701258 1250 704700008 704700023
    0x7051806010f08040f0b190204030c080105151315180209030d11071406070c03080d0b010302120103060203091c020a0209090708030921070308030f180601060c030c021c0c140a061b 79
    0x20040002520350b900c211038cc2503009224079150081c10406054a01c460030760001284c0700f1588030480303507801034262045001341441038952600c031803034400e14042500d204010b40014505800d814200072000c07a200719854100b0400d04070489040d01c0d540c030b52140b40c146c100c03800e11001707003540c2d100203c0c1c9199600415140420344d4a2800381e0071a008060304070304240c2b07020b81840b01c5500038000c54515610b8401042c98680c2180d031910000d40014107c9401441440801440422943c030043c0049065400a01c000300d11740c41048100707140140b1284490700a80d8082100c01000010344200343d03400c9925050040c0380c241001d60101d03121030342d41024030448400009000c0c2150045000e00c401010b885d0240d038420542071074021550401c402c917035000070700400120340b0450f00c14840c10312a28242c1110b1b42c440d0005041d000901c80c054032803a8444c0400d000300201e100c042801041e030074100c140124a510009a40074000d489503800340328800c91940000080d8503062400103500c1941d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 704702508 1250 704701258 704701267
    0x6010c11180405060a020403030e15120411100c12030c020a0b04061b2d05041e080d1b0809060408060a05042d021207051806010f08040f0b1902 63
    0xc80a4078501c151000e80d814014030f4003040d0607500500887c0c05403500341e02c8840c50a941803042c000d803121020851880120280490310044c01c81501c840c2c003560040031300301420754440c0c040140441018448006120156001070009000850580588841c46c01c0000d041018414280c1c184014604006c021215001c108000c2020950281268022800044245440300388059036141f000c608801c12003100c8000388004241000e1942d11003040510740305041540d201c00d0103420210007000008041410441031060351420030a0744081e541e075281c061b1070451494110a040300116602810300000065844155243e1000b02e4004000c02c03012a40c640ca4520181801001d059034202c44000b41c0c000f0380c075a001100a10180040398020706018082e00359402c12128011462810400b40501c03100010303e07556030291506280c641c5414031645241820005000101d00b0800ca03003408110310901000c254040a0310310150742c8100400015140d010210151050000b9134290380e41c0000b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 704703758 1250 704702508 704702539
    0x4030f031206060e060304060b0109080330162709090506240f120708030a09050d11090405011410050a0801060803090d14060f0115031406010c11 64
    0xc640210900841e03042002e0760700c0310011280904040c01a03544440b0501c00300e00401c0341540690b40d65141410300012103551450000d045070407440b40e02060240311400703035110a81d1001b0203d800700d00d080f0041d0702442c140f0b1564070050b10000e5013004120007090303c0c03800e98002001584002c0560b0751303085003480d946c40f4090302030001c05204071864081c40000c110780b03c807042c3c022005030454030019480e000c82c0d0801d0118104100300700580c000b181441c0c000c1140400d0003010003912640c0091540c40121120141c40108164095405600d9a030700c00c4022800713049250f80401403c8401c0d2105031110306005000d4522803d03180e00100342182482019600c54060400301d03002614075201c12a81d9a41d49422100340d071094114a40003008503d0462501008902d141c17445580520070002c4c0503001e582c58602e0407a0400f0207854507200601071030110f80c01582c440d40c1d00d4541030201c0924400e010b0f0041a0160180e4140880e4400da04108800f04005007817480003d0041c00080c3c0307100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 704705008 1250 704703758 704703767
    0x3030f0a050423041a0a2d0609081603080d0c0c05070e1e040b0601050f040f0602030703030e03090307030314070f110a17031e22150201090b13020604030f03 69
    0x202c601901c03491030910360001c1011102d07403212507100000d09690030070b4540f44c2c928032207100d07405400211f06c415011428507565100006070107020140d65501d0982e0400550914004040120400d2016410010400184403908039071807880700c0d02011480040c1c2c010140c1303011403040d00c01032503400744500c0411070100520030144240640389200d03000e940740780c6950304803a4003960050316501c181e030300159455003e50003c10b46405c502c0181441d241c3d9070305401e86000c2081d00008016000020300d0418168980141050004141c001c1c41c40c041540e80080c0c0e83e031150703120003814428800110051402d0340410341c2c807055084560300c140f0300b0031890812203072980244647d10412550101040c801c40140c041040400002c0c02540340a0000b155800b000d8a542c00c20455104100503202075030706c111140d00000302c4520309010303c4600b086a920340d8511a95005011a072401c00000042a10080015080070000c41c1c2c00314518024000b0a05600c15a04080c1076401c1000d410740c105a0711 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 704706258 1250 704705008 704705069
    0x207150b090114130c0507050d0f08060604080d200d02070e09070302060301030303050c04090e0a030201201602040b10090e0c191b0b1303110303010503030f0a0504 72
    0x1280e0041c826a21000f07a14845142e10316403e804c00b000100301c0ea011551944403401403640c604003641440b140390b03039880c504050301c0701d40c03800034618888240c02e843e0441190340d00314000702d40d00303410503051003101c544d60015104280c041100c4030800d00d032207486011801c0d2015403208140c582090305148007946c0c0c0c26144c03194205541100c00003440a6902140d10310035254003d140903e96403035034070114060700e00070303000d410107110401001032032001522890a2040c603032070292100c950213040290071034001100c09100104004001d12140e68150101e40f203107400c076298200690702a00105008002c254402c40d00940203000f00132109411048400c22500140307520100c60303403441c030886002c0c0100c00b004140001c146000c00310306801403c4040101c01f4828200303041101c02d0301e644440b83e400b030f079560691305401016103040c503a000d101c00803e0040f00703000710315651400000c00e40d00c0c030a00c202d66094003c042102040343d4032500c1103a000b41160345103892910b0701c00340c90303e886a01c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 704707508 1250 704706258 704706281
    0x23030a0203130524074e1b060e030f090a2102090a0b03070308030a0b01020105010803040504150b03010803041d1e0943121104020715 59
    0x1e91040000d040ca811101600f03080d0b52241c4a03020246100020042d0340c000f400e003102e50b082c1c2c19100c800300040307020801907600d40030805a0800c022000120340300341110707280c0c9010008140780d0310809981080304203102a10301f0051021460850a0060082c400d40c00c0441d96030200141c5011034012180c080c044409040324200900d50780c410024606c4098003001c0c014030711407002d11401510b8030b10300c0140d10a0800c2c40102c1c02c890080002030802c070310354004541c008008414020030210070720032440303507400a0008201c154189006560340e40594131a1707912071900c0d00070180020300915101c81c0104860b490160310713035850301e030101c1d104d402c0780c021804002500c103441c045140741c02c2d000c68010f8400da001201e04403290842c100207000010f100000034400e024031040300c0c09413109541c0c01c0d0350040508019142c503a03141d0081041d01c0310240742174550040c005111554110301c806648541c460702c1f07803041034200c9003c100a80035010b0003030082d0452420a000d8003100e5040703101900d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 704708758 1250 704707508 704707537
    0x31c0507140c07121a0a050103210801030f03111504030311030708060d0c0f1d07020604120e1929180603101a1306031823030a0203 58
    0x940c0809001d80600444040e0640d50b84070100410211041102d200c4150340944080100400d1100016008540c1500e00701650f80c1c0e600010411b100412009852400000c16150701f00d1460301d078001c2c00e100043c080a044e2003481c0c4603000c1010f0164114414201d4400f069450321880c1e01035041c42d0000485060b0046800c110b41100c03241c050104a901c030707032040e4a603c0020f80310130381804a400800c410813603844c034a500000c101440710100d80310003010f00240c3d05800714080d03040c8013081440034082c08290344c841c00a000000f041140c0405040780b861801c0110701d41c0d0880080d130321051b1b40c8c040e440c00c546061008104c1500303003040100c7c013182d605043c1100114101941146116941c1911004540c440000c01586002c000654003e841100140d103540c0e1103240c0b03515042c00c440b401c1c40e42160000303030803026402c811300c030b81004000e00c0c1400c1000c0d03d120034120070808103001004000100e40072860314075109080305680c46000342812680c07214210761707000e941c0754800c040103031581 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 704710008 1250 704708758 704708777
    0x71a1908010810061a031308031023010e01180302060a0f110f1f060b0c0102090a09050f04060f02072a1e031e050f0705040605120717031c0507 63
    0x1070f294040c030011103181860000b2041d00320500d00801e070b000905803900c01440303c4056004255000040c6002e141d4041680c46074501d442080302109000d8082041500515524a11940c1c1c0154409034280020700b0911203540044058813480b072015000254454000300701da00901d940301840e00d40c24002621000b40f01a0b040800a65030791035103a010030b1903400510941001c9140d4424040c0b00109401d001c50003030344070145100c49411150340404240c2d400b06003c510741c9860030b0030100810707000b0310420113420080049492550001c1003d401c0544401d9906058071081d07040b184111b811004400100600044001c090000c18544814440c2d100b4804a60542c044600011494004c1c0c0b402142610307607525a4140038215074aa0605180f4540130303804030340c06010400031000c0c00000740000c503081100b0081100c4031900180c0c010107500c1c0c84c0c0491a032002a0f1542503812207009580044000fa1100d86107100701951401e0b1224009a122a175280d10b801c52030098119440d51000b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 704711258 1250 704710008 704710033
    0x20a031202070b06010f0c0f1a010609080c0d0f150f0f0e03030406090f080f121005010e010804050c18041e0c0e10050406030b2403071a19080108 64
    0x6902403090301401040030380e4040340c229805448a800031b2404c07410150007040d06902c2d032641a1403050815541a9540083c19007c01888031695024058600f4101625804d0181da2691542c55a0409000340300344007440040c01200c6501e40761095014881280a01070644a0006090400201d1f0842400c000309070b00e480c0701c28010b18900982c900010b5086588036182c40001d440200420b50b003143c10320075105c0c041395150303000b0f01a0b011803120752940e1380148001418401c0000b4100320000c28034500a0141da0b81c491801e60608900f403030010316607266420414140038207164044d03880f019200020300e0744480521010b10603800b8031401058840039541040300030f07015003401003010074880c07000d011101c010090b16811920540c11406080d0300c075400f1078111009074000707441c00d128003800c000d0540c0b003680350001d01c80500c101b41500c0b2104500130907500c1c0c209010300628140564001e182a11000080d1200d140d04103001030320703007480303040058201c0030280a0006a4081d030941c0544 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 704712508 1250 704711258 704711261
    0x30112110301020309250801231b040528090c03050f01030b281401050909120f16050714130203010308070b0403020a12020f0f0106030b06040b060f0a020a0312 70
    0x5c960080c02c080c000700955102010000048900405581d0440c814086040764091090089580710108088000c242501180c05425001894240481100076407440e1007001d420a48041300c00540354900e901401540b80410311417050fa040b13007901e09444000440100340d4002502c014104c3c1c0b0104529120007021199104090001800082c0c110001c0b94001e50301f03110701c0076800328069803600c0701d1054680791030541d22140c12030301104003a800140700d10714040b0311954202c03102000400c40714224a1405415003d110010441080c0107d0881e224a45040304003080d154050256038156480d03070380c00c041c1d40c00341c2c0d00418029000c0024541c8240160f00c02c4906032130b0440d9180e81461107c2e03484203107c2c030004004500318000c2c008040c3c00100948913101328540e047d0058000e80d900c00007030614120442e6030041040c2c0c1450350810101b03418007045070300940107550100751045054082902882003c20b442c100450005948403051b501146110f06c140c400ea80d094400d0059450400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 704713758 1250 704712508 704712511
    0x6160203062712041208040b040e0103020a06080708060415170a03080c030907050f04020d140103030f02030f04030f24020307020705121b04060503030d2a0c14030403080301121103010203 82
    0x1520200c01c110500c03c8445c9020240b0f1964820550285803588038011051581c020b580000d201c0c6030440c0060046140108031303c4060070452030444250f107030070b080003004080090031560003070b540d40c4c5900a401c400ba400c1350f4003800c0034940c5050108010028145c0c0c1c0c0388010800e500090105000c0341c12052a00204e03401190098001c1c40070030700b0b010401c0b1101c42070000a07a0700c150308014091440200d0b0188140a9140d094112810740c0745041c003030503000540c001807045410030040c8101c0e0020480c1514140ca0300070b0038111481c0020300d4071560142c0c2100c458110201883d0190100d40e1094005501c15002c41c0e00351041c0542e00d4060118006101c09019080d8000c42036251103140b0303103002e081307007144000c0001c240c1c980c1d580e021a0541e48088000040a07032181c440800706c48071000c4050040b06c112b0701c81d400d00051101d0060692070042e0300180518074180402e04c40d5103080040c1c401454002038240e81e03c1d6501e004200094950060869843c01540710020075450180b00b540d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 704715008 1250 704713758 704713783
    0x10201050403051b012a020d050921150f070f0927090c060c17040312050a020c04050106090e090d0906050a03090606120b09030307020c061602030627 66
    0x18100695992448040c100725401c101c403d43d6078807120f0b1084107080714200c925550280f900c1b1001828042d0086c00c01840701d101c4400d000d800c007d403401a403500700d0106105250460724085002c00d80c2d400b541409500c001c0c558124041001784101080c2000d4541d0081c20240c483d044944080041522060100c2c4544168043d17000040303d08101d6070500012600140391001614180980c2c40c4002c029071908503000040c8416003440c108074485a190350b1003400c000760b05080910f142d99480c0200309070000d1400b0002c02048510b00c45008021500310800010300c01e111075a101c00700240380e00600c1c468601c100c0c40b440089901329a01240c121045041075a40700c070223905114061f1519440302c090801055a5441c5440101d0f1051048001824040740f03d9143d40056044c009a90354001d00081c0f1283c10800c1801410f9070001440b00c00c1800c01d54240d40c81e2001c02e0041c0c1d00240c4207407000380d05401503c042001400b18900e990920200355442d0394918091b48a606680721440b0850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 704716258 1250 704715008 704715017
    0x31c05070f140703230f07050d05071a0901030b011d0405100503101b1d0d0312020a0f110106030c1208040308040f05150708090925120b010201050403 66
    0x14030300481d40540d141c18000740500758205141000355182d03403400e80654020b4400e109206248801000035800c0e002800c01e098005250848240481503221189445241e1003607154081f680104035003800264024085102881644e450304840103400e0343c042c200d0580028941240c2c142e5540c083c62008000d01164a14030307500d100302105003c000c04020380042c00701c0d4181d81c0000b03242d40e000c0040e80003803000d041010500941130041c05101103640f100c010140032043c01400880701b0214800251040210b4403030dd0103203050b040540385a00c60b0742e056007206000080400101b9000041d0043c602d079503698a42d8104461407101d400c8601b1804018240c0c12448030421800022072040d4404a0081415514195480d59090a03a501c541c0c09020b205d4054a020001d914100f8244800c0c83c585480307046c5406d5596807a0f12031782c4101c400c800c3c841c0400f0404621084541610000090200290510b01030250003001d0110108410041c0703a260070841d10710400d51040c02100d001d280d040d1074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 704717508 1250 704716258 704716267
    0x60b01020c0402180915030f030c1203010b0d020f071a040506010e1b0f13150908160b07060603050106090f110901200c1806210d03090201020c040203070e031c05 71
    0xc10480c4007000e451041480307107425418469560508c21a907030385038010000c55880300e082c0d20711400c1201a80ca01c11034200300740010000000400221201c2d4480e0a40050b0f80d04ea407150641d115008151000c3c00100380c215602c02c0781c410414485004901030000c4810f56a0b80d00d05801c089081180c05807d0648110460b108440d203c1e4007409102100c0e40d105070400321400c001400b11011540032200c0c02101804610b082a00284e030307180605285c00c050941101642038003038a0a90718496600e200d100040c001003808510b50217100915800380081c081d455071010500c0207406080600342d801440c1005940703151540d041160164a0181c4918507041e4039448070004145500320070840d54090280880c01c90b99590b403080c44019101c411041060030218240303c0314001c00040d04070101a0052100b561100002d0341c500740511602e00401c85d503016100403820810030a00302030708a400402441030f0b441c1c10410055088200b507045800d0052903983c03040440a0704c121000c0400c1d800c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 704718758 1250 704717508 704717557
    0x80c09040c050f0a05120109120f020604240f0b040b0103090f03080c0f0f07120305040507031509051005060f0108010e0a0203041e060e06100803161707060b01020c0402 74
    0x10054500e640c001003400e07010707980d110b02246c3c2c992009011001e07035940d10310003513040010450b42c42881e40c0c5c1500c0d01c2080c54900440103903641e0000b901c050b000f5401781d462001d030b031003108880640d40050088144480722545035480040c00700844414444d03418017500b01c01d294828851004242d4000007510000341c42524203851008000d02a01e00c1c00204000065007001d10900520f80b00c05e60240c61951182c20342800d0012120300c50348001018103010511002c1200085d818040e01d4015605051000380d01040c50002d12140700c0003049070003000d00610740d4001961101388582000d40c2d52144e202c0b0700600441e0204024003414880030b40003804218075000035406503074820701c21499841090b00740e81c0d880c208402c540b10125055034550100204000041c0150740d00415070401850425003482041c0da280e00a815007003280044c100380f080240300d14428403403c02d0701d6030760380c80341e852201d41408005002070309000c90262140020041142c03d062003241d5031441880703240541d034000786 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 704720008 1250 704718758 704718769
    0xa021c0b0408090607020307080a03030b0a08030d0e010e0d030e0d02030a050a05223c05091009052e180b0f030d05041d06010f05030901110d06080c09040c05 69
    0xc0e03401c4d4000b00280001e03001600d00b0000113026102182c02891200e140d07290040c1034400104541c0d0242014000030000c00c1400000e070f035a4561005d101103420320051401c0c500400300c28600c0340305442044080910a0340603807101048012242c160380261200b21000c0c0d0b5644100220000000c904220f051040b41c4120044c1540e01d124400c401c2c082d0b107099440f80442d440382d8020305a082800d0407800181c07940d0340c655010740000c00354202c81e0060001e101d070b0701c3c0035a50300c0b80c94026040c0c20001002038140c0d8200c400074240884041000d410184000350702e458250400d500c1e110312107828504017039036070541c450480d0a0030343c2650161030500803060290904003511a045102c0715040ca441d41d070103103e202100e20007035540702d4840d49000c01160745117100300d41000100c07444205100c0b030750342e100c4810a800036450a100e96651100342c901c6004000d403a1426000002c08204d5604002c443e411030b00850360004221494140100f0410190b14000c0d43d00a050900e00c500070170181c2042c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 704721258 1250 704720008 704720017
    0x15060702190b0a0f02060603010e030d020706060f060801181a10050c070b19030608100203040213180c0915030201030f060e090d03050903030c120c041203020a021c0b0408 75
    0x2030455000400e56404503a0440d403c812503400c040340c4207080d103800442d410007140e40d00107411030007403050a8030880525140d208204c89015981e030001000400e10001790092070080401103c0d040e4115521040100f041c0006e0140d070b081c2480045070440078a041d409170144d100709c1c041000031040c00880410031407400c10f2088005004085c4803c0103502010302100d8000c140d0607400c1a41d5007290008a510b4950740c444000600d49480740a0080120004403500e0b80e0020031001a601d4680f400000d101410110b150302c0f480d0304021028044181810101400c9881402040e1501d5115052403041e600c000f4603102c0d0182d1000f404001541c46a0440480c148205600180d41a103690007141c40c22812078001c001341c0c1c08441220f9032694144102caa0040309a0003960442c1060140b00003c0d110712260b05800559034404500f072462840f048400030301c0140d015417090300342440e02a403201440038003a80326070301a40915840741000341c0106105036121030003440c40ea40d951b6454015410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 704722508 1250 704721258 704721289
    0xc09100b0307030209040b060a020a031e0e0907020313140405391306111c0c030e1c03031d06070f050c070b0a02061021030e01030b060d1415060702 65
    0x1301c40c001003441c1e8540c000200100e00a4ac0c0c090305400d0210305010700303680c0364a507400103114800744a8031170659000000c075440d10f0084454440540703ca041c120300d1400f45000506580489610001e8024041c01084001450545080c0010760340d242c2940d07a0014540d804214001400b044480c1450003003072500f0548030038141c2141404601038001c880480359800460100c1c8901d016010160401c21a446854152110300a101c03c1180340007000010000402014460300e11410380c140c3c1d48410441444005507050030520b0b203880d040050141600c2a84030940c080b07102203d0040150219130b051096007991500c14500c004041c084482d1f9100d540380803401d009800c1c010800c1c140401c0280b0b030440c200e81c01003a140c1840c900104801d4410b9001034019034140c070f046000f00c45202114140180c00d0300302018660704106c0180c024090f6002c2c00c1d540490006060f00d201c000a50102e030607070300d442c0240300403951000c0d5410490551103002592002040c00201c0052400705981500d074103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 704723758 1250 704722508 704722511
    0xb0d0b0604031220060703022203110105070804081617010b010807141611090702061e040302010222150309020d12170c040302010e0d0b01170c03030c0c09100b030703020904 76
    0x6030049080c4d0704010050b28504002900003c0031140d120141e015105140040480c124145203141c0e03404100c1d080e811881814010041103240c24000a0800d85009005010640d40381803400c0d2440e1070003000b903001d61440b10050700c0504915890512607181128010703100c0b1007a50b22444c00680714014581c1013030070604400c00450000c0301441c080c078410107214031125030b54120074004101c0441e000070884800c543c018410003404501306004881d440002c40c060030b00c2901c03241000c0b400b81c4204800c0d00741d009080c80c04000e0300c5003102140c0045501000c1604c068000d001402c5043c2c40c074124010390300207880000b013004115180181c02001c0e41504142c540503070700b03050305424284111803030352410300080750400035560421300c00d000b41c01044030256000c408990342c5c10354028041c0111900032454101c40c3c0c5891800700303d540300c83c04000b400c9030744860f6815052a6a00d1007103031b8440c0140f600501007429101114800e50990342d034480000d00715601e48500300c0003034100940c4158401e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 704725008 1250 704723758 704723807
    0x60a020c010906020706061a121311091302040608210a0c020a0e060a0909150e2104080705032b0504050909060a1a0f04240b0d0b06040312 61
    0x400510050140317500c941d07000714009190001480200d800d040c2401003100042001d0b800480100d55407a0348035410001070341d0340b00310908003100c101a410404542041500007440f0308200e06c01041c1394010b100321401e00ca11901c03040415191054907280c0d0100c03075204007a5840389142040034003032016030380c07030060382603042d540000d440030207a9401010541c9080003030280905009603044041c010a010900803000640c1c0d50300ca041d18442a90344640b035a90f40d078820703100000c0c40808507521420020f0320700c040340c1949030180c55120388905070703151090403c0041c40f4200481e4900050380300340d05201c0c51030042d80d040d00c031440c1590710070400c21204100204569660440c0306007d00300e20b10043c020740c540711031008110344109841c1070000441c4900001d0a03502d44101c40f000d2001660b0225041210340c0156800c80000b801241c05182c0032000030400740305440c040d10104803450018420011060188803c1c0e205a0001801c04050b07000040300b1030b80100ca18008104036155006600d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 704726258 1250 704725008 704725013
    0x1713140301090503031f050301180b19020406110634020f060403090e130b0105120c1203031b040503060103030509010219060b010906030501050a090b030a0503070506010e07050705060a020c0109 85
    0x4c42d84111410f084129000b00f001d500300c0e50074020340000c1c0c00142c008201070040e51074010100380004030000c110340500e50005110440c1c02c0d101501c0c0344036181043d03441da40c590801502c550140804c055540c42003000240c419020590002404440403ea030411f11152016425440f0402161074040d88180908a68421800c10485100d103010b81e854402c0c090605a4840106401820403c0c0d030740786800c40203010030110340c00a0f0450381c048800d860540302400c2a1410450700c01d1540c0e51040d5800d00256801030080019442900e4240039000014840303c14210b81b400b50f800b5494244e48040300500003e8000c50060100308014011a604202040c490144d20031607546d08840c901d03227850380c10803070356001403100010b498a41000d200039070520000c10291100c0f8460920340646450241e0b0a9840600022188a801c2015aa920209400e1560b0358842c00c0c0324030700c11011004005120030744100d0a0703503641e69010010340300a171510321001b0b02030340004500810075540e44161800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 704727508 1250 704726258 704726263
    0xc030b030a0f0f08040321081f061d060714010507110c0d11030f0d0809010c0c080f040b031315020304050606040e34210b220f17131403010905 63
    0xa1f40515500c4c0b000548880c10010301c0450060110050840c088140e00b0380300c040040d001040d10314078a03007455601d01030894565084105c04d142d50308440001005414094440c01c428100c1042303100074025030f01c51040442d002400581d100c1d80380d80003110610f207145050440915480d0240f96100145086800081d04150050030716610b6a0702c84982c0d1010a900a03110329403041c0c0c20b000800c403800001c0e4028058100c0d0b007900400c3c0d41c030f001440c1032092803d90195000f8003401070b00b281d100e140407144079040105c03081c4191910b07108001d1698085201d4001ca910139a40800504071a03220501408090801c0d01000c4032980900038241d1005450b40e01d0242c0f12040f461005c90110305849024a0111aa5005160741aa20000140034100f044800310442607000301c00710803580e2148480b00b000c2c44609441d6403100500d0508900740f11600804a0b9880c1c028050013070000b03001560081c0d5440740b127030950f03507004500d00c08014591a10060450300d000260011401e0142542c6060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 704728758 1250 704727508 704727533
    0x250f0807051e18041b0e040b060109060912140303041a090d14071502160209010e0402030307120908030a0905040f050603070510030b1f020d020d0e0d02030f07090c030b030a0f0f080403 81
    0x506e150340420801040c41880c0800c6501302c0ca00f0308205021701e00f03040c0018070b100d000c0d019003440481c2c0e088280e820410f19009441c840b108103c1501e0300c9081a00e400d0409403d0082c442c00030070080750204d504880c02240700d07205040c40303440e60380008032400c20741809900015403d45500841a040c0180000f15000030404d007400031200c0101c8183d0703841001160b1206802100c180c9002d10104030050301c000046074030103504110019442c000400d0221204552a000900240804101409456080850703e02a6482114180a002805902c81701290340440e48168140d000d80010007041c1003a03410b01c142d8100d41e00e800300b100320b51140400c0c040010b402076442c01c04900780503103103c59030500600e22480d40030b10181503519664440145120072401181e4424154514182c0c21503408000344518075120340c09942d03803241d0700c02c41e940c01003c83c2240031b400700b03081200d140320a10b40491203442da030727600940d10007440f0a161a0f200740090800e20455290004100c0032021500000180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 704730008 1250 704728758 704728769
    0xf0501140d150812030f0c1b0709051005030313060815120c01020c060c03040e100312090806060a0e0c0f04030f14011d250f0807051e18041b 62
    0x8440c0d141c0351030580381040c61340b420042e0f070809005202200149240c425007010381c4803002c9445100c00000d45003180f094804076a60361142c00000281c01c41290081032280e440c002100b00364503540c2c014503450b07101d000844165041949000d014160041c80d08542003241c02160b0414419504003080c02543d11003542103281d03000c400312040d01d682c100030050703440d00117030f900500300620380145a60f28002c2c0d0080110040310200016000307046190814011a04424485400c1403030007000b13001c0b40b00d2405200c1c424020000014028102012000e0495420401c001c00c1a84c68243c040300030b82013810300700380b40030b810000000841c00d034001d03007a5154018085446d81e84100b0764261f003116045c0d80c2c00041901d06101d01c550510000c5086401034000c0d040c49243ca682507002940119a550082259242c14032004502050001481020f03198203448240d04104030150f019281419075043c5640080b000c2101ca4603020070303002030b513040381c410f12034485802c01511040c01e003180180c125 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 704731258 1250 704730008 704730041
    0xb04081b0a0f120201031e0237200f1b041a04020a03110d06030213050c0f0d0216240e0c0613080a0b06190f0501140d 52
    0x1001011000d03000201400501151218105480c000e401501d541c0786214081d0041c504000316000c0d039019030006140a004111035003a80b541c00c0d980740300250003c4a4801085d8284a20158a0b51813096001c094080361005608401c0c000803003120304005a9500d109425013030043c420383d1003c10042c8000d1000402c2c094540c03c240140b00c0c01e01540300d03c1426110724100706101c0c616103107554403061080001d49000d40d0340c51852400b0750203098074104a02c143c00000403c8005601207030b12801c10382c0d10840d1104c0fa07010943c200034040c0c0340706a88a00c2950010441061000050300003407126a02502c070150502e090307080c8454000302141c1d400e0724442e801d00c0307009007040c00100a0320f20450408808010b5107221030100c41e5a04411004103004110002d204111521007520f440002c0403503104035010443e8924214520380c1c81aa400c0307004003071104500741112a04070708401510b103e480c1d2240c0d25440c00004562854042c0003500c6000c80410019248018a00465455010040c01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 704732508 1250 704731258 704731273
    0x2030d0e1501060c0506100312030f140108012c1504021206040506011505132102060d091b0e06060a03020c0f060403021002070b0a090602090603010e070206070c0807060e03040b0408 80
    0x180541450f40080c010380412000b1720060000810449195601c9d1f112031400180340d2186080e010006d14891404540303c914045c00001c03000015009414030541301c8402d00c1568000750042c002c000c182e840b09180d1a080480213001d1110100082e541c001d00080803849901580020241002003d8800b96166004500144241186030b0f031206180f0100f85415460080031071804d03001c080c000d004801e000c8043d083d20754958a440e1841c1401580c00900c4031b540c2d03201d1840034034000c2055050032125203441c45400c019001e0b101c1560011034202644040c51541c0700c0040060980c0004010070505a00307200c00b0012803410084000a180c6480c001c2189003800e0501a00e000440d1405803070640c0104601000100c0c00d10a458102012000104940e1580d207001d1003e070150380100742e000b140120000840e00024070525000795069001d4403401c0d1148d4200b1120b0510004014103080410041240040c0c3d07250b0140c08012051010340c0c3c10151038000c0040260302c2a4040c02e00d681c040300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 704733758 1250 704732508 704732513
    0x807020d090308190e0307060504030204060509100e06130507020a02090f01180509030c0321010b0f040320220e06010503070315020d060b120604060602030d0e1501060c 74
    0x803601a452060400c28815440c668859109214803000c044d140c403107054840640d0f5002d00000600c1c440028155286a9155040105560821300c82640305a080071030000d82410710007042d40c080d00601c01e0300b1244604019460940c40d20207849640c12030446001002d03034090500ca1280940c0d00d550140101007800c3c010004882000381900701a650b018004009900c00031102041c41224800007250960f10900c80758114006c074486a68036000000300c1c20451480744044c0c03030400784d01120b10786440c1d0301c8201743c0f04640101130114060000400007480454040312440d4554548407039941c103507403180382c04100f01800c0404241800340d510403d42d881050b050003000c04040100d00106129858140000c0e42c8048a02c8043c0169040c01c02070a03011400e40c04450740200100c038280b01d61540e580c95074459a011400e401a51003850010072100c1c54507010303100403141158000c40c100240c94083c10000d00c4010300361141440b81d10344880d505075641a04600811884e2280600469070b030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 704735008 1250 704733758 704733763
    0x40f02090112060f0e0c0d030e060c061b0c060606090f0a0e0106020c010c0b06011103070614060a2115151205070f0f180b031b03010b100c0212010219080702 69
    0x4c920814141e060003005000c4010014054142d5081118090200c01035403c050707070b2580e200341100c0d400520016942030000c400140742409692103280140c0d1000050709060304902461300b80b9100380d000540480c030103203051000741c4400f40001700020040044c035400941d10b41e07034031b50156125803680703c01000095010b000c09010103d080c201214101c0c1d095840c141d55660040003d818040004000320300f00d40104141c03000554007100c00c001c02d100b684144d5078180400c8542c1481900c01c0100421980d50b080b0090707100030b01c0c0281c060038040a030341d1b03030300c03442e00020320301510440e0381d000c052a52488017288a0000e26214040c03418045140c14a103017841d1854202160102c242c0030100322513206411610125592680c610340307400380c03021200c8083c021011034035506114050544443c002c940c40c0e17003c140b007800c80007042044031140900480311640d41003000130a078040c0510000d800c165445801040705036000500e03024810700410072107540180404001000007040000d842e804 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 704736258 1250 704735008 704735021
    0x4090f06050106030b03070902030a090c09150f0303050d05060103200306090a15150210140709090501051c050c061b0c01050301030b06240a0c110909070509040f0209011206 76
    0x1440c0a03c00c01401c5d0300401e0795140d0a100d2030705000c0d40003001034072420081d80103044507507100018074800c948e25580a4060507840002d002d403010908000241e000d03411203e0300c2140e50603241d09040c001c8424010006160083c480d505258407003c500800c02642c2c40103c04ca540340d16095070316401d040b01030001d403201c0180030010607403412641004451000081008a42c10326142840e040e8500344101d00301402070368400c0f0118140201c0d1425500003540e00e41c4108600e6480b071000700da40d0318461050394028802c05800c050181e40041d209a15148042d0000780240c08949c150b01a4101052069000b1220254070004074091100011004d100d84103000c802440c180b401d40d410b5880d0703602c0c42103014200d24868100b0f600700c85003010b48504020100301211182c41d8450402d030b500070384558941d060440e03074001d5a80764900c0302d203071040e0711038002c0990100505206080c0b405004c1d9104002e081a921118130940c00b00060340e4a080c441c1c06890108100e118030740043c54030b40c040d902c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 704737508 1250 704736258 704736269
    0x15060a110c0f01140307030b06070c0608060f0a15090f06020a2102060c0d0b0d03080a0e06040c0909080f0d021803030a12020a0c020411040512060106050a030f0b04090f060501 77
    0x290300c0e10790945030b80d00c0f0a200d0032158601314120744c1d903103950b0010740042c440400150341003000828200c01f0b00c10903040580440300350392107100c00d50f90707040c0403c04040804040d490f40f02caa2445c0c180280c07c0307251202010841d090400c401c007240c490901e800f84203141c0d8040c0740103034010301100003080740000034a0314101c1711003405c0c0f210003241c800c003035283e443c01000242490f101159403680c687c2190004d641c144806000070380b000341c0d24180208655401c8034a20192400c280d031403030403c800040d2003485a50028035000c036840c1040c44580103400100010350300c01d507085c807120484003030074001054403402c12400142d9032004c0c060841c400d00c40d00001640f19400030705c11000c9440e04880860304442c510030006a40300d040b118240c131045606140650041e2504d04078030414081c100042095980813110380d07400541c0007050702c1e82c5010900507640026010710440000c14003982080c11400c004c01000728a4203400c0c804030742201c0700b0440c103032544480517802c1c0041c44030a116082c05000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 704738758 1250 704737508 704737519
    0xf0706080103051906020706020c151b03040b0705040e090d170c031609090c050403060f1b0f09030b07170a050105060a080c1e0d230f15060a110c 64
    0x41c0b45840b07407510b65810b8a49400d010041400d030b0001c01106904071101c01d82c1c4160115140c0b0740400d0130039500c1030318104010303080085c1400f054140d500f00d2031088030550f401c103802d89113541e2a6642c100003c3c0203482502400424040416041c04544442d442040360000916490000305002080d1000303902d2560400d03552501400905940c0c00304882d488a60800503000401e401d0004039100740140c0c0c40b20824030310b080032600303009a002008108503801454184019049021000d045078050b12003101160000c2c210320100038014501403005000a0034200542641e03074880010485046a400c0001800341d0340036400344110700340868020104d420100125030400000c10207900c02c0b494000144541c40b00060308840c00e800403203038007a0b07140506c0e440e40804052108070540080405000060800041000d034030302c105044250317038280250355400c60301e5400004035007460240045501c02501000c40101d610780c1e100800180403140e070307601214a0101e6256040207082c46c01c031449007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 704740008 1250 704738758 704738761
    0xa02010c0c03141c0f020705070504060b0405090901021908040b090a020105030a1119090e01090c090509040f06150501090b0c2d010905010c140c1f0b0307080f070608 73
    0x1a40c4406080240c54000ca81c86039035007201026200c0c00c000c0b20503c500c101307040c00a444900285ca030007903c0180d10410440300266160307400c000c02d44400d805000044041480104010b1510000d2142c02000c0c8400051a105419200070881d921842150340070860702c0c014007007003040f10303041da42d4041c0714500074040c0e82882d80c0c00204644400382650b001c19480d2508161001d44285c07c03212041d08800c03074402c0307003008400c01900d0741840e8800c25440a009000000f6078004500909150070125a0341741d546608002c20002140c101400c151035a8061410f4078001400034842e8080190102040803a880d280900050503149a41c002260101d17050003925600400018110000038189030302017441c40200180b01000c400d503c501062641c240072200e000c1c004107510042002c00c4944e16a082440c0305046801c00b885147d14589890344846c41118041004418485600540600c0410000c51030760010745000115044228203401c040381100e51040308215500040099040c8039070075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 704741258 1250 704740008 704740013
    0x61a0114030910020c010612050a0c081605040903090503030a110105070c1104020a0219031707050a1209081e0408150f010317130806190e190c0306060602030a02010c0c 74
    0x88043c150300f940c0038641c012525058280c400c0d0000005030100c0d226030f503034240c00b80c100380e0755440da18002503400701c1c0e032408046142c80010a9451a000b4404861841c06d881d290030b0100410449609078204904101c0c0414181d0b4240010b10580b03150341c0d21016070810f42c03c0064211400980b01c0d0040c81b03c800211000200a14400c40b08a2000c480041c1c83e249000002d9080929010041045140244440f010560011402d0214041c0616843e0b495904c100041d1080d11500004102145441d2103c840c0d00519400440352507105082e400e003000e504a2850302c41050b0080307010701c103400100d024800b44c5000c000303112604d00081d000540300e0030102090301c03003000180400340281401c000c4003203002c040101103a58442100c2000c924642e44d88482d070307849542c15600e00004040c0e003680e0705510b11583c05038003800700d6030304090035584411480ca00500c1281d20401c0740c0036601d8a20000c081000e521600c8001d0200350083c42da0341803031440090844801c3c0340040300344101407a40001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 704742508 1250 704741258 704741263
    0xa2c011209020402040509040803040516141009081f0e0105010614030702012904150806071d0301020a050712210f090506040303150515190903061a01140309 69
    0x40c00040e1500085601950002c20003034030858002940000894081c8020000d05800071489140210183c0e0001d010121545d10540e8084c81104040c0210b10540c010742d01d4880c11820070580c2a04116241d540d8494030300e81010342c0400c84200c0c8003c82400d448501d016400b8100401003808003c000395814247c0261030030142142e0007259003400f00008140c14002d50150340450f40c0110340390b040000d60342c1d0100125031242c0d0068003c40c1131206180019001e0590407064034680c002400301c65949040845905030701c41c5200361003404800b8138a000740c5081c40207000c041e03415039486541d40d8060400d0361550781c08000340c80c10004211180c03201c0040007008002e50009480d0081107050109440034050a404070b4003410342c0c094941071208054244c3d10411070001421501400b0507a244200000c841070700c85808100101045280f00344407441e038941400d445181003201c000c80d00d07030b00d030038040f14091810f00c241c0b80101c4074403283d1036030811042d46100300c6a090441c614645041c0554 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 704743758 1250 704742508 704742527
    0x303010b070203031c1d0c01080f0a2304050d02070f055805070323070303050310050411070b04060209100e12010b0a060e01140a2c01 59
    0x1981080421030703008559084c011140c082e6100d014140d400380b1070120041c000c0200c43d1146400c480d02880c01300101001081072603000d04144c65699042d0f4650399044803103003009010100c00c030750b1045080b058440102a05c98816084020006c42d0724191801c00d14014854458000795030144c001003004001e0150090250354054034520900c0307008a601000c5804000c102020040e80c4003000301c1e1b181d081e40002e14296403d044017080c04195040da01052501c3c01e940648540c01c000000e101180d543d64030220a10b05807484080c01d142c20500c00c0d8109040f94200701c0000e04000706111001d4048603410020386030481b41041410366500c0a40c94501c41c001004040c0002c0301c00080510803954107983c10900c001c0c0c1a5014640d116400404410301203130054480d04500600b007001e0101449901d0a400700030341503105c51410410203456108140d80c1550400aa80c60040c031078071030034000740c10220115240c1d141c00c2d80c104140715210754644c50540110500c5078161606580e400300c0d072071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 704745008 1250 704743758 704743769
    0x1023060409051e1603052a18060d0f140f0303070801090c0e0303040611010614030a0807050f150f060d0308070309060e07121e03200102070c0b040f17030301 69
    0x4454110390f0f94101814821901d10030302114101e000004280000402e088200c2900705001601c250010000e00003580440c0c0b400702e40004802d4803d119204c64407540d15013025004000440400040d074800400800720348049a84440360100421107500c108030801b203001304100954103524051000030b140e01d07414403a107003905840c0c01d4072252031809010310544518020b0300b980c4c1d656441d1000035101064122a502807503281890000301e0918405219a94000040140000c442592103481031508003000c151014020504840e0904071b0800a03c10707900e032901680840f81c40d03d0302010603189001000607010f4407d1200344000642d0003108194400380701e0500203100c114505001006002c134448800350342c4031301c04002c5440100c2c00c5652145501c01d0041078100305544403054184d4000210080200d83c1c960045116010926210781802038280001401d0043e95125060041800d5000314410304000400340803503050302d0b54002c0601103000130942124008800b0603600d102c14400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 704746258 1250 704745008 704745043
    0xc09060f061d1c0b0103030302180607021302090a0b03010e0105040c0e032d0a0b0f06030d050a140d0504061a030309150901020708030a0f0314040305070212102306040905 75
    0x86281520506403503c50041d00440c101d64290707120310b0b0181c000d600c020424403c09070114080101460602c00b2900c456601400020710400682d0918020390000d11030540d02042500d00496030307598100180d40204000d0112040750351601d010300c000c40d00320008940403c451403840d40b640703403400540c1c00d105043c51f81d44030840380140d000389112050f803100800702c3c9000c0d4071311010500c81158141406403414402d00d0360640c0f204001c05903143c0d10444500d000c50024806118094064481c0380104094030700850710340403405103601d0885104460442e91140d40e50007503001c08141c5194141f002c0f009038000d40c07400a0317440002d118a8951031000c108000b001400418a9100703004882c0241000f80c110780d00e480310740102502225045c0801c000007440c2c895284121a440020b890140f901074488914000068003400301983c13070075126584501c24403140c0380d10640c0c14810500000b03d502802a0520800c0050300c420000150040b803140b03080c281b08001049020802e41c04500f00c0101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 704747508 1250 704746258 704746279
    0x9010b0f090d0503190302091503040b1f1703120a0e100e0307020a080d12090b07050a0201090b01060f08090106050928051302180708060607030c0c09060f061d 70
    0x30903a1a500c11035042c1d00c000c0761700c8490b0220207030f0107401400060204840c2d61b1038004011184480d580400c48001d405c070b00840002c40c00d80060403080380c0c40204449a11151941c0303d540085084504641c03840995200040900c00c3c68503d0001e03541000c081401800a42c60100100d036480780346884668000d691501300c03000700c4200300119601d4a502400d074203400d5a40d02003140e03c41c0248900d1002050440e19040e224240510400d9611345e0301012000c02070300d85074402c90b15074200d44914815590385d0401300700410b00d80312229000f00341035520586510148a801400808050011145a030510070700380156940ca02004da03010390100c0c84404000c149504142c0182c1d0404241950309281005001d0f24813406050784804074025101c000f0f24002680c09041c468408554502c006030f8a21302103580c5192000040440307034001d103400c41c180a440d4030742c1d91442446500140c182603841d4400c0000d1022200020700822490400f0a43e100200c58034160414005c02c1443c4141c000c1038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 704748758 1250 704747508 704747513
    0x10506030a121b0b181009020a060c0f0510060503071703160816050c0405090f0604080a26100b0403080403030e041107200d050705060d181109010b0f090d 68
    0x107243c140529040b4a001c4507900341001904182910000700c00390b2406080825a1181c00500400344020380c050004e404291412000f250f0a08403117004039040f0b250541c0c80702c0071070006c1014021441140000181c8a842d200805103030080c030380e00100f009902e207203056410348000f009848030200044007480641c0820301c0d0908003445100240d1b64101c1c42440701c2030900000050b614440501610200b111380c47d10040c0c02d55500554110081031f50000c800100001d04050141105802904080c6500c00d80c0450415010b4542503e1980d8140340504006c032480038040144020801a0300a80c41d00e0b0540e160486e0710701c601d000190074464035008220450319982c1c019001502031018181c2c035505140341440e01c0a240c0480030741e200b5014101c018061611903020f6640350751040061241038608014405e181e049014503900f055600d615100c0c01d82d41c4544000400c40c45107003c8401081d41030108980904c0680060301421424442d00e02d03041c803440c04840d50018100d030013684207407051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 704750008 1250 704748758 704748797
    0x9163008040305010c030f05090c10020c2106010b0a050f091f210606091814090f060c030c07060207020301060801060b18060307210e070f08010506030a12 68
    0x11200a01003200094000b05105066215400c00116a81c05101103807c4500b0300d025a00181d801080ca60040c0c0342d01080d0b8600811300300d0000b01240142d600d0010020002220401c568004500c02c0160716284030150b603003409118098441100384600300310003550020101d001d0b070895076800c0200000e600d0f0440c2d0b0b60b01c10440c0040003070201c1d085403803611440201061041980040b040d40f000c6051850048180900c1040ea480759850384a482e25002c00004140c684403032410900ea40d0380c14030100040808001442848104010b2480c1540d80e0b00191418000820901c82d011007481480202e20012046821803500303c000581c60f80560700011b40141032991201d1301c2076107089c10001d4940d2003c0041c1190305120090800d2404504050148030b2208441700300008080100029910404680410b040011100c00085c261207aa0403180f40c81050b40229a07120626501048581c50902807294481001d501a000d2580d40340c0ea03608110f42c0100d4440c0170b003d4038080e280c20380700c1d00c4c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 704751258 1250 704750008 704750099
    0x2060106201b01080a1b0c02040e0f03030106170124051c0c0e010507170c07030b010603020d050a090f02090a02121017240408040306020c060916 64
    0x411081e9203492407420070b110340c0085404581c1d07001c140d030080064050145072054038000035991002c410400a245411070350411020401c070303071159960711104090b1104121300740b11400108000c40e603039418840003800c1d101c0040340800300c040010f030040c0002c090484200000c0050305001d4031800c05829026034803400307400e1502e01140d18401036a540354a1a42040102c41a80d0302c0e11074621420000440b001e00c85d202000d041c1c0c100101112003a882c546000740b40502c0c1007070a4030816900c80d59020400542030340540c0010381c0200d90b500c0c1005040c466180c000150300e03010000c505042d910341100c1310105001074840c240f4100020021441390301110284040350f02080d49524040d08081407028807801885003100039842c090300c040000040e5a660001c0891003041c001401460322400b05400400482d144e038428000000000c6540c000f4100c0200348902908140c40c01d100000d2610041c2180c460002904610411075400001c0104a08a200351108540c9041007840480c140c40c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 704752508 1250 704751258 704751317
    0x60b01140a020d08060a0b16140d02010c080f04110906040213030302070f0609050102061b04050a03150c0e060d1a09130b0f010f0b090a180b0312070302060106 70
    0x100180c1e8800c9103a0114250343d5407019910742803c0c5894880500075650650701030f12070107803820442c0154051540d0070300103403a842080007401d070320000805d5070300340034400c440200543c0d15400d0b004143c50b002109160f01c07603164540910145800d86401044950300e07811140524490008146540c8843d01110152000948505c4449079a45002942d403000751265600451602202140c190f108101d243d040343e205070b0041c0b0094680da424003990b01c11116088248a108010010f02070b01c0d814108002180150f1552603414225420f4a09030b802046507001081509000200290f540c0c0090b00d00c20070102c00005100c1c40342840050030384068a144e0782d07203c0c030464208488046200c003000030807881060418059141e510407810392810a0090390503404001400b0301900312881c0c054142d0701c2000b8486486c80341e907600300c102c1080b40d84001000185d11087c0003040303403c080101001c10069865600c0c900741098032700039110030041c01410304100051040740c4041420302101c031200714 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 704753758 1250 704752508 704752547
    0x10b0a200a05060c0304050705131b21060807061101090803040809130b01080a02210403050a0320030606030903070501020f040509060d0f061508011103010e1b07060b01 74
    0x216001446941d245003240898251182d20000303010212900e00342c038040c540c0700b0001c0c803000d810002005036108400c0204820760f40e07180410701c04051820006002e2103016110300200500407241078821041c44184440c206080c48401c000ca0310001030108201c0f401480e0540481e0300040c0414050720b080e850182c204500442031206102c021001001e00c2c110496081030451080e00c0a4002d03102c0004505010840703d40c0066844411a001000c81d010001d0054002114400c14a00c0301d00c4151001e034001f9001090b81544903416109021003000c98018080100130159210b50862000500e0385000d0724002c000f203081098200141d90351240c0c00b400945d00d41c3c0c6800003006464101e44280c42c0700b4210100840c00e1420020488080e050700080c007960011000c1d02d452001e0038903005241d20504002d40001400c0c01c00b881034035800b4480c102074036503035454800b04011104001d801315048460031244060101000c600b1507a11640c0114007180303100d01800107071074030311042641c1c0c0f2a60 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 704755008 1250 704753758 704753807
    0x70e04050901150b13050a060f1202120412022406060c010209130e070e010b070f03180308040810060609060809070b0d02190201020a0507060b060d09030207061b0209010b0a 76
    0x3401c14020f8000f045d44e03034145000e001e94400c100f020b184941d10400380400e8842d4503034102c05118402018200030b41e5540503140044004401c07a003282e0841d82039842400042703038004044d50503c48110082c1121021400103120b8130b01d540c00b0b51b40040d004501c2031400181601c2d180301c082d01654070302c01e8020106115100d41c004050080d120410315240e81e07000743c110100c1c040702004031260580c0d019401c1c083c20040c4c0c0c0d60310f40012a140301815020300c23000008000c00321807031320001c5c0003440c810a6181d86561400340800d01c0d060b02c400101c1c031820b080003420f0009590000d81d03901160f0040c40d2a40542c0c980e0700485052038000d8005480d40b4100161907044140745400600d8510000c0103246181c885480d002c0b0300302c0c0142c084c8240010f00411031103000c510290081104200300a01c0a440c0c030041034030703150484015550840140c0c1051707030300f04409900440400030081c0b040c1442030078540e10380e00180e9460414028504020b501190030380341d01740708985c920740e0f0704411101d01004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 704756258 1250 704755008 704755019
    0xc03191a0f040c0e100902130f0902070c0906050102031903020903030d020901020c0d08090607050c040c0221190302030a1e1a01050f0406051e0304060b09070206070e0405090115 78
    0x3040700444041d1602c050b656000a040d00c08080788a00c11800318100500c0b5a01742203081c8003070b42c0318401d50569070240314004140743c0d40e9021080c2c0102000280140c2d924407919044803400e445a06c211062880c0100803c11139030044100e507071940103201d040c031418882180540c020b005054060380c141c440810031044206040c1e009006c0705000b42c00b2074141420607410400c0d0601040340c0104421400d0000341030b40d0400d40b02604440d8441c03800e4400072101200814101d58100091500580c00998040b0b240d40d4040c05465600005007802460444146540080325511240c003070704141d030000000350241c00c0d562000014107810484080c016808544640140c2070042d251142c40b06051600c510540c003070307011224190440c0207800d00f0309142041c2a0b8090300655610200c01c0880c00800c074a0500da540210301c00c900c01c90b400141401c101080c0001690028001d40541d03014070280220b80b600000300d2000003804440110b101d5450f023600502404007a001080d40c51071813100400e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 704757508 1250 704756258 704756281
    0x60a05210c0324010c03051308060a06090b100206040206070c08031c152706030807300804022806080a1a2803080307050307110c03191a 60
    0x41080507840c40c000b030100b0000781c64007000d90f0a901e020400c003041d0580002c0c0580040d000b0303410003020007508281e4070710b80c19080c43d01c1110403440481d0340d0001444a0b4550303105484001c041a038203d148400390b414042e564640191001c2d12650b0049503200411a00c10038103005001224144d035191540c40032f040f50070f44485844101c1c00f40c00c005082a003006903800e45012150403815001c107070220781030f614084d08159490718162585410001c07005c200900024240244a80d203d034a152210460b01489030100b60402604e854010041420856000c0f101540180c1c04440c1040344038008070317102900910301c404031680580b2000e4000303038098015107080d00c1103018090501c5007042040306000f640d100029407550040c4030f80024840100f6244107201c005811592410000e501e940300c0ea1016013040b15200002200081000380c01d9500203034031501050000020417070381c00300c200081e4840002c01400d03194960031681c04014425619a500f003445d401c02428255030a024410b0785 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 704758758 1250 704757508 704757511
    0x70c0c031a0603060f1005040905031216091401170603011b03060302090c0f04170708030d020d0b01090f0504240603061a03041106180a0609140f060a05210c03 70
    0x40c840d01580c0300085d003202265110511801c104503032021103d0405040000070300142c041500e05200500001d4215100080300d50b00544128403610300c5403001603802804c590454200003520300341420041e48598000c2d0709a174880d81c50504e010340e00e90b282e1020038014242d81080d000d890815001d00c43c41540c0590007482603e0081d40c0da02c805a40d00031320400740e442012114204400c040004000500301402030300d500700c400340d0580d0800b82c0d88070b02c2c0c9031550304500d02d10202c01da40002c1c090051607040c070404110750b0307082c20020040780c0781440045403440248501030113aa1200030094000b0503007100712210130a0fa400f8601b5240e120103005000700b2903406130f5514626440c0d0701050a07903460301a02c0c40703158022400241d601c0d0002c1848040d8000162101102c81824180d880b15510581d10b14040e1043d5907400604528009004000742d0841144500450101058040e02c5d2695812908203981504000343e07200c05c428501e024544100c1200c0008a04c481c00b40080c1502c4d160055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 704760008 1250 704758758 704758771
    0x1209140105360606240301030b0f0a0c0f050a09051f030506011b0215070501020d0b030601050a080c0922050a1101030b0108072019060e0a03020303070c0c031a 70
    0x10144108044181e12201003994103802c103075100400280d400e261015950140c5a1160043c1d2621920210303042040c0e0402e0b04202c030318140742d50401811400c0200c0b22540106035030720611034003030364031800750003400d40c00290750401c0710000351003024500403040c02000b03203400791000454003100217904607039a61546040c00001c0c10540401c907550300c0740121051190003a0204440e0310f034250700b00000c0c140c03c2035212440c0c54003403200b0b0700403c0083c8060b10817064660b1012400c140b10004140c1007003816000584100c1100c1401e200e4001f0000b08503441c41c0701a9201042078542c040407007a40910300c00c1300d900c80c240a0b500c4004102000c103040700c01c103100e0400c0d5038050440c2001034040c1d0f185a40d0f007500041540c400aa84c1d548604498122010100c4145029001c120f820304e0a1901c2c2400c1200c00040c000a00420040c031403060100b01071121010b04505040c0d80d500030f40702d1002400d030300b0401ca582c81e000810b01c0001c6080600a541c886400810350042c40b240440c403803c122040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 704761258 1250 704760008 704760061
    0xc0b0c010204080c180a150e1303110601080709050903090a06091e030b0c0a030912030b01021501062705031906050604090203030301091e09140706030c1209140105 72
    0x21340b480b9041c25045000e601418105424095540040078002480119074031446005112400500200134017040c030700950746084250840200750070050071500d074150258207507520807001040341100c0400d00409580507818049081e854041c54180b841c01280c600381d0707110050700000a40e1a0b0040802e00458810803501010000c880e40b074401c80c0b420a100c040c08103c862400904080141e400134040741e4507c0c140020303460160b459012420345200f03400f0000c00e9070750041d03092640c0c040060051440841a520784c4540c189a402450307111300c0320072074440140b90314403600100554140b02004c0c21021b000c4400302000c9030755410103240740c8c1606803032413031404011403024106030194084660b00500114550392909100100400448000115580a9084010310f079004e90040110a0b405174440844481d181642c413800d12000c1ea1000081c903240c092100101074105c5608001d42e00b20840c0090203010504080302c01d00b6201c0000c0e0403551804007000784000d20700201c040580564080d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 704762508 1250 704761258 704761273
    0x1a0a0e18010c020c01030b013b03011b0e03031c020904050106050a141803010609050f240105070807050d03063f051504050c10080c07020d0c0b0c01020408 68
    0xa0441c2200c0029001c5001a00080c0600c18554020780040701d58504c1803600c42d0b4070701020442244d001c2c50380c00c0394600825080c0001900d840705c40c01d0034210004114001c0200100b54030340245150128030081d0f052290300002d0000307569040c41500d01000c0c600617a4a004420001c1c580000c1d8401d52006120b58034140011074120303c6401526001c81c0203480e060000100407030300e5011a0010b800b044601002d40e107030300e440ea850070300411008080d40c800c00b08450400042030920b0007001007614036060400c00c04c100001c0d510000b01c001c281c500f030802c01c0e610805070804102c00d115590016140748a0200070007038036a45644290111120074098450b04002210039101414401b02940751801c810007a0f0041c85850200b880003c610510466070000c0024034420441c2c0000c0768103451383e812001c401446070a140e0306482c01a00b052919100e0b03032500f2902c90740140500d070b1020340540e0005400801300702da91072488001c1c1541d031041a40340d15640007841d020307500500408401340a00c0f00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 704763758 1250 704762508 704762551
    0x20102070f03080d050a0e0d080f0105041b1101090821060303041811090306090a1e0b150f120a03121b1d150c01140603060a1a0a0e 58
    0x41c40d800a40e584000342501e072499100282c2e0203410f018080d4400c0654445040300030304420400381b00303070100303035240e601c25464821002c0142c4001640710030b01807424070038107040303038440d50f89a107030030408504040101240c0407890314010032203803400a011110000740e0001c00800020a00506030a11000b940d503680c1d4034003410340b2402240b1442000850700384400c2c01e03420f0f0a030070800c500060340e1022401d00041c440080d00c0c0032429110317840a034003c0c03001a420300c80840d90368004000307640c44e4500010b24170303a141c0e03420760383c010480c4001c1904040c0c01e40044e600d0b0000740c10440c8000b40389005141c0c180800688030050010b00f1000729844100318896401c45006684074022200700c1c0901c00c00101d0f0b016203610040440741500d01c5800195681103641d6842040d10b0b0004800ca00c603183e0b40c11400f45d5086a800c0305190f425501e40c1800c1042907034002503450307400240300700d01081d410482024920032101141039a507114a1030030002c149003003d03014051098086140188002c0d8601c1d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 704765008 1250 704763758 704763779
    0x3c02030606040c050d1e1b020706020a03080415140c0912070e01171005010f05040b040b030a0201030f0204232701030305030414030703210204060c0f080c030c0303010302010207 78
    0x81c1c0f081d008580184114131810f9401c1d40100d1240c0e540c843c401c17030101010b011800883c0c200d4102044c200040020a05034150304222000190000380000c00360b901c0d540d03c000c0c0143d90700400003462900040b410700d198403c1a000005a00f00c5484d45461a003428000142c0c3c9400c0340301c0c840d00941d924000c41c901c810002801c001180d42a4410343c42c03603400c094000880018620302c0314038500c650908100c01d54041d129003402002d0030204030800a0521040001761440c4a038203512450500554000a03500030490800c03055090900003820481401014041e015a0f48042c950f030301c8102410003c0303c1c00710181d050b4800301b01c0d844045002000c400c488824001020340381c201245c2001400020b00a0000315005170060284001c0c0c4031003d8171852175030380036041c11400540139100c2000c10b60050040030760155400141907052905002d0014820401540c0c060074850b80c42000307009000c80d140403540c2c0840820107aa94411982242aa8a41c402c0c84101c4c0103124441001801030910f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 704766258 1250 704765008 704765021
    0x90c05010311120118110c010b030709050903180f060a0804060b0a0b0a0804030519050c01050108030c12160b0f0405120f1b070b1603020105060d050a3c0203060604 72
    0x205003800050340d09002d500c81d640c0855400e25240282e40300c9001b81e1050fa0000a000c1d64881c5200209002c008403044c14104407459000c00d8415062001b48080f0010200a4400482002101d0741c00032003401c00207522070035142d516540204000a03501141c0d50b018003513031f1045004910500560380c0420038495003d0f8244180e02c201c90081c0034080110b403080618035080b5000703150260520310b402c5540242c84414400101c049280020b80b801c501c2000c2c0038183c01007071040051420030152008007a100c151040c524401160001110300d440d42040c0000c0601c0b9400c1403260500d86400713960f610454200392810354403446082490100103903003500325906502252501c0c0e00382600e40c0101040c40b40403540c504034902415501185004c0090050318440891501e409a04c410710300700a07007101c101405650040c204182d81c030022030f1000468414450740700c101c041c095068100d9002145409459484582100210100d250034159400240880c02101507a4032519041c0401003221032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 704767508 1250 704766258 704766277
    0x90c09010803040308091e04050c07020f010f14070614150a170d031d010e030d060f0f0314031207090e01050402071a06060d1104030b010e1308031504090c05010311 72
    0x1402c06c242e41107410140c01c1c01401d12134049204403213903000000141980c60488801164850108040c4254034140002d4285e030142800d0600c00d4980c094402848214a44841601e003000000e6507010001154480440e61400510030505410704003000c03501e40c1d0100c90103a210309450640855075810101034620510080c00080c10b0150030420700342e014100e074210701c445d84103148444400025082c081c00000ca072518025550314002c00900d44100c030995040210340a02d230318401d1011074403d4a03030b0402d1301d8101d6086076007000c2602c480d0b40755200d2113464030180c04c264414860b031a5040318041060b03c240702c50801031130380c07910140003c80c001d02c01d000c2d1040030710000000d08000544400da420ad00d001c2c003007900d498402203500d8180d5035480b03100102c0c2c020000e03041050201b40d0401a0141841c10031405041c2010301e000250100044400341c024a00000072a41c06083d010002030b0941024105108004140c24a40d100c003005122301030100742043c5010450031303071030f030300301c804001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 704768758 1250 704767508 704767523
    0xc050616080705010507202503060c0c29042d050c03071401050d0b2403040b09120f031012140d11150402031e060a0e0d0503060d0f0b090c090108030403 67
    0x100540600c40c440214234000d120000c83c0b481c004008680b55014414904801c1d84546401c89068079254900660022615203c0701561152108114403c203505400680140c00040c0310716506021120b12003080070703021039004044401100700040400c560404680c1202954465940d0742d80c40c0c0450222400c400c0d000807070401424900b02195030105444d000c0140101c962587e000c1c0c03c00b4140b0740e006036030409140b4044204001c12018039407043d449102c1c0d6001e0900300300d88002c4101340c0d000c0c1e03081554100ad40030000410569003a02050000c2418601c1d140403241c1505140c49001c13031710000c2c68420302170850207400c114011651030345a0a0311320300916208882c0a04c00c049140c000d00100e0b414041c4000040f60402c4100e81c14031100000b10181907075050260180c4100c55408808c25200e41107003906031003050b0810141e0764400c805582c401c43d40141d601e0b180c06c8680144400030726a0307000400b44840000000340b001c02040056540c044140d0f25103000c00d6503405244001801070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 704770008 1250 704768758 704768773
    0xb0709120201050c0a051b040e0d050307140702220c1409041a030d03020a1205060f0618101806080103050d0e0d05150a05130c05061608070501050720 66
    0x55228100903c101681c1300d0554001a0055451500f41a104081034841250403164240039203010300c28482003075140d4000f8005904c00c041c020f0254040204036105001003e00c1401d0b40900e4841190b0303019a0080616507010006018244240c06180c142c00c041440d0042000b90302c2c3c0100d48442540007042001410051401c04220141c040c1d1211a1b180100282c0e001605803402c000d40030425226840168841082d0140144507034541465107000d00c1c1072909111035610303040030304281c0c0141510b50560b1202d500e4a00b010540154030184d4004610000b11943e25604c18514070607080715038a8040082d6440030304850610303080c00007520076000050a6041e15002e8150f151400701f000d0302030505401c0325212681440d074070700c101120050344141004241c51851180c00e0b071066a940d01d9908071b01c015210310641c0c605600480c2d00034600004d90001d100e00302d0841031851580300d140555a40c11038900030307020f4003080d128000400e548100e00c0102c0496040c80b007199546172001403504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 704771258 1250 704770008 704770013
    0x21090f0609040e07081005071404051e0303071b05060703140d060b0f040810180b09030418061818031d06030f070f020d09120c0b03040308040b070912 66
    0xa51005401d01c1d802a600e2040714042c8405000c59001000f00d8005044080f0705000150f0994500510410800c00105051070341e145800e015203003600d4007650054080c600c00d002c80d0035032584030030300d4a50510020942004001d19071981280140d01101085d0480e40e460060084078043c80d80004c0205d0030309514104806212005000c1000b0401d001043c21940c3c7c10301e0b28001e50144140101841c000141801022410803022540c0c002d144000c001903400080d0008040308102c200034480c3c2c0341e000214407411810401d4902410010302e21101110312030511030014819407080345036440f012500ca03a10603a59110340a980b01040c4100c49604800313603011071320f2414441e10380c808800d11905122080e20303184c015600c242d040c8018010141070044002d030070f8410202035581154002c411201d042a4055440d02c21101d1400d46141ea803041440e0000d10000c554100070b102d401c0200400043c10350220341980500c1c01404881e00e5625026012503009419008403040d40d62402c214100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 704772508 1250 704771258 704771269
    0x828021c0504140a0b0f0307090e0708060d1406072c01090317160c080f07081b0d061503230c1c0c1e060503010312050a1701030521090f 60
    0x200b44400030300f989100c80c0c81d03185c802e0213900000350701210810302008016902d90028922400341000060020081c81d1211008000c40f40041401e402403031048012400c1098074000708910410300e406a906a00d0010130040c00695170800719001c1c031903069081001d070741c4491020720000d03c0686d2150089070039510b03003400d2840c02c07a40608003240c0130050006100191507400351050320462000003140d01c3c14081d18945007038141e8040060300580c1003007210403000030300302c1d454200c40100341a000b201140054a1064014406008503082040000c8503290103c900e10650f44590403c9003d41a00490b441c4422000f070381c6125144c1c020702c054015481c110a4a0848000403e0084491004c503601c00c41303020410b9010901000c100d09040036502c55180c0148050101450402d04662442d00e40046c070702d03042d2012409200000a02c9001c07107214074000380e081c103e00e4a1520b4656943d01d0116510410001c0500302c3c080600c80e8021042d8000742241c0a03800f0080000341c400c00141d00300324 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 704773758 1250 704772508 704772539
    0x60a030f0201021002131a1218010902031f0e0304150c022101050118020c03070f140304170106060e0f28030308090f07030c030b040828021c0504 64
    0x2d06512402c0020000402c00d0300081c0800da05400b0b560a01078039110709020303510601d0b81d06407510102485554140f071044c0202e607a0004907c2d1104900000e2001041e00401003580042d405000340d420444910281c1407a0000c0e0696959041001e1214207403403a48900480c01003845412000c1000d03254240304040c0c080c45031b400100a8203e00c1191102ca80f002c42c400184848240d4440004001c0d0051108001c82c60b00f0540106510b4100002e04040d10f13413040c000018601d6a41150400602c40c0801c03414071114034400480e9030f1681c0b2100020b8055160400d001e400d507003400004900940304000341010380b48054000031455403203d00300310003081c59400d400e44900030820740c0e2603505009202c1d0402903003c2d031982c240301c0c180000568100503140b0090303940765204190400016182808003801c03070750410181e4489072a1480d21096921600b5060341c08010090880c11184650f4034100140d510f841d001c80b00c14409610140081c6210b4103280c07800b141040c00100803840c001403000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 704775008 1250 704773758 704773763
    0x7031409040207031808190b090a080a12060f050901150309061104050126070f03090218011e0b090111030904060306091e020a180207121e08060a030f 66
    0x450a10a050010400300d80080c40103600050911806844170341000c00a00c0281c1441005480d03c800c0810b0703030085038241034070001c000641c2040080d950705806e0145480f4964095881c5030364601d2090000c2c10040340c4117090f80c119103059030010300340b10403028030001c070341003c0c2140c3c880d41c0c030f00154443d5008407800d00078181905c9403080000544e4501c180c15a202103040138030b4480781080001050325000a0707260510100c0303846800040720340c0d06109603010030a840d25400c0f8404000c2c045016015002c0d00941044052011a4507180013001846c103130b403519038000403180c02102c1d622103050100d20502d55500c0d0104050121940b0407480f9030101d0103a5012689042003032070103d811124a40d1003656141c4d5183c8074202001294507002e1140c01c0140300300c0c5001c64050b0006042c5240c0e900c102000c00309900c95441c0002515010744a0301034001c141910041282c072070180407861482102c0042c80200282d0703481075809103101c2405090042c1a0000060440d03803070814402241006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 704776258 1250 704775008 704775047
    0x70b04020a3212070f0f0506090f0f0a0308070602040e0906040b010608130215040509090d120f0902090901090302010b03010c140c010603050d110d080c09040b12030a0512060103050405030703 84
    0x3070000d803040400200780140105d680f0032603500c3c42e103c1c540c08007885980055110355001c10012080366251261401503101c1180c010200f9141100011207986a60b03100a020a90125181d400d210b110fa01500441c3c03040c403000c09065440d440b045071200001c4030001c0a00307404030014841d0350b05c0780f56405e90202010303c04200404998001541500d0b02c410b824845038000101840703d424160a00c503000000341009007502a150036000c0d0a0480044610482507500ca14600f01c034801b0b900801030b01900501800054105454103e001e031242c4201503025609058840e499414144074a40040e49140d540711b0043e1000081c090342c1d42e1104041024541d2540008404a070b42409000003107103803510382030b440c0c040c50400b0328141251220b0301e03428003020404000c0e26030000d5007290343d442000c540000f40c1040010004203544000b0851111a00c4041130315200250040b0080c8070030000c00f082001c0035522040114152501110024441d0300140b0548000034020303107418401c404072030310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 704777508 1250 704776258 704776279
    0x7050f031503030d24060f1706040b18090d0918050402060c03042715090e2514120a020108070c050a0308010608070e01020d140f070b04020a32 63
    0x280d030050384c1d22142d4220700300c05d0903800081949445104c900003080b45080003c50458080c0c0081c04400c600d84041008900d02000103070b1581c0c1e42e0380002941d00005129000030440c0c4108da2b440e84104603201400d520402c4101c00e1040e002e56000c808075460f50303c40450240d0a22181740c00741001070004c03600a2414000340010100500203800900000c02c01c040b100c40500a00c640100f00d0b0b04c8810394200d280009110008031118165001d840c1c00d51000708801c00d943c1c07006490400040c0c080c1c0042080034495841c560152402d06c011644000b0701a40031341140d904006038401080c0440e80c00d81d10994070440107500440700c103a41301580d030504903840b0480b52141030500c00390b820700314000358010b0700500000f500070814a402c07601610f04030003407121580001c0d650b02c1c0e20703403201818825000398040500c49482c04032070000a01ca2004c507100e1409160012606105a40c1240304d800b07a10004139441105403c20036501003030390170b0f40c4a2101c01c0740e401d40140e282c1005168000340181c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 704778758 1250 704777508 704777527
    0xb0c04061701032a12050c0315220f060e07090e01060e06010f0c170a11061005150c19060b03030f04270905251a180a080109030807050f03150303 64
    0x1a0342c81700d640180054042008003508141c10030108085d0f070a0800804401e01c409101018041d0b11f8018150510b4240c8610900b00780c1c09020500b10000c2900b030030700faa40b0030408000b1546008895030071300103009141403141e14074280c0d01a030042c00c110f00b1004d000a00591b120b0811556680001d041c0f44000d4401d5403a00e20101c1c100c141072060f45080000d1708039003694850040401d000014000d072502c2d0a04496007003040c0c84600c07586110390349000691501c14403010844244a40f02d408407040b82071094000c0380c2a410341d40e42079544628000d05d11006043c040112004d40c2c042216151909003408110740c801c81d1116003080299811010609030203806104034000700780141c004000c1e0100c1c181c0c203884800b2002c850b410403031504500400c0300460000b05010340c20b606a07046911400b0507039100c142c62410020842e482425000000b030401c0c010340c081518640250744104007640d0340344040d036481c800d411903990340e030710104001340360941e010704480500e02c00102924508a01c00d13 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 704780008 1250 704778758 704778779
    0xb0103060b0a0302040510080906040609050f030c0105040c121203020315040f020304060f020a090b0c2401080d030605060403150b1e1e060702120a0b0c04061701032a 73
    0x6154503010031340c0000d080c082e910744007200c04007118980c5030181041c5002071107651140f8028000400c2c46840340c0b540000c100c409c0c403011100949100441351500d11a05c802da01030702c41581d0070341d07040342c800c80041010001206170040d990b40084550380780694101d000c034000d500090251000d6841004a80a00e6440d4041d10f007224150410258990501c1d0508904030380544114803d86441000b1100b07816410823195801c841102055585942500ca025030801c522691044120fa0360303215001401c4900240c510705a03084c01044548141d4403031010340488100b0b018542c2c0c40101030202700002980280320008014166401042180c81640440c9100c035445075801c00a48180954500d5400c006202c08a40c890301501c01041c41c200714041580707840741148c060300034402c101c800180c0c0c7e1000c10400000c2544100b2081c054640505c1a82d40303600306000e4500000d00111002ca112800040f6560680350001c00c0754074849136134480d80c402984a1600c000d41922050400940207240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 704781258 1250 704780008 704780017
    0x40b0912031905160905060f0706050c1b010b1804140f0106140105040f0e09071211011d010f08280b011e05040b0d0b06070f0302120705100b0103060b 66
    0x9299a40c03961000c0c400300107080d02d50003007113460040c40c110501300d01340303030b20404440072941c060301d80b2643c82c1d811240015151140d007102502c02c0703003020284018a6002d500800c0116581403850442c110410b01003403c0e219003150403a400b842c0100c45050f000408420540c1141c0314403200481d80341d00c00141414541a200824110b035581d4904001c501d801030a480c0008a00340382c074a00d080d003040440b440e800d81d2340c00f403030ac016500400083d40300c5c14100000340180c185450f01e4081c4001c6031802e41d41c40000d051609000804038890890050300c480d9400f8040c59050711008001800c0000c1104c803140c0080c489884440032501006140d009201c80103064110941c020642c02d14502c00036102204032620f419840000304400d48101d0303804000d640945951104150740c4039904030010025108003000340740e20240c009032440c1042407540362079061030311039003c0c0c8070f221200380142c00403805603002c05041d80c0c214140c003480c07a100950000c41200f0301418001103c039140c0140f012260030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 704782508 1250 704781258 704781271
    0xc010c1d041e0c03051f0b2719030657020f060c0a021c02161403010b03031c0906060b040f06030e071805090a1403071712040b091203 59
    0x50380c0f010700c00020790049680080b403806650011b0380c01e03d06440d24100e8800c1c0c0350007120400c0d4140070b0000224201e8000d113044e01005101004041011560030b0311142c86d480308440c910b10f04002c000705003074140008074501d8400003100a04c001002880c0c00e508856110380070014805c8408a0a170000c0e0107482d40d80c2031060f9000b40020504920400d1501c03170054105010400c091240002d0756500046650056154640c8201c0d481e14010059251042000350405100c3c032491001c282201c400f0004602d4207001c4000b40b01c0381c1d11100615032070344145120f890000910007845048a41690015540310b0310a907800200a41e9400b038103840da800c46d401c1040c02e112080010440c4e164180626004c3c19a82c10251450341d1410001460708106d84500c0b40c070b010b0300c1e03800003145800c081c0034481c3d0707954109108001c007802080380f19440350701108c0c044481c2e030702050320040e082d21044180da211400c00340380c1084d0b0b92034076250003a2000005010301582c0c41540c21101201800d400954050b25 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 704783758 1250 704782508 704782511
    0x809210f0c060901181a09030105090102091005070503040e0705030a0c0e010e0d0503070203100903090e060f04110c1209030f19061e29060a020601090e0102040f0b0c010c1d041e0c03 80
    0x1c1e47d08042c00d40b40d02404c0150540e00600040742c5d9540c6900d01c4a078560350078104250741d9000b514041d821406240e021068400502080040d010b420400035807003910f403580104207403040c2600540d00006070005050000d442c000d01d0003417500340316903846402406481220b08040481d030009140030042e00c0301d66a016250203480b801c040d0080d4011005d4003015000c2001c0740380182c0895140108100c0c003501c1240c4130141d15842d903500d48101c0d20030b81d403420140e5009800d015512202a0302441c6010b009115000050014160100301030000c07109201c00c0e100c04006a0300ea4401130100c3c0181c1d042d038038a00c0e45c451161aa03091049200c901c516400c0085881d070b130b1042500000c18959500c1d4041c040411102d0540355020404606444131001c0000305200f1b1410880d009009540014602e4298103001013002e030f4180c0d000d8030807018094001e1000d10358143e021107c100707a40c4c90803000c010314031070030f441e8a142541254180d120380040400807200d5076010081914007481c20540444e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 704785008 1250 704783758 704783767
    0x15050c1c0908060c090414070806090c04080f0d110115090b040b030d03140708060306180c03030c0609010e0304120f0302030d09060903090504270809210f0c060901181a 74
    0x3810240546a0400b141581d100b0b00c48c03500303800161110400802e001e214140c4500060070741c00e00441030324044c04c100400c503209000a50003199450000e401c02c7c0c808604101c51101c1d81c3d00c01402110181d0114024800d040c40c58141502c0160035004102c950150721110404201c0e10100105502204d03542c3c2c02151083c1d4964091400806c007034150810000c044082056135200001c11f07a0b041400c083d03900d00722045801c905814244110b0201d541400001280d240310000020800d010b003c51000800c0300400b46080c0981da0300c16445544002d040f03014211000c1920070450a040c14040c0c0107807468641c2c500c210400320761004a08450031507448040bc0c1c181540056001b01504050350104064460000140e035800c4038800043e5000d0103002050341004040c0e0251601000050118140e04403802601d18032255410a00038480c0304803410950711a01c0002d0090150340e0181940c1d00c1c11003800e004441c1844180e0301e90050b1101d4040020ba12a040c0d0140e1000c611200e0b280c0d9242e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 704786258 1250 704785008 704785027
    0x307090e06041401020a0c08090d050304090207020906040504170c0f010606120c0c02090105130e0303072d1409030c0307060302031006050315091801090c15050c1c0908060c 76
    0x203010050f0303070480941e1043c01700e02420380e049411203900c04d4001814549841e0403200255070f014010300300070210300000c40d00041003602900603041c80b52007140d0001c0701d66107110a010407980e0445e030140c02d0078000109031101002800080144c40554002e42d0601e407182150716095030707059800071000070040000c0481d0090b80348100c2160109a180940172501c442e000103840720701c11300441c0d1050f6a120b00881003020258803030841007440e00c040c0ca45a25002e032002c5c1050b51443c9441000c400f15038030441031364903d0f00711005100c1003502c3d5070341c171070900444040c07594001780011501449110076115850f5010400c100003001d00d95005640ca14214204120740101c6510480601506005000e00c40d5800030000035100301c1944c1c1680c1c05ea17148845c4001520341500600ea455107009500414820f041c0b0402c015075441c208803a841e860340c00d4088526109a10b00c03041c440e01f000701c582d00e03a15547c050340c2051031900c2c5490240a9210f5072103e092407000c0e11200b4400e000000d81d41c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 704787508 1250 704786258 704786273
    0x9011d09070f111f0c170a02090d0215031005060a0f03150e04260913090609020d0606061d0f010804141002030f07141801090315051905011202010507020307090e0604 73
    0x20a600ca030b2618035140309010b20b4514001c03801030200b4051fa90013042c84d072050b4407103c401484240d0014810314a4084000e400719440e0300030307503411440042810300401d15086c6030086840039103841d0340c0d10b40d2050401004400504008800000e000004c1c0400504e109003200e00e98004e90043e840c2d044a04003501c0c4c4200309443c0000025820f01041c405580c50b5564100c9517180d00304000004145142913240900003054840d0b0300079404440c268013482404510b83c4010240c512a85686648242e10495070040845207902e4582c02041110340c0003485d40f003a100c5a80091044400101d0301c004d10409504018828102c10f80e4984c0c080b080080300c460b1541d519030030804a041c241c101454100111300d640c8501904000c08840131070742c0d01250307403043e4a030400440e00f020b03404503441c0b10f10403407030003521040d50040c40c11004900c2c0803294001e60302c1a40c0c100c40c0e00001c02210100740380c3c0195060b4000c905c06aa050250304c1000403402c400340039180c4040c20b040701078211072916103404e00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 704788758 1250 704787508 704787521
    0x2030408070218060f120c011805030105040f05060f042001090302120c01081305030406050c0c03010c0c030807110304060f03020705100606120218012a050309011d09070f111f 77
    0x1b0b1151403d94002c180002c008203e400c4c1842c1c0030b18100c0c1100c10300d203002a20210309a4416a0036600e860104403c5c020040740d6403095501c02c1c002c0e036074140ca07030042c021341c603441c10f42e0007174011200703080c400744540c2c11808502e03480c83d01070404000c0c0c645da13034001070160606402000d200d034002d0842503d0945c0d10000c1a40e00a00420360310084541649415507240600c0c0142d405010b00090038000050007004441505000103000b40301c050001f5100410791031040c24120041686a00030400080c060024070b003407034030004021820b041c0b52100803074500002845100c00c2c55401c105280c0414018002c10150746601003010548514003240280500051042d212800307106020300d1844c1138019841c10307000d2509103414510784d06210401e85000081c020340304082078101b00e49170f08102002c406400c10807801d8861a41342983d541005050f140040c0e001e0f42e00c19840300000340c50700d000e60020840c001151800769a40201c0d170700001d00d80f014180300b28411444569510700c2601441c006c51 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 704790008 1250 704788758 704788789
    0x30b030f070305120c0a080316080c09030a0615030b040b090706020d0c110a12060f2304060522080409053102042705070501080c030a0203040807021806 67
    0x207011451460702c81980b113540182c00c0c80c072540400a08900580d00401803e19450b4001150130b540c0d013001c031180e65007141c600782600086451140082c4004010038107840100c580a0301038a4480c1d590360364403000b000c044020701500c3c0c0c101c40000c0041250a5030091280c0c2c81a00941018140704040b1440c00341560700000c2190301c100d440341141540025051072140c0d1003002c5905405042c0002018640c0701d070005070000080d610440140040bc0d0040307414003044610400c007000b0510040342d641807030400c1480201900201050018800b503014039840ba20b41c0422400d031421030510121000d540550640f50380070003003028450300042e841b6150b0002030007102003880007181c4031391800e51181541c0c001c1d124008000c43d0025501e5503040071800c42e00501a1143c1c580c0d0b800b80c85207180780010001d440c18400d0f5513010a155020300c440c05d010790054496142982d5400d0031100213540010b20464210b10140080c80041c0c0b20342055101107a11921808894039241041c40070000440138103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 704791258 1250 704790008 704790013
    0x1020f040815060d0609111e1008072109020a030b010306060b090a0909110901060f0e030307051903020c1e04150e1b370801081e1c030b030f 62
    0x20300000c1e68130324000e0300d02aa800300300861502d9240c18064000783c514035a440e000141e460414040140070202204140821100c51301c0c0034080b020f0495045104071990004124400300c801085400b0291104002c41c0350f810216150b900c5502240019009520803510780b142900107004001d054005c4501428080c440c1d14180700c806400250041801c0c86098003042d03075070400c4000d000b1508a1080700c03c002410620065940d180000c1000c590f00a2140c0010440604c203015403070080300b11214990000010a900c040c4440d2022580583c404128258800c01e028192552034900e60a05c01c01c06458040049004860034041640c4980301043c4000c00041418000c0038030440416421400360b4140d07165207882d10504001c1403081c8081c0010700301c3d810321803403544a00440a07407001c01075101c5070241c2d8016102c040d550b0510070b002e13403d000e802c82d039034002c04c0d1002001c05400850744c14080b038000355201491080c08541840081001980f502041002410200003100502604400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 704792508 1250 704791258 704791261
    0x120403020706080702120f130308091e060405011404150504050a0b091305060d1721150d02150309010501241b0c0302101106070804020918010e01020f040815 69
    0x2c0082d20b590694205812a000c081a510486d2400c401078805c40d26415840354448c41d02c81c00e20380c4042d0812400d451091107007031016412080400c00d03110034014041e000c141003d0602e4010346018603d00f280d540701e1030042c00002008051f0030080074915606489540e6554241030078051011510782018010b10f404002a0500d9192aa10f1034520703080d01c82c00050549880e40010040b0600e4007002d07011003014805850020b500304001c000f410000700090344050f0403401c00d1400c402003206d000324101840c14101c030701800d20041e8007050510042220b40152201e000102c1c132504142d600203607903035558005018102018601109284024600840000d5114001040740303d114000076200203a1088000400040c1c90b0844051580100140c0012a0f801002008402c990045821500c103140c00f150015006407000c5020380c0c1c000e4800360f501d6072680041030800481d009500b03410341d0307500d540b0f404a8000f88003501c00c0c03104074681d0b265250f140c00f0096241c90260f954101c00103072441c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 704793758 1250 704792508 704792521
    0x60b011403070815011e08090c240d0906020a02010c0f03060803180a1508041a010e0403050703170903120a02030c1b12070b1f061d030f0312040302070608 68
    0x4100590203461684a01d000300d42d603400498940d0140d0b9990b990100b0044007410546e90082c480c40d100c3c100340012207103c802d440003040742c2c601c50404140c000c0c41000002d481c1d40384941c0018080000750744408550281d00c3e81d81c0c0c104a034401d0081000603590783d00140c05503644056090030840385441c062207441d0409400d6500d134410087c14000c048001d107200358064a032a80326000820258003022114980c592018000103030803142140c5511410202d070240d01c071030441d0345060b1582d00304601c80642d9039a6056800d03520400d0160140072a100e40c0d004484be001600070b103ea00044041c6442c3e841c2b60b4a0030000541c0504aa50484d0050080100c429248000c0e1740a4441100721100344106c2c07241d0160400090070340c54405600002504810f000304483c40318007a002806030711202407140700c55105000d10794003409001440c040c2c0d80b6240d81e202e0340c035000e0311540020b090b10400218000180e240d0382c440414010602200c000b084181a010700c0600000d02c458105a1150314145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 704795008 1250 704793758 704793767
    0x2030d020c06031810330602031207051c0b010215090d0f090320010905030d0e3a0209060901030c06052511031b06190309020d060b01140307 62
    0x100a01c19010072510b000589101c20040380c211050002400c000b40c0141b040c501c40c00b0030341c0c2241e44280010101000d41b855401d04401030440d051039000d14180041c038012220710480c0a003d03442000407e1140010108002c0d81c44214001103803800660110703a40006401c0492084608420804e03190070012040000b00e1900840c001038503110140c003207400e10540d402e116031741000c1c0c48449900322030300340d000a0f002c1191216800341c0350003003600c1c0c0c2c03207080603516102000c081c400a42c5003480a0300c141061040950b0708182120751400421001f002c0419a01910301c0c3c413604114880490760960401c8100e241d04810150780c0314007658150344030030700c0c1308495204200410a0018225880b141c403c0e41c001d2040e406003400b110f41408900301030300c480360111580e62107801441c00c52151029014490000c818018005a04080751517040c503101d1890074400e401455140c290880041c1e944c00c907901ea4151080e13800140c00c1910100050122541d051030003011003040040c040c0e803a410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 704796258 1250 704795008 704795011
    0x305010f050f240d1a01080609070b2b1b08010f1a040b030408040f181109011b050c0301090803160801050607080a0e06030c180d08091203121302030d020c0603 70
    0x3910401601c1c0c1980c900900c0b02c4030141c0d0614400c0c1201780001c1244080440c0c128041c1c1d08010849250940b0f0302c010003110321407480524804c2100b20407400788440340d4040d54140f200316017000500e2021010145282410341c0c800040000d08041c0144400d5992040031006030803150046034601102d0304600c000c0f840745018a1213a80d1300880010200400142201d0107044820040406255101010350a110390b011504a0b07841c00e0803041401e503000c1c401038075001001696410102141071981d6039103040c01d001e065650340607207000211107480902440f01e01600c550140c4e966841c00c40100002540c04210f00390421030a500104116951402902d4800d03030000c08050b40c80032504020b450700d0f20344103442500000040f00304001501290060601d104010381c51003030384900340c42000290140b2040050260f032003800b4056281c1008850140740500d58005c90349030a2071082c064500043c2181c0e12054842440e06e08070031818244240100d01c01d070741c00200800c0f00104c0000d040e5000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 704797508 1250 704796258 704796331
    0x1e0509090a0905070303110d031a060a09090c020c130209100e190e070210090f06020322050c0f010320030603010b041d010b010c0f03050f040305010f050f 68
    0x4080c0100d03440188903400140721980c00f0007140c29030382c1c0d2480d001d0680c0c10320714042c19075809441d28060ba0f040c0240200120010050501411800c510301044020b0700b144880c0300c200003134000c01280d0080c035440390000c0140560010410304101604101d4002003403444cbd0701d4024014451543d4584030070044c04880784060a01c40840b6200c2c2c008550b0241c98056071300100c810030035000480107041d8032050f0080480d6408d9544110340c40b54004103844111000a044407840c01002e808035020754084c6410ad50100340c0b00b003a000022560b1001090200000d80c0c01c3d0700310300ba00f10414504085904140e84007800c2c10700142e640d80058000d2540318160b5485890300c00400985039540030340c80404904001001007001f039500800403509584010040400740d8a40340890b1165806890440740d019441400726615150540d81180d10740c00260100c4a03c200601001c4005042801803130700e030a03144071000816140c442c540d0684500c0240c603e100f4018104665903003079903124084412042d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 704798758 1250 704797508 704797519
    0x70b01091808070f020109080a051b010315080c0405180a03030b0a121104060902031311010341130209060a09051305010c02032115040c0504061e0509 66
    0x1404440c4403a9a4518588000e0044400040c05810401c1804028801e503000b87e0303030352003002e455010082e56600b0344280a010f80d800b9050300b40071400e03102d1030405640c50614000ca002001d05101c22014141508261900c2e08500303035050761411715200381540712010b161140b5420006840803601c801030108003400301030f214060452030b0b0b1103455419001b02000e0174401c29031400742c14140107001d98044954411424010700240480c0306000341c90141ea104000710308000441da40f40480d0704002c0030007034145a00c1745000c1210000e1218000180351008440c2a1105030822400402c2802c26150300031102301c800c1800403159558040780483d580c145d07003c410503201e0300001400700c07030340d50b205040440c20f02c002c004044045030215101d4602c00c100a10412040d050b059840f80a42c02002003100c5510650a0304c4581c001d404a8004248221080007203031054081401d0324407000006000c40c1000804000ea680e10122480440c2031640d642c00d00c6809581000b4018803030210414441c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 704800008 1250 704798758 704798771
    0x3010f030b06100f050a0c0804060e03120903070519030503180f010c0c15051c020a02070603020a121109030d02070f080f0a1704090213180932190b010506070b0109 72
    0x25000e142050701892300950860b450340d0342c4a800400da0020720115500900908500d911005080c8042d5402520002d0181a4813070516040c021504449900d14028070b000200c000085241480206500201c07070b1540010719a20000b0b1001c003608421455040000c030b5070002010034130346a110003d07250b10711000f401c40c1c028444201c0380e500604c2103000c01c41e01ea0f0f101d1120500c0b1660300402c050f803469000c1e552000e60311042038089000d00354400020881c0611100c0440646030711503c1c500340c2040c0300906100825010074a4038030303412003050240c1d10066092003000c0000003040c0041441c0c6004009a86c021031400d51501001400208100140c844080c00c0f03c1d040d8094030094101c410085455054401895070312107568855800c1000d80320200c00041d18142c0690151030350040302c07069003406000e0300300104a405e20034505040810100ea0104000d041c010100c480d12600341e100d41c140130350308041d00d8140341a0b009511403c020030903140019807000c40c80741102c49140c03001a11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 704801258 1250 704800008 704800027
    0x9200306061210050f0604051e010b0f07120806130603080d09030e130218010806030c0906040b131b030e060a050606040e0702030a1101060501020304050d080f03010f030b06100f05 79
    0x245000700300395a9003d402d00303040200d19510303000014402c8104030340c00d000d46c0c0c0b10110401e4141411516a002080790354005001c00d041d054005d024400d14002214580b040c82d440d01c10142c010300c8032010000d41c0d45020702c16540380c44100d21085240c1200200300307082c41c503500d0040a02c2100b00c280501130700d400f0705406040c0a01440001142c0c05008048072200ea054044000e62041002e030151880010303900b02d49500c01d211191048001034000c0052201c41401c1011007580102042e40c8280c07140080c200d00c2d00e801864011035042081e01151005101c0300c06440100e294001c5c17020180b803d00001c0780d045c0000780c400d80040d20f02000140a80716040030401300e100d19000b0103000130104040c4990b0f03070307400030050401e003120b5502d0b03240c803007a00342e511401d84917103204160060b0b10070b00c41442546400229841a90b01c5400b52503e4110698034008042d00240c0c0811088200b85a04006110b03030842510f03801758003294400620360071008041e0183c030060a03818208000403860508 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 704802508 1250 704801258 704801263
    0x190303120b0301141602120702120705060c010b040605030303100b0a02010e060717072102092b052503122d141809100e0a092003060612 60
    0xc0001e028000344141000f0000a9a000006903100d0704543c10b00c0c0944994148003245000348100e252040600d08031030340e0200510035918142844860086000000b041c0d0341d00c900409600d01c0c440c1c0085594503031141000202c400d6540f2603406908204108161030006201407010369400c5d8182d0342c0c8549205030128010aa96801c0c585144142c909001c0d065030802d028100c0a4813080c001c1c00301c0d6844141c00c40d10340003403022034101c0301c640b44400582d880700e54002c1c00b01d080c8054084811381c20008549060690180c5200484d001801e4048040c08030030b024402070f0106000c601c00140c00c5104484081c4500703484068115003c0341c0712985400d215104d00e2030280c5c45407400070070401442800e843d449649041403004591604030701c1d0061040101580c00c1109810101403001d000306e41445008a00240310600700c0034448004640e848212141900541100c00d00165510244c1790101c01c00b5070350002c0b0030310030180400380c011a940016056034030a03025145a11000026808540f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 704803758 1250 704802508 704802521
    0x3030f2618011a120a060f0207150207150b031618050f041709010e120d020c040b09060904020d050708010f0f020405090a09140a1109070309050d0f0903151a19030312 73
    0x86c01142005d07062000000b064014005090003042ca1740030807410290294201d01c20218010b0500c0707048468103c5c8490305134810101c405000d0160f80d503500c0103542c2c0109100e0a0740010440b0110301d42014410b00e01031007070903408000f200906555062a854904002c2907080d81003c0308000059601e420740d00c1050011794842c405402120720500300c0080c83e07110070210031003000500c80c0000c18002032403e03001392041008080e00912041d11800240548100000d00c1640c22501c104480400180c0802120000b090070800004006500b080c0020654409524041107280140310034032146c1d850504c4241c20205154001595441070719000d140000a0301c030400450140125120038444000320248541c2c1c012918a000d981e01d0000540071612a00700244c600e0380503100c0b01240500402040030006854102641019500c0d622209403010030003400024544404030403407240785804101084040840e41c8a044001124040710124800c4c032014040000e000002400c00c1940e90100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 704805008 1250 704803758 704803763
    0x11010f0537020d020c060423041d280209010b031f0f082506110a0606031a09070308090d02040b06030f01062003030103030f2618011a120a 61
    0x1948030300c48a0501940f41c0d81c5041d1001e015010f100030034001480c20504035401d0740d03080c00c1e01d0b5401b0380c0d00c010030b40601e08210003103c1d00203644600503d240034180303898250254600f070003800300000d50300185d0541c56001e601d4200d0400704d4020a401070f6920404e2a06650b1142c015507240d9581440c0110603040700e203e203001c01110075101062141420f83c4401c1601d01d500116038998aa40340701c20507419008181e2426074112030b0061107503903c1124180340414507002143d1243d600f41e1913031001c607803e40d40708440f2119100d11201d0114101040302e07a101440300090724042e0f20759200d2142611442d03200c94400c40b1040075103011591390f035112601d0003001602e41c40d00c0c2e1404c04510b42d543c3d40217000e2240450500d026110b250040d03a01c024612103044005141135074a0b42d40d09440c0002c829410b081404640c80700025095a04009216000f2100c2c01d810a01d06082c642c5d24030421408030721342400d90403c10803800c980d48145031030b1220001079030748940b44009051080d00b0000c518100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 704806258 1250 704805008 704805097
    0xf03080f0d092f1c0206070c0b030c0403061103090c040b03190b0106020c060f0405011404030f0c0603051602070b0309070305070806060f06031e091903030911010f05 73
    0x1080250b03c20318403051410185801820480107080200000000024030180c40b1043e010125801400d002c0058196a072080c507810042c075403251194405a0012141302c005940302240400920400307004c0c101150004007850391650400750a07568550015043e06809a5180e0142501c15101000078007201e540c40035060401d081207142034100540d0a100b400014460300742c0352880c0c0e2801404a8178000031010146141c1890040151580c3c103250141017000c58050000102062080101701081440740c1c07000d80c0c415042c40e4024044460150a0810110428900d503408903000a0f01500303a803800410b0944030ba8420b5005441c014490708000c109004030380b80045d504600141e002d0107004100c0708210040301c82414032010780003c4a020110001105d4884050049a644550099004c4017513402c08034144180c040003c49090f404ca002075a500180300030702a45c0307000910a9582482c1642a84250033b10050144c090110212460b0041503070719880800e88000c8030941c010032402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 704807508 1250 704806258 704806283
    0x1c062c2206150617041202100c2601120809030a0203030406020d0f0804200f030f0a11090c030615091c1a09100f0605041a03070f03080f0d09 62
    0x815102501e10307101810b188500032980442d2542c080d110320002c0c1d03001007a046610b5070f50b9440b001800280c207200f0f04158010400c2880244c481c9000f01401c140c6c075901e810290003c0649507104214105581c41c40c90b101c0c040040c0170810040f203005401070b42140690307840d0710844001a0610441d00d030029890704c40003800103541500810740c60001d40071511030349070b1105810f405954503a000c540003403540110030559940150310268803070494001500342c1e80f06081e00008240f401d0507000c0d0341d0701c03d80e01020950003040701e40003008150314801d9540c4020b50034200060340e02804003a14103803281c9144008003101107115403c0e1902070000900c000403100c9001d614061a85c03691505035a403510b13804040c2d18049016001d5801800107400900801024030f1024005086e0f070400740304600d81702c150020f050307030f1540540018004506201070320545034000705460011130364081554403c070ba14041000c42d45403070580d445244400380d021b5031880304414031001032007011001401000b4428 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 704808758 1250 704807508 704807513
    0x1615050405040939060f020f01090c0f0807150f1b08040501030b0306040b0610030617010b01030c0f020c01080c0c0d0314071b06150b1c062c22 63
    0x1410755000110103500100e900d01c1034443d8600c1e50035204011041c03000003c00801000d41b00380f1100b030340022544140d07042d055051410a003543c1881505aa03260001c1d40b040c031041c0038800d82e003001000414001e1004da8946201d81010f06c10000da1041030003011502500c416000c0d4415a807450380710700700d4000e40d20192a24403079540050003400d0001e86050040381c0541400524035010b070b604180071240a64032042001b45604502119108243d1602d10000789102c01d66800c5020f15020400810301c0890100018211251021100200003d0700403d10345c0b0b41e0086100790f1a8402840d002985940b4010300c99040e21941c1e004014620031280b03814503a80d810f40c0140f4004c1e00c0d5618250442c0c80d03802d001c0b0381103400028450056030420103810f0000d20964010070307025425860f00c2c105c09584820442203500003121180300c001c02c450214500b510036109140c0a40002c0300324100808403601c201c0d5444020041c010656441140800c0504140c0e03101300c01003804c0044040c2e02c0380e00c1071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 704810008 1250 704808758 704808773
    0x60510140a09080d12150b070204050601030b030f060f06040c1d0619050d0b032415042c070b0a0c240605030610120b0406060e0f070e010216150504050409 68
    0x20070007a406140041b5001c03000341c0900c03080211591110080c0c1480e521b6000c10000b050050881070506a41c1c506545140c0c40510040200320205c5025040502e01980c100d00c03d2200184210302c00c03840d05800d151603541225200910101c40111035400c007084c20042410ba2040d10b00401942d0b40d402c040b251400c1e4040020041d2000b141400d20401c02c0d40018950b4840c00e82140d450310701402c40c490098044a88030b501c0d80606640500042c540c01039011178210f40d85c13918149452114000d823010b003141710150740e00070000c0c034400421905180a469540c54000c0504140800007881c03d5081406000740e05903420052080c0781d0548030381d00352511001800c00e031140c2030003401220001400031002115a03c200e55501c8094041001c0c0f40d6542d401c640c10040003110900d540703040126500400c03510311842003c9100172a0a241804000500740b482e00b16145030441d8000d01180354040c06a050b200200d0f202c000d0700e842c1000715039070141c905000d5500119007240ca004548403e11000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 704811258 1250 704810008 704810027
    0x30406050117010b10140f130503160f03020f04140108010f14010308090103020705030c0d05130e0610120e01020d0c11060f040b070903020d0302010f060510140a09080d 74
    0x711203030141034002da0a41c0c500341d8244100031640520f000c80064042d5000703a055400504010518503e07107001040300c01900e80101400400d8034409200910441c141002142c5d80d4074200110000036038904044a11032450074040280907c0d0700060072081c5440750340081500c0c041c8070003954019a161080300303000340028600100003c0c00c09518840010154401c2c5050701c0d0818000761920034020010f402070342c03007508102c80354841008004603940c000d1090079440005551583e41d0f03070034800304da08500c4409801c646102403e0b03d0030700046644004005215030428102646080c0f40440311070001d005841d4034080c9540006407001481344a50700c6040006643c1d01d41401000144109556450048810150007001d820220340400e118a503050f40c400c3d040c2c0780210b82140c590740440c2050070409800ca0160303449100104e40785803240112005400285c84140214105203001803c09410a82260000400041070402c0a20801c001006842c10b20116a440c10501c100107203112103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 704812508 1250 704811258 704811269
    0x1006031a0907030e0709151a09090c0403111f0e06040f030b27060c1c0903050c1b011706030a020d08070b0c1306180f090b181324020304060501 63
    0x10010041441a047c2c4252402c2c043d00e25002008141402031141e90081d0286102c01d410406001d410103558a0886540c4248441a80d45071660301d5071912a520060050074640301e0044031507a070340762882d0014100300084982c0742400d800f000c010085080361145402c0101007660b014404010301501c03002080c05541c6c074507000b0342150b40340c0350302000d03050104400401d1500424046620480d02e20042c1031007201c0101c03110004c0481c0e031450002c486901030100c01103078000c902000342c0d501c00c0c0102a88400813140c80341d4440a07080000384912000d02c81410126040c4001c145a924200101e0480b1503010f4582584c501141c01e2640721a000765808171010b411410004214404180c203a41c0c010a45500030414141411b00540d00304d01c0098030b402c980001100005241208c0c0088038000708022080054441c41c03003403d002280c07004104130b1a0041342d110a2208146a038104242119001a8216600400941f05408041001010061090010007400180041035100d07504a44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 704813758 1250 704812508 704812513
    0x3060c0905130c0f081905070903051b13090606120605162307141204060e091504052d0105010e090915090a05121207081006031a0907030e 61
    0x7001c03030302c1000944207803c2c0080d0015840396844c0c81e03e03a005444103500160a460500d41080d08103894000310b40b011106100025215030b001c0080c008140a0b8920103100c0402160204501d0404949a00f450441b520400c6584005500502038203900c0103020703000c0b140c965001c0220750b0030701002802055421990040200142000c4680103001302d42840f8442c1000880e202401d0391010034680121005407500160100040303031154043c000c1d00e003c0e8240888d800e840701e0600800510182e40310405a0042512906010b5800080065152038407801c40b0080340342d5480d0b060a0214100c0c0e81c848800a14a01100c8a05038520412071816500c003a0784640c0c0020400041104000050f90f00c49034a0f001205035000400108603259845007101003100c0c0b01c411540d0742c403440d1000c501050306a0a8001c00d0f245200740c10701c003025406c8061450080b0f018103088840c0d1035608442c3c80707048241544d405170b100e0450311115100200d4407006114a40700e15268001402801c0c00300e289031001e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 704815008 1250 704813758 704813779
    0x50109060914090a0b0c07060c08010f080c0904080c0f070e040210030908030610021c02030c010f0603021003091a010b19050c15041a071805010903080f03070903060c0905 75
    0x4441c82c810441c89502008000c00441c00f0300c1e11000040c1001901016125a0422860300455494080c2c04a440d0719607440303210940c5404561304101071560000c0307899421000c9900c00980d10724600c56041501712031940d584001003540680b0b407070808001c50450380103417040011508042c5c0d04046c030a074002e0f10306000052602004500310368000800502c0c007030041c00440c4441c200090b51000c180502c1c01222440d2040c0541030002d210901c0d1410300683c0700060305050780d0002e00401c01034407070710a800e00001e825980018180d01180c5400010143d0311132284d401d0020a0800a4049030041858042540c41d003401c402d007036009803281c003200c0420f0181c64000728458822101510100c5014080c03203015013841400c80c1c480540306640b031900750a82c0d44e0070000e60700d407564016011038680780307011881807400480302c2e216a4445414080c52100410200786404122140b001310b0b51100c503900d40e100b01c800e45800b6041c0d000544200c0c500703100901d10a40041c1d44d01d0640c1c0381182d101044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 704816258 1250 704815008 704815031
    0x100e130c0f0e06040605030c220915050d08070b0406020d0513030f0c0c18110c031b0c100525060b030705040b0607020904021c060b011101050708070e03030c010501090609 75
    0x83d0b102c0d912a0702c1c0003941c00c00018410302d50a90140c20b44820042402556012008045e01c80100c5a0030481405585a03802c8104a07581403402e00240020749400c1c00c104403030f440304100c0c0d028454000d420b240d005000603040200960445203542203040c003c0000d8200703040c2d107180345c1c800d01078202d0200360207601d96880c50303010754111100250302000500c1b105043c01c13029a00d0741030032a1008034560b2140142e100380d0701101e0203020f507003844d41c0c0110b171284040f01403c0c1502d42c0c043d548141c80d402005580320162184038281d000304c03003c0d0030103031b42d11020340e50581c103154244c4c880200304003001c5500008201d03170340e0040818180200c0032100c0307080e11641007004407000e0419040d445030b8100131250060600419103a03101e0b0008009600c3c80f281d40004610010182c64100d8160303907151207140156030080aa00004080d807002002549060503020b0b00e03441c07000c0d10320014070180c1e840c42400c070395041080b40c2400300044024042035a40d100254084c0400d170142c1c3e4101030418000415 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 704817508 1250 704816258 704816269
    0x15010f09150c032a1b1206020915040803091c02120601030308060a260111070c0603050114010206060d0c0522050601170a090c030614180705100e130c0f0e 68
    0x1419003540a0441011596910382c6544150b0054881404090400081c001b882c1e59100030030302d0203170101690b5200083c041010340400712000e401280000d0200340108207001040c1e8102034002e4601e200f44003218400c5d580346485402000758400c915403a0302d61500701c0406c0c294100c03480307920782401580300c0c4010840c09045034090664042c200150408410440c0348074034a0511111000040e0b815500c24186d07407651150320142c6d12100d0015040001a9151192500501e040d16006c1803925410740001e49502c2c010740380e50322032009058a4014003220181c0b0300000c160081c0300995440c0d42c0030307058940500d0b40e8580648a0700e810002038a6501035400d4415022965103850303000c3d503983c1d4003a00182040c0382c0c140c500c28003a0034084005004d5114071141007006407083c00d180d19058500c03280c1c13035000400020340e5401101c0100700475140d030710604044000c2400c0200500c643d05010680810f403880b40080f00c1820800500c0906400c04009141445a545c440f00d04002840a015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 704818758 1250 704817508 704817557
    0xb121005060a080307030521010303110c04020301050a140a0b0a02010c0801050d170a020106030609061a0d0b01050d030309050607080f0703020f09060a020a060608011d0615010f09150c03 82
    0x3c0e00d5400800003000000c1c0b140008001c4030748054583c0141030080c158a44a89209030011004030320011096100100100140351420300c0c204c0302980f4540c1400b000ca000319240e0f20940c00c1c078441c82d01c0210342d280d0343c1c426482c0280c030400f09426190080d4140c020301a0103403000c00b00109230504004646802c0103003203508000d4100141007102c242903031060071203510009201d0119562120301200283c51801030940c0d040c00b41c1008140709020000d250f04040c2e10700d24140c4201d5410b103010b070020300c43c0051241180e01c00c032018901d40c0220b01701500039001d5030200030460302400d420485c03400e401619540c081c0f1001c03103051800342e9403600164128440c40c403060070042818802c0d00000e02d01a00240304101d0325106449004403280e4031102545d03c15003102007680d45442c65180c0a100a0a181c40b000b00307440020038490400500030041c1b50424240c0c913042200d030780c062031107850003441020b00070042c6400524078807900b00c0c40241500020001100040d080c114000c82c4028440c2084 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 704820008 1250 704818758 704818769
    0xb03010e0303390403061121090c090f0403031b0512060105040905070e010e01020c3003070302010222080d300204170604030c03080405010b121005060a 67
    0x15880c0d40c480c01e030710800700e10492550f50480036440c0440300000781036a040954054002456981380e40c150710703200b000d45004521041c0145001e1018010420b03030390306e510820341105140c60b5081d88900081030b040c0000b031250030b5040300c0c11100707000b84003440100707651146000e50750802940e6030f4407103d007481030402280100002c0c1c06014251044160014880c0c100c48141000740c80d20f6580c0d9020700640d54115129004030740000308592941d60040c90200e660038007440a0604401c07900e00158410000441c812109001208100300c1810076080e2100d1203214041100e4a815040c0342c020302070361108500c2c0c1e458420344040010000c914940a41c1555058409002c02c2c1c9220a0211134032000300411102e407110340b00b0900c65100154621544600f0903c9016a0300c0c0c0c2070618580129800a51104059000c2c40c100000300340c0c0500e1160f00340e54503281c01126611142480c6015202c00c1c50f4259000318240b42c026481c0d100018502c0503610004400e001c10794070030b010090010307064880c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 704821258 1250 704820008 704820013
    0x31508010c050919121e0609080c010c140403080d020403080f0d1a0616030c02190609051206130303020f040b040e0604090c090c020724020f06060109030f0302032106040b03010e 78
    0x2000020380e040c0e0703e42c1c0d200204e0170f0340301035141560307c4410594108a1080e40c545000158620b2260020301035100c0c01103c0742000d40d4102000521a0b80e9840f86100c081c042c00000304a90040c40140d80441d4021500300c003100d919004103a0400d4403950107031780b90910300380ca01196030880c0da07554002042c072171400900740781c10101004074601008444030f000702c040002d105042c400603640e00d03903e1000c80c02c1071810410712030b0130040c0141402e0920b4003c10320601c030300f41031848103100000c2c940c0ea0000414183d08041511072505070040d025005403060081030104022510007410760203441141d0f15050281c800e40c8500c800c0c0301c121140c078800582111100c080511103000ba030780020035240c0c0305104844006594102c490491020b42c00d21501c404010100307503000690410000c0618072040001c0d1181c0d04041c4006000c099440c40006c4c140400d41d410f00c0e051600a02c00e55a000c44e00f4076400300c03079030660805190006070889409100d03502d0500310380c0c418103051041091030b8907035100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 704822508 1250 704821258 704821289
    0x315090601080105310c0b03060406080f211207020303061f0f0503060d02061c1b1d04020d0c0c02030d02010c08060415051804230a03031508010c050919 67
    0x107412040445444074540c148800d82d403032000039006c10680801803000420003600c0307060490810050300d00c84c2d40403280e5a03100b280400c8440e90081203444414001030034031550300607450407040d901e01450030544901d030b04000401c0041c1da004002903201d240111811000c8a00200680207a0842d005c000c0000031001c2ea000f07400240035800550700140010000303050b81915a0005a0a41c004040c82c101c900030b0f0825a00e5801c100d004010840110f010310329442c000d80080140f4140d00418010203489440d00045015150303541115507000c41200140540d03400504042c01c06030188404a0280c400c40c2c40400c071081c03040c85949945e0b1400d0341c4001140d1502e00c2004003400260111564001c0c04031030000e825560982072542c1240031010300f05a0f80385c24188a00304d904101c1410307459060400901c40700800c04910041c54990604001a06040c40d50a10011500c00d40003440107629100311590b075142c0010117042c3c0b901007243d0744544101154041c090703c85040c800c0c03150311155081c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 704823758 1250 704822508 704822551
    0xf060506011407050a050709020c0318011814030d02010c0926160e01050d0f03081008011d060901020f09220f0623150d09020315090601080105 63
    0x80025400200500d0110a10941c10307182501540c07048a00301c1d002e40c042d202803020820107202c1c0038000c1040981c110300345002070120b03544070b200300092003003900403143c242041a07014909131060380c0c035041000d0007102e4807034401034080a41c5401d21072003441901c2040720000c0c0305002d402200e00c02e50340e074160070501e0303e480c48080d04814a80350b0f160340c001f1140380c03058000422138640e0310300201005500d524500070245181030010781001307001b05d00320001d61300801e41c030040e404c83c0300d903043c80c05844581c3d030040178900604094110031040e5003808240282c0c01403809034030b41411b000005581d000d03207481d80304500701d101c4c00104288001d030078800c41f44d5518000300d42c00c088230804041a910300b9001449501140e055071448842d441d61742c14140a0041003100713900d031204103620b8030f25108110200040d00b0103240c1c2d420582c02500040c4001801078640c10900b90141d0240865010780d801912911121030102e45d110108d00c100710000415000c1405928002e400009282c01c0e44049003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 704825008 1250 704823758 704823761
    0x10050f090403095402090a03110f0409141005060f090601170a06060e030105070212130e2706010e0703090c05030615010306090b1f030605120105010914040f06 70
    0x946441100c4101c48001e03081c088441034202144139446810441001c0c5640c00010f0340440224101000744103002000e4140c0340d06840c4003c2d40c2d0818014420f4000960005084038900e41117143c1003070804841d5401c1111000c1502191410b178010341d00c1030182591742c0d404503001202d030303a035015180481206040c103100c8142074128106261015060b5108001c00c0c030400d205580ca03540c05079031000c04100781540000c22040b4200200c000340310354140800000d42d90101c01c98a501c44403000134840c01c100c4010f1a00c200100344505d8095400d2512101031485103102d1aa105007010228413241485600801c44034140c54542440c01440d440e408821001040741d4a0201d03944c8800441c0800c59a80c104500741c42410750080a005002c080c50005041c0c620543c0805500c0303040180110a6507102d00d9180d00711040a000344003051400c05044000c0c0c000c982c0320641120030900401c0340c140b010340010b41a5149840b050040c029000100c41007120111000b902880c00c074050b110006195 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 704826258 1250 704825008 704825039
    0x20030a17060f1c02150a020d02070510050913241a16200d0b04021203090112090c030807140105090d0f0e01020717030711044110050f09040309 63
    0x28094000210b817240c0561a154011100384d030142c0e1040900c60030741c075030411490019107001d030b1303202028a0721810064094003402e5000ca200d04c8215a0301c2101000310340c00900180380c2d222002c0303100e8400502c1c200010b419401100c8010403003002202079140528201c4065510514144d00c9008160325081003d044080c91100030088190340c00440c0da94400c41e04240a010700c4803107400c1c0c00c00e4410000640410181103616420034003585926a8025515161008111a01145c20202c41c03031b010203c801c954000404400d8040f51590512041c6235010070407003410300007080b198032041489130741d48900004100c0024903e00013600450320581c44106100c5041c0100c422140d02c4908040c85001b441e1407400b00b40d440031652400b40010000004801c1d40280c41c20480c07042c03545413905040e1030f600c0c0b80caa25251078541001d4003003000c840a101c8880c0000640b800c5007020001c0c022411035030305c03800d40b1030303580390054100d0391074280304c800d00407540b54070b0384003110303142200540781c5000c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 704827508 1250 704826258 704826263
    0x10080303070f09090c050a0806040603200307030501050c090a080712060f0915150f0e07030c050c030c1005090607170703060b07060603020307061e20030a17060f1c 72
    0x1442c00d0005132400c1a00842030035034025162540ca401d80c902c1e004003450401007046204d9170074801d081011580b400340243c4040c080e00c02d800100650080421b1802c09950710041c1990b2034070042164000ba914040c1c104607400700c03000000c05035070703a8549a60395140d0042d0250410b50210210005400d81c2c84511031096160011444030019120301040d02c028005085d200c5446004804181515805003005040540c102c141c0701ca05101741302e02c0c2e48070300410543c1803503920030301207060034010011381e0007440044040302e5495202d18401ca0b100c0515042d40d104160600c2c01241c04400c0105a661181001d961803207a4000c40c00801e169090014007050241a41c0e08000310340403681000600b6050701a1802168080c55403042c0340c0703051410761001e420801e4900099190010300340d0300303600c8407051f840c12004000c2c044460705445007144112241034400051001c407001d030890b804070300c000c2c20001c0c0500e06542d9401800400d100c4540300540c048007102c0c0c16004188400c02160380c1c1030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 704828758 1250 704827508 704827517
    0x1030c230d0c0f05101d01031401140405151c140109110a05030f121812010507020f01020c190f020a030c09051617060d050115060810080303070f 64
    0xc4003001040701d03040801426105030205030020700803005000d00c80c1000f00003d4400c40400070581c08003e10034054031003030050008035241c498000d80e00c260000a800282103496040c1e5507518880c4813035000107256540e01481c148400114004122000301c400c2c908050300580c0301d400c0d004210701e07982e040340c80b08807540e0000d0300004140480034401c2c00d003403074490205402601d0354041009540c020f26800b80b031081d4400840101e0703400340032131540d03882140414030607212440000c00c0021038002c1500107400c401c4120341c3d0428420150072860040c0203276003e41d03456490b8000c519081c0d204888a09132a03a1040c03400410380e41d0100c41c003000c100c2c01001d01c51201c80b126070016030002e820798400d0300d0068520b14244281c0e04c2d244035068020910300c508a502c000c03d00b501070a0b002580c00100514445000000c039a0303102c00d200c4c1108141c2c8040204000200c00c1c0105508016501030704000403071420014112603402031000007964000c0004504695481c24100c400d01039404100c1c0c00c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 704830008 1250 704828758 704828819
    0x6060d1119180e0f0610170109020303070b07030f05010308190e0604120c060203070c0909080d1103090d170a151802030604050717010b030a180506040209010e01030c 73
    0x10b40000070b501450742d9100c0c0001c550641030000e854a00f0f1800e2540541d940c2103101407203006002110203804656010300c2e10085c50741456034040c0180a4001c0c044d4150200103401c40c104003603005030502c10384550318108030b5101e080d10b0850407602e090000500e0030100700000229111503541d003a01000075860f1501c041c0814001141254010b607010b003000c3c0314109074003020814001d4a481c080d2600c7d20040d0704002c2e00307440b240d5940e029407081100c0d05943c0c4243d60241300b07080044a00c0d6283d02d003070910844d504208003490076030088bd140d84240c000d40192504281c4075280082c0c004030f02d20301a07480b98541e04410341c0104002d112201c0d030440350020014540c010174403480303d03030600f660300183c9034a01101408240c6400415400c2004007a0108480c8017291000c4541520415045241c4a540d21041c400082561260800c5901c046184a4082100001c2d80030301c140c1c400c1d00d0070801ca0340d035600380141c0d03140203010081c10640b501078107000103c03400481512224614511076441e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 704831258 1250 704830008 704830019
    0x50109050703140d020d05311509030b04060b0d050d021c050301183b070803031003060c020307150b1f1b21050c06060d1119 55
    0x844001480460300380d00540010800d00400d004000680d071034140203003004425507107000307444000c1080d500c000d014002c110003420030032001c0e961111241c0c600c1486582c09810052600d801c00c00d00c215042445110154080903114614002c1103e82c081440d20b43c0b038403a6030742c41c0040d1501c0040d041c2c200c0c43ca4106000410010080001300420715005031812810650001001240001c40c000c03d000c03042004004130030108000c0607098404403000100317000080041110040301154000502601104882c5601d520f550020401040f00381115890b5603944032040d201d01023128030b1488480c0f4520104049a03c54004100c1c124480c81903034980303a065a5902118100d90319084011603071444154084d0415007020001c1d0220b4041c800c0d40d040f0301c280c0080100182c1740b643e425800d0160103c0c0b080000c8440748500150410f410344607003000c1c200c0020055040008401c280b4840e51001c01c1c0c043c180442d80400c256040510700064034410300500c0b41d0601d05a49000c0724152000c0000396 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 704832508 1250 704831258 704831261
    0x60313060507081609030c090e100c1205061008010312030b0301020703050301060206090a122111070c0b0c0604112d01020d0504080c0d030203040e0c070b090102090f0108090a0501 79
    0xb084519403100401400c0a0103440d0190601c0a4000c080c0020800705101160500140d0012240b5404000c5903407181042e64070b00f0074103001c503070b85035041c1008040021950881c1068085842d40641045035036165010416000c8401583c4030100d124a4014004554070690410110095007004102c5119842c0031a089a11400b000e40c000381001c401809801d505002c0917400c0480c2030000c0208507183d854072003101e0700c081412802e221010000320b010503c3e1140030761030700704074440410600e102e07124080d186502c011022600020500d402044019420040d200341084001c0284401d940d1079407000c80f41d001e010b002c242c0c008401ca031403018176003041034000071081408003800c1018480c4800a890207081d007899100b40002400144402c1100160310f01038042d08981342494041c15041c182e01354400c1d50030001030605040108503041054070020304c2200d200c0c02603012141e0342d09140038200d01403010401e601c2070b101002d03107540d5803060380d502d50400100001c1d074050f000b195a0307490 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 704833758 1250 704832508 704832511
    0x405010e0a0815150306160f0314010b1809040309030816061a03010f0b060d09030c02030a0605161b0b070909092301050105180c2b290603130605 64
    0x10420742450100409280c404104e01c0407060f09030020101c5081054440c0b043c0c0100d001c0c83c00410500c1900d0f1407500d8880d82102d82001e00c094822130031075845420b03002135a032011075140003440c480861a0f55a040501e03443d807103281c0541c0c800c81040d06594500420740c3c88480f254041c22905030881005c11124422403521510120511001140c440141800d46034802d4104240a1401d03107002090380b1600201c840d240303a40c500005c0c0c4a041d80c5401c0d07032031000d004000380d05840380c0c6402104006030790307014078062100600c40700d1000006420441c5c00303810003002030303060381d5000e070401000074054250f654000e1410f0611140807911615018201e5000c54015101d02000072500101d1031030340004486460580c10003402a0340c10400403410061900c1a401c408030002000624842880800d07144015198001e04102410000340c0c01c0000d000b019807240c0084c500380181c2c0c2d00540070780c100708441307000509451510849104100c86600028800f080401a094000c80018503500c0b607039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 704835008 1250 704833758 704833783
    0x9050405161d090102040b0702040506040f0e060109112a120a050d15140907350f010810090f020a06020a0b0f010819050c0904260306060405010e0a08 66
    0x4191490440c12040600302c0240c00c188090740b04110900c0401d014808546c80310f5010b40700031030309484140c0414000c1075080b0288042503c0e014102081ca50b01196507070403121200320501c065840c00340400c0040c0b02c5c0c0c849401544c004407003008100490507410700d00181b15807081c1c51902e100150406420303403001203120009000060b104441c2c0c8868824000c2c155017072195403611608103030501201d0010458001d105117900b000040842d40701e6101030070310b420120415141070410054042400490503462296000c84500003810400000c00341c6048806a0700104914a40d020501000300001c1105682d00480c0c0c0e420740000da154420110014030160340100700a02c96030420325040714028142400d1404070314010440c42070009903203666a0300c2c03005440c00f100f03d1850441c0c544011140072a81100450080206201c0c2113041c40c0001d690350030700344a00c0106540640c1c07030303480100c46036075000609200c01c5c4402d510030ba100c02c001c08006440810010313101d154a40c030341007150612 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 704836258 1250 704835008 704835029
    0x5210301180b0a0308130f03061401050f0a0e1911040801050c07050c0402030a02040518010503100204030201021e0703050601080d0e1c0b040602040f0e0603070f0e010905040516 78
    0x10480c03110089840c0440580d4040200b022141c2000040c0140a80c2d01c0040c014010100c2c90a100480e801442c400030401004060030705075891401301c015024144101e100011404000503c1d418101d902a07020f0100800343c540711401c0100c8900060b60191011304d0340382002c17284020320340d40382c45100c0b0f52407504540d40da291442d100684c3e096880041000c2807101041c4881400503100140e0030b0b901000c00c45002d40c50342d48c0d54641400030301450b80f00ca83c1c0300b240d00603503850b11507614074132905a500c181e0503076a000c502d0700040c005a100700d210090059100820103680751015058a48400c06040281c4070f5040d500c1d29594a4400280c00c2200c10340c01880e002d034a80c2c1d030003814004090005640c805403000303034201c4003149881c841c0303c050031b08030303101002030300300450350f0b044801a008040582e44480e442d00443c036014401242c074580644641440417408104a400860031907000b00403901c5180c5c03e00110002a0001501c1210540314224105904000b060b0100b0082d0614200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 704837508 1250 704836258 704836261
    0x8131e051b12070627090e07061e030902041b0239010e0409050d050904050a050606040506070f061d01050f270304030b0a021b07050108040f052103 65
    0x1071182011001d0015100d01c401d0302400349801e03400302c0c0b030004807103ca0806072000300c042e500380d00900600c440400041c003505c00001ca840a050351040074a0240c0800b1114140c0d15203900392006550310645c8030a0700299401100d1040c07090308251076651001d8001311364951403000c6000390b41420049100981c1000100c4c02900480b49136107021100768500340c054402010b506184002c0c0c005d50218100101441074903510303119900111700250303003c021240d40c030650810003483e903084004000c0c0301c2c5040a0204250140300c0c00350070b00503400101618901403a080070030445521045084542c800d181205002140d080d2142c407014010b980030740e45041d0000c2d2002801c41e003004050041c0100000103014210084c20009841320064040340c40103090700442c0f07545940101e07400180a20040030030090103802507009001d0604082c054118081d080e110816261134042c0200d50000790440d00141c0030444140d003103d0102d0190098403480390801903541c00446010f003031500000d90010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 704838758 1250 704837508 704837533
    0x20304021002010b100c03020a0b1906050103110f03062b02040b010201090f150908160507050904081213022d0d0f150213060309020102061608131e05 66
    0x405201c0c1052082c8000c00404111000084182d071070410190208100d0744031105c20076000700180140250001c0c00e16200385410100120a40c1c2e550030600f0003241400c00002d555402800380742c200d4489030b0340706806c6c40c840c80706003031136500000d0400c1d6100034a11140901c500e076062904440c100744149180c2490305a005001c243d82c0e249010328110381c901402000468814045090950b03845480e844001710900101c03000b030300c440d000c050048600002c040206e44403040b8518038451040302a9000280d6a130100301c031002003100c000c1d000380030821210031071340c3c0c580b901c150f400030f0005280045c4a041d070f00810303082c40f420703c0440310b00a500c4100b007562100050b0740c0c14105404031509580300d041a512040c41d0008528010005482c0c0c411454401c1081e030103981c044000344007035820059903903100030b000c0c0081500680c0513025040100304070910f80071007500307203910075240d19a82d5110454424602d01c4141e43c103503441340c0200d4013000040019044070f000203014000a1034090005c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 704840008 1250 704838758 704838769
    0xd1101080609060d30020f060a0615050a051608031906051e1c081c02030708010b070c050907091a0403030e0d05010603121e02011104230a0902030402 66
    0x540703414880c8840c00104003203a03440071084814554030642e81200d0f00c000c415541d016000d4814110082d051645031812401d80c0051140711310410041100c1040d01d8600080040743d2160060100798140f41044550050148004011103412850328500e442070407907000103041a00c903011a0705010020921040401c1221410000c141d040001c10519140c0300004070121501200014800b04030030038100c050b5240d42050b8103440e154071142802401c249030504190340600151030f40b20041d43d001c2c80c7c1d118035500c02c4c0c900c2200703a602c524a6a9082404404d010380080b00c040318001880e540101d10b5031503900c401070151610b80c40e480c4220b42841c1a080071070502048010000b0001d02082012a0340025450500b407000d0b40d8440384480241070207405018540c1001d00100c0c0e41d40407165049601884000340306050042541483c11170002c12401e0314005140194000c400b8442404003d40e042a00c01c9590a460b0b0a502c11040325000b18401a81e25400070f001d8070b034041b04010642c02c21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 704841258 1250 704840008 704840011
    0xa0206130c031b180b121219110604051f0209091801020d110a02120702060d09150e0d1d030d050a0216170c03030a080103080702220b19030507090b0f0d110108 70
    0x3d00028018502040c1e01c950914020303e501c1010b031002c41500c0420b51405540148270004550b01510340c64a01030505940e50941104111160805006140c0700a0f000b0701c2943c9040b0401070600b0550303101e1440507054554102074800042d5801c10401c40020100c3c41800b515064540c00291254034400001e401d1a4456900c9600d20008001c224016500c81007100d07084100403100246140c03d07402c00034089959900c000c2d205514103480b154540e8000190241019400e907205001251810140b0030008101c40c01c19405501c450904007185006102400101840340b040342c2c403000003c464000c13960302d00d034098540c4450702109814002c80a00114030141d400750004d40c41c06100f080d0003440420b0520028000c01c0b00840c240c1e0442d65145070058a82000c628220200c81c940c1d200a0010446524007910900c030020607144840a1800801d0440e900f0070007900907145014060805050079101180d400302a540310300080d50754103c80008079901410503402c41700c03900360026002903030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 704842508 1250 704841258 704841289
    0x331303020709141303030b1206010302361f0e090d0302040605030c21010311040b01212a020607080c070c12060b040e030a0206130c031b180b 62
    0x1070802c907240c0000e0021030140c02404190325000b0484d05400c3c214014400c5103001c5900c0b0b100c5510900d5412000038086050300d008890a0b41207016000c00c001142c18428151401d031b001c00c01d10a1803900c9190300d1158003104010644000140784050076030400050b0f0000c1780d8080780d45041c040454020007448020219078181189003904205001d04940001454003003001d100046107102d42d001c00c1807000500b0102040f40e4560358403841c251451101024400340581e25026440f0400d6220701c0d0801e590b0034070700401100c1840e4042c1250701402c2e240a07590020144040ca903040124003414560903806c0590240203103003045800100321500c0942411840c2030b007030041e600840d5691540000700d40c445503103c1d40340d1146141c480050030b940d140d400e90140c0f919007643c03400b88010000b0290002554290351300e40d65100c0d00305110710b1080300090405c4904010600001e0b144882c1c01c4100780082c0c250f140c400343d546a11080e080700840c00c0446098403441e001e00207003000307880f0510846 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 704843758 1250 704842508 704842511
    0x1110d0e0106121e0512030406290127090b0306090703020f060307030e161e0b030c0903120f0d06171f090f0b0105150705331303020709 60
    0x103140045164580e03104410103000c6003200e40d07138903030b02d0681c90740c00d0b0300351603481419a140324154504204464008403400d848040c00d004031044101d80030503200400500f40102c2c12900343e01180110307075103480e0080e112241d00c03802518118600208a83c81c008010621020810700e103030310300349420600060169591544400c0c41840141e4540d01500c174a04800d43d221916036a03101e41c02c0f809001002d000305458001c43c41800e040322036589000e401c0e103900074080001c4050110b40800d0280b07051088502c281418070114043d002d01800800380421300400700c49082e04594000c47c001c1e4807120b0241c401020004100da4030080d5801003d0040c262151215101d000868000e41c40e8481c140c1031040e18032140114802d0803406078007000300c41e9040a4608421602d901d00880700768801c1c0240303403080481c440d4000003d16103a080300c040f154003070082c001c070420f550041c503030440448000e51030690710045603406141c206040d251040c3c90f50022542032007030504000e428008150041082103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 704845008 1250 704843758 704843771
    0x28110312062b0201120f0c02100608160323030d0e010c0503040f1401150b07060b040b1509011407050a02090105060c0a030e12030307120e0a03090302040906060801110d0e01 76
    0xa16404070b115140680a003486540401e8028082000f49540501509114501444c4602c000c0d80054810303d81100304000b08641602d40a1003039440d030141c00080d100c085031071814000500351040051025106c1d07001d1200c101c0301501c0c4036041d500b224071500d500d99920800e2880c0503109004003405001c2d00d080061650901c1c0d02d525120140b25500500501c05414204400d01030960120b11580511b0310208081e907212036081a41e1380c0b2281c400e45655080400300385491510b0f1040c480540d10040c10001b50705003001300c8820b142c001c0c0c0c044a041c0200e01c0340c4103500f000442c00800c81c052085016108803200b510400c0400c510681100d80284001d11600f48201c03c00546a040309805051207455410441c001078103460030010169140c0c000070080c800070b01e4002a003d071101180c00340a112188940300307101d80d40c0c0c80703845016000410724076041015090607481540c041e40500c201154180d1101000c0e0b0035503182c10b00c0480031000c002041810b10b4940d219001e80400c0000c02070004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 704846258 1250 704845008 704845069
    0xc0a0f080106080705070f0c090b040f0c0e090403030f05010303200c010527030d0f02060c2812060816050a03020d032105070f0906052811031206 64
    0x2e00c0f0007400082803140001c0c03508180640d6400f55845c403540120460070240e142c1075100080d16110141a0265060001618071902c50b8041d032125901c43ea5610340481d64154104400301401030000e8040c59510f00e40392403410014040c6078046d50117516820742480f10b070b1540034034030302c043e51b000310b01030300005c20740502a82e1280458094103c038440300600b12404000002d00da80c1100840d6a142c072601310160541500440b06118400c000c0d000d0311055655400d030034103135205008510030090742c48040b00708040a0503949506008107071904421100401e8050000c8480c1d64100c442e21364800401450301a00d010303200006444161082280d0610b10350202d0180c0c00160001001c0c02410b541c003000182c603d58290000c0492701d071040c0b010717080c103a20141c980303e003d6200e50005900c5034000300c0c2d03281c00703501158444180410320104a0103012420f1700103d02403112101080083d589010304004200007404801c2c0c140800030110741089000c0005210074079200700e10042c4400b49030401c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 704847508 1250 704846258 704846267
    0x611071415150102030405300a0816030e1003050103051c1205221104110703020c0405061906090e010f0617130807150c0305012313050c0a0f080106 65
    0x82280c0c2c0444051644046080142c1c01e40c015604000c3c1c1019000f500c11088011f900a180c10482e41040c4140d00940b00203503481c1c44226201c4050009082085400a032103000c400180405008e0b04d404000c0085143c00505520210b4810800103a1500018803d1000078030405044012210229919881c9520040c2c010001503400340d55050391880082d0074003011040c140c40403c01601c43c1134100000e46802c00c0a89134091125025a00d03103000d0b0403001e0980d03011241311607096001442806034070340403c0080c0200802c80c9030001824140c51602502c034001c0d4078041c15880c1c80e0350114034100300c40b910301200b05038409080b0035003410302005501d4002c42007031101c00030f0780011206903541c144603c0f188040c1c01c800900c0000c000030850244020300611070103030301c16142c0c2072248680080c021000c2d41c10a020380c10170010440c980c1c0c41e481036040d001d00440c1e04041c2003203071000c84010703c1c0d504454044404036541440007a484410581c4000b00c2d07000301e146c034100024154180903000f807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 704848758 1250 704847508 704847511
    0xb0408100c020d020c191e0e010b090a03060f0908030c07060b060325050705030403140c18010501051c0c09030506070309080d02072a0501090b03011409070c0611071415 74
    0x213001b2150000c001860780482130355078020708000c0601c03a844126414511035000c01c50b1184501411004001045039007884040340d032449070080c500703020340e825611844000d0030b4440c61528100c2d40c85e0400e40000c0c01003800785200f00d1707000c0c60703241c2c8031442d601b0303c1c40c181d4105020b407600ca540108100082094203c03c81d0b01d2050100900c0e040d0742c00d514000f9034187c0306900c000b51447c80007040000030801700c91905510041c3c41001e0303c0041c0c20383c40500172040a0b200c8190401284580140199403085000d48030301b80b40c160b901c80f4400c40d0b0f1000f070001c4903800d81c40c010025620510900900808100c420b81004161804015080b05500c0b0500300d4020b20340000c00c0c90340c0000301c00040c407050700000104906807a2000758a0035692841801c100c21511545000c500800c0380091805207035400d690480341004d41c42d10049040b0700401804201c0181740703809009151010401140c20340c440c14810b0785180c1950740da6020b590070240f00350021400c0300c0304d4a511005015540850801b0714a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 704850008 1250 704848758 704848783
    0x801142203090b0c1c0509030d0503071b06050702010b09090a020f0a0305010f061e0305100c030e060103150f05010620070803180a0506040812130b0408100c020d02 72
    0x3108000c640c54111514811070b8001281048045822052001c001c5511a0031140b002c404102040d5041820f036418001d034681036500d5005850340e60303542d078000c90080d070380700318076280070140d821201c03040390505045800146d031400e91b203904000700b1940912404071000360031141000760740350000b03a903a43c07211008c1c0b000f03026220300f00d0300c0c00745070300d41c000c800300515403180083c030155130007081d0b41c00140b0140c4a241d86100c12064000d60b8070500c0c140302c2054941141c050481004c00b014400d01500724008108205966810b0440910308140b2000740a14401c0e240c61008408020649040d200310100080c0d81c980b600d001001102c0d0842c080001c00012506004000b030842e81030746080c1318140d4013116040c0400070741311408850481180301e040c130341241c174002c80c00d440f0b105000841c001c5010f280b031a41e01204211170882e50544c0174103454514a9883d18039544c0300c206180303540e04242e000364013036448403800310f22001d164003c2c2c45a412417031009010705100c5200081d510800070894 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 704851258 1250 704850008 704850061
    0x30c0706090f0b1606020309010b0f0f012019031205070306140d03110610051c030801181104031a060d0507050402130801110405030f0f030a0e06070209040309080114 73
    0xa21503410f58054130892994009408548a24040c1e045902900c101d5142c2032003407454403010403651400700180b060076003069458400d1900c41481c20841c0140314504c2c0500c40c0300302c07000200344080380b2080d2512944260b40c2c0300c40c1144000b030014203840c005450202414200b44060012580030742154502100848545204006070b080c00c0e03801ba0701c60104200c00380641000c0203091200c00d91000304486069516204800c0e07062040c4281c0c81c01801c000b000039551400411413a080c03c22000c0c07003c850f02d00300094401c140c0030b02c20020f52050b0300c200c5050003412000f001118010420b198800b00035070390911801c04540d501c64850000d401000d11030350780410300c44d0040d9821402e10b0080d03d4400d0003041b43d40807008118039150018850548a4452814195042c18001ca082501d520744100198145821010140c0e4001c070301c1042d0075084042884940003507a02e050000303014501130b4079010203050424807424250350034031510f03604050300c000038421400110700d2022403011005d40d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 704852508 1250 704851258 704851267
    0xc0d0201030906050a1b02060f0412020f0f010b01030605061204030324080102041703160f06110a09030519020a1403120f2706091905040e030c0706090f0b 68
    0x580c002c104050010b01000c1c0f40100304801000340c0c0e8000031840b40b010001801044600310201c0e81c80c101103600c40c82c2e0903100310114000800d04010303a000d10800e401910030300440451400d213403803e01c0540c1440d90303443e050b2403446541c05209840c0a0a03055a1141c43c0214803107900380b40c0780c1c014000500700b503607503045007054000084d01c5101d00c810170030f60001300c2a5100f103814041d40250244a001d030310801081203149100000b10761001c00c0315940034815080c01d40b030301801034102c2ca0058030f9154580c07640d1400301181100624070301031907444d41e10019046040c140d24290000c092490120745031900a405aa50b41c01c0c460215803800d559060091062000304e410300080110703000d00903202040101c0c61003418805404c841c44404051018808079188045118040468160300440c003040400c5a60400361861040b0203084802050b82c20342d01c20201e81160603000860819410115032059018414081d910080640386441000c20341000e481d03200ca50100d21400e00c80510010313 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 704853758 1250 704852508 704852513
    0x10c12030b0d2910090e0114041a010f081b040b040606021e030a12020d1b020a060f021918030c060503150a0b031618091e050403020c0d 60
    0x4022803040351000d0400c840b181518546030707605041d525149007440c1c081801c0c2c0b000c40c6070011400d510900c2c80d5000e14150514101d1024024901c203800c51903135540b508083d0300b50002c59001c81d80180c0c403808900608451010482c5000ca5041c0c0207006017501c1c88004204a4100141240150070081c00920001244a00090003043d40000d011f030080d050076030000700190003052910b0030008504000000c1400305d16407a48a100f03508090010030316a2051804101c8030b6400391861089290000072503000480351070070130601d1000c600c00141d0004080c03400f00f007418000d02802442038a4207600308204030044c0044881412403400c10001031124070009039000d004070400940c1c2001603802c00710313120030009200d039004551094000481200e4589282040c1007544100c030361b820140d9045884000c5c100076104d80403400002004001d81540a294170742d904810001d0060150018030105508401c0d5076014869403080191460001000f0200b500490343e6401c006044a04090101d19032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 704855008 1250 704853758 704853761
    0xc0b040617091e150c2809120204090512031b0412030c0309031a01140d05070501031505040e060a05090f06360706090b3f0a0b100e010c1203 62
    0x403580d138101c0b0841e4106100088201c800184000105103018131010f031940f0030900c502c10100c03020b0100103030f103905080181e03000b8040e9403200e1910041c8045200310f00368a58520340101d03c00a86103002000041c00280e401d040d4100a4003444141d520b4103051500e004068240b00c500006418020554094000c1510505488000d56413041d00114413401c805440c8030710340824041ca0080a038803440b081e07010320b013409403e00d9203540030008007816410003004401620818100308111000c2e083c011401d035455020380500d5101e40002812603150083d99142038801c00360907071101c1c2d040700c000180c1e0071102041c116032090042c01c03002e0014038151740c4036815032030012914240b0300c6560004101c810001c40c000d011a20307155156400592034110100d0300d4410030406410002c94110340d01584400c9803466000c008101d1108410120100000281180c003200d80712030591ba1002030100e9464400c0700c444010601e0701d003c4070f540d140d54001030664500705030003508003120b00c000f001d0b6040c400d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 704856115 1107 704855008 704855023
    0x60d0902090a1a040b01210207061d03030a0902010c1a0403080703020f09040f0b0a0f03120f0813050a0c1508090a021c050304030c0b040617091e 64
    0x800c02040000c001c5d1070711080c1030001030000200d2440103603041d0036160040c41000342e940d00147c540041199454121400401d201103401c18a0400c000b0940c1c1e80309005460004840d40319000603544545804402024610700d000f5010f46080b01e290210700413403003500c9168491c0c954840c194164001c00801d10740081003070011481e01d240c203400a0032100e40b0400009008064100800c1042055412064003184144000c2082010106c406104140507241c02c0b1075005076403800400400300500351401c507500b00e41910091043c240800303a2420b5102506001c0b066a03003040003100b1407103903901d40c0411104c80006420703060110302c1e0780805030b0080034006034032500e250041c10001c1c1e5160135900c0748014000880010081c6800d8006011540b101036207a500d0322030010910b98105030b1443d0100b40c0702060002903000020640c0320f11016032080780d00d46001a081c5442c1024 = true := by decide +kernel

theorem cover : BRFrame.Cov 704676258 704856115 := by
  have h0 := BRFrame.cov_init 704676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 704676258 ≤ n) (h2 : n < 704856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
