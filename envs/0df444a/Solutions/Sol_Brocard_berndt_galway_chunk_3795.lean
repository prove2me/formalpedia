-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3795
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:41:49.276013+00:00
-- url     : https://prove2.me/submissions/d0b6c55a-7298-41ff-9e1b-ca94ff26dfa2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 682374100 ≤ n < 682553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 682375350 1250 682374100 682374149
    0xf0c0f030103050705040f022107111501030b0601020c03061f051302070303111c0b1306080a14070e0f1f080a1104050708010608040f0519021018 64
    0x1150010002081a2656160701d007030f0351039040520599104070704244040265030560310032101c0110f94040d028201c040908149008040001c0443c028000e4075802005070345c4003408000d081c054030b4100c64404d5070541c90042d00c0c040010709000d046602101100c04952400900150869402104c030f035081844124420b240c69100e030030042d0000302055020085030b90b00d40142000c54440d071401d10800401da0700019003805001504010b60300700e100381307048400c0c8540c0410134407540076252503001c80c908805041690355552007406d47d0f62010101505100700002c43c031900c4031100002d041400d241c201920000c0001500c4070307442d80e5100300455290100040342b6846035a00944011086a4544209072950309000b000d440703001c40001d46265902c0c25114081c0b20710707502c1c0ca88103116401e00c0b01c1201d0f40e00f401002290100640e42d407000c00300d64200608400d15031407098101451906106000342e1b1048081130000744145d00381c00c1642280005588070030350b088140340e80c859024084490 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 682376600 1250 682375350 682375357
    0xc08040818030a030804112b060b0a03110112090201083103050d0c03020405030d2304080601150e0f0609010302120903030a0606091202090c04030605070e03100b090f0c 74
    0x2942c140300300c001503010036030812102803240c0c0c000c5503028000007490b014081a901d0203400c000c3d42c20504e240c035000d01803a0012402901c0d0242000254401c2240d01056a01c03d0341d81064400d1403640003100800c0d07030b20408004042c0d40b66101488284a00d0f40060040311001d080b98504600b5848502d40d001505464140510f04540c90180c2215003801e01400c01c0e0302c082040c402c86400e040079050368070b00034000c0710201da401400506103035101200448a0b6112800c4001d2000c240c0f1a031550490b46800181024007580000b5100552500c00c19164018000a0300814030803005200c01480c1e44038440007001c1c01054801c5940c5200c040c004070300a01c500200b940381c4c0e43c640c0044c8604074400101a42c881c1c1c14542003000705036107415042d12140880d10644040004031222000141428840d41d5000180f00c0b02c1107090a4403541e07482c0c1030300e03411282d240003e034080e04021510b00d4100700b8064414003066007000350f54900b90104049050080c00c0f110038000900100da130020604044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 682377850 1250 682376600 682376647
    0x19060b0411121006050a05030c0906070c030507090c030506030c010e030c100207030506010909080a0e03011d06070905090108031210030c0602060f0a05150f030a05030a05040e0a0c080408 82
    0x61640d5080c2d0010030082403402a034400111410820000c03507064060030841c0c500702c0c0692101411035172600385000c00c40d8025504a904a502803040744c000616140007031016510440c0640440b50030160071008a03180b2142c1841010300300720500c159610040707038001d003480c001c1c0f806100810380000464030f0328184111b42ca801c250707000c1020042c5680800c0040a9a2265080c0c0e11241d98408200d020380d80c01d0710780178080c44010000702200030f008010020741d00c0b4014002186481401c8160740040100510003e92034020314100004154402d1202018180460384020700d035042003540c90703582c015042078030340100380718003c07803448541c1c4024807000b594803020880245440f00380003525400180e42c072000c400401d0000c281044900c1c068140314507010030a4449024000c410041d10b15800d44cd0541c15010707062505012502c24070003000020083e0700c5135941c80b8a842c00c54410800000c00308070300c003490b080000e505264030a000a40080d08003202c2529500107d03114605003a88019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 682379100 1250 682377850 682377881
    0x103030c11040b1903020111010e0601051e0a03060b01030c110304090f06080303102102030c0f0103200a02070b0f0412050f030309011a1903062d0e06060319060b04 72
    0xf040c0e002d0011182954241c1b8401c1c1d030b0380095181c018940741e00365007003c001d480041e0407005c01400391303080c6078200c4503611020391808030700304c4440c00100c0c60740e02d0580c20640344c140d00c3c4d05003074032156010b00956016611528010b1814003000405a440b401280500b021142e1680c0040d0f034006401d0300400060404002560790301d01348500715036003881081c1701c0d040d8a80c0828807815980c02501c1e840212854002c1c0262890403007000400003500b04003102181410740d0f8007220307124147c841100441680051500030303900c4000316806403410a096026500b0380300c0030030905090307c0305c01050300c2c00c80f031040d05024200d0310585089400c0190300561095207110200800c26006015080294240300c10148a00344041b11070034801c400d0b0b041d46421160a00c403401c1040080d1a55018025608414048001c41d0003420f0810610000790172105509507112100702c8890001401703030302d8006808800501e51290a60030800d98a4080240074010070341d60301100440740c4440d0003909100c0755088 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 682380350 1250 682379100 682379119
    0xc1502210309061e070807030e0d0f090b0c120a0918151a2208010612020405010b1e0d0605040f02031006020f030d0e0109021908010b01080103030c11040b 68
    0x503000c9480d50812903054036284030b010041107002c58081c030244503051910b0804c2070300f41d403001d5080e21142000b40c00407007010395402107011001020300005c02c103000295203c580d51104200b00805da00310540001010050420254118a00003e01d034402502a110070b15110310b41d12809468a002560010440c40507400a207062240c2640c8100640d41450b010340c0341c43c58507280400c0b091511300413020f076100010000d1600115003400f03511441c01c0f003050031030280307a1100b101c10309403244e590043d2150000480120114501030040b40d0140c036002904c00c0c1040e911000e0000c80180e80c044080e0b035001c0004210401d5107039500074001412018005100402603040720f20000d6008a5090280c90107045000c6040b61000c130350b20a2a04c1c007800114103020410074084000d01024055044944d680c0d0143e40050710303040e910700740c20390b440d031038800406140c154081d0079284510300f801c0c1000107000c01071000a40105502503002d420034160240b003200540400d00400b0000c5696903c00d5002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 682381600 1250 682380350 682380403
    0x70501020703050318030f0d0902040609110c1509070e04030504090c0e100e0609060d06053109030909020c0f060a1b08190e0a06050405010f05010e040c1502 69
    0x10020750048029071700321090803c150784072644030301880c003100940280410202c00340801079007042c00114001440002c03c2c41d5555903003000c50305221005d02c0034820100780c00e0b180c1c54090129000d1000c1c9048440600e1030800d094503110300e100d000d44c0030145403141c086410306105000380d8004e40041d0304100001c108056016000407a5002c03224411040d0348a208802c41c42802c45401e1b00102409071800c03d256903040000a4111091020180da078500e000a6180d449030300d09080140300c0080000170701a1890003980485103042e20301c074414100740d102000654040e02200889241d44401600e0b040060102820001e81f52004886d03032081d8018000c1908117a0311036400307440b1381907011040d100382010035901086c00300c46800c0401c604010000b50020f154210100c006565000e480715083d580c3e0781e180440300203135000d031940da40d9010001b580d51240c0c81114003524170003102c64194505a501e50390084440c3c014a0b14482c0350340c18940000d8002c0240b01f139440d030301121803020480d00f0f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 682382850 1250 682381600 682381607
    0x809030d0f15051f032004080a0b0601050c0d0f020f060f0601030e19060c0c1407080706090803040b22030f0b0f040f02040f2c060601030c0c08090f130e250e0c070501020703 76
    0xb45200b2ba072040c09100106039550b02071412182d2072516400904008110380e40140c40c0c16030201039802c1940100301110a80710010701c08684101141004d03c0c2c084e0603c03d000600f12004c058022049511058141e40349003040039241403440d5000a01040c8a48001c0003201c0141c1c07000c900502c000008000c0e60022036002c1030030415140c501d0100c403200b0f03a449008030303941d41c03541c0700e1002c440e0401c100030701001123801c00074075007802d850001361003070101e01e0440c080881a40e8030a40300c2c6401207162070208031010180c15040000210f40c000c80c1d040c1070706c80d901000c0e4440b000a00c2580d840b01c2003060805180c1100c0a103011264042000d03082c402e44803030700d4120311101c6684034080d5500140007980648561505d2840c1d50f9920b80d94004181c0d14000b265005900d09a802003490781084941d9881c5618400a01001c0b00c002c2148400200100e180c0030703186141c40b0700022240c103001c001645440c1d4890895081c04807400c90754582240240b014861014050015400010700006040c0c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 682384100 1250 682382850 682382863
    0xa060806150301060c0f06090b0c0307110c060405010804060e0f100b03070614030a060803030103030c140703030e0607140313050a1a07030809030d0f15051f03200408 73
    0x81d03540c0104003094000d40442403100740500c01c0031441e00ca503000041004e40b82500851445020300003500141074960303a5035500300312913001124800104004429911001003040c8842d010b0042411404450000380070b80a00d0040318100101c000002d000c3c0302c2c0c00e810071601c11030840e007a5080b03400f0101815450f02039010114042d507051484014641c01d0011340340c0121103081e51102c0c141c0a10018110542e80081c182c0c40e002511914042000d2005100441c000c52194442c0706c0c2d140c03214540000521024440e039220354102400400211741c0145030002114021981241d4565061401804a0b11040da210000d40701c041001c500c041c0c03c0c01d40407029500221000c21001d507980180d0008106401007510f582780050041000090080d100d86800c1990744042c0d9003005000002a03003180c482650140ca40c54581d5440c1c2c01c2141e50303070168005414241c0d480500e028501025920000703c00c0e0079070381010ba48189600202c2c42d080d905072804a824000c040c1d88941d1100100c3c0c2e141b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 682385350 1250 682384100 682384111
    0x12150702073201050c10180204050a020909060f041e060e0609310210030c030c1107140612090a031d01020a02040c090b04030602040e01062604030e0a0608 68
    0x70303410114a10304000702c11100c003045004141452440248200444480d0049203070700f140391180c60003800c200071450050b6004c90383c295a1030304e4881c841d030042100f80d0b54050003018189204100c40e01050305c8091000d50320010980e0180c0110b071801c0c01140c014411003288804541103c0454040d0322402e8110740201d541200f1121815104c20007000b801c6c40f415180000340100b1407000b9910070445c404d44424800000c2c1201c81d605141d5004a01c00214031440c000010b940d81c0c000d00d500da500361142d2201c92040713207004090000f22621040d070b030f40b07018042c072507a410355810141505d9984204860744406014204040d9080104545540b85620503040303001c144d020b05802244601a03041d01082d040590040c070400050390203000c010140e0401c40002c00014940120f0130b440640c5c02000110f12030400140c1e954a01420007004072010703044082040700e2401c040d451550344440d01149221780c12081c1159448515065960140c01c2d0221900809015000208030340c20102c22031007238 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 682386600 1250 682385350 682385369
    0x15060108012301050c15010f05030613060b060904021b06101401120b0d0f0b09010203060a0b0c010615091a0a090b160f200d080412030c050a12090e0903091215070207 73
    0xb01c1c3c489c0300f09034031000100c0b00420320480341d40c01007000c81c0c0284c0100c50741c4a4042d04540c80c6c480b0f04404107003aa8031103400c0c907800101a0b403412a40038420170040d40d0242c10103105108050074901541c41c038281203501103040095251007101c48445561000c3c13119440140b1240c1048190b142c042d10800030520191500d00c403d8000840c6581c2c18000c6034800c6a005008400040c00e04550106540000701360110540d038072140030030000390b883c8620004080548a20348103074a8440c645440c5203d18075608945a0140001e0071016080704c4084242c0303400665858980c40356106411300b031140210080c0038503280c0f2700008140043d000983d08802880300d452030728071810000b440b603d800c134000300801240c3d0405c0204555442c114010502d5031080c83c203a0400700c03064484601d000c03016603055442107848203980b940d450b003001201c4000d0148130366144031858030000c00c07a01e03400b60002740c030b009142c598201103501c0c1c0305100c002201d030602c1650b02c81c0c07801c003c1c00003542c402c080d029079040c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 682387850 1250 682386600 682386629
    0x50607020705061905070218150a050d080714070306140a020903070b031e010b0a0306080d0903060903050705010e07050f030a0b1618060215060108012301050c1501 72
    0x1880450700805070b4402401c00e900d8121154155000042001d0081003001410b00000005070f0300c400084d050681403104d209650b003003030400b14207442054120a84034440c8211f041144d900c64004040e1102d402c0f403942a2211100e0500e2040c0c02101d0380c2b0101d06000c0c05d90044100403855000480c65031292040395215601c80b0030003401c81c07240780521681a0701000c03081005080c510000d40d4810fa10070711043c80a040340c4080d4012550a800007054a84003240408405034140300b548001e064080c000d054860b000348020f8808612408060300154590340d488052501400880340d1955206001f000417203c0380f51a02e0b21781d546130284a00c00c3c0d044040700b103207a245c005804012142c216113012402d4407a4010100c038040c6824211060002c80040c0c0e01595030814102001400203402402014421030040303184884002c11407818011080010b008042030b0030480403a04011018003024018101d005807014011040361485910805000403050107030540040d040701c00003d0003103e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 682389100 1250 682387850 682387861
    0x1060603050c09040507030204050d1103010c0215040807021c030e090603030307140c1c02071a04150c1a09010614041406091e1e130b0601030c0201020c0a0f0506 71
    0x3070350800d0754000c400b081c0c207200040742c0340760a83c8800d8120b140760900520305580e400c00f003a07040690b18000d030f41582d003c00d443d4105040030b001d9010482041c0c8040c1025001200d0b840035511005080545180804188441152a03128101440ca009140c00003c3c1031034a1074000e040c0c0d924100000d015202c440003140e01070074004240e900030b5075039131281c4404c0c0a000002c00c01d1504040d01c01301040c440d0ac1c0e105124224207403043c03c03480c4150380c0070b002c05900f4440010303a030f04483c5944020895007040f0401c890010745890120b100d00c03500c0d02e9029032800b410010341c07003100f0070400d000d4501c0d64010705c0207140056104004440105050700c249210080811084406080c0c508180100760400a03005240007880d4a5014080c51511244903044440c0c0c1307d1110b0080340d42403405603070850522000e07980341071103640c080040c240580510b9041d50303c0c10405200030300307110306041d182e07a51601c6145c001e4058901150003501207504946423410207080c000a88007003501c981c000c240101d0b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 682390350 1250 682389100 682389107
    0x403020414090d0e180f16020f1e0a0b0f181f050403090b070501290d12050f0309010b04150e010e04030917060106030f090f0f0f0f030f02010606 64
    0x38462a241000381400c1c0050000c203450402072a1280b44d8000b1481c4017081000707618490890044141c1d0401b03c107189815a80e88120030a245480001d40d070150002c1e06004c1d80c0020360b80c40342c0e04c0c02c40700c5961040390f54003601e141c105e94641c01016000004104407515040560192203224914040385064000f40c0b081ca03100c0000301e0301050b155911405492f4441d009804c40390700705101c0e14082c01e5080d51140d4000013600540411122a51a000220710b0031100200518a84442140c0d5800850583e0b000410402144000501da84480d0100384075190050055480003181c8424550b070f04e290000c2d0050003000c0d00c82c0801d200381e01c0c2803082600903610a80740c109030394030301241c43c2540c2d0070640141078a040041c002c03000c100d0040404240d88891001100300303503203d4001440c140d410a01c01905031004000115400c1d450405904041840400c0c0c001400d50170040360090328a0700e090080c1000f083c100013400b6000c4131078410b810180d0200b0b2021240c1260f60003082039640741d50303007203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 682391600 1250 682390350 682390391
    0x2150c07020607141507080411010f0f030506040209040c020f071410080606070204020d0510060810061b290105030a0804091e0e0a14010b0102030a0f050d06030804030204 75
    0x40d40082d024404400012144050304c030f80d20303001104032030312501d8002116002d000d0407521240002c09100134801088444c2c0c415041c601000d080820300310440700d00c01040310003441001410981c035a004070740180c56a60440700b203c030002d0801e10100c042468003a541d1203c02c0820300c858452444000303104d503003141d4040c2c4440c40c024132608012481c202d00300c660010240180d41c0c4068200045001696980300401c88003412460204103458948090401030005520440c1070000e5941000340c1401008030001c1901c0150070004502c02c00a00300107800040901e00500c48400c45603071011110303800c803410240c651024001135050b80c85501745034840150000c0100a0b0720188000c0c04082c01e2a00141d5000e80000301401802040c00b540000f81c0340752006d0200203401003140030003440340301740102000090f120028000c450080000035680c0c0f10700c40d5903100304400c0390402a81c40d40b2032021907840c0008040288041d688a040c1401c95174410f1100705d01c240c0c50080500703260100e4803201c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 682392850 1250 682391600 682391603
    0x250b03090a0b040302190605010518160c1109331c0212010606212702011116060f0f0815060903060103060504023115090c02150c07 58
    0x141c24040700d030369600304044201810480940c0150640c121080f00088034003000f036030080c0c0f170114080d450041400aa100d16410f4100b18000d50000c100c0c0300600001c0010440881c3c0c0f902d07000711070460910340d6803400c40101039030380001e0305400e00082e21001085410489403144c860208503200c8108582c140005000d400e030020800301e01d20f041011018490400a8009414102d80c162182c6070b10b070850702a904441c1c089034001c086100594403862403040141031500c0c04101d160200c81d420a84008190f010701b2080504103480021648505913650301161250203c444071407030300310408a8504540103c01c0021809240e40003c184903a402214205503a00e442c402d0f0749600c04080c440c0c4a09000031500b180080003c0400c41d101001501d00071805030300000303a241045e20410680b000c0801d00010000407285105030808100480120f80075861500000c044c40d205088c01c11045643d03200f82c041710b00d000d02002d0740c2c58000c140c01101c0c20304100d000c2c03480e07564081c060900b03016a04d0f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 682394100 1250 682392850 682392853
    0x12050703120f0f0f090b1204031805130c020f06100e16050d0b0103150801150803030c0d1a0d03020d08010609120807060603060204030c0312020102120f0703060305250b0309 76
    0x3840c12070f103009810110762004203180101c03000740c031840c89192a81c0908a20882c442008082005050340418000d0300d840341c0507022070181e440c000005208000030303001043c107107664480d42401d0074020403ca801d00010182624601d10b84540041480c8106200d048031071010381000404c1145007526a0010841c16110581040129460701c4001c3c112588d0445c113069840c2c0d2010600c000111004000744040d100104401c0c070042110b901900c41c550000101d980f09209000b00e00381c8000070b449074640452320005000c40d8481088050031001e808403a0045140c1403590b041c580d000ca03800700c0040070f50b01e800e502030b40da849085904c0a082d120340b82c214640340a83c2000945000c0041220b5805468041106916601e40c0000c0742e0069000b21050b203d004020010488401091840484540000c50509a0200c11001c0b811001060103d8a018120025903454020351109001d0340d00b100481d844500c5c080202c05000c0360039400d1404040007648001110100344049a00c204030400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 682395350 1250 682394100 682394117
    0x3050a081f0b0c0118020a0612090b070503250e060c031312022112091306080d0201060f0b070206070c12060c0e0105031005061312050703120f 63
    0x2008403480c02000e0702884201e501c1c00038500c41e0308003603280200a09040b0003503036680c0740e20030039090849090f40865803484845c40500005662505142c20031281c46040c080700c91841c0c4061080204002c0400418080d503050522500b00c1c0e05c01c0280d0f00c01c4c8034600c501940c080030210164180390714107001000040e205030504849003009805840f01c000203d040740d0030a01601e400e4a006042500301c086110f07501156202546003403a00034990025201c00c013510f2100e81d44159032103034841c000300c581c100da001a00da00300c3c1c0c4a1074a0f020310108010001c02246840304d01050b103409803902040015030a041c00881c10003400410300e0100d032042d0060780d140030002c0c1c2c00d02a00d034001130015900c01f945032500045100300c07441d019410354481d210018801c0c2c0140d0010f05003070824441d4904106080c030800410491643c1030304180e48040325401c0c0c40d20f00c042c690095002c0650031100145d00503030100004c200d0b002400e10107891140a007021b48560001c1c0840b56141548441c0001a02c081d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 682396600 1250 682395350 682395367
    0x50f090406110c061602150708010506180d0c0f0b0c03040905270f060114010f030f020d0908040306201c150e07020709180305030903090a0e010e0609040305 69
    0x207500240d002c0c0c0d4814490b03400c094a461502c1d04040b0115640b00c501d0980c4608124a1641448406001400c40026800b9801d280da0000c00f0b201b814002c0c64003410000400c80034008000c41182d91210f0028244050403000d8a4010400451807041d480b000d82d1048001c282386440e2415a25240100303c000c5d03040900d000080c00103040043c200c10200c0f90303482c031415801c01200300d03200003116a0740001c0c006100d65000982c0740003c168030846200d528109581e25a80e400103030042e1005042ca40410900d4900003900024170840d2060342c14a403900403101e04008080d0b024100b1280225010880755981d10111901544c588404440ba0744d020000541c480381080886540c900000c0710000b141c00c1a40d40403940c10941d900550402000b1808000103181c2c1048441301070240c2160502212242c0c400498824105070001020701a020000608540040040e126500c4000f8114000203a4403102a07480c90020f000700c541d584411000284641804d1202078001c81e4982c0d51146060389a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 682397850 1250 682396600 682396613
    0xe0106060507060519050c04140f010906081b030727120206030912160605130b1b12130510110d09030201021e03150102061614070606060315050f0904 66
    0x107040030b104100902617104201814031520b8420905066080da4440c281101e54200c3e02c044200c0e5032166642041a02c00c0d40d0380403481d20102e8550307007400380b0143c48030441c08505c1240c1240c80d90301541e01000308840d859010906c0c0300134890542c00c2410450411a00380c000300703604e00800c992030a482c4000401410100021030b40030310640c01780e9040c0220f404488100d40e00ca4802d4044400500c1c4a91050210034401c0540019000085155804c1c050f91240f85190300201460b13000800d800b9030b010380040d5042100d4600c41d6640b4801e24502d1b000d84800c0b9038a80c030b8003007038035107115a0b00c801c10300d44054440c0c2c0940c0300030000d825041c0500144001c02a100c80c035400c80465400788644142e407d190307440801c3c00000702c00069183c3c0b400951304043c0003280d58615045502407010b1044a01c4002041001206540790101d1384145400c2000c542e40700b0508001d20182c80e1980004405600d58045528901602c803841c0c0c0f15591a0104500056081110b65000f010000441c002508 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 682399100 1250 682397850 682397861
    0x6030c050f01120f0515090709030311150405070306240504111207080906220602030a0b1302180907021b0f04090b09060a0c0f08060d02040606120e010606050706 71
    0x1c140351002c1c4043e03442c0c0c0a04140ca580b030041510351525001482000090710015252030300301550121500c1ca4040001440f4540522000d0180180c1c90b803026040032080c0441059441c48040b03a030380c20b08007403500d2a0303190010b1005662813807a00083e4243c050704031120480c44070300f00088034030b8542404100801000300d07158034178038102c0410140504070841c181070b07881442952100101c0d46444464a81000d000a00e442443c041c410410b1005c0800740c11044034041c0c00181c0141c0385c4c0d4a43c0000e070f008140c1180c4141d1b102c2500f0101000561050b00280417152503c0300b5050b503500d05400380b003889102a28500c015800c15a85042909101042041d421400030004026840a40040350031a01c0342d2400303a0303a0001400c01c001d00200d04101481d003110b01c00320108105014608020f10f1081e200c006a020010742d01c010a6240e980c0d004070705000c50b00180100001a41d0b04805800e546402a00200d02e07070402041c241d00003010b214100071070348562102468a001c2ea0b4410f4000c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 682400350 1250 682399100 682399129
    0x1e0c03120f13060c060c02010507020312130b040b090d0e060403061509180209060a06140f0913020903010c090e0a0b01020f10020a021002031003020f03010e011b110106030c05 77
    0x34802d22000d41c0400441d0020301c0100055100c40070610f056040400a8548105004056a0501c0b090040b5190300004076005e04011040070862919a950607901020183c0c0000c2c294090300400e00080c400c0e0000c0d294044d4800d402103e46508001c2c00658030003421071820b50b80f09905020801c04140907130000307010300c44030a581d00e200c1902e0302c00c550200d948915007654004066a00401141015424940c0101044858040d4245407601c005e046402f10303001007540d101c020917000d080c0040202510f800b503800a1203481c0c421109206040250401011144250f003001c0304d8001103800750207903c00f0748102803031050140c0e654445401c0a40183c04940e4111300c00d0400c42d0901340e000703001c031240490050b4400344c2c2d1480810070080c035184101d107c00e0005481002402512480c920703148003100e038103507154044462240d001030300400e81c007882c51016500704109014603010003031722201100a50340f1588224144000000d080300d507240030091007204407400610403464002c0a008664 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 682401600 1250 682400350 682400377
    0x180a1e03020c030d05031906140f180c031b090907050c190507031109090c130605190e160c0609260c0c180f040809030f1e0c0312 57
    0x2d1190003003482c1c43ca004030003500280d03006c01800050304101c554191800c6500c20705025250602d6181880c0140e89281c261040c54445844c01c060749910164032010b0219401e5241c0307034030380301810348002d034130445880c040746c031107400e00d4013920350601c0507600c60420141c44100955035464055407158482d8080701d406204102010700c8801042068a04243c13107030300900f54151941c600090700540e2212010b105600103010002d0039140007512303000032142240e00f6100554089035520080590b5041181c01140c0019440c810340c40e00c0d140401181d90021000358070340d490701d0350500c61805001030b42c0c001a0031114050003040c05504040101405642c4008101420350409818641099600c055083d00030801c4180300c042400800c080c03101c140d44106601e038022014000d2104000c00603105180910b010070280250b0702e0130780c0c103610000740458101941e5000c9507030303450b440ca18000c0741c6d0b0b0103040e8130058040000304164203003c1002d0300030085000c90040d400c1e100e42125521100f43c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 682402850 1250 682401600 682401613
    0x3130501020f0a0e04050108010e030706020a05040e010602010c020c0307060c02040504050705190e0610050f031f1e050f150c010b03011a030607031b0e030f06040803180a1e0302 78
    0xb6610007032992260b0340d00d40200d01502c1409010a0b030f10140d02c0b802607649417140aa40103103010080f5128958414070043c1c1c0c1d00504101582c0601031071f0400900c2c0b140210011a0b0f03a43c0540c03041528100d90307000c44441744e9401007010360340c030100d018250009415004100050400b07400c01d6030082d1040007560b40040c6c580002c60300d036040090300c1b02400ca20150003048402c2d40ca0703503015080003040d600c00034500148240a8001d1090441461181130000005900340e042c050256075544100c1072440300441d0f4941c1c10b011543c5a09000040700340304554000354a1030404481d0100e0761018080405070301c9000000c00c055003003089041c03159500d40448150350380d801c0c030510a13070182c03580c0e5912070031900606062600c807005200da81030611f4042d40030390391666920800f14940291508940030a02500840e0600d2080310207000e2501c00c1209000070019454080c51094141c80101050301a820104035a41c00203080040c21440302066014020384d507001111109600a0044402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 682404100 1250 682402850 682402867
    0x3031b0306030209090a080f09030a0c180609061508060a0e040b10060503040230070e01140d030c170f070f0b0619210512090a0b0f0313050102 63
    0x401200045a01001a80c0c8103800d10452410b8a0a0b0f900100350000520b400421360303031802d000b84a1940052508007010a215202c0e6a08000f6240b030a41e0002c8106400356072004d6045416038015010a1260700703160020030014800d05c61380b8100c454070110018010b00c0d16109581c0403501030220341d005100340e200800c1c4005001d0482d03000b14030940034071a5a1416403100c080450080e00054200801001440b02584e1011002643c00c01b00c0d000d40a45900200c42283d848801190302944a00500100240be12042d098182c100d5222179070070500c10010004120b40d42402c0d10004001c00d40d0035422001040000048102c00701103100103500e000580d450900e403503040311000f16415181c1d96000350402c9a06082142c100c5030684548414581c8142c0e00c0f4407001150080d56901030b10760a910080d411204105500240c10000f5500c800700000c242c100294004c01e0b0190113800203410020f0526131700702c12a2000080100001d06503142e01b10010400c8523103407015500c0307640a100260 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 682405350 1250 682404100 682404131
    0x1170a09140a0809040c080112150e0a0b040210020a0807080901030f020408100b120c09040501021306080103030206061f05090f330703020303040f0302160b070b0901050c0a0c0303 79
    0x2c4018020341c410360720f8201c000108000d076a040702d03004003040780b2400104001e50700c01c0d06110b400369101100c0b101c4441340c01c0c45600244090358024a040c804d00e44030034244641038002d54020b0380245c6403d50320240080c03050383d50300c500c4003008202d2407003000310b500810a4500070f03200032001407501044040643d0f80c00070590f0400d400140c040e0300311040c1745100c0c02c0c07a485030200070207007610342240b2409200c9146444140c41c030724a03070060340b003100060100002941150683c0310741e0310b0590111a16080000c1504600340401c4015210b0040071640d81e00c1d00804035200440312224078000580c40b020129503d030450084c081c1c2050400401d41035582e64055500c038102c0d011100c0134031120110402c1a100781c24107800403551a800c010706c1c001b00b94040f00b01c0f0b0748950480b60f186101c960b40d2404a280c41400304181c48941c040040200d6141d00c24401440c2c01402107850010503141c4c4514142200c000b61040c07540b613003080007015010303406039400f165210300900b0001a92241000c848 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 682406600 1250 682405350 682405363
    0xa080307080108060a0903050a050a230301050108010e0c07020d051f0b19360507081501020c010f111f020408071203021506040b120a1101170a0914 65
    0x40001c0790074140140104182009440d5020404010a010302c8249480140c05803040030003160802c0000202031408500610703207207148540e00748480c0d0062010f901c07150800d0b0428000e00340000c54120001555468100d07840780220149070a1300e1403e0b000b542000307660700251408892078000c04489441031400f51014005a6000442c045000c4078020200300401c401c0d01c0781d6002d9030104400600000030341d08a044140218101d155070724202e07126034407030341c46991081d125405052004024002d944542c416000381c410500802e410a0020016600c401258a91500207450010b145404900c10511802203400725003e80750040311400080c2140800c0c5c0750384201070ba40004003044090700401c00f91005100410003040c881160740d50003912850141c1004038211105400b04200395103641c040c20200304000c01c00d500c3c0b582c0b80da01c00c2da1980303181c0c03006403401a07810328044410350041038506115007888a0540065940c010380303200928040c40142c600c10354058001c8410300d800c0105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 682407850 1250 682406600 682406611
    0xa11010203090a0606050a030c210f050114010905040f03031a0402131a030106020601090510051002011d0607020c0d0809030a08270a15020c03120403020a050a03050a0b0403020a0803 80
    0xa4032800f010790900ca03080d00c500381d00a40c0180742c45002000481d540c7d2090030180e4041440e01c81400c403185a9140d403441603d0000b0b0079402582c3e8041041003015448031101d45441c60403400b20781e0346c0c2c50343c10701155402c61300a00228801d401c0040041d2003580030b030b120100140f84000e1680040000700b001c0740c0000c03c0e5440151401e2206120350103650a030b8a0b0802d50f102d0a003407456042a134000d48814041c41640e15503520f42022540440040c1c00410140101400200da500c001400080c0a42403540c50000380e1507058110054290011a160740b08e0f01c00c41e001030028240680c10b01040d516440e03804d65140c481030002c030341156400c2c032440465070f0042d1005610307440300203259009000400040c0c021074100719903c41050301d602c0d407050704403480201092001c0d400410103a0402d0100300301c4c030b540b600440d440103080341600e0000d0801e90380240c0d004400c5030386900a01104100700d010180182c1d11031042c845c0080e40c0000c0e110752141c40ba205540605ca2941c0c1d4480c030030380080d1070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 682409100 1250 682407850 682407853
    0x20a200f0105010b030c12070c02040c03020a0807021605060a03060e01030809030d030c02071a0c010f051029130b030405030304021e0108040314090d060f110f0f0a1101020309 77
    0x140320440300090065a000d0044001d11a01c0c605000242504a01c9500f40d500d00240c800720000304003030f000c2e039410036503590054801d020302684660010020b500007140003010400403000301e40b2a42c8009148101a9508510801030361300b000c0030820940c0200c04035800301501da06000c1040e44034a0f01941c0218030611141d910b40061804050408500e030005034200b510b82401d0400d5264001003920480310345030603030900e0303641d80e5034610403030710030b10000781c9684d0308248103c402d849155100f948600b9004003650701c40c0d07884884040015802c1400c0c00c4080c1003517502c4480d0f008a0000622024802107000162b0b103580e108036130143d80045a096900307420203c1000154200480c400300500714041151403502c46607000070705588809030001d0100110058609aa0420f0f41c007141c800310b2000301001820403461406001500100a0306200300c1c3c205401000008040010703110580c1c14020300c1803c01c52a041c500c8180d800048520302040744c0c1d2095894078010030b10095000c1c1802c03c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 682410350 1250 682409100 682409113
    0x130e01050405070507050601150e060705070305060901020708120a02040305071d06040203160e031e0a050d05040e2a030a05061002070b070213140f071d13020a20 71
    0x1040101c80c00200043d060040802c030750070004401003007440c1501c4155030303100c1c07555600e01011901d900e800c400c17030358100034001030103c203000000031007100316403041d412030b48140c0c0e920341c40900303074000e0660040201000388120910a16007459003580315145180050401d9680d48a9030724228940e4040c00100d40110a409890070801903d9640490705680a5186042080ca00003250a90b01a04810411000c0d420f070000c0e0b405229030740701c801c0700300400d450030114035858a441e40700d1080101c40030312403081114115070040702950110b03070400180201c6d950b580c001c03094070300c2e8903414248003504d695142294440100302c040c5004440304a80010300d440d00030700b0b002c00207000200b120150b62200404200903810030302183d1038140d041d00c0f54013600313864140c11006441b462080b10360600840d03003000003d414003194103100d01150f80d5034101801380300809544002121010701d801a680a102960b0a48160000c0c40141e0542c9000c0c0705081c4150b84800c0c108500600b8840030b0340094 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 682411600 1250 682410350 682410359
    0x809030a080a090501030c09090b0112020f04170a0308010e1b030c071a0108031b01020702060a022b02070e182d0c0f04090f1704060f080921130e01 65
    0x1490100948400c6c2020882c1d102520005013545c900c0b0711804110383d0722942d000d82c05074482d0a00d10314070312008106544580403e040720403943c219002d043c14058002000c6010000e0000e45484a690180c583e18850303400d211b9000e102050007081400b0980004156070100c00142e001180b04560300c4070341c0c6488020b60320b0501201c1c0003c4200e8618695004010303c54070f4000700455800b18624401d40c044058800c66040c0613008114004c0e500c25408106c0f220710f80d401082c4a81c491101e505641c1020001e0346803403810715804407030600140d000c80010700904080100c21500140718280740035042c1c5803070072203615042c2401c03500340c1054540703c0c001c01000c9540b419054100c0404004e04140f80500e03010405440150200c58803680e00c4002d035070705200080e50840b28903500010f04003440201021300072040e0348184108400500c80b080c4425200d071240ca4664080e81d0f5400c01780400100045048034880f0760359100c00000301e420050901c1d500c0400481000800b0348084080d40b07503151 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 682412850 1250 682411600 682411607
    0x70203070525050d031403060a0801050c04031b03030518121c1404060e0f011b0f0203061501120504020406050a06180603051015121107050609120a0c0809030a080a 72
    0x72540020300510040d1312803000240c110b20030002c0800090650390f10380d0783e6400000d0075428540d22081141d4a08001d20404d0f900c207000a00c1541d0203203100d4505201f000301609411040d911005d000100140800300b2450328154402181403c024140702d0f6040f403000107542070180c1002c00104040181142e2034410b40c1003408a0200000c4032070107410b003850307c075010741300440700d562007403044455444101187e80030701e2034807401000e01400382c40814100d2030aa80681114142030340b1034403131400001c811034694205e020184606940e20789102c0d580c6004d51029010191049034070648038440482c09860b5081071070700a1855641b64004580050000c0c0070840b5280c2201703007094240780403c900c10404505000c101c40b1601140b101c15051410100d400a000b82d1004a04a0400f40b480b082240d40401800440c1c0c0600107564039a2a8070302003503030710303841c54074141d03070002d0240842c0c5c090300e00502e070f0000c0e075134042c0c5201e500c0c0900c0000000d05042c8608800c4424210100b440d4110a60 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 682414100 1250 682412850 682412923
    0x12060507021b060c0f070e0703150302011704060b092d011202013c02010f06060806040e0a02091006140705340b0d0b0f0a030b0702030705 61
    0xd40c0040c0c03506609060b9106900155402a00e008840c001030032983c21004025500c002d003e51030035100d40e5500c4011005122905598240c002410141c0310b90385045101080c0b02100c1d4140c40c0c0300500d820055034004000c0004205980c42c9942d40d0b1030030350070f840d0114454850b41c140801d00500480d02481d1407140d60030018640c2200912000510011080000c40c1d1102602401c0a074050101c0860281907d20784420004901c1c2c42800400d408070050342c08001030b01415002030043e010900c0d07941c0200c404520500001a0200000c0340c031030b05142e0b200310f082c4901c401c10750b6410350b004c0d0041000080180e4080c940264801c100300030190380302100e00f002346800100b00d4035060740f90b00c0c0c80355607403101400d8010500448040c03140c1742102200c03040300c0400b854207110407181c0d5104600310b69080314480c45c056504040396008a40340c00a07154001080003441d081070f141c2980c8501903603c0004040b1000d41c0710800c20750020880c1041041c000d2801c40c003030030303005c6500441281070a15 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 682415350 1250 682414100 682414111
    0x3040512030316270b040f080610182304140d020c041802130501140126063c010e030613031e08010504051b0a0804020613120605 57
    0x401c203205010b81000d800c0182e00d2850428a08120800f00209250f81c91040151a031035034240070000c001903800032140a002210495009184856510010305403030710022100b00130301d000094030030f200d00020f181304510821440c1c1000504ac0c014114a41c95070000c250328200090368400810041001040d0300d006801600b9018050440350002e000c3d6980120181c000d202e151034540901858414800010384507400030007084500c1c6480c01c1890042c24280148120010002c112070075950207409102c15903200034054490340b00d80180c01c1003c505c809404140d218558102c12045c4010f900c0d60b071b141c0d80203031540e104000b982e4894810459142506414180841404113100b660380104903503901c200c41d020f203c00d100039a4030b01110041c1902c583d072220002221003012816034000819416a0010350b0100055124800c450b801e460b0203000e038003820382040050880d02486001050b4010348054441d03410300071340501703000100d01e107138125a54102c2c000d14400c042c003010380122900320 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 682416600 1250 682415350 682415353
    0x1113080d02070f03110d120e1807050703230a2d05030a021c0c030209040501140303041e0b07152d0b0612010801051008161809020d0503040512 63
    0x2c0745401c80c100102071040c440945035524150050316140c44481e540e0300302550001040d11107041d034910203480107041007246d40c0580341c2c2d40e203043c040c901d0001e2141c0c000d0b45c0c1e580f1600c1c01d201d0f40741d5044075000d420305c0e858860440014000c01c046080a0f028006408054441c03540019003407526012100009144403003466008292950300f9402c40e08407a0050060400541d4800e0324545141c203c0c004228500260b81c80c0c4410761282d164182d02400010804031002d0001f40d9a580300101404143c4030000c0e41a0000c00c0b00b04040030390040c203408a00c0158003100d40303150703845c2e008560b5600500c10560f02190b00e14030f004c41241040c0315000c1c0280f00303c001e8241c81c41078229002080351040d0380ca150078564a4094012941c2e4000a8540c58100243c0c40309066031034000341070285c4415142c00513601d03000003004c80c0e140b1703010940c504129118880f04072541c0c584044104540088030300362410640c0c0b0806000980c41c0c0b441e1414026016900840d0748a01e841e09000810158281d00c0c60366 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 682417850 1250 682416600 682416613
    0x30f0619140604091a01030c080106061412040302120f070c0b0316030209180c120c0f070b0c0c030703080f0a140604020901180611010c0c0201080601121113080d02 72
    0x10128110701c50703402c40001d540006028045141c0f082003402c030908009009611840008100082c9003848425195050002d01200e40e40e41d50a0b104000385c40c40a08103040b003402403040c1003c001401980c01703402072040700c2141e807280701854055808551142407490002520700b05204039040d09400500502e48020303c0d5140420003103c10910803514007040503000600d14809035144524003a014201c019440d0440c2048441461554800c03058150f00144000003c3c007000b01402c1074032040d80e184618a031074407500382e980f08107141b801003403c1480c040904c244034180341c0c01c1001d401800e10a0310740d004141030a5118541b01c200042a09044500744488404032a202005642d003002081c0c4000da140c20250005842c0e0346a0704101240b00c0c2c08800000440c2c551000104101c2c0c00414020040040d480d401115000a82c4a002e0302044900c00400d02079403207034104650396031503a040090303050310030300070030b020350b03100c6802d542d1814810642070081e00303003d020744d0011034002d0004141 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 682419100 1250 682417850 682417871
    0x215010303020d081504060807030c0e060d140a15090308100b0708090301060b0a082406070f0f150605090a09120f0207090507030617010b01140a0e030f0619 69
    0x16190b103d00003d03400c2000c550049286a9450040000700d108000c0c014003e035500c9005207030303485000b803000f9514a07210341c0c80003550913030030120301d07002d420301808e030345000c690301d81b00c000c109100f001500c0c10500c5075425240100d482517061800515400f0320116210074203040090107084090030060390303000154410010242c1101c00c0320125644500a20740342e200d00000680185a02e5101100d8060005207880c05c40d41d004000e28803480c4070703500d0000341000125070882d807100300c0003003660024010070454010542c060750003030550f03100340c2d28511040b4096903000038681d00b04008527040b40d10790301e0074801c91030240302440e0301074460602041108c18944445a0441200c0e51100521041d0240d070043c1500c00d010b150702401c4800750034406428146001401000310b44581c2031106004542020030103018024030b407522805944030b4613144900a00c0c043c0f5030b4040b9450009201c2c0c016590740d01902c007409084800102c64014019618101950810780b06428140003c200e16025103481c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 682420350 1250 682419100 682419103
    0x7032907080a09020301060e0f0417091e06070f0809120613142104050405070e01020706120207050f010c020d180e060a1d0709080109020a12020d0f03030c021501030302 74
    0x982c01600610041001c44450010078014803603030700440e44030900ca80c00c11283c079607004a8503004500c2000131010300c000c10304120030140101c00c4c01e00c4e4041280c4c0700c0480c0400c1403a140d440000d5004010900d8880c3e01d6603001030100c3e101c1c07000c4441950115042c81186002000e611041141c1c0b8081d1046240040031030880c0030042d20018842103100064420a0b8010002c440340480d0b144502c1514090224445441b9040f07445450300c01d60400000998891041a030f004c0d001c001a001001c3c03141c2452825542000d040841880c641e900b401010042401003281501508480000082c0810698002810120703000c0203001804041c00520451100c0c8503501c0c011903a01004034000d5403109000600300d0040ba51000186030340c1c1c580700a01d0380354407442450003000d66481c0c0402c2e5696540c101c03801e0300c484040c081e40c48000c11004000014442c2c1803943c0d0780344000c000140d45002ea40d11950401c03002101500003a40d01d446070084150100507542c00824080750f84180c9600d1903900a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 682421600 1250 682420350 682420367
    0x60503033609130503070b0a05040606051206043003050f06010302130603050601030f060806180d02101d030c031c02180105090a05030d0c1515031403070507032907 72
    0x4065800121030f03114180f0000340141e4002d07543c8050314402a081c0200c9240c0604002d503000e4428500d0170740d0016442c604032500861f46201500541082c4d0317aa40c4415840000441208900b40190341c0341004c02d588a54840000d035185440004060030700d040100d04c5038200a11181c1410720401040f8042e85109082108451a03850042001da0310400101c01400b80102c1400d042400c00501040307441011441510500c5104078501004609489550765009184880409600808603450702c03440d041d00100c1d640d19200070480201d03c030b103075034003495948a0b0481c12160342000c1800c030302101001104021090050b1020b6050882c0f0001e03c00c040b000401e1014184034000a21030101d803078544008008020040a6860b0b5082d0100040c18180c0d480308103c6284680b060000b50504080c4140f0b011082005407072461241155207100c45118000740920380d522042c0f156000103031003004124007440c0700341010007500c000080210901e56070601301d601000c2c0e02000b042400f65200121 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 682422850 1250 682421600 682421611
    0x90c030f0c140706020f040311180408030126160501080912091c060608030a170405060c0705150106090f12020f131d0a050f06010f0302040906060503033609 69
    0x2c69a4403038591030442c009105180c00b070a09203601080c000f09214080c07200780c00002c016601c25a906005050344241124100c034010302d0031030f0510040c8480c2c40440e6509041d583d0505920103182c5031201090300d44020840003506030b404408040c001940e02c81d2540e504104150f004001030004000507079400d0080c1d940c90360007000441d0000d100100024480e401c05504030408006e055203507844242c6986c04114084041428500344c0c0b504400701c1c20390135100daa002000b030311443c0c803441607a45c01a0b100c0e60040d503e6111b090b200d45032403200d50360814024035a68454003065031820340c04000500301940550407205107403803a140503031500c011220385190115483c400f00c1c0d1080d8031500003003140810340450240c00d010111109040010848010f501a800301d0301000b843c044000d94404c0e090041180901c2d4034141000182001c0d0081e6000d140f2621020840d2515080449c0ca503410019840d00300c04840300e00c403050382850b80100026042030b030b000d03803401040040c0031030543c0002070b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 682424100 1250 682422850 682422887
    0xf040b03070e041b1803020609130b1309020a0b181003060807030f1103010b0a03080304031b0b0618010b0a1209020409032001060608061c0b01090c030f0c 68
    0x1400192103100c0c002c404040c01072040182901c04114480c0140b1595603075070115580041501c0c00d82003014981e07084030360040c200c03440c00e07404a0130f00100f8860294540c110350b44034251140c10360340d454400080101508400281c070380d094010000310980a82c0b141a06550400054200284025003812078500598092845050012084004000ca40d124030568091003502008000041030754802c060300401070494002804400c00d030803145003402c2c03580c2c4400300c007000308001213140c4065584503000303091074a10388503071141c600d020440c60f08044448441324820000d091810005c08115000c04104042282d03040c490091210701c03414004000380118004074044101041e0806103106078003410503c0f00e48018640a8140040b500b04074102c039240304271080c40313808148203410484196907214003a03510381c40240b041d806140c0c40010180010800d040c40401c0d10200c2c8580249568400046c00111241b80103044510450034a110f90b070030b0002d94126603a010128200032160b804 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 682425350 1250 682424100 682424107
    0x5031c1a0120010f020901080a061215022205090f07080c0c0708010c0f140703090314010b2805030f33040602120f040c1a2a120f040b 59
    0x3450ba00c1c040080d299894429801c080c1e0700e800045042d0080c0c425001c0c20380780c04801c0e45a1034103901c03e035003182c05440b803086421403001d07000c9070721008202e0702c41e07008600040c5003032071000b00e808121002203111030340803082000420941c10400c11007580040541c0102c105400c0c80c0900a05040024042450546010801880c4440c0600c482c0004001810081060311400e05001c2d00040d040002c0101052450704c6018003110700b44200e411703041e8150b5516808900716912004d00e5003400e100f050040d075803015581e10b16219101020344c0b0014903c00301d0407841d2a500c0190070b0010a4012a000e84c11250420f107200c1030010306c2c61080381c01440708800d411100207030034081c05982c1c2c00880c114800f007420700003404115030040402d001c45a039000001d942d0b481c82c1650020341a00d00811241070498100440d5606030010b60002c0042d1900501c0c00c2c0421400e510505114114681c55158170a1808120308003084031050b0003100101d480d043c2010700041c030a242c080c9110702d40307a141000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 682426600 1250 682425350 682425377
    0x40b0a0f0203011d0717061c060e0a06110f1e090d0f15060b07020f010e1306050f090402030d0e0f130203151f030b0f0d05031c1a01 58
    0x1a00224440c254540c0210344960303455115103264804011040102e20125020402551042d483e9030400507644000f02056200e039070070312100c007507041c002c1d40941c4040351660000807483e0141300514482d0200919041c2d5007810881d00704c600040800007420002c009868005021a0913940c000d0304652503104501002d810b10b0115114808049a105001d44606010040b091100c0c586840c080d02030307801442e0000b40441c04485880c000c1c202181420f000c841d00500e0040319021541c081803500d18208051000800e02c02400d90040b076160584400003880a410310f4809a06814021501c81c0000c0c1416008691628500d60100081215400b840503050316901c40750307550042c0140c480031054100d602501700039081580c00e0000800413002d445014600301d9442c0e01c8403215048000307840c01440500740c0050002c3c2a02980194071618502240d5880c0c10f51265124000e0303000d569642c01d00d619400e000b100d020411000c161801034107070303024854003c3e5002c41840a00346880402d409 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 682427850 1250 682426600 682426621
    0x61b0206040f030f0605060d03080c030405100c11010e0a080304020108150a0303030e0f010e060601050c01060b0d020705070603180b0601021908041406030103021315080d03052d040b 80
    0x8a03001080b0011082e8000000c20516108166a160142c02d013040381343c64030b10400c008100c100d0740c06800640302001094903808040d00840d00117100d081168105241c5031010313000d407000207048401142c01d4140358200c5480030b0058100c101001c0000c1c1a400010b651265070600011b0006810440e8020008540c5c0aa0441401c00c10b80010f107801c1340c441e030303910740100076040503801c00c0d04900032520b59010045e014020746c04032500f1540504020364032000115029000101d458450b0740d21080d0004580c2c02c01c00050142c100015000340e9501050b0421030302d012100e501200030140340060000106c1158820240000e9020140d29055110840100e107044180910155140d403d41039000c20030140388000e104841e4000d10741d2070501c400710100078540c002480007039001410039802400c0003000b60311203090650900d00c426100b64544400c40d1031304040d408442e010035034440900011044c84150447c1f0b0400c800340d840c406440d829030202c980b520140006042139400350108140c8000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 682429100 1250 682427850 682427857
    0x19051506061b0a060609020c061503101109010f05040f0303030209060702180907060c0503031f0f0603020301031106040302010c03180b18040b060702030706082d06011206061b0206 79
    0xe1007807000c56010469107942c3e0001c070442e07509190132000990007803140242e0340d1036803409001d01f20301d50307407440b50601c1140e0b00c000083c2e05010b60300c1c82c418424a01c0c401d0740c82044840d10201c3d20b9110752000074040c0e5100d25205001c0c00401c1c40204207540300c43d809075040d29458a005615036031440302089040c080c20360000c1d032050440b2000342e8103a030a120020b00c1070300b15008440e201a640e000c190381e8006039003030241c5650001c00c002040c4a00c0d0052861224440c80420302c80b0030746d92905054403154039085200020780002c010001d014101280d00948202160110315040c51640040c0005046020040a010840101c0700e20f24520284850080005200d00c1e0760380e290440c1410081407040004912581c50a1234641050504406568034260b028005008080c20031030141d660940c02019030411034461400903880d01d4017840810f90b11010120651091704100c00003400403562400c0290907145080c2d010031190707a12800e0000322007140d030301ca81040100b5002080d054071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 682430350 1250 682429100 682429117
    0x20301140a0b031c1403130606030503070b1501090302240c1f060605120c07050109080a0215091f06080712031706130e1c09081905150606 61
    0x84400700a07401d4425004008401e60403030030340d1060054003014030203c01c01c5200d0074000601c40c031403580450501400035070b0402c02e200d10300c600078416507865a003520030b150021a0306800214101c0b040114400041e0303080303404c14103038500c54464640000c1203010940f1010303201703c00d40c1320382502550071510f2140265142d00e03050742d919165210000e99808a400460068294448020705441d01d980700d40e40c15030b040e556a207441c03d010304030740c117508010240c109841440200306803000600244143c4004900c40d00d4010348416280a010342404011005900d04401c8002041600700780032405070a4050341542814410022444100040a03e030704098200e2041420200d5a104650502804ca910a54683c10300c6692040d011800117001d46085822014000c0c400308031050381d41010683e00042c40c1121800e03040c9050201c0740c28091840d01c40070bc1c03004002489519028022036a00c009840c00d80100c8100c03aa41d019520b9454464070102d15801d480400c40b6941c80004032501036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 682431600 1250 682430350 682430381
    0xd0c0615140102070b090a14010909020406080f060303120a1d0a0c0305010507050406020d1d06070606031403070302030d0e070b0c030a020d0905090f04060219020a021003050f070c020301 82
    0x154a811502940388400082540584a000c0b0005171420424040702c2c00640e010300112251840d0880004141503020b604605019408074007256000d143c5c4041d00062440b6079441c001c40c28981301c4082e480c03a001d0000f900a80041121a00e2141440c8002c0d401c00c020302000243c04a44855a00d100008015211054012407807440c090195075010107081c7d9004038020400303625041c0041e603a40c821485000b026801c01502002402e008581d00d1400500d0200d4850b403080641e800648283c0c0250710403150705540b50810310034444180d41e040c5024203039a00035803800f44c1c203032000796480c0a2200791200003a1210703482c1380b0101c414840d03800146840c1c0981a201c001c1c80c03c400303490390080030000c40113208240500020900c81d503641c4003151006000f001c4940c0b128120100d02c0c0c90010000c2d200c07184c08010031001e00d410700100c10091075582c1e000d000d003004070348100080d030204a4040d404150030101070100c4404030421482d000042400c021b103a105041c804a405001c500101c00b180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 682432850 1250 682431600 682431641
    0x209041106130b120601090f120303060b0703110111030606070602070c3b071409030106080d020c03070e061c0317010e01050909060907170c04020706022206020d0c06 73
    0x1144800261141603128060404c0076039810004480c000482e201d805ca000402c1c410400400070700d40c07805900580a4503020540326100c10300b80780b90380d01c201d5040300040c241041c40c0c4031884080c85042a100d10310080309186091100c00103499014040300603008660014001c010803a044284070f0050002003030800300302d0b01d00001240c9050344140700b40040180d043c607250f010400107410502c941901e442d00d44188089007948110368000035007060305507583d0007021501c4ea504102c0048a200b0307036402403640e46501401d2504010050f404400517100c0364062100d140c2d100007482e00c030300300388500035082440e090400700c810960088001640042e201c002182c864480300596058a509586801c42c0f80c4500403025640c62007103038404101e0700a5038040c070041c044000c1c455000c14282085883c03440002001804036880200100c03005a03000542c5030080c44c032044000403d9454000c4800b50514201c070203505c80c00c18010b54020858042c0901c0c00300b000036880581003c1030f40440ca01e6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 682434100 1250 682432850 682432859
    0x60a021507031b0f0c20030a06050711070812160b01080a0c0b070f020907050c0105010e09120f0904050429061c02030a080c07030819030f0603020904110613 69
    0x30019451080f00c03103e0006010307680a8012034039101d40d2840c0e50b0300d902c841c40740e51310b6608036000c070640956548a0300d0300a42403159420006c68162074020403000429040c03d80016100d010001d0700302c10280c00100080005074004119850703d480e110800607070300d00300c083c07a40545001c5050014549420700d0004580300c1c00000d0450100c52144200340022912030804986d28040c5030002020364a141002c2c0c030060405015064000b255414020304000000045900b0b42e24260801082c40100000b041400601000001d407102e62150b51a07151801102ea0181c0318801c12901078000c03621100031408108800000f19104032022100a410100100700d09451800c182c0d91648035080751717143c95909000c1c02995503c100c0d80100205800c00240d5078445054020910b2124a40240c000000210784074100915000c52400703062aa0166070101c040e00303e5580480440500c2d10744142800183c541303c2074190071a4000c0c45003901d600d80303640010b500784101c810011428030368120004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 682435350 1250 682434100 682434107
    0xc1502010608100b0a0e24040b0303181504031a071b0f2303070204091b060f0f0302040e010b07111306051c170d1407171006020c060a021507 62
    0x15403880041726280c0301ca5544582c8140081020b0306c07500e52210207042040300c13401c035495030844000005400401c088030441c001a00f107800c180c800e008108204600b4031598504004400e10300c16900f8903c90401e07085442c0d6020324020060034066030041c0304003003801940210045045003550007810017588110b880d048680d54000c0e4400c8500c1a0400c022068543c03540318500448107c0d42c0046081c4801c1d40c081002400f08000c0a032015981d00f211000c100381c01a4848010b01000e4583c542b1032612040c00804120700240480200340c410300082c0b1000d45407101c40b5046800d240070b072603100c100b181071181400c040140c020f40d02c4103505506100402454001364200c030b00072079030500c40c481d01460f2441c04102201e4010002c02883e09503d84080c100c0010304011706860700c000a1301c42d0144481d044241080c0c0b20328000c01c032452010000b9400f02c050043c4d0103e0b0076180d4049d032500d007103406580d2310b0800c4005841150045400b000052003004945051007400c81d848025040456019 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 682436600 1250 682435350 682435361
    0x100b0712120603081e040906080307140309060a030b120a0c05030d020f0d030903090f060207230315072a050d140301140a090c080a0c020a0c150201060810 68
    0x4022460a0071140741c000712922603442200e4010300000d281070007004400c900801090400320f0380d900c050101203112103140c0300725000391600c6d00080d50b42d1041428070440d0140d0840c5008020340c020401c00b2410b803202d4040e100303119424100400d9007002c2c00000303030f07185400700140c0c041071082c8180c40c010b10040c0750f150380485000740c0c251b804c200e441203012626020310024942031039204100080c03a0f14482c1e488000b15900031700e044007180e911803e01010080d0740b80c0c0b1040042c2c1c030002050040d061a40d0801d9260030f070000c400c0001c1c480f99008252074010342c2406003040e055100000720300902404c58041e4002001d02d2a200c184c15021684808402026003a00c00b8800c1258550109020700c0c540c0d0492110000400d06680c40d01071116008404400c0c280d130001d88182c0300060404490013080816200c0d619044130a1408035480e0088409030b03500c0710219848007040780003103020b005076601940c2c0d00c40fa601c0c0c140c071092401640903201960003181144500c810100040902c1da008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 682437850 1250 682436600 682436633
    0x306120f0a030f0207060816020a290c1206040b03190c183c0504110f0603010b1e1201030b04030215010f0519090204170606030a0b0f100b07 62
    0x244048003807000c408a03a41c00c2e00d80a040080f40d40032020941c1403c0c52030822030522489d00c1229108896982d0720010b15080710303c0c022120b04103002400d450018810031542c030800310f04e42c4070705001e600b51089061101c0548990300556640f0004059500e003032000c151030580c042507046042e2014502151510290311860030700c500304803a4003d100f13041b0701459a041e10030000805011081850001241134030b80604051200c20b40306410031103200b805041e20032401801441c0501107500c0070700200c860f0960f10140f041d070702000103003c18a00c2c07200f03440d941800048401e001e45485984100d251241c42c0d00c1c10160302d4800000020001075444545c4158429420b4484407460780a901c80b440e0320a0044015480c0009000d00c41c0307060580240000401440d0001c0d00c0540d20242c40c4100e0b071040d040440d241204003880c406038642004044d070001800d0b801040c4117130f00c64880441511029000300c120040319408a060791551100d031b18090802d10869940d6900e0915021030b003400401070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 682439100 1250 682437850 682437857
    0x203011401080f070c14150403030f0b030d0207090c0c150207150b150c2103070e270405150906060424032a080c190b07080306120f0a03 60
    0x24101c0c1030402807580984031580b80c040e44500c4030b5032040701c460201146c3d0003041c485da840d520300680004040d64003942c0a510002140c101090b108400e44940748601c60090f03210042c900da10a50005014044a17141170002450485c3d4460884050312a000041c000e1401a4a4235030f5091659008040d15841220115034240000c0c10902c151500b10558661103c0d190f20004e910701c00381c2005108132081a030035134080b1105040420a1080c6034231144036044004000c101d1819005481e1144406080340c142c01500340300442030340d501d1f95403041121324106030400f1504008041080300c1100701c011659030351501d05040c0c0d4a40c0c0b9a001c8032100d01c00c604103000c2c211070a140700c40c1c6a51105e4030301c002e40c0d0f4103420754440745000c507c690f5134480d00304109072088600007020b00d103a50250070104060820a10a41c080240988140741c04c4140d484603140108000c1c030010342101c0d0203d50088089403660707030309400107140d0410314082a030076004005450300840c5010030401d04a074465103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 682440350 1250 682439100 682439117
    0x2160b0306180903030606070611130f090e03041404090510150b040302010c140c040e03123907060c1101110a050a0302070501090812070801062a0c05040203011401 72
    0x200c100c4040041940c580c61113400800201e445801d0100007002610b005103408501803480003500002d9600101440404101e00681401102138800901005080d00101406007100010144ce1203203d02e124030201348181460409694545400c0656450b030800152000d0444c40c42a850140c03000304050005030842c00c038041203c514001c10b8405032901a9501e41041038195940083d2000400910096119000b1011003e540c3c50185580303074114a0003079912a41c462074800d01403407024050320040e0a8109243c0409410f058022009412081071012214038800115400e482003040c003400550602803401d00715a00500f07181184a40200200030010716480c2ca112103018410310500000d60070070102c2e4500d442a0041c02c0c1d181d000d08000104a0b80d0703680c802940f9072069005580400c40c07a010448a03d8000748074030300400c040e04240070404600450f50746801350000000c1e0041180d40030700c0d1b090026004404d001342c100584115580c1d611482002e004810700c90034540040e030f83c413 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 682441600 1250 682440350 682440379
    0x403080108070f030c1809060608030912284815030207050f06091e07050306310302010f06120b04020d02131802040b0609010206010603050702160b0306 67
    0x40f42c08100c035003102d205150036080c0b003800c01007450888401801c140d2100c2000740821000c2c400d800007020718200941e40c030401e0000744040036180a4020900e501301c0c4181450807400700074a5030002c2d920101c4c50748200d0840c64545e03400c014401c10b12070444819102c040300d13460081030040c491045e001e00c0040d40341c1e500359544600301680c060341041030145918140704a0180d00985030306440360050b83d4444010b80762051604404603404403845e03004a00900042c0b00d685d80140b44a1640c00c0600045400d11b00400ea07208405050b282d25028102140fa40781c1c0c514a0360302d09981843c01c141501e01200c0d00b4002d0280002c8141544443e15103200029030314800d05803411200e6201000b5a090759a075002c001e0702e1007044a01f03903005190a07506041502180c41850818000441400310f07034881030050101702c0d0041105980070369000c2000c0c02c0300f13a03000102030381110708500d0042a1643c4264040b400d00040403003e180800c0d00c490045410071402026601c14501611610f041c910b20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 682442850 1250 682441600 682441619
    0x41e050f010b18250507170304140304030507050118080105070c0b07020714060a170c04090f1404260a0203030a0c0f050403080a0e0d0b0a0c0509030705010c0f0b040308010807 77
    0x152111207800300c03a2190070f1040744c00641c0646140d402070404a0030555151940300c22850148162030100600000304420051040e6400b4426502a0300850416066940d130076510651801018184510613044074814000d84404201906580c03000303108504040001900c9072440030700485840360300b00e0014080a1000582c07500700c850103007009507032003502e00074040e103940464a520200a00384da061030b0105203480700d01d401000100307215035030f50303103413210520459001c030030880200c81c182030034060014000c00c02d213500142c1201d1080c0342c4a03001c0307e51561290000200301c2550001003445074500b0340100145200d564500d2003400ba00c2d0201c031040301c2d5400d10740007100124a0503c41400407400c0c0c40e0161880400d5810118001f682c49000995003a10000e421180c0740d036240200700202c08640101b0f04075900d141020382c246614540040d0311800140100c9040100c000c003a40d040c00104103040200c04d41080c4503070042c3c102410020981c003001d0142070366901c81d110002641c0e0b0382 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 682444100 1250 682442850 682442899
    0x160b0402130c020d122d06080106060822050601092703210605041803030f0501050108130c0909050a0b011d0403112b020106060314041e050f010b 64
    0x90710740c00740013510380380d1348140c40b81d0030500044d0401c6561244018202e801600d43d0881c06500f074490744a81401c1441d0800c00d80c1c0c1290080c1d802c03031f41008001c001980d04002101e42144101030451010f03810426480c020300741400300500a8490344000180c0389010754004103da80308034841c464101c07145c00d00c0340c4454404400c02000541c2402450780d070110340b0042ca503402c0c80c0200010402a0b520130000381a00d22140c5040b142501c0c2c14000c100b00750b003600c1843c0d200c0034101000c1c0718641c07401002800c5d0210081c1040113040e01011350404000b42d4a85150184c100031a0410580035282080f9030380315410f00080f100c82d0000710002c100d00084c0b040300285009a510031088580c1c46a07070441d1140d8401030741d10000d1040401d03050060000c050207200c0c90860304100780603a4003e0030004e0035186a0750000d001d251038145c03e0151007e109009079070041c1c120020324038400003817120040550490303030f016145002d00070404040d04030640102c00c02c3c800880340b060301c8011011440350b5941 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 682445350 1250 682444100 682444121
    0x14030618073209010e03100c0f0306092903030d02040f0f0806010b030a18080a031401090e0a020d020109030209010b031b09010c030806031002040b0c1c08041106160b040213 76
    0x11003d2090804075803107181c4107480c064020b000e42d21141d010517010001c0c1c8642c242101c02248040c070a4020781545442190700a1100034070a1010a8440444101c0042844401d51024115455052280d2020401c07510250004113046603244d94616005005241c640120010301c0c080090009034030000240d883e06855400d441a03266840b600d00c0480200f03450300e0800388075652440d014011800e1480a4500525181c90100b0408036820f140a800ca50507003044061030324010f1711400711000041e1540110b98140d40c044081c01d900d00050b500d6154584c002540007800200100c1c2d10602c103030156000b060302c010f2203595050100c10340c5569003d00b41d0414001800c1072803075400700384036a40c002d40090001e000c0d5510001c19944240603640b117a040005101000a007082d4400000c02c6140314a1201e488003050710380200f40c1c010030513540980060f0040e0038442d1000c40c20f0759400111070f61401c11121090001620b440c00d000c102d00112000ea102e403030320480200615202d8000c850200c07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 682446600 1250 682445350 682445447
    0x14090703020d0605090a0506040615020a06020309032a07050406320319140c03120a1e0c05101b11030906040e040b13031403061807 58
    0x665944900318020741121615502541e15580001403945443d9030032806034551160204051a088040c007085c1c036055400540f0f452802803881c1451680403070120046944a00c02582c1c80d1a400180f52031400743c954481039944001c01c24180b00e8491700400c60200700702009603545c0d180d41d1800c1004a0b036081c03140d204000c04010640c0c0c01030301401c81c6828000306c4e9520360b50000c0d0b800e4010a19220340c00030030036031511400d0111401c7c00a41c0380c14005509100005001070b6050700040394552a403400c1e01d030300c1a0808200d117241540247c0c61424100c506260024042c1c51ba503400610542c0859400e40c0e440c000c1052034051849103014800f40c41d042803208168003c1c844104803441007000501d24000e0005004500300e03617843d074006100a11040f90201014141810404011040074003100f8600200003240d00000ba008583c3c0c800141035141200c0c0c03655940f1000c24070300110324020615016001042281e49604140c0250682105050106c40c480302054445035803021901742c039181 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 682447850 1250 682446600 682446619
    0x102031003061d010920030a510b0301090f11010c080c0a0b0906040b01091e0c030e0601150206010315020702030607091a090913060219050c0714 64
    0x8110b55800c04002166407104032501081c03260600f6003100c11541044441e2501402d52400880d449021500700c84d00481c06031100c81d20300d90700c400e1901060310030100014144121000440c0301c044020960a085040140a2001418480a40141070130f0701e202c03210f150180400203401c05201c1c2c0559250700070a00c01c1200d4154903540f18040310100302504102c02d0001440001d208540136000000c0040018170f480310f0145040030483c00001c0c00094668011000c00000c03603140b0000e1411254440344c000ac0c608020302d076106240050340044a000d0342000a242d443d16410b0740b102120451041c01d4071060307622031010080410400f81c2030001a0300200c014004031f10344043d01030810fa014071700185850300e0f41d0302090400350226100300229185050802960400203124008041c600d483c0500d09440d036000070710b8050018096038034001c0e0980d0108100404d035811035450051200c1e41400c0b82c400110300400c4c0364441031700102c0d00d0061100002c0d4609440f05009960240142028003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 682449100 1250 682447850 682447853
    0x606030e0a06050903191e140f03040203030f0c0303091209180a0e1203100f05150921010b150403080a0507110907030c110a0503040b090f0a0b0a020f0102031003 71
    0x1600014040b00c3c07503804204506c031180030b00311607800f401c8403050f01e41a8141d40013500409100b424252032009106055030024031030241c4d00111803040e4102d0580ca0707220348460000c40d1960265040b88c06417401c00103182e00d800000000030b1480759002e0fa084a21703a641400142c4110300403001281c1e000000084621a0483c1c0e000720150301c601c41e11000100c0030900b245151401d4030350345c42005141e20010038400d070700f07055640010207044145403021f480d0707280c0300114062404010840706200000300d801500d0307583e09101c10804a10703210001554000d90103083c0d000704108481540b00300001030180c00c074002c848090701c045a4000d0b103601e09040300c041041e50703680d000500c111950103a181e40f038016640c2d403051032030150055590000c0c858695a48c042c081c01340110307040c0720300c1d44912031030310003c2e00005c00c039000d85511011242e121021a8042904440a0f1070003544c014480f1a020172503004000150480d004194201c0791403d694003866401c074441510b40041a14080c6020710 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 682450350 1250 682449100 682449113
    0x4140a0b0411130e0703110a0e1c0605062115064002070f06020d0209040501080604030f0f020a02011b05031204050709140f04021c0311010606030e0a 66
    0x8a01020160000c02c528441d15840805640100200340c44410080c03070a0160000f1812495804112801e003008611841c0b00c59004d603010b072101c90000c001c9079140d00100ca884510303102082613a81d07400584400300510b84200500360844502e40610002e200c1c14412030b48003001c941080c40c100006c5c00f0b200c1031a070800044a400100000e0b00b21a4419551240c000300c0e126400f502d00985a4540d60038055090701d01158000c040b03804441070040c0162408540c1141903580055440880160340710080440741c8081d004a541040d403040c5041c000041c11440450384500c5a44282d944000310128801c098424008036559000180d001058502c015401080004490151f8041f08002506d150342e840b45558081041c0850894490f0180000c10073304001c010098061100280015450340f0f10840d24050001c1071080340c1c5001c840810155203400106090f10b40c80042401e0070b8541034100903199400e0803020700300079071078601e0000f4044d00c2445580c4148800b000900502080f41d180e0b0b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 682451600 1250 682450350 682450361
    0x20c0c0411180d050f100203040b0106050406120f060f03060501030203070e1911070f110a0b0414040f090503070b011a0910050c0c030d0207031709100c080c01020f0d0b04140a 77
    0x211550f101740d2240c80029841042410300c04210410050390341e180c1441d1544051030107900c50001d2160a0101744229500320060090b4031800b5507000078601040c008400c0034100581c8043c402080000c008802d028032904914113a038001c1d021590401d6407890f40d80300000049844401600e5581c540b01200007840d0802c0965a104258090400303603d03403280613248081340030441c2d100c1c0c0704a420030001e05140c22000b00404014055504041c038206c00c1340140603c041c0c099110f5540c40102c0d010144d001e602514400390040216601da044034a81390343c20300307000c4c0031310702207120b003140341c02550b403007140071540403001c00b8115050710f1543d58800c0e0740d1030304145006507181c0600380540804d40c03801c002c025480b03203103640200b080c986141840f161056054004224080c400c106917440ca44812540e0000140e042c03610f8030000d80386052605250007150340b6000350303500005401444040202c0540250030032070030704100c445419820481100c412150116202c4645800515207040c0e95109 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 682452850 1250 682451600 682451603
    0x9060c0405060f0715022104031e170a02120c040f093819080a12020312160e031501050603060f0d06020c071a0708030a0e01020c0c0411180d 62
    0xc0c1d814418941d03a0010317400600b250384203078540e020407181a00c0c400f00441154505000100407490b040c50b4900605118800900c003074002d190381102140d062080d0031f12044510078000a0785282802e06402e0301a5104280702c1c1020312111021511800f4444100c0f021164003045210a0341d00c1d10384050050440c1100031960000d40c140444808a0054840d00d904408046450300c21102803080200481062098251482001d0070500000d640040e00395035460700a13203038076100c03104070404038030b14443c2911452500e081c1c01d080c40b803601340454810421402c1c6850b26802140b00d0420326a503100c0f0549039030613810840d0010805401d2143c02150030440280050b00010409008203454142d18401120619030002e50560000b000b40000300262150394441d04182c490607040f131109008464000e0030664002000c52210951544880e2072244c0c80d00094cd220340100c86034544440903060f42c103009506002261b02c1e0100414202c0311200c081c0ca400b000054482c106001010048140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 682454100 1250 682452850 682452877
    0x221040305011e06061103070803180307030e15280207150c0b060d0f060515040c050705010e0d0504230306100317120f25050c0609060c040506 63
    0x10100204100380200fa0701c0c80b015000d003850440201800e0000ca400562041040000e50403140c03108a02c04400c0f1050150010481620f940311000c031944c01050701c031681030b007a100007d004000c260704000899014241154020301040d90020b80245910951510840c1c0c54000d1840c09460144401030800d185014411609419140c00a800c030510403268050046007551010300c041040d6000280c2c3c1c04502aa00b0326010b81250f0307181c0c00c0503080c400d0010702c266128400100718504410b0442c2c000700c002401841142e51a06018001d9401000d0603201035091030414144d403200020096a280c4c9c0700d40e1001c0c40c29281c19080d54401100d60300011503445e818a485025a404119040c000d2191700030401c146440e5252118000c075880c1a0b40124800500200c603401c3d0440010660041400803000c00e10b9840b0710b00240c92288185490324101300d46078003041941e03440806091440d4100085406540740c15245a07550a8100c9801c080d50000f004184014144940a0081d001d1034a6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 682455350 1250 682454100 682454107
    0xf08040318062705011416060603060b011206030b06100c0507060302191115090102070507060f0905030601050f01031d01020c030d0c0f0815030c040f02040603050c0a0221 75
    0x14100035401000d0b07001200141c981c41041c101c103095807040380c0800c0f00800300f0564040c580400a00759140c480001611410041041c1d2030385001810014091580500d0400c2070703c0d12072501c50000d01402d039955001542c042c0d9007540403102c0344521030550360018000c00c0195920700401c80f2440380452420200095450000000703142000790601600503914007684904403481c4210100c01092120030401004440000e17010708045959410103c03002c44280700d95940182482c003921560500400318810020001551540103081034108805075407010340d01039079201016034411007030088503400042d80203880003660182c0c0c021184c0d0f0a10034500d0b00101c903902d5002d400c90300121028000c58100281da188511801e209212088600382007100c0011010355004100080080040c0c05203500d2030091001541c0810458854502c010014481c80c0a21500d8401a403c40c2c40340001090034040416075010309078084d00d007445a144d000308440100c802600b10b00307404120000b14141c0040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 682456600 1250 682455350 682455377
    0x170a030b1f08090a0804150525021507030801090e1603052b05030613021c0b04060b0703081f1a1207020106081e010204050406120b160f080403 63
    0x21200d075410041841503048400704034910151a0020043c4821410b800c810340c14030001d03490701d0599042e5500c001c040202022040410341c1c00d0300c146440f06444450b4000c3c4002c81404a140d01090107200341d814845803803004c0510405802040c100078003140007c4010302c154946948040c404400c10411140c0701d461242c0310659206460b042a106c41d044111038120710100425069401c410b81a1446000401e5143c010010b01028000f1482003c05185440103009240c043e00d0400c510b05a268121a00080380e40d8018250244198007903030034400d0004a2180c0320054840003501a10780f030100740c3d03600d00720034003020440003080b850702ea076001c002c14541409125a040c10b1006000c155480c01100d8000c000c900000b408102160306000c014400304130302156894050440c10703000d041220070b804032103029000d035800c29908a440d00d64000b43c00646000c150345190b01481c000c12280d101c4040301a80d0b90350b07525804020034000800d000390700b4841c40100e23034001d0003440d2022015a50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 682457850 1250 682456600 682456609
    0x402130b030f010602060f040201090303080901140c0717040b040303050c010608060a020c160503120711130b0a0e040f02060d181104060503070f0308220603050a0c0804170a030b 78
    0x658088502c2e03545600180310180d0100b11140d007040c4000301c408030324980380d400240702d00c40602000b010031442a000c203042c1c6d40f0942060348001103040c1e05291030310301400d07a00301e150424601942e54461035602c1041e2208404101c8065441583d2000e00e803d00f50340782030700c1c2c641c00007a00c50341d150350304c040006034a8001d103c8103010369800c481c096910866140080c0c40d24990f0013510700381c6420303803030200100d59001408180e45e01900c20342e5501c980140c00c2510160f0000d034500780c4c205034640c030f80300000d104039804034500c031504440740008141c490350180403410089800070300c480024145000503103051809000c6a46501e807002c00ca007164148240002c001d0120203c070303107544148240c5003a144c41c0c02054080d10301035004100c06441d29601c0744404a603440b019001c4c08002906408005040d00302100a14540145042c03055945800500030310301280c3c01c1a245250000e0750107401e1040900710b0050b500014007040c4101a092200425480740a1031010b05a4800302441d091300c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 682459100 1250 682457850 682457857
    0x30313141009021e090f06061b07051801060c0f060e0307061d0307020f040b2413050f060a0f090906080a05010605010c050604030c08070803010308090f010306050f0402130b 76
    0x1144000c03808a841e0700c103100741300e0f4056010421000c500a032040040c1c903190401603000b420403900101c151205400701c0d00500c1340d2000380c0d681c648183c99021030a100060b000e4211901521010141448107550004095080c0a9900041c40105460000c91450009140b55034084c401c001180340001da642451640500350031a00643c40e010100f4511030702c50701040007013429902851801d5910b90001d04000300808015109a81e00c40c640300b0682c0b15901c07801101400569910142503840c2d60b0000242c1003541311f40c443d88490030010809080082044424200241a8905041c000303c5d0039904040c4a0459004001c001030000035a50003902920005040010117800f4140c0c05062260944a040d00807906001140302e2100018400044c1c0c01c1d4800c0d01468000714400300c91074455144e224090000d001003401000200610075140d009000c0315a0460304115110a070310015820340d100c510550b5404452401041b050b41003540040501034100740708140c109865082e0b0151507007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 682460350 1250 682459100 682459123
    0x1020a14030f030114011d0a0302130e0d021005090c0904230d05070204060803040e010b16050a060f1508072d090212101211010c150b0a0504050903031314 68
    0x240103c0305e0400035600807403503400485401d8001002500b40f900410700d894090700c07009019152500d03500c0c035080e0305944141292400c80094035035072101494001d54503080241300b040d03401d260070040346401a0021302c0001c5a8000b605007072040d43c46484802e1042c00907211070040340c1000180c08a0031405000c02c1e08820b016840382034513a0194014441217036182e4004071410382c8104000d101d030b242c80010160441d1380800b581c41e5100d040d4202e95101c02c0300e4810041c11b9100700c1b4148000c00481d908040f20100041000704603a061100070601100b8081c8100c0d03100e5000302e0f0081c065180308424098420425010340d9081c0032410810041d803042c15803200440650129011005419800f06650080400011500b04504020076281c644504400007003080111200c400301c146d0085040c2a40300346c1000c03401044800380b41d07412010301200c0c200707a8482c196111010800b4500303485114001d43c0b8000003075040d0394890101060480e482401655030040d070b000c086c03d0b0300000f00408001013 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 682461600 1250 682460350 682460369
    0x803060f041b170105090a0b010216271a0108130f0c0801050f0114040504020a09020c07030308060301022d0705030c070e0a2f040b0d02030412080601020a14030f0301 73
    0x103800740040c83c03000ca0800500303050104a004004c00d41e40d90b0212074000e441c40d1800a045031550300140d20f400c20001800d41c0d024a00b0400040310368441824809441a5103486d094610082d150309040b1000d6250294032200001402d40316940700d003180f2644400c201c031258040c141c0c16243c1c040d042c20307100340c110351104c600718007400341d880c0078000c241e0046405c0074004120b505040340c020100c54909921b0340502d5803000001c01303560711401c03200d005000070076046598600040c19585c8500d000d010a81c0851f40303280118040b41014421500c3e1101403a001c928024520007040510154090904035801014001c0303502140c4103000409180d001c02c0f0003401024600314140505100040010850300d292014902c00c00211107090700c4c0000c601403569070191140b40030544180501e8202200700c800119814440d190581e0045025900691064124501c400e42c02c030350030442141d0301401a00309001210010709640c1c0101c0101c10b5280075031b801c18981d605404216002684500e508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 682462850 1250 682461600 682461641
    0x40e0109081c0b03030f031b03090c030124030b060d1a010905100506180a170309030106120c0e0a0209180114010c030e1c02060a08011707120803060f04 67
    0x11522250500c42d0300c007201c40d00c00e010300051400000d40368004c9640100c00b2440c00000150b03405281e441e401410315018030416224288050541c0d500c1e10a00c400500031342c6055034a942c59001c02910b4002c0100750400350240a040da5902000d103030020700303841d0b0482c0c0110300d90710015409490840c00001480503284a0750300d01240328040e14005468001070305040382d018001034803802c040310014803d00001c10348070a545130110b064074640b0b502a45410208410400150300080000c20130035100720001e00c800780e1901c2c02050f41d16180c41009001140d2940100501c4d0a046a000d601468441c00103080403480404641d400000310030503102c3d2110b0400620065400400e268402c02083c64070303002070345503a9030107040001c000310b074548200000d100c2c1800c124044001314505d070780d000d00707980d0719103010034005080c03070781d081c01a400b048001801d56400306000161440413903400174883c00d48420745840e0040145d00107880c0940164035055540215210342c002c002c0e0007c3c0d8980701118 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 682464100 1250 682462850 682462867
    0xb0d0204051c051b032a03160602010c0206191e09050105060405090309010807030b0a0909052b140f0c0615030c04060302280f1212030e030307030506040e010908 71
    0x4100d00480030100c41e1110a041d110381742c0700080e01a0b0800ca2003200600d44004698000f0200001e0941c07543d494495122254107010801c828001140c0c8240c00a00c90081641400c2c2d0701ea00c000c07101052078100300400d001800d52140c01600000d400a1002031030341a4440700c503001c0e00c040010669150391101c00744603e60070184242540000e00b94003541c02d051410340000e00e00a00a0000002c01d85c4446a5441960340c100306000145480030041004455500e007140e1124003650300c0f2102440c0080031000c60359014182d114a9068175901c180080c0b0020014403035503005401080c8200100f80083e8030903200421401e801a007590040786d02020381c0f8410146401c0d03400c82040d0041e03060250800040e03c801d0110311149000d0400c990200c1c02c1d6003045502c00c45c0550065500d030f0045640024581401c40a0300740e0a8003500510751004032551041e420b550b120354540310f90b9401000001d16032846070344103603001003004102003940c1140d4140c0c5070a5400200054480e00b10001d501036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 682465350 1250 682464100 682464103
    0x3131119050f010807050318330606090a09320405160807121e0b100b030f0a0506011427030c0d120e09010609230603010b0d0204051c05 60
    0x8800840910744042280b40c448001071103804058519509a0030231a6451041e030014000c4101d0340c0032000020341903894100407250801c4c3d204054030f61402c140340105420781040c5080f0b662000c40680707200042c034613100105c00206070800240b03443c0105441c1060000c0856520031444403110080000c25052034185107040c24058024540e9070300740d44408222515011400c00129000c2140720345000d40b1038141100024001002c0c004030170700040c0c5035020080180c41050140c02c00c00c52501c44544c41c3c08010703803944425101802811407d1001849000c0190041a0311404c185400c1d017042c0320000c0d40000e250011800c0b049842c1c2a4078a4a00c4814454034106803510704800a00d8414900408600104c0e40d658000c0d0040c85002001c0f044d26016a0326490b90340c002802d40d02d170759a55440018481350f000d000300c0d1200c4c25443d03c01c0c00244815980c4001000004008c5441c0d40d02c0c08110703100310b42c845039031283d03a0780e000e0000203000c2c1d4400b00500211815a20b003e03610602c14500607 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 682466600 1250 682465350 682465369
    0x13030305090703240f141801050403051605160303021f060e060120030a0302030f150102070e070306180906110304050303060402090f0301180507060c080313111905 72
    0x1801c1962101004102040e200011480945004190300d5440041c903045200601541c07004821864141042c0d11004201842031302c1c03091179218941d070402c00c040100d0900780d4005a40c003030300040701803012021003668204510b04461040b021140110700901c61100046003da0090b00540c011541100800c5076020401200c440012020030150307050150003900c5840117000b890400101c180030403140218040c0c1403000c56a960101c903129000480010065132044541280351302c0004081540143c005051804055058014094183c185072050540030b00050070340f804c02d61100000107000103580c440118410340100d0110b40e941c0142480020780b450303210010b643c01410400c10020400120699410240440e005a0f5864074440054800b0070b0000c0e2165065181c00c0b454810070a000c0341c0c0b5040c80d4860b4040d25240d66030b9420a8900198084019008100420014071988a5401d02c1000c0600c5000d80c0307401c045040b4003003561211294141550780c2c4684809100604c0c216949 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 682467850 1250 682466600 682466611
    0x30b01031b02060c0a020102090604140a0909120309080904090308090c031f0b010309060c0503060909010501050607080304060e070b04030c09050705040510170c120a0515090907030b13030305 84
    0x420605a008100039a03d000050521600800228030340c0301d100e1003901200c1448000600064a46458041014040203c503544502c031380305c1d4050000b1a4501401364603807103a040032046411041500095014041003101150900743c00c00103003600d41d46500c55001c43d035000b603964040c40c2c070340340e8816890104417401181c802d07481100560b6610882e00b141b030380f600c0d00000d00070910456890050300580b083e0345005006a04004146004a5000f8003541c440c0b80201d130781c2030007500c2d071132841c85c04c845007801100c2c0c101008100c9040807038907441c01950040e102d0714000a94090a80d1a01e0400e03c15070052030590100040130024000c0c00114a070141402c100300700a030f4100300324003078858465445131a000d44c900305440c1e51801e0281d00b0125480030415104480c502e01a007101e10f542c0d00194664010350041c0001c01c0400b8640c1c810307188904044040840b50071601000c101407050003e21001151050000110004a40201650043c054805140d0701d18519140281c1034134401804d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 682469100 1250 682467850 682467881
    0xa21060203130507050f1f050403050a1109060a051c08040503070b03160e0a05011209050d03021e030142050904050109050402220f02031f06021218010915030b0103 72
    0x1c6da419203640303141c80c42d00c200e503509400100c1c01c071001c60700303407203074040e90f4000b400341d00459400c0c909105640e00f0000010108407130282d5640c1d40e481c100300480086006d681e411a402124286500282c120f00c80308250050880030b003040d0355400000e1501ca4180c0008c003100b003011081c03221403080120b80952914941c18000031104149003c02c1203501d60b03124007410840205966810343c582607011021098002c000d445030103a0004c0f000d00650701103668203003202d107400d8500c25142c0000c01074a06035020202c0c8107203226114405203070100c003160b1008130f910701c941504050b1641a00c0c03103018808401e844a42d11a0902c03001c01040b02d08c164001d080341800e06041100594407462031000b40e000398080c4031448846580725030020001d0060340000584000144440343c1c0046000094101090340003d4405881d600120f80341c403d002c10320781c4014418081054070342104c0880d00c3c054001890055a071955600024956030503c090040c04a5a5803040c7e00c89960301d40141c07040d4009030750703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 682470350 1250 682469100 682469119
    0x5031006031a0c0702151605070303090801060e0105060a0908060f0402132f0c010c080a1d030a050705010b04140a110c0c271602010e0105060a2106020313050705 71
    0x7100c40f500b0f124024009203d50003a500703c0304041420402d5600034030a0010340d4154036920300e4415510402c0e40016000725081d80400121600140144c40544d0084049074000340d00c2d20040c0100707504030400e150305001d40d441c070100c0d00748401c00000d4460254000401031600380ba0061200a0340301c5400c2d24102824000b941042c43c1000c0c1c40a20383d10449506500f10f4030303680c95002624015601003c5195081020303003c1c18a0344000d1950003400110001c020f0802c102c0401d10b1209149010408560814095400c030703540104c01070302d00f181c010300011940c4110701e4005000c5500041500283d91009001c0c000c101c0c0b0540b003284450303501074210500e080002000903503995070040e00188508100310511403110a80c4200351070486010103880071a003084003406015100740090040150f1920b01180c0e00500c05000d05070050b600035005201d2103060898891516803d030810304c500312140548440060f80c14401180302c1c18529001022b51040c40c6000380c2059141e0341312621441c51741 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 682471600 1250 682470350 682470361
    0x50c1620330a050a0f170106020a060b03010c0c02010c0c0806070503160804050334050a03020f060f131e0309060311070209010e0405070b0703050a11030c0604031805031006031a 78
    0x104c9034280e4041c104443d841140200403200031000061b4035041d102d805000040264000482c5110b0a1040360300f0302c10b24131b2a5052501300d031481102c100c0000c58100b2014055405032030f995446a001f000390051075a00d90801a01e4114141d61706000103c0000c00c20000041807001c801c1202200e1408224038101500d41030b9982c081d070020031510140751b18006901c0702c031144075103814005088003040140500d0070426164011248150098024108400386001001c55440c0c455542180c0212081e1140c1e03240c13191054900c003049030140e0703050302c01e5620741c0c0414181103d5944079903611030b201410f1480040a4518088191030211000c0c0030361001030b40d0b9038164506544504184600d103036120300b04140f50a405512070b4a00d242c0005c1c05d1414180d000004001940090703e4480c2510000704543e552841084242950b0303400c0340010130006403080880c641c280105004124040340c5440c00681421010311404000035510300040040242400e080300d41c08014a60100551801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 682472850 1250 682471600 682471607
    0xc1e0312020d0b28080a15020d02090405040b040201091d39030f010b0702030d0e010201060b0f0c0615030d0c02040f0f0906050c1620330a 61
    0x519042080351900420b08041180e15980405031032800107260f800ea042d600301d02003000301300800c030074500520b20b40130100b03070480005481e81409920032203080c0113804844012000303420401d152030b00103400f002101072a9442d03002d0740e40141d00a81c0318900500b0280300261005001d64484100d0210b0000452042070010b8545540018280302c0000b020402d004100e0340a921815503018020103003403061800c006a1000d54841c84100e030a0b42116601d881c0c412100e401034800c025415808401c85a04140c45051014411601070001189090700d40d14100d982d5080720408204622000ca00303945420810000b10350008185120386008124000110342c071140c0341080c007800d120100070a0780454a03107078480304614890100401411521100400142c0b01107501540c03040d040001094078504020210341402a0f8101120300c1c3e0100303a91884d41c0740b80c0404401d140071411051504882c0c480170000824201124038402c2d00740803040815600c0c5400c8000c41410110911000522540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 682474100 1250 682472850 682472867
    0x16062901180302010c0c030501060807090b010c020a0302060c01090c15120c05040501080705040906030f05061b031b0c0313030c0608070c0308090a14010204080d0509030309012003030103030c1e03 86
    0x102840c000b4030b02e0f045d03820700c000c15414503800248075600c6d0441c0003602920204000007541c180700418004026120b00450300070200090181d072065104004100501d0200300400c442d108010010404400b242c0f81c02c0c009030744992141005901c0c10780c043c071b100f9034407046d0b011505136020020401007940305002091030146008141c140072050000c200102d00550541d00200144102800303516281e04e410b214655036410100c41030b100307900200f64600b400204c01c1e5811040c02c5081c600350341c0c921030304100c180f608880d1418600010410703100c0001c01400104811501d1410f19000d50b071a62a058843c031180d5031010b810032100a0174000600e034044a440c1c16150075190520007501c940502c1400d02640d0000140003684501d003a03190214103401400890b107004068500c0c80100c404141d4a920505191640c075401c1000031000c198012244070900644000d000d0030404100c411031031841d8000e803c194086003120284034100209410900080c12070020510304600303da580c00b03400100c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 682475350 1250 682474100 682474103
    0x40b04060b030103080313050f03190503091b040e2a031b10031404030306150903051c031e020304020a0b120411120709050f010f0303080c160629011803 67
    0xd01c00804030300940d9014407d02c410300d030001c056a1000760795103c0190780f80c0c0003c680c4682d502c0700703c00e1580014015019240b065000d01d001d0020019410300351001072450008450384560380f8000440b1400d41089007100104c00c810f0810703118030701041a001e60041c00c0d0300403440f80d0320007030034030410340c203000e0000f000d24a040e510103902d0004030038194040c210045c0500c1d51203404e80208000e04d40c4c10b4000c4005c43c1c460386030480b84101c1c8210b08403600070719400090025070003071220442d81c0d101010300400100312880c0c00180041503111070b41d000401c8070300044405402100388030540c17404401c07020041591030030392441c2c0103401d0a09500100d001700301070541c03180407500c00c15944401d40a000070541c15816140c42d192507407542d01c01000b00ba944000101c190074008240d5840c0c500c003002c152501501c40707070003a030f682111103074207075000d0700045160742d480002c3d05002408a0140c40c0700245041807114000000c1c8909030039841100061504100085e07010303401098480c61041e05a9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 682476600 1250 682475350 682475363
    0x4180b010f110712030e090703151a0f0a020703030e0405060a05130608060c07202d130c081f05040f090203060f041e12030b012606040b04060b030103 66
    0x1c1c5901040c01c000c10f07648107124540702c00544d0b508040e03200c0d07540d08245000f21a040d101b51508942201122100c820400d100000000b003030048500c0505546400b155600980345000004542144250451003490026030700425040c0209a0418040b9041200940b4100030510380038000425560303551003214048e8440d00340c00103003488560480ca0141c810101154481c0c1002d51000c19074ae400344c43d05032100313038120308407501000d0284a0f05244981c020080e41a0200b22550a1300440b20002007038501c0c0184040c4840a0b120301081154203070f030708100020344000c17840002c0c1c9084001094602e00300010040038100484000b090001e544003920002008544502044002d01c44d03504047d50601c6008104020340c10040c89980c842c0d486030403149401d0605c03400d94551000714080050a0200d041d183c003266a00c40d6100d50a01c0304145041007140301e40c8995850030805500d448900356151404010907801c080c012000d07201c42c15917042114510742056801180010b00004200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 682477850 1250 682476600 682476617
    0xa05160f02030702030d120b0603040803041202150903040e0601050a0c08090d0c08030901090b0a0804060c0c0f06052d04080d090b0903030114010e030615060c0f010204180b010f 78
    0x640d8420802da5036600d42c05421105180d0031000050700800c0b501400a05003820481d21210504041e42680e0095078800c9046045807595541d000300144070207490340840c4181406049021908a88a4000e07030401c009507965500b440f40d03001046000612150501104000d42c10b03901b036010300a0100035401c0103031252561303035040010360b0501070544090125541080041020707100440100602802606d80c90106540c402d1100403e0194112400c00b0a90100005003c00c2d8140c0001154651501c1c002c99180320755903c440003407105000c142c2d521566203040210148903002c40421a1120110442c0a0520b1808006010743c0043c00105504000300c1c2da2080003d058010032003256201c841100036151003050650f41390400d20030403413641001c400402165009000d9194903000c0640580002e9856030000111508490701c001d4004d4000c12920652072024070042c1c0c450f0720340000241c1d9840c6010b5000c0750b01880050b54940c0d0f0751401141c0400c684e001260310388225064100b0507032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 682479100 1250 682477850 682477877
    0x5010c020f2b03090e0709050a1202010201020d0e0109020910050a44061b0a0e0d050124050a260c0405040c030311060f01050f0f1c0203060a0516 64
    0x101c00c2e58564011488005412058109030b0800f02075416506010900801c1d0b540f200d404a80b071110600c280e58115599850901c4034060047c80102814010300015241000c83d0420408458080e024642c1596580c03600004518110340010b030401e03400c0042c0c2a90508100010742c0100f510f100d08229a400300d9132900030f034180c6a200d1000c1c810744500c9203100740c8020320140c00c07020707010401c41514040c600026400c130785140d144000c98843c0717040e100c0c20411083c8044da0040307034804450750b000e8100144040018024000c1d9650450701d462400c2981440c0050800084240d4014611511a141d820700c80700a03040b040042e168a024017421b107032001c095829003402015249203400c5800c0008010038400c402c080c1e042102d219640f040040c8810301080c1e41c40b9002501c0000d00030340d20400420140c944001c011b41c00020050240d9015a1075800068030b0001d801c103503e4050f07240c84404c10540c6414085907500c40c2c00c100c01403003a03180c4803070943d00d0300c0d211000701800d101d5200020310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 682480350 1250 682479100 682479139
    0x70809032a040c081807081c0912171c110d06050103090b0a0902060c03040b041802090a06050d060b120702011104062106030510150b040303050318030c15040302060105010c020f 78
    0x40c020262a8240c55902d01c441c0c0e280381e80e000201081300c1c0400c40c0210006000314801a001011981007000c001e05041c1d11a04bc0302c47c1e901c040038280c4030b5000386a40800b40c0b0356511030880a42c0c2c60080c890303607c45a09507000103880302584054149858201f0203c0401c603003410340c540c402c0e2110740007d81440b19100268060040ea4242d04103840007181c04500302d0400b400600c1a54403880c500e00e11281c1c107014401c164440c80400b0398010100c00d10130841e0074080c2010300883c4c031240720b001c00e41d1070312007880706801d80142d85d800719490504c04c240b188058082c810402c02c0860600054078190620034041d1000b800301c40b0f980a00324070f00066070700704455540950061039100041d04c003107604028490000e01400107201c512010001e2000400d14244000c40f800c0300c1c2c1c1a00c80b01d05594071b04030008840035020780e065246002c02c021024040e442845220070441100280700618101070500030303c0c0141c16009107040c010780c551a10007581c0c035000d0f0011100b00c12221020103592410b281c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 682481600 1250 682480350 682480363
    0x6060a0e34030e070e061e03010e010c1206060311040e15040903030507083d030b010f031b0302090a05100807261501050105070809032a040c0818 64
    0x1d420008004070741c0201a89600720344035107442802190350f141d03100c007410b5020754810fa4074a0b5002064205807614944041d08a2269190080000030340906566450f03007900d90098080001036040900480101e560780b190601030241c3d8901000045010b40c022840740c46680039a45800701150001411364596103900083c8420180061000e2485480c0c00b4018043c15074540300410365400025015400300141002450800c4801906040425906400c2042c5141c80c110300342c20602004000b14500b0544207000340190204008124a1800c084076402582244000d00201d00c100810240c4c3e140c503201340c3c000180b0f1900048035281c14440b00708485842d0b11885950240444c001001140c2150300074010035041d4681d405902071003e01900d955140c0c203450909510700340144800c0d44140d002d081007601c40c0503914582004000024900101030000121107081074800b42c1d4084079240c0e03054000702c2d00f980c045c01003050b1030402414014004100b0304510a0b54451000030f5603080209 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 682482850 1250 682481600 682481671
    0x20a0f15020d05011415160816050c010f030b09010509060f092833030b0906041109090c06030613050a02092404030611041e0806060a0e 60
    0x21035454041c020400040d110034072940007202510510307045170b403d01d000e4407548038488030511483d16645080c919608500c000d020348582006004468844200b40c00c2844528040c078018400c0c040a900010110030f003454840e400c042c10040214031684844020905450041740c1030707480e0f541c1d9a0041201d00b0f8040c403039503611543e00011301511600c2c010601d50b4101d41e2a5204209041440406060f038198001e0000751310f07a070420004244c13003c80340c040e02c00300d401c07010070b50815031b00d446078001c92406690780403064002c1002d02c01004131005c9010345004050f26412070340d14041c0384480d142c841e50074a250282030700000040f140d0356404050f00c01c400ba2100100120304007081400002d4208081c10780c0650340c0b00c454541895001c10241c81d10001e0280700614050039a5541e401501c1c50407411003a0240501010820f00c8040c905520f1343c07402d01446071682e82c600700855140c030340041d05031801050411400d01a0413519401d455000081450340380c1c10f01c070950400d9180e581100314 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 682484100 1250 682482850 682482893
    0x290f0903030a080402030c0111070311012d120c02031204020f04020409020913060506190e0406060f140415050f07060c0507140d050a0c0c0503061906080706020a0f 72
    0x45030390220f50040540c500590098040702d2141c80103100545403408604a050b03202c0d07015807801c20002d0001c3c1c1d00042c01503c10325217a207405e031510884214544212032560301d84c28044413084a0583c1c08045d45040020083e42848403400d0190046d40700c1c071407980e1460400e01000c000805544039680e988032072030400703402156555076030340c40f10f002508541a40b91081140c0c8041aa940045005000507208000c101e540b802c2c07419807510b05a00701c00140007080c8403103e074a00040b5035441c41840003c00c829221a00240c071090b10007010103c5010a01d15801014401480754480402c81c40c00c2070315503400c3c51550b82824000d15821802130001c0105a14200440320029690203400b42c05c07090300c66800024078a440310340f115210b445581944000071000d025030190544903d807103500e820300856444940d00d8841000c60302344141162502c01c400700c1c0341d0070280c10429510416006040f10006802d0302820540c009450b01c00d00003010b0f1901032005000d0003481050300c4104c020006011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 682485350 1250 682484100 682484107
    0x11404150c170a0209010e100e010c060b04090303021c050403080c0c07091802100c0b0c091c06320109151814010519090c0c050a0605040507290f090303 67
    0x41c40d4006584400805c81c0001d00c207115803c0c2504150300d42450709000750b11003d48400d644030045130701280140303090701c1054813004544015110340c03203441d0a013800399170b0140c3c0d0746880341103171040c0340154910303850458940410400401d510560355504a0000c141e000d0361207402084032490710034507400c000c0046251000c2d94080010060591055502c00d68040f045c10814840640d883d9403859005880c807007411000035606690500100030311b050047c00800082c940c043ca0b03036990b0a6800d8115040d41d46e43c85e6080222101c000c1d058a018035601440003101103c40d14034440e980107108800d1107603200e01c03104c1e000c42c2d8801c901001800c015480c200d042105040000081e0240c0b08201102c010034000100340c0d07045c01c0e100e44400c0381414243c410301c540b80441300001890303070140e0201000f90808440c1c0005001340000c06200b4090706000c00c0904060070801d0608405500406061508800e01d800e00c0761005001d4135480486061aa1900e880901c0c0b95610711a045400340e1600000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 682486600 1250 682485350 682485361
    0x2090a0e01020c2401080303040b01060f051902060f0a0c020a020d06020717070201090f080a150608070b0706151a030703090b070f081803070611040506030103080c011404150c17 78
    0x132402444040214080d0315076981c0d62142c15101c1c4400d40f4042c0800c20040c005005d0140660070b50340c01241e5500d80245000c46038030320000c0d084c0e0b142d924440140c01c44028007024048102e00310340c2024000340200154114010040e588081c9440024090050421600140182541034906a40e001004400d0068481100301116802200e080f0b0201c0c10340f010108094070715074905800d1f24008001429603a0035a12041d0510401c600e2901410b900d030745c00800c0080091141c00c00070a200d60f80303540ca842e202d140c5030054820090429176000c05118003045040542d0700e000294004c0c1c040d849a40f5140c2c0072089002d40900d613806004280c3c003030180300c6225444900e8110814055603825416120340c900000f10024803404000c00d507100740440b201103a00c0d9840406c02210150000e890641c0d00d4021510981003680241d030285070115030504003400a0051403280b1041405060892810760f5600014400384403110701420350b20312901501c140954851607078070112400c2241c041c600f2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 682487850 1250 682486600 682486633
    0x270203010803070b0702010504030903030e22020904060b0a08011806030501090308160201110301150e0904110909070b070b22140d020705030601060f0c0c14010e060702090a0e01020c 80
    0x10403c1120103418120000714105d1040c07143c00d0040380c0c141d86020702c0c0d92658500301d07a1215200030341c50f8000c151000c1c0791300c84a010340300d40e829040013103005030315511890100021114150310150f1400c0007000010050750b8084030301070664002c048081d04002c2440880c2004240c82d030002010780d860081d2400516801288144c440d02c00066000406036071058200c3c02e80300c0082ca8440081c8091005122200990003d107085a18901d000e0841e0524039000402000e0b06a82c1501e100301402d8081d0507030305100c9480c90740024070f20010000383d464055080d030305101d400703070143c0040c1240c0c000c6510f002c4850840303107568a8920581070200326504200c1c42030850082402c819100e0101c40c020324a0010a250040b01c00042c00380c03003ea8a86070b0b0070307240284c1d010501000c009034600480700050000070681e015050f2501c5000540e05203030005064480501c4203544124024845600107a499180c600d80c8042d0800000c6918080c480d2411701901400360400c1140c0a03050010000d1800d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 682489100 1250 682487850 682487857
    0x142a0723040506040207050705221d011112010311151b010f060501170912040306020c060703090f1b0906140301050615031308090402040303050a0306090e07270203010803 75
    0xc0898040055481e40c0003000100e00c00c2c1c182c0100300782c00c402c108000c1803515210140c0c4000005603040540d281c0b00c20604104eaa0494031184080402520601851024803442e145020401a801c2c40c2281c0b28000303020020301440300400483e590f0b4000026903c90503140710540440e12050b60321424881041100144e240c031882a0f41d628014040d1007003100b90141101700e46042e12005078072502d070112080180c8000b46503280b580b10390202a850b6103181c02c001c00096003c4c00700143c541c11035070f4446061900107450b020400d42482152004510403483c0041f1050b806259403550101d0700038411035000700c81c0d215040c9603291100000c0c00d075000610703048146004070020070407a580c160401544000c80101203c005005000080741c2c1c05104001c142801d000e03e0350716041603007400000c0c0a9a12a800440005c0e2011844c2d40e4096098003c071409009884800d00c105d140811802d540d40c0321034450319840c8480306010f0804601b03200c071200c001441204055503607684450302c141d0741e9803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 682490350 1250 682489100 682489169
    0x90e0303010f171e0f0c27060f1206040c0509010b03071821050705060403111011160501030b01020c09070302090103020904090c0303020601060512190b0307080706142a07 75
    0x10401c00d1001407409107d490000800c00d00340e050703103040120f40c40c090f18100620440d042026410421169943d042c1030740390030354a19004181501d020319001c0b034540d00720703804940628100c0c40140001d0b080749051743d030301c08242c0c44e100741c0c0044c0b400c21030740160309240e000049a555203811092004134402c2c481c101c16004204548550342d845081c411984034a10014003c541c002030a150380b490040110525014285022500c08000403a164205001d60f080c0181035040d80340208410b58150144400d400ba00b400940700d00c0c5a4007000c80c0400100034600410150f001405208a80c060340c190390300404040e004000124151808000c0c1c82000c1c002a03000d0701c00d0308000074032241704008950001d40d035150f00700071a89480a0680311907001c0c95001d5449511048110300540b801c00c028001401d50314000d001440c541a000b4120110741c40b5014020b000412085890b0003c5049440b80700403000010380d64a003141483d141840c0c080e4100e80d040c24400012072035014181500501440e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 682491600 1250 682490350 682490353
    0x10f1409010c02150a0b120d0816081e09010e15040b0c160201050f12160807020d0e0904020114030901050703060506041404050c0405030a06020301090e0303010f171e0f 74
    0x90345500c07080c4e9480300c036200c111480404684c00200c0304502c1c2e8001602c10113010306807100d8680070101c1641449200140c140004032407808100d4403030820810003031080752a040140c0c00742444944440e07428103100b1405109840b0700007040301740a00754000910b110a2505a4550b0040c1c901410050346099034103030b9005d6a8100400d6911201e0811034100d108510101030180845a0040d655070b040881c043d8950301050118110380080a00c04078812088803003101480f4080c03e101800d10900a8440400c55100200110023a81c00c840e41c2402820111000b05480e591440100d0720807500740740e445403151001c410320010060541120303000e80103a480c180321003910f44050000e0b50255200c0c000140601d1441003c080c20194443d5801c8914030a006140c01d0700c07080420302c1c1c8501c0b210111070480e4000010461200a031260b0061508090003462455240014805941d605805108100d0ba0201482c3e40c071440200090b0a401d040410341444407031350502d181e9250301d011801c21b6007a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 682492850 1250 682491600 682491611
    0xa141e0c0406050928061214100b0f190b0f18093105011805010506040207020d02011d0d03080105030606090709060507020607020306090304030314070206090909010f140901 76
    0x84c41d10815141c4103220140080030000d44c0804440012400045506440d43d41e980c1301150b2441d80a1a440c24a802080f10459910401c0350051419200054242c078047c0f900202c48402d03900e542e81c1c01e4286004030350644085241410504820080383d100041440c1d002400b110400402405402c400301041c5a1890b50340e240e20510a89100c1103032400b01140c03006035800c06140004e0200c00703001100300300c11003041100d562a1030840e92451150020b002e1040500810444240562580204140ca00794289001c650104110303002201780207052128885005032171760b011180e0f20030b042000034040c444514003810f002d001d40ea001c2c010302d1b0090082074001902e80c188020b6040c05010141c1d00e25034114900401142d40b40c0100d03070100c0c2d201c0010081c1001690302040903c0c051060100599500c92646ca00a4512003112110409a000c1403003043e0240c4d66a40940300200c606983c2c03030401e980d4140040c1e0061061891001c1d0315450500740b50b28103030b240d0b032889109079003800c0200403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 682494100 1250 682492850 682492859
    0x708120d0b063919050a020a03030801090b0d02062d120103060b1903020f030322330e0103060e040302010b030c011b0f061d0102090a050a06020a141e0c0406 69
    0x40c1c2d40c80c100344409084e0700c8001d040c041c1d03101940744914020302980a0340c00c040b00c1c076800140440c035254019000500740030010310062805101c3d1000b00a402c4035140031510b101e901180c094000d0000010311140e010a040c40c000546411209501001804a503aa504155003400300302a0078002078400700d20304120318640d401d124905140c41d500d5250b200856924503400c00c80c0985102d41d00b103406010a11050038490000721101c0485000e4000800c0c02500300f02c03042c4611660140c00704c2c2c07807083c000e201400b90800300b00d04141c9101645000d00200c4249001600501400c0e40151503242c1c04104110a043d811b600c105401300086085d2056034640000449a4880c00051003d06903020710600d40083c4607050410060ba10518001c9005012460940003000b102100d91029940001d841f01191802030703c4500941000c58011003120300381200295a50301d0080c0080a40701400364001003000c0402219018903041c48042d08080d4644644c261900326100c00b4600403401c0480105 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 682495350 1250 682494100 682494187
    0xc13080f0c0405071b170705011a01020307020105041707030f062309030d09060b0405090a0b0106090b09010c03020a08040b0915070218040317010b12090708120d0b06 73
    0x40c0501e14503a01c10030310940d640c5d2502c00c0d10700c001074203c1d8000c2c4184a980c8640f00600c1c05003072240e0064000041c0d448001c1101214091114140340c115041004490010f0ba00310041d1415603a50441103c10880900e00d01442c080c102c5d0405410400042c0b6a80308002040d0040666100e0060340400250950200841d41c00700c03d54110401d5001404107800c811059440254000c0c05004040762500b02038001c00d044410598907004e0315000300252600b230145007482540100b006207070424a0720701e018007940050003803d040d6810081400d6466041c54800c021910750355030060010f0b8bc0d19590707405004500e80c00100b01d0380c0943e0b1070302c4070898002103003070956082c0c64010781a000800d480705488208114001d208800380112440c9001828105000711800b80a0440180303584100c45d203180e4480d0340d001001024540e00050301131140c1200407803944003480c264924181c8030444d25119802a20000d90f1030380d040703000410180c0e107040408a000b60303911030400e4120301c0d2a803c0710040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 682496600 1250 682495350 682495361
    0x13060f030c020d0c02040b06040906050901210609020d1b1e0b09041509020f03010611030304030c0201121d0304030615030c030308100504090b06010e0102070e06090c13080f0c04 78
    0x240096041010003000c410300810414241a200400001c7d50f030b491200028443c5c3c229802180842d40d070b50900703100504011450340e0140c01700005001509517650480a002240c404c0002c01068440e1440d40842d150050f170303040c0b0720303901c0345009240034400c1100740c0420100f07100781440c1400c0e508060103403100b1381c0c000070103860008010502d00607400041c80b0241c42e08040403d1645640c2c2000142c804131071026020402200e12032580d00d501d03060004150681f0f074102d200c190b810420600002030b8001c01c2c40b440303495083c03e004886424152008005040301010340c90f89a004040202c240074001c4010000c1d00c0c41091708010b0307508001030580186000780402807555003580c1041c400719009440c880d600100c10740c182e60100d52180040307421754040c06c000302c4400c4c00350700502003a582c200581d00112503080c8000c0c50043d00e0402340200e015009482e0500078980c0310081401444080c0c115803144000b0b02038500703240c0e038030b003280d035507680c41d00ca0340c0e400500940c40220207500d4240100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 682497850 1250 682496600 682496621
    0xb0607050a0b130804060201060306140c0d0903020c030304060c051e15060a05130b0f0f060708090d02030613033b01122f040506030f1b13060f03 64
    0xc024a01e51642c811280d54009003030040140107882e650700028035000c1c000c101030109580003007400c6146140500507242c0c1c000440111250340e01c10043d0050945003920190700c2101c1010804030090b0806a0070841d20700103040e02f40c00001408100190007104403841c1074820b1045a842039001000c020790001d0340313500304016400c040d02241e240104501e13441d0700614001c00500c00c90740e4030300000d00302c141c00b02c082440980c2c480036400c0a501d48003280c02d0840b00e05a40203480100f0180020b07000b8810400020111030000c0b9001810703443c0d0b404542c02c3e02e03a0103000c590150518889007900301c40030040480010343e0700c80ea000301024006e03182c00d50039500000060a80441c922404400c0580d0240f80c038100906d0000e0000e0742c0503180248240c0c142c2c4694020207441d4001801e08103c5070380c0c0102a80007108120422140d100c1101f103c4d44003401c8103200c4001e0b01e1341488075541c0203141440300b2100030042900c2701d40000c4151f403a0200c0310395072502c0c44141c000c60301c1603068a0041a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 682499100 1250 682497850 682497853
    0x1706010501140408100b090709140d081608030f0c130b031f0b090a080a0803070516051203160c17030903120117150c0304080a0c060c11010b060705 65
    0x108815405101c4140e0011001620a41800c0d1103004403854176101c2807002e80e40759101da12205450801c4280144c00c809240b9049036100c1c10001d4100300301d103071400054043c0140401e44000e0000b80720a03203280907060048507004c4c10240c11f2144040d0000d0310650300d0420750b90003280341d0103114001c540c4181e61010010f000e19150424008690700020003140900c0c0701039640c03ca03405211080c0c00080e003903610409464845031402d00401010a0300300b41440d070300c0082d955010804003020307694400329a00e4419610030100074520f05a548019000f0204d00c2041079207c140084003002e1441204144480814140110004c603138404241300d01408070007008810340e1b04001c212000707584c4003203424112403030248601c45000808009900c419801a0b4200401008400c14070074a00a800448501546420700011a690700c4c400508010600b240c001400d2a4150088074110195504880c0c20041d03203610f41005014174410309001d0580f5460072100d005240f50000c00d66000c0c0c2d8000c1e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 682500350 1250 682499100 682499113
    0x1c05071b06020703050c010203090f1c02030d11160501050109180803040209102328170123060307081c030f0b030703050d120216030c02040b0418030917 67
    0x807503a00095005039030a801308001004600d00c485404d00007140030340401c20040204800035107401e410038040c19400350460444500c40128640d00000b511000b9003410000228003241c0a84001e56200d00c050f11050b4a1001205809116040d0700441c12501d0248003441039a1640a2086c02070580f003400404001090000c00d026003014400f03603520030b04510f202e942d0786845518483d42300540c00d2014040311b11f42c50084041d41005030301041c0e50581c920342c0e2040111540b50310410084603004070b82300402824403002d03024400b508070030031009400881c0005500310300c898491808007280c03424013902c545000012054000a0050294260790aa6085003480d00004030701404510340b6003903074035440300725018181d641170102400562140300200803c00103003d01800d010070000042c24080e10600000c2e0380000308d240c902e08055810716203110812414030000300180b0044c494280c02c00e1a1629426103408100c0038600664001d44071240c0190703541814000721040020045020f80008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 682501600 1250 682500350 682500353
    0x302061204020a03050f0a05011409060c0d0204030614070e0102070803030601110a060c0c02191404090515010315060906051e13140a11070f0b090a081c05071b 70
    0x2900caa0454030007880baa141c140d0b242c88092500202034020030594200c0c19422080140034032401c410346404040000d03862801000c187c0d00c1c4c00c1d00802c0a1740b4078000064800941c1038580c102c801860740040c003040000040c00155115405c200c0d02980480c05101c1c0349202580001008021120718000440c5142c0d0b4540c01101c081c0c001e9603001909110b6206a00d002a030789001d0855130900940d01c07102210f4090040011001410b840d05036241c150348801c1c4030000002503400d244000648001c82c00403002d103440d03442c0c001101c88500c0d02c0c0749594008402c00095901603240429944001d0040c191180c2c140c034110b03580c0d440340d40ea00c6000d40c442100801800c04822405510061607680d0344400005600161100380030f103c40c20401c40c1c0c3c108480703d40244901710805040422003428000c6980c0e641d18200d1003140003428040507500050701c080d07003c2190003142a40002055207070010042e100485008004442801c02e040c400001ca14034415401c9650210140c1c041c513004204030b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 682502850 1250 682501600 682501627
    0x60e0603040b0105041802061207080f041101050711271e0103020d21030203090712200301060b040b030f160203161e1103010b01110307020f0a050a060906030e010204030206 76
    0xe241340000001021b400e084090f81d100301c0500010005c182c0041064900182c0040c120b4800403d482d0380c0000900900000c6088492507803220b290a00b0020356074002c1c0e080c030301c0c02e0403420603100d684020b2902400031405510000144c00505064185040b504c45010f404a40c24086508030f000e915000010409441c00079081c1300410300035040002d01038000b00c0c2d406130004030b840198000c42c4d000402d0000e200c100b000248018000c64005080c048810341d01d00b01c83c95505440304841e6041442020040c2c1c0d82903020780f0007080f40c4400f6541d0b8590300c40401065400803200c40b406054210b00040300c40c40030710402044840c4c0340d406103140811503801060010020740d01075a284040180256810143c6c280e0307003c2c0b5a0140000300580081d0904150a40d007105145c5410070503240644040c80b04000242c50304545c1c11126901c1e54104d400109551071525840542e01c141c0e0804001a11604220000161422035805011090424013000e082c1d12403803000a40050081000100c011f10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 682504100 1250 682502850 682502861
    0xf06210203060f240a090303020d0201090f0206180a08010e15010b0304030807110a0c0305060916270c0e031207030c03030b030c15090a0f030203070b0c0f0102030907060e0603040b010504 82
    0x60703000a250041340100441501d9411100101001c40c005000501c18107404104c5c81540c420b20b44000d0002c403401b80d5600d2102990301034001e0180340041000d54403118031144406900c800503241d100001d60311401113001c0d150341455900c035805614260b031645590328001e0b030705aa103944003491568031590741c1103400c41401814003080014400c9400c120790000c0c80340054442c043d40c40559441e00318240f1508118016283c0101503128802051641d1102c0c1c1019049031f1003040c0d8583e02c0d03a000240482c003845085110074402e8601964070101682101c03003071411000940c110b807005010841071111510650074040c4c0462010311000000030b10a4006030b101c100060240c40000c008800801c0e03c0c0c2055040c3c445c250035020520365214100980200002c0a40704a100301c21032950700420b80310b86460296490f510307400540c50118038010000d075402c845960000f10751f0786c5401090359880380064054180001c81c0c0841007002071400c0b0060b03900464102c0321074801c41e480e100c1007000a04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 682505350 1250 682504100 682504129
    0xf090d030516030807031d061801090512180d050604020f0d1b091a01090504050405010207140606010f051903090326011401171605040f06210203060f 66
    0x100181c0030106500046002c5003403198a401060b0b0a00c01c80140598690170381e03820b00142c50000e5201c0301800000c0f11608844603408141044207500c14440c01b41018460160140c1f103010460300d1101c0744c060040c49030703040c0c1d00d003850500241382c000c00c1000138440c10090300b00c2d84040c0110380503182505003000300000c001d00f46c1c0410302c03943c0c1c4c0398810112500710007440040d0300705d41000441420302415181100d5001c14528450201c000605503111a0290900480c3d4032000102000030940c11644169000000b80340c0d00c1010f0184a0b030b81c0c81c8200c40c4980082d002c0400302c80302d280100c041e90f00c401243c0d01c45404000e6031003000c4000b099142c00590801c0303443c0c12680301041e07409004140086010100260b190304005209880700b15195031281001801c0d5085090310b4240c00e42240c002810043c0600c941c1ca002c01c040b81e141c000e41e0400f00103010340140c0062a981c0141d803040f08000d246148a005410f070800000c12400115142d541051700c04410300784603d0410320040011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 682506600 1250 682505350 682505357
    0xe06040c0317091f0e09160309060e030c030c070807120b07090509090f19080a14040b0a030b040b01030e0705040f02300a0c1e1209030815060f090d03 66
    0x43c01000000c1c0140d010340103504407845540b072500a00756200640c40a490f0342500c820016050281c644d08000c2e1426004408040d80e81c03c0500402006801080441c001d003021a80c0340d4800d2005d407030700c82d4003030280000d80c1c0c81011000a860310002c5100402c456a528690401100d1615500c0700058014842c0c0200402c1a0b0045a01c1e0396140300c0600401250004001140240e0880307480c040100390308004031780941341c518000402100444051107198a04001040100860a0418001d5800c03421412030041042403140d945540a0019040304450901896107181c00540c02c035070401102683c2500000010f100c64105a048640d03210143d80d40140360814842101c4042007141807243c0b074040b0072102c0003100301e0400c0060350300844034040c20000140260740142402030ae101100d01c00800c1a041c15800c14002c110358081794614802c00d2010440514000b0000329040340e00c3e8412520902c03011541d07051604c10b6410440101c0c054500d041d1401d0100300441e145030504800b003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 682507850 1250 682506600 682506607
    0x81003032114090d02190201030902010c0b040503030403031119050c0c12160605130608070e09040501051b09030a0609021c030906080c181527040e06040c0317 70
    0x200081c5101c1d8444a12031803000d0103071814014a094100440c00da03c00003103501c0901406964125400c1c1040c1b4507909090024900c020340c070069505001d41e10002c0d141d007140500700428828044010f62281c1d200e40c0d0200003042c0802e401042600540400c0005e200c800d410075203140d40500014440320750200121030011240f80b0024110520395910740282e80c00c04910624440802034081010308101e040190400205002054103400c00d4030600080099680204980900405000f0707000e13035020b00541e081d89000c2c103000e400703400c0544680e6103000c04402c1109220180005072404100d0060252070f001125880720400350155480a980c0310094041102400302d00500030001e0511136110310005519040c0c0203040a00024410603100340308000d0200b60b001101404c01120100326541c0259400314210100f840c05030f4074502c8990b00d4860203660643c514411341d0f04440a00304d80034040d19400d5400107485a50950380204804850b0a061000600c40b011034101312101d50105401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 682509100 1250 682507850 682507907
    0x504020109240842040212040605131406060a1703040b0c190510150e0f1b0307031a06071a150402040f03210203090d1401061e0608100303 61
    0x810660034050120b0a01c8a13400008100003401c2888216104640850800040103602d842a00f03000300b005109a99900018880d40c10600512800d40c0c0c2010b60b039145e25207540c0c1c103075070341d01d8003680d205100d1440c508000842641c43e18010000d200c0c8030010718103041c40c010704004960040507281c001030051054680a9200002103588024052801008101c21159281c01146d41e4180140c000c52008482480b1450384550a2908100451080042130ba100d0405802440740100710409012000091100d9103600da08481c1c910803905800c500c14038080010409280b00d0080001c1c80500c10303c1ca4002c0030310f83d64962560101c00381d06104020040b60700000d0490f40710b41c100303407001340d0b40300c2051042c020140343c4208510341b12035969000f98000d100c081e5803401202181d504c00c4400c07031400010801d2000081040c0c0310800000c1c042541c9075654064071401c282041e81c607140c1030100004485200d0340907a80618119095140300300d0454404881900001c4640000501c020401c40d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 682510350 1250 682509100 682509151
    0x51507030e0306250c030f050307032301090e060f0411030319080f060d110402090105070605010e150109060c0b1b120403090803070305030a0f0e0307050105040201092408 75
    0x2441464144003e0902070b000c0b12a54005060004d00a410888898107020000307800c085610005155400c02d81c0c1c4940c3c0700c1e0303000c0b0b0140c001414100503400d038411500d10510032014102d0705139002d8010034005070081c5900d0a594400403282554900c454801003404500586400340e00a00050f00307503840c0403a04104a2600c190610603c03000500c60010000b0603070a10104642108084600400b00c04458440c54005150b080d546441f96500003403100550380507100b1074901d1940a1000c4c03007030b0740e5a0540c1203040d150444401c1c01c00c0c215041c545032070f0361044940d8010741e0090780310b10030450201d40b1004c4c1c10740300007000300d031569401c0240e812400a08401901503219481c03c0d0310520b141c1032900900c034280c80e9118501070ba0060200c00700181e005010703654440c00c20306000506201740c1c512a0068803048103039203418000002c0380e00c14000f0640103144114000c0c0c8601d001c840d6190207155420040c0b0490000c4d0301d0000c0502c2c0b54184c400c212a40e002529011a034084007211004803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 682511600 1250 682510350 682510363
    0x60603020303031618080d030b01020f010606030e06060117040f1a04050a11010503090c0607051c1206080601060503150301090b150114030705041203020703150207050c0901051507030e03 82
    0x418030783c000605104c51580c41101c00c40150150008034000900c1c00c61069518220a12101d05060f11100d4264181c0d100700124180f8840900085c40015554a0301034000c0c00c40040380302c0f190143d0400140e00c0d5011382508000c40001c0c0404280d255515241c1c2c100c410050070381122049843d45003c2c0c2e04144003c0c0039801580031368091b085404082c9042c2e80080d8000351568180441802044070360b07407011510207080c0c1c5040d195035585200500d02107090201c01d000c04501c4c5404038600030f00c2c46601c00d02400b15240b04080400011340c8880c0259511042481450001341c41080040d030001042116580c50841c007500105001d031080d6541c5441c03450417101c550003031a030428880c09660b403207a07001d07650001440810f80345090140c0010590301c51406641c209172300368100c86041500c00c00540c030066030003000c2e611461902800e5a40650b003c000191024800c2882c0510f043c905440c00310704032200100022108115480c422900340c21070340e000c0e401d00000e401e00c01410b444c00c2c401e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 682512850 1250 682511600 682511611
    0x100203091225150305091c0c0503040b030108070b0c0604080702010507201005040812030402210d030b0315010524030103060c091512050a321e0f0406060302030303 72
    0x10450b51608080c5200001c1400b1811141018140814005010030204020b03c8a048924102e099070f24440015101d030803401e0030040031031200007000030b01c0500d00c2c00690f050342d0340a0181d4242c40d64404060ba0306004031007501f4841d07044440800c00150b03480c0000d00c1d940e881130420780d0428038503441e00c04580c490051151411300d40b014001c003681c41c103900c401c1252780b5507040507410203092212099039844100302c580c01e41a8000040740c02d540d00c0329010303803070040b2810492003c040945080c0d91030b4045295108042401c0007442c200d5450b002c00d804822040c03403034100720284c0c82c0a00704209807840c5083c20341a10141980c100700715480c44000d6010354081d000c0491160060b040082c04000e8a5100046010344c00b043d0020082d80804652903d41c94144007082a440e601c8000c801030180301407180d154000d103e0718115030b1141c994a08100d444d182244001c50b41c400780a0301c0f4100b00040600e034603c0c01c0f600050542c0118583e01c0d504180102800110151682e0120b4616401580d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 682514100 1250 682512850 682512913
    0x70e040b04091202060a0614090603031b07050a06081612020c0307051513020105030a050402011e0f08010e0709030215090405040b04170906070602070f02130e0c1002030912 76
    0x7003e01c11a40420900350481440b0300300308030039803030403500c11a0710001117030303562061070300f01c000c1809560b04000740c42c0d43d540010b22640043d440114070345e5581d2400d01c6076074001e071200000060010300400e1101c2c80340c40c0d186294801214421822200403221040008000781c1c244407440c1e020f00100081c0221503c2080181000655406580d0314800001c0031800d04445810401c00181d070b00c0804e503a04800ca010000c04c0c580c4032440182d44090b0000f4210000c0c210200084642e00d910101828040000c3d4a407100280d0700c0d500e0300c0e8039042d0304440400101340ca1502c100010b04081c1600800390520102150510b0900400202a203005841c2510054a45000d200c148000c050140c01030200490079149403541400c042900c0e40242c1c034000d0701c155404603030304040c0011094210b000c254000c1980d80c1810004161600400100d14484e4240c4110f101500f60740c10a40e8020031500c603203030015070500318080c0801c0b8680d403000d4000032181c01121aa0b080e07140c0b0b55650811204491003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 682515350 1250 682514100 682514123
    0x1c0e0108191b120b010e010807050c0105040606031202060403020d050d09051c260106030e19030807030c0c050a060c02071802070b22060f09050312012c070e040b0409 73
    0x10000b400e014078030054022162911144c14042da801804100e2240400c1c24008182da903084010b03a11405480070841d20b40d401d250070481003041541c0000c1c06e4034810700c00700301a8041210105da81d41c004444c020056401054a01c3d219406080607000c190f05546001c01c4000036551500d040801c900c1440f90288021051408000c0d00100d0000c01c980566618100c1d000c0c0e00c05c4100c009a80611446040c581c2d19145582988021f00410b105100c1045a0307192024480c0781c002c0841d0b000700c0d014400245059520846c0390300c20404402c00e10740003030082c011603000380c850000404590300300c101540b0408400058412804004107040d00d10b0500050f150313242030800803000d610003412400c009491750b0f4003402d00c001c4000b81e058260742042e8000b90700c100c00078180000f0b026680300030f4031030305c0046041c1131020008905c56058400100303010300c00c1c2c0c40040d00d4030303001442c05481c0030314034101400051116214020100e8480c1000b0700225290922001080454040d0038007501c4551041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 682516600 1250 682515350 682515401
    0x13022208060907240503180105040b06190305060a0506010203040e1315020a05071401060b18100e150702011b0302060a05010e060a0311061b0703051c0e010819 70
    0x50040500a10503800103c1c9880b286100c0405244c9000b03a240701805004800f041e400414039000d049081044402000f0034101030420701096001140d5041c46514590b84182e142c00503000c030082266407042c0244116100d14010b80054a8014800c60440c401031100140c41c1c0c00500505005101d441c481458540d490306150003802d650083c2118031500400c64426600e6000d0201c9502542241a9041d03250300a40410b000d08140e0f40030b00c0c100c8c50045082c98110800101c2128200b03802c4030120380c0219811025144010002c45040d40324091035044090146007a0081c08080e20500d0100c11018290107000703c5828444000e0303005078048010001c40304818864280036220500c1c500d00c451070642e0002b40c1c4484540401000108003d50421494507142c3c1174075041d4a807500d1408041c41c01400303840e0303140e00620055629100380b0764050000c5030203c407500052000c503a14105002d140f18010b5800700000350405c940345a02072200c5c000c0031424030660b00c0c1d124400141e01d0090105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 682517850 1250 682516600 682516603
    0x60e0607170a020310060503190204060e011209080403021306050a0e0a0c0c021f030e07030503540301090c09150e0708100f180f020306130222080609 66
    0x2000300b003049204006100c41c0803419a00b40c0121251803600319aa65903818291500f010646030894085002260100e00550010f20b0206141c2c0b0070384c5d07035494804803c280c641c02d951b032011000d41800c90804c01840903090100d25924061071440020515598400101d800c02c16240d0110202071030040074803a040e0784500440035603185c5841c281509480680024040b091b014808019186440080e030003154029003106080d02403440c1074644555890400507107036400711001c401020120103070260a0602004a0781c244040041003e034061203246c400350560304440d130350745004e16a4030402e543c550303070900035440c0e001d102e40582c125162030b00000f141a2a00c000c40001181c43c4101c06200c80d230400c100c40c1d40d100ca11450543e050352201500c241d17004600f034000201c0d400c00030202140050140140c1d6a1083c3c41d61800c0040303205000c0c6001c120701050703541070350000c00c51803020441c201c160058281c1008205484c000d240454a040207032104951209445030031030010000100c20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 682519100 1250 682517850 682517897
    0x60f060109081c0521010b1317100903030b03060a0614030f0c040207061d0d021204261f050103050105070309121413230a0b0f07060e0607 61
    0x11940080504400c0e001407900b07030042c000c483e08200600402c03141034810081e1300c021030500401180d1465540c466465030540d9100c00c1070f11a100000c4078000854030084c00081d06c441c507803030019200808054084c5409030420300010350400d625000c00942a070740071300c9114003850402c1b500052451030075802071001c0c050f582c2218800d40041d500590300f84008110050f40e09400c075001a511489840c0610003050800d03c2c442c400340d10030003201000c8030300150300c800c080d00c20380031030311001c1e91100d00ca000d0780b04500445000c0c0445a1410140e841a6020419105207082c140c500c1d860001070301603060b41700000c1c000c0c4081d4541004105206080c8201d640040440c50240400c07000c94444034184501101a10100200e210ba00700100c4020020b0310701010114100c1400e080c0c1da00e444548194000b41c00180700c08262051603050b14028002c0000c8466803103440f41000c451005820076034000700010b8423480d86800c61440800f50520000e0701c9654075840340f11601e150100108542075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 682520350 1250 682519100 682519109
    0x210304031403060a03110d121809060609090e0f010e0102090a050d020f060d02040308070b01030530090d0804080f1002090a05060304060902040e010506150715090c0305060f060109 79
    0x7801007041c0304180d2919484e1400b80c07604040740048806001c400300f0260710602a02401403900c10200d24200c5601000348520000b1940e1280c2d0710503100e00f444012207600c0d1241e0400700b49a4502002265a170750009040e8074001c5c015201406e8003211002e095840e003110007401030350b00280036010340c5050386210002e040152416200d102641d400700d89030602401d5410b104040100c0c0c030014524194040b82c02550380020043c2d02c94080d403800d14450202804201c589006801c0c1744490143c0d0707030302c00040030003400405503510302424902454540c040c3c440d084d0040da012440401160342c507401400103020940c0104800445521311a041805100b001d903c0240100540030a0707075a00c410300000c0d030318101c644a0340c903107583c0745c80710042000c1c2000070740003401c01403042d00c092410352103103220f4902a17904c0c0c41428510600401648600751000b4040d4452a280d205a10f00c1ea9022821041c800c49460014540326103583e850181c0440301aa40d1403486420031400b564030190400091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 682521600 1250 682520350 682520387
    0x10e040507210b060d0e1f060e15010206041101090509010f140307080705130609150e0112152301030803070e06210402060f0705030c1203011a0a0221030403 69
    0x42650800500184203e005c0150031544900c00c06c0c03201320b020700140c02c598120040c0b07510b50710209912039000c1c208511500110400e680005103a001981c80f511101d60016030160200e65241e6035005003000c0240c0423507040100b03088021500c2c0e05d6083c040d42c060701170540319140180c54160307240e400e1030031107a0303441c080d8006100802080d00001114001d68000300c50070510071108204441c010151a80314042d0359041c0503400d41c000004e200e4140645900c404610056a2180c02503070004c2100440203210620440b10701100320016071102241d000e03401f0280000c5903982003c50b50481003a0003d80e0610400004c1c40307030790380d0000b985000c6c0a00c00d0f62040d04111001880302040545000308031040340c1580006411569848111201c0c001091141030704c86400b414001d96a4001c6e44494800f84158401e0341c0c14000000103590495095229100c042a040c0f441c6005030340140311880191703c550924220202d829103c1e00e42c505400003100f0791079140900700140111400ca5a41021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 682522850 1250 682521600 682521611
    0x9090201020703060f0b060304111002030405150d060b070311010b090402060304030e0d080c010906050f0405120a03110a3203070c17070305120a020f070b06010e04050721 75
    0x1030760041203030012280c0100e40043c40101400410740608a020086984a40000100030801c50700b10b81c01c038015030701030340c41a50000310345005070b0b900d109600980b5071080816008803942c0d0301300d030b0040000da00c0682c1e0100700c21ba920010000c042c1c019036400c4020420f1040c4030101c4040074403072044144030071034035296107061640201c0c0d070f41e100180c00070b4200701003882907003035548451044100143d404218155180d03000b4410354001c2507880400c1b03032041c0c18840440c08244000f000c0600494011b03028003160407410340f5620701580010501c005054542000b50940c501c5c00e0003138000c00d4540e880300026181e41c00321031001c180350704050309010700015030b02c002ca04200c241075a80c40b03034035414004090780c801e04101c040c160b0200c6140040f9a0000354041c2055801030261044180e110100c3d05140c0701d000012040e409242002c40b050003044c4580401704d04600001c03500000f06050507040b510241021070705684c0304452503408903c04840013881d25076000c900400426a07010200311 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 682524100 1250 682522850 682522853
    0xa1203031d03040e13051f050a0b060903250e090a14010c0f0810030512090108130b0c090d050604112b02060c070f090501050307060e1c170a03090c0909 67
    0x20b06401a107030000e131104158003003040100400c801480c101100f00320740c0c5040d442da4000c00107403502700c03000301140f4209242540c01b810000162044010018043c4c4210700d041910b8a0001041c200b940400c680c2d100b00020303484c9070740c5551030b010300f0006024144a2a69080520300144c400081d025241e1600000d07041c2e95a000715501d460060900c4c0c00303945034540064150a2420a8002074014000c0c9e040544210003418000c0c50402020b8950705802d030307955411011500380e00720018181030340724000590044041c6000b041c22000003880320088590030b807101460404115001ca038041140d8100b071505180002034a1100c1c0c440c082d05141000c81c0e0f481060348040c10b544001c0c0599004140d4001500c41804401e01034110060669a280da44100241c0903044c20f01c90b180c06401182004207100744264a98107050760058004400ca45005000c0706401c0c00364a002d03500c1d40140c1034242800f060f88030050a00c1c1075640d501255910031820b022400200701d40c02030000c689007120800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 682525350 1250 682524100 682524119
    0x30f080103111005041806050f031501060e041b0804330203040f0605040c0e0c0301030c050906041127240a030b030a0807260f090a1203031d0304 64
    0x1c0100a06031004440e00414443c261340c0c40c0125001045806103240da20440d800c1c040c0d02ca0301c1101c1049030f590f076429020000749511a05070b8121300828080c0d58005001243c001c0000b89039880c1d015200180018084800241a9a04030502d01c0042c01803401e110520101c08100d002204030002d00c60b5810b00e010841e00501d1078130340b160b554113070740200c00501809000c0020b10749140d003106080c0b2062070107240144110440380104801e0303440d90390110f2950441e200070f82e41070381e80c41585007441030309000410988540003014554490b8071000716010200000c0d014000d40040c140d0500c05444144444400c28010300901500615049005142c20340e4480c0e800c0d50008000b440566440e541b0f680200d0150001c881070703540511030400d0030010011070340002c0c6011401800c1e1038001c804c0c3c480c0c0301510140d404a59404140c0300f8080d280401100e08010038449800820501d05035a0300c10a0311880d14858030180c000c6039483d20214450954580020301c0e003215500514681402c0040e40c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 682526600 1250 682525350 682525373
    0x606020304051309020a080a12080405030702040513050f1609110a03020a120e060a0b1806010f030207060e01051e070f1d180a0f0c17250309030f080103 67
    0x1240304207210f1005000c004500e501000d01160050300ba0500d154661035180c1e620100d901c0d0843d2601e00e039624454540344282c1c0c25601495011015526060380d5400308030180130040c000e035045d401d03808010340008104001c06800c90a405024241c5072101a00c1074078400041d510941c0498201a1000392100007034003100d115070600d00f401a100e600f143c004503010b00700d800120304203515100b9980a000c03000a4658803c1200d46400d220f0350030300c0001c0c0300b2031900c00c842c00382010508801080c15036000c1c46c10b40d8006405480e0040c1424242d840711400d96025132008082d59554070103101d600c40740d0198100da9078044540b85483c17401c0a940040000b5108401030040100480169403995aa91003088e850f0000034000491602c40c0c0c148801000340580b42d40c4025450a80321400590381802402a480d040761110002c880b900c50344a1058000100300c0d11203400300803e0040320507000d0341c644200e44a20359000a20003014a800740051020522040901c130301400100002030314000b18 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 682527850 1250 682526600 682526609
    0x9040c030c122604031202010504050d0c080a0f050d0906050613061503150f14090114060a14070f080a0210200c12030a0f050c07030c12020c150415030606020304 71
    0x400002419401188407940543d170070040900099103020070105505400950040780181c0541d240c4d40c903d004143d400000240d801065010300f4041d5002c5540650001e141d0751113207083c010b16140251010004035035031500c0488440e650f907014044141481280b001c20000610820490f4a040006030303818001c0b94983d200406440384403c0030180303052005000101455041610055102c00303509840016a013000e074001d50282c0000107121300f5001c5240c000d0b200c0549100e18025442c0784c1102c00ba40d10442443e580c0804003d003900080f50036002d02102c034020941d4030f445481c103001c001d042c5a5030b241d48524450a282050300d100301403a07002811014031184030b41d03803600e030001c40605082e8100b4004040c020040304110b00f40302d01d0380040308dc181107440100800d544016003c90940110080a000920245c00090004a245160011488040c0129a50080520001f070488904940e03a019901c0340406e00708543c528200c41ca070303840e91060909001d05800d0940080d42c80c01680b00303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 682529100 1250 682527850 682527893
    0xc050301050904030c0f03030506040f2702120a050d1413120303150e100611120c03250b010603200a120501031b080a0b0a021809040c030c12 62
    0x1060404d8040e151140c0016845903101c20b85400c5400d000d070007132100300e41d414000d9050118460581c1e50b14440c200000b50a2100d840707403020207103480070301145040f000302d07003005034203161100c40c080411080000c548078400501d5409041e07078006013100c40014102c0408141408481121406259154140c44030384048903250110f50501b100508000d0303842034150703006c5008c041000741660401c10b10400d04050b0348000c26540e14411603000c0545051405103801000014950722440d40050034443c81d09030840b800c0c61201c0100f40c900010030341030b082c0644d02c00361910080000020000c0d005180b11304003000003e004c0074030911b07a440c0b10419004004000034440d10380b02d020302e0480c4441d00b06820300708000c0d030316441c0006000320105c0a41c0c01400c200b840004c1d18040001e10f4106959000c9602c0364a901d4071036115003e5048145442c14254284010051549500b0300d03003031240b8003034083e44001a207107040558003440143c1080202e05038402501012580c2d111000c040d1072000131 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 682530350 1250 682529100 682529119
    0x9230403050a1215050321030f040c15020309131406090406060f26010e0322050402072103050105060f031305030f072013090c0315020a120c05030105 66
    0x221aa890025442d61040b071070107843d01e03e0400a0810442611780c140c08440542040d04200906031303d51581d180c90100d020400a0460441070740600d4216104820008407030707444402c0c116a00300035a042c01d0051b480812004030502d480c003c0080d403000b202004020540384050712200e5030400502030313401018a180030404002060380041e00501d4107101c11512142c807000e00940c04469a41804103500c02c03040c802c0c801f0071040c41079580010002000390319202d0000d1001011800e40f004081c14801844400070721610b903800280402407003000550382c1d41d00d0100300004d8182100450004151070800103001c10340b0744000305c40d80031404170005500d980c5c0700c800303043c3d444d8015140103015000208142c207042d00f10f20090b140f1135108802c1c40f0f428100f030041580d40c91004507000f0703600086025240f0310510240c5d104000b4617001d80308141030a80c80780c48049021f506c941d041761107d940014030701c441e250712100c02c002522790084140308644414400078102d00042c002e16103e1288178 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 682531600 1250 682530350 682530367
    0x1080109051504020c100e0c1011010e0d0309060c080408040b09060d0606080402010807020a0809040911040603030504050109060203070807020405090a0f0807020a080a0c09050a0e10060923040305 86
    0x2142d0b40c400d11400410540d583d40460003d5078440701c103018080202c0d41840f40183d0740010100f03103100910300182658015090506040711040c400c400002401d560b9811a08021181440501b9041900d9100855920214681003003100c040203100420400f61105100c0081c4201c001c9901311502c1e0003070b1a8580c214040002c10a1040c2c0e501c0d10f025516000b400244190481e030014492030003600c2e00c824641e01c0440980c0c50b8120031000820480082040f941d0b02c1c0303000d40c0410344050094580b002242450400b003001c9030856001038002c184085400c1020351382c80340b80480505640c1c4040e504000c0c440d5641c41c0c1e14060f07850000c0c46107455900103036189000300704103584aa040b0103038056802090901c80b41030b610001c016130217001c2c13501010504410024130956a241e0060420f44070340d00d400c003000001e103c050301203840b480d207407901c00800b1703141082038400c50103e20360005407103032501018070101e4107079002281403032100c402a590400420600d10b03521640508005944900c1c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 682532850 1250 682531600 682531621
    0xc0a0915120e06011403030c0c1306091e11090d0204020f0702030a060b0f101b1e06050f010e04020a0603020a0e180402011403131709060703080702070b04050108010905 74
    0xa00c9010310140d03103070507070b040d45080300000c00d03034101c5000391010707059a40c3e48414192240b11b600d0504001d0340c0311990b0b081560800c4110751202811907400011400d4903405a00191002c41180d18001c0d140c0180440c05003103e8827681c0491190380c01c021746010341642c003140c001c00e603c00000e03214650103d0140e002070400c0040301d0069034003d05444103207201d49070080c028405818814000c2070206505030050604140900c40e090780c1da11480d80030603540c1500050141220000c0399402c00c00c000d0740a01c0c0c54440c1030345030210304c100c9001c99145425404102070220503030109480300601d5043c400584c5440e141e0b08142e6140d45400f598400c0004000c1e00c0700ca100d482c646070806042c4061400741402501c8080c003d51007640c46001035000305066941500003510200d0140d4100c80d100000252901a01581050000c2000341403281080000300c55401c204000e0b804100c0d15010400416230510860010b8808150b100742088d0070000003c241e000140a0f15040c50798840124122051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 682534100 1250 682532850 682532867
    0x15020403060507051e0a0503060d0f06051503061003020d033c0f030b060d0911091611070f0e07110a080a170108030d0903350c0a0915 59
    0x80218003030005083c80c0300c0c0240709620600010a90b0240016020f082c20880c208aa45089695039480c0c1592948410849410141c610803240d1104a05481d0001112801010f100b00001400324007000609801d040c1482d000a01d4103100b0341036000103000503511090780c40f10140e01440d10108070107541e03a01450003864249040d00c000d5403081014407103031840444040d24a41e50781c441a1a461502042d400d4070440e980e2180c0c0080103000b0460f90f4402c07a403015810a0140540f414010100301c0030039544081a02c0d000000c0210601d180c403404d03002042d1200e8801407070010200549020807444105880e4098038000d50141404203451621900d200c0e20610801826184007400e20701e0b2000d00d50b4401070707600c804902055102c039480b01550302103030b041300d550b0302c099842c00c403d03903400900901c0141412010700c004104080f010740c5207425030003c00080303070401e45000c21100d00034a40032130001b094200c40d0300041080d10f030300c20390140d094400c45610b43c445943c000141c6509551418 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 682535350 1250 682534100 682534103
    0x15141005091201050c1e090906060d1509020304050606060a0503190b060a021507030903350c04090b0906010219050c0d0c0e1e0c0a14030f040210030c0c15020403 71
    0x1801c01302032140510806000700300881c008a1080c81000940c4050501c5000f40da900e00d5205840c5e40024045061081c010556129201400074038a160325031680c48601494103c2044181e01104100400c003040051907041802250070354205945a40000c02920000349032030741d0b10b01c903540012122039035500302040c0918024070480e150b002000000b5030f03d60302490143e00b01742a03880840c0455020b4850407072499010303541d85000c80c8080c0080d08a4000b005c160b901504c0a18200a502800d4006510300aa00b50300360680e82d00e141c2030600050715565101240704000c2a024400c10360780000e04179044049040b00c0d400d035601a810f01c82e0030020819009a002041d100300903080112911246080c0c8621003c0c00d0140d0f222007103075000d8040820034241c413401c40071010824001c0300790064040d26600340b074000903a130300520f0300c014182c00c19070768180e170800b0384414081189804c20002d40d01c3c190915040104d41039008008011884422019040d16140103010401401a40441d005503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 682536600 1250 682535350 682535353
    0x20607061113090c0305011401020705060f0c06250206130b061f020c031b0a03030513080717010f0b0310020f16050a0b010e0903120a1806151410050912 67
    0x325660320314030002c2d10004c2d200c000000e240c0302c00400c071102c481c80300408c81c01040e801050803600744000d101d41ea40c42507943c1024583d007403107254541b80081002502c5401c0b021252000000a5028258a54040d0103500190742007001006030348108421502441c5410060907407450701d4142c0415592200c800ba94134182d10003403c00c2068580001d00c0a103048010380464101060090040150702c0002c2c1019501c040b990404001291040000c1c008480e440d21164030704c9543c8000c031500d092240d03840403140d031704400888503140b03500303200d42d0440c942008018802d80c05050000303a1140401800c00c0102d81c2d022890b41668803200b81540d090304400306d01e2400d224660f00780f55507a1031708400100c80c1c20038080c0011440082d16103016018506c0d020017141400ca1032082c04e0700070007008040ca51520303942d01540c44211500d0585411080c025a0300142c4450514030b0031141d102250440c44604d202c072004c04c9e40c40c5e1507200c4d5500302c0700760702c2c41e103d074a45180d10002040c1008000c0c418926 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 682537850 1250 682536600 682536637
    0xe030a0e061207030203010f140d0b100e360c040203070c020a03060509010c0c0b010302010e010e13051b1206060307090305030c010c0e010c261b1e0a0206070611 71
    0x11590140d0003181030325020a623501c601799a4200d8010027018030b400c0990084040c1d40020006601540000d410001410000700c0d0f064032130321004900402200c00c0c2c0546003070141c0e0f080101c0d20318064044000e4071b2840000c01800520b064583d110166100c0360300440d800000034140c2da109001600b880c0c1e60013808190440d682c2c0c10440c0181006441c81038155190441c41076403e80600e1038841d0700c2d0350003250343c080e0380e107150010f54101d40ca0b00300075818000c0c04100c05c0c00c10340d20018500b08168490a00046c14284003c210104040ca2203420f0340c414000c01528000b120b4520340a64403080846041d40d03070355964441280e2001c07596200410074440825120071081d81904140d05800b40f50741c0b240b000310170010044510044900c00039080003074006880b468180203000200d01d503c000c00e99145081c1c507415540c1c000185214841b0741c0750b08450b480203040c1011045c001002d401540040c201c50060390000b03000c0b881090001030045586003004400021180c003609ca40644419403202c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 682539100 1250 682537850 682537861
    0x40501110a09030b15011d06040b0a031a01051c111b0a0605150a18110c0106030203060906310605010603020a0e04110d0b0a0e010b04030302100e030a0e0612 69
    0x42d21a01c0d01040b206003000030000780e15040220708000c18440c050b9100f030412101480301546020741d01c2015a0080820880410708000000082403c0052a5400219000c2040c945d04c4064282c800d07150405c1002c2082036000390303100c1d800c40c1c024000f034400017480f03003208145401c89100d407115030090040d0300202d5109401002c14a464500d0050074107104035900c2421010b80000080d6120b03a11600306a82404030b2880c0300c00055148400d0b10300061119031050141d20240c10400100100b60b440c0ca100344110b0500b40807654203e110f450051003241003842c000540c040003400d855020000c0400100803041c50311600906907500040c042100e035864110040c080e50021000b9004a02c85144080203814a4421928100300940c03000b410a03145122040142080f0394240e0380c4508000808140002640b00c1507008010608a032507807249140ba0203410000443c00703c001c204c1c580380d501307841c4400210448030415035625001c46000402e40005000d40074150341400002010301c02c022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 682540350 1250 682539100 682539107
    0x1080c130e0a0b1008010207021309032105061219060b03150702010501140d0317060a051221041a0306060d050907060e060901050f0c0102041710050f0601080f040501110a 75
    0x50044c8001800d00c6611900c5140300350a030311a00d4002900842c064a007038241c1040340d448540d42c0341c400d00d46500541c400d581000851803040c0080c0407456559000d10000e40307040a40d5086030304014014100d140d1030300d127911540c1401d000010302619212007480da50742e0350600076440012500030300c00945091014000380201300900821602c5500101c87c040ba51600c401c040002d298142e070707540c0e01000014075050900c1c078064040c640003490110085400e0755100c5241d000944002e0080c0703040a0001c3d0030808a10b0702c12881b00c1810810001804041c07960781d24030349140d420034107003503032603d50201003400d40c032071003005840301c9103840244401142c01107941400c44030301d541d070161640390f41c00420030b2501c203840700c41d804224200034104440900c60064000c0e000030800050919650f5144034607080b0140c4050307020342d00a01c034540ea10450501c81c8a4008182070300710a40340c03510300c2c006001c13502c1c0a0016081c5180e40000035080000075044810041165101d040d20740c03003181c0300034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 682541600 1250 682540350 682540373
    0x506070c0306051008030307200703030305150a0b030f04150e011a1009090f090203061e010b0a0801030b190c0e03011a0102060c07030306030c062601080c130e0a 71
    0xc07164141000f002c65107096011a00700261081c4070b020f14519160780205032922204003071001003a07400210003000051007030044200075402a1808500c900c2e140e9079059240b080511890310603160b00f003044c058a02003c050769030100340c040c4030f0180d42e2614109808143d6400f4540120282000510203a181d8107402c8000744045140c0d040150740f45020802940001840d400b800081d05650100202c0107940c01100615645210000b003800c10b40c7c000c40d051000c102c50000c11441c3c00071501c40e40400c048806401450b14654490400418080c0244078070011310024008100d410081100000254252960070301078030000c04c03001074603000103407070b0043c9101000c5c8654038081e007005030000c161460091003201603003d084076950b042c001e40c4076900032440540425664000c04000204c5290364000a40000d4440d00c2e807055034401440b50f014841c030205080a564800100002c11000036244140e0104a8102c0305280c0c045400000900482000814501c6070f810042e0901003410f044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 682542850 1250 682541600 682541603
    0xf030b0903073e030c0409080d02040303080105131a3c0f240a02031308010902270711010b1e090906090a0f0c080105040309140409080714070506070c03 67
    0x107050005000741812041100d41084051301604182e0305000d82c2d1401e94400301c8079610441400f81010814a401d0007280c00680007100481c644400500a5141c450381c41c80204d00b00030345c00e00440f424259952071500361042da0034043c864a00c80d190b0341c05201004400d0082030004403a0400702d50380c1006003000705112800d03000e0711181c19558113a0415140d448000c140c078558102660085051019607507209241e00004c500040c4402c10f180e1002004c2c9000410f01100040f03056041401080403201c9115295844d540c8542e15451000340064809540a1b1142c00e0440c4080030300101240541840d0501030b034000804820341c1500c01d6141603a590340401550034203419a5040100c5135140015505c02010361700c10601d07140051500c103641440340348a400345148036980e858945081d02e001750b4044011443d00304040c886040000201070001404031028080708c045501d40f60140d00c10900c0150a40034000d07490b071095581046180300038080680419910581c80c1000321003034009000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 682544100 1250 682542850 682542923
    0x8032503050129160602091f020c06030f0a0c03110c030304140c030703120905090906040605100b0a1115130b0a0605100f140a17100f030b090307 64
    0x6140503008280e03c0841c40182d00050286012204440a81c04540741c3d5022140980c00f00300fa02d02c02c0d00e42c40b0504035502c03a40f18194510206511000c0c3c101041f046045d40a50b5050041200a07600f0b00301054010700425800076500702400b01c110058017a10884c14030242d4006841400c8020020007944524020005110440b0310041615180c551407040241d00d6880b40c0742c14000728100305034221012460381007020203181d13148003150001400321781000280d04514200014403c850040341e03401044070070108580b42c20507031101d40320300031070028000704099820b400a034207000b00504141703040c000020285602d8809c4c7d00004080050b60111401c0d4002070200c0c41040a5000351819034100604030600e5025100c011202c804244d812001008030922034098240010710080620300e0350340d95401030700498082c40005c1d1020107860000300c0018003900b0003940c0c40f090720007800d0f29070048c0012201d44820003e185107003e0410003400b000160080c1034403000e400c2450103c10b803035224 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 682545350 1250 682544100 682544129
    0x804030e03070b0c12040608010b180a0e07030c1715010c0b0925030f0605040614010b09030d0e0d022808010c111b0906010201060323010605060f07080325030501 71
    0x181031700382d4010b500c201404070b42c0090060007102844405091440d07440403a2084044034440043c94145887d440b1051010601090020040e03241c041d41c040c1c4460742c1400382038000c0448820362441380003024895200259020360110303030300ca0044c1c03050b01a0800c02450340d80c102107141d01d40301c05850740d00080c900341e04102481e110101180441c00ca86c1c03c2008150304a07003586aa2000d002c00038000c0b995a5500e01c039140300406049038240c040c10550b0040c685990b2600309162500c96400f80d0981400000720110210755103043c071400d0410b41c10b40794610040d0354410104100f404c10341030710320107a000d901d001c22220015032029125506541e5541d00c17036140d00c491251140064280d0710280c00c0c5000c15600c02e800d080c12681d070440010b20000512a80c0d986458030781414100c4110700f1a8681080540d0000c0e090044001030082156101e18052180151150b50310540300000c00440002c4000b0790f4100d04280c00c61098071100702203015085810800500500c8240941400c0c2c85910 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 682546600 1250 682545350 682545373
    0x521070305240c0a050a0c02030d08070305060f09060f01050705060712060e06130b13061d010e070f0e0312030414120f04060831060c140301060804030e03070b0c 71
    0x248040340180720411110b4540410f1034411503a0342d1004546e04207200540b442000141c404000c4140101c106e0f0b80d4030021402c1201c130040a1311006402c0d00d00c10044c840d4441b8881c0c0d22a030500750000c0007107a001e8400071017080143c1d058081d00d00c1c041c1c114084c05041209064004001c8120004610f0b070421101da251001a61081000e039a065044216003150f060b11540b2540301d1035208000405078581840d5204c01002903600c1a0080609001c0d602503030f0700c1c02600711342081e0140c0300304240c11901b8502000c0c0140440300b8101010704100d00c1c9585095107032401d0095010040e010f060042c2e680c03405080c03001442c006001e100302140304580f5513407440d038008070030b83c3c480003000c1c41103901c1c0c40d280210031120045c020307101801384418144145048000a614440400800c00c2a014144200d042040c12281c0350820f40040c05072540c0b1003c40b00c28003404582c1503d40318244901c0380e031100d040440b105512171680c0c41d0103103d403400114950340868050195030602c03100311040e5072810f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 682547850 1250 682546600 682546663
    0x130302010c031a06070f050d0320040501050f13092c01141906090e0a0210080f0402060f190302250f060b15160201030606180521070305 60
    0x181e52102090403060b00c042d0b5113494800002c01074140070700d20346003079951541c8506081c400424000c0010036076074680709034001c2e188805400f4075030016202074205440d040000e8403903c0303414040100c10300006840200c180c00d05100f036002d8000124200032005102001d400c10885948640c0f01c0a00402c008402000301402808010608403441e00044c1d12250111038032031008528007604503403200f0340840c0b0445640300741c0c07401c01d81c41c40080c5a60443c5006000c0c80300540d146e00c0017046182410441d50780f501c0c41c2c0e000e80081d415601c0c5541c40720141d066000b14000c0c1d0a216009002001d01da000c0e0f0f030b506030023070691001c41c1c070684940150016a0164000740700b400c002c1205005038400c0020892a9110706408080a4444c6151183c0c0a5500403103901c62840c0c1c9680d1202c04141c134003076503803510806c0c2c0500400d042403946001009001e030a1240584140341c0704030300d0b00010281c0c0c20041181000a401c888003145c400744d4a0345850703500c866480710105140806054224106900c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 682549100 1250 682547850 682547861
    0x309050301020c07150c1a0f160207121505100e06040903080c090a030f0305030708060a14040c1b0606031a10061d12030a08100803090621130302010c03 67
    0x408600420a03149044c5502caa2903d88000310014040c0070814039000c00c2c400300303034080800100400707481307d842c1c2007003030500f05040509140c4841c0a0b800c40d0303001c12a000075195080d40d614821380c10341c0003410b143c004011848031403031109160800b02031104808002501d01c1c1510b2181c41e2a001a0f5522018041110140302c2c0240010782c10b50013003120300008400404d0a0680a003010400b151240c40340728818807410005c40029400000b088034803644007884c2500201c0444211150b00e00d48803a80d1078014240d081e65114642d11402007480314001c20505540f04903170030100031040d40d181818001400a0301c4181c0d8000000350110000c2c51240440314403030013a681ca8800c80e2030034450b040311051043c200d4688003160900b402041a0354101c002c400310a4100010f41c0d58144080004201c0323480031b042003c1040c3c0480c01070242c501c0200c1500c114010640300c3c2c9443c4e010701e441080410701148051040d284c010406e1140d6040c041100f105898040e400a0114070103201049080f1070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 682550350 1250 682549100 682549117
    0x102060c07030813080a0f030501050a0e04080a0324080606032b020304050910142409010203040b13051008061011010207021201051806010e1308160f030905030102 72
    0x1001040040000307400f03a058240c005009242c0103241e0801039442e480d040e401211070b60089100003241a019503803501401e070244c10b0075525442c420b484c1450545031654040c1005008100100e04402600d100744e004215400d1007003100c074000c0c4021580c10203050403601078208540940c030005501b50400098100c03440d80c0c00312401c406080401c0c03c2c242c1590802e0040411808100000203231541d83c89443c50240d582c1c4682402c02910b4201650911710034140814021028009002c01d1160070402840e0516007068200d40e41d0140180100e0541c410794015050a44002c10000d42038000d240703a020550f082503c0c0c40201e911010825204a030741140c009030700000c1d0030000401e0603c40c1d0b5441d04014102c030005070038100b0590004008400c8096100100d130740d0340040004211414130b44480c200c0645002d0b1210354107149040b1003951001308000c0f030f501030000c40a800c01c6200000ca0704140460400f0211120082c5011080301100070003d030002900303c6400300d09481c043c4221104c0a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 682551600 1250 682550350 682550371
    0x306060e09070c05190615081b06090f1302030a0c02160911070818130c05120405030c120a0e1f0f1413090507020c0a060c05011b020c0f010206 63
    0xe0303948400860f00d401c000e0354200d0f4035001e20502c40389284800c4040c6683c9922668022890700c1d1030740740341c403031116283c1d104c501e0b1640f0041e0214000c1c00016440b450410003694102e94400e01c84010400c1d13000c9020f00613402462031640300c00c00341c119901450040c41810000d105105040784126591882c3c850419400380c80060108011005540311590303041c456a01281402466150421250010030000740c040719089880c03d69840d0a034811a5140d400c0c83d8100b04070011801c008101d4080e0441c2100b0b0306540c1800700c5c6c2444001c00075202e014400c0401c43c6d444803002c2d0000c94058018086810200c0d06100c0e03000504e1038041030381d81101c000d9050000103800c0b80d4004940b101f81211245090000a483c0380c0320005600e0010600d5510000340b0025192a003641e01c412500d0003440082150000d8110103241d070364aa4043c0100c900514145060701680c2c140780e03005112102881c10000c01026108101c2c540125a8280000c1c0444440c80c10381640c1005988a40b8110b8100312039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 682552850 1250 682551600 682551619
    0x6030a051b1c051f0509060a083a0f030222230a150f02030f0a0f111b0d03020c042301120206030105130f110a0306060e 53
    0x201015803155600050708910100003108401502a0950101825101c1c0c4201902940310100e142c2c010320f500440c0080c9005000d0300564810304d1100c0980c02130724425495100880d60301c1c3d44001d0311801908180c010384510001d020040d40c0c08001200703003406008507060391003007003182c0d00b85250a00607090321a1502c103c0001012002544241302000c1c100c0e2004092011004100c140c410180450845884002c4500c00e0507000443c002d420541c401d0b900b0007028086819004c2042183c11400d04001c008031007405011b82c25401a5942404a0400411a501489d83c001c61360300182090340c0b1110403d074244d17460551142c404102c8100802c84440c0094801d0803d2003d540f2454044e105886201c040540050140d076000310240b404010400b1801c10340d166400303002c9004103c20510050010803c8d8085a02400144152449240300301201d5001c1c0c034041d013100344c80c6845e0007010428004502074204081d0410001c050020f880d203480450b100740a1002c11449400080941d004e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 682553956 1106 682552850 682552861
    0x1121e120f0e030f0c1207030b040807060c0806100e0d0f1109060d0c090c050702220c0e0d12140f040503010b09060d020f040b0612190b0603 62
    0x884d8005039000880254002405400300c802601c12240490300300300c082c0d0030070119030301c045e00c56a0381c0803c1004000c1040c1c028103195204400401140d405000126069036003220f5442d00540110290039220380110315007014100000c1000040d580b003540c3c0c84148580340c2c1d90854031540d0b0354200201918003152129888401aa09020492000c0d142e01e40c108507a48201c3c13440b41e13500c2c25100c1c40c1600c280210784215401400001030210300d44100305044d404c54040c485114a010420070030184a07129440f103e09008200b895401d15076103075001c88640011400007440702075034a0a500320a004041c0070504040880182c4071490f110038903003500c44180c2500e1190302000100082c2d95a16540000d010380c0503500c601c8a070300310601141c020040c015015a000340007203100c0b01c82582403141140300b800c10104081d40d41d428003030340d141034885410100c0e6010a05100040 = true := by decide +kernel

theorem cover : BRFrame.Cov 682374100 682553956 := by
  have h0 := BRFrame.cov_init 682374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 682374100 ≤ n) (h2 : n < 682553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
