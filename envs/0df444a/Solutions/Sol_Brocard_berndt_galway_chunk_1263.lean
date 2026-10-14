-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1263
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:03:42.864605+00:00
-- url     : https://prove2.me/submissions/d6c1e499-fac7-4b65-9873-961ea65ca835

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 226978417 ≤ n < 227158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 226979667 1250 226978417 226978429
    0x90b0411071106090d05030301051509030a030e060417100b031c080705070b0705030403030e030306030d08090703060e1c0f05040b0c0f0f0109020109050d03020a03050a030609020f1c0614 82
    0xb20b144003500702c5003000407040000e10a100e209a003a54650000401440309040000140d091224500d030038624000d03002c0c010a5440708104000380400c01040d11059a9680e2031044500030240207208042456240a445844040242c8147d0352940361155850680c00c0216428140300000c1880320380c0d1700a80d180070b0300d030580d00401e0101081000c01c06a000100601da0581c081c080139078a4a4580c80d1524020702121954103141d85103078020300411801c4c4c4c0d000a51380050542c2407400c0901501c0b0000c095151075125040149030304e081c6050ba41079200d001411512010a44169500c004000b050070b95146141c0d445220000320108414051a0840c10080c0262b0146008075140c00c21720b55943d03420720b200b13440811060394442c02a1000d569000c0031800280030301300c514081c000c0705543d01030364900a4210040074021b0104003903440324080c2d8441801000c1e0b121045d03641ea8005410812954031560b6121100009080c07600c0b1068079501c12481030301c40d11904000003a07411010848 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 226980917 1250 226979667 226979693
    0xb27210a09030606120308060a080601050d060905060117070902040303021506011101090b06011124090708190303050703020309071a0d1409010c020d05390601090b041107 75
    0x7800001d01e0004005007262241d40010203034000e8065940d5124a801048064040c1200b0f00ca0400d4030390504c078000b00487d1a07130444004451040714110140752003c0031b80140710010b00b1070b029103000041e090786c00d1600c511006240405440c0c3c035507110384410049008600028005038040f41050100c2c602e85601d154000405050a0701041011006075007940d144080c2240d00340d00c02c0042c0b040c107507085000315104010803006031440c024800140e004091035006101825004030001c00c2c490381d401d000380d001400ca1034081d20040722118078803c0c0380d5108684c1c02c600080c039040000726843d1091007541c1c041c050400182810f02c2c034280354141c50806071704100d61100d1040102007040b610a204082c0c00c83d014501d44811440c000c200c0d582150384020b036400564001090b5000f000d175014003101d03c80ca040f400360750f450b6480b10081d0850b100300380300903014a9840301c0314035103c0d0300001a404d04030755080e00184000c1c04e1000a000c261a910300706980c0d07505d0144401380000b080d85003025 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 226982167 1250 226980917 226980937
    0x8100c0f0c0f020f04020a090e060d021c0305040e0411030606060909070c032609011a0108070c0804030206040305011d0d09050631030302010c0215011806030b2721 72
    0xc06005500b04c0054201c0e807042c200180030403140e440c100034081c0c10803505540200308540801e0194040d4002c58a40b1840141e030396085018100403004050040e82900e0152035070001d6082e9a24041c50038803040300148850500c280f03e13001c006450b0b498031104440b449a005401d004454813030350f1050316103005068085041c800d8040c40c2281001418400d180079104d40a0060141d0404403e11400c482200342c1c40009909100190800c0e40d80008465802000a19189500c2d960504208040d4025500020361050001038000140300054000016001088160340d0300011404111a07840c45486254404900050f80c101700030b26001d006447d107840c6e001c489044020f890150301c00e1401308880000c000c0d030905074040c0141f503030910503130f41c0c83c46140c002001c0002c4104e015a0175800d05100d003148a00d8980f100c40d41c2561150000c030011131b0301403d940442c0c10280754800c0485000385007901080380b042d81280d1002c0000400007206610380c18102180c1060300300003000d907404215a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 226983417 1250 226982167 226982179
    0x1d0702010b03030309070e09072105100204090501030b060d02031015030203010c0c03230403060c020c041a0411090d020103090c0e0103200301020c070b090a0b0408100c0f0c0f02 78
    0x1601c8103840a0000714420b48061010388a82c2d418010810529400a0110384165200705024010300c80d414003441320001f60480d42c40b00b03106091030040c0c58114182c0e00a90300c1c0d80041000106645580c01c418183c074400c0340c0c018825aa0b44052000e001e2040c040070398194094205000440120750081c0384400c0001c070110f260a0301c03900440d081d80c4a10229000181071820828103156101602880201e1a82e03565024408111503070420f6001741c3c00084e000b01e0b6240000590a0f00801010100300d2020b0301c00e10201c45e403150010320214844106c640a142005070000c0800ca02404942e130318a0000c0400180a54580044008040d0a107040310104000c01c808103074040e410700b0242c001c1d84250301100c034096113886802d03c4081d01094460090307005001a0346d4140010a44105540f40e1081240d141d280c00400030300c00c20602d500c502c81c40c580c00980461040d202041d0f400703c444009d00305100084280d50100c89540c0705c07424881c00900b00780c2c07080c400102c41030400034080b4001042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 226984667 1250 226983417 226983431
    0x4020a090b09040b04090503040302010e010c030c02131b020c0a0609050607080c030913091e1101031e020c030c0601080c010503040b060a03080c030c0607141e0d0204230a1d070201 79
    0x170a00715032800703406440130352020030100215a405a181d1880041c01e280c8198044001d40e0080d0032800c2140000748598007200f0a170b858480d081e40008401028075074880d01000c0804400780d2901050324100c2d0082542c0c0f0400314410740189410004c0b6140640018030302215501e4040d50394001c82e420715090b010810044c045655410380c080641c00b42600002100c28451a011982e0107582840122030318903081920041000c641c0c018278002428200818a003034015580a803060802604004081c404210742002701c60000203403c04101800894004c1d98a0301e0754150341d00c02c00c0586500052007040080c00241371842090b40100000d01251916034503582c03860070036007000784800010383c004034407503401c44020400d141d00031886003801c0e00c10f42d1070141c06800d140b1500107030f408030381d00c00510040043d5210307084900043c5008011921140c840401c0490450ba1b000d03901d0200f00340c0804403540b480c14299000450314540800d410b10100c07a01100714160b8010b10f00000c1d0b5581d186 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 226985917 1250 226984667 226984669
    0x71d090a1b0f08010b01080a2a0c1401020f19031506081e01060e040c1106090a0b09280204020d1d07091b081018020901080604020a090b09040b 63
    0xc07280e260101c01d20410104541000300a407200c1000da40003126a078180602d4012a98000345025000310320103a0110b0b10032000440e5005601400a9501e11141d10301c80300b00c9015480f014802c00c2900c1540072070200a0f080b01003500343d0103407820581000d04101700e003050756201c1500d0081c030000b00d070801044403e81d603c80c88a850242e5407001c00071031168410803405ea040c4500c10b0581c001010706008055049c8000105406012000e16010729514804c41c54654042e1104100d114602c0084400c1840c4c2a141c0d0f5881d101c9821044071581d20040208514a001244040a890300c95003180c0310301c00e407010f40301e452040710070080e038120364200100f14401e500f60007043c001c1103910b814601d6042000140c03600d00089640843d524915060204a190040d91a00c01d11704041d450092100e0705c4c1e000c5040b4640806902035503001e0810700155000c0b02c01c0d074003e441c000c00d09807103034449a81e81c1d209120603442442198000140d07550814800b900c9070801401d1081c00c080c2c0006405a1654 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 226987167 1250 226985917 226985933
    0x8090c06040806062107090c030605060c0601290315031e030304080703201501060c020904060c2015070f23090301090501060e07031e050402032a0a08071d090a 70
    0x11f00104d0410351101c060b0600c0ca07405024600003000140c2c0c10b47e00c4d00364120310306a115201805100c1c0ca1440c138001c40151003021000d21003038003400c0d80c0011350303a081543ca126058090060b140d03000e4003800104502010302403180c01a942c0d840c401952841d0785680e98001d032036101c600d04405200c11801c1c60f15141600c20310840d1740001d41001000ba8250f06020681d003424140d10400070810720b110b60340c0060302c0e6083c800340c019500c8640404d2000d85404155030810100c4140743c20211522000020380303c3c001000d089901c400350f1130130302c00c0d00e89d0349040760400201d8038140c000c20a03400b040600340b071601c60304562442c0510001400e18002d440064292241428165483e83d120001405080a40c4022a8005109060401110000718540061301a00c200800103c60744c520004055460501c100c601c0504080c070a80401804080442040001c1608842c09900000d0001c0741c00040003c4040503920030180c07810301800d001040000c2c81c007004080c4181c6006110814002034041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 226988417 1250 226987167 226987169
    0x4030c030321050c03040209090106051c06110708040f0807030b06010521011d061c0305030c0f03041505063a02040f02030906250e010e090708090c06040806062107 72
    0x1006244c4d0340d90400d401000401d190152104600b030740350083c20001542d44000d00701e182c0040d149041d01e60701c0c5600303100000701501c4241c500b00d07203030024100302040b050758000c0c01600c900301216051207840700202d52b5034000701c0c04000c140000d10000718080d9070240014040121841c103181038829452500135203000020307071081018803801d10a0281c0d5003200090140c1c0488160b50140349500f0406d141e610701e0503101c00280c240000000441d00b075226000480740401c12207210180e59042038641f42410381c40a2045402c0e540c9410040341561503c1800426030a40c81c4c031180024030024079041e03a156000c4008080c030000207901100058070b403800740c00c2110f80d9038400181c407403070810b0120b81404402840c118603c0801e800307054144d03070000c0d0a04115050340c81c0c0044041e04880069800c0c0101ca01210340c17000d00f9600300030495074000c600318406c18400c07003641d10780103281c0148441741c0258003440000d5008a00001e055082004040c03c000c8000301c40d017164202c00b800e865040c0030403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 226989667 1250 226988417 226988431
    0x7111306091d12040306020a0512040c050108010801020909010b0a0e03150601030638161214070c14280311150a030e010b03070b0d0605040204030c03032105 69
    0x40319a194615544024254a9010800c010740640b001c0b102d03181c0f5841c0700f240001014682d0100360300a119104209031928405440b580100a04080c00c12031170a440711b208940c0005c080c2400426a1801802030b142070050240003d42c117a42403580c00c5030246c2003920100b080040841b01d00c4101e03541008001200312034052600c0c140d013411000103064a2640d000b520401c0070082440c2140620356003c074002051a02481c81c2c0d24800c41805403191080b130300d00312200b200003070100d001d2044171040c1441ca00410703281c80c0361589851819038610702031004041c1400000410402c442d1b03003e400201c412840041c4003c800b807aa00141c0700c00600f460005000040c0184014810450350350454500b0b4041140c1d410310103104000160464401c07400c49008242d100c0c0124201400d094009020000b001410768035200e44821401181d0340000010f04801400c2c120b00090030704041c82200c003a03a42059083c0113407401d41e01d06031504080030152001030945440c01c058030704038070302c2000d0144072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 226990917 1250 226989667 226989671
    0xf150c050c03190c05030d0804060b0a0b0a0323060307060804080409020c07030606051804020d0203070306021c15030309051c05060708150a05011b2303040302130b03030711130609 79
    0x55411308045000c52a04907a0096004030201c0c0392094201d8545540254440f0300810b20703103030400c040b4400d228260b03ca0341c0e46140c0403400e80801905078000c06130100220311001900104800280013041c402e941d0590140c00c00b58050280d64890880c09030720038080c407009450a5554003140e0300b00e9004104904070b42d005075405004005490191a00504044899519500d080f0059007981080900f0003445401d0708424801191410b1200c6d070f00440e04207000719218041d14260f41c000071003817248500e46034584811a803039a000406443e09980d010f9940e08032160801d814806600c2050401c0006e8030b15a10b007450010b4020001c99100314842c1e954628a0b0038503480405070740c0440d0390178031b00c9409402424000c0740d0740080e21100c1140032000b0000c000c10181460600c4082c08030945180e003414812400f0500000402401200d100303484010220249103110303001c507800c0c1580982c0c180c2042280c000801c90f070195060140307000400311024400c56040701d100300c862603400000003075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 226992167 1250 226990917 226990963
    0x509130c110102040e0c2803022a03180d140102040e060d050c0114070506040b09061003110105090117070309060b06070809060706090506010e0f010f150c050c03 71
    0x29500100042289800d00020b50502e41046000400c0801c0100500300355140810b102c0c10703422a6104040400d8883c0202d4102016041001006582b001c18018920309422800380c4294001c80d240140240030140030b51b080400b07041d15501044840c80035075500c41d0110240384003088072951b82c488400000000186c0d1145050821040c40400030825441603401c0326125000c03c03000710f104403105009203000f09911400d4404580a0b009064001d40f41e4072585c000c200400140d0841c02d4002c3c1d0f121301c02c9824558807035032410b0f0346040342d000003098841c0024250344254000c0c03001c0c000c00b103014100f100600140100c82c00e00003074105c8001c0002034480d440384091081d10311a03000020300903504c162501e54a91074850b92441441d8540f40280320001b290010700005502c240c3d9039036444420b0ba15030f0759441410a490a0055424240c0b80200d080001943c0110701d00b284100c034002c0070082d103003000250701500c424442c802d050359140034165003400305030741c00c1c810000c41813203001c040702c00381e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 226993417 1250 226992167 226992191
    0x9190522140103020f0f150c0c0901080f1e0a0b0a0506120c0d02010518090f0711011517011506030213050303180d0501020c011802040e0d0f0f050913 66
    0x1440301c05034403a488840040c01840942c0b13451040034141202a21410094040c80002c101c840c500302c915645142e0000c40c000810035000700b01a40004c2e1704031a4801c4990301c40c1203803600c036401c00700102c080c0c2c0d1211200400f82c07514840d405109040351700640d00712107240e86800700e02d403004803071403143d00d5550410048a0714103c61300c030a400313202c02c2c014281c0d02480004160091101d400280c14030001140240c14121700c081c0e0400c1160012f04026503d003030400004a41c1340f400d82d4413502081c0000c140a02d8103405224020003404484420504070307141001e506410307108001108c1c0d03907540365000c1003840c180114441c0c00615103030380c0060361444418140049802c00c0c0c1c00003032082d00b042003c8a5140000e240007804458121403040d00080107142090080c401c29007c90b0003542841c089070308541664070028002030090701c0c14442904500107141e1a454002c41c00ca0200300d40d00c00000f41c0900c0344504040400701c6042407450a00034200140e98003a10485400d40151201442114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 226994667 1250 226993417 226993421
    0x160503010c08010303090b16050f0d081506040909030507050106140102100603052508121308210a0c0506041101090b0c03030703020a051207030e1b0609190522 70
    0x1d18a09107010b59440d411a07400400034803a9100701e440222000c03405003010070205a00100d9507a21004451500140900040c2ca484003040c19a002c5040c032400102e0481c1101148099008010015440c040c207129000004002080040d420010184680030005100b44240401703401003200c0780f07c0352501034000900d8001d40d070503030198203818000e08000241e0b0001d14030042c003003600c80c0800241240605001c00c10301660242c03980740b045080c0c0b6a040000440100301c907407921417032000c4803520764400a0b0b862040c00403000c85210014128111510f040e8050026070000d881c2101e01108151241c0386020740c144c03801c2d1004006010b18001c01d41e00314400d00018562000301504202803100344075280c0c0001848001859000100f000000384114222400c052014240b24003e090200d0000e00030902003203210250b2061050100c4a8502d80306820b42003040240464540805041848186094040000c103540458034002c01c0c02c0d560390300d01c0314100c0342e4246080785005a504030002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 226995917 1250 226994667 226994681
    0xe010609061508062b0c0f051e09060f030f010b0301052a0c0106090212060111010e030a0e030a060903050c07050a030209160e040204090603020f09220c0816050301 72
    0x5a501d01c0d900c03803084180e81110f021503100e1002c17600003446104004140c20305c1141c104180c1440c0060100c0701c1c0401031005900d006682e000c01c24800080c3e20b58040c0202c55001030445505044940394402c901d1804101241d4401c8000c0d080429400301807010900c1d0010368192004c159440342043d19160500744556540924a20031a00585002d01d0b0f05001040013403645000e5035200042803400340304250072030b200a1003900011580d940a01c43c1c3c05a072001c0c03c1d10413900007940d515900030302d1001402140390740c40c0b802c80074514000304841c060304c8107131440030700980500441140601241107403140d003030001c0c040d845890f624510140013505040e07461300014881c04d042c1805001688070780784043d0340004461503008003070200328001d40d41c1100070075016074801c1c0001004240480f9a42084084078801d4903456410402001041141c450031290344800211280c0400240b481008800402e01e0156a5404510385c03955009400c2640d5680400c400d04c400d0b1a081040d42800d00c1220 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 226997167 1250 226995917 226995929
    0x3011d2a060a08090c100f0f020a0c06030915020307031d03030f01060302030a0e0618071a0a30090c0503010c020a030302030919060903020717100c050d0e01060906 72
    0x55045a100e80000e0700c0340281c044240c1000002c0000a5098070704210140318244014014100740e68842001051012031580740d00016510002c140700d454000900540d46a034810030707122105003411000c40040000c40300a460081d2014011944e801440c40198001c500940e03011070f0069510000c0c0e10066140c10410103994803c000300074100c1c01201d42c00f410f42d081840c000d40d403629844840b6020f4040328070145414041d038410b10840700d2040d071040c1c5083c40e2a5094808040d620007802c41401c0000c0041c0d0103e41d0100702040d584c91080d15040003240405140c0000c010307201d0344681009101d5400c000480e0b0340c480e114024441100200002480300b100240106003a46030000e4845180d240002c0c1495004808505810420b026400083c01040c00c2c165102c44039044c503c1c080c1001c0c0c0780c01d82c0507000d0118040381c2c0440390481100c0f46001e00c40145017004d120001c480080032885110380802606001c10342d4915118010294024840c0002083c0103080c54840000c80d81d20358045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 226998417 1250 226997167 226997233
    0x3080f090307060c08041401140a03061a04060e0d060905030313020301110408031e16030c1a0106090b0c03040e01030f1104051506030a02040e19200403060b03011d 72
    0x600015400c501220305031503a07000650310710f007c180010390300200c8988021074000f0700421a451043d9259200b40c04560404042160000c24403010000390301c0780f0701503140051224503141a460500103e40c0c40c000e4843d01c00000c0423001c1b92540d6046800580392a484504c010301e80e02c0030351800b4006d4800c0c0c86505070b5160b191038035244043e030396445101e41c0095907510015801c3da0340040d59050711841c0000e200e828207401410302d0001c2290354021412560078010b280d0303510016180711403660588600d606c44d040200c1c20030030000d505400052041000707110401c004184007a80d84010346c02140300d0865041c0c20f00c0c1d64540031290380304406580d1f018901c0d09082280283d1810031060001400b03070395041d5241c40b0510707100080c0c441c503040380603c00c9001c401d0180f0350203644944c10744480308800410407009100b804408510504c0b110721a26202400305001084444d0300000c1140f03001800000c0011071004a4079514400c200d41100603000a15007080303403a042925031203241511520 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 226999667 1250 226998417 226998437
    0x9120406080711250321050901110f070e040201080703050907050f0109090624020303131509020a03030504060207050402040803040b160812101d010608090703080f09030706 76
    0x400c104001088002041032459518007004428410032080314a0455000c003c407800ca102c20018600f203105c1122510354205004894680070030315a082060300d6030311a0b2234401941d0044800c0d95003aa06401180901144140c0c0c05004007d420f00414036081c1101491074180009415504020045014181000300300a096600803e0b800155407007160700c407296078808401211104942c2d089400960715149010484101c650b80045045401c0d10b81112065041c050032600da010170b84400d060002c40780140707000980150214045080c140030001401d110f90340015951051507801900071400014041c40450f50620820001e040c0a540561600346040802a0b6900c100d2280c200642c801054584a2284c040e91146043d600b0241e480d85410300300702c210029103416100e1846041000400080d0441880301c1038940c040603030402e01182e840e050040c1c0380010300500103602402070003004400105107101400c0d00e03841c00310401c0e80740c0c040321003403524104a60b04000140300003420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 227000917 1250 226999667 226999679
    0x6010e130e010f051e010611030d0e06161e0c02040b04050a0e1608031e0c060106050d06050114030f15030a0501050a06051807030b0109030c0b0c010b0f03121e0a0206091204 76
    0x1c4c1550440300103203041045005108e074003904500070b14100d8500c690502e0b6014140b00c0300040d0583c0a45000030301d07101854003440040d03401078850120541c84000849407200d4060044e2801da00540c000b80c004140001c250000408603401181d00003c4c1c50707994004260144400c101c8800f900070240d1218601501307001042d907403400f82214114401c035030198036504405405041c0c50310071032a10111001961640c1d005483e036000f102d0823074a810b28007040010190300c20741001229403400350110f45140c4548104009810004207448250011540d00c89103031b45040003601901e501601c00021942011403881058072102d07840b01d8030402859090406000740c00c090a50402100d04001640403140001030710b401c2400e03400901b440188020000304800350714000e06c05030030318900800c0000c0c203000c108010303e0f11032a6003540540c4490b09a265042c8180001c0c0740204400100c05007071100101c0305240c48d407000c411500160003840038040b00e04001c000c003440c61041201d91908040c1400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 227002167 1250 227000917 227000971
    0x1c0218121902040b0301090b1603052e05030d050c1b06030c07060e030301032405040507050d1b15020d02030307050909070509150405100504050906010e130e010f05 72
    0xe04070040d00c0c1c62440210866030390354130180050074041d000f8000c1002d1802c0804c2d60500485603605403415009216a0340c41c03003486040d1050b4080300981d01070307001590300056450075680c2c1c04200b000780c020021500ea03800b00001c000d0b0303060750341da0f103030350b494180340780c03505090320381081d02c005c2c00080580074100c0d611201500c1d80700d0781407d240b54403402c8074181100500082d010803c12404000004403e02442000310807100740c0c842e14030504590500070040c12644100d03400b901c01e070040d4009201074a010306040101a02811080c14655490810f00c65046826402031680341c850141c0317008415014090b01d4a00580c0f4000b950542c9004800a48a4450b64009c988650781e10720024841c140601c040e1450144080e0040910340d03140d40c1c1d1401d190748140505403080c0c51105000792024030800c111003d89001500840341921080c0064900e8000310303c10aa124484103024900032445202c0c81c000040c0c04800410702d400d0f0b4040360800c440b4080c02003200c0c40230b421300c004c035292201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 227003417 1250 227002167 227002183
    0x190506132403050c0f0d0b0a020f121303080c0304030905040b130c0f0e0303040f090e0c030d0203030402040f06030b06011202160f1b18050c1c021812 66
    0xc2080c01d40405a034403602062604001034012070300c1d0110500500180f24001034005a4015a0928101080060300900300c42c00401d2000107100103180e150b203580140a40884000d0101d04000303c03082450b0000138221035038030074180070301182421f0560001c102600030b980510501c1c958241500d004009551a005850295480300c1010700300307132035034905200d0455400c0001c102ea6100880000d1061030a0ad241d080041e440c8080c0409919000c41258201d5a80c0b207070b000c010070b03d80080c43c0c0180072803007500c6410303002e0350702d20310186d440c18040000c03002c180f90302855591034184104001c035400140814200792900e082840002c0c10541860340208090171315110b0300f42521401f40280c81883d007000c0801d441d10fa0f072141040301d0702c1300c4c190031305106545000711200140c1203c10380528600c0303140c0040040d660700741100f0b101c0c0e520032a0000c0300707201e00d1031074455640300b60213800810f1803032146a9940001d200c0402d40011100c101c5000702151944402a840034010760343c0c1400b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 227004667 1250 227003417 227003449
    0x40c0b040e0c18091f0e09030d0e0c0910090c0801120609061e020a0e040b09011e0801050c0a0f0906120b0a0e0106030b100c050a0809040212010905190506 68
    0x1918003500602d0880c01c1005600003010380c001340c0b4103032480715508010902806018181010049a2052088003091103501c00100460400c80c101c2d040f600540f00103170710307084680290f500f6a00c41e512890807807403081e0005284403541c180340008480c111081102280c00300f0900d00c0042c001c3e200c0682d9404242754104001180d003035410b0900d400240450207030f04c0074502c00580360783c6049180f07402808076a003644e16904050b1204806010a9818a802d00c50f4450070002c010f00c1480c1244003299200402c4507a11690252140400c600f100c200382c1e040c002103500480c1c5112015801154201c0d52803061400207011745c41c020303001e81998a0020001c021980300e0407055120f448100c1c0c010024500148400120350307460001500411403618100d000301c180b007042d140740c14041e022410b15198040020715035a4882e440345044c9401c56110b8070b07400b85d001c012000f60301c2c3c004410103000e40180b00d4000780741e0900d80b43c1c0b121402d803071003088000315040004100442e995100b1450320014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 227005917 1250 227004667 227004691
    0x903080c030c0d061e090504020901290a022d0d1202070203070e100608010e010b030613051602160308030f04030302070c0e060a050409080318071d040c0b040e 70
    0x461a0b8040d1090254441040f8154500803001a0940300c00711510f000780d2840ca405072944c0d8031942641d0541e8800c44d030103500040d68a004001801d28069071001c1551003500c5429508910364200f65242e101088401c0140e00c40c20081301d100c4242541e4100030001180b0b180000c2d14450843d54441c0d405510000510070181103d000711025901103d00c2c1580c01001e031f41d1843d0b243c140f5031043c140c0179034100d1078011000d0008a4030307500602450f070599581c3c640700c5529a00c2c086e10f0045941c0b008120790b42000c0074003001c01301c042c124010180501d0074600608001101150004c0c5005c0c0001030342c0d91030072406c50701000410400021240c00060742002d621159566003002d402a12907100000d0029002c07a0000410040398810140036240440e030701504140d40b00108400d0740c4a03502d014080501c100301103804e00c2e004501e4078149018000a07105010744d1010045101c10600818a140c0360300034080000304200d8045110290102a181c107043c01d007440500108800005c0860722240c2c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 227007167 1250 227005917 227005921
    0xa091109070212070303050103051501120b0606040b12090d020313060c21121107081204171902010e0d080c0a02070906060f11010b01081b130603090201080a0903080c03 74
    0x20302c284a030061203200b4070210b65440a591a0050040c41c00b4801614140501c0d400c0e4061140e17500000c5049546800d0000600750503a00d030082030302c84c00b0b055561310510030400020440c00c2c80380134101c000e4911049112600d08030b103a42d03052040d5044e1400454004001c110b000900e61440402642c440d850300d004600c0103840d00300c1411540c036103024162105d010503050143e034420004004521103d0003486403000d881c150081502a410b00100b1203402131182100344c801103511158814000d0861810300c821641164202c1e500004014412161842d26000c000c0c0d02400395071f20b2030070194001d15141421241c010701e07905018009820191b000071f44801c006208101c004050905c0d6141000210760310303500500310400b01107015020904044106076882018402d2881807201130b107480c51541d03668200c2c0c0500d085050070318074840005000750b004000e0b48103400310103003ea6440000e460346480c000034002907001011103c0f1b65040003400c0c000654032030b0119401c0003240c64016229 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 227008417 1250 227007167 227007181
    0x60e0901180e0f010e0a021504050d0b090307140303060f09010b04050d050f030423010c0b0609060616050105060a1e1e0801050915150121060b1804050a091109 70
    0x100000d100fa1059801c251116480220200d280e204041c400c03948482800746100c0541d845019901c50964041d4016442c0f002080a030074495500560704800c0e2440c19240d5900c07036400503a204143e0034507500c00320070840c080c00e0500145e5618041190310454561401601506074807403806810f0050001139003000400408111048801b40b11005490300c40c0c1e15007842000c00682a0090303010f1910b1b4403140340943d409070040386c4580e40c1080c2c5540d03c9955500c10b01c145540044c106507040341d001c1240301381c944041407200303080c24450300010846007480c40c100121480c20740c005c400c50f0040541d1143c10403074081e01042c11241412039203503c07401030303182000300346210364001130b815420b10082005c9080c000c40c01482e482c0403114401500c1e12a91010181d0384200000a80030504200405050100d008195560001420b001084075500d072000c1c44502d4000f80c1c4d088c03c900e883c400e0310042d107103468000c565020390780c4035080007100d501340c80d1054000020300c084c0f80501c480401180700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 227009667 1250 227008417 227008423
    0x18020405060c1c0507031d21030318010c090608040201030f180203100e21070c180c05030f0c0306031006080307110d05030306130209030610060e0901180e 68
    0x14030006000d0340d162101c1c6504142c40d04504140d880c141c0d0b43e501c0001000324080e0f820340b190190903507901402010601ca0422440c03101d0445607903c101c040c1101c043c500010410395400c40c0310f240241da00e81c28120300b0761414864010854040d80d0400c0c580b0300e01b483d400b0002c10b003111080d10f440384451700d031400107078001c00c04d0520100322700e0b04000010840e40c61005402c1440ca01c00d40803550035a8000607403c08407906801d03141c1c07070768000c2136440300d100884507a0718103460103041200c0d242201d9039981001003801a13102c8060546100c0c4000d04d00001b51240e1181004a0f0a00b5440c500d45101c8207258518028641c8034150f80110106507035840400c01c81303103400a500410010143c840d44141d0b41c3ea0400c0008a41140d81d01c2e447c0303501c80c2041c02d803180c841d99002c1d0045046840e8101008840c3d2000400b00481950070b118220003654100034150144480d00240c440180c14850010030b07402c0c056a04034000c040b408010401c0c2c10101620754803502d28484005101000480c910341 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 227010917 1250 227009667 227009669
    0xb190518030304090504121107090b030c0d2109060f050307112a030a020d0206030402030f0d090603050906060a03060e070302060706020c1c2f06040b180c0a180204 72
    0x500741c800810081440340c401c1d4009400355019403049008605000e07422105220328400c000e5482d04403030400c118410682c0c001030600350000301910740703000156022079090704403d001510501218100c0e90805814061454414015403422044083c02c0010103041850440e00a174204240000020301d1a44110001250100e03400c0555440c6440003102d01da101d028007000000d0004000e01071041481c00048860b01540c3c00761144820140312b030200100c2d40c100030030030303038160007001c560800c059010b02c1b219000106585455182c036040c00782c010100e41009080110301c0c1d000800b440050740e00c1010b0082160307031000300801d1034261380010394100621580005d401142c0401c0543c00c02543c0d030042c100d06034014049070141c03003100c2c0503c0e1a1050740c00001d004241c0c6403d0401c0303505400c074080861030300c86040b03110361141540c00c941c0c5001d004403000c0d00c0300813000d41400017901d003d05101c1150780060b401009000c03808400181054018885e08040e480e2f0748400d00c4540003e50107842c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 227012167 1250 227010917 227010919
    0x903050604140709020c12070305040312020718050123030322031106070c060c0f080a020105040b060f0f0915060c070602160308160f0602030c12010b190518 69
    0x580c2a040030b2400780703011080024218998083c112020503400e455200391001c16100c00c00801d501c070f12102825429a110300400e0301045170801000c404640701c40c2e0620000b03061a4000c0940c40e04e80741000110098001094040760305083c010401004e401c1c0d100c180b0313032140300c4104001d50300100000c0e203184901401481c044880c00028401140f501020904a0b0b0040407a5034880c04210304200302c922400000401000300d0b1802030004034815004034174568800d004d9030426090030f440f0071525405c81a807190050b074403842000300300076420a450b40c025200384c82103145d0001c01800515808078244410f8002d42c2048001189002d24040d4080219405041c1d00d41c0c0f0951079903ca6120201ca008c0c00380588510826040c1c030100002c1c4420403030ba0400900e60902e18034900446200e480c0d05000e4600030601c040074000301c4d01602c000c0d0f006440c0007410560359031145000d41c0300c06038160f000480c0070390103002080100c9080e0f002d000104030a440d190b6550005049d80d8100130ba8000051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 227013417 1250 227012167 227012173
    0x10302100c0c06030c1803031b06060906030b0402041a010203180102070906060804021f05040504090204020702030111190305040f030806030a29010b070c030b0601020a0f0f02091b03060d03090305 86
    0x4a0a030158040041c0ca45c40c1e40c0c0301543c6420300c0392282920071040c4801400652240b03c20282000003000d04503225205d0000031a205940e4401c800030b880c8283c006aa4084003030302803008514251261a441c2e03640d80c641c1810b002000c4002030b44034020800003e4151021024003501c5038402d0240f680941003403c1c2c1040050b407180783c01888800c084a0032130103800301801000d40711407051180d00040c101a62928038090030b0500340000703040441301c100d0700241c0a10440f401179030300b8011100e6504803000d445864007640081c0248103000c1000780341c00d1629100070300000c02d502c2041e0155064050805c69015200c04e00030030716180045101034007800030132009511020399214141d07107501402c40302c40d030641d803a07d188080b244905800200400c1c0d440900b0000030320400044d5602c0700d414015606c000a464450b510f601418490496000008199981c00c601d031550302c07650801030942154000ca00c0ea034100611301d220140689214100750f40c0c00c0301c02c0621660542000d95880025 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 227014667 1250 227013417 227013419
    0x1c030e0a06150e0c0408010b01091203120225060b010309080906180307060503060a06032d0e0706030204080d05040e04201201020d06140112020f090a060203070302061e010302100c0c 80
    0x221a42c0d000750203006c5240d420003800038151340c41801c100c000ea8040301007000404c600c0360b070700b81e4460310780b000f541800c25028482c1c00c140550710180510b10312120700810508009600d000001c80f00700d441c0c458103240c5400c0e070541c0820303043c5d400e6800c8200180c401c00d0b52140404c040c0c040a4080c1090b0b50b9142c484c020010410540c4080590702405054031000102a100d66050341074a20408600203c0042d48003116078032082051145200002810300150080d80402e5041c10040c01380c00000c08640c002404001d00d00c5c00300159074505500346086410241032050749007403080064809024032803400b0710940c0d89200030001601e2000f006081e49488420080a14040d4100e8800803803501d01e013142c00640b00c005030112240c03541c4141d560b511450720a03464940207400000304200c07098004c2c0100f03501c03511000b9115000d0000d07a002161142101d28000b89494001400964129072116100842c0741c0203003a1141900d42c1269189820146d00c80c0031900b05003015405070003000030ba00c3c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 227015917 1250 227014667 227014681
    0xf02030702100501050a0302060702060702010c02091017060906072a03200d210603140a0b1305030a14120a05010602010e0c03060105010809030f07051c030e0a06150e 73
    0x6048000040c0c00b041442142c0c1c4e1202000074400c0750f844040d4001d40c0070003070380e00140b500c40b0041500380d00c141058170724541c95801040410303c089501614005002c0001d2201012140d807040a4087c00d0f4000c2645141640e503494039403c000d0404001d1001c004c00f000d42150007030004512210458030034440039881400c009003050b51018880c051520f01c445a804034010210341d0600c0041c494840c0c003c1780004c0001404108003206a49a0705582c902c0080300141882d0b9001c0082210600100000080d0741040350071020040c1010850382c0100e280c0000040b000b02c1501c131000e006003000300307400c007543c02c46900354410788502544400701071007005030880c2d2540c0003505a030b80e65402004085150a0826507401c0c03821080c82c0c0c16070052004100c1c03584600a0554004094400d403424924200c48501e410303082150111119040035840c00e0f05150a416510721542c12484c05020503009006002d80f10030328032038080c110a40300e08130b030400c400c03030714034010028001010442c5091030070b00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 227017167 1250 227015917 227015923
    0x90e0106050109060302071106090d021c0b06031b0d060216060e0d03150b090a03051002040501020c09061305070201020c0706050d0b0609030d08150a080c180c040e0402040f02030702 80
    0x802001c0c00310b8204000803411303610030f109903106617501618110351100e04004204603504400d0071558803010344031001c00161900f8a44c9449207007042c071200340c03062103458070049049000300624004e9204c0314071b07822044e01a890341009401d0544990b40780e141a4180840030f03218896050005402440707241d010088036520410a13140d02c01c05460303150b4020142113040c0e40d04541e10500702d5036000780074072071003400c00b004290f4548024840c0d07003070613966070f21181811000191074259550101c1c0400c030710350b01440302c140c0341042103904045915111001848204110104204a968410000c0c403007500135811203032404180c2c1c00311007038076640303180c014010b500c41807030401d81505141d5003403c1c904206090384c1c007261004002d08107801700722001301c1c0ca910b00184143e80e100c021b07003c168260740707038071100d08060000300016200410101d4240103410b80f07828508021000c05804010005a140b0251402d464484e0120307642602d440c000035018103e00600a6551032002041c086215000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 227018417 1250 227017167 227017169
    0x50c03040b0109021c0f02041a04090f06061209020d0b0a06080c06092107030605270f031602010504081507091d0103121b080c010e061b0310090e0106 66
    0x800c2000400e0703803103201c0d0005902444410241d0012545c01e460010411900002040305e042940141080e60711081241490601d441c1001010000501480700303800c6406100c40078100d80d14140200ca182c0a4000c108100b80d40324052066a10701ca0300003190365680d801d60b84241c010000c001c00f4204000c3c82e400074043c9205401207442010840201d038105841a5582408005c14021310b5401c4440426400c140103401d8500d030340500741c40400010601d101e018019004c1407400104982e0000903582d050102034201002036104224016030841c0c00012603050800410f000308070094244010f071134602898004030f8060040000b10f0030b1410072511410310404d000d90b182c05c0082e40c1c40da484205c024402e40300301598071842c0010702c007041600219091002c00342c0b07046400c001c240c42c1b00d000c3d00c640312442242d010b400020104640c550034000c6103620b0510b00c01805240c1071042440c0b44204083c1180ca043c0500070000a40c198819500310300148400881805002050500f2900034465 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 227019667 1250 227018417 227018423
    0x1020a0306081504120207080d0e040c0507020a09020a030902060d09050c1f050f0403061d01060506041202120f160501091703030601120b120703060f09050d080901020d050c0304 78
    0x1d00040081c03140380008200d081c0d51040303140780380e140d2550b032915210544403951800c150310071003a002401e041e08006186c0395902e25900c200808031000204000d59a5110381d00e8108038052000d034025964844800040701c0c1c08030801a55120406800e030b000d8010740c103029511040c08522141c040540d80c104200241c4100180c0b0000200da10801c0400c5014001010407100e034414420b1045008000621841608840050400c1d585c3d60f035490948280c5080d000e60480300a005080101c0d03340503050150100b02c034014100f41c1008290605240c02c1203001c0c0c420040724503400000b901c180960020400001c041d9102a15409080d00e522943d5120b0b01d80000c140b01c1000608090481c002c124003a021000703503146480d14801152616120040340c001103541d6802010581e40e620070800c50440c40e500900400c40c990f0070990101c0301150348100205080101c2d040c0011004903c4094200307031801c100c00b0b00d48a0048240c0207010344209182d83c60310740003d00400b181e401000d544200c0c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 227020917 1250 227019667 227019671
    0xc031b0f0603040b0703090f15020a090501080108100b0f09010305030403120e0609091b0309010b0f1206010e13050a0308090d0e15070302010f060b040503070e0c030604050903120901020a03 83
    0xc0440a000d01ea20040301c01401c070b40018004500071612a8102e07000c400d01a101c0030429604540307882d00705588110401081540c0001c5042c102504640d8030001480e0908007104207601d0030400d5900c0d003410020750f1030700c1c075a13454902d0042d994485d800a20035902402104196850b450540c0c3c0c0c82d4030900059030751000e0899040383e000e02c20ba200080a540c0135192a00700481d001c103000504401030701c1c0d44280000400302c80c81c016040307000b551003124850004034004200c1c03028864000c801c10907440c0120304014041142e04000100c4c6411030300d80c2404518aa81c0706012503400c01c0d02440010b0180c02150391820501d544150030300e0051030f038a0241e400e40c4521500540f90b8048a8681680100c4140c04c071101c0112030001406d44d850007400041070a50a80c0484811034210b0313000410405400300707061205041c2003285030040d2501500121050500e030240b6041c500001744090321842c0c035440000e401000038400c1d1500082d0b0f02070120900c0c10710600560207900440d00a80c0068 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 227022167 1250 227020917 227020939
    0xd080c0708030c1510031202010b040507120e07030807080906160507050906090f0103060b03010209060d0504050f06040803220515040b1506040b0703090e090606010906050c0d110c031b 81
    0x2401c25041c0b4014a0951080c5c1c1c80c1500d16603c8444401d607030b404039000c1d0356880750190745a07151070041522920072503032480d400d92003c201070400c45031044c884004c40e0f44485030a0001a40e400100c403140f9400c041c40d00d80f10100703280000c4480c458005451415280813010100304400011402c0aa6004840c0c940c3c55544040601c8010300c4119000c040510b031010040001c030384940d010000c01000540054644500030340410b50944c02403002901fa15900c0b0f04000c14841300344102c04448046c440a8240c9060031b440c1d00120b400701400200e0300c070341c4040000050020040c00e90706810b511000b91640842440550003070b00000f01c1e1b00b42d5400c00300b04006a84c00480351002c0418090049c1030904282c200f40804015400c146000c03401d1149495003c500c5d500d800c86183e102d042d114004114901c1c1c507a0004207014243e60250b41880001c1c0f12925404901203500c4000c0401c1e40390509801101c0c0294a00d000c0f484a9115054003c0400d0010000c42c582049103800c3c00580e17513038030701d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 227023417 1250 227022167 227022193
    0xf060501030209060d05070201110414030123040b130c0602030c010e0c060f070f08120108010b1e06031e070507110a061b080f030c030a15140d080c0708030c 69
    0xc0c0c42a03401c804d03401807040012103150300940e40b00ea90842500c0c0b00000e138907000052810708541c8607800110300900400301700381943c40e09005050f4140350103050703c106601040d94100b400d2601600003030032020031720002014541040503103075820382c0010880c0c520940e900e101944035030001804488070f5003401c0c1c5e0801c03220030000e42851240c40140078240b40c18241011030402c0e80000e4000c1358a2042d06039000c1c0402d4a84024000030348502804031000e524144030300d0b00b1504010b01d42801b4504900218240032090320b540c0da120041074640550380e64a242c00d107615000d0100000c200c08280e0003e00540c258400302511409206030709128048080d18204800a5503d200700e8000074280c80509501111518100b03006a1042100e181041485022000746400031a113020a100c808400c000302c0088900901684c10b410040000c080780c2071114130140114081036a82c028030390300d44210304024a0310116100c1d02440710549000d1610b80d6039a07038695005100014907881864020101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 227024667 1250 227023417 227023421
    0x7030c1e0b01060311090409081c0603021815030a051b03011e0207080408060c030a18050a080306130e0d031d030a0e0d06020307030603020907090e0606030a11040305010f06050103 79
    0x10782111201c501e0340c0c0381900c00c9024002075907400c600000140041406a1110b01403100c90604c0303000e00f00d03140ca400001c1c00c03d0310780307515414640c40b605001c400c00158071110708212000c104802807400790369801c091100b03058445d041c075681600c160750615003070200105030500c4050f941000b40c18110351440405003030f02c0148020840750791000c050f816400030350368010600c043c031030141075003015980d60169042130070803100241040000410040da0078080e10520f29030074050110785001e42c116481d069038907200381c40000d0903c0ba000000c500180d031681024003040c940c0702d0307040c0100c030030400101c0e45a0155004031000300e400d100c007044c8040582e4444200c0064800c2c015400c000b03442604541c0c0c1c01140f0b5003c5c1c0c204548500c05800719a080c0000c40c401d004984000c159a851032060141014000700b40100704680d03440c0911a03180694002e030f401100445040703403603881d003415590050000051205442c140020000304010040d0014402d001d2800380c20405a0398038801902 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 227025917 1250 227024667 227024723
    0x50a05093c0303090f10020c06040314090303070f06050c03061e0a0e0114030d0206060d1506120b0a20030a020a02071511010f0605010e060705010e0307030c 69
    0x1580001808212021180c0c0d02050010070714600c90380e0309414040740d5402d081d80c2c410790f5140f030303603401141c03648007682c00030030076800d041d02213520461501c03007181012500c0e80310140000301001100300003c00341d1103106094440d500c900030140c0e41d41b1492442c049094260001d8101c41c16420b0000089480c041d01007600d01c40c80c1c02a00d20361301b901020800110403094a006036070700c603000306d01c0070940354000a8400e0181c40748504d41400d00003102d003010302d032040700c05c0e510701158442130800c1180d8942c09401010103612071070345103030f00d80201c03a43c80c013502e9941c101c00312a160034030090086c481403080003030050044840400407403441c4550408000801741c1c2c00100d0800030408200074424590007070403420b58600c15078207596202c1201d0380350080c40b2200c240c00500e826103000c90441c020300c00c446110019442c104181880d110010784070729210543c10b8450702d0702241c91070a1040c01e40041c0791510140c3d09680e0340da0300d5854084c000c4040b41d00c0940d000115074003c04204601c250b0012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 227027167 1250 227025917 227025943
    0x6020f1917030702010f020417060619050f0d0204111e0306010503190f05040308161715150301030b0115170a0510080f071e03030c06050c0405090a050a0509 69
    0x3666030808a80001642d51001c3c01403c111743d030303560001c100e000e074074406400a4050081d039850b045500782580703450280081c12061044c803074a8001034010807015000c1080f00c43c19a100d03007442c8130000001303050b800d00c0180039400034104109024400826001030050403c14252504001045aa5084280012111140130800c200040b51064042108450486041c010007141c0c0200b00914041520000d89040740481d01860620203100411914072241b4070309441d19a50a45442c1082a440c05018092800c107908441c0741551503120801c550841380030050b0b078184ea9594900e00014884424441c90f58a0049002480465842a241c0984030100074143c1c07201038940141050007494050718060f442c90200c0d200185148d8140f0508090f0300e000c10203040350750315080000400a01696040c0d00c60094640180000f0760020080c0050f99089200010f0a545a21a081d003900c900e4220310b500442c983c041002140c1c00d0780002e485640560001d00440d181d10079aa42e4070b52074440a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 227028417 1250 227027167 227027183
    0x2090c0721020106082406062203060b01050c1905011b0c0309140607020111011b0806040507020f030a05070c091d0c040203010b040e1e0915010602030703090311040603050706020f19 80
    0x404c06c800040402d640040005240c1413501000d59210401d440e40000c0c3c40000c1203a8000800a0210510070510503c0c400c4c01c10b10702d01485c4080940d280c402c02c1e6540b008500b0802074107030074400254014543c1c00312406aa4219080e4088080c040741c2d00d007101100001e4081c80d010420012850758140c041001408039404d003029a80191654510321960500940d6510314001c0f0075a070f0000c400003044603c1c0c883e90700038241801072000f65400100514290352002e10002110300c000001c68414542514002d45c4558035860000c00398081580003001c014200b1003a0310798401840340c031302c0e64407400c14110b62610441c00b0038001a4002482039122034181071000b001445142c0e820582c6c40f031000030300d580030b140b009010b500850b0740030340c0c407035141d42e00c09100f40005c0484810f210307014042a0000b54117207201507031b0092240d10203020081078031340740500d100c2d041d07162908910059944030040e20500c0303859140c000d41d500032040c0d20341c41c68401c0955142050384000c030048038298005080d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 227029667 1250 227028417 227028463
    0x1b040c140705011e0605010e04020721030204030b0705030f070e03030a030b040902031509162304090221070501050301050d0308040203160909110301050702060402090c072102010608 80
    0x1604141c00501e8159425500c503000718018a18003075460061180d12807000403168144030004003007000080c501c5006500c1040000d01003050317443d54410007a903c2d002d003914110500421406409194401800c4403081002d00c460650410003440c031580e08034894102a03a10703960216452608424000e0305500708000c00b4035410301c00d8000494a000251011500d41080c0c8d02281c600324031186526841e0903464284112814140241c1c00c001002454106045041483c101104036105950418003e40146030007041c0e00c0b95003142e1411a0020245429000190003500240c042049403c00501403580003107003540c080c5083ea03042c4d40b0081c02c94001d0515070355080d0f610140150060364984640c00703003042c9516458412a010f032541c00b2010130320406d1850642c0042c0c90f043c038001c0c8079034108020010030382c0c1e0000b80503921a4046400e11266180c5401d412002c0c42203000c05040081840540c1051800b021145030f1075041d181d001700085503817150344e15203410307100c84070340482068250313 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 227030917 1250 227029667 227029697
    0x106022811210f0102090a0611030901030b0409021002010504020406050a12060c1b0302070602071208180a0812130e0105010801030b070302090607061b030b03030412081201081b040c 80
    0xa00d000200709140700006200b590b01d041c50b2804141800c414030b10fa4000802103814102041500010881d81c108400c6507284002c10300e84034028820805d041680d81c0c6110421030341c4a070007144d881c580190030713088140c0c6c06110081c0601030440701a4041d034184080011142860b000800c119800c1c0c0701d40301d81c00182c0707550f2000503100f0040740f80d0400c1800c010348c01c0100201d0780e04041c0c0074800e40081090614041c000f03410048107500c51001440c0341c02040d00420042c0c421100e1140f00c081c0401c4d40e00c0640000140440a190010002c92158149003552000c00000401c035400384003030020a0f0a03aa4568040c1c545000d0082c18009426400100300007685103081c59040740103400d001d428004000c022900903000b0701020750356030303449040003401000101401d8104103440c0c07a047c0280c0c1400d4020940e80c0c46a4411403c0080102c06506d091189610a8613400c90b03640304d0034205960b551000c01d90f60380c540050000c91540c0007010303001e58038107403092041010a90719401c90f0191101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 227032167 1250 227030917 227030929
    0xe062a1204120f1a01030606080102030606040605070317010b0408060f06010c020603040609020d1212051501050c0c040f020c0f03130311010e040609242313050106022811 75
    0x3801c00c0707419032003e080d80030020300000d0500c440c0030180035a0b0f8807558594100315054443d01e0f8401e10061340f04106216860701c40d00c0c01c0b5810381e03a00342810390362003500f0702d4101d8550401100803154444240c0001c50003411090040048a090504441040e01d03410200c40e240c0314241e44103408038461500050050400d5005141e00600481e0001750340c400c03940106181d010300c2c4004648010801840070002900076600070300032a56414104041c1c40c180340302d0001c05400090b82410700201240f59080050200300030130407144007070070503c1218000800e4101a410aaa40d0b807424050500350341c01001c400000d48545080203900ca00c111071942d203034958110740e102c050310304000c03610001c50942c0d00c840c05244001d0a0032600080c1c030300e8060401d2200d0241c1c4040404001c0b0300e4400400c96a114507944860782c0a03046820b00803564103000050342c0038880641c039071003a0704100c000100546c02041c1d48625402c0c450011200c90300e04d180d00d0b9210344052a0040c01c1641d4a01c2d0046641880 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 227033417 1250 227032167 227032199
    0x8060307090218300307140a020108180c060c0d030605240f0405030118030206090c090a0f0b150301051822140102041403120f190e062a1204 62
    0x19000c1204e0142c200c1d2410362412081000d00314540c0e100043c6501001080e2080344414039540700500f400264540c0000d105d0880a0011202070420baa1501952242841b285140403070007404156a000c0b0340b584c0a88461041c2d0b081d4011038a410340000d45070070300c25140322550781080c1003074038500360340300305000d65030801e221840500328240030100d13060300c5c00d102d80d9006d185c1440046a03500903074a002840c1c1071000300207000581002c0b0030550143c4403d4a03541d0000d00121010445000c00d501d400028085c03429896030241e020300c40842c200114200440c180c903000e8504858212280d01010059907040e134852100040c00054148044100302d80010400d00c1520520304034070028000500307a0300070750841c030b003000840c9070000300500d010800d00358031498030000942440b5001c0000a1203003d04520b4000440c0c203000c1e00102948914181d0030032580c010030050b150742801851030781d64100030102c01010040c215042901c10000618140c140507401d44a51500c2c0c10449500284606 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 227034667 1250 227033417 227033449
    0x702070b1e12040c09110d05130807030c03020c01030b1804150609020909011508040201140906030408030a0513020a140a0e040b0702160509060d2108060307090218 72
    0x803009070301d03006020503004216182c072860003419039041508012030094516848014401d00d8130209840e641079080590351740f007400460009255445001e492201451044010182100090351030209500301170105030450090b42107035200030720103005500701e60b00c4a41080c1d0104840030b0090000190aa8541e841486954480c440003d0452070350180d4005400801d24a50046980d00c402d04003018200c0c010580140320312042c6400c141b0181151a01600c0a81001202c0f15a140b0700d80b0442c04580728050090582592460030341881d402c282c00c2a118509040e0811010940022201c1d0301e103504560000c12071810740349408842003d11200c010502e4000340d942e0400200d902ba641c07032541c4584d0191203582c01a24201000078104004c00b0f00030346e05e2210007102884142c4034510b800354000016100d910800d101400c020005600403620444d101c800a41c0030500c1c190f0003440786000340d81c11f608640c41d003074580d140c0e03c086c2d029114010245814418034a000b91418495151041c3c08c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 227035917 1250 227034667 227034697
    0x20717030f0a021e07090c020613020d03140a0f0f0816081f080f160f0e06010e060304030201091110050d0b010306080a0503031e04080306040b0105130303090302040c05030702070b 79
    0x890010030091400201c05103130f1608007041c10089a4001c1c0616203c0c04000d10141045240444924100382e85000c40603000b260b03d5482e1034200b40c01603040190605000085a80340d50a000000300501e0000c2c25440018449195811003140140a018003468840a01070900c0c0c42c0103000719903e2100420001c0c040001c400f00c1c2400720030081c10321010341420005000341b46400102e0500e00140c80744454282040380c40e0030424180c5c0c008100007502d00c8041c902200d901c8140040310824172580302141e0020001092000f0960158414022984200750681c141143c10040100144181281e040415000c103c101282811a4080c0701c03e000141000121a81c554103014030b4003991000890b0070780c0c40001400550108014103411440100070f42900c00c0c90140d454415501019101c80e02031502c3d40c11801003a0b0051007a1181000043e49581c8107d40c2e078100202042500d10050740514686440099220b100c0c0381200c2c8101da03903030000e01126107000000032032a0320094459601c85c0f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 227037167 1250 227035917 227035933
    0x602030a15232b050d0507080f0c010b09090307050106050919051e1e060415181113170304030507060804080d02270306040b07050c0102070b0a0c020717030f0a02 71
    0x244560600026056031a24203c00c4140078609907141c100550080d0003400014026800002d0328442161100020030322183d84612004156501400c40347c0c0ba03003507020416034104018520004003414055006400900841c1c1d078a0b024054003003000e49808080c88a10200740200410307640000d50880ca582880340d0b0031003070280c0c0c0c003032880b0020340d600b0788016144c111005040d1207444401d500704208883c10800304600100150000c2c280344141c902c1d000c05642c070901014425409900c141c80a032284a681c0d546207856040080302c5805540d081400798440c0d005682030000980d01540d0340440140012403d00000b542e0020004004664600c003c0010003072480c90ba00240c420707010b001d003240a42e0551420b29503028145404518041e600c600d08001c0460200303040300d0f4005080c0d0510590b50071a40d03c025003e4440c2c01c070301402202c00f01d820700200c400039030300a40107882103500760f801c91174580c031039443d4040e0200303440d1810f58414001065050500c400826210040307004980c418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 227038417 1250 227037167 227037199
    0x6040902010912050303063613020d05030910110a030e150403030e010807080712020a02030c150a060510050702040c120504050705090106020c0901032009040602030a1523 75
    0x250203000d0b040300c881d0000300a0100c1030030030881c0f0a480c2c0304100040003c0f40491149500e03564a02314102110240c4400860307040f002c1180310400913a005400d40104034040d05100765241e01c688031060080003125a042032040c80b0310f102c901c40f004404050140d1503a5a10216044141102c0240c0d0201e0444141c08803010284020700055100c0d4036958119004c00d00054440c510003043e10f02801106e00c10003030155030080c070100005010150044e200c1c18000012440c1d030045441030704072445802c002414003100c013503101d0b2150038409824440e40e1b0310340041c480c8050a202c1440c2c0032030301c240001c40051610b50000759615080e441e2181c3c040700d40035041e00a0f0b8030113440c15106500015000e02c141d081007007905005d408140001c0c4144c41004002c0f034102501448050010903418200741c18009240c03080200c5214001c21200301800d05042c8200203600076556014518540fa0401c42003d51000c0418221080e6880389144402d4180d012075100d0442c06803035a00812030a09038a070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 227039667 1250 227038417 227038439
    0x3080909070e0a030c151b0311160e0603060105010e03150a140103030e01030c03020a02070509091005070f030e0d0f050c0c04020f0c070e22050f01091202010c080708060409020109 79
    0x4d41c012110003d001d460800c001c01007510b0114083c040094a41c80303a02100e820b00101040603038107150140d5900e1882e0304450070004080d03d0726003202c03c26940003a42c0002c050f0b40a003e0340088060f19081d981e10b00043d1400350b084103210703405800110300e9480342036020404660146c2070f088003103044103038030034440ca4449013600211b02250a10000160550745441261580318090408510301401c0f03000c0696144402c2c4079640c8100030311400240880710038130507844800302e804002e00c441d00780120007504501040d801e260009241441002c41b01c100090800024869a203440202d0344401d40200c0d03840d403125100ac000343c818858100c03655201c2c0e20080c290768071402c103619251404000501c0c205040c5a02280ba4260071805221740e41417280d0041c0404083d00f200b081030b81d03c0915120741040702c1c43d00860125460a0401d90a000000d000c04203151902c0e402040b980c00070510640708083c09490200010348600000b803c01d080c42d50108841600504180c07c046981e0001405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 227040917 1250 227039667 227039669
    0x8012115050405060a09260705060a1e02031006050309010e061501030e07080c090601020a0c080c0108180c01231c0507140706051003051e0c030703080909070e0a 71
    0x801036074030002c000c00d110051150a8010303c603d0814008810181c5510110b00c040031a611000c01c12401c0c1108003912040482d001c1c03075072220076a5954641100e00400500c07400c50026641c010050501010802c28800c0703078490004d05040c20411800c0040803100e80d04010320308107980d0345e50000303001c4580c81080580e01c110f1100c60400c00c0340c0501d800040549801029424240c2e20115080c0840c613408124100501015209004503076600340c0104e00d0070703030242c0300034050403c2804003280b0700c0400300b00c000c0a01400c0e02c424407641c442da0285107850030012078000213500030100100296104600e80500501c00380503201c410503141d111601c60f60701a60900c0b1f02d20702c80c1c420014082001d0300585a02c1881c070308102042040c040c010640320301c989031000300481d42c0d0320002340001c0000d0801001a41d0490101c1e1001c24901a003a40150000000c1e1901441a440b14102c10303e00042e0141c180c9503c00c190300e040c40560020311860420181031401407043c0041c0c034500030344423070708084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 227042167 1250 227040917 227040953
    0x301020c06060102010c030903020606191503050103060507050c19080f0a03150807050306041b090c08040201080912120a060b0307050d0c090506040e04020f190e010f0303080121 78
    0x4103003070800b0400a421220304090b00c10038542081102c0780820b40215179298020b000356811040795240440f031710300e10481a002400c0082c452002e40c1c00d600d500d82d2286040c0d0b440f60400f0410b903151500c095529000b50380046c05141d02800307055440d00440301400c07006902c0f50150301d080a01100c55002d10f03801c12450180044e584040442c0034041280e4020020302800014164860602012a4441d00c0040019290b4150700c04903d46030301d540c0c2160340003820107401c10020384100e003100030a0002c1c10303202640050914070100f80f07200b9012418001007901c0090040c9003503109240e4460030003000b010361182d00e07600c07000000c101003804000d61155940b0b507501950351083e08243e50407500e0040c401410042511020b00041c0c03100011103094480c500c03c224110f6032203200040a00c502070605503004156100e03440c041c100b200c41e40da000d0b10000c988034189030327032a0160300301091500d20000c2e0000710f4900040203d0040703a07011843d850794400c0110300c030003e00d0301c5200f800701d1203400314 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 227043417 1250 227042167 227042173
    0x20307031a0402071211030d020a0f0806150315030c0d0f05060708060105041208070f061b03050910150b0a05180906240d05041506270b06090301020c 66
    0xd001801d008860941c50100480701141000d21a40352540241d052030b034a4014080301c103200306100c2000f08140c40d004c1004000965031141243c40050804142268460200f0f5140340401c19610341080d092100c00303e00c0c03520b6415542d40302d120244000681c081c840d018040c1031040e0240da04d9017000e4498085c02509942d0b40c50186140142c070b40f00d4002c20010030080c0340000c0c003803145c1c0d104040303804403400c11407640c00010040c00c00700b500e4441c4240050407000600440c608001041d040342c4800500301d40c00c5043e030640c0040c15400d807102210103c10710f4001d84030340038200ca40355021244000c984100440c1440d00d59510750f1040e0700140880010480c040f4cd5021549660358600d040100b050358229141d003032030300205410104420113014040400607101034451240410b40d0318103c140c0005000a003080c0c100340c0742d559001c849450309903081010221350921f1100a40002541000c480d01c0d0181c40007805500a02013240c0040e40104108050800c1c2c3c0d4090020b813240c444c400021b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 227044667 1250 227043417 227043431
    0x9040b040e0f0d09080a020f120319020d02030a0e1c05070e0604150302060901030504030315120b060411190e120313051005070303320702011107210e0402030703 71
    0x1c0ba0700c0e000380c5000c02410440340800902c4068004100b82c1c1c110740c0e0654501c405e1001070310001e031707010070305c0404090103110201e404524040b4480208504283e25001e81d4805800880120303228410a0104808110411410ba41a003020f06e610400c0d0b070314085800403110340341d42c1c45e2070521384c0950041c1c0c9104c6600081c090245031500c58800b941441c2d1413110066403543c0c2c003140290041101e07442c141340e40c13a8001000e15020b40c0106203242d060300e10035008a43c8900c80001c698489a8058032400c00c420f00060250405100d83c1204a864107500d504211840600181c80020000c0c110204900c030407005015481d00101d0405640302c0801640d101d0502c512407961005007a4001440703040d03864035010949420500301d428840d0545000700d450704400030744000808600500802460b0701400300740481c1c040c4a10140900c0d241e50081c4007900342d621440103240240e40024144099010040e200807003c0c0031040300d04d41f042e003420601c408014001500700e0700704032400c10219440d080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 227045917 1250 227044667 227044693
    0x16030b01030b01050d02150318010e03070c08060708010b0703120c030209040b0d020f011d060a020304030c1203120f150f080f011505040b0a080f011b030c0806040209040b040e 77
    0x214180500815958030b0700020a940000c0c00445407e00205d542c0c04002000c40d0640d021803020020011130030009100000c200d550032990380d4442c40c0c00740d44100700341c00040781d6910082592400303401a0307503074881ca50342440380040140d4800ca4044082c00600c1025100408040c01841c0c04078249450068440310b44406000c2070b0b0706201040c0348105078403240c200040e65a03040100484e40c01703280c80d645500c0041c581200f982039640507268070250100341e86101a500200400660b0720075256038811640d40c3c3d05c07043c2d11816000c00200440c102080909040ca03469200c42c0544130117410208860840300c1440503540c015400c00c003109140040e040c84040380800014128200d910f00800c031845108040c051001824003800d4415a115104240d90365508490300e0007920081c010307661460040d203031060003002410310868000503001e0300c00070750741d01a108102c030950b4070b42c444903410380d00c8104000003541300310942540a55603600c81c01d1140c480c1d11030b24101e20420320041100d016144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 227047167 1250 227045917 227045933
    0x30a02060c0a0c0e0114030d0f1404030f0803040c06170c130e070903030f02240a090206180114070f060c03150314100504020a0e0703021b010c08010501110d050c16030b0103 76
    0x2103a82e0080e44005614810030f98480c801c0250302d070450ae0001032202d40801c0841e000d10455001030f00d40705d41c0c00710100c144444900254000c82c0b15601541e0301e00c0c0e45034001e4500b82d80c0000f0030441e00302504000b07100068070f8401045140e040152000a1715110480c500d01c070f160960f20000040c40e014000c1c002c0580020040c100302130540000d05012196624650070403a8118640508120040125409544580001c44240e500800281c0c850b01551021081e42e20071000c0380e80000c0101100340b42810b501402c071810b1a40100f1003064100c840d844841c0030b00350001090040582e40c5d0310880651700e890b10500c000e18400d90310009040c00504005103041c000c5010000d8051800d01840300581e00c0c0150101101c100c00401c1d4a1991200030980081c0200d1071541070500b045510030b494080198080c0742600010b40310322245980399401110f14600b624280500b5a010001400c80ad41c0980041c010b80d040400455282a206021003583e41045510807100c1e162280010703c20040b0714 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 227048417 1250 227047167 227047199
    0x4050103081c0e0304030f14030a081b07020f0118030c06021509030c0304030209041a01090519271b031407080d02030306060a03020d09150b040b030a02060c0a0c0e01 73
    0xc1e035400e00182c0380c0c0606050b04c3c3d2003a84801010790341303d80d99050421a03000c514419241d5454180e9899107080c50b000341c80310200b03c42c0020313080e0615244c2c0c061101210190b0b88156006410303c0d0311040d041c001501e440c1d40707a200140020141d020000002030b0301c1d00760318024240c1540580003105030f0320081c000009010b80740000a0b0000d11140180340400000e0380c040325011100400d1a072118141040120084a8901c040d4540c40340046000702807a00300b640148190406400f907640240e081c00100c500c0750041030780c5e0040c3c480040b00b1001c160404000094015288a114404040307460701b04582d0ba94822100049c006a004070b00348818040e600052001c00301030600801c20842c02912480010440c2d8405d610125186c0e408501c244c0c1554036541f0f200400304410b0250781060804a010002c14100b0310341403000282042c1030502510966803400f800405602919a007002120b8002b41012001441001c0c400d4000c42e490031504001000706505000c100c0d414034400006e10054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 227049667 1250 227048417 227048467
    0x1020a0e0a03050604030f050f0315090105030a0309090b041e14070f050a0f35060604030507051201231005011e0e01052106120705010c06050a0603020405010308 71
    0x10703039001c002181c40820683d6000f680751a20007202c420f1040b003a241c90007a468090301c854808010440d1845180e4012004800211220f01c06682d80f142050350307420030040e000f0300142e903810080203100020740055456660084c0042140e034035106001d00000200102c400b0200e07268000e44000320480300e0150f421020614111a441c80900c0c40a85207100703403955203040210001d030500809200703510800d0386100100d40404160325841d9460f00d44007407a038001c100011040041142c1c1d242075011501241e900030081c201c090302c0c0c0403c104079401030790400d5105540b903001e80e4a000d124282d4090f0110191034100d03d80e4248550004420318494002a040c40720320389002025000a081c641ca04c0398281c605171060288105c0121190301903031040303a009105040706405000400c03407401d03119003016500b5440000220b40402d9559560f0701c1180d010914030b402000105109030001c9911064081d004140941e0ba81d0100741202c40c01d03441a91507042c00b20ba000c2002000e50034100001308 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 227050917 1250 227049667 227049679
    0x708040f0b030f04030e0d0c0803030403030b0405011d04020d0b04050f06070507110405040203070e1504150f180204050d060b010206060d030f0e040608011b09090e0a060203061206010801020a0e 85
    0x6000c80c0d003c02881409480641406205101c000c61617407001040d540b059404402401d80d00e0f079500b00c09030740390000c1e06d0131000b2031b003040d0a92040341000e00c901412140403000359818818090002401120090401e036046802c00d0110000700d2090300c040c40c02280304000603e5500203803200c090401001400c0034082060411044001c0b03881c4982d1691003000403180014541c84604c0080d16021199020320600ca442030100490309102a52094004074169402d00c0030702032034030f42e90b168500c090161310046440b00c1c40a00042c2d100c1a80c900c404c46454100618160712200020341079200752100716050351710b4480c0d0700a81c0d64180f001503000030080c2d41140614507103075170150089195035408020044141c00280003a5241d4212400070000d01008100d1100e0700601200380001e80e42d04c40700403480b20480016a05614800c0400d403005640c007030300a0403682d54940c0b010b03610150000c1d82c00b00e0302c3c1f5000320040030103114460090440c01e000681c0d07480040800b804088802c01c44a210711 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 227052167 1250 227050917 227050921
    0x12020909070b0405060309010e100b0a05060c06150604031401060603060e1324050103060507020715090b0703050705030313060614030c090a021204030f03200a140c01020708040f0b03 80
    0x1800c2c0b005490035900f00304c501546a503505085039005007002c040030b103e180704003015815440100c1e40a6030451000b500c00b40d5145031103505021941c401c090314105141d05c5000018111f030444080c018440c4d2000f850b85241c582da03030700e40c0340212262a4071802c4c165510681081455018400c3c072005040e00c8802115500d4810314030004030f91641d0f400751401d80038554814401040780c801200031601c2200030400355071a07003051801030408480741c0001d4403c80d0b6002c00e80400030058080c20f641c02c1d030380e080c03043c40c202210515a60410740782203060010502078107000480c24800307580f00302d40b6202504250410350421100307454999000c0120800c4454a91101da01c01007a141c0740d0100c146d8401a468a0700c03411040248903c540000040c640c200a0100b0142d2000160880f0350aaa0302031190b0310891080d083d010000c204090803c0108002c4002200d01a5800c01e0002005140c05410451446a1582613030300c004011038078080001024040c1c040ca4000c4d12015104500c00f6900358 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 227053417 1250 227052167 227052179
    0x7181e0c0e040b060f0403060501031208160e010203070804140108010f05060f1b0a080304060b0a0f060810031202030a17040f0b09010b04180b07020d080118020c06011202090907 78
    0x981c0e000c0d0041c020307a203030040d00509888450031503100ca150342814981c1e45075242868001001c2c2030101700d40c4d582101001c1d2901030b100300703601030250301000620021078522074401e5821005064619055010610260000caa4494090402040d010801c44c60210340e103400104103150581040c40f504041550600054460750281e070b180307071004000150358010204406110405001c4821b1251086007101820400c031807014600403441540c081c0003002d150820011480038901409801c3c150009003006028400c9000d6904608a4854880d8080d03c90321628800603c95000d407001d80c0c00029045592a4060702c42c40110402001201250605545001d22050780d50320142403090010049420302e003080d0b000b00c0d036410008104000d18003665a04d01b031481075010098480803e54000641014008035140c04068685e6507078180581c01e0444040300e809842c03201900315a800d20a003150f04070200161400b9062240b2120412402407040000c101e00003490840d043c1c200b00810412 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 227054667 1250 227053417 227053427
    0x1b010b03060f0a2c071e030809040b0103090b10060f02030309070509040203121206090a021603120216080c0d1701211a0a0f0c02100207030207181e0c 66
    0x2040c581800404c41c810000c031212000d201c65080c0c00054903184401d80c100c00790004529080b00c45140681c3d00450880034030b100341407210704c000784c1856400c00104801d45402d90001e03080d004141400951090701d81c4403607801c1d040884030a1801d040b664800d000940d000401c03148a00c0c00c900c001e51951802c3c5d03001c240c846a0512406020f84070300000308045613400c0c05405100554502c4050311542003650010801009070b82c0103000703100017400320348468180c0c021152142c2c10401900761500082d64120740c3c803070300c48590b16107403607003400901c000d512031401c0d0610090283d001035840740030406030365003031144550b202400d0140030310b02c000107011a20211030441d002c8055554000300e4000181080041c4a0001000341c40842140009840c061147e1030261107002ca0402903c1d40d220b00c4041107404004c60040564031070314607002c40c1135241d00101000c521074419544026603d048100441d0380c40c020070703007042e0b4440c2101a0482c10400038050701040031130050191003038014020700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 227055917 1250 227054667 227054671
    0x7090b0903070e06010c050f0726150402010302091509030607090e010b070204020f04081e010605010c08031801050103030c0506070206010303050702040903110d110c0609150a11031b010b03060f 85
    0x11071540c10780300291301680178412103151036820009171000301c5480c82d0302a07210500d901070003011540021810502820003440300454074100c0300104159032a0606459407403800600c224100758003046068040e440d600f8280c508800c910b10850388544c406010507041c1000107000e0f408021400904000d00d0020310300f65411222a05c8241307503581303840d0011070302a105003c1c91881c842000500021101c0b80041c1e500d401e440da034481422219010244035090f56136a01c6043d0004040307040da1000305001308025900268152141c14130001e540107050700f0342d03500340c4c030650100b8807040c801402d0003400c0c000315603c002d06101400781740d030550758090198060008040d00550f99210184101402410f01040d030300e84907030403201185030300720b0002c121101c11140c182503170240e81c000700b2450030b101080d6030031503800400d00511010181e8031041c031a046081d400c820080380440304c0d0340001c001c3c00103042960303120903903000020701e0407582820350300340c150140d010f0381c80002040740c1452003840d84d603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 227057167 1250 227055917 227055929
    0x6170f070902071703091504110f0a0305030a031a090705070201090b040e04031110110c120310063204030204060b1204060518060906150a0f06050310120b07090b090307 74
    0x2c0c5d16601c41782107840c0b410b415000c400003008907250500c41404410780c0741022807101200c0b04280031034a40180a00d4241503c00200b06620521565000c036029800510769a0201320101c482414090001580142c0540c1c0803004a40002100415540c0c42041c4c080541841083c1c9850546451840914818010009010070480c44a856000c5005111159403030120440501c04d510341840080004d602141085490703100790210040101d550400340d038481c0d05071100104104c0d142200548040c0210082e10064513080c1c40d54140200c1104080b0403070040d41800d02c0d89540c00d604c14072046840c2134000c000c00c02802e00c402c7c1e54010b105c141c0d9a5010350310040200d000e8503612808032012181031414400c42c00b554003041292080016254490302c02c00036080d01c10b03003c18090082e010407901505148003c0e0040c01d0103000c1c051030081d6000400340c05210444c40e40d94403c04144a9100300032241180d6000a1182655110340746202600206c4456483d20745003038000781c0d85151034420300d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 227058417 1250 227057167 227057213
    0x90501081003140601090b040b0114030604020424030b0d0221100204060503040b070c03081803090d06090201020c04022704020f07080406030507140a0302030a06170f07090207 77
    0x9080041c100d200c0400860b40240d062501d0a03520b100f80340c94400900820b1841860300b42c0d645503510b05070055005612040c0c4420300100383d5224a1111075000800907a00990204000580038148210021000320111008428031401440041c1981d018440861055261941e0000035980c1c1000c1448070071500c8810b42d6214214148490412449920340f0b003a040c4082070000d032140d0041d005504c283c1c400c1d910708805940310042590080c41044020b00007603140f0700000da10302040d00c00ca440e07029651003141e092404403000101001c51000c01202c42e11386070a05482103507010004400c840c00100c1d01036060148103604507405504000700040035400014a500107034546604079140c101a410516903903e280b400c001d16946c2c031034803c03040043c5c5010005003065201703040040484c81444c408915204500d0f80840c0a50800b03400040a070740c0e00c00c030000703400d81d0079503940d590a40010094003540e0205607219081052907400700340001c0c010418200041c0032200d02070755050349a402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 227059667 1250 227058417 227058421
    0xe040b0a030c2702191101020c060c1b120f0f070210083106020a030e1005270c092a071101020c031c110a080c07050a0609050108 57
    0x60380360304294409070079058903080126040d00b5002c8280f80d605031809200b400d86070040340e90000ca20a1150320942040380d002c1c03410f030491142400119011a203000903083c0070b6281d41440c1000e00036540250b05c070800184c401d0743c1c11041000382c1c404104c0100640f10006152180c2d070071600c1803100d0490351684c0001c1311040da2803850261365590350060400100c0c00c0c8412009020100705560103c119508102c40080d0048405041d1440800f1841c14032a2082107a403403402135001103440500745925140701c491017110410034120400d42505020509007012096031510070a0384049020b117400708410001a51000942c4642510342a511540300303070788880300d030703403003070084074900c1c2a200e08101c803000380200e004000c1e080c0c0718050104003061226100c010b80c2d4600380358025503090340000341e001c1d8070a40319845899590015060815541c81e40800e1107041c9903000c81c0855440c280454202d81c08802040001e003c0c04080e0380a00ca51f41c107148000e040000603200d0b044c1040f41c8000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 227060917 1250 227059667 227059669
    0xe21090406030b09011508030703050403080706020d050a0b1201090203030912070816090b060403030c0b0a02091215060a06050403080f04030c080d080c0301121e0c0806250e040b 78
    0x8824001103401003140d40f83ca052001101d4044c0000d82020030303034402c8000002c0b9281d9404000c41d00c00f04e625880303091510b441d503940d4200e246c2200f402034501079030900c042c20f80ca075018050b01d48540803480000034103200d0803040100e4080d0910b4100e800c0c0e89064641e1005840010490300c1c1480c04441c8400c1c010b403a00d000701e20b054401d0304114518010940c1c95001e900c1c02c48144001d8a845d102d0900040c0307041d0091102a00070343c4400f038005100d05241d00b011800c0700715035a800913003401c00546442011070200b0480340400d60b980100b03900c08414202042048000d003034102c04200c1c0c000c1142c3d8a090802480d502907404041c0c401d082c00118540f01b4408401214020360b40001601c1c10203903140d00407522441450240404607031039100140300041c40d001103a041c3e400307011007449200707595200c0c41c0032002e40c121104001000e50b02c0f0744002c00c2c48000c00350000d00c1004010011803074401550781a80c0030000c0380c40d03401c2c0e120190310310031a500080d040000e0305c01650f0009074800010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 227062167 1250 227060917 227060921
    0x7121a180a020c0a2102011e020715061403070b07020102030703050a0e030a0b040b0f040507150306090501080a1a040c050d11040c030c020d0c0b01030b07051209010204090e210904 79
    0x983c00a55034803d100c00d240800c00000d40200c0000311150a14125420300b40c02a426240e00c44621100e80140400301114002554080e00700079008003d0b03060308034200080101101d01d190002903401202280095951804119a0b805080d00d000c400b4248505540084c0d56070189900c02024440c000c81c001000038400c81c86000452402803c50b14405001d00700544410400c0c4c0c1c05aa1880750fa4000502896000090300d0250380d0000c01408214075021203100040c1141c0020300c2056160b01c00010718100d80d000b410b019040c094040d104100191402c481245000c20215094291450402021650b081207020444000360380f2030b02c2580381031401c1c00391441030720840c0e64060310304440101c2890341644501e16000311a000c84498170034045090710303144410381004003090303c1200140009079100072a6038010303046090190902c49081003419240004503031001e81030790701150801218003d40a0b0b4481e1400100240c2885120351940580b0070b10400d00c1815940c0c00040c0ea401d00351915 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 227063417 1250 227062167 227062177
    0x110d090b040e3112030e070504110f19111f020a090806040507030b090f06190209031e10050c0315010e040905070e07030c09060e031507121a180a02 65
    0x7560b52000c4808415000115030031018013074580e40d03c0f0886102c18070f030081c8682ca40c268a413400411840746018100000390540c1d0160710b0710040d0a11442c1145c90509020306030500100c0412450b9000070711300100716004000f041d0405038000c105481c1000d403858030646044142c83c0000da9104d0140405407910000c5501c0398582e44038103010402803006c082075060030340e8880c0c81615403640318149901c6e0740d1016941c4400441c0c1105d404075148200100340e15020440d038800150503c184000040e0402080f000a80840301032075201010151003031001b0181c0c1d2450352001c02940c28180c200506600004141e1014070340352011400ca903a000d07800090000c000108107000c0c04c46585002d985520b400d200f416044800e120200e502030740680564080c0032441d58078082601d00c1c0c880200e074201502099260140203c404010601c52181d90f01c0e440b0340c03140d49448130049146203681c0100c400e58030842c070482c6518034180c00c4503620f40c800311200130f480b10100303100c80d11030380c90000081c450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 227064667 1250 227063417 227063461
    0x70609020316031103070603060501270e0907031505040c0303030e010f1107020f0306090d0c03050c100209010206091507120b090f010e1501080708190c110d090b040e 73
    0x240400000800c4903e07800e08000007019029a110740351f03500c0d020f1b0141c03184c60050901142d480803940010b40050005c000c503444412451084542d070b42d00c0c04680c2e0000c16501400c41d42c2150740107005000d900306102c507050042440030045840c0c1911415406809400010201919800b8140c2064025044055034006c0c1500404c01e20700c0b00f602c41d40c100c0e809001d0803405103030300504001140c076010802512954062024010340389441c4c104a40110a04a04600b0b2182c28004901034000070400001c051079168001680c5100100c00603280210090140c10a548082c4a14100003136110396150028843e051540c0708028035041c401c090141a150315810085002c10406562624285103048a100f442054907035203031001a090100340410a05011400070804640107a20422209610005050b050f0442c9509250780d4001d0300c5030502040002030f00d0f90548507c180c0c01340104040b0030000c0c1001c0217450714201300b0450902071446201036041c102d00008500302c011032001071003420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 227065917 1250 227064667 227064703
    0xf01120e010501090e010f0b090c03060d0b0a020d2406391205070803040b1e0f0609090706020c040c0302120a15090c080a050601021e06040210050306060706090203 72
    0x80c48020740d100030703c405d01080c002913082c4008540124111f104281c07000d60f0140100b4034560320f40c04041e120703500c054031031074001d40341e40c0c44600030a40080074580511812000982d603081c1a004080503580c03203146481c2c080c00b60208032001500b04804032000c4481c3e5050454807030010800d40c6003a01441680e82100351001e004d074441020402e082418031034070a544d05500008a10b104440c18003a40d00020101d440400200d400300f01c0c407484842e030140d84500b004510000f43e03500528110030a44803201500c84000500c4070300c2ca070102d001d9621040303100051107124602080290b4030100728504501981c1d40b02d0700e00c0540d40c480c0c0c0461b003030310b034898112286a0034140100001403100c40e08841c11203198442c04500742880d0300505000d16015964003081e07469031070350b10005210162120341544a56107a16a2400d07000164030082c0d0042c82c00381020380382900602c224166208283c2040040403c10000d156440d08117440c910794000310001441c0303a40384003207458481c100340d00c121211 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 227067167 1250 227065917 227065919
    0xa05060702010806420703021009082107031407021009020303090604170106080c010f08191b1b0c1a0f030f0a0c0306050f0d020d080c010c0207080c0f01120e010501 72
    0x40c817104981c2006580050140859044160000054040c00c800240160807456007200c1440207030308100350550090303040d240361550100301c222280c0803404511004d10307609401c01c1340b03040c1c1512800c1e403500041508030304180390100000313468040551404c82c4142d034400b0b00f81c0a64404000361002c0001c090000fa0b46d5940360310110725412441415480c03d90700301130000c1100100031034460300b18101a1510800c1d0284201305941c4060014540c154410003840310000f01c01c090b0280702080c98a00d03201556481860344024148030074805c8e00f500d44512810740c1400103410f0000c2104480724280c18a81180c0c400c1d403115600d110b00e414208079560302009100c02c40c20b62294547c09000c0b2188100050000186c0c258265000e41c030030280d100c44190050b22a606025054081c1030744010641d203403900d0240d994070820703000304048003034030f82d980c125005059404000c1d1901602801c0c0060104000c5400011041940c04289034100030243c1009039400030190461190000490b000344015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 227068417 1250 227067167 227067229
    0x109200f130807050a0312231905030c030703051b12010e070c0c05060d0902031002090906031c050a03020d0e060f01060906142b0207020a050a05060702010806 70
    0x103504006182581e0280081c00010b802c6000244a000c5800160465480f54030b191070f00711541051101400a001c095040d21142082549426880c41c000002d056280d0781e214022080d103698002c80300c01070090030024401054400c03c03e072a0b000032545408502c650305c40b05900020f25480340556108103011030307001444282982080c1c107840105c240300d10b00d90f4890f90222a00c49984001410081041e041448036060000062104040f1501c001c151402a5808240741c01110103c2c07107a030f583e0102c0c0d03076401884d100f5020f46d0088030485c0101044d51100d504800d0fa1440809880c052100c0040e048020768080d4055036124215060100b110280da50140f0b40c8604c4201c5241c030186422100209a0714003504080013514400e5480310317400583c07040859055440014a00c11a681c901c100c0101020030604450030074158540250b103845480c41486108000c0b50000d81c4141040704003881140c94120aa850103a02442c0294241e111a80480c00c180038458108004d0001c241c1403d01d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 227069667 1250 227068417 227068447
    0x15020c0d0c0515090108071d031f0605030109051b0a0b03010305010507020d081e09070806010803040303031a1003090f0b0a23060d080c03040e011706090114010920 72
    0x31a4030a8640c441142c03c0b100d05411944229000540400c00e8075020030809071250892a03100000707107000b40d03800200c000010745414143c02c2c00841e000d51161943c203042d01c00b409444003c1006a0090041444a90b2940d890740002c242031070319203004110040c019035404002c1070061544413840303981c95840f4103000d8082d00c5c0856801001d8400d00068a01c21485103445d2481605101414502504401034001040102a110018504c81d41038049001c00c1c090120b18000d2654400856840380b4515010301615080040100000c107035145c1c02125448107911070006c140c003490f000401c40014030f03001d007040c0c020007000380a664460040003900910b6500c42c9400d4402010102d002d028001c26000c600c00381102c1e03241d00910300308400000207010380040e210384940002640e0509446c0c500c1ca0714013401c04d030300c0302e0340e1030701001000e0301264000d0000540007a1488000d00c00740140360001c00e9814411b11038001207941c1e880c0d9015800d246128212416010340a000740e0341d100c89008900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 227070917 1250 227069667 227069669
    0x1e070e10030e01200d0c0311130f080d120b270109110c0d0e06070b04030903063c110d060f05030d080403030c030902030d08011a07020a15020c0d0c 65
    0x1682d50300e81000351404901100c502c00481481d4802a0326011848403000301070300c440e4109406054840d080e505c1002003810103090035a1080034141d0041e441c0540400f40c0f00c03400d0340004001d400c40300609d00500d0f070240001031046202000841c1d91103428000c0b407021225089a199001c020086008a502c40c3c554014125601000b0502442503185907244481c420120300600c80d41c080c0c581076440c02e0091050b15101ea20040071107040104a4440c09540481100c0440000c1c83c14501032080000901c56448603081e821103a01c00f4040004102c00320245a140c003070704000c500c5a14405c10506500000c5600404404550301c1e201c4101d41000541100d0090034442103408201044c1402c0015a05108103070995650443e91039a407410b80050404008010030551a4980080507840c10010300f64148107a6071084120340c90408040c41c40a03551500200d082002c1181c00b0140c0d07281d420400540c1c902188083c1e040e00400000e80c41c1c8070910041ca5041450044000b040c8010034601c90 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 227072167 1250 227070917 227070941
    0x20f04050a05010603051803031b121003032c2812050705040b0d060209040603080c0d03050f070906200706050c0c0307050a0e0910021b0f03031e070e1003 68
    0x8400342c0c82d0b0721448001f030085405541700c079520078070014104561340190780d00791400b0010300314580440d9840403502140110344161205101e000104200340e88000f40041c0103070045910307114841c2101d9051400c03214501100e00c10300382c2c11519000308d003041c010800f420307441503800c0d0686a96850320500000342c4002c19034541c011000002128282402103905601005100805581240d80c0d000020340000b0702da1600329580343d1020001500010003404001e001900030060780e00c58110050540710010004142d1034483d600317000050780c0054049041c2e0381281001450b01c4400d105c54001070201d00d460340c0c0d81c0e21910380c0016001d5003180041851410403420386410904180500d907461a6600c280303038000100f0707a800c0002040c01c3c402d0f107801c07044000c03d075402418141c0941c402e80e00140400014007a0031a0281e4205804020505401c41032401850461501e2040014402c0300c0032080d0b0302080c2450700148031148295112160580001d01289288280c000018000c0c01c6440c1d20f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 227073417 1250 227072167 227072171
    0xa1403060604020a02120d0608062715062814030715120902120a030305090c03072103110312040c05030c130f0b0604140931020f04050a05010603 64
    0x101d41281000c0c02141c02c481c0094005080382651014460902d034080400700811994a0002184810f4203000f003601501d41650001443d08801e040015480a418804c110360b5104460074007d03404c0088443e94042011a1900c0400741c0f800054941400405030034100c8005c114008514020121614032030f602d8141c0131103a00d9611000f0000f0205404448000458800c054542036902e698203c1403910303202902080f9001c10405803a0303d00340350307030200300d0103c2e441d80100000c8036420000304a501004500401741140b82050881200d25009052070408094031070b803000341401405035140c900e483c00708a0313035a03080b01c1c501d5183d40c440c25501150107100960700010b05180000c2d80c06203010340100005002440c903c000c20050a105d00c040d0302c0c482d111010400300750740d41c401400051040540d5502c298000804116071805c00500c000c540c08241c500c0711071008155800c4131400c145400e0f00f00383c0311140f0700001d0420f5411409040e409420720b82084804134045d00180e048500d030b605c003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 227074667 1250 227073417 227073421
    0x90108030c010c17010524190e1507020609151803100509060a2703051207260a0b06160210091805100906150905040501030c03020607020f0a140306 65
    0x400c58200d55089892148006900c00502180c03604480541c0c01c078440030780010a074402e0045040f02c7c4e401000c4000717403000c03030480c04080540e001015140192400c90760b1400c44002ea5000070603e02481c500a400f500011503240205e444900900b0a66008125001e0311503810703413580603201d0221044207000703000f85584000ca078815801001e00821140000c1d004541d02c0c800254001e1031440c001e01403c05406448071016006041e5683c80e850195842d1030380c0c0c1803640702c03070403050001500200821058448820b020655141d4800d0022803642003c1880d89840304600d000c0d11040c040c00d68024800210540081c1010350351020f16407095800c0b0054141218041d0b07409040d52098031200c040030040c03c2001b082c180c1c0007950084040031f1030220749444803640c1c41201d8013a0410340e90425500d2500390b800b500000308800412301182e062253b0340c1156105c50703814010380b1000b4065140480c02c1e404554804003981d800e00320260105a920382d60310a020100042c41880501034060303180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 227075917 1250 227074667 227074691
    0x30f010f0503070e06010309020d02040c050a03050f06010519030603080307052116050901020f0a1a0a020c0a08030601020a0f050d0f030902030a02010e011b0b010f1509140609090108030c01 83
    0x90f1200c2280c01d0644119907940d150801500944504a01260701040040c200c80c01662a403080d484480495903403980c40e03440e5007501a080300d501401c4954404607040401040d40c2e03004c0c044441c00e10448502c29600305096100b500034004942004200c4c05d408400c01103a160f02402030b200e5098911800c081c2c80741c0841420520040640700e03020302241c1c1e0b030f10706039606010380003c0c0502e0f01c040c41158a00e0812141c0541410705c80da030300715a00030024100303a040d41860000207800801e2008210300c0c00e09000717000e9548084240b401000e002003c000200640c2c024042d0468480c1c012400d4500071005141860312904044031107004030307040c0855500281d1103889514032095026008148900c00e5800541c5c039800c81c0d202d01810030142080d2038449440307040707480540d036101d801d82003441d5042500454145049401c00c50601050310a00180194008903030001c5846c0c2d0020484c042990601141ca940b10b0242d566030415800000040c820000000800a01c200f0000030040855405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 227077167 1250 227075917 227075923
    0x3a05040f082409250801020409050402040b010f0e010309080c0d02010c0908010902090c071106070302011505060c0a0b0a0b0a060c05010b04020708041701090b040515060102062205070506030f010f0503 88
    0x91000f260300d60140b0100b90800108000201002d00d28030110f07003180b984e400c0c83d90b00717a80c05500b041501d281c4030000d000440c20580200384214500f400c000c9800941c0c14070003814042c0916905040544452041050090000480b031787c000040c010344411a0703c002c80603010b403201112040004106400c00122030006214240c0900ea00070403501958441c000188043d800c14942604d22041c0c0100490441c0e0364100144903a900c65000072035541c46134540d07903800b01c0e010340c0201d0003135104102082040c0404103000d4222940140004e07000e031181c50b045402402e000300410b400c10310403d408214240c100541e083c02038400e400a201d0400b1440610081c1c0c0940a00181400750070b21050003441e004c00d900450781c0849000003e07801b041601d4060002e00159406e90700360b00040e42c28251208101080c035846882030000b03180b94148a140301007207168511a00da0303410785400307444080001c144804801018000c1032310341caa0030710030394041c081c24080c4225181c08420807000182d41c1408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 227078417 1250 227077167 227077171
    0x40b040515010b07020111070906170c0a120818030d050c06060402090a03150902040f09021c031b02130e071e060903022e03020405033a05040f0824 65
    0x400e0450074410185d0040d01c0041d00b031300d001c5c0524050060040340e100704a10130301c3c001f0038101d4200800640e01003502820003c1c0341d02002d006940f07001082c400f031040303c101c0c0ba0b0304507485888590746408400503d2040d00e000c101e40340e458060300e4030810809a1000c043c0c04140040010340e11075803903007c100320480c410145001e8000c001410700301701050700c40f24096006888480d0200c0d045c21150700140c01c46010741d10000c425a038030140e400550425204482200039141001c400c80c058580303015203034406010010b81c040506c0c00c41d0b0421520340c5e0700c4800241c000380c0c50a100004001444544824040c01242520b90381002d4440150040307080140807240c1d1501c40d049200d08603000c1c41703219980a002d0644174281015990034102d4481480828842640d80040e12a400c100405041c200004080b644458002129a40c40340440b11035171001c140e1303c64201900c0401d4001034450307005640c020000041d000304001026070b00443c5070940000c811002480d5440301c48484441e0300d02c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 227079667 1250 227078417 227078429
    0x12050f06162a03030504150207050304090501080105042001020c12060a0c020d0c1b05030a0b04150225020409020916080c12070f0e121f021903020306010306030605040b04051501 78
    0x30700308102010134003da00c255001400f4035120340c800b2444140031410f0760302c201c8044030143d1002804200540c7c041c46402d014008290080c030142c107250303d8051848008209140b45100d1106010070380d81c1c001c0240d8440c1380405800c21124003a006150358440e03100701c58400b002414030b60842e01b034603c00300d10716a490306c076511001d1090120740c843c031000340580d038411003403900c0080c1d002c0b46a41d000c00095900d0b500c5050040c84502d45031a140e000b888030700500c0741000e0f005000345000741d00603c01d15a078000e041070060070310702440c2c00010301520071020003940011200303007400703e0302a02d904c2081d1040d103107848000050321144100d07440c5118442012a081c80244085587d140c401c0040d1041c81199180c00030401600c0800282d8020100ca5485c0080d48110300e0380c003446480d019041a440b000120844c240b00c02c1400032000d6010034180303041019800400550707568065408070000d507030046401c10803031070036207041080c2036000c0e60152034074410404560851059050064140c4072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 227080917 1250 227079667 227079737
    0x1306030506060604061706030a3002120403110609150705070b03070914120304090c03050a090201020a020d1b1202010e1207050d06112a03030103050712050f0616 71
    0xa203024030380042d04019207c180d05006038541c540100f1600091041007144076600d2094131902e1403011500440c1c0d00b142c0d0030940d00320725118950400041c0036502180e40085881c2d042c0c08410303000405610490052951015600d00112400003100700681a02442a011204125200c81681032240421070b1400300080c04110140107454034282c4d11910300c040a440b024104000760503180c03e54226400a4004564079801007115507498041c40c3d41183e0144e0003049110b455400003502c03007080c2c54020340109260745150040202d08032a02d030b05140a440080c42d500c3d101d2103a07115407504c0d090305900240035400708200d00d1424080c800c40c0403044900809800749400300f40414504061004e0700c0c1d07984d854200f01d800f03030200c10040050300d1000c480c0c0700720224407001011007200400c000407100c0d40140b0062000490028031003050380e403140c00c10148041a031506030315000281c034150206000b014248074000400703114024400015840706510700c18231480c12907000c3c009090800c0004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 227082167 1250 227080917 227080937
    0xe030607050f04032d060f06210627120f0509030601090b010e0405270304030b01141f0306050f06070503030c07080408121908010806061905130603050606060406 71
    0x51107042c1c408038008078500c4c210f0143c0c994130342d00c00c0c1403900c031700040d243c898035201044200949031040030064a40387c0810425910328a05e144d441e1003092800810ba030703580722010400c405002c11888410b941081c0c03a88500c0c3d480d450424502d100b0701480101141d042001d001c05c80e800703501629040b01010b0010440751f843c016045000d0120b1455440c140903080d6803008460b1254040c1500c102d8400c40c0100440c5030114200010610f2002c100009810070702041c03000500b0840c5650441e0340c00e0b00410034107075070080021040a450389503028540b0207034660401c9035406400c080100da40c1180c100705000c041d039003840420320811900500301d4000704006030519182c04058124507024410783d90a103610740004078902042d80a0203622100702080c100b400b001040302c407100d83d04591410200651419801643d141e01c060001031241509150f00e9070401c400300100740082c50300030146281d40124201a8004021600058074a80030355070008085d8140001114229a4950344940ca84 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 227083417 1250 227082167 227082173
    0x150108031603180314070e07051801050d06090b1e0a05041d07081b01090530060709050109050a0e0403121404110102150903030a11040b030103030e030607050f0403 72
    0x1024007001c1103042c00070070041010f68000c84000c00d8042c5125084141d1040041d2000303510706a03a5603c10484026503000b009402030b4070400340c0324403000103503009181003122070041c0c03220f002e1545c040c1000c1d4502200000c410120360001c9031020781c21b8901c02126000c0c0044140e00d00100d00749150441c0089804101e2802d0070761003501510800308140f107403555582d1405052160b41c1d4000040c96211941340181010b031001500c060000900b491101c2c04c0c034040105260300e40030350f0301800d0004424050001d10503a649140d03c1c10001e4410b8850502e0718590280801400d07016050018030b1081004c43d06050564450080c2c1e0740624501303826680c2c59404a0b500207d800f9400d0001e0344800c884064504400071480c0507074803a003406450b420f844400280741140001c0d0045009904605209140704048122a007120007130f41d0100c0c540381c00c083c2e200064030440d4008005007100000000034580d1040c0087d4000000320103031b03034160312044011a924024110f0f02c03048160100410400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 227084667 1250 227083417 227083447
    0x3020a1403030d020c0a0b100e07050904090606150207060305010f15120203010308040302040f02030f010905070c290123010c060906020d0e070609230d0206030408070515010803 78
    0x40c44000408407840d00c1c00140468041e60810080403450b503000054182c00c0058480c070741580600d0840010080310300c0c02c1e001c86181d80c0054403800038030100144032802500c0da9049906681d4105e078060088907915203401c51140c44041001e00180665800030641c580b1074010107040342c83c8444011443c5090120701e402d1404112141c505016048007480b250f4552400514004c42c040c10041c0e443d14038500602c0195820601c100c2c240ca48104100f100d0100c031541441c2c1500d011402c00101951010b400340e420b001040006040ca800ca01210214042281080c907040304000758041d200340d907540d1014004801421070b100e80003202c01d540000d035510403411031900a0081c0c00c085810700f403075200d4008a0380314400c816145a11035602107141c000803c141c10007441d2038034002d42501d02e4842c50307550007010110341d0307080c50443e0050215180e40d641c0003070644540041c00d465072410140b0b4007052030744c07008901b00d07464012040070a00350207071108a1412606484061860485c0311144451 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 227085917 1250 227084667 227084699
    0xc060b010c0b01170c0d151e02040b04140d1e03090906060c11060306030712060f05010b0307080a1401030f050111040b090418030e061602031009060c020703020a 71
    0x41040245120400452282e9003098000e02c9200300f40074024005130116820080c0c8040464001c1c40c20010000c005460f2199100c1d540183d4040011a442c3c0c000700c0f099114441e150110b20b481c000301d004204481040c1c0180308031803922020340c4188150314144140254801c0018200c41404d05903606542c940b505942c403810f10a1602121564a82500d00b0860341103030812000241e09007040420081c00d20004011100e08495160551400f0710009569034928020b001c88955404032031010403206401a400080040100340120745e1640081c0401d6041114445c00150410300403a64103a00340c8500070741e640d200c1c29842203a81c21510b5842500c034964100319070a41d42e03021402e03400e0021a000e080501a06080b5903a5141884204030544901d90414030207110744251712000030350400d84400c4040001c3d26103d483d030b050a17400781e010b4111018041d401d070044c00318014002840d58030441c40c813881399104022a900704c4600326920071280c04002d42040f10204180322084070412044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 227087167 1250 227085917 227085919
    0x3032b05041109130507060306080d03110313050106090e150115020303061203090a030b06010f0305130f050a06021c050f0610081b1c0b12030708070303020f0705071a0a0c060b 77
    0x403501c0800c1781d803094900300c0540d200c01300280e9500c40a00903001c0505c042c404001461506001480c14106108803901c0050821011084002054400c1040a401200003044205c0703040110200945000d81ca8a25151300304c00010100c02c00030072910140005e04001c0350a590085041d680c032041404410100b0030300304c2da40751100307000381c0d50325580310400700029500c2801444098100b05c03002502a4080040c40d00525040004000072601c0c0042c44144007500301070044540425420300600301500910003421943c00021002c1c03204102151340600c4890200c0b04000c141d0f01c0b8007400f05000c5059400c5980070140c10b5150b04601c0c4601c900e5a0482908600c0504104408150413440d0f80704d034a1030703a46a0380307540c0c0c882e1800e0703021310400031048002d84040b4541200c0860480c0c892041010041443c20f0110b80401414426410b0ba2034120790050469507a203c0c60402c181d44000d41c0c03041440d801241a170130000d16200c2ca0584d00e402846894040600d0060f5071501c02a1100c02426 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 227088417 1250 227087167 227087191
    0x3030c090604170a14030703020a0f061104080607090f180e0106150806030d0e150f0415170a0b220b0904080a0f0903080a0f0201090203032b05041109 66
    0xc5903040030105210107900700b00b00180407520360b91800b80745012417558039145540003401903202080c0c0100c1c0100780181d0100407081003407001d140c40030042003601c1104082c58000708012800c410001036042c050f200720345402c10243e6680721031661030085030141d007100110a9070f00d000311400b80d4000c021107907842000419420b443c0c0d0300d03006002004221b80c0d00015021418021141000d103c00d0001c1d4540e850800c018242c09000b0404010070550000340c0c428002070041040c180d8801541d014021074900403200d03000349680142040340003105e0b081c16003010400b0840074900d0b8400c0441000003c0c000e40e840044000c007081201340c0d06002c1d5142c003a1034095008107651443d401501c00c80c443c070542510790708030080007011030301c00d282c2e490103200007503106101081407202510042126440c0c02d11140000c908124003500352000c0082d00341c840802c0c00003140c0e035082800c107005454030b1580e52035102c41180f544191034085d2400307082c001509044c41c030a8286900d006034894055210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 227089667 1250 227088417 227088419
    0x1008160b042102152d07080c070e070903060507020105060102100b0103020c03070f12080105010507080702011106090102030a2405040b0d0c0806042a140307080f030306030f0d0203030c090604 84
    0x1040c1910b84d40a000ba4101000094102c51055848103154210480001030600810904222141c03482007581c050082d0101182c41105c070041008510007400c7d041ca940000383c01e0180000e01500c10900007203a0241c1840d0009240900c14072030f041c8240f40590003000b1602d4440603080c0101540074000b0b04054080100400c00c00c0c0400c01094098407420000d10003448a0901c0b200e81c0c580c070410102007200d4000100f00c036030b03849016034050341e40040305240d8909241c40145e609800c01c610810060242c40d042200c140e00c194091841442400000e101d01d16140408076817450b03841207101004000394030288600e040c142c2c40b042140c0706c045c000c40c00b85016511011281c0c00f09034007007480380e8407000800c41040256003060724918540983c0c890b02c401a540c986580b8200f07030244882e030742c80c170301c403d940190b408002c490000c1103e030054407002d50095103056100d600481d003507800b0b44100030030140c16000c001003150890003941d0185085850b1169080203079030010103100d500c0802480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 227090917 1250 227089667 227089669
    0x30d050a02100e06220305030c0f04080a060b011d09010b03090705210705040603020d0209190e0304090605010813080c0a080a03020a20100518061008160b042102 71
    0x20822110030001c40c003d00c40e0703207001c141d030943c1703d191000c0c16820340c2d450003003072000250004207903600f0500c084001d0340c031180c0b1201e66030303994011548200d0036031040c03460281c2030100030b5210f01098038003a40c40b01c04d000510710950702050303000803401e90070140c004010003086a2680103560810102d0301038580035962000042c0102e030841c1451023031803003400443e0144020400c0b040d0001c0c9029101800720600c1c42e00010030b02201780901034003900c554800590014103a500042c03a10100000400c200100b140020741d03260014001c5010041c0b50030f4010600350f00480a8510481e04014140240540381d42e81c40001c0c3c00c2084810301070f2092400c0e030400030b0f8640c005410410441e6400503114909400020305449807208445401580d580c54103521910109100d100403445050104003516610485101c01b40c000c0c0090280f4040d120a01c101d00324180280c00403981800c0854815104011203806010b8480c403841040c03a070200020040941101a6501c80d40030302581072540380400e070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 227092167 1250 227090917 227090921
    0x903010603081c150302100e090a0603150504080f0c010908040b0a02060a0603080a14070b0a05060a1703090d0317070e0a12020604090513060614011103030402030d050a0210 76
    0x78100702c60380800443d28006a0040d00d410b03028000c0c05075410701c282c08078074081400c0c80c0090f00010340142c511201a1990b00e000f0700403800c0700d00d400b50080019140c1010250004d2013640400c41d03101d0882480303071076000101e001d194000d5400c926030600d02401e1001c0c0e0201313540040c0350840c0715501e404100c0040344860300908005c0900025155030b60220000082c24880000c1c4022132f4680703049418030210303c412040d144081b0003400c080c05403040311809402140918000206140011410040e1607003580c1c0046000e10025200302c2107880e110300d10580800030300c040c80b200c20743c0b0034800c1c181986000449507803140d0003070403c4103032181d1002a960b0328400844030a8017041c5164042c600a04104060742d008140810300381c0c802c401c5982c00a100c51040d8030410807055110804555107565403200301c9401c0e50702c070508000c03180d500c2c22035445c481d00d000c16090110302e03044403022500c1804003c5a2040c1c1c2c0c0140031f4078000e503c0b04400c0c0c0325074102d03408107001c41c070030366460b0100c500b01c0b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 227093417 1250 227092167 227092169
    0x30303270609060a05070215040209100509040c080721080904060b0c01060e0c072f100810050a050f1e04090c05030c030d090603051e010603090b10060c020909010209030106 76
    0xa00c080e0a141c50645131100c00ea072005407100c804c5502c082401c140807100180240c0c2c0095048a42ca9084d481d90454040d220303000760001944000154103100801c44020503c0e82152560400e0701c142564481c01e00c0c1044041c03402d0400112940b00c0003100103008400205140d0070000c10005285071224443c81282c4c1003000900400d03903582d4414408100480c2d5065482007a940440f41307800001c3c1c1c0c0d003819020300c5c401c00b0b400705944080705100b80050b100100c66109409843c2e580300741e0106600034010041030300c5501042c09403500c0451541405007407071041e200090254001040c0d00818004002c2c03d9503032000c8910302c15407900c0b04969172030041c0d02a2a028138031002500d41068101030400c0c0e00301c1031031407183e81b00160441620303411a00c101d00f10346160a0005c3c40b03a41d0101c003010340308100170406003820340860010aa054141c4d00c0f0305249809030000c00c15660301d4080003010380c9114040d103000f042a10704490010b250003584142c0c404502c600150400c282140401e0035203e513 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 227094667 1250 227093417 227093431
    0xa0f060203100e0603030f070203190305120601051e0702012304030314071e0302070b0a05030a0c2a1103010501090c080a0216110d0c080d0207140303032706 69
    0x2484882242c10200c000030b0601c000440006042038030020741d42c0d00ca4a00d007000303c0b030400700d8941c00303541e0103026401840c2c02240c952403260300d1520700201203a005250a62806c8a101e0100d201075204005941d21a03030090101c400441c02eaa2416160382c1109004904000300c00641c20744201640004c4800c24003000003042e120360941ca0050300c00c03d030407500d103184010306000e20008201003201c403804070307440f00c50902c030001d80d2410224202551070b040207200305030000d40c080915034404000e40c45150250800c0001111301e00c0c00302c1340b01071003003403c03805401e443c251014041100c0c1e0350948454401c405030000c0f503482c02c0209095843c26406010429030350001049020f4001300380310747c006500c000441c50060014528000100c1250018129040d80c402002e583d440c0d1007990b04c199a0407545511400e65540c40150b6140c00508101c001405074407000100c000d401e01c407031002040024051810b6903140130580340444030010b4800c00300c400804401900c1b503400d102c1c03107002d004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 227095917 1250 227094667 227094671
    0x110a0b0f0405210a141305060703140a080103021008130605060112110406020607080f1b070209090703021003020c031903150609030b060d21110f160e090303010b0c0a0f06 75
    0x1500070050081084001172604400c1c08004440104c0d44140e10f07502a29003ca0350030741c4410203402c00b00c80d410b02c4444907100c40b0074002a111223854102c141c06048a200700d602c04043c61410340100d64003581a90300340c075210010210314000803030a4001c0c56010700113150081c2503241c0c540108042d19403078002c200404200003030909c081541480300b0340d806509801c05501e241448005020207000062058140c0d100214550841c011134800b25540c864004200700d0b40d60900100b400d0712500740e8403040344201500700b20081154080d009495051580c200510b08003034001d00f403c06080800e010040416650f4040461014041048080070780442c1d42d40c0400f0600b1441c001c1692100900b40c1c41c4600a00c0b42140006500c01a4580c1800303001ea07410501080a03001c10307202d80450400011290240c03c001d5191404c00007044078081c1c0000d198100e41c1969020f8540302c0b1842941d1300f00749a0020401440b4170f03100a0010021445500212050134405440f050156601440e003214129 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 227097167 1250 227095917 227095927
    0x60d030c110103111b0607140d0905030706020708030702100e0304060809070e1f0b04150e010905060d0b03240609040c09110702040e01290f12030703110a0b0f040521 73
    0xd85c104021603112100742410312005450812901d00c50107583c1c11400c1c0700d80c50309800400c210040c03064500050b0b002c00300359202c0001e0300e041c611a80045810100610400d000d030302226019010311180160301d80003840c41d04e802c0040884405800620400f030500c904c81001030a80c1c0c0b040314a03885104540d0880c1100240380420312602c0c43c2642c00110000d030280420700102034481e40300384484402e801c1601003501c5641c016101d030122640820340c030040118048010522541010110080440a0b135070554981041040d410b10070323003c904176400c0100005030280c10001c83c520340241c080d2482c2607400e5500c2100500380c900003c841d050044e00410024114100340c0113a40c01c40c0c4540000f88152144003402c00d07076280340c1d80c18000c1d04056003050004251600301c002034810700c0c060980c41c3d5014440c104103a8039480040c00310001020704d00031000c0d2080102e1042c082c20f902141d144070b9900e070980c160080400180040e00c0500420f0841141401c0c10101e03018250112100143c0f65 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 227098417 1250 227097167 227097217
    0x50303040506010f06050a08220b09071d15010c120e0a050d0302060a050a0b030106032006030405070905040311010e1f14240621060d030c11010311 65
    0xb041d010b9000034030110100c00140a602d8101041c1c81d50318006180030070303095139224030714048009503541d140540303c85010744009100070960000c0c4210400070440b410301e5560300c1c22030b007000501c000d480e80c444803850104407441d900f080c540690000501d802e480c600306c562500710011083d00000808a90320b4140e09400741002002c1c4002400104c98224000103141c034040d4131820020811072580340e032000011034202903944001c0d110f64016000300040d94a910301250703030000180c99094031003003c107a4600f5034513200e0212842168401c0c060600c00749420202405071901420031000e04c0364183d107494a00409108180312002c2140040200f00010300030010481091541400110706008080300d202c400140340580201d42c44403c0401c00140e00c8040201301c08032040694400e00000c0d0740d48444c9202d00d442c007044890b51800c0880c548940c400c206c005242c00c0e07801030200314404400720100c1c3c20030a41d041140e030103040c00300305e4060b03a81c441c034000d50281c02c0110915400f401c01c6214 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 227099667 1250 227098417 227098423
    0x110309060f0124080702160603050f0619060c02040906022d03011202011103250302010e010c080604050406060e0112060b0f0906090a020f041202030d020c091914040503030405 77
    0x14110251410316106075101d80c034559400100d90001413145840c0450070840c400c00100d42443c521040085403162a00d100901400003501c14150803480b00c03011070f90600d0448161001d0000e40d40300d003610315207004401e039102c80b4048800e0b603025580b00010710202d2440c1c0024000c0001e0811004034100000d1a00b0b0150212191103000d00b04042c00103200c4401d8946030310400e01d80900b090182c0e2028000c11919510598568124034060450780721030300304010a0754800c40e80329030001d00508600d00c0250f4221500c000a440010b501d910100300d0b81d080c95030215411038014800030401d80d4036040c10a00e826420780c0100880d0b00f04401350014084907100f9424880e0003102e200c0c01c1c00400e0780010b001000c0140601c0d100f0520400490300d206408c0e81154031484819100c1a201c554a0740c8000280649003c00e0f03009000f01c0c0c100b007202520210b4800e00d6000001e18a100c1501c424100a8031103118204440c06280e691125904110480003518440c9120780019556440c0034600942 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 227100917 1250 227099667 227099669
    0x150402040f090b01050607060207020a0e1816050405060301020c0115170604021e060c010501060c033b01050c06010e0109142211090718060203090f04020c01110309060f01 75
    0x82071071401a00b1000541030550444c1190012030f0404d449200da814114000d22400740001c0d48181020400281e0189129046104d416440c107015030710000880c1070303074407a10a400180000c480390301050005181c0382e0710881d00110060001410882c0c86040c640c215008501c0d055111072051008001503035040707003001d05881010004e018141001d6002c500300c80c540d007a040052100039000700000b41c80d80e00c01c0e110b800c11400000c1c411543d5500014002e185407071400d500156021021004400c0150b074101c060300c02c260743d100e007941040d240801c111880f0000a504000003000010b080f558100302d02406050002d829031181e51402009004444d0344000c1c41c01c01500c46000c01911050140a4811001c030070f160320850300380d035480c18130000504441c2c49680140c1660610001d00e51100040402c5441c1c3c400b00303039156071130391026030b6680101948950f2000058a40c11041e051507006028511030000c00425100c044601c44c036403d800c2250a201103a224000b00f1a4407081e00b19614 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 227102167 1250 227100917 227100941
    0xd020703030509040c11030d0204051c03020606090612030a08010807060305040206040b091f030e0106050906030c040f15080a110607080909040f05120706050f060303072315040204 79
    0x2040440c61950702a166001c3d10a0080c42240d031580c080e020035001d1100c560b60b56140d1019295038941d51480341000b50882e0190034040c607050040307156145401003840554540580041a50740d4904042010000c001040c00c1e400500c1c80d040c09603540c03403c0019200346402c41d00c80600d0342d81401001c03844d00c0e620307902c01002c2500f40760521005d83c548100701e9050703800e54003071680c0c3e412010000c9800340ca09581204c890052507440c81c0303070040d03059201c802d00c84030300c0000348902070b5034500b0428801025103503a98103400c8852941010310b0582d2000040e03081e42d06000c44d01280301182c0d031895004540c844c0995402800381c0804120014140c01051a802c480f07560514074942c441050074041c440e0198000c00c10203012405002c900200d421400c0d030b00c00b04850300001c002d0340e03c5140340c215620449101d41807901050503814108003070f0f4494040940190300704486a22014490003500e0110b83c0c5160700356201405115090104401c00384078141c0402d214101803050200303c600d40c00c00f032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 227103417 1250 227102167 227102173
    0x1e19180606050f0d020408060a05011d0615090f03060411150a08041419061d0703050c101b0c060e04020c070b0c15040f0507050d0503250b180d02 64
    0xd1105079002402d80d00302d036070b07039400c1e03107444d648110f80c903800070311542d040110f0911071142006203080141d00624141e856040c0a001044001035240c64401c1023624500d0b0300403004200b0703907916400a406480707140401050450b001f1508804681030440c10741e01500c002c40841d1442a09091040020310301c1c2d050b845500340780601d41c0b90000d08100c0060070040030b840184201c042802020481c001e80d00d12210442581c0901a140100003444040b4a00e2030070090b00410301840c00c000720305201160341000103030040605100c10410407400401c80c0c1428000d00750402d9160942810081c09030a00c50509101c1541c20920080d140c0c54080b414103100f2801003113500c13055900400d41c8421100290303421510f58598085c040d040400720f043e000c00400d4050b040005110144040106980c058410780c1c200036156428008940e400d2000985103500401009001c2e42000c40205215000b4a0900082d02500e0f5522600f801041e583c480c262034590044c2d058551050014201072102c078001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 227104667 1250 227103417 227103419
    0x52a010e0a0f0b060d050610050a06140301050f0a03120201020705010b040608151b1c050a180f0303021207030902100e0a09021b070f06021b0603061e191806 69
    0x14480728416400c0008000c5400680440e005480701c2d018001c3ca0341e801007c0e107000f0303c1c1000ca0184d00c10039520606110b00f0803003e0001d50540500401c20030359001110317041c910781c285402e12030010b0801c005036400c14010701000001c0354a0114030351140c0c070240e0016940f851036042c03850a5030f40003008075119510707021003000000e100003410b00d14210200c40b15480c550700c5070307a4011042070180500c0c44044c4001085a0342540b4940c0361141000082d504010700e48542a01d0740c203c0e54800d20111140810701555404200c807190b50719140c62292401516040348509140800c2c00300396210030209031599420000c42ca8042030601094405182010007064448005001010b0520a190716198000788041c00d40000c10032014103955940104d50686a40341c1c83c901c112072140c030074240103008481001741a045612078403c142e040007011942151075510400c002d84045411008904060b905141c40075180c0c01e109200b110110740800004529040c0312520b11809040921040703450104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 227105917 1250 227104667 227104673
    0x9070e010603051905010b12010e010605220506070c0503100506091302010306120317010626070c060603050303220803041112010501080c010905030102070308070f052a010e0a 77
    0x8a96046428620b004aa2030302c0e1000b51181000b050a45101c0701400c00d0008075103482c0b40ca000300343c10000c1c1705e000400350381d03038003d41341c45040d00703020b2400096002c201e8481c2c0e00d400350101c41103056010660004166555000030410742c02141c00301c0305443c0c1c4503000c1065203400e000c005001c0702810000c4c4150300d4400000b0700301420007401020400c0340c00c03e480c001d5910a0f4064400380c00a003400e0344402c456424091301d50106402d0082d620b545030700010400038498110004640070404500102c0d0070f0060101161807030040001c0d0811803442c030030f039002c1040c6004020066001e0342c095540d038100034880840280040190b54075400509048034001003640085a174000d40041c0b002003040c0c01400002c5a21a001c5c4140300b056003440000701d9170300d4002c50340c0d010341a000d89400e400b45a58006041c01c0c4d0280c01000360200d0f54840016042500441c0b03c5002c0728031a2401c1864020310007000000182000404204400342c58203400350070760300340320f240d1080d802c6100400b88001c03030359 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 227107167 1250 227105917 227105939
    0xc04082a0d020a06180e190513030f1d22050106020c150a031b030b03011a090411010e060f04030c0b12010605090102100501080a02030606040507140c0a0204060e0109050907 76
    0x4c45401e040002c00d0001c6615031070141c140c08040e00185a0009090400101c0c00c0c030f110b02e203240380038026490135001c203103c200c000010040300da526480713540b400c01d51000160b810b041001c9041d46854441c08a02c2e25130303592201d500e10101540c2e41c9510596600c7d90a240c11a80305800807001d55000040c15540d03680c46020210003d00002d40e4244d8407911a80c00b103000e003070616800c091491640c071088189c83e405800096550005400070482c07404c0b940c0a83c0603400c2140501900003074144080360200b5803464418000d403c040c1005220000d441001c61000d43c0040c4900070200800b107010300420603414184402096406515424400b942c10b95250100041c03140c4401e1010010b03041200d03900134008082280d601e00406c004640c0c0d80c00000c3d881c1c40640808074402d00440000031030300e10b0b1511560707002e0162070f5110000d454051918580c1980607007a4076200307204947c121f10040e5210f004440180010940d40001540b61079000800c3e034078081d154810700c0e0441c0c2000d200e9074441c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 227108417 1250 227107167 227107169
    0x912040b0904020706060801050c18010e0904030e240703030b0303070816030207050918010c020114010512030c010e0c210a0321060308090f01091203080c04082a0d020a 74
    0x3241d0044c2d0b15100c1703103014001400d1139030040c0895403c00003005030848001c7e000d418403001c12200d245070b204800340119129101c186006500000c44008a00803034402c0400354001e0402410100c1900a488906031415502c060300c1c1032540c02c0003400004140d403502070300703100c220160000c1d0304000741c2d030341c50640c01d00501200c0b6543c00759811210342454400c2060200501003e804034030241011402100828652880f840b0950f00301440c3c0c1b00128814891900707810460241034460f0b9003040c0802c40700b08802e40c111000d5110a20400103008400e1040500c120b940a00800c0780440200c18802c01550700029103072250103410a5076002d000120716110b12a0b854504842030318125580504100d030359881d00700809103000b502104011240b00140a014800c0f500319090034140001119002d036030b801113010000300e42000e0303800a406a032007c3e4010400170708c15424140c8904000d0300e080344c1206011031011000c11a450085903d4042010381c20013a07668408444054000c01d0b440074031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 227109667 1250 227108417 227108419
    0x4050f040b0c0f0301080109060e031c0b0a080303181c050403060203061c0b040c1403150403020c090f010e010f080606010c020a050409050a1b1a13150203030912040b09 74
    0x14080000d48000e2160115862464441103c5459507124845039009200c8107204480b43c40c035064004010380f81c000155601803901200c3c8882c0524420440006000080d62054120500450100e00c1b03541c280702851192a0500d51510380e044070141c1c0614040802d05038191000380c2070308803039500e03900c80112001d5036000100503070383e9198170003c03400c07440b29021141e03500e03400c7c254801c040203c3d01c1c40300b60099008400e8035501540321084c0202003462011a1036260340891803500070200380c1c0b0341031544107000c1e006407a583d040d55008241d6440741190a110354581d40340050002032204400d4602410800c42c85020b030b00d041084059507075102904081c103000c0071003002030441d615a03d0100107441e0141051101901a00e401541d95500c803030126200324413208010085d01e10fa92031102190720300d001e2604042501c80c11010b141c2d01060f5040052001c1d10004100e0722074500082c0c3c0384545560045940703250900c442400d11150350301034400c0c12800c0100b0850401c0a100707031070401c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 227110917 1250 227109667 227109683
    0x301140603060705131d0f01050f0a060809121207090e0c1227070807150206010608070c0c0b0901110d1e120f020901020f0109030909050402190308090f04050f04 71
    0x80324030000b50322003242c0c040e43c902003041046c00741c103600311800035014a1450800641513600d520800c2030083e2071040a5800c0001610100809482008880c0e0012a640c0907200c0a44260181307803440d0348545103c00f0f08048850501c4943e641c00441440203108883c4d01e14402d0a10398011410352084400d10262029031700e01084100841001814000c03840c000000002000200166200c480e5803007403d20a01803c5800504890041030513098051240e01400a9038240303582682e210760301411000401c034011039645e0002c0e49035500d0038041c0c040e91040d25102d45205000400c1074506581052140c0c200b10f154501c00c03a000ba40c4d01501440e042440e407110604a2001c81e1100b00f00c80425458505200e0641901c1030b19500400d007248080c2d080c1c9401c1c030845402117090307a41042c801030000d5800201089452220781c8a0350f00248010130507103081c4400c0c07018000d0421540c0058070401c0c1d00091100d050714002d80c03032090030030050f6020700c03162412421207481ca180013440500655 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 227112167 1250 227110917 227110927
    0x170d120504020607060c0e0919061a0318030c03070c0e0a0912032004140a12050c0d080f0a030c1e08060f060405030f03070501050c0f0a030c0504050409030e0301140603060705 77
    0x85c01000400301d43d047c094040b01c0e4030320f05a0a440165051045400c42d503070f10b000000f040214001a00c020325001c200070b0b41d40b0703548500c0401c54510f05402c40211450100340103d101000e002c0c002080007500600009440b1410405213901100300946071103410303440d11002100146001061440560143c14002110b600c030707101c0b040100144801284070b0320710004001c10040e41184503007010520981d0403030540c0d07444210207101da04003543c1c094003a170b2010703100ea030322483d05410950307106201c1c131001c0e0b04000241c00c80400300e8010084100210f40c49030854034005a0140321180c0c0d00c1128040c807a015440048050800c0002402e924003a0303041c0340f28034a00d9195001254028100502261b080117401401d4546940208004413203079400e010209014103a82c80507a1580c11311103808503d40148200d05a000b04031510074101400f005120011343e650f251700c00c0b84441c1c1d0003030f241c1003c82442e08003091b085500c03451000b144402c1100900c4816100050000d5210640e1706200d035560b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 227113417 1250 227112167 227112191
    0xc0c06030112020d08130b07120804032307080a030b150418051815070f0309020a1e030b010810060b0f040611070503010c0e0907032d06170d12050402060706 69
    0x1880fa0903c621403080a0950010740141808001e141050003581c010704415143c601c00c4ad02c007001038401600091524000b94282c0b0800035111040360701a294151914046a44020064000c404050f0100e5170711801525182040707192885c0c0941c18400e07040c581030070400341c02c1001c103010084080d03180d99800084c42500001139405a42046101142c0c3d410700380d9802e0680c508811100100091405c1d103841c01414060b004804039150b0040c9010030441c14102c40c49072000216441d1030390154003402c0040892060a4100c0c040c0c10900040e03c0b1518007544003c0c00d070342d000c0d84624640d8404000e0302d40f0451142060760f09480851030700840ba1000310740c01b02e1400110703800059240d442c01e0f180d098490380165051465070b101b0f4400264958410070140c1c12116410070127107840d0000c030100d001500d0702880348030091102e400d000601e6502c40c27044030801040003035110382e40d40c405c4060462054000307081ea442030450b01c8041c01680741c158045403450046034070080200f41c5941400f448 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 227114667 1250 227113417 227113433
    0xf03060c0c0325021801080d030504020f090a2c0304060f020a0501050705040302040e0105060a0306021326010e030309071505160308061504120f05071a0c0c06030112020d 75
    0x140b05862003500070f05070600e02e04800304401c4201d080f4844d050042e8031007808025200c0c020704840d1b42e44c01034507040098210070b901400b001007049a000d1403000c52041669942c02141e40505040040090b82d684a4191412100f51101164480d440031220740800400d000003214144c540e2860f2001c002d04060300c06900d02100e0f440001e2044d401e0004115100c1c0d804000782040360b008407000d2140c240491004cd080303840a450b442d41202342544e0500c0855000d400070719019000007152080d40e561841d05504d00050110401c011303a00d0407000000c240401d000c1c1030103d28000c00a075195081c181c8072169264403034401d804225080d0340480140794040c07070580c2c61814003c60700107050030842c9070081030800216041c130b1140707070b04000c410419100102034800341c4094014603890202140c0381c0001164002504407404e20940c50085411601c11400010030304583c41219100d549020903a424006200d107128000d900c02e0004000540690510602054050f91101010b821608008103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 227115917 1250 227114667 227114677
    0x901030210020a0203120a08060607080d1e020406030203012c0f040f0c06051902010501080a14070504090516120f081e13090e01020a080402191a040303020c0f03060c0c03 75
    0x3605d402094149481108620b0050802d0300d4182d031960042c0d51002c2c10003903103018a4a004d407020b6030500c0104000c100d141c0c08600c01280700c111503d00c0410319500300c8c0c2a41c3c031a030445000070380c000c40100880c0403c9502c0c0c03c2a98440380c40c6854440c1da141c014a0258402081d12040010303030301c0460140310100d001c505009030001c2a080c0c4058a0b8000604540d0221343c2003170a00c07041c09480401c44d481841403034140c070550805000c55421b180c5a10a8411000700303920040e010707031040010ba03640c962140340c001034400c4015120076904103c1060b0155076650203680d025000844810029880300c000095240d07000e00c1041c1c651030000308108540d0940780d0300580090000a9070a14148401c59140450700703807003030034044064201c1e500c900f41c2c0582d01907000420061408100186042c400c0328030405d03103210190702c0240e900c0c0080b014405e50749a103c0724030980003400b442490f43c1840181e1100b0300c160748840a05903c00046030747d07040014086203a03000c02040801c841a8144101d40d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 227117167 1250 227115917 227115919
    0xf0c1b0307060c170c0306010f05040f0905071b0c061d0909060a0e0c13110f070c050f010f021b0307080625090b0901030f0f021c0c0e0901030210020a02 67
    0x190700e89509150070700003412035a0704200424014000140701514042002e0b1084032200000360843d1078290041d41d002ea0800701e2442071120600000c1105400340d070a11004020300d084c040351b10308151101a224902c02d10f94000c80c0d0701c408101d41c01150001c1094000c5915500c0c003035004103a032030f2920206001250340c4d01c0c0c0c030070350303000074040125000544c890260300819020412078108600e503590302c0160a07200f81c1c00c06500d0100840c503400c6503005000003194902d01c14500036100350380c00ba05601c2004225081a040807040c0003c0c01c03c002000840c6100f0300300b101c104614000042c1d178a1110704c001030943c0b040c105600010b900c0c00d00c40c0c44010042e8804581060520711000951200c0c00c40d0480b4148040901f20401070744111070740c00c1203807072400001e8600405070004501912106e101002015101e01044000b401c0740d100801050386824107030b58030418109140c3d0150380e00650b900b0104003041c00308134907030b50301d5880b8541129812120480700000042c02030782000d06480020b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 227118417 1250 227117167 227117173
    0x20411460801121e0b04110609030c0d0501091b093206040b0a090e10050403080711010b15070506060105040f0909020f0414070e06070308010303030b01020c030f010207020301050c030f0c1b 83
    0x82010031440c0c040140c0075500c14960750712901880700c140941401070218640e80f60b40320003030140d003608080b10300b648cc66010350008100103c03280ca81d901c5c00010664540c80c030030024101003080209601c504c00c0c121145141c2ca014182c2203020b2038601825592544003192141d030042002ca40c0c84d0b0303220024100026250946203942c40012000500c100110b45400c0e014601904004034400d1051034411585521612915200c50004aaa5a03400021201036658842d0300309420fa461000b24a484142001050354444041c82c2c86801c0000140c003890600c0f00c00d02051000e681003c1d410030503a449070070f00044c1c400013030000920181501820a400c540b80140075980d18034120401c611034004c9458000000d400242404402c0c0300720003016001541050051000908c00c0d000008400350510444490485030b100081c18200c0c201c042030b20aa44c0000d20a045040038003400381e02020340c00307226046140c803800c2d281c18800b004001d403034041400a03501d5500424000d510300030340018011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 227119667 1250 227118417 227118473
    0x5060406090e070608090d0212070501090b13030f1d0f0418060501050a060504050f0618030d080117010e150403020a140d090506070c0302041146080112 67
    0x202e640300e1409016000c0064525000185011000210014100c91544c000c00c2d02e1200304070410001c0e000070b070044680b5505d440c0c098022905041c00d40380644000c054550842c1c400b86406025211180e143d441813254040c21700031445410f580280e030380311082c0c40c450020000c00002a008192a114070101d00c402000d840040c460a07a02c620b060700c0080e00c80361046504d130241a6802d0183d4824103600200ea5a030702c040d113040048c0504440420035884654103150007001030b052019100c25a4006106400100001c0119841d8954001000030003003008940304000c0a480e0004c0d04010008829030001080030148200320b4444d281d41c020403400311410002010549445a91400400240302c03c0070100d40d170702c0c02c4411996540d0b405642d004e813076413440d1f0920000d0010140403131040340302400000e124101c20240f03003000381c0300f8500002a101403507441107903004550803c12a101c5c0000e16420306a070300403642c0350550720005400d1552180600c4d0000000800e4180b60340d50303590403a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 227120917 1250 227119667 227119691
    0x240f04110f040303020106081234050f01050109060609030206070311060414120f03131e030e0a06050702030a0308091f09020108061203040933030b0c120601030506040609 75
    0x2014000307880c401d40c0203010648c0c0d105034840d510401d245c582c80400701c0401620489186d00a01603d0002c4174140c0c0803140f44170018031600c041d413075040c03c1d2103a0b004542c50306024a400e20906014040e2a03404116490525500900010980c0402030082c00c00085843c00d0600500c2c05050620442c02191500c0c501440d04464070348455502c0001c91085250041074041c84400b514410036a400d2030500b10b9071864071000500d0a4000180d900d031110310003000d140c0d02c145c0603074114a40240c4903000c5c03c41c143d03028070284018130351064080020600c90200140d60100d00e07401c0b80b60b0140b402c008640c48200d01c1398200381c0c0c20b00080c007400a840c00c61130401c250540007040c0c068001d0704c5081e07041e51850140040e006500c0b01004207500100414403580c40198404041c1d50b0340300040c03200c2003000303000126403886c0007007040d00c0000d4103070801c00c20403004944041d8084e4112400e58108454054402010b0070301400f494103247e00d69001811035111580000b0041010aa0512100c004c405d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 227122167 1250 227120917 227120947
    0xa050f07140a030206070509010c02040f200c06091926070c06020610060906140417010501051c030509150c010911012a1b0801020a0305060405240f0411 67
    0xb81c01200513018100c0090b50550254060711102481a101c4810b15841c0380d081000620701c02266030002e50b070380d00500b8030071801d076501220105900360b003044e580c0203000003562400c0c0000f440320130b56910002110758180b09800074a104540d00c28403451500c1030145d010500c61010203145a1300a801252000621200300c44080c00c6807100d030261012600c1e007030074941403a405409105e01041c844241007000d280702d440715040481e0314581848c10103440c0c486501c41d008205182c217405a4486006005074640a14424865002000f81d568880c465690103000d502408454078400c008580740c4400c604040030865444100c1040200900d031560f15100c0d80451342c2d698641c0c0020060000000e070000c44001e070004000d0b00f4000c1d0354050065076100d036071004028803004070342e1030100380004406409002819009038140c4010895103440000e00007201c100032720040b80580368164180720b20002d00c4280000f610305503840d010160004001c100505204206140b640e0f40001d51b20740c0c1c0807200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 227123417 1250 227122167 227122183
    0x110304020a060c031e0203120c0d1b171305010f0905011a010c06050a0603080c100c0e091611070621060b030c07030903170306090c0a02030a050f0714 66
    0x840740300722007540b158011075a4040103040140425014081c4200804150305241282070f060700c112442c0000440b000012804241c641030030040300402e826080d2801d84c0691850030280708074803078408809c600020929001c500112025010120124241811480000c906240c203d070003408100c01170091800101540c0740166204d51a144c003454901004080d64080007005960f038110301c4489486900c0180405800104a0750f40c4650005c00109a20301030000c0c071100f1300207020940d4503282e0201c1075454407815102008144500c00509548142086411001d2040480c110503101e0b070003aa41541c10300742c0000306116007580000d1555120501c9221030b20072082d40110354506500b83c034165441350007020301040c41880021500c40450014104a178000d00e40103040e10780d240c42d1841698501c03404080080c000008011140c201300b084950049124000300d8540f0041c402d00a440340207848194080050000380324081100c07030002d4907940c40d0400d2003e00401180c000300740d503032880 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 227124667 1250 227123417 227123419
    0x518010c020d0c02131803020a0c0e040312020921030414030a0b241906030507020a12051810050a02061003020a14120105090c03070e04110118030611030402 69
    0x204014000020701c0450000401d042e0341d260003100b0a682d0307080025170308440c40c892980301c0d41c0303503103c400608144491541c150b010740c01404078100303e42850080c800d015000f14260340365550a0100095220b52403031450240d0090051b02c40e03d00900044c089441c0d00d005034032402c0c1308900058660800f00082c8101c1c3c503d07003100303a5142c03658420f041e160b20001306c1c042e000303030240c0000070000348800c50b4a05030015800a42a1500900000a03803500d0a4070209054256525070a01580c0e03018420142c2181c271600080511305080e580308214961400b42c054104080401c110030140004490b034080701400805d80d034120000d1210003080b6400c83d041c0440103206400c0402c01030000c0e044100d080d81d40160050021500381407041000380c1e254440c0303541210a074044990002428881d06003d14090300241032303029040382c2010300d41034554210500300d012001c00c0c00000740c00a0304082e0382810a00f040c0091400030300c080c0e4484106640050104d50a08103112a078840510065100b03501c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 227125917 1250 227124667 227124671
    0x2403061505030106050d0f030207030b1003120203070c170c04110901020c0a08030901051e07060b0a0914010915030f150f020a12110903070e0405010e0f0d120b04051801 74
    0x541c400c00c01d820388038107115890b00010460100c00204960300800d0f1042802070040390036681e586e0b80d440420b40400c90b013544096000030310610400160720301400c4000c04a100071030134072040361036120802d00148503a05000f50481440020f081050008034402e0b41300510130844011640a2405954000110039006010b040e400690501e040c410b11b80035180c2c0c0c10021801c00c4406c000540d05940140c035540c0340e04006240c42d180341081200108221845000040f51500c0c0a009010010380560030000c4503504020351050701103403038400141100d040f41400301d4050100954991a110140c00c09404100700e0110141031100d0b503090012080c3c40c81c0003c0107481001c0600000f02e00440010380000b80c140100c4070300300d4015070031811410440d000c1d800d10b00703400080040e14040303156006040c038242960401007800320a10503c481c040796200600111480d213605a5100c4491940c1202482104890810804019030104047c4800904200503030304001c0d4802c000e411081c84420650340c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 227127167 1250 227125917 227125919
    0x60305100509042003010f0f0911060c03090409080408060108070f0b0f0403030804060e03030a0e010f0b0102120a030e01051014040e0601050103020c1501060519030c0203030a24030615 81
    0xc10007640340d03841213030000100d082090b1400a00c840307103920740e403d080c0d0640d210051515440002d00c1003001c6107080742c00c000b48140d5180342c04403c4128940d03440303101e10000c0c0034545002d8004000c58400010031640001c1110741032804150318081c40c0c10a41c254803620002180310b800002d0300105581032031f00c5400d000ca60300c0101e80d9081c0300b018100c0c0d0441100f0b000c1000060f000c0d100c101c1e0058031420002c82c01c42c00381042c0900e1a04202c82902149845100702d030810b000a100f510b404204803507050041031076120010b550f603c1c4d254503034054410001024040b0300e10030b030302c202c01040240f0700900032810079007164609111180a00584510440444c4040340740c544207180c1d14003402000340020741c5c07804006400941203c00e1810550003100d040071010a07000030418040d042c191103294480d005801c0100300360401803c01d9083c1841c140029a01d2030700041501c0e0310011800002c18200b1804090304031580d2402110310768450901c2c008010480b03141c1100c182034014000700c0c4461 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 227128417 1250 227127167 227127169
    0x30906050f0108150103120e0f030a030e01030c08101203021905010507090806040b01061d06040b04031e0b04110f03010e0c010f0f080c1305090a0213090908090f0103060f0603051005 80
    0x8440c0a1000500080c200c107250003044e4007032100580600401820300c018840a08007080c22f1404071801100011108041c03101d80751f0300344c817030000e068034280351072080d41c6450020903003a03c00c5402041031254894003c03004242c0300300035100d9811111984c26995a2952074110f0280070160345a2002c5400c080740481c03425000a0440d210b107400800150080c1d280c0039054402200034569440c0da80900840070302e80307440d5000108000d0046000456541e455070610389440301e05100c1c242a400412401c0601145102c40c2a5800c1234212049448000c8a40c0005e11500344980403170360513500701080b60600042c049041c2030304840a89490090210f1150100e801e00c255444d010041a180307804283c41e0f9007042e000d010442c201642c9900b0440c0c40301c0008610f028101c42e80200582c00191031100ea800b980c220300d00402c0041d006210090301c0795079148a6008652050b8000c10100f8040c00141c0c0c070981003140101400e06201041c40e49072800207001d00812101c49005a20000000580b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 227129667 1250 227128417 227128453
    0x414030607030b090a0504050f031c06120201080a020a0e0406080a03020c060c1b0a08030c0303040302070608010b030402010804020406030b1303020f160e0c0909070e0907082203030906050f0108 85
    0x11458001c0640340b499407520304400046c04040d1082d07409200d6200340e0000b00c00c04100070651031417107186102d00c0b8400c148440c0140e0f00d954028800041445900c500180d80141000740c00c130b92200d0000d600d5204014003140d040c82050140780e07000c2d091000c0007400c0c400206600041e18025400d5440340e10003081407050b6480b0301200c80a042c0d000000f1407040b400b10000003501c0c07280090500120319540c5684518541183c1d04240382e9810000511040540410070040200303000e0034150820341c50300701d09040b18000200043e0600c02500d0000f01156503c0e40110f015603409800d51001d414a0303c10311882200924086002d446019040ea055520014214108800c2c4101d402c174140e00300803001004040140c00300c1910003091220f501543d540c4004144104080d98a02070302c1d8023000b08025411001502020911085000344000461ba013800540910b0103071084800c3d000c2649000c500034060414060b0146d89081c0600007040c0c1c400300399031b0403143c044086540e04000303d00e038054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 227130917 1250 227129667 227129681
    0x903030506040b03030406030e01090f0308010e0f19050c1608040f140d0f020310050f0a1103070801170f012c0601080c040b0409020315100f060912060908041403060703 74
    0xb40c117520a110800c041403282d0005001c0000140010903001540d5551174002005440c08401040c040001400f07141026a00c0c998440360003085010181031058003418044a80300558040c02e44804c00140355080e03c030110f40c03000000f03041111041c00c1c182000c1c3c002c0d4010f03006080001542c114001003101c454441820706000c000d120f660300803502ea40d19104502d18400407a01401007102495841e015882000c0c8100b00354202007442d841e04814400440b1107080003081201320500c01c0c0070003150300001c4036041d41c0c172041d1048961107030398590f145480b598880d000120b608080d43e007200242030340415141c41020303094000b403042c04400c65945a000900540200760300074004c5400514080d0403030301a0603000b41c000030b680d00440d00401c1c140001ca0020704007028480c4240a01e606031071881034002c0c03468180404045040c041c00500541d00d501c601c0d10180000e41a500c18412183c0c400640c41da030000c0420307943d5039242311502d13107807a038020301521a00230f80d000105507600a0243c14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 227132167 1250 227130917 227130919
    0x101502030a050d050604090c0905010501030c030621051e0c030f191707150507020609070b090103050a02090a080a0c0e130f0f0b070309140a03090b0c12040303030903030506040b 78
    0x5080031014103048004040080000d1b51154a078140310002c07500208404010b040707044804a410340c1880000f50aa914603d80f040400d07240400170403561607410040c9e8048005071840301d00303500341c40c103001d8036040d84914095440b001000c8891201d01000454403c000d0f0164107841c0b0150031198510f40300c0b800c00156003260401c80300c00d00009121101c4583c2c100c107030100f0940c1003501d291580d425009160031143d06a607622410f20201680411505a005151200070003482d428440d4592282c02403140613030601d511003001c691846c0300350701a00c1140a028040e0301d00b07242d40341c0b0030655980601005480a840d00c800100d405607010810a128201d9003080c08002803080e07458038450258804191540521060060000780002d804203015560039a008150701d1038504000391744005602e203070350b042e9004009060010b0381207001c500c110b40020404a80328178007010924240f84150b00074008100000601104041c0c0540c890000b150103641c0400041d500c5000380022908100340c86 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 227133417 1250 227132167 227132177
    0x503070b030c040b0703090902043020010302091203070212120712021f0e01180203060a050618040b0703111804020f0d05090703022806030b06040302030303101502030a 74
    0x1d0006513542401000c0a42c804e24040c06940da8941d1287e04030b8020360005218035480d40c40040f0fa401b018000350f103084c50410200c3c12032010b03e61f501201e840e406c003003000b014502e03000c00e042e090307020b41d0640304d480c0c1010302440c490000001041391258031100d030492040d482e140103c0010200003802d9040d0314a130450ac94134298854840d4800394a11108400443c80743d040e00c441d180d030a92201c0781503907008140100361210586902425540c605484000d80c0842d04003203805a42c00080c03140c1c100a00300c1001545844080c04200d0b4183c041c4030400c400943c00d001d0000b040060400b06101d09400d030b5042203840c110f41c410400c9072040c0c0c42c1450181e002110a00064a050360041414125240801f40342c03d64060b450002c5c0c1d8401c85480103940c006800802c19810102000610000303500c0c2544008445550b050071191102d0044e0000c060f59041001110703124041200c0c0903640090442c2d40b0b1b4a4001100c4d000803095001d100070141c09041c15202d032900010603030b608940d07540c070b071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 227134667 1250 227133417 227133419
    0x108061f0b030a06150c0203010b030d050909090a0816050d0801050d0237080601050a05010519030b040e0c01030e03030702070e0a0f1e0501050109030218180f01060503070b030c04 79
    0x807a015400180c19840210b6441c0b10004000c421540104241c102e42c1c2c8400c01c2a07141c60040500b100c680c1817410b4065000541281c01040c3d020045a40603842285d4587c8680c0304c80907c0c0e40b601d0042d48008100090000e032220220f5054001c1600c01441075040f68500c848103c021501181c003803183d180c112183c100400011302d084001c039001418646180300c800e40303d81c4400c01600c4120013540708c401070010000d02c0030010500c201303405003000340c03240896070f40b4160000b4402e1242c2142c0f14800d03103c2417040382c0d5051080c1c0040c100074000130000e00010340840c1c11592a070350791100c4c841c0030070301d0000308911181c000b0054074030070307a8141c000e0400b003450300103000087c3c440200009020b40d030720203130f10071445094030400900e808055500c2c64a04000c0304200102d80041e0406810b00c40b00d04020001a6941c4c1c0c0c41000c1d001c1900001c80e42c2e520f4000c0d40b42c514060f03810000c12a8000d0784410344641105501c003030204c8000b00d0407a40807669403010350f2100d100c1503880c0850501d08003c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 227135917 1250 227134667 227134679
    0x8031b070b0406080702150112020112110304020d05030903030d050105180105030c0409170304050102031b161e0606091e1803030b01021002040303091a190e01120e060108061f 77
    0x1c4517070100e11801a0ba00742c29001031001c400072000d80000e100021809100070079564030a8040040c280d0a04003045000c0500b40300c00450b00000304002c1c07042412a031240101304080c000c0d07484105020b401c036605c030344002801c1c0010300024094680511602401003a4032803150402074102d600260280c40e02e20a1541804064852143c007554469074890300705040b00146001144118060000141c8a00301031215201ca0039881501000480341800315111803100a200c41e014283d00610b5486000d2404800c0b01c0e003400e1000300034213250729119000a091010360858007018000c1035002c41003c241c03e07440e0048502c04044449070b50a80351024000078041d92000d90f80010500441c3c0145c103c0103d1081603034429001140001c01216003000f905019060303200c01d00c0078401440d0304150b41d2000038036110b031005000c40200002c9414041781a405285010703236604020030709010307541c510125a50750f42020f12641c1c2e03a6208107030018081c0c640400c0d04449407601090807580d0545041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 227137167 1250 227135917 227135927
    0x902090613180e0a0803061e030f101107031b030302121e01060804030f0315080111070b060108060a0303030f0f0f23011820030108031b070b0406 64
    0x1020540c0109007003001e18004090341c107409000306902c4140321455407482e121501920880340d00d03403500d0340c030100c540b20000c2c0c031075803c2d01c4d80403400383c40701c0545d805052102c41d00700c018804119054010380700d0b04110350a000c140042c4100620005025901c81110b001840e8800c0c1b440160020f880b00c0c0b00701101c41000b52203240254004c0c40c0150404001801d0f2400703c840907101c403441e86200c84410f940c000c00441c05107004103d94205280507261a0f24043c14814007149581c04240c0c0e2141086840415540b03060007030403c1034020804980d40754990301c81940700c5107003036498581c100e0014207258404c91009100b4000030303284004251456500b98003600160030031807549515000c801d51420140d12459401d202440d130003240c854481c10002c3c1100b003031640ca121408035030354010b0140100382401c3e6802c1403902c01c4000380c03040c2c10303000e51518100d4106500000600010000a84244c004068010040300247c485015076002d40d066650344c290b8440d0700342d8844144001c001050140c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 227138417 1250 227137167 227137177
    0x30c060c02120f161b080105060105030408030f0423030403030909060b1e0f0712080901050403020d18050301020a030516030c020601030303020a0c021002061801050615070c08121902160902 83
    0x16500c110000c060b0f51010262038002c500c0401d4170b680c01030104031100f000d00615410001c282803003440c1d13081a880e4560f19100040c042081d40f18000c0100b01005500c10031170601104143c900c480000d0091400c64413540b041c8401d0b0000384110102180c5003c040c400d0004560742c0040203803a016201c0441c801800034030000164864003844103499081c0b6000081080c00d105c0c031070540e100e10304544050400035000e080954941c0c5032008100c002600020201c104100380c0c242207000a8014840003c0481c4a4018603095400800c41c02242901600301074020150702c1020f030079021184108070200c8145541e82d000507405030f801000803c1c002c3d070041009900c01e24101c1d006a419801207041c00400b03120460050f4411800c00884040440c02c030a402d03010744000348000d041030000585106030500949400b12000150402001280f20104000b4071044045e00e5400310305803400092600702101504c01c820352908403410062000c20f20148184040c0780d042c10360340c244a4200029041 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 227139667 1250 227138417 227138437
    0x30d050c1b010617010c14161401060e090607050708030703023703090804030b070203190801031e2001110102070f06150302010516020103090f030c060c02120f 70
    0x208100707103151411004034a8024840803000401c0e20b13071414201524048800203004c015914100c4e103130842d554003600310f5591b401070120460311181b07809649160880503000003080d96a500c3c1150600705010342081c01101d0060050603116505c110704d46446031404c65000e80021020054100011740400c00341d50000c2c51840c00600303046104d0a0f092003000007030b9080201502e000e01403a043c8991b5a195483c400b814070b001d00031800a9030b503090260051380801490102d6080002c0c802c07510810903a030351200381922100c54010074600c0a030040200780001d9448021490288150300c040013a03031881194803400200d080c038900100c442c03011600c122414108031b40c014001c84030103401d00141240600603099804a01654a0030710222042144500c01c4c00201000c1000035030f8201b420342c7c6600a49a0885820041d5440128002d01c4400c20050103008039001d0003060580c0072090588061040400300310400103050113036039a038000070740352001080401a210811210801822410702 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 227140917 1250 227139667 227139691
    0x12030907030c03150f060812071109010e15030606060322020301020c0c030c100c17090901030f060b0102010603050606010e060c190c14061215030d0807030b0909030d05 74
    0x180325515608500d060f81e000780e42041500c3c4040084501d180b180c00ca0140405104002492078002d0071341c0c88007800c61800c245040041021307028008000203034965400d00500311115580c44d0034031a0100312050b1904000b04610205030100b60600081880c040c1d80c00900b940c1c1541d0300c1010522455061f20903c1c60104403500c03000005840c00d00181507400c08c0b0701c01401d0b480c1130240615203001884c0030514400d80d0307104481131103c1e401049121216411880d40000d0504161284600b0f00c10416002e0f00040d0244c0000140a100d44215031107912540040c480c2d41d1550004900b0f0300c406001c040c081e900280003007541507011318078042000342c000e000503041c480030030305a90600c50b0907010f00e4112000c0450200400801c1c194a80c05050401185801c1200c0b010104a860140c1081710400200043c0415119076856034031301d444100090894600000b1030324020014503041d240324001c02d00f00382c0d8609c40da00e000c41480f40b045000e07800440c00d040700c402d80d06003d030070b000d0400c8007048 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 227142167 1250 227140917 227140919
    0x20a0201020c010c090503121c0b061b010506010e0d0209010504020c0c061603020f150c0912061e06030a0305090607020105160804050a0902120a0b011206090f0509030c12030907 78
    0x150b013802078040c58001c580b521031001380381900345820000da1200e13180703c042041000c0e0308403014158100425145016001698030351101c0410340702e218040c03003004280103102d500201c229054010910681081c2d80311040c0004041c14403c9124203203000035809140c3c480107001e0380c01d042d40901003100424080b22900c10034500465a42e9000c0c0c0b0150807014080f01c424010300d40c0401c000d00c20b200e100c0004081c50f0240a50100c40f0300c0f07025100503000d400c0042c52115a07680c1c1109151210703444415507019050110342c4501c4102a400703038051215a400014503545804251103940300d0301501d4140c40c003941e80c3c08001441c2d1210008905100050148880b12640e00080e040810310550910390f032103007404204540c4401c1c0d81c0c40080043c0c0100304504c40e00011411603074102c840004041500211280161507010040300956521454004000345003601a009084a0700b40c49104001c00d40f111031003180c41e4420040307100040d6110341c240c60002c145500c010342e80f1800f840700380c0c0c07182 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 227143417 1250 227142167 227142187
    0x40510110301080601061404060c15020307030b09150d0611070b01080601030302010b10270b0a05180f010c0b0c1603050703030b1909020a1b0f0c27020a020102 70
    0x100d411000c005545400400188654801001180e000d0300140c00c06150004a1138400c0b011407082d40115000c0140c4d8407402d900f0440080000610304007640c905544074505044020300030301000b00074510a00a010200d07401c0300840c0d04d60f01c1c0c0300c20050a0110340c3c1240d9140d8202400c400b44808101c80c0007001114041022000d02d47d000e4054180503094a51440c10300a0030350792000381f00d0303214038030100d0718802c49501718484902480e000b000503a52403132004a4040000301c02d51111416441c0000c0100003e64050000c0c80141c0e1101d1400d0302145150b42072000810711850524080360041201c440841e00c20480e032075002040035400d610740140d102040d42c516003181000c0340411004104101019050300410b000c03040103440c903400392010300e0040d0380201090301c56880701c0d030ba0020709a081c4900c580d5498103c00301a002062180300c0c1450098014000c0441c140c0b228404d01c0c2c8046111000d00c4846851008a64481007912110361030210095102841803000e540d402c10100804c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 227144667 1250 227143417 227143421
    0x91c03080c0a0210141b090d12020c03150709122021031b0f07060305070203070f0510110406020c060d140f0a060603092114130303030b0d030c0209040510 68
    0x551150411850729080448064069410b030b0401d02d01b0200d0306000b00740d034548900107048140d036008000c00043e4214090f0590511080044441e018002d10983c01150001c03a9a181e00940656a40c944100c2d5076030f41101a40f025040700500e41c10032018541680c04000c50b91700c441070030060080e104c2910016503144200000f0303030b070044950404120321160700240c00b0b0103070115800302d026022820340d03611701540312080c0d07020303040c140359468004c01c1b50303a4420000e4031043da50050a411464545092265031803206200c00c11415081c81d8420b000d40d5080c405503000c4a00750b40041c00320045e0b40c4100305964020682e2450741c0c60707681100b0300d41000003d5085004100e50003104446042140512040e45c0841c0c000c2000c0c9401c20410400140149600c4555000b45c2400d400301401c070500229100c0030382d2103070f400c50748001003032104108018082c00400c40b44292800c0080c1c0c22a001803003912000a040900031880201840700581424811141d01500ca1403d0740c0b680c0b007403645a081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 227145917 1250 227144667 227144681
    0x90504020f06120106080c07021f0e1c05010c030212042916110712030e040b0d03020f010501050d020906040f060f0b1c0b0603061002030c01050c091c03080c0a0210 72
    0x1c07292003014010400150440346d229040340352040d01500e0034200d500410444140d01c420300260304070241c03510a041d07216036000310180d00001c0440c1911151178494014500c5094000d8481c0d51030f00070003540d030901078400c0754103070b8404502c4480c15030344586500e41000c0c8400c0c8040c190607036108502030343d072202c0c03600c2522035004000742003600304003140005c2140141c2c072140d20060740800014060280d2980c1c0c500c695550500c2d008036240c01c081d0105000d003030002521030700500030f000400100758012503940d82803104600200003507a654002c00c01c203580400e00294201c0400400b06159003000d8014a403284489440490826135a003088d4161800d150b002e1075a050011079040031000040c0c4403c000318000c5c82080c0304080c00c00f000a4100c2c44040c250f035101e000c805242c400918024401d41e0350610600008200b103186c14504907844e0340c85016035622844800c04071011180c0e0901500c0340054042d600c1030802d039180000e4082d1030344806c81007015841000700ca81c45152480c004d0030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 227147167 1250 227145917 227145937
    0x50601121a091f020415030b12011103040605090a0203060702030d0c0e060f09011713150c0e01030b040902090408071106030108030a0806130504050a020a140a090504020f06 76
    0xd5003001682004405112030001c03444140114805000285500049964003015116920441410710750060760080c807550348280040b107500b00d40307500c1c05501075200300724401d02a40c00140002c007580e0b10130700705c40c82841706c2180e501e814000f08010690326803000340e000d840b4504442e1080b0441d0000392030102c04948203c0140c0c00014940c440840030701458100da20941007250700401e17918000740c002e00420f415408101d40220b0404040da100b51100420490324045c0ca5503e400d008030340b41c0204002140c1901c49038500c41502aa0003060f00c0b9010381c100c074598502c60001103c40046001d0204a4455940b05071154508030141c0e840d07244c50b6004610038405180c0d80c452500d400c000703a1024890340d503c06d05092004010011000c030450300b41c030741d09107410601c2c0c0e501c03840080c00d08600070510944407841c0500b0007080000024110702d106000302c8540b000d6503603448012144442c803d40b4507400c540344070020440c0c10b2158200750381261000307149106007050800801d48a03013180c4505 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 227148417 1250 227147167 227147189
    0x504060902130b0f060c0111130501090e0105010503070c050c060a0203070b0a0c12150e090a14071404051b03070507030e010c08120604060314070e0c04030c05100c050601 75
    0x3240441c42e040d08002015001410203010082c0c10307500040a020319820340d81d0040c80e0010741401200303420f500c400d503e020426841921005c04081214180540d402424041006136802007000d180140c242c50480f40c0507035900f8070f9541e404500710f4601c0f800c02d004880a10500c0c401ca80290345a001502e00344a0383c0d070003540c031100b0340e080950f44000c02a00100c24145442e500b0030b00260f208550081c11188504e000c03590386a254042d102e565000c0e80f000200d0188201484090320b008a0740401050040c040d84000502e00703510152141c103e4420260806141000c60405051a400c010b80c015100004030b001000903c46440066004480710400a04002940010181c0224020300b01d00c10a02c0c0100944007940c3c0c2c0c903103840c410718040c2c0002d1001a400141203035a10341001000e158400300c0e040307141c980002001d039100b500d4000c00b501000e52400055290500b0020340301100d42010040703561a14040a2040030715020b00550300708411003104401040301041141e0080001c0446 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 227149667 1250 227148417 227148431
    0x10614060714070b0711090f01061b050118141617010f060609180203070c03270b03091009050c0d23100c050a080a0506031603060507080912042106050406 68
    0x4006c00d155840c4035144100710420034040f039498255581340c103403201070504040c0b08042d01d900100c41c08442c54028103d600b0105c2d0180100f2507007000b400d902d8071036030484100000c140212074840035103503c1000c040802c00010070145185200c9690b1000790035000240082c00f19110b14150341e816003020010407403005040080c0c1ba40f0054420382c9280800702182141000710004010010b2400c01034100040e180c1d402110f45000241c0f5200001281c0b10038428580c1d500080e14160001c54401c2602d01a0405070030000b1060b02a41300260b5020024021450a80c5c007081090000440c0503102803030158412441c0044080845140d41088001022106020361901003a140402441c400b006002e22214141e00d4101500c0c90304a00000d80120300380d035409000ca850203e008002c9504d480701c0302c6001090080c903500c04c50140d2882d40e501c031944c0c2d44444071590f44110b0412034543d40c010400003084600104040e4070003044040c030b201c0d100b42d80b29845a8050344c2d42640d059501c66661f4035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 227150917 1250 227149667 227149673
    0xc0803060d0c0e070e0a0e0c09040e0f06090c030a0809090702030c2b09180c020f030d060e07180e0603240609150a090506040f15080f010614060714070b07 68
    0x40a0401610485442103100c0c284001001c47c5c1c40701600e801081c4001040e0b0035681c1d41e868112411181c601d03021a0400082c110105540d448150390280b00e501070322440c800d290401003032250009410030303036a61414410500303102250500600c5041140002e20003030100100501c04c1012141d200454003454404180c1d4400c0d003818601460018440020803c01030101c0030300d031840c14142c0d1702d440000d1800c2e49030001d0782000440b0280c83c8440c0030000f150714140c2c280d0b5002e1000c0d51240c11101c10b00782d42e0f407071003981e0003600c69100c1c00d20203115000400102111340807155001802400380ca140001c0300c3e01a27052400001031002090540d4030810185050a40209510010501007100b018075081c0202c2c81c506898054030044903151000a405902c0e960408880705102620411100300990400c80b0b0105242c010f10015000f180c00e00c282c0c28005004090941d0307040c83c0d0f4034103224030304070421046030700c0024121072000180300c8000e28168248081c8004241e06d035100703030750754031586 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 227152167 1250 227150917 227150927
    0x906060d181a0f01180b0603010603020d0506060c0606090a3b010605060f0c0c0618010206070f05090d1b090b0f011403070507031704110f04050402010c0803060d0c0e07 74
    0x9001038540c1502000070f481c1c404036850341194040c2000300e403403044000311200981058182e184d00030320004000120300780d040d0b0003011340c1100448108800d85941003000b40b00d110b0343c0c125402d10381c0401c001c100c0614090414a420240001d0001240e4900603001d82c201c00024014812038501686468000401031041200106080000300702c880c2c100400075010b80942810300111142c00b040d0040065001c22011010309401440075484403188142c06020405101d4014010300420004c41c041e14080c00750140004410f45440b0304141c107103001e1082851040c0001e898005181e202e030514049101c1b41d510242000080108040480310188141c0141440e6036038104010070705031410701c40c2c04800340d90b003040141c903045079900300300c1c00c0c2107510301c40000426064400b6601030008020042d206520451402d5802411449802041200b11402140c003e030206031101e00d0320000500b00302c021a440b0703030b0040406202044640340c0308000c9409421100103043c1c0c980600c80066000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 227153417 1250 227152167 227152193
    0x91109010806040309060302130f032108040f0206030604020f120f28050601110f160605071203050603100614090f040c06030f0f0504030f1d0a03020906060d18 70
    0x20350024525410f0955004040b03420911a0a040613404182040040f141c0403003070000f001c100302c41044031501e074240203948800d10040301c0d41110f12400d1201c0300074082c0ca909841207421200740c254141c9039800703020240d03000400c0294001e900b0804060b8044e48031000d003160000c40021204603142c80c09100c060001c001c1c00e0602c40a083e03400c0144051011085180114402c07140032440d9111003005070340d070042010107621036010308030301580340d0000015801d0034820414007105601c0d64800007582d1621990002611608100d000604524025045241c02c40400f43c101c50020040554841c21104e0030f8000c0391070329103600d03082da0b200d01d813075102c503908412a0b48081078141000e0307442c921924803501c01d050901d40c4039421000200c1d6a644010800100e8040601c01494036207030041c00d4480c25090600481e01000e800c202c481040d08522419030b0000d040855860300b103408010103854000c00301640300d601040942d001c04140c0c0034420145254103101c1d12035190038a07200f40341030a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 227154667 1250 227153417 227153429
    0x1407050307080a08160b0c03150f0d02011d13090317061f021518060a090c0b0f070804030c082401060c05011401060905010906020105040506010e13050109110901 71
    0x110000a000c000404210803d20503407140c2d8a0313948110030f0381124a1700c0c10b4540f000c0d0808030000c0400182070100d800840c030070203842d40002e0140712a54208929180c10000c0c00d500460b60400110055010f80080001101025034807282c542c0e10000051200000c03a41c840026a2982101e00815070400f404400c0184000c00070080e038900b10740411921a0703d446080880034040410700030050007030200c01100880d4142c031036801d2911212000002c050030300902402c1c400c510014035000c48501c105881c00e42e010440140c44c5242c01104080c541001060781400041048002c00042c001c10090004520810028001500d046400e500f026036019400740201c40762803020040d1101581e04d01c1c15100d19007042150101c85081150040082c240c810510fa9441e00001c1880e980103405441200c4d0241d80c0c42420382d4030703214100c2c20789600381d50091030340c0d00900041c8042158400c1d0300c3c3e400041d200e8003010f4040c1c00d888107825100c5088080e150365050354500303621401e020742803a014041d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 227155917 1250 227154667 227154673
    0x20100f0f0f06180c090b0a05090a050f1e0a05040612020a0501140d020703030f02070c151d0d020114030708100b2704020d090506011e050a060f170414070503 69
    0xc50f0488180100d40e40c0d50b0701c503034215552480311205502581c800c0002d030059032502e80d211000711601804651050744498400d150740c0303900040a00e0400600030001c0d101501c03c01c0860108828005195041d084082e800701c0c0c40b21000c60a40c527184104802407c00d0110030005507010f0061140590a503000203041081000c020704600b03a1020450b08007141e64900140e5501e01c42c1001c400400520014071001c5000250002c1031050720114041030f51441e030440c00c4000c030b00100548900b04400310b01d200c011105070b040f08207407400903401404640103040c030589050020103c0700341039104482c0000800e03a400c00740000c40d1038280c4000098840005c5103843c0160801400f0b0552240d0840c071103500c0010007034007005840d183c0545d0031221130000c0c1841a4461440d0154640c5402d0140d60400300710300310b083e108910a10040b10454101a107e04261810440d00b01c0b40c1c1481441510280318050542e0b0030307101c02580c11103100350702030b044044402c0c5601140074100580c41d44018400c0c0c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 227157167 1250 227155917 227155919
    0x20109030207030b040204110f03100b1801110c0a0314060108070f121b0902120f04020d0f08070c0b0c0f0601080309040b13050106030b1003060620100f0f0f06 70
    0x207400250b44000d483d006280b0100310740d12440010080d00850008420f13031031000c0740b568206119080914054400c000e098a5501d445015501090107a0412407186811050395080c1c254000c5040c040000d21038000d903280c0c440014045041c0c0d00040d07000311201c14005da12002c00c06000d2142ca40580381032805098049d15001b01d82c0d43e412061701a00c0f984404c1c005642040080960a041500c03280c0396004170159500d4540b18003c1d003015444150241d1800c2c00601c55510341c020003032049500a01d003031401145074440004100740c02c80111600001042513101141d59401030760b0003081004045d82d5038034810031105003004002c2241205030350000c40180050341d4007105842d1b444005032000255820f5810000380314810143d10761118a20307020010035405c1d41a04810300824040e0b41c6004d00c0079005508038211690b0f44902400200b8400c41d4000400c9000f18111a090a03c0f040f11104078123481010200c98000b40401ca0039540e907200d16103048014010880e480d050450100805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 227158273 1106 227157167 227157173
    0x7170a0905011a010314010305210c0a11010f08070e191806090b060a080601080403030e011803030c1103040b090105040b03130605010b0306130903110f1c020109 71
    0x80c1446e1110a800307000544060480c5e501200a00080c810311034000840b03004d1180c03000740d00c00c041000048043d8200014101c03240140b140000c00258000050700c1f003600c6031211018841d20301c0401c0060381d0010300540801e9001c2e0786d035000c820707981d0301004062101604030381c0716003014291905809019501007030981c1c61980c3c04000781c840c94410048240581c194540c00941d410f0700082e069481210a503402034401d0801103a180300306d22080d1f09460641d0070751244016100e1907802455854001c0c0312194196040c900045100d031000a5224401c0f4000c0c0d01c00000c0001388000300364402c10440303006180c2080059164107084000b005180c445043c2501c4881c104400031903021043c000b240c0c0100350080caa4004084134610380006002e038010700350700340903001c0d40c0500849410b00c1142404c80e420f8025210065450300c843c040c015407581da05045a00d445000000 = true := by decide +kernel

theorem cover : BRFrame.Cov 226978417 227158273 := by
  have h0 := BRFrame.cov_init 226978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 226978417 ≤ n) (h2 : n < 227158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
