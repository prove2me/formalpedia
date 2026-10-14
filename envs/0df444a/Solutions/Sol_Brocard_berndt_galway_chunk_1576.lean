-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1576
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:48:17.180819+00:00
-- url     : https://prove2.me/submissions/df7d23e6-9a30-4b62-9fe2-dfd5ca3a7bae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 283273381 ≤ n < 283453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 283274631 1250 283273381 283273391
    0x409021207020f06011802070807061e0204051f0311191d0315060307080708010518060705040314010b0405010902090102100203070c0609020f030a0f0b060609130e0109061a0102060a 80
    0x36141548400040c040e1b01d0316003c100f0a40c1c0b100b81c802da0100c4000c10350080c21280e40e91001d05106c001401c4e40c803c8540d89105101c042904079240d4001c2c0c0e410781d003004080703041d000d41200b540015503038082c44810034183c507500e22050040c255005001020302c030b01800341444c44640b80060141c4100340c07d003545c0400718440503d0b42e46000411003001105081c4060485d107802e4000380c5402140d40c041940c1c0d2043c004003150fa08012b401860090440d04030b9080e5601400315881d48a240403100310001030010712041020072000e1884c110100c8102000150241036400401d040d03070f009070403000c140b40d000514100346581c1000071003424048154110301b9403c0c800b0009000d0b08142a01802060f1541030145c1550345030810f80e003404d80010300301d6a504159250541d02d070301c4010030980c1c1d81c50340e5600041042c20204215460186c00420b290003003031801000c2d400400c000d1160009540d40c945050300000c00300d1040c80c05002d4140e10001d00048407100091401d00028001000c4a04103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 283275881 1250 283274631 283274653
    0x240409080d09020406030c0605090a0e01060203030402060d152705010503032b24060311090103090f020a0303020616020c03101e050a02090414071d0312040902120702 73
    0x300064452100300030401188020260000401800d00d6030005420352403118400601e454005006002c20481940e2420405a88810070386028100b48100320168104200040062074101e001300b056442d070000c00600b83c000c3c1c8001002d41480c58110038000c8021041005520082180400030018046014400343d8142004251a4010100410794540200503000d200b0038150000c2e0341400342c2070380c2c2008050001c4d0b08100f0300d42040c40048100002c1e0810104085210380219a6601140502e00386800c251800450092501d44415101c1305207100d4420010fa07515902d900040d4001c0d40105400e040c40b81c01d050391068443d560b41c06550041c110511251000315840c4105680110001114561044040c0c240c8c044000c0b10f0145510304030400400a2250307000d4103a114094804200004d000c00300501da01d44140d07681008510442c803c080c0750b00f414100001440006010707181c8045242c03890f8a016001500100142d90300031449404040503880e07800c1c1c0c000200d00c0140031407030007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 283277131 1250 283275881 283275893
    0xe2107030e010f1101050a0603110312040605090a1203020606010201050108070f03060218101e0e011b210203070b0c0702010c1101030603080c0a0201020706140409021c05240409 78
    0x8145071150602070b030b0140c0000f605001c1e007181c40240c602c101c0244501c0c034068011600070001800219080f01d4058080d003818200013502030141d4844072203840c941410704905840e107401001466030b01503c1c4150100341e811001441c51a04c0388250003c01090a08200190130358105802c42c81807640041c604212800c0ca1140c00811a6040a00180d4036103110191800e4100d03801170040c3c200c07843d051611030a40d84403280c07408002940c1c0340c00c9440802c400040303411400f660211400120080b1989aa40403150f0004c01312601c43d40c103c40d0000c400c1000c101d01e0230b0a2422507009a0400720b015820f01c031440b030034242d1001c118441c452400c0155400a411010392003070241202d075000701d000034681d0090303000c4000b03035411150842e1910a0b0f001120f03940da400d14400c0340180a803c00c000781c200d0092050100004040c4140f6013054106840071000b500301d098203481070130810121005040881c401c071030180d00c524a091107440390030400d8181f0703000380d01440c9002c4e0346048072820104403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 283278381 1250 283277131 283277147
    0x90906070e01110705090106020d0f0219031110181b0e0c03040c180c122007020f0603041a011505030a050c1908010f080708030405060307120e210703 66
    0x5003400d03e4005042d103072000340d2500c03966800040d044011a4000b0455540003e003111000304143c0d10001040d007050000c9807200c00180410b00108600c0141c000043c1c0107030242c8840001100c11200102540005002035540c804e500894465110712940c050088815542c10303c0004441c003072030302e24600030b4044500c5c10000e005105050340030000c00d040140141c4a031000f0040608030181082206094030001d001c09410078000c1190781d000700754617030524010280b0b042400e0601181c1c04a5004011101e50b1006008a03481140c240701c484690b40c1e0b803806103003d00d005004200451082ea000f2040009060300048480340e8844001d48200390b129044aa100303408840120343c503242e801d070134100c80c01801c0900d6180c0c2021816094102c0c0d01c8081c0300e0403107280710083e0503840c1d42c410181d070b121040c50003100040d40040005001c0b5052a100454105a0300d25100914460009483c2c1c200c46016181600c5074000d035040131a50130440c10440c40b40100b1406840c43d0460303aa03000381000e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 283279631 1250 283278381 283278407
    0x61416030527030708071a06090402090f09011103040c06030c0203070b010b07031115040512040812130f080c10090506030f040312240b120c0706092009090607 70
    0x311607002c40d10890b41c040c402d50300e00c6030707110384095210a214178100128852074581e41011100e0701d80014042d1400d540c1c03050180e0340162003400c00d62509114103d080c03c000307040c23403699903c461f064100101c3d5100214070542c02000b5031546141030034801019a41904507806c21948180f11940204481c813001e40c0c1104c80301c0440f030f45d80c0d80883c40d050783ca10201d503030400d0341d43c010f44000c0c80c040707880203592600c9244580c054410b91498484100000d020310700034a03005500c907102d01d14954090300002c18241080880100e0540c2d501c01c1da1146010094004000079002a00800011f0400030303811895000142804058242014081000307400010a820458014040800c0502d80135003c45a001424040d050281ea03151903890000001c0103941d1349555082050000380100401064426000c040700b45c6920355107c2ea0004085500103900607501c083e960180c1c600091100803a800f2410000343c50311003145812002c20030000c600415001c03454210104001c001c80e40859043e28207 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 283280881 1250 283279631 283279681
    0x906051509010e0616051e0d0507170309070906080a030c021c140307020a091a10050433020a02030c060d06030b01120b0702030909040206030703090614160305 70
    0xc0001400403240710340648002030308803000003030301c00c8228191007100b10345c02d0282e811140c410768100007114020810541221054004030071044c00644154014500360703018101d4a0300c0a100000c00300d44682c402d41307001001da03220201c10054199940200340003041d80002a102065090318090b0401c40c40980003440741900c5c1408240c1074a20382501c800d1141c21543c82c0030742281c070426031690780d4800e44081c1d200351141c5000052000b4940240b541d045490201c40034040400414400c021031007103c0c20301030141c00e00011428100b03090800e80701c818619640c1d100e0440c410b4001c143c140d000c0c4205003c541011101c0030141e00d002031030b0f4090b04410b40d22030340e42d804410008002050140c10003000344c060080001080da419140c0b0007801ca005100d501203035213a140040c0ea50313102e0815031a4000004c400041c1c09490320b038010790340c00041c508011070000304079642c1c50125103400000b03910442c4004240006070001d03000b00720309032000d07040030003560410580301440400211144140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 283282131 1250 283280881 283280887
    0x305030703080c1210171b1909020c07090b0105091e01020c04150302041107050a030807030f05090f070911030a02030606070f060506090a090b04030c0503040807030b060a09060515 79
    0x30403848002c58004810a8421303001c44d081841d40841d070341e0710328440c5060095151030b20140d515008074048801d0203965000354010125041032004403a05500042070100c02e8000c00070f9000f805000824440c0e82141c0502111420f081d001d004a456500300241000400d020112554a420382a500d0940751400215882c1c8001c0c00103c1c500200954001d402c01e082c04040b4582621244083c0f003031344d201b11002c3c800128101c484c03441900512401030701c10390010b5000400f01340640c522a13080607451030b0110314040351061010a4903c00e4a01080c5a48800c4805060070024082400a8041c4901c144904043c40403158400e00021b00080c0710560b0000128410755200e604842505601c0701c000d28407090b09050080040004468150007000d4060000e03160706054802d118000368041105045500c03285c034110b4124062200464462108110203d144401004983d000390b12807100c206862400e101030140f5150b05901c0002c00300d06040c5d0a100d03035a9102d0140381c003e024200c000780c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 283283381 1250 283282131 283282141
    0x303020a0b0901110f03160f0909020f041211090105010806060405330a02010608152d0a0905011103040b0105060a0c06020a0e0429011101020403050625020601030503070308 76
    0x8010311502c01343c8503680100061200d11400700001070b41c401c4420101c01e50168a03d4036080c3c0f0184c960010705000100c15030402c5c4a40d221590190110b4060340064500300f0740c1300d44495100d200740020607141129031000003e007070318242d208140585000c0ca000400c034204040841d9160290b80641c030311800035041c0040d40c000d526016800040321640840c07004690701400c0341d00c25031000325200d00550900c0008184100c00041c508106003280601010554500310312858040c501800341ca0326095805207800810709840240707024043d201c02c00a450506498441d0865203070701e40c4c410654400384104404110701080780f6044030401e444c10781d0356000c00c3c042118188000040240030510200ba04206103500003c6061420000d44003049a6510030f01c180b03142d1000c8261142e41096070344801036095110300703480c08480362031400240c00c15849989007414440112054140303214003242640c40940c0081c2d4001d603541241c0080d15040d410368031016201e104003500501841300103008a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 283284631 1250 283283381 283283383
    0x3010b150423090c030412050705101a031605030d0e0d060e0a080408070509090102070c0b0a021011070b100b0a03051905180f0c01080103060f1811030105010f0303020a0b09 76
    0x1c100c044003d03c0d0380c109181c04540c40e04981c00585066404d41001c0204080c010700440840d0b045c00c0d00880201018030f427517a041c0d00070380003060504590405050303e4540350f407400c116451642d04280d0304d00340010301b44424035180c462058000301c100300901d030b02e40000383c03142106680e80603003100e0b01207800171740701c0f11280c80c103010908018645900020002812107000c0b62036030a80302c048030b51003441e03212101c005080c0d0150341800741c1095010401001251071800003401c481d102401555034400902c903103107040b1031900c1d0130350045080010b0b182d010001940c030499484208408003c11880c1010000d030014026500d04000303142d541d0000c60210449284640202a29440113101d10300c1d10408014000c1c0c500c1981c00014032407101c188200581c0801c6881c22140c040e50340c540d9983c83c40e2030302c0c0701805211106c02080740da641b80010144000a0101c082c0d1030041d142114503040260606007191416401040404519002403001076404100c03020a40d4014040b400c0da503d94100c07a07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 283285881 1250 283284631 283284689
    0xf0d020c031e04080705060918060102070812031906030804270608030c060907051810090e0708070602030301030209010b0306030c030d0f02150c0a080718060306030203010b1504 78
    0x108940621080240c0a9050300c00144161355005080d43d44080c0d407003040c000c2070b000703061100d0343c81200d21410700c50700c5004000903580b0000510480700c102d030f81c0d0884035050141034440c2a00c0050f00008001800e140300da04031044103041c00c801c0103e0fa26645401e5072500540c040c0d2613042919240d010400d508008500300d181820820800c07502d5a0baa030a00d50302da1007502c1c0403a030b034003c2c880007039060200411080122030014159a172540e00306035a4003c14600101031128110154101040c480402c3c03080b42c0c4c92020380402050f00c982000c070700d13a10301600d5601580445d80308100500060700da20a0f080d0440d8086069540ca9880741e0001a0134480300c481a03e401d4807455141c450440e81c06024099070f01642c1c2c017520b900b900f1005544810310811074000c01c601c0c10030010110040c0c03180c410715902100034504800d407508101200601825168040e10000e03898490600a501c0c084c415000d2000044030304a40c0202884005906401244151842a0b0180d90920b070045554030f15 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 283287131 1250 283285881 283285897
    0x1509090103082227110a0f020f070909140f0309010f0302071205040f09021305010503040f0506041b09021603051c05040f060c08010305030306060306040b03060703050106140f0d020c03 81
    0x20310b80c00503880707500184102c555409505101104074504240c011924070400d02000d610f101d1440c61b0190140d020f403841c6921186410441c4161950f2820b00c03001804508040c080d525400b1560b81282d0030300c55032910445445407003d8102c07484c0c090768404004105c0b080d0762028200758410003981e11087d4024014008080e105e80403c05004800c20340c094002d0064494040498a4603515948110124000c80400c8090b000207100107120541c041c3c0080d580c440c1c440c10701496600401c0d50f55600700441910b088403e41442c401d002451119441c02034050040c0c20421420080c00013154000d020010308044d09204c0c1c001a611400c0c40d48545002c0c040341a080244400d0615281480b01000f842c1e005542c4a407609a40200c02c902c15018581240e03040300080d419500c80000f00b281580c00a85181d52283d5109440c114944081c800c480c8503440f80d4500259035850103401500c0d04017000c184c3c0030340400401840c5403002d00302c402c1d02d8030300c0300072040140c58040b044240d515501c50304030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 283288381 1250 283287131 283287187
    0x6030c1709010509060a02070c0b3a0c0c050c0f12010e0307020406080601060c1403120a0911090601090b0c25080c0919181709150909010308 62
    0x2086180607054000d140501c0d003540842d201c40d9205a162030480c021900d00071701240b40b46500b0886200c00b0300c0a00b1041122040038400c84140c40346038074031010111035140304601904a9458400140d0ac12801c4580c9603081c0a00c8101705560b40c60340b90707000402010300c50ba6695004558988848440c41c804800c0c100003080707040420302e419580c9030060003049200340e0030a0301c0803c60b034102040385412120b070794980710740b40902503550505181103403046c080940700c103024208112541e59441c0d400780c442c110000078418098184503011801c1f0301010340c024030840c4140120359a104d015681140c100300031242c0c41c1c030083c04100f4140342c65450502c01c1d000d0001d1b80036400040000e050b8040300e1035031003198540d00c882001d115900904031159004c000d0b03111840c1c204c11225400031243c18a000d0200300b01400c690b0b4071000d80d82060580c01741d0019011070750749030b98102034050410004a2005241c10954108002214001d05000c0141288408a0103c503a00b03040d001c507080300f10301c0417 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 283289631 1250 283288381 283288427
    0x18190906020307230705030301060c051005040b06040b0907020c1306091b080a0b0d0311010906060605030a0e0304080a060e070b0d02122410170405030c01111306030c 73
    0x1c0000344582d00528221800d8040c80d520744c440091444121030402e0f40c0070380990b003503a181400554a83c9807051050701d050154041e0312052071118850170b07100398850381d00d07061682401030500080f1000b401c8100e01404468083c8003171940c001480b10b480d180c04136080010350406d4502d16024000581c400e485250a0420b5522078409007020034a10010943e50040307507503101800001500c02c61002103402580c011089404240b184c0e094100b0710070341c40b00100700c00415a03601d808540c2d80da4010000110301105202071400a40213885551401100660804d810b004180381ca540103a0002072005540d503248480341c06041c8506401864145542500d820384a4503d8020398060f400801000408000080d40d1400c45041a00e600c201d0030480d8a1443c01d2400348081040250703030304805c0c0103c10510504100d200e5425610544c4150301071a218211031424a00b560384403d4000302111052080ea900010030240c07074000c607041c91402007006041d034407084d40e034402c44454011040e6961 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 283290881 1250 283289631 283289641
    0x1b01050c0307030506091302010c081920070305070506091f050c0601050411090103050912040807051305010b0f07110d0303021201061103070308100f031b05181909060203 75
    0x103010303600c0341d10b00da1014426592200200b12040504030f070304071741400c2050911070145d4840c808002c0440d02c1a6507083c070b0300114031a0304e00249410701944000540041c00045040ca08422001030780000c10001c0c4191425640c90940301c54040c01028001c0f000800c40c0c40e100e5840b070885d618030500502c0c01801d441540c01000b051580b01100301c007094403901d8000199400c0a1107102d03800104203d0190410407084011000f510f070191a0445912442100099144080c8002c0c402002c5040c014150180b40c6402c1c4501300c50500000da00c800d28050042001c860400304441080d401c4c005c185070348041c1441c14011400c2505501d0360085120b49a110415070594001e1500704500d00746600310340e80e900412a008600803c80260b680c02c10b002810009003d0000e00741c00c0794160388040f1050341c568520108440b100d03401964110995042c12602600424400000c1c001c1a50007401e514600700006e030310302c070029240340c2c04004809100e080d040f00e113500070344030583c1c001c00555030303402c01c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 283292131 1250 283290881 283290901
    0x7050d0804030b10150305040203070e0106020a03031a0913032615090118020d0e030316080903091e031f02030114030c0a05010f091703030106030605040e0a06021b0105 74
    0x41800300b1144070303030a1004280e9040034050303030008030385c04040d280c01210070703924048014110182089815204030000420111484140d65003e044c0a03030082080c072600d418010300750f44c009040c10a604184510711030720b80d12666591503100c01202c02c60025004a45811a190020070440d8120305a40121b041400c000c0c5c0c030302690046c0e8002000c5203000a500c401c00028500a109000214280c02c084501c507100e40d030040d08805100300740c0040d01030102c0104c0390440d40201c401005584005001d2039049400c00c4000f074215841200442c2023090890200311131100245034400c4c14213066030000440c0c2d60401180300c600c000038010700100300460f1030160294100703020b0400c82e2070100c81e41c210242400034403154087d030000c05c542d207900d18100c010340360f0703007014119442000071031500451032160101000480b0054500111f951350303d807001c02012504140c00c814410381c103141100700e03101c1000411102c0641c000310010395030300300c06aa4481c03807504490038414039420700d0104224880 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 283293381 1250 283292131 283292137
    0x2a0c10091706040201030c0f21021c02030610090303080601080c0c031306090b12041101020316080909062d0f03011e0c05190305130b1611070b041707050d08 69
    0x4070070b0700c041c0550005040151132440d1040c0300b841c005007100301500d91a03c0c00c4d441460100855640052401c14075240c44404100bc80c1c800c40c4490380c00000b4010281044109038804011500d050070f441821560000c021840c05006a8104200403022400384d80d140400c44a0780d900c804200e03035880c60400485800508240701e0070020404d1140e0005034205944204d41200c240c0e02c1201903650345503950a0783d00101020b180d0304510050103042c82c81a407542d400c4104c140a03010564a07090080100400c100c0300420160042d44404041c0601860340928184540c0018000100c82c610000104018800ca00c00c9198190708110385800ca41c520416004c0021040200900104400c1182541d0501c10030690412480489610824031071081e400250480e8410000b030380c01000f2503d410040c03a1080d500d83d00540c0e160114584125000070541030050390030f101400b401c5190448103001d5000d1031040c8101d0741c0c52080d40254900c0141702420107401c1c000c15494246481d420420a160 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 283294631 1250 283293381 283293383
    0xa02010216031110061514040936020105070209090a1b1703130506030a020706090b150102062a160503041a0906090f01030902030d02032a0c1009170604 67
    0x130003070003000c0070303d4400380c0180c40c151081100c0b00002440e058500b01c44100b0002c0302000301e800c080c000402d070740700da50040a40e80280001d40d241702031035961005040d410403000b5000107841d5030a490300141d07000302c182c40e8600d40403500384080d0313591241140d08040400d50300511241e454082c04032140e14440545042c0c5d20718409a10760018105281980d900c81c0c0143c2d030342d2001810b4810800c501c0c022008591211040501504000f01c603079520081c0c50000100301c40a070f840300304100c0e41c0810440d0607a00154244020a078a041c0320a00503000101180000c4122403502084240114010102d901c9101c3c3d00c090081e0340100b60801c640c03a40c005006101c080a05801e5034010006588251804604020091481c109140c02004203800841400b0741c14540c88410400c05a60144001c081004540d00655a00d40340c014071045101202c6507014500c0d1200100843d1a03840041c10440e11041520060048408a03a050f40d404038039601c0785546101c00c182e01a5013002c00b040780d030301039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 283295881 1250 283294631 283294633
    0x2030d021014040807080703050f03011415120a27050f0f1515010c06091113111204111905030c0a0305191110080105090f1306020a020102160311 64
    0x40014030302c02181a8094502a1040000b44110300c045682c240040803114802e050607460702800c0c403554030158000364881041521500725040082c102034a00362040300580800b640390205110203404150006414048400e0340c90b60140c0381d400c40719100d01e8040482600300442008245040d9507604034161b01030b105d038002c035009100100300024135100800600c1e48a015640d0303641c00a1030454a2407030031175040280388082d4a000c54843d1080358109030280c4004c111880c014814006029404010704002620341244079100b2082d01c000d551442140720100e80b44c0303485608180c20388204412409070b0101c0342e1b81d5403500c031103000c842c4002160b81c140d0a60301001e000d00f0400c0f90100e11440094260741011042d541449562800c503040b29210303c1622000028a1002c03806600706042140d0104801c01c00510580c07808401720341c2c2c00741404510103a94030302405440119240010014401d40e000b05403054018001c0d016668041c1d1564100e02c10b4440c2420014408903a4080b0400a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 283297131 1250 283295881 283295891
    0xa15110d060f0f030f030809070509040b040c050604080a08070c050406172109010c1703070e041802030a020d080904020708041508040314090303070b01090e100b03060f1302030d0210 80
    0x420034500d5403c0c120781d00621080c80e11640750701c0946640c4402450f842e8103008405010170240c1d51810020f00850081f100b024051825180070b0071060380315040188920710500c401c10048000160860318150300c54103c41d251010307840c00000030b80d4036030450395001d4100b00d0045070701c030f80c0b000100810144100c1240c802d01e400c0b01081c081041e4080f4083d807a0f01b0b040001c0705195001c1c84001c0c0480b8400c4000c1000b403035000411003c80c1d0030030382c2e103035000580f941e094040c03d2426005d40a02c2c80502418090402026800a40d5805510000078000c011076451503040c0302030b803c1922079071040039105541d1000301b807a164030507600c54050804038404400d0740e919285c1c4280000743c8503c1d03050711001310760024214244603d40010784c085501d0711042220600040000560a0003805861408104c00c40310050b15814004c80c05902c519003460070300d01e40140d50b400641160400c8c2d0b015000460361711034400c180d4204d9031440c03010350584655240401515800500701c002541c1441041107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 283298381 1250 283297131 283297139
    0x306200301030807140a02040c080702390d0f0f03080c030f04031b2111150604050a090f24090302060f070203160b0f0f0105030a15110d060f 62
    0x41180428000540050814480c04c000650203808080000c01981c0485050100681c001000d480110340031800040da16000e0160b143d4040107000541c59920715001c440750100c5620301040c00100210034942e00c20404904502d8070340c40200c20701c164006469590140321030401070810000300000324009544480010b2501d00b41105482c0205d0400803012200d40311600d003240c0f80f030419801c1070704840c01e1030b030b5400c0017456080900b82c002060245031005800601400f41c0210680c0b50502d031250000001408040038034500030358400001c80b00001c4680f68072440382c0040103140d9004003c4070020380b145082c4002d090b0f04180001401c2091078200c40c80e100c42800781d170304e20b84004000d41c6c0071202090060854129103a40401107204132401d001c44e61800c0c803c0c22480071415691828210240f060480c070000246a0211555008d44099454640030075507030a041c40740940080307032140c441030703c01e802500030f642c0050a0039080c46c0c550b008010454020894de04c500e0030301e0040060001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 283299631 1250 283298381 283298441
    0xe190f062c150402031b0301020405120a0c0b0c030313170c030d0501080d050d091110110f0604020d0f030903050d0930080304110414070215040c2d0306 67
    0x5120f40e90142c00b92101102c841c01d40c041100c90348032402e0f07055401744000701d130985961040c681100c1b0582c000b8042c02c00320382051641405980c101000c0c0c50700030045000e08440000c00c49400c0395103a02096001401070804407d003c031040511240038100040d20021140000050f100720030b15801e0800a41e66a20003031965a8644140800803400a11086d1907900c05caa0024401d01d0040b10400401b000701c400250318035221045d401d001c28400d07080c641140c1c9040059500b0032103100c00038000c0b82415000213a0711894404000c0c01c4a100002e10740800d44180013072001507501508985d82e040b1541d0010306842580c0c018852038050040030091400f0741d000040c038441c5217081c00c01c0300c80c5019482e4002e00750300007403081c1ea900b03006160000058441c2c2c1705400d480a0840404003076401e20f040000d0524414102880c810700b40d480500005c24081500c00003190310002c90407540600400b440828075001c0b141c0c42c44540e140da8000000d20200d500482d0812460320014090105401110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 283300881 1250 283299631 283299673
    0x7050309010510062309040c0221090901052b2d0b0610050c0a030906030f02090a270501031101080c040803030c2511040e190f062c 58
    0x10000140d441c0c1d4914200380504201710a05014038100b5030303d4031885001050540c0c40051003440142d00142c200114082201840291404103a07070032442c06010740009414000c060007920302c185900c0103040d0b48030000e90000c9101d02031007040c2e42d850000d2828201020a5031a001c070201c0e031466410000d500e20884050002281c0c80598041072392078030707014480104020052401803040411a00000c003504100300d042c020f01c03d0303441d111024140280141a40d2140c034101c00c440340180400900340d03903a2140136098070210041c50500c1006002058400c0c22682c001d8000a031030040007109002000c4841c0b00d001c41d088c0c98102c0d85440c1c1c07540160480c89644102d20180d00144080340910000c035000b0040c4110101c0c6002220400c2000c0d0b20000c03118507000c071000000e80e00e00d417080342014014200c030303a800600500b6199015482c641d40c4109005801020000100c02c4142000381591140c039043c03d581440f807480c8a42200329810503001405004031510809034519404e400003107503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 283302131 1250 283300881 283300889
    0x40311040c0e1c02100c021f050f120a060515030f0a060b1c0c050301060206072f0c13050c090904080403060c080a06151707031b17090a020a03120c02060307050309010510 75
    0x4552502c02c2314110469020001034084420054108600400381d600c90016140428000082d2103844c182032102500701c1e25103600c9180900c52030300300035102c1180d00003560350080702d0b80080200c41d076400f010b0750f00400f100d420807040b414011460003001829080440c00c2194079010401503e941c1c1e000540c2c0c0350109224810050b48023200040c500340c46542074040d4800305003800000c0c0041800c4c803020421189602e10070b140c0c458000c541082c50860900d44000a518208004c58280100d100019116203158170303004e80c500c100440c040002c0c9204803001142c22580400424807071560050001c401660360041d0b003401c0201c00b0400301c2300b030017001008c040c05c0d858103158440b561012503040038006203c03800b49540d681300340024035404242d00d00304402c00e43d11080c0d118041c009208801d680609851010750181036010700607200c041c009403d0301d4020141409910a8204c111112504e41e04c00941060010050011454115000c0c43c040e4401c0d100a121503651644d804c11b1203112482 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 283303381 1250 283302131 283302139
    0x4060e0105120a080d09030e040606051603020a1202031201080c030705040c03150605300a11070c060914090411060c0f1f05010b040311040c0e1c02100c02 68
    0x4010407081c81e00d400c4881d006404030040d90983c80460b103920a140c2c20a2194111450b115001c0e501059402030601c3c1c8904001c0750708101c1c180c10000014064028207001850328040481210306060003080305003d0a940f281c803014200c054a000252a40c001c40b00300c1451400410020441000200713010f000c105015005205581c03811f42007001801041c41e1000503da03444421000441c1075545802c06072055441700341d07640b69250b02202540e09030b040d515000d12a04220243c4020304140c40139008a0744200126482c8908600e55000384110040100442e0914000003462500071219104450384458680800c1321541c0500c140124110340050034050b4030f400640d03c51400b44040e0601003840c1044a55a0b00c080b9400d5107000034064291510810f40400100e103401c480c06440d01409940038050b00b454516501e0100b05817402524038822a191a004040b86104076003803202c02600400501c008003501800541c4808140e105074042c08c0009072000ca42d03401801210036107a0301030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 283304631 1250 283303381 283303409
    0x50f0a080a0f02060d090308041203140f0705190e100306350109050c0f0a05130c031b0e0102070801060f0b030c040915242c0415030c050406 62
    0x6582c400100342440800c036401001401142c980000e94403071580024402e0b1100a42424581801400351140b17515030030800d030800744c0224013000000c008581003805040703118640d4448000c01e690038041c10724288a0824110400f0030a1036001001802110040d00c9080d48120446000c405803440350240e01d01020340003c004c1803d87d0b90304a4207211201d20056020604030310f04c1c8c03803030a64080044c00d0340c0a031b100c0a403200b050b140004140a00c440211600c81e100c901d02404903180040142c07440c505180e845040504140c02500002c064440700b6460485001103580c1c040c1c048038924107014011300c1a41800320f0000414840c039419035515103480c40c519032404841150380c0c0e00041040310401024800084d8948440c05115800e0715040d0b460245e6509100482071515080b00ea046c981d6405c1c805444c400310f400c061031034100c000305017071040364890349011468195107040d03503240c005240c036038040031400d2405000b9003500c0c4140d06042a81d5a1401004151079150040071301d001124 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 283305881 1250 283304631 283304633
    0xb0702030a0e060c0f01020309010c200c0d21090303120b060d1508070e01030210080408030a050601021609060801110c07120203070b04030620070c0e06131104050f0a080a 75
    0x20b03001d010f004c0102070858004024520301142640c2040d03416050580d11560300d0f0500c181c1001e425040300c030303100c14a004c0754640e0414051f6590384841030503000c2c60b07001c2d600301c00740810344a07600740c940a000c520461445540d1001032041c051444150f000806000f41803081c90158060310110b243e000b4075841c18520030490f10300c003e10000200f16894115000d000603603920138000240100038489603600b83d58554014014054560104c101c1042903a00800001441d03130410340b90015041c100028440c0d940c00c00603468100700001c0640f03059000c5800240014a40d00040c06a40c10000203002e00c0440d4004202e29004540300d01a0a07002404144055000c5180b407031003960004049460b015134801021000d5401a0006e0310403d031200d20480d425120720984038007a00c00840898601001c5841c0c3d1152070b0101c2c041c488401640002050301940c50380402e48030302c130941c4e40400c100c0f80304400000d541d0f40b05218040c0140540d0105050394502451070104807059640508420005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 283307131 1250 283305881 283305889
    0x6110910080c0408070e10050303030103170906090301020d05091006050d0b25020c0a050612060907090801110409060609050112020a050f04030b06040515030a03030509011107030c0b0702030a0e 85
    0x41100b0103001c1c080c400001d04000800c403041c01000a0940302442e0304251800c00104103803900410f0081c0e02c100010000108400004e4090b1482d4426072611001c4c20f400160407840b0b42d040180d030540c008609489801c0c610360200b4007803454103003201d950040941e0450140c400034481d181d40016155560300c040b80814601c1d5912004000701007003086030084410807090500310700000107034000059030920307040070088040a401c0488515061000b1000c280043c06001401c480c05103421201080c0024000c01e22140504000c0d0000d2181d404520880001504107214100c000ca0030413a001512500548010003036860607076a40b0000040100c804002e98810801c0c01c040040070428018800b0600c005000034502c40c00c805040c0741022010001640c2002e04030076501e19102c514400340d95000100c81d0000e40c0c0c10f050108080c0d0f5103442850060820340040301d40c15000080e1072080650001c0105945407080d02020310030746511504982d24080c07810300b1000f081001e48299110310f0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 283308381 1250 283307131 283307147
    0x160507020603130f0803190612030c0f020a0b0711040b010f0f020f101d01060501050a0c030c02120d02070803070f02040506060c0706030c020f0c06090907141606110910 74
    0x1101514441c45800f50b0344054072a00a400c0544101d00302205101e0445a41220704a005074007450070301002c1d0504990540015045c1d00040c207001e043e407800c100304203076009000c42e4590001c0c0000c18080e911044c0c124103074071403d8101c90110090080041030304d02071050030269072041c4e480340780540c0c40390710907207004100c0c40044003517100c0c1d140300e8088000304000d02c1032555142034000c211828426802d580c0070300c3e80400044164106201402543d0b4000162045811b05140c940d00f02c20391404c00b56086601801c001e50011a1907600e00000d80f0006031460040c151a421200c5d196a0350145036101c3c040c0d1034008007851001d50240e009450941c01040d00010000c1c241894144021160f62508100e5408280440e4407982c10501c6250184400144c5040d440c02801a0304441c4000030180d03c150072103140300e00c0c0c0c0c060114040c1c504c1000e80202000d510cd100d16614000e036401500e5565200201f26245414507030001a252080005d541c0030364406808082c0000034030b4000c2c0d45401d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 283309631 1250 283308381 283308391
    0x8061005061b0105040f0c05040c0c020103111308071e0311130e0102070501150b040e190b0a090e060c07080d11220503100e0d2109050114160507020603 67
    0x1500e021000d00c2e00d01ca084c400c0b41e00580c0300f10a00085041249440c1843d840d82d648501d01c958a40200d03403801d950002c4c1c84042c169424640010800c10341c40c40514680a2854000315a401407400440c88a0700010110151540e0b41050451503610240c494210340b0107001c01000054500903580c5241806903c040e23060040c0140820000d2044a03503500b240c0080000b80e80c42c1c0c2d183c00004014508003c01c9a02400f03043c582280307003e050810400b82e03800c1c00b41c0440244900f04c411003410700c4040d030042e03001c024014040c028450780e4000a1025115a1541400c18024800425000c0c44064102c4869540c05a00142858001c43d0035100401e0480d000c5d21040c1c004100341d0b0704100307410041001e002250b074104078032181840203151800c224811624403407031030080408145400082c6903440c1a07164680b41e0b894200c2c214954024080620310700c403a00c0d042c41924420040190413003030743d9800010403005240c0e90000352404244400480300081001004400054240200219448 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 283310881 1250 283309631 283309657
    0xf090903020705090f0a1401050d02060d11070c03030f0507170d0906151a030c1b030403080a09060e04060506040504090c0302060403030306031428020409051005100806100506 77
    0x4255181c001c1009130000311540006071400200f003241c004654411880c0d111442d0004500b6507041c000070035030540c0c081c00c02030b00c1180086507002c030350142500821621881c00400e01d807111080d1400452040b0039000c120041240c0d84691607a1034490340644000725002070840c680b07000c9209406550303610401c07080004644500001d804102a4000d06400055084030310b400700d860141c0f04402000e8001e0701400800042081c04401c007043c405880b51510900441241103120701c6d1010700d148620b40c0f00030680780c0045020801c141d007045000080300c0850b21441803a4144c40204002c0b01c0c0306000f41a406007090000b40000d007031230f0b0302c44084d061248055030141034803500098041d130095802100001c1e1513640a008202464200c1b586401c650802008800c16042e68140840c0507103405488499082e14902c2c155695600000e10340d5030031400f90b4801c00d000101e41c6010744000c94031209280d400480c0001e40044c0004c400d44501c2111480220841c1424100511030b0310541001500c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 283312131 1250 283310881 283310893
    0x2030409020c031e0c010b04092006270a060c0b0c030a06050307080330060108041113200c0613020d02060409020d0b0402030c030a091b08030c0709060f09090302 71
    0x41220040300003001030440e460385a40f504c81c85c140c45825904003442050040382018908070000da0441c558120300b03080c0206a040e1458414080380441c007510b034030031001d01c200c0c4250018400a05002140c038800554002d080980c590301e09070b940c0907840000802040401e8001407020540001441e00103120707a0020500c1035441300028600b08031600110b085804c0001c455004078040740030300e500316405860b4402c0014102402145450f40100f0301c0f03044c01189400281080001c1009072100400101440783c040f08140300e02c1c00078195041b6211110f03801c45003441858801d0401d03120122a0200100420f90341c0120003820000302da682260031601c0e040d5500300581c2d40304090009880c1d0f0a07801a200e1405082d44000d030350b50850614051403040040c8407201c4502800c80e80e10480c4240041400c0c40a0b10380307060b0301c008904821070341c3d1003901c00c04207540801000900d028030b0240111040300b601c0d2543c08040380c3d8688141100030003442020130800041d40c001400d610b001e4016203a0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 283313381 1250 283312131 283312147
    0x140c21070207120515060301090503071203060302060d02031017101a040204031203050601170403052d04030201140306010f0f0915030e0d170c1c140f0f0702030409020c03 75
    0x10f1512050781c1115260010300700c0b1919000e04003551580448100c000780304a80071500d9243d12403207101c0025082c02c62a04890036401c0c00398011600640d4041c001070350b10444421810000d420540d07988420300114203000a00748080c401603440301a03000003402c81d9820701d25220f001400f2001070102c4800d1204d48071211982d541c400f4000450092040031004200700100404035900100b000f0b040c0400c2d241424003001210025035446035050811503502c20012030348044103161345010740f1901c0c82140c3c8840b038540e54000540b0480340700b80c13611602c854550300a241e503800101c401500140d9840c1111540718490011484400460f0900c00c1400e0f88072110450000b00640410020a07200d000701100d8110401070b06200c2461441c00540c11555601d410f4020311019000790526000810120700c41c0021061300c040d90001c12101b008032501607a80780740011000c582c40506103a1210000d000c40d4084801c1500c1b80506070701075441d042c10188018025005440200c5081c482440804 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 283314631 1250 283313381 283313399
    0xf010605030c1809150a06081e0702030c0d02030903010b04020c03070204180c0e011403030a0207090e03090916080f04030203030402100527101103090609041e140c21070207 76
    0x85d0042031070300818101520301e0b000b441841030311a03001c0020030000d44e0401c20b8000c4807415901c000c5c46500c40764103568841c84802c900e03500442c0f100b94070340e00508426000a9070004024850b200082c3c00901c00c3c44d039100100012030040b0780c40c01d51103030410000b581c01441d02d68400214049031841140442006844501c45040c00350814441d58884e0b00061002001540b134080c20944110000d524001910100035142d5990b44074480c075003521540c4404414405209035032041501805002d150318099002d180c03407801c3d0003540c50106d24500b01044100c0101c0050622454150b0000d5140d511590f0920520210046102040000074002c01c07420105000024010181403015469022162810849271407850b00c1110f0910040d02107901d07000d403001c401d64809003000c0740c28986030700300712004c18081c040c0001d41c0030b148805205440c881c0b003001d601801d455450f18083d485103036114040e41d099441000601e034142c16084400408401c04004900e521070180d00c151501680d9540c041 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 283315881 1250 283314631 283314649
    0x180903050910021501140310050712051012050114060409020d030828020a0e10020d0806040e030408030403060b0105070c051c080a390b0406111804050f010605030c18 73
    0x281051b641041714090b65141c104030144240840b0340c8100154205420050900362800d409070490586034400140172402c030015400007010748100079000c2c2d20345031601900034800085c0001031104502c0c0401c425007802d1240c0c4501030b03805001140e8020090f1001d4451800040103000f0300c0f2051116110390804084080710301c00c108032070140e1140212030028007440004229940074145030000450425030008a04d00c440d00340e402c110700700780c43d4074000c41c000c0c2c1001280c7e44180d210001e00001c2c00c404c000002e1040724018107040018280a400442d0303240316018000d4443d40c03540300c0c240035074901002901440744200400c80e8403030750907036580d001c0e0313400c840c1c0d0b00c60200b00c112541e094110140d22072400304005001c6410090034880c821555012601d41019082d0881c40e000201040015031185d55112100318500c0d0f154002600f500d0660045401174500070380c01c080c0450000403020520364180e41c45501c42c0c5056648289141643c0d811164581c0c8043d000d11400d0020b40c1c0703c00001d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 283317131 1250 283315881 283315889
    0x190605060703030204151106220b01030f02100503070503010b0307020a02030d050307031505060a030209010224013006021c090804080601080307120e0f120106180903050910021501 79
    0x20250300e491504c10f51150000a15001b0b00c00c1c0006070354101d08800006c50752a6100201c4c0f007480712040b100343c0140542c4044c06c440200004851030002c428007000050001401e03100700e481b00040c04014800b00c070180400e072601c2003c030b02c06000500c00b000c110000340d60700c0555031049903441402074000910300980c1c07504007008a0400014085500e40c50b000f410401c1c12038008030b1b0039052401e000300783d851148400c1c0c5400c1590126500400d60310038040301061110024a4800d00315121041e10380003d401c0c4281e8501a2103081907080384420f481c0d02026100d40c0341d182c9800c0300d138075484030300182d84503814641e560101d9410000e41d0310420b108401c102e6000d00c03c142c1d12181003807031891510790180c0000c0609d50040c0b01001c0000e582d00d20040e446109480d02406084001c0003040621030710300c01d82503001041820102c0401070540c0a41e0450321248056040c08400345130100444030b01030000b80000b002006120254103142140040c2090188100c984200d054064460384080a0300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 283318381 1250 283317131 283317137
    0x90312040f140114091c05070b06010c020d0605011509060f08040611040b07050c091308161a0403094104020c0a05060a06060801050d050708011a0108091203190605060703 75
    0x500c01c0c00c0c1e00c00c00c010340805d032400c0c030446c00f541c115103005029406680801091221500005030080e403040d2880c81130796501400014041195150500c080c000034021100e40c4c0c000c20f0807011075188500f8000d42158190303111407080c2c0c0104802101d4003030000b003003601e10b15240c00301e403407440000c04001c0000300f030341442c074a89a01152409900b011050352030b4510805984090055070031102c0d50103440c2581c800072031640d0705420740000e203290050040280c0010a501100c2c00014081c82485201e176100e84e079000c6070f0719120b2130b11001001104a07098410701504d9900d0441c8030101d85211041807100b20404800019040050240c0c1c1c803404413030019401c4416403200b00300c0f0030004c0c0c9820042c03c1100f448130904080008042c204140b00b070300e20a00c4043c1e103403414008188a20009840514006e01580030040780404a202da182040d0f03000900f4040080c15216004c40c000041c0320500c0400c0c0d246480c2d80441044010700c20740c0f0b40d011140e4492002840da40d6a800410205104c0d031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 283319631 1250 283318381 283318421
    0x2181002010e0606090106080c03150904080a03140108070501140915040501080109020a0c0611070f110316031a0414100911040506030d0302031302060f12090312040f1401 75
    0x803407003d00f442c0002e840c440c020300c10b280040c844c05400840325a44070840d480e01c42e45940d41c01150200d0000d01000981d0059144418041030040101c01003124000644040c44001b059006a0700400e1003485040c540740c0214500780329642c480c103407440108070381c81012420006102e0010f40303040300200714a641e10500060800841d44c02042150040109000440c284462100044c00040105400030b04080da101c0c0ea07500003050740800d40b410140c101c81400c2821180d4a046000114031200f8a1701c6071156100700c0c00d050443c0100e9a00b1340398030030745008280c0014000c1c40801c90000d8811142c02844588810780b800341046001036000000c40040340c04c0304c090600c902200d41c0c03a61045d01407410301d001c000d983c2e1400120f0f50315801e401d21307005235696620030542880c043c020400a5104100003a11101c041402000d0500c529015200c0740c071b59144d1000255491040d075080d802030001c1c0b03000090114507000b0041081e28051301e94419480e29142000d401c40310b4074540002075014030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 283320881 1250 283319631 283319651
    0x50c03070e030723011403070c05070504020408070b0d0e0615090106030b01050306090a02040f031b08010b1302030910021902060907060921020d032a0210030218100201 74
    0xc040840d001c060142c1c0a803115034107004a4640825510302c4000c184c10441e038504080303034820750120031815103242c0055100e06089100501104008001b61074921869901050900d0315208031000ca03401e540082c0102490100c071215640c000d1801c0103007203a5218040c4014480900016214a1030074a50070311240c0300100b0400c04210603000320b401c151910740b00251503600141100d42103481100e841046940300149403000c0c4c89a03230011664030800c8000001008514040c074001c0c0d003101e2140c958925264440242243d800b0800c207640100868421142507540364021900b2405e4401a0341c0580610394095069a120101194180f02640c1c49080020740c14071805420249650103400d5440c500320000301400035034014507a001100c01b80d03540b10302e0704920222045540c0035000e048030b40000c2c10007610b00c91fa56807901c1c101500340542c05014100034083c214106600901070241d106611070118007d412481c1704c1809046c1c00c1003480d80717580d00d45070f0783c0c07003905255030000c2840710b0030f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 283322131 1250 283320881 283320887
    0x30f0b1b07020f091005030f030a1425060b030a0309170c030c040c091d0405060705030606070327080c040b03120405150706020426030703020a030e040603020301050c0307 75
    0x503409225601401803000690300c1003494041074000301c1e01c038565034a031070754a14141d10300d50744855410b12460400d0f29030143e02202401c0500ca154541c52118020112024100d1054911924a6945040713110100320022900884c01d50701491000450310010000302c1e2409134401000e4010400c60002003010810540a0b241103200c0fa1000c3e00d00310b005003010955400052306076902c903548881d42d03406218810b01c131400003010701c081c2d40c28480c582920385803443d460544094405018450015005a011744200e90041c2c001500b16441d148003914100d03071060841000f4402420000c4030721405645013030b86940507200c400c000d8098410745030b003017204546481354294002d030011b42612a40c9001d90051301e04440e4285c1e030240240c01c1c00000d810403071103482c40040c8294408203020071005091405107204150f9043d400881c0c01900c01c580f42c0d00d01902d500140168003140f40f02d00020710074a5149015031025101160081c4c40b6400039094550803910300944450100410840e154 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 283323381 1250 283322131 283322161
    0x31e1002040b0403020a090c081b0c1c11070e01032009101404060302061804061a030907060c12120f090b04020a060311070803090c0603040302060411040608030d0b030106030f0b 78
    0x40d0300704007000415296040540400c000070009080c070b110010ad118031220b9a1001c6980842d100d034103a464000c2d80c40c0001d10782281c0680c58100107440c5d545427001070a00021084156001004c082095a2840da24034143c2079416800c1c44030043d070707108040c41584450800d603009a0344040c401282600b81031503681c80c0055154140c0c070950501004002681350303101118001504032000320142e50303100300442c002d03050701c0d4840d08161080e21034022500c2960805107000306200c10540304540da031824110f50445502c4000340c08008401c00c001a054062403150014094028021502c1100b8003190030480300c180a0541d107489980c001c110446ca00203445401808450804014600f000d140c00360550041c5040201000e41c0040424060782d03040100801d181c900605044c1e50f8685450003c1d145c0c00c09650440e07041d8003141c1030b00c0c610703c0d0130300071402a100614000c50401d02141c505601910751400001d03010755807800e0100c0411285041112200c0c02850185142e0038500411a0120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 283324631 1250 283323381 283323389
    0x509181204050607061112180708031206040f110a200f0a0803070315032f06031b070c060512070201090c0b0306040e010f0506011d031e1002040b0403020a 68
    0x600304100a010558031101610301c00c6400420000b0071a0f940003014200f4490200146078005192080140960342d100b40e04003150b807450203942a15035221545552401400c84410982e10243d001800c00d00301030b030000360b4540d092000401c0120b4010040043e41d4820306021002800b105900079a07080191440ca10380f000c00b06c018121160000d1840340c4411601c1c00040c1f0340900040801c00c10391103501300000524081203d03211182d540e140003507043c880c1000904440a94810701180f682000e404e00e4036450026092900d103a44d6446140354841c2c04074204065603401340407603008a800c09000303101a10150f02c1d03240d038801d0304c5d030110078814070020301110840e810030301d0000002e218a401d1404503040d43d514982c0342e03181d03400081e0281410380540b4030150b20700710700b00851480c82d81050b4000c5030b0a0704c1e1065032045008201d01c81d40b5401260503003561081c10300c02c0c0b590b4464840280282086400c0c3c0314031f84900a010000e0741c2c0b060303210028801d0040f03004c2c025481d154806100034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 283325881 1250 283324631 283324663
    0x70b04050f0d08010302090c03040302070b0d0c030e0102030f01031407030b04080d0b061606050a061d01030c060306080606060c010b0d050f0c04090b07030b03010b030307060522050a06020a0504050918 88
    0x650b24686c009a125800207001c2d0454440100208041600170010038020303103030140b05182ca54444c00c07c05001846003181d600300181c2000c046003010001842107030f0007207046640410b501d0b030a40d190348000e94031f050155800c5100304d0700e0001c0400d482d208201d0050344282050792780c42105581440507a2440b14190b4810f100030000c1e4111513820f080804801640120042507507510f00308180c00628241c0d1014500c1010b040850300004881c0c884141a2841280000c0103162103590032406c1307911b01d0058031a607601c108042600e51424601903c2c480301e0100000c52922408008911000004002100c02e40d02c10075100314014400e210814240c8030940d400c001c41181520f458140030000341601c002d165a980b0180520388080d0441075000c10003404883e522101480c11034024001114104448002c2c20b490b244641001c0b40b0200040e90000e005200d03082c240e4485000951001d42901b0138008204400546500c0d01070005100304c2502d07a02000800700030a64604000801140e0820 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 283327131 1250 283325881 283325897
    0x60f05010215040b0a1d010213140a0504020702190803070308060418021c060606020d02100903020a0305130f03060b03300903070807080d1701060207030305070503070b04050f0d 78
    0x400300202201c96003c0e400c2043d410713050319242810b5000b4490592070350310080851041d0010001c0540003020380d20702040140002c0381d41d0f41d070005080e5098000b880da210000200030859898260050a0b2150005200c100c5e96a10302d00c5030f80340b0414a82c02148260004141101803640181c200c5a118406550030301c000300b5101c080c02c42d442405003009100306106a42a003441641804074840a940090300700725558035144040c2da12403500c45840014030074120000598540e42c00b40030800c0368160014000c502095800b9038490304003c242010008118400003501c254034103660f801540107503400241c0c0e140e4403060604050520352441908545c200903041d174a080e91122607040ea0f0414640c6d9140e8017000300090600c20b4952041a085c0b0601d00f002c106803002203041c056401d000e4840302010f40c1c51103100ca01c0260244200c03809a040350702c0400103c1d000700001d2103090700c2041900c0c50202c180d40c954400445c159001c2c0e0741c0380d2101034801000c10082110400506690602c454 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 283328381 1250 283327131 283327153
    0x10c170606250203060901061a070224070510090b1302030c01030b061c1401050118060806060405031501030311010e250509011206060608061f050c070603060f050102 73
    0x51501c01c4031426884000344000445041494440c2c2020741ca50090543e40582001d00c43c0f07a028207a540550b00032110f002e005e40242a54000454081e164081c0c0a0030020081c1c2c80c060b02c0740d8010580700d5280b00c2c0300700b01070000101c060003440060210014005a0207400c2d08202680c0d0b007004103c2c0100d000d040344c0c5a0050303a000a080a007241c001d01e400302d02042c42c5030205007640100d200050400f141185000110403c80d00107601110782003101c50840e81c0d0b90f1004490214800c064001030312160501400020305c81c54490ba40600054803407890555100c0110b841c00e045000d0203540c1d10782c460f00508c201a40300d90401074000855009002c00040d0a0f20103071a5032a4940c00c0c0365040074044117130003555000000c0401404020700100e282c0d03035901c69602c0001118601160340e54603044001c61f50f1030141c141070b030144101a03c00d20703110000c000c00c004000c840d100f00034180207080c00354140d42d420802c41c10028010580d0046010341c80c0203090140c000c071036003089043d50416103000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 283329631 1250 283328381 283328389
    0x608160513050601030b120705150702010801060c0309030c15030507050a021b04110c0f01110414060304021503010902070303141b03131211060f0702030306060a0e060c010c1706 78
    0x480620030040e0010305501e4001c0141e000b800401c2d050794204448041f18100140003040c0c602c1110019903038812400e4504c4a110514421500e00034003140c00f203c010b02440d0320406000c82c4540c803074140181340f1501d87e1a4001c9402d290f502c92280c1c4030040d80c000710080d5140c01410742003861420900c0c00d10342c0b0250040c0d00d80c81c03031511180841c8200e0f181c0c00f84650746c0c0e4100c15164102014850398600b02840026100e21048180907215800c04240101d10030210003241c00301c90240d1750396041c124880b0100601944043c1c400c0e6032085014450201d0416044011030090060000060ba146074034500a01510304000c10119100201010442e9483e0b81030f40e5030200406e2100407603500d940742031188080107900c040150018a85003a204501074000030410b615004500032189142e89400c01390001c0345003140c0300c0006810910105d07100b0b06020015001c0c0303004070b0801004201035100415000c0c0c210300680c210302c4e912614118095500700580e0b1540c3c6c60510a405050b00d00799001c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 283330881 1250 283329631 283329649
    0xa050f030405030f183c01020c04021602030d11150a090b0907060908070b041e1503140603060405070302010e010e03010513021207060f0507061413060b01021504060b030703050a03020106081605 85
    0x2c503540501406e0141c1c016071080c040c0407003c80c3e0040003103444090003d0303140184011401d08030300034070400030024a0b0034050b0300c21104c88520344000b071000d011540744010001402a144004527515410b01300002103500b511a403007190400c005120091400c98020400c1d00c031540095001d4105100c14001280c408040310160388007403140030b10000442105181504496000501f5400c107035240f0511654140c0000380185000c0e039040c41c1d1921181c0415441c0e4a054400030281d40c421081000194001d28a040840b501414045134540c3d2520100f420f462080701c181c1e045903000e101c0d08007140b500046021500452600804410b0700f0700c034000d8400500c0c09405010f00c2800700e850b008210346c58011442600c500912030304241011140a4800110110210390380d9041401e0b241700c80d4800901045911550900040180c0b1281c03030307c2c0003d00000324001d400d4006c4510202c041602004082841c07403007030b400007440501c1c0c03017200360800500300003031044940e062204114541c1c03407001d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 283332131 1250 283330881 283330969
    0x110c0622150c200606010306090c1d06070831060806040b19060c0b1e01061b1a0403020c1e0607080d0504080c06100f0306050a0b0a08010b090c0a050f030405030f18 72
    0x10f000702d01c0701d0382f4006000b900418000400e0704a000646041060007440422010821030f40c0c1801c0303020403080c010009840501600d0005403508000603103910f000d8101240409015282040c9106002d54010800001d0340001003c12241c1c03941a0810080c540402d520541088240b10340d1300e0481d8005074003400c184030341300401100910340002013062480003080e003075201c0c106a134000c09103034400307034141d504a500760054000d0108c4903549003020010551554118082c0c41c4405400e54100042c68006c2e0308140e500000602101c1c1d44450399101e11400b8602640501740c4803110780415070b1030400f0082101d001c1c481c0041d020040086000001002c4c3d0340c0c40721001c03030301e40d49005481000b050704c0c0100c540d00c00d000501c000342920044d80643d020100030342d51508666640d142484c454481c200765280040d100704044144c034218000619080f41c0b08100360780c6000d900a402c00c00c40d4101c45004581c000d07510703e0703401ca01d103031007454000c18002c00715040661040003990303070f0038003170301402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 283333381 1250 283332131 283332167
    0x2e0b220f0302060427150509090105090c040c05040807080c0a090204050102190203010f060b040602100b0904080703020a12080604060e0403020604060f110c0622150c200606010306090c 81
    0x2185c2e84c01010f076410414070f180c861410003007416200c034420f10b4942c1d540b00e014041c0764030740040381c2803083c10f0252500c1201d802c0d0091241c003e215081c8001041c80e0381190b02000030620000c50024014012900148028401032115980082c20840000030513800324002d203204000c01c1040d6600800c401494243d007071095106030b14140040790241c0401d02d20110413070f00d800300100d130046120019009488855080311080070540701e10704111583d43c0c04d21b581c000c01050000740050b041034000d005441c4a0f206903850b005403a500e40f03502e04040c0c00124080340084d010010a4245403203450011b085411000c1058181038070065280c480140016005a0f1200c0f5280d5004800d600100c03c1540e40c26900c964586030724070483d0300d44d102a00d24002c0d0341a06030700301d903041a580741c0392071560350800c104008044070050305100609103405000300740f021090b524589080c03003000303480e0103841c0c50003e0b060030315241c80010304441182c0c0103188011b207048800ca00703541e44100c21000070082e240e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 283334631 1250 283333381 283333409
    0x1a1c0609020402120a060303030c02011503120201061a18062715071a100303050409090618030302070b0105030712060b06090d030504080c03062e0b220f03020604 71
    0x30000c1000fa100300700010316040b50840500210103890307401401228081e9408210203181d1340c208a098494200d45200b14405915061004c1070b4812a0f940c1900700a00001640d40d40d10196000140031a0200455261000c90200800318102c5140c2c000d42100321040380c030708055440c890607002c0380ae40517188201d4600304014483d4603a11100000007a07000c0c4056211800b03443e005c2c00c2c0d0220700000a41c0703141400701042c45449020700740300c140c0354952962400c04e4204400c01d0028210341034280c0e041900d4003a02c0000008c450560718406010ba0b074050f03170744d8015060400c020703032040e440070b40030750302c09001005021003903030503203032840d900400125035103443d00b000503060b00031104081c0e4001d604201c4501010b410000800444074600d00380c0da00e020078001010303281c41d404c5480f207501c0854140410355101345030b46104460201e80140425050700c500c40410181c000b24100040c0f20034804a15000080e130b005903c0007071000e003800445180c107660104007240514400c5050b050244 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 283335881 1250 283334631 283334633
    0x120106050c07081c090503030a20070e0f060108091b040209030304080706170705040305100e19030f1b0c05010810030f0602180910150908030c011a1c0609 68
    0x140031240040150b4001c8410b01039400d40180d290b90413150814004c02e01081000030281000300981d0920500350b114814030105a001c40d03040288402807801d401e00803840701090051516207074a00513030041c0061200c1d49009030005d0003c8401520359009907120100e000b02400d0064050803145409950140c0c07140040d0f0041303480c6000f81e40000416000720040840d4030b9038801c003c807240c244a10a030030f0841c2c40340401a030300b03413199000c0508243c1116249245080039500b240f20001d140c8070407220281c401102000d881d004001d4200c0c00102c1c00c0c001c0c40f0a9642c045149030151103e10046c0c11609e1041d40c0d45517400d0807910070a414003000c40005002c00010060410080d41c00807110242c40c0c096203460310013540301c2042582d07a5541050349002c981810041103110b200c04155205070b89060584014801140d211401c040054418020401d40f60910240a1961440d0300100d2966249150f8140c1100700d046124000d4969540da0100c0c82c1160f20316048080d04039100203001005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 283337131 1250 283335881 283335883
    0xa0b0c0307060f0f06060c0308010614070609031106090106120b0c0c0a0302010204090f0203070c0215040b0f091002030306101209020a030302030903150903312306120106050c 77
    0x650310703015103024500b9511001c0c541c41604216554207060004001464640d40180d90404d080500540003840000041c0301840c09100a0740108805001c1c060070225955120780c2510f0560000f00c00050320420131000802c410052180c00182c0307100280051418010f60110825448801a000390030741808500c40952a40441d0b100c22580005d442c0e075402c9501300079020390f1151056240003850303c900c29019002a1080d40d00503003c40c2d96100380115141c080100c82030064400c440920000c210008070882048002c00d0b0302905041019103802c0300701e04010400300503034648010340d0020000c00800c0d40d9a01e200f800d068255042008050000e00e405100408007590300030740000c8045e00c0802815000006404000380441c202c0d2900440c40348161800b001c16103003080160b100740100d902c2c00f44540040c4003029944000e00d5481d100c05080d4005d0b8400913400300d984820501c070b0038580340b1103203920820701050594410345008000325160702c2c421814412034042080c04940c907144440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 283338381 1250 283337131 283337137
    0x7062018040e06101a0a0f0e1206131103070521010b09010f030b16140a05070c0314101401030201030c020c10030c02071205030403030e1201110703080601020c0a0b0c03 74
    0x40010222140ba1401c4c440092181213940074460b841003416240303980482d0a4012581107000b0740c0d4410041c012400c40944190008200380c5601c1104103510070060700c02004014403074404a0203130301482c840340c14652030b113210882d01c0030700075000403206100c80d4641c050714070b403070107c4504d0719a0b001d40c4880b856401046c1c0c14019542c000c0c0b540c0000500000d424002c01d05807405101120001e0700e800032403405000b4140070040110300400300d1000140d0092010300340740b01c80d0f0b0411500e000c00c1565001500101a001110b0001d1020040004a2002c21016a80000b9642e08202c05450108100030384e40701448002c0c10107442e0301c407140c41c003442407100c0200701001070416105000c4406014000d4201d01c90034800501c0341c4040080c4c0344085100112030079800c50f014618113401c6881c22a040040030003401c0d0051048145143c2c04642403080d01d40300d5a04013070580d01c03404503140003041c001010b4141030440d448104c0c0075100b650785441903411600041d8100381c2c0e5003950b03c1c1d01e50440c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 283339631 1250 283338381 283338401
    0x603021503061824270c09030703050f01270b04060207050105090d0f020c01211d0106030308010b0408030315041b0309140616080601030f050702030706201804 70
    0x200c0128240700b4001c0f1200204c0440401d40302048919403140c2d800c1c0f20201c00c00284124007524890780b02840c102c0d401000035041100c0c05807640ca0b1805110100b450312078558805c031201d9000d0001031072030340028460a60035200301c403075050352140920720115525908001c040c0202b4400d070b01040401c91240d040302c41c90b603404002401146021804103407504859035110300440d82c01c054000009102080c0390b284018143c446911080d11214148407000c0004110342c1c00c00d5503080d010241d0050048a00c034a18004000401c540b403c51034010802c40703040c3d0107800b24010510003400a00c4003c02900d0f07018241e861441e51030100c080006020380b0360070b164400c0032203064012490182e0b1542000c2000d070b0149141150314000c28170310550f0342c41d013103890305198580c40b8900b00e0310902c070305403031034000b0700524003c1001900061000b0444000f501c0d110056071002914404220840c000c4030880a40b200f24924010082010940d81d03210f103412150310601a000038a0301076071141d10104000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 283340881 1250 283339631 283339669
    0x1401050409050a050426072d0803040611070c0335090901050904080702010f0c0501050c0301081b0114090402040e090606210c100309062a03060302150306 68
    0x242000d43e840301c014101030341c1c20303203411069105c404401940c0c2c0c0b124441d0001800683c82c90042961034407013001d80e9040c40540340c0d00c3c400d80c0d502e8809003c54603142240e4010b0f8549640e90800b85011412aa80040c2a00700d040c000e02c92007010442c800c0380c55040785d42051015100602e010900c100a131500d104d20401520103140d59940c100303000014060f000c40503902080e1903600e80e420440d0000741160010210181007041c080194401c041001c040e1600c1d04024242c540f01ea0703101800c2d5141118089010140072004001000d41008007000407030440e40300c4250400c0305400282510400744522203031150000d1020300340d813160b43c1150014003090356611f00e1814100e09140d16018183d800b2803049215034841401c00d4005403611600904080003080c201014105015103d5540a03203582496941c4e040e103404690036008000304001c050a14155000c1203031447d5000309940c68082d010503180c0081840180c45000030f90100c050794440c2e0035242ea407040001441003206008036001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 283342131 1250 283340881 283340891
    0x60b0a030e1e1b03030f04170708030316030b06070b07030515040906020304052109240a0806100c030206010b0912030703051206040212060d0302010e01060b0d0c05131401050409 78
    0x94407010520b41030032005001c1d95500c0c021581d080556038061b2200001d030401c400c1104110328140500200c1c0c401142d207094605140d40c50840c83c3c2980c1007160300c4030003500394003c0d264685a040c0b240f0030038020100c41c02418140c03503031641200505c0081401c0d09042d900c40129100c03141d40400c7c4a41da8200a01c248000c250071b18001010b034005507400c0703030a4401c5d440c3d07141b41f942c01122128011805006203906185440c400c20010342d142a240d0009000c045184104540e140e000505104d410360300da80c0441c1c180b040500682482c9036020f442002911a52400002c0c0d004c1780340d50444d03900b4000301e52500c10400009144a640f0180308440b44400150781e400c02d13810401030444201c4200501d030040d0389400c10705c0f00b41e20968801030b0509980c80700040c06440c0c0880c54103d10342c003a100002c0e0600311000c0c02c901315002500124600d10020400c2c039060303030701350285950890944c0741050030310140f400341d81581a2103000d80ba02a0924002c0c102c950391145058070001c148001041c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 283343381 1250 283342131 283342183
    0x402150403030314060a0b07060b06090a0306020a0906020c030d03270c0e060105040509060913050303010909151b050703031407031b020a110d0c03060905010b03060a060b0a030e 78
    0x4024100c1303104c41d0390840d401030006015460035098010440712030700045840d101003070b6158001001c0207801c480d03110740c00b0301440041e03031208141840a140b00c0c000050f5070306001c00001d009490560300580440d80081e00c812044d46003c1001c00ca012010304010032021000a8034185410a400c00c608010041d140440140715125107802e040f07503a405610503503034980348011185407045004840d0000d0228012925234203107444019030242d0306524104212049694107400c60b8801e2303008154143d240c644940c2402004c942d68139016120400030024101480320b0028a4515061039006010380421200141030182c0c0001c15401c044801400031850001c40181c000c0414822525507007004811034009940009840c010082d0004c10382001c41c0b2500040000007155120200d486601e90000080040c9650169010b00c84c490f5002041c00951102858a00712004020405050802404014032160802100c035081c2c06440c01140c040706a1002d20724000c190070b5044001002841488 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 283344631 1250 283343381 283343387
    0x2040c02012309030403030509011b03080a0b01171b070f0f03090801090c05090c0705030c0a1103070609140d12020f0709110d0e010603080d140c0a0c0209040215040303 74
    0x6050501500240d07202240201e540b1903010004031888181c82d8820041030010a010340c015017110501450b003407011411f10304c0b0700c0c91261810841100480c5000b03091000340503d41c060340e000c000c001e1030315071801f080400101540c60000b0340b070000b80c6400b0310f00000071034400200302d901b055040610080c041c640340c0742c81c000c40011148142c00242540c0f40101e110a41070080480b084d402001ea5215141800d040005e10b400150030f0710a05a0108000c10001c0c40a002400e51554880c0240c41e04403100e0815880b43c4290180140c441d4004000c18824560090081404e50310303094903054445107880f010411461601307401a00365030708a03090205003a40064040d81005c422000c0c1c894060f680d0b05028251006200f07004038100c8240b00d03006128006a00036903c600b0032000203e00d01d6a0b984506e145d41d4400c0c010a80740c07540f07900c46c074008007244c0210700380c000f1309c2d00131441d00c1c4c134441d01001000282d041c90024400c2e40c141d00400c05550b540401d4503c441050749905940b69582d107000b07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 283345881 1250 283344631 283344641
    0xb010306270c0824010210060f0503010b120703030305220f0213051003021201090b0c0c0f06100b030402040b040c0203250b011203031509090201020c030a03091202060702040c0201 79
    0x80c1e00d401d0a1148481c0114411aa481d0255207096101c881c940c0041c0003d050200c04012014114480c18100c5000c142282c010312000b4a4416021602541001c05050035281c080e40b031039008017a0325800d1711600ca0300049800c202e07600f519000446072100c50720003840c0481c2001d40c04a030308841c104041800a04c01548070130038401c441e0020107a038800000416182d044030500c900d8190444204094240440d11286880840f00002081102a0340d520382d4900152024201d40101151101000b92b04001122202c0e501d0320041c0858503014545042c030084501036410958404800301d4215112508012a010001401440702031035410000b580c0e608031050504070050066054901500e0781600701c000c258100000695036801c10240c0603062240980c110101a038400504150020000480025216144012070680320341e0000a24048500d50000e1003900181e42c1c10780081d8009080c4000c80301c12518041c043c0505000040e03507400780326030181d04241003c101d644500da041d406 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 283347131 1250 283345881 283345949
    0x1205160803070f090302090115170a140f0903180d050f010f0f0603021018030606060504030b070203030f27060c090a0609060c0312110a020d0206090c0102100b010306 73
    0x51034106410405040b10740c9013280c8006500301c18a1401441355403003006101d003000c00d843c203007441f03561a640e042d4007403180c0440d8407941040d03890017a030550fa880500070540100040c4440302043c01c103e140607489100710200d010351411001d44007801d5840d004015150141c0040c2904e50941a42140c0d50180421400c001d1110340b401d000b905200000b0310030f070010707640c01800180740748604a000780c48401040307a643c1c402710a00c4d2070000009903d4012040074082e17540d07400ba121460b51426036240c110141c21003041d500305004114100b45880e440b29030017110300c0d0340d4180c10013003804141086055010320345881d00800d4104002d0040841c000c02c00e0181c2510202c104a90352001207500e5403284c0140d030300054000001c6008644205c00400801c02801000a1401d07510300c0c60442680c130043ca40005031b0400101c1915182e010b110181d0310588080180c120300700c2e900c00003034880d00c84204104401d5aa407003440d2981e4480c3c2d00a01c05088c07220100001006440c40054440c4a0404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 283348381 1250 283347131 283347137
    0xf0106080c0d1707140d030902040c0305040f02010804021207091a01140d0b040b0a080f06010602120d020f0f22060c0c090203180105070908011107080304120516080307 74
    0xd40c03801c1c5402e00c600714009403500001e022a210380d055003401c009502ca0142505c2419598003820000c1005001d140500b02003501d00081100b801c0c41404291003081d1010300074185004c007000049000f03c202c21045d41e6092030062103030360315840000c004e1400020b0148043c0b24815010846800d503a101002020340b441d0076007403810466004650f407403035030700300740018003014003010002441640000442c000010004a80300000c4800f023010001594083c9202d6801409420f008000905c2218090720711031024140800d604020b441d00da200d412030102800b41d0000b21840f610290b02d00f500c05491400c00d05c181d8406e603600b2408210784584201440007030404d840091010f0140d0142c0a10a9000c101c1001c0d007450911807100941008020b1030003c404030311080802c410070301c00c140c0b14030442e45030124014206020b070b5003103820001c1d0619125908205140100d0b80f03000503290700a920203240300076055507180850381406030000c0c8124005200030464200032041c0003841c803c0f85541c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 283349631 1250 283348381 283348393
    0x70f0905030102040815042f210706050703090f141f09170c10030e0c03031204080a020703080307081501024b0706020631020f030f010608 61
    0x101802c03440b44d0303c196161a400007084115968002548030f40c01401441d42118074049030041004500c003500b01107410540080d403240052038150030311000000c0c85411161906403103c03100765590aa80103060070f1210126040b010148224481c101030314003d10110b10880c1d071800c0c1800f6685512414510402d04070b160b03002007e0322a12a40070740c07406542c0310000c0b1881e20600c05035281007003002180a008141c040303007071500c601c980702043c100320781d0f000141c43c5840c1d0000c6003019003281c1107911030342013046a440104a1440150381240e00324006940c1d9050181090313107030810b1603100030006c10010040251240d0416034161151107100810038131100170744012070700c40c003160078032582d0403d41c42130300300e41550f090140154002112003402c0f8030880200c02c40d2210851111103c21a600030141407203803d80c1032201d247c01c500c8240d50300d98800d1010030480d0f009505820708421405070800b500c0150740d00c5407070032802084c024099841d071801c0702000340e010b48a0350044620328864a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 283350881 1250 283349631 283349639
    0x30a021e0d1d0a080304020105120f0105031009032c0904050c0109090e031c020409020c01090606050108010513200c0a02010206060a120816020402120106081311010323070f09 77
    0x42c40c403004044960000340c2a9580203035503900b11600083d0085c0e0400105001c1c15a030300000120b43c50242048030861145585000d0405240003111000c40500509080b0488002500984800c04100c01200205600340e6160b0702265030701e42c18500c042e8400c80c0c0200f07020074032401082200c0350074400c1c0c0c5c0302c00580e81c4602c2c020090b100c501000742c04513071040103200070080d50348040d055564041c3c140036103000e50fa003075000181c0c2c200e007103000303000c2c0d64800c011410060240f01d000c000301030130709010703032603624004c0002c402070342400140007a1900c9207004941e00d002940c13415135035029110f04030307101c0024403262541c2d0f00510f6002c9003d0b00c40d80001c42d02070701d4454458411109040c990f11141d07900c03079807101050b41000f6207541d040500a41c449006a07201d0001d818a180c03481c0d2840403643c90305800400c2450007030f0507115402d01105409010070100100420700400138207000c206021055803580040d20f10310303076043c500e0080c0342c2070102e641e612004803504140380340c1c1e8103c2500d0f01c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 283352131 1250 283350881 283350911
    0x80a090e06010807050a120e03090a0807150c0c0510030b0405091b060a020a02030706110d09060f050c0307021e040614090f060d08070515131502030a021e0d 69
    0x1c1e01c407640031900c50800560224420401005080079034986402c1140b020020318003503406071a4801100e820114100480c1e0503c101608010b02c18000106425485c1034070140c080300b25080f80070304000081d1500d0701449070703200d1400c2c01403201400080000061030340c001c00400d11610014407031818040851b0418600194198001ca180e00c502541880c404041001c0ca80c804055401035020316110b81000d030741d0510480c001440a5102c00254500c4a202d013410070106080040170312159607414040c00380d1000643e00003403410f0403c2e581e034116044070395103180901400258401030900c20034034942024144840411403e540620036940c0718001c50004080d480705240c0c12902440c002000d031407905074100c2d00210054070300c51a41e4030540362042e443d84810015525039001013000141d01c0c01c5101441d50111a115070760041208075600d4104d407810f19034070221183d4001c0f0103d01040895811641d020010310400d000c0b07210321151400321070300407001119000e86400540307810501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 283353381 1250 283352131 283352159
    0x7020a052b08090c010e04090503040b07061d0319050405030a03030b0103050a140f0604060e10050901060509180601020f03120103110d1e170412050d030e0d0507021309080a09 77
    0x192810213000001044001140d0012113050020b1740681c03200a604040ba2080c070040c0050910002d00c03564905072420144165002c191200440031890b007100340c41e05001106444007501401c01c0400280305a0300c017242c4d280a01e030403035a8980200d942100405030941c0c40155201e1003a02c041c00745503103000815080722401c403168411a918140081d014485280714580d122000420006800f0b4880320070f011212022030300c07943d0440d0f04030010307c0280b07011100d1030300420451900d00e2401c004480410322018230060b0900000c0c4006c6c002c04c030740e82cac02840380030045c400c0e490803640c07075414141020b60716540030300c81942c0c55680031407071040504100174104c1c45950015110140c0c0c444280031000c511051315011380791000800d0743c10741c0c40010750008000a00000c400002c40340c40b00c1c1080350400300001142d80c241450001c0c03040c0e821001142502c0643c1c00d40c104561122450f00111708441000e902c80b034040307803416062008002241c00078003a05800c40ea2441c20607038a0b585041040b02c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 283354631 1250 283353381 283353391
    0x30c0d0305070f0c05070905010e10050a0303050f031b0c15010801050705120924060405070c0201080115110304080f1e0705040f1407050c0129010807020a052b08 71
    0x10120941a00d40a029804c540b4030640308a0481d4202e69903484064100d0f182038220307100c2d18403d5006c1c4459021484802c202401d021550015001d265540250a61080c0390343c51640071000b0000400e400314444503844a03101d00007800f0f585090904c040340e1180200210005800511b80000c240040144100d84c03140e01c850312181e02c0c201521141109186000b00300700720304e1054000d0301d1700e1200c24074558040203260300d6025605081440402040d1080104140100503074036240202507a400451141164110300c0c05050031411a9412500c043d980c030040d0b0903911002600280b800e400090055880b5100810f5480480004035025045881c146c509406584804418419440e041d4071010300c00c8201d4000007000129049000b0140d281205ca1002094021552401207542802015520003428400c9081142d001581c47ca403a244036404038108005000001c400b02d000300440000380340c0080c1280e9400c44041c04098600409045004003000e80c05d00c003089490141d02090301070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 283355881 1250 283354631 283354637
    0x306020d0f11161b1e0803120a0c05070f0503091c0305033103020f012007061802180103030f0903050309090408040f0603050109061a0a0e030102070b0108030c0d030507 74
    0x30107801910b080d02d00304060f60941d010301031259a40184451898100004c1a1207000c403200411001102004012958000e4001e50400c00640070140c81040010750301c03e0340c3c90300c001070900b903448048546005e0248000c0480075a00d10940c14003070000003518400304111000c44030680b1103610312001040c40500100800c50a1011a014000b16000124501c03020903000a02c03012520381441c01d02848c81055015820594100380800001e00a10f804915072804a050310034149404078003604c90030070080c0000b6a40c0300e4609041020300c04507181e21b0340040610040b17403554208214540c0c0c080c44100c01040d0807280c001500d5000d4803101080b40c0e08100030710700b0400e0120500c011400005d0044400080030080440c41c041030f0034820000d090703907075800501903051282e4801198030070340110a80312101c000d560b0854060340101e4505036805c3c6040007a00d0100402700c1d01900a02e40e0013014101c7d10307400400c0840001018102d4005104210b41e0035128078041035003110340641c0d1640c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 283357131 1250 283355881 283355887
    0x1e03160317070203040605030f060102010921030c02030301050d021e040617070518070c020f04020f040501080901060b071b080604120e010f021902010903201002120909150405010306020d0f11 84
    0x20082d800b275101d82c8640c06000101c0d0900c1c040e640c04803044440030040910075074503941c0b98041a418812000b003041d079800198910b5042c0030006104051644c030080c403c03141e1511548560564031500c1182c1500a00103010300e540b210880c03041030070348490f03014842c4212600010a443c0550844482c21040000001d190700e407a1011038280700308200903600140040c0c0b0903940707519181300810b900c484401030240c80e0b030b080600050485401500e0b00b619a8180360040c460729500d44c0441c0d440580c0503100e910803080301c9001d11011b4050340c2c005950fa01665042005104d00a0025440c0b9040c580e00e00d140000400015a21152211180340041e40312107501c400955031100390002c1540141061000c0b1940c83e0b440c80c1605204203064109050030984409a5040540c034805c01080140083c180083c030b4410070b00c0389401103d9000b482142c0440206005400b100506400240040c0c410b1149603120308240c8003944c02401c40031b41035441c010311684c96800030720401013904584500245 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 283358381 1250 283357131 283357141
    0x80d020a08040510110a08030105030c0901081c090305030c100f150303050901030e030c0f070e070509010513030206030f0426070b181501261e0316031707020304060503 74
    0x4131042c00b0004903014022031000705401c0035010008000800d11504d070050740c03903041005040c1880d50f5115481d0003500307142e0040c8a062008185900d5003c4840808044c840c092803040b24958440c0d8005010b030302000501c5420090003240c0e884507a02e4040b4203001c0d28140b1446c5c0800c545100700c2038050280b14200034800030744160300070702c1c50450514010894101040b210f9056a20917010b80215610003a543c1c02c080a00348070b548001d00b45900d17610203034980040d01400510400f0b200c0750402400240d03850180311903040c80c90146801412103034583c82c2c0700c0310350400780b07030150b0307040e24403641c0c0c085403080c19030b44404420007040050954074202140c3c0c3c0d4500c0001070000d0000030300c82d1100c007000c1011101c2040305440c0c01004624480e00c5500d840150b00c601084100404040740101010503064440081d5130201341500c01d0340044401a448001800e500640403040904d11313251152405055000d040440d001071003c82c00d2245883c0c28000760b0303680c840c510501c0c011403405c1c80014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 283359631 1250 283358381 283358389
    0x4060903171e0702031e030609160912051005070f030b060a0c030305060d0609030c1709011407050109050313030512040e06010c080c060c0c060609220804090504060204080d020a080405 81
    0x69000541801240e0401d450600e205c010005080c1d081c0501d041b000c4104035042c0352003100c56411034032101c40c100181e125280020182c00c000d01440c1c10103451589a0010003908219a42102107100c000f00300c1400c0081c0001c1c051055190b801c0000f0703080c465001c1c507506e004000c941808955442e4051500004d41d0300750040c001c0200040d50000803004c854010845a0013211000351080c1c7d01d40c00f0591403842e004141741364041b00300c1d00c0650240301125050b604103074803e2806040401007611240f4514005000d882c2c8050300803c14000403c1c0e4034250050f0240b003c040ea4400e90685041d19092503500b80d040c091441106080030128001c00c1d8594002d04400d04141d0050001e1850b000c240d000184c41c0c0304050715000880d81000489030750345003083c4072040e00644111108503042c108280070001000704800070113200c0f01014502410001d440c1e0032a4020003980a0900131450a070800030000d402c544190851401081c0f2043d44861011480129855004500c182030031708101c248 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 283360881 1250 283359631 283359691
    0xf0907022104050d14060f091002071b030b07090e1015140a0c0c05040209180c0705010908121803220905040606030c09020a020318010c0b0406090317 66
    0x240071800c0c001c1101088130340b110749120080900400c2e684440c4030341062560710340a401403214060780c0b0341409024200c035011400c0325005951003c09625103059051510005644025081418881030030000070400d000410354881c0320103803140f40d4030303a03580ca8405400381022503000703d8041c5806010302c441c04003528806250800b904d015802c2e4000c009141c1a0766022114500102e060104000304120800c9170140c080c00041c2d9055041c8684840454882d151311500c1c4010b01c8000c10004901030400403d4520903500300c0d001344125525030500c194507a004001e004400019400007400540342c02110070700d141c03403c5000b1458040380c9901c580c4000210000d110103024012000181500d25004450099004a80005075949980b40c0211500303800d60010351158014081c80304090f80200554010700501c0c051034098161410040fa02c148103408000e02c0c5d2107400c030920090049990103500c01c0c40c460f4a8039181c1d0781c2d454454015020040b036441801d440340a00700201070041c40b80c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 283362131 1250 283360881 283360933
    0xf12070b1003150608060c0f0706051801022106090105030a03111c0e0a050103060602030f07020a090207142401030305070c08060c0c1c081b040305030a0504050f090702 74
    0x4040c03012070b1240c0c1c9214030315440c0303120904419218901032201c65030501c0060782084800070035a00c4c0c82c8040c0e00c80400d900075008003500c05956400011200603c5128030241690102e008641d568032a00001c0e409031400c0d030000345d680000000251940c2013420740c0da4140e0740300600604c003c1a842d81d045800b401034860864803409083c0810f8442c0b1403028100d24840b03e641c03182085080b000c0180003000312681d020070b04250401f230b010004079801000300c0342c01d4140700b91203a555015030300204e840c4030140d50103224007500c0002e984040c406030208410040b0003603c1502e0965840c004d10300200d00000420078400744202d0700410000c0e0056008044151084418081c002e50b80e5001504100c0201d8041c01001b50020310018080810301c51541028115190404070210705100109480e00c002d14411604560034281e070940001001035400079507015044a984040c00780c00104550024420b05000d08440ca4040311a49000c0c0304442c070800b0395500500301001d240008041c55003400384 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 283363381 1250 283362131 283362151
    0x10c23032701091b030203150f01090902040e0709060302090f0610031d0a1202070f15050702060d020d0209130b0d0b070309080f13061d0108040804050409050c030f12070b 75
    0x241030800900c0003403601107031149500380741303448601e540181401c0c0011740788513400880380c42c8100607540c00881103150540d1261000042c0c996000e1021030010f01c4508944982440b40003c00100716a142e0008019240309868650060300e544803402c610481c203440069110064954154290380300c0da016034004403501400e0318503500e1800980b030a01c10003039010340300d062088151032070458040005030b004010301050001454600608400c8499840f40801c040260000d000c0b4199a6140252484150180003c56440c440c20714500000d5200d807901c18024801008030b40c442e5103091240000e1240701800030800c9016564425020f010028140c009040d40c0c2c134058400300d10810068001d403a04411026650003045050880c50180f95000c0c0007040f01040d070081c20031609612400c1c103c203080c00c0010903600d92340307800c441d1030199401061b005840c2c484200c091101c00110b01242d100150140c6510310501d40496031a1000550840309007801000343e98001064000001c1d03121080d09 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 283364631 1250 283363381 283363391
    0x80a02030c07150c03110705120d02041502101404021008100f121a0105060a1d150d0c0f0516140609100501120f06180203010c23032701 60
    0x1640d031510310f0780505448543e6540e034088a0b004260588100c910308200c0d07a800c0d0742849010f40e40c0e40d0352a0012181480d0413400850303036900384861601a41d01070309001d1140e0482a4001c2c0c0001c4d541d24120240403644c50604106a0302480340740340241c06180c02500301517413a0200d110540b2201400781c264110a102c0c01e0f40010f5460514040b04090202c458000b400c4030414104020106c054a5041808804110040085aa40d40d0403038104410600f094098040c042c00c20048851510b40000c0e045400701b42c240c070303241e5000c10041103820204202004000305507541202e09a02240903100406c02c100159180c8820705018260040d104000c4607070380190a003040e5007009001c1c0e83c0304032039500c12668814401017600542d805080c0064060310032102c00d40b20f51000000001002e040a40d550801c41000c184100b00d4142c1c003500034000340700103955880000c000352100c00b0784001003060540810316848001080f60301a138800c0e6102c03003108045041c61090740c001b02442c4126903681d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 283365881 1250 283364631 283364633
    0x4020a0c02090709060e06090307210b01120201120b060901050c071208041d07020c010503060d05070305031801030209030a06020c1608030301051305040506070f090308040905071e080a02030c07 85
    0x40c0901c10710500d03442d618a0041445c040f07001d4804d4103800f034868881c16041c41120311540700007440001f110582001e50f034040095000b505840d01001c140074150001a900114040f9402104080914401c0e40e800401e050850441c2c070840d04400982c69102e2020400c80c503a40d0311400c0a0940010fa030401e07110040c0c2e0728503071490030815036242100d1454000c1020441881a2190708401c101162813100c400e00d09028000c3d2130f00500b036040c9041c00310100c080b42c215212920280c40032540030003102c81d8a6124249580d403508000c020740144200f5201c8809154424000c0c0d86400c240a00141880b280e19a41d04019400000c1d264078503104250803840e440400c509131500420b8218041c50f900d505100921031152983d00341341802c0c0f030400e02404002100020443da0000341ca10b05106142080401143d0903085e6030f0015040c03c1e4042800304103130045034000d40c0207107826126005480610703048204240c80308000107000c980502c00042c4000e950390010750307000e43ca0054042c42c01c902 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 283367131 1250 283365881 283365889
    0x1031404110316180606050309070303050d091e02030c010e0a050405180d050405010e010c030e040b010905060d0f0c020a0c0b030603010b100201050a1406101103070c080a0506071d04020a0c02 84
    0x226500513000070454112005000d115882501d010380340500d006841c43c601400415911784085c44000c0402c84001480b44010080d075200c5080c16034807a441100d1854021a40142c0c4007001c00240d10a018646294404e58000e060090300301074042d00328041a4640010070000b4600200401403c81418403005817800c414800590280829111192100e042000040440c4403907a41a81446a4442c44c1c60200e60054091560f0702c204035070219004c2c0d20070004885409281d072009803c6880400c1f5501c01c8845a003202000c480306217020003101c2014003040303984100a000181150744c9000040c032504000034000c543c403190145c00803e0b65000540854548400c01c031041e40140d5691043c828814500d002d9581c1101103008106214140880005c2d80884c2d00c03000b0809020b001d44c580d440700c54050003941d54081d045a50329081541c0c45442d5511414000f808503628000c00300012200c90090318640007006241080d28503011040301844025400800c01c801402207070107280b00142d80d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 283368381 1250 283367131 283367173
    0x7030302061b03070912030c06020a0e041811010807020f120406030506010309050d030f060e011d0a090804350313050102070509070305060a030803070f0e010314041103 74
    0x1100394010301480c03400800a440c04000d90002c0701803400100140214a50f20121072000d0311044489644d00074120f1038140e034224603008004041c01c0c00420020521034010b020080001c40c150781c10321a403500c03140d11132594459000002c1c0800004c11030140340e54071940030031b54089118011500204103030b00d1014034140c030109002081450002d000e1041c82c1d818001c490b005502801c00b0321a01140f40c2e80e0329122a41303040e95074101650340802d4030b02c00c9266003194000b00294866003a06507101c81011a2600604021818022000c804901c0c100c03020300c03a0707641183c0c1000502d030900b420005e0b4400000b294018070724018034011101410038088511501802030490300035a5940e40c130003c000035174941940703d1815900403000801c20703512980000ca61000ca2854005a04d9441c207000405001940c1c02c040d01c2e100c0f0101c20045810b41103c500b4892090a403188060301d03903501c0045080d43c0000c6500c2d404400c0c0e500208000a599207260b0b00c090500030180e5182404010201c0c0c240e131 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 283369631 1250 283368381 283368383
    0xe0a1e050f010230070c021e1507050105130f1712090a020a1205100c05041203030212010905131103030c01091a0c0a0818070e150a0e100512010e0703 66
    0xb0804994070404040c4c2240101d000080c40031244025180014000e0800c502c00300010340911980305000d0440a83d00030413010401000f4499a0700c0e151401c003d642a40003403008480940c40d041c0442c4201d42070880e01b0904035400381c40491440c075079a0b42c06540d0821041c10507584c40047c041040861200088988203000741c4009007512a13080c0100308140361591700c42c0a4074200404440b010500c00b003102c0c140d100d18414041510f54640c0c40894542c4200d91200d1684a0f81c11148000c16a041e00208090303182d245400d10682d0701c0740c425800719602640e4400c4004050082d0b58001401c14841507245000202500e09222800d28942d09403081d481c000ca421040141c03a509151035002a0745410114001c142d60a000da11480a09101c4024050144500315545a49445c44c0100003a41c081c24000e801c0d08802d0400580c0000194540f119680c8601003994000c2081041c50b21360611501200540c95409464141170007031504a92103e89015500c86081d40c4a046041080100071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 283370881 1250 283369631 283369657
    0xe07030911060f121513152417060d1b0e13060501081506011407020a030b06040513020f19050a030b0402010206070804030f051b0d050c010e0a1e050f0102 68
    0x603501550401c401c07100c00170403407040045801103e00705d0340c69020004004c0044080c00090000d5010340b003c0d42c0340d0701940400d41c0f41c850b2020200d202d01280462580d80f06507901d4940c0403642c20901d542d1411802c44055400c00c4086603030301c1c0811700300100f21909800144003210760b15150783d4107030041c1c0c0c402c0f9a642c44006403a4030000410585204050041103418041c0011102d1f80150a440580140a090402840c0c5591076a00304503002140c1e01d2580c018103003101d140c0e4a2401c0f0111040480700c42d8401e074600301c000fa820091408400c041c0990080040c185201042c0070072002c242c0c000c0300c0da41c00042c002008079054542081c42009140110406c8480e0b16092000924055000707200c50100700d0120309200003c1d4000054040100c65414134981319803040b502c05800c0c3c50a00242c14061160703400003031140d40c2210041a002d01240002e1021a10044071300f60303034801f041d10041a0f100c110600c0043c030016403030b510040620480a480500b04142c0a05082e0380242c1308a00c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 283372131 1250 283370881 283370887
    0x60f0d0504121704020a14030712120e010e030715030923010b060403170a050c03121005030f0c130209120724020c100521010314070e07030911060f 65
    0x32504078a0000c0034243c080d0203000345142c15800304100c0b6803248512000c40700010b48464640d076050109101034800810110030b40016810070756140f03119580201c000c07503148003040c1202e512980d2030b40c09158002e001441d480346403034412100508681078007400c05545d0200480042c00006480b221095036040403da25010080000c3c01c50b00142609441082c1c03c000400010b070288004c0c0e80c12851400170b0503121074154900765910705c01c00b40502d0085c04002800f9645c401d8403092603018020740106030313043e41d03118014542d0f00e43c01c2c0721205640703901c0760500c81c882e403619001da1510942c7d07444025040c00ca001000c92400c134401c1d1201d10701ca400c0190280007442c191245946400e003520a80c8012020b0010065212810140c5881c051016241745000d06405882102c004180340f0881044000b10442c0c9440c030800280001c039000004008400e80307002c00000c5d81e02c1650074900780224541c803000c0c3d096004021615046a8601014487e0a06a075610b805040c0144e00caa400507a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 283373381 1250 283372131 283372163
    0xc0305070b03010303170a0f0603050607020105010503120d05150a030b1f050d110411030c0c0f0a0c0605031e0f011712041406090301090807151a060f0d0504 69
    0x10914103990841c00c00c0003800d00c01080400e030f00100d0b00c00983c4040b898050740352109103000003d000010b0340da10603a81003000010401000040040c410303d4150b000304002d0340c8802c100354071741024010740307821040240302c00d41103001c1070340c04140c021041d6030000d00a0020721001c94602c03140d9501c1550301c04040c0040004e0b20310550b10100b070385001d240c0d000320194103102c0020008042d41c000508148e4680c801e0400503110b0307920124034514104a820b440b45442d0f10039a140364030800f5124803d000302d0180f100c00d0035002038805202c40d400384031108114103010048429800081c5a4101081c122821040c008002c110749030054516a0b41c504080d810959144030700c0c9110b003220f54155202d0b00100d56213019507820351b400c1ea01d070000703081c18520040001034184d000b040d61051303140d440c104113001004403440007800032034403a402038210710f6610714072801140e80e0b1130a1002d520f05100c01c0c1300326614140703000b0074034041407073315442c1070000c844001c80840d01d0803101100d0b203190030f41c42c1c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 283374631 1250 283373381 283373383
    0xa0c0e040c03050403090609030305070b0603010f090c05041103040b060d050a0b1510050c070b03181006030201140310030b0612190b010b0f07020d0201020f0607030b18010830070c0305 81
    0x19200c0d074104020b02c1c0e2714503074000b0300d20b10a21802900c1c43e041540071a4240e502074100280040511405005107603090410300c00c01c105074452540306925011011041c000c001c0700b0303a4800c1f034000760024482d507500c506100401e0950002143d00d40030707480e550000505031280090141c0403130343c1c50780100d0755a44140510143c2c00a43c94040c813405001c802d5031950001014010b03104440d441d40e40329140c50400071106030302c240e4621100e000d2001c2d00c01040503036521a104581c000d83e40c0e0705a241242c00d4044a0748010348a000a000000c1d606101264022102c0c41d04104090a42ca4480301c044d03000c03170300b48806003039401ca80240000c0d03510180301c0340400711400340000c160b041c1d141c0781c407041042c1c0e1203218040300207006000140300c0d0811342e8002c0c04407150302d482d04c0d02603a61516103441c008000344482c40c030070781c410782d006610101c0000c070005515068408072002407070705200c40d104201c1094201145a0b8070602c1411550140b510500701515810744240c4201015504501c0c1c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 283375881 1250 283374631 283374647
    0x31b02340f1806090e03270a0603020904060603060506030c07020d080c01021e21040f050d020307170a080a09061b170921071a0412030c080f0a0c0e040c03050403 71
    0x20001070178056006035403003020041b00d003915540e81d12034020310910340c025807201c0030410103071350301c10a03920340000c1151b015002003504a0044a040004980b13401c0160100c610a00409420200500024025034035180042003510700007490700d07043d01c0f0300382d413015001d900c4001461005e035004a4410042d4080b03160240c46588130074549401c1500388007850300300644014507040411203050218050100fa81c2d604175440b504081600d000c42e40070030010b90b0782d5100c1003044036011040c841e0f150f0026810300070f451800d20203688844040c2c075004d03a0a03002e800c1407281550207a036030304480a4440400c000d03807100380e805030303e0740c0818650480c0700d071661400040c0105020780020200f00d24240240b07043c4039019440b591066100d00756810310500703c020703205400e2038851503101488284405d01d00140e2820035156028400945100022130352007105445210880b00b10002040c42c0e1051600b20b00c0480036a842c000300542e00580005064401d06c101c034901080d41c0b0414442410303448800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 283377131 1250 283375881 283375889
    0xa030e01062c0411040b0103020d020a081b1c0504020402091905210a0609081b030318010e0a06380307120803070806120607031b02340f1806 62
    0xb032a040345002d0b15556039407004107000c180324130303940c0c09554006ea01070750540304030340952841103461300f090039000340551100351100204040484261551f400455048072103107070300c0049868034001013180840c0600f0018004a078029024003078400151110030039014503000d000d0100101c44d00d408c080c48a01415558008030500380d9503520100c8080009000b1a8a58050400920000e80c1d0410344058060144003c04c1c84260310b602d813084075800000355000b0740324014002c00203805008081c2c200c4000c80c0142903140c11a041450100340e080e88800340811800451144e0301720101514074860800b240ca94030402000c0c0140109400c1c104481c5020740594000743e0300c520302c41d403540c05150000900410402044400003034281c1c50b4030303c034036100d6038450b011210307182002c041c0500505a8000c142c04e5543c074901544440da0b01c0090840d219104150300e6070b807010404c80c8606001748007000083c145095410b000240c24a03403e10600080c0340004c40018445000b104000c1a9640c9500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 283378381 1250 283377131 283377209
    0x80c0f0c10050604020c0c15040b03010905011a09010c0210020f0f1e03031003060513020d08180a060906030e03040b13080c0103020f04050405070c05030f040608010506030403140a030e0106 83
    0x40501c00400203031401d80c07000100d540783c008e412116102c161034480d9030480c0e5141223000c000000c44000c2600320300d040c0c03107c02c00801c041648a8a50b20170500901e080e080c0010200030b09440036042041d90401d01c00c026205071580e2401c2286d07201d02d82103004c01601c01355802604110078242138404115000c803d83c1c0055461400e01405010600c1c02030300010b806280d541d004079201480f1803204020060307000e0030007040680541081c500c00d0300400c484c0d20800b98500d0410b4030714a0581c07000340a46686c1e49441c0310040c00c00104800400722840240b41c144000c100c04946445280c01802041c4009008040380c103007410055418031201800c10390606005125051611000340280d42c150342050320000344030380d94914101c401e9076602101078941e00000540d0990414684010025151207032113000c0795903a42c00c1444010701c0100c40148c0003c4ca04403102e0081040c0c103005100b0402d007441c0c04510000c0c103c002c0760071544182c0c006901902c600c40310160000514500c0b03110080380c58 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 283379631 1250 283378381 283378387
    0xf0c031005070f0807020a12270b0f0c0f0105040c05011107060203090f010210050403080a0e0606130203130506090304060f020c0a0e0901060e1005011b0f03080c0f0c1005060402 78
    0xc8003e0079010300c11242c0014070035014005880180b00708000210700d6000303000d20310800c808600c040e154020000e08a40130700b000400081c840440140100100e0b50014034180c40c001102c032500d0420b0304043c20100181c082c00c074050b04c03402c0003401681e0003240102c0030004007500e410300240041d8443c00030001580c00408080110640120a60705100f5040e01e81e1314040d8003080040741400003800c82d000303a1038a090188011b01d035128901f00c1c414100c0b400100035503424001c8545d501c0804841d46540611060304208441a0f641c000c1c42c0c01501580610044401c1507403140d080420840310380e4042d80c004030f0100100380e4441c8041021035080e00141013101102d8010440d210307034501401c200500302c000401c000a030300754002001066100241c0c061403c264a10070012130143c0303c0e5500050b901009909482e039140449420b9030740c0580c8400c464215950207079081c0301e0080410440b00c038280004020013208800620560300c2080241c0340403240640b4901c201e403005000c0038001d91041c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 283380881 1250 283379631 283379641
    0xf0103030207032603070908010b0a1a07050307020306070804020f0d020f0d03020709090807050f1f091509060504060e0d0512090111040e160309020906061b0f0c031005 74
    0x810002c1c1626000340220751003145500071140700c0c480184065500f608000104442c00d80d2180030402690748240080c4107000d0303050308100450119000d1044030a244403034440b048814500104101c2d480340080c4c1e0b00b0b000260b0006030030480d0480341d03800440d00300b0003000110b2800c0e070a000f0480200311410840004180c0125060106680c1480d008010410f1805c06040c02040700b8001800400c000703000040b400e15111401c3c1d0060a000c07181c5200741111411501c002090800c18007905a40003492442203040c0e11016044805045d034102440d4100000000c51394010084014050740e030218181c1070034034100c0129480c1c01c00c01d203155040581e11584603a40301302114200c0380400f43c1030801351034a404082c010000042c409208450000f8006000c0c8000a1903620660369569404030480e040d80056095540305031000b0b502c2803816002404503c0e11f4406820038580c24482d184c100780c80a100c491604901003840540d66020340049101c61030100501002601055000d01448c108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 283382131 1250 283380881 283380883
    0x90c0a290406050d0f0b0919151202130b040609022104050c0d1a090f10060b04032d050f0d03020c0303070311160b07090b0a090b0a11150105090f01030302 68
    0x107140640c04400e61260403034440740f0324a41203006d80c100001c0140da128204020125094409007500d0010796040440a00440e0070b1055040c04480380710000c550f420046038200081c490200911603200d654038016280c0350380340c51260101400701c0300d10040e654015842d011040302108610a050b4031307004005c00002580c080b03800f140c204020788051244a86905c1c0c040007202c1c1100320100300268160400140b400d0008a00f25610b103c2029513008101d0101a801545d049004041c1e1000d0308000810004822190400801c2d2802e06490246104030110022404103188151815071169404c20752440c000c2c80401110103076414110328000e803100c0c070552280002800c240515503200d507503243d0048060103c0e24400d108007000c90b2400c8161503c90030041c001c0d00c02c50700068001070040340d11030110044400f01070701d540710182e0315403a0070460301c3c1035804440e10904114a50700b01c1c1c01d0600040007080200715048610000c0c4d507061405012131007000034002035160592000420110750 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 283383381 1250 283382131 283382137
    0x3030e0609030c04021309090501091a070804030804110d110f040b01080c0703020a1a0708010e060306190615081f0b030406020a0c0c080105090c04110a08090c0a29040605 75
    0x1c04c2d81c0140e00d400350b6035581c03400c012666010068a0f418080032034204801944164031807031090015002d80f00540c4801003603014200c1d408000320750342401142c0800e0080203200d500ca840f48180c100c1c0d00c1070031400b040c0c01c003031900812511000d49a00800c0145001001c400000704180c800704143e200760700000700320400217040d000745c24800040390390a0600c02e10180c644c1d19008043c0140800110071503000124086402d00e0004888100100b0341030301d072001d01800b4200040003083e090310f0350001c6400c00e0424000607000c45a0b5400005414003040c0000407040849488107800c6160405814607021109600703251401014242403100098000179290407580141d00161540040c41c0306803900603404501500551244600054818054010350311458100095030300000c110020700007075428186441004010620840108502c07400200e0303846070540040300c031a44400008903c09204581000020101c06040c00002c89200140401c0e040116100e05241c24035182c40181280 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 283384631 1250 283383381 283383403
    0x31212020310170a080301180b0303040302060a030e150a0903031406220f050f0106030e0d0f031104050a08070e16050405060f0c01050a0516020a020d0809032503030e060903 76
    0xc450301e001c2c0440e5070310422400074203545c885003559503943c440400559440c013510200714000c1c100310090529040100540c0d0807a680900031904004000344207a01071312031500084202d20955603426940c2030160030741e5009864000c80002c124a950800030150344401c81004a00c00092084c0102034943c1390b5030300c85004140750a1740c0b921159800c0d1401a000300f10100c040c0500701010b01500f11b80c040d141c28126a0300e501e0170881c4c401d0320b203120b85d250403820215002040140c0820351a2034004c3c0c100e44548520707400705520381a12480003c06400d1a5027040401da072003c6004d00c009011110429000409132007080001c24041200030810b11481c05441c1c000e040c0482c4189a11181c40d056070641c0004074002d0140e4034100d13001d2801080201e840c0d40761210100405291307180046182c1c0c07101360700034101465200a54503074189507406901e90f990984240e00701140903d40f41007a00301c050044481c03c55a45296017401003001c50030915451040d8000c108110300f41d0b400141a83c190 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 283385881 1250 283384631 283384649
    0x6010e150103113903040f0e040f08031005030102072105030f190603050f01050f100503030301030b091c0801050906060315090604020c070602030904231506070c031212020310 77
    0x20b4481c1400a81444240201c500c84c15008007450070790300040440a48250307602c2006000c441d640d81c1d103035000710203800c0d0b9025103c2c42d5401150700214000c80011a0700c0b4201060613503045035a84003090890307112002c10f41384d030707030902c1c401c1d521002d405030100400c0159860564103500b00b090110706100b0010f4908456107655502002460181c1c0e008240110f4000043e183c400110440b080d018042c1200c40340a031400490000b108051030160f80700503600041d00035401d41e03081d5550b920046002030100409032281c203c1c114222514841e50706a003880da644d071101d40d54540014414440c10250044c0e114060620030024035040505200c803100c4822a41c6001d50744a80c00450000e1080580702d0003180110b940100c2c801d50000010054418250b4080119040501514a6042405680f14942040704000c2888207041c190100300c800c1c8024005031400142e41e446101784103466000301d030305040000c4241455900725032020643e203102e580c00d62440c0341a03c181440d6103030768003d010744 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 283387131 1250 283385881 283385917
    0x130b041d040506150f060307120e01020a05121b031303020d26040c09061e090903021f020409020418050a050f0c1b060c0702131a041d06010e15010311 66
    0x617030343c44c0c1035003c0002c43d0262160707640e81082d42e802001d59107000880281681441c100c1200e41d01c0501c03c540c1600256621a8101409807082401010000d403102e410150071010800f000c4600400840c011110440841054002c41c9406810322404098090501064918040341500000c032105c03041302e184081d91015642d1450b11103218451a082141003078035180d4085620407031701031040242c54107413003c00c01003a690002407099800c1c0c03181c0140180c200b8011180d80d00160000c503600444c03100009030030325881e940c070b0310100c2c1c200c0e5003c07041c0010100c22203100d00c2c85a00c01c813900004003150910803494541c000a40002014019201140d0000340f481d44080e0f074088450b1a00c1c8980e402c0d2195418041d8104070a6044900c0591280303004120001840300d061046c4801e81c0300c8180c0300c5d40318256845c10400141084031091421041e050355003410540c0c180078141c041c245100d1540c119003800c1c0c0c0354052070410402558141841c00c40c08407020000c10044d0780d9068240e051000c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 283388381 1250 283387131 283387171
    0x150603040f05010e0d0905181306021303080f03010e25050c010e070f0519060e012a051e0102040608060402070c050d0b04020922020411130b041d040506 67
    0xc01489850480f00442c0659034141103000e40c00080c0f001140c0d030440c0e4902120601175020b01000205540f521049c10440ca000c00014000d500a4401c40e0843c0c1098001c00b07507291620f5189501002000070f80000020060000450704400b0b560444104c103101107510742c86c0c80c69240c00d10058031220003805004295000d954400f5000300c807003885001c05450070389680704006142c546003801074030f10030034109005a055880002041003154071641e0b0340701c5203500c02401522403024100f0a01840840c0b000112890560310481c0c0781c90a103d1001402d00201410485036808680e044091850740104020080f6550042085800c01012140141d4034080c3e8078000c10740f40c0d803070b0b440250045040c0030740c1020300c0051382a0900c590300944050815980c1c8054071000034035440300c0480500c03900302c5200058101030340244a210007c2c07059078508651004008004655503002c0380e0300d882c00040038030000401d525140109604040e0130031030760901d56034060301c920300241072000d1000d028500d98 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 283389631 1250 283388381 283388383
    0xc0b04141302090a0e100602010c0516050703020915100306052b050a08040e0a020a0912020a08070807170c01020705011d04140603011a03060a020c0705040f14150603040f05 76
    0x3500614008044c0555155100301c40105040c080322801c00c03424030030500048850040c01401d6000344107a03500c91030807014103410358001510100a4585110b03d000110058950741096400b0f110f110640022031345030001005020141340e40c80008041c02d044003000107480d410780c404841c41400c0e02d00944107018001c50b03401d1500300a0003401900c0359010769414800c0e0400144242d45507003001d200c0e0b650703d06117250305074070410300b90b8400250094030400030703440284148540d1904c018154a8140c0d901d803401c1d46400d07056000700206130172040e81000000d40d940e80c440903050214001d81342d00d00760f0400207900c90a440c8030f5141801030321800400b80010011800c260002e00030400c020100b01c18a840e89100021201da034003a6207001c019801010405086003421100200200b81c950341d03d800c81c41c040d4110810b40344c40d61180c080082600e903182d00840300c0303034140c45900040b400c040248a5403d60710142c411300c050b80c000740c9290070903180d0404403540a5040704610003803840c81d10701300d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 283390881 1250 283389631 283389637
    0x20031606140702032b0c0203060118020702040f0e0d02150f061306080106030201080109200f040911070b0c1306140d052a040806061201060f09090c0b04141302 70
    0x2513050044403d096410300c051341882e6040614503600036254010317000182c80b18070442d00040d5060307000c0f1004008440780014141064003440e58050309100c13a560204003a64003071800d584285403a10b00d40ca804110802c10104020941e10007400c3c3d04c0b8243c0e2030400000c8011344140c20814841000501d152541d5034009074120301640100059660b07828418001c2c0124002203002440100c00018070090318012541c445810b9107545011002c1c0c0a031030f82c2c0c654024510401d40300c2c1d0038400029110098410103d4141c2900d04a607914030403491b20883c00072006050301145813007400441c0840b08401c00c20402e0340c0c1141040000c0780070703010850180c4d0003175040e07034000542841c0801846c100c80002c2c50703030043d041c0900040605e5080c0450503540c0144e005040043d8051130006160b0318000913490003c141c004000141c4503241c0301c01c00e00c928850b42029105a855a215000b0848070724190340007046240b01ca181894108241c00500f05408000303c3d2103016003007502181e4420301c1e03040b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 283392131 1250 283390881 283390883
    0x709030503030c09010206070908100507030b030f07090e0a0308150a150c0507062c04020f12040506090d0c02060d11030106030c0e042322200316061407 67
    0x459032640303440d29200200b540b0130301e1014014090358010500c481d0241da500025a030301c00020b00030740309005440b10010302c4024590000c241d00c0d04040c0305503803810300408030300400b58400307041c419042108020654001c591140056030040303c0c91804280c1c046041c43c1c000250b2240883d004280a0000e0200001c81d00f0044020501c0c05164401580000111002500c1401a07444256030364806592444a6118007015070812008503040e404446200030340d190001080103040444802c0031058541000c0605504503508209000034440c0c01c0165542c020380040042c0184405040d00510100e10b00038000e01600022407501c96a04c490340001d542449142400303603c9694448000703014010780414040420307081c40e5100410704082c05095205040c41c520158039441e0742c0703482c43d51503c00501403111541e00e60301c00d000a40c820750b01540040d0045420103801c0307035203003000407640070a540c0300780c800c0d4424040d0005109000d240c1c42c1c1100e4641c14200f4500d00c1c2035410300b10038030541c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 283393381 1250 283392131 283392133
    0x20301020a030e0c0415090b0406090501060216080c1c081912060609081b0105070f0f02040b010203070b07230c150c0c030d0903030b0910030b091b0907090305 70
    0x9003076424164036900040d0781c66010000c42d0409144401030100700c0f4404181d041d8030341b0815106000e8520180c012000078107000e8000200c55507a01e69402c00c0390401c2c0c004000507041094545c0c124116001c200c806030455001400c11400c1342000140c000c0b408c7ca4681400303c00441c0640188003440d0f050300c881c0d11a0004001c0031010085d40285410450854036107628500b110201d030f41c51080c1c401e0029034100a0081040100300d9034a6602120a500c40c541044410465000000c5c85280c0d401e9887e48030300c261191400c0240304004c143d45090590604642c001d0150702d010400107103545401c43c80034180713110100d584410b0300d28244600b11402c8098000050800d1070b48400190220020144d001145610f440b0010102005e1048030282aa10f50003842095090700e4076038800010141700b4140000c40c1c48040b030204000600850344403c104000c2002041808880100c542d80010600040c04012440f08901c6071008010b612141c000c00c00c01c000070b9510740c0118860006160828 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 283394631 1250 283393381 283393387
    0xe0327040f0c02071e0305120c1c050403030f0503090d0c08190e0a08070807060302030709170d023c120c100b010905060a0807030902150a0311030108031207030902030102 75
    0x10b000a03550750300c107114034003030012100c4000c3c070700010042c20f0360283c990090240c03000c00c010300aa00d005420440c1810442d0290300c104d090240c5000440c441104015114652210710b1410007805124460802d40140803080081042c420390104d82d506a041841c1040f44d003424107030034115140d000d1910000c1d00480354810724030901d03030010a002000c510031900380305800e40b10301201d45c0703561081c4500c1c1e4903907000101c00d010b6a40240c0103103511203070910380403040d00c1d42c070306400000e031141e01c0d20f507050b1742c1240c0107440100c0d605100d14039a20b00300d40c1d44401022002d0407554550f081800400c14044070f81220741036565030134021550050407041e9441d4564509464040d21ba2507400e03500e0094030714100071890f255005e604003104a800041c000f908180c000d0905803220300b40100b114040650306c10341d400059803030030082c2e04039a00100c006911401000e2029088482c48402003000c40c07001c0c00104250000001150112900844080307420f86a0200540c09407070302040096242d4004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 283395881 1250 283394631 283394651
    0xb0f04051e030d150803190c0f12020105160f03150b0301140a09050609040627031809061203140d050c19050c0c210303040b06040e0327040f 62
    0x41e092843d240c0c2c07000c2140c035282070345207260140107101e03807403840e081807200710100750011a03414603070145410704001940c0d40343e03a40c0300034201c0385608071544440c0d480304000040d424411b10740d000d2603d1060020300328003048080c0a441d101e559420400d511500c0380165480d000b001007001300384c1401d25076105d507110781c0400d0407803601c5d4410500900841a002500c4000d0f409940c0c01940050810182c50b1201c1c1c0702d80d03001d00300680d0640860135400c80b040161000b103603040c900c00c42c002d42d9003400b060411412581c03000c009074805581395003060410b018540151995290007075050a0008402c00c1285805a00b07024800f00300001d103241c481001851150f02c0c2c01081d145c6203011f010a65565a50000c0d6014050340024601580c00300354000034a00b4403c11001d442e064680d0144103500e1301b0b044c10b5282d0f9000325002c5483c10140750910419042c82d015401d198100c1002960400c1101416010405810640d500f01d1500500100c2e00645455108003415000b03004288041041c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 283397131 1250 283395881 283395883
    0x507020a05060306060403051501090c1805130603150c081006080c1308060406020d0609020f120711010213030605090a031d13110a09140d020402180a08060709090501030b0f04051e 79
    0xd11404044d5401c0c1851004060b1240400c0210814990400d00b846800d103000c0c00306022560fc0582001a9a40f5010001c0f403d01c0b2001c0341004044000031079204528030740140048d4000d8070340c90042c003004106110085d0030491140d40812402c141d61b4554401085980e01d110b0554020025402104180b20502507e038000b8a20f807001c201040c41401d03502c0b00403030101d1040d015100c14075102442442d184448104070160400340d189800030030001000780e500d089a00c510440d600550000c0010400c00901e80101d560003039408001d41500d080540303016002c21800e611030440802039074030145040e0361740d055584500b0810b1f481004256186d003000e60517540083c04c1800810a500d2000580080d0507110181c40d4401a0106003070b02c00560910002e901316042a50908bc6605007903602920349103050802051a00300a00b8141401070000d80740c0305564200c0361030141080010300100b480450702942021005070540c1c00c42d59941031550400300c101c54160b040c0000704c0364a000c0000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 283398381 1250 283397131 283397173
    0x100513060509072909011b0606061119050a0b100f0608040605100f06030917070b010f080a0804030b22060209010f0201060f1401140d0614010507020a0506030606040305 74
    0x1d0440610b4201e80c41d86045060344d8481d04100c09a24141000500f50340c0d4812000795288402814017680303800125a6040c0030341b40c054220100141e2410141f00307914104000c404c00034560441c0d80e1200c0340260711083c1c0c03240f0201001401c4184100c020501d42150841020002c00890112480301c50301c400d0010000c40e41514103544a42c100804070b2044050175240b001180d4152038041d4050749050f074150b015010a0f141a01d400c0111140075100740510001810200c0c03240c0320650040d0f05143ea805203130a03ea401501140d0700c401013110004110b10100c50690ba004080e0260555400c01002064101b520540708591180b6a204e02001303095000340502d180d090b261031003030364041e00cfc00320300f00c4d01c951043d194480006a8100442c8100c180d00c00d42c07440040c07510180d00c07c29441c01c00320950040c1184200142d443c80c1c100001143d80442c90500d20003464001c0ca407600396000030b00000c1090099621940002010801c90f030345a404a80c021079105043d105141ca000b881489000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 283399631 1250 283398381 283398389
    0x10608010f06050306070f180b0310050a080307321c03050601021207150207120c02041a030307030305070e10030e06010b0f0f0f0d05090d030608070810051306050907 73
    0x80c100b46000ca000e1038045a11442050301e170795400700c0840c41590403a00170001060000300f152980301d011803904448001584105490444039003150316200500c20807082d80d078486010340d0814890381c0e00013000d41c041c1d00500411000c3e4620800b09103c910a107595045e8076541d800d20501c0024800390013040da6103502c101403601c00304002c3c2d0300e2a0059840d8140005c100070f50707803410040c0600088506040050b07140b02c0103001420009503940d144054200403040c10040f8010000a104525041c0a88244039185c2c0b00718024510b01003010a03664000c0030801403e25071101e0000c5c0d4118413507841c008403200c0003800041022048000034000b0000302202c3d1007d130280394000b10f03980d800541162103280000100b5444c02e511a41e5080f5103400ca5920240386400402500d600644107000b0039000e900c0100c007500b02405c1510024088901d994480b00752500461030802010101045c0c2e10451011154045115a07030310400c01c110107816a070040c01e09161205205401030001415025a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 283400881 1250 283399631 283399661
    0x301170c0a031104062304090c05060a1701120c0e150a1805090318150906032401030e0304051302040e01240903020d03140d06080d1b020307210501060801 68
    0x515201d16041131b000c101080ca4010f100b02c1104400358605082c0e118501140c0148840c0705195103410009d40654000c9036502c0019041420315040080200c680c00c2c01402e500400315203113030107580c07400f401030140d2240d450321094a07000620310091020501d4440c04005090b2030583d925450160301901d1203200030b8502510b00000589841c2001084881c0b002106854a107038406104c1008040c1126406a00390040c0600c1201c1d4541c5030a0041d40c0583d140100390404c1e2040004480030080c0c0c00c448080c10541400c08c20260b42501000f00d4003a60010348a000404c0e40720302251000c3d1090781c1c04440428400c0d000050303030030310710060720348a2000c12103032038007582000c042218420b10f41e00001e980482c402e00b106001900074240c41700d2150010f0810303828808080c5ca00e204450169008072034030b403c80c0100304030070b592020010908800100c8051184846030b0046035980090f4041d070b003e00c95543d4092007072642c4480317040707006e10740c08402488003645031034407503006c1e0641d078524100c0c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 283402131 1250 283400881 283400891
    0x30405030c01051008150420010c060207030206010303030516080a0b03070305150106030b0a0b0a030b010c020310060303021c0503010909020d0212030403020108060607242301051e01050301170c0a031104 89
    0x3c01c1e1104146c40307002e41d030010b280f11703945071110145000120b070140e03000e41484940412540041c6042c005403444a010390090440b030761450601400382d410091204100a0720054002c0810f50455241500030819650002e040d45401c404680b600ea0180c2000c0c10b94032498800c010314260101d40c0c0c0d1306860300307941c051055848090070301542010b81c0c01040160401488107501180c8250300002c032010301490800c01c1c026581d004642844e5006002c3ca6801d910750f0014000c1c581c0400400e984040e540d42c08003500030311036a00038624007040c02402241c41d21a000403081d544c408080501d0b179500202038809542c84034504554a900c248070882c0421401070003d09185400003d6980054000700c18150452811030260164171082e5040210151f84508625100e013a40050303420301500c0c4042b800940d41030108000b40c3c410a04030b141c4046085005140c1c2c079036841411380e8110b48802164240500007107101e182403ca03054122504122005400010301c1203601e810424010b00751000c00c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 283403381 1250 283402131 283402153
    0x8010603140115090b2b0507140307050108090a2a05060405060f070f0c0b0406080606091503090a080d05070e1e0f03012a110a0314030405030c01051008 67
    0x1081e200f0100c83d201c0e0034082000200b1507000a07412440741010000d100c07055660490881c4810203c503200c41c2c06602102c920b0700c0040080030880d01c3c02800c000c0068000030458080003e5443c0201c1c007a41e8108420714001c207011090412440c500c09521010307150060950381c0d407503056411001e06814100c5600040002c450a100c0115400d80340090161403401c002011602d20030342c400f240c120381c4e20210035002e2010811290410010384415011103580350f03e0014001e0031802c000d00740a1080c40f00300441d0b001d56131030082c0f070034409060506040c0c9030340e0384e0925142130020408000d0084c550020b64040407e0079a4005842890240c540812400d43c92042c0101200c00e00c0e00742d002003204404004207403420300d603401c812100c020000f103821701b010300c0f81c2c400380c0092820707516044552880e030741200d54002d11740040c9a64440d0081c820818580c4000b4010383c0c1581804c000f00388000003040a211043c8100e5019504800c0240864100700c2c02070038404050b4402c4000502415600344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 283404631 1250 283403381 283403383
    0x2108040209010306020a05130305010204090f0501121202030f030115111b0105030a1d0102030a060e09071a0c06040b0601140406080c0d021e030402030c0609280503070801060314 78
    0x180555006400c1d029140c0c20766139500c00035482410f400d01445814800c403000705a1080e1110040c51242d0005070b200e5107400302c0d51003504c100500d10100142004014440341c0c62a26610148540001001c2a1034482003001e07410362144040790440c0681c008004030344060722a1072141d007441580e56800c103c4542030310858403541c51078404040030036524000d021a40c801c802031600702990080016007002a045040401c03d02c0a8007501d160f5008401c2141c2d0080512031345000b030841c45000141d5140030015983c8811030f070b0042c2d445003585400c036540e4030102841034500400006044503414100303420841e5620400301e6503e80012400b02c091010302a0304025101207a09039110080c4580300c0b02c8005549070011944c5901c600e42c01d0100044c4c034034010f000812010b2107140519075a081c580180341c10a00c0c4001018040c00081102400d00c0d00d0751205107000815405118403454420721070580304441030b50040c0d52500c0b8002002c90040e5040d440704080745d1140090400b80401d8131030321 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 283405881 1250 283404631 283404647
    0x140904030c0b04080922050c04030507030f0f140a1518110d080a050406090501030606081f0e070f170402010207052404030309140a051e010507060921 66
    0x1800030716a51040ca0000303140002040e0440d01c16401642408909804030f51440840c071005414001e02460105840d0024071429030880440000d09281c5411525000c1e65104030340b00c010b25501c200a8140706000c2c140240382d0085a001a00145041081c00d44940e034140c003903415501403101e800c1100d21403034a48280321405080840c2500c0107030300303501d50814410601d42d015400609110500c40090750b1400100b0f600e0071203445181d01c90381492030003480c0e000e0341d4000d181814640103090007055002041164003c546c02d40c000b071140100d40301c500c88074069501450161642038180b01d4032680214518a038a10590b546d1003104480a0b402000c0300d034207840c040d001d80c100840070300250a1002c2540d000c000140d50800c800d101ca200c0c20411a23010340c0c030035400684106400e00c40159070000c00d005004084401108603818440010844200c0c8808040d100c0540400003110707900030b0b000e44180d66048241000b8030303121820006580c45040044040c040180031060503490f02030a20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 283407131 1250 283405881 283405883
    0x1030c0e10030e01150e010312050a0e0d051615030b190302011815050304032d0315050603010308070b06011e0c0303060509100905090c031b04090813140904 69
    0x940585401001c0c0154014481d00080103035554031003424044080380940507130010240054505040d62643c1414901c070004880d03d0310420030304104065803280d00c00455940807000f12285500302d003981c600507203003009141c402d410b680c403000d200051490040403401d100c2c550540b401e10015002e00e041000f551b485c5640601c1c6c2d81c04c0d54800b07101551003415035030460050bc94921055035120144607500391019540c0e0000a4400400c001c10140d010300800e44141741c1240141c642d0034528922001d4851280241341090303a601201c6202f42400003901004220250101d0f5580d45c403410000c040b64800f030020307076296034000041982d0b540b0030201c031001c4d1840046208214248850201c41d61241c002c4150109900c0d8000451942d0f2100c074858016090000e50400e0070345850001815100002c0450483c3c2d00283c01800c1240c03408586105c155082c00d8608810540c444001340040108180c007401003580460403404003201410700d0025111410b42c40d01041549804114050b00c0c02c80d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 283408381 1250 283407131 283407139
    0x1707030b0a20130305280f080d020a020105100f060504090e150c0d0e0f0d080a140108150c03060607020f01090503010c050702120a02090711070306090804030201030c0e 74
    0x5003221586601010000c0c240c140b9000d000c080705182c0300030b107801c0f014802d4401110858100204402084100d481c868902040c2032641c51036820440440c10546010742000d8049104100700000c140c1290051404013104549504400100034000c00301104e11007280d000c0100003146040320107421104440381ca950700c618180c10003042c40c0282403208100c06180c03280d0790300ba141e450140c59140303104903040c0300095161003510b40104180e030310324000408a904002030700f041078000031945100c048441d041642154948801c218010020351849001e0b41c081c0500200340e80c4000300360302014006504500c0c280391501c140c0c8580500c415215994007280404c5010018203101d0407030f4007000014140768402955480c00f003030035105100c910350006031000074414110f2900012074202d0040c01001003071b0740c80c241c2c0c0c0803d400d40c00162540c2c05011303110500c2004001c04111400245601503401e2000a40c10f10700703450075401c03d00080303020070305201940c41c20a110310108109410014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 283409631 1250 283408381 283408403
    0x150105060c010e01290f13020a0908190209070f0903150e0a230a020d060203040f080d021b03031e0603030409051509060d0f03210c0306170703 63
    0x8000c0d55038003541c60000a95220168810018400c2c411803140c00a1030317406240c01d9202d5103040008401c84410f082c4502c0e405042d1107030300c0c1c039984d000104014010100603034403407802006844810980d03111411900c40c00070200a449281d402d541e04c03851090320110b200391074036601924141104c00410f000200c1c02c910400228202d100c1000c031040c840440000e646015000642c00c100700403400f60b40c00c02540000e031010400303021519141c07038401d001400742100340b0b50029169120700c800250484d90040045401e0040080000c46429804421240c0d9034540d08804806504810510000c5102103140c108003114044101d0344074820a580b1544c01d440800d501608061000d0074258040c4420310012407146102c1c89940c0c02200710042c0301a02d0041001000f0749520024092030141003496402000924100d281c003101950605102c05200546051021660861603400b054103042401c80111182c1590050003618480300c94500343d10b00218401d80d840b4918800105003032044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 283410881 1250 283409631 283409639
    0x10f0e0d0e0d0804030b160e03010204080c040e0309060c01090c0e0601020a030f02120c100b030109031e03180f020f0a050d140a050304150807080606030a0b04110301080d111501 78
    0x10b92080a04588145040c3d4201a22034945c24080b003001c9400800c3d80141102c9465140c0d00942c0c2c400b0b0a50701180213601c0c280c1040e803504d40300c64240c810705000d152a00f0309041c00400510a48015204c06001a900c031007640d802c45028040c2a18203840303004880c000480e0b42c40c88015150720940b8180c0082c2007100c2c1a540c100e03001002c0001d20b404502070031101c9019410b100004007102c2da040c600500d280c1c03200704401c80856103c1042580300340e01d041100d00000750041c0c144000b03d03901d00b540a40c09802102d007500901880400c0f43d0307c90025450810400c50020202214640282e8092500c491004141305003582140265a808826890310320001b5251281000256980c081560113481a5a40740c074555001600035580001405450482c91a4800484c96021030545031003041402c12078003080c070610010b0604841940c803080c550036191102c2d0041072100c0709206140b07503290707910072200d5103807140b112040b0f000070011481c24001c8500080e2403580038004000000080c1d10f8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 283412131 1250 283410881 283410889
    0x1608090c0109180b0a1202011116062001050a02030f0a0b06090f041407050c150c0f070302150903031b0f040e1008010c020115150207180f02040305010f0e0d0e 70
    0x141c1c1d0b4000c100262607484240d085c1c1c85883c005030042c4000e0f0700c0c0c2e51018513035100141280009903550307111980510507410552510540c250102d49240c10480b00c0c60005003a0490140d40c019004c03010f035801d090612402c860303d58000c520820100340085110b844030000c08040d9807a080e030b49a40100280010302c2c0624028201c00302c090401480020601031160656410000c12580600030520200d4420f82d088028084044c280000c4401e80c0b0592501c84d4403804580070343c110345080040c0c040f07102400c250081000c140d0381d40c0e070000d250616140405009079a94001c460441c107094595211040c55401d120580d0505090120540d00700740c28910040026680102a00d15034408200c0028000d5000c0c843c20140140c582e0010a0b50381d1141c801a15002ea107a11942411015009488010345d008c11000103540c612480c0e030101c88503194051000d000c814920354509440058004104201540280d01d00310f03580c02d05100d4070409405a6440750032445a480100c2c01c0c1001e118510701d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 283413381 1250 283412131 283412159
    0x9150a0804061d0a0615060f020304120611031005040c0302040303120218060d0212010e0601170a1b030f14010513050403140711030705030106060f05090a0503061608090c0109 77
    0xf180100301080d01041d9099180c00e403160b0040d503090341d40b200d021003082012030002019000c0c2d800c0c103011005282800950700e1040f072007815200e00c40406440100b010642040c000300058010b0b10352a0f052002111035154070318400e4610440c03520544052590081c001c1d0b404480d01500c80102ca000035a010201a42c0810172007503c0c2d4505804545482c0e8800e006007440d400c04500068a405c081c0d0755a984104040e08840303408801c940400c0500d0307910a81910040f2580b4100420319180c0b8a0f0b100c0180940d07545400c61420604800e44100780e050348030441d00000b007041404400e040e52502807044d4028003480d600f1400d031f4040301803409400c0e0085030300280f00345458192000b1082c00c80143e0f4001c5002100d00c1074110a40764010701c0c0c1040361002901040f8003c01181e45070000180c00c1c42011003102c000d1141c08a04056150742e10300700c142c0140005403e072181440c052030f0405140090111690106201101040c81040c0010b000944c500040c1c40d140303030b0b9034100a6503140b480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 283414631 1250 283413381 283413401
    0x30c04020708070c12140105190e010603021002211809130f061b020105060109051011060a0501060f020102090f0f0d021809010b010806030712020a0806090309150a080406 75
    0x207010015040000d1462080030010401e003881c01c0b80d178040c40d103802c94001581044100c050780c1007a050100103850b0700607280030300404007800608000c0001c400b030702414445c0d1010353701c27590841341030313040d1500070848558001303402160542c400c025000001c464010080c4204002c0e01c41c409165031800c2070108943c0102c04c00340f0030740315400b45a0300c5c0340c840014a4411a00c941d2256070344041e17140480044904100c150000340702900e00840000c002e40c0b054403e5600c0384905010346105a40035030318900443c0740b024103a070b116103000164200541400c0c490b902c00611740f0700009590602c10b2080c3d07802e4000042510110082d40010030201c040074141540c1c4c400e800007a48801a59000c1107148901c20318214503001c1d03d05142941d0031200309402e8075051000e20402c00519030b0300818460150707080c040440f0140d4103540045005248190003c42542c4165000c0c001e1500b000805402c1522003100c010103503105014403000305001d0700050358041031080b40402c00050050700415507031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 283415881 1250 283414631 283414643
    0xd08100e100e0103060b0103050c0a14090406050405040f11010203040f0b030601090b0a092d17010207020a03110f04021903200d06051f0f0503040507030f110a14030c040207 76
    0x2107403078002c0c00d25000d40a03030048441d990344101c0e9044550301402101d40c48802600c6003810a907081d00080c04034002010a400000e8000501c54015a01ca512501c064640540204114034080c50701c43e1048410380c006a401946920b2103007800d6200004131000d0b1001486409245403a10b06107107402e400c080d10071030520690400c0814102010000b526480095540c6d002c0c2c8075140c00c82c1c100c44200c070440c1c0d0007407805840709080a0700c100c81c0f10300421181820813000c00c40101c220701d10f0080c0076480c8000d500c0b15107100c000080c00030000003d452250215a02441451064108030032449043d0a40814100302041a01c0303090095010341c000200a5542c5800d558044100c440d50740d125104411071103546407800e10003030801c840c4210080a0440056120f820103050260804107180d40900401c0741c00030010341049000c0c0a210010740d88103191041986980c0307400408603c0342d501c018011035440c600051030000020040300800d07000f41c040d000d0528110705000103540540e4042d190 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 283417131 1250 283415881 283415911
    0x40f021e0c151303090602030a09030b0a1104150905062104030c061b02060603120f03100909060225020a050d1403030c04081506100309021906050306030d08100e 71
    0x8070700d85281205200300207012040c5503000f000d160160403d0101d411480466000744907100c0b07200c2e0441181c0042e20341004250200343c0e83c2912fa003002d8200c41c1449041d40c0c40215001611007034801204080a210342c0341c02d051207444406000142c0280c0035811032040402043c0e1150300e49860003940c21501a00e030100f0321450607190310341581c03440c08600310800044080000001d90600c01107400c8035044000d8104605a02e4440020740130303106210001100000208060314118038443d8014420604284200324080c04c040c002504481194100101c5c0002000c44080460510190b580d070300400c1c6640785070508052203001d03916072908841203503c0c51240303c1028010801765110304501c2e5002c0303075560b003041c44c16821302e22000a600003900f010170520403030707503581c03c584209041c2901d0300180f191800c2c00000c020b2080015401d8000301003002c0840d20681c8000114880c803025411a0341c5c2c01078030030080350024422030340400c50301c1c2440018840c0c1e030718a003c0c95070000003000c41c0000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 283418381 1250 283417131 283417153
    0x10e101109090703140c030702070503030c030403080901050c0f030405040c0804052a120604020114030c030a020d090204020c060709080703080f131706093a090b07060605040f021e0c 80
    0x83d86042c151a46d06100d030001c02080038a0741d042054002606041d0050743c2010900b0300702d00d0313589c0550701000348070f540045190505039120340b054a440040e4082114200004251103036280c0c0c1c000d0007524050750610308158042401888854083c6610000906c08520100d940da50406c101c0e0b88002803954071181c111780d10340d54104a0034038207440240a4903260426100240003c81d1914152442904c2407040044c644d00b107200303803903100b0138010001d43c0c0c035402d005802000308a0104029402803010030f1707052800c807000408602c40c5005031100c04060340c0340d01625a4602c001e01c030003040c03400208142c1c01c040e08003002030003120302c4165a03610100e40f50500400301026151611405230311410410000c4841045910001c1d900309a062800d6001c0c42d640c00d0648242000c0903440080d902c1068040301d100380f8424005011541280c2d4445003135107042c202078405841164072941c00c1401c42802c5800902c211280f001c0380f0b80c0c503000410003e00780900305421001540300c2e00d00843c50214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 283419631 1250 283418381 283418411
    0x3060b101b110a0b120603010c0504030f1b080c012d03020706020f0304030c0302240105010e0316080a0c23190308071a0708010b0318010b04020408010e101109090703 73
    0x2002402c5498802c0d1703164080c4416040141d08028000d40c4030380c0c1440f0161400681040403030f02900d230400e4001103940d5903070524103400c00c8012003803040b1540c0030310009903a04002c1452780c803030b00003643c4540801c00d00c40c5801e00044582c42041c59507003215501d9400f124001e6006042c00b900c958805410300c0c44412424003950811201900030032080580764041507410700c8030042c0d02c0c54108000e6803c1031040b41545201c4030501a5905001c0f0b0b0480c00d500350742d020070042098400c001c600c030f0710319074940d02c10130b844282030442103d83c01030451000c1004200001000300807090181d002d011100c0c0d003010441100e214a030701603c0684440ca000c8041280c40300100b41c100c1c01003804401044544c000210400c00c01080c0340c0c10407501c83c0040c0241c1146008030313070f00040d281c18460005104901e90303030300500d0708103401640b062000070300081015040d00880d03202d551000030741d1855984c84642d4401d4502c6d40050701c01400c02002000881d141240b5625001101843c0005d80440545010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 283420881 1250 283419631 283419649
    0x7170c040e030903071d0705090301020d06030303060807170d1b080301030b0402130c0f1d03061006031103100911090303120412020703050c0402030a141003060b101b11 74
    0x4034075036000001c07244000d040801c9441d000300f010005401602c0b0700302c2035585004401a0070f140801c100040d243d00166000d4040d078800f00c3c0700e040300f0802d043d624035001c1e000740f555203e00c840c58010080300040d00d584414544800004d1070000d020075500d0050111815506861500030640c8100c6600f00401d0120020b1406544074030048000c9040500401801107000b07528940c143d41401c0e901d180c040d42c441241c80d2607642c0c03420718100c200607072140d014404c0d081d044401e07003502c40d440400a0b00208000890301300c84964504200e9080120344c07064562004850340140260000001c0268101c150700864805c035124150501302408140000d04540c00300403401c42d689016010b01050100007400011038240e02d0009120881c0786a90780d0f42c6621180c1051441960b02000191032080c00b42c1086d1400109406038091900e44803c2c241c030f5a88090106031940343c035114400d072050910400301c07490703800540c46005027002c80c402c1190950880c6a01240c88150902c450042c41d1505210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 283422131 1250 283420881 283420901
    0x70512071101050a02090d0b1b1215030c01170403030212090109050c0a140d11060a050316080c03060904060b1518040209060f07051203070f020c010206070207170c04 73
    0x1501c2503030803001031090300b554406003142e414144100804510303076440842c1210001c0e0301406c07041c1d56949a00d2210310025051040041601001075461054091050030303510610303141c0c80081d015070342001803594a1007006552408031715158811402d110300b426a495129200b0302c2c0241c60119924019030100d0004ea6032460140c2d1641d01a01c100041030119090300f503c10740d48036074441e25000c041005525414a07040c0180850040c7d1818003c03e92000a00a0000b40a4654549040000400ca5401141c084c02400080c3c909201094410740d01d1500a0f20040003090846d2261404c1010700c00b0301500072514555a4001032240b80c0701d4015500350301410141b01d54031044c0c041840031180f50103205d920b120b1413040280004a5a4141c00e03100321480c80e00a1548441080c5005840c0040303401d64006544070200401c00102d500c050b60303582e541210303425140c80400c0007006982d141d40985250000da00075000a00250030190f038400c8041c0e1940d412221165a194041400c9540b0103134 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 283423381 1250 283422131 283422137
    0x3080706111215040c08061201090f030e0a08070305032b110a1805060d09080f0403080301170a120e0103060b040e0708090a0317040303020724051b04030b07051207 72
    0x800c01c800702c00c3d00400e04410ba003041d01e0a0000700d11050009000301e4000701070a214000303001c914941700209610519401e07510018800782c0309a2410050301500c160200d081c82240d513a4004101e825000c121041165400300044d42004040c4100117010000300700580c000300f04503150307991703020320340d01030400d03c0901041c0766651410246401003d80c08441092040b060005d5010002d5441d0103085a84104006c1700004102c0c0c0d15250082440c4528805909142c002150100a000c85c00000b14100c459008008565050341e2410680796002c15801403c650034001601008a015241c039100e0140145000112180c8030f110350a81d9800941003030485901340ca0812030b54035000070400760003a0301107009000c0d096032781e54028001c03541450304140903090440403c040600070340545480070343c04040000b04041d60344c40c84021080f03107109120120308100c04188000c40750251580d1504c4008000d601d094116180c91520038405000e504c00c211041001030b60800aa02c10b040c01452156 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 283424631 1250 283423381 283423417
    0x15121e1508060709121205270103060e06030318030118150606081003060c0e0a060e04050a02030717100302030105040c0f0f060f180f08030901090b030f010308070611 73
    0x1d0000c81c42c010000385030105018002006000041d40207541c00e4490342e028651013400c10440d58100c640e40680001c000c41c48601d49021190300040340e901d044c8209080e03a0400070036030348420701c60341d401d01600d15940680040101c20301e01100020940740358035000e070010420100d608144603c1c10f2009400340c3d9003a1641501492812240c0145002000e503858800f4050a040020408a0885102c010715855407800e000c02810b010300a001070300c01005000380e014660381e10000c0c020000703183c0c1d80d5120341d1400001618000482c400c0e603000b03040719503945402203848604945035032400b804511085091950010040c0d509005d95480380344100f400f80c1450b80f9000b407915032603245401111040340c800754184890b0303034080c2e151412041540b6006801e6949180004140b410300e1300701d800e00c0e4541c0d24010070b240c400040280700d140c5003070340c500b20751640c1d036980d0b0410381c0010750b061403004900100400c0442c80c441d000d007802a00805000840d50001e03c0c1c4580280d2002c409aa4201c0d410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 283425881 1250 283424631 283424639
    0x180a150209030106031b23060901080a0605030706050301060f080f0606160602041e0602060108060406051e040302030307090504050c190203040b1c0b031902041d010905061015121e15 80
    0x20381c00042c0c8809488807110b1f25226040015103180100850705040016610019011041c40c0d00900024040030302542c03481625004010040da000340034800200741d01c0164801d20a1068690750b1050b00307641c002d42c00a8403041d04120060740003034005030b03152814a92860202d04544001c100402980ca954842c030500c03e110180c08940981c0180199001200100050308010422590050b4080c1c0002901d94139031000c03c0c2504500b640303102c4018140c204020806800000550046045849071001c1c281c1d243c0400013585d00480392541034000911005082ca0000305070400e520455006072424240c55028241c16030300700c1854419119a607001400303121541d40b244207850b00054000c5d01a888454003d0b550300c029060000307005a0760b800844050082d00100d4200700344080b002400441454144540d980e00c0a45200c011080c50f1100014101005c3c0c403100f14449268032056003e8604520190040000400c2d07030010849131554042d08a24a11480500c180542019401d541c14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 283427131 1250 283425881 283425899
    0x10081b16111008010e060d14010c030506031207260f1201090203040f02090405030c0f07080c091608100902070506070e060c1221040308180a150209030106031b 70
    0x11401009004a03414480b50700303100d62080c070490556080c3c0f40d5504242d158480480c4051542a8024040800b1507001d188110700c1900b12108101890f0f8040c00705848003020181c40f0030074280c240c01040820864200001c10a00c00c10422400e0004040300d02645200310500585c0302000d4070a100d10001100800c0070350700201c141c05404110411415403410780e40388403007102d81c2407001e4400d070140c0f0009070411100700201c8020840040c1540c00200841c188550765032101e001d03200246c050400c81803020b08214030224440c00ca4070242441d8036156580a550504001c2c18021131045000404208034900b0f000a250341c40c420b0303004100358035103408001c200c6503010800328030448041101c0300f4004e0b400103414041140e005043c0e0b50340d00b07207140401030300c100401100c0e00366160340c4100020701d600100da07139100340d03000750028090001e982c211507207480b08000002c0000c1e0907261884107602003640903001381000640000740756a00c03034655441001c00e03100010609203815000b0b0001d484 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 283428381 1250 283427131 283427153
    0x7060809061308130812040e060f18070c0b190f0e1b030c151b010221070c0b01030605060a210b130b012306070210081b16 54
    0x54000260585007041c01440040e42d00800001c0c120200102c0c01450f9280044c29800c0102401e0044512135100c2000074481500b0a00c0b6100c5115515000160b56050031034213032503003810003044101e016503021341d0100ea0741405004242001801e01680340042e0200e01060f000d04d0404c1d24011100c520b483e0741d40b007540c01d0030005078181d60502c1c221076206a40017a440c1070f02110245400c80382e803030072408a403801302c131410040c0d40090700d80e044500603607104006000030303040c400c544010010340d108201e00380e00c134144402e110301e2100d000c0b00440c2084200c00640001c0301e850030b4691300e080c0391941384d54050300780c2068801a5a800501400c4c0c50030f8400c1800a102e04071950f0320580c40c600000582c0501e0141c080c0030410030400044c00c90300140c61403010103600c061100741c1561904120b00e04030503806064103602030100c0030360b11180f900c0400d948100d503008240310714090039110308580d500d20260501400303401409216003c10215809010702c0304450a9100c00444035007489404a8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 283429631 1250 283428381 283428391
    0x1005030f0601051003020c0105040f02150a090b0714010f05160e03031c110403080a020c01090b1e0d0c0e10030c0f030207051c0507020909010e19080405040509070608 73
    0x3521045120640304808500e16044070001c4030200b10343d5003801000d401912407506505665441e290801c002c000041924140050094072829500c0314512000140751081c801d0710400300c0c101660401441080c2c0006040300e610580b20140c2c0c54055441082c01e48650068080740591600700300b20f03004404031035070310704441d40d03103403182d9210071540202c0c0d00c134818800039a02c2c900680c121883c1c044d4468100c508091082c013401599140d80e400d103c400b641000307003081f005000d0880500107541c403e1701407130199002c80d640b01d480d051004011408024040d140c20040c00d10038080003045014510407074132408850385420f8940c0d074005040001c00d007110f15400090510785020f140c0c2c0701e41e2140c00f012003040c0c5800c00691301d24080c101f081ca0112981854941c6950280d40452450380c01000360514900c01d03200001c041d118514040d00740c0b14086030000c1c0c42c0d800350b04080c0900e5031080381a08214000c1d00401d15040e200c1c0c0214040c0ca904903200340542d48520800c20410b903101d041a03a010f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 283430881 1250 283429631 283429633
    0x115030b0a050f1302040911100206390a020a1514060d0816050307080d0e0c040e0303130f020909011e060f031514010609180b0d140304090c08100503 66
    0x2840d1070110345a4809035500c0107801142c0d10541f000400150684441000c00700400c106070340c0e4a1094001d5030760030102d40c1121080b070011302d442c40d1011310140001404900016a45000740800711a01890300074000701c20451090101c4180400c88020500c03200e52403042e40420300055880941807031201c054801c41c0a0480d079034680300030600000c00d40314803580a1201505c11030050500b10f11f03500901e88040c00306000066031544128484d4450b14500c0510400e0f580d1401c1040c0070001141d410340c0742c611154004100040c8603070a00c210010800d0b00c10f81141400b020281c02044d03201508440005070f0341e43d01e010003801351041c11010700c0032100c000000e228040c140703484d1001144c0035210060041907080305084803203840c0d8001001c100c9820300704106c0d640e91340308001d1402c44c07184140c100b121100320058180c40c01394020000c219a0250602000c1212503981c00c0f4070011900c0f6425035030005100100c0e0035500d901605010740c41700d0b55290700d1400e03c02d130505c500b111503500052007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 283432131 1250 283430881 283430911
    0x1202190f060c121113060c0b0a0f0204091401060801121505060d0b040b0403080705040b1204060e0601060c02010801090501050907030b0a05100c0c0911030411030115030b0a05 77
    0x29004441903411654000d40100e16402c0b000e500740c840c00001c0c0000e0504a003002241a80c0070440b1000c1c11000c8648141005040d40d128001e4502550301300b8060b181089940000349050041c3d00300341202c02002000525045d5944802001c5801c1c800010111b40b6050004010b0705612801d520302400d1540d64102407070380d1540d80e80c0d5100c0c3c1841c0b103e200b080c0d00c5400040ca035603a03020b144c03141c00360000c1c00b040b442d150a26248850b600222800c80c0843d0102c008101070b40e1141040d2003c0c2c0b42d801c2a5546494010481c20f040c20300028000c455494a680d4840d03442302c0b050041600a00c425203030b40320221582d10000d04404d80507084800401d2620004000a5880510264104083c0d040c001881080c4a001c14080c0402c0d4000c2e51b041100c103410070050301c2d4401e1110700c5142c09080034101c540d48660440040c0c424003951007180c1c19040c400304021034107480c0e0050440e1001000090301003100c0c2c40566441e1160b134400e81d45041074104224104005004040d030205562405100c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 283433381 1250 283432131 283432133
    0xf050604061d22090203100c0f14131d1b040306180c0803040801051003020306070f0c06110d0c0801060912080c010504050102071e2402090409120219 66
    0x61020407203980e0500928180100955071584081007501c20031020300d0015480202d801c81d0094600b00d44100e001c6d214021040307c004a480c49460a414040d07501d0a203d074000c034008860400500341c101d001c8081c00c001c03581e40c0c00444815000104440281c101c80d1940440700c142e08000000d15041c0c10840f2040309242e07030980481110156540281c00154440301c04140030b100e01300400d0001c01d16514440081260030002010b4000c441ca008004d01640d40e80b6500c40102c2001031200070b4041d403200d800303d0122402210070020400303003413402d140d50244545440064652004e403d800c0c01c480000c0601400800d07006100b01d0388180d0400c00710783d525040c0001d0005200784210310403c4003162400041041090481302011050b8009100c0d9042c10b00340b541c003e501c504012147c000190440340c0c40e000b0400c501d14081500045040340387c0c1d1002e001e610b0806400c81a00e03440d182e00b0401492617607124401e80180d24022405410320031202031004c0d207400d2245e04a180300184550b1020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 283434631 1250 283433381 283433387
    0x30206061203120705280305010504180f170f030103030f09060c0b16030914010506040e070b0702131b08060108090708030f070201020304030b0c03160c080d09020a0f0e010f05060406 80
    0x1a4000004c1d00e030a40e510200b8151041040300a4000094161b08000341210a036a254004905803001160200041034200d40a01600c4106200041503100b146240d103001c604100c12212140e04a94410b51501241c5c0000903c194426001280410000e2000c1c0410550110180d800351009003450304ca61003907a203035542504e6005214071100024124516040d510036009003800651005410952180302116503000c0c0004444450207a85042000c001c061310001d103d00854204405480c500310790354082c090074002d80031610349110340f40c040103041e006100130a104800059580d8401e40d0600c1000180082400360119004e584900820300c800c3d0408021034906068078602d40b550349285200603405c2d800b4952010f006007500c0420000c2a03002000158454100c800a0301d8010820030740507500b140700510b0187c1415403d22000c01040181d40c4030f0715845000402c2d036015166200c0207841c3c03806450b0044c240c10030051004020001e0085a610047c21040306e845007400d040100003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 283435881 1250 283434631 283434667
    0x80307030603020603010b0319091e03050d0905060a0507030209060f090105040e0a0b0f060a0e0d0516060c0c050d0f1b0314100501050d05190614100314010b06041502120304030206061203 82
    0x1500be07490090280a0403d40074904075400d007200c509041c0480c0f2824204070b5100c3d00d040303a0001d485410b140000d0080c5100e8421070700c074860002c00b03060502d40c9400210304160007410300507051001c1040701140e113031843d40c1401d01c1101008030101d0090604d0042c001000301070b1444500884050145d0051103401888008203000159210420b505550800d03c0c41e00342c190942d000da400c105c0d100416440c1c3c0c000110045140100b0900301040c3d0b4950038000d403400e85d0180a400b1400c00030001000403441042041c840c21540d02100200344c49841f1034041882c80703400c0803c40d502010251510600034043c490042604651502c00001540c4500c0d4403080c2c411149136045148148103001c010855111003517203000002c2c8038860b8642103809682041e0140820b9070b001c031409010841b040d205001d01c0c2804c6001409883c14503280041440203880810038a400350701a150040c04006d0103000610b100707500990061141d41002814048a41448400c800c40d64208000364626800380c1651 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 283437131 1250 283435881 283435913
    0x90f0501110a060207030207031e03020309060a030905070b090a090614091306050f250f032d0b0a080307051f06080a0506180307030c080307030603020603010b031909 73
    0x3441c018081ea5207410b1440180000780784600c0800c021341415070008184c810741c1d2007417a526010160348165040c1c40c4902c0d1200800592003041005071700c1c104000034203240c44290502043c40b200940d170b2103044c50501d400c400c1030814007046038462483c20241c41d00c002e000003442001460300b006d0241d14a80211304480d40100c0b07991001c1183d560044500500d4250844410030031402d2044800310b012006556440c410180d0035003001181411a6600d408045191500640c1502050041d07028011605045c00d01c0008030b0145c880d80c0700211030b04270980d41d4804000841d51261000c210540499401c82e42c1141d1040c00014002000043c50b000008007012f0100381700c0c0648003c11002e000c41d50890a1140200601c07002041400030360741d4055640180061191071100c000260f03240101c440140005540c0c0d0b008501046c809001190400003034a40401d00b0f035241d402041440d170003a0f228009881c00003003005182d0081c1c02c8040417800103480180182280ca4807103983d01000c4402c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 283438381 1250 283437131 283437137
    0x20303040b06060405090403080405011d0604150e1f110901021f020927071b0314120108030706060b030f0c092d04110415080907051816090f0501 64
    0x404924140e407400c0640b00207050040000c582450a2324004140702c44c1035904440315800c054404445121001c0242d503074514020042006a481c3d885441091310f4158660786c4450390741d0011084214180065001101e51420840140007a1240716084400709088504030407001c0c00b0300340315aa03012030100444e107041030b0701100d01c103400c404000080c481c9101d0325078041e10308220707480c455a018400503140d803103100721a480e035030f10070300140d45006407400f0904a400000d444000000d014600c1508c3c00001d1a52440c1481010714080750034070002e030051001a480824201e0400c00107014032409050881e45250540c2004052025668005003a40a88540200340f01d001a200ca9038004c0d28800d080014519029a54642602030025030413070901981c2003c45a05095404800316411202c1c0c0418a61160301c2d507500c12204904d000c1e001021320300881000040310b81e1134980c400d4403519080425195402c140181c031424a02c001c0400d014441d96010402161402c1c2468604854082c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 283439631 1250 283438381 283438403
    0x90f030305030f0a27021f0801050415090509070305070603020901080606070602090a030809040c0c05031603020a050303010b210601170705070b040c030308010b0304120309030c2307090c02030304 86
    0x101c0901400c002c591018854940e82c06021702000b41c00114441d6500a40b0000803d465451071604c008442030303c0b00c07001c0782003600100406c1c149030b0300c00c02071002c100d0032460503c2d03211915076003580c00a49614503694000070060080c00414041c9000510146c1001c51908015400207403003c000101418490740c404507082051100725011280d804000070068544c0325102e1400300d900b50032203021b0307078052451304818000c02801500404040d0750084e0003103040004046a0040009200c041202180102c0c401000003610420145000c1d103001c2c50000d0303e510050020901200354204040c580e43ca01606115444e600407404540140d8400c0c15400036903074804050310b4912450b440108120040c80c2004103004000c0c1001c41aa0310a540c2c0c407520b039a0f079105000c00c0b0302056401401c6000d960f148a01540d000b41d015201c1d840c841c0c01c08505c0c1180c50344484980001c5200380100444100c00750020300b031024000b60014280805042090298100d8003d54078000200000c01e012000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 283440881 1250 283439631 283439641
    0x50c030c0c010f09060c110a08011d0c0f0d0602130f0605090f01030b13050702030c03040605250312091e0311300d061e06030c03180f1106160201090f030305030f 71
    0xc1108c06004400028400500080f02021507503c403009411841d004640400d012460120400801c65000900c0c0300d901405d6511000c000307502200c24001c102e211080c00041d0380702510300d200001c002c00d8403501e840b40040c00500c280700280350360301d504251420412101554902c080302104165146000915603100c5100741d145100e0440000080d01c00480c0000d00d071a4490020440c10b0350300889041080710303800c000394030f00c401450010b01060820030030040c105066813060b000e01c2c0c0a0480001d8800c800200b000001b10182d2080c0c0000340300011590750140100100840310340c0c481400711f03806090381c161032103500b140e0b06080c0440000080409042d85c0f82d0b003200c40940101c5200214040076070038003408d1000244501c0002c00d06091340000c0d200e01920594602040780c0755400130360326480e610300d1228a42c42c001143c1207000c110b281101a15840050400034091480044c0003185500015212200690160814041444003440000d9101040e40d42040c0151141401e41e211 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 283442131 1250 283440881 283440889
    0x180f060a0302031605031236090403110f060c0a0e0a08101506020606060405040b041d071a0322051c024207050c030c0c010f09060c11 59
    0x12035002039418130a41000c40c07003002e00c0e003100700d0440b001202221034000c00811100c016020f18030301141d0710300d0030316048440d019680710003102541c1c5102c20104649508400034441c2c6005403003d4000030080c500d03054138a0001c00550016180c050004d00d210f00e0052541c648503c101201401008502400104a41c44034409080903006441c03d0715100a1401d25141c010000c2844403102c0c42020100011003c7c004140f0030302407000940014079040c142030910000d004904412038126503506101c205400071140882113860307084000e02021840c201c00c0c80c0b20b080e02001e003c03280040410900490720001780c82ca200080c06030100d00358061260400d182005150f000011151420900d02c41c1941d45c04120048404290458044a0400d05042080d03090800441a912903410841c801240d0300d84030445501071800d181891030100035410341da013150009a0040a5540221a140519030304001144400c083d0b92404641039490108010700e0400c2090020341010b4601c1c50848494032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 283443381 1250 283442131 283442149
    0xc020a030230010b01020607180b07150510080d090f1721031e090a030320040b12010603020f030109090302030d050126120a08091e030711180f06 64
    0x810300c02d080707600040c00a0701810f00740d403c070350042c00303914001600d080c02000300c90720b100d00b000421442103060000181c0365601c003034019503800c0c9900010050349440c40c0101d07846840c11546601080346020f0800703107801410100d0b4418843d01070000c3c084501c005103039204403914120003101c00e03481c9001c0c66090144048220354400050906031010091840085008565050780d1054030541c811446403510410307554a62540c000081a40100e4441d41280e00780c1004074980c507480c000038680b4007246903c40e17070100080d15400b003000218840321034150b90040c01070341000c0d840d08a076020b00300c150788814052801c0701c580d611085000d16108100383e804203c2100c0e4104120b50f112000300c504501911031803483e1000480e850213035040701255510001006c9170004e400e11400101c1581d050400401088007845890300143e0510070500d43e0918640d041e1010715a282c02604064002d10300500d0400e000300402c0c88243c4001e2940343d50141d0000741d580680006440b0740001604680d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 283444631 1250 283443381 283443439
    0xc020f040609020a0512010801020a1d030c0307060f11061611101409010c030b09161202070303021201090629070b040506090d0e18250806010f0c020a0302 68
    0x948007186810784a504903000340b61b080c840507011a42c0c0d81e40c4999150071f03031190b006880006102d00059112421007a01e900107240340013000c0c0ca80405000c0b022038a4801d0b04d41c000000101c8156840a0b03240d04a068001c8811208016140d20714003000e080d005616801c01e4902040320302e0014910b41c110503c1200c920020244090114442860b94040e070080140c0e080c102d0355280c4101d413010103004e4821944903250160600e20195954074074901081d2240140c031060001e4820944650302140c030050028a05c40d031801a25003c020034a418103480507040f001c1443d14020080c0300304403581c180881180305192000780607584403680d0304003602684800402c41c01c1144244400c000b4045022441460003400301d400045441104891381c106074003c0682000580c044400c0310304039000041c0d0706c42045200d00700c860340300a034841d5501e242d9030080000114180309111041da4000c610410010f40b61412a00d00d45254001070305d8501b16200091041e056000b2007006c030700072035060114030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 283445881 1250 283444631 283444649
    0x1031208190230061807050418060303030629030a02071203060602010c180504020915030a05060a0b0c030a030f060906080705041d070e0402210c010315060c020f0406 73
    0x205a00150003000260f102c0c2100c810390000108285801041c1009900c40d880080c014011900300301039500007070001400d0711081080030000802c514026010110300c0100c0400700140292442c200181140c20075000a0280c81d007030704c3c1414a141070f440000243c184440c440a541b41ca40b0107000000740b00d68000200525030721009100c4080c1c00d680540c0845810790024000800c92400071035688141e0004024175100c00e40003441710b0300f0542d02400c10600c014244940345140d08503101c040e9081142c0d03d030300084e118403c001040c14a070b1039a00091148605440c102240d400c8595140d010303030404001090395480d205803004005412840040002ca80200b244c2e92311041644c1e26280035008050095044c15a400c0340c421548100412609d1408007038580e09003058001d1011b0440944141da2000001d94041e000202a0f01000c1200d45180010000381100c0e00003d02a02d030140902050010318150402c01543c2200404084d10390455010000420400c00900141440e801401c0300d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 283447131 1250 283445881 283445887
    0x3070b130b0c121b0a0804061107050d0905040b0f04150b0310080f030403020a061808010614030f011a0f041410061808070611150f0a14010312081902 66
    0x2c9031881e00000c001c3d040161032055401c0da507840310000700894010560780d003031100700199490a88255080c80d0898494000400c08030000030440070240c00050041e501900056100c649054000b50035a008103401d03201808083c083c0b400055000d40ea0021050207152200420141e001e900702c0c501010780000e07240d0a41768180b400400400082c2030007204100e03c103151280c000040c00006440c00c881e4010719445445081c040100c0c0d403805040c050922040014101142c40d101c05c0c002e903c040c041c0c070308442c5e4034000b0800405240c041d4020304401c0c9039152040c00303040c417541000e160103500310544171303174030000b002002240c003d1032000080120920a1000e00198003800c01c940b00031513905643e90030f000ba81518404491078000d10130388003140e00c4030204028944c003030010100f103607558030151800000045400030700348004131101290580d902d81081030400c90b034401c2013400028520085015815643c0315003c41c09450040d8007400042c50000c0da411f20f01d5100d01a2903202c4201c01e5403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 283448381 1250 283447131 283447141
    0x50702041401050a050316090b060c0f03030402041413060513020a0801050f0c0307050a1b0204020d330e130c0e090601061407030c0c050406060c05150103020303070b130b 75
    0x4030150a004440c4542004000003aa903c1d0000e1410a1840005884122a450011094009d08691001d00d80103a4284402149c0b074405200d02c10070700c1c607400082d40c2da0b4030301841003004540a070407052010480f03070810720061011100c05c4e021650f5100c040003910307071220100080030346100a00258024400711003ca41d107901908000d0142d00e00101d150f44d141c483c080203011600003101c000340098414042483c64a2183e520307000926803401d01c10780c2c04080c3d50003140580c2d010010504515407a841200702001d200c508051b03a1141c100c4444105000a03130003101e0740c52030b61042c1004c140e0500d0100e00b45c102400c00342c00d9401c4d40105071408240d0741c0c0590501d20001150b0080f154001c0d88000180640100c4520000c0c00b102c804052a264140d0b0701078481c00402d0009840c0c895004801040c0c2d0303101c03486500041d050135100da00415030035140142c074042d810110000100c60307010040006807000070584603110b0703206078624059690968034814003140314070007611042100003408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 283449631 1250 283448381 283448411
    0x70f08251109071b030903080f09030f0c030a0201030207060605041503110f01170a09051b0f0301022a0309040c030e0f0c0a15030b060d15080d0804060c05070204 71
    0x904540c4180480d0003484403050800204020442d403080224078a8240402c010184131200c82209101c0d041c82a1855166210f0461940010110785002400054946d000c0c0ca0700b0020503080c00c000c04000c02e045070055020076298000f011009042c16000304401040002640003034002c3c0c10043c2c401c2090070000d0900e848100294030068850f090f407103910380310506220b1800503030080180c40740107500006c804207601ca0135005001c580603d03600c440c80000980c040c8842050083e00340c48221a0607031410800080040310580c1c10702c00d0f0720400c0080c641c9020101603408440d0750b8135a44224100d00485141148140811941c0c1f0601c1d14503000d52003901540501b10103e00e641c2115043d58100007510350b510380c4800810b50200c004042041020410300b45528000002c0c0380225a01158101181c2d00e50400420034030f070702da07c0d480424140c0080c120381400800c181402081400040c41001e44103140150001e40019103c00542c05018080c0003101c1500743d0180c4104010040a1841 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 283450881 1250 283449631 283449697
    0x1803120f0318290112021c020a080d020d020703110f01020a060c031a0f09061306050405010315110a0e130e0d0914030c061b0106030206030103120f09060203070f08 72
    0xa54032002c1c140a030030200d10301d1030314142c41c40780c417100c064085580c08011030041d00e00a0712524607503030004a80107813500c6902c3c0f401446003400030070200d440001c1c06030a14608404940841d88582020400300f12050810080034030103580c0f0848009420740100d04000b1414009042e083c1440115030200f640f5502c1500415150720111807a400c00c41c080042c5d448d4400007031544140840b010a1080c6801210f20200003c4070a00240d03c0d90760b1400725040d106c00744c0c0142c0d01589010802c0620ba00701c3c1c05101e015000071240d252070440c80490141004000032001e40c01942c509070185000103555200d401e031568000c040394070085e40050001c1c0746610b24060718840c01b0104092000302d040004841c41869002403509050403070300d0749601d800d403410510b069015900d03904000090781fa070000440c0a14007030f42e100b01039002c10100c0605100414080c03001081003101080085942c040140e4080381e40c0004240c1d5491801e0420786454010001002c06641580c40d440120582c0d04880e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 283452131 1250 283450881 283450913
    0x3030c06070327030807030f06060e031902090f0903390f0c0f031603030206090d090b03060d0c0504051501020c030d2a15020a1803120f0318 62
    0x60000800f035105010000000421040020a81d2240300c40045e0003501d004e03601c64803910740040c1202c0c0c8220600183c40169000d000402c0d00c901b800c14190405000c01c840702150403411148280d0750354086058074400800c1c03010100035080219005c65002c1c0b08840c804102808613000c139810984208100413a200c0700a0252050810a1184031202084030420416000301408180c001c540502c14580c002c0e6045a038036002c2d965046200001d401c9243c0051070080e40200341c4c2e4039124074420710701964000d014090100505c01040544000c3c021a54040803d448c00e180813003480c94910840f044035001076a0250411040103007030b18880e941c06441031001d90071203403841180028135486505c2204202c0001392002c40e40c40c052410300525098610b51000c0403942c205560f258032018031600b007902da020640005a11134000d602820040301070052076000300c411465a5142054603e90314100300070b224020b52a0107006000b80c1c803081140340b5000b04910081210b1910302002d42000003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 283453237 1106 283452131 283452137
    0x6050a020c04050a02120a0203060904030c02180c090301060b1804020c0f10060504050114210c030a0c090518070b161a060a051207030f0c0503030c0607 67
    0x124444c8507680409005844101c80d41030b003c1940805042c1540c880d00500c284001d40d550b020140b50403684c5810000500440d44c404035100710007070348001c4000b000700c0c2d00300101c10000f10010424114128001c000060306c961a0003064095190301107841c9010346a02506d5051942c0140390030307443c01084070b06011254071403078603003122003540f0b82020f034440f038003084141058042c0c64050000c00740050010401c800114000c0c1d44100581c00440c158184e49180ae54401d100c2c84113400c202a00759030000e03040e0704260400344d09600c80c501c50185801c2c000b5400c2e0b6031400401b0341036080c100150680c24034125688400750441c400020302c0010715081d5000040c040f10061016680034481c2d0b1031a890210100b21800300d880c2c3c8201d000c3c1c2d0f80e510000c0101540814080d0959a10429940300c40c561420078000c03407482d5801c0340790540300010fa400704074407002403054401c038202d41d = true := by decide +kernel

theorem cover : BRFrame.Cov 283273381 283453237 := by
  have h0 := BRFrame.cov_init 283273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 283273381 ≤ n) (h2 : n < 283453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
