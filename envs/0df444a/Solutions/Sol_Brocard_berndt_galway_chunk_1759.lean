-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1759
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:34:40.495111+00:00
-- url     : https://prove2.me/submissions/309d9156-9f47-461f-aab9-7530126cfb9a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 316187050 ≤ n < 316366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 316188300 1250 316187050 316187059
    0x80609011a06070218010905160c1a06010c050601060201020301170703021f0207030b01081f0504050d0f020705030307210c0b010302012003030a1a03031e071a0f06030c06040e06 78
    0x58100c01e45d01d86400083c00d4403120300d1250b9044d40d48500c543c009100844a4440401f00d00c84200c0090b0701ca0f954110f40b440d000342d03500460354255400c01c40a0b21010300b481d410300520303881180c0015818008103008144603000180c99603d031442e8400c0c014010880c010098100c1d03241800180d90300300da4141d1450700070144101d4040c052000f41c0c40c150283d0000ba09281c0e400c400000c06040018007180c0103a032404400702d618034103070f00300c9084e2070782035a005003581c01076070b071100000e4411880c0d002c461005104a4504a507600d001c42e040d0f90203510280e0b40300150500c807130545400620801c50113203841c40d02501092091702d80c40c400341d1040c007009040002e50000841d0301c4080014041301003010318190703542d9081901c01d2000030558506909065181900e940156180200030b85010900000f101042c503520307035089091641c410141150102d034140c042c607030458510ba402611501e0440d072812000d00b040e40400d031a022068220501c50781040100b40010803d50f1051900001e0544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 316189550 1250 316188300 316188307
    0x1504050718090f141f060804020904110402220f05121f06051e19080a0f0203240f06090c0f0a0c05030a05040e0a0509070312050903070f080609011a06 66
    0x2041c0300e01800c00c08411042401d404414000700c9140381490b00e0440990f10021140207a41b00c1090390205402c940281d801440d0400007004988504090052480010001490400461321060100150031437600d41d030184010705100c42e02130503032a00040c2c1403c5846452414000805a640c1c41e0310b116524600c0000500340c2e01304041c142c1184018200c0146110b0000d8200120041d000c2582c010b2184681d07500c0c2c0d40c10012041c0d20060005a81d401c001a00810509444844100409030000c0303070540b0580f01c00039101200304d0084000c1ca80d182411492604028811412040d4081c041610500015062010304141c081c2190011059400201d80300ca10321081590000c014100240240c000016150310702c951120003032040d00ca080c6600340041e112202c51300c04a510032200040700c0d038400502440415a00d00e8158800c03061440c01614102d40c040200c0e00300265a440324600818001c0180000001840803030b602901c80300c020441070641c40030402c000c0c00420101c40c001c60001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 316190800 1250 316189550 316189571
    0x20a08161703060d150902030a12030b300c1f12020306030303040321050405011e0e0307030309150c080103060c05180f010309140a05070602070b0a1202090405150405071809 76
    0xc1c5c00421b1540d4000f802e03120590308030f003001041140046903900000746416521015454441a0002a07074000b1419220014101c84450216500d0300c03500034183c800c0d02c0828080390740c1c1d00981c00a150322903580395084a100c00c07026085580036200080c3d518018400c100e07064400009403548030350546441c0d03a0340100300700c81900342c41c5c0480801c00c0742c03810441003101340300301504401080c14408000c6615403081c84840070481e070b00080030076880d810030030034880840d110741c00c055403c60203070028464102d030031030741441200c08282d000710104480e08010400c0c024076210328418451a418080d00e41070800392400c07002c0564102081c403443d46c0d03501c1481c20380d01ca0340c806a00141e0000342e0030609144958466900c503803e8400f01c1761485204404901140b0100300d400440d081d030749550f81840c03110402601e10040100841541c0d542c01c2c40807820700d540358082e6502810b1207848007a980d180007010b11007a45d070010030800c01e020740400456103400d05003405200322210040d002443c00c040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 316192050 1250 316190800 316190843
    0x4020904030c060c0306150e010c151107060f2304060c03240f172a0406090207110405160503060a03051e07140108010312020a08161703060d 62
    0x160a40030f40001e24181ca442441605980607405480d11200402e900f0b150f50242100c01e8504d4030641400143c032200840005001e20421100f2002072102c00700e0900d82032072544d141d0317402108007a0707000b0361107480d4070151680c0c61166141050885045080e400b4502c1710001c5c43c0c5601620080c0500d07581e0a0300170002e80300303a014954030b0180354052045c50400f00d802e40c0c580141c0e802000d5843c001d401d000108203050070041941151644098104440010b440d00241019015041030303540361084088006d0740e49120700c1c0045d01c040140142ca4040c0d42c140b100440c1c174524225805a8039100500262800d1241b45032007a407614604280d4a42d5480c001c100101200d5100030314900c510621041d15501c0d00c0c0c00fa01000640c5021209002d9071240141c0e01403c0e40c10740c04e401300750f0003401030001c11810300c2807242c01c100b2801100c0c00c000d03003a551000310364403200e10308000440040100c410080c40008501c62400104815411070500c6000150550310945008000e1310700c00a04500e10f540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 316193300 1250 316192050 316192067
    0x240204120b041704080717010b03060103201009061209020a230303070605190c09180e060106020313061106070e1801060e04051e040206030703061707050312030f0402090403 76
    0x400d4400035100c07952a42e4a42c1e1b114018015051244042d05007552112014441d012a40100500421a6912b1034564841036000d0121008010700c04005980c91512000114002c0910301c3d65a00005441c1100041c01401c421540400c09801c1089140c096980da41030f03402611803040a103c0c0d1007041c0203450013a154204a600d8041c00081541c0c1d080c8003203a030100d44601c1c02c10420745000c1100300a1182214115401400441c1c0b199406100820140c4200d100c040d184034000a90081d90714111032409500360300800040e4000214441e41c440844d00880003848581015044a003410309155140c2600410a004100720a89010a50b1381c0e421040380401050031200f03981541c48081c0103003114682c000c02d40c042c0b41081c002c42c0040034210596031080d0200d080781141a1580c2c0d08116080d4005401074041588032074000c074940702d840e1b000e05c000069076001400c4581c90702080c035042031903840c03800e00d5141c0c00b0700802601b01d148402903541705a0441d5054601e949600c1c1c01c0c0c42c13615 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 316194550 1250 316193300 316193333
    0xa0c0b07120911010306060c0506040807030521010524030105131404081e090d0615050a0b1215010516030507170c16062a02030a240204120b04 63
    0x14200140038040c0864516100f00021083e42c080c00350586581c01070302e0001d841000100140d0008000502248061014026403440381c58000d242903504a81c020502050481082480b500c50004110302d242c0068105000c1e605c9991010369840e41c808074100501051151500440e080880120040015417100d0743c081040d100040f0345003070609041304a034018030240030a1007040b81350a030b4110b22003000c2d00c0416000401461500402e55070340e8000e40642840103000312017250002c1030a540d00040040600800c004280e21071948408860b80c0000283c802210381c41040300c00d0b42c040c0d81c00703421100315284966840441e80360303078a002c5440d449400000307803e98005440005a00784440c3c014814a0448400c84410503400302609504d5221881241e0104082145030003889003280b41034100c540384d40081d03045500042d0041307400c0c103648520440302d2000e400596810126a1135251311008550541181054140000500d02c1c010f00e03c805084280100e0000c0c04100c112403151529a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 316195800 1250 316194550 316194587
    0x607060506030705270c04031709010e040c0f02010b060301050108041b26160b040915080609010b0306070903020a0b0c010f11040f05011403040b0601021e0d090602030a0c0b07 77
    0x42c4140c144045480c2ca40013080c030b401e10307140202c0c00e0106c211080d80c081d82d402c5014001c0543c5001d030058444da200300d20040c1400080c40c1640b6096646100e88010303000c103519000340c8040c0758107009086501d032520712407144801f400140041d0360b0183c649a801980002e0755481ea50b40c5403444880d2404070352211075113140d108150284035000f00c0340c1184038440041291091080d1001c174084172a280c1c012074400c50000d200402c44580541c000c0c207514002ca0b00a1500c15494a00c00703420004100c0380201c803691281600346580c24200000e5600041030f243c1a40340900303540c001014800503104001004102180b00380781c1050a60080e10b440c91480300400c6020990182118590428415600010050400058075501034000c10034003200803420030b45542e07070703958501d00c0841004e01450b04510071040705c200031200020880d0081c00c0e0440042034240e609400c010000507aa41104086405c1031007070000c0603800180f0180350340d901005000003907407902400c54070050210300c0000d41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 316197050 1250 316195800 316195819
    0x80919080c011a130e06190e0703050703020f120304030602031e13030206090c03060402100504030b07050d0612052a10110708061015030213030821060607060506030705 74
    0x81d80600c2c100041c82001a00e0358900300320321084c0c000484035041102a642c0d0040320000308220722000900c0f071a20007841c00000c50a40703040045207088042d42080f9400c0c2c2c0320040074010351820072007010350ba00049680300c19240243c40c01c19280d01852000400194010011442d00c058400043c1100c21038100300031000e1611008240d403482c100141540035000f031401007000621302041c1c610345c010000e0700170103090301c3e9607091180401c2444000300412005000100020b60301c0c090319401040107903540b81e140d54566419808403005a40503104604142203d2400610041a0326031341c0309240c405540d6003081124400751060381041d213035030312400c20088041c0564010156000c603d00030411111001c0d2200c403000e1390f0340c405442d41d5a031103400b02c0040141c944130b9400b1015101c000c3c9005401c040c00b018040641c0445500200c0b80c0c1c2c040810b42c4c51510028142000019403440c100c00e03554100340012801c14805d0080280145031208000b408603141008100000d2030058010140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 316198300 1250 316197050 316197071
    0xa0c080c0c01030e0105061507051005070807020c01020109030c06050a0605061b1903022d0a0f02091e0613090512070c08070609060e132901080919080c01 68
    0x4039a1200007140b404240303032000c80e07102c608052280d207108802c003505c0c10307205c880c024429803d40e030880002203d640c440c81e0203100240d00a4004d150003044e0585070b403c064101010080e0801c0c0c15034012a04583c1b4062140d40401d900c0344150000a40280303000440392542c420210141c00760360000d0b1b400400001d00c000c944e0b051004d001d080c0142c01d40c1690b9008a2003150050120a0b00e0b40180041e80300915080303110304169041c4ac10352068450b003004100e403403101c0604000008100755000d04012040c10154104004210390180009c100c074003a901401c20403e10a08028244a000c0c40c240c00348841c02d0007542e4840c51038581c0101c2166146245040f103000d40d944080350032200503900c86800901020b000410341e003a18040c0d125035022074140f580803a8924800080154170a50120390800507140368070400c02d0140941e82610500c1b410101c001c0008504200114100700c200f40030000c144e03030301044200860700940e0809030b03004100d041554040c01500e1680b03006501e805032580 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 316199550 1250 316198300 316198303
    0x1020c010c081b03040b01051912030c020a08010e060106050c0a0b04060203041110020c0112110a17011a0909090a14030c0c0d030e011110063005120a0c080c 69
    0x5220b01181c14440910f01c0500c811010a4042a2002000c1d0400c3c3e0b00107000d60303d00682041c2c555140300da0aa24090307612032055032403120000c0709402054004825406501b000c549804c082c0410000a100c1a0b184080550362600148604030400101103240680400148404510141c0000c1720070349a0900d07007001402584140c0f012203401100108580841c141600b000d41c0020403500a410410072910055603811b00300004850782c190b96101d4044140c03150b0f000b0300032070842580c0d2807002d00700030210008001d0043c0c1014613651021340001d990701034008126600400252742109803031b00d444a102e0b03e40340d18001300800109c8403445010300002e0010250002d403084c581102d42c083c0140c0e052000c1c261020301c010780028030020440b140e55000d4654a0950105141110884200d214035081119226000100039a1501d204d00c054402c861162014031901b03a00740210400690391055600e602d0800400d00c1c046011900d490005d00511840d05a5904070140c2640c541408181c02e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 316200800 1250 316199550 316199567
    0x80f0408030d0b0d030516230a05060a050907060c050f071707150518010c0b07020d02060f0c030117070503030a03020931020f0d020a0201091202060717070201020c010c 74
    0x1801c20600d40f40311070700c080c03810b807090180e0f85801d45c650501e0101d030409908085e941d0300006807407004c5c80815049080b000003108003002c0c4400707005880d040e81c051403d58100030001d003511409901b00414042116000708001c3c04407056820b0881544105141250500380d14184003605409a204001840d0050081c0145099041d40c04c0d911039a03102c80c140401c05088107115400030344280004109659044824800004141882485040580e42d04499007800300c5812006810190035090055010803c1c0c5801281500b0102058500b107060750030700380014400c044032101101c1c03041d035070f645040c0011409440007a0640b81d803812082d0000d8042d6201c0c0d8100d85c002d4080c0540f602010a080c501c81065460010349071155103442503071040650852800b542e5800e008021101e071140c0340344010f0040450940002c1498020f500300001c94012041010055401a00c2000750059200300314140045a908070141c43d61508442240240281c101807445581380c00070905d007481e00403104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 316202050 1250 316200800 316200817
    0x30516210809100c0e010e0111011a040e03090303031617090d09060c02032116050604050106150912140307050c0f01020703020306040602030604021c0605090c0a1b080f040803 77
    0x1140d030f4080b4040f41c804212000c07501c44200049880014154541c861046400a01c40500d056405200c40c010024219000f051510400c00314014030100e4038240f6024151065030b085001d98200000c40004c2612880001c1c0440c180d1480d0300754009040380119014a042412502030081500c0d0150445035655101c405050101d81512800100d0b00d1290740b07440b003280c0c0e002c2e001e014000e2200c490441006a19607080e5500441407000b400c41c0d0b1410801a4003990103131f001400c443c100b904181c1d0840d0602e8001183c006884580c141006030065006d4085400c07601a400108a01c0e060810481210500d52405400300154080500c000000c002c00d06240849140e07403054148001646e46100e03610000f9010380240c0000b80205410360f0146502400c0684050f02d04003540e0502060800b001d103da28001e0342d0b501090126003032040c3c5032a8011000075100c2d103800c0807080c010707085d0065191002000100026000d0802c00c0200070b69a00c22a526206038a0f0f80c1c450f0b40715034581e0041c041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 316203300 1250 316202050 316202053
    0x40b0a022d0c1012020a020a06060e040327120f0308010b161e06060b0c0d0302160204020c0109060609060509130b0f100e070806011b030516210809 65
    0x400d0441000e00001e14500c80707100000904501c0b903484240282540d4031405001480700c0000400002000c9000070004c90320140d0160020b076419140c1442290700c9500880884400e000410000980100070940c1d540c2650581952629003851401c00d814116001109a00210b0a40100b003004444017400c0141c86502e03008096030b00d60305000702c030380503103100403071700c83c0c00c4400500200311040c850802072060b070400721202c1420340e12100d09442040c1d0040214190025002d140110144850500200705c0e03e01035141c224011000e60000640481c00780c81164005940460418258082c1109917840001480150340c0e95030118000e141500c10780340a5402c1030300080011490401c1070807502d900058200040d2560001445004070061000d100720120880126616640030442d500c100965568801c0d680762003000103041c10444503d00308000381e408103403070010750001e082d103c140078168281d0322101401c0c00c0040700c641038841004000a031888104800035409010b5a214100010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 316204550 1250 316203300 316203343
    0x204030b07110309040905071d01080706020f1005130f0c060f1107030b040c0e09010b040605040b100e0409020a030507090506061809040c0b190e01050c150606040b0a02 74
    0x354251104201d10500c803020f07410401580031685403c0d840b10702c0c1035000c2c0046407480c549a90481c10800c800405044900c8802c000400c9200e00800030040549101c0c03002c0e0214840b91030381d8aa9070f103400080c6403012034032200010310f03407044643e00c0d03c1d200d41c02504c1756075014114104611031010601608000505500710303005070501824448601e505007600401c44a403039034446002e030f5500a00100c0b55040b003440c00003038080d88c0481c403074001d00868000241c644142800c01048800a81c000c9000d142008254216a030354046040d010140c00e0074852100070030640018020488a54001d41c04014050080103000f00001c0b4031099400c1c50b01c0401198480d00c0400c0401d024041d441301d184004030065240609101d00c000782c0251041d80702c0101d5036151b4000c19540e0304100d034891911203060001115403980007030200e80190080c28107a103098910007030152100101c034410001c0384901c001207030690b2070303003012a4020010380c0c41c0a900c80507a000c0c025100c0c3c00f1090030344142003411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 316205800 1250 316204550 316204561
    0xf0f0a09150c0c0e0a0e1510060f080f09030d0e10060f1203050a260f1609050f0d0206070f0c140108010504050403021c0c020a21171c0204030b 63
    0x80c004a950560005000c43c1480d107451643c01800500902c42d40036541c440d118004140020022100e001c5034030130000003079260240400034060001d80c0008100928030402000294000d0303130031504500703d03500180b09940c414503034600d14456140c461000b10710306012403002c4140842c40300040c2000345824400c190390f4005a54007000c840c0503007480640204800b1000901940044c417541d8658180303c0c0b60401b41000804c658126407182e004000201c0341080a40d4200800c0b00c1e0740b007650302444041c581140440103081d0420741c060107001e5044906594116900c5903000180c495004140c80d07943c3d98940381c810701400c60034804440c06280588041000c0070b54051101550390181d4400700c2c2a8039100402014160103002076042d4020007000c002d680d03048041650a10300385840f40441c94480f48148444001030307134044419800e15030040c81c2280e59000302e40302e560350401142c092a801d0341e060781c40e46214011070011450760028041d0408034054014004881c001c0501008a0340c60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 316207050 1250 316205800 316205807
    0xe030d170c030115080a0f05100627140f030a0302030c280209070e13020322120806011e03090215030402011413090e0102030603071a03010306020f0f0a0915 69
    0x7070240e103c8501c85450341a180a20510015034480801b4602080d000042d40e444012102c00b41c4600b40c00090451040c84102c0d0080500114245009504803402c842601c01c5800304069010b0110741c810146070045055444507043d40320030034000c007a6100e00303406242c017079034035072001001011310b01034130031f03080c40004007500035401ca4480300c03107440c071001041e82c00c1040e41d4500800400510020001c0310285403140f4114040001050000681d01e08041c6016500501c95140004c40039200000b9600010300c4001101541d080b181040c600d01e81741d040050300c0f000f0b0482c43c10103103002e501d400b803096030798150802c01100703000342c50351200702880720200e000510003241d0190104240024500310001080300514071000c880201100c0300e9241e07141c090640d80c030f080341c001c50b0b43e4000c0700f484602d150a005620082000010340b807151060000d0415090005210180c5469804201c504002c8500e104959920a108c4409956a56103260160840e00180500340c4102540c2810039076803800b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 316208300 1250 316207050 316207057
    0x405061308030f27061f14100c0203060f0f0a06060f11010209060703030603020909070f03030f0905040903120501140607152304060e0d080c0304030e030d170c 70
    0x20400803851031581c4201219030310100c040e00c9040c144840d0340c032404094a02d0710f43d404d007014984015000d10704041c9a90130121203071040e080d1514948503010071440900074000c41820710299204001c00080c10019a140034030202c0c0650140078842c1000324002e20001d41502c10000c0d4101c4290302d0321074034100d40c21103009025807000f0425007040040c9080c0151000703a085001c1000140c038003000303400492078076044084218042510345405004624010801c0b41d44980e8510081041c14030301001121442060302c00501030248820311264035901ca1100207002d05000b030018415081d5a140003003a10803c2803088030501d15010005c1080400120f40c000307142c00c01030901e420400c042e12818803840086c42c003d507826558418490348180600744a0308680d0080c000900781d4649814480190351a1035075000e4950041c0d03036040c804a4016201640141b04401e540d516581d580c45e042e40c11003503030b00f0304607407510500c01504070180c0e00c5540700c40e80c01e0000d8000a001c0e200d2035038a101c64003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 316209550 1250 316208300 316208303
    0x303050903090112150f091515050915070203120304020f0a0501080718030c06111b030613020f090103050d1121280306030618150507090306020c0604050613 69
    0x88560070300011040302a00805d130308910900030394a04540ea00480441c01d100d82d400440c581d030f1a000604040044c10340720b00c0042c0100740e4050241e01c10f00e0001007481c0302da503007074030310440b420034a214100d918203050344e512540c003030112078584444504031002a04215000c9100300c050b941103150600304454802c04444040e10707107601c0ba45a6650070f89180713480100d100080044c50000002244c00d02c040340000300025112013203043c140d6400c0904240c6415601c91301030310303030510040c2240c400040700c640c000020081070305400700910010700849030021190341d0008840c0f0011090100121b900c0c50418400d0711041c2500c18060401070300d60703001032624000c07184c0070842040710383c050340010b110440c0800b240328950495403440001d8070a4150b0703580006070351204240108402407160568000200f0301c00401c020341c9a448484100d601428000c910742c44801041e00035000d0502000078580c00301081d5265a4003046075513843c40d08490694161060b4400301d101010034100050045 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 316210800 1250 316209550 316209557
    0x1e0a0b061905040506060702030a21090602120d020c013b06010905220305040302130506130f0b100c0b070f1b0c030c060203072d0b0c070209040503040303030509030901 74
    0x1d450001000001c0c18010449500607904001d50301c01a603060201c440d0441c800d1210304115416540d40820b00c65681d038480082c019130507400c1c4001c82e000a410100e69080d482520740d294210040000a07018105440d40341d517080000d41c0790f40e4401225103041c221625000c038903401e800215084050382101003a688242c018074018081801c1ca5000554002c140c00c002142c03120130318507010180382c841d01c2c00b41d0009001003414800c610384820314059003a11000140190309100d000141c1303400c07180e40546031941c3d8402000158107036a410102c0c205100030030b07840c1d02c40c032000c4019104c140200412161540b201000505681c02144044801500c075a2402c0f40c0d44031100c402c0c82000303074220058038103002151001001031000c584900c082e01295010b1030b00d80000d841c05c5048a000001202e42e030348a8882c02a5011280c0c813101590107410486452a503110041c900ca40c600c66004080c2d0401031070402c1005002001000f042200e101e5a800c201c01c2e47c8002c0203946900905c9080c6000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 316212050 1250 316210800 316210849
    0x4020415020d0207152a08180103051b0d060308030a060501030b1c030c0503071205180901140112060503060901020405010908070f1202041409010b03010b0609030303040b091e0a0b06 80
    0x85e4403c1e4034450b00020640c480c00c00c07800d0546110f940000f0107a2040304c108070005880603403a1501003c0030610282030070b0a00040c1000903107484c54004a00c070300701c8140400304000c6d10008041e0440401540c0180d060b40d5a030800456040241201e409102e001c6401e0084203111070074000900025001c1c4003040380340c0c06049940c101c07100d84880ea410707240380c8800d210304004101140e449140c0040e0613110580d503120700c2c0003002016010720414902c24a030441c0104000400d002490703005110034604040c2607044582d44400602090300907035010b10800d020880350358015801013090326026201e908046988a40c5d143c1d03a1412402440c10003240480c00b0000411111014103280784010800306441e1044948005d09140450b000481d03a0f464030100c0455040078451400300c0b24040d40d8051811000e407022031703070324440940018070b48031300358000460107101440b900e00512205803034140604890310405035503010110040da003000f0542d0201d1010b250a090600b003410549a07012032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 316213300 1250 316212050 316212089
    0xf091404180b0c040f05060a140904060918021f09120312150509061002060c0309010e10050702100513120e0a080f0f010504020d0f020f04020415020d0207 68
    0x64910301180705900e44100140310001444640341502ca403141410054445242c10b00c42c2c40d0590855000c6402102c0170042030a000b548040c410710311410381c150207030303035001542d001c64010001c940c4640a11841c3c069032402220410b003081200c18000c450101142034482205484004996038150109409100400812205250541400e4024100010700320304168880080d44c0c010032040e281c40015403420b000b0b5242400030550424030030303038000c840320510200c040d560303400151205007050004800510503030743c00d422003160400007000740c503d02d620030724150700900401e0301d00b00058050105440c1c040b0b805d80c42014070a10403c0300c02d00c40d40540c0e446182e44041042070113020800e0b10840c40c1229214a884940100b02c180300a148143d44400100d0510189001e80855a41807009100240c0d40e9034401250303a43c2c1251454039101d13680d10002e808500d403881c207580c2003030000c00c0c0000c50700343d045001c01c0d5280c3d50340c0a9403e50442508101d86900e0301d4050b12002200c20040700c134 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 316214550 1250 316213300 316213309
    0xb03061008150c13180f020307091a040506040e04050c1905060a030b040608030405031207030c0206031e0a050103025e05011a040e1311090a05070f0914 67
    0x150889143d441440c039040351114410210076842e0085500d01a00f094071001020507031084090094540c4800c41c19408c001000410b400003a125030000590034030031b007002207800e2a044030001c060080a1a035600d0b51004421040c807001c440c1a512400303902034249807418a00300341e9002c4c65860400306092820482001456040303826178208066589900c0c850a488603c1003030042d1003d00011031300d49192008061424031074090f0389107981d005014100000c0d403ca41c4038485e05504655082e104d61711340601200c10360750303444003c500c040650b05002403081c50b98400da050302c0c003d03660300a4454246114068801d8010b44840d409400682158203003c07110a400c00300700680f140d0000303013890001029220516000390180315650743c000401102d010300420100c0c01d11103540480c240707072a25070032152440000380300c219011a06245c0e40200540078450391700c0030f10003c251039600d09154a103c801040111030100c080350142c207042d02207a004002ca00110380700340d40f280700c600ca50340c0c0a01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 316215800 1250 316214550 316214593
    0x8010506091605250f050708010c05040b040b1605010504080301030c0e042d0203120301060e100f050702181008190c0306090f23191104051503010207060b03061008 72
    0x1a0080081512060005071800e40c171504e42e1402400101002c0e81070179646801c45800301040824040e0401c42007003400d503040309450440e011401880d8a450400301a03242940044000400b19440c0004105c200071040000d14160703801110b01d994015182e2a02c0002d025095030091715014102c01900000b0f0024070b5a14031500300300358030403000300040d4080b0f482d2200e8005001e96090002c0014840c203a03104801102030785080f924a0380101050001a04000454200500b0000c000500e14195122400d1003088003401880e02d04580c90250b150310030342442c0d0b000b0144c2c64018001d10607074558540000d02803039508026082c40c55465680d8032401000c00c0d81c0f044032000712000d800c070045484241452002501c40540d42c0302284024182810038800c0c468109100b80180704420110f0b00f082401031914400f0b13540000c2c20b4480080c403000c010b0003c0300b099415800007a000080001c9a00500500c5070154201c81c0c01c0c1e00c4422402d071000c900c50280500300d40c4440c0e041c80c03008000b100c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 316217050 1250 316215800 316215847
    0x90501052118100e0d0c03050307080405120a050a0e010e0a090509011d0f0f2e0618020705010b0405010503030f0f090607230f030301050d0c0e0108010506091605 71
    0x4801e00040140d00c20307820302d0509180f9041e101d503201d00502401600b400000080400c5180100e609021540e02030006d0001a0158081000e0354000900300101040224442e010031031455449a0400c00c0040c01035010605d03540001d80902000b821650064070f00c4c0d41800300040a6203c51400d05003c00001e0200811640b017071f6480d10310f1107840813250038804801d0403900001d003852001e4a00d0720b900c1e2406003c1c2130152540300d1114030b561070b14200508010f03c02c00b01c8440c0e08d070109240b4040040c00031508040081801c1000c2c1d0b03d13020303042d68018681c0c144194002e100b003030121420001120024410103400d03420130040410200071034801001001c05400906060004540101e40707160040d6204844c44440d11000084000d0080e54000d00e044140d401462503c9890304001d03120f00062091600450000752900b0030404000e00c820003070003030088500807540e0b58001490182400741c84903806445200040341c0d0303c8132414444400424162502480e0020a50810a41d199203544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 316218300 1250 316217050 316217071
    0x60b0f09061c200301080a080702030c1801170c0d06020a1202030a1e05060a0302100905150a11070819230105181b0d050a0507080303070905010521 65
    0x1440e08241540110034a1030b00c552240015042c0500300e800b081d20034052042c5425003011310040210200020b204800164065007032926907100780f0200b483d09843c0ad40c1503a000c16242c00420074080080059030403942c94081b080c1501d08a08001d984a000b260700c101e4003c06042703d00404104a60001c0040000528180364202d40300341c00d02089800c16510090403d0f2a60402c118916500310400700103203660208100900300400090301040591100074026400d4a04c80584607001c2e50203600203110141080800c0b080d03d503002c00c00ba61100f40c45101094a992481425203000107440c420f549440c0c00518010441031208009442e910340e00b01c0706504c4246c2c944c0c6411104210390100004980008a0507041c1052196850100d20103920b075030354008800c2c1c2541c0406511285c200000c140c0d94000c0007242d6041882c208117a11034080c0c1248a001c100044911000005621610071645d03002c02050722507004450340c2c031801d006001c2d0b10388942640181400c5c2c1f01001500f0008519 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 316219550 1250 316218300 316218307
    0x2060313140303011805010614031603020c16090c05030c0a050310091a09060108160c0213020301080a03080709030305030c0c072715050d03180e15010210060b0f0906 73
    0x24159145a0091708203440900388810600140015070107018003410803404d120000303040640752040711b8040103120300d03d80c400511004203207a0095044078507000c074540a0320ba41c2d40f445400807408452a1003100b0b034031850007602d402c200744140141e81c003c810a001061400c1801d040490b034a07003000e803c842050301c1140380020104a00e00c43c3c000210580d142c0c59403c090108100140741070002d1009061009400030405251403e28103480c0400b42810030084a1225002141808911143c48090140300000100c4c0c06140090140f0205110740d13162442951f6801c401c440e1407015203c0200481c506001090360061818042c0406007280c0045031003150313482031207950600303188800350b45510781206002d0000d117460041d1103c0d05540401411120700d003c011421030b000354080582001035028030b20203c600118156401010180d1159040d400d1000400b103425190142d030038094856612100e0303442900340110380c1158040450382e130a00005510406440d40700c031004a40c01007080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 316220800 1250 316219550 316219583
    0x504030e09070e10170601020105012105031b01060503100e07030303050c07150204050a14090a0b1305090715030504050706050f120a06050f01080907051302160b0a0507030902060313 80
    0xe122a8820013034a42d1031020000740c2010041459001405407411641800c0041c00b41c0f03ca09164181050000810003030f019182d420f0050031401030800f44012181c2c628039240308110150003034400c1ea0802c4095a200707140201000d01110445600980c5030f4010800400129020ba84425440408210703018508541680e95641c1a41007007114245598003040074441d038101840d00001078000c000280712108585000104101c0c80140080e200c1500e41c008450183c0f280ca88a02c2180b0800c00117215a09110b12035985403020b902070b050319034010f02012480350b0301c00d005040c0034540240103072082c0c0e0300b010310454440d400002d00a03103030007042103000081405060391504c10680d04c1c40015880c0d080000300142e418600d01e07042c2c100f02d583c0d424021650f00210b10303001201c5d000c4078400c00c01e42c400f462400203405481c003c288031403181041e80c010300c82c00c0c0d20401d1161b1100f41b01040540d030390380400d4049901c1c40c1c002a4100c882400000e8140356000507a0a809015000b400c0408450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 316222050 1250 316220800 316220809
    0x102040f0306060e190c052206080c070c1809050d030f0c03052502011107230f07170a02040606080a0b03010614010c050c03060106021c0e0108220215120105040504030e09070e 77
    0x550048c126000c104041003103003039405105960045083c41c0c100389494800d807242e6000c402540a6134603405010804020415805d5110164065100b800d4904108030444050014125908c0d4103081e1801c0044040c0c10520030302c160783c0b04603401900203a00c01c0820804001c00400341c107800741035643e13961205590f0480000541001c1c0c0c49030500d078030303548001d060045044044540a01c0c0e1a802005e040c44112404561441034406228071034480c83c503c0c210780c5280044010340607400030715006010a490b0352208019125003200c200610101050800349422a8002d00c034100c8050340502c000d20306580b02d5100581020f001d1411102450b00ca040002c0c1090000e9000b1405a031204045200c007a07441564405190400d003070082c520714300c2070f0018103100401001011580158287c441d142c1007100e9500212a4020b07084001c46040740c03990138841d5110694001e0b041c0c980d2000061345103403034000d90307204a0b4561f680c11f00d014659418040d2a05001c2d00170b60500a61204ca0301081d01d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 316223300 1250 316222050 316222087
    0xb0c070e09010c110309060a180b0304030f081506160c0b030106081f14150c010608060a15050d060513150f05070309050d0f0509030102040f0306060e190c05 69
    0x85600000030f10450503d405030940c00381c584100e0642d0018041c040c000e9032684251003505101d0304001841d00d10308500c20f2030711122500083e03908030010003408103040d440002c4c03081154464a4251564981c42d0000150501d5091290361240c01000303240d40c2450f12040d008a202c2c0b003500c048004588500508900360002d800440c0000c101600f0012201414000f00310044400306050030b819041846c40195030203802d615034042c00801500c5200010003030125020342682e00000c0010948a03400140c0f182c0060f50300103d007505015800b90200806805c3c41e0480c0c600418180284d0750301d503901c501030280145071104c00554118601c010401e091500710042040e0000015511548000c0d80c0444401038100d0b000c2600e403110b6030f8005900080c580001c62142d00380004603c03e0501e0403100c0c0e1180103502a050b500110f4006061a6100c0500c03040c0d82c03003034009009241d00d1304c010f954104000c940314807641c1b40c491540d501c2d0803015488000b60070510301d000d5150403c1011030004108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 316224550 1250 316223300 316223311
    0x70f031104030813050a030827120601081c0806040b06070210020703170c0d080a0605040c0206060a15050403110409060203011d060906060a1803050601032006030106090b0c070e 78
    0x1c000140007021150b0b0030142d00c0580b0003101c028188504548a16040780126404d0f0340140307a080100b0003064003880941c4590450007008240265103d0ac141515140e007841940e0311446410140d1100360404054050340d03146542c1c07210101c0e80c8800412020f4031083c048141c0041e401c100b1480541c036150030002da445902d400819440d880c40c074141804002403513880440000c2401581d4101c0000310301304801110502d01800c10f9120303011508002c103802d901140d4860310f049902a082900818168400e090480d02144020b41d24003076846880c40044200000440400c42840050244501c01c04101000342002484007400d6440408aa2081e04848490b01d820074030240e000905002d4a0703800300c0241e4905425042400100307060380200300c610710922078026445001c20200740c4001000b150001d0403a10296581d052000051404201801e144040002e54040c5800d05008a13070480c0c9465403800c86882c0742549420703441e0800741c19454140a040ba0000390104040d00b15801030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 316225800 1250 316224550 316224563
    0x14010e030301060f0201060e0708040c0b03100303020f1507050c1515031c08150f030303281a060c010b0a090b0a0e06060d0c02031204030e0909060906070f03110403 72
    0x9504103000a13089503090202d50f011603062039000e025640720314800c2500300b141800c040c280b648640c40c0241003c100c5030080f2444c914084100300c00350210703060f0b0310b0440e030181d002d45801340010300002d511160000c0c0d034211032000140c0451a9284140000e100702e044d42029200001142a1546000c20007500c040681c0c0c404802482c210f17160510506155080642d01c500342c0107922140030b01603c0e0000c1c11990310801004044506403104100e00c21481c5008042c0c1e942d034076140d200608440d00174288461175030240700d03441091071028494034600e07183d40004c180e000c030742000c10811030b90b20100b07610300255200c4401c1c1401d1707140e42e02c400014120070748021401000c0c01c0140300c030890a0703500402d40ca401e0401400901d859500844000e90200480492501e00702041a4030310300c1610040c5007071404180c00c220030b05900040400c41e08408490703800c01030303c65100456854030b050750100607582042003c200d01500038040d180403118541400b1400f180b40502d50485900a9401540d14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 316227050 1250 316225800 316225807
    0x3020928150501030c0e01080a021b15011211061812060a0e0c0f0d0311030414031603020603070c0309120b01030b1605070305090303040b04090f0c020607050d0914010e03 75
    0x81e40a41141d68000e0682880c0400100350313204d80040c00c0901c0c2190707050621100c03102145030089070f90111102c90741410300d00c4258400300707071807a5038a1a03558610941101d44000218244100d5041c114820b604007090b02c122901c0340e010008150b2003c002902022500c2035074140d5a11202340c541040000c01d0080c0c4410301d03100b0303030200507120040c0383c804241c0c1181d8480d64041d91903401981101c2429282e0341000041864156084140c508160f64a48804100040c1090481c078422181210030303415110114020601062028440c2c0802540200e0500c000740102d0322804607a01e00f14081c0c6005281241c5d241101505420181015515075107010014000d002d080180700350030031801e800d10b220010031007100a00500540e0780042c1040310001c0d000001d95010000d5901510381d0b265090360344d80d56052003200400145000046003400c02c13058071039085c00403540c90722483c0340c2d44a562802080e0108c078001400c2610049130000381d0406001580c5030309214100015072003100a40e1b0307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 316228300 1250 316227050 316227071
    0x90e07051216020d0507061112151c080702030a020406080a0204050615040510120f0b041a060f160b0406090b1815070c120e0109050108010e0103020928 67
    0x301030000c0a10320b00c0108140c071078100c10707400200240003079198603010b0340701e01440c50001c0142a0044504881da0340129106801100c2c03811200d0203201c100e1040009100302106000380c3c1e0082c803542c41010300c81840c5100100b0f140708010020940700900f5031340710781044d90001d411219150031004003540032890000031428980301c2c0c581c0080c0100c44003450740514805103007141c0b0460182c14040e039019505200814090310704942c1c0196180d5050010600003c5060000c03c0302a100c02e102d20b01300402c3c00b400c0900d04104800401020305480d15203548640d88550b254012040044400b00d0140070030003040c00150403600952190f280800d4403480c1d41024000c1541c00b42c406c100d2119142540300c105a80081c401042c1c0400000c0d4003400d54a540c0c06030303920b204410703015040c1110400000c0304240d202c2500e5101d00c1090701c1c0e0a84040c0c5960045032450390034003030307008040e41000040c4090310f0480541540031040e00c6081e4045d040070820444d18910624003480407940342c02240b1b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 316229550 1250 316228300 316228327
    0x60608010605010e041a0d050a0b010b130b091e010905060f030906240103230a1b050a1209082110090b01050a080c1611030d0e060d0507090e0705 64
    0xc0e9030004403014000180c01d5a44d6850b1b000d2944003c501c615203411071501006030602501c13050942080d0307860415a0740300d00180140e403260f040e00380b90b6103184401103120310321241502c140d050301620702c56140d10489202484601c5160792a81032000040002607a80e132410700a04140b640080c20030340fa4104010341c0c52500c00080c08d40001100e14aa0352601c0131380d55030160121070405d01c0c01107421040e40d842c06a4514040301c030b812010b858181081048000e64000b00401030034540c2d4402c28030030000d021030305070248003507600008440ca800d82e0410001a04211304d481d001d01d031040d140c421507032001581c0d180c3c0c0380680450080e80c00200503401ca19544110010540030b1801d1247d03c40e03510000341a841500c90780000d01140b0000b080382503090b0b81c2074a411700403010052218090714101114140e1a60705603034420300c1041d02120440c2d11810381909200d1024014509189207000100040c080090600c400c1159013000001c600204008840c05a0140e48806035200043c81044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 316230800 1250 316229550 316229567
    0xc020a020a0e010302062d0a051314150c070b1b0f0102120f15060c0309031e060c0a031e0e010f09120f120203150112050c031303030906060801060501 66
    0x1c80304561000010801742e1600340c221141149003000040c00201c080c00084003a4811030807441d070019000c07609a011a8011009086090200802e03201841c1da580321130700822800c0d00281e420140c1224442100d05012010303204039800a030641d1241500c5501088098010744c20104d100306242c0c1d0140b55080c4117001507131000c80168001d625200305014210030008001c1c1c240e00c004009200001c0c4c07148040e00014022180041c01d5550302d8484d00d051a03540d803c03200d600c0b442402681c030030a040d0401c000040480b20000c4025003015075501140160b1500a1000c1d101070540f240d4005131110841070710710290b03818074400000c0307180c449003000b030031601c1e059400d001180c600f640030400b061100300d841400611500c1c160852414441d800c507081d00d800100c4410050000c400d014104030142d0300700a01010a994214140751040310010949206685040d4820030400c00300b5071040c0450305c8264424040e0030041345d5030416035211001c032501580000107a035503800d0140819a80001003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 316232050 1250 316230800 316230809
    0x20040e0901060f150216030309090b0a08120c0f0a0609030e09040201121116060204080c1909051510110c03010b150304020d140307020108060109032012010c020a020a 73
    0x300314050415403546200001c0b030040c0d40d40c1c1c010502403900c02a00c00c00c50103154038803001c01b40104640d24980038081d0003542c09418003050620340c0e1100d140c00c0102e046012140c04400404550242c4041035003c0e605c400c0c160340a40c01401d101040c1403074100948403110303205032030000350a400c50030000c00e0036400a00451140120209010160781c1c0818540d44140e590300001445040b801d4501c40745101d205007050540d8400d05040b0f0500c0050750251017202d54040940e64018055803c1111000c03e00e40070240c01d4200410900542d4250780c4800d5000550040b00141e0b1b4907143e0000d0030b4110010350050005542d0708511125940901138164061000e03030007402020f0000d000a200d020b075202c9084010600840007800790340c0d47d000c0309001d00340c000003c06681075071202c0e201e4896103d0601640824022404602c807544a140800c08494115136206100d903420f04456196a81c002c1c0610360081410b40d044104c000203104242c802c21641e0020580c0895134030510880b040d19030700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 316233300 1250 316232050 316232053
    0x103050106031109150c0f1c080606071e021302130501020d0c110301020d23071805010c03021e0114010905160c0303110d05190e0d030207030320040e09 67
    0x2031080c103035055400d071100d540048640165034010410081c007103000381d406c0e6500d50321440e07995416412002c200c148844072410f1243c030000c18409015602c1400503124580c1005040190002144100041e54800840502000d086122036000a09000011800104807550010b411868142e100c0b50744001040c00b8000b403c00201074150150004009910180001c071130507055000700d0354203504462409000c120108003440080c00420403030441c00040c0b00312045900d000c1060a4010300030b404e6032070f160445c00040c171400d01c801103804005040040b4107601c929403444070b41c5500300c86c401d555112000d00028000224540b80340c0711403410707408201c0e51072400061240401c100c0300756030366411040c21709010441d2a0706d000c07001401c442a0070f11100da00030856074051849d64001a00440e21107a0302407030300036454001403c03a50100803900d100c0d48048041c00b1401d0198000e0701c4454000e05001400b0051410320424000c01101c080d04070000000341070103911440fa04481c1c20644100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 316234550 1250 316233300 316233311
    0x9031d010f02100b031921092303150a05190b030303060d05030c0102040312030606030c0f18050d12170708010b09040f0e010b011101020a02190503041203020a02010305010603 77
    0x420183d1101d00e110b8000c4103d0740c40b240c3e51100d9480030000310b070504104291910080306641031040307880010304210302c80503903001d90300c020542c40340c1d045038140d0b101602e50000700e0060050039110220001521601402803490350007000510f51140c1f88103025005003c1102e15180200010311500780d840030ba000c1d4980b4813068441e450000a50b07a1064050b280003582a00e01d08040303185010382650064558000207000c410890400a004180421a1000d0003915103652090b4141c80d09080000001201810200207081c401e103042d00324078104203c4030344060349903400300d450203c0088e01510325050340210400103542c4900109401100f0003e0a0101e0030446802040c0840c10f00c20042d1020000c640c0c009a943c50350b2001410800c081e00802901c0c00d20500c4030301903c1200078079404a048244003040306a01802101c0100e9243d0780900036030005103a4910704501458400d484600c0140000b1072700c82e8010101e130904078042e40044c66800310710720006050350b81c1608110201410721 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 316235800 1250 316234550 316234577
    0x30e01061a0f0f04030237030807030e0a080a1a18070303050705100c03050603150c0f0c10230a060308030109180506010f0e090d0c150603020409031d01 67
    0x25000e079514102010380c41c640d100300c00f141c10300f5030340203d0308040d51011031b426841c01f044104401105040000300c0480c1103c0e02d4141840c500782c2c0e4244000380140c0c508004d8400003911908050b400a580180700807842c90711044400e2a2520407041102d9506100b41da51003074003982d254503070384041200391420480c02d4401245880d02014400202486400f2401800b04041409170b009141009602000001c44007a4000e01600301903444d50b0190062100f030000044505002500c40c0e040b203043c0501c0c0c00c10b4101c1d10050740c0e02598000c042d501690b00362a0084059015440b420800d07445003410311121080101320b5080081c14041e501c030300d030400410001d844035081d2170440310101c4000a100142c0d0181d0403649850f4040248140540d02c008549a1315000041d420f413030600d80c8840c650354800c0320311613445800329000404980400c2c601c02c0000c4240c45c0601c0a401c1b20380c40480c5d0a942c0b07501040c10390703143d403008501296186100d109400102d01d50300d210190240390000701003604 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 316237050 1250 316235800 316235849
    0x30405030f210c0702010807110c3d080c0703090b07060b090705041406070b040215120703091a190f060b0412060b090108070b030a0615030e0106 64
    0x30030704404001140800d02c111888010111000c50700700e5542d0030b6800b0b00c0c210821104503402220300701d0104007c076000c10a554442c8a1110494201c8402051400c0b500010004d10b40f000b03140d500381502c0c2d240014402c25410042d940ca0300b500c40300ca0403244802680300a03140200c01480075545d01d00502070341004c280c0c480c01f0a400c03100071611007a920f844a003054005401400c42954000000c04148105c00754844000c00c00ca90484000c031210030403240811100c0c0c801c5a00c0689288600e0f000704000d490402e161040e10b0200903902c4c1d1a2a120340c0c0c07110340d0300c4001c0381e640e000320756a80080400d211034130f103101641104400609640b031401203801d00b034030b0042c540e08903940b558803414030364001d0180c1d20507000380122100554503280d80b0003403034080c0c4103c0b04044031039900b8030451882d6401c10100c083d050b5180032010700141401d2407014a43c03500000d105615140d1107810000302d2a450701c0d8440b480001503a40480c0e030154150342242955440e0b440407615001501c0301031200c2c00e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 316238300 1250 316237050 316237057
    0x5101404030b0c1b0a0c09060803030a021b1c120509030d0f06050402070503040f0b04081c051608030906090706051804090210110705030a0206250503030a06081203040503 75
    0x140400841510b40f216582c00c00d0303d01030400442c20b08000203070380c0c800c0d602d0000f810380001849004c200c91410f440b00034200a0300c002d032050030b11613030007400803405440e03071500035101032011010040c80100301d0f2415a851305030b030016883e150070060102685800d0b40001d010320b284150030421f101c14242100c960b40c0d244a044041c41030146d075201341c2409040903400441c018800104103640b91080c50030305a440e64020310070407444510500b00054290b00728410384088801440240003004001c904940f000c04001c2c294800b0001c08100c601c8004110390144080e8600640880b034403440c1a1214a02d000400780244046521100080241541c00310031074020608aa2400032484a00070100d0050319074490001d501502c880d51041c0d0340c0358004981146d542c810b2003103030040f596400a05403600e401c803602070342102042189610800c0c404005803c0a1003c011b402e44921480e03d4490440e001910306807981621a44204940381d4108a070210b00f160000d1003901e0340c1401c0c0d95080d6a4070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 316239550 1250 316238300 316238303
    0xd02040f060206061f0e01020a05240105100806090c040302030d03050a0c091a0c1515100e031203041a01080c040b0301060f0909050708070801140901020a080c1b0a06060510140403 79
    0x10540d140c280039640300744a09c2564981c840200d030b02d103148030b6000fa203901c10510000c959400303000000058914045011508401c8551144055600c5007401c0c00051940180000d4006400300000001a01d0820035288068019a0000b882d810410824401c1e69100703041c55080150310701e8148480060701c1440034002001c8102c190b42c5030341001103c1c2c1003a16400003069121400000c01407010103440e840c03410040c00725680e44c1e03110740003203007540c0d403142c080c4001d50540e000c2010240c0b50100440115000b90003103e803030b070703004544403000728900c01c0982041280b60409408010541498060f881c13080c4403c400a01c240c1c0c1c100020325040c092184508101c95407180c40b040140f000a0100c0405800c05e5000e9400c529202c030f60b894041c10341c03804010401002500000d03040d040602c241d503030592007583c540d00d40752600c5000513650b4001d611400303541c400c1c6d041c1680c458003003040f41100c00751190802198103840e110401030011000c000b8402030040c0f1210100c84842800111020703207 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 316240800 1250 316239550 316239557
    0xc070f080c2805040b12060906010611030703020c010309031b0507030605060a030b0c070c080f03090117190b15042d211703090f0d1d06090301020d02040f060206061f 73
    0xa0602d400100400d2050411b2031442c0100400d0080c0824042108d50581e189a00c1d9295811980850283c0e02d04c501a400780041c2c04c03c82c2c140d100d9610076000030305805c0c02480c00c40c80002690240e0801e24804010456250b8007000c170810401401b400f515911050898107025070f5840c41e100e04015201c01092541640000200503003040004907a00c0d002d40311140032200325045004416640340d0007511110b000c00d11054600061003140c806e082d201e04580724900c58141d40c48810140074010012842c3e600108400c601c084580741e80c400741c0000c0c40e80324081c1d0000b191a520650710301445100040004500e4181403201c1810110003600300d03c850010359402c82064208111884000c81c610049030b0000001d0150f04000090b4005040c150641550102001350b2400d480751110070466210503e100040440c4900e4100e014003510342021f000580307007041d00fa141c02c089901541092880d9161401b040c00440d0781080500ea10600a840c011740c40d8550002441280c40c00440b88401c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 316242050 1250 316240800 316240811
    0x609011506020a02150d050112030e060304020a0b071a091e03130605210a0905190c05040c030608071d0a020a080a0903050903060f01150206040f080c070f080c280504 73
    0x100d801180c102c50707a2085180d010002941c403040000390050b1024004e0300016420003075050f0f2433070060304503401194028500c04d1035500d00a01401c0350381200b1000c5d19080750001001c881c8540500e840c0303103c0d5080340064209101c241591028080c0680401c203186e50080c04262903503a59150340c83c09813101c83c203010341c49446c061124020191488580c1d03007110002d01c18440c1441d001e070400c1994510030000c1d1000144000c0300c3c090201c044110151a419903d2020881c60a259002888102c5245000b2580c42d440d200c46c5450310050303a1140551409004a603001a00d81e04510340d04035000000941c6013141d004001002c00d8005090301281503a00ca00b142c0c00c06015100702c0e04038440150550b038040c60700c21161204d2160900c12000302500070b8900e02c8a032071011504d584130b65400540500d065003103403a010030503086040d40c0540d501c9103100100320b02c50550b5888004210b03860060145030600030600c0300b110f080c51702418422800040c3c44100e019581000010340d07105560000e070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 316243300 1250 316242050 316242079
    0xe0a0e0f030403030c030e09090703110103140f0a0c050a0509010302090d0f0c0f0803280318060608010b060301050d02040926031506070309060f0509060a020609011506020a02 77
    0x1858581080c9401922001400108054100d03200d02101e5010ba243d41c4885806036040c0a600c103030440d400b1001f80c012000c03c0c0009014070a55014201d01850002400c219035040e480004030152108006200131307008000d080b81c80d6005a04030910140b03050390414100741c00290490180305040c0c0e05164022649500310f40321140d0714a20940c02c0240d10200c5030040c1054002c880043c0a520b44074a030005000ca608034cc00001c4856088000d1703004121200503080e0900060f5140304030208140e220502040845101300c8027000d46d0340158070020b1030501c2c29000d1821225030705c6030640512020300040065949040307080541a806450100c1c011000d40b40140141801051000b01006140840805501c04402a41c85410301101c0d002100f4035075801c0004c42c2c026584e0003000540000414402341d07210301c800039103540d49802c0c00e0307080c64036180001d8050341000b80c003000140d12040801001c0c4409009a00851010030b400040782c03420081d000f504c696034408081d000d00c220500c0402c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 316244550 1250 316243300 316243303
    0x4030c1a0a1b03230703090801050108030904091a010e24060f0a09050a120506010f03081b07050409080702040513030f110f0d030501030b07030203090304090c020309090f011a040e0a0e 81
    0x301c4800b40a40c840740c01c1c03084c10441c4c02d401440c8182e00003041c00314049140d507814440e00d41a10908001541400780702020413010780030350a02155603031154030810f25001da091558501808600d1101b82142c50b002020642c2d20380743c9280400c4c0e081c40c1a400e98450340f1900d044070300c4500705585081d503c0006040503940302c28164041a00b0500c403002c0004c03e01c40509280324801e22a00c103850f0310340d90f10501c0008400d182d00026254070070420150320300c1380135000c000c171519080d4002c0d111015600d00004085443c0184240da4010f00010340e4070451400e841a40c0e4091652229106107001c07a4900400044a103c00c40051000310480b1a01c0442c0400545074001c1441c4201d0f040c0340c0071110000d000d00405c1c80210f40080840020401e010f0090083c0c80c442c40c1c280c00198240f0349001d088101030821035990a056001c00c0041e41e41613198180c946200320800301441e0340c0c0354507004503000d40e20000c00140300901020b010034020028180552600055079000120314840e400000c103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 316245800 1250 316244550 316244567
    0x3080103060c0c020d050319080906060f011101290d030215090a0c08100e19030323040c0f0801090201051602060c0a03030b0307142d040204030c1a0a1b03 68
    0x2c5c0d400103100004008122001008089041080182403442c080c481e00c141d0780032100b0788048055400c00c0700001d50741c4c100a00c4882400c101494100080310740400804e0031198514a850070400300c0c440c0840110300071242c0c59455030026175008140d0740454500a40714110150003844420300f950119030010b8023081620701094000803403810040d50707503044903514240001140100790408201c0101040e0220300e06008156001c120600c2d62480d980480091a9568041821600c05100c40c0054964440310920852184a62180c1e45082c0b01c1c07840d05002107940203520030782c10240840c00503640325069800561203c8503141c48902688006034840c003a000822105224886000080c9580343d00114115241542501c2c03e6585420702140c03040c61000003660480c12250000c039884a00c4149070758048241c03802250300012001c0000d0583c0d020b83d10503907400039003200600c03106076a24075941c0e08469030030100b07290205000010304000040503148940e200c0c4200494141409440036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 316247050 1250 316245800 316245803
    0x220f23061b010f0216120921050102040e150f0f0114090a0312020d08090a0b040803070e0303160303060e1e0c0d090308041b0e06040b040b030a030302090909030703080103060c0c 78
    0x5548a90f031000e07099090b400c11034016942a0800c40e07040d00740720300904480050701d0400c1d0401c090080d1032350303132012130203d03003001110203641c00c000004061203400e2805000310900f60402c10407421031000c10054144010746148104800d15403c40140c3c1c0010711810484103412403180c0780c0d00e51100003080d200e115400544514480380c11404140d0b800304810842c284141c5400c0c105494100559aa611075010000d150815840c0850046080c0c2d00195500c8070b01880c150078030b01071140100e41943c1003501030100f800c80000d4100c04164050040d5005010007900d43d40f801e01d071404030702d03c0c0743c07442c4103100c3d1040c0c444901082c030700440041200d180940c101411b1180002c203113001040c09800710340c00e81e201c03512044000c17140c205215180c011201c440340003420a449036800c12005080420a180c0e0241c3d0f907040c80401c2e91000e00c07807268230034002e403001030f10707400b4100134442911001002c044264008000c00345c0026003041e44981526004800061611242d030300c15509060b00180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 316248300 1250 316247050 316247081
    0x1506030c12020315030f011404030503090c0a06021006080a0804030209040312020408030d0e1c0305130501090b07020c01050429070602120412091406220f23061b01 72
    0x10400441302d09000f2907070029080d4219092617820000c9282214502c0c4034081322102c44c1004100482e118001843d0018011803e0b606207125201c00511000d82503484140560808120b550014595100b18401020741e01c028041401d00d55641100d18417890000901c943c0605c1d0118080c07501c40c10420102c00e40c4108110b6890383c07692602c03a5690011140041c1c0e03641414001110018045030054540c802030b4070301e0002040e11041640640002400b0f0200301103115041000f04009000b00c5c21094003460895405007002c0c10000d041c95500440a07050010400081120340e02810901403440c1d04402c01c010102130300083e8240611500b40c010742010300100c1d48500486800c529103015030f1044010300004130006006030360000700ca11035920080144111124641002c0008040029140b01c5c1e20625807905074840924018a40000d1503005842105200d4903080c0c0324401082403400e06841012114800041c005d882080040175184030365405013a03284a094001c1c50b0b50720504403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 316249550 1250 316248300 316248307
    0x60b031002090f0f130506031903110601080d050703030b01020a02044506050408190207080601050607121b080a0f080615030402010f0c020d03080105131506030c1202 73
    0x5090400394000d02d00161007550004510309491800c0190000c0304007028069030107200700c00340c0240050070001c0616406026807007400348209030350b080d0703103844a00c240c817004031039480201c2c01480e01342d050f0070400740c41d0f20038418880550f401a05941c00e203640740c6004500780d000440101d041411410bc000d40003810220003d0607094907000d00c070b02c2c841250340213020303000c1c1c0200091114002071400c01c640322a003a00803400715146030041c5521901070070082d440e00d00b109202c0c270325624800981400581000c042885140d00a0256500402040358100c1c2024030744d4a030103452510864a4905010001d0100086080020f520105d0f0517001140c19444031030328480600305087d4001c40b00e00043e0b070a4002802e600d0809040c140c2c00f1040852035003175a4031035005640f150200d07003541c400d0152910130b0200580d2404caa009030280709656104041d4505414801540c9042000c0940c041c00c2c40d08a900c0129079460400c1110210328020910b004c5a4006071100300d901c0400584950000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 316250800 1250 316249550 316249573
    0x30b0f0403020f0a02011d150c1501090e0d08060f1918020f0a0c02010519030906050a0c0f0f090f0902030709050d080a080a020903060403030506091003030c02060304060b03 76
    0x450946114a00a809807607004010882e81501e481100000901045035a266517a008400e102e41e02050f02028084a1a55090410001c40c81d001000f2034034180c4d012074170086840210482c414010110b1361414071075a098491480d48400b802103220b0100044400060344580e02d0f20000e00d81458054000c642c4102c5014110b160b910080c000c0e66084907107800c0261800703034136100300c4260310580080b5a050a2141c0800ca914031140c1c0703001c2c0c0c1001414070061401d41c0300c3c0d0b955605030808586001402c41c02e50314102044da03c1c002d020302d8540740380500412b01d081d0040d4041c00c11000501c2c00f480141c4c4031910980322801260409000440c02e03003c00f103001c0e8855401507001d168107843c0c130380c0c0065540040000d224420000145030440602804407524007070b101468201d031821001608144003440403178604002182c00713a00190700c0c2c0050115600b03004401b1038021004100c11840d070b07811600d01800b8a4198000240038900000005080c044035601841c56500700030240d079911b1912 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 316252050 1250 316250800 316250821
    0x4050405060a110c060408090409020a0b120106030501081506031c1d0406061d130c0c1407060203040501050f0d060605190504050904030c02010909020d021809131407030b 75
    0xc4070044509031401e607208000074400c07004d03200740c80b13030f51401424a540c40d60f450380d800307401508203560060707112910a00180d8a605000c0302408812a05689491700340382603042d15071042c1c1c40304007814074020043c0040d410110340b1001e007028200301c40d012a190440802e140203402d03007886041400c481401080d46034170036802306901040c400002840910a810001107a46620400d0f001c1140b0104071854034516924100c1c02c5203000380020f50b5191854a19015070318102c0500340010420744800c0208034200715110450380b000c5000340b440c503003481e00c0a50780c1c0c8110301440d41800b802080203c100e1241d03904031203041400803000c0c07041a998030400f6003660401905200031001d580ea411b00c2d0103101d9801d41e41107440080860400d80c0701c541b000d4490b501d1081051341040701844021400c4191400100007041c00c0c0c0b4401a0741d42d8884c4aa80c1000400e0341c9003501ca580007201b40024000c1e1031480f004001d41100c0140c4000b81002802032130300b0b01700d80c4020829481d01040100b9100c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 316253300 1250 316252050 316252063
    0xc370f140414071b0f080d140a1103060f0d0f06060e0901020a0207050108090319020d1106010b0703110a0b0114010305010501021609150e011418011d060d0204050405 73
    0x81c0d40c280500591900500700d01e14040300c6000002d0160f25581121010b49652842034500411940c405a43c50341c03560a199403200074070324a00b6032207120031112180e5040d04c842e071140141101b008100c107000f500c80c2c018400540b4141c030640d000900c100345555100c0542d81081e510241d20301c1e410b2154a0b015001d40418855090b01204900000340f41d01d006000b2510340b452158060301c41d55040c140155408000036011403003511060000000145905070145904031490f002000a200b81c558002c5c0290b8004041164941000004101c1e82c400501a101400d5160400746940540c00f41058500b2600c0c90001c1d2015107007400018078903907000d083c1c02e10828203076070500c880da0305c500c010b80c0c1e81d003010900041d00c00d5507c10100b2030070649600c0722140f1815a40b841030350310f685251164032000e080c0c0108001c59800325030b0f407402e840c2555035402c00c0341211a4811840d8500241c1c043d0f4005101882d054114140000800e556241ea4003185003550082041140f81480c0c2003855803040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 316254550 1250 316253300 316253339
    0xb030a0b061513180b031914161a070b0403120605180a0f060f0807091b09030f080f030f0604050702010e0d05070f0b0f090c370f 57
    0x822200442d001c0d5028088901c01e50701c3c0782c03031a2240c0c0c3c80d1511103002004018031040300281d072010250001c0d50288020960402e10008103101c81d080c6e41030080b40281c60100c103403101c2c0d02101000d0383d214090310b203880c1240c10483c842429100e01074901c5c00d41c0e21520364020407541d4890100020190090180300c0107180e041000c0003a0f40d04c401c00d2000001050b10320349900ca03548800500c044455821010101c60240c00203d10a651840200c070b84007143d07001145503030411181400340744040e1241200a10fa400755441d291a001040940200130302d01020b04a02c00345020030007400380b80c90489846008100d00d247d0380385050800a1440d00082d900288950b0905012540c528814082d04210402d040003400404103088004d503003607401480c04548007040d90540e0004500f40006071341c4554a100c01840881c50305504040c1811a0340039114422441d072407240c40400100c023a8028103070355000800c0b01820001c0000304684102e54840b206041c0840030225540030307003041034550745 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 316255800 1250 316254550 316254559
    0xc040e010f0e070c030e090a0e0106090e010b060403020108040b280204080f0607020712020a030f0b16080f19180303020d06050a03021309080d0c02030901090b030402011409040b030a0b06 82
    0x94a49280454884440000145c0000c41c51b001c62100d1340341402509400040200b4000303101200c40c2803840c00e4501c00d601160400380c0d101c01448038500280201820b4181c11500c40346400c0c19070340041e002038400740c0040c0101e800240000c09a0310300340103e500000c01444658414080002c1c10000395000f80243e180d140100000c0018201d0002055070013003e07282c0180c14110f003010f15000c1003208002007617900a03400300001020800802d0f07020a413600801031001940f62922030301c05032401902e42602088402c0040101b40c0c0000007400d034100c40083c400820100a85004401038101c000905d400001500701075800c2503090360060119240141040c0a410394460802c80a2030f543d12019411140c0c0c440f103483c0e212401c5e80002c0716503106132911418910300000e1007007140d407900c1c541d0000d40c0c00003407641c0644d82c025611100400b40054518079501c0c083d80001d152103000b46049450a201141241d8207a0f100d030030220b45520040c049030b0202d141410b01800c14207040e50928020f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 316257050 1250 316255800 316255829
    0x3030f0201020a021e100608010b01090b071104091416090e01020f030414030f18040501050604031109040c1701020711010804030c11030a020a0b130510020a0b0c040e010f 75
    0x6140180203880030400c40d40c01030008003412403400a00c50b80d1031404101c550046032000050b644a500c503040c003400c4140c0c0002a41c210050025282d80080d80000302480010300c82c90b000540d1034045502d0382d020a84011580c8040c03850000c0d6602c0760300c41d044500d80102407440c03030340c07102c2200050300303c4580e00c6c0c0c10302000510402d15800c0744505055100b00450400014000c038232000394403c1d841859808071f070319144601c0340d000603035040240710800b4800f82404042c520300e02800b401d405084225000351034180b0395900c000219940380403981c045e88000c000601800302d00d000c01001003188000079064100b0805180d8000d5011240c00c81d4260444105500c41d540f0a8003903912696042d01c07651610100c5481e6041d484030001c5402e541449070219040058841d00400340c01071030400b1082d500d50301311a0108a070045680c00441c040c520b400c0600000c00c0e4001403442020b5004400360950703888842140c0c0251246410108014400800002e00451003148880842e2410403a4610 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 316258300 1250 316257050 316257077
    0x90102100b030d20010212072a060b03150c0a080906040317040606091a01030c03050606160203010f020708040602120a140a030e0a0b090c0402070b040f050a1a010303 73
    0x1c032065907154030380561050722250000c2d0f0007200d2201e405101811100d10310815070003440e00307a074801e1486100d040154807d020900390408010b06401c0c0c090580b00071340c40340404480780c22955842014103000e4a6042810ba240c0381404904850020a0044640c1c2c0c5419540d942840c0c1c05880c8032070008a508000600200300441d0f00e0b8007542d81580c1e0310f070324408400e2004c1286800540241c0c0e0701580c0d050001000807040c403031a083c001c0211480c1084059250000d004c5070002a880000d25007014200802d170b58031442118211810400b00c01d119003a94000301e801040d02e60803040c06e0920000e011814014050060812a015a800c03184100500c1440d1405802840e02d50004510001d40c128021003140e4090240702041340303400940d20307082c0700c811440d101c0d00c8442640d00c440d82e2820310900c1d40c001c3c0300d03403c46450140c1e01985401d20326601c018001da00208003130f2903100020881c5007040414001c900301c181d0080300d41101c40350303501c00d03000b0f10560a11080300410070065000c070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 316259550 1250 316258300 316258333
    0x913050702211603030509160e01030b150102060a0c110102030406060f0515030c031e0703060e0c07020f0d05160e0901061505030609060604080307060b10030902130908070204020f090102 82
    0x40f0444404540e40702c009680b42c2c0c0c1035000e044060140703406800b07a0040420420820890580101307200000c1c03880a503d1810300c1011942e01401424841d1890b00a46209980000c0c240741c02c495614030000e201409000b0483e000003200c088101c1550000091000740440d40c3c101c0001d813000f10342c02d40c0895603600100081825901e00500304100144000381c1141c0c1d00700059903000324241103800c030521454820b4241350340f00f11000000710f0354900c0f09206012090040a501c11440aa00b41c50040160000f425060b200408280713f000c2d0480c600d41000018808000c403c9031201e0340c0e034032854555208828180701116260300541c0381590000711003441081e00e40242c101615581e145071505070a02c018140d00811064000030300b04000a0304074403c000500307490b406004005081c400320340400500c4100090307018205401c103561031000da950098071100314072201e40f0009280c4818600380d403081c000d0700e00181d441403020502c1107409030401c00401d14500b00340d0030307500600341c402382e0381 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 316260800 1250 316259550 316259557
    0x6090e030307120b030319120c02010605031203181c0e010921170307052d03070f020a06020f0c011d060c0c0c0a0303020a120309110105091305070221 66
    0x1d0006020480c43d0000b050b0b455204000900025041c4e903d84613212848a0741040801c1e0303008001040c042d202c80406d4541e06c00e1420608442c4001d10881d46000c000035610091110346801e4202e00101152007091401500c2d2107450032101070701c4081c00c0b0108005030181c959034190010175088501c16a4640c1b290803254281c0301700c0c502003405004034030018403000c3c209200807282d0704010120001808030a00195110b01031560ba030503601e6861503030248414060300d5040d9003045e64401e40880b040414400c0d03d40c442081d141004006500901c00c1b85001403000000e400c0321701c000344012a0a40c2c0d00c000b00074030140036000b488000d58429100d1003803409014030703000540045010440085c43d020040070208181400c68059220f124005070122200e54000c8000d0b901c0f048103881000003110700404030311a02e04041000300825210415051303024079200341004000070301c0b13130742d1355845282042c0407041c491000c0020740313003414019582e003241b08440c0821150030400c2c00100c20000044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 316262050 1250 316260800 316260811
    0x24030601030c06260a0c17010b0322080313170c060703060b0711040f0b0402030901090309080f15070c0b04050d120b06180406051003060519050108040f05070b04060306090e0303 78
    0x4584d459610381079075500070110100d01c0c0c41001421078080034a0800c0c010410301074210398090720745d2400c11a002201c0c0701c403120004540010398140c07074070110391b0a80640e5402110000319110344a098074100020aa08041c42c407410368001c540c1c4120341000183c0c051043c00c0c9034404100594440700307201c1e800d00401000801000082d0000350441c14960800c1c52024a0300101042e91125140040d09903001140c00300c5443c0e549007000800d150b400703603204c0c00400842d0050100c10321f03580304040c0c84180b2014074001404084020803070081c81109101021904940404020305003032409a440c0c007560059440000c010843c51542aa5a071043e113980e0a0020901c91404403004008003050941201c02540b1030354131000010240ca845441040811546d50f00103010340c1403a0800204c00311800107078000801c0b015050100c3e9800003001e50304907030000d02010301c0408600e0058608510368129402c103201c041000140d103601a04014141e030030364881444502d84280801780eaa0004070760 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 316263300 1250 316262050 316262117
    0x30203120f090a020415170c031002040509010905060310050c0702101b03030f0906021b160308070212101d06090f06060607031101090f03031a010824030601030c06 72
    0xd400f00625260f8020300070110b04a011146250780d40501d00c03184020140800e0b116007243c0e008091030315050220034003c520400045081c1030030305000c40c0400e0014005d00ea04a6036503408940e0958007084803540042550300d041c846481c20a0200c503442e0000141280102c1040030700c100e41e81e00500400c0d01c6000c3c01c08200384801c804d030700d085018207411550745140b240d44d85e0110011410600082400e991501d03040c2d006c610700e650000d40303080c071007804200d00b401c10004107100150380d810448441c2c0b034044606607011a0300318050390425008512500500c0c0c504285040b04074201d01000715419408000d03146156508900e5548408022800c60303103a80000c5e0018605180003c0540b007043d00902d80000f1081442d010035003100c20340781080d03403158030044030501011307454003410040d00001d01c050140000c1c440c1c0060508a0042c082060401c1000251005c1820182840c1c000c032100a048a035556901d0504074055241c41c000d99000441d5040c1401070108132101400a20f0940b02 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 316264550 1250 316263300 316263313
    0xf030204140f0705180307030501061d0c0d0b27060117091015180501050423070f030906140103110607120819020a081501030c0e0418050703030203120f09 68
    0x100b0441d880d500c01c000e803101803e0200001d040346c0c1c90070041d01c00954861030000540c1424543c00302d0b05070201c0451500342c200c1d08420440281001d0b030950300c1d84402e50703070003240c8030760a003000074003201340051009841a024501444070388102c03030381c1d00e0003600b00780c9510406900040c44050003407411240540ac540c000340d03c060000c56568080c6545580c2c0100d2110415182d6421001d0000c031500d010200d1074031a4010311851410b80b040800162500e2980f65070421060314090341400000c04240c180480c1c034030042d84c0c0390b00903040800c03015444401080103480346d8420b4948000f00f808240d03101049100400c00710304000040302c22454024003000000c0c5000503040320131500040050b0503010071460b001d0702c00301c014000740018080a0302e85071007919180e00c1c1d01d009801c0704041581014145003568210380e810900b1404c0103403081d58080358400c4440280d1780700441d1824000c00d18410031100000303141e0f000c4041c0c400643c41442c030900c181c4036500000c41071001560342c00f00350303004038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 316265800 1250 316264550 316264561
    0x200109030f03180b0c03060607050f07030c060c020907031109031204090507050c030f090627090f0c04060c06020702060a0206040b060d0309050103051e1503010f271a010f030204140f 80
    0x50001d50740c81f800003480503203446855079485081c0805802e450305590700c00f190910410581c82c41d00c50191000303140030204408075400042c0610005070049084c5640c8000328615039101c2d00880700201d9003d0100c8040f0b0410304207441f4154040e1254586070307860400801c00c003910900440e48910140c074000c50600300d0192106207180e00c61220710b584024100106019091904000f210b020050301d22958566040c40901c0b106a00c002d01501d00e05640d101002148000c141c141c070161007407840d2030302c452911840c09000a104080c0d02a6010724040740403200345500003085032240b031040c100302803540c580c00140144082088401400305816030800c0c445035209511040c2d02290900e08a800760100ca11140c0c200d890584110390b00c0d06072191411400d0800b400f502100b07030090001044a000c0b8181c00394640500403100301489400722610805000300c1d455895030300361014811040a503580e5000c21007211441c4004ca001c1c80c1445800840040c503a18400d2140b12088440c0c4443d9442 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 316267050 1250 316265800 316265821
    0x30c0807080304151b0b070f0c021c050304030624060507020303040b0a05070609060e0f0703110904020604030c120624030303180f0501020901080108120703200109030f03180b 77
    0x140784c4088100459811001107851307290012548071400342040c1440c3d03040110b0010465101105080240b1104802c0c5000588428072500e100f481c0f401040714001503145401400d40c0701d15413001d41950700300705603040010154040701100e848070208200200b5901c44d0309644034020f02070081d40c180c1061000300b150000c0075008021012440c50070a02c2c000e01c540d1014201c9155990980311190740301c1c041504e9500400905840022480040c20304514698901c03c040941015075400343c02024007150841d12801c06484c042d650240e140c0b2205900c8485404902c84806002c1c0e803814200442480c0e00c8540b43ca40c8448401001016406903045071000e601404080c00c0f4100300540c03020151020490141b0300c00c81c810300c960f0002d40d481040500050030140181c0206071550070031b00c0d00c041c01503440c004403080690f042c100144231900e804c1990b0741d000c130381c0074242401c0c0d4200fa01140405500c010741c810701e042261810050341c044018070308055011030000510a550341000314114464 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 316268300 1250 316267050 316267079
    0xf09011a0d060312020a0516050915010302070b010e0912071e030e03030406090e0f060315060415080c04050f010501020c0f0621040c0b120f04030309050313030c0807080304 76
    0x441e01c004144140e0320368610400520411000d030060300301c07241e4441000003d00100b0b240d11001320b00e920a5071700301b50014111032001313042c2252404c5030035649069039000780c06607240140c0103010f0b0b401072b613560307040258a02c070200c0e1940c0c200d00402d5807d940050b90081a102e10070740000c0030b2010040d422564030320001c0e51b0178042d42440715000c40711070240c2d4100000c00c040d002503a40c02a400e0315004d8030308160362001c0c0040c48010041400c0100c6524002410310b10381c080c41101110391340399500843c2c010300103545488004420340d42d000c02c0600002901480d0503034140d50400c0302d584d6003521301e01624401c1c042d160040e0499051412186401203d036100c0b01c078020242d030314100e800d02c1040c24448441246040417582e1104010501401c000d40c00f0050101c1805070346803e1316080c8080390340c0c0d401005403805a01c42004502410b00c03d50000c054641c0c00412039988181c038a030400710940d4244003c071b07102800810041180720700814000111500300005504081c20250220f46140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 316269550 1250 316268300 316268317
    0x21c0f020705030106090c030e0d05090d29041203052703130e061f08061c05011109040614030a0f08121e060612010524180f09011a 58
    0x4101c4202144554003072041100a00b400e000000c1c1594000c035025041d108014002801c680240441c001d4141c0c12004540305e8040461316405400200c1c50640f026041420205c1c1c40c42c0210b4240f0000440c0c00800c60b80901e0140e0b44000700800444011419114100d8036014090306003031002c1f01902e0001400c0ea610308490041d0f80c10101300440c40d40c508185507000c502081c0754a82031020178203100400c50040c4000340620140900c0c406070180c148a400f80c5814003035400300c0f80a4a1400080d692a0041a0300c10024444101c3c0c0170014111600f0a02405100d94508100040d401070b440b0380c0350ba82c0366009806130480b29100d442d052130680049105076041c000c1080030621001300c58441c1e030702c41c58086510a503d441202d002120840c030081545004403410005080c1526404d00c2040c11070310115441464902c1170305104007181541c40701940c8000c40461000310024071444d012038024419140004400c5224003000740c241802c0c46645590b40b07580001c00b88000c07a2100078030054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 316270800 1250 316269550 316269553
    0x1140f0307120b0d0311190b060f0117060f0a05041a1e010815031c050301180b03100b032505030606090f07030b0103150e0f01140102030a03021e0f030a0c021c0f02 72
    0x51f882c058000c100107160441116807003101c1040145a243c1400e46146c0c0031002c1ca80f6400607040c41104181000e0080c0540348290801d110044c01542c0e4020014041e200142081c030624082c01600c0b13403a079a035140d8240c481c0c96001a005100341200c05002003601059481901c607880316000c0c0c0d40d814041c48000ca805000d103c40143c01d01d04c034550480104405c82d940c0076902c0d0303d03110145850681c00308468808909001e0300300d00c265400910b04002000d051030000e05c20414900203894200415a210360000c0c80030b2689045510803102e20040300c8055003540c920b0f51b50b410800042d404201c0c0e25031500d01c1c288002c1050350340300354024202810181400103980940c4030483c03817000c1c0c003a40184e10610110080251003262818a980100b400c0d660746060700420400103512402480a0b1404050307010860740f01c400b09290959143d480303611103841c0c0c0d40c03c1d000c104210551003140d1002940d400e1019145c001407000070f1130a03490301540d5100000341076404080b81d40001444515045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 316272050 1250 316270800 316270813
    0xc340b0309010e010b1309110904030807020f0703120e041d0f070906060f20060a0b01030b010309050712150c090602070b040f0306020a02010b030d020706020d050415030b01140f0307120b0d0311 85
    0x8d40d2640103199008900a4488011a28241c08000d2030b00c6a10078000c8281c0d00140820800109040a4480900c2c02c60030840000030300c40c0003090003402001000c070003060b071700005030440110200d11100c05d5010002500e10950300ca40901081e00c201d803144200150510200307100d100d228000111426407100c032030001c401c507401a920f16003c3c007a02d20b0401c040da107042d440360542c0c15100308044680d080c203092110300c242da15420b444402178402c5001b0b65079001c110b20200501c1c00204054280b69032020000c0e84c040c41001807407401180034440140c8544100440c0c0503003010117071000c130b8807600408140c040c07c5586c0c1801075000b5580c10380640d903c1d00700c20041d99809021500c41c0000c1603005000703042c5092002480c00c1040c40710346050210410003440403001410915100e941d9038107000c0340c01c8030f2034001254541c050007218200d40d2000b050b04580203288400031801599184d4844002c8100c09810108442c000f0400729409110000e91a00090155591450031002c0b10180d43c01d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 316273300 1250 316272050 316272083
    0x72304021309230106020c0a12020d081b010501030b09060705130306020912030d15060e090a1a03060108060f22030c03020309181603020c340b0309010e010b1309 71
    0x20500f100b0703046a0003603049140e1288180c00e00a840301c00400200180104a0b50700790081202c900d21388001505c032590004501410880f030600201c44222070750020006036a4904041000d0300e01500c0880c424028a004510b1301440f4400b640d00f0f42c03420040e510201859030750707090006d52000400c10f40100301d620320184d8030103081c00507020032050108003241604008074040071400494001e4024000000d20644268868441460b840b0b40c0204002a2603d0305000340c110f004d40c1c01560315030600c1644000f04040c60040390390b0b030294540711017100305611042c0403c900c4051f05081520f403040d40c06113000210384911000b000780d034020f0054038a0000c041011441d10300d0308900e0400002c1e25007050281c080301300d080503a4050354a00c0c0c21030030407069415003915031880c00021083e0700d68030407400c542551804946c19800305030750044640341c7c1c2e0701c156246440d0411114070989510b4140d03901220f2070180108561650010502424040001e90b401c0040100d04402e9906d440102c04030759 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 316274550 1250 316273300 316273361
    0x30c101e0c06111b030319020702040b03030f070308060306040b070f1e090e09030a050301230402210612070918060c03090506100503060615070203072304021309 71
    0x1c410300f5410410076500d40300c009a22a142c4000f500d4a55241e204104000300380c44910b45409001d40d02e06000760b9209180d000040c060041084003135854000051515160740e980c070020f0801d18483c5d00c40d5600c03542d032401096141e403011180078084040440001c5c2c1c80134410380070100805050300f040c0c0104d000900307000300750b01c1d0b00000c1a0702040f10004107006104601e02c481c1da001d02d40500031481c10000380300040850106210b142c0c0c41c600026210100c0c0c2950000b04108414050310454417009084a0500d1300460710740b0103001241d1715008190781d0304010700306580c203101010040050902e403503d80d0005064107c0c0c41d00c0030032070113000a80020030a01032850023440a40d0085038240d0203081041c14144044c22140b80c1020700c07101000030791008140076500100445281e41c181c1403c00410070306202e03142c2e00a60500540d00e01040800103201c3c07110b0101c0100c00451601500766040c40228421108041000b424140b02005103a130345402c00c1214250701c850303000d01d0410100144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 316275800 1250 316274550 316274561
    0x19090b04300b0c0d0f0605060421080315040e0a0b070806010306030503070812330a03150915020f0301030b0426030f0c160213060f03050606030c101e0c06 68
    0x40304a078800081a446002d064020f03001290800102000b081f0b01d0100020000c1c40781c1d115109800380b090032107690402c0c240300400601030b08010110394901c0d1803500803045096508509100f03078a40030940c070b1414000104040c4003680204541141d494100055070145001040103040548620000c000034070288042d003122845420426154089070004512103500207019502c409015003c500250700002c048810031030780e5072030b130303242440484e00403e40c0c007803542d00081d00000e00c4421110075400a51703c03003e0400d0003000740440075800c41711040180c2c407908140c85c2e0380c2e02c42800103001140615070b0080e0054800c03519020215054203070841d0902c5480200b10541801008010f0410700f01e22149602500300542e8610b409403c0e41c6020140318041d201900524245a02c02c40c802e145512010191480020210215507245071455450348201e030098021b0013040048000da080c6141488485071054a6000555581e402160340005034a0a200704220701c1c2100c0102103200c0f80b01c0c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 316277050 1250 316275800 316275811
    0x10c0204090203030f18091506030f090106122a3b0906101401050d1503050708030408011a24090627030601031101050c1219090b04300b 60
    0x202204561b14001c1240c0000300418034400703c0c490500c040c02c9585c0c6e45048076880802c0c041034803003e482d110382060041ca4030f50441c44600310380c07401440a00200c126890007900400b062050800a0079503005180d4085106500c006a03400440a000390f8841020703000900040f600b40718818155000c41e4002c080540e40308509802400920000f80108070040024000629400f10092140c50008089115103203091074295600c55440c1c5214051003903020041d50800102c0311180d4445000c161a58050310820415601c0c02d20442c009180386441400440e01c020714624010400c0b144018100801c46002e214800c800c21100c413403503981c0e40c0134180040110082c440c019540f075080e800c008086540c0c4034480da02c240010400105650004200004203117411516881a143e04900e400c4030380f10507150307030240481d041040d1104100c603846406441d03520303000031559583d412005807081e4003458122590822800c00c4400b280d16580d900c0d4507006c0d904c00001400b640311a01e036804187c92 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 316278300 1250 316277050 316277077
    0x20903010f0e240c09030c220e010b06041a0d0e0c090702010e0d0e010504030222051303080402091012111f1d03030408060a02031e0105010c0204090203030f 69
    0x5500c0918182044100b400d1014094808452500e08015a103c00001010019130740c0c0001440c050f0782d02d040c05950070b8005c002d01029803d80c1822282e80240485c1c80d60f9045103803404410050b140d034140500c0e016284054841850a403d01203403003a13103142624442900c6000300200f0032501c2251050103a4185405c02030503040e1f803408204039000701c02a1441d411681844c480780c004407404a0010091081030030310003c600315540040e91180155400070b50321000c410030b0301030401c40c030301e070190805107078030344100119541c9070303101c16003021000c40c05800510040001001810000c1c46203401030941003004034040d5039005c100141d02d40d41c1c481182d00c100107410181050426100c406941031840b5490000501c04c074100500f420f5996054400400d5900c180402c0c0317840c00c0c4201c8010b040c1074400d031055031500f01a0078000c0d41c41580c1e100460400081c0302c3c48142642211103068071416501c1181040c3c49401f00409040d04407016603240c00100078149854030038070b000302180b618669 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 316279550 1250 316278300 316278311
    0xd050a020103050c0a050d0c0905060f0309010e0d0206010905090a0f03020d090906052b050102130f1a0f091504081b12030403080a05070f0c23150d020903010f 70
    0x3000500740c0300060108290fa060611114080c0781d0404191890742c2c1d0580b00020b184004a003040f1514480d40e80083c0c4c014a00140300364112541307070011449a011800240a0302d0308080400e41d4071002e0000703540042c0c01600050091149541255811a101c40111340f01030500b515171480007058010100c016a000c0794020102d5a04641e00a0040420b150100411450603010944820708107164194051040d80c00b590304284c50040e11a0250b0003200842d1070f03015031424810303918418021500d41c1400354100207120340f1601c100e01560b50b0940c0e4414104074180080141d15000503810300c1d07104460a00c080c004030441d0000e04002c19411005014024411440a8191903a00030081c00b0f0485a43e036031080703001c00411907080725400700165554040d02402200c0d24002c0f03202c001d250000191811045c05800000d090540307009040d40e01074000004d180d11102015640d001d500010714124061480c002100a0020300d0205031000d8940804200040e084a086031171600c5902c0d901d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 316280800 1250 316279550 316279553
    0xf030f23030f0a1806050a1b0c0b030609010b180d11030a050d11210306150406031a040e150703021308030705190b060607170711040f110d050702010b0d050a 69
    0x344d9a020a044031303c0ea94a0383d103007402d034001c200c0c3c42018606000e000c020f040084030b030540355618146650300311850380007464032881d10342c001e5403041c2c581a11031a42c0d00c0c0080b407807176244421102a203038490080c44402d03d14400707021103910100000d4907030422000700112151018400201e00511a5000c4c0180d80b000c0600039213100e1075001c07100e410b540000c2c1102158200d5482c22074415240c0450952a40c0e034840c0043c00755000300341c03030701c20700540480c00050940d0503400c441c0c0d81040540142c100b040400041c04112015441c0100c0190311684e9500c8030314100c5003105400c480c241c900585002030308440301c105058268082c00c0030341c0c000a200003d004080c0700740c072148a062030710744503480501d0f00c81c80c00c90b1030041d052a00c03a0344001070960410451420b10300120311100d40c45178071646541000d1841c0b041c44014140a10308000215000074402d01c540080007030108840390410516a40306001420000e05410640d907903244000365039a904c81e01c0d6035010313203d54024070043c1074a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 316282050 1250 316280800 316280807
    0x30a23040303020709110421030801050108131101140703020a0b090109150209040f0f0207060b03071815090516120c0806011101061a070c0f030f23030f0a 68
    0x24551106864505000900009601144400407511281c0c408911201d428800c40d429110384c0e84207200f088081d0481c18100d900700c4882120280c0a0349a1000320303039071100107481541c01200d9100403c4034402c0d0800000714100c02c448451601032401c0d0802c56115220254143e220000981c0940e122800e43c204001c50365030b5040d4024081002849225070a5590311054500c407040000415004503107000341e500c540d80803414801100409024416910300400c1c001d5024000685a0034104000c1c410581800203010f01124001d03014286c1002501040320010514406454080c207641003000038019210300807140221808284101c03480c4501308040d0900058034100e114407400c1003c001e02c195084400c25500883c2820003001c7c40c2001c40c45c850040c246500002d80403404422941c4075003002102911b1514441c20030f80c01d03aa41c070b41142205012081c031004000b113000200582c00038048100c00c8084044500713403d40944841e07811542550000b040310020704101040b0320212660 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 316283300 1250 316282050 316282097
    0x903230105060d030e15070206030420030f06160c022e0e0108070e131401050f040603020609120709020a020c040522060e070e010906030203061f030f080c030a 70
    0x1044a0f40308680c9280d0307401901c00c03010107500c02c3c842c01e05402829161007138001102c4425900810080d42e074900780c90b020012042261004c12090b403000542042e90030005091460103440074014a0b5903612007810301c01e8481c21002c2441080445184040161204083e92400c0c0c10030400f041e0b40d40c030070208180c0c070008003240141d003000a45208070380c050b604500b80c6a04001340c0e00c2c0c00924609008003142c030380c10130403000321211850a9841500300900348959416070b001115212078000c404020802034a00d603000107984420100b00040440c41c1c80104d0850051121040e2210143d032501c004049030000d02d40070340542c20a00b05901c06240a10803964400d0107160205610030004407405181e240c0194000c001c5603668081009074001080421f00a20840048003500e607150401c4a000c1e050500c0124001d00c500340104003440002c0315000180b00c6040680d50b40280380d81c9807003290070681001510311301c1042164542c013900078001041c01c12851784964100700103290b62440e1542 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 316284550 1250 316283300 316283311
    0x72004090c1211010903080a03020d020c0d09030308090f070e131703060a0f03110d051009050f01050703060803160c0504060303050c10020a0c062304030914030105070e040504030903230105 83
    0x5c121041440000d00100588560f03480038540107848100e0440900020b110b03031101035102d40705d142e0704442c01680c000f50a8041e00d10a0b41c0c3c505071a01c40130703125941c41d02d122100b101d49070800340e4107100700014003220036440040c00c00c400742030710345c2c80c0c85039130355a03003401c1d00ca9a04240001c00c001e00c07420551800340080c11300202984007a0301d1a15607400700e110881130030344199030a0f803803001444410400162109109813080225402c01d01e401e0b552a400d2480c02c0c9425400e203400030340240e009119040403100c60501440c41c00070503c902c4410400d28078800c0b20305404092000c42c09031124840c41000c1d40c0b09440e01960341c038590500030710382007103e00895003050041100700d880c107502c8000156220341c4a000480c22450700c80c018003410781d042d103280b041c08001504110a043d40b045100c0115421000c08a052444140c20706090341d200b1543c2d038001c03640e54811990305050640c44a940036000789025602140c8a0340c404101d064030222201144243c0c00c0394444c4803800303204064010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 316285800 1250 316284550 316284557
    0x31d1f030e031c020d0b0901120201030f0c0c03050f130b07050c0f010f0309060209100f08010e01051f270501090506130e0c040e072003072004090c121101 68
    0xb43d201c0001069200030101d81245254010840b5001080640c00218041000503c21111982c40301d0311000c5100c141901030b40003c2c1071108002ea050750501c80c0321803e126540c0c1d03880e14202c207500d0a076910303072020704440c9002c402040321a8400107000c0118000c0d004106a00d0340e00c500d281000703403410110504180c4215118500810a40e0b00a0810f0003011641d04020501c4486400d001d03000340504203045411111520110a038107a01a800902c41320482d2685c0d085640c9032042c40e900a602400b949811035446040500300c02002e4221526074011490590000407004071000c8040628a0706001e424486071800d004940c1c018025001610050390354608080c40305550f0001030381303648114601140c1c4500820103641165040328040e000540c0b07040c00314140004000c10f0000c01d608076080040f00c0c10141034800001008440e842d82e000704105242c10740118003160a0340380040c1107a40540c2d10400b81c00001c100390415001130000318040c08101002e41401d2005100342c40340c0c035040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 316287050 1250 316285800 316285807
    0x513050f0a0e1002070c05011715060702040f0915240510140f04080d0f020a02042d0e0c0105040f0e10261203090a031d1f030e03 57
    0x100e00d00d0250380e644040c01a4012800c60580960a41450110f40c1c4001030180002804400e101c0c0d006420400c0f11005c1e80d56003d0385454a01c0120403030405d481101220f03250f090350300720700c0c5494030117008624001000054041ea0109c100c00840b14100030403a4404c0443c916060320201610038002d410b60080060881c440a540e07200800f8601c3c0c0c003a291241890020b2200c8141c840d011000a207032882c403125580390750301103400c000e07a00203100c5c40c00d00d44900180426590305c602041c8507142950380081c20030050a42c200000b40010255088519200040c00c03034003000100382541d9140300c08400022580c244082c05824a120004003505003d070400041103190030007042407044480041290440c1c0d104c010300da014440c259840014100b42c144403c10700790550f2942038007070b013220030215200743e2110f0159043ea4002103a182d40b807a005007001e040030a002d60807800ca0902110140320302030b680070001503440126800c80d800b01d00700100d07071190442c0d010b124011032014200c009505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 316288300 1250 316287050 316287061
    0x20a020f011b020d0606030606120c050a0b0a030e100518060f0f010b18092d06061e04030f05010c0807020a0807150e1005150901030809101106010f051305 68
    0x40012038207000303011301c1d840c10aa07001e10159500450185a0140050140035968003003524030f070707258010075904090352100000706860302c0c0419004941c0c2c1c010700682044e00135030041e801040c06001030001c60041a00085642c2094441c1c82d00c2401c400101503400e008001800703152160090054210b24132410510030020814490281161a1000180d984401420030041403000d24105250000c2450b0244500801c844090b111020381701360b0a207880074648010200380c9001501c816800407010010030550030084000c0900745001008460302d800d50781d070b6820b8443d840f070030000d9616965400c41680d02c0d55000c440381d50050001d00c001c1a074a880307610380c45070ba4454054014a603d150100043c002a60740d00f080f4104981d940c00e5a100318941c1c3c0c04180034100495003910007001c8035064480742c4c0340c038410f41c40c140c903008400c1e07506055040d004d1010130104000141d0900070502c2d001d0590b0740081046501070001c000680c0b081c1807822040c403234008105d0b0001000309050104001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 316289550 1250 316288300 316288337
    0x103060c14090d080a2a021e10031a090a02030f1014010c0606080a0605180d0e0418080408010e010b04110901141606021206100203030112081603020a020f01 69
    0x24a8950429415035036011031000a0b203a008480d5903007240b0511000681101080b46e414105280b0b000791a08104400340c400c200340854504250305500180c04001c002c00f4a100390f02034001c4102104424241d801d00c2000a144160221041103005400008010516890358241c0b900510030a007584c1c0e01034103014070106145d14440c0d8203410089034000d107000780182500010004c0c56140142c03451040c2a0402c0c1001d00411104c0c3c01004090840c89070101c10005400d03043d5910030b94583c07000000c0c80c402c10000c1c01c100c01c04079014001c0880c40c9130220300c0c8980108014120b0000000c2c00c051050300e9542590b041c40106d61286141841d8078070150010030071264001424a4404200b8281150161441c0941c0c0301c22144440410022001c1001e00d900030311080701e03905900c01483e43e8000402070018100102c01006070000e00041140f2010350000c1040c0b984035004117400c2049a103816081721954032410f80060b4040e224110a500304401400c480d80d03000e290a85000441c180c008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 316290800 1250 316289550 316289569
    0xe0601091e0b0307021c08011a18150c0c1804080304030207031e02040b0d052d010c0504030303150f0512030c030304110909150105040b04140103060c1409 68
    0x8518002200e0501c1004030162001c03400908950301d0050b440b0f0a005070f00030740d1951010600d003000c00c4180039808100780900da1003812a4205503150b003070701e0301201040890b50000901030848031a803190135107441d034411250160385800804403076220420341881e20301e44a950010075005045a03a00160800c00d507451440d0321581203070350155240c1f682d00c1c0482c07408281c0e61001c0c14030b00702c501d500040b41c010080e00c1c0c583e41e4002c46041c0308071003c10040018031085141c00410035072041c0c0c020095684644520200e03402c00440700034068410711982e0782910443e180d41c00c0044c1002609004040e014070841d0154107500da0352804c028100440301c0300704034050090038898551124071000300d100800849411802c4a41540d40700d003440d10384444442d0f18000c410348914547c80c006003a10400065148640080107030b020717520791a2505110061501c0d0741c0083c4c009454203122030b80c024001b0b940c54000c41c860100011404411900106109024041a10803c00400c00c8010940d9506040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 316292050 1250 316290800 316290809
    0x170601090606050d11070f080d0c050f1b160915120f06020904020708041401080f040b040b0601050705061e0105010c0f0b060a031403092106150102012904060e060109 73
    0x83e113455000d112244030b0207604001003a8503841c0b50207d0810035000e001c1c1c41d203244040c105005800d0030031820b858a0180f94810507802009004001402603101ca0100000c104401500c07400400400b9100700c1040c1a0480c2500d5030303c981180502c02d105800306002401c00c1400c2c030424007403640d2000905100600082c14180e00841d800e14666965070440d0303003595020b4062540c0f541e85104071102003075104803241c04105c120001512150854031043e2150783d01194451140c4c0c0c0da03a803880c20406014000030304100c028401c08000900802083c0d000300481c916040820313035030031500301d1500c805030001410440310b1418000001d10036900e1400b410b50180741100913580d40c0300418664065940064424202140f004924440200c0146050103090347c51210399030140e078a1352260f8030350601c0c061340e03584a00000340c20a51342c0d9140c0c1d01d450105100210b04a400ba20141060140b08005081070003210b000e07501d21403403d80300e101c4c000c001113000029645019800604015194402d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 316293300 1250 316292050 316292077
    0x90d20040b0913050c0a030f02040515011205040c0b0703200d0c0305160807030f030f0504110d17040801060e0906280e0303070c0b060a180c030e010617060109060605 73
    0x801c80704004d400c0c840c0b4801d070726014005544403a56810240540004444e06a01891400300407400759440749489038074100d41a11501480e0a07000c0061004281c024429100642d420f40046184c0070f000c002814000d01175540d900b0803540b40304d8541805880c030b8842d4a441d074450140c0c1c8640d25000321644e2400c6815003401c6480d0780d85d21070481141c3c4c8601e1002003441c9000036044c410903030041d14200c04040603030340410003100d803c01000211032050701e01500d00e0304600ca08005034504055140d0806200d1400000c010308920048210354000741c124000a9440310414440025040811940038421f41c0042c05c041c103110f9042004000d2241100c026480d403035044060007150307504007020600c2880200d03552480c0511008007000300003c0d00319820103840d00482d2040c9811300e15501078441030495912403055002184000384142d046a80a00d901ea8026010840c400e120300d500400404401c003141078002858603007800301c144c102d0208036282001c1844401d034801c040c0c42110aa40070f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 316294550 1250 316293300 316293331
    0x20f0d020d12020f0d0c03021f090b1008120304020603070c0c0e0108060703051510050a180306052706070f030608010c030c090b07050606040b06090d20040b09 70
    0x1c511080207005014119410302025a040e80b82e00248503401600c800041e41c02d44115108101c40c20300d1040c0001d00103a000d0440d0b040c000040c50051040070002c40f0707001031042e09603500c0d003190080c1261036000b2503020b1001080b190710b0510220405400300e40002d4038524042e80000d1070740c000941448c04014000c070800040102c0d0782ca4100c080d160103858503e0941e510b00307010360f5407007049a04200003410b00011400721072003901002d600e004000e10f1003554410401040314680c120124580030003920f55844190080700304e805a001e14010440840d00f446d0507101100050882c02c043d011794052207a81b407078200e401113002500079000e490500c0b0728444c1034a003200a0000c82c3c00844455181c44601d00c2c0d07603a055030141e010511941c031a038004036950303400c0074240c0c0212000074225800200004135103140640c00803c07621001003125050242d481c0120380300540b000000c0750781210b00350017030f90354803011010340402007030466007813110201c080007141c0040e00162510140d50313080d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 316295800 1250 316294550 316294553
    0xc0703020106031b09151203030c0915080405010b0901150c080702060301081b100f0e03010207080c071409070c02010309110405090a02040609020c03031803160804090c020a020f0d 79
    0xc2d00030700001d50300200d00724883c6109803ca41154032052003800e0000e490b00e105909000b00f00c80840c005c940b4020300805598101d40c400741c01a0004c10b40300c07420030801c2580414020700000381b81010111b01d650720320f19450207180c000d0850301c20103003952040440b0001001121030b2400c42500d2000d540c50b0840c220540f40c50400258000c514009501c000080004181c1a030001100704910081c051410203c80c000018002849130320728021000540c02103403004a18010b030602c04040c075015000501e03112441d00c0d0f680050700203066069454101c00802c2015450440b98401030b0002110300c030745c9608002601802e0a040d640d0021b0502d034440c0025010f2060804004c1107082c005070050001d80b03480e00351f440d142c04883e0001ca228503d060008165080507200303075054104c2c088003c51654441c0c00100076010900c091581140c030080001d0840d100d520b640d88800e2074810703102e5546641c01c1031103510985e00200a0201190f010340d038080f02503600ea400440040b04103484c4540402c0c1107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 316297050 1250 316295800 316295803
    0xc0a12050703020603040b04050d03090804050f03030d0c03020406020d0e060d0504031107060818010b18042105030a0f0e0709020c010b1c02032803081521070f0b030c070302 76
    0x641d02c007a40c04100801080309101066540c80d00c1503108005450320700c1803d0b4020b40844003240b00280c1910018001807202c0d0400761401e4080400c0241224104658880c0240542e0001580800082e402144c104412030b0108903219014a580c100030b41003544840c0032a0242c007840c0c0510700340c42d84400c040780c1032600515150507503021420540308032588030400a411000240c8100101001030400304040340410f01c82e80c92084401029100c1c1c0300301c1c0b022500704610001c2c0c0103540d60800c05e071200000300014155800c913180203403a002c1c0c480c40c00c10f00704000c64074150b000103983d600304146410040b8000c5050b00c2560159040161264402c15010340104412061990404a448944503450700c0b0701301c13110142c03842102200c0b002c2044800d400450b0f06140b5941e106d04038007007011000640140740090340314a0f641280c8070308801c5e08000a40400203050300b403a50f039092801801d030004d402e1003540090481404041c02d0680342c0f6041c000c0520008202c50f40091020030114200340c070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 316298300 1250 316297050 316297063
    0x3210507080d05160302040e0c03180d03091110080604151205031b0c0603070503040f021c05070806070210020c03090306010f090f0902090705090406051c03110c0a1205 74
    0x104841e03516203400c403400c4000001c01d800d81e402c1814850051400310b96a1090084809880f10300c581c0c0031942e101d0724000b08141d040948030b20b010b40d2248498017103501e4200001b400754480b958010a880380c032030420403102400000700030301411524600071002e5800c0700925800280903600010400d80424440c032010350190080c1061110401c0400140031000000d0100000d00c846949900c803449962103998003001000300e50010828400524203502401c080c40d4824007a496414903114150700140303d020502a4415004d1180e40b12182400703010840400a005d001008104904003140080c0d030b658040305030400d5040d00043d4045100300184191181580003400321542561507000034214480e01d03000c0c803000359161540c4080354414601950701711a4002e801c0c21981d44070840201c44561040d5800d58100ba211140000d003034a4400e00750840015500320841071f0142803070020509100c44142070042d03803213590300015550752180000704440c400f440e60156140382c0e1a02030f08114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 316299550 1250 316298300 316298303
    0x3203061501200f010b09100f18020403050a0606150206071e090e0c09030d020309090f06030a1a0601020d0c0507060809150c190f0804081b1b03010501060903210507 72
    0x180c202026a00e481500804405d100869070b00c42507507560020b01c0c1b40507486108282c07080c036901c903042101800c42580301071800b0094001501e45030702e98440d1450851018400c4860340d550b000c041001c96522081d800300d0400c1840580098206240003c001c2125001034908605111000d0944140244559401000002e003020710501c1c0c00485080c09400c03640c5035601901408061a0b010781c03020086400d541c5006201c05041e8a0302040022801801480350703030184580d800c0360b4041241c040d900e94082d42000810303541460907000090520040d042c0f0306040c8600b01c4880c0703002410114000c4191000e81c03610700c0c45541c660b01c11610b0300e1000a4044000e010140620014000500c003d0449000012030140c0742c80c692a021504c3c8810103645034005008500450009101030008112030b4050145010f07803808803100050070016284001c1d6100088041c4419503402e00b0f00540d4018186400e00c4221207140d902c45e80d02c1e24041c81d440038030283c0324070b402f44100c1c1c1c000c500b51607015 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 316300800 1250 316299550 316299553
    0x4151b0e061b0a170c06160c050105041101030f06050a170a0228060503090604060e1f06080f01050402150d140a05070305010801020a0507110307320306150120 70
    0x2c2100e900c0254440c8141c0e14141c800c2c410414100c070700c00200c203040780d2845115000030845c6507140080c084201508003001d07010881c210540d080400d90034020107000d5400740464a1220020354000b50031103031110071138022141030503c00c02c40ca03030b92030740c61104440a42444110640081032500d051652128000794031003280030302d00f85014103860301c11691400308418240e4054070384000343c4003408229203400d4aa8400c0c0001000540e26030821072440c0d042504403a864050304803040703038a807210714000010070b645003402c00004808000001912044030000c1000b03003026008500c0d607140030780c005000c414000840504802c80c3d640700310030000900d840342c001410a101e203600a000140c2d2a00d0000e030518001060f4080b041c800c8602003c22600c43c640b90203000d69400044042c0909660340c14014020002860034803440e40d015420070103003c110400304000005607030540800c40c0c443c000c0d84902e08000c611400c440d48044180d0007401c000c40c00c1041901e1004068030000c81800b000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 316302050 1250 316300800 316300837
    0x80c010204030b091005010f050d050709020c010b012007030f0c05060723070b1917130309060c08090918300f07030305090709021204151b0e06 63
    0x18401d0a01d1240d0041113214144c4818407142c2c140e010a840c028040c02d2200741002d0700c2040903151407404c1c200040d00c01c80a54501725038a1205404a030000c0101d1241e594480d8502e000540e8000a42040905d1900030103850503641c14003d5a01e00103400014022182030400106029007211000006e02008210329a59405850311107440745810201341a407441911074030910f1540441e00d0425500304100700c5003009001c0240f00c400544a03030744d00c1c2c103020003070003003141011294454900c00e80580009118140052400403d240c4869000030200022042070b1000524588201e074500c003401c441082d0380c1d840340b4215810008000641d040c25105204030b6404150744401d0700320484600040e501509a400a041e945500c90b010340030005071010842c080010340a0392001c0d401a200300704941c599a00c0e46080c00c2241e10520303c5003911403481d410041000a0460010300c02c4040080a01c900d080361000340d03030100100e8071500140510140004460b8a403542501d00000f112101c4611 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 316303300 1250 316302050 316302053
    0x150e03040b0d09030905030a020d031413030b011a12150a050402070f0501050a020c10020c1e03030405100c0e04050405010b130203060909031201140a0b0f03060307060e060403060504080c01020403 86
    0x300640c3d44210b000c00c1074000001114580420750714000d80c3c01416040c40114a594101c40d007101c1014410740050301800a24207544000c1c83d220051032003460203035042c1d414000080c2c2210b822032049000d40004100e01c1081140b40d52000fa08007050002da4070869540744002403c401303040e00060b030801d2000c601c07402070108403c1195503036401800200b04607194080b551040c8d210b2005031b191140c0c0304e00b80400f00d458140d8020910040d000c000c3d1104810f01c04940f150400b1485041c5e00240d00c04030030b20040c032206120743c54103840c812104105052000f48094101201000f02c984510740d41c0c8000390501c8000e40003840c0c0004028030805981c4010446203001390010b43c1d80c00c0c01031004d40d0000350b0404c000400c82c0d0814440d450000f116030b203400800d00a2030801e0f0949900924401400906880c00101501e00280d48941007030300e0749840010301d0310b00750b07035544035504101400510000c0b548448045800780c0790890707008240fa69070b41c240710b0001e104102d101e2032a076100060000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 316304550 1250 316303300 316303327
    0x260d020304060b010809030a05070c03050f0d03140103020d0213200a0201050a0b0f0603040501092003010b3a0c03110a410405010f060e030604150e03040b 68
    0x1071040380b10b00c1080007019a610011105110101c500203840d038002c10080800c01d019002900caa503200b41a00e00400d0f440b580c2d41400d081a02000b0425a40079030480d2a0381c6806002d000c020f42c0b003039520780003250300d15000981d10090b1050040e008040111440030b003018035820103a051850010b6001d9100b01e111440302480d481618000c0043d4645004500901c2c068080c1000c0e03420010b0903600750910707000810030150300c0604121499035170740d658000007640030000d00c0c0c40750b40500c2c940c2440130020700a041c00d41c0d011900440c450325035030761005002d040454030040740c00345642c03a0002034024068400c8a2540307050f0090901d4454603000000c21511914418010790306031076070a10190b03100c034060cd0b0907469541c003040c0b010300c2c15061181410001e4502184056100c81e61240010a20200d0102c078000c0c1c000b881102c0d882501030101a42001000103001da0035001401c091074103403150b0010107021408200b0706074032000c1c442e803c95010015980a409180540b0b40d58400080020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 316305800 1250 316304550 316304557
    0x3010216050606011d0a06030c17040b010e0a1e1503020d0501050108010e03070317060406091802030d0e0d0b061906030606021614010825020a0b0606030112260d02 72
    0x540000c5d55036103a1290034500d0808215130000140c88411020b0030418240e01030109155200c1c20012101e0000c02c00b94500004140958000c800281065040203500d00401074024402032030681004c0c280b440c12803d10034442507a03404450001560107141000a8125005903c045c2d401040f014030401403141c107501c1a4100c4650700300802850010003892a202c0c0103050b070160110707441350700558115900b0341c80254086c40003000083d400380c40d100c07468221812820260405040341c1c0c4548110b04003044102020704040c20800382003c00500080d501d2290111b00030161a070b04004100300c0d441d03001d40c45e1030003003c10620310405511902e0043c02080303030348601c000512642d901680303070034141c0600c0c0042d120501c4062480c044000010349500d80c0140004c9070400d0303e038070329494040e8941210f80010f030b000c0c5d0140c06141d019040038035504101510051188504100400401d245211010450307940301d4a1070f9004e1443c6004d10040030401500074259076000200010318207100d9009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 316307050 1250 316305800 316305811
    0x140a140c01110d0c0e011205151005070c060e130e0f01021903181713080102040f050f0a08190312050106030c1707140c120d02091c03020615030102160506 68
    0x4000741c04c440d5a04484003c29031880da4081603010581282d0117085070419a8490001c10311084002030354004240b042c03110b19508800144c010840d80d0800840c012480d0090600f49421103146403044002011021a44c0d00201e115940340c00d540c01d009014400380300003a80c480001c6448030b070301080383c4e5031a1210002d00c1c0e00080c98518280081550070024081b00c0b6004100b400301c051100d610034000794440072804400c3c011000c0005201c074402d00040c00070300b201c07400c041071841c9080f044c071003046007a03102c60b4820403121006100340440052055625036200c2814107155401e401e0aa0b0f5036685a110030803035a04240001c03550580541113140d80340901c0c1d41c0d68114050302481c0d83e070506001d458000015108040d07006410030103c000e00781c3e0f4075154064a4581900300e642d00c4003a841420412400707500801c001c1f40c0b40c80d02d010180804646203415150b101280d503402500d82200a012030006100c0800220790364400b54140c401e0000411a14000003002d414240e03514442101c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 316308300 1250 316307050 316307077
    0xe07080402030d030509030702060c0c03061603060e010506090402070312060b0a081e0402120c12010b030105090729070b0a09050d020c1c081306080106030606140a140c0111 76
    0xc40c80500b0320034417480740b0451140c0091410f149280d82002041c0d40308a01a0304207114456000003250303001d200b40c901452080801202c514550ba002800f95808d5911001840480d600100180d03202e8404a507059401101c0050791244245025142441e141e0340e0b490035245407c3e400700d000b05c4180000d1018500c5611944000d0741c8010011110000c170100c0301c100c2400020104005090107596409403074034170001d0724840803c900c040f5603020f03100407031076405a4584812190320300702845440c1e04440e4031005020000d08003540c0003011420308250fa03000101d0203841c0e8039000010390580c2d01030f03039129900ba0300070300380540c0d150f01400064100b5200c0740950079951072114000106003886510181106644200c400c0c83c8120a40c141c4905850b082010000c42148200c07822584029040c01d0303d40d11550350500340014112a0190801400c0c04040c0c0c0313101e0922004001501d064049074a40204c1011030480b00b01101d0061306102d40080d0300300450703041040f01080c060035002d4007040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 316309550 1250 316308300 316308313
    0x61410091512060c02010e030705062a1803010204150309050c0603010f060c0203010b180717010b040b1606180b0901020304032c1c12030e030904150e0708040203 71
    0x18401c02809425214000101c0201c03403140002440c0f0790041c04191150780000105805100945403e541c07009100310f031681c116070100100e0761000c003145060180100410316031582e140c0010801849114074188198040e02111103aa5509404543c0034111402c8451046810036001078060519407600b02c846002d41280b49082d8100713036054038103c4404e040643d075070300d01e0002d00380d451140d42101641c00d5500c41c1c0011040b9143e001000e80c55034481b50300b490342c0340360100e40100b4010290906140a0803030500400c11060010309690542c4c1c8440c0110f59252842031500120119103200200360a003400078107401254001c41180e040c6000311013040c41c40d59900080740c00c03440110780c02130100d0130b80c2e8440392401201240c09000000b403507008990f07114aa4000517030100d403105120b030310600d03a803000c4010808010350f10004030190782401d01420b0300c15002c00303403240101c80b0910f016650360350080104001c13400e40000200740101c0421018100040300404880d0300b180d00340e001b4810302 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 316310800 1250 316309550 316309571
    0x6080c010c1106090411030c0304021003020f071103031c05060a080304050a03081615021c05040f0321150503010605030d0503070e180a05060111010b180406141009 72
    0x841c04000500c1e40004120841d2024004205140d00075840454105581d2919082d8219042004602446402e010796480346420710401c000d8694845400702010300600015041c0d0703072004280c8003030307560007810a110120340502103417450081050322000d078000f040740e8a40d0290390358400c2c1d009940030f841100c612a00c618465513244528070440b5040180303d801003021580b8000030f466003000e0755200c1091844d117a252088440c010005440040d9400102030002200e002c41850307040000290a000d42d00d4103442e209881c80c0c0e1307501d015080c0500106035001c0b01c03130454140826038080020400c400200b082d402c0f0210151400742501070740c60100c001c150307460000358220540c500c40d641c15140d562012001c80b880d810002841d900460380d005945e8208024a00c400d21403002c0d42400500f500d0904001400c0c88211078003840c0700d91414401903043e03140c1802c4041c440310b24012603602c0d07440310702d0903c00030007210714094884200c400078000761000c0342d090380003102d404072014014040e81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 316312050 1250 316310800 316310807
    0x140a060501020d050f0f0f181801080d08040302120c1605040213060e030304170d27050108060307080a030206091b100c03030608010c051b030405030a1e0f030306080c01 74
    0xd2505010400a1007100494802c400050134441c4a101d50310303003800c5540e80c900031140c1140100c07a035140b11113820011b1301d00341500d02601483c0354000c0c12703490b5490054900c1c3c440e85025001000c1052660024091500030000f4041c0c0c0c400c0642c0065031030029600391034171010182070b044102d0150400001e50380c98a8020740381070300c1242001000c0285051010b44a408c02d05110310380501082c000091800c00d00c9103c240c1c10510701026000c0030000c050300401c8071407403458511b040220949203422285002050f241030b0355003070a060245da00d84000207450000964040b141c603110300102c00d010142d0101e80746005404080c212405c01e040000d9103a07502030000f040c1c1e07070008001d210207046540319020903c1198082c0c200060b105441e4003801d825101a1035605011810020308014440b00040c02508058190b9014605250411001a44440c034514014104a40300300801c501c84d004101402c09070741c1d21640c01c1080701403600d001380152000b4818100e450080035480c0f100e5501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 316313300 1250 316312050 316312063
    0x3030f0207020901050108190504060f24140616031e0309020f010c020409061a0f010e0a090506120102070b160c03091e050901080319140d0c050706140a06050102 71
    0x2401443c03496240e00304001161300480051060341a45042030031059020254412a400740340a5907020a180581c1c0ca9254183c815600c0405a950940f04144141c005d80c00d01034801d44403900c00c03010000c492100011030034054040c007101c1000418003510f08054001d94000c42015080c5400c01c4007544044c0c0075402c403100c2c40800303500440795213448540344d071045078240c0005200070070001e400c1450703444e0703107080315034020791000305100e0403602420700d00c1e20301845000a002481c262070029480004242100c0c120311802d0744164603138021800d02e943c1c1c251031408500c40b00c4021502c1e207002c0c5c20003995030242950340724448420300c1400b0007214802c40c00000d8540c1c05440f148a1189411a8010325110040302013051082008000c41c190792402d40d581e00131b10060b0300440e150b5109002101410880d442e42d081800b40040c0004c1602c034440099550907044101e00045403400010309903901d10490318020b04540c50100074030007540000a41ca40030340c00d50401044896200e40041e03a9541 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 316314550 1250 316313300 316313303
    0x609081906110c010605090112050c0613030210080403030609050403172d09010e060108190206090a0b0c060c27040e030a050c010c02121b0a0212070303030f0207 71
    0x1049081240411030900254101040c4140310000310059006854010b54001e52651600c0d03075100c070750800052030503204881c09810b521114a9124609941d45651090300c0f81c40b2a010703190200d14251090626136103900115000380c1114411541d14a00510305602210210007180c5030070300c04260f004041c8074044c412603060300d454408055808411110502c004c10501c075120407200c02066102c484d40c01a0210384100b1005070042c101320801c0b600b5285070003161291039100c580100300b4950300091403003409654007010300c40211103001241c014410710b80501e8201e104040001142c0001e2001800100030140a5400c1034503844040401c0388254a10501e9041403138078400151040c40d00da101500500a00c0061003007003040400c1c2c116044030114101090000c00c0000208800380541000c20301a4400703815074050900c80e0758814000c40d190709090304601100b00304a810304001a2050940042c01040c0007505901810340d0b4101502003140040e06003004040d0072a0030340243c64a0a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 316315800 1250 316314550 316314553
    0xb03180102041d06150d0605130509120a0201111b0c0102010606020d030b030a14060708090c0108010b0a0e09010807060f03020f0d15030f050109060b0d0507061407050102160203010501060908 84
    0x2066031042d20b54910f4050720319a03100802c40c12600d40d10f044000100752200c400300c40803454918010800845104000900340028101420000c6808002c61841c2951514035840c50b1500d010b25000c038010041e045004101c20000214400c2c008e02c01000c50b100d0001e090100c80070907540c0c100482c20380700d040c411100580e1100c0520f0780b40e240641c0140c0503010008e4121000500591240c6885401c02c019450040c2c2204007440b16a6078080d02242d0703c00c11400040c00083c0f1240c00003880c0400c14410380c02426000300c2c0146c09a4418010040f07003901c02803c000c100c0d615032107810b85818039441441c02044201131014201c0b130080c02602d402c1a003845000b400c01502c0c40ea01c001416003425820502065028040000341a01e000c10401901a0000048401d003600d00603089841080d00c445c4218002c070050f01c0002d030000303210701c143c90017854001031201070800c41c00b900d8083e1281c010103075400030800301c8050160b1000c14010030b008900070f0000d41da0361001070705d4a50040c040d99042c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 316317050 1250 316315800 316315829
    0x9070c150b0901231c1b140303030f0408030408090904140d0f090302270a051005011e03090501151206060506091302030702031209010c021c020312100504060b0318010204 75
    0x46141c540c2800b80805c1060307504550340502960307408103000c4182c3d190f0306604240c038010711148071484aa08240030040d0015465402d04208229180a005000034030144002000800b004000e009a0751010030140c4240f100d41442d1910f505091038483e620307401489000795900301d803489803c0703034902c001c2c00d91a0480c40c0c0381141c00384180b01121026204400a08541072200d422840c60f0462150188100008490402c0c0f45c0e090122340555100904002000b0288415113030844045074142000d0300340024505400d24085c0c0c094581c0795190681c1c503403421070000e80c0d42c0146400d41c0845201d107004001c0140c64008202c0c1c075004000d4580e13004211070701c0740300414083d54000c40e00400a80100c030b0034012980346041602e0360858460303509035154400c180c0003980401548a8a0f4031188865000903440c0400a5484c060b030194984400c0100010074201406107030907501070030014005202842d00d0389546071740d0398030541d40f03c00145040c080010700c0910610907101500d045000c0e0082 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 316318300 1250 316317050 316317119
    0xa020301050d02060906042402010b060f22080316030e0405040b1f080601030309060e090c19090506030f0402030d05030702120a050d0603050607030b1e09070c150b0901 74
    0x90340e42185e416240c00000400011691000d9030001801136160b0324503c0c1c0c400050000001d0070345560002050084d20107001d800c500c0304100c0103980e100650045000e070406d8104120f1108844d04d5801071006000000d00e00c030b04441ca800302d41194600a8640060150b03864080c8811a101180c0c00b401c13100c07480c80800e003408007403544a00f90b41c80c000c0b80007200c036844825080c144a020b900450201c3c7e4001420003020390003120002c4850b1080300c0791549850400c911508030310690040390b030007004000d08551340500941550000e8000501b04d40c0c1c507031800c81441d92031040c05a03400c1e403217031142c4184030400314800c41c02c5900c180c1c0c50307501401188803027413030718081504a1000e0105000307086c403000012040507c0b850000350f0066006002178203080380c02400319040700700102d0240d031440104201220160900904001065070f407640e0590702c014017261000c80341c030b1005001c1480300c50100003607900c54014825403801114500c1c09646c3e2100da4140c52508090740e2000302040d6230040300e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 316319550 1250 316318300 316318309
    0x12030d060e01030c0311030703050d0804150e060406021e070b01030c0b030106050909071b051c0f020a120212030a0203010504050a02120a110c0f031305010309050303040b04030302070f050d02060a020301050d02 92
    0x810601b030203011507030b10f1030300c0c4c0d03880d00d091450300c41c865000680c12070308100074030200ca602cac3c1c10f062003e09000c00c204102069680c0d00d405c0000c201030081500005c0c002800d525004d44501500511480e403500e0b240745240449501100384802c3c6c1c0c0a104e400d9012814680b54400c4070304031101c9444a505d8601e2031024059443d20042c12041806a1500fa0024040a200307480d000300d84200060403401d00d5000c00c00c8107580d0300700320312401c10402d81c803400200741d000290400c1464000103142841c0d905100120b2901211000c40300b200780020090003207003482d94001c3c0d0706039481205e0138441e80c0e8a080c982e07000c0340034070040341800944501c0403070504802503000844142407042e40510f82240705003010701d0000000d0884100e5440010b11001c0780304041c0100c0042c20302460140281c0484d502c2d11580d07400301502c083d00104a803000301e41014041d40c1195030180e406100c040c5070324068100152640807542010000d0301480e40045c0b803400841c07080f241a114000d1080e2000140d94081c00b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 316320800 1250 316319550 316319573
    0x2070224040e0901060315020a120e030d2406020304170303040b010302060315100f0201060f0803071203020409060e070e0108160509010c0606091b0807020d0509060912030d060e01030c03 82
    0x148465581702d4020003c44d003601380c221820118000c0260303403020000e20040c0101c160403803500b900e0341b412100e02c9800c3e4020044904d500408140411009104200a100b44c09401d0584644441d24500002d1064010024004940c90300094039002d4a80d10421038691008030390042410451400600c018940000a990800d9a541c90484440000c40110384501c01e040203400c0401c040514040480d642401610060000f03003001101142c50314501c140d40380100e10000700010040340003049414030a0b410344c1c2c02418100c1091240e2560f544c1005c10b04002aa01000054203000781101e00c0d50282003020700a601e0201c10020b203000c441ca040300c464000c4040241040402800f03003000c9009409401d001d04030398040000e20600c0e07040c0b01644480c2810813002440480c0080200040e0041000810380d143c50503c175580e10741c0300c000a0780a06c1608803080d0f000c40c0c4c41250b2081c0328400806420700702c000d040e0030080c8540f103040407900c2c150248401800d07058541c401780005442c01c40103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 316322050 1250 316320800 316320811
    0x6030a1a0411040f05030a12032a030c09060f0207060503070512042102060c0301060c0212011a030c01092d0f0602010207020f010903020d022103040902070224040e 72
    0x4040503040c06400040903034002203072181510501040070310492144801010040c07004034003c00300c10500342e44441c131040c1c1199143c000e15a80345100c0d11182c42404561524410144c022140100e01207405802002c4002c0307840001600c40c040420b0a80c0258802c89400869030020700110340390100880309944014191003c220080c072041c00303021403006a03980600c0c41020400030f6241108170740c20001801c901e035402154003800c1805075a0f0304500481e41982c4045c82c01140e00c0450b40003040708c4814000c0c14002a40c81c003081403610164080c61919004422402e54500008800044074441410b00030f80c0d5024041c03114401c110821a9000211481c0010744071420580e180e0480c0b03c03400107640203001503500001c01c1000c500c1c001c0f080380c60498013403c07c0070b4a40d085801082e840021a00c00a000d4040007800f007620408115200ca401c00700072003120b43c0d4544136071049000c0c0d00407a8040380100341d03154241000c811800c3307541e035401f0312076400c950502e803828102018048001e4070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 316323300 1250 316322050 316322081
    0x20a15020906040303110f0303060a0311030a152423130207050703061811060705011b0f020c030622060b130b0117091905010605090106090317040506030a 68
    0x541142e4032803402070300c02140a520f0701c5410340100c080103070801c00030701b18103000b5070000c00800006545841012041c0c83d00300100b148554150383c0402d11340f0205030009050320041c56131083c1ea404154000a8070100000061075074850714681041c03883e070403801100b80c82041f032506400c0300c032103180c10613441010003424158513038542c3c54100101c2c0d000c410281ca454106040a109204843c0540b0f101c020055042c1824110740b0b0f20b400582801c19000c1a20070400012404140142500404180c100f09a40040010140308000e84041d0001c2c42c00380140c01022101c20440c640411180e02c81c4814400c200c542d420000010002075a03028000c988150741c0307104424464850b04621402c0200952300010600220b01c009015031a0700e04c2c40b42c2c00c400f803036000c01c554000d000c100400c502d07030a0b100c0e41c41200c2d0b0920b4100e0241205030001900f0918560000690990001030101180d0184101402184503e0501e0720580f0a40c0a104e401200070400314494a50941c0400d030048400d11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 316324550 1250 316323300 316323307
    0x10020d0e04150e1b0f040509151906030b01170a050405071806052b03030b040b0d060204032d11040e01050a05100909020d11180a1a090601020a1502 65
    0x80c05041e0300401d80040c102c0315000740810440080041013001e604500031311807070606a590b0500c4041d44141d0082a02554843e8040b60f41d105040d024201c2d921740080007010f1189071060a11003402c000d100b03401c0001d042c05444559940105200c0d0081a80350401c50000c2e65000151800f400d0080c00856152088403800504090b03006064608440304080c046003051400381008103101400101c8119884000103195000c0c41c10111305150551500300801c00020000014005107220001c0580009d43c209850080122a600130000c0e2842176504100c02449080d04900740324016114a680c0c004c400d2507840851a504e0202120510003480801e05a401c0581c0303a003998015100e80700102c0d03c3d03005008000c4103040312140507190b05002000200705580008040124142010b84152000c500c40d00b02c3e40c440c02d0031003241400c003003400140b81c140501454014000031074148400000c0140c40780340d40c5804c440c004d00540b016401040c1d042c955440d10301c00e5051855009003000e5080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 316325800 1250 316324550 316324571
    0x8130e09060f0114031b0f22150f090504020607020d140c060a0906180e16031a01050403021009050a120302060a05090a080d02090301090c1410020d0e04 67
    0x1411940c45140210007034400e03410302980c0902c07500010f8108030490041200c1d404020b440024080d01e01006c07a1a2981600035100082154010903500980d0084250366040c02d0f8050015140c54120b960070604211036103003c0000e120405150140ac9000502c06004201c4101e05422040c0c00a0004000c01d140202039400503000c400541001c440b10016001c1d503180f0303900c052084144400050b5442031a190303024000034106001c1d409050b0501000c0036980712000f02a1088e18040c1c6030b501c0c0c0556160a01c101d010321291400104100001d080c260003102d0010158000c42d841103040e112281010f045a00704404002014500c2081111500d400180b9590301640440140444120a40440d60504000f42001c00007040c0754800c9042c00180281c04000140550040c6c0e04102c500740c450702050440c10203882102c81c0180c0c59800d0041d0b00003440090b1b000c02c003c03180326008509620260b20240082591180c2641000d41c000440b801c0280340250300402d9680002040014840050b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 316327050 1250 316325800 316325819
    0x90f0b0901051e1309140c160f0203060c0309060c071109040201260601140412110d05100203060a08010b0f190b0f0c0105011a030406020a050904050915060406060504030813 76
    0x200d00e1407505140c0f20b0405c005401c0c00b840344695020601102444a107030017000400d1a110300350240d0b000072003401a820601020000000020384e0003000d031516402d11554000d032030380094075514290700410b804100c1c0219040219a00701d0740c0400710b62070036419030381001280b04c1c0c010030a0341440f4480302503541030808059150300c08000c0104140b124100070000400300c44400d8050120750500f0001030204032a4412210240c60340f001d4002c0f0880000d10200b00050000600240f40d07100b401881c00c4441c0d010740142d80b2956055031281c0015a0380d00e04182629500e041060b00a60001280300d914104035111860300c3c00c1c98409850740c030b80c3c0c80300c1e13244003580030400e0710740c00c00300105003040d1b040000c0c081c103801044d86040345125004901544021072001600c010521940004c11124180c01481901c03202e2000400400c268034003108466114000009031005841c071200000d011480d0034443c0b0001c0e10041e9940710308250850b039801d036466200240ca1108101040c80c00100c1501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 316328300 1250 316327050 316327057
    0x9030304150c1b03030f0c0e300613030e0d080a08061f050d05010504020408030f0c0c0904230714060d090204090f0b060103020a08060f0d12020706090f0b0901051e 72
    0x425900006c128048080c0c00c411204520020b1040100b401c82135515944c8451011001d200000601c5280f00c04204801030350100151010b02180140d0b010001000000c6504400c924040d031100345544152004101000c1c20a000080041c0b80c240840350039644110012584084c018060f01580c0a020000c0901c0e204103510700030000340000f5090030448114061940102000e40301541031a00342540070f5201d010385180c00d50200000705010300300040c01c11401040c00c0018101d51443d06113804c01700364800420f500f01080342c80d9922691070540340012a035088030f0010040809800b040c4003002802c0d84544080b2003e00e80f194580c4000d40d484e84920480e03984140ba001c0c660420703900e005000b159005191030b0500d841440620340554108250307e9200200704c5036428211058000215001d41840e00030704511a0b5013284401541c002902c10700b521241e07150850225a24884078a502946000c1d81c1030020040c080e02e61a54000d002070030445e5081c05a0b081140280903a0722800e42 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 316329550 1250 316328300 316328303
    0xd061e0501090209040f060e040f1b0e0103051605011e09080105090105160503010f09050405101d0f12040614190c0c0617062101022109030304150c1b 66
    0x3e9001a000301c1a24081c0f0840b10b51402200051180a161216041400e4401400030b8408030b00d0344d800204204000c2030365a941d04407160020a61616451144012035090000b203a05210341e5842541d140d1040017400102d400580d280280c0b40014441042c4003a01c1d540e4031400c1c42080701c00401c46500a0103028451a081c00c00000d0b5032822020542c0c1e008050143c01c014401c00b00018404d18040c20108015128020800b2505413603629040d0300e0202c001c0e4074100c61910300a030100307007075080114542808070210101c5070001d20444001d52038540e52903405c440d401d420042000045d004d0707441c1c0c0002500c2211103074141006001400100700d001e0b602000041c0b000907441c0208400082180054180c03407429514000c95100b891202e68400362182d4231641250400540004030701c0340b041d49024010000355255200b40700c503045001c0710902400940c14480c4002440d041000041e40c0c4940c0e0030010b24000000d42510000080007082d540d0310030400700103000c0391030001c21944181701c00d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 316330800 1250 316329550 316329569
    0x5031603020c01080408040501140712080f060f0604030b09070f08030306040f0501050306070c060b03030f130603050c070f020a030b07080414030f0409110405220e06060d061e0501 79
    0x10491038024108074100c903000303060015441c02d000c04038030684103403416201d00b03007400b03104800104641c4c44180038180c2c2c0141000c4601200101240c0d00038403103030080c0300d420328005281c0c523906c0401c03034000f40080c1400d4110100780402c00100e4003902c0300c0c40d04006200b040e1070303240d07488234204d010014503900804079640c400414003810b41400c0c410500603000c201000c004c0365041030300103600d0348405000e800c10444200b000406009180c1d00441c0213180042c100c0b46e50b0200102500f9494011070001a001c40360028000348031406801114411200110701c01d00d000001d99a414110388000b0741070380c2041d2441300c04000140c2e02e00c80280107107099104c096451030103180810b190520085101038540051103001c0306010070006450a86064241c040cd00002c810b4010a550084e54401507109080319440c115a04d83c0403100b104045c0440028000c01d140721079019540c24040d6102e5401071941d00c061000f00e0150f5101e415004151055000c4014850617000e0075940c081c2c03c04400d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 316332050 1250 316330800 316330837
    0x50d09020a2c010302010c080a17150103060807060e061e0304060504060b0a1811130f06110102070c0b0304150504030f1b050d050f04180209040b040b090601030e0a0503 74
    0x1001a00e40740b81d00c014502440302c080d0304581c0001d2500b110704a00506035000800c0c04046a4000d900703591400000201045161801030009034072052400216800329261441c085685000030030004140e5556032654000300000c0130600100c5e9110305c40700c1034401a404101009100040011806140161004201c0c1d06150510b40b007120055071506110721009401000f81d5000c214200c4610103040e2400a04441007145c07040300740c402c2c0500b100300041814004907404000e00d50b1403080d0741696846d103403088071170f0070514201d104484001c0c180080790181003080b060600c0055601c14852180d01c1c080c04030300041030003507500c2581c00310302181503000700200c0c0591100e43e64880040e031140300050b20b0055280e407034035005031600080800400180441e100d07500c00c01240d005185a248208401e040301794610000e40000591500c40c03400d0402c03011040c81d0600035150a110300401c6800b540c1c0380c020054008088a603e90400c40c040e4842e0007000c14818009444d1074103185880c2e405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 316333300 1250 316332050 316332089
    0x130b070c0611030903101a0a08031908010b0403061a040216050d0207030809041a03030c2508100c0e0a24030203101e030c0305010e01060602011b050d09020a 69
    0x740003105100795543c070500250105503000905148400920f003800982c090403403440043ea02091060241c00541848000402680000007400c2c08116618034600c242d80d905412645440c003031081c0c0000400c01d01080c0301146055110515040391485540035450300c0c000410140c5e0005001003820407810ba503444103110302400200c110f0481440509091810340e5201e5070240510328605000350750312400e4000c0d004480c0b05d0480b00074401011030383c50700c8440f40100d80c0d5400e411029020303860420260b81d1f810801e00403240030b80304d81c000076002d1f00e1804c4206034000c0c090402000104580506c4a601f15102c01c130405001c0c10300c8007048103100076001c41d5100407004c19849141094410401c0190036501d00d0b007190292103076042140c80b01d8807650703190150280c082c3c10241c040c0601180c00810003005601004040861100920910f41e849805908845201c111180c901c0170000d800d5150602c0b840061981050204001030000b0203900850480f80b207030b412580c0c000308143c42120 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 316334550 1250 316333300 316333307
    0x17010f050c0d0e210c01020408070b0a020d09030314031513020403050610050105041523090913020102071502070b0c0c011713060c05120406051b070c0b130b070c06 72
    0x80420000d1006103400c1c813a22500c0407902502100a41100c100442c00d00148002901101c00816a41040392a4030b6101c6c030f17400d01c1c01d601507881440940b1a9200d00c405682c0504030b108101c030741588598425030700f84268403c4683c4002c0079040c04030a964484141c5030b82d42c0c10220f1820035500d034011f0b100e500358500b0a2070310001800e402c3c28480030746010002682d0040860701030b0750203440b001413400c2001c48242c0d551007800d8004112200d0301e06010301d816211601408240204a460322a04e80710080140c8034207400c014083e00503040a1402e112041c54008030314000140303441101c1e1b059541e480040e20036013100210449a41040903000c00c039607030080c8200b800400c10f01400d000c0e03082010250510038041e0303500400381911001c550011368055410340b41d81076500f020b20300980c60280b400700028002180c0d100034102818410350f00d45220403003901c60095000700140c0000d400c29680c02e159801803441c0341221391101ca0045188002d0b50013501110348202441c081e80707401d00d80040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 316335800 1250 316334550 316334561
    0xe0c090f0108301b1b0a050405060f2103040806040311030301081515060d05370504020d05030a051309020a020613020a05030d0c150c0917010f050c0d 66
    0x90b6820300701c2c682c51410003d22600c1c20384500d542c462030381d91a50802c02920001041103038560203805503036159943c411000c0c80c007082c01c0004441c0034004070b0f00c0380108821900709551003600000c007010181c00d20304010340c24a03c01031890003003e001400d00c2d506d4500d164040d80005100c0d82006040c4010103800146240f0601c00c3e10000e50b0441d81880d4403191b441a40001c0948106001d2001c01d0a103903540d079240c400c060001c3e003659595100351481c03001400090f9050581c0030b40a00280e02007041d0510055502d10003440032401d00134003941440e0103020040c105030fa022001c517902d000040c0081005101c1d0200a840701600c40291444850810315246d02030408a80100315809800364003041c1c2a511102c0354800030011501800410800b0420b42c1005030103103c0c40300e1102480342c001440521591041241402500c6821400801c0e60b008100901c0480c5005a0a000500104640d4a40f0004034070000508294020006042d2101a50346c2c400e582c0e00000c1d5031118070001d0040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 316337050 1250 316335800 316335823
    0x1b08060601170a14011e0e1909020a05030f0a1202033a0606020313140d1502070803040605042f0d05120c0d0801090b10030e0c090f0108 60
    0x14245919210300081d0480800407000314901e0300540018100c0c004640c00318004a8456080074020341e120012503070042101090303d1300c03035984044c000902808103800c140c8215a022044100c10101d0000ea0f00900801801203034080e00780c04012556440400c40d0180c68006440200714501d403e0400e1a9248002029201150020446e08441941543e1940e600404041c9500041604241a161790309004010f1403862818085d00017a0954004058500c940740d01501314451a62408803d01e040c8040f11031507001001181c0000c04250300d040380c414640c0203501d015281c600c46940710030ba00e50048808590482e59081804248003941c01d0122008500d041c040c800814101c1501c0f10b030321007101e00144108414020101045801e0150301c4241815644043e02c40d540d0903c000c1e01c4a00340e880700750020f0034150000502d08a00d000c4c041b52641c003d40000f8541c80c0c0c140e03044020b0003401c64468a50703ca41c000460301611208030040c4209540002c140711135050140d420304140d040f004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 316338300 1250 316337050 316337053
    0x1002011803110a0b01030b090d2607020a0c08060411040b090402040e0304051e1f0903170c0f150a06050a0b070f080d02071101110303130c050406031b08 67
    0x64003202682110400055074060400104402d1a6240c0e02c0c40d01e00c00110041406003058000000c12442c1c0300402d001d10341020940345401c07030441c1c0884800c4180e001c0f41009151140f2100640c988140074160040000d205440e0300600c2c2d500c1d00d6140d8009030303000603090b41c00501000140a50401842e100240455042c084056240c1c002416001d010700082d10907070f82c40d48204c2100138100101e4000f414080e08c41500031000300100311815030070740e00391401040001c1c11951840d1852003600040c8099864039180d583c159103a81c003401d48510114018580d04001e528045007003009030b01506c0c00403900801e10400d08052150600b8805000c1e540c9480c01d00c00148956a41e0740850415a03400107181525100a8205203160350000b50014100c030100007051481740800350010030006d805408401104914000112040c04030000c1c90010380d001030010846103600154003662150140621104031921000000d045883c69482101c80c54011601410f8240c42c0480b03000040030714a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 316339550 1250 316338300 316338311
    0x9030209010504050c0732010608010b1210050a02040315050a060608091905030f03040b041217010605030604090524010f0b0702120f1204080609064303020306100201 73
    0x1042ca08074083c81d00014072809120f800401f019954410300ca814074080422860701034040680c0d01e008086e58043c1c4041c0794202090b60003035082240711100305180210092000e0b80c0b501803030000400d00580004041c907003c1000101003010944031000b0f846041100007a1403c1c00d0301290210351699200d542805400c808000390f26501051441c0503090000d07020707420524505c3c2850540c401c2200c2c075440d120000c0140030030f005441c7e0708584180c2c401d0f4620014422101000c0e07401301d41e00b24100019400e140014402d20b486035010b1500034001a00200d40c10b0016501d45042502d41584120400d005610500c403214040d5010790042000c00e0640305146c5c05c0815400d2207100c1c0d440043c1c001c402a032003100c3c00450400410a05c85c4c20201034600640030034941c0310050380140700f1003580d84135480100d40518008503001340110880503400c0e148641080240924110f50603104a0802c0041c9003c5241c0181c0380c0c0d00c00c0040c0003035800607a245412003c005680d0310500503c0110780c03400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 316340800 1250 316339550 316339561
    0xd0e150c09060706020d110405011b020901090c0219080a0e060712030222080703140606030a140304090534080415060b0c1c0311030f04031107060903020901050405 72
    0x482110070009054071107550390780c1c0718209580039100b820031200d03a0714a0421900964000d000142080c1c6100340d84a4468600744610280700c2c50b600030b0043c0d4040d10300c100410031034a035540034000080043c0141c4e4484911003214100402d40c0030000e4540701400180305240d59400b00c1c4035048400c0480d0010b0400d0301c692164440d04c0442403584c03007410b0303000400c10341210031010300c40c00c2c54140940221a294481c810562201030902c012901072130b490402e00034420700421414030840014004003100728807034952107251610f1a6005069000030000451607032418001c1c40e00c1866030340f64010301030000c8035120344141c40e42c0902501e402181c09034082c00d16402404141c00907041400c50501e40c260b403405200030034480e44042070401000070300130404040400ca48100c070038a4a01140a0036050005405444185a85032101001000080c481e090161a0315070054007924044a03210040c2c0070103071510416805c800042941480104114900340c410b0b103002d0001680c0031301460611 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 316342050 1250 316340800 316340821
    0x12091a010812071b12060b0112060312030b0f060d0902100f0906120612050c09090105070905010c05150c040305060c13060f021011120f010b03070c0c03080d0e15 71
    0x900900610740c40740e01104044e1080020b2080c0081c140c04014250788040515040d4020440c0c05003245c0450022035015288003114802c2d9001c403900105440315155a01404900520764020801d03803050080c94040c3d0143c88039005019164a0030f40c002503042300c43d00411943e8081e44a5803020813202d40308a5889903030101511080750841d0070400282c5c10407082d0b24018201d2904501c81d0307103094100350400e0160014154101e041c00b95031451241e1a620101400da0344200c81000125900305e508000d203500c110001c00301940203200380e840303441c100440840c00b40401c1c2c0b15109412800b290501c02d01c2402d1203c0d50700b00000c041d80c1443c0801e0544d01c0c2044495901c5140d090145082481c40b1003070003807000030011407001101304200c0f21040f02c491007a0304030b070301c883d26140450800240c0310000200002d0585070441c1909040d40e032014001c0380d0403501c0031000c0324141d80d6a90b0010001e5100c201500114440320004030344900701180003403400019802d0010103072585024411802d01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 316343300 1250 316342050 316342057
    0x6040621140102191b050607030f0b01170c090103020712020d2a120c0615090b04180b0c0408060903090f0d0b0402040203090111041403011415090712091a010812 71
    0x1070900f070021158403c0c02101080c4101c07145c0150150045130200103000382c1c1035121260a8010580030065110b8010045031042150140c4080340500000170404403c0a180608800c1d17070145405840c100c42692000340c030f45c0c0742108442c0964050302d4102c8035603800804031003183c450030201d10303c0caa41450f1100305009500c1d07006004485030624006400b403281c0e4145c41041d8010900344400e80c8a04503c40c10700c0040d2140445035460051009820314242c0944c407240e120396448101ca01d2247d4441003180340015001000544040100181e270000900c240c6100fa460000a15202c80c1c02c6402d000e0b0384008100303103d100c0c1c1040302c4007400040f0130307842003604140c06441c01030710b996070580c5150041403101241c07001c0403400301d000186a810381c000c00c1410f410550007884008541f10140c0b0b01810147c3c0c0310b00c244020110302075200c1c185403101543c040018505070388401404200c1c07008582042c00e0903100500d84000315011101c084440c1d038018492880244210451800c20003076030b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 316344550 1250 316343300 316343347
    0x10617010509070c0f030f0f09180f02120c04050f0604150f02070f0b0408010e06070f0c031403040602071a0c07020f030f071706011a040e06040621140102 68
    0x2c0b019020450b00e501c2a0441c55486511002480000081d42030103007140100d101c002001840c91703000080040e01c50a0440111044204500000e400030034100024000d804500f1502c60780c00d2001222070640b5114050103000342115403540c0d60705000c2400080c05001c1e44103030154030b0400c8104180b114013500ca410411692600000b1141008000c909202117a0b0040b0480c0701c0185c0081998002c400041c4125031400d0000c00161112a60080d15400226607510114401221141006000d82d0220210510902c8c007052440b600800c0340314540c02c20395098902d980e022404004014003c4001d1440c80086130b100040c502d40b00c0c0d0701c912180b05004c0b00a0003240d000480841d152400c000c00741d0070200440583e9291615680751940301d0303c217011310050b0b034410718000065038142406d09910380000b90b20007910f89810030440034584040a0a900d4002e0360325400080c04c030f0800c04123044415040c6c0034110100602d41800040d80402643c100c84903441004600c0300c00b98a21184101074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 316345800 1250 316344550 316344559
    0x302010804150f0204060e030105090a0f020d08070c09020306010f09050907110a060501030f020102070603060f06080c1b0d0e180414070801020f21070207210f08040501080106170105 80
    0x2102d0032003280c01400d900400419030500104000c80c040e60803484000d0880001c0d8001c00c001e607920f4102507900c56041402412001c4019205405820f150720b10381461402042e60f1803901000d5520000c1291081d40039003651503010040c0701c1c0b650703031049205004c2030272490300f01c0c02d45081c0000124502c4e00540f898003805035a62081051550500012004680143c07007003145683d00e0811075080d00c0080c40480c01030041204c0403403031a00900c103100988030314035000c0c0e0b0700e641005001e031031200d00a0500645140b0901192a844048140703c0e100d41c4040b002410303940c41c07070010243c40351445102c61440380260050328005601031010156000c0d8005020012540c80c244003136041c41e0040e00f00c170881d5400043d400c0b481c0d80540d4000d021160b685500080e0008002c180121032005c140e5940c0010382220304208840d9022800c481551400c043c0c24040d103200c0360b0f441e200902c90303030001150389c40c6020608200c00d40e0420768290040c03c2c0c5041045044500b410300c1e0750485014010305104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 316347050 1250 316345800 316345823
    0x5031512010f021911190201030902041d0a03090603200d0e19150207031d0111070303180902280e09180c01020c0d0303110708070b07030f060302010804 67
    0x4000c001d420501d0b4125003080115951800e07010714103240300b040003031100410544c80840c01010310008440030400e501243c0050754208903801100644200c00d0103a030701070b85400014017103181d0300c4401c08010440d50f00130180280c19241c060030344034003580f0100905181078500183e8407507404d6032004c0d440e0120151079869542c0d1040000428400452120921a000d83d0301c621003102444d403065a40140341c1c60600200c072030bc0901c107a11800c28002d00140350340c01c1b440100c051103c1a031100301d0050424145400d9200c100c98a00700c07140d0b1080c0e0004031201480c8050804144051020f0903c0d003400f90328040400020344d100c0000021400e82c01c00c1ca1041701e130013003440b5440821250304014659029418451b0100e0700480101c0001000e5001d581c1d003002c0d00c0c0d800000d0700080d011010707200c85903581c4261019001800c0d00040085c0d0300034104031b18000a18000f00a00c0c04074491114074545041107000101161504030a80c2c0400b440d2400910160b07810060480e4090707442a00c0444 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 316348300 1250 316347050 316347079
    0x60f0c09181b08070207080102090f0f030106050303031609090b1c03121b030c17011a0c0f030309060f130809030a0c0e01090c050711150c030a180501050315 69
    0x402e4810300701c9480e486a07551980310164000c0449000380415421540040d448241e040d00f02d00c03e178240144d00810604a01c2103c5c00c128a4120a03403d0090001509030307500d102003801c50303000311074144c0031841050786442410303002081403000d086100820454030700c204000c2059102c403011070b4001c0203480c1204108043c814401e102c02403456840170300182003002c2e000c01d481a04070322050003017801c00c2c50040401d84282e084c3d0620407a0307a17941144c82d07441d1a20704840340e1480424200195020072040012840800c50721802000c080011a0340e03240c030030b007481e0502401500010101680d1002d024500d09920800000301c2e401045150f0384620660010340751140113007000706001130700c0c880020b0344808440540e0480c3c035582410b01c5074104070441185d691040d1700c4003c015083c4040f0003040c500b080d800101c0e80c4441c0b5480e045c0ba101ca1449500e285410803460f01002405c1000b200d40306030301c000024401401c0030b0a00608505090410482c0c0544a4460721300800c030003484100d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 316349550 1250 316348300 316348349
    0x3030603060703023a0e1903030f0902190911040311060a0903020d0f0b0a231012060509071a0702040b1507030203040e060a060503070e040b060d0207060f0c09 70
    0x80d089543c0351802c02200b8000101c0c400216024045415038071b18101c2621240f110204400c40001400040c028500f2000d603400d40061124002c00c00710360b84c0d6102003d005840f086c1324050074108119800060303610300615002030303c001d103035004401e84d8140b00800018140e822080394501d02207855640f1400711040c100e402c41610781c4003070740c441d202c08580402d00c000045a00f0b100c0c1d01407a00c0d02c04aa48510a01e402e941e0092041d8400324503441038040b070544152092034001c448180c001d03074042d545c1c0144081c0d6201c0a08241c400550703d00a00090100c00c0200c0c42c000e000c061781082400c580360310164580c1c011128040d00840d1908071400c129510ba200042c464005901e00b1915511b080c20001d5580d00f090046100040c02e520101d8001e1600e0034400003180d011360f450914699524408071403002c44030710a41d81085e100c0e00c080006548480c040c240c02c00b04420010b0311003a407800d04030184c41403101c0c0042c1c400d15100c0041a000d522a81400a40306510202d031070b021848071815 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 316350800 1250 316349550 316349587
    0x7110105132106050c0a02010605011d0d150203070210060602011a06071104020a0306080c240c010b060706090326010605180a06030605090a0204230f130507110303060306070302 78
    0xe15491a00041020890b082000b8040b1b40383ca03a40200003464170703040103540b2006420040c00000b20001b1009407989054005240e03003910401c1c10480540e00809100c090340c00945160026810103004000304448030f12412004003a103100038803442040c45041c88801641a034014086d1400043d01030920032046c040e1003030954007034421513a4100400c0024020485401408d00c0c0c1d00546072024072614001c0d450110070b88481c0304e22502e4500702c55080c4100d5002c0004000b00c3e5486054078034040e500c40300980780c03450181801141750b16407494010100ca0a00441c58001c0d1645080c0d4001007006200d46810b4074076600b04a0ba4483c1010101d08203260345900f15540400400c030041800e640c15001500ac48000341d91008041d02e51000050583c01140074207400c030012041005411030044002601c06c176000341c895400c4003e6a4042501441d201c01c000304070390384940900c011107610100c902c6080c0c0002001d5820b50400b40f000988401010b45030008054011445244030042803401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 316352050 1250 316350800 316350803
    0x105060a02390901030203100b030a0c09060e070507051b030709020d0207060509033108030304030206011401030b030c04050408040b0304050d030510030506060108181002071101051321 81
    0x140555000d55208850396040201e0007a06a000c0d030ba41c1d1203010381004a80141030b6540100074044041c281c24020005110308500194140308401244000c200c0600600004e030001e100c0200d01517040000c40c1a0040f80603100f2010403000704001c001040300032540760000845d502e035042541d028000000c0c0703042ca46811540145100007694182140294000c01030140700e0078080c4015a5007949080d202c0c0610b45c40210315001c66030140d031000010009607640180246c20790580c45482d000000d1440e001201d00303d000d42d00440042c001010401003141da44d0209180c24007502007580042511340b409401c080b40900e8403400401c08008000059030060700508203481e483e883e090030503d588100009040010030314003004070307001c2d00100752501c05881d007043c01072605031560f10044a207510010705408040c070360300e00c444048201c10f11400c41c210144400244c3c48081604195900401844140d8188902002607004000850f400442156041c00c103001b442c501c01000600202c044080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 316353300 1250 316352050 316352083
    0x5011a01050a08070e120114011e09090515070206040b0906010b0a03052a0a08070305010b042105010507230403050c0127030b010303030509010905100c1106070509120c06030105060a02 81
    0x2c40301b5141c15800080b131203010f041d80d89a1a66903640d00300106a9501d500005600c500009104110f21a08825151840307501100c0700f001e0006503005010340d0944880c4011380180c0b0502090005070115240c100408002800c25949007400040a41c82105d1000c400d054544000880710040340d10403400ca284003800001c0021004c07810088a80d104c80d9100c00802c9907070700403c01281c030a100f50b0381610b10039542a483c0c0703820036002d01c105d80b80030202c04502420300c00c104000900d080c00307020300030105a11244055210030f041510314036035007030b141c03d07000780b091004001007000050005404c201c06e091005180c07484a00d0707a204410103248001c0242d140c41c800204002e4802040c90403680a40e07020003042d20703072440c140d090341e59844024103180c0c40740d0302c00380151400d45e0061600310054108441c640840032089800c2150889560340491030100301c52129060160001c0301e021031403400b0345040750465001581602042c01261300444005ca42d07042e10758000c001c41d401d10381d480c15 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 316354550 1250 316353300 316353319
    0x1801090e010e0709090605010c11030307060f270b1b040b0f040515070c03240509010b0306062b060e030d0501050a05010e01020601031104200705011a01050a08070e 72
    0x3040e0400c502d5043d10b1800c00500110400600105517108500a4070016500c2c4661850300d502c0704982c005040d0441076041c001009401c0005050b480f48040840c4141d40208045400b6001c3c81d880c402009243e115050448a4100008507800c4000d903003c440d03c0210b240401e0100019080d900490700308041c0b01d08000756170090344403141e000d0000c80e41c049405403e0040280d105801034003401d00b0042c4000c0c0c443e901800000c020300300c10380345032001040c50000c0348000580f0f402503850541e01c60302965500c1e06843d0050070b046c4400d682c4101d0654603e01c0d0402e2505030281062409403495540f022400d010707a007008200d4100743c5000c3c00d0b4500320703901c80d0490003c40004000c01c2c45000d1003a82c00d00c030001401c0d400b5018024011005802418040e8a1030701c840c0ea510440b0030344294002c4c0d80d941e1101a03941850444004601c00b528440e803104038078940f260840d01c90300201104d00c06c105c0200c20050381d0100440758502110318010010b51140c0c001611441c9080c0c2c03e050b4407000c0714 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 316355800 1250 316354550 316354559
    0x7030503010e060109030818010e060a110d1103070321020705010b100306140111010e0601150305060604211412070303060902030c04051207030609030521010b1801090e01 75
    0xa0040c40c141c0e11010b00d026040e407039650040d5a2403100b0720005101a03001c0c0305260728200300c02c64030307011400306041c06c0403841401c90010302143e0244940901062443c0312140540351704100302544442e142c14040d07117402900d07000303e94901032034030010204180d6105036048607001045c0740e0403c10000e1300554803102c182c40d065001c2c0440b003890324001d4a140b0b1854400034842c1c0a4041118960b80003241c00b24208070046401c96000002d01d44903640f9440c20618484042005034002e010203001e1501d14040844001d05981f0080c2c022480b5800a1100f484402900c80305d140f03032001080c0c22043c0c66072440c580038800c5020400001c0c200c1c001c000c081e400c00203e40000b454464403c0e0ba081103800d441d40303081ca080f0f0105072508581c54200b40000e02c0356040070030b00340a11384602421116807075960707903442e425111000c00441c0040c40c04605c001e200d014140701c0b412011500141144c007581402442400d6021300d0a248103480c0c142c080d107861590040c200d80002d000454005c0e074956031107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 316357050 1250 316355800 316355807
    0xb0d020702150a020105070e0a090911030303040804080601080a0507140d230c270405031b0717030a020a2a0b0a080601090b040302150415030b0a12030c06050901060b0703 75
    0x14042c01e50142d402c1c140001c01c10b034030601d00007514200040c00201d00c40e08120803980100b060000894aa330b01600140c00c503544d04002840c8600e20915000390303210b0408100728281241a40007a00d540d200400c5a00050008152507081e10004912232200000c120b000510686494802800540d00d102008007002c4002a02d100400d140e2012103840d00b03607400034001030035441c0c8041100c000c0c130001c800b14083c45045016070458040c0341140c2c10007541d00540c00c10018a041d107201c5540c0100e20400500145a6550704a03400d001c003e90309280400307001035200d001c0400c0c000e00342403003100c519894044218400404456200f900e844041c1ca84c40491820341c089070380e400c049a04803000402070343c440c09c0003c3c2034503810b518160505185909021046014101c108028603040c08042071700c145010b0400300042c40e0b940c0104156550200380200400349810041119103039050400102c3e820060207507815521090002e11076030f420b14418014182508280c1d601c0c540000c118052561 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 316358300 1250 316357050 316357057
    0x40207030801050a0f120204050a09021c021302030123010210061d01050406081c05121f0603020c0706140903030301060c0507090c0c0305070302070b0309160801150b0d02070215 78
    0x1c081da0131905040c1c565501d03100000d058880d08120b1181d180002e001401d013500000d8000b84000e0022401130715650005202d8141803943e0304000450182420035460589507000c100c940300c00c0c0c114134550424003c243e80303062940090301101c500000380d0f903103a4801c11840d108031186c40402c202860b107448130000c3c0d1a81040020707641410070300020a035441d044c03017803504856000d002070007400700e034200c42001d1072103030324048003409410b00144941c5d42a0b003010034814031400307004e030061140c00d04422036103442503003200042510601050719407190000f182d03c00cad40c0c05030400780000024901e503d01c180c030a41d0301c070315050300020000048144c0c1004d20b501d00a4840e03410360344201e803101c510354111000446100001584450a200402d000c2c41c000d03e4954024419100d080d62180f01e2806039502c1a103444003c2c2c0c4c041462001406442ca103484090300b03d200c02030244040e03e081018601c0c805000e12030344a00c00090800800865504a41400d030f80940007031544554580000d203580c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 316359550 1250 316358300 316358309
    0x8191a040e0c0303090108070504090c0c0b090a0c1202061c090c06051602060702040e0604110301061707350a0605070503040c031e0611070309051203040b0d0b040207030801 76
    0x30304100003100c8031034011803240c60b1600098015418050040011621440d0180c518018004200800300d900002405103a07c100c501d074440d40991202d41c5005941c4000082030601303503400040c65000018000142d00f800c450091802e003031000c1490000480f00d12415240015140190050700001c0c0555008440d01d203014103e00b480c920b9580340261030078401c050b001c1161030813400162005103002d030080d003902070001d0000076070160000b000c58a0414250760035904014010781440a62609004000140008694084891201402ca265202818000d449007081032045100003034040c01600f00c50003030300d406c3d040b84400000b07060a032034858a5400303840d000d00b000c000800311809201144c0c040c980c000b207041d002d28656182d9001400c401c46d40c1d107010046241d068804550301c0c3c0201b900707101c02002c1041c2d07207000500d400b41c040041c5912003405202d464480804071880403043e94215103d5007049940c131803900380d4800c000c28250141c107921510128100003410b41c8000218140c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 316360800 1250 316359550 316359559
    0xa09020f0f1b0d050309060604050414010f0b0909011a0f040e0a0b1e0f1915090b130b06070813050a0603090c0801180201050c100e0f150705040608191a 67
    0x440243c10104c560b4030044408a5250344400082209418182e202c544d1081c0100401d0800d01010840142511120030300010040d40314180b42640d490302c0c0f180b00e50030002c090300803c020407001a0380d109101f100c81006200d0404808102030350b032039071f4210058400d0b003803041d2907204e85103242261460a0a441c2e810380781c40c51604410450800c6a407090054a02c1a491000c90340d5101c00303640000c11030420243c40076103604280b400702c0c4403246100040c00081c400810342c05064800c3c8052034000c40301c44901a030404054a800351100c200301c580864101c40c0442c0da07044084a803d0203008168030450700402d19080000e02c807545944408078207445103668558042d038507070166007078410380010350101110b402c14110040d8000c800070000000c9810990b800002c0398400308003240e400ca0701d188840d800011040012440134824140c3c00c5070403040c0d80c6824100140020958015801030009114010000c1058016468100d80102c40d07000014407460080d1041030481c07210300c03844507018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 316362050 1250 316360800 316360813
    0x50304030e090601091214030c100e0106050918150a0902040e1b0409030908030a17010e07091211040509030901021b03031801110f0a0b06010e0a09020f0f1b 69
    0x1607280201c8101c3c050807059681703c06681c2010400c0041c4984080200d41d90300000b0131000c4024001c0c00a45480e5420001800001030340704040025140003a4000381180d2600e84140f00300d5480c03942542d08204039444010800b54140c0304585030550001a2044400301d900c100b15841c0615084484124803d5806110f100f102d80c0c0029139070700b805a500380c0d000c90054000b11890800e1340c041c03a0362a02a240c683c11356952680c40d01e065501840410b40006c800e528190101c800c1003142a00405001030507178164078100700002c0c034802c402c3c041c4038080030011104c0d60030311507100c40c00c44681100403c01c10490510f2240f0654903440880614054001e1a1030301511007070031207002c00302c3c020250145103401c4a400038044040b0303d640009052200308101c03420315280400c00c0b1117909003620b008025071401c40c245010709500081c110b070304105d036410400200b62520203030329048031a503101c05a15000381700b103070001790b010710410110f6940300842c240c0b1509820880105140c0f25450540d1003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 316363300 1250 316362050 316362077
    0xc16060c030b040b030604020103020306040f051602060c0f0703030b0d0614040c05010f1202070302010e030d050a2007141e0319020a0503070b040309091a0301050105030705010903110d0206070305030403 89
    0x10b0303d04d89041c1c00e506030000700000303015500a0f0000c50f44450300402c0041c1c25102c07803204c401258015100328640000e0189000116074040009942020492003400d050080d1429241464418900010308142d11404850541d444400c891307405241e10010a21000302c0e9511840b9052008075000c1c4c480317440d4840c00180c070354020b1000482c0d000d01c0d9501d100c80100440e40141c0691b00c98a021800c540da141c40e0a107c0903018005001c000301800404501420602110b20a0301c64003d20004287d04115181d291649510111a0a25400b8401d0191048816082401c041c8040701075001c49840d8101c8041d848004402000c02c46444e40404420241102c0c0c201e0740c40313a00e0503000302035610400c038038000f007040c10100300d6006110b40307400019192609884d0050b20318903d000390480c4120507100655113000c0c06010b003d80001d50003046813519001c0001d1203451903104c0906411150803103041e00b86c6803208420342c001c0d005803070560303180a1407800421942c402c072401d0f000602c01542088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 316364550 1250 316363300 316363309
    0x40f0b09031c02030406031a030f0d030f05060603070305071103030c0403150204030f1502041806060f110d0e01020c0d030507020102280b1f0e060a0f03120302030c16060c030b 77
    0x400700340041c2c1c021340c202400e042042e00246624116a10f60b4425006030401e03641e410081340071900600e13400b90142c04000b21001e0103440c0e907101907a0b2800d0415081150030307141c0d07500341c9174842d0051802040949074040b007a07859010b07039042c0e04224080001001510103103003006004403449840c8a08100c0201190601207000d94000108002d610b0507160020891580410b9101c0420314001031526a40700d904100307040c00403002201441e2030b20760070008103070031400306004403e0a082c00c005200c811066150ac41050740126010312101100101d05a442086001031000001c0c20140041c60320382400b42c125000607808031b00500c6002200d42d951030300d2070404900c8000121844e80003c10541c1c62410340d201c01010b01d00030980d403000c104900035644d80540010212080c0071081ca0078024184110600b00c1d8125180741c010f590340401c0000c0f6103c100140740145450010303102c0e107410301003000a1041e400314809031883e5801e01401e11025a01184404c06581c804000c07401c540300620 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 316365800 1250 316364550 316364593
    0x1407060f111203010324140103061d1c030b0d080c070b070f030807170f0106140703050415110d021b040902010e191707150201060f1a040f0b0903 64
    0x102c030030807000c2c40100002040d00c0280c1021020001150650b4400390300c0500480e800001c07280d042d40208801042802860310405a12170b541100c0c5c200d02c0f081810784240d4a4030400c00742c40c0c4030040000080900d52003030388032800c1b2640c002e0440e2401d80c29030928111039048115150110f008a860028901184004031403040e03910600b40151002c0944054401020040004061120708100901d54601965180c2d12841e02c11014070455410132070700811004803070710716440a150030054040802e400105480803665400703000400070225040c2143d01d2448a201c0d06041e1041e5400103150700d40114a5040f05111212106a0b00ea0140304200a031031007204047d020030b0b03107001d8902c802d00b000d03034400d1b4292815081a9601076501c0e0880181c2c0e83d604c05404c03410381c200203c24402e80b1081080e4108944040c030080c0440f81c00e0100e40000030040384502c5643c001c0481d4030492401e0000152802060a18442c00e1483d949484004182c1d1100c2441c0d0301c40e006440707012a6500180c03058 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 316366906 1106 316365800 316365823
    0xa1104050d030c05010b150f13030605040305030109051015080a060f0b090a050d080306061602130b1008070905040e070b0708040e0a0b0303030c03041407060f11 71
    0x207084454203180c0e50312840004c00002e04a10319038003515070800242190580da81c80c61204031005000714ad100410103400c00d0200300c149508200a90304071040d8039014070072596045100450140e040c014850107407032040601c00c60300c0c8101c0c481680980d1034540014180d49a0100c0c400ca10241da1050344103600020345041d4030b09246034011b004000542d0403000c0580159104440307408000d042a01400d00400d03003081c026100c584201020350050071070540044103a82d0b5402900c10124070a0249038003101c1e140c82148148a180c0c4521355a0703449800300c904001c1040007428460250001610812a0214900f8812001802418450a0800e544925104d50944a228024803811040d45051403400e19510702000712a0b114100151442c0d4955a0b0710380859101c3c80c08044d1103091181050100b02c5541024030650f208071151109001500da4064080d0340b525103c07030 = true := by decide +kernel

theorem cover : BRFrame.Cov 316187050 316366906 := by
  have h0 := BRFrame.cov_init 316187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 316187050 ≤ n) (h2 : n < 316366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
