-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2581
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:17.582287+00:00
-- url     : https://prove2.me/submissions/6512e321-2444-4b8b-94a1-3cc7ff276cd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 464028776 ≤ n < 464208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 464030026 1250 464028776 464028793
    0xf100b1f0c052a040e0a12080703060506030a0603020a05010f3203070c0b0105030304030c0312090b0a1d010504031208091612050c06030103031704020a0f060503151002030a050f0403140d11 83
    0x20b074003050b20402c441d01b060080144c00614400cac8660050005000044c100584a042c41d030b41e0500980803d000032807180110388008505940b14801240c00d103055582d4180b0344c500b501e10441e80184540300280c1699040c0c0b2589019030024900840c0500b600c4d989540101603a41050b03140002c06801a42c401c0d0070070001080803035149203e41d010750760090041c01c1c04240540090300d10074460b520407544400007041c4540815040524200300340304000000304001c141c0001151a846240001880e0034030f0010203501542c0300c1c40105038000500310131580c0040c4e40707649401260a03150300c00c4a0012514141904126050000d5480c1c400305417900d074115411650f0103030002c408501c00c0c10f0000e40440c001000c0d0341d01c403041b001c02050001c8518260944843d40185154012100503c9400d0040d440310250705005c80c141203484400d078080d50038100c005100316141c0c0d1156032041c030b40c008140000320104000b00950403400d26404020007080b0741542c0d014050b20031440c00d540d2140c010f41c0c1d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 464031276 1250 464030026 464030033
    0x203010b07020f1809071e18020c010f0612050c030105040206121302180106020d090506030106050d0b0301020c010b0306160912140f100b1f0c052a040e0a 68
    0x29181c0741d607030444508083c41d030980041a421400480000b56441c402410301503c0140420301c1403d0f00d44c09211955a40c006079480c802c1d802852040251f1030051240359031114400da405880446207900000c225102c1d00d0740072a090740c03c02d8111003601030300d500403d01003000400c408021000250020302152a280d00004c0c082d004926041620700340d5200060025182d2101d8071003050390081c40c100d4030031000c00304a0b00c0a8002d005020161040030120000780d0b020f00c11000c2211001403005155030300b4a4411a901d40008074650303000d603100c00c1c0144041e40d080c0044c20000610700000516140320300d08041c40d108015021009e00350038410700500301680701c11580b09a0b41c903044070320840c0e202031801061211a003c035820f21801350200c41c0920610200b4004241c0340380d060305020317030f0b103045003008240c8091f41c20400821551414090010b8050b2281c2c180301d9000d007040d10311a8143c0400100f00e01c41080d01c0107241c55030340d1034140b8940f41a01c1040301d01c0380c40f11f00600100c0300564 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 464032526 1250 464031276 464031299
    0x1805090f060a0b0703021b01081003230102070515060105040e150f190e07021612050c0607030203030a05130201020a1b0f0f050406060315120611161401020301 70
    0x203012205098150001440039120100380c60020006019480d58a01003410000d444051490840b44111046208040305600c04d44505000d201c004c01458009451940c52030340784950320868a404104606880da84004280702428880d40204080d00c0d9144c8810192544510001c1c260307410b00c0030510090004d003640256603540600b5000401c50707a07644420000389404030380070215600041c4200ea009440050341d003854100e501055681c291034448142c1039031905c0b40c030368540b480f01e00801c40402051001d02400d80b0801c1c00381099801c03c94a400101d03d540d4050a0140c000da400001403209502c61441107540c41105181c4c1c40d085510381ea40000d48556043e48082d180c10940800040b5003405540024000c100a6082140311513070341d0b215003030424641c4a114451803805c403000034114020700a00300112504603c403c019810710700f0201124900c40025140c2c180d03602580300325010040c00900200c8200000c1410f44c0703901d4038210210204650914440382d00501c0100880905c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 464033776 1250 464032526 464032531
    0xf210f050604110720041b02010e01020c0312180d020610060903035d06060c0b18030a030e0f0708060105040e0c040c1e0e010203070f051f0c180509 65
    0x2041c0400c09030354030000c00040301700d640e071380c03d40c403600c0c0c022203c0040d00440d850740402111900241320034407080a0b414200d000714801c1000a42042001d41c084001e0011815800181c81060125100c0060325062504045605c070101503803103c414444001d0030440707803000410300e52500108841c25a60020019508100710310190007401260b1545c003490340f03944a03454403035200300c8500784409120010040140804c1c00407070955001c81510707030030100d008140c291000b0341c450420301d0360150764505620714010b02d201c425440c10925058101410302c0100394004560303602050740e060f50386815003400c2c01c140d01c580f01d961141a00304040c04000c1005411030302c003101c0c0022040350309078040e420901d0403a04c480e07100f403038400e204120540100f50004803030b08038032481c1c12a50b40c410301640c1620415194601603881030051038000745064001f41121880748055510303000032521105007820081c40c144003410f0b1900b03131170070866900028400c000341c600200000071312b203010045010524003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 464035026 1250 464033776 464033783
    0x90603020f091807090518070804021801080105010510030219030b0301060b0c01240608010306051509090a020103050c0f03160e0907030e070e0105030d0f210f0506041107 75
    0xc034100e00020325001c295180c8480141260300c88044000d042e44468208461034000305142c0b42e40402d49007040d0f0052280c426a01280600c071740c40d215016180141c00400880c3e000002040c7e1040044000e00018000d008080010980d941000104000a0000f03842c001c01c151050100303e08582a40c180d140b44104035041c00591107100c2d0022a01504898014200c00386000440180114055101f00c409000184148200e240c1120584086c0800c1e44202c10000b00c6007001400410816170085400c00808100074440c2907402003c6410980c0459806a0781c1d08403a0036a405c0d540c240c003650ba0300c40d01c3d03881b096242401402880050340005410000800d4881c890000c039207005e40b1000060b0710008000301d8042c030348000d00070f000c0c02680030071040601a007800025013004280525050303c10081c00381c290745540b02c2d0201e8510210020030020424080308031001e00c410a0003c001e404065007002c540403c2c10b40499040d00d0015100038001d902c0c24254511400000042d0344200c0c0c1d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 464036276 1250 464035026 464035031
    0x309031c0210090804090c050c0c0f0a090b0103060e0c19021606050702031e0a11040507050414031204380a050a030b030102030112030315050901140a090906020702031c090603 77
    0x4504104c2020300864200c02019860300d40b82100c05908a03000d840c616110300d08070f443e4240c0c0c3d5070520860a05e212901a01714281180c00d114800458000304c044070b4043c03500288069a41040e40340a02e41542c1d90000024000750402d480c45c0407550410040304a40018440c0705030216440081a410784148000c103c40031618204558092204121914084c0c03a5000c1941c0c45c10421601e0b001500300071104050441036040c9107041a01076184690b4840c1c60700e60505d4507060007440c54031141c80000d9454090740d5040021007580c2c9000e0400740840c61103811b03101c40e21544440d84e14021000d00c6040768004182210180c2c0190200d480c07094440c5030142d151100804142c010b0403020080c10341c10750021001140589616015100c264060742c1c0501003410301500780c03904101c450040c2e81e00800709100510204044100c21202000094514644035996505003070031907900d100210303a1980c00003049000d62030208019044162000c2a950004881c00c0005d0030080d082c1c4140018940c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 464037526 1250 464036276 464036291
    0x60c141b0316140d0206040c05060a0c020d0b0711060103050d0c1a011e060f0206070320070f05120a0806011d0d0605040303180515060307170309031c0210 68
    0xc00610503502101c024100e11008409145001203c3c64100943c4142c03c3c07003400390b40f0321294400902c0500868201658100e140d0a00c1c05101155018403200c45c04d10544c0c1e500f1000689a910011040700e014501c0300c03145040101c0014804105100d080b662030b8800b80040c0041580440e0421804069007000000c240e21898078103550b860103801c04860080107000002d104485c201c003450410b1304070681e40d18183c2c4031081900c00402c4040c0c1c0d41d0060f0300040026000b14003d40c028049140b01260380ea02c61802035600101e01c2d0b01100084840d0172129841034104001000003104070001c00c0d0b1032608000d4040402400c8038002800e60b0704000182a000403480018001c840304528058461080d4408508094024190988044000a191000c0a60000c10060340c242c4450341c000040d21403504600c5440500140c060007040e814041e40d4000500e1640d02a4603840a4516101035501c0300c0070141054208507407031807110044c00c1b0305079134a909158041030305100e90114034000103010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 464038776 1250 464037526 464037577
    0x30c0e130b071e0f020c01183203062815030b040b060f01140f040b0c0d02060108030f0316020109060c090f050a080d1d040216060c14 59
    0xa500006001d040800c460381840141948402e10001c101004111400740c90141c0c0700848000242210304801600b00b260002c01d19889010005000b1100650101302e90785c88050718008007007a00413030580e11500c050000d4100d4650340d000341c2055400c501400f141d250084030781400000542c0322003805c01d4000a8655040229485075003108a4803484d42e8a071516450030b100c3e175150545054035030184280004640d45050309082c01980300694464071070308c2c0160035061207a004065403c0b0b504c2c00a200200c1c1d0502040045c0c46485000d0000300410f4107850000707801e114041e08034140f503070401c0104500c2804c420045035041854001c2080311455101d00890041c442a11b000308128103081041c1801540b01c010101940c41c0c1244048a00e5a0341c400c024400d03010748540b40c0180c0140400110040c040d031358540a0450141d02d4ec207480502100090032640941010704000041c0302c044010b1003100d120b6128856082d0400e14030000c5020741e401c40320300842100042d20448010030541e0f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 464040026 1250 464038776 464038801
    0x90507050105071b060e130e100e033001090b0306010314010e061014040902090a020717030a06030c09020315040b06070f0501020c2104151e120b030106030c0e 70
    0x100800fa0444d1140c098581740000c0c41c0b4400a02610b12521121000583c00074a03131081001d00c0c0030140042000204c1c0300080e001500d0180260030709030200313100c1c001103183c51512003e900f540300e03000d00222031500c402180300d48406030403058003207160182c4081207480000c1c080c3c0c1540d0300096101c81e40c40300c40305140e02400003600c8401440c0240802d200000203522104d2050310440a240ca082101c900244012513003800c070080d51280040c0081a001c0081c0d134010014240901218411080400120b081c1980140c0740e172b6482561303030382c1d080080c4684100e83c0c03c06084c1130039040d8034504000c000380d88000242d05519100300c0d41c0340d107800d015649001c1214840790740241e80740b1800ca51800c019000350801c0580c0a194002c1ca052940b41c0e441c000250030184000303c240a06060500c4400391380d001d10104007809202030f1803402da07011158070400c0341c0440450768404050f032503c480032005481001c803100740079078105031060000483c20408081681d01508109545076954030514a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 464041276 1250 464040026 464040053
    0x100f03080d1b03060311121513020a060807020105060f0303031f050a03140c04020313080307090b0d0b010f0509130b031c09060201140402210c04020a110c0409050705010507 76
    0x2450b80d01e050070803805406400070002c032409176200302c1c0802c41307040a11040851a15840142d5007081045440004449400c55000705c0c03e035507048000c83d074035404108810074030307000940450102410840b146d07509014850b0700100c103903a04440200c0341c8022035683e010180103421301403424011640069440880c410003044001c00c07011016542e4202103541182070582040300d8010091040150309260007160701400740c0c1403440024880c5e940f15a0065080034150342c01300000800002950f540c40300151125141803040020400310f130b42c00150018401080260070b10105211200d000d50302c405d403800085e10240c501041100203140003038141466031140018000140455071081d42e1b000e50b55006850440d0001c2040807521200124020400c81c1e0003588554003901d241420645540000d0191031030310704452880000f0400241641c100e4940040018011500c5400d9080100002c1085840948081044420b5a201c003030302ea400d18010355040c8180003451004104611000b0003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 464042526 1250 464041276 464041301
    0x220e0c250203010e06010b120c040b1e130905011d07080a1a10170c0315010c032010061205061b07170a080c12160e03030d06050405100f03080d 63
    0xd051b9038686015860b00d421850300e0f441e407070f200300d00050300004a01040350240d6001000c110b042c210a120412603035024100380b089143e1003400404680905001414068481044040b419605104405448002c06510096106c00260a0003200b03900714022607004458800041501c01518445030315440d03600d00c14a410101c840603120320140d00c002c1044000440d4201c61000f52a01c070b029110740e020a4409502c56001003800303602c598014030b59025024468100645803074201c1c040810000c0002c100c0500a0b0451504d0529007481e51040002402200940141c8483c1e192291662080000c103600c10710b0003404e4440d24402c40c0901920146644034a00b040d000714078286003000c98122100074004584441d000c2280d5149110980364542c8240d0000f80032503484d840607130190002003880d60705100b549000d009070b90310144000c1400b00c04003100820303403038034000c2070001f1a00c004040c1c1c0fa0540b0840e40a0162400340c00c4010300f00c2e5044044203448401c10807528004003198441113 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 464043776 1250 464042526 464042533
    0x2090a050c161109010f0308030703091109131202010903080105090c09060703090306051008100b040e1203040b100e0712020d0501030b040203150723220e0c250203010e 74
    0x800401003c070700c0010340d040080d03e4803182640d884054285051071070100529100d803c1c03000400c288d109601000c003541c012003c80318803515800226502075002d031040407885100030409000c1c08940341400c440002117100030800500a83c03070041c203909060280d1481484590041280d481030300094401464000305440d03aa00e2081c44e010703014001911045412a09000c002900d03210b0f000d072010211a40b8a02411903010b07110a258010030700c20440315480766664000c030310300c03035010080d480e00142480b00380e60b81c80c1410b003412410041d0040468120100740e404c24806000b60701005030b044038550074243c585101d1001070501900407040410789203407414000006002e501c4c41e01c0c81c001c42c02507041d11204d10080540302000481141e8000101d03444401502c100031042902280080c084490304c1d0a02038068201102c00002c0c804900d0300040303044007446107900050806400c9088400d0741c0349000b0012010700c00300350f040c3e110144100310f014001006d40d2000c0d0091039035911101e094 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 464045026 1250 464043776 464043817
    0x506070809071e0317070b0c0304020f0103050618010902180a06140309070e10060f030c1b05160605090108010602030a09050f0105090a06081503060906010b07030c1203060614030402090a050c 84
    0x3e0164507002102d050707d1601c244000b18138000c3c00982100d028a401412211000002c43d0055015040140c0420340191415130041150400d1801d190f01030308101d070015070364030450607080e4030781c50070f521145204283d507050401c80c042d000800762502e031800e1141203480766a0640356a0074043c0b143c0c00f605c02618500104251411144011819200661910303250114040c070110200c802244007040803891298030728010b02d1414880701e1002c0c1c4110100c40c03074901c40031070b4a2904100c990100c4080381020550390030541c2c0101c503103030242c10144000c500703200384c21400811a61301031007003e008414400b060361309a40718500716100a000600300001c42c5a81d0314009040040855444607244074040854909150100f105805a030418002307100c5d6909081d13072040c055100d03001c21418272844460202c006000745014400c1000f06440c0000e0451070204050544848005e0a4404102c10401c010041c1d0710522a141c00c504044030000c0c9039580e041d0121164030401016545c803c0070241c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 464046276 1250 464045026 464045063
    0x1210020c0c010f0804020a2102130e07060203031009020a120c110d0c051c05070b01060216050604062f01060b070c270b0105070b0106020a0506070809071e03 69
    0x100d001907580281d803003401005154808658611040c0c1700290300100711801046409000250070f640ca110400510b030700e0922940c0041d886503054510340d0f440580b80c5180c9442120103100c01d000030142400175519615004501d551408418010001d030329601040d00741150340301d00e90600d03070035124038400c000201c01040003500c91107443c603a41c2201d12907110b01c803500707d115000501305540d01034018005401c4548000051103031055500003000003d00030300002c02c05220715240200006d40181546403d070f0140c20740031086980003180036080420080041c6507100c2c0c601c0a442a00d0054083e510221440071108040f914065904035824680003003684200da500034001c143c4900e00791a0f031700307985400e010101c00103404a07c0d0f04a84800741c4502c1c15000350082da10035107052400c2031030800c05554192541c070342a0000e0780140d200031040d00c20030400700020f40d00140c0b00c1c202000c02d403428420103940c50800c1d02032108a04100440c1502d03a0b01054064806035a0000030308401104511 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 464047526 1250 464046276 464046283
    0x2010b0a06020a060608011e02030a020904151d13020904023f0c0108011809020d110108070c110f130f09050715050403231b040c03050c04051210020c 66
    0x44240e13002854003070001860001440341c041402440e0003000a0b00320ba0030307480802904010b102d411516020414514030b55610702c9041c0401d1004c0810343c405c141003034140501000030941000403001d0650a010910000b60340d040d2019a048038000ba055441c2e101003805081c000003900003401c50665044e130301c14203048001d45081105000c081d402c15841c0307405503a91000500d2140450b21751001800301d1071002c5855200311410750000700c0c2140e00c550110380000c008840aa41c00c429595808030603603400442c20340c00050f0f503d0080344031102a1a504c4440300c410304c3d1039209071100051084240c4585050042e00d03074071024104050000c001c88000948030f0010200c0e01c501481201003042104103640304a030003039035a10300342420709680c2d031200c1413000130403040e811a001000c845183d14040000021640e2540f0b080d130024400c19040c801030320791100100c010b0500304420440c0d503141c41d0007070307408481b02142c0e0901107801c0c440400d42444080b5000c45101c5000281d285004003000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 464048776 1250 464047526 464047543
    0x31e0105091510030b1008030d020a08060603090d030507032901020606030d02030f03060a0305100c0306080c01080a05060604030f0803041b1809110301020a030603050c0616030f02010b0a0602 84
    0x50040d0b5200034141c4640100401c400c840349443c022400e007042c40866500c030310362030380710307080c000402103082d141c0c1c199a24542150700016140c1e900010020301d1282d011040c641c11076829103a280c02c1d420b05503c0e00b9241c1c04004812400c055030340c0001405507209400884080d000c0104d01c5d0a090400403401c51103501785640079015105040c0480d20a0600040c81c2c1034041e020303409541080083d4003212103a40c00601403542c81010b400010010a000303000542c030ba6035540c480003500e10f03e9203801501761401913129460320b0700140b80300680759800c01090f075841084410700003015502d002c001150390090b50005462036804a421030b0810050748011405580a420446480600502c005005407903e014150355651440003903030400c18030750403211886206080b2810003111a0000c0307401c80e00024007480c002511442c003041404800e1007400048c407000d5850500d8440700900032100003030703c800018200680005501981403003035009800c503000040c01041000e039640002075031010b90 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 464050026 1250 464048776 464048791
    0x200301030209060d0f17040f060e100e0d0b10030803041202010f0920010c0b150f040504020f061308011e0507172a161202070b030a0b031e0105 63
    0x20000300b5000d28003041001320702c42d400240c01008040716a19540011201d203088045101d003440301190004e080d000c0f10020f003000c0e5035041521001041085403482d0100100b01c180016501d0310070300c54841007101c52055403c080c09100a07145e448000400448030351020300300801c048240b02c100f0900c400038441d010704d1a402030103022281d035441c3e021110396040c000c080001c039511901150f0360b5a09521001e5405050144400007540c584410405080b95216441d1191486400082c0361132031040260460558003002a840d007a03002c01c50031102c41000c54820040454580484c41c0c401256601030003c07034009001e40303010024023040390408a00010009030400f00001c500c684500c4103811260301d800b00840c51500d5080c1c00d154628810307010062100c0c00d484103410394002d640000c14203581182d1030021f0b4000182440c0008820104010b411500305030b500300603402201c0252a04038140740d02c00907100184000192411352402101e8582e81e8101209000411043d0302103440f900301d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 464051276 1250 464050026 464050039
    0x302011a301005041b0f030b090309032e1112090307050703060203151801030215070f0b01060f050c03040501030209041e0609110c280503070501020a09060c1e062003010302 76
    0x10040b003444514803940c0039400c86c080c1c2ca1003042011443c400347c2180c10500c00426285040c11f1640480d0a00c049032113010080c00b00c080d40040030f8641d2071420420582169000c100200340400c500d4010f12030761111503440c0c0c000f0707404681151810b00c1222940d83c1d10030100c1d0f078501d61340d180c4440607420031100d0340110491010b005403642044190682809003034002c3c1400f6078216820070030b418904007400040c44000b401130100040095101300420340c02000c21600b50744c54000d000f0210030a031000e15040003c28440d840d1808000000c0d40d042d07450900380942c41d43c042e10040350042c4440800082c0341082025104480600359011209442030404244644104040421114403c075070040503150f109841682142c0e5011030b0109003003051486a40e60a40b0a13161207185400082c81030f2226580011180e002c150400306020017000541041c255444054803030304040d08a44100709400c540344040c0344200901d661001e940c2e1121049981d8090368000091300c1c1c5038109010403802043c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 464052526 1250 464051276 464051303
    0x105011e031e080f0a050415030902210109170309100b0d1104090b012607050603070c1109011403070b070b160e090406090302011a30100504 62
    0xa02060004196500030182c031004403040503a41d042c030030b80360000350355460044c0b00007990440e850004003407420f01c956134252a141017555482c0d0f10740c40c0d0501c02c800c3c1403400100b040181c4660103aa0300000840030a005a610955040c07030141c1040640288030148a12020721a090f500700910301505042044808020000e2900c104892442954952141c440b85042d0f0014450654a10040c03030b014001007905200d07642e91402000080e0001d540002c0d014607541850900c40c440c616030030401c0300040c40c5d01072030003010898511001c1d008004014905804038180401d0103481c20f228000031b400407443c0c0da51980c02d40c0000c141d864031107200303020340d40740050702c0390039541076032680354105100704001e40703510348030105441d0420306907403c1c4003054418000e59507c03a590b891089020701c0c0c004c5581140c51600070b08645130b040e0280035481c1e6103072061300740303445914880d03240020001001100e4500030b940700c11801100c032255002403040b499501c03c4503030f50707411140c002d5103d14503070408034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 464053776 1250 464052526 464052569
    0x160b0a060e06120c06090d02090109090213020307050f180904030e1003020c03090f011202120a050606070302060406050a150b04081203041a04080f120438060a050909010501 76
    0x2685420003540c200d40c45036136190500c0c600000205203200c4000c0c058260b1402641c04160720300826800418103642d941c42180941c00c3c62652100c0e1900007400c11442c1d450007620251240c06009402800d40030003140b00e150150014510190200004150188500d8245001070075a8030144001d0300480c2c95880340404107000380207542c00343d01e1200c0694201240b1800b440940032a0f50f02c25070400c46071140b00b442c4081030b440140031449809120034054070748485035005560010b07112a0140c1e800304010782c0842d07408509140c10030b81c070003004036042e15451840c00141100030f1034080c0c02c0300503413000602c00d1190002041103411036416601e141010714609a40c074081190050310170100d44034500045010440c00c154807070720a1005909204060804107003d400642c000b0440c00d2821090000f8040d501507900031220341444c80034001028002c0386180000d44050382e89980c000400400c0240c0d9a0004405c0074080c007400c0440c1d81d01d0403200c00750191400f0311070500580d1724100c200748003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 464055026 1250 464053776 464053789
    0x70602072607021827060402100c0201120f0209030102041e0f0302150705031308010c170c04092310091103010e07271d010b120c160b0a060e06 63
    0x282a0001c003246005408110042c618100c000c1140c60010301100702100c0c2d406141401042c80e605d0100100418603103481800000750010b0720480c1800890b071003420060303900803528405c20646007000320f2280d105915a4020f80201c01150303604d94008107012518800d00040c1d8031010050038200301840e07544114051564001d030002a4101075444208045803681c0b40003004098800c20031a45000c11030020b408141c0100c0e00898101d07511603840c060700070b82c40301c6a140d0b03110034002900c03100c1c102901c21303040300d2042c0d20460400586030003450082298446091284100d00d181c0c481042c40c0c141d5075609007040d5809006401454183d02183e0007640c14180c90580b14590b9001626440711107003612810306940000c01040ba2559001142d800d0b51250307180100151a0187c3c90b9030204500c0c1850001c05030462030000e102404401400c06d42c030128150000b80d8101c0a9540b42c0250300c0280180c1001ca802034007240b11282401071b40895a40035a049030912000c130213803503d410040051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 464056276 1250 464055026 464055037
    0x1e030402010e0d0305041d0a1b0e0409020105090301060e0f1b1204020d050d180e06060a031e0207110103050c0a02060412090e150102010507140403030806060706020726 74
    0x2d280350038220450400728180c003810790190400341d08041d0740d21078050802c41d112144510850286080c000700e040c050080102c603c0403001c000c2e02d4180786d000001d010b0880c50044ca8860f940702e4452905690140342200d0343d51401800031b1004c0f5450b9000030030000026104500c00541c4100000c400c560390b0301c401c01120f15585d42c101d29100d051205400041000361050b80d000e40603000c0e40002642c01c000ba504101c01c0f40c0c451844030051200d80c846410040d600c0816446419400c002013a0b40e50070481c0e245a41d503080001c2c0e102c042c1c0c0040c01103902c030211718050080c8009800d00500c0092800303d80440030036642030003a540c61210181103402140412400341e806280404d000400403c40c80403030700400c1c5000320006917039100711480302c1c82c29a0701030011868070703504040c156420b00400d40c0c049201e04085096020075405082d0901c681d01c000f40800a003480416299038404044030320880d00300c04c0641d1100c2542c20141c0c560b4403200400c4803ca280440c40d80340c0821910140c52 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 464057526 1250 464056276 464056279
    0xa0302030403021314071d03011a04050c09060309010608010b0a03030e040903031107210903020d0b0916030305090a05150d1a0d1410090b01060c051c051e030402 71
    0x6040c60701e5503092241c084144c0c126400440c0e121800032400d0500011070510070320465403100f22801c80752140c400381003840d80b04207000364140700d01985159166005812414419580000d1550705c0c070b42461281d00519143c1c2d580058000144107003c01e054009a0035a04900c008000005004081100169440c403008002c102e855869082c01d1070142d01180d10715000c1c0c1808602c8200c415021000c984c00721004032400021502c21192020382d00b224060440000d040000c00c0740d0543e00061042da40d0030500901c0d000c4003400207451900203016001103002c0700309200108903140d16000d4816044000034a00940c120350002865203800380807402140f00c04c0710800d24083c0141c2d01c1c43e02074a101440c40e4405c8202d04101e00f0720b501d41500313010382103000b18654040d102c900314009003011118040500800d0400d220500410720109000f0b0464802d810200006040d030710707143d4180f0184411490911207802106041d46400400800f202c0c3d070202901c0c2c42001039040740341114002510b000c0d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 464058776 1250 464057526 464057533
    0x30209160306080d2001090803011d0108010203010b0f25201e042408030304031209020117090a050d02010b040b2706061c020405010e010c350325020a0302 68
    0x3c69611170945204505511090004501c0350069108c0750410350003032340000c00081c101d000709100c0f0040d1490082c0980390200003586035500d0800e03641c1c404c2c068496080c62002d4002901d050010440078840000d64a4100c20824000c540c00c0c0310b100344109044204503024030032180203803031801c00210358200c20307114605103942624400b03220090034110f807885c8170300894400c00300324002004040c50041509400440da6850a80b80c0105040300c240c0d100e85400c2c1c140080100180c0c1c00c02a00307041c5907003d49500140f556140c11b050f1800104001c080d01c07600a4038416559281d040d00070300d00e03104041c2c42c00c0c02500c1d1131609209041440504010b00003003035114100e81e242c1c0d1010f0064110304005c10f21810800454002d9a903030314101c104508455001070301f0007655070450710440c010351090801d207200007520b440340d40440881c00c2c3c51100d107100e940341008011103825460001960f807101299120b18000c0c3c003103034a418800303410300009903021445614403071001501800c00f65059000c1d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 464060026 1250 464058776 464058797
    0x80c13181406060f09280f060f06170c070f022803030305060307060909020d0204150c061437020c0708100501030c0b0a030b060f0a0306050402090303180a030209160306080d 76
    0x40300c209808844406d0030103031150b50240d80b40c4103a014240140c0580114941c885141500140a5803c00b441007405201c4417420400302040b80c8054940c01368126003d00c0239901d0078400500d800c10001c100b41c01140101c10440145070164010209803846a102009691188000c05036034400c14072030040002c0c0c0207003080c002c2d415150050310320440015405400c02e911244996101d06090342c1000020b0b020743c140b5003d10104e030003102c0d41003e2101e41d4070824108a80c0c1042e099581c00020300c200c60041500068800a031140c68011880340301c81192118040600d05869081c1442240c40500c5900702e82c0aa40d002445414100c9600a50026145142029a4000360051071400c2c00f8141c1c1c4001114240d1281401030000750031411250707507100d802030b40203021039015400c0540500d00c10300c5420110788002040b0348204c0c90b0751400340300c9407a141c400680b034050f0a80009401403024000d0009100b00e61914026000039500d060002585070703900140d540400b410740d03800080b0990790 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 464061276 1250 464060026 464060071
    0x1050c0a14070f060f08100311100210150e1605030103021e0a0b09190b3a0c021b09010501050d0906060806090106080c13181406060f09 60
    0x81108003509201c05880d461a510842e40d114140d050348141c4c04105442d0561150a51126015500002110510f8161030035910380403205444003121500400c4030a002e0b910b000d000304590001518100f9061010030208985103500c00c9441c4107040004501001280345650402e1000001c0d000c00d9640320b0039a840d43e000c120084012411544900c0a155142003407034582a1014020b4007c011300260341c1e05100c01440400403103a962014040c5803e21b05002c000340982c03c0b41d0020421141000c42801100d0902d041041800d025a0040104801078001c0e0710140d0090b40d249109030b020381d40041e03c80f1240b15910300300c584040317900c000c8140040c8080d600803400381100314000316000903940320b2070b0358080c110341c0260000005503208108002c900e4409000c1c0c40054408280078290008000e000326900d90004803204207000c2c2c0b1480f003803603c80c840118180031a5004070706445517103102454203032200c2c0c040e60b07268020510740b0100c40a60420b032130313054040c0080c02d0780c2c1d40307841d11001e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 464062526 1250 464061276 464061293
    0x71404060b0313021f200a030206070e030c04230601110a0b0a0b0603040c0e0105060c0709020a02160b030a0f0603120e0609041e050702060702120c0a1a06090601050c0a 74
    0x804c0b40e00204151110064031000b0b03402549013519034442141800090802030300c07220103d15030104951140507400c000944c00b19100d60080c69604091200000300000681864840107009801c1498101c0d94031b186000f200c11000c181c4842070100c41140c440d80c004644071584081d140c202940006001030006404202c1c1a42c0180c51503000103040c0000000601280c0c410340d4280c3d0b1a82c5070040c103002c1c00c5190000d01b40105422120607103411030441c031454132a00c140c41007000740796021540c0c0c0a840c0c024000c503480a18510703500c25100d52603291a14841e003064031681384031442d107481c81115507928030640e825a50000201c20700b580c07100c201143e5405c035014000f6040601403009006944890094440b0b000051185444818004150804440008201008550141007800035003a00402d08001d62110070310311503510043c02884919000d8010401410404181050010300003000d1006015220843d1103084603115500111568007600000b02880d03080ba01c5641c001610b0780c1d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 464063776 1250 464062526 464062561
    0x2090102070b0915161104022a070902040f090b03031204081803060a061802160f030306081009030f020a0308070323040809091012032a05071404060b03 67
    0xd200d131241d5040b20318072a02d00d400c00c00020b1802d00e0303400d01050400071000844414541c040d14214203010f9085e42c02505101c01080712141c44440303c0320b400000c10706110702c1d0003605030b0f030b20203550b12a650b2842c02e41c210900d00c2040016860001d400c0300910700401240c0a0044a03540c01c0e5041d01c0fa501d0300c42255100c0d02c400d40113006036511007042a1010302140307100e040e0f942c0b0700240301e42c030b00346c0560302c0e94080c0810000c20f40d10402400540100e00154010038075041940c180a0400a160075070080000350802c0e1480d1241d90208131011540b500800c6c50103200e5510061607002850090382e4808c0c803a040200031070080e030005440315100f5400340d400a510003c50041d880694040700c0f28000301030b502581c003001c00240c0025181454900650405a000004602d50346860001610001c1ca810000d0402110701003400c1041d003080c10303101c0c82159003c01041910b45a290450b0b590700d081c42a4002d4144014041525140c540324050031034060b085044c1c80c0d981c3c0c0c2c099204119102 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 464065026 1250 464063776 464063779
    0x1707050406090b031306110c19050307060b0607060218153f0405010209191409040f05060f06030d05040609090c02010603080a2703021809010b181902090102070b09 72
    0x2021101c041082405550030641041c4080e82d66000c0e52314404c0d041c40203080607100401c04203801980001e00000468000503000f50000800381c071203100003415403240003809840703071703001140000003241c002d480c11130250f200b181d03400d2948000b1002617155000d00d10310403c00d00c4601e582205460300911110b07100c0d010380d14404800705907480c08410300b80011344058541d40c0d0301241c480b29600704083c0c14419117a038585903064407480c001e41c0c450394030104480f5601601910300401d040104504031840001d60080640b00709103400810080701d10000c40d000d0b48244a140d0781400d0160103a0100c405071901c66071510012824803114402800e854000032045645e10f240000105003181d003d88501d03006a92041046180d60490011400101000000c4981000410401030fa102c1004040728800103c14140d903541b0498010b00404801c56810703040061041c0d025040e035612002c42d4840c0952459140c01048810700000032401503000707103070269000d42414400c00c130307412015007401d100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 464066276 1250 464065026 464065051
    0x10e0306280207060614010908030307050a050417010c020c010302180d02030a0501050c07030207051c0308042301020d05011e12080c0106090207060e1f0e010216031707050406090b03 80
    0x1e00d00c81100c12a4420081030724502d5940d00107101a106032001d9000d034400034030b402e01040d8248840e442d260310002c0d01c00c1c020720038000723400b03910180180d042d81c00614404111106647e24444520b001e07000d01445d0303100501851000960641c000d10a62700181400b5424680c2a240c05045c00060030b076850040e60f1501c512051480014024024284911420780c40f007a102c24007031801910746405500070034420707a01e503103017600800607000d00703000540e406213400d072083c1d101c3d8208601d4481c182442060809280d02402c000c0003415002000c0044403400104a0780c1c0c2e0756a80303801d104651f208901501c05d00356204006880c03200101a10490041503207500d44195100038508448096204a401c150045015803d01406100c0e004522000d0009001482c500072000303213803165070300200717201541d8868914004101c00d41c1074a03164044488582e400e10f04900f406131080c1d00801c0300c0c031080c11110700003440341403045042e039007110346ea03484004400742032001420503600003c02a415041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 464067526 1250 464066276 464066341
    0x40f09110d03210902010807020a110f0f0306012c2a0c060103051e010b03060601030e0106050405040b10080a0f02011d060a0807020f030a0207090f0603240b010e0306 73
    0x200c0c0c50400781d80f05034081e500203a02c01091001404003800108030700103542024006501007080a5602882c1e54402c880307184107403081e030000880e0000303030041d02078040c450300f000405d4102ca80005045094401c102e20f081c00381b0131001e1049504c404568188100844880c0b9031305082881403149281138910350028141503480718014074003402640140d46941c0111480c96508440e0000c2c0b805005400b030007484071030302c1c01022980d14680a419141019928006400392460030343c0114040c1400610620241c2850308240041980c140d441c007846222211002922150004148400560061548104005c180c0040d070f0a4010441e1555851316100d48a1003250340d00300003050001d4240d00c2d080094100389000a00d0b250b40455116803540c03013007100100c613613000541c0408940961001243c1c0030303100d0b802c4801078a0580d10060450a2618076400000c180c4a401c40340f850907581c007001654580b0004507100030395885c441d501500000c000c41c00c0b9024024143c3c2c3d016100f41d49080090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 464068776 1250 464067526 464067557
    0x70914190531020a122702032103150118090902060415080a1a030703081b07080f0c0a03020d1b0312051201050d120810080a060b040f09110d03 63
    0x7510441c00c072007405900290003401c1e150402558409240300020070031060342d1400303520071b01156042c02050078000e4030f41450304642c0e040140e080714410780340246a50030200d100040c2d99810a503404817958061940894155215400c9902c3c0301082c01c0d030b8410360743e26294140e00208940c3ca400d980017201044013140e0362203010b540c1c22081c0c500d569004010310702148448101c4040141c07a0210f0080d21549500c44d5070300085010a603900000e03000e81d140c2080304c55402c0307003200322100c0411307000e80c090000380d0f0a00410020503168145003a55484520340003005074007241400003d43c001c40665a07400410061129480c0318401c0c118500c503066141d03140c102c109c81003441c1e4003001440c00151000a0a4100300403801070500342d038201810305d03e55903503000c03450405200c98200a2481c00203000c080c0c071080084000c190500c2580d802444906188014148614100e030080341044103160000a803441072404158100d0160315101880104120545a00420a43c00c00c0103c03401504503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 464070026 1250 464068776 464068849
    0x51906060816090e0109080a0f0c02090c1309050603030f07030219061a04050c030402010e030a1205040e090309030d0806010216080c0319030c0314120709141905 71
    0xb005030403580304404034944003000c1e05075141c0341c0307502540e83d040201c613400160500040d900141c1c21414540048000400c0071900d8140c008406035100d100401403000c0c444d0a41c005107a510300214000061a840ea003025080d1001035480c1d1750550b00c10030252161000d07500c054240a4400c0c4113464008050b44240d0003030740011041a40c14a941c4d20503801c5000b46100b030008683c034180c03000e1100d40381180c091951170000810180c11701801c45c0d200c80c010380c0c00344040032010380e000681c080310442c1401e00030515000303406035042081400020a407000b20010030395440c0c0100800030401d00190740c1c070494810101404050543c41a28441e0a80c0c0c4000034209018101d00c40c01450458046020140b4000b454240c1d24007440b0442400800f00340e008035080c2142d81c05082032803440701000448510f0748a804001c1c01d049070320340d05004403a03030700051810031606412020103140000c0420084510780c0074840c04e450400c007040c2005641044000250181107070b05000d01d82210882d2003156 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 464071276 1250 464070026 464070043
    0x11a071208010906080a020d02090a2324030309040c03020c010c110c04110328020a0206061206060310051003022e05070c12060b0a2601090519060608 66
    0x200e084800180128003180c851301c0020b014400003440060a1500403811a40f00f00c0006801042e2107000030700143e115070480807400440c40d229442e000c24603030030800000020f903040e0350f00e5442c604011920001080c407106202e03c004014501c0d000305001000001c1c41840030318401d15400f4040880806002e00c40d080584220ba118030841c6c680310740056003401400707969544500d2414030400c04001c88a400d072544028509000910b01603410500544c2e1107244903a48180360002840000b042c1c1d0204d802406120241c07400c400c8040c10049090b00c40c03604070760303a64060b40410200c0d26510aa500140c0c2c200c0440100410402d80f41c2e004600d40800c3c1070b40e40c900007c0090324980360801181d00326050000b087c60001d0400603240da615900861500c11109030315404524501442013a500440d0034070001808891041d944452010400b084121a1210358810307504000e0744100c18020116900c1e801000f40003c41c04500760b0101c1d40304607140c15181c040d500c0070b01041e640d80c20819087c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 464072526 1250 464071276 464071313
    0x1507060f1d061f0315091e0209130519030917030301150305040309170c2d01050909011e2c09010912050d0e0316050c060a0206011a07 59
    0x7246070780a40e0446107000805010301e10072000c032a0240300c07141c04280e810001e50342e0240f502102c10b100180b41d21701038180080c02414035101b0901e000c120282018810f05a14800d503840c4040d651100b110351030403010100007408541042c000d0604140440341e141c20327101e210b810000c03070701c0ea220a152482d0a946003d03402c001e42c40040140031501c0b85600c8080140360350314091002c2d1619a4008011000c140708002101c201003690030b075480030502103102e507683d0107071141e5012881c0601d001c1002d000b1a0b0310912040c0003242e000b141e54070810494203142d01c040d09a29540e4a0300404400c64040e401210700300b4a072410010500491241c508240300712202100d46d41c1078407090510318507200260040165a15280d140f1000030240070840c1c60726502800c105413203030280b6000f90090714205660b900d072400700158160610f540340341110440741c0907a0885900003444424010381348035098803400540e1023080104180d802e45050070744011500405141418020b03070f24100f00041c860140d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 464073776 1250 464072526 464072561
    0x150a0e01091d071d0a02090d0f020f03070f030b0702030408031305090c0a0c03030c02010b060c0109120819020d110703081f141e030d0203030a06080304051507060f 72
    0x30150390702c0c0a1100c07082c0301582c02424210b880d212042c10241444c03074982c03448480140018404d0300c61036040d1007500d0005444200503201a10740724018020030f5030101d00c00c181035100b20b141401d001030000103403206084580f003803d0842e1101c06242900408090446c40304000200d51403000b032016202c05000481c180b006036040104015014100078684444414180442200180d00c07541c101c48558150038001000001103408034050004501c05030f4001500180c014028a01540300e010f005008100054039030b0782d20700045542c6003041e03c80320908080440c02c60b01c00b0340c4690003030189140041380041c04614015640c07007103410001d0182c001c6001c0303604004140e07000851850f031500740d481d0001c0c030260402c120440351142404a441c041c0300581c1d00e000085240200da1444100000c0858949840c0c1d200e000b076582d0302c100c445002031401c3c0360300024500c00010980e0240d903001015046816002d0041c00703119044400e098607465200c020061241d8064460550a461003c504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 464075026 1250 464073776 464073791
    0x90d0c0e1b09100305040f0203060711072405030703180b07020c04052a0d060b130f2702090406230a210c031401050a0c03090b150a0e0109 61
    0x1000d2406804090005003442003050190940e07440c281000c03000d415007400540703911b4a05150f14202040c440003501403081c102131044998001824040030341d104000c45440540342d84104440c1c4030303109001c0d402c414250042e4101140500081c642c450503501d0001840020749420244c40d072555003064909103000400c0c092816410700c03c1d1200e40c84191020310890921000c40d0054054000c406285113002e40400d81c0c600c80c00104032006256021002e115881e11227102c1c4100758000c495418010040c4500055490803108006003151084a00c0301c18150010390300e0105241a8002c05006c59070030801d11000d5179079845410b0240144044403200728403008111028080700c024218411621024100802c0150700c1e00b41c10184014220301d0800713950341c9860a5001102c0d00020f262072450032051001e4401588224840c9007450002d00608010032019001c0312355900c1c0c0580f0719201c403800654847c102101c81c004850025001d8080107955072003ca014081c00e03001000c07059101c843c0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 464076276 1250 464075026 464075041
    0xc043c020a18050f0d020402031b1c0605031c0e01110a1406070c0507090c0c050a050604330b130c031406030102091008061903120f02060c0a05090d0c0e 67
    0x10350060001520062484101311001a000c0300041c00000c2c800d84c1c0000000d16206184c0c1c12401090380c0400e2031175183d485006401341141c10070280c01545501e0218005180c1c64001288503c2d894004200d0311505070351042120861912134885040c0000078111803600c1e00d04200800080c2d0082e00104c50a101d080503203800d00c44050803081c00c0100103500d42001c5040412003074111025800000759801c81d51605441d40030482d030029200d40201030f908400c0c4040840c0003480340f44581c170300d070343d001c03400280c03144404a410080c0000040320101c2c4044144166000707000ca0400103180340031100107101d04509a80c100039841000989400e03035440d01c10080c0e004d054101c84220000c0d8140010720022a60800120381307031108100a140100310f007a01c4c0c3d60b00d8141d1400c502c2034803a501503101d0510a03842d0a0128030302001503281d08070b003298948003252280c011203025021a01d0404002c0003182c058001400443d441424559010009841583c5680003085402c4220444c0d180522 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 464077526 1250 464076276 464076317
    0x301031208010e24190e011503090c1401120f06050415050d1203110703090e0f06211501080c011202132303100e0c043c020a 55
    0x1e0010324410460030502c4440704100400c0900290354130242d00291100c0400554210741d010156455503120b40404903901031000c020754180c4021b8902c1e40001c0001100490441c0d5551001410114000380f0900621000c03903200f0825440514040400003c0041d034042200c0c00544220003c550314601000603003024085c0380309140c00040c8100c04145000c01144100a1800e0000e06c0034a03820b07105e88500780258000d1616600584c6002d446203100d01d005814200c05004060b8824000400100004000e101007480340c0d13000303400741144000101c248000c0005102c045003060041d070850045200070914020300030200400148246000719001400b122100280c807807106004100b07800e03103c0c844c3c0300454200e4031811600cec00307440b00382d043c8a80100d03a07248015034180101280074111051581000084801c007005840e02080094100000c40b03003606200034a250800c112030000d00aa1041000301c040c1c400442451013108100385130490313101003441c602040e403c00451001a4209 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 464078776 1250 464077526 464077529
    0x121e14060f150a0509011808031305120a08210901410703110a08040c080d0801120f050d050d0c0503010803091315060504031401090b0712060506030103120801 70
    0x5694224209000e00405040b9105110302441800000114840ca69128010908142c1c114810341c00000b62a42209500c07584400310240365016031a902064034900707030074a4111820702000400c04c08000e50340e400801d4004441d071b100e94982c55040303442120510f4400d248145126000010b28500545242c00d131940420403108100e81e0149241c5200900c540381000d8a12641340018840c0d036881d02c040700038204140c19034182d6a404201d0008598000a05900840c030595504c5030721500d81c416281d50300c3c0301e01080f0b00083c2c1e1200c010814007450780b5010810902420700b240012400e070f1174141c40c2c458a404000b000403030020344040c04009500c680c0801201d9458164a5540340c202c000d9a45d0190b400c503136204000c00032642031510045d5101056041799003071002c200c95075603d000751164106100507a05607c000e40041540320741840303118506d40d804000c00c581074032201004c079011019180e1840780b2036940c02010035a95100d2009d54002c610a0444c1c4411522400c0000e02c41d9034107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 464080026 1250 464078776 464078779
    0x3120207060f050c2128050603010605030f0a0b04080d14072604021009090609061403120f0f0403150504020117010605030c0c07050405010b07170a121e14060f 70
    0x81c403614004019141840003803d90f007814074445034031030104901041c03c0c5211510481d9550340d6a41c146c02100e50041440340794210020030050351764005241e01e88290740000300c0b007a041070500707000080b8040c00d059001030060001d02e040204601180c1d0454000d00543e103081d4111008206a140c1e20441c00c62048440a104100403425030032907502c64540a00000e1050711034000c1c40030000e1042c404540240b0504109029103587c41c1c01c9034000744024007640380c900c00c52074038680321130600040040406507000d4489184c0f0344041008c038420741210141501d050401c0100002051364100c8540490b151303418000f401c1c1c109031001422403e00c0990001108581c00c0041202e5034120050ba40c0c41200d070090540d075000d40300e1290703040144940103264010b107000004610550030300007904441d403242d0700003099444005401107071070081005440001e103400a03402000103d94000318200c400f8181003203880070030300018205a4402150921507403841e40c040000c03615000700050100e000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 464081276 1250 464080026 464080051
    0x1202040305070e0f0a09050c06160c090b011205090705010c0222150e07080f181b15030c09040213051309050c100c0807020d051501060f0509030a0f03120207060f05 72
    0x7155247c6071154120000c40e4843c40340481c0800f44445081103110465500030040f00b40c1e01e488281c1c0f50018441e0008560028000d4a1840000012489400d0041420200510f10140740900455000790320346012a04012207a84001d440400c24406a10b43c0c3f80682c4007003106500f26541290640300e9038403507400c0c10815014068031981101a85400032120011219181c2d2803440c1e00030340c0c10102120540d24844d28158254500c00d011050a6580c8225801100f80c0c040b00c000d04d0391800b00783c0c0c520220034420042d14000b45081d40c000c1405604034500303080f800380d5030400034034140c481000ae000c030151983e112008100b818000c141c43c036a8210b070b5103942c0841c41c0720000c00803400b602c801410240300003604010340d074882000c04a003960100841d040c441d400080300491035420700c2082c01044d01108000083d5001d07805880c68442c019000704082042510f8600c1c40b494683c00660902103022050300795400140000d12203d80224004103010b01c000d203000d000c448004040030801c21 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 464082526 1250 464081276 464081291
    0x8090d05120f041802040315200f18010e0117040f0b190b0103020a0e0915061902100b060306060307140409020c0c2b030e06031303020d1e1202040305070e0f0a 70
    0xc50544080c000101114800581c40300f08698180c0f0927103201c19016094030010864120b807003800c000401210110300b00180078041c80e08015100000c4181040d40441c003906a081c0742c100d158000d8590050294401c0c2c210384949440d40c9182d102c0c256002c407142a41a00c0c1c3d40b004610601910001200c00e00e8110b103003040105005107450104042603200f400004041031001e50302d07c44214442c0c20003440c40303596400072401c00f0700c82c086542107c1c001d4080d4250b8001c0080703051041c0f02c061480078116520390781c0d944082060907032006101505000b00e46000381503400c0b8041c05800070781010ba00c0103030344007140d500c0b4a1600c0c4a10f42258414804410b40392403602080000300c108000d050000030240401d8617007511244408001c80703800c810007008100d40741080d0701403003000a0291702a00d410f005803800407590403102000c00360440e6032200000009621440c180300d500c0e0f0450030300600346614ae5440506001903903111b0300035503079040e0501c22464015840f00b81c0088901e1800c22108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 464083776 1250 464082526 464082533
    0x1d070f050a0e120d0806120303070207090c050c0f0321060d290f100b07031403090705030304080a030206100311010f0c02040906050f1308090d05120f0418020403 71
    0x10301c80c40101004001040041c540c00d9111280508640d0868400340d071858074031a18028030500c8229841ca10807013051030400000310021003101d00900d031903405844011b040c012640702401d859200790301006820441c00150030b40c01d01001460000c171502540d03a441144000b01400ca5542003070a22842031241444455601c00481a02d05d81d40181c6010b2806880306103d001c40e4ad43c80d44030110b001c002c4041001501484400c244160055460044e510703440c2d40e05501c1601070410010082903d0040c403000404c2010b014561145c85a41250042a280c10209046420541c44041154000e2988004040d010b0041e00c2c0d111030302d401d90502c0945980c40e040200300d0514031281c184030b80c0341d06c1072000e207109000c42c001c015000381c410f10080d2554a0720400134842100c210500340fa48001041c031280040c9100a4800e40015134141020584d0040050030034960004031000c0c0301e404c0c510070022488101a1505004c3c0318405500c445c0303082000018507440342c40f49000c1c180b0401052001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 464085026 1250 464083776 464083787
    0x10e150112050109120c0c0b030405150603010b03010603051c020c0d080a02012012070306060e150c0607020a03030b01050301030f32070603060b03130b04030512011d070f 75
    0x45404a62140140c02800d0501d0b50041040603030282040b0011558a80160742203080c1c1114203204940c80c00d41c05945002c148018001910014403d40118210920018050001c00d4000c00c006000150084401c0c0c0080e08460b820340c41101e01d0b80229040c00e48a01b960000b0041460282c0040c0076070444210000340c403058400300c01050000081401480c0ca4803d41c41b400d4450803058065410456094a001c015000210708a5040c13400a0005a6840c4a801208100c4025071a40104500a203081284c2d80d00030000100c8030b24000d00c82c8070440f103010880c6600416940e00540012041414002c050352142c0c0c0c01c41e41840010001040003c00c2407507640c0c5102d41005101e4200c181884520b000c0c074420910000311203074408049203240e000807405030100d5419490800220307554100381c1240e4001200d090421001411f0580c01007140506600d501c10312070700e0420300d007194152064114100c02e8008110711130900144044411000069540010031410000800b02116100415 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 464086276 1250 464085026 464085029
    0x1f0f062a081b0c090c0301150f080613090503041215060503060402040c0c1202100f050603030a03050417040b09010908160311130603060b1f020304140a0b0d0c02010e1501 75
    0x200011419450300150800b0301801c0e49841c0f00526044950a02c4480039034950001c1c021143c12085080241080c140100c3c000c48503000c05481d150140e82e105402c00800c4207895a00301c01c815241c95201e0001a400e00c0100054440350340300366450281424018007000c8451a0080f01c246880030510080c1c3c1d0005129030320aa045801060a40c00d07101d007181d050f0032400c401410317641c0448d02041900e03000708181900351170a03041048075042d40e1940605481e400e580c1300741c00d5001080808602d0340b00350402940913000301c4000e840d1084a1181040e9948190701c00c100c0c4000200e83c03207250b0341c0d10180e504028503501c801001d42c0700140d0800c40d0a00300d40e2100a04841c40c4080701103194880c400c0700032103541c401c070040041d03640d2410004094420990311a04c20503d044601c00050490781c80d0100300b407000d60086060038180380e001410300020345c030600c0e80305140c11800640c0301c0035075005116201a11401250310a0507900290075542c800000910030780080c2c0c5118801c0031503003c141e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 464087526 1250 464086276 464086297
    0x306070909020918090a02031c080123060a0504091103041104051005040207110405060a030312050703201804050c0a14090324090d081f0f062a08 64
    0x40c0d8a070394220003d452244013001d401e980807500420458088404200002c034580241c003030340ea0b03000c61a80040c49407070002c0d40e0b16011503402001031011000481111071000c20144002800342503030300020b00550448410760000a000203014880010180108208442c078403201ea425402e250b5030b5016100e2188000702e002d99510000600456070908a5800500024200315562106418100c1640b415004010b000b01e0034007000c40e40e00c1c10440000011607415680d4400117480d280d0301c1c54050000505600201501c03050034076070450b94401e03178122540c0c0b10404c0c541cbd42d60740302d031340018512240003005206520b40010044110074241c2213500180444c5455101a00000f42050041c09658004c0d5018400c002d80a00700c4030104280407100d20781100304608660300c600000e55541c542c1d40000c1c00046e507035004075400c90303168146120094451404c02108a03280c6402680f081200d0f80424006084e8480700908800e00003030000c3c840034282c60910500b001a201e00c0101d05c5680d0702e0360b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 464088776 1250 464087526 464087531
    0xf0f080c15190c170106091e1a070c03022205070c0201050d0c0201020d0e0a03081b09040b030a0516140109050306040b04030c1a0403030c02161502070f0b180306070909 74
    0x8042036103c4c80840d519141c0f0b0950303001e6256124a801031002d00340d0f0088000c50400c407144000400c01c11040c0104544079100038124000d03100f4901c5800c1d8120700c1085030109910580400180d44150110350315003200e80740015900c010301c481c8415250050607400c180803180b58000090303603010382100c040441c40e41c404525040d80c1c0c10102e0080c031841c0011002e19190000f4140704940104007103030000e01035510141e1a44a4955009000711401c0700d0080ca0442040f11183c24101030300456600040101030b00c04590117a1103060034201d452901c01c01c010004d0a050214648606003c180c01c0780c20718140d48a107042c200404e40d14a030280001d051503900c000014101817251004d4240c031507100b41800e424007406039469880040a4404401203410503032100b411510020f1680d54801c0c8000d0f081007041c0c42c081074070013801030210080046001300c00300070030b10000d80b500d500d00a080c005180b9540794580243d091040c0103503007800e4071940006051014540d44014000c0a444071000d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 464090026 1250 464088776 464088791
    0x306122f1903030809031201120c03061a0319050619020f07110f0405131103010e01020a020601050f0105041a0f1b060612010501210f0f080c1519 64
    0x280380e080034a4250035640890409034501c0c40c0c01c050650072048a100b5281c3c950103445e641805a200d00501001c0200c141c00700340108420501c0a1604034004d015040164031103840340c030340c10291200340519881c08081d01203420b5840c20100220844100f100707440304203a000c01e40d05d1980f1400042c0c0708000285113840448403688003a070441d1f4101c0281c0f51825581d12851506a09089080c03a24070700c61030411010030a01d0400b03009113403141c090404440c40d411016900ca00e1440d40a5410980540d40c50700c2c1901c005d9024801841402c0090b001410071b985408100160041d6a682d9103041000c10311040088202d0919030250503080340e2040394881002c000d1406c1d0500641018a6510883c04030000d035402c4d001c030741c0c140a880709517000303040150105412070030f0b100203114290300c43d0300600b00400c0a202483c031252046100d0660180c40c110b840d00d4101d2580c4403240d040d00d400000040065801c03808020f2103014501400b1100040c1c584110b1000c0c0341c001004c006164542c0700e072030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 464091276 1250 464090026 464090093
    0x2071709100509040e0708070305060106080c0a0c1b17010612050d081807060815030a08090f0609040f050906130309030816050706030b0a0503010b0609150d0603060c030612 76
    0x42010445c03081e00321214240e6459940d956401144001c1d00d042c000d201c0041400d61044031464400e52545040c140380c01a110411580001320300400e98a000d106080302c03625161140c0c0101c001d00c403150102c0c01c1404410804c50846c0d040380d220003000c400d0140d504000850210304403d990b00d01c2e04000030f169035119500031281090341c99981603801060360101d151074010b00128000d50705007200000108080e8281940c0f00412000a04240818400130350285001000341e044400040c080d6410402400042000e40d1004503180c0b00031070315002006070403002008142e512444043c000c14280006d501e020340392100501000d08101400900074002c035064a4813245400d50004c1261142076540344014020510722066a2082c0c9203504000f03006d20b014012001240340c0108401d1405585204000c0745e003545a1400c0310615003400303041148a110f218400080d40103c40c003080c0701e101c1030b50040c12910035800c02d00300d010755011003201080d03450610005191f850b00400000070300114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 464092526 1250 464091276 464091281
    0xf05120f010e15010e070206010b0a09120f030e150d05070e1e0a08010606140309010902030604080301050114042306090a080a0b0c040b03370207170910050904 70
    0x105405038540c200703146044400310006a41c4500c074902000c03210207903203566034502000d500780c8007000141d001c0401400742c01c5980b8001d184d1508241085c440d0a0f580f10b036a840b84001c10744c0d0075a0301030030a52598007415080013115601e00001c841e0b0082c090400d40d00440180100c260341d9000b0313956000001c02c075034010510907400e0040142112420051109291003200784140b801d07004810002c800a0301135014002c2c00309440d019240c5582c402030541104105410052603842150349030800540940c60510509008900400903203a880d030504001400c031419082d800c0c500c2040c2041b0400c40d41c010304200700d1424016800314002d80c403040002503294040c1c12a400d60007003071a500000d0078140058000419403003001404000e44c0c0b18002090ba9002d50310800300e4050040001409004030230604e1004400c0306125603420800c7c90b00c40c0074242440038207400b4810ba000842d003042c004000d8411000c0c03110610070910700240d41000c82d00c040d080e103400340148000030501c0c542301d039101d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 464093776 1250 464092526 464092543
    0x62303070b120403020f1f05040c030c030308160f080c030a090209090a060e0106030f0311070918050c0301060b090f1f080f1308040303050c03160809010f0302040f0512 74
    0x2015440e454a80d480c55400c0341d0b201c2a80c089000d0302c210300d1404014400400c00c404c1e0600702c0403e16443c09000703c10000a000c00400444c0c0f04101c02401100040f001c3d0a00c10103180603035540801d0b803130a0001c0c3c0c82c21304203461524080c01403a4000500b400d512021090b0700689030310226480340c44521240002d8910f0a4000703506c07007810340400c21111400191031301443d010309400e0003030080544d9542d00f01c4e00c81d4000a00801c40d2300c0000d202003400f49002020000c5110b0448881940d50610032003207462243c0200c400201a00688042c0042000f045120030411030003001003529106e8070301070798800c5100660255000b4802d040d401d503552f00100c20410070200080c60340c1e520201d0000d080003401c64019403401c2e04400407805d4003a4035201e158880da8041c402515190440d00c2c20760f515008180f21601034031003005035044611024801d12405c0780b017001056201c0385c2c1c0b500050807080400850608161040c8420460041c40141c0c544c2117990541d00318280e0241d1116403400c0c001c0c1b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 464095026 1250 464093776 464093789
    0x303011403032109120705030a030e03070c0920031e100b0301031112031204110a05190303022a0f18010b0706060b0901020a0b07021c030218030106230307 68
    0x3a03070820000c254143c001d03244070300540b5058414903101c01d0b0342100c4c58098940098800e610034081302d99014001d600201c049140d0702c0031641084242e68070351188502581110b14050345902d101b04a94100400607001a508403000600710318090705440d40e5074980090000114900d0300100d4038a514a41d06800a1310710002d134656250303142e08001c01d50146000d0071074012008c0500d401019a00441925502d41c0301c2080c1c1489519140c803a8500481c0000c80507600c08200340d8006078550310f10200c9909034403401070031095580340d814041d04050110401c81031555595442800a6104800031034419a0031100700030700c1000c46000c40c80300d8809000d420020360262001107611181440a030656605c111001d000803501d42c140e8807003500880c0001c9000d60304c4240d990001610181d116940143c10380b04840c030611406d60500c00103034980c50303540007191340040c001141403902c000c072402d90740007038009001407031500000c05c000c40d4003c0c0c00c4680d0001c5034080854103507814095403005081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 464096276 1250 464095026 464095057
    0x9030e0906060f071b0b0a08040f21020c040506030705030a020d0c09022205030c010912050a021e0103050a0603021c060b03030f0406030f051009230f1803040503030301140303 77
    0x1e1601c030304043c800e140000038417000d02c00001402d01102c07084480050f0070356079400791600c45603170388446201400012038020300c550780e22181d080f01d903100503a1841c082e0781c01840c6142d207050034081101d001070b00311406600408400d102c0741e00c2c00211f44803a20390595608004051500700071030782e041c007601715401e100e000180114840755042500108029001e0222a0150790303201050b07980d1120f070105038040341810340d080240c401c0200d40c0381c034860b0040703081c1e80d09104540c1c001101021154103400001c001c9a90001c0156894442c2540c010703c1d683d0304000c0a8115000140141f0544103030004e802c94a40740350040003295000b1406808001c1c003101d4039450000499141074200d4000e60000a20307000002e0310300a1140a801d0182e0355141d60010464100790252020f8a1003114040905070a01c1807140c01890000b8524410901c850f000703005410a03548200200688980b142c01c00d510910080c042954080704490445a028041058590000e00401e085014460441c1b10000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 464097526 1250 464096276 464096287
    0x101a07021305040b180303010e07050702042414060304210903051b090702010b10030209040b191505071205460306080709090203071a040504060909030e0906060f 71
    0x82e00101380e6018800780180102c1c0c2c210300c006040e07500d010901c18264003000c910040b6100307901480c018807034140060030101c0c16070f6100e40100d2004041d544010705000710f8810401c02504c0441ca140c2824004460880c42d60409445080b1100902c1c0420394201e4650540194424040e42c01040155844001c1d54120910300550304003810b5072010241c01045ca003000241c18a2040c0309031280b000c801070103030440200d4610110025002000060380041e0341c0da92001c5507a440c20b80146503109901c800b0050f0f9030400d5000b2078025841411101401800c0c4801400201b01240940d0414064a02242ca440d034002c903525101b547d4000c07020403403031050303e1092b00f001031680c82c1c01958400300c2c00060b4440343c950203c0480d20540302d40212900311200c00c1c040f0b02d031750350071000c05180002c0407110008e4a034024000074401ea50b030009400751b00000c0400880c14540240d070010901c3c0c00c02009514400e48029010344c00b440c0c4c1d1184075040318400500c944c0e480b14290b070440c400e512240b40e20b40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 464098776 1250 464097526 464097533
    0x80105100521041106030f16051b061501080c0403060902030304090603060c0306210b0c13081501080105040f0204151809050f0303040203031b070503100c08101a0702130504 76
    0x2d00c01583d06a801c028580403a141c0da04000c01224000c0c08488042040740c3c0c2c80d1007543c100d082c030b048200810480104044400950305440790810303e070191001d0101070415044100316104084c0503503060050110400400c0c6803000142c60450390480e10100b041a140d100080c01c508c103a0300000c2e0710350314201000c024405030313038003081d2840020340301003142c10b881e038400408482451844000e0080102c1200c80001c400c01a819040100180e80c80e05180500d034081900240b250031040c000e40c0310b840b503c0102906036440e64010807141000700541d0500c0c0d1a42d11031030625100213030250381c9a0044508007018440d1980060240001d080c1d0a42003401c010805440203000a84592150704001c902c8030002004072401594020300841c40c080300200d102a8400100144044900440c4800210394030b00340101406401700340c0c0300254410003008081c1801e0005003100c0c1600c94840d4042c0605c0d000c5608109145900c00d80c450b840c0c030024800102403114100007052124248030074003080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 464100026 1250 464098776 464098837
    0x63804060806090f0108060105040c030608012a110d0e0d02030a03080a06050a181d06090109150c0906080a1d071502030705030a0e01090e0906100602030a0801051005 73
    0x4500031100d0b583d054035500e81008254500f80215481500304d9401042a4901039111403a1101142000300341a540e91591a08480c5412034603040d840d9024403510154800740750b150060403031801d2034007107900401032981c4c1d203940c060441c5051001100701c1c2c41a40e43d5201403005d8950f030007801c80360b0340c440380e1400231b000104c1514108509400c2c500c0210741450b01a444205590300722005145108032404204d0181c18054501034010611050f41c1d41d455000b8444180b05110701e0b000403d0040d05460701c18550180f01214140b40752600c2c82c91303085d017680007200c40700715041403030300d51040e8444003c000010194400c040004c500200a2641c82c0c660215880d01140d000140001400030107000a0307842e8400d01c04c0003800c0360420000d591701c45000c0c00321340d2002c510614080510f69140d01c1160440c1809503041141d40e4040002c0149600c245010300f00074044500c065070910312070030806820070380180205485110341c5d02000008901c2030080c0c0303000341c095078a0042ca43c20b100901c40c0c0c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 464101276 1250 464100026 464100031
    0x1501081507031d011d0c220b0904030824090a0c0509040f09060b01020607050d0903020705090405060a150b041404091703090607090b04150c0b070e090603010638040608 74
    0x444280c0113017120303840300c03020607030740030800004d4544100c070551301600342031502401d00c9503580035503100ba034000306840d039211652295100340ca41541c00e003801c00c0012800c8400e024800c2c200405490403d03850340b1801481c0703811070a032140119020b100940242da40d40104c241054025241220700700341d100503a003140f504240541001c0011b810000300498440034120341401c0491b0040001c182d126215074010034146d4002d105841956480e107000907a4a402075801743c82c02c0d031142051100c1d00c0b2003449200d046000241c1781c01000c6143c444e00c14100e00480c800c81a4403440058404050344490b04100206076010711140f02050b82404980d03a40c0d0415100c00c1440e11a00000542c29401610f289080d1001c4000315030425251908071001001da1031009401c1082113a142c20019600000441c0120342c5500c5080e000501001401209031000f08000e05c0790b818180c04025070801860840030b401642d880500d10800390400c04100c1c185040317143d00c2d21100c0050000380950f0710160729070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 464102526 1250 464101276 464101301
    0xa05190b0c03090303042303030c220e160e0d2103020f04030f0602120108100e0105060d030309031115160e0102060604180b10081501081507031d01 65
    0x200c0a4030307a02000ca03a14003044482449560040010a000c51020002c684001281c09030086061743c41c209140c1c1190010344e961040c0d503002146214590f056481c2c8500360750702d0908031070399851410811415140019010380d80300c403c6070050307e031003520070f10007429200c502074200104c040151a001c902d00030507041ca02d407a070003103160141544e40304e07008581c10b5a5401c2116818a8110341b900b0042e480315500844002d0b03804c025030500c82010441c00c0d030003440300b0f502410b4210000080707942682d200449480b1a64580b9003000345517510342c90740001058061400003480d0205160a4400092604000c0c6240c0300701100446405d41003003820348a030400710489000b800703200400b900d078070900303456281c0581c000c1e00018115040545c0040c03400c450b98494041c44088940360110760507006e5541500743c924150302441049001c008032880c60703030a401401c00e81d40c50403102d191191000ca480108240c03070340c2d020880d210301c250401c01e100b898080c03120510007910f580150003044032400d031a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 464103776 1250 464102526 464102543
    0x70c034e0804151109030a060605090109060b0409020c2104080114040f03270311030d1110050411041410080d0215130f051b04180b090a0519 62
    0x50851a00c03031101180290f500c102e181c101c445154100202070458584c00700f42c00f900030b0181140540d4100075074540903025940c00035205042c0000e00048501c16048503c01d2410214100502c0a0802c04c440440300c00c03030302c01a144e14071000d00c5401c00190404000c5030000521004003e010b40200400c04c48001000800002c40c22050a0303851010803a4043c1001c0e04a04030303140840d0080d07000d911480d100d0400c0203812100e04001c1d800c1e20340e042e001a140304910700703c0c80c12345080170800780f581c150702d50602070f03010416407040c1c0b5550880400d001c2c04294032200807031304102039541803450301c900080c003e001e440b03240147c00c41240c00c00c0342d00d80c0c52010700c0c2c2000203400c803011411403403031034259002d4412511440c604010001c0d0207402c60500c01040703000c1102103241c01310300100551185c0e000d00300c0082c13603903c0602c03030078400034210b172117545040b5914030075402c513940c0011042c1e8003420030803156644100c40303400c240407a9009403041c003810103515208034541c401c4003003503032045444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 464105026 1250 464103776 464103923
    0xf150c0106060809210a0309050c19030b1003050a0212010908030c07024b0301020a1e03020c0d080718030804150503091513080c030d0b010203070c03 66
    0x2c2c00048400034890b507414035010040c6c169424030940000141e540120111103006100601050401e248048003541c80765a001c014420400a02000340d00001120003a0300d16a00b0740d02d81d55100d0706c486030002d100f51412009039010380350030340101740b090b0307005003c00341c980c60400b001203815072101c2d1040780700c2c401403030007109036054100e08201c000301d0211504403428012550342c100b02d481c8156801c000c1c0800c805c50f030301c142e801f40001c1c40758868640d0795415140345101d50a2201e0004448070041c9801071082c031022000010307110440d040d5614003405691108030055590543d000e5410b215000c071814048280700004004000310382c5080310801140b4850701045500303000c1a905007209811100f001c0c2d00310500f482a0306c1e00f02015040042d0b41d600c859540c8089507103c16000c568076080840c41b0b0a18007154400c00b044200280003039440c2c184c0030303941c04c00e003400e150200610b00045203107001501b440400d046800000e44d400042c098521f00d80341418122008900f94465803440000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 464106276 1250 464105026 464105053
    0x70c050907080604180828020303090607030c0c0213091502090315041a090a0317041e0501150803040314010c14160f030c0b0a0203060f150c0106060809 67
    0x110244546140d42e40c6107a6a101d54040001822000b003030f0981100601d9503190200d00b015000b4001c41e000094441e024102288418141c900d00e03941440941d08103200b080200000803c2c6a941701d206440c00182007a408031090311072000d85103000c3e4008000d0350310030003180500c1d0320024200f405171100141c2d105416600f40140c2c498006030540682214041c840007056011800781c00ca8440c131400035000c0c05420b0308113140041104c279507459a0040001806042c2c02803035040805403200b41402282c036064454114000010300300c004e01d02e0920f101c81c0240070080d40a41c00c5250600001c1c005590380740940c96580c0c100b4041a29601120240e02d5a100d105210382c18036800c0c0e40d10307a0401800d032100c08405030380003010700b90800040c880c06031000805102694000500c42e480f507016000d6036081080f051100100300703050f811b01c100f080c08a03c4d5a40100545013800c1100d10070314082250b000700e02240904040300c1003542c20b14100ac135016810880aa205032000821036960f90014071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 464107526 1250 464106276 464106289
    0x2031c1805120d030f230f13020109060804030c0204020f0d050a060e0105100e090c0d0e01060602060c07060615022b0527030703080c070501020f25080111070c05 71
    0x1031003500c1d070101d03036040c003020301a8002c100f024544040020303550309503681c10704001d440e1101c40c016a2201c001001f030100943c0c8903080d0401c1c03000b2180b40f642225540040c0100c0301e580180414000103400050805104004034042180d0262055407280d45000c004c002c01c1e000095024103042c1050700050068046100380011541c0c110b0a04900764a0131040c0114114011007403001c00c810341070a0042ca440c0c41010718000c91503208040d40e118000100b004c100d03070700800714000e147d0420004200e010b900040660300141c0600409a542c982850801c00800305680168000400d1031546851107402003812003c40a00680d0249548880060514201c0c940b1100c1404500140030080c41d4920590200c1c07028001d4160650015110f80002450000d00c2e80c070444840ea000605400161424819a0000d02c0c0a000500c0000c010040441d1120303841b04100326220081c0724401407802d14403c885005080d03480c02000248405844d01070542d00419040da007000d2468400111400c100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 464108776 1250 464107526 464107549
    0x100801091805031b0304090213090b0603090c0922060e07060f09090902040f1a040b150702040b01031b080901110c0d0c0203030408070905090f072102031c1805 70
    0x14040c61421a509040e444c100300c0c1d413148035015110512022990142c544010658006414241000700b850100071380181c1d0740c1012420301030349040c41409840003000440d08a4441c04682c1d100082d500d040d20b45a40611051401c102e0115407423841d030a2225552006502485a1341a2040f03543c880d181078545100c3d544036000003910081080110f02c0c42c644c0a030120600c001c00216203401400b40410030b544180944464004e485000c1003018a828418031890f09403c0c0c44900b06002441c201c203ca074010034001034010381c1c9400d150989a88641d200c41c003030041c80082003090340600140202103180490382c192944d0702e0150f404d141c600040f4180d60307484c0c80c3c5000500741c690082c20122140b843d881412a05031206004c0420301c0001400403002400140b80e00044510707148407454030303000304201720000c1c0f46c008400a202000d00280350740e5030200707441d030502411121032010918102c5100c01080408a00c05502c010300b6901145240c2020301c1c4281040c01c3e00e44075810003250141c807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 464110026 1250 464108776 464108783
    0x90c0309051c05070803071805010207120305090402070803010b120702010b0904290702100b0409030c02190503010216020f010926010b0a0602010c080f07210207021008010918 77
    0x41c10402c1d024020342118148141e945250150509100e82d40f028803603003003515504081403004000a10112003030000200428007440107102c1c03940703080d411846001e00d400020703041002c00035003449161901d0701200c61a0381e0000413103650b507940340d5084506403c0300c1080e02c46040b2074804140f105105014000c01014000c0c034105e62511191345a84c0740102440000b5440c0581541d1240402500f00609116503481d801421f00c0c05100d56181c4100c42442200500c5039141c10420004a80d014450008659043c0c84084000e00c51814909100240d98441607241d80001042c2080010003500035055610940e81d81503041c21110064803540100c0c0a000d0202072400d40020f0f01350001c460030a0424a80700002544008c03103404a038003a8610703005000036130344030844421319690003252554040440d048071141807d1101c0000c10020000702025200c4801a080d02c413502401e41c112800305600400309460100c034014040c003105e10910402206500e01030001240022860083d08060307031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 464111276 1250 464110026 464110033
    0x50105030d0302122e060306080d0c120f0207030807061505121b010c051b09100609030201121803080f07020c09040b180304080a060f0605010203090409150f06090c030905 75
    0x105e4041080740110b44c5940020b440c903030711100c0702a204003030780c0000140003c2c0e0382c0841c1160611003c0c5140281603016001040b09080320303031000c035003001060b405021162500b0b000514260008a191201e43c1d040a0700201d0001100c01c1040081d92021507104101c1004091036a45c420812040d00e5040030b0031350064200e08244900c190034000140c0c02d68005040400c109086070310fa80e40380054a0156074010a40c0c0240c03190545403111800d58000300380d9180e04080741c140380f402841740b80d031880000c3c140110b0100241d0054000d03040810001194a5041652041810020f042c0a01540c02e0f4032005e2a007404500d00b18404241c60304c40d40c0007d0000ba4003034807250b90343c0d10f600100030015188000d030f40c0a5031040351010f100620003890700c1001000c044c801818000112024200411501c41c50318404101c141d8000c0207503031180d1000c90300000c1c0380c0d840d8200300c2c00381240c040c41c503581b0b20701d0304a440300094041d60000341036450080b4100119034010030b095048524041001d4050307070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 464112526 1250 464111276 464111281
    0x307030c020a1805010305060604020703090b3601170603070b0304020301060b0a051206100f030f0b090c0c15041a07090b13170607230408070306050105030d030212 72
    0x28010801552400d2018080414150f90707042d8007601c20044031015a840c9494900410501000301302c1181c0004c000c4900314540341f01680c0280c01c44034603100f0707031000b000007007101e610380140492032068000b0584410400c40003c4400d1181131410b400002c4c1c0822a0203076007d0994201500080c4034080c003400600345542412041600d41c0c00050049a041d904c60601060100e54007010b00380895107501e41d00d0703c542801c0c0e000300c5094801030013203015550407080340c460326034000313050b800c10b440500b00041c1c000300201e200c00240a00f505c081d6084410b403401c0c0004000000e005110140f0b0741810344041c07644042892a481401f82c50142030707c1c5101c1044100681c12040d0b01ba0420b156050030298140c0d188000030840d00320021001600021400412160b41c1c60300221110780281c2020740329134038010300050400020803441003422070381c00c01c84000c075000c500c0444e8041c04203881203440e110382e0b924001e405001c09024090003401010842ca4200f0b01178001d8911482800541100c2c0d035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 464113776 1250 464112526 464112533
    0x312090f240509071a1c02270303031602030702041e0c05120c09010c0c030804030b090c130e0f06090607110d02030a0e041805060417070213150305031b10020c0307 72
    0x40a590080005180104505000641c1b1000c0e00d440c4003505d4100580c0740d041440441d08103c014240c1c2d0320748003600d80c035007251641d404400c480e4040781ba0f00e0074850b00b65161800b245507000c3ca410080d0000d03c1d00d584110031015030a015170710307110b500d07005014041850f04122082d0107000002e021549007400400c915400d41e402800c081c2c28113143c41e0070070507519241c48030b10702c2d2035a20079100200c0008091041c001e040280ca0f030f0055211008105000c10b0201003810308600b1130980c0d6131650f68400c18110300d5014407412a00c03406180c12142c07a410103000311501d46106071449008034042a0001003040c0010581d038840708a0740e0003031030071b00c0031400e41540e14060740c4a200741d0003507558981e0b0b01c070388020058102d0a5806540140341ca403030300e403070890b01c86900164100b980b4001480801e0040ea1001c0c100303050034480c4400450304120040303a15104150580000b02070740030119910000410181020f410004414121030a60301c042081d94101d105441d031031010b54008004c9074011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 464115026 1250 464113776 464113799
    0x1106060f011106011712070b1807090e0c031b0904121809020a08240f04020405100c170405092206060b04060914030304030312090f24050907 62
    0x5050041c1000220b0342501c0807281d082002c01d800a446a1502c2001c50031291420003205505c00424144c0c1441c041403511650325080c1c1c020144150346041a800d00c070300ca28280151801800210003d00c440890002c041b511340c3c501480701e50188c884d4a020062030b1030314000503510b00c1806482c0410070f44039a19805078a070400a040ca0900c0710b903c6510304041c8102a840c00103040d446001604c1d14090f600044c00d004002d4441103c4448c5c19040b101c80b803404144404030210f089030328844090b612000f06020f80107680c03240354080403641d0203408041d085030310316040340d110b5084a240d4030503510140506019501030341c0c0d0411103210004100714030301c1019480905420115001d0f0800558644050360300f980c1107903162410100e0204141034000300000040e00441e1400c0a2100c2a1000302c0d075a4010307440040c3c04c010b40304000c410300f010590f03c890106a0800291441e418407414814881c003544200900d21040b010342c082071400b0030740f243d54004c140b141c024025803460a45c18111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 464116276 1250 464115026 464115049
    0x6070209090304030c0605070203010f050105090a2d060509160c06090f23010606080402030307170d0e010518030a021e10020c0f2a010807090503011406040c110606 72
    0x1c451100300004004104030424400081945a4506980310301900c14103080d0303580c140081000e241840010b03c5291340d01c0c120a80e11171142c000000c0c403910385490035503404a07220704124810503924900e40d0683e000750410400d8a40c156044490f98441c002846a501048164100040c40c8090040c001461681000307071541d000700c10102610304142c45e602d01c608c1001d00c112900c03940307801e24000313842e80c2030040c00000c2101d030801c0d070b42c00e02c0c080e000329071030303103d4044018111031007001c42800380481740b020b440c140d0201c0303002004007a000c0c10903180240002e03980c45141e0408225220740350322000044130425802075014003041010010300d034510b9076001c1840c00140c02180400c0010103820310161845c481280e0082c0302ea202e46000d840d0900c8005000c00040c0d8492092a00050ac520161111641c2c0286400c0d003071541c42c00404ca805a40e1900026495424aa6841c64903002c80d41590b00a5800b25030801680d22481c005417030500c008215105540c001000144c0b8615101c1c4a105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 464117526 1250 464116276 464116291
    0x60f06021207110a2705060d030207050607080f030c0702040f0507051911010e0a021023030a020d18030315080a060e0c1206040c08070b0405040b131104031b030206070209 75
    0x1064650f4055104042c0c04043e42003104910f0350895085007081c0540740d08411f0569016050141c1c6403402500d50800d401503074024100002c07000c040003803038022509105103a04800c0c0c0c41e030170f00001000307e03079000460680c840c0741401e01e413070600c0c202c81c4141d80c0901420b449a5282150710807040601c0001049107100344020f030200300c041c0341d00a00a00c80400100c501604100c400b91041110440400360b180041107154052900800c0e6a281c0f808604920040c0c0a5240d80c0c03003041c100060310890400c1c4401908062207050f40028450072031400d54442c0e01c01748140c050b40e02ca080d81800b090711400080b03502440081c1c01258040e88100c24031501603068485040d042000721b6001d20445055030580d44c4180e0801060287d45010080946115000703400514a41804458180982e0081c0d0b80306507a02e06010030f040ea14110f04c8120b11406802c107203caa02844840b4110b504640300a5805101c3c0940701140310340c01560200960b036008002c81d040c50700c075800340803038500020301e040b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 464118776 1250 464117526 464117539
    0x807061e02010605310515010c0c081009050c100212070204090f11010206150904020f120d05090118030f0303050c0f121603050442060f0602120711 65
    0x2c035040c0c03143d40b0000400342d1703001945400c03021030400750b05200340074044013145146040d080c4550701404400381d00c0500c5092822580004040c00c00038502c00b40b5030f00801051141400d14195401d80e5008501070a0003001907601150b099070a224a00000b07600460060b0003012040e000c1c112120003410100340058800695039045950341c80d00c4502c000800d4404142c1040500520342e4100000c0d5440400423460988003a0284042481d02c103020300000e10800b007030a840c204c039851310400c0c582d90045c04001c0303504640440d40003078043d5000c92441c40c0060503502054094005403182c10046960020301d1000d10400354404800508001d070501d410b484040001602e2113042c00040c207042816510b0711403080c1020b00c50b01c941165078603865000d05041008000c0416410311a80b00e16031420b04034120b6200c00c00581d1801d2140d105c02514400c02109c1303800c1c0800ca61540710000b640c04600f203114203651141c40136681c0788221100c00c80c01507001c100940010321045040d1002e100050202d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 464120026 1250 464118776 464118779
    0xf0c080a0e010209130608010606090f1203030b1c050f0706080a0b27010f1a09100203090607030305010f12081c0b0a03050c040516020a0f0821100807061e020106 71
    0x45d007020300f410006a00c3c1900c0d0039043c841401c0070311500c4028103103800c1c40c8115602d80345004000c0700581c400c201c0216001c1c2e0012003414004d4000c5d100500d8001d1002c041400c420308102c0140318801400d84040c0310f0341c0980e18240301c00049010039145103456074100d580d500800038000e03015900321306030800906803080340b4138420019802c00c080030b1103852104560401003130310b44c80d1700e056009071086101070242240010510b011904060411b0380c03450490f0101c00e405a195202d825102c5801040c0082d80d90245941548254180d400d032110060b60241d50740d203d02c050b101d1115028141d404108102d4608808040030010500c4ad102e6010445048100c000754840d0380c158015140d030780205040e821545418806c80d41e10031141e000f140945200c002000303542c0d00590794001c1070b4880e0702c103400d803d1103c00000e440c00c141080420200d10142c100c46420303241802e460441110350380440c0031984c004042881c130145c4103a40d40e00b400e006041204102e10b408840d25041c01e5540e1900d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 464121276 1250 464120026 464120029
    0x50a14060c0106030f0506010905070e060a0809011103090f0c04152303060c19141608070f030e1503280e1203150d0c0303140c0102040e0a0f0c080a0e010209 69
    0x81c0c5c02a460300541c042d140c59894164030400f0754400421107400c0002108202c0e40c0c954644c015112803801518158610359074200c1f55500504000d003440600300408801c10184480014221018446a201703807a04d19070a1802e2005990a0101c2d105d3f10b281040003e12008031080c3c41c40c10b0800500082880c006400008a402c200065035200c0c144180020b0020707a0003250080c2d00e560460b90f2410003001206107046800d280541c0580c1e03030044a12400c04024007160405a4402076040424010381c1426440e019001d000c000d4210380c040c650203111140398502c10403d481c858068011044800d0b6090038040134403022882c3e0440c12241d50364098243c8036030821400107814150f810403580e07814403030540d00d0f10800505015105040c1042d1003000141c4490b01c0008807907040c100004480c50310842c0d9105070040320ba80c0c8016610205000460140303c0c08141d02070740c0620020801010150459000d40f001d0030420070118502c0d0010429072400740c0c0c411550302e4620400141400c04820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 464122526 1250 464121276 464121293
    0x1051204030306030c080d0f03020903030d060807090605120a02040506060d0c0c1401060b041a16051612050a02090a0f1104030b0106080613020a020109020a1d01050a14060c010603 79
    0x1202500000d50b03034001070040003c5075010310b01a26010000b400301d109001f070005c3c52030050007800d2042540114042c1d0854408100313036000c041c480007040c0309554603818400e540d56a148107000106d0301306880013a0030b003000880101440101c1d0003518018a041c2c091001501c800f030101c0b60880c10422920b00101c0082c820700c101080d1a50360101806000e082c0f138660081545501c0071b01d40d1500c2070410807001c0d218100d604844504407095040c074000e03449000540601c100410659a0010000040040200301a200720300f1180c16541d205449281a00c41104004030060444c0d01200100c4054a0900e40c65030380050200303008695512001580c005845068007109265040890281704214545082d039024024600d010081494000c001402080d01d80d003403d0581503002440009280c03007900000803d540203807210195903944c241440003903a1031100c0c42c041002501c0081460328052450b48203e81a6401000c4000d0741d040401c003440d0b000702c1c0c10680d9990b80d9000080041d5085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 464123776 1250 464122526 464122531
    0x705030f03010e100510021b03100510080f030909130606080d0207030308060603090712031710170105040201021209040e070b09030601060309120815040f0f0e070e0c0306010512 78
    0x650040c15a401d04c07803094104580c2c590001307441b850707040781c181c0c408550010f0790f040c500b81ea000344a0a100c0040001c80c1c10041d50b04d00b4050380c142820104180c101500702d40c84111000d2400b11004c0c2d4078050440c54980c007804c01d50a034000d0039000858800019104a03852680c055500019120307a603402c0145091100e10241c4090f03009124200203140c2c010301c9859015905903081480c518200f078810786c546416001d071545542c9000315000525108966040c2860b21a201e00030701d9081044c04140e280415214862074401041c600344036100040c00ba1900907030703040c1c0090445980001c40c44070185c100351191a009a598500700d80700c084104110740041c01850032441c1d03501c800310203150408405030440814141030602000c001011104940d00d11900b91a0911150719040d07900005881b007038090030380c003505019804681301c40b82d40c81202d400750f84110030071110081c0c1c420641c440c1400d118030000004480c1c0000c020310000c40083d035026505241051409024070031002c0c3c4108103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 464125026 1250 464123776 464123789
    0x221070e0a0f0c21180303020c0a0b040507240806060a0e0402030c03060a0803030705040e101710060603060806011a12040c050415030807110a2d090513080705030f0301 74
    0x20f160ba200c124030034000a1003d101400410301845e02c1e8560207040c0b5190b1a1401010103500051a8042680502c12405078941c0080d401e0605c1c2050705003d5550707840e5000e6100e604481d5000341c040742504003140105080f050310717400d125079654020002d207504092108020300200b0104851541e96a100652069141c0611a51207042c642c003030080382240c03904200d6450b807041080c0280c554000041c1e40454000c488405003541e622144150b24002503804400c2c01d89041c0c0c00c440f2081c9010840440d0169004410444c1c690341308411402d4807070501c5044001d8211070018002c0c4888240809202d000102003145450824840da0642000c200c40a0301c405500e5a805c0c001841c01d40105000305407042d241c0d12407107040d034588a64500c2035460060400140d444004c0302c94403500b103104028411030300924006842101c20034503450540400159540f192003011030480c1d582c0c40344500625503062043ea1144c015514426160300561044e1210700c0706009100420035a00b00540c00b0300308 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 464126276 1250 464125026 464125037
    0x406020f0712150b150301030320010b0f121c0903060608031e13080601060c02031005070203030711100501090606230319020f03070306030221070e0a0f0c 68
    0x24003185050810503040031807007151040000d0041034036040040098031202c00002444022800082c1207001c401e4086409108041700001c145500b1a06d00241141e0a940b4080062806541c0c242200da1100f9050b07071100120301a4901410440c0354a03400941c0101110020b210400b111110340c00c1c1c42e103541000031080c11f030500c00c12080b8000c0d1001004150015410302c012404645202e145954240da084200402e41c9542d40d6260146040201a42019900c5658641c080103110070311302c140c243d009100760040220f41c0315070b51080600c1790003243d01450440d00c0741c0500300c40718100289181158890b9106d114040c0080e031280c2e81c000c0856103000107000785070001c041c00003801910b0b11014045900603402a0059460403240e2064903000d600f40d105e120702481000a00502c91919040718010040100341609503201c00242ca0003220803c8040480d51260040000320031605019500205010040d0300c030f21340004c5810104000300800c181c0d6071135503c0800c4915102c1c2c0c0030006071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 464127526 1250 464126276 464126293
    0x120d0e211e03040b09060a021c0f090e0405030405040c090801111e03100b0c070e0a0e010501050a1503020d0b030f01090c0b090d020f040b15040e1302010c26040602 72
    0x90003612020352490078180598141803401c0100c81c02c070300039050703528060000000d0030481c0c07038405d000600c10403a40002880d1407010742c04005244c801030594070804600640320105020020041451040d94868006e501e007600f42001d01c0042d24002c540d96041c03000e07100000c84e15a2080c02030020030300410240716100c402c042507e0300600010013196074004c4040003442217030441c00c005001502c0400c16656510858009010700d0700c940e42d4000d000f0801c4500601943c203402c2e0700807028a1a1410081c00f0503602c4500300403844106224405282d0320321000b803020b19001c0e401030010000341410004180300d00310040780c1840041d16084006942d42c0210000700f01c9015403040142000901c41402d1031240390200e60310350302210019219610384501d04520b50754540046a0285014060079180054680320082c6904640150350981141d54000703203540e080700070350307202240d016500c42072044071139111488048041c103100c000d21964040c9549068140100074070052115500810580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 464128776 1250 464127526 464127553
    0x109050606010e0306162001020304120905010c110301060509190515013e150606070201090e100302120d090b0316080901060503070b0901020606120d0e21 68
    0xd0001001d56040c001d803064a00304a4070006405988003409600e80300703440501c1d2006075071550218484100904000d489090058010f40140d030203103100d40b1942040ea2180d85040d10045010b004860020700c071410441c01040c1803200b03007400f6120103000010003030349450200303124540446100700003001c4030301106031600305440381e643e00c070310080b058401c00c142142c002000518404018a040d60010318001c02c1000d014605012406100010020309900703100440e44400b00072043d01030b464a0700000550780c1c00c04404481da000ea050f07656000b10b6040105004042502400a02c1c42c20944280400180c96900c00d41c0411003c0320010a83c0b040ca071040200b10341803a4004c005820b1080c0305004100800481c3c3d02142036683c02c04400d29500c41207114014041a1301c003a80c54030800c10b0000d13448000100030602000300782e09541c981d550345c20501030001e0400314041c585504c40300c0b5400303020748106018091103100411a0384039484040070840462004502a54a42c000140c8000311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 464130026 1250 464128776 464128783
    0x211e380604050603070504090c050a0602070e0c0301050d14030c060a0f150b0a0e010c0f03090306110a0f1d09100e0f130b0c07061b0806040612110d050303010305010905 74
    0xc00e044030240400c2c90450086902d481c030b030703101d1203000fa034030313016100c003000301039504c0001528018007014a42592250002d42d2106140304d0030740d0060792100855084c00e070b80800c5071b050b2507001d00090f02c40c40060f030b41c00b07070b031580c0010604103240400e03c11000e0300302040c40f907503000760028140402c4200c0c040000a04803030003a0480761140d4802c0101f04000380c0040c0903964440802d05000140c0ea1070f5000591341c4980c59400200003454031103404c02010303041070001e81030340c0c0612410007084411500c02c1c8001e06c41c0d01c1e0b071480071405100d144001c45202e030030403008030200d494440003058078100100d00c484806a4050b01ca0700451035003805852030401265501030365190704400700b81814107414445040c081d00142c50b0018101c002100340c00c2c0351040b07600d00c691106081141707c0c1001c400d44808a42e01d00104002014200030070003030b1402d40130307002c1030311800020000c11070010b5070703a000d07200200514540c2202201801c01c0101d03100340040c6000f91302030000400e50200619120b0b00307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 464131276 1250 464130026 464130031
    0x2a02030709140a050a0605150a0f09080c04090507080f030d0b0105131e050d030c030206060108010b0f280c15051303050c01140a06211e38 61
    0x31a881c1102004550010b85601a08022200f0000856448003140e4030080d00b40d0360005500405c8008108070361203200700c020103020b0174994401007c5202e5607021031701752403984a140041d6204058080861401c2d07800882e03001e1041d8203d4200503513402000b820b2003120306005250741c00c0410641d520142e540141c80124030246401403038807140440c0d103034600380c590140c1031890045401c04803101d01b0030800b001c0902401070000700d04850707501d4018504501203604400601a6602181e440c0d4011860340d8107a94000c0500d5040c400b030340d80a04040d8000c055003000b040c081c0078031440d407074030385c090321561a80c0c0a95507002a04001e0030004d9000036410382c00d89038145050700f08900c9803440040e0a8426a00d403070101d655454940ca45409050320300c10b914403054812052207080c0807990b0008048454450103420820601c13614a0010340030000e000d80a1680c242061140e40607608140c1c0c1c1c0c6900c12019000d01000381d1548a1228010b0700c02d0317150700314000311a04440d552901078541d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 464132526 1250 464131276 464131289
    0x7050909100e2b140706020429030a090507031a2401120c02011d06061203031e0403120204030b060111030a092c041514011a0a2a020307 60
    0xf1444014108000c050108400d801c10340c48030074543c01600c2403081c44080305001000b91203135143e01c09400c02c48000e51141c8514618000d00f8441602440f448041c82d0360346030b221300142c40c20743d60f9940101000c0c203030404044405019000002c030008080100c050304081100c241d030301151500c00c6160042c100240c4040c0440c208080384140b090b80c4c85600f00c01000b80d042c90100710342030b03401c4050b405043d1171a40d401c441d10b03038420b0000e2081c40000b03049105001c111401a8140a000c45c11034030392200b0384041100b407a240b10803414641265401c035030001d10903d002700d1031942c818494000c0ba00550811a81d03d4085010301001c0c1da40400e0515600302007030059458820504409880140c1d1441036010000c07003440d8030895038072140090b81b130110a0502030360961030a0700c2d18122000b03d010321030200c286804240d0084000c400880c6050f650030042c0001c40b00004079801d101904140c4090040000c010510b0140700461214020504a075038441c040e40c5805104040c1001c20326080403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 464133776 1250 464132526 464132533
    0x1107060e0c0111060703110c100b0102071401140304020102070e090601080d1e120e0a060b03061b040614190f0e04020f0a050c0a0f030c060e0309010503150307050909100e 75
    0x254900f150100303e49400c42582d040010365038030a11004c03030203800341c941004c020340503030321001442159032b4200301d1209030240e0a5662254882150004c61001c40c501203000640c1071b00540f0000d00d491004503009801401103680003650307032101010929048803084421f410010040140110810154501041e9410000321080070b400504814480350034000d410410300f140444000c15143e0310113a2000030010940710380001c607080040c0507190080f10540240b01c0c00d00001c4904041c0f0754500280d04081000c00d01c0e180c548030040300d6a0300000346405900e00100f042401c0304000000b441015000c40d00d4503221610072038400b40c14022f1035009540101c0c01042007000e005056030881d00e898102c0d0424545030602002c10914118091030300420b171142218024090681042d50821043d01c2000140000300b045100c1e01d407240907603c4460701086041c404034221a0307980304c1c8042c40090141c00c98401139039890006040043c2a520000c560300000000e040c041e081d4020308104c0344000303008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 464135026 1250 464133776 464133797
    0x81f1e0b1b0d030c140a0c05120a020708012a050d050a091401090213110403080a030e12160b281d0102070c060c1a010b04171f0f1107060e0c01 63
    0x2e040c01c2040d4615805c0200c000403911255402000b0790005039030400c00303e511407001188442c01c0c513031081c01d800c0c01501c141400011140414040c481d624403605040e21b603803120003400d0310400101422031310f00b80403060281c01c48100322031096a21418140a010a01c1001414500c0c181c0035030303c1c00000103034141560003015071a40c00303800f41c10f91100000041d805041e0300c400b08060080350002031042c0e40004010840d00c3e4117400040c030402c5000140c9041c1c10500c140d45100c1d02c02c028070119240de0002030f00d00852140707440d080e48440300d8000d000d440001c000448a02c100800c03440f060460b030390640c40703010420040050141b1036001c07000b140340c0982c54032200c0c003d0007180300c2d4004020100c42400c0410040f100148003480e141590310300c0d80e584440310314003190014010032603045030800600401a40002d140c020003050b40902400303d046008031003003c0d0003151400f009085d1030354142c1c0300020816006021207801640005105817001200c28106000c02e07021904201100e80ea = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 464136276 1250 464135026 464135051
    0x10150f080c0922020d020c0f0622061d0a0302070f0504061d1e010914070f05160c0503030f0306210714190e0403081f1e0b1b0d03 57
    0xa41d642c0419442c0701c81142c1062803c59001030310400603401401400490401e2102c1d45c009100c041e644000e0040c0c55166850444140c6402e01d400110051042c0070310000001c104140e00a00340291180789e0201d000304042c04240c0742202c000c00440045e031003248100442540040c10001624048030240509840e1640034542106905c402150104805020407402d00ca551641014003440b28514200c13076035540c64540c01840c3c0f050401e500030f21320130000b41400d0302ca411080c207400e041b520303900c0c1450640c520503800180d01840460340d0382484540441d881d50100081c10001c481072241a640b4a040340a014200304401c5a1110300d00d000b21003050540c9003c00c2650980c0c03c2c030b500190b0fa880c41200001c0e1064034004078070141c0300c81c1c0f400215802003240301c6070748524021b40340d0119544410302480303940807403140d181c88802017100003405040e18502e810905004042d0100107059141c14078840260701c0b003070043c0080000d450007005e141c00c061082d075010f41e001c2e0a081019420410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 464137526 1250 464136276 464136289
    0x50c0f07120b0a0204050901031203060b27010c0804090b040b060703020a240203010906170615010c030c06110a020f06011a0304020d0c080f10060b040b0310150f080c09 74
    0x11401440b542800c0c00041a001595040d07034010000140340300c516581d242800707480c504580e034241d130000c1c1c1440c1000c114800321104585905113903c41465884cc940340340e0f00f141e40348540386c0504000007410342c5c8000c14800f202400c0501100c074000140740003554100310459440a070824000e0505026507000f10381c0200d51081c84c0c1e40c00442e00303200400c0042d4040f401b400001a4015060301c00300001c0784010030b9a016005646850065925190141d0030150782c80b48100d46126180c40b030320125205952281101d200c0492190a014070680144c1c0e80d1601980e94046d2502d8a44c4008151801e0b0300ea41002410340d8104000301070709403541420340704480041d040301c0f80c1d150034000001040454071004140101d040d00a210355101c1612040b8068403406c0034000700880344540301c146500300100703100d85400c880355621075905d09450f01800d01e0071358100501810100c0100c041c0081c03a03028448603204070f807065590310b40110032611350240c040c001c082c0a1100000040c042c0f8002e0b511401e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 464138776 1250 464137526 464137559
    0x90f01020c090f06010908071503060902280c050a050c0f09010602030a08040809090a14010902040f050409030c020907090906090501050102031b0102040b07060e0c04022505150106050c0f07 83
    0x1182d00d0807890b1345900040c2ea20600c43d50109003c0e03c11144001080311208128042e201002d6500f07212242c1d480e1300310750690040c2100c2040780244003400500e55241c0d6045254800e100e0301b08054140402d49a0b6401c0552114090340c2c160807000f00880507107848022a1091034007103c0c0c840495050080080d9a1f0017041105000c2c00765590104041c441040c0580301a680c00804d401090b1034809402e101405144548844814404c00049003003007142c001e507402d80d12b8804000111501d0402000b0140c2004a025000d003ca09881400541c903248882807240c540c1c1d0311000c046602c1c01c000c3e60f044401e80c0c4c1c49014410f01d4480184850381c3e000c0300700d0741101446002000041038600000340244200e500581410000081040c2040155040408440390318029162a030b8603850034407060f07228003460310380c606d840c9508510034517004020001c41240500201c5080c4c0d0320384206c90301150000c0e00203c001c5800400d0f034103105581004076142409444014201e000d151681c0c804104911 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 464140026 1250 464138776 464138791
    0x207114005013003020712111207080c06090f040204060507031e17070210020d09020307150c080c030904091a25051b01050c040510031416030f05040503090f01020c09 73
    0x81c0208400c4c10b20810000000d031010ba007404050018070f2070000300c1002e40035002805140c01c803c0009001c2c101003090300845a90402501142c01810100500e81d4803081e4010f0f131010440c1c4442a50340c1341c40c80a030000d40a241c072010b42d580f4040c00c01510456400440080510710401500c19840d404182026104c0c520380d08c00d940d60712108426401d165882070b82c600c940d440820303000020072045d0040140540264161401070307480d0408151219103903110440030401e91844400044e940c9001008100d0550382074078202040e02001905440a04e941603825134110112181c035000b131104204d4002c0325040d021940790010344141c1c030508911032050420301c44080b0340ca500010b0007040c51200b40010a00801803454401c03003a00c0c490700280150f9028a442058a0101a00a106800904441c841c00401741e03610344a848071105490044202055120001d408506c5024000d00340030b030f40b01c0c2d400b868444c1c2000c8103105180414402d0941150300c10040007546445502c0165041020b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 464141276 1250 464140026 464140109
    0x601090e120f090910050a050105130b030903040b0a021014060307090203070c05120d050106020f101104050301020304030e1009062f030a0203070312020711400501 72
    0x1144a4034818902442c3c03145500311104c80104085030084020071010707188115804010541c44900449840c041d20016078010451400244680d8107800e02a41d07101c1c0001040b6485c050b03c2d1040d210594001034030800150b070200d0740d2180800241d01072080b6481c1e00000090b824070300800065900c038000d05c1641c0f1000e03800008200254414000c0f000e8460b0000c0803558241d80c03104c0c00421981c44200c0d4070640505d04400480c0951000c50b072200300301d50107130041410005409501c0014500c50f40700c100c030410108030000d616142030000e58485c6d8002c0e160702e0354445c0100140201000000000c10803c091507000784425500f10b43e802d8907045580c0781822140317458400341601e0340704c07200740c0a11920001c5072074441e0650000007480c0e903603c6661000322646085c4860382c01c0c0d01644200030b0200d048003465a01c1e40c10a9815030519100e000540c803440d102c80c50703001940c004120900c1403404000f404610015805006081c0144080d4500c0f4424902c0010029540a0301c0095000c5031034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 464142526 1250 464141276 464141287
    0x6011a16020f030312040b0a0c21020706060b0c0f010b060d050411032d0c0d080706060b0c0d14030145090b07020a03020d0e0402040b0a0807020601090e12 68
    0x44031030b0000c0c04203442c0641143c0c0c0d280418601000707807110494084404d9401000001e2001c0501c0c0110340841c4080c2d01c450b4140d40e000d400144030413203000915000160300b40001008034000d03004032801030010306950b59880c0280381425090004022004516a040c00c01e0a0401d031100000c0755000d01051000003266110361a1060380c01c5100c00d0716503030503c902d102c14042a5091840300c07c08803600b0044c102d10100200140340c07141d001d0061181d01600060003c40821010300c014032070390344a000000f8000b92681510b07103098001c000250701c2948440300504a40d034010895000d59004a41130b02e040d98540000744c40341003102081080c0e400f6040c5004c000d071201500c8180e01082c426060141c00d041505401002031282c44400d680f920035840204014600106800132078540503805406850140b05064a600041c400041c0e0031541c01c100c000390040c018006003c07052401e50b9075019506080c2c000900d40903042e0000b91150303240480c02c2c0c400c800300041c024090036000303000c95200c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 464143776 1250 464142526 464142529
    0x10f060f030209040903031509090b07111005040503041802130504090203100c050921060406320103050601080f030706090201090e0414010c03090206040e0612120a0206011a1602 78
    0xa000f000c0c0d049070004d0410510b8000c068040d01b210203140f0a44c904514080ea50b032400b075069481140c400b4120464079004641c0715031044c440419181100c0c0120b03a0041c481700c2d04001107035000c660a80e0260000b0500344000b2040c4844c9594842110105500f403c0d030282115242d018148036603880346503074000700011520140314080b050000f9810030407000d4841040a0040d90240340d21511803c0300b08072000c2c0703007184070b50306c094000c40b0b10380101100d07034455071184014007419140300340780c0311006004c061032100c403c60310800c0c0400700041d0845502d5440d002d03140c000103800090541d0411003d4650b881030000903a10700380e070000c40c0890103680034001652241141d80040d040b6551003c101b00070f100c455082c0340101c41003000200107010407030404800310780460314001d51101040100300b100100c16214a030f005903005000c94002450300d18418644102100c2103022200d0100d0398084541d0140461030040070a0240314407404000b00220074640705a40b46d9600b080c00c480c000001b50b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 464145026 1250 464143776 464143781
    0x1030b07110c12011e0b03011d0a020d020a050d030c20030a030302070c0e0103030c1103030f040902300108061f0b0a090801180c1719080d230f010f060f03 68
    0xe07101c120017806044a0182641000d0300c4039841c214001d6007004202e90100c0c07031800040030303850054000340171130854907400c01a00700c40c0300030103a9112850150100b12a540d0a405002280c800d07240d080c1440301926191142103206111403808030120000c000e0241c40108003601102d90510700140d584e10185401e00703598105411641d50341c00210004002c146c2c100305805000707402075008021a040c4a000c05a4078415081000b4500d00180300800081c40d042d00548001d0b11010020700011000d60812195100102d400320031529110307004000071402801950f400a2044144000080044400d60384c186100d00c07910b0302d100c1d8006440e0324168820302c40a4064000c0c440213004442c03285441d000e142038102000e9901c400119030005072a1600d02c1d003400c00c868007001401c0c06a04000c60f282034101e074598151740540e810800d500c0904001c4c801c011011201e035003240e00da00c10f4503604001c83d8100802a16401d0082070051156101010b903550484561b8540030f06241c5005008801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 464146276 1250 464145026 464145041
    0x803010506070804032103050a0c090501230a051903050603060f150a181518020a09090203010f060f080402010806040b0d020405190c0c110f0d1a01030b07110c1201 72
    0x61110091401038550b150142a40c51b0404d81759001e01140d1a200061021074880304420b0001c10100e4008000c65402421449000c4200e0300700a000b0781c005078084010b5a020b1210303200001c80004d1020702040d030700c1890003054510341c03070200030034a010804284c0d50040501048000c0c0d4016001880c04207105001d81c1c0c0001d00907003001c0e001a07444104803480440c162a208103181040387ea000c03804001140c001c1150822085140086a1142c0b014002d5000c401c02c0c00800000300300100b1002841e00066000f007400c2d88101c03281c3c40c5089002005208541e080c00c0801524400b031002503a801005d05802c00822640001e072804040009006058a81c0b80290414100340802c4000c03c0c408402c003081402c842418003002c0c6414004858841034103600604a002c0056280b6041c00c00d06080c1584000141a4001841c3d40b500ca002c207590910385800c084c400c071880140104421548941d40101d900d060090200d510580e00c103865017403800e042c9028075414800d440c0095002d410650 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 464147526 1250 464146276 464146283
    0x80c0f0c0d02010b0102010b04180f0c08030703050c010516050d0c0e03010c02010e150106090b0c01060308041806060e130506030a0c1e0e10051002010b0924040603080301050607080403 81
    0x30030301c001441d80a80a07107100c108039405546444400e40e1141020b001d141b007584aa20030328550030030310303540c0c0f10a0880d9441051710b40018607034010441550070030040c04e045020303032641500d55088810540c00d540001740800e424020080f0104142d640000550386091800c1ea030200d5581e200000449003020790704001e0b40e00d03600f0101c202d46855010352104a81000a40c282c0e50902d03508241c800c0700342000e10504d000907180300001c005a810b540301610392038542100100e046540c030744030820355400540110350b8004100b0441313a03001055100b000300411080c205034030121030100000d0201c10300c031080303c0400c6440d1000a1415902032140403062a0300c000c0440001d40c84005020711104059210002200844804551103050071103441c4205054041c400d241400c3c00700340f00388449083c01c10703030541d905c0741ca0400d00d80ea1000310360f42c40746455040c0d42000201c2d040f0106110305451100314003c0e881d2003414004503c07208116819107000341c40e1a80d43e84401d140000d028803503a030025 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 464148776 1250 464147526 464147533
    0x304081e0a03061a040b072904031e030605100302130e0a090b0f0606072d030807120908070209190626010507090608100e1005011707080c0f0c 63
    0x3452025015803111041d02c000e0740a8100c0d060340c0e090144c81d188520300426005420030300c600b10000350781181051034440b0001d0322401405522001d050341540c242e5086000c42e5014468034281c039203903d458540c150076071a05110640c0381501003000146130f0f00c0008101600000e0340310100c9190305564000348800c1c40d41035043c1c5029400f0308018229600125000100d810128a200381e420801c10b000f900010001d51500f00e03165640440d0000300800d220303814007012070007903030302503011070003442c2c64001d460711009864985c86c02060594060b40c601e02c1a483e02c0d000c81c0100e001038040d41e0003036905680088080d10303842107070691014a0044000301ea41088070101d101b0400c030180d03400c2810044a004085007010703030024282c07042101c80c1800140405010004984107000b01a00001d0f1520306121007500c451003182c049d4812904602ca9102d03405040120796403002040e804281420300c00c2c0000d040800d00101400d03000b8047c44801000407802c0440d00c03256004441041041c80101c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 464150026 1250 464148776 464148787
    0x903080105040e01113f0606070c0b0a091511031207031b020102071509050a020405060f0612060f030708070e09070b07030c1103030405010212030903130f031401060b0304081e 77
    0x2d0203002c1801b1000d01c00489156600b00c822090402e154501c44016132880880c0d442c4014040786400110701601d4540e40884c000811030400001882d140d50b10360740d41e01070b0501f0300003031401e50011001900d040100a0244000c20710010096444040c2107280281c141c0d00c0306002100906404107082462809256500b0280b42c5c0550080811038410010700040503c0450144200d980d45280509690016407540c401403070a9400103900c10f900424480c062802d05020a20701e4014000c80381d052000c000c24000b4030b181000124030350420850040000b02e06050342c0544a0490b84510420035101c407002c0343e00c16800b030013002c01502405150a0b203a22041c10000c0c220140200b00799144241c0320b408103843e041c0072048406890701a001000403240740c0400081b82d40c002007180665000510220102c1a042080c0a0003072100c5005169007600b1818a4214111203101e02d0040b40e1402d103041000c110014103a0768043d4002c2d0b07180391036403003000b030449405c0c40d2294040c4844200003131 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 464151276 1250 464150026 464150047
    0x2030c150a11072d08030a0c03120906020415020105010b180d050c031f050601030905030a0521010305060402120313030f02031e06010f0501091a0f07050102071101120903080105040e0111 82
    0x1010120004070513000c00358981d03180b201035140e100744055000020010881c04010900034030500d0321180f18000c0c00181d1200130745410081381c1260300020540c025149031489029424000c140c050010314000e6803030802c0e980d0111411846d020f9080d03001d80d020208035402c1c07280038407150000f140e016085d1441007000b40a1b40c0c0e1104046140b0040a80c540008280c66510a101e43d5600e90313880300c000c6151100d01c800a444641103228001c14003015003c0201c2c0da241440800b078002c5105000401040c2481d00c1006294400c402820100e80c1c428403404404240180b000800c490304400b800d07284c50058008607080082e41700c0c003034150036881210071081041c0014050704031a070f4030906d00e011355111801112240c481b0b20844006129811412404003850001021004083c40c1c0e4640b801d0040c1e5030b40c500366008071200359502c070490000145696000011800181000c2c2020886503110390303005030081e0018002c150159543e8034021025034804d5100b4900c6498400c0c0303d58403500c0b43c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 464152526 1250 464151276 464151329
    0x20303120a06030c0e1006110111221e0302040b2805190305100509010204050a030302010b0a090605010206070c0c1d1608060913030519050702030c150a1107 69
    0x4000c403201366505a0001d00c131036001910394010154441c2c04d800040c42d10800711244004003000301c405540e60a051202414014010700c000310007d05070b07030000241070072800101c1c6020380c07043c0c110656810001c0d1040c62481c07420300640b581120300003031400c8c00b4804200301868442e6020044010401c00e140c20f50094049901224403c44018032007035049030302208100f505100007402c80d8000e100c4c00301c0007482c6820160780003c0801c0014102030b980d8002075005c003c25402940540d5503115203000f1400d1261910010307102c190005c6c80502e1501c00000d507290f40080a0b0810807a50728440b0b006c00148564100080c00842c4000a5005d110400c41c50146010f480c0d0601542c0c0d003c810121040c002c1d005e652145400800050860740e0f0b0070a01c5090200100781101080420411102c046148020141c0500001d0350b400d600c0390010720515190007001711500e031082540c1d035034420740c10305010102d41203402035141103034640c07009079092031915106412143d199040708400014984060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 464153776 1250 464152526 464152529
    0x1d04060303170c0403231e0316020f06030f090601150f0305060411032805090a020d0c0905010b0c0c0d05210d0501060c0203150f0c0c150403110c030312060d020303120a06 75
    0xc00035214400741c503241082c030f00c118040d00507080323810501000fa0f40100ba41d81d070030b0b032403800508500b42c28204080014074680c0700f16042c114042452048c082c0c0b100c400c001250140083e1444141c2d0201d0984000c0c3c0741d404c6003403566040648940000e11310ba2281d0b00502e02141d00c070809180c0740d00b411001658a0b080c001d51804440c10b101e1489800c0980a0080901609003003018145070342d030940038807504206d42748080c1c403407080c0603c00181581071031050170f00130039910301059203503040c0042540c201000307103030480d06c1050050460030109901080302d1034280c0030781d0b10140c0d501d420b02c081c4e00c40b5400b50a040c101903c3c500b03400000c410390861464426984200c0584120201d609240c0c3d001d081d044da11031100000d2000010ba14184540090042d814828111200c51031b085070f03820900c40c0c0855045000800d096590281c04da000c00c102030341c050089001d036040c190003c220481450b8014003c81c07094010444d881c065403414021035036100c0c04410081d05900e071072000c050262089 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 464155026 1250 464153776 464153843
    0x60d050109121404030804050603091e070e090f1b0f040f0c080912040608042a15031a0d0c1a1e1903200403031d04060303170c0403 58
    0x386644034140007020f0860381940e070300504140c01d040c10481841404c0e04000c000340c440e40b040a816040c40c0c1c54104646240510341d90007849000d0400460f0307014441e020740411f81e182e01100400003401d0001c1071860000948016098026002c039002510380b0108001082c1c0080c94242d6800d03550304941c2046110f41c0c41915004c001c1d8840341c086541d2582d00b552600c045032801e000501c84240300e00700d0250400e00131500f0703040a42d00c1d280320250303074440741c00340c10601c0140c1a01000b031a452045054201c4100d82020015034116070b4a80180c006540389d140c2c4141c4101110004004100d04080054901031f845645000c9400c59040b1296100810400420f0b40489036008504503d50488181c01507483d07001981d03000c2440c0a1707026002c200304000590510281000360702d0f03420000b90000318040d694054606101c0300400140c8420700d0700c05801030b0b00b056020300101e0703001003031150041a280382c0d114540d90740c000007030558001e0b0740009042d2141120308000c07880d54050306a0585030b6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 464156276 1250 464155026 464155037
    0xf071125150504050105030c03070903140c09070206070e06160606060f02010b03062806031217090f0d0804140607050a030b0f151305030d02060709060203120f060d05010912 76
    0x1c403500580d00340c0500d1003031500040d01080020351181340b080255801002034107208094944070b070358946540c941c8200214266010480b80001c40c5003034034681d6009061070001e4040e070f0902681c003c01c030440308510a80601d400142c03045555210030441c03000c03603402a80800005803541001081e0071806ca101800660908003285d5643c0390202d001c3d40103441c0840080c018003002d8880f00f000c00040641c0701945a5503540c0000400c17824545050000519a20201118541031080d060a10003030a01909907016a0328820707a0740d0006110304000805050010050307a030307460150202d960700d4020400600801091203002a0400054a44400281c80c184481600075080c040001418910594405401c0000f01c010310703210b138010318500b801802c030414802d4071600424070301000c0c485180013782c4200f04001d40343e940190120094280c92000c0d40c40c2c6000d02c15036140c450300181c1181c1606042c00c0228426503100311029003c1588540203121016aa0410888803069500c81201042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 464157526 1250 464156276 464156309
    0x15091104020c1c0927022107200606010809031e070209070810030204180c171c02060408090f030a0615080d0507060908041e0f09050f071125 62
    0x600070720b00c4005941e4103400c02c190440f100151000c40c00007041c41c0000c40d1b07600704070110285180366404c40d00307044150b191681c1406c0140004013548584520b1340f00c084100c004440300d9002c0840c82c00e070007403024600142c581c2c0742c43e24060b081d442030074800400c03000d100011603071210300813014022007802103072011403c5c2d0b5010015038060100301d8030a80030900100042c401864541e1280c070071f2141c46c142030700c0400c60f15910101c02c074602d0f030410304071201c0c42d60344a4100101042a04a84588604090b41e5100100f8004e50b844d40050700003005408017243d8441d503030b118803034441120391004086911584160a180d0003c000d80c403507111005918070404a19908009101c404c5030221359119840c0542c0394a501004024420007203484d0f43c02000f0005921410104c0c11900004000078900d800c0d1030a01c00a609017115404a440581800c1c00c00c90088141c1485c2ca500c990340c0d042c202040c40b5140e62140c182403000940d048101c41d08034a15080c41d045800e441e0a50314808201c40020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 464158776 1250 464157526 464157583
    0x7140310061431092903010605010c030509180a0b011d010f08150d0302030a02010b0405010501050405120109170409050c0c0a120c0c0b0c060601090315091104020c 72
    0x10700c00d4030303c44100d80018000e184681c0d407465150603040381d803100c90403078420b48403210682a500001e0907490b950184143c1ca40022540c4c445801404d00210300802c50a490040060908504008050244800840c0000468075000111400950010109641841c240580300014a001c00259001032041e065800100c0c0341c00103502da0000d0140c4840200c00c01e12242110707a4a0010280c1402001d4000c41410585a035246442c155110717802840e01c1d0307500900001c1c2103510614141e0700c981e040c94010011660000116404d4440c10f41c0c800d040c401c40f88000c54050000402c00919409482c050415185070a0000e44240c030b0700707024103000945408040903407501070340d05241c2003a0008412880001e248039000801145a8106400400c1207031f2030b8501c11303031550751000b4403012001540501c0030701e090180c103070b0107030003428103070b00311415030325041c003040d10303610f40000d0150391101c1c0c00f01405000301c45401a950002d00542d55074000f44806034641c00101a00d156402101c0c0740c11740344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 464160026 1250 464158776 464158817
    0x50403060b0a0b0f16170a020d1d04020708070b0c09041505100c033006050d0c0510120f021b1504031808010e0d0212041a030714031006 60
    0x200d440d01c4002e1428402e0085030079a585c0c1c003801c01042c619044005500000d2802d0740c460360780c02d09040845882d241e01c02006030412000040c000100031050b0701002048940c04c1040c0824007003950010703100c0f29240b8101c0200d200e00040601f1a00c070420402103040300d4180242000b04041d1001e0104885042190070300401d41d01440358084190610340ea00984600c04c40b8440314084e280c005800446070040c100c1c26880d902d5510858070300081a000041030358082d41000b48015540e90784072107840d4841c074030680100e0040d5441150760030f0403040d441c0d201e0465200c508142c0102007101c0b2051294410080d0310000f1240d03d44041030980181246000c6040c01c82c0d9440006039211680d84c0c1d07a0204c0705200c1d151401c1c0c4640c9124140802c0070b404c2407180362a68030000d400ae0000e0700c008400a8a44620601400c1803480100410300480d51040030016180762000d070b225807203446c0e054003030b60840e541c417030404007601010040020b00b4003800305c008206c449585440d0309840400010390031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 464161276 1250 464160026 464160029
    0xd1a150a030503070b04020616110f011103070b07020132090105060a03060c0927050f0106020307110a080d0504090f0b090103020607060e100c12090c05130e010606050403060b0a 78
    0x2c190070030f1110002058420500d10751041c4018805841c151041081e003607a40c03880e0000b9141a6001c0480b24420300b88001c0303405511200742002c07102182e03642c0d01607941c2e1003a40d10003003624400c180400d96140c001d40212000100202c401d1104102c40e1b04034000c1412144c4540036080300c07d502090400606200f003601440001d0007118001d0f085403251030103403509110010401983c2080010b64030001c040800804403a2418803403c1703051710104406544000c0c00f0b0405c04110700e00104402134000080310501e55103c800c0c2043c025480000540c40003080c0d00125581c02a140c804180e240d002d00100700380c03180c50310100724212070071484104903143c45c0b5001d40c00034040d400600140c900403003e0000c1500c6114049886690004a14140700e0051805000b00780c40307800c58403004c0c3c0c1100952090301c3c6200b00800280c18180c950f14110645031190034017609480c0780348810b410950308803c014440c0c1c00c001b4005c91b59030350300080c641e600a10007901c031585041c500300c6c1b55203400d070742100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 464162526 1250 464161276 464161283
    0x2310140c04030f0807020d030e10030c050a0309020a080304090e07060203090109030212100609021803031305010f02031b03030a0f0b1e0f1e01110a1205090d1a150a03 73
    0x9081c1801c40e940c0e08454501100c00307507070500c3d090044038016610044a85041882035658000102030b66017441581e1101c0080ba074181401c000d19502c00c0d43d84003003038a401c45402c1c500450380714040d00101c1d0544020b608044040e000024001c0381d2890b940c0c0001c07050810050441e41020741d500c0c41240c03a402186003040c00280c5114003000980b50040300e094002c11007906540603a03205408403402c0f28040c0e8001554503402041740c114843c0d040509100800341903010b54038002890b00030400c151918018541800307840038003003001500c20000c0e81c6441c0d140d4a101d103600c1410b000300c035559400c110b840100ca54140040491034601a000d00a81081c0103042c403845001601d403500501c00c0305965064100050880000072503940700c0c0c180d0301450182068000c40d24105000505441110640725002da20103078020f00085d07240c1c0f021000f80c480a141040d200c80548000906914203610b01a088984022070501401d0a40d02007500486880c01005070502c001403d00c04905100e12019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 464163776 1250 464162526 464162551
    0xa0b0609070c0f0209040627050c03030708030a0908090603070206010e0c0705030711012705100809060103030f0e04051e090d090e06060403020405090601030b0c04050901060507231014 81
    0x200f0040c10b000c1d00c8942c1045c407501c0007042c580c42142c074022080e0082101d00101c081c90090307600500a0901200d0541e80e004c1c2c029501d000c0f940c2e10381d00039038400684450710702c565170ae080c3c80c1440241c00070380340c0c03c1500805095480c00c02c00d00c0203544503428001c590707074a48068003140b100c81c48101220141540080618105110307a00d92080d0544000c5a036030503c291205140c26902d581561520f080c6201030311007180c14100010b0100702407288001e4401d10441d202800000040040d80d07604407070b0705180650b1300c010103c80882e00400d0950360940c000c0c0c1031030700740060b08048180b080e0032140300058000d44c5d036891003040c40d95000300d4420400840d1084805111513039410310407a0b0f00c800c01401d41450725030f40f03070b0105d01200c0085840208940041c0018400c00424895a5070085407900c0002e0030a8203100005204001c10312a440034400300041403010000801440900c402528003540780185003d04501c1d112070405000031603052424007403410030490305004501550344003070300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 464165026 1250 464163776 464163803
    0x3050705030106140f0d0b09011e020304030e0d05030405150703080603120a0320030430080f19141506130e0402030f0d050d060902030411130603050a0b0609070c 71
    0x28000f101707140c200110f0700011080414008a00054459401408034000010301e00c806551065050082c62041c085035600400c00d100c0880e40c041036048580f07801722108001c11146150207480e501c00c40e4016038014a50001109540101d440980385550181e11a0b2860b0361b02e1004144c0c480e042030318510b81801c000d0021340601480380d0300c46980c801365480c145950030411000701c0650781003100c0c00c64600d1502d80443d007880498109903a5282c200305002c4080c01c00c2c0030320241640c0701c0201413084100c200000601041c13250064a000341d40c0603c0c0410411802d84400c1c00c00c1d04084841c0600c4009000c500c03000390401000301c074000040c1522096106040c403101288a14002c1c00c16a07052040303141120300c0d118144060400d01949460709503840580c2d428031003e0f15080c2e4041c0038060300c140200404039041ea181c0071503510048075030764010540c408100c0c1c02440190005070003441181412010040840e100a0255504a0758880c1039600c04200315241000340f6401072428400e00304 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 464166276 1250 464165026 464165029
    0x90a020306030102091504050f010504420305061507020f060c0102070b010e0f01090e0c01080c250c0f06020d03050402131b121104030219030804030308010305070503010614 76
    0x91500040c0c002d0000d40382061100000701c0c005241040c0c1d4182c0a030004080101c0d02d801b100d5010880d00a0030040d081c10302d491540700360b048500e034002840e2840503840310100303181c03184102c510352401c40160a15031070140c0001c00130314080f11441d02032170407031040386110a02c800030fa411542c2e00815030400f140804040c0b0883c0e03081001800b94030340d02801801c002500c501c02a17406451191101d584c645080a51000d080c4010b9103c8aa07040c9080f500e40b0130711801060081c8140700c01e080085040d200d9a0000c620f61284040b144040d00f4210810202e070b02c00603000c2c04410303009450310001d1540b030f2140c18054803080e1040754003603408102c81031842c42c080d4002c254406c2c001460a400c0070300003841d0742c050301e0350064416400b0803049541c0c0004e5401901c21a0040301200c5c04000d02e41ba204103000c158400c88c00085e11611072284022401c070f05185081c0003866005529540b107079a81c2c40c0160000c41c00b070004550500403d203011885050520580003101c8120440b10000c540950 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 464167526 1250 464166276 464166281
    0x10091b060305090609031911150103080d060b0a0804021905060f0406030f0c022d0a030f02012a0c050f0313060f0302190302070609050124050a0312200f010207030e0103020702090a 79
    0x5015100340248085c2c202d41e06407180c440f40c00bd500400e41c0d580e460381c0342003c0200710f40c0c66401c0803000c84020b100ea10304103580003507850b60042d41940e1858203400c242c00c0030250000301c1d5120740d40c45500040c078504101c51210103001254603d072402c1c0044901001c441d400e071403800c03c100006074041e100244051482c200d490801801002d54541029a03421a0034100b140161f829800305040f0f019900d5801e5092141c690b1640b1750103070340501c0303020610b4010151480c0d5a0714004200200300a4800d0140074028040e007044d40e401103c0d52558164101c0220004e46c0c4500008201c040ca000c4612034068003c0705c2d5100c6050000307000c1028959400c0c0c0081d0403809059400950716000000040d00922031103108580c521202c1c0c016401108072901140d405400560103194400340070400901404103505124200e405d14629103400b1100c07005031a28003941d0b4050034454100d29000082042d8020301a55000f83c0c0d0b28a0b581010304e0040d000d911030484000d4101514000048041c803040e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 464168776 1250 464167526 464167547
    0x51207020d2a060c1806020102040f0608040c030818031c020c0306152715041b020601180207120c020109142d040f05010f0e0910091b0603050906090319 67
    0x2402d240c0540c01c4205d00803021a015600941d000d0303940001e09004440841034008010b060030b2400ba4818a86030383c0301c01c413003181340c400104070507001701d41c61001a41160500170307098005070807110f030f2040341084a000030120500d030002500915800344024107000c50000e10030b1805500c0010807a840c80103005207901409444550203500c060320b043d6120f502040640140300300303c1c6000d02c0070409420003003103485c3c025500317410b03c07154246998000d4004c1205811201c540084002c5408a640024007030b00c64101c004242d850102c0028050030303004018500360394001c4c0c2e01c1041042d1200c0c02d0318040382c0d60601c96640846018513800024800c0c81d084498071958240c2070310350440c95000f1034162748480d0440c84256031903100620105002010200007040c80121074003c50030a40741140c0c407600c408806003059500c60030342c00305000b64902403105070029030300c266071855590740008000300320686401c0741c68004d2401181c1e01c9032000040e12034117450400c4010819594181c140d8020124 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 464170026 1250 464168776 464168801
    0x70b0c030d060504290f120303161d011b120507110301050f01120c0b1b0f0105040b220b0103061e050403050906070c0f030305040e010b04120b07051207020d2a06 71
    0xa146e401034180e101c0c81c04607900110948015034681c140b800005580d40304c044103030410013042c0000c0d6440710501035030101640000b0309026000c5401e07815001040d00b079020300034140c1c280100113030354810340c010001c1010300d00403140e843e04000c1c110708241c00d85106441c11003030710030b08030018011000300385a541400e80c8110960b0301031954590140000d41c000a02060090503803070125042040144491048440b004000b00b0052400c0e80d0b0710000d105021f800d0f2a284406980c03a40c92060880e04030110164020131048070940c0e40e031400320082c102e079a84025041305081c2508400303030124060b05000e070780e054464078140f0340b804e0140581c60b08005070079560b0318011000000c82d0700032012003402a42c000d070b50345566a414903664451007281030340304d40c10300c020401c010052108401e05103035109a0001041003075031a504001c94650140400d50440100108240222550009084001c00095480b418800080807100010315000c4011100010f0449001040051015404a401b0381131 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 464171276 1250 464170026 464170039
    0x7082805060402123d050c12060a030f05030706271104230421080a02071a1911090603060f01020118050d120209030a14070b0c030d06050429 62
    0x1e1780180d180c820112880f80702c045d01895a03003440e003a4403000c0f1640d464100e0400030b214604203503040d00414070030034120945141c1d0b50004200c141d030340c0d64070034001190440c0d1640c04200850409507203aa008a2048441501d4100080190440320000b020900f480c121000f10005140c2c0302c005800c0c15001031a548942e881d0011a0700d40c4049035003045d8219101d451580d185041d203022000511180c0405216000548184014943c84190135521140282c400f42c2c41e001e242c50076a00c00c11070b01011000f089a403d0030400700000e0109884000140004280010440c01100107060b110754070501d50030000400004400b0304104021543d0054184000241000b2001c00300100382590242165560402e030409a4503680c8924014489012107a003145450180000241d0710001004010712500b4002c842540083e0b0502960009186c03441c615a0b892040740302403a2039074800d0000c0d8541c1440c100021895007028414507210440303c9a03944d0700e00b071510140e101c1d001001d0101c0c941c80070b03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 464172526 1250 464171276 464171293
    0x302030d0e011b2f090103030509031e030715020423180906150f010903060e07051002030c0106150e060f0c01150329160504080708280506040212 64
    0x1501d0800d82d201690092956010400c2c040320100d400316020303003a2071608007045013516510b980e02c4001c541100da1505125070303144401400b00b8142545e0300040030030b00146e1b20006605041c044010002e05110b0045140640c00d5000c40000b00d001d1400740c80d52007044c00701c508862000d0305203104001e44000b8100d8010000c00703041c01040c1e480881c0c01d00800c0e0070010a000b00c500018041d043c2000c03040740e500c6180018480000d242030080d210190a5548170790303012501070f1007403000700042c101c042e00c5407500e81c45181c1c02030750340e501c01d100c1003084d50329101000568110080c03c03218008402ea946480740035008041084036003003030f405100b001798204000d8040b40803d200311100c101b0040440031449246040081c4040c3c40c00d00500b2003180d459420310101c00141c2c000c250300024040342c024250b00c0c1554101e40c03500031034000b035010307220310040441c0d482000200c1026044805410400c070613220040000d1a0062410042c080da000c0c802240051500600c07008611160408540600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 464173776 1250 464172526 464172557
    0x30406050c070e0c07140f06040f110306091f062d1206060e0601230a02120c07080c010f09060e0103180b1501020c0607170f040609060206100302030d0e01 68
    0x2580944e668440c1d2100051420100b007a80310b1612000e01c205000380c0b0071125000c20141e21a18000d02c011301020f8142000d000b00042d81c0280c120340040a0100c0d0401c3c948100b10650701c4132214105c1c8220316607020101c000415030f008540c180c4044030501215640704a00048680303050300036881d800070b41400041146140607858108c0c1d1405401c001c240315141807480c81030313024003618460410040920380e19070300c080b460041500d06800242c3d543e43c0e65000408a0612081003c1c08050f100001988041b8000000e10f2109a070b00903020748007110004001524003060a44040c1701040103002e04010781801882c0c81c40c02e00006044c00308131400084030041c1c400c4841d81d01211a00064424403d03a0080ca000c0e00f44252030078002808044800c50025551b0700a0100c001c0c9280346a6000103400580300f42900c3e11600d01c894850780302c03616124040c00000c0e281c026100184200d5000620348480129100d0480e41c0190141c030a04410003801c540101004c50300d03d06208480b490070011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 464175026 1250 464173776 464173799
    0x50906180901090c0905060d17090604090510090b150315040f09060605041a06031918050f0303011a0d151202030105060604032f0d120e0d05030406050c07 68
    0x303103801800090900700034130703060400c220660040140c0d9407500b01044442c0d1100b418203071040d604407154034544d02424604107814442e0000c09900803030702182c001190321081e003109014407402070f0039220300c9807a104800c0840341c80100c040d0380301c1110700002148140c0c101c02140c2195041100c00750342d010b9880407a0503a601421030000b441c1d071782c00243c01444001d119500113031808440c18044041d1102d41c640c1c482004400c030920030480040170600d00d100c15001c0d10b80013102600c05010352070404660300111a01c1070b4003503405000d10303407061451500200449043e204010f51402440740c00307601003201d6401920100c640c0c683e441c00062000b80e14901e07444014002504800c0000c44144141420340300080c20040c00382e0030500040c80090303055650020782e08010400040001004100410212402105030340c001100e04c0240e424001c06800300c0d8141c118649554000b68288028888100100705014004c0e030010f02040c04054442e2004000f0001c40c88100c0c1d91883d15076058028 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 464176276 1250 464175026 464175031
    0x20d1401150303020610050901090e101802030609030306010507080a0e1207080f01020c0a06020307091806090507080603060f06061b03040807080a0309180f05040b040b0a1505090618 80
    0x101d22070001c10400c159040040702d42c84103402c018080c6040c076050104942050601400040390f4580f030509110000400041c02c40c4c0491f0202031040c444210025032000039a0350f0113030701a0003541d002900c841e000000300c0703003c0c00c0c060b51010300d01301c0140c0b181a050b0f0406c114910400004201d81600759aa51a4411200c07003440c01502e00180703012200e03403071b0060980d0f603402c01d07034014040300300540c0c1c0104c1c41203030b42c40d003009000d42d682e5101103040301c0400d5960494110313440649006681c032203250f4409000da031140b100400c01c070744442d923080d2141c080484145e41d15a1001000440100b1018046030f08500c5c090720740ca080848203048240c01090f00381d40050740364400b20b000c00c254803007049550000c0458a001c1e0001c0b9400391001031030f89810b4083c1c211958000c04105154101950120707000c850b0403a02007005040070725162803a13401c181c809440aa001101007600d40b040351040800c88001490441c190b64981000e0040541700104042c0c0d0105002d10240c044c0007103261001c0c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 464177526 1250 464176276 464176301
    0xc1302040506210a0c021c14030c0a02060604020f070f02151209070506030103050a060b130c1707081003060902270108060c070b07110f07121709010c020d1401 70
    0x5245440803843ea0181e20003881804003900306418030784016000b28081a101d944031f18000c1e4000e034108130660354904810030082502a00100b0400c80b0300100015044407041d0703600f1380b500d83d1101d00810051303025924926022a50811001d000100e00c207403504011440505540d0420500711030b01040c98000680904109030b145041000c00c0d002444103001601c03084400d1070440d410b6880d1180d0b02c03401040002c0200d40e9603580c0040550300c0c0d448035602040480b130180300421860b00018105074805140c540850304d00c4010906403401500260f103e0301804411180303072451500d810000e422000001c0c1d0f0889400c1054019104040c4030441c0d82c0058124109070315454114050303c1c006000700001112502446900001a010f20b41c3d10340103501440c00290040144a8641c01d0034036100e0000024840ca140c0041d25594894000221500948210525204110303140072140b003002949400122152851401464071040300380000b0f0143c0c1c5040300f4160084049802c5812070310242 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 464178776 1250 464177526 464177557
    0x90308040b0903210a081509131b03020105160c0906030602030709080c0105090108280c02010c02010b03030412140105090c0f030339120a140c0c1302040506 69
    0x2d807142001c00462112101c103000c124201c10341d1211201117402909035280c10000107601042e0704044581280e00d0300c0c00010003841c00d5003040c40a00c0c2c60f607020a80100e9241c1602c00e00340140e000c544801c0c0c01244c0d01a100c8611300b02024101c050f02c00500130044610740107011011541000c82e00c180009944215801a900d080015024140c400c4540c01349440d54000c1c56000c032141d0703214003a0b507841d440a0904048070740300c1140301c1581100c12000e44d00c1c0440c0ac48031030309003001c59801c8200c50a403250000c12911038030080490a84050000c0160075910800c4200f2a00400402024140380118442280c1210786100107083d80c0099a10003440e500082442d07005142001c004488141c086008514044034010000044450000300c0300c004100c03040e20202c11005030700381450440214003510b00d0700c101c20358180a1604412200303400110041c049103141500c4008031454003480000425100501004109280d00d42000d0310000980a01000801c4d440b514040c10001c1840f00c7c0c1d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 464180026 1250 464178776 464178787
    0x806010f0603050603030307090e061203070302010507030506030712080c0f0304030606140a05130b150706140c120a0b0a0e070302030402040b0f010c02040f0204051503010611011a010f090308040b 86
    0x10b050302e4000c4d003110f10a40082091080b2160000f404204030784500139028000d03501c85000413000018280c4a0119003c00111101010760642c8000c0c0725000360340b41040b543e1150b00605542e0b001900076a01c140f140d61494a000c034030f08170007070407111414204603903054907043c3c071450554015600865280c1c1d01d6030014411110031168010303041c0400d9401100c003d02c1d100003c2c15188449100203940781c0e540048d500c01da00c0d60040e04c121101601d26142c1e480f06a860300100074038403d5480c5c120b02d5032650204814400d020100c038a104900000f16106407070b9504507000610002e110030fa44901800c800040740070a075000280304908a0301c0050701ca24050040c04142c03035518118610034801110042c00c07507038000150440c0c20f0380590f030000360030740021a0325000f441079810480e40289402c041000e28000140110305039081c40d9241019521088450350a0f9080f4000030092010381c131001d00400c2d4425040720542c041d0924080c120513a80307460340300e410ba02540101201000000c2e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 464181276 1250 464180026 464180039
    0x325050a0803120a1119090b04080c12030a05040312020c09160305250c060b0310020403050d0c051906090b101d1b130b16031b0b061002070806010f 65
    0x540e109501c80c0092084081404451724548540d50808103903540104180c4040c601c1130500c4005801101512a510b0703441d882d55560f9021400d20062140c1c401d0220008880c00c04016141e0004003030b150642000d0469540702030b43d21089512104500c00e84088180c1a594200d580f40201d404281510000c0e0700c0035001000d44000406080300031407011901d003041040c01880c0d200c4520305113455004080750b0718000019051001c03d5540c548111851340d096040b02d503000304110391242084404100301d860003501c002d800c008010700700b0f401400f1000083c1601015030717004140308840010311a441995010740404050710040d08058108a080c405880500072282070b000c10030b50b10081d145402c2441000d82c2c1603910200a19620218045404200b110322200180040701c101c5c030780f114501d0b90b19403420780d0050300640000d214142c84100c10041d00201e0480c1d160003944e45015940d64005000d16400318182c3e003070443c403032800006105001400a44d000c3d0106400c1c1103e203503e03244 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 464182526 1250 464181276 464181307
    0xa02030c1c0f0c021c05090406030507080c19210609050105130b06120601150509030a15110a05070b04111c1401021c0b04021c1b030b0325050a0803 65
    0x5120000c4d9402140514041407020465071011100b5162982d550a817050110b070282505030b2000b4520b210703400d4003040214022901c4c04101c08103440580c015114103892242da480d15219050508681c1e54001e04070208440301f210b04103028040c003050508007907032200d084417021a00c4020f07010201140e6003c10a284448a4002000321000c400c49029440b40c2c40d25804180f0604a15400b05100c074606c441c0038a00303813507c4c40d40042c05e541446842d400c00440030030401c0701171060300b85815800e0f07000441e0142035032980c60743c0c1e58465060114599941c00d2200300500b05446007100d5003500c2c0000e80d01c400110741201000400402d11410619051000300c0400b2a0303424164014410310640c86540d0920000d501c54409001c04c0e8400b01d100803400a104146420008024000d40e000a0f0160380e000880042003d24000040e40511402141100c040446103503060300300c081540003c4d24800c0040141d40820b03031444c5106680d6200007016811a544860741982010441d06441c03006038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 464183776 1250 464182526 464182541
    0x1090603050601020c091509070f1b0804090b0a080624030601030b07050d020d150314060411041505040c030c0215010f051e03060a02090312040308030a02030c1c0f 72
    0x504081c4524104000080d4484102040c80c030700818040e030003d64469100500c8036111a405000ea40003820300503401808021003a188001203410000000c42601c0b402d04181c080640010001c0c0c00c0c80d0610780580c0c05415001c00699102c83e00400c0843c2c01c1c01c0c01c2c04800e010b42400918001c4200c410040211882046002d0510a40100300100f000c505030303a04e0f1540c000d82503c1e02d1070355044403d8040009004400502907a145801034404c0404c1495004800740ea01500c04804240b521200099030b80008440003002c1c601681002e1005080607004244603800d0051300441d000c4d22a404982250000c0c0f0300b010000fa100c441c0016100c3c0c050002e5031a074004602910419814803031116900f00c02d500c0b65900845000003059041c01801003148000307403008003a01d0990800340d0110010350850b4603070313501c01d001e40c04800c414a4803071800c40301200da1119080b400c41d902c07181c0400c003d41000b00070f6a441c010400c00c91081e1100700c45110725450f8181030010380045000c10201c2140e061 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 464185026 1250 464183776 464183789
    0x5031909050d050f070507080a0b06030d0f110705090c030f0f04050601050d020d0605101502010b1309050109050a06150b0c030d0e0115060207140901061209020604030c140109 77
    0x52400d0100032900105144860380b0240c2050340e582e12001c40c5a8a41e0702c078100740a042c0f40520311011442d400c01240515107280502c0728954251169000c2640390030140514402055815100d204003600864403210701040319001d40f9070b000c1c1d43d140401c1c03007184211083c180d0040e0000812021324810126542c101c0d610789050b81c114901583c0f4142e40f400d0601480c2c0c89403503000300180855481d0f00c450b103200c65110800740407d0410548002107103c240c0a085108450301070f01800c07292052040408840c001494054405803914910340141543c0401340e50a5491b075028402084042080c51400d6100c0ca00c0000c520200450070140414035400c14125604100404e80e500a40001601d151a0044000140100522540c00c0c01400f007002c480c0d018160071040020720b6174010441c0400c413a032946007105141d400100700316101d01c0074000c0c180030440300601c0d00d0703004825038801d81920f84041c158a01d41502d07616076910030400796200c1c8854010030400014130396407014000c0020400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 464186276 1250 464185026 464185031
    0x60901060503030406050708070807060902040515010e120a0803010602062e0306150305060a0b280e070e150c010c0306050f2713021906080f0604020712050319 70
    0x41c400041d03100d10452040c07108108012640c0400c6c4540d8200700d80c0102c0d401540e0566690075880c11a01401822005034817480c6840005529242401900c04c10b09070165500300b00700103030404100140100c0d8019254502c00d0f102c45c1c0e40094101c1d00198060001500108124503191140d60802c81c0c81d070f15403c0700210101343c8148282014141356080c1c0c0c2e0300031800b0500746c0442c046250007166650020b002d034401c0307030300744101102194800f600e00101900c01c0a6601035501c02074605100c1c80ca00c024102155102c208079803005041e10541003031751490310140c5000b919002604840035240c003042d0384400000c4c140c401e84401d2040d02c900203264182805440c0c94000011030f0450b01da0300300c90040401201034240498a071410003070b20f580d42c4c09803800d00c0c1001d613070214211a0320041280100c1d07c1c10011403d281c01c024002c4221007407a03540380c090740c1d1601c141000d50071024190507046a0244840350002d18941000d0614020302e80e20b11751030789000f0300074003000e0020a69201d4081e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 464187526 1250 464186276 464186279
    0x90b010b0408030a0e012c0f0301023907030804050111061605090a0503030f030109060e01120f0317040f0606230609030a140c0108060405070f0f0e0a1706090106 71
    0x42010013503442e80c032020b040180c4210440c80047c3c3d10101c40390003034590f07100b080c41340030391410480d080c03044400026212403d4041800301418201c0c0300d403000301400200094141c00304405917041c5404202860328074980e00c100c175480018580422508101d408840c04141400596072100c02049491072080c0100201d0904a1881501000e20500d480030803000080e465080e03214040848000c080260482303645505007850f0340c02d950000c0c01201c80982c03c2c10000035a4400100300c00f41a184c01c04005002001959181d41e003540424404506010800d0b0010f2014201e03203103124402c9001340540400c0d544d5a181c488111440c0760040c40e4840340c00403d184161102e02c117884030300c25064410654505041000a03d0140001c100074814440c0450710302445502144200b00480e0a07210380710246c0340c400c1000141c41e02100d1801c0040c1b400c1007012030440c420003095611030268140f0a44415640011882c00d41a540241303080c50b2034450071440c0010f00300300d80d6074041c09000c020090345 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 464188776 1250 464187526 464187539
    0x3060c1204020f0103150902030108010b031c1809020714070807060c0609060f0e0714010503060f101101020a2a0c0e0c0c0d0809010507030e0715020c090109090b010b04 74
    0x50806800f40e0102c48a0840d580d0080d0b0151221018501b08220016038450046010b035000f40113901035035003004094141404c0c0010401c0000c02a000d007075141103000c12084800c0c50441c0c000f000301c50090840060201258401481c0c0310b4080d00802c1070f1501c4d0200d00b00d00d07221403036001d480315500071001000a1503201c0148000c2a50181003c03800980343d007440800742440c10200001070f45050400400741000144120440e40c4c100d9a5410011448006442e54001116642e80091801a03881c51602d0810702802a00c4801d00f0103c12507603240e4102c0d802c90304200324071000720b070039000010900107035003891074852000c0c80420080b0320340c1e07503607010b0202c500c0d84601443d07110b031400032611182e0100c1c21f80700c0b0640e008044426808010400070f00d180020390f044040c6500c1c040214003040e229020b500010f44a05005203505443c101e480c0310b40d040701c00c001030214010700d20f100b48240d899011190003003400903004078a410540c00c0c07030031004c401a403081104680410040011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 464190026 1250 464188776 464188807
    0xa0e030d1d030a060e0a0215030708010b0f120a1e090f06020c070810050420010c0312021605030702100c120e0a0503030304050f060703110423030a0f0203060c 70
    0x109108014901084441c00000c03e00d005039160b00100300c0381c1000110103a8035800104501494000c9803842c21070812081d400030184010303075014000940040050280d01d0032070004142c010251140285414182d034161445c04074241c8000b6001341d200c0e10100300300280c0c45403202d0615203401d000c000358101c9a07a00300c015924084000c08458011070700040b009020b02000d0001d00414003a01e082d002040d08a0b0002e10003160121080d000c3d0341c1e04010b51291083e40c2031307210001a1504481c00ca0a61000e070350300d00801e08420401c41d02000402d0780c0c19100c00341541003500ca40029a119201403040181c2d40c03440742101000c03c1076602085011802e100516400308805040138102021803801280c1c04c10229000150144070000a0208100f00042d81288100380790302514025141c00004070281c1e800048500302182c024001402601a00031071400d8004450b0403403503a5810b4800402e041048440003a40c620b8448e03504002035040070701480b94042c14030350f41e051074060b081030000113 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 464191276 1250 464190026 464190047
    0x405060126031303020114180f03070f030302030a0807030506010c150605030a0c0305150403120c0e060324010207061409030102131203030513021003050406240612090b240d080a0e030d 81
    0x1c02c09c2d12503802c06a43d1070900c00100603240100c06040c83c0c0380c6038240a0341d264441150744000032030500015814501c80d2040c1070007510140e45e620040102c44d16560051514400440113041d501c0d003000a80f5641040020540d51007080700b072410514500b071250401002c080150b0320741c1b80f203400b0030001030380c054905050001e54a0000948540304503049552061000e011030b003162000080c081400c800300001d484c40000c05c80c4510200e1a241c0049032030340707614814600460030012903000d5802d10350000c0c054030b0401070001030402e54202d083c2003000c00f65074011944107041c5c0300d500c0285903042c0031750381e031000002c032101b0080e0256902003a528850f0a09030002c25669002040400010350030000300581c8400d01c03280d0080c0d03200000803407200e2511815001c61440041104c20400a0041510440d0080717101c031901d80d00d40e41c4a101c0c0d2400e01466802e24100d41040c646c50340e60b54011408410b015044071512460240c5000d81803071002c0034503c0c405d03804485401d44c5c69a1106a242 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 464192526 1250 464191276 464191279
    0x60603070c051207060207052e090303090b1f060e062b09150f0b03060a1d01111b0a0b040221061303080c03040506012603130302011418 60
    0x1c1811410304200341424400c0d0500908007400140020030301c001c0c4c0c0c0140c00000c4c010f0060700c900d21406120b02c210345140c1410006402c1010301d10702d07141541a440032074024040e0030049000110b0b07540f1015100021070740e10000b200380d11500d00c01140c1104a0704094122400c104481030290000200135000d540d1392202c0d50304041d102144805040c46e150b04a1034040602800801c5151030000024500030311080491071401200c1404d800050040380d03107502c4090081c00c0d0740d0b2034a11140300a440c50100142143c001e41541d00c409000c01d100b002d00301d001010740749480e803c0c6180f404140c008841e04031082640240544404120b809044541143e07045404003d8188004403452620f02014804107041c000c032000c000c541160300400d90801446551800c0795540c0c0c21030420b13031034001501c0c00382c4161b001d00014403140282e038101e100c02094880f00d20140c41004010b0318510782c4600110002e01000031020421960030405c4400603130b000300a030754249400b842174a4015901d160005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 464193776 1250 464192526 464192537
    0x3050702100e030d0e2b02060306060c1c020c09041223160b1e070f0315060e03060702010c0f0503061314010311040209060403020f01030f051906080606060307 70
    0x8094640a080010600900038042e40c41d940044d80000d0301c001d8891700f07007034061800e21104960400e4140405084200b6880d020104155140c0034041547c2008202a8102200304040d1034150020411040d03c0d9030505180c00c03c48038501c20082c00d0144a8a545002d0700c3c061003404000b4045200c22405e07450240b40201c03030000d00051400105580010450b07078210001114071103060301440c0501c0d55030207036500d050640c0b614169403a0310b4012068855100c10480080b07040d09201e0342c48101c00c01002e01d400309449818480348100d1044d9070780200082005c00340c2e071400314101030200d59030100080c0020049441604030281c030960800f0817072030070820f00000245160383e030391190403111000340004004d0301a14030b41c0c0c120701c8002804151a417040044c201e000790f140034000c40e00045006042c59081902d50380c24009007a000c0761410781410340b900103041821050340b00c1c56124020329108540c581c02e1607600c0c0400c4449075003010300590041c2c401c000d481c1e1240f004881d003000c5c003403500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 464195026 1250 464193776 464193799
    0x109151505150a110a0203210405040f0207020f01030c0516050a050d17010909020112050604231f050f240a030605040c080702060402040e120408150105030a03050702 73
    0x1101403014481d045194480340b0044080000c007035000c00f400840d5125240d511114005100150351059002d0000350f00d507110300b0802039006000c4040c004156000f284071418036440f0790005d8203691050f0303d0900e04e540e01060103810361074900c502ca003141d5400e00f41000a0070061030000c0051040c0309840c0e400d060394090003c20414100304c075040483d0444295a207652108900802c04409200a441c80e8161000080b91803089032080200b1180e0507101e014854031282804400350000504440d409540d50105820213103203081110290030070000042e005140c901c0a01d2903201d03802c40c0b10442e041400300140305644a2129030345030707510200e456401c600740c0320840700703034012004540d00c02c2d0400200344e29003500e0701a04032800ba00e500300e50600104c8a560030072203100c0c5044411100503070240010402604089c2d20075003070304500c00700350745211a640030030340019031080e481103000d81e0000d81001c0070130b444500d03054054001280a05141170b05030710005c00d10700808038064401c20071a03c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 464196276 1250 464195026 464195051
    0x40209030c1809120c061513140403030f06030b040807061107050f071203120509030c0a030c140105130602030702072d0807060c06090503040902130f050102010915 72
    0x8640051100404200e641d8848624100c11040d0036110100c0d140700e1420704c0044803100c90f05a40e5004c041c0b81c0280156a41d1140d80c0860003c600c48098000e1a940074100c4800c009010304c076400d0740350140c40410b40c1064a4005c2c00c0340c500d0401070b1501c501c0d01109000046580403e030b0b8105410040b80c130745840c040d0400350010040a05e5a1150440014054041140101c0d5401e001211035080c1c481c015030700c0301d02403015810705a0040002d8072000d13814102c0032980e40300030740100d00311003200c0c1040142f81e038461800344545002e40200d580f03102c1c800c0c10440c640f204a8902d200304002840740d07080080c0d800720210031400300249801e4000c00040c103128401c101d61001817000894025481040810401d01c55000030f1500890400216010440100014591003103a0081c1e5072422680c0c034030303111000104a16841221b043c08200000101c00509001800031100482c0c91001501e00d8070800388002d030180d0340800d0541e410027203000c010a103049010812000c0c002004640c1c0c203030303902 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 464197526 1250 464196276 464196283
    0x80603191a01170106090b010e0d1b0602010b031c020307021e03011121041214070c090c12090309030816060e0325050d03020703020f01020703030213060e0f04020903 73
    0x1207041400031031440005642414107140180041110008104840d00c0e0189581039440340204d6901140c058203c111050402c0e26405c0c003d00e000701655000c3c030a07403207890128841d8580c03220006039152948248245400e20180b1f080c0310345240503101510f040440a23489000d0544060300c43c40030300c07141c41c1140b0212182c4c104a044005c008010700380308a141e0400c00e4108200c61408485030903d08a030070000011018021600b06400c0440c00d030341c1c040120f40c00013080c0c03200c030441d01c4244060800141a12044000307481d00d10404034424041c0c940060420b00001101300440382085d071002d01294000100c001584d42100000e030780d078030000005100c410001c070002410705141c20000203030044048050300320040080d007901e14058030074064102c1d00003124000303041038020703500220455000e603000b4031403d440390041e1056040034440d2a82260441c51096011940005407645524a2181d41401a0129007046609204042c010904440491013418003640d4001b0704400c00d640c040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 464198776 1250 464197526 464197553
    0x140c06150a0b040f030c061d270405010504020102060601020a0812070c020319031202130b0d09020306070e0a060302190e030c041a040c0503010b30040813050108060319 74
    0x5986981e5036507913842d00e0503038207000c0c4003e40d02003804210210303c0600c6504507080c0c40e0003807440910041540300820040c2c9003c811800c90094280002d00030b4003a50800a41c4903d00500000880f0300c2e29000290400000800382411504003107100d50004440000b60b49001c410001013041640c1c030803005451039501c561010354140f183c80f92140c2254841c1e140d204410717100b5668040380c81c44200c4048164090300c804a44851100c071414085114858050540c090882c0408518a03885401180c00c204041e1004400603410410307080c5e0500b0315088080042400f440d0451410031003440c181020308041c2808810001d6440c2c808016690400c00d50f0002d400080040243d4a8003600174032444559540c814081d81c1040c0810f880240a4401d41f4122080c2d41440c500c0d114640c3e07400c0400c03503030440c041130a01d9840c01c80340190504800f45117108621440880d507841030030622440500d0349507807101c1e040100e0403003000090303200803410700309c08641c003080f00090f40c1c00c920f0b01030038a0004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 464200026 1250 464198776 464198789
    0x120c0606080c0307061103040308070609020d14010509030306010912020315070e01020c0d170708040b030106080a0e0d090b0a03060801020a1e0221031503060c0406140c06150a 77
    0x5003040460409404189585800c0b41101120742440c1d450000717982c0c1c04004c20402813290170610003040450b8502c0700824003148603440c00a2401850781c00181c407900b0040c0240c1c1e50182d2a1107201c101d1400744100ca4100d402c201c011411450b210700000c20040081c011900d110410030120402c548040000300c440b505030b802818030629002c40c0007840c640900748054018030034461880312a062504d510081c258000720784018003040b041d000c4000c0c1d4802d01c400c4800c035908000010349030b0652400366011f020103031f4440040b0704210030b040741a1040242c11101a8100c5021017002039081501001160b444070406525a02c1408041d0300400555110905550000402d04600383d0300403240c40802c0200850701000340c2c522202283c1d0f5410903c1c501c2650380c0240312100616071441e0156030301c05951741e0300460041442d4040382c10701200ba141041890f2011034103100c0ca5070081c99030350405003444940e80c200030505125541c0c2d200007078600201c0b04484040c00c1159140c07000a607026004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 464201276 1250 464200026 464200031
    0x2060d060306150b03101403150103150624030506060c1507020f0d230702030115150e01080604090606050a03030c030201200a0f021009080405031c050403120c06 71
    0x1e8905200000e4080280c08195004211a012581004080c1035038000c501101c00c0003d41030401518009150f4100301443d41441603540c0301107046100400300d40030b940f140103104801c0081c110b040c429a031b241d8004004a4035000c80d1080c612040484c1c2c242c9051491901080d0b544800d404158140708620b4000300c1401002c01513401c2400707010705103010308455800c0391608240415513076251130304007404400051040035601c031340f11142e1191681c004c804202c00d80c07800e8840d038002800c540440444d1742c02500c0c294010000d600d260400784400c40c00a0078190003004a00700001d02400006010074441c50340c031741201d8240115a8407890140030007a241031b20180e100d04016014a4285808400540c240300e0941c056045100d445d0010b0142520464104581c1c1d0400b40c41c90758030030400d54114452000d40300710382d61140c040c4a0426014064050391142404103260a2840d81149540b1000c4a4204000c0d020350107000c440c02c503908103d0305895270000ca036041b9040803600c0006002d560 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 464202526 1250 464201276 464201279
    0x1403070e040204082b170c0a051b06040c0b09030712230307110d02090412110102132301091a04030b190e060610030f0b0a15081b070f02060d06 63
    0xc0c40d000120070341100401d0710036484c422103181107030b00740e800403030005046c2c6500f80440c010390405006802c0c0c44980f424806e0514401d0040c200360516500c03045081035200700f0520080c00700d080401009004056550344c070b80300c07003803010903950704861003160540554118098144181c0035204403a1035031601d01140140424500150707603420070701c02a1400170030310310026468500703000091034465001d08040815601c03520740440c0f078038011a05c2000c2c03044000000f11101e40078402004001c0c20200c0b08071010f414602c01c00418a040d44000150382200c0e00604c4039a0f030040f4285040740c0000c007586138110f00b4048190a82c0c09a41d00050207200c21200740021030118104204c813003071f40e0345800c210140d001c0071030369581c203010f48036260000600c55011707a4881c420307080510300340c15211001c01c21245120100c1c210319495400081c0207030106040702c1c2e4040c3d004078480d030000084203010341e640600107c2c87c611440b41c440e00501c400b0300c510240046403902c00540c1c02c4802c40c3e003030405c03549 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 464203776 1250 464202526 464202553
    0x201120c0206180a120f1d01020a11030a0501090b0108011d070306110423120604170c160e040308010e0907050409030905060304060f0e030c0c0d05030c0714101403070e04020408 78
    0x40800243e803c1c080390012004034911f0310320043e240c0203400168002c240741941a1500d907120841c40d0a46901230050301180c40105000340550340406103e0307940c0794103640c9050345060840e9044000c24018441030346200d0707000280081c0c42c1d0309494110000051109042c50a0030f09403040394490003a90480c070806500d010220740d030004280c2c6080e40c507102e0003c0c0c80156240c541004440003001001d83c07007141d444003406031010b000a405023500320703262034000080407104194203901c4008035171440c20401003015401141710b401080c810080e0f140ea81400301342c05131640610302a80f400f0f00d694111003802d142c40f8210010041c14050000b69590916080240c00f07400f10a00c04078083d418000000c880079000000c80e01d61003c0c00d0060300c103940002b802c00441c3c1045100541e140e21060081480540341400400010301c02d034101414803540c2c1d5800e1080c0840e030702d000d000c24450030348960030700c210001046950000706842e109401c3c1ca85000020001e0285410049080c0f180c1c0c1ca034503510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 464205026 1250 464203776 464203787
    0x607050702030d05030103050a14011d0f0c01021606050f1315020f160b03040501020c01140109110f0d02031008240a060302060403020d050321040201120c0206180a12 73
    0x1280250705940400441c00f6080e20a44400c0c40014210b500454050001c2415002c03002c0c4003a080b200040703408102107000b100510031000c18000290070014003142c1281e010400c1020540084c0064a10700840e49040106035150f4840e00092080025804030850039810445060142d80c201070b19510303407079050441500c2690100d20f03015105e2030104041c92500011608074900c2c0c24089600018201001d0046640000d0012030b407964090155402074807003802030640c424040f000c14541580b40003500c406948a143c03582e80d02c032404000c9216050701c084100d032102c480410000d81c0d81d450341081010f119010ba4001c80c000d00564021060520344014a454900c01068060030103880f001a00d008131585844000d5202c0c0d002c01c41000141030825601c0308050061003a00d00740a10b02800d0014001080c0200c0381c04041042084115a0031048400540d0362800741080200d0001102075038030080a8603503441c003048000f10251b00e40303041140c1d4081540c8605c109542c035500c103601420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 464206276 1250 464205026 464205037
    0x8070909110c062511120f130f05010206040609110a1e0f0b040e090a0b091c030524060c0f010c080618040b06040209060712020c18041101030905060705 67
    0x464007840c004a00409840d00300c4d810b052080000310011030b4020314040c1d81e402072010110303000e0301070040181c0c0e40009000c082d0001807a14186280e940841e10150010000580c11042c2c030001042c0302404566130000b1815441540035500240c01c04103410056542d0380c42e607549552100e0581da01186d40341054041c0402c000c1c0c0282c450360362640718801c10380003a5080c0260110303a80140010000050136560751f0303410002480569074240410340740c003640f020017141c00b05095840410b20600f0001c0d030503609584480245410005c03400c1c005a03404841078403000f070440181400c0020341ca90390390030f403c6401003100315040340e1142c0281000c0601034280c1d003441c400400c041400003085400e00c0300469174510316103d0002074070354540e030703c4c0c01007060094035503900140d00f4003d00d04640c07543c000425189003c0c00003980030106110009207001144184039004404c000b2040840300c4052110b41d8210380e208200301c80250700d1400483c018207400c41c01a10911502c000d1241e6560420010003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 464207526 1250 464206276 464206297
    0xf060a141c230117030d05070504180903081003020d11120a060f06120f1b050604081005070306150c110402040e0f0c07031b030e0a060f031a0604060807090911 70
    0x31581c1e0b0f40c0c9001c4c080c15006000e804c13141c0c008104258a143c481e601081d802000750070220300349a200c11740c50408545215880548940c0c0700b40081c18560007490080e400642d0b81c11107039000342103501140d8000444080100145414501d221050b911014039400c00402c0904507840424141840c0303000d4040040e411203071074070344480410341841c0c01c1518000181c210b10012030900c595914201400485240c3c0307100318200040c0800c00303665443c014002042000d00804407114000b030300300101c0344040d01107410b16140010400c0700d000e08141810301200075042c02d1031070320520b0070004140d18030203020300d50203440001d022541a0610744901c1c050a012040d5504d181d80c0c064040c6042d108804015000c00c0719440960724452094032070340e02c26031080c80c214000002a8010500c0d0700070940007480490310304c1c0c08004406a040c894880085000c0b24600c0c0d4005003034020500314800c601406c170820603a28001480d141c05183c0300310080846410030001540840b00e000000d8001d4000741 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 464208633 1107 464207526 464207591
    0x3071707030b0319050c01020c1c0201030b090907030309080c03060609070c0b0411040b040908040603240f0e071107210c090b0f060a141c 61
    0x1002d000803030200040b440342c05171501c5404c0c1a40ca81e00a0304540c044040c0759202d5450341a80b03101c10043c0164452036100c0307400101c001c1c0c000309142035040f105803024410207060001e0100104c030b0195580070800b503202c852503034550750b8101455034594090004075440786003601100782c101499007851940d0710090360712450001000c807401d4403030b40c000440040703c60405014165510404440402c01c0702415507500f81540038500580781010380d60403050041035080ca8012035444040400134000c140d03142d00b42055985940100c0b0030015100d800709200718041e854002c42c81307140d00060031415080c201c0350f09400100e9000003450b04410816000402d1540340a030b0003030404520041030040600040c80401d1041c610f03000d004175020005446234685c0800c08e084030041c949411941c407580d0680c10341a081101080f0444945415045034408049403042d02c0c6d20740809842 = true := by decide +kernel

theorem cover : BRFrame.Cov 464028776 464208633 := by
  have h0 := BRFrame.cov_init 464028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 464028776 ≤ n) (h2 : n < 464208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
