-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3127
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:44:43.675216+00:00
-- url     : https://prove2.me/submissions/d7e10313-2439-4cec-a9aa-ab9f81b9af4d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 562230215 ≤ n < 562410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 562231465 1250 562230215 562230223
    0x708030f0a120603140321070c030f02010905030d05010302040b09010b0d09080702040f05040b070906021009050c030d1805010201290d05012406050a12050c0408240f09 74
    0x109000b4030b000241c1010582522019003e6030b07100603c10070440c28541d100000c044003600018800003516290001c981c10b88103c0e10401b900c10070045283d83d42d408000c64403d201803c01c00c0180d0001185100342d0755151882c5901024655034200d640300c005008500e410b0140c940420022580c0b402154100110b00c20b151040c400e13225450f0342c1c0d0b40401c0382080030601c1076540054000780100011110302071200045c0c61300b203d04a401801d20310004141c2400b890024042d55500d07030081a41815084009008180d01101582d03a846543c101c5845a50b040041e1100712650f0b644556501c030411840209001280d0095030569050001a06117151100c241c610900c03415885900d281c000000450115100c01d48041c0c455401c02d403583c0c442100802000340c4051828040c2c0d03505a82e1003100322a00c1c02544580030000d60018640e4140e0640354010325000b01e46800c40614066841714020b19002855405a000013140d008844440025003209540801441107036502441c00740300207622 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 562232715 1250 562231465 562231477
    0x303082d0f060d0f0f140316020105090a03062d0605030303220203100504020901050103110703030f112a0102190507110618030609240417040b0301080708030f 70
    0x5800e000400103441c50381d606403440c540c00e03003003021606103040e941080c216a041d08001501d200d442409544100703c0000300312202400d0341e404000c08c00b1016401107801d603121084044e0f0100c40114003001141840c07140c503006100318100305650341c4030007071b40100f09064600004804c0340350280400c10ac1c0c030080100c1c3d90080103620b160200f0034441014240d0f50081d1200650944103035410718410244583c0914003d6008451401e4103030381c0c0d03000460030740d00145010a0304060038000040001e0080e0014808500140004540c0c002c404c5002c6003150094080421030700319211903004a5500c2c25035002c80895400700030342c50080c1e8002e40821440361404402e04010000401034140f15142441e01d1130250000c081d1951100443e0f8006006800001a54400c2c09580041414081d0014955414507103182c940010f006a01704580e240c9c00d401070003900c0c508426400210380c0c1160300c0080003d03180c9040f0303003a200c1d4100700300b1034a04080c1d5008240705500801a414030650b00b0360035118 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 562233965 1250 562232715 562232731
    0xf020a0f1803051606030605090403120504021807050d0b0906030a08130503010507050702030c012a17071a09031201140102030d060f0602121e030705130303082d 71
    0x6490003410307000d4140040306520241090241003d001000074000042e2421500903075030070302c4181e4035802000b0903488183c80003804203e901c250244004ca10b60003c40d031050008001c80d500506990302720440d00421103500e000a00700103034035404034031240300d00035194005403408021860401c1c00711340da8200c105400350200c100030901e254a85010716020001d084003400a22160600c040040c02c241c01200d0101d200703000c0c11900312403039441441002030b2046404210010303030314400c908d983e1440791312a003541d1001013603101c00a07000c0190024038030140304e802600411003814202d1345401c04003078003148142e0070802a10701031406914408c0e040d1800c1c516a4517590403030340010703440c600c5024814032105040000c0000d503000d10700c00c03010848010303800f41e03a1403003000c642c0b01c4c101e40320381c200207050725034010389d83c5148400c49c030059640f01100e401c042c4e00c1d18820703000000d100b200d564811400240600c080015901c5000070210240d1b0910156400300d180c8503070b501341240b0005040071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 562235215 1250 562233965 562233977
    0xa0b04031703220c150201151701060806130506010609180510170706030f06051c0c031e03020709140402090601021c05030f0603031c02030a06090617010f020a0f 71
    0x506640203403e088141d20303042e903140d0f45203102916107801c0c880401e21a107400c0246010341d815602e0300600422222111512150440d5030a03c0300130342d0304440902c5c65a1407507590303001c040703030f1410100401ca005460a00f01700c41300e0b00701c600e00646400816000310080104124040156000780e1041c0b0072600b0b1084004038041d03490b800301c140135100c00d034031803000e640c422026489100c02c0072071160151030150303a050040c00c0d208800e03441030311880d2003041c2e006031060200135004000c2143c40d00d011480340d00e540c17031910742c0e030f84512200e0902003016030030802091019004164041207608028050100107222611030701c41c50140140c0024406801403a1080000e000383c0e01c00e111030040c41c914030844114000d9031aa0080680d0012150081502c3c940c0d17001c10111324000003542c08000041b12001c4614002c40c6282c0c01130341000c1c184111540d142c00c00411303208428003513030000d8410300700244081580404441d00355107025007c010024410400990b0455100468406642007030500d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 562236465 1250 562235215 562235221
    0x50a0806010b09060d0504060b0108090105060a050103050406110403030f082206020a09181d070806070f210b041a09070c030519021608030408030a1d0405070503060a0b04031703 78
    0x210b0114402d1450503848141b400d82000100a216406055148003c0c1d8401d592681d0320303030740d06080340c0098403559071081070320008000d29807180d005203074007910890001c118214202e100e200700780c0164104401003480500e002102a600840740343d44401c40a42c0012580d40030f00018400da28418400390411750001005211a0f001d0100000101178180106002640c80050b060091a58000080c2d400414420440c007405000509a007912560341c041c1119488040081c1c0d913501c1d9900c4000c0600410300b01d140080034552917842c241d40000d05000c20b040e01c000040008035420391101005410003a401500ea075250301071006c2d88481c490501d00782010140c10706440d00c4c0254190090040c40e107000d44500183e010603041450380200030040301c141c1d00c3d050072644901035401440201d500238081c40a5240c0b1806015071200c080609522941314100007140950300b081300c075440032440c00014041c05d41015840700000f070920900107800d0030301790b507182c0000001e0b400e05140402008004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 562237715 1250 562236465 562236469
    0xb07180b041202190303030b0a081f0207020a120308040b25051303020a090c030501240e01090b0c0c0f0d0302190602120106020a1502160b04060e030a0c0c050a0806010b09 75
    0xc004c210061410380200079070b6646402405405d10702e08007070051450f610300203003002c000a102a55400d10683c00c008101c0000700c031400a41103100241c0e4040c07c10307100020041c5512440500030380c001c0d543e5101e02e14150511841640c4054021003008c0084030281c0010811014082107401881c030f4556521344100d40c82103d80352507a040654018000d1070300291426543c0c0c08a02c41850b19107040c0010303a030701e506030040f00302c0d10072001c0692030060440d600303414460841e040281205040c000c1850b40c680d1914145c039000a840f020722903220341181041803801003881315101c401112003103840e80b440d40c0c1c0217444141c134166190385100840c111100304046a0140c80911140b2465000217680d41c1c54000e68400d50280706940b4540c5c101c100d200c0c0c0e42c0c9103000303d4122410340c0c0c604c103c2c5629181d0320003c0411004000340da0980d616618880090000c2c001070464401c07a40c2c501ea494111410034500145855014511a805a40b000c00c00c10901240c170030b04484501d1062911a544000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 562238965 1250 562237715 562237729
    0x2061302030d081005030d1e050301050a09020a05040e0c0a02150105032a030109050a0b07030204030b070f17090c01080f01030506130f051606120911130b0405040b07180b041202 78
    0x701d203905001f070000303030240302d98040070152156007490100003400c0e2001005640c036100038000e4540048001d07009001904c41c0750004c00e1408894507205103800d0380c2c0e001c00f0312800c800740c51080e08a680050b46e200c500d41e042009040c000207d203040c00390741d49003000295540c400e840d02c0300c0c68065003a11104001d2560091240424005402803020007883d161054031105008030840b1900d800c0c1e004101da081c0b0034400c0e40c0580e40d01c011810b040c2d40300c0040985000e14100ca4043c100285150070000080407000128001d0740b0301401070150b211070b24000b42000100520b4051a407000e000100085034000801580180607c0160318004000b41424464011800380c0900b483c03040c0505124400c01690190023200d19650320341c0f58000034603803917030292451143c01900000c0340000d0080540f404031842e0400300c070403180004032000614081010f8840441d001d964401c030340740801540680040c03500460b9803401041220740c604020f8001c0c00c501582c0600f20100c0a200c0700001191a500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 562240215 1250 562238965 562238969
    0xf0615110a050d08071202071a042301050603280f02181f1d070302030606040906030606061803050712080409050a290310020c0312011502061302030d0810 68
    0x802d907214940c00200c0688641001c2d131300f5400142c1c110811110b014014408d075003200b544000340c40181c20684840103804600504199121203040d04054400580d10b00f9444d5684003190001c9114a0a482058188a000a0050b14814002d12402d81c1c4240c0d403045089043c2c4d00000c220f840e01d400d80081004401c0013104a100c9a542c10203004030400c1c9201020840c2c0c0c0707158410104c5c41d4032240d2a100484040b0b004481651600000c04d80035402a0041c50b402080030346084c2c1000c1c5d8500b48242900c1003035105a808a9803143e05119181e40410300407608443c169025040d60302d07554440356180824402c0c1259010440c0e580310400080714100c074028240030405000504014030b0100c01803000c5289030381094900b000f0b00e4000588051001103001004014105007441104003002070742c045200901075010802c0041c0c8460750400106001c0c4c442030b541d104e8003070316010b0060310700b030700141008001d20103219103440180d0b000140502a1442031901540607100da0f849994894455 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 562241465 1250 562240215 562240223
    0xe0a05060a060f1503110d06091107020607150e121c1803030b030a0b15012007090e0a0c0312080c0304020d0602070218070e28050d050a150902040f0615110a 69
    0x75407203102040941011090768580340c010852b000500360310411510510701c009411589c1805401c001c5030440c040c0e0715221815034030109002d51501c03442d030b08202c40384460184c100350100720041c03a4811021800704480e8064800c0107103040a024644521031020001420103848601010306a1010b00c11091902e80c06095205e40741004207803d00544040c1110900088a0060300e90030380048545280040ea070342d1024100250800340d5941c060000c0c220b40700c1c1107204d01d034441800070341c459002d00011070048450340a14094100b0042210310041c0484000034014401c3c040540e071019001200d00b07500c2180143da50b0308900c0811587c1710701c0c410440020f121401080390103a0003020401c100c0c842214a41d0b04a204407030054500d5101548502805821000c14413160a14407034107810203006408440c015001d50b81c0c4d00140d82c050441e4503156540310f4015204504140c01754420000b00c1c080e09100d254100414400c2c800c46400c0030000300000c2480c002c0e015641030140110141e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 562242715 1250 562241465 562241467
    0x30f03050d020301180c08070504150c0506150a09020414060912010504030819090b0f1b04140406050102060402030c040f0f0203042a08070306020703050d0e0a05060a060f150311 78
    0x56621610b03074003480070b4004100b146c1024842c007042c41c4641045449024241c0300d0a00709410f103c0d264510556030f24400c000d01601e040d000c13000c00d0b01004034507c684075210a6034110200d0708240100206c4503409041091300501c414030a00d040e450b81e44c82003030425a807090b261010800064802c101d59130f502d1303a05520380030601040c1988100030900c41e41c803071490760074240400764000007180c50098002d88200e68407000305120741c115100c040d4111018514100100034000520111680180c0c0585c010f1010308990500500f0b15029190081c5003d0025140350b03e083d4002c691904034511501d0303c25651061103810200266001c070102d0340c01000115100d19007032902c9020900c00c125510104034040f00d5000b02020888480307416500303544090840d2901d190344241c041d402211b011418850700f40b02d01d1840b0b990901c190351200c00c900d001448010f8027420b00c81d081c0340300501218003160030081e0500910140e1100d5100712542256030345542800c0902c110010241c600110119243c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 562243965 1250 562242715 562242719
    0x2403020d09020612040c0f180f0b1c020a0608071211041d01050405060316060507110d05060a061e06050d0609022113170904111b060f04030504030f03050d020301 71
    0x154104c90302c01c5101e40780041103191030740f0b158000d0300094818400c0072071042c01058243c0506d40c00410703415040c0d603000308840303644c01c002501c100c0d0a20f1503100c240c0c00300c3c20714606501e06108801c00401300c03414079840740d0520300401000000035114590016881ea10310050300b0140030300721002040f40c00003025503201001041e0398010006e10945200b00d08210114001d49404140c8026000e11845400030b098640041503072260070124054801c114001721132a61a103840050442407841803000d0007440c948448480d04a6003a5000301950340780550480c1f80121464020209407281402e03c43c0d01c60641c480c648d006804690000c022903400400c5620140300034000c02c1401e15141401515141d643c17001c420050308108002400321a040f01d041c4020401903001040d6140001c1c2003c15002d46a1481c01c0303c40d40103c5000f41d0740c0790350354604100c000b4140000c913084407103a000c002a60406880082050295001c0606192640041d0300100750142c1d00b10741411040a109544070740e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 562245215 1250 562243965 562243987
    0x4030309031e030e1b010807180308031e1005150c0a211706060a030e0c0315070f170a0509070e131109100306050a020c190c2403020d090206 62
    0x4401e00134040c0d514420b0041d2a462030034000802c82c401401a562a4420b41d50a2403ca0703208a448076010811000310602002155041c801917114800a01c4401c03542d84a001900b04445401800c500c4001035050041c00b15a030341a02104103402591216900d131814025858104203c1900c024501194400c850300380e03d400200d00400c0715a25240c01c1080c144804460302d01503400c1b281203601c51010004078100383d0107907000032400581e080403580000d06090220b4a00130125900c00200721320203081044059000b01103460114451514041d09070300f090303c1c00c2c00001e01509002015440d0000a00544420407001000b400c94140d200f249040c607000ca0462400c915205903103a110002400502e03041807140c1502604950b060078451900e9501c81c480204005001c00d0040b0380c080069800802042008000103070010903e0382d041d54040c42c0c51107a5686544c000c403500d4019241e1504003800c802c00a00c1104450b040269039011181c54150040c050f40e10b000f540a280072802c05042 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 562246465 1250 562245215 562245221
    0xa14010314091b1806040203040305040905070801170d021203043002011d062a0a05090a0807060212030915240f031906110f130902070b04030309031e03 67
    0x70151080f080500840fa0750a206900350404501c1c560500e450000ca911418194003c40d40b05019140150402d42c99074800f41c2a11416201400019840d03401130000614802080d001107840c24000d019180304180040d440c2d40d0f503071070011960900407002400b84284c89440e00d0941c0341080d40b001d100603402002c0c00d200c00c40582c40000540c64000b0460b0f0340c90b40841040c0824030803000420842d0b4808043c13000b4160700804154003942c44210300c98140c1c4031200074058000158403081d4076126180140301c010003555106c40030540c020f0741e04001756030b00400d00b4160000d03110481540c0b03645548100d86009840c114030105c03242c41d07030304004883e10001044c0b4180090001041e20142d2550100b0800c5080d950200358140c1024030f40f440e4403810388907080e05840c0b01b07200104410014440410040d00b02504040d03906200041c0180511203071003d41019080c00c0200318142001038450f13481c04003000700002c040c150703100080410325000301403002c001d10f29001e210068a182080013405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 562247715 1250 562246465 562246483
    0x5090906010608130b0613092420070b04050a0f0b0603060f010f05040c1106010305011b030204030c033908072c0705040803070606050109050f0a1401031409 69
    0x5420500407810060b138640c3c02036102034102c1d842822984918040100c1304001c85480705509035564a0329001550000c070600306200c481c0f48003200118080f5280040d1100395920309410819070752440000c01c00c1e1801d417001960400d44061235a552890301600c0e000d031000d0b01509119540d80d01c0741c05c0048840300030b4402c1c4025001c4e11a00c0d11007070205203440f0000e00442c031031400c400b10700340000c0c2060b9000c0556a0003a1411001d8802f0724140f882c10040203030801c0e90185d4650511806403498221700400d81c0d211860114605861919112181c8941307000051803089070840072030044032050f145003001800d9040c80344100d09015905500230b40d0074410001c2d5401001400150a000b1000c541701481c03004c18038060940c08030702083c81c4910003d210f10103005081c0008100c1d020b0800c054034a45100756000110341d800c000014000c01c420381d02035449070503030781020003464030340d81400d004503160b0600480c880782d85000141c010748208041268408814000c20500910000340c1080c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 562248965 1250 562247715 562247717
    0x40515010f170f06070509040f0e1c080c03040201030b01030608060f091b090a1d0313090605040506130504110d0b1006020c061209031606020d0c09050a0308090a050909060106 77
    0x300011400b004035860b580030343c440600507001a0000f41c0f49034007800041034219070080001440d580180c123032034211340c4501c0386180541e000f000d00c0f9540400079030743c3c10009011402c0112007031810490107e80b5100c0148000e04040c1c1b1003008400d543d0090b00642c000c0c2140c1000d540040c50081d50b01050003c08462800c414480d030b00e440c0c1905e51000c00030b489480400b4140d0045580d448a0480103003803988500c28841084d0300441d02c4000d03007400035003001c480130102c03400381910380614002a204260040e500c80c61400007444220381c1c80d00401c048584c0c03501e10106069850381440303c24205403c3c651034100700440d18100c100b000701c90020740704001003144132310b4154450400304d96810300320010f1500254100034045204514041e26640710010504681c03400034540c09480d108006a001203440075008543c8081a09042c000c00c10021101c0c0381c0102c49624000000342240814840601a10400102a201a120003107500050100030b858102d241c2814540700360307290300901c6020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 562250215 1250 562248965 562248989
    0xc0222090804060507210507060b060705030708030a14060a0e040303061a041724041707060509012018011206080a03140702030c011b051b100512070305040515010f 72
    0x500f080c0041013014804407000e81c0c0d85820050103903149d400a21b022407146500072014032522000680400040c10158403c80703241c0d441e82010b607188800e40710424602c0d280d003440b41c1d082092640300c241e00c03281150301c0140b5102031503e6504003030380185019040542c06071422034801f2036040407007004000b283c43c1c84c000f941d0a450081003103074a43c0240d0095a074200f40e04410302a5944025a2498010380690420300c0d203071005001c50182d0b6071042c0ea088400644403001c12052501c284200514040050720110303031844030310307c0000d0380d100d90090008078100d4081c0c410b17050303481001c810506802e000703c00c110b400d4581041d15503c1010110403400100ca02040b002d890000e1010303903045660280091904001200c0151130b0355202152000700c01c0200d8440c00c3c003090f410840d00102d0304403481c1c1c0180e4500503406014602684110712001d00608000307042620790740c0082c5585c4076025240001d010345a5103003860030094000d0300c6200c000b442c1400401d88413003031502101160014070682c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 562251465 1250 562250215 562250243
    0x117061b1e03061008100303050a05120a050105040605011e032003042a0b0d0b04020d150305011d0601031202030403050f030d0f0e030d0915020a0203030f070c0222090804060507 78
    0x4072507000c4c08a403428030170121b010040001030300800140031840342d030b03003000b508041028003581400d08044500030301c899214030040005040910959000d05030a203042500124a4440c102c000b40500300e1640402d6550341d0301d150407180305500640081c3c1c1841c4003950b81e013031030305000c61310300300c58115100040300685003014810440c6461004848800c100a0308010600301c1e42001040d01d0304526401070340810170b445641c000e5124400c41e1315140240702e10940d0640c101103003116101c05440c107600c403544000070b10701c0200054a6044960103c040400030038001c004074298011580010098400c40d80300064880001c4013800040745d0310001000394801c00443c520588442d08040051904100329091a03031085801010300e00e4041c41c1d0500799820742c0c08004040743d00121501c001a0004000c0c803010120206d0307115048038141c43c02c0c041c00c529580019124120fa0079240c400c5030394110030080b40240c0358000c0030505400140381920f465964401410940c02a00101c4a080c04c2e04d0310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 562252715 1250 562251465 562251467
    0x182e060501020627030d02030a091502031005120a24050705030103021f02250504060909020a0b18060d0914010509070b0f0c060a090b0117061b1e030610 67
    0x10324495165600e55041c902c500003801e00513400e00d8840542c2501081201010f180200d000944c000d07802080d00041c4900d240c01c2541002e8685180307010380ca80104144400803881402040945104071804d22025800d101400e183c180000030042c1102c82000e440081001c2c001c14079003032615580020300082c2d8030508102c0e200d10003400001e40c00b15000400c90260110a1041a480c690b1801107a0b003059040120901190001c002c29002d68030700c58090200b824240074840061a10480c103004641041d40040c644a60740d02501e140550046060809422000402424042e01403c003554410032102e245001d40100c074011345082c0c0054840d1501a001481a18407a90002000d00907090415141c51019070044d02d6480b50400d0a018442d46402d0030711400d801903004400c0061003032640c0c980015001c805034840100b20741c00c14842e4a4044010841e141e00c01d1a904010820407c108010500d6000b00300304440f65812040c401c488103803a00005501519049809580b44100707848 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 562253965 1250 562252715 562252723
    0x1112070209070503130c03060501150306150c02010207090203010f1406032505120c030603011b0806010804021219060e0703030903080306040e061005130b09182e06050102 75
    0x54001c0d0081100d0300000e40807807165010350f40150380503c440c501c1d20580e4883c1c0f11003400d1508141c071102d9886004118100ca050703a02103090702c2904040c40010710f8400301110040303001408105000c2d144151004580c03007030043e07902900000702d0840d12540c44040000308400d890180e10f002909004010443d0f1829405403403144c09603007010603049421016400941007200300308401d200040c80240c0381e10f24212510340c41420941d00a540b00d03d494000c25080d10f4030441c506d0300740c8a04486a20308940d00c032510503440b640c00c2c02c2c405d03c01d446505c00326400c051101c580184170702030551180401c0c0b003e11240c1140c2e03400b6920a200d0104146c46a03511000540f100a0100f00341c07020070400101ca20025680c0604000c1c0001410003070079504d2414404200d4a40d000f100c0c0c00780d014040ca01d0f01c00c031a810705c1c20344184c0400c41200320f0400300309603000141100010030080065030102d080100041c08040d40c0d00050196081204000700c1d211711341ca804031900140c145900821503502c002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 562255215 1250 562253965 562253977
    0x12170307020f0c15093c10080105030a030f0210020d0f050105061c0f0e0a0302060403121506031a0301150617040c03140a062315011413030609031112 66
    0x4440d442d280d030200810110803502503004040f0500f60b0030090742d0100d034100c5055406482c0a455000c24448020803580403503847d03906040c4400306d00148695140001d410786020b83c035082c95012410300d0350091340380031050a0340b584518000140a40c010080340c000e2082542e001c1028485a40c0316003c001c01401810004900d61012182e406e0f0030640070b0b005411404455000000c3c91841c90428070b0500016142c2034000d80d11030700602c0101a407180741010741503d003010030040031420807181000c1040c54801e01c400c16455503000c2030700300b042b01c0300103203003400060081140b207107e042082403003603262040e100418124400411041403032801103110350b174440724013440300d4110703503881c825030840001c8518644284d01c2102c0015845206155031100068030459004441c0f0300a8401d0040007054246402030042d0301e40d0050742c2050b002685070b69008401500e80d9005054142c1c0b0345850703031010b030007141820b500c041415003043e00c5c14840940e4405030b0b821803d140380c000045200d21 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 562256465 1250 562255215 562255249
    0xd0915080c0a0c11040e070303080a050403051204051f1b050705060115090b03090a060506190501080c070510020a030c170403030b0406151205060a0e0112170307020f0c 74
    0x10840020340a02c0349080700c1d00f281c80f5490810034440e00c200440d040b1506036403810310320782c030100d0103000381604417078803913804510314505000300d1810ba17031b004201380074072006044418114004a020000148010700804030f0b8800c80c90341000480704e0810147c0159910003441801c8244004101c43c4a502210b42d00d41e00600202226441c01c015001c0090002e0994420440c0f0010302150021080c030041d401440d00070010103140006042200480d0b0000d0404d42c8114200d0903c45e000315150b10761081201c4003401c1c40d600030360b01c515807181c10388194040100203000c1d1b003052174844200b1f54040d1002030b41c696010004214005401c0d03130301680752202420001e1303028000500086c429004401588005000800c0907640c4220b0022544024810300c80480c003500c5100c00300d004680705160340b10380201e601d031014034900b05200b00903160600a010118811600c042c05000c401050001d400b20500105035031391804002c003e4466201c0c07a0403a4441c01408170100d0507113401c4d54114041031131 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 562257715 1250 562256465 562256467
    0x8040201261803090d0b0103053a1b0303060806090d2c04061217041d060303040f1706100501200c030118020a122103060302030d0915080c 61
    0x10b02c0d01c4021100091858142c003480100000300c81a101e5140d5103d09501c2070200c06165415403802c030b41410104403034044000c00c1e0a44003101c04010780074001031400709020802800d0300c0c2c803000725650300100c0f00340816055000d04503802c25515601c00022644004183e5119031a222200c540341d09003d111040000c944441c2940080380312040340441084d808403405120014001003070075100194041d140ba021189844411b1207400b846082d000444202da81d40303803d0034564150201c44800040c007100190800c000741090720208201e0b00500702c0162a4032115a4030014602d0f01e41c1c2072108a4205d00a080c0451113080d41340410f08251941616414607448105980c40110017404019401c2446200c0c011801900c080c81411400710a036030306480c1103c01070051180c08071080d4031034400000b6041e488808607003e503902c40c020844003842010340281e40c82d0300724080d01c140e4002950500801c0c0210903400e0b045592203044540300443c00150360f036810420380d49000203c139075118002e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 562258965 1250 562257715 562257721
    0x305060606360a06080708090f10110403060609050105101b0b061305090303060102011107020307090b030a050102161401090c09020a0201020f04140910061205100509070804020126 79
    0x803400b0a50a0040e031180300200c81d4089100000c44440840d4005408a005442800780e4640c0c413400d515405080e50005060384003c034424540c0c0d1b403624100d000d81a6503110700c2c8112100c05042145c00450b00101c00744005500e8070700c1c11004103020b10800788035900802c2001565801190304818038451041e0790f802545050f259250001d100806d0198400c90140c0c81c80d140004522810b0701458902d802181c80c0d15101001a08441a89800c02e400700e400340203100050707030009081400c0d14001ba0000c1a9283d00e01c012031b14110091000a146500109415000545026001c05082d0003441c0000381015402c072003178200c2ea1008400307480203400c00f0301440701c82844d400401d0030418510005140c5055062081c0300c58200b90481c0b411018041d48070038181c81c1c40724046800c1001542440100e518048029001409400102c1ca4048c0c85400280d0b549031a1110a801494050481e00403454a1440244003450490f002ca011404151080744140000d400d500461002c2c4243e46003151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 562260215 1250 562258965 562259017
    0x103150f05040c030e010c021c050705031b01060e1932040305091c061505030d0f030609050a0f05162703050307050319031112061809070305060606 65
    0x80183c0d08200c0c2410b07240e0460704040b84092103090205440c0c1d0f800392038111020341040c0c4582801e052000100b210500103180407944c044110b600e01426034802c480c90302058520940507000c00d9100c40c00706581c0c04100409481080302380740e9000146a820081124913080070307000d01a01c1400381c855141e07248140100707542901c0d00c20b0703045030003030410034104880c040020f981000c9803089101103488900400003046602d004c5c5002c6402a545178010709402d00001ca941d540d40488241c0800c450901c00d42125402580070b50301900c841e040c240a03915042c40894081e1072980e0301c2d400c10515000000301c00001031007544800302035540c0c0c2c8c0345218003131a041004445c82050304250404400c0700c00000900c08100500449100b040699200c90460841f004001d1001582805044c100442022071188003411030b51040c1d1040300340c6d00942c0f205000309207221018041141814a42402c1c420036403c00030b015400c50707104000f1141c4980c3c94109100c140e00800c0c1c8601a4483c3d2000f54207828 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 562261465 1250 562260215 562260221
    0x3040e070c020f10030b090f0411091306060b030105010f030b0310020d112101090e07170102090a140a0f030b04020925030b4b03070b090103150f0504 66
    0x34a0008208200c01e0b000b00f000140b00e0904050100082551500f020010b402c1020743d8907440b03090345e003c0f8035242c5000e0301c034444050000000188104840400195110007003e6182c81c21a0000c2003089070f40d0322411000c0d15603100303016160102705008030b851011842030291004810016000e046504421086040030390008905e00380101d131203800034103a89410001814800c60308101551700d10610a82c54502244180c0241e041203082920310b000a55002800784102c403507200c1d0a180d0411030b200c0083c020b004e04201d41c0e6010b6030801e03000412440c2c40403407601d018000c58581c0301650343c0322900c01c0e10845a10000703006c0054078001401510f003151896610040c04144030036110783e881c805a001a401200c00800709580d00c0c402042800c2c1008080e01822032804030480200c0b15032041e46803020480b40029614400a000e508012064041c51002c400040c084a5000f07442c1d214009442e000090b540380001d1a01d0100c00c0c00212816a400442d481c02c05140d01503800d10040c4405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 562262715 1250 562261465 562261487
    0x100209030c120120031e060a03050f06090d1704060207050109050a08130e270f0307060204210f06090602130b0c07050301020a05180d0503070c0905010803040e07 71
    0x10501990080304401d8645503011107226042d0400041d8038072000a01e048000c0c800421409a40d0052040104020301d52003803522103106401003404941d01c010004c0d480071015040144140a00c1891300380904000a2036402400100d0540d81040c3c4e40d01d5044901b440303100400d81c00e8801c0c250100c0c01241440d8000c10546000d140003003442c2805485052600c200d002d8101e951910004100725010044140d000140a040c40080d10a051070340c1132998400c0620094040911a6a401600400f04100301c800300c1480505581e1945030034280365000750020b200b0303110941480400087c11003104903070041200c0c1e02c491070b56212030395502e40400400660030200d4809900300003c80303d10b00c00b10003205c010311000500310713070301d40a4400e82810041075a20640c0039070b0041c045132212a4010003500c01d8070303800900031640008411f002034078801d4814400b500380d010000d8001e00740100d044a08064030460360040c4400d980e42d03480c59940f07210300d11400082c15080c001240354244110b0070014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 562263965 1250 562262715 562262719
    0xb1906200622051c0c03020d080c03010b0306130e1e060405060705070c0902040b07021009061418060732101107060c0207151b23031908011205100209 66
    0x6405a41000070001e42c0e01345110740b01203000c04000404241c2e04001c40c40701100940340001c00c0d0708050441c035076640011300501c4054800803002030403035121003035418079004881506210a01c181044142c86850880c1d200c400445e001c58406626900040c040780a2f41d449001010203649540c402c641503084000100c03400041110002802416030014001400244600c5d03545d40c600d500c100284008180c0d44003083c400145002c1042a8110081040c1c03610700030303c2d8a0b6544201b89004141000da501c070294803000c0442e0f580e00f0300844041034200e950a0013084490000e10410740d03542c04113040656651603001c28800300120482d600712101e030445620a05017012800d070780f11416144034000d00d10040e80051000c00031022031607981c40301d071032103030a100c1c0070b0701410000802964808003010f02100c902d0080c58903001e000c985414010010312090f651541031200a0f03551103222182201f00150441c000807800c5881052988941a4000e0042c43c0141d030100003280a03420052090b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 562265215 1250 562263965 562263973
    0x1e0f0f0a15050306040f150303050c07030b0406050405060606040819020406031a041226100e01030609020f01030b010e0108060312180a12020d060b190620062205 71
    0x504a5490400c005112210b40342d040c0c9034a010000d2004440d202c070b0741c2100d00c60400700700f95a60388024600300b00741ca400d8500346a581122110481c43c1241c10ba00082054110000b0002440019480b2030b0081d0f00c9201550000d45921080046c1c0740524051310381b50340c1045aa44c10040c400c5020480c02500c06007001c662544c0da600e030343d02c102c0c16011381248001c08400410003081384000d100415031900e82004200c07040729803a20103442800315111009149501d0102d14811a180704120003032481c940045100e6840e443d100d400340c030150b0b401328002c10303400b543c016456012303010b0302e206c001041e1754100b40c44c03a48500454103050083d21003030300742c05014245110781d8402d200170140500b9102e1030580c00d1030cc0500380075607194990b010148054400ba80e1200503614212103100b90341e00810085110301941c00096070508211002c0050416218000550150440c07405e5030641050303d200d00c41d0304000d442c1251541e40407030310008a8841c608404640071007201560004c103000300101d0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 562266465 1250 562265215 562265219
    0x207120611030405030309070f0f1a0412030903150204060c06090212101406180c031005220b0409051908090402070501140907080c0103110d1a1e0f0f0a 67
    0x1d070030180d0082c2d5080d115908000308102c0b0100d41001034400604010844402c8180f400724036205201c11400780b809010b15451300c110140d0800c4c03080d5030161581c0043e511002c8807628000d01500c005210454065501c48225807541c1061300c01d440480c4c2c1d8641340d2807099445c0d5913402005090152040f07034031250b104031040e00720702d04006482c2c034030b41c013030f0350020382c3e20204c04082902c200000c103c1441646010b0080d80613042c0c603074050740c010500c0d401d00c81d20783d1280e88640c10140f107150001a041a039104005406120703503410f07036050103101807007008510840c00501042c0c0305401800303050313030384115480c0503250081800700d0b6406024003142401e00115000003030a0742d01042040ea400e0391194803184890143d4118150001910342c000c0802c6403901e2805511094011005414956183c0d5141140b008a07000c0f82c40401612a01304021044030032100010f40040c814180106070156141481510160240e521240001c0c42c401c1190b040324200442152000416a0002108000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 562267715 1250 562266465 562266491
    0x903010905070906090e06090a08130e0c0d1d0a02060904060e010f0f1e051509060a0f0f0201020a05160212100903080c0a210e30040602071206 63
    0x1200241c030f502c68002c607050b4504407400003510754080020340c07242c00c0740040c407005010000c2c9284203503a00c10051902c03070380761030f01340803152615600c41c13900d5880351f03000c001007044000020605c0341c8240404004042c0b10b40030a0182c0c00e00b000c40341110398401c0d00320700003528040c0050444020010301c00f107002c43c0c03507070b001c1020b84500380c1c0005e00340c8040040c01d021500b0064006006012543e01030a0b9081035022040101502c600c6418015001c407680c0e0301e8550100320031140c030380d4000707403840381e0f11207864000801c103c98485401d80085c40c0110348068140c418000c640c0505c9e51356541c1c03030500142c28158419924420400c03a440300030fa0742410010740060054181741ea00d0300500207074203001d41c14007411040d4000c0040642280c02c00424481e960001c81c0440080e04a003180c81c209038407800b140c4010003003220074021a00c2090007031044801c02c1544209040d031001c01080340020500c1030003049009600607075015811030202400009400e603c4000e807140101c4000c50100e0f42400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 562268965 1250 562267715 562267723
    0x3071b0f15110c031e0702090c03040303020403140a020909060c07060b0310060b0a0206060d0803040f0218090a0215040b0915120403080402090f0603030406180312021c051801050903010905 83
    0x6103107403a54001180301004111740c18100348820040307000c1a072400701690300258404000601c012241d03940440840d040c14400c1d41078401a56025420700d020524072411140e4450b05400100d10454120000071000180482c180c0e008030b400b07002c858140002030703490601904220404607058450001a07540131101c40c01440c0042040b61000c41e43d542c80f14030000c3c00e2240c0240344c24000c201d9580740100103519002283e0748142c00030104250030b5043e1001072194038400c62114000d050100a022040308085100c04915208590714800340e40901c41196250049220780e00881e0303828000a009802c0000402c19402c0282c1030003803800b1108144440c00c61800c0e2030540014454078104411401c000425913005031212544001c0c034502100001e40c4da01c5140a003c0c100046c0742c404400a005041072000030710351101000010f070b200e0380c2000b0741d00e05442d0022015000c80310380c45a80a406003040f109400605400f40c49050400e07001500d06500c9026916010341d6612100c2e804940c3c140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 562270215 1250 562268965 562268977
    0x90b1f1b0503131706010f090905190c050f090f010504090f080f040e09010b0d080a14070506060411190507020111150105012a0b0c1201030803071b0f1511 68
    0x2001a00e1031070305081d6110444034854004c00504e5121900620040d4070000d55401169034031a40414031903013610703005081101403070740082180100b6148408104005402105440041e0303103042e1080c5400040060a020030b0b18400d8040312902c0061000c4c6c20039810a013129030065011070001072a41d0394003611a413240c820044480c4003c54244007195000c038100341c101002800038083c00c80c00c400001c0505043e030000424880700041d06091090040c4145241080b860341d4503031300c0da8010300740651110740864001d13100e2032034910250404140441500c2401c0594150711489141c0d001702500d540c0e00404041e41804040c04000c403815404100b521002c0d02c01300101030b42540341c10005404509004034054008420302030011501410300d114010454010390300c5101e54461900100062040d10321020910200d80004802e220400004500805080c1c0d5420843c0080b2001c020080321301d010010714882030801d80c4800300c1c071110031888920030180400207000d46d02a4040d0810790041c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 562271465 1250 562270215 562270237
    0x30b1c1a0a0e010b12060f1b0d060f09060b1b0a0804091b0201021c180b010b04060e090709231c140606010c0f03020c03100204090b1f1b0503 62
    0x240c2e000a00648203000e1809095425681095140c911380300e140c0d150540207100d0841b030600c4500042d100109045030003685070301d03000d1060b528007089510101030480d41c02001103c0e6100003000410a80501c507060888041c10f01c20360510b1030022032400c03118040020b0070580e01ca0410080041968240100003c00d40301400281411000d20f00024482c90800f113032066900c18031110b1a0101300a00500c030036100741d000000d0900035021a64a808048030b0041c040b0340c1d14500119115000200074015107105450302c0224040300c100704120700c001200c0a40020340702d42001c2080218110070300400702c0c4501444400401c00e60003041410609942118841202c41109014090b64100c184071501d0100090003a5103850320000e805003899000c000d041c4803003400b2600905100784145a40342d10000c0545d501080300c40d012001941150117524101c51400301b1030307060751400a8003d0f071001e00341c0340000c0d00041456826940e85a942c030500780199207002d03e01c000210180300401c40a101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 562272715 1250 562271465 562271471
    0x60c0c0f09050f1f090c050d02040e090f0307020609010503040602090d0c06030e01020c0c22060f151106071d060313060c020f0703020415180b01080601030b1c1a0a 72
    0x4000d050101c0d042c007070030461303d680c4003195140603502c039505032a080c0d6500400102c1e07480d846641c11213440c440c0c2001c00c44200d1021401144444440014130301a85840048a54040ca0f26804686900c9207600080d802641000300c040e440d4080c07005035a115020303442c0103007001100360100346d84000d082003c69980040c4ac0d41440b4582d014860040f030122400021428480c070340b1006603542d1011008144644002000001c0da00035012049558511002c42403160301da07550712448110700d80f400341300c0d0000102003140485500c00e01c07220461040343c0000b4911a100c0201c241c0c1c105450340070901030640101002115a1240801140116420440307100c80407181c1c280f000031542c2d40c842500864104014050154a0005440b02541e80448002034401c40e0701c40b202005003041d60191080503c8075916104102c1c0710340c40465069020b80b940792003680c8400046044400c50042c0030b83c402030309060704881002406202110900c24034085080400b080d01a00c5846001c407041d11625032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 562273965 1250 562272715 562272721
    0x1b0306021210060504050d0609060b18071b0b2a121902040305030304060b010e101101050a15060318050601031b060f0c122a2604060c0c0f0905 63
    0x34400b0005008181d0b900c1d001d400c080c24400051003c0d601403401a0a090301d640d40c010034044160702002056500804080741d50702c814503d4070300000211081004030360381d500408148901038404a05507503100d0b14111695840c0003404030740d10b000807000341e910b820b074848045035180040c008144410090745641624500071250706c440091a8056010250041c001000042c0001003925000780c0c4c071140202d007450a19004071001500e0014a0b80c1c020410004c610f00544c02000e410401c50030b010090210b82e81d4a01706c9000e4410203c4c210040c0c0900200070000544031340d000c6c40d821803401c1420842c1d81e25a807545442d0000a81059035610001e010090604a03182c0c0040c000307207800d09050315100560f40f80900800483c0401070580e441181c5c41e2910140b03d01607400e010b100c00090082e80310721811100b0660a05444100da0542c0d4100d4001c554032401c03160051a900050566490940ad044040f0380c19102c081c0d08480d4400c00d24000715400d00060800006018220740c00103142c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 562275215 1250 562273965 562273981
    0x71e090f080a0302030403290106030509010c08040308060609060403380c03010302010804110405040803070f0206060d0609031403190c08150919020f07020306221b03060212 76
    0x1100652207034070540c2c4042080400070790040182c800301c907000103803101da5010f103600c410003072485503804455484000d400401e003590194416070241032032500801c031000d1505020307526041c090724042c010036121000102c2c540b50400041c2a040d030050601c4d07060039030741d5445000005c0790087c10101c0e5803400c0261031895180c0e078a86284180100083c00103828031004000e52480103000c0a030400441c480002c040c00b1405080480741500604100710700c0c6420304103803442d600107440e40c100082c85c02c0f8035668002d200155450058400400100e0641070503594103008044d4079000b10103110146070800c244070300000107584101048a0343e10460302220383c9400c00c072410514000c06105000d010b000d82d03451180d864642d900d50030b48803d0000e8442596002914651544198240e03000045140b0003e1004020b00a081c1c400d4003281c00b5a00d0b0719000e0005614081203840c0702c1220710502e01c001c0703101046c81e40c140d080301402100920381c580c0c41d40d000b41c3e44800c22060341107190306d003440600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 562276465 1250 562275215 562275239
    0xd15170703120c111903060e0705010912050c09070807031104151d03101508031e16020a09090b0f06030a2009010e0411060a090509071e09 61
    0x2140400035000c034038119aa00000048800d15410400409022103410400c040080a449050007014045010b10618407400b0310722960000322600e0382084140c1c4015580002e070706040d114142c44002000d4109800c2c89081111242c068407184516401c900c1152105520a4040c0c0c4842c0c2c0c6210091404140c041c040e241d600b1a02544202c0411041100d58004503181501d076640345000b82a44059035280b503031640308816540c2d4503000d04d482c03a5a10b00305071380c820041c001800704a0110349645810090720f0340140044080c10b60b02403040720b032045800307100400c0110060224144072011503008034502c1980741c0c110014583d6200e003408140486000b180b80d0111901e10341d82c40c507240940210fa1103201100e001004a00b080300543d48803908000d12003058103028000b15a29a0341d40c2905111001c00d0f1801e541140110b2000900381c100001160035680543d110b0405032840c100900c2101500104030004000c15000d40c900384003810f00c0040c516442c039035101504541000060360103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 562277715 1250 562276465 562276499
    0x4091803032711150408030703030b180106140c03040617090a1e110607060b0109080a02060906031801050c04050a060e090a050601020a0c060c17090d06020903030d15 73
    0x3254a41d280601030141c001980300e0380e10f9210080d1400d910010002c03070f242446030480c04d240c80320007250104080200101410103a40640d4007400848140014419040c00c0a2100c15810280384010b00c2894020b07204407001021070b45c0461b01d02110240e00500710b42080c0c12600000d1620170102e5034030a8100a13035600061a140070f401c0c0105e8580e500b800c844890551852100a858070076401d108425021405408016201982ea040549070190050444032502d42c08030746640d0300416114400a0407004003a07015098900d0502c0d07850400405400007080c0e011200c40312101805100c1c02801101d000302034216040391240d00b00410001c00f090103400c000100080c00c02942c14a5076541451a0001495000010300f500c0e00c500403800c0020444020b02a04284800000e8080d4003000700300019014500e81c140680d10990002c40301e12480702e043c1d502140307a030045e1000c903040c0d900400c085c00008007207920348141a5032a03016070304041c40001d9503807071803103013085450910b545e0196 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 562278965 1250 562277715 562277741
    0x3140a020c07210b1e090d140706090204090303151a0909070e10080106031104060e1216120614060307140604030c0e09010e161a0409180303 62
    0x414824a2280c090340c905035403140c0d0b20b6481200e200400d2151030760a402d001c841c1c2100b006001850200174541070f00341e03281c1903400000ca040c2d0000341c440b140892140086940c540c0c0b110444070a01e045040c858000c03c40a4454075071ba054600c0c01641d8920818080f50301c81d03140892180808887d01000c441540e00c002e454514200360f074a01040008200d41510004441e0405a5200c002040306c25018207000142c01c200d000e00702c1801d19800924050482c1c449603014400c6942000d03040006014074070400002c01c1022480074081e1809071050005035840600300c400c5229052100f041e078441c15400300e00b200c2050001c100600c90303540a0611900d0080c1e41510b22400e0450210399102401d1140d4503e864401041c0e01160751244200c0300210b030402a02c4600c42d4842500c00c4500101340c601d002d6561a20314900305500c1d001c24081450044540d4a240c0301e85844400310850707008041d6520410420003010410040a1042c106811108107981e10040564903016081701c01241c10703a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 562280215 1250 562278965 562278967
    0x1030b06031005090c0c01090b040c140a151e030e0c030a0b010e040501020d1103010915260a020a0b040e0109021e0a05130602010b030d0305151210060603140a02 71
    0x4541440c010304a04201c0f28191035141c0d41d0b5131440310032070ba18020070004520f03550030030090b01b042c80518207a15008a004034001009a55928002081c4d904030310b1106402c400102c1041001e9803a10000c000e200e03040382004284000060b00c0c00111200c24003800b03000c41d03952155010241c10401c045080076805400070442c4946640340d00500100500c2074401d8001c003000010308000e400c0d01515280c01e803001d82800891001c0a1039901900240124000c4900d00f0080d41a060401c0043d40c1c04c403401c0400e08a480c03a490442c1040080b005040c056151017042982c800588403404902c1c014a96841c03000d840d2420009200ca0156040e403141d18924010f001480800e241d62000c0003c5500340742d076281e5152101c45068451b03021340000104000031203180090b401b6019007010303140040881c01d840c0e0301680c0d004243d081b20070a46440c10a6060380d1680d14042c01c00038000c0218420034001c0300d0705800000c8864040d0b0303a980d0080d900085c0c403641218100240300da40b468005d078626031f0039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 562281465 1250 562280215 562280221
    0x50705030a1d030904020f130e15030316031206050a0b0d0c08040305190c0b0907080d020f07090b011e030c1b0210030b0105091e03100e0615031c030b01030b0603 71
    0x40f40c0c0d9000d035015103445207a000560000d0720543c0c008845d61444400514082e155880c3c041c0e042d0410202c91406400c0d00604140515290100481d0151061602e1b103007203030145910221a005011000241c0184d52120089501d5448000c40b400400c40d441e500f583d101321748540d103070a40e05101c2d501000e1004060501000a81110980703030041c091f03090114050383c40700c100302c0b4101076813040500140302d202c0502c4410503011414406585070382c03044910301e000c1400d00b282e86003a5685402202d8200d0b4506100d800017541001c1c051240514184601420344040787c0703000e40e14010040042076441000090f8280c00060104030209010134000014815401090350b4109000c0c4400403d582c4030f640e00c3c0160f00070740030782d0700007507002c3c080001c003c0c20b011910354982c0d0508103041c40f030300c03034410090b417507102500590078000308220140400d529000e5040000c4020007030b10303d5050040d006040b2020070b03240360410f41a03902c1d98000c1542d440d850005401c8801000c40180951020020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 562282715 1250 562281465 562281521
    0x3010e030d0b0901050102071a04090c0518100c020910080d09031a0c0d020c100606050d0f02090303090d0f0609060b18040309140a0f060e090109050f0a1d01050705030a 74
    0x404215130086003127115180304502c0440c0e007442145c103d690030901d007801100d441036010b00a001d0044890045403140c02110081140f41600240050005403800c4030300001802c00e5820550020303040f10380c08a88507182d02c102400e0121158094001500ca240c0400038002c224034000001944100c0c0442c0d24108445c080c200c03486190044c0303041940020710495100010010081e460240b100d04008940d02c90400822590102c444001c0d0641400c59a21503c851031088521483c0c0040085150021040a012008511210903101a1848144030011510074043e4520300742c031840c0300040380b9100f00204405555800c90351303241c3c404807504100009410020307840c261004d1500c0030600c5003520b00001d1420a0940000d4100503604500080444d04010f01c140105000c40302c0041e10381c6c170760030340004440d800c603070201480c00801c0110303091646941c031941d418040001244841c0d00114115425a0390503038004000403000010000136440038400d20004050681410b1651004010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 562283965 1250 562282715 562282723
    0x6030a020c0a0c180b0103051012170d0504030f030b0f0405091204030501061502030a0230070c1809030903150603140a020312030c07060506030c03010e030d0b0901050102 75
    0x200004580c00681940540820030036034098503809400160496180c803041c40c2c1d034403505805502d5981c101100d04403558040d00880b4450382440b83c61f0b210321440e025403940c6180d48424140d0700601580403c50240e60110300420b8209015100820b140c20145001004604041c0107030040501e800c4802e64076a80752656014038000880340400d561322040c0c842c40c181003d44031888d100da90009800001c0102c1034000c03000301c4800d2014111204507010f0141c0c3c407880303024030941c0140c110725801e803d440640b5801c1e010703202c6007103580030340d000500d22a000e15501c4143c0681d4030a441c294100140f004402020703111242450041c05020b90320383d4082c1000481c3e000042409140d0350b034082000000d6408800119003003030105081c6a00302c0041c0b9182e585400c02070f40a40100031104401e4071106040781e0250b86c00d1035030103241c41c3e4035440e644018540580810b9040c021181591000e940c24010841c0102e18a8081c6035542e054440c10022201c04400590107008090010005d03070f81c0103e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 562285215 1250 562283965 562283971
    0x10f030903050d0f06090f09050d02121219110c060124050f0c061e01060207030b0a0c020c04050c180a0815090c1c030206090f031603020a3504050603 66
    0x103c800701da826441c002400103071074035410203002d0b9440c1003001480000315410000b601c03070140e026100d03800400813080303072105029640e0708030084080201d0040640c0781040350f548400700004240552480031160300541d100504500180300000c08c82e140f01c0d41d01441350034010494604103a5680303c4000b600340306615510880d00606c040412035008a207010011179905404c4034090304c0051515040b00624440c0302e8601d400c44503ca00300208400c1e000168013015130742c126010708002d5881088260142c054084800c085004e00c000e402c07080e884074040d00f402406d0291000703440386442c112440000e010110610b2050080c00000c00104034082400c5103506025030184000e07a80740b5a000e450001c0040c903031a00442c5100c1900d081d181040c0e0b0003000e140c0f10382e0030b550658444881090ba540740c159a02c1c1c0d82034004010200041c00c4040010380031a110340103132900c0f03455549903281c0114406c0d0008200c070f07140058407074201c0740508031070300160824105a81014240710114034140002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 562286465 1250 562285215 562285237
    0x3030d0f0c09151107090e0d020d030905060103020405042a0501020c0102011a060a090b07111c05070b031305191a090706031e02030a0b0a1203021f14010801020702010f03090305 78
    0x134124424031450240171004c003800051a0502004e40c0280c0c3c1c0c569200580b440c03800040c02032610082c10303140b003400b071801c150fa0044010481a401d5070200070041802070811140c101140b04d440001610803011085a80d001d410019500d43c9000b0001e4201a0382048243c11a4504030701c50007851002c03a00300c41d01c001c0c16101c2c1910392001c00f400340c44000356030300807059008001c2002e0040200003191640b58840a4454200455107060340101d0040c8201000740079030420f2006114010401010f10b03031180782c618100382c000d071b03680e2505400e103140c1c0d002081800310ba4080e40004e018034000003464003070100c070780714070f1600d00410703516118130560040408054803211200d941100b4904d1007182030000c0781085684e41000f40a00c0c0007002d004042601400803a403000515222407601d0104694041e0054280108242400410300005032003003a8290b60b54003607200c201c4011400c00b4064850b91000580c1d5610314000501b4400214100e4410541042100300000f6800f005407240f190345 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 562287715 1250 562286465 562286477
    0x31b18090506040b0a0f0f050f1012110a1805030609030a12020d0507080a051005151b0a052103060a14030c13090b1003020105091201090203030d0f0c0915 68
    0xb80c18001400ba0500c000169402821060003080c412605042c50086911101d01074100035615001e0000c20070318a95801c0e4002007081c1101c14a40c081e8600c4200d0804030b14000a13445840d20f1441d07130a130043e000340b10020303c03603081d003200d02840060030b000501000c80c0100300381e18244403903981e80d104070120a010440a400381c401d45649580503280c8829165109004525102030000c140e003904403140e0045605020108140341e000e442c1203800d80d10007400001000c80007100701d80302d0b9481242c100b52074403030480415488a0041c40f01d5105c1601ca9000f0b0000f0102d12070403a030031404a110a0180540104140300e09599100e4600045885600c683c02c02040054002403d10414494403a04103180390360351b000400e01c543c021000c2500c105065031042d16210040054803819000003404100c0c108894803c505d410004042103622040020551500e0355002c030781150040c1c186403400e5900e40740d0f000742108079800366080c43c000f589040c45810380340c131116142e500d0400e1400d5052200c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 562288965 1250 562287715 562287721
    0x801060e1015140409020a0e0d0804270e0a15060521011b08060a090506150f07140115090506131a030106120611030403050403120c0b07031b180905 65
    0x3003e107512090101d410000141c81e540c0c1c0300000c0e8043d500c10584a4009030f042c8202800f07500d80281002e4456421807002c078142070500c07504810143d800e0310001a4668601d40a4401c1240c5000ba003814001a4003d4194602e040c45d00c01150350810f0b07100c511050401109201507142d04a95421607c00e880e02d104001119858060042c44412002580d58a603009424441c6030030521441c011744040c0c07214464580d0700d445036001c845090340c641d80c0c030807c08581d0741d00102504000c0c2c40119090b40f940303480c2641c1e955801003410f100000c08540c594517104d04121034405200e1810080c407841d002030000d07240c0100001c1522480e0410003801070b6407480e2140c885c065200c405442c0c500e014000f00300854448100c001001c18049088a22509080703c07201ea01c88a002a203000b40ea150700c40d41c1c1803504640e81c0c0a0a81d0650381c0369807c01c0799640b0314102141140c44401e00076070741501c00098610001100b0180c00302c41202ca0410701c0240221013160190407084003089944800000529071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 562290215 1250 562288965 562288967
    0xe01030b070f05070f0f0201020d020102040b0f0f1b01060e06091302012a0308101e03030e180112020a0f05060711030c15030a0501051c0f020103060e100801060e1015 73
    0xc0104139001d40009010201c0d0400c100c0045417680546000340c080341d04040200030201d090b84280d01500c22001014040340c4513054401c00038100d69040e00344e083e8101508198007960408000820000e02c0c2c1d100c580c101b01c651070390b12120342c00c078506440c03000305881d024004402c41d1804020003410400f0020306075100e800e9000c0d1440a980c555176141c2508081800c0051114000b0b5444080f8110f040f080010301c0d5501205800c05a000d50340c10102c00c91440d1070640b9944000c9802c03542042e1200c2c7c1c0035000140c00c4855901070107108058901c030303840c40c0c014481e902d940ba4000000980000d0024449591642d0035114610f0384032402c82c500101c00d101190821446210064100105a4100040408001c040c611403860a401004183c3e83c840c100041c84100c2420784a4070361440020034041180802c0000c840f078010b04022800581c2c60600c3c003002c100488541200720352041050155080038020030740201800d012980c040d00f0301f1200d51000640c9482840181500d0050103071001d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 562291465 1250 562290215 562290217
    0x5090f06010e041a04230601050d02040305010c0504173403140a021f0c0b090309030d0302190c1e03020f010504030905040b090f0a0e10021603090e01030b070f05 71
    0x40c410150060194848003441e040c8060001c0040920407030421440848106c8000d0a0105031500098142402c0e2281001500c0c01e034801c40702c04809a808000200103d03e090180b84220a00b55688558aa01c7c2100c1101140f448422580190f041001740007100400340395001c0741c1c107901c140444d050410700010700240c50982c0d40010040b412050544d41001801710391811624000d45440705842400d00100700e24081a013160000300f01c1040901000c500458840d582c800405800c8a10302410350000170b1034181c030f17201c1c4a000030350000788c1418202c2c1544034040649842e0b0400911864169545d1a0b480d4400150109881038465228060520803c25030f41c4410414008001a0805085c000c2c0009014040c082c0503034106151a8513a09211400f148112207591550310542c542c2c10720b0202804e50100d02d00814406c2c07030100220004244010424960304000c1105c1500722890b002d049010103a022400200c140e0004102181c419035101e40e110031302c0c0c5418a030662140702e0640780c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 562292715 1250 562291465 562291487
    0x103020306010903020901080c01110303040c06050d0b030a12120606050319150306061a0306490c272301080109020406053c06120117010605090f0601 66
    0x111400031b00c00014415000700700c1114027102030f41c5481688903215000d55982c801a80c1c001c0c41a49854010840f580c0300303c01400901c1d401e100040f445401e1130780020300c0c0884050068403a145850301c030040e01074005030080c030b85a612450502200e803621a0140140c003004011403480070020076074074140b800c40d0b4040d034810100c48840808064803400c1120050078240224040320544189445c580e030720040603680b02ea140107050b91689807694070b8450216030368160160b6904195140c0c16003d164001d070034030340700880c5079400004602c20304180f00340306c16a520100880301000d00e0511f4854040c5080d9551140d180310103d10111003031042554a00300100f02e8101a00030070012424013019003024092070b000700c900340112500c8804000d1101a15245000d11a5801000d0310b090401e400800b002e002001007151003039448030009c1003446e0f008030060405503048038018411030130f4541c000100c00b1100300c001c1101d2030074000812000c000c00340004556104010020300d40e45e02c0b030580400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 562293965 1250 562292715 562292719
    0x20f030f070e07030605031906020913061203020114070504030308071107090c0210060b030105040b0a05060309070f1a0711040e070f181802011b06020403050a0b1311010302030601090302 82
    0x70710107a84100da07801d054402c1e00c40c41c000a0510600060074500081e40c407020b8504044189000402d50760380900a50000c243e15800c0b0001c01c2d1105076840f558800c80d4014050340c180001c2403441881c00900b11410360854440702c02c0442c044c04440f42c2c1c400251030540b580b6092a021649400c107041d05c049081c030702040c855103d00c2a021401094503080680c441d00340b41c08a1303601c400068100350a85205000382031845900b072004100307614190f00400c050243c0601794000241d110b402281d825031040301c884003d644070b180108020101c40c2166001021400036003000441c0781500007074641720303212003d085100544542461a80c070303940070800c174004500c11514101e5503804146843c10740e511901815109144c40c0c07080b280c04030301801e40e8120700180e111141514940c015100140ca04d0810040745150032811b4001a92900c01000a135000d240140540e00b5145000446500000c2208400d103c0c0d4000d06030000d151f01c40c3d503c0540409081c0541c8a5035850700480f051102c552003c0c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 562295215 1250 562293965 562293973
    0x1021806161223031315180c1a0f0a05090103060e090a060605102309060301230609030303040609141204050901060519030506210c010e10020a020f030f 67
    0x7880650700400a00058680c1c820300f0034000050b02401c40c060300007180d80800c8100c1801c2c1401c0051110742c160002403200180005102c030012003003819000a0031012610b860b50007400780803800f00984981c54201c0f410440e181b07003000c000648140b502807040b9210a01001080c4080036a00079000600a44135401c07031118246000805141d403600c000d801a10054503000700401c03141440c140561440341140c45946d110080d01644403404400900d0010b24000140070482999490000a41c020911852010108100a01c440d0f080050090034548034820402420120391004000d50b41d0280d0064400102c0280da4142030010390718400000c41c0300d00600032551220926140940203840c42031301c400e001c581c0ca60b0381c19241c5100d902c000220b00c11848880120152081d00411342c040707406812410441e21048508080c800a0404145660004519080296407005010001d031804440c000107101c64010f002c2e4039086046030180c0961050342c1c0340d4080361401c001c08052064803000f1a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 562296465 1250 562295215 562295243
    0x30618130f0f0f05011407030615080a0609020a02160b041d131514090a0503040308131203120b010e06091e03161809050c0103092f120102180616 64
    0x4900034101002c1180e00e888003400802d4074140300c0d00c40d035030a40b442030b10522542d90b8403840555040d880100b07332010958560001090540300b42c0054142e140e40741d001882150b0300c03154150100c00756500004071510b4144802c004100ea02c00300054005e000e503000d058203443d00f00d10f10708031020300c56020f011410300300390503420750003140e20000024000b81c2e05603107207071608000b10b6112130320303d00d0281495000740810720201c2c03c1c1c0402010410107c901c1c81c01c941755125000500c09040540950218200c041d0075071020800e4090800c48840c24600740034008241d0002900074050080e2180c01001c0503018000010143c222413001120000d013203949090300c80c8242c1c40c9101c12401140c810000440b0540180c0f0140d0094040d4158404083c181000c894001100103200415060714402a900c055000011564201c1e0705185840c940705000983c18800344410304003241c241ba4036030ba03c1040958134800c9070081d0740000da101100e41d155902e040c201c0402071002c2c41031000e00b00c1d0b60070b6208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 562297715 1250 562296465 562296473
    0x1e0314070503011502071503020318060103080d05150109150e190603060e04030f08040201050403060c020708061e04080f04030c0e0105040c0908060f06011e05030618130f0f0f 77
    0x50b6040b100c1111001014001e2140c2c200c0c1c980b90144030b41d0b41c5514809010440d03107400b90300034562012040041f1420b040424207201d142481c04c0e0300555810000164000b00c0302e00c54000d1940c0b20440500c022500c40507000000c05412540c4501d1404940121800c0401c82c803071056405e02c810002e02441e03200c6122941282251158030500010a12b0301e0b0000411100181040c6c0c425500354403906641c0d6a031010035544010018030403410010104001300c0080c102c1c1c46016035202c0d10b5401824041d0400c0002450218050035106481c02d01d0403200141814480d4505da02c1759022541d643c841108203016041801280c00c01002054880c40c045000803070f10300058100c07501140c041c06500e50305101a50404918050080c40350042d400080c1c40d10034a8403145d422071700624256050f1109100c1440401344c40c00c0c12000061b01c00030610145d481c080d03082c03080c5610107029078145170402d0804110098900e240082000200076801802d224807426811070842e0041c0e200d014040d4a490 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 562298965 1250 562297715 562297717
    0x70b070e0d1a0a05072a02090f1e10090e0c030133150305090f01020c0706450f030f0303051b0904020903031603180b03071e03140705 59
    0x282c210035202880015216051401114050241911a00c0801c03d804130301c074414513100041d81000d03460807904140162102e06103a840b80e40860140042d504000003100c03d071031040201250072110031800d112006c280451494100da1465400140d45d00390b05118034200f0502ca80041d525520b8a54445103019182011440540e0000c103541d00c00354a87c84540000c030340a002d45404116102540700c0001d0103a440702e500401400100c905101008107414260303800318149050076003040c5010045160829a020118040301064082d0342509031061002a44000041c5803000d403d0300070469003007081c51800000c1c01809005200c0103407a4144021242e080600031400a860500024a21144c40c2c4840e0540001c881c032651402020340e04100194000c2140954180000c0100c0301002c10b8101403070700c002e0b1003a101d1040005850a214502c10303a103231b00510182d0800c008010b007440d1300c82c0c0d482da45065041e555030021024048104c4c0141503c0510326100c49070308040c4210319070840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 562300215 1250 562298965 562298993
    0xa0f060c02060a0c0504060e010e041a131406090403051303050c0901090207050705060d0f0e0a06050f01030b041212020a0908240c030a38010f0203070b070e0d 70
    0x18080360b0207034644119503400c4684000242c800204240024044207109000d07031084201e05140c0660604146800901100e10000c9121540c40b04074401031701a00b0807000c4100c100408280401ca0b50128507a100b0081e0002030146100318843c2d4002800c050180051300d00034501c089005100300e84238980385070707a86103050301a445025401c00024800c0410b000b2510480c1e400405008010f00d0f100902c9041d4100031415407a05072564285021758610307200782001c0d4041035004110341e20b10303030400908032a0040c0444805440460040c0b02140c1d1205046810991080310032504650409003203920840c01c0c2c4042c20041d000203082444540d00203c1d45055541040030780b40c0303101c959100410310440c1240302c0c402059098000401000300240a1a400251400040f036600c1130000c0d40c2038402040c5e101d00404868004540b410045600324940f0705401c2824241c594822098000c0c2d60380c09041c00081c481180980040d117003911400303081c550070002402c1068640e10500c0c1524643c1015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 562301465 1250 562300215 562300217
    0x1202060c0610050a0e060d11120a06090b0c0903120d0b060c01090203060903031009020906040f0806040b09010606051204030c0c080c04110f0715060323060a200c0a0f060c 75
    0x2008085003040c0b14818160252a0040815480d880c15a0301c4022108d295815243c0c410b0014003203640c40901842a0400284a01800205403202c0d00d4809e40160340508100071050051207440700e140c8001030862200310821502d44c1e20b50480081d038002a00c80001e040d07412010200d69940310150540020400600c203e09943c4555596a078035517807400122540160041e10b414200403000d601d034010b14092a020304407510741034451040c81520743d020b0f40300b490030741d01410400003800701100c40d03245c1089040009001c26450140000d0031409078003000c4c120705409401217400c0600820708402c060b64010352001010b5540d87c240c80d15440b06040f018051800c0241300f2900d51001d0f8100c1d543d5801c0b00c8030341801c088440d00d43d081d49410141c0061111a0348003c0400418150002940f051420310103071091254400a02401c4c850003910300c2c0c0105040c03012640c1c20355041d1002c9480c0f604900d4100f074a80c072201d24128038000340444081d20200304007108006103d110b0700030b50545219 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 562302715 1250 562301465 562301479
    0x60b150c0f060c03061210050430050405221b0f050c07030f14030f090103112b06050d080c0c03190b04170d140a02090a1202060c061005 60
    0x78551103601d80301c00b201d0740412120100000b481c50724003d00700034600d060107012210304100005001c0d08990056030b094804152070421400210514803400e4560413134000c0f07403450031041403405003481c080e80c05080d01c02c00010246560401910886109240d0314400501070100c2c1010840c0070840369144010001d6484540349940718081d8084500801d8010014050305107951140d000800800d07000711100d400c0700280004003038040000e04208100356680303954441c038440000d4110b50f074040f18000121010301c00c008510604280703031020081d44258a0514000d202c900784014900303500550b6000c070008110704140119400a018400c203070504544084500804142d80e94895100c0048504a20300011000902d40c043c0c441e0001d2151100060740808120113400030781202d1f035001c200c9556048e40d084404005e1810a802034001075086241c0300241001c94108111801540d20000908050604544503481146c24443c014001d030f0341c05003003c0985400706981132051620440b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 562303965 1250 562302715 562302733
    0x150504120302040308040e09030714010c08011a03070f050c01020a020703020a0e04020d03051606050103080c0127020613030506130c080106120b34110105011d04060b150c 75
    0x4000d02c210b030181e9030840710490a10389094000404103d006250740c20381d00041c0806800501e601703d540c95400503003000800c0c11440f4032402440010140e10080210314a00300303540070082000e00b100e030400514a00440030031070355001652203200356620518958400200c01d07080f5175001c107044007524070855045285942d501d082c45d003000000d4502a5000f0148003092000030300940082004175940c100e18200c031902a19420100d9030240c0c400e484034a0000b407a240b240344203120301554072000d401c19090a600c1e2030505070001d60041d100034080d5900040d00b100c0206210900401554000100da0142c90200f8021a1803030201034216640c1c184807a020030102010702030308003654a060701001d5003059649501440542c090059811010032844c0310b184d5a101c400c2c40122103140c540703505118000d40740010070001741c000b05003240d64034100041c000c81d081101c10500003400110100001d45560a0002c014502c1c2e42005a104c81101190700e680b4003c44041d08901a030711081d141030003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 562305215 1250 562303965 562303967
    0x9011502011d061909050102040b040302030607020106032a0906080a0524060d060e01050c0331020114040b0a0c170307080c210a020d0b03160303120915050412 70
    0x320b0907400741d0b40180c22100000b14014040c0800144a100d840c80124002155844213801c80c1e000783c200d41c415080c00034042c001c2d801c0400102d5008061407008120440c80e61701d40003003007032456008a000708850b910710f00b442a9418818000381c03101500c1000215524524a07655a041503030864060003050b501c09001403028842d041455641310980703140395070b0f8500308070b0303a00005201100e400303030b9403110885120340034400c23948a4a042141c840d940d090800c0ca5402c9150501c010110546003050075040c86640754042c450060790a08180c0c030b03d00d40400034541c4a00407031300b1900280303c001c83d043c0c519550101d480240340b80105004000001010f114604034402150030320301180d55400441d0030700480303400500280d0510503140c590746000c0c100389500b071513040d134100e20308680214801035118068407546418002c101c000b0700309000510410f8920341c02500c4042d0511004036504411090a83c01ca00d81d150303401601000c2e071502d81c1d0041c00051505690a860100003083d10694613 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 562306465 1250 562305215 562305251
    0x5070905061503010810022808071b0206180402071b0510030c200106050a0605042102090f060a1203081803032710020c030a08090d050a030c0e0901150201 68
    0x195400030090025071171074410441c003a5001c00000d00a04141a50108e0b2400000c400444106040d07a50180b02e400d110100811080070b040c50461040d080440c2c8070016078860f400c0b1801228a10450001102c844001400a0081c0e0b41d010b00201821011200840041d424100a4440403901440e110000e004100c0c200c0382d11410fa0b2010510040c02044034030002b00352080080d05010000c1185034545000c102902d0f0790760f00820125001140c188038007802ca14154014403104003200e0807004a6070000784a10201a00e00d40380c841207040412035645035031000b40050b00d82c050076045544005c5c81c009192200481e100001c1d003180313000d00c104021011007201c0c001c00700b140c4100400004611419400385503074481031164460010005003068860000c0c01124210502071a1100404030016158400060085102c0d82100743c00800554100e016141484840d01d000568120b40903019250360341e007008810751150b000300001801052018000d0300480c6242d00034459200d00c400400d01c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 562307715 1250 562306465 562306469
    0x1104091122090f18081606110702120a020f09090a1a0906060901060807050d060f060c12091d0a0f1401090e0a05071523030f0105090f04110d0507090506150301 70
    0x13070084070650000114485401900c504042c02007a44640700065540340110b80d00114850300304007000c1400000d5240035203c00c40600710b640040d2045640c20350020305014590300d000d905c103c10700004160101000c02980d54560f52000074150240d50b000394002c0044412034110341640b0501c000100907041c0300450504842c916100c070041038503461070a6031b06400c5040e140d400f0660b24a0300155401c3d070b2101500007014261500d1942001034204000c140102401c150240045500e0420903400c0c88000165540070f018500380d600e4542c6050400500b4803011004407150500401181258100004504803850a042008402e43c410001d03512610a0040500550000c41e410041d80120000c2070001d00c405103481104405d0b10703010403940b552411400e4003202004001c0004103030700310200d076005d000202c0b5110b099103081c000f051070680c0c00a00c01016001d080608000c10780325050601802e80d40601070f21035468503845003000400d8100e4003644600603100d2440d004401000803641 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 562308965 1250 562307715 562307741
    0x8010e1c181d0a1404060203090114040b0604110f091302070f1406010602010b0127120c030b060a180f0f020c0f01050604180f080702040e0313091104091122090f 71
    0x4101c3c0c0c0c0d1070315058003d400c000d210701120f542f15071107010030801581505106500c10300703940b64141042000e03c011030ba110650101c6461042196000825550044c1c07014a0400c80c0c0a0307085401003580078010b4018031400030003142c2140f1000c1c0800004113001d0389112340310001c46400b40e036a10317412801c0e2824403c445000c00d41070744440040b0900c0340a4035041c1e80c0017500c2140019034030b40241c0300324005944107a40c10411302e1000e02c10040120318080e0044411144840e41a0400100c144400c500583e15104590f8410743c0700201111500801c10580409070304544800315500c0071512410b030003110000381d5282800094640c0b9140c800d80340c40d2484080350404154041d540d41c0714081264009030742583c1d0500800300180c1e20790003a01a500c140201070358851914070200d03030001200f40c005450380e60a202c04500b5810410f400d5900b190140100400c1e031a12007580c501040c03240d21195451403108602d5022006c80e4000d2400844600e0001000294550007640c1e0898804041c165 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 562310215 1250 562308965 562309001
    0x90f120a0504031b0f080a1a100e0414070605040f05030d0e062b0207020f03060103030f030b0609100504032a0302010c06021b0c030708010e1c181d0a 66
    0x20000c60200720002901d00300410011101c00e4440c821040c11409646c40704104c1d910140600d800c0101c00c15100c1144a5880b4070041e86050010340c000003c4141c2c007568001c050390400080900c0090200d180c102c402110543d800d554440b04010016403050140f801da0b01540d180c00205410300243d100005400d66403400280b8a0450800c101c84e8004070b0f158010a00d456142042c80c1c1d42c0c4020031210f0900300e000143e0310500781c41803002c90f200c894003851091304150010404603402c040314090b0f03410a898002021021580090003034021444c2d0070307800c4011160342068207034003c0300400590f80203000c1c496082800d0354a8400c0d01c2d1400846411b1131000c0c110410055004542c41c6150621600c400342c1000c54081005000704052402d80b001580015261102c43c00e0a004041c06418540300a0040422407801e6941e210400c030082401c43c002440b100c2c210303512441d40136a00210a10340d50310001e944840522495000700201040701200340c0100320002d020b84195020307100303914518 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 562311465 1250 562310215 562310219
    0x406090f0b1806130909120507110f18040b150d0c0501080a180f0308090a081b03040f06081b04050f040f230a0c0224040204060e090f120a0504 63
    0x10418842c0d110b5645070031610034003a100d1625001000f4034064800c0c82c0c400a00120103080a001c030550341902d80e818080d0400480c0042504005401d40b090740603508151b45095100208006444698002403030051000600040000584000d801847e103e1814600d01203080700704014101c4494006002e01c061040420265025071041035200a0281c2c0025907422119000305600c00c21520803102207502702004010550050030691f00720070072a004100c1c0302c6440d6038070310403481081c08008000c000c401e03403800c22040800480b40581400c21500c20f40ca59030300c00240c0840c00036140c110180c0481441a8911740e6020259070803a80001c3c4400d5095507138005000081007a90340300d1000d191211078000d00d00b04498500c1c507001d0070801c950034007890414126421916003102103021904080e6510030781c0d0300c0103003404c1802441c00382e201a55450340e03c0020024034460340541c013001d003a0000c1060110300851406035070000c0ca003d4a10003210400c0100d0584281c0740f114011601c24001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 562312715 1250 562311465 562311487
    0x6040b01030b13050a140a0c110c060417010908070b07020d0c0c03081804020a050901090509041a19181e0c0620060c0a14040e04080a030f0608030406090f0b 69
    0x107036048080c07085c0021300d0103c107020905003004121920010300d40c0b41d00b032191805500405c0b41d4101400c8001800c81c0340721840028440344994891980031690821600080716001c3d030141803d2580002d44940d5880280350042d04680103c40c43c01c094015590740404550003854915403140d480a20109050700755030350b25000b50010314440f58400700748100f803429a00e6510080031240001d40b036058460031618001010101c40360800380c000d1141406100000b000d184060b0214a001e001e0485950f6500c1d510001854400d83d00095482c140580e40040d0342c0141d60181820b80174130074210380144505824414044074410013001e00c2c20260701017000d64454148840c1c0601030340e0780c002c40400c0c0b0040d8035240c40d03000d480c01d08148000240ba0404541c01c810541c205100e040c00484c1804d15204611055040080c00900f48060000d140c0b004184070b54402c1e100310f5416001005850b868049290303580c1c1050140c0c40104403c0600814041203c01140044620003801c80e4507107500c0c1e60b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 562313965 1250 562312715 562312721
    0x203070b0702010e0a061d010e070b0306011206030f0309090203071709030d060b030703051015030b04020d02070b060f010203070c140a08061305160b0d05040c0b070b06040b01030b13 80
    0x8241411956144550140d4110034172201d640315014100100d00003201100040c3c0f40780e10fa91000d40c25030324205060704100350200700344040f1082131428640300c0d5148001655002007050a2101c15481c0a501008200e181c0e50b00380c1c2060b01079500e47c1a05a03e4451040891100b9100c880c0400e480101a04503a4004000c265102400b2020b50b82005481500e05040c2c8045800c00d1044007404404c00c0070156141c496143e21410f560007050f83c040c5000130602044078611144000c00d5250a001c00301502d568044818003000c0d510210360b0303088541890002604180c0c1c0b80c51155400a08003011980b0000a0f034100f00d030002c1c00c6001040c40c183c11102c24019121066801c41070030000012180320900420f803081c000c0c0b44d1000f200c07610324500541495515110b5185440004c07209102c0c400142c01559240001240005010345890a0007880c45005902c00301c4513010000300d881c200001d0542d0f29000f40750985080c05182c801ca8019020b5920710308a080e0030040280700310041f440307590 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 562315215 1250 562313965 562313971
    0x10b04020325050405040c0302041a03040f0b0606160302011e110d09110d140c01050f0909060103090c0b04030c050307120f11031b030d080720011401030b06090a09030203070b 77
    0xf003040d034a815683e0000c10181c950900e1b110001c41d602081c2009001c11700e0107141150319031420014a18a4169a101c07000000e940c00a4400c40030030b03000803001d89500c011100c143c00e140d0411004040d051500134068900ca402c2d4558182d9084540801c21846001e0b000d802002c0755000e50070a110086440002e01d4080029901161b08449001c40da0f11040746145001e402420814104c0b20111101c920700305200508038108100cc222440002030254161911604110383d101100d441746c000480207484110340c054544c04a484000030b0307114a42004000300d030710803004408070301d40d00c1d810103486116501c42c207020350072580ba01c07400042c03507400c0070f1140707601c10403500e0300f808a5071700424640b07a070040110005190320340c0995054902004240d41d250207900d00181d03980742500000703090055103c488031601003030040c0242014001c0d00600c540c0000c90340003008540c0c0d20b0400100f80001510b000303000e00c01d40004101c040d03003540036a000c0950150000c45c81c041440d41c698000110003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 562316465 1250 562315215 562315217
    0x105090f0a0902070804030c060804080406210f0b03010e0f0d0818070e01050120070501052b0903090806040f030c020f090708060f0d0b0412230a02010b04020325 71
    0x40c40220b038110481c400350144500507050030340ca460445c0780c00300711a1a607821000034041c48404000c0081c24141c1224103a03001441c00b0000c0980f01c140f03000100202280d0680041d0a01030468440a4035500c09001c883c0118001d000828141151548501c000c1e0041c003003581201e048459203502a01040c1e03007140016034100c0d00310501d060750f242000420b401c84600740310080010401e560744403c805454108030640c41201c1201c000360750b60346403800d01c180d40c184500800d000418000c7d05921410000d5490358003905401030064680042c9a104001c42c040b40d0540b502150041c3c0015001e0710882d03109446498051454a041d661842d030400202d03840000c220040c001d68454400580c080d0106868441c202e0402c4001c1047c4406401145400381c4618070b4104003140554030b0094200c0e8204091054070350901c24201c8055030410003100411030503501e04550201c0510003841c032441ca0354000c2043d0070f408402c00007a84010b85028501041c0111045a00d60900e4034543c880d91031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 562317715 1250 562316465 562316479
    0x5280c050913051b270312072a0b03151c0807140309011b060b030a05030a02070603060509040204020a02070e1005090903070b070c050c130507020c01020a020105090f 73
    0x500007030b0020188046400c5110b855806000344a401d00010b0010710414050150800300300c0606480d00c1c0c84400a40b01489034481c5505805480620508103d81d802c6800143c0d034005600300a82d0390340d003001c8442c100c3d0800144420400524454a200341c038140300500e40307162034045201050404c03900c41c45600154005c0c5202c074000d5110450000144507a01c40d68969645080c1108011211900e058a03900304010000c0e00c1c0c0c0e07105030750500e4662610320000d410340703407820680e00405c04001c60540511441102d90248003000002d0300907020786908640782151a40012402d8860700e10807581c00034144004900186000e40142a42d4205841250100380c0d4500c0c3c40b00c1140c03800d03500803030707a800304c1c5d0414025801c04a0042e54400c0d04d5100642c500032a603078034690340b40f42c024110800c00c2131007042079080200134401495103010007080140da180070298190700038032050300c5000261080b2006040c4070350000c40c2030030035940c050711220b060007410010b12100707104030344019900a00e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 562318965 1250 562317715 562317727
    0x30c0b090c0607060c1e0e240706020408120c07060503070c0c090c0f0302090f0f03070b0d0b091509061909020c0304150903080304170408150a05280c05 67
    0x2988009002d040c1c0c041e082c04122015018000713000b01401d007221b11030040400701ea018a4030342200c401820a0b10079903c59204032000f51405501c41c2d000c06092480640c006007c4007131089580140050300c1c4040b0940e107810281c41e60307400035407054a0800308a604440710070071909010700e02039640401c81e41010184c44aa556484001c030010390040c80b4200e0342d43d402021f02c2c0740d00c09110700b502040d50408610f0880c581700012400241154018810010801c0d900c6098806102c90390052010076542d9858600c2e11040b903001d88030128506014006001c0000d01c082e40804400c824cc1d040a81400c00548400040c800e0b0007a46041002d00c14402c40c100281884007031005019401c0a81d0146440303605000807072148110f111108000c0103000403017440407d0040044942050380890980415000404000c107a0300495111540364010311410114505c0c6c0e003d034841c89180010420003c658407003440445d000d4a881312242c900600802e02e04140415074820342009580c0e0410700d0a0031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 562320215 1250 562318965 562318969
    0xb04031511070605071d030123040f15021c05040f0204091b03110405070203030f1501141c2009060c2e050c0307050702010e0414090703050601080604030c0b090c 71
    0x200207440d000d000440c00419540d0350150805030b443d265a044000703110803000e509c0e1503091903540501240c0303c0d407403000100c0c0820948030040001540d02c6150204c882c200300b2600c2c0020341004000405034500120000c07038a0303806101e49480740d9400000e548051071141c00b48001814000c0c41250070310301c0710007450408003100c1d640e000114851141200000079410a20003510405840c0c48199441841442030007000c444c2c1d5168482442016a981c20300c10400480c3d81c1540c1c0b5000c042424400070b142e84100c49190301a16200d008030100780041d0003d002c108201751a2075401d0811527805005540c00e9103031a4000384040c0300c1c03810403207400741c0e08000a001d02844081c000c04208215406c4c00c14810710f2405030990080c54050700354210700c0c0c4407001804070300c61441c00078100940140d50a04598541d80004460190044554101c0c43c01d40001517944090b0b0106590901c920b10002503240c0c0001081d6105690581e40d604810400f545c5088402e1006403218a0074040c10030010381c50303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 562321465 1250 562320215 562320221
    0xa0506220e01080c0f0a060c0314130f0501021b060301230306160207140102070506030c0c0105010f14030a0c120503040317074202040f0e040c0b040315110706 70
    0x2800c048405040e8422500c0d0800520ba034843c5c0119001d02c00c0168100101034004880216280d01030820040b200701d1200121454030a85400320781c001174150000c81ea250089110b44180d84080e02107454103841ca00303841c00c0c4a02c202c4805a8480c03020001800389803d00241d04034031034010328000c2c0d5807540d4940000c0c104130b42120048810b600300282071101a0381040401c00801181401c505841e00100000b52609020700038030307000300c500201203440703400340500722114410410020002541c40c0d010f80464010310740700d20300d034504401c1d515801301c0c58045400c5440c03d9001c05c5d000f07503071442c00d20a40c18100c001c0409949500080c000040424190400701220003850b240da0341d81d41c600d514051039081c0703607910028008a9029107410200c0b1025409100040314203030800034035240240410041e100d140c008402241d101ca00004140c2030604016001c2c6202d00e400503503030364031847d0300400b501844c8005461401648014452580940d02ca2040800020300381440e18046072a00016 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 562322715 1250 562321465 562321469
    0x911060c0f011e0b060c0a0305180301150602010e030a0801030f060e030f0301030b0109020f070f02031606020703150915020313080408030d0c02010b0f01030e03040305011103010f050a0506220e01 86
    0x20482018141d20003410034402c400840c80112a034504289a180101e0b60311f140006004007440000a100344c0c00007000003442c140340c5001002802040034050710900540c00900c5224095801c1107401c52400d00c011065401c80702d01907a43c808641c0c43d54a030040f802d443c0d00000c0c0d0f4080c2d40c4241401803020705200070010001c00480c0c5070b80d0395245140c598a600700503401a44003510512842c003441d0b890400302c400040c1c111094442d002203500009042400e030904c01a5004a445d01c0020141c1d00801c0403021680134241348d944c51070080041400380d907030800b0011b0400d59408602c40a035030b4541e0146800c00604410360541480fa075035030f03081039030150704200c45591000c1000040c802d40340c01280c40450180c4024032000a50350040ba040070340300c88401e4103141d1941608156250b00b0800d81d8015a0010005c0c801d9840306030040c049544213016588460040103401b02c1c49080400c00c08040354405405240382c86140903c907652560307400c0b0400c144128000b400148404041c40640c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 562323965 1250 562322715 562322741
    0x9050303010e0117030403020f040e1501180b030604110d0305120a09050c0114090f0d060c0905030f16030305030703092420040b03090f030304030309150911060c0f01 73
    0x3082d414001138000491a8055034400c0380d0007000184016120f2419440c1d0010095801090202009501608049020406402140c406c000000381d51070303484200200d0040c003903400c01103c640202890785030241190080c2941e481c0000312509030410000206a06001340703855400c10220b020900401d0100b5a40340054641724210401409014000f0310740d00202401c0c0340c2c1003a41000100205070081c044c10a104010300340c030240154403001c1c1c1c0d0070740285e8820010441d154042030041d04a20450084500900c40c043c07204030001000a80c0c1640300c0540e000c0f441480d482c5070382c112380ba540010184c1c4209906c40b00311400240da034440d01041c2400320100c24014481010f0003a04903111000d64010028402a1a0300d4032102d2008a400392940c48a8160392692440342c0a490b14011001520061000000300400c9c50743c560301c6003005501c00e07500040b12440c0c480e00801641c41141c0c000d05403100032140000582340403030082000c0300c551010b441e41c1401e0022040d08689403180015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 562325215 1250 562323965 562323989
    0x408030106171302040c180306050f13030212031506030f0912071106090103090f1b12020f220f0b0a0611102f21090d120905030301 58
    0x2100c442e40004814000c034514000070212441d000115502c034000904002c2c0c01141d44100e40010715104101e00c100101407880b95111142c0e0b80e01c0c02e04000c2008495a8980241c03810106100d040310f5860301e08299019401485c0400c40c9000454199001801d01c0c0464103000850b002daa48440780a5031140d06201e110b030341c1c11f151000c549410074040d803c0c088082c0c1d004005401c0001c103c180201a0341e5800c1d90300c1500c40c20f50800607001002da4144c041c102c203c05202e90020000d240d1881150545044d21038042e003503442d05a00c8148a80c048001c2d4070210021707401c062407c1416990032426504070741c50700c1800c0850694401c55500c84001c1248648841b07400f0a107040424010f40200741a1400c6414441100511900e580380c40c6030b030b01c0186440d03040e403010000d46400c3d00719201505941c040402d011482c0120140c0d409040c852199100244403c1c0104c45441000e62188480002030001ea41d5030260440780ca40200740010b6801f035944140344085201000030f903010b85804150b031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 562326465 1250 562325215 562325219
    0x20606030303074d060c0d0234110a0303080c0a0c06051302091b030115020a0c09020901080f09190f0c0e07020616050f03250806130207052104090504080301 69
    0x103000a0b404d000400c0b12940c0040140724801c9a03a45c12948034060304940180c0381d005803600d03601500a40685a002480002c00d00c48090480313038203c8400c5403061900301660141d02003440103000442c8000740c00700d81d00e14001080040c4000040c101022140361010302a202ca0740c1c0e51040b039009907580c0010601c00c010840440c100480c1c0d09400c60b0f0a0a8a0000b48204145800145c4014010b2070030902001d100c00415034002c01a9003245944076080140c003a403206002e0000750410a40c1d54000f0b000780c0f0204070b0041c52182c1190143d40c649002e0801b415040303a001d07440e1202004215118205034034442d000c10440c48401c40030345880c259601407420a0718009140c031002800d202c003920a0b451420301203541000c03c036441d1600e05420a03032241c1c0c0b035110005035950800031007952001010217890341580d20458040c4580001c50b2105510600162240308038080c00c503005004e94088400e28900207180402482c0c1d5901000071580f6294881c006002610700546040300c0c601c1c008801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 562327715 1250 562326465 562326587
    0x706090b040b06180c0f0703090b030c0d0b0f010c1101020304030827010212030106081302030f0705040c0320031026010b010f0f0c2d05010b0102060603030307 70
    0x1664440034030713010a82c0c0c1e1810280c118482c1442031071030a01002c00c0008500c0c08250154103c440240811100b1503240d107007a01c0c2c010169032201d030030f814005190640c24007a03440c0c0104121891003041c2d445c407601d5541c6039588a030b5a001c00c040a030552105210010001d52800002c14020604440a041143c070070302c02000d41e259404821410754009002c0c00c20f8504042d410303a07044407200d29144910751640504000b080d405000040d406028524450150350030009000c030032100240c42c108400c032041e000803000c54002c190142c0054204d1030354804401011ba02664000c100391811000140d0b64040d0388904040f0000c80c1c480e0312003951800308806200b8032414401c0002800d0100c000c41c101c3c0002442c00c051000307564248020861003109000503000c85c00e60445010301c1464039503014101010709081060400c83d101d600700442401554404620350340180f902900070740c29a181c40e1400d484804441c40c1c94604030308030b84415001111442884401001c0410545100e156a520 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 562328965 1250 562327715 562327729
    0x15060902090a09140a0b0103180501020c1b06040627061707211d0615030708070609180e030d02070209090c0f130f0c2f030409020706090b040b06 64
    0xc0f05a015500c2c0140f0742d11014101c0c03200e10b621240b030245c005011004a0700586c01022040301c40c0e01d02600004000b010004154018068a4001d07001c0700c0c5283c4c6e0500c40712800e4901e64a41036002402480b0410075180a401201448558005000d003c050380c99200e1040241a13032110300000c183d00b014004d98013040310540d411100a107000000ca40141681c0c1c420324256090b070390780056480b26400480b01209a01894031040c00701683c40b0ba00308146202c00c0d8800c5143d0035403203801049c2000a0140c0f0003c0c1c0e890403907445446215400786840400c040780340400281c58612600c800354003c0c42c2400b40020000484060401600c501c500c1c01884520007000b0704880103135016401c110a250348a507029a00920101d81c85401500f11665420203000c10041c030741348680c10030307484400031504030800c0314140d61084440780d0745000514080c46440b840350010503140d0001c11090001044a400030f042c0e580c007800012401103403542d15520494812242a82c2e03000c446000e006240c5040d80d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 562330215 1250 562328965 562328969
    0x100c06060302032b0809030a0804031205010b0a0e040203040f060c0933021911040e010f0c1704030801060c033b04060b030105060c0f0f0c180c030a050415060902090a 73
    0x1117000d0f000307803030114203290750384c82000c800f88103000215001a042511a200000d0758202c62001401656956801e018441c0c1007002d511020940e034064803580c5080501c20b03070344140e82100040a8880543e01c0d40002020854113000030401801c201144c0c0a04048180300c51140d6000b100f40307004000e403005218400342038140b00844d040101d1401d80d03088286001120030350400385118201c00600001030040c10070901e9030186500b00b14000c0104075081e8040c0c148403142c1c0d162603003c0c0900306400722000d10111801401f10300850010f11000d842551207603401482424008155486d80410b0814170650f10100400f0100c216023001c001d0700300c02c010115a071410783c1e0901c41d031800c1c10540c4c04c0c02d00050223114040c01007c030b110001c5440c01c010b5180c8030502c1400f62004491040c1002d500d0780d56400001e4010341c0788140041595070b05000080c4900c500001ca10304541700d001d91500a040701500c161006402c43d8903d507002140e500c02c0d00014020001c00598618081c1c0030b000c425001c0d6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 562331465 1250 562330215 562330217
    0x7020c0906010f030c0306170304080c01031418152806080c0609040207020a060c17030609060f120f070603201605011514040e0c100c06060302032b 65
    0xe401030101d140d0300408001c0d50300784242801310741e00c0300161045000700700980c4180303000076074526888030201f03010005009441619050fa589610500b0065050381c1e41402c80811106010b40010345010a0480c00d444405148058550b0220245140849480c05481d04852703010300c280741d146a00402001c0007012017400f0300601941c3d14048001307884804d44200703540684400103a84040740d60b0b9a044520540d80101320b0300d81c1c6a00c48030000d20300c00d82c40388112500c40700d0501119190f0052010340c0e1140c48002c043d00e445580d003005004440f900c481c24a40c00140d10110f500113107100741714401c0c0102e0b441008200c65807400c0310003401c0e6140c2480342c500885903074141c5420501d200307041701c90740f61640c4040c496010407882c025004143e0a40004000c1e40f044901280309542245100040c80f130442d0140700345c43c104a440b68440e4400c00800b0b03805280b81061382c1440d80261414020940514400603580c0da41e500402e0900c440703840100107842045104803081d003060400f6032824405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 562332715 1250 562331465 562331479
    0x10602010b012f100509031b070f090b04090506010305062e0618031202070f061e110f0a060209010807020a0c050603040c36111c06081507020c 63
    0x1c3c0801c0c605049501d05000c8011580b00da43c0c128400401c1040350718416011800f00442d140a24401c0d4981d000344501d2100c21400c04d00d2424030640000f502410f5600c01540914440d1030480440000c141042c190ba401580b00c1c10003202294060204031b000b035000d00080c0c0360501e0681c240401d221191080c40701c2c4221980b80c041e00d4011064004015180701d81000901002c4030110700084142c2070b40010440c0c0400e07441c80400340c5c2d010401c0000c460010b01c407010341c0c50301c42c40290761251030003010044983e81000c400006074030806412040d5803444003030300c0301001600d0b40f55007080312903001540d5603500081c0740d40f29540d0103109103078001080d06c05040102d9140d61100c0c410001803050500c03c0e10040301040510482102d00c000520396110031b4200c00008549100100f01410340d003002d0210083c1c04c940036018103010341d18543c248404441c5c54203c10b03075444075510170765007500b450151761210081000340041001d5000c0881420320070f01d81d841d000c84001c1c0f401d12458040707406686c2e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 562333965 1250 562332715 562332737
    0xc030216180902030c030a05010c08010504020a0e0f010509030706080118021911030d0603050f07360e12030114060708070303090212070f06080f0408040302060a05070b0f010602010b01 81
    0x100050407115284010210301c01c0c0543c00024501049110069414001d0310240f00820105600403100900340e0303262030300e130390783d0b85d500f0442240645c0300d40c1da0114120b00c5070442d0300c0c5410b804170130714103e050500b141400e55500c04646804400c0d004440450480f400602480002c1501d4070344601e01800f0035850b140d84140300c4055016456003450500c031600000b440764a00034002d80d9084582010200442980ea040c517550722484c1031044123050040c2c070008503110701881075843d0284100c0c1051180380a00c03000a00f00d44015139050b00119a64040c9055184c00a0150b207402c1e0002c1c44029440f035041c807006400780c181240d007451185600300061400070320b41206651400e40c0504000841c2046800031400e091104080ea494a0082000c0405c1d01d403005030340d04040c0c406c03560381d2060903590070f00305003048042620054103266060000300b005261100c000e0208030700700e14000d0b0030500543d0364540b1175141500c400754100d03100c1d0f0040c00326690910807118621070901e82018019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 562335215 1250 562333965 562333979
    0x1090e012009150f0703031b03150b0a0917070314010b10050922020a030b0a050a1205030c03030a0204181e150308030a0905060601050f18150a0c030216 67
    0xb01c92454094003454120444100101ea0340b02034410f004401c000840e502c0e8000e140040c01880e04104100d0800028645040f00510138031614600d4444140c2c04c040e03d5040c80c030300402c20b821440b00c1c0e00070041a00c80205002c001501d008a500800d14014070900741540b505002e040d042c000041d006a2410500100031360b01d0306003030300000d00203050441d03071641c08001240030340030005090b002d18013140b0052140a030341b6238000d02043d001d40d0f0b000c02040c1c10280c10490009000e01c00c4035441421007006101c0c07010503c2c0f51280d440e10034400c5a1070001c2081440382980c00440b00040780ca98049020094841d0a2210000c144d10f208410400e48400d0340c400303050710409015180800b55107000c4400d00669a03500440a1500801001d4480c0f0300800500040c00d107030b00c800c03038050190001103081e41d402035064074604070a6035481428043e04008840c0e0300c440c00c0d03501030f50008181540e91384030100d91005105030f0406a884030380c04051420b01074a02000210b031003100c0c00210000300440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 562336465 1250 562335215 562335217
    0xc080702030a0e0d0f050d0905010806060403080f0903010207021005190906080406110c030f03040c060e010206130c0e0103080315090105030d080a200307090812090f03070e01090e0120 81
    0x2c204580140081c00c036405c059036000100c1c0070083c514803500030503400340b40c0c005075954203c0d03070240e0f1020402e41d10344041c0202406248030003400b50009014641d006600c48018001120000c0c000600707003441500000e00001050020300b021500000700700c021000c07003c0c51031981402d40d081c0003201a1070500001d2000300c0060010340710b1691124503008407004102280c00c030080c643c00f00c0751070315408074001c00c0702d07032003038070103c07048032880c00c0010f0614001c00038030300160300580141c8140c1e60b54140e0b00505440d480c0089a40c00302c40d520201d103680092200d00d000c0c502900a0079142d1804100080c00c626601d90358600c1141081c0040049940000b000c40c220702d040e16104800d5283e0324800f0700039040000000c0e45440305a000400c0103c9001d0155100f21100c0d035400c5800c580d100044e544640c1d40d5403c03440c1c2007404000c004810304102c0d000103036038600582151000e55940c0702c40c0941d1082a000721800d030340c4034590a20100301c00d0150040440030003200341102c022100b286034607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 562337715 1250 562336465 562336487
    0x1403071202060a02010f050709080c04060b12040c030c1203020f01050c0a14091005120106031118060c01090303020d0608060603060f06120f070315201b100c080702030a 74
    0x1141d0710028507030003503a04c02c1d0050b00201c2040641804a401c241c400506065041d00036080140310721400c0000c9490140180400c07281d4451500b80f6000d807841c0706400c5644010401c1e1081d08481200100007054105884010b00c09103010102d0b031142c0f0b1030b0003414081541e200c44441d0381044240010080001c0c22100125102d0500403650404035401d00020300070a1079a66000070b1404405c1460350f04a070081000d40c900c40d880f502107a0321b980d001d804480d2240381d854802e000078011400d84038100c01103000e02c0000140034500b4802d200a6841c20742c1e40040d0100c0001c1d40104024052001901030718000d480460007403c024030b0113001090303461070f00800c02407100103040e0114145440f840b2004a86005000075511200700010201d96030b46070302c2c40100e903c080441304861900710b01d403198020301c4460b140c4041a00300b000c040814581c00c04846d40c0a4000c0d452031840280c0403c1085214a40c103041001c1221000340070003410301e9074010080030564104024034076607240d1028100d01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 562338965 1250 562337715 562337719
    0xb100905090c060a02010b0a030b0609180604021903022206080c1f14070308091c0e040504030e120105060a09020c06011203020312240a080312040204020c161403071202 74
    0x2807282c3d404c4004902514520b0055500080040004402c2c440d900300d0b154401c5400751000c5800303840b0540341400c2d80c015001c134940d9a410100214005180c9012543c5260407000985a10030f5104e40018804c88034001c416204150000305c815540041c50143c5d00040022002a0013580004004500c9920207a940e400c1c4030743e51071203801d00c540d00511113043d403000d2045585840c3c00042ca009040c40030151a84141d41c41207600c0281c040302ca85480c80f81c58a102e941d00c250700245030080c0700103044060011400d01ca01d100020714503031500071644010f90b600400101c0c090078120300348130601819412202c0c0c0b69004100d0a03124050018078241101c0040e4614402035000b42412030a6004505020030392101c108144440c03141040c200e050051000b0f00d8040c1c03040d800c0300410140d203120380320307000d460f40041c0040b101b00c1514424281c0d2103400074101600e441000320740c5c1414a54000300c00b070600030595070140803200c0c1c0c0c10401e060302007055000703013204d0741840e80ca03180d81c20807250001c1c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 562340215 1250 562338965 562338967
    0x1091a09010e1203072004060f152c0f0307062a020d1202240712150605030906070e0f040b0d02041a28060509030304030f0b100905090c06 61
    0x1119035290150200d09030f203200d0041c0d03500c0302154030701540700f03c4005804110107030340100c1c0d54030303103140034800c0ca0100d0701808803110641d4603040b08912041c602160319401d02038891200030002c4001007015017440c0c01d035603209595080d000d0411006804c8104031038040d40c480d0320288511030b04000c04454802e0b03c03140d042d684c030311004c1c00c10054200e18003000b500900000c42040800450350782500c9004110307002d0f03548800001c0c5c40a520800f0b03003540304100c1c5601c40049201d40c0c1c061000042c00400002c00400c01143c061030318810308441d5400382000030340000c100200d055061119580010340d0345009807403800030000140840d00e102c0d01d82e03403185030b0320141d1000702d9542d1240b80e400641d0203881402100301d851002c08a00d561100d945009420900785502401071150040448001018000c803149080c981c040701c842d08032a41181d0103200800011000c100c808408450040c42082400d50a2818414041520116510040006050500340100e4807004100810343d1501030300d0003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 562341465 1250 562340215 562340237
    0xb0112050f0907093b0a0b040213021603050c12070507090b1504150504180606030c0201021312020d08030414070f0312180504060602011a03061b0a030f0e03070201091a0901 76
    0x4170b04105d2201d8103c00502c1041d010104004902ca00e09110b2402103810248010440c801d40040c1d03c04e40f500c100c43c606c070110bc4440080c1c010310207000c2e001001e408030381c1d0306808000310100b142d1004c4025070b401d6104090400c5115890300410605110688400110340d0180240700311600540c0182c804d083e2040100c1d0400078458020355008051002e40c203036481c804030b0381d0071005103494024040041d00b440d40d40c110700c5005000b00c2304c009480c851050328aa190614075a000720100c0d0b01241e102003030015900108001001440c041c1c1d0207407204200d8005000c00c8649410074682c0034540d900d0a030081000400c109000c2100d1113607081c00d1a941284000d02c280e8840d001ca500f0880e801460410702041c0d40750b055010050143c00118402c108a840a082550f1800704880400d10f003091100039440c003400304005030801a6050401107444d07a800020702066413000324141801ea8404213803441550713031082c100c800601c101702d40011510080110100c46101e90588981442010040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 562342715 1250 562341465 562341551
    0xc04090c031205120c1e040f030b041103030c0607020c01090509040803101e06032f0a050f04060f0e0414060402090a0b040e190501080706030b0112050f090709 70
    0x1250802c9410907001e0340f141c917001a56903001c1d04800440d403030011429440050702d0901404907015100384462a1080b18659550000b0880c4001d10460303c14000401c01890307900d0400c0030b00703110b90031400540000e140007800249800030080000b8100615214100510f48804c480c103a00319400505d099034075600d010f004c1c0b42c0305110b42e1000f0403c82c0e0301e45031080d4100000d8801001c1e260f01c1c0d50309114050481c406101345003040050086034045207554040090f00740710060041201d00c4c14920b04100c18011922801c0e00145d00020105450b8506500c50725402074403c42c03c04001c51b010040100c4030351100304549001031845009560004965500396220300940000744a800280c650362a1103c0c036507010380501380e03000015003c1d03d807020a0b052205004860684040384000e1502034905001200500052041b8506000041d8654400c03001c0742e0040e1031051403410712020842c1000f4510900e080d00b10b5004054a500c0c00000310010a90a0144150345c0d41304941000b1140c15103031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 562343965 1250 562342715 562342717
    0x306161205091f02130e060a1e0b0c011d03070f061a150a030b01090303050a0507080702090a09030e01031401050f03010e0d0315061d04050a1b0e030c04090c031205 72
    0xc8a0001040d0b0085205403d02041d0020302c0081010003000d584503907618040030a961080e19915031210307424600340b01c3e0a410444000081507070b0400710884660380e240221107544096400001e69444099070b90501c0304900300d00143c0042200154034080103921140580380002100920a0b502c40c1c9a4100d407500c6084070b901032600040450318610400d8808810701d500c444c1c0706a01281c14002c20860540c041d890010032071740c1640380d8034030b4064502d0b4112504c1d8000103040781c03807242c18003451004d611200304007440b40d0b89c2082c00103014151402e024003c516141002030416003003a00c001c1c0c190000b520b0182c11154107940c406d41140d00c48000074050030700c02014040c80e11540c110089a164581c000b41400c0003820fa51440d03c0d13490342d0003156003491a412a00d5840708044288034182000d03070040d540300d0340204001580728012458200307042c44132a2100c00044449a54000c43d00c0c0c1845442c0188600b00c5003040300743c084d965041040f09032844054034500b80c00102d0012036001e04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 562345215 1250 562343965 562343983
    0x20d0f0309211202030c0303150a12050a0204050a06080a06110706051e0a0c0f1b0b010815060301090b0105010507050c0306070f11060121050c10030b030616120509 72
    0x1111a09400b04051640402e0458403000d440141e4809100c40341a4004030403107400c0c5200308042c1d8519518400002402240e400b100383e0002d040342000209d116801204a103068401c001038040c4504500400040c1c0314040c2032600c0042c0307016000c11a2290004561555561101011034462410051240c5a014400000e0a404e0908042007180032903c521500c40b08041248240252a141c140c0f000701c42c410001080400c14440340105010f015844c1e44c010600c83e40c43e04d2015a2503642d40304c0b4078403000c1e07114003030310b5000303482242e4190404400c01c0e41c4a0001d6000b00007040068075101c10f503c0c030603c6070300d0620200181d9807051288c140620410003801a04460441c24000380040130840c00c5292400010b09000c1410b0424030085107282c101e68100442a5a05450307007003540949802100403582417181721f02150064031444c5245248420540f0000b8184a0100a144c20000010700135480302a03c440410512034101c9821200f00c44400c10000703c80e9103d1003c14a808594 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 562346465 1250 562345215 562345229
    0x10f02030a03090204110c06041a090d0318050a0c081b06190c050d0804030305090606220e150603010e0304060210020d0b031c093c0b0f0403021c020d0f0309 69
    0x41c45402071500090814003952050075610401c03d1134503d100cae0020029140035165402c00042c207141184030b500441110400815100803181c401d540f0f06240403803007401180e038452800010040300d4024040d081d0310102c101e03010001d2181d0640001c0e82c030f22a141c4024022071501c508516801d20030540041c42c2c544c00401c81c1d050f1000d1250107800b41000300c030704070002420040007840e0200d0102d03403079000d004050324030340081c0c40c0040e40310402c0104204100d00320740d41e170b04807071152401003020420480341000007805505101e018107003035501549107201207500030802002240d0380064104d201d446203440060700c41070140e40020191100b514030940c10b2007208007807620303000c4e078094039024205a9200c506015076200004503c0c01d043d0000303512840344107451303551880c14000000c01481c0f004054200c07015160342c00c03135506400080c9400d900144c003007014411414072101032564001c00c0044142d104901d540040c46040d00501c004190710140882d210400d800758003060050500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 562347715 1250 562346465 562346467
    0x100e070b120f100e0601030b2d0a0f030b0a110d0c050a091a07020f0321030a050a02030c040605090f0603130506060607350301060c11010f02030a0309020411 69
    0x200c500e01e6020300401c1c0c80c1825074020202c04103402d00031645111040355903801c2841e505607203c90040d00200b0200c00110f401142d0418141e80400550758102c0240880200c0744405501d01003d0040e0160a9080a0382085e0340c0d0034280042065400210752190318a2404641c01161940000060080c007284060150804240b22103040c0c010018007240280e556860400a03038403620351422280412454215640030800c100140c2440400c03409101310140480f8951800c600441c5240003481541c2a29070304048244106c0743d146026860b003080800c2d20a40c11402c054003105114407c5200708001c1c0240010711351029100c41e074040049400041c0790070b17160300d840d209448106604490480d40f901800e000610b8601d0321109881e550303a00184080c1207951300c40120155071502c030000c421500a41d14060312112000001107019001c030390f54607240c4420910701148545020034210f41402403005201424907070010a031a90200c42c4d01e004a001102800882d006044040d038140c101e0318 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 562348965 1250 562347715 562347727
    0xf1509041a040804092306040207020d020901080601150509032e11031b0412020609120a081201090c08071413031103070515030a0b01030e0d0306050901050a050102100e070b 76
    0x38012004d081210703820401031041e9a2056410014a03001303c62225494041501040d0a41000c0d03003e024010300c007800c10084040103030005214104240d2082110703a11100c0180010036070340a00c21030559030360400a0506c040310300046c5d210a840300f4006140b4903c0552404047c882038100c00c20724211900c1009200c0b800d07508161558000c59454890004040d2010040b000b82411074044458072450324081ca0299405c03c0780300d9102201c5250310140b2084004141c03c01880400c864034031507a040356075044405150924000140d001c3c14490f442e000c2e00031038403a04000301d00e52008075440e10143c400c4100040b0306031402098428110000e001101108100f004142103020403011001c07644007581e03603002c0043e54002ca54a04149400c140042101c440c10358100c0360540205060200301d030380600c2d013134602d000c0440c5521000203440300350401460910b80181400b411003561005a280d0074540085d5440703400350b6580000e555999034115014500b0b0003044007414120303001c1e544e141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 562350215 1250 562348965 562348973
    0x3061908121c020310060e18180102041e0317090303070f020102011506020c0310020c121e07150b03010e2505090c03071e12021c020309150f1509041a04 67
    0x452030301030407003c6160346030b50046038640348071a80d50000917050003070465610719500001d110083e410710941c0399024330010680d505013605001c80c04400034030307d220940c91400e01161140400c000118040030410505510340c802104445806800c048001d40340a07092004030f005212245520682d81200e00e40419195030125940d88800030807030440d5080002010101c1c100c1c440d1580010b11030380840310020070315044901820342042604010f8408529518491039a9403010710101d6030034003140b040303402c04203080c85003989000094008210f140308a5011998900d5108a0000040042100440b0020416644501900010f40180e0700e030300304050500320540040c0c541c8030110300007090303404620281181452070300560340d59202038010250b4081c0f009501c24600400100342c0381c0041c030900c80031400154040d4540a000f886182800c0c0b81e03c9030501d4015180c00440307c8030740c1c10301c0441820700901220a02d000c8425090350346880c44c0c81c6c0101c3c86c038a00120b82d4200b000301000240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 562351465 1250 562350215 562350241
    0x40218040e06130210140a26070221070f0623040f080a02032b0b0402040f0504050702030d290102030901023403050303061908121c0203 60
    0x10282920240114000c000704252959001c0340c202641d60500194000540350041040d81018117a00b0515011030414048121581c00042a100800e808840a4070350a5924400360604107107a100110103090540c0025281c01041d8800a01c0c1443c00c5d01d40401340941d00308807595140e008045a000d030540d454281b000c0d001130b031884803094000c403200120180560300428070482e444100843d80d030703241c2d83c0e48000070b40148036030100b1407006208190240c01e40c107101c0710f030314000d07864014030358040c072030000742940c4509504500903801407004002481c00c1e04072070016104100e03000303d0f540d512448103c1c5140610082151518240072000041e90003400c2c200700743d81c04030100080c4c0f404484005a940b0300c0741003030040c0141e009000c000401c801c21601c4003408082841c00b02c00c1031048940061307150b4a141c00560300341d00000240308841c0360050f11860103103114260407400714940141184c560712a510318880300d000000302011340e03501b5010710100c5800c2e601c20864807400d0104e086802 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 562352715 1250 562351465 562351507
    0x9030304230a03030e0415050301050f0406110421030c05250905010e36011d0604020a14060f030405010c080916060311120718140f100903020402 64
    0x10244905040a601c1c0c181100d0700e800341d94064440400c12001074007400003d0540b80c1542807040c0881102050942c2c003030150318000c002007920328820b0f003440c1c01c025040741c50780215644140f40800040200040f42d09040c40070010840b100c50641c1003c0c182910a08800500240b09029410728030800140c0d08002403142016900708024080d00ca00c100e40440d0401e014000382105240005400c4000c2d4409140b81100c01e014040621120742c60040c01c002d5482200d1407269455150710010b0850075403111b020174110074004c141c1801c2540100740d100405001318903004010111300c00654a030103045840f05d10740f591a55a0340e2a1a0030810b00800070f44401500182560300885c0440c4000501070f030641030005010840300d445d012099009000d4403210000d0750b070042c400d01c0f482c07108007942113104a0300764071504200140e549101821400035009400d50354410203148002e0748446801c452100c4056840741d207a44800c181c01e8903400d09035480258041d000244106c0344060014400d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 562353965 1250 562352715 562352759
    0x703030306051005040306200408010b0916090608090c0901140306100b030c090114180909030a02030307050c0118050c030c041a040c0c050a23030c0d05030a0209030304 74
    0x41260784440400000c0d414224640f0300042d8207110610115210307902100d03107001c07039551402025003403401020154105d90711118450355502a000d500341000d0136000d6015070500140e000d8620004405400c0d0009800350004000c00c440006494803410400c0280e121030050200f01917613540e40b4481072492803892801d00030301444011580060740e99082070240c54600f0030a07070841c1c1d0b840121903540d400127202d080c100200071005507440d007005001000c2800d0301c0c012031290030004c0c01c01c1c8600c20002502e40082c550040080d44261070703011040c2da4000301d0515000799640380c8512914090200d60380c10004162140d070003a010844001014840c215056080c1c4400041c0b440c1000112000c0f04211540603209404c0c00172145059070140940f0346950074100030100540d140e203440d00010b5032048986030100c4040017080e014111044010340c0c0403030004d5141185a98402d0b441391501549141400008004104d40e07a0890301a619402d801400301d90b00d55995481e10070511028a0b0400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 562355215 1250 562353965 562353971
    0x1d0601030c02031815160b06150a050a05091f17130c0909050a0f1b0509060d0b19020c030315030d08041e060e0309010216080a08031f0807030303 64
    0x755480d070003c01680d034002c85403040030742c1600c0b02c80c2c1841410000c0c86243c441c03a440c10841c1c0490325000c10841d4010038010300090b0f14914125040c003c06182000400c0059102030202141c042ea000d01107414004040c40e100e9183c4c2c41da00c000c2020105120100c91200d101600c42811180d8400c1210101144520403c0030300d840d1080c1c10329070554200344c06011140c501c042403100c82e00c1604803411061040007103401c450031913142e84004030140c0a0445041442d1814600d440c02519010405440b0840d2046203e04203c000074180c0064070380024015803030100044c0c1800303092102c0c54005020384209550300d43c3c40d415942e07204d600c02c482008210041d0310482559040000b4018090440c545402c0c421351160307211060500010801c07031016070072000c00d1400151050040c201c1b0350441800440d241c040c80740001e0308000343c80d500991441140365080011100000d90103043d10b400400c029500c1c2c65404cd00002c001055040050f50800080d0008086500044550481e4001d540070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 562356465 1250 562355215 562355231
    0xb0c0a0e10050405120f120403050d02010c0813022101020a140901090315020c1501060f0305040503040909030318050604020306011a0307080c0c0f010b01030e010b06030406020c071d060103 83
    0x20008940601c0001c0006000788000d204900f4030780030340410f2081c0d540464860b04095600180b800207800d811812105000c00d040041000030031040305030f5a120300083c0f006100100c001840041c004041450500079101c6010035521265458964084180450b24500080850041c041e6200414240004855428056044451100f51114014160750381c0d016a8559100c440c00094884c41030408190b0802c10082e0841b41000741520704400a0f0451001d903150140c0a442440c0200e03030b090034541031100300f000064001c01118140c0d1000301c80064800040e042c11001444003110725000e501d0112600014404005400d41c46a03108038101c60f441da0700d070340d190880318141e604004001082031000c255203074012040e0a42c00034042c00d4070390400e414000714a10b040e031690b040c00c3c1c80d81d64900c107981031541e00d0700560000205a100074880310036990046445840014005400fa030b40c0410030b00791a08003804098018410031500c0c680240c3d060910301003400d0244c40850110b8608504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 562357715 1250 562356465 562356469
    0x9080705010f0b1e030c01052104061508010b100f02071d04050613051902060d0203070e030606011d06070f020d03050d051e07080402150408060a060b0702090a02070606030b0c0a0e 79
    0x240d44229005e8054036030103201c04c0c019201c6800034400d40300c1100c440001c0c08642c26102070103500c0f803809600301290382455814205051103054001c07a040740d04204945420780c8402180300c0c0c510455150260008030410700403400c04160b5040f001a1403003400340c40c0e00502c3d07045032260160340620300303861180e101d00c2141811540ca00300700620b1504032181b10ba412500c0806500c46150012380150f1414071043e80c4082207910440b1103201180306800511054201080401d510003406c3c00e06003110b00c5e40c0e022901d03d0560b07207420301d40324000006a800c2040424210207075410b5000c1d148a01109140c42c001d440c07500500441c0208038980800150f2980d6200c14008407004200a41042e0b40c944038411070380c80d00010310680c4c001074100d0071078a0003028038009100804400c8064040760428500103815145980e02c10b101030706050010344056528401e00c660050800840141e84c0d200c54074203540640302a600160500043d4420041c1c040603030002004100010b0356000544600881 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 562358965 1250 562357715 562357759
    0x30702090603060615090409020607140d050f1206030a02030d0503090115050a0311121b18010e0708180a12180e01050f060403060c020d3009080705010f0b 68
    0x12101e61120b8110a91228580000300804801300058004039810010749c0110f03451b907120000c100e40340b21000300440d000700d4080c068854192820304d0214541103041c45500e149015192010208141210205003540d80c1000540403561b03001d41a0f441146521a000d8419001280c11160135402c221003002183e986036141403e8840c001e01d01f0081c1811510b800c0203120110107600c0c0c11010300d00e45019481410000220381c42c40327456103600c59511040500c8007031802942d034090010502d80040c40180091030001e0741c040e51529101545540318035940f1002410002c0c06a4140600c01d20b140920203c0c86a42903694400d071181d102088852500403071001c0c162040c00d01c503008280044c40706103490500c0c90090f00004002504141d00c0f92508011510380b50441400f503402500504d02186d04502222507060b00c1c03204407803107442d08514185000694509425220703942e200131208022070001554071140d00040200b200e0b00c020b0340c102c0300030407544020b144600400003510b280494400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 562360215 1250 562358965 562358971
    0x711012319180f11090a020423090109180606081c1e05031e101706010f030326090604060b0d0f0209040c151e080112150b0402070503070209060306 65
    0xb03100300b240c070358060716141c180d0500000110b41499210400100c01e03907502005a0042100380801071b96103240030603440c1004d980100340880c03500c401304561526940d800f026811a04640c0c008141c00c030807410075108503100e400000700a82d10344030340801d1900c0009481600c00040c89090b208403c11008256050590b81040c13140c180b8001c00141d40043c030400145401a0709110320f0303002c1c000e0a04940c01c0196048526003c03140500c0d1040000840d0140c0650b645844940070700041d5050500751160390303d2074000a0144210042c50150104100c6066054074903240340c869841d0821036581602e408050f10203665041c02c224008005243c4030310403001041d4442d203040c80216070b030f81c240070303840800903c161000030f01508005401499641406c9039415150350300c0c80404402117514800720000759004042004410042c40368441506543e5000d0790080381501a002c928112030010f80403e06956420500108015041000000107054068800c079014400c0369166024195551421 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 562361465 1250 562360215 562360241
    0x1030c140d0b060c071415040f0b071104020c010506101d130e030723010c080a021602030f0a200108010b07110a1701150e0711012319 59
    0xc01c40461152902c0c1c1c4010030200010344040d0500d41c6101c642c60501c9007a0340843e200700360401e10300005203840000031f01441c601540440c03c03e410301081a1040081f03001da6455002e0000314007040c410000c07118400030800410039503a40045c0c0140364003900041e600c0900403074800c038005182074081d80301100d0a400790144d4520f1120b50004000c96070361101103074040c540e9100711840555105000402c40140544984012007081c0c62005198034042c1c1c03507040d0264500b800b558a240c0c2c0c412a100c0d00414281005032311240c41c0403110908040103032000358544961401b865001e6000f1801c401498047d45005080a044140350507001003007090003030000d122200140860481c0760080c041c4035000700e29810750700314000c0210f8003e0010342c0201440100e1080f140011410900591306080621003119540b2440d1403002c2c40022000341c081001c3c406007140070804400254412001c5034144015140c0450038400003040c00300c020350356009012146d100d5503a0005c186d0003008001303204 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 562362715 1250 562361465 562361467
    0xb21010506013603020a0603020a11031c1a0a06030c020f01022107300b01031509020f0f0f03040302010e0a0c0b180301020a1218020f04090606080313030201030c14 72
    0x1c0034090115450184800c0b803440300f820011001da1100b8040501a042d561001a61549003030009030401c00c00d5811205654002c0004052164070b01810045003044514007042c08403029450850030390074240c078140c12024203d40040c4042d411340042158144d15000d8942080072004094240d218200003c18020700e0991414114402080c800d9400609450065001c00d4441606d00d5411107005072668481140303500100c10059500c0b407046007035001d0a08206054010001d0f80b4038100502c144c0b01720903404980c4841d102400000c445900a01c500c0145e40c03520407000c0f203015a00103031415030040d0700c0c03c800c0000c1c100b0002402d8644642002c00e0490a0740341142c1c9040a6010314000d00c1c9075240800c0305a0203031401d0000d041c0c00201034803174000e54000c807403980040310000726240c1600030701114240f0240e1280c0781402200740d016540031807600890305012000c3c101584c08925a4440020901010020a124902036900c00d98007032102680e4100100c882c0ca483e00010380343d01c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 562363965 1250 562362715 562362767
    0xe1f0207051b010e090114100906081b0f07050604110f150a1832011407060917041a030c09010c14070b07111f11010b2101050601 57
    0x7142c0441103981c03282c14074241944107819000300da00710000713a2104002604a0b0700d05a542d140c010700fa03d541010714034081e51403901d40343c802044010701410101301034a01500042e107807610203044898141c0c051a290340e440c5410319095680b581d007290251000000702c454501c4070724004000e120b2502c4020502100340e10308222004a5a110b03058030414060300800c0e183c486000320b056032004050400c0030722881c000a000c00750042d0045945040350050f19040d000c03441e030b0000c2212050400c81c50b410340d01c980052401c02c0c020148034801034506420900c50a0000c1140401001600c2c1c0305000b0701e510300c2c0320740c0410175280000e81d040c07034204406021010131540b05424030300c403e070700074401108100d00c2e010407542081080e0704800d080d10f40005012090000d10070341d4900b01001030300c0603180c000c0c502d9007403135190003d01402004c0000881710650985c07000d40003000440c000801182c6102c640e00504140803050100390802c55081c00c0015003550301550b040303e104d48480b400840988 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 562365215 1250 562363965 562363993
    0x2090d02100e190314150112080706050126060c0405011b0605090d180302030607200139080c1c090b010e06060703020a060f090203010e1f020705 64
    0x4510055090400c00118050a02943c840c0b04030440386901c01c002100840c15070610f03041070080e01d0500200d5900c2001c010b034566490742ea038141194a1036199001c01c0002c0c0c500385c080340c030034504e000e0a59414140089088031000c03071440c10901e1900440800c80300c440a15503103031501181c08821b01007092004100350b50003184640c0070541029000400c01c00039581e000e088035419910703558250b10a008604400c0d8004070440c420701a218000780080d40745a002a542e440024a408100480d2800c0384c440c001c160029108940a09002440f041c50611140c4001c0e0b00132401307025682c0308480880c00790407522920103c2c101107581d1000840d990301011440300d540310607003c0380c05840510001855040d0341c41440b1004ac407500041031740d07501d04801c2e0300703401c0c001402c59882410100611400250001448054039a00c44004030303000442c0900d1100034065140c02135055420040d00400c02080880c18030900b00341014440390180841504030224012154000d04ea603000d90700c04d900321 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 562366465 1250 562365215 562365229
    0x18090506040207050a030e04380d0b070e03011505010f0c0201052203050708122d1c060807180e01061d0115020a030915140c0f07050402090d02 63
    0x440310281000d85040507603070310f00b071912102020940009510640382070a904e004d00410100d6170b42520401c2116051039205040c03141640c0148409417400e00721115991180140880c0075504401254200e1500b18406048101c100d036040d4420752a1255001104045540d42c0040d5801a50b4425800700301c0130003999034070302010040e414000305202d1036400481d080302c094802183d081d2044101c43c60751403c9894000d541e00030708904d800524031030400c148854180c5842c4191b0301684e5009105581001c100c6684617540304240c090001100c0342c4551901984046010004004000051b070300c3c0181601c0b05036901900218000c41603142e625180280c01a103040315052000045040c5e4881c06102c50811202503480d05054010041019103844415181d1003105800030300000d01540c1d5009211800f1801034000c00341c001032180c502c242c400d02405443d48400c0701410355800780c403d40c2c16a101d01d00d0620941c1c0c0c0c82181c43c08149420a80280e4110340800341407044580b025a0810001f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 562367715 1250 562366465 562366471
    0x51f05070f1b080f090a141c06060806070c030e0306191a040e0d09090c05191e0206060f010915051b03040f1401030528020903011d0c01180905 63
    0x40b10031042d04000800c580400810802405601140d51144080140401c080d0542c0c0b203800036904040d038407011600d1355540c440c0186800151075145c19064500710b002045280c0100086104100c100038a1a0700460710f01c034aa806a294000c0754583c21080540d190350440f41840e42c6001c0c01c000c071040344202d03001510040409501c1c40340c46d030015001b2501700c602c140c1084032140c1c0003a40c0900400d80002d2083d015000c01d036030500c20b0440140f8054142e100d6036502e2807111100002c1c266205204d01c1140000610030080200b18042200000755900400c1e13404512507003440e40c08100c0303907008480000c12220303109030190081240341000d9603260800c007108400c008408030701c107000b0441840184050309030035611007011810702e1050214a444090070a0602d0f1070403007400800354110448198810035400c440c07a01d000c5044074130703010340a4017651503019801c10801c2c8130980340c803d140030f20f00d0140340c0446400308401c0c07004699070005908948092204d4500c248400f01e0941c01c8298 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 562368965 1250 562367715 562367747
    0x309140303070c02100e041b0801240f030209041a10020a03080f06030703020d03080403020d0f0509040b060d0207050106150215040b09070b0304060b09070e01050412021c051f05070f 80
    0x703004070b42c01007c203064a4503500488100c4d408001860105600104480d01400014820503c1b1425000103c0e00004440c080201440120f229140100f4800e804071040600060024007804900751030b4501e5041a081c0c55910915207c940d5181c0e0510005900041c1038050391031400548640340204140400540340c030740c2500401d640440943c55072150000124031a03601c0c41d900740307020f0a000f41051180280002048100d0310000503041c0d1003000d46100b603a00b11000185031810100040607803140f8007090300c5813800443c010301884010b501c00c40844504404210a450341c0100072600e075203d80715810004090b035001719005c100d05000c91940030402408880e107242c0c4804804074540c000f1103007101c4081d111422005c40d41407100180d600501503003001c984001203000040c0590180b40036a01084e54031030b80c07181c05d40da100013600742d6810302c1c42603070700031074240342000d50321400c036901c40c010000547d940e00002010b0701d108142c0310714040e0752420000701481b0340c112058020b5503100d00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 562370215 1250 562368965 562368977
    0x92003160309151b0207050a180e100c02030c061302090f040c0816090e060105031f0b0636090403080c0904150f05041505040207140601060309140303070c0210 70
    0x3d1507040c0e030312a4044102c8466105a00500e18020080c44c00a1036001680503c0550800708010031580c000034600c01154a4040703071242d1000204c40c0b5001e800c5c0c4038040f44504140c1350314200c5030084020041c005001068400954400003840c00215040320025001004100003518641c030403003259400c68072983c0c6401e8499610041c00e85400302e201c030b680b090744c49416000c010420381c6100b0080110034041c09062150f2411001903101c503c81700e02c2820705498514140d81c0e070b940a510102056000030303c1561903140d140ca80c58480d203100402079200b28900c1c012241441c09414180040003801000c2d45042c0e174907558100c60401000c0c180c912980000d000c01030883d81d89009408013451800c070080c42d5640740c51203a0342030201c0d40e4040c40c0a240b9001401860040c48100003040d104165009a40e0b9503452074a040794140513004203d0310300484002060380c0f039164000d4004580529030500138208515403d6889200944030b0740042030311400b0010041c1807040344054401542d0a141d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 562371465 1250 562370215 562370243
    0x8012c0709110909071b11030c0a030c0602070609031205070f15140a1514060f0c0c011806170c0d1d011506171f092003160309 56
    0x207050703981c0c0c10041d080340640403d81000d2410310502c155031011551610000c03041180c11120104800b1a4014100c00303019510741001d614108481c40826601a1807290b1281d681d00b000d802c0c1c9945400307400e0060091306000150300d03106005000070f4035080324504007402080d07a02581d01d07500442e0300f1600311480c4800c2d100494034160001042d400c8250000c100c462044d0200c50306103030300901d45a00903290220a6080126421440d01550123a42e040300800c2e040d00e000a5150140d01d0007444d02040000b404a2001d0010581402202d001e80b115000c85038600f6a44d28006928050b0380009244003003c1d004094007044169004a401210305141603103200050055841040800054107035815094054200c01d110f8842011401c41c0c0b10400e06007441e10050040c40d8007418142c001d0040400709000302001a08014801c041d0968080040c0e80e0b00304200147c610110300500740c02403041542c40e443c1c2144110791050a0b8507801c0405460400002d40c010548000e040d03c0e004014420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 562372715 1250 562371465 562371479
    0x9030909050405010f1113050906030319050d06051804030503070c020307120b060406080c28170606030706200c15030118020a050910030216030504080708012c07 71
    0x751034002c5028030b0010842c440080c0d50720b0162101d04080c40c0c84401d04021341d40d07054280b849208242c980894101645440d581c000910b540141402c150403a040c00c0700074003400390840e0081000322440c810a00240d562203082000841d01ca01c400e140101c007281c0081c0009105038011940140300303041611100c14282c010914013070664018a01140c4220040010301021100c00c40d841034048406025941c10325002580380c0b4026600306000e19407001e83c80c0b55020507000c0c00100e0104030084050b085a5031701c0d210071381c07940078158008103010302d00c00b0030704508021a070303001920400d8071211a000d8590344980075a5140507885034460040890401a503a200034065030084000510540ca9506014041141c010318030065614148104505198144c0180c00e03101d2a071012102d012454007480c2c01940644031304400d150b03840c410740030280c0c00c15800c000908140c0c0c122408590010307464140f030600304c4041840018004002d421803401e1281c1d400d0804c03007442952815154003076a01c440b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 562373965 1250 562372715 562372721
    0x6011407050f060925030521041d16020d0804140c030a08030117070e0718030605070f020c061e0d02040b2b05041113020906040b0c01050a0504020a0909030909 70
    0x150321314290b044440c042100b042400e0207142d441d17400c48803c0d00880e01d1640c2d8955074040140742000000b84900c00003400c15103500c00c0d0340041c286004881442c800120f030482c1990021915407110102900355550382c588005198000801e403034413070b690142c4a44e1507010364030411a1030011207200e54020b03501030b40c500340030b5246860300c00d0020917100d50521030f00e80c212400d8290071490720750002c8400c02c603180300e00508507000591030800320b091181542c40b0f00b59070880340c0c0000e40454100000d00400c140c0c00f4a007040078000c2682921005500d4104000a48c070403522101400040040c9104201c3c0a050041c0801c030302d450001807810f80e98911800090b0886130950803080c0d024100c50540c0c0418240c450100240038000700308629060395004800d000c038140590090761418250310170000e169040783d00c101001049281c455507a9007a1071300e154058183d0030203550a22011525a000c540501070142c4d900400a0740382d94103040414004080e0300c0025001c00c1824007000400c0c081c688 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 562375215 1250 562373965 562373971
    0x110706051009020a0309050d080f07050307020c0d0311010605010908070302090612010c02071d010605030f09070e130c0803040e04021504030b0408070302210301050103091502031305060a0506011407050f06 90
    0x144010440c606c103402e00504080e0002030000a2100e44420001214a04030009074002145d00f4103a850344c454070380891501c0e01040882b134000e4034440e880401d0613003028240b04800c081c003000f0300c040d940301c8004490a45c0540b00e80c0001d98020790051005142c1403080a521a038054541140c403204200900d0964020500307420240e00843c80a104076215000b005003143c6d011004001c15501d00607000b0860f1200601c0340041c0c3c100a808a00091020700001005104440c40c80902e800c1030250040c0f5001502d00c1111010b90030324000411800102c180c03004c0346e5580040b00099036841e000c0c0040c02c00d0b100310102005500f04008070000e003003052441d02503800784120341d40300d42700d601d4080c0c5003144186848480c0000740584054060103c001c0b01e054078030a18012640b95214030307201c414900d05d11035081495001204104100554808403a140c9000e201110b64649850200408407101506c0c003070b0020b4003044141c1c20500e1210014888140b041d000c03a440d020101d0892410b154084e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 562376465 1250 562375215 562375217
    0x2090d08030603070909201801062f0a0f0212030d02040504050f25020a06110d1503030503040206031e15041a060403020d061b020307030909110706051009020a 70
    0x1006020352810100026805000107003000c06c02e030306250310741040c036030f4100501c0d51545904544e504443c0e1690201814075034110800c01c041561140e0020384003043d1069010021602010001000b116000603c200780041c3c0d8050a034600070394940500c031040c10303041640c01010003048080011005c20080c0860b09041400580301c90a02c003c101c103542025107144001d400c0e03541481052a012030011032885003111100180402e0080c05900300308100e0400340c1140d182c0020000049500340c0200b01c1c0301e03520001003004007105498a0f800d600c0030700021380011003d0000130f0040c20514002c5800620341041c500f01e0b00c288940b60f10221038221004c02c5d41207400005030203142886e0040d110b03030036802a500c2404284480c0030914501640c88042c2c4900c0340013022400b800703050340c0042101d00c2c0003180f550328503083c0200650750b5071000b85c00b2800144032180c0014140124030440501d1891081c006103407105a8860700301618000e858101115100b80740002c4951592004002030f00761 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 562377715 1250 562376465 562376467
    0xf02130f0501080a09120c02030c0418020f060a1e09030b0c0d0501050303030606090d11030105040f0515160302070c08100609050a020415050d0b030321130210050d02090d08 76
    0x90000040444030f01900d0211514202400345e0b0028080d03101c0c0a01003170451416610404043c000249095907460318a0b800c20b1038502c510752509545a50601042d0003034a1062903a0b94440a000c8a031080719040c10005800780381900c0d83c4061600050440075a5103441c041300c2e070712915a10030780c3c10151100f0345154000074401c4100810b5024050051004801460452412402040b030500c0340320000ca119617080e4000c1e204110006071218043ca1010300200206c2c0380c2898201070241100368207944600ca107146590414803481c80e0141301c2c90b1044000d60307905080580079000707504400d42c1111580702d41d04000c60841000c01c00d040c1c0300380d401500420320600e09002c1108541001c0c0003120018010401881081a1882d4514209026203402541c07a04070b841c850740100101c81c012a418000050203040d9082c00c610200c402200c41000c4500b0340c1c54054403c1200618600c2c000d412440385c0c5200c0000f54065406442802a40e10000d880c01d00c400300000d0040054000032692500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 562378965 1250 562377715 562377719
    0x10503010f09030e0139030809010b0f011b14070906050d050a080f130902090a14010c0b070e0310140106080f0c03100e040506062701090f02130f 64
    0x16090261000c80d48024000308040b82c00e50310010200b0b5a041d82d44c505109810b40d04d01503984408078600c0650000e0304403140c2c103403005150301071150002d44040d00050002008903800c1e40c0180314401c00010000d0151054a00190041d111a2150007060020081150155010403500143c806a00c00e19002030142141080c480404590310b640015000d4620b2520400c00208001a40070384150820020b0f40c640b070f03605038031519912820070421688059210000340224054000c2d10541200315901050a51900c1910050b4400100c40600242e584000000401c4912404907080082442c000e440d0303600d0304004c80e103080400850860003a984004cc4464502c400715494094403a51404110350305110b501d4004072100038021078004003001010401313000007540b51500404403a5000d02d810328050074410780300c074001c840c1075004100c487d98101c0c1ea4050840e005000010104800d603580c5d0038031010f00003c213911038029005680c20070280c052402c14210500080454851403c0301074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 562380215 1250 562378965 562378969
    0x20705390409050a0506062d0603040206040f06030f0f0504150506061308070e1806011a120703050631020c0a08041e05011e0e1809100b060c0c0925080105 68
    0x652340c1c150400040b940c440340d5040310260001d510b18101e542c00d849450b18000208540b08540c49050020850080000d01c941c054000e400c66020004040103140c884180c04400e4890031a80185102d0580c0b03500041700441e17034040e540081003e8129070402c2803400110300c1e401c240360070400481c0e2100c03800308210026a0111640081007038041800580c0d0703030000981e40c41060048482241441d00c0c1200010200b0050301c0400c105070705c010982c0e05280c000540101030503100a070107000b400ca9200d0180c41c00440100410440700042024001540c4c0c2400c0250800501c107501350080007100008034203080d002d40043c0c03d0b130307044542a111100100d02240000c651281e4140540555428100340a80b100d4070081c124600b1b0003651040020001005244c210310340e050141c0468050000102d0005840540700078880700400442074040c0801615003c0d81008001301c1d4090201120030b800c00d0303280c0c2c035000911444682040503001035003030000d0310038100c40e800145402004011178 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 562381465 1250 562380215 562380229
    0xf0c09061e050306130f0c0e07030e1518010204050603160f110a0f060f050a0606021006050a05040b03030d050a0213050d05060f06120a0501020705390409050a050606 73
    0x4070180d0740d9045500d00e0003011940f02d80c0002c1c02c80c0c503080e5600c1224000e22180348241100c07035030702003e0551801d03200c80030b07000c0703801d0180e8100001903d40208040c203400005148d01200302159008181f6a5801050500809480503030700802d540078000007415464500c05180221000d4031080041c01c440d500050020120102c4c210420203000100a00e1000125003255502d0300202454a0058035041100103001901c01441800340380000300151100654441030a491055003544c0000a046405000b40c410340d000300c551000c0364040c20000d5103000e61102c41401e802500b50713070400703110100d4501120700c03c1303c26500c0305800103220561050003140110103000c04840036050348090f52103c680d100c100905c00761314140b07401c000ca0400d07524080070400703080009084030024821450200e012f5001501d04840503c29041104944c9080e40124190003440003070150500e942d01507112089844100c889800c503984024050100300240100c5d00e50900a10045c0b055003001c00a000034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 562382715 1250 562381465 562381499
    0x3110306010b04090504060207290c0405060301050f240304050c0a18050601030b0d0602120601051905070f0b090616020f070e09070f0e0703050106050703090e040f0c0906 75
    0x1003500024014084109000c09440030f88016410000d055512440d1020082c4640e002c003a040f0007642040c100c840c01c40040600e00e03101641c0c0e881c2c0090321840d800740c4a5016600a180d8031200c1840180401d00740442d40001b031304001082c1804050384000c124003201c11a1109010740d8030f00000b0070041c0700341004030901e0309070251604540c15180c0030351690143d201943d04000d403a1904003080460380300743c00140e20814010b01c0401100c030303245410b0000313600c418600700901d800d2100148444d801007060f62960b010401c110350514250388411140c59102c01c1084500c1e84407490304002040c0700692581c42619244000d01060034000c10418482d0550700c4810215844170000300340c400c402150354003c40b819100710032110340314882c0690400010b03070003007440010401c100240c034424a0411502400c0d441e10108a03590300d03240100c4082c410458040c01103410721004102d01e4107251a641d50082c0a007400e00c0504401e681c1700b250702d00e0264809042583c46060500c41d4000c10405100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 562383965 1250 562382715 562382719
    0xd090615090e2802030c271608010e18030d02040608090703080405060c070503060a02040608010e04030c0b090c0d0602030108010b0d1a1f120b0603060403140901020a050106030c0311 80
    0x98141e43c850766078000760050b00051400c03404145140320840d2400c10900010308002030000c108061005466100300100040d0250082135110102c0e2496052004000030401c8958441c400e981c00c08215030b40d010f101800f0581445616000c80103480030034000b82240f4080d250001d030740e40b40307480402400a64060003264107030300110000c00001701300b002110220340e41681d41e41c0c1c80341d40b128021420084c10f030b4411b036014080c080820012113613582c01802660001e403610380d4030366200d43c81c0a0f01c0c0c020445006000c1030010501c0030100352540d8050354408001c03012100910104800704006444030f1000300c45c0c2c69000707c010700c0816801e0060000c0c9140c144d0304020300d509192160a421790b5541144c640b410a01030200304040c03020040b44021071824260502100e0740c0d02c540e92102c00c030340c0342c003a80c207800d401020bc0c0306440c02081303103070213240c05540d005807003200180c54051591003041041c1c15413245242240c000b66080c01802c008500805110301814618100304031900051043c0c14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 562385215 1250 562383965 562383973
    0x90c070f2001260402041e05010b0c010c0f1407060902030a120f02010b010507021504050a0e0105040c03020702060d1104080d2102070f030e0a050409050105091209150d090615090e 79
    0x210a9001c3c22143c181d200d90120b401064010143c2c0d642d50182d02c030114501515800c0900100f018002c0380c0043c00d04c0080030300200040c030a240c40840700860b4020040d0001514246103682503190040a020918000c100000d40390280c0d600091805050000c1151401e04400002a840703030080d40508009045000a128803180d08000034118494948002d00c61683e080c6041c9500c044041039401400780500407262054492034031108007102445a14440c42c1000d10032600c03548a4001c1c0e4005030707405000f0508101508a5200107044458252900ea241c00d0000146000c410040201a0380c19074641e00c48071041041000d10f4400030004407800c1030300403c01c4100050101c24203600c015098604644034124400000d1700306125603211550090610308a1030038018190b00c12401021240c01325210203000a6030b84455001d4408002e07800031180200004441c2160018015041300c43d07400502070b0043d1351603104651080f880c0e070304210034803074061007102454401c0b4400045010010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 562386465 1250 562385215 562385267
    0x60405070503160603111b0a061104050f0904111c20060307110a0f2103050415020c011503030201050906100e0c071509061e0506090c070f2001 63
    0xc500c522003e1300c2240f00b0107540e00c1d40740003074200400c00d8030404150465800e031015110030085550300d240c9402510480e11742400030741d03100c0c220022201110000340180118468400401400c424011f2003034502c5440141042d045030b0303443c60002d5805615000340c1d071651081c0e0503c03130351007080e90441c2010302015801140b140c1c0d0300e440540ea2b008010385010b03d035038005040711074103210340c016000f81680d00c980300d030104101e0f0400000366128146104001110700c1a1812815180d06840c09810007501c0860448294002c2d00185100020354002103040c1d030ba02e800d401d0b54110180c1c000c0c0c005035514414014000c206101880d0850180550070b03035550b09113001e2290009002e0170603200c0c82d400159400400080341701d801e8520f103c44a04110014145c1005006014a40c01d808a4101c0c000303840b52050b0b10902c10716000f42c3d0007403d496138030394074001c0d41202588044000d5540e81c1100007445c00003515203407241012a607a00c60300c41f103030340c8050026185031518008244403845803004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 562387715 1250 562386465 562386493
    0x503060906061e040b0a122d060f0e07030615050a0804020a090f0b0108240607020f0a0602070806060f030a030f110d09031a04080d09051e060405070503 67
    0x95508100211a150750301d030607074850501c42c040f07003881c103024041020a0010341a6074142c050202002c058a50b021084003680f9010300b207514611003c0e030010002c2c041b03881b0038400c0549550741110400c000054168644c4460703590451513900c0300300981c0b1100200414170794540200f2005240c101d4240e141e60342503040103040e9006910320301040007000c030300240565941400050003041c15020800c0550250344115015200d808074581c0803808c130401041c11501c100300560031150456080135509021081000884e6102150990380040300c2000e42803280e48541410005007626002408120319007010075042c00c40050840707110f1340359410359030180d44000c1740d00582607516180040c2851030300d4100b40c0e4582103000211446103d5403608100c02500100f4000a903405055012030302003000605a8050070200e400400c002c3e81480b201d18054015000075075284e100303400740c8030001401c0c94581104503020307850714445d603c50014001440810310111014040940282c541705410460f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 562388965 1250 562387715 562387729
    0x807060807080c07060902041a0102070602191509020a083a0f120c1d04091e111e130504031b05030d18052404151b09090c050306 57
    0x52091601e1000411a0401041d42e01c15042c187c1d00900401c4694014012000000e50010340140503100d0544045109400040d1541c4a450640614225a20b0559806045c01c0c4101000030150391600460b000507a01e0000c140e028001c144010101840015581e0801c4c62a00c4414418640461401c1c11001141048079454101505100382a801952005c4071524107241100c45840d04c1c20751200a596409880341c1289950304400c600c07842c610100704411905140300051a441014401e510984007410055242500441d842c1c0c4402c5554070200c2d00861000020050000007024400400e141c2081c44402801c0c00d84800c00652800c2d03274025091130681004d00390301c00c020b032002c4001c0010800890b2409030b0901403d002002030700c10312800b400c041712000c94041c000d9070b0302141c40e0705c001c0845507200043d0440303003645a00e80d900e030402c41b8200810715044094403140c402c507402002c5070003144030012698441181c00d03d00b181d50021544008814000c20600f0020320015176a07550f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 562390215 1250 562388965 562388971
    0x180b040605032d0601021216060b0a0f08060604180b01052418030c1008010e06012a05070812030a0b0604050907050c10050c070609080c0115080706080708 68
    0x82003003a42d83d16500c403098601c2036149030f98501e10141d070325110600e200c611000b5004d10401c0c0c003103a842c004128490541401030713079400408020080c80c032101190700c07a0020590f44102525102c00f01b03445035008035004007607800860955003c54140312042c00e00e841989078080c0c0010f01c001d200306e819030701e100080b1410b11400d4820380704048008440000159260220000c2000c65a0741c0d0001d8a0303681c4004001c0016284a4020760801e20110b00b452031007031160020079502c61240703138240840138014803009841c880c1040031008948100b07464120501c440051100800400c90015160032443c0c4009034001c0c00241d081f004181044020181c16030f504000d00b180302281c559100340200d42d00340619404903500000403003d02c01243d800200500000720700c20203a481450445021b98290707030055a9003e814074007001410042081d9600445116204940c810314250f0305615250a641c440503c413000500800d108220460742041940010030403403d005500346001000902501001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 562391465 1250 562390215 562390217
    0x106210b01140a03060906060c0237080a170f1206062b05130206040501050c160611010e0607050a120e010207200306091e1e010c180b0406 61
    0x5034145030841da000e0390307803402030038852588141c582400c803000501500b030300e00c03900e40380a10300000816101e118120038501550040c2c4031072001e484011500303682e0b00c201c42072281d00e010030110141c0420349414004c0c0092000d14000e25a0a5803418840d5106088000b10080c008080104007c1c0740c0421054841c5055000c4084d11160b40d0800461042d20402e881d0780f100c2c80d04030409200207114a9407000101c51042c2d401c11499036041120300704130140c1c1c01c01a60281090008101ca51310840080408d900031109403180c0c00d0855050380c4450650313400c0000410281001500009824030030003170459909401010113080030940074005106003401c4104101c4051801c14904800d40c100307502c100c800100840d916517460408041c508401c40640c0900a40900584000d2400290070ba0045002001030301c20800c500c00411015000c03003e40b0610f602a001d51012520702d1202d202000101510010071100311b6060020501c01e0304000080f012131030983c040c0700c0b9500390010f6034150b03242 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 562392715 1250 562391465 562391471
    0x30504030e0d0213020c01050106080901060e060d0f0b0a02092d0d020105070b10060f02211308060103050a1b0b030f0a0e0604050a0b010828060221010608010621 71
    0x2d01d0012070803060038a50b02541c1180005100f000c04001540018100ca00c503650380c10045d181c860b1074070b00782e503800e11a4008601c1c5130070100b001807802a0500300031500ca01126291814550344409a541c021a14040403a0340030900e1001c90038100007200416034111800d1100c201a281c000401c20310030310346c0b9801042e85070110811a4000d2080710095504042101410705c1c0c81c8054601c500a036006201c00036400700d610343c2484d8000144859215441c4822002c0914010002d03211500000003000a002050b800011041300c2131040701d0295000d5030240040c0d41143c02c240b0b0019000406405e28415070300c0f001c206004410054a0700030f081608403500307549911a50001405800a500c2d030075000c0d40e0144810440c0006406400c18461720402206030ba0f2007100b20389410320345c50002526000c4c1090011103100b000c4111504c10311030000103080551060010300c1c41c1ca400c0c40000e03250800c41e0018403800b50080c02141c0105010314101001860b550f00b00d206034110010403541080e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 562393965 1250 562392715 562392739
    0x11d16081002031803031005010e1017070e04020a0203090f03070f060302181c050d02060106091a0d140f0c07110f040e0d0302071103060408040e0c0405091003060c030504030e 77
    0x5441c03800364004c450340000c4a0310307810300d1000403850b4401d40c41081c2c0071640c1d815207050241042d035002d0001d58a291580700c9481801480e10b80300d1400203002e1820060000d032214a030360346501c00780c8400419a801103450b10450030501500c540b400108611950040c01e04000c031b4a4254540802d80354a0b2802684405182607200c0d4240750425103e0b5104403010b84d01100c05203a4001d030b1100a00410403282081c0221200307984801c42802284001400410305110100d550ac00c04125104440a00303031900c0a0581000200c61144400c0c086217071140050128109502c48059004040341d40d1080c80d154032503850b040344044800546020b020032090013900c81c0e6507036203d101c2007180c0009844220103120002002540001c0c01294a1035031894030030700d2070400003131441c071803540500320300d20f03050800329035103650b240061230891f0b8148208800314030f0f5120364034518010b1030b44185400c052030941c6402c4007510900d03420b081c1003500e0182000082a804803480906040503507000e52511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 562395215 1250 562393965 562393981
    0x160f3206130302040204060c15090b01120201051b010204030512040f09050c09040911190e0103080f04150201142206020306040603020303120105100516060c11011d1608100203 77
    0x15007690010f5031061005c9000a0601d40001c10300c100c035407051550701008072100003010101d0b40300182c00382c520b0703003003800610000f01070b4401400120300506009081c0740031000024001141d140c2003c01e10b94001c1030800c00c0180800094074807103400c03940306041c6800e041d40c8940b034020900c01e20100a4580000c5840c030007501c82120302210001e08144901255414000030313010800303803003a0140300102c148104100e0a500c0c002c0958020000703074089a4078645610006400481d4044003d9030100b000103150445100c1c8010f40c030343d1a03000401d0303010720b80401f01c40001d401010596104640404d10404003508c4107046007441d030040005880340c44440101d0010b04d5190002034040c480003c842a203103581c072052504a4004551800340070f2007040007219680105481e20b64818180d04030308002035a5030308074000c01041c51504a075482d014004150a5450088ae1005110900e910300840400d0174030a0321201c1c03000007002d826084c03403c19402da40b402141c26004210b0741c04030110380a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 562396465 1250 562395215 562395247
    0x30c0f05010c03120f33050a0e06040c05090307030c060906030e060619080a03030b040c02011119031104240503010803090118030206130e07080408030a0905160f3206 73
    0x5450443c1b218202281e00750131034800100764412000b280d41054100060364540b003044482034442d01c5060b6820742d1a44424800607107071518286052041c24003400f160b030b0310208840780065001d4020300c02031600d000c8014110360500e41110b010941014011074007031000282054008500340d49801d840400e92041b000c042c800f68200119501a100b81c182c02d00d070f40350304100c4103180106ca04020a03403615106a08840351003071100208601444490364000b070180051890014a083c00f00b50f5403076456804909030b01542003e07645c0810207146203074000210301581300302400350510500c1c5504148002c0d030f82c0d000d40c0c02464100840304500d03080040c6042040340082d940a046251186104c401c02c648207001805015801114a03000410461080100d24010b54101c0c440c030340345407107910800c40a0524001d054540f1f01c15208010040c50001e030310301c0001d010801c4180c103011b0420301e00800e01040c0041400618a10841e80070003c050314070110880241160002d03581c12050003082c80c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 562397715 1250 562396465 562396481
    0x21c0c080f090d091e080706020c0307150c080f070c0648030516110102151302101110020c0c010c120302160c06050301090c110606060a110601030c0f05010c03120f 72
    0x410300660700c00148050300000c003c2b10320001181900d508640f603c18840040388054810b400040c1d03d0b19401004c107174940d0003800340303d180a00d4076240511607119410300040c00d0388513000260010502040c00150500070100f44005a6025480311442041c0c84059010690032140402654542c8800301130140d01198103c0384640f030809420500c900f0041c0d50b4200034080d45016025258101c607000c0c01081140c0d11601d0300000100c202c1e00c15400340716481418000304414001d450040c105c001c0400c01029100e082c40400141e40e80320603110003414802405080790500c410026600b000a0900e140c0c9001e480507480c2c01070315180c850012401d0f00e20984006800b208111384046941c030740c4a07000310305079041b14000748898501080f046583d252200c0040e18150424000b0503550302d403100050150350424940044c0e00c00e0300070407a504008003a07000711500b4140110030031450740c40141450041c04242040b42e03072084c554601a0001d04000d500d15251942e803a8542c00b81d00081e44010780c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 562398965 1250 562397715 562397729
    0xb04170c01051003060501060513090f090b0f0a1506050909041707052d0d0c032f010606030507050a0305060a0b0c060f160203070303021c0c080f090d091e 68
    0x816414180ea0300f140d03c0b07145010a88003d81800c5c000301d0654000e1003214560006031405840c5070b86000b06a03001005042054420680c84005950110b84031070325aa0044208540c002d04504120700081c0440d40c117080d00e800704000ca402d003004244d80060a803598007500b640c0540440c0d8a501e846600d41c100d00200c0081240041a18414401d00003805004c0c40340070041c0e10f030f458024100b15005402c00d1f400035290390b817090104074001c034810310f003240c04075209083c1200c420a01c00700880701880700011505481004000c1550120001d00401000b40300314201044107003850b03030000f06580305081010081c543c40d41d002c00c0042e00c841000310700410b100324130580c8400540c60b403503840d9101030701c40f52404202c0001041e408501001c0248102c2100d80082d03140c101d00d9501613000e50042e2808050000c1b000c007000403e071007113000e80e9129071140d546000e030a00d00380710804000311010780000e145601c140300c6a80f000da04102c0500645030b044225140141d08070920183c20445508420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 562400215 1250 562398965 562398971
    0x5041413020c030c0d03060e04021e0307290702060316020307080a0806040c181e15050702030d0507110d141e1908120705120903030601110a0b04170c01 67
    0x2d2001da50102c06010b842802c2c80c25500c0c10302c1d202070700f1816619079010328010117000c0c402080051800003a03055240d4890091400300c05640000242040c807140d101c584d040c03c4641100105c0c2022141c000600a541407084d810404181c0106916020081a081115030140d203c0b140c418000c2065850941d40711a03032950305c00b205072005000710407d858a900590800700201c40c10f9010701440d4005003803d4240e0fa00382403412828080744841c410840780e044524110210f110100c50140603100380151301c41d075a9904a0780b0507d0f2400b40014240010810705200c0e400000d5000301203c002e584007218120000042814420642e500a08000b0301c644038229400081a0f0220080107030f0020710015500d040003492500040440880030041003100700b04000318004115881c0e55410400a14103182410304414582c1c202c107800380c2c0d04107a02c0c0d10200030441c0030b607403140211521130705a4018120300740c0f060b40c445940080280c4010003010700c0200041c840000b0100b641d400c0c5540500034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 562401465 1250 562400215 562400227
    0x507020a030b0705041401020a0302100203060f1801030308090a030e01051c0e0a0311010b0a030b071b111908030d0b12070306050f090c01080f100f090c030b0307060504141302 77
    0x7804d282d1041c812941c18030904c901103046507001003130060b04260542c003d40785c01c850601905c402903000030071482d8800321008039240310344c50b0044c00308a0751515628032681d65040d800d010f0003074480200f03502c1e11540500b903140000396001c003480011220a0800680b1842e0b2011120000c1420a1568558034940000640910b200103003101c40c450094990310b091409181c001802d032440303c1c000d00c6c3c00c1380d1295400c0001551a60340503074008264501a1062854a4501004207001a00c01d50381c40300c201340310042c1d900c1e02c90001005c1642d041c10703d0f15003510305907195449006045403000d00315940c0220004c5911103000d6140319662502c2684c00154403444c3c140000c0c001526001014441d900c0010a11040000c3c940d0a40034142c41f00d00d010380d181011640480401404221201d12600d8009091282600c4080181036a0302010034402c0030303102c0090071154000c01c10f611980c499013003000708580150407941580c1000b07982e80a03c013a01400300b500c030300c8500c0403100150320001f40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 562402715 1250 562401465 562401467
    0x4052719051c0e0123090301090c06080606070c090e07050307120303060b03101502010b0315151801050402090a0f03080a1101050f010b03041b080c0102010e1b010507020a030b07 78
    0x40c140d0304214500c000c42c0360301d0101c0807607051010340c0d003040c041055031906560143c049102165501001d40c40710b07282c80714681c0441d080d00c1d00e42d8011a09040390324400d00c40c0f15006001d960b840041603840c0ca04016a44d22090141c0040340310b2400095a5030503008031035803081c000003016100140c12502da00760350f07900602c1b40907111202500044d283c484045810811081100c0c00780c0010a504201c40e0305200c0740c2c3d0843c0300b06110480940d980ca00c0d602d041510244940710502c2d49403900260180b5002c0c85100310903418a204501c5548205584207003d00181c0c0107605560b020790300180c5950040c40458058246500105507a100e28140003040002860041c20b18000ca82d5400d140c070081950b40700d00741c0d44295400d10005000c00c0046c4654034080b0080c541c49400303121502d54035001108065030030780854020003015000404240034950b02400f03a19215034800c002407542c0215804c0d40324142c050310140c1030401c03034001140d2040d5594040c411001e541c104c41d010050b4203010030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 562403965 1250 562402715 562402723
    0x2091009060b040b1806070b090615010c020a061b140309040b010504080a110d080a08070216080a020d050109080f0c01060f06020606090a1d0c030c0405271905 70
    0xc03800c2450340c180000850038060790300980e03044a0802159030300b00207800c20000710350100842019080041404094040703440e4001440c00b805194000d09058200243c81e101403c800f0000d0300e0511120401d000f005894510300d01040310f28515202850b03403864030100031110302812000d05510f841c81e242135001940840281105001150100000b02003940151281c0c0294804c02d034142e0414060384021503909580c1000204004122603101d035055a16820794dd003004801d10300190b580001c00c260700ba0100464142c146441e40e019202030315000d01aa541c94102e0f2000b0b0040d501c0e000d101c0c0c108030b800d4015414080e44008615240c441c006410f406640120032116072940c01c107500015115a4141168162412a805071040759551000d00500c003001525000d403e40d030301d81ca908500381401d100c22841082000142c02140041010035181c0521a03855a20070f0f440d0a090010b410aa00600034803002130000c14000342210450041c200081060b180e800b80c55484022410080081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 562405215 1250 562403965 562403969
    0xc110a0518060906030a0308041410020703030203060a090209030307060f0e06070f08010b1c05090c03030f070303150501051213050a03170a05151507020d0804030213020918040f020910 81
    0x600c0a03202c503644d000806540d038040c22000b0700402d4441000ca0042000c056508030074070980d100301e0346200a0705c0c01e0302c8101d9106510039400213502209002192900a141c5002011140e405501b045468030010f5102d105444000b040995550710100c1d0340c4815401000c0205400c4003038441c545020500540340f100351040c00000211420000f040b00d005100c00d880544d0480c0303221109009481c04020014900508111014440c088003074806580401c02030807549080c0d4482502d0b0042c82c0350280c04c6c0c0e0560b04084440f045002801d01c521799000d000d40b1509000c414028100d0344418070840241d85c00d070035020f03013a400717450300280c240358111616003441030b810000c0110698031031100c0c0c411074909072006440c0342c41c100640c10300d030f15006025036100790380c070000140303450160303030000700c40074407114044601e0030005c241001549004000d00d40303401050031040d4170304103071031000413640207032081c034114014a80b01c04507050020900c18070126550240a441160401441f0351100b0b032414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 562406465 1250 562405215 562405219
    0x1311040f080610060f020a02041a030705060c0319091809031e0e0111070e010e0a1410031509022d01020c03060105040c140a0e090a0c0c110a051806 65
    0x2503500250000d0001a4240304401c4981808001c6080c65021900c60800a00c008214403550f022840980d0701c5100701d100d080e40001e0007100c0902c0144c18035003414031540c1320b40c1c0f080d8402c2c4650071a03048040204c913814152a0b43e000350400c141502034400c110540c10542c1540804240c24840c0304a40c3c0c44a4084c9010340c07104003c02d100e004442d050000d083d5180c0e80090b15540c1d1280c02c070b5000385040100c0da90000142d034178a9403034202401620b03a090b402001000010814020040d03158070424825503055842d80e4000e00d80400b00b25000410703848010100d0820f802014010405035200420490b0f0042c840282880c9045c0800c06141002c81354201e070041c500260b004130f600010b1030b146425005030240c422a81780c4001c010040509a40e00010b0040f8211807403402103602005100041d0a80c803030700042d80b40c41041c004e40381c00081501603c87e1600c0c070000d410f150006030070100c250740041600c2d120b080e80e10100d002c0c40340c10352025400c50141034111314020900a0b1140c425501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 562407715 1250 562406465 562406489
    0x30503070b0c070f0f110d0f0c1205060c030c0706051501121a0d020d0b010602100f1103190608011104081002090f09100e0f040b0a0902060d020702131104 68
    0x81c0314103148103841240001080c150750f01324001e00180038035441490081c000e4080a807170380d4405000c50210741c3c10310300031140314252910301000c000880d8080720107448000001021110a40d441c10b903907003c040c004400c441c01c040005005201282c0c12071b540541e0004061009007052152203040400a204050101300418074050003240c1d031788600d2110001e50501135110381845000c0c040407410300b04090381c00103c40e901c13000c040b500f01c040c440d008108643c0200030000200300c11208403949101700c2c0d4041030910082d400540008410f42c0d401c0800074001c201540d2041440000511503503001902c25400c140205000400076000f030005c03260740c4000d40704030180004060080780308800840e540000203024000c1142050512540d1003002e403403440c5a51529038500d4260000111008602444c03414104002c1188882c50320340c11801c0314109106000c2241c1c0003071124051180d80d15106603004c80c0d0380056658295540b191400075480402c4000c0703600341c111400760302c20701541030301143c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 562408965 1250 562407715 562407721
    0x809100e01020d05090118060818010504200111011a010e030703123504030f080f0106050c010b04020c160f0e0408070c03050d02150c04060503041416030503070b 71
    0x2018091000c18508164003400d1244100c8009441c81e8100b50990b604118031103d50310340c1e17480a01c02c2c3d440503104a889131503a0f40b8020f000c1507012100c2d485803003966410181800300169040c207a5a0204a5810a80c0080701807000100c581c454040c100204643c2041229055031007100c602850701c003002c0c2c0e5040c606a43d090300741a0344004510006048105450010340d00521401103841d10070041d40300380c1081450042c1282c00d8841100350781c0c4800d582007082c0010550415030b01d021452081c1401021490701d890b10050001c0b05100c0d400901200052200c05008294001c914503c8010710840d00c4a0385207a04999030301341c04500c03d08075103481c038020918101c00f0700c0c08000c4810300050340120740ea650b03880c224150070880d0115140c549a40d0003200003a018072130000b00c00301543c018007800d40100c20620404202403d02c00448070100002e2140f543c5c002c00300c9070f125821101c4640d0740341514410620300764100d03146454000d407010340401007290120044c040da40c090340034241c46403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 562410071 1106 562408965 562408967
    0x304140d05040513061404050406020c15100801181e02040f0203060a0e15270c03100b040f060f0210020c01061a0c0a20030307080910 59
    0xc1c5002c103090010341007614840704499609007090054601d0840c01d04003400d4045101c40c0295100c0d4006010702401e07404480d04590203808030f49101e06100c000420982d0141d0789140764020080e40081c00c05014010303020b2040d0540030940c4801aa0350344c0680c076003101c23005030700c1903640007506030090703522841104018400c2a07005039032840d10500b00514481a43c0004491206c00070a001100c0400f60580c4900501604c0f07541c00b0703078032000d23039070005400401c3c0c00440c801e554010000c610b0407620203140141c1c961031103050300b82e458000040f1540598003411040c805820300811106105007012052544540141d42c81c1034040300c001804d9070300c50b1920b0342040c0e44941c410840400885142c0d04e100030920f030805c0c14088140307021a118142c03040003808034402443c0303104c28505541000713450b0f924000e044030382d02c40c1d440c03a042a06070000301c1c00c14410501c07036142d52891 = true := by decide +kernel

theorem cover : BRFrame.Cov 562230215 562410071 := by
  have h0 := BRFrame.cov_init 562230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 562230215 ≤ n) (h2 : n < 562410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
