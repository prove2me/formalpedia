-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2767
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:40:42.362672+00:00
-- url     : https://prove2.me/submissions/18720dbc-66de-461d-b69d-e2823eb18b2d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 497482014 ≤ n < 497661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 497483264 1250 497482014 497482043
    0xf0d0501090c0f020a020108060103200f22060504090903030b09091b01050f1903060b040b030f150f01080402150705010b15042102061e0901090503010203090d030e01060329150616030e0418 83
    0x8d003005c030248a6140002d0080005008074110f336044200982e100b4180402c030052904000b07640f11200300c9060f98d140d0700c007108040c2031a9100300201c00264083c2040c40c50036040a2403c0610b200d801500c50381c040b00011750011040c801e03444079005108043c0c5042c0c0300c0f03403103c0c6e0300d1a09500a842d4658042840c0011412440e20b8190b0703c0400d8034010440b860842e015001513038030807002001030784c1c485043c0140f24a0070180707800a1881c14420000024000f40305c46c04c10109100d6108090781450003031000707000d00d00d1152810085040d6003160903d80340c90790701c000b48252040c061148260122100c01d500d800c98850041c25000a09807102c1d013101d511101452700700d000440e0f04400701c2d400705402000748c4d8080e5002d02001031084001207485034503600c500540c0c4d0040c150400e0034501c40c0c140a01c481c10340400c80d540080c0c48614050030741035481c0000b060b81c01441c004030719000004d28903408050040c540c401a2030000380c410302c414600c56403110b501881250f01550070f20905800c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 497484514 1250 497483264 497483317
    0x40303030e030310050f0a0b180315040b040314190305090606030a02090a0c1b05031e040602060411060d0507031d0f10020f0d0501090c0f020a020108060103200f 71
    0x1030f60f110b0b1082000c403603540c42c42e250401203000312a000054202d41c0485e004991162260018204030300c4500000030200011002d06160400c0c810045401003021401d00002690300d402c00e0780c00c1501441c0004900394203140c0306160f48101f02c1075202c109903032000105c0c6a038040c1c0195101d070031110142c0300c00303940d141c00707154807040c44820080d030220b0340c6030000d00c212400380c0c0f282003003100c05e20709102200c503110841c200f160b44a40c0c0550f0942d00c04281a21034440c1000044140c207400b540107410140b60500181d65490081c00c01041c110303201d58a000b203911200300741c50012171214400d0080e030420755005402480d50380103181348036a4001e091080d80303400064240b0314490380402041200c501c0140075000303403c1078a40d00700e040b03c10007031985514040e000b664041c0c800c90900003a03140654002034141d41d0380b8420305040d50004408100540c0e000f401c1c10780e120700300703007400300341c20200e140c03032010b00e1340b8598006848100106008041d034142e030024040d2100c090341c00c9000040c00c0381c40b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 497485764 1250 497484514 497484517
    0x90e13050a03050f040504110d110f0409110c01050f0103030806030f0601090b03070806070f03050f01080d081008070602160603110a03150312031509200c12030c040303030e03 77
    0x6000d540c0305080391000a40300c0c00c0109400034580300f00c039007410740f140c001a00782c4d290386640910405000c0780140e00c04980d44110805a0a41c0c89414a03002c0c407910311320100d0060b44100c0700703500da40300410b1880040307020440300c2c500f0607a40200058500070350b608075411420301065002420708000a20981000140070901c000d07103000400480c1c1c44d0494100192101c25034581c0c00d0301035030074002010f071810480720780642e42070744030904040c40720341d00201150401042c840d20041e064004001c0200081401d1441211501d0f050b0480d940f000180d45041c50f056204005a03c11300c000040c3c11640820040292091810500c00386aa079440440586540c0310a40c2c4541c9810004200d14600071303800245482c44032100b01d01000c6e81c03921034070b010381da540c00460046511500711058031100345d0340c82001303406000790400102d880d003801d070540031703500700c10170300d01c840000662a1030203400308803c5604402001c190b1b95280362814019950303801c14841140820b090148010301c0318000310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 497487014 1250 497485764 497485801
    0x170705010e13050c0705030f190306050604060c2307030b06090609061c0606091b0201050907051306030b04050a0c061d0d06290109050d0809150f0a090e 67
    0x1841440d09520001d42d070402400701502801e0b000104101e0000010303021b001400101144003000d50f2034646903c24014000d400014107810540340c03070000c0c02155502029141a04c10754a0f02d5801d6440c02d00d04807088400103020ba10b20507001030000c2c3e40703a542c00519901503c1c400e03205960f42d500ca01c8240050804195609940440791100252082c141140544100d004a0000007010b4080381c541d9801c413802c0b41c00c82500300d92214444480c281d0072520500e00f078074440c07000300000c1c41c1007981c0e10349800d001d0280c1480350307204083c080d450b203a460b0031410203160400340301030340b40c00c00349009551500c803034000711100c042c1c2d140005045030080708800894040d03d070904d40d100000340d041000c2d6248000c0215a2103545401540000358841915204024084058074040c00d060f0005400380c00280d05c8580701d060714104081c0022081000e07074046c03203810b0b41d5503280040c04400d03c581900404c9003220b1071102c04501b1240140e485600b40f01268007880c0f00441640750301d0103600402c02580c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 497488264 1250 497487014 497487019
    0x307022a0f010516060504050313031115030702070e1915060806030601061407021305040f140d1209060e1207060f020304080306010e190e010305010b0f030d0503150901170705010e 79
    0x44d00b0003c086080358200c1035006100f14244c0345080b484070794903100c1c18000c0e04191461a5a01c02000700703414203091440c400c003410300481c0d04610700b884000f5501d0b191402181d07410320016000c03e0100341c181020503040e803562541030007d00038101c0408000c0c44944a01070000c0d8104004c1003e0b400c0214580e4107031042035407000c050050f040000c4505603c10003040360001007002401da24405588203d5000320310400c2c080c022120709040c540c001c0b0381c000bc807001c20ba801c0f030380b21400c1082c1c00a40041d14203601d81d0000c2061512820044001c0c80d140310350360f1050003070108170140c42c43c0c0d80c4014031415102d14410443c2c6029080b0010480c041201e00038141c22040020410310f40c040d0340c52917200352000b0300710030340d6a0400d001541101066445140211890001841040000e0040340c2060700c1c182ca030409000120030000341c0d43c550060840382030285c0080860340201c4041101011554041e09040c801d581d00e004141d030079090350000c0b080301e001d1101c02062640c443c01440c162080d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 497489514 1250 497488264 497488297
    0x9050604061203320c0d1409010c0f020604030812181504060f110f0a090911030f04060b27070e0a051203041a07170a050403080307022a0f0105 63
    0x100d0840004c2103904c00c095480503118021202c0c21010200018010842e810000e8100d500c80717850003070a4500d4944e00a07c00000911000016990006814440d1904501c030002400c0c0c460011540c244982e40018002100001e6000003c0c084009540e000700000c0403500d0207a10424600c07a110070440c50440241c810880120700441c00c2c641041340c0f504c0f482c2c500018540c950030f2070407005078031202c151001c40c003011401d070801070b402180c600b0003044c4017881071010040c004c6500c140341c80300915024035032003a00041000c0c800c0c581d2150640b248040c21700155020340d4015950103640507a50021070300881000640301d944208210440410050300c440501400c3c074040120b400640d81413441584024000020f0341500000311401005108080c142d654245050142c1c0700c070340b072104400285204001c200b940f00e070f0000455003201d820405094903501d43d00130403800e103403881180c02c83c0c0c8400c2007110107130403554120010700070b2811140f449119842800540b80d40c040e6820310710f9038026 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 497490764 1250 497489514 497489537
    0x6090f01140d0203011d1b0307050a15050d05010b030f091f111e03040203010b0d050a0b15060a090e0109061202060306030a0c0e0901061a07260409050604061203 71
    0x2e0401c50042c0e02480100040b0b02c4088401c44610000391960111046520000c079001c1102454090040d001c4000c2d800380c0b1480b410300000c101c107061584190708550800c2c0440d401510302c11419110179480c0031000b4841c5503076036500d5410b070b134000380c0d000c0200103200c501080c41d05d0800614079050052039181c46104020440c03a180082c00310394840a6042c04c200b00c9154012501001e03080503105005280303482e07040c28018942116681000d9501440403040e149000c100001591003540b548090100e41941ea01c04203100104107030313921103820a074042000785d01a5000310413070f0152143c0c481000c01581c0e0b031b251200c0544105118010150501c0205200076082c07081c0116400180942281c040507019501d00351141408d60004080c02110303018800840828040c1100030b00c008803a046198000c41780180c00c92196490041c030500300a16031444180e0415500d881c40e14169030303200e40746c1d80c2e43c1100c075000c0c203001c542151107030f4a003600103e82d4441603500c41c250305401d50f41c5c8040007827 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 497492014 1250 497490764 497490769
    0xe0f01021c051309060f080a020102030f07080405060301060e03060708070c0602030c19020a0302070617010b071a090106030501050c072a0f0303050703030b04140c210103060506090f0114 82
    0x840008800e0810800300001c0d507160f900d030000140203155100000030a549005440840c0c500d5540080d2000d4100075014400761707070f00005035000100a00e140710b546020f64030740918144100c1d40002e070000d501100005865400a52840c91040c0640503902d00342d07583d07607040380c4018080b14840e0214842100b02c00225403a5800355074040900700c102460280050443c69541000c01014001a84000000c030101070341070140400038000c9040c48240d504240b40b2101c030212050184120050010985109026200c41e041c0100302d203000b1044818184054001d020302001d000c01d50740c540c01c0501244071080303000b0441da206a04002c8807250b0030641d80e40050081c81041e902079851400b500e012a03001100c2c2d0802004610903100c1c2079454100f841d0103801d0b500c031107a050340f19520340210040056182c144a60b03110ba090380d41960745210903400c0e0080000300504c2140c030314404100102c10026039500c582e000ba4400c8410004955030795180c25001b25090041c0b01c03010f10400032385044c90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 497493264 1250 497492014 497492053
    0xf1413020307090b0d0203060426030601050d0c12092603130b060111150a1b020d0e0102121309110c0a060908040902070614090a0b011a07020303190e0f0102 69
    0x104c100801c1481c9501e500d80000c4d10b45041540c090369108003502d00d2820203090030301040b025203e0f01c5540d605510341080080c01c00d02a1001326241c40303480320700c1044841c0c0305041d0880310319003441c000c0150b40c0080c2807e06440200d517901e040c460408080c50402d5648241c240c038801d1701040040880d5070521b03030b103101007100c0103003525042c00360840e0f0a202c070550520240700c0d0302c030700c04c100340c40145444085801a074900e1b25001c170007020046000302c034655001c01c5040041d501420006408030180004074600744c4040943c2407aa4004103c1c841448040303031102c0c0480c2c20780c7d44240a00f000011044146100e140300042913640090070038000240d440d0003412659000300581418240c4d00c0b064030050760302c561030484605079151050f030150f1180900351500704801c08004c02e03030b290603030340e6421410206000d9184084600800305060150b6001200c040039801703000d99842c0c1550080009a40c220014004045140008042450704283d0081d1044c030038141e004000e031801030035614446 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 497494514 1250 497493264 497493281
    0xe10031e1502070b151801030b1501080c1b07270b0102031c0b1f020610081c110a08040f03060f02030f01050108041401062d0311220f141302030709 65
    0x40350340920102c0000401d207411f4003c500070044c82520745070034071001d141080d50304005d505103c01141401780c03100701c0c201941c84294414640c85c445540102c2084e2400302290711040070301c0c8030040a4042c2e0301c0702444152031241151401e03c4100d03200c0c0016030b141d024070580e0000c0b50044103000c4134440d905030082109401e0182210f0682c41030010103040161000c021600540c2c4400c041c0a544c0d5038081c1140c00528182001c4c2945e0452864580314070303484060309030200075a15441110000041c0000d130705069200d400300e90f41c1c07942c0e50160304901c4034507c0f080e5586071408842c0111410746000702c0741319220322400e8400ca071303080500543d14803c0c068429121804002c80c140ea502c14244118000380c05002c001c01c0c2d961104590810055052003200c4080c40c180601c100001001d00390b150500c44001c40c0d00503c10700d920700c848034946040d1810032014504121300b08034400c085510401100d54442e00c640e803980c0d6035034008054400105002909580a114100031000107640031002c03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 497495764 1250 497494514 497494519
    0x80f09030a0f030b15091806060a030f060b0d06030b07030b0303040303030c032309210a0e1c11041b0c060203060411030a0c270e10031e1502070b15 65
    0x101c09014a002c5849017000c82000302d0203000005141003d0b01e00720312040107107650500000e010307103072210201d501030054a920005041d1104c054102003c5140c12144c0541060b809407034035040003044075005004e5070310003074810072041c1c004100502d21034000c00b403103800c000c0c0040d0300d4185183d5080b0020702c0c1c42c003205804c1565a459840854a4503200041d2503600091900382e5420070100403820005604000307095043d01e1000c40e0030441402c07003510081e282d5800c2c442904a100404110181f40070026103501000004032501085081c2c0e01c4070b51030312070968040010b014036441c100c1c500384440036500042880628074400140c03503a0021507114001800c04201303106080c1c0704010a4005030b403014110794545241c035a0302540242141e114030550f2100b252034207040150b02d6011445401103e40740007040b40080e9007002c3c0201810000c3d5400038071403054100318001105c0d4001071990440303201d60000f540340031940a50080d18003c0c1d0700860214199160024a0001207200300030154 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 497497014 1250 497495764 497495771
    0xe0f07120b0d0f02040e070501080103020616051005011a0301031a0a060b07150b0108060d060e12070b0f060108070e04021b0102040f14060a050315030c150a080f09030a0f03 76
    0x20303860b4070b4158804000e548a000d075542d415495104020684001c070110604950020070100b0480c0c1e40204210b046a4040d00c05994650003580c40103a601413014000d050b605c225415030603055417540c480c604030382c02120180a201e01c0383c1e4a103541d902c028031000e03100305032101d82c4610000000303000740d4100e6038840000030314660b07ca103203407102c3d040700c40240c1c1d006018100c65110b9200741d0282411030007092a0107003092520600040806604442c0035144580e520311501000008000d000350034008401355a4a4a129103040890309d14225000c601400300300b008201c66500408100d8010780031600c5020300c2074100300c1030000a41107820050b85c41d88400d080d00801403000c0c0b0003480504030598123030308641c4c145580c00f40c040c80f81101d4540200010458400d009a0010a59070040300c3d0004c0c03c5c0c0b1050088000034501107080c00b459a02c441c00600000b020442c8500a01700488141c807400200c3e80c42c0409001d2400003202c02c08901d8004011454130a803181040d40b100600700c3c240007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 497498264 1250 497497014 497497031
    0xc070210080702011b11010e0a120507050709111b0c0108070e030c04090b01150c03020615040e010507021b011d10020307150b1f120f140901050f010e0f0712 69
    0x350150031910041002c2030302206c60600703114080c00f0f15031800b40328030014080031030765603500306030380901d001c080c2c08004c408a280003c10034148101c0c4010544c0c02c00501c40824240c001108030307407051020545030030340301445401030400840c1c03079407228805842d11851075407884410784200042d100300c25814014002480c545030b40f103104080c081401007100085a6046c1080082803020920035072080c040791074614400283d00003403890b03200d55002100402141c1e4200802d014005d1449803032019401d0908010680354006181020026010056907603110b052005540b070154103102c0300302c2e40b003450000100c1e50400019034140e00700984116464400740b40c4030307800d02e00000d540403003800d5140c0103a18814584a5211030f16044451070510210100e180d0103000d001048880440090b110a091007100446d80c3c0301c800c0001620600300300c213203840030089008000403074401000001c07030700011030f0708480000c1252040300940340704c06954a54640a82d500d10551100401e9a034031051305 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 497499514 1250 497498264 497498291
    0xf091609170a0303052211040f1b03050106111902030309120c100512070c03030b0607030c02120606060427060315290103090f020303030c040e0c07021008070201 71
    0x4844003956200050324151042e45401000d440d00900344407009210360b44c900c3c804070381904d002046d42e0780c000720803d403501c4030502140c060174560100c01981403400e040460301c10b1170240600c036420182c0d502007242d40c0e240c0b0000c0e2a000000010300c1103d900c80701142a1040310300c0701c5011910f0000301200d04040b400e0001501c419000411070303015400c2180e450400c1c0c02c00c40c204450104044c01c0c007900b40300000480914584000f4100f404204140d0541c50600d402070380a02c0100102a00d5582d40d90103034100034008600171501280259034841201c90040800f0403510f02911008044d6482d047c904003124070031f502d00512812650460a04184080c079183c8201c40003584560b10880f41c090004501504541e042d07084407913984040d005a054041400009922110003400c0000d6900002d08114040141902000350144000418403404641480182040f03451075070f42160295649880b1a0041c0921003000f504003503100400e100041c011307656260300c01c031148000a070000b004404d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 497500764 1250 497499514 497499539
    0x1203060f060c03040801061a0921010e0322030b04151113080c040c020c0d080d020a08181c031a090c09010908071208071a071205060f091609 62
    0x14052150b0f88001420443e0141c280690002840300d01d07200d003509259a6145402032084482840c400d01e0200100074100700085204603400c455070b4001c000340c3c84400f241564a910000b00010360341030514800d000e0010040c001020345c3d50000c0181d80c0340c1c0300d0f6aa44060440026806644a910350040000f039500300740143c5465035150703404040c81803902d00c6060400011001240c012030800140424840c1c00241d01402c0c1241514841c0740424a410203a00a00a4494001915000148044420361b100d06118003030f4090b10780350300581e50100003150f036622125030103080d03042100f02070208142c042e520000e403044031020300e009840103c03800640003240440b911a0484808605042a560703c6046000907050a40042810504200e00b05440c42d81c9030300002c004000006450003045000d20711903880b905144100103550500f9480074104042000f40000c089140c0400142d040c0f9061081c40090755000d03054001a44039604800004070f4999514000c0c4040008000745406c0c0b40b05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 497502014 1250 497500764 497500777
    0x12020a03032f07030b0109421d0f011401053406110a0903060f15060207030b0a06120311010e1629120603070e0403020a061d1203060f06 60
    0xb000b401e1064110b00d004421018103801101407245024100740518112551b40010402001c0008400d040240c506407400c00303045110311140700640000041c3c100318490140d0940141d50340d0240030341c0d81d440e1408002442403141c0801c140c1e2400c880c45c1e0381c2d40a4801003126542d801c0b8040030621086000c4041c0304280f14004ca07140458021050501c9058442c80e10140f01400b001c614007410403900900caa200e0780809009241c1d1a442d90000c14207a40c0170514291141040e4200c0c3c0d990340c107020b9250b502d03e1100755024444100003d0603040d55100d032030284c450700142d4005a01c0941c40860b502050313008012159907071078580107144102006000d52054800c5030f0a0359071400c0084107410303a0411408110110440503550410340141c00c1618500401080c400505030b480c840020310b000e81c264001d5840b1600c920906c401c0c1607000c140980c84d14061401442100705000d0380f0050904841031052081d04040300d05d0040348100c00c010f6400c07880042009000414400016440e5403048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 497503264 1250 497502014 497502107
    0xc150c07051906030f060503120d0f092a0b1314030606010504180908160204180302030306010309060f0501060e10030204050a0e270d020712020a0303 66
    0x811414214101088040c000c0d10007a40c01c2208070400d8034400201c450070b80280418107403211108044503420754403400003401c0090807161071215080360301e0956030085c9400501c160521158103801c2e1818080e5003082d55226149410b8220306201c00311490861580c500c8205462000c00140a1845000741821004d080d640349001840c0c510300c1d4081110561090740260001020030210707a1708401030700d08491000807510600c00140c03503200c0041102d5640201040000304248440c0c0d41d100100203c2c29200341d50030004079000c440c54034060308180e000200160310800008000c1d51103500454a440c1c8102004100e01c460020b03070750b0584400b41c10401c00107003468400c2c01c043ca080f80010140304468241185001e0804010840440741801510407550b0301901140d000c5c1003001c401502c5010105042d00e0184a0801503603ca041036036030000103204100010602c41112000024042e078000c00010001c0c1c915a0709403094001d02a84400ca8078582c451801c031001800800401590034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 497504514 1250 497503264 497503267
    0xa0902031f03050f0706090b03010509060a03150c1101140720060f0a0627020906040302040207030815150313061508151b07021509040f1d120a030c020c15 68
    0xc10910b0f142c483c0e176500c02c00402400450030440f207504801101d0550f007055802c10305595880c0701107803030311003203074002400c8501209100c0c01081603544a03a46440d010b6440c441c1e801c1108500e01d080e5001381e21340003540700c2c1c0100441c003501c0c01401c90400280c101c14101e840300320380301d030414246a012a10b10b103034000e9000030000031011910409010300010b0010080400e00d03a0b5031200039081c2c02c401180010390014051605036603900030344004544c0104250340d25540382c0b40040841c2d200341c1c0c900e041910890001e007140c3c58040784821003900d1068407142160780c1e030032160380c5800a121042e10029a07034000100c004030007903181c03401740030b07180d000340003179854902081054800203000c03690300008000c0104e881c000c0b0004403a43d943c0c0459240080d07540a91108516215204070701e0703440342c079003160a5501045504000e13202c84410318080c0d040e080300301146403500313102980c2c0d95954804010000500e4003981c0019940034070303407048900003005c000100300c112050707040c1c02d00c40c1e400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 497505764 1250 497504514 497504533
    0x30e0925080f0c03040c060503060607080406020a02040b09160503130c06081603050c03070c3002010b0a05150c0c0414060f0f031b010219060b0a0e0103020a0902031f0305 75
    0x810b212071508800701c56200d40c40d514094540140f07004290040c101000400008180f6030340c0c8c0c12090702c01c86500038001980e560760721030000c1e69524144000302d02a41c24031075410441d2030042855403007807002400c66204c5451070717501200c165100503c40e14240340701071384400101e244030280070068403041c0c80b00ca40b2814000e100f8400602044a01d4080500301020490b50030403400c2a640c0242550030500d00e61485441c11004a15400018091290904c0f480345540f912211010b80c01007100d030020442000c003030701031110b414400d005180c2c10581006181c04000207842c010014800d6050550740c2a95030040002c05903042c1c446c8d1340d013140002100340300491420f42402c041600048440042100d128070100c2d890b00c00c480100442458401038000040c0d009100c070381240d00a003000b111008045142c480000e207411070b0624014500070310081103000c54010f059068a8000300fa100742c1e03d181403040c1c1b0282d40b0090501c02130702540b122100201151402c07040c0614800c2c80902071400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 497507014 1250 497505764 497505781
    0xf0212090c13050402060703030903030917130602030306090622020708070b01080a0b04020f03190c090b0102030a17151806010212130905062805040f0603030e092508 73
    0x400801d040700ba46407600b4203000050b51408100c1c3c00d80b070b505041c08203200402d42420f0380200150803002c3d1900010010080e01c1c200c00070020301080821684c894401c45e101c407412a40ca010031229190004004004503034245002142d81d00e01e0064985500c3d0018900ca10010980c0c00c40329048442200100f01d80c01000380c800c1402e0301401d4000c1c02412620116240e03080c4094026101070701503500d0b0340100a80340c80c00d01c42c03210703062681c3e00c00c142d031502c0c14500610200011f103d80e600c80d511b0880e14090561000c4101c5410011594030815a40140d9071302c1d06505201501132800744a00c41200034150b103e2240000c21130300e4507592003c1c00c0c50b1190000e4141b1030600b0b00407030409001c002008002c1c2c80703107a00c90161203182d000003c450382c42c2c20211745031580030f00d241302c1100c0704c0e07450b8100441c4641000741c094450a45060190b1404a901078007962032a000c000c01003660aa1007695a0501d400202d510002c2d0b802c00c43c42d6980040700200040c04035000607000070341320004001e03a03074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 497508264 1250 497507014 497507029
    0xc1809080c0d020d0806030a020d0602091507050105070f0c083604050f0c2208010504050607031107212d02071212080408070b1e070f0f030f0212090c 66
    0x6134500b00113080b89014000261101d086803002480780920048001c10b0161329030554082c0100034180101e00d4540070111032030303038024007000c03103066007410000b0b070100d0f00c904510b950500319922903901d43c00c980d503103203102d94001509030f408480102c2c0c102070345142030040401d01c4503842041e410440501e0300501042d500000e00f0000c580301c0344800e001d55100c80004443c0c14082040079540d243d259541e1640b90003441e42d001048a40c02d02040c003050110100c0c0300b501891180c4c40400000650346071481c0c5074005e40304041d1042d2503500461007550080290101201c20624203002070001300b09617101c696540414185014050f00c0c54080300c10f80400900c00580743d000700345060238255981c1d0002c0341c3c148003900d0381003148100100d006c11400201f6224040e0b0300001230b403524505410440840b10302c0001c1c041110036242c1c08205103e004260b1420f03e200d856440b06e03100c5e440c02900794050b001c8590100a80c507030811500710400d4200810754001c1c1c50308009080118204820440760703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 497509514 1250 497508264 497508283
    0xe01050301140c04170c0a0f0806070f0e091f080d141603110703060929240f130e06061012090c030605150306090a0c1809080c0d02 58
    0x4002580007401060b00d090350550f01258000084105c1c060030f4203400a00748035400c5509074014000c10000714503080f5512550083d902c1c0ba904565081e0307507540040314000c44100d00360010034000194480e05080c0244038030303032146400207010b12080f0500710203c0d08086175404030206401c201176106016510804c0c850021040310401410081ca511700c0b00b080c50030b03e45009040c0714201d20130305802d0704103100744401160001d0b0100b225075014200a144d00d020702c480e5610949000c0301c00340c10300ca44194170034000e4110a441a03154420074605102d021071442040d80c2c40000110305c0b600315600c90608084140d4000c0c0b011900341845407400746400805000c1d00c2c400d0002e03d4001e13a40545c41f0a0904450303078200000706445681e4103155042e40c4890300042d02c124100010002c00da032420340d80a000f89002c0e41140c2603540c0d1003050725254074440100800401c9907940410512401d010f41881c0c003d07585a0014465280e61b4544060341e10140c032000071500951075030084150144206c044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 497510764 1250 497509514 497509541
    0x2030705030a1a0a0b0a0b04030b0615030613110f12090708251203020309030601061407080c10020417060a06210501060e150f10020304060819060e01050301 69
    0xa80c0c0c0350540c1d4010315410f11030340c04070b0200d4a00c80000d00d48403068024148407403000d402214166101e401541d031550180c002501c4e9042090042011350500d00307a85561488041109070641d2250f074100020f1040d21180c4004450701c4000312500c040340ca10051041504180e00c0c0c40c1c4e03441e1441280c000440f00103080c2aa190803480c4108400d08000c280c003002c05505d4010301e840c0c1000240a2001464243c0100d10380401002e044010150008010715080d80228121255a030341c0d030400301c440342414140203849034024450100000d0018000d80048400c02c425114200c510300759510881c0c00a6201f483c0002111074292049581485260380006008030180700d03290410000301041142e00c5001901920385403614414800d007940400c003d0001148a1081824031044041555654420640c41405100c0c045807040c50f082c02e03080418112500550f00f01450f0010546a4400c0103043c0003c60700c1140d401c0e540325400744074420151550200803812541448140343c00c580380c1c00c10b03920 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 497512014 1250 497510764 497510773
    0x10618051c0318030c060f02060609040203100c050d0905150c031317090a03060606120614060a0c0515070e030a03140d0e06090a060e03120105131b08040203070503 72
    0x4602034007040d00c100240c2d05070810890a02902d14aa031a1441c980c1c006440a00e40001c0854603590100c012840c0190980c2100c5040d00c690003040401d0f0b50584000b903055215000002c1058400e030040702030b40d10541051410044e00030307550b1080d5106110121a60341040e00504141c0e00c450748240e401600c08407905046140c0140c00c4141e29038042c00141c5a80b00c5c1601140c1c1400340401102c00300e07030000d0061022940e803854508081c2c49540681004074a00626003a010410f030300c501002c554211600f102e600b4080d03001d21541d6804004008104254041d202c808100d0400a981041e0f00100003665107181249004081d01c40c0014290310035004851074901003a8450b0040481a81c15107a4a0f5a0081e4048440c02451295006030b805d0040c601002600840030481e806050f02a03c810702c01c0c09010903403aa124481c4070010a6040180b10051207281031600082d007019410f80c900080900f2080707980d02400c1c0040c007860000030024002c110840c1010312070100103103019002403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 497513264 1250 497512014 497512039
    0x6090c0804030c150b06070c080c31020c121e04080d030509010f0c020a020906090106050a0f031d0303041a1b0f190906111c030209041401061805 64
    0xf03112401e041c10240481c4000300c1c03043c0c40003038158400121480000c0c111580c80c0c96030314100149500750b02c5651200e0294540b100c903541400b0840380b040d041b129124080050903448400040782e400103443c1001381c2e090190402d41c40c400c010440030044a0020340d0380b00c00c80005c0a5075414030144101c0e44190044c80200081c0c4000510401c2182680c2008165550b4001a4600502010040f90102c5040c03002e090700d0309801158007441180240c0d01c0b0081070380c1c0c240074040304250038814400014010804180c44034421581d0103401d240c240f50200f4041103803500123038226001c4850341315981001003031008021509000705480340200703c0103440e5141c540300e45050800b0380102d500107210002615802040f9840c2160034940c000346500d901031010030801030070303c1c1c0b550003040301040700004200c01c01d03900000c4080c00441009003c003400320007540200c0c041d401c40074005402c41c0d250f00c101c60390401480141c40c040d20880e5a00703030790840303d600074036501c100941c02a8003e01d6a048003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 497514514 1250 497513264 497513267
    0xf0a11011806080403030f060b04090605040203040503031f0b070602030a0b190618031a0403021504021f02150702010b011209050d0e030f0f0c090105041b0f0203040f030606090c080403 81
    0x201d004980003800c01a036a43d0382c5050a0703010306403d0311014205450660b001ca66400e0402c0940241e400654041000c41d4581c0240412403000f030314080c0c5994030030702c00211030344411401d100b00d0b000140660000302c0c1c0c6e103241050075074002c01c60845200d9004020000c69201070b220b50882080704071090440c046e82c2e001000110444c6000360740411060703030645100c5091b01482c1c1001542c0c82007041c4601000312a50b4128860300360340880040c010840c11100002d1084843d50141b50000c0401241041c1030a011080501c00c031701020540c0030b221101809801b040486a1142d0166000030501e00016000140741c110910030600200d89031400d941701244001510b13480940d417900b0510b80a000b2200000c5c0b91485801c80380c041d07441090064004140d000c500004c100310143e80079850390741c031101040305030341c0440044150040e20f0341c82d03100c10900c074002100031000140103503440c26444840244401000c6d804c151000b68641d1000c00c80c4411502c18104045102e04d44402d507414075940 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 497515764 1250 497514514 497514557
    0x5061012020c07170102030a1820010c0b1e0106020106180902011110090b150603060108061c0803060316050114091302070b0615030613020d0603050f0a1101 69
    0x80c900345940c0c081107082e00355200700300801c00390100640029056184080704ca02079401210880307405400e00501c01c44441ca0322070141c00040d80103480181c508900b041900720351009000150411080c08030b010042920165481d003e444030031401400c0d030041c0380010010795010382c004004c6a2404504005a198051440c0802e034010100410051010b00040301c1c0103140044c84c41240c0076580310080821040d071b2150340b4003841006010071a40c0c2f14885921a044501e0005800c94820000203000350b00c1890501d83c0000000e1862107003c00e2041041105040288210340c1030340c000007401901e140c00c02142104282e00c40e8a11252401d100c0002c0c580f102c4064030000c2d0301004600c144140e0303114450240d141e103000780110740b5981c0c2420b04c1e0884000c1501e80c1401a4410340c03d07540144ca00d1001c90f0301c80c6c1c2c07001d4001c607a034003040c152900096000a4100400300ea88040c003000192080c05001030b5034280c1001001403e100703080c1401504205003095040c00f003107000d804030f802c10310300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 497517014 1250 497515764 497515787
    0xd0e01141012050c0a170106140a090f06081e10090201020a03140c03190e0102210d0905071d1005010816050d0c0504080709181704030f030207050103050610 69
    0x10b010700450b091a290580ca001885100207034803001d070704804900b10445c15422030078200d0540003448643d82d20712040010150503507a06030421b00810301030040c00c146030401091100038103c0094107566030703983c80b4140540042d0001d0032846200d41c8007010704040100740305540c101c20b13041062440c6640042e5941501c0c24004092085502003100d22862001c2a42e01e8213405100341c0b070307035036001070050b501501e22014180d010500c0404c50902551000403200c00440768400e0140004003625144c80c51500a180176840d4903468900b4000060340620880d4010304800c8900352200382c0b142c0c5440b4044e10000c0c200b40b031400c60100104220380e481110300d5002070316035410400081509408407518450390880e1750b5850f0501060646a60340a002082101d00310740542e000700c2d4590ba800803e4415a52106c40c03141c1110a084000c90800002070030800d1812950030310300b944d2544d80c0c0340744000002e401c3d00542c20041b010002c0c0c1d601805103a40c019001c03103121f6a1641c1030303003018043c50402d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 497518264 1250 497517014 497517029
    0x6040b0301050d1b060e0111010e1002030c130e01050405010e070c0201030507170f0f011e0311030f060a060f0609060f0827011a01020604021309020105070204020d0e011410 76
    0x70503010300200d010a10440741d07207113690049282c1c4502e03014160383e8200f00094000740b8001c1c041025002c062040c5c585022503040944a42c181f5071200001a400c0501058003c00003042040325400001000400500e8244c03582c284541c54401040700300c900581c06005000e142400b0000016400b00040c000980e0900340002d091315007200031507000e400300d84440101d1100cac0c420b000c080c02d5000c9040b0f2061400c144001041d80e298009081d03070340410b182441c003610000009000140200b6596000306c4805811510700030350054200d03260110a455030340302030742d40740030502c076000784030800313902401c01030510034051803902d51b0007424985015092000c004881c8003143c58071410b15040c0001c1400c110100e03580032881110349000b02401d91600000503828451764020394000314906100d00c1d00103001c60f20800d0800ba40d13001400c02400101c0c100300c0200316100050382c5520103003207001d40c4420001803403030641d8002c1d804c5038051031803109104102c00422151041e18981c10301900c2d0314 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 497519514 1250 497518264 497518279
    0x801090804061b02040e01020903010c03181410180302070602010c140c0a05070824010609030f0c09090f120c08030112060b040e15132111070803030a0b06040b030105 73
    0x400200060f00a42c020000398480d0510f0700c4048010815000360a0801c0c08900070803091800c200240d08840c146c00100d00b80e1209548114007003102421003059070502e61081e95541c0040155203c101e812400c145048080300c00c94280501d41d04000303c80c05840640020026803030a0b280c003070050910002d040112240c00910f25a2041c000d01c03142c4070055001d4101c0c0c09590f200c0a00c1601c8003003100c010907501c1d8500c1d168030340703410b0b030307201040d0490340c01e602c0720036026096071241000d008105005541e20321074054001001c000a02c03905880070301840c454100310780607140c4088907942c00e60f202d0080002c03044103680440d48420840b411100c0b02880d4803640340031352071f215015000c00d025203503006180c003103130502c00d94001c00c620000e0f0b640c00d0b1160186595880d0702000c016100341c4042e1100881e022019180302016030054135552a5007481001c4d51010781403185040b9454010410503007003c0700740003543c42c0900403040000300c00c0b41c115061508000d5502202c3c0814400d16100c1c0f0034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 497520764 1250 497519514 497519537
    0x80f1609020c0a05010509010b01141201060806011b0b010608160e190305032a06040312020904060b0d0e0f0706021203060612040602040e0105100c02101b030216080109080406 77
    0xf0043e228800d07a00c03400070b02c261318040d10028020080b0408450100d01110b2685503004008411140c81401c00c100c440016403c001080302c01c078500070b01d160b0520082940150791500c1c15042c03015510b10031407049050b9030400e14010403000c0007519400d98118001d040c1c04829403c002468011042a11004c00789004045030401c0c2d402981d1003d03200340000960b1b010340a11800c41c8180c07031944113030031b6014a4801c07014076603108e0084802500281d17800d25006511000d540041c00e1900c4010008500c003034031041002420b9100d04680c51156549075225016400e00384282036040003d14050000f561800310069141c10250910070848003000000a502d65218426901d6001d8101080803e900d0217140210095006020710420300f014400005100e1402d2440321140c45400d035540d040b0f010981e0b090003c0390078841d05040502c46403144c0d25120304c2900c1c0a00c007a03c0d00070350007010350114000080c0d0001d4490340001e03a26034100f0510300c0200304000d048030200d424520344185010b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 497522014 1250 497520764 497520787
    0x1e0e0609070909020c010e071703030a050402150d021b06011a0c070f030804030506060306070507060b0a1e090b060903031c06050315010e070c0b150111060907080f160902 75
    0xc650b0083c044884c80450f071607151400560104050189507030454082640702c808050914a1203004070000398403c0001941105090304200d401610181000241c050006002d007142e4100705d6417540b019501155412544440c0070030b1804060088002d08280c1d4107286801d04841082e40c0e440081a0000403442c81000042002c100203101303c1007041810350f100d00e000d40b041e502030300c0141d60714130440011415500c0c0100700d01303004106c9078031194913100e41c0380c0e20b0a01600c0040d9500344c0c0074541d144000384001b0a548210780c40c22000c10350720100da0510402c070048030340d54402d450107075109012145040d20008215080c1100b02459000c41e003100e0010f0b80c000c0c1600750422074041c064a080c074800480303551a07441c162041440902e282d07642d40001103428203040d01e0b024224409460110f48003420079a0780b4448034106251165141d20510521031170800191a4000954030a040411105405010f00c07800d91001c01c01414400c2d0b00c0c440900d040210174011070f1040380d0700007098007540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 497523264 1250 497522014 497522027
    0xc050d1b090504181a0f181b030c13020910020304030803040204023004140a03090905100b0309030a020f1b011d120c130b0108040602031803040f1e0e060907 69
    0x2992028801c502000185c401006480090794241c200c0d60091010403200c882d200713102186450403400400c180b080c0f280314845411031078030b03503143c050113a8424403146455010780071440c91250b140145c2d13152161414010303005000003920003150010710040c00002c0300c0c0300859030800d404845c0561541c40c0e80802c00c0011851030074414207052034802548805101c82c2c151032056006081100c103aa80f20040300e51a2011035100400180070404203000c0102280d10603900529444c02d143c003281c5d10780c035a000590b8003c0d55518015072010500303105103a030412100d21081074005c06490b080b511600b00c800c00c1c0e445200c08505011802e11803074030450041c8001c0038de580340203000320a00f50224a2590b100c1c0070328078006004004803440101000c0c0c1c54015806a188180d4541d010340d516500e800e8002e41020b040700d1205000051401c0e1041d4042002d000900655070901d40040e190400b0750b642a1424078040548441c610002c000151034810034580c03051068500d42c0240c0c1d140101280d14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 497524514 1250 497523264 497523311
    0xa031b1106040b040804260105010527281a04060f0e0903070f0f0203210a0e0a08120307020120040909050c090a060807050d0b0c0f09040c050d1b090504 67
    0x203460540001004140c1d907402ca03049040f4200700030811030341c03198140701c10040326407510b80625043c01318400c000c0000078607141c1e01003244191004150181080c00c40400a82d288de154881d8036080c100a41c40c40c14440b42d0000740c42241c0400c410b43c54440b65000b14003070380c418404065184000508030b408203000720385441b035110109000301f81030345c41c0c41c0380f040f01006400c0e80a031140260185444544c0d4850403650440f81c02d800f41440124441112810f51162400d50883c500c22800a800101000030100c1210341e2400c40d501c1e8901003800a08486092070860802c83d0480301c15200c80807000d0881701540c0c0b02c040b020850070818240395243c5141072001d10740100d2184108401d0558940c840026a044001034545a503910320400c5100b000c480c40240c5213030040804140400140b000078010248a00e1003542440711020000c0c4c00c4035405ca1280d03012030000620150b400349984640403800741400c500ea0030b04480e840009010001500030f4030f00440d0350748401d13080a890780407519807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 497525764 1250 497524514 497524529
    0x111010207060501171603031413030c0b31231806010f030b0315070c05030a0f0f02030a020c010e1207180c1b110a09020a031b1106040b040804 63
    0x25540c0d00c0d905c1082c11031101d5101650360080d0101016840204855902120340590381e00c00d049000001540c07855020f415405040c804210780000000c2c0c0914000c00208004040716481d1030580d802c0521501109042a40c084d0001105e1081510024080c105035000010302160303604010b41c5c00c500920101c0c2c41603034066804550492911080410b807880344800380e80b0815801400d000a400340c6986640c8113074945c0251080074890b842c1c1e2200f141e44141c1a28040462485a4980909550106002e100001e081068001c080760300100e814039072500341d100442c40c0140c8000c00a45072840e22004504002281ba8946101c1e580d41031140c2420301c00c801580c050341c0c3d4132200e801c65113a400c1c7c8900c1d8400d0070301508a00311030007813943d003407400c1000701c00b034030395400c25a140c02da641d41040d06c241e07004149443c0490710f45001e102400f1510f800d0303140008d0551601b540380b20029141c1000b002006200000d200881501050403038201c2d0740300c0201ca1994a50386060007041c0504e411084 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 497527014 1250 497525764 497525771
    0xf0608041a15030c0402270a03021905010e010c05100506060d0c021f0b0306010326030703051008011104050105030a06080d081e130f020103090203010c120501170a02011101020706 79
    0x424118060b0078040d680703908404480f001c0c0380f40400e00040e4002e41102c2c514411070020002c4000204040c2c1803954140142105042e80d00d9600094903400d40c503880e60b440482110061240b940c001c1c8003013004000900303105d0340385032280c2d44503503503a0b2500c1100740c4070341d4486002c20701c651140c00c282e030360200c0b00b010103024404050078001d6417a800300c540c20a03050500290700c034813511180301e01c0b520320b0005170240156070300b10b0704e03103003180341488020b00348410b03a031000008030403101c801860107142c10b42d4001c929401d00040361003020322035804c0364100703924052900b200c21841000311003c691003820203d80700d0361655280c0c0700400c07460744010158014800425941d990040c4054451030380c08140d0500490394250b99110307a081150b00c02c0c2416000c190020226007040440c1707816600c149804110300045a010a095a0b6220000710103d6844103504505058078050140500b84403803454400100000800faa1a590396401905000c0158008190f0100030f40407640190b802c8a01030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 497528264 1250 497527014 497527021
    0xc02032401050402071e050a0f0f020310050f01230916120c02031611030a0b06121b06130b0a0503010303031b090501050c0c0a03060c0305100f0608041a 67
    0xd640304401958a0803501805500100b0540740502c00c3d914255088440006d0443d8928642030a60a405030140c07500d10901070300781c000070b8000c68100345082c403030914240c4414840c81810b192000d00024030221606000070804007022061099046825904080220507490344942d190001c000036010341194180381000700e000f00d154841400880c1c6540c0300c0d0701c041d04d034082807805c0b216080d0300ca00060300100520202101100035500100c0d018802c81c8031508188000a860703c0c3c48000112808a1800c0800c140c0f071420320f04589400c408000542541440701c01402d040039207400e101ea00c2040d004c220551800340d00c16800b4041e04141010300c0d90361152220107040d42d0801d2208030002801c2440015030074007000006801c400e9651075500d441c0b070070302e401900c03940c02040440b4107910588200704080c0d60f406d045540290b02502d8001203400f1800801010342e040149800c80c20000c611041080d081510300c0700e4111241403916902c551564501800071904008560722640810b4050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 497529514 1250 497528264 497528293
    0x61306080f0a050c010c05100209060d0f0b01020d030b0603010b030403181e1d0f1f0626090d03020703030b04050702061f120201050f040807030b18060f06100c0203 72
    0x4202c092401542220b2640041000444400c1802c0c9030003401d54100b140b0b12158024150041c010398000140b65505000e110840002103500c426180c180103034803103c285120b540c061003c0c2c6140e1a191070700b0f010310948540458158070040c4601d4400000020005041c10f1117080314004144a0001d86408590760700804690404110114466000c84023000184640866800310120084c6c2103918201d41d1403030048000c3c07000040003484131403035158400ca1030081709100c00001e0900d54803404402c1150104040c80160088a074010500110040c0300030000005400040f18a46207405a41e41c20355140842c00340050f072441d103420a003000d0600920302e8011540c60310440d000590920b580030407076011034550809204440151405418003009944140b0091000003242d81803180b4003036460032118900300560307006441600b080c01c140501002120140484180410014522401c0044280000c040094817541c801c1080740c4c0c080810f54016103450b0401134009040d0392240628840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 497530764 1250 497529514 497529523
    0x201181d090d05120a050612060106030c03061406070210050919060e0103050421050c16170705060d090f0b0f070908210307090909080a08010509040308061306080f 72
    0x4071541d050094000c2d40010780c1c4918243c1d881c144c04880c00e107206031200d120a000411000d0318554110f1503a00d0404034007002040824020201540d0000315203e07404402400c84840e9048030002950301141d035141d0b666046c0c1500c040c00c0d01100c0f910701482c4074107001d44040c814920000d800840600030001c992403040c00c03001c215410b580310309840a1031100110121032003150002c00d41207180d0f80322032202446d800c481168650a04000345070600c28941507140600a034407c0440c0208004148490610104454a640300100080c8001f6003040e0006500d401500e4142410603518210078040c403840d540039400d40c4e03400400131803150810141c064620381c021140c00d4040f8401d642c00240441002810b9504040c0303821841155846000404806030701c0a40300801300030081801084903146407141d4807500d840340c60426900c3d03042c0c8001070b08a1805038001072090310501e0401011a030050640c0c2c1d8080e134101c0d610030b8400d1100c46508000c2a1581000e1068460342003402101d000026 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 497532014 1250 497530764 497530771
    0xd0908040f060329011701080105010f0f0b04060c0303061205211606020906190903050d0e03030a031508031b07050402070312020c011e090b07020303010f030201181d 73
    0xc940645600c016000c1e602442d095040d20880c100c841c10382d0007050546400f15100500d0075900011110451b044072580030b8005051503555403004101c10444141e02c41c0050810a10521015203003011041582c000d9200700c40510914007200c83c10944a0350000020782071300000e0403490380709070a04540e5200c07542454007103500c9070340f580450f007050107007552803421030b42049401442c0342d40c0d180e00107504100040c41d0003240c20f02c0852080f04004800344c01d400001c1d0348074640c2d68a9404e001e46051960003164050007540307034811905032408012120a41c1403400c0c08200720141203480040c1400c01d6000e1821400041466144514013404000744103070001c040354130741c035229030410040b8454024024041541040b9820203445640c02400c2d5000100000180001024541c2d092403207401c41070820b0ba950703510035541040040341c0f0300b40d0071280e1032000714195810409942042c10f0030b404041d05100c211b954100e400c140c0c228030200a02440000c0034040c15907201c1e88050060140c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 497533264 1250 497532014 497532029
    0x506130203281a0d02040905010c0206090d05180616080c0102040801060803090a230d0809090a05070210150801020705030c0d0e130f090204090b010602010c0903051e030d090804 78
    0x24200d65058280030700030a0407203800c0720540b000d01401501041030b0241c00c4030049800c0354491f040d4801085081c030558041d034105801421a503e1705c07440c0503082c02031218451052140912405503000080c614002076064180c40302940c03801c5401d400c18100c4000c410017000040c0000d0f801c1e512200640181c422101044000e10180361520b502701c0e100d024207800180c000400410410101600e044440a10321215981070814044da4020400d00301c0000e81c2980c641e14001068030f814101104559448141d03650100f056040240c8000c1d01c1e04104281505038585801c0390640d451030780952030004011b0440215035801c82440d00d01c1c0c07130b03820450000381c1a0203422940c1e0900c5000c1d6540e0301e4810070092040405002c0c0d005414000c24500b5401c1c0d00d0300e6070354408407005890f00d20075581014095507007400c0c07541c075045c0f0003804d50f0b10461105c030400006020403c0055800580d4903101034005291412003c02d81e0354051942c01810380c60303100300b8103024840302404802c41c001c0c400c0c0e5914 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 497534514 1250 497533264 497533321
    0x3030c1403090d030b15070b06010e090405100c1115090105091908071119080d090303050909041e03080403170106020307020906030102040b0d1d16090506130203 71
    0x125429000c0c00e020807680c50529420a81d03180c1c542070f200e0340c002c101c01140101005010071a0005008580c1c02c02c0781c003240c7d000040f4051040640e0008090b0024000495101405103000d41d02c0985414511204c0d42ca141d844c0d118440455019195048101b542e640865100c0c514080141c0d1404c902591241d6055280134040313405c1034804248003a400c00000e050700c0101d401c99480c01c0d0298003c0506854910b03200382009650b0740c40c0c0403030051680c1024600303031032281401441d40c2031601400b603400c00e000800718108006504402a10040d00c401c0b40c040c9074540d52418120b0416481d25884007032010038950181c101504181c1e11030040d8081e543c1c1d40d502e000d900840812184080c05900090380c02881000018582060080c2c2d200030045c00160601d550340720710400a8118a0402215a480301d0184441c4140804a003204a500368014035100600e002c200c6201d0303602c0d0040806090302c41c00007940f103465464011404100f21401196245882400281a001d4140040010980 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 497535764 1250 497534514 497534537
    0x330b0a0503180c01020a0f03020709050a02070213020313060b060d0203011e0e0103020a0314070e16120603020f09040c121208060910090209030a0f0303050f2203030504050a0f03030c 80
    0xb800183d961896038181c008146410300c9466204034a09280d008a0441c42390080c003107107002242c050300b802000310480140e04d5160784d10411489407802e25030024407904c144100014020a8401044a980c0100300000c1b01d1200d18046103a6200d18909807141c40c0c000000026030562000030024186041d8010940c84c68941c201c0014a04003840041d40c00350b444001400490388000001e0004500142122100742d501c030307044482c1203000c036152840420b50a884001864015030b5040044004450400c070035401c42d40001d003034030020414640101d000f6000581042008403803000034210000d559181000b8600e80000403000b888013040000700002c0204038031b814040c0030b00f400703a01c41c010010030752420005040005e40104804c941c0c18031840d03200e50040340100c0c1c5c0400000340a6640410303a45800c08400f200614041c2000f412504510b08031020741c1c1d012588002c52a07454030340070445450310b04100b840c0030960b00b4080c10340e800d00d4440804064060748034650760190307615200968a07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 497537014 1250 497535764 497535811
    0x302030f0607120e1c0f0813020306010e06010219111215011401020709110301030606060c0f060b18041401141b090409140115140a030209070c1a0601030f330b0a0503 73
    0x2120302310002e41580c44800144000e100401585501034018411191102459442c0500d0141d00c40c0b02600d0320039444900003100e0400201340321035004648000c025000003801e0705042110148916841007102c00c09900040e8403d2080354010040403105000d00c4214882c0080315510a10040b030709039140520028409001d00e09003240c0a811007541030040c0344030389404000e840500d40b881d501c0000103044103038804030104514080c0d4043c03030310b035280540000348045c01c4450300b848429101458000304208041c5407191182007000e02e00006844100307920204000c1c24501000600030102800030282641c0c05500c03000301e140240807101710240d903e680003c0c1113080b07048510f80040e40001c050002d07040040703205801840071303d08000c11258a031101281d81e0601c12040c00c000c1c4401042c414a0341e818080e1071926500844208003100e011101280d00380c00c510075040601044d00e5592002c00400b501100c010840300320200c0d82c1c0d1b40e446070010700d05c0d80102d40480c42c09070761004145c00740 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 497538264 1250 497537014 497537041
    0xb01021506061209011509090506061e100c0c08070b07030f12020d020a021c0e0603040809090c0409060806011d07030b0a080c190b0a110a0c0608010302030f0607120e1c0f08 76
    0x66000303004ae12480c2c0b2910305100310700860480809020b001220480060340310503209215440c215500c5030b803140010b03e0320700040461b60b8404804c0303a108420030b016040300f2000311002e003941800c040620341080d10341921041404094845954808503015500b910117400800040d41d40354207488804025104200c0c041da8041001c0000905c147c61000d52410450004c0d42c0090080684034208040c590008681a8040750051920440803e003000b03160a1030040001526900e00682100e41c10b0460700088991010312241400d00030380c001c0b8117075900981c00503090600c00303011030200316140d103d22541c4c2d1103010744043c060000d51000c01c1e6035102d02c84101044c3c0d00c81b10300961510003c402d0440305031101c212401c81301c0c081c41c161000002c40444400e40200b0b00c549031001e1035071450042506008008a2492040d0005410401026030044d0800e1a00030310304000103912528070300c4a8038044420522441c0303249840d84960782d040d00030280c404640c00c2607482856075503c19400c0c84a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 497539514 1250 497538264 497538281
    0x10603140f060d1707030c0b13020102030901200f1c031104060309150501120303320c070503031014010c0507091a10110f010b01021506061209011509 66
    0x100021240818090329000f0002103c0358042c40c1088014401510000042c1c0d00410040f4042800b442150b0100541045c255130710030b03a0b515000000f01100e4001075264451192413904004c038035440703140c01ca452540900007001c00c4508440e18103414511884d03480903a45500c040745007216800010240c8280504199542c48100b1241840d141c98403d401801c409081140c2d8600203500d501e0b4464910702c0f07030500a1540c07250312000e0821900300a4215503040000e6050800400300320f08a0204480942c2c801e0880f0034814034a81e601c400d074866481c0949000180f440c0000000e200201440811000559810300020350a54003017000654848402c00c0e03006041d0380186034200000c6859501280351212445104010380d5000c0c0001208003016181c610045482004040c0054208004040303416410070001c208142a040020350f941d040d400210a0310790401300000c0c5a81c403246c0c10386d0805640c040340e00c8142d0a0020074140605807201d807442c2c00b9811414005407403440d83c01031700c58 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 497540764 1250 497539514 497539531
    0xc030f0304090e0c09132603060f060c030f03041421030c070c06031a01091a070203010e0a03091706040c060c1a0703090b06090c030c0a0306050a0e01060314 69
    0x6402e00d00b5000070007502004214082c6802182000c0e070850322500ea055209186000e10080989820300d4264800c2c1c0680d102c0c44110b100000890108091031422a070704068111407100060301000000361b0a882011460109400007050703400640d00c01801942c05544550f400f2580140c911000e10ba403a0380524000ea54a10000005007215007103c3c01160806a0702d03145034540f5107182c4480c91000d80c03079070010700043d907100251146031580004601d9180c0c824a0300c0b015551034058840108100740d410020150400985142159002d5012116003080c01d015140c0c00800303400d000e0008031030791142e01220240099004030000001c00c00c0b91159038007103030405441c1d0400d4030031941715518490480300010300d00841510096081d0800307115400d00d580c00319003c0c980f07183c88021003401900c030601496903001400410080c01050369400011090203907145c9000d520200e0203414594440b0350400c8032300d41d000c13070521100406a03040e075445890500c19110703459001c120a02d02241c0149 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 497542014 1250 497540764 497540767
    0x90504051b0a0809120a12180302030a0e1818190302150403120e010f1a030a02010e0607060603050105010e06030303040b01031202030d1107030e010c0b01030201051b010c110c030f03 80
    0x104240d00480e02550402c8000007118000c030402c80c00c01590754803d840d40d0300491210062038282c012180290071180d1800d40c00123001707076040c0ea4007139540e0040a003503800384056a078290281d5182c0645d0682c000c10380001c0300c0d240d401d1010000700507510a840b100c05038020300482400300b000600240218079816030081001e9948401d4007a54003801070012001c001442a11002d00a09802400703080c05100c0000100d074180d00c06040c2c21502100c1c0a81800741420388805050358010911242c8541c0a080280720804200b000860900c81d03400001c1200d4900071000c01844415804035058400049200b08191110410140e5078007084400405484103400140700083c01d512082c000b80300b107070048a040c0303c01160300c60305031040c3d00800c3e40782580225604050590203204416016828203241e240b8100d2500ca003d100c0905000103414000c0c000f641c0c91b00d13000b1038030075004101c054a00800075003032a000300400c8440c400d940060144661034a192561070041403241e00184120002d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 497543264 1250 497542014 497542027
    0x3010b07030c050609060709050f03100f150b07060b010c0b24030106120c0501090f09240801150b030c2506050910150f09091103030406090504051b 65
    0x1484154000c280c12020040750008100000c2ea00f04411401284000040c046c545003a1500501010143d48000c4c07241c0c8281344602c1a40c0c9021075400c4d441c0c9002003020440c202e040800501510240a80c0825105038080000714140140094a0210701c10b0405100307180c4000c004440751045604040c01d0f0981400103d0440b030b4406442c4915407880d41418180207000c81d0010b800c440485e0710603080071146104080410004021010141c1800d0924a401c9400d0403407036140d81c8d200b0f002c0d02d0107059513035140d8402c030523300700d607903030550601d100058441e44c0301c0500a001c0e14400004100c0c4041042c80440d9a21918013a0391203209907403c6a420150b00e5041250602d0350006040300c41e5078003001440c042000760254034816079000000740243c11103c52070303008442000d01040c0c80d12490301414850700340d01c000c2e21001c9400342e00012908010b28108500c168400340040c603414400042e00046203600441c0003000c6503c201d070100050f544a61425a0208407040c9401d28003400b00704d203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 497544514 1250 497543264 497543279
    0x30909060524032a0d050609150d080d0f0b0405060102010b220f0501090902100201051308030c1309150b09130e070f03030519030903020a0b0a18060c030c0507080301 73
    0x6180c0c4005284c0a08001202c42c091000e0b0b100e41c40b410240000340c1c0000c1100e02845180103440d0032000598507000381e07190052520340714003031110a280c0f00340c1412404c9814408035500740d490030b4a40d07800c1005120242003a1100030b110300202c4070b0182c0d044c900001c81641c0184141001584003800700521590042c60002e240395045408a04069a07807503e8080b00c0729030f10903240a40300714680000c42261a004000c0365114100c0541d046a05000c00c000d400071800c0c03c0203c1c010b510a00032500c076281c1c81e0121301d00d4050401d86240000d240140040d241c072094001c600c5646000090042d8aa1603a914a0051142440c05174100c10030308210b06418590760b0102d5100c4c0340c070320140c81000e9200e44502d03128100640c0706070002000803801ca8410b200802070041e021100d414200708640103660084e44400e04074030041c0580340b500c000204660065004148103040500c0c1081c28182c0f14582a401002c4103150400002c0c034002600b40001c0c054011101c280c2d42109445c0d05580c41c0900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 497545764 1250 497544514 497544517
    0x108090a110105130f03022407031b020603240102011514040920011202070327091d06092a011713021305150105090a030807030909060524 61
    0x60746810003000b0000001421140c500020203480d202400302c440c14a180100140c601080740c00200d0158060700c5c00700101d00c900100c1388450341c1402c080c11703c0300c040018414001040e64010350030140000400c14003507810521000303c0c400360455118061400030049080701d2104826060b1100810313024807112005000c440c0561030300034000315151003191340b0a0040e003030040300d0150b6121807500750360131580c022900c000b02c0600d002c01142404c1543d18000c0c80a500c415540f00f0f0030300e1400c1c40707800c429200142240904111030042c00301201160521140303554282035680c090241002040d00c0d031401091440e8450426101481c000801030000c62800b00c0f079000c07090500010001c3c40007021040e03194184a4680d80c0c031102c2c017060290050021a19441d2102a034441c41c0c01e040000419508260b05160002031824548130b102c4200070032034010582d00017070895400414a43c04060f40304020200780c0c0c03246801805410b50392000d00603000c82651130110441c00010b101900d00707060b02c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 497547014 1250 497545764 497545793
    0x120c090105180f031f0b060a050702060706090506090a050c04150b210705071b03031d030f1b1305070e010f170c0d0b03070f1e031406010e01050108090a 67
    0x80a1010600040b80081d24010655a6200171562030180314124210f1500c22000800415640c1c01e143c41c001c0c980090081c400e4240003842850003095100910420b980206d0a55a00074111562810401c1105070360f902050310480b40c51003250f1400e855401c1900681d240300c0301ea840b206d02062b0900001000c190880c00303070036008112001000301590386024500d0300801064590035a2181d0340d01b820f103407880958521002c407084001c02040000d61143d42d102d0100e00010b9004c60f1655003400103070504203102180340c1180310b601030498682c2610000c240c54200b0450f414030a000f1001c44000a9840469018001c40d010296881c2c1c00c0d40920142000c5001510700403406c1180d0010042c1c0c002e034141c92241e1285004104615117485070b204061041c1d0088008042031850036907012201c000d540a40846000b0b450700503c240a6030000107009140d20408138010400c1a6080941c0d50109104101c24540c603800002040c1d4050702c007543c040d200d0000075001e0140385071a5100d83c03d4000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 497548264 1250 497547014 497547019
    0x1908090904021c0b01050109050d030824030601090c08060a290d1d011508030714121b19030f0e0109050a03050a05070b0405031906060b030c120c09010518 68
    0x30034060a9400c0064021803c95108040307412441d41400b00061070381e496508030380c0c0030306c00076a21440844d070000360442e0301100060101c08440b1452000840340c400b0740d001540c05203d00f400200c1c415510340c12004825800c2c1d61030050f0b40d6190001c104042c007052284000d074522107841c044484021901e107010446250300314910307008bc030940d81e07800c58144c0708071300f0007403d11078203105c0401800307000e59808442032013100c0c031106081c00710054a82c414804010001d40456984840c0042d00340320036850229884241c585483d10007500c0505907018020604540c0580f0b2007810b036404100c078188171b4083d00759403140079040e80c070042680c338420780382c21a60602040450001c0c090350341c007054078003a40c400c5015002c10310307103450103904d81089a0803104c540d0100348018003c5490000d208810840c01d01c100e01c030b844015040c850010103890700620610b4400200700100d000c0200d00504d20070303009550410441e030302c00400001e14001e07107503042d000038401c014800c0c0007101002c1c3e004001c90300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 497549514 1250 497548264 497548279
    0x8060a0b0301060b032a0a11010e060108070e060414090a030e03030a080a020d060503070801151505031b04090606030b100201051b09120d0306030b0c03011a0f07060c0809190809090402 81
    0xd401b81100300e074000403c44400103460045140f9840700a01402d6004040720005000c0c4d5410b00800c41c1c1ca44034203002d46220f0240e0240081e000c1c0d540c0d60000e070080b5190f4503484c0094146103480d1a103c0100c18070035000306541c03401c0c060107810700208641d4801c6181d82e130385003e074032140c040c1c4010f03501405500c101c0640b107150118450394284801d000034110040001400c1881d02061100b61146603c0086150b0000001c0300006400c00c040b030b9402150071048203800c1c074001e6070a854501450f00030700400d9284c24404161240c00d03510a0b000b00108440d041070100c07080c2d002b24280c0c1c4044818601400e802c10b03007548100b103204040d1003680001401140600040c0c456140303080c10ba074002c607000070b80700c003020804e0004e014001a003003000c109281d440c2d0340c103024181030150760400d0507003d84040062480303008800c807425901419404141400101c509d010014a41c500c1601c2d0400b8a0145100080c5003103248159443c0f195440303c10340303080622440c204504040000d00c10780e000b884 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 497550764 1250 497549514 497549581
    0x90601020102120703150905010b0405011107030b040807020a150e15070b0f011403071419170601061206030f0b040f080301150f0c03020309040b0105040b0408060a0b0301060b03 78
    0x100b002d81e940c80790301030345c1d000075114841109810200045500203040185010010700c070203440a400c44003039030f8080c2840c034a01001e40118914204e40303903102030b11600301c2c0410b100410003100700410f000303070003151060b2840f40c50354055141c1d00252030200010400c0040c0b0541039042c80b604000c0344855054080b801c0c4411521001c00300181101d0070390084050000600c0124002441d03d40034090a074001c00400d0b0a04a8441d199040c4c81c5400380b082c60041d400c00c44038215200c854002e0943c440401020362000c041c407071303604d107002c4c0a404045404048400d41d03000c214820101200d41240308585022015210b1540e0030001034410342d2241e20300c01c01e000c0850940070040d402084448191050f00d90b251000420040200d60014104003c44001001096000060b515006d000b16000100d10b181d000041e0740501c541e40c080c480c1c554001c2000100d01c8004a5564495a01c0200074404ea9680000709402c9512038000d0b0707101460203101080c43d032403000c180110b101c0880b0710513956210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 497552014 1250 497550764 497550787
    0x8090f010f0e15060a171603050102310515040509010b0a0f0203360910051e09160207030c03120f1d010c02061b0a05061003030509090601020102 64
    0x200807100440180752501c00005600b00200025002800c0341e40c111411818102c1c001003450b9a580302e1904250003030014201c2d080001c0c8000103074a15000940a2429580c2c9406030107900a6200341c50301e420003680f200c081c49050ba060100c0c28900f140c00c1c542c03071400c00041201c80c00321a001c450400e003080c03001051a4030341d038401f20b004e080c0e00100d031500c41c400648020848441101d29500710f40080c41010410042043e14071114240350021003130a5664a900b040b14001203106503602c18000c0b0180060900360704036000c01d540d0706540c10f600c105000f20f81011002d0440c0180d5170060250400120035a1100600c8100d0b885184140c3d50190b03500c6d102d610304d4024075042902d000300d81092004113640c001e40406000d25150610301e001c910246401801d031342d840842c4905200e031400b0b0910455032100221005110072240e440c4c44030713403c0500203035201861941102c5501c214000304c0c00300c035251003042c003c8279419a1018901f000034030070302c08070030006456039055640a200d03010310003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 497553264 1250 497552014 497552021
    0xb0421020a0f0810061203120b040c05180607080a270305030a09050f0a06050a020c06030a05010905060108150411161a1006020a0605180703030504060f08090a0308090f01 75
    0x614804201800060800f1080c504003982081d5a00e030292600313a0400c00d00041e10240c80c40140c050400703903004a10b8001d6071010301ba000d06c0e25a8400e00d448034030000550400060100688002c3e4107580c2450764138107100041c4590b0a018010402c1071015000d00d0340b140c01145803c0140c550301184e401c980301c80c0c840400c0d00941007190550400300710807000310ba0201000c0c3c0200b100301c0700080410781250100e4014001c034040d0208000c0001150b001550003006200c44148010b44203995a2402840640c0200020301070500013600300404100799611071011a400b03021040090302424000e5002c100c018020314016074420407040c041d481000441403601d01566000b4082d03040001c01d000b001461502c40145078041a07503180f40700b8000c65a0000c3c403450358030342c80040006c10351520310b000082c010b01544801042e101d641e0b404010164068040d20840744c10361600002ca03850704205031142602140d40c1c1101d039021400b9840801d00c18030340da6030800b407088195110103005110581c2034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 497554514 1250 497553264 497553269
    0xf0c0102070f06021c11091513080c180f0112030e100206090601050303210a110a1e080c0306011b1b030b10030b07050c12030109091505010b0421020a 66
    0xb5680c0c04904580b140300e0442c2c0000603405042030811036030b5106c0011490754042c0c024481d01824507008910030b448119811141e070600e5031401404904d6440801c0340d900e5600410081c0685040c5070301c40094880075001c9400380800c042d4401003a070030840101d048607820f103019030402846600e103003019290345544510043c0294054007440c6000103080345860010fa0056020b075004003d04a51089105102c082640403900c94242ca03813610740c5204064440a100300e40c40950000d4040c620303030342180b641070203003076038078287d218181d01d2000594000388202c68901100200304000340b000d612030200406071b844030980380d080041c600e85038075142c580d40305142001d40174000d00510a001140d60740c01d500c90b0f41030a80d070584504580e15050302901c0036004000344200407402180c2600248881e8128401101c66151a0760399101858003a1203020804e0f204c850b680144401d02da04180205c5d41a101d060850600d031507e0142108109003642d10340000b4102e580541c800142c2d80c1100e0b4000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 497555764 1250 497554514 497554523
    0x2150c071b0906030c211e0320011509020304030f0f031d03040602120c0706030b061605010b040b1f0518150304020103150f18020c1903090f0b0f0c0102070f 69
    0x3281c0d420703c61151a186d40c0004440c40c041e40c00c01d140030003c0d8034025843d80d02800d041d0294202002da11b0142c0d4200b40a10b00521202010086080e02c000150f0182000c80e24241411070601d1380d446c40b01040380b00c190740c054000f0b00425041c51015002c0e06508001c24118034001800345038041c5102030410034624061019000014100912541002904000f101c03c00e01309181659400003070b5518681d502c50b03d814035441e194464020307911070042c0c644c440a0001c685405014901d8a9030007000000c040c3e601c00e5281500300c56081c1031410700302c158588200319100d240c1000c0b82040d29580c0210840b003404400c0c0360700d2090f45482e443e50f04031120b083c0280711622030901e4400501500d20220302107440050b05c5800300f042a10003c614000c85880e4003503024110709450540c00a8860740d0350079401c6101d00d850441e000242c07040d140d0b0526010759207124840e070700ca00e8040309012140c8190f04440509100002407208401d00420721100c20900052610409540d1103402003035240007543c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 497557014 1250 497555764 497555783
    0xc09090f0606050f0d02040b0612131209120b06040e10060306050714070303020a1803030c050c090c0d0e010617070e1e040602090103060504180302150c071b090603 72
    0x8042081c1c41c05018054401214400030b00c0c00503201107058043c4400c0040e114075220010400383d615000b04851141540f005e050515280560400c00150780403082240e400204401c14980d251055850100390b4282e0390300700c0c0801c585600d5010401d10060050b951003a540c2c48852003054007080859542c0c1801030b804140702c1c0c6035003030070710031510001c242c44140020300707070100c0d48100c414080758440740d4107040060725000c210400300d40c20541101400b0412468000101c2410341209081c0c10305842101211001c079400b4050011041e025100ca060f507210902100d41d048480350442c0c419440d00e800000741c05699225614103035a10045000c4d025086a50140000e0300000c00342da078083c481d1103905071f4505001203136540e85003004001521a60303000c1001c113600ea2003a000180140700043c824407040d0042c00b8100d00b9103042c180304901511981c1c0501d007a441540d0211407041c0402e800407421b000c240d469101800d00000d030751128080c0c1300313600440d00781824402c60000d14000e000c0349 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 497558264 1250 497557014 497557043
    0x501020d05182806080a090807020105031e01030605010924050d0f0507140907020d0c0308060d02041a040e0f15100312020102041a03040c091503080711030c100804020d0c0909 77
    0xc0c00100c00078249201b15030078113001501040b821000c665042c0c0d0f080c6000b564036500c0d80840861000c280a180b0750a070f40220002080c052281c03c001d059031000c01c400c100c10f00c5d50ba007450501001010742c928181070104010445490314079006d01e1441d01454024610f40344507901d1504285035900032803e200794036486d04641c0e0809180c81079000c04070340014954903040314009003901c9004480181040400000203129880d40c40e00009407d03070260044c804240340001c4040380c088010761071030140340742c90740c16401d8420010f681014285984082c00d0000392144481200c0080180a11120742c0008000030001e030740140395076505e000f15800140c41d41e0618070304070054910f4101d200b070b05810910600001c115010a02d908560352820005413034910074002400100c0154005003c5000100b842d0323050258000b82c1d40c904500490a0720403e000000801c021604121a540f000803035041c001170040c18200f4452003200d0051920041c0981d07101008020ba560380182155481e041c1601c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 497559514 1250 497558264 497558267
    0x504020f03010f05310b03030d1b05070b04110102010b03100c1b0305090d0309120302061806070c06020a0504050d0f0b090111091c0b011205070501020d05182806 71
    0x308405440119000c840c585a1044a2080b01c01382c20840104000b9800705c2d0200040b40e035002e002d05801c05815240c8410b55800424010420711418403808010415042c1103c0c0c0f0910850703140c140e000c124954140c846803107212810040f16540c5040d59038030b4540038001d40d030402c4180019210b0500100d280120344400810848030000e08660104140b10150000380e005416240c0c884803d4415107081e43d018101100d014030a0f44c00b110030865000200c01c181640419150b10410390320300f1005000c80ea0301e000b40d039504011035013035000500303400605c400240d994004007940c210a150050400e41c80e940000d98601790b202081315045808105c0301c0801203030701003171680481c010000700840242d80700d01d41303200c1c451010218403500c03a8002d9103010b14142811664002e8001404421941e11408168000074056100342c881c2c0c0324031f04c40045c49610000c1d0b825450119961070340d04140008043c0d08001c008001c540703901424800300f0741003941c199454a5050f0034500c0f8046002c81c64244d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 497560764 1250 497559514 497559539
    0x210180f051b0f0d110109050909010b1e0102030306010f030f05070c03080901050402010219050106090c080108120306030a020111030c100f0f050f01060c050304080304080a1505130206130504020f0301 88
    0x540e400354046015104107560781c1d41301c441d4569040b40140811880e1800100c0d04900c11780c002c0c50340038010000340600c035001544810201071007030307814990303032052014110111482450030f240140c1c000c0000652130351003050300801c842c01c10304001c075000401441c400152034081740c03008002052001401c05050744001e820741c0080f100e20003008941400d0700001e4940014040d4105100940500ba10801809600c000014a01c84034108034117214800c00414201082c8200082c2e845000c1412410704103410880f4082e00005000b8645036030070394010340b200c020740d2034140d101d4002402880c900340700c2440110102034685a0014202942f05061030440d44c0700c0c3d150080c2b06c1c1c0742c1f0082000b146240702c0c03117a05407080b038240040c0154451911614502c9035030400d021500012a0004d0301410000d0381980443c41140060b035400650309400e0101c806c22200d254940015001e46005414030100904008070107154002d0b001e80ca61000c10140d900c00c00305440100c0c40000100007644c0c1104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 497562014 1250 497560764 497560813
    0x40b01060c02030a060b060d0e0105010806010609180b0a150801030204240320030d0206011508060d0201180503032803020309030304060f060302120a060e06070210180f05 75
    0x2400c205071030868010940e20105408000d01c05030f611080302141e50389042c140c4451000c80300040c030010035003201c994043d00c1c0a03c103540c0c1502c6a00008038002c2d0007480044280c1c2c1a1451004c01d15602c01c0091001d4440d11240303907000807000401183d4401604150030b191001a154201254510b00c10b000844643c003141007003101112100a00d0540c00b007540b03c048940181c0c1154041c50f213480745070f2803494000c40c404c0d4907100b00c14140034045d0700071131004d0403100c0403802c0b1000301d051401c0585482e0f404564032a80305000820140056006403800640c1590982c941451241c541003c2460341e80518010340c040c00d140d0280171008840c00c40240141940c034903040d03066007045820700740e403400003800080c03441f511000410583c4042d40e0043d00110380040215080140c20510346440c3c000c5940250f80d110b042010300c030745101001485078016040c41d0b0040c09940c5070418908018000c0031440c80050705603281c0d5801040740105000501400f0718042c2240c0c07021030507030179003142c19a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 497563264 1250 497562014 497562017
    0x40f0218181c0c020103050c04050603012d03030f0507150e0313080c010801061b020409081210150c0809031b0111070b120405430b1e070f0605040b0106 67
    0x11140b00a02c6a40705806560950707080c00c002c01c0d141c46100c60000e0300d008603085540c00000201c00000c00b00420b4408038051400c1c1c82a045074035142070326105092003540005000b2400325044030217294851001054054002c03030801101000d00036030b0f441980c0d103a1048500310b52002c1000061034200c084500014140d0200400d0b042a4400c0064089041482110284204603143e01000b08200c001000126030080c02004501050310f0003c6054010004204081c0003840010315a4107001e6844015030764006e180c461400180c0070111900741c0004022600c204e024070984130103490400100154601c200840101145030800040c0300c14510071070f200b180e92088108000040c007400440d14020311200c0c20760400c0d981c90610350302c0c01c44a0306003044403562440c8035020510b6407190780001015080030480a6403100341103480b0a4105c2c0c066546100d00400c05100585012603060180104183c2d40c9400c181143e11580c994881c120010341c0c00949441c00c20007000701d5441c03041c0c05007089 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 497564514 1250 497563264 497563303
    0x190f0e122107050408010207030207031707050c0f060702371202060703090305150f090d021b030708061603050f1501210f060f0602030c0303040f021818 67
    0x580d607a04241a008609000c4441410000b00e416548140b0454001d000e200000390760300c0007103242c001d659070034510068400c40c4c0c4251036084580140c80444140940003c014a6203078002030030441041c080e0403565500c0041004002c0041e1500b280b401c004900a801c405410110040481040c0b6170854010b8450040c4200c00e0142e960890150808643c06840c2270f503c950a40c5415a0388604a803c040c0c0350740304849262159072410310609114542028050400f62601d200d002c1c1e0301e401c21a00007025030031a00c07011044850064640401c1c044c0102290009642ca100203400c0000c213850b42c0d481c0c0102001618540d41d010701615810846c0e6140148862408044903074000c4c800b808514100b0061069140840c0d441d00c044007410b02815004000c00d1031040301840082043d0301c10782010810301da00c0001c1c0680044151600103403031001462640e52160f80745000200310110032640800f000300503004d064090307c1038500c107c00031065403038800d9105503c1450441084c06180b50f020710b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 497565764 1250 497564514 497564527
    0x219080c0d0e0a051b180408040f14040c0302040f06080912030103030810150f120b03010203130b0c09092802072f0303040b09010e030a0609030f0504050a030803190f0e12 75
    0x11000029500d9642010480340c150311f691800e4400d500c203551045845102c12500803d10069480800442c0300c0112801c20688602440580c1a030080348212400c2a01500080100d1802450076580c401c4001e02580e8503e4031405084055030408e8000342d00040c140c100b0003036680c010a0151000c1c21003984400c4091804040c000d01c510021405c0004010384140c11462002441d04400041b950040080d912031170403030342950800380c41640c1aa415030b8003034081041101810203ca04c0044050310f032420a54030070400e0100315030f462a40d080d1540208045000d00703140d501c080c00000784070f00c1844500d10514031401d02e100034094219200c2074803a8442d00e80c1c40c0e50000403503086601d203140751915010300301c0060303d011021503006174040c0142030600c8200b140c294028030308030344203488141c01c50114200443d04c80c001e901440360002d14000b42400402c620b8030145a00c0804140041101e960310103a10055511030100140282e403108900c108444051000e140c0340d5401651913403c000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 497567014 1250 497565764 497565769
    0x905090a26030c070201032a09090b090a0c0c0b0f010302100206091f15030c031b030c0e060f120d0305060f0a120f020d0b06040f0219080c0d0e0a051b 66
    0x2c0043c0a05407001d200103940320459020f0b0b00503480070a03100840f140340740d0300b180c28013100d080107540341d0000807e152004a07054104d0301ca60174017240b01400710041070745c1d200d06140040c08d5440b012800d000b80c11900c03400046803009814845c4114100e00060355140d4810f0040e807000b88600d81d81550402000c01c003454000003502180c4611402009807002403481c65503005040d814000400c501e985030004c814050600f45100449125050f031143c030a29072552860562010301005101c4082c0e00001c200480021001a0f0840e070000c10842c58120020f0001d0002c1803106400d00c600d070080d01c19a80403540520541c1c1d07000308151581a015552400042c00080f854000c003500e00114003c480c05116a11382c11042440e4090070380c2d40910030030300b010000c0f590115503042c829410030038540c9007981e42d030080d648032010824400320900d105600c2511069002060404031803024405208559414062020fa414090026000c0c4164904006090189c1c0512883c4201400e08078840b0b1034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 497568264 1250 497567014 497567017
    0x3011403150f041121010e1c080c0c1006120c0801061206050415090507090e0c0904111201021903110f09131b08090609011b0c0c0905090a26 62
    0x20303500580c01c1341107440c80c03c00100c010001402c16100681510002081e0b680305600c0f000040c20840200ca009403515011412000d01c14045280001c2140012503840d44a50000d0500c0c203151909440c450216140000101c0740b542d8000110140c035507201c802406402822070019100342e40c024411207050810035500a0624000105203680e16000101802964040c1070460003141c8001e100488060a0003640ca125134020140c45c589000c1000028450028080082541c084c0c04101c031680c0b591610007114a0b805a41600810401100000c005003880209840e074115212a104001c10004c02021181d8090000c2c8070903e04201c0800d81d0300130744040d10701030310084070380710b000054840c40c041c050990361042031104448110158043c0d0382041000f80700340e040c3d400300e58080c1d54803d402d600f6a4482e01d06982d1415841948a144620800400710414051443e031030b002d940d02c001c6242241c1b0100c804580c0c3c1d42100b42904101310803910800700014100407000036064034194101c2da82d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 497569514 1250 497568264 497568271
    0xd0e01050a02030c06070503010e161205091c0815040b03030f0c030708030c0304120e0a03120203070b0118060b0f0a03150b0705060726010509090f0303011403150f 72
    0x1400008201d03485518030800499000c01c0c03c0d98103036241c1e801e001602500c190002e02950706000591000100c0503000d495184412681380d03a1010740b600c48a200400007440c020381501541c1c0160b046841d4005940400710300e1006c400da40701c8941d0701d40312900425081c00700100710300c602d08001e2034a0a6980000654000010746c01800b507039039002c91000303443c40c41081d000070700081c0301004000c004a80c0b100076500c2540205007071401c80410140444d030042950306401d0b8840360480c400d001045d020901500d52000340c0c0100c9107080441e440e510f03441182603009511800c02030b90300161820283c01544001d1000488041c01c041e10720f00083c1d19401409850740800d1b81e699969818410041f003c60010842c6825407a44ca24540c10203e0726110b00301d503500046034455080c00c01d6080d454004510301e40090814841c242d01340300c1000204c1802900940603071180b400d00c0b5030521801c0c00194024819103088401d036003005030a150a100800e43c00e441070958040801c00d41031244c0c49240d51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 497570764 1250 497569514 497569517
    0x3030501080c130c030204080706031509050708040b04060b1c060b090621190b0a1a0f010305090111280801150302070204110406020109030810061e02030d0c050a0f020d0e01 76
    0x1011411136808400a000725401700941c0d100c0c000c40095078540603032124210307041080c10701282030388407100030b402d69205686480c0061806400240803070012000230350070900c1040041910f60f0b08030001510044502041444510006500070801c5280d2041c80b804d01015290301600c0d03d406800030703480c0c0c400800d00d40d0054000d090b01c588044020b000b240d10349104e008201d0304045403414580c035045c0e8200c40e01b0300140d2a050400503040b00d454107107600188000c003118568401d050045014113000b401c80b403c60f40d214a0005245d00c5d038000900414031144070b415100b590000da1111078843e4009001c07041c00708420042c40803414001c03034150741d9003082c20096134550152006c54014801c41240084400c00400c000c1141c640c11f40102818601030303a924016a11001c010442041c0c4900c1198003090103850f032500e003600500c01d140340c0c1e0090b900544e4144000070f0f0001055480c500c071204000f904c0003d00701c14454100154281481441c40200100442c3d080701607d40d0320030101150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 497572014 1250 497570764 497570771
    0x306040803130b010608041104050c0f090105270a0e040b0a0c020c0307060504080f030f12060111011112070203070507171609020c01182f030d0c03030501080c13 71
    0x2d000c0700303900803028003460b803003000003015607900d040040000900b56011600d220540c079070408240303400c1c02814021661294041d1620541d00d5042190f03a000034031007414094203101847d0700e141d000740075a420700c80c0b0300803034600d214814080018606007904287d10300d00078441840040350800c005e41d40c1c81920a640091030702012a0181d107020312030000242d00d4442d100c0302042d820b0740440075000720343d488070450300ca01c1120390030340e501d030701a210b000002c4e000c040c0203540010290100654200c0e03418107198036105994240503096480f0005084000c0384001560340c101ca10714ae4034075601141c0340c805181000c03002d685a40c0c40303203e64030582c418014580400205c015003071007074204508510b15103d414650300d900500c080e401c882030001c41035107003200e030304e000d4101701422103a0182c0c8441d00c078415600c505481f4844050021611044641203000580151401c00c02c810fa401030903140c1d508501d500d894020300b51070b01600b0915080c0c04c0212800301c00e481d51071500d40310a02516010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 497573264 1250 497572014 497572021
    0xf06080307141207080a0c1425060c120e0a060906080601080c070f06020904090c050f061207260406150504110403030318060908040f1508060d02030f10020405030115050306040803 79
    0x4480341c08a900000d88032300e1640d01400349660780016015080941041815800c03c2e2a20740c0c4905d20005200700400300e0743d01c0710014005254178900c541d01c10300606003402510310b09000301d0718411103a00040e0100d9500a000e02c000f9403c958281c1c0d100e4400d00e000c400e1440c018010341da660041410041c0798086091800d01081100d1f016150b00144c0600104004e0246003441c84100d41e25102e41409440301f09242c18140c2491801c075429040c034414070752071944941d0400c03102c420703c61b007203060402c10243c8060344040c103441d03600e801103000c0c40e03010400f006030f000380b0262410140d10807032141d403401e00b1910b24426010103480c200c036014140000c100c881c00000c89041550258001c0c102c0d803400352040e0400060001030030a50761090694076034a611000301c5000b41c40c0c0c0c1e5142c0004078002030001030540c9070010b0f88140e0b00f4806825210700c02e140d440c00c2850200c1d001050104136801240034013242c1000d108a1590340403016110a4091600300829103449010f000504100c0c00003002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 497574514 1250 497573264 497573267
    0x303010f091e0203090706080f1302090405030c0604060f0e1c0315050d0308010e0a0e0c0d020111070e06010e0a05060f071e0503130e100501050d0f06080307141207080a 74
    0x21501d06140000250364074504034a0171034031480316026000c00705d1301080100f1071002548024070f108038012001002c52107025000c1000405004004890740e21040001d114040700500055020f58440c182c04200e41001e0301440058130f07410103048034550700804103c4581120f081c0f40c0c041055050800182c0c000703007085d2000032003103990000c0703800440f944a00030805a120580504030307202244807800e07603103420b03540c84140c80c1360312075010700c5901c42d10000d16a03160500c0784458040c41410407500e5401050401d6003001050303400300110611400c200841560404000c1c220160201c4c0c450030340c60f003468001440750203050076031410020042080e204105410310103c01e0198480e10a114440040c6005641ca5014840b805400388242900140010b403c901341c5018540e1401082c0826041034011185a00044441c03a078007526006a04440a0741c0c1c1f090601400307002d409150340c0d40a03400c0c941858040300741c0715070481d1321149921100410901c00d5038200396018010956614210301c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 497575764 1250 497574514 497574551
    0x30091406070501140a11031003150e0105180f30040503060f04061d03090d0302010b150c060c090102060c0f0d050f06040614010c030e0a1d180303010f09 67
    0xc009009620b130070001a40d580c60784070310b40e20642c06008184040b5007401c02d0100b6078013007962496808654160144000f40e008002d944244d9043c0b03000060b1270200c001030b80c1c03d490040d1030481c550403d4071001700d1f00241c103011a00c01c5c0000c201c001c0c1900e400d00d03040010401080983c0e803c0781c0c40c494020183c2085258212802810000d00315902030030135403c1c41c001d41205540c200c800310720b0505401a02d820000c160a003409068001c0c5003451801018403200c20141c0c0c108500f155a20081854143c0d540300c500d40340c4201e03070500070361035410075401c0c613107002405054a80ca0032010b001c00340240c3e0303001030402d911542c401450b54540300f2500d1042c1c07c030300a0281d003c43c0e150505c0104050015031f000d64034880c500848043c082c1a61720710410003240f12101c4294000344141c03c03803002182c0220101e03819040c0113404034103101da4880c226442c0001076900c110706040164144403081e590b922800c1d912030382c481c018500d554503100ca100804505440b800d0a41601d40402004200b00c02c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 497577014 1250 497575764 497575777
    0x2010c0f02040908030106081e061009031b1403010501080601030305070f1a1608060a0b09360106020c1327050d1b0c09020f04090930091406 62
    0x40061001c2d4460b458504c0c0c0b42c0d0000d02400c800614803000240110720100020f05060b07101072240300c40b50710b4903000e01140d400c01c101031600344072030114000000b80d205600d400128500d00720300c024a03428140610802d140240f640d900c01c2e03052400501c540080484c49504403689414160758400f9a4a0a19003041c6c800c800030f40442c10f00365400802c1eaa03144901840703042451030740701a40d4000003050f14040002c0c0c0300300f42c1085601409003c3c0c0b1200900900e44480300030420010040ca030a1042940c1035000c103604e4081d000c603854507846070303c85c0c1e10150140400e4000707004051404004106058032402401150302e840c0c240e05071a00884d220700d500b0f50040c2c03680c107400000741410825602c51030f4254110020b001906498009500c030202c26810560003e01e50b4503091600038014040d41044045400410040000140000c0a8401d03100c003540f0600000c1c0e0010030900f030300e84140051066080b10045944650645140d1143c0d400381580c4004081c01c00e0801991302041242c000e10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 497578264 1250 497577014 497577019
    0xf1f0f0234080c1c08070e040c0c0506090a03090803040305030703121d0d120e060a11090d0b1608091504050705030709020d050105040603020a0b0c0c06030f0403030c0203130302010c0f02 82
    0x80300c0000140c04034150081130040404940a0b0524007400c0340c8502089a400e000200210042c854929040d040001000c02d94500504007485507103515003001c1003550010710303e50000030050304158000114200415001c00654142032850310380c00d85034459540e000303007040308500550240c0e4129502081c01c0d880d910045d0740c0070445001c1590394400c1001400008032794000408035841102d40150000160904040d007525260301040754098038580380c858110140c280180030154492203400c03100680900740c040301d141468540b0300860b5020300000d108001c206030070400d00300d4000801d41100200c0542c0f08130180e94606125080170015001a6417500404000103034000041d0080c02020a0002c0108126642e40301000200d400c40e03c0001d401c80c02d0303100c04100d2885c8810140030002417410a0b03440110401d0002065a80201ca0040d1000601c40501090580c1032148100d031802c44d000452a00c0209100e4812250305c51000a0400903010084020021455011485607501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 497579514 1250 497578264 497578267
    0xa1511130b030405010b060a020a08030a0e060705030106170708040809040905010f0902030601050414010b0307122c010b06030a0c0e1e0312040b030c0c0f1f0f023408 73
    0x5030301c5012040e50080e58284e5266080009010031791400030121007103c07440717400800c0a02d0460b6075007022504010100614541c5e00d9000151032001445294403448850365950b550758106a8090300e02165020440f2491b00c4e01010000320701c5c0c220321440d030080d40100030f084d260701181001401078251090028103c0d401c0c82d41ca050581c4d59034004414440c400c40c145d0700d490b83c0300c00070721045480400090580c41500d1004000d0121a00300444d0403144910301116043d41c2c22081900751200301c040102502d00d1007030083e24111003419400780cc40c002c44c00a0195508240c001040e5020141a83d0655599a5202241d0a000d00b03841d1009a41c050200c1e11681e12681f40005000e01c14002c02d4000c2c011001c802c48503d401c541190190741b9480642070031510b400d0720601480d00100705071181c520621045100d000003c00000c02c0303d0503100e0b650009090030107070300c030b00b501d00038500b0094141c0107100007111881c080b0f2000841550040b5541044242005204410a40c114018008200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 497580764 1250 497579514 497579519
    0xb0a080603160e060a080c030d0f02100c0c0c0905070c031206091806060b0c03031f12200102010b21071206020403031e050307030b0a1a040e090a151113 67
    0x3c08102c81e600c0359504807059191617946507015516840502c00b80340d815003000841000540c002e0880c4107000380c0700d1045408001500c010b401c03c684070909840c0114a149900f003081212800944000e00281007048c4124107240802078201c056001c002014032040e40020005008161f000d01c008100200042c0038900600318504c1024107021000d882c89030808030085143c0e100b180858000c2c5210394000c603c1c41d5940c0110001644100c0743c0307500041030390b07030000410f50304000c503d0311201e0241000350200481c90340d08003406e051107048c3c0c40c15641003454180003560b07015505007072014690107000b80c4030031203c0c40340d041507101d405c514004803035001031030144030040c0d001e042643d1080d1100e0a4a469800c01e90b0b0b0340d420690302d8680050010030010704007601c203400407001030b1070103800d052001d529070305948940d21500700c00c41001500820200001c2c4800180f49030054115405807014a48603107841c0700221084100300c03003264a640440070801004030480710364500c4000c01c11036268 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 497582014 1250 497580764 497580779
    0x4080a02092a071115030a020d021201060201020309060601020c1c110d0f030f0c0f11011403090c0a0b03010605070b090304030f0b15041416110601030303060305070806010b0a08060316 81
    0x30000c1100360755001101c0c1a410b000c0c10140040e4009100c05d000c03060440c0c0c0e440c0c001c17801a6001411036041343e5020b110313a1002071740101074140a40341035000543c992902c510082d2030101c001f0417441c110342c0310610071402d90f105c141c450f0300f140d000c0c0d400c541e4000c1c049007840103420903482c91054000c4060411401480780a00d44001d14610917580c030034280030320f00c9c411601107039144005045a0603201a2100140900f501008131050606203200d03899420260300c600380d00203c4d6540096003241482d4440f81c5445010480a0118080e25030305650402c00000c0040c003501c0710040c4414200c1001c0b07030142c0400c2054400946e0710000c0c00400e400740b0f00e4004082d800a0350442600186480602058a014000e154205007414031400481d40e5440031103914061440441c1e081c441c4124001c0c0032208244943c43c080e600030b4801103045131031858002d2608107140c4c0482483c0c0c000310018032103e0350000485003d2034035803901404545a0320002414803140300060150036624900015064 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 497583264 1250 497582014 497582017
    0x161a010e0a0506060316180e010f06050f090405090a050a0312050a0b100e0a030206070503030f160c020f0a05120d0905010c02060405040504061d06160504080a02092a 73
    0x21094609503854545455075071100b91031003540c1c00350b40b05100303200040e41c650f400e410a940501a52811642c29880b120310311501010b950456107019400c1c030010300072100d400c02000000c1c800da02d8128a04880c0900384203a0b4000e1003076040c8169140c8003c1030344035004100083c02c69410500340c0c1c10b15115850041c140245c5003c0100c3d80c07034181000510001900d11a109901e9400390480c0014191903004442520041e80740b1a0300c1034500c1d20100250315000c001e403c40e5885a4019503503030408401004142000034144060801e81440b090036035640040080002581a2031101000c012030000600c1c1c0e403103e41065030000c0d07400401500283c000514a450f1003901d07112840082e0b160001101d200c03a1820010b500080d0410080250f82001d9000720340c0a8014000019140d011800700c0d02d42d0f800d9140004199882103081c419909400010703e8480d010b81d00304130b07180c01e00c4c0515894550b4240c04003c2d204020320000142601c100403032909034422000b18a0300c0d0480c160103030b0001ca = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 497584514 1250 497583264 497583269
    0x11040b150a02060a060305100f111305030f0c18060409080d0b0103111e03090a0f120f05040f03030f120c02010c120203010e1b13062001140705161a01 66
    0x140f1626001c00c09881191180341e0031b03281c001000c0d1941509613401c00c000742040e058002881540c5010030390018207000701500c03841500026205c0d28030b04d40010107282101280c0c2070003131a00110504c01c03003951100105202c8a280d820040080c2d0f0710034000400400361000c2c040c105280008005005072010750003c1440306098070100314646105044c031b02c060060142c203450340f840444203441c030284800f01035588400e5640407030303c1204007952008d0891100302c0c0c040b21044070148454040c01e4016a00c5190302c40140f510b641050303d42007444a02004a202c090103000d90104420400340c814a0701c82c88190071144140030318005414001d0081460064040000e171a410800d076010720a4000c80307048580008a50b13605850b80042c4281e07601428080d400b103444100000d004501c12902d0107001004181c50f603803603500d482c20300b00d4a58195941c1c65450ac0c4d00d080c4613074491103186400c1940020484c40e000c3e8861030b00415800140c2980d1901030a8030031140503c0340c000c034114540505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 497585764 1250 497584514 497584517
    0x40b0301050301051e1f050a0b040f09050405030a140d05011e0905040f02090601050d050411040b0d0f031209050f010e0f1903080c070b0f0601110d020a11040b150a 72
    0x260383ea44081c003144240c9074804081c03904440b01c04100c40c0b50440c10400b40346e040303010003028041d80d81c20000e52200301980c08852010300c042820044030380d45c03041d020300424507103c003880b0500c0c145da00d1a84038454042d9006c1031000c81c100c0c0308030700c030b01180a0301d02c8005e01d0701c2c0410141d41c5030340403402500041d040c1d220100072004004516420035002d250300843d40710888200b00d81c2d071b607400c220070084001d14060402c941803200c03000910590081078002c901800f11032911203026020b03c000da8540f4458503005543c00f50240d40094242009203030280d4040c42c1c86140007601c501c4040240158800241c00c61040c48003001421506602500003000355404559030002102c3c0e0f6a51074006100005e1401020400d904012a0041092030350150100d00c0c020303d0000a0354502400400980c0d4910b102c28550007080f42c25600b000000c00030f8076560004100c64100084001d40c0c0b101c0324500100380710500d90013014903841b030317800c69400e509006140f10281007094407135809a030060b510540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 497587014 1250 497585764 497585771
    0xf0c0f1303050705150f030a0e1209090112020915030c040e011e05060604030f051e0c09100b0a11010e01050c0a18030c03020d110a080307020a0f0e180a0602040b0301050301 76
    0x140c28030b400082950540905503510782095418886e68200340c00040166a505442e02041100007409000754440c8180e030903a000d0b29401c5030003c0c07212258050304001800e01d6a507910001507035542c00401e80c031540401c2440d144226150100382412002c0381856042818150701404403101074004006240140c500190300c26000382c9140c0a4031000d4801d140c00845c200800c4c004030300c040d0b000014541c000c2c0c08640c2035050301104000d03d20311450034540190060051050b0381d1030324240d9150131a1341c400e07420000701c0c00c1907401c0500303118028001003801108507040a00712400c0d0841411005008003c00882c50055103d10703d5078452a0140002071140d07803d9400c0d01d500034560000d5070f81240140c0f08441c00c5070700f80304017508859401e460030102882c51503c6940c441540c1409042008003450b01c41d10301d40b0500001440035040803070140b08441061004200e00c44003164415650b10b000002354602c03030f00c080d08000e41d051010742031500008001c40c1c800d08040c0154104d1300150000c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 497588264 1250 497587014 497587019
    0xf0718051b0405060313020612190c0e040b0109050303030a020426060a020a120608031b062401050c07060801030312090506060906060c01181a09060f0c0f13030507 72
    0x1100364600381d001119400d40140410310482c1491406150b0203032000180201d0041182c0010b101c503004005042c200f4584c0c0f000300203405070045204401030051711814003000c542c5036030140c802840003200c036008035551150110103a1150076240010030025055170350f039003000e0080708083d51041c01044055410403070b4054440b402060800ca00a1051010348130f55154064210040c1d03020b284103030100700107400f020301c48408910440b4000c050800003103544820050507202c074902502031400e06a0425020064107500c01d030300450141c62040541c8840712541001a03407140941a1050040d11030300c50003090780d68000001c02e0680e8065201c404c0422503281800b000e032802540014031a0300030b43d0214142d41850345585800400c014503290500d0600d602e01801c4507900b070030904d41c08484003400414040090001e00400804611200c1280ba000640a60700c040280c10a00201065400652203d000900b60303009040d00c0c1916660340c170618101100409030b103000658640c003442100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 497589514 1250 497588264 497588281
    0x80d020a030c090e07050f0417060402090c07020f091b0301030c0618030519020303220e0c04061d060d09080304060c022a0406030b0c0c0705090121050f071805 70
    0x2003d0440e425400800c0c00e542d43e04d602250303075810000307041080c0a401c0c0700129a00907400310150300501a00000c00c8030b8586801088044d20010301164451241003050201580f03c6090302040040155041034050b02c454000c8584040200e40d0b485c1d00c1400400040200b010b1564902c0880c0e503590703510300700e404c08071030200343d070210500c0000d12650224901e00c44848081a003200142c1c001000c4c1c9040c40004035075014030080300e050031001f07001d41d0b09040c01301013041c40711030760461041031840c0c6c2060b086c40740107001508003508805d000101c25a403c440340d6100c01c2140d205610100c2e09005e6410b0901d05240c0c640c0083d41c0031201f00c0c0c1011400310000344001044104240002c80d0003c1e102c14410742c010710704022700c40207500f045d00d800001c0007040351159a603016001203150240d5a020701c40310b0600704180c2e60405480707412010010000c900c2691200b0b81a000032203040008844c062618a02e00004094690400d000e003070000103403150388007015440b81c40114011301060b9145400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 497590764 1250 497589514 497589527
    0x412020f010b060d180803090c1e01020307021c0f0c03021804051b010c120c1a15060f1c020d0c0207031e260901030e060402090c03070309080d020a030c 67
    0x490340e0002c0d018408400004a290404020b80b480e0b105c40202c080ea41e038461b0113456004a03a02c40705a4442c2d1030702a410704000d200101c440e00c0c3c00c1481002d00c281000000c2d16031040407000717442240e003031810302055080b45101c422015440b080d4075001c44030354030b04070300081c80c5480140d00c1000c400900c030341248460b000c91403180d54001c02400c2408070511880f052000c0c10f2500b1b41c100710250f134041c8006401c030100c0c01e901100d01e88440054140c075240140d20b80ca51095012801c00b460f03014041c8400007905042c0c41c00804031038198071614000b42d10045070140001d0070500401e003070740c21000700720954020540f84032142c505200c00700300c2400a81c2e5881345e5200c010200c0c1d001191009418010101c1c1c1d0440700d1088811701c40192003c000500d00d10003014440d0441ca1000401041541c0c140c854803418080c02e002802c9145010b800180e40228010407100880f030700000040d04441c07203a0700120300c01c1d510000380390b141c0c00d1444074040250804030104c00482d01d480a50400d10f0300810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 497592014 1250 497590764 497590781
    0x5010909150905150d0c140607080a05030613021215100219030513060e041a090a0c121802030105090109020d11011b050105040b0703060b1611090412020f01 69
    0x58410000340740101200040c60001c0084410084501d07803101e130b56980c440c0c580d240758010000d0100c2d06040082c002c184003221481030b40314220800019000423462416070300c041100c1e04080f07850343e40302c0c030201e02c2d591f60109440307031018400a0442c4500a801898070300904072071203003004014401d8207209507441c0c0802003801507030042845100a41e07041c05000e01c0745211385001d5003040003038140201543d06e2500030602192803c544c4050782e052500c203c00308001c040c103088020226200c007285000d10040e203c60455500c454824181c18040d50380c070308030034180c030340304000e9880b020452484507555480100e201e5420030011600010050265076005a0010005007402c1034961314000740242584610341800100105691128003907034010101901440020429280c549450101420000c00c00030905203409400d0090941120654001c040c2414440c1400c10316801d211048a580d8040b9940c452054410042001810142c0c45101c604e0781e000c0719005240c0d44c030172600703940120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 497593264 1250 497592014 497592041
    0xd0602030906092118041517010c170403020708030c030706060b040e06010c060e060c0306010e0415120c0b1308120a0c020d2303040819020a031211010c0905010909 72
    0x4130f100300e0703280b01d1520003030008502507142007095030915000305007a11007001f44034584284040b005c001c509826240d140c8001d410300000c1020340c1c00c0c090098604140d11280a0362039085030005010140200044406801040110f0f80c41e941c000605a42d00c1c0d01c40309007224058202500000d502038008165030640303040c4c8440400c113641e0440116454400081e080d45c2880d254100c99041640502c00305000d9507003818000d80da46040b80014100403428003000b0301a6107028202929041c4682181d019210a13415a07460424141060f503030220160b0082c011000000070344d0850b02d01503210410440e904402520030344018030003c0340c024043c035076003280401d07114148a001450003840e545415032050100010130241260701c00c0e8000384101080405900019041c800c3e080c0800141e590b4041070f80490fa01c2c10040d90120380d504a00788070007001115681c808101040c01520701e04030b0910004000c1240e8211480000e042640f240300b02030201c0c0c40d040020807a030f00c1a000d16211644034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 497594514 1250 497593264 497593303
    0x210e0909030f0c070e010603090b06061908060f0405090c0103051f061b0b0708090f011a060a021e01150f06020d18050414090d110d1d0d060203090609 66
    0x41c0c035880c2c110707503004608680c65401000008161a400702c01064043c0c20b00340d400284400841c81c0024615801601403842240c09110260704003880c5c12035040d0103202490541c00a0f11500049080800300d003036065440340c1030404001d0600400540c9030b00301d0200745da041c081625130700782c036888040841e50b103100c1071441542d041c0215401031000c0381e200314080050104001c0c0c96203420360601429900780300001c00020500200050401c280102e900e04a0020000c80507280300c143c40035802c3c9000c0c140540c1000c24600c126900a10528103102c4402c030b0082078402c14a42450b000340000344072002007201c0c0c1440843c0140502c0c20388403c0d51490303001801001c011207016540c01e842c194059510281605c00854551540d004490420100b091030000e14100303103888504245000030950104202c2400fa031380140c60002d5196412101c41c2011040c840842c101060075040ba01c104139048410300401d07004101e03036035000714400e9806200f13031650b68a070b040b809915550600c0340707021031146 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 497595764 1250 497594514 497594527
    0x7110907050301230d060203090109020a09060609090e030f070308070305010801050402060405041a1c03021002090f0603041401090b0603061e010b250609033e0a210e090903 76
    0x5880d131021360115002810448039116681c0c03414282d900450320422280d44900d230010031810f10700c3c4030201078190402d0038801c03207081110007046003030140f0802d540543c41d907204c0c0001410038004c461940d214403045540e01d800d18140580040025580071000a140100024100c0010322829020f9030b401072020749007070310f0502000702405000704244146a4103142c0c02240750f68440c444800f100c03010042e200980c05504019040c0840103036104200c43c0100b042c09a95a07644100605004086402c6500d03500c80e8100b40c07056940a00803180c281d842c1020f00d4003480488032803544200d0040741141c100d5901c0e1716a410101070b442c040c00368050700410061086000713103009000065036481940c640d0b000b005a1410003112580c03c00d58655645104840c20705510a0482440c1c2b100f0035000720390b00e02101c00c440910340d00000c03911003900405d0040610310708207020f0441040d40001d0724925040c00028039400d001d1b8010f11580204013090410390751820540d842030300c21001c04018604069 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 497597014 1250 497595764 497595809
    0xe100207171b0f0111010606020d03060e09030717040305250b09100f020a020d290405100b04021b150106020a020901170a0c0b0307140414012307110907050301 70
    0x14203c0c0b0b03860500900c00f204203612942441650001c00c0c075980203103d10107580c0d02c0542217a40e50b400140e00c000304a002c002d10440f00004450b0025440308103050f208410041501440c003c0780c2005043e402804d40c9501b101d525801c080260551040808064540d01c3ea001040c170701c20f40c0045034100941483c41c0359000d015804003516044c01d030040e201490507940c0000c45842161604503010b1204104104502074a4054a5450344c03000507056510b04041c0c03110759a40108407401003589490760354010158960382c056540fa407041c00703211030366403403c3c1d0700041e240c01020030f410000c04240000054082d20018052964580242c00c03420a6400c06e40b0f2400c040c0c800600c081d149211346c4604100160009800c00c00030000e1108458603070a107582c0c000c0c201c2607600100210a4401e203c18042d121180701640c2010900f406c1c4103000d20b00c00c0f6000f84146481103015041e40f080071070094184921000c0e100d00c0d9030b004840505a07640c07102410b50b0180028012540c1c05806900408441ca = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 497598264 1250 497597014 497597029
    0x501060506160303110906040306090605070903081233042d05060a1e0f060c0b070e0d200f120a2004020d1b110309060a0e100207171b 59
    0x101700c14005a1400ea80740d800300e115a44550700455255a490404009020051044170380101191410094062951315580c40c203008001c0c402c0d400c00780315000304d503010b580080710902c140b80311030341c000c7c1e260710b95140c5451480f0700c001c41500603800d2410700b200f40301005c4520b1070020061003501c00140782d5030340420b0003454003c0160350401c2111001003946404d20700c0c40304403ca91100e80041003420150308408031003581c6d100b03031b040c85064020301001500220310294056920b25052071440032040010780c0001400c00003808414041e514039054034030618162944001c00c1d941d16005040d1003041c40540004103000c01d842c3d401140f0300000040900c04000c4c0150740b075101c4401040c6006000800303e0f803000d05112151039070380c3c80d6007000303c40c00e07030040d1b00502d001d0070188290381003011165202d103d08000c440c40f440c40010b00c0e032511401740071100e444040113880b55040da0a054806580c910345402000352014440e100f008410300000b69011410315264201b00000d00d880080c03144a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 497599514 1250 497598264 497598281
    0x6070c0302072d140d02010e1c05030c1e030714072102010801080d081f03050601031101020715050403030503040204020d052e060813060e0709090501060506160303 72
    0x450042c01400240f01c10041c03030000b0540310781401480c000f0f02128003e14403550641c490142e011407040030303031103545da40b0229190807078081c2040d03000070b41510005100b0003030152199070351041d0071042c03005119000029290030501141150344070110392210501080354828140440d0b0300411078100010a03400a0185543d900000c0b505003580f02c0c01000f00c4240075030000a46094000710b998150341c1d00200140c010003680028000c6400c1003a402408040008d1036841d0210b8010100e240031070040000400443c2c005003603503020b5842c0d29002c00d50f4960385107841c4c01803103017080114010075568059198268982c0b170f5a0700c0e183c519a03003903489800040050b40e1142e400c0c048642c100001c0d015041c0b02c0c45c5440d510429010240302003241c2c0e50302500c002007600603203440c00d0227070540040741c654000680a0061900d00d4191a081e00909020021003602d030085520000c0e951116802100810348107900a1181d41d032200d0601500380120b074854640c1c0e0320559034040102c3d0181e4001442e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 497600764 1250 497599514 497599517
    0xf1c1e020a030f140d020f07060f0512090f0d0201020702090f0c04030b0c0d020c030c010c050414060d020c0708060115230a0e090115030b0402040e181606090602100b0306070c03 78
    0x4c112048414150a003140c10a103500076030040f01c440407007107400744401c0700a40101c4c1400100b00b004110014164010044101c50704260312000c10300e05c8204000c2030440d80c0701c0300e0807076200b0442004020f02139000340800324080c503c0c07500030500b006030704460948600321804c6910304051454455805108000d40b000c00412420004800c180d8100d00040010b14400e000443c1c3d12039101e41c1e100e00311010851000e0411030140000d00049482c402c400303002c030354221281501c40c00c5400d2030303000078450861070110710711030030800058001700841d80314100c4000100301251880c90300c00c160360344007180148a8240b00c4102c1c0001c0415405405054290501c5c078142580449207004108003100030b030415103040d0300c20300311801815410300510035502c400f030340d00390300b030a11b050340341038200d04090000e9281c4c800030a40591011820003c04500c03c0c828002c030002141e03200006800600f0501905005014a00301c200d9031030510f00a0160741503015000f408240d03170b24901190b41aa0303e00d8100c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 497602014 1250 497600764 497600783
    0x20114102c04121701090204080f0a0c060e0301060b04080f10110a270f140117010b250605180313030209090102120124021612020f1c1e020a030f 64
    0x4a0560420071139902034200a080103a80d01d0614101a1600080602c0c091080d07126440200002d114004490121030042c2041c2c040d001e00c0c000000c0c0074055503000110b20007004070f40010300040c002182c050449045040da9000e81d080040c00c010707250ba40c7c0d0401a006401c2003441800d82c4a01c4041441c540d0254843c011801000d02c14109450303d9880000200890401800a031001c041030184040017403d00080f5940a5410441c01c2c2c0380511426907482c001080a07800700c030812225032098604074502101c500c244c0e00c0c01d04024401500c0d00316400104024400c1c80680000490b06400d0f49106801c00e042e280d542000120b2000402c9205555003d10417142040842101d050107400a00610602d024044000c0d000112840c8c07448021540400301502454640c642210203484100c0035115994155001003a084580802529001301301e41d0351030200b8800c114500e1056038840e0003800c1407101e0610b6810004214100085d5100055a00800004041d19041c0300d13040e01ca00e842c00b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 497603264 1250 497602014 497602037
    0x5091b0603070804231603030315241b0501020c0c040908030a0b061c0b0f03060106050307050a021504350a110106050d0317010b131203020114102c0412 67
    0xa4205000c44c030035000c546c03822071000d104164050041004020f2040c03c180e404600e09880c10f1a030202083c02450600000088404560f218008502d80302d281ca20222181ca4801d03d01741d0300039401205800d8550103158002222032500b4050181081d40000c9001e055864010092009088904486511610402503014400d4614010442600b0040800250741c0001c106200c01c2c842c40442c5244660440d0005102aa810605a94106015181c22a00c82030b454109914140003800c0340742e0141c040340c04200806c140d0320a80d02809070310101c2410404000301c1070010106030710b8400301d180700040c001024040e00c40e203140c14a0440d91000825202e5454021a42005508000b5000104440d0034840115810303055140100055144d851815400004098a034560b60207032440c1441c00d20101e42c20b1501c05d40000310321100c00d80300032070706040140c040c0e13812503414413482d010003149904419545405030031000381d44901c02d40243c216540c0399204844020411040810b02015070003d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 497604514 1250 497603264 497603333
    0x1005070f030e21070b010e0c03041b091508100605030304050d030309060f020306010f020f070302150d0c1101150f0603051801050f25120c110105091b0603070804 71
    0x120400003100d030f40040d541d41c403604180b0911481604071040103500300042c071200d00301c030360104c90707001d0740010411600b03d8104140e4580d58900d41d010420b641e040c081c207441c040d11410914412500c8035000c81d800310383c11810081c01e844a0303204180c2e054009200412840c00d0040000c1e40d0036220f846d000407490100c2d6182c4084038502c951100ca2150301004009281d60041140d00302c0c072840b40000c000d00042d0f040d109541c1c00041c00000e0040d0240080801030100c000c09446000d100100300b484810148803009000d8500c0c0328401e55950300705202c0d036000140303102c2000305480b90748407000d04a60a040341a4058000945440c0b240956800700018141080c801c85010f40c0d802004180c40c1d0800014905099a0701612080a64540580c03005420340241e02011035103115003000c1590801020709988008202150410035402c020400c0490000031840f40401e4001e10690250a01070000f0300c1600d0000f114079001140c13124002c034000c5100d00e01120910302600b0a81134041c15210703003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 497605764 1250 497604514 497604553
    0x9210c0c04181a040b0604020717070f151505090c0408030a020a0b0f0c070b1f12050d0905030607030b0a0f120c06020c06070209060d14030c1005070f030e 68
    0x218502d9016041000c0003c02c0703c0f803000940d90660041e03050400d420141c80c1c0d03802c0110041d00c0d0034481d0f94009070140070055030381210803012a0240c0d000f9101c1e60182405075410140c03400031a01c1410a4010f403d0a81161003110355951003071401e0000309081c4070a0080c80311020300300c010b0119084c480010780050800c02420000349030b5000d031810008618140d400900d01400c82c02d101d14450307040201c0c0402000030707508034941168100760242c503005d460008252450b00d520b080042511404200d8500c000c0000700a68843c42c2203511554481c4400c444d03441c01e6010722a40740d0041c8020172000361198208068410000b80005081917030b98010140c9014554468141401801180b1051241d10000c95000300310f02e0000d04081c1d0308400c0040c4451080920080c0300c0d11565000c102c030f036110016a540a65030115043d440c6404640b2801c0c2e880d0881025039010340300d00e03120101040c00e03600860f4000d0b101354494031302c044840309054001d841c80840700c0c0320622920100ca80304410700c1c0c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 497607014 1250 497605764 497605781
    0x504020a050a0320010e0f06180a0b0a1701030f12030e0d03050402010e01090e01050111010b0604080c0325062703060605010f030b0922050a0c06030509210c0c04 71
    0x500c003c000740c4004d403c008102160300381c2c0d02e0500c00305030484880d50f2158440403150b40c000301e900c2c5580e407400008441610003c0d1103007503002401c070000418103029010081040910b0390b00c0e1044404c80c484440f0041c0c000c24040203000b401c0300d4001d440012210f40d0020845041d900b00400e102c0c034108641071a02a6110304200080e440e1010b00095580000f4803101d80d03c2c1c203180064102d401c280c1811804101845000c1c10070002501b0420680d600794000310548100070107540c2e580396100416995504c501c099588207016034a00903449160101c1d60441d40c084c070300500e01004e4602442651003010809011802c48148260100030b49031202c0f10303001451080780e000912030700f03001c001410214040c1000041c90715014a017645951601886944201e8280f0701d0340030a0f9a9100c0c1d850b510036018801046032098078440707020001081c1c00380003a100103035800c00251b640c00702599a1465840d10203080d1110400490350800300a2000b005540000d4088031140098200418100d80c0c010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 497608264 1250 497607014 497607023
    0x110c1c2610090515060d0b03010207200d030905100909052701020c1c140d05090c04020928050a09150902030402130c090b070b0403020d051602040504020a050a03 71
    0x40c20059030000401c031031000b406001d00c0411051400319144100200d0030908180300b0500400e456917403e1a80c4c100070107901e000780003592103511030719100e01c0708401d22203460111800004903007603a040c58600140816015600d50001704d150800740010960303050960b404000d00701ca4041503241e00b0b401058052400012809001c0154504261000c0018a61200c2903401000403446150b400206100600c400c0340058410400b00c100c1580c0300364103d403076100111004142202c00c07542d00d038055842031540809584801800c0010030040340705d20700034244c1c42040000540c2007010001c403507401c00c4242040401a558417071000402c242d049620001082d5101ca007203540844240a22000820301d4400550450507d58005040710384464180203800780d6410040320300501c01c030700d41c0d0000d1040c282c40c00d035540080c0c10b082d150401d08450907405846200c10030322f01d15120381700704d403428000001e003069140c2d51942040b01401000e401683e012101040128003556520391800046100e13 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 497609514 1250 497608264 497608337
    0x4020415020105220201050306030f070b0c01060f0609032003010216050c040903080f04110a09061e060e0d1a07030209150c06040809130c0f0201110c1c 67
    0x90301002800d4480c020b0040d060300c1001c2c00140b9605024541c804222036090030415100c0d52100013203803804035980c4c2160b003503110b0140700003040e000f084000d02c0145a050003c0c440c0989603044030301181810f02c140c40004180b0807080000c10301c0909208404401207611090348400940005d082ea003090000946030a10f07601c8940c10050200540303444188103940034800b42000d900c001e865948018410740e108402c120014040141c2c10710f02e440d81400080040c041c03035480e0f0250300000c000038011035550403840002014542408101c42045410f00c0d40d0700505004901b0900010266002023190140e0740280110840c1a60118242c418a095640140c03100b2140d42041100c100d00e03080c61240f0b2000300007544200300301003030940e8003e4101210b01e6844c0c1c00d490105440d003500310810b4500500d8985654425548a0b6040103501e845500a00c50660b001c1d042d01018402c40074840450341c8030780d42041d19000d0b86d0122080484103402e0400411502030b0b14180480e8040290b134420400d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 497610764 1250 497609514 497609549
    0xe04090b07120908031302031501031b06020c0d020f040230011502060a0c110a1b0f050307030209040305040b071a0109020309030a032a030506090105040905030d020315040204 77
    0x24407181c4505400202030b0144240d6640303445031207240c80068090240c01e6004c00300c45c800d5442c01c20180541e88200180c0c1c3c079680d81e60b07040240c0e2031030b1881d0207143c00e18401e0800154a070310001700802e0b10800142580d8820100c2da007000240c0b0082400756030041e800f4000c3c0840308110000283c01e10440b13050009178490121101d15400030305070000429010549081440c0a40c002100340e80412003050000e80d030400c0c1c0d0000d440e046202c2aa10003988036040341076007000400030715040700705044140b90752121f450704405000c0c80b2540c014031350181d100d0304040000d0310708001c0d9550468080e041141c501516040c400510358410281628400134100c2800d400b0601c0340e0b110b44c014071442c2c10860450400000e00341c0c592207103403414010162540c98507506100b410640103608008119207482803901400d002e0003400c0100d401074401d80400000142c0f908050207002c44140d40300000d503181842550b2264004e41018281c1d80c955100c142200c0c0d119240c42c40140702a10704100305014049 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 497612014 1250 497610764 497610767
    0x60608090705030a03020a1118070c0302060f0105150f09030d021605040515041e020a02010b0102010e030901020d05032d060301050709050307090f0f02030a270b0a0c0e04090b07 78
    0x403601e42c4194000d501541c0000c012a9010501c0b8600766400b00815012031280c20002c1c1144281c1480690440321000500130200d4000c0401c0305024829020307111240d0740d40030403445000e0244101030300319a110850100c0c0c201c41400910300809501f4019003809400400b2901d85400c0c9990744c0b0260340020301450f1a1002d42943d10006e2400310b0307041c8441d261100d08914140b800b1038420780034a4030b400201c0c06070381909048120f074a201e502d0464982c01c02d840000e000c0e161030001346000d5440c0c4502c190003100044115402c00f6410713002002850012201161b29500050062a850b6200c0000d0301a84103140c20010121000302441a50303030510000701400c4440c050080d1040c004424010010740d140400c0701d00844402c1709002030541c40348403a0b140900460070034580c2c09407000082020b1104264070080d00c1440418103444108012000d00e0307034040000101918055011b000528010925004440316503150f1912080310078003c004102620b6091408030b4140740c400c4100a60f15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 497613264 1250 497612014 497612023
    0xe1204140409140c1203340f0b16091202010f090b0a030c0305010e1e07020a0218011d0f2202040c0305010612090305043005030301060e120613021306060809 69
    0x80802c01c051840c1154002c1c0c1d484800c41c00713a030056001c4c07001c4601004203145e40d1f41e4609070160800c0304451180340c03924040d001c03620102d4071580000300c1071146240241c4100103550a44030400c03800c8031110615001940c224800041100401c01c0301d80001c07600000e6003010307050681a548000c00c50300a40301000d010781e94143c007c64414181c903420440c42d2560f41580101042404d440d0409640710188120708200720104041e402200395030b00c020040e607404c003540341203884401c014031080800c10040307200001d080e1120400050440040340350420103000c0e40c03d0903010010218080c0640b40c0c085419141c41220040109588038010040e1075004815030f11800c549980c00c0003e8681590702400a0165024184044818142c0750500c003900700824540c801000e03400c02094212441d00c0d80da00d0b40b09004220010381c606281e0074080c100340421080000324070f00509050fa441c040b00700c120a82c0342c1401d13603004d195407a104411410310301c034180243c4241c0c0d80d190324526000100c1c030300c0d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 497614514 1250 497613264 497613289
    0x705070909020102071d06091504111b0703210203070f11040b091306110714100b010302040e04030e01030915060302191406030405030403080d02040302040e1204140409140c 76
    0x114000e06c4074030504010b41000d55400042201d009180d625500d00345001010030200c155003180ca0243c06101940034003000d050080030b28006842180320008103152608414070000340a103440c1d8101429403c1299400e641981e0349104403803d24001d40c890150f003803882c1c1802e50320b507034001c4508000d0b8280f0b07005a5000304819030300001e150134200b05130450441400740140405a0340e00f0007244d51754503001103a11103034104941c82c50003114142e13a60b89800343e22410750303030043c03801446140650090080e00c08451030b0001c0c1518a035a55141512a90441c0022904165443c02074100181700c06003074040741c03441900001802800c500c10b00c03114010a07002800074003015141080403444401c14040360105c2a50819203d07202c45c50b1092440c0203a410041007a8000315440d4138118075a4094000c0342c3c02102c0a00140c16131070036550300c0300800d80441107500d00c100800e1044000301b1007a868281c401030310000d44c05409480350520203108102c4840e40b80c100541c0391440d40303000b481c1e0f10030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 497615764 1250 497614514 497614529
    0xf02151801090e130f020a0f230a0501050a02032a15040203071e0b04060201050a1107030804060b060702030111042408010509060112050a05041202030f04120206070507090902010207 80
    0x2510342401900c0c200f000004044000a60404285808000b00ba807101c03106594054002c3c0075003616001c01030121022402881841102c0110900402e0100d00b954139040b8070203011b4106c41401c2000458190f40004a00c0007540b10410000a0040c0b41d00354603d80d440d080443c4030820700318140300608050007460f226100c0d9910100780005a500400c807003044a0f4088107880183c0d040004541d0303c522194440b030b1640e03038040341c0090381030340641000c0c2c41580343c064108510a440c0307000b010f090091010150005404800103000100c0c240d11540a000004200c0703418080c2a0380040c0c00c0d10100c8045902c035a0012408000d02000b84514000c8200c0003001e000200f040910000d24425051040900c02d00000010910690046420519104000d2810300c031301c2c1ba0005000c0c015240944c4e048a020b654840305a0541c0d2000c01943c40000b19062003600d014609500c41540b00b03172401c0c003a41d0061040014800080d000c203c032100924240c0000314810f403581c00007904041c0380342d01048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 497617014 1250 497615764 497615777
    0x70305100b0117060315090703062d050603030f0a030219030509120319090b1005010f0e01030b1801031a0c070c090216050f0304090e0312040f0f02151801 68
    0x1281e41e07049a0100410303120040200855520380d400246081c0c5842031400c1c00d6501c0c001407191003070380843c41800f920b000c2d090501407c2d03141d0f94101041e04180b030000f0142071105045041855568000c1c1f6049000101201e051201c3c030070a100c41a40201c9c10040070030707400030740502c2031007005060ba004140345080401c07141c40d1a01e01d0702c1d2102e500038042e00f85810004005003000c42444003070a403101040008010018241c0381412441d1002c2c2d0700400b10790000c88001441c4c3d803044041818504641d034900381c4011004c001580a803078200e1070960b018103c00456120000705a103d0b0f80210300850340003454140700c1c070107240b0b10300300501050320311001000b082000c10740144421003120403032034006038cc2d55400c0303c00f411041075100c0020414092100c921105060006c00380050713401300c0c3c400308005d0518401c0d0959034411000400c01e20840c210004000c074000020381001140a420740c1000c4852030b81c000781e0980600c00754481507500120b55070005801d280c405078001442800c011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 497618264 1250 497617014 497617031
    0xe01061509051c0602030a020904180309120c1a120a1b0518030f060115080105150a0207030b0903030103170a0e13090204112113030f050f0c07030510 66
    0x4265803164080d50f80240315054090fa4145041c54408100f640c00010031500c03802d2100d90140030f54450f040e0030380f146051003400510740050311a081d058503490f07150a51810310305800102400e19080341903070315144005000880c20003144603ca040d08819a000b035441c0001e4105000301c090180041c80d900e460030007504070b10395913250038203240007407400c016440e0345125204060041c03c05403a40d405000b00c0e41d8642240000060403410396884521031701100c00c950300210364400d0244a0240d121005e880c103030340120781840042850a2a500c141c90faa01c0d2252100010b01d9410349503e9070b2a80000010070a11004005074403032754020803040d85c80c02481440040c0003007190904184200203480c070000301411180d00100e40d4607400f400074480c80c014035a0061554003e90403900d0780000000d01484034003010801d4900c03a040030600c03000d070701c034141d101199207007120f14450f03042c800100102006c42d19801d02801001c0c041d04020308401c1e0a41c80c290b030606840c4030940741910304080c01e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 497619514 1250 497618264 497618267
    0x191e1b03110301063009050601032a03021c231c0509041e230603070303050d0903170c0304060606030209010509130f060308130602030f16140706030e010615 69
    0x1180005424a41e01080c801c0c01080c541c130712017450b4200c108a40d10708111441008001b1501174100c4c1d005038040d08040c0b83d40258114141d0058660820f10005480140014540001003034030104d1080e0b00320280045603038401c0e40100088144450100e0000c0d2204d5404004020900f00880450080d05218014480280003405104090782c03040351160032191410b5903040340b801209150950a000c0110012924203035950079008064014582c28001420750800240d044203ea80c0345d038a551424460080c410010603924204030100030090301803900b003100e42c1b02494061242d0103501666803c0030301e40700040352038980c08031003407500603c4809a00e03a00320b0295512140c080ea0100102030745624060003c000c01700e8064030b010316004010003401840e00c094140f041d00d01c00c0c0507414545400301680d40f40140e28074885200820401c14503401c1c00040c2002407548141c42c3d081d8200b0710440d0090134604503401440000e5070750001c042c1c500b242405000c000384594074043c250030609820 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 497620764 1250 497619514 497619527
    0x11206090e161a09040b0d082b02040f150e061801020d0c020913080708040b03010810060506072003010e0d030b0f090417120112110306191e1b0311030106 68
    0x1212881242da46d00310005940318040b686e100e460744210481d94030200380da2840040040301c010780c5000d0000b0b5000303055143c0f5074803c860a4940d1161403240700783c90315445001540140c41e040c0c00b002810303171000c1030030380311007001e0481c10340c80c40c080301d0b100c4d8903d1000918006034840b4000c09c200c11407210328096102d40b01c0064000c01c4030b01804503d0180c500305040c85108114004150410020300061141050340240d8141c0b4460700c144d1728610070111125080d60200c3c02150350103c0100002d500103142581c598000c564140c021600c102d10b41400a800c480324141042156040074034000009645403090203d03034041258080201d94070a400b207800008000c2004010b000061203e440300c000d000c00fa184c500c65202c08000d581c0d03840e8041805110340c400c5086640310746204800c8001e00d8041109171140084000075144000f011503100080d01c0c4248810307070340b10003544a10351042da0074001c1c181c1010300d401b00003101071000c00380141250118681d14808850a01c010f11030582d0041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 497622014 1250 497620764 497620777
    0x105100516030503090109020a080a03020d02060f1927140106080c0603041a0403090306050f072c0303070f1707051e16060f0f0503060f011206090e161a 67
    0x9420f644950f11004030f140103000e44100a036110442180024841034000f503480d2140344654252074220041c0c24003680d07586400c0c2d0f030007020b5201040000740c140300c07510542003c0300d030720303034000b044040000058098134451102c800580d48000c8207080144640107074200300541c80c0c400200b0a81c1c0c80d00410300d44480321040303110310176500007003c5028455071410b407803448580300e10b000f070150502c2c0c40c016083d440c1611045680c0e50610000580314405070514910454142e140c01022440d0060422240e080e00c90100060740350700d284a00c0d1540b010009410554421074084101c14001d080c900c0104100d1641c4240750381c010000728001810104501c0400816210703101080c00c0c0c44d071589401c002e8480350005168450140000b400703a4030003110712340015542c41d01c0c0880205440d00b00c13140d11084800b540c1080714928690328035485407a51500d101100100000c60b5611100c6110a03120020004220f5500c984840085040c074001514028000070601e01070007000107a102406020b0034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 497623264 1250 497622014 497622017
    0x8091b13020c070e0403020d020102130302310b01120207022206050409060b09060409081e0f04060203271c11030d0323010302090a20070605010510051603 68
    0x90140c0060060301070b200c0d11120710068607686900d51181c108412021901900188203803d00c80454074018401c0350f000c3c21241c40107154150564083c8035019180c40b100b00d0f5190780c1c520380c0c5c03106054032840d810242c000c034000108034022664001007444400001d103078000d074410000140165500c0440521010700071007503002c8001d0007883d0f54002d040070f80c0155040340c01c154040e0200b1a166010b5000810210754019803915003009100841304500310080400e14100b080c94003545120801c0ca2008583c45504c9180410f0109060100d400542c41358000d40d001240d51440e90f0705c0c00c0030445038030380210a42e00c0142682c10025160718090409660f20500c40c00c00f450074410694418048240080d003140c2102d07110150090040290040254038080c0361003942c6c12001c2e600003041d048a80090414200780c8400000310010000042c05a840201c44107050079507515080203000b440c0d0007100002940e600d0401885020800c51045800300281044030400901401e4200000a41c15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 497624514 1250 497623264 497623279
    0x1050108100306110a08010e09100f020c07080d030501060f020a170408030a1701050f18060a050a0e0108010501090606050a080603030d020f070c0b03090a0f05030f0f030708091b 78
    0x10020107607410311494001409041c20610150400601d8000038500c260b02c0f0b40c0c95460380d0780c1c1c61188108003070065401184c20b4124607503082e03010103030380c1016503000c4401c00010b240075200c5c0d1031180703441a103a201500542142c0c415240070f41d014410203004103182c0c24a20b2a00080c80c200a4550721075040c000c000e40700030840070300e60745d91030016507000e00b2040b012241c0d15400200c010b0210b520031003402001a000c83c002046900b09641401072000740504901071002040c03540c1c100141c001418030342c000d050031400040d2a5592000b0a00510003c0403d561039410700304020300f9150160840303180541040010014640c0c1300d4101c170f009120034030b8805600c0c4c40e03000000e402c3d4421040010444c1e4004100c11010119810040c07100314400c10882d030b20241e03140301d248a28001218040003e4015160100114074200102e0304440d205000344d070b14001d850015a00c143d003015a4010f1011404010480360079000903240b900320b09514024400811400186804000070f1044075010341c0c0d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 497625764 1250 497624514 497624521
    0x3130b07051e090a081b09061504170706090e041209090218031b150a0201020409051003060b490506040314070b0c160b01060f0e031501050108 63
    0x4244151400c1640400c2d1000101079000c4580040f600601031551040c020604001001400000c203403507507a6031610710201c100980410007000107401030005420000c40c1076400e2440c0030300c6000344040d0400300c0219004116000d0518504180e0760041401e020200c40180401710100304440d80c070551280324002041400002101d000029500124480d80040b0ba54070b0743c04100084401480c0058088980101c6841c103001c41c2ea0b034107a40030303030b401c05000b000e80301654507404001c0440010a000140c1707029600c6a00c101180c0045038000c0d4010b03041c001c2802000f0701c901039080c0c84181107a160b5105010a040800307202031031444524900000e807069003150001e50300480c016000215036801d40c280c5030a2042e12040e088408400181d441d69900b001c1d01c1107842601c41c0c0c1c940003401c9540c0c075559021002d4042e48100b071100c03aa4201c0d0118400095214903045010344029510f0f181900382c0030300c0160450b4a1035951301e11031303008080d5100d140c1d183c05245034111602460081c010b0384 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 497627014 1250 497625764 497625767
    0xe0402030411041a01030f0b061b030c0706031416080711070f0909030e0307270603060906090203010b010e010c0b18030f0310060e0306041b0b0703030603061103130b07 74
    0x11082c0000e54105042801c41c003090019135801010b010b100317032014003080c0390031082d0608032564483c0300c40c0d10180900c0100311a510610b9401c01881c041030031649000c00405456140c401154020000691581c01d0300401e0100c0000a40d00308024040304c0c0302c131051065002d84542402083c41042100b600002501c07201e041010000800103c00200c0c06c1e16141c0f4041070140035070340804d80110710b84550034695424000303800ba00310303400700340d480d8103842c040c82c03149601d84e030004400002c06840700c402002040c01e500c10000001d108140001d440e42644c03044c103081d1010010141e050000300f8450640c1a60094850b0092941c0030070510240d980d0784400030070703114104540350303030510010422400e07013140310000314083c031100304a502001d030751950b040b9017141d070315a13109404d40c10002c00304000904401c400044400800001300050b83c50300d0346440300390808181900040e440b1070003041800407910400c4220f0070001882480d601e030003408036440394003005d8001d0100303290100080009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 497628264 1250 497627014 497627033
    0xa02010311040b0c150601021906050901020d2405030106180203130b07230301240c021c030306050906060a2d030b1305090706050703050d060620030a0e04020304 71
    0x801e40c5611058442c0038a50400c0d81d211745007a851100c8203400f1002c46c1e015800040c2700d010011449014405290013580c1c0d400103040007a120001c20340d028040d000c8101d040340980c4981c0241485481d00c07a8043d5150a16800c0d0103a1016009034542a800e00461242800203004803485440241e80c4c3e8580c1c1c4240f03c11403129000142171100e95400340701d481c6a008110221018046800d280c0c0d03410202076030340083c4400e00c144440e5a0400564001d403004c13959829044040904043d04600c805802040078040d10090305084580380d1180c960030981c061056030046c01082d50348040500e00321010038000d02c034000d441014420921002002481490740e8944103040308503007030201454248018018012000707581d84071306024020007a03c02038910440b0711036655107008190031071401c1002d5441d68002d00301901006420843c0044e02d207600d024810003055195114071a028020803c2c14051440c402e580c0415082005448a8a07500502100482d02c1c200c2d8010303640e88943c501741150303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 497629514 1250 497628264 497628269
    0xa020409060203160f05030708091f1508030301050d0b130804080a02010f0309030206012904030b0106020d0203040305120a030216050c01030c0f020a0b060d170a140c0a0201031104 79
    0x2203814400400c00300320581d009035001303044201030b2028000e10781005a41e80140e14111800003001440021401c91162100321b400500e401c062740d00a04003010001c1c50011000101c140c0d0580b04c0444642130026941d5800003001c041000d1030071541404002443c140480c03901400800c030b840c0229080c01002030020030015404401180d445031f5030140d0304d86075070721100140c0c0032801001807041d06500a01801010642c540d010f40042ea0a0007054040030001000b02507c50000303180926a2100c4200180f0145006505001d40b661415000916140c41c1c4583c0000310b410602c010070009500082c3d20400420b100d48607030300c40c912804100c000740140004c1003100d81641d280d45080c048041105e9003403001c00c0e627060203e6400c115050b6100301d5405441d00051740142400c40100700110745035600510010f2101404c0807590322100d040003940c00c0300d80354140c000030b05648200c1e000350408010300c4005d190681460514001541c483e031640c1c0d400b80c103154581518030007101441d002c8401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 497630764 1250 497629514 497629519
    0x15170c09011404060b0a21020c030706090506061005030103152c01050c0c0a02040b0d020a2309071403090a0209070314011205030306100c05010c1106150102030f0703020a02 76
    0x1055a52850500040c0820381e4459001d98138002001c2a580503580461718031510f6030700c1c1e2116840801c07200007841340c41d4a0540f980142c0c24006803010304c0040c0014030780907014110104050f1140e01300f290418a02415252140b42000c0c1c01c0310546800c64203a90449401c050b620f40d40346843c18900016060001406040e9110b11000d42c044999000c081001005004020080c50340d038049a10f100c0d22030a206036055510a0068800600c2e041d00a079036404009404040304500c01d40c04581801c4240e0032081041d030011000086819400b8020740340e101c4111070440350307401d0400e4054880028806003c0c821207001001444440d8100108050b150f03001d030541e40c0b5807400c96001002003a03051480010111000000948058145070301c03090107410001440c0341d81c0b82c480802110855481600d0248082541e8400c0411020310400c03002c988241c4920010069041d105414021b00a00304054808014024000c2c1e0342e00006460740c0d140400c0b086075989256007420307854412410030095 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 497632014 1250 497630764 497630779
    0xf0c0302060f1c060305120715050a05091209130509150a05010602160b04060302250302010204032109033306030201020f06070f0516050a0f0209090115170c 69
    0xa0082042c1c2c0041c0341c0f94491140d0144107111059030351054408521014209900c107402d2021501500703802044041c2c030410b901d101d00c4010110020949008942502d80560b50700d042001204090000482c2030030701d960301501d03001183c000501d00b01d0050360740d545104e41e43d000281849a0801050440390710104c5050020301c1c2000d450405442d00340144001802040300c00b214150040841400b5aa1049d0f2042d0030701d030406400301d000f5045905000550281c2c00d00314034a003800c80700910300b40343c026800035a172030f4154204a140000c1c0f64100c0e2034113119900404410550189003d02901d034420590812240d00c030200381c801d4941410505103641000e008030360000c0059002a046a200380c007500d03004a1441034007503d903142103c080010a011825403a2081c0c494801401e402c07440c49661200085c040e1a101e00c1c0c11103440c02210400c8008104505510b403c84141c4e901507400701c02408281c440182c0708900d08610301c100f1044080030100d810030750105118080d05194082c2c01d10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 497633264 1250 497632014 497632027
    0xc1326010e0f0705030c0109030602130302060d0515010914090403030b030106080105090f03040b18010c060c03020a14180925050706060b09090723031806061c0f0c030206 75
    0x1548499118109180c58410303082c0000391405d0228100f103038000161511010701d45151200f13000395003c2d95040403005c501d141c02000603034910015000b0f60311903480000312850088036400448a01c105c1c06810b015804000700084846c55640c01c854440954898046446502e410b80c080d000d2070850704d5042d400c15002141c2044158041c40c03040815004a0313440008081c0303444c3d01c900c0303030380950004060104007240008030124110f01c0540f006141c012411443c030b03155030742120380550700c11000940024100d402c0c686e2103011f66004078900040d06180c044800c810803c3c1c04504400340c0d0140000e0400034501203c1801ca00c181200c0c0c900039108003107207034a0010026400380c01c0c220b0340300c0d10b800004124aa4000140c983c1c142000d02020031680300c094040e1030700c4d000301c10890100c03c2c03140e44100010b82108042d50050790381d580c5a100c05505258110306040004000034001d10003110b075003121110002e80c80c154150003400f01c080360581410b0021010031030b174001941001000a21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 497634514 1250 497633264 497633291
    0xf0311210c0c0d020f091f0902040e091c0c020f04050f061203030609010509360c03030c1b03031e0702040516020a021513080c090c132601 61
    0x140211030030403040c2e40903024440204901e004007414003a402c0300d01d030213078072040e030403d040300310340200d100c0007204d880a0420300711901c103180c0c0781c2003509842d0b00482c0400c000c04940748016040f20401c0003600c00d1421202c908000340150803080410420054030090a44d200c4035070151310920041c005110901e07001d00c3c020721400050744c1035401428402441d00080300c0101c20340e4017990005250701566440d2100308894008050302d1a200c108056000c201a03180c191103404511290401005010142c249080d083c62580d540c0b0f01e010360030030085801600710110701e40d821680f500009180041241c0082495030144408141600b41170f100071802040001c800b80420364801c4509001c5a81d4103c1000f000590280310100540d000440d4078005140c41c0c0880580348000144603428501d528510f855001c40642c001d00b10780d004080341c1107450070100d08240c0c0c42201c4244081c58013000c08689543c040503031091180601c846031610400310b221414080341d80b0060402445031000d585038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 497635764 1250 497634514 497634517
    0x40e01050901050114070b04080906160b090d08190209060a08010e010b0f0a030c2717070b1b032a060a0e12070c03050d08070305130f031121 62
    0x26103225080c501d00000700c5612590818014000d1900303283d0402c1c07025a41d40180e8400900112010441800081e442c4d4903210050700803406100c0d9400c481d41380b10700304190101e070b0152024403240c000da003030740c04156086949950007142c0d0002c0d5640143d800382c4440002c1c0188030754598003010000b04e04002036070044203503040c0d501d000009655640d844000403118420032400c0f0080300c1040c05101451400303a4800074003c1903d0034813502c85207900d5100007019403001070303e400c0951982001d0107100d16407120304540040c181e0007480341901704290080103000341c420314402da07011218040100f0308184190340c04502119034944801031040100c400b504ea14251851813441010700044029015004400180c0355480240403547c050740d210500c070340d120310b40c2910044150080000090410049a8440f0300541d880341c200d800d000c5801415200060100700d80031040400d40400f00b00381c8a09076120562600740007000503298000c4900700384584440442c001c050b00001210441d0300b20 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 497637014 1250 497635764 497635769
    0x1111c0210050606041206021c0606020a1b0303021507050c01110408150c270306070203120a0504030e1318110312070b010905041401020c010c030c020c091b0d02040e01 74
    0x2081840036603189003c0c000c817402140b00301c8130000a20303841c3c100415079a0b8010040e44054180c02c600d82d5000785002c800b03454645c0e208800580c440d20032081444190514914480c20000c50b100d045840d6444c029a00d0f465580720700d40244c40c07240030458a43c041c10441b41204803080c0240443d811004081003503400a104034505030003140e4500080544c0301c5407041c40380c0049403545007030402101c4441000c0e20518154003202e0140241900786650421103075224009560042da41c60440701c84111408030b028014104040c100418040069044035120030150320588902001c8510130100002602411b9002e00c00d4840351180401840649042c650103180140c08032542c034002109103c54070b100d070440242c900400000148040b1080780c106179082801080c420740c03000305503035005007240d00c00c40301da5a250390b4650036070690351b1305405032032850136050000e858424141008a0042e54000b4800c1c1040880c00041d006000380010942d904a0488801151200e44038403c07000919000e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 497638264 1250 497637014 497637043
    0x12170c0a030c1e150507030b0618010e06040308070303020f251b0f0b0a020a080a080108100b1e0301150602010608011119050a02030909190b120c01111c02 68
    0x3080c80354070720b0f000c0302c041c4070340e466121107007800e50b1100c0400340c4000c08014011034200b41e04d4216804041d6102c4024042c411800380d020586100c40307100144c403c0c1c042d0880b2502898082c042000441c907428240c0740c1d82505414056526109101c10400c284201103440702c0042e801c1962186101041095181441c4100c1941440c00344580c54460013588503c80d50068080e9050107203c0703010200c000d445401c0c2580102c0314001d0b003a41d644181c0307800480c08030000a15140c01040350f603c0030018140c500e03443c00c60400400c1036010214000c01400f62810485066040295159407400d60000c0300c420102d000901021340c884500a0180c20342d48552800b0307609004110304192a900f044511180501c20904c81407000281c040e903040c0c011030106420340c08244a041010388030310350000d100e201b88411a5002120f814010f104644c18101c646010300e49200c911032800a0000d000c0342c080109081001d283c9000007101480d01e400414404031019800982501d640e40004444104e00d07501c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 497639514 1250 497638264 497638283
    0x130602031b012d060e090f07050d0b061c020618130b100f0203250302010509070f051e0d05030a0f0503040209010b0a1101060807081612170c0a030c 65
    0x71050450300b610800844881001581e00c40784010903441e4000c00720041d40000c000c100c0315030741d030301c140520b6030111000c4481d80c000119419502c401840307182c014110480d07941d66001b0140d00d4840314000020700090250034508120a07020701d0700c2d40013000040e4010417143d41c0d0b1091508209220341c01000c201e0040d0400300482c4240c020324000d01d08912400707000113002c0e621490b0200d46600781402e22605501080001c0640540452200810002c000b1442e03808000d4a2600908403a402801068140c010002c01d1000040804400c0f084590880b1101e0f1803000035560740258004446c00e2913440380100851030100704010026003040c690300e0f02c903d540e080e920101511140b00807075000b07500041c150300600028010303d02400700310703c180c600320000e4220b452501b03003144c00c1c40c4c001844a81c031610f42001811010003200d000b904050000035200c6141c4282e9003031032030700500b004001500d101c9031080710440c0b28050700c14507a5030604581010041e400d001c1d006038900c0e0020707181a0788 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 497640764 1250 497639514 497639557
    0x305070c0b04140d0803070c0213050705090a0b090a0302010509180a1b08070206041509050f0604050c01031a06030408090604090b04141314100c050306040b0406030f061113060203 79
    0xe044c580784140b20b801000745480c40e070320000220303840a00860101e0344551a08032900c100e01e980d210703142c458022500c070143d850001d4800c001054003103600482c00d41c2804c12880100d600c403e2600c500301c95080c00c02c992584c02540000c0d00004075024000200c0b400d210410120740300303e40000055947c00103403996803610140003141c101400700d8043c0050f900410104000815442c105e01520481101c00505504656601c0e801e20703404e202e1444095100a081c4000d03c02c3c28000d462000e031007400c0400c8441d0b81c201d00840c0c80300d2040011440b408002c400a018040d03684100c4071080c500a0400d5500da03202c0c04000000e011400c030340c80c0140d00c0d0800c0c0301281000303494081c0c003500f41801a0b00c0d52500d00d035262000020142d1141c082c3d401103011042084c442d0703014800d448841ca03201c00d82c41c0d01d8410103010072940c0b60b42406106a0500e00d082011501ca40c4000042c290030003804100781da5075070201002d40c0b10b160b04c0000c2c1104d4080d8009130090780071018182402000002a60481 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 497642014 1250 497640764 497640769
    0x201031d250503210405100e0405180c06220f0311090606092707050c0606030303072f0a08040915051005090f03010606020a051002030408030109090305070c0b0414 72
    0x34800c1c01820f8050b07120058000906504039140c14211881e0740300b0515082d02e07400802c20040d40802c0d43c5002c5508000007113414541030040303a034090300c1051600100f101e400a00ca0380c40c00c18144070f5008200026503003942d4140f03100c507030300389a1100c928054565500ca0000c80c9038120345c401500d150340444030851540c45c02c419070780d000361402400c41e0f04041d0340c232007004021981401080a181e11001100843c26281d20046200312000d45900703850b940710103401810304000610b414420b030010020407000c070f83c0206980024455440c00368000700f00ca05001c030580081000c86c0c0c43e40d41304103000d040422401100410680720004c80501c40c000228407401011085400340b26486224112140081c1c3d1052010704030503400100140b4024641c080800d01b16902ea8202d04010b0b04070384034103c01c2c03100c200320200400c4010a02107195190903241c0165600040c01050010b80d2100103600c01d141c030070400d8400309904a00034654083d40d0301d80442965205101e29030354004000f1002180e071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 497643264 1250 497642014 497642083
    0x130e0c091e030601091a09010902040918051005420301090201020d03020d150312030e03070807060915020a0201051b0c1b04020f07050f0c0402180d0201031d 69
    0x1141c040c00910b101d90030141040040c0a071701e100350101150407849006155034200c0b200b4028140350700010784d2581040502c20584040a1610b00716100e02106080003c600140888410301c142174002040d85441d421078200e80403615030046944406c4200e03101e4003401980e90350640400b081a03d8842005800f810b00341d5045540c044d0150304030b050b48185650280e0010f101c100807001001030744004e80e40b000817403a5000d42080c0c0307640302c10441d850542c40d05417055040c000c0c00a00118100440c130703a2950882e10031180d0003045607864580b000200845009a0084080906c0056440d01c0407140000d00925040310b0006003944a80c01036028004400c1c204c45504c0070f540050490444441110300c0c4182c5402440ca800c01c0e800c0146801382c1040d4070181021a204901400700403001d4045940b03452502210140304510400800305980c4003004041094202960410410390590005030010500908407050610400800315406800462102c0340141440f41020b040500010207000701e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 497644514 1250 497643264 497643319
    0x11010f05010e0609090717010b1003361e02010818070e0c0d150e151804053f0a17090a06060b03062d0105130e0c09 51
    0x304041c03101240e420f081544c04070350f000c41d0100403250400d40e03c2144500c880d8891100c180241d640303170580065490041c20700c40040322240f505108aa8941d01c50380e424401e0000280c81c42c000c0c843c200e01044481024101000390030411501e04403002c500d482d40c52000042081340003034040000515030003c0030103400042d980140040c000c00c0d0400607100c40e200701c007a0030070810700c4003480b0318281783d403d50268420103040324040f4240b803450920944c0d000c3e14007a049008038100301c0c410440a0b03c52902c17208200c8808400008a5155030410b2030a04000d500000e51018900d0f107011071a00e0030062401c00d00305018010f4a00b40c5254070400198001c2070006000180d031a00760202100346d012035141c0200c0712004dc2e4074640c030165210811562154080e0744010408010410742d89002d402c4828042043c07031089084c0008507a90720346d50000303032020740c1c1409000b042040a059501c1c070110081e128003020aa602e040c90780341e9900307075080400030910952502010608103006070103a00e00c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 497645764 1250 497644514 497644529
    0x1403010608190204110a0201020a171303030209042315030303041a1009050403090f091505090a060e0a0509010506010c0c03030e04091b060e0324150a0611010f0501 72
    0xb070400006200b024500c410101a680b00e600c40340e2060505140e140141030f5280103400050303440e1142800941200e46140d0b0800111070030100f000201d540103070554802c1b84c1d040c600181d452088030006002044164241c1c03401030202d043e184d0744000b28504403030040359070110055442d0002010999284021940180b000e011a11480703003001600308400d81100540351561303503a42d110750784202284d50407103044d0006810481c00b0403500c10000d030f2020243c06401c40a01c100c40803c080381c046c4083c54442c55006841180010307002078290762200015045140c0542c000341048010300d4003602040e9940d81c03403540b034000420001c3d1b0046982c800b40c6035010380c001d20920328680b01640d0503060302c0e0409802c59102c11420000894952811052007000c5079144900c6080000c014840d504400d40603000740c0c46103100548000107a0b440269541401503036034100e0b61070b500d18100798102840d103142c000822100104069030482000c1c1d00f0b003807a6130020001c044211030302105075a001c0c4130310305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 497647014 1250 497645764 497645773
    0xc090d0809031f0504172b06170105040c0f05130905011b2001020c1b04090c08030a080604110901110c10020304060809070803040513061e1403010608 66
    0xd44140d01904000400600381d4404014402c124000300707925000f100040359580c0d04020800000f54038401894000700c2e9800c0c100307081c00b4034501004110800240b104000c103062403c10700c0132074000c10040c2004440008611a00780c1580b03020b00f000740c1d030803a15001c07022804119450541449011608020101046041c1030030b000c0000b0b01003207401303645035501c46122204841d041c054058030a849a5030348511086642068980c07021200384a603050b90041201112101c40002ca80000c00801c0c1010280000a040090001c10068400402c450103080000420220200c081c0c8214072170b44c0c0702c0d228a669040100421a00043e922025000c0c0c1441000c600e0351064100701d4000c4050001c03503401e031103404000342590f02c0400d03c1d040140c0c00040c061001c0c03684211050b810259810041c8186410720003000d4490140380a0350307000b102a40480450180c4075003243c0e00900d00071170000b03140d017031600485c034250146024001c0d42c0f1100310b45d00c0980e070505100701000c5901741c00280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 497648264 1250 497647014 497647039
    0x2b0209010c0209040507030c0e0403081e060f010c02030a03050a020f0c13091b0f06020d0c050d0f0909020a02030306010e1e01051c0204090e07210803070302040b1903050c09 76
    0x3454040508203917080e21400300701100280c61403001002900e805059502e251405150042c02c000c0014640d03001d50f0480019000c100011030089074000c1402c44020904402d5140121000c081a40c006981841011264024180c1041c010403050000c2d40c240c1d910943e050039826603621200d48001d800c0700308090503070424001540010202c920414400f851224902540e019080c01904408500200c001c0d0401210fa010820b0901000b0a4149002088103584404d40c030754030034010040c1408101890052078030b00c108100d00c080d14540b041103448882007e8000c2da030f40c0003210400d0204408444090645c50001c24403a0500081e946565221441da001120a41c01280855141e0a40c0703409000c4e80c104140040c1021704540400040c0380315501641c1c40ca84440b550283ca54101c18064480580500350401d800c100c1c0c1241036141c0d2912681012002840346034400c00c00300074007051310380c03080086186840340300000c0da60a002549403503045c46814800c102c100c41d0300c407400d01580c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 497649514 1250 497648264 497648269
    0x801080d08060609060c150709080604080a03090209011e0603111c020910170c1c090c051f1d0102070603090206091801090c020d081302152b0209010c02 67
    0x429446100500404c0c1800043c0780451083d030010b024528154018030b0300c00400302403025600740e01618515203d201189454505500c8000140c40600101d00000303102810350b010350041402c595003c2d04c03400840da1341d4030034050040c3c11500c0c20440482c031aa000692184030740a1084100451861645040000300410901246010400711115020b00411856036901c1140f0a0b131520300e504e4059408100c0309a402258000030102c50100d40240841e9280600d01c50178005002c40513040003429a250b810300d03d120244681c03060f40c0c49035204c6801d1030307501d02d85d00341e6119454107612000f16400d80031904025644200c00b44a0040c0e105420401009220307400c140d44860019028a2401903002d0204400e0a03103844460b0b522180040104034844031b511403c050011303e0300c00303048103502c90100180100e801a02d94128085403c0740d650030356844203c07800c1003812150581740d0300c4e0012a848443c2034138080004003040b006103e04600d45105000302d800700302d0160743c4d65802c50ba143d801c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 497650764 1250 497649514 497649527
    0x706031505010c0f050d170108070b072303040b09031b03060c1605010c0e0a06090302010e0904140105190b0301050c07061d0303280b1e131401090c0801080d 69
    0x8181c5644d02d00d81d00c807a022407010712039205a507000740d070b41100e00d404a0001818402040e03011401c1540110707020003180c1002d07419144480c2d4007031130000340c09000146807408000080f41180c0319000000780021a9003040f00204074002c0d05030142d6510380f0907054498003490301c2401950700354000d00009003405c0555402041d00c56590803101086100e0782d00e0f0030b821078011542e19000310b000d94001031031a1070310f6401e620003022030745440301c2441d0943d4002042e002c09000d0035401038076035801007400c0085030300c0e00203c0000b980000700700a10382840c204100e8520000009141c0b8a0003922510f40d05041c0a481d1144c1803441a203403900d101950340c1801030090000701540070000d410542e103200000e100440c0500421449041e203088104525101588814001480c180c030308281d4004540303030007010502441c18010305a459605500c00700f501105c188400100103460b1400c0d02c0001340d000c030090b505950480408001100c61028150303220b40080c002c0e006564008483c3c404610b11a0700c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 497652014 1250 497650764 497650787
    0xc06060907051c060806010806072102160f0b011d01150e1905091608041106160605040c05041107080915030406051603061a03090304030f050f070603150501 69
    0x80c2103441c001c001c8107043c0c40320307200c00c4450071426120b42c4100070006040112501600e800b00161480e4100342c50064808000d00c82d01341102d0884200b40c12550a079581524030b078003920300188100100e6071400f00e10980c0b01010403940c81c41e920b4004140d505010400f0b4410b503403640c6442403e6401c1034240409592010b04506c2000900442e0381001c0d115800300d40d44800419503a41034081c01c210400540030030042c0300c150310091100c40c19855940c4039441c103030801e8000401032000982c1d40003003640c0784140f41c14610106e112620203410400e040e1320462103540a4200d0b098115154000c11003541c40c2074408181c0c03079006002e404040b4001c0d170000d00c04801b0041410010881101c0c815003250011a0b0035258103075108100402e00c0c1071900410702e169120300c1c08001c00360415101c01140c2041400380074a1a0000c00000c01c000010011240a107400c00341ca000741e601d4600d00140d40b1121181020118020362500081c140d01a01562203a5034400010781f60140c180001121000c0722003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 497653264 1250 497652014 497652017
    0x50c131508180d051c1112070c030903020f030a05030a1d0f03060c0309011b0f170c0d0903180f1d0f040b040f02100315060504080a06020f0c01111306050c06060907 72
    0xb134260841741181c52040010080c0079003a580c2d1280a40703818503071038150060a84080c001240180000a580042c08905903603044400410402c00c100100740f800d100060010a24800000c41000307240d000940031340764604072510511020f12040c140110302c48a03520050701030f031010011070440d102c0c80020b141d100c01120000180c40e10380000003c2410861a84107011030907000c0484540c6500c510580508a00f410040c0140d0800d44140308541c03142c5d442c560384981c0d4a80d071400816114442070211034036410f40901031551a02482c5401681c0351080720711440340303505100010f07002100130074414203003410182c0c0c041e03647c0c1d254000300850041040301c0c1d0104003d0100011394803203540d108a003403e40d800042030216801c0c001d110603055042031003800300030b120411aa800000c0c0390340000e940700b1000341c2c8401400f02001d0042c01030760800d80342942440520490002c451015049002007030079500070305561000240c9452084da0080000b070f8102000207a01810400700854101d18203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 497654514 1250 497653264 497653297
    0x151906110a0f0803060a05040903021e030405030109080406031b0e210a0b0a0b04021206061602090403050a0e01080415051504021206030606030c0d06050c131508180d05 74
    0x41d03541c0c0007890a901001100da0140100a10049050441c1100040c11040c0c078208202404c0303440296403921481203501558044031384601c00e0f00014404d48000b000054024403862290340f80265440e080380c0285000a403601e00b107a40580b42d46001c0990b00c414503210008001d019405002c5401c03030800751107030610b4408000300d2102d4810807081119a028007020482400d1882d80d410585100250b840c0c481c5005100d05d1403400710a40c80340d0b41103001142c045503500704400210004815524019601000c0c01e410403060640140080903c0c11031b60f0b40f029840c0313402c3c0d00107482010054402601e0380c03000b0510111694265441160000c03004440b200a0404010004099a2194442c60003215595041c0652030408002c0150040c0088016000d00384802c00400c6441d1010040a44059151004206000d0880b01150039042482c404100e281d41c491518001c6010500100e50021b41c4010005104285107941c2c044140302c55000b41c206c075441648100d0f40b9400034a41c981c041e240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 497655764 1250 497654514 497654533
    0xe06010e180721050405120408100b0d0812190507080402120f0f010c09090203131b080a06020a0809060403021b04020f040e0912090f100507061415190611 68
    0x405031081d80f03840207903001c0420949420300d807043c1080e03180220110038141c01c7c0414451082e01280c500e40c42170005078001181550180000c581840c11076016000e114001b0310107070701d2812807027024840c03c02803585140180c90b0002860403100d00712442000030720207074040750040c5040303802c014140ca186400c4681d00407d4000b902e0804000e5404002c02c0d80d51002c01080700c41c0c00c042d040340200031110b0114103624040c41c900e00c50a5140000038402d01c0603580f104000d02c1c1c1c01c07000501504001e000c8901c0c0841600d4403030000d5000c0070420021450b1f03031000511141c1c00140b0b01d84515411350107030400842014616000d00850760001d030b0700a800b48072040c00e4404150141c002000640d01c000c07140d04100d140341e03051000b224011100440c2c00c06c038401c2c03107807603800352401c05001c246c440e2150520520421111402040c0005007500c2c1480070751900301c480c0c1e0100900410000f40c4024428000b01c1c00c1243c846442941d00000c000640310800600380500b051100300803480003078804008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 497657014 1250 497655764 497655797
    0xc0c1403071a0a2910020f07030f030203040308130e090c03101d120315030714010c020a0b03040f0b0601030c09090b01021501180b12031206011e090e06010e1807 71
    0x4620221031104c54402030350000c00345c0351000b02c8012111103030000d01002c0100201640d10b030b81c01e6000c05044041ca500021041510030800c96000b035801403a45911100c00103011440352840d4460024420700b40c9010582201000c1601494a0002001004640280da141001800045c041c03240e840041c1e0303454100140c400e0005480b203894640340c0540d02d10b0000407500c3e05482c25203046020341d00c90302d0184000204110504070188090911544415040c4001548014180c0142071158008000d1008104036030181201c1d0a10640341c0340c0145d03482c840114100d85007401e0b40c40000306002410450b0092035444841d41400c180306803800e201410f04407010008087c4d000000e03100d500c0380b044215001078402c04600c102c003110500c20120002c40c03081e50700e015a12104c07494040002c04200160300904c4d41085440c140e01a10180c01c0721480c01400c403564038414106903603142c2000903142c1d0304c515aa803030811002018152102d01d10301104075920070060148007030024032104100c03103c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 497658264 1250 497657014 497657051
    0x40f020a02030c0d02070e0f0a20090a06031a0d0804030206031f080304030803010b0307020f070803090301060e040b040b040f0b0412020d090602070506070f060c0c1403071a0a 77
    0x100c4980c00541c1d03070391080d9059501c1e01c104141440300f1900012001c1c490010480f00c030b07980145049004140648458480c00010100380c0b013030220038030840410044c1e4443c004040c010858084586102d103a07642c6000b038042d1040c080044140c14410b00c1c010b0410310301606109105070044400c242080c0c1c0b41e40c045055944143e807440d4202d01e006140d00c8410410a2191015003c80b00140d0704107499581c61100714041030145071003c000100018810341d100b004002c000007111021a0b44250343c07000c05070340300e030b1004d1000c60080d424414046a80d20940c201240200e0380842001e00a0f40c8035100d240c9000f901800480d003c01401c210400461126400d080c040c901400076a42c881c081402d02034a0980c11180c400280309071128108040d5801240000c12950f0559040350740708400d251200d89090010001084645081301c0d00010b140d00030b1116048074800c1080c2300c3c0318154141016a00d020725200145100c100003000310030049584810307600301080680109541c500c0e0781d20b12001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 497659514 1250 497658264 497658277
    0x130e10050c090306100501050a0f170c0c0c09040f170d0207110127050108150a0905010503191e0819030b3f07170c210a020f040f02 58
    0xc06001241c240e542c0e180031300440b80c00003215400210382da85850006001d5000e82000c860510060681c00340c1c0080c025038140c00c2155481c42001a070380342554160b00303550030030b070004150340c8164a8452100e080501c1500d0242d078014251907005442699032011800d00100544010740081c00164050052030000d021400d00c500d50064140b00c0f200c000420b866181103080d000c000088000b44070f10200d00d03004400307580c0c0c00c3c42d10406a03600d50200c0c052008070f20642581140c4041e00010340848140e120b14140c0300c0843c11f50351041c4c44101006c5007d0341070640600f0f041441078080300e040701c13001401c0840920444646007070100603180c01c480703201040200b00201e512120f582c1e00502d0720f26050644549801c1255100c031109141701001c1c2d0491aa000700000100d0105072424901002200000c041541460314540c3c10b22409948441c907801005008400b041c19012030b06c0909103034030054000040007058540200d4007001040100409850380056076032000604045041c00100350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 497660764 1250 497659514 497659531
    0x30216060207080c060414150405150306100e031e071a03041b121e0f030f1403010b090d03030605030d020717060f2e060c140606130e1005 61
    0x84074580483d19041492698075240304101c204014080082c02d1401428030740400d0f0b80786010004840001d070083c3c4190380103254040209101d4440046280c001580b186c482521442c030041f004400503524680c680d2905a4150042180b461070202200e0500b0b082b0040b5204890380155505508154030500d9070304c50001c108004204000d0110041801c07441c400110011944185800050092204002c000400280510000715002e2102002d520880d58001d032022200016070300e00584032a458070030700408210595050420768001c80c05a81c100d401c0041c10924101a590802049559800013141450380d220380124098404101c2c6142c1848240c00400425007402410000c1812200300000d803507024008200301655801c0003507400c180407080c244004200c01100810790500b41c14011020fa510780c01c0001d6450b40184190102d50042c2090541111190a070340c0d125501120f026030030001084680c06d14503440e0b84890340b58a244c2050f18072b4507000e8001d000940d44142c2d103c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 497661870 1106 497660764 497660773
    0x50423280b0309010605010f030e03070f08130609140a0b090d02061612111903110a08040b0c0111030907090b0d0218190b03060604090302160602 64
    0x1405000609078181d1030749000109035000709418411280020001510090090300910580c20705103031820240d8603003c01910be90071072242001c0201d6602c48204074100c03448002d0303a1407001901541d0386080d0380078070b811152490302c0100d8070b0240c41001c4c2564100701403403c00c1c0403201040416034281d00741c0295400043c10b01c0c00b0b921000f08124280290392000c122085c000101198410380303840250442090f00165220800300316083c600303040c0c038405000310b40110800040c0781602000c45824a0702c0c1e5803241183c0c1c0141d840682c00c5c04e408100104032841c28011800154810b020782415480c00003000740d070b01c2c40e41e44130300f01050707603a008031241c26281e5201036201950094444407a10f84447c0083c0140b210455404604c2e01000360125080f803814000d030303810180001c0040645407166403c0100501c4101d000705c09511030051150b90000364500440006e21a5030082c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 497482014 497661870 := by
  have h0 := BRFrame.cov_init 497482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 497482014 ≤ n) (h2 : n < 497661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
