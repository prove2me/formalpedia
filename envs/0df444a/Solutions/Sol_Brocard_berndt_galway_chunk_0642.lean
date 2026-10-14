-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0642
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:53:55.486272+00:00
-- url     : https://prove2.me/submissions/22e69361-4f53-4cb1-8747-aae9a4643332

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 115287769 ≤ n < 115467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 115289019 1250 115287769 115287779
    0x1f02090301050a05180a0c05040207030e0306011707140609041a1215010506040609060e040f0606230f09040f020f0307090602060603030f03011202040e0f0705011701060c0305030907 80
    0xb9180c0803030310001c0c034503610300030000c000d690362902c0c0b603414400300b0203410100301950b03072100c940d960703401168000c41e40403882c3c908160040120344d41c542801000c884203580c1d00d030080020b07445000c20200a41c0581c01c1c2c009078002c0000c11100310040c000381082c0c01c0500c04001d000040220103d6102040015505040d50b510784c00040d41004081001822400700c20030700040050b0410780c0054002c0000304010000c40b5803100c210000c0c0c442c6854050f1807041803400240141c458040500d1501d031810000040e05500f00f244c080101c0309808811132004100d0968070124001c05c90784030700801c1e08000b21141c0d40740544c44a45810b078a10b070014200707040d0110801d25500122881d502180b5034035014048030b5010040035030300401c00c5000b0761603d4002c0b070740013a00d0300040c07060072400050498603400719542ea8025100601840007102c1c10342e0000380481d80d0320b14861042c980410b003594100140c80b0309490303409050720103c0d12182d42015050764103d40780c1e40003c0c412020b5005034040425 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 115290269 1250 115289019 115289021
    0x13050a1203020405040b0f0d02060c010b06190806010306030213020a09030f060c11280201022e0c030b030c0603060d0b040b01090c03090c0b091203032a0c1f02090301 73
    0x450036103940e40058070380d030404060104a030366480420740300d10200b1807920100d41da8101c0c0d1101c06907040d2040d64540c80f1500045024141d043c440541c050790106080ca00c4c1d900410203601c0391044d0383d84d40c9107144c0301c00006404990541c00065041400a01c20441f01050707a002482202c0e480e00d8131f07000d00307681d070385030341d078a04030000001c41e00c807500c451800504c01d41c011040943c180c4180080c1012044e81000c016104100f0380f0410040448024244103580c02409171406690518140e03a0112070300079075148540c0012100e02d0409031030416400c80040c440c0c82440f41e2004058000c1012030483c4c801c2080d10b80000340b50a9108c245c07441020005400104101c0c007031841030701401380d95410500c1c501c00f0380b890907000508040c6000203040c045003510a01c08110f50142051075501c01f10280407e110148040385c48002d40300c004280304c804443c2041000c110380c09503611040001804404c48894420120f1595403640012490002c103801c4400c11a82f500483c3c03001481d003455400828 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 115291519 1250 115290269 115290293
    0x60108030d0605010203030106170a0207050a1103120a210e100905010b0f030a0b0c0c0102040816060203040e0c0d0906050c090a0e010614070503070615060915050313050a 75
    0x16040e08003198200007200303140201000380009001450171076050100003455120700c2421a10400301100224030100c0082c1d0454a1864100b403c0e9030101c1040e00b028040e002c1d00c2e0440a00a100c1c60a5004607504601c2c140d0b10380341403950f500390007840310403140f0f0312140752080042c0030680d070b0b5014918104c504200d170240000c3c1034031740810303101c03000d003072207402c660700030310b80c14000c84170801602040d680c0403418100143d0300c104000e240c1d481d4440359503c40e0080c0403042c0880c0d8070004021480e4400004c00502c0024481d174500d0055407206000c0340c8a008610540b0100d4030142e02088500e00c1b0400a4416540c2a8800241590003a11181c0581d603040c3e41c0c035283d0f10000a040d48850510b814884050519010482942d504d4950f0041c508499001c0800d0540740200308917007001400d10031122003d400100c2030103105041c80c65203d90780030741d2080c4408204860340c00500d503015903200d207000002c0c1d6241da070705550b6014040348618511800c03c40d01809440301003c00205810124 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 115292769 1250 115291519 115291529
    0x30301030f030810030309121109010b0d110c030a1110021c0507020706020c0105130803030c0a0f0815062a07170604050a0201030b0d3305130b180601 66
    0x112031406082e080190521402408840c0e00c4641c0b103400b80f0200341c000c0c84040858413107081110f0a038400341420b2592458268000e60300c1231102000042a04465004d441000d0000f40100101e055051800145105a03660130495030000d224110000307004c1c0d20a061520481010b5560460140052004a80c090100215007003440002946e28250910038164403840c1d60004203a090b00340030001e9540d403000c00b00d440c10040b00140501400208880080040284d00d0480c1c2c2c580c1002c07a440c60417070f00711180600000c0c4890003158061072280c1a03041c0580c0c10161440d40030107804017407008550010005141008609020504d00852240c2c0c0c1c90204504901070030545050031000056203500106810b01603104d40e0910000c214081004454642e09080002e14116010041a5140c04260b005400d5403501e003901d808888451520b8451058008010b5802840e20381d0f0207412201c0c1528040050300000d125400003943e800c84050304503403236440c40c03207280070b00400945c5081c400340c0007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 115294019 1250 115292769 115292783
    0xc0c0a06021c0e1f0203090304050312030402180c0d0225030215010503030c070b0a1b0501091b0806150406050d050307020411040b0315130504060e06090c15180303030103 75
    0x1d001c034404910500d1440211070000d0581c100010a10301e0540b031a80ca19884c4003036002003c18103c0c1c400700100c5006180140a680c0310060962070f02c810764004031001d9000d0240044400410322000b11040d201e03002d0031030708900f01249103692000039000400650109140e1645c03003500701114424202d0500e01c40d83c01000c00c1e0980381d06040ca500030680c0b119001c1d81c000d000120072030501150b0b401c282c5500c0c07800241c0724440008101c0c0c0e2a60302000c07506003c0d6007144400c05001064000c440f40c20b01a10b1900d800010f0444580b400e02440d11480904ad00032a001c15609809109031a40d106802030001c101262210002a2607004584007100c150307000041c6032086013401e004110941404040603414249041f200c504148002020f2f078060310500040300340b0580d18480348141715205d240e400c00451801d0318189004010001e14500c0d80d114800c001086850006100e440c41c030300140c00011341144290f00341c40580c0141054000040c03000703d50301003940302003028500030740c001c640d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 115295269 1250 115294019 115294057
    0x14030102040e2d0603030405040b0a091506110c06040b070201030e030a0f120b0117070207030503030a02031f05030706140412030c1a01030b060607031e030b03070504140c0c0a0602 79
    0x3140203d40300c0404595103041c20702c204000c01030380c01000382e40448130181c80100c0c1c10080540010305003102a002984854a024540300503080125a03200c1691455100c465480f004031416079070b02c060454071981d00400c108400d00203000d40e500039000140c418100070507155900d45047d410f40c0c1192034408001060380d02c18105d0650f12500b40050800524020868118964002401071288018020030218500c0c0030403036262080000500035604941a02d44070b05001407040c0180d803080c3c80701c1c0e80c08100a240c0c00c0210035074041070030868900034014012103107440000d6402081084040a000d1800c1c88000741c840c01c19a05100403a100f5902d843c019200c81c580440700c5c990500d000480144a14014400100602051741d0404021500c2c0c5131962541d00d011034200c1e528584494010074030180302c402d100d8040c2c22003010305034210280c90f111911441071200302d800c510100c030080200c110224840c00e202900409480e1413903015503603401c1c0c072a00d8040590380501a400414100a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 115296519 1250 115295269 115295311
    0x40c020c030115030b13030c061a01080604050f0a050705040305030403060506041107110103050414010c020607020f010c05160c1d1902072f030d05030405010b12030414030102040e 79
    0x21003484001c03c400b40d040704025045858000c1c104800a18114040700c210301884240760160785288140343c3c2c0410140704080700c050003103c040c501c07200447c0c00300d0481d0020401074a41405074078451090020f8903900e9540c0c4c5401d01c0e0161401030f241c2d0081c40b40030000840820000c9c0003e001a500444001c1554101030f01444120389030040114147c0000344110300010704212101c02038040b0902c0c0c00303c2c060316030342003034041d400760401e4000f02503103401020700c04190003162042c424406502503e940c21910154203003a03c0c1541340200c00181c040144415401e655110802224000c00e803410701c1d561207082007000780c0e200d400c00e8040c0d031a0a1080100040004c941c038072180325031180550404c102541e81644244600d03020104240c0b00c01c0f0241d5184005005200f0904401011141d03503400552014083e540296070a403119420418555900c0c1051000c2e051500888030085107031606c1d00c10070b42d12a590140c50a035140d5003c0000148800841000e603010310750308000700050f16410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 115297769 1250 115296519 115296521
    0xc030408070504110406030902010e21010b060310030206030c070b090a1205090607020402090f04061d060301060503070b0f040f03030e09070810050415150302070203121201090b040209040c020c0301 87
    0x158030241c8600d05111113240c540040e41c040d1400c0301d403142008281d0302c2907440140c4244580f14180f58102d038a1148034212042401741040505098000030001c11280324140f015502c01298451100e5818400810050900c2c00c0210340c4140d4540c9032134140302c0c90344e458400000342510200d0b141c0d44804248418401c4212400b202c0e01c6d40c0d0306105203080c00690100b6900d01542a01a20456010451041c981c65030280e030026194024010865103490f02c8507103003041100c00114850681103000100d05040510a19040d03c40040003400301c40c0c54410060b0055012180310b442c03682c4140070000b06020348002c07e0340074612039210030f041c82c0700400c00d00801d00c0008144030100640102800602e01d041000f840680d18259404180801903640c035440340e80c40c5600c69650a6200401c98202c190b15a000d00b503030300e100300c0a880214030301d000b1088150050100c1e0160411805c001088000c1c100d500221030a00c002e4009828224007000280c115507660b2028005a08044190700d01440d00b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 115299019 1250 115297769 115297783
    0x220510060f09060804030e090a020307091d04110102190f030305070302090d06020a09030f0b090c030a050606040b0103110a08100f0305100c05041e051804051c0509060c030408 77
    0x440c502641c090500c040d000749032000610400c814000c2120200342418441c400304524214050a650000d082040c00000290320854184001402e40f481c00b07c2d4030120000c8902d020074114418403010380303840c0c0360072510143c44090281135204444100f0141c16807400c3c1c20101d01c0c010742c0c010300758042a080140c15a8401011401090301c1000b941c440341e0794141082d00d59035081840103842d82d0b152070040d03d0124894001910b59984400c2031410014113803a80c603c00c641c4501a500c070400c0b4101816518614140001c0c62900010001065030900b1346c402d030500401494040703401100ca08d03071320304546d00ca182004d0008625404101121003050107010041548031030410b142803540c0c48050b102c1d030070124081d080350303250b00514101b50300c85c03419107020f000d2550418016140854200e01e90b0403031842450301520030090150040740045420507c29600700c0d010b09154034502c9046a40d05454018040038841d0910142e01c168507180003030801d07241408000c6680c1c1c1d0030030080a180841e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 115300269 1250 115299019 115299029
    0x30501021c0516110115090510090b031203060406090c0c03090509011809150501081c020307081b100e0312100b0a0f0212130311010c08030114220510 66
    0x2042c80305200601d018072400215940d0f062a054131110f410419090250032480704011041c00c2900740420345900b02e0b88054061170404010384000c541c1c450010046d100790720b00c0154150842c12040d03802d070f59031000940c2e0094000700300049117031b11a8158811690b00200440c005805d01404104050300480301c1d40107417104460902456140254000403550035944c10003110b5214030803403003001300c40851b201540c0035082040c8099038460a801d0b940e00746021400c01ca08000d110300110391400481100c40c240d41000c42285400089400c40c400807819001740e0740300c3c1c40345220b100c1030701741c03035200c0c2614140c88940515070310705124421a07032042c2c0243c0303850f5144011003400c02c00c1130903e604981c2f090910341030081401d205080d042c2e0802410781048149143c0004124821300c0006103200c1c02c0e244142d8403896201084401101d100c854418001e0400030200014020310703c69003031048840d07500504401022101d000f070502e03513040f5075180d000c03c01c0e10740083c0840001e50300900b030003900e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 115301519 1250 115300269 115300271
    0x308040914040c05061b0111030403090e060a05010c05030919050f040608281203090b13030903020103020f0f0c0303070f020d09060318140c03070807030201081909020901030501021c 80
    0x420a078555a241c03030500d20643d80f0910300000c11b580c03103150012044d040549141c00030485002055844400303644204c43c201d00043c071401d00407552000c40c2c0d914030301030400500440107031030a00005555892010800380c036644001d012141c0c01d0358481d900700c1141000b01040702c884034030b040280460044141e0f11180b090782800c07018445140c0006a10072034074640007a513010000c155074101e0880d001ca00d4081c0c20305c40e41e01940c928064054016401061045240c0c040c2503561031941402038400384401800544410000c00142d8402d401030b00f10f228490a80d9454503164540c05041030b408140c0f00d01641e0804002c0001d0705400000d6050509010b0001d080340b48500076000307102d1241401100103140d41d482600884079032040d030007804158801641004208140449a601c3d4189040948240314140e0080351410020903090100ea40c10307180c100840c1c503070001014051175901461145242e85501110160355410034890085000d01d00060303642e240400b10340350010341c2100000c211 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 115302769 1250 115301519 115301521
    0xb0a1403030904090f020303030708070e01080f060d03020111180a09060e13030309080a021507180b0c01020f1903050105010509060301090b0f0402040603060609081c1404050306010308040914 84
    0x140c9000c02154002c2c80d00700da000480c071450b80791000d042c00c0c81610281d018880882040303e5150007106480c0100015202c50024094000c01126603610890701c40e6035189900f00419214200101d46075a80c920900010810404c1580e48d00590b402c400c0b2300080e0705420b04c0030344045007049007800010f0f00442d42d05100040c104024000c40a1020b03081c404170041001080050510039444000030b654130808182d90340946810095507000703c6800105605005c030301240c10306024080c4bc9407542854042d12202900d0208401d076a508030801e0f40040755000c115040380400d400004125184a0714240360100200b9a0010201c0350141c104905005003004559036582d1840c060b030341110303c2101c000c03c800414030007069800b2240f85205402c14008135003c1a40c9415401103825200140d85900d1a6640e895603980d90782003034981d030000003440c51802c00440784100d08410020a81000c0245030640d10700100385003400980c002d1301c0c000000b16081c81404018000d0b26000d952840b206041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 115304019 1250 115302769 115302809
    0x212a090e030415020a080310031b0503060c07030c0c091407032a020118240213051908030a020717031216031107080c06060108040b13030c0501020d0b0a 67
    0x50381c0304600a440c0a00e0b4001520500c2a108110003e20540e2140c03c06d41c40e801d100108a10641050104540c018411401c070701c4034a0b060803010b0110b8400500030300315622070400906807584002c0d026030820281c180000d0100c0d582c600340200518401800240801c1d407203014030034160002e07200d1390407d0700b82080c003c0c219035504540718581400040070521554810340c181d0040280d6403206040702c41645d02c48041c050486503c82100741c6c0e1426070031400900c02050401c0b4402c16402c641b40c80311921050015007085440c3d1004c00244103610b1818507190810686036401c1800c10a006030701c881800e000c1040e040380406070400e05440114100711010400300300a400040c00e0b081d03940b19082135400c0030340c42504501c81401d00541c25075aa2021420720032007543c0200c0000c00c807481740070080f0744c10b54418408144510303042488101642c0b56410080554000080c0507410090040075900200e40280b0090180409114000036180162800c0c0044003a85a2004000c9110810170000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 115305269 1250 115304019 115304023
    0x10b21010b0406030c030e0604050a02010801052b05030702090408030703060e0103030f111c050903210d051f1401020c03010606201603082203030504212a090e 70
    0x1060f2840c906021803004c80e5031340d0840040825000303510b40c40c0b14034424001800307c042520307207225000781d81e000d200b0b1387c075107040c03040c002d80106162503402480c0224000700e1440c1d15441088074410000d0b617140c844560005500c0450986083d1040840002405482a011310968006102403800c4180c103600d507071000f800b22101c141c0b10707400b80804403003034030034042041c401559014001400d403421140d900d44010f003160010303052180a4401c407054a000c41090559600340c0300c1d0302042d85460140901080b4026060180c40420403040800c529102e100010071b8560103445400001c81001d24072000081c68607600f0f04070704d03020364540b0f00d0901405600070a0201e003000100c086040c0150007044032440c29080c8052a400b404400e0b101208120800700201a0414a2000212801e081c1140c13443d902110340300080c082030302048108a40001c070101500144808002c261090304542c851001d64a80c6600038003a90711760701c00c3c090003604428800306c0a401c07007150410440c4142102030fa = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 115306519 1250 115305269 115305277
    0x504050403050d050714210a02031312020703023105090c0d110d0c05190b0a270635150604080318100305060108040206090a03060203010b21010b 64
    0xc1c3d0002d1311500014200c80c00341402d4031035071020800d115900c40d0102c4089601d5070103c3d5030700c684800b00ca404501c92002c54000d9034000c0514180030700b040c12442e0344241c3d10072450003011041d03000f09100080581c1e22007208003401102041d01e81c415000d015842c502118402084005003440c05051288840e400902410030100c04c1c0d420000504050521040e0b400d0f4540700036034001c980b48664010003100007882411903000346c0301040780054043e544515140c2c03e02540c0720b102014032419080500c07a400f030040300300804d403178040b01c062081c8000302c048206410450204003410341054803040740ea034445600107580244005801e0712003034120035005c0086c2c4038144200415003980780b0383e036981080320010100300d030440303550340c2504030b4081c2d14400600419205402c0341a00301d160038040d0180c0380c030400c4140c0d2020010f640341e50801406402c102c84d00d07900407035005c070080006110f80c4020b5010b4550004c5407519001a40e601d030050601000803194800004001048004481ca041d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 115307769 1250 115306519 115306537
    0x2090906180c0c07030602130302100206010806160516050109150204050609040b01021c080603160303170a38030a080720090114010f0201020a0207060302160503070b0907050405040305 81
    0xc1035032801281c0f8a50b1030000d03d5080a010740f8800208000d001c060f0491b01c0f01201c0c802d44245240348414901640c54807400d2003000010b401900000c0d018002c18048111402550b0904a00340b41c045512206001c4804a04aa0320307951610b601702403066030100d800301c0c032081c08410b502d010308140200d04180a504104c0b0b000301d4560301c419200e41c1c0240580c0d00c034118403030407401ca00b00c2103c2009000c40c00503035415000340210f1822050382101401c140b07003074035059125800042c1c9051040c44200d0380c0101800c0d913290b620050100500340140100902c1c54014046602030300c61456003510580c41039480b28806d07400014500700007030900060701c041540015001c1d48680401050782000071b0000d881c182c0c0a0305900021800310058400c000d03040c0c9081c0da420915a14108040c4d00701e2003817040f0351000d48d0003040100300c1076110342c0081c40d40f8407402c5e60740c0740c441d100c2d55101850f42d0040304045440c0c145c01010040301d84803c1003408020201110203011078140f42d00c0c041c1c0b82d8800d900d01c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 115309019 1250 115307769 115307791
    0x170c1905040b240703030b030307020109060c03020708060114010806030c180a1803030906050907051c03020a06110304021f0507030c1b06020d020c0a0e07051c02030108010209090618 80
    0xa941c1c05039502c0781420012000f5030040e00140c0b100c2c0100301590780c0104000c8021914240c48440b4509001003550941035060b1074210311f00b410081d055464640707044c421001c52261050100f2440c00501c81d240c000c0c50300318699288214288009450b400d00104858043c3e40000c42c811f503a903407800100c110b04d19100c60414420f840750741e00c02000e000b00100000840110318100030800d40c2c1a1f205600f4540289801c20454503a40e40301d0352101040c0c0308041e40401500d604611403041a052015140c0c443e0044442000056031000309440b40741c251046110000300c100029810214601c01043c0c05424203201405a0b441c00940103008001000e8100030081d159601041580c5581d0890402d071501c00b00c11469072428025030715220010410014000d0a5480b650750a22454000075a80b0b0070620016941c1c41d80804c441c16007000380b5a01c0f0302c1d0090070030070a200026100542c040d011560002d030b603c203000414841407032005442d060280202203002d00c070000c2a06507254018505c101c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 115310269 1250 115309019 115309031
    0x41815180b0117030c010e0c0901060c050606060c160f0608060109060503011202130213060e0402040501080103060b01050415050901021e0a06090c0504020d0608010501080106060c0b0718170c190504 87
    0x3c21286103015040314032070150b00e440070701c2068a80020341d080c20f150040300e18100aa807070715011590400413490051007517001ca03010074401e01c0e000740605095a10303501210317091106840782024000c4964840c0c5c03e68103900506004899002006550242e800c1c20800da400d450a0001022844148184d0401e90b00e100e070b1850442d03039580010f10039103140c200c06541341d5101c5041c1400340b441500c6070074049400d4030240d641c00d040c2802543c00b1580f0507100c0c164a42c2c80c64803404060b140c084881410004100310220b86045010100310b01010300c1c0e555251100103200029103490140c2020060740d071500e01d49503010b8000040c401c081e45502520210340c2c6059443d01c90304425554025540c858000724a540d20040164402012500c000e0024440d50741c0e1801402d00700c81d81801048006a5000c503140040760840c1c411540180041c600010b20403c00107490120f0480d94102811800f11a241d480340100100f002210602e4100e451003500c400d031000c55020031fa1284200c6c2c0c0600d0f02c40d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 115311519 1250 115310269 115310309
    0x1050c15090a0f060509010506041509051806010f0e07030501050a0605090a0308030921030c0301030b04050f030a0509010f0807020d0f02010b040e03130603060308030114041815180b01 81
    0x40240c10303040f6800300481c021518245031aa005e0202243e5801840d07181c100028414034003400b4100d040f0400040034007025081800850240100600c0203608110940c00101420401c004640c000d1104042210b001410b020f800c0e107030868043c01050416040000601150340c8484007401100c1490404544c0d641c1e001000c00e4000e105940301510039000442002080070010412200140003c15541c0282d910045128820300040c0c03088607003104240014130000d40854207103a0001d000388101c8500c040da108240307145911210700d0000140700810740c1c0c1b209580048021461040368106000304e4500100c00a54034545083c0800800408801c0d20360558000e40c00b031000101c1c0a0030900c04c007051390070440e559071701543c00954840c40c080d0002407041d109219510540340d002462500d564a01000034a460382091001540a81d51f50740116984001811900043e8810302404407000030305890784c0100d510440781064015402150380000444420b0740174151817240011014030b07043d103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 115312769 1250 115311519 115311523
    0x316050304052505010207051212090d0503030a0c11010216060c03200901180609090f0b060a0905040f090b13171c06050111030d271103060601050c1509 67
    0x1a81d0a80b030100103414542c03140700243d10407041907480c2030b0201ca80b4166900188440001d04d00e110400507081002c0342c011005c01741e40100310512008050180f48605a01c9450641e0f0098421403480c50391803100c040c1103600a03101186104042000710b04000c3c16004030441d94800c180f00404466440e4010345130507029034002c0d613000e882281d007003480414a03c0b40703c8840c2d020351b068a021a440d500c80691026228858000341c0c3d46a50b2040e640c603141c2445030f4003030803816581d82035094030782d0452809621040094400b03400b443d074070030705040d00e0700060104607000010200c000310b041100810102c1c6040b08419008101d892480d2922440743c14031108101d440126a1104503002400c40090154105010b2042c01c18aa0030800b29030341d240156078a048000031010213420511071a42c02c41c1c00b42d030121401075600031700102d254000eaa41d4002076130f040d00045450742001c03600950541810030043e580320f00c080c00c1580c83c000301c82c04d60559403104103102580b09440f030b0b00010052001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 115314019 1250 115312769 115312783
    0x6150103020415080a14010501091203050403060507080601110106060203071103010e0105090303070f0e092805010f0611010203070c02090709080a0b04060506030c0a2312010207020114031605030405 87
    0x205054035039040c00403c0024803001d0103407195502d0b1400c110100f1030744204d07070740d1180c100c4805031a400c0c20240790182000fa4040b080c801a02406001c1c00008080f07122405803034846d409655500450b46070110024040d88040d020102051f0724019043c48a02e07000001c480c8000c1d045140302e010700e88000d00090250407104426211075080c0411f10200ea00d001010790700441c400e44031486041c10404d411213048410344e580f142c0c00140d4501203040c45004d0002c00850024883c2104484400c040c0d240081c1c03075003039104064228506d54108280d42e407244841400c00340f103c0081d841c60a007110001c101c07502000c2c010b446900a01c2c0880e00c0319000b009054001c103030a2058560f01031440c108403e810b80b0845050342e8040c00c20300040d445141c08107490680703a01c02000c030710909060100c2c41421503260501c01c1c10b088084030164415540c1c21400001e02c11056001603610229840010700401148007407120080b001e20500c4920058407044245d550700c1c41c03620a07101c1c1c0d99401d00c903281942d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 115315269 1250 115314019 115314029
    0x20f0706141b12010b090f100f14040b0a050c030418051509240a030b09010603062007080a26091209030606090907030c081f0608061501030204 63
    0x21410706001c100c2485550014402d000001c801c8500403450100d240c0107128241d86000001800c2005018803030900002d80285c020181080c1e101e450004089504c00f00030100b00c0000c28155201100041e50018a512481c0c40e2041c12030700f0725252800d42c035003600401940c08280a0003290007612850108240e500501c990341403103401c1060b51504400601003641c07500ca444915005100c624144110054000c10710165280c146003102c02c030307000f041e10b81b56400950001c00340c00b0000201d11880c00703071070145034004000210685903190080c01c5031310041049170070300c00325441501000f01b00c0c8107031491190005c20f426a0382c0070002e0100c45900441e074004480c1c11703104541a000f001e011015600c115107180031101103ca800c0d0301c03d4194040c4420f0f550f895405280090303810b051100590350050145030441d606661241c4e100001c0750b04641080b5034030f520140c0016207032099442e4030303021f05a2802013009000c0c1011720840e221400103081c08912400d45091200c944d110768100c80c0180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 115316519 1250 115315269 115315271
    0x50a0b0c120a03060801060f05061204020609060a0806091803040b18060301150f02070b04030f1104050c0a18051305150a06020f0139050d090f0213110d020f0706 71
    0x142d6402d00c0035009051a0040d803c3d0ba44c60113001080100c6454035050981d00e00030040c6080c100aa05480f400000042c802c0340c0069041c020042a80c4805c005480081030b5919440c290f40391001c24001c1c00d040c0104240c00350401250780261040c0f0101c00c0b5400d6528000c08559208038103200d4001da20751070003110740c00c003030000000180720312016400b84561069640c0c100c4110f0607014102ea42e45000e00811249500802c0104001220b4020744d40398036214000342d01402a030072000604071141101c0080696200180010a060b03001074403084141104503444016030070400440e113400c03429500010855502c074040b03407407010982c41c5031096000040c142001a03807140d000a440340715942c0e0b203c0300c541c02c0c54201d005560b05954581d40998030342d1101c0300060710300201d043c1c3c1c00068110040900404102e1440d04074010301071070080700d00560716004060240c0c0f06100c500d808596080210074030f08054000000c0008085510030f079030401015846042000c0600f0061141d0b020040c406 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 115317769 1250 115316519 115316527
    0x14040501090b160c18050f06031c110114041203090b06010c1a0405030a120605060703030b130f1506030c0f0e060d050117010c021605090c190801030212010204050a0b0c12 75
    0x92079490401551742c050f03100520054135141c1d042c2004040a50344a030303050704012400c401c0000f02a03415201c1843d10b00d04010144d0011500500311a5501d038a084541c0c034040412051102814082c421042c49190802024105864640389004040c1c100da0400003034403400d50500c08101c880030000c074041448003000e4281454030385d81e00d901440045000c5054010022018000d51080404075207000c3c00003072502d0b2155404a0041c0702d82a4030a03804000380d40e52000443c00307441008400703c03200c203001a03403450700d80910b40100c029510503c100750810042c100620f501c840380c00002445818a10341d80354074400043c1c0b0074025120240c49142ca03000000582005901e080b18400c8081c00003040000072141d401ca80b90500600c8000719010300e030004012908284804681c484d061b006a00d007060004d04104071040e6844240c4000030f03aa040041c815850506030301c203802c2c6050740c02146001d01e040c4c042804c0e56440d1082d500901c402251000304c1c1c030383c240451020007141180303e60352 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 115319019 1250 115317769 115317779
    0x2120d03090c06090803041208130303030207050c0a1d040c09090303020d060b0f04031502131e09051b0306150a02070f060807080f06040603050304060f14040501090b160c 75
    0x2840301520035074064030b82c0403000400d80d00070032114060b034410b04040e40c500750409034401c041c2d80b901030040360806030400a2024000160f001e01c000395200b0755015a81d03000e5820003a10f001d044100c654400c0c02c050070200003286d40c100700040450b0f05402c2542803642e035410101421015031b0b00890140c6d00b001d142800301585a801403210802d0f0f24401c119070f581790f40000c407a602031011000e1030070008003c01d01c0411002030000112230440c0c0070162821403141510052144142e1041c60f4039030300c80030040e10000200d15071310054000c82c24200828900006461090380950341c10051045001002c601d82d07845441c8100007130801911420f0395182c25810080d034070461442900c2d0403880030040400c62900c1074181318014072040d5038038101901d6442011140314006000290300c1942d9110010014405002034001070102d41c840701000020550058002c1d03c546018040360442044217200581c2c010980b202901c1c0000c64440d04c80190302101c07914800900c43c09000504103000c0029 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 115320269 1250 115319019 115319021
    0x50a080f070b01230d0615060c03030b01030b03120c03041e0314010e0606040b190b03070e1f051309050a09140303040f0201050306010c0b0a050402030114010b0306010c02120d03 78
    0x81c0300d0720808400e52030342e98805803010030301d03500c048511595100800642e102d14151241c40191405118000b460000f04501c1c081400c0c890340c000400714a6207810103050503010300c030f070348208102030809015101c039a50020380c0f29100000700351801000490509481b0404100b5140500700d00070388201042c000d0711b80550441d0b40f40c40102c40360694124100390040d0180200c845400b66200182005d072561004c10015044164056170082c41c05c00010056081d030414820007810b11b5180955a4200300c04020076550148007424010403000c0901944000b1002d01064003034440d1420f50740f80c012140070001042007652105929904007400d20107403021650007940020721079005105449000c544043d00e9000031613000e41041d941130600e4015500401c019070b4017020524003a80501041e6907400d001c0d64064031001c503041c0d0389204100450800b441604899604840c210718617605d0110130340143d1100030b12007410090f80100000854a664130485c001c00500e4054585c24994988020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 115321519 1250 115320269 115320277
    0x503030d0e070b12010e0406090206030a0510080d021c050c1605040606030b0f01111009050a0209060301060b1602030a08030c0a080f0108100e2805010c170a09050a080f 74
    0x108250044640000b450f111000c104c036048207281d074845102d41e207080c0c0f401209600090050b580f003525940707140016503903803005510400008000181c0340c2454148401d4410f03654215044a5000d0030a4190250700010102420f82e40f42c5600521055441b80450f124001c5924420b0327a44181c3d06064030480a180460003a1001507804000b2160f03510300032000e40d150318140e0360b040070828140c1e82e01544140245503858901000f1074565029909919003250b01101c01500e40750846401202103107000c03440160091001c500034080e0f282030140c504e000348941c103500c1d160501c2e1030280a0854406001d41020150800f030a5520313482d0600340c3e1203440c2d00c00c04106e40064a02000180c3d030313000f152103590686042200802d49807114034020001003210b142285030900c5064104200f4034180443c1003d800380300c074000507010b0302500e005400d44002c8019031043c016100c51440d000c03a447c0e071340103034000610600490149054102203051000c18480508454070004030075a03002c0b40c280c020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 115322769 1250 115321519 115321541
    0x5220309090e01020f0f03090a080c0102090301060b0c0303060d03090807140916020303010b070c03080a172401051c050703060f1208030403031d070303020a060615020715090503030d 80
    0x14400c0d0500b1035070041c03c0b03100d0300741003003400041441111260482c19003d50f80c04480b080440d490f96075503440c0d8840d2030300018030041460f0740003d019901030a0a00500e0010190780e1707081410611084003030790300c03400f000304a2030089400d00c203034005051055207450028400380041d14182c83c1c64010b940e480038200c2910501a00d0290042804001030f107022440968047c6c0c05941183d0906d05180341640c400c0c2c6003502c5102c03403044044086180f5030010710480f145619211020702541d2001642c04e14010002c06400d00c42d502690141d0480c030b40d582c80541c2c401d18000342d4036138030703030041c03d1000030400026007005181c0001c01000a4066102d10246c0719400e55000840e07035038240c00d212a17a090403009002c100d040c004500000c1c0290044580028505202c40703800030000c80d1a860008190700c10350060340040b0490042c00007a100d6140a801020840b6001d144400c102940d00da0062140100e80000079208550b0a40300b008181d014120080a49980b401100b03050b4029182000079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 115324019 1250 115322769 115322771
    0x31719050a030606021609150504021201030303051b0f0f0d0920040c0504140109030b04060618111e04080a1a090105062107050907110f0c010c060522030909 69
    0xc00301325580002800941c820182c95680303441e90408080402819440d41003843c010841c00c0042119602c0c1e001500c0ca210f40c504e003029a9600d5410010305540340600388545458007a12440d08080060703080b68454601e0400c180e640d5070302080c0404a901c1541b0441c501646481201310401215250b50a1a024820796401000482d0300400049810968062011650400c810000c4d04c8954500e40d9004005040044e48a5903944488104240840d0200c40b201d586071018070404041d841040d030071102440381040708a1400180c0142c521807036a1a05001d02d0741015441c0b030654603801c541c0a40b1120741910320125091400a420741944080942e90310034241c0010403010301482154423078a0010700e0044072080b03940c405403180c0d80c2440200130324001c4103804030722519000802c50095500382c0d10040d80503003680130786061402a4a8802242c0c20001003000941c0c4c1c85004010901d401c00e1000820361160201c5440104100200c245000e00d40f10345081407507085164001184c401c890 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 115325269 1250 115324019 115324031
    0x2030906040210031505011107050604030b0a0507030912050702041b02010207021203071703100801020a0e100201090203060604150e01080309010801080a051c02033703060f031719050a03 82
    0x10168184c45c202c4001d9003d0a0403118108a298400e0000d4600070003c1800c0c0c0d0a469110404110301d079015403c107850315104040bc3c46016803039841a282c2c4805940340404c003902d41035407284910010702d000541000004510f04055507070b69400605410f6060100300220742d12410068040c1d0800318040e48107814100501c5880040401100d4903070394000010110310946041c070302d010b504042e00121940c141e007000030941c844244010300c000340c0790792600d9080111001c00c110503001d0a0f8419000c40e410b0440040040e00c1c00203015401000072a07010400f1804940500c0150800394083c250108401000240e24030300400102003a120a90310302c800c41ea2243d401c00e99840e004c2200400507407020640030f002000c1b01c1d004280f60181403041e030345040c4a030383d240741c42c51420b81c80c1c070f080e1a02038225020356100301c0410440c100d180c605060080929011a07400341100e20310010309181400340303020f4044040c40d0100c034081c240202c03141a45101c42c3c0710052042c0c015040c1d41c1c0101386050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 115326519 1250 115325269 115325299
    0xe10031a010503220503070507030f0c0801150e15060f0d06080307110603040c1223010b03030714190602030103060b040614040b03012c150c0f0319020309060402 71
    0x110792207110304d0700f4010079122a011642c200c82c10b0b060003c0c2d82502050011000159052003c003000354021000880204010300f0080c5c240c0742d0903445072101e41c4c5010282c2800305c61011814045406603031840a2070780d240403140103105c035146844c40e4000c20000d00110003c254901900c060074090390700308149600c030314a09589110f10a80684400481e07079030082c80b86010307401503900034890801d690034556900c3d2a14031510b0030301812500e40983c140c10242c03000d00c04080311004c8004030000d0161490b02c501007500c1e40300c0e001e40903140016401d003240841d041082413496200c80d28002d8109903109041220080d00203000031135415051100302e04441c601070085009544842c003500c01e180548408200042820007810b40c0c06548a400c40780e100340517441c1d80d10503180b44080c0040b249c850311055a0900d18a0302c1e10b15100403100c81441071009101b400d550580101d0241c00d580c980300c801003440b940f40314580101420f800001003017210030010510074004c51003030350b000400007851 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 115327769 1250 115326519 115326527
    0x5150702033106020d080a1505040e0d140310120f080307120605010e0a0b09030c03060a09110a0b0301060503041a071205060102120f07020109030b040c03200d0303020a0e10031a01 79
    0x80c0d11a00020b001c0070082842120548d1100d40070f90f41c081c6450b20303015030703600204007540c03411010403c01e504880b5200c1065a0401c02000020030304181c40c52039842c1007165040e00d11514084c1e0181030805042da002044400001c481d21141c01480c02c03510380c580100300520014441c41030020803414a040002c895001d41300034681e00f0401866030400c035060804101054000803a9a0341c54810726400ca07280d620240b002e203000b41c1000d00040f4014455041001915621640300d90180300c01000400c190030590003501d044d16070340d140090b542e46480c102084040b00d094074140070030407110184042690455034010848070b070780c1410700540e590b2400590b00d6403440c41e991418650100318991800c132000c2c0c0107110681c0305041c01059192641c681c1d44044004541c100c8418050031414014400002491040407800c1c5049c0c6da841407100000c030b03400b8080c2120050905802042a446540c010701141e80c41440c00b030180140c44282c0c1c030004010304420b14820b541800c40c214a41c00702e500c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 115329019 1250 115327769 115327783
    0x309072c160201021c0b18060d0803040507031703011a090f06160c030602070c0803040b091003140702071406071707050109170a09050402070515070203310602 70
    0x8200c9200215620030415880e4151144000d8007103550030090011000e1000c6048441c440045100181d0003c14a0070f00010004005c080f00208158808000d115580d030500c1500c8190700c6205181c0780d440b146003451400a039900010490207004103c054502c2c021005541241c07007100842030210091442800d56104801c034141e00844404008202c0741030510060800480c2c0389049003e20700a500c0d030611107141c980003101c4040c0c0000e004802c0c400f03c100804040c000c00c0000c0c0d0f113000d1805880e06940c1c41801207072802404100040111140139511000b01000442117001c40c40c03030701090003522549580250304c460380903502d40c8003150900f08256180e19904c191603104444411440c500160070040e0104c88942d01c1d00c0f81a000540382e00700780000081542101c60319a50030420292030500c090300128062031041c0840000b0400000d1a104c0d0b290709011650000d03180c10310100d0451103040031810b11990048890708100201201c41142c0c50059100658100d803900802ca0304c2d005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 115330269 1250 115329019 115329089
    0x40312140c1e1015090b030c0a06080a1e02090109080c1c05031603021e06070e0409051507020a0201140307090e0a0204030c030b06030607210c050d02030907 69
    0x44000c200c6660110b806070303000590380c0c0c4501154212020f43c800c540940f5441040001200c094203803c008025040c040c066185030308501402c40c0d074901901103810b902d40703441000c1c01c024113100810501030311640305000595803840080300c50306020411002175804043c2283c001556080c0010704c2520229001041503001401c1c07007540003040d60072006e66162644180c4140c0010030010041c0150b01e00210052803090b0054042c0e0101c4201c1126404280200001d580e0410b4040104169111260308414542110001104401d0b070030002e00c0c00141400700420344940e5014098030680004180303041d45d100366600704600e00406441c1700140420f45240c0c000c0b509000d028820360342c0c580040c540c0300000c59001400c0a58076120700c052940d140c2d00503102420314100344425800c040c46079079440b03070035820324085109002001421340351419160b80c4500d0b070750303250600c01c0354810011070700000c480d0303070040d500c9080c140d00b071549a034018800c90706850944948000d51f98600c165110b00301c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 115331519 1250 115330269 115330273
    0x60f18110d0305091e121c02120f0d0912030f0e19030305130b040b010608090318060c0109060203010b09100809060103110d02030d09060305010b07020a051c08040312140c 75
    0x80c4450107000481401c5414041000380d44000c07540030341c8450302d0141c05049140024802d04e143c905002887e946000302d85800c541001c03640c0303048480c01000301c41890441c2c0b1b250903a1850081c0c0404010546000000d0440c1c030b1603490340e21548c1c2d00d0781041100001100d000c1080c642846442503440c80e0315001118650184282100070a00a6101551000300e1843e0a520300140b95903c2c100302d00b048a04482020201e80144115030b44001102e41c030040c6500110310745607e02c1090308070245a0811107100741d00c0003400c030641c00c00c20f4001e4040550300007010364903941c481200c030189400c80803072280213005a24807a0703441d520405401e800340c4104000380950713034215280d05a5542d02031007821f030001780000d02080161010040000c0c00342c42030799840103031410140000c040d82c8040e070001d110040144260809a5038680b096000c440d002c032102541c0c195038812480c03140990500c041d20400000c0340000911100118008040c1c8140d40c40706180c22801088241c60300034480b5907240d40d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 115332769 1250 115331519 115331527
    0x9010f0b090118141807050a1409040507120602120c13121e03020309010801080c062203080a0f020d090f090b130f0603050c030114070c060f18110d0305 67
    0x248401805404106921000414a0348540c0708000220506458505001014510085c1842424803d22000c0c1030304540c00c049452400441d10840004110028442c3da040d0000c0343c1080380401c24500100a085807812584001d41030000082d0000200f00c2101852140043c0c4404142804c5075903030219620500100340c00e000d502c602081260004032821040605503001803040296011f03101d40c07096001b190340d881c020b00010003030b4506030301c1440164080d4408100325506c0c02c0540b080e20030501641000144000c42c1c8030014107080e880540122030004030521010b90042894041408503000c54a001c1c03035011080321004030900c201700c01c05c00008070034007101146410407606120010310040d04180048030b03600898416501c04e1070303510313a60031040080140c18000f0414482c0114000c008010070a03040c48000c0c0c00042c102410000c0029448040041c0742e444481d0180240d0010410f0300c1100440084540c4503c1c4192122506c101c80c4846901d80a54046641c030341c983d0740d0f5818 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 115334019 1250 115332769 115332779
    0x1608100b10050708040302130905010c030908220e07050301081203040314070312050c04050307120b1f080f0705040f15030803070917010501091112060d020402120a0509010f0b0901 79
    0xd0b600f041c40c3c100c1d0502810080000907981d20f0580000c0072000c46000524984549055801c5401c840401c41c181414001401c0c0810440c03801d55000768460001c1c94071401c00d00744294009210f030717005102400c900d1010311155a43c032901541c1070b240c10302c08a4003551030145842400d40021036004001602c40c0c000801c201d5003035030141407428424109407841c0300b401e2031168182d0f0350480d0300003071800700441c1c2004039150400000cdd0051108e041078202407006512070440c010002000e40b15555051700002d03d8031040185c140c0c00809600040c0c07115004a1000386885401c103100b00e41c0300f030b8244807080c0d1021581e44140502c0c815041c0d50000901d10319620107009801c002d20140501c80c200c80b000a110400040030080c43c04413400000d401c0d0305201c180c0f130843d07014811000f4002c00600100000440c40d102080d0401ea0442e0040d6260020740b000501911980c00c5610b8211400014010b18800f40e0304443d01869882e0300030b100e0101c40580f5201200d195412041d1701580b840d00400c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 115335269 1250 115334019 115334027
    0x90803040b0a0302040509042406060c060207140a0c0e06060408030304060b130204090501091401150305091c02011a01030e0c041d0303070c03180b0304231608100b10 73
    0xe0b44800b801d0150501d90342e01c0004540c03000c1281e0694105442c6022130070072a06216081d0004a501e480400c412400c0c0400149050b01c45071005000380d07400908142408a0070300401c840f80e1110040742c40f00700031032401c600d62044601c1540c081840300c00202d03a003450064103550680380d050740114115503840d01c40c400034040903040c15801854004000300c49141500041004d00075119000c24594540807001d0202c07101c00101002080d2030348018420070342205030f040c41034060b40ca0042440c1e00c484c40b00c98105050508480d43d030040c600c0d8400351040d0190824140e09510704c20501e46100f070724005409440d698140c0d5001303504489a1541603142c69442040400b203180000000d900e144006249580c6c41030f00e0f020049116881c4110815a100040b00d010342259000004101d140a02d602c1c1540005080108074040700d0b00c0760704055081c03201401c0844803140445d004660135980800c0c50f001c01b405020303840d00600d40c2841800c84039014000c0580400384c045c0d4121611800125 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 115336519 1250 115335269 115335277
    0x19300b04020910030209070c0b010b0f0715020d06030c06110f030a032003090c090c0405030615040902040f0605100e0d020108040302070e010e07090501030c080f130203030c06060a06090803040b 85
    0x200000f400c0e140440503071540c124070f0f4410029034a1b404244292400d2800d800001648086440141005001c005044440c00d90300002c0d8009a28581d0070504a00c000c082d002d15030003c44040d242c4500001801541c401840c110f0b0307259114031a4002c0402c41c9a611245107007284140ca07407040284c2e0490700d1117036000050000c80d03a00d69031030000d0280300e441038a50040e44c007140030790f11501e1107413594644041e15a4000320051410740c83c0034500340200b516041d004021002ca1502d0444044540d201d68204416440d03004204210443c2d007021544c00038020750240a0040c000031580510b018022114084100b000911846d10754940354011100f116004104600314040c030440001c1d0798940565441c040d0101d080c41d0181445c04c0000141160b8a5034802c5040504115072007140c65040340540350019a481c1006901c0e540b49001e503080d690781d4100080d05480000382c521000c94000c85c03c00e0285008a84603c040360b541d400407206185540144041a0820803081000c0c100620040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 115337769 1250 115336519 115336531
    0x90c0901140a050d0f170a020a11040e01090b070905011419110607091e03032f0703230706050301060305040f0c120308010905100b0919300b040209 65
    0xe500b24036112008607000c0706041d402121091000c0500d281004042d0720410f2402040c142d885007407045140b4000d545d8140c1c0003000e0412201d01404540300c0d1507a800400d0070541c0d010091120490518120407101002c5402000291201c200030a00c0e43c4035698500301248580140d6042036031040c07401c4100b0880a001006202c504854013101000c2405498030501d280d48494194610305070b01c04070080504040745e00d03081b01441d0188000394100340d4611102c118241c401c0c482c2c50400f184c0180c00800141a02582d2082500000c108002e4036482c0c3d0112024001c00710a64510108481d03031081103000e02c0010800074801408a64881d0703200690040c01010980c07158804c90f00c841c0c080000d65008a0074100030464440c080c1a0040259401000440710801240c40d000c3c40380d0318100c1042c090104911130008030ba500d10b07079683e03060f2212200545010981ea85e87c030419550341021020b4400c00c10080d90303000c480c0030030410030b10002080d0003601c4400255586d80c00c10021900040c80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 115339019 1250 115337769 115337779
    0xb0109030206090a05090c0a090506030f0a0509070b2a030c06071b020d0f031d031c03060f0b0307090b04080a06090f050a06050901151d0c04120309030308090c090114 73
    0x41986d5803500c03a0b8061110190702030340e1068200f800038000506600158003501f02041800700c04140b2040050307004501d07210000d080c0d101c00700c6043c01c04403290701549a1903408200607042c0071100d0b40c3e4074101c0780c40d0711101040030f96802120b40c4a00900c00e5a4101d500484001845940100c014104e51104814081841e105070b600040d6000320200094074680500c1c040402016000b00803024501520f00c0d801c400d01003542d0010b6035a10b900f002002c0314001001034802441d0090700310b100980303c33100555541689a6001141c180c204585c2d4134001902e400000561b220310104607004d44900308050014606a5111000540407400c41201c011055400c0e140c0400e0041c000c400050f403061030003003183e041c4003000500303580e610100d890800c0f0800b40100b110b02c00a0407000d500804600d6a05441c0c0e07241c007842c400c06e00995004480b0300e40304d40704010426a01c0300c4040185e034030a441d86e0705d294455090729517031081003050b0540c02c01401001071040801c403228201401d071300100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 115340269 1250 115339019 115339039
    0xd0807061d1002070b0f04231905150105010c210c05060a0b0f040e06040b04020307030b040804150503010b070f05010f02070c051206091e0a240b040b010903020609 72
    0x20320740380019508030b40d084103601084800130054040a840d42100c40004100c0103424140c54011507039119012042040921600c8400120400d02c20a9a103081400d40000c00d405207042081e150006604051942e060480c00401c11350302602c04545495046001c0c00c03000d03890072020102c0ca03150441e080d02030044541d010000210204034440c820001e2041c0031a05c44040014170408015165082c0c1c8654282691200f00d198001a42d42d88142c0048186c1e0440e1503a001203030070103c6075000904415070800412080c800c164006100712035101c2c509002e030358010802103445000a0003038001c80e080401c241c2c00401d000c01c490701e85041c000c1c0000604488a10b01d280202e03449240200c40030b10013100d042080c3d2821a9940c100c1d00d2002001d44090b00e40f40d18103580310114200d50b01e80c03501d44005d521005c4001000000241c0ba0300044545001d15103480202e0000e003109008860103040c20f1340b20f441400c2c28020b1040105041e103400c01c0c101d065600b008602d80141a120703810121030f01d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 115341519 1250 115340269 115340321
    0x110705060c011409030a14030406060807062102030f0c0702010306090f091b14011107080109111c0308070309050c13090203060c0f030c0d0209040e0f0106050d080706 73
    0x900030014041d48900000e03100301a02d50860110034000d04091a5030800c1c0304103d116900162010a00103141c2810340c2e483c0c0d07075490305074014107403600408083c4c403c82d44c004c074125404c01410100c01c0e0340180440050f800d203501c00c0c016440100d5111a040c461100800c82501d100710140c2181c40c4141800300d1119220301d803c200301c038400c503510343c60107032103142800a2105440e01c00c3e01c0c5007108813083c05500e08002c4140d0358028285e2071541000b120003981108005d003800604040c0c10300c40001d1081800d5804c00380d0010011a0b000c074852030040507481194072841034448078039a49515220b0b002c2c2e407810803d1f001061b0000b4141da0074054039001e41c1940c2d5602c03c28900e5601503800c00503040307105006243c5800c02c014403001c41c2d52400c00c00c02d460101a0000e80707034015050902e0345d40d10b15407080c02c003000c0e0241601603a041403c14001c0745400d1004548203154027404070080048a40d203608101d200c2d0b00440d03016000e802c00b00201400b258240e044500946211707200205100052 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 115342769 1250 115341519 115341529
    0x915040503092b050c1018050f12030a0801090b040b01090528030c03060e0303010b03060f0f03031206120a0f02060c0c090115030605060306030d18170a0b0a05040f03110705 76
    0x8040444d40f540100020041902c1e0032083d01e402d0078814640940c3c55020060348031601486801114490080b01d803142c0c805548200120100172001c1d07003a683c83e86104500940720a00038043c20b90141c1c01c10300c10341714608181c883e60300c6043e0305030750741c80c070700d926000c14001c100142245041d01841002c02080c2502a0349000c41c00071031194136504017051441c10506e0032520000030041c41c9400400040011210010a40382c110004a44a02c132162103440050150720380c803036185415001c08601003040302131121b00503201e4002980c0c041c0c404040050322940342c0743d00d18402403042d485000d9000142c144800607001d401d802e60115985180548001003602109a01ca84001c203d00224001c8295045c0a64001000d0942c1c00a055040c81c9000a4642e6204c0090b0340400c500840d0040c6ca003003000503907100600081c015075183e00f1005070440d8441c44041d005540140244003c501c50201e588141441540c1210641c1b030b0050140e07404548561a800040b00b0921076000045810758034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 115344019 1250 115342769 115342849
    0x20f040906180f0b07030e0a0803070512010602010506120c0607060203040f0206030f07090801060f05090901060e0702150115090b030a091e050d08010302010906050f190305091504050309 82
    0xd558014400b0645182c446540c03030300284040c0c209800d107c107090988000040c0b006106a0001107540c40f641c07002c0c0202c415016184040c03940c9000300c030000810700d8042d40058006e48003a11500302c5180018940c95036456000151394100c84104001c1000c03a00c02d0340916000782c440c4400301c6107036040340c0015102c1d070420380c0c2c080d03101e507410400d01c8400d0f074122078400020045080280162450702c03041c0c007020a03643c81554020541100000d001c2c52081d80010080c00c49400700603500e05210030002d41d02e52544685a0941036080008195044207941b601c87c09a0305550700d208041c2020000c504903000a4401500c55455290000000721049072841000000c00c02c01007a0303041c1410514a42a144107d50b41800b41c9000140051b0768040c004000b82d41450500c035035681c0d10003844000902c130b805610f50414400400100c8003e07415000f19000306888402c8461904242c6000e045078141614010081d900820080e52107050040d00034510100840031000b14a012242e1350f49040c031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 115345269 1250 115344019 115344023
    0x803220204020a08060111060f0c0702061e0c010c03020c121b06011d0c070b180705060d380f040f020313020102070b0a08010e0405030702030d03020a0e0d020f04090618 74
    0x40c070400c550355901c14482500784100038010300c0141002603054140c0c1d0405000c40051210004001c03055451724001c49100c22803a00c41c00e41c6404191141d53b1190f084811620000c1d4200903907402918072034002e0390032030104400504007240c020004a40c0c140d000d03030862111028803200c2e45042c0e502c00d2101c2402881c18040c4000070940f0f240c4584035041000307040c1010310320b0a1140c10003280e140704100e03610003440e480580030100080c1c0c581e454100c481d40041d41c0b01d070300001c0b100403c280d15040003550141c00c0b607210507132602c00d0301000c2c40740c100c0f1007108e09100a88100101c0d240ba0650a482114501400004594044690890a170380c0115402512181d00150314401c41d6410003180c0001e11404111a04204400300001c1c10030324181b15542e404210000801c00303004080c0100c40c0c68950040440b10701c501c203440c02602030f401a48608010468a01c00c121b1031f0305122403407204042d80109440c94880c0c03104100401054141000d8800984d200d42603050380341c0c3d007062004031074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 115346519 1250 115345269 115345277
    0x1706040615020f100207231c020f010b01020601080303040f1b0303021e060105150f190c031106010b0d1509022d040f0302220c030c0215040803220204020a 68
    0x20044001c1d51501e207090b810b181e8468170402820002c5207501642405200a00c1040b0014044200107a450044048207202c200c2c418084c84880b995000075244d0600da070b030b4000a201001221005984407082441209800d130410400a40051403070b0301981c0100d8811400d0845840a060032403424041d1a00301700e0141e88805c01020307001c4119505d0065000001c2c2c01401d0542c10035012035401c2c407040c1d140586028011561800f866007840a072406045006421040d181c0503a000903c001800e136016000b042801d0201d0305507000100b16141600c004a04052600740c1c2850b1840003480c2600304000105c015140c00300d041030440c001843c00002c01c041d205103081c00010030100c1c0740c4003100d501c80301c2c03502041700b041903000c3e0444000450380c0440b03a55042001c06e20065400c0c0c152041c0349100e441c6804120100190550f1200f0090382440c0d00300d500c4400d0b03a011220740c658054a0203411b600e410300c0050301e02c1800029603031740d840304075000c032111a52300c1d07021a060f600042d0004c4089 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 115347769 1250 115346519 115346533
    0x51905030f0a0506010f0320070b040c0603020f03070c0311121801020705030703060b030304090f06090b0d03080a0c0c0b0108010c081006080703020a0c080d06180c170604061502 78
    0x514016000a4201c002c0c2030301042941854800a04034140000c0c85805041c0c0369030404d424101c0341040788a2000300d68441d41d80e107483c50314142e440100100c9048640d40882e020104449103e4403d0311460447c081c0c039286103498000d0240e4031810203683c01c0301040300baa014041411418480c0604d447d020b0000e25882d40348003680008145200e651a50441d401032100304a86d5400203209412a6003140001807071070741c01c9001c41e043d03219035080119181e080c480444400b284583c40f4808848044104001a940b18010804a0310032050082e00080e04840481c41d4560150300c5507100d0005410039070511030041d03035903101c03070042684441600e940d034401b4641d80d9601300000c140d001158510307140b680c6040840c00703440541c01130301c3c040c00c05a0100300c041c88640107500340c03540300d60803594068542e0806c8151001070b0541d07002da27001800004482c014840a6802a60f80d80340f0b00e0b884002c800700035510380c1c10000ca0020480d42e8001d465a000254ad00c10382c17528003064011950103800d00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 115349019 1250 115347769 115347781
    0x6021603020d030e1f0e0f03190806300d02030c070e07020604080309160312030606050f12060303191d031c08040303060509010b072306040f0305190503 67
    0x8042d250000c0c1d02c28141050340c48450f52001113801c502d1303403a8845040100303004040d914001441110110303105481862600700c2c140c9000806844602600c400c90a48001e034000220340400301a20001c2e04414070584030500c685010b00f010912107081c0c0c4030582d040101e00c000034600020380c01649c000d40c0000800c586034020a0100780041c1803665000d0324071381000c4070005c2d0b85005c0108050f020100120210300039110a00c421070311402c5c840d50b0002c0040d2030f07083c4074042e00030440608001c03a1614000143c40303401401501d2034060324104031410124042d8180050010040c24103038140002c200380607000500c1e42c14000441c00c25603502104510700250380d0226000003141510a921920082010880c200c1c04035140b602c4a141c9030200e611945825009040706421140d407203d940400841c0101c000406404158002c080148061454000011140344124152200b130340250001501181000a1180145100380341051415070a41240c058031071010004900085000041c0b181e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 115350269 1250 115349019 115349023
    0x504050306010b03010302010509060d060f060807110c010f1805060304080901020d0203090a14060d051504180203060c0a17010303090302090903161e0b01090204060f08040c050d06090602160302 85
    0x2c0501011009140b0315411500060b0241c040c0c901c0b0684180c8001a0b6808802d40c1600074500904040c04290540b50300d424003e000400c0840e071000020b22001000d4a9485000501409905040c1c461080103002c140e003c5564000365060072180d110002d0340010b964698a0007184a54068840151106a448002030414180c00c500c0d40441d481170056940d20b41d01d022211080b250707150000c01010903030602042c09401005118a0880c0c5080101f01c0d8600300302144120210044400300401c945580c018000c0703082007003000e034142e844032001800403602113000784208003803802c090070142d00103108076a044100742c004400203038111104008501b4200e050a4020101c00051400c145201d103a440141031106c0020f0112010b02081d00030f188801e9000302e09894001d11800c001e0b6855821140c003030342c05441100006069448000c2215200da01024001ea5215094240440c50202005044040603005940f1541c1c0e8405403400100c051000303200c0444da2000c400d104100c1814040c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 115351519 1250 115350269 115350271
    0xf07060b1801270e010b040605100c0b060301110a030c080604060803070b0403050903010e1c143411012c130f0903080108100c0c020f010c120504050306 67
    0x40c0202807052031100825080c1c0c020505407160821030040c04002c6907000c286260320b06112040403441c0140c002080312041d004800e4100301500e013800029075610900002501c07004260b000034011b0400d9000180360807800b43c0d04594003e0012440741024a00d04c11544c0c842d64041000c20342d20401c1101d180e40000c441507200404071810480c59150102c403075184d00c91044000d01c040460000a0101401001515208400a4020048145080c16096482d030046402da14620340811440a10b6417154150040005403807503101d0410200b00c0c3e075044907242c00100c2100350072a403540302541c0c01d0026006058039001c0e81480c40c013031015a0014004004c681d0710040b5000040d10341c2c0840492071243d4520440c810b66005036905c14991840004110250b044042242012045030a00d81e0159040d070503a0303520000d4a42e032a016589900c103c44d6143c1f602d10104446c0c030003041c09840d03d441d000c104d01c00181010303150040a070f51101122040d8105050100741d0228003482281410006a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 115352769 1250 115351519 115351541
    0x509090303150d030c0f020a0e09010606090e04030e12151005010809120405010f0c02040903020a0b090c01021c0c1202070f09090803040b040213020406030b040507020604020d12030b060f0706 84
    0x80e0f559604640c60082030000d030358002400300855141c0800841d15a00500d000410749000d0007003050401c2c0020502800d2940304890028015040200d00100089200344c003540e815101d0f080540e071282c0600135040c0d10706030002003070b00074003401c0040540301e000118407032440341c0c500d01101810f00d0f0001d00988005050884c003584105031002c40c414003401180c0a40d8804d00344809151140d041c00c8441c1d46219000075042400c00d810f0404068000601442040c403132400c4ea0f038113a0b203040c80c071645c45d00300004980c0180d2018501d0500d407050065504100c040a01e4452003d804c2c03510b41201889000c004100107074080030003001041c81c40c2102e1006420040b806000011f000d0700c6801c5240400392000d00b031441d00c480800c01715642c181d8512039001c40d04000703540b59540c40c140030f0003c2c01c00224007030041d414100004c072481d20106245200385d074002c01c0f01c0000c2080da19030950624500e8044000c0c1640c1c0e00070b450f000d50302c00c8080c1201254072071303029594082c9440c1040c00d5412100c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 115354019 1250 115352769 115352779
    0x1203020102120f240a1d0f1e010303030207020d2112090c050f18040f020a0515030a0906060512060405120f1912060b030a1a060a0810050909030315 65
    0x1409500c9103944a1001e0180d0450440d03400c0c1009900060111290b55002c0e032841386c81d4030641102c1090188100b886100c4138460141907688481482101900d500e0908409500c51001400000c1c00390b070203004070b00d0025002d000c0b6141c1c0b81c0e0f6030610544a0032003001c802c5080c0409a05550380c4489608101071600505210716141070395041048a902d008182c42002e078060740c42d050741c60f4030364903002401406035010b5241c2003500308001001c1070060240c0c055007402c4408034880c01c0400d500c00c0ca0b004d40600581c9142d5841740302a0040c40d140c0c1040f510291103245c006903564941e135a90800c1091400078000c07604003490100c0c074210ba4201c5107421030310103200e5116400140c6061300c1c000e101400041d909142c085108440c000c1404030303450080c03440d004010603241407102c060b40c46079000c0c013403c01c405081001c07848445403090125030340c452020400030307050901c501100b542203088001e180c46910707140d40000d080030008a900c0886984040304210a501c0880c42c0316411800c1918 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 115355269 1250 115354019 115354021
    0x10b03011a220207030f021b01080a0c0309020405090708010b09070915030219050901030b041a0402090307050904080c16050112110d0507021b0414060f0a1203020102120f 75
    0x560a407003880000441842000ca04400042d4042400e01c41c00c06100792103800c550340c00e03403032602615030000b462070100144215001c0e07040e85500503039800502c0c0d50503100c0c03403c640d0f00c043d02400501285041c400405423038503640001a111400398600a9500801034610305040c84403060031228040b42e0944101e4186046c0441140c00150f80320035203600901140fa0070442d41006d402a00c52600311591620700f0f005403504581d4000050914104d00366410301812100d0070030003007510042a90b0b10000054140b824820b231601c0d90080c4038085025081c0c80c031496540c00001c08454040b82c050361401000110a40b0703040c4c1c00d114107210040e200b581c4c00f07815420480000e00307502e82555488580345d59001c151407588604010342c3c21364000508280100d2030304140003034940c0000d000200c15040d4001b000d02151400e170041c14042482085000c000d65181d4080052242d044003155401511030000841d8411083c200c520215009400140e81c41d5188500040c6002c001000b5000a10006d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 115356519 1250 115355269 115355291
    0x6020d0507020f09041406041a01050d030e040e0109080d050703060b0c0304051306032001020f03040b0715020c07120b01060f0804030c02030118030804140609070e091207060b03010b0301 82
    0xc865640f40410996042d1100c1d0358924000315451314564100703480744a040c0801c41048444482ca00d000f441c80c00700e0079041e903170b51418031248801101004010445407295040c441c28158807040c0c042e80150000b04506e881c40d03ca4203205c1d40a90856803045032541f08120405401d030162000404001990900c1e107000950202d4490186009e4648a4081c400704658a6000c54202c0d0002d1070700b10400e044032401650b0070103000842a100d25001d0b0040541c045e010308404000da4040f20f00b0f032071041e40307004120360b1046920340c902c41880300c03101d40c00d110705030144134104403241c054402551700c0c00f1101421704010080c01b00c16408102080761810390340c00c206a00200c0203402540c103041150341e0081502c002805003210b181c1642030045000304840078150b008090b00e014900508520210101003a0300940b40c0104079003180d01948011030420410440380c03206503104024600f500e03488040b82d22403076000d5010b61020fa40c40c5031a0b0b44294135501d000c1c0b08441f030b080412002003024070708030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 115357769 1250 115356519 115356529
    0xe090a120305060607120302090f090601020a0201050d06080601270504020a0506130504020a0201020d060905130f14010207060c030e01090209010b13090e03031f0e0a02030705090301060f06020d050702 88
    0xa0100034101602c80c030200d001520b41d0b0040e510311a52040e4007100d2031541440c010b000b5000302c00d19510907141000d800400e8104440a1030080c081a40a4045d80317501d60015525a440308002c0c0380641d07500c0a00050f070344414000e10b406800303004014808042e2a6107003040b142c0e8844020110146054244001655075403880c2c0304035081900c0741516040702184c04000b90310340e6407040e50001e00000313600e80314640c194020302004114202c10400182c4448200b01111002c980c40b03903078a070000c001c20000c05c2240d551014800d1240d04140d1603040c00242c818266000120100c4609840d40f001545854050083d00c1012603c01c0082118007000c2d000200b21031810700c1003c00c100400074801c210b4180321310115000d044c48500038080395400d804083e40c0c030381c000c8603104140054158699840ca074500c6214080b40d21050b5a001507850303410b890002517202808400601100700a03404564500707000d12002002408034400040c3e00c0c0c06006800c000fa000402d8041080410500d001a654 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 115359019 1250 115357769 115357793
    0x8011d0c18010c0c0605030a060e0c0706020705070f080717060f04081e07260307080705032e0e0601050408070b0703091208031e04050607080402060409090c0e090a 72
    0x141690540030381c15800041e145016103074009007803020360001c081452a000030045020704d108907803c0211941d14a04c801c010441521b070701040b82070403c01074010540e1a00905510350060064805056440c2d0426111030701d075074000d80042d0000f500802100c0407c40c403c151803294078016101a1a1105007000c0140e0020320003005140046980e205c2c3c00c903116025400c190368002601d50b58481400d00f120484841c8140003944803150a82280c0b88000390700340e03030061b401901d42d045903844200c0f00b03466a1304000c100303441c4462003a00c5075804d40d40307581e05031221b0308260460900d50703420480360001c0110020034040c1407260800003007140b05400912102245c0101d2240b9440307100700e160840341510300d070340311800c8030844034a101c0500100360011070055803018260030802d01620003080140f8411600609560007010011344103602800b0301c942e102d44002c0ca00c0d49083d444000240859035030070302c20740341c0304440d0500303000e480040114242c1007101c490041908450a030b99105480e44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 115360269 1250 115359019 115359037
    0x9021f0e0909031e190f120f020909160e0406050f21060c040603060609210213020307050c06090316140c03010618051008280503030708011d0c 63
    0x6141000110b5112081c0b00756240d051604200b03112101d1032030111001034000407281030501c03091801a480860084090941c01c43c0c10f40c9566890030200c1c18260010260341683d841c2c00da80070842240590b540d00444da1040c2c450318809001c2c000040802008010000c80301c9000e10b241110501c00da40d1780d8401c80521b05000c5500501c00d0714181c41b00c420703019000072041d41c41e2252070140500b4280c0100034105807a8159002c10090b0360345d02c4112161166449116170903210001c1507040c81f6040030780c3c540d03110700143c004c0e144e40490883d60001c90344202c0e5440002580403a18001000050042c1504501c00c0da00450801e1030048501030240c4c070192004240000644035120b501a041c07010540c1c1c04401402004020340e42c910f0b607152505280c5201e24250724243c000b030098041c0c0800d11060b190204000d00c0410006032407210745042c1131207a8405442c1810006e40094400c00c021032007003c590f900c0c41e100d5498802e07007001490036040c050b0042d102c0041000213007a64a01038a10400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 115361519 1250 115360269 115360279
    0xb040905030f070804051c15020f0a050927100e06131d0609010203010906150215060607020d051014070f0e0a080102070501051501020102070206070b06060f0d09021f0e 74
    0xb28501c1c001c1000e20582d07214a400c441c0410395000395030080c1801e1f50f81607028005540940386802503040407446860300c42c420441080c401443d416103e10081c02603a54090040049140404491408110a10b1181032585100301c104107140140311300709030080c0780b0000b400703109040510000300c2c542c04000800300c500390344950640307801c042c0c1d000e40702d10040c0b800152140c1781401c0d03804038041d6000340100c44106007000b400080360000c40741200709481d684e501801070200c1c800a000d20700c0d42c01402091344180c05011070741c050780c0e400016000700c5102d88001d02401c64289010810f50310041c0740200c05650700340400442c580c001c180c401202a4501c0d22028216034900000c4070900182c001c44013561005c9151410488150311803030203400f041807044c10f07215074840120b0a0388900c070f0009410220a010f980000360b0590f0106030824801041c0500700b0104469041c04e94120140c0d100310151645089015400c01144185100200c0c458010030005103000180030301d01ca0745c840a0040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 115362769 1250 115361519 115361527
    0x10210020c030702090109090c05010e060901080907090216050111040f03080705120705030a03050c031003061107051501061b0c05060a14040f0302030f060106170702070f06030f0b040905030f 84
    0x107440240308580640c0c0e4010002d0700700d941c41c0c0c90f000004204154040f01d0310704504001080d298044d000d500c0c590342000300b00d40e2802030084011100c555003c3e01c152014030840101050391080c900241800454620407100c5100380c40c00c0090a441209110b450910710800c41880f20907400c40d40603080d0303030300240030a61f10300080c900b0074074085561154200f08040858440c0030094040010700c8950590740d020310407504c42c40780180c0c051000b42e841a52070448000100b00045858105d046e44221183d410303410b00c1c0345621264100031000ca00c10342050003000040c0003858000c1c0401540c41031141082c0858500c80e41c5215200901e03028071391042c04045174101c0690b1055a6452046950f9411551266074840060341c8510307090000301e00c0380c0a402c0c008100c480e00022828106c440540e16100c400350054031010310850040c040034214002c90101181c030b01900040c180081405030790004e032002015006000b1200600c901510a60070702507000701048000040e0784034405151a11561 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 115364019 1250 115362769 115362787
    0x14150a15031209030c09020301080c010201142706270607020a02010309060207060e010b0a05010206101205030415080f060402090d02130902030a0f03030e160e04020607140f0d0e01021002 82
    0xc40c11013540010b01c040030b07250300407600c4071994016504882c40030040b5604e11007580016402da9215454070010380e192240040c0510310b800d075890846801040c03000c0264105484c00e542014022540701100c036280c103000418010040c400c01c07260005d0400a4816070405102c020f4580c1c0b05410041e040584036900c03002800340f00e80c101e40605502960400031640b489400e0b90182200a11a501c0b800344c0c0000002c10f540040f4900e44103c00020b6020300a506040490a405c0320300c0205481034401404042038000d45038200242d4141c0540321103050b0311703000c41081081c42000340000d00982c01030008600c10345402002078a050b82c11034114051010500703040c40140044078000c4c0d850311610a00b001400b00854000004600a9a007400f010070080d002c0ba079502404000c40c0754a8946100803c166410b8000341500a44010080c514200260311001c80d04c98410014241ca40c110361110f141c0c0800070405070301410b02c0f80c10a603c01140000c0040d48494844c01030190fa59000681c54078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 115365269 1250 115364019 115364027
    0x60807021c170a0e120f07060e07030b0a02041401140a03050901150603090507090908030a09061d1c090602030409020903031b0d09080303040803070c02040914150a150312 75
    0x2440c801c5103120002c42c80c1c92180e1401404100e40c51500c9805480c894402120750302e41200ea070b02c900203405520f005219900c41c4010b000300301c00388c04e45001c2c0c0c90001c0700040c0700d2428140039103101280507031103e042c041c080401c1414600d0b45410b100e441300d2200800500d110940300842158140000d0a50318000100d0160a144060599951501344040f0301c090b01a4008031402d40600111a1120b0701c4034150422501760f841c01520200301400090340d400703801d4204203500351040901041244252000b4a4000f4161050344c45580044100c08900300200000450400e20391505213150792030114084d40f139128500a0001054000030b8200b8a5141081120480c0400076400e542d21000e0924050f110026014003000251406c0c0000640304400420340340201d80210845240d030710703401d100f51019058404101d0b08030f03071240d0890000c40c81e0191109244404400079019411106121408501000b000b0044152800441a100002e90b0040b4000e803a800603c4580440c00035005031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 115366519 1250 115365269 115365287
    0x15080a0905031b060a0e03070b0403141803010b010314180703050a08091203090a09052a0405040c02070e041403190203040512060402090a0b060408010e0c0a060807021c 74
    0x50a28070001980390802407401244403056283d000640751117440d000040d00a466440242444a50003070042102080201100d036030401c0c402d04041d059201d010010301e03440d4014a250004048c2c86c0c48010805007028020024803001c04d1a0070000300c5142d503e8491004030242001a2501404041005800041010801031500181152003d201d01c4c5000041e941c04168214025486480403000380783c000420303101815001414104100c0c02c001c2040e000b40710003000480310010020019490094031600f84a60b8409070340420390f52800c1c9010712064400901510085502c004410000c00700d01240c01e03074100e17901c130410484c103000c0d81008528501403908181030380120460355000380c5800000900448a05031440c0717041c8034180c00d90030740b180400c88019400c40d001d0303400242c40510342c0d4000c2400020061469040c2600c8558190858210100c50b11165208510203902440c248a40c00300a0410341b400c07018500e13025000035116020008546052448403110103241c5000340104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 115367769 1250 115366519 115366523
    0x6030503030c09010929090d0618050d051305121203010e1006050315040b0102070801020403051b030a02030a03030c0201020421060c09050d031206030203060c0309100615080a09 78
    0x2607880e410a82d00050080d40035048003800714807a00800190341c50f0400c0c0c10a17001581143c94a1346500100d64003085034015072229500000d49025000016820321401d000400d40c000031000d0f481c140c1ca400d40c5010940e4030040b0500005000c40e100915201c00140142c1300b040c1c07506403001003c40702d29842c0079071403801c5004000e0080000310750b41c0d640e0720701c551040c0820946200b40a581e50010b950903c0151b40031103c01c0700c001320350301042c14150810140d4110620445290503034030100c40c0c1c22608250001c03642c903044500141d07400d803c501040f5504070411000740045101642c002583c6034018103005092544034240445200d0003941518020a25600c620f000004200c000c41c0320a0011602191001d1900140c580658428401d0300280e400240c6949405481c1c0e40b000c2d43c603c1c0030001440d102ca900c80a001c40107807024000e10740500b51003103030142ca03030800c1541e550801d0391071031404803614948001048422581841d00e82901e0450800800e00d440d055012000b41a1602c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 115369019 1250 115367769 115367773
    0xc030115181d070324171501140f04020414090c070204152301020618010e010c03060512010b06160206162d080405040e1603050d0323011503060305 65
    0x144030100b15466031000e100d024640c0c0c1c04c1040301848210200c002600700c505034480d80d42d80c48207100140704200098030348502c1408842c068100c0d00c00c40c0304002403d8101656402d100000c00116003400d8005c6040c03840101c41c00d50901d4140000030200110f8920160f208a02ca00045518052800304442c91103402400c01d000c0c1010301000740e003811701c1034030a2072503400648182e00310020340c40030b40d108641e0b8140e0103800c00340c5504408140c41000141036140c40d541c2c031040c94002a20910444040c8000303514081640d03441c1ca010003030840c840894840381641009000c2d80c081d034543c0d048411855403a40001c2d00028540007042413030180000404404c118042031005000843d074074806821100d514203290f0320485003118004045407200100011024441404607192982045d0102c000f600203c41000e0401d520750055a030165200380c1b05074201d109843c080e5070707140c012582c02c0349100302c08015408804840d403000203014804c5004064890b4807051006210750000402141c011701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 115370269 1250 115369019 115369049
    0xc12040b07320c01080a0e07090209010318050706080903030702120a0318030903150c0503040f0201172805070f0e0a05040c1701050d02030a0b1b040303080f0c03011518 74
    0x101d8150f6a400e804003082c0805c00d10000034601406502031b88a00220b51800b0b80515842e10900350007a400601c1d90030b05041d00c0f40c3c01030405640c402c0d400b031030040c01b0307600420300c05103021800f90801502034005440c42e0130410400003166000121060805500814640d5039150103004038020000c0410b00e8000f410101c03c01c4091550001d04007041d28061010034645802d0541c05200b1103540800c0b01020400a000050211f1400420b00c0302c15401814203200c03140d00e4105182c580041140c1801e02c0b61300e10312542541218081505d0b05486400d0307010846030501800150a6060b1005080d041142000c1c910482d501d42d1302e140d03001448064018004001400310103480300107a01804042c0d28003e9000107594909a000c0150542d0003030090008034a9a85501c208004001c128540740c01420812500009080c001400290b02940e10254642800e0300f0141c0346080140141c03d84400c03c1c0010300c0320104080003030b1100c00303490070140d11400e140c01c4030111148c40c603070000c03400428281c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 115371519 1250 115370269 115370363
    0xe15040303050a0206162109230c060403170901092105011b0813060b03030a08070e0102070614180405041101090902180d030201090204110c12040b07 66
    0x6020b001800c1d25074080d514141c3d15204500d9003010000b1142c00011030070240310100308100c0e4803001030341f20302142c0412541100d0311228031141081d100300300800f280315464403407108240709501544500f250010711740381c6103031589c4d0000301700300070600315007440040e6401d4203a0103510780c10010542d1000e41044030709074141048a48070700440540d501c0d42007110705218514a0303003060034032200c1d41c0c0301c48903c0d407a580160415003e0001d81202d040c2d680706103c00d1556420405016041015a1303518064900003200070054034850b40c049040d980124000e2003059004108146d440440480c020340b81d184034017440d00c402d80c0380c02c140e681140c40d040030300003030051645080201c0300003030f20340480041d0346244403001c82c81400b00d280244806154049524a0b20305407482da114082e1001250340701c800d4001500f16021030744a21141c4000040310704075101e0030b00c003600c0c41011182505040614050390340c211172241d96801045000a466040c014801c40c00c5a031080301c0d140742d155100003401d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 115372769 1250 115371519 115371527
    0x18061d031c11030708120907031a07090504050f070513030209010f0801050f070504060c06020d0507080402101d09100f030506071709030904050a061805040b160503070e15040303 78
    0x400c076240019904058088001c00000110351050340d02c0310441d0314010840074030400c56200034104202d0b5000307403e07000000c114204c5107003904102080c00348400341000314024203103d5440d4407075406507040100300704c2200d0082450590107140d03420829910705d142061500c0042c3e294000030340c4848800000710320606203c0104054a107070200070821502c0380d40500000203030441322100041d400b0081400030510800c21260f46d0703446004058180b03044c074114107060341c80454940c0c0002e500a02004298a0202806104001e042c00e00b16410701003417010400d850946000d56008030500800b00d15090301c045c00400007000c15042c949030054491134881c1e288c0e8010b40b080c000180d0806000c003004d0664600d0140240301c1ca00080d4600051181071101074800188107640c0d1550f11039000500301c4c0c4058645035801c2d101c0c85c0024940c074191906440541c4040c00721507940c40503008051aa6402608a80d08640a800d105c400d6603a03580011b03000c2901d880350010a0b80c0082000000c060300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 115374019 1250 115372769 115372813
    0xc050c010507020f06130c1a090f0108010f0603051017030c100b09130302250302030609030702010801120f0204150302090f040c0b0903160b0306010f18061d03 70
    0x4040001d01c5140c4400200302d0340c0d112a0303490460079402c14004a40744002c2642c01c80340b0700d441010035075032890707448404c10a0090080d500fa402c00400181c044241c1c90042103503000d04000742403c4007203506100c0e196010b80614090320083c5a40d6a02007a0000308840080c1c0c020800d81406480010050a22076140e400407000c011079803042e0040c0300040140e5018803d4141c402401904c000c0e42d03544a0b01c1c6004140e0503040d41940207016010006030805100561901b00071804180c00d545036205051034288010b01a143c0ea410611a2000603a8050b0341541158403440c08030703038192602e0a04139001c142c80c0d00e000754850304c2c004003006130129030440a42201d001300d480700c01550710034181c0c0c0200e840c12280180440300c0d2030740a02c005107003140500444e030000380807203e1000d03440004000460258104d0020120040300304010f540e840034440440c00030601c3c09405405443c041880c00400710300528080c40403a503142e10743c2c8081102040607201005045440310020320816001c04e00c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 115375269 1250 115374019 115374037
    0x1505040312093b060103090b040b070f02073c1d06060313061a090a0203010801150b121918021e0303220b0c0c010e040b1c0201050903010c05 62
    0x240e0040c250b0010150b0740040002402c0500c070f114801e281c1102800d41061008000e1814140c0e0f84d071500000c85c260301c440600c42e921680c5110b900303003400040588a2241d0300d102c80115407101005100d068400d016040c85117201541d8101c1501070b0035000c2452110a420481c40e0455a510020312458884007422100031603440305123aa03181c41c2c06001d054802184c005142060060035240080e40a9000f10071000020b45680a90b811460002d041003105035003c0d0312043c1c0101c0180801d130828400d00c1036004103141401021031500e50210710500420440c04c07a2804001c0001d0103012030b001644003800038503002004140c0c0c40c504a14880343c0f403448181c0c002c2144c100d451010888a114018002d400140154280304000c441c90300c0710742440440440c1c40040a100250b1050a08064511680d45901411042201c1c6000402902c0d582d030b43d40d84251f0a094901ca02600ca200d2410007500042c5d40f8009200003d000590b0b16208109401e9055840c0407006d0741e4582d03008002d800303284 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 115376519 1250 115375269 115375289
    0xd0c020f0109030302060f0a150603090605010801090f1515080319020115170c100206010305010c020303060a030831090b0a151112030103140f06090601150504031209 73
    0x100100300456a442c183c1c000100076a00030000700b03040090004210347c0c4500682004540c801c8841c180810701066940b0040100c0d48401030281000184d028442c09000540f008004039141502c590100300b0f040314001d050038280001040c07240100d5044000b00c6401114541c8010359512b4510350f13641d001c1340b141d90890b203410503001c4a061044c020b1a004070000c00001002d90f0a05525032f02c5800c51030311646203485002821401500d0b51150b1480003425030700501050340c991300301039080d07681a071004c0341150010010084d940e80c0b400b07072a40a0341c0d003041e001c42d00c03461804008106414034030b81c511001c000c2c0c549422030303d50070b140f4004180c03014998140106c2442c0403c1c04141c1c00a4021071406066070141102145c0c400e545d0361080d0080201181e41a03200707003150310b0481d4801c0c0c0040c1c03452448482c54002c440e60400401e418072481100501882c90070f52980781e11418107004013088240560341c80503030703030b0b20500541d4065038201c80c4104103007114103030150010406200301d007241 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 115377769 1250 115376519 115376539
    0x1401030f050601050307140d110421020904060c2706020c01050f0702010318080d0f230403230c010510060c1707021813050609010c0e0f0102030c0d0c02 67
    0x20003260080d24002d0906031115411911009010b030703145203503602c6c21044e42e08240048011003480f802281c4540c0c008821169440d824034010200315044102c03401d41003040d8030783c52001a01c0700181580d0150700058002030400e60b11034200d41c6107420a48800da421250f00d0350043d5640422042c0707040714440e400b00c030b00c8800c82600549240c02100b52000c01c0030010322001c4050f500a4102c40352818000b5a032449400560365284090b40111242034080c40d660100c03003101c070050f0b10510058040000c1c09035091010b4140e074102c6a0b000a100030200600404406100740320380c0711021014010001c0d1a454035001603c86000b4441141c4c80c0101084015000560502400d05400002d4125044640e0300c110860b40340c41a0f48400b8040780c11040c080708030014806454045806010000c0c0c0d296a04107840c10034501e0048081c0c00d113034681e490314028401450f040b050001c804c40080c0c90640f01840300c200182c0c1140102e020004240c051060000302c003691007045025102d200311340280765 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 115379019 1250 115377769 115377791
    0x1020304120e04060f0302210313030b0f0408091002070810023f06010909021801020c041a13090605040c08070905010b04090203090709150501091401081306060f140103 74
    0x16a131144c4695107889568034828405400d0940c00000000305014000c0000070501040e2071840d40003c0b401c103010304c8044028002c20400c01500f6030008840c0400f8409130070030782c482c7c007018030496400a102e142c5015410889a00a20640b40249811010342d82c1d44010f28004801a5000540600d08002c550105a0805034200312940a01c1d55540d1803100c1c00c81c2507078000a543c00b029101506000351004000360f90311440c002040c200300011410b950290700e220000e49001e8074444050b114604210b58000080d02900c540200344030200c5d01c100c0c03039548450f0050001c00b0f5071140a00074601380010802800007d40d586800c4074035540c100c540c11641da01464003121000e0007601e1880e0010441000700d617071280c01464025810f40d080d00c905954501501040f00d00d250300202c5141c050000820096801008050007403054003903508102c50988002040340038000c10000c007400300d100da00030500c032281c0d00100c05000c040c1080d44205850320145004038001400d518002810440c0600c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 115380269 1250 115379019 115379021
    0x50609060103080a0c03020f0601031a0f01050f0103020d11040308040303140708070b0603101d0c040e0d05030403090e0408070215070c0302130f02030a0203040c050102030c0d0e040e01020304120e04 87
    0x1049a40058007030b810b084c1040d00440d40d0100c0c00c03000398110300c80e8400c0c0c048007103010b011079802584503422072400101c842e000c3e02840b12000305a4042c003c00e2000401c4035495030301d8000c0101d882440d0059071400707110304c014014084082504240107020034080b040150403801042541c1c00380e1201e42c008000040144200d20074480000c01c070301e001340009000035248080b101e811110040070303180e031052704c284c9100442d5031018001c0c0414450b40c0070060003190611103100c0c0c10100f80c0e414000228441c0f151a51410003c0907402080000000202403510407030951001d803152100180e19420103003000841d42d08017860503481800c8480070b4052910901c070460700b4090303006806090482c034540810807019682c45420000c140c4a07860080c40500c0b5100840c418030400b840143c803410542010400c49180d80c10280c155441007003042c0c04088005503250042c121844c2c24801c02c9642400302c2d024105001c0354003915800402440200070075401d801101c503015946c2c00003103d1040003008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 115381519 1250 115380269 115380271
    0x40b040f050a0503060c07060903051b0703060e0309150a05090a0e0f0c0711090702010b130e0d050421110a030f03120c090b090d12021f110306040b030a02030102031305060906 77
    0x81b0000e80400260001400503085248038500a013003060400300c0b034006061a40f800500c40500c560000001401008443c8c45141042c4c925840207500f4209408041520a490103d50142c00c800110b00f0101040c452011a0b075051800742800440c103680da89184003400301650194808100c3d64001000c40c1d030410b007504c40c080e4000c10145030350341d03614061103d01680902105d0465481b107442d5151a19510b05980c648a0400000a100b4501a007400d040c070010301d02510800504000030080900c001c0d454075402810303107815140b081218074092100c45000e8603a60b800c440c02c5900081170100590301c01040324001d40b1061312ba04c805003c81801c442c1030280c0070008c1605188144291240207002c2d0641c480054550140c40c0802c0d02c40d0b0b80040500000702006178440380d41d03c0d02d0101e000c144010b200c56000401d01c08041100b8844225000040103035014555800c1101d00342d640400040101a0300a4021941d0b070a242ea2010301000d13185105507502e100711400304e06140700002d070035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 115382769 1250 115381519 115381531
    0x3090812070c03110409060614030c03010e07150c020306040305040e10030507061215080c031b0d0b06030109060c021606170606030c07080a0c1103010b01080106050f040b040f050a050306 82
    0x140803c0c11a6a0b08060441940080340c10550f83c2005600148080c4580f4010308142c1500b1242600510b00301854110340d883c8003030103641400141c10941d200010340c0416035441c0c0c65640400300e41c00504503181c15100134080d616214103024070003416080030060060350304d202c0c443c008070380e00c80ba28112003180c180f10080590b440480c1c2080748912403200546104d40680e400315844603441d00d04c40d8511f1042c1c100040e184c0046040587c18a000c00c1441080b160300c00c8602060310a500019031050440c100c0908403101000000e0000d80d020340c00044500c0d406102001140d608200c0255594882d58030b45001021603400814542d00421003525401c03413140305060b079540c0381c40a208594001805070940034105000800000e884003014000946856544221100b04c0d0b06100c2d61401c1140c02c0b80e030090f49010020202a64003020f058152036441c1407861b81c5d8809203000914a101e981d1010008520100300490740d01c00c801841401c0340c0c0111405e04045440d0810951550400e4072030b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 115384019 1250 115382769 115382783
    0x71209080a03021e0309030a0b06010e0108010305100207241401061d0d020409080703020309010e0d1a071b08070204112a0703020406121203020901120207051204030309081207 77
    0x2130140042d10250b5100e024007000c15079040041c018082840c3c02d050500465403901c20b2001c00101d541d02900b420740c0c00000746000c4406515540700c4503119005000461165600081e0700703801d001009070412a048006001000c580018500e04401014951000302c15503500500004089104154a03a98003402010070510011400200101111080001c80c1c0003622070031140c0101d5051405000720358041e8001e50b50303c610311000144050000401c06100d078a4080654020402071000600141502035a040080d111401c090760028020f2201c02d80040020350a0003c00c1012001b0385452842074406001108000d2103401c26070144040c0c01c2180003002006840301c40c1d0345206522124420015030700240e803290003003021b4a51b90f8103d10300030414190030404001c00e40120041d03034505489c045041404a40009001000c512140100c1030b4010070884144201405504000003400d00c01a80e0742c2d6507450b02421844452290a809001c0c809c01581581c1c2c5034800c59428070740c0050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 115385269 1250 115384019 115384033
    0x5040507060e0a1e0b0304050715050a050901030c110f031b03090108160513090218090f07030f020904020307020d0914090112051006030302010b1201020906041a0f071209080a0302 79
    0x400b40d03651080c1c0e000c510381c901034100c20000d02112120020743c00b45000c2c070041e24199080858940d00c02b0452907980381080340400094985591107002c1c2c629051092030b002c210480107034411245100242040c400f1402001300c080305c0c030070300040140042d004402c002050010703425000c0381c403030042425850200e20402d000402c1c507840c00c0d80d55003140025081450a0001a000c05510100d158002c034015545c00102540c4d1040d40c000d0011800e44112904211803500c0b8203281c03400040030b041c8200781134544bc600108c0030030075010345914400251086441e458000070095480d941d00c07007110081100f007070010866507003641800041d5400504a850b890f4a4910040c141c02010340c030654031030140c5945040802000e00440000714002d0b0300114070440307182e0400c82c0100420100100c20380c81040414800d403031300c60985003198010407a104403141c0021b0aa44648030790004c4040403100080e00600f008451900c111260b82c0c285d80314100551180d82440d510000d1050160140c2d001c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 115386519 1250 115385269 115385279
    0x12708010b04021306032a0c0201200d050c030d0e150f0108060103110609031b040c03020406020703060906020705031b060708090616090b0a170c0f0409020a0e09040605040507060e0a 80
    0x50000c518802c81f0b40c0c94103505e2810100310340030550000b201c0d040082c04102c0d44009643c0d00200005000d680c0c0860311048224a0311541d85d0307814107401400c01e104000c5811082d80d1010f206a44410107910424055403e41d16103142e241d031001e007039080120041c84d01080d2400088003610303050340c00c0740004000903421901c07030b40314503012111026801002000000560b0324140101e00c498089000254682142c40301003000b510350000381c4404052061204003d280c0d8009042011a0b42086000403c10004e0504c00c01900c140716025080344800100b65144c08a05412100580b10790015190305446408049850140940c0e140969a00c0304012800140c41d1101e4401640d58a080c0010070980e03500421043e07400c10000348021880e403200a0288200e91902d16a2000070b100e0540d2421f1710f0081b141506000f00e000f03841038a0b601049254510340114614542042c00610b03800d0586414a01f03607004e80750842e8200d62030701a5400001e021401101c40003290380c80140b0b070301a014280 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 115387769 1250 115386519 115386521
    0x1060503060a0302060c0f06060f22060f0b04080c0904080711040b13090606360b030102030a09060b030a0b0c07020303160b010e0f04051209012708010b0402130603 72
    0x1034250703940003140490010069070740000074502d404114002c1c205010a13910902d0425030000c041e0b5008020405200301e85542e1143c17000d551284802c115951880a40f140d10000c00e1aa0071590301142602400300308160000003800031a044542103603188842c000c240a40d444050340e0042c00b100c0140649070000742c480880f1b40002c0805000000d01c00300800001c0d0000002d000c44000f4035503610711000038821240250340180140c6a801ca100c0c52078040d921691402c142007407030ba2802c44003207414400d60181c00245906000800940d00d03401c02ca261440100301c1c40794122000c42c1303007007050605424003040310801c068004000d1303101036603100c51507403181d804103400700d0f41800300b00404c9440b101c408268114060103000808095810024841a040e1014000211ba001c01008000c0041c00009913012501580c1ca121500c3d0868800180d4031060a01198954088030100c102006040799201074121000c0000a1048cd407501e42480100d118105000a101501c6481030000341c0c02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 115389019 1250 115387769 115387771
    0xb1302010e0405040c1403010209060405090405030712080f01060206060d020103020f07020901030803040b130f08130305030309013c0504051516030c05190c0305040b0406030605040509070b0301060503 88
    0x40c1048441e985141001030200ca100b11003c036401101d541d414084416540c0c0b1011004406034021031800c404180029501d02542c400c0920032084100002c0070080203000341c3d80229406845480a80040c3e0405811003608032003080b1074112a000011b410740c0b0004419000b1007000e40038005180c580c0e00118060b40c480518420f911ba0200080c40058a4440e0b19a0086000e1101c0b0303510303814640340404000c20094407041c03080c00c0c0d6841400200f90803200700d41c901503100101c10790b0381e00d4103401da02c080075650748054000d000c0881001a00c04040d0801f5264001c2180200c0f201c2a400788a5650001540548e5204880002c00d110f00d00c0c010345d00150b00540a0011140791001c1140b50600d9102c048a0a83d2540012018402801c0d054011140f8110540c02c00908081b1075044820122100315044020041070f2100c080a050056045034040c1ca9442c440c255960f8480101038080c0c5503520510b40600c0c580000200e05178030219030704082d103020012042c80c40c4d103013050484448d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 115390269 1250 115389019 115389023
    0xa02280b0603070812030a0c080f0f040204060513150609080a0204110c070618080d170618070512060d0201050304121806120507030e07060c060e031602030d03090b13 73
    0x42040c0004c5a083c204105468241c41c500700c0c40759a030700c2d000b005281541c04550591040c000030304c040c09209001c0d501384640c403a000400003050342d900c900004001c1c0c1010f90185030080165038a4140c022a90b810807980e1117a0000400491075855001b1100c0d24094800c420054120100312030061501e43c100d4100d0055401300b00d400d00c0c2c4814030250510fa510b40c070007404190082d40003d054040410400f000b419504040c0c001d280d01940094075000c071036144404480100c01c000b40c0c40d551102c921080c0b0310450070060000e460b01c01c0000e001640301081c95505002c0c2800081d01924044600442082d81070751142c3c00c64880f6503c42c0700010004100506000d903800d0410141046020030100808440e920350a240241c240007004844000e4580002c150401c0000d00100c1c0307000840d803045030458585107207840c07001c0c10100c00a00c80d500d4101940c1c0400501c40c0c420a00720500f417120280202d042e01c520b42141101641201c0f541c0384020080d110880000301301d110754110200300f0b24 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 115391519 1250 115390269 115390273
    0x2030606040209040b1903031e09060c0311070f050319080901030b3f06130803100e01090207060b06281202030405010f0f33150201020a02280b0603 65
    0xf81c26500184410141312000401048113400c10010706a020b212503009d50009104007900050159005201c2090741c01030740103114510b004901014807070344c4102180b001c104166880652030b19840c8022090700d00c51284203200340c0c0041c3d00141320307a04d446e1040303036403201c074584ca880405401034014040742017071554031261400419038101100280c0d00c00001d13100c0c1d0f80c0203041200145001814103802035101c59540100c007000301c025004001140e02c0760700511001d0b101c0e50b0f403000845c5008410b80251441c3c0d11104c00010b0800300700d0300507149640c0304060511101f00d0307400a001242c02800040c92a03442d4045144018001604401c40010114988030310b03444000701444d410f99006031402c550b00c1c0c1d5946603055002c1400c0c40358101c804454030090084244070105106c1a41607402d2101c28182c40400001018001581c0302c0b004207100c020a08031018000006030003500b02c0040d80b409402448a0546089074840d961502e403003c07500d0840744408a9111303514007110041c001d0b038043c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 115392769 1250 115391519 115391531
    0x50102160b040e060d2307151220070305180f0120070308190305010608131e020a030507030c0902030f0403030207050a020306090d090e150913020402030a0c0e0d0203060604020904 79
    0x4644076606c45546204200b90b8401c01240b0031003024038100b0b01c0e61105240d007550b903411002c46507001c0c00e210180808000080380f070000c002d9440c4100000d8031720509850388002031103000c00d41c00c40054001e00140d000d9035400603e0107000d000c95802c0403038506002a00e03040700101207001000c000c22401d000a01100c7c507694403a0b50b1025075a010340410700b58180340c0310200c2021945070080c03030f003d4402841c02141c28142100d00b80340215829038010003a091141c4070500c4550051092140030346c008000480c1107a0f0380c104591544034601003610882c0d25a03070b0108051100707000b103038044d441c815a103000c50380c2c460b2803c070000e41221404036001c0c001c604a000c05a9070421440e402015800042c10003103107081800340120030a07a009815000580c420040b032607414541c20110b800b402e90f225030703141d611445494428202640000d41c014804402e000d1028440e6228132040e030340c0c98554858800c050b40c00c02140404803c07000b9410b178089800150941425000b4082c5040302500120f60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 115394019 1250 115392769 115392773
    0x10e0d0501060b1b0606012d020a1509050d0e03150903090904060209010306050315010302101b0308070f030b090126060129030f0f0705041806050102160b040e060d 72
    0x44d0312201c0d0301107020315280b001c6440f4060901416800900c08d00300b030400c0b03150743e1070b48103c100504124007130001e04810f60301c801e01d0300030300190700019072208489c1c058510044404d80102605031b41a681441000c02814000d402070241d02d0590500034010a10740140601180700210000c211015600060080b82da0070703161291424000c52203000301603110504c0f0340006085500c59803100e4800d80c003249400941c44030352407146041d2501a6060501d00030041001d403043c0303c0d860100c411040900300300c0020716506c030200301d000d480d43d5507400f012a0249a81201a1025070f81c2e100ea000c030008004105455035107000784001940c092022105407082c454650420509038803400601ca502d10303d001d403940380c10643c0c0500440c4801d91a040d400c1c40c1007524190440140684001c0044d04e010481c858040c009590080610000d20381001c0308141c5050058007a42c8202c5016125841008401012001042e02a00c0a0801c0c40341081e10b09101102a128050050713a0000444004200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 115395269 1250 115394019 115394039
    0x915090c09040e010b0913020d0818030604050106030308150105120a0e1f1404120807030b0a1509080304061715060a091e030b0106030506030f0f070503070b09010e0d050106 76
    0x954100f400000424001c6141800440c000041002d9071807c1004040001a50b03820a25189940c200c03219a44940301e90413060a8401600071450b490301c0b900c0c040000f0002d05400080640c0d01c296030340e2034292241003128014a0300c0080030307400700358140f14200c160b403085903c903540054869408030720410301481071400c0401201e0b903c2004124a000741e51001e02901541d00d04240c242c0e68050249840d071035100740b4000f0041038008010813480440c00651007a040424031150007001c041c4c07400c1d035402e01d081c01250a03081c9038000c21300000000071019008404c0e00c1c2218850f4445141d070b100703000c0c010003020100810f94085c026400d40d59482c20b807101d80140c11181b40b01d440c1c0038000b40c1045980d40b11a030003032110012a15241409100041c41c031146035045510a080208071074807100006801c2c4070410b01005180e225080803051018400650201207803429410303070f0182a1142ca42800510a1841e40d40c085038100d0760390500f50429602182e0b03c2809940005851610303214604 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 115396519 1250 115395269 115395281
    0x82203031e14010e040c12060f050a021c050403021b130903020c0109090209030d050d02070516090e06160c02010909021812060f07030b04020904060905090106050915090c0904 77
    0x44169691850400d001e003142d00481c05005050f5085840c0d02e083d6039000180b0f4454003510b000701807113244460802501c0c0c0c0001590030000e4905100b18544040b009000350040a1180420f0704c0fa010582280c0c00c45100d040d00480d019800342c8100a2400051400710301141521504803680c007540e02c42c0c4507498803414012a02c00d502504d4080200c1c00014100001074100c00015071041096550a40e4001f035110040005810219241c0e841e000082d4028001e460780507019000f075580301c4100032a80e8150005451542604120302c00c5010107c0c0d9603104121100c0c01403940941c640201d05001c0c0484d024554070501d0710544042d180d403180416078100c600d01c030040600c5601008110301d005400c81d404203c000d0b0041030b041c039140f03000d00394244003d440c003c00c1c59617800c20401223440e9030301115203901019200b40803e0390380b175084030000c00c4c046803811065481c20350301240f28030b04844a58060036070790800c01540c070b1510302003142100003d090089050402c10130301120303441c0e074000d01c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 115397769 1250 115396519 115396571
    0x1050f030f0312040b01050303030f041e08070302060603121201090b1f0206091207050d0311041509091b0203070303050712050c0304120207150c020a0f0e150108220303 74
    0x10f0012418240341c0750317a5040040c4c0149119030001c0c410000c9000000c030880f540b00f0b0b0070140100302445c0d401ca450b2465105ca82016040010004e001400d16400041f414001c940940880d241450101c210400d1800707029051014080100010000424550410300789044014070700101910444110a8505058944100940c00503403c004038507505000d0080c0e411140e4054074505031503560b640e82c4076400050f102e0305056543c1843d0810103a8070003500d004d410a250030f40c40050045001030401140c03407040440807801d2085a001011700750b9007d4a4801c0550019420081c45039400d50252800500c484200214540000c52818040c000d01d0702504035030030016a00d04050400c0c036450b072900719020040d5406180d0820600d181609410024045454181e0442e41603100003138608505503c11220000c01c1d031008900c0d5100e40c1c4290b03004045520700043d1480b151401901d205070112025403c0b1a0f1030024840100e400c1c0740007070380680c46842c000486a90b0890081658801c40e210 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 115399019 1250 115397769 115397797
    0xa020d11101409010b090c070b0907080d0201060801060b0c060f040f0c0308040611210a0c05060906070f0f0509010e0303120103150e010e25090603030e01030b01051201050f030f03 79
    0xa00c1480042813017200348000055581800c1803a149160352824412100020000404a00050510101805034074007408520064031607000342c014000f4083c1c51140500c05507546000400aa4181a01e040f50868081034015100c0c5940748841c83e4680c40c4010320907100c05050062007400034812105040181d0700c41c1d04815203da00380003009022000c100d02c1c0241a0b0302042002d1540800c0c1002140c5010003484031079602c0c0c40c41001150030184003480208188070368014044941d40204000f4840d01241d40c0b019000e0780e04e0002100d4400341c81e1342d5080498020804d60516500c40c1c9519004944064100c91038040c80000c40405040b0991091302c0c280da010b40300c0200c17071760300340180302600c41038030000c0c4140c01c440043ca0351100f010002030303505401c69102c211107049404111500a1010420800801c1c0c0d130b90801400c0c00c409003200d18001ba00c0e00e403540501d580100240e402d04000c601c041440c80e800d11092200045024110a6043c800e07111303a814452000c00007000c05040000f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 115400269 1250 115399019 115399021
    0x120c0106180e070302090601020f0a0605010501080c0a05040506030406060b0304030e0a0b070503031603090b0108061f1410020102091c0c06050a0507080a030b0d0b040b0106050a020d111014 83
    0x28001c00140c1c100c03820540190408500c4050340d100018108243c035012514500c103a00c45000513441c0c40054080300030706004110f05902444003a40c0b145040300c4003130b29000d070035656812200030284148050ba80216100f40400d1001c0e0402002850340184035510010b522a00d440d83c8036007980080311b01300c0008502074060451810424194030040100486050808500742d0f181030700d034000140000e0050843c800c002c41da45101e5004a1401600b000200c0e0b40d80d6180d012098950300d00321110195488248807103034607080c070108200d0445800f89031154100a52400300312100a58040500841d03400f84500c103510355405009101c0744242c807210104951445c0b0308551203000c1c550000301840000c0c010307a082950032004445a09038400490f903a41d813602c0d01c056000f07103280c2190740e402000c018140300402000c0d5410900890042145001c0350384c0e240c00454191140030a00f00060f0001120303103080a00402030b403c0030065400c152031200d0345070041842240d0200c8201218019404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 115401519 1250 115400269 115400279
    0xe12030c091f091206020f04080307030e06030403080f1306020c010606120903020706050f0409110a022e0207060204090f021b030f0f0c0a1502210103020307030303020903120c0106 79
    0x1400414603541e1108100c400d50041c03250140c4040f441e13208440300d0907030102d0201e082182580c1192050f040c1e4071096074866858070042c60f6650030147c81100403c8180c01c4101e600d29201080e244141d6142c0d82d0481e07596100084021010805006902010f000d00b920500107100d6001030b1400d282c0d0107000188040c60490010700c4a000c0c0300c81d901c042450703c0b045402203580403503044296649814150703600c0d002c550240342c0030b00c00c95104000e5603280040c002c040c05148001880400759550072170b20210340e070100c0c00c541d0800030b2403c0541c1d042550305e080d8a032421500a04581e42c010701d0010b007400c0c0d441d0000c10542d824240620b1a80da80040e87c25a1060803543c5965041d4001d0011420700145d2000d2402c01d216800e0801c009210100311080c22510400042c8a25581304417141e000120b4000c001c00a500700c4e4094400541c0301d12224552103c0483c5840c3c101d0f03030020000e1401c0d074a107440036030080d0302c6030711b003d901409141e0741d101e201d070740d0300c1c008281c008114000000c00520301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 115402769 1250 115401519 115401529
    0x406020d1e1a010c0b010501030e030409050721140a0c0309060e0609070b0309060a0f06091503020405060f0306150d0804030c06030501060e010c24150e0105010c0302030703030e12030c09 82
    0x4000c030b250622140b445600f011501000d00351341980c10a0800003504500b04503800e1860049520001c10142800108901e8030790054049482c01d9084080000c91480f40c007070030081e20390700303aa01e900031602c520015565030300e20f4100f41800c48840c01c00060b030420645030304003a94034680c40720020b684071000744215204100214001004a09001e5045080c480001629880081c1042c000503840e0114412070107400ea000c407008003220101000582c0005040d0021000c035484107030700c03a6280c04005041410300e0352040d0413501e4000d015180d160b4602e0107144e4081081007240c0e030080b112100c207030b001450800040c00590301540744101c01628000000f400d03100c0c160040800c000303000ca607110099801440c0c070300055900c03040d68851008518400360101c808a82c0c1c2c2c4082c1d40c00d1005000e0394103100d201d202c040c1c48008200102c182e0b00c800040d541c6841c0c0c064010300580c0204000400f280c07086e404102c00c00810300507165800721b802e0381c28020780c205440c22040b81d034001030745c1c100c45e00e00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 115404019 1250 115402769 115402811
    0x90906030c030d0c051f0b0f04020c070504090c0302060309030d0c0914131119080a05010b03010b030c0c0a03050c0114040201021c02030c010606170a020c060406020d1e 74
    0x440c0188412000c5001180d103581040c48582d09100c82c20181004100c003d00400c2d40300180c204848603600d032012840c80140160140381c030b0041000011481c1c89007000d0088410308010070300106081460501808028071502c80d007070f210406888408001a600d890095000f00c440c91b00858848081e4407100e811501000010400e125801d0300802000c509440c041100d044221100c2e9192154104020054204401100003c200025601102c4404845090508091a03980c40010364492400b10100c5a007030213002502c24043c8010010714280c41300840d40404841899414191783d141581d2078040006801c9011842c00f09447d01401000d01c103c2c020616040c48680c014100b60300080e460700f074028941307050409240f50b10a004c03402001268154441d01c002005842c1d80e50000500d07a00045840701c40c2401c2841c04030b280c01040b4003d85580012810140c0529110350795003400a50000349100c1c822929144141c07081c80180b604607800d101300f5503010804094540085940b03a007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 115405269 1250 115404019 115404031
    0x7060905180403140a0e030706120e0601051f050f0d0204180b090f09160305030c010e03030103110d0c090509010504110102150f041e05010b190501020a02151c020909 73
    0x4100c41c10440800d5000400610703100c3d0500199646035510f0404450032584200c890b5090300c142000066410344c003c50440e0403c0151400b000802000707110300c5c0e1110020710406038083c0e181c064403400c0c0003440030500408401410100e15104412510b0711440d04051040201d44e07a021804000384e003505d1005200039021803101700300c41680c55001031841c001c081c0c0780386c0c41e0250510010f500c2c90010010864440184544594a80d40d24a0210f81d264071056100009509203000303408045400001e480c141e03548902d901804c2820038003480703010300400714160b0704410358640c001410805842102c0c019140c0500220301d501c0c041c1442c0303816a0225101c541190b1010480c1c2e4082c9079030301c80407a0044580e2091005036142d60a02c040c0b020408070b601d1250100120011041081c154043c1840102c103580c04050290041d4051102d601648201800343c0c0203140c0e00720040c42c18885403004054404205420200303040c603403070312060b100c2c003030318042c10f43c0003401400c40d103000c8246540c006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 115406519 1250 115405269 115405309
    0x170408070b09010c0320030c0105060a050a051c150e1005070e0607021c1205030a05100e010902030a06150507020a0506160f0807080307032a020712030201060807060905 74
    0x11080d040004c0203c801c0880c0036040201621020003a15072112604d108400420100d0785c807511230310036070740c0204815100c0700e114488640b0000b81e60708000740100c0c02c940000345981000d111042031880400200381041304c0ca00840743e0407810390344061042c07022510540c0e00070b01811808007200701c11201d001e080501440301c0d0f4040c00da00760b6503000031a46425811303540e103440701086200b48a00c0c86405040217000100c072200703107181140d009000e9840350003442d8091100703445840480c0c007501c02c0381c01b41085c05022040184406400b036002180c110650220000e440c07552a0030f0b088094020300043c00c0081c0000500c2c80c01c0d4900b10325480301500c411103403640380c8200401c0e0300242c81c40f117140003408190030b07848031410f010340c0c081a07504154101600d181e90b40b034804030042c000d0410303240802c06240c000345031105681019844048024454005216103410003112540c80001000100d04540d04e03001c0100d400c3d20300380300c0c6a008005039103a0307240c0706040c401001050700315105101498 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 115407769 1250 115406519 115406527
    0x60906081008030f09060c0d030e2a0f03160605030a0c0801081507020a150605041404020a0509090a0218070f020d0903020607020402070203030a020d180608010e13170408070b 77
    0x1030700003c400c84040490313544505070b07110913500124030a801001042c403018040c2207090b031034454042e041005001482c81c10350701d01c6031b207040060b0011107440380d013502031180507880007116003404e12012840c050010100c4440400468114003290b4880d041500000c13404420301c90859170600406032060b10718244101c6560505513011f40e81d0748101c1c04990b0100f640000305004c14000c1c0001c0e050241c02c524400400301e0f0360301d1110060318a034810b041c092443c202d8803000310041229078900541d030060007000e500e458a410080501d401400710041c5002e190710450050791403e1f0140d29000506201030390515003148090558a42002d84505640228800302c014075030062024042e00e604499064440d080d50001c20000d000380070b4002d4042c480040c003460480d40000d42e04149001170784d10440c6103000704d60306400e008164850034010a070341000500081808580e00d40e07001701490000700d803a10031521920105003c001e00e4000c5904001001d1000310010711101d8040d094183c2490300e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 115409019 1250 115407769 115407779
    0x1020d0f0e090a06080601141f1b02040e010c08040c06020606090109240803030417040b070b0402030313120b010902040311091f060201140912040506130f0609060810 73
    0x801e40c18031040c034451811107000900400250b80824090000041141c2c550f684803100032481050f0a1003003481441452031200499a48122805094015565000441d00294140640400d1541040340d02507207800b15401280002d10404200250b10f0760b48650324102418010184c030700b03030b810102c00c64100c1c4080000300d803901c1c841d49045901c242d400050140d103808051a14580103258801041641600050600c5000020350b00030b9000700340808124500041008403031081d03101d010b81117030084c40030744d02041b4134013034099101e03001400382d80c500f03003001c0e51040340c285083e0041100c02111260901c1400203c1030403601400751100c045203040d040d5210070010f06420342540748103c100c5000941c0300b141b05025603001d062201450500d041c2c41c0c80000c0d01a020712212607140d2035040b4001601407100090032545441c10150103841d0034144424400c50303500c5440140c0000c4581403000440c00700110a4a004000560328448001d0130300000501d620b0003d8040e4580f0b00c40c122003400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 115410269 1250 115409019 115409027
    0xa0605040b090c03070c05071e0305010e06150d020102120408060709060315090905031c020a0e0607022b0506070906030f0b0906220203090a14150703020d0204030f03020c01020d0f 79
    0x3400c40064140300c06d8404562a1151801035140c20040071001c800d0564202c6080080203042070364071440007406a0401d62000c90340d281001c4403a40203038a62a041c05c2a0750800c4040c80e0301c41401841a20500304622650f044141d0141d403100560764401001c1001c0c071a40314140300040d1a292400b400805002d48100300300301c0c0d081c0030b26500704d580e0708204c90410030200100d540d83c10040ca00b50384c107035420a0082e002904400320030404200c02c1a15a00e6078074002e0201c414040e4002c120f11308202a442d104580210310215868840074100b4072000400d0080009a100e10441c1e9070342542d650800e00010107882201d5103140030982046440d8071541d0700c05000380e601c604245d4240d00003a038100700d0b5283d00503000003074030408c5100105000c40c070880030800501c4640128000306120740c004440c6d030303075078250941e0710344a58003401e0110304070501c0303500100100300b0404409403e090b01c076240d60080300e500401c01c401580c4240320b04000c1c0c1d40c040c1b04d51201030f4007030704201034181b000303400c058 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 115411519 1250 115410269 115410271
    0x1407020613180f0e12070813030f0f1e210201020d020705010b100503010f060809010207020406062d200a060504050307210e0607020a0e0a0605040b090c03 68
    0x24814480400d0381c5106001c0700700703800002e0440324600141a404410381030010050000e07405180d0f070501152a0704a000010403c4c240c082915400e0303e4036580c1c0e11140100e80000d50481016440e00d0700000c007064500180c1c03011140200000310b150960f40c5015a4003170b0351070388640104034850100c2d5003ca050303400301070402d2444806c645010609040102c0c02440303070703184c4200517171703c0800c0341001d00005502490441000382c0d454032200c584100159528002441070540101000d04148230161044881c650010000300001d414500340b0307400101914131a40051000910410600d030800400c09464001100380c4042c01541d400407800082c551050400d61410688016001ca00c0090003005095041d41d045801004141010715095850390321031101620030700400c0b100102e10064403148224041c106440e07105c104603d0205002d400c4e04072400a980c4161400340001d9064035201241e40301e90001d80001440d14101350404c030840c4c446c0004180900c0c3c92204104040300417034126 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 115412769 1250 115411519 115411523
    0x64505121b0c011202070c030c090e010b030a1e03020a05010903050306190506090607020a0509040f1202070806040209130c06051324110304031e02090718030b090c030f030a030c1407 80
    0x740c0d0f1b50101c1c0c101880d420249038001400c0050703952000410240304e6000c0e14103480150000d00042000c40209540c1d5040c845010302000d9450424002c400c0c03d110380c1c100d00768807e0064914445582d140c007421504110703000e80204800204001c0c0310301e4141c008002d404000e4202d8004241002d0100e0f0300e03400740795019405948000340520a56480d40e80004c024080200070500f1494a403a12040b0440c13003101c22900c0c0c55410078022111030011410b0019102c09a000b05229503d81c0c0030001100400342c4504482c00c4031580c280081811048840d018114940310b140d683c668002302200c0d0300c0401d0740003030161446a08006c0080d03d4000074280034211504d082d0913070780d480095107800d502c1540d2009020100701109442c0c10a681003851a8490003120240b180d0b90794003105945806102c011002d1010741c7c4201400025030b0f5042c1d03581c101805d0b004585810003050042490840a10740d015020b80c80070070030000b0341e0b50500440204a05518110a240701c1c0b5981c000d00c107015a00c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 115414019 1250 115412769 115412771
    0x150601171618030c05040b0603190f02070f1109090102041d151f090f0501200c120304080d1110090807020904080304064505121b0c0112 60
    0x1035454040c42000184185100c1039510481c0655901d13110054407200d22039140111f0400c040d203440303450324070241e038481e05825480d180100d08032410600100140c403c00307145181d0900022006c90342c0c420710100340c1d620405e110f0310382480500410078400d5006000b84c2046c1c0c0104424058501601280d1680400614014806840700f1811700e4607084402400b0b5084010b021801c00022003800006012810b41d807181603c19803a540f9100300c1c00d86601a0034089282c4a000c0b43c050001d90380c01b00902c10004003951070b051801000125460811513024409070703c0801e0501c1075030700038410004004900d04000860391400c40c202c40c1c07581050000c03041d48503528582441808018400c542d041d9a000300914628a0145455000e0b40c10079076003904d15510346090481c190500611342941e07515510160744111100e15041030968401c004003001c03103c0031691f50070004000f003190807c88103002c0341154071010850f64212000422074000c202d9036010358184c110070707600402d2140e058024444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 115415269 1250 115414019 115414051
    0x1701050f070c0201081003061103180309060a0e0a05060c010b041802010903021519030e0d0e130b030a0503070503072f060a031d01061a040e01050f0a080a030215060117 74
    0x8042c0c0c1b0300c900d0759440500f41c1401d04035801c01c80b92001c0001d5104081c035442d903601000b61888040d6486c050684910340051040114030481800740c0d10b40d0000c1c1000507d410172180d1520081034107500022200131507030391142090015481d140c040d2461080444541850340b10071500003c22001507484040d00410071084403c0b111107484040f41c0780d4404106203100f40b130b40004401002030030074070350756813070b41c0501981c460f0024498a40e04601c40d1004144411040d0b000440c01d000f0308000c83d803e40d040c071809a4141c001842403019002c0b41c1d00030710165072140c1c150700701400b0803500003c107a600c540d041d040c0c0c1c0c820074402a504903052038050307401c03a49440003c0170544c02442905004503502c964116a40d90420054104c20151000c4c1e030100c02c0c2800c00d02d95003192602550042d00310321340e500f41c014084d50801800e81071440100401d0b40c8001c46e554501141018070340a025401600004403603c404c09144041720f4202d40c0c280782281c24414401c0000c1c292034000b5081d4031a00301c00030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 115416519 1250 115415269 115415281
    0x1f090c060c050f1b1003050906010b0c0109020a0f0303080606030708071b0219051e060409090302010b2101060611190201140406080f1b0f090411041701050f070c020108 74
    0xf200b4007851805804548100390702d41090034000d41c08101144c032611641d503ca14515111340a42e600400d1110300411099090456070142600040340c0e1500c0d0750342c0c82e64028096a5412522401460340b640a880c14031b080d410010903003800200b10500540c810410321949652003400c1769440740240c904050040041c811180e2620500b1901942c0001c01c040c00807000d400001510b41110022511811840c0c0f603100e04420f44901d680c000e035403210040c0010400700284d50082c2544038460300c00001c1c1c0c80c2c44000000c4000c07041c416024141d01e00d0301e0411020750024420000504418284182d540d030b4848030300c1ea51002c090180c8a0308034441020402164002d02c00d03284007510984d10740d03444948400f0018038022088414900c0c4941d5400031403d0b0b001d00c0c0f2407280c240b8156544e00c5203824944c0d880d100c19075120328401d0341c206503501c00300545030130040041c0c400780c6200b001e2105080c1d181c0042c5403e40e10054403411b4131005007420300850a4104080500c81642828525080c2ea150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 115417769 1250 115416519 115416523
    0x60f050d080901170406020307020c03010b010c0b0c07050613110a0b0d0e0f011109090a0e060417040e0c071208010b0d090f020418120905030d200109051f090c060c05 73
    0x3684c0d06040b982000c1050108209068000d10f10030001c075070840d146071041c141018241c0c0c8489044602041c4600140c0c0e0100c1d45000300d440d07002d00008030851411041343e4407a4a008d404490340c20b2812203004581040014a860310f410010013144d05921040c00d1400b844a244540100b01c00c03226070b0745442e602590024020b035180e41d18080700800c00c24003802c0000360f0940c00300740307100d126091800004490a00078828074041c009020f008080a40d20b50752081c0c000b004080d0110011602031200261010001001f54840da01c0681e0741c58079104289007240308400f510b10f1000c140540c0e1001404006001019210710002e445008075501354942440303596660789901c041e4006007000000f0340d8000c000c0680d208818442d1056240c5c0142c8190100c03820350086c0200b42d455008000c0c1c50000e248100c15981e8964241103031411411004500c0301e0855141100403549604125003040d09200c0b12021225400b1502c00705100301c1c80345a94054480c2640e001341e03005e001c1e11403070300c006004003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 115419019 1250 115417769 115417787
    0x3170903030c0d051f030308010515040317030402121f14070f140706050a0509120c060402092701050f100506040b0c1e1f2a0e0301020d0e01060f050d080901 69
    0x202170140c85586480e410014001802405503501450700c0148260000c1554030403142101c0e000743c07409400038841580504079038030103403003642e22007541e03200c0c20f00c412410306c005d00358004004000018032490345000720540d1b0ac1c40410b940100260b1041060507500010322000070200340c039028040180400443c81c20380503c407009000e562410701004603c891961000c0d01901088040301c00c2c00f19443c0012150741b284000201d4250003040c0403c005041504902e41c101ca80b0b02c40c01c3d0b5440c13900c8007070890001154100c08440340c0d1514188a2042c00101d942c0350001148201c00c08080c1c1800e000c07845920440c130451454500008143c210718000344041603425140031800d010b24540d04000300e0380d07202d07254605103000d21440084d0a040e1428821094a589540380011280c40821044040c40100b030301e42d0018080100703450b204a0380c0a00c01008207881d40e0f500060481842a0003500711041a0011800f410120409010903035480c6100f000140d0320500307050303039880860012590040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 115420269 1250 115419019 115419061
    0xe0319170a021504022101060512070506120411120d110c0a031709090103140607081905040201020a0b0705070302060610170a021e0d0c08010311062503170903030c0d05 74
    0x1862a0303010f401b50b07042d04003004460701100c4950b61460090b4201b61101d0f868420307103074450070400c980d11540c00ba40f08a154070900640200814407550400b00c3e80c0f0143d4255140c00503000021030000e619040024281c00c024058028008806980089902d1388803500024240e03401d03425024180101d403100311401c0b02e0002e0210f85076941e6901e4a1007074480d0042c00c03003401d406110006a0079038450124a407284807a901c0349211440d8900e0f0a100401010708141d045014041c016404151090304180c058030040e5941782e900c0d4550b040c000d0400201a00c0248141041c031544c2c00101d41c040c03d06104008807004030380b0240c071503d14920081c440c5468820510303040000d9045500b400002804d50b107104880184105069414100c0e8044000d000c000c2200c005020401d801d810688090000b09080c5099060700c03401c0102c10b10710b07002c0d40307450490007e0f000c200e200e803803c0440c1c0c550941000328a0000d609509140260aa5034060103100d0320100e0395501c00902004000000141c0e0b42c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 115421519 1250 115420269 115420309
    0x207091a21071410120f050403081503010b030a020906010c0c0b0403150207031205100b0304080405010e030d080f0c121504050106020d05030a0207030e0319170a02150402 75
    0x510140030740c6035814514141081c0e40200c490005000702d16051018055000502d04040c0741d031884810740d4180309031204104940e03030b2142580c5010100b1710816000b02e00940b102c0f00c0a103880c02110b00340c900c604c2180b81c0282d050070081c0025840004a4906441c1c1c102c0d400c00702544c0c0c420041310401d0840b04060681141e00c00700040640202c0010400e4a0040c50b00c0c1c0e9210302d0002c0b850007a481031482c002c0c002030344460200800d000592195800460b4070301c09041c03541da83d22107140513800a803030684441e000000c0c100705544c0c00ca0040e5440010a402501103001d40c1c2102400070480108048070000010f0009070201a000b01210400c45107202003d03504c0c20800381854840314009510341c02145000300214201d0300001c2e0300d440b0b0964a42c0c50391303d9969800b40b100d000c3d4000130b00c21000d0040d101c0305c401c0c9503a002c0c01200d8084103841039844d4614500e0504d1085401c0f1036461030241d20301040078406184c0d02107403241c1c804c0d81e003203040d00803500c9a1007c140c1585850440c54104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 115422769 1250 115421519 115421539
    0xb0d0209070503090114040b040b0702010e07061809060e040f110d05010903030515130b0a0b040602030a030506060906030412020a0606091e0501320303070b0f1003030207091a 77
    0x54100c4003450084213814002c218500040c1e0294441c44410344010f41181940000140001c004c40011707940b000c02480041000c140d01c040140c40e11717010f41c209070702081e4140103c8901c01240d8103040300610f0103c2c02800a02c0c40d0a265241d141405040500b07030035a41e40d2910700380a0f500c001c030156a513000d00f4070300c1055541d050030350003000c024a0407000a4101400315001003d04a900071345581c0050000c21070712505540b810044c84000b4041c0d4110394040c200044a0900d0806031000382815000340d5983c1d04411030080032600004c10492055000340000902c503103030751040c1c9078041c1e48540b440c85241c10351542a403402e550340400a182a04019020034001c0d0b4036008042d40b0380108200c8090000c20401400507500c1c00d000c1d04030545500410440161207000048207000124030380712640b1501880400d065511080382550300506080900c040c8e9929001d03169031109400f0004c00030135003940ea001b52242d00a20030554095105c08411220805030750703c061200a00504031149 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 115424019 1250 115422769 115422781
    0x90206040626060102030901030e0c1201021308011107020d0201020c12030406020d26130c030b10050102160308090111150f0702161a0f03090a1e03020a060b0d0209 72
    0x1c2e507424201d42c240c405103003264805610280c510503801110705070090b5062070b41d0a00110005c089104494010348218200c601203602d51540314608075581b20005a552040601d0300034403040c3d079034000c0c20180c0c54140d07150407203120714080e01e40c860b40c100c0340d01c90b41c2249800102d00c2c000b03076248010707030120880140c000c41c42000002001150082e409681944180c12070a66503010700615410100c26110082c40982c241c404280764090741c49010881c030920691284a90410150406c458551140382400031081d1910045002880244000d11502c1e04a0154031000389040c84028000c3d4008502000305a010349584201c4134a0841150164088203404011b40b010070750302c80001820000200e0803183c800f056012130004410340c0c2c0270040d4a80246001044050100d06c080454140080c0c02d110790311000460146c905c160040040c050340c0d05040300c55003440c980158410b2011119040081e07008680c0321601c0d0380001c2e0000b11200da40c8041b9500d030000c07a50017988014040204a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 115425269 1250 115424019 115424027
    0x6190e0f010b0406120c03020405060103091a0a110c031b0708012d0204050306010e0a090b090a050d050406090501110c0a030507060909060308160f140706110105060619030902060406 80
    0x28646a0880d8140110750380e884201014115805c030240858404500900241c10706030031613900400189000a0501510b444101001005501c0003112000c0030040c014000864010440010796510015142031071008181360f8900c14010700c0e1150a10760443c4c003400c41814020540246420402800403198070f540c83c403104c04407509140d003445030f00b00c41080542d0a901c02c1c0e4056400185c01002180d003806d0303840000f09801410180c885854140910009082c6900c15004035007040040c500980e151034400c1c06c000a0820290400109000401105a0000c050400c840c42801e101103019498140320b4100a24080c1258102928100c00401c001c0001040b004868003070342e807070a01d980c81b40c0408003a54120b10018000351000e00c414088869001c1110325128401c40d080021501140d0390815030551560802c0302e190842c0c10200000d5810090110001060b84020041071800d440090300300d00800c00d20500d0030703010401c0d0205281c000d912071038403503400410301902c0360390f03e4100038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 115426519 1250 115425269 115425281
    0x31409070f080f1905011811030105060904210c06060602030a080c0f0403061d01090309090c02010501030c06050903030d050126190b06060d060914010f03030206190e0f01 75
    0x100c00c1ca000300c00005080c01c40412081ca401041d00081c101101030442d4840948455410071703a00c5550711350490b50154135040c1d001c0c950f01d120b0304180c0032030f90000b010503084610050210707000c0d9071707404100400140d10804010034811090403054014038061000c0345c0720b17081c0207401440340307142000201341680c002028140030060f0b940e402c640750382d0361000d2001314000c0340700b8070300c0c8504248024400580c85420050940c00c01e5002419100b0025400300d0075141c08910079004540284e60500141146000b55408100c80780001e00c010352442da65101d030303202c01d403003884200080841ca46d02140e40901c100c44103901c0410b4144090750b10b40c031003903600020100f41aa5500204115041e40b0000890006421102c2005002000e4001d8499040071a4001c1a240d07011004101481c0c20702028407403103029040c072100005821039420300e8140d081c5410381000d0988a241c0100300002a40001e80039804200c40c000c5940070b80080b000da001501000c282456280102c80c00e150322141c0544c02a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 115427769 1250 115426519 115426529
    0x90b0304020d0b0c12090c150c060a0f020c030a110601060c020906040c17160e0d1e0203010e0f0a02040f050c0d0c0516140d0e060d020c0c0a1805071d010305040303140907 75
    0x2000b070a08e15035200300400d105130400c03020710380c20600019071103c1d0594421440c0340c41c0c00202610700841e0068160441c1d200d41d000c403000c11071050300405400c801f00165030144c142e80c240b0b0ba40c13000c86500000c44400005100038407072900d031f2450f80074040c0301d140201c5aa409810030032245007010401c103050380e00c020312000001000702c0342100d1a49030900741801d0854101112a080340016450040ca56004010590700b541d2680c1034101010401c0045608a204040242080e07048910401094130040444280c0c03650030038007440036001e07240040351402c40c1c00740340025110583c2c56041d200340c0110b40342c10080100c241064010700856061001031030700034100703490444640c2002621030f0040001a1500b0000500c10740307800c0d8070180e004040c03001c000e000f1a11071207580000580301e1741c082d0b0418141c0d0819008909045001c43c068541c00c00b646090100b684d0342152700144c141e00c2e80303001c85810940c84c0c501140074507021750b1021800d00040b4102e401c1a01e091707401160b45038418810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 115429019 1250 115427769 115427779
    0x2070b040b09060c18150301080c0306010909030807180305071503051f0612060b04090912030c1b061506051b06040b0106030c02030d06030c06090b0304020d0b0c12090c 74
    0xa00b04150101d42a8412468528581d040288507505031000c003040d003041a400c0614030310168060200c18004c1c5000740560700c01840080340c583d0a05007000c6043e071110700901c4c1000345240010345c103d030503594092998035000078540c00134000c80c10010324075400074015000b00340340407031040c400d101c1444508a250700c0c14012911001603010309110001400b5008504505060101034820025100c10800501012801a0700e41086043c140c0c860343c46047c036079603030714120802c124400d010040030740000d0404002842d40c1d0500540202d070181050b00f941e0700e00645020070845180c1c860301240c404001c400309040d86030390011303103654002c02d04491401652900929003000000e20b2502c1982d0051260001d40d20b010400e0b4003030b003e0207007401e00350702040c898040b81c40060311400780154051761100075a18a854806006502e0a42140003201000c03c00c00c00540c0700c0102c64401243e201c410700025a8840492501502034200e10f0a049102041072006245c0001103000303050300c1c2295 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 115430269 1250 115429019 115429021
    0x603101401020703061a33030a0f0e0601030b07090303121d0307030e09010b1303080705030c0a08040603050c030705160206090a0909021201020a1d0315010603050412030b031b04090602070b040b 85
    0x481812820f1500b0000c0d042800c7c6412030706404a010b184c102308103400204400c24103d0b207241c15a0704481d50b40903591f001400400901c0510441c458000841c0c0c1840e40f40c0e0350558600804410245d40c812007551344414066024855100040d511320290106580e00c6000341c0c58000d20901d02d103002948101c40100022542510810881e4103100318a01032007507030740c555540c40303800341c01c01d400545e060302041c0301c0e0300b611007000d00c5600100351194583c107540d130342000c0e4017404450018101c500f04800070b00c10810b0b4150000100c43d07541c80c0e192004004410a0b10000300c4501c1010000742d0010703a401c90000325840e00d03400800940344200c0b0707908500c584c64030b041402c074050400f96000003081707600710707004041034404221824503000e0161200c8500385010319113102000c0e41b04000003a0b541e81000140054007404105c01809490709000c105010030019644060018600307458100f00003200180d580d840e406018101d502c40e80654941ca002e0a082c010a0000c8030709a6a031003000c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 115431519 1250 115430269 115430299
    0xf08190801090b0d0b0c070b090607030e010c081f0b04060c14191704081c020c09060310020c01020c0a081306020601231206150f0603101401020703061a 67
    0x4010880c20b10f0001e002141030002c0c9403a0700c3c20560340070b001607520010801100020524a85905110700025402031919007840c030310060071120395001e42285a450440420a00c1381c0c0300195a4004202100d50356240e114120301c20000c00c419805030600344000100043d0907900300700342070322041c0510006a040b2a03281c0206803070340398548943d16100c0c101208840042e2820154420418034903554a06064941c50f200d480d00c40d00310381c601000d94012010359411541080b518083d00c0041c0c420042509000b40403a41c2c948002007a20066070300411007102a8100754142c2d808862640d086031070110b00e500700500c155000c81c4094000e10484000451410700004407139040b54075403d0f00300f240160226440707480c0c424200150354042e00c020303112000c030001000040c1c05108151805402102d0403010041020511250039004034001d20802501558041440c4210303449002104001c100100c0102d05100701c940004011320720300166007201c100c48440c01980540281c0e84000f01d01250 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 115432769 1250 115431519 115431521
    0x90705011b320105010306050411030a0209061003181103210405040b120d031506020c09220c060c1a01030f020d08130803071502250f0819080109 64
    0x8040c0180c0b4240c6003151482c1450118012101c96050307803000b40140c2028640c2c440d095030402e07131003a1500c0b40ca40d01400103000d080c1c50740002c030050480060010030582c4e400b05244001c001c00c4148150441c3d003101104038002c0e00101c611f00c100c000505580d070410324124004810040c4910f011348034103804141d030300350201001240d58012141441c00c0c103182070104006007a00e80b0101c0d81160090041a030644010042c540d90b03220384d51000301d110995480340c0700d000c0203154044811503010b2003950015458006c00c543c1c000c50071080361000604101c4551244d0716100700020a40806084009122a8020500d08417903100c3d1142c1410800e202082040420003808007414100c280007140006107010404654101d04c554040b0303040021000c46180718007260340c0302030016080040d009003001780f039840700c0f02d0003103880408601b0110150003410035486c50078200e45050b1102000b800c140502c908140102d40c4c0d000c0030041e42c5511241c80340e0601c201031080b4101292341e042c00070410580c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 115434019 1250 115432769 115432817
    0xa060c050c0712020312040608060103240b03040203011803080a0c0c1203020a0e040e030403030206090304030321020f07150b010c21180806041a01030804050d050102090909070501 79
    0x118000401c002d0741030030b40f400b022088903541260f0500c564802c2c54102c04d019405000100055200e0301d09526003080090161050041000d07101f03011007240d023064038580c030000010b5407483d045181d04c9566030310200340148040d411641d01e03050a40000c0c0301301640182042c0c800c00b4400070504c81110181e800b83d86403c0c3c040300045c90000b1030102003140c18440da001e4200b0004601d005401100b5501c08a81256910541100c09400002d018024140c0401c001d94101c90302c003000b10b280501d5500c0080445846489108000b4007080d80508041102c0e0140c805001d03080054a03910300e46441d16039000e0108010403000c4070309180340500150b0190240034081508408864500007070f00d80c503401407001e20140c0380c05004035600190300b401c03041c0c2010005052000000e1900e0704181c00e0941002c00d6100d00b580c03030b0092900050001640110a079001c40c1d40c10780c2c0700960590245091806401103801d402c0e0018454010040c0720100002c101003111820788405500c041d4002e240d4400060b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 115435269 1250 115434019 115434037
    0x307020705011b02040614031b0d081606060f090c080f0613061a040618060504050f060d02030405010c0f050918040f05030309030c0601060f02060403230703020a060c05 74
    0x105000c1040349500900049a1043c414410320080312101e9000030301316002500850300d2034000d44000e400604041060440300c035040417100c1302d681f801000240a00d010701070001e05005d00441d8001e001d951001c480910964480414080103450f1040070100c400580704142095040015801902e4050707240140240a803e92090070b40c0c3d1034109111010590f240c0f1100c0c025900c1e280020f010340f1101c181e0000702c00660003550740b04e00c0d2141c000c0905144110b10b500c54000301c041082003980250444040f0749065403d03078901041e100014a4900a00400d010481d0001042000b0000c042d40a26840c2445843e9070040b6140356404075198003a5800700c503004100154298901440002495070051041042d01076003600c035540c0300d0542c0c000b07941404242d807000c44d5011001c02c0c00c0c08003901604c0180340105100c08030210007591b424001c0e2016050200710b004015038411404200e0b00d0440f481014155103810031716009542c0c9850b0030707003030311502e14210f10000c01c80c0c0318104071081c041e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 115436519 1250 115435269 115435273
    0xa0902030d0309080304030e1309030810050117011e0e15010f090b04030b090c0d030228030c060e0a170c1501050d080c150a09020906090903030a09020109090204120c0b030702 77
    0xa1b45640e41682c007401a540f10300e40c04040480000c1c40c0c45041d00407120824403d40d01c00400c6e090564a0307811174401600f0407810706c10000c039010803c01a0860b0039046030184403a40c4c502c80100741c0c14030003540040d00f01a8180304e0090402c0404081c2040b2005410406e989040d21040006011a2080b08600070089020710400042010500c40303030600b030b042000c010070307900300402401c0002d942e98204142100560000403880410300303d0100b10603210441708029070000d45142d0f500074000392100c1001440207694085024122404000c1d4115090780719111442190407001010303402d421400e40601d0501c901103407000b20750b4105807142e04070381018001c182d802402d0b40e900103142c0c1184d0310322005441444120441d00f41c1e07100c05180a48911140001d410030580140104d149008005a026180318014024012400012294000b0b50706200080705101c0d0301c0120396003941c0c2d91240c1c8402d800414081080c05040c07401c0341d5050310440d0a010b5640c1e807280364000c4c900080700c0502c056 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 115437769 1250 115436519 115436521
    0x61109090703060501200312070c05060106030b01050a08041e08220f0b0f1314010306050d020d060507050909010315061e0608060d02060c0703060e0a05071a120a0902030d03090803 79
    0x502002c8086e01117040d01c00c064070f0500e150321901c1c5006013800c4445070300003201549030ba414803105101c440d01402d26840c060046500c1080042c009228080b001400c1100007000a0148207508106502c000802e000d21410300e0944d04080707206030031035244107600142a00e10030080c2103048050700c0890f0101038040821600c1d15002d00c0840e040442036018241d410060034111480c0301180d1000f404504a1841d40c2c00d513041c0005040b5641a08842c2c000d0803602c85501c0580d81c2c0e0480c02d0b0310181d010703801041c0e950b02e100c001c440798020454640c0e000f1001400100c02c101c0e080c8142030103101000e000304025907403880008840807120614102c2428451001d2004512030201c1662101d0007038070881c2082465404680243d1000782c458146400140c411b00411184d40141d0303080341c00e005c004010548003a25600e0711010039100d442d90041c1c44100b0031010103030520903600750302d444030010601e03483e000c0400c03005840c44240c104c0c442d014800d05480c050707000f0b1144104180d0485611811 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 115439019 1250 115437769 115437797
    0x1030b0a18060e0103050a150203070e04050703110a0908010b01020a020d0803060406030f0b0a0c110318031c0c170f040e06030a0605070509040609050405060402060f07061109090703060501 83
    0x2010301280e2a80c0701040c1c5075180400d1044449038110300071881744005000940c1142050300c140128401c031060000d00400c284904598403203010100f240b421600043e6588a0050940c024044d1300d0b510904040c000c00c88060075500302c203c8400700c034054002413200340c0f000401242c40349070701c0500a40c85031511035504040340744000039552200014000094003a241d403146000744100840c11100b0b99102000c1009004190103400120f96842c10b00203041c02e81a50303403a88074010700f40002c440900c15006002a42d400f003080c285080007c1065440b540e11500000348584032040c8190307500c0d54000100340c424024201110110300f02403131900d00b403030308014007004007000203444158940700350140700010884500c9514004c0c1450340304d03103542d04440d030107000503581554082c607401850f03c3c007000007094020490581c00b42c7d048550301d0b50382d182e5602148040c003034080080c080074507040c0d080c18618040c5004103521902120350707800540c2ea0420440070355105005041c005040d83c602900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 115440269 1250 115439019 115439039
    0x4050a03051605061801150347070f1106040b0718080105070207080a0f02010f090e01090504060b09150f01090b13050406080316020108040606030b07020a0b0601030b0a 74
    0x82c04140c69003100010a2551680d81c500401600c1401d44803d003c1c3c90015005000d1190342440204540b201400c245991075400d030f5810228001d11038110002007106262404001014a52860320301484004413040d00c02241c2c600d04070303a40000320f0003081105403400d024510744030b803802da8100142480e81d40d582d0348881034500902000284250a0b00801c00824400d0703200d0050f2480c5000020f217480c0000000386020400d034000c071225004450b1500100b410282d58a0580741c081c20310201e01d400c2e210080301d00e000d195004154118400d0b001145200654002500803030154000340a4080f0010402c03010440c1076508191607240340b03011800508200a0312400c1020504100401a41c0c8014042e010340c0928568000008402d6083c00940b41070310520000e0222480114289088a03600c0b03018841d44800107418001c0c8040000c040020a410410140d9400046001c1c2070071b01000196646050000450360844107900240c102c0d4440d01c66041c4c4c142008010940c0c3e9468004041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 115441519 1250 115440269 115440277
    0x5120408090a0e09010b03012d0b0a050d030804110913030c0809100801030507091104090207060213080105040605150307050f040e010e031e030c090f03070503071e08010504050a0305 80
    0x141c000c161240d001400c0d080003c0e0301c922a48506002003000c1c2c031200200b6084440103911b00b44c9101840002c024464682d03040d12226802ca0f010000d07a5900707110001e80c0c1c200c882d910840e880700d06151880109944100c0d002d00552162809810300d03403001c01001501d280441e5110480c2041941c4040800d00c03c282e00c8084c0c0e801394802e14941220780e408500c550030712115a00100319040c004204200741044030304000d104140c0100001002d00540c9266407003144100448144c0100700c400030300c5030030b0741213444504d180080319040310b5680005a01a1004030b809944242c50b1a0015141007110022144003507130040107020000d080a0812542c910ba80b52442e0700141d41d000c00310480c010920400c3d48484150300119264040a04210343c4120100311a1100c3d80c424810f20401d00d42480079501c9010044492205800d4100082480c001095220a034188a11840007a4420044081a026040c10280d150901e610784540c0c1e0f0903500241c8000301203500103592240400d100758007034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 115442769 1250 115441519 115441537
    0x12090f030f030603020402031314060402030303061005040f0e01080f210d0902090c0319060e0f0c131806210206090604030501110d140708010504050702030903061005010f05120408 79
    0x81c41d0fa840e5004102240c1040f110f80503084c1c0302100070814848903076041c202019150307008020519056000c41d440c0e00000e443c3d640140140e1741a20304240c095001c0e50060800d100c509541e03e6958090030b0201c103000e03c251030180c003072660301d1814180c1c0403a0348a100a4000d0b4402503001c9a540d019002d81c2c8203103d07075110580e1b0361042000503500c10031120300510208001d2030b10ba0030b1980c0b4212a12038034035031041985d4a00a4200081c00c40c046c5044d50044401c621000260340c2d21090008a10a40c140607082c01c2e2a03400101c1c0340201f01c483e20408049018040103641d03124140c5091125602000c0400c54408180c4c503001440d180d0002c106e00381d00034211a003480e999654079800d40701c1c071446d242d40120740800c10071301c8101e003403098100d80082e001c0100d10714109107030094003801e41030180b035019607221702c002010345000b08203c8944500c094201c8803185090382e1030340c1241d482409494002a03481440300c0046200d0020755460101d5500205031688076551403500a42c499448 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 115444019 1250 115442769 115442771
    0x7050a150f0e0112020f03160c1707080c0d020106031b030b060904080417010606031a060702040b0420040503060a060b16030201060b0a0e03060610050703080901090b040c0612090f030f03 82
    0x913810380c1070f0310740054008941c00159403a22800c00e556801003000c0b814001104000800d0460804903041d007681401d9010b10400d901e698401c40e00741580244944280b48056105066400b400d080d8154050b00031680a000c0294855541030160b508804161001078165002080450100c0c54291601c1d0b4110b8070905000e80350941c3c034111619051010050112165034580e020004550076001d50000703031011140f00101e01184400003100d5004416001e8026683c03400e103260300da02d695102480e10b1000660500b80400840e60400e50b99000b801858041d0080c0004180504401e000318015111300012040c10054040003810b40c1210100c0140c04664035031100144044201004000c00c1c80d1565641011449130024180f070120080c0203940038508040c4400303025580107058030507103a414034060105407507102017140174043c2e58078058054040d09040c0410000b011018404489454480d40178001c102c49050040319410700000e809a0007440e1108006403140149030000001410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 115445269 1250 115444019 115444037
    0xc0103110d0903020f0c0102030f03010b030a140c090111030306010f080903130e0105011b03080a0b0406080d0302030402012304030201200f03090a05090118090f050a0507050a150f0e01 81
    0x66034034242d9001002c01c0e0050b8114500e1704840b010248001081544280002d40c58070322200d801e110580f00c1440f0318212902d000c40130504c4824140c0080c560a000305a50b0a01401e0404010090368400025940800d4031040000030155000c070130b0700d214010584600c0f81146a524044e10b2092009203050303803c0c0400c210016903446111802406072a82e10071090780e942c1090005004550000c41440488080c0c656040001e94008820342e8014500000416500d0014001c100945940c1d000344056000b451a4200403503803550166200d03900036600e14010b480401550b40400103030401020032800100014809540140d4604601c3d981c02007600121210419042d030400810306800c01140c0c00014041d030491400200c842e007e01400c403061655540b400c0c54507a05200e0038801d40d60b801e5160a07154042c007007910340190300c00f074115058a541c18168070f030031501d0700000d002d0548181c0024101040e007042c0f1003412a1000900d455482045103000825070310499001103640c100038601d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 115446519 1250 115445269 115445287
    0x209060f0d05012607051309080316031503050604081b06090c01020d050a080a110408030f120a0207050c09150d0c0f170d0302180909031b0f0c010311 66
    0x90014154161040341c00140b035410020301d520405101e8040b9420607000700203040344620085001c10840320112100765140070203640c0f03103003c0c086021018010210100c10004a00d44640428103494401da80c00c00018035211444200e01c0441c0c000038003541c2c40000000e00141a100c01400d100e1442901005005101c0700498a818021510300380a034200b2a0310741240e5030100015000300c105030400e9418003099510003000c81800401a8a03e0394481ca60f14580400000889000c0c00103030b02500d44c1c455211208a0191344010015520104442c0010f03001524604c2900c080580c000060a03502401c4020015007960280c00c04003000920010710a80d41c2e1030b4a664801144509142707452a4680050344040113407079803108000d90703c40f625000800354003080d0242070002d581001611a00e04452000740110140f9099811003404818405902000405041042c800e00c010301010240700e0101610750001510740f1030070b0361001c40309110344c0d80281c020810b00b40c140081c87c1c1c2440d03001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 115447769 1250 115446519 115446547
    0x907060822020d110301050c04050d0f0206040807121b15030209031c02010902040510031115090604030305040e0901110f0a030e0d0e090f1003060f0b031608010b0108010503060a020906 81
    0x10b210443d9030071050f0104c852581401e01903264440100e40740300d4141403400000c1030005c041c240000306503107101c444403001c654600080d2000b40482d0301c00c80c0e4450b038446c1c0913031803503c50001c801c3c2c81e09403602c082280080c2d4012001401c0d0307503400d0b105a401071300405040e03029412901085d07915014100c488040c084e41c024044c842c1140076030010801e074074540140021114003502030026010121000d0011030400004074008180039a10b000c541c2241448212082c00703202280b50b440304000a0000038503034084003400954501c0344100c010390300c40d203102d2801c030752034400000000714081c05804190314001020382480b00c018180407440b9030324501c4c0a411700c10809401004920742c07018052a0b42003403803213a03600c0310078650140030301d08001081e5052810180b000814041c0c658150b401007040c1ca410090942e80060100c4200768549600191049103901803d40158a0301d00e0340043c641c40f80001074100c41c0080c002e040b068507038400703c001940c840052140c020744104400b041c840c82c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 115449019 1250 115447769 115447789
    0x702060c060a021c0216031103040905100e0114090105060c0102090919140f13140303070201061a09131802060708090102190221120d020d05090706082202 68
    0x441006a4904800034180040c02c01d03204d0400503244140b04840040011815443c80d1300d4040c18030960b2054000d075010b2440c07041c1c4e0400c15215042c0b13001e0140c1884c030003031908160b0f400705403012800c4ea00c44034a0149022060030003039101112070f00420190030644028003111403603c2c00540303009440b038042a0003540664940d001031800c010031740c3d680308081c4502c28201594034121011402c00e015101c03040f1a010b4480c03040c2004061402017000b4418001024800010080e01e46915203820040d0091907103116440c80c0c4103010768a802160303070403402c43c0c6000030300514552000e07030701c10704d0500280302e140c040300c01d13800c0c2d085650b40150782c841c4042e00303000d813061054a075204c2c84a8002403c001d011085400181d03c5002c090005a996000207600c0555030304603e01c814003000d440c0d91502030031400103144203100003020a004c61190700185a500020601844035407516189a640c81c101c0d40324a50003e00500042008444050114420300031100400140048160009175280b84 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 115450269 1250 115449019 115449031
    0x3021c0504080106060f020a0813030b0c03060405010e01050a0b2512020c04060e01030b07210603020f06030609070813060213050f0a0302090a09080d15050a17070b0702060c06 77
    0x80807030204841002406010050401490301000c04040490040d644030310010000b4604200456540c13624044410540000d581000800b0454204042400c4d10350b0300a550490085051100200b60083c103c0642412100080c20518820f4a801e4860201d5008021590304a50211407201001814110b10340715003802880030f2400e07107101d2500640340850600101d4044c0d81407602c10003c2314001855203044a030000d4180d03040303a6070391204984000c02070103034014901c0810a9604010300c00d50045040d0391085d6400008841c8007420000c00d0702080351000c1e400350500000070503151141110b82d0f0040d002c00074810a1785299a1420240c2e0405011440401d408200422140ca42822540c0c81d030f41381541e100c1d84460450700410701c02000107004581107030321070300c9140c03c00900038212400400140f03410000021941205404100d1718840c0e14450f030326042c1d0110b494188826200441e8082c0c00003030440c2460a00f104441ea08182c02c266032001c0b09109042c451482440001e110340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 115451519 1250 115450269 115450277
    0x9030106060809060115021b040f0f1a04140601050a090810090b010603020a09030201081f08010c021509070e040f060903030c02060106021504080318031603021e061303021c 76
    0x726219503d00c0c500345050780101940b0502e034000301a4a50080380d9048242d041c030307004208003403210001c600030b407202d0030100f01c1503850031124481d2071855600000c143e0710000e450080000d40c031070810003030704c50707070181c2a44100d440300114500398001e40041110b4080c90034481111640c581090382003500ba841180300c00c03500c0726075503001c00c582003c0751805890103050840c00d11045030700c0204400d409000003030500411002140040301011401c01005103003e089140c01c60b2145006030207001c900341c4850240c41152101040121416031462140080000038103107186040c080344044400900281e034565824130200002c0b030030074016003014a0080e1004a848c5d040c4110082c60031005078411003c40d00045500412004500038494000d070700036901c66140e40760f0144629041460110312401d5220004803400700070700009034001061b01035003c1c1e03481046004010f4840309400c1840000760b030880c000060009d6811140e01401900910442d035054509503600c240308840303900b4031304c082 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 115452769 1250 115451519 115451521
    0x2031005040903021903020f07090e010e0c0603191805010902090f0105030a1502042103030507050f0301030b0a14100e060d0b0f1b2a060402130f02090301060608 71
    0x5510041524801000256020010508151002900c552011040044400250f000841818800c000c1c01e64940714020555440039a80d00403003000300002955035406500b440000044108003080700e001c1c1039805042c0354596034034004c0c4080ca09405000c7c1c0c4c4602540c90300d42c503001780511002d80c07500a2085000042801030390041014884006001e441505c1054005014580b030220701240b00b954029200103000300d045103543c1c0a0302444e04030482e08120203030452962280c40c49003400c124060748003000282c4030040d045030f0621648215810b8400d0810040001422006600da4071019000000600c10500501c1c2481d50105581c0e440340309003030b01e0f03051241c00468601d441e0080000c44854960406e1507484e140b09440080012074600f0301580001e00340c42c000fa50300c84100848101950395a00b1411101c0583c04080c520144103030040c040076045141b002030f030a4010380c0c00130486113109a0800c840005000400c5500d12895003d0002a002ea1001d028810142c0312039142c080d81 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 115454019 1250 115452769 115452781
    0x1052205010605220b250206070b01150806010c08090d0f0b060103063c0b0c0d030e010b0109051306080f010f0b010216050d0f1a070f0201090209060d050a0203100203 73
    0x80710001d1482c1c0325000100100c1001900c50090071506221003059130366041b49001445420040c01402011350080c41c0000c1000801110041440c140c5046211900150025090858141070119003250104101401400c08510fa000140c903180743c0013000900c1410166840c100b94803160501120000b001000344605580c02d8000d0401401106120000b42146c80d807404a8510f8901141c1c1c070a0f6980d62100038883c2440480c0a02400c00c4842043d80c443c0340c410760961b1403207504502d00000e440c1504100340d425042c002e58815088c1651044040c5081104002c51304590b401420300107540c4070349c00900d591090064451050381d113400040c5001b812403101c026101040e95081c115006281e1003001c9a20840f02101580c009079125424a0041d00e0500d82d1103580b400b0180404040c842000000c1c2c3c40080030512844a1350f550014508420005038241c40821034001c0d440940e190001e240c50602d040140c0b80316005000300c8440a80c2500400e0a0191302d01c043c2100903000810405 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 115455269 1250 115454019 115454047
    0x9040207210c0f080708210402031207150b0301022203060506040209060a0e01030f141e01080c0d0507090c08041704050109030303050a06090c05090306011403030301052205010605 79
    0x3a00541030521a80e4001c03165103c11010b1510b80008024020110340442405a080c058034451030310a041d50012460510305010340c000c04540803482403040e8480c001d49a4580c2c403e40750302d0b0354400500b0361004406401903000c2d11620b980c071134040d1750130300c214135240d80d034070750b038100c040036100c0c100740c0c0240c21810a0340603228000d0409000e2401009816403548a44044407140070b000d01e02460481541c3c40101c001e04402d0301d1800080d03003025520302001e20340004050283c2c1d041c224107040070050101700c2011100c240b1588280d80c2107040070300d0580c00c001b50000300c000d105030244c506081c1c850014034211019545036400003070403581080b003008481a596015154155440780c145407174080000c1c4030700b078203010040400d40c0340c6020a030444000e0304003001828804006003c0715081d110010404d4026025491191241c0c800004101800011544281d1703409000303180b440e030803c001d101c0003e010b01181c0c2160500484180c44296452081c81d018100d10303594180d41c1e180c2480a45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 115456519 1250 115455269 115455323
    0xd0c0302010b09061f0216030605011d1012020307030204050a0606121505010c02010c0f12200a17070b100f0b03090a0b100e090d09080d02030f030c09040207 69
    0x34080c01a01c028880143d8a60259054500d224038000090b1959017504a00b0b1048041c120040c1c1608003d020080100c103410039416030b40c100c0c00503041140800500c0e13071103641c19507001d2503001b200d00040c030070039074620399000803180050111820185d496010074121003080342c88501090750f5945c02d00c16264000e03e40200c203a841082807240e100d02401131400b60700c1e0f6209050502244a1204c81103900594020f60740607048509813180390345500f8500349145d00311200c000042d02c00781c1d05401c04660100008120200240180030030403d541e0303502ea200303402d01c28142d03400400b4040c2c01c000070040741c9900c8c030403412013126116032840c1030f04002c009c860507003118294500074002c0100c04100007079405002030b0081e0070340700c2e940c0b00c0300e0b100c000d000c0440d002014090246000c05c0603c810000b454261400d507641c070b0345a4150f569500b10b0719988180741c200c2c0103030800c01880c0c200028a101a6410540201c1060315200d00c050000d41241d02c0794000300c507130092a48403041c044911130501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 115457769 1250 115456519 115456541
    0x207170306040b030a120305100306091b172107080406020f06013006150803091516082104030c060e07060909090c05030304031506050a0302090601030e0f0d0c030201 73
    0x3d1a10000551700d4001d900142641b078800c0503035500026601221640300b203002181c00c45c600300551041820100040c0402255902c802000c0e8a8000f444100707a04050420b8030b24600a0b0060401034500c903600c41103e0b0050035250b640920100000c122508010300042941c0d800502c44e00b41100001420301605900500140c0e0011040d40c0468240121401184c01c2c401c0e42d050b500743e2145000c0340242030754407002c0d81001c1c01c10004940054004002c14282504a420500c120401c401c800ea50384110f00c0d2412aa403c075030780c1140042d541030090718030310318228046480d100441c0014041c00000b00e0302507000440a01049003401034510801c2d040c0343c0302c3c03005444150f0801e80d001c2c103c41014861035441940c0c0c0d00090f0705210001030304001402000301070b20741e5542d4a040c07480315420120181c000491800034009050710b80040e42404032035019068460558500e001580140f4040220b100a030060001036000703038006100d50306102049413075041403507180f410000d0840c0c07041c1c4a5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 115459019 1250 115457769 115457773
    0x17070b01081506060307050a03051315061a07020f0613080a0b01030b0601020c010f0507080c06070917060f070309051e0f070504110403060c051e0a0314040209010504020903010207170306040b03 85
    0x2e028803d58414100d0710300423114240072840362110881c20b00442c580940203894840d0580b822155448660040c0c41150031020403001c003902800c07442c03100d5100d00340000354400301d1502084001d043c0b00000c1d0015103801d2840e0361130641c0d115003c0742400b140311012030312142104010701c00c0280510384150808001e01c0102140f10310440042c024501507241401403103800b042c1d1908011040c02110390812030b0720181c40c080d04180f88080d00c2e6001600440c00300c00aa0b080442501800265691003980f4040c0301c2c48a41d250003105400030404110b0540b60ba015501031200190050301080f80400300f039400804690000700b2006050010300d40029101c0e50802d24202c401a030100240c80c113403600400002040c044145044d1041e100d200c42c2741d80c4011014a10702c14002d001c00c090068080e103600d052251100b5881d01d9100c400c02202d0080d4407d100c40c005008504003036002d4424a00040c000620746841c83d00ea407008000b0481c4603000e4041c000080241d42d0900b400b6141010400b900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 115460269 1250 115459019 115459021
    0x9030f0509220b03010e0c0306090a0b060d11030313140d02060306130615091805090604200301020d0209040c03051e0a060b1b07080d090317070b010815060603 70
    0x100180d266908241d41101c8003a6507105000c050a80d58410610f05400400800c500c550056619440b03900da440030038442e00601000650610001c0303006c4441d2a80300c2e19070601540d80404000740ca4400680981e030140c0360424005030740d00c04000401f212009000c0e00c94681e8542440005c103030349000385003802004d004000500586405090b0303604004c080300c00801c400311201181001349000d510000c8109450031425001399000103592040c1c9401d1103a52035010f020300c0c05201659416952050781e17510400010300440d4001c01118254000040b0034804d0701501000a801e80c1c001140d03000150ba030008892500b0300c0d044c810301c0090a6030382028000c902d055400700031014001218a008a5a0500003c0721680d00340c0c00140500343e058491900d464400480c180c0811006543c0d14482c82814000b1481c180d0000f01c03258214617640d03d8100d03050555440c140314006425244003181070501aa400082c0540c0d0014040d2800e0b0000780750107030201052465040780944594020b401c100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 115461519 1250 115460269 115460287
    0x4030c0c030213020903210d0203041104060b040e0a02090a06050a1707030605130509060c0d0905150402091003050d0c08040f080f06010902070209310302030c01060509060d120507060606020109030f05 88
    0x80684600c007445035030042e22a692f0f8140410031640e80e0540036406458130202182445c0041c01801c03c1c2c803020441004140ea80c51856001c80c0b06521141d82c2c40600ba5038108000c5225400814103840c0c1361400d64400c0198003001e140601c400c1e19268040fa486400601c000c0c10300c404400d110709007a08040c80642410f4149603150304010740146134100001400c200360b54a581c00042c0c034150300000320340090000c5020144c01d01d408ae90101e114010031004540c19543d00c1e10910140c0e500f040181c42c8070b010224040e945000c00c140111400c0348103000c00540300081400f624000c2c0b03c0a8054030031000c9109800341822016004280060b205002e601c0258030303143c14090740101d200600001740341c100180d40c0381d451749004110712500340344e4641c0d03010550b02002a14403101c01d080240b00d010340351000c1210280040782c617140c028407000100c070f0100c1e0b12aa6617a00c0010719040840c605440c40d20740b04107803910707900300302c0150f034441c540d00007010341c040481d003002c034281c1c80c010341410804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 115462769 1250 115461519 115461583
    0x9240f06030c02070f08010921090501050c0106050d0b0402030d1103040603020a1e090906050f0310050703141305060c07030509040504020604050a14040b01110604030c0c030213020903 81
    0x1801100c0070503681d000075605841c02009940c0280940d0544050041d907501c018a021f0008400c04540c0d100c001c035041a518011a1000c00c94542d4a407034540a030390400c0011211034011105944a642d2030f210005001d8490100e081d103501c0c000c5144603460302d0280141860702d03100006072f85c1040b240c084e1001403d40c0c044103a80550740203180c0980e030f401d04248101c846052201c500340d0890309201101c47d603d074001c61200c0407100055003c0c80300343d660f04100a41100a10703110b07505034012081fa00c080001a9004a500058038240050040714494210202c2e900454a41079001003070510074040c400700300800c0d6445060546a98030780515940d0041c03050143c42c460038000c6449601240440d55460192005408007810311040c20340da4818015100907044c000c28001c51410701507500075403294600c203100301c0110b80107000035211603804941d003285940013074a1f843c0c500030000c0010703698501c282844000381c2c000541c5441c2c4600c01c041c103100c0c00044260b400059031121305088584 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 115464019 1250 115462769 115462799
    0xf0108061f03022a0a11060f0f0901090e07050f0c2806050108010501050607021908120403020a090b01050f07030e18010603140f15060903030d05091002040b0d110d060924 75
    0x10252a80d5070114412007c690640180b9020214141010070b504040340032040181c000a00e00342c1c2c0b10000182d030340e0b0100f1000e8105890060000c0d404200510520720050014120b28210700115000000d003000907142030041004100701c1c4858000741c1d1b03000d100c402d00030350780501420402004954034000c00141c1c2d03441810002801280f20888055403034104c00c00d600011701408003903c42e01d903050241e8880c154091f0008911a40040e040840e80c2402c900c00d0342075404068682c0c4d071425450690014040d000614220100110800c0c4069503886443c02a04880703030842050301e0550404502409641c15070032011041d4042c0340401004e50403400c582900f2000007020303003200c905d201011542a00c03880d4040b94161200003680529040180e12552181501a080d101d00c00391140b0030b00c082c1e00c19403060952100050054101440d0360381d200e444450b05514005c2e103031542644245042c8c61240d48509002c0b65900300000b005031060812104d8030f580001e003000c40354104071010301c241d49 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 115465269 1250 115464019 115464023
    0x10632120309030a08030115030e0604020d0f060204060503010306180222091b03030e01140d0c09121109010617040f030e090405030c07060e0f0108061f03022a0a 71
    0x1035004002003800140119000c000c1c014090740c00c011203038141940e00350b00a1242901440da0307041c010203542c0c802d01c0b035004503541c1d28000d400f464485408111032800b1164094661078003d10099000500a200600c014552a02c44230744070742c03450400302d08503000d0381008034115901d80c44440040e603d0440c1c0440301240107003000006602c0e0400e6a000b0400358100402e5002c1d040c4070006032070203440b0104c040320320a42e41c104600540e40011108245155140b212140051000c884039400580000b611400207180c120303165691100e4580d22004001c01c251800c0c4500e0321180b0060400d2140e0a003d08402d061420303c0c181a00030305200c0000040001e00407005040c1080d080500c204506041120000c210484e5428141800c507126403003012408098810880c0c0041e1300d40c011500d400c1c0625004117442c8103035640c00015200158010501940000440c00182d80c000c42c41c0c441c0103030304205d9a00161111508009440b41000100a12558106089074420b80440000740301b0400c076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 115466519 1250 115465269 115465279
    0x1a0f0402091b0403030201020702040c09050303070b070219030c060501060509010c060506030a050d111902130c030e0d020d0e2407060902040f0515040c1d01020a0f05010632 76
    0x1640340e6015151801203040b800e441000005400402c0c075905402410300c50f0b0080f24100302c3c00804540c2550b01c842148075807609070704240a003a000c1507042070a264070040d14010f60710568041c815100032a08001001c401103500b140005060001e98412071b405030000b0304186140000d10310000c3c0c028503110b000106266103402c0013480c03945043c0700b404c00c150b074800200c0b015030309041c00150125107181b50b0680c1a120324050b00d14000012140c10075025000b52000e212555185062005400442c80b09001c1c5902c0d48030702076044008200d003100c00c0b442d5030701600385001e0380d00380102000800300b100383c400e20148a409542d60b06015000a800c0c0005803883d541e000c8510b04480641007440c0d000c3d5106107005980d00c01e85174103400c0f0920880da1140c800803034845c1b04041008883c540e600d0f540004912211039042241c0700461000800d80500464440301c80310340e207030001c81e0a10502100e469455901c1006400c1070000c0c1100f441c1c003052031a20398441d20f2404a00c00101c82c4403194422 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 115467625 1106 115466519 115466521
    0x1e0e012606010506070f02011116080d080108120310031a0a0f02032512051017120712050f030f010602060c0405030a1401060e0a091a0f040209 63
    0xf90300010b05890601d1055210700540c140150700c104d0503c80c0b40070070090703042000c1150340d01030490303400c022219906282c1000d05081d4002c032030105020b50700e4014000d10701c000c60403140100c01d1151154699890a803001000c140c035602c06024a440e00140080302040d4000442c0309800900c1e080c40222000b0500034202c0c80308031400e5031a203a5400203105040903048598545007082c1c13905050240445012804585064448001c01e883c0390208100030180394880c00c5404100700050a012514100807034042c2c17052400040c80c40140c031a2580d4454040c00c01c1d0f0301310090a00000307841e40350a404100c500340d000e028200141c0b1880f400034850000e07010880c3c05981005e009007d50030003a940d110b806001856030a43c45540f508008200040350b41d0360107115122034000807a80403620b003412009031800c65418441c00b5400001c02c00b24841c0c01009641080c0c4c1503800d8030341 = true := by decide +kernel

theorem cover : BRFrame.Cov 115287769 115467625 := by
  have h0 := BRFrame.cov_init 115287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 115287769 ≤ n) (h2 : n < 115467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
