-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:52:26.776496+00:00
-- url     : https://prove2.me/submissions/94b2fbf9-2396-41f6-963c-3fa3ee62b9ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 183633093 ≤ n < 183812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 183634343 1250 183633093 183633097
    0x50f1309020903011a010504030f020409020d03090e011a070b0a0608030408010e06010f030506010501050a0507051e0d030504150c030b030a080901140304030f08090f07081c050f0904090215 83
    0x440349540c0966915420002c0500b580c4000400500400d034059a503044c030381c1c200c406c5408980d40b0200c1800401c0c220b00000d07008100da1480690040d404000503420076501100c540103803442c0c841514050f0343c076000f1007110b000b41c0d00d003114511101044050049030740c1042440c0d0041094801090340c035116481a41507800980c402c00c0c1076074403100e040b0240030040c00704d14007418845000c0009285180c841d103560701010300c03445051145c0059504041ca100c0c504540c0c1a64010040792514810a110fa4541c112440042d154900038040440b501714030178000c2c82c1c0103d80080b61645080403440c070382030081074841110802d1503900c0d0445501d03524280a15407130980100715070394594078004000340c00310491000125003a8401c00c02c000000c1d030008a00384e400201c602e00b03402340350f5038040198a42030989030000410f100d080000070b1503450004800c5038494603918414240100aa816a201d00680b507901089210920509a03a42000da00c03010800c0d00041c0412021584006011129 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 183635593 1250 183634343 183634349
    0x10c05010b0307080d030b040213140a0e04050c09011409070e030f0615010e010908100b0111010f05240d08071b092a320c01020c010f06060f050f13 65
    0x10390001207810070700d0b0346c01d407007400c48850003500c0035841c10403002080d0840725058040c044c03001110683c1e01005071100001080030381206807450002d4106424200c2d40c80f07801400c854841c0c42c4034000440d4414685c0c4d20345408030400b81c03018030300b5104c1e46000e0310922051589c164040c8513115070310308400c078100403e41c0240d1410405015112034a0001411504038001f0380f4140650040104180200050f611403003514006000464580c02001241c00c41c503c100691025070030059514180107440d070240e400350038040488080429814060700b6160900d04200c3e5019588414074402f0038841c40080051910500c3c03c0d0300c0c103005c0312081c6425800b140c2c208070034059541c1c4c101d0ba60b0003000c5180414103134a601042c0080001003c0041a01c0d040f0140c411040300d0703c441044481c42c80c07002410b503c03139491010949860404180c0c1307000b5000606400c1e565030030002d402810400c103218070401d881c0c8950307892072221160074003035078140c0c02800300e410664010014030307075405040714210002d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 183636843 1250 183635593 183635609
    0x16050c0607080304060c11060a050a02130806060414010b0f180405070906020709090816030909020c01090b150102070510020304051008010303030c09140d020a050612041a0c0702010c05010b0307 85
    0xf64141404c0c41411145d6241340d84041c8000c14041d03505503400000c01c0c039488606e8100c0860300d0742d605d044d0070010380646e0800c040c40c154074800104142c0c2002c500f01d403180c01c0640d030402040c40d03980b14051281d0820700c54688402c0080110200c0f400d881c0d001403c07144e07010103d090f25091640e000c9400c0321812100040000d1580c032041c00700e03c0e818030030700004280001052010304050385071a90280b103070056005595400c1e2400d8800c040c001c0644070000c0c83d001c0c0085490f44413000b10079000c0d012455086645051910000398112400381c043d80012030180e000744081c504010501c007c1101c4000128107611080c00001140d035030301000303811042803580d02c1d005039526518024007900d0305041e07000706002100c90705200764040c0c0300f401c01c0134440c200e95804640300e403800420a01610360300b00c0f940003400081c400d0320b07644100840f0b80c01140708a0401c29903410b41148560f61000507038511210880030000540950311840c0f5200100e0302503000010035504200009243c400316a0142c41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 183638093 1250 183636843 183636847
    0x150612180506090f010e060a09050c090a0509010c020a05070b090607060e0109020f010309020f012015100e010f050607060e100e1b01021c020c0907020102040509071416050c060708 79
    0x1c403c032014803802c0d0201400c10000d0021620038440c99803a4940209500c20b406d03540ca490748107204003000101141d02029150380c0c1c8a0030b15003041c5007e080100e644400741d42c2401c1306e800340c03d0310024088e402c594020010706070440c00c001100a0b941e01080031580d02400034010800400c9003481504045030701d6000004030a100c42c030501c2032140c2200e00c01414107244c0209140980c031234000c0340c1040b010920344910320011012840d12003c1c0310f80704460241c440c103080d000d51007a111404d80d01400c841e600e120840d80d901da002203070500c0d003402882108050a00e00300081c0c10300d10050821036100383c40100d00d041e06154100d2a16072910b8005008a072501c428040d1a40c050140c82c0e0003482c6d0b14000d018074002c07000042e503241d001060300c0010014161070118164401e00c10206003e60003000c130440746c10b1820000f400b0f0f400c540541b9100741d402c00046203a980c0134181c5200c820820001e4a8202a012104481002c0c07500109660502519a10b60402d544120041c090079201e005055 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 183639343 1250 183638093 183638101
    0x10c050d090303020607080c030f0408130305070e0f0c040e040302120703020c010909021303081303020d03050714031e1803010f060f080c03061801140f01090f150612180506 76
    0x5d1400d00d01402c5003003803083d140e0900031407141c40b104403540000c0944041046486500e041d900034458100e208070014032514000c01040808110300f0100e41c4042d01d089030607181c043d0b0944001c0020b441800500004001c10440103c010079442c1e88240240147e54001500d01581040c540c0080801c400581100a24020640e00845a0005021405811800d20700c2c100c6900c0d04c181c0460002611701000402c1c5808045105c48407580559400b030503002d25140702d460042c044c1c0c1c2120071304031021a15444900c1401030b001040e00c585003d2604005540303038881d2040c2c00c03268402c26001160450400a01885843c24090301d8400021498005440342c500701c91501c00c910250854001500951000f00950b500090b86035003004d1280180c40c401c4216441c41d60040c803079682c1c0000307112520410400101140c48946040b030700e400da418440c1034450500c900c105c410ba0401e44103006a000e2040c0103d030320840e076681001852100002d2a16050f100b000081d5103c10401c6070326a010714204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 183640593 1250 183639343 183639347
    0x10519080115061d060906090a03080a0f11030304031d0d05120408011109060a030203130506070c1101030509060711030c0304181104180f0f050a0f060b0c07090b010c050d090303 78
    0x2013038206000e03201e00c0d0018152403002032018810280018425003020a150031b01340c2d00c100e815402194171000c0c255841100903c040e01e60a0041c0460001c44d08080032071540b000084122031041354165288070003258007110f02e41446030101d4031142c0121601802030000b13001040324030a10800c0c1c0440648481c82d214040c0e095900f02e0090854100c82400720b110243c139020300303076858401e49050241e22592244181000c01c4c01074a0b02603d031f07104031824090016040750b600120300e030081140c844290180b00054040d50810350b654222984450009880207108545499003001020141c900c1c1070b50408020340b864011f60080c5402840000003d8a00c164601c100710400389403001c1c41d801c192410b03e01004819031766140d85407031a11805401c03038018080e4003250740b03202103c80402403800c000b240440101182d4203c004030780d141101c04148684140155203c0b2039506000702003aa05044503c1c019040c0742c01d40a06000b2500507140016400388581d0001c00b61a565500340a82f0714140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 183641843 1250 183640593 183640607
    0x1201050901050612010e04051609020d0513032c030d02060115090e04060b040209091e070201110d0b030a050303130b100f0302010c030c140705091503030301051908011506 75
    0x40e11600040240104000401c4003045c1150b00c442d600c0100c0303980b00d0410a0074041000800c0b842c80311140c03400300d00c214159000e4000340c100f4081c02c221541d94080c1c083c500303985c0c00e8005800714040f400c200a101d2600b0041110754000041c1105100b600c000119103003018000c01c64015800500051224822084414402c00b03024500301c003440380f604004010412015101511903601d40000803c0c0e0384458040350303060718001c1d044683c81d03c0c0078914144c450040a40c0c83d13064107000d0000c1031134079105004404450a0b0350803110701d00004140b0080041400c0c01070f0603014001d00c8140008602c0500143d4412410000c4003042034078940744c8181c050b0f600030302c00880c01c203440d4803d21006000000740002e481c1c1c282007490b4107003142d09041d1100051880300501d0003403200aa6081c40d8070110740c2004640307041c0ca440c0c15944408000f030810024581400b41c040d07000740010403180c030f098105442140e044034041103c5585641c007444c2500d406013800d0384910180c44082112940c4688 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 183643093 1250 183641843 183641849
    0x16030e070f0e0705040305100219030b090105040b1926011b031d100b0102100203040206090423100608060f0a06050901090915030302070b130621021201050901 70
    0x3400c0c103141000300c0514440070314002c0c901000700303910000354a80c1c000e108444c09541c11000701e6216140d07041244001e5445551070103241c05010400a510718000e004182c103400b40180000403aa090506120041c00c038941e2056115400250810f0001c038000520300c0a4000082c4411400c0301c80102d20306080c004020000c03150303140030407807209040706801c000483e65140c503001c05c1140c1015180b56800102419010590182c44443c4891a04076808800903803001c0c2c098030303000c03203244083c10202c0c017080300c1c0a03420004c208040c05040c070701b95100308156082c410300410f034104100480c42c07568104440c8601045441c003004c0c0700203a000101e035a4080030488180320b0b0380c901040403d003501300070b01c118814018040b0b400c8800b07a0003982c03104043c0109200401c5098015aa030040c90f070b60030b100a402500501030b01044a650b41002c031860100c0004001c40d80f136240440072944030141111421314080a0b110000a01c030440c0002e000c058030f4030244410550420040041a910680c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 183644343 1250 183643093 183643121
    0x2031318180807030807051b061b0f1804090b0103030c0b2d04020109050d0b0a06050d020a06050f21060f0303030915090a060912090f0501091e0803031603 68
    0x9490307080003502d4002194141a07040c64608019240c802042e501805075020100b982d41d03007045000758105000030150300c240540ea88500340c0320322140d11f86843e48520001d189007450100701a5040100b008011800341c58040d000080d41c1200d91100a4202801e070030490024486901c26004e0040000c0c11680200d11aa4200c1034805022107603080c903160422042c0808610400082c2035a0041ea1000000d003070181080124460900d07248004460032921260064a01000070600742007114182840a60140c01007404504106040d08c640c5c11030f0200c0b0b2001c0e08104101d6050040150014459004034003401081d41080010001d0542c1000c0600380a64010b2041102c030000000c1c2d0b04224000f60b011003002c40d103407200c065003080c0c0100e2025003018100f141e62410401d040c2d031008070f151016541d411446d61110700ea140e0700845882800d0000c1c441060501c0900c1c0080c0440da00304d200c190b08890300e203581d2401c0340e0a54208039808c805101d04007002d10b8039140c16000d0307908070340994 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 183645593 1250 183644343 183644381
    0x14211207060b010914010e21010b090a09020108041b0f1d160516030c0204111905070c06050c0c0d08030702160302090c0a020a0b090105010302010e0904030e010e0102031318 76
    0x705c540b210921009580803410003041814115071078407928080000c900c005244005001344503020b031400307010220340300750140e1444800100c00f0f9206200d40c014980d8140c0d1210800c2d11507482d09803101ca500101104072120001340090b60002d10485032000302030741d05191152201c10580075498800080c0100300c0d1a80c201918044151702000301c4000c8003031072100c1008000d10b4201212105030601000390001e02c1c0000c82c0030001ea5034400f4004e11f15840042c0c0c1064034141000b03c600380900013005044034500c950601405018201504c1180d84400c100c070b10380f101078000280310068510040d80c4d01c101c0081030040342c56042c0003842c14041c56071a0b0030401c0d4603680c082810f139000100100d04001c40420700c420064800d010014402da0000e0101e9401c0c02c201c0002c1c0e00921082c4012808500920411416400d1075074139a441980c0588561422070700c850019a19152511001411400304104040815420710345440188c030014107001d030003400100e203c200700d52070922100303541c0d904 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 183646843 1250 183645593 183645599
    0x30601020a030f030f060e010317040602060a052e0303020c0301021c0902031f0b010201060e16030b0105160b090d14040306180c1502100614211207060b0109 69
    0x41403440c03103901d46880881d100d10f0305001c40c01401c102640584035402c2038400582c02c2503010368181664000c40c401901340c1541c20b200a042d11481c1b06010160700603400245404056501132036100307200c84600d68441441562145c4440140e900c031051340080c400051003410307810402d0542c0d100060f80210f282c14810009025180c4850091000c20740e04c4003800400c5407400e0080c50300483c2d02c44140f0400b100030400e024080d08039004528015031030800c4c0013508410240340c41d409958040025404508507240c1100a0081900d405052000820420600601c109514810903004d140740041a04141c00700314145404004080c082092441c1c6400700c0c00c00f01022101160b030b2007178002503070150700c51a2014418558a002d06044a880c400240d4101c00c00e01040b02a640c40d07007510002c000c002c3c20300c021650b8074002c481d50626038001201c201d00b0310501c03080703a614011020200030081c5001c460b203000661070700316003004401b2802401f000300b18010314018403800d00f060034241d41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 183648093 1250 183646843 183646847
    0x50c01150905250c2603040f060b0405102c0712050f040b0711010b04090b0a0f1116060b09100302010f1d0405130605040305040f0806040b04020d0311070e0a05010605030601 76
    0x41421005400012204170b070150390a0000d5507a00c40144260700d250322443d05041009155a16003400d0704c01d1740c1006850303012032801d4442c4e0ba100d0308142028485290804440d44030b0410b070b1b800394000c0851100000c54808101010003840350155588000c0811141300f907900a030f61001d000481c5c0c0003011000d2100245141090135403100351403501b865182d0307a0001042c0074088800406403c1407501a0344c0c0d0038803618440e9140710740400c110602c400b440754910355040707440240320703c0c20104040c05040110f455050b074051071070740922008505e100b850400241e417610f0946400c0480c600711760b420400c6503006900c002e0618803900705051521005410010340c0724000030907910a41d80d610001d04043d18120320881e150350070890400051909150250080d07101d1701500018050030400081d504d440003450920842d44410341d154951603603403c0c4244103641d08422010b02c22100038509091900b08250740c02040e03040c00803001c03410010003003402c0307030b6068000300b041000c00c00030800c05903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 183649343 1250 183648093 183648107
    0x40b0d09051507020304061e0c0b0a090b010e180a0b0403140708071505010f120807020a03050615040b100206060108040615080c0a0501021507050c0115090525 70
    0x6a0500450140d6007840d009007480c40c0480111650b004003001e110704a54000050030a4490603110b242c240a201403a12010388c21211018000a04081440002801c070600d410303040020844003045600c1d1a0790b50140b5200241c02c50420702092000300400e4464601c989000d00d0201c201130a51030f180c0785c48100b005c0100900280078000140701800901c0c01c0b40f03049550543d00540c1c0d03070380c896500d0300d011440e208070214101e03980c908120020421110715202c200407075034a016190340341d0b4a84ea480410342d8005200690f80411141c10000202e003081c410f480c45414000402200c0c1c02280c003c002c11512480b42241c061003010104011071303a00091920340050702402c0c40c035101d660f90720b82640070700341110484550884100000803144400203a07004050750464194605a4540004a984024076060801802088000308480a025800410b2400000800481e00c000c641000703180003140350380402c02e110399840811060070703c1c00b21726100035485510700769040300c0340b640010450 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 183650593 1250 183649343 183649357
    0x60c1b05090c0c0a08070f11060910141306050c070608040b0402010813120309020108011e06080a06050913060b040b0622050307060e1305070804060b04150f050312040b 74
    0x82c40001800010036507040082101c015405500141d0300c1c10a86440381541c031403101c085600345001d418002c01460440162010040f000d0305201440c0780001c002c6805400c090030b0f0800c146001c1041140c28a03103025800043d20315a12066038400d4a403d1440c0703010016801001046940007c0c04009110b003841d082c0c2181e0246044803c50320303411480794816184020007003120b200d10340440820b0b03806802c5001c0c0303117000340c80d64400c0360785e00c07034401c0c1c0c620018404445000072000014031416000d041031541004031000002000e64864000c1511101d05031202100748a50012280812440d8000c405030244103503014401641c800d400328240d0300940c524158526403044001180300c0603400c910300104401011540065070707a08001d0100350450301d005000d4451054002102e6085000d0540101819036803991945d4a503201c01c03008040340f1100b103a006440b4128001103159418454001c2e100e0314100303541192808080500e04003201c1200c01f8060001d00c4100100740e210300950f646 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 183651843 1250 183650593 183650611
    0x403060506031009050f0d02060f060405180a050304050f0402120105100309050102070803071e02060c03060103230a06090b0d170403080d0b010f0e21010605030304060c1b0509 77
    0xc10385403440003900b84200d00c0b4505000c6481d050710301080c440001041c54040d010b61040c1d0360151400341e02280c80f85003c031002444403408001282c2c403801c05600180e80300003050419096101d0311038855062504501003903c00d81d0000c84d09002d513141450086540c0101145c04600e0500e10031251640602c052103418401c920303200095410130b010f50400c403080c45d4000000c42d40c0705d401b0301c2c109055410603188100007511144074100d04801004444c0708800d1a5001002160780d82c6560785100e078001400d41e41019262014400540030400c5500e42d80001c1f801d96100750302d8010186012a03945070f01c2042542e0409282c081e070340c0c444401116005030401030103001140d000c007d10006101d0390b40000c0070500d0000c2d0300851014950300110300384800344d075011004110040203c03080d00d20440040c0c1e1041807070000142c80907120760303a41c00c0d0219410000c2003039540d890010381550082d42c00f403030115940c0b4240104006104101340c410008030000d224040341003601203102c1a000400c9015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 183653093 1250 183651843 183651851
    0x604180e03301e2d010915080304150e0628081009050406110a0206041103120d0527030d05090f060402060f04030510021c1109010513051305161103040306 68
    0x3144d1400c00c20300b808000e2102100c0440d5012100d1080c004c0302d09100c1c003401b6906c0c00001c2860710402c0c01401d0b00b184c1c140f40c003d509180c1020154010b04140c031042400b400400200d02d070740e58030380a0141182c0380000403a902400c125000c0741c4031131600c0c0c0d000c041c00c0014030710030481200d85c040f0410040e070760701ea280000e040c1d680e4681900280031200481350100d00c082180b030300745a800501e0502c02e500c210a1480894080c90070306a85072903030710142c01202c80074005142c01c2030080c0d22681d0310409500321700e40d440c0001c0180403e0800d030780120f49840d420018030021034401501682d070300540901d004010310004109034503280c100140c0004e1143c01e00041440d1440c840340d044d140559048400d031010682180c06210080d4070210303851046d54040409801e51118512941c0915003141084600e4005540300441d950742c4440013900700c60554400200340b035110044014040b0600d41000074183c1000240c07065060b11000c490810412502c3d104408040003000b0b440c01c482d4041c001203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 183654343 1250 183653093 183653101
    0x3020c100207060c0804080105010807060f03020c1b0d020a0e010515160206070203070902030c04150509090118020705060412032703050d020f03040f0309140604180e03301e 76
    0x48170900c26980443c1166007840004a400000854144122803032500c594482c1802c0e050309800b64003a5440390074561b00b000044640003142600f4031411080d009180000e091940d40c00140d080903160000c22614106400610040c00c00340c070b4000203156941002410010380041c1c1d100d4550720304900a0182c040842c464013151000c01c002c0000d0541c201007503449140804405503160018410b4400000081c015201454000e0341250980c54010740101002c2c1c7c20b003190399414010104150fa40035608100c001c02040052201c180500d00c01c0c141d403000446040d500800791205140e860621038001e203403e0f0201d00c0c0740300d095071403194141070240c0c07118002c4070008000c2c040d600100152100008c108010000342d00752a40e40c1e64030944030030f00d02e184c0342d001c1221a40005000303190040300401080c40007055182c02c1402c4034a1040c8003182c5812090120350a580141d011100d114581c0744203440c40f459550b24940c0200741c400c600d1021031130240602074481c1703007104880e0f00716101d0074041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 183655593 1250 183654343 183654353
    0x60d0b040914160f180b03120706140a0506100e01030603060612021801051507080f0406090f090b0f090a0b09180c0907051905120a050403020c100207060c 68
    0x207512803a000b510112078480b80081c800d03110101030000803444540c3c0c000c0400c124010344801e40540e2074042d04054040c0340b84000da401008841c1003a075261040d080c4c4510324041c1600104502032280b00080f03040f40403011b011440e2000a03215413160b60800042148540790002c04042d10310051900043c1e1080400041e4001c01c407a0304054130450038120041040941c504c005513216100742c41100910180728245800c1030b40c20302071594000c110742d14014880d21104090010745004601451a103596088040e109a02a0f440200800e5681034200411205024114000c005002050001a141c1ca00080c201c419010006200e01c40c2440815040c1000d6400100c2c000000340c0113102c0b45c10000e0306c80441c03004640240625100e00740094001c3e003081c2084600492450311214140110500305c1503c41010320b0b410020888144000252854903101c82c074090203007904002603900345802c0c02428210b0342c00300079025020006d00315101580c0010b100c01100c810340740c001d951903a9481c10b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 183656843 1250 183655593 183655601
    0x60c2f0d08251713021c02010512010f080708060417030a02130602010203060f03190201050a02160b09040f15030809040e01021207080601080c0d0b060c010c09030302011a060d0b04 79
    0x104409082d02d044800703019822240608900e00c00d007020340f0740799035441521301e43c0603100e103402500808042051403ca1850b04600d00c04c981c4141405800c6c003612517400d0340303141c80c00da0224050411540c03080000042c00d21090000c1e101c1900900030514290b00c0b41d045502c00c550300303000c2034200040010b24a0b90f0ba0341c16580d01c001505081001e441e524640203020b0740040e5601c03403044503070911014071441c2c001a2854480c210f6408000482e00c6500151030f560071460840c4150300410302d896440414801d010303000350003194050303030700c0b50307009014031040700c204900300140035280c8510002c00c1c0d03d11180820481c1d520100d00c80e03032030500402080c0941290040c42850398008620010550303100e2030003e104074480c0d980c1caa0140d4a4000448242100fa25103030202c00703082041950303900e041d8019002c100405042c60f850200d500043d6030840f0340307110003c800218948801e208040c1e0a014211a15580c901e0403c1c82d4800080051510700c144291070320f60035541e03141450b581d00d650b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 183658093 1250 183656843 183656881
    0x9110111062d09010501061d01090b03070513121203060605090d02030f2d0303040f03030b0d02090906040c052209050c090c0406020c0103020f040509060d060c2f0d08 73
    0x10b1059608040d030f07519002e8a000c0c02007002103591140036070701900c9101207038909948140d42d0245d20515001401450b684050603a208103c1c04000c0d0024100140354407400910588001c0302c809040d074240350030250b045083d140201420804200003096100003651030140c2d003250364064001c80c52000034a08601803074a41e0b154000c8800a901605100803140c4c00180c00315180710300510500070164492004440040c01003080341ca542c00840d101c1e5010000b1144060042c50002c00300303800040015108481d02d04043d4800300400c01000042c490318002403030191420961131852003500000490312124024841d950317000000c0038030000300012240b001001e030035802c0314249680c80300d0440c0d125001e1017001d44103030400c2e40840c0d44a44200c4500700c84605042e81800e083c076041015a107000340080b94407907800820440414004c0c42645d82e07440c200c1d02e441e039036007280500d60340000210f00c16802d0441d2998266100c41040440d4510360300000d898800ca042d641c543ea050140c0c10001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 183659343 1250 183658093 183658171
    0x1031101051201031b0801110903150709060c1506030b0403030f0b0102031c020d0603081b07030b0a2d0b0a0f0807090b03070b0d0b04050f10051e040905010911011106 73
    0x1203c41708d1b00b50800300503c240901501528203540b000c0501035002c8000f07880b00d1002417007600c010015240f107030568a56880c401c401341440c0d45c2403407442c1800d8a069030003d031a01c8581700c003880101034040c801c0784d0035030030983d00a004002020001039128040c401440440081c10101408540356a504884054006120030080c454481c1440140c940014009441e4100143c0d02d00c4811500024a0b0741100d40c414814185541e819001001410900b190f82c50722042d41800480c41c942c10310384000034504032400011768061030008100860b105079015080d135240c80b00c1c090000320743c0810280265441c1c274201007201c85460000c03074a0b1603070710391103041c4035080400d0701c046c29001d58001d110446001c40e414021529001a4129681c4c4140c8280c01c0d41100000c2c10032440c1403011124480140d08600e200e02602c4810108054071002e040c11a41a591618008100007114103158032070003003842c24010100c1d052503081d0350384502801b10118040ca140303200e000c0180c810070310181c0740200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 183660593 1250 183659343 183659351
    0x11010305060a081e06180307150216060e071508040206130f180506010e030a060c03020f0c1014100e091002040e0a05090d051c090501020703020601031101051201031b0801 75
    0x300260540b20105602610042d0040d800410b80b114100d080ca4212201b890021313500c5c0c81c82503035900d0340d00c0e1100c0c030307412444179000d02400300c0140150810540c2140684000b00e015030304c0e1581c9504240041c0c00020992541c4034000c85800c0d80058266846603050b5080c650303030700107201c91050454460b40540c2c12400e4600020a94000da03040e41124a0b081100902498440780f0040d582120412100d03900755000680406c08078841e81c0001000c014581401890030b81e2041c000c0d0343c15444910b400907964044110340b00d004c8180d01c03c40d04094400c00a207142400c0c07080c90042c012131280b250803001c4070840d021842104092003640400c84d01d003d000c41d5140d0341da045851714500120b440051083c540000030f030010310085003a01018170159220f51a040415284000c100e0002101d540712903a07802010340001c0e4240300400f90203009400502156140d0b01d00304120440d4030b1b0200341008014084101121303e68181d1a0640e0390000d6160b14500304000289110440c0358401c00180d820 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 183661843 1250 183660593 183660613
    0x3080907090518070602071d0a0608060720030306010509091506070c05090601093008160b130203060a09030c05060a05100b0f0a08042103020901120911010305060a08 73
    0x8102140c3d0080c0c8282c0b815207840d076507940e20980c3c0300d000034410100714a0047c450061440e01c0c4d2480345501448260f400164903881d50042d40c0341400c1103600c500410102d11007003003010084058241d0f541c545000651840c9001c6000038000d004280456014000c5140401d02d032540b920a203508040300540601d850381b42d241440a00c20a0ba84070b001d00580c0c030f0740c011440552240d4404025504280b0808041c920a09404281c0c80d0500c0d03480020346011314910030000d03010302c00810001c0d03088a103410401d030003410f000207003400c0907240407401c0c2203a0002d1340068a01140c1c02c0d500c0500f40d4030000b02c0952504090711241e5104034000c10074000c18040001c83c0c0c8190344003030f0085e0400200b422145441e00d07144900c1744220341901030b0154041c0031540e185c40c4100c0555502c184a03102c27100540388840040403119400c0358040c80800d80200388417445580c4a90b4825050790300440c14080c8170034a88900d6032680c005d43c08141016100d40c0040d104d6258606124002c2040398101d9908101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 183663093 1250 183661843 183661861
    0xa020f0616231614190c0503030a0c11030f07090e060c040f060507060b060d06030606060203071a070203040b130e160c120e030a0305030402040f0e0d12060b0c01020901030608010501080307030809070905 89
    0x2901140c1101d61900c001b1020819040010a5414480e90f0f510303400d00701440380e1110314a143c110841c007036151040000301c0800030000e204441c014002c262010886003859a601414174400a210b01600d079010701c01001240a918025000c407061418402d03500c0503142403441c094403018001039000040025419001d0b0b82c40e501150403a80200d408116041d21900102c0c1c89118040c00038207140ca44c0d4032840d4800140d100442c4c0c000c81540101c030f180c940c5d83c1c0e02d001050340069172313480e6243e0b5941c1c00401c02d0f0201c003280198800c1000d5111918850315000180804200ba82e02808042401d40c0a01010340600014064000e0040c122001c40c0b03c2440c1c0109030f903100301c0d0308134021401e000186007032440c1805000080a1401c0142c2150310310090304440d030511202c0c01101341c0d0348880740012900c800304014140081d20788009a40ca00c1110005001c1d21035070340c0501d03882da1401c001003110600100030f0fa5041e0754586000152501d642001904e030110315044524443c4c540018415200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 183664343 1250 183663093 183663133
    0x2160503070b0709300b09030c0c030705010c060b030109050f0703050c0609030303130602070b01030303051e0403090603020901050c0709052d0403050a020f0616231614 74
    0x74480e01107140d0654030030008403801c0642d0301c00c031700d0b030b507401c151110100403401c11501440d003100462044240b001030703c5902507000103603111030550b0030002e95282c0310181405000c1c405034082c0d004016142c50403000030114211140d000c0e05d110f9031001c415060383c1d020b410410b02c1c19005401c03607205070011b0030307081d1701c480080c40b003181c3c240b241320020350807401d00b101a06c1681100602842c1140d5444501c5840078640c803070121440e640c08c03c0b8003400155480c540c80c1c042e50180c0e43c001035500e003100c1e005003410494140f8030481e50b0500204400a40e100c030003641907401d14500580c0754604100181d0b503034010703c011003916009044c000310340f48a80781c0c8000d1150b80d000e81800910543c0864522405400280c040716964544000070003103400307070000340f03807403200d91045910344001020f5003800c100066402c038030810740220000402c03e0f44500d01000d007a14941d00700c08054071460700145103229412611240f01c0f007141401c030a0245011186205850020030740c2d181040d1407902072811 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 183665593 1250 183664343 183664357
    0xc020a0312020f070311010e1507060c0807020a2a05030109050102190507150c12020309071a090319261903060806070309020f030706030f050601021c1202160503 71
    0x14480d0768015407440c0000204c000c00c032608104040030120010340111080c140b64034146401c0304043d40891010759241004102c2c00e809060000341c503044210307000745072007005001301046500c9182c1181c00b00f041c5880c2d0132222915408181c071a890f0b5131070a07112256590380b0491b455403920380c280301480300640040072140e07002012103145020b030401c140c2d818020040042e000d1502d221903000045126840030104208030706012004681258030305c0c0690340221103803401c98220180400482d40311644084c0340030541c800301c5041203501404a5500c401c0312112010884803e040321090240d0030083c04041c0da0703101807801c82014406100c0b21294000300c0b2003485c034086451030300d070080e229208203000d40d00385201030040c60300c0b140000c80281840140c141d07401403051912030040d9900f04004c2000302600d07280880c800040412402c11514020100ca0554022042c182c4410036480c84250140e00203090072000582081e400b50002c0c0264081d0a0399004c1c405041028008000050550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 183666843 1250 183665593 183665597
    0xb01050f0604061731050705041e0902060904140414010203040b0624040f230307030210120c0c0506090f0304150e030601141005040320010c020a0312 66
    0x2040c018001030240c0303846140318078000a40034210360016050a48292508245a400d640360304078030b1100003503424084600c907130500400503580101005000d1180320014a4121400c1010006032462400309000b030b50b040c0e00e06590390355480021584c4240c251001094041d0080140c196060f40b0301c52a01000e41b0280e420681c500c44c2c900c0c540c00c050007100c0c45694081031840c136580702d9009214400f108a015041c1407000765592208080065007e0f0004000b0042d001c100e103440c2943c1c2400a00070420302103d0b4050070407580b109a10000740140480303905407003982114045040c12500d072018108410381d6142041c140d900f8003544400031001381402881601d58644170700d60b0141c0d6030310b081018070815400900c4104030072030408491980030160750514070060b14040300040d0900d2030917045600640d00c404280310503030600c10385942c3c0c04070542c02c0040c90301c1c1c15038549141452032218640070454046e016080c80d64840c15000d0507059001c0d0055060301d440c0d141894048100c1419440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 183668093 1250 183666843 183666859
    0xb040e040b010902090a0501030b011707031d03040f05061b010603030201020a0e090610110102040b0c07060e01020607050d0504060b060a08190626010e06040302160506091806030c04090b0105 84
    0x18443c065882294104100103200c00002860000158040c040c2d03100304905025032504e04035640c00c07039005183d00c100749582d80011198a1002c0713400502c40306040b0800c00741e00920060080130030400405083d2a4205c0e00303185c45111001320b03524020a841003544c1e1365400d0a80000030541c054001d0080802e460303c881d0b10b40d80b64201070052504046407003603880083c0002c0700120714000d060040410303907040c0c005841d158480c0ca00d024070307521030150035905501044042100c0b55100503d034003000024170140c007190800b0100180b882c002c41940074a119900c0c80410200015903216006840d4080c00850b12018080400361051b001103441c208095410300c001075054044e4400d00047d5485a0300c060500208019416200c03200c2e44111403e640da24510714203c0d400c10004140700d6031080e030003095046951101d42c0c4028649a00540c0204018030181c80c0179a10141c652800c0105403650403030554078000001c0c9000103000318150010301c1c00c8258014041a807032100e068440541d2540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 183669343 1250 183668093 183668099
    0x322081c0203040206070609080c0f0c0307060503040804140103090f05100b030d2712050303160e09010506071104021308010605120607270b031611070b090103060b040e040b01 77
    0x60306a1200311002940080c00b0002c90000480592141c0120381c0100744203400c2c20500030035980b40c9008a09100116804411469102d2404101e080040c10740c42c6003150540c1050340d40d6098500071401040708035808103d034216264030a03403111540641000c01c01100032003a003000c5031a030310700e890801c1c00d03d405c000201e00d0340d003400950303038107002c09684d030300900c20703100000c1c0f41010004018009010203200c200040c59000035181e01c00a54018000f80d6036a09101020b07010520882d0145c0081c08101a034020196445048540c1100c0c01030f6030031075132620189000f840080c1c0c200c143c0b6a0080c0702291840b116051507000d403068402c00300c02002031a8540042000c21200301051101030f0f0b000d100060100c920480c0020110340002c5041e26021455205001c0d48039001d8029019080000c020056003040684061081a005003807245900c1d207100b641e40c4d25420746015042401500060190069209038401b6004011080d6a6600d40e0303198010440769007003d85064803001000c40000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 183670593 1250 183669343 183669397
    0x130501110a0201140f0f030103050c130606080106050c030d060e01080c06070804050f180405030d1a0f040509030412060b01020606060a17070504030f0f020909160902032208 76
    0x18074007194058541e19aa40d1040f019035905a001556104401c0424044081308040724006140a50300c10006000d81004580c01c0c400203d451040c46034542303003005010044150402041415a41107250840da5070000c13100c50f03450741c07040b889480c451900d00000050310310441d010390350598101105440703024204504001e4503000f003c030007502042040000700031a242038104200f6000c070140032064a4000079074090134034407048406440300d40001034400c5601d030061164070800760550407150a140d00e440b000c00c500401c05002d650003030f80d45501040b9011000c006940052413242503206003040b00340307401d00c050182c2e2441c03540988910700228034145401002d84403485c00c641c1d1600d40c5001c000c55251031208001d0092010710100300404008121300710108000e450181c8210300b00c1001c14410301c1070b01c03500104200d9061b0804100f50b8002e5012442c103008540403140003580300e0f110f40300c0c1c2800b40780d0780c4000350a00c118015000803c0107181e2002e04010810840400300140030b400c0c3c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 183671843 1250 183670593 183670603
    0x70f03050a2c190b030a0207060902030706030501061803081c0b040c0207030203070b090d0305160213090b070e010203161a0103030f0e010813020913020a0b0c010b060702010c12020c0613050111 85
    0x1000702c0c20b1340510000f101c1001560180c900c060065030049403003505500440e05000b903d130014400642c0b500014091345400c1015811007211035492007448501e9030326a01d40038026040d00340c10b01003804040340c01c56550750304100f000103001003007001b03101c0202c01e01a42d1145188400c034041d0107450b200141d500041e209a0f42903002c0a0f1012400c0196940c084616a1003441a030007890310786a030810168961881c080c0c5440003171400090100101c0c10a92107089006000d0401c01c4800710750175015036400320540711640114501900d030280d5620b40b208000303452000c50b8031070000b51000001859400181c0340f07060100c50b103ca80c070f9061610011940000116600341006417030320022001820107028066025485101301031103110540d0006011602c6588084003a810101d14500740e40b80a100b0707810b81140c00c03285140340c03000c2907001078010005100c01038055195030380710074030090003441044c400074401454075545072200500c00440c2e11036401260700284154803104d24207400020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 183673093 1250 183671843 183671849
    0x50403030e09090a0b0a020d0c051c05010b090d080714011b020c0a051e090c09030705040504150c0507080c031305090702280503070f17070f03050a2c19 67
    0x2034941892240c4480c01c5c4040e0140055001c1903081105040c2841c2074482d60500300281e07030726184c0e0f4096519541e05241000d00c4809007841c44c1c00010000180d140044400158041d591242030500c203003446074050080c0140a0050f4401d00c2860038140c0042d070020017a80680d000c007052419080138200c1e0340d4160200010381210600c1c030140513030315010002944030300a01c10f000f40080c10300400b16540c81c1c0240d132500441c400c0821101942d00d41440340741d011340001c0d101003040d45815150000410002e50700000841da6508002507400d00c1202220324560b00100410341d0750444400855481e4000b03004030303001034ad0196000c990351a02c04441c81c010702c025801040c00c00c48110b00c440c480e08082030411598219120386000060040c4007400003a8000c0700d643d4040c0d004dc0c203001c60708400380d440301d4a105108004420001741d09480d10600b20f0740500c2d00f01d4580c0f000082c203984400c0c1140c40c1c504c4101c0702900c0295044100c1d1541c00c55000240c9030140e40fa813080c40e4595132044280 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 183674343 1250 183673093 183673111
    0x1090b0703020a06090606080a0f03080114010c080f160f05100603150f0e120c0d050c03040902090d0c031101020d050f071e060603080c0d020c01090504021605030406050403030e09 79
    0x241000c1c0101342a80c0183c50454040d10000402c0f90b41c5250399803421030f401c0021104144158482001c3c1038205507014010151344141c45040200d100000b08112030000c80107000b00008103214480c007000a059510f20b0503170351f41900c22540360f81001e1300003c248400442c1e02c0e2191840122030f0f0942c50140700100d81c2c0c8841154900104041002c01400700414a0100c0c00e81d14a64013455260412a80d0200e0782145078890741d80000c083c0e050b0602084001c0344090250030007002214043c008201c1d02240c0403040700580750041e6000045400031668800340c1007804d140c0000c0140005440b0340cbd05140426005c03036a011502e4035003610240201a20b1036100c607420310102001ca1040818400f00070b030bc0c030900b2260b242c4141d54110803101c480c1c005440034440416240f81d120820808058450b00500051210300c1620b40000d020080c94000c2c280180e8022038480e00040044001307440c231300d03805002da83c1c9407030702e8017001440b6803c01d12041d000202c02c3c0744018038a040031074a007805a01c0315 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 183675593 1250 183674343 183674353
    0x6060207031407061718030d020a0e0307060507020d14030a050406020c0f090105120307050303070c021e031b0303090409151a0a06050c0f07030615090507021b0a09021801090b070302 80
    0x306601e0003445c50018a0303502c0b01910000d5402d400e0b4018001081100200a0010380b02c1000600c01000c3d903d4900101d8000e90044400380b00c0280c0040030364641690464824540702c3c020b203007182901d80c891429408a11020500410703032030700240074000303a45540d8200c41d60280e02408100000c01e004240c0d60b01700032204010702c0681403110300085250b400030100c82ca0010700740d43d0b1380d103141d20844030749000540021008045150044241c81010001071202e8000300102000a49500d00c0c802008074900d070000c042543c6031401e0027996500d480040c810400041c4a083c181e48500130811803808152410350710f983c0002c210011101048400b502a00d001ca00701881a204c603800440b808400e88100500c45928407002c002100282d846003502107080303085820f002d640c2030310b1a000410124100010400040e074000b407090b166115a015181b000034140b40030a2180c503850704001640b80c00000d90314000c20381c415141000030b00a076552100b8130390354240650750b4000d0000050041e044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 183676843 1250 183675593 183675617
    0x201021c020c01111206030601051806010e0f030609060405012d0e0a080f0408011d06040b1f060203120c070c03060506040204050d030804030f0203030105150f04090606020703140706 80
    0x81d50281a82e15202c200001e90090704612000c60360304000c4070145180c40c3c41040190700c2c2810b02003e801400191400550100414040140403100030900c90410000180b01d548a83e9000c41d00f03e40c0d510040c003544e0240c10a407004070f40355401210300307980941c20004000c00c49135451405030405400742900c804164182c8400c440a44a24003c2c0c1d0703aa80b00f40301d81080230403180c10040180c000280740b0310b50758038980025142542c040c039183c255020b140c40300d900300482c000b0688a5000745c0c003550003d12a95110080e4810800680007001080010100440c4007a00000200a030441c82001040c10b0ba480140040051040b207100820b40001d10000300001446e54201e250031480007440507052580740d0380803610b21440101c069000a0740300040c0410300d500b1690b03100143c03034140f018515544c1800041000c9c01100322720310582c3c03200014a412a011138a069802909107201c0603c03d860742ea02000b940c0390342d140400c0d0b8100d0f0642e01c05050812001580034102c843ca41c0700d005076406 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 183678093 1250 183676843 183676897
    0x240403030e1c080c04080118030311090609090709090e0c01080603070501170a0209030109111c110d0303020903011409160608070e060c07080d12020310090b0303070f080702040507020102 82
    0x250031310928034014000400c25000a02403d0b0480711646d40308081c10906040090a5039510070101094281c2080311204949840040301d04201003600d400c0080c3e202c002c0b00300c80450b1954008060145000003002035643e000c07800c1c00c20075000f40e80d642d54603103031041010380ba01d03800e10855012407005000750110010114070740e82d2003250745000504126144000ca425602c22100484a01c1d00c940080603840c58001e600304110300450450051500d07040e0381d031106150400b2000d902c0b8905007001c80c005c240c030a404407003940a0180003882581c95104603c9023003c42985c1048040c0242c00303001e0400500c80503420221003103a41d82c0c0c0810b03151280c0c145c0703d480c05601e80c541c001070100325140c0041810400d400040421308010b040310480e07000c3c000c0065191680d601107141c0101b09100400d4600246031065820408000038400c104000081c0b841c41140d800402c0541258095030a000181d005004010b000b62014002030b030310468100c1c201d1280c550b03414011074401043e01c203004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 183679343 1250 183678093 183678107
    0x10f05040e0d08101512050106050c100b040627060501050711040902121c030c1b3f03050c070b04030f050417030c10022a240403030e1c 60
    0x15118601003c607440d41e0b586068508503111490115407200d86d503188a407050b11402d801031130140703441400c1414241ca400d0b00e88515003900c1400d030742c49104104030f40e62507601038002042049260041510307181d507201070010340104104241403800b0070004040d4055400c40c1e4195a200c2411241c0000d54001c1000a11174000203981261910703800c02607003a020005406198a080300701040000b118400a050301c007030b582078204001d04081e110304508415403014011aa002441c41c5040e401075640b4039841112418100e001d621448a4407403404600c0d2000d0040d4125940038030041d5150909400a40f12303c0348001d15800a580000700468803440d40c0102c210280d2400f40c2c685a030b40c4200e0086a2001100300b0180c0d00300045d84810240f00304115448000006000d60400015500c41004890500314683c00c074201641400030b501000c1c0410240d80d102986012801d5803440020001c0b64001c07030301100801c0c40c1810300d40004c02c000540c404400000103071607038140e00c0a00d04903016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 183680593 1250 183679343 183679351
    0x3060605100302121f05040203070302070209010f0605121b04060801030b010509160e0f030102030a0e0606040c0905060f04031b0e0a05010806010605090d06060803070b070809070317090406030803010f05040e0d08 93
    0xb56050345c00200381d5a039140010b5024582590780503842e02040d004100c0241c034107902c08981c2c41d018000c1008803540100585e42030b2404800c4c02c8a141e928101d1076111a000d0141c01610203c1c009404030f112508005e4150589014000b0180c0f41c0c0c0e207d00c04d000006078180d510802d40056000c20600080c42600b00e012805409091844120403c001090036030300195040a622078940280602c15242040b03002e51008040b24248507840700042c01412141d401d00441d03004800026502901d01e01107000c40b0000c65010481d45403120101e900c103181101c0702d0103035410040903c400b18018885074083c4a058548a41c007520380381e441c0060650303155101c0c034000c50300300c031403107a02c103021900c244292001800c444019650720703240d6240004540f1401450042404103034814003a151500040100649600c01860700c4450f03e503070a10a00340c040e1110507a80f1a043c03520101c10800c000b030155040720044144200c40d0b5448408000507106400162042c0e0f900088600306510301c540803941d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 183681843 1250 183680593 183680641
    0x3070c0609080909090705120a021e010203040e0a0506120a11040209010e030f0309010f0f0c02060d0f0c02070906150c0b0604021b0303040b060d0b0a090c0f0306060510030212 77
    0x24010f50600411605901240d1142c120f810151013003040c2e09201148220b2010424042c110445a0b07500140d12100a00200652000d070110b0751440781e4000c01c00c880140c0806c0c010030b8241e18281c403000d406041c1c12a40207006e01e003112070190040d140094070a80d4207501a400c00c160b501500c1c1440000d4114100c61410040c0515810710181c400340320b0000306008030070145a840b01a14000b41000321003529080070403000e81d44154949a201c8940030701d0aa040724000e54584032035130103c0180c4000403540705060314060300244a990000f910b50111104001d0a2000c01d59481074407000201c4405100d000c900346010900004181440703499201800920040c2407000030388500b0040700c4241c48500ea658000403d02c002d000910489039803284003100c030a40a0b01c00e42da1079940c40c100141111100c03607215890b8800b00190070358908050328048800d00006a81d90618401400c003511032540942e92035003000300303124440d008960f00080d42441d2078400b600c0d40e100644a500c0c22480c5102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 183683093 1250 183681843 183681847
    0x3080d0c1206080601031115030109020c0a121e23090310061e08070b0d0903020705030d050d06080105011214030903011e0b04090203190201030605030f010e06070503070c060908 78
    0x2001c42140b00c0e81c009011101c000307004543c158505035002e076440040d1203200e0007024240d61800e00d20f16080b00c0c152042c40c0e001580324a21041030358034203210010028150301c42000c22203280e980c0004014004202803d5005500ba070b41c080c1035890006d45c0614841300c54901300d800340b644071000300400b03c014001d02100c10013a0840c010408945c20754020140c40300094450034100711609110700f0181c4061405003c04c2e03450440b2036a01031060302009040141c44800410515009019001c001c120140944020145c1d080000f0b0440d0f01503a02021101d2820346c0200349890144900d5050700c0c0d0744040249045090340b504201d8070302d86c020100343d83c4000c2084194030b8800303010b110540701343d903541c08814800c08601d882c243c408000703020f40034030300c2e007601c0300d0242e540092441c3c40030b5090110488400c00500048014243c0c6400a58041c030480a03964800d030015401980c000e6010b0082c1c40b00390711010b004540c0c9120543da040b0020b82c06029180108229a201150561007850554 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 183684343 1250 183683093 183683117
    0x302030702130501080609070b1c0212040803090d02010e0c19081614030609060f150603011716060806100909090c050102010f0b1c020102070825050a03080d0c 70
    0x10784600e450060b1036901980b210010084108204880c980098216003c6c005041c101810f090150280305000035440d2054800d40e41959180c0e41240d88001f003030f1000141d140340c14100481c6560060754030700c1e018881c04811500c090b01c1840340c10402c3c203a05024185800c801810000d005920040ca5481100b075071f000024240740410540d62201501c20030795018926184040c0c09821a841e5498044d410180030000d4814010851030f07403102c400c8104000a49a07a0705100200103110b07202c41e000700001002040c1600c40c1003594140610603412181c0140d40d5842da01c58602480c4141008559040d002c62298605041030120341c0c242c92a000e6070b141d0342e03023100070300381c499040080d1002d02000405010170350742802860f81c03600c0161418014080036901040b60000b9060441070700403610091034045a10a024200050990b5000c480248044803001784a6201c030442804510001c00b40008840c1440041d03a01242d42082d00f42c2d04018407517105002a102c0d80c644c542c10045499012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 183685593 1250 183684343 183684349
    0xc1207060b030f0a020901050103061d22050c0a0b0f070f060906050103230c300703080301091406010c080d0b060a09090f05011203050c0102072001030c08070503130302030702 77
    0x80c030f0007001070342c00800d004420360050003144041038005074109410f1103030600102003217181c031040ca049405c02e107451956803509600c2801e8800300031602e410300c560b0000c10074404c000500304200d00040300c2d400b2410b80d480b80075404500c112004540040d40502c00e0001044080c00c41e4208280180340100340d10721140e5070403040320800d800480f0090060340011801c01d20280d0021610141c02c4c004000e4113070303028001420320b42c01d900066140d1004403d00a403594001e100f800000004400311209103440c0e240120964100f4081c04d00441c0c9003107420119200d000382e28030301600d0181c44556007290f0075112040282d2040d1000e00c1b80e55160005e903001e640381e6a004040e1003155943d0b4844540c1014480d40681e00d011100d00c0c07103607080c8001132102c1c1c0d1000b4552000190b05003010790303071003000039400c501900400c0e4010382008110058100c690307101400907009a002680c3c20461044808015141758030700752800000036000381300003400341c1c00000101801c503010340122801c0108136400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 183686843 1250 183685593 183685603
    0x7230405032e091a183a05070203100b3f061909080d0e0f0a061b030507080a020924130806010b030f07050c011802030d03020c1207060b03 61
    0x3101c80d511500e110300e1300d1910414481d60801c2940c11010344039506030701105d41d25070050309548001e21083c8010354401e02c03c08001d140300c4420007400100c02124120140060304040001e80c002d002d800c07000d1120383c040c0e1144100507000100004181d402900e0352565484060f0301094440840d5491f010030190441c00740122285004001e100a24000907070000110b003440301020b8075400d02da030383c40000d0319007026540303000b4200c4000511a0b6840c1403061604054500b5514070307006442c0d14806200f1580c010000a1039004050410100664012000c45904880010004083d8404034280300d40e10b0300203102441004101400140041083c01c4801c0d0605c41c645a0b03a080c0080c02076600340d440f464450040851001500d12585060f507000d4003840018010740000e1440c00c00200c4090051094170800710b03106008010304001000020740800003444168400c0c800d0580322103030140b181c004c4803404091300c000792050002c44080150260480c40b81202c40d942c551501c1d10041d10708002c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 183688093 1250 183686843 183686861
    0x60503040303090f0f060b030d0210022203030807031103091009061506110708030c03030a150b030a2307090b0d09060e210702010516021807230405032e 67
    0x40106240a440e06d03154085511aa0980703001c0c1e00900750700341566070003144590301c09640308000759907401c00341d2054115026403c43e400320120000404801e141d0310006140c426655a1000c100f03483d04101c2c031103042d0004860104130342d03010004080041d14607412602d084c5228150100d0310224080502ca80714909030007190000b072005500b206c0394401005020010400400a07501c4d201d211078941d5203a100003403a41000c1900d0304200c0c0c0c0c100c115804050001c0011064041e00d03810043c44600191090a0070180d04010391125480d00241c04001c1c5c500400894a076401494940404c60b000c0743c01805420590325640c14800000c26090b010303003101001c024010700170400350318007908504000c40c104012262810312803030f0b0050b6003200450b07203005406460b2051903d00741c400200038040902c1260306102d450018002e240b0b42107101c1c28003030031000340c0360900300078a58a0303100305004612030154194004d4070840090251403160030003201000c02c141400c0c40740301c02c0c1d032001c8c0d5000203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 183689343 1250 183688093 183688103
    0x2070803160201090b03060603070c050f07180c020705010807030e12070f17161709030d03020408010608030c12030c220306180b0604050603280b011a04060503040303090f 75
    0x1405076000c541c3d02035035500140c0b451620300c03030a40c00c2040101d02c1d2804005c4c000e6041c01074140300f62003405000c1001131400700e81042100e48a03503d80c40c540140041660385054914145080500c3c0d16001290060903150180d441c03400e00e80e20230304110041d04588403a8802402900300e1310304082c80e403400030303c442d178040e44103d242807582e40762401410130031440f40241007005100026541c036040c04400c03c601c0c0c0152420f1010900d000b0f81d0b02032480341100366079140c03150079202100b4a82540203001190021402001080c0d03548000503181d100d1444840e5050f017190144240b02c1c6411405140c100011260050520f02c030866041c2c0c0620000c1252350403809103900030800c102c001e000d81000c0080740f0014036204106070b41e0b101490300d4040c100500c038039224000540340d0b0b242080740806070140d0250f032410003028041e5007561100e911006682118050b0000708000f0030800700d900504003e403a8152a01d46000320441d29500080c10481c209a2950400e03804640901c60111449001d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 183690593 1250 183689343 183689377
    0xe060f060102120f0304081318140108010903020604150e06090604150912030c1413081b0102030d0c0905041103100f050a0504020f0d0e0307151a1002070803 69
    0x20001914180810120121008041110740200121340d01501d40003039000300c0c41b9480d1400032094031144102600500d001010301c3c1e52202c500010b982101d41c0030765096040303a0750740c1d89a1302c103d03007601c007201c00150140c3d2226012a00140001100c0e5211540441001510ba00c44055542c10701c04c0546002855600c100180300a2201c0c0c42c3c61004e035950407481c2045888465650701041c082500190814107a41e940c00c441424040d030285511850155070250351044610846030f00710a00e03000b00340c1d04d8440c40c00c100c803090740800b4070702c0b100b100160001d605040041d1a000043c18040c0ca445082100084000605884a0207644500a0780e203c00b40e03141c2c544a0003034003007051180c0c00500d00e00305545080117141c40c0c10003c0303c2514000e540159440004e400399410510400c000d90010a140c51030000c005500480601052841030706041207018020441e00260380d00003030388a20a640111803080c039464458003070360029166005480e122959680207a045401c030061641440d508 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 183691843 1250 183690593 183690601
    0x4050604031b0210030509100f0608011407140a050702130516020726120c030415051315020f070806150405150d021201020a090504050a020a020d05030601030e060f 72
    0x1001c203800030080c19040380280a08030f80c000074107030900001060f06269542c004aa011b2105006070090b0140b0364809124000c8010845002400e891140490651916003c403440a2030b12540d64091071035541c1e06008041c1e0320400081a9101c0b55442040c040b04100d5400180c58411400110609400002541e4505800010071000c482d138212801c54001c4e560500240305505071100130411403421900580320b416640600e40282c1c0c903465000d206011030b080b10701410000041c07066841e09145688464410703c0f090f03506000b1088010412451001c040c0440f05450789503004030300e010301c125081c414200c000b0b10709001c9640c102d1001500b10408110400c11080c01c09604130005807804c10440c5883c0d106644848811134001d44100c49003505e0714155990340c1a03911400e1480d0b0000c555800000340050000c3c0503d10446004d2424000021f40c80d80fa14400d03210f529551ba0041c00120000c1c1c001241c0c10b0340000e040e40c1c103140d550450203048000070000c042c4907410324680b400e91828 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 183693093 1250 183691843 183691847
    0x2040b090f0a0e01120c0605160b070c050f03030a060506041a2b090b060324090a02060406120b010f08061909140105130504031b08040b120a0617070302150702030102030405060403 79
    0x610f4105005001040010180c0207400c84a052700c00b40d0402e40c1090940c9132040103c070b440942ea040641603100783c1407400d1a600700840118001c003100b100c07c20550359950f05114450003140705442d07414809007115039803000703500020094550f0841d444030300012021400b024000c0d000d83c9010f90f040d0b0b1030509104000f5003400440e049041100182607165641001d078050f101007446600d0070f55000302c007040c000a801c01886130b8140c0d0090a0b55191034460000030080300b25220841e4509042c9401600594010000c162034165160b441849540d50b140c00d12400c1c0c18000720550241c60090800224661a40f00b0341001c0806c40e404010203500d00701c20000b90640043c40000045e2400040c080060303005103001034038034456045110412100c2c24919040e000c0d80e40614080c0000148108114003102800c070b00c5090608020800c564440300c106e03801c00804003410340755038016071051001d480c1c240c0c449904100000c00c4030703180000c1130307000c6826a00140c4003250660301040038081015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 183694343 1250 183693093 183693113
    0x9081e07111909021305030607020f060c0a09030803070c020a060e01080a05062d0301060311011101140c0c0a02030d020309011704080304020d080909101802040b090f0a0e0112 77
    0x20812202980c2041100d00102d200160510070314002940c001130480c0c6072150641c16000500c001015202185841e400c041e46a42030280740402501a44000841c00700c100d20598402d14a541d031031045031411940c0d0400d150f4409018074003882540610b0900503554111614007a01d51541d5801071303070704240300250800b40c018008800700c50402042100f242c40d6445000d010050440000f42409141c03000d07a001c1c1046441e0a580650a0000100900446400d2101d601d442070f43e444000d420240c0306c043c204c03240e2050401c10002d2140200360001c0d01980540901070302c10082e18414086a80000d15100c131a04130721025030804114164a90303003090700e449286200c440c003001d65103055a5242c42d0b87c800100001c0c42040c0005103c002c0c441c00800362541500c0240c100b00d110b0421928003100f0716494403800350560300c00400312101140c640291402c94001d45d02560402d03000c2d40030008004d0484444640214660384001280d070090030615000b001d010b10418854003460400c01080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 183695593 1250 183694343 183694373
    0x90a020a1b050d2f060414010506010804110a170606040605060f0d0203070908010c020a0b0c1201030809220f1b0e040519020f0310050405061309081e07 67
    0xa50303014207804100003043e10440201036141081029101c00c180c4540346940450315209064461a811046040050201d000c0c5028101c495840341e0200d05450036100c0c12616039001814034000f040000380001c24510780700400a040d039580e151210600d0345180244002080107030f000303205010881c1801d125506c007038942514514a840c8005201c1003440c0300d005484044258004002042c4030307c40c480110103040e44100a0022031050310000b543c40540540076240710542d0008940c00031140c030210b59141145c0014042d0582c6961603030602504004c507443c4c0c21024605d4070840c030a0810307194106400e920a00022112520340345c4904817104400042a14240444266409034102c00c41d00f0100404a501080c650b880d12130304c04412882c5075075080140e0020600c00b40841c0a500514403500c05541c4058265948200300419a0000d5580a4100545c0c2119040110458001151842c0a040c040b860300c0020906208203814040e030180b03040342e01107400c40422540d05080010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 183696843 1250 183695593 183695627
    0x501050304021f030902150304050705040501050d0204050c1908010e0109061d09070506040f03021201020307050a0c082101090c030506130c0207081e060c030c070605040201030b090a020a 82
    0x9625056002c25440f8600300b810441950682e24054002482a00080c10465024001410705490b5081c840007a0308281c40448080c0540040860760b41402d11585048407002043c00700000740a03001e010003000701504d5039124410810000200c910b41c5045821000320b20707911090740703600d0f1180070101d418040c1c12190116091003820080000704508100d1548420302c800d1141d92990754100d4602501580700e6500080f021800054500b00351a01c8012a80260340c4034071511001e44409080b44804c40f10800401d07418818002d9107440b451305040054414415640340030005010f02d041e0100c2207034035100101c101c50042c00740e49224080c40c0c01d81000c034201440035080810001c0c10b08030310700c068460503d40c1e030600a141140308000f084000d00040307003500c40240362000200c4490781c1e0005034541c2ea00c60714012542c0301e003042040368803944441d1840ca0402c18280c3e102006808041c00990425884026080311540c0320300c0c501c0d009050041005a440c8152040900b1388000094008a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 183698093 1250 183696843 183696847
    0x4170706080f01030b0c16050c0418080f070305040305010614040c0e03070b0a020a21030e030301060e0d0212010c080402031b03030d0518030c03210601120e0f1002030103020901050105 81
    0x302c607800c50300060544c0d50001d040c441a65405190100d039014484003055182050080c030800e201011540201c0d000003980c051003101b04e5110140680f200070180244030004c00c010544580c01007402a00d421b603c01e103040351800d680c0303498a90a4603140d070041403c500300d07a425112189020b00c51403800300c3c07940c03d08800108001c000240c03211480c0c407410780714400c00947d46e52218400d00c00c43c149251300c00b600d120700e0f02d100c845101b05c80900d00c40303010100c0d02d848001a01c0c00c900000f82c0f81224550360b100c0e120800010180044015182c0c8100e0700b02941c024a43c584a20038002e68034100300c10f580304156032405004043c90103032031786a0394584000c50380500e1640e88012048962015042d2408120b0b0b803580ea002e1b880303004101c101400b85000108014100c44404001028544010180040000000d1100c00100b06050341c3c0c01d070101d4901e08107410741d10350301e4018010059001c0c05440c1c0c0042d144401c142020b16102031840c08035800001841140303416104980504000c0c07034054 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 183699343 1250 183698093 183698101
    0x10b1008060406140607110f10030b09180d030906022106040b09070903080c03041205100e0118030c020a050910090f020301051c05070b0703030e010515011e12020417070608 76
    0x2400c40c850080c01030440c0c42c00c01c1f5a103980e81c43d96200c59060410180c60030420030900384000b0010f04086d00b0040c41100254080b81000201c850244014032041001d031111744030800098004040e000d4040700c009030203000000002d1aa110390112103040401c1d01d030083d2603c2c2c400c1204031400406403610688181c4103000085030300824120940b98030441c1c1d2a5100100300401d0301d1409903a0018140032a206040d0b8100680410f56218040d00107000f4450400014031440c00d0320749074200240782c81804404407000c05d10036010b05400c0c078009003642d242c182d110001300d400c0030720456071003610a51210003080300c42c44034400c1c5a005a03410340111f065504000c0045c0b096a490750315004101e0100f0450f006101060000000030f103642d0f800e4581e61100c0b813030040c010b0070310340d40601907a51a02001407085841d05813550003290050b55a29880a81204540f0340100b03054450300400903030f090081d40e400c101d84001c201521150420f29500040480507138900046070304884d0412058030244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 183700593 1250 183699343 183699349
    0x40e070311060f130801020406170f040305160b0108060723041a0408150a0501050d020307060f11060a060801050601140319020909040308010602010b0d02090117010b100806040614 79
    0x8038000725021918299101d1514944507514002c00c4441c0740b811213540c1c00041c01c90790550040c81142c0054555500e00038104181c205901e2040b26040e107005012800a40000c3c454030092900f4001014100d50131480b607150104401c80907040510a64001740c00e02c008203030410036404403041051260b00b224402c510010485018034403600b944603a0110300100c800b070402051700c0c058110002268206100c0d10b507514140481581e00c034005034a07000021400f4100290903455554010700108006407900c1800c940c031b00f2520401100300000b600e9500007410003484807130302404401d980804c007541040c880304c0c21540041d05c0941440b40c040d440901518480040d00d900c13140c1e50202500c0c01100c44600f00107032180e030521030340c842c0124040204041c0c2220f0480d040c1d4003550b00800001681c00144044041c010f100a98400f0b55100100024290140141d00c2e052a071400401e10f01310400c0031034104018007080130702103a007810810a0504080c0315032801050100c0f8002000030043c408 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 183701843 1250 183700593 183700613
    0x6040906051305160b0409020307050f0d0903080a060e0f06010201060510020a021504050d030c03090306020d380f03070305070b0714280609020a0906030212010c090e0403090302031b040e0703 84
    0x14948a0540120000341080c1c09141235504d41e202540000f0b41d2800c11034dda40006100881040300410024000b050446100744280f0741650403804d018020741c0c0710801112202100141103904640d01ca507404a070b9a04c3c2c4101c4103203003100036002842c00714628810842880240d5468081c0320b0411b2008001c03541d11003034041445505410070622010351420110390740c0c615500b01070079403400022080100a6103500c40241841e1046d0981e0702056a0b16100c2808000300b040041c00c417103160703802d203078031320b015507000781050001011500c141d43c0d69a110760804129500c06035420308d02080d1102071101c2c3c0c1c806104006440001b0300f442c9060030200501040351120f8008000c003410b21001c0400c0005da00c802e4516030001d005c20039140d92004103002400350b600080b80903500607455140c000605000740541d403001d548134082e200341054691410000010026810803038000c8001015031424024186280301c501e54094040c2c044c40309010a03140014003104090380115003c001058140b40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 183703093 1250 183701843 183701849
    0x150b03060103031b050303010f05040b011107090209041808090102190302070b0c01021303060e241f1805060a0e07020d0e010908010e01090b1e0106030506040906051305160b04 77
    0x200614070f504140510021060801d40080c031720700c030000001c1500910303400d894007145d00490303062222610181c0110f034030115484103464150301c0800140f000315002d1b005800800e0010f40000303003151420b85500c0c02d6030703e03c0000361055400061094481d590511072200603050100501180b1070700c40c2d400039a0758566104000e01c0d1180441e240e90010401e4044a8000d10010b09140d20340d074407810102c0c01040d204040c1c07020391082d0310f12080e00741c40010009101c24038010000e803143d5248903089510004511f603101c0d06411070540492141c4007500e0b0141622407604c800105440e0001c02d22007600300d80e4008880510702d04080015130380d030004011040c00c1880c0741071000d00f03c5c2240113031600c1d40c0d160449940d5508012030740c0068013055000c030a03828000d028251483d01c820890840b003040d1540f03441a0903103450f0041c00414000d8000541007400a400055112a952640c00031124155485802c041030541021b01740502000038084800010302e150180c03600d40300c0c16150038440c2e44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 183704343 1250 183703093 183703097
    0x10303020c10050d240f08030315010203070813090b01080114041508070e04060c0c05030706090c030f0506070305060303030c0703031e0905030c0f070e0a020304020d0203030d09150b0306010303 85
    0x100d9a03986240716205507280304c0003252040c4492000e400c290516011045a03584154103541030026001040c0e10541084800d01c7d000386145071150700a84901d802c0c40c41029055100420924000900c40c00042841e030031000400e150060034068444140c0c2d5a80c40c1032030400035030b0070040c4a030070008540190b03004011a8001040b200b001ca1003a2441c1300c5600c00b00c42c90140348400280d82d009007111750304c101d110308410044d01681080503500314140407000341a561091005900196441e800ba928140c01061401207141c0d49030b540031722840032803030101d82a0300711a0500618a406000b09a00400d0880195085260078036800d600b901810360b0107410103031a65034401e00c00e030380144c0b40940705002010a0004400a0910540d80d03840498081d0142c8101c2c0681440c1c59000b04101c803d45104000005150b10b4a142c0000a5080507009980c011645c04841005036800c200802d00f070304100101040c00780460038504400c600100c2c0b4a0841800d080c076441c642c0d034000c41d040781500e03414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 183705593 1250 183704343 183704359
    0x60306040905010b04061401110a0308010b0a03060b07080c06090a082205040c0e1e0607060b01121a01090b0c0d05070311030d05060f0402120114060c33010303020c 72
    0x14100b0301d0251148030300c465081460a640070902c480b0841d4450701c41c5400380c035100c080c000e04a00490380c1c0e4042e4100680007600c2c01e4014010391982c04014061044a464040b41d40c3e0b4443c1007041c1c40c0d0b0b008150841c0d004000043c00a0050300521469a0100c0404064003401c0700c1511241c040b0700c0b51070411604c40d0005503861190b901542091349c06040054000c00014400107400f40815030a02d10b030b54442d60041c2c9030301c00e8860202240ca0850180a801142807481ca40d6465000d4600c40c40040c2c180290790200c144901018403e644080c0350380c024103420200450005030442c445500030740700340c14003002040c01c0143d00040401202c003061070120398072241806c0889485161610032610341c04001400e0001c810300c0d0f0410340c0900c6c0100d07410058001e00e20100070482c0b08000000080c040c1000c0100f1a40d0b4100f0358a070700100c0e01401c81450b00d5900c1e54440d091615010f040411003003110803906000041d0101444a076051601c01e4140c2d50440d28080d40d00d110501201c0d2044401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 183706843 1250 183705593 183705611
    0x51306020c1f1409031c0f090f0f03030b0402040807030f110904151415040b06090a061d041401030f020402070212030a03111602090c04171f020906030604 68
    0x800c98100d5000003041021120048200c1d80c902512009101503e1140c5060116640100100880300f0f0b82000b1b000c40544811944c4103800580b204486a0744826540c0c000c9001007960304400b88090f03803007000e95198011103407501901722104e0401c928002c510502042c0107482c40020324009030303a00304a541e180b1910a03c0d0501100412520440e0000d034140c0a10040000100c410000b0010161040c401e10f040c0c1640341503010411903040c0c2d00c1e06203454101500e0305066010642c040c074042c00c05803070000f078440070502091507035000a00150360802c4005020400e400c0b042104c00d002c079810302c282445034200c00074903039040c04050f000a81c010f060108540d255411140c890f5030150003a040483c3c1b4141241c1c46c0d810407103050b404a41400e9900c00c44511100c21030300202c1000d1654212301c1d0840d003c3c40750400000b0004c1403131100400010500700050301388005481038003002003080d42c034146801d1042c0382c94209108501030040c03112045507500c44081e298056410b0310002180f0311 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 183708093 1250 183706843 183706867
    0x6080a0b15100207031106030c042102030102031501170403050304080d0204120c060e0a0b160302010f021603090801061805060414040302030d14060607020402031905010602071805130602 82
    0x2a4100c050390b10050006440c0455074010400303a0844c0d004490f00007810003028148001480300701c0c0d00108a1300100010705c208091404403181c0c0f2424211000100f15413540401e00b2640107507111500d01d998940c5444036580c7c048441c980b00b08040c510346a050070580d40240240c00060f000420814011440c00c103061404c0d0b0560340240740081c44503481c1e40060400c0c04860109000f0400080c2c8120803110305410240585411280c1d0780c515070303190454421a802c6140700b150000c50441d501c0c0c00c02e0700060401800038010f01202c2c03c0600121242c64540900070240702d901450365a418110204490114008029a42c0301501e0b804102a0f0ba0340000a00030b20048444a19122441080c00700349580007024002503071000740304025140c000038002156410446d03081748d00c100108460001810326070080c40d080003400310385070b045c800d990a084082d41d509030060740c0103900410081010760000c00d4842414000070404021500304004490210301803c1d40c003034801600081c0000e1110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 183709343 1250 183708093 183708121
    0x50d06020d1e0c0224180607030c0e0d03020705190308030907210b010317070501050f100609030b0112140609011a040e250b04060206090708060108062a041203030c0306080a0b 77
    0x71b9210050b0394a903d44548007130002c00c07407000712100203545503490300c0541c141b55140e884029010340081c92120301c3e0108129809461016422082c20624170000000c0d80e9400a540a001e540d07018082840c10308901e440079031075901021500e28a80180e031400300c0c040c6a0040d0550743c106005c4100c4500702407020409115503840109607600c0c2c082080600d00c80380540c2805040314001e21502e10340d4810045640600c0350001509001503400104003440c4400d80781400301d44070740003804040504009a604040c0b044590203100d03512440000461000c3d483d404c0507840c412030b0b04204118110012641d40d905010000380c0640f440c4c00e410001902c09007040c80100700c500ea03095551511550000e4403110190340007006482000e4000c20b594801045080c142e801c00c00042c5201e0742c0303004004641400085040920540c10010802440701c3ca02c0104058a84241d03000614449481d00400725071450194908141c90040140003500d400300341d1292294120030485c40545910145107099 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 183710593 1250 183709343 183709381
    0x14060a0b180d0f03020c030d0212031003050a050d171005040c030b030106091d0105071b06020c010f0605091e070f020c1801031416050d06020d1e0c0224 67
    0x1103460302d0b05101c100040c1e00450000d01e4070950a4504880000043c5562a90302c407043d030780075030404409100640c0c00400078551104280b0010384106035252511400c01c00048000c0d5081e821042910203d59042951864241c184440e290a940340c0314801c12090342e00760050a11860301c0d60100c01059101360444000c180004000b0400155521030950082010140c690100800c030f1821900c80341c0103100d850311030043c40d16040140c2c4410070140c0c0451082e440211200c0c0d5081c4406403408000744640310f0016088000050240e0906040145614006158035403d50382801a80c0a250303910950517000403d038240194003003d103100507428003815402c0b1540011109000221000258230400e048031f0080c8100201c000d0610301d042c6c1c0b5404410143c41d00d00d2002c000030441400c0002c04000c009011307101c018100400c5003101310940d01036590845850f80011035242c00f50240c2d205045500300c5074002030880013528002c03ea1b04028401d040951850341200140c24800007420500345 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 183711843 1250 183710593 183710599
    0xb040e0a0f050a0b040b0f03060a090212160f050303180907090e1015020f150a0f050f0a0605010318060209031c050d0507110c132d14060a0b18 63
    0xa1502402d020000c000d01d80049200e103091109002c6581041d040301380380c7c180b001d0007501072640d5000080b0b024002d041001c90300100d8022340b41170031280a1014014400162920503019031500e00000c00c05566500181d109401c00c105180f4a41449004125201070950342c03401655150714003584d40307030060342c081000716102e40204040d20101310b01c02c5042d070382880100340382d0024403801260756a00780c03009400c041c2c1c45102c0b000d90140e040c0100c2c2d540041c4200010444499001c203103000d640041d10849110640d403004d100c40041c4030700802001d00020318007001050001d001820138900d001c4c40152006074000360341a2a51403d02c948482030414040108080000a0009085500025503102c62038a400c000c1030081d0700c64001501d8000d01100140b80d0315981e1000c22000703482c550003481542d81d07034211050400034cc481d010490814510005004803401c106480290b0f0800004031940190050070050144c0c1e4040c110010780300f81885040d1100010450704d54507ca0348910345074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 183713093 1250 183711843 183711851
    0x1021020904020f130b031003030e0316080a0b06190e090a240b0604030c2711070b220807060b1327120e0301061223070b040e0a0f 57
    0x20203c40c160081038140c5150510508150b41c9448041c0d542c00b0554441e5403d0705212010804a849120100051500141580c090410841c60903003451026031189180c2c0d00125041ea00b804000b64480f40d0028050755042241c180140e050040500503015081440140780089904488100000046982e01c50741341140d00e03c00c00c0a16040126060080304040e08144151500b0b00344001580d04680c1d10448581c0400e04100400d516511548038180c18400700f00000558032415002e8000c002e40c00d41404ca41c0c48000e42022180400c1c010680c0180b00c036946c01c01802009003000b01c0801542111816494014034a801c0d8043c1050001e8150710001414000e16201001e0340005041c807450034039030795280c030f414040c508a50400c4c48042d00289245080c6003c040c003401c0240d1003e0f000600005a0300c0d110001c0c9041c190b51100306071102c03e03006140f1200040705518107201e400110b001001340500c1e106403001c0d644528001d40502000c07013030219043c03e0040d02310449010754208188 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 183714343 1250 183713093 183713107
    0xa0c0e0d03020304050a1a040501031d060103061d060f0f07090315050106031b020604020402030912030f0a200d1515020d080601170606070201020f0609010c0e102102090402 76
    0x30343e640c0042c09803600c12085244002103000800102d41c14521011074104d050910b001d0040d001814003c03814000d400380140c40804c3d608044c00040e020b54803611001a0a841c120f074907000341100740107040410343c011002d120a00044000042c1e00c5855014403c9a84d91080303001c0350500041e03032006014000040c1c04641c16003039504031605a40203a902040031b070000c5d900301c2ca0a0b000125078034002d0303007001010a015003411b8000303541c8003135a1000c0b5141a1200f40c4490a298001c64200c4030301c0c0c1e55501440b07544041c50081c00b01c8140c200300184120508086590028402d0b00040c160b8242d40d044444210a00e404410703000b014170100620503040c10620180d281e0030180f140e50006004840055000d40c0101800a10440e007800f10200951762401480b649034041c243c240d040d8403c01e00b1084584000304111b070710800c20076002007651003040402800381003211410303030300c1804004d00c0042460760062100c0002c50743d104090319900c0f4200d400310020303c10104181d402c40c0c00000d00d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 183715593 1250 183714343 183714347
    0x1a0705030d2012061011030403082703030301300803070212040f061112070311070e071202070609140102040e090604170a170a0c0201180b0a0c0e0d03 66
    0x100c41c0c030598080950400b044410039103540c1c81000c441004007840a40841c86904188502c030b41890340c981030403054140341c0640d5a1454206500c215802c9100040111056403020440d001510a90700710000b5400090006520380c0014050310202c01003080f40111501c8402e84826400d04602104120710b400c1c0381040c91144d84100c0790071026104001801c1c0f0030421301d808a40071598901408140c0d5810f01e0b608951b140015020ba000138480d0380303041c0c980c0ea00d040c07006114451007911680c8030100c0c4542c40c0b50602c84140d200d980401c0c100410005e649804c4564801c140130903110060766080743d4503010000b00380446001d010131488074107a98503a1815401001550303251a000c549683ea030201050b690401110001e01403000f80d80c10454045041020785a0b04416060007400800320081c100411034040300c0d41c250a07500d40d90303003a011980a02c01c051010b003800350710541201e641d407540b051200020b00700d440e00c80c1d9600c040740d1000b8071441d031400f040b0700c00034a1078203151005c2c100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 183716843 1250 183715593 183715601
    0x2060708040e1f1e03150608070b0403051504050a05060108060a1d03070209091203040302010b0112181103100f05010503250303030507030603021002070e060409020303041a0705030d 80
    0x30b03140e002d0300010080380310b041100f104040190160840c0c0443c3c242080c4440400a00605201e40d442074200c80120000d0403c40b08102244480302d00041c01c2441d0906091800801e80e2250000b004100700600c00318030041519400c0146012040705503031a5854228582081d00201070a070f805884d0000c15600340105000b8001c0859880512a000b4080903204403a0a21300300c1c0d5113250320401c070030001814a0041c50307502c04000303004d0310b00030868a5140d1801d64000c0b03030304400603592003a0380c0c4400c0d0f82142c000314401480c8101005868404001c0000b44000c054018100c0540381044905998040011411040d00d0754428428003903018000710141400303015251280c024444505420360802d113103421040747c40080f50314033074610b8900707031700030400139018078101030322002e012000da00c4256405410a1142e402810207070b2814640e140b400d0006040c2c248660f00342860710025950000945058600c07180a281e00711000d80301c031461368811031000801600010900310100001070340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 183718093 1250 183716843 183716849
    0x6040b03071d06090306010e06010e03060f01150302030c07140f011e0f0209030303070503091501060804060f02090a1a07020d08280f0c0c17010e120a080103021005070206070804 78
    0x1c042040d00c1150b01c20400103010b82500d2030b8241d40b10b07000400040d01c1008440c0d0300402d060400346807044038600841d05111084aa024003121404010000840700301e080081010a524003182581044003d1188502c11074801274143c4142c610011103102c0305200720081804107600800207140340142c9003d181c0c2030403800c00540c7d840d1807070510706800a4003c481c00044010040d41c610780d01c010f0240c0d65038002501d90390161080081e0ba0030340550803c10640a001d4913140c4007007a1a0030328022003030300c00e94882e00052500600880b400d940359000003105945000c214600c1d54007915000034014090700364080c1d4045000c3c1c810304d041c42050001004a11070102d110701546041e448401c1c0440200e81e5848005810481e400411b1485800e0800d800c622401140400c141d03540b41e0010111a4001007a034142d5440c680034850901c10070001003d0000507646a08142c00054050490a014400680103505101640904900c2001160034079070780240455200c5515041504064201c0c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 183719343 1250 183718093 183718127
    0x9040204061e09110301060903021329040507030e03030601051b030a051c0213030215270a0e06090109020a051303030c0b0703020c0a110d05010501090b0a0510120b06040b0307 77
    0x13003004a007440e10300003203d06840e81915004101c502c4d40d1709100340000003c002c0704505980303124011291402400389496070301602e03c10b4002e602104100012944094801014949400c4a12606500110903a5070184090030020303240e03c1500c8184007100d100010036005400009103e404494100c0041c3c4180742070300780721440381c040e40e0084070120f11410302c103503c90080a400030401890076150700065103079048481414004c24545580100404400c500d45c42000a4075030681401c280d00902d005054420f03064026040c00742c08124961810301801d01e1090700020414010f034001e42c102d980d504580c0c0c401c82d841c43e903607080040280e01d690f0802c54110f26a40c010520280c0f00e4000d0f924042c82510287ca00b8400300c0d44d50301c1000c80620102900b010001a03028049002849031074004c00410801150441c6050200729083ca03c0d03404c07491081032100e00460910f03502401903506100410400107888482400141c40da00a9900c00c148109000080001c5180e100d81e00c0205d54180e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 183720593 1250 183719343 183719351
    0x5030601120317011212120c030e0f011a040b011b0b07020c0402041d0601021f0501051c03050a030b0f120d020d030e1f09050f0703030206130b0609040204061e09 71
    0x1180e80400c2d010001c5c41640800039008440d40b001c0b9811034000c0e015502c3d2800c1c13081d058180240600c054401040c044000700e03a480c504040046024000c9284515a0b50003c00c00030984101c07913a04040d6648846004035961150200035034026103500100600006c03450a030403e05107014501c04204070344000040c05404065905810280241c606480c180d50b5040b034103090040d501b08510340300505090442c403441e44e002c001200d4800441c80d0b82144414081074640c1002c1c24413158030602042030f9500100410300b6004246c2c040141d4443d060585008545980c4940000d250502e007120803a41c00002c076152034008034000160a510b025854094920700c0b0125a000d0303003100e49680400b00550031a4922902990b42a10207009a203920716000030a50841d032621807070310554025031245c541c4040418820b01d501000065444a400d0803120740e50f401c290f4401034402c50150005014000d417038045411541c5642060015114151003025011810f01006c1600038042c45491a81494 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 183721843 1250 183720593 183720617
    0xc03030c130e06010504060c32010b030d080f040c0504050c070b060118090c0c140106180b030d03020306060c0d020c0a0911030f04050a0506040f0317060d020603090106050306011203 80
    0x501c1541a1041c3c105844050405242c0710080d902003443c1d92007181d4225183c6a00700702e0030400060f5805001c4515003007200c41c988602c9940c21554292031183c4694091000c0010581e4000040c5034080107007100d8004c0d40d1101d1919020f184040c2d00816400f5040c40200f00302442100080d060840c01020070070740e41d03100c0900658a80213124415940415805000c4c8040d10300c541060350040100c0c60584500c4249855104c07a0b0414000741c2d104a0b512203104001d0f942621806a01c0880180b0b810016244450300007030340c030f08405d1901003e0580100001d440c941c1c40030151810116540e0a80382400e106060081d2a00d004956151044000c0c01e00407401240d00d104041c00e1040544009146458501030284812401002140d842c807948080c0c10010703a0a21100d406540705001c20001d144207440c000d0151030b041403003150080b8007a420050360740e603a140d41c800545e40541c1e03034560b02e4503508000750140140b40c002c59018455240000340e0b4a0301e824250944034080e07546e65540001d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 183723093 1250 183721843 183721859
    0x120a0602030f10060c030c02060307090b12090d050307020c04052d0a06120b0112052410060e090a110f040f0302040e07060f050a0504090e0d02010e0606060f0d020c03030c13 76
    0x4505c071014001581e080c0d501401420450000c42e040303042c60034402d080307070341d50f0300901c001c0c6e0310811201e0002c04565040c084c41e40c0041042d51075030001c50800da415071074007940c020b640394140103030301c0e20580e00d613030100704402c4420b4404e01201201001017040584d5840034060401c4054803450a807901d00380b400141e01c401c40400004095001c5c0d440789899280c80071344d1454810145007685c180c0150740078080304081e501c180141c424101011070450307240484640e40411034039480b4101f4000050080b44607951800c000c550f000440718000994030740c1045030b050090103580812549418001008107030000503c0040040300e10071101405071802450902da140d041a1080d1004200c01c1d041821542c0d01078006020341000720319000d418141e8541a10341030301c0100900c00c101d50401c0100d0742045a0a020702c0110691f000002c0c1a42c4c2014008030344d482c81051515081c10101050000c84042d15070100e0b80c40e280000c0403207449040025900b03025a03c04101300442103405800003c5440d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 183724343 1250 183723093 183723107
    0x515010206100515092821031e020a05120d15050a3308040201110d02030301061b0210090608090c09010902030a09020d11011d030c120a0602030f1006 66
    0x600141c41e034012460303e14803d0300b44c0c0d001a100c036980030701c20b90085443d2886100152604007a0004601e640d24a400e050740068040c03824144000103208040300c001c0b9404c80c1d600f9460b407645241144456103c0c4408909280150750024690700415003882d80c903507203401c060800c40c4da11803030801054118400400b4106010700c5203a0f009521050200f02440440340001201d034202d07110034200340040c1d80328840030101c80c101c66000ca83c10009101c00d44d6442003e414801180c0e000610341c900a030303030004c0d640b80070520966041002440e0800012142c0d0281080d1066000c2e040486c0310f03114100140104000340680000142e550740010404140000c0d182c81040c800740200002c2d90a0482e42c00c043d50004104c3d1420540f50790030140103880305901d0803441406090070111520b4860001080e20056036141d0f21040c0c420304075504640e401064440010108813132200140030344445860a000c02608064159480030003000703002c00444c0301d403610035815014554071880c0c540d901a10781c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 183725593 1250 183724343 183724349
    0xf09050c011110060909030305060105090f100908010f0212070c0809010c020d150c1101021312020102010e0601060e04060f08150c19020f0106061403041b0504051501020610 76
    0x19800040c9444055001d500900b4608480300c080c0c85036022160590815500705900400244d55161140307000e150f403501c80d039a0020000d29142d840d040d100f41c00160a403401c0a0034500c21010351480c500100d0094186074002c01c0c0f003000a10282114502100094008040a4400c0c40c41000000c6410380b050000074100e40d40494560b0a00800030011036140f065900c0880c2c22610305074914010074010710b000c144440c5450000700c0c0411401000820741c0c4241220281143e0042c008a400c41e281c09070030302d0940e800c9c1c0703140360094001800101d0142808a1100c04e860041c42c0010840d59401448503541680c2910144006a5121403003014880b16218007429a0008000031001c03130000b445280d045845144854108004c20903001804200d149121000d60301003c138502c0312000031b0003510000c1c0300754100728144041c408040c80161000400c018440524080c039076440910b100c000c800134080203003013040300d460007102e40d41003240c54807160344c0548208800600c01c40b4410700c20900f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 183726843 1250 183725593 183725603
    0x302160b040605030406110d1407090509090a060203040f08070c080d05030408031f0801050c0a0909050c03010501120e01110a1706060d09060e030304030c1211280c0b030702010f09 79
    0x2c0d45e603840d141d450007400d40d00c080c926021001c00500c4110390b980c0c01226145044921a0b031001d0504d640060300b4a603007a804240103030f0742030040082c80d040220b41010401c0d00450056502d070f40d60300c0c0c0502d04031003c000042504202054440910200900c103800361100310741254071160542005503541d010840e0014648042000003507088a040c2c1745450b01000450010060300d511404114203460040b20103445200020031614480c9902c000030000410a40404021504220b8905042c6100500440c2d0610001000e214802070180e40302140f11001030303000300007285044c0c01c00d244990210308500b000500b014800150210b00001040c00380100401c554a0840d40c40d48107006803103040e02c1500c41c80c1c0d0700c04006003550700900013140b0a910030f640303014080c4094502040b10301c40c0f0407070b2007080248a88410300076003400a03150b2100c840c42604510340720307205100340c0485031556030010b0421101d44000101c4815000146000702002d800901100c880c198001d002c40d2404507000e48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 183728093 1250 183726843 183726847
    0x120c01090618050d02060c12090f0418020405062805010305070e01090e090a080c0102030405010e030a050f090d050114070306091505040e2d1b01080406270302160b040605 75
    0x2003d8941690203000192001d0b0006082203800d40320282418600704455000b080c0c001001c0943e8a892041c010640d4000c540c208540741c0310603600d68002203000d5000b0b018594690200340d180c0e80300840f080c4103000f00d0854069000c40e0b049421003142491284a002c00c1c00c05000c10549801080e100242c1c0d44103075110031a56180c072002c483d0f149000b81c01d1448600413011010042030044005191008070302c000543c1da801c281c03400e0b50031111207410071440c1d50028048160b140d94000c0c210703100046050410743c0c88900140000d848003643c3c1d00c00030440d6181c915210155000703840c42c4c51042c142c81e06c003081203943c0d0b501c0f0081030791210250039002480013481840a031400754030500151028400310b03070418500e4081c2c2d14007031300502c800390f9503030410000013100c00100700301da40031358070318800d030918914405000a000a580a40000c00241e200d1a02d43c0c0d503030600e88455103180046110540c10801c041c240a5101e000300403252805003810b071030103d4088013034003c9408641c90303903a90324 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 183729343 1250 183728093 183728099
    0xe1039030507030e030703020a0b0a0207030807030b0a09090f03230901140d060b070c061718010e0d0c061d0a080a030b03030f0406020d021f0f0902120c01090618 71
    0x6004010081c284001c0c513a6410301c10800c61020000707011400d1103a00203010491003030030b00d038942d0f1400504141c0d506004200c2840001d9000d4001e9800c000941001b04540c00400b0026013010140d800098001d0f140003c804c050001c034518040035a4002d0f142c280c0514064101e03003019040f21071a041c1a14801c11101c9441d52194541d42100c01083c0350050030226440d403c80309583c0154460011904086285010b0002c0c5511303623001840345080c032000d6031a50040c3c5034807005008140c05031145190f9a000b0314030300203402c0504903100c06420f5030007241c00c0c024041d1100700c8250080d20710b58070704450b10084c1400340011075542206c5000510600503c1d69603050943d0080c0745c018201500c40b0542486504e04101400d041f105548a0035140d41c141b0100078680f2005101b004115130003105444019100030030180c0e130100b0800008101102010b400030050000e01e0780082d00100e08240c1481002004250045119400d0b13940c0900a03640300b100f202c82554409500040c0301120b4020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 183730593 1250 183729343 183729347
    0x9050a060e1c0605180106061416060f021c0b030318031207240c17070504182304030522090920061216030e1039 50
    0x4600d088004100700c070b40c1c0300c000e01d540010050825040b1005074940e0306100750501c0740340c2c1d03034030041c2c55900081201e64944030f4010000f4668050001220100140c40310041840d5881010310039003180303040c0454a050400300009611410001c5001218452744010780240c90203984103021000b0000c604280c100d03642c0450441d070251255916200b40382000800007601c80182444500681d0144c0341c40c070007021420708081c80b4848040445240562400c6034a40000e00040303082600b841000c6107550f8a181501e00c0e21850b0060f4958101c03000002c0c41a03030054100d4529207a400c4021090143c281301561110a400d60f00100441e1007446903095132040c500100044981030303444000c0440d0780704004801c80d044400d0590b00c6034111400030000c0c440d4410b540b60000c405480c100c0ca002000d03252840340500203042c103040d241c1400c0c2c4c40c00d02c90748030342c0008400414a81c1a260341000082d1040c005010200340045a03403079142c200c516400041040b020760220304140d40202040e50030301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 183731843 1250 183730593 183730607
    0x60b04090209040b100207180c080403030504050708011404061109010f030b060f030c0309010608030406020a081602060a02250302060403020409030c08190206060402180d05030904090b06040c09050a06 88
    0x49a43c01c1030b5259003182d002e54941405040b541c010b6000740c42520b0500d044c2c0700011400d00c43c1250800d051402c0b1031007440e0700484071036126801d403400090b2601c0720f262440c103200c1d855116058035030030140000781205000790103d00441c41280200080c0010450043d254095000890f0205501714008140e150098100c0114101c1c01032541d881c04000781e500c0c0c00a500240d401852101703002c4100004d1280c24401c0d40040e002000c019400c05242c120000d50703a50010a00031308010001c40d9054400200701810350009138010718594a825109034000d6503010b10001403c0200001e01444400341400d2240303405907034024145514060644c0c084c00041d1034010811010043c0c00ca0020022440c0c3c6ca02400005840650900385c10514140003442c189001c5c0030144075030b104009242030401c4060180c4106a0f00392140400c03101182450703411405104d800325005400c000342c04003003100c45400c603032207544111400c12220f49018805c0b0750000e201e004840c2c203ca442802486a81e0040321 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 183733093 1250 183731843 183731857
    0x2030a080f0108120d11030109020a110c0a09180203150f011a0306060c19081308070b03011406041518120b07081b1201030b0106110a0807060b0907020a050d0201060b040902 76
    0x200403807504d40301950b1b901958401da001c000c03480d034045101b90700e99600800407200340d124080101410004180015150300c0c0900c107560441e951946a0104080d8007102e00018036002400c6e1040070407540a0300303038a50400c490030000660004008501481141c90500704450700c1d8180c18195990320007072006c0e0f540100c02205d4584900302905c0864000310150360800c0d403007080480d4484203520a100140190f50b0810035158029980c284841d90003c03003503a0440340d6502001c40480c0840e400705070340380300e1500701140c25060f106144d02030780e412000118070f2481415000060940d9042040080c00b18014014017154401c1c02081a07140b18448190f040f400880f24840420392150300322613554888100c10080c8508040104240600c841d08140101824104614030815507415561a481e050100a1401f84d001ca044024880558010390000c10060b00401320760410100295071040074860817101889000110346801d071040c014541181c440c20f070f0f23031824541491200406034012403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 183734343 1250 183733093 183733117
    0x3150908070b100504420e0a02090a0b090904060b12070e010e0f09030f0703020102040e0a0e0c0f1003090816080307030f151401090302030102030702030a080f010812 73
    0x400700c0c1002c1840e407042207000710581030709596128030b003c0611082d100000d10b50103016014005044c6543c84518000410841c0626006848140400309012a03006500301d106404142020031a042c8031a6004001007202101d00401040d920406004988500a0165000300b13401c00494005002da801a000314907000740080c040114660313555241c00f1301980035020b200c00c0b0304010807100e0b140800740f07508a0b1203410100d07460300d0304d0415541e491040c0301d043c4002c05000191102810701c03c2d4180c81c040c000d003801600781030401c000b20002503c4080701c02c1040380100740c1e0b441e02518150044041040015090020300741e02004160000d0044080540d00790101700081c000c10192010b045002c01d02c81c040303440e240d080c5481c009003201c103180329140c0c0751840c2c110342c05991040c0107081e5003210030540c9220301801151004031040b62583c0e100941540c000710620070490340201c080c207d12940d42c0e0300d03c07041c0c1d42c4642041444600c284100d151582000740c0740b00702e0300c2990000301045034901c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 183735593 1250 183734343 183734347
    0x1b030c0f01120b150a0305090c0604030f03020313150f022a011101051f12020607060c020f0d0f1701050a03020d0203030712090e06091510090801060e0f060a03150908 73
    0x5102083d0509640b13003074260407030701c00070301c0400710364040c45499042a81d180043c40000e1101340450740c11300c220701015208079419885c0c2030416208004075600038088810014410780d540402034011150601c80b0008030303012008031450684000703035203103030062284107821a001c113002122007000620300603141000040d100920841c0024029140100030381580c000c0e000c4547c03280d14031001e10036084246460100188040580ea403841504c01e215044200090002810b95040c0e1404001d030030540e010b40a10404110341540040c010000e00c8120b41703602141d403039031503130403030342c811f402d001c0e030755100c3d40700f9800f8009800e00c0076417100346d2440030301100e18050446d251000c0c0e0b040032598660000c1c5e0000020301030034154070512508a101039480e0915418103c601000540c4900e11260045108000314040140700d050850001c118010003007100740d03111124803d1450044981400c6c000c008408514181002030411086079003280c044414140d40140d154040c0040d02000d54007a101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 183736843 1250 183735593 183735611
    0xc0203090108041119030f021f020327030f1e0a0c0b0d150f051c0201020c0f0a17010501090c170415020909090a0501050a0209101115091b030c0f0112 66
    0x107050044041c5000300f003401010900c2344104409200221034042103d00600000240b40c0c0e000400d032006400d000112503001c41030a1408003102d0b10301d101059141c40380a14a54581c40041416103504901c1140c00c0c1c4060b000b1540e0940d1000350341e00040140071010f500300038080c8100003501e02404903100106651825501e82c003880165500306114007540410100143e02d081a40c9410ba0b81c1c0007003942d40021507580010751035070001d4541c20701400c0908480b050641e6020900b80141c0042c840c0c11100300003a5403914001d2000340100d41c041c500c0c0402c0c0d400c03c13600035075040035400713902042d0008030b942d40e61f0360100f84809184064645a006d101121080c0d642c80740c0f4a00c42c80c403d4009242c580000d0501600307441c006000350038010b2041140c1f02c1680c40e03840031241180c61505242300c8403140c01059a01d814181c03000d022040800400388107100070042020b1403040a0044c0303203100015070408068840310740d07a1138658071004c0e038420b4107580d500400b1030104030b403000c3c5400a41d10314 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 183738093 1250 183736843 183736879
    0x1080615190503010e0d26010b03060d140a0501110301030209011e030c0e0a05060a0b0405040c02100501081f0507050a0806040f0e2406030d030b130c0905040c02030901080411 77
    0x400c000e210b403900203007100030001e0b80c4030111030241800240c0740340390347d141040050020803041c0245907201c3e00020010b101601c80600348500f40f58042000150b1200f80590039841d01c95200c0e04803150b50070901200503400e003884c2540c2c140c98006081c80703078a92030851142080c0807224000010b20104440000104e60400e1110000b080400e41100301450401003500889100406891080d81001410300003460000700362010b440c82a68001004a000b2500307a02e80454207000b61032280c10311001040b039103000f150b040700c1051098001c5084080086a410a50300102c3d80f140024005004040009214181940d00700300042c0001420125465940b1b00303685180c0b40001d0150300614a4009003139052031071010440507040c10b0011402c0240000c3c0d150080d40c8160020552103014020003540d90b92148075a010044604001040010002030000c0c616441850310942c54005006444c500210403a000c45d601651380e5061507440342e0700c0c001006040260f0310b030002014850600300300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 183739343 1250 183738093 183738101
    0x60f01140a0207060f1d0105090a0b070f06060608090a060c0504080604120e0402070503031306060503030d06081c0f08090708010c0804021c0f0b04111509010201050108061519050301 80
    0x711990780604649410f08001030320380c401c0c0c2c0b02068104104542201032414103151711124040003403038a140d5940c9800009070364502182c001d05040c4c0b40000d1980f040081f2445080001c512542080c070420799079000c140c0310034204481d0342c81c098020094900000b4800e40c13010300c1d4070555007405030030140c0b1041c0c0c00e464604100d0b42140c182030084440d0001e160001094002044c0449065160802d1940c8441d2240800b806041e03080f540c8020060400a0581203540506400741c1240d4507941c51200d007030003404492081d40d8241c05480c01f9202d03e0003410381a02c1c60225251100c25181914010459035207500074541003250003038000200d039500c002e008030130201c0c48030340d03401d503031403c00d401001200b444d00c1214991810040c60315400091860014983c1c05d0b0708482044425912820030f18801e0740003000c42980912200200340d19011004094095003000380d00803c20360ba00d0798030203a9100300c01d40703410441080e100480d402c18030700300602e02131000e04d100d07854038030303580e558046820340b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 183740593 1250 183739343 183739357
    0x1020708030403050c06090309060a0e0a0305190c09091709010e090106180b120c07060e030301030b33041d061005011202030c04050f010215070801140108040b060f0114 74
    0x280c00185c8581282020401c19410501800213146001403500002e40c0c544170b44640034041c0540e41c07041c1d045030354a44450703500440d006000d82d4546403290003003951501ea8400c0c01c48140341a988080b072540f4061103005529075001030101d01a007503445c08a01c032500410012410060141d400202623120403840e68000c18182d240d00c40301210178045100c280751542c0107051040300038042000000d091200060b04807558070305091f40c404407030819601601020310566405d03c40040000100054081c2c030b24459405114130004e0031001320104003419141c20399078a016100048107180c14541a40002150b400288128100040507110039081c15001c880070040c4510441c0704020558011044407071a8038000c4003103180d480c00210f556050b0145001d124020716000c1c4c200d02e916402000109900441c42c240c445c1c00c0d26103460b000b40031640074040d5040d030801284e102e0f85294000d07900c10f4044c5d0351100c0c8030600d40c0d07142c80c02d004402e410f203494141007209035004a8000f0b8001c000074014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 183741843 1250 183740593 183740597
    0x4022106011d0a050d080c120301140d05210705010609050a11070308040807020d0b0a0606140c10020310030807030f09060e0f04050406020c030d150603060b0d050901020708030403 79
    0x551034104005003026010b410910b10911442e40a00c2c5595a84803202c415076004582c420503110450510b0443c6010b13a03040112184100c081c07035103454010b500a107048905841011844404110a104450f6006040109584e000c40030b5201100070080400d440d9104441b503d9040802607291142034601c00c0c1d10040780d00b540c2d0010f10002d824140a1103594401018044e460040c1960703004062400c001c00103080c24001044180c2156a404118507540790062101c01c4a4240b9406140c014a060f12450002c03e00381d001340d103500b845002c00d0762081100440907003402403140d010326011394802400f5000c0841000c0002c000584404047c0142130b01941c0c032503408442a82020b02110190340001341030060205400719280d807000070712008032109640109850b100c2d031900b640a07010700d00b00c40d601800b0200e000704580d080e036446440f06003001071000c481640d03140400e13012200d00d80a84018031000304150919044540c0215410501d072500041c50485603848000032a0016541100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 183743093 1250 183741843 183741907
    0x50d060b12101b0507020d120507060c3b1302070231050f071107081e0105010b1204080a05160303020304050f010b0f040c02010e0304060810060e010c0b04020402 71
    0x100f0141003c1c503a0310418641c100340d0b1800c22542c0019403000141c8034000c1517083d041c902d42040038031540a40710440d51102060000080070100642100303000840101503490407041c4850313400200c0040100188490a48090b20144000f80315150f400000104132141d000c01c068801603d50150503208800300070038a011144803107449061001c104843c0d280c1030381c01c00c0240b00b004a82030590ba5003140c85070074460320b0700c01c404500718100709069000c01214020901d20038421750310f070307c41440140c40c5d21008110b140c1e00d80341480c21600650f902070b2403450300c2c41d000a00151814005144050302c40c1451401c004200030390201c0b4130003040084000079008824401081410050f40c52241310304002408200100c502003400c04c0205800300e4403031500c40744003100c170074000e50100086001e86801e0b43d07612034480b10007420001054600d240c0600300312400141c04c078070550071440c44540595035505980103c1c2c07205410100c002e0710507a400b079401c00000f41048a01401105446080c1043d54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 183744343 1250 183743093 183743111
    0xd051914030a05010e34020307080c010e21030a0506011701290c060105010e0a0b0a180905040f0204020d090807050109050c0d11010807091e1505040311040903020307050f0c19050d060b1210 83
    0x18140ec1500140d16429000086c000321795062035405e4a90121319480001000ea5810340120b0713001000161407190065060004950304003610030340c0620840c490903030f03000300e60041c510000314405c048c000c0b2a1a0003130070041c00690721424140f040c510005055072001500c031210301d45141e024100c0040800c1b1080354207051203404003000002401c81441c1004245031030f44604c0d0000c82c00c4400207215036400655255820355aa0200d900590492007613030319685246000f500030f0140d40000d9030b2a00c503007400e01d00c031894000803d80d487c99010301030600310400b81d001510141c6c000342c4100c051060100c00402c00700c0401d000c6c111210070180400000e40c0c546004041001d1002d2049001c0203000c001c14404610300510341000004140c0f400034018209050403130842c0030301e050090190045408000321340070001a0100303454011607501005180d403500d042001c040c00d2150a4200000000c442c0120f489640103c440403000390186003003210641006080414049090b00455610a656 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 183745593 1250 183744343 183744371
    0x903020309090a0917180108060118030305070c050a0303090e040602250317070c03200a0c0801050a02030f060418020604060c140d051914030a05010e34020307080c01 73
    0x50202c1030000c1c0170303843ca41420030030b0b580001044082c0c058144008000840c07402d0340715803450700001206901c1810fa83e51285030007002d035400024241c50003081c06201245520f4060b48610407a6810348501249c18034004104c41c980000034400d4642690900103c0d180c1030b00f0320752082c52188416100045110701e494041c041e5100051010090324407901040005a04440c50600d915003604144000c83c410f11150b1201e0307000d0050440c21340c0070b864454420040340c3e0b82d18006036600300000340300968840784540220b020448038070407540c0045021403540d00f8280d100540c1001040b482c0d440021558011440c0341d031103544588000703802484400d090000380d4020140f0448110b0203403a004a00000050090081d89a0710018030807440000201a0041c0c94504002070124115626460210002c80c010070091003450b0502020800262031003220301000c06134200c8240c000c11140c1024100700b17000186180021095120400c6070340046004035010b030030602c13080340020030104850849 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 183746843 1250 183745593 183745613
    0x1505070228020d060f05070f0f1d040207050a080903071a0a050a09080703050109020405060414310c1401020a0c06030234050607051c0903020309090a09 67
    0x2888119001586058442002104400d2024501001007070824019000150601c00400d000030b20302c500d80450a00008055001548501000c0c1c03104649079031fa00400740c0300e0354080045500095003009001c0781a074000e944c1a803059101510040c1820201d5031200d14111074004c056540b00d001084004003450100310305000383c03401601c01102c5041c02601a505402001c40041c140800441d8089035903108d84100401440c0300c03070807160b000b80d59050680c028070208205900440c1043c0c001034950600b40105451040040b07680c40c0c040d6506035620404603425100312400901c0611311b030b4030074030349a00018807aa004d110300000c82803622000d116000001a01c481c19508215500008224202c10744004c40302c0d54100540d40d18005071017103562030b240c02e45105182c207a403d011552148246560b42d0b40c2c510803022900369844800f010744482c01034400004802c043c130000c61680d401c194000c00c10180c0309004890814441031300251000c10700f07c6858280c00d549000f040280000c1c569 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 183748093 1250 183746843 183746851
    0xc0b0108010608070e060315010e041a01050f040e1c0908100605090408070f020909030c070501050f040b1e03090a150507080a090c0509150301052d0705040f031505 72
    0x8001c2c00345440c03101e58844207188200100d21250100080c241d440510001c100e40e284224010015070719a883c2000d070300401d0b607040e980801c0080c6207007100c4c582114814183c8000074203d20f0406001800c12004d80f1519089502e0b5000e0b403103104050614103a501c4412842585403100f6007070500c0890b80c07a00c426040b0b1400c800e4100320302040303503887d01c0c0c1280d0b82040d04000e4080e6904010708042902c0925540004c0d044048070041181500010000e043c152800c001542e0051b42e450004554602915040b594501000c2004012114103600180310800c0024807041c4038040141004035107030012a40c51044d0340007a980c40c010085103403010316402c0d9102c20108501d050000c0c2c000c004040c0100b19202c050340d1003001e1400d0000142070310008100060200e611403900c8241d0441c2088041d0047d4065070030480807980c1b544106845000600444025031072219105241b1401c900014003a04140041044041800303503400001d8405140141904480740c0020710040c021188014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 183749343 1250 183748093 183748109
    0x612060b040b0d02210303041a06090402031218041107030212120a050c09030a05102307050f04030f12140702030709020c150f040309050a060806041107120c0b01 71
    0x10b40c400141d4480250a2815805030785a101141015803841005410310542030740034070011080104010992600d007042d045001c1d07070704030305490301e0f4240a02c04078240da000f94550001e03007400b602d00c810f0001a100b00c91f0070f00200c000a003110000b0600710741e040ba1b900080c4d51400201e100a2640402c81841e159041000c4145010325840144610369000750600c240d503a00c03030002c1440c81149000341d541d0080000d0a441e83c2101514080e5500d842c0c030200030031954105400da00c41c03c00d10070782d5101804292001500d295445da0012103181d4004407902d001d01c20240030100216481c85a01d0b0381c02c1f480ba048042d00841a110040c05880c1c0d101080c041100d400c1060f0001a140855004122000280c0260711030002c0c1c41000e040c000d2402d540043c0c8050300701000140c040f155110ba019500036120300c14400c1d03c0c6c000340014082c04d801104081400440424080c0c2401d40c0086681005001b04901307103415640d8603941104052804000249504191401c0c44046821540104190 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 183750593 1250 183749343 183749351
    0x60f0a092114040e060409060902040f060e01150c11030f030406021506090103030c150f020d0506130e0714010e04091b08070609030312140907080105070f1d01020109060612060b04 79
    0x25072001d1320340301c000b03003440c0c0030b551180e400c5000c00c980707900b02a40c01c1ea80200700f40300400a402c0880000d00542c4503d50313a408000c03000081c1d801d90b000b00075003120102c2d502c8054130503031074036030169401800c040f1640512508440348820403040c405040503000035405031034045807024074440341200141c1010b03c43c458800040001a410080f840031940e4041203213083d100c1c40c0035058004101c22124440e072a400056003608140d081e030720252099104861090305039040104c2001100c08103104e07a269907002003001c0c444000710100040d0100d00502d00944c183c031020f0003140030744d0401c91048916180f9440c1c0c8901c10014411800090005c20000341141460180d000b01401e0311444050203119108040034110206a00030b41c1c81c188951003080140e040030a8081d07902d0025128201080d440e250105a519200c2d124504a40e2880da55900c144010f6040e103140825140c0c00c80c60543d0369941480c800100e440c080d0394014403d49144890001313450800c20162404481c4142c411860 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 183751843 1250 183750593 183750599
    0x405010806101a0a18090218090f010515030a02040506070309030501050f16030b1f02030406090b030f071b0506071805040905120717040f03061404020102060f0a09211404 75
    0xb10810b50700341601d289030419031200104a00031030340305c50ba0041c41c1d10600014a00c80c0d403031680615092150310031b4492400c41d40d208040d0414102081c005da5502c60b05480c42400d1a0003004051604490021001440c0c2607490000920950040701c007280444c02030703130041043c48002c1c81810340c000980c5a01103003500e4200c11840030306090301140800d0503a10000c03441d40f6110755600c0111089510540011f10340182030181d41c80e0000c2c0301d003900090301000c0108103003148800303480c007501498030f0304c0381c41340c03900c0c10140c400020b204081003c10f810f07103007690b020540c01c015841c00362a154417a19402d118285809651a07680d8000502542c20601d0020010b9800144084803aa04940c540e0701c0d845a403800d010040300c2540c4100d1840000b14001c521016640d14040c200c920824082000c0f41c500718100d26801c0d02100c029015030003100004001100341400554801800840050703840601e5030340c07020302000048082442507401c0f0142c0c0340c0c2d41d0010b24040c101c013191000e0509083c6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 183753093 1250 183751843 183751889
    0x30309240e040e0f03030a021206060a0c0308040204020f0d050106030e0309031e0a020607030806030705040b0d02040902040608030406120b0a080604080705100507030507030b060a021905030405040501080610 91
    0x51010100380119039034080c110144601388107614400c00036038150707035690402d066400045d411001e0f01d00d681689210100348103240c40e90444900c130725113131100e80b000007a64400b9140074a006005076009a001c02240b02c000e521072004204008240400007102c0d4140000142110b0500d00085130035401001260070aa90024100b000c90601211020041c1e030800c189a0030880c240c24000d4200c8404036040041641041c0d88512a081c05c2c0c089034603569071401044299200c4d030b4030b40c0c0c0d00080c4000450000d403c181e00600785150024002054003540e8403001c52840c0e04c81d501c07540000f28455048a403489441c064100340000071130700a07611608044095840c0c000103440140203040001d03512080220074402c20200362025141000203103044000500545400c0302d500c0c0009241c4070050703825150290660707151421550040c4000607160800341c3c01e5000d042d805903400d100034000010303265030314081c0c80e0280038243d020b4070542c20701300f03d05182c0b40101d40001aa0320203100c0c0d0004588 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 183754343 1250 183753093 183753107
    0x12150c020d1b050307050f0a030e030d051c0b060d02090405060d05030306220c032a020303130510090f03121103060114070209010602030a12050f0a020705031303030924 74
    0x1064600c8064803100d01032a0081c42c0d403003501002060f1f0f0040e0360517039582c0304002c00c2d0500c065000c0c1d1502404050800c00705501d17040803181c01c00210ba02803088200d80141c140c140c0c480e441040900141c402c0f18900024516041221105013050300000d0391811401e0502034190400015100070101040681e00c0c40d8403404000d107100d001e030f20000c0c95008400da1514101941d00740d04007041107170811700400103001e014080002c07280040401245030700800c904070340081c600710b81d901650440d12100d02c00034001c02140c4054520344200c01503030741070f0383c240e11400300e50501c1580903074541e8225140c058440501456122078071f91a00203240b100705542000c80b54400300034600420281420701022020f40101d0402075040b054920000c00c801d034000000706100344580e2555a110b01c40c1e20847c80556204507001c031402004500030036585001900504080d030321540c20f490825180003407050f84541c05600030b130009040401c040110a81c0c0604034020007440e0740701550444010302c0064141c13 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 183755593 1250 183754343 183754367
    0x1503050a02091306050f01090b060c0a0308090313090b0109050a08060403050a0903140f060c0405030a0b0a0204150905011202030103020102060f090c060417060709030b011503020412150c020d 84
    0x1048544000340386081600003d07016681e000000704200c0c20408204100c98600b40280c3d914203140c0440d8021500e040070603070750001d44000007002d4038071450b542216288006007e00e01c0e00c1c441441a40030181162100c0000741044080005107640c001d40010300c550b8542d40140d000c1d2601c001c0502007240f01184507940150181031050740c0b4003414208680301e40e004d50003e829070a61721034803a0707201300114240309001182012070b43e494a81101505803841a44141c69041d801241c03d20005210050102e40c0481d54110060429581d440c503107800d20465604000040c0300c2d03010900a668002d400222002c62001c0c08500303560555002070b5503040068200c0d4001700d946170020304054000c000352103802c00c01805240d01c0d513a94001d406c422800c5048112020f0090500080300035103d00400d030112a04440d205034203034a0032040d04103a950541c400c4080540800001c515820001051201d0a1040c02c8a440c443c0420004c0d0702241c0c004e00c0104d003103410094103204c2e0700754070401e50301d0300c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 183756843 1250 183755593 183755599
    0x6080c071e0f06050f060402030c04030303051509012409030822080319092c0703271a10180603020d0803090f0d050a0e010c02030a0507091503050a02 66
    0x149456a00d102a405025040c00070705044200526008104442d000103001d205c0408580140c0d0320381508100503070104a03442808900b0902040000c80c1c86500b041e070b001491504600044c20310036021070180e802c03d13004a031b04507050704000881d120208074811509080c0d858840344031402c56584891a100300e24407926042e101810030800841640038080083c01d081040b240d807110004903150102d00b601d21342c080400c500c1c0c9030000b01d602440c1d00849251110002c1080f040c00103a48455030200080c208404050340c895007810a119001c0340180c1ca19000c80203412070f9039862900c00d50150310311031810310f041800028400700c2d0301e0010400e019501e03c810040c0c1c9180fa0211072200505069202075840713072194551700140400c100007580151490016540010f92002010380d4506c201c1c0c00c500300041c000c002a242486c410b103280415032a0501d80b64a180c2d81d04d40020f032030580004d40c2a501034201102c2000a0406413080082002c0c5085846203074618544a00e80c60300c50030740740680 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 183758093 1250 183756843 183756863
    0x120b012c0301050115090603021903091b0303050d0c02030c0c060d09050111031f0602060c2b1b0e0612101a07050706090506070f060605030d0c050706080c07 69
    0x6038052998880640000d03000308860740e520000403581e040c800d000c1201144140001040c0c3d0b41c841d00071075511070341050b17108400a6103040e0840040c1284074099519000200d125401c24540301c03c8280114042c0d40c03140c0e21601d0081c1048102c2c3c41481d21041036520400030185140d00100b450a40c0520454401d92504002c81c3c580b0060682e80710000c080b5440c2c0424102c0581c490005180151100c50958825101074642c0100441c03150040c9005a800b103400686142132000081840c804407991402100c5040e24405001e02d90640e4182042e64607480e4143d0b1180d134501c400e24103640b82c2d02e004241041954081240f910a40b101c44615500d10340016042200e0401c10301c0083c0060380000a040e6520100c0704803641021008852900903120000741e240c1c4980e0f07260f420340e5002010075290007841c3ea41c0801640e0540c10480d8281c3d261000000c0e560340038401e42d444041c0b5615048103140300351800c1410300d00c0c40d8001600b84039044080c480c100c000d040944a00590103800ca034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 183759343 1250 183758093 183758147
    0x6061106070806011215031109010602070b03091c080411190308031e010314060702011e09170f0903101b05030424140708010b0a0c2f01120b01 63
    0x1d40000c082c9416400c0c01c0d080038041b50301d08400c401600c04580c000c03816406c00c1500c590400240f134500b8031451006a00032038003802038420b072030300454000341075100f00c980c403926a000b021401d5144040c200041081282000705104440e07496120540e0116044801203821890301b1a40c02120f00001d00240d82c04400200c91180f820520082e19801c10760310101c640c4d4030f203095403010410707041720766290207041d010510311342c014018a01a450160840e20201042c1c00c0100c004200c003078425a0302c4420442c441b2882950321004041550240541c10b07560400d04e002d0520306444091581100c80c60152010b00250082c07500b0400002c082c5002c590729141c0d8180004040700641060800801845c0c084103001c3c5d465215100c0790010b103900900d242e0300d050055a00e4082407003240000031003002988aa10320604014003414803c15011544401c280c0100da031000401d18211401124000c009240b580c100d04140c40342c0512035814002c030b81c8043c0c0006c0c2003000c901850303200100315546203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 183760593 1250 183759343 183759347
    0x503060c0a050c06150310020301080a14010912080a06080c10080402031c0f09061d0111030c07030606031a01030f0b0c07060f0b011e140901050c0d05070302010606110607080601 78
    0x22598a04050b04a0301d0f507041505c02102c4070844141c66612074810030070314051002ea00d0007075a040700d03036000240130102107035140c40d0345160181d180403000303540e03a40f40e0304006a400c031034038002420a60394901c41ca282030789051003202c1d0345e50080c0c41143d1000000010707994070412440301c80c01c6a89041d41d03da491381d1021a2a0500d4081045100300c4c40043c103200c40f680c00810f100b07403020240d03180258203940b96000d031180c503100042c8010659849001d50903a5011f20317015103110011800b1603152550160750142400d08940085030345e0341c1c8030783e07040003800010318600b010034140745160780003549981d40d40034074100000f9004003119800c400181c085d000e2401a10441a00204103020041038a4501001015201e034818046241282640228454007500c1841c0000035128480c031201400b800e440c1c50b0b004000d0481c1008020400c642d8002c0c020720480e0304030310340f946900b52590406c1ca03002e0709640704ca82041c801c00007082031111a2140000d00b443c1c201031241401241d5032921401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 183761843 1250 183760593 183760597
    0xb0721030b1804021f1e1214061002031c0905030d09030c1a06060904020c0c0d0b0f090309060f071b0b0720100f0e04051009050901060503060c0a05 65
    0x101591201d00702e04031200c0c100030031102a10591080fa0b02003c15080c0c5c08468500d104020581320004820082402504031400d0455010b030020f410b20340751020003074811038150741c105400c000c4882c60701410b1014900700320950480c0c180c824000b031414120800e0160080000d50581400c023070361521282401c0c803d0034001c0380c19040c1c415000f888050140d041c00342030b40080070001c13035046021501118880070810a0240281c00080c021844c00002c042000040d400501910304d803401181076050466690503d007911803441680340d407089142040202e061401e00409052103600104039444003a0f95080c126154100125802516852642080c26405900551506400030380360b8020640c0c0d500308024107030161140907990200e2405c5445034032081125000c041c2c2001c0000707007410f409401504d00d000fa45c2c86616100081100100c00242038881c180c41d401580003100390280f1003404a030048a510440c02d800900c0580d04e8071000c40d59681006190401e01140864090501441782003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 183763093 1250 183761843 183761861
    0xe06030a110d020304050d0c112701030302060412020105190f0f06090b19030b0105090702030c0a08121810050c0c030705070503061003050a0224070b0603070b072103 73
    0x9105600d4545074102c1d00000d5106440c151600d100f45200503001a10075400f07420b8090384400c0148505000005200e90844207124082241d0380d41801c0060392140c90800c0750081d8041c0c2e000b88442e0415060940c0307040c80d070300003690459040030108003003903510202d601d4401c20216400941c20507a9240c440060400b0380d119581d4904002d4000385510751900030b546005030442e00300000c00c40140c9000280c00f920f210060034944140c00401c5540381040001c1c1d40410701d40183c914003c4070149043c14041005411154820301040030b1601030703040c94441d076104412450701086040701c100103690380c180c040c81e12160152a440098440c0d16503600717071564008260203d945480ba1031a0954654885000d61800b0344a000b000810500d0340341c1d007400c1101e802001820040082d5000c0c040781e01d90080c40c0030303800c0c4030040303205d24401440c5000340709241c05041c1204683c07d02404050403d129507200304a410002d11942000c9024080b5903540e00f000e003100180381000e1480147d01510041e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 183764343 1250 183763093 183763121
    0xe0604080f0d0f0e090a180f06021801110303130212150103060507030203040c0b030604021213151104170c0a080303070201050c0a1202030a0b030706050904110a0e06030a 75
    0x41d41c015440d40001a6100d207241940c44840e84114081c00494000c008251981d0b8007840b600302042090758a80d12910800502c90040c0c440040036850718416412112812120075900007541c03803120b00724485410705460240b1740b643c445071145d04c0c40f80e40e0f400301500110043d00030130400c104543d00c0c0d20902c02010100c0007692520410f0303c02000812600b44001d407020b60401001070343c0d061182c0f00304ca1007640d01040181e4010300307108440d80725420003031805810030390170840940140040c06203503105400740c418400d40300005240c2045262005007091900342d081c900c03440400003000082d0303002d44112004640303020401800880c900400f4a90054000922a1f40403440c6ea80220040d4410341e5150003c9c801500e40c850034480780c0c81281510000550b42c40c8400e6080001900215044200860081aa64188400282041507550190740480c0e00000e505580c0e0070140207007016034071400b40300781c00d08543c4a0b010f0708100324642c451740b05060000001b59000c00c5a44480741b2900e0308 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 183765593 1250 183764343 183764353
    0x120209010303032c01020903060a1103010b0304030e0924030109080f0901030615031506020607021005090c031e0d1d01110f0609010504030801330e030327030604080301060e060408 79
    0x5140c43c002c0d0f021f5001c1e0741c0030380640760004521030384c1c0e0b010382c10300d60403580c10940c516882c01000503901d40000e0800c03400c0040e8011408402c1d80c880242c1409040941d00d1442c1d03296118840c0e281030003000d80034501030f90400340010081414103003652001c900c2100307440c0d90741c0e170410700407402030030190042c2c00810044034010300d0066056001c09035440041100342c143c55240c0d9010382c0c6c0c6000803280240140d00100f61000000c4c0c00b5082075800445042c2104e08810422002038180b840c00c401e088210001d4483c1e040b0840f800300b00d9460240001c3c200b4002e50030381000c4c0328000350f6144080905210070034112a5011a04000740c8a0450454041c0c6803d801c0181c03106000c2c0006031400e80c001800c1c00c0010402500c0da40301c0d0029010442071042e6900c0038803c0c001701c01d400340d07002d8509002400b4050141c50314140024184492180c3e00220760446280843d00e500120860140c02540180100000980c1d81c0c000c032410f544071750800c03820b14103518000803094410b50304010114064 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 183766843 1250 183765593 183765671
    0xa0501110904050105031f0f110a030509011503110607050a1a0702100c08071110020406020705041109030a24020d0504020f040b010905010c080c070e04060612020901030303 76
    0x1050000d4100340320100e41c03c0c421666203404150303480c10315007845504d4003031000c0b44e031204002a40c000f109142c54180003141d039803104042d118840c0c0003c95000b002c40c0d00c1d2001c020070f4a6003031042c56026007010441d140b070303582103440d00d40e43c0000e400241070003000002480418400b0400c003407000158050790581000d500492200254001650400c0c054030500ca8500300b20840c5000e040c140c1c8004daa00c0011540d1000d400704c070303145030074440307400540511a250503c0000c1400100041c003941d40080c4001d0b0b10740800d006c11a011a10350350340f4007400303000003d25594041040b10f01c80350810003445010400318409602c103041545268641840050302010700c00480d00101d00c81d6001311011060542d41200780310030354601c801c0c013b00088819009100c190300503201548014040d40346281481d81c00303001c075454100c0e40d4000c14003d180d100c00308400c1103280d00840b4060503c10b1611495410300e680810103181040c040102030540311140d44e0220709020100104c0700d07404070f4114405030340c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 183768093 1250 183766843 183766871
    0xc060c030d0506010f1b020d05060c070c050909030a1404090c090303020c09101a0c030301170f03070c060e01020a02030a0c050a05150403021011061608150907110a0501 74
    0x10004107214405400c0c0400540c6a6008001c1a143c9082c2601c540004c13446041070400a00c5d05407000700e901800c10354610012541c2046082d1103824020720590780c419060a02d8410304000354052440f61200c142046110700d008401e4821581e00c504001d8500760030401030418a0240b07810a6140d0352a01c105401104d40c4003e040c012207000c1c0d000d0700c43d8140e00c0700c14810071074412100b0760390024128004000650138142040060740b440c9440c0b07403c0899074009142964021b03800b034a001102004050311611040c80241030b038249041c021880c0c14441e95481401d02e15500c180c1c800e1041c00f03560300206900030b1040b40c00e0150300a041d140624100d00c0c3c056810001405807034018801c000c00030409003480300d039004e0f0f030700c2c20b0942050410b4035590812040300b0b40081c1c41c1007000f0940c41e86001c0804104031541c001e0b1840c0741e441030100c0d10000000c040140c010f100b1101c80002108031130864869428a036006100e0b40f501e0101c444e505500145003042c600e00080c941e41c0792000724030290b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 183769343 1250 183768093 183768097
    0x90405071e02031206092703070204020408010608071d04020f0a030212010c02100b010801030b0c0c0708030405041803081303030204080f030315010806030325020a080a06050106022d0c060c03 84
    0x7000f40700aa40345e01c4c0c0909021807080111070a000821a07450410070300322003203a80000d1041204112860400c165010400342d030080d900c4155a070b9190a002c1c0081c94090003507e010f440c0c8002084612141205071102010002c0c002034020140045a55915141d03c4140e0001c0d42d0050000c10079044014403107802402c042050100600509a140301c20319903502440c0305100c0705130b4466203503900b181c5440c644444080c02d80d070404002003007000701110381400501c0007011480051a19a460700050000760390854401440001000c03007160002500700e18403d4003d84207900d41c040d410510300d800d03402071150b40c00c141486d00c2105000f0b00071000003c02148100d129071401c1d211304030f901d0010340700802c0c25030300e881c0d02d90030078000e0701215041a901401c0071000215034103da50001d030085204101241c01604d56034001c00d904505001c1f44c1d00400e4010440f500c01011109910110740182c41400c8107084a08040b9004442d0180d20030807040004500041803c0e0b5245d01030001c2955039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 183770593 1250 183769343 183769357
    0xc060a021005150d061d01060f03060b0405010b0307050a18230d0507060f1e0509041a0102100221130b010b090306010b0c010212040605010f090908090405071e0203 72
    0x1d50b0800300003992100302000c00c01012100602060701a00650313540340050007118003070380c40041c0f1140320086098024040c00009207281040b2202c82d0742941000070a40d00c80c0c11049020b54100001040000340d00d50450342c2c05501c038a8a1911812691070456001511090480c417601d4400c1002c141c803041e088003414902c151000b41860481c07800180808403965050180080c1c00c00b0f0000c20245005444881c3c0348178862800c220783c00043c90f40480354076420340c0d00380c0026502160101540c2410712034000048040580140ca082144000039500d000303016507081c0107600400c2e000c0805011958030002141d20b80d000802501d01542c04144120f0010401e440507440100002112070600301101c1710a02c01401a000717a0f802c1c010104442e500950100b50550743c20081341e899100307404030690141c0c1c482d210204103549400c1d4040c3c41404560007883c0d05c14680004e000000303c00e41d08952074450152000704155841030780540d83c181c48020080700d81c01d145000040442e0b0302000400320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 183771843 1250 183770593 183770623
    0x301140f0a0c1803120504030b07031d0a0c05150f07060507020606060c06040b18061005100f1b11060706050919030203221509080c03010903050f070201020c060a02 72
    0x20031140c680341220280c400c3d58a0903501d2000242c103001094070076502c80340500044c00c08a1902d99a5983d0101c0d120080302c200000035a5907175889000f10100074000008800d2400034a0010900c0d100d5801c0e07915503105481c81000212072070007880c2d81c03110540380005151021175494508a051003005000100c4000005000c1c80d40066024503085050f2400d0308103800081056984950760361101041c06442c000751840f01520031400c0210400045100d9840e501c801e0311210302d8071080c0328140c1d4100b9004001e00180c10382e0151030503400400800c8904111002050f08c4c4058101000007485a0300500d4100000081403404e000d2310f5005103010311016000ca801c210005941c681842d18220340082c0160010010070181d11a00700109c003d028900009810b50382d682c1502514600c00c00c81003102090840e001007184030000d00c0108100403003540244240b15203960000c04a101e1020031100310030f408a00c10003964400c00c0030309032100015001558554012501960f01e807910352035000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 183773093 1250 183771843 183771851
    0x70308040203161a03040503070f24050c0901030b040e0d05041706060d0b090f060106020a020102070e09070302060a030902040c0309230303060103020a0c020607030507050607090b0f090301140f0a 86
    0x20f2852103411054003104c41ea18003000c01c05004203041005548050015201ca03c070500c03910001c250302d500328100031441240c41589548144010990b011581d40007107400c41d15102c2041302c07004492084490304802460001400c420400006000700701c10102c1118a112301007021525640100003002030301c041d0528420054051a410b0350303503403c02c4400e80e07080050a0410b60000e850020119003024040040c0e5646440b6014842d00e481001d030b22040041c0d0040c4012410b65030144000d401401007840320780c03060b280009645030380724418480207001e50300008010110030700c0b9a005424442e8020424010700e079110400401030003003954103840c042580480704c600366894480e20542c4142850295066a1301e0f03400640094001e0304810040c405000400001a900c2600415149100b80c0f035068551015040c040c1ca400030041c00c05061144c691414010368010005480110b4201a81c0130303903400401c40400c0c0034008000c9100001a078802c1030016503002c1c0000d5038414010618200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 183774343 1250 183773093 183773113
    0x42312151810020d0209120304060207062105070f183803010e041a1023030730051009031b1103010c0c030509040207080913090203060c070321060902070308040203 72
    0x348c59110754803c00001d640078182c1004060300078140805c0c444141c1240c20f20295254080c041540c03012075180b0001035801810918403a003041c0342c0c0e8030140c103074180e030036410303042c00e55a03081040f01d40c40d094600381035034008144c214144205129078650025055440356580d00b080b032126130040d14212a9020915440c82945810243c04c034807407143c2c06480703072850349030200c0004e088180e01020150101c1800d000c58454400304103003401011a4000819104030007800030950b04c0850b10010710006000042c0b001080b0700080d00c40500114000010345001c00f464150749000c42d506060a00f41084400507003800240100d02a11030b900741c009001d0201803e40450703245141d5000140814000d100400c040e0807e503001e1700110b4460340460b4a040c120100081c83c0e0703c4000b540b0800c96071219807150440c10244901600400400801c0d81400020b42c1c0281015600280c1030500d01550360309400c04030f603290003100c010315000c03504543d0707010541001001400111800e0b4003034481d80d9150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 183775593 1250 183774343 183774379
    0x90a0212070e060405150909010e0a051e030a0c12090302040507080a0f0606092304020f03040c050d020904020609240403171e0c03042312151810020d0209 68
    0x20344c445c0f010074441d04c0d400d442c61b0041110210002e40000c074559a19064131a03801001c1028064040c080c00c010214481081280d08020141c81c941c20806d801c140000049140c03c03c2c501c0e04010f500031140700040c9002481110b80c7c40326940040e6005007003000f400b002030303002481c0c0707400340b0811503050040000518031217080d20305903c00d40c03000901c580700030000760b50a400745d008900e664816000e0300605910000d801c0e41c20201c04030001d054000305200c00c201d001c030138280080c40140e565a903242103030b80000701c40b46401800a4002c0c007001500b0341540d903490908032880405411400103a80c0c082040e0750040e00302c0e001c1180d219400c440700f18545c00e680c505072411312410b036004100007000002100410703004007214079107a200c1400701090080c00554055802154005185902c01450b8200506d0801109030740500c2d4010415107a005080f01d41034562042c0c43d450b030b01e200c11180b1040c0c9460031102041c0820914030204420520340095001440c0c0c14808907000c1010014403040c4c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 183776843 1250 183775593 183775601
    0x403032001060503071503150b03071205040f0b0c070c0803180406050307090e1203151f0806061606021803011104081b152b06050303040b03090a0212070e0604 70
    0x48139455400110204025a450030403c111212a0301c1c0218910104a41903800040550000e507107140001c020010010741c00710440e1060400030a0a00c0700d4140f0742c80e030444084040d0000313030001c1c0c0d0b8400081c4101844404542106602402d0041c80f02d0390b42d00c0c0c00d80c5a0f0800c6014107005003c02000f05c4642c60300e8003c02055690081c0500301c0320780342c104030300d009142c2c0440c03c030418001c2038401581c040c540c0d8040d43c030a0745003c410900310504941040760301045003039100b00080880000241080d846050581e01c60700c00d480860350b4a00c0350102c2e1400c60190440100070b42d000040c080740101401011304c0032618250000d02140c070441415040500a0b80110412680840b54209035840c2e10015900000c41c0907014142c100588100592598001a86200002440c40c0140803007003001c54140009109500c08006860800d80040d40724400d61050b841c1d804008001f1800e00f5406201c05590b090340100328001600c22070442a8840350f1b14810400000c2d46440014100d0802c0d0003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 183778093 1250 183776843 183776849
    0xa0b09030c06010b092413061e1409060d0b031209011b02010c0f060504110f0f090901020d09050d030506010219020d051e030c1209150d02070602040303200106 70
    0x2030b001c542e00300032203043c5a800c03007581e041d4418950600302c0b0510b4000754407400c4181c0c6100c000c0c0d548410442d074070401c51405a20a1007003101002c5c80301d541e09454844075500d0700c0707070345403d96003411403403032088071800f84141c07450b48040c002403030b4019a05c0c60307403048075200c1043d01590b000c0c1911040c0310800c1c1c000e0703400c00f501040758a0380b03030803a400c4c951b49610301441c8141004c44100b055501d0301c045080712104100e42c8580c0e208144001d200c0503081c0740300075030070407a441110b0307a600c18045044803000f102c00c140100144804980700820a405a480c10341100381d0030086007810f810140e9a6950000e030f0700d00803034904070211700694404102c81d40001070310011862071a045a09002d484041c01a080c2e03103600400c41c0030716452180e44c0c6003400041c030000045840d0445095254200325800c500e00c80036001c10028541640c88241b000d010310807083c4c0420780c4486881842001a1080f002c0c02000944000360110401d1f8000391810313140e15100d92100c50100c03000c00c8041c200d5601380 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 183779343 1250 183778093 183778117
    0x503060103030e0d0c1a0c0f010c050f070c05130209010f0302030105060711030a12050301080f0307051b030a06150f05041401150e0d0f03020c06031015110a050a0b0903 74
    0x1e4a20284c02c00c00c032068400780c4504681901036903180e0790410b00b000010b00c1107281c4000014200d03050b46041000043d0f240401c4d00810071040c1004001c0d0840c03007121900411641c01040c4401840580c1541c40c000303000c0546a0b800325800d00c40d032031000390f00c18110070b07001c900940c0707480c05050301c00e1007601e040c2d45d03002e0900c07031504a40f500d911025103040004a54580b103000411000141c1412582450700340c1500c8a5071a541000d194909002c102c0c402942140d000f40410008a04006002801c8145403940491584901000720341004020700c0d001d000c0604201c0005c00d00700002a000d012030f044507603007920341c82d214030400040d1a030090158035035111200051187c1100e454428043c1794580c2481e50561403c0408200803010320300c03050f5200508030341a076050503010f1080859941c401c40b65a4590700e04500300d480c41c0d010502982d03800c1c4001504a81d40c690003004a00300740c0e4022411251071110b070b454140e50310881400b00319110020000030500c3c2c01c0c4000251003000e9005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 183780593 1250 183779343 183779357
    0x3140c0d05070609020d032a050a0b1008060c030f011a0703030b06130909050c10080103033209040609020c070608060f0409030c05011103041109060d1509030306050306010303 77
    0x10042160745070400e1000b515010366515070704006070349182d0001e5255100b40c82c0d180412010103a4039008001c50310001c20460004c00441d400103001050446140c0c1d40003041071000c0d02c0d0205421041e10360754200c030910b407144505000120501d0343c040c2d0700c56401000c210210360f0300c41c81c11604e007140c4404504005402880b07050000380c0203400c004111040a09928104140c8550340c1d10b03010309035802090f030140e41d2400b00060102c00d100303003010030409803840784c2d41f60031b0b14200420b2601d0520014080012505100d42d1082c030105030350902c00e1044110082409029020880319400a011148074a1814800003414400da000741c402486440002d405054640030040d107200000421091f030015000d107a0180c142e07560722820801d00c2c02940c2d2420002800d1604600f120002010700da04120b0610803c00081c84030300545442c00d000b80c6140507551500000b080000e440a1030040184070f4043c6098020103080d400640c2180c040d80c0d050056650341c6080c541c27a54000c0c08007174002501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 183781843 1250 183780593 183780613
    0x14010303030c031103070f090e04020a0e0a0b13141303021b0103020c0d0f09060e09130204020d050405010b1315090510091104030605090f0d03240e010303140c 70
    0x9601034546140b00b0b040200b4400f440c0000558030f0303841101d0607000305103401c0c40c00116a92000c036400c0500b05041c1405a6402c0c26000510a04950311440340040e00e01400104081c0305a0408810103501500c000440e00703841801c03c000d4006944111421180000021455560005a009143d81507000780449101c1035000842055201040c0d5051503000c10252a005008000e81a0404ca01c0e0b036070500c24818404c0000c0000c00390b603020100b0842040c0103060241d035010703003158004500380f028960045d418400b040123409a40703d0704000a00d0141040103202040d001000d100c00212f404003e40d16004188000301c6a0155482103418500c42d01400704c8555940141d8000c000d40ba081c8040e140c1c0c0301401c07029910000300312442c601000c101001081000d020305504079403084040c0c002010246241552007240311815010152581c3c80c0c0301e401065a402002a50311034519901000c2c0c840390ba410444800303100440020b0825241c18405e9030800054400c8500102c02801135240303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 183783093 1250 183781843 183781847
    0xc11270a0e06041514071b171305010801050418110607020a080d1202121302060c1006030b060d020130020a030504031409030c210304080a0605070314010303 69
    0x14005090540d4281e0328454000060020050244101d20946444005440c0750301c40005440b002d24494040120300402d02c14016040507201d0400d00340c2154040c0c1e0400030782000d001428880e40c0702d1408031800a0070081c00d030703003d50306030082d50400e80f1100c1850340e941e0107000840314180541c2c00110103450030040002c500240b5038208a00c0101000d08140340c0340c0009100d100170358400c45155008002c1c98103400c2d046440c88690000c16401141444080388180c090150000c1100c00091006030390701d41190707250410b07078010040d600202c916146112807450010141c6010959201d242100040c401c1d1500142040b412581a500c4c0c1e26950a42c4120b100c0c100c4000c5003c4807411010307a003e0046995a202400c0041c0d01590049940d0034907040180031050f4404100070f04800c100613045035a100080e203189416000d5900500000609248170800c11b054800b1801da8000041d000504840c0010609c00f82401282c08000c0c9450b002c1040e01150000c10f4207000e0384613183c0042010034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 183784343 1250 183783093 183783169
    0x70204090507170703050c090f0f19020a1d0d2105070803101503051605090f0901030b0105090c0403030206060609030109060509031b03090f0d0c08060103030c11 71
    0xc1c07080003200c01140d11030007540601c151083e004026a84910303001c1041c0f0004200003a82d00b03109603101c90981c2040703094000c2e090b0000300f01080b403c80401c0420004c52030242460703e030403081e480454031120301c2d8400070021900d4881821040980b41c4044040e4509a0b000c10306299000007150180600300c001030b402c4d121842d040c5014404248003100124500740025071003860144000311100d400c01076401e41c0b0444088402041626040c10481c6680011184601400c40b0781011915001c03548001549400141021a0408141c50001040003442c003041d03410381e141101d0b4000c0503500c40907406410301991001800503807210020410604040004001d4a54094004100d00c0b040b03498407800c1d940b007610900c00c2d540c00000c401030341c1214031001036a03d60b840805035203032010f5540003d003000300c4898420b100340010300000080200d24135050004124030b1094a0581d0313982d0801800302d03545142d0695009508405942440c5440f0004401c488084000d0801b15600500640d40380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 183785593 1250 183784343 183784361
    0x3060b040503030702040b06040911090907023c0a12080108031606050a0f02070c0e0a0603170309070e09010c0f0f021b0310090506180a080703050304110a08010207030215010b070204 80
    0xc2301e010040442c0741403040c001c95501350303040709a0300d5a400481d014819130700742c001c1c580021034112812010040840290504014080c855a80381d41d408c5401034191032074691600c50710394030901d403c0c2820080405100b01c0a081a40c55880c007603030380d4400d480d449110b1600c0303d09d84c12100501c0303040002c101d54010354009404140020300c01c9400c0350341c00c0c01c07a480030405807003020000502f088a607403030026903a0311461041080c031000780355903101d490701e0314141e02c4240200b1012002442c40c100c2001041c000303100105c8504600d042403840319000340781c2c49240d1800500760314505d010310b178000c00304c5a007054030750360040401749105503c00b114540003100650303041c000c0c4414070340090000d0245000e110700400240849091030050701c005072071203d5000d40181c0024128001190403042910106605418015500d50756490078001114107505210ba02802c46800490810415805041c1143c030030780840341040b1010100340c042c1c1c0c40900ca41c5540240401c69100142800c1c0c03c00c2c801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 183786843 1250 183785593 183785599
    0xf17070308030a1508160506040f0308160812071223130b150108011a0f0a020703020901180e06100b090102030f03070513060c020913031b080a03060b040503030702040b 74
    0x404900c1038001300003c419880401c999100802582009803028070f08401031a080300c4003890701740f41200b07034224102c1c81d100140c5174440c0424200c0700d40182600848640d42d0280c5000e589100c0303e47c0c11440c4c100143c41240005244c2e0f60010507400d050f02c01d00c0030381c5804484001c48615200c540b2004d00000901e40e44428840c80c8900c2c00040d1101925405104289040503111a10100050055805030b00a40340c00359071004540003c60305030101d0f1920418604150f5581e199410168506100c0d0790000f5005000c1c030340002081251100a1560002c01a400340140042c0c80642c0d03030b031400c080da0100da20742a0394404000e01144440100844141801681e0512250042880c1160411110b850100740000b444c02c8410400e000114081d14407401c044010f002c4c142c021601d283d500806200120031070780c06003404d240c0a511408804d0002e84010321801e50700b8a080761403508040c0c03c1030040703801d010001c60881101000c1c0d0b03090700d5002e0011800c05c4020707000c020180a1160840d50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 183788093 1250 183786843 183786851
    0x61c0f0c0f0602010b010512010b031e2703070302071e031b05040e030414042307020f0f0c0906130e030403030201090c0906140d03090815010f17070308030a 69
    0x1142a000103004241c24075140c000030b441c118029003544d0400c0780c580e040060811120250744c025036500d50650380c418880540b01c0da151020f42c280d0710b00c01d1000e42080702e901010400c00c080c0b444855540241c0c00410040121810f18001d69240100c96005016800c034a0b0240940d04c000e81c04121400b42a0285491355a0b59031100c0d44041d060480d62407100100f480c1c00d000c83d0800340a034000c405103c00055103031901d014a4500b0300442c3d03400281c404c03500ca1000ca00048111017202d4241042a0902c0d41103081c44403001e940c40c842c0034462080b81c010180141c042d16404103142d804408082d000d442c10307544075010440381054903440c5c4401d030756950803070b060b1500d410800f41005e10b10a40000403010a10b080203940c0300e103261300007880070b81044d00c1400781924641c01c040410f42c05845040501c603042c54180c814984d6908601d00e944210381c81240c2c10b01c004a5200d04844c90000c4504400b9169010b24040c2619414641203640c040601000010700c150000c581c040107800d000a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 183789343 1250 183788093 183788123
    0x2003180609040f0506030c0d0c1502010603060501080c0a090c02031206181603050901050c0901120f051e0604020f0a050705160e01140d02030706030902030c120607080a05061c 77
    0x10b01118448500d429819690300208900760604011505003018102d40c400803400540e51012900000f50140360f0501d50f1441c59030b040315000b500140095a0310083c144080c0da110b00819035038500591400c1d21500d0f40c0c800c006a905803d03c521265031400b5400b0b186031000e68038141462440141a240d00803036004410441c8042c0b540700c0d28000c0c0c15140c404004515031071401401c1d01c60151140d07006914203014003100f0104401110038420080c01e100c00c0c40c0c01071104040040c101581390030310301824003041122002108000160403c980e10300b010740c503140c0c41d0030300c0b04901510100c00910041001504070a60040002e08448c0d84241d0031a00d03265850803c2c18266140b5a00c41c000440903a001404490300c800400c0c0b4034081d00352a64030000259400095499021303119110905584005500941d1001e014082450001071319003001120b0340c102c0b0076a241401c984d00800141d0800c0854581440343c001c03140610701c000e000340c040c80400c0d03002d441000103484040320300e084000b110b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 183790593 1250 183789343 183789349
    0x3070506090d08120906090c30060a020901020d030b0d0807080f0c011e3b03070809030706021f0506010e03061501090f2303120f0a2003180609 63
    0x28145013100000380b2116041c002002c41c0f0f40301000e403070303030700c16400051103803055032507486030034440440d404900003800b491260171030003001001c182590540244810440e255015030002c140c120002e07800c50704500c4440104400702e942d07031408140d10a0005a959020a01000c083d24455004d40c40440ca0030344002c1f610044e2b540040405081030b5101e4000000c1c2c804004000c20810003041e105000c18140d440300c5101c40c5a001181102e00c6c81d14003500f0421840380000001e044a90400700c0f07a94107001e0500344080d400c00c49103244244510f0b100460558408580901e0f0018150103000240c81c90252000c00b4060007400181002014164454a56402c001f100d028134020030621502c4001c4100041845050743c010440403810201c1c100001110b05005111000848004810030007040c0e00081c1400125050140e0052000c01c4440019140754001c080103411611a181c041000807080305420700340f0540c040c031030740040c00300500e50f114a4000001084004001529114102c000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 183791843 1250 183790593 183790597
    0x90607030c02040b0f012102040f030311060c0f03040f03120f050f0f0601050f0c07120302060106030c02070b0d200c01090c0909050309150f07150f090203070506090d08 74
    0x35000200c220031090250300780b92207031041840007618016130300d02e000340020b0708044c7e420820018526001e5100095181c203941941c014107000103e10600e25a20b081c01400d001603400c40401c2c85c041c12003c180c0b24036008003110050101d80d11040c1c113698554071501c1610510480680a0054110785600081c001d4070411690300e9100742c000880e810003220f4070096000060098480082c2070041c1f08450f0303040019a1300e00d007540e11090344c1c4c0d4001c404e0000e041507002d40c0000f95074602d150480307080540105296058500b5990100800025402d0882e55441c02d8400c00180c030400300116442200e69800a0980c1e004020441d198070320619204119644840700009040c0d42d14011742081000c14a6140000c0c0010401070040e03c036103480c3c95449209503803400e44622442c085a5080b04e140ba42a85d451070300508800ba2603010318101011420980c440d0410f07002d240c05405407461403c0d1043c0701c10960043e00500d05c2d6400c10060090960010301c0040c0d000d20f2030300640700041c0300940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 183793093 1250 183791843 183791857
    0x1012020301090c17060a05190801050702032104020904030807030e07030303020a0f080105090a0903020a210e030609060106050307180906050f01210b010e13061703210a020906 77
    0x140040e076103505040c0213103041d00c20000f0100c0030701014144142550b44000705815980c0c11107048040380d9044809494101c0107900100140d42032004014107585c001c0094000422105c4058100c0d8441c00341000c0b40c448201d400a50100c1c0e52004200401d02c80c0c09a25440102c0e400d0018003118580c51844c50040150b00807400a0380005a90f950103900039015640c89841d0300f40f00e807155040c0000200d0032180149002d007126030301c008c003505045c404c2141d00701d090b40003420b80038140981c3c0080056107155000340310124004502218240c1070000d580380c4501091000b408859086c0302c070444a507440a00b90b0007c200300c184501d8468881e802421000700309460002441c00c0c508414000404c80064150b414860b04042d61455583d4052000c10020b060304400034850310640010b84035030048a2800d07401000361380e1402655034040d4021001d4a0041c089074a4998600b00b010303540c2d104e1788103154000305108484074440c1c0c84070005d09401040103100941045401c2e008034205401c014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 183794343 1250 183793093 183793109
    0x30b210706030b1302070c030f0c05031204030827060c031b030304210909050406090309091a0103051806100e010f0e0609070903060f0b120316021012020301 69
    0x24111605200800805006011a09051040075510400500c81c8450071243c5254660002010420424900c002502455014071514401c00715402e0220452207d8044d40b40640300b24408141c50400090a40d41144c1d400b40e103141c50304008015905000031001160a041106602d0900c0241c0d1a040507129031280e5100441c0c4601d1003014001004200a5504100e50000c01c00d0001103042c280169066034000410a201c0307103c20842110300881c2d951210390300307602d03103001d0000304a21a007011110500959450140641b6480c030a4200d520703c114031440408007402854031540250803069209c141840794a24440341006194204503041b540302c080c0340d100110a00200f40b2030740056003d00070003c1c044072001d040c1641c421183d9400342c003a0348501800c1e40080c022603c10304030346010390362001041c8908001c1700800c502510440402c0383c490040c12005542202000080d180c0003004042050501c80c019001d00c0143c241040001042000709429804501502d00045001300450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 183795593 1250 183794343 183794389
    0xb040540090302061501080f090f0d03020403060e060c04090b0607050a03030e1501060507060b1c030302090f090c0307030e190308060901090e07050909010f0603060507080f2401030b 80
    0x1a00d00241454401480f40c5c020b02201103840c40c269031f111742000e51042e07504010703020503100ca551075840c1079810307440c0940130704c01c3c0b187d04c10205e54150068011a407250400703010501c6603a040b2a107880b0210b80000654005000401c801d40303203a04141015000a82514034200403901e42d80e040030540c100580200b6280c2255094125007000790f0001d138409800d00c0b80f110350401c0d800500502c21018094641f54449041200590300e0900142c0804090140001000203a20700a00650480c0c1107451140e030741501d1201e05070038450859440754500500c558507580d40c80c0e0313041e00140301d00b0503000c00314880c00000a50680d02c1c5449081550300a840c0d01d00c03d80303001c0082140000058204107403007410a08007540c00c0382c00007004019504115010780d034a0752001c16507401090051450002c042c1044400803c0c8072441e13101d503003d40b400303a45401569407407000c9452102816290032042d00c1c4103d102040315085248040d180301c00524003c19120804c000260002282c0d0b202080d0940396 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 183796843 1250 183795593 183795611
    0x60411070c030f0b060907020c0d2409030806010c08090d0507180504120e032119050903010f0b22060510031a01030510120510020f03010f0b040540 65
    0xc07071202940701170125011030041c609410000d48510361010814000d0460302040d03030410420038407100310002d200803148104001440007001414008100f5400b0074030740804110341e54481c0040300c6501e40c0058050346404500020b00428030201b1030b01741c409000f40c55020076540c40803608a1040210f0f2440403407a820281001103260b07803000540014401580450300b2140c0300400c01403c10400c1315a030362002d00034007d945030380d813003007203c0c0d00512407100c40b031800c41c3c541200150050541c190001c1000202c00c030701d0001121040e00b005544060422031b51150b19a142d803900f0401e40740c007580440c50a076138038040740c41d110303000710043c010a45a4580800303159040020000b6001c09190501c4603050840c18601c207000b080c05441c0720002da0507002014024100b286032450040b81c04119505d450918021116030000e005500312150801d800092440f111419541502d0009121802d0f010502c0e07240e100062800c855001c11a40310508a00880d00c8000f02e0302011245c48004151014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 183798093 1250 183796843 183796853
    0xc0312090a03021c0e060702012003071e02062a160504140c1c0b06030a0504020a1502030f07021c03030c030b06120f040c03060510031415060411070c030f 68
    0x240310b40d904c00213210f00401194254050340240b403040040c1c039403a1b40e41903a4001222464500e001407001e40480e0000c0c03112080c4008010600140690442602902060425078400d01074070030284d8020720900c0304817141403030b506a0003503460b64000c0b06011044e106101608141003400c240c00d203800d205200300000d0030180150800c101d085902420711f403608000300023440c01000c18401e200701030718082c03005105039035201c2c03070022400400702612450303c04d8503071000c1c0c101200c00b28061414000b000507980110400802050702d160061030519403040c08031207242c0c000010503a4090491800b0700484101c11a6074480580030b5030340400c58000b6940301900b5a82030f9440240a10f10400007941600d14094440b500f00201944a100302d803228189401807146a0300050000d61911081c01040300004070346104032440b41d40d050041e501641c10403900e51040015480e4201000e50009915161507402041d94440001e01941000030300d031036210f41205580c0003241c0c9181d2194115050007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 183799343 1250 183798093 183798103
    0x3090a06053d050f1e010302040b040806060a08030a09050103090317071d15070b07090b0c03040501020d030504030c23010c020f16080a1401061d040b010504200c0312090a0302 77
    0x4003071328a880181d80080210b240784070016000710310307180468180c40f03260380310341c04446c000c0c40c69101c1591070700e494089a68450700161103052154000b07800c0002c10013408800d8900400c1e00340c582c5140315242800540c0035161a83c01203080080c54149582c1c100710341280d0178010300090317441c00400c1c008070f0180c40840c2401c00c00c1c0c500c40c1c0e44d0302100203b43d45a450403540005d51064100a40e5204c091090322114410b0304401312441c1d011413200100b8400102500840e00241d080740d84021101000349e080345c0007910041c001403001e000d007601141504002e00800074100d1000e00c1400c000300321842c01c40f00f10201c0140140c02201030f0702d0814030200030f03e11065074844080c4090354542241559110b01c139560080c0340d40c10240d8106e0146800f0740c0000c0007000d800a2003020784e00c0c581007524080500b110304843c94800340c8000724107801c051140c0c80c8000300006001d0607242500721800e22607080b480881400344401c1100098818140002d5802045400c0c02091088803525002e8200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 183800593 1250 183799343 183799349
    0x11070204060b0f070305180d0b0f0c0909010b091908150609150d050a080a080109140f06010509060d06060507020a0b0c0a0311010b0315060f040203090a06053d 70
    0xb01c018011110703880115001c607000c00c0e80c541031503540d440c403c0d40040c01103018078101c0c07544482c0302001c6d0343c20300002c0c6c0385151180c10084402903650740e46108040307a83c0149500310750041c5001f40184800c0301048014080050000d003c031030035241c0c0006a032a601c03a2a0400040b6800c0f100b03e00c0301561b415050f04e81c0005048412501d1403030109200e180d07400700500e4132307486910000d10343c070306001e4148801080c0d10b4000f541c0075600d10013283c003c0c1040c80288224030030641380030025111960b01070383c014014088a01c000e201c503110a401143c65801400030350b94071050800080034039884600c5054010810b40e16029121801c0e4010010141201d80c86a4040c802c10070100701d40e800003103404008943e1504011f048031114100d03880c01070600d0252039426205084844404420301201144295000c030398200f00c2c0040030090006901040d9855021603000090040024015400140d808012000c4104181c050703507c0d4180c1c1080c10504182194910088140d41091002c1c90304000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 183801843 1250 183800593 183800609
    0x20a0e0102030711040b0d060207030806010801090c0c060c0504090905010506090601091a0a03061d0a0c02070308030402120f030313030f0c03230c1614010306061707020a061107020406 81
    0x1041c4071602e9207180e104d9610036180c401d0b56144000b004c0c5c1d030740708000d10780d0b19078000307000315180c0e40140703000307040e155043e01c41e5030208012200000d0310442d0750080143c0b4110a84d203060b0442c031b01c3d0347c8180245c441400307070703005200e0103010104e1160352911404034914010304c000300d030ba8100003040c0442044040c10560412180e03103010300100c1c0c0840d6007007448410921409583e071048450440c010001a00421685080390010301052103848004e0f90181c1600c800801104001420030390795050588070040003441c040c0002800f40c607050081000034a4000c0a542e0800310910040d400e5520448040085070524000181455406440c0c5940752419040c41c2b00c0d0fa2001c2d44010f0014400c3d5000c03d19807240c513100d801c4210882d0400c3c0e640010041017150000c61034469221080f5265001e118003100c0b02c15030003441c1d0340c42401080304651250304c0b2401c4900485d5100c584e44030004000005500c2021000c40006000c0d110b06050803e100b03001d0b0362034240070b204010036111135500c142c1d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 183803093 1250 183801843 183801847
    0xb0103050906070e03010f0f0e0d0810060e0414160315030b011206090c080708060a0501050a030206070305090d03030902190b18010c0b04080c161404020c1609020a0e010203 76
    0x307100100241840c2c104a0b5410183c02030041e00c00040e001d810b4007965803214501342041200321000d540c01a004507021901039440043c41620708490007041141d40c8060840f0801042003411300401210008803005040460803510f0349450b05000c1600795032903090b20304070380f0780400741d5a41b42c803800d95803103215002440d8140c55a1190240181c060013501145401c0030324060803c11140d1120024680c040038262009560301089900e90075a03104d1720066000d00c01c00074001c260240304850580d500200b80d8446641141c0074440305410080d030840900070104a2000655241c0744481d03411232190780c0c04034100c0d02d10320500c01e11180c40c884170054004819018800801010145c40c2004070307000361815501c4442c0012a150b03800c011006d00b8a52010003071005200e4581d00500420f510740d0100d0b85114001d00d809091000c0e1440380001d02c0e00d1104400c03840c0d01e41031b0001c01e500701160040342d0320807a010010300081c4030290b200c040d0701507000400140c0d440d000580c41107c0d4070300340041c41c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 183804343 1250 183803093 183803101
    0xd1b0807181d0f03031e1311180a09021201090c05010e0d1a0405010525140d0c030c08100b03150303040806071206051c11030304080a0f060b010305 65
    0x12600580100e80c801ca00354941d0156a02c54455901e10144411508111040c4240e12403e80d0b403030390310503120103100080b100c5140c64400e20203580940554100801940001459102d008002c580c1381e850551040e01040304050b003040110b00d2500039401402d000510801d103104000b11208942c808502c02d0741800009000700f04e00c211440d0880d6001c0c200131940d42290400900c440c015034000500a906c10300d014410140c1e144c07440c51103203210700d00070081e82c1ca5556008401071001030f00c224030b01c1014070070740c4070042c420703050385446c80036238890f04e030030030401600e04815030302604142000030b991a161000c07182d502007400c1c0d40200c04078501d4001141491360b1115144802090466001400c210403105038408000302c400408180317055500c3c0f820250340040c012801c814401100904003000420366280c65090401c80d400c0c041981050f1140c030f0707501e07095545034503e011030f4180401d200c001040c2c032083c0302e1103150521500b44441205400d14000d81100c031100c0d00941003600c0c0500304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 183805593 1250 183804343 183804359
    0x11205010b0a081504090f140115090b0301021b0a021306050d060905190327050904020d0f0c0602160803030c0901080a09020409121b051c0c020d1b0807 67
    0x71141c9200503c3d0030185a640c00c110031004143c034246070380d080340c508150340d0300b40103e1200c4201400e100321b5107090704580b240c50b62800e81e0301c4400101c1e82882d4640d0104068a070a5000d401c0303210020b8000b60520f0684240c0441c0e0b404601c11010f110740000c004081146045c0d940c0112040c4550b07001c120301410203011800e030848214000342226035441c07000051210801880c0b41c0101d400014035810a084d1600400318900000785141c91802140c280d62040c046182440c2a90710140c8000d107266aaa020086c0100564005035032b41d408120000010038403618810001d800d168004000440d404025103401d800340d42e016440d0340d00b050003030164446180c6c0450700e161009181500046d181c0300204e500915990000a500c81d182c210740b841080014402c2c41c8a0450365290101600100c20b924001030ba00c8500046c15500044040505019840d10903041400e003442c043c0c074045929070101d001082c801c00140d80130038020f44000c01122000e140080600481005049524606803007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 183806843 1250 183805593 183805597
    0x120c020706050a0215010f0f0b03040803150f0d0308060a12170c1606091505120c0f0706020309030c0106080a0309060f110312090d05070b0a18120e011205010b 70
    0x36203007085000100b0483c900d10030040b003400b03100541c1c13042d20a942c0d980f813080902d003014419506110304a01002642940c5001a41d12880c1c121404502d95510040301c0c00da01c0d55440041607006441a00c001c0b115104c40d04d4424004d03219450384001418004104440f841d49544198000c56020420f44c001a4145a000e41e4880f510016261103190312010075003414400c1c09003142800c2900030000d007441d8400c000500300c0b10922416020b5030082c0504403802d100320324103180c3c1918441b01050440036084010f00030f00c181400204d062690a940f03c6040c0d901c240c80d00c000e140d0001c1203200060700c0c2071040d000100000c0c402001a00c0e460b6501524903c450301c5400180401224400601801001c00007104c003880c00c152569801d00404800c0401e400f520244624455080196403841c000c0d021513500507001541400c0703594031289042d024140101c0fa010483c015041007800040f91540401c940044c942c0f5075514079040f0100040c01c400403444010669401d10307004109040e05941 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 183808093 1250 183806843 183806849
    0x90201020a0215160b06011428050f041d07030216080309120c0a1103010507120e1e030403060b0904030c02042003240a081f0906090c0303120c0207 65
    0x412030986140640c050480f4002c03055144c4104c041c200207402000515003800b48540720980303841c1c08001e0369a114010302e00902000c40070348110b104200c02c82e280c0b4251140c1c41000b4074608549000f001c60210780c019001a0300641052614030707081c0c201d0b0b071290b4134440d60095040c6011800c080c0784280303522010620f424041d00102c0c0c000b01040d0002c00a1040344001c00c24000c0c142c1c1e03902d40400e03589036201103e501c291000310080b4644041c9103018000d507409a58242d40301d5181c1c030040b0040c41e0041c000100202410710407400d0814100440711825600c00d68070f100074549603440c504003401179400d0180c0841c401d1071010200030000c2c2d0007444408159405940000701521a8170704050644080382c0e400d98107840100070480c402a000000826809100507480700d084042c41c1402981c08544c081c04406420101c080d152b0711131a580000b8064000e100e0205000c00355440d02021140e80c2c3d9400e40784000c0a035030030f00c28503802000c2842540c0d40604100401140c45030003d41b2000240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 183809343 1250 183808093 183808099
    0x10c0219080405030d050703020f0c090118021b070e01060e0109031401090609050102041517010303030c1404080303060414100302131427070e010509040f14060a0f090201020a02 78
    0x48003900500800d001900c01500001c0e040ba03100e41c59008000d4500c1d044040100c5c014440d8040c2d502d1b250802140300e00c01c00c08040e01081d002c0e424040000d070b51f00544a40d02c0c0780d003982801a03041079112017810301f5031480b0030f0001d025540e06048454030071600503000070027800340303070009440c159a02a04001c01c4980061460b000d40e4454126140034110500003d8281030412035240280a0103500500c219181b042c1010b9045400701e00c1581c3c54203409014842c00c10100c07004101082c0240c11050310350516241c001c1200195481c06086600300703800c2a19150310200421a0b1824103218101000166201c0c41d41540b41c412189d05040b4641d0000074090840f109045947d503000d030b0090711040e040305412803160b09d03100c0361403072032a00d401d00d228881c07100c1030342c01900240c004281d40c8180c855a89510a06a0800052144820000e0301c2200c0f004044c12482c00400e0704080c20b01c01c03003140b10000d056142001607000e070542e080b251001007114549008900180c4c2c0010300e90403041d9040d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 183810593 1250 183809343 183809383
    0x402040903030209030a03030e0106092003060414070f021504210509060403081309020307020d0c05100e03090907020d1205040f0602030c0d0509152a040b090a0503010c02 75
    0x50324044003e4002e9540c4680c0510071102400205509034000201e03404d070400c02009080d9546003441e06480e00d00402402a0903000c0d2a403448010f020700a6501c0319001d08045002c500810f4503038103142d000c6602e040014a044d00b030010f2140c0c14418020f082103940d000f5043c2d8141a02c860034101e00f00b088110100e2a0312001c00c00140c012030590f180c60030f0040c190f5441d25030b603040c8500305510540c522a007030402e000c00800c40028520a6034040c0d48103900502c0816840e03201522074041074038040c3d61134031595040340380c006590301500709070004200155450351800400d000c800140500000c0a54100d9034060351120780c031010f804080305200d000441d2607103d60803c0c0300146c04c18071019040740d000004103c803c0c02c121004040701e0409101c100029a03641d1101501d5007805038800d0b0002c0486004680c055110541e80d640300c43c0000764854090703803100c03410b010651250303100001e5180081801c0d0010714180820300001c22044d0000e200d40041f41400948503001c0c0e0341d01c2800e203500c13 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 183811843 1250 183810593 183810611
    0x906010e060d060f050c090a0909033f0b24190302091512010b092d0d0606050a050301050f060d0c080316060f02070c03060b0301090501110403030f080f040204 70
    0x20a4100140600c2d0713070a402c025a01b0070404c440d0302c51f4810014a4010880f0250006940406110b900c1d61250950340e241e2866071540003050070203680d02d400d820442600c241074030104025005080d031104500c00700280c0c2c11300300420b00c82100004443d000241c028542d050740c8411000080300c3c40c110844200d10300a09001c18154024007850750369a42011456a00e40c03c01c008140007402c2181600200211981c0d0f520030f0030301d00340700d05581c035074004049900d184030140301e031840c1014110011100b0f051804a0703d0200e07074044d00411042d14100d072652030801407414002401405090160024884c502d0710710000d4860f404054002405150034070b03011010312210104550242407080d003500d54410807140d55500c01c603000c0e01e05031822840d0401c40541e00400e4800c56020fa030b8008401c0100300e01e161280e0004080b22070845425549445032900021030a1046080040100c1d0307089446600b181001481030002c01c003079105000034141480784841441112991050f4110783c08144101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 183812949 1106 183811843 183811853
    0x4110f0d1b140603090712021c05070302091602030405150f1801090f0e0426040609080c01030917030703060306050711100b060a050f04030c18050906010e060d 70
    0x4c03011001f00b0006001034601413105000801c0c0241c0042c0081d6120003603011114111000d41001400340708600c0c18546036030300400c00118501041400043c085e58a1140e030181c0e500c41d14400706001640310b031013411030f01c0c181d2100e00d0aa40b220b07075009984140030018414640480c0895201107414011070b400c95080324018808510175880310f4403181d10071070400d4124020605080014003048034440010001088103903580030308146020746590401404032665410141082504004140b2150948480e843c10f0301c0b9881d62a26170f0b22068005290340e900c0200050308040420003419040b04485c80d0807810036003558505009001c01c8001c880102113002d03400407041c0075207084540309101178004024400c0c2c00e60315041e00e98682503100c01c10799101c80c5840300c24021001c8281c495005680d0002c8880340105510f504000e08081d9524000305224004c0a5003184141070113 = true := by decide +kernel

theorem cover : BRFrame.Cov 183633093 183812949 := by
  have h0 := BRFrame.cov_init 183633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 183633093 ≤ n) (h2 : n < 183812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
