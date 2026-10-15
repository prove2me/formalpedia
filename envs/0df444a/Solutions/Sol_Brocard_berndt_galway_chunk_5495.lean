-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5495
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:02:51.863915+00:00
-- url     : https://prove2.me/submissions/a3f202e5-3e0e-49c3-b300-74678b7cc61f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 988129496 ≤ n < 988309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 988130746 1250 988129496 988129529
    0x40902010c060608030d150608010b031015050301140102062203020708060a1d010219031a0406030b070905030a0b0105210106031a0708060f060309150f160903050304 73
    0x1600c40100001d000b4084030700d80701c000030781c1c03e0002c0010310f41006000c0c0100002205031603201d02c140824085c2e14005880758006100f41000a00150313045060018007118082d0788020541c1c0501c07d560809000901c04001040000c040107052002c03210b0900103400d56280491404c2640c00000e0f16a045003a01e203034001e400c0c14024069400070b4000d41d02507903c14a0311440c020040e10740c85c01810403034070709206101d03084401031098420040743c6d250903422601c0d8080342100070702481e003404001c118814400d52505c0e96907119000c011886103001004500d4950340290412140b548424002d800a44484000403e800d2596064580c00c03616620002c1c4031411588031408a69111181c6600c3d01101006000b404c60003100030a0351100c41d0f691b1580e03400012180020180c480b01c2c2c01504020341d0051030300d4030b4405141d2103c08602101e80c1994801e1840200c0c91043d112142101e04000034890f41c0d0300da000740c3c81c00201d803c3c10703d51000380c41d50307039504c1da03074483c500c01c40c0d0003440c00992 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 988131996 1250 988130746 988130749
    0x2130e01050907140915010e18040b071b02030a081b0a0311163c0f140411071412030406020a030b091005010302091c1506060503040f02040902 63
    0x1410425020000800c69480e1014080381d80e0500d40c0642d0b45081c4910f04059075500d05092901e20890071203c4041c0c52980f0b920041d95003c0265456942c80808280c21006900c00b1254061243d4040d2403d103000e0304007150040c110441c02c00c04118051080e84c0c17140050784001400c51101d9620403071642d82d54401c03201e8066103071450f142059041c010514194241a441000b10900c60425401ea40349040d01d00168000940c5900c01d40c1501d20202d1800390006401100504d0841c4000800302648145c0007035510500f200b0780c0018101d004025014000007c0105240740c04000c1690104a100e804030728400541c05807110050503d4040e500104900005101c2070501d00720300c1400da2346238180f074a40303c80690003411702c4200007450400700280c14039004050310301504006030f0380050542460011000380d486003040a400010840e041d0860702c031655161203159004289001511450082d00e034141c440a030711100401c40c0610034000881d100903e440c0700035504440c0000c0c410120b20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 988133246 1250 988131996 988132001
    0x1a1c020c0a05150604061211030f010608031308030408030909040f06050112150c0e0d0809150a090b04030c050907020109050105070e0a0f082104030c09090201080708130213 76
    0x445030103090054903906401c0000004418504140c04503d20610707583d14001d201c00c40740c1500c240341c5003055041c400b4002c501c52088107980e244002d400d6506840e807a039a09400d480f915070140c0705d40e07440021409105c1524011b16000350144002031450140b821201e55540e00a0030069445550740704042401c114134080078846079940700c0800c2c0203070769540c0069007004800110984201c07440f01910340d00403140d03101c0c60203006807030317158541002c005030305000c080c00690000f2108030600b001015407966860720003072000d556403100b142d6154003511008cc030900d11540400c41d0740b00140000c1c00020b4102c6034040076208250760034152640d92030350803405010000303400350055107058140050241d0000c955a1142801e803420040d2540d900403a006180c2c9904c140c010507000300b10640e81c0e2944c030075010400d440d41d2502c0035091984907101d0421405250344244140365941e0104003c558200515948c40401130800400e10b04d0320039204985003066040081c41400031035141c44801c00c290317 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 988134496 1250 988133246 988133257
    0xc09050a0e190b1207030b071409030d2f0d03111204201008010e070c030c020928020403030f0c03050909060a0b0c0703060b0303070c0e071223011a1c02 67
    0x2803040741c0031710307540c0d007400d01c1010b10079075182000681c1051300520150740341c0100d440c1d4410250041a596140c1c0c81d040f2200c20041c0300390000b045a0702c01050741441c0e00b40c00f0614a882800103403000e4251050060100e1304205000d8205c4581404005000c0340308105082d03101e5004442162113040503290400103180c01d003090f9a02140c4000c10004444d480006135050311000c041c10780b19500c6c0c2c20020380d81c41c42034080c0203001070030000f0804014213100b0b41880d04000c00e8441c50b06103030100d008403032051780d104581c100c010342d000c20204241503000b080c2c90100c02060404501c24074454400906c0317440380b04035145c000d000101c0812010307120788440b00024180303451402d407a14910b82c56141c84524500c8183c0300b01d400d04130061118900801140c0485512440350181d81c0d02c0c0000421194000500e06003d020040a590b40d88840314000d240216400042400040118211203840d0400680003d11075219881004440c0810701e4202c58890035080c0600d1040e285694880340a4483d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 988135746 1250 988134496 988134529
    0x4060b04090b120606060906130801020406050a020c011404090507090e0705040603061a03040f050a020402030c190f080109112515050903090d02040902040c09050a0e190b 75
    0x400040082859110b142115411107000210f90300103003070596500c4058800d01c1d4820420040301403107140c09402003c203e5203120700c103542c484d6960105402c82e082548030101042c1300040e0342003c0740c1c0c18898039a440300c0c00d0070921400340d590784418480d401140a0704044980d11030205d9400750195600c04010080d01014039102d107040800102560418415000880c0c113241000c140c1d0029800c50280b100c409101480c00e55455450740c0040d82c103400e006650602030440c0d0f04e03002d62114001540f1400c0c0005040c3d03601c9054181003a010050550300300b04100503034580c9001558001c031502d0440342c00c0f590100d03204048407001c0d8100e00c100e200e5140d100100f2300d50640740c6042d00f110024030500070511404030b1084843c0c101c4c1921412102589150020854100c0b140b81142480460300d0020b8800a000050f82d400b080890b40707503e45c544041400500d00308001e00e400700d04440034240300100c5112a050004c05e0f0a070b00100003003801d801030b4550281c0b8605444060095040340c2c80b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 988136996 1250 988135746 988135769
    0xa020a0f0509120f07050109060314061507080d0207150207110909070b1b06012103121d01050604180b04020d031806051e0a2304170717060103030f05090406 69
    0x340c1121003170340c803c00c510405011030302003100000c0d943e0180c46032a8207441c2c4d103155000030f507485000f04052a0104a004042d440091100f9008110b8160141c045104007a00041e900d149601300701d0805141d0101468096004202920004882d40700145030a10207a07070103007554603090809428242e03c2d4108070b0460b03601103000384100d50412200f010a65096040e00c84a9881d0b0740040d241c3c00400b1800c0c0c9640c0254241980024490144444615000c000009000f5081e81c8941e209011001e16001140e45503024860540381c85d2141880000c20020b032103102ca80190303950035202d580180007071300c0360003141140c0d0149402641801160060312210307420391a15088003800b41d41102a580a2082e01c081310490715040d020115170825485413181c0600e006140680000860310400300b8502032828000000c1c48441e0880e0349000d0f0002c007015001180c200000841c4c1d082c085500203456500500040000c6034100050202040540c64080e40d01c0b0090742c0840c01a1011360b0043c0200384 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 988138246 1250 988136996 988137013
    0x110304050402180418050703080f0417010e15100902030a0207121211030c072310090615211e03211407050c16080105040b0a020a0f050912 61
    0xc03400c0480e0080e8040451301040b00e05c900c2000d8440200d01020010002d43c4290b20510106e000e80e000390040140034844540f0300307500c0702402d0048508454100c2c50707580d140d5420516048050103047c00501072200f9030100c40c035005c1066500003109114030700400380e002020800d0030415404a0360500d400000420030300d59507810003032464003010404c454440ca000c0b0381c0c2c000d001c03a1004503400b43c1070f4503422609204540d11100301803500890501d46c082d1403440d0425258034140f00824014000b580002108142400c00000b654800d140f40c103d070009101d82401850104140300c10581a402c0a440d040032681c544084000017218100300741140e69444a010554010718903401c3e64140c00720071142c0010b2900d410180c50034900440c203803107400000142d10512400c05444103101010884441440760f8106d0316103001c95401824840c0d440b03008102c18001c010040366080401590704510300a5401e50041648426109a10422200090780ca000d030b55101014401b0445540544400c0d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 988139496 1250 988138246 988138267
    0x18070e01260103260c03090603070c05060103052103090d0e13180606140a05040c020a0812060a05061206090c07150f0f060f1502010e030313021e0d03110304050402 72
    0x740183c051320012041d0703a60f0100441c0107060540700305071655801103040c040403004200854200070000800c0140e21040300c03010603c1044668021801840640149141d40c0301061144202c0c401c4e03603140e42420000c1c0000200c0000f070341d0034211a2464014143c00c03508000070800d09a40320b4202d4814100104102118110024182881d101d00020818259100b80c1a084070612b5050282d00c884581e0041140f814540c20841440c546841916500d4407642c1c1c41c41c1c0607800c0000400e01c01c211f00c0082040904201c0500b5003d4841141d20034100a2850015625004010300b481d000b0003140001c0f804000c0002c007914070584d4001c0751003c00b030070420400b8004280e0103d04131202c0c0c1c01c0c440000d080507a01d01c43c08081d20640903505000e2801c0c80141d040050399404401d0456685110441282c5414005140102504402a2002c1c0320034010800c2c3c00310114418280030480c1400e201c1d03141d840d000b030f09402c55418204902d42c0141c18548508600030785d8401d540241c000a681a2030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 988140746 1250 988139496 988139513
    0x603070518040903051905041206060e01050a0e04060f020904020a030e0c120a03052109161509060c060905060a09150216170c0d080618070e01260103 66
    0x1c82210140515031403030103010801034503041c200290104208101100030101c0d805024500c0c524241841d900c1c02c1d958100240308a0b0064005980640c1c3d580c2c8280a922080b007101e5004000488862a6071401d00403001c880d4100984020320f010341d2002082030541498054482901005204540300c1034a80005070140c0111300e8400c1490298140b61f0383c4a14050846002501040c8010011300c14103640a031815440030400c880c10400b1783c18009607140d0600c1c403036449240840c020340402c100424450746030314041c0c6c005403451500341c092680d40503880401c11040351440c0c80e1072014885182400002020402d43c080e156002d590100544210242c009000b418424060020904000d02c50303d02280103100c101c0d409103400701099030100d100010a480c142e144c44058514207001c1c40b00981c5001d040030303031000c04216584100704280c80e0801240b1141000300045203454940814002c001d80c4d0f03030030420b50510181c1d00301c81180d58049140d9044080d000e002d284040c0d6103030b080c005c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 988141996 1250 988140746 988140757
    0x11070506130e0a0c1d01030f15030c1226090301110414060c1009140105040609030e0612010b0d090c12021f05030c1c0c030f0b040e0a14010b06030705 66
    0x680424030003c54140c0c2054420010010380d140e03140350b0302107185884651600c0900e40480d040540300e2000c0300e046e00d03040c0f10350102d55901c0c10710313071440900c4c41c5030032610131704240d02141e824809602e840003c02c0c0080440656400d008004507406502c03400c0b4902c0740c1c0600007281e5015840c080d060b680c0c00400c4001001601e0480c1c0d800d8400006070402c01086210f100106d46c980d400118100c2c40584480d008000400e218101e250310280d00e61f0802402c49100f21030542d800c2c0c0d2551545414190048182400f82906031000ca141c00c50041032403079000c20620565400d184001102103190f0360592140c22203d03030050007800199a40d101800716120461008d0380700e4020010002c83c03c1c5022030305014200d44c03e4a640341113540340b0381da0950710381040c00210584091502030003a80c0b036051080a24200d00c607100000c0343c21b80b41d52420110b038460403415000b1b61030064140f00410300040d1600c025940011000d490041040c0f2250143c0082d2400c5a00520f01009004a59070807001810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 988143246 1250 988141996 988142009
    0x30304030206151207090f2307030606050c1b0301021605070e0717150609130221220206070210200601050913030c08030106031e0506060a1107050613 66
    0x1007220041e074082224a0721031510464055001c10340c201b1404505410900c1c8004258100003410040d0f07003007480070b000c01540c508032010310b2442001000c80c1c140c442d18000c5c1595280c0f80303040401c5460000e980d201c854500310701d8110103002c858146d5a00f501125a501d400e0319100c07102140701c0c0351259903520f0034092210104c069000145e000e41c0318003102d6900c400c0c03d14804600b03864028070800480c0c50741804540105d010440e40c5000e44a003540e143c00800c1d90100160b0750180d1110301243e154051080c0041051424248507200e40202d801040e80d0070b4072109403600c5500d0b407000810030311803c10300a4100d000540300140d600c1d0040107450b07a41815410701c0c140b0b00b0485020a4441d06d0900485910240d4800400c2c41030480242020300d5130320904004000c080c00e40c440c00f034681c100341c0c00680020b4650340c522403200b42502940c51003400401d424045410084005a03090040324070f10130420503680c00c0c0c65011001000340500419000c0c0030140e03241580014415945c01c0b81c041c1c203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 988144496 1250 988143246 988143271
    0x320010806060316080c070204020318010e0703030e01032c0303010501080a0608191412031603021306030e0307080c0d110c3001050a020a080108030307091203090305030304030206 79
    0x92041d05001040324401d0740c200036040081d40108400380c0f05c5180281105903521014000f120058846100550042c92490000c40140410101c110309541c12020212415086448100000b1350001d4080148240909020a80208400841d907503002c0141d2076540340000d500c0400042540400111305a6000f82c4c1c0750794456441c6011402135900707912400c907450b0310920606500301c041010800ea054810003000d280c078101c0c006990f1a00440390b514440e030500010920001000c80405070041c914241020750601e002c090400c1c941c41024030410062680320b185080b4041803e004659200e5480101d19440d02c1d1403082c0c0940e5107001c281031b03c01145520258200090001618101000d0001d10110510361424100d03084c035111032031090091041240c510315152828001c3e54400c102c1558010780b0f0b404000c0b0010002c02040c0d00800d1b040d00100103200c041c0c0d61008848040d1400b550080d162a0a50b00c0c00311140e130140e40c406000c0b03001c084207210425501164540c020000084d45 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 988145746 1250 988144496 988144501
    0x20a060f0e1c0209010e24010318061b2307050c09010b0307090f0506180a050406080a020306100509150d0b04060b0a0504020f07110d080703091701112203200108 71
    0x6c0443c50081e40d20842e408041d140602425540c000c0b644803524040c5070100303048070541c58070180b00c280c82c1000c80701151503501c0c001c2001d0301402903010300e20380c91900210403100c40e44500c0209803646c1102c000c00000150320424000f0070840d0550b03504c0003500b48a00e540c0d43da41c00700c50b41d42003030f58143d0001c1c0003a0b80008400108400c00b5083c1ca070700a20041c5000c10003101c10a00402141446402902a190014040c1d41d03d1040324000c0c85c80801401403062248100b5082c0340c070051081c0c042601411040c0180e40f2090350003a8008541207088c481038449100203103142070700d540c00a00d0b4041c80010071082000d660400303940d003e0180d0340703000c02c03c0c1c803031040106074000d480d0840500001400881c010420200d560b5405140103001c005025070b454603004200c6e80f12441c1600070a9030f19204002900d50b40000500740203007080200a00d074007142c40361086108140846041e0280c00e200c08140d810208600e40065500040c04400c26a0800c0140805001e41c0c013003d000c907010300b00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 988146996 1250 988145746 988145759
    0x30a02030d0f09030e210115090b190e09011b050d0e010c02060703020d0e0604082713021c0e100b0f0d02100504090207030309060c0507020a060f0e1c020901 69
    0x1000c0c019a4544c440100700b81c41002031001c56581c40002d0307550484000b2106c091030800707203c1c0562045440030312440341414846064107a13194072031024000c3c17207131a03d00e4030003254251559050300c2007003541003626104c61007110f0161241c0078a4042101c103143e0401d0f0f40702d805c08010000c0c2c0c10040710600200e2503075503030301e4200d8a5038202c1c3c0700944c102c07000040c0024426030091030000b5441030008be500311a00720301c51900030200c034111040308001614a0941c852010b80e0f03900b580501c2c980801018602c00807452107880d08450060701e030340205420080078414002d203505142d1400c81001040340d505159582c0301c10213400e901415141400403030b502d0401d64801105c0550140c01d6149070b00250b0b0034003545010500e00c800070008244004610504580010840d283c086c1e60089611851400c00500301d51a00d0a20024858100710940058480c00854011500d2500f40031083e400c0f01103080e02e05003401c82071141e00001040b140d0001160381c000b070441c0b0f03500035510b100b0160388445 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 988148246 1250 988146996 988147001
    0x280c11011a010e011b1218080304060e06040909050a1407050330072004050402030a020f030f0d080406150f031407090518010e06070f1d03030a02030d0f 67
    0x1c40d910241600c00002001c5500800041020580600d40181080c2c821003c2c0f140145040001712144030651011146041e40101c00f0f1807000c0b030031150090b04a241a440c241d0b00c0c42a8402c02060103000500c0e0390301580c40c40c050300c0003003440f40700901c00340200f458400d031100e0b80e602c01114420405204c1d01c1010900144d0001698406401841540c845e104004140140ca15158a41030960322202c40f03c03040740b1000d03090051003603e29111014850260f500d500e41b00040b00e60146e447c1c84c5c20400075036030004690001c50f805644c01c1820500e0007010a00382004912580014401d01c2d90404001d030f403000c4480d02ca20b000b10420040d40840418080610300544164440700342c1c00001400480c0d0031f1000402c920241200300c41c0035642d200313000c2003901c0085802100d41d0010072a80c403044a02801a10941e18000c0e0240250380390035000600483d28071482d040c101318040b0300a9551034002c038002e0b8450071000b01169207070020507100950700da020300c1c4200318003400c140c5860840c00ea90f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 988149496 1250 988148246 988148261
    0x30f0c180d140f10060801140c09040605100e1309080301031712100905100b0417100e010b01111507110c180718030803060405280c1101 60
    0x25004240400304902040801c0d00700d03070002e44000305600407840050b04100000b0703610031411000b4040101c024400701c000c8a50b00e0340140c5550f4101149260000040300704280e001540d0420a51a22139101c042001000103402c00ba401420841c41d4443c01508030010b00c1c00448100c4802c4d500b0510b04201200b81c640d507a600510700c000610060000940714241900c1c1d0481e4542440e041840b8103090300701140058400b1503502e80b40c694148000c3c0d8003030113000e43c8114250080f0510914061080c102c0b4400c138480d01d04e40d461080040b01c40c0d8501480010032039060758906020500c03101020a000b00980780c04580451500903400d065454041480c0e02045e070b1301e492610055560450030359203103030781c2d01f503940040c0113808911140d652034550210f03608204c441c0320340b414502984050500014480032084940d80b43e801000010051000c50b98015010740b80801d60b91906031005450000c400e10240b1044072030344c0d83c0550803010341d00c42c0041c0a045c0c1c0d5000d8000c920201d280b422240382 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 988150746 1250 988149496 988149517
    0x12120f090803010e090f070308130e06240403020a03141c271508040c080f0c060a02070e09030a09060804030230120108060705040e01060804030c021302030f0c 70
    0x3400100103100c0f04084c5958070581c10010340d85480030b072606050070b24440d90401c0b0380c484808a288150907680200f0500a000f00d03a00c2c950050400000065100e202d4480c21a036203190444a035800540751002da0300156405450b540030951640781c142c11042114407040810b109020080222040001715031216072241d44801340704642101403aa0300c1070080d01d6041e240050b0900c002104500c1e5103040c2d03450601541d032403e4904241c5007107070b0081225842080b10740d0101200f000c110801149541c100c2c0c1d404c80d1496620740c03003440143c0c01c0441e280d021084007190f44d006c2000640c400700003010300c51415a20040526140c03141543d0317002c070503500640182d00c40d0506900d8003450403000c50a4400e2510400e401d8a207250089000d5848a01b8021100c100600100b00d0568200000c1d900800c060500c141000e08000c1000f806600c140300306003c1006070404101410301890344458460380152001044030010039060000c0d50080d1100c801245680c0d00040c060781640003a507088064 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 988151996 1250 988150746 988150763
    0x6060f06071a0a0b060a180501021c1d0a0620011806090c0902130603050105100f050a0c0c12150614010c0302011d0c0310112512120f09 60
    0x6050401c072120040c03e42c001107940d00c901c4400c55599030094001e40da55960380b400504080b0818800d580c8903940054107661014080c40c101030788400c040c41c0700501e40c0c6844041c403500458100d4a01c124420b601d90041035021000c201d085d4003100c0080c00300001c22220041c0340e0003150740c070b08071080360b40303494604651250350400261040c4c110001441c051342011030010340303032031004bc200d910040050318108000001004504e40500903140107040c102c9911201c9000003202134402d040304080d000810000103411007446000d6003120412941000805100c0ea448861f2024204400d4105a601701d40c032009819041304580182030680c0d03e051885900c3c20035a40054a0340c1d85090307802c40641d501c40d242290a0030b2240440e03c4c00018040050102c0e10062082c1800c00d544175000c401154202000407024141001c22a100240d10a5000c5880740c0031100d00b000a44041c007004240301034040c0e5034400d80e0740c00fa078400036404800c07400300801c540d1024514200d8011420080400300f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 988153246 1250 988151996 988152023
    0x624101e090b19170a06050a120210030b030f060103150608010213150203070b241002030415110a1506050321030a1b050c161d0406021b06060f0607 65
    0x1c02024030200320910b0f6080483c4980300844003044441c030708840019501d99074420801980c580303403c0b5000209001c00340607442070a240c01280604210300800001e040d203502d10b80f82941c504000b940240c1c0b000f01d082c2d03071207540c6030318240201c002c00882c500c9025003044008648040b040c400c85100c000300454125650b80b0b00f0420884a011640c4a813007540410300455000c01c0b07041c0d250341e100e0034a01d0304110003c2c16500c2c01c0c44087e081c0b10442d60088070345806081116030000304131019030b0825103141d052115007100c111607010300c3e4001944540030300c40e103c2c0f0070410b9044000310700c13503c101c0d01845502c1e200c0042c1039590030031010352000040e0100b030380040807040c1c4001b1904019a121f01044c0d03184164400c60032400c219105c500003450004000502c0503040c00442c100d580c24400b10a006854520f41100c11580f80c0d0240c645003040101150403c80c00b981210500c1c0c00322038040801c1c12031301520381d40300da004a4440f40154000704010003546804402c030303902298410300940302103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 988154496 1250 988153246 988153267
    0x9060105092a0c071e0b03010b18030c1c2310021b0106080607020d0c020907050a1101180b1b0f07050c040203130615080624101e090b 59
    0x3403a00d012940c800e20020030079a00f0008040c0040350151094080101303042032641d0340b12460f05003d500128110b2414001449205201811500c1d42e011841c10020204203c00000e07007820010303030416074809441c00b51501c3c204880360081240358003079000842c03100440d401d80300040c0710482c0110001e80141740a214202c940c0d901138513800031002120070500c002d08207642d08541c070942106a13594404820080c0c1e00e981007151046886040c030b482c210903c5142e000c9140e244c00900a001030250101e00c4032078a6105100150010700d0380780003031000040c6d01026907400c0780303203c5003540d0094841c0000303040951940002d0b42e007101c81c2d1303000e00c1c503112000c482c01602d40c000100407180e41c06114120400c641e030314009140505e04c1c021084c0c84482c400c0c03800604465451000461000d80c10b0820002c0c15004034001da4060315680800400c98413044d5403c3c80340030074031003d07a070103620f0040151380d0341c0c1e02c0309034803041504070182ea04000005040035180d141c0c05203e4103105242c10440791440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 988155746 1250 988154496 988154551
    0x601050f011b1a19200a05071704090606020316140f0706080a0f18030509131e0c090e010312090e1302030d030c080402040905070f0303080906010509 66
    0x2820b0b41c50100d85510310a5036940c12100000d42c900140c696494000d102c0a00d6000394015406036000d881006901022025403910389000401100c0200021810010742802071080320140b55200c000d4100030003141c490700005800c140900004c41d440c0c80c03808521940000100d4125010301ca141d005254025540c1c03484055807410f00c03400a0180c0361505200b000f080040402400050300c1c0c01c0982d1400c00b00500c100e0b0b0030341c1e00c0021050300303002000038004100c0e9414030704a9018505942e8941010003c11a00e0740c00381600714010389442d02800032880e1100091704040c5d0024024440d010b55a4070844121040d4041c4140b422411001040003880f001d034204400c030a40c0c24529289507441020203801c03c411034003000022040740c020b40851900f40719072021445d640c1010070109003e800c00801e03c2100030002070042e030b940d003c0c0000344881000360383c004040a840e81144103403030b850010004d64007503600840c64845e8800201d060726040e101d40744210f40258542d142080d0009608c0d84 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 988156996 1250 988155746 988155767
    0x9060906072604140a051f050c24070e03030d050901091509020f091905060604030209090a03120b1825090302091b04060521010f050306090601050f01 66
    0x4070b401000b0350365081d00360800240803989168004890b220b500c1d11410501c02d101e114200703889242128000d2103550b6a102d001001714142d1288903040a1884005031400e2040f4001e103c040c0c41085400346420540070602d00020310881d00c2d0400c0c40c0c03200201039481280318803102d079060700300344181c0081d440942e10150780100e20b800040b61105140d1503c3c0c44c84814809491903564984441000b5400c0c400c020081c013100994506c0454902030040600c00c40020441407041c030745507008a4426500e106c1034401960300280181100e04201c1412a6651003440e03044020800c4810740912210381c43c40b03070541103c405020380c031103540c40d14404604010f00818403402c10503907a0f01a6502c2c40b04202003a0302407960303110111000c0c1140104950407400406600c008244d400e444034182010400b51006c40c0c4590402540310303200000003076000c0400d8440c5094801140c400022401805148501111425001c0d201c2981380c11407078580f200d10034000c070707904049160940b100c9035100d40340050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 988158246 1250 988156996 988157003
    0x30b0705090d080c19150c050f040906061b0305030103031b140606181005060307052104060b0316180204030b1f06090e07050307090803071a09030906090607 69
    0x40c90940e207100022110582500705499401c070204030940c08110402200880102c909902d0700c44403080e960b90381d01290a003400e0241240c559006000460265050703401003081c002030141c8031900d882202000f411980b00300c60000e1280d4503503903185083c80340e10360141609070341e03620310316820341d281940c0313aa40664a844a16050b2000e070310100300300c481c03407107a010410000350066082c41c01c2001106403411806245200402083c00a00c410b40070900044400039214a0740701d503142001030356071b8012001a0396590342d941d80c4012680d0f180c000124411442050100501d1503840285513855014100100c029410380d40144a6071000d084505000303c5005005490a03449030b0b40c900400c002030342c200500c10420962807140030300700005007020f070980f45081d498461410304000181c08001d0021028031000102140c5058130540782071003c0c19122007201d95604261400e541c005104c0c84c4120052403240010841d001d502008a40d81c083c40204085e0501890000300300c1654802c4c00100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 988159496 1250 988158246 988158257
    0x403050a0815061308060c12040b1302120a1b0e07030f0e0115050a05091015090f03030206060114040609091e110408120915091503010902220807030b07 67
    0x300280c0c0d0b07610003021310300c5801030f0300351000340342092980c41c102010f040910800802e000d185100640c3d4001d2660040e00000c04204a0312030380300d81404240340c031b01d02a400552400b8902e045400002d0700d4814184500302e62807485d0000c1c201c20301140c1c06805030003521850440404d400d24841d8000524940036a003000880007071096a4a00311684d5042d00c4003068440c1104000078984040200000d00303080d1004001823919040200320100035001e80f89865504076950302e20f07a0312480c00c1c0070203480904000c903040350702e9040107550347c80202d510900080256004541105100d0b003603800b100c2258980701e8403982044810320207806006280310300301040d280c0c0c20701c05100341c0c01403c48610121029603078440c14110490b003407103006c10f41310140c5035040040e09442d8507210380071660340b2421040c203900e40d40359074000746d1058402c2e400c2c09000e12002c40081006403c55004000e0405807814205002040742c68210314182d00788241a0190400e050404c00700341004240d40d071040e05071601c5c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 988160746 1250 988159496 988159531
    0x1101080910051608090a0203031c060b2b060f060e010302070515160201090803041106091e01030b0301050c1e040b04090603060c031a060c07051e03060c030403050a08 73
    0x58411180c00726004014010031115910f4190f800510258000c844000035000c0303204030390040380d524822100d000b844940680014804120b50341c1c40760300500700b1043c045541e401c101d5940075001c0504c00e100e0752031003640d400181204030720b03124031401c40d8550007d0309516450850305640103411012424103244d0204a4480010024050784030700034001101c0ea11941060910f41c458805815030310415a803501c060756001c00d418400780ca900a138088070312a004240c2001080d0305002c1c40880030f8000444442c01000e034100c40220303445241d401c0c0d030100500108007041501ba036804ae070342e801c0c01c91003c11003a0180c4039030078100c4c6600850440514649070b903c1c008e9140340d03030190b0700076a1641e0380c0707103401d00401c602030044001850162405000e0081460f454a00864010300d02c135114080c0011100001801400b811008110062540c0b09080c40a045005881c241400d8030748a4003900000540381440c9101b9a40565016521301c3d0403c6401a0151922030b0040c20440111440000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 988161996 1250 988160746 988160773
    0xe09060d170f0d140906011208030f0601030609051504050c1215010203090a0f060f031b0c1e1401060603021216180b0c1005070f0302030c160c17030711010809 70
    0x281044c0807081300c81100040c5004004582004010380005214015091802000c144940c0a50f0381100d200c101340f015580b0746c0b000503002807a1603800301044034100320400030f110030107180d00e040d5000e0956040c00160b480410b0f43e1103501c03d550050524050304004605a2503021514042c41e0714180100e900c0e020800c0001150f110455210341480740b011003042c081c01303074080100f90799603003241020301c644809a0002055006514121420001855110018000c0c400260808882d4906540e40d50000600f000d4010100004c030700d502c40d42c00d010000a069101c2d1003111500b900d941075420050f01c412241000b42035019098100f00b00d240b400e040341c4026810700d12401084042945562501301446050034400140400340c44580b504081060355904a0500d040b0800c41d4600183e6907034030450450514001c4038021820145440b031031a0401c07118034640c41c282c8000b065400700000400034103681e03d1003500d000078804100841260855400303003080d2904040000240e0740d01822401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 988163246 1250 988161996 988162001
    0xd09080f04180b0d1b0905240904050c060d14010b0a0e180a0c1b12110d120504030c05120414190e100b04060e09060d170f0d 55
    0x165030620000c00060400c07880700c2e40604603030320141d104418010808400d000032900000018041c0417004121000720f9281d400421401c090550090200f28a007042046445084140da40344a48140000c1d2491140d1400c44241403195500c4802001d00300d0300e680138402e45d60003a070115115140c50701c43c00706103140e442da48503010300101e40d60213460b6019210000d1840403100980b034051331081854001480c800d05082c2c3d07000701e4504000c1000106054222284042d00104041e0024141485410030101c15407414070300d042940c802c440c49110f00c42071512810381e031003100040744e040c500f141e807202d003031b504034a601034040c0c24004003100d00d80d01c0c1c1e54202010001e030480c00400c0010107000466545652480201058500c01e44169000b141340c7e45c5c0c020103000d01c1b400702d8048030009404580c0ea841410280054007070150b140c583c1d40e04081c154043c4888164410b1550a0000da4a4204a0450040503401800550b0039000c051803d00c10390f03000300451907880c80704201c02d031031048860 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 988164496 1250 988163246 988163257
    0x16110a03051c2309030c150103021002120901031802060a090e0c04060804140c3303041104051504060807030210080c0d15030c08010e0601060516080d0908 68
    0xa490703240d50341240341e402541e07031071185154414051810103000d000c511518a8800504610b120582981e1075100b062840d40c0143c049015a43c818111f030818404260510703641280d200741c2e00040074a031000d9059031100414407015a03012403e008108a80d1702c240c110301c5100d00c44080c40c0c0c0710301c1201d0f004103e80c7e40c8134403a030318081420030004100c4403141d5146150320030301e80e00c001070500e03062004c018080b00c0003510140c1034000c1c44d01c054507600300501c0b40d8441c61030014500181e00c401808580c00400521004800444240d803c90b035807440c4200407648156030080c00400c0c411118800c000c014280503040f001c122684102c948070035100d0348503001c0074080c80c00003800c10706d1a6104100c0110b4400d82d1420402000d1020b0188200c082400d0f19100500181c0c08030b548048900200e800b00c0f8681d101508118a01c4000030350504117502c005200200c20003642d80d1680c95580644441c4507010403240a4500002d50700081040180608000b040c4010b011071b00350200d44550a468100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 988165746 1250 988164496 988164503
    0x1c0f02041e02091f0207050103020c0123041b0e0f0a0f24050f06160302150709170f030f0903100903050a0f03060b1206060c01051f08030f0316110a 65
    0x4150f421071410b50044940081284007414420780d00040c029251011486124141030b00400e130b901c003c0d042034101002e00d801034800c421410309041e04903103034a142035a043c1c40ca48003002c00c0041c1c501da00c0c9d1400e0b0640310544103440312a21030344104003225034001d104030400c030355920600307407211003502603807010600c01020007103490b907a44109448078020f079000031b11034040d241240e100e036200c80301625110405181c100c0d500001609080c0d06001c0c211200702c06401011080041064002e240070080d107042d0300307480c1740c28070800400f56038805400705255402e5106208001c00104050010f000e07102c000390664101c000006640801d8444442c0b00b140459004209090f0721039010006d4450070030740386402e03c0f01c40e142c207407004494421003543c0090040d2500000f00c103519044100c0d9004504034008024520303000722016081d4861003154501c1800c10440054051030010a54003d540303560585e92540e2685035025541010a0034800d0600c4202005080900c1007408004d944501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 988166996 1250 988165746 988165751
    0x403020f01060b0c0c04020703050403080708030f060607050c0907031805010608190f0201050706140f0a391107060201060e06040903020303061012060b0702030c1c0f02041e 76
    0x40c0601a402d480aa40243e00080018001e07150f200d00002071550b0090f80580d001643d81049040c01c0301c08d4450f540019100640029200040002d403500a40c4940d13441d84144107030b034444a040024511888034040c00baa4003001d1103e03140c2c580300140700d401c46990b0400048940f0b034215903113440811040c00303aa560355035403810400c0c00350901600200b8141a11007164a81d05030b660510842c0d220300e406410407802168201c10041c02d680304400c204c0c85050807080a280060707a03109015005c884800180e401e0401c0c203840d20520101000707401c60700c90503003c40304a14042086040411603814010000322148001c107803070060143d400a03002c9a80007140c0c060800719203d80541000d8120b83c02640350007403950101e0b07408000e403500200121520415401c1139801180c0b4180d00500d05c9040030300d008000200001c44000600040b4425070544407248120001c110307999065041e0318442d80c0d08441000c00080701c050144040038401040000c2503ca010a84051480d103090380e10403855 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 988168246 1250 988166996 988167013
    0x3150a0f090b10030b060d150512030702040c3908070f140d0507030e040609061502010b09060f0d031b0c0311120c040c14030c04030309091803110114040302 69
    0x4107420200c1e40c0200030f00b02442150045001306e01c442c4184a40241101e50301d500c140ca05a10016805008000c028021401000301c201d00c0b5803280d04c0101c1c100d20541ca09006010058010748a04a002e6480591200580341d105498843c4034008040107245546080703c0c3c1d000200560301600030640942090402a0a40d14005200d20900703403030035180b903110049841c0c107a0703404000ca842840d458906a0044c625420101b8050640c50f0000385205007440400704141e6004035207919102100d50081c81528440e4085c81510361003550410380000c0030740d40c0098241042003007161560700c40d1801004a03440800c80d0800301218600c1200c4c0c90b00c2c1a0350400500090201480701d1200484180c50940001840940c0c2c665440324883d010b140c5036a401e00405001c0c5c860104240c03194074010741c0d6403500980d00a1254810700080340400c080311000b0425010034800c4801103000f00034501000019510151410000c540380b0a40d1592241e4100d0820901110182e001c0c0c0c1c4640c000b0940032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 988169496 1250 988168246 988168249
    0x3061f02064215070203031605010b0d030807030b0d021f020709020414010906020c030c04052215061e0302010305130f11010f030b010e0d05160803030a060f0b03150a0f090b 76
    0x78190303904400c10f00600400001da6804030444040b20454800141460311394584140585500007070142d20010309500d203428036070010040c500c9141242d500300901020b603020000c2d05008210040d4100c1c202c100e0038220202c800502d00f640081d01e00442c0d513180d0381c5614072400d036402a000140d201e14248107455803942c2200317480c00544200e00140100744400e1000c29aa0101d0f03503010707480786460b03001103a4007101d0704207481d0b980c100b074080c45403000050341403519543d49001e900aa0030380ca8035100240034a0f84000015956104001a642c1c1c9480c41e00110003030a03001c0c01d0940c96840050800000444048010b8021807094824101a6040100243c8080e07801d04000c401c0c5810112061b19982e804814a10081d504890741048072045003081454031540030703119128100300b42e802080c800800030103188100f91085090002c0d68444c04088020a000e02c01e100410009002051403030300401114900100040d2500b6a01a69020081081d449641c80380400303036514546010079 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 988170746 1250 988169496 988169509
    0xb04231f050f0c0706051506070c080f0a03021b010519030b03010606080105030a080309160f080f0307120f02011b031e0b090c0703050904090803061f020642 69
    0x2206111900c2c080600d00100700c07000c2c510031050014921640d4100003415540030440401c040500905465156a080d14000e44207a0503409405c1e02c9120b401c4600b00b44803000541004010362540c06040b01c803016921000004800103006070500c44141b001c4984040865813414002c1040d035004100d0320500c101b41821074aa81d00038004014801d0011701c880c0d1400200035680c03c0d40306001035961380d05d501905050803066440000c107005030010000d10400525141c02c2a20314100c1030f00c02003010320070134075528400c0c3d1300700030b03c15090b143c110a0654041c0325040c100b81c1403800045040160949000c0800c11000040008281e8600702007042c00701040d40e8602184801c0010001c6400200000f44401c400420f4003581103030001c6c0400030588920243c51066030b0107081408400b24500e4403d01c035800480f02e540c002c400c00000007011060b88407000f6401d25031500a011107480301c0c031190751491180d030b00c01d68403940e0302d000c0c1a000c404410700c008124520304145045141e400c204009a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 988171996 1250 988170746 988170751
    0x1101020708250b03010b0301080f1b12030702300102041d07050c010608280201090501050a050c030d15060f120b0d020d0b150a030b04231f05 62
    0x45510440003400086000034629111640c10034007000d03103002c503580d50861061150440b0140f01030100000a410400700091416503040074195014040040c4416030382c0c00400d4034006400841d100d10510b282882e22140c0c5d14405a04c064074608138480d004207541c0c00c010020518114040b1402c3d104807002c0c800c0c2c032400001507200a516080c038006007455140d400300c20351a1034102540206032940e0082040725800005c1000a010641ea00c410040c1c0380d4183d54081014030910a49000c0140d03840307600402c06a13416101d01c00d001e42004011292a04004030400a0203000c110305480450104083d004036030800d0700110310b41d0002903044034440220341c03040d024041c0f800d030f00085841e0440c060024004140038001805c1c1d06100005000350801ca00203900407003040c80708400d210b10801c00505c83d4551484525a4045000034087c03540d2507480058000a0040040380001d141c104c5414803803440c0c1d908101c4079140c20b421042c10588629408078055070101642c8244c24a14080d695 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 988173246 1250 988171996 988171999
    0x10606020d08011e12030801030b0f091509010f15031101090602031b030f0307030903080105030d0c151d07080d0302090d020f031f0209120708030906031012030c11 72
    0x4104444100034051810600400114003070414207013543c1d400044455005217041041c11011404d01d04005d00311b000280004d81e0362542d420b001881d224411001d5074040d000400003481d94540004050f28442009080700049540f50000d0070340c0c2d000305000785495005242900c004251440c9080344030300b09101d001c07038140300e001c00701002126004400e85001461072302403500c10301c1c0128605800c512404070254001c25010060046080c1e0551102c29140d1198407000c0b5aa600c0b581011740d140460341d001030008000500e0800018a240c1d184003e6a959560108940c0a45061030340011100c0201100c107a000560402c5071042c108034101401c169428118540440007010441c202c07108040a805154400ca694600744c4003003102c0700e03481c3d01c02c1008510b10801404980040d6001c6206a8410b030f0203024040e181c030b5030100305c1d4000c446800000b5454854070350203006240d000280007885506401100240340c100441d1403c4942d8800c0da10300440c00200d00c1c044580311809083c1c41d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 988174496 1250 988173246 988173253
    0xf050c060f0a020123041e0b0a0b040c030605100e0d1202010e060a050f0705090118060801140306063f15090604050a02090a15080721080f0a0507140f01060602 70
    0x81840d0810401054210783c001f8a049884140485003044090703484030014000003443e0b04000c43c0c0007141d8400b4910b014111340901440607052000c030700f610143e0003920b510a00511003c2141d03405245420040100604480503d00084e21006403100703070540c2070350144c0d45070781030b44000c01c506001040d030044c0c001c10100f0450038401c0060521802c000c100c2d009100b400101e88605c3d03030092125106000f1a190788942d03058407890010840b031000e00c6845003442c90151002a02d14002ca2040c2c402c0d03801418107000d100b020001c4804000d01402701c004524980844103c64540d6800281241210708006040d01ca48103059400b01c90340c0180007100c0e03501b1035414000005c2c400719440b5403284d0100c6007450f0944940e400080140000c1d03030f2245a02000020001d80340704041180b8040322400640640006540300011007400d5440b00c004020020410030600c14500440141200131010725016080c030710306685040d89911803440584031b40d41301c101c00c695045130900601000c0d0001d071014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 988175746 1250 988174496 988174541
    0x50c0708040b18030105071e09030809060d060518100506040e07110f07060c020a1a030a0e0a08160615050d23190302010c020601030f0f050c060f0a0201 67
    0x104080d038012409816080b5000080b4443c00c603250582d040000c8500a000300040d050112000e480d140840200340d10074206803001c1410b40c1d0041d81c080c001c9a41007044103103029108001c001d207561202145070f8800e5510740012a003600d484145200d10700c0b0030b0801c205d1500f000d8000fa004042031368002441400c0404c818041c8400001ca01e035008038103400c04250818258250030300b0220000070007800c0b0302c07803100000341e001e60040c0346100710340c0252942c450a81d01c8500314003851007030244001b0b100208001140748180540c0c440052240c044080d19041c003032503565150b5950014070310f01c00d00e198003040c0340c007032207000e10030003911001c3c2e40070010394a840c02002c076544081c807003001380c108840003c0c2c60700b0000100d4850780c115080c5805540a02c1a00e50110340b10b090b405000751700640c40d0045030707962903000003035141c10b980d0003040c111184542903071101050030360a10f044555018802c10011140c64807c0540790340108040c3d41501c61a8140000f821aa0310205c0c0ba8442d9402112 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 988176996 1250 988175746 988175753
    0x1e05390109090518010e07051203030432100501060e010e01231c0e070602010e07090c112d070b090d0503160308100b0304051216020303120a050c07 65
    0x2002000c4403104400412183d5448048000c000303c145003844c1c45508050003450070f03c4e000f00b800016944101c45992030141c100008954a000880d802043c3e04182a208011511016130320101c018121510340f41c91250384880c3da0030820340e400c1c10001152074000600200d41c028610461491080c030f068072040e003424000900280720340a000c18181c1c4800c0441048181c2ca81c06c0340c8081d0710b0070705050380014880c0201801440c4505503490680900040800d04a2041c01541101940d4200070110a030070480003d00400903480002c0502c80720100c402080e401c1804083d202018000b071000034075846181822482d401002d0040e00c80e04610b00030300028034901c05560f0a002d00740c59201020405103000740c40c5200302000c441100c00542042810164440d08143c412040d4031140421255205c1e1030000501059400510300d411030760032600090b0010015228944082040340c4188220b5004a411540079183d8003522103018801c110503004113008aa400007540402685050040d44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 988178246 1250 988176996 988177007
    0xc06030908360303070b0a1a120309012703030e0424090606020d0504090b040e031810140d0b0a18140610021905150115090506161e053901 61
    0x7447c0c4800199603408071000a05022080e801049000d007103d40101c50b1204000da03644c104034100750000c1c021400005241ea90b0515170704c0740301c80080800a6160442d5415604c055110b4845a0041c0d910a00d0050303034140c0d5040704034411113680301d005030603040005100c2031310b055821480a40d400032003082e01d45607114040364101c8105c12000110760b811440058003402e244610b46640384400305420040710b02c9940000d000c000102c1c0c034031015010709407040d590f00d40000c00e00400d0050600000c080c2116540000c1c08031040140504951501c5450041002e203050b25854115662031040100d1003000a200725003040c03045030f034401020748158000b95a45001042082c450001c5550034080010070032620481d103009008048840d03031103030802100c02d4200241000011074036440000c2c0303400e204084643c088a80340d03140e0000754080c0c441030020220400c0c1d0f0502d40303e00c204041d01040c4244180c00d40c00140448140790309130404540c1c99400e01c0000076501144207c204032001e6038004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 988179496 1250 988178246 988178251
    0xe09070302040614030606120106020303012d030b0a090209150a050a05030c1905150705010b011821080c0304030201090b040b070b070507050f160f030c06030908360303070b 76
    0x95046581d2980d0303120115007d40540e1401c5883c1c108507000101e06580c021024506a5024140708110b0042503110b210150301c00b614242076025128070244040348249040c59440708850501080000310707036011849000c4100c1c1d180f1409030380202c01521074603140c022880281300444e038109015041100090312809205051803091620364031b11108480340500328001007038020100390100c418862500c1c107551000004440c99460944222015801036030b50071040c0005000b0000342a0070000308562a084c0c61085003880211201940001101c0400800c0c44442800140d9100d44c90361002400045560300150380307000003480244124035055056a6046402c80380070081e40d240c1c1c00d410740d071a00c00d050300900030340580120781d0006e01d00081d0100702010001c2c00056160303a12840f551006a2070b000040403c169800c042180c0e500c00c1e0010040759000b84019858600325400c0c0d204082d04c868541c03841c400b031180c0c044ac4a540b042040d000b0030360043d00035610b000e20035a2242c1440c0b000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 988180746 1250 988179496 988179527
    0x903160906320108130b04080403021807080106110a02060f090f090405060606130518012303030d0207020a1d090d0311071b0803071103071403070e190603030e090703020406 76
    0x599001801030180310303620800c0503800c07505000301b0f0304141c20240c0030b40c2c0c4540001d9000b098281c48010340b1003441c402680c8200d01550b84d0300a00d90070180b084450300450255960140f00d20b140e070720003507500c8800038144c40b1001d08030155100307908010302c0303590f01003201403a11402002003004041000804c400f9800607044a18071f5854000c1c51103d40b2200064102c45e801c0107800904041c44140c1084890603900040741c500340b058101c00c40350b207540560320300c0160035400510007840c04072502d4010b0300d0541d20003020001c03003980314540364070b02c2080c0b1414284204880c00900400100a110b004040207071840c0c14014811028860000c0d03100d03107280100000403815440060012451019000d001d162003500d507074840c02d08100003844941c111951185c01078020028490b5080d001900c0541310107409481d0711460404011030483c0002d119141d03114202d91502c1e185c180ca4400c50303010f141300c0d4880e4041c81d40c0c00014044003480c010041c1c030a1520400007403040c65001741140555041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 988181996 1250 988180746 988180757
    0x50a030f15050108010509010b1017040606210308010602121602040f2c03040602070e1f091e09080d2406091508190209031609063201 59
    0x19540351001c84000503404028101d45480b001041881040d002240992101c2000f03028031084201009071041012040c4004540348113400c08071500c940200c0c3c1c1d07100780a0000050200e030b8402c082e5500840c484594414001c03043d1034a800c02d07800c01119405004144014248040c941c988021244160011040c0c0000749800c02e20455603141c02103038220850190620228506555154400b03142110217540c0707415000c032410416000000761021a2031540c020400c403407905120000c140310103400c0320b441c00e00c03a44d0300000c0c00b580d0510580003410181b500082c01040029580500848144004071782820407000d00301080965042d40c4070048507500011750007000000c0701d01d21800901c001c041402d180d00c1c4c0025140d40148083d821580e4000740070f095060211000c1f1001681103030010040000d810981740100702ca54042d0a501401808a5604062a03018800c403001f030f5900541d1040c2d2030b20014441c501c0c0122883d1200014191f010141022030a0b40c0401e181184240d81d04200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 988183246 1250 988181996 988182023
    0x30316050d1e140c010902030a08090a0902120f1017062203020a0845030a0c120f15050108010c03020a02070504020703092711190f020709020d09060b0a050a03 70
    0x1307401c0d03000303111844c0c0c000d041380c0c800c03da0b40c5000e41940c0c001002e028460f58521000003160641c5000311001c40b8220301102c1e44d903035244c20300c0198015000e05107070030300182c003003012490058800040d83c6584a2600528651814400005802c03502c83c0e84000b07640b10604629000980000398030301520f920070707000741d181c0c40c644000c001751382c4004118101c1160100201040d00b4000c503807140c220171009c10041d4520501405240d81c030000441d0040c810442500b08101000216212050b114800d85e402944d0340099241d080841001c04a42881c0d03a64400040040d04401d01c20000e000107141015030604c51700c02d0020352034141500c10309008580001e0710904041c8602460409480d9074010168050100035031844003026825040d610b4520b81005a0100c01c0ca40c81030302d0b082c40419030000809903840100321901c0c620440580103611400c0001304a550450024008103086080300040c4002d0505100c410360b0b907400c10940c002e0340351075004c3c80562545507040090b0798119a41d2081d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 988184496 1250 988183246 988183267
    0xd180807031d03070909050c030606130c120c030222062a080a020607171302010509030a0209012903041713091a12010b0307050f030316050d1e14 64
    0x10442c0540715414060300d00003044500701680211049801801210455500c21080c11303035510090302d00b00da102c1c4401009140d004050f4001c1410010b29250111001c0c0c41400c40c101079811401c4140e002c41d40104410a0b8134a0100b04800340d8072046000d20f0001d80f40440c0541414070741c1c0e048000c80d13001900501d0803502c2d44681c04041a07803101c01e00d503840c203030460000d46403101a65500d0002d0421113610049440400295025a0607040b0b0407126181541c019640b5501035044260940121442e56026a0ba6a0b015038002e000f00300300d10045043c103c40d5242650962104025540000e00601004c602c0b0b000d008140c0504807800075544200859010b214440a0b40c09401444c2c2891070344400b285c0c0c044844c03141000182c8028100b0290000d8040c20303035245c41041505988074000810286c50001c09012154030068141c0c0d00d09061011409103400f596030007503030158003034030100052980c00729504181c0c404440f000700c59004a401c008101501c40320390078640003800b14030304000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 988185746 1250 988184496 988184537
    0x60906100e041103010803070c0b04050a090906090c09020d06051e0118091b0e010302120415060b0301170d090e04030e2d0a060c0206040302090414060c0d18080703 72
    0x503d5204856616583e44540d0030750740c4c3d4081f00701210000e00100d00083d82e20a080141d8041c1c400c02461050f5550402c0c095030300a04403820140c817a42d842d4400700e40422030626021002e0012103070090303980d41c240b20056090f03030b040d40d0209001d101080d03018803181a030007000c00b101030750034a04a203007001006038100481c5070940000144130301d001d50801c2c0c490301e4242e0703a1440103c80e45403502001d500c680190228011021691003288482c2d002800143c001603201444540400e03002960130744801500780e15030005d820115540f080c1099460512904001d100660000d91421400190420104c03c00c0c1d050060310040a00c6500e500d103c00e10396807001a0255001e0f1080c0302181e500181c6251025480340045040c000c2c2c00011020604e41c0c899032070548083e4001d011580b1341843c6500748140c56100910a44900d0800310788528003e1041c0102c600410103568072607100c00406100000b22114559100c10901c001c42d15400010800c200355881c29800d0b0600141d01c1050170b02c40c405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 988186996 1250 988185746 988185761
    0x1505181b0915030a0b090601031b0605192c0901050904051504030201110a080f010608091e010f0507080a0506040b0a12030e040e030a030e03120105061305060f0c06060906100e04 78
    0x14041610304000d080c1000090307d6040728004c0045401c40d044601c0d22080f41078541c000c14001903010851460006c4070b02484044958461500d1111200b5101841201c412039040e551060745c6503451120351490805072007409000704413240011410155100d9a554459205000002c1c016a0000c1d040c14000e51040200e69056021240d482c1c4014100501108003211a04400542d10002244491088080034810824000240240250320041c04100c039003603903a1208664890600ca0f550701c800380219030141d40192203000060038442a803400307940700100b48900031450485008230943c2e40b4031541e01220b440740c43c09600b0f011f4505003280e000b0580d440703064010f824603800781c1c40494004024003510b0410b94040011031242000355403a4800c905250031046592401403099181203001405482c0703410300080100396640c0041106038101c210103c00a48000c42d4000b00351601344110759000d0703000c48a001840c58400001a5010b01d4060740e1001c00c6403010401c0403d460319841500b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 988188246 1250 988186996 988187003
    0xf090506030c030613270c050402040806250804120507020904080912010902151c0612110301090312050c0705070308071208041e1505181b0915030a 65
    0x503070700d2030111010000b5902c15154940245649140740c0458403507841014010f0006a500c9603181d800700105490100444034203840c15401e0a800050640d15440108000e06181000d818a45046540c2c1003290a2201c0c94000300b6400d81c00c0c08a101d64001c503041e50069002202900c03042c1e8a0504869070300600340002d4100da5150203010620903d480034040540088907583c90201c803940e441d500f40c0750035480094000041c6400901401c0038a406002e64060195541d60b400c02114228416104075a00c0800000c07200d1181101380000044495507911055000b031013142182d41d0000e0001074010800c2a0040c0d82d4008504d050b60928110341001d50803e00300c0c6c10858407800d00310724903070213400700300d605000303038902009070b58001c0222903c2950400c501141442c03541c41e80462940203010112042c00d14091072003809511440345a00030510340c2008540300f800602418640032041600b82107200340d45040c00c2082da14842c105030311a4400d07103200661182c3c207001c280390052212004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 988189496 1250 988188246 988188259
    0x507031d0a0210091d0a02091c110607081606060911040e0108010608060f06060403060c02100c020105061c06020d0203071d09010e0a0e0a021f0201060b030c0702010f0905 75
    0x600c4125000150101428022500841601d07000f107400d40311250f0a10030040c0300312490307901c07041030719048281c0c5500649102e809440c1000d040002103d401081e4841508803110409030028003079034036000b140140003a00c1c0d044c5440802d481d42c4281c1e0089500240303421400040c000c08008a0740c01c104020424100c0c1841001c420303400300300e072a1f00140928017010200304000110314405005e110201d40c102405040316444030802074200010082845030844820000000000c2c1d1502c220000030441d81e0190180b401009076807800d449558200000310780c108014130603140e4403892003440c520490108210441582e1610030040d00410300d00d4400302d40301208010741d458105e0964001e0003e800c40b103003c0c076030011040110b505020301818514141c030741e0004020209030751003010560740b40400c9840402050f80020200d104000c620a00072a12507105405241c090069001501900010504528080300320b400d050003a8a4043d0400c4400007a40e00700a004038601c0c00500f1014208 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 988190746 1250 988189496 988189541
    0x603040309090e2a031c0e19082d012703210e12030103080a05070f0510020c010e0601051507172a15010b1305180105030d08070210050703 61
    0xb0380c40451051008107010b4021017000d0068002211811b0550400e5a211030091503064418490038069402d011540300001c034201140a01e030411450310f155a0707100409003e501ca0100d45201d0a10101d50307040d45a05150003010f039154201e01000d080441d009410000e8146818215541c0c0040c0720810b11800298400d840080260b03000004421420400c4540d240c0380007070440c003203200921001c1c03d13820091014000251045000300b0040d402040f00b0400c10710140c8071242000441070030a80d41640c00101072111880030300a048010f0b46600203058607601d4607021030500c1400e414103003000712000503c801082320b070781c0c0e1600327182401d10740c1981c07242036859013100c03184015046d0210f001e0551403244807001c0d0001b60310104502d07c500d1501541d00e46680400e0307640000ea205038086002c420301040ca6142c00e0b800459181c0d20f10580c280c1945810241410314038074205000c1000401c50802085a80001d01c0062030500300c0b2001a41d551000e40840c010a074480c5401d80c6001d50f60003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 988191996 1250 988190746 988190803
    0x1211060c250f0c12030212090a0b270d030905090c04120b0a0524040b06090d0f140a02100c060605060408010509010b03010203070c0201081e04080a0e0603040309090e 73
    0x382c4461052140c1c064034001510f03281c051207070140241c801801a0f00c50540c004c50410342c140500010080a002c0784245c9481c2e440d00b14154001da03805040d281c06000c5d140d0a0080003c209180700e0f4000c2e00c41c03090204c00c58030000c0000401d4022139000b031206002041740c40840c04100c0d801403011100003420f42980f8500f03030400c44c001340c4241c0d040da4100ba0100d10304040e0f91883c000c0d080d124051901801c0400c8007480040c0c8194912194480420301004140da103400800c1800207204407003070100701219250016a00011404080c000c0d4410340f881c50041e00c0c0c030b0000b01c44218103410710901441c51071501030090a00c03038002c19041a00070900081050054100a004900704002817264503400e5060501301e000484103c400a1220140c82d40594055071071990807504250302000344101c0d80d40180380001c030176a81100c0b80d001c001003400f41c2c107900c4081c2c888600d508441d402e02d541090703100100700c40d41c81d014113901165222114102d00400f00015403502a030350001d00790344801d212 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 988193246 1250 988191996 988192013
    0x100609141903051c0e090708090f01060f0612020c0c130f0f0c031a01050405012003030705071218030213180302010e010b0f0303032701181211060c25 66
    0x9200c00c03041c40804402441240a4074440d40f4001713028280d54215590141d044071081d601804000b0180209070b032420f1480400e01814024040440b080e031801d40c54000020112003001c160a0141c0d84140002c842c0a440801c045000c900122544d200041d0f001d6500d500074a0704c4045d10341c019251900014020408d5004102e051405803420401c8043c400070600180d08102c05441c000344081005001c550b0241400c044250180001e0911000c0e411020b6803035588191185d4011450200e11041000071600180d01088018905000f51050711188500c2c1014280030003032162508443c58194503407250b0080c101c001248140b1107035500d141c103005e402403101e040144455400d2444010301420040c005541c4480c014005514640d1128040c90702c002c8810800320346e03c41201da4000c0b00300800d0080811505c03154400e80451070407031402d000c1d030081600108007481005e8021f9402000b010031220760280b0102c45031652985110800c0240003454006200c60300c2012506006110488 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 988194496 1250 988193246 988193263
    0x7060e010e09040c031e020a0e010306050108030f0406140c01050711060919020607140a0b160e01020c090c04170618030903062d0f0f10060914190305 66
    0x80c1ca4811210146406205041d402164064040e4015880800014070b200da915070040e000707049101001012580007910000184e0310800c50407918500510034400140b20b2701d401000f030400210318106001e409001705009622405041c485070020002d4070a2001341180c8030f0120440007004189401180a400c3c807054040300c80d098425940090902c580c00640070418484c0d0002114809801c0ea00304403007540044070132a03c00042d02c5207013a210004204190965108065142041c40d1001203007184e01030380c882c803408114807146a524a6600490103400642003039800344050ba4855000f85460701c20740d0700501140c014200103680117003000c510540550f017503410145800c40f03154955070303072805600d00456242c0c210380040b0300801101c0184910040f294980310420514545200c900528100c5052409001480030400845000781131641e1101d044040d603110395007005802411307010603000d800e04601e5142809421590b6106071290701c28031100140862a0f268604142c550841 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 988195746 1250 988194496 988194499
    0x406050d0b04020406050f03180601080a060c140901120b090a0c170114060a170a020414100f1d120c1507150506040912020c0a06020609120309070807060e 68
    0x5041c50888149058000c960485095581d214100000c40c60140c102e80c3c0701800314503000c41c41c2c0b1040c0300c600d0001d2141500800e6a48041c0201903201e0404000b500e494004100800c107404040300c800720300120035660340c103c007803a080b40800082c075481c00c020448400e90b5035000202c070b0204401d14800b9049880b0a006555450750060351054544e03903051002c0c0141e40c100341864590000d98140080581081c014915140003c07543c001c0c0d209008a00541e90b0180b881d400040905c44c2400607540300b01d04070800d44907031001004684000b4000c110904d5098204050107200c5003200c4110302e0b07481218039005010700411101d00f80e01640da503100c49502c41c0140240708801c50400c0310174050300d20030390f00410811000b050351030081d00204401484103030f0203552807a80c540420900580340d20b1000c1c180d00140f1844100300b081200102c440d034840c00c01c40d40940100545004046800300918055140c0c00c0e4036134868501740d60800c1120f81140c002c901c1060b400241c042d51100507039480420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 988196996 1250 988195746 988195751
    0x1509020d1113050f130c090204260a03121a03030f040e0705040b070209042a06030545151f060807121829090d0503070309080406050d 59
    0xb94070314410b0985008944034003090a030351002410a1120207012002c0c2840340462048003030311584600c0490704560449242141c0e2070725458a144044100907229190400040c0b41c903001c150380041a80407083c12440405483c3c0c000d0f0010340c00380a680401c0440020245c80d00c500103c1c1e03402c0485d81161003881c010040001c046025180a034044800b034810740481140740500e250280041040003170411070392090355004030311514818000ba00c00c20313081c0091005d07078145015001815950702a00b0281721021031004041400640e80000d81d003281e18110b070481c80e15040d0201580d800c0c03036011198050103004428501001c82030307541481968070007102a5013110b1207031404041090340c095000400c0f0680c020070340c20b50054600c60380164181001050031500e01c0f1212204111aa008880f414440b4095589800c0c89004024140d805000f03822414500745842c5030f5101070403d0706009014000001c5001584a90481c1c0e01158000381c010303030345d10394540c1f009125078045075105ea4940d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 988198246 1250 988196996 988197019
    0xc0d060e0601120f030c08120403270f0515210103030207060507080307031812090602070e16111510141203220906091509020304030503041509020d11 66
    0x83d52008201d0001d80c202104001c19600e40d6002e94508000c90000e54a011050100c0c00090484c0e100051140b4480d64401002207c00015406010140007218401400703020741805542010b00802c03046620480b04224004000e4bc825a5603200c0c460050304901c030511050502d10b412502e202d4101c82c440c0e42103480882d40d80e20111010300034024001c101110070404516214030036003000d10a5900356040c4c0581103e5651944000b100c80b002c030502080c880360b010010184c05200e20b100509454050042030b25043d400016030480c903038036580a0002020903c00110f6040194002226032100c50341854204100d030b2103280e040d0751007400c00d003118064000080c1e0506000308528017001900550800c00015000d48540103000000000c4040c03002e0001503c80300360003138030000d0200040004500b01314240740740c0e68003000d030400340c40305004000b03020000303900004403035001e50010410900150f03861600d4016185e41d06000e50b1041702c0d0180441808003401040f8502c4000b11031103510074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 988199496 1250 988198246 988198259
    0x13f0b15040302030c0d02031e072610090507120b060f060a200a1505010501090f031101052a0c04180320010e070b0405040b04140a0e0c0d060e0601 65
    0x41c401c5000c0250075030040301e14171169080200b4491503a0388020f05840d00104000c1310329103040952895002e0960012004110500020b18081c522000300080d0090b840800311456550300e14441504136501e9941c0c51000c140003050244a000e0844210510101c4c0ba10f410425a540c1c0c05851840c82101c5084c00d82c0140e10b0060101c503034940c10758948800041d42e55801c49224070880c401d4040349c0c002d555202c00007500780e1080d411000040400016507506101c0014018070aa0b08086c20513000b555050011070889001200051000d10f0701d2941e4101e4141d026800b02210000d00310b81ca074822111041c1c00d00c0110b014209207200703907800c000d24039600b070320398100700c1c1e0040e0003501040000b400066031001c02c8072452481d0b5070140001c983e003120541c03001d07c6c107095036018480250b004202400b0038901070182c44d120300c0007250244044412000003001c002e00151135a004680c3d5119000200c00f0103012158030320f8001842004d4202d90f90601c40e02801c1750365945810342c043e150011810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 988200746 1250 988199496 988199539
    0x30a1403040b04240e01140f0106020304031506050d08070203010f110d05090102091906090f0e150409060203270d050712030b2709010b013f0b 63
    0x1558200401c8801d0361626114900218082000c4030181c2c0104104c68003c90181c0c014032100b4035079040001018650b01d9044680b034100134005202c061807907030040001941c0003083e075090f240c101c00300401d116000a030640003031006501c09504031664920540600c03146101810031180264024041440510ae1560407983c8802c07601c1c45801d42844141000815030748020f030f010b26640001441c20001d03c00003050041d452504056601d503808041c02050f43c8801d044c1e00038860802042c1c0b0b11810090080100f21004051a95a10540d8501e0742103aa99800150300607070009400c40d500d00b0500541c1d031480c02850703101d00c110780c00014450084000004c0644050401d0340e40d0f50709102080c1c1e1900c400d40c3c07401400c40100754903007022104580e52202e9440300295540055140c409425104030300038003000b00190056458007901e464a030b42c0110071840e40e900050075820760041100340c11447c128110580034000151420380c6d03013a0980d00e81c82404003240846007940c0c48100030f07180c00503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 988201996 1250 988200746 988200751
    0x308090f01062301090512060403020f0102070f0b0402010507120f02011a0f0f0613080a11010507200402042d0e040f0605100b0c010516090602030f07050c0d05030a1403 74
    0x50001161001d40380548500a80500703e401490174400c0c01e5507441c0081d0b034030243c1d103611120b50340290050208140d010443d401000000f04000c3d414110503482e6603108403551100605111000400542168410002c440300c559000c280381c901c2c905140002040f500d4030142e4040558600740c0400000c1141c0b40904103426002050b91804600e00c0043c0300d1880c0307010440341d40044050018090152081003d0b6028110040040c0a12840c0d07040183c8d10301e0130007103000e0503c2020061400400c0301c41d4040e9541c2483e62101414032070f5200d020a000b44265807085d040c0b031610380381520400303a03403203020000c120040c4460240710752035142100324031006a4009244044090340f100000750070345c211070307130145105070343c7e1214a6440c0358491482d4800c3c041d92803507035500c01c20000c0000561802820060507490550440d504002c406540c034070890954132503001d404940d200c1009002c209207801050090300d01e03000c0c1902c81c0fa1407992a0010880100410640000b2621400084040d01e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 988203246 1250 988201996 988202009
    0x40308062416440f0a030203060f01080c0a030c020f240c03010f06182408010b031306020304050c0a0e0109050901380a23060c1203220308090f0106 65
    0x40005480e241c40c200d010383c802c100c04040340400e01c803104030a18902c0107014103080c43d4901607a40d10344241080f0701c10b11206499410f02a02405020604003548291100300d1243c1c10002166030162405a1601c016292103110910414062141d81c4800c4a220350b021403004409131304540380c9011700100c90209000b50340c030201d600c240402c031051017032a1140041c0b00c03041298522540320b52801c0c03400c408046c02c030314982aa107609002525400302c0c0e034034018240070b032805d81107091607520844070203001c40d00035002540100100b0b080c030400740184480e005000300220b10b525513032440144070503824403421102e02c1c50600020b0f00e40c003041c0221206c00324070750341a0a00c0b2a40b641a07016200c0c00001e25803500030448017a140c15100c035450b1402500781c60140e0042c0c040743c0301808480d031603c5034009028a070140060b84540c0000112000001d0031015040e48a9540c000c00129200518000105240120b40380c0c00902d60480d001c00c2c01050790400340d51040b021481740d02d081e59020701c03541 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 988204496 1250 988203246 988203323
    0x20304020907080417030106080105010f2d09080105130218150d1a180d050c03040621060608100608060102101e05042009040308062416 60
    0x164510b44280c0f41c283c3d22a101c0c0b003040440206038000d035a080c0c0c000360402404103120500500c415a00454400b00e8410306190000c40310165541c810407908112003003032001102c4410050052780580318207000f40403020002c00c11031904200c2c031420f020600710141d0164443c202c508a100d082246111b114040c102d05c50480301e450803044c800d446136103034800e60b58084215698145014003018150041e4214022000d102c4001c00045007845071400300760091000400c551600700c0c201106072021a034641c204011101780051841c4480d0b0744503d828100340b032802101081260f00100b155010b00c240f181c400eaaa203454041c10703102e514045d06c1c01805a40540c20b0110944404d070002448061486010b00c10603041c3d2002800f66481521304403480b680c0707805803500a140907840c003000710808984042d40782c105901c010f40501d0300a0003090140b80c0c0442c50007605900b40b0882140d0a842840e01d0f80ea60800b400c0000704410480e100f1164041d45044010103070030380c1e120580c0000641c0400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 988205746 1250 988204496 988204501
    0x32006070c21050a29180601091e020318070b070b06060a020303160e21010f1107030e0a0f090b12010c0210020d060f0b1b060c04030204180804080309130203040209 72
    0x2000c3e1041e1307117a50740703138032815521002150140000340784500a00384841c544c840f07040340320b104904090781600880901880d00c0c0c0410801c1c108001042c0400045c0d4600581d2130711803801c00d90045064002c4100240300d0540c0c00030707100300000c0007048154010400d100f5183c0300d8a0800001d40308807030807000164018404150162040402186400c456003400309020041d40081201d6091107041c0c9000400703c5600c20069150070700415071080d03009503041001e0304204d54441c6a078060380300003400f0005000c614012076101c01e00b10202410070454600e010310350340d02c80540134080350381e2031702c0c003421040c00034402c0c0c030205001d0345182100c2d0381c018181a85005034110000d400484100c6100b64460100141a11420f40100c0c00741c2101d0303006540c2e4500b0703000005c00c1c031840404407400301d0313200004001c0c2c4250080c09071416030380e0450740071520014800304017603015840da902070440000080c0004030024000014007040c03000395280041ca45549208100700c1c0421500a504003800100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 988206996 1250 988205746 988205753
    0x14030105040b0111490c060603051501080d02160515070f05030a0206090c03060c070501150618060206100308091f18050607020a032006070c21050a 65
    0x20780009a0103140150140c0a44c40c00d036032038040c00d15091040030115104508042c4d442000058030080d0601140c90540100040c0c401d540508021324003c11080310300c00c50403c030003500024021900a01110f0301038410420349482c24000303115240305846014103a4403a1400401c0d004040c4103008500f811951610003806808600b805e03c410820f00e042001d200060303140c0c01c1a45043e40180025500d030360346602e029151010142c80e00003683d0203103a000d40705541c0094030350341c4003003220340d550344802152034582d000d80810301150480800320f50307000c500039620a08014100000c203030044951940c031641a41c0364101035031b1305041003243d15018408211188002c002d07250740079194075810135240e40f24441100d1008000f4001070320105156000b64450f21511019140403143c0d1890440141d001480e441194400186604140c5000038a10701d2044c666641c8064081d11455a030392007031802c1c07404c01c4418040c081203010000c110328101d204000030520004e9000000f03249a401c142c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 988208246 1250 988206996 988207001
    0x905010f0e1902030a060e1302090609330909150703060b0306060702030a0807031d0603071706041b0309060e06041203180c080d1409010f080907050325061403010504 73
    0x244005c0380681c5500c00060040c03651080544102c08418829149044920420074040c0d8081c19441c880c801c601c1c2440039081a500c5900501d21034070345a148094000682d08001049e4a08007640c031680b2402080340408001c9100c041407108100503200c2076882403015811600a0300802015503030900026041c2d081c600010031056000404035080380c1c89070f80d60751040d54405a000c0300002c1500180e0307480070311101310f0f04001e1001280c87c030f0704500d404d1000604928860451058507000705000c941c0d20340b0389500490244a451142004c28010301c107010b00607180d801c01c00c4528914084980b52491000f140c20341c0100d50081310808404000742040380a41116240d84600c001c2401c80900028981c00074036008014202c05015102d0042070007400c11040342150300d82440c03042040b03030f001e230780d020440b0840c203000780c2082406c544a1264091802d0b40369085240c0522440d660307003d942d88010714884074500b20313455580201c0d8507400c08a400280c0300b4411001301501340014170a9103000d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 988209496 1250 988208246 988208251
    0x60e12010e070f060e0105071a041506080a051c0504060807022802031005073005070201200405031f02090d0c0521060115180905010f0e190203 63
    0x51001107401c42507200c1c06070500c002940300212030a00d240c001c0001c56040f080c20860039000b400c00354103140050b2034507421078409010701d51405009600060811034080d2945404180c1c1480800c201511401050303a252012003003541c1c01c0c0319901070084443e05261101d600c00c1c070346039581418503280034015112800045c003900154020014103030040c6103181c00c2e1031654000041d102030001c4150040c50b0800d021851080c2c0c0391420030b01045011074000c030101003c92011500510080380d0450301303480e0085079034044c6806038242010721180035415004044681420241d1940c29040224120080c0c440d03072280740e8048c0c020800030b01c0440c00e40400c08402400c182c43c00743c50400307401c0000b04110b10440007210003002c44802440fa50800300003881d0100080c4000b0403075820804001580c6040c14070819040050a20640328410710950000201d226559001c119a075160380304100545005d028801b43c0d102ca61100195040780c140c295401010190740d01c44941c0081c0d07003000d001e035000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 988210746 1250 988209496 988209529
    0x61915030510030f0803010510050c1209010c0c0906082415011106040b040c0602030717030601020a0c03050a030e1f0309020f210c0303070507140a090204060507060e0106060e 77
    0x1040c50003c041012668208090340c13140354a50f1740ca40c1800e00300180500907038004002c0103000d1080f8924807500040042c02c0c045009409038480e061080102c50001080800416410043c0000150044103402001c15600c40406580c481110700130400791100503028000315905100c8007240c14611303201d101010140e418905a081d258941c454545400c400f0754080301c400f9022000c00c000c1c00340e000c2c0401c014110901c0a5482e154443c5c4030130908031a64140c60410050010100c0d0701b0f60300030000104030552140403003403096664288551101d0555030305a000c0342c43d400c00780b40c070ba00d05810305600c0c441030080380d001c0302e842001080707004012402c0100d030000e40b181022103181e51400e43c0c6104010030710352202c51003c1c07900c01082c140502c58104c107019071300a0022000107440030030400103640f202031038801e89420b103500013000c0070143c0d4002c0c048503100140100b004c40e03003e8020700d01d80d4000d14051120404050140e0700301d030101c2c4691000505007200050a13480d001500c1c4414024 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 988211996 1250 988210746 988210771
    0x10020a120b030d0534120e0405090a0209090c04060605040806060109121101142d0903030a080901060909031215051309020103090615080d030c08060904060e150619150305 75
    0xd0f0910114902c801c0e81009442040400c072510786c84036801620a900d02006890500c0181001d9800650303482d80c810000744600102000252079540801a4407012030009009000c200d95079a0060469070190092445a01402c000030380705502070041c0c1d500312a0100301c20303c84403999841b113000c4100102c0e030090410940c0444812000342c500c02608a030182458000c40c10000c0c1c0092400c80c000d4070f520201007207014003511900c2c4d034012041e120220b8003410108a180d0303d00e52042d005081c0c0781c000000313141c5401e03c24414503134040300c41a0020440c9004000007052000004001c99852050f10340c882c07071010b0021107004d03094000604c058818100400e00f80d41e07965075a0142c071040d1005820104082c6410042049d08102541305e0100e941400c010b11142c48200070800440106210702030f100c13034008036003000760765444001111000300035505105603240203e140c0c5441034440d64403880003d04400c11506c0242c2c0140c048420f10014040c1800d941403080d0301429008011421816 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 988213246 1250 988211996 988212067
    0x17060703020a0309300e0f0105131d0106110a050d0e040f180314030c070b15100917190f0809100305060103052202090910020a120b030d05 61
    0x424418044000c40c449180c3c540702c03c0711500c810280c1c4008107400e242000008003039001b00d61642241e0300c1050f030081ca0207990b0341c07000a1820440b0085a0302c0360700640399180c0051031540011a525050f1402540e0391240c0e1030100d02d4142d510681c9110141864101c41000e035003603070085403807030003881018001180307440c61080b180c411204008420b05001c01c559960340304142d482a0744105c078851483c4000e0950034003108003085402407031070091130101c1c180c001c580103a41d402850341018400402c40c1003012078020005200b100340c0e20072041c0210200c00c0000007070401042c8c25203082126011150311100700d4603184002010a807066402d1002006030081644138408a001100c05581b008a19030400000040484000400b8242c141c4211140501007501c8141d078010116011a00051151901310b00c0318148110514412101d03440010110f1030300e504000d00e04410208002c0c20400744010905050311820480040e00000d11308020000703040010381540d240d20003000c016081d524 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 988214496 1250 988213246 988213253
    0xa050910060605041a120f04052e05010b030106020a03030209060f0f04140a0b040303030c0e03060a090c08010203040804060810050907032405061806070209040f0c17060703020a0309 80
    0x140c40540091000440c00136040c0169685480501089880d40051615113101c00c0c155001c180006030000f20311820b81c46c0840c0070712408000d51104109060841001c0d004d1444a2041a0303c409403580c412a00704000040c3d456504000d49040703401503009043e20100c40c0d0741c114001d41c0440031840d80300005200d240d4110454502500025201011a544e40c1d0b080c903101030f12401c41d9608462180381011403d201a1011806480840e030340f50030b0118200c90010030541d00403004142282e0180b18040c20040701e0440350300070203c01d901071150310f510103455480d180c0c243c0c0f0041320007074000d00d020031040003042d06c00c41c034081d44a90403c441012454868000a840c5142598003900080c0c403200034a06110036030014501c3c02403551230030406c092070100810014003800e08018520100c9203200174840d1222801c0301e5104c2da0082c400340e09032510b4900b070280031000807403d58801c00d100c4400704001008640300f0489440d984010031a503600c4000c02c6010790312000d1001e0030076440c1e14004000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 988215746 1250 988214496 988214501
    0xd090b0901060f0b0408100b0d0b0a050117190323070302031905091003180c090e253302011b05120408090604030f0308040c0f0e0a050910 61
    0xc080080020800318500b8083d4240068680c000d554400b07000c000401540b8000070b503241c0c1d0141a90404101421500c000030b0820010b02409085a0380d0780c800c009052205a2003e410b0741e00038521030030300c41109078125130b0740e10704c00788c02d450700c1210794120401003801506a030180403c4080e82a10200b0982e000220075006100e00300c0150f807001ca00303524281d400f40b00c0446030070640d2401c40d08142c14080007621145147d40584181591004100b072503e5070580c05c400316903004480c0c0e510442d502d4542200505000090b0071603801540d4007104401c2600c016407480030008080c8144581c10a004280500203403022680c080e01e40010304101c40f4883c84050130f034181c86800000e4121000d4000e1281900454009010841d04002e00c00d048001c011050390440e801c031f4000c94440fa46840850602e02c50b0790009000b0341e40404110040513444080d841c403440c400c203116081036a6070041081c03454010b00403201040308440020365860810741c01709030701842030800c6400900c50010780008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 988216996 1250 988215746 988215751
    0x5040819020607080112020102100506031213180e070e060631050102033f0415060803030402130e010f0c09030614012417100905090d0203030c0d090b 66
    0x560070800403c070b245500240700b1801001c1c00e100c2d0020803800707030740002d403540c248080300784003e40e4580c045034207a1801c000110764064803002c056920021050101c3e442c03111481481c4140180c0c04c014034518850b40a5600c0c040d6a410003071024506000c001d0b684030000510083d000141408000305512107000e0508644904c0f54030040141ca040c0d2040c000c803001508054150360003040200e6054420030342140070101c0c40e07460801d000c509000d180480d1600c203147c1034001c0e0205800d001c01e01921a50245080303490305410403241c0c1e0f0b5454101e0700c83c04102d41c065401620300c2940c00400019800400002442d0400050264400f0464404441911104000140c4000740c240200800341c843c0518801c0c0c045480c9089604d4402c071030000000e103451000b601c241c840404a641809010a91400305011001301864940101c0410404101b4450f0810305800e180100e0301c05900406c1d41e801c82c032400d40c0a036245546140c0c0e80f0030b056102001a41e022a543d4041b5004550494070050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 988218246 1250 988216996 988217047
    0x32a080f0306040c0c0c1208090604030317090f0a020103090218040b190212011a07081204060c18090b060403081204022e0309060b09090a0201080907050d06050408 72
    0x7512818150b0610003203070304605012050151840820000c510407050315422039803400014182d1341002e01e45481070f800342c4203856411000100d0040101078100c80507080750901a00010819034481c0051503441c10031030220904c40c0c10409068000d075119400042600c1d001610181c00b4511420100981000442e030030f4409441c0d02046c0440c54800c1d0103d103070500504142541046005144111502810f20856000300010072505003071020010035103440b035421820107034540905a02d1070b0062641240c084035014540520390941c64050501c94000355070350909080610b04000e041801401d03004100381d4400750a100001c00126020b005060000009846206906291040c4404140c00200e40e2900c5201c1a03030000711020030043d01030b1b94107030a150228405a940c18590001d00030540c1264010442d041044010280001c60140c101d100303071b95010696840340740c05900c3c0e00c0140a440d900c80082c00d41070b0702291141c1c01c2941c120340595410b0345011940000060900c1ea41c29691 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 988219496 1250 988218246 988218277
    0xc0a050a0303050c09130b030109020d03030606090b0f0306040506011407060209120601061b0309030b04050a0b0f06010233011e0e0114060c0f0d03020d0501050607032a08 75
    0xc0080541c940292608040100da205040120316000a065400303031181c1001070076581c10203142c096600b50802d108054000d402d0b08150f403440d08008014001500510000c215080d400140c4800c03400c0807140782000020703da604584030b55040101500c400b03040340741001030320b0310502442c9007a140141030591252400590318540c500501420b0755070b004072030703a80360070401c01042100d411009903000301e00c0c00c102d02e240d02d010390300e800c0d94080b0040e0009061006081c080108014001500d801d007a0302071005070010390b03105d041e04940141e04559860050300071000380019215111041c000604011360b8045d00b000c01c9240300010000309a01c428080911900e8410254420786403a001510b0b490400c1c0f0540e606103c410703034039a904024650f01800b0005240c240442050005000c0185914181c449032070300200010042c0d001941000c04c410300e0f00000003414035200c4111800300381d041d1111f1294081d10310b48018846c03100241c84020fa1201d416001c00511031100a00c41c41e0484400d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 988220746 1250 988219496 988219513
    0x50a0602030c0c06041d04060912031a030f1f09170301170102040b09010e240307020118120804081201081e0312040809010e03010f05090607180306110c0a05 69
    0x80340ca4800c58400c0b0f640501c40802c01800600c8010071003980900c04400511150340f21072a001006100b4248040e180340c905a60040404d589900465161801d6908a050800d01c000806840d0803108a14000c40da016502101161029498020300a510b1130b00000f0120071a850703241c442c0e42d44007040040a1400801403260700c3d0450004014514900c00841c203140c00e20349180b0311071041031a082d051202500d00e00c070a55980740c44040c1420380350905082400900024980360f5001aa6000055420030f181003da90700c20000c4c844402d038008000c0091420552010390309903201038400c2d103c54204000801078041a100a14028500040240003164030360401c1859251603c8040340303503400400100e00c4003180d03c162142c1041d085445181d94011400060b28680c0d040286503400d5400d1180d0704004029950240c1d00c2080300d542a04c025a442181c201d501942c21684a00d44604140c0c00f8008650264070560001440c101107516144940040d24580b83c0059021601507000819 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 988221996 1250 988220746 988220767
    0x180601080d080f09060105040f0204091a21030d02070807020a08030a03060906050108070e06160f0b0702031c0e0109020901121403090d0b09010f11030f010e040c140307050a060203 79
    0x21990004840844402a0900201303280e180c800c10711a113845140c03140b204284da81650740c1200c00800200c079040107400b00c0200001c1d0501034540966115a540c01d10b01c0503840d00280000001c1e143c2c1c00040c0d440c119007880042d00a4000d04002c0d40d4541092100c100161546c01c1e02d000600142c400661301d440749010010280c641603001000784500b03100c0b040100e640c02c1502e40b504543c0328103103039094080e4400480e44500417419a92001c2a0180304c48060140140303202000b1800b0341034008a03035441c1001a41d8903c00d0060441c610000c4090b50030100c201540148890b603d02c1c0004507030380e0000d030002480440282c010301c0c060306015517480304105c01d446e10407102403e50006142000f2902001548100000c0d1010300b24440301000100b902c002036001d5510310a001030104406041d0f0320b4604015041101e24450307442e422400403448650b90003030980300390b038404a041441804c02d0344480c0f00d00241e4580b0b030b425205840012030305a4a000602d00584820303030080d511801c0906 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 988223246 1250 988221996 988222007
    0xa0e070e09061608010506031e1003032c011b081801120908192c030d03050402060d0e39010903050a030302031b4e180601080d 56
    0x5080310705030040c064910840329003080c6100e0441b001228242c0d101d640710482400100c4c0c0302480c06981004443c01c0110140c031103450036050300c1c0241c1d180740ca40742009161000f0b25a240580b0822882c00c07003c036584642c0f05503018420711641a2101340c0035141e55642100c1c0341c1000144440714004138818039031369680103512000d42c806502c401d0101c0d18403521441c40612410140202100102d103901011502600c0c894034413522407003c6419103040001000040d5802d10403640c424018020201031043c07080c05001d003d5a00184082c0c03800034001041e0005043d41c90a201540c0500b00c0380c1d11003022041e0000c50341040b01c4a0680030840901000d42a440014612070305008001105202044c0005000d850650385400c0040c6c0d070381c46034024600841c00c1003608401500c03000510600d900010118040d8030002c40c101c1500400ca13540c101d00c020480b030102c0c0b15405964002e04102c407502c6039065a04541d05c65819022103208810981c145074090300111040c0d030180d2900c150b01c50348031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 988224496 1250 988223246 988223251
    0xc0605060603060d021c20033d06080d08010302030106120b04110d0b010b0414152b0f0227130b01021204030311010e070f030303050a0e070e0906 64
    0x80307901ca840c51420302d00041500c000d822019010318441000d07000722a045200d411209030b04424041e01c01d0b03007080898119001c10b207450078000e000b14410044455142d0058800c480000440d42c00e1044623919810304d12412000c013114a141c6400c000030b007000090118281b10002652000555811401490700391102640800a06402c03280400046914403d400d5042548170034441c5071440414000b82d82030b4504500904480b00300d60001070300e42508401441160407401100b400c0741548030400242c48404000084680401c1003c40c1250301d01d0748051004105500a010007102038105000c12900c1d0f8083c4184040d50006007000c00340740305030404101100c2e0401c034a802940041c08101507451000d45810050781b100c8008040760300900c660105409010703003403034030f039940e038100140000b04500c0c00040c1941303001080d9840700d20129051041c3e40005c085410080e1071642c0c102c00600b00103020a225603582e14801d0144c0c0c500703102000041048000702c01301401c0450b100350824401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 988225746 1250 988224496 988224499
    0x6120607050406120f0c0818060c072301021801030f0603081909091103061804170c07030501061203120204080a031409040501150e040e0601290a0c060506 68
    0x11410009026441812142582d49134038080702c0e140e0340c580000c400382440410301c4d040781e400d1548110005502160052154041d01c00e820086410403071038607100d09003520070002c400c40800000d8003080040040c0c5445102c3d0b1680f040003648005806401c80e0000314900070b0081d01545408000d6034140509280750348102b10802c14907186580d600c000b03208040c003001c0100c003001241410a03009161f22801085425000d201250b20b04e009a200c2d40e00c01c5400d18070a1001c170740c0c0c407000030001c1d5241318403650344010a02c1c04560302c04200c1e400c43d00a0303442c640845c8510711004c40021030a01481d0f005040c0040030072510500b84c03501030149500c101601c0e21584c4144000c0104000001e45581d490b901818810740c2c60071081c04c48045442171035200e9403c03c0c2000000a40a08006400312590545651340c9031142d041030204000c0c0c0706050074500440c2c0c0600c00612204031000650301c40b08007019015030101941c00036241c4150001444000800c212903a000140442800b0301640f041d030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 988226996 1250 988225746 988225753
    0x9260f030a1713111512010923040219030519032703060207020406120b010f05030d170907030506010e01060f09050102101109030a08070614010312052107080612 71
    0x3c1060702140003581d4407101070304080d0181e02000040d1155000d6160200c14030441540e1005031100301103086e0002c0c4074001c071031854034204507141100d00031400040300440720011030300d8541d902042040205084503d52010b111a00000042c60800c0800711250307124404000b1035a050070050300c0707031880400122101900c4003105030041041c04062098a62003080161141a20300228009004540001348009001c00140040c0180b0701a040d04071030304400c0d80c005085e00c401c245030316003280300700b07000124101e148011700c04104240e919034800f411004468510707940381c540903e094402e07440100a201d002e00144041584800049100100f50400b5a07540d4070b8040000c1d0344850942144071999900c1403400c48480d0120300321034000e00c00800b100e541d400d42d402c01d107100b94010503003280c143d850008040720b419400304560f4101c98000b8466004a183c40c00c0a8802e507104412440240c101c0c0070340100c0c107902c1e0242c6a405000709684a115511f40001400468014080624a0b070750 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 988228246 1250 988226996 988227001
    0x11041a032b170f07020102040905090a051b060f0f0d09080a030506060f0304201e0913082505100603300e060f03041217010609260f030a17 61
    0x400c0da9000340d04560050f825420640c2c541004038024004ca130003075840542084180f20030100d000403100200340c000c6040d1454005a5100c1d262019076020809070003c40c00e1000001d000b05038406082c0c4004441c0d011450442e155041808a0b034122004407580b483c08a55048113603414450203601c007000303076203442c5861582140d0f0509404020401050140c3e100d500744507481035060541386407800030f455080c1a044d18514081d0030f182c1044c1c07540c061200f003800204001d1010210310500307900101c150f40703440e5030041000d003071015810740040000c85040c60400010010170000c070b0308141d0b02c03c00045890540c508102c902c40480d85040f907183c440161000c1d0f0001c4e080d0210840d500c207082c41d048a00d071650110f91103000d41e908008024101100708028031a15003421800403410b039031002ca0351089107907403040c0710f6820701910002810000052242e200c01c80c0700031060009002500011520488165181111a000c801641c0c2c1000c00d560600603040708203909488030b40340086940e171 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 988229496 1250 988228246 988228277
    0x6020d050708190b0612091509010606030c0309020a06111f0f05070804020a3605180a050303010504150b1602100201091e1a01080c1c11041a032b 64
    0x240100115007130210b1b0301c04046002451f00f0080340c83d00b85105089064249001508140201824801c40700400d0804400b0301115100e4442c0e9a24180c0c01000d0562180c100341c8111031006030740d0000541d91181d115200c1002e60003e114030030718a1039000c04900414448440400d87e407001d012001485590005c1c8001030380c44074642000d40303864450360212060b41000c0f0701c02209581d940034011890848140024201b00e8110620402848000035502c007000e54005079a41b00040b00035159400510060225184c1604407605070500e0071041010580c40d44d801300d410b1f5100001d582050b050160811007181401007080f0b0440080e0300007086480b505403100d010440f207955a02141c0300382c200c0303403c0400400d074400394510b408003940b4129668440c01843c2d6100d1001c034101d0b215601c52030411a900349252101d064003a80316205030a110b0218003480060311242c9821221207050710310b800481e803801c02501c50726046a600381c00f1910640c1c02e1004e05083c1070003440c1d003003020040320303407a11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 988230746 1250 988229496 988229509
    0x4030303141e09012301080f07030201050f090a030c0605090103060519031113050103030804050f0109330c0512010803040e0414030d06060c03080702151306020d050708190b 76
    0x3609102480c40d00d0341d40e403c0426070041c00003085800342c1801048241c1503648515841c0b9050b03800d541c045440907030b45010490364074003080c07100a0000380f0030007142c9070a4551801412041300003500b000e01d05512940d0300303080c6404a82050000800205a00010350381c1401440c00074841542e007407069404542101c00f40000740c2c003020b425a0038082c000b0aa0f0340b80d0f99504100411210390820543d61640740c02014040107a80c00c3d52644140317072440c122202c06204004e4038940c041c00340007160054001b40d078082a400124014040000760304024074001c1405030210740c1045595080c0d50b0644ea4030180c03c0c0c200f060f00442107550045c80700b40540b011154040360095006900c01d5506140164964510f110304114205944d0402c0d00019503507030840c41484041e4802d40b03c284032aa50781c58101d0f501d02041c1c010000618048000c64926545108074140013400b6000262826002e00889030070b4480a4443d100090540010484401101445405074068160b8140004008040040caa = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 988231996 1250 988230746 988230781
    0xa120b011b0507090f0c080a020a051204031101110408012004260304181b21141305070b0f0d050604060306051807090b03120711060f0403030314 64
    0x401400c00030280e051040803c80c4038002e120a40040c002d90801d1310102001d0000e4108200129807150b0200703020840d54000d4903440d980701e544d0181802138403403110103010000b4000340c4c01d010010207180303105102030140000f44100c680c0c586a440307190140c20750031612100700038844002c9900341c10040b400d20208440444111020f1101c08502181420280f0840034613901d041d03100006002902c1094403510016811040d00c0030420407444407201b01102d120040c240002920061110045040c15040e01c003400003000000110000d0b03004c0c1d004032001050f030ba0810305001590f010800c1001c1000848080e014030080175003001144805101107000f0107400b40e0701c1c00e07115000144a6110307940100015a005001030001d42410f00314418074005640700c21405000f15200410f981c04c290180350358052010780148000f02e20074881d1012a004140304880100400c101e2014035560744015101d050034207c02a41d03502d265150240c03c450110300b0314007003030980d4410818962038100383d210 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 988233246 1250 988231996 988232027
    0x80a170c19060509060708040f0f03020c041a0a06030c02120904150b07060605030c011b080d05010305061008120a110106030b15190b0708220b0a120b01 67
    0x2512100c003009058140701c0d20004100307500900304050303002e01059400c1580101202c505070740aa40b00c0c40000c40d410300c0d0441e0050203025030707010700360002103041c1d811001443c002d106032030030810180001016540c2d0149a010b041504206100d03480c50020030309130040840d814100100d40c10600082e461b800c10304200b003024040841e201c407460711685c02c0180e0000a001e2420300c1d607501c56500c20f138160000102a2856840c1c00b0010400303003070000c0c80b44c101010586075088000c060290495440c0c884182c115a040000c0c02a00680d0005002c0d40f4043c51250018103075a2030000c0250b01035900d603503c80c016651100105070750081c03100c01103421001d01864421148a0001034150240244d6480202940c1e01d01c020448414401040c040791640308444440160010803010a1001161300500041f80c800700700b2003000449440042404404000c1011042c100f0844040080e00e032603445000c0c149400507202e04c0c4a80d0016043c1248c06034148104011103003000024082e150464040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 988234496 1250 988233246 988233293
    0x3090e04030909020708190e0a050d030e15030f1f0303050307020321100503010e060601030b1201050f0f130f0303240f060807020703030507150906050a060807080a 72
    0xd4149441200c10301c015282e40d0b841555a580e0078903180d903141c2d102100b504521500712081e403000703901c10f061650303911400604441c80c5508000800143d0846000d0403002d000b80780200344d00c1d5888030000b81c0b02c0003014a46050320703850030000300301c0000002031001d0f603c49a410311141544e21052294400d03a5010700d440c0d500c99070f5040c0181c0c80c6101e05080324010003049404000502901131809226218031070800c0412070343e4070241401d0b103240c5140011310360041400950554826030000340382010060041e280b85a12485003404c540c000e44005601c4803a4074100090b4400307801040d5003005200c0300f070800c0b1a91940f524210400540c100404158440748030044641c4d2010740c808030b4040c000c0c43e1046c1e181d41c40d00e2000c40076080340f0598004c140803800003040d0078008540794049940540740d01f4a0141c0c980e55112480034100b18400840d540d612080c4080758840c490342c0c8c8903a00400c800100203003003041d6a0300d0003016900080c400d030300600348040020300b42a0308140fa0f0704000e050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 988235746 1250 988234496 988234501
    0x6070810080a0f0212010f0506130606120e0a1203060e1012061d1f20070f06020418020705010b040c1407020a0b07050703060b060712050901090e0c07020a05090403090e 74
    0xa40f090300f0300107055034071b5800e0070394a01000781d07558440c5015100c1241c0d0a6009488141801d094403540e10500c008200d5032182e440001d10f4517049025100c0300d410036610400003558600c800020829161030009944072002c1c88884041c00c1416007203440e44c030004681c00e01d8506441c81c09912440024082521807412402e030648040e84049d030307214040b05903409070b0150990f180500c064401c0e01c1c920181090303c0c1e6641040e6140451100054512003d8502036031038030b8101007044c42507821030b02a03508010016a000b07001090420240301c1c2d00f00560f0b5a52a820550309444120042e01c0c810752910217001301c820f41005905200b941c0301c511850b210308090001a08414450303014902e44080014900d080050114014081d04c0c4a060104003a035110b90904c0a6030240002c000d0100c0461402000c4460288002c1c1c8440f4505151220704140c4843d14076044200030f81e814182004041400307011464014000400392105554020303d515058500800f02851807048c6241c2e070041201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 988236996 1250 988235746 988235749
    0x6080a061a04290c030901080a14011208040b040902040302040f062106020f0a0305060a0603090b0408180d0501021306051810050708030f040c06171602010f0e06070810080a0f02 78
    0x1101c88140f03c82441e5074542c01c4491000c0e890354070401d1660b00041e0381a00094074219584201d164403c0300040d000f059a0034050030070340c00009110280e60800d024000020258200001840a46000c1d40050784951652041c0801d4400c251200c12034142041820710841295080d0f662800008031500e000f22002802d01030000e103c2c24072145500000042d0010040b9096007016000311810381d50319101c0741d45c0e0700003201101c14600c0000d014060180103d00800c0000c000361041d900340c43e60610f09200c00500080c3c00c4400140c08982594010071102d24400042030020002d001504269142c512001e20351100703082c1402e0b000380301d5031100c0028101284140305640620354480155a40ca040c542d0000300200d1084404685000c56a840813500c20b11900400c1c41450301e003070010381c0d640c0302c215185007985003101c0c0c644210342d40d801358400541154006e540c008028000940190b0400060041c040c0704000c0003a05150310703508080140140c009005002d4642000c68541245614070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 988238246 1250 988236996 988237049
    0x11101091a060105300f16030203060a051e010305010f0501080126070b0d183207091d030307020d0521040605061f17060d0b0106080a061a04 62
    0x58103001401407001d41440401c0788840355810b003a03184105071030359a4000d10860614048440307101c103d1201f10a220401c0c0250051130300700350000c01c0c034014543c0320400304020002504d5500c500413800800c40603507580610405025101c10758070040203906250002e0300a103010b100f44c803d402c1d05020203820030200c00e07109900f070b0403182058400480e955802c0038400c0e0850800d1410311440c0c80c5c5c00c52000d4048980328040709902c645011035050824000c40f00c54251082c81110381c800c1e8a41d0040009000d02c4188007070316401600043d0585013492420691004803030381c00c545c0e0f00410601c90b40540010302412400524a800c40e600e010041103e0301310700900c1d512034200294001070104005407a001140f26450035900e90054050b02c0005074880c280c80713100e40340460541ea54007c9500511070440351300020160200d000c0c0c0744503507110000000243e0000700080d100b1014851480b880707005100c000c00b20403e80003100800c0a601130110720491140c0c0c68060180b114000a414414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 988239496 1250 988238246 988238257
    0x4051005090c39031804020306030106050a120c0509070801051002120406030207050f060c090d020a1a03070f0503091c180314070504020f1b0f030a0905011101091a060105 75
    0x442182c1006114903207103031080440c4040b00c1d071220b03a51100403c62804004140c4045440b00a1070382d40c1d4455039418840207500c040c140d540c0654964001103016180e1150780300c024085c070394400c8074480a40c00c05504e0b201841c1c06c003610664000c800e011072907a1060b9028190381003210708206407101200c05a151111315038040f28120380c00b003070005050340c1640c040c10200780130b5820340b5040c8400b105c445442301411150500300e80c43c14031400c015030903c103210164252003e040c602c03441c1c0e2607115000803115201080300940c0400010407440650102c00900b00003824246641181810f459940d1591000d112aa405003448486600030620031883c0f041e1200c003841182d10250784038100b052054802d10112009442503050004042c06e107442100c80043c03119000760b080044a21040200c0c00102d18048500d1040707280901c0401c0040c00106403128241d00d030a640d903884c0c14000761403604a24401d1480f64540302040010034901000360401c2a1600703143c1402c1e668980040c0c0b55030284 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 988240746 1250 988239496 988239517
    0x1050114070b070f080705120a1e2a0801080c0103021305060a08100f0317090312040b040807120206160201020712080915042102011b05061504051005090c 68
    0x202c2d061001403900f100b41c0c407980415990f01e4a03402da4410383c0950300c40c07241d40704440800c0406400280420440d60240001203038196151064035181d080c94400e0792000c000c40307417031030003641d4550b4110b0140b542e59000c226604c0c200b0304a1585006a00c13a215501e030f010440c14180c0020307a03e44500781081200c0080d110082150741c440c068041d0040001c2d0302203c3c544041c000c0158081110519860081c0440ea030140b2201511024005a40da46801003144190184510208402148450400b82001c1c0000d041d00350744079460320705040c0c17505178158407504034100c0c041421400350b202e9030210390b48070100c90048041303640c2c1840100e00d04ac0003640126110480c110200d000c01a0107001000070180c12201516120031072003d40361540f01c1d0384100034104090b1b200360030002c03844010741d800f42401410100075101c0c2c02000300c0980680c01c84201c50395080b8004100c8005a83c480c0e401007170300d0a440412003440c00c1e420b50786050f0784030b01070248248182000101007150405c204c850030040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 988241996 1250 988240746 988240763
    0xf0304030e0103060e06061b0f01020412030f05180603060111030d02090108011d0106110c03191e1101050c01090f03110d0c08040e0711010903051b0a0206030105011407 74
    0x2014280240544000040c0500280c24010001289000c00c192180990030040600b8605000e440492404000e00c0d00d180c41e040c02402d400060300316081c8041c0005042502c518584e0f02c55616004000402e0f01d100d20b018410107118800c2c030032600c0d03080f00b0320081cac05858840e47813901d4510050760004c281d1841e002052100041d5224030052580191100c1d0341d082e00c1e4a805a601c82c4a0f060440310a1003c000039072124200400641c0e1043c01041700d266089800c1e64090314000002c03d0404020318146103d07044012084410000d071491891004091540c9000f05802c00c0c0c0d0390000c650320f10380c0ca003c0c10020003040d009001d030f00c01c2d031000702c0403035004d00c5910b218803a46c60302078200d030520520042d050003100d052a02d000d0040f142941e0345079100c00c2e5030780b400c2e0500444500611024000b481000304800f01e0f0702c0f03810024402c2000d0b8034000c0e1038503511740903408410b48170742e40c07500d40400e05500300c00c1000340140c580009980c151982400c210311203491120340e4076038074054400041d02040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 988243246 1250 988241996 988242001
    0xf030702040902010c0204151406040b091c080a020601031a090a0b100b0315040507110703060c11030a021b04020a12051b1c0c030204082d01020d060510020c01021e030f03 75
    0x4232905516000ca40c0d015a020741e1400250003040002d0080d8030514400b0341080140180c14580450b54400300b900f08642017510843e507486041550700014101070243e4000c50045c4140482c0600c0400b0b00111700348801e400740707041620741d602d070302e00b08074020882c0c000c3d070020400403c06c0703420f101c001d480502e55441e100e141440c0b4080d103500d034aa0045001e1407070305001c585d031b03640309103440100c41240078010980c091450f0b68101c003e201c01c00c202810011040500340001505100410300f061269008010381c40004510b281c24100011440780715900c10007401d0a0b15410607034044070302c06141b50010b402d40da005a4034200700c00e03400c2d0030007110703000080032070b03904041060381c0c02d520301c0294082012282034007054040340301e00d0055108c241d020440000143c5403001203c0340c413414030007480c0d0b8540d0400384100e003a84c0144030007140345503c1707080c24043c0d070800c00126000042c55200030400c154010002130340300c0905910300c00c20000501702c1d00c80f045004204030754071000e1528565580e417 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 988244496 1250 988243246 988243271
    0x606020c3307060506041103130618080a03050711120d06090e03040f061407061802062125050c0a0b010b091801060e0609010306090903020606120f030702040902010c0204 75
    0x25400950221030b0b2911301000b28101e0704042c4200c2c00304445240c20350f4a10f88400507070501e08482c02d0021582a9150034000500c0b0203001c41c0344183c0b0703118034812603c440c10040040c003a94402003034002041806e080d040d05050001030600f194040da21038407551400308803240c1e4094407503a00164002030800500280440c4000010012100854810340c8803e440d81c2d000c482c00425091500c54403c2c050103040f02140c0c4a51200c01001804040f00e030590f02181c1c082081900683c41910111994044418104034003412059000d440072018212800101e056182c0c6043d0a05002007001380c0030901e00000081003004400c4a900081c01c01d07601c0d07945442c0e1454035803080234a0303401200f055004080c01080122218184e034215103d03410480210320034415590014510383d810507403261000140c0502d01d03c61403403514080e601420340c0d4502601030109444503104022032a5008520305030781c00c40080203503001142e04407404142007603d0300040b03071101d070310350006075100e444c214140684 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 988245746 1250 988244496 988244599
    0x30b0d1406091c0e0d0230010203090a0f05190602041401022406010905040905030d0516080c0a1403090705010207050a12020402090a0b07140606040606020c 69
    0x2035a10344001c580300ca0362010160740c2c862412986841d02d07811200380c0c45210138099454807032107240180c940300502c845d41d0002540740d0381ca102c45201c0c015005088001c0c140403402c140c40001d4524009601d1400d04012070b60380c8040c54070011307226040c100542401c000091140c3c070451142012005902804c60514000075031042c41640251400c00014252950002c40c0310b03c2c00d0718000440c02c102e0600900360302d801240041030141001062714012450340c0d074601c9007240090042c80215114025008601c085500151584500004410510b1500e960103e9840c0d80050400e800c2e6171140190481903500944a5800d4400d01da800302c2000b581d01300000e040e2049a0090742100d10b80b40c3e40d03209001a408440c00f642da0f1204a2481c1d10000d03091980081080101c007811140c80d49680c0c14501581ea00b00280466609815034101004900704015440e048202210100101840d040010307540782c05102150303016032800c00403068100c20030011306800103041d859103000a00d4503803400c0300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 988246996 1250 988245746 988245773
    0x60509040602091807050304060b0103060b0c0309030c04090c0603020c01090c06080f0f0702031e040b04151e09051228200d030c08090d030309020420030a0903030b0d 73
    0x556180d14052401c1c03900d2404c00d0780140f949480c0e0f00c1c50b54440340c84180207011403810303484c18562150400510000300c035004103100c1701084051501c0e10500c07010581459403c6003203d10039805c015035200400c0d0116454800c980d040e00300140da0700b0000c801c503409002c480b80042c02d44020b0800016804d40c02c1030752984201003d0008000d2591180031401c8040c1e01a00c0c2403006903c240b00a008a100d12200e0001c0c48610018550038a0f540e60380e15149a0b00c16004a59100b000e040c2c1c03015500e4105100b0300c0301d102c14045100d00002d00300c0b07000700b0010300c40c41454410407030201480b0501600344100d2006414151215128059400044404902d800070813123800a5807440c1140103441010741d41c000c080010005004282c0c662801c0310082c51200d8295035003d020080591030b5a180016000388034802e840100c0e90f6546401080101d51041039020f140c0d070101002c044030044504100c2e03611a0805000158241060408400a0612500003504441c1c01d00243c421b00100003880903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 988248246 1250 988246996 988246999
    0x1603022103160201090503031605071401020a20060403030209040207020a080601051005070507030212030c010c0915211802030a0506150a0f0513022808090304060813030306050904060209 82
    0x2484001c10b40300320b0880c3c240c00d00203802a00103201003032040c01b441140903898085441d09508002064480f40e503c20400c400c0619141e500098002c901c5820048400e001e0211004405001283c10b02c00e81e00c03020010300007020107500180c00c40b000e0383c803541502c5401d81c028080b54002c80d110440c8030f581d48030a020f0342d403190700c0d00e02c1d41c015010310600440d540640e0100280007007520315800d214000303203441403110003408144444083d881013445520840291580e40e41e200d42d1070b0450800c207220769945081d0400909015030729840302c1400700801d50841481000034a9039006e83c56622200164400950502030302c3d03039801c14840006103103401040000400d402c21150582003141c00c0455104001d081e20b510b500801c810714219003d01072240000d1005880c0c0707480e883c44420300c1407081c1258081e850844010701000e0750320660480e0310540990007140340c142401409003014800400c41d4980b135140d24000310405d032103500404001d21020705596001d08142c508003019400407046035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 988249496 1250 988248246 988248271
    0x40315020c161a070f0204020c0c421204021906021f021603030c0e1c05100e03070f08042711042301020a0b090d1202030c1603022103 59
    0x80084003c1008403000d240d80308007400c1c1002015030030300003c0d4003d101000100e001c1c00340a0b00349915048610101c0c000c00c0d15200e80414000000c4c0214100309260960764145421a54030341071105501b21101d801403c0e201400131303912071001940071104103c006030220b00141d03001030507074bc0000d0071101540c0c6014580104101c1d03204043e040703000d40f1a6040041c4020b41d5031401007402980201c1c00c140145c40c11410009a46000c102030520510201c1003000e59512004280304043c00320a030202022141440b161001d03120712683c0b40191080038260b003001c0000001002003d9040342e00424050b26170982007118060011007201d400300400b0a1542000d20b42c0070a020b016003180c094641a40803140c03130075040f100c0030084095a00b007a078158030030a8448404242d400840c2c40c1701d612210001c1035210f0307030040c0081a03048141c401592050051044c400600802d03c182d0380c5241c0032211801c4000c6c0c003400c0c201c1c5002e04071540120383d40c052000c0b4440751034080307000b036100394101c0b89017 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 988250746 1250 988249496 988249529
    0x12010e011e1104030210123204020a14040906060b19030e060705032a09130b0d080703120203010305160e06091b120f010e130305040315020c16 63
    0x100301c240c03070b03054801c2c01445808000034001860b000a1403488124039142500081078002c0104080b1084040858082d118140002003074503256580c0034511440e80300414464103156001c600542183e004920064883e0300264400c0d0310750b0b61003010b030300c0c1d004141808003a1343e034201d009407030348170f9403500004d51139540010812a00900401441e001d401c0024034065440210459103034101600705807210429844a1586019402065844201080c0070543e2580010100020941c2d0402079480b15828140c52080303c2c0d45640090901640000001c0d075140850300d021100c940c000303540c0842d82440803001200348080060150319854210341021001926404410514081222201e40c81544000015107506205a0302c940a04881e1003107810324803e0268104c02240c115060031040d50341000400c14440740300c03910754011081c074a400740f440c81c5a803402040c0c0e100d540409001b01256696550505040d0340c112100f48001000351130411054240c54407125010b8442c92101c011101003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 988251996 1250 988250746 988250801
    0xf0601111203151c0605070e030a0309030f02010c0512030402030d0305090a0213020415031a0a06140a210e0c12030423040915063212010e01 62
    0x140002456841c9080c24259a544000c0c0b8441100e02012103802400f81d404041326920089424101103114002c0800c1e149813084001300044102202c5500c40d50000351180d02003a00905500141ca40091001810341c4941c00141c1e102c250b0440003c01522680c01000d0b0b41907200c402443c00340c0e108070190380d0b074950600c20840079a42c1c19200c0c00b00c41d1f0004d00c06200140f030509a1084000d280e00c2c3c0c00360a02d80c0d640420030142c02c0c43d640c0035000c252141a00c0305040c40340010070802e85000c4529222590618078014180010f4040c2040b00d40300001c1e942d01c920b400340d449040d08490400311111110f542442040c05000403941c0b00c0204c0c85010800441d52920000e0100c01c03020400c0210305143c03505a1080c0000c221000c01004550300303402c192191b8030b42d80940352001d0302421441503203481c500041030854400303030f0104955105086404015440e816065500d909103604000341000354800090042061a240740c90298640880c44040c88010341040c0b030001046080ca9050314400c80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 988253246 1250 988251996 988252003
    0x2130518071e210e010c020c01030b180408180405011d0702062e080f07081c0804140c0d120912152004030b01030209010b1908150402030f060111 64
    0x80b00b80481c400c1c0c1d003030b0481400c0c00350340000a5052003001082c41a110a09142150600039840006070024a007440195804d4001c817141c00c1c80a0b20704140c103401d01c0395210043c940181004200500004003894080400195080380c00c800610030040b0396914254002c1500c0e51034103820501c482400000c82c2a030010403640d1040c00440501c00b9a40030341c1d4100f03006004001c8100d008a03100d0003000c11074000070001c006030f51a1840003040000d080400e55441e0001c0002141884030740031031145811030780710f140c03142c206507c80241810302d04018442070400559180c042d410540300078800d024421801409070004655485000b4541c1d100e20409420703081003800a0420a21030805131603014545d48404001501d54a0110030803880a03e68041d551060744295010140307100180203620704650080c0c018100400c0729450605082c42c5490b905206260420920890300c0014240030281d4004442642e4000c004547c0e0b890b1010420744125415a00c050014603140860080e092000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 988254496 1250 988253246 988253297
    0x80d050d050a05100b0306030304080111040602280f03090b070b1503030a05181203040303050309010f0501051012060906121a0408031b04120b07120c050d0213051807 73
    0x2603c0900f055007481c07103080040c6c3c000f40410390107200070040050b80c60800c1c4a0034806100c0b503140c01e90b0300c501e0400300a28000c101f10040300020001c1040703107049403c2039032100029500018804a20f101424280c541002a602152040d6400a1001c080001000603284100c603001804148010f42e003040c950b5a003e544c07244004204200107c000c0341c3c130700b40ca8410011070000c0c030001074012584c4102d41190010f60007240840ea010092000d6035000380140c103000311444200f00b1156241c50000f070700c0c03c0c94441042c400c1c054613400594550380b07143c0001d000750030248028480180c3c0c6007800e40c6100a40401034a41000b08100c1b0641e2070102030000b8003403a0081c07a1241540c41c2c1b1a09088181e03410400c00c2c2480d14104030000f02c3d41000355610b5142c5000f41c0e03001401d440c0c070078805005403821122070745480e441d100d44c2080c0103801900340c0304c900780780358001a1030315002068220034503543d07004544d02c00c025804254150200c0a88544034040f07998074462105001c0ca0100da10301c03404d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 988255746 1250 988254496 988254511
    0xb1918140603180a0f14120406050d060918031202030f061903120309060507020c03120c070302152205030709050a23060f1e040207020307080d050d050a05 68
    0x30000d0051494034001854000c85640740712601c03503249840c3c4501d01502400102d40103003c00603200140300b000092250f034000c2caa000740c01e5403050013510200d02d1081d8012001070020200705003241e12071541c0410b001e84007520081046000b107103c140c3c007040561030101c00150380d03036190b201440d44038000e403070142c0c2030070020000588481040010740b031248401c01080f000c1d0880f0010110f964801c24402d44241d0303441c001049907107810b0010079210300508520566120801100c0f2640b000201106030908103154203454204d02048981072644d02d92000e54041c090340b20610280e074001d4000e0a01100701c40c247e8054141c1c0706603202010f100303071281ca82e144e040300c10108081c4100390842035004800301340000d80d100e0002840701e40c8880350101e820090034007608001d00c60502880360440208101c5454101c40c046840701c0c144039041c3c05003580030f6a008101001191410001e4502500b280000d407071406002100c010180e40100314802c10385410000410b01500c0e00c6c2c03240310700450382d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 988256996 1250 988255746 988255769
    0x501081e03090604120305070b10030c080d020a030320030c0c060f0919021c0c060905042f0c1e060c1809062b050c04290a0b1918 57
    0x207803c55918210b0300741c400690a1200230030020000030ba043d03031124410001c80c011105254114108244442c07102c7d04480b5195204a180b440c21030740014070403442c140d16103004152101041252030546400055001074441d0210a200b0140d01e0f44000d07060a21000c8122515a079070440d50200101040d0f42400d480d42040c40300d00f0a100d8042d1030300c50700c140044d25241a102500d00307501c048010400084e1000001154148101d0b50f2150080300100030442e0184600d1414205405450f0342150701c49090140001d29000100d010006645280c0e0304c01054900b440c22401d20081f1a0310340854220b420300610f80003c0103c0d0440c0140c0d2000c4890040915002400c5000e0040c26400502200c1d400200031604141c134402070403a80400c0e58091410200340381315440c0c2545060b1803040d143d0710a50a00d49420a00030031300039a41e400b00680c210f071601900c1a00c0c007040796040e89410522482e0b0001a014107103d280320910303550549503070303a030b03941e62440c224412003a070282d80110402d444 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 988258246 1250 988256996 988256999
    0xf18040b0403030605060a030b1003050c0d0e190c0614030f180709360f08031807062a11010f0306050301090b010e011401120203040302100501081e03090604 69
    0xa1440301030a07030061090900096280d19803000a50540040f602e1200080d200c1c0d030070008a040140141e01100d219040600450a1000340080903000e40918002d07c25643c0104c2d22000804201070300403c02c56004d040301420032420010340c201068084c40c4041005003000d241c0882d0304404980c828096005920341030b440d001ea0030300202e4404c07030105015202d40c000100e140c0c0744078404d510031540300c0010800c809a92081c400d0411072200c40340c00a42030b003d81c040c0c6c08140005440151240c0c0f14010903640e580d407400d015000502c800b5648800c0c41414000f2448c1034004540078078140c1800d04220600e00728116038903140940f620000c10100749c2c0c99815245502500c0721284289440c10b020030340e20b4545001c00d00312245103200b03a44448082004008103150000381d1800341c145044039100703031094040040c000c010082140400a03a001001405140c424000030070aa00607400a000d696940d088440d0f03100094490203091f12002030b00144850000012601e4040d0040c0181c0e0030309 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 988259496 1250 988258246 988258253
    0x51009080a03270608011e0311100507290f13020f030f0f0706031b0f21140702010f0c0e06220e04051b010206060919090b060f1804 58
    0x81d01103004a943c0a00d031000b80c01003101d00f43d4420342c043c0c9410b83c1d80071025072400f0150b200c44141003c40d0000d8101a42080c00407811914066481e000700f51801001c0b4120340200301c80e18890040c0c0a895901148208046145031181c0700916881021840e20701e0340b20020003040b040001d0b914030f50b503823070030314401001418282d00940c00a41e004080e140644511001c2504210300d5420f4013080390032141c0103100c81601440b850500b170700101402c501e201c22107503010701942041e4440c01c040c080c411401c0341e220450014034645d0400c1403802800903142d00580c45c03003401019140348015500b01880708920302914072030a00c0900c0300390390303544808920209024142c0e01c100c921056509150140088403d01c1440b140001e00042080c5c8a452415080850070072507160041300d10110440c0014036140c0c0d000070116040703c82210b001c5107a031102c09003950b0072140c410005a02c10b0806d0f02140c14007903079a51481c460304042c8c8044504168050400401e0a410031000104081e45d01c0401d010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 988260746 1250 988259496 988259507
    0x90901051c02120106121b0803030c03011a1327020c030403151b0c030207290a020a0204050c0d2f07030c021c0515160e01020a0219051009080a03 64
    0x61100700f00000f6005485505052201900031810380d007813441d103c1408200c0003201030850041c9500d1001e54154100703044e1202079880306108032004044547d0b40c038140c4100c1d15007118503040e0700703c59a01e030f0030342c0d00c514150065495104071002209880c1d5240320000c01802140d400340d624001071803401d0309640d10303042e20000140188405660764210012217051420407140c0f500c20380d03142c904c410419032a0007450918680c20031815003072200b126000c1107130400b505000180000340041d4603403c109100700d140200785007020354014200800e005c90209a000204046032129505028814407908644c4686c0903110b60031800b00034203034014110b0001d001c081c103040340c403a180980c2e401c000c03a000900c1d00c0040c15209440211203082d220100402000780c014000c1e5983e2504c0090f08d401003080c01e081c00c034016141e0501c1015003005520380c1c424010856659801064803041c08510140504140c03858061355010784041c0d5000c501250040c080c000403509004010000b000a41e41c040300c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 988261996 1250 988260746 988260769
    0x611010912051606060e24030303070f4107050a080901110318130515010f0215010b030702070605070b2d0403030b010e010314060402071a0408090901051c02 69
    0x20810f0480880300006100d40c09410010400d440a0301c8a5052800e00480421a08a03001c1d5242070440701c0710760241c401000740c95200d41c0d6030420500c9189141e000303807904003070b814000c490b100c6060407010000110118070030a181c0d02d00d2611701180048440c03800d240c8500d2202501b6540159421400141c41c40001c1000d0101032410050307800ca000d07000d92460700004040c2c0d400800e14a10100ca03420403031461405805401000d221038200344445c12800c003540102d180c100028100749845043c020404c08680d03445a0121780c00541c6c1d40c0d1005162900240c0b203220050003804400940da038407070b2099039845c40d08031000302c0107034907100c6107106843da03c082007440050f401107030848440d914407411480b5a0081e10042050701d203010005007085004540103043c5854911000308106c9842000703a44044140c4005982d4511410101090540030000890b40c0c0d80380d0b4108001c12150b40c01500564006071a401540c0c0d0300ca600708194042501820308286c0143c078025000361a20503848207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 988263246 1250 988261996 988262017
    0x60d020109031e17030a0c080118270b060307060f0909180b090102070b0c040605090906030a0606031208091504120e03100b12010b0d02062809061101091205 69
    0x42000c901c03943c4181050000ca0600c0710500b6010040010f4074540380285803c0c00001e2900941c0c2e90705028490000385a10b003908100c15a2f200c09c1554000281c00085401540e60101c2d9124420640b030721045056003140d469000c0d01444000044160045046402e450b007140c40b400700300380c14403030041c4c01004151955a0000d400841c0d850108203001a1940224240000560b0320f00e01400d01d0701080d074004d0802d2081c030100704000c00038603038403000b9a51030036000c4600c0b4085489200000e4038100e000303040501200c0c40c010b40041000a540b0038038100c510f65842c3d40d0304c59902c0c45650360700c51b0b41c00941c48a4441c5d0110004000820401044807000180e040111980400502113444c00d03041e104812400e540d0350349114807528203c02100000e4482600a120310f41c1d8040200d40c03102c400483c028011540070450050034140700c201110103d040c00145440c064007101c00a0805600e44602004a05450f03c00b200c1c1c2c00c41030040c17000c6c040e00103540000010091608580702d900050101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 988264496 1250 988263246 988263293
    0xf0f020c0904030e0108100602030d020a200601030311030c0703032001050708220807020d021518181e0a0e19020a0b0307170a11120906060d02010903 66
    0x8980c940d91801018040c5002c1d6940c50110f0301140000340003840060b0110540b16001c8000f001620790000403140728040b54503001da22000d442e01d0076074010302000d00240070071900c1e030440e2450b0303a80003540740c0c100e900a54405c080400c180e00c429499101d070240a5805070091a81407012a000e260310002c00c020484003001800540b02032942112070640700d50300040c00710303401e00c80030f0390000484a1244006030300030010807505030380b0501c1601c034050000780120a080c10400c2595600900b80c000c10826281030b599038070b0064150f40d4a62090500144600004094a140d82c5005036032284500396031b4540c803021500500d5140e520310001024101015190100d54590100500c842c0d000078003001c1c260712001c60340b44100032651047d85c00c807081201041c0100686a40e0140c81035405e0100c00500742d0203611000c44c108040c0c15004504001d10300006401031542140385503881c4110140000c2e10140c0d1a2142040070794040c80070301900103902e880d0140046441d0010a026981200d11030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 988265746 1250 988264496 988264513
    0x180606070809060c1e16091112010305030322082209090c150f080a0f0609050c13080d1d0a0302120a20010507260c100b0f010f0f02 58
    0xe00e09a00c04198400c182c1c10000c0104001c0c1070390003824141d400ca41d0b01901c8006e42d48501d4101c04800d901c1142c0e00c140d200c0101030201101c0000b1601501141101c1c06110368680c108956a64410317030ba0103103900d00b0100014820345004124440b42a881400c3c281307000220f0b440007114001d144582c00400c480c01c003000a8a4856110783d90f901c82c8540000c44603a4a09201b103165100c0011100c0244a44002e00f030a24543c042c40c15903206221500008035410b5030450302009245582200c801507140c6010b1048038160180508070741240d10101d86907480d02e8007012910b66000086000104072520081e10055030f111480641d20f05015196042c2d0a641e80c0002e0700080e1340360000403050704202e50000602a0b5003550041d4030042e519078500c107502041c0024414490040c0182071203400001d11960075041c411008441a0b402d01c242d52030b100640b45a070344034144c1004804005283c0031064000d801d001a5001074040141c407030020391101513005449078002c034200d0038214001d030141c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 988266996 1250 988265746 988265749
    0x30c1404061211090901030b0403020703230c0a060509060715050106050703020f0d120c020f0109060e0114060d0b0603030c01020a030b040b030604231006090f0506180606070809 78
    0x10300010001035442101d5540401c00c08030481c0c0d5818214000d00004008840403034840200050450380c0c0548000703120b542e2414201d05004c017641008055840010305a00a81d8003904a01c1046008000341c4610038846010800340004610559000c50001e102c4082c0d2480c140700274100090081403c84840304d0007007803a00840d2f00c260070041c04184003003401410303d07a040201c40c0301801c030803004000e03440740c0f5500a4451103015006000283d181d503a040c003e00c1c82800b484003110450700080c4412802d81c5840d002038090004207410720340c0381c500900c8002c40e0000329a4005c000103024081141c4541e218071010406c000c0c030054140c44200101d103c035940034401403031661340c41d40d0001800300764030041205031640c0d010218403960140d824031022480601e01040045004640c2c1820031030700e51925801c0200b103000d00c3e03001c44d14056001030034602c95000030340080e04c421001c021503502c1c84c0402003030020411604c4080800300b40003822a0503c1ca00900340c85010380d280c2ea0400c00c8950 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 988268246 1250 988266996 988267037
    0x30e04020a230703180e0a1d0616020d0314060d0503161b0b0408030306131b03060e01092a0c2003010b031f090c0806010b0c061510030c 60
    0x11015104000c0000310705082c0340e4017030411400000c5245403403040c1894010111524031016090380034030381d61100303810f400b40b2119000f0a03200c40e07000255145490300ca10381514940004190b8005070045405081005120703108220004e03240300c4602009448420503c9a8220941400ca41a1004110004006040140140013184075115200786460240464030011800d5480511703400418031080c40488404000d480d4010303c00d0700c104048510758003000010b4090803010011880b18040040315055040e00010199191030900318944d0340d0b6580c000044425404801c41e922400404d50b000e49450581a4141d06107103141c83c84d4500c525407925034a0081d4a800120b02000070110001c480c1002e0050050000040b005400d125500d00745800508103001c60242d14035545040030810003000650310710240029900300c0d001c5607100d91420029030300c201e1100586118550000c0c58264286280d80341e000b001074500361884a609605402410b2030304010303018800065020991740d503200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 988269496 1250 988268246 988268297
    0xb280c053327100c0801060804020f130e0a02041505030d050309032709060d0c1703040e09010207051e030d0e03160c060311040503151806150913030e04020a 69
    0xc000b5020300c16104012108031341c8141008824410004010040503410040c050b0b0f01907010b9038003400c54032180b4001440740320081540c4000704d2400118000c003c0c40019022000d034420b690070000c0050480d1542041190740c40ac07680d041c1d01401c480d0040d64882c1001d16000030051003281c2c1419940052000405040380a2510501541003d08400c0c5401d1400a403c42401d8910140950264444280007040c4d1300402c90b414048410841d0505010421107008080c0352408010f03908100e42594041d50015005858500c01c003c02500e403070f83d2941c08011185035590003145030080f0030420b140600052581148103000c188003000c4105004c1105074030040c415a088600f00341004070140854004420185880380e0920040c0881e440000c6c4a0f2085800058444860b6661004030481034008524594403800760000b0701824030242c1000355002c60086604104540d0740d00c0740094030100c031300f0001e00001e0301070002c201c0d02d09190b0300600003c00e081c0340a07680407540030f01d44039018406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 988270746 1250 988269496 988269571
    0x5060f071101090e07050703030516020a170c0304030b010f0e090307110a05060a11070b090f090408090a090e0c0609180615120f0a020a08010b280c0533 67
    0x130310801010340c140b0444be441009095540b810a01030b000003540c3c0c4cd0a508010000441ea40f1030700205078071101510082050320040304c1e6115101c1c900380110076001e00c02d032000c0121803400400e0407006585054855003400000358140110303030319240085d08100c20083d800081240e804150390300d80c80001c0142104a07181c00865140b40d28103d482c0c004164000c0c081c000c0140b140c03180b1a50350311004240100c0c21140d2001d01e4031a030402c41c11030710800c60b209078070104100c8001200445032700001c00e419075200984082f030804c43c00307000c5c491007104926035011048141044030003a050703443c150018000350605007003008034540c02025034480b1049a01c0d0001440401c9100d19002d262154030a2100c041075041059554004d804150180281f5140c500c001c05c0007142e00c0b0382d50340c10394503c4400300c0003500205005000a041003190080c107903018020045903c465000302c42511840003a4201180501540755248480d11407025102d00e9030064600ea800b07a020190a040ca81401032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 988271996 1250 988270746 988270757
    0xc03230a0b0913050705010306050102250e071809050f0c072d0b06060405061e0d0207060b010e0411090409031107080105090f1c2f100605060f071101090e07 69
    0x1081c0c10702615048042c2c6c0000e04160a242080c84107036404125000d039480413a0603030014194003007500f010b001080d00030700074421842080196080d845020740c12001c0b00d1192a41c44140c0f161602e0041d90402c0380d03888860100607001c100c00d002c0010003406080e000d9518040c50840e041000742d000d1a5540414940590f20203900c42030010100c0700d80c0e0440c1c03040703501a28043c540804034040307000324001440120b84509090b0112441d510485403a40d00b8094211b541d5183c510740200100002d58186000030410f02d00511242041d104080e06a0755000c10385017407600320342c01c02002e4030b0090f50031020495801c00024009104002c504050039414001150500d00b4020a40c54070380c4144001005d980881440700e500b40740c14403000d01d95502403900700c0030f0030f040ea481e14812054540ca002114481015000300b9848007040401c41c2e0124010140310700c0d0303640c0e01000118018458442e0300404100301480008220360b500500341c200c181820b01c44a656545d075062140d01c02c80d050000f094 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 988273246 1250 988271996 988272031
    0x20a09020d062306090102070324050601030c09270203180609030f0a03110f0d15080109020105040e0a0e1204152a080f04090e010c03230a0b09 63
    0x214022000a041d06581d5100f9600208482c0c6200c0004069014050040042d0303040440e4402e2000a0103190480c980c0d44040301e00c031000c64040400c038500b2142003440c0c1800329501e58444d0180c10000f00d41a540e500e5014141802c00034101c04a0803a489500388803002aa4182c0f49800a1131080b4800f010044c110b03411340013041e040140041600c1c007250002c00586111080e540c00703540800c0418980044d03201003000440400384100c1400b8158003d012130510703c0d402154005400409220304a0002c10341c0d40d4003090709940e05004001c0c0428824841131105020040d0740d2903014411080100300c030b800c0d1a91213420a000300800403401d02000500f40524002002d1400c003244091411881700540c01c1e400207925007500050740700c80c043c1070580380f0a100c450000c0d511806560546241c0e107982e0303024110b00511940c80d142c0f040b94241940a820240030780700728009400114100f40200406940c102289800108500c001580c1c0b442401000d031030b140d02c054429840541c441e02e094 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 988274496 1250 988273246 988273267
    0xf0608010905070e0603210a03020d0e1e030306030d0e04061e140619080402220902011404060219030306120605180615100c06050408040f0b130b0f07020a0902 70
    0x132401000c4034001d03484403210b840c01d07446155119980c01c100294107501e0700c0818004a000c0e108520503000f2050500302840401c0c1400b02d203544140d01c1143c03680c81103c85544501e6164041203400300c0e4141c0166071a00345240c02001c564218401c01400094515200c01c441d80406141c0f1030311103224000304c00240700c118600c160510090500311400360800200076068000e02090302ca61400f0082407401080464a40c061004c1807003180c6881d405681c030740342070500010101d0b4502030340000c0e03800300c101c660607621200b103d003076840b6a4050b0141c00d41c2103a01000d02514030b01701704d0806a46d610000351000c030710b078034154031070b40b00d45130120f013900f04550f103103448544208620071281c001c64140144110401030920380385000386d4180f1400100d141047d25440c1d000c43e001f41025040c60100010010780700000c3c02607030103640407018001e03201d40844001d8011812030304103075000008203108400c1c80d400580421126071107402e01c1d12180d50701080320125640d002c0e00f490354001c035140821 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 988275746 1250 988274496 988274519
    0x60b0307180602010e031b0a02180a1404020f040c1209060501050114122d27030a0c021c150605120309030a0602280f0e04050402030d030f060801090507 67
    0x42c000c0e0b00c02480420411111a0740b68840c10724500790800113900c40c01004007050080a03101500280080c0703840c140c2245c403512403c07044030740700f00c05403910100c7c089401040010900039600038180d8541c40c0903400030711004010b031900030010301198280200c2c00349054050030087ca4414100894594034010015010401000048032903801c203000455010380172114480e444170615aa13001d2200b40d04900501040c5070008001c41c0d1041c0c3c40421803145c0301a485c40c0280e01e11b07524188540d032024840141c0368002c0c2d6000c8070002d0024900b1030003501d0a559030003546050030508642209003035a503203c941c200e101d84904030640302d800802c51803030400605c001c404802c1c40075510313104010300001d8985040d40c0c4001c261950108944600c0e100c400320f0004540900d100007118100e80b804050a10004014000e001803012000040c00b03007401e00541d4010380d4040c00400b299088284254050040c002000c500696170341d00000b81d43d402400f59400c0640908003070511181004c614411 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 988276996 1250 988275746 988275749
    0x702010207150f0f05090310050405060c04081b030312090a0b0603010519050a111617090108040b07020f161806140613081203092b030906060b030718 66
    0x200d45512900c11070182e030080c542100307500b254504143c2000341000d05035080c0c040c851406e909031080f0041d03200c0120050b80247d005500440444c0c8160762007901084040c07146020354607464000e00f614a603510144003442c00f40203c0141aa41049003041d03030b0502600e000c41314088150b00550541080c804440200f5802c0721060b0000d100340d00d000c000b6038500d118080c0c204034a440c0d84400180400f0810340c444100d014924040540d949161601d080441903121400e558447d1640c021101c0e020360309040303c00311901a120b40e02d139981ea0b61105140b1240081081c0e00390301a4102022450406000303070b43c0801c64100141c0a400e0030102400c14465042c9503102e202c510305001070016082c60801a50f19201c1140c20581c3e580030104c0c62030503000c06134022100da118a0f810400f00ea00b00901a61282412001310360f085090030005c4d400050091603454108080030006501092203500700c0b640301402000d0114400c0d640b040141025032007119000009011102003a071120220b1a0040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 988278246 1250 988276996 988277009
    0x1305010e09061005120705150405010839070b04081b0304120809150c07230a06031107050613030906080403050f1b010f0606020d0203181e030604080702010207 70
    0x980c80e001d00b103d4907a091501500e440340c55a0341100600b031030700300402805011302819030302c4415010150780c040c640180c062107001c11111030010b8149a000c505082404900b100c80340c0b4451a40005060008080045992080000c10600000c110036000130340c05244510030031503071400c101c0c803681c400b88803e40301080c1c60f802c1003004006802c1d0000080c01940c1c0c108000994a215100015541d88500c0410075038200700800c80109444001c18000c04880d18070004041038401c001140700c118440c0a1100c3c1d10443c4400248000c51081d8001d01c00f180c08691014070b000000c1d1031307007468018110340b41054903601d0b4030f41c07034205544070120740010001801c00a8083c00d20f6a00a01180280c25010219880100e188040c03542c241506450f0807040300000c1140905400c140006840980034030390140c850030f5124502240f0000850344100e124030724500030b000b42402040000c1c03102c1c100310a001d22a1034203050383d81d50140803590145128900c420398605947c400039040190707552018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 988279496 1250 988278246 988278253
    0xe1f020606310f090b1510030e06070c111203130503070302010903060b06040302180618061516050d05030a05060a030201080a05130516091b1413051305010e09 70
    0x2901d682142d003802800600441c040415084808000e540c0188103041d03019000141340b10034008110052040300300214000c0da40c00c0301448203030f00c00b038095924101c805805030780042c0c005040d00f841048400e80c213512541085452040003c0041c2039182628002c030040d400c001204e030305da801c0d40d550a40c0108415800b8145040c41c580020b4802d0005100107058151600e8000740c0d269942400c0300e000e503a0091070411015018002c651450300d08481c4540680060040007129481c22a03e0902c0b810009114804420036130b410312100e900209250150b4181002c1500700013030040c40004030050940d601c481d200d00e0710180d0641a980050000c0c1c2c0518900e40041c00540d0340805956030000440d80041910348072440c0180c0303142810034000d4614000c03651048140b0078003000510031180c90346070a001207107104201610200701a1502c07070100e89103101c141c0c107488a01c1d0140c0408080f4000c440401603030b8801040c40480e8484401940e20754500045c0486c0b0119000d0395005801003005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 988280746 1250 988279496 988279549
    0x91e01020601032d030c03180509070c0201050c0d030b0130050903070b090c100914090903040b0307120c1704060e0a21020721030e1f020606 62
    0x303074a465040c04003510707044503122100701d004c0c0084c00e034901c0200d0201501c00061258107006050360310b184001c50003d0040118000c07103440c610103000c25244028841401e40d2280c0c801a5206e0030410012410f12400b444001c0150350107010954101c0210740740424454844400140b51a141d201404000c5400c9a6a102505092841200c154050f1000002c00da160703001c0c050b1442c010084000e100540c9002004a021000301e5032850701803041d9a041c1d02006040f00c103494800741d0340a115608015800700c4809882d00162035500a2081800e82c0e1a2a440d0903074003030385500882d43c58006c120304000001d070015442c46400100040d6140c409400c40322580220344206000d80040c1c00c5030f49888800c810394000707014040e12550311031740394200c2c0b02082c2032005908a0014604015008490380021032038801e1080e907201980301c092407250000c1d150f80a0b6094045040610342200d02c1001e0350520b1114014508118905038004061502c2d080f41000020f80d150200c1110061889a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 988281996 1250 988280746 988280749
    0x90d0203040603021309021c060b120a11040510020c0907050c030313020a0513060321050f0703030908040e040521090402070203010f1113060305060a06030c020c04060b091e 76
    0x2a039042d2121032501583e00c00c20003000d00700007100c58002c090f100d0310000365804600da20b4894160300d2404031006104955462103159824010071001a41c0300c04807800003000e009055102001280c02c4070700c0541002d44907408900c03c00302240214000da4854258001145030204106d5031040e101d280c05071900c0810821507480380000740150541c0d0540d590000c08641c1c1d20b120040240c580a0800402954040302800180015100980d051501e550140884070090000c1c5c002c404000e0321100d00d88519000040060742c4142415802c1541e5412403500144017440100002c0040030006d01c600c1c10b141c00c0a0307080c41d10348520400900005280d00102540b4074060721003c5100300c400688035043c2d8001f0034003401c440000c4619082c074044a442d100c1c0c0319103000e44041191015070500b026202c09054085410684402c1e90101c40034030204a00c40c400c2d0000ca600010a206032886c00302491f0216041d101c558100d8086240e0100341c0203800d091207000c00100c01e89504145035071058140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 988283246 1250 988281996 988282003
    0xf1b03030c03050a020a06051317090a1205011107060c0f020c3001020c01140a0612060b06070b16031a06120907030c060e0a0902270d08041d090d02 65
    0x1c401014004041190300c0c00354020b01c0310b01999500f084080c08140717420f40d000e98006100034002c589054600b48441c0402d108039007032701c00102d0081e2000c0302c0d440c1040d417051300c0b541c02d504003101c00e59250000f9580650314100076025040c841d4401080c2c0448130709020381080c0c0c944020b101158007400d203034480c559800f030701500d202e076006146c2492040514207610829481012021b255030000801d079107007480543c000000104200d114080da912445025000d079199482020140c1c84407490110104200f98043d03004450010304075407820140f642c0c0c0940400742160006501c081c9288108805505400344661002410300340c415800c41d82000a1000c1c040e014079402d00c44500000201100000c1000101560b001000e180c485541c1c0c034001400d205030441c0b828000e42044900007105082c1d030081c0c0342c0d8016018060186075010744010300d50032000c080076583c040056208540401c40d40e000800c040d00f003440094001d803058500c2034140c1c0c1ca000e01062160b9201c1d2310641605070b80407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 988284496 1250 988283246 988283267
    0xc09031119090b040f151a1e0d0e10091103190807030917010c17040519020f150d052d06030c041d06150f010509040e03070f1b0303 58
    0xc0b103002982406850100b401041c158034a01d0a5900e8490001c40b0704c140340c411801250070312060b4089000074a0580c5916003e0700100049a520b03402c0000864050303076014040b000f810250016140300741940c0585818624220088010b6648401800784005550b14501003d03081e0010f0100000000e00107aa0448030340c1c003c0c20781c101c04a401000c0601c20541100180550030700301107984044080355000b1302608183c20041400007941045080004c8516845a40c1201c090050b91050788611904040405000c0f40d000c40340400d41484c6564404d00021001c10b035101550302c40d1038200440044440140968070344000c005500a0b4071416000b40800c0c0c0070112401c000d4075140d083c042458500707280211a80581000346560000c504450300e1109007503401c0417101903840b8076003020090700c029071945400400010324074841354025401043e003c41c2c09440007400780d121620640c11342d084481c040301c55030400001c00c01400300e01881c00c0d24050002c0000100c00c1c0c60750f9000b405002d00c1c07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 988285746 1250 988284496 988284509
    0xc01050c0705061c0b0319150605030613031214160c0501020f2a030a0f090909060b030d050f03160e210d170109090507090c09031119 59
    0x50010a001081c0700400041202a1510351110054000c940418040c01004001586070010340c00b200d1078002502400c209001c440940720f000e203500c5101800c031502c001c2c03401280d01d51600041036203080009034030030340f07000403080f814031480e00e0000c1c80982d01241c0661180d00748444041201c250741145500700749003d68a03948038546104c283c07403051a846001e0301e2544045400c81c0d054091800030005d100d07440d42d10015014082d2034004900c0600c0030b000590383d00510449120350302074403890210680705d0601d40050b507626021039042e40c00306c86003241c80584858455016090402c224803d0021030704016091959601e4a2005400010140c401c400d030120260703c840390054202c0e10b40002d01922642c0c03414110300c1c401c021310001301c2c0289031a124000b200c01c0c3ea24403039010101400400c1c4002c1c0400d91800840e007019084a440940d10781c05002d20008003003146202d4400744000941752690030a1440c1880318641d5400000180030f1020b14030207007080800c043c4c030036050390f01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 988286996 1250 988285746 988285757
    0x133080f060c160501020301030f150e120a27030b01050904080a080c04120c0602190206040e220303050a1104061704081c020415020d1e0c0c0e0a0605120c01 69
    0x800c50300c0f844000b03041d2001406552002002006100b4401b1000020714001e4185a031602d800410120807142184900e5a05070001003c96090081ca40018400c04082d80b40c841c10748103448409410800315400c1c0c0001664400604008100742c0010f618010481169000c245d0701e460b4541c0b40951148100407001c01c04040001034540e200d40b000c1c0c030040c01640384180f00c41d41d078514150900040034020b0f0030152081ca0b13558828182011651081654040d01c11418070303181000150400300d014058000c03084a105100b0b0b8410001c0c2c0034120510b0081c2ea0200d003500f0000201c604441d0402107810003981d08002c02d000c950b4011002690f403191403103000071240c0d40c030f04100c0703600e010301c2004036607100c0004014212000300750050300c107542d031022512003600a041d1050740d5800c0c1c200c0f0f20801150070581491142c140721038107414401d155080180384900159149000d02100d5082420300c100401d05004100905101c0c0030702805060314520b4412500f60b07226590713800b6418000d1304021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 988288246 1250 988286996 988287007
    0x3210c201e0a06261b041203030623060306060d0525020a030c11030a02060c0102041d041e050a0606030b1510121503021314130f060e0133080f060c 65
    0x110104140c0700300710506103101e813601d4503030001c11064094401d023980040e0404001082c4d540103200107400c820b401c04c003082c03040e40e1281d05100c05a0402840980e002c1e0302400304104101440c01291311820031914004e20750361001040740d0741140b441480d030702154001380c20080000c1e040503c1411850304a241002511100e00020b4600a48040000e4001c2030105003111104c4054012744103807100090040094200755103c2a12500c0071030f03001c0d20582409550390150081d441240700d0481c001d0b01901c02c15051901d0301c070103031555640308899200c00c0c0400c003c480c0688494111031940100c3d210040c80d030285034014145040d2910b60100e030b81e9240e40f600c200c00ea040008000459001c1c2a5030601c050400c01040200514104c0c0804c081011700000c4610b02d0b0704040c0310280d940081d00300b071000c0c040d03101d0000500402140c10699076888581c1e076158420310003603210280c500301040300307118003190b14004c411209a002c07100036030014061031810390000c25100e138401080c400c200c1c1c461 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 988289496 1250 988288246 988288261
    0x20a030b1f0f0c0f02031c030f090f030810090612020a051e0f18090607020106080a0c0905060a05030312090f030403020f31020403210c201e0a0626 65
    0x440722010000c1d414440c00002800ca90104602070340b07c520141c0303041200c1c1080401a9054502950001b00340c03c04040860780040d01440b4281d8011100d001184225622002c1000071141241c0001d202d420140e0494011841c1914404001d0b06003a91046a5000f159041c017030304a1040003003d00c601100c10003032510b0b8964414155103a02004402c0c0030a080038044c25403680340965290700154240840840d00310304c00030307102060a6101e0242d06c403040c900220240200005452560300c010710b0400001c031a9001c0000d80034000414002424030300348014590300e013021407201080b00382c0040c00108007507030302c0c0c044921049a040d2441c8a41c456080803030070032030101d0310143c03510030000d0020800c4044103a0250007640e11400013441501c881c00c03140110524491116400100d10350a540f0001c0e0140d090ba02c006420082d4418841540000141c4c10746031900810307005410340401d06a8515002841e20014150b60402c10700b103082d2100104142230305180b03000421000d0705c0101e5800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 988290746 1250 988289496 988289513
    0x1002040e0a05220c090b120303070f03020d090b1906080703080f0f04030308011d150105070c180b13050f13050f0d11011b0207180609020a030b1f0f0c 66
    0x3408044039070030000700e4245080f91a04401d4017407a801645014140c044504049504440b0110400003d42c1155161102200ca0b0031038070124900300350b000d000c507031040c54a5004041200f03208035038940d840d10340100f0400007440c19131004901281031030420086110045442c0d001e994100062580d100448040c950140c17086140090b1600c0300040d001040c554064401416902c0ea101d01015140005407058403000080d074154000048410311241150b00800040030702c3c0303206400030700101e41d513104c540ca400044400500961612000c08070003510b1b001000b01c1c07a4102034001002a41000800c1c41c40c503042c01042c0c0d02c01031038440d00540c1448020803a05076280340b0a811110750180447c00188490245003000440750308288503000c0c1c118003041402d088201d83d40c0100385a900d8568030080da4504007a000d41304035520359010944010360300003003001c40d407181c078046a0950b041044c0203a0a00341000700c072140305600502828a54004c0d840340c200450f51400c80d0754a08203007481c03502e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 988291996 1250 988290746 988290781
    0x2403061521081b1c080402100c11040603110a050406140d0c080d0507021f140319050f07021c0509060d110d05090c0a0602060a0908120c040302031002040e0a05 70
    0x30780311580303103c03100c40c0500020000b81c0f0407a44400220030165142c1c00391004074080c0c40080d4425090804040c2040c810f0b003629008030f008000122003d540803000ca021502c603a0001e5601d04007210b070300b1601d4206662808010b02080e00c0411200e403400d550340010f00c4504414500c98107490480c0000d2052130340047c0050480f0900384c41804811880c064101d520503107040740180c440c1c8125030420403030304010843c03100003925900201100ba070305401081e48001c050f0b00700350192201610b0410264441c1e5031040e0b5083ca8100c05604001d88041c0c0341102c2c06543c4c000100015401098003039002055030041c2d101078400b99100e110500904014115018490411500c00700c4c0159a080701c1e90082c41c05544004d0988400084510601060070810f02135540560722402c0401c230000d4041d444602c0e07980c000c01096040c1020451000120300c016580b030655000d02103401d00a6150500016100c0c00c00c41d00c045213854508525400212001072202d440f0076a1074002030901900c09681c2071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 988293246 1250 988291996 988292017
    0x5060409050f010203090d030605061603031d1605150a0c03030b13091403030714070807060c020a051002090109090f0902060a050d0b150702060d240306152108 70
    0x3540a01282c886600035081110008140d00c031340408800c680d8000d1140d40e00f9100003810b0146805012035841c00003151000c1c046041640c0c50401c04085150060b800c23400039240320180464564401c5c001c03e90009a82049108081c856a102182d80b4007108a4aa01c9200e00700f4034011409402d0a034001e01e0707450900c0790440250301d00c018170000341c1c2d408504500e01c161504982601e0340c6000315035a00040760400080345280c14421603104120020381885489204660310f01041039075018141e0f49101040000b42c1c0c004810ba0041080a00804103101400b2204504050704140002c280400d903104044220359907624001d81e983c5c02d5081700d0062178004d0b2450b1340d10900914001c10f40c3d801610950380161030210545510b180c4803028103680c810000e5180c1c1000c80342e03000c120060b446000c401e1501c0d5030303c80a02c081e030821808160b011003a003000c000500c03413441c2003000130746164400440160449090500c02410304000305284072032001c401c88401050740c54001d800381700f80b00110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 988294496 1250 988293246 988293253
    0xb01051504063501210206040b070f0c0305031c0207020a0303050d020d050709140906102001060e0a1d2505030303100f060503070921060e0a050706020703080304060506040905 77
    0x3c01e005026815003604950003a1080c0301c0302008484aa00380310350340000254030400400007040701c03c070180041c2c242d5501440c200c001418441c0d81d09040d98000da4822111034001140300c0c2c84840c203068070400d032034180c50415840e007081a800036007001c17250700006042c442c01040d541148107990741514001c05040c1010899030600d00c2000c0d010041e180305018a02a840c0b00314580380c18200384050042f81c0140c01e41400c695099400d5a00020764900910701c40c0710100814042d80b000d00610004011450003085541803180010b002d03562900c000201103401c500d400c0c000a040081c0c1008140c0501008460f04500440b249408500c2030380704940c98880403003403000311164415450111107801d04c0000081c0e03500c842c162110f00040b184c96010807488081042005151003a19620513040403652040c01c005980300c0c800c89917000c3c00500c40794401e001590420100f086941c0c0607001700c0c00140392180c03941e920510181700090005150a440307002090b26500c40350050380710564402d055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 988295746 1250 988294496 988294577
    0x1090e1b0d0c03141819030c0503120417090d060c0201060f0626090307030f02010f0c050c0f060105030a081806070b190501060507110f04020d02070b0105150406 71
    0x9001c4c221a070641c002114044021699540040302840e8030750404070042d000342031645514903000701020206078280810b14108500160b0306000401140c0c000f8007400070f960815050150400000c101d102c500c601041149130065510703030200300c0c1c0030b40e440741c00424212100d1000724050803ca80c4019000303484090041441c0e40c1003e14111101d0b505003003c2d07004c0c0c190410500c9900c00540d541417140e0420412540070a10401d81c03c49090064000030510440e40d00705242140c00600135036002460100e000c05110501f880313205c650304015401044c00d03504100000c0c2e11400d02e08401407070325400150b00d0740801000008442c0710100103259035120902810050058401200d240e085000369010103030f84546e080c417030035040c1c0741d413030742d440e801d082195941c01d0541c0880003446034046103015102c80c1703a9031103000404e4090045600907031a074684d0b00d000303403003030406030440e92092181d001905a0a03c00000b60350445641b840c0501032030b5914003240003000f0403400103001201c01042d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 988296996 1250 988295746 988295771
    0x9210702091f3b1308070305280e090114190909050309100903050c0d081b01020d0e01050c0702041805060a020a0f0503100905100504140f0601090e1b0d 67
    0x210112009003c45000e0004041a0080071003401c080f1803c040c002c4900020308080380e5244050324000e807007414101c0c600b1101e18683d0a008107122215104070101c0c0c00f5035410300b1740c401d0024403040c0080d9080b0985504181c2400910001070b1900b9001d1203181c0e074161403420380d070020000104642c050400c01b5507003070f0074183d450354002890302c0e0141040007120880d40303104444043c112500000a0700038003248404110030741958550030740e04007406100401c040700040d80d0b2520740040200005136180c0c0300c03499800c02d03a141c0204400f00d0b64908020002d001c80100100d5506682c100c80010b52040300c0c910b518840e8544a00c05041840344808000c14812160b0091419520945551b4412003280804403480d1104a844401c030202c988004c001002c8503800c0290008846100d031107001380c42d80c2c0400c04660340301c4102c1d41d80c1d524400034032201081030708a09412420a00c0e14085450030584860380d01840030349040c3e0784000340802a10700b06c04810603641c03520706000041c0f09429102c007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 988298246 1250 988296996 988297049
    0x609050304061b150504020a0518090120180a030c0e190605030307020123120f010e130b0601120218092d060f03010509210702091f 58
    0x4071400f0a100180402d400c4080c031500030b048960040d40301c1040c4d9202e0b00e030440038001c0580100d0f0802801903000c1100d542c3e40d0302c1c00040c418440c1b80b035603451511005031030a55245844001114200c40c0710000509044012a080c05001640d00c80c070100150700482c02891030f60303002034030910306604041640410003d4a50195110701044a003408203c028141100e0f518490713140e150380200a0030b0010350003007000c03146030720326101004490318050b02082c40036800400b00a044500080c01c0001006010a4070350150000204000c1e0030701c0c1100003940d64001c01c0764040c100c902e00c0b40005203d0380c4550000d14223086003230f0065455102c40840d0003403404034071007544c5c81000c030040003941c8860104080c040c0c0503660381204000c1c1d01c900d210000c0305e08014103a5a04404200100b01d200e40b424052103000c0c02c00d8400900302d03011807200320241d00e042e0310703901320140782c0c03c0041030050380d101205603420034901c0740580c0b18103000e0306c000d90f001d58159005255100319010301e89101782d03005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 988299496 1250 988298246 988298249
    0x1090507020c2d06120708090f190b0916090b0306090d02031c02091903110102060606090d02120118020312030903070b0a0b150309120c0a03030b031501030c05010e03031c0506010c0609050304 84
    0x601100c0d0681805140c041c2c4800e1030030201681a06400078ad00c02003404001c02503000341c100019200b4400a684040042c02415040005955200c030180409401c003000b480c1c0e400303108140580041451810b00039228802c403541c0310340703520343c1729045074822002d641100c0050400425940c0d9801c010403d036041d000651205440040362034440050f02c0d400800d01c03d01c200b0005008a01c2e142d2070400304054900c07525003d0b07030404034585042e03400c0380f0b0034429080060480f4a205200c100107204141c80d2040400580d806880c0a106001201c1d070000145d4030060b602c800404a20f40e0342a201200502800e600658002c00710600c0b40d0111070324100442c0595000f00c256480c2054004101071a84502d9080100c0740d40312410700400720740b00f41e002d030364504002030a8480302e001512400018450a0701300fa01c84401e42c886c100219a01f11808007810070081e4003860400c82007003021000c08001c0201600036540710320001d41941c0c4507000600500d03920000400c508100c904102d692a0403e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 988300746 1250 988299496 988299511
    0x1509120d09150201020c0705011d0607061506022413150906060b0c0705090703060b0c0c032b03110f0409050105040606030905191a01090507020c2d06120708 69
    0x40300d601e002e00d1441802182c0502c1a140d000f000200e1912004403440e80000c681e2868000b0141d5000907290b4407040200705050003014003107282c01a482c0c060b1070000403980300700700799801150b503040c401c004c0d14604203c040e60041c1d24141541c072442d0307c0311400c0464400074100000384006940d02401c80e4000090103000d1201040410380790300c1c3c0c51450b8440d8000b550003960040e1003c01c600d1400d02d28440c4d01c074409160220301c4a646044881c05900b00180700314203900315011040407400d0412010035401c041c2c02485109007902402411001002d0020404050f00d50701d203003081c83c45240880ea294090311185079600c41da290640c0e0018642801070a00c41e60400c140080e56038400c3c003138000c61540040142203528510319100054200030403080f2041758441e5100c191103071400c40c1c464020404071034080768038a4a100c00074200f134140140c2901c03a03200c2d926000d10699200c01d124554008400340280c80c11100c00002d04180034010200700074244170010071040e60b0b0303c0141c05000d90304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 988301996 1250 988300746 988300769
    0x2040f050f15030d1205042a17030a0509040921030905011802150d06030c0608010303032301090c1407050106030b010812370224061509120d09 63
    0x108030030144c40365091000b4034002840340e080d400d12415280d000d643c01521030701c107003103200b8101d82c2980c014041c620000302491101840401c07403100b80305545403842017180c0145190080482d006040d42c00340103140d60240d5074a40750f2204005046408101c0b8080761050481340e408010002400b4081003a001c03120303035007411000e01c410b0f5184001c0d00522a4010310703e6000c00d003007110140d5540c2050083d00251522100d000001c180d05a00c00c40141001e540c5203115903046040240540d0050030b43e5002d55000c2218040c00700750700790311081c15500c01c0030000c20b000b0600c7c2c90031196040c5200140c0d031180740c0082c4c000b040000560048084a1140d035909119070b988030b4600d500d0700c441c0ca00010080a08010807213555040b940c216000383ca4002c800075036202c00e48035004040041c03100800140e0300c01c05501e041c0c0075041801072516800d0004104e968501709004c01c11140095451a0090b4000700f080c1e440d543d80d881082d54201141c0f021a5409040101d0041c0b07011000e2040c55007805 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 988303246 1250 988301996 988302031
    0xb0405250c08030f090715122405090901060e09010608010e030307050a0e1c0c090b0d020d060903050f0a050a08060f011d0a33110a0f02040f050f 64
    0x500070154480e94580080040c0c0c1142e071020150392509000030911007090141070030114200e40c0018540b000740c0c4a698518108185a0010345d044410665800940c1290860741d00c081c0b001c03105070f01d01500c40a2700d000d11303a503c40c0e80400d0b01401c0540c000c940c240c0030207000c206044505501070811591000000e1045400c503003640303a00c038402500d01d003001440130810800428010710104416038009400541862481005004c0080ec802002c95000100690400070f80440740903881015004480c04805082da541c0041c0d00340c002810020003141e114032544d41418002d40603281d071068034040303040d5240c110000060955002d10328107030116801102254441c244036a40720700740c84060712440c4030b0030100b5403410b06e1b59142080a0b50f0040f2403001c0802c0130550b58020341c1e0290707174000644d400c82c21113010554400101d00b41204c200031102802410380303400000c0c807002182e0000000040c2100c2c40c00800d000e412040030b0012244c1c1400107001c2501e024040c0c02e482002c07120046484070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 988304496 1250 988303246 988303321
    0x910020f0706170430030203060415082a030d020a1a0408030606090f040e0a031709060c0c0c10050405040e06010b0f0c03070203061f080d02070314010b0405 69
    0xc005043e5800c0005909100250014043c2c561121307000d80c0a1114190310742c2c082c001c0c070000e03d1880c030400d030000790080b080c40014103040c01203050704800c5000c003038403a80c201002c0c0307684c410804155040341101c0f0000c201608442e9800000040c07130280c1900c034412011035010b0340e14005140121014900008004114440084124000c643c00301c134040ca140c64030b4041080710341046a038142d01490b54048901103942d41e1240c1011281008080c004080f4075090143c0341c1d2600c90300c0c00207050405400c0200708500860700075800116000b40d5601d5050b40d0208a103028014000141c02c4a00d603080c010009401c900a84101c036000c540502000548242c81d6403605c0080c8a003c07030180040c800c100f446440d0501512085a000040f00d0030810302e900003d00c0c2820940b1101110b10b001c44108041800c200700d002c000e0702c442c00040052002005000f5550307551488007a100222500700b9400c0350360f080d080360904000c0104140454184085003410a001078003035060740c4804c0b200940040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 988305746 1250 988304496 988304507
    0x160e0f300309031e0313030b01050406050303030c041203050c0d0203090406080307051036030e0102032d041d0702210f1b03030106030506090f0c0318030910020f0706 73
    0x101c41000d4050701450b030f4903d503039031100d1180c0764003a00130340401e00c0003134008a03148030008000c40c0034445910b0254508030501040b12240e4000a0082e04100100b100e040352060884045503010102d060007030765a41011a5a40241440b02015002d080e1a0019042c0d00001515108808490802049079555103869a0b80314102c0000c08541181c9001c28418100c0d6100802004081024821000b0700e24841c503400c403030040d040c110502045030044c5c2815032110000c0c115010038002585000100012801d0099400ca1107800e00202c004628a00c410810142d5008200801108049050700d41d0700800565040b40d10800500c15100c000c01d0401a10100310308241805d50201e1514014403c21070380c07540400d001c0107a1507055402d84590180800042d8006c0400e0340d0000340c0c0e42880300c200414204060951030800000b1820310207544031310030440707800c50300c01f5070783c4030b5087c000102e00c9045019440340e00d80c0c0a880aa07000401a0300410040d0382058040d0940c0d260a440d010103540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 988306996 1250 988305746 988305757
    0x30b010e090424020f03270714040908070f11092e030c26010209060301090b030c0a06020c01090e09060106050a0c0f060204080f0105160e0f3003 64
    0x500c081c0e07140114010401c08001e420150164684203c0141110031258050780d10801309480e9030705c000404c201800140c1c0c40c558848428011540500740110001ca40e43e448050049110480d92001e4442007552141e0000c00481d9000038640d88449850a24000c40004458159841942e04121488071725124111510540c1440180610211501c0c3d580c1580e14101000150440046401001003000340c50360300c0c010644070040390b48884a4100c86102c81a03840301611241c0e0060101d18803e6070f502003aa815900380c0c404c0010031441e03d500080c0780040000c1200c0d00165004000303d03080f5400b00b8014610502a2181e02403a43e403a403120348500b1080ba030710746a0380c02100060140c0c030300c5840141aa44011702d080c208030b2019031100304113071000407401c546a40d0700280811000c003060005000f00d00c04003000300710314909024034035080c01c503070101038003042032600d5a0301d0325039550b01c090200004080d20b0701403101c83c61000c11042b100500319808000310712807a8281e2400d030000883c1c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 988308246 1250 988306996 988306999
    0x150f0302130e2a12030322050304051005090901180e2113090e06060f04140f0a060e0f0919030e1009080d020a1e0201140f04030f05030307030b010e 65
    0x501050300200c1182440402c002c0740c070008031008100407540d40d802d41302111050810069035603414248034252142c400c00c00c1c01d100300d442860300a0f0220340c0220981701190300545804181e00300032074040722a4801c0d00440c2e81d100b000e000003c00c06440b80d5401040e4003410210412491940c4c0c2d00e0b00c3d548854100e0300c011501c40810301700a0b02e0f070410300603204240030307070a501d4260b503203940e41c04c829201440540725082e88440108519480c00000e079801240b4152020800160a6800043c501d280207100d2500c5200b21070120755401ca0a5000b600100200050f080d050301b0220701c018510b50058414050328032541417400702640600031030807941d03030341500d60700f80c600015018419a0b0040105c0705042c000003443c0010b80c02c00621064010340f84950180a041c1c86a180c011400301d038844843c80b40300c182d03402210041c3d822850100b01e0700d9014118644030380307066048989504ca6904010701c0d454240d1124001c0140020156004040c5500e0500c4060028001100d1409248200300e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 988309352 1106 988308246 988308253
    0xd0807020607050421110406030f021302091327050c0306010803040f032409080c06060301020a050a1209121205060a0b1c150f0302130e 60
    0xe910040d5801c00e1030406060141043c1030740f6501e0001070541a00f0901c4c10240240506e20444903400240244081038691920030001017441c0c00072409040c2a0b101c0407070030740e03190007075520f6150040d00e070740001c034225500754018264210003e00303000c01000340346802c41c90540c0010145805040100180c14004040c94509901680b181d403145d0000d00040c010f0694400d2894112600030307940c2400f00c80001140c5040c096016256100d43d0318200c084020491507c014000c00c0301c40f00152040e503513822080c1030a0384504110400010340070484541c501c1c1c00703060303c040121410040003030220210384d244100e13500c00050321404915542819100004c00380561680920705407540c0c0c1900d807401824113054007464201041d40401d00c1c8891101c0155a48181810f00100c0b015070440ba5a40005c07600c8000c0c54001139002e140e820204107402c0f12180564002425110005c = true := by decide +kernel

theorem cover : BRFrame.Cov 988129496 988309352 := by
  have h0 := BRFrame.cov_init 988129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 988129496 ≤ n) (h2 : n < 988309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
