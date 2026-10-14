-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:05:01.594678+00:00
-- url     : https://prove2.me/submissions/d67576ea-4561-455c-ad48-67a3918fdb8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 191187050 ≤ n < 191366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 191188300 1250 191187050 191187067
    0x30a050a0b070815010f1422030c05010306051509060712030c0207081f0506030a0c03080408010c0c08040909031206060224041101050c070806010608060f0f0303030a0b010c020a0e01030c0902041406 87
    0x10b80e405a800c038805040c4000701662290004506c610092764070a10302e02d10000e45520044044403903601485400c515042e100c1d440c020400c4011b0f1614200c001d103c2813030600195600035801c03030340f05070380c4000c2501c0e803196805540d010b00c60701001d89102c1c001011007a00c0a000b80703d100c00843d0344480300607038481c0450845d46040c8103c00080e50003959890203240e41c2c0c030701103c81d90b110740324218040d40f03030010441601d445540c50510240c1c11010803401c0a00f007101180081034156400c8061010b604050241e450303040c020762000f071440e50042c040b020749400d8040d07088080c107240c940c1c40f10810805c0100040c480351140c090300305c080c60a90340b0350740c008180311310306051500410340b28810f00300000365142d44005000c1c0314003030a6511044a80f0010f052150001038903100c254150002e10010383c00d02d505038822400464145007201621280b6000319260f03614039001040008007150040c400d00200c030303220b0001403165103030840c40c0605e480f04480450a08070381c0c2a21a0500240080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 191189550 1250 191188300 191188337
    0xe1605041419090203151f080d20031611040e031c1d0a20030f0601030605070c060501120314040608040210050409140910020c030405040b030a050a0b070815010f 71
    0x1b03407400c585811100c074200000152500700c09806c0c0d20700c03500941072000c10590b00106511601c1080c0f5154560010700d0480c0d51180d409082c508c03c80d40c0c0c030090103d40c00758500e10003610841e6015056000000c0780b030205000c19181c0559240c0d01c560300030004090810650003904610707407408800001e01c000d0307031108032100e046051100701c507030b1244000d180c0902100c0c105042084108844980f80b482e45e001c1411345500540d8000345540d005200104045000fa4100c960b1040c1d103440c04010021503075650701c044400a800019100200d0002c1000300740d009000d00450070301c08a803481c14140f52000090002000420003070282442c168080d06090241003503901412081605010780c035015069440003600440360001644103203010704090034600e208032042082440091850036040c6001d00c005040c0f00c1343c2d1075400d80b01c1c0c04060004581c0911503004000e1054507003020a04000c2d40040162102500e517007070125440a0082250f07800c8a05400c03113203001d06185494854094451 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 191190800 1250 191189550 191189563
    0x40513020306040b0d38070827070509012114010f1802010e040501081b03030708031e0108071413061707050405090106050918010e1605041419090203 66
    0x5504007000404202c02c010641211b201403400345007035803140c28504241400d9a60840c0c21000303414010001140c40a481030711525030001103103003501800c00741c030107482c41c5c2036540d080019096080b840c02484140f52029200b401400020323a0030810ba01c0c40c0014965048440f0303030090440d031403261032a850311020341000015500e05c44003000183c504074500e0102c60b0344c2c403d0403400a020907072440b0462070f0920495069855900007040102100001c00e49070030a00c91425030f2600c0300340003210010713882c90b0007140300d54400102000400842081b445000c5410b03042610140c000d01c03c01d0000c4423810004880400c002c031420680b6021803801c80c802041a0f800441c1014210302d095004507400180b42e408881d4140c82c2040103544842c1540d00300c4505000745030340880060040f400c02c00c000a20043c00c0c500e100000110002140382d2a0315182c06c0043e103001124000b80c04210524281c45511a020003042e4020300500d85261980340c0003400c80e80071000596900303050801e5403401c01c81d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 191192050 1250 191190800 191190821
    0x50703060f0e0c04091101030b1305040c150504060c030f050705070608220f020d031101020301080709060603021305041805030d020d180f0210030b0d0f020405010b04051302030604 79
    0x30044000c00c040481c0140100c14102c4445100301d0114118900b0310b03129058103950442c0e00d11349140c650100440140c071070f141c030f516804804c0c006190f001195910950340154401d80300350103407500e803500c02250302c81c50b92080014004c1c103101c10030605401c0550001042d91610300700e82050821712082d240c500665902900c1441040300210714140c01c03d00c8640103404c0300414140c2c049119943e10800708080d44002c2039030040c0381a0000609268401c01c520900c40e08002000c030742c032607005500b241c109a100e584158458074003008004c1c00c4d407103540050441071405610704802840c4d014200d501611070346000c1c5548240308510761480212505a8035405026a59188144804c0c0d5010390454181c4000f114030b811043d485540d9448460303000254403840440c0c10617846e4080025202c854910310b0705050700d91980c0c0b6039170340c0d905000c0e051082c82034010b02080200d6005000480358141c004603000c0306c0400040c031481c2d0b2107202c407030308500f107181d00584c0e00d0b0b54440c0030034042c0c010b0703505 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 191193300 1250 191192050 191192063
    0xd06020c070905340c020904030309150c0203090f01020709021c0e0f071806050a0b0c0d0810030f05120304080408060c0f03070c0201110304060f08010b070c0e04050703 74
    0x60400d03112001082103011501c0500303003401952240942e20001100740000a002c50a1035842c540800e0300110024585104504010b0b8006100d90045411440111000c400090b9103000040c1004402d0f080d6041d54101c41904001070504124040d55030300c80c000c502c520410084414401d180e1007000041c1c080c1c8801842035403900055482c9100d040f81c1d010300714507a58181000000c4200c0000341d4415448039160040c44c4580c40c1c103605002069001015440c401d855503804945503c414070941c00404003590f0360395544240881d0b65040c00c103101c1c07000c4104280442840b1070941010703a60030a4941110795552078500c50b180c0741c0d2419040388070b0000c02c010040208002d10500710054022500094140d881c10303a00d2120141d12881810b2009000d207000b4400714003040c1c420070380294040c1c810705008174203c00c45001e05103150066403080002902c020482c1800c1c03a4000510383c0105400e500e41ea0610b4210f99501c8440c0941b8010004540f15910008050003010003060005640205 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 191194550 1250 191193300 191193307
    0xd05090616140706181a070b0c0c0a030f0f090302030601051210060b1905030702030307050c0114010308030a0f1401030206071a131e0f1401090209090304030506060d05060c090d0602 80
    0x10040e045902c0144800344001d4450b031700140711825280011070908500340c4640c80d10a2a6030b40001c40302d0080c0c10495001000d21400c5e000d00c40400c001c032015800b075200d0004c071010610001300380000144a030810007c000f041040183c400040580c159402241e8041000480c000d1580c50008d04491010395141007034030000b6001408030041c011048075444980d806d66080300d041d29580b00907101640141d10400008140700c0c49140a03100700540d0400200700780302d1400c0d80000c0c04000b0781060325940400000d000300462140310350b10300d4003900c0d0424800e82d4948040140308900500c000790041800160350710801456803c08100c42040c02c2c041607041c1400c424052035010416011200c200b218903001c420340c5000c80040d42016130101500150030029915a8003480d40402408201d41d211846480141e461074a400d2186c50600001e540f00c900c0c5d410510315000d0b0280600e40100844612140841c03408680d007a0300142460104e6176929410004c60307428070300d40c61b01409003840071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 191195800 1250 191194550 191194559
    0x702100f051e04031409010e090405010c03051302060d09050114010b04062006040210090f03061401060c1a0601020a0c09090510020a0504060804080904050f090d050906161407 77
    0x180e100c14002d08141e5400420040100c0000e00e0aa00c29940507010071403401c0c0030800c030140300300103083d404418540030802050140114007420301c00e41e07046070280d4454548541c0705600d0710895070301c07003880c00441c00c044000c1d030041a524030444042ca107506d500c0e5141c07141800400d4011123840718104000750713065030f540c80090b000b0350444d0080d5000206102d6042030404080035603450b552000300f01502d0103032255400c101843da28501c1d001c1c14014081c0b0001244902110f0180082d40101c3c80032072206900c5149800140d0141c00c80c0b800d0040e64100c042c08514002e00210020391903511440c01c5488000050341781c00880100100110364540e0080b82c0d20340b0540181741d003148580c044034200b03448120140d043e0b002d40700744d0000082c01030008102d094030a0042a4215002c3c0c0040f0307103030602030404107064074011100709009800e00c00500c5100c203403c200001000e4040d1410174203200517040020520710031b94081881144550031a40305000c690602e0f40f00e210324407411100d2280d84c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 191197050 1250 191195800 191195831
    0x1030f0209100804030206070e100c02120f0307210206040b09010905030a0f0e010f0206070c03092115021c090503210106020c0909060c0a02031c0203011a071a070210 73
    0x45400f200180076507c0442c40c010700440348010100002080942801c40c00c1030700311880a1802003d0303a100c0c045c19090031803414180301c59060451041c01440d560138050514045200090003030030303885c01216040821842e804519550450352040d804440c580341c1242050140042603005445400b0010340e0700c2c03280b608501c034811660b98076102d042400686400543d0240c0b840d000040241e0808800648007910948806036954030a061142c140354a881180c04c8201c88840e00101800c0040b41000501074401016100042807001c10b5240080d903200610b004003118004054098640070480c042120500c203954481c1044070031000107621000c180c001c10b090a100e81000340c022401e800c0352a041810303110b40f0403103110008103844d4a03091240100c41d0300070100f440841c0000d01905140d485002104000355030512400b50302c95050840c1e420f0021a0f6a01410700110108283c1002407408a00c1405034560710751021600e603035403642a400c00c00b40a1010210602c1c054001008552 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 191198300 1250 191197050 191197067
    0x60c05030f03100f08010b090403080a18050c0108100b04091a1e151806030403020a0b010b04030c0e0103110f01090506210702060c03041712070201021903150501030f020910 76
    0x11540c403000300300c035900c0e0f01845c200c1e444051f00e103400090007400100070901903102d482d004044403800007200040c1540c4128581400b5100b1201e580008034120038560744058219003008908601c41c19603850050302810521442c85038140c81c03915000081c00311000b0380849020760402030808040411029880d80002d2080b00783d091240c1001400e0075041c2e01400140d420a510031454911109024801c1010344d40000388101c003144240100103002030584c0707240500030442c564405031030700c0c214584080946016040b00250707490240040000c80c0c806803942c07101010a69440c064075590340f004a500442c949c000540004000038078041082ca08403504010040348501380c4819154000300b2620745200359010190140c0c2800894081281c00703075000d08100300c120b01603145c0301540d05071000650017241c0103801b503540400c8496010b240500c1d4200c1845c2e15103010040c1c00c0b4031390307c0b808416000d030084a041543c0e0340c2c0940610206076040b1141032100030301c0e5812040b62400001e120b080d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 191199550 1250 191198300 191198309
    0x5071a0702070b030106050711030705060c030d0f150501030221010b090102160b1e070f080405040c020703230a140f07060c0b18031b06010f0609030507060c05030f0310 74
    0x72404400080843c081e9060740e0585105503921441c008440c0c131140f014003010080198140a240d000041e07694900009001c00c035410005503840301c070180c1144041724601154950458103006640440140903078400050301c0702400c0068591590b5001c1c1810400441d0450146820120011800004920180403201026800c8800e0420307029031a4020500511611110307610a0100c02c11210741604400001030142440c103007868055265401514480700050b170707039144c002070180003904150049900703040450000b001d60724515515000c100540c1440400401e41c0c4036601d055000c0c3c03d1280e00341294000d0b18400c84481282d07401a00c4201001d2000141d03c40c204000540030301a104010090f17801c003801d1081a80d60b1000d0403410103d0412402050004004500f84100200070003805101507400521056050000214074601c80303030042c1007444483d100030000100000303483e1064a04500e04650440c10b985443d500d5800313100700c40c070b503000c1010040120750421003541d401241d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 191200800 1250 191199550 191199553
    0x20a05091036050409020303160b0402042319090203030304082d040911040308070f021203130909050a0c0605130506070312090c0803041d0c13060c020105071a0702 72
    0x1940702c400784800d403a8100084002191951420009841c180d0310802c52a800a0140ca1400780301e01054081c1c040c202004441e859104000d01c420b41c10248525000d0f814103182506d4132000000c2c400444810043c524850341401030a02510a01203401c2885c1c1071ba80034044a440c1d050078035020145420000340d079414000d1942407444503282800e40e098003109032180349481c0c9070404030990068103000c5031842150408200010000d18008003c05800b8041c1400205041e00e030310400515100080f6580140c0d0300900c0401111102c4140342801c0f1150b6070400141a031113842e100d410a80c03041d002403d10010f648002402130b803c41e0040c01040910300d2907440c2d980d02e803000c004c001d00134424098001000d584500e10210000c1c0c1c45054090f000e080ba00c01c00c1942c0c0c200140c51603009070070118103812a451403034170349400c21100d6500300728a0040a41010f0514485d05c54070000703031154100b00066095600b0569009001711003101d1340100c2219619000c036070551582c09030542e80308006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 191202050 1250 191200800 191200847
    0x7060504060c08010b0d05040302070b0301090e010e0606060f130e090a030f020706120f0609020f0904060902030417070f02030717060a0519020c03040b0316080f06010503010603020a050910 83
    0x3168410b00545050321700201c0b01e2410094001007040c01410024802c50a5100e03c45021401a1058001d50300810580e040801d8001202c000c05080d41c041002020301070f4020405e00406960703940950324240100c4030040d0300c6402c54034000985440365403006500e5801c078400d000c0c1400c3c0100741400480c1c0a40c07200e03494502500405c9989907a580700d01800201d03000764140a04182e078105041d8034980100101f079150f114010352040b44e100342e4601e101902c0001d400310280c2001d0054200800320b5800850030341c50a500c0e4425264180c8500c42981c1d90001400d07010400b441c1d542400140d0042c0c121601940c682c806500001204041080c2d030303100d0b800000e02211141e0084604c1002c00400e000103002d55039200101940003d4a14540d601003030001040d02c94507038028520861074035160f0019040c07980006005020b0180850121100c17603400c1041c079136002002c03203045034110300c4e00582d02e503000c80089586005260100d83e101c41c4031620700810300d40c044140030400021040c0e1610 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 191203300 1250 191202050 191202071
    0xb0904110f09030d1106040b0403030e0f06011d13062c0102030a24170a050609030a1e080f04020d06020d0518010e0703080c0102040e181e06130203010b060706050406 73
    0x3030341840ea030022980c1ba48102c00150004984241e442d8015109042c0410580e00d00300103242400c582c90790041440c8c1c45040100b01042c1c602d80f4010400190081c00c0555003411170310310010080e1154003030251a110101c1c0f0110391411070a4114031040c1e4124000c80d90010000b0b41c0c042d45c404c0d40d85208180c20b089102e41c00b50030b10180e15400540504a201c0c585151050700d85424490b5940d4042a00498003a0b80c00b040052001078450045070300515a15500000081c01d81610f00f1880d203440c801c01c00075012415003050352690804500e005038a200c3c0d480b840000c0384a004440018892030001c0303070044c3c0e589a183c20050088007036030040c400284d02c81040c10708803560103019000507071002204001040b44800144682500d550001d85815180e140c40c0000003416a050f04850050040004a4101c28006080d00880150340351100f03454058030701d95244000762280032242086801c40c004c66400358808004c100e0b000e450141c492a6074104500140001c4400791401800c01c2d0781c0030f4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 191204550 1250 191203300 191203307
    0x80f0703061a0f13060504141b0304020d030305060303160f050105010501050c030906030a0f1b02070b0406080f07032d0608060906070804030203070c0e0403270b0904110f09030d 78
    0x20410b88010300350b49100c0440fa41040b24180d4444400e810710355643c0000f04994a89015101d2a034035248800049400d00d080400e5084020f400070130301d411014014040182e0300c8035a0035032100d825180101d1182c46020000f030840c81000c0050b2002603902060b4420040503281075007600340154020003c1e40e0383c800054515210b00300190019800420406149141160166801443c1070f0b00014428400010390000c43c3c0701ca10420b42944081e0f540e50300c000da0f041000001600003810940d0601c1e1030820301030a14000540b441d40605060000510010301ca0b03804848040040c010400c000c0c040d00842039092003501600032046400c0000202c1c02e050001440703409202c404c4021301c9240e40f844002c886401014000310214042041a14082078076040c1c45400381140c45c100003c6403c3c903260191001d29140303220b001082d480c001089094030042c0314001150407206155a0756051400010000c1081441c1c2c16030030013000c11240d2540c060000a0000c0d44e00030750840741410003498064 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 191205800 1250 191204550 191204591
    0x1407030603051509070b130902160507060c0308131110080a0f09080a0f120614120c031c030207230d020f19150903020f0d0903030806041104080f070306 67
    0x4c0c090303a030083c1d81c10070031248060020b0400702c100d100a40c50850325038680d04180d03440091103510203090900071005110040c40498028501c9090105e21b09090382d0303014041c40c40081c154889010b601e1246410301c4400325007034a644c803008200410807442e001001d00111401c1d182a0341023842c1016160541e0620f01c910190983c0090380b181c181509000100c581c4840040d41c101000521001580015114001ca4000e0034a40b0045446508018148000c2c4510000c3c903455683c071203030041c4015140410302c40341c1204031044a40e04c1c0e200c102c006802920a041c0010408914414520032812560460214080c113484c15184401c5100c5022640c6620303502c0207042582284018606110000d444520700c86d02c0b5558500c072620a40045200701e507519034007580540c0240080c84460a0240480007510201e07080c000d41036421078400804811005100c0e0340074a82c0d800501c174103603044009031402800c500c8216603113000d00d071052585969180c40100c0e00c42d801d011000b02044002c00e170300c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 191207050 1250 191205800 191205811
    0x14040503100b03010e070807090510051c0816030e0a0e0c0f070501060302060a051806030114010804110a03080a03050903040501050d09170a1d0d0f03050c0114070306030515 76
    0x801035403503000880740c0200403491480b030341996500c0c1d40342102d160500640001388103c00203400c0c0145003950300000c0e00c100900103807160144000c00c1c8103d0f83c40081c1c10801c0f054001c0641c01508540c607186100748030301002e014003507550040d09410154841203400190700c0c10750790100784540d07403400200c640f20152012345414605100700b032132804411001e407070003d01600010480c4e40d52500807a0f030980c40011400c00103100000c0d10611500000c1c9600310301082568050710359858a0900c50400d0138000b501410440d4550200d010300031205041140b83c5002003580c500700e42d6a180011071039100740c040c0c00c0800d0824001442c070fa9804030179a42102d0068403058902846000000020700004d5000c981144040a90007032200082014108034503040e00c60000740403074000e5045074298004801e41c80380d00e5103120300d000168000a801090356150818546618002c0c08c400d005d040c0309000003c01d003040c0020412007991542000f4109e0780500700752041d1002c5010800d070703040000c640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 191208300 1250 191207050 191207053
    0x114040206070201080907030b0c09010e19120c05060a1e0201021204020909010905060f070e0420090d0501050901020904060503010506090106050a0504080604060608060105090f010506091206040b010614040503 92
    0x2c040155000325100c5600c80b200105a81081e5140c1c0e407000803400303090312100c2035080085080c0c00a5600700b0480342d6280001c840503081c45d01c6c0881e002005209501074010412031020510007003080a174000c801500f002000d0035111001240c00920036565101c01101c54041d90b10f00304e6146006100311540b4840c12101c003006591a9020300c080c10b0303000340103a0700941d1b0310318500000c03d6060000f103005a0810030316074001d0030f090400910b4040404040da2041d480d0100d0005220804014000304849130f5141c01d0700c0c1c10f28000051122204113402600b15400c000c10049828030640c0149019603003102c042010079182c2003403508940c0211881c0c0c0d00120740070018803180d400f4201030b080310001d62a101d480c0079140c2c1a89801e0040550303040703580b039403a40402e00014106118a502401d82a610030071240703800c4900040594041c81800e0103400000380240d455100c8039000700c400202c580840300d050801e40303440d05410350244540000070790844014035040c41100c00711070848200a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 191209550 1250 191208300 191208307
    0x115080d0f1413080705010306061b03050403020d030201020904270213020405030a0302151509010b0904090602040e1f1d13020d0503040305100b10110703230114040206 74
    0x1102550034a050350541c0c414410202c14003100c1d0012078005003600410203250b800018546800280307800c074590001414981404018081030741d01ca4401e064001c01e241c4503490300411800c0170794462259030030103900600324040e024107154054005008010050303030b00304141007412035203800f01c230321101c1031340c40d40d000030000340c3c0241c0b03009045120042c512040041c81d00d0b55400019180c681050720407000f58208000200a400d000070116034000c9100d83e2121007000d000d000103010704014040c07071584241c041260b000c19290b5034005000198880c80c1150743e5620b4503007030071104400311040702d4a00c4071040303424180c000002004007115403600528071080307107004000c40030940090000c0400d4540004100160707032946540f007a001d0051002c1e60381c032425410954100000e000d030340a015810500045450303104c03c8841d0b100700701d9610748908003001580e00d0030300b0010a548044c01f80e20207883c003040600d2912707800002e4083d0700d80c000c101112071031841d508220f404a5000e9482082031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 191210800 1250 191209550 191209573
    0x130b0a121b06020d120c18120201110703020a030b07090b040603020702120c0a05041a040204061701080703080423030d03150815010902070804030f03262404060b0c010e011508 77
    0x2d40010b2140040381c24001c9110070340c3c800d404483c0e84954400c600255414008d034083d941c00c0750030b40d200d0103074200180003400e086401180c4401c40b5484010098000c41000a2000b0b10070882840504141400030340c3e21580c40800030301030741005034142d105490b070b1041da8102c00700c0050b8044503030f0005444d22555619050411009000d800b04036041702541140c0740c8140d603103920090000d40741680310043c0840c2828010308101c0d070160031981c1160300c40c60b0103001003903096041e10101c1e00400120a01c0b140c0c140103e03c0e0401c80b044109405110340208a0101074046e000035a40c0588641003000455882980b6903482c40d8845003c000d0244200c014400203540340c008020250150001a141542d40ea84028601041c0346041c0d0000b290b06032150500b1084101d00001150520740c0440c450a00b0b0040440d13090711100ca0740210b29140c8034200381611240c0000004001d12440c80d501c5210040075140a0003240c1c0e1390180c254600100c5e514a00300c0c0544510035500c40600810004152 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 191212050 1250 191210800 191210837
    0x2405030f0c0c010b0406030c060305060a0e0a0209040207020904110420070609020105071e0b01090c0518030f0a050a050c0607150b0d0b090c0301050114130b0a121b06020d 75
    0x600a500b8155210941045551280e0240030b0007144103424400240b440d08030000c0890701d001d403145215080303010f0100580144400400d42103c29168010707624400000050000c1c0720780c410080d00304200004001c2840100c0051407000c0d14103231010f100d00482e181d15645001c40249425144100c180043c41c0801c0a55204542c40d82c810f05002d484d241180c0c417012410841c43c08258040001790b4040c008000e101809280105001c0c542400325504009001c0c0090150f10466050241d00c050010b1242d50708206a034074908d0000140d40d02003816007807241e2142d518040688044c401c01d420520325081000490300d050303802c0311100c1e030003580700350303540025001c11011940d00074076842044000c5200a0001030244910000419001a0140c145429681c050380110340c030703039800e01080005840d0326540f54820310000b0300c0021032020a5000039070800e8280c000c0d644003c0c2d03128564042209101c41d00040c0b10040300750078011559844c003281d83c0c17200c40f1103260004984600c4400e206a6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 191213300 1250 191212050 191212057
    0xf1409071a0c01110f0705010b060a05040605090a09020408010b0111060106020304060f090513061401090302060d11040e0a06061d031e0c040f020d11070503090906120102042405030f0c 81
    0x30b00800810b00040303021600340c10b900405407055140b20009072040c200a024030542c24000019221b480c186003802c9406410703402140b00e5001800340001d418001503551940900240c83c1400c8110340740c580ba28010750082c22440c4119021a4810400c00c1011100050440c1256410b600035403800b82454000c40c2c82c40d007210f0707842e414810318071070109050307466011010104081860000e405817810f1844044441031001c0141441203010003400541c48001c219490865000c1011440300703003c01c86071090340701d035038800b83e1402000d0081c49220042500148201c5182d82c0d200d000c004a01102a540d40c0180408981e250b41f1000016491645040d184014082e400003a1120f040444000c10282ca00c0032507001c01c940c0d40022485c0b045001761260a074900d82c0d031243d50307003030110540c2c405542c1d1184482c1e2510071500d5030b00040355540c454070b00c201c22000e104004d40d2100d5480c1044900c80701514191a011039241c240c80b4599449a03007940e11841c1c440000502c55121000888003039032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 191214550 1250 191213300 191213317
    0x4122303070c081201060e012a020f030a17070b010609150305270105040b070f0909090503070c090209010e04110703080403020705030f061008150705090d060f1409071a 74
    0x40c003401404d1009400b000014000d219a88400110b1780c00310000500304044a442e61004041c1000c240b498201c05240c001380513907060b1060100700c1c50340c00010307140005a41c4024109c201d003207201c18031200303210b000d050103a00c1800034a40b01d0743c03681e03c150354002c8103010f0300c4000d4141b990f80380c138560b00c00d8001d280c010441c2d040c080501d0758001100304204038000a008030740d230346138028401000598414198080945d140101007a00080c0d401000c1d41d241e40b00780014652602e100c07400b444810720403111002c2d40f005020132220351742c1042d040a900604455404600301103030000c95420076024010001030f01c4000c60b468036a0540c0d05440405010b441034045104105001c07581c3d07241080204040d500c6a4024410351900c4000c0000303020071904074042e1038000d08140c080000030184050b81000d2142041c944401c00c80001c18035480110300f01824180c2001400303080900e2640c020066401c120303030342c41640e80c0d41016003075a0340c00e80d00c00d03d104031986070358040c110380804000e0601070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 191215800 1250 191214550 191214563
    0x9020903010e1513020607080d024803090405040c06090b04060e06070507051509040506030c09160e15030a0f151202030309190f32060c010504122303070c 68
    0x11f0001d440e420000c1c7c20080450200b65800981e0034102c8160841081101620380e422180401030308070340041204076400e41c000818401c105146c0c13082028020f40c0c18420000c5c004000a20300741c10001d040d4030140c415040400d05859020920711140b4089a060342c41c1034407103e050212800c2802000c7d40158070544903400b031443c02251a0f5074014202142e0480c045071a40c88450010401c0111000070308540d10071352000c28283e806443e55a1007a6200d15400b010700c483c0c5c00c060744141e0303409041501040c3d200d140c1c401c140701a40c05060245003d030b040d041c004c200e001100f5015808813031300344801107100381400c0360401c080c0307001c0c0440d110359520140c240ca007401c0d840ca010800d0706035000d80046450824020034020b00c10031340c0500b0010081045964010320b200c140341c400000140f01c03c800000c80752031450003642c071200304032940807101c0c400030800303403415007846000c078503007034041900046101c5204203035030b151080301d558a2600f102e85a840c50301c0300282502e03007400b5000101e603513 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 191217050 1250 191215800 191215807
    0x40c09051003020f06090d03110d020304030f0b060a030804080a0606060c0302100b03010f0501151e0903230a0b0f060105070b0114120d08061c110909120409020903010e15130206 78
    0xa0703482d007ca205813010312a84844100c459042139850400840481083c210f6205000801c042400c88004c00c1641d034000b40f03405071a40301c0034049008010150001342031070200044c005a00200043c00e104103500448007044495110001261a421050005801648648450b4402c40c0780ca17406402c003848020300005079140d0314080d04060f54426030192444e02d02e2451800030894005070280c4042d5600040c0700b90f0b0406001c806040c800d410301002d03098410506c1e504d4605800420440c0052aa801c1100c076868200d05d001e4060900c00c0360004400a0300340040707042d40d40604103503024281d004040c03034000c0c2e0034458204444506433000341d600c421001e07030a2890b43c0d01440700400a800c56507810400c0c1c07400c0030601c4a46d141c403802c5040001a42d81c10b20b80402c045030840923400c24121040c010945800450b5071604000455404103091300080020311400154010000d40e44264000d11208035106101601d800c2040e103a88045044000000c41401000c180d41e10214030003824a0706 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 191218300 1250 191217050 191217067
    0x509251203030207050f0c0a030f03030b090f240a170102040b040b070501050708060607060b040e0106122f010f1e08150a060e1302190503040c09051003020f06 70
    0x150346014001c1d00403d80c0040e801050150078001d145095500300020482c040320803010808420592001900d40c500a041c5d0000b014400d8002210048008008482c141840041c90000e4542a02c1c201003400031a0003014180160b00a1140040f0008007001d40503454044d0328000c500f40103140400340e541c2044040348180d02c6070041c20180000b1300403580c85510b50300d409400c40d040900100b09100c42c150412410b96142e01c00c507100c0580c03000010640c180960045400b91181b180c10410070350070315401107001c46945100ba45013500581d2000c081240c01c2c0025402200c2c2909000b542000c11040107507994096100d45604010b2490a6500241802c0211440e01640000040084c00240500c03890f41a2170010210020003100c0b20880d240c90400050f000104500d42c02c1d000d0036000c0c2741c144017902c1d80c3d81a61008080064001c14920100000030100da00484c0d08403548070601001081c800c2051151500c641084010f64000c60308640800000c004410705080d4484400c208606 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 191219550 1250 191218300 191218319
    0x27031818010b0a08010819022b06021305090c091c050102070b0115110a06050709080102030c0306010f020f06070c02040204031208071b08071b050d050c03060703050925 74
    0x50082c40b02210b00742d2600c009180c0200703040c1043e40f0a030f1403640f1030084c100600c00414100a191541111381a8114102448244545811180c42684102c003d2074010038400c894004204103071545640001c09a02d41c0208100340c0400c0e1034031600310800b40101c9166042403404140c0101c003009002249542c542d89450a80e0b1040800b1a0881442c40041141200880300041000f00da030804800350048050f41503920ba0100b10054845a1220041402d140c01840440003501e094070080d5900d2030215401e1069074001e0300c1482c001034072030b4070041c01c1d60710224218054140382006840d086d103841a00300d401e051120000c0e40e10540c208000800503001c180d100c0000d544503107402d006403078034500c003519600602c2105205080d000260000248188040b11001540440700c5a10380e03003108558050b080050300000d4115507c050014107002001400c812403400c100e04440c0c542c0d84c3c03801d040b03050315410f4074051400e500101294110540092000400f25042401c41035410f9903201c414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 191220800 1250 191219550 191219599
    0x31101030905030d0614090708160509120a110f0d0305030402150a020c0907030e0c010302280c0c050312090603060d051b090a0204052223270318 64
    0x70095143e64417010071203000500d400900a9034119001082850b007804013901c803580042011510301c400c41c8480000c42d00803410b0b50381014014001441d041b60341900f880d82c9403081c0300152031550180103100c166140881d0b002d00499406400e54012521641c0e06944a8002400c00ca0f402074095550450b030321840d1002d44078004040e8020503054045100707000c0340c140043c00f40c108160070007010131040400000c0c00c1350380361428600103a50b0050681c1e800d41401d568403003074003c04081c4410100c01c3c0c0d4003d54541502c0c1c003d42c03c80c055182d8940c1016034030000582c004c8910f0304140401062482c1c00c40245a0200004d08400504001c1d5965641061646000303800410040000e81c041c41c140000116846100180114600fa0400d0002015602c400100ca00111407142c003030340c51301c0b01c1d640090318000b0070019842d2440006882e00350a00b40c044540c9060000080c4650101c010006050140702c06035030081c0d8074201002076520701d0304003145805a000020360307400d4103408266032000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 191222050 1250 191220800 191220817
    0x2090a0f02030a1d1506010c1b080312070201060503070b0304020f0a150f08060d080f070b250f0e010e0604050901030501051e1006202a0a03080403110103090503 71
    0x954415130f000d00728200e11100448041580956002030001400b610090b81044003400c0c0f00a82c684c036894241140c0d024070f0940150090107150009022800002030441c96440c5010110b01d543e8040c0200d00f220310500c40c3d140e04d0b0380118000c20584103610000c5030483c0c0060404160a58050089000b010050f4031110310031031141c100e82c0c403080d8480080303e004a41450a5411800c1000008403899508180500411000902070b05488900303001c07079050300d5001500ca192842d0020340c00c2c414151090369190002c1005035201c0d440c51181601d00e6092900d500c414003000040d02c011110024500328403a048001001302041e555503001d01e050085200780008a0305181100706600c440c0300c06036412006040207003e0081c0040c0242c2e02100381d07029840c0c00021880018007841c031082c0380d01e9210220b4020306984680460001c01d0703000300c4102405100c08030039446820301003240d0852202030550308081c807040c8001440b42c12450384400d414500032a040000380c99185c11076000304503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 191223300 1250 191222050 191222071
    0x506130b151201091a0c0f04031509050f0c01090b031e0c0405030304030c030212030f0406050a03020904050702100606140a0c0503070219031203020414060d110a030207050106080a0c0302090a0f0203 87
    0x32400407179020700c000a0303205c00c00c408050b0409403903000d010941d01841c08000d28102c056081e03030a503444258403d4096903040303030803209002a209407160316102420100ba0019050410115071154440c084a018005080743c075034507503996044101074004050300100d0b1110b410480094a5581000580041c5008001c2c1c0e02c0f84034a180304003c0c0480b901000c0480e290400e01034200d1680030740050714200c03007860402c117070340d5000240c00700c000f0310422907110f910600c1d00050050321a400102640d8000c140b0710b003007200c5a00d40301e05560407422680c8042c4061001c00003540c00e50701ca6010007480500c15030489003842100d60015412900380304e904070b41c2d1380703003c0e038108184104a0754140e8030302040d00341107207018204801c0346801002070a2981c040d80740054004406401688003000500030202c046071036540741d0b030006002e548144d00c00d80703156007000404031b135080b07000c40d070790341c201e54082000c0100c80d1440d400d2180b98040104040c01d0f0b2655020003240c404141d000441c844c400180c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 191224550 1250 191223300 191223323
    0x2042a090503011a090609040309090c0c050105060d0b130c0e010e071b050c0906130e030a020c0a050a060809030f03010303050a09120213020309030c03070c030506130b15120109 78
    0xd0070715085035104004c092800c1d107016039015460f100d990400e40c2000c01541d11240030ba48500301136071051100c2c0c0c0100d1400345850303220080c00d50b2001e0301442981c03241c0000d01603511440100b00c2031145061002d0710580000e008160714550a1048a200e14030520803090210303038543d0340400a10003680301c1d80783c0c55030610810008551150410006848076003081f0322b0003800e915900d990b41c801d044c5043c040c3c1c240002048480d0b442c454901e540000721101804402d002103c081d840f0340100d9240c0016100700702080c0c00500e070036507030300040d203401074003024140d49000401c54403000050030384c50f1907010400414040c00c0e28180154040e40c02903d40360703034075100d0310001411840e41c2d5024081910300160040c00682e900c11a440944a03034600260300c80d00e888905e1410340c85610070102d01807100140701001c00041404500c03c4034090320981d02242c2c0c907406e9680740301c1c801f12002420b04910a0000d040c04242c04015901300101401008600442c0b0741410708440305400c0a552a1344d160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 191225800 1250 191224550 191224559
    0x901090501080c010809031e0c060703090b13150b01230a02070b0c1906060b0a031a010e01170907050d030c1506050105040b090f09011203031404020a0302042a09 71
    0x40007014070f016000e00c0e2107582864005409030303c9002d4500c3c42c0080c1c0c00e08281040110720300b031084c1c40c40c141c0c1c51410b4070303d542850000a0000c08400504a980d4511540011a10550040c0000d45030380c004004030840a0300c282000024441e00a8540c1031100d0149000c21b401048803185c4c2c0368001c41044a40c0d600b110000180c6000c1180c0d001d08211402048158401c01d40403582001e070325018400d000d039803900d03407525030082d090320f0700320440c4498082500c1d100958590090020203410507481d45481e200e010044034000300330160385000c01c0c18681c050040f032060000c150781c46a50710b002d58104940301c0000842c12401101c0070760024060b08601000c2c00243d52000b183c8940c0c01e142007103038a02d80783c00602680074500c28410700da900800d140e030103a11007406421044c04000c1110700c0070341c0c55100895810384e000310107600007441d00b03030302c04114100507040a01954009004007400782ca99401c1001500b0343e80808071040208051004407a1410513403203204104c0d0361100020542030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 191227050 1250 191225800 191225803
    0x30503040608011a070f0b1e1906120201140c010f0903030c030c020d1b170307110d140d0f090f05071d0f0411030a1502130603021804020c0a02090109050108 69
    0x840c13007102000600700607030400034a050702c0c861807039680715680c0d00310381d43d684424440c402c2c000c01030354103c0340350041002a4021000140a5911140c003800c125454581d540010301c040c40e210000c3c0480c810004d8003038101c00100c094006000f080d03002150030801207202409807100290b04038007207902c1c1c4e45d4065042d50180207102c41807241384024075100c040750704010140b024903c0d10602160200450300244401c3c0da60059010010b590415a2810700501c0201180e241450741c1b00c05002c3c030751814080750b05c9000e41c404190400c04540303003050890f80e4000000d107050454210380c01d940d4201d000c00103000401001c2154002d401402d10300b1310300340c06411017510728090030782400070040412043c00e01e024001e80c0c00075000104440304020078070100e445d00c40382000240c4464801c00380c00b46803005ca90000c18010b40c1c0003901764200ca5445c1c106505074002d406c0320412000079a0511142810030740e010342100c94495080302d2115005130081400141c0a0300b00c0070202e902e880061200080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 191228300 1250 191227050 191227079
    0x7170a080106090e1902090120030c0f0304121205070210120605030307031704030219140d08091e07120b060306011403030301091e0212070e0301180305030c0403050304060801 77
    0x701040c21801031410405c00c00c119915058a401580c0e4045240240d0784d03c41c8190851168228a058600e0b0402003913042c0d50350004400343c14188610b00c49010840c0021055604540032001f0190308000d8941e508c050f4040c10040304810020f0520240d80541d40b400d51240d8899119100d01c00c040101c86110b1003a030303a240c0c02181c020b62040040ca00040d5101c2240b1000d44a000c2c1d03120242e8440e490b00320304050502c1d040052041905601500b40503443c95510941c0050a0484042c0c03810031101395a000000c961000e1644c0020036102c04119803aa90550112140c2080d6a40b680d1100401c0321036011340541aa00d8001900c20840795003010005030303016200c020468003078082c0c841c1c0003030f5503480140034006c51180c90707006600300c0146421b101c109040490405540303d030341c1d010b286941c100041b10780c1000070360451344800e81403c0620480544003503010504581509688007911150300240c5000328040b020003000000c110180003500c0900090741d51080103501d0002c800c80d0541 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 191229550 1250 191228300 191228309
    0x92703231819081209030c2e0906050304030c0606090e010605030606042f040302061602010807080705030c13050307060305040309141809010f06060905150f090607170a08010609 78
    0x420560103101e60000024044031407240032041d181e039001448040313410115201443d40d0011441101e2507a2034042400603841589044400303285c2d0344010f58109c0d02c00d03aa07442110701050b4204003090101e489107262102d0203025000c04281c59540d90101c01c00c888803941440c0003030b50b40c1c4005108900c0c1c240031107030308071b10116010701450040070300c40442da80f402c4218244054000406100000000c1c043c3d4004603002400c280e02c46090854071001c80350fa00b03404a000503902e10000350f0190003107010501511181c0c1d01d440c15039032444030301c240075441035a1002036980c079148000340551b000c02002004c0d01d40307560301140d2030409140280c10701c0350035085071200c51203100c450042c0d915045800004145001c100301060345541480c1401001e51200c040b90b01400c0c64000301e0041c1e04041c824046910680e24451507080380710351000c0c00d01440008600e000002c100008203454560b01404a550040345084500c40084080c201540d024590210100700040010030a00ea04245990001c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 191230800 1250 191229550 191229589
    0x50306013f1b0e0d0506010605250308061903020a0305070e131106091518030705030307030206010e180304030c05100507030806040906020f0703090927032318 70
    0x1144000c01d109007981c4102c0304402c001525030180e406a4032145030785103040c0c024041d2082540c403000000c2455000440b020401044c507400c0c45407a01140303e41034030b86034255562500c291a40e0040243d056030030889041c511515600100160f5a00688a0000d61048004002440c6000800070403408014015203072505407d50f14804111100d5502080044c21501a503544811b500040d500401d0030a031080720380c001065407038110805440b0b41c1c02c280011030440c1d00c0300d650381007015900c0c0301d0a003005006070403802c0100104088031650541000c1c1c0855408a94015010250700d140c110758029510b0203001642001281445a001c0510034802e00d412482d101d0aa1406005c14070040c1400b400342d40d0340c0c0f03d000103022890307040d184040b0400c18950b980c1d454034100240040b00c1e0f070050856551504414940400c581a4240119442c00075030f0708042081c0c2d00e0075141c0600d07074031040c943c14225000c18001c0c41c080c0c8004003030310b0306003643c0300302e01d80c1568092140580000700d030503108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 191232050 1250 191230800 191230811
    0x801111209160b0309031303110315190209030a050102030f010f0e0f0f06030703060204060e01080a0e070b1c090609030f1812080702060c15090106030c0501050306013f 74
    0x2c407003142c049600b620f034280c81103a607a480d6074040600d103200c0d03c12000b804402803000441004401e128500300701c10300718100c50301c0030701c0100c542821500644062100e1440d60418140c40b241a40140c50300d0720006090321803620302c0752210350a80e401120320f100c1d00d413100801444884446104030b80500030b4035801c10780e540f4190660f4070200f440581510244001d4000040080d9802c00400010b154045c500b90b403500d96801003c0e000c24141e20109003c40c90140005034400300c00e04c250786144042400500c0150b203031004a05040d03200c198002c40c80c0e41444400000640203000740c100740e40c8030724000034406c006c07030400819042e4020404010000040074280c0982010031003281a1040503100440ca2503203454080a20700c20031a0003504858081541e00000c035001c0341d07041458680c3e086090036542e0b010b014900b250f01c1400010402c01107080c0a214035482800030f1340e070012060402025134901034407002c803114401c0741410b9035a650303207452400607403400700800c03074103244207005110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 191233300 1250 191232050 191232073
    0x909090109050a032a051b030606030c10090306051006170f04021507050a050d0305011a040e06040612050d021e1903030603080307090918030c060b04060801111209 72
    0x40310210341c40d0240800484180c84841c01e203019040007900d1060b120300000c06401c9281c650341f00c0c90640c036985503641e041021002d160401007002031007000000d0103421a454404100050044442508401c201e107a1401100050f0288102402100401d446840003442c01310014071620556020021501010081c004044503282c641e9400581c102e0301603403400d1400710460028003416401500900c11058003000b800713804945d58110643d0390340e06200c16170321150f00721081c81040c104110030341803c003c20440d00e04c031840d105030030420080010481d2070752440c4d2114a00c262240c25101a0071000007507415a404100c00d0503007645070254440480a8220115215403000701035600c2000c607000b202d020181319078002405035501c06400e80d100d0501c440c0c0104201c00318045c4400862401c0e860084150405484548065040e41c84e0a01400184e48081c0500b200b644c802d0780140e203c40000c10400828058a050415800441601c2d84900e0058a81c0c20f5400307403085440340c0090b100000f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 191234550 1250 191233300 191233303
    0x50109121101030e0d20070305030f2206050c060a05150f060702090f1006030510121103060109020904060b0403021c030e0405010e0414010b01120c0e0402040b090909010905 76
    0x44545801c04a450504500303040142c000d4040c2122031015401040150300840341c0200000740035403c0c000c101204104d84c821865550310071408003814940c802d0185981015425009041c0643c0810900e600b032594a000300d24102016000388000c523202085c0101e4092040211603804240f011052080d428003c07600c0320105220b0001074050303010b4150055003a201d13242224042030340070300100c900c3d2401801c900460038041c1e42c0d00e400d9001e2080001290307882809003c4c028140d4584000d00e1034540001d00d480690110000c540d029801c402d0101140d41c103020703480c000c02c0c1c01e5401594880ba07620421044038040c1d003044101480c02c0c002800581c654116a1b903088052402921540049080c02d980300288030003103d9000b0b080000216a10003441d01a07400f49214840d00e13404950008906801d07655103108160020b002881104204c2d0240c3d04105c0d410403607410710f0350290580001190990344160403d00a05000003031500d010b04203052038651001151000700000c03101036a5a6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 191235800 1250 191234550 191234579
    0x6060409032109080417070e04020315090c0901080708190c0323030304060c14121501050c030c0d020f0d0e010c081213031d131116060e07050109 64
    0x300694102c600c810700a1407450351020702c110350031080d6240c8503903031103194003600012821500201e00801800140141603015240d0045a00a01629081c03480d6246001c01000c0140303090600e120f5082010fa80740c0300d418045000e44240b8014118007810f105910341b0f01147d4800d062860440540c414010030464010681580e0b404010011451801c000004a01c03c2c1100c0d1200d45000002c02d020411210394000301e05050301e80c40d4607551281140481119000700c000d8500951030500c00108072140c6124070b0741582c00705051050034500c0007841e0b5440c5401c0754164003401e60040c0403440b50740b90100001481c070784800c40184450314224200510451144031003505002c500480c42c0204502003080d5503001d481c544410304503251102e1038618020070800c080d03020a40b21454a0882c250b600e500030588080030700b0a41d0610b01004400c00102800d0101c12007248080c825149503c1c0d00c1c4000f50580b5008240c0411007a8440746554141802640641d05015003000200311650500190 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 191237050 1250 191235800 191235827
    0xa05060d0e0c06180405060d051914030c070e0c19030e030405040c03020d0e0c010203070212010f0c02061603140411010201091b0e010f0509181c110606040903 70
    0x895103490005100d03150860500ca01076105801103001302e40c04d950315031030034104202201c00307002a80740c05d004d0050b40c40c40c0c0c21000c0c146820030007004003112103c10380150038030f205080010714411244441803c0d40c10030b4244030030540141c503081142d10454842960006032001001e80f5201c50029424081003081e0000001e242d180c08802282c054240300365001004040c0003400401c01c0180018002d5020800250f0789901d020000c281c40c40000480600507203060b00118a4507400785c0070084004d000ca400581150340710808501d501559000c1e80102000301d800078000381c03e2500ca102c0304010390b440242c04051078842c0c0440560118065603030000e0f008440705840013090f000403805880c5600700504840c809010031644402c4602c03403178046425440101c455643c852514030041e03c4588a620b0340501c0e0500802c010001c11048141c0f2060b00c0c00c01c070788105800101c00c008a0b11904200c8000c504c51800304003d03071600b480100d80c0280119400c10510140fa6170250030006494030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 191238300 1250 191237050 191237077
    0x1020403030e090c031b070c140103050a0b090714070c030c170a0309060c0f0c06050c12070506150604030c0b030f0a050601020a1b090f020c0d020303010b070227070c0507050a0506 79
    0x40f402e070745c0c0c09010125080a504000722030f408c0c5450703480e030300c11240c103040c3c00714002403030840014850020b0348110b03060fa040040001c40e864441480072200600c0a28940981100c10400344c00010900c0c3c402d40029132141001c840e81a150040c081e21840800303011480e1034010082d0b010000e44d1101e0726005807031a50402c4020140d06090500d000f815050000300030203481403011a2154001c4041c1403ca009401212595880d081240c40ca0740202710000b4070a6002038042100d0910801d2401724248000e00309900700b40c0d59032540c1006480c59030080c04400c0c400810300c011980b0300d4421540c8690280001d11950501d031000035aa41c00b020800743c0b07140c0b480c04a000c0256001c07441c1c000244900e100a2190301d808462481c000c6d030210066031074500c11210703140101c40c00030003038134101e401c000281c0d07007400005d03001d02c1041c1072a41095004400c4102403203514087c2014100d004035542c0d030303c20361701514907d40701c0d24281040c1c004034401c038014202007105030344900c1101c044501c00301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 191239550 1250 191238300 191238331
    0xb0c0a0303020a1b060501050a0b0c12090f0303030a0b0117090a06050a0216080c071e03030c031407060e010506030c0f010516020d050a0302101b0302030415060801020403030e090c03 80
    0x320380c1a01c081d20f0030038601c82111341c18014000d0641025040e10070444030040101d40d590320480c054440d0a40903001608035054042d0b54400c000d01518036914007510311030880d9100c1c2c2c0000c1c01c55108850713009049513210038280d00e43d40c0c08100794070040511403400c48541410303194241e846100d00c0e00102015201c0f40080d48a0720711b078040d281c1c101c11000d0420900b4200b0300d886400e60b0095104041c8a11981000055807042007249414458400040c50f00c001e08548048071006a04001038050081c801c01140d8071300c541c40024400140501c90025903100e03640c1c1501d0035183c01508491081e4070089a454180c1e60f80183c040380400c0900b002176440084800300354200d800c40c1c001030b41c81310019468000b80b00000c039031040304921903803c0d40c204955403c900d4003110103d15181c05010401001c1e00c81190080c0d0041d500b01d8040d490314400e01c40c81908030400c0d03400b41e40001d5440d9401141c00c204150b040104e9804083e01207540d12042c0c909100191b850f400000c105003610b11500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 191240800 1250 191239550 191239567
    0x305040519030c0f0317030412080a091a07030c02060105130b04110f1903050403140d0e1608070602030f12071101020c0c1206090703060209040e01150501090b0c0a030302 75
    0x44020070015030344030041034002580c404440c1301d0380c1000d11007a40c00c5052505603840701070700d00382102d00c2181d10a000e1400240700d140c1c120b400a00007442801d28a80e00c44001000c1000c8100125840c00400a0341200b4540180c000b415a40862011815035100c0c00041c001a5141c0c03850102d01d4181031000128821100c0001c0d0143c4030011030399925038000607031090300742d4202008140c11808036928a6130200c0c2808201c00b11030307044402400023018665803040c02c030400001022100c81d11400440c1d07a12100f0320440c200001c80c44a20740224960404110407201400b40710020891070028509041102103849103610588030a0000c081810b0006000e6a009070111800744441d132008540720317110082c1c0c4940e0707820445d05640c800c07060380a44030311141300011520310800904000d0304440c4d10b55a40c0c00b01942080e464035038800d40b68992010700541c01d2050a00d260344000780e05103070501d04400908034080982150359174050421540d208064005910950154107240040c0c0d82d5524 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 191242050 1250 191240800 191240839
    0x1c0507030e1e040501090f05131104050c19080109050717061009030506010e04021c02060a0c05010b060a021b01050a0f1805060c030309060a051e060f030d08090c0105040303050405 79
    0x100100701c2d03480f41c84d000c008120f00125521030740c1042e082030420410345e11002160709121015040041203204a01806801800e107904050782200c0f135000040c2c1420505040030b941004050000c8000420749401005402c601d401059007200c61410300e01c0c0f00302d00ca0741680c2101d400040640d8051b54244c905410074600c1100000c00454110080d15440d5031105500d15410380f003640c040c0d2007035078000b81d444550103145030030840490b0300410480c80c1060f841310546180c2c803001e0342520295601c40032080340b42c036141c00410404203a54003401d900701c10040b0100765074080b00401d1741000400c1c4032500c032080d00010200d55600560500c0c201c215050400520010180d401c05a080580810030456881c0c0001c042e50090b4020070584009942d904040c0084420890301020407900302c4000c00c0302d4188040b1b00343e030480030281c00304c00030031709c40c7c008a40f426000d0030b440f0380019000c008011160605000c10923900d442460030615062454a000701240290300800d8403d00e002c5c40d4480440c3c25 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 191243300 1250 191242050 191242099
    0x806060c1e100e0a1202060709031b0e07020a0212120304021e04110d1802010e060d0608010905061e060d060c0507050109060c1403221707051c0507030e 67
    0x11881c0c003403040f20360740c030b00482e140c1c02410411501d01c1031440008a026001007101d0380700d4186551141103443c0f55450f4500da00325603003d0009440c1c040c0c9404a40c10301c555903c140714009940007030100741c10520502217040210784420510360800e18070440740040c2e01044940003601102c0c018400d000d4000b2911608000010300b0f81d225140216080c81c803200c0e18080d1400c0c0058200400515103e81c3c403401d40b4140542d4000d00049400c0d200300c1c2c1501d01000640b0351421074140004a00d174482804a003120060300065409a00140411003440d61103041c049142c1800b0031030b0740b1541884004251900e41c1460028007041d1102100503829200310140c40c422500300001344452101401e000c001001d50340c080e0000200200000c24490b0b030200c0480b030140b0724106200341e8007600c45d0300c1c00400c1d08600c001150b500ba1004400103031182104041d03c0220300482c084c0c0030500b100f40c2c1d4221034484081e081400d01c01c0c1840980c021a03088140c2d020080415034082c00003031441030300c1030440309 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 191244550 1250 191243300 191243323
    0xe1510020f19060608010e121c022712031204030c0f030f02010c02070302010c080c0a0f1a01090513061e020a11010b0301110322020d0302010b010806060c1e 69
    0x46000c8081c1c101204088820501c10b004010404c511130b00d40da1101c0c00e84000d521107481c16070204240350005400380700103100381c0c01084240110f403200076000070181d0340050060030300340f10b6501d81002c1ca05009201d50854071000c4070030303c1d001d010b1444126244d00544607015064507201000805160080e6501440f166204803d6a2001d80342d1a01810b40d07018201900019803824800724203d0f030000803d1020f403078050b1120318241140303a4a2140582c4403032030140030344c040c00b4011710015001000d10019507108505c241301c015841040001006016032041e1078090604042c00714811ba031548a8140f903800640210f02c04407400041c0c106400340303d10f00f00030313244001207a083c480d0344080322180d144803c400038400303202e00008040c241d502d0900c851207800010400b14000b112414000c0c10301d40300c188190025075910fa000681003090b200740c1a000340c3d4444001c80d0913580c0c030080b07580d0700103400c50350503050010b81d84007295611110111400143d9140c400760909130400c1080d0400301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 191245800 1250 191244550 191244553
    0x90507081f12030c03020601081207060203040813080f160b030406050604060510050a031506080117120a031e05010b041419120510020a0503150409060c030507090e1510020f 76
    0x1c000b52500515a60404030300342e0043c043c80c0004294400d000c82d450782c4600a4401040c01d2841c03545642c002035101030800c490f00300c0100402c0254040000d50700c00140002400f52000c404103030075560401c10b01500c40c0985803902601840041c44c5c00e01500d0300b0503082840082d00b5910f45010900038070349030300302131b60000c81c01400c0d2100319400f41c01408100910307030f4180508204001c1100700d00520f402070201080210300144040c0541c000b4043c2800400022101c103c928140c0307c801c158403105100300001d0302c82270046402c84046015201081200c0000c105640c90f00346a802640030768020300d0012107440b10a120070780d40321410059880c180b50920882540d030385151725460206010125600d000b03601041421800178401e4940c40c24050710b60318910342c1c82c00c42840c40c3d185960703412644150b03600400c4000c10300911500d05403169640700020542000c0101500c0d20f00300783e100e10407451141041184160900c041c0412045080c1c40c10101703031200300400c3e07042403400907009216 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 191247050 1250 191245800 191245829
    0x7030c170c090a0602060c0a030b030a1718010513060305090106171b19090c05040306090b0f09010911040f0608160518090a020112021b0115090507081f 67
    0x2050301d5400200b800707081c1203d199006603500c80c410b0781c45180480d88140e10b00d10038403450f24668042d811121007c1d20060640b02000c0541d034990302280414441c03680c5005000c114409052840b0b00807074136011003404c0031800d010f440740e0981d0000702c05004503810951260040340300c400094101d9000b038005800e04108076425551655606c03604880e420842ca5000600c2c08443c0c10105074042d107600b03006807034440301c50803c41ca91014096124249003003040c100400404100c2c0c0344034020315148585002103d42c00d01002500d80000301810901069240111803130000701d600d032028203100d1007524003048041501d540d050080a140e0b01031601c5014540034000701034016400724013a40c10440d811502a4140082c0e510060003c44403100b0f035a1001e81c01001541c01100c9050302010403240161a002ca501034078010302e00f505104070001c1c7e461717a9116500c1180301d4542e0b0b01914050303000300310b18540001c0003030030b4100150800c80c2c400f909085008068031080d46900192440b600c00540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 191248300 1250 191247050 191247061
    0xa020d03020c10021005100f1217120f0106020f030423030d020715080f060919021908010902030405031b0a020405040b040308060916030209030f07170d020c0907030c17 74
    0x417142e000c29040f8103a0f52601c40064041c00d00c251520055030503107170034130700e00d03a040c9400310104843d110b4050340c0e80045d006508041a0201c0010010402007103407400f03050410241483e1002d1068101c401590000c8500040c40e84000007600d040701c0704201d20a030440a44000031045002050039160140100e00c01c3d003030295000902001110118100760406450f00142180d140da4141d440e00d0500070b000000c07a28915007903142d1500840000c02c0f014010020700007540499000609030242d1450b0040f00580c4d940d08886110300600314a102589545410740c0c68940f80d100700711a0300c00603240c403220140e060008025140310560b0240c001c021a040506007607080b84000c980441c0001e8884c4001902810001d00407401208c02100c015110300030124180c003e034100321503050300343c13180e1003050703441110805c04d003030007001107900c090102005055082d00b8080007800800541d44102c1e04121240c0703c141245600c1401441c0c0000d40d030001c0d10003102c1200402d0f0841c1030400303080c4103026 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 191249550 1250 191248300 191248303
    0x7050f0f0d0b16080a180b0910061806050301090c0302100203070b0403020114090c01020c0f0d060204090e0d050c07060f090b030a051005010e030307020409050a0206030903090f120a020d03020c1002 87
    0x40f441946850301c40036542e55003142401d81391000d0500c400e94680c2050f110008007594000380d004070740c902c2960002400c441c051400c071840d0380d000110003041d2401881c031112246c45450f000d000150000d0140081135141c18091001910009000d9401400c2a0034800d1080c0305076900c0c10f03880361600c80181014200207010b07092610b150288100f60b100810550f0030f0001c1d10416002c0d06801500441c1c52060420860952810000b500952030740003440c0014454802400505002500003809068404040385040d5035030790002d007848020000d941503031400003031150860351245800041411005c2d03044034402c1d4180c0c85882c15000110a000000c003030340c1c101502c908650071000c0f076000d41e039800449260f822041c8003501604204511000340c1072640000241c2401001220b9640369180d000c10060703801110072071696080842d04802c181307450b5040119680d02200d84400c10744040c1401c42d01d0b010103050082c4100005040c480030103000380550040e5030001003085125050000303010703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 191250800 1250 191249550 191249581
    0x120611160303060b0903060a2c16050109051302030901020f07051b010f050a08040809060c0d0e0d020a05090612060c0403150c0203091002030f070f060b010207050f0f0d0b 75
    0x80700401c0c00d2050106440403031000fa81e000420007001410a622141c01c8140144148602c2010812450070910f110b100d51198030038240301d100000300b804c0c2c00421132101ca024501c0d000a810461203190422190f0707a410941c034529030078001c0044c0e8a4071141403a600a2082620a0909500100307801c0180000802c0102c1c0c010000c080101400c100d84004440a40315203101402084050006045c1144140c61056005103d0305016107440c203400009142a00102c00e00390142d400340700021051944500c210b0070b01c120944011420405d103900080a15075140074180c044c0031203c0001e040e80e42d81d601216840c0d84404160384503414500d42c0380009512501081d5448004540710031003a00041c414500301a1640d0f02035400c201d210001c01c0203401d54900e8540c01c520007400004d0241c603504004010b020301c01d44629210002900d4003030151000106d01c40d040d5000107a080125803540071106002e040c04540440044040d02c0c0050000c4032803000107040450524100030040340c44640700b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 191252050 1250 191250800 191250803
    0x5040c03020f010f0207090902010e031204050a060f020a0f0609150209030c0609090103240c080a0e0303042307090e030901021c0c030c030302042304051e0112061116 73
    0xc05102c25101c00064641c04a0b4076150401031303010050811400d44039510142040d841454409002004800004e180c0034513034800500c0e85100113010040d0f81350107482c100c02041c10f03081c1114615003116010b5214021540003030003a00713424200004000c06580030401c540c0e130000c40000c0d03040d91400140c000350840360405000b0b00c504201d2864502d081400c0e2200c81900810a0f1003c1e801c503950051071260550760340240750380540e06d02e12591128019002078140030b82e140d142511741105004c050320b80b40300300141d01760405c10a00c4081200f000340000c1ea10950013120380800500f20107189004840e0303004200d45032030030002030403c40020008100c0c1400c241e01303da08581396413034070620710600041e24001156002107c280000d02640d12040c0140c000e040c01403c149da40c41e000e107864180101c3c02c2204d600c0807070880b100340c60f180c40b42d65000720911015642038540740e00c00070b001c00010300a940d41b250000300024200051500802c1522822a005944070311014561310320360072034900f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 191253300 1250 191252050 191252059
    0x153002220609260f070617010902034006090b0a050705030a0921080702010c02031c02090402210406110a0503060f04060b37050a2105040c0302 63
    0xd0005000d449152250300f80c40410400320040a410075408051a4141c0d0301006070313008003000601d19400034046500284015160070001c91264000e10b241408140c010242c1c0038030500522600c01700300380c121000b191b01100d5082221085030716020300c000604490405512003500035404104068000c0d4510500c211008500c07a01c40c40d2040e030684904454403c0040e04c1400041d0918a0325005188440d0003011800010080c40750200b0005252040a101058042d001c4c0210203034240709441d801d034100d1014608262420713520310560b01c04604810941500880d0b6401c65a6403681203445c0e00d0b485074652103001c003409615001e4220200ca0540d0320515000b402d0005001500840d1030100c02030740d034a8a10399070f140400c180c0e00d85444417503411540c4d0f0322010860305824402450a032001e0200038080c4151281c021544080090700d0b020500c5080d116050b031541c1000545111100d0f5080170040302c45603000004c03800c41e5198800c0a042c2c01d01041c00140041c020075101940c0c02a10f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 191254550 1250 191253300 191253367
    0xd0605030a12050f0712050c06100302031b0301020408061003120201060f050418060501030305090f0a0803030f0702030c100b0109050609090103060510081203090601153002 76
    0x105501c0d00c40100000e08039004022000c500303544250028507840e214a000d0a040c59496120030b040340ba00076500130007007840012a60750402042000c0e56015100083c0982420b0555011030b84400c0180b95041a000340d004001c401c982e03003901590040c1011004039540b0b4074100c060501580314034403003030380c103010009000c82d2a2481806980c080e240c0d2916660307001858039090000a00302c0d203035050b06a1681c0e14018000840c0d6000e02e074000d5010f6a206502d8a2283d0b08100b041c0c011031115a00c9460b02100030005440040203407031340442c80c0440d00701c0540d541c02090382144910000d03011107000f148400011a4480d43c4030f66503840b42a030707500350301c2919501031222038810008469445142a070040000a0080e04190307804405500d4000c0751590390800c0a00e41124114907541101000c010407071426420031159004015140190700341c0843c074038000e0720384000c00c5602d44410010300c884100c0301e800c4142e0061301038034440341156150000d1385102124203042007099040340c02c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 191255800 1250 191254550 191254559
    0x1c02130315091a070f26060402090418231b06130b0d150e04020d0201180603051603050c030c032208130608100b2508120106020102071101030c020a02090109020d06 72
    0x707506295030301d5032141d100e05001b902c2c10844450544020001036000da02002802441d1311070780628120700c0d86224911070213440d80e18240c40c050344031210700441040380302c080e82c0048000281c902c04049410035084106102440400d5841c41030302c41c080c0c982201401c000501c0c1c041c0301e0051804a01d002c40400c818420b0101d00c4601e0b0605102da0b003200b4610002160141c0780c004d210400c81481410440f00a8507003140e911044c22032a0b01080c0030a070b40b0410003464070580d00c4000303040407880c0f03070402131131400524095107800050502003003280040005034503d4040101d51008841030460810044158940400c0301d42c05006100e140010744500010044d020b11004c44c0103c003003801700b00e81a42010b14906458201c00d8074807281d00007071101c540e00b03030040a0741c03200c089000c0c9440d9692440b141d4200c01d680304060348800c046a2041100c130000c01d0481007400b803001d1003481c0101d0710383d52900d4100d00d0041141d41c06944062041d000190302030060380285880a0304c0c4001b8421680e68 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 191257050 1250 191255800 191255807
    0x503041514040605090304240327140f0706050304110901030b0a0b1f111f09031e050d0e0a061505031603022103040f03081c02130315091a070f 63
    0x2030f8414100c4d2031842c44001423205900764050824844246030000d04004617600510b07100c3d040d80747c012041581d00e50b091040c401c01c11402d0b24032201000080940b0400078101c25a940da1900c0341d18200980880450104825604e040040f030200500c0085a540c49090003410b00c541603800d210260301c2c14541e004103040203070201c104a01e0003045c0c10b1407860422000d80740c3c02c801000b0030025001e00041010345864500080c80c0c9140707408000107030b0459170300c0d01038000c02c6421405c400303c021011249103515442012140c0c4207041032404182c0d080e07000c032007a00d0300c00c00510052130701d1700380910702030945602c1c1c0e0598201d0794114121040d501c4040da42031034543c101e0102940210a15130680c07001d1100c40d03000030b01d01411314116480c159444040c41c0c083d00c12500b080702c40c81000148200a0079003200000c3c10021081811460040002d40d00079201c002c0d40701c01408048444210303d60310f18283c1c04120190342081054081d02d60300a2280e56424048880f1070125116001c1c88440510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 191258300 1250 191257050 191257057
    0x30306010e0f0d020609030102070501051006031d0d030f02120a050a110a080402190e0a060801110306031c0207090f1b020f0303040b090c130c0909020f0a05030415140406050903 78
    0x74003925083d890001038007400700d20741c0400c03034468142d03408025202c0024424410203105041c100b90307000e405824910020203070350b007024041802c00c0c04034070402203450012a402d4240400da050000d10b54440c0c2c0740d1031020b4010f810080f00e0004a40c800c0200340c072140e402c503078403400389401c0c200000321511504904034000c0110b003000203600c1741c00080c010b007010001040d081d01c0016118070407950740c00c00380707050900482d07403003200c140c84103020000d100d0300340541440d045007130310a1402c528041000ca540c0752660174501d200014001c200307241090092104001400000c1030a10140c100441c811001d060380030075071300d42d001e01410198552840822101c1c88200c00380040c503c0c5407075a85072692007a2024004203854000c401100a4690700c0004121000f40d074003101040c14540d165024200c9845940b0a0034035038010402c1c1f082d2800003a040710000d02c2e07207040c2961a915142020004007a14907085a00d4a16001c10f17018084e01e181400740c4598845d510522880d0f03140b80c2101c0e282d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 191259550 1250 191258300 191258329
    0x20c070b0a0909020c16081501080a020f04091104020d0603173105100305010504051e07050a03090c09090519021503130b040605180102041409090f01020c030306010e 73
    0x1c196103402d01501e0b0842d0020203611600b5000c507640d070403031600110804a401d0303102d41540c0e030000e0042248c8243c564109801084680c019010000c0709402080000c1080460144940e681e590042d080001754800780100c0b00d00a04219150385910340c3d80001010580000e0b02c2c0d5456100d45102100b5402c011222001c09034242c854100403160881800c403070820b070300030750b2600e110240403c544d140d1046850f071103000ea07a40418154500b001344021100d010340400501d80c254108080580110b4425a4100300c040c13130150303030b82c05040300300320014192101c005200d00c40342800081c6160700c98020181d054010010f5070381c0394040c1c07100c00c0c0001001340002500031440144004d601074003013014503440640702c00c11866001c07c940d83c00c0e020301c0741143c0894455a07100280074406042c4c0940501803161031000714900350604503031b0400700d1043d1000d184908003d00003e14071420034001d650300603108000070740d264882e05810944a40046814600242610102400780d1600041414205 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 191260800 1250 191259550 191259557
    0x11030f03090f010309020102032506050601080622060b04031202120406090302040506010e310b0d060c05041703030703180b0a050c04081608010c0f0801060e030109060203010603020c070b0a 83
    0xd02d94005401a2000300b00a90543c003081c0405269030b5039940c11400e44090f0340b101d0790350044052610008880c40600068100001103041000a888202d00802030502003060396410703154a24448002d80500d41100712182008a0700004210440d101d001c03a003c099000e69031070310f000b000e204229010303c3c0300300000528081c9040016040c0359121b5500310006142008888083c580402c0100144a2058141ca2030f40c41c0303040b410b40b4480d4280800503d6a00702407140c1d442c2c050010f1444850040080e0030b6a0780d40c00c81203442806282285d00804030754001c000fa000c3c015140c103450b50000c0b580100440d00700750400880d4040c200e0801d901a0f80242069403079140e12403240002e12000340b87c00c00c010720402c0041501001000750080c40000400c0b1504a20704010307055003529092031805e0b003404400340412507902d0b0800349e458191171142c07628007d0801907400181c054060840090300e010f200100100e045a416001001304141c0b280031100e040c2e43d1000010101d224040703070540013 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 191262050 1250 191260800 191260819
    0xe010b040902010203191806050711100509040216141b0105033715030614090c120a0f2a03050606010c06020d020309070f09060b0a050904090c0311030f0309 69
    0x85e00390740c40303400c1b0500f0700e18082e240d20700c1c80d00040c1c0203c3d41e20741107a404140081000000c00801d00502c105224083e075005814480384803018080d806050142071166402198a018640c0140c12030031881741c011480d0000110303103652954031101c69403076240c08100f1103404589254020342c2103074000d42c0c0e0030203005a1b800c2c0900c000000100d10400c2e4a604000000170f81403984010300440c0881c0c070108000014892940c90120115400344444410b501942000c001c0001c10219000c0d07203204055542008001da000102070030144070b41c000400c0301900c03240c440107102000174608070405078580e8000c41c40c5409001d174201d0710719600c801001c96112000283d01544298035042d0007501c1140007509003030302214080180d800850b078504c019070000100f0850703000380d10212801000ca042040000c00d00b41010045030748246403282c0c0c240600012503a80645841c0d10154004d40c00c558119855500c0349032010210030000c003071a100e032140d401607240c1c042011048448010300201030300c51 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 191263300 1250 191262050 191262067
    0xc0f010c0206040f1a01030b100501020c031c0507060f02070b071107031e020603180c01050c0309010e010e0409030e030105070315050d050109120201020a120209061e090d03030e010b040902010203 86
    0x134100700803100207a60880c50480340942c2002c5034003840c402c00d0b11101529208400e00240d40c05580b0447c11580140e030041d440f42c034081030040101c00005103094610364680c5d41920b481c0b01e469002032031149000000031195042e81d02a025543c421400d0400c2602da0b200101c6000b46960744008580d04000380820000d07141d0321181c0b0400040b1003006104008540000326190003c80303c50300210036402e0091031444051040301500182424003e007020340101090360350740614410700341804464014258181e000b140c04407807000d0014014054410750f480d005003150444d0000034029800c0130003061354240070b0300504c104102e8026442162500e0f200800c0003103500400191010b560302c0101001003034010034484450603660300050780d124901c0304000c010030421558100007610500000d1000d540f07aa00700d4213200181004c0c4002840110307481c0002c1c2c450380d5801c2d980200f00d581020105501904140c44440b5024020010f2000d240e041c03000b56065014001c0c0140c1080140c02c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 191264550 1250 191263300 191263313
    0x106030506011a0d0b041b0905030c190b0d1b03020d0b0109050303090f190f03030206071805060a140c0d26011e05221d0601091d0109080c0f010c020604 67
    0x5441c17000100081044002c000391550303040208a4440c0000b403c203441844507040820001d446103100395280c2008560b2005012141e41da90b006103030050703000145540d443e042c1500550100701c0903e82c045080c400119010f0000e5001c03110500c0c07079500f8000c2c08510380d80129080c00132140701030051403410350f2810404c45000840c020040c1d1010807445600300d00c80242d01041c01a0804c14480174040e0b0650401074507240004002c1d101f0041c0b10310005a40c1c1028400e05011211706403441d81c1c590407551400d95401851407000b59852001182240c9426800541c9000c048403d8030341b80c41da4181d02c1640c4059400103410080c42030300c4c1c8001000032150b002d4415070600038903545194030640720f80004650b20070807044000743c0b0541503601c10341100b00f07100f0815a400c60035100c0703031007420440c43c003a00d522052150142146c1c0d0303199070040c40e001d0403a04501a92a03900200503405c001d15080a00d5006401158842d100e123640c0000d1042c0c1c140b180d1072018011742c00034003980d900c0e40e4550 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 191265800 1250 191264550 191264561
    0x15030809101709030403030909091e0305091513081212040215033103080105150d02040b040f05010c030504090515100e0f0d020d0f050c120106030506011a0d 69
    0x10410003520b01c05100d0203030000050180a03054240140da912450760030004e12600b00383d041900e00b23514010001000a140b82000b1186246051080800314818103080da003a01406d034500390403183c031243d80b08500c16660001c01000030341c03060050005840da0380050390b6284442c2d6507811f5000800c1204440c114008646620500c0142050300c4000a51880040c5410680307012942c001c59030841b46445a48242c000e00e00c950245d443c442c401d40c2c0361001040c202040c820075002d1010490840180c0d0690030440384504802242503503280c0d0781f9540503440f40d01910405180c4021864081520b41c411000d0380117071601640c50500341070420001c0401480f01400d00445c0c8101c00c1c022184a03242c02d01401000c0315940c0b100d8880e00c205009101140040c6600507205054001c6a040161307a11900e0031900303034000d19010100e403040d01d84549000c18118086034000c01d10210301c071034840150041c80070303241f007082038a440b03990701d0600901c000002102d290240c0c0c4184a1005071003d0faa006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 191267050 1250 191265800 191265829
    0x180a0c0e151003050402180609040213020d0603050c090a0903020718020d0603031701091104031704380301060f11101a040e0c1c050c0604090f15030809 67
    0x180486010007002035840325401030207002182c0c4610421055140c04408168a003091a03400380f00c44c5000c0740050840c840042009218540d0001c03503049001d541da043e5550000401001c0184035100d00340039039500c9150705d000348903801090001d5111310301e6028800e1600d9240e00184076503400c1c0520360010030780f54030407954800d609000d40c419150440c056080150b004c0d8881200b002c004d0100941a01e00507009943c0c010304104440b1001021030013142c0849420103a0103201e800350119013079480c882ca40c40055030341204200c49a4400700005841c0141581241862481c074980040c1d00e4180003d20800e004120f003001c85003843d034040d41115580d442c0240a5850071000741030710030201c40b05c2d000401144044124403041500740303480b60480fa40400c10050a0b9204441c001901035180c8002c40c8810124007030f0560304100c82041080c1c20044d005000759222922802c8000c003d01c440254002c40a05103084800c0c3d0010101d4000252034020309624980b2448070288548078100845 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 191268300 1250 191267050 191267071
    0x12070608090a050a081c060501080a020d090819110c03060c0a02240105030c0603060d0201050705030c010911010f0c052a0307090605040b03030a2309030a0605180a0c0e 74
    0x10b0b5002501c2844401e0100d03100b12066501d03100d400586058544504075142c4485150941c2400640e810802e050f90000e081c4902680d101d00e41221034010b007900510051039a4004603030b8280910140c40f1b488000c5011380c3e545420070142c25400d6603100d441503e0680c040e0030050116140c000141c0080070640400d004894a120b480c103d03401046401c0da9050f084240d00340018446464140910560410222507031401c5050034400221b0b009040c0360028140100000d0007810010b05000751800c201c980c800030172000d401b9040c4000c6400045103c00e00149140c001b0890f82c50203840950a1650014020701c1c11814000c04454211428452000710118103060311800d50ba00f0400103024241d030700c401282091401c0e041c841900c01c030600320b5219030001d10510402036400300751807404081140f0400c004481400f4030480500c11210080c5d05805041c01c2c60080c441550401401401500c0d03062250f5107072031540c01d441344940480248001c00c0101c00b00300b08054460890b4100701d1094 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 191269550 1250 191268300 191268313
    0x80c030f18060702010c020f010c2c1206041a0c03070807030204050a0807150e03120f040b030a051801050106120b150301060c03020106081603120207090e0703111207060809 76
    0x101d0580b90050840340840142e440b01313400340f072030f540c180b0101907030b07002c41002440f03458001e64004e020011a80c0b4040302c1401131140d440440c200c41120100c41e070f08007420380d02c1702d8030628400e25200c2200311800e07105030140000d100021103002d800544603d000070350490a5440383e010444400300090041c1c420180c0900c00802c090b69023510540044c4404401070070002c0c5480c2e4031055080f0140c2d01c41c070910034401d9882c0c1854802086801903c1208880e0030344c0d408001454801c14041c50704000320100002c02007116040c4079038811801100b0902e40d004026040281d21420b0b42c0d02401a0b900145200316540d152480c2074008460581c0000d1141025034480c030185a02d58009912210001e5400e99600060640a00c40c540150090030081c0ca000580d00040c4c240c1c050306440300a140f40000c004d50041c20f407082c022803000d00b000c000c0c2030159000f096010341c3c0c3c0c7c102c03d00080c0c0e500c0c0c1e205c05401c070a43c94040c40c14280d0303030040e1015150301c81c6070100550700030000900c840c0e018010b14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 191270800 1250 191269550 191269591
    0x6030203010608030414061206010f020a050613060e070501140705011e090213090308010b1c0501081e01062103050c030f031012020a0b0310030f0b07030c080c030f 72
    0x3030003140083d0a5240c0115116443c06081e00b82090f85c079804e0074015442001100401514503611780e5100c0000e08080e01e03000121a4101c0c40c08405050182140c005d210901200b004803103441038400703024400038858aa001700030541c81e0003192007840d0210301d40b8100324580380c207544054240280544000a40400160b00d4450344070005401d0489265070f07140c01c1c008518040411140c4000c40d02c408029444456801400c0c0c010180101c64100d04081407800100089010b448000014000c0900c407550b0354100c940d5544e00103210302502039480d08426503890205119901c200ca0030081142c0b44401444071510009541032015401c00c4001c21001c10007100800c020300821201d015560740d2864201407000404042d80c010080184606c0340c0040940e90b40140300303083e10924420140d60703071510005002c142600e030b800280800c14030003807070080c0040124140e00c681046e407414040d090303000404441d02e07403040380e6081019038140045a55000c03811813441d4440b8030080f0010390030004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 191272050 1250 191270800 191270803
    0x10309050303040c03020a08030309030d1d0d20010b01120c020109020a0f0302090a0c050a030b12070603052a0f07050705150d0b03030315042003010b041a071109060406030203 77
    0x203d40039184164a4074003003086041a40c4554000c0ca0408044e5045080056516449200700210090540d40f034a4041030a030b8501888200d0680c100402c560001c00c4101c80074007090754909030f44030300303101507a00882020818000c55244000580d2516000043c8842d200d000b0a8114540d40c1199a191a00b10050701c400b160700b00070307041c955100391001e0b145104110030b05400400802d2130f05d0803d00c4070740c2c0f180d030024152130f000919400c0211301c3c0450b00010900784811440c5c1c126141c0b0035030800042507605a440f060041c440c40302c00074070404030707411044082d40080c2c2e00044088010055030302d05000ca00040c0140b207100c0c04c2551000da507100001500c004442c003081007141c00000e580402492284602d80c2c40031b4051b40a14154500f030030159401100108009001e01d0b1504002550041882110b0501c8042d4400c2e2944a50b15000f041c0f0301e603049030284040d0701c071400c200616440b00983c01c0c1c0d12095489442d4440c19004081131212000c405413515401540710000480103170340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 191273300 1250 191272050 191272057
    0x27031e0c01060b0a05040e06030f01020313050105090606010918020c0d0306060f08060108010b07050c0409052109090403050a0c021503070e010305010803040b0915030a05040c0e0708150103090503 86
    0x5285190584503040e69003a60308580c0240c0c40305060f20701c00c0021121540d000020b40d0202c0b07442c1d034482611652080040ba00f018442100c070b10f0654070002c00c000445082101c0a10058000c000030802d1341d0302e8580c080d90300d4a06450960119035926810801850000c8440110b60503ca001600304200442d41e545401404101580802d0b200c01040c03003800d6022481d00c2100a1900d071403c21801d00900103400f000c0103000d100d01e20000020442c082c02001c12219a440030040c008124134402c0b414540d031112494510020007008001c0462142c50801c0107440d41c400380102240003540380e03990103480740c2d400181c85905118900280b4400f5a03130300f5080e141001889070a09640c0d01d00f0410051900a000051606052400006202214000081d03c06641d0070403105a80c6230b010740005141100c00c580e07030841070300c0c0000800260702e4a070f401650090303114000824401d0740700d20005080e00000c8a102c0001105400040d120150b11755507400384201c107040000349120306448960840d803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 191274550 1250 191273300 191273347
    0x112141207020405090102190f0c0c23090106080a0203250207060f021204120203010b09010807090507030c0509091b04030503120709050d0b0a15060c02182703 70
    0x440d50700194289400380c0c55000e90340c000218038184a03244c210501c0290650403004020084101c0703c1043d00641800444d507400a0701040030031707612540880700904018480d0b480d8a00100282c1c194108088168180d902c1c513110040b00d65284070000009420090003940e0100180440b40200081c0116a03d100340055000d004a00d041c8100902000c0b11580030404541c80704038003900d4403420b2001e44081d140344072300103480102d15000203405003044581280c0d0109242c400003d900500050040c2240c1c2540c00501c0070340d9803202c0a50440d05600b0b5410049a4100140940c518250591a40c022441030306400480713104100101c0c01d40164008690540c00007408064038041080c0d001e5200c04145007002540d801c29011400d855218040102000d554002245001d203c681004129400c1618a500c106a41d4a0001c10b80e04c15180c060303024203469000d004465180100340b03031040c59282100126440840c4021896103c2d20f0350070303580f60105120080821a5000c401030010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 191275800 1250 191274550 191274583
    0x40b060d0c0f020d020d11070504020f0a110a0c0312020f06070e04200f0a0306053a0c05060d02070c0603050108060705040609050609030102130e0a11040509011214 72
    0x84000200a031542d2641100700c0b041d54010700c0180310701c0f98002400d0000d5085c0d45441802050070a07080d520380407903500040d034440d00100360319100c100140c000d0580021907a8440c03040c4081c1509a45e00c4032076201d1f019040c007052170401d0010401c03868401c4003001301441203805140041d000c4a04190040e10104001010070013188114039050052180176900f020641c2e95040b100c80002d05140f14101043d030350034201145c00c1e9a00c50080d44584014000580305840050f4095035040000c4c2500140d140241c00001090ba10400c1030000826000e1703102e00740030b08040c01c3c007080000c1a0042403c80150580801158000a4411310000020240c584020440e541080225400c0541c010909010440c007440300b000616481100c003400c64000391085551040c1c0100882e01910a1840729007040d8228070300003800c102d19902940c403891a1407801c00c4000748503e0303207046a105506c2119402041c08006204191291013030190303007485110b401c400a10075100c29414034108403d0002c45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 191277050 1250 191275800 191275811
    0x11030603010b01080c12060a0e0a1407032c100204080102131505071e06020703020f01060618090f0b100206070206060105070b0f100f0e1504090203030d0209040b060d 73
    0x8a040034000d1a09003502400c00c80f00d945010144100350b406a90384264240d6200800b160081e1501d803114000b41c0a82006402c0c80d2910358094405040d0743c0c100121385a91500c001402140710703224600901c0c104005104064644000e46120004203403150307001c5000d4040e00500f208560300c01400200008000540c850310302c0c5004550070045644103a0703000000d864100317911640102156a001d40c00049a0070f044051003800c04400522040205802e1000805100345500002c41b904442d0f40f03d8000d0010702d441e10b4045078101c5070100c0641100354171039420300100029030865218812103980008880e4118000121910380121070303000507030804024440240e0b814480d180c0d100c482800c9c0a85058084c0c0c0e18409812801043c8000382100a40462100d450249800d40149020003007451815291203101e1031951080d11010701404d03129011052030304040c003524144a030000d0145003089668001880694401548154065540c03103e00f04180e42c0c52010342904003c18000040307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 191278300 1250 191277050 191277061
    0x3050c09101206020313020d0609050c1903060b03010908070318050603011404020703170a0c0206100e010e09010204091b030e1c0e0307030f12020607090b19121103 72
    0x5a0400240c585924402030030741c20700c4403004080d21810116403110340143d40c0c3d41c443d405540090a2080c000f580640704120341000d00080d600840000c1c6d0041054848441e0650100201c0368160314031070320070b040e0380d150400c08030360341e944581c601c440050008104d641d55651100d54903409524114003260701005030900b40c42170225200007810b000d23603202c6e16650404401008901810355024821500040e03840f0402d403207001c0101ea0b00d003c07500218201c1c01c048210801418038940a0801880341c04000f403d140202c920340320840740221121503244e400e204100514000060891050350740070040000c85425a00c01c19229070700700c2e800b40000008070b60000b019540544a9000c071980b03e80c040300703040000e0310140403049145003490307043c0d0421b0f600030a007041600e40c400b40c15040240508001d00c819403034102d0300c8103456400c1e10340c2540c030450140c620003841d0040a500c0304080c00f04080706034031100c00c0c1882000078182007031000d0021210785c1c1076400f100302c1114104800704c00d001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 191279550 1250 191278300 191278309
    0x40b130303140f1b030c160203390301110d092105031023010e011101090f051c0c0803060a030b10080705012a020d0b01321008090f030403050c 63
    0x41e00710013450505181d4209000821568020044081246c0d0444002001150740800400c8180e0310991118171400348012441102c070040054480031611fa0001130440d1880c040c4504840d00c0861300019007401640307002d29005102c1e5100450712094598501341c2c0d99401c2141c8804a00e14a54503d0f95030302e04010b001c0107119066000175201c0d200b440c5405013108a9017941c1c04464000e103403e980460b09800100d400c1e0803d200060100d519000e101000c0c0300b0003910504c00c4a000300c0031074004c18109903048000450044803400047d490020700c10001d0900303c02190856802049442280d071640c5519040034003c3d01c4505c0700c01c08000c0c04000d4450144400c000078102400d0020f10f4802c4a144a1420344a005e910b01d1060011016070045598031089404da890704654030540d250707103c8803001a040e00b282d07480c00f1000110741c0103101c4c41e42c4466400443c140003802c1450002841403084c2e03000d0307038064041c402070300804010580d800d02c01c001030030040d4000c0c1c0003822005400000d02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 191280800 1250 191279550 191279581
    0x601140d0903023d020f1b010506010504050d03050a0c0c0905250914040e06071205011e09021303060507050a0315210f06060f140306040b130303140f 66
    0x5181c01130301c500700354102d00e441d8502400380320b5002580c600b4858148224000f032146021103c800a00490601000f040310700384441014884002000142c0f2800015280c50103544076856001d0100301207000085c1c840d00140114100c20b04005002c0e158075690b5086e8100b0507040001c080d036803030342004143c1080020600c24030514071411400c400344800020911038090092900c034401061902d5596286da0340308040341507410b03065030020b00304590002d164814295010501c2d6060200100350700b1000041d0203141c1c0f000421a0072401c1c90702d05200041c0d040501c00300742da417603924800000b0882d03500030207104010035641d80381d49000000c8040e084400180b413201c2d00f840c03085000d00c4094a84c1e1305a05452180c0c0001c440d884246d890a40c4210080c00d20081c001420664005000401520240c00350f8881c005a0f5680d000e03514241569820122400740c02050200041921845560080c1d06004d0103031070b02050f1011481035a45c0e80041c240e07402c4403540100d80806c0f103101500c8806 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 191282050 1250 191280800 191280823
    0x2090901090c120c0914060f040303020105010f0b16061112092103010e010b030612011416110a0b091006080309210a02090a0605120106050a060507020a0306050601140d090302 77
    0x40141c180c1d04213004060541500030408255980c42c02d69880365187c0d02941d0b51407441d0f60b00d541d940c54591130300270f020705420302c51941041100540803034081080f40945013001c4542e0300d2030892480d01c5d00d803200901100292095450010040c8103102100001c5207481110a00000e2003180d010142d03601c1500400c15101c80c804800348014850401c20401c1241114410541c682c1ca980310389001904039405007000e1f00d01c81d0310701001d41030015425407032075104582a80c9500c28113a88007509039242c6220722020010742d0811001800003902d00c1324040d802860000032605034480c01ca920404880c45078101c2c50380e5500c0480e20440394540070a400744403440c500402040002001420b079540c20300f042e07000f03202d801660300052107018035520810003840300400c82da03084180300b800e241c02000340307008280c051100900301052460050003203030342c01a4054a003050742883c4d074413003000610001e4a101e04102d03500e81c0c00546150381d075010b02424410640f0008910b0407a180c00ba2802c241c0e42074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 191283300 1250 191282050 191282087
    0x1605040909141905030702060c0c0a030c0311060a120906110d06090f0903080403030507230901180b090d020f040617010506031c0e031f090308010803030402101202090901090c 77
    0x1411000071341c01009882d019607041d00c07541c0d200d04c0758403651401c00600340c0c2440e410509401d000818018488039440803030b4002c0c082d0303400400601e0140540740c460f5046140204220b4510481b0400304d5510010009014034000a0742118101a09060303174000503030340c0d44950312104203100e420010310603100500002102084010b05594015280c210020400f41c00d155030f441c0041c0e03060f4010351007880c017034010054103151003101c3d520005854022010050004110820350300c10a2141c14030003040d10425000142000070b0002080f00840c1c100d20103e0b0000110341d054041c030b84544c0a41c0c0701070088964080585200a41e01b142103d0008006505c40e40c040310390414a800d20040b1400d8140562901075403c3c0c0d5248040384c600b00844d03806105c4071601c000300031070f0b68889070310041400348284c1d128411070740c0c0c1d080d180d0b507a4002074030065407008202080c890050b02070854685d158600c44405420300f11150300103107940c0305c240d00030060540c881c0d807038000c07030f50340800d10b41d020042481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 191284550 1250 191283300 191283343
    0x304030309051309050102030a020304140d021b011101020a020a02100306060903020d020316030809010f03450602090103050f070c020f1201020f07050c0307030308160504090914 78
    0xc80c02004040c80b88605402402e40c802d0400c2690740a400c00403059170010020755603800d10041d048025842144e040d141c60f4600300000e4441d05020a000ca0802060381c000c0590b06009558030520030780c005c6034241485500a660729421000b80060a204001342e00034004816090040c0150804010120410149000300c24440980c21040c40426607806491300807121602e403006c44e241101d41c0300f1025405414140000402c05910000c02101c5800c1c0d884080c0c084241d1800d07419202d210708800d0172007a881610000c0d0861000380244e440131903c07540c41186203140740402110716001c4096a0441d0001001d65082d43c16000306078208104851501d032616100b40002c16240100034024810340d81444090300c1d030f41e1181032031000030054600866a40d100d00c41c16902c030f80d00801c0100d41e02d0003001c03016406894041403440807690541c4422440750f95030440703050314030796035010032003442410300011030100300c54030070710a0b141e10170084210140400c0c19900c0c85d041c41e45903041c50b211400c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 191285800 1250 191284550 191284553
    0xd030806122d06190c031113030201230d0213050a080303100f140f15160203070b03040308310302010203040c0503060112020603060f09040c031713060c0f0204020a0201021308030403 80
    0x48108108a1003160b500049003170144078110701504040c82c113031035000d0003c210024000300403110181101d1007600c03803c0800c0c50001079082c010f81c04a403000c4050f0010700000071803c41c580c0042030012944070414084580b0303200050540801d6402015a0794408020051500400c910102c094240c507004900081c1c41c1450a00400c070b0301001c8a409103210102c10704190b182e0804d865868070111001e0746d00d4100040c1341c01e0b0600c42d00b6205a00ca0301c940030b40001e0384845001220300464041c0d880b000141d5485200003079a0042103401c0e009680165906120010000c48034003c8a200f81e002695034242802c22500030011500000e119420400040002c09862156000d003142d05540c51910f9594120000340c1e04201204c0e0be913000050b0804000c1007246401c0044240d038031603c1c0d5003880c0d18040c130030000107000e8071101c203181101500b424002035020395003907400980308800c2040301c04403580c0401d090f604a0800d100c05030390042030002484040161002c040c0c010000210b080905c0c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 191287050 1250 191285800 191285821
    0x303012309070c140105130302160b030711070807090f0b1503070f051c020a020706080105060412080c011104050f0303030c031f030507060e100e0d030806122d06 71
    0x2030940c5003440303199400e420822020352046041300c0c03c0c08008105614103900f051026020303481084005004a00b03030b84440c031140b44198000c1c1d0700182d0030075007141d5030ba1005941020784420030034054460100b00280c07080c020022003000c1c04a00304049042001980c0f18003e450076400c80910600d01103070546607a900050a41c0d61101c154a80000700024050040e07860f84244070314070070410110000300d5016002e50700101001c0c0950707070860f000c03681d4900c0d040752007940c2130040710b500a17003c210400510301240da90300f80315030207941101d29085168541508480703502c50580209d00000c1801c120310320303241400b03c1039000254091403451034111442c00c400c0c07000515840203456202d6000400c000400e41c40c0014503407200881ea00c007519010050950500780c21505d00c00c0c060b20410713080e1507114468103160060007501d02880e0b072580d42d5040c1d0306400024101c42c0c00012408100303100712800c02841015000c01e84210482030024400c00b0449030715491610001d40c40300d0f0a05c1030302140c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 191288300 1250 191287050 191287069
    0x15060109030b040f020f06030f061e0d0c06021c080403030b130c0e030c0418060c0c02100809070b1c0509010b130e0601060c02010503011707230307050406050a0b070c12030203030123 80
    0x11708407004070b1090bc00c0040e4415080040c4d19040d01b1112131600c080c00c0011a28400007520310319002c560b4402c0700110b440c8190394032500003400040c83d000100300000d0203504a140c04550092002c2030b0341d20f02408080c122481d840004002410040380d0500a0805004411403050141d030144900c405807000d4002400c003a14005040fa0364804074050114450301c03807412034a41c010001c002c0d00401410003001401c041c6c4808059019031700001a40c0c031000803c0303d03000000c0800402c1d40c980e203104042c0080c04c00414100a43d501d6288030899596880301c00081058001000030700200756040141c1b801d103050b0400d80a0011110551016030b17040029241115001204107061180c00c0819900700702e4560702400c0c4c45585184440043d03108a241d0300c000d03460550844001542e24820041030f50b5490cc22550030a00c1c2d0b0364180010603401008150440c00b403a40400320640c0c51100880450850b0b20a400582001c0014080d061015610b90300001448243c00c00807481000024400f05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 191289550 1250 191288300 191288311
    0xd0305030c040305071205190209130303061e0303181d0901060504050408041401080103150218130e1605060a050a03090203010c0f020d02070815060109030b040f020f06030f 76
    0x90100000d00d000740c806049402442c1e004043d60030135a91805011030550103d502114680a40758030455403082340302c20414100e030000c01c6a011516841d03031651024406036019010541c484a0100e0601d40c0d545138a0740140046004607001840c41c20000c101010f2a20201e1000e880054100f06c0c02d080c0340c554030103100701c103c0300c040d0b01e407900e0080c10f00406081d440b05400609003c101300900002c800030700204d45000b483d040340349030038000440b425842400300038801550381020b165a604a940134050312480d00071500000b41144e4001240b6662a44801c1c4c41d82d510780341ba44201d0302c014050a8403480d9100034880f030250a001c001041401012115005c1040125860440074440e81029102d140c02400800c0015038443c3e00401c1d0101060040016209804810b15a00e10005020040341d4008002d08a040241021540c00840c0540a1030400c0109100800455452080140520700c980d00300d11008110344144818480d444000901c148418401c02c6510f201e000405a4050f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 191290800 1250 191289550 191289557
    0x30603060a0c0c0501050a0203180109170c1608030c0d02030f0d0203040227010312050f1e0c0d02160b0403081c0216060603140102031006080408280906030204050d03 73
    0x2c00e00c200c01ca070704040e03040010300a5030903d000d00c50610010741c021070060a9003880e18441e4000c00c07503004e09840c00500d0003020103904c1d41000310310030700e41070107460711008540982c0c100c0d48500308080b0311001d4540201126820005101108100802162a0901c4140003650420a5100d560f503918081d000700e000740700b03800200040865803001105c95200f101c4440314003c2a040c4080c01d9013a4600340421510308004012034411603009a0503034030b00110b04c5194a1501145103041e00708902c174070344a546240c105001d0031400344414021850108000d9009001d0080d502d40391408503501c590060b03102110800051010803690f204590b44440890101c504003580e80107510001d21501400d950142441100c07a400c0080c0c5400c003804803402a1880301e495007020001074200e100a880c010000c86038003408000203401006c50b04c0e07001d4092180c1c0307400e04c4a02541560042107032407800e00c190540000111115030400f1090003c1c080601c0d00718106814580070070028140848040c0c01e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 191292050 1250 191290800 191290811
    0x30f05070305130311072c061c060f2d061203120509120a0309020906120607111c0801081c0f140f0c0105010e13110105070303140405030a14030603060a 67
    0x251300c000c00425000301225900d5410458a0401411008015600d111180e0300142c0101301e0710f02d402d01e010f10002d0f4aa00e444270041d400c1d07664000c000d114107a42c0075001912420340810601c01c15080300f01001c10126081b0100b516030800b081200d26640044440352166640900030907409045c0300c0d0b002c00c03c6140000c20b074954900c06890070000c00d00d000d0a4250004040340c80c250306030000c0800703d20035103085405440701406c1142c81c03030790b10004107002d91004000890301880348400d54101c00110f016100c401365100d403800008142c0c2401800441c8440004101041040010b01d10050620029071008562820f0007051160740c3c2e080c94041211900302d1050685050080303604d4070b4024005d00f560307007818004050103031400f48188007141c0540c00002d650b4071000004016015400b25030000c0e5001000010346840c1c0010300150708142d55004001c03001d00d0014900c6004e1405800155128402010020440030018901000c1d444060081c48225207001400640000c0e000d0f002146 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 191293300 1250 191292050 191292077
    0x709032315070f020106050103061a07080403080706091101050a0f0f020304180b1207060e060714010207061a0109031109040203010e030406080603160b07030309050c03010c030f050703051303 84
    0x34100a04210452141c040c0040c40403250b00208807030034100980d0028880640d48100650884a89114510000b000c020805102c143d0080c02071400030b11600300c460a142e126290405507421054007250034582c0d40c512541400800c0c5d00200c10b040c0240303085031800c00401d1005100004110404082c045500a584070450081c01030343c02400a8400008054007146081000f0f0a560182c00d4007441e10303a900039500e000d02040303a0007981c05039100c03180c481898606016003903011210550703882c01424009045900280000e100d03980c0201404240c848070441c0340101c44060031000345c14000c00800400010b04441e42d1a41040d500b00c0300d41c41c26a80e140041381c058200c160048045000002d400305840e0b8201d0b05e8139010b45010350480c1c4a05021001e40941912a030140b80898003042c030044000074441c1e08240034003849241a07a00500616011a0030344109500b90800b00b501c070610701c9a5101944540d40e48048180b400340018148041844149024088042c081100700003a480 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 191294550 1250 191293300 191293303
    0x522061434020f010e06041406070504140103020d060e060a0e010f09050414240901050124030902090907031e0c05010c031116081b032a040513020907090323 69
    0xb04040010f0028810003109412403500c80f40200c804880c90740002111002c52803000590510503960750f2502403415041000700c44d4012071001c01c8604064003040130300084803160080ea130041c0b180a0070152036042040400c5180e081a80001001003100c0004120b42280d07050701c83d04480e0800da00161a803200e080c254420729400d48444c0a44c807176000c1c00c1d0b41812b4041c83c150048141c80308070206a40fa9401014240c0f81c0078851110944901007160800c980d2014008610302914100081c41e04010760110f80180000c5900a056030403040c0f0410611a03041001940c00321581903d8004100755030310a41084d1540c080c10f810481c2c410702ca0300815014141c0c4290f14801003048407100861803c80c8001e60046000e1424a809100380204c0c1400010300d1003495040001d0107010710f40c200300e644503402c1060002c200800f054070452066241c482d4403c181c00340c04d00034014484181d0314018081c1c90480a00300307004211641d01c0401c0820b10030940030f0b05500985441049014008058a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 191295800 1250 191294550 191294563
    0x105071b0224120a09030e090c0c120306040e0109080409090219090209120a03020a030f050f0c030325050304060506040605030114040c1406070204052206143402 71
    0x1882400d51903000c01c20b041c504100a40780e0300d0004080d02c1180d6459a541c0d0042d1040c1c1103005012604603000f60101e803a240703203806da00004644c03146081c00e400d0003280385802c404c1e0200040d00803000051000e0f905180c000c08611042c070000a1009602c940c1d01c1c510240714520804500e103640b0a034000441d0745401c0746450a02d605601001c2061315a000980254007141c041882013406c1f0340100300301c401c00300d49100b1442d0503402070180042c2944099800b01c002c80102010008100109840c1424850140207a800c4150045442e890808090142c0b00031820b25404ca152006030524032895204040b26401503100001013419195940481d001e021207400481c0d141d402e2400044003d03030b644038860f120f10300500074041c50350f82e075070701d0a075005490019150300304408000da00301504003900840d4128030044060050f01700407150003060581459400c854080c0c4a15070490300300600d0380b501340c02c110000c0c160307074401c540d80d112540c074005421210300d00f0481807008821818000d0112 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 191297050 1250 191295800 191295829
    0x30c0a0b0603011b05191b030e0415080f0d030203010e1501030b0907020d09151d030c03070314010c030b0a05040b0f0301110c1207030e0105160f0c03060e0105071b02 73
    0x31581513002c1103009019600007001c0072102c850340f0203120400512862003041d00141c2019040450360031524101d991082c0c1d081c1490304a901c0b1140907082071120b00840307008020240241031102c00c1c01d0100c83c00c0c5100c07030f40d541d01010b00502c01888a4448100250340109007851707042401c0703d01d000180c019041117550320350b210000b1420400503580120305010104695038903002e0841d180c002c154806045a81e20b0000240e007100f0140b2452402020091012801070444400108041c00070b40740c80070303e03001114810a031040141c2c43e807101340111050b80403941414406c010a200c041083c400d405d100d060b1083e515080540100d45940f8040c07480c00001800a216401007080c00c20207503403104207000d64510030016005c03a0350403c04152500c4981c542c0d07600303014a01d01401100c103904850450040b140d18071441c0c20008441c0c3e940c51019501c41d00080c81000c3c03850510708211025688203050320790410040040a036072200107000910318143e2010a80c03010340c004210001d100646 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 191298300 1250 191297050 191297081
    0x30f070c050102030a1b020d020d2a080702090a0b010c1e1205030612010504080307080c19080609010504140604020c16080c0a05100806060d02090603070f0f02030c0a0b060301 77
    0x500a64205d140c20101110b03010070089080740c00c040b0402c0340e903041203582e004c005070044000662131610038100100d02c906c211070301d8503101d51400d0f040a42940e040d5422640801c0000d01c480460802d0500254490018a4100300144240c0000f03401c611020340b0003405251044508201c46640d40c2c0d010000c2d07500074500c5581f1051001001d030841d0300c16502688640c0b400100104110414021a44115071150034a815070f05c90000980b2007071009072420014410a00c44035118180c100d0451074007101954603241e4505011061005142e01a004140620308041507200040500d1481580080301035a0050781c5540c1200c40d84c0c2490400703086140d4514460300006641c0400049042101808031920030306903584901304010201a070500b00e01040ea0303000000c280345410006003d0051200c0e4000d4035044034400024070310313401110f030320011602035841414910b5008601c540000c5240c0025490306121480e2180ea80d40c40000c000d03c0c500e03900b000220507490030340042481503603c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 191299550 1250 191298300 191298307
    0x31107030e01091e1203050403051203060114030c03130201051b0a170a0f0c02040f02030112060509010204120b18030f04080f011104050d0c0e010803181005030f070c050102 76
    0x2400a008506000c041c40c009030f000200403507104884405800c0c600c0084001e0701550341350040843c0c0016a404e015018001c040c031002000c0f980078001800058829140c0d40d035649410320000d0b00480e9001070311920b4200034002c0241558158003280e800034040300c1418841d2016200403035140c85003226800d551010852070b104010000214100c0d0b140c45429005480440b81044208070b015940c00040003610205144a6050041e0b0109180c640050004134581c880e81c000034090317034800c2e0720500341030100110300710502160f40300f45038016850300f000f94500751401498130000b406020010703107201c1c403580111f65009204003803903114401030010349440c0c180c403050b4600707690403512949009001d8141903504042c4103204e03440003600f900c2e20301801e045c00c06050100c1e2009032042110700070304041002c0740ca03c0b548030b902030090100800031551500c06000c1c032214241400302141c000c0c030ba0100c241413815088416030380d210205c10102255030b034502204545071209180301900715440007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 191300800 1250 191299550 191299553
    0x2060a210e1e0307030f0c0606080114090d09030503040b090a0305060c0a09090c0c0b180604050d0f030b0a030807170a1d01020a030210021305030f060114181501031107 74
    0x4159141c030941c0189401500c80711503030075903032a40700781c904c010000345850b188000100d00882c0d00809490003540d0016402d0f4030b03640c9003801c5407007990303125062040c600108600150304101c0c0030440d240911702500914950341d80c840e9240184d0285140041e00840c011440745c590681200c02513402104495040c00c01e92030350050365001080c4400060f480c0d45010881c030121380541ca9882c0b444d0fa032602004440ca0312910492079000d071074121010840c0329800404401040340c1c9000303038098005803008007070000014103114807000200c000e1600782005c883c26683c440b298a01100c0d0082d81e186da03039228502e802c44000c0f10b02103102e08181004146440c11aa02034440c0b07404080207442c2d2000e141da424016a6104003002006005a00540164040e41116005010b030f00081a65904c003050715880000c0c2420301110303580002e644044010440c0c40001480501c42d110281e40708011030048500600e0307808801040c0608140d0040380004940c0d2181e80061540300c00c1c90045501c1e130015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 191302050 1250 191300800 191300803
    0x1501092c0f10060e0f0c04050f180f0a05160c081806071505070912060b0f100518010804031209050703020603011d07020327030a0602040b03010e100302060a210e 71
    0x240107904d4801108030010781e9440310403440d035016013078002c84181010300e480100803500780100b0045801000e1030036180c840703070100c101803400303034540b2500f0b18064a003e110300400c9460052040c00300842e803001061000d41c0004884035031301c0d0890045c6661782901107012580039659000c194005030001010720610001c0000100e4040c4600014440e03a00c1d0004200c40c00e09950040c4d000903580515504005601503020b00d03040007020304039815642e200707000036103c11402c40c200d902007000011280d410030840c0a010140050034200701500d81001d44000b0103c0c1445404440c00c03079070704d200c1c107020f0250400c0000000c580c01480c513950303584c49100908028070b50041580d01c0d012224081155103001200b9214402c104200d4258110700c98141000c0122a03c41201c0d098001c1c00311107804540b5900080016050780c484469482d45406505010400002c004c40c0901001c100244010703034407181200c00030136039448c240c803200b00400802021031042100141000c0c1c034040044103006d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 191303300 1250 191302050 191302061
    0x30303140603061311030f0d110c1927110705060a050c1c06080102190201050a0c0503060609060702030604050604020306070e01141c1e0b01090311150f0406021501092c0f10 76
    0xc1c110644030580000c10510198bc0215090208070703640040d801e10400340032520309415140000000440c8003107035034076641250303182030000ca248071000852034107200d020401c142e0421132541d410405460301010281c3d2900a500c8104420070500340140c2d200b05072600290f014140403402150340d0a03c2c44644189800700b0703c1c4032800341d424100010310580340c51190780202c0b4020b032501403a5907102d008020142c0d0260401a80c011420301400e000350300c04010f9544038620a50003000182094010545801c00090410302004081a042d203440d9034485109462206a041900d4407040058003903078181c80b4400000e5901803403ca6910701800d002c803d9208442da0f925010801040070f240112a40800d1b804040c207222049050b00049062180503801da012402240c60b081601c403160741d1060768001c1e444040160300400c5104d45802000825a0040c0700380c079005c00c900e60700580e4001c100303182d03444042c8403211419000b0009250a011458404a02030103a920412042000720010030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 191304550 1250 191303300 191303327
    0xd050a0807050a1a04031d030a020f0103090c29040b091003090803070305041203061d071701030f030e01211512050f060108010c0909020a031104030303140603061311030f0d 76
    0x4082030018001c10300d507542019a4801f001e0007822051980b9000d000c50301190750141d904060707660301c1e1316010440740455440940403001000351081c1c05401c52114040c030031248841c0c1104104010030814105100302ca401034019103e604041d1075540054000307140d071a00103407009100100300403075503906a0166104030b100342d0354401e0b9000700402c12401c682850080901c000c1680148120701c0403458035203030340401d0a18000c0d0380300d810410020307081402a4022200100c12002ca00105600030769070010654080c6801410b00000300380c0c50424400f07418a5281c0150f580b0380020751001ca0040907805000000408011039405141c0265200031004140304140034900003c80c0000060103981320324070302a6074a0014500b019a001d0082d40a01030007010b00d0755841d806141c4440d00c1015000450180d140064002007000c03511503e05002841548250010410054080d602e100e0402d4081d0b013010345183d02c10541c2e00400d282c8034400003208058820764000c1201e0301d40c458401141d01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 191305800 1250 191304550 191304557
    0x605011214010c05070212030f0f0c01050604180212010b040c0512090607050f0307090306090b09060615030121060f05041e0503120c0706060e07030b0d050a0807050a1a0403 76
    0x50149001070742207079002250140014020055000581b40090004134045e80c51415070b86060b915104a88640e40b01640c0c1500140c004641d07511603000a2068035881503050b030b400d0200703a161066041c062400281d0092190800c45450311900900b5803001070300c08000342c0200320800302c0503006815a0405100525008074520000c0c00020001c01d1a0b4019a0340b500c80c64200f101083e404c0b2082c0c0c00040a11081100202000001c51514007404083d507025003000c800c9400c08800c45802c100c0001c02d100e0207101500c9146d054490358100320fa0455400038196001c40310903101c00c1e003c1c401405000740416051540392813003035002e40e008034050352240741c40500b004040003040c41241ca0861001c2c02386c0e00244071003500c10140d200c42c0ca50100110f20007505c0e000c281c0d690542207850a80000c10b901c138042007007126140e058425003803076150883c1c40304804900b5940d4117994507000400201001004194401008420041c1c080e1a50b844a00306074900d40e0060420344952003114184c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 191307050 1250 191305800 191305823
    0x40906050607020607030c02151917040309091e0515040b0d110103050403090314010e2e092105210609041704150509030d020309010518030a06050112 66
    0x80d490701c002250340c801e0b40984610300741110794400b80d4520000800903600501041c003107801c03000c03214005124031108a6950145645204402001d0082d0304a81c00203c4111400344404207812806c001c04a030b0070080017240c45402c448a01c022107103e0740c4852802c508100030310028198801c140418194140d4042144800d1101000404005410040c0c80c0e451001c6c2e580e40c04d54461382010b50b000f400390800001c80c0b50740f41d4400709100c03401d20044c10381f03941d601220042c0340c0091154030440304580b0f44500a004a0405d41d015032608402c0700d1a83c1a40c0368030050400251403821520100303c031080c04552100110042e00b154028901064000003202201c0303420110685010f02032103000e045101140d80702d0b80d0740400314400e0501629822410300c00002c4a480c61800c44c00b45441503034506443d0b46042c001d241c504048054600213640090240e0360099074014252150160780b00706d03001740302901038042411300f241602c0c0506043c0c01c00d030001c2402022076403070b80100b03807084520245 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 191308300 1250 191307050 191307059
    0x11b020304140301020306180a060308070b040201030c0e01050435060106030c03090b060d02210c0102060a0203010e0619030f03090608060a0f090207081b240702030702060a0e090a02040906 83
    0xc1b440101c5001d5401084c3c034a22501d00a0198180d5500c0a202c003070020300b007901c030b460b0140c1d10b4003c3c2c14121542c41403001007008559060198140301241c13030500980d0fa91070740002810380d02640c062991003d00c0c1c12048007154020a00018a9001d1240054608040398039103640340ca000340a540c0100c2e051062400c0d00794440d21503070300e440c1d030004403643d001d0f00c801d03007000004103020b0001d0341d11141c81903000c14180e075801c0d416138050b1504002400d440c010000060b042140c0244a1130915205200400200c804080c0050f40700303c04491105850b5070b01b118010390383c050b6800c00b4048135841da401c4020550801c12140c00d40740d2035240c18005544210070895101c4c03981c09601c004004030304041000b5001d54000d0551584580c042d241040009000607a06105c0051420041e90095003103420308140c004000c840040c080c10141d0592a048001079500c0c032480780024040c02c00082d0414480340300f12480f00749520b00802c42c0aa9051640c404c02c0650028010440c81920b405d07000a07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 191309550 1250 191308300 191308303
    0xa08090c03030406030b01050d05151002150a110d020f03190219080604060810061d04111c05010c080a0c03021204020d060908040905040302160506091002011b0203041403 75
    0x11000e80003030040d4038060820404601401e03040c02881d0510000f44120364441c02d440c0a00741c03146460002401401010784100f0401c0e00d4500040410b41d088212070090030126500d5866202408503c08a101003c22400c000d01d0301c205c100b2032005606c0442c88110152503200254000c00c4261703580c074013508541c003114007244902d1000c1030380d05a1003036041040394050f043d980e034080da00420000e001030f5a41019410706040302c080f90031341507030b0348005c0c410b000d0005034203084891010074205040c64650303514512000081c03135641c4a0070358080c181446520b048108a10240c1c0440240440080600d024220387d100382d506451340c5007000c000c030790000d100c0d10a81d4480c0e1342400f02580c007900d0f40d80030310002c000303915000e0712441d40740c3c03296001241130031000300014041100c0006592802d820700078103096102d080b0020890046500f08800c3e82c801e001e42c0ccc5042005c9810b0305c40600f0041c0d09034010f0001b80d0002c110112052055480e00350080050411281480e404a404c4803001d010907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 191310800 1250 191309550 191309563
    0x8030f0702060f060306152d030601060525020301181208060118090b0f1203130503010506010f0305060a2c091204061b0c030b060f0108010303022a0d0303020a0809 72
    0x6500f640c4020700051640b644c1058030194010054404002c650308441c0d803130703006801c0484131122303050003c0301d200d86401d041108900500c01460041e003460183c1e80e2510b000c3c43c81c40f145030b00c070300c040c00205002d542c0d080d030003000750f00031059aa101c4141613241807220321250f03000364000f20300d882002861550240c4015080d43e40c079481030508550030941c0e50340090440411407604481900001345e0180c4030445041e001041080013951246000c0d5400b03441d14030140c02441c020303410701090041990700441d182200010509001c15980e5450012401d0011594401d8209048008000c0da84a60304500f91180b000d80e081d6070202551180861a541c81d0300200d104a25031040000f008814801c4245648110072651501400b1340c16480d12009c090301501b09540d21140c00003800240d00d09400c1d0000403600030300b4940340e95850350703c000e07484018038041c0807004021110340c0b00444426190644544000805d10000d050f12401c0080094101703041d0700303020520f200003081c800c2c800017448 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 191312050 1250 191310800 191310811
    0xb0610030507050927101809030c1106280e04050105100c08070804060801152f030c0a0501091103071a0d0b03030a021b10090b09010c08030f0702060f 66
    0x280f40c9008180070030701a541c0814000e95400010b1120060003a030f2034600514080e24070500d1803004641403503c00901c0401c0300d43c5154940e460410150b00081e00115001070241c1c0007400010203070b11500208185204031000030040c00403414040b5000044020070b1028a8020f80c4ca01d0301c000c5210302840300700c403400c0c0221503201140c44242e201c0944684008013003907100d42c0640341010219503030701306207801c2604008080b4098000601c00907601444180202c080c9103450b003000c006440703440c5072060364007c1001c400c0400307442e1580b48120030402c903920a40203070304561030303502d0908109000380115607049a10104680c0000d0b13040c81e00007000310070b642c80780941c401d0075414020300150b954412054215425225000300c040d60f6005c0c0081d000c840c21036006031003034600d4003844031214011700c840c00344500056501035180503880b4050b4001c0d101c4880c50545d81d03851410061300c008000000080c002140001080340340d0020105240c0281c000c1c0d003c4804c1520740581e039103182c2908840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 191313300 1250 191312050 191312057
    0x13060e1003050a0602090d02090901060303080703061d0901180c031b08070603020306031c02060901050705160305090a09020406051210062703050607050a020f2e180b0610030507 78
    0x902c00003240d0700d1790050010751001800b0a0180c5081d601003078018900b2101000b16942d5030b542082071582104d480b581c4282c49240c2040110f0508118400001d0a02440c1c91044821000900505130135442059030014094159501c01e52618011819480500080780c02d455840c401031103240302d407135490041d00c5014002d03152082c101078084000303400003481c0e10350600c5584030008041e0000d09500302101e81e03944c041c1c18580360030342169080d201c025080307004200341045409042d0368680c00e66403881364185066562440c41c00b00142040c12184c2100d81e1a0384000380003c1d032250042d0080c607031700d420050800000e94452401c6c007040c905a228503800305e42083c20350603000c0c051580428151502284190a044d204c2d10b900c0e02e0329100301d40d91070109500250104040786c0421181c00c50b042200c000700041241d030441824541141e44420344550920000416103040c01d420010300320b1503559111020304114106440360301815981c050160207004960324401d4031a01a00c0c0c4510a1620b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 191314550 1250 191313300 191313313
    0x80c030712030504030c030b060117040c0614120f0603070803030103080405131805030a030b0f0f010c050f010906020405090a0b0904020909011112070201051317030606070213060e100305 82
    0x90821802409000044080043c10070000c000603c1d02d10900e80078500860581003d450300c0d000160294140a405170020b19101007000300042e10241d08005a80d420b146c0901e0701d43d1800d1403a2082e0080040741d640301883c59080141b10481d20600a20400c001c03800c9078851035840c0b1030551603100030300002d480150100011320403402d006e42f00c000480d049420014040d804006600a461080d8004907600c0d0400908000c00681c140a0b4000185080301e4000c3e0010207440012003135031462041c0c4e070500080441900038000c00380720110811014000a00030500b0600d0180000e5009008540c403c035644004034104550503c0744010b0408081c082030215200c41d002c00c407080b4801000340c51383d992a0400c288201c4541070141c000740e1400150300381141403210b0040d0a40b80001c20710600500031071100d40210710300c400603844102e000114581da0792100c40104526109140c1e000c2d40001211004400e0600507034401021109118084030440e29240c0d01f0301120203940c400038000c0e074400d8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 191315800 1250 191314550 191314559
    0xa020a1203080c07020f1f0905030c0a0918050706050405100f08070e0f042d020c06040f0201030b090106050c070b090d1104090212060906010803070b180a05030d0c0306080c0307 78
    0x24004d085903400209071100a40c0d104002034241c412004004203491f51415420011030740004008000c0e00c81107004d45149100900480c40c07050503071080d04149a2900b10b40c00c855054a4240c2e20210f4208003601c920303d4640d000680298041d00c9107500034841c1c5101215194441c03400f6680740c84407a6226802078440c050201c41d81404481d10036409007990701c0d04000303680d4a03c0b45541303c075040410781c0000038581002180d0040182400060719004203c1803107040b4002c00d0082c0d2103540101c202840e0591400100c0c020f1105000c099000564040049540c0303070003001801c101002007003140d506580f100d07500349140c094581d00c82c1c1c11240c10001c0c24001202c2c52204410a20041c1000450703030750640000301080c041e0702d143d10590300b0040600c40203c1c0b040c4030450140c130344000290f02e440107594504815250041074607003000743e80c00c9454110300040c02244c01503134001040340d84403070b24407000000400b104005000401d11342200041d4940d0702051070f0380385010040240164503e00b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 191317050 1250 191315800 191315821
    0x81e0a110906130c0e040e060402061b01020f0a0e040c14030703020a02030c0106030614070206100b0f1207020705040614090708270105060a06030e0a02131401080a020a120308 77
    0x2405455018407201c814005103440751150131005003840e503500030003a5406003030008841031501c021059400040400c800342c0c94040880710062020203102d080c0309141f00c0d4207402406074040c4004101d000154590182c2d41c440b04a14580390211810072030300c00300c045d0075100d086991401440b010010700000c2e5141e4003d6024103841c2d841401520b2500c41c0b07000c840c41c00c580701a00304076180c07640d4002c0b0076004c0800080d0b5a510810354001070802d802c010042c080e03140207502c260200c44400017002d0050104d40e0090f036014120740d501c0488141003542019444000e140110f5001c0c07885d000b80007c405029886e01c0941d10000b6144040c5da13202c02c102220848402008044064408105802008004840c1141c05103051000141e40d0400d00c003001044038035030b80003008060504200c091020401320b200307400380d82d04844004000c24401d1035030016102030340c40116942e407020300005903503801041c00200103200711030b0380000315100e0400078008c081c5d070180035000030000d070f0000300c1c1d101e00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 191318300 1250 191317050 191317069
    0x7030605031f050a14130c0e070903060902060c0d113a180303090f0b090303090405040303180609020906120d030c0e040c02030909101d100f081e0a11 66
    0x940c15000c11701e4007400000d0060f0500c15103040f40b0401080c1d041206000140010001401d0b484240060504001c00020b00c82c840d1400090107513952401c01c64110760358041140c1c143d900703503c1034440004500e90040d00d101e00b1425030010500a0740c160101c43e48a503901c8051030040030b8007400b10350841441e01074660b07030b44102da0782c14041c1e40c04c0d000c140350300b1751284800118800d9030b8174110345041c4203131415070f00c9596001d465030410900500d0019a0301205603261801f041d00e0010741030361641021006404d10340c829016021081d0002802c0c80115008405214004d41c3c144da004e458501c10b01c9085000c4542c3c40045801996408554a1094210001c460651f24000314030615000009045500b10500705015078000100c0e48490304082140c541c5c808644903c120303070b43d032a11050b00a480880d4954101da80640701c00602c2c0d03098500760000c0540f0440e0001e00f00e4a444507034081d81d0b040c1c4c2d01041151203e01c214186001d0000050040a0b00d500156070b4100d03000366000d010b0f5070324 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 191319550 1250 191318300 191318311
    0x60f12060504141e040c0e190510030302070530120a0f0806030f0d0e0109080106030602070201170907060c1a1f08070f060c05030415030507030605031f05 68
    0x1912410000381a075524010394412050310003004806050901e08030844e4103071050b907641c40000da2001c010224030314900b000c04071a00e070308054503140c2da031040d801126a0403210f40041280b610050150440c0e80f00485800d880c82502200d10f010380f16410059812503007052100004502c0884009a222070b0311381888a00c0e40c0d50450b2240b40303042c0d43d9224940c2100c0020800110800d40c00700c103043c1d014520640200094026000003006908902d80b078010810742607051081020213600c0d140d100e190303010010076030f1030020000c01e81c49103081c6000e9801048141d0018102e0309461042580312000c0b40d006103100c5c8000c1126501d00001a6102c410f00c0d40c00360740c105039451040c00e0a003a94184070703224201e1130310407102d180c800205041d40000a03070403150240d88124800c0c010640075a42c44070a03585242084038a050b2a03181240c42d6200700e07040150038850304400600c1c015019086039000e400f11391401c0c019143c030b6070141a6656584c0b108800e07403003501000042500501d500054010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 191320800 1250 191319550 191319587
    0x606131a060c032106040c17040b0601091d011a03070509010810050d050106150e030309041d0307050309010e040c05071104270204110a1d03071502010b03010c09060f 73
    0x1070004440c0005030214210350700000c44c1041000514a4036200e005013002650811941c41015000032200d4444010b000401c020b1503a400314000380e0058040e0720043c80021744003410a007640015210100b021700c16030302c440303002c0311035403400340d0102c800d5034402c0415580300d90130584c010004540c4240041c00e51280c2c0200e0040c046a962105010114128044c0b00041007a03444d0044034a82c0c07400154480082000300c510840490382c010080f0381042108a8010516010050300c881d000712840220300364501c00000e20b101048404006400ca06c60240c8400c48000d4001c0b0507c01a00c03c110440c00025004020503000039800381c034201041c600150001408100030000706400780d40d084000e038a244810302c0141e045203050701412002c06900503000c1d040c46401e02018001100340c11190701310400645055610391010450100141046c146c02e14000d4602c400c041d0003000a6180c0c42d0095003080d0700c0c04400d5006140150840ea12903076034603031074005c45004032034140c0d90600742480d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 191322050 1250 191320800 191320807
    0x30b1008041e0303090b06011d0d060b030a030f080106140403031d060a02071a09031507030902090106170604050c0f090402090604030c0e360c09090606131a060c03 72
    0x241d0b002403a4980322a200c0d884c000340c0ca240d01d00b0300d00f180940003490a410408100381d4400f01d0303e810500482060026a552003a0f030300c051501001030482501100d4040c45603c0c0d40300c09042d03001c0b03440d52002000b03485198203030b40ca0700e03c11140b078070340c1610700c02e600c1800304000c0000a10440b44001420410008030491099160000324164000c50301c010042e80001700510880d41140394142d82c4542c8990440e24240c104c5000c40d4495002207039034548801f28000003984c140c00794010702d2045500501240b00b96031a00009840769000b00a981165804070000a800b0304007440380038010f00b0f5000d002c0c1d06003451a442040d15900404081c1d0700503409100c00c442a0b01c0f8140544003840c421803403402d140d404e2940001e034a040c0140030341000d00201803260410a1140d20708007403d1000c1203143c0080c10b00f01210f507e418615201c081e04064000200006004040341c00341c0180303011140000307041100000c0d001600c0c1c01c4404220300d68201800702e881c91400400a065a410180c01d9a04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 191323300 1250 191322050 191322083
    0x702130c0807110c130f15031106070201300b04020304030926010203040c06230f0d060308030f010501021902181003051015050405070507030309050f07080a12030b100804 75
    0x16900b10040c007051860b01d8000020944401d4041c01542ea40c592150320b0321f0924503102c004c2e442080204103401500e0000b49035040d13901c42c280301c049a0145001044203810703020f84600c2170640c001042c04c0d100707141583c98160ba2415000302d9004079007651f00c488040342442842440c481c0402c201e001034401c110140100c2600070b00207544128040c080004800e840e00d00064841d450030892840c20440000314a191000c1c45c50603201005050007010342c640b4034011058008201541001c2d01d0404040300300140d0b50600201c0905075007080c0e00faaa024032880402c02505d0113441d03402544040c00c43c19107000b0140342030000e98064401c07850603400b00d80d25102d00f0f003080c107200c0503440c1e070710b4403003041100881803c041e1038010310703080d10100711600c1d100034018510f00840c0d4006080503120201101840000c100102c0308002c41e03815600d509540b01390469540c00059000c985504d4000c4c22000c0759030180c411010f00581c00b9020940204490300110750340c0000078030071190380403208850301 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 191324550 1250 191323300 191323309
    0xe060901121d0d03020c071d04030e0406090e030c010b0103020f09010305040f020409050a03020d0f270306060f05090a020708030c0d0204030609080918060f10170c0702130c0807110c 80
    0x40f40321070310010790703511100701a54200704941e04030440d40709007444100803d40690404a44c0f0940502d498690300f102d150003d0040c00169021445417030904090340c68000b00480144002c122410080002d82d490320019000d81c001d5071180c410404091181d0246540070340c010320713806481040f216048030318503800a02100d402990a890075804400d05008040d0100900a21003115040c00b802c13803024408001c113200083c01600c2c041c1c40c50305e9905904825107200107406550301c1041803002c180c035581d0f52000c54203540b007104d21801020b004034585203040e01c220b5448941041c0caa80c6583c1da100c1c01e2150591001313040f8102c05508200003c04030341076100e031001e920301c100d141c0c4d03070340700450800c0040c031002190302d2400109640e028013180780e56036010b812032600c0070b031050f609009820a058408600606044600c0883c20040003c0d0b9680a801040310904c01c0300c00005108441c446441207502110350380b400f040c0b030f98010601d640d02482500b404550460308486801c00c032040401e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 191325800 1250 191324550 191324563
    0x2010c0602120f090c0a0306090816030e0406050105040f05060a050717042301081602010213090902210d121b0e09061002070306050a020c0316030e060901121d 70
    0x401c0e040004810300c0300c03241e60100c8103130b040300b8541c000303115031542200011240c441c07910008110f540d480400804000102003540c5e41a05011a88030710121141009450f0f901401c09180c416480c20b030002c45c0070760045c4180c809407400000000038460803c8241b000701c1c0e1040a9880500109020082c001403214601d10001c0300c1000f241030f260b51a1010386210f41401c00300c8020a40d01c91440c682d00c0d42da00010080e80515040c01c00c0320400c081c81307030590081c0f06200b060ba00301441002c5c0803587c001244c0140b44558400c0e030b051060700320030000415004180c1c298520030b503040b050703400b0022445007081580510140b01c0009440304214402110f242d01006010045007111078182a10b28126140661151b400d44181004212080d00207455504d2400001c100c40d0303030b4001091441005505980640903454100c03680e0301c1e40c030742c40c181881640b02402c6001610190220203282402d01c1603070003d58042e1203804040ea003e64000000c2c003540302d040a90408002d00e03107945a00e040029 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 191327050 1250 191325800 191325817
    0x70b040801060e0c07080d0903030f02040603051009060605040e09010b1e1509130906090b131209360c05120105040606020a020123040b040918030f0c02010c0602 71
    0xa2040c5040b810541c3c5030b80003082c00f0440c02041c0a175038041030a21044444402405c4000101901140307000d9000f08800b2440407a20b9201107030100310180c055100502074925809099440c594803500d02003a94514040c50b800907405200800485c421030f500541c1003402d40001080466801022490300028040c0b0406000a0045c0345003941c2022440f00300c1c3c00ca040c4580d0b918058510000c10f001c0404164002c40c080d42c1d80ea030603014410258851074850303900a001c00510306007803010b01014808000146c90840d0800540d90400307000b000c04104880e60100d0021800310340704803210b603221200c0d2145901600d08000031224400b1403045426445150711066120201450240c0000805800070780c000c6143c02c000344111500021400e484990901c1c0c0398007000403c6075004610003000304940150302001c100031464161041c0a8001d0710704044017040019202d0b0001c4041201186020700031071915102029068411074072000664010304101c02000c8641d500d0404a0f03200449 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 191328300 1250 191327050 191327053
    0xd03170f0105010f0e1e040906020c0106030b2a1c110319140121060c03140703052e0b040b070c06090317250501090308061804080903070b0408 63
    0x40c00030b981c01021540080c0085d2421101c0c4136240c80c007042c0b0715180074642e1641c0320480d68004006507070301c2d08441400d6900020079520b410502c40000d01810381404106d44084503000080c03e404500791030281c4210a170b5224840900e000300010f1070681c420300044501e110a0902c862480407035015692807007400901555581c6805210764600c4966014a680c40707c5c2444880707841118118845030540d6858642000802800700c00e407640b007000004000c1110341050a90040e0b03e40680c48014000065003600100c0e42d02d041e012403ca40c01202c0c80b4800801c04901c1c42c102c4014080b2910360707003508250007054291107001203c0640c00c9548080440380c0001843c80411410400c500c009211078149492114119030764454004044100c0d0505c540021460030448900400c1c2894000078a0800d82040701e2715092450103444000b8007607003c148110007042403801d0411303625042c1081880e10310440d0700c4070b9039031146d141d01144106606100e1120042040c0351003000078402461b8030300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 191329550 1250 191328300 191328331
    0x4030e030303041b0602011a2106010806010303081003020d0f03022401090c0302120117160b180609030a0308090106051804050c0105070305070803060427060506091003020d0317 78
    0x13074198000800c0c0c010f103046904084d074850055402003814800500c04503840d41c86c05d0185080980c5240d005102072560344125400051111408603206040c0c0e4013030b50324120306988041e0300700c88030346d018400290401c0328581044003180b14100908070a031300ca841900c1c0c2c0705961201a0380c8800d0400110680c680180c001000416128819a00031001c44d003000c1d400d0406000120551410500ca0b0f04140d0440100e826100001442002d07007044034660209240e58440c031102080d41c204800c098801c05900220b4007031458a1000c0c3c0d40300400080080c902500301e0707542102d03100340140100301e03150740701d40c0c02051940e22140085803e10f0b0243c07505050b4940380c00d040c1d1626802d07210040c1400b00c104448400300b544141205d086982010744541d40b5112100070400404464140b8609040001e242c940352008008050210fa40215018081621203030108490700c1c10540d1204a0541c034844c08000604000d00b0091415029041511001c00c1300020841210300888110750401c0418 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 191330800 1250 191329550 191329583
    0x1030e070b1c0912080901110f09190510110f0f010506010210110a2f2a0607020f0d0b04060209040606020a0209180309040207110103052202010804030e03030304 71
    0x2c100c421850b41c20000c2803110002d0b0b615443d0010100c15202c00412001000040781034600750040c0000e8400c40803050340d030359001c4040400f150041c02009215298101e41c0c403900e015403000807400e8490080402e00a078007030543c240c3e05101e2410264440e40140b10428140700d40c1401100000e02441c800851a0b150210009080c0601328000d01805c0d460400d000d20301015450985407009040e0414001e00c041007801c010401940741c01c44c1c0c03401604071802605081021480c0c49142040074031a00d4041001318061503015212030f562034010000740454005860003807103a25503844003911880881000b51a88118020100d80c1900c1842e00018082c416007080e00c2118024100e40c4043c0c82d0182e00c40c0d0004400a81c050711448800071403241000114105104503615000b008200710350354a11450850b124507001310205000c6850000000c065884001c180c501d005035820402042040708e90041d201200013810550801c541d00a10452980b01040154000ea0003801401039801c040b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 191332050 1250 191330800 191330827
    0x12010b0310050a06050d050304181803020c01020105100501080c0d020f0a0e0a050402071101080901320105040c090306020a0c17090f0609061819030312050105010201090305030105060901030e070b 86
    0x241d01c5103001d042900e95103000b0910110030358090712b0718024250072118200e84003902070b00784c8200c80c4a100404203030001c01c040e0001107140210100ba0028403a6940d41582d84d1407041c01e074424140400c43c00c41c0000c8880301214000c020055541000606201003810300c040160003140f550000b0804030502c80c10540780a50700400144400c442c25460600350307550300d180c2442ca0030b203828103008a80c000304045000a401c808a03280d42c1c980398820640c03000200980c4003d09110329040b0f041101e0020805003002e000e1310104c0103003038031641c0405140d40d480c1c0000350b100108000400451091510000384106140c481e404003401c412500c070181c80c420031842c524440d14040c4589000c0006422546409040e200f00140030111269100b4007000415080207034800000d0301014041008005c050b00020800759020300303120200803d0381c95a006a017255241c89000d03010071010303c010049890100001c0c1101d29042c540031540f058917098092408c4c40c0c64012090001001c07494840c0c1c100c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 191333300 1250 191332050 191332061
    0xd150e15040506010507021909020f0a1205070212070602131d0601020105060a142205010e07020307080715020c01061724010e07050c0a03030c0906020f060612010b0310050a 76
    0x302100c1c208268140007001a14a02c10706200900a65885110500e00d0010100340710041280300c009543d01d4988000304c02c2c0030b91040d0305000104002030300c403001e091300c036105461044d40c140e0000d10703405010001c9101a60000781044071429007c0014518110240c1c10070001408400302541c96a940240707884189940100281e045a01d0401040040c0d03031107012040480384203100c8180c0084948c4040750405d40c8620104050400360890349420754210780c442e034100c4e0003d03400804103440e02c0804a0b120b128000018020080510205020a0390145c81c4600d00b1800000140b505503c8404c0c20300351486640220a00c50382c80e00880d44185017841101c9100340000d115007007007a24014910307000b89041c01440c20f00d080c00380000e00081e0040c2d0443e038002d00700108803030760200b80d0f16004014015056888000980c0d8400014003075000087c00104c044100b00502000d035034405c1409170080e0003800c0d06141e59210035103c0a035440a000c0035050302100b100100e014071300740340000d09444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 191334550 1250 191333300 191333341
    0x81b101104030b0114010e010e01030207051212010609030305030f0a090b0405060f1303090e090c09090c01031404122a05100b1002060109090615240e030c01050d150e 73
    0x510174103401c580c1e000307420310344507802401c3c90700300c986c6881c0048000f130090810007400e9100f000e480c11001d0440001030060640741a5200d1b0711680c0340ca07012250348040d0700c40240071480138404184400703052032180303074032000f80746e400903100c2055241c00030540c034240c0d03003a00e41344c0204081c45080f10b840410f01d0340c400c080b0005200c40c002181d81c001e00c1c001c03c41c0314002e51520000007260760742000303114500841800801d68425414505019038541440400041c04207280c100b55a03410309004002c070784078540060082040804221041d03a07882010601083c00c0d48a4030300750001d254a08025404250040c002071081d00d441c0d202002c200e50008500c0d40c0b14400d001107140150382d00041490545041080105024000385042070103030803211604116134250f50004100881200790814500303681c846d0000201420310702c00e0305c203601d42d4661a9015041140711000070750062000340b21a40000c9400140e2008030b00400d50080e013150400c1050305415802d001030425102d481d0301045 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 191335800 1250 191334550 191334569
    0x30f0f0f060d020d060f1e0605010e0d0204021308031c111e0c1603060b040506041109040b060d0e060105100f1704030c020306010e071803081b101104030b01 69
    0x181840d41c0000c10859540748000d1041da58081a54200807103a008401d00008440041c00b00c4504c3c0300802c400e00420506080d080c901d0408001201e42c0318101c01d9100c0e810180001e2580d48254082c032020f98002c00c210391010300300520008141c1d02c104001d000052440079508542264503130098241d070702402002a84600c01c3c4420070580507020101c800f1139101045071a60b80071021145420b00ba0000341060080b40480400014004560004041d5140899041140e80d079041c04001c12512040d142060600050240900508182e80171120b42c010080c102030800a240805100b620250030070b1b0a016044500100501e0a16009200220200d8248050010042040205001c0c0080403061541000c82c0c080b605140c010981c2c2c40d686600601a1074440da1242040c400015040e241c1200140c0e00400302d01940c0a203120030b20a40b68043c03c41450800b07031503501084401044101004c40c001c65010030341c2c5111600c030b0680c0100355521155200c81c5913023015030300c00c1c80582c08071214 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 191337050 1250 191335800 191335831
    0x60516020d020915121b010c03090f03050a14010513110105270f0303070f030f0c02100206010819030801030f0201110d020105010302040f0b0f191503060306060519120512030f0f 78
    0x60100f40c0c0d034201b4841d10286060305039a106801d003280d0310881d550000c0801c424038480403045c00404180c600200340110340d00502c42131480c1d070702403c88001300c4501d072291441c1e044120005030000d40c400310304241494000d04000c5c03900c054040e52101d001c2100003d0040034145030490504075070070b00310100f00318042c1d41031410301e0b02d800008214940c001401c00000d81d0b0302000c0719000320301c0c5100c450740240400d60300d00140c0744080e645850a00071007206205280c1c2107900d04036a8040558810391680d00c0880a92865882680e81203804908a042c060780141010594070308000f100e220145550020a140d40f560050201320b60107020070b04841410b140090340c49032580c843c440003400c401d652032410038040f0302614003208540d0304201c1c104211849066030066140d00100282c0e0b00543e01080031035583c00c108204010521361424456500c5e08040150000b007100c01d82901c0d01030303400e484084084090520017036001310341c003940c0044004140100c14490150070381e0b20a0002402420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 191338300 1250 191337050 191337073
    0x605090a020109171c170105060910030e0109170406090e0606041701110d090c09020415080702160f090f11091e0901060e010f09060516020d02091512 66
    0x16a6628003402c02038a40d40da00d8031811031800c101c0c161241c40c440f81c100810741d20081e001800502904103040c40c01c2220760020962780341c09001c40e07030000c00040c00d4a800c0e00c11001c1c19001741492280b4017619540c2c81c4403200c017087c100c03503400403180d180f200f849a485080510151942c0d025400c5500c40c0910001001442d48600044a0941d04c0035008503a0491744190003501407e5440b08503055400c0109060b28010600d80000355102d00c40c01c2130b244490707120008101240103501c20f50002900340c061a1a140f40174040051300840c143c41601c1c6100d82104031120a07880d40d50005041010321103040040105511071050220482c03941070100c40c03425042003c042c060210310306c0c0b0030313018142010758509945646210110015012848541e1b5444001d802d0300000302c2c01c980407505140803090700740d2080041d042600c0746900c0e0a800d0200c1c465940507802e0400d5030032a000200078080001595034070a00512501c44040080100c11226013401001c40d4409c07801149139210342100c52 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 191339550 1250 191338300 191338307
    0x905032101090b030721020a030c0603060503030c0721060903050d0501170c0126010e07110a0c14120313080709090f080c01020f04090b0307060c0b0a0e070503010609090605090a0201 80
    0xe0845281414200540d1b5103001141940306090400960000c5481d4000041102e10314640e8110303100341d2420458a5a59024552039100340088010950817a0b20f06120a0410040f0411020a41420b4280422040d0b9903e000c40b10060810f601207100803d0b19003030b10119008032409001446012950044000314860352401c003200480d05102d5900016004401510b143d000d00074040110380101d541d43d2203a20350166000e80390390000602d076104032407540c4030018100d0412540002050200c0d45030082d0a40d003800c0d05110294001c6050310881e02a00c03081025141040c00c08041e0728159180a1080d450048903901c00c0c14850b0601c2c081401080d003032050400c1003500700381c491b50746003080103284d40244030f8102001c805003008500800c0d000300581c00718003000410f9080b01c502c00d45541044d102ca1070b03d424000d080345294400900d42e0047c03a001280c0c0b81d48141c045410850301c1d20002401e651150b000903820956852500040c003000740180b039085040c13180902428003560300000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 191340800 1250 191339550 191339563
    0x1002070605070509220b031504020315040b160c0b091c0207060f03090623011703090603070c0303062402060a050c03040f05070b032502150a0f0905032101090b03 71
    0x11141417000a0071100c0003603508460b102c003d0041c1605d22440741c56106880400041e1030036801b030f1181801c0305e900f2185905e03944e070045420003202000c590383d4511480300750040710360210800030500c2840c0c000580121305580540100009440c1f460001000030b810706e40c1910080086506c00301d02040380c5034001c010312506d40494540810076004070f06040015041003001250124448903503c48401c403843c8109040e07070400c0e004415802c10b1104d0459603401f80c401166888102000450a01030080159400c00c2c0d2080c100441c0701c50752544040ca50301041041005c01f441044188010307582e043c800d407075110340010001c02030340c20070403a10758080c00010f20040848501a503e18203000c030400c2150001d000480d105a90303843e1038040b11500060380c64071501d1110341c1d8101b140c44a4008a2058010340300030805a8050382c0e003880c080302910344c0282c507121443d92445000085002840200703065511405d076441e40305007229540201c1d800592015041790324000f013968a039680450340703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 191342050 1250 191340800 191340829
    0x403020f010912031805160e15010504060c1b060e04150f0509090304230f010206090604020108060d05150f06090103031b32010c03020a050f0a111002070605070509 72
    0x302c00c044417000300c0394018020300c082c0680c403854a541c9090141100c04505480481c020702c0c0f12074645406030554006201250303070220f1030900c404d100d954401d5014803181030142c00440b8601a40340b08001500480350001c400094401005208030304041c0a030341616844454540d5020f441e00348054080346e841c2c05800d00c2004606e01251380c084042003580e0140c60b507030340208800c0356074501032160701d01815240d9008091201e82c0020b95800440d45070b104000da100a0a12035840354011945130300000c0030b007907020010341c3d42000420b004110183d45240c80b501210114104580e6801b905c035070060030940b04022040c01400040e41c421404604951b41740b000002032103d82c07034100d4403503800b0303081d42d00d200c6102e94600860b10310b07007004d480f1050004002048101d5144000300c00781c1c41410100749c08a4800c20260980390800001408445c4403490400a150501c041c410b00b0502214100d0826a030040f4245040c00114402c07643c201c0704a00b001458500e1140102d110b80d40014407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 191343300 1250 191342050 191342057
    0xb03010e060d02090a0b03160b0a180b13030213090f03030f0902150910080112081b0313030c0501020d0e04050405010e0f0f010501050402040b040515040306090b0403020f010912 78
    0x21a5031030322803a62200b074083d80100301c50f9440c6006581c550013807241c115030502c83d20810001070441084800010240c61190070400e180548000041d225226280003d240c9a41d810500061341c41c00301018242000d4411000f5003c5851401004045000c00c000e51410b1403030038031a02c00003003040301d031254030a9050502043d85000b5031054001000030510180d082116450800c110390101c07002028120021238403c80b440114510803521400c09000f0300d1a030b00e21004000f004140f00d100a00216006001a1103024566000c036605540204000300e00d446007181c0300344200320700ca04040c00035290a200400074002c601500a001e2686096600e004940d03540c0860180182908080c01100c9082d04607421520128081e0780d03203507944c2681c4d1896500c1c00780040b40c0c5182600841c0c2c1119204001a400c042c100f03820001441c00002844007401c404005c0000060403e00a03400d800707002d403000c800c182c9882c1c06c019042202d0981501146d925094048000a40c0c900300340705080031b0707441c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 191344550 1250 191343300 191343329
    0x290c0c03030f0a0f1103040303050f0106080c07020d060c080907080c060f0c15040506090115080c01080925051003090b180f012a08090607230a12150b0301 68
    0x8088401031509100b841800f83c1805681c141c020f0106001b0360084d88603582c10005999400713501d101c003d00c01c2c010342d0b00080245004c910559420001303001c21030700042060f400317424603a0b580c0d800c8031080b000c0e002c0032a40070000c008030f0f204103002c002e00074912880034085844070000014214403c207603030040424800300b0340c0043ea070b204100c065401c101c038080d110740600340b5080c10395440344c08075074400c004d6003014641d0214402908400044440c1c01b401007410480d580c0066900481c000c000301070500c6481442020850024100790304440c1e02400b40c11201d00340000c0c1b0103c461a1284d010900d41450140300005558a51a40c1c1c40389603005100741c10040180840d01f4481c010030380c03030459800c240c0711011926002495379004160000441d5146100090031744100310211601c100c542c00800000780514020030070180300c01140840d02d0641602d02156980e284c2226007200001400318480c1d11803003a80c1e2261004850b01143c10000c01d80c03401d81145000e10050040045020015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 191345800 1250 191344550 191344561
    0x30905040f0f020a0c0204060902040e04060207030c0203150906100509180102040f0f0f060309021e0301090f0303020310050306101a04050a0806100909030c0618290c0c03030f 77
    0x142d00c0688080c8903044199aa5004880700030308500c4460700c1039205520348030001078140c2251088904442c2c0481c100021542c680c0c4501000750840c0f641681841015602800140c0c0d062080342070241c200c02c1445007078140007075140d14245009001d415248010300d030500c07040e0303100c154850780005241e4030711014019410400340a4026940708104080d00d0301004189080080005070603101003c0054802503a00d480446c192640d24001075044400d8410803054058000080c01038140041c0002c00d0781c84165541e03000400c41c03940f09034000303580801480111205911010001c040840050426040c2815500390121007845152903c0c51501141d219502d844000e44004000041c410034040755203d511540b5504101da1180000d1685a40884c03504039a1090602c000c0d01940d1320740040c40c5a61340e04005090b0381c42a80c0b0b10f49140700a120028002c10211803003002c14407a0401c0000f030b00c440100110801070b04803000c02d8814024802e9007400041601e92106400c4140316150301e40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 191347050 1250 191345800 191345831
    0xd0210030f050901021e03060a0302010c0c050904210306260c0d0f021f0503010e0910110a020f0715032004080321040b041103160312180303090504 65
    0x7005051807941c102000c20005a4042d0301504500c480002a0101180c44a02e801518802111030550020a152041c0059442400f188204903c81d03600d18000e683ca4100160111074200c07000c90f04014030310201d816031007090703203070010b02c3c1100e050900c40c1c203003890b0314103210001000d5540000507040e000207004000c100004101c00e0b1007e000c05071001e45078100907516521903030f0240e0260007040c4402d900c0000f8088d604132501415074800b03065900300345110030000b8025003580014401c0d41c001441d069201e01c01c00240d0000072407071a548040141010b03040c90140e408000803a00009000c1001d468020742404044c560380c0340001d40f8003061900071084882002c00c00300341400111340410351070b400000801100c0d001400c00e8010782d403907141d8589260710845008090540701000310f4002178002d001300c8183c403001826101c0001200240414000c015401560a91001da00c2d80700402d070064a02d00ca90006100c7c007004082c01c6440192102103984280c60040c3d540703d080301c80e01c07801f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 191348300 1250 191347050 191347061
    0xb0403050d020909040c0f081504081c05070e0301050705071502090d080406020307050709020c1f020d090b0a0b03010c0c030f0203160602030601030c020304050a0b16080c10050a0b0d021003 83
    0x185224041d00309400c148584107550b02130550041f00d0b881005c01c150070000740c85442d109071411002d4a650325aa540c42c00ca07084901c2040349210500c04009800ca000d0003401e1103101c5668a11549810140405003500d1014140c40e051200c2080044085402c03141d0090724072014450250f0340d6503030307480400c0c220080010054400540443c02099040d404030041034440d0085c0d0444180e56159010b1504030b01ca62500d42c003460340040c1c9440140d008003403c14244a407240801070274181002034140661f92008421203100c1003020070820004443d10403080140c20a90081010307280210000c3c01803a10312a0140511114810784020036100304122a02c81031055241d0b14a140d60b0320307010019400a540c018042802c086403c40520303c0001507a0440710020500f4403040d180c45101035035076000481c0c1c42c0100540080c03840c089540340f4004c1a0240d0701500038201e4a0b40c48609600305c980c0900303102e14031420003021600071761303840e41d0500459030100c0f6032082c0344e02582000d800130b04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 191349550 1250 191348300 191348317
    0x91205043803010b0c0c150702041a030d02030405130513080f042402010b030a0302030414030a1a06030d0302070507060807020a05060412170c0a030b0102030c0a0c030c120b0403050d02 81
    0x101c0000003003400040c550140044518040449000c2c5501404200082c1041c5050a0140300d040c0100c0e4050729254014429140c040c2c8200b40a044071000468144852040c11001690000030200130a0404444450103005904e000300003c0c24002d41c0940803100c21040640004004941854244c0e07039001118010b000e04450b810505811813031000003103c450380c060000d540f801d1056a07883c10007103028081c060703040c2d000c1c514150411381c10445030042030b0034241c0c1520407000c0c2100000c0c0c8902420440084504040c01245018420140303000070a50b446402c0500600142000500c00107450307003555524104940996100007003207140c10481d4001400500c075000c140703c140820b0b8258000500a180e0300c1582540c070b032401290030390740291854051440d00300022514540310768411002a541441507a01d03100e008600d140c509900002c4c2658032503811203040081202c174182c094000d10f11210b040301c1400301d40d140c1d1841031000070409418044001080c404006c0264102c881c943d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 191350800 1250 191349550 191349659
    0x60a030f021909090b131a070215090a120903050327040923191101020c09040506010e06120d0810090204170c191404150909120504 58
    0x4903501c00c560300113030000c4681600e520f0560b201003a402c5400340c003c0c419032600101e20380000000350f40c09403000607008014401318081e2243c0e88503e81368141d00140203600180042000c0c1005051070b02d91058042034400a21960280402c00144040305981c5244a00280180c4401d44031010000d03070841c0c2c05001d9442403412010008015040364107060361050030783c06009140111500c5a40c2d407602d107820801d01d9018004400000c0d000815040c0b5200f010b10544078034407110804511079600950f011103054000c40010301049504090007a4018021240076042d00f01a240c1e05440b0007902240c0410800807600041000a1100c2a2001031402e220b0440d500d69444000704000f031503206090f01139020300741030b51020389024525550b907101002d0045920743d15140030034480000101805800c5519a101c0d96012892102d07004000d00f03c03104041024822441c2c86408002c00316100414080c081c03000703024000071315058913203010074035000034411031722658680300391200410380032401d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 191352050 1250 191350800 191350849
    0x1060309050c130212060405071205180105070801090507140f03060102010605061b1204030506010b0313060f090210080f070c080c0d051b06040302030702040c12060b03061008060a030f02 82
    0x44680e0340e008007110178807240e40102d181c50b400d04020079203906403074600020b44550078074800b200c0641e11403070304102c07480c002c45d5035501c4d1051031501351031040341e0010124000f80010001c41019001b69507024409150010960040580b000343d180100c0704045042c1c00d001c4001041d99001750300420103408002d1140351100c06004c101c254002840d0f0411401e4040e01c01041459114070707007940d0170f0780c0d400320141000c2e03801c00303071080c5c842e800082c860640041035869100102e201403044030228014030b840441c40040c140180321511210150071001c1000138410010001658100607801c8100c1c3e01c0c000240a66a0400e00765a00030341846051324015202d544404680100085c03264003600c1c000c40100041c8800003549135242190064056002040a20014036141c0d100300072002d40d6052000c1c008240001880c1183c0c416001601003c3e00002402074518102811406ca0038841c90302c007981c2c0c500b66020501c02001444020101e0701c0c40c101e010115522200039500031404281d05241 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 191353300 1250 191352050 191352079
    0x1b030f0f0115050913080705030f0c070302011e0c02100c0206040f050916090918050f0a02011103070201020a020906031507030c0e0a0503060613150603021314010801060309050c 78
    0xb00300c103001951103079506481c00100ea091003890180b080d6509100020604043e441e0b031416944103260449060000b00110703103e0100030400380c408100d01100810703030181148000740a501c1580002120390100c0746485801c994894128040164180e40c1a840030202c28016641f1401080000f94002030100740882c40c040c010722004c5c00c5035411035120300c91b500e40004005400002d401901c0c0000d00b480f4017444604910340200c2d1041d5000503144d0340002e540e845450512074640c00b00500ea4100001990035507910159400400410101652a100442d80042c1d41c0d488065002802070203203c00090740b656081c402d03004d00780c0f110507800c0e01c0b0b460304080040082041190200c08100b80c180740003194180f80d1100400e65602600034071041d19000104a011064040c106d4203281d283d07041c8040708048001c0c8100100400d440240c0c032100e010011411612840e00111014291841c1d400240d0b0790020703046044600c5800c0c00070741981a810b0003400c195141c0101900001540704194 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 191354550 1250 191353300 191353303
    0x1106040b07050a0b06060a0207140a090c05030405010506041b030e010b0306070c05070f0f05130f1b03050a020c0d0f030e24070e03070b0a020a1b03140303091b030f0f 73
    0x6425104807130110342645d0b01e80030006d050203131908540044e8400c18060060340401300e1803500c2c00030001e040340c1d2601c0d41c0c1d20304502910340050050b40020008814882001003d00816401000440d010b0010f01e0300c580c2500080e91899035440d04040e01c0b1880c8130118007082d44011501d0380050b0a440d2076107000c640c064001e20b5885d00403034003480740b5100040d0341e024a840600c01c5d0765000f06c045642e21300e00420020507100340e4000d641040c1d034a02410b81480714038403600700654001509a007410031504000390480384000d0188003410b0040010a90b42d002c0420b040c100201c144c14500101131303031710200301e000300150000920341e4820004141558104000c00c5281900c2120315040380da51000c0341100c4d540c83c802c0010340c15a010300c0040c04444000c10103003840000304d10407102102d0454403003030800122900c2c42c0c2e0302c1c00407219003130061203241c68860a10400e49c00040d41382d41002d0b502c035691041c980c3c4034003c200e402204508410b0b41d041c000c0c1d410441040080f10f0602d0403800003076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 191355800 1250 191354550 191354563
    0x103061e0501020d08040213050c09040608010f180510110d0603030302031605160320070e060f030f120904020f0d0b040606030e151008030307180b090d1106040b0705 73
    0x8034054440c0c00c4c11140e003180b044004510490b8040c14450140b200c8412000140101030a036801000342072020306070a80396403055070020300f4001c0c00400c1c105201281501201e690021280f55520140102d801280c4009626103107030092a6000680448901080411380140b81610b0007203810000300000380355140c0c003c0c6008a615440174030348001c100405071201d00c9131010102883c0c40e41c2c10094003007405920b00f0303101d20240d01ba20401140341951003504100d41c50308003079031661100062010a040890080d6000c44041c1c1c01040c1c2189550a00d9a941c05c01c01c4191781484000102c1ca8419103607038064a0240b00d200b080145c44010b01000f1348042d203600c15189010b40d251240005003c1d200b8040e205034015410041d1585001c01c3d10203490a0000070141c80c60241d800c94005a00f09080000318440d801f150380310450420300b100c00c07012400090703003c0380102030280090800f6680c2d07c180209103591110050360458101008203040740100c0c0c1c459400e0030070101c0d24400703110000ca800d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 191357050 1250 191355800 191355809
    0x30f0403080a0e0922080c010204080609151b03150405070309060f0507090b0c030c07060807230d0216020406090204080f061308071109072d0203180103061e 69
    0x506042d8842e200c00d0002c1c0c4c15085078410030718050203d0f201402d40100350300510840c0030f0000d1034030f0907204007001826039005a204004541c0000c0800040a009102074017031a81070401c0c05849041141e55070b000d4103172484509404207030000115400c076201c0d806a01e0070700030281c4140315a03d800000038000b0091681c050b00c8050070708002c0308520302184240c0348600040e890b4400c03103600b0242c20700b5698205000c8062944010001c51702140000c001c000c0041820750383e42030301854803d600400180e48107400f8549900e04010403000c515152054035110005100010b88a0910480704100038041840c040c0d0050300d030410203e26612142c00a0040c1c0f50483c046440c1039107400c0e80c050741c0301307422501d903400d48062041d06000110440020314609010311044540c45421100086205c5c1068400f50085103200640c035885401c1101426100110440c05480080710040301035120710602c0b082c10700200410039124900d80c0280d0080001d842c0394600e0407502c080d5104402d0320a0002d000303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 191358300 1250 191357050 191357057
    0x9070f02010c0e060a0c08090612040212030301030f02121c0203190e03070302040b060706020a0309030306050306100e1803040803070b01210b0612060709090e0a1a09030f0403080a 79
    0xe00480e03280583d4110b0400c203405050545049018082200c105c807051200300c50340481044408201c2e59090080d10005080b201906840d060074410405070080c5200c000320645c00c20310041001c10074403140e08802a405035140b486030b0140e010741500340144010010000444055030024450b4000041c0c60300c2d084201159164428000056444000c0c9000d450351640c84200d0900050605030003c40e20f0326000f03048035041840360340d12034090342c01c0ba03008400026501c00e584014903900d070203004010481640a0003013130602c031240d03c51030000d81c0102400b81d02ca007008a48820864800002104044405c1c1e0781c8580d114040340307459920101043d5501c40c402c1001085144c00e8001c01510144e105400008903104c59446084540d00101501d0340302c058601d00f1301d000c19081c4103041c0700e2043c0355101961281401c1e511001c9902c080b9001407240e000c8180d4030000703101d01e1907581a01c50401c8200c21140d0710710b10f60707070302e0b5100b20300c6424041c0e14040740000c02c126584000d001001850b0701c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 191359550 1250 191358300 191358311
    0x102060c04180b01020102070f030302030f011d04030804080903010905060406140105060a0e06041503020d060602010c2109050a0b04060c030c0e0402031f1707090c0206220209070f0201 81
    0x103000311180a00e014030345090003180070380306040200c0c0c0d2024001c81030600026090003034545074000d64448031801600481d4002040020b080c031104180d90152048811162814840252001010000800045c20311100c40003007001d00901c902900e4191000400038801c0c10342901c0d000e03072a8030086d541240c02030304101501c03100d8659002182d050b60b070f018001c0340c2410710062049030988105c41403d0340100040001003070800d403240ca041c21001d42510050307510b5110212110891b8000c0d030100342164035069142c1042640008136000d00410b0440000410010381030000c001d040c20071000b0300c248074222a40c0100203040820b00d10079409803c042005400c003000550685001b443c440000460410031003010740740907805150400038001038400310b6282000700c91410401500020342c80344604800e154492001c019040c040c04840a050103000c0b41d4140207599020040c01101282101100b200040009502504100c52f00100382207481e08108134007402480c403188144c801542040b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 191360800 1250 191359550 191359561
    0x31008010b2e093f120807030906061401320c100608010510080f06040204050712050106091703040509060f0d05031204110d0c03060e0703050703120201150f050607151406010206 78
    0x30790250340c4c0aa0010f42141c1c2141c1002d004486030341005200009055507810240c01003a01882a04058410319100220310413030000013404281c41c03000d030414015904061307042000c3c61950281c1c0d0a503081c1d00c107030362160584c601c8282801000707110894040e00c0c2034070000e81c07200305412850160340e4099501c8510364988800c561220106c0c408549158420340115005082560250760302202e640f804a80c0000b000c4070002c140c0300f080c2d00403000030b1040803050004401151282620401100045241600e03040100f049120001d01c0c0a11410200b2000c80064407085403c000c1c056119094940d0741d00001e110552250f0b0aa5007556000f00d03000e90a03105040241241c2081034200fa610040580b841c1d9513070016000c40d18204116000b55040000000c2c010860300000c0c6225891041e01707aa00c0302c60007402c4a400c02e858181d1001400d40130408402c0c0c1804240640d41c0540b50a56241158103200c02a401480081200389140c24145000e06100310481c0780140d81c2642036861503180c0303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 191362050 1250 191360800 191360909
    0x30a09020a15080f270a020a090b091305190f060b0a05030309130b0a180c02030313030309060204170d0206010e06031e070b031008010b2e09 62
    0x200c0c09180b01054400f4007054003c040780c0030281c1c0c8420401400c00324031840aa1641030b000d24400d1003101d9600090f005001c619044108001030185848100109552000010b43c0a60b000d840504000200e050340701c20b000e404e0103a0640480c10100d1484528014a407003082e118041500340c80e0302d40b4100f182c1c4402e291445250046900c010011810600b42c44100000442384d900c0075036034155260080481600c46e540400300070b241e099680f900740700b01ca88540064071525440350046400410410501c07a400e40a840e01c03160701351900003040100c0f880c0000003881142c01041c2464280c0400d01c0003040d0005074110014a55400e84020f81d0761000c515400c8001501c2459140e000004110000c2c254200000c0050007040121020351b0380e50420403105038025910720000c0901c08400348024a024010040140d100781d8164224100e41b0a04402007174401d66202001d00f04a048001d80500c070301c028070702404141c0b4485145207007940b0f003850f0000040c0441c0044a20301a04030403c840e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 191363300 1250 191362050 191362079
    0xa020d020d171903020415081510030e10060605040317040e0a0e0f0a1104020904060b0a0309021005090604140409060f060f060504030206180d0b15092a180303030a09020a 75
    0x150f0100c0104061f2000f070301501c1c0080300500780b0020420070461320041d541e0f149840c01c011005c03500d002801e010b40c01c000d241014051915400020305001082000c640d100040f0b4080382d03008601e1110208014a80a10900c1240d000001140c10f03001032004445840d0300c002c01030f0424001f00ca4000c441d5505080c2c95014414008e0241000400c0b0305006081c190028031401c0d900400c002159520740c0341e01100f40c1c010311071180001c0e54a0300850304600b0300a043e100420401e041442c2403620305000a20544076502406003188440425590140c07501d821200c451540302c80d050221010011aa40040090340300304071300072080a600240e441c1c0640207c9054a401411262801c581c40c0c05210400141c0e01ca00b0780c0110001142c02c0c00b2407104510309004050310343d180940d002c0700b0001c010a00d10050000c00b01880f840300c48500800300f144081c105111101e5220ba12040c2c40b0a5242c1c0d40c440821003141c06000c00004c014805540e0350160301c1c2c2c1407084481c0382d481c03500c0e840002030160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 191364550 1250 191363300 191363309
    0x50d141207120c1701060302090a0e100f0605030f0a0f0615120b010e031009030e1e0102070510020607030e161e0f0e010b030c091f0206070807020a020d020d1719030204 74
    0x70107001481102c0c8688c0091019150190004e0131056488004403a4000101c500c4240c5841035403050007440641003c4100508003890803600b076090140000804480142035104c00301d650728500041101260414002040900d0b600585129031a4021300380010300c00502041c10f00d0300b5415a590740c05940444d0304102e001d802091b1400b02c4409641c000c00c15800d0603000e00030009420416665510040c9840d40ea00c0300f103440c051606503001920302410f44c0c01c030301e1241c0e0100c0303150a021030b800106c03140e20600714500440e00302c12400c401400c2090f002191042d1103200c0d00f01042010380180019840e003032a80400fa012a03039008441d8003090140628038100c80d15000400511854a000e16003110364050305c2403400205d640010140700242003a0401d48800075110707108550140500c0764018614104401249081c0b08025119501900c00a10811401440e40c0035911480d00460201381d1004031f88c3e04204240c2d02c1410550440b19144442000c2040014412803180c003d403030454 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 191365800 1250 191364550 191364587
    0x604060f1a12010f150f0509270709050901050f031c1101020d0f05250f0201020715051012030806010c0203010b1504170307050d141207120c 62
    0x1504002914045120500d00780794003220501c503030755105a060044a008100e01c0c0c54041c49070b4905120301e070300e40300000c588a090101150a050005070031100f10b0b011004101c2c2c040040c3c2080d01b00c10b4214810050500000c11080b004201480f43c1020141b410750b407003121208210382e659801c004c82c000b1441911a015003107080e160001ca141c100750401d6038107170790500c08800900398042d030b822604200c81030314174192610040034180c0b01a1250a42041580c3e043c0e01002e59444140c4400d100c0001c003c1d800c101110000c074842c2c034803c1d81524480c40e44030f4880b032440211030f002074024050617101d030b040401e21440001508502c01d010313401001d43c540c070303840c559a0701d8100548103043d1010050341c240d504c9040ba8809941e80b20383d12071806660800301350302d450800660122482010641d82d80c4c0b03030720410850001c0b91002802c11a151101d25080c10400300c48030800605016003444150f0403200c1c3c03428000800e404c8481100030f80e14551040090004401d0300301d5000e0781403004070260 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 191366906 1106 191365800 191365829
    0xc061e0c0f0613030f0f210603080304122a120504171c030605090c160b070e03100501060e090903130905090d0203071a0405070b0301030302030c06060406 68
    0x10814510f0001880100c140007d0951152101c0f1158113500032580401e0031140c9401ca0000756501114194481c1000d190600c2071510341449c803400b00c2c2d000c0c8030380d0b1003c1b0144807400c40001c40900050394140810740360910040d800c9100d0404000040002084801c3c100e0b40c21004400c442c4028854401480d010342c2440c5200b0303e415042505010741009217070749003800c040e049400e920700c040d03a40f010040c04418a2580120080070502054208400c1a4103da40107071901070a40599070f840101d0f0000d141100d000340103140210701c01209030900c40c03d1401e4100d40c013400301d004803490306810160703021651702c1c503034007054003c0c1c1c4603820065032210a000d1010901c1580c00150b08002c65543c0300c4100d001500e5892500102405c00101488020800f500007444012002540d03541c41e0b040007522a400504c115a41c1c0c400c02c40858a070b820503100300350460308504000b141 = true := by decide +kernel

theorem cover : BRFrame.Cov 191187050 191366906 := by
  have h0 := BRFrame.cov_init 191187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 191187050 ≤ n) (h2 : n < 191366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
