-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2493
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:52:39.246285+00:00
-- url     : https://prove2.me/submissions/d85bdd0c-1278-4809-8334-ec07219a78a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 448201438 ≤ n < 448381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 448202688 1250 448201438 448201451
    0x913170a020f10020c010f0b01091502120c010b120a08180d02102f060708220506070305160804120314090a1202060415020d060e16020d030605090a 65
    0x36008100342001d94003414203560800d003403492144020741240f048880c0303540c20080b00c0c001c40641c0340710300181102d041c1e4030301680d2030030844480d000d101a100c048045106203191916158008400780900c1c030a03540020a2065a1800304664581c0308451500150000581c01001440c108201c680911192031569140511080006c41414240714081c3d0881e4510711076490b029030000c09141c0c0c20800c0c08040201c1480c00e40c804501d02164016519a03070b00007000b0401450017000c0d0170f60300c103240c0300000e4006540072003440243c5e120b80d20300302d039240c1c01582407013020b03505401100d51040d4440c180c403c1c03e00002d40001e00038440640041c098000a040c1200101e10a405c030307900503030031b0300910303072090502010b015990400c548064503142580c0741010f09081c8082002c0d8040c1d600309100780040b00600c0c1061000758060b28003214010340d00d42000454880030795080f417143ca140100c8600380d019807203001e4105100032241008151038914180700982d28061600e8200407441d0700003d01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 448203938 1250 448202688 448202707
    0x16050d03030e030c0f07080705092217040f05090412080c090a0f080c09090d1404050909010b091b0d0506060c15091005010612180209010b09091317 65
    0xa02c85000320014902000500d410031440004403810782c010004101c4042079502c0f440651590300602a06a000300b8070804600400d9148407030210101c0300304a04084001c0c20f03950803d600c444403c1c010719520300468104140d034020101d01c0002c110903a4080780514103079558200141c90388141c81e05102856010440c010605815a8110003001d4030683d4019180d48040c0d111580703920a44541d407050488100043c103061b400d090003001080010402e100307001c401a45c0d01703100315501e000b8407442440000760702c0d507409440703c1c003c9494900003c2c4d00c26440e02805000540200402d41c400c2c00054070741c6084a072032040703074108061714200103216161540010518440c0b1041d80000d80b192508182045070201d2180f40180580c40c1100e070f50800505c10101620800d00c100c0c004200f140c021114900d18a411241c403900790090000004a480d60018001040c2a00524000070380800e03511041d040c030005c4d5a401240d05041e102c0316626940d90099180811000c070101da440c0030895222 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 448205188 1250 448203938 448203941
    0x100903140a081323030a0215191106070212040501140d060f0e070e0d0b040302030c150106030b060306030712020a0e04030806010801060309050d08070504080604140c0316050d0303 79
    0x400754080402c070f9440e00c8125000305080194000c00702260010300088035080710082020140480c045e000c0c01c90301d58241c00304024070801803005106024100060030300031403411680d00038100c07243c80d01d480c1d4052140d5000d02e0324000501410965000c02d46400d01c0022120a40c0d01b01d807000d19000400000d000e403200b085005094510b50314a0409074046032008003000004240d801c0d004041c0c0aa43d00e0b120102c4000b0800101660801c1c059454100428000039006a1150003401120302e00410500e8152502419400440303010804d4030050298590502035800620300c1150481d08504198000a44a80d0a0720410074040c0785242040301f15180c038441c240081c2172002000d486860203081c007500c0040c04690b142d002440060002c54068040d10a0030300c00c0c0e400400070804400d9004040c1c9405002802403000c4c40300034000020340103c10444548101d1244414050a440e8004014504a8000765481c4203401c4880c952049000f4110a4001ca800840d8905890446814180c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 448206438 1250 448205188 448205203
    0x306040b0415050306071d01140702060d061a0403051e010e03070602070b011203050d0507111e01111c0f060914060906031b01050304021c0c031110090314 68
    0x10381003030405140d0b0020203440d0004208450b41038050381c080360303035410b01298220441c0401c1c2d062032010203080d04055100702081e0216045884c000d601d002010380015009801109904080540340c0c20b09001c01d60155414450b280b4400c21144d007014117566440b5118a01680503805100010310840384000013508825444c101c0e010580b95198517600f00b0710003079480004103892030303c00e0100001c4d03250740c14240c860035160140d0703641c0d0070b000720f4107010030140101410b000100112001c0228245c81c060008050b03005400240d100720903c81c2440c9800d5941003040b20b90030304402d110310400c40c40c0c41c41d840d506016010780c00084940031400044014a0b103600f050038000d00d4180741804044503c22694004d00f0b04030380f541143d81d61417040550f1001e100d1204000d05204940d80445540035501850700148002c0041c800e102d40f1000c49144611585420b40741202c05503801c1007440810103812600c01010741700848031894801001c0d25100c030622000f4030106050301041c0d031400081c408503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 448207688 1250 448206438 448206461
    0x1e1a040e01022104260a080c040303080703020919141c0b0103080c01150905220314090d05060403020d080a0b01021218040501080106060909140c090105040314010203040c08060402090408030604 85
    0xe0605c841407250030a181d0b0841c052080c0403c0713010021840d441c103030000b502d003180e6040d9900e4426564480d8101d010750808481140c015422501d040c00048a0b034040c580a0b000c054442a5441d49c000200103c0342c1d41c0d4025508040485044d03c4003080c030021117541544d4000c2041c6550b5190144640c0c01400000101c136072501e130010010580d0052a0042c5001e80111a0141003800d501c0901919240704000c004011503003100418000506141c00351411140007807110412030701c4c03034480c142094000c5608600581060040c1c08040da0890101d58001a000d401041881c0300940081d43d15010400340700706101c004150844c01a41a41101d00c80680140007804156074800605010f44114006c41c40490081200442d01c00068030500303c0486080c96000c0c10354136007800e030b00300c03903408001e000d810003d04100100c0420ba1401c800c1c400c40300410001a920318040c103000240000640252006400c91300038000940d8410b100550015009504150f0740d844400006009010b948502c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 448208938 1250 448207688 448207733
    0x3050a230114150105030f1605040302090c030a0617030306090c0d0c020f071d0606310e070e060a111c0215010b09030304091e1a040e01022104 63
    0x844080b00015800c6003d2240c440f54840c41190401c01901c490004651410810f44c0b0400042c1c81151003040301e100901c03182c1400c0745010340725004580e211004440f10900036600000340a0481d0981c443e0b900106095120010440b0010f5011030b181d1001806e107c2c0320380074a0307022600061801045901d0346e25005c804001340740fa1a00040e48400c02206618060b000e4801d00142d5140c1740c5113100d210009540c400c0180f42d079030408214180d08110031200030b4460b00108000781c1c0060724110f0f149110b42103200c01c64245014140d0441e210010310480801101c0c0d0240300907034445000340d41c00303c1c02a041c42c3c84560003a03995940ba01010700c8070018904820101422a2034011039802114104501404002e82e01c0e0725114085200319848290903502c00c10042004034900c0e48201907030b042c1c20400c0421510190401d0003a1030184004042028001c111010b00740342a10030301d6280c07902c4038001e41c102010001c0702c042040c0400200d0306104000750000e4100541c601d00d292000d03468054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 448210188 1250 448208938 448208951
    0x110a0315150309032c130e07080a0c05100c06021605240a0501050a150905130f1826070b040f020a08030708030c0c0307021011011503050a2301 63
    0x107005014040042c400d07400b1501104001c002e103010a0490154001c60500e0329100100b4042802041030030145c034114010343e41c0075500b0b00d0143c2801064000e090140081550350490b007045582c00a25901c81417040b1076801c07000c0f0300301e50022582001c040d040400140c40700d0084899017140d9848000043c02405803114400d4004400f200880c0030159a0200741100d5803802c000d0345c125102070003000c0c2c4c462510a0204080c1c80200c08801010103607107003040803d942c80c0d000c10b5104544c84a03901340e80c2d44980354698480028843c020040a940521402e011a16261101105041000800340344100102203024030f504008a941d0203500140e482e84d145014180814100c074a80e208a21a2041c400001034150b4004107603a002500301045619544a074600f03400d182e4019400c4845600081c8040c0d8056a280710300b002c1e446106407900c408040b071003810fa83c00c4422405913018001402d07003050000c40c400141802c04294402e29001000500310b00000c4406a100d40c80c182640c200070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 448211438 1250 448210188 448210229
    0x2030105100611010e070302150d05040804092306010f0c081c0e031c050402042d060f061205071803150506010c0308070c020a050d03020304080c0301110a0315 70
    0x3085a08540b6035036500385148180481040c00e0700c031a80710180c00c65210344801d00261900b013400d0740a20a103400500d181c05040044d50007030f12400c440a464950000c94100007200c4035001340d0340004174005c403d5103075049241da10712100c44080c20f042e0400c8a1414407891882c050050412101d030495401900d8160000301c042445c0c094404110030641081211070b4041e4002058a60380c40c80c4540c401c0700401c07988010710043c64001d006036403064031400d0009000c40c08503001640131814048a9840680620340403007540e00c95840510f807007910410400c81b082d88501d41269401d1680d001244917207a249080f0f03010381400c100e030f480c0d2950b99200041044844e103035010302d480000d84240002d98071040151030b2652004030140203c0c100400280c0c41620031945080c1c620300c010300960080307443e080461086070300244100c0c0940d10025091101c02810001000001404ca00900806401c0302c0358012502403504000185601c0d00c41101203c0d01100c0c211000d4031803d504d081c040449507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 448212688 1250 448211438 448211461
    0xd0f03060815180c0d030e0f0901030609060c020c0303043c0f0e100302040f0e0f0a1a04020d1b050301020703030c0f0905150a050f04030f03020f030304051203090a02030105 76
    0xd940b1515440c05100c01e00e6280b0f08041a480c04c8070794010802c0144071105d40302555020040d90500c6ea000d48011924031880d42c5402c1410302031070203040c001402c2c00072031030400700304d50040c492a0255406001c440010380c0d400401c1700c0540c0d00040c41000c9107116448002420419501058822554010300305c900308520006002200c0b0181001c0840d143c2d1101400710f2020242d13285040c0251f40c100900250030030b030b0082d400110840c07000054600401409078102001408a880310f50010801d86080c40b980001042c0001d20120f503800c0d0700e0903da4000340003402581d4000b4121400000c00007500d8083c1d81981c401000c01800a654808061a0060040c20600030b140e0111303030b003158051a8944030f50350080c1610b401400d4810900400f000f000c00030381013400316804000d420490159442d030404040d04c01140700d542e04c0880c41070305180c0641020b24071000c0d581158800e10421000c00c0002030154103078400915010740e40d4491100c2c1030700f0084542c1c0065010740c2811700740710428800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 448213938 1250 448212688 448212691
    0x1e01020702091e070306060509060f0c0607050306031e030a08040203151f140d0b06030102041701050105150f040e190531021305070e0a030302100b0904050d0f03060815 74
    0xa1003251581a600c8040c1a01202c806d07020f00d8000403009c0c442d02c041820010020710307140507102543d40c1080a0503841928008003101c280f4000351021080c04003600381080300d201c0400b80000110f11441c44058019a40c0c01204914820040b8030301c00b141c29507c0601c2201d100e445880200c10321846e010230401071180401d80c1c01850411400000110498000d25400c1701c0040109642c036083c686854140d44140301409540d0316560030000001c4c1c4a4000c41264000c59900c400840c00e50b00d8541001000741d688600c08000d0641002807003d20040c0c0812074040e22000d801281841d15082c100c1c2541e2001d150740c110304c051500f0f040c481145082502c140c5240d0302500340ca01d449821541c001140c4d804610300070340006002c05400f1120640d900300c164071509620300560350724412000166080b205071300a034056003004000400400c0c072806180c54001c400c0e01c20b185e660a0690ba810781e00d03174442e40001d04008030110005d5416102e60842e00040c00b0840c100d804a03540e40d40f820502000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 448215188 1250 448213938 448213981
    0x603040605070806010e0303030403140d02041409010e071704060609021602120706140c1006030b04030e0609060403140109081b06010807080303013c261e0102070209 73
    0x30300720300080c13603503119600c51441d410014003c0c0d81117494566042d42c16501100b142d0445000901048405500910142c0000c00c1c080c10184456040300c000c1c8020a081a0400c1c10f400464000b0040d00d0340d0081d54840d02c007004007400c004255110700700300c001040685c05c208001c074000900010011040a655201507008441c40300c3e216a2070480b1a55074041449900041202d0a815800590020010381a40c200200655049481e20102310049403220341044031000322210500050540c054040c00c04100152107192030030660000081042c0514400103262400010300da00035070f42d080d0056602d5581c00382c651616242d04400420f0842c80e403c905c501284944800060f507280001040030449002d0800780d850359017000381c40b001800b20310845135510074040d9140c0742c06c0c504080d8504020340107844040c1031242031501da40c1120102011401090100700c0c00039402d060301090111480300c103940e800c1c1c003031850b4011184c0a805205001b9512070380e80700400c900c514821500781e0780842c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 448216438 1250 448215188 448215197
    0x30601050d060609181101170c0706060506190206151e04090b0c310312110304060503070f030209010807080618040b04060b0108010f0311060f0307030c0e10120b0609060304060507 79
    0x86104011a41d02c41c001c0300368449006003401049c08082080028081e06005003c0462080d45850100300356900444141080910860032000100e074107000e000d400200d90300102a070b1200f103000142542508003e100200812006603450a03900d6500c0003000b40c2c0e004504041507c0c280150f090690800240d1440048500c00203200302404110030080f501101041d0a9165041d52110b0700b40d07500c2c0760941414000c000c0d050302130030042040500001c040c9039460503520f19003c0d8000305a08240c003080018076005011844640ea0880c0d00c450380609207241403500781d030341c4074002000c40f90484030b84c5032244201400c0c00140070840101a10484c041c1070144680702c070590045440c48002d00c04d40c2500c40306698107100041c55040d18a0314000001d003a81d060401080901d080d5034410350307101000c40c7d540c0c04a8040160050b10904640b141214080e00280b45001c014144d16044400d00700b0700c1d5520620b601d000d560300005d417602d54001419698803440c05260540040109136281004034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 448217688 1250 448216438 448216463
    0x70302010e0105070206031b1c0c180e0a0c091a070c17060c0304021504060305060f121002090a03050a05101a0a060c0c0522110405030601050d06060918 67
    0x550141c3e00b26524503030f01400c80b61850b520341c60b204280742c5002d901404154010401d002e516074031104a804804000000012900025980500100441a42d00c0c030f01c0c0700c68400802021044d1868990b00404254010900b0f5449082c1260607907140c1c1c11181c0f000c1400403009823050039100107881054810007181c841d03a44c0718030301740080400a1104000c0b552290f0b0006040c1020301024580180c4050100000265088294407442d0030a0300420006a914001c0109914000005040d82c08c400d035117107020f0b41040c40015864450300442c4800091300050044041e13128422030100841d00f010540b80d016010b40b8149803190014040d000909080040d081d001001c40740142d200c451004000a046a2403c5819582400700d08810340e101e180341003000031280c0b10310145201070407230701074000380a000300c400d00ca04458090545052a0009001c14407441d02c0c00a004c2e810341d013049890782940e081a24200000c1c00f0301da0080406103003801e050300803d80b42100034010b950711031648007405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 448218938 1250 448217688 448217717
    0xc01020a090b16080c07032102101103011719061d010b0109140418060b010f020c0a03170f0a020321070e45090715052a07030201 57
    0x3901440380651968034078044070341d00060313200f0010507505100c00251001d1030b581e61a8404001400c20140c000c01c12001006100b01c1e505111400d0040000c0304100b0000301c0b5841d075481140414040c0142c04000a0b00011001c24108401c140109914280d44544080d514110015010040c0c1c0e91005000040810580c01010b020781c0e9620391042e540d80c9201c80c90a806035100441686000d500260b48022040c0c2001050140e102128003c11020030800422000100001c9911000034219040f0307200c400e000341e0382c60f1001000c69400480704c100d01401800c6410081c0303d0021816100640092015140b503004005004c0c80010040080e001d0600c0e42d02003a40c25004480050019094640c0e60400d403401a8000001d40d00c501d624440418034001500410281c03030a140e01080581e0300705140803c103001c0710503400100a0060305540b440e0020751000041401041c2d003d0090109000320001e01c4500280f010340c2c6200b980f5601c40742d08800c5151071b4021400142d0001d401e4208102e80b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 448220188 1250 448218938 448218959
    0x117150f060c280f0c053d02010b0a0807050a05010c0b191e020706150501020703080f09040c0c05010e0105070203040504150e07050408060603010b061801140c01020a09 74
    0x784000300002074203d03d28181500720781d40050601c094494026480d10307501081c651218401d04901c6901c0c3d0003011070405c8100501841594130f280d1240181480c1c100917a20b05c0d4250056044038410307400143c0d011028164090301c80c0e020f48a40000d0983c00000d2000d200003081c500301c0307400341c81e40c0046548070401101c0c10301010402924000f120008035144004c440d201c1c400312200c08000003a90112a00b0883c1c0141302c01c484c603815103802292540500c1481e01c1440c803c5196602e0000c0a5464400041d44a0155120280c0a42404226102121019030403a00314400c02441007108007041c01001d0102520482c007650150321700701403501d8044052040724090001d90700190b00b003c0c07a000821003c0e0280e00b2040d0200031900c00002814040722100310302030030507030315515103c03070400307002914202e402002903201b40e06024858145803501d0742250301302c2e4150702e180e40340c94803000c0050b02d80c0d07030b41c040c01080e218a00040c0866000c0040d03000e003100802c01c0e41c0d51038442d07a40f80d142ca078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 448221438 1250 448220188 448220197
    0x1050112061a31091110020c0a080106060e0402040e0106122c100b150904110309010606230702060903031c0e070e0c0406110f0f10060b03070804110117150f06 70
    0x801031007a902d82d0450506c0c01420b60702078400035204a80300c00700402c0c0811480701c0d203607100b50348907034580d0400d0200b0fa03001001d0444030542690110f0a0900d080f0412054030818410740d806d00940943c25aa071040300d41102e40c030401c002c1d2100700602d5010840b09542244c0c282c081c0c0040c0078441d420300c0300381118051040c20b160010602124001c18010100c035903482403851560140d60f881d20340b00380145400c05140300b0000100002003042c603080c00640b140154544255049880341081d181c001c44110a40e09140d40503030f902d5441d0f44030740340801c0c41c0d882030524040000d44c2e00840340e0b425914070f802004595000d04240c544865640d100c0c03086800058540510100c8107000c01d00000d0721821840d4020080b2404941d1082d20804126050030001c10010318150000b205141403d181405801c0080082900e038500c3e6182404004040e81c00250000301510021051524940c2c400c40100f1400c9050f281d84a140d81080344020044141d840c21300e500075000413450711101d161450649 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 448222688 1250 448221438 448221443
    0x100603020712030b0402070b01120b01060203031603050a020c061006110d050304020d0c0e07050405030601060e0d020d02030c03030f070210050703080705070f080708120901050112061a3109 83
    0x8404410002c1c01035003c0c082072509550003039824010107002c0740100448500804548482200060450a01039203948058000009541c02081444038020080901140c1a001841c000426807109003500000e0f21a00181072044c0c460b540c18000300c0740103014000300700d80160f22040709407100c01e80a641c465400e86030300340c0444d80900c001805403d101c00b00201c00385c0302d549000c0ca01516043d00100d000403c2e10064002080401c040c00780e800e04000c101e000d0141400c12103d82204100010a61004803a009000301003110030001151010403440c98000d40c018152030b02da0243c43e04202a5400c0030100f0792017030499105860351580034604680c98a07806559000c00d980e0351708400d0f90640d0200340c007101c07007001300804140030031403900151206510a210856981d40030044070b50144034090502106a4500401046070880408506134007039440840031401c81c2444603a910034403140d24019030045d9021407542000c0d000c0082900e00300a008100e54458005809a40121220702200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 448223938 1250 448222688 448222703
    0x80f070302090a0e010c0203190c0c12030c06020a030213050904081b070911120603060c0a0f02010f02040b07021008070c0204090819050a09140607030806150708031006030207 77
    0x80c005400d041d008640d00031602c03007001c04e041c04c0700c3c60181e00b12540580100d00582000c00ea03016465181c050064071030601d40f6090310340d5110303500e80003070360079140c0300c3c075801a40582c002100301405a110014182c1d044403007152120004031000d4065401070400721149040203002140518000c000180102d40190303520381040c080c80290700c40000c941d4403030501d9105220b4000b803414020f001d15a001030220032101e450342c2104c0c030034403800403024143c14440c0d0004000c00203000715180903100001b0803031804500116250b4402c0c2c0c01061403950a0580311b00001c0c0118103118044000c0041c144203951001d22140740b680c04480d40f107010345d030440029489072340d504017501c1c1c190009000d150140312401d291840c064543d101c00c0004540100105401051050301e041c0c002c440c0360001c2c01c10307002c4c0751104c4030564001443e5100b0114010103002011000c0ba60986869590811840c6629949540c0d9602d070704060041e90002c54212145224122000c1140c610034002e459440354419603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 448225188 1250 448223938 448223953
    0xf10051b090303040b070812060603160e130515240412060609090c090b0609180a1b020106260a030f02120d0e1203060a1502030f0406020d030501080f 66
    0xc980c056500400010707038948810704c4080b030081c2440d001000da0510400542c0e54071881109491581c1c0c1c0c0c02001a84518420700c1004001d5400d50410007242c050751400b50358444144000030340700c0d141c00c03c240345018900f01c2000122081039240c641414005c8910407008d02c240d00a0700071116803108480e00d003141c1444104030040c5059203103810305205640110380141c43d111440b044840504044d80c03040a418070800002a02e4420032074900406e03900203241c08140f902181c0c0b1201c0689400541d0b054800c00220900095440719030070b0310786141099114914140000e010740f100e801843c5042101d0f50380641c101c80c141003c2d1110f2440c2c0d60291501e52400c3d01c0580300300c10880350500960045112110310341daa504d0050100400717902c800200324801d4040903140014030ba0740106541820010721009659101141084440000d5101d00100f22201d04a0550060320b40c07407042d251000c034011800c5034012943d21841446994100440d03a82c450265644007102106014690040756 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 448226438 1250 448225188 448225231
    0x12050f24040f0602030c0304110307050a0302090c1b0307050d03141603150f060e0f01050910030b060307030e010e211b07080a05060f01150f030b0904050f1005 70
    0x10016a100d4001c075030519280020307860b4403013030b13900803280e0454500e40041008100820855002c0200f007041d0020b090450818010178603072080390201900c0344ca49007001840000100b0f045074162031500c1d4082e008a1801184155690425a4122000e00840c1e43c20075600d4464801c0540c9030414100c1e10116803901140e0041a074900c103e1a410103848030520f004405628a044000740983c040180d1410328002000380486100402c19100381c800305503800c4241e9010b01a1030100314100c42001040c044103200f03600802c801380d59140c1002c004410400002c0c0c060f80900b10741c1344030328000d001c440e1000680c142c482030200d40c04442c8484d60140b00c3c40c0358940030040d0002030515040d00700451121a00186403286035071040156900c6503155404000c014040c40d6041207550b9081302071541000024412100d104030b02a040002100b04280715074881e030400d01503842d004d0030200080c04e050500c1c2c4e0b12084c2d820501c610f188104540300c4c541d51518810a4800c06001015400515011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 448227688 1250 448226438 448226503
    0x501030506121b130e0d1107091a04061401121d030d051b030426040302061c18030503150a0e090d08010f0302010509010315080712050f 60
    0x740c5040c2d0056800814208103000811800001038034000491104555100030440074003031034030400100b14202031085503440740000b41c0f411034051604044560300050f1034828a0108550301161085007031840051851502244044d00650b00303480521038035458401c0c000c0504030500809000469100702406445030940c02024403102c400c03d5002045655607081d880c60704400401c050860f514401c0c04030300100c50f240340d018000307600e00c603d054bc82d10307403039959106840024840010240400c041e1b9049a40710449001e160700902250310b9044501c1e0200900e040c02a04004092920081d00c0c01c02800210303c80d2102e506585030b41c95030390f840c003a20758817203400e40c4c074181c1142034500f01007100c5002c00c8200c5c0c450b08909004200c0440758004c02090200103a0002c008060300c00c4051000d81d070300508a5104003000c0c00e010a0480c030281000f001c0c07808a0340016001d005548010500c409214007070500c10f4002d104503104103540d5070115031034414400d02e050210300c074800701d007403030b9040c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 448228938 1250 448227688 448227691
    0x60f050121050c09121f0b01140304080d06030302010e21040b0f090d050a2d031d04021303030818060609090a05060711160b0313020a0506040801060e15030705010305 73
    0xf1022424110880c010600400025190211a40102c6241260004015281221100d40940c1844500d0700540040e00c51400b00741c0c00850110000000b03014843c101080300c0d101074026908000465490900030700030265803a80c0081406007451440c0c6100340c4520a10003403400b150118a407518044c81840180d101101a1445103001d00c0386a01d240d0750b038544a01114010f00240c0300010317030b034a41841c40d0903001414103100c880c40307550f1810702c0c1100c030070110203684c0c5804e0070340000d0640e140907180c5079036005070140d0080c0000b45c6440115020701400c0c0c00c880c0b02e91640340c6d0945500d4035508202120038812401c0c0d0b1300c601c0000315230b45800f20712a03800c264440c00340c41c0c400d07001d5107919040ca041142d400001c00e03609440c02c1e400344070070006045851018038009040b2400c0c040301c2d00c4c862002800490103603100c0c40c11841990f42e804e05003001041c005015507500d65842103c03901801051203071a021040020000e1282c0190a1050341d0044c4010082c1031014102401500148030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 448230188 1250 448228938 448228951
    0x302070203120406181a030601030b01021e0d1803080d051b0d02041403060603100c2c040b12030306090403030b09070c1401021e07021f03060f05012105 67
    0x20b03085400c2820070848001d00c050020303aa24805001d0410b01c3c210622816940401d10642aa0807241c00c40c80e0740c0c10135660405024a0041030143c8101d004070701d400c000d9201c144096a240050b000d58001c0041c3c1640c03221070580b50b01504d07035142e00c4298140c00c0c840c40302074481d4104001109481070707503520081d48880000c9040301152081e500c802810f80001400c04001a80003600344103241080000e0512004100c000300346070315061020a0700c6044620000f500b06440d401036860340d80c06500f030b003110680f10a005000800f01000c2c19440070b0710107110f6500841c60f040c104000c50070700300320320466140c0d48801140346407111814044d80803001042501010b50314441c0e0b2045564903011a4014503155070740c54044001401c1c84020486103200400b4540c0c810000051072200003294005441c001c241c1c070503241c11950010860019110620000380010004d01d90720700f0303405a21400640c1e40011010350039680310801550310120f182800d4403400d1000100d41c2800e41184c0090f680651b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 448231438 1250 448230188 448230193
    0x3c0302211614012016030e030312160c0b070806010c060c02060703111809041e0c080d0c230c09010803120f01030b040f030504081203011502010605030601060302070203 74
    0x2040c071540d810454090100700e803a94242290032090390310034040c00000b00ca0b002c108240d506801c290410603441181e07120442c410b4468403480605004000c4040d4003031014041da070341c03903102842805060fa000c480d0403e8030500405c0a16826201e000c05410541e44590304412a031a0f81400303071000d02005288a04020154003420005004d5000310b40c500103a907002030989080c1103170090191800400043c1903042d00b031141900e20524114503407002c000a441d0101540c40e035081050380741d41c8d4003480b01051105c1800d1802040782c4038008a0440d0710080c142d4084509c8614211000b034000d0101910007018101d50603064900100711480f88000d032001c0300c005081c03500108402c50426840701ca0903810101e0682d440004031741e1003e40c8014003c101e80c0d650f6041d46e07112110342c0005070000e071038220041e00040c1014000c004803001b40c03401a044803d0503600b4641110b19a100340501001c2e000c5800850460328014042c500940307600901805040c0c0c20b011003100290804078090340c4c180b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 448232688 1250 448231438 448231447
    0x70c0f0c0f0f03060b030a030905060715050c04030309080607050324040c03051005120d0318061401090b040507080c031b0418060b1c02030c073c030221 67
    0x110018004480245100b10409401624508190085800594407607000360025245c400000340e02c10501c2055501c1101d00945580e41e40c100242551078400508440034134007814044100e09202c058030840344681d445480740307500c0350345954403180300f0703180034001c240305001040400543d08480b0109880390300d0302070052048140018203031191500e429001c25900c205008011a00302c80700000f4200548250703480d40c0042c00c6107030b03848074100404000c2658601c1d95107000c1e840111b03070001c003a411450500000f641a0081404800c00f88248521640751020041c61401c0900807244a042180c0710603d040d034403403500300d40d13642c00107002071010b410112190440b08114005440540500e03d4800703460b40b180007007082201d4850b0004942e000e800e02c02a4507480e4030a4150240c1441c5000258481d00d48040d41c44082c0200a40100f02442da1948002070780804448044040680d0740a45045240c50a40d42c1d18915880000b900682020b580c0c48680da02e4001c0e045510344c4810507040c80c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 448233938 1250 448232688 448232699
    0x151b0204112209050c0405010507120306051005030a0c08010311040e030903100b03100e06070c060603020406030807020108010906150503040804030209130606060f0507140708010f1e0203070c0f0c 86
    0x90203075920040707200c50303007072006100329099486005da0044500885c589040e0500001070018040d0308001001200a2800031342c00d90710a4000314003d1a000c3d20002001c090010090501c0d0821038880c045140303061030604e0078030300c00c2200c2412607801440d52090340c0000014032014120645100c4038030301c020002d650303050700c007040041014400e0740c00c002441012032003054200410404010001d508100c0000070503080450416005000341c2045120800c062420001520803580081d501510b005000414000d9240081901038400d90f150405070303880c0c0320640103c030307034502030103442a41113118030b080c0340d0041c4011600640902101e40c03d165803a8000350600800700e030300d50180381e04101d071501081418003d00e0094542424003100d5101440c000030854020002c0103461240554804800309800340031550103441220001d01001307040c021440090003d0040d000000c08031035054013201180c41c401c0e00d0250307c15a079503e2050519403110b400b8004500d01c155075070400751a00144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 448235188 1250 448233938 448233967
    0xa140403020f28080c0f030d05041203180e27031608070510020405090915060126090105060a09150902090a0e070201052401080a020c0f06040c151b020411 68
    0x40000300020260f141d41502400007a43c46c1e008454000da0050003c1401c154002d0309480c19a04925130f404058000c40c10100d451002c400d6000c1204008e84c007011907925440402c003440b441c4002000309100c44d000107a445101c0c5400d0a559041e04240184106220500d400584041c0280400c1d0b0030a41c2c1902d505051028031a9000100740d80050108000d091800b4260790081240024003040042c110300040b00410061805d810130440c41d440c00c14845a804c4071041e69101d009a200035071170540c04541c000c20040d80c401e4456040c80d10300240d48001030061a40883c1c0103266856a1780ca80f42c44080650413072074a9541c0100001c5000c180e0050007603060384580ca40360700205581c28950744540d24141032601d003500c240d41c43c94400c03060340d0704404200c0d080701c9410b00069546404054a9050070f00404452906000707400c140011300809280f0242980d070091030b481780101c0a20400d82d035401c8504081e00b144074050f0012000b6251540c40110641708000003e0729081c403a10201c6d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 448236438 1250 448235188 448235269
    0x170a11070204020f030a0c05030c0d0b01210902010207050d1a0603010e0a0b06041a01050306100e0d0b0a050c0408061f03060f02070b060303091c0c0302090108030a140403020f 77
    0x8404e4a4048204071400e42c050086140d60034450800342e01e5400c0c080c407500024890800031a051945078000c070342d050392264111015440070b0510845403103d103503100714043c6c03841440590052154440c042002e1503c506c030040c14541c44541c15100c803d0003501351070704420085c41550315540e14240302c5503100060040d00000c40c4200c402c80402e14019013044100d41c81000e07440011070700c1c80a0342d510369030040704681d00002d0131101001180c20981e8126000c0d007290307281940140d075410700d141c00c0000000c0440d0003041c3c9138400f884996210543c0d039041f40581d20512040340d100340c000c200e9040045010a12032040c003419126001e0f03d036111007003a59202544000c0e241d50000381e000034480079050321500024200c1c003451810900100291050f0b00c0103c854041459080c3c1d020200f140040c0b042b40210b03406800c40d4180e43c0e4452410751280c210b0084c0c040880c0c201e150b41e59900543d5003c442c10303a0740c0200010ac0b10942d81080c05040b24211030b8800000e200000c680016020044411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 448237688 1250 448236438 448236457
    0xa0803030702060c160b06040e01020d140a090302061308041e0801140c03071805030f0309030f0105100603020a032a0e03031201031209030f120f170a1107020402 71
    0x110303964108000002c0c98900f00910800d000300342400507190040c00d408000417042d4004400025035118400045e0042141c6000c0b030302950720000f00040d0a0f11f82c0d4000c605006840d8060b20550b550f4442074109840d00320f80c0003401a04240006440d0712580440520f100707005c1e20116041c161202810a1850407030501d00802200c900e80030480c0c40401d02503075901c0301806a000e00a41800c81841c589400040c040b60140000d440c046080d1062405d2908000c02c0000d007101d40400007004082e4030790b4020b010780c50081c02000c41c13005030440305004950043c07804180c0741e0364942c03901d04110300a41281c0d00820130035450b11503c80c5510600380c1c4042c0e03012564001e0a080722402c4c80c2c05842c0d48050b240a502076081804400c4802104c0407445044903004051441c080707244540445168050760401001094144401c00c20b015040000d00d000c074055854003140190014400d44403100c6a00000d00340c07250141c0040c111a2140d0003440d0009034511650b030030a60347e9400141031341c1100315035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 448238938 1250 448237688 448237693
    0x321030f190903080103120309030e0909010f060909110d03050a0516050f0f070f050d200d0b1f121b08071206050a0c02070311061b010b0a050103050601050d09050a020a08 75
    0x14002d0003190842203e0741107c80c1800c01219000d42e90240800d501210316903c1880718000207403003e0b000b90855154004022410425140c458032420024043c0c0c4e0020344180f03920410710842c44c18100f243e00b0038590141c0382c80d4100400302508a845903c4070610000c0c100c0500e0642000807810441406ea002c0040044e09881c0b240304003052900c0c100b5408441020f640c55400c200716210340302a1582103411401d1000f9071441c40101c4400c40ba8110700054010a282a1400c280800004114005c031600c244000400042c0300100b200442280140c0315280801c01c030360000602000001c243d0104500080c1c601036584481490401080e80d2141440611100000c020440e81e4400c07140d000b80d10300b4041061843d03540b8000d5a036a95400006c0c1034681701c2503030884603640c1c0401c0d111007031880b4601601000340c419466020301240341c1404d002c1c0c1e030f51000104403903005c0d008441c429107041e55003d04001520021402070044100d0549003402044491f0005d6141d00301000c002d132101800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 448240188 1250 448238938 448238941
    0x80d06150f020c1e010509030f1c0f080c0f0903010e01060b0c0114070c0807061b050702090a2a05090303070c1e030b0411030f0a060b0321030f19090308 67
    0x10041e00340003c0d01c0c6814481ca0794545094800580c4000380a40701c0400e10b0b05503114451840442d243c8061010609541e10410304107051300e007541d426410f070600340c03a0340d014100c0c2c851100031350740e1f54000e4507000c8541c2018411030418480310030162503c4880100080340500700240b806003184c4242d000701d800d40c080020b05c2d0385811401d018224018980420030360062401e000002e000e60400c080081401d4800104941800800e8002c4440440a106201c1c44801240d001412941c8240000c80c041c07400b9500141811256100e0881400b0f850380303400001d1000c10070700c400346560035503000c41802001d11840145031000c0015040e4948500c9140114504003120303e8090351250b0001b02c4002c1c03981d041403001404170000e690700b1a61104020142c43c0070000040d0501c4521440705c2003a00c550000e0500380b141e140c2107038018000990030380e82e10407090207201c28400c05403000d0010304e50041004c542d0303c10f1184003403075204038829201c286a201c0c1181980070799200070800c0e030000f40c0080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 448241438 1250 448240188 448240217
    0x10501030b03060108030d0c090f0b040f060201050f070f05071a040209011a090418080309010c082d060d08030f0103172508041703130504021204080d0615 68
    0x300707070070440c08101d0041c0800e42c58502c0c130a503240b04003404450f80c1e03078071a52001c1c640380c005d840c4000a00307210f41043e000c0c9034942c03201c0d0446800621401c6512018084000b230000c1c01845840d000740e89800842015660700f07541655a01d44d48005442081800c020b40c034041021000c0c2c030344440c4013003202c01e021400c041c010014600c00c103130042540104204075881428104004542c0e0f04507060711b005c6030034024074071954011220749401601e054400003c12240e05e6065006100344805510745080da9100d0a002d83c058071b03070662000c03042030070003041d580e81034034041d80c050340c0401c00400140c8990416554401a60415616540302680460040c402c000e5a10b03005a1485004030030903052603140100c607002090509803c3c031014210f545044140030340002101c02411021300d204800c1c22098000d2a0b90340d00c000b2041c418581d2208003c83d4614060080303a450320325905c50246e054075a42c0350311400364828280055007a603a69800100c5a240004070f02c1e03110046d03215a11b541030009c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 448242688 1250 448241438 448241441
    0xf090203011707051008091005090d0f0f050906031f1707050d020d020607020d02100203040504050105060403030503180c03071410032a0212070b04030f080906010e04020d0c090501050103 82
    0xb50001d070054010700420b009a032a00036003500350909900d040c0101c0e460707807100c082c00c1c05c141c481c0b00d915060a1004118092900080e621030941195a0b0392803013861031802100c2c603070502800000010010008503085103004005150041040540690259000170f4142280b513000d0b4800030980581a000781c11601051190300001e020070f888001881c0c0c00c1c0d0340042c1c07499050f0034009200700c401144500a5446203880004031030380c0900044039040451101940e03d80151041902caa4203100c0042968100745054404882c2c0c5030b00e0b41030540d02e401e01410a00e80c202c02e4460420b1150101c5c0c58240d9808012780002001e6911140e43c51105040034403180c0402080544107050900300b00c0400c035081002e401111090030300c0c040924020f5203004a0410041402c10310324104082440402d1081100e515400786104e40c40342d490071040030f0070503034146104940000c80340e0403410041040d81413000810b50300c540300505441090413a6a61540e0707c1c62140c012116941e0744a006210b6543c26 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 448243938 1250 448242688 448242719
    0x23090f0103240608092b050903150a0b0609090426070b04150506010906081906030b072007062105090c040b0402070837110d031404020d0c0f09020301 66
    0x44d08042e1458600001c08400c08001c1b40040e070360f41010b080c801c210002d1044d8107442e8030000c0202503418149030002c00881400d81652841e200c186000d2044040d854918219000304034080c080610030b54490312101195114402d90f808440300b02661100748005540c01440710b14881c0000e030140e820641002a50040b444400a00d841d14000034000c3d140e8010803400100d41d194608800c455640c3d1000301c0041030301c0740142c03c1c05418240b01204102c00520024442d95455641d103036040c0d10041c103256580001201800c658100714010300c19039101d500000544a140d106102958040800e0901106c40484041e16590001c01d070501c51450703d03015030581c00354125020b42c01d140c029200c0d18404e2054900742029051003052045100b110403e0004070b9502100002d140c00d040a040540715000e025040001c5005015030501c032140079100f003120050b8a40102c0406984540c21b00140c844007040640702081622800a125441c58200b00701604400d040540c4a51429080800d40d502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 448245188 1250 448243938 448243951
    0x1207080103051c050903010612050114400b0a14330d0c29030115020a0212010603050705040e2806020a05030723090f0103240608 57
    0x450800400106100003903800e500d01203030704800d0100c0c0e40803600360303481d00c80c26040036050350804100180c1c0080c0d10414440e4903008a00034001041c1c034616410603584200c4e071440c19010031120b008052811031000203104c2e00e441b8001300310750080283c007800d02d06d4060000ca6030f640d041401c01489820a0003091044400710a540071a802c0c120b0192109050341649c002c0c042d0305010401c030b03d64055403e0a001c1c0580504040c0754400542020300200710709000e0803174200ca11049091462210248442000f101c00001505607420016114110703c511150101140b150540400140c1d460f900204001e00d400c500020745540307545805801d151007940010302c40c2d03140071040d40b200c00c400301d034018003403031050310349100d003c403182110070080701c20103014049920224801c1c4490703800100650280c015500c1c0e000b11160803510a091080c001c80d11203640302814000c6440d2401c0150003240c82d418141400b1074042c490044503d4118141001d10326506103011003000002e07040300950341c00c0007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 448246438 1250 448245188 448245197
    0x30819030c2c09040f03021603110906040f05180705010201140403080702030706050a021c0b01020a030f03020c06090304090c0512010e0c0403050d09060f0e0d140a080309031207 78
    0xc0d12508080c2c5211141181651591488071201026066220b040c10700e96200420340d925a040c035080c96200014000011805442207200b0221003602180c015801c50380e00010350350728080d07040140011010060401a00203072282c4511b040300c80c84c1d00409100e44103014042c540e001d100e1488901d0604c1907030116055900d003e808205e08492440c4059020707405042007000c988540030222324500c1003030009400645840f0510400c2c0d801c1d07400500728180c00a6494480721007410354201140d018191980c05030b40f001d010100003900809680902d000a0305005040088860441c2d061200c00c8440201c1d80e0000641400000f0852080380e0010000b40381003070505654008180c80d0000c180030311003000c40345000244411080108a601a5901c1000c0d11000c000044020f0312221150044a000c5201e451000c6e0850b4880e444050310400024400c9190f8011078940400e8141c1282e40c0282900502c001c0704042640d203001940079401440c021541d030110300ca01080b401d48007502ca0400c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 448247688 1250 448246438 448246451
    0x604052d010911040b06090d080a0e061303061406010203071115070f0209011409070c1b030f170a02030d1d030c0d030e0304030c140f0405090a0302010624051b0703081903 75
    0x9440d8040701c202c001d41d0054841c0e1f0b2b1744101b55004d441824141411a40c4202c00043e8082c108071580148801c4034800c503000e001d2480051081c02203904100c0e92580143d100740b00d0034011484042940f000300c407000c0c1c000849945011300c07642031365001101c1030700d00c0362050140208500f004215940180840c40880010070201c030300083c120000170709800100104401c4c1001404071500030300b4110060024901901542c1303141c0710b00880e40c20f40055030013019a01141c40003080c0c210840d01042d03480e602a514091400846100401103400c54003801080d070050140700190420050109181e014024409646941d400600b5a0b404d03050840740380e0400c0c0720410000d02c4200c03e01d02034503141030f604007007003000c00c0c0400c280550004289512508102c00c0c00003032000410034004150099000380a0303540ca5810000d002500c21209800401ca14081500d041d031103070014100350101d0040030411070000007000d900e4450190015250720000051070b81d119002d0356880350814845084c00e0240c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 448248938 1250 448247688 448247707
    0x14010902040b092202030114040e010504051c0507080417070f0503030f0a050705010c080a0f06050906060a140f09010909090b0601050c10240501020604052d010911040b06 75
    0x290700524007660300541d0300c204a00441c00c020110240c0601d160b94013107451f587e440e5503901d0b140d420000810300403850180c0350b17143c55006001e0540310700d400c0700040286008031085034100d02020040d01c010050207010000c0001c0c200d00042000f0f0000802080c070707541441052034203000c40d561050905c00100300c001c100e96200071096a100145034004c194650080b8081903a4500c180a001800d6502e080c481032070050308041c0c1c06008078012076041044401c1c0d440781ca000c9910501a0329441032040f40003e10a01d070100003458490501c0c6070034000150a150031100d6034000f81e1400b00009070100f03500840d541e009021400509801805105014560b1174003981c480010b80b1050410100003084540300404106141d5002601107080000030818600d0645c00740c1d012541d80b40c0041c0d2460b000945600c0050314a0145030440094408070049e8075200b21103410800c02580c102031844050310440e0401e02c1640c42c100d010300322041080c55081e04000c12103044e010510300c02d681c1405051710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 448250188 1250 448248938 448248959
    0xc030f0105100f080a020c0f151f0302120321040213020703120911130510080705130507090333060b16020f060304080c15040b160905131401090204 65
    0x10183e4541c10581e0303030f5444011004020f44140a40c0107081e205081c041010703079400041801110704c10010841060f100c00c031213001416080e900003e000e400e0034606002500c1c141301185500d01c00c1e1401c8a1521420720400170358030140300d0501400b24240401c200541c14040d001400d8410200d5046161840541c0c0103000c0318081803001c00d90f156a81d035000100700c440c0348024181c0900800100714200080700354005044100c07424051036021001c00101440001900029034400500a5a0382007280e07824000030940140340d601040344000b800000300390b402d411201c2c0c000303070304841c503038030100c440f100300d00d4080480c20448460740351410800000d6010300a44500070030622400c4c03207090090001900d0200700c0b48a841e44010000103000401c1042c90080101340540e6040d01d5208100240400e54160304480107800d41c85484001002821510048143c041480c144116226190404201c8019501d80b94000a0340d581c00c0d85d40c4440348440303204d801030260010a42c40d040c00d01c0301082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 448251438 1250 448250188 448250207
    0x1023402211908040e06030a060e25082e061814090d0c020103060b0c0d0f0c0b04060b13060e1f0302030309040c02071203122405060c01020903060c030f010510 70
    0x500e00c55404001c111b265500348010043c950704030a0901040c94280c1d8003a813680641d41c251042e1401e00e5142000c5441081003003804c8a0480700604070403802418107007541209a44685448101083c081c1142c0b000c9105881c0904058031480c145910803070919000c40d0a10354140c1d15098850003045012440010032001e002e143e0b180ca0000e0503050702c0141c014181c170341c01100e03414002040b4a8142c080005890b00305468035034810b0a1403039044400e0700e10040558014000071500c000080210b4101d81000000040140074122010081c176624000c40e11141c10400c0c522007a481032001d212031030311104418090116482000c145180d002a649114060706a400b8640b21100c007440c040c0240040b8005140d014010242e540692400030420103080000449451610b5203642c0c4015802c0c01c8840c9450843d817046212038100420400550458080390480c0d640070000002540c40900c0800d0080c1d0310800e0954980c01c15079550568510140c2245018071980b01d8003282c02d0f0313805071002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 448252688 1250 448251438 448251449
    0xd0c03080a02030f0714060705030906070503040c0e04030206060a09060e01090525020a05160636060e030f010b0108041506030f05031b0102340221190804 68
    0x3568034800340320142c0c00c60050026007072051402048032414400c2d5a011643d5440d01101500c03525a00c2c07100a41e6a401b00383c0b0220b00d0f0b17910200000340310a02901c001c64001307001d010101c0e9150b981340c2c80500f10b21400c84013240180c100c0e006024143c140340d00f503a8080e00200380280303e01410400c1151507608140710343c0703041c0c6032030780e003c5206090f140040301c0003200e101074106401102d92601955a60920104a0760351180c803040000100d01e421011060358020b58607418a04622480340b0142c1741888031a043c110a0407003030901c074290070f00c03061000300703880e407034072042c9200b05030400d401c0c10781400c61411030745d0404400125580c1e01101c0320340c0c080c1c1d00010500341c5d800d044072158000c0c0140d030001440e0f00e200d44660000c0c4100003000d05401000700f030744c1a6060310600f84080c21b0f80a40c189060001320704100c0d082e082402104400c04520078500001c1c88402180c000a0b42c100c0c0f1600c07034400000811245201b44042480000361090b240559140c102d0380c0d41c1e4844041e8480c500c100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 448253938 1250 448252688 448252703
    0x4060b0a0c1e0b0f011a041203050307140a0903050f01060f0522050f15010f020c01030e0c0d030512091204350c0a1212200a050604110d0c03 62
    0x580414036141c1402e801c00c1da080016803040780f034074122080c04441c0030301070f41250940780c0e00242e501c40351071070845003916135144002c0031484099500f07441030380000d80803100348806002c85100080d10b04000d0551100c0c00c0d60b82c0c010092031410000e00b4010610181d05141e4140b030f0061005070f1401c1403400440e5001e5590b400044601c2c08000c140b51612440c0e00112403c200c1405460740030b403250180514100a850000b0003d000019a400044028a00090303042942900110740c080d0340201c90300d8592a05481c855068040010040300300e05500703c01050000c541003051142c0346c45000c2e84483c105000b440c2040d81e000d00311200340201c0c40f0380c00101c0101c416150101c100c02071400181c100c3d4040c404440310000440d981c5440d000c6280c54051200600c000882141c0e1040b00305c4c0320768102038400c400d0001c4650440312002e5408036070b079001d14840243c0c85400c8013000083c040d507010342d0140c02281031510b410005140600000c4e44220304005140001c6204400990100c07a8072508 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 448255188 1250 448253938 448253963
    0x91d0106180b160308092b03060e0405160b120109020f0403020d060b0301150506030a050a06030c080d0f1e080604180606050a06110712110406031104060b0a0c 70
    0x2480500030712a4012018511002c15404200f8550150ba5494540b20391580081a942c41c0790241e911500301d40241c0c5104040c800c0e5843c0001e100745284031464441c60b0203d40c2d5510f44007400d00c2800d050360102e270b0a82c0310740d4122002c0e195007020100906400e50641c0d190000920715214ac50f00d0600a070140c1c0b0f40d0001d01c20301520044000c48000b1070380a400407620f480d40b81000002489040c81c264025401c280c0800e903155582c01c140020707160b00030542421a180c0122003001002c00a0508482980c0c0b000084003007003444510742d0042013068010318104030321103401007800032110504418803810b0306554828034010301c5000c035250040c2c50501840d0b62020000f4002d00151000c020408041070108800c0c00402d402680a40b00f003600d5044190b5604da4080340c041c0e2115145071110b4104141c04e000207a61031002440079809000314030020422800050300321000d5030710842c0c50300007800f0703135442d142054041c00b00200002d5031480c0c1001080e00c005411206418801003120310020ba = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 448256438 1250 448255188 448255217
    0x7110d08010e2527060c0c06050a0f030e010f0e03190e0603160207170d020c0d0206070b0a090203011a0f0d05060a0f020d090c08070b030103050d0e2707091d0106 71
    0x480011240d00c04d4245030f80d0380d40d49050186c030038080030f6800d456100c0d56a90106060340581d013101c981c2c83c1d0643e108030b0f0380300d48414224014207180c61218459500d881c80c0b074004020703500402500810b058003a55a03941a16691400c4100444814060021192200d01c03a81c0e00e25080d2907000c0f180f4a403810074845542022402c2c226140c00101003108154800801c1036000217001c51340c400190211007540b40b1500411114000d00e2000a5000004201413000206140c102c1d507045518140e01080061440c1d00090940350050607008000c028410018010b180005003102113480644101d4120030341c6407241601ca000c01840102c1d0f0989451519400e03102542c11180c02e1124110304018000c0b0a02c1c0810388050540b140701c0c0540f1444001155218444045034100c039800030092005c41c44204c025240c0c1c804100130f059211500311804449815000d001101b1a41c020041950318500150003030450511a082114500200380694410301c0c1d0b86120541502e000c0d0601039030042241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 448257688 1250 448256438 448256477
    0x315091e0c1914040c300501091a011d060403080304060e16060f0c020d0c051003020702030a021e0a09060509060111060403030507110d08010e25 64
    0x480440a2142032150810304440d0205001c6812035040300c54040000c103880b8060b6403000e850084203003500c21815091030502d016481031002e00c900342440003040c0300025512803024509815401c1544844010700d02441e00c0d4402d0502611007604100100042c140440c1d6945a460194905002d842c8844c050900040c24412a01c00002070500780d446460340f40c036113816081510b0031640d4070704080c015034120380c000c80d04480000520b42c80050891911000711022482c11044205000c4003505410158403868030f0141c1050044c0a50b00c0400e02e8101400b58040500c0c10410405105001d1100142d802040306141c054040340c030105d515900b60023030010080032a02c45540310100130400201940d00c2e07007104040701d500721070241c200d41e616001500e40d800c1c4000c0c540d17941d8206034000340009000e43e0203a50044d68030316001c2040d003a241100380c60070b6400c1c56014041891400100001408490001c1d801100c4021200f402d07581c0310600241c5c4103404c080c000600500d82d208240c81c1002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 448258938 1250 448257688 448257703
    0x904091103070b07020406150507080f0d050a021b0d1b02040e0109050a1b050607060e0705100c0c09060b0406080a0e100c082511030c0a03082202031509 67
    0x701a18010380d0b442104081d2039000c144128005c500f80040040c80a10314014030031070760107585820385040000c0c0e860350343c00d0380007501000001d0020b101810000b5038034411203101ea4239074080140e50742007403114180d0103c801c44402c0c441c0ea0150320881d600651109a0035031010191b2400300b458070507840058090720300d00710710b9120b5618000b210f0003402000644480ca49015100e038603074521f1206c142c0c04001030903018140c2c001104001d41c40000d04e0a81c040750010a1140075580540c9d03d910004024041008000c03001078000c800c03030400c0c440000c0e604002804410710410100b03140a010140f80c0c0a244114030038451140001095211181c2044110039008800d650346040d460741395000419038090100e0004500200040080c05c0000070703010401c0209070340c20301041c1020012908100502200c0f206c6010078019000b11032010410354103101d1298440f2040b5150903150007105000c01623800b00381c28a010194005a10003081541c80380c89819280815613032100c243c903103031211 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 448260188 1250 448258938 448258973
    0x230f190905100509070813141c0206010f090b1f0504090f020316082707030c1d10030c15091205010b0111010e060612070b030108100c030e03090409 65
    0x41400b0451208a000795030030544004075150b00190310717045412100010b0407240507000d20fa6201c4aa000304903100c0c81241c030400c015080328141d4403103186201c1100ca02d03002d0f20006d64021170050003201141070612006c2c0c1050395080203002d070f05070001183c8120700684c0a0208000f0f841400306c2074070450446014164142092010b5130038888450001d60085075440032814107601c103c48100d20540c403190194004981c04c1440c201030303140f601c1c41540c04031407072002c5100301500040001d5983c0d42c004024107100c500020b1314052560586c404010082804c003010050070b07010301c00520b90380038800940d4100103031900e40482c0c0060039107034001c46400c03da09180c0c420b0720020420205410000403000c080c1d80f9403109402e80401d40382a03841c00c812034040d54000705c000500b82e040150b050344110a40808403142c16941d1000e03d4820741c004c2c0c0161404e60044000080d0844007401a801341180a140400c1764600d162903864a0780140568244601c0d1900798940c20701101a5240c989044c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 448261438 1250 448260188 448260191
    0x100312020145060e03031305070909020f0f010e0d060b03280803060609120c1e06070204110f12090607020319110708102f0307080925230f1909 63
    0x108400041f01da100078800845035882054004603401c406802410300140c0e028241d440406004010070080031841c091080c100050b03180641c0150b91100e044004260268000254103d40703801410b06051903010b410300351074100000c0c01d00784c00d849400034001d1031700031040c9502c9881c2d0100041c442c3c811402220346c000340b800c4a4545840001c5030b041c04d4a80210703035044840a52590818450040810043c1d22071000c0c000b40e00541401d82101100c3c2500f0300341149002e04418042941d900700038001340c40e4003912410060221410022070b608440c2900045050800e086481c3c1007503003408100744c082180b41500c0c03400c180c1c010401c2c0406001c01c1030989002d05c3c820189103006007500001540c0c43d840103151000c1d103c2d028000c2c1d489a072017580c44546142e56554058464040c00f070001e8131548a41a100944100000c900c1c060614040c0089401e4601c2c3c00642c0310080b400d0803c400018492111003452a40c442c04104104007094a441e100306501c00d02e0100021215445404541e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 448262688 1250 448261438 448261441
    0x60904031803140d0c050d030e03041a120a15060e010210060b190914010819050405070312180e070c0b01080c01200601060503100312020145060e0303 66
    0x2c005080003507110702001c41280c8039002d441344103c1382400c000300302400c01d400040b060326030184260071441c0d001802c1c00850b8a02540c03500020365003807030f81140d80c09594001c02e90101c000c07000c140307032500458850f10520a610001102001c140c5641c0304220601c89001c40002e4107034000e0050720784016618908101031641d40380181d046030311802c0c1240d03541103008010110580102d180e030b0207072004c441031088020604001500e400e00c01a10b040010004420f1100311a000350140f94801c0d4890009001d0484c65450041c05c0c007881d1504560038001c1c03202c0c1e500c51000400d00d501c41120401c0c0c031a042c040e280d40d842a1012040324401410f6902a00000b003100080016200c4140b50203070784200745014010092401208124485020f94014800402c05a40304034081c40c0c1000c03040c050841010f0f41c1e43d990601200b03000c92146c0140c2d4440c1000d501d001c2c006074000d6030300615604800440c1054942020704012003000e000030081525841c1d1081c0002c650102c01c0508419045950701d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 448263938 1250 448262688 448262693
    0x4020d06090e0c031c020601031b0f0303021b0d020d0b2d16030501030b07030c051204230f120d0b0d0f12170a0c230705010e0c030303060904031803 65
    0x3520780c1e00c0100c5020388542054a01c070180c507940310028800e0705d580a0102a400c55944001c1003070b20a5003c4140342c00b81c5004030742d41c000302803540000c1d846070300140b180c85186800841c0c245c9040d0b02c041d2052044610510150700c0300341105003065400012804246ea510100c040850100141000c003241028030011440601000740782c00b45114074083d816501080e1011005d60fa001d00008000400031404201240d000e90041ea00080b040e0518074200b82c0703552560203640700201c13801c0e242810055900049a002d2194030180006a54090030440c005285081da031100d80325404080c1032800031341c00010f08040c0c1e200c038041000040409840301c0060820341a1041c020009407513569460302c6141c1520b00581003180110041c249002d2569030701c078900c10040c1910072071501806050480f8262250415811440110380e001c943c1d0b40750755090810b01d0849540400315080d0750300244500509940000c01d4990281c800c48000080c1e65851500300c0c0d100f40340310030250f11441c91308008402c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 448265188 1250 448263938 448263943
    0x9060306180809010807050d02070c0e090a120f120203010e04170901020718020706060e0702070e010f0b0306030a0f21080f012303060c0703140403030e04020d06090e 73
    0x45a00400c010310107140700040005041080490003804114108098005540101c4900e50711010500344141403841d00058a07099920101080710024460302c0240310200c216800c164003d45480020b14020959580b09580b04c1483c1d10210107000d800d0308401c3c9024450118180078801c06942551030796503404141043c0c1c00c0560b4120f50180c851007a071880c0c000640103588401405900422003036203804410f15121301014070100d0100d408210180c0820f03403034028040240801104c1e11045d25040c000241000d40c5a08801d08094101e1300402030000a000340400b540c0801200d5650b07a16544d0009140140c00385008100e0380c0d0600b05002032000c0ca4072504140d05804415a12501100104a9040008598203070701c400c41d920040c400c82c10f8030105416034284044002e01401d10010000b031401400b124000a9988005040c104144c0e0208510300c8404100c40060308003401c50754090240755050440c0c500581d0701048030000c40c0c400790048030040000c950108484000d4140654 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 448266438 1250 448265188 448265201
    0x4050d080a141207030504140a030c050c0301020a0e040f0e1006180501060c111201060b1b06070504170c0603040609020f090903090d05070b030903040f090606170a090b0109 76
    0x300400d800700e02d5403120300712010890780f4110b5040c550f01c409507a00784003039006080c01b40042daa41390001858010049081080480b428029141d8400241c113620b01070740340c1000802840e001c2e074018414403e4940d000302d026103026204560104003840205513440040c10700c0c40070511b051007004041c1c038419070700e5400300c1305032030148441c22b180791164941c000c1034410070300c16003000864906d43e54020481c0c8c0c1110110305100140340025007c49800c0050a40b0000c1c0c02610301d4050020b441003d003190840c401c07a08d8a02c05010340745034078003501c01402c035001d14801c880203036880780220368003408244103000c880c240003410180c82c1d0500c2e0410400400f50004200e004022801140081b8a06040d0062141d4000d45c015031410494400f80200c101c24420100c407984144c038004602060114091482904000e004549030352410599644604c0154000c401c220300e441410300c18554028181110402010402c9500340c44800701d9600524141c440544081d22100011858085a4003c1c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 448267688 1250 448266438 448266457
    0x5071e0203010c21090b07051309050a0b031e06040b09030706020a03050103051b032e060e19090b0408210403180806010e040f030c0503030c0d0507181a04050d08 71
    0xa0130340c2181a9080c5045451000020703000b41070b4080017030325840c03180004003c240600c048050740c0d240d80d83c5a182c05daa0080e42c0204007961164059051070504000b80d1040c102a40102004a005009210348612000d00b000d84040304a0f40081c82e8014100101c444240d4085011562030054a100800601c0280002c40385401203503040c0a0f0300405005000c440c6c035005024110090407a04104540f001c1c0c1101c1641c0704000d003203120b00311119031203800001c040c508803904203072902807176420b1400c24600d0f2049400385080340050129050160b40c07a0f105502ca4841a920307080c5401480c05006074a2510b190040c0c1c03075040108141c3c3c40b1031907440103041000e8404004d80c0756441d054a4402c01d004d1803141c00390340000140468541c071000d142c01c9000e4108001c0007101500c80c135055a00c111482d40108900040c4150800101e12840d80d02c855980b42040c10301d500b00b0484030320143c4a00c1004066014411214055807511040703900400c001031490260744682d1501c00f40b25000f20882 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 448268938 1250 448267688 448267727
    0x6050a020f0a061a09190e19151d06040609022803030207080309030a02130b031911010f02060a050405011b081009050103030f03090c1703090301110a05071e0203010c 73
    0x400d1400d04001807454010103100c0c20058411b10550084001041200006001c0d4426003610001906c01e2424802c0c0c1d850280c92001184070707204840d10151206007114000140803074030084221a008078200e504580e0100f40800d64134940d000041d5071403440a42c21307140c0f4440e00c6a4100c00927004201604a074841d8089d1040b01b640c40b032070301352203014040c400794041e00003865a4006240402118801184060001401b14444404203151008103600b480075840c01c91000d2040c4020640b082e50340c08400d00e88450000c00348031000351140c01c003611443c1000d84032001315040010a400c41c1030701180b01d5482e0640c000e1003c10040170350400791203101d4038002c20040462280c80e5402080d05132a09074480c09243e80000e0000c8006000c9228140c1d502900b640d00442c0041d41c400f110015000503c0055403500402c20401d82101c2031880c00c03405010040069181003604482a0340f8035641007110740200880003140b200f042040b0ba03030001d516519000c40002c807690000304100724520312140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 448270188 1250 448268938 448268981
    0x90d120201090b060a050f062107020f01060b071a181b1305010b19050c0610060f020c09060d0c090c02060f360102090d050601090c08010f06050a020f0a06 68
    0x6000405d011790040b6504020298000324440c00e1090042c28881036503500b0009141482d0b4552445010503aa02c03401604a107040320784600c07003400380d00c01811800340883d203400a20390300c480080d03a50744039000024440400251002500040c0d442e0a6441181600e04186500f030ba14290851041034982c864001d480e5000c4807a04a44680b134140c0341540e8441d40380c01d928034581c50f41da10b548646402004000c10184c02501401d100a90080d004a0a07440000e4185140900075103230f41000d41045600040e801a130341d554070312000b0340101c800e842c1c03a05075440728202542d08611075000740340814204003144c07032003640c00924188502c0c00d05c0284101350320f490385004480b5000c8503070740108203c400c1071554140c0c1032082092501038100c00041c500340b2000082022800e03e201c0569694000304010003050b510f6000d08544009145004541ca42c1410480310707040d9010301411017008400300b811b01d00d43c0d0013002070018480014003100c46074021841d1100160015108903050044580c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 448271438 1250 448270188 448270201
    0xf081308010204150324081e0102031005011103130b0702030105090a05060a0f14072a0213090602070206070507030c1a090103050603100603140d020307030f05090d120201090b 77
    0x709a5044d03d4031410070401c100d5030a0740c100d000e0914000d1000c542500b04200c42407400103403003038100400c17040010381a001c440345d40c103141860041c3c3e004130169004008104600c8030341c03180d0130300f6a03109081000c541c091004240d03245004040159410030b40c401d60210b0761101160203000c9c0039108030001d00041d034540100d207446800c4902c1c0200164080d00206010010f241c000c030807990070b010000100b1158828007801800400d0354000c0104400c441010407400b00e50b48071160001c142c11900261621076404214a1150103003100302c81561103458404001094046a0040b900200400e4032680c05085c8681c4030a003520003142c0d07001034807000041c00340e402d0a11900e1503044103092800c04c0c0c040341c019405004010507180c0d05015001c0030181b2030b1524824036001d103014043e1482c1110040a10510b4400c04240082c195030043c484a800603500800415048001d468250b03100e41070340000c5500f40740740ba003004014102e0031004101c143d505500201006020701c20501d510b44810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 448272688 1250 448271438 448271441
    0x10b030a05071701140c070c0e0c070f080c2a010806010507060c0908031c060b16080a18061106070905130209060c1006080f07060e13090f08130801 65
    0x2103001001504030303420070000c1454030f101ca4800001544008502080c40c0304100b0381c0164112645010648042080818800b060701e0210103440ca8801400d102d00f0700340000e600a0091210060152440c500b017441040440000d840b801c5404504507032071552040c42d00c2c10348a0700e075558528042d4618802c4042da42c400c0c114940180c80684402d460618292a03103000f40c1403589810041c40908800001c0c0890100006c02c000500c02d05403005507110300780c0080032f4848039484001c508000707121412600005070b0010300c071035500100781c42d55120a01c0040d41c08a580075140100040c009000003200381e0400044d05034071500405441c030795a07885130240c0381c0801034003800d030700903d110b4001021003d640d402814001030040109007483c0e51001c42d0361804003031040030140c00f51640d408011498003003001003003081d4864094a50281805030007080b10445440244c1301e9424444048103d01141d84001071564111000c100070650f10b0903c0603940c0d00403113268041204441d400140b81c0c406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 448273938 1250 448272688 448272703
    0x21040e0c0a1107060c0f02040b0a0b0921060604090c0b0c0106260d050a090915060f020a030c0308040c05042906361309050c04051302010807020102040b0c010b03010b03 74
    0x19107406850705c0700da032683d18140c0103840c4100e070401c0e0740b82c0f1890503580c0c41c40c440c1c1780100717220b0340800d99485200e010301440c0741c61110b110480c100b080030305212015020550581c8030380155400036007030703050342014054004180c1c0001d118820029070800080010340000c81600c10051004070703001c0035004011488400c0f8aa01d0403c2c0e000300010010703562041000f8029040c1502c0d00340040b544401040c41142c0364220000c1c09100c04140c1088999001104001d8040040c0050002034a150320081c1115915074001020049420005410001850481c1c070181074041c0c0104810000501c1044210048810400503090403084d2f6a48030b1410404603120020218003054621001c040e071504800703050081e28a1b03541007503c840700c05803508481040752848a19000c900720314182042820038440740c01081c0910b00740810400c186240a40c202003d035428030f04110141e4460a04070300a020b0794114044003680040c0d801c0010f101500024100a402c03002040203000c1c150806944694 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 448275188 1250 448273938 448273949
    0x71e080a0e0f061b0106092c060705030c160b0903030a0e0303161103071b0609090b06030712090507060c0201110706080601051b01050c180906010221040e0c0a1107 72
    0x10130880040f4900c620801c0400b071415000011811940b02c14022040d2083c80003001c44014510445c060205040c40c00030000c15640c402800d02c0b400c00b40401081480b009007442925440010744192100c808550949126000101c01001d0304000c0e00003604d0303038010303156000741c1400c11509101900021084030700070842410f010110301c04110003034804590003950100d140c0401e2040c0300200707410440c56481001c0503040c006009042070390140c0002066005080300a02d0300b080300c2d0050700c6140c110b9400c0443d45c200701c51001c249007001d1000e0308003180c0c002c025011b107020006906070400c0540020a00c01d8844843d56400340f0b00c0c0f07640d20541841203100145418000c51065401b0741d0040c09494164000d00d03100c1034601840c03a0a544003a10050682c0702d0020f88400d5000200c0502e040090049883c4117407410407100003503603500712402c10300c103900b0700c0f403000101d001c00d43c1d08071001841542c402a072103152900d00c2a09030340242d04800080380c10464032031800803010840005035007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 448276438 1250 448275188 448275199
    0x601080702061609081903090e15062b02040807050f091f080f061014090f060d020a09050703050c070c0605030406020d020d061502070e010308071e080a0e0f 69
    0x3600d001c00c9180348100643c084081c001654000b10b41c240007404881d0301100c44245202d040b6400d8500104040010351105c0d070500494401d01108510510400c0c94080045810380e481c0d000303400a1005854210500110000f415040401400115000703042201c000c0419106099070ba081803262002110803680e5000700e643c0000b6003858240c0d456401d60200074107880300031580b01e48904d0300c0c0c04841a01e25103258031800030402c100010050140280602c0c4801e0981c038072202d004689100b00142850309404100000201c0c1d94607611052a05560020051706c04c2076a01c8280c1e800a0a0644501d40000d0030f150026110000310300440e100580e000b50411211440c0c2203041710301c0d410203441260f0082e02003000140d1510030740003400c0100031008000560610301000c0201e41a40500c0400035504001010061010843d824604481d04030380c1c00c0d0742c0e505083c6031104a0200211b000c404104142e42d50b60280448800a13016181d50f58030f03508114441d00c010000780c040300d000b000307a100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 448277688 1250 448276438 448276441
    0x1060e0a050d05150a0b1c020d1410020d0b1908060a05060d1208070e120309010c0c030203060906011802071203020a020c03071215020c0c0607051221060108070206 72
    0xd041044903150b4080c00b0704181ca540f003166021402221301c040d078640d14016202c5000d8849454404440e0403180250224461301d02c0a95000c5050b128101074080c008801c2491030b660301d00d800340169810814207400455964400e140c1c494014582c640d1158080d80200d4000e84a0f12081001402903401003002001c040e034624040740c02a1400030306190308503000148050000ba9640c1c3c49174000301c642e4071407181a15000b1801421481d030041c07520b2049418542c0070384d940070040100d03102ca1030f00380707407040030780348907051003600c0e040c0e264002501442007104100e5aa200824110b0503902c9450606030b410408402c200b00364010b4010142c0402c3c503001c54469028000c0d80180b04046090043c1e84101c140003000a040c4156a440200c010808101c41010840811b00c0011065081e1b0001c50400d858031070001d0741e98120050150180500140042c2030000800400e1100200502210340d140c03444014619a4400c0e124443e4580001d0780204443d0740c02a00040e1081c503003a40241103071f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 448278938 1250 448277688 448277699
    0x6020a050c1e0d08090406121e0b0105010c0809030a0c1505070b0a020307180306020a020f01020304260f040603060f05061219020409061212020d05040510110d030b0901060e0a 77
    0x342440d0040b140d501c030400c00c042e03075510f860041c0c1c4000c0680f0401c0102409507414480c0002003000b00c01c02381c0b1000802160300054190720112f055480c02e1902d01c402c070026241c8030000d0311607180000d61510480340382d05e080011010403601507071800c01008409400000050f0380074000e0034801000780d8270050001d43c151055502559100041e0700e0305894018003c0c62100c0781000541050750920f800061100005404010b202041c00d14500214551f161075100d001c40d2200c0c0c4010501103095041110320360314900016940031100180b20f03240c0e0b0740d580314005002070078203110709900340f001354800040c2403034500251140400120b510040d07903a0360010f070280c1e580000c2600d00b0380d81d07424440030801300094400c42d0003400320100b0071581d6080354201904102ca20000c1c4e40e04550180000c102800e40c810180c500701d030010344148400c3c01d00c0c11002e90f005148400085100d07c101d48000c00040e40c550085011124103540d0341c03990380d03201c000131101171b10019505504109040000c121 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 448280188 1250 448278938 448278949
    0x60406081609051f1404080601090504030314180d050f030f19020a02100b0405011802070201020c10080f0a110a0e031c050d0f090f080d0e0706020a050c1e 68
    0x24001810b20b0005002600c03040090014a54004840780c03203100c54a02140300c54200c45081c0c203024811108606207451301030160765404050003544080b54803000072404043c06900030048a54801d1440441480c1405468000041c5420074808074451200d0b000308442c02101259043c805103200c1600c1c6548840d034042c000716001d800d0103140341481d084035244070464405003580040982c040e00280d1440060803064030031141a80788038504d802c0040001d48000010032110024803180981c44d0b482500060341000c0c4410941c6810641212100e080540e01c81c21707151090000000c0a0803984840d402c110440c0c080d80044102802c003000308100450083d04624a4000000e00f1a00e40c61240c8500300b102601004090b00860404140321211500900510141c0e50504000b0041021140c440c2c0001d1040d0040141048800140031001d100007030308070600c5121020f040b40d034210303510b080003543c841374903605a81e07501a0080c42c0e100d03440e00190100111020200c0442085800010090b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 448281438 1250 448280188 448280221
    0x30106030911030d021f06060503060907090302040204090c110f0d0c020a03050d050c071208070818120f160506040e071101050403020d09080c0d0b1305010906051506040608 76
    0x1540700e607012480c0d500b240c0d03042221000e003120543c0a4405051900c4078428010395860100d82c0c02818078105000301c80e48501aa507101600b02c8041c44252160b080945880071a600040c0d005400001c0100e420f40813034010700f0701600280c1d00d040403401d810090580300c200d4401800704c00d80001d1410a045481145004880e6000a00d080d5686540f55216890038a600c40000045540401e071140480014480003005080448400b0011140380d42c03a0645807040d40c0000301295400700d104080306000389010b0500c020064040084844501610341e030384d0341240d19801c181d2055035502600c00891034040e908890009d011541001c0c100b03181c00c5c0c41c00000030840c00030040e01018203044d04400340185c2e4000c0d40a5005071001c4242003000410f03801e0182c01c8000503920081101403503458003e008903445401000b100f1143d00c59507001c8640d2a94208003500030742c00d1a2400d030600001d54040b40c010110560340d49070011110742404458000e07881a1030105641e14002004540d0003c0010b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 448282688 1250 448281438 448281443
    0x50907060e03120c0609060c0406020d030c0507050f010504020a0506041404020306010e0312030108071a0d09081905041e0e19090c030f0c0b090a03171605060405060a050c0301060309 80
    0x1183c81502207035002003250400b40c5220041d0f0300c10414400600810700046800c035000410491a040c189117004c0e5461503d04801c80405540303e0f1040c4c00180303d41d00703030785c0000c0e44023080e241000041035015018102c1660160700c14880c0800c0002d2915040040390308452106a0b403180010b02101040001e40000342541c1c184030000031140e80ea590103001d4900e400c1200c031545510703035044c25203031842e00031300b508075902c4910100120380828a50b803069841c3c9580902000c54840c0c603520b0038021380d0281c40500c00340ca007008090314015540101c09001507440005001030002407003181c241d90604644107640d40300d141c4101150306210f402186810304041e035940402c0c3c962081e510720b640000141d0040e04c126041145840030001500c0451000b40101181c2c5030501040c100018078840907403100400102c1014041d03081c903102403080e2103070f030000d107110001c0329041802c0154954a00b19811500d41c0544000620500d00d503100c1e40380074402c0c07203200c9030441c0c0c00c01006400501e41e24809 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 448283938 1250 448282688 448282693
    0x100c0905031002090a0f0b030106030c030501060903082b0f0b03010b010e013c0e0d05060a1d0a03051e1c0b041407121103040b07031e02040f0315050907060e03 70
    0xc0740700016101b04030f0041c44110b640139900c0d8906031000b0b0803109220296410141014010001241d00c940540c00340c0390800d9203240d941e4061801c080288109810142903906d0000c841f04011a081c1c0c0404a034680d201024003907403088100301400c07940c5401819003c10321903c40070015511440c110501071403000000340c95480b041c03c044000281c0c00c02c0203a42d00d00d007081044031880d80041040080c407001e440c4007040b800365684140d00c801005101c800942e9403101c060f44440645440100050160020388000395014200248030743d005c0b500b01204050801c50048070b410000d4100e5071401506080d89034000b44210b50200030303100b00c00c00c00d0f40c000d0b21f8003402000b14904000d003500444841e00d600c03c201c182c40c50080c0944d16010320030138101038103100700008074290380d80d9541d0007000b40c0b0300003032040f40c81079400c0c00402d01b0300182e000c490b2021034041000741d402480f00081d00e00800d101a900b058443c4068140ca034102c510040e08d400400041080e0750042c0c3e4121705400d0001d06 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 448285188 1250 448283938 448283959
    0x1230a0504030602070c1701090308011a041d16050c0c0f0a0b18130b010c02091f0b0d0605060702060d090224040306110310060c0f0b0702100c090503100209 69
    0x55901c11380c0c000d40c805070f4168050316810400c06404800107030300002d11034000c0c0318030110b58a001c1c214000500c01c0100c4106441002540200d1400484001e008409188100070300000741147e14010105c1e0103610041d440e0804608207805002034070452072142008001c4000e40f0014000c0a01c54484526001540900007258281003407020b001c00ea0041405190740d601d49004101d00b282c00728401480c02841c2c01c401003000e0768403c03000c03c095501aa1844003a869200c100b0314581140d2600303100600c44040d0210b2102080303c0106052055001c090000c1074544c000c02c031280c820080c00130750081d41003291200303102e5290480081540028442c0c00c1280d094005c00d0310340003543c00e16611420001405104000071440b45143c0307070350104840e40c114900b110000d410749032640510b05c14071070300d500043c042000c0580703401c0c0c0344c07944041d40380c07820b00b09500060b5440c440c0c1406440c00d282441ca0701c0400622440c010340480304c00400030501404840000e000951080b2403d5400100054 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 448286438 1250 448285188 448285193
    0xc06150103150e06011e0f03150b030c0c060105030721150e0106061106040b040b04170d050106030c140a030e0c03071d0a0908070206090f0a090b010e01230a050403 72
    0x5600003c2100e68000c200d2071038440f00040c180250074203040601d40f402d41c0c0000215601032440803d03800c250600003000c1b202c000d42005000e21644c00b040c2000310010800c01c814442002400080e8086801c650142c0d07200d6082503150710460040c5e0102d061014601010b042003800d85442072805a8141d060104030490f034903041d10104181e820150307454200411406612000c1040c240101101078025418650764031251041c000e4405465180c0790303404207041c0328040c503c00070a1041461074507510b0030501c01581c081c140911940d03020070302c0c0a00e40349556028000907203c000428401c01e1800700317800e13416002010240c03110045807040d00f02d50300542c3c0382001400050040480040105013003559034404031000106a42061420110b401002138101c2d0161100258125005619800c1c80c40118005115280096034016a403420004e000c4101c0da0254100705400c0c2d80d1180c0b00b0a100005603850145031005012807894080c010001140c2c60340905203075080d03440d016142c643e8a8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 448287688 1250 448286438 448286471
    0x70e1503070f050c0d051b0106030b0a0e060f07051303050609030c010b03070602030a1416060504140307050325020a08030d05010911031506090a030f170c06150103 72
    0x116010011240003060000c125000145806148241d2410314a880021040d40e6100c884041c150300600c030000c1070507071114100c41c0c0485030f600007490080104039501c0c2081d0405403001d8944580c0a0b142c03002c1013411a6009c900544540c80d43d0407095091703190028101c50507440390000b02807800d200500807000074418484603000f02440d000444d2141c41c0f81d01380c40d0845009104241c844c1d0300848003004001d4011007603c200300c0d01c49c14180f128510030042d00c60385114404640901700740101544d010030120350f0007a4080c0d40214102da101400070311038030755644102c05010740541e105000a1030400e2058500c00c241012513148080340c09010340c089080d0708025046610035420100720440c0b992514480c813401001c80900a100211014114a145120180c0369014103100c81e85180c40030b80310101111540000502004011a0f60b41031a4211801d440400c5981d021415820810300000f042a9101d80c45810050300840d19180034100d0003140e030250384d41c14540c03101400c070340c0180d04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 448288938 1250 448287688 448287709
    0x10605120c0f010306080703080f0d09051e01200d020c010507020604060c090302150904090c0b0a2721050105070c0201080703111c020c03040b090a0e0402010512070e 73
    0x6100070700d03012000008010800d202c0101c0e140c1054600102007003a00e00000e41c0c00b0840303811024255994801840c915150302c00d150340c0304030f2035040200c01810407600045200220003508801d42848000b82d01447c2a9211111800d85030030303401a08281543c8410010040e0511000f0010310b041104900c040c251141140d114005d0b07049881008184690f9019180000c041c0f480c1500016007158001614003041150102482c034021441d43c1c4292259032024203122f0f00400074040e81551164401d14543c8480c807140001840c454030954501001041164140c000090149141c0d040c00c6091404112a01d088480c0040145003040400d100303100c3c1501800d01c660725244c2d0700216000142c82d100d4040d102c00105481d100000707a0401d004c20a40780b400e040c6440924208000b400c001e0082d004101a140060100180000340310000c2d000415103202c00b035501e6801e607641c0f80c0a010b00b90341c0450b0041e01103901003003044120600314000c2d40c1e2210150a02c181280070140100700041c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 448290188 1250 448288938 448288969
    0x81603060f03030c0210050c120702122a0306061c02010216090c0e0904050d0318050303010e2d0115050706020c0c010219030e0f060417010204090c090806060909010605 74
    0x1e003211300700c10350505e1703003880000b60100e003041890310004107819541d07030070ba50740700c5030079100d010030490115070350f006c0e980e2082c105000451fa0343c5d20800c080d9101e8141c64100181c2021034100c83ca0303600741000710718144176401c010301c0400a0042c0c51081400120001402c0341103020b4019890300c41e11101e4099006044540e10009040b801840e0191403805c021506904c40c01d80c840401c00041c0001070045181c400a150110b10900003001c1c20120582c900300060481c00044004a003400f02111440e10030b80002d61040c1c501e00a40c50502d060b0400320781030041c152003d40040c050759000327400b00c8810034003a2400b2860a0710f1500c9080490304400150102c0b40c2012010f4a107960f410400c8070340e00d0303258400c5540440c0d40390758041d045141008519006885082012520303958000640e002000a1561034003000500c40c4810300035070090040032101407801d1454030040e03100d02c4014040d2a2080d00601050302e407135080044407a402000c0803082d648904000c5081d071a48089000b8444 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 448291438 1250 448290188 448290197
    0x30b060307050c07060e09180f0d052805030c0a090506070b060f011404120f080a0f0f1d1e1306090f02120115020a0f141c081603060f0303 61
    0xd5224070f1060a080b1264040030400c10f00720310038100d594079001625080f00d01802e5a28048588034103060606c600000c000c01d05000340132100410039041001003200070543c00404540c4060500214080b04022074507000103982400000d030101e5402c0000c0c01041c0c0c0c14140090034907500d50003d002903011070303803c40c1c05102c5c890521855040c1410407000a0342d003401d1810008040d4681e55481e40294440d00c202d401c1c1e0181b45d0014004215002450a500521403075520305104102030074806800c07031004d000070464290300c4045482010360010541e135122303545020499440401100340001d846c010310410b0345981c00945995243c0004030690403a6501264191034107203e8011100000440031519004103c00b00e10016000041c0341540c5100080f5948142e550100f01d16081483e02e00802412001c1c0f4010180410040c1c01401905020304542d07504c10304206c110b600b4030b181c00d16071000c104a00d01013104503040503081c903a0803d5510b030005440759144803012410103564419400709 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 448292688 1250 448291438 448291447
    0x7140c0d1218080d030b06041205060907210209180109030e0307050a0f09051003051614120a0b0601020a050102130501091208220302030a060e07060e0d12030b06030705 74
    0x49400c00e40518200003007482c955102841c00700c40ca03803078103a40340c1841c00301903480c0b4214030955100803d1750094050054004001013181ca0703c43c2c2c0e80c45054500d80c195100c1d420000813a0745403070034203003000c2d00c450130f000c52580c0c4c4030740c24030916400c05000c80c81d590080007500b00c08060248903107100c440c06681c64072042c1204109160410007160441d41c080c0707803280070070710010030000003000c100d54207035500190307581c0c03084907010610030260030040032402104424801a460510200243c0701060300512094201c0e00030420300740c61203040341c0280d400044000c40030500094041c0d41c06103040c0195284a203256544a08a0380300180c0210211981c2e001801a56030155180025140c107912070034000300e45848040ca9030050340307410141d1081e03028011418090a599000c020743e4050101c40c20608a85000ba000e081800003059031403080f1500095014460b0b080c0c012262809040015101626181c1c0952088100315082c14140c941485803c5511914000c501c1606c0fa650786075103c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 448293938 1250 448292688 448292723
    0x302060712080705090a0312021603050105040b0105120a020114090a03140706210504060f0227030d0e0114091c0b0f010f0b360901080106080307140c0d 67
    0x68810142c00441000340a100d51917558860101c01d505503900599603950340050410101e1800d1714002410400041c0b10200000300181500300502440c400d807401b8403960380390f10a00600d040800c000300c525901401030301c8055401601042c10f03201b0404000c920b8500c43c50f010410001480c2c1c811281c600071401d02c0508101d049c41144098042e41c50400300c0c0c41d01a8407512140d00d0100d0740e26240503501c5010030708101c65a03121504004040c0001c3d901c51840c1d980034001e400480c0520504910300c0d048080191030301248055501e400d0b40c0f5280350ba00d01100044521204000300718480050401880751f4503078038142c0c0c2200f400c945907100c034080c0310b8a181500c07010341d0117018600d40c001850010700c200c15004a00406a50034081c400c0d44a000d09840c88000034070340c0704460400d108160b000e004001140e00c00115a10341035841003016660350045070b0072a07100f0320820306280c03c14000b0100003000c08403071400e075101c1d0318112014100c411000400f2802044403c4400781c10031400c1000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 448295188 1250 448293938 448293947
    0xc0f0c0f02090c310510050c010c092d061b06110301081204030209061012060807060306080714120708190b0114090a0509031c0207021513030b0c040302060712 70
    0x4a40302821440701030441c0584c03030110041e0f00566200c0e40300036648050603131280081c0c4400c110000000c0c0007910144034017400c102458098089104030070141c5600420510706d0141440b681c1d85141d00c4a80c0c034102c0211020514070004070203102060780ca810215a0741d01440781c0f0030300424033841e030f030707515000f44140f4011070700c00041b078036000902041000d60388503104d20b688000240e40b0a0118030104504551030919504c0a54407e4070700b620120f590280040d04030143c8100352003c01c00c0d191260442550f0700c2a521810544110490359240300382000c40389010030842c103008658446417140c0c266402d00d001140c2c0400303010918502d0f0818046141039142c01840107080d0070490305143d4012840c4e110f002803003096029107600118101240c200112459424080d2116001820007220348019520000d8164410b02041001160300404442150025007400b1620f8158038074641d902550414010001d1980450620002015845901c010041140b0410140c99448034200c809071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 448296438 1250 448295188 448295227
    0xb060a03230c0910030b041110020105010810020f0405040905010612060b01030605150a03320f0106080702100902030a0c06030509060c180409020301091a010807090c0f0c0f02090c 79
    0x40c49000010244000700d8078000c0904c0649070014080410f995130750601c80d40d882461031240307401c900c41084001c00158103500ca94140d40000c0281c481c0fa442900c201805c0e405844901c402503002040100300e60f140645c040e0707220f24441d90020070a01da4542d10780700c01d0184204107646042d1140703031040141d130341480351801905045940c403018402c0d404034a4480c0c01410104001d00d940c0d07469031400e1300200101050b1819514900110702c80b104411415004402d450344102d520364000003103009800703051040c0c0709219a50003407550000c00703c0701202404500005981600501c2401004145c0f5000ba0102400203624045414200301c0700540c40d0000c01055214840400e11600c82140c070702040403404880110780110b9544003e00002e4010402c0810040451400e00c4200c40191080c1003040d0482c0d01a10680f00d903155503030810340c161400007860900040f1801d120103c0e85c0e00515021501c94082e280c050055149680410303044601920481c10b0182c0204001d40b084810040c4036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 448297688 1250 448296438 448296463
    0x50d170a1d1f05160c08070314032803020c060a1b02060405120d0b060a030b03061807060f1209030e040e210f0d020304030e04051f030b060a0323 64
    0x1c007030581c075160312842d9600740106060400600003016a00c0c10f086000c40c0190340e410807074241e5101d5945141c260354107098481124501e8440390502100d4501000303a941c0c11203194680101d40e80e8007100c81e060700126054042c280340c1d00344081100c024041010030301c079008007500014505611207001134240321121000301150f000c4000c200002d10045040e08641d0311003d86107803180d03e070300c1070f42d4040e141504456400c1070b03010880449265154000c0c103030f80c440070380c15510540c03030705ca500d11301000c0c803101c02c89900e5201300c0d0104443c03449880500c03000107080c40c1c0000b5101180040200b544c070f0018042e0006051404081035900d40340c4102615048050300034020918200f03400d9a40f004000c000403103640300401d9400550441004072940815110821036603440c181c5406010424403007801406245401d0004501c4100c01084060441c0950400e001040c590798425021070401425680c00400740400000050170581414441503049544036402941110101d45004103040c00c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 448298938 1250 448297688 448297699
    0x5010f0803131401200a030908120f030606120405060603010c030b0102120f07050a0b041a0f0a1d10140601081003030c1113090302010f0b01020304050d170a1d 70
    0x30302c0a2541000c0007204603450080039a0407480c1c800d005a500c3e80710003070301890380d80000c6202c2c50b10302c80c04110301b4401c600caa1200e00708a0307103070140103a8078500c1490b40c450501c000c1201e2802c21801c540915405003000702100e1400c80407600c4443c80200079103080b19103500c8941842042d29081c010503180e05c0c000d1030304200c80c185040000f55a80840e030721115a600001030100448900700040b196640d07002002c40c0c00c2c08075a45000181c51604440039208103d40410164014608103005802030741e802c409089940c6038581104014085c01d0340301c032140c106004058a4909080c000d45030381514561002403404001e40345c50001120041c0a40d0421603400f0800c040d507d884200701054030b0b003500e40a0b070b41030041e1600100420158011030350021140c407000034030410b0750b0087c4110314480d600a100e10007400440a06484500e03280340d0243e041440140442d05050350b146059901840c131a080e00c1681c00d260101c5580a59803100c00030ba843d800c0718000c25443d00038100c00d032009852 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 448300188 1250 448298938 448298947
    0x20f04050610080405120c060403020d03060e0a02031806070e011e0c0b0c0d09080d0f090209011404090f0b060108090613032d030b030106120503030106030209031f05010f0803 77
    0x146001000300500b024000320300003040c28402c0c1040070b26240f20900304004d603250004503560355204c6088500310010303c501004440194031a014502c00c070307008240c00c4625038a414601402039000201842b24018002e9204203090800300700080c042c030400e0f00c80341c10103c101d00c001803030000810700b82c03000101c0781c00030244a1a4400c0300c04d19480d4114404200a4031000010b641c244100c10f0703d0041103040004240034018044000c0040c0d00700d0500030403203000b038840803805460380880040c0d40490980300400203254400a0010002d43c000d0002902a03120f961340002d0188160050b12030650840412110303581054030a034000c800800248206d18060040c100e89009004006003048220382e182d550314200a0112080c940180c81e074109491190303040100100a4943d000340301c1c2d800d041000408625113215a400ca45d0440040d52031a03003400010341c042c5d0300c0940c0d031940600c00c0c00300302c400c0341001404809110782503c001040c01c0d454004011407800503a040f06074250001c11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 448301438 1250 448300188 448300201
    0x140c030a1404112101050c090108010602061501050c1504080d060b0c0d0e01090b071a01051504031b0b1605010b040c050d0b03120a02010e0f0d0801120219090504020f0405 75
    0xf0381051110364221102c4c4824054042d20f042014004540d081a56003428180001400d00c013002d8102a8802e07a40d5505680c1d031814101c1e034800741520108544c406081081d2100c1d4411030081c013010803680120340480b100c0142c075032410001201c05980c01c020101c1c003098004a40e00403200102003103064181010402d820385030310303902c101c0c800c4010b00032000c05400d8146d000340301040c014400e054440b038507040c1c907080c4404030080b81c10602420710020000401c4030300c0e018580001d00955009458206030a61359244042e030050941d4080d0b440d00b40a00148070b4001e00000c115951601c5640d0001802c9442c00a003540d904c540b04078072407424016001081503210050b03901c9145940030101d02d12030900007281c140007e1002405019100107100c60000390150041403c80c1c0c040c0c0304503407030314036071055881e21114480c0b0394400040111004202c414858222002102c1c00101400214541030b0b0360007005040590042d20300c0b42e151001c1005601e0180254522107500b0f0302e007400355107040b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 448302688 1250 448301438 448301453
    0x608160c08220e1929011101150b0a030f060513230901021b0a350a0e040c0e030303071101020c0610031b0e1306140c030a1404 56
    0x40070021207000000c980e01880d00782d50440c1da005000b0360034090140e08001d04050b000304054401540041c2c2412018080d040f844950034082c40e00004a24118041840044942401c17010400143d0b649480820701035400d07401d41c1d50000d00c244640c0550300c0104230b4014054804000d84820110300d0804100311a454001c020301c0c40f1a5a900c0014800c484c00c88407660f0541d4800c105242e00f51102c2c01c102526405600800851030848840f01c13000800038245030b030300c178010100102041040c0f41e00d240c10070740000c21400708140400503100004101555046070f50043c11403580080c0b0210126407550030103208a0f618600d641c90603042d180300403004640d891001511580801c0384990b25054858400e40c10f68007040e180c88240c9010b4100040c1043c4480f03410b000c01d44030514403200c0010a45400081034003100e05400300f2403015965900c0c41e00319010409001d6520300e0711910340130501c12960164038401d01002c82059224100103500001312100414a851000e0901c400d010228884 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 448303938 1250 448302688 448302697
    0xb030601091a21010512010b180601021c030c0f02030c1c0509091003020102061e040b040206040306090b2e050f01140403140d0806010c020108060111070608160c08 72
    0x20081c00c2c5504040d507003041940314840702040c0c281040c140710852000000c2083d8101c9404903a0b81000500722080c0c5800c0b90580c24489503c8945101140f1085001034002c40e4040c9050054460280944040c0c100c2c480c848c2c1d811000003030751394411620458000c040003c131030700644010b505111080c280607035100c1006042c41959004a40041c40c1b85105030112142000050030310f4074981000c0744650480405800101e0142c000e08000030700c0a90302c05881c1f4a0051390100016040e140c0e5141e10a040f000a042603030812010030001c00807400c0707805500312a03449400b11030300d145041100d548512681c072424030030001c0c1500c3c0300c1d100440d541480c0b6080d01c00407100044c81010820041e40c008643e0002040400e0380880c0000500846490400d9a015000151011080c0e0301c1800c840d168022a2a42c1c003140c124442040903502c1035071900c0c0d214070b040c1020750a030907084030715900d004c50f0341d8080c0001403020b10170820b030035008003038000e40d003091801e0000302120141e80761402d501a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 448305188 1250 448303938 448303949
    0x70b011508040f080405060c03040f090203070503150d080313062406180306090c06030b09450706020c0d031b1703040305030109140c0a0c1115070c0b03060109 70
    0x1181000d140a004d004000c880092000515080e51181350520032512130b04148140c003100249006d000807002c800c0e008070791091509981e05480c50356000194108040715484158100301d0180c2c0e0034001641050003540584075480303102c03d0315442450403006070365003904202c0c81d4812041070000c0441c820340c8548140c90711030502081c0d0301460140507038483c0043d8809000c0ca03040500c40380501c01d500c0340b40303002d0744c4050750140043c00b5640306000300e546040c1e4000d0514036044501000c0c05810307242e003444c5013030444039070806030000c01200c0d40c2500900901d10401d800581040008940401403880e40041c25150b00d40e0144c1c17151400b034a40ba411500580c02400c05407502c0b0100107540b07248041c1e501c50803843d00d4490070035040041c02da40090040240380c0d89041d0048025014001d81c840c8148090070300c1c076180018144045400304541503003150f034220302c1d840516013541c50083e0110568110003646480b11443c0c1011805d0520756400741d0092a000c000b03020803640c0c400121401c4d82d2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 448306438 1250 448305188 448305203
    0x4300206060f04390305060d030e0409060608010213080604081206131112010618091e1406042306010f0c051b0f0303121503150c070b01150804 63
    0x50710039010802400042c81302040e000700c1c15245851980e480060307400380d030304824001241101490016001c5030815218164010241c2d442c500009100d0038140d440940c0c0a00042010803031990b4600c25600c59800902060b50085a0698164010920381008040110062080c1e05080d200c010f4144120451405503176000400a80b207520381c0716000c0920f8007411000c00207429940d0f890b41094003d48805c001100c0500000140304e0301c90307500701920030000c0a800c1c407500d1a0a880100411900c0700561280c80c5540b4206014986407241004404020b81150b001d03140520820086541311040e81c008550403001c081108070b004945180c1c0f207942820174060403914100d091303c10340410701005014dc80b40c100544080003062025068048080c1e130780341c03c581c03285003c040c0c49003d1010760f00314114000c000901d00140c5c0d00f07d2081005009800d803200c034440300f90140c40c1d22000700c940005110300000c4ca5010072040c1200140100001c1d9182103410564410003040701001420151491 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 448307688 1250 448306438 448306459
    0x402030304120309060201060501050703120e01110d0b0922030f02030f04140f12030f130e040c0e06041503030810050901060f0801140321040e0430020606 68
    0x64400300112006402c0400c00324155208500e0000c0454280f03011384030055081c504002102c1d40101e0503680744640c1a1240c10000613501410301c0144040c40c0c04180319074858900b00161413440c4018065451000c0d000b0551a00320f0040c4004524054190b40559001c140751030ba500040b0300800d01c41651501d0143c1d074031190007100701d165025400c0d64006241e0002000140c03004a042440d41e4030005132050100c810440e000c100ca0301d091400f07007010580041012941c2e40040c0e030002e2101d0056543d80c060110b480758040000f10f10100c0e4103d9481d224200280100c140307041c000c652021040f2410b01c81d00c0503007810091301350400c0c4401400d000800001c0b038500f119a00710071000e440d01820181c40b560f599100104070780014240040411080070003c40c42400d2808003010b6108040d005042ca040c800d0580c6600814110031841600c00520001c40c2d401d036568012801030b80240348a58081c00412140b0b0349003040f070021400032a203507510f10124150042191580018215015541c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 448308938 1250 448307688 448307693
    0x705070506130311010f0207050f030a0c17100b0a030209042a090b0139050111070210020607021002030907080a0f0308061903020607060609092001050708040b0304 72
    0x4005650304095400100800c102a94030b0341090304108480c00303229984c0c1614808801541c01d41c0c03140e014440140c00840041c0140d0400703001c7e5051703028018088070041d4020340c5600d425070800d504001c05280350b420310b02941520400140106403802581088088840800940040305901c8000d00501c0c040c0c1c0010240043c03005160000120751904044c2c4281580340003442c80071074020418120714201c41619554843c0603100070301d58980e1110482c503201c844124210b9906003070742449803980c03082d034003000400a003c1c040042d03441500f1152690740510400c031a8840c4c41040700304650101d000c20841c1a8001418101540c01c00c00c01079890b02c0d84440d00e8200300f0030360008500d500c9040c00b9041001120519840964001e80d104410b507101c400402402d41c0100e002c0c12000c211501c814405440c0007801840a070b07118440000d081541d55003030300180d40b65110300b917038284010004d038522907283d038483e940c03102001d203481403912020390b44420141c010740c040e220304140048005001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 448310188 1250 448308938 448308943
    0x50601050705011503020a0614121302030a0507050918030313061506230309030703050a0215070c0203010f02030603070308070611040e16090b03060409260d050609011a0705 76
    0x401c01d402070002d011200310880f07064840141ca1008030b001c0d2800b254000740d602d20484802e00d4000b080c50710945031041031002004080780140c400400c00001c400c0c0d00c00165000c02c0312209a80c480c00141000070b184c10300300000b0210080c2a01d134810000107680c12042400310459901541c401e0305480040e41c54104070700284500070304c0d54041c2e1221000480c0c1240c0242240004e1410592025035180c00c0480382c90041c042070310040c080e98000d210100010b401100a040b4000d122b20440d02644443d841c0d40d24100000da54400104610344000820f60030203003da00c8801140207825403a504112010070340d43c40180c4409064024086410f03410084c040d00294040241c01010a443c1c60321132a01c03425064044e91004800240003102c00b16090040e15528100e0f2420750411741556185024000a0030201401f01c070b15101015000355814080c01c01c02a00c0742511100d01c0d1039a003900600001c40d18094111840ba100100040081c1080011410565000c000035191502071030f1070311a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 448311438 1250 448310188 448310197
    0xe0f16020703051e0105010f060c0f030509090109020a0809060601020705120f0f160801090804092c030903010e1209040c051b150a0b01172211011103190305060105 72
    0xc209010b0034030301020070304c907070303401c40c0d0150180384020005641c0c1d4907a12581e080305071007000007007100c881515004c11800c0078030954490090800324544400c0100017540743c4001d802002d0150780c04140258265808005140d110f4103903001010a802d243d00046e41e02c518522038503228003003401c1090b0307824105202d640c0390900808100d4186e845104c5c280c2d0f07291030580c1e9011000340850036000034070040500800250343e0700411089c0c9480d0520109901a005072100c9040720340716440040354058542030889a01440800075544506a400c2090300759140c80e1409a0390303500c21071130000119003c0342150a410b40c12140015240764500050300c881c080c03000c00740d82e20034644400310310070f01001c110b42918a0764200d1960b140d079581d503002c00446032520850ba001030020a010040c408844007010740001807100454916203207045101080c5e0703607001f0b040b1420030b0302d13804c50300481d40c101e039030340d201ea62a0030041c0d424410381084d64003605c2540203c600c00c2548603004990280d0003082200d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 448312688 1250 448311438 448311443
    0xb0402030130030518010903151a15040510030603020a0b0307030c1409010f0e0d1407050405010e040f03200d080718093c060e0f16020703 61
    0x295229030b0740b40d00003107084400c1604001c81c0750404100c0c920058003510040e0259030705403101e9081c40540c1004200d5880f60a00090612403c2c0f0804004110006007007e01a080c29102203201480d800c0821420000805040e00a03540c09041030300704441c0900740c6007a540309480c142e003102c0000700114003900c543e90010350481402d240114100d03044400a41c4038408580f010f201502200c07008a0305803011700d00d0502840da051207559040d40c4100c22608146150380b424000482c0036400060310840503513800c9a003041d1421315004404402d0107560020701e0304039020086503240070307103034480e0150080009114050000c0d81c902014040d180517041c005905080c0204031090541640e564403e10120b04080344200b0300103018544510003030101c41720340010106031245042180c40242802ca0883d01d00c140003401001000500140e80700c101450092a9500a04001c640d131002c4030358070340040a0102c40142009003051010300140d40010f10044500d1031103440d14012030a003881c94000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 448313938 1250 448312688 448312691
    0x1801050a091206020708040b07050c06040e01060e030a0c0f031a040f03050c0a0b01172a060703050c01020c0304050901060e090f040f21030c020708062e060201091a060f04020a030b04 80
    0x20a08d0340c09070000c0d10b501c911a20485201d22444000c00c01c00707024074499140d020340c10400601071544140c510780a03661020342250001c00c5180c1d03a0f20300741d0413590005100c0e4000418100207202c1d203030701d6004104420300352028140c11701d512008440c0f002c0803005410301900040c05c4030520004c21a4541e2150440f501c54025612508484800072388100c4481083c8034100301c0881654041c800342091660305d0105181c81346000c801e0003110b07080710005505000081c40040ca004200703000420700d039441440619903030750802007044904d04068010340d0070003401d0440c00c2c0554803120341003a003100f0384100c0c0d1049540d4914001c541052143c50042000081034195400c0b18040080080c0200c2561001e00080745951001c981d1040035106448155002c2d0000c200c0c07448450307041c101103c031444058529512005001410140e2a500950060707550703401c0c00013406010801c8001c2040c0c0c8652003c2103007011400198840c01340b004d035601c00ca40c00214010058000da1000301d04043c050300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 448315188 1250 448313938 448313947
    0x50901022e0b19050f060c070f05040c050a020309060f19080103020901081b040c0201150b04090b0a230112180507050102190609020f0a0b1801050a091206020708 71
    0x2400c00c03900c0762035500125418200156911a450104810440090507604082c5140c2c901820080c1000941480319040384080124010345401400041c0280c01c1030819441c00c10b24010500048640d83c0c0000000c00c4002d00c604550075a01000326600e0384c8003102e00e0703601d40700c503041c540c5800c1c8a82d8040201c20b842410200f1081900000818101e900880c0c000800c1c2c0c0c1d80780002c60f100c25080c0581d00030010750b13101c813840ba40303404e520840c00c0e07220030b100002d040c620b032091750040100d107900155101c481c086420011034643d0f00660040c101c007a2641041c0c1ca2804c01c10307440d6240151128915050303900404d903800e92140d20061034424044c08144028245805440c0c00700d203600c0020f50300f0703001d61580401c55500006000b1350019014600c26040310301600d81c1001444d414508a900004070041403805a0354096510060461703850619a20b81400a12050f401c0c0d51a00c1d150500200744032510034643c0024000c400c5804003115a88500190b160840081c440d00707500030002e92001c603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 448316438 1250 448315188 448315243
    0x30c03031e031f091b050406020c0603090109080304050a06060603110f03041103100906051b030105221d010b031f1a04020705030306010807090e160c02030a1113110a05090102 77
    0x1c0004641e03e01c500010245c80368202011100d80c03040d8000d04000d648114050019428028001e551200c01c000c000100c0c0c041d5581c641c0b0040d841501e09460355170090158806002d9144904001004039040c1048440d11400c100d601c00c1c01180c03580040c6900100000341030024000c0045600321005094a03043c02842032800c0045c14203150591750786141800040c01c44d0038900781141c0c05400c007110070741503a28040802141d1560040007030b0b038042607403000c04448032441c01448514074080b10a80d4034404081d06050031920a0b2140c14400d171310904020b428003410001030151003c505030080b524440140010744101c9100c0038a030703081840040d85a00748103020002c0c600481090386e805031280c44c0d003842201c07181d0160003101e4402c082c10020949800c042580400140d0035804c2140c01440303181c0000342012010300c0140e034030b6070312000501081e140c90840610018030000c0100031014160f00b4080c5c581c02030742d07052014000300080c002d015a0081000004034090080d1829a10006a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 448317688 1250 448316438 448316441
    0x131203110601060f0f1b1b21060506011b03050a020f030f0705060601080c120601030f051008061e0402120f0d0306080709060302031c1806030b030c03031e031f09 71
    0x526200005e03010545000000c0c4501e103e84c20001d2a540b07110440f100d26225440c6140c800000d00c404000882c000281d40d022103401c14041c41d50203844030300401d1080c1009400d071040109481c0c108811007000a561480c40781d1051099605031070415291048404180d00c0c28014006110152001280e14980010200000e100b15031240e0141e0f00142c40c0d100054450a60540c3d8824564005220300c14020307030310608403944464145808290b03451844083c0003103c5003595000414602c1800078014040100f007070541190080300c401c0200000d0303a0303074050b11a401800007840780340b0314a8a0321000f00100400c0c0030303044807a8151003016260041c0a0002c0801d4441c5100354080c08600091000f014860300c0122a00900a480031088046a20b02c01d01c918041400910024000c1d410006e44001c0c8a00c0c0030303055a407000036540c0065010103141009151500303200303910801050000c04610b403050f000c0c2d191201205c54032521805144d64015000d6010380300c42c44000d440001351040316 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 448318938 1250 448317688 448317707
    0xa15120f18120f171b0c0c0907021603060b0d021c03020705100f080621030c060f1b0c010e01090f0213050f0117030409060603150b13120311060106 65
    0x381d41d41c42000c02c64038801d94003441500045800b15090350583d01c070442040081d10b80c040300e4440445412110b804803007407160402403840c82258031011101c4510b042080e203807a0440b450740003e05e50822044140d60480720b1900009000503120019484140c84050310011070a900904044c40341034856400008a44012019401403003a0700b0005034604080070b008003004c403695943c81c101400814140c030440780160030359400c05545611900602480d40c04980b102da84940030719561419015180e07d003101c0541090300710007218003889604005280106c0c100d0020341080d82c0c9548108900a005204c10700600d20254200071686080041c1e400080305044d200300c907150342002d2031555013030440318122009607a400f00100140581c0350300c0c0c110406c20300c43c0b60044030f02c0c298642d0352180650340154403500100340c407094456070030001441c1c0e090161800403000c60a2030200d0007441e442004610070707042802c188461200a040c403680d103001044140d8000c07248139580d9120020541d281 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 448320188 1250 448318938 448318943
    0x3010e041a0603030f16050f010e0d05040f05040e031b030d050708071211090a0e070e0111100b0111011506030b01030b0a14061b01020703020c0a15120f18 68
    0x4a407541c101003103000750505802081c028000310f0030400d03641d0f0070b602507900c0b0350040000c2e852289110000030701c08100c0004559914400864a14003150240d441c0100500007681440700c18041440303010b621806000482d003044802280f003044201070300c1c1c214490b00c210010720244901e12a41b140c44000300230460035410032000c0181c0c0e658560200c507130110a44d144400103082d0580309007030780c800750095003510441204440c50098080d0002c5d48200b107a600440c6a11aa4002c002175160490407110107281e003820400507980070b401600341c0712003e040e0b4040c0707500d41e6600300d100340764414056000c401e10b07400000c02a60041e00c003482c5134a0600e128120001c0d0800550b06595407003401250040c0c407003c2c0c080341d0f1440c2040b00714a04180c0c0c4035421900845c0900540088988942e44030309410a40b400059603217550b0708009007031144030300c23005014070588c2608009951400540c00c00c4c0159500d130080d030306030101050001a04c0c40000711031501d400e0110800c1620100601001c01c40d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 448321438 1250 448320188 448320203
    0xd1209060302040b07060b0a05040c0908010c0e060a2106060c0611041214010e071d010f0b0f031003050115050f100504170304030609030f0807080603030405121203010e04 75
    0x3a40e40208506911950003605403c3c8003d01c100030004855410181d07202c0740091081c1e100030b440780046400c4810800503080014040c50041101c0407082c4509c0790320031080d1500c008403034944c0d804984248136000c419010060005800c55684460a05070201c80068400500060b0b0340c0e82070041ca0030786146400c1d01e03964545140c40300039915010454088a21412800008000b142c8a5805070000313058820200d540758248500b481405020140c081d01c580c510b0030412149005802c2c0342003d05070000910040489428411400c1240a680d6101541c0d4051a82ea903160088080f6100407940010049d40c03c04480f9200440c5820841d41a28804c1d1002614003248800b003101c8002c000c034003000440c20070401409294044418201c24199510441e450710341e0700d694203021a0640801580015250302880c130050768401a180d4201009141030b000303d00b00940080d0710703885070784100d82c1719214000301840c01c00818030011500c1c58402c4030482e02d039030b9188039807404502c0882d011240b04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 448322688 1250 448321438 448321457
    0x103031101051611031303060c0f111507020c0d0302060a0b0d020604030305070f0803070f11010203040c0612061a0a0201150806070305130807060c030539090d12 71
    0x28a051040303511603c0300481d03024403681e0281c400d54003400c902c80400f403180020841d00c94201502460100118070a03000018a8040c0380002010300c60500018000c00003032404034007131110005441f580c210020900e170310058071801c0d010b03850002900a0643c2110101d0f17016414140c001c00c1e4248149518141480240c00038030822059503141c040082d44480180b00500200388101e001d42000d5129240390320341e03401e1f162203502d0190000ca0341c0c400000c070003199840040398820300308034a50b03e01000a6081d0308180d40c0e0700d006003050b802501d0401842c80f101041e040000d81046000f0030101a030001181600b464a034415402001024050740c01c1580b507004400e0300d4542c610845800070081c01c40c503111000b0841c0644170280c15034007032050f05020080490090002040300c1031052100069942c11300b0009400d07100014034611a9481d0741c0105040504014a0704e000504501082c004500a20980f941e0714082d1a01e1580c001c1e210a002300200801418407101d89a507540340c28045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 448323938 1250 448322688 448322717
    0xe070f0207030b0a1104030506041208090a150f0e0615060c0d08100f0e040c0b03090d030b060c1c080c0310090b0a1806030b010815040210090308030c03010303 70
    0x16500002004001030740101c0701080850011100309400001000c400304480701141650300c1141c1081c0c000740d4644d0404020711041098548101d080b400103410074441c62715040080c203840d01c01d41c241c05400c03014442c10701002c84000758040c3c51203140c0d810f07041050000e1070741d4041d13561303000301c41d0b881c2c52591038a180802440c04505941e203644610004200070007400c01d04a414601c09042c0300d0f280c00800031b0101e1540d8108445a02401c03581680c0b800134a02800c2500800040c1d910200d00ea82040050051030340c2d011070310489595181c02c0c0400d11422800102d4514460051400018001c1d145100a03000d964841035444400503542e400203900c1d69040c2e01800d11055a509201241800040107403010070340004401c0d000062014041a61380c0c841c00754200b51110041e1007041e9264000d0040003941038049000d40b55140091100e07031040c810301d9021610107030000c2d1042410007110505e113807040020902940d40800b0860b2281030101207100290801e00040703000c1540120910345 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 448325188 1250 448323938 448323947
    0x20d0603060b03120306152b0b010309120e0612070201050f071d091e0702060106140909010b030c040924061d0111010b040203010f03060605091003060b0a03060903090e07 75
    0x1100c20b40c00c560340d01e1030b180c15040001c1d11031000c1f40c02c02d00e800117100314100d0b1200060194540081c8401c0708030b070800346240540c11a1038031800e003410b03d40b4108904002c2030824107418030321030041c203201c45070708401d2000403005c0c0680010420310301444000c12501b6681074118030300880c0501070034646c646070402c1c1a01c413030384410010820004a02d00351240c500d040c602c03640d00f268004041d10402c50a02c41300c400940c03c101d4250000d40d20180c010040c4c03690088600d1a64404c210026090000312000604c0046040c8200c0c1d03504c0c4808030208030a40d81e00821503000b01044c060802c080460700d22a6100c40216014040c0c0b2980c400d880007940314024107101c140407040e12000c82c40f100c2c00713200541702050740c49443c0d1215941e88029501d240c03071700d200031400703004216503400da601d1850ee0f1910a4448640005020340004020b020840043d84112000d8952103000813506045801c04190f0700e582c43e9102801c22810880c9000034107811006c182c050ba403030030041980070760f116603043e603 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 448326438 1250 448325188 448325203
    0x30a0c080a030906060f06030624030b012c0a0807030b060f040b0307060c020a0b0f0a112806050a0c02060a090303090b010e0a050c160b0a0b060a0503010e01050f1507060f020d0603060b03 82
    0x4481c241c2b94540c411080744a50320903001c0c20b205040c45c01225145078411141c0501803890380140110b00f09040d0002e10788240088000c0c081c074402003900034115951090118405003403180510042c0c0031200c00746e03803547c200900c2c850020301103500c05a600c01c4028a840200341050307008201c01c2e1408103034200f0360307012260302c6520f12040d01d16000c1d020310b00303c1d000d281c221803d141d40d0260602e140f02d40d0030301e0741ca0b010082d001380030247c0e04030f080b50420900f210005802d01003418540a405828160049000b503800604200c00164418040c00e054001d84800c0b4001010b015802c000841c0301c150007080d80b401401c082104009540d01c85864040900c542c0824400100d85001690b0010346d0a9100c0c07070b40300421000110b403400081b0007248217604803105550104202000501c104c0105000c00c41c01410216660741140c1c4820000c00c1003c810b2080440d07800c000094802c040c420180c122542d0030104070303821582d0b1004083d00070300a0000e0301089400c4d6041c505480401d15001840e103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 448327688 1250 448326438 448326479
    0xc180d080f090f03010c2003040f051002100f022206091e03020d0b180c060f070303020c06242209260301030311030a0c080a030906060f060306 63
    0x12440c0c584a5003001c1c60603000001c8980e07000c1c0041980096503113080c024194050305036201da454800e0701e4107c51403418507449200000d03a00905c02040b004040303964281c12942c041d2640340006000c104101e040ca20181c014890890500c9905448084207038001c0c0030400c050a280040c041c2007802156040c5882c0c800e071000034080801c1070064006c030002043c0c2c014804007190042c582e8950201e030200340c01c0001941c2000c01d01e82040b988189140900c1c1c0310184400162503140700700e600081042c0a038006003000c2c00c3c004110202014044e0341282e0441d201402141c140c0e10341170b603141d107217850702107144a0352020044161260b8144180300b0258490040ba0f4030450400c500d41c404010042078009580d040100080001c0c80c200300c82003206404002e8401980c2d035030440c01c016000e21001000a007143e4030400445004075131001c0700307200345580400ea0581c0c0709140c0030b040300900201203000d0000c600d07102000481c800005051412114551024058142e4804403600c50030900d4042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 448328938 1250 448327688 448327703
    0x1614010f020f0705011d03100603110a03031e0302090301142d060409030c24140105010e090a061e03050d030204060c030e0301060b031305101a041503050102030c180d 73
    0x103004d00e42c0905c5881081d009011a00c0702080c1ea0000080d00c1d046078401050320040d40c1c0c50702071003403200da04140c002a450a0b00d12608107450341c0d400800960000036000e081ca60441c0d0614142842034040303d43c24075000703001340004200388255103a1080d0135030b849894603030b00034940306081d10704000200c6002004501d500c40c07035441380c0070b20004d000710b484202c04221061051400003a68030300004110f59481c0384400040900741c14041c1282e050303911041060041c84010060b50303901c5480190030b288103031880d500325282c406e14100584500d8102c00c800e05071004d58416611910101f51044a000f03400300c840656424405804a2040c1d000f441c0c0020440381007180424000e40e04070a2507030001d0000102103540324025500c2c0d0300169400c140394110070a140091127400c01c1410042c0c5019072003004001200b01c4503412100015441c1d030f01071030302c9281c0103051110507190b1400668100c4001c0d90f0303070715003602003e803a0b0b80610200c007a9210b409042404605000c5d85044815500819 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 448330188 1250 448328938 448328953
    0x140f0f0a060c170a110712020901030f050a0210020102070506010e0408120415050403050415080720010204080d32040905130c06261504020901021614010f020f 70
    0x40455040904a4064507496068510119000c1141000b00141e1300240d61380382c80c150320001c8103814a6243e03800b20349040c0710404408090381d0b0703101009046170350211113072202c00c5192804508048241a000c0d500c07040c1001c50f07040c0590103400500005200e0820345486a032070780a0150101000d80c1c01400300070050010030b000807100500c0a400502601025034401c01c030459400035120121000c800040c4085000c1161f64001c0d00518003180c1c0f0740c185948d007403504640c0241404441840710087c44524090440820000e6040301e0103004a030040d03603801c542003100600319907211082c00750001509180c00007220b003aa0203100703098800d40040ea1a0500d06603400016001c00380c00b001c0c09001601c14000056911501e600040002e9259a81c4020400e1180c14401001c0314400340200b42490420145145200200148081c229001a21074025100403860300c0310310a4414000514644003182100c001050882030320000da80b07a000c014030b1582c0c00c985914481c44034020a500158 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 448331438 1250 448330188 448330199
    0x11b0206100e040b0c070219061206090509061b04080105041a010e430804050c0102030a0c330209031b0108070c1b0b09040e0c060a0c06060f140f0f0a 66
    0x4d06c5281c0c001032500411001d080200800034000394000b03408078081c0c94980210300c405000e52402042d003480e00f00454500794440700e440310401407600c803400c03004400304401c644003035007514094200b10008201c42e20703042c039000d03040b0080060081c1e4011500b10000450191b501c450070301c1103260113415031341c500141040300242d00c0011b400e40b02c1e1660768a1194011110a8104030610313440740d55070412410181002420b0103e1840c1c030074119001002440950342c0c2100050480c558007214462010741b4250340070320042c01500300d91201c400d015a0610004d00a600a44a500030032004d072140d66a060f403050405603e46c502c802d021600b440001003070b0038026546450f646001d1181841c803103000c103900c1c44560401c1e07040052114800301e11965213051500c00c2d50903070120b45008000880d010741c0011124001e80070440300300007800382c01c07808000481e0083c1c002400c1c0006018941d90311400c075504c1950070386120130b001d844840e40e210424641806030524292002d0725011a02d410003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 448332688 1250 448331438 448331461
    0x170f04090b090408040314030405130516260c0c060c0a080603150c0702040b0301020c010e0c092707030f08040503061e01141504120c120302060604020c011b0206100e040b 75
    0x2a0300e9024140230038400020562104503e040303190b04982000905454002090040745900100110802003004143c0f0075074103000c4904102d20f00c1c0c00b0000034480d941c9000c40c00a62040c0031032014980200c0c01070000b003642071030240808000035111911039503504424560f8410506070724407000344010f40812100c06001d002005614000360020a41c1100000846e0036a40580c00d030303285a130341d614110503103031005205900b040e04081740c1c21405424400c2c0004501030084040e903008030100d0300c60780a4000204440c0000703660000c001d0798401c40721300384035483d41c1062003464040c1c020074002070050036000401c000d0a0f14400404011079081683d0f013038826601d5181d10350090f4012601940010441029000501c0e202e416001700076a149400d01d02400c403640003004100c918003118000075004103901c1d40c07000003958010380b01d8140d41d00d00d5015064503943d032003207010001d02c8880420f03030105243e0721403815801c448125a41d15805c40000040496024108240c0d080104020807540c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 448333938 1250 448332688 448332713
    0x100e06072105010f171903110f1c03050a090f060e0114040b1006020a080d09020f0910080c01020d140a03110310030627020904170f04090b0904080403 66
    0x20361008640d4007250800408070354080c0c1040710004a851000c100300c0114500e03520b5080c4009000d400a40e07500ca82c24000740040000003011700404115248580c4010070041c40002081412070f41e009109001c0814010b006002e000300090a0400283c1c801c8514040e1281f12a8020014039507000192160001490741c00031488a6549036144544022054600d25005a004e800000320f58205030060040007107080d8880029900034214043c0854136000c151b0f503e03d0349203c00820310a49a00c0003031014410b064500340d00c0001d02060214000c0c1c85007103c1d00b40e808010841c0d011070440703030044ea40d0b12544c011890025007001542840c0d24032000c0030784905c4003281804600b184003541e07988219081283c0049642040700400c10a00c5400c0c002c0141d1006491420301c4540004680e1421690380c401010303018071321840101d001c0082040a00c00e2251807856519140c00d0703d18110a100e50052003181607050510007410150b207000501140500d41c802c15482c40d04e485e5580f988a003200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 448335188 1250 448333938 448333967
    0x4030305180706020106140a121b1a0304050c090606040b13030f080d051509131406090a0c1721122e030b011208070609050609100e0607 60
    0x12600c01940c0401c00b00800009060a5000407500310308050041c01030042d00c550140c410000c0c20001c0203400d543c000034846540e08002c100c080380120000640018520754414103903024030070300070001084007001840c0507038855010b550312100010300b0061124010380741c042d4002010001042400d0f2154000d11002c940d040c0c03803900c01035598651000b8100895000d60b080c0030009194040b40c9018171440fa404501d984880300c1403126000422801a4020201c03126854007100407010f000c0308000e1900001111030440e40d55240c2102c2590300c03182401c9007105d000751304610100c0c0c0d14130110114036010404000810f030700982c10f98000010701011140b1b0040d90010061980245c1011010354441e0081c0c2c004142c0c521007455140001070840142c05142d825044414000180144800303030440700340700d50140030800d060a09611a1050f02c4004165500c2d201a000c01c00c0700224445208198000c250b5454000c00c003000010b45000076a07100c0590005800a000e6a00a004003400c014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 448336438 1250 448335188 448335211
    0x815040b0a0807030606060801080706020a030c02130e01020901030c11060609060d050a0302071a07030c080901053601020601030f170705010c020105150d050703060b030a020604090e0c0a0e04030305 87
    0x390381d980120300b0711600313402c01e89496480d80400d020883e0081030140c01000703824002c04242d4a024002511411400c07001020000846c81050555441c54441a40d011b10803108000e40510000c0c042c0c000d40c400304c0c0b04da02081c182260f070042d01e07004820230b080c0341c4032075006082241d03509410402c01d5440100f81d103600c2481e004e2004045a003c0220404451080d0000e0694504210a81c0c00d0340d031803144020001c140400c812000240d10000c50310003554046041510340802d500140e880d8010140f03440b03d032584104071190800130312038100001501c80c8560081804a040c0126182c040901000e082044406007060000d074641c0b00207101c40b016040b1650070b04a00e503a403182914810b80c007903001030b0b44030f0060200c0c0b210300d6000700500034000c03038140b40d685c642641c0305516250a440080e000603a141010343c840d46081c00545d0314564024150359440391036843c5040180441c4d506176040340700d400952606401c1002c511810f80d1043e500302340d010750b9643d42c12405007400405800c1d0380c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 448337688 1250 448336438 448336459
    0xc060a120f0e0312040308010b04261e0303150109030503040b09010525050606040e1905030909090a0b0a0204030b01210501051005130612081602090f090105070815040b 74
    0x8a41480a80703c0107502d4041c0030221700b028200140607400681202e01402c1081000300103078603103003460300d100f00d002ca40c1c6504001d44280a00d4207200603a8106400060310802c12201c3c0440030008600c40e000c0c0040008002e24070750011220441e2a0200801d140c1c030030070044c8200d0508a0281c141d24205150484c9000d420340061072042001c81c8602c104006a04052404c200050106690002c4140c50401c044620520307426a40c0c018a0a03501501b400812564144181801160202000a00703203039058180003040c181d94641d01c0005480b0402c50202140d0381020600131034049070380050380790501c2d07401c00407060b820383c0302070f251004007000c8560b1400002c1c1c020300070284aa020f144c04c0100315460a405c0c030030441c3c10a5115460189800d00c01d00c5980010042c0000d0903400001c00d54940c074400c1030000002d040c19502941c444600410031025140300c406a62040240c1c00080c002c907101d500040e02d806206440c0c0341c0e21003481e000c3c0310032182032650003102c66440084c11600c14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 448338938 1250 448337688 448337711
    0xd050f0906071109090d120c09170c010206150a1503021c05160309020a060c0c180b13050403081906090207140c01021b040207060e1b030c060a120f 65
    0xc580c02007400303e825410f0048540004d203000c11903250b2003845500074000d1041490001400801140884410306580e10000d59074180318404920190918001c401c0c04101c10034031081d0741d001c00342003840c018891030000841600c0c070702503924a0000c011b4055410a030408480ea456908810000300c1059403c5c0403521002c14107003240414044a04800216800c0c40100740d000703000743d0601c01d020b1506002000e0300503100c000004003240c00514005240700d10340e24201c0f0030030f02164014000303c4000382a41d090102d0a5004940760141260b40c41e009000307682c000702c1030321000c4038040c1c04500a05c000500900e0f401100340008028010002055516002c0060407a0440316040d55802203240c12250040e208101d14a4412000d00043c10408200d19220481c41c2c26407001d64003444e004510b0104028050300000c030001d201006039002c000a440c1c81c1c2c0d410480c610500f501c6442207042316a6a0305001e0100c2d003ca5405584140c60204c0e08018040901482c0a51080c1c940da511440d40a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 448340188 1250 448338938 448338949
    0x8030c1903060602010617060f071403071e1103090d08040f080312130b01090903020102070f080310090b0d0f0c031a040b0906190e0a3302040501020d050f09 69
    0x11038000394500080c001c0c00d124000b82140c0350380d0855007001500081429000c040090311561002260800c0022542d40300c904855100c140080c1e21003800010050101c0c40790050782c0d00d10024814054828100354001c021201b0650384004001144c10400c150b00d203a00341410004c0e41a4081c40c1181d1034541d6615806e6034082c1d055010200c0d40d000465031110031144115941c2d00300b582c1042600d04045107403a89a0402018803a14090030b0b990803c05003094002e4040e18002c1e034100414402c0400241030807442e81d441121403000586540704081600f65403449044060074016008600b412075660f21409080c1c540d0308160f0704807148060020004140c01c610307400380c0710304020450403400d20380340003000003002404280c165040070f0200030403001e00c04085400c1064517000030038440c151840442c108581c1400141c2695180b001c403100581034420554485850041c0d201e10910240c81d642c0128080d40c0034040c0160003a9450a80c890300c198003070720400d6801c030802c600d0200036000280 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 448341438 1250 448340188 448340227
    0x150d0201080402100c050f01020901020c04060b030112060b0a0e0103120309031b020105070b100302012a030c1a0c180301050405100c11061314010221180105042001020d0206010308030c 81
    0x11f0303503900019071034400e503810300c40100002d800342c0c0c003800b40c9404c0221020550005000f6000c90144400300b000034131080f60030120365140301404503504540c5074905841118001d00040d03030541d5025482441d0b0a20034843c0f00360241d00b40e07480c0700c0b004050b400700203d00890004183c0c1045404e200c1c0801140304a45018020100c1d80386400489146100240400070f8045040090b2004030450701007603d0f955004141c5192305150107081c8410b9840c003c0c0041a00c44410080100f8140c00c011608444800511140c4401910b42d24586529000c240c00e0343e004841c01070107a00030b0414503080d00601d80000032824094108407051203031621500703103000001c0300c000302411301500c404e505000320301c10245c1101711310380000d42ca80b000d502c00c00070f000620441f06041740504a00010440103071845581407003204c441c001d011900781410314400300001c084110045000703003005140158000110303602c1d00e59294024007440d80c40d50311000c410350001801c40340016002c1090480025401c078128 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 448342688 1250 448341438 448341463
    0x2101809090209070c0803011415120406180203030d0f092a0f060804030f09050d0c0812190503040606050a030510050a0e031605010f050f150d0201080402100c05 71
    0x403008907900401096000141555041c002141c60002c0450303176410440341501c20401c3d41d10600994070001c00c0c1c00c0d604101d190340c100b900c0811400d404049904486016901503c0c0510060003428090480e00900ca14002d615500820241d4504146038021040c10080c140001861044d907031175240541c0c034460180007481c10000803e506001580030740c2c00103821481c0b035145055043c05000703030103c40007420140c01e011030404407414a0b4826150503020b07240c05000482090f100c0c0c6402d51842000c0e0203045028012980398841519114041d10321040d400c1c084211548413030541992079600281c002d070b0f4a95150301022075162201d00300d0304000c1d407041380100044882a4002c03030480d407018140302c1d44503040c990481b050602c004203a80c103078102900e008880362000d1a005004220811609a10b42e0508041041c3c1d1a21694401e200e00c2c00d010603d80102090010085882000c05000340460850000308015080c80541c1042c40000c50a140170810540d45034685008500184c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 448343938 1250 448342688 448342691
    0x30e0a0302100507170a1704020d0c141c030c0b0901060305071701050f1006110106080703060212010b03041a130506040b01050328030f120c0905010e190302101809 72
    0x8204100b0010300c031401c0686405c400c14240320500d0340040105078080920020300099201103801d554554000b0f0140300d5101024000f02036903010341040c0c0411403042203105146501e0548030350ba0741c00401600e45a45983c580140d4481340c2d075000d00c506405411003046640e554000320008000b00110b8000d04880704c0c041002d004413074803003400d4440041849000031004020311043d403c070340d00c690003505c55608250800c024980350072401099a41c1c008400d80c41201c00c00028050550300078070b40300502e500100d403543c0c2c0b94040402c9170f21040d01d0007400741d8250343c2c0c150b034411501d40c0443e0700202481c0c0d00485a9816032112480d10000b943c00317459120542d03004000c1880d0800c419450b402001e0710030320300000400c5800e00c03c00c84040b4041c05015080201d40f00d02032240903090003181200300100105020214000c3c230030f00e1903015071070100309420400304240c030340b1085440c0090705410390302421508581c00d01c20f2071b0303010200541c140002d0819808071150155621006011034060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 448345188 1250 448343938 448343947
    0x11071a1603140a03140603010b090402040b0d06060e1e250309050307150b100e060a1b120e0105030114040b030c060f0d061203050406030b0a050405161409030a030e0a03021005 77
    0x85c000710b420009012a0b10a0f07150114201d41603c07001e03040c6610503011980020402c50b2040030420000b01004000d103181d152440100e0001e46102420f0301455a000310030b90103100c4165140807000e001d80d042c2c2d8250385204106025848015040d0030b01c0c8540d841d011901e01010b0307882d0b529640001c40104e5403203082c0d501c0c03100c2c2c4903c2c920510070b020030119040303090025803000181003840d204041c1401581d0009042c141140190140808c1403240b40c05031b0841030090034022240c4002040f07000002e42d00c041c1030281b542c442c07419641039034045175001d8039819841c3d041100134889141c000e07401d4054441c1d02031007946c0d698040c00100d00c90a19050b59486141c0c650300403114103410030054074640b4055034000c01d03031003c1518203550071400d00146a003100e074001400c01c500c0342d0000d54082d00707003400c100012035410707051802c0b01516100c1e503a012402d0003148525020f044441d42c0c041d0f1040d0108001303e1700c44c3d5502640e1941c0a01010700160f12500840d4240d046d44850801080f40003d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 448346438 1250 448345188 448345211
    0x60403020c040c2309120d080a05010506031f090e01061a0a0504050613030503070303020c0d09030506160309150b15040e04030804050c0a0611071a1603140a03 70
    0x101a01d451407003180c003000448489040501542c04c1c950355962040100104003c1030000e19040720002000180a4072004017400031460307440c035544042c14001003551001c20110040350141605a43c0d000b89035900b980d6039214851100404260388031166410000000f556600300d100300c1e04c580009030000f2450a0920340c2d02e11406101041c0e060b4000000c00586468550100503242030700c0007101d450380d40e1101c1705e02202c1c600352076800180c03080c00001000000c040e095401841c103100c802d0159060032000110135243e0380c640d884081c200e50000e03030008075414161015583e0700865401c001801c1d000984a0030f42d420300c40203483c00d000380d5400000700289070401401e502e0880380380a0700d25003410a09160300924000d40b004041c004624042010404284807502c00700c0009480b40d403c7d04c0d5a03010080c8001c2e21414410264000c0d0107012840c40503003041071030310303082c1020b8035440c10510031044e180b180c14020b0306504021010705800201c5065500500030306100d654085111030300103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 448347688 1250 448346438 448346443
    0x7021c0210060e01050d1106360103020a0c060203090f060f07090803130b070206070204050a05040c0839060304060501060e010c030c02130b030d0206010812040509010e0a110c06040302 81
    0x107822000c80d070340f0fa01004104a0b60380c000541181544030442c0e10030001c52101141d00c90044000e00e4111210400b0b01400c203d920004d44490b00c0c102000000d0501c030a00b00543c200e104404e10313440090400140640801e201b40c004540204030001101d040c000b1b10031006003080010340725442c91000000601a05a038032100c1c0c4400b41100c50060751820106894041c04da41d0140300c0c10801c80800b051040556503080155400030b034002c5c10610541c5000c0c50f010b40101800c403001c60344010450750100d14540001200c0d80c10450748110f14081e011180700305031200c0f00e2025000d100c107911036201141c0d40c8582c005140160b204000c0811194100300020f07000301900d902c0b480c10010041d0002001c00d51100158a215805483c0700e10402c181e00d2400c2c01030b00d041c0c0003080c2c1511070001c52514441c0c0c001407a604a0321800700355030301c0842c503030041c0e1110b1049224841d0300050240c01404944003200340c1f15041401100e000a846c030130a010819540c02c814400c1d0403c0d00220704110030701d82c06 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 448348938 1250 448347688 448347701
    0x510090e0c13142a030a0b0411030106052b0c0801090b031f05070201060f0602100b09090309100309020901091a010f0207060c06090b0c03012d090507021c0210 70
    0x10b0000c20300c11400c20381a682055440180420b08655a81c01900350480782c4940892191640300045692803800100810203010001e00c4103000381d2904028005982ca00c0003a64146c2d22203503a4203242141503c03101c661030b84280c200d01e03900d0810302c008404c1d1010a04c504d154910301c580319400103601d849501411a40030034903c41c0070303070003a4405c8001078603010b91240342034900d0040025192140e072000c9004020035000b007000248070b82c0c00418642d400003070341c0c1c10803034490307209001c454440014003146030419990265294001d000054040c40d0902e50103042013404c0c44c0004a421894001400b0b800c000e0344075800c44d65540c82510002c803403400070541c10950a0070502c0840e041540700a41d82c0826128140400079941e00309403c012103a0454500136400c100c19800ca81400700d00c001456100f071007852001e004018085540100b203070103046230003500d0301c8081c040c1490154440c000e040c1c0141341900f140200c80e03410b1031030001d40c1400040d01109a005000364401c01c15030342d00322204c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 448350188 1250 448348938 448348969
    0x150a08030a0507030f0c1505011e120305030c130b071e02090f06060702060301030b070f0c0302030307030c0302390f0a02060c0312010b03090c0f0102100510090e0c 72
    0x4100308600c001d0340c02c00202c5198541c54640a0011815110219101d21000c03d00504200c800300501449184d0b230f8003c94141e0b00740031f40c03078400c403186880801c0d807002d030030b100d4070b40d1880c60640c03150042401000619444644140c40a19011540d00d202083c000b1a400030303083c81c1e201258910a001c0d80c070302031303820703c1845800aa401c4045a00020081a8000c150a06d10081d440000b906919281c06982e2895405004a5100d5840349007437824003804031480d80c001494103101c1c01e0440d102d00141000c46405801440c03558407200c030214040d026420820081c16000c1082c1104061250b0232446071101107550703c0300700c01c11014520701c0c0b1b4640340045079443d030222204a049040c0499400c1d515581100c0207a0360382000304420b82140283d040d44520041007100005150f44c0881c003c41c4580e1204050320320040ca1602040b03d800e00c400401401640502c200d680314200a0740561f400400f07400c00640c0a0ba502d10501c02501c0b5120b0929510750001e1005003042c3c106159821740c00c12 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 448351438 1250 448350188 448350193
    0xc030f13061409180406230604050709050922020d0305070501243003170901230604090c0f03020901090603021503100801090c0e09072103030b0405150a08 68
    0x1205a0008030036090008584041329108400705041001580c0b00b00c11304020307004110703484c011920035101440d030212009802541880e001402c0d41d0b2140c42c1c200292100104555010f880703402c0c11010f0908914002002546900b0541004d40e4400d1340f1781003100d22030341e15903540c2c902c50b207010b90948494409201c5066000d0b482018400302004912098643d14001091610311040d0035448007200240d906502d0081c1010040c00d0641c018941d08a9410342d1100c0b054035155140d0080c221414a9141c541c40705600300c00820120410072180d4001320000d0000c60074440c07036103e01090785610342c0248403000f24100c0c2001182403000c1114010405040200001072454000c10440810111050b1100e4800400591382400088540002d0300c0940c0007007101c20900c0c5028010424180a14001c40c1900c1740000e0300200000f81a0058642c24091808045e07031010528100d030b511018101e00b85a100c8403062060380f958800c3d01e00c103601c10554101030580410a00612808075000200180c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 448352688 1250 448351438 448351447
    0x12030907050613081c12020913060305010606020f0c0f010f0e130c110f0604020603040f050604030c0212030306030d0f090905130303150806131a04110103150302090402060c030f130614 81
    0x1190800300310804400d101b0000341c0d503004010300050080c0c1e0b481d00d540c5421841c21902100b44801503000c2c0d410703a505074003161030105549148503550000c0901e265441071000085840f2541704842c0f0407200324142c01c01074890340c030000c00038035803048140701490007641e1540305140284c1d2049080c80c40c003600c8005400c258401e015043d45845001b40040d015410003c0814100400c58600c50381041d0401e05441e881e003428130f00200315401102c8141c0c41081c46510141c1c2c1580f000c0101ca008240080042c40c01c1e04442d9020b4580c20040700444040c800c059500013042c200e5806410b02c611000302400c18868914038014048039400c8004140742201e800092100141c0024416084080d240145500543ca85403240e04d03070301040d20a41080358254140402c200305d107241d00d81d02481c02d072801d00500250b8411781d941c0458620001c2c0d0700c801c8540106026080c60380040039010011320a681c6080a22040c010a580c494101c0000003e8411420407520760b201c2d170708001444243c0081880c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 448353938 1250 448352688 448352743
    0x40806040611090a080d020105060402091309050309040603030201270c0b181302090f061309090804051c210807050a0915030e0c0901081203090705061308 68
    0x666000030002486a9600c031184409824500151241c1e05002040c4070001d545510a0a442da004000b060000d503080001184580c07515009540b0070b100d000d492070780c0c0522041c040c0409404004019511350004204130400740c0ca80707000781c201850007900042214031503806440b0306207915882c003002064100e11048001101d0384001d90483c0d00b160340322525201014184ca00120451606980c84400300d0b2041004c0200c40d005003130702c80710840b42840702d5100d02c020b01c4003501c1201c1802d2046403c149003403111009550051500c41c0c0980030640c1055280c1c03000c140b20790384c2c1aa03400b51b101e100d4100c800400c104001e11240b803426411441035801c3e0400c002600f4028060f00f410144000400c000d140d8074480c8007003600624007510150711403079842c0340150081180b050503041c14080c1d075440200c2c504207565400c0c12261200010007030159140c01210840c0c20142c1040418092080009140d540c0c40d0081d01c00d10105580b90b5414503e0500081e241511480594030114002c1904154 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 448355188 1250 448353938 448353943
    0x60e06162301021215040b0105041a0c030d020729070f12051006030e01021905031f140901050415061116030807020307061b02040c12020d0e120408 65
    0x205268400020441505501840e000c48100c152221141e503101049210342100d280301198000c0d025409001941400d480503c41611250700c61a0b0101e9070410003000509c1d010751010101c8d10790210038900301110002d00504661209180240b0250040364020130711107100500212031000500b50f9116000001e10844810b400802d4542404085111904843d000b851220001000c0100420103031130921800f4180840600819000a2900c01207902818052080f03e0100b400e111031111140341c04541100d1690005000001442200c80b1030140140101040300103008080d60402400d00400180042c108050b4800d034811800e104200390000284549041600c41da4500140300458500e0304500d40303191844030b0898001640c5001052050741d50241034041c0c42141544c066941d500300c00c64039020714040070341507600f0505c6280c005203060b90206800c07440c141801030031001c5403685402240c00242c40020200e807030b1003001049030410b1108801754200c0c217150321b0500d81030009995 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 448356438 1250 448355188 448355227
    0xc01090e0c0d0e011401030c060c03050913060e0403020309150412032a0f06050109050105010915030f0617010b10050f0313050717191a0a090c0906060e06 68
    0x20074200001900c5071039142c450f040708408540750300c000d121402c145184100310300000d20094401d400302c401302040300d6105a6080d50440d4060f80c401c0e0500300b40004204240c0740b00c1654041c401d80d02d21000900928008038507221310302980145445000d03c1d070510000b2002001c142d2402c039130800c001c0c444030414002020440d0703050301d410080940b80e104189203004400644911107080c0c1101041084440090540031510600701808a40d9941c0043c405a6500307000e0b0b1400306000100601810800000c5e5200204843c070b80403649681e070b22242c104641c3c00b0740151000d040c9042190360702c000240203103103484109039017113281c041c0c0e01d810092843c042c40c40030750000400000410b88510401d50481038103a002410f1300c0c00c0c2c0c1d0341c8010030743d845400709580910900a201c21201c4855034031440104942c0c0002c080341000780c2039412107103d0b18006244240300340e0b039104044089035142a00001401b8003001c00a0300e1400c000c0c0207007600301c0d1400004e108880412805100400003103206 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 448357688 1250 448356438 448356451
    0x305090a02061801122c060405120a051306050d0b090114060c030c030a08160903050a03141b010c030b0a210c0e0a1a030a050703141218030c01090e 65
    0x3442a90366a0004170307411035408400070026030401b4000402e00d8510644400054030071024054000b1301703224543e444100c11030b009401600201e26640e041d49161004180c00310710b9280142c17030017074180b44400c80070983c3c1e00490001600492004110110751107030202401048074160110b40c54a401802d503401d00134109400350740c0105118516820800a0b03030f80b0200c684068a840c1c10f50040c008003601c000b260702003003601402081c5088140101c1015060b00e030040082d1802c144251000d071111a0b01c0d0074042c0c000c000070000805810f40c1700d60042404501e103000810304001c1001e00806941c2000d030f13514403034444948200007864565048803400c807200f010903860b400036400d1081a00d5040d50111240c88400020030010600c16405506a090b000e0968014045208141566401c01090052655000c0e0100f8004912040e50306100020a142261070b45a2490500303405900100c252040c5419001008140351400b40410004840300b880c000d070540c1c2c0307004942d40164030090083c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 448358938 1250 448357688 448357717
    0x10912030e070b160201030605090c091c02030f070810061211060f03040b060915100c050f0a0503070b0603030a0f12090c08150601030c0c03030e1c09060305090a0206 73
    0x1d811909014014007004010b1411500d0b129406600984841402d660040b40003034607141012900e813410210700ea004000803d150b41c240190702c818401c0e5074003410f12007100d00845030b5540d001a6010001d031b01c1c0002020029207011882c096245140c8801c0c00d1700e03425803e0400384d080c0100c1001d26108403682d80c101862900b803901c030701c01203021842000c2048003c100300004000901c8a00319540307025460550345003032144d0700c003000d4030140303a1042ca05560103014a50088642441600007500e0103000344c0980b101d4201070141ca40c54880000011201500042502010b200350b28002e20f40c00070003a03002d10314200d2a2840100140c62041004043c44034140d6402503111043d4014800282c3c49035603c000c540e144e041440e61140300d108170035012210500043c2413540f00f8010070201081c1921f807042044115901a0041c1410f840110180e100c0c3c90b4016440d0308444024540a4815480d6041c0c03440c01c2c40c2004003070703410007002e010b101c0c1d02c558408401611480216000803407444038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 448360188 1250 448358938 448358951
    0x7210504140114070501020301080a0c050301140711010b100c050601050f010f080c0c0a0804090c020a0819020c04110306030f03041d15130501060306090605090a020a02100203070215060301091203 86
    0xf60000b80d0042c44000380c229032011001060703240300060864503031800ba10201855075982d6080600b65581440368042e544603c0700450000c0e8020031404010388403000002c03030380c01d40c80008544d10030011012040001d5010010009014052181902420054616419030794180340040c2885140c3c007518020015510b0000d01c0d80c500c05400e681c0c5100a92044e9541d10b0081e060102164220740100f5206034505854000403a00024081c1182c40d40200b5450914074881d131681c4104a005001c82c05500880d01883c030284e0720f074071a401c0c07182c00000c00a03860f810b1100625107003143c0480d10f100e2961041100307000311300c01940c2c5140c100c00003501c40c05850f074820b426920507001c0e4000880c0c201046c00104505080d65401250603501c00361340c20490308d6510a204010f0350300034461180c03c04a2170b001700d5182105c0340c0007005003141f42e0040302c90304411104000100c1e03100320303807902c0142c0202040528480050f51107030b03000241100203100c104001e03207401c12101406944481850360b142c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 448361438 1250 448360188 448360217
    0x10b0904021002030721110c0a0303112d0f0d140a030b061317030a170402061b060103050d030203090d030507111f0506060703050d020915072105041401 67
    0x100c500031a07010a2682d030903151560140032003006540c01c500400c25100a0b0354681f1f100246d50700840030001d184411462558405031000c04000104444078007458841070207a14066000b01c4e2888240180065025443c40801e41400345813852400f60b900a1205429160341c401b015030b5020b854145110740e12448024241c0041407016022038100c1d45c0032030190301c0d20300a800d4000c12110140341140f080b080320000030340c680c410449a4004541c80d100640588050381d19030684c8148081c6c8002d14084030503224260120080107040f0b225440a401801008410b2015200d00c14145c00c055081d400c00c210f40c25210400343c079000042641e1000080d94241c40303035441007141655002681c021402800814195061854407001500e003008046030103820640200c0d05d8050f01031341c50b03c2c140f00300070050701c003e5448882000d5014103640c81e1000201c00035002040401d105004034500f450002001020700c0c80f201e80c9500c240302d418003041040301c0302c0049d0540440024640446100c02c1207 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 448362688 1250 448361438 448361443
    0x702120d0f032a05090102010c080c0a11010204120503070606052b02030c040e0102070c0e01030f03080a020405032b0314060d02030102070f0302010c090801020c0d0f021e071403010b0904021002 85
    0x5070f03202103090424540d01c044103030010003c1080541c284c2c020311048424040a40703c103501a111091150010441c0d154641d108108155800480c50009440d0688c4d5055201d441001818142d819800000d46c1d041000024071802c00104000d0f10390740003402503207400b01184042440c1500341c4d0201503801c0c20031541e0510801d070203030b60001c0c4100b19444a012107035000b500510411940302c08002d0001c103043d0301c3d00145a0480b544005410340300b04c010799048444c2ca40241001800b140c0900020a60795401d0102a4011440701401e007805841c86c0c40c036500e80e1000200c441c09042c40d040c10f007158040d054171200c2c0d01c440d059821200c95099440400c0c0213115000002d400d00301c00d042100105030b4190088801c448060342c905000d2922071240074200c0c4510480c20f0b04236440300c10500400380c001d600c8039009a4550064840c1030341486030007811458101c504140f83d0b08598003c0c810040300010f24a00310364150f00030004401c81c2c1000c02c400700300141010b84540c048204140a0034800c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 448363938 1250 448362688 448362731
    0x120c05031914040303060f0b04080d0302130308030c070c0e060a05090621030301050307170601120305090603100603050c0f040b07110d03030b1813020f04060b0a02030702120d0f03 79
    0x2081e03181d146501d0f0600b0014000c051360b0140300c01003004403400241400f56002076a003503c00400c068502c10040c0c09040e8000d45c440500c0042142385403000001080710036024602c50203c0312501650340959103404910b43c1881c0c0c01138110181c0b81030500285440e46007403c8150380e03095840803a0b40d12404000703003010350f080c05003000909001c0e240080c2c1d1000840554100c901c15811034503c50b0f02c4074030f00c0400c4803000d00307103a04030742c003000c01005811414200bc284060007800e04601d002d64510100b04554401c4400800440501c0700421000d5410b209803070340600d512000508059015162203501d200b01e229030b0349402c130003150f00fa05101c1801d6404010210007044030340c1520231468090041c1c814030300000e201b00c4210b201c0c540754101140c0803600c01c07880c50114118100c8240e08011006400c2104242c1103030761818045200310511000742940415a0029901c941241c41049104c07040d130300000c19545c001c0740300294041d40042282944240505004c05c220b1b20405591950f0002c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 448365188 1250 448363938 448363961
    0x310f0605031e0f0c090a050601031e051006080106090e060303190801030c0e041a0901141005091e06060a0201090c12060506090c090d03121b120c050319 67
    0x10b500c03061140005002c80c1d03040a060704506642c0f43e103107a5010a41c984040e107115030703000382150001588443d030a9100a0780114141400156000941407240c1c0c009021181041090ba652060102800c80c602c103c10050495180c614074560404400a01c04003481c03040c1e4a04508000200d81240d0b814015501710900b02c042507800350400040003008000c0a200c107556403420705401044040c40940e2880c41035811496210807200c0c03001002e610740c003008001e4a160355980c0705010300742d45d44d01323189801400e448001d034903014101410054400005007604003441e0b60074424241d2450304503074180e41b0100440b002070700d0382d140c2c1c0c1090f4058215540028924600c0c84404101174400c644d540d4007480c090407042107565661814401041000c1e40c40320000b05040c017548141d4074082c1c2a50680510030301d0601002c0c1840c0c1100c609864028500c40c0018590150509a03158481e10b410080e1406c04428413182d0943c201c003405510019140300442c00a0701100a0b040c00e642c0c0102d00da240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 448366438 1250 448365188 448365193
    0x9030f07020d020d12110307030e010503070329030d0516020405100b03010b03150609150d020d0518010b01020d08040f030c050d020c01030e150c03040f02030601060c02310f060503 79
    0x4442e45444007405d08070403004408a0043c1ca4130f40c115000003c25540c0407135140d1070304100c060016005540d2a00000c0074a4105a21080b0321440c5c648404c03035064464040761207000180261008060070807400d01d40c500b00300501401845c000140f03000d09494140e07010703070700000e682d225010881d10716201c5410031940c01d600000000745500c0b241004502c42e030080e25902d81c140ca01a01000010300c12801c01c03075445400300c01400e5560030030b40010b00400004000c01894a14404084800e0315411176848010015a5845007051102070003070b166210802d02c00303040448024880a8103454002d04050490161802000105030042c18035000d115000000c41d000034400f000c00a680da185003140030300182c01c0111955081c000024008030000a4900407062940d504403804c4590300010815140c11010800e084c01680703060007800d01800c580d0b030366032008103090700600a00c144003001fa0070b00000400c03246d4122031004141111a05800100898130503d111402409403003131b50040c96150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 448367688 1250 448366438 448366459
    0xb0403091a0903031e0d060e010906050a080a1e0f0b0709050109061704020d0204060b12010b120c0a02070806010803040906170c190306062c09030f07020d02 69
    0x40d041010481201d203000807031020714510520241890103418111a0141e00900c030a004079a002c50b511000658414661400c1c4400c0c80c00d2402610915404442280301030f100604c0341c4120360044c1303030180070203848400c000391800301400e94940c40300e0005401040101416090010003442d082c035903a8020407061501c6405041030301310420243c41c07520201e500d0400000301303940904000001c50300c568a48124a0b8003101520302c40740402002242d101581d041900010703612403080030b0140c0a401c4400361240c0142031005101001a005082030110500c4076407941141104e1240d801017150a000d42c442e440054140e1400303401e0b0f0841d007250f0041400224180000202500840d04000400e200c1540d62702c82c81070a04900b1002d18072150402561804c00d03051601041c64103801d2810444a2169a919180220354858200c568a420481320242240c0720410b00c0002c0f064807141c00351420704141440c16030342e1080030800e448680b40403e07118295920041d03503410b00b68000d02080600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 448368938 1250 448367688 448367693
    0xa0f03030b130b040b01021614061209070807060c050c010e010302070c0e090d03020309071406040801290619140d02160501150e011e05060d0606030b18010e070504030b04 75
    0x10344401c2510130f02461a00b03544600c29880000c03a1035006032218581a1040d01f800d4081400ca00a149055041007080280c2007010407130f020220310514106000d0550709044c5414541003100a40c0b100d17040010f0a41d669010070303004034564442810900b0110a50309505006a010303004401020380f0340665600c0016141e140010f4151081440ba01500c00444030104150103e002c01e0b82e41303030b0040c4c4c80781e8001e108000c03010075103402e070600091034035080c15a1100010700b0340300c41031980c00b0701d000005401071000c0507190480d103109004032441070603d000303003255280440300e1440f05010807141c1c03030001d0704c0081c5000407a0011440f404c402d55443c07500c3d03802c082440c481581d00300c5582d071800e040b04c0c070000b140360041410b56140c40c0001440d6480d010b440780048601d242c1d000d4800116280002d602e654110040003459624a00819150b00c1c3c0302c0c001d801c941304103010358094004c44c000008000801d4514a045d540c01001c102c099441c7c409044603540100c0d08010f001c45890403c0c44203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 448370188 1250 448368938 448368941
    0x70e0a03020d150b04060f14040209030601030302240103050c0409080c070b040302090109022817090a0b31060204081203040b07090b09100c05030f070b0112050a0f03030b13 76
    0x1c0445040d10a0022444032010f05c4111509441039000300b400c8418140030307074070a502648518010003031001d8280505000003a0074500280e000310050390000a1045180e855045c01084c18524a1000c2da00342d0300d1522180c1e2650350100684d845540d0741e8a03a40200100b807420b940c0913000b807008035080651513041880c82503209003c1640708503000d80000954408500803030f003402000c44101d400f920040f00207090f00281e0800c1c4103090100c400e0f84651281c03a210782c200d20402c1458002c000c804094100f8842865018080d42c51307403820360370616401003003c801100f040d1003200152580341d0303580c03e04500030b0084c1d030407942c9240200384420424000355000380d80240c1c0505c1403007a49440b0180f054070080e0440c400c10300c0107401031210107140d151514040305034108504000586015942d01c00f800e55010810401070168045201c3e014000301d105201d0240240f542103200010041d118a5511101010000d110a2000c554403040500c2500458088080a030043c1401100300500e1070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 448371438 1250 448370188 448370213
    0x10090b041e090c0c0305030709080109060501090b09011505070515070306170a0203060c210103030f0207061107123305070309112103030405060f011a03070e0a03020d 73
    0x10300707105407200c00b00d5a079815100d40c040c126155140d084009140741c1d4151843d03000203010100344124001c00190101c4203003e0f85031918414000003a4660600c0040700443d07030034511090081c00c0c0c0100600110310030403c0d0f41c003004202e007007464031490a46807092900c41d0010015000208490912030b410381c00d41c00c10310955591114448010906010b855070303c140001c000307035140c4d12503408584000030502c020513507150340340425040c0765220005500e01c4007080c3d00440000b90208410700c4015414000302c80079013064640013005560342101c3e15603504403401110000c5900c115407400700b20744012100c09940038000450301b88040185041103100c07a141c9108201800c1c5030000c3c8280c0d01c40c4c4034091045502055503c92841e00300d050102124900c0c8080882e4602450cc034044030b9410405588650305c500001d00944c5001c02407841c103114103a11403505c241c403d007072030040e21240300181d95010035180b078038410b22120f83c00000c401d0f041e15803010f0340103c0709500002c1408403101054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 448372688 1250 448371438 448371479
    0x40906051501081018060801020304030e010e0f0901030b060d1b0323030304061521050c010207060f0507020114030a0207051b011403040609060e03040918080910090b04 74
    0x80070356054600c0150f800603401c60320200c901107844410300101125030325801070b6600c05000003d00649545e4003908a03841560143c01007005620003010340d41c0d00011310f24200109458440c140152407001c907000b6407060000800116519000481e107032640100460f0031b075003055480c1960b12200c004091a0300082c04150790080342c481d203416410511150340c42900300307140015461070f03945442d04002404843c844510105003020002007491440c88074660000c0c0038150a03a0b40d6000d460200e10b0080b8201b2011f0654110401c1001059085400380c001000e03103040c110368031321551004032680703040452103038015040031051107107030400c0307501910050b441f40c41124420800c800d00e4041c04201031881c1c50006244800b40540071442e0400385400c24410000800c6c94a0682d031050207071041c20b002205507600201d010409113606000700041c1d8800c140248202040395112030b0880e01c92120080c2c010000700f451106100e06c14000900104444440320751641d0b120344c0c4109150351003260783c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 448373938 1250 448372688 448372711
    0x6011d07020109030914030f0d0f11010b2b0c03080702010f0c0519060e030a0e0102060109110d111b03030106090617040314040f180c080f06011b0204090605 69
    0x1000140140701e200c5600e501034442c003030841d107819503080301140006030300c47d0140140e98050702c88110802c061115100355482c0d25000140d031200007010505000c81e005841c0c1e040c4944842117440c3c60300c08907a44540380703160001284001c001494000d620500040000d203030b1036400424085440c0207010234a10036070701c038000c0e00403161b0100d0300141d200360b004d03220b600503c0303440102c00b80e00e0103050080c6200341d401060b90803520f48424216088021480041040c01e00e1041d09036906205043c003400807020100031104004000750003d00850055060321b554031101d03840600220780c199025513003102c2084041c0404207410030b07103c3e08288030b80310200f4510800452140e000c1c001f126000d414042000070035a440313441c12200900c140c050309000341001c20011a20401c03483c0c400c0040c00368003203c1100d111600d4001421034070494800c03810041003030180300d22542560300700783e004a001d180808054051195100340c1c00c4940304029409450049580d0401c402600314911400c60100c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 448375188 1250 448373938 448373941
    0x4081905040f080a1a061212040f0807060206040836091501023721030c020a060b060d09110916171302040e03030f0105010e06040605070807020306011d 67
    0x1801c81d60342d10f80342c1d8010007080351003170040580c201c24042030368050320092110040707400441c0e1060038820f034080a0007400388005400e0080860303280000f0000d14049005021492a0401c0251507000140005050150010701080e01d0001e18410403100401d4403103180594100d00c004103100c46041c0216406540010300050503088464810180e551060700502500301c002000d820b5801e2414600032025042c2e11480a000700ea0400c00c82c00b041e1049110295207542003070500619400c94100804050628000001c40c0d503000c00c1d044a51503200f54003048000040c00040c02e140109400500c0040c601886403050041240c0b400810785000e407524001d50300e41c06886041d1175001c400b80004988189840030452a02c0d02015511102d414040d14911400c0d40c00102074030030180b00e8400c03951011080c8046020000d00d603500400c000d080c40f44901d40c001c00845c549004502c22142407080210702d4409001d2180c04841e0f0059004094502075a1100d145900e00031400080d51240341c0d8140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 448376438 1250 448375188 448375199
    0x8030a1d010b010f080c070b0403170603120a0c11040e07030c05030106060c080c330609070815011812033009020103020c0f010b121c03020304081905040f 68
    0x4203142000c40181c2d114885945061801e130b0305d8580280040826203002c0261f2400b081540c03001034002d620075582c40c8045151003c1c00c803081a0094000c1d4843c1c0c000c00820300040001100b00d80d0564024204280c2c0f0304030b64140001001891000d0f0758006081614050201c00c020404406480c8034180c1c0840203520764040c1800c8480170300448011995840720207000c6202d00000c0c280d14403003501110f0041c500052041d03043d0204018801c0f05803904101c0030b505500c14003101d94041c0055881c1340144c640790400070139a41c0d018202d456207489040c4040002d911811a41181c03503500b020440d482d03541d03051054082c0425443c10340003c2c0c203620701c06958401c2c5c20030300c021000900b0482e0560469001c1d22070010184488101e050507420000310308000000e002c1d0b24500c558030000002c05a1001041c408a581000e90314140ca4000c80f1015024103019488040750504a160040c0c0300e80d030720f241c00303400c03485003400d2b4180b041203298221110650010003013050702c80c0051690404c076540c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 448377688 1250 448376438 448376441
    0x51603151d0a030e1c030509120a0b240312030a1503080403021c06051005030106050d03081f122d03050328020d06090b0603061f0302040308030a1d01 66
    0x41c0402540740c00c02002040420b20865511805507030007403000342c03840f41503040500a81d000c1c4600300d0100740e010500742c05529121011416402012024000582e460703603842120990003070402c5180c0c0c0b07840300c40d014000c2048070344811824001d0202e0316104500ba43e00803143e001150450003a50414503500103a4019201d10030807a81c0c0003070120704090850f07003001043c03040520078044200744901003c02043c59802100c0c00703402c0f1820050442d40c2050705142c207440c01600b0050240c1454100034000960016810703a0103038100c00c2c07030351140742031140c03600624029900002082058001800600580502c10001e140712a6240d103103a0794034150810020010804c09000f1407401c0c400a2090f821900c11900c1000d0040c15007544210450360f41012a0004880c0000c1580e946c039003400078010601c60403042d0300084070b8242c1549171040000c0d20b1003a801802d400c0303809032050494820750007501500c000d5540700c00700944a14014907000000d20110a509034991002010590aa10306 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 448378938 1250 448377688 448377731
    0x12060a0f1503020a030b040c170a0b150d0605030102070b0106031407051909050a080705031e06060d0609060f0b1f0806010f1209050703150c020c010c05160315 70
    0x1512080190708414829402908101062001d054807594084599070712446442c030131590030344074035002d44030300e40d045542018003c204c00e142c145400d40c100c0080d569400c042c1c40c110702410605035114106c0702c08001034841603114542540c004182c4604000d41c03100000c1c1600d540d81e4080000162459501c032501d60107440300c00210b1800c00085045003015038030440c1600300c506114103c29a40e8003c20590500c81d84030303a5554000d4041449603240c14002180c0c501c0044807004c0d04030954103221611094082e096a200d0006401c01c042006426004046040e03000002000b00344203090565025101d2a006a407040100e003107981d0648140611821001c2c07941d54a0400340d554000056030f104001360700c2542409005c080201e5208403500a990307042c2d100e680a048030700c3c554030305145500c2000d21004c1c100c5050503042c021259000520303918151003444d00000107810350600758108a0300c4100c5aaa00d00619008018051004655140070b48400000c101103c2e5421624005004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 448380188 1250 448378938 448378949
    0x105010c0201051b100e0106050402090f0108070c080712030b01110606040b150f0414060c03070b040201090503031317300c100507120209030a030c05030c010212060a0f 74
    0x1003204400140d4407690280040303002d681c95078040380940405081c9040302d50816203540d162141c4d04800d40312400e002d4400140b0082c0d401b0f505200f9410300041a808a20340030604100203007001800b41d910411a008245801100090b694401400c0c4070755140d00c01004000428100035202c10254071070b411f0a1311484010700500b9494036083c040002400c2605001d030761102c0300c0941ca00c0b0700041e0b00700034088001c03c1d140003a516841c2480000d29410b100010300e00c64942030044081e800c1003c400c4540c2c80d46d00400307200c81550f0310f10060300c5040b01a0005a014800400c0201c4680c90980c82842652a800c1c40d000301d8801d03030f041c07455440700c548040244180d03c00c59440600204803410050b0001811a11800c2070750031f072403062038040701c81503841e0001d032a4028498640d0700400364420208458005600d004e9640c80429901c440c04100201000b040e0b0041206000c01481582d003224000c1c402556504605850b860510b0000d580c001d12901124000159881c01d00b55280111503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 448381294 1106 448380188 448380197
    0xc10080a0c140d0c02011b0f03060e090a110349090b130e0108010b0f0609210a0606120b090c03060c0c010213031a0c03010501 56
    0xa40320301e8101c0600c8400400c41d2000581e4008690b1682d09884010460302d940510407401800e40d840b28500c0200031382c070700c007141c2030b44451a9030046815039030a02009444e00e100f400441001d4410310102d5221030805c40c00140c2c041c0c95450714240c01420386042c21051504910100459408245901502240c41c0c54140c942c0555800f540e42000541030740d100c800303a001e080e440703040c040c180a0030804200c40102514907044000079280423002e04206503920303012503000c1d24011403620f1050003401d00d04602420b00394251816070a0060030405102510b0903441d1588400d40c98420060244161030720110301c0c54050305006142030b5140030851502c80c1402c6502100182480000307400140381400b10740d4001408a401c140c081d8807040d62580c01001c840e0080c422040200c220407040c40c1c0000c18080c44602c03100d0302e800d552003220042d54559800800d2407109024072070104 = true := by decide +kernel

theorem cover : BRFrame.Cov 448201438 448381294 := by
  have h0 := BRFrame.cov_init 448201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 448201438 ≤ n) (h2 : n < 448381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
