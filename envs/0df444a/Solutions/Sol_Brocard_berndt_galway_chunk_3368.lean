-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3368
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:00.442902+00:00
-- url     : https://prove2.me/submissions/99d3dcc0-442f-47c8-aaa5-f7a1e3fcbe98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 605575539 ≤ n < 605755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 605576789 1250 605575539 605575541
    0xc1803030c060b0f090a090303090204110a111b06070204020d150e060a0e0a05090705131d030403030516050c0402030a0504030806040902100e0a0e1e090a080a1412040510 75
    0x10300803000700e07809000b911150740840c0c001040140990146c1341c0d40d0000c007081601070781c00300b9001c503005842000440c182c07030034202042d80190030b2000855952800340c00c408500044014902110b4080c681c119001d0384280689a0040042268082e800b444500310001c082e10034008142d1042202841d65441c0039400c1d072118401400c1c05000d103c04910601003801d1815009811541030000081d080d5202900c0718104943c81d001240d010b0406420740b003580035190002c065042d003c0411040780b2040484103a0b80703110701d03c0002c022400c00d00c10b201d61031510214004950340110251b03503101f2100340004040380c0c0b0880380d4503c0d4030386c0e82040c0802c1c594800c1e10f040d0311010686c0c1c00c0240003403c0d00001c5044043d00e40b00000c200310752142c40d00540b0340000c050002e28104d0018602b07414030300303040030034401a94078811044801e1000540c0000c3e0000d010060540c028201c989028080b02046405c5038000d00c5105c440c0703004000080310700003980c2d04288500d0045c400351014240e0850588 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 605578039 1250 605576789 605576801
    0x3060b0d0c120204080705010c060b120607120e06180f010213060f03051e1801021c0e030a080106231c05070c0c090b1c0c0e1008100c1803030c06 64
    0x10b81140c3c414403062190090000da40d0090703c07003d00b051000c1c10124a08000a8440b5610760754000242072145e129140c000210390380109202d80f100e000d446803809000c0c003120703042e4911002552166001c6800c2c1c9004a0b2071507100c513080c2c41500c401125051a150030390b40031814122100380424000c11005a0140c0c1418003407000340b400340403604055100c480c9401102c410f44460a2482020910b95491b80c40c20b1610313030300030740c00030b40d21056140045080d10380c030203442203069401c00d00502205040803088420842031038648142507428640112040c480b0501210510030003496607098001c090340c050300d071000d03104145110507a400d142c4202614006002201408403c007088030020743c0c001c0c00d100656000480c00109010304000147d0b680003c40c100280c41d688544081040c854164107010984001d03840c1a4410744030302000c43d0000645d4803e1000c16003150b920100b581080c0d4100c043e130b9400c507107003100301103c40d2402034141884981c0118007040841e00202c0030050540544 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 605579289 1250 605578039 605578067
    0x3030910180201030c050d150e010609120303050601030b0d08190305010b070803041502040b07050613031d0a05120c040f020702011e09030803040f140c010e1003060b0d0c 75
    0x18000d00c08034003900d00d4541d10410009060607140c481c660070079441902900d0040c40c10f450180402c1c1c0c80f03107070200448892030040044c824244d600108100d40900c0036101190607910b1141001e91f0f681d24101d00070000540324070704140d220380b40256560340d03102c10403590310b000714a0300b551045203415034101114494503400c140340c00c2c2001001800c0001050341e4986400c050066aaa80d4038500503c15285003075030103c00030701c0418003003410111240901407040c4500708481c402e44841543c1d4000e09010b0000900040388188944c2c83c80c07111f40d0125252030009419030014503120000501801c640e001c3c006402c3c0e10400080425180c180900e04035801803180440c64101c1c0c40d00002c014485400308039001d030790755681041d42640b14080318001103400000e07c1762641000e01d480c21541c0c810007400d0703c0d041c2a0340c141500c00200418082d582200503151880782410f4401401210225840c01300b0a25981310400102c90014100800000000b500d00140c545411030000e49041003254071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 605580539 1250 605579289 605579291
    0x60307200c010e010c080f0408010b0a0b040e010b0f120f0604060509130311100905064213060312020f0d02030409110d090c0e0c0c030403060e071703030910 69
    0xc4102643c200c009030001203403c0c41c00322002629801c106815102e01058030f0381ea02400900001c40007010b40c04402c07a0901200d50641090f610781803100140940e01401c02c54406960040244902c030600030403c0d5400900c01d40c3c00c10b2050503809903940d800300ea02140c141c104204200341c03131400d4420b040140c0720440708144c403800d0050410f4544030782d003c40102842f49183c2000c042c075000f002800660b814551040c01008428940241c84203c20340703e603010780340405001c0d200d840704e05000850321800c1002001d5900904850f220301e8000b00c160a07900540002d0380c1c038124a0543c09440e010314001c1d03048072000d8074003090007407038940d0920026500b0b03002405080e100300c1d4040100c40881d6104000451008441c1e0701017000d81c45000b44401801d4500b00d4201c04204440003400c04640000c150003180303541e9442102100d100b110190300c0e40d42c10400c010700c0050120b6203c0c070b683d109075600301c070005611591121801038694500c0000755101004014810300d00b003041501c0c144034028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 605581789 1250 605580539 605580553
    0xc03051c05181c0f03030b0604180b011808031c020a0f08100e0703050708063a020a03141204055d030307080415020906030720 56
    0x802006401403491410520980e051030341c0080e035a0725a103c078001d1900c550a40801c1080c5420145800c60040450100e0b0074900741c41650301d00a0240c80841d0304218003081020294283c01e001414007040030f0b4140310340c00d81142c080c68040c500ca00d02901c6810b004558400d65031b10440c0009d07440f540c80116040c0102700c29080680e0107140703103141000e2400d0100e201e448100c2c0c000c202507001c1c1c02040c81100940d0030000e1440c0d05070003641c0142c08503161050300b41c0301d02c0e042c0190001e50019002c0304120700707020000c1051540c520884101000e41081403640381550010b50aa17234107030300903110000c43d180d0140502009103d10444040316900c145d00d040d14100116a200318200c9425246043c0300b00e940c0b88080340c603c03120300c2020714541e0014214000f1107150034804028010401c5d018840050888181e01c00030459001300020744412026685940c2c0305c00c0c00e4442d003034020210035024045031485807100f030b001d540103e0481d107420907540c81e02102d0803544803201d9240705003640041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 605583039 1250 605581789 605581843
    0x15180801061412030f030f060f2d030c0307030606081203240609030a03020616170f091c080a05090303040215163234120c0305 56
    0x3060b00190114103407080b896003101810761509601035028500c12401c0700004002643d15910011481400c0c00c07103204034120b5402c0107028005210100300100c0e2050310003a00c041c140950003071103148500900300c0d840c5004540c0881d0800401b0382c0111040b5481c0c9500703200c0c0000601004000c0e50400085900754984102c5000340300f5011802c3c00180041c00d08424241e8450600f15029030801608503000d5070040c1c60300079900d113021101c48034600c8051a810411520800c2201420414030310740752081e4882410702e8080b1003000d441040c0c5d0b80704441d04224000d019070300710307840b00e56903440e80840e901c2d00e61b10310000d49000400102e80360700100700b000016503410000400704000d4080440e01d4000e251440140c4000492004e41040c0452040448a9244600d00c11900c034007400002200403401901941d60700c6e1080902080340342c00a214848501c19026104c0140c2410a0003240304d80d0341c0c5038050b502803040c44142c503000320a5105000303200302007000a510243e40588443c58101c24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 605584289 1250 605583039 605583059
    0xc0d0503120402040f1d01110906040e28021222062c0f0c0406150c0203160b090a050a0803040302091e070503070e03160501030e071518080106 63
    0x3464080740002866004035081d5265503100304011004641c0410148105016484044080224135031056081c41c9144d5880342c0c25405035240ca000140c106818079007042c10341985414020240101c2118104030080c440f10754144110107042c1c0c4000044e9501015040b0740c201141c01840385008000090705581595500b10241600c01d070411000900c0c400c0001d01c046041e06041c0b8160340c05010031204a29454004c5071030a0703400e1520702181c0814075200b082c0419240c0c2e0b845088010350040418107032880c0507001c81101d0354801029180000d030228100345024000b81c0044801d00c0001c83c0c1c2203810300744050355501510007141c600b402c0ca032400411650324452404001d003e0340810f000700b0361b0203415155494500b01c802da4440110301e0f003c80004c281e038004496490014940b18082d0b072040c1804541c050702c4901c3c000c0c4078225241030400560242149a402d0225403180c10030000d0003181240d0100c1c0b005519980300d15000174150b4005014500d560082d0150742d1400004100080007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 605585539 1250 605584289 605584297
    0x22e05070e010c021327141f0e10021b07050913080304080f03040c05011b080d0209010504090e0d09090501080627061f080114150a15030b040e03031b0c0c061204050c0d0503 76
    0x10143c8086420114032721201e0800794800004048035001040707400c80142a6000d042100080000b02c0b4084c503a82e000700951034030300365900c1015485040c002070201d80503c0c02141c2c806c0c05440114034000b0500024445075000301c0f0103403a6908032410078000d940e40014042c5491080450080600c2c40686a25540d0b11901491814a0f070f0700190a06943e400780f4141c40c010a203c0204000504020301041d8507401908461800600c2c8000042007200b29803181c3c074180c1c0c0e91400288280e56035405020564102d140c1c05942c00700804107002000e40c2d003003002034410102914004030884a82200c84044140d82c0c10810b0240d040c18140610020400d104560005221000e001208100c41c040b0f43c000b01c035a0031051410443c07410101000e50103402402000c40d06540400445289450b00b9440340806e881d090101c3c1e242c2aa1054480c400f0710140070300706155800d844401e4a4100041c0480d4000503608004200340c80410091040034021400c01c0c0c801511994451807550b90340d25101c0c89 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 605586789 1250 605585539 605585593
    0x702030a17130c0308120606070c0308030a0f02070c03140c030a151e2009180c161b2405030403022e05070e010c02132714 54
    0x105000010351091100e440b40900d89800510300005640c50342440103440d44050412000303404000085041810800105c80c0340d250800781045040c0d0642e5542442948040c2c03515081d140c503043c0400c0501c0b25071006204d118441c0c5800c3ca01d49255192026403d00d500300a0f80d000e03040000440c040d40c0340843c0443c400d0340e1140b0107410080c0d4801061008114928282645589800a0707044419007a8800c0b00c151100919034901100030003042c40e182d00c1a9032980b60013008610001886130510100035403c03120a29525081c101d002d5558959502542d500f03441c581082c01c000000c001d0f480340100040c2c00356080760070564285810500004601d00a1207080000c0007000509061003404028103c03413001085001402240041c0ea00d0611891001920249844003282c001030240c400d4148501d41a110141e0100c1c00e0f4003042840c42c81006441150703a22800305440400030f031a596000c140c0050607c014128080c140008030029046102e140b9900010541e140005c03110701a2110350 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 605588039 1250 605586789 605586827
    0x10b1602030f030712091a0d1505060a030603021c020d150f05010308030708100608010501030c0e0a0f03050601080a020d061d0d0201020301141507110105040f0b120702030a 76
    0x98408285003001040c440051400041450410404007115143c0c1c10501d030750705c2d00c1c00b03e030f124080e445048801c400d80204800d41000300c442013960541004c0030f8200e20307502c2da5003d01d58500204505a120300c44000010341da524060046181403020302042d07010429003248602c2169020414070851500c3c05880810044105641201c0b03a0f080024560b030a48014803c65030750380780c0350340d29810a46421000c180d0540004a240c0251120701c0c081743c0003a500c0d050540d1a140040d00140701c003602d10400c000b07403607000c41034548600c4034002c02450301d100208415444c5080a50918006801c101000d070440241c040150380c922404c28105908a80c00264800421030b03291440d156904058586005a01340792443c5074040d0301450480d221060b007e120800e00500b0010840860b9003000c03450103040c01520049486441c400d4041001030504610b081c2d00c962500903804115400306510f40c000286031203003403614410b00c0c3d401c402d450000b9810012510000382811482c06000003450b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 605589289 1250 605588039 605588077
    0x80708070b1c0c050304060e0a0c0b031003051f060e010b09060904230403030c020d050706021806040906080706090b0d05070203041805100f08060a0203090c040606020a060b09010b 79
    0x1106080c01c0002450312642c400c00c88910340300401303010781c3c208803000d6910b00d150422107242088003082500500b540000903c07105800d00038403180b50340000d0b092803450700c1560b00110000b01c04002505584001c00f48500700d00d10415045400c0c0c4001e034110344c0b01c081c0080c00406c00c500c00c1c1d4094440d404002c4a80684520001d400701e0003e103801501407130202c408240600308402c0c5540410b0095020366014000500d40b150180d0340e5140386241080020400c00031100881c0013130b4042d01107222b000c10703d540405524800100c0f542c100303421501e402a601d500030804104104866001804a410a68561450b0a0401c1702034001c5041303149a043d107407800208010b02c00e2045401600d030420070f80550446820030000140006c0720201d40341200c0c07400c04035030b412058039540102c4140d800181801d40d0f0301082c0d500a50005004060369203e80403003941695254000d29002e80388542c003d102d0701859080c55000d650003507031054042c4035103400500075240110111514881d02403141401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 605590539 1250 605589289 605589307
    0x61e0513090216150504060e0304080c0616020a03030906081608041103011e0b030c1c02010507110d060f0c08090706140d0207050f25051e04140a06080708070b 70
    0x509048032008000c4407140b203844e060750307081e41e004a0040e4080c000c01c12a001e16810b0040d9644280c1c011040c0b01d602107051140355141113030040002c560102c016215442a90340071404910b06a0021804a41d0400382840707503c0c0e02c01c0340181d20682c103808565540350440006030030440701510103080c0701c0c64480b0b140c0e50368909400c541c03c41c10701d000071b0b80616401260203000400721040d523648170340240c0350088406d20f0300031004429122280d4101014400a070b005480303a620076141100d180000054071519030b41c80303120340882c10303016680100d103501b0f031103007148100c0c0c01d0003158200b40029503080c090303a15400103410b001c5c1c8016062140810036214804840ca00488540800090001491408210012480c8081c1107410000c0350701d500c00ea0600f03030101c0c1844154184858185040400c4580340204522109503104100003a406d01ca110104094415001601125418100a1040201d01445a54024803004020f4441c581c20001607075125444ea1203180c49402c0082a4200d07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 605591789 1250 605590539 605590567
    0x1050d03050c0a050f010204091103100e1305060106030b0405090a0f02060a02150114010e03030304080702100e040507020109020916021c1b030c061116141006061e05130902 76
    0x2488a4200e000c89034120300c20024039007c0d40c040c0c0108a0b4072806c010300340468903110815a0b0040010704102c11005007862042c0b1030304540100b0280c1e00407030f80d9030000c020410a001c040d01810b690746d00030031600180000e101c25524050101ca100d9030203280c4590204101c41c1100c0d00d402d034112052a920807682604034074240d20002078070090140d1000000e00140c10a280240d030950a88030b900201d42110100b588074002180c001d0190300c0204086001464005c100c010815490f00340302c100714450340049000c45404540d11000340c0c5d0b40c1c040010135454404005a40450045869060380d1003420000351a12441e20403007440c24690550000700c0b03401101c942c42c3c2e285007a10303458028001e50a00800345188928154ac03941c8c40e103422420038030030380c1c0122a440500105d02044105c0d0702d9a48030b01c0826102c3e8030004500030112290064400d502854004020f1030f80c51080c0000c19022020744001070b032181c502800420040d08191014408614084501243c00180c03105a04d1031156 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 605593039 1250 605591789 605591803
    0x27061706031e0f0f01020a1d01090906170f0606100810050d0b0a06141005090a0f0915080307020a050d0f290a110d09021305040b06100801050d03050c 66
    0x100041080c060b001c10b00b00e0002a1403c008240208460000d05012031031802c0740300e406524000660140c5a201030341a1980c00d0b15080030040c502000200e903079514243c1201c04680000704111086c00300032140307500420a442d84d1040358405030600b8105000010816501c441c1c0d8003050200d042c00260075001c500c59000e0003032402803c0365540070040e250a60030510201c400c560410b281c68030100c0c2c0342d1041454082400b00c090300c45e40e0b190424180988007604071000b41640009001e0f40800c03944003480820000b45034654010031404080d45040036902c145402441c45940244400000350762460804400c89100f9035900042c0c1c0c00301d040402c8909500031004d01900400760182d504581a0803000c001103a0705c0d00200310640300d80b080b4005444c1032044140c007049041c0058043c103212a4458400203200501020745400d041015000392002220182c600940501c01c0141c01d051010744103203800d0b41c40c900f00c1c60740d40c1090b000a860544400d8068108000440c404816810810080b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 605594289 1250 605593039 605593063
    0x11010906060305030a1716053912120a02072a03020916120b03010f0911190b0d1a0402071b090603050c040f020909072706170603 57
    0x1401003070b40781d0910b2a5250712034800803001400070000207101c450b880011501548000030400f1521180c00c0e812120750300708050400295031461041010900c0c5040c81c142002440d01d0482c580c000d001c0709441c240050180080d9040d00100581c0701903000e101c1c145503201007840c10058485580303041c2500c50221082c9102d0038410004c90180d602503400700c80c2d01c2180e100326003d180035078800241c000402200c0004a010642c0800d205414000d160010ba8880c0703400381c000540100c080d0340034815600e803150280d45101c0042005a500c2c1001451074502c0507500c0308c40481c2c84c1c0f034066100d14a210344101d100300b00d503448000c005040c00c450120081071100030410364440f8139900b818040812030103002c0315051014100042c0100d094080c0d030080740c2d008009003d42041e604107000260051201c1da0451913400c01c620310240d5596800640140310707980e60780d1322054030000c1c1031031401454880e0803034407808031908000d4a6070084081480340b800a0040c0c003aa25490b020078039100d810056 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 605595539 1250 605594289 605594291
    0xf0307120323041101050711100e03032703030c1005040309170f1506181b04030308010602010b0103060b0f0703030b120c0f0f010c02120a080301120201270611010906 73
    0x31030b2001c1c09280d50030b80564000c5040c000b401d100040150703203a2044280041c0f8540e009400d03000c162074800c542c45001c0404e428104d5120008100203411540200281040c5119880800203150b800324028901118250000d515103d151041ca80d541d0310111a00b1444a48a400107001c0601c21172042c40208102843c507000035501c069503c0e2240070000381e403d468450740b00d0b00c0c00035407000d20032680220006010001c0c00140e03010321110f41d150092403100d54003115034442c0040502e800c020001907009640f091115410220000e0039100700094641c1054141642848580003034011079500c1c4500c500e5a40c0e9a498a00e4150098150400c00a600030b85a1b5441002c0c0400414400300e03e020844200718107407004d904001d80315015030603c500003484104148010b0410b81340c52040100c08a04540d5045503943d1080d20030780c000d030003034003600f4500c2c0c807240d0855030454612440c51454541f400f09001805102e4000000329104000400107084101e070100380d020360107040b80c641c200d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 605596789 1250 605595539 605595581
    0xc050d0506162304051c11130612031e050406140904091a06040b0a03050c090403021005011d0105011706040203310b060d050a0213020c0f1606020f03071203 69
    0x242d00f114603001445014021690755604580d04400b40303840c0d505031b0394812402c1e000c4045030710900c81c0780300a1001c8155031554030b280c0801c070310104007902e94445100f5a036828032040503541440c0d98418110b01e400501c54280310901c0450303000b2980c00c0c401000f0301042c6460399035040008020b0b140c03424000c0d100000c000c140050100501e043c0328071421066406220072440c10b0203021200c00203100107403580e0051101011186009a042e80e0002c2c041e10440f14081d90215a15048440c207030720000b03d6050011405020b052414000790040c4406d08242c0354150b00340c02e4070401c0e0b080c0101210311450f0300100181350044c0c04405403e810640c02440c07021802203008010303004240c148141c90310711184000420a203040740482050650101c00713084032181660911803410380c07403c1d018111a40901c030600d12004200100240700c10420001c0040318400c07007401001d00c0c840c1c3c00030021034100e124000804034001040300e8407160b11803030700504840c544008500400941060700480c1c11090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 605598039 1250 605596789 605596847
    0xb07020703030315060509060309120d05060a0614070209060310061d150a120204110f0a0305162001020d15060f080618100e0a090c050d050616 63
    0x1000d1040d644291010030512254407620402e0003060f22806000070000c05c090040c5081040c051600150a28125003551000100000c002d070805800112010341d18020000c070b61601700b507104008c240a092141d81c8502001306805a88580d00010f80601c14400204909881c02c1084019105201000700103568135074442d170500e0200500008030840d84200403801c003403410341e107924102c08020f000c0311680e80340c070901c224010000007040c1c1e07120341d6031520040f414400f0300c000c003207e1410325840c40d0703501848030000d412204003400c40c02d0340c20380300182016003940004016601c802c0220380f6484c000665912103000e84030f40d010f078289690078000450400103c0075001341c1940c00d03070340300c81c5102500c0d460100c0780c20a0450340b2950000703000305142c2030000e86c04807441e0002030382e104000e501ca49400b40b59090002c00c0c1c41c0c1c40078855481ca00301040c00174000e00140030705422a8419504501529500d81d00c14000e01060f84c100e0301400541c200d00d003d8894070112140180807882002080303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 605599289 1250 605598039 605598043
    0x1150e1201060e0105120303040b07090305010c0c0623071202070c06030b10140301060c11090f102327071e0e0307090e01200403170705060408090d0b0702 68
    0xf881051100001c0d84004582481d209900401b070140000055085035602e0711061808140a4804c000f44000c01001101166080c0541461011607407110030310f006003450208101c444121341172007030741d01c0350005480c0c801440803419000009454442d5250b5a00056030303009100302a801015100c0c9150b0008130160150450361414004a92001c0c1003000c0c24415034840b0042581c0001d0000c00b04018869280540f031200349550095081c0e9a00701011004550f0b4402c00341c4100503101303151010400000001d55410020b4010030b640742006243d1ba080540312241800b11042c1f15030962590105900803081d256100b5003a4040d014102d400c000340e01601822004a00c0011020500780c62140b10b800b41c0e04040b04004040c0c0105002850701480c4c10040100c0944042555280c61807003200d102c0c0a980c046050401d05030042d501e500c0d51421501e400d10404142001c81d0082c0f0208c00480c03000302e68a40c0c81600b01e8401e541e6030040c44000303031544040010041031078130302c041400746050740 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 605600539 1250 605599289 605599301
    0x110f1207031e08030106180806040605060a0909030e06072f03011802090424020a0e032b03090f0f080a02060a0b031908090607240501030b01150e1201 66
    0x2420108103001c009100b1906011403009020b40000e00c108010000d4034811951900718011032907150b81c2d080d4840c1039481c1044001d4a05541e80c1361120240b011903d494001a401802410703010046141c030b550300030b005607040003083c1c0d1080b6000704102003805045100543e0b403445040d055001c0c03044030400204039001c440c075807c0c000d618002060030b401d00740320004c0c03500b01d4004180f070b6816940c41c1d03550b404506982e004020784030410300f03174410b0340785890014001d0055143c48a101005800041c1132601ca903d412030b811300c1d03c409034034031215211039008a401100b91725002c110101c650806480b54813103000000d10700d844056221090103502c5018080c5e017035159080c1c8400d0f0b1034010351601038407242100c69625400c601c030a0604c0c6030b00d08019507031681c407425001e41000000c0c80020269000300d44159045000480481030741000c80891070704a07102c8000c10070055065440b10400c0b0740050081b40000d100355244110410f00508540c0c29124000381030028810b11500c6142c082d00c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 605601789 1250 605600539 605600543
    0x80c010b030d181e0b0702030f07060c030e03060f010b03090f161d01061409010c050d0503041401020f0a03020c0a0204050103060209030f03180420040306051e04050703110f120703 79
    0x2020343c070108200c0303800200c444840f0030644400d00c50a0425070a0380c001d9101e4142203926106001c804900e513034080c425803004150a13220000c1a400c0f904000d0881c1403c0b00400344603070440c0d8104001c1940509580d41980c5c2c2508495880c0e82c0d4010341c5070b1401400d261440709900c00d500c000c2c002412801000410755404120072140305680c51900b1460600038002c02000c0350426920303403c00c0708980003030f2000607014500841400401c0c0c503624203080325401900006100001000b090224103c03800040708403507802140342040c1141607062034000e0741c00c00d204141d0000b40c03101d21900200030001c44d48d50010400c000550f924603100b4001d500c07040c0541e001c2d00400060b2005030b600402595180e00c0b813a650415600000b03000c200003406a01d00002c15200711034030f100c40c90741f604006003000d0f40c45420001072a05008020360000b00c1020a40501050000100b000241c008207801c801c43e6803012500041300f0710b540010301003154600328550051510400d216901e03400090701000c4078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 605603039 1250 605601789 605601827
    0xe0303071e0c031211040f0602060603070602070e0a0f02030723161b15030b0f100f08040501021c14130c03140a1212060803090d080c010b030d 63
    0x40403610710a040554110446004070302102c0040300428040c201042c0c40d84880800020300c1e44507081c1c00b510582054011250b0310446170000c1c40400c0d01000a140c102c00110f008040c80c40c40d040307000350717502518080e1500c0e104d04c0c0e42c04114405480c0d007020604640380303002503490b480c044000410441107420148400c06210b490f18007040c00c1e82c011107010540c0e05a42960a60f000c0d154100305250f25100c0d440b440100e6200052003015002c1c0480c4002e0700d82d9008035911800f60100005080c8100d403491081e04101c07249603146030003441c125030403403070b13030500910651f56420810b0081c00303805912400d0125070710b650120340c2c065500c1444041c2552544a02c141c54000b20b040c08240d01010050410a140700705001242c1c0d40505c40c0c112040741412500740e04100c0d5141d48110342440d561001090011a01c250f020b0480e00070b40c0041e10b2840c0003181883e01d80000605828007514001c0c001920006407c0c41c400001c0d0004285020040c00b144e440d11003a0000901c00c503a0cc1443c000b1035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 605604289 1250 605603039 605603057
    0x12040b01050126040f060507270b03070810080f070e0a0c3606030f18151808040f030309060c030504050915090c04060909091e02060c010e030307 64
    0x1541c0525440040c2d12104030001d9400040e003c2c5142401c04013800c03c0d205082c0c0100c00d040003642c6802000c0c4185066035840020404090415420781400e640541d04a03035040307028030903854040f050700e9000000d45440d5600342c03030350081c56039600c1803500284400e0103070305644c030003441001601740b04480541001049035510300c0c04090403650f0904103030b0001042c200c80e42c48000c10405032202c00b070305421060080c1443c1502d00c08060704a690084000c01d840e954400c865290a1082c0d41224140c00004044d03105250303074804022880d545030304007650340c44a40e10360003159207203000401640210f0300d698594481910f42d66442240c03000706c00049c0c0100c404a4124810381d02c415025a0540340c02d401c0504050030001e002d44002d0041c05020000c07283c100003540c0307490304c15002e20600d80042c1c4c0d03514101540209940401d4101c8004681860014000192006e40800c202840c3d804a0b00780c041541c400546940b06441c0b5141c07640d1f0030001c03042455203011000314000c00c25919501d90b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 605605539 1250 605604289 605604299
    0x121d030109020d020907020f0d0e0418020306040b19090812012403200706090209240607110d0b0604050f0603060f06040f0c05040504112d0d0212040b01 67
    0x2600c0300800020340002121400b83c0c0107080031841c154200c01180140c0da049011641d1042c03078442401c8148000810f0139080103110f042900c50783c448070420000d42890848a41c000c241d8450002d40003c0c441a84007002900305081c401400a008032401c0051000d034560341001102a00100a06180102d0000001501425240c1140d03503001181e800341c50040da04c140150001c1c54103480702080410680c165005030101c020050081d184502000140110140140304c0105401041d00100a00741440310f00b016440211804006c02c040f1041c60303880019107000c1007a440c80c1400d20340c1200c200b003005410004141305181c03240000307680400140c2c0e1001244007680700252281d0fa01500260b000c110003865005580ba4400e4000e4801f1456070312041286d007c4a082c140050006040400e040c003091405000e089801e101070241e607400c0030000d40c000c200354a005160405410043d0403c022920811000da50780c1c0300751901c0454564001c2a074181039401d0071101101d1043c1840004a5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 605606789 1250 605605539 605605541
    0x105010f0908250506131827380912040311060c011d0c01021b0f0301060312090e011a09010c030e041503030e01110601090e0c12150c09060d0203070309121d0301 71
    0x70420310a05051000b20001b813407848e2108580040e180507882100e0803051884a403c43c03c031403406120100d55030401e0710f501c2c0603030000242c0320114580100c108900d00a041e90181d171309a0760010280c048146c103103800110a445010140744140d4240810342400078031a1902c4444881c1c058191200c1c80c41c503000480c0c540440031668010a00c41103003e1519040006190300e03100009800029403503100d0700c403540b802d00c0ca540700e03100154032a02e044c0202840050b4090040500d40003070000d01088c900ba40515002d44a07103a8100040c0c10300710003c0c144601c1541203080d030041d1080100d0100d56050245c891400d0000740c010a10880d880007665100f501190000c3c0111030141c002031342001c50100c003404840c40954502d00c50300b01d20200300d943d1f40e40340408080280006045440b400501e00c501500014402c405000d41441410201c0d00c6010490b840801714010041e900c3e41e0750f03a42134000b014100e1300034001d404c204841c1a1003642003071030b8010f02500552a08414202041014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 605608039 1250 605606789 605606801
    0x10f02070308030f06180a0506280303230c01060f060518120f030d020d0c05040803071e080d0507021e070513090210080105010f09082505061318 64
    0x2c00c0d0441c10000108828040c60308150481401020450a841014058204002d00f80c078100e09a944d61020f100c00c3d850000d03850014203910840192002c1101d0452201051081c807002d0280301108009501d400d001d1034500311446a0244c815854052403014a4003d010301d00892400c001c0381000451003d006e68143d071000c40d40e50420000948210080c4101000c0c6150071145601c10302c0d048240304007051001d0070700d08262100c0181c44280c1411024250b4002e929000305020080100344407107000407048941e420380046400b03e00713140b40500c0c0c80c0344c0d060350302c000f804544011810320b00348010358116038016021603003110070780101502043d40c0248601e2582105900c02c0d842007215041036a5a408120001100040d05004603008140f03111465446280010071210050041350f80004038418803048030300d04980c2d580d00b00254950b035094064040104001c41d4090804105041d545030005000040c00312030301d814a01516510003c918040c002146800381e0780827055080030b100759 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 605609289 1250 605608039 605608043
    0x30d030209030c041104050a060c051e030a030515150a031104080a030c0503090d08030106030e0105040b010311130204080c120a030206040215131202030606010e091906030c0b030402010f020703 85
    0x83c0c84640280750802000700750b8019034400c0d00005101c00900c96461110710300007403441f5144c1096240b101e02d082d604145640b000c3c01459001340192441c0301b0301c004140d400c84655410001180d40b030342002c48200400005200d540100001d0303400481e8010080500043c00c02c40d20180710014a0810955040c0650302400207503074048094800401d01c03480d80002c6030790140041d42d10f4480d521021603243d8a40f00c03000c3da642c07000007004001c050391511a01c140c0d0b10071030000b004941404c0d91030300d009010600c00a0035040d40034205074100d94903010030842005840404654a0f1303030340c812258032000d01c0720f003061154441c68840c01c0c0f107040100d90380c008558560f000d130410f0350710796003040f011517101804c0002000080c010090850814841c82d0042d20107664a201e80c0da500340304140c504040206107504200000025001d60744440704040d800400d201c189084136036454420074010040f560000d004d0410401c4002102e9404000450080e4001c1c0d8a030036521102d0072083e43d45900754400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 605610539 1250 605609289 605609293
    0x120803190614120a050c061804020a020d021501030308060d111206010f0b19030c0521011511060f060409023a0b0106080a1b0f080604061a1605070e0105030d03020903 73
    0x1001d0041e00d0608000c1954055003003800c2344a43d8020049000c9030803140341200540c0c41080044201c0d5010800d1003a1402282c01c5500c8135810743e80c0050040030302800c420300400f14034524000704052451200421400688030403d4020b0030b965003643e9080a200e42e42c42200704450200f0345038203410889032089104c00031016540700c400c00442c01040c6610204042280c1444010f142458244108000181c6d03c00c0001a5504101c20b424500328401480b00c280302202c03006050010001c10640d6000c401c5201d02141c6584074400b003000341130a1176000f23501075900000468000ca82e01d1124485d040940009400c00a107401c001c0005810741c03002410242e8044010400e040c030541100f40d2041500d94045200010402065400d4810441c2400400d0415140380051a480281c00e584094201d03024040286032a60038900c03204109946019154000b80d076510010286009403141036104003120240c2d561041141030201c820301a0500c80e000320010f2002d034a20034000e4030000c400081c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 605611789 1250 605610539 605610553
    0x19030809060306040908070c08010c0504050d06110f04081605010e0117040f12080a0c09050f0103051503030307020616020c5508010204120803190614120a05 69
    0x20044141c00080c003d960250301c4410810014a90102800e00148a0706802d050a400d0501c1e0320f00b0741e00c031558007404101052004200e141d0710508100101c0e034110400003800200082841240d12803000e0120305101c0006000803540c07000103c40c030b60754511011142c0302c25207610044400340000b03078020703000412104c13140212004d05003015411038400c002d1001e80d24925038a070180c04100000a6010680200403c40d83c4a400d005a2481d203401d403500e01d408a04050000359209605400a030406079940d0018041d40d03644140c40d4004040203003240d8680c41e0040d0001e603221000c071005583e81c401d007c440300141c1c0c0001140d1600d408020984a1400d640c0700d848203c54500303810b00c919107095155503080040c69622080c4001001c40c000e00804003001c4618000340307555034098040f0360300c10041040755180c80401001d080d50f0211610f596500c8494000c000d141809580701e010324900000000c5040d05000160340d9543c054070206015120401c1c21a100c14641801404540002c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 605613039 1250 605611789 605611807
    0x1f0f111603110c0d170415030608010e0a0503030106110705030304030615060806030c1302090405100518010f0b0306030a06060b040311060a0807030c110f0c090108071206151d0402190308 82
    0x41e130917200d03002c0c0701e4420a0504d940c40c0415030301d9940e103442c990046690b410080c40303601401c0c02012103e01c1018010640205a40d5400360380b403105200d0307501080340c508003007205035005100040003004003c00300c3e922251a8108440200b015418040c00b0b407018080009036507006249451250030010041c219500f201011301c0240c0208200110819034200f00390150742e034a901c00e41d40102d0080c02440e0b2000d00700b0050108282c44080145080c022000041020700e14001802050740c1d05407010903181c2e202d071404203242c503661610081140703042c550085101c000d2907000d8000c881c01403011042040e03030002441200e12a850655001035600d000248000c0c3c003980040804e0f072140d00d040852900c0b0b01c0f4140b4180000007980d0320541d08846020706852502501c030502500540c000790a00c28909050418891140038000306555110008030b10150003940c0000014002c0d4004081031001c00d8800c132001001c1120100d200700740701d60900389003c6000c040030040c0c91b03100c0300d0549004041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 605614289 1250 605613039 605613053
    0x6100b0403080a030902130509010b030a05060a0c020a0c030506060a0f0b07030c031b0b0103020f0406050108040f0213020a05031b0c100513050a150b031f0f111603110c0d 75
    0x403c0c0c80703c00e0603160041c00b030041e00c0d0381c00d03c9514070500036000591414445482c50960b103c011806210380c4c0181c030280d0100b000802d55030340001103080002404010203c0c140e040c00d2034000301910415400c40000f0038170a01040310340c480c0e0300c221040c641e0951102883c50b9054000d00403102c0612040c0102c40019000d00000c084c10b0b80039051502c0f140f00c038481100040400c001c41150025900c01c010801c600309006400c800303420445041c0040390034500002e0030b100005001900005891441c5015500d0704000c0036244440c1c1001959260400203000e080c070b41c01620580011080710000180103c600401e41c1c00324420302004d000414483c0d01c0c100080d0801500c0080e0400410b000800012000c21039602100d00c10015580503802039601041240c59010f0180d00030380114000144820410540e50342c0d00360700d110001100c0ca2202c444800034484038000c030200c0f45002568010b8104c0c0307141c4030f180c80b501c0ba5852722035084500000302d49860300035810f05c1d00074540031000c80004a01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 605615539 1250 605614289 605614297
    0x10e04031b0215040501080609060f01052113030e151e0415031409120a0c0303021207050915040806010303050a050c030a090518071d0d080705010e06100b040308 71
    0x844514101c0040803600020121a0120703800128140001002c01035540c100d02480e6011314101c50301c2ca5545031450200b01c41e02c040c00304017410410006001d401440c0e250001032051000c1140861541c40c10448000d0303000540b020a03408070396100c0042c402841c040c0d0340c55034a10010500c0e10f0034141c12084954140190f903e4804110340c0038003000c5400c0f100561480f0080d00561350115a0030f51802c03c45401030809020b6056070341140a01d8004104800300715803051401c2e181054071384090381800c0b40280525505841031280007420f0002c40d0f03900c40e028141d0b000040b02c019a24109084400509110740e11842081e9001340300100040790051014080c40c6150781409450407440076025410769101145000101d41c0a80040c0054100181240500182e801f064025420079400c0640781841800310342c1c00d00f11800c0301c21a02c580754020b401070050342c000786550316180c081ca041c1d40a412101c002ca4840d1181030700240148203419080d10444142c4031450717141c24250344510a882e44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 605616789 1250 605615539 605615567
    0x91503150415180204060801082803090b12180114130c1a130b04051305042609040c0f0f12021e0703020f07051507021f05040801060e010e0403 63
    0x9801040000c0c8140900b0080001810f20000141c1c0e50341861809004494188c00c20340c05c03039203e0300d2528220100050300709480301010244102010261a00300c44428098008240a01d00030448100007425400c226011714550545601000000113200303003264450744818901c0c200d101c000c01e48000c42407242c2c1540a01859154542c0c0f0389603810511100d403050007400b11101c00156480c0c6100310f6621070005030008910580c80d0900c0c000000c1c5c2410300041880c03807110b5840011608120040b1115400741c00ca0b1030100820044c4c0d0341c0d4401240c1c0044410302c1c01141007010403d00d45108032080c0f409400f160f1200d00702c00e5500c0508079000c0320405511a10a90b01300f00744c1e020008026602e8003000c0360780560a650722181e24000b0b0038803808450003141544903010500050b0b0700c000f800180c115118030401c1d1140c3e1140001001c4100416a00041300556440c51101c540c0c450011b009692002000740312982d511184025141824420b54085030381040201d00000d10444010103522 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 605618039 1250 605616789 605616821
    0x603050d1403280e01062301030203010614090d02040f02072619030204080a11030114150609040b04020f030105120a030c030c03020a050601230307050a0e040203031b01020915031504 80
    0x10244c125460840c1d0064003d815440c1820300d000850790200c00411246000c207280a40c110b5140003801b13001c40c1da030034043d031440e418007040285213030f00c0c0c4008075010381d0b070000d0081c8008600c0b088107034020350018006a41c4c1041210561900c140c00001d041e50fc0300786440a03070701d440244c48060001c03100a201d010105602003000003500c3c00100101881d19000e510280c01c1c0340f104004050031120b118a076820503000c000d00304490300c10383c0003003000108000c0c2e406030764490307440c00010010701c69401e5640d07000b0f1010400b1400e480c2058003450596105690b0345d10403820142c0b00540c0d9071ba41c0f50000b000a66003a6444001071701c148030200c1c20602c02d00440b4910610343d5141030800000342c0220489029a82017915000040f24505034444019405056421f040c0300c0414020b8442d030148580480d142004281151810402c0f40c1c403c0c0c01040d0300449460140c030456000c1d50080428620075006c1c800007518060300101260f0040121803002c048642042c01480098150210180051 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 605619289 1250 605618039 605618051
    0x29062806091802390f0705040b191e03050f060603210d0209040b06070f0201080a0e03040b1e041d37020409020a090815090303070315090603050d140328 67
    0x64204005c920024040c0c2000741007014102000c1c80125007005a116203d80d42c0040c8000c100d54449500d50159403400b04543c12160284180c000344854030740c0001e103540b103004a687c602c40c0003c6080c0380110012415100422462203402e5101d5080c4841e800e110141041140381c442800e80c018206070300040c00c0481c0c22040c10000420b9a0014501a1460100182c26070115039201c0c9600c1d600404595007046a043c00624030b42e81c1e0700070341c0201864503030001080386c02e030880032139a60740300d20600441d82e640d00d88548640d0a01d441c260001c0d00107412180128600b0b01c0564003080340fa401801c2c0b01100c503c070050b100714502030b440c3d0b1815841c503401c100200c0d040441340001c0c106448540c8401f03041714070f03100b039440c80c0111407200a849070359007d0078050400300120403a504100c4c64074020030150490150200000c0199000710f59883c6081030000c108440443c040640d0805030312080144e4094501e64070080c841100e021840f0318070081c9081d1070043c0740001c0a03032800581300000710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 605620539 1250 605619289 605619397
    0x402130507030c12050c0d1a0a031b0b0406140d090b0a0b0310091e0c05130c0206090f10020f0d050406060329062806091802 55
    0x1150001d440d03441c0069103441140c180160018254840b102c2e04072420012860302020140e04c5010304003210b08519150807814500c00403404020200c9080108403a48455032894400c3c1f42003110082d00405210903080080c0840540c800d5804503100c5071600c1015944505000240344d0150016403195a9074030301303100100781611111b51142ca0000f000143c400481d004251418a04460b110b5010703085c003005e90002902261680601c846131203150002440d1031030103da038200982c0129400c00345000303070390b04031411a8025080080c1c00b0f40940380252030b00705150b07445451880038020a0361103005606080d60315a80100110882e400b1224102030440d1000020b40d2001d0b2b5082d1000358a0700410702c01e1142d03800491401c4030b400c00c0c04002114100032441035400c0b0051000e40300381c40d508000036144540005c8005a146031901031001035484220140c4901058021a00c2d1003048038290084c900c500c1c400c45824024100e1030703c003082d0590f00d6801c541c60404009800000e0202801c01c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 605621789 1250 605620539 605620541
    0x1e021f02151806100612110a0c05280204050106082806050415050f09011a030703090602130603061d04061a12070302011b080a030903020319021606030509060f040213 73
    0x40114413095402e80700c207180210080211350614280d904152a01c004001d00540b03c0085a00d20191030811072951030a1341040750629502180403500100e65030b107106081501c4140e1402110b00c00c41c0c1c100302a0340c0ba05d1040740c0c440e1b0b0840d4128440c8060100e095440745031105c0c0a00801101e101c041074054684011030180d40070035201c026109180c280a1145141a0030321441a0009540c40340c0158900001d0054032422981c002c1340f880da000011441c440d1194120b8210b5130f8100d0400d540d54401c40401c2d800c000d00d10320074840000e10741a804141c0944002400900e0205000003c1c0355498a86401d402003401c0c0d401c08580381c0c1130821001c0c407911001c1b5010b00e401005070183c4071040c07440c000500154580d0504c2075040110079032040019114405403007521240d403400007102e44140c501646184a840000d100d031441401649240990000b00350008076580c0500e5004c4c1541d440e03059003035810940f40d0b80e001e904502c0004d00c40d080c140e00e12940c0607000a008205080030352010300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 605623039 1250 605621789 605621791
    0x5010e0a080307082202042f0324060d0c03020f0f120907060c1e02100815030a080406030b031615020f1b01180e010b0c061b0a0c02010c1e021f02151806 67
    0x40422804002c0100504204101c5061031400c05a602d96800d002c200040c424418541c0141c80c080c1c3e02c4641d05014ee2080d410380345900060048596100032801c2c080c2c0e81d030780041014031105003030000052400130021071120704480e055152281010072a0780d03561402c0c0c3c0300054051006c80c040da61040540c0c0d800c0220381e80100d0940319610316047c00304c0001900701c0468001e07400b9a014014510000c0e81c5031080318201e0340c20740b400013200300c5020300007401d16603c1c00c0c1e0071f0b06896010b00003080401582840c24241c009a800b1100e042490b0104151a02c0e0a80402a003610103030000d100c0e194090001600c85201100381510802d031100140110340b402030708205a81440440c41000a4a0810030b0130f81049a41c581c5102d45446030a1050b428800c03120701508018005040008590003826698076403039002e80c0c0d03800120300c0c500303012810300c064003000d07031062041051001001700001d0000380300b101280d01505c4140b111a0300b0111041c80500745040400401902030070640c4140203507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 605624289 1250 605623039 605623121
    0x409020a151101060501120c020f010507211e020f070b070507030e09060307031506051f08060108040f03030c0e1305010e06030706050d0905010e0a08030708220204 72
    0x286107107507801460600400348104090f8900003082c05181c0c0c2007201c440c640300390b1400c041100d144026089050240b41c403d00c2d0b810b50709280038050041c0c1c01c40143c5500500502060580031940440402603d00c146d48030f4150210300d22103403214414903002020780b00c1181017075034a000c0580d51a580211000c4075414001200426074804043d80306050f07500d6440210f5104c6000e0614400081d211001844000c06400216100c00c038485e0040c0c0041000f8500204801071686520f0f2004d01d2103045000088002010400010b00300d42c06940d00a001c3e0b40c00040140e0440303410f903004d42c0101800342180c01480354441406000350389182208884400c00400840e00f9450500041103060002c0c00c3c1c01d100e60417109082c001964480c094a40c43d500480c0c0118070b204803814510300420324500072040b94001e04101c45d003404050380066020b0703100d036564070103295120801298070305404076403204904020203405000d031806401c00500b02205140140c3c0c9011f105004d540641002912 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 605625539 1250 605624289 605624309
    0x9060d08040e01180507050301050306060409060605060f1e13030f030207030c15021e1506060f030403090f0f050105090d0c0504020408070e130317041a0c09041a010219020409020a 79
    0x4c02d0400012400b8290b0410802e007061815541440c000a4a414005007440d01a17070380c8500801c1808100c1d000301d4010320020304000d56032381d040c64541207654031601180740e400c0711219100402140707010882d080410f04500c1688440d045a40703c0c0e00721421000c0c1601180304642c400701c04508840301caa001880300301042000c5014028000c5e040c910506a5500d240803e1480407000c404080355109403980c210f14400b02903511200041e2a50140c01c803901c100c1d20010040000f0140c005045106850209a54000440e584d10820300108098085c0c50300103503046c040303000c050610002494009201e600a003528544032008102285c02551011129900c0300e0f4040140c0703c007a4a4268004034100d90080c1074003808d48020b0910180040102c00b0380d02240c00240904c0304980556400b0307403481d01c9e508001d0610040000c1ca6400154090303125034681071000c9416002c41050030a458010b030041c1c042e000c400c420141e90f2410400c01660030a48034080000166149006c041c003604036506 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 605626789 1250 605625539 605625569
    0x60f0904061401060e2d1003110f03040516050a06051614010506013903110d080414160509091603150e030a05070b1e07090e1509060d08040e01 63
    0x1b041100711441c0d6552084100620302010502d17008a0f400964010a540b00740700110310f10011801082d002c10800840c0c2004110b401c0580c0b4030344001e500490040d02116101d5111a00340c0740c040c43d0a100b03259000502071010000503000700f0103041c1c5026204d100d4101078003203444d2514001c04410084c80265924420000e5560704400d40c09900034a01104c0c00505c81988102d065404003007074a600940074500ca500100751241ca031115442e140c0d282038890341e55210b08081c103c0041038604940582e51a00901c4408100140c4120507641c08400d07448114602418080413500107014070980f806415009030741800094079441c0114031a0154110044031809400308683c00c80a4448654100700540610f07154008103880c206078021401012075150400007a001b0f0481a401002c2c9028600030800404d800074a810100c0300c00d111100b54540e0b80c40c10441e5202c0244021551019940b404545c541c108040c006502a2003040701a2602da01d0700c151502254003640405400aa062 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 605628039 1250 605626789 605626817
    0x315050310050f01150903021201090212030c0c040e060403030504020609030a080c01051b0d0513060504050a02090a05100308030c070b0f07020f06060d02011110020307030c03060e060f090406140106 87
    0xf8001d40103042402c04031035042070401000300f400400d880064464403c0300c030400110b000a61201080c1c603030003404000c503a00c01034241070b100d8005071500850760041c00c0020201c2c3c1494003d0004074101c00001d009503969070340d01a0020030000c0c00680e00b10209001c001000e80701005413403003140c058081d968441c0c50148000b803d5610081185804500d5689c440010740844015240c3c1100e80403404515a40e46000d0214501e03a84d02d40540712a0500c4103100a2290209501a00714003d4900244540d80d0094a20a41e80e02741c8051a820701c5604040000c074410001850f00708001040c0a0b24041c003d4071440750f091801c0e191485820040400e00031400d4041101c03003440103c94000c2c2a491824100103100381400e40c074080c0c180b083e824034030304100e0800d201d001940068010110349038104600010006d00d4210704800101e403a040c000720b0316000d81c0b003500307206070001400240c1805446040c0112a11301400c102c0c1c040351912903414468002c030144034041e0100d50b4520f501c0c01511 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 605629289 1250 605628039 605628061
    0x405010507140a2f0307032301020d1103090d11120705120409050906090a3201060602030a110613110d050a080310150806040c0522050301110f030601031505031005 72
    0x20130441c6100381c3c440e540420000315006000070f003211400002801034034088d20502e004e0710500b1715140364985442da0650209520304090b6009904403400c4410b4544004001d032009140c10140d0a041e07401095400e82032401800180026441882a01d064007401c45030701c0501c0c1c2058111500700b988880070020665006c104942d03000014134010186082c250301e40201e8055200441c0048010103944204229603000c110010829890020020305554003402034132500124550400990112440401c0c00800150680580d400318541d204840d4142c1c4e8000d040084040d5090708100e2082000020900030300c001040d86004080b041c4d6240f60803242645000250740010075612540004181002d50042000e035011605650015281e902400d05440500030100d041000f0044042c1c0c0341180f0048401400440d54281e00a2084949000b5000c0284c002c41503c1d0082a109100040156110760800e5110950030120350b80c0003512500032900300f40302c82a1211b03d058944080c4142d0311a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 605630539 1250 605629289 605629373
    0x90f0803040515150f060405060d0c0e0109030233070309030614041101081f060507050c011e030203100e0403030b090601030c020a0b0a18050d03060b0405010507140a 73
    0x50310314500c00f03d00d0645600381986008030300007401290002d00700e01c9543c4414003100c0123898001c147c1d0791146080c0100001504059840030001a4890440c918550140c2940c4003680d80c0109402c940c25004483c4440d03c00c103079441c5102101d80700d41840c051484100060520f00e000303555200682d4150b0501d40c00b42c8991240780c89140136450304120102d10465035500d503041c0309190100840d2240300c03108030781c1c5282c200c40c4103000d924910f0004026800100600d1807034401e03000d84480001000c0195001c00c003081040c2404441200c00d80a180d03c20f03402983c0c4800c01d0540f07034801c262101856020a4801c840441c00310b95503a200a1041ca0f08108080d071001c03091074203125901d01a030000b91510000304000307101c001154046107148405d50400a05071071807491903e0760000c40e007003a41c0d030740900310000004607207072080109a00e152907044400392141a10b40030f02d840c00d02d60300c640222800c0358585486018a141c050700140c82d400078800c80c1400c0134030010320440d0358103151099200e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 605631789 1250 605630539 605630563
    0xe0703300c0f060e010f02040906050901050405010609062d050301170d0e19031e0309090b1f0513060509040b0901121416120b07030504030207140103090f08030405 72
    0x8504000400002c4607030502c46003040d800040814a100741030400da001d03202901c01100c0c2c107400402c01140b140600c2e8896004c135841250603040c00c0c3d9840c030a1204580f428043d48001500e10041800700720700a48100c1c6100580148120031081c042105004a074000c180d071000007040000108810560b82c5401c004e440c030510040d24078483c580340c020303003031302e41c00c160300c600403503404204034442031801c01440c00458001c4c8075031360140c00c141319076080301c1b0040e078040300410f00c0b84101240c005118401e00e21800c0700074220a14040b20606500e14a103403010a0604000c0c1c108400c0001e0008845e4810080016448140c0c032600080304000075501004600750040c80b1030001000440c00c0511030310082c0e0341115221003102c04000010341000d455034001000500c2001e4005582d03c004014512414055184042161100442102075640603500580160f104140501c402c0400103440000c0d040141000036400300a656607030a00c0f842c12909a034000008400c003c1030146c14803080e5032a072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 605633039 1250 605631789 605631797
    0x302010e0a180524130c0c0804030f03020f0708061f090e0c040b01111203100b03011517010605090909070f032d021507080912060403030b0f01120e070330 68
    0x4013100c0810711300450f0060060615890710000001c190107040c4141c3c6164200320515030b1543c482c14000d900c081d000000714018403641803070300c40c0e925000c2561401d030b4510720098111522108190000d54240300700c01401ca0300c60610000d0501054414080152241c1c030140ca8902003403000c0108840e0545a42c0341400300305000244030110100c0c5e01004011100c690a480f9140c100c020404086940c224402010001002081d001c150307214041403104182d495269020b00484200d0030710f202807240c80d000c107006004044003442c081d0080b41d07008007a001150022303980c0d4502124403140c0740e4004d031038580c085416405108a80640ba48134145848602005c1c1c11032640840c0a1a400340c4680100e10310100e94001007040c80c2081b83c4011000a0000d108614149185e5446500c02d036004c401003413a0006c49003480c00d00c080e10740403402c016110002d00c01d03c000c800350003410501c240c40843c1d028000c4040000340042c10b00203c04000c37003440d0030b4480104038109445d5501000440140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 605634289 1250 605633039 605633101
    0xf030f2502030a1d150d0b0f060f180a0b0409290d110d0303020c0c0f09070507020d0c06051b07080703121209080c10020c06010302010e0a1805 63
    0x205800200b03c0e010080d440c40c0c02c20702690703503240b99040c45041c0e801071580a1610221409200f00c0340024241000f4480020072003000820308201e41d851081d030307010790408401c1c010000b4002c00080540610155034400c0076050f0356820000b0441c003502e410460b207680010030f0500480c409441003010044140c007031006400c0441c2440c2e036803a034010308028819800030711200100007158400c0c0303203000c2020b00703450031400080c90098043d400081d0081698424006400c40790315101e8910381e20307040007802524940e214404100c0e9603034044603081c1c1c0c00040b210100000a940c941244001300340d60740e6a079440380b030141d10401d1094038111480c0001c0d40402018442e180d4007049940440b41c0c819a0f600c89800c4203101075541445075450000a103190521003000e2080c43c0b0002d01950b000c11080d00d0714040050450f038220f000300d4031001c01a43c0050018801540103112800740d07014007d0400e454030b50740e20007400c03441003588500c40804d034658040c041d074280c02c0036a100020f4622480c03031940d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 605635539 1250 605634289 605634361
    0xb0a0f110d0c0c1e03020f07080303150607030e01050d0902182d0112060605060a0906020601050a060e09040203011b0e0a0b0c060727081b06040f14060f030f 69
    0x46030b2548001071513102160320070f8041500801001101d80d5810080e00c86d11a07841240d00c1d00ca80045a541340b19201c1000943c006280034004c807200075034180c9030700d0840d0714000f00440e21500151640c00455985600031000f5075180c6511302e00d502001103a481d0107141c100a41c0d540c0c54255981028004080303d410311055601807500750541d180d904d09101c1c0030b0001d04000700a00343c01e500c11074004000003048008240d00100340e10544000d6005c841075640d0360702c10b005800005210b031a000905c04100300409240c03150704150054001400400c0604100800c8000040340284001c049203510041103903504180920341c4c02002d81c140b01d90b0400840140b100e0700c4203801001c44e001c00a4080907491180c020383c00c2c9800100d0003241c80000d46844469803903030f5015078801040c0e83c4003068100825071904208031401d0312000203c58039894540103c07007010442c0040400d51050080c01590f20301d61900010314454590b401c4400f5507402e1102c20000f80c9114401d040344070350201d490f1411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 605636789 1250 605635539 605635553
    0xf050a0e030403051b040204050a031101140901050403110402070c060c1202011802060304050f030408030c120702030309330a1b082205060301030605061f08040b0a0f110d0c0c 77
    0x1c01c00d801c0c451744400840d4084c0008000b441140c11031544500140d40120500c28641c6181090362001e8803608a10440d11440000602a5501e101d002640401060001070700c0c60100211042c2c0250002d03040500640c0e8214107190303182c10000c0010743c0b45504009000324000024090044c80c00200082c110702d007402c0041d00910480603000f40000004142080002c1040c10f0540d0800c0043d071391581d4484000719107039440345030b0700c4040748107211421000c40019011140040e074000c1c003d40c50400080288500110340c100e010b42d140e514640c0c034040b44650342e8004038114102d640c00c05d5a07a0b00e00b02c0090101c00a00110601d601000405480068002800c54506892103010000507905580703880d0340c20900ca4000175008800400004100201500110700800302110441e1540b100d41c0f0850b08170740044484200080c690601080100d11000c486580180c500400481e00d00580000d440598410000c0d40e04c1c0d0490006003252554014440c04144142c1d0707190221000c3c0c2c6c56101d540d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 605638039 1250 605636789 605636803
    0x8010608070318050601170f1203010e18011e27060f020c01020c0a1a040314090d0503070c0e060f0d0b090102070c09090b1b03130c08010f050a0e03040305 68
    0x80c06055031102d081c0c4803e14802e0b102141d032030f40081101c6103580c41d001404500304030b0242440032813045004d81d4204803000b050303e145030440e1150b2a81540c0c600210311102c0030002d05018a40008a41061a002428064040d42d0701c00082046400b400f081008012506482c6120000e1420604261480c0c0340e1450704000d100c0d003103400895005001d2401a00074400c88210030015031001400f120042c001140350703190700c0c1c026480c84c06e10008880d09464401001c40340180001c00c6440c003903808158180103030000c034074064000010391080756030302d620b1944400c00a8800f40c2e49400c0800c101044410b900ba480078065400852030064240440c5141c000e000d40100003808500006e44441004d60581c0d00c15600314803903002950780c600301c16008101e40d200507900303d8006000110b0301089401202d0031010403444451031aa900d200005401020803011184950380c144001b85a90090081300e01444018078001610300300503d0040840300c06044641441d00140020008140003080304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 605639289 1250 605638039 605638051
    0x60206040636050c04020403080a030c181e060f0f0c020402071b030605011e030f0309031718030a030c1205160f02041a1c05100204060c05070608010608 67
    0x101c0c5075228103070780802c80050245942d1141c110400d580740d01d00080001919228014015900b81414502c2400180d12a41c0000b4001a400308140d05070248a907200c100001014600780042100d255503031650600140d220004010a1800c091000c10703200d02208014425810850407203410f0b604080c0c0840c24050604060182c40e40b140e000b036440380d40460345101d901403025020142e004522150041c8240015030700703285080004900c0d42c100e41c1314452810414911118540d19590341c2007111300035007004800300804064000000395410b00d000030908510b9018070348910b80d0b02c00c0d010402000f182d41c9407007540183c80d00000b203500001c100101d035810183c10104034404e840280d50700d101d8000e9050418280034102010301904500407010705100f26010301221442d0413401c0c04a03c0b840d042940d200c4c1030740d00d42d41c0c4201e0400d000c00410034030500660307142c03107800c0f09200c003280c0065000002203041d203080d0b1001c00c04140b125401812650602c0303d42541000801850402d0042031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 605640539 1250 605639289 605639291
    0x910050103091109090a0510060b0702040906140f01090b0105040b18190b070201090e0f0a0b03010e07090902150307050301090906020f0a032004051804290601080708010602060406 79
    0x112506102000303001400c3e010001d0a031035810b04188403043da40e04000d001c00d60301402900d0b8921102e944a0180741e04031800305841d10b0030710207181c00300070040115100490b109071352807a81c0141d00c0d180383c41d41171140904080c820031320340c5800b80c0c203015500e04050250401034100001d100e01e1000c04203840030300b0141c00c50046607483c0341011482401d105030010320031400d080130000d401807036400101102403003030342c815804641c0c540c14440b50302d40603078211103460300400001745c1c104003590011001c2c10300200040703507014441c1412418009181c001d10341564a0302d00010560924858000b0304600c0318401501d5031601c0e4500510901042c0500c0401d5525030a980301403100c01e80585004620b0000741035941e4400d09005002452030302815004400d0124003040d00e140c4100555081310405404061494600b014008001c04001d0003203441c1000354074118000704420807103e0110f90044620422810800300150601400800d03140c00c10090800522215030302080740d5410940c0460 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 605641789 1250 605640539 605640551
    0x30d0203090703141609020301121127010e010614030a0e031c0c080106110a030819021902060f010515090102120c03040f0807060c1b0801110a0e0910050103 69
    0x4101e820309445510141800c030301c015800300407060100303010010151a0701e03001341040d540c03800703403041e400b09218290f070700d00d980d01c0801c02190845450300e805000041c0807100280b000d2010101d240c0403420582604014980140706821082074614007510340b504201160100c41d00c20888107220007000d8002ca6516140320402e020010015640c0c1c054603201c5c010341c054081980c80c0c0061503a80140000600403c0002a10901400c550f8264030b8411002c0c2000700b17060346054803502005000318060b100c1c6124a0611b4072100d1010740007041a01c0340f04d0800c007048150080c500f20000e04210f50180c04034004110a40d03c031a4002090f0400384040e5441d40c2c9208010313414402407a54084074881c0c00039140515080103c000d1090703540b00b10303110a08a455013041307555201c050254002250002a0070304c00f1404807803407440c40418a0401c1c10250b600c600c001401c1d00d03e0545042e40080c00441d42c0865960061b0b4510b441c2001a510f10840b807030701002c0c200c8190741c24810541456503d030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 605643039 1250 605641789 605641801
    0x63809061c061d1f230609060a05030105151216030e0601081e031c020313080c06071202030702060103060b01050903012a0207150f03020c150a110903030d0203 70
    0x500b01000400c0d09502d6003406180303107000842c55600440e0428038102036100c04071505500d88403524261052110f006980c2d0002030740740400d9028159007281d00500500c0944030340d544042c003d09062000359122912945803209110210444a071617044518082c0000e2005500038001c05a00181058441e0139003944040140d000b000005000c02d4030340034150000c81c42160019422014092100d103001ca0240155071407500c9008107040d00000d001152600181604680c000c3c64102200302c5210401e00410741e00c900060740b111810605542286041007040c542000301207803ca4040c020944ca907203030003c8001e4940a050000404259842411180d00d9204409076060381d00d0141c000c108841184900c031a42c908205a41100a14012070484009202080c28012111030780001c40740c08180c600c064450b000404101d2080660034041100070b21401c128000a030303c1c822850310540e007410455482603640034052101030307102c20441300e0302c561800002c45100c400c1d09600141c49440e85 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 605644289 1250 605643039 605643041
    0xf12040305090d050c10020a052a0307031a0a060617040620040302030c060c1b180705070201021506010c020904020f1203030a140f01030308040501063809061c 70
    0xc440c01504002042c83c0c1c03008200c3c0006214a00c00030449280d070240c0700042d0100e0f6200e40490700100b260300714859104808580104812260440006040840c10303081c0c04203103002d01a901c280c3e400840d07100784078124008542c450f500445803401c00d04c10741c1c4c00c1003000307071042a40c2c800006c8030900b004005420310110b5481803140c2001c1100140c00c010003818540004c0c0c01c5030105a109000d4401c03280e100345450403c48403442c1d113007009054000c6000c904040c41c0c14000c0c005a4001c0c001e002114001c20588081a2090105481e01500e9030b1140c0002440c003440d242c01264402c0310391092100c545e82140d603510a03554100c406010990340c0344040340400c42510742c1c1c50340154502503100f400340e00c04405544a00d000c41c10401080d0514003070600b44c01021364805001e10300d07100040c00441e2184a0345584240507000105a0660b200442034a80710040321203c4104c0c00013184440d13409060621401d06614044c903941040d24079000280c640c8102c070070481d004072601d144c3c07520361015 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 605645539 1250 605644289 605644297
    0x160b0c03011d061f02100f020c120d0b03011d1e07172506111207030503040f020d0c050a090b0604060513080303040b010f06050a0806010f03150909060e030f12040305 73
    0x220a4440b85020709245010f5554030110407844906c0f400c050751148001e80358400d5400120f480002031148400180281d4116031051010940709a12031403020a03a880034020201e240d040340e80d12010b119817258055044c002031440c00f06000b2110140340c10030074000958007083c0c6180104062900c040d03800840c0c42d010722104070326400d8510881403000a901c94034240102e41ea00d4545056220b080d034655620341003505000010054140b0941c40440c0c4600050766001d445580c00700d06e441407540006000b161207440c111101c00c5101c10500150030f05204150040010b4441480001c10060000b001801070f802032000300003001c62001440131002c98658020080309043e42d0740e905080c10904c0350301009010344448201d42e1040024454070032401c0340c4a1900580da02e140e2601c86c00d004407154144240031608160f00c4109900f40c12191203105001001c2614001840c0015803410b801a03c13008692101940c10034130100300c11807402003c0303034201c1c041d000641140e07903118a0280c480340070b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 605646789 1250 605645539 605645569
    0x1b060b0f0d060b0a120b0705030a110d05041103030406023a0201091e0b1b25140606030a030309150f021c050c181203160b0c03011d06 59
    0x7514070310400c00d2000581c045504070703205640d0b00c0e0109444078a024a4040240d00080102c0304500004042e41d12440107560040c00880c0040381094910740422405d40080900003203071582c80303051104100d00010800811041500036506007843e11030060348a690030200700c0725071540c8101100011460062401240000510380c0c92550300300c1d0130003402019030182c22100ca40c00c1001440da0036015050003414986d1120031111036a554a86030402c80c0c1050500c8104a0700a020685401d0200302c80344000800c0d88104030320188d03081c200a1410012009031400e280c0094042c0308194801055220f049a010308001c14800c0c100d01e1300141d0850780c070340b8500c0e4445c9400c0c461419040190010082503442d61503084080183e0055117085031070940711110056010444a4003911240780e248403042d90041803200c4081038004040e0440d4048509039624a240072101c5c001c102c410040b05421629079005030741550305041010744803c080840c07141120212200242007aa20003040d030541c48 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 605648039 1250 605646789 605646799
    0x6180b0c1c230d0b040c0c0b240d02040e010609090201080a0203011d091006061116060e0f0d02091f06090e0403050c01180605101a040302040e1e03030a0c1b060b0f 72
    0x10f86402c020402d0540300030440356074100704085000289d0302103250403524040300e0745614003c042000c20a080210f10742c200e810680b00c012152580ca420301c6510010700c0d0320180485e1110781c0784001401c422000f408079540c41d02c1400180301c1c0840c01d410068500c800414400f045485103401e2504d0803007040d2034a1071407401c0c4000411031560158110034145480c10445148040403451006005558050344000902280d14000d407441c1007034920082c0d801c0a04a000038918580100f4030141d82224500101d01140381044030343e40048040d80020a00f41c58000521030078001e50002c40b41c0c014201030104140400c4108850000b03500140c03142000369000b00416685250030070242204440092410b030b0f503000000340c0740f030903000c4030084100800e109a280034115402c00c0001c220800001ca070901c20b060701c0b000f8001d980040d42c040b0000000c02507441b480c1c4024000155541c02c821001080841407413001c0060035100e25808850380400040b541d46142c101003404492400d80182d800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 605649289 1250 605648039 605648051
    0x90b0105040c0309051c2304090f090302060402191d010807050306010e010e06061207020f100c140a0e03030c01060305060a0c0824101707050a020706180b0c1c230d0b04 74
    0x10342000051027240c8034140c09009050504070b01c42704980c4101400340260b0031200001c3c00514101c0b81c650243d02010180d03100842c1c40e55009516a00480d400761003949010006010320841086040300031b0900328000c3c6495070500c2c0100e000203406108070002c40c4150070125403c0e80d00e66040da10340c500c20890803807592402800c02555006840e031204001d01070401990748a21030350042c00c42003c030302d884440900510060340901a8001403450301003007036000c000c1d80255004d0008007500c2850340004940300b41103017400c90900402a100c1c2d020300780703000c100040750354000b8500c66000084002c0d000c0c140342c80c4802d82c100341e4116000305510007140710b4200115070300000039848240801d070f0f0414155944000558041c4962a41c45000d40d101000400c9061f2040c0a4465103024004481d0ac031036070355041620740703038014100d2a60b80340c02006d12070380442c1040a01e400d199801d807900030001d0303a159070303000c2112800404441080500007501c4801c111140c210310a0810003420400031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 605650539 1250 605649289 605649347
    0xb070305030f01050f21030d0504050609061e04080a0905060a052502030a021c0b042108010b0910090b030907080d0c120807020a0501090b0105040c0309051c 69
    0x3550040300e12103010224200042483d05100b08011001007001e000042d844d0403d2260322030440160340c0099440c4000c00c002c03801b5180038012540964414802401c584c10607400160504030003d1090a10441c20320400d14282e511202035074001d0742000d02141c1d2032a800b50300712030f000c4d00c40e0060780d08113400007038a140c901d50110060070302807000650159401c6120b010002615210080a5070592102d20a20007514001301000c0c40510403148006a00809556095454808071020354441c1d50780c1c2c462420b010744141007200c52030b4262a04002660402035040740a0045520315401099002c24400000707000c2d9400c08003420303000c00396648a240424581c3c0c5d461b51203020390001806540c003e9102180102080f1001540c08007103107224502454007202c1110f0700070250170461003521a060045242880f03009100c0d4010010a4195070402060106480a070310921003018074000408020602c040380445c49c41074030b8070810810b02e02c0c0c80c8080303a00b88076050302c4903200d0310302404682c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 605651789 1250 605650539 605650547
    0x130b19060e071713080c1501080309010e180106320403030e0303030705070209071b1101081b0403080f0f0f1815030604110d0c090e06040606091205070b0703 69
    0x100c035481036a90f840ca50521042d80c0c00c16900c1c02d403502aa01c058200740f0a00040f03ca00140c10782c4a005401c0b00c2450b1141c03a10b061860100380e214045903040060460b0481d603006070144401e8800791050752440001a422000e5070405101e04002c022200301c2007607034052040d1a4541c04551241656883c1c50b000f041c91800390300902c4120040787c03841e0548401c505020050b40c4c403944158803803a082501a4091103014600100b9150401004100900e005406440940803950040c521400010058400980340d2040503201d00303a00c40b40032040200c0e402802044070700380d940c0008441d450780c0c5010385940f0300740201c8034590900e66001c9030180c00302a2150240801e550741442c1900c0050740d40081c4101080010380c0c00c0000c1c00104001185030038150800c50700351021810780c6140a411800400403602c81030304440001e80c6a00d002c01200b01c5a540701508408210340400c040740c9010400303030844d445072113494488555800d40d1400c0c081c0910429008100c8916850394560b10303403034010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 605653039 1250 605651789 605651791
    0xe150a120b010f0f080a08130e0a020c010b090610111903021c0c0819121d01050906091e0a02060d0c030f0902090c1b0d050a020d0206130b19060e 64
    0x400300c0905404000340380c00030b1309211000c44418501400da0178546440b40c002c0c0d5170010a00010580c0414400101d48017450300013072282480c03480058a440558441900b540c0d0741c030700154404c03181601404110340d543c0240540030f81c8181010302b01e01b2441d202c40e5080c2040c031600e05068020000b880d4042c1b6030085840f207880c100c041055154a0b540000a50302860070210241c8994020722044694000070240000c0f40c43c2c0a051800140019000303c0301510007902140b040c00200d00d44003070610809000301604664800c004c0c200c40d10b8040c0c0d109a442a00440c0c1c0c1c00c4449801e4401450000c09005194065401030111603440307400c440080090a0004055800245000b10010301c0e17900b10701c540182541d00401b20190303038403800c01d920b0007900580f180c241500144004912000341c10404c03148100c9041c0c45403a02c0c1d4502c510080c1c100050092400107541080c0300700000554400154444654413900e1401b040d1580c0c40d0b0303007904410303801d03201003902d14211020030480c2020750b1355 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 605654289 1250 605653039 605653049
    0x90f030309150e030703081510020f0c0f180408070605070f14032503110d0e0c0105031918080c06060a080a03050301052404030b1f0e150a120b01 64
    0x56101d05440e03602c40011211420a09619504107110703160000303218060068001050201e001c154503004d40c009130120000c0003c0001683c0400300d805410b047c1802030180c2040d0442d0003c51614050001c0364800c405c0404580700e84034200002020046210705a401082e0011800c003d20300d4400b401510706c4101d410b2010220f07210510b018050300d240300489104981c030780611800340d01c44002c0c0f48800e2418902450038140c441c0741e03c1283c49841d20180051981c07406000c607142c0011240c007130a00300c0408140d41001020420003900d422141c234608145080c11100041300c0f03014a00801c0a90b500000c01004400001a00c215900c4c2c0025045e00484080f10004602503a90800d29074507004c844000300032038010300041221385810074400000c803801d80d620300742074080855412900d40c0560011224109102c00344078941d0040ba030907907005040081311342d004608195080201e480300904050030182c121114007482d40320304000a005000e400d4880c0560030040c5090001e2800900031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 605655539 1250 605654289 605654303
    0x3030406021c0605030d0e040b1302030109270b090c06070b07020f01022a030c070e16020d050306061c181a040b0601050705070308030f06030d0f090b0c01090f030309 73
    0xd074112a154a100f40c004565000b4003c10616002510547d14030048402c569070291f52005480741c20345a56000904030302040d00c0042e81ca60400c4000d00840f40300040b1040002015010b46892902c80764219080c260414107071020b95980041d02468000315a1125400c1741001c94650200540c200f0ba0034000c00054094540311070f9441c5213030303080f0b015aa60402c8426200000303600c45982500306800c0151000c03081d0f9188c50300d07052089240c201341b54040c6c101c41d40c000382001218000c0e00000c07041601240701401c0018402e9400400900024102c948180c000140320301d80c400e0030034102074034049402d000380300d48882aa181d505281681c0001c0d40c4203580205000303804442c03850000c3c0310b142d0240c00000580c88802c01100c0c1c03a000a081121184039681021001c00d0000c1c01941c410b0007407141c6102039140040606003050810038013a005c0c46404403641c8016500421180217135a0081343d010b450340140300382c06014280d40c5030050031030002e4400900038580c2c940c01a078021406000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 605656789 1250 605655539 605655577
    0x91109090d0503180c1c120f0909110712030f060b0306060a0c0227040c080a051002130f0920040b04060e0a0302031507270306020c030c0303040602 65
    0x401240c81e022107048201c006102000050f103000c0e02c080001094000080459009600400c04907801d400940d2082001d06040c8400c0030801c0700f0502c080034000001e242c0140c00d01c0d410680500600e500c0c0c010b8800603500c5081104d441d140000c1a07480040d00040501200010114080c000b80b160f00c20b50b1401604100c004912407540004490140401134a0135150007100c640407a00c14002100881e84403e0f140d0340e02040108084055554150415454009042c207241410b516085039115408c076401410440002c20000b141e00e10007000d203a48c0c09a81d50401e58130070036658841e030f00216050b103827031100810808103543c000c440031151000c1c0c010408407c0140c8840c1f5000710b20550394907220402051007401d10408284111100242105644940301e41c0042d04048015842c50b80c07000c203050030444040e03409081800a010080c3c1014000c0c0ca0002c0b40720f04c0600c0368000503166a40004604040e0001041143d4040708800305072500c80c00c086c0b4256010b54008034444010ac40008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 605658039 1250 605656789 605656801
    0x20d08220c0905090a0507030b100b030a06051f02030315030c13020408061005090a09170309030306040c080105012a060c0f0905030c09012102091501090f03050304060c15091109 78
    0x617002d5259030b049402044401c2c03940d521412040801040d0904c0141052300c0040d10808800256010b55000140418468102f1040c0311003420400340c031000103c94240040c3e502c1e6001300c2103a40102c0546070a80c0c2da4680100400d14007000242e180c0c2e0010340240030140d180000d81c0c0500180c40c03002e010303034031281c862002542c2115441c0c0a41c0f9400701c20100400c2e200c507080d47c8190300c500d1062185036042d091185100078560411283c144190f0000420001d4131b10b4a0b00c01c0400300881810003180740d50510000921410b000307040c503035a245d111800e0074250305120302e0300d184c0c960307000c8010b0212601211005103580c408000038000b04801c0400402c1914001c503c1d8030450b180134104540701c0c2c1c03a0a6020070b0100c04507841103841a243c903e4600540c60711091140320380c030000b8081d42c24881041c0010704268a0f5440f185c0c000c003a08000340f001070703808011202100c00b84e2501c48494002c41c149810649642c001d8141018078000e6200304005035a90342d880703140000c0ba0703146540c0c0c3e160 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 605659289 1250 605658039 605658043
    0x24060c1b09090706050c01090206040e150405010f2c010828150209010e090a022d04171006080705040507030516140705010513050d050703020d08220c090509 69
    0x140c0b0041400d4200503000d20003030744920081c100d540740402c00400c10400f6a0086001c583c082c2c0c0050003260b0541c810403800c0c0300d200c007c0300401074044d0b808111540c0b61035800410000c0f280070f1180701800800980e00001020044500350f1202e03a5074007440d40d6501c00800e5600e035a60003801c034040006050003c0e450300381019101c9040c0e0406c00000d07074000c107e50060001e510040d00607051102c4146510380c5038940c1c1c10000d20480c0304a07001613807611240c03103190618580c2c0d44070310180445810703100e00600350441954110741c0b401d0900000c1201c40c0c1c02071030520792105115912585019000207280744000352030022104141d03400c20140d161044220b0503600102d0348401c01000300a582800584180444064092500d00399401c04203640d840500390ba0b01607501d0103225400500f0b11050101c184039400c410901030500c1840c050103690701039151051404050244080704001401c54030845464102200d0603182c50703124200a450144056682801200747c06450400000d40766280 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 605660539 1250 605659289 605659291
    0x406110a050901081806090d021c140a0302040b030c030a0c050405100c0507090c050c012a0305060301060306050705071406011802030406060e101502010606050324060c1b09 76
    0x100d6940c0600d0031400340010740d24018082c003900000c003050840141604800c3c45078501079440c40700500341c500c2001c00001d1030410010750901c41515107003c0e81c041d054005001a112513451500d5584420b680441900240256400030080322000010000c681c80481300461140c004a40c0030048c458a1070342c212000e020f28040d440d000303258024080c20450042c1000c001d5903204070b0460700782584480040d41030b51089a000c002081c80800e0040f2903e90a001e40b480c40c4102c50b031300708810902c81180340754400109034003005242d070707c40119a20392003e400c080082c0d034203d075092000d81040e000c003c040342d01081341501d61035840500c0e00c074850004600c45040319100340c6141d6200c42c584409030001e42c8044c2c4210390443e40c904c03000484075a0b02800511500c01342e903401d0859450040103000d406030014194085901d05a030038441c149c9c100c0d064076080319104690140740c11074880760048010045000b590300c03540c003154292044200285c500340c90482c0120b01c640f00d540200a200715580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 605661789 1250 605660539 605660557
    0x90801150f030609060f020a03060f1502030318030f0a09170109030504090b0307050301060605120c1e0d0207171b0f0d05130e09100e0606011e031112040611 69
    0x210341c0c40c040021858540041c84418021400024010784141c6880c0481e4048229400031030344400c000c21082c004010004010514560540300401088100a4403884000d040312560214500d520754202000c006803507900300050b090981e41e800220010700550000e1240011030341080010020303002040c02501441541030700d903036003080d0518641c180546000141305426103e4900300091690f030034000e503c0104050384505641e40c13000d080c01c200c03551009084a207d51000c000c1a030070401c000d0300d5560841003040c0865219a5010034090103842841d401900e1080101c84044a10250200500c601c000d0006140520010980400e0325502440e0302c54281d0380040741d00c00415030040000b09142040008101da944d6200e4030030b1001c0c40e41c10307164481c030369120700028958001b07035215a5900d6502040100303418980500020f0040b411034405084511703c800c99024040c3c0690000032240b00420605500c91100d05000201030004650030395446081842c0440446401001c840c1410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 605663039 1250 605661789 605661809
    0x12307061b05130e0a11030f040b16021c051c15060f0c0209060301151403010b010804052e0207030e030c0d0b04140307060f15060f0903061a030a0309080115 69
    0x1d113000d903054907441d0010f000d420f199441e48441061420a04001d5220b07501014240c00182054201f101070300394014a2061894810010440b005400044400e501c40480c40b5100340300f030505000b2581c60061020507000e8130014400011170a4054010030300d400c003c0054564203030fa44860031070b03507452040c0e000001305201800c007001504158103081c4c0d1008000e40049203800c90343d150349101450903030007040e1035110401021413901d001c0c001d18100607000d19149015080079220981c41b0089410200c0e14000d4041268610786900d407070585041104650845d156599414007922082c0d9242400740b00b40103003218092640f030035800320424141c10030b0440140f680c440d600e42d0f008000902d90410540b0080c48444001030300d40c042c1170b1080c04400780114a40e014181445140700c41600111f0512000c1800d0a180650000002d0116500504007003014050008a51107004100b540d041d0503008140d4541e041c140c00c0503c0b030b030445a11500030000c0794072041d02506000c806000740c8940c0c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 605664289 1250 605663039 605663077
    0x403201f0504060608250b071104050a1d0a06050c03010b0708250c0e150303031f170a030f0206101814040c0504060605090609012307061b05 62
    0x10040e164081540103108a000140290300c4080e014a00305032a0780900f07041c124950f1052066180403100307002041c40c041010704281c0716548030180c01e00c501301d849000b5030340e410024070310410b5500420348641c00c010341110002056001e99032600c01c040c000303035051820000840c05401d0907600700d034104c80c403860740142030010700e50310550142d0141040d040c07074800090248a000e002d00c950107403860303c51004c0b08001c41c5013180405004600408a04154034a40342e00502d03600e0100c1200d50142c4264080078041031640652140c0b0821500300c0030141000c6030180e411141c0000e44d82145501a0300c81d45955080c01208030303980e544c01c840514189141002c03c02003000c009c0709003080340ea40044c000c2100c00901f410001d02940407201590031901c440c00400090034a44a1100a0241c0c0d00d8518904058000030513414813922082030b0410400000d041646804444000c602c5640901201e5403135003d41000006130034075007800c458800b0a801240e0920340110202d4000c01da901046d84a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 605665539 1250 605664289 605664343
    0x1f021513020f0111060c0a0e0f090a0e0102041208030a0501120c0302041e05041109010609030c0b16051203010f0510021b0301020d0e06092103010b1809040320 70
    0x80d41c0050740c165410f008210710404c02e03030003061140501c12042046100d8440d454070100070b01105110303810500444107196543c40c141c5070000d0069111140d00c01c003103003c5d508000883c0c0244119803000161507000c04250b001c0104d1080214018440c01200307202c1a40c80300d00d0240f1420060030000c080c02c4120b071040005003041e8101440000c0d1284000aa003482e6a0404065a1040f1000c5555052100a003102c9160958406016104a25207240a98210b50380c000f4803080780d0280f00611103010170981c0e80e8298000f40388a900c2c3e030100a440c070b01144600b40c800550428061203103440c6034058081080d00b400b01c00c0140385042c0b9401442990381c842000700003100080d2020786c15540030071141188016900403d055054480010103252420b001150304002d80403010710040c0211404881c1c006031444240d905450300303e513000b070384e848040442145550760440481e0b08409144204424075411500c200451403e554000c0c900b5130605107010b44441c80c80340a007440e81c0080d080108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 605666789 1250 605665539 605665549
    0x604030c06021303030e0907033e2115060d0b030f1903030e0607020c06220e15011e0309021507240b010503160309021f02151302 57
    0x812a80070724801840c0c074103020142c10341e0035615001038012941c08010400380d81040c4254075404481450b00300885401d884d228400780c0424140d248405140030f40111a0346400d8501e14001448000c9542e5100d0208803a9101e200812500701100c101c20b0001880ca40b00321080100004d000402c00380c03030501e0050503000205408a07a06402d481069944119118100000d00600720204814404034000c2d15005080d90003c0744e0b800d0f001d030804c10034040d5035500041c41c070760540011500b15484804a006103a070b400c1c07075404503518504000794001405c0b1200001c845c0901d50b0703031034800c0000e400d80c1c0040d02d1341000c250787c01c400f100c02801d03924076162180c0d00a9a5041c030081c50340500d5103001c16031005d140c100e540140c1d8005403d10456030542003942000703038041c90500003805031440340400a000f900006280700645034140e44003c0c00d5522075849143310300c0e030051110268201200b0810b186e03084a6201e040544550703443d0031050680c0c01280c6203d194124912000c3c1711555003884 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 605668039 1250 605666789 605666807
    0x906130f0f09060b0f1804060602012403080f0f0d0504030306031a101701110304111009030b07080c072f01030b030c060a021f0c0e011106150a0503010c02030904061403060403 77
    0x96420102c050a06c00c807990340c0d004500061455900105e580443c840d030328404088014100e20098040110030000600d41c0f900791130054040c0d01001d9240e41410742e0248180c400c1d01d00b00c2900038600b900300b00030160158000020750f800b0b100b108500300141c6000114030300041d60b410306c0c0c04250700c50401c4400e000c1d010f030790ba514a00c1000842d6240007445003094942069030f04403803820842c040080c050400d100a81610760a43c54030303481c05480c648070558070344005031008040209001c000754a80d80e984040f1145940e01900300e00c03646d400200402010940120300e015062242c1c080450f02d984280590a20900f0040c0a0314171481144104011680030781d4100701036018880c400c00a5100810f5920407504017058042102c03407105038001c140400002d86c85040c851511181c040400380041d0440e80a11086d008070405000a00041c030328160a074071944c1e140d8200b190541210394080080d1291200c107940510000e42c555a5000c019511117072044c0c1c065011500190105c1d215426030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 605669289 1250 605668039 605668057
    0x804020d02150a030608190b0403180510050a030507030501180b0a0f330f2303090c1e060304020118030f080301080d0305040201140906130f0f09060b0f 67
    0x41d4400302020032800c003d070408840032000c240d46120070000c80505100300c500800482d03051a10100b15541c03030750440c200242c005801c001c030011601d441001d41d8585a0050703d0020b10703210301480c0d60385004001e07034080040000028182408503519034002e014150681e50f664010414000c1c0300c2d02c070301c40204400020242c0c0143c1c00791f0001800011510320602424015940103c901c410002c400c62181c440f11000003418104031407030890b1a030020201c4240c10007864448194a000c4a5012580d804c4484146401100105201005800203038080740c1d4001a980c00c500901031b05464000000b03003400194003c8810400200150300c1920741c0071141840700080e0740880e0700e9460f180d0b48009540030494041d6030000060142d03100070024461602d1f06860f0511080c503040c0c1c00200590024201c81e03000003c0450300c906c5940ea10000e65110361506020100c5031940d42201400d06103083c81808041003200b41e002c00d031403c0d0342c0501000d075000c07500e0300c2d8900302142e040441154041034039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 605670539 1250 605669289 605669299
    0x25020d0c03170408040f0819110f120f010c210b060412050a0b132f04050f060a0e240a09020a090f1205060c0304050109050a030807031109010804020d02 67
    0x2400b0403003425a02d00500550160107820348490821a001c038012081340c01034034131039018105401004640840c00300d111580600e88440101c3c084002c610107074155940346a11107012545403020510000e81c807005040540028403401c1940d01c01510303102102da1a10010b4a41c106900e0059a2a0341121040c0c09015054901d0244d590354a0304107110000c0c4102c0b21604402208000e101c0c004c0d070419006042c003491409658a01e580300d070b03074450410305000e55840c1c42e019651312a803035515404409681c050070030700c168a000120802d8144080f604984500030403500420520200c909aa1081d4010b26413806403c0d640c42c8944040300000f8032156200c2d00610011072002402d0000c0e0038101c0301625515039a0703007004445413540344150404036110014000d44008504000b8159401994100a09980c0d403143d04080f0f014151403207000c0d1030380c40b070f01c03803a140ac0691105159115442690302002050312845101480344a001840740c00111003201003000b52814100080c3c1e60351000302 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 605671789 1250 605670539 605670557
    0x614090c06040e0402190b0309160f081902040b0406090b030d02240c0706110d06090c050f18030706081605031e270a021f200c130525020d0c03 63
    0x110301f11191300c125004400740e040020307890400006030092a000c2d2203d2482410054207005889617039a800d0208020719184240700b650070364176039500049182d40007030701c2401003c0e101c40781b9102624548103124040c2c41020708404013984040781d061030088401c600a41d08110701030008a07203980c040c10342c03840600300304100e40010b402c0b40b003213122030b529041134603403a01c09543b1140100d0341140d02400443d414038200c0101c1a41c8002250001e0311f0b0390381c070300c0c0d110445040c1c407013207121a000b00135070544204a00850815000307882640f0440d6440700a10054100e00000c60b214081540e0000c182884001600324030500c0412555020000a644850f408960104140ca41240d414900f88603000700b000e21082d400c000c007204031030b546500310341501410300c0d010090071a1100300f100848118200c0d041c03010794800b80a4281886802031054801a030a48203800041c0010346d20419000c0d00c886914a9140001c10306102c0c0c80626000b07004005c020030419140207600050843c10014051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 605673039 1250 605671789 605671799
    0xc05121002070c050306060a033f020a0516120303020a2105180303101a07140601051e01020a0b0a02041e03050d090f0915030614090c06040e040219 65
    0x440070b088040e0040a071090090302d030a0600d800e00c00058031044c0a2040c40b031050011544500a0800f1071200c01d90000c0b01c8240002c840300b0035203144021204058424901c13000d5142c0c0003030b180c0c402d05e01030750943c6d0003014281d902c0301041400b0310900c00214088400710010901a40c05480d107040a070034041322102d8480d18001400503801818054203686009208564800000030703582000100002d502d5420420300304910400140300b8107403144100c0600101e480440d40a4410b080c0d44030790719014400c58240d1345500d8110900070240100310347d29007120300e90306070003012200c0181a0060020180c040d21000384d507410007084c0007074094082000054400304500d10300d1400d8101c540c41c919050030341c0340503810503414030748290401c005100107000800c15142030300110380d41c0510004074000001000a6205c203203a1003d031046140150240c2c41404000a075407007070512070b007503410403c4844100689030286008100c50001c0075000240141060075020b10902c0d44003403988110740c1e940c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 605674289 1250 605673039 605673041
    0xc040311040f1116050c011d0405040c0e0c031b210a020415030603020f0a0608010e0702011b020a0c050603071205130506010b0703020c03070308161110020c030f03070c051210 77
    0x2204600c6104042c4c560b00e44140b000a10007020002c009203020a000798240719944144050f04020a01c29951b89012904000c0c071100b01800074120700c0076900d0686000344a40b4480d81045a80f00002810070512050301c020003800c0319841c0940100700090400444c2440401140c010420000705508000205112000601004014220348c0d004900b0034158814400c0300c410807443c50380222414501440074035044000941542c4070708000400b40c0d070b2039010807400b6100d50125204002c0002c0020b5045070360200701030344554000c0c48074400460340c0300b0030f0059610080b980e040006000d5840c441021130140c200c1500306100c0300700c46040c0303405900c40c14100300f02031b48408021000042c00307004054041c8010022002c00f1000390044d0762554582c0c1c195803282c12950841d144c1c81100707040400c21140b4004d20801c0e80a031901c491020921350203569101d030380050901c28400d480f0694911107000044038995503015807081800c80c500300c00d1100c07a00d00300400021900070303003024410311009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 605675539 1250 605674289 605674297
    0x30305061302130305100e0303060904031202030703061d16050c0f030c0115080c030705210d050a0216050312070c0306020a05030a0b03010c0c02010509010905091009050c040311040f11 81
    0x4010710800054a50301d4401d1400300e8010986c001142891465828020080142c80c2d1040e4180c420203415030740e81ca02210060611020082c406101005200849034903038401419200c00001040900150417101d02e0040000c030303680c8561541c040d80074098103210350050112a20300308100e13034000c0030404c65642190030221502c0910380d5142610190070a9002c00031004100150140c035070741a40b075012903203132402030007001e003d03c0c0c004c000842c80344101404034040f0110b400644446006040700100300303500c0a0080700052050000c0209a03803509003180301250340040040c05814404980c0a20303580100a040e110546030800000200f049800103001440c2c40e80ea8040d030700c0c50f200020500710780c42880001c0c000c0c2e01d01a101c161807500070000c068025024202662107800c40d000403943c2002641141c0d03003000500c401e2180001e481c000902c1035606802052107250b4076500c0400d4280114400038203030347c0100d4002c807003509240c0c0c090001c0b20a03044002c581040c0c0a50000010340c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 605676789 1250 605675539 605675557
    0x703060b0f03011b0201110a0e01140d05040f03120216020d06020c150402030709020403120e120f0102252604050a06020c010e0a060921050a0c060f0905090103030305061302 76
    0x4200c00d0a6503e0b5080c4187c500d11104a0202410000396400090049100d1092035040c89182e40428001150350f0f8141c440c07484d2070040501c424035003450311540c0304894070021800702d520701041c98103e04140c001d03600d9984c13005a05480c9010340b60204a040e80e18608280c0b103030740d420400001d4041051000d0010044881c1004080c0d0a09105151912802e0341c02880050300c1484244002415041000703440015032402026038000e1000007400300c0141182d64000744a14040010840f10640240c05505008850100c1000c082d1030341074200d2800c000000e00e201a80d01c1034500f0718800001c0c1c0508002101890350500351110045562441c00760070260241c0e03c5001c000b2599030b4010f00c0d91000c0102541c1c5004e5003440e1a8015120111030f018000504208041a50803850101c0322a21155040b004941175011103041c0f80e0085022805103000007604c007007400710001e000307001c500210380006d0020701950b0f01c1c5450032801032801610031640480240040701c1e400c10b25001030302501c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 605678039 1250 605676789 605676821
    0x80604140f01170303040804090902030f030c07030312060f03020108041109130b0703060f12050a0503210a0c1b05010b030708010501060905031b0f2b06050901020c0703060b0f0301 79
    0x1504000014807202c0e010f080480751540104100b00c005070404040d0740480301c07469004141d0070040c0c40003e01f0030701ca41e100d121310b510000c20003140200c40010154101c900984403080c142100311198426591703907000e403100c50114490100015445030b507141c3e501902407100029100c0c07643c800900c019409507045003420f10b03105101810710000f80299500700ca01401c0822225140003000d4080c44280d20036a1104085120b049003030140502924030019403200580f03540340c0d1500300c040030900040c0081c00440706540001036001e050fa11541a081c4a2034a4403804820341c0315002c0f031041000c181c00c1303889549440404440b1b49040000c07801610150001158960402070010200c03486940414400c0c0c0c0a06211856900301041c6144260720940e03802c0c42c0c0300c0503c070200300d5191882100030700100020041c003001c0540d81c021104410f100307620610080d1607000380c2da400d0740503052181105e03421212040000034141d601013103107540003070700d942d04041c6c4900000e030845101c0081c0c22003035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 605679289 1250 605678039 605678041
    0x8010302010e03010b031c02030c030309033a0b0604230108220b2a0c120304080909060111100906060602060702030a050f0706020a171b0a080604140f 66
    0x40d030b000b40c0c81c90300c4100103800800400c0e201c0000039a4800860030703401e58584000c0511303012548280104c0343d440300d10108072642ca04200c40002e64941c403825035031140068851060212218500416100c00d07903640f02d41c0341c520741c0303056501300801880c3d8590f980038a040000007102102e503500c0f000141e07a41e1030444208804c03600054445d00d001002d541083c41404908140100413400c40d11855803c001007031690799840440403e11201c102c03014113038151070040c84810145281c0140001c2044030b06840403000c03580b030300f10100c1c0801e55000701498004e00c460221410504a070039880241494800d9580744030115140c00e10340c00004116600d61200200800d2203d54092080101010f200415140c80c02e82c1d00207440380114080035040200004060401d00040d03c1030380e105540101342150380d83e8981740043d1415440008030440075403400001421113410405251144010b0300d191840c01c01600000c0b180e143c4002c1c62780380c0c02507480350b20410304508d8010b19031207981030120394056 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 605680539 1250 605679289 605679293
    0x501030b04061103071202071e2105040e070c020d020a0b120c040312080703061520010606050a1103070c090501051203190e0303070b090309010908011406010f050c030307080103 78
    0x3d449100314a45100b01c002c0040c0304a0070342c08000c0741c1446401740c40041e200c41c150710f0102c2c00203840c00c1307551480340c02c080f2006d014021800005142000740802d01c210307070052410241c03102c0c083c80c03140c000b0b103244000c00929118010b80c1903220052005040c540c600300da90b0b000802c650340701c1d040b954184801040300c1501c070000c481e803680c0103020b0344012802c0500e55910350000b074000319045000c0010007008100d05600a402640140240240383c501e1440c8940c0010071020041251072110700d000282d03190844010f00c02c440c20781d2800e948451401100110a80f0340050003505052207100800500c0046600c02d40c2680207490040c00110f00c80d4074242c2003289600859043c6076446e0410081303220340d100300c3c880c519a800a541010046c904100d0b000906500590b07030040d00c1911540300300700382240040010302c02c29030b090701c1e66640e50340c407541100c0c0ac80c0d03455442c40d4803e041980c0401c0940d0300501c01115800c000d450110b24020703500c5c0c11241581c000780d8011001c5401c01d0300500c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 605681789 1250 605680539 605680541
    0x307050d120f05090c060c0f1506040b0d05212b0606021605040c0e120d030614030703060e0a020d03170a0b030d0e0f0307030b01081905030a050c0c040501030b0406 72
    0xa1814502c031000e00c0307141019982ea54070307201d822070b04506c140c100040080340214144403040c6104412000c5e00c034140c5820482615200044845e588502e280203401c400e10b143c600c0c0e40c1000107400c080280113603605201c03c0180546407008135003c903030044c484c407000821140c0c00204424070007a19900724140072801801910050b42205c0190341001e00c4110501d87e94030285002c844040310003044800201a0070343d4101500e079066500060713420300000307200500052860f0040403a580400203c0c1c0d407446d031072651500d019504c03540b58000324801c1001c100160402d46409200c401030b1159031000754002028072510920880202e14a005924803c14080c0b0700e0742d80c000400d001c103015000407840001e0702d1714400300543c403c3c084280340c88603154440301c01440718140090203c0d07984940301d08102880c24001d2013034101074400c0514011b621070518130900d441e5036001e801141070400e40c8209030b5050300000d18000740ca100d032301c10030069a503a17030007858000c6000d00500c503072f242000c1c2400c078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 605683039 1250 605681789 605681801
    0x307020a080304150f180e1e0601020c060903120307090906150509060a020a2009010902190f0e040603030e0102010b041401090b0103060506040e07020d0c0308010608090307050d12 79
    0x2441034000f40410080710180d030044051650042c500389480140a18007902d5401000c0c0407550200c1042101040c0176440039001802540c80c0944030b4100c0d100b41010801d180c031b044034181d0040e04031102c6101e403414084003516a180000f01070303c00c0c000728010070044a41040b241c640006041500800c528200e510802000d801c20b2400075849581800340502544030f074102c054003c5000007402c44966100b0b10075510101c0d4400d0326900714040790410440f4490700d482081d48181142d4000242c1c0c28854070031242003410041f20302c1294000d000701030320901c1c83c65894005014a04004403242d42d11441a100614230a4444103450381f0424002130031540c4100409000d1480c0040200c032601201d458030b4110340106c500800c5160600e0012006416154403480e001000460003040c0d450050904c613109103810340c21140a2250170404485a00d5025005004606000c1c01401002d104415541d0b0104800d81240d140110a64078a441e0080400204001070100c1000002d002c0c5940501c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 605684289 1250 605683039 605683049
    0xc0b0703020d09170303060d03030f090606050f03010921120e030706050c0909010b0a03020d0f0501050f06070803040305033d050d0308060405040323030105180411300307020a 77
    0x19a241c0c004c100e2610b6501c0c1300c003601e042d1242148180500415120b80c100118246038403100b8003201c01035140c42c0d0b020701914051035200703480f145c0c40c41d0040d003814805c1c2c80c0f18641014500c0702001000000409403055500c0b10800c00000d0f0085030720300303282409520104071440008580e0792141e400d04a040f03c1000c1c1154203640410000c8454903030391220001c1c192092803111030b071740c0d556480d4150028130520b9a601c01c01e9050054410000c406a800b05040b20010380320b007680341f414001003203601c0c802c139103005119200500104011074400c4015590046c00342445000d014041d10005804080f0130040d940b10300d80440e0741c07425902804c0c0502c0000c1c071003504d0259000610396405000060018107490055507070700d00085c00c5c548039018881c4d11170060581c4044920407069554542c1d4002d000c0c141c021440707014080b01080c04010424030071900b0601c41a141c1c07200c14108505040c0c04030f20744021140b9004450403c80c001c40c14468900e003501d000359950121407040c060640000d6200c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 605685539 1250 605684289 605684309
    0xf0711060711130b13051f0803030a061403100207050709090620091c020d021504140a05010c0609020a090e0109030210060e0613020c120702041d12070c0b0703020d09 73
    0x10010341501c2e0400c1c2c117001111000c1000c182c40d542e840090040585941c00c00c1c400258240c80040c1a120110056019080c00401800965103522105000c0e051244515826600840c3d03880958079030341e4054a04e051240c016104110350b540083d0050320341703940c1b01307403510780d51409021002c00c800001404001a030b006103a04140410000600f41b20101c001420841407602e107010440d60f41070150074038698008e1800359040c80556280342c540c7c0040c001c50030180c81d11800c8599030f00e803004505049034030503511043d0901491761b805014000402c001c81e080110390b8004601c18000d401800d8400010000000b0701c2c680f203040c000e103428650440d0503e500d10f011000c2c45280c0001483c250302c501d007991a40707035024400f01054024418811914107074041c9100186488075100000d020660017101c040c4240c011900f00071007178140c1c10390414502c1d8050240c440284012034007600d080d030b0155120070350440ea034000001c6541c0c40817200300c00503006044008003083e0090038280140c18419a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 605686789 1250 605685539 605685551
    0x1020606010f081b0f07082a0a12111e070e01080304141507050a0b070302031512030403021f1803030806090a090f03020a030f030b01050f071106071113 67
    0x20b0140c600c10300501300e1101021000d041c5078204641d81d04680414140c01744140c3e40f0045800c0011040d0000810000500c401800841189070280469000003461070058440d0440b5945ca1a4040d210421040c007480f004007001f10480c48240600c04140b07108100103040c140c9501c0c1038034280b075105d400c80304240010030011b002d0800000250741c15545081c00c0c0c4404001050b000541c03120b000002d11842c494001038a0040000203c0e04021451086008010340e8840000590a038001150014000380810301050442c2c07a0403060300b03001007007000039130b885c0546039004152140034203844945500f90b0888120310140d80012442d1903800550010340900b4150360f402000b1042c06000c1901c51a14800424581c0025a1107010740319841410803407988500d02e8003a4072404000c106070701180c0f030310060704001c50190040910185d0140c3d1030510304403948200c142507411110083c0d0380b00c20b240303958100381e465042c01019081d005410418079482c0f00c40400c0905032074445a40003850a02e8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 605688039 1250 605686789 605686817
    0x309010624020312040206040e040f02030d0507030f0f05041d0f06030109030504060507080d06090b011106060a050126010b04030c091806050406150612050108070e070507080c12090102060601 84
    0xb00946902254013059403840351500c2c0000303036071409150000b000201540f02800104800c1d124030940c840d00c20380c180d0752070500c41c1105031550b00507007901802064031858082840c3d0b03c507565202c44050300b81001e0b400c1c0303904c4100f0005401000c1d9230840f1180305200c203004103c05444441d60780164224000e001151050341d0040403070180e88180014480d002c95107104020708401946c20f03200e60030b41c00b0440503070b0b01c039409800782041070780c4079011480d039946400c0c42070404038000c0d200d06400340c0305141c4c25240200440b094032141c080c82a0061500401c800c90b41c55246800d402001d8494125440c0c9085080c05a090041640f21116281c6810080e02c24106441e031418070058102c94009802d03915070a0100180c50482c0c41c0411a40c070806000c155240c201b00900c1780c5d520a084c0400045c1c0c2c856440c1561001c0b24010510324008580001e440304cc0700d00d005001442c4076007680f0741001600d00d121441c01a251503007820165002c908103030fa40d6410040d0b43d030b00840918041039485505 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 605689289 1250 605688039 605688043
    0x20a050901031a0d20031209190e0c1b03030f1e0f13030c02040e011a0904020a03060207081b060f0c030f06101b060609051008101a0303030901062402 66
    0x41ca60040004d0322170900003151040c944a490030301540501510702c610074400d16038040e54444010a8454010b140035588150705803841141660448142d10031075440d003404044081d000308040b2200202082c07841b054541d0140051402070090452244442c01c18407030310040e480c90360200724502034070b403c04c001d100703500711160383d802c4400c10740c05500d14042c03400d04070340ca20070180e801394001d4100b8040510b00c150550104403c20418103640460320002000c029400c001175502035030041c66954140007082d1554002d00321240f1404600d4034010201483c201680542c1d207450b10150400c070f003088110494403010b158040284200580b442c685a03e500140000162550f03005c2d040b07248440310149e01030000c0940103180800d6083e40f0100510b0160048c181d43d00490b1441410080400c1f01c00e048501501d080c7d40c568405041e44218400c12f186c0113011003031205038241c07100f200140a41d10b0030300c000c5001e122054000704016042081021100301c814180301c0700e113110b401140300c0d61580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 605690539 1250 605689289 605689309
    0x6061409010807050d0903020c100201020a050909220308090607260709080f01020304050d0c02180606161b050f0607060e012d1118060304060f020a050901031a 70
    0x200b401d040c0700b141c0300c00740f04440d41d00a034440b85a0b028584070a0b00149038001410350b0b22780e142140d00034144461410b00302c1c02d174040e81c440c03140401e03414445169180350040007035500200b14500700c02c401c0d00c224906841800509402c0d00800c0c029020701040000c20301c44c0a50128060401c4080010000d5480d420350300344a000d4189041d0000200d403075640f003898220000d142c80d008699401440b032070424001c0d8016501124544941454150490300640303420030110380013041350000202c0e0300181c00c040000204410f41c400020800701c290140040864000c40d40104070b264a0742070f622210064001c0e86070041c40c40f4550070b000349401e690700c6500700c8006c65401000421030711f0f200c01e4114003400600b0070b141050705040c600b00c0081c1119054040403100038003402d110b80c17100390118124500c130794000d2260440d0880c4440085040c050015a0498800c4a0000388407524458040c12a000400d01da0b0000e14000307a030502070340e0306000c0d20404818104407004103034451800100f2004c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 605691789 1250 605690539 605690557
    0x310120f11041e140a1125050a12080a15050f01050d11030601091401020705210a140d110c0d17040b120a3305040204090501060201060614 61
    0x108805508402d48070340e002442e0700c0903c030315204094a510003103140504030700c80b100d043d4460f600c0c2c00590400c400b40501c1080c6044116218070f08002c4c1809440340703600101c449110400c1d800920000240c00300403804520340501a0144102509040204034400c0585080c83d101d0903d01f1030f10341490141c031008100da10444403c2142022980141c42601412903046400391410a600c4681e803284030040d846400c1c01da03100703801191940e5040c0031052048001c1030060b4008001401903042284d85015040301c0750103081410b5a018020500e05040e2181c11078044141804030fa10000c0200407180c119003081c1020702a031800303543d1040d90f0311800b10280384104140c5803280d0900540c0714110280084444039a03030346581360031515100fa07004d011043d040e4141c1ca400103100c5400c522500038040c140ba244450303648030b56603030060b00141080840030034040c880030000c0c007035a946c402800184080240810950302d08907000e401c44903a0b501250a100c05003405105502244040b256400c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 605693039 1250 605691789 605691803
    0x20a0302070501050a0c02030601090507020f072301090e070f0306050d03270e07170106081909030306050a03050a02100e130c050d05090303041b0602100f0902150310120f 75
    0x10b0340590221029606d11300065018020032002050029441c0c01044c4900c4181e000c680600042000042d50f03600345100741031603030b900e90421b141140300b40300c1c0c140703020720051405680c100e4452005001072070054a01c46c010030921940b4046498041c0078100040004a400851030445514003600d2006200c4205070324046039034420b0962149025908064500241075182c01e00d070014000d0003000c4003008901c0300741d0380000001005445008018412007148141d210f1000a200044c0c0c040e2840200480c04d0603100e41c0c0c0459140c0356132034640000c6000780b0080c0a450103a0060100d5030b03100100c0c41d000c0041c42886c03810700d611962aa94151000c01100050f28284060110b0300b07400340040c0f1040e01d82c10481803043c4d01000101a5000314050a06c400805c0c0c2c10b0f849000545900e03100d00c90258010503c520501e00042c1c1c001380e165000d00c1c2012511000a900041020070428045001d9007004420700c0600b0b150001058040e12071200d8046140050b07444118041750f240d90018200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 605694289 1250 605693039 605693047
    0xc06180d0f14040305010c0f030b04021c020702030a02040509070306150501141602091008101415041404060c08010608150d0503160503180913021c08040801050f07020a030207050105 80
    0x181c0b80081200c1c021038214000b0800411100c0008043c1d4030701c0f10b041c0d0006400c2c25000c040034501403007100e4030018854200d00950b194a22034130081c0d00101d078241d0b49805400f00301d20140e01d07607004503072003455810b001c0c01d2a6401c40c84c01320100d9044c3d0b40f601034201d44d03044c4284082c0e6040100309a00c1000c052959490380304c02d00410309146000540207401c211204140300030b6203850250202590303a190709680c0050501c490000890704007003150710355805050046074410039004048458900d0140000c1307072302d0b03c01c80d5000d01c0301ca1041e03400722010380d550340d2400e1155034400031480c0580030a18249000381841f4030880240d41042c01140d2148032a07282020400c070702042283c2c403642641075075103d00899401c0c8651250080d030013140c071003c14440041d00602e00002c1d540d1048403050b03501403302400d07400380000700d083e051112030703060348244a500102c0c2114016100030540c602c008510781ca0040c040c900710040160100c0259401b81c4285c1001076000300e05041070364000e00c0c5c5140c0b5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 605695539 1250 605694289 605694317
    0x110f0712050703060e1c110c040e030903031c050f07080a1109130b041a0a03110f031b01300c02100e0102041401170412030902060c06180d0f 62
    0x146401079000a118916081405019440c003085482010700006c5242e40c5019103e0025968150705100d03d0b410f03504248183d40c0390b45803603406004484100411a0700301410b8501207403455004c2d103210f1000e140d414000514192160103544e40c8995038000d83c0440f410040c1001c0d100800c007070034992201c1c0e1950000b410078006d120603a41010b000070b003101c0d681c2d0f03500b0064400416460303048a02a504041042031003a160b42c1170b05030038a2014080825031031454440c001d410700c1050106501c00105513103654190307010001c81c0c5481c002d00d0000340c0d501c41c40d0400508102c0642030b210b40910450244404100482425482016001030021641080c2004200d0800c00c070011221004c43c5021003541c04c1145c1580a03101f0f581c0410203a4104040020043d1090090281ca020742466454002400103501c0b0b0b001585180d070a040c0810002d005038005015030708080e102c5040b40d8802001c010394091003000b460201701803000501800301d4645002040304004130084002d1080b03040548070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 605696789 1250 605695539 605695543
    0x7080307020c090718090b060f0705070803030f0a050a050408030a0906060b1603090807150f020109020a0b090907030b130b0f09010308120106022a0f130c110f071205 73
    0x180411000380000c0c0701e41342003640513045032440d03070009400d4801c40303d000c81c1100285c40340f07030740441004081c03604003040d501101050754010002220b40d40106000050203507802c0019500588606121191924110080c0030403034800914011003c0d040c0014000450642004c0301d8224120303840106048503d4200322001d05403560104d002024000381c0d81c004200c0c1070b00241111031181c0d45010781c540c1c7d1120615901c66041c042c5090022011070a03101c0e15025501c44c43d800754660001148014080c2c00040010345c031a40440d10588001402401c2c91411000b556800500f03801c0410034814000e0100d0202c8180d18420403180c2c0da00c844603c402c0c1d4400c8640721942000070402c0080e50784a04d480807a541062903c003d41484140000c60090f00128114034485401da41400402585107c0e051012103104511500520342141461a40e2618034000400c050043d07008110350707425040040c8080b80c44512090950082e04041d40038510200b2498102c4c0c0b481b20700800c0001031030602038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 605698039 1250 605696789 605696803
    0x60905061b06070315080606062209020c01090204061e15090909050705010206221104020d0e160b04030f12050c0a0b010609060c11040903270e1305030708030702 71
    0x100030791041c2c2d002c000c1e116605801154084603038484a20701d04d030303586400503503860b0143c40680c0e0000c404e10604010800c031060024032080100e00c604032403a601c101d4481242e101e0a0f900f48540d4684002c6010360401c0d0007190010215007a00da0000c4921038120032050350103014401420020652900c07045103d06928400b91407003000c00c0010700d035986025a81c92026102c0c2c02d01501030728002414142c8059086900c402c0860706868520000e83c0e81c01c56408450b0f000c40f03510603420700c4050320685540c410215003103048001030120a000b87e01c440c403004e403203030701c91200210108000d00001f2032120481c003500754040d82c80c145040c544481501c00f4021107144415902ca41b019890901c158089024104d0315641c03948410350340c0b2004d0407036040b400d600020f0402d421018001c102801d0980c0828001c500174039100c1c141a10301d0203988550707881c0031004220810645c6081c048500c2840d44c4031b40121890003040307146e04036580c40d542c0720300400d00050070309000800021400c038000e220b08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 605699289 1250 605698039 605698087
    0x809030a121506120506010e211509011d07050307061b080324090606070b1e0106020708010f021201050d031e1706100917011104080d021606090506 65
    0x907202d0a8480800a14141003510384040d180d0500c400708543d540104e040c500700d4200070b000021010a031905100d8228042e50030080c90744517201401c1050038502203001d00803240e00c0b0021a40c812541205c0e41d0341605450000c0b030030b030004441001150303400101ca100302c5405091003480031003105105500112a4130014204c1140017003006a54030383c076151908096480302403400d4030010031081c040d007000300b2030311700b5000b4038100040000b00300c0e80f000181e03000c01c1652070303150201d04115544c8095803003030f03100742d0142e405a8000d00c21400280554161070008441c21401d1280d000c2400e040382d081841010300500d1710030520030a00d4441c1c0b050002e0b203481038803114444da2104100500d68112402001030600490300464024544404603513070219440d51240181c604110420301050382c4c1c50a085165075845401c00042c02c2c00b4005400140318a00c00307001c0e492080c01001e030a0510f4007151008080090324240b040a0700005d0000a0720002e41e0069112200705554001c0d107080b401503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 605700539 1250 605699289 605699321
    0x109090305090a0b09031b01210207060f06081e0307030e031207150c0c1104050c0705060114030c01090b0406051c0203040b060f0609090402090408071b06030c0809030a12 75
    0x462400d0b041c4006101c451700c10342c02c0394a41440311500c8160689081080c41c0000c00c000701d010080e0040510203a604104c011b001403410700740c0d42d20380080f94104c0c41c0c100307a480d88542d410400d0a0040c05020202c1245038461022101d01c814515140d114681c401014014001561850fa8508100c0034464089503025940d03034208070b080c1204904a900c000c4086541001087d10702c0c944241c5020811030340c0605542070340611081040007902000b8903120407050148000c0010030700411503d0300078401104484074004003d42418100b640c5081d203d414009164400c000400422040344d040325a2450f1081d1a0302c15050281518100564800d440c103001005020078040c5902c82c2e140075440407a05400c2c500f05101c01c2c0407850140d40c1d0616070200800d40040c01508007085442c0c0d00502c100b18061820344d1a40c1c40149100c404000c041a0f118004030a20886825102d0130b119240c840c2040915440c2c0101950740c0ea10030805d01c0700800a00c0c100304800049a83c1100840400400e2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 605701789 1250 605700539 605700559
    0x21915060b040e09011109130e010f1104032010030b06040b040e090d0207080a0b040807050106151209230114010605070618320a12081806010909030509 67
    0x2040c000071050568407130b01c07154a004040c0f04014507200882e044182d010701281c007584500c8180328010303c46040e400a2954a0b010b110201403401d114103140704004207a855103860960400d04120100c12880c1c40058101c90028003041d40c820080d121400100c0c50003103069414000424111f01070b5500143c4007900100300071810203020380f07480340b00395003c00031100d0082440c0c0c01242d9500c40d512591503290443e03d58107000c00e0b0075a103140e80c4603004900d400e2070072056541d50303802c65031950700240002c00d1001c030202c400c41c3d00c0081d00036080e14104040c0190010f94031030454044442d98011030600c1c003c082d07a0b101034000c0d0881d00c0440f060000707070002d540c4d403a08040d0440d841100f040354124540f40a010080f0712030700103044603a07000700d86040c0300b12040b4988140303583c0503100c101c500e88800501c8128400300b08110b03403034144104810580c0d2140e0310307000784c039140025103c4014100c07500e0481d514500b000510350304461b280200400c0b00c40341c50070291000e128403c581a08006c56070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 605703039 1250 605701789 605701799
    0x1120f0501021e1b0601230f060a0906020706090b16051509070501170907050f120a06090b060405131209050a0e1e130f0606090203040b04060c021915060b04 69
    0x9040d0b1102000d0710b818042e40e000481c0c41c0c403000240a0442d00c171103443ea1f0049a00c9442000490701c1c40054180c101d40c6c0d032000300284d003607009080318000003100000140310702641840340d14014215030400c20480c0d41000008110fa00030007880107066032900c485001840030400c03c16900d402c05d00280c02840c20325409040d01d1300303210b0250302e022905840c6000e0210303824196503840b40000401600c2524200070400c0702c0060000013603940b0401010b0302102c07501d01400510318803841080b000584000a24045132003c4000701340d07901c25450130040200301c90a0340b050102c020f40c0705403a161116081ea07401c5c0c2d01e45a951700308941040591b00081354031030b05038040034000c10028122091031440b080a828000e2412502021412000c4040e940000d280400388041c061050360041440358a03070034002c0803600704681c02d503001c0f00030700180018001c0c1e92149000c01b01040c030140211501c180c4104284c80c0d6410300040c45400b5510307000300070540550200010b0f09035240c4c080d03039032a6a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 605704289 1250 605703039 605703097
    0x9060e01051006020a050601050d1103070e1515120a0612062027010c08030703050712270215190f02010b010801090905010f0203070f0e0901120f050102 67
    0x120b03a00c0d03010007038107140441c002e1300016050604a031b1020083c10360340e00304418006000c104083c2141c1c00420002c0740446c941e03041c840000909207507120031001e882d20405461040c00c007050058019a21078840c2d4482c0d4148070111010742e03145d040d000c051600c510080200500999105201c03401201d480b80041041c150000f0170903507607054192080302d8850b104c54106100702c3c11016058241051300701c0c2c0381c5200c0701681c0817000b03050400d0900c0c1d42054a0340d107c2a070084400c80700181d920b900b00044643c21174120b032020050030104000035040445002000b10b13240311956121130900780100110b40e40c83e010b0320b215071542c02c00f803601d03194014482a00700400381e06d500302043c1c03840943d40300f4034414811140e003104c0581d100803441c1d1034081008000c1814a9054549540f100118190113078240005d41c01030744107544000603410081c1d1b00404ca40d00309140244102d00505c01001030700e00c11006803a61a030000c0d0850801102860481e0082c03003440600d0101c1910130031125212651 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 605705539 1250 605704289 605704291
    0x31204030510050c0702150f1603020d0c0510020c0c131508030a09050f0105090a0308030106090e01080a30030605090604020c1e0106051f140f0406030c0309060e0105 73
    0x70980c101c55002041039101c900340e4808036a8070030318901c1403100e4005031030941c00704c1088041c00d8415924111010703103428081d0340881c42c50072828107448000c10405134104022480242545818011200d00303039185505d441c00b0a01c840c80d095004031301070816540c103002c0490142d5000700a401c181d248203840704041c0c020011184040801182e0026013403102104450f2484490b96a40c032036582000f0420210708075044d101810070109001d00700c2251507101c0448083c60081000c503031a980b4215005103000307000d400410702c50140304010000000d0000d00b40002d10f900c802d8403501d861081e084c101d00e5400408401026600247c0040300f11905980f04000340d6400f43ca1614a940d250302c20300c0282c2c4105e4041040d95800084802c2552148610414000c8036020010880e107541c5c8000608641d00c810101940b07400410136001c2c001d07000000780c101c50721500c0d0b8042c201000c003031a081141c042e5106035018192a00481c050081c800d50002600c2688003c0130011050a44601402800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 605706789 1250 605705539 605705543
    0x30c01050117011808030406050a29120312041103010e060a020d0c1b02010e0301060902071410060506030403050f0f04120521180a0302090906041a0f0708070e03120403 74
    0x482c3c030002d8100d0b04c21038207039010040d030044002440c50300da0303941e43c900501c0300411180c1102c0c3d80e03e035072800c2034a45c114545626110f10300d480001d01c10107010020307840e1442100001513442040b00c2000e00002c81420341c2e0054100a4150741e0004260220340036202d00040d045250189070b040100b5460160b01608e0b114130003440820000300c110b02d0540700d90800d042c140c04509032030195000150b12941801544580282c0040740c41651071900c0340680e080000e08807007441c0904030b842100c141c10042c280c01c0814802080c0f0a02d8a4030011640740e1101a0001c2d0401c080012101080201c400481340e80c5102c1c40c054543e20750347d070035159040c0480504111101e000c0d602c15050f1a580000129190040d10340d151454024640f07805861000c3c02e143d02a00210710b01c4000003d42d0b14403215901c281c0f54407001c0d10b45c034a800d10b04081c1d9172500f4076062003100c00e40000d000b104120345007059440322881c141920fa9071140242510420140c0500d0380d418820019541d084201a6010340200c034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 605708039 1250 605706789 605706791
    0x405240103050d0507110616200f04090201050a0c0c0302092508090601170c06210f070206070809010e060a020a1107080c04360c05010305090c040e030c0105011701 72
    0x103040340b03404460b0b85c8114440134100309038500100302c0e035150100040c100024214400700c0e24540c10b0380c46000007011ba120a81034218040d142e05002d0403e0041440780c010308070b40820603d003a640c0040e00a002d4449803004000403440854100f0011441c598040c43d001040751071149013031000c040700550741542050070290100c00d80d0f107480340a00340c11401399480c42c0103081d8513800c00e000c906200080c5804003085200b104003a11107074440741c0c01403d07905113002031202c40325440e4080078840040600228805080c02003013100c0d15070701080c91a000821440c02c1c268a45400c1c4030940502204070354050782d03000300c40a20160054503070092220075502c0c9c54010948078803c842a443c3d040c00d104403101600405480c1c03d40303203811f900120070508518499025014080c01110b9213921401c1014000000b00c410b03441070224a2151071b00400c400d280a008504e040307502c580d100c442d140041c0e4025a241e03c0550215801482070b528202001d42c0200002d42e903a0b01842400003104c41c85d00840c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 605709289 1250 605708039 605708053
    0x607031a09010302100201020d110309070803040812030c0c012c070302150a0215010305070503150105130b012003030f0112030f140904060e0601120e070509040524010305 75
    0x80d0940d4114290000000c0014406a01c1c5809008442d81000200000c40d5400c0101642c1c4075002d109080d600024007000da51245044c1501a00c0c01c04141c01c0769500e40d000b40005c02803080c0005c2d40c0c4d07d0740e802140c6a02d440782c4034010b884145000e0818009200e50030100d0100407a807901e888035880b40d00c240410011901348440340b54840c0b441d404040d41040d8002c4241403240980b80c0200340b1883c072841251500791f82900800190340d0280c104072204d400007901008180b07410071416a50fa100104c645209514007400a00e42a40401482c00015201c1e03040251076030141444010801718085648a2005004841d544a0b8400c82d0010000421500049110006c00c85000011541520781007500d2010a40554690940c1c0c4034150322014200020388140e02c81d80600c00081c1083c1180040c11b042c071400150183d101362a002c44028541404046107410000320141140d40036103a40d4603c0d111070601c2802c01c2d84848000804514001c2c81480f0001040301d014101e0740924180d40038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 605710539 1250 605709289 605709311
    0x30f11030709060c1401050f041506060c020f01020a021c1505090607110f0d03020406030b0907051b0c0603101d092805010c021c050415031503050f060703 68
    0x9680026034a40c000038101030014040207015040c00c0c0c60740c0d4011802e030a03450200341c2d513050030b65034103d6440134200054800d003c104082c1010041c01401114020700c41c09080400042c440710742d02d40e002e4490b4940d003000c0c2405074003e000082c00c003600a401281100007040e4100c0302214107000403603054001c1030748559110030912805008844c480b001c3d0400741c61b12031b021511200c020380302101a014184400600410811032030780c0c4491a500c026841d80e20741440030b13080310f1301000b4560040c075040c0100000b4540c424100e60b00f4030850340540e6a019514080e0070b2900300e050940d2500064000180300b007002c41010100e00301d540301c1120745014002c1c0708216510007010303103c11500b0303403203d5115030800860510002100400c101230000d01c8006454040c29150340b40082800740c1c000d010034011031540749040d407900ca200c0307091180c540344c03608080d04d401c1c09014411204150361030741100c881e81000f8040c40015034200303040703600340300000c418151556029203200340464036100d41c0c140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 605711789 1250 605710539 605710571
    0x5070f060f0c1b080d05091009030e0108060111070501030510080322050d0f0f020112021611010513090c090308072906091602100e0105040c0f0810020d0605040903030f 74
    0x8846640110011700f032465041004c0003130300c40a0300c80c14690250304480484120280b04014801e4000c2ea6800c4545050f2000034150040240c41030381001500c0c040400c45c103400041a80407501c0030f02c0c1c00512944d40c4014540d000d03840d90400c580e0b5000010710120304803825001807680e0001010f0309060703240d4520070402c1200744804002c10030b030304075907400011540001a002d0034500606040c4000059000c2440407a40f20342d400c02e17100e0001800080034020b04034040d00440c0000e0800c60322300303400102c500100c0c1c0c0c40d40c494050302d2501c1c0e00c00c80d11110310980c154002160301c500026120f030f11a19002c441c100c00100040c2c04141c42850704440e91504000c6640104c2010f0208005a140c0c012001d10320221200780b2810f510039828095a108214402c2254024550000207900d0038503242182c1196110f43c0324814408401105200740c000105030303110750391340260300180d484002501e4100502450744c0482d5101380340841d0002030641542001c030300c900100e101000809240100c41c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 605713039 1250 605711789 605711837
    0xe0a080c03060429130c091e05041b23030316030c021504141206040b01121a0403030204290414010905040e071e0303080705070f060f0c 60
    0x5505600502c00700740411445800349808510000d4050410701d969004e0215641e0152000c8070180b00d5a85c035072082c800f01d0200c3d0400342c0042c4005001044800980580428504041001c000c1e5100045003c00c0003041c0c2c090683e003510781130245031656640e20f0004080a188880101303072a4400c68080b00c0ca0040111040e203400c890100e51405040d48046544851941080b81c00c4103001a02803408035210010f4401080045007118280760017800380000e8038504e202d00e803400e600c0901804001035080f00c0c50743c190b624800308019211218202407855023044040c4d10300394a81101840141079254000b0020748040e084c50051180c800c0c401d0040c86491300c8011441c0b020b040c003045c85110301d44c015044215105241048141e0b483d10b001400300d401401d00302c0307603030352040c0030800c083c51080d00d81e410400d24580d85816020f1458501404e9100014100005c010700000d07850308100110b04003100042d004141007007210308110403040140720071486140441e00000c0c2100d01c9580850f403117 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 605714289 1250 605713039 605713063
    0x6090406031515140d080d18150f020906030606030c2203110306090d200f030a0f0908060105100c060c021f0e031602060c150109050109060503150a0b100e0a08 70
    0xc0711744507400d0b02e520007940c1010b0880d03c4520b4480840003012024800d000305110300034901d10311180d0040c00c0c030a0482c0d0110350005c0c03401c5d0050101036100c1d80d6440940e40e1241e405d440e1243c2da13a07549c100c4d03400c103440b40c1e51130a10f40c03e424030050141a40c858245c1030949200e584102080a6000c0c10140d80700b20840356000c4c0340d070000d003581e5a0203216100303112060112655002e40440d204150504100402c249202e040e030020a00c03004040e4001d480c08c02c5602d0b0781c10800c0105084c40101505c81b00c050140c86d01a440e41d07100c07070321002e00c80d1190141d1190044801c2120b070002d818020348807001c0c00d48070035064040c4007508055080b140b00340600440c0c032800171481d00e0349046929a400701c0707902090ba40309800303204201f2030382801d02c55103903402c1d514500705800e581040c2480045400c1170b088140040e00e030503c1840591000500c00c56100e071141c0c040072140e90b075146954003500c5a0082140c02c0540e113034200344200c0d0040c81c0d002d60403100301c840041c80303034958400035600c10b002841 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 605715539 1250 605714289 605714299
    0x6040509101a030d270602210d0513060c020f033001030b0f01080c150d0603060f0605090604050402012a08040b360609040603151514 59
    0x4940044059000c40a0301e9001210301e490901c02c0320003c1d0611404180c0c02d0046481c40c1d04a07042118201404003009083c04990042c143c100b1800954504000b041c500e410b0044084041102c5104410742c0c6198440c500e044c881031a0a41420008138440b58003264a0fa0400020500250012a005c42c078036000d030b4011401e0070784801c920502c0403101d00c45210b41422003109424040ca13400c20300d9000c1c50041c4e040701141e080800c0143d2507a80141e100000c06d4112920a0103155103500d0b104604034140c0f8500c903224001c5002c10001801c080d403001700207610b07141d501080c00b41250803400071114110b4101d0030903541d040a00c4140c850450b0021b001911811100b040030540c1c1800002d019500d100c030f05410140d48d600e02526501681007122102d00c00f1500d01880c110070020001900b100f840141e003503042c2082400e410015844500e0701c60b11011982042c00e84441d8030900c011a00704840418449220b00900d005105406a403901c248680a01260314200a83c07010840c04029103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 605716789 1250 605715539 605715553
    0x62d0a17090601031b180e102a0e060c03090925030e010228030f0e030a140c03070f021018091e02040b03060906030a03020c01030c050d05070806010809011103160e0a0e01050906040509 81
    0x2780b0002030076180030020240501490040440d4444102030034483c2545002580c0d1041030303000300599120000d0030400711f10340c044154071441c840740383c100b620b10100e4100030504070310480c0307440e0281c0144503c13503401c2105001407490041000001081c6080e00d41c80c1000300da00080d0120003601c00010742d021140c1d200b0000d1301441c1b4800c9004106011103940041d00b800244416181142d0103840706445106c0d140045000354548400f011030303900030034107014039101102c6005442d0b481051040c2d40b05982c0d81c0603141c046031140c080d01040301c03049100031540d89840f80d064a00c10340058a055006050000000361942400102c550342e441d0076800030440240080c00441c0a0030302d00104004216050200118103c100e01030341c0e000c1c140315202c1207100d107012000184401720040144000d681400c5110313101001060840382c01488a01e2040c0c1800703005d110a0b181c03595074044132074000643e00c0c000149a00004086410f8400444500c0c00d151900410002524070a0b0385014160304128 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 605718039 1250 605716789 605716841
    0x20a090b0702210f0c090603150c0405121f1e09150212040303152603040b16030f0302090f062d0a17090601031b180e10 53
    0x1000c0d0490782e100400041c01555819401c03140381104022107070180d0b210122034808010300307010b9009898401d9810508518241c40084da950300a050903850340f8149002264450381207404850203044041c00c5100088861080107690b0400d40340071011900f4001126090020303a4020030000c0440b0807035104402410001c000005c0540340300c210b43c94003001da5542050011400a00b0140e40e0742c0e0660700140c5024200a0180c41c44550020340c018660701b014401042e03007808002450b40a841c0480c80078003e0b00c07031245980b2a6401400b0030120100d000c00c40100b080000c2900548240d880402841d40004147d00b0383c0143c801c1c103540003000810b149098100603020f484e002c50024207072a501e203800c40c030a45089440c03111020036080000f8581c040950004441c103074480100d60b50050a18041c205551980410300009054008000200c5241202030000c68054503c80381200c8010245070b55a900a0806103929100c40c05501000e82400141c1d00c0b802840701a02c01c01030400c41200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 605719289 1250 605718039 605718059
    0x311070c170a0c1805060414070302070503070c0828050303010909081c0614030c090c0901091a04180c0804080a020304211a0405030702040f06052e03020a09 69
    0x640e48a40c002d00c9468407840118071803204610061945022210045600e85100d07800d6030702c014601405103013481001c0d4607006204000690000300c91038010f8031303100207190250540c4642000074002d641c900b10007140307107034002c204c000200e400c1540c52210100224545900b0390200b58025004d50424001009944950740180010300d101c0e48106180440c840140e220704150b40c40340c0c4c84040d5445106001d6401c1c6500b03118403040c4c0c120001c00500b03090b031002035038008005104401140020074084d0060340140e0041c000340a00f814620072100302c2102c0000320b40c019208aa01e010048070009452031103922500c80c0030b4881d0756440030b080e9030b40e40315031b1340341c1c0e11602068045110800c00001c2000b01c1c0442c802c0350b1401d0a105030030809942c18022102e1440c00d245030001c901c140e06000c0000d60000407584803507030659000c03c2c07105034820400000c05587c0e00994010070a2025414050b10424029114440801c03140c500c0003124030b4110203d029030404070001c10455803040c001c0e0810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 605720539 1250 605719289 605719319
    0x30801050d080408160501140711040b010e030601090207021005190806210c100e03060112240c032009010c05033001050603040c2c090d0311070c 64
    0x89042c1441d040e990f00c0c10034a442c00d03001d01c028058192245c144115a40144903d1010341818400d9050203401c1d2241c034000c00410301607a1290380d649801280316401644c162540b5034008040c0c810a681d14400e1a000c2c1d800380780100d124a1a054070030304031500647c142d80c0c0510004141001501d94070005079215180607044a50100e000034254407202e442600c200c07031a5042d23401a0440c1c0750b14905002d443c40e0a507540405024050a00c2c9489413400200241100e60480c0b65020a51450400f030440b9a600c5c003a01c0cde03000404100c0f42c001c000d50303500700302d280600703c0d90b0800030780700980d5001204aa2041003a009042d0800c000d454540c80f4050701800240640192480e104c00000e541c40400d0801d18001541c465100c0820106030070170145600610041c0c880d145076107400c3d91040003151060049100a01d40440007140040c04281e07078007000b00040d429820541410791045641d0303d03c56569000081c00c3c00c000300483c0440f14281d940040d401100203841606000b040540221 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 605721789 1250 605720539 605720543
    0xc0712080327060702070812121306090b0f0403080604060305060c0d24150503010b040b0d02190e19030b04020f030a150c030606050a200307020a091413030801050d 72
    0x111211020b803000c03400340401c901441064004150300c07460102d1190400f28043c0240003144000c0c850700f02c604071003981701075000c501c0041c0306001d51030a00c0e201c0020f10440c2000790202d50341008018080c0480501c4c076000d103029840740e4206503500801c00003540c0343e40c003004009410441c007107401400381c5009000c2010503010f02046072826170080880304003401d141e40700d101e00703030f02810010041000c074107550f050724a10b859480d56040c4181c95005125074131812070900800200111129429415202080a09903540084040344480102103170400d04056105600182c80d030000404051a000112a444140302d1182c1d80c0b1790b001c0080a00caa22940b40d010f0082019800019030791b03403104000805c12000c00101144c10850090403500250441e4040c00010000c5495603900911010600000344d84043d00e01400056194254010303000025040304007110003058201054000c04030b080d4640311000341c0d9a40c1d858001252486c0580e000c2c0c04940340400512103824100b18030311a8074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 605723039 1250 605721789 605721841
    0x29010c120c050a05070e1e0402100522081009152715180b0f0a1b0e040c02120414041112041a0702070e090c03120c07120803 55
    0x1d20030307200c65041c8a400f0b80210340e9a00006024452990050101380d007002c00283c6c4047d281100030f414482900d40504081d204491170118240b070b0318887e9040350101803220781d5070300100929040102c6402410301401c40980100c810800410081d03120352201c27190407041642918041806080040c03140c040e082d006142c0942c0f1980c0c008034441702d20002984142594902c2c10301c01000c9104803081c040c2c110b903510f190795481802041c0b540a043d9003042044858501030340b1520290401004200f0b40030300304d00d85486003000038681218001000440030785060200803580e060890712210f00c0a05280182c0090109200b92503c000001c800c1c4c40c0041d10010b0910145200b10701182c0085107000c01c0ca1600c081000200001088007040344900034001c0b0246060080b0007030744540c1c0d5030141d4540c0040c07840009503000400c2003c0b010781280035041d540710401c0144170b903115074815841018240f02700c5500184003040703401c1c69000f103600001d0580c11030f202c100e40071110f103048c507071001e01d0741c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 605724289 1250 605723039 605723057
    0x40906020a020a14010501061e0215090d02010608010e07061101390207210303060506030f041e0c0302130212010f0503071202100806150d29010c12 65
    0xa0403840240110603903600101450401480c0a80f101c54621040c10303c01c2c0d0401004000041e0040c948410300c0303010180d41061590340450481c90000110365801e5103061708401e01c81c2d004404038146104d201194020302c095034030388c00c0c160300365000e03400303100c0d810752000008001042c805c40c5003102200908001254000140c2184001c2000043d017007940e400510742d14103c03034540c8030782d000c44092081c0050300815141040501e018200e0304079081074500350310142410588258081000740c20021b100700d8480c141544000e0708110304a408840040e40c65021805281e52101124000c0d513204c0082c801550865080c4181c14140c0b0582c04601502030107030001420b01049143d0103400d80360302d204c0c5160b180404152812010381d000e0b0800214826401000da200d4000044a80a043c2050401a01d4035000300d00692040201480d02c83d5002c2070050f01c00f007035900000740d140348010fa05503281a446a03045244903480c122140882c1c810043c1000007104c1c1c0c7c1c3c500003501c0c0107003400080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 605725539 1250 605724289 605724293
    0x3300a020f030d0f1d060403110a051f061d0c1b010c110118020906040b0a05061206030705301c0503010e100506340b18030f0a0507020409 61
    0x10b142c01014250702200e448610441100003035115002c40d45848513103007005100d080003e503031180c00c050710140030003410300c1040b103100b43d08000411845074080c0458521184295107101c03801c035051100803019040400003d2408219220303413420354a410083d512507182c3c4018805994060141d0303054101d4412100d80781c01c80e081c801c408504180d9203030132810034050758003142101c102e180c0c0d071808059001d40a01c00350b1a03d01c101640000c00f80c2c0d00145281c50100010350002680e8081c0b03501c003d0000d440744482c8500d04505000d0242901100d4001d41c0300d00404c112a8410f10300800b480b040f1400440444020f81c0250b60401d0401d000c2e526408040d5106088081210400c413021a80c008010462940540e0159510107018007244084500b8a00041c00502c2140012501d43d21203070403020b44401e054110700c80d80d00700d0300c0007034420014500d4101940c03001211108460b12090a040c0300150002c400c50703e112620600f07452800402d04c4040e64250010307001641c10503914020940 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 605726789 1250 605725539 605725543
    0x70306150804120f0c020f0402070602130305100c0e240a090f090213030803070e1c050c09060105040603090c03021003140714030a0b0112050106050903300a020f 71
    0x11440066035a40700030346001c0c00d041c5030380303003d00c0580c00c1040f1140d401c003d40c8070707803103400c03008100c1c0e04a40c3c095560040100050103409142e001600252001840e0045042010085811684140c0c25500012090242d8104a521400640c004105c10810358500b034a170600f208001c481d86031440780f0907050740f03aa2402180d0440200e240114a4254003440150015103503d0000c24140405510b00910400100c549840d41e100045c007090000c070100b400280540c8404006200c00341403011a001224500c9685101f04001a074541c02914485441814035011071441b980b810303140e0340d10f8145006422170003044420020f0301d01c0c45560381c2c04070040c0d40c0c2c0c1c08000044240740d5400f20340c1e05004204501180c50140001c001d010725401c907010429902800d596006030b44840000b1003413140700059441c20308441c1000c8030186440000302e00341c0d4011001d03080b4004150200c40d000c4001d1810740c1c030800016869400c98066003901c0f010161640001048805054810f8800c00705021074581c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 605728039 1250 605726789 605726819
    0x1302060c2505120c120f100c080f060a050f0127080d0c0b150a0b07050f0601050604080307150207140616050711010f0201060503030403080306040e0105041208070306 73
    0x401603089000164024038032044010301405045822401c40510420203e1340c400062869074002c0d014052500c98000c01032000c2a900450300d0255030305808010b000d07100402e04080d0483c0490280c0d0b01003000b41540c405c4d070511410000c0c003080300e0319040c9010001444100f40303a0314100442400c01310401ba5240b070803040c990108441c95510241070103040c0303051040c01ca00321020400d1407012003001c6481801c01a070040c9074a5903d1807140c507040d0100d070305d6080d03a82080f1959000041c614007000700004608112039400d00c2913454590b2038100300080c3d0700c160b22400804e984244056004660501c2500d001000030180c01454903209903100380c100d4001c0e005005894000328100100c0c00f010580450402d8841d1400a18006280d03681543c07104c5210a00390401c000c1c41401503029000354008000303008002c1c1180e48a903503e25045a060b481291a180541c2c1440001060a401405076602950b07200d500485100e0744c01008442c0340500916403800c00d0384661000554042403c086 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 605729289 1250 605728039 605728063
    0xf0a08070e040510050415050702070317030a0506090603070302130f1103070f030506061204052a010e0307030c030206370e1008071b08030106020d02150f1302060c 72
    0x16603450b1600381241041080f20072a081a410503082100045c00b8211284120008000000c1c454407030326002c0b40741c0003041d040101040d14401e101946560107001552042203110310600540d51a50705201e0000c000740e400e0390301503000c030105100601d003680d10705500c00341a207000140110103200013800d4850424072813164407400014070685561203c040140f40b01c42d4181440541428800701e40a0320030103003c5504803801d0781c04136003048814410032036015141103140030800881180c2c01401280d00d5803143c0403951200b800f4889040c041070507811207811590f05000f0354075540a019059101414a480c2c6464403507400c1c0b43c07824180040302000d003481c5c071001c0048069a0010748101c40340100c1d01e02c00d803000d420b0715020a40c0503888a030f04c044503150908c003414039590345109544100000420616001c0000300c0c00c030783d0020300d40b290004107a08803203603880f048111014103001a01c480901800c0078001494420156500124151020700114a00311901c84040c1c1802e0054a071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 605730539 1250 605729289 605729309
    0x80423040e0d0309171b1006140d02060c1b04061730130e0606131802090303160b061504050d020a03150903030e011103010509131b0303120c0e0f0a0807 67
    0x101202e040c000c000361400108070150808c182402c4c4258800ba071654078041c00e100344601030800046480303400950301801c1d140401c0300e6285061682c2020205a1101c0b0305010728503162000030403402c0484422401c0b9601c101405001e0084040c4801500400d88030300f00c082c40800400c0e20f20001980141040044200c010401e10f082c02e61200100e0000b80c041441040305000e51540321070001c050604464604c119441032040e01d1443c0000380c018400716175414040490b404030b42c4880c1d00e5000800d1031103401d00f44000c0e60b89004001d99041012018000e07018180024022800e100071000307102400200810a0b5550720394030502903442803044051004c3e05c9001a00030150140a111899040c04000380040b040741001d81070329010500c50300e4401d103492000700d003810080940005007660032110180c02d0300c801540010f090459484100c0c001503800740500b000d150284210400400c8681d1b41848a002640402810f201c3c00701c4015440160301c200060582c10400c042401058940c907 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 605731789 1250 605730539 605730577
    0x20a02150c1e150a020307050a08100b0c0c090906161b021002010e070f121121070e06010e092d090d02010b060301050904080c0a080423040e0d030917 66
    0x1444040000f80038012101050050042c811901e800c54150f44400401d0b103004082a6603031150f21510b040140d01141000c003000814120000b408203c688451100741d4080301c1a4641c61111076030b600c421201000314000210b25014007521400e00350050708030705d82150740c50f521a0740004242e02c3e201520036025030356804564000a50601902c00144143c120a20001c0d14041c03800e02e00024040d0b0003004010000c80d2444141d440500300410341c401c0b041184041d00600710040c1c2d46543c2c038016880104204c0340040c3c01588103100c407494604000d4101c5903940c440100641c8160740824042000c2c0b00c07011545801c0c5a0740e4070006116004200c024035452131484030182c02c49460261040c0610001c00c018003154441c9404681c21a40c0300107410354680e807210706070707040a1100000030704001d400540080ca4003042c4003000d1354550440460715541070100f003040100c400da80104500e94201c100030201142c0264000c540306030061045088405110941700810391200c450240c216060312 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 605733039 1250 605731789 605731813
    0xc050301060f020d0207090c091a0a09090506060a08090f1b1c050303070e010207090609020405011409030c0f010905041d071a0702040c2604020f01020a02150c1e 71
    0x20380d008079240c00310f00203003031010007400000303490354294007500701400d49030a050b5200f0792240810b00c00400600b085008034000d8810300c400d541d401b09100600103051807801040c4020a803090501450000302168980b03c18218180d440441c01424030f50280250910328401d008244a002d01005400b04c076988111420b6041059107007403800d5074505c40c0f54460301c0c0000603070f000003125001442c82c1402c8841c035603a000100d241c2502c0e86c0200d810700b030500c400011640b540f900030b0710a40b44c1c240c039a80c07025401c044008100d8010440b545606a012240c0c604460424100202514106240200440d515803021806490380354006070486800120320b0500c681040c461710015040180d00d0201034052901e00092a004444010f845250b5504041100d80c0c0101c02513241000c182c0c0422040944a24244070342200031a0240d010300000240300d00d140d840400d980b0422a401004004160340c4e41081d400300d5000340d07003109171900c100c4505802101038a03088291005142d0000e03d2160690 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 605734289 1250 605733039 605733047
    0x30b060d0f050619450c0801051b07032106180e060112140a1a040303110a050a050306030106080a0506090c0d150c2003180d03080408070c0302040c05030106 69
    0x4c3c0b246542c155182044212850400400b40c0014107450700c01c284071030440c50401c42011201c04864940514042000820040162000c8045410640081103903540719400f162901c006d4010960f5460001c004050000b4080c4091500310401502d000303040c03c2503101c0c51000c6548d40d42244030980f0808440005c49011405042c02c1c16480001414455152196150204d2006500144031141600c040d00d02020100003444042e5000724004026100800a20381e80302011788064001030f0801c00000d400341c03600c0341200c03010051580e803030f4501078428104880741d810207058070740c0c0355403a900005000324040090741c801340d004001078541713404d02c1c2c50094500220a4401805a070799240c2d0341d0045603900c070108003002109a80419841c0e1441012035151011081000040c4d00d91580410b680c0c84c000040d0920800c506031401060182c2c00821052980302d030401400543e6140c0010000b511800103011010f1041c1101007816803284c0c002020f844040310b80000145000c40100156540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 605735539 1250 605734289 605734321
    0xb0c160b09060306060322030c120f0509040c0201020c03030a0b010801080105090c0402070f12051e090f010f0212031e010e06030a0602091513240504030b060d0f0506 73
    0xc0c103824245040062030100e080c41c0401042203102c1d82022002170a10b40c3c03600c1d14072840c1d85160141404c0b000f00c500d00501240c3c203581c01074441da4401860210740c5030181d070780080300b040346843d80b50801780c0480401c0080d0481c224140f045540034446803040c6007080001d94083c0e05403c00c0841c004180b40001010064142c0c860f003503981c107020910120500c00309030005420802c0e2070141e940d40c058105140714904100b0000c28540d9540080700360b00e5800800307005000030b294100c00c4030710400c100002c000e005120840f41d1005443d2801400d80d8001d01070700200849a00580714005280320081520b0f4100b1112031120700c04014001c1c1040404255031800750119030241005030038604046a502c500040c80245442d078000b50102181d551b6442ca20309440b00701c0384c00d99542401601e8460784040340c0c481c103a40c50802483c03101c0d804041400648440d5040d65030306040902d1901e88400761b280c017500c02c2d41c100440800c07501c08181240c04140d84540200020062801c1c016011902112 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 605736789 1250 605735539 605735549
    0x90b01091223120f031e070c0201140435030406020109020f120d1d060c15070c081c0b060c0c0306150f120705030a0b040308010b0f071203060b0c16 65
    0x200f081c0003125003890a03184058160b802640e213a030350300c0c0c0391b49100300215813481d601c07074601c201040300850f030002003074514900c00c4c0e942c02c1c640395000c0d040c44005c1c00383e8014400340e140c400040c100e6000c0030a440030501c8861140b2444031074814440607003194415001140140d44614040d000d604000f10140d00580080d80c3c41c0b0b00c0400c000d05030585440c0444281c10070850008181401d1140031083c0044041c002404607982d6442d24000981d030320142d4440418111101c400146401d000f44681041e660300208810701e0407101403110804014138001c1c0340451a603942c520243c50b22a0005080d22024010017000f1340008074042600d0201c3c024a0100c4031007860f80c01c1e802a03110010010308a0105030b6081e0440300c550303d54241849100e8010701e81502c10130340004248050350560740d000358001d071190f0f1000d903200c1940c134945104000a40c11603d50030446000000c0341c244001816040515001506c00e072105007850f400e60028a440807941c0c000b020071000d58164100842c0181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 605738039 1250 605736789 605736793
    0x50c0c0d0c0e091606050313020a080a1e0b0c0a030905060f04020111010c0e01110c03100902090f011a03040203011b0503180102030103020a0308070c030f05010501060801050d050601090b01091223 86
    0x215a001984c1a00100d41c01980104000800450b100706407034070440c8800d40e80285154200c940343c0b059a0303607800b25040b060703070444840c00307c1c1e5400b421001084d0001e03542021011856583d0760400c00aa41c1c407142011040541d039220080200d9030501407540202240080e8280a00305070000400030400c00c551800c0c0c5900d0006807680d8260044d5400250200071f00706201900000c081050500484540311a0107004403c48070903250815448260b680303200702c40b5060192182442829149424010400a01e00700150841c0b841200809140d005100500200d15070100040c11846103c00c42080404030307c011050043d848092680c12029420800085080d50b1540e000501d00d80e4903448054103c2030006220f000b0300100303800d140b0203182c100104d6200c0100c1031508900a050900c51b0b0800901440000305403842d0240980d03100c1a04000106a241d003008a4880104231825505051103422140014032103001f0518003540b5014664001104548a0701c0b072102800c0c0103407440d40341e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 605739289 1250 605738039 605738053
    0x50702060f0f0c0705010614100518040510051c0b1e06060333040f06050915130e1e1207140726070905011203050c0c0d0c0e09 56
    0xc2040c4103069400307500c0d0300761242a903c2d40000c08240744103805025182e5400d229010842e010351000200c1c49132010b031040700c190900400100c0b0140501c111100d1303185900103002d50030b481e298012507004098003003107009065503100080d50f680511004041e03c80007400410b414441807004155000304081852100d07029500360800ca811002000f69215035008404078a80b0510020f074507165081c01440c0c1c902418140e483c4070b0304002080c0380144500c0c1010724003001c00441e4014803084400162000d00d0355203416404440040c02c042c5490340040b450400d60b0003981c014015122011081d402500b00414100340d1503000741030600c040141c035440038021079204c0c154081210030070307a04502a00d002e002e41c525804d007030903c5540109403600101e4034050810242c40e005a48280d65036003100d418603521901c0a0a543c8248640d040407200d40340e03810b010a01400050021034560400e940c0307000c0c06440007440f19401340c031090f5080b10038060300b405850b0704443c280313801c210390000400d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 605740539 1250 605739289 605739301
    0x40503212703040603020705031902062a0a030f090206030c0405040e1912210501061805010e010f0c020904081201091a100203190f090617070e0d0f1505070206 70
    0x2d00c0c41503108010805900250b50000d003d0280180d82142e0f040d0b2060158100d101d1340029500c035820345100c0120720f104048240c000c01c220301c1c20b1450354403d2170741605041c012401130707000b080f0300c02061b4282c039100c0650200583c2d0f403000551243c1440004141c1301c609000a01c022188040207a140d294804815282410180d041c21080d047c1e1000740d296020164040844103d1040c248180200f01c5149a011a4402603000141a924580d8804034100058661109099101d01c00c09000c00e41224048066507c40d1102c0c1048501d642000203040040d41d000c03c001c072504607001d80704c1c05c4000c1001c0345442d1900101d240140942c076402d004803018070aa581c446207600034503600c5551103000381c0c05180e00074030640748032000d2180c003981500180309004d4a070000f50300024000404003d0302050103030180c0f015201200070b00e45071003000e598111090302d203513140031000c650041450b200a0b001904007900010381e01d1140b9130481c02204850401001c2d91405025081990000010000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 605741789 1250 605740539 605740543
    0xe03040b040509040c0305011b0e010e130c020c091602010c0819050a060b070f030908030f041502070b040b04060e010e0d03030b040e03041202030705030105070909050405032127 78
    0x19030b8030840e440c000503101d070b2503d41c0b8884556030008090f5401c00913031551407134202c3c4072110080c0d0310f03841c1e0142c400ca040f001158020a541e10b459880340009a000e840c01d803880d80400c400d81c2c442c1c0101e9500f140007500280c00c0e030030200d6400c01c0c01e0001c2e00b90040c0e035940c2070054407040741c0c140c2060a81400c0004418414581c2c690b211320300590380d480080c1412000744c0140004103421800199525035500700f500016042c0c220aa000c105401ca0005010000204444c4d088240e094005d0426040412100d44100d43c03014171021031003410404508454548028030040401c0b6403401e55036446c2c00005410b82c4000300100781480350b503447ca48450b881d1040741d00412035042c82c0c0040c80e02b10040005008121441d4a94524440414049103010700700080d902c0260003182191106a9110201030984200300d9070880042c01d40d103010803c2d80d406030089038100e0710036010b59081c50380311403c09081108070301a541e000c50210043c4801c0d41005031512592034503d5001850440050301076503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 605743039 1250 605741789 605741797
    0x5010b03070c0f0c2409140d21050c01060e07050a030e0a0b100806060607050a0201080c0d11270a0b0a09090606090314070302030a110409050f060a0e03040b 69
    0x2001e00c040703811030344108040500c00000f015405a141080d842c0c0700c1c01210038145105030907046000d803c145803018030f40070b401110120340b00c001036070600081c06414480192940c0078103c402c00c0340b40e03004040304210034a10202040d040e948030381e2901010000d0500f0f6030802c0d845209403101c10024881042c0e0b010b002c403200d1b00010304000c00c42c486005055483d00c501880c002d422008004180302203125030003114403c68a104045a92945a001c100281481581c0d001411a0300018841005501641a80d64420070042d1882d00344681501170900343c036070003040d0310700d038050001e5000117042c042416000c44682500e00401c84003070b080040f5074550000c2c000e480288102084401c0c40e00c0c41450000c000d0400030b002440308035030300d10024101c20003a000031641c0381820f90742c0658003540044c0400c1101e800034010103000c1c0c2d060712000840700c08141c480350000e4540740c0180101d40c041040c503104003503450003008d4618000e240c1a04031030325108020403e800400c8100480d0301c40341d05903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 605744289 1250 605743039 605743051
    0x1803032f121f06050405040c090b04050f0612040803180a0312020c01060302040f0203090706170705031e07020706120c05181c06020d11030108030a030f02090d150f05010b03 76
    0xc203503544070a40916282c2d0009649024003840c0141d021070f0540e4003030042d00442c0d01c290b0f014000c01c60604001c1d141070740326024104072074109020400035882c1c00d0756010b440000260400703140c11140d00029081d20b00c119010344200344008180035940188070100420b033b00e5464007500c905107095400030804000c03241047d80701500850401c200d001c003907210400443d401802040003414a11044020350400c4070144814025040c00145182c01081c81d07034003c0d004440901d94559503000e080d0b405420103001ca00b000ca070301e1006007018424401c8401e000d9000c5800803c8101c2c90b0032402404881d4a40a40c0e040d40e0400714a0302d0100d07048003c1d41c5003401c0101d03007002c600034520b021854800240500c550142c15280d6020280a01a070042c0803600c080390042c02000340142c01440c89100170300c40c842050340b081100d2036180c2e1081d0301c12a4256001e003c00751610390000700081e44250700c03845c10f8510510b11402145032503c0c0d840f4900010b400d600c4c0500c0650314140f00c802c040d01008000e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 605745539 1250 605744289 605744317
    0x1805160f2c0310060306050c071e0309090603200118090908091f0e0102010b0901030b1b031005041401061b050304080102040608091603020f131803032f 67
    0x4100040800c1c15542410340c030090100c5001c140d0792807800300505103603c01030350020303e03007004501d4090710b0300200c9585035000fa144014200d001300c01e508016291280a8040080ba400c000c030f4480802c0c0030342c0c0c00460040c2150700d1b600209a1080c00d030384855010f0380b8103110900704a0801030300c1207600e980c112200807000040a065034105441c1600c50065482d0f400314414040d000308041c5980c004408103000d541d2900000752600059080b100c0d154001640100000010800100b2404059910000b00e0851030301050700a81552041e400c161614800e0410700c2a0078005400c00e440b5a030950301340b045800c20316506d4100003a002e01000181c036118441c25003290340c107010041003183d0091003070707000031542c07542e171800020106101a9540d64081c01035041a0403c0321030890000f09803038008000c1100070b040340b010007103802640600003072515254030325608551807200442441130700a840100e501814003070b07040380721304c4c8560b1417811002801c5207940100050300c3c107a940d65100c00a03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 605746789 1250 605745539 605745587
    0xc040810021801090326041d07090e073e1c0c0b2d07020622150c0315030f110306071205060f09090a0b010b0c03221805160f 55
    0x4102403a07c1076401c9415541e000503981d000c181524540b0502c503217031a41d64040c0503034a071040450142030a5486c0300000d210311844902000002c0d00b80c1501405000b009000f400a450041e126801304800c01c406540081c404036400386800b004000c8480314a24003800c00e07400703698520301010805050542c4201050348207581640d410010200c2034001012a0b05162510f030301c000b952030008840d500d1208000d190740009005c075811342c410806504c28600418642e085038a100241080e80c0c0950800d521009940030b800380380b809101c003960184140b21407401301418501c5684d20700c6010036020f9030112042001d0558004820082c0c507100040c0403543d0b44412001070350218240710703070360360102145051004541000a10303107090b52203031020801980e42c41c0d100d40118001c900e420806500308019080f40d406440500000c0c801094000e03648140d1038a4820180c590840c3d03014a0301d6a5034004c0c405405800800e60708007240f1490311001c21340c00030030300524480300f00020076801e141c40c034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 605748039 1250 605746789 605746853
    0x80c011218170c07050d0809150405040c1106070c1a070e040507030b13020a02070513090804080703170a0f1b082b0606050406080c0408100218010903 66
    0x70120580040d000184202040d040d41200103465014000000c40b5102c1c1040002d814201031170510704154001186d541403004003014460052413020320001352500800001c503496030b83c0d11481d9110b05090340c517200a0b8426051480c42d281025042d0703424010040200b4000404103000c10b5606c00c41100400059102c448054641d1205c8461642c1e11038140420070400300d034190b015501d402001c07141c1481c0c007180c4034094400c07441a003403003d0042c0c0100409010318140007904164440c80c22100058010184d104d625140c3c00030380162141c0c0c1c103e90810000d002d0306215944248998015152030200c2000001e0041d651a0392404140010400071340700300ea851201d0901e01541145946582e0050a14200e4146902a081c2180050460700107107640e4010300c46d050940c1c0264580b6441d0608103d000d0346d807010002c007000000c01c01004003290046052140d554014403082300075884000c41404089440501100c441c100000d1030020000318507401130340d80341c0c0c2c0d40404d09505002041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 605749289 1250 605748039 605748071
    0xf030807120909060e04150b060d0902120102180108070503160309020117070f03110c0d0c050304150207030606080f0715031103010b0d141e2212020106080c0112 71
    0x150f801409582d19010300042c581004004052280b07120b0724141c2c2030b041d684181e510480d202d1459464100409015850f41c45600794407400050340020181c010b00105401c010f420780c1e02030740303800040f0030b2039004030422541c05c01c0890360410502e0800320b08514200b022421849405d4205104044c0c8800030380c02964041e4040f10700141f0080c1c0001c4180c0b4080501404003592009000000392900950b0711111721504141c07084500043c02130620a2070000b011600409000310546080c0010400010600e402d4040c1000d10502a0050b041040c95424200300320b402c035610030f80040d00a6554945042030200d024800d842c0044014104000790000803001003600c648101d880c03890000c00441c01079600300103080000d285076007c1c070034003081903805c22000e03c041c1d8440c0440180c0c51020283c01d1003001145500516408085c20105500c41180c03a070000e1148003a9440d101c403903241c1c00f80c6542806444e0142070450010f0110103015070009000344450348031400c2c030660300c5154040008103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 605750539 1250 605749289 605749307
    0x809061315140f011a03060d0c0512012a17100f06020a020f03160b181305090c010905240d090c090605031b040905011d01020901090f03080712 63
    0x81c03500400c009000345201682c40d01068480b40003104000e4000182c200040142c0043c0b94600d01180781180c40d403500740114119003040440f40110804c8001c2404d4890000c00d2880510480010a40d10400c820f00122501c40c025603030040000312480302c2d0046c0d00801e00014160b41180c540e60241c0d112a9502503115082e004100c100c1c82000002600d281e0004209038480d00031180003003051030301410160740d1301600b10610008800304030704200304402003014180c00d403030001514441c41c1000e00025084c0303410b0740860b4003440d41c82051120440c0104a840040c007401c1c2099081d841c20040020a19840681d407400c00c0f400300c02040178425404001c0c3c03044024940c8003400494a10316008a000410303000c4d804409140940000300ba00e80052a40034a51010585000301c0e1401c8003404003405040c2c2c41036a9640d281c007049403c6008010740007401c1a090800181c8605001000503e4403045501800c00070001103020300109078200c0450f980e0f55070044140c1a849203401c01035402c242 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 605751789 1250 605750539 605750573
    0x11040501120c08060f2710020a18210804050a0b1209070b0301060c020303070f06021b06060603071107031505071119020f0105040b031e060108090613 66
    0x10500000040107800c01004064062051a5008000d516040300303036034070802100c090f07030080994008202221100446072918001d50385c481c1034011080074000345409100080450758a81c006a00d01304181d1125002d1b800c0358000c7d00d03c015903842c04a0f0949060704880020b00c010640e400b46c00100865102107600601018009039071150340d580540050b07407ca044942040448100000c111042c007003803c10072382d020038441c14210b908000c01201c955000d41c10407030709031104001440105038039010f2030112910440d80903039980d0303d0441c22550907455600401041e4072120500c0b4a503640c0c941a00d03408400c0f032a20401104500005c58540511580042d00d409510400000701d4445900258840c442d151107250720360b01c2145a003652510700c00c840c03001124411031810018540100580c0810405244c05c42c141a1500790345441a0300685e40c421074103403aa001038480007180c440980c0e0140c1c003405e080f0600d1503c048810b44580307005006030490f5902c01e071082d040201715207911031404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 605753039 1250 605751789 605751791
    0x90203150c07142d0703110105040803120118090f06090c030803090307030306170316030905040c030f0f1415040627060b03070c14010608160603060911040509041104 73
    0x1c0c481c610983c072201d02c00000000480c0344810340d220083c1d005a1051103018281c020324101d4510707242d88071f01d03071031000866041250401c00028800010006040e500040c0030240080354904018100328a900e141c02040c240d003820b04c1c002c045408001e00001c0e550b003106020034034a40e07070710b055100d13512076420040003140c01200380050700760000050558113100e0340b803c0045039166040781c0140d9442120030180c0d50710420001109040040311a4880d5100b824010081a00c1d000043c1c1964805041440069030f01c841105807980315003d4020120704500c0b040026003103501c1123514041c00209201c42d1300065102440c0740f6280d55004200503e19413420206043d4002e03858406180d0683d0600c11140c2006c0002c00d400d01d00c1000c5900442d11078503611000c0711990784441c4100300801100392955a2a000056640400d010300d10020410540000f420303402c180c006001c031841030301709020080ca00340824100444440071902079402c1215505076581d59440d01c02034007240150b910b42c220f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 605754289 1250 605753039 605753063
    0x20703181e18110f071a190209030c031906050a0204050906060f0f030403030e011a09060d050703050a12120203010501300f050a1409030904182004050a090203150c07 73
    0x10b464500c001e0041d0794030558440b1840728403000001b40b011130594001d0324807011300e00b15000f283e440e0360040098010240580e21802c1581e00000d08002425600c0d40c042c0030704442036000c018042c400e0590040d4000411030400e1b042c10040754000318020706840c0244030010300c0014034850081914044050072255554900d0145030081c041e1142c00031201d110340c28600f81c04680720790241e08580301a40540714100315a2440d00b0012b03d000420010b4420740038074480480421004d0110481041c010149102c0d814032010b801030120307105504c600c0640c0e106100500c880d03070340902c04c004500090640280365003d800c40803100d92020204040c1703240d1a06020340129130082d00010310034250441e0802860f12081200d0b51442c000b03c612507040d4004028031603c03850603502c680a0750000e003002041c00b03030050351140c0042c2c2480f1841002e42802d4400b1041c189001c2c0600e07640200300e124140720130f02103580030079550032f0f1040703048200004610001c0c000d4001441034450198102801e0605 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 605755395 1106 605754289 605754307
    0x1410030209120717070e0709060305220302070905090c0105030a021e27120303240a1205060a060503120f0706020703181e1811 56
    0x300000350b0b202003660030010408000503041c0814210740450701403580c1d07450030b81d460740100c1402020200704441142c0c050f00200c1141c01c203040c003090b5529001ca0310315180c1c960107c3c01d02000b40c1e0324241418540c1c00502002100c03540c0a00704007586a150741c00c1d40314000c0e420050b010a40410120303241007034640c000c10801844941e103100007000112100030543c41200d804000c1455508241030006110031041e0844800715440a650010f240d81241c0701d000c020030306680082003d0745021800c0b03c00700560303004600145428015519081c2e030451300040800140d0351803050b0300c00648980564070408040da41d0050081405070031070807503c4219400700059071f0b142c4005102810028880d4005800000e00c02e03120b128070010108a5210621400d50005810103541840458400c0c0d600481005980c0403600081d00f417030a46541c0d01c0900308001e1461801c500c0002c0c0310074 = true := by decide +kernel

theorem cover : BRFrame.Cov 605575539 605755395 := by
  have h0 := BRFrame.cov_init 605575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 605575539 ≤ n) (h2 : n < 605755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
