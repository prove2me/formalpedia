-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1732
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:28:13.775976+00:00
-- url     : https://prove2.me/submissions/27a06ce4-00bd-4c6c-82ca-45121f421739

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 311330935 ≤ n < 311510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 311332185 1250 311330935 311330939
    0xc03020c031b0a05030a1d1e130605030f0a060b031b010c03090302181b0c1207080c0a0602090f1e010f03110d060e070302070c090f180803070f020115050418060204 72
    0x38110011401000c8001c2601c0e511500c810719000c08c42e10107954002224030700ca00c0e0503c0900c03036000c0d40c2e1903062400d1900d44400240070f44080011036103804143e405820415810302c4e064040c2e03001c002d00d16200f640710714482980f0443c07041d01100350103401d082000a00555150a071614001a0300183d07114800444421643d041241410301c200f01c505200340840040100d0707034615000d0303d00c0e8442242e111600b02d44810040740001c280f403502400840c1d05084c070300e003043c0303140414020003150b625802054181f0542001128078034041421209803480c07140b41001c94000c600000200e50410406c49800980c142c06030f403098603202407420b1010b9443d42609038181c040d1075140301c1c1b4139a1000c02ca000510a038424800c0d55120795100400c520b9561505000e980a095a9803100d90241d94900000580e05e031210700d5011702e540b20360407843d12440c0c5191b01900c480030b0001c210007564144012040d04500f000346510940e00100c2e00000c2503001114030007209003622000400040c070000f80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 311333435 1250 311332185 311332187
    0x100506070305250f120f030501080c0120060c041802030402062506020408010207020909070608060907021501151d0f0616060c0c021c02090406020a020a0606060f030c03020c031b0a05030a 82
    0x120f10004a56919a03084641b0511b1003201210000d03c5900882d800c80c941107521580300b1000000c418104030754110030b02d243c1d01c490b10304040301038030001401c248c00101040102014041d050380d405501c4011030540c0707000e0300440c481d40b140910508201050a154000540d0885c1c848841c0702d810060443d2038503242c03050785000358800302c0164480c00b0030a00040c844480081c1038829100ca580e2020300070f441c6c031001d00440c00c2020b0315040030350003126241e00ba07240c42c2c59406802003c04c0c907100c00d0440d500c036402034402c00d05101c50901407940204d400506880c1c008090b42c00c40c10540304956245080300b921062000d90b084002c0c0002d0074840b800700d90960007100240898005c84011111000c1d105e4103008455600c00000e401085000014021a8082c0d001d00265501070040d2200900d0568a0000711100750700810042100c41c104424656850702c220001e1100e1803c0c1140341c2500002c215550780505148424031820b44440c1c514000400d00c03441611039030050840742c0742c0300c2d1010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 311334685 1250 311333435 311333453
    0x5090f0a08090a050603040c06080601050c1204030b150d12050c03070f0c0503061303030515130f15061d010203040b120103051902011b29100506070305250f 69
    0x41c40707a02c03d00640070045440d00c1c012040300e0049602c011440c0700107151041c280c2e0f24442c001d003030a06000c1c0a02000c2840001842400a80c01500b0043c540e00c42c00c524002c1608100a044403083c99605084074007035440b01036100b17045a4002001c0480c1c40401c202c03c440502c03d102400d1028080803840710200040f0b90581207025208100f02401c943d2141705155450008861440200c02c0310703400000802e010b5800325030845900c05d8032154403c40c15000c104200d820a0300380030960340d12400c00342d005940b442184040340f0001c0281c41b030585030080040801c000030206041c140a1500054820703802003046030000c04a4143c141d841e1115036002d540080380034071080c0c1e094014914540c0c01d0709045043c85c907400382c1c140c40c0c544090055909202c07610881020403562210069650590903001080f5541400c0c41d07111307904400c0c9020844541c003130080764001802803109101d440006504030742555501c489032004140c1c0c100c8204e039a040510700703084000d452460956558010312006072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 311335935 1250 311334685 311334697
    0xe010501090c050306030714030c06041214060603032712030c07060201061a0304050a060e03090109140d1e0f0803150901030b0105100e0613080d2105090f0a08 70
    0x100b0400302d01e0901065440b07110448001d540354000f94802d10400c195005207404c00310024040b00c03071140300d8001061685c1d00075000400c0607070300100b805080001e0740070200802c100d80d1000d08a6420800042590f034003d10b10000c0da5451300d035004c051904000c111030b560900c00280500241e0542c0c600c1c41e0745075442402540407900622102040300c50050043c1000c980242140b1000e95210303240301d00c0700c0e400c0a4021100c90045401d004041501409a00245a804005565589030460000d00780c1900c650007451004034440a410035a0f8548650000c80c503006504040313a01c41a900144000060503401005940800081401e004180024501c60b1020400c03000c10704119030108004614248070080500b141a030040c0301c0d606140706400c401c0d480d82d0030b001c045d50251000142068001c480203400c0356822080c2044a00820084008a2000c41c1800c0703801c19a10030205141d00145940d0001c15501d50380421b04400c0c0420038426071007801010344821010619040c2c04581c011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 311337185 1250 311335935 311335949
    0x130f060609052701090b010c0c0e1e0f0c131505030a0b060903120d11040b030a180f0b13080a0806030706020f06040b0408040f03030903021302190e03100e010501 71
    0x1200007520203c070b281a0485600c81241491860303182c0348010029045c1020310754100300722120508001395200b4108400f80203800082d0f00c00c0d00c0c06a42140708008c04148503581200c200d030600030100f400400da1a04441c1078428183c3e0b50b10800e860785003000c80c5500105070444c00740b0b00021001d5011000e14000d034807581061064a4020302005828000c1001c4568180c004028840d11503850400608050102c118013140c4804562103074145500198050303121080c00104128845030503210780c100303050817a1100180115a5110008034021201c0010006081000401c0d1094010708400500c95809014541e40c2c403911030000f40340d0f17041070300c450340207105402c0301150050020441c0d6980e0007001d802402c0340ea03590340b540e00e42044080c1c01610041010080032074000c00320301d244406540a43c0301c00c043e075441c51041c449204035050100a06501c1400304040c20710f409502070010311128640b50682105070ba0020b41080b0391078081d651014a00441a640c10b00190070250481d244 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 311338435 1250 311337185 311337199
    0x8160503041e350c1e0405130c030602090f090411040510050112020f0f070b151e0f132904050412080403090b03100e150906130f06060905 61
    0x150720f68001d810090100590524901541d10080c840d041c3c40300080f106401c0c400b00c48152014002082080c0c88060000c01c9010040300c100c07103203040c240285078121380618100540c029280e182c5010680c26404024109500064205695a1410700e1700318420f10041c590460780c14a85001c0624a40240c0712034051824140041c541440d1100107800711031040e11071422000c0e00102c600000e44c4000d5410300324600521222110002e200054000d0a100c3d0000344100e051003500c6a02c00c00c42c001d56140300f143c0e904110104400050300b0721820100c00c0c2c6501c2c68801d2640009440454400749001071107141030030003c050105d42d00389049811300102d08403c1d04881800340819905c0803a8007420f66800122413449541c440c105080c3c1c8030b400380c41e0000d0301c291103203940012680107a40b00300404030842c2c018840034003020405600900300381e07609403528215130040f808001c03006000d18821900d0034110880e01c2c11310703004200481c1c02039508010543d1a90300c0605000c82d01d0007403a000c0d1170 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 311339685 1250 311338435 311338439
    0x40212090c0f0306150103061815090b0a0b0a120905061911120c0403050703050606041d0709050a0207050708070e10030f11060c011b12020a05030408160503041e 71
    0xb003000010140b104058050304895562121052480e5100079440c0d040540d034010010307104100440c0c00b01400c0c00a4400714010000d5110361494074025001210614508801d0700e01e107a55125603101150075590000e511109240402d4a851120f140d624500c02d0400e40003c01f04400490740c0f074895651248030996211040c48401c0840f41070302041c5111501c2081030012200740085142c1c0d100080031003417441c243c1c591750798504210043e44112416400310090103050302d46805081002c00c402511100c03407201c030362042c0d0ba40340310780d20032a040c86642e0004240c19440030b4044a0490340c000301190b10b42961400d801c2e503111440d100341446200c42402007031403511a803050350100e03038000c0c10703001e0101d03003503220250000104031400354405000c100c08035041d10300307000d280c0540b40c252042c031078844520301001d030080740c03d4560308941c603104004080c440354118058035009038002040b107490708074040f040c002c2500381c03840140892001160000c2e402c5d00d0161003450a44040e07540700070130380d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 311340935 1250 311339685 311339689
    0x6030611091804050a050d0c0501060e2401050408010c0905100c15050c191d0603090d08060604030803430807120e070518010b04030201050711040212090c 68
    0x805409100c55100c0c100744142c1100c046202c108075009070080c4261000705030b03c0e039504d510740180c0b280050b0114500c49091018084284a27040080001051425442c40c0c048200b2040c4407200c20185404642d18007104a0307a44103800340d50240107460b0003007100350045080908030307000c02d01c9080d1040189542000b5240d21500100c91400c0c1e12054203900c16034a0103001d006028018102c0c0c079100801c2c00110100e40002c900c1607800e0001c1d81b207181803000304014012681803030000150003507100700203000d512a0700003054178644003e4a05981d22340c0b1400001481480703203500161000c0408030030f00003840030440b035050322003404002c104040e600911440f0516040c400c00b00002c5030100b01d00f00f55003405403900316480f64080c07400141c0055030003804001c030380c0880304201c0070381c1c800d541c01e110900b00a010480e0f41000f482d801c0c8115858548407503810300c00c03800020304200700454040200120b80102401d0590028000e54448030040141402d128003103940d17120324030600c1929a1741e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 311342185 1250 311340935 311340937
    0x130512030f0412170a0204030b0a0c1407081c0c0206150303040909022206050102190c1221021f060e01030f03020f0d0e01090e0411010e06043209070203160303020c010f06030611 78
    0x203c00b292240e499a4542c1d0030007034000c1d04221020f0b62022420484031b01483e8251085040182000c3fa0010700e1910b10a002442d00b030b001041c00440a402800d0b94085a8002042c5c504481d00c1c1c0343c1c0860322009a1000c503e5580707101d0380030950b4100d0b20440c0b119145498202c041510020307803c861038440514280492946011000b404800c0105028828124400560341c0414017560004c0d100c0545900112140b049102c0580c0058000d45d032286c055100c10b21b09001d034020840310a0002d0360500c40c0c0420740c0d11043c413008000006002440b41014000c0c4030f00e910f40180501550400c1c120340c0800f414000306004064006020488040703141c2c85d1460115015a40001a60060150204c011b540300300040d800158000c00c24040046c500251980c103c040082052210310b031014040300219601c014410013a205403421420840e04540c000181e440403602510b203501030102d1410150b00038813440e0500b800d15400c001c80b200d240c140c141c0041017220700c1180c1c200502e02c1406402500c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 311343435 1250 311342185 311342201
    0x1020706090b0730200a0305100609030213200307020c0117070503060f03070f060302120112020d060203061c03050a020708060603120c15130512030f0412170a0204030b0a 75
    0xc3e807180c01c0ca24021580540e101e1103a07600e101241004c9617202c06298200b603045080d2510000b030f2568100600140c10380c80060042c003990a008003000d065500180d4194043c0c00007029641c0c0d12400c002c0b03400d104410458203801c0344030301d540e03a074100040d00a4823990b003500694041502c800b10030200c0220310b080c0c0d5220b802240c0d07400d81581c80e0041001142c0d10708049580d1300d841019004100c52490300742c403034028525528010780d111415000d124603504141c1c445145100d00c220941c0c050b0f100d031000c0b20714050303010100581da569a400081d0303444807607018440d4090002c084003010540c02c4001021610701a408071000203a4506c2072982e115070484010790140c201c280064241e184d08001391524441a070251903944a002e0412411900f04841d10084070300c1ca0025002400000d024540510011941c0c0501d1440d0406500c40001405440100440d40c4070100d0220a4402c40d920401904400800d6526091644400c00a9045404141c0d1404101e001243c4156030a104000c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 311344685 1250 311343435 311343497
    0x1230c0906040f0f0b1602090405100c050406031d0a0b0c1303030f0809072103091d0118050108150c090306040605180c0d06110d050a02040906050303280201020706090b07 75
    0x6d40041603091103021030002e40704440500c1500280e080202d03190040600c181c1456450301c3c0c07a14036001e401010303186000d000110101ca20500f010720400027144070201c540c5c000d103c4208549030101980d807544685d100e00c1845100c030710300120030180d20101d6400000121b40d01c0c506144c0f5500300711501c03401c0c41d00c20f0840c0c0b161942c00c104413540745219003195041c00b900380740240c0f590300d03640c0d80300110202c022600171802c404010300c41081d400749241c000902c64081000030f507060000e003540d643c8400c01045580b06010002a01e814094800c54040b8030f0090705980d064105850520050541550700c000d081c00c90907406034080800040e456000b1074014205003c00391183c440034010101031803000c1d0010401c00c0008bc2c4040240981c1d4020413103420010707519841c00200c0e104880f0680c01103440798108200d050740c8100718411001c4000c101c03107100c80031104461010307802407040c02002400c40341020100018423185403d1581f203101340e40c60358131000408007040300040c0c4513084554 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 311345935 1250 311344685 311344717
    0x6060806130b030309130501060807050f0412061b03050a0b150409112703060703050c0706110c0109110f01020102040501020316051905061801230c0906040f0f0b 71
    0x40700c00c80a68101000e403200282c00c0d60f1030030360b10f44046001170403140003a030141611039004021166103d00b140f40c1c406c55524082741010782441c00c3c003a05114900c940355a410645010313a0902c1510341c00100c0c040025003190900564041000d4080d22046071500e002600c2d020b150011820a0b500404e00400c00324805481c150078080c0030402401000d200016100050100c10200d001a210480d455503501d2620040310803040308041c03408000901260070103080c5010b200e02d00d1800810741d404640d0058001c82c42c0e141c8200c1003095800741c1440c80c400c80d820042c20780280324562040312640901941c0729445400c0038401a400c0c0e1050748210b9006901c10014410548401850702c0e10051054094600c4082007400000300e18501503000d590a400460070b01c8060842c2011502034411410300a0064130012042002c0c008500c8403e15092500c80002400b40c1001008865503010b0051005480b5601c448102d01442124000c0408202c2c0c015004940d451410b82503c06514102c0311070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 311347185 1250 311345935 311345959
    0xb150c07090f020d0e07080c01020a0f080a120c0e0414010503070303140403020907050c0105090c03030406180503010207110a080303010b1c141617191d030c0c0406060806 75
    0x50010702c0400d01c01c02649900703114254140c000d5010380045282080028210107040002e040d05010550135054195070000281c480000c98550f1040c0549030090400c6441d01900307034080c2c40c0716a10b001e201e2146850016800308d415000a488030b02824190740030449481040e980068001d828010541e16a220b0032040000030312555031101c40c0039501245504181c1d50707a0200d030b108001590b26a02240020a00c0c2c201c6581c00d101b10303a0321140400003085601003070004240c891140340a22810050700741c00b003000400c8017406134001404054021540d0380d4450803d41c14031460001d60f00d208251071a40018495400000d6905891b24880c02600c1e02d2280100c03014000c07040344c0300c08415911203154004c40c0c01c034203a84620441400f42c003106503410003040200b0b819900480481070709541c60500115804410180b07401d6800c0f07050000f60850704814880040350302d07441e00d6600d440000341c6005400004100c014400300162420f014554407000181d4000904451aa4203d60350740c540e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 311348435 1250 311347185 311347199
    0x80903032d1003020909010c2001020c0a0f23070b091206040f02040b030111090f040b0d0f030e010c050307020d0213060306020331030c020a12060b150c07 68
    0x203020001020500d50381408111076440100c82003003210350204910150408000b0350804801c01d940c400b840c00002c1001d0344c0c007520302505529400e048c25546000340c0c2c0030862034036002d5040f0703500303805c120b0b0494420540030314200300c001030318400446995000d1100c441c00142d0110000c401061100c02500c0f4181c20300f0101441500650110350f8040c00c10404181089001d1000030300441c0100042039201599005120941c1c9001030802e00980c90070380821400e41c0581c0540d5600c0200303e4500c1495141c0b000014003030402c0b2154140d000034a04590800c00c02e5610044000038826110600c1070f01001c00155045d000d107003400b4080ea00200040c1c1c005140190150600c0740c802014500e04543c02d030b8861003100d50b5a08215230090740082405226081050f00300310800745401d40c90302091405800d40c5000009242c01014492400d910b102155101000d40010b030101d15400701c4120520b04100c0094074035150510300803048070f401c95104e2502c0b90100c03003148100e04010100c003407038542 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 311349685 1250 311348435 311348461
    0x305010c0207030b2d0f0405010b0f010f0c050c030303010e0f010e01050d081b0303010b07031404030201051c020706050a051e061014160302070e011d040b07180e0702070608090303 79
    0x15003880342c6a402101c4252070810b0843c0c14060165040c804416103030a148c00350031200302c680120310422440b42c0e01400340e03a004502505400c06031410200744460307468010302d44050b000100c3c1e41030001000104508800c510541d1260000c00081030250740c0c1c400810800d61001e000c5d190300035007200e2030300700820980c02c01400300c21854882c100c0c84181c45030416003075401c03e0700070a28841d0005000014903900000303411245000c1351f1070341c0c40c251841d40042c24174842d0704412410b500b1140080d181d4050070394190751074180c104805000624000050000500301121051006200c4205502482078040d80c80f40c843c0c032000d8907a805000300c1410503101880000303011080c1450411070039254103445081c4002c903905c2074000b0940d080c00c1040349000e5840580020150690041c2d02c840480c070b5080074503801c140c10620003a400e440b050006c0300c1b05032000740a400115840c65000403420f00e4180e03614130030b10507542aa40c1c500c0d1109411121040e090b142444280c1c018000329400a00c4d1a03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 311350935 1250 311349685 311349721
    0x7140405010203072015030105120c031e030c060708101d0c03150303040f090b09070e01050715092d021813050f010b0103060609081f02040b0d0203010305010c0207030b 74
    0x341d82041920281e10018480340711002141401b074070080b0042100307041c0312100082d000c10400c007600402c0c0e01140441c0d959600c004443c1070100901440c00e014410138011542c0d208805d00986515151601c0007414003541520440d80400c4281c1f130014007240040c0d90308100005132090540c694880d0402d0f01025000581003c0603501c01c02010b00c4260390400042c402803640c002d40410310f625040b90f940896181850302030080b8214401c01c420603601480116000c0d00c00d003031180d00c9000600702402d02c1d810818020b0012172411130920140084a9204144028200011580c01458800510254488050085d000078400070741048000c00d9a03d0311f81e022030b9014120b6090a55612520f1808240248205840c1d540d440d0341185940e05000f003002a0a05092604015151801140c0d4612800c00c00c148001010089100c40c0000f80e01101d000340504440380b03495002071200080258800c0c442264550310380009201c4160010962408072500301c0800f44096642042c0c0c1d40c000a016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 311352185 1250 311350935 311350973
    0x3130204020c0a0311071205071502030f0403030c021518060702030c0904030f020601060912030302180303270906060412030c080a03140a090b060616050a0b0714040501020307 77
    0x24020541103901c00c024010409020703994044041d4540c40d03009081105a410140c460070038841f280001c42c2d40010101c049610b0a9003400da10b075620b9070704078214010842e0706401240005030000c185a84070020402240c000c0b00c11441a580740c1c0444117a40c811000100c440000c04819a245442e00340302403c0300714005020b42e802404000001541a1001c642c101e0220703c480011903592941002140d01401481c10210200b03802d0803600c03008401d00080080405800003103010341c0500c0318403401d201c00030180440352078581d000c001040100701124400d40071031250401101c0c070315000036102d01846020340750514103420520040300d82c2c40394101c260140520303415840c00140b0090010005001942d80c00904d120201442ca008e0510117401030289504290800c8042402002d03116000780702201c40315603c2e0303d040100c8401c000880c1c005089400b4080d10791043c00401140144556110340d07440e0b140d82c200d451316050a009500549005034802d21141c400a51060050701003140c070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 311353435 1250 311352185 311352187
    0xc13021303050a03030204030507060c1e23030d0b0a2108070b010f1a09010f0f0c02090c040801271e02030313080f0c03061609030819170c0313020402 66
    0x32911503d2400e076185200700c00281d030000701042400310a000080c050b20340c80c0b410600781a086e4680003042c0e22582c84190440c1e00030340240c1c0402c0206a0040f02000f00c3c0319070ba00c45201041807c1c0c1e100c2d000440303240b00b114140814444e03107281c4000010240d4044032402105075440c10311142000075030110445852004000c0f4101180009e1169030003840310b420701106150400c82005900c4450211840c0341d00420701003a1542d81e081615102d0035265440d000301440c9c01008101d552101078ac90203500000340304180665003140710020029146040000e00550134000e0104031b0f07246c0702c4800e00302c1c84084000c8078000201c00c082c41508019460742c500d0302c1301400c2d8000a00f9940070032540c200c40e60340f03040c3c2008074a03010300850280200c103101a00d00f6001400100b81c40c0c000003880071b403100d0500703110080340c240601d080c14055074010000d60b4480e0355024100a0001840d945a000f00c3e011007040034250111003000c1c2e110b10200082c65045840340c4070b001d00041c44069040b41c1c4560 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 311354685 1250 311353435 311353439
    0x2060c0a020c13021e071509020319060e1216081c0e01020304030206250507080d061d1021050c15090111010e0303180c210d020c130213 60
    0x5542d603e903031142440c90b2001a5545044000305942205000c0c94110000040c003d01000c5414a841c01c41c0302041000c010500b2221031002070306100c2408444007020040011140c01c1c40f905500840d404070001d4100c40b1241c5101c1c0038030200d0b001d001d010043c4000d00000000014002c400a03002da503e41e070700400301c80403401410340c045d2000300d42e80700d41507075021041100f8154100b14094019a908003403a910341042550686480101c080304820b0000002d0a40200101c040450f0302400910b4020003000c0e0b266406200c3c15614458241a110f60a80100d080c0d204150703040c004886008240d41c081c0840c40024040c2e070700c22600c05a03801c1c001d1201210060b2284070210000a00340d00030f0329900c410b290000f4014414140c08800241e1400c4006c1d03a01039800411030b90055841130664424941214a01e854507140312510b540190f0788079012074456100040900c1d05151450941e040c6961580040365240000350506511008040c448040b080c4c240d1700500c00400c10b0146030103519 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 311355935 1250 311354685 311354689
    0xc0b130f1b210302010c090506270910230913260901020d0201061211241819030206090d06060b03070908030a090b090a2303100c02060c0a020c 63
    0x3244448140071407440041002c0030554284a140c00400150901d0f141c2641400042000b45c0520745241284040c0e1101131800b10300b030100180c1c6020300050044038946009a21a44000d6a503c030315420b912032542003615220040c1d482c07200032400a01a034880303079071341c2c120200517101d004025500b2102c25446464413509045200c061408520f0500d0303034800d03104000900d40100c401041e02103914190302030202c103680580740c078810f680100184803218407000005003c410000c84c1e0091a4a1030100c1c1e4240f0020307200a041218203006003965615040d40601007408801078140c0d6000506e01c00c00d03c0185803c00c09021140f0307001c0c01c43c185e82e451540d03d5004580c440c0d0842014214080304100c0301a6218403080c01424400340503500784041c404000d00151003900903410007013000318007003510307480b0307040440018a24001c030f0b106040e5115041740c2d8141d80340c60441c0d00074040c0c0c04010304c42c00c18500803804880c40720b6008100c070741c0c2c842900c030310301ea00410365040841c011141d4060040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 311357185 1250 311355935 311355959
    0x1022203082512030c0807020c0a1518061805060906090d140a0f02030c12030313050102090a090b1201110f091305010b0a090f150c020102010b09070c0b130f1b 70
    0x83c88545001030a001040d0000c5d00016004084004650250b14840c02503141c2e01800b000b282d0b0b203050a070f0072240718540259595030501642800c2203034011780008a0701d0380315844503c001c2004100c0b07115961601c1c14040d1504c142c400107a0010b001b0014031600d41444003811440d24000c401440100c14200345d80c504040480c00143c40c0b04141f0200e48003076103810f1000c121203000496200d170b400c041919030246c8130b010051900080303d40c080c5503041807100c00c0d0121036004400801e141c0d00161110b914600038812050614003c0c842440310314040c581c140b00d1340c1c008d103800c1e07107182d410070344840f094025030740c455502c20f50480500080481c00c8029401039502030007141d000c030764640c200d10b00d0092094006501c140d41c2c294001e2000c01040d000520692a0701c440d0345000303840351216000507070140903078041040c0c210a410040045455110320014000c074441e800c0702d03600341c540b02d40005803074603a0341000d80b80e0411544041d000036469070000c103d40e41d50442c10421103a641c0074241c14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 311358435 1250 311357185 311357213
    0xb06030a060e0304170109030905010f0203090405040b25080c1e0d0b09090118080d090b01080c0a05040e0d08130506010e06400204080708010222030825 67
    0x2c0e5a1010030f0030301c200b26000004c0d1030b0410005000300102c02c1a07450041001440d8454903041c000e15031103075040288288211402000054428001801d01303191a8140480840f20b003000d050021019045040b1241c150065801c1644e0b079000598803202c10403000c030703030000d1444012105c3c1310808928950008003e0083d03045110340c0040e9500c034040504c080310707100400c0d01d40141d151680010740011406c00c0052010b8010b00d24a0b02c402800c1102001002102e10107090b00704d400e0000500e141d40090380c03038003022058902d02c4050b81d442003800f00381e43e42c52102d40c2260700052110501c10f4840e951081e03002140c00c44408003d03040e0b440300d9041500c01e03080350300507600610801140e810007150007240852240c010700100d640081c0800c4030100101c246220500700800c1002200c070090f015034001d045400145c2d0f60300741e5035511080c001e6102094110b14006060700400440c851040790300100d1f908041c449140030044002201d0101d800709500f030002020301e103900c020030b2070b55042d1a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 311359685 1250 311358435 311358461
    0x20d050607020712080409050402010318111f0207090c031e0506090609070f030b04150b040906150507080901020106090618060b04061b0f05150106031a0a030b06030a06 74
    0xc00e0030700724002810081d06030806007513190f10103464400948840c0880381107031041540015281c6a6100484c040c0c01c10346181d0b060340030300c54400000e21206941040f0504021140c00300c88104100d01b050b21b8514400042025803c805400c000d424065088004d80d92068640041c0c03044c02c0b041c1029100701c08050b20314620703079a03008101c218241410120b42088081310075110b5482e004400070010341242d0707058400c064840c200110942c4458028016150011160041d1581c4132446c681468200c1c1c456107a1881c04d03d40d001408400040f100b10f03010b102a954070303191038540e44901c0400d07848041003904540d41c0e000001203c100e02d2181074050040c2181c400007403500c0f17462010030f1b0b4070782c0c0e000711036081e104100c00c01c09030390040351044a030503400503c512180401c0c1820281d0402c03001c0003406500405a082812000c50209641a01e0203510108036101410030300740c501101252400b500410380b00418008541c2071680741e60f100e00004d04880385903800303940d0741d0151207003882203803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 311360935 1250 311359685 311359693
    0x20c2202070b07030609090809060d0b060d02070201020c06090d0209040c08120901020c09010608130618080705060a09080306060705031303050c102c01020703080a0206150607050a0b1003020d05 85
    0x46900c0c4c1d810f0107848020300303071444140680e02c0c82e521803201520903c94454880c01c40002c884000034420b42001c804440e0044c03050f82c85260703401d0883c010350300c5120124014040d890000c4c0c40e0380f80120980d17100b82c1002d0000482100303241d091004402d0040c0c02661900250000003a1107082046480704580441c461107403517103803030070000e0f241180c80a910f0b4420958a401448860792001c940c6900c200d10303a1400900f42d010742072078002000700c07081e41c41b0307074080189298003400062402003d106204038100d0701c0d01da03100c5003880115403481000504101c0c0c03c00103d402c9140c05000790010f40d00850650703180c01c04222241c00302180075070049440350024108070b00d4520307101542d801c40c010300e41004189544140e020b00400c00d0b0b0b941282020001780c0ba10b03201a03910800190740a15480080b0a80d1602c0345d0380301941d03803d001c6607100c8100e000058811683d080a5050704c0240f83d00c00d0061600c17000b1645c0c0e203420203a0040030240d013403a032800d0000150750351310480e11845014030050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 311362185 1250 311360935 311360941
    0x18280605270105101b4d0d0203030403050105040c0b180603151804140d0e040905190834060507020f0a0b010810090c0b130b0c1005060907020c2202070b 67
    0x55103203414240742c415500f29506e001002215445c2101030106001d2200360b8100c0c4203c00c002420041c8501c0302030f401d0310004c40e02008006056204c240600e008484074000d41e5070b1504444114496100c0201c0c002d0141c07640301d849401d099002d5a007103096522140d14014420001c031f42c01d20720b0001c51240202ca01414003043c000910944060680010042d0124501c4003c0241c0000f51000003580156a41d050307a409200041c028220706001a400c1d900307d011580c1042c803e181c006c0807441000340d24081d010f002c0c01c00c0400d6048510002000385251100742ca803a840700501d0014515030070340c010212104880c140034441c0c1c4203013034850500701c0203650401400900e000d480c40e450490042c0f408901c90081128202c800080311983c07800c0b103903680c1c00c548481c10100c10b140d200d1041c82a010030362008400303012400017034058207181c0c00c0005940354820040d4402d07042d1102000746c1c0192910b010903060040c00301003441c0340b0074074240c000340c0380b40c0c0c001c02264450070080c0c503071a00301814 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 311363435 1250 311362185 311362223
    0x50a0f062d0c02030c0706180305010e03040315182603010b070501060e070903121404090605010201230a0905010204080307111504030218280605270105101b 69
    0x10325540c10942d4801542030003803095175165a8800e90040c90244041c9106102c0060700303940302d19003d140d010f0001d02c001058400c40f07aa403908a0300086030662151b1040d107421920900c104080c80000102c0345401c000c140e1210000811140c606181c441494941c44040d1800040194000c10005400e2542c038a80f03405c000e403c40342c043e082440394050500030700c85210f5004075280e054980100c03086c18000380d1501d0a985c3c4089102d200170010402082c0007940502651004084070b00a800a00244200111104050460f0b100e011240300040001c2591010103520444807144580c00040c078054441c50640e1032b5030400340b0f0855008290305021106402e20000f02d020885030b990006050505550000b60003824041c1000903640782c03c030018503080300700c44810055402490413a4515888a69640090005030081e81d0082e220070310f42c01400001c5030401204c074400048500402d0342403a013048290905620224108105481400115082c04041c0f8103124810a00ca010303008000e00c3c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 311364685 1250 311363435 311363441
    0x209040506101e06081306060e0f01080606030a12030902180a060f03030c080703091503050a1a06041e0321080f0903030718080304030615050607050a0f062d 69
    0xb40d080000d21030040e01c03a02d41010304882544c04506100c005c42c0c0d00c404101c803010462131005070003a030402500085141c0c1090905014000b00f002c1c4240b643c3c0c031034003516990802620700c81d4160b0702942100c00418145c1807208100009880c001c20300c0d10140c0c000901450300d099401d64002c051400740104d02c1490310428000f031100d0742e07034032050910307540317026100f05c40c3d0b00030141103d000041c08004062182c0092000f41c040c12094642c280c940200040080c0313030484a040c1c1c55840c1c400d0003442d100644613121091007008050602e82414200c03085030403408200e18103c8650038641c04000901e008413852150343e945081c2008150001c40e004281c0300c005040340f242c4072505801e01510803408001c803540500ca9080a640c60300c070200006001e068a5446140c3d180808100801000610b402c44001682c5a84055a0181d207802c10042948500440180213a01580100740040d183c241e01d40f00d402d0081e500007c101c0380c2d42c00d4040e0000c800003440c0d1501c60200c040550550b24604c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 311365935 1250 311364685 311364689
    0x110a02010203060418030903060e0c0405090a0507081209120102090d03050c1507051801200c011e050403151506090510030e060a1113081e0a0308010605030a09020904050610 76
    0x150300000312207406d44015020841d5804040c142c2611900310001c4014200003070100a400a88108168500604003945134008500d080b142030050b40360026000c0d100094120075034820008241c54950100204600c040404000100b255000e1061044aa850701403015407103000391034140d0b403500b0840240781020b640a400c0c0c00741c04200d0003800030a6600100391800420540d0115031821124801603403a07208051105c06020200110344e500e241c40856182030640382030325075801001c100c00c0540c282e020b45001810010b1000c0c4030403c04a86aa01da42c0010211080c000500300460040301c401c501094201202048103210100903908040b00c2d60030820311945810802405040140c64643c0c1016110341c0d0b6860311a034105100c10aa007040b110214030404940e410155134913080d40d2601290007509207100704200602aa1110104060100760350651b0f480c0896820414152016003000c4e1410f408199201c0000e801078031807400320b0340114010310040c004d43c0b52010031f48070030404603 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 311367185 1250 311365935 311365961
    0x90f12030501060905010e0d0c1811160b04170706060608090616030c052514340b031e010b07080702040b01050f0304080c06070305041208060103110a020102030604 72
    0x3000400600794840c613203900380d52003480c0500303101d084034000500d444070391980500005114040001d60148528901c01d5801003440280702d6040040c9407030020b80107030180c04144c3c03d600d20078100059091007a8a600901c140c1e052003003800010905852a00040011580c180d0b984505001c482d4004400c1e07903101c1d04000c014103851500302d9400a01c1c003843c11404007856110741d2400c81160041c0147d48101c404c032002120b8161201000f04440c10b07003504160380200004681c40c15008000c500b804d440c0c4440c0f0300003280140d1110220310142400c0010060460405d5000305174503049000950043ca02100e0b941c00c010602c0e0260b000c2007106a03c00d54440724100712150000300c031403054555558044500050184200b4010fa071035210788000017146100002c10041041140b002500e542d00110341141c03020394a80400754101c1d5000d4170050101d05403005040843ca210301c0701c056020006240c00300b02c0c15040005031103107800050074200581d40100130070219040611403200c01c1c0d140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 311368435 1250 311367185 311367191
    0x10050609060406060e10030627060b210c040302040c0503060a080303070f0e0406150c03081506040b0a120f0c020c0307032a080a030e01031d0c04090507030204090f1203 74
    0x1602501510180600c2c070319a006030b11b1004031002c4103000c0d40c4140010301c0f08000000354000c983c0c80c0c4101314185d2031640d0a10070310301500441c440041e00240c2c0c6541c1c0824509002d0701e00c6400c01800034803c01480203442d0001000701000584a50080e8640300080351902c613140d00f402400c000e403821658014070032590050080100c200d5200092140366503090500d046007074a00c50214020304440c0c1c0242010350040000c010000b80d0015003c24014000da0340c00a03651604601881001034106156901a405020a002141080005200c0902142000103100d10100420b8082d600ca5020703803650940d50f0006031400030b406100c491643e800482c007502d081815036541d2144881b907443e8000c0b00740d0b0600e42a00810010702c00d614007034103200040350b42c01580f500d002411000a00300241c0041e04040d0010516140301c050882031011070f1019024028600e01800700070240c0800039545807041040000150300d540c420504801c2c000c41c41c0d040c0e600d1a034142258140707000d07000c8404040c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 311369685 1250 311368435 311368439
    0x3010c030c050901110f061305070f030f060b041401090203150607020a0306090f050703061a01050a0806040c17040602030402011e0905010c080f03090601031106040b0708030a090510050609060406 86
    0x250210403110707030b0fa009003001c005014000400900c3c024800058488030700ca04018403c0c41000e288842c140d142c4580c080f143d01070340b114200141c0f07c2d16071000501c41ca105058450000710b0681104c505074001500020b18001080350100903030030280c0c082c0c2c00040d400014004072001d5444480002c10302039a1503458140a5800314286506611000e03042a0b03450702650208041421580e0030940c2110071941016200c7c01c000004108818610b90311000b10040e828a95000b442510540c01d00c0e91130304511680d4030070900002d0100c444000080188000084030741c3daa1000c800307401180528001030720307460148005043c103600e462074400c1c5400420565407445a02c403c092098030002e1a109214000d50702c1c08031018022030100501d5402c0120811200704000076441e0b040764081d495540190144405100c003d00c503074040c4054400c02000000007040c0c912006542140c00c140340018600c034280c0b45c10b0305101c1c001c200c1031005501d0700f091103d24688000c001d600440c003168100100d034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 311370935 1250 311369685 311369687
    0x80106061b0f0f0f05060106031802011e0905210c0103060302130e0307080309062a04051509090403090603050a0b1c020a0324051e041707020a0f0503010c030c 70
    0x1a01079a0020300d8144554007038010440d40c452500d101c07562001120f900c030500e500c2d01648862090044e580081d24111801108100f4041c00d2860181c040c0c6822280c1c501742c01281180c640c1c0034084006102000708002740c0d40d11004502ca032000f02c099490005038003030540c0c55003805007100346981090704102c414805039948144000038100e0301070b0002092242100e0082c154010070300040c00c850004010440440004901c003807150b00340300c00c1e01004040c080694084d6030314060410058003000e1005121609103550000c0420a456180030b007400f544500064000404682c100d001684013079003002050b0701f6002c3d0541102c0c2500f010b2003040d080300c0208500d450410004801800d01eaa404015034840340144000345030006150088884131494400c0c00c42d004062140d2024a410000380b20704103080c401800e954204401c3c0c218540b190384500044802c6000400e96108003041840c1c016929000940700801640d80d00c01c001707030702d000c0070182140d0a4401000c01e050400d00c2e07001d082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 311372185 1250 311370935 311370977
    0x1003050706110120070210080702100b0d05030706061509060507080307030e060124020303040b27030a080403030c1110020d092a05010f050906072a08010606 69
    0x5119a0702e405420100b040c03040c640034056064600e0380c03880f1002c2c180c0311409140303c0202400350094501884800c1030603c00c481005d41114040010780150841640342c131207640007408240b500404520360969070303803515800d55200c240100e071010394400c1c08002d05c22184c220b840c1c0d541c40509040c81c1841c075200000d0300c0c0c0e2164040090441d8000800039018601903030011500c103401404507101d40da164620405031201600301c00e00c090f4587e1480103981d620002c11a88210f81c0b040100369140c0380c0309090311210080c3e5807800351140301110141600c1008201402e00137055664503207032400c1a060203011900d45030301c0b080c01c100d8140000700420360005500c01d59003062140050769810020140030040020348801044103003400ea20344809480505500d44200c0c140000c3c110442c0e545005450540e13000e52401c4c0410000c1c44845a18507180015014081c0903007808031180a0008a6401d40c100601c1580014089040107001e248024030510002d800a03013040461070048842e0712204d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 311373435 1250 311372185 311372189
    0xe06070803070318060c09030c050f03030f0306150a020109020f0603071b03030f060902130e01210309030c0b0a140f090f0609030106120501150308070303091106030c070b10030507 79
    0x3891344a03407107803070405200d290304102942c11203020030032080e10704002031850180b8070040e18020100d48002c1000c0c540390101d0303403aa142c020003d524200a6482611a0350802081d01e035002000304010044188841300900c05010f0702d50002404841f14410810101810518580120390074010480510381281010000ca04904c03414241b4074007500c0c08802800002d2049110603003414400245500e05401806400c440240c061400c5134540e0984180c0708404d10540d11090a500a01e54081c0030880490181c1030280c50801c042c00d445e0345945065400c0c991240c40d06000006002c007007964401285d1090004441da15481e0881c140b022402900a6500c4188110803043d0050340707a540358400c4035a003500140013400a560b840c082e45066041031b600543d600c0d42040320440c82924080302550640b54409801810891103840031070060501c0030f41228a040441d51160b059039940001c0c51041038840031035582c51149103449905110007402d100050041c2800510020f1000b25902e01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 311374685 1250 311373435 311373437
    0x207020a05041505040204140f030c1005070f05150a0e010507020606060d06150309031106100909080c1b0102010c0201141810090507030c0b090a0e0601020a20010e0607080307 77
    0x40c243c00c41200c102903800d00c5520507507005200040016007a40f440580c030300d03a03101c03c440201c1040c9000e030a0544400c4080c41e11b55001004228800c1c500e40218003600840b03001e95209400a00bd40c1d82d0240f4020300d007039464680c0c902c840d003089501c05043c0200c0c950b20f0070740700c020700003414690f401075501d078000760019204c0d00d0f001c00e540604060941c8a00010141c1c00440c40c241d11181d04058010403421a003507000900c0d222042c1102c480008282d8081c1031580e16180b000e9241c80513400c02403104100440b6010400c000e0f20260020030040b0304103800ca0341d191740c04a21400c0c0300290860381c60801d180c0075641481085440c00c2840200a5444800c1140001c100c18518030f880d030800710404814040b140c60961070b00c013445070015920040d039100c0c017074051240e030b2600003110040c02025000d0398132080d000424007a145e4401c0d11950400e070f060040b80d90001042e61800442c503045088400052003629401d0305642e4012800801c41a0960343c0c90314040941c0c48614041c80020000c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 311375935 1250 311374685 311374691
    0xd1a03070324050a05090c0d030203030c0d0912200a080403080a05090a031515051c1103100203091203091b181e0105030304060c060b1504030c08100207020a0504 71
    0x448045201c6920640c490482c88041081c1d181c0311480d54003c02041c0c03940c20940c03113072015191085c10541010a003203505600210700b19641c1c3c141c20b000c281e100c80900c45e12280c07602d003a00c0008641110b29004000240c031940044202c42024501e1192066004140c5078007003250349010540c4d00b8100ca0a40303030071803070345030390f030405071000707941e07520583d80c00c9508040c0101c40042400100b2a190001c950018020300c20542500c0a054140d14180515940803000c0110450441d40d14881c007002140719856240761800d05000281c14510b412015440540e000810824000b2052056044e0f0b4070015000d0f03821400c200910700d0740c07408040c00740740028622841607215961aa007040c0d009141d1810418501e1138101c0c940c420540242c0c99682008101000105a601d4003000741d806850240e0368551060b007042d00d619001d0700e07081400d15044001034100500c072180907001403005d9401102d6000e190341c0382c16802d40c5014030f06e01c203840c0094414821080166106210072003100c1007100c0c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 311377185 1250 311375935 311375963
    0x3090a0603050a0e0a0c14030313060c1b18060504020c030f0c011803030212100302030c0d080903010f060303090f0b0706050a230601020c09092509060306020d1a030703 74
    0x1a03802040201d40810580c41791128042c2004a40f01c0c41e10113a0300d8885c84040713511110300c1070643d0707405050b401695030b41744a11f080c407540703106a00f03002e281809144098042c01801144000c022090b40004482200d170244040219140e8040d02d0f004001c141c80c114642920071110548030300405c040b03082081d20005070000301032400d42040c03440280c519100e900300300301032902900070352019031070340e40c01005240050070360710307820107103000710f81e00a000b0f004200031810400c0303d020005101216507400a0040480303d4a092080c0f0582155141c0300140c2c2904608024141117003c0d4055200e47d040310a0901c10700b01a03e040d03640c0590300c01000300d015211040480050508a456594a20381b0610015042c240c1807440720300480c8281c00740c8616219140900072810710803a015810384c0c0c0b0406405800b042d081d024801e0390b0081c0b44214454988500843c001d56009500554110360040b03031001c10b40609200e0030100d06174602c2003800448040020a49034000c070320004c0c14200c044030b10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 311378435 1250 311377185 311377201
    0x50304141f05030411060307083606040501060b1603051305031506150903060c071b0b0c0d031b0c050106210b0c03040b181e1c0203090a060305 63
    0x1e4401180c101076500c0d6210314214000a02c0358204030b03021740b02d503401910b0300b1074541845000c590180a01d035840900903030b03409024841c0c82d0034000d00781c0800281c01b0b07800d40031504500d41c2c8815040441000d05000d06146c10040d003502d507150030200842d0b50400c5800c82c412041041905c02c1c81d45410095210612018000b020400c1d0383e005d503416002e1181080c05841c0303909a400c0c40f65004454108000c03403c00ca0044c0c40f40101c80c10319405a000c1c402142d1100496405014618030a048082d01d01e00b020705111000743c0d0550040362180008100794503100030602220a4503101481c00b0015907101c01c544018222070841020148140301c0102c0302030000a4000718054080b01c1c05042c91584e20044690380d904c0403080a8410912701e178041072a40d80188100c0b40659000099224582c030b401d0b43c642c24040c201c84c030000c203610070b1030700700b80500100b02c2510f02103450440181624030800e106051040241d11800011500100101e81e000e6031219116001c9d9030391403030300043c1c1350741d5140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 311379685 1250 311378435 311378449
    0x8150303040905070203030417030c16021c08032508040303150b1308060f06091602150c032203120f1e02090325060503061309060e0f070305030414 65
    0x2d1455075081c542003042c06030300003004500807482110903403552010a40340798114002510107200e044000c1088000651a060f402c0c0b13081800100700c22411200078401e202d8480e880b400c21580c00d040170042099401d040c0c400c0308145241603401000b2400c81c0c48004100d460b00500003810b0554803603043d6940118154400050700d019203d25a85441c0e00c0d01400300c52110b03200e21003040c4581400a040542e10500c003502841019040a8442e120302034698031440001d60924214070a14805c0650040ca01c24064010f00594400355a2030402e084080024502846204200c1c0ca50542080020b07600801d0903a111b01d40351000034105ca60060300300c01620342c250030850150001403009a41e501554001c081c00d4004504480850080d9482240240100d8210304800b45658008021050003000190750081d0020a050740520440e8250021245940d2042e50b00555502102c0d0b90b908042020411001840700100f403028a541e85417583c0e88200e00880703120605104003084503031a250 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 311380935 1250 311379685 311379689
    0xa0b04110a0f1503020c07120302250f120b07030506121002130e0c07170d05040b0417070c290307110106050d020f0f0f03010c0207030b0901020a0815030304 69
    0xc04079440240d940440801c844a1030007083c0340540d4809100040f907000348200c981c02c00c80c0300050f1002da8545200d403014071000080540641c003c0d100d60000d504155064000c0f482c4071203890200c0d0f90304159803200103290b030390400b4662006203400e80d008944120030307059202c41c0b00c1c135012405580760004a03002c0780c00d80312000445c0c40361100744103d0024580260001201008141c1c4019503502804181c1a10564201050301c1c000c20010003c10001c078085080c03d404900003601c0d1a800d15080b80403210119015240c001204060004205800c03080d5100d2080340e078401400d0101c4d0f604d41440b45a403620400308489285407107038012581c2102400c0310f040203500816160318080c0340103402c00b09604600040d65190400128991a00311406252142c0141c8607050b23528504041c000b0b803203803103080641d000c00b075404106d040d55001d004401588159a014118032803035498170891301c400140400350164014805c102455610006840e4818000491240384103003c5011038103501c256 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 311382185 1250 311380935 311380939
    0x70b070501050603011a06030a020723010209030f0705060d05090c04091b051014130503010f09031205010b030c0a1701060305090c0406060e150f0307020106050109080304080a0b0411 80
    0x11420505015065218520901099000341700d51500909000322140d658941960b003c070003800800c90211440d405804054450240848246001f058101001c1450442445160740004503901141001d1004d1001c03085024000c18040707060000283c01c5014454100500c240e032400040d1441c003040014030000c0001030800c00c050102420310340ba600010407c081072454a0090014850030f1451026203180b1280d91516030501040e0901d000c2544900c104c5411055110408034042c1d030284105505500e540b48009032046640c600504407140e036940150380246000c00400c400004c1c003040726402a008400310342c3c3e0b282c26146c03d44440300f001c4030003040000c040002181480d01035020350b02a07203e2200b15410b4810706000c000075501a8050382c0002400511421450b041441c030b22a409402545440d0905001d4608502141c2003101c0410050307440781d508028558110303440e01c01521101d0040c501d41410b001845036540d0080e00c2c0140f2150701c3da00080c060095440c5803100075840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 311383435 1250 311382185 311382187
    0xf0204090603050d0207080d0e030c1302040602120f0a0318080301030f03030501150c061e09050607180e0412050405040903030b03120703080c0307090e01081006090b0d14070b 77
    0xe48046400600460000315641d01c18a00440a414000952030301128007020043c07040c1451a00201d0340c06040610740ca0b054801d1208940403a99084030003090a41115401078a035850003500030320700030103a410700b04944800c04c07190650b464440304440a86101d4100400d5104c0004480f203400d0300003580c060242d22000c40040b080140c481900d02d030090290340d091240c4d03602c591a2141c000461400080402c0c0c00c0328000f000504280c100c0350500f8940d03a51414a055440c24000c2070300c020540445007a049242045509a000242042c00c1d218071102410150300780703101c440744608098000380c00803611b00e10f24400c40c0d06c10002c8030b01400b4003030002c4c00603030801d19002c0e0281400240d6144240988402c10480e001c0d0b14040e590000c2e00f50360f519031283c0381c10350010402d510241c20318080003512000410200b10b65000b141c002e1440000400196114010391400c030f5250750030983c0303039505050214501e40d840041142c41c40ea0000480085d01c200c80f001d851406146074409688684 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 311384685 1250 311383435 311383439
    0x31202031b24060607060b030c04020f09040e0706020a030318200102060106080c04030803150301060f080c100e01110f070801060521060c0c0a02030712201e040f0204 73
    0x494901c165500403000218894103a0003a0450b014040328040d070070107402e010440225490b0340100203401d10150030740f1103155084001c98243e900040c8030300540c540001d040003142c02d06116141c101745c0a600644809400e0690083d1140b8174031001504241d107641c0c0740080c06541c60942030380301e03a02481042480c101c20111110101142c4121f6001d8012280001a280d001c2c0c9240ca200700c000c4540e40b49800d0540d560b40040380c0010380203920701c000541c5030051030f4909101d070f08050843c9500c941c1e00c0340d261004031464607018142c5e41d8091800b50040c1c03c40c29410140b0310881d02e00909040c00310000c0500180c1c80c0540e00d100c1c2242d00d10848800050384107042d03100d00c0030703510143c414085410034070700007092003140d032041c4200302c2d0700c0100000d410700340c0c95003c0d03c018407083d0300703548003100e880d0000f925094054101500f074040300e400d11420002045e06c1559500080d01c1d6141c040003103070000801c84c00841610f2441c00c1030440c000c0003240e489174001802d11114540842d103c603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 311385935 1250 311384685 311384737
    0xc0803030703140709080c130b04090b1b0a0206060f061603031a01030902060a0302030c0c030c0309010e030d0c0b0c0c0318120601180b0f1f0e01140403120203 70
    0x4900003d0000c2076054400100c1c81161144a440090380e50344402440c41c00402414815040c1e503181007031003220f0b558001c40d80d03681c0d2180a1400c20038095510b0740044e0600400180314a400b9445a1200c440e081003c20100d03030300030a22580c0040f045400544154070000454640d106840e000d10050880070144001c042c0c140d40003c03450759048942c800da15221000540880d98503860295020006000300c0c440284607400556110b800102006e051407140703c0042d1964000e02280315881e000422500360340d5a00c1a81034105003401c800820701c00806c240081c1a41c8240d520103001c108056000408540034a0b08407600071202c1c078201c903915126240a48200c615669032180f1910404c01d03190700030500000c031075041c0c0b01d440d1890500c503a0760000c0300f401072001c1c2e155150400f9036400c545503596154079171009407542009010812500000c0020118100c20100d036049c0503d6081082d0042290f005407016240e10850a1503100f03c5c070201a803440c000c540101040c98407000c42d1030000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 311387185 1250 311385935 311385941
    0x61d060a060905010f0f0306050a020f04060e01020d05072319030815090f0711160303120b1f05030907030b040f0312050f06040c030f051e0c030603030906070c0803030703 75
    0x6440302d240420480e40c0720140c043e4002038522614124101001060020400e00d038000c1d9041400300da0014940300804000030340a0308182e100001040f80d1382c0304032a031942c0600040d021350742d0703901d08140b51071115a2100034080c070326001d140e9004a200550078101108100418100010f00181001180b5501e0001c0005800307c3d116000c4542074a503c02c050b080c041c810074041e400c8003200802c95940c5940c111072800305090304030354520400d00f901d4003440380c18510001642c082d40e680c004190040302080141d46804181e240100c1901c2044005000910022010130300285000d0703540e622440c00e95850705107160406000714070351030180410020032000300348038640300f0b1b1140841ca2025110240441d102202d01c503803000207800001301503103001d9200d4203010f440c5040009404054000040171141c045600b0491400301d010041d03205511314040c0c40e48100d0100e8001e14600d00350021a85034055128514022a80402d114007080088140000585604d80840f600d0380351410005002d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 311388435 1250 311387185 311387189
    0xb060f09130615020708010c0e09100308030a0b01020c03120a0f090506160b0f0105030a152c250b03060a1517070c050d110f06010306020406090e010e04061d060a06 72
    0xd8417501100103000070041c001c4840e540581d89035940c0c002450010700c40312680007004001140c010903030200c00503c203d8003460040c1440880050402c0c422800607203400811503842c0d00c2640540001e40c4461081c000f1100046900e103401da1002410600a8071064802d4014551028002c14903181c08080e80080180c1d203030266440000d17540b540c0f8582c0d103da82080c00b83e04d825401c14078101012030407010043d000702100394000510868a91000741c82850303682030f0481c580d0107141e40039481032820040c01045944403c0403241d046a00040d450280d082845071503020b42d0044009981595138503445001440b014021695480c1001001003080c1c110411000d50000301c0804603100620500320111111744c0b040c0208541400104107640c03100c509045520584529646541a8007003030110f58021803240c0c40c0540c45034105040030300800300c20317006140b520010200401a1400c21b461954002d9000480044c0c458118110b1b82d581e00030811410485100c0c2205021456000d540480d003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 311389685 1250 311388435 311388437
    0x211308011b05070803060409030e03010c031409160509101a130e04030507020d020a08010c020a05150c1b0a0b01180c03020a020d3c11010b060f09130615 67
    0x911922034071010b451074015810040c1c2803031420b00c0022100d0920b54400b020fa28040e041211107050800002400d4030015034004002903281d0480e0411a0300c140e4801e9008980304001d8058031119030401500c1900d24400c19104180450210746403420740301c1410098002442840c294101084036800642d00c01105295040e90300800041c090005649890069034035507074003443e0a44c030703400300050069014030999000440328800100904240304681c03410b40b242d0060955400142440d41c05c102d03030241014032400560b0100b0101200d224201c40108891032074030500d100c25103003468a044445803000300343c00000000410307182c07006076a00021200f4098284800590303003104070142d000303803040b841c05a400640e040e040c0b18080c0e51300f100010400240282140039060701600a00f4074011030f40720201000100b46206940211044c10305c2d901c960090100d0080c00380030450741d110342400c2c14880003000c980c1031501c0d9102c000c628003141000e1401d215141d11801c800b5000e00312855504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 311390935 1250 311389685 311389721
    0x60914030a0207061d090c0a110106080d120902010c02060304030306090609050115090e15120a030e0102060f0105010c02041a190609050d11060f04030f06020712080921130801 77
    0xb10380b88907000c00780c2405c50300a01540d0480d1034030072640c0c5603500002140b106010f0409902d4010780390900c0703010024010600100411441e50902409604400528105407402e04440c0e80142c0d0700f12503407407240366040d640d0f07039035035500e81c20220010401d13900601201424504005002440c03908250f050b900c10f858000b000030140c03601500e6401007845640014412840052082e801000c0040541c0724090070384c080c0c09444000150510180110460214111401442481d40d04000d503560149160803009910750400c000601a0000b0002c02442580c84440f103200b40503450350030601094000d816400c0c400c80061524039118543d000e4a000504400f5000856140440620340e1080d000456600e0802004060003500e6026002c14031107030300c0400c070007c0000c0c40d5010b8105064064000140c66900500c0c0000c0240d002400320300c20020800e0a000d03a15101241100c01408a0410b07a6035409010a81301505d004425480c0c00c11603646078001030340c441c10f410611940040180301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 311392185 1250 311390935 311390957
    0x1202031f0b0a020d0f0905030303090303180708072309090705090c04050a0b0d06050a0303090801060e06090a0509071d01180e100c0c060f0b012307060914030a020706 73
    0x1d20800e0280810000050340100007804c281402161904009110341ca0300414081e180c4004c24516072040d60303004012382c000410400d0048082c868614800d10100207040700a140540440d520540e03402002d03001c9502c01000704050702044007440350b140000d0000340d401c0c5000c086581c0ca64603284280d2b806000c0d000002034284002c0340468040d500010881080d860030152019041d801c0000c02c240100d568a81c081110307911134080100461083d40d0f1a903405081c840d8031420355215a100e01700e019420380c00d02030340307039121060307642e02031400080003d003030355000d01c160321381000c640c04211040d045083d030300c1c00c290064601c10305032048580c1e02d0095664850403e0100d1f40c2e4580103010301d0b00326000700c0c00d01c903c4642200c2e890051610b40f2080c0507403d52240d0701111003c824400000f561050008260350700924150590000c6003400541d022034050040c0080c840c00300001c240c15524440da41c2001034403000000e10749084000c50740c40d50b40d1090041d5441d14140500804107540d6655 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 311393435 1250 311392185 311392199
    0x90b030601050d0f0e16060c1401020d0203090f100c051c090c060e040e0a030e2809020d0c030507080c0a1103030a0b12060103170f1b0303100906140f011202031f 71
    0x1900101d684a607a0000c0d40c175840d2700c400390000300c40b1410780728a5400700108206100603001844c018881000034003044400380491310b1404190748104210b1600700061808201c3c2c1081c01d885000014201544542000c0c0740000000c000180008060154418000c6031b6198050101c00000f2003d84040084080c40120281e403031030350040c01000945030800f03070f0159080c2044010b1040e03165030704600d50130b03401107010150811160010030301140d000c1001950840540644066042281401c00260500f01c000400c1c82000030f010100e4280700040c10100306100e00307409445110300c0d00030b603512418000d20f890301900c580b110103031042c003043d004042000404603155049030f50220650303481d0480d9011b000060b800100300e000a034038082c45501c242022b0414007800805011024544d84e00e4604075488a00b00150054a03282d450248107122006240c4002c85001fa030468011404140400c012144801f003c56508111070010083c0050900400d8035050110f0844c02c200d0201911038070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 311394685 1250 311393435 311393473
    0x20a0204240b0405030c041e05040f020a0b090a060f050d15050a0b040e0402010f1e09060f02010207200d140a0201081b09040b030309040207140706020706090b030601050d0f0e 77
    0x34040d170580254003045540d152503400300d4000201800c5130365860303030600c07045002c03164200e40070340d81c0441c90006001140b0703007111a20081d004404016090458034400b0402442140c01039a0030300ca400101c4948060243d0309603038000c02e1001e010f004124019500724843c0c4891710880d40240c01034240402e4080400e07003550706840300d18101c0038030385d60386400450301c120242c1c0081061048200c51075040000705000400707200c80503110b8044080c40c0400c0146604641080c0808591062180d07a00050112002500c035a89844050380e401030100f0020301d09606564005221164204c0412000d4030003281607000309000741c071016802c0e9541513603c0e11041c01e42c8950010150100051718a610b000d503c00942c4040c050212401c1152502c04102240d200401c29294100041500c28616000f04410405480c991020348000351801e0405006065140948805a0004000961545d10510555a40c0700c8007035400e00c0380d104034490050080074000c070ba520550040c5810165a101000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 311395935 1250 311394685 311394689
    0x6020a050c060325050408031b070b030c07030302161e0b0603061003061e020301120b010503030f0304060e0c09090307061a0a0b030a0906110901080f061309140d020f0d020f06010902030601020a0204240b04 90
    0x1237900d1900c20340c1d80d401c8000390300440007035150b011102e80d8200400d1880e40c42c685c0000302c50303649603029a0603080148c191070009000c14030036030000080000c00407002041000300c03076001d040842d050220b0002c0c0002a050600f811800600c040000500300c840841041a0580245980c1d102d50b620381c41171540700d100702110340c40f800a0400100e00051070550003c07062104140075204103011180010340c00c2d01080d9403405107a880424190144107841c807950041e00b13082415810052007801c040f510121041c17059461005d0003200188075100c00c0c2e005a0900307a841b20040200138022000a09581c200034800d6001801c0d650000d01c500e44003160840c01500018071021f45040354002c0c481c007030042082c0c225076001510131240c100c0401000001108010384c2c0280c03400710300c0040b26038a001c4201c0b000400f15840b5071650a00900042040ca042d640140c1c00980c6da6070f00c600060785002c0d901d080081d0800d01d8003030720f41d080f1003141413540c104101e10508040e050341d0f99500c1192900640c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 311397185 1250 311395935 311395951
    0x91b0f06020601050127030819090e041103160909060609050601211805010203010503012405010e0a0b0a0e03060601030c050d050615030106020a050c060325050408031b070b03 77
    0x2c9001449250300680581280b0380707448a4141524140340704020804400350700840f0484004502c0c1d0346c82e403441c41c0410308012403078608016170380d141241c0c10429040152001c1c104180500103400c96480c28441811190010084103850980c3c0d00300400c011f008605040e9000da03e4400007185004007030250074001c580c140d507400203400c00b0007200202802200703040007046982d8401400c101d83c1a01440004500450005071298984400c1c50b007500c4807029458101e900007582421403041c039131103440a0381e0003841d04012002d80000070504140480d08590120400442c45560301607000b00c03610006030096044d104941c40e10001541615028404000400e03814803081c2000c0c2d4044d80401c1d444140148003050a118081c0720340c402d58800c2c0c210380e0042c1c0061712100c0c10700000300151112050b0580342d451440c0352284003020300d107010a04ca568800c0403440000025880360040e40c0c0540b1102e01078941d25000340b61054020346810f01808003c0c0030b070460028001c001c00054030320942803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 311398435 1250 311397185 311397193
    0x405070f08090c040906060302040605040b0112020903031c02130803030714030c0706090804031e12030531050f0a031e0c06090b251b05070306091b0f0602 68
    0x35220300e04018035481051191a0000010303035105d0140306036440c098407000414a007940103200a43d641c0b0f421860040c4d040a2901005990240b0040e5540d9100103005850707014080019095214003190703d202c8071041040c0805110f00c0781d00a11420b025510300700c50003a43c03030010076105d01080340c4c0ea0021442e038200103c8622902001140d000301d144049030700d0132101d80c0e2280112900940142e030940b0010406000704010344100f1041d0210a1031a4401d1002d103130f503a0074640d05e0216280082585031004100b081c0c03903a144041c00301c52400c030900e40b6002e02c5280c8100400c04410191450302c01d0244c2d807070b030918012484166050f010740d00c281c4c8605040194a045000058032081040350600600d00450218851440c2d41442024000801d080001000014a5040d070441c10000303070f4841c024074195040906503940410b85c680303011044155042050500501d5440541a00c0c1815403c20402c440b560308080d00141e05400e0540d284d0300c840004808080c503004031800750f40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 311399685 1250 311398435 311398457
    0x9070206062106040c0609060e0f13140901020d0609271a0a052509060807144e0a110a180518040b041b030b04030e040507 54
    0x5103005190000200d040021107004035425802c0d02d8800200d40540b10406425028498141c0c004c1070b45004200038508000030b0031441c40054044440b000b0034522840c070f0b08243e0502440b96410803281c032640000e40310018944440d8082c041e41c444400581e00c20703d00f200202e80c2c4209131080c0c0084054402e501504884a00c55107080d151101106655040c0c041d0310100d100204030b020188513546040c40850355081c2411100c800c050b8181000505144904401e030240354808a0705049035040d150042c129201c0321020b4440e0b6011170100b0260803000501070002c11185407402c115017500c001c0c00f14804141d40326030142e03094005c0d880c0220310b0101ca403502403068440740726900103a604800007078410740d11440c0310690b40860b9003000821001006640848004490310001305816104602036401d41c109400c004100103100401c1c0140c481d010800780040b8171008840d8580c001e0021402a4480c1040e0403012012201100001c3c4941704081d50f0b4102405003500801d890740741e01030819 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 311400935 1250 311399685 311399689
    0x1e031107110f090a0204090605060708070b0a02040b0a030915230a110d0504110a08120c070302090403120f020708040e04030320070b0c042706030507030b01080c0907020606 76
    0xc1c0c8450701d194000b1518024000564400da505806142e51110040c0c1e02c0c0c4c60021224280c4400350701444c070549060002002040d6040c5c201d03404250310552541156482401841c0203020b030780c1060b0103203140400d00030102074240d8014043c0a000b1262841d04441c1c10442006035030603000d180440400d142c000384034100e02a40140e410409483c0040780d05419084043c0040d082601c51441d241d44510502c0240041c0003128104a0801d03070381307012142d0400e01440d50340c8800081403008540e0000b402200c185083c410311000d560700401c0780003e414036081c0101651305d41000c40c50804e16000002014102c5c41c07089601d0694010509410145089c4088034520002007090b802d154031012224100e0300651510680c3c01040a1126222211401c0801022000a004642c8090100414040003000e0414003c0b0440094080001111a00122000fa18495000505a00c01c41201008118044008906032442c410894800700e803072504126610b40700351140405600311070007048680c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 311402185 1250 311400935 311400953
    0xe0a09050609300f0d14090105150f06040807090c020601080c03070303030209190305010204150203070c0506090316090f27081b030415090e0106050f07110904031e031107 75
    0x5200d503180360382c2483d0f64184103441603170000c440c546070165901d84e000100340c2140025500500301800820252400c0c0100c0b103021400c0c4400280300d8040c01d140c8031041d50f1030310111005001c0010039600010f503a4482d800103401c89644010142c00742d06c0c00410b4030f0b03100007640c4d00003034801402003101c240f40d83c42c01c0d00290302446096030085400046420703541424420b560007503100d1800160b07928a0040c0c10303c2240c540c010205e045400400580b0040f551a1084005842007100e0540c2c0e2024044002440e01c40c400c03106461a0004000014110344164000c0c0502051008184000c030b9403001120104c0707480110781c85460031004807036004600990050440c000c042e000c00440144846074140c6103030065880300c248902e98010b100b0b4880d0340900154000c11090f8040c50955062080251103030052114a45a0440100c2e04e14207200c48184070580e1280050800f0400b82403e04006240000d18008116440300c034198040380c00d0b100344110001c10341c60410640c10180a42e40e00100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 311403435 1250 311402185 311402263
    0x601030204080a2004020903101a0d03020c031908160201050f07050a020a0801200a05040510050c01050c03060a060e03030d021303060b0108060d030c03090e0a09050609 74
    0x1055401d02001c81d09650810220200740d0245804e01400040c8102d0b5a40c9525203040041c0200d0052000e0101924001070700071902840d1b12010401d54101c48500550a95038802030360300c22907183c00c41003415004500341c004000c080d41503075a80541d01400d81a641c9481500500005080040a4603000481c100485040c0f0500d000c910f840c0e40c0a00300ca8080c0c01555027503407103400c581c4d49001103242c00c4100340020107d00000784225190000b040f00500f50b030518500300e0120000d005001148920103c0f0040e080c0141400968481c0e040018900d80120321024031662070200442d100a0036042038038403419006060101c5141014821250465180d0310640c05100a0000041100e15400901820410b0004020034180f071420420199804072640034103210026041c030240c1d131171341154030501075014140030344501c520b480c00301c039001704550201080c010310074144111814682c00448020340101c0c103c440c2903c46114840d00c41d040f496031551109103158035500e41002c00100e8001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 311404685 1250 311403435 311403437
    0x304030504170c130e011a18041106040b0d0e0a021e0102070f060c29041e020307081b1e010324150f050702010e1909020c0a0302010507020607170601 66
    0x294010070344041595680c008000090f8a0b49175000c01403010030911400311409407010021403904480008124007140c01035500b410820410001030a00020b02030152020700050034480d9660380c1c400005440c0e401504615182a09140c42e0840100000070320882041d001082c000c04684100e1410340714000c00703103030b8a0641c0078450000a1010b41304c0aa08020301c005d4a5a40014040d443c002900086001c02c58560650b01010000f14401804400358416404600e204030410000e282c1094100c14560007507240c8120b002c0469405008901c99000c0d03000b40d408000c50f5000c0300c00f0800d682000c01c0704500f01d40c0481952980a41c840d0b000000e4112040c0e02c15440d90000c40c0100084440303940003183c0414032007149206040c2e014210510158042c41c1c06402c00c460340d4002099944c02681c0c0c10b20a004041a0001d00d903c3e8009440050551010031551a00d100e01429201c00310360341c0680255190200041e02d441c0045a403d201d560580d4031840341c400d03066401c0a807983d01508083c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 311405935 1250 311404685 311404693
    0x601050f0d050106030f0201080f07020312041103100b090c07080d02220303050c1006061e090f1202100f021f090c08100f0605010903110d02270903030403050417 71
    0x600401c60138402e5401840c01501300c0301e41c0c4901c500000d410741c00c0c0601560001c210346010030030815408401d40e104c0203502e1505080da61514108113039404c42841c88554140a10104e0b200e44141c550700c000705200e41a110000c89031382e480c40a20f010302075120080c0c0135050401c000d407444c0c0c03410f50080a440c0b104021a50160356000000caa08119a03042140071a00018004c016028104152085201240b80c10300005042280050504084807508401800b40d00f20384107001d8003800455010b0401421750107900740c0c3d1441040d51401d40c1c440264002c12001c0400350500b071145084031003008144d002001030456141484100350303003401058944d541d0760780f800c400080d94420300800030201a002008003011041c2840300301c922900c046a9017038a0114100700c13598200c81500e0440750006400d0752a01c205001240b41c08032a080025805810444011a0014003080e03442111415000708091307581e5102c43c031035413880183d801a02060082c0010003501407222a09108003401c4002e039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 311407185 1250 311405935 311405959
    0x90303180a0306140f0c0a092108030709050a0504020702014b0e031b06070611131d0c03180a121d0d0b070e06040b07030f120e0601050f 60
    0x1401c200e0384c0b103541c00b584280502c01407082d00511010a5500544014051850401e5040b0042c101d90f5461241380701c41d000100010300d000210690f58a14140c100d02c03c10b9032450079843c002c0556100e800b500384a249411800b00302401e1600c295a00b0030707410303118002ea01d140101d228403403205109190450410146405550100500700a041186820000310742000c100001900d60b260709403a941c007940c041075070900424003030b400440105d1410b4800781d5a40c140c030309101015103040c00410315100340001d0390504400607030445030100c60084807002d0344802e0075030075080700501c25108018140c0081c00441c0403d082400d04100c1d0702107880c01c0720444800b643d10a001061040c181d8400704010503a801c541202d003100d401c88803181210541d504100550b52000442000303041101000744a814040d015211501150701030711400ca181e60325401030f40380c02090704120b00d8141c2c00141182003851000340b96801400da003150114041c00440e0700b814103110049008800503035000d4400602c4c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 311408435 1250 311407185 311407193
    0x50c030106050928091b0c03050a050912070305010e03040f0302190302190305010b03012c0f06161d01020316020105040f0810110c06130c090203071211090303180a03 73
    0x2c901020400c103e994114500e817010303000803144044107040300f80d21100c03070f0301c0400d9030b200c40348841c81e55260400c0d6840e81404842240c16000340210b0b40d07048141e04070500d03c41e5100266003011248140b00030300810b0b00170200c4584a0042d4420403000a00c400000e20051138603c808a14043c01129078281c0365542e0780000c0c164a4441250602006000d05c0c180144502130251402000040d002405140750b01800b0b4000c83d076291a140404414020281060f052f05101300500c8902c43e1045030107a0900702e20112580c0000e48001000c50121303041e10701c102154003d000e4409005170045c0d4201a1004100c08032000d940d4030490411204000c04161080070600d0742010b403894500800c0e5001c0f03098201c4c02190743c14000800c0040b41801401c5504000040d00e980c009035907044510494074a05e0540075102c080c5e007041c462a4004170800840940c89030503600400400802400207517003200760400e052064503402a05500100040284448054a56034030900094018056207a890311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 311409685 1250 311408435 311408479
    0x403122003040507050102030f0d05040c050405071205160f18080f07080606030109080f0d02041a0a03050f010f230307080a1209080d0822060e10050c0301060509 71
    0x10000e445401009010078804100150b00c044c100a00042d031401010300d1801c040d5000c0d8201d40200c140d00c45d070006040146060494000303000c054000d000038141702d10084d0180c140a20200f0b0700d40d18200021348440c10444a0030200350b642c0c7c41749d25428401010440312005130120b0301e6103442031a403000888920401c5140800414080a400401c1c100a045414200c010701802c5c440e0381000180c0012580481c102c0f411206c20b0784001e13a85002c0340488901078040c0740c0c002d2500c41c0c00311002c05181d28800c0001d007412015a5800c00032a95034144035007417004203016040707400c902440c00b445034a110340c004100d032101d01e510141550800d140003034070f040c00d5500001c80e69004100044100014898450703990343d42424285002c604003010300d9903401000403000708200c034050210b60030101d12070b084910901c0d255070144141c415030903c140a0301b4075071000045880b07000201040702039075104a5010300078108440786503901e4920115041e401580d2060b6024010000c5980c84000c452 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 311410935 1250 311409685 311409731
    0x705010e0f100f0e070b221404060608090c100e03160602190512130e040b010e0c16060903020f03070b0106090902090603070f051c020c06100e040312 66
    0x100400c00410301c1e102c0c0d101503c49515843c3c0c000c84c1800b01c61001c481010a0680507110101c00098684c01c2c04200845c800b034940aa40244d060a580c1c04a1600d44500107403406040588040c031500d070344e50301d003180e103604101e035000180c0c1c10009240ca01890403c0c0c1c4181140e206181c520480700e1800c001900300710003440d00700b00312849218104009078040c08042540544128404607a035070584400b512440e070150010301a20001070603a006081060541001d41136840c0f04042d1480c1507c0d000040706002c0c040c10144400b894000f038900304c400c104540c22015125042100804d80c0e95400d0054801d080044095005100e6403541454040024081540c06003a070f07000c19516008019200ca00c1e29088116040c0c010096121241c50713440489030803942d580380c112807150392020101c80c1c60061001e05402c0040364980d030383c4c038090541c01401c01c81c62100d054400c0c40c0c98105544070040d900780300e00380e42d100a820002c2c0c0464003e014035100306105000228061030340c01f0910400d46086 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 311412185 1250 311410935 311410963
    0x17040b0705010e0106061b1704080a110319081308150406050f01030206040e0a1512031d030c01050a0c0506160f0206190b0103060909060209190302010c0204020705010e 74
    0x82400d5090103000d00030540c8141150000700003680c10030340e00424040e10340242c1c5903540c5155100d101008108034204a5044080da0100d0f1140e803039a44083e128011864140d40301e25107603ca2645c0d619000c6803010701d020324140c0012481420741e885a103140c004149810081c040303034500041c8054280140c095205030200743e5440c80c5014500354085030400380c10181030f00050030040c0010f0300e403401100c09603050103001d1101656a4a40007001d4548880e400c4901e61887c0d00001d00541c201c6840d10300d142c440c0c0c6410100340c140b0114001d00c6489641415851f90048513009000e50150f0010b010b0000e4038502000501400d0b01c03580c0c5030031001d441c09039080c00d00c071a003600b45960002441e150234100d0320190000c3e0402d000030030030407411401e2140071304c7c0d030b12903041050740c1c040d0b44540f004108442040c018440c2d80d0426000a4016998540c0508030508014031940643c120480030b4a90513101c00d0b14032706030b42d000d100080d0001641105c0e40d641e00c0390030b62401d00c0c003000400008151 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 311413435 1250 311412185 311412187
    0x903120609091e02010819090510051803090319051002190f0f08180a020901090f0501051009031205041806090b010504050f06070305120c0a020d0f0f0c17040b 70
    0x890f00d411205042d49425500728141140050700051703034400c1e10181c2002c07205940507020051005103000901854400030b00d20301c0b4040344c488a01c005900a144a602d402034604c1d22800003589d000d4503403188d030783c045515400500030305640f10f2030f280c440b80c8d100c1c0c01201160149007100500c0412a4050840b8624a00503034401d80307425640200d900900181d513241890b00c2d5010031002400284c4040c10185900861142c0c1352046070040040d10707034540d0020020703040c2d960340c4d29410005004440f283c802983c180342c0045160306000016410542e86130390340c034000d249035441e070325200d01c25000d000f41004000c000000700c3e040c544510000e8072840c048002101854007001d842141c51152046042c4402800300300050350300c0c209166a52041a541701d551001c891070115440d01c07900c01001000d00d144004d010805c03141c01c01801c15074074036030221074031210300ea1810744520311500440c00000d01c840c0a1580e0503803090001040c40d600c01e5143d0071244070040380b51809070b00181c101c519030f084 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 311414685 1250 311413435 311413451
    0x80a0602120a02180d15090305030117070b191e030f0b1e0d060e030406020a12031109060d0b060301080d0311030705031605040f0b03040b070e060d0903120609 70
    0x21880115907000542e5000071442d100000790f41c4280042d07900385052064143d48410418844030318040412580c403010700b04010720071840c02070003d4000303000e005455030701101c40004000002a002040d290070b6401e05040020b0902045407240c40c9004040402c501c0810500701e1008840d01050f8640c07190b1004549041c405400c103044a200d11030092041c00d4031702088522040004184241480545010301d01400a00380100900000c45944496102c00070300011400d1307000c510a030010780315060100a660000c2d008a05440400d60b00c0b4a0304107080080003681e24110307009203000e0703036003800106481242d240001d1305500241e116600503003040000c248030540c503200c0c8154081003215824214184000000d00601004203c03086c454a04c80007140c0d0180501c040d10000c103080d4404940070754564841180e17940003a501207030b20040c01400b0580082c000c022880240741302034031941c1050400d20b4104041e1108510650500c01181c41080d4407086500407030001d0700250070b0110314a4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 311415935 1250 311414685 311414707
    0x110603010e180a020f0f0301021204050f10050606030a05070c0f080a0311071e020a0906030f0210020c010804020910090509030c1204030803010302040b040e0616020705030a021507060204080a0602 86
    0x10070302c0d50410039641c110025020040e50345040c43c4a42c2282a140c1d20b03008101d80340440e00a128180341110740c80070300410042009000529101c142000f4400d413021000e00e0340754002519816550741c6c0c0c2c040014000541124465408254400c801c2d00d081e110001050704c0b1130b104510082c405079000d03280012504003440c0c02d400f0704e8012001c036262130745c03601205031203024843e48042c603241a20244900b54005650325201c00002421003180200200796a13451315204030300d03201c0c0c0304a000d81c0781c001c0705210003400440d8400b40b00d001a1030b80592680c60ba820054128001031500c0880ca03010100414164044e12a880c03090300c00000031941c4005180c082c514103032000110b024034000c01c01047c8006082002942d0460b079044e9804200c08c40c030500000c000d485602541d404903c43c00040000172800d503103244100c41c0c070345e400b0b0726110364582c1c0c285500d5007070540e006034000030061075803040f4168440c014145140074120040c241501e881100d410700c0710340f032402d40d1040d8021070010144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 311417185 1250 311415935 311415961
    0x501090b01050d051209060405030d02010f050601090305060601140c01091b0e0108030a0809010605062a030903030f0d0204030b070c0309080d14070609060c0518040c020c0904110603010e 82
    0xb400b412900d8116007001d5640e002e139206181142200031000200e0f05111640b035031019500501002402d035860f600184500900820029409011007410500401c5665000380036240030b50b80c000c0c02400f06a52040c0055030040800c11a4081010040184c2c102100c0d0030f12421030340510a8001c01160800b0714065015511b143d04507858270301603a0010010113071300104498400010742041d1140313950f0054241e0042026034085900b1160005070700d00c82d4001603035072041040074030075805461007485491507034902603946459015403003040f0040003450940c0c0500108107000c07002502e0142c4070350b10322101d00000e42d500008103003032441d4801019040301000c1d014203548002000d01050304031000b400780c50384048480c02d400c4009001c40c148003d0b40c0140b5102c2d0f40000091101d00d0020382c00601c11b50000111034031108541d1041c480b0307850140103144600015500910f550520741e020044030481c05032048440b408081c180061988902c0701850081201615000c82890041c03100664 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 311418435 1250 311417185 311417189
    0xf1b23030c0f0603010608070e0a0b0309100902010503010915180b100f171e15031005040206030a05130f060219020c090f0a0b090108210301060c06020306011b0501090b01 75
    0x814245048560102e40f52203080e203044444030314082c3c01e91307154407100b52054920324a1054014a00d4040440c0c4450318400560250030450220b90070354101c04444d004940b01c05200a0000e001000100822186900300d100201481c40c40d05003c40d80d150184106071018034506201c403500ea007101e01442c40d00b151803089215003414910400c104916000702440804442da00c402c00515010405007140350305181d101c640880d890060608182d0102c044160082c4000da10a11a0411803680084540200b6014540c05089141152540c0c1e810f03c02900d80100031640c01c0601520203801b10750302d031010000c41401001d00684d285a290000f4503244c4a14005d0000e540c803015802401c1c0d100c0724926503012400c0403029100342c07030724900c00010b041400259030b4010101400850403120208010030741c14001e00036170328102d00e68201d002c04e42c00b0034404c08020440c280c002c14003240d01070b0019a44100140740850440014000d0188101c0e81084217864580d035400030141005108100140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 311419685 1250 311418435 311418439
    0x115090b150a050a052a0c0a030c0e090f06190f0506011e110d020303010f1d0103081309061403061503121e041806060306030f1b23030c 60
    0x90a050064031081d218400c0810b64001c0242c001aa8004144203e00351545080d408504449090b041200d0200c0c0c3e0300740c00480303040c90080b40150520303031509001c040304983d400f00c100c4003820b2a2118000f440c1e100104420031600449102c400c0c00a01880003600c501507080b01d100e007e03240e440d00c0d00300301c4120031195076105182c9014004103a070041406404074540942c00c0c25000ca15210440e9501d11070040340ca81c0748103180700c10132a95000b00c06541178030040452801001e0369130640b000388141c0019021000b5100d000180301068000c0000c0c0701c3c1c081d4000c049124265100302c03000c100c46c041d9001c1c060041c0045d1140304685420700125030002c2c80d4040e81ca4040c003849000940302c4440701078150140000040f18202041044041c030007059036800d88603112079403441c40165130040c0d5040400024645007003c60311354043d02c260810349130030660000d040016547c55440c00c2070380742d00900c000c1d501d01e1000207021210060f20a051a00d05c03641803098819001454680070446002034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 311420935 1250 311419685 311419699
    0xb04060906091d04110103090606081f06030f030f03060f0e0403110f0309120a080d0b030f01110a0804081b071409010e0c0307110f07151806031109030115090b 70
    0x28040d0002542198006400c05c9943c1600804200141c4c01402c0c50540140603d0030000006001c502c0840e640088140038010600301c01d0302a003d03131044841902000b40b840c40100d50309800303c1d101d02c1c001c2000e407446040005a46807180501011301007240d0150354100355200820080503400b00c0c0358183d40400800800c03000420403101a128003c14117414001d420040d10040c83d11801c0203100740258210441d60fa807840d120200038050b040c60110b16010b03224070794031403400d188144250b00c0b000c421002500d041102c00f4034121220300014100743c81100d02800070300083c90070801840d4100c00d0a030001c1684616103903050541c1e845c000c04c814460302c00c01004004290181030034641c0042110300d01c0b5503035582c101e0300f03440c02014000c150b2410310034611054120000004d00406032070890b2034410702d243c0740c10740071a90f08813413200841c507031180c040707040020a01a4114000301c40c0c0c1c9214950501031a0350100f8215200c08a40000d40251090b003081101d009200702d49000c80180da0320 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 311422185 1250 311420935 311420969
    0x6011a07142118010e04150b04030b09060411040507030605040c120606030614040e0708150603100e15060307380301050105040e06060906030f250e0411040b0406090609 74
    0xa180c80e507601200c0c24180000b205509141b941c0b1a4003503100082e2a600c80003902d5158001e003009078000d0700040b40e40060a4012603840d400c001503040c8102e84c803006400c140c0049900b404041c040181c40101415100c1002140e02d60f03885c0142c210a819503910500e40421a8004030103445140e8420018035290010500000d894400c404078051015a008500388500005443c82d0007069441ba40303142c0280c8020381d10303580308100c2850180340b01b182183c00c0344108483d44c80850700b1400140c1031313550101261201c41c540368110903038482d4000701507440700c90340c480d004004054241800d24000c03820850043d850114000000040844400d52031704542c103100c00030b00284214042c06800306a40c1c800500c143e66420100d864201004c3c0015850307080c9019901c9421038260340e90723a03011103900c040c01b54040701102c0d101c141c0c40c00c55503400d4414038000240401424000401c05695a08000228042c481030700104000c002582c2c565070f6881c0b0302030340185100d120381c200310054490344001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 311423435 1250 311422185 311422207
    0x70503090703080310080d0810080607050406031d1b01090e0402030606090c0c030712120504030e04021c0c0801060f0c050a08160f1119030506011a071421 68
    0x24510540e903003c0003040e6a51101c0c035038820110a00e501140c914410000c0c00c0f0103142c2c3c480c0202d0701a00124405c82c40e40c0e521445031700d4440b00100c80f010300080c824407040000c58072035000041f11074881c4000455004049000d5420801c1101d910079150420140c0b0040659020580c90020030801208180a0405500098440b01c018140f14821080140841c006000070340803644030114010071a80da5940754a400c1243d0903940080c0700109442640031003201d000d50240c030f032140d80c9c035650f801d030310200860402c002500080b2926540b12141c41c950a140c0c01c103441100010b82c07542e00c40b17503901e42c0341a1b00240301683c3c5920380c00070001140305800c000341000035102e04032a40320644548500b51640c0590301c42680e404050460341e0084414000e000b442c20350360344c50a07000c0d80c000c00f8115541920715404001d6201c010566848980103300e04100d85041200c4d15080b00300040c038000c1d0076100c1070014081d484141da101d400c400004049140304030304003e070300311215611038100048018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 311424685 1250 311423435 311423443
    0x20a140102030408121504141905060619050c0a050c04050a0b030d050c01140c07121103250b07030606080c0a05071b05060d02030f01090b030a060c0207080d09090c0201060b0406050a030b060705010504050607050309 94
    0x204201c034202141158114070b40154140d402000c3f0100844550a2003428034035540c52230300702910302407850000414164074681c0240e40c104140034008200010010004860990102c2301800c0f0781e540c0c50310511003240c80c0c03140f5070380200c00c0402d4581e25a42a820500da42e900800a26424080d606071000712076071000c020b17a4190345824840d0300c0720115641090a540092040040080702c4280030485c07440e4045d40f0040030741d20269244141aa0b4030030040c2040c1c0300740040b5101081007403043e4400609500314000504001d011452303a85079841000c591550001a40000e603940c02008000019400c0e0a18500400020304144101d0102c000400c0e103492440c08083c1440b0349a42103c2ea90b82d00810a41006100c001d00303c40342401e6020700144888258010004080d00f402544c0124510500a080699001400c9640342500e00034055840e0703484800c0c000b00f40f42e1107041c0014603036201300c060485d15008600106245c0323441c2c5080c40c20510010006410700c08244240410428001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 311425935 1250 311424685 311424697
    0x206040c060305100509010603050907060f091a1614061302090109050403031b121a0619020106031703011d0f010b07061b020a1401020304081215041419050606 70
    0x204000643c1d03141c0601d40d00321001103401042d04481000000500c865040e07210521032628075060711015904c51030111a80b400341141c44c800507a20360380501103181c481007602c0c20460812031061400c0b40b030f056521041c02c10705a0540d4107080b10443c0f00030304981407102c0c6920503441d1140c1c03604000190f00040c40544180504100e60f45d854000038105402a84408140840045c020b8100c10301c0100052a01a10401d401c404038144400c4910700d4100b4210300a40c0c4038000c06542c05d00072112805800c04a02141050866480e080b0002c045002c4134013006158a40700506a600e6040a05148240c803c1228003002c03950050100074121240c40d0f84079040d5001c06650680e20f16190070104081d00d0700ca512020500340c19909a80a55000100c620b11144103540c4144a80c0c00116018200d01044401821001d001c0080c051035441c454052680102c001181ca1090003985002c070301150070110030900d501c0001c0041c006140d010940740c28103c0800c14003400b441c0782220208215019007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 311427185 1250 311425935 311425937
    0x50706030e19020f1801080705060f03131e03090603050f07090b030a0f060b0307080601050c0703030c0f0503030f1005100909020a050c1b01140c0c011103131202030d0206040c06 78
    0x56202d4011540c444030150b055000041c00f800071000f0400800c0380740b400c284a110130b0b91103080700004950074030b2000d49070070550801c0c00758110b50341d0b13001c00845403039009403c0300c80008815035000c100d80550f4040351040d0107680c805c61030074248070b005003c0700c0c4050b01510004080400700000c030f9a2011400d01580e080ca0400350302c03034803031034106806001085000e142442c10040045203040501014503c80c101d955154a42501c40d40015559031141152803403807178100040510100b40156070101340c6501c91510484025400c3c1c0b81c113410b44e0400d582d58120010444c050040d010400441c400140108549646510001b64006041d040003840b9105506070040385080036103000d0070560f9903c0701d42c20150764141000700c000f001d200348003003681400b040f084240301d00e400c0800c1003030781e4038102807000505c003110310003006441c40820085280640d100401c02020100c03c9c5c942c0c90300c024510281c01d813409400b103104150510002d141b4040840d4000780801003ca041d80500808480352 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 311428435 1250 311427185 311427223
    0x1052202040f06091e0c0e0123090d0f05060105010207060f0806150f030a06090203160516050102210606071214040801090807110901030209070e0303040801060b0403050706030e 78
    0x30050b0b2010b4201a8480c0c80242e20300215402020004030301c09156003062041003000c500c0000c41503c240510812090006142440c114050311907900703140080d0350500c1605040c65070f640000b4000d00180c00701110f0440441d20154100181001a240509000d001030090725051003001000300d8200286442000300101c00f00d551511400000c3c04d003403100d00f45495842c1d0ba141c1030040260f006a807070820103441e2241c00591031342e4510a0301d000f10341c648400d09100c420b410040340d85420400034504a03402c91468800002c40900c000d10030911419a02c40420145209007590640010440c0f4040e20081240d0381c0083d1111203618440720071802c00001a904c0314412040c5400740707800440503580f818640c4170034007551001800c2140d110f801194104800d500c1409060102880025008001800803030300740c2d0b0007490707803101c641c070f01070f00f220304181da107001a9095850b607070300030f004801e40040d051051140038041403001e09a0fa080c14000501d291804540e05c026110b030300352200c84 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 311429685 1250 311428435 311428451
    0x601051303140604031805030c0d02041e050901230105041119021c1803080f0904060902090f0105070515060103021908010906080a05060c0c0a0503040902030402030105220204 77
    0x110384003518080c5400c080e0303021002100414540e6070320029902900420202060050f048404180000a964018014010001d07160091055114201c1c4049038442e0721002202c0c008541804641c01a80056001183c1401c044001908680c0c858040c88100703d07070702c4020700c0000c2d012590181150740640d1f001404000d28401d5030300a02a4981048105e070f00100c0705a00c550340040d24041140b104c100f041c001281391081654500e0a00e00e985580343c070000d1007000071480340805441c0040c3c1c21503210b4a4006500005400c68007541c00c052142e550108600455040c50405541007000078200b40349442d13040d8a07225074507480301059812a01a10780055403d074465016078000c03025580da804007a098120020301014401d01402c4901407405800091008000030305058598101c1c02904031516038800ca500d050b4842181c0001900ca2400c0314400107900308001c0c801131800e100016120b003881c1c4101400d42c2c0c0098403034044050100d148600200001148505641d4101c4000800c09 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 311430935 1250 311429685 311429707
    0x1b0302040b09121513020a060512160302090a090e0105071115040203011524031b03091713060e0a0e060622060c02090f0f130c080307060e1606020303060105 69
    0xd6100d221004c42100c681060141c00007071040d04803201c030702c2102e19060450325604100c4190050f07a41c9089800f00b1000032540c1400b940c450408481a280303805454110b480e80420398002440d800100b01c039580b0361041080300020321415030440c1d12032405820078855201c40d95038450b442c21400035034080803400320702199000d501103601c09113400c0c800d1540d999200c1160301115039610000d900049010a080412032180c400d010110300c070692100b40044c00c2c004110020020518101c0c1c0340b41c04220666041084280944031f0700e485444c141906a0420380004c00031b2680300074050090015520901030240840c021650004055a281ba1540404241d0f806070060403072003180785648120001c00d01c2c0d81e01150f205441b0b40240d50f00885030b110304907100352075101180c6044164030000040703505a0000340320181454000c2d003c840e0510340322034250b401c540c000c07502194030700c0d510001c81c2c10514041c0a5809003a000071200a40f95150407006501c03803100410bc03d0400c1702c00583c80e01e1007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 311432185 1250 311430935 311430943
    0x100b070b07020c1c0203010e0a0503181201150f08011a0105030a0b09090705010216080d080702030c0322120b0402040b0a0e0c07060e06100e0703060503030c011b0302040b0912 77
    0x5802071006a00c0505130000307000b01d40014400307a00039400c0a00b195044080001d811040c158054025460100001402c0aa400c1c40102e06607010326050390b110800c01003401051440b90400c02049000c5207000307400903200c1450303407041d50180d040c07a034402c00390a82c03220207041d280402e003007096490b59070021a60052062800302d55000e0180018896101c0002500c0d03070550303000703800b15162101c2d402c0075010400858400c2c0b60b001d6001b03101c020b0400b0f00c1a035805400010301e004680c1070200c500b00d0305041d0342000c40311100003245002c0480004001d540f188000340707100d603144148007200340c0f2b54111011004001a0040c1d0b2a080c2420762a210240280d0003003101d01e003080201c3c00c000c1c1000312a6406028182d520504150300c05c01a20808110380e80908500241c2d480c1c02442d201c080701500307500510180515036541e00028450b2002d04c020410481c10400008040089400c4046c51104a4072141c2c10180f06200034400928520700712183e802044a80754601420030600d1890 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 311433435 1250 311432185 311432203
    0x50307150f110109060b03061b180f0d0f0312020403080d05040c1e0f1a030103140a120e010815061b07050607080c06010501031b050318030a02070e100b070b0702 71
    0x2d986490b18070803c0c0584e80d40300030f84844084042e43c01d0707a03e6030300b0070440c40e0300c204180719024041005480503a403401100b242143c100030f00030090b0180c4d450002031507181403980c182c070000b50341c83e0b2801c101a4007548803180c40d001d0b0305046041c52f00b580c4a05249000d044610081c0503070300c6000c10240031449030007000610410101e600400c54041c14601d003000c891081c8a02c0c05000400440c1d201d510030301030605844da05802508582c41c40c1c89000007071501200c40001801901c0c240e41c0403d003000d2548000c00250f403110b240070034503800010f01180c0020b12203010482d00d1b0081581c190b0301c1d04101d0b01800700308421900c088100e40f120310308009149d03001550144001030080d04210b008000f030180981e0b030500385d40d002c1e0f030380d60019001d80349800e1498605820004014803254051006950080c81c515040080d4900000c00c0b145180c0c04418243c0240c0d0111204103c141021368a40780d00c0810444110304542c90a6240340c1c0e5401202d200401c5a40070b1000141c0b040d03c00c0054400c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 311434685 1250 311433435 311433467
    0x19090e070320090a020702090708070504030c060c0b07090608010b07020303041d04050f010504112803060b100c150915091b0b0325050705010207050c0901050307150f 73
    0x400350302d100350b40c01d81c10442401c0e01411440002840074580c0703100781c1d404560090600807850351401e50803070300e40d00001c09020603c0000c0c040031010894140701c181c05411151142c0c84801c01c541000c5a11960042038801048041039044c0606640306a407281106c00001076140ca9110380d200080c00c5006540002614054502c210744200f0305031a59180180c3c000d5086c0d07998030b111a101103081e540c04403030280c500c803001525214a41050b40f0307200125956070510812502c8040b4052071640f407154410360b40203868a60001c802e1400845003032820702030741042d030104078440d03860b00d54002c05202440241640c6202d164140045049110361808581c117041180603e146411030b4070b012416100c1c40070310a41c12010942d00980811a4011000801a00c0813aa2014084c400034a04403440c4000c1040278010303440001c4090004c0c14146110350064079040b0380803030601c0480b160581c09548280c0c4a11001c1069522801400d030301c02070285401c1d04c0026445074251454080f60803054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 311435935 1250 311434685 311434703
    0xb03070c0812011a04350307030c060f0b0d0b04030c0b010305060a14090319020c15041509050d03050702040603080706050406050c03101e0f08030a0e19090e0703 71
    0xc058000b20754032040c10b0b03c040381505031548000403000201401180a02d003000d811081004a500380340044c0c9010a490105081002c200c81285d594195001440210081640d8100140c100645800760700b0008420100401c5080380c07000002e007140c18113590281002481801103800e0602c100251319029070051003007401543d503441d00f40e565680840e02500c005241c17440c400e0341c01000448150007615480001d500705800c0c0002217016940c0c001600c02944910414402e69446140701c0b4020030320048070043d291450300c0809200040d100d4006400c1100040701448103944801d9000052505807500303580fa00c01e9840803c1c0206055007001e841c0040100e1500d040240b107800079440786104210030310003526a0010004140000d0303803402d20502403101d0522119175440c13003c640312407890400101040d980d0748007004020b030742c1d046010107070400104803440781e03004400c1e219114400e546903200aa0f6901c0c101500342e00e14006d141043d43c0301c40140034480700410402d000795070003d0100c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 311437185 1250 311435935 311435947
    0x181e03010507170901050112080c10061202010e030f0d110a0f2108041713170c010f020723180903090307120510180c180b190b03070c08 60
    0xb0f03207485404210990441400380000b0015401801801c0c12207003162420400030714a03a588142940064500518505c182420441c8103925401084001c1000d09103150380c443d482e0000401005405204038001c0d03014030918218044002403001070f840d4985458002e8024090003d800c1c180f01401c00307030054405160b46028451990781b00d0245009103400342103003c180d1401600c40a000702c601405040703074284010b0790240400001c3c025043c102c03130703034000d45511900c14400b80d043c20740710300b4620ba101c080001c0255030042d84080d403024150006044003071800d44020140c6006d20b0308042c1c52141c10310048a0354a8910b07003100f805400b0b120072201440c103903d9003907032500010641c40c400c0c42040e40000c2c145000c812170304500e9030040b0203841140006600c0c00c02038410030700c48041c002c0041400101042204480e0005421001840300501c800b0061600c19140682013692240c2084c95947c441c800a2446030400c45180ba00344d692240e0391800b0070380e0486034240c8040c0040380c00181c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 311438435 1250 311437185 311437187
    0x4052d011104140405040302280209040804052106010506070303020c0105040f020306061c0602070309050d0b0a1a03031801030f060e010806090a2f10020d0f0203181e03010507 77
    0x5802629050b4001c6403900c1d15800c100000d80b0170a96000d80560052100c49410410315080c00352080c440711000b008101440c1d000c54030000c0c040b20250b42101300450305108501e0400343c00c1c0040611541058041007403038103125121941846120304c95000001c44400b0180640c050310502c80c5000c00030052403609082c24540030422070702c100c0c801d026000c00102c5610303000d0600b00381012407003500700c40003491380d03281d4000703610100040d018007603480f5001869a882a60070101284106493b403c1814814503400940f1040880700c140034000c544030410a840c00001c0d624014900140f2140507040c1e24010b0300202402c81c00151143d04000021520a1071400003d04032115001102d040340c1c1c0d00c01c20703030351100f0b6020b030020900124419421081000d1126500307100c0d40401f00d00c0d14010720b0340005010308103200100f80c0942c11003451181c0c10707504102c62040080481c005149807901c103600300c4041c0311b00454050303c40c1c10400e40d110b0b4044001004d1004d9110064000c121500306080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 311439685 1250 311438435 311438437
    0x3071706091204120b04050109020334060e01120605100302091f08160e13060302040b010809070b130312020a12170408090103020903011a0a050904052d0111 69
    0x901c030100741c0700d004000e400906405080310100d402120140803042d005590b00340c04828040d106444079900d40101f98090b035010b024a8040071400d512950035003400400d8254007002c0380481c1103400b0031458007042243d8100305851103101003403900685407071404040f01d00908454000701d03000394103070300d003220103d4055000b040309440450300301800d031541c180200c404020881c080c40010b00d10310041005c06180c5030304004845d419042c00c44081d0764401c0481c038404003000441c201143c42e9482042903062030f102c0c0031085502880c0c440147d20b0040340090384c43c5030910031907400c400001000c040101000d000d50f405580d002c00128107040504000039696018800d040e141c64281d1410904401d021316103880c030114007444000074039610758a407880940c200e201ea580c14541c003000405819a4284580950703505240908115070010500b40500c001482e0003441c0902046428000400e400141c54000d541120030b0841d290140300c01d401d40d1880e1401d9049030b140d803c12502d05d198107a514 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 311440935 1250 311439685 311439691
    0x50318031618060e10170a1a0109050105040b0f060a0c0c0308070605011e0603020a120e0d0f020a0b061507020a080106060210020a080708061f0305040212010912080603071706 77
    0x8202442415103c0c00113128800094496012240076000100035805d000c1c20031156108050081e2102d4100544400f420005000b0360410024214001400001124400c1c0d50241c80290b8081040d02c05581c00b0401c0502110f4455109500120300c070340c401e500c502c0c008400303581d1000715007180700e40d280f03401c01d043c0d08203802c01c5030160306060021400541e141ca20b240d038401181072500301c09192441c160025807000710110100259201c08804820450003120055030540008107a10b031a0000e0003000c030412020490110f40088202201082600c0c20194002408403500c1c01035130707031030a40307a84c031403003098002904214171b0345000a4a85040d8020b00031590300740c00f07884110b000340c40d42c50124820b148002011407541004240d030b99210b5007001d5070000b03010300300c1054603004e00500c01c450384040c2e5130000081d446504100031400e0544003405184402c02c001c0c48114025582c0700200c926022041003001140c0c030000d050b80d6400c01080c8020b04144182d10040a2500009600c1300780031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 311442185 1250 311440935 311440979
    0x9040f020315042705030d0203130b0109020a0909152402060708011a0c0a0203070b130f0506030705030a151202090708100501030905070302040c08041502070503180316 74
    0x85070000b820b0b41018059050111051884420060101c01a4200b80c480c03901c0181c1707040c032046c41030840c0e001251000b58080c41105007881d04200311031414600c05241604003047c414018042c50040c00d4020300e210f001d64050a902203107880f0b20301070700300c0650219030142c1045036100da080c10041100504003400002c0d26400e40300c5c030780d840c0c0310203851000081c811410422441d001c00340c900c0d000711000c3c4c00360b00b0100003601c40c203440640001385494440d070808003911400003039001601c81d507842d583c8004c2000703000045501c0e280c0000180310b404000d240f00306010300000003812541c1030794800d072040d00000b0058209503032100d12100914070034190407030141900c0008038000c02d02802c0f501e0311904005420001c15400d00740110090629000221024811a0804001070780c41d0300072400895015a605012445c25051510031844800c0c02140554810003001c0b0100f48c01104030380c40c0c0341142e03c914000030840f5000c0780c0f4110500c00c0700c036213481500c0d6001c2072400c001c101403054000300b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 311443435 1250 311442185 311442211
    0xa0602070318060905011b030c02030703030216060e03030403080a12090c09050c0c1c110a050d020c180609190f1a040b0f0d03020f070f050301060f030f030c020609040f0203 76
    0x1512415503803031101e030117040d0110762038a0715200c40b00c0d5048003062a16200345052602016140c0c00b0a28104060700100c0158000c00070303110181800c100001c000304480d1034071295501c0340d400429100d204500014054620000f00c01240d1402030742c240204c0c01141000f0002c1c14141d080c000e002c038546024a400c02800d002c01f040ca03011648056941c4401024090441404100100c0700b4142440c0b00c0c45e0148800140700c080340400505c064074119021301c000e410700000000c002428404450142481412486584880c17070340100c0801d079104d20300390350781c10686e103071020756003801550f291044a206d030402c0f410402c440aa0703000007404000761000c07241103040700310410044e0340c1c801c0c15142d0883c00c10101d0f00e9403864030140c5036040c50f0007070042d01c1c2550018402d043c10a800781d00042c1c844014039000300160304003403194030000c00701e41c0480e00203a4196a81c407464038480420182c10004018a42800c2d55aa1400c640110400a01c10000803143c01ca0220107900100c2d030300405000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 311444685 1250 311443435 311443439
    0x120106030615090b090409211707020a050a0809040b0a0b0a0315180506041d070815010308040501050715060f0509060a05101b020a0303080105040e010e03040504020901020a0602070318 81
    0x40940c103c002603842d0410020b003401982c03010f1000401c03416000365008403050420f502e800a01c201580d403280c0781a603965414842e034051000d4a03040140402045620115514010403c041242c0001581c0b2401e000d079a28580000607024040440010394060b8411030006001e03e003e5000b040700e0b201c65201485820811105c1c00004406886402d081c01c4c50f8820300781c40130381c10340d21059100000a00c00030b541008844017100141103da50f0311003e0f80314002c01c2c070140308104080c1c060f050a15803461203560460703031402500d010b81e1140314144080820940c00304580203c03403880c0c0c10b40c00007080144654440b403082c1c0785521485864011002007010402c50b00b01904000140d0700044d01100c5100416102252a0004138003001d821040d503030b1051006940301c144141c0118081d50381e440e950350500041100303d82c031480f641c0002da0f141c040109540c2a01200790303030460b00205d400584035100500142d05010a0540091900d0b20000d01d00f010103820220140c0344c10250820404020707 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 311445935 1250 311444685 311444687
    0x10605040e090f031e0d020304050114090307020d02010c03020c121c020708030405010e060408010906021c05040b0711031c0c0f08100b130302130903021b0a05040e03120106030615 79
    0x60443c481800f11604200411070b4040d10091009400c50040700c1c016280150707940c40301c002c030b800994045600c1d03512088000360078420850754580152504001d18500026a80051041228540000e0600188240007003d060003440305480040700a0b14141c003064040c1503254440520040d4040300c100c42507030f0410201c0c80000c00d40f06480700080114a01030506d030054602e5000c0005099100c4030030007000c030302c120b020300072680214401c4501503151444480028560301b9074840340000e4625000c10040400c0707035a0441e64210515061003011030300804d22003400c62162009280000450b00c1440310640c105d644401c0c20454a5654102450103100003250551400c1c0c440e000401c5000034207115a02800300201801c0c2d05414480110b595254042840f032007009070150001c81d600e2154005154044c420355282d500d9454032120f035130381e840d0000303040b21205000c1c450080d50b03241c2103840e8161080048403078a104242d48601c1640e51060010040c000758001c5401d2401118403e5901da = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 311447185 1250 311445935 311445943
    0x720070509010902030603120a050301030b010501030e0a02010c05010e0703030c05120a140d020910020d03050a0522060e070b1b030432090a15050a080d050a030b09010605040e09 78
    0x36a000904101c500d034680704142010350006050541c0c9801030790303040e18201b42554000c141101c01920303142e44941c5142030401d01040305a001e10f042c141040000a5401004606c5110f5150709003004840403015003445801480c0c0304080c00018855220048103064020511103821403003102103490b001e1004001120758081c41011002040b100301208503c01d07030341e4000d00700c8201584c5006090811a10028040b1110350210001503001144030001b0143e143c01401d52011030301c5811b00403800c0005060310b012402090705603081d0308039880d41c1c08100c1c05030001d2003180c840104542205440c1c120491003540100c0c0500c6801c074034409200b0006d000481603c04850f061607021000070091031225200c954001c40852120201c2d1540c0040c541d110481a8000c5ca024200004d0326a0551900c8840e2412a00200d00c45d042c650340030003013941d0014455040d50094075250751070700301c400d100760302400c0d561041c150f1011920001051b05984003010300202c1c0c000800042054944001194031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 311448435 1250 311447185 311447189
    0x81c0501080307080301060c14030f030906100810020f0d0606030509060f010f0b070602130e0105150924040305070303030c0806011d09270109060c02121c09020603072007 75
    0x130010240010000280200345451000340106503d407010540c1c00c140904542c4150360080e281b000120a029540c0f50800c001a84050b071910105000ca0805c01141d41e10194039240004250300005c4074024645054181d4200301d0b0b0424090140039159000580a0b000490320141e8910038000000d54011660000c14122680420751118081c01d1200c107840640c0410350076103c0e5602081420041ca203030300e5040005111070580403039103504040070001021400e01010174461000e12107000c903a6200320001003101c081500d04428040640d460602314020303940050700da4000c41d2400818150142c001d02240d00c1c141c0c0e82c13003019588807030055a00030768004643c007043d0b586100e00c0034581460a000c1c0d4209144501d21403000900d07490010341c1d0240440c030450180d441d140c407002084054020300d07107010404d0000d440000da24601c414024040d042d203103847e583c1c90800b8100c04007440c1d44800041c44c1c014294984d0f80c0b520502c0a004421a92481e40701c092055101e490141ea001c0b03901d4003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 311449685 1250 311448435 311448443
    0x9141204030b07030234050d03060b19030603020a1d06090106081303180f230303250206030a0b03070602030c19051219090614070b090a081c0501080307 67
    0x600b5890760340049009401150038141d1a002e034144194a42035204c03c02c60101c0f4280031841c1c44504c01e850001e0415841f0007078802031500f088402c0c4111802c0c1030581e00f9900018600c0030700075440e40300c201c0180c00c1d42d038000394000104000105450490840c448060081041c00720065141c64047c003560b04824440c480006c0e05403804500390204100b07001c50000c1c0240741c68040c0c400f00128003411200640d0101403182084101080950003e541c0b4113200a036403602c506003a50980046500ca10504500c14180340603081212401d8107a1441120900d80242419440380390440b000b1008001421051344607210701000040c40f180300204860107840ca14016240c01039500560801180c80500212a03a028400c4210340401d00c0c440580080440130504552a0f83d560001034058032098001004000851901d980f0040c0090200c0b412550312048120320341e907076411842c1c1444220380340248040000039441d10400390100011101028821081090743d90341e0708001c1d9240300d038640082c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 311450935 1250 311449685 311449703
    0x50405010e0402090a0905070903051c0207030b07020f01020f0901020f010506010e010e060708030a02090a140607080f0d1a030106140a03020613080f010207060b18190608010914120403 81
    0xd07214141030700500345041c000f620386440e00f62140c140106842e0b040315580b00041410504005000042120703040c82084d40544140d206090070b0003d465807540d0101030403102c402804180000e20803c1100364a40030310b0021521030b40307a40c0485007142e00a106440c0140b03d411000180f0100c18401c25003c0e0105031100102442c6410040da80e82401070b042c1648500c040c842100401c442000031441506031990041ea103060917010001e80c40865080f440c03c400a0480b10034036511500c1c00c940300903070428542d40d01d41d0f020300744a50061203913486602d50182800200302c0310704004142c8a80141c8224000d0100c20344504000d080740074020a40c03988814205410005414400300030600601c11500c5000c681d07031103c00b520300e480d003c4e0600c600c8030303903000078a071087c00014458520608401c50302e00f149103d00a10b2044491405400340e80c07500440300c0d004c2c82c0c91030640d00140c001c0406000901094005003403041500d840d525032114540500444008120042400c0380d0580b94801200c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 311452185 1250 311450935 311450957
    0x4061e2405090732040329070503010e0a090204090b0402090a1514280e101827061a060f040306020c12070609050c01030507050409180f0b0f0705040501 67
    0x26454030004c4001c4450309501009036034031040418002030019600880c003201c5903291544000800010454072880b40c86041010310490541c8101100c2c11106510040c030603e1312a1480580184003080009600c01e10f8800309404024005c04041d00c1a4001c440030029656200c0504007613481104404d005003224400c14020140600003800c1e02e0a8040d00340c424224070070b45c602d0192080d0319a4050340e401c3d0f0403000c110f00420307450641c0e80a95018410000f452070700d00314500803035514040407612901d80c2019416100000d0900000e02ea0304940d41c042c2c1038441c03d1050040c40008aa1848100e60301481001ea0400c13074102c844806030800e510785002d01d540c86860080d04110502156030107500c1404400c11201c5010301015401920002981c602d10701e049440e01c803010713045605050904040180a07a04101901c04603001d2600c00b180b032000a44251414200800005065180c07052a800a21115400b03241c4200019905801035860b076482c140c0b1030313000b04d108082c0010148030318 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 311453435 1250 311452185 311452217
    0x106050312030c0706050c07060c0c150207050a1e020111010b010509061e030c09011101140a0911120703120e0303030103030f020a02100201020d0f060b0304061e24050907 75
    0x55503c0001c40020500300300081c0d0fa01002d88001751103d56031804003141c030800f4444140b14031000c001190400028060b429038405620044108400404680c04164ae009107d8148a2412119800380381c40c910030103121281c00c0e202080c00c5042e130024111038180c0300c008505118410314020140c4410381072561110402015500140320700300d58040b14002060213a0a000213075005000340c60301640c8406035000010565240c0b9aa20340d050780c184651182408842c02d001078005090300070100c0c60010500b031024000200d90401ea40003140b07042603070f03000b000101d1000d043d01c2c4114000d00121442120495241031080c0805138584c10030401003000902502c4107650482a46c0150f0310052041d4002604d01c071205600400542d400281c0d02d111486507210704a845400e1400800c403d5080544002c003500000b08002c0038151f036040b43c007600110b1300300c041110700c0e00c144d001d00448203000c1081101c85480c031800c800b00300c40e20001184a241200340070703105081e1651040c201690300b0705 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 311454685 1250 311453435 311453437
    0x80604020f01050c070311011713030e0604120602130605070803150a0308030a09030e1009090f02040e0a0f0b01030c05070b06011e031401080a080f070c0e0a0911030106050312 77
    0x9101c41c14841c1c03c003d1243e01c60030901000e0300035406509089a444003140c000340c4050980c0b05582e440d007032540c08018a14010010080d000c0d80c140c904076400c0c841110110f0410321840c0c1082107a41762454000c0c0400003a50014081c103210200f04d800b0141d0f45880541c1d080c020b030400140082001d00000b110103405840c4070380640c100914502c10b00b84d0f40d880c2c80f2026030040d83c1c403600140e243c1500c07000b03254001403030307003120789050340c07010810840340344020080308243c0180c018091316407000d043c4030a40c076015503014112602c07000080b4203111034104024461aa100113202d410b00880047c07a40c0284a040340d07605e03050b160b1501d441d18940c1e800c606080020f010a050000c89190703113400c0e030540d0355a8610805c1d03d0b140010300d00c06420f201d40b14004141d03c061105c1d0300403003072080000d8542003072b030b00c4010000640340d0703d4800301e141c1800b1041d1290482814900008108075500740c03260022210907000725205103901d940f000034182039807228003840b03802d0341c01803003400031308001c2e40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 311455935 1250 311454685 311454709
    0x90c0e0606040e010617060f0a03080c070b1315170c090a0810090302070b090a06051c020703030b1908060105010c060908070c051507170d150b18060408060402 70
    0x1844580b40c151582c4441186550a80108001401020200c0c140b03042e41a502c98009900b00c40d00141c682035000002d03416521400000e041d940301003540c0d80403620400100002c2d1009940035030701c449015002c1070291a252042c0007c0020885084102d0b5000c0e41841035800c00803030030402280c0d103440c0c80302500c1e40001e02a581080c0140700000b1000014403218071750950720400480c64130380c01d0030007d2501c4c519410852410000704059203040c4d440c0a40131085604e1414042d40b140d00c24600c1c0100011002150100c92b03000080c010200750f07043d031041001d240e0880d01e42d0011414000503400340380d26406105143e51117900140b103158003070745960040354481c44000c605001c0300d42c0c0742c0c0340d0346e0010081141c1520b102402801280307403003030000348841d003500341403400c120711500c5c2c0c840c560307154404913400c04c6000200c917104803225411040c0c40c09080b441e102c01040d030314070104161782d01004602c028031760b0b20100381490f4035204c0120b50403600750b90024402e68841d80c0800241d41d1000f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 311457185 1250 311455935 311455939
    0x100b180316290414040504140604052103041101030f11040e0105010314071b0f0f120e04060807090b06070b010603050a0f0605010206040308040201140d0501050f04090c0e06 76
    0x1c0000490440c900c0c0040341c01514400419001c41580180b4060b1402c9002a4002010b602408248280e41841c248908213000c100e50114440d241c0d070800c103c1d10040088a503400e405100204418802c0000f251209401412100d10780e01b0035840402c003090000759002048603244480c1c0b0130b6250701c20f0f00541e0845241c114001244a001546000b10780e000c0c0e440400c0d00e00407500100402d680600c0303920040c00d48400700d81802e24212200401c80d0602403440c40b107020305001d8a0b020b2202d59500a40865800301c0c21074a954518105160384040b288451070018260007800304035405e0a01941089410340001841154245030007000604038402425811420030310103880460141d8980d64002c041c3ca480004440c180f0310b207030009541da00310405a420b800d001040100c0d90340002c40c0c3d0390040d00f5190680e120780321803004032501b20f12000a4601c0d58000718805540c0070083d8001c1d4102c6804507507c0010300446401d000036030359405e00290121034400b404210403640e01d81500e03400303040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 311458435 1250 311457185 311457193
    0x80a050a0b030106090906050609071715120a0605091218060f07030504030c05010c08091012050a1e050705040512070b030109060e06150d180507080d0206100b1803 72
    0x50800030030b0031140c550740031700e001a4030b4000d4902405850301c2000e401c028180c9003900d0911300004060040f0070303c1281401d0102e0a4000a200244c0b20f054403003030010000c0140c005030815992195640784540c409941d8030740b800e40440e03c114000259011808080c4c007c1e5400c003050411aa1309040c3e2080e112070700480108205644c1c650128014118248641c5410362240c0c190305028a4182c0c450b000f9074140521542880081010b00c0107070340000c0346c100c52004500c941d500c0211155025042e13051006400c20052003505000e0790400558030140180588548103c07800d21810f941003942c0301000b140c0100021300040c00c01c100ca141c0ca10394800c08581e003242d66040010800d5100364060544e4aa40b42000c0c04460b044a050341e40203041120610107902e030030380914000d485081820711265940e003081c00c0101ea07114980c10003064100054440040c0d542c510b030f58448001098810040c01004c001802600550b41200160b810038814681809070b80c62140c54120ba940c800c40c0d6040c81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 311459685 1250 311458435 311458451
    0x10b1e03070e160f0203030603070e0405010f0518240f0c04030c0905181b1903020d080a0e010f0e010507020103141006031a011d120f2407080a050a 65
    0x10741021107000f4102c0700c442448114103210003d0001d100d220a42e01190420018000156800104841a07501e03800e00c6806d0b40d150b07445c009004000c149111108982000708000c00d507a107400002d0180d0b10008161103904803103500d80800102c0d052046601030f14481b000c034414446c01401642d022100c000e901d45015101c1c0c0b2407610180443e44280a4640c54104000700400c0f003184800c0c40340c00c808003c000d45103089032154489454805031501030740311050031080049051070503400854028011000140c441d09029249038420360326040410000446142254803510f07400310740c41103543e141e0410720300c00801101c080c0e0100205904041c0c07243e82805c0140180f00c90b0502035060048144182e5280103000340c00e0729042455094440c07190030600c19107907084440d51100c4510b00314100351444000c07000038800b6043c0100c2c010140708840020a5030000084e000101418011004e0714449259401c0000d240003214031400142c980300214822040e941c0101f1780281c1031403400f252000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 311460935 1250 311459685 311459699
    0x904060f0204030f081e0702010507141204060206040209010608060d12052a0f070b041701020706060e0a1a0f0103020306030c09100302040e010513030c03030204090c050d0c02010b1e0307 82
    0x100701c0b020b036114031000400328482d4500c6800c2d00303004107040ca2a541484001c2d00068094000c04034041c033a000c3c1501043c05440c13003840b40c5c2841c0c0200c00703581522180c6442c4003d5446074101c030100c0c0110004070022803414010001d0611a01c00200185002d103082d50700c05070128070720f1403410203111050006014291440c3c840c80b40c9400e18141c0d0801c0f0401c000130907440d102e0382c0c020320100c50b000148248400740402c01210b00355407202c0034031181030001c1c191040c02071150f0440a04801c2c60072a000c034440c00c80303c815600a42015100380110580040d40f40071841e01c2040056102a00c0000800594004d401035544510010241c64040e032420001c01c4600e44125081100017803081c4003442186040c0c880c26228000a4008100f80e2405105460742d0050114001d014400002806800c0501c40d804a801070304c601e44040c40030000d0300b0809015500170580c581c0e82d4604205404106510500c2000c0006000600d09203c2e00c01020000003a004140b5517950580501d0401007104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 311462185 1250 311460935 311460953
    0x150c08090d080702010201050618070c0302030c0708030306101b06091e0507050423041e0606150906021501140303120405060f06090c07021017180610050904060f020403 74
    0x1036030003499016501d00f020310009003100c40c0109050700c01c0b032a5a9100c426561441c081039405400c80c100074103102140d0406911718041e000f414029441890008110b900d00030003c0c500421064804501c000c50110060b6002c07549191200041e65041d244900800c0c02a0090807201e03010350030020342d04001001038001d1034129007040d0781641c0041d40c03c01c801d080034400e81c0c3c9240e5401c452188a80e0309034808070b204040c041d102421212450152000c2800ca04e001d00c8021607111301c08000e500c0e80e079400540440300c00802880802c00c00c10303001034550300120303010f1080316580d1006034403a07003441d042115a1030001c12540c0c2511092100d00d8003811100305441c0203e029000900e1545444a16448603941c000d0040d80500c0c11071041c02041040c19040c0e425066040ba50340c800526026412902d2405039268481c10b5011002409001304114860038000c4464a05a654030b5889407001444c880f0301d03120f240d8001d07007010001404200c07143d0220406240c5840b01601c0c255803521381500c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 311463435 1250 311462185 311462209
    0x602032710170105180a0b0111030d150605120f0405010b150909010f0f0e0702011b08100803090d06020702060d022107020606010e0405060a0f0f0f0b04150c0809 71
    0x400e40c0d0082c08141c180b410116280141405c44000d241110ba031410742c50000c03c00741c00303400c44903101e20400c00d140c0e0083c480140c1d21890407003101e03102e4442800c0740c0040c05a622050000c10084900420f80910903012900a6041a24400700c25121076112590301d00b0000c100b0380d8035558900c080ac0700e540d1101442c3d44842540562151586c1c02002003100302d0344180d1140c0e6085410348070400000000341d400c1412500300d103810920300e986000f01640500442d07032200901d0301c01c440050580d07540081b5814007270580d4100401049880341d031010303a20703c203244032643e0003002c440b035840000b0701c01c0d00103103841840a0321050421941d58801c0e004c1e40c00c102c90b0400f010a2440038000303d81c00058034594040000e100402e80ca04101d80060842c842d41c90590b40901d032920700244040e150401d0702e000078480c40821140380c950310340c481042c0c5805030043d0502c802c80104001282d04c0d58000f51001d6803503c100d0301c00082003a136030640320310075410011103010505000c01003842d5600d800641c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 311464685 1250 311463435 311463437
    0xa1401060f05060705060415020c0a0804080d0c02031903021f1b0206061e1c03030e07090501211b08031201090203190e0c030105100509060a0602032710 67
    0x1100e50820341d81c000000480d810840c0181400c0c480b26021410000d0303a1504a50000300401d01020000c01c044064422044583e030580714041e906410400b4041c000c2049800c0101138421000c8011021510b0b03409542c070280d415030200c0072803001c80c421140e182d010144a8011110084502107568084070b80d01580099415590380c040e222030b25408084101c01480d61000c0e2600d450600c00007825040c02680001503400310621140403074441411048500c1d4800b40305100e108054031b0b00501920295003202c07440d002d050000510410b813405a54180e943d880031817a40e00d03142c0b00c0107911525282c88140c41c0700780101a4800344d5040100c2c040007509000d03014558800c00d20b1400c1c1241001a07000308000c1d44100704004140310800d2003024807491250010030300503642da10940c941090702401c1b50b4903518180901065541c4500745d1800c45005889200c80c6640300c00c20019601100e11076080940c00400800c151001660191007030341c0c1d0b440d10086180341c00c032404a5102c1e224281c401e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 311465935 1250 311464685 311464691
    0x14040b0307061103090a1d090a03170c12090a0c0b130306093002060106110303070e120d08060301050a020304170919060503041119032d05030a0e151602030a1401 71
    0x2004410087e40130990088111004000c400055a4001c1c130140b1000d00d003003040d000e1680880c100c00b42c071104440c40840c001000300758604005013480c0c1c0722907080c0400c590710b803400d60380024052103e00954070340340d10840300f1840d20351664407500c019059481b021500030400c41000c1920700606a0320b0304242450030240100002d000b01c004c0d01e8003106800c1141446030303943d50701c1185030000003101c1e0300c800c02c0e103401403417640342c071020030706004c40680855a240112482c20703134010b03488403400384101c504030b00074040d94842445110807480141c8000c1d016102e2007100080c00034021000b007a0740400907003480584014540c150066402035003104001400003c140002d000b0344854512640c0350032680c4150403400c402c00c076641c9003081d1000415000c4481d40010260402c1203d0401200e000c0d41003001340001460b100782c03242d01c907440210200705001e50401c450b00f81032a19074002007482e15a54030301540400d1100e45243c4440b400c0380d141c450b02c0021400502034030500c01e42c41c05620004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 311467185 1250 311465935 311465969
    0x302040e0607020f121e0f19120510170a0501020307030c020111040302060406081008030a0c030e030615100e0a030804050a0e07120207020d150c23030408090a0b1314040b0307061103090a 82
    0x9c144034100e2807141101750500e030034042e010362440c0c2a1021101c0021649908001c0d040506003800d18005010301503510210403c00030b960035410a0f208444180d00030070170b2040c03000550041d80214040603400200c20300081c000e40d40500c140c180c2143e89022031300c02c03c17950f4031076680c9154040d404000c0000c2c3c2010344042003603003220040c013001408802500c0a413418503203c00818140400c0d0710711445c41c03242e039010400d0091110441c6801d0140c10103c8031900c038101801141c0c02889040e0244440c030600107031042402c0050360041c4141d96030210040e00181c90280650401842a03074040f0349030754010001850000d010308020480074010480c03c0c2800006408040280d95540e01c51115101e440d01c00174070001241d6010342d1200d152030310381c03010300042010489503170040020a01d0015180c507441d45201c42a1040303a4138400040d200c40100000d0005503108880c40d03a40562140100344030f2903000c3c1060071410039030402143e051074515000a1f4002c1d5050b400030314090007403000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 311468435 1250 311467185 311467187
    0x52806030606090504050906040201050d02040504060e01030c17060703020d0f05040c05090a0606170a0b0d0308041e020d0204112a0c010206042a0302040e0607020f121e0f19 76
    0x20f1000404089504115500c0c003044010388903807000300001d04004000442c040ca070f222540c1642c0107044041c100300055070702c7c1c4006081100d0280070071340719480d851000048544103403c030615101c01400140145072188102038010790130a4548856580c1c855414203000c0c5454030440d4420b0740205003040300130346403005100c424031014160904c002c0c00c1c544244140e5800208414001043c004102e81c6941c94241082c000d11140c007100780d1241c2040400c80a043e417003101c15020340d0251507528680e800f21a0172521040308900700a40007003100410f480903141980c012942c0d070100c03000301454806101808400004107202d00c980210208005801e082c5003000f001104004c00e000600040c201a05c9085007012032643e0f11424070785410201c10042401c034816401190701603c14482548800405c1381c40b404100c603540014807443c01e0426030640c0000b03400721001503030605903160985885425561440400389203507081d504108990032800082c00400c40820040c40d0754441c0a00020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 311469685 1250 311468435 311468447
    0x120a020a09170a0b0a06090e10050106020a1101080a0b090a0e0106050907080105060d09051b090f04080307032f040513020301050901060c0609021e1903080301052806030606 76
    0x50010342c8419203141d01800080d0421105410a100031401d544003107000c0702400c902d40002060b0703030400c40a0701004c200002e012045502514052201c2d0b030301c5040482c3e407140d04e1480980143e80c036810801065016007929600031040c0000801c01b070318480c3c0800c1d0010026a400c4100c90340c2c840a25481807401e205030030140004661a51060804940040446406001c0c2900c80c031000100700c502c048a40c1c0c03120802c07691200580f40c100303090301d601040060400c96103d0103151610000760f8210800300740103214960100740e46e401c0d03445240048005002003168060f0381c0d024100312041c061a22181203003030385022850103568904140c140300089022440d0343ca12a0300500051000356a40301d65541500d141e8030744481c401c0303020305007440540480003005e90800801d24410321210800c802010308280140c843d8030b600b52a020018105030b159104c040c01070407042c0014841c40ca05550498a0402401002024004104401c600300525a40b040d00843d9458104002403a0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 311470935 1250 311469685 311469689
    0x30e01020106141e0a0f260a0f08090a03052a0303071e0206040b12091e060f07020a0209010915091b0c0204020f130512010203060a031205120a020a09 66
    0xa442000301900c000c0070400b40c90b0300020502540e001c0034100041130325081440d40040c6038481103a088075a6a00c00121f020308603526058003030045e810210f15060340040e000c444070382d01c25001300f0149030503100c800241d0003041c20355501025000303001012510401c00d0140d020f486018007a000e4035001c0e800400c1071010107800d80a078005012030f1001c141816907042100c911032040350f1403180c1910015031544216001900001804100b01d00750340a00c1845510580c2010100c44903010040c40000d05050140036140c060b174010340010b044c140c00110043d03000040743c0102c0e111000c6603030010f26840800d0300000302c0180d13140000481c000e4800040310041c610300d0000c0240790311070f01c110880030b00701008503400d02514124440c115100c0780d04544490907140011500d41518441041e071360790b039600c038562140100c0b00b210000f5031418070840b805160010b10049050345981d40d1140c41c200c03a990903c040c0182400407440394448140224421000003c0040e9114042200602001101c0e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 311472185 1250 311470935 311470949
    0x3a170a11061b0a2703030c03020601081603020d02030102090306040b1b03010f0323011b141207110a06141608040b060d020d0f080901090e060306161b030e01020106 72
    0x900d010b142c00e110804102d40c60f514040c6048000c1110a07000160294029881500349115001000091560240650105500c42d030b080d9074070360743c0e00c01156541e000c6040c0007042202010030b00300010302e0000b0448000c0380c0301500150400103000006810048100ca065030034400c0d84041002602c1500040c0c2035200c8c070041c080c0d0540d4100050b034580e5068a01008280e04050089111304000807004010300101d160000e1000740d0aa10190f030b035903000e90702e101010031062905124401d0b03900080d628410500254044565034291048500d1020103030501501d00510708001c0c04200c044c000c40d504003120000040c40d40c20518981001c19948400b404201300780c060610001440340706110b03420603000c45942486d00d100c2e00000302d49410b0014005d2480d4481c032205001c01030030f0006082944000d807120007900b651396003d01d1184404884071b40c1c2c03507040f9400050360768504814038000140740f0700d0034030031001d02071814081c440201d490680c0407550328803402c07800b503a09000b2007025180c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 311473435 1250 311472185 311472211
    0xb09130210030e120703031401170d0801050f04020306270f01050d150e100204170111070f030305040311011401031b0e06060f0c070909023a170a1106 66
    0x444440a4444a5204500c0340d420030004940c5c0a051080c1c00001210301c60424a882d5940c0d02c0781001200f90411925000074054038050107901405411040d040300c2016203000c141c0102d1400700300c000e520041800358410721602d6801459030348100f40c100c2440c000c050381802c90a1101c8120301003401603014034482c0006100000005022514807074441300c078144c0200308000e035080c0450800c030500480c0071080b807003c1030020300c1003424444049800700d50750080010200d0700b1244a03041c40780200c0507101000c1280440e00007480786c0c3c0019072190007490407820315081084042e01391692039a0140245001000500c1400000441040356401b00321445c5081890201c076001c9400004003a00e108440224204001124140c02c8a00c2807511078180c0e0481da44451003040200880d28059010b42034016420803868011052001018080f84140100b000c001ca0321001c0c4030140c031811115184a04000301190070f1800c007802d0b010000c2d45a0240b1504507a0030706240000080c44288201c0d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 311474685 1250 311473435 311473451
    0x41119050609041e0903080a0501050a0e071d281e03030c11030d18080604230c040c020304060e0303030f01180902091303030c030501060912060b0913021003 69
    0x3507080126045180300703640c041032035503030070794003a5607034030410f8018040320300300b03c5000e0826074040e018a1081584107410401640c881060029404041c010b20b5120000f0401042e80c01e405081e41404c034440c0d18560306049500f040200342035814007103020946200700310b02004e0300c1310842e59000c09441e8146440c1c4074180304041e44141020f1a105c06414002c04003100d0040c41841c112000d160340d8054126000400900c00041401e00c0013004d00c8001151503002241403640400c1d0903002e6900000551080c441d08648940001c1034002c0700d04c110704c190a2002c80b551030324000c8100101868028540321443c1810180820716a00b420f24400d4204104100030f02144550310350541380103401855010360080e0b5524014903600384069800b50280c0c0402c00d21500b408000b4420f00d110f580c050045560703c01040c0c080c0c50080c0100d8000c82c00004c07003402903e401d42801c261150003404045140303c00c0d4001320f141d40d241680c844440004d0790784c403d025800c0070341080c0a1101d0f140340400c0382e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 311475935 1250 311474685 311474689
    0x605160c030f1a1f170330010602030a05040311030a050a050c1908121e0301032904030e10021609150b0a020316061e050a0f090209062704111905 64
    0x4049001d41017240c1c141d09a411180e010410587c0c50a07001c070703200c140000164058880500074181d840080b0f1a04500c00407540078808002d0300c41403c4241c81d158141030442e0341d180760181c03111058540503c40c500d050000700d00104007a080040c018005049004040e5040c01040035252418607202114404104452040000c5001d442c4820303640994a03007000305a035050700c1168504003056810040004000d12800c00c0300038412403101009900c0c908040c0b44003154060b01120040e010070b08010300c540050500200380c04030049644107036440c00417002c0c0d10010034278094020000c8641d59903c101409a0354801140c0a808800c40080c185095800b000f5641d10904080030780741480d400c0c00100304012500b1030000700c41d04402190804582c0320f141d0303000342402c0310411941d90500100c64072698003440307100d079100e80103003485800c1d0307070781c0018002d1600c41028000c4a40500341015041d5122070303040507015910814010045c5150722041184207507002900f40c803030401c040c10400c699 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 311477185 1250 311475935 311475991
    0x616090f050108040b07031d0c0307060804020607021315170c060304080a030b040b04020a0f140a1b050c0307030c030303110f09011d04020a090f0f0605160c030f1a 72
    0x100d035205e40c002d0503940e5116001c801820070701541c10358442c810030076a044004003140f003905109080d02220042a0b0761300d012214144255006900070b00c1c100300880240c1003030f05c2d2100b18281e011070041607180d1f80b001641e0140d406580000003001a000c141e4000520601482070101400c81c3e64074114103003611010028401c40da40342c410f160781e0700441d03c0b150b11349801c0700c041c07100010000c64640d82008070140502000b0203000c40040e184c150790b048400a04800d481c401c2c0b41540d18452800300340c0102c05070b403c14030003068410348a50407080c0c140355010031519021f1480740e1100c90100b4035500e00174065070303d1a08914040b903024448060100034000503a065100246081c0700c03080c40c00c1200007140c0f5010b003d4035400c9800040c12000e80c0387c020301d001040315503100032a03000b90350302c5500e0240c185040c06100001001004500e5000342c3c00b64502981038007071a585405190740c0c1e034540d6440d44201c8400c544090b10103000ca4014840c2c078070385075449884020703041c40001b0503296451003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 311478435 1250 311477185 311477191
    0xc15030906130c0506130603180c06050f040e040503121303021906140a0605010e0108040c0303051c050702010903110c010801090e070504020d0e010c02031305060f0c0616090f050108 80
    0x1074500c0800050080c45036000100340104005021140d40c0c004911100d00750146c00d02400f40484d04108002010341e0b445e03800302c0342c0c441e044224900600d08003501100c03158000c502d0b4103c0c12105000104050030001034103406284104025940c2c0c1c508015031703603070311030700180b00241d0203600d00345002c04250041080c41300164041c2c1c4504807038145141680c01004622000d604d0000341c2d900f0050340b91913940c8000d041d21400d80781c5100314548840119004082110001c19042c101d24003000040e000b080504924240b40020005200011480104840b421569500182e440e0491001419003100c400704000301c5100140115441102c00600360301c4040c071494040c1940c481e0410955101400084040c0800610555039107103540c00794000f800a43c8006400da52030842e03080c0a56000004444503580000d00d4000882c1c0380100300302850304451880d201e403510801920750b001070f007445090720503004490004801c9004c07407002001b888003078120558550346103405100c16a005007205038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 311479685 1250 311478435 311478451
    0x50d0c0c060503070c0b1e091209120304030803190b100206060111010e010e1f060f12030306030605070518100c020f1807110f030a09120204110c0c15030906 69
    0x150f03079240e54000b12100e4510300b8010308100858010300111080c1603200c0c6d08941d464280008a03921240034503030702c071000e0505100b0400d00c10084034003a400e1412400452842c1042503c0c02c16030759841b0581c41c0ea00844241041c410222660760901c15944aa284114002c2d00c0240c03206c020440c002c0d6071480081d0040d410320008c9080201141c01c25000f6502c5002c00200900c10780b4420a003507541c50b4521800e54245981441000034025150f12440e8100d894405101c44003e00e014991410441c41030811703801c250725090b0200201e6075078000c0a02500242da036080d40c91101c0340080216080184080348110303141c49200480a600100e0f901d080790301116003c0e0000000340010b1310840c080300039441018031070300810100c40d42043c411080b82d0100b500b81c54414075840c41c0c403038483c45862a8a004542c00c9601440780c010210401a1b4591001d030002517003c040c580305c802142c0000e07580301080d42c40344001c000d0900704040e0603807540742440c640ca03045062140000740ca40c040200180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 311480935 1250 311479685 311479687
    0x70519030504140d0903050c030c0306130303090b01260a0503090112020c060703020705060907080a1218090e07290a17070e0a080a0b04080307030f0e0a050d0c0c0605 73
    0x6414891808540c6030300405400c200c48100000c200d000c0c5c01081ca601c801c3d6a54002c00454081c1800c0c0409c2c046100310005000e440c541d0745803104900b201c68842c00503810540c0d41c103100000200c0b42c000da20b02903c0710740c10107101c202d000e41d6079000000c1060445011a044a01e100002440000c10b03030320142c9007420010621110303006610000c0c010400170b10380d03a2080105028401780c240e4001c15180d03000381d0695590f56111012913a66000700d210311340143d030040d08440301043e890314080d01031082c24138001b9040c00c1400c4000c43c04600d15004403800603529001201121800c112800c01408113281851541035619402461030716002c0c0011031300e9000086a89145100380a82416011804642045800d1a02c0004c05d031181d48014280070740c80001e400b190032040040c40c0001294409041549a51281d95411094101522040600d52148145070000285025080c4607049420061410090900307003d0308e000c00d020b840f54107102c0c6d540e0728200812030100b0340300141d0b680d074103141d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 311482185 1250 311480935 311480941
    0x513090b160e0a030f1a011809020103060503010507020f0f0f061603061a03061e030c0f0109271a010906180512030d0605060a0e090c0c03031e0705190305 68
    0x2524030a00c030440c419441681c140000c005c00030309042d0948164050403068010140783c0d001010805800e011362080840ea02044284414241e00b0100d10329106240100d4082c2e52080441e094810680e41c260250700712121000e0001030411090300421106030080c41d40d0305500b180c094803440d010b00b1403804961182382203100700e03020f44c0021700205501c00300e100291645190641668000799102d03449800e819041c03040c03c0429440440245d20001d010f01001d5000e941040300e402c0040d806141841259000014492400c01d07042c06407080104202c1045600d401004040701c0f1a024098003990181030007000740c2e41c0c400304a02c1070326190f060910303101d03410358500b4501c884030794001d645c05030201500c2051240c010001d0003882c080e01500748083c684a0b42003143c1c0e4000c0100c8000000d401a10f001071034900865080e41000c641010780e4035001007107045a046501c201c80510380c3c41046e0502051342e01c5000381040d0f10580e18900542058085900940e4030000c6807081d130201520f91003c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 311483435 1250 311482185 311482187
    0x1050a200d15060c0606050904030f08060f1e0348060703050a031802151e070309060206090a1a070302190306180207110126010603060513090b16 64
    0x1000b00c0802c100340076028903a41e5030b80d0083c88440c0301e40c401c0310007030b040c1500040c590400681450040350b02da11828550040004204c0c0d49040003850641d001c0c2140c6c9942c0d2490b19501c1c0d882e1144c040c03021400451b024000289898060003011504e8080703000b034848980d41040c1c80b034041d80040100c403245129449810496404549044002d6100c0300004600d0b0815030000010540340285403000d008580c4c1c807440000844886d010081d42019a200e0041010f040d8200180142c4811490304003041c0380d8091510f90a07000710800710041070130400207000305601001100da00c02d0215004003001412640e032072031080382c15152008010310580c045035089009030162401d86150340c0d503d085103074900c0303002805020240319003168986002900c0c030464406000b255040c680080c02154016603280c0111403c0d91805400c0d03010240020701000d032003007401c01241c020300340c42c0d9010803042d0810f02082006e0042080304030030b5524200140b030008a0b00e03d40c0315404460a26041e01d02c1c07a103124 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 311484685 1250 311483435 311483441
    0x60506060c01150501080901021606180b010b07020330030403111f0e190803040503040e160305130f0b150d0b010f140a1a1312020301050a200d 63
    0x1a5101071035007020814110202211001c00454409a071810b0440d00c3e840c02007402c0307108620000303128210403200344002c1071b4250409103810070341c400d5074106c1100743e840b20780c1c54407001e030020380c400a00003441d5415031400f00034001c2c040f10203041c1815004c00780125080118060320242c1c80030740002c03000a00f403500807101482d16114a50650784140f07040c070490408250f0000320300c1c01891608111032642d00700020102107450302030702c02c00a040243d880c1d4110941001303104451a2004220108942d81c0c0120041d00481b1501943c0d41801c000c440003605403000240070f00031081030301d0000380109801748090301000e600401031290640320407400075020440540000c1e04642c04002c100d0401c4094454241210454480740d80d245455085081140b9080111035901a080c07a90a0040564580140c0e0000e11000c3d86640350109901c5526011045079225400c1c900c0e140451400b50f003800c0c0140d60303100801410400c40311b5103000b0a0f120078840ca103030000c541840460a4030003080f5a44c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 311485935 1250 311484685 311484697
    0x303121803020c0109080606030a0807210c14010203060a05061605060c07060b03030a141c1b0807140a050c0a0c030b070f02010204061b0222240302060706050606 71
    0x80d520855001240c10041e55611001c460b007030000f020035800240b400c1c0082905070040e03600501070800c1003c5911045030300d400c041c5069881c0380141061203469124089400e1042c64581c444e50007040643c240350807407400c20590603259900400c204506541c581e100042514800c43c3c00c032b5120b25103241846440717441140c00511610a410a101c100d2039030001505075a48546002e2040007980c0003071640340d0140f102c1c0302c1c010507504a00310902c0d4511001402d8580042003207030045100d10940314081e036608125403413455000ca0004c04c20140e0004a103580700380c00e07040000e0050082d194030040780c4500c00302c00003000300c0492551002c8105110744d18540760400b184003803a940700d00b0f11070780d045026101032010440c60146030b008a8018000e43d01210740c1c0c0e0300d84120f101d680d5081d0b6040d407078003404100da2200110380b140102c291610f001403003412407410001001d0642000b03003044c019102c2c600c1c010703d07103404000b040141d4800d030032114080e6000001084680381c040210348240284 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 311487185 1250 311485935 311485961
    0x501031107021302040f0f140103052a070303061502070e09070e010e090d0f021504022806020106081f020f16060c0e040504030c030c170f0301050424030312 69
    0x428040403c0b00d0b801d8001e441503507522440c1c540b0881e52000c0701182201079100b184050b030480d08509001d50f000360b0081c0c1e8055480c5101d02c03050b2004e502d000308440f01a034040e90950b00042660300038140d15100b03a50103080900030000d0103121350700010703660382e90510403508400110f100180f01d0726818407a500040103014900d03c01541c40d4541450a000d0444040310940b144440e5070f000780384101d80d960b502004580140004c010004038a088400c0010301c140d80088840100550320410b506417400080ca010700310000c0c03039003000720003400e44010350320580701a132142c880c0881c00f4020340e001102d840c48010005075100c0d40c1920610342409038521081500340c40d11480030078008142c218650840541d660030000c80c01000410041303035002da5000c2c000034180c002810002e030090f0b207142c09050040882c44889041c01000c0d555580c800d01c0003001c09007012004002900701030203450300d031100745540042031260840c0e0b102c41c8030002d4400641005861300c1c0400c0284004d91004605940d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 311488435 1250 311487185 311487199
    0x2010204080f030c060a06120b07050717090a24031a0d1202011112040b070201090507060c02031c051c0e010f090201080f09030d020705010b04090b01030507060810050103110702 78
    0x440b280312602d98003c020342108a01800380041c51000312445284282d504071409a8500c0361030ba100c600320100002e10801c14070000308140e101140028130340d178154500f0319807000e550b600035205003c04c00000740c0c03242510204400c031001107103040c19600c3c2c03840c0c0b02e540790004048080000140f84100c04100c0523801102c0c4803041000e002100992a006901c3d035002030022401881180495104403d5030032a42580785010800144030755a00700d821a00510003c00e45615503100c1d80d0070b200e816031040d0302150040ba4440b0443c1030600484114040b09203d20b99100101c2c1009411442903030740b5000004084e000080b6003000a0740448941d040c041c008000300e212070303100800240650b8a050f170104e0240c2c0c0008200d080c202c14482d20421001002d1030a0010140a92000e9000503508403815503d900f0b20403101c2d1511300c59044414001c00c00d5650340d502d075040080c2032500640141c0c0030407840c0d400b0011020071071506042183c03828a4001282c02c1c014a071f002031806060030080d40004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 311489685 1250 311488435 311488453
    0x9030c080c01140c03060310020711180105010207120b01140a0e070f080c1303080a050702092a122a160c08070501170402040902060708030a0c030b1f0201020408 71
    0x5611441c081081080c800705140c5484d080c00101d4082100c00300c1d4150f1180106019000442d000b40450503c0341d40d4103280040c0d854005000389101c1d41c403a2040d404444c4c01003255690411100c0020052490640c1e00f0b581c894440c44a000014000c041059100107010805034545450020040146000490740c1382890301000300b1a40b40d416050002038641404294025800f00c00c850480740040911149a4070f16501c0c03a909800007442c007010321505106200142e11101342c0d462080c2d9095500b000c02d40101040800c0104110100412010060050290300c1030606041c071782100c19a048040c02648000f60451012916410040180c0c3d001c1100380216a501c1d0038103040c0c07840f03a0b010142c07950b100c101d015079400d281d1007254009040c1141c0041d012150248080d04240060008a01c420064021406540c0b110f2000c42d0411800020440c8001e03451042018196041c501400a0804140010301138010340036075498000d10700c9565248203000750304031b50041c0600f0058900c011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 311490935 1250 311489685 311489707
    0xe040218120c0d0b1608010503150702030c030a0503100905010f03061808040312020f24130606060f0e03070e0103140a120c0b09120406120e120316030b03030d09030c08 74
    0xc2c6043c2d805035207010b00046803070030403801004d0260623100e024000300000c0007400040e0986181c0580041c00b03600040000c150701031000c1c001455102d8064a40310fa503802c0800d1030040c001810740c01015500e19000040c40791a5940c102001280d401907408a03045078400b04181002d00c01c1d100007416420000f40000801503200401d00364200d194003a02c9007110f01a048a0f1036008401400304035041c2805001c3c850175600c0c7c001900701501240190340400c05a44220440e00190845404151100d030313440c03a8258480201c4039000130680c060003001b4500381040c44d0440060000030100d25025421600c0300c0300c02c020b8a11015000071030b080203500c030800050300680c2e0004081d1452046000050322070200040c80036007100b04a0308140c80c141c5460700c11114800d0405000541903103c1c095585a03075020000000c0d1110710f240c1040e41c030b040001c90504505010001e031070a0506114100300c55542c0841950048a1006000300f0704500f07528040360200100c000040a0a00c00b040540c042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 311492185 1250 311490935 311490953
    0xf08070c1805070e0f010e04090c0302040204061106090f0622020d03031b030509072601020a0323060102100b0d02061902010606020f07060c0606150f0e040218120c0d 73
    0x10704198850b414004d240d6810700c040a05080d900a011404051480e0403a00f005c1c0d000c5029540914050510151658000740aa0b030080c1e00031800a00300394052940000305202054014400c0d400514264071740d11a030319180d10b002012112a00074032611040c2c0c1d22424030b0b0151402e580204014001c842902d0f01030010b03d8000c01e141810804003200e920790b58001d2140900900009000308003151408112401d851620741030750346901c452035120f2880b2542400030342040e11060301e01280c050301100e01a110001c00c2410b038070003c0c1480c0f0a0000b182d8020410ac0c0c0d2a54502030049404404003001c1030304000c568000035048000050003c0803002010a216040c013916802448104e5503050202c0e9141d055005c0c140264100550420007a030250a40c000160310580b00420950f5549007516040020b41c0300400c0812400c01000403110f500c00301ca044859004c032400c40c24010505119160b141428150034000e441d1791900030030b100c200700031200c83c0d08030041c5a403060602601d000946 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 311493435 1250 311492185 311492191
    0x210601031e08030a090311190209060105040e06040b0303090a1409011202181504050411030715050d090f020402040303050d0e060708071d09010623070f08070c1805 72
    0x100207996003000000c4480c00540c448400d03003044400b421611000340400040c8607484040381407064411001401600c280040e460b4418480b0a00307018820341d0040c4580300c240100310030f040240030030090000404a0a0840e0041000d4400041030700042c00441d140d80304251032168428984040050321040f00b18480032011001d5441ca0403990781c3e07015002e12802210f00c001d5100d80045080000c00e4000303d4401d6000c450660820901034050f80840e049840030b480aa9507840b4403075030032200c0c0c1000c21062008150300d804402c1480e42440d030052040c000d0580012080e900e1740c90a00902044d400d05100c0940c001b082151b41c1c079981d18016001d948020358007110107050443c1d4a031150b501083d0305104040d685c85680c003030341d80d4410440e84410080c083c00e0010b401c685100030540c4640b00703031501034500303925544994081c03102102c0400a420741c8100641c0c004100f4800090040800380e40616486a801c0d52142c0c01c40c50542d60841080d0040d0480705081450082940d0840d0001c0d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 311494685 1250 311493435 311493443
    0x7050a180b030114190302010219110a06090e1509070c02010201231009060302060f0304020303210a0e120a030c110a061e090c230d060e01050c04060c08030621060103 73
    0x91030840c14980c0c4021794502e0300c4040c2c050703080758500506080043c1400910a172281d0a41481414100d0009410b50050342150002a400701c4040c410700c0800c00501e604240058001c60101c0c0d90319000030349c44200203000c881003050420550045900075005040c0c1c881680058141540710325a0b01c2494402c00c50346050205074540c400100007845102e0f110a0301d4002d026645000a44501c2c800503900c082c004980511041014428103070310100b04c5c0032443c82c0300318002294242141d506e030039541d5042c070210441e0004c030150300c000480031080b281c03000280d007008140c5020026042d111440501569203190003440c0140d0104182d5034099070800c0c40c0480800742107020342c0e84e00d408684031260f000b0500100418203200f100701302001034541e201c00c003900d02100c90442000c42c286002c3c11504441c07840e2680d81051a40400b80105948480900d0401e42030600d801401402c0031040c01c8003030041d03007000012031000d1300c601808402d0358005501c0c520150101c1407100ea60390109101c03e035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 311495935 1250 311494685 311494699
    0x160f0f050d080103030f05030618040b2403030d0b06041d07081501120b0a27060e060d03030506010315080a03180b0f0310120c06030501090507050a180b030114 70
    0x1070262030180300028182c0790155108000c011102c3d00c2500d03180d101800c2c10360700c2180660b004d8100018882101d00c0b80b8400c004503541e83c2449204011104c0a44500001d80303640082050f0040d00d001046d5800c00758000320100301001032202041c214482e40c3c203c1401000400442c1906038040104180203d5065079114496921011031103450840c07402c84600140c00c034412403695488941148035445002032004000075617980264010542e41d041101100061452140041820344640030043c24030880d9102107203801c000080b01c0d5000701d8402024943d0f9031020a1070350b4400d0780183e1442d80ca280042c1c1c0a5030f29003a40903501d092070b80080380021041c800c0500c540460100d00c030201c800002c506428072070901c1c150581500020134007030090010440004481500c65211002d4902414584e800981025401016500141c101c3d4401c01d00b818107200010783e100303044944140c500e14055a0081c092302d005540c445084e0700c00002e0300004000031405003480010320702c250030102d90078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 311497185 1250 311495935 311495953
    0x40204090f20040902011d181303120e070b03130c1404051501020705041d01230c0a0c1e051e0c0d022b080d0b040606080912160f0f05 59
    0xd0f104c20140090000b0700c40083d4081c4010000d80d40120054020200c002440d005040c5040711030701103c006101101d91907120b024035420500303810400710303032f01000d210b8175444546447e6500c22921030a040410f0000015480c0210080c0100075240e00150324014555104505103030b8079440000a44900e2030280030030055060040ca80c0800141a006003889500c0c00041000801103081e0049640e19249107694074404288641c0000a11440c40c1c0b803100c4d4009000ca062440c0011703c909070480d400c0050690140d0804511069258095010600c500d005158441440c0c4182e0f40100548101c041e09010ba00d041112060b0303070400441251243c0a400007045000030310302d60041d40181129481d8081d03030440141c41200000c003141c106191040c50303580c28030f05034040c440341c204003681c80b094241c0510306400b41d84010410341c035049000d81482c0d00f45030b44910004421403c90000020546a00350480311710201550304100a64001c0202d81010340310b480780c103142118240950002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 311498435 1250 311497185 311497189
    0x10e010e04050a02040b0a120f0302070e07090306320f06030304060c200d0303050901290409150e280c0e04150608010b04110901020312040204090f20 66
    0x485441550094024603d910441e024080241501c1810b0b941040c021100030034500b44000c0c0d45031946d8803407681110b5406450400a01706a859004154845022028000b41a03030044160b400d49421000005015103850030440e84828410020402c00c0255076008e0201201d560354a44150480700c1c0e0180c40d55164000c06850303100e01c1c0210b40101d501e6015800225070341500100045944c242c0101503010000009052040302c800111300180d1200b0800200310000e0061100a481c1c914444584c2e843c031800882600d10000b41440c0034540c1c0342d10070001c0c030040340f03065024010055010094601040c01c0c1c10380703030302c40548002c3c040b8034809519140055458901260590488903d600082c101103201242110103003050340c06000311140074403499094482c1100420030740c000000e801c07003402e0a20055400c00c0c107640d03220010a0100c8400750740c000c011100081c0b40b200815507203565510000c0c006183d014000b405890320000c009003044845e5034004403c2c1c0880289055480b04101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 311499685 1250 311498435 311498459
    0x42a030c12140c0a26060117010b0306010605160501060e10060e0901120818060a030609140c2b14011a0f07060b061207020726070e1b12010e01 63
    0x1c0e50f5085900d0307500822034404000d94043d46422908100d008034000244e0180c03400402380c00c0b507680000599646403001c6002d10503a441e6120983c00781401e907250541c060081c2c092900c10782d00328004100150700f04827081d07203e080135101043c1d5060131070501340702c004119800740c09494007181409441d00414588550203a04958000107580340136445640c0300000b64100011003442017504040446150b900d000c054840d904d0030341c0e000101546400450700039540800a4401e00c000e14605009130703482600c0031203c81400c2c2858a100c002900100c940002882d00c140054940c0b900030300c46100f0f820031849504880c0d10103a03190b10810032503110006403042c0c90700711000d0f04007000710000281c5550040051500010300d10303410003142005003c2402070480b00b003030040c0c100100900190b888424100341e00d003007501c080c124082e4400816681d5044500a07902c00c15505400180a000403a115817504070580495689a0070241900042480700f03015144144642d10700200c1d041c080c0716 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 311500935 1250 311499685 311499703
    0x105150c0607050717070f0b06040e0c0405071b0503120601140405041a130608010c03022502030313060509031c0534080309060f042a030c1214 63
    0x50181c001502e60b03890a0302c0a0340015801c5501844103007400301d01c0e09025000d0402c590040c5d000940700701491800c0040010002e0440e031059281124042c0d01c9000052222486074081d24002440d0712070300c200b910008031038007013107040e2407120980c031080001c048041e083c0c0454480d118045030b1107000c01901d4406261111004e00d907030600042000f442d09400840c00c050104041c0740109914901182800ca601000d0008140d00c4100801900000341704a10003038050340307011420f1040110035181541c02d140c0304e154601200002450a43d902402142c0021201c078003121b41184d541e450203802d5800900752a80300e4081c1c502c01c0154110841103981c84400c01f50359541ca09842c2c0d0100c020503a03000c1c0c50107200112000c8010324a4074144010f004800d008030b21407a1245440d601480c9040c00060941400a0100b82408001125031130309400c030000e41c0c0a015520460700c03408143d220712982c4040d1036103420440000e40f61620340e1703540c00141c2c050003204940040c02c4203030a0380c5110003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 311502185 1250 311500935 311500957
    0x3060b030a02031b04060e0901150e040e100c0807030506030303070c081309020a0215100f0b0d020d06030c0503060a11040b0708040302030f0d08010801140103030e030f06040308010515 81
    0xc00025600d886036900030b680c00b4140361071024032900580d06030748041d0800d801c0280401c900c0300c207141d21031509580c01801440e4490b6201e07511031100c08000d00b0b8040c4006954019600c801c0d64451000041c0700c803c105090600d070401800201ca1000cd280140c20781c1e140001c2890f15005c5180d504001c01100d2054289448801c41c0001503912007000b270380440c051a50104d00810302240145450000b4000d90440380c0c010710302480340742229030074101c0140080401d8041030004002c0e01100c6040e00e002c8611600c0d81e142c80d54142000ea40c00b03482188091650703107241400c04000c000e01d00c080d94094075001c4e41214401c1d962600310008440401d0886207030904140810800b07050040014065a80329111603400d09a0b20f40c042450100011020f0300583c00c1036003840c60300d50307125140600600024000b44111002164602d1031640c060001a0401c141040e0340151510f003005090300c80c0601c0380807501946003d0400034607891080c02000c3c41a0811880c20003103083c10360a4407440100317 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 311503435 1250 311502185 311502187
    0xe041a18030f070618080a0906020a1a09100203040c030c0815041101091205100c1409150403050316060b01030207051902120f061f150806030102250204060603060b 72
    0x39040240b415402c81801113901984800070b80d1040d0344001c10701081584110110b603225880d1540281806445801803011540000c400c10041049110881c1d2400d04400c2540215110b40001070309001410300f64102c01400002070004000418030410100c2e402441c0414003030ba2165049901d0710000d9041c1851500a100890041441c50208600c018814100013031800c0c1d540000f00001d081151090300d00d80c12030480c1c130300704070024010100190210b01d8400e504400b0300f00e10302d0090141010203801055409207002030300000724112809148c002d03045036100e4400b40030b02103000c0b000140880b401402d08a03124869400b1f8004e9075000c82d48080038040c80e801c804403d00131140c1c003544c240d91120641d2442c007a82042848030041c0940b1080c003034107203880d11580f0a8254050800808007401840d03004012051030302d04217036070401807841e1040303003911500002406030041c0d03a000c900c110761074085a0b128804010740080b03018800c2d40c2c02d00c20710360b80350400d0701144d21034402d8150a80d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 311504685 1250 311503435 311503447
    0x30f0605070e0301090b06090906010f09020d09080f0304030207060e0a0b0d020d0203070914010f0e010503060411030106020a02131407080702070801050f06030610081e01060e041a1803 81
    0x14840c0c00440d030091a510700854403010810001c3d0a6031030200b025035104204405000c042d0400d0520558429104801481154507040100f514600d2900c01c41c0701d000c3d80801c2e021000d0394a504105102500720740815100d000b040c030000c4007a4402da0381140588620500000d8150141d40d5214411310001d001202240c41c01100007156480300c1c03024107030341d83e0030081c0041c02c0700640f02460003404e141c0d540d46942c50030f0114603421029120511414048107890f402e00c02540125640320810003840c00d40c0d200d494080210b4058440f2440070f0a81c0c000c048008101c1d1540026031a2b4458001c8540f0240c0c00c8111064a040307480b0100b940021403c1800000c0c106802142403039008034082c4105e4114030b03660810942100c105544044018050000344040d6180400034070f03412510600414465520b4420740580c0c41403030500c0c1b0034015000407054500764001390300810090481202280345031901e46414840b0700140f81c01c1c88400003242c40801c146460384e504d0407005105003c01185003007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 311505935 1250 311504685 311504693
    0x120a050a0206060d0818031e0d0f18090b06193f050402060c060a0f0f0c020d080603030c071403151605030406020d180201081b0d2c07030201020c0901030f 68
    0x5498a1105030548070703050f03039600543c04d00c4c0038402c180e43c80940909115120880f0052103400071884030410400215840362451646c04000001c40e0f81200002900cdd040480100e40203003e4015402c580c4080c0c4045003425580080041e111503044410a42200d1840503c0e40e200762550310507026031061680602030346202543c4655041400201030f0703414004035400141c60308a00710713201c41da01074070354000185445c914010010301c0c044d034500c2402041c0341503034000c2d40c0d4400706d209401001350320400b181131500e06000300d078103c2c11110159181c0c1030311003005c00400021344c6900c0d400307442902800382e0340ba60310910903401400c4080d20781e00c031000314440c00c607095000070300103a8545a003000315800c0701004c0c1c40340100140320078030480c0c0c1a01c801d00014260543c010514001c3c91520090203810b81f001c0422200e00404480d00010108101001c040021506500c91708070035032280c0409498000000e605012a8801d9080b01c03a01c481a80510010181c01c0c8002030001c58101e034428002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 311507185 1250 311505935 311505967
    0x8010c090305060115020a20040b0a05090a0506010e0d050a0c0e041e0302010213031217060f1509031203011707050904080a020f060705130b0304020102061602120a050a0206060d08 79
    0x3c03900e00c1141c940c0c4241b5100d00440e507d011040c18880700c8c1d6680d88100c9420300740030301110400101c46000d132003032408001c6100d007200101101c1c0c5040e924800119260701070002c00082140180407460b0031507083c03406035130720319070751105881800d02540f00141920081c07400510441c0d020100b150a0f03003c0d103a0345100803000e100200d0555400b4040307070320074001c02d24401e0000d6002d612232400c2405102030182032840001180c0000c039080d08104a0584c5600c040305014603c00d80b03e095850154500c2c40300c0c5030040e4a60540c0c140103c0601c581809010006035040e00c41207803018160590348655150340e01d41a00c40d180d08072a4a1700060045551900505200784017401910030101a00d04940d00301a030403101140032460215582c3c011003584501c03034000d000d0300c101c00c91841c100b54001030341e00c030700040030f02a003298006079244e1500c0c0b0900061080e0103d880c101e50315540c0421002e406a00004560401481100c000600c203160500c103034403580f030b0083c83c0c86140054030f095450344 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 311508435 1250 311507185 311507219
    0x10b01110d051611060d0506011b0c140a05030f0f0d02010b0108061302071a072606060c030f030f0f060108100306150b070f06180b010b070c030203031308010c0903050601 75
    0xd00d0713007461250307104d911044010981c00d048021300083c40d240171800505040020340e401d0500003c640c040300001880703000c80c0c03002d5880c292544203000d100c00740001d00403011a0815a00350050b250f4034400440001110004441210191600d4100c03e0004900322a2070001c5680050994030100e041c0d414a01c104603003040001c1e20261806905440c0d901007140f43c81564040c02e14030408101d8140d03402401c440702500e0207425207000c2c504113403604005a038040c20b15481064001074013502ca14041045400000c402411542c5924140d0056110400125900c000c04040c140020740c0940c401c5caa8a031207036140060a020540c1503841d40c0000305440140c03100148240f284c0413480e00e00d400054a40b442c4030b5042905144018079108003aa0802151007007404141040000042d1000348180c1c15218002e0599440f1480d03800c140c0780c915002e500180d018080010044d9040c1454800c107030584aa89000340a01980c00320200d0b0501060b1102414582200005100410100c070404e50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 311509685 1250 311508435 311508443
    0x9050a020c010504051c0207180c030b03060c0d05010b0c0d0807090f0e04020a082a011e081005030c1806030106170a03080f06010c111809010b01110d0516 68
    0x414041a249550300f1642c06403001d0710380c1c0c0d002c80d288500d0710520080c84001512603201800740c5074601a0282c201c120840c00414002d074440186456503480b0f0340c000c0080e164000d048420790301b041d4903502d402d60b03c00c101054030079080000104039130071000c0c2210b11101507000140b01c00b0300601400c5480f4440900080c0400042c03038000a14000c01c40d01181c050082c203041612607090074410040e0228042d4041100e942004130801d074000030f4003004861036200a141c027408850f00000407581c15204e540c1c01440c40d0a6040c0d0b00030002e0f840900a13200f20001e404d2408001c2c5c44204155591100c8441164007072000c3d000e09940c0d15620090b00d420600150000c07480c583c0b00c50000e080b854400c000b014460303000d02a3311060550141d410340d04240071a41d01850350409000081042d160786c4070240540c0c042083c18060303071700d07051500300c0d03c2002000c2c42e21050601112242c06040c019a015001500c0880486004040820900e031031203502c3c1c44282c90152100541030026900ca88151 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 311510791 1106 311509685 311509687
    0x32607090815220c090c050d0b04110306040b0a031202030310090603330603030906020d05030f1609090f200705120f2802010c11060109050a02 63
    0xf03c103040b90804078210740d800c2400c1c101540215944944903140c41c01c148a801d00e0750150140001c4901e032103087c07207004070460800094808181c401c9010340800c101160791407505038420030361070b0320250803d0391643c0e49480f1901070403000380a131070140c0c00010070894000183e02d109405444012400c100450440d21010f065500a80011082c5240107125032801888003201c0b983c200c041003824800c0c40d84034a1700400310603180c401c81000d84034a410b000c0c03106015100f41e910410308400114a55980c4505c14903522141c401035109000c490140801d2464850254595011075105e0125664441c21550341c0340c004510702d050004281480644009100070603203030049480c8001840e1100c001c7c03d0411028171078800005081c1190307429034208600f00786000100a000d9400800112280920a0300d01402215150400e90880c80c01400118406da000c0d603041010b003d001 = true := by decide +kernel

theorem cover : BRFrame.Cov 311330935 311510791 := by
  have h0 := BRFrame.cov_init 311330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 311330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 311330935 ≤ n) (h2 : n < 311510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
